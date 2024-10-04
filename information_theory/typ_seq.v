(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix.
From mathcomp Require Import Rstruct reals lra exp.
Require Import ssr_ext realType_ext realType_logb.
Require Import fdist proba entropy aep.

(******************************************************************************)
(*                            Typical Sequences                               *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   `TS P n epsilon == epsilon-typical sequence of size n given an input     *)
(*                      distribution P                                        *)
(*   TS_0            == the typical sequence of index 0                       *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*   TS_sup           == the total number of typical sequences is             *)
(*                       upper-bounded by 2 ^ (k * (H P + e))                 *)
(*   set_typ_seq_not0 == for k big enough, the set of typical sequences is    *)
(*                       not empty                                            *)
(*   TS_inf           == the total number of typical sequences is             *)
(*                       lower-bounded by (1 - e) * 2 ^ (k * (H P - e))       *)
(*                       for k big enough                                     *)
(*                                                                            *)
(* For details, see Reynald Affeldt, Manabu Hagiwara, and Jonas Sénizergues.  *)
(* Formalization of Shannon's theorems. Journal of Automated Reasoning,       *)
(* 53(1):63--103, 2014                                                        *)
(******************************************************************************)

Declare Scope typ_seq_scope.
Reserved Notation "'`TS'".

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

Import Order.TTheory GRing.Theory Num.Theory.

Section typical_sequence_definition.

Variables (A : finType) (P : {fdist A}) (n : nat) (epsilon : Rdefinitions.R).

Definition typ_seq (t : 'rV[A]_n) :=
  (2 `^ (- n%:R * (`H P + epsilon)) <= (P `^ n)%fdist t <= 2 `^ (- n%:R * (`H P - epsilon)))%R.

Definition set_typ_seq := [set ta | typ_seq ta].

End typical_sequence_definition.

Notation "'`TS'" := (set_typ_seq) : typ_seq_scope.

Local Open Scope typ_seq_scope.

Lemma set_typ_seq_incl (A : finType) (P : {fdist A}) n epsilon : 0 <= epsilon ->
  `TS P n (epsilon / 3) \subset `TS P n epsilon.
Proof.
move=> e0.
apply/subsetP => /= x.
rewrite !inE /typ_seq => /andP[H2 H3] [:Htmp].
apply/andP; split.
- apply/(le_trans _ H2).
  rewrite ler_powR ?ler1n// !mulNr lerNr opprK; apply ler_wpM2l => //.
  rewrite lerD2l//.
  abstract: Htmp.
  by rewrite ler_pdivr_mulr// ler_peMr//; lra.
- apply/(le_trans H3); rewrite ler_powR// ?ler1n//.
  rewrite !mulNr lerNr opprK; apply ler_wpM2l => //.
  by rewrite lerD2l lerNr opprK; exact Htmp.
Qed.

Section typ_seq_prop.

Variables (A : finType) (P : {fdist A}) (epsilon : Rdefinitions.R) (n : nat).

Lemma TS_sup : #| `TS P n epsilon |%:R <= 2 `^ (n%:R * (`H P + epsilon)).
Proof.
suff Htmp : #| `TS P n epsilon |%:R * 2 `^ (- n%:R * (`H P + epsilon)) <= 1.
  by rewrite -(mulr1 (2 `^ _)) mulrC -ler_pdivrMr // ?powR_gt0// -powRN// -mulNr.
rewrite -[leRHS](FDist.f1 (P `^ n)%fdist).
rewrite (_ : _ * _ = \sum_(x in `TS P n epsilon) (2 `^ (- n%:R * (`H P + epsilon)))); last first.
  by rewrite big_const iter_addr addr0 mulr_natl.
by apply: leR_sumRl => //= i; rewrite inE; case/andP.
Qed.

Lemma typ_seq_definition_equiv x : x \in `TS P n epsilon ->
  2 `^ (- n%:R * (`H P + epsilon)) <= (P `^ n)%fdist x <= 2 `^ (- n%:R * (`H P - epsilon)).
Proof. by rewrite inE /typ_seq => /andP[? ?]; apply/andP; split. Qed.

Lemma typ_seq_definition_equiv2 x : x \in `TS P n.+1 epsilon ->
  `H P - epsilon <= - n.+1%:R^-1 * log ((P `^ n.+1)%fdist x) <= `H P + epsilon.
Proof.
rewrite inE /typ_seq.
case/andP => H1 H2; apply/andP; split;
  rewrite -(@ler_pM2r _ n.+1%:R) ?ltr0n//.
- rewrite mulrAC mulNr mulVf; last by rewrite pnatr_eq0.
  rewrite mulN1r.
  rewrite lerNr.
  rewrite -ler_log ?posrE// in H2; last 2 first.
    by rewrite (lt_le_trans _ H1)// Exp_gt0//.
    by rewrite Exp_gt0.
  by rewrite mulNr powRN logV ?Exp_gt0// log_powR log2 mulr1 mulrC in H2.
- rewrite mulrAC mulNr mulVf; last by rewrite pnatr_eq0.
  have := FDist.ge0 ((P `^ n.+1)%fdist) x; rewrite le_eqVlt => /predU1P[H3|H3].
    have : 0 < 2 `^ (1 *- n.+1 * (`H P + epsilon)).
      by rewrite Exp_gt0//.
    rewrite -H3 in H1.
    by rewrite ltNge H1.
  rewrite mulN1r.
  rewrite lerNl.
  rewrite -ler_log ?posrE// in H1; last first.
    by rewrite Exp_gt0.
  by rewrite mulNr powRN logV ?Exp_gt0// log_powR log2 mulr1 mulrC in H1.
Qed.

End typ_seq_prop.

Section typ_seq_more_prop.
Variables (A : finType) (P : {fdist A}) (epsilon : Rdefinitions.R) (n : nat).

Hypothesis He : 0 < epsilon.

Lemma Pr_TS_1 : aep_bound P epsilon <= n.+1%:R ->
  1 - epsilon <= Pr (P `^ n.+1)%fdist (`TS P n.+1 epsilon).
Proof.
move=> k0_k.
have -> : Pr (P `^ n.+1)%fdist (`TS P n.+1 epsilon) =
  Pr (P `^ n.+1)%fdist [set i | (i \in `TS P n.+1 epsilon) && (0 < (P `^ n.+1)%fdist i)%mcR].
  congr Pr; apply/setP => /= t; rewrite !inE.
  apply/idP/andP => [H|]; [split => // | by case].
  case/andP : H => H _; apply/(lt_le_trans _ H).
  by rewrite Exp_gt0//.
set p := [set _ | _].
rewrite Pr_to_cplt lerD2l lerNl opprK.
have -> : Pr (P `^ n.+1)%fdist (~: p) =
  Pr (P `^ n.+1)%fdist [set x | (P `^ n.+1)%fdist x == 0] +
  Pr (P `^ n.+1)%fdist [set x | (0 < (P `^ n.+1)%fdist x)%mcR &&
                (`| - n.+1%:R^-1 * log ((P `^ n.+1)%fdist x) - `H P | > epsilon)%mcR].
  have -> : ~: p =
    [set x | (P `^ n.+1)%fdist x == 0 ] :|:
    [set x | (0 < (P `^ n.+1)%fdist x)%mcR &&
             (`| - n.+1%:R^-1 * log ((P `^ n.+1)%fdist x) - `H P | > epsilon)%mcR].
    apply/setP => /= i; rewrite !inE negb_and orbC.
    apply/idP/idP => [/orP[H|]|].
    - have {}H : (P `^ n.+1)%fdist i = 0.
        apply/eqP.
        apply/negPn.
        apply: contra H.
        by have [+ _] := fdist_gt0 (P `^ n.+1)%fdist i.
      by rewrite H eqxx.
    - rewrite /typ_seq negb_and => /orP[|] LHS.
      + have [//|H1] := eqVneq ((P `^ n.+1)%fdist i) 0.
        have {}H1 : 0 < (P `^ n.+1)%fdist i by rewrite lt0r H1/=.
        rewrite /= H1/=.
        move: LHS; rewrite -ltNge => /log_increasing => /(_ H1).
        rewrite log_powR mulNr log2 mulr1.
 mulN1r. mulrC. mulrN -mulNr -ltr_pdivr_mulr.
 

; last exact/ltR0n.
        rewrite /Rdiv mulRC ltR_oppr => /RltP; rewrite -ltrBrDl => LHS.
        rewrite div1r// mulNr -RinvE ger0_norm// -INRE//.
        by move/RltP : LHS; move/(ltR_trans He)/ltRW/RleP.
      + move: LHS; rewrite leNgt negbK => LHS.
        apply/orP; right; apply/andP; split.
          exact/(lt_trans _ LHS)/RltP/exp2_gt0.
        move/RltP in LHS.
        move/(@Log_increasing 2 _ _ Rlt_1_2 (exp2_gt0 _)) : LHS.
        rewrite /exp2 ExpK // mulRC mulRN -mulNR -ltR_pdivl_mulr; last exact/ltR0n.
        rewrite oppRD oppRK => LHS.
        have H2 : forall a b c, - a + b < c -> - c - a < - b by move=> *; lra.
        move/H2 in LHS.
        rewrite div1r mulrC mulrN ler0_norm//.
        * rewrite ltrNr//; apply/RltP; rewrite -RminusE -RoppE.
          by rewrite -RdivE ?gt_eqF// ?ltr0n// -INRE.
        * apply/RleP; rewrite -RminusE -RoppE.
          rewrite -RdivE ?gt_eqF// ?ltr0n// -INRE//.
          apply: (leR_trans (ltRW LHS)).
          by apply/RleP; rewrite lerNl oppr0// ltW//; apply/RltP.
    - rewrite -negb_and; apply: contraTN.
      rewrite negb_or /typ_seq => /andP[H1 /andP[/RleP H2 /RleP H3]].
      apply/andP; split; first exact/gtR_eqF/RltP.
      rewrite negb_and H1 /= -leNgt.
      move/(@Log_increasing_le 2 _ _ Rlt_1_2 (exp2_gt0 _)) : H2.
      rewrite /exp2 ExpK // mulRC mulRN -mulNR -leR_pdivl_mulr ?oppRD; last exact/ltR0n.
      move => H2.
      have /(_ _ _ _ H2) {}H2 : forall a b c, - a + - b <= c -> - c - a <= b.
        by move=> *; lra.
      move/RltP in H1.
      move/(@Log_increasing_le 2 _ _ Rlt_1_2 H1) : H3.
      rewrite /exp2 ExpK //.
      rewrite mulRC mulRN -mulNR -leR_pdivr_mulr; last exact/ltR0n.
      rewrite oppRD oppRK div1r mulrC mulrN => H3.
      have /(_ _ _ _ H3) {}H3 : forall a b c, a <= - c + b -> - b <= - a - c.
        by move=> *; lra.
      by rewrite ler_norml; apply/andP; split;
        apply/RleP; rewrite -RminusE -RoppE;
        rewrite -RdivE ?gt_eqF// ?ltr0n// -INRE//.
  rewrite disjoint_Pr_setU // disjoints_subset; apply/subsetP => /= i.
  by rewrite !inE /= => /eqP Hi; rewrite negb_and Hi ltxx.
rewrite {1}/Pr (eq_bigr (fun=> 0)); last by move=> /= v; rewrite inE => /eqP.
rewrite big_const iter_addR mulR0 add0R.
apply/(leR_trans _ (aep He k0_k))/subset_Pr/subsetP => /= t.
rewrite !inE /= => /andP[-> H3].
rewrite /log_RV /= /scalel_RV /= mulRN -mulNR.
apply/ltW.
by rewrite RmultE RoppE// RdivE ?gt_eqF ?INRE ?ltr0n.
Qed.

Variable He1 : epsilon < 1.

Lemma set_typ_seq_not0 : aep_bound P epsilon <= n.+1%:R ->
  #| `TS P n.+1 epsilon | <> O.
Proof.
move/Pr_TS_1 => H.
case/boolP : (#| `TS P n.+1 epsilon | == O) => [|Heq]; last by apply/eqP.
rewrite cards_eq0 => /eqP Heq.
rewrite Heq Pr_set0 in H.
lra.
Qed.

Definition TS_0 (H : aep_bound P epsilon <= n.+1%:R) : 'rV[A]_n.+1.
apply (@enum_val _ (pred_of_set (`TS P n.+1 epsilon))).
have -> : #| `TS P n.+1 epsilon| = #| `TS P n.+1 epsilon|.-1.+1.
  rewrite prednK //.
  move/set_typ_seq_not0 in H.
  rewrite lt0n; by apply/eqP.
exact ord0.
Defined.

Lemma TS_0_is_typ_seq (k_k0 : aep_bound P epsilon <= n.+1%:R) :
  TS_0 k_k0 \in `TS P n.+1 epsilon.
Proof. rewrite /TS_0. apply/enum_valP. Qed.

Lemma TS_inf : aep_bound P epsilon <= n.+1%:R ->
  (1 - epsilon) * exp2 (n.+1%:R * (`H P - epsilon)) <= #| `TS P n.+1 epsilon |%:R.
Proof.
move=> k0_k.
have H1 : (1 - epsilon <= Pr (P `^ n.+1) (`TS P n.+1 epsilon) <= 1)%mcR.
  by apply/andP; split; apply/RleP; [exact: Pr_TS_1 | exact: Pr_le1].
have H2 : (forall x, x \in `TS P n.+1 epsilon ->
    exp2 (- n.+1%:R * (`H P + epsilon)) <=
    P `^ n.+1 x <= exp2 (- n.+1%:R * (`H P - epsilon)))%mcR.
  by move=> x; rewrite inE /typ_seq => /andP[-> ->].
have /RltP H3 := exp2_gt0 (- n.+1%:R * (`H P + epsilon)).
have /RltP H5 := exp2_gt0 (- n.+1%:R * (`H P - epsilon)).
have := wolfowitz H3 H5 H1 H2.
rewrite mulNR exp2_Ropp.
rewrite RinvE ?gtR_eqF// invrK => /andP[] /RleP.
by rewrite -!RmultE -RminusE -INRE.
(* TODO: clean *)
Qed.

End typ_seq_more_prop.
