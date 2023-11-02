(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix.
Require Import Reals Lra.
From mathcomp Require Import Rstruct.
Require Import ssrR Reals_ext realType_ext logb Rbigop.
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

Local Open Scope R_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section typical_sequence_definition.

Variables (A : finType) (P : {fdist A}) (n : nat) (epsilon : R).

Definition typ_seq (t : 'rV[A]_n) :=
  (exp2 (- n%:R * (`H P + epsilon)) <= P `^ n t <= exp2 (- n%:R * (`H P - epsilon)))%mcR.

Definition set_typ_seq := [set ta | typ_seq ta].

End typical_sequence_definition.

Notation "'`TS'" := (set_typ_seq) : typ_seq_scope.

Local Open Scope typ_seq_scope.

Lemma set_typ_seq_incl (A : finType) (P : {fdist A}) n epsilon : 0 <= epsilon -> forall r, 1 <= r ->
  `TS P n (epsilon / 3) \subset `TS P n epsilon.
Proof.
move=> e0 r r1.
apply/subsetP => /= x.
rewrite !inE /typ_seq => /andP[/leRP H2 /leRP H3] [:Htmp].
apply/andP; split; apply/leRP.
- apply/(leR_trans _ H2)/Exp_le_increasing => //.
  rewrite !mulNR leR_oppr oppRK; apply leR_wpmul2l; first exact/leR0n.
  apply/leR_add2l.
  abstract: Htmp.
  rewrite leR_pdivr_mulr; [apply leR_pmulr => //|]; lra.
- apply/(leR_trans H3)/Exp_le_increasing => //.
  rewrite !mulNR leR_oppr oppRK; apply leR_wpmul2l; first exact/leR0n.
  apply leR_add2l; rewrite leR_oppr oppRK; exact Htmp.
Qed.

Section typ_seq_prop.

Variables (A : finType) (P : {fdist A}) (epsilon : R) (n : nat).

Lemma TS_sup : #| `TS P n epsilon |%:R <= exp2 (n%:R * (`H P + epsilon)).
Proof.
suff Htmp : #| `TS P n epsilon |%:R * exp2 (- n%:R * (`H P + epsilon)) <= 1.
  by rewrite -(mulR1 (exp2 _)) mulRC -leR_pdivr_mulr // /Rdiv -exp2_Ropp -mulNR.
rewrite (_ : 1 = 1%mcR)// -(FDist.f1 (P `^ n)).
rewrite (_ : _ * _ = \sum_(x in `TS P n epsilon) (exp2 (- n%:R * (`H P + epsilon)))); last first.
  by rewrite big_const iter_addR.
by apply/leR_sumRl => //= i; rewrite inE; case/andP => /leRP.
Qed.

Lemma typ_seq_definition_equiv x : x \in `TS P n epsilon ->
  exp2 (- n%:R * (`H P + epsilon)) <= P `^ n x <= exp2 (- n%:R * (`H P - epsilon)).
Proof. by rewrite inE /typ_seq => /andP[? ?]; split; apply/leRP. Qed.

Lemma typ_seq_definition_equiv2 x : x \in `TS P n.+1 epsilon ->
  `H P - epsilon <= - (1 / n.+1%:R) * log (P `^ n.+1 x) <= `H P + epsilon.
Proof.
rewrite inE /typ_seq.
case/andP => H1 H2; split;
  apply/leRP; rewrite -(leR_pmul2l' n.+1%:R) ?ltR0n' //;
  rewrite div1R mulRA mulRN mulRV ?INR_eq0' // mulN1R; apply/leRP.
- rewrite leR_oppr.
  apply/(@Exp_le_inv 2) => //.
  rewrite LogK //; last by apply/(ltR_leR_trans (exp2_gt0 _)); apply/leRP: H1.
  apply/leRP; by rewrite -mulNR.
- rewrite leR_oppl.
  apply/(@Exp_le_inv 2) => //.
  rewrite LogK //; last by apply/(ltR_leR_trans (exp2_gt0 _)); apply/leRP: H1.
  apply/leRP; by rewrite -mulNR.
Qed.

End typ_seq_prop.

Section typ_seq_more_prop.

Variables (A : finType) (P : {fdist A}) (epsilon : R) (n : nat).

Hypothesis He : 0 < epsilon.

Import Order.TTheory.

Lemma Pr_TS_1 : aep_bound P epsilon <= n.+1%:R ->
  1 - epsilon <= Pr (P `^ n.+1) (`TS P n.+1 epsilon).
Proof.
move=> k0_k.
have -> : Pr P `^ n.+1 (`TS P n.+1 epsilon) =
  Pr P `^ n.+1 [set i | (i \in `TS P n.+1 epsilon) && (0 < P `^ n.+1 i)%mcR].
  congr Pr; apply/setP => /= t; rewrite !inE.
  apply/idP/andP => [H|]; [split => // | by case].
  case/andP : H => /leRP H _; exact/RltP/(ltR_leR_trans (exp2_gt0 _) H).
set p := [set _ | _].
rewrite Pr_to_cplt leR_add2l leR_oppl oppRK.
have -> : Pr P `^ n.+1 (~: p) =
  Pr P `^ n.+1 [set x | P `^ n.+1 x == 0] +
  Pr P `^ n.+1 [set x | (0 < P `^ n.+1 x)%mcR &&
                (`| - (1 / n.+1%:R) * log (P `^ n.+1 x) - `H P | > epsilon)%mcR].
  have -> : ~: p =
    [set x | P `^ n.+1 x == 0 ] :|:
    [set x | (0 < P `^ n.+1 x)%mcR &&
             (`| - (1 / n.+1%:R) * log (P `^ n.+1 x) - `H P | > epsilon)%mcR].
    apply/setP => /= i; rewrite !inE negb_and orbC.
    apply/idP/idP => [/orP[/RltP|]|].
    - move/RltP => H.
      have {}H : P `^ n.+1 i = 0.
        apply/eqP.
        apply/negPn.
        apply: contra H.
        by have [+ _] := fdist_gt0 (P `^ n.+1) i.
      by rewrite H eqxx.
    - rewrite /typ_seq negb_and => /orP[|] LHS.
      + case/boolP : (P `^ n.+1 i == 0) => /= H1; first by [].
        have {}H1 : 0 < P `^ n.+1 i.
          apply/ltRP; rewrite ltR_neqAle' eq_sym H1; exact/leRP.
        apply/andP; split; first exact/RltP.
        move: LHS; rewrite -ltRNge' => /ltRP/(@Log_increasing 2 _ _ Rlt_1_2 H1).
        rewrite /exp2 ExpK // mulRC mulRN -mulNR -ltR_pdivr_mulr; last exact/ltR0n.
        rewrite /Rdiv mulRC ltR_oppr => /RltP; rewrite -Num.Theory.ltrBrDl => LHS.
        rewrite GRing.div1r// GRing.mulNr -RinvE//; last first.
          by rewrite gt_eqF// Num.Theory.ltr0n.
        rewrite Num.Theory.ger0_norm// -INRE//.
        by move/RltP : LHS; move/(ltR_trans He)/ltRW/RleP.
      + move: LHS; rewrite leNgt negbK => LHS.
        apply/orP; right; apply/andP; split.
          apply/(lt_trans _ LHS).
          apply/RltP.
          exact: exp2_gt0.
        move/RltP in LHS.
        move/(@Log_increasing 2 _ _ Rlt_1_2 (exp2_gt0 _)) : LHS.
        rewrite /exp2 ExpK // mulRC mulRN -mulNR -ltR_pdivl_mulr; last exact/ltR0n.
        rewrite oppRD oppRK => LHS.
        have H2 : forall a b c, - a + b < c -> - c - a < - b by move=> *; lra.
        move/H2 in LHS.
        rewrite GRing.div1r GRing.mulrC GRing.mulrN Num.Theory.ler0_norm//.
        * rewrite Num.Theory.ltr_oppr//; apply/RltP; rewrite -RminusE -RoppE.
          by rewrite -RdivE ?gt_eqF// ?Num.Theory.ltr0n// -INRE.
        * apply/RleP; rewrite -RminusE -RoppE.
          rewrite -RdivE ?gt_eqF// ?Num.Theory.ltr0n// -INRE//.
          apply: (leR_trans (ltRW LHS)).
          apply/RleP.
          by rewrite Num.Theory.lerNl GRing.oppr0// ltW//; apply/RltP.
    - rewrite -negb_and; apply: contraTN.
      rewrite negb_or /typ_seq => /andP[H1 /andP[/leRP H2 /leRP H3]].
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
      rewrite oppRD oppRK GRing.div1r GRing.mulrC GRing.mulrN => H3.
      have /(_ _ _ _ H3) {}H3 : forall a b c, a <= - c + b -> - b <= - a - c.
        by move=> *; lra.
      apply/leRP/RleP.
      by rewrite leR_Rabsl; apply/andP; split;
        apply/RleP; rewrite -RminusE -RoppE;
        rewrite -RdivE ?gt_eqF// ?Num.Theory.ltr0n// -INRE//.
  rewrite Pr_union_disj // disjoints_subset; apply/subsetP => /= i.
  rewrite !inE /= => /eqP Hi; by rewrite negb_and Hi ltxx.
rewrite {1}/Pr (eq_bigr (fun=> 0)); last by move=> /= v; rewrite inE => /eqP.
rewrite big_const iter_addR mulR0 add0R.
apply/(leR_trans _ (aep He k0_k))/Pr_incl/subsetP => /= t.
rewrite !inE /= => /andP[-> H3].
rewrite /log_RV /= /scalel_RV /= mulRN -mulNR.
apply/ltW.
by rewrite RmultE RoppE// RdivE// ?gt_eqF// ?INRE// ?Num.Theory.ltr0n//.
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

Definition TS_0 (H : aep_bound P epsilon <= n.+1%:R) : [finType of 'rV[A]_n.+1].
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
  by apply/andP; split; apply/RleP; [exact: Pr_TS_1 | exact: Pr_1].
have H2 : (forall x, x \in `TS P n.+1 epsilon ->
  exp2 (- n.+1%:R * (`H P + epsilon)) <= P `^ n.+1 x <= exp2 (- n.+1%:R * (`H P - epsilon)))%mcR.
  by move=> x; rewrite inE /typ_seq => /andP[/leRP/RleP -> /leRP/RleP ->].
have /RltP H3 := exp2_gt0 (- n.+1%:R * (`H P + epsilon)).
have /RltP H5 := exp2_gt0 (- n.+1%:R * (`H P - epsilon)).
have := wolfowitz H3 H5 H1 H2.
rewrite mulNR exp2_Ropp.
rewrite RinvE ?gtR_eqF//.
rewrite GRing.invrK => /andP[] /leRP.
rewrite -!RmultE -RminusE -INRE.
by rewrite {1}(_ : 1%mcR = 1)//.
(* TODO: clean *)
Qed.

End typ_seq_more_prop.
