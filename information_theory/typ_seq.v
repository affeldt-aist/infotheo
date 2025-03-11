(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix lra.
From mathcomp Require Import reals exp.
Require Import ssr_ext realType_ext realType_ln fdist proba entropy aep.

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
Context {R : realType}.
Variables (A : finType) (P : R.-fdist A) (n : nat) (epsilon : R).

Definition typ_seq (t : 'rV[A]_n) :=
  2 `^ (- n%:R * (`H P + epsilon)) <= (P `^ n)%fdist t <=
  2 `^ (- n%:R * (`H P - epsilon)).

Definition set_typ_seq := [set ta | typ_seq ta].

End typical_sequence_definition.

Notation "'`TS'" := (set_typ_seq) : typ_seq_scope.

Local Open Scope typ_seq_scope.

Lemma set_typ_seq_incl {R : realType} (A : finType) (P : R.-fdist A) n epsilon :
  0 <= epsilon -> `TS P n (epsilon / 3) \subset `TS P n epsilon.
Proof.
move=> e0.
apply/subsetP => /= x.
rewrite !inE /typ_seq => /andP[H2 H3] [:e3e].
apply/andP; split.
- apply/(le_trans _ H2).
  rewrite ler_powR ?ler1n// !mulNr lerNr opprK; apply ler_wpM2l => //.
  rewrite lerD2l//.
  abstract: e3e.
  by rewrite ler_pdivrMr// ler_peMr//; lra.
- apply/(le_trans H3); rewrite ler_powR// ?ler1n//.
  rewrite !mulNr lerNr opprK; apply ler_wpM2l => //.
  by rewrite lerD2l lerNr opprK; exact e3e.
Qed.

Section typ_seq_prop.
Context {R : realType}.
Variables (A : finType) (P : R.-fdist A) (epsilon : R) (n : nat).

Lemma TS_sup : #| `TS P n epsilon |%:R <= 2 `^ (n%:R * (`H P + epsilon)).
Proof.
suff Htmp : #| `TS P n epsilon |%:R * 2 `^ (- n%:R * (`H P + epsilon)) <= 1.
  by rewrite -(mulr1 (2 `^ _)) mulrC -ler_pdivrMr// ?powR_gt0// -powRN// -mulNr.
rewrite -[leRHS](FDist.f1 (P `^ n)%fdist).
rewrite (_ : _ * _ =
    \sum_(x in `TS P n epsilon) (2 `^ (- n%:R * (`H P + epsilon)))); last first.
  by rewrite big_const iter_addr addr0 mulr_natl.
by apply: leR_sumRl => //= i; rewrite inE; case/andP.
Qed.

Lemma typ_seq_definition_equiv x : x \in `TS P n epsilon ->
  2 `^ (- n%:R * (`H P + epsilon)) <= (P `^ n)%fdist x <=
  2 `^ (- n%:R * (`H P - epsilon)).
Proof. by rewrite inE /typ_seq => /andP[? ?]; apply/andP; split. Qed.

Lemma typ_seq_definition_equiv2 x : x \in `TS P n.+1 epsilon ->
  `H P - epsilon <= - n.+1%:R^-1 * log ((P `^ n.+1)%fdist x) <= `H P + epsilon.
Proof.
rewrite inE /typ_seq => /andP[H1 H2]; apply/andP; split;
  rewrite -(@ler_pM2r _ n.+1%:R) ?ltr0n//.
- rewrite mulrAC mulNr mulVf; last by rewrite pnatr_eq0.
  rewrite mulN1r.
  rewrite lerNr.
  rewrite -ler_log ?posrE// in H2; last 2 first.
    by rewrite (lt_le_trans _ H1)// powR_gt0.
    by rewrite powR_gt0.
  by rewrite mulNr powRN logV ?powR_gt0// log_powR log2 mulr1 mulrC in H2.
- rewrite mulrAC mulNr mulVf; last by rewrite pnatr_eq0.
  have := FDist.ge0 ((P `^ n.+1)%fdist) x; rewrite le_eqVlt => /predU1P[H3|H3].
    have : 0 < 2 `^ (1 *- n.+1 * (`H P + epsilon)) by rewrite powR_gt0.
    rewrite -H3 in H1.
    by rewrite ltNge H1.
  rewrite mulN1r.
  rewrite lerNl.
  rewrite -ler_log ?posrE ?powR_gt0// in H1.
  by rewrite mulNr powRN logV ?powR_gt0// log_powR log2 mulr1 mulrC in H1.
Qed.

End typ_seq_prop.

Section typ_seq_more_prop.
Context {R : realType}.
Variables (A : finType) (P : R.-fdist A) (epsilon : R) (n : nat).

Hypothesis He : 0 < epsilon.

Lemma Pr_TS_1 : aep_bound P epsilon <= n.+1%:R ->
  1 - epsilon <= Pr (P `^ n.+1)%fdist (`TS P n.+1 epsilon).
Proof.
move=> k0_k.
have -> : Pr (P `^ n.+1)%fdist (`TS P n.+1 epsilon) =
  Pr (P `^ n.+1)%fdist [set i | (i \in `TS P n.+1 epsilon) && (0 < (P `^ n.+1)%fdist i)].
  congr Pr; apply/setP => /= t; rewrite !inE.
  apply/idP/andP => [H|]; [split => // | by case].
  by case/andP : H => H _; apply/(lt_le_trans _ H); rewrite powR_gt0.
set p := [set _ | _].
rewrite Pr_to_cplt lerD2l lerNl opprK.
have -> : Pr (P `^ n.+1)%fdist (~: p) =
  Pr (P `^ n.+1)%fdist [set x | (P `^ n.+1)%fdist x == 0] +
  Pr (P `^ n.+1)%fdist [set x | (0 < (P `^ n.+1)%fdist x) &&
                (`| - n.+1%:R^-1 * log ((P `^ n.+1)%fdist x) - `H P | > epsilon)].
  have -> : ~: p =
    [set x | (P `^ n.+1)%fdist x == 0 ] :|:
    [set x | (0 < (P `^ n.+1)%fdist x) &&
             (`| - n.+1%:R^-1 * log ((P `^ n.+1)%fdist x) - `H P | > epsilon)].
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
        move: LHS; rewrite -ltNge => /ltr_log => /(_ H1).
        rewrite log_powR mulNr log2 mulr1 -mulrN -ltr_pdivrMl// opprD.
        rewrite ltrBrDl -ltrBrDr addrC => /lt_le_trans; apply.
        by rewrite mulNr ler_norm.
      + move: LHS; rewrite leNgt negbK => LHS.
        apply/orP; right; apply/andP; split.
          exact/(lt_trans _ LHS)/powR_gt0.
        have : 0 < 2 `^ (1 *- n.+1 * (`H P - epsilon)) by exact/powR_gt0.
        move/ltr_log : LHS => /[apply].
        rewrite log_powR log2 mulr1 -ltr_ndivrMl; last first.
          by rewrite oppr_lt0 ltr0n.
        rewrite -ltrN2 opprB ltrBlDr => /lt_le_trans; apply.
        rewrite addrC -opprB mulNr opprB -[in leRHS]opprD normrN.
        by rewrite invrN mulNr opprK addrC ler_norm.
    - rewrite -negb_and; apply: contraTN.
      rewrite negb_or /typ_seq => /andP[H1 /andP[H2 H3]].
      rewrite gt_eqF//= negb_and H1 /= -leNgt.
      have : 0 < 2 `^ (1 *- n.+1 * (`H P + epsilon)) by exact/powR_gt0.
      move/log_increasing_le : H2 => /[apply] /=.
      rewrite log_powR log2 mulr1 -ler_ndivrMl; last by rewrite oppr_lt0 ltr0n.
      rewrite -lerBlDl invrN => H2.
      rewrite ler_norml H2 andbT.
      move/log_increasing_le : H3 => /(_ H1).
      rewrite log_powR log2 mulr1 -ler_ndivlMl; last by rewrite oppr_lt0 ltr0n.
      by rewrite invrN addrC -{1}(opprK (`H P)) lerBlDr.
  rewrite disjoint_Pr_setU // disjoints_subset; apply/subsetP => /= i.
  by rewrite !inE /= => /eqP Hi; rewrite negb_and Hi ltxx.
rewrite {1}/Pr big1 ?add0r; last by move=> /= v; rewrite inE => /eqP.
apply/(le_trans _ (aep He k0_k))/subset_Pr/subsetP => /= t.
rewrite !inE /= => /andP[-> H3].
by rewrite /log_RV /= /scalel_RV /= mulrN -mulNr ltW.
Qed.

Variable He1 : epsilon < 1.

Lemma set_typ_seq_not0 : aep_bound P epsilon <= n.+1%:R ->
  #| `TS P n.+1 epsilon | != O.
Proof.
move/Pr_TS_1 => H.
have [/eqP|//] := eqVneq (#| `TS P n.+1 epsilon |) O.
rewrite cards_eq0 => /eqP Heq.
rewrite Heq Pr_set0 in H.
exfalso.
move: H; apply/negP.
by rewrite -ltNge subr_gt0.
Qed.

Definition TS_0 (H : aep_bound P epsilon <= n.+1%:R) : 'rV[A]_n.+1.
apply (@enum_val _ (pred_of_set (`TS P n.+1 epsilon))).
have -> : #| `TS P n.+1 epsilon| = #| `TS P n.+1 epsilon|.-1.+1.
  rewrite prednK //.
  move/set_typ_seq_not0 in H.
  by rewrite lt0n.
exact ord0.
Defined.

Lemma TS_0_is_typ_seq (k_k0 : aep_bound P epsilon <= n.+1%:R) :
  TS_0 k_k0 \in `TS P n.+1 epsilon.
Proof. rewrite /TS_0. apply/enum_valP. Qed.

Lemma TS_inf : aep_bound P epsilon <= n.+1%:R ->
  (1 - epsilon) * 2 `^ (n.+1%:R * (`H P - epsilon)) <= #| `TS P n.+1 epsilon |%:R.
Proof.
move=> k0_k.
have H1 : 1 - epsilon <= Pr (P `^ n.+1)%fdist (`TS P n.+1 epsilon) <= 1.
  by rewrite Pr_TS_1//= Pr_le1.
have H2 : forall x, x \in `TS P n.+1 epsilon ->
    2 `^ (- n.+1%:R * (`H P + epsilon)) <=
    (P `^ n.+1)%fdist x <= 2 `^ (- n.+1%:R * (`H P - epsilon)).
  by move=> x; rewrite inE /typ_seq => /andP[-> ->].
have O2 : 0 < 2 :> R by lra.
have H3 := powR_gt0 (- n.+1%:R * (`H P + epsilon)) O2.
have H5 := powR_gt0 (- n.+1%:R * (`H P - epsilon)) O2.
have := wolfowitz H3 H5 H1 H2.
by rewrite mulNr powRN invrK => /andP[].
Qed.

End typ_seq_more_prop.
