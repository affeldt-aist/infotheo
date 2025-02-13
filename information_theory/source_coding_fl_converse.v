(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix lra ring.
From mathcomp Require Import Rstruct reals exp.
Require Import realType_ext realType_ln fdist proba entropy aep.
Require Import typ_seq source_code.

(**md**************************************************************************)
(* # Source coding theorem (fixed length, converse part)                      *)
(*                                                                            *)
(* The main lemma is `source_coding_converse`.                                *)
(*                                                                            *)
(* Documented in:                                                             *)
(* - Reynald Affeldt, Manabu Hagiwara, and Jonas Sénizergues. Formalization   *)
(*   of Shannon's theorems. Journal of Automated Reasoning, 53(1):63--103,    *)
(*   2014                                                                     *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope source_code_scope.
Local Open Scope entropy_scope.
Local Open Scope reals_ext_scope.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import Order.POrderTheory GRing.Theory Num.Theory Num.Def Order.TotalTheory.

(* TODO: move *)
Lemma minr_case_strong (R : realType) (r1 r2 : R)
  (P : R -> Prop) :
  (r1 <= r2 -> P r1) ->
(r2 <= r1 -> P r2) -> P (minr r1 r2).
Proof.
move=> H1 H2.
rewrite /minr.
case: ifPn => r12.
  apply: H1.
  exact: ltW.
apply: H2.
by rewrite leNgt.
Qed.

Section source_coding_converse'.
Let R := Rdefinitions.R.
Variables (A : finType) (P : {fdist A}).
Variables num den : nat.
Let r : R := num%:R / den.+1%:R.
Hypothesis Hr : 0 < r < `H P.

Variable n : nat.
Variable k : nat.
Variable sc : scode_fl A k.+1 n.
Hypothesis r_sc : r = SrcRate sc.

Variable epsilon : R.
Hypothesis Hepsilon : 0 < epsilon < 1.

Local Notation "'max(' x ',' y ')'" := (maxr x y) : reals_ext_scope.

Definition lambda := minr ((1 - epsilon) / 2) ((`H P - r) / 2).
Definition delta := minr ((`H P - r) / 2) (lambda / 2).

Definition SrcConverseBound := max(max(
  aep_bound P delta, - ((log delta) / (`H P - r - delta))), n%:R / r).

Hypothesis Hk : SrcConverseBound <= k.+1%:R.

Lemma Hr1 : 0 < (`H P - r) / 2.
Proof.
apply divr_gt0; last lra.
by case/andP: Hr => ? ?; lra.
Qed.

Lemma Hepsilon1 : 0 < (1 - epsilon) / 2.
Proof.
apply divr_gt0; last lra.
by case/andP: Hepsilon => ? ?; lra.
Qed.

Lemma lambda0 : 0 < lambda.
Proof.
by rewrite /lambda lt_min; apply/andP; split; [exact Hepsilon1 | exact Hr1].
Qed.

Lemma Hdelta : (0 < delta)%mcR.
Proof.
rewrite /delta.
rewrite lt_min.
apply/andP; split.
case/andP: Hr => ? ?; apply divr_gt0; lra.
apply divr_gt0; [exact lambda0 | lra].
Qed.

Definition e0 := `H P - r.

Lemma e0_delta : e0 <> delta.
Proof.
rewrite /e0 /delta /lambda -/r.
apply/eqP.
apply: (@minr_case_strong _ ((`H P - r) / 2) (minr ((1 - epsilon) / 2) ((`H P - r) / 2) / 2) (fun x => `H P - r != x)) => H1.
  case/andP : Hr => ? ?.
  lra.
apply: (@minr_case_strong _ ((1 - epsilon) / 2) (((`H P - r) / 2)) ((fun x => `H P - r != x / 2))) => H2.
- rewrite gt_eqF//; apply: le_lt_trans.
  + apply: (le_trans _ H2).
    rewrite ler_pdivrMr // ler_pMr ?ler1n// divr_gt0// subr_gt0.
    by case/andP : Hepsilon.
  + rewrite ltr_pdivrMr //.
    case/andP : Hr => ? ?.
    lra.
- case/andP : Hr => ? ?.
  lra.
Qed.

Definition no_failure := [set x : 'rV[A]_k.+1 | dec sc (enc sc x) == x].

Lemma no_failure_sup : #| no_failure |%:R <= ((2:R) `^ (k.+1%:R * (`H P - e0)))%R.
Proof.
apply (@le_trans _ _ (2%R `^ n%:R)%R).
  rewrite /no_failure.
  have Hsubset : [set x | dec sc (enc sc x) == x] \subset dec sc @: (enc sc @: [set: 'rV[A]_k.+1]).
    apply/subsetP => x; rewrite inE => /eqP Hx.
    by apply/imsetP; exists (enc sc x) => //; rewrite imset_f.
  apply (@le_trans _ _ #| dec sc @: (enc sc @: [set: 'rV[A]_k.+1]) |%:R).
    by rewrite ler_nat; case/subset_leqif_cards : Hsubset.
  apply (@le_trans _ _ #| dec sc @: [set: 'rV[bool]_n] |%:R).
    by rewrite ler_nat; apply/subset_leqif_cards/imsetS/subsetP => x Hx; rewrite inE.
  apply (@le_trans _ _ #| [set: 'rV[bool]_n] |%:R).
    by rewrite ler_nat; exact/leq_imset_card.
  rewrite cardsT card_mx /= card_bool mul1n.
  by rewrite powR_mulrn// natrX.
rewrite gt1_ler_powRr ?ltr1n//.
rewrite /e0 [X in _ <= _ * X](_ : _ = r); last by field.
rewrite -(@ler_pM2r _ (r^-1)) => //; last first.
  by rewrite invr_gt0//; case/andP : Hr.
rewrite -mulrA mulfV ?mulr1; last first.
  by case/andP : Hr => r0 _; rewrite gt_eqF.
rewrite (le_trans _ Hk)//.
by rewrite /SrcConverseBound le_max lexx orbT.
Qed.

Local Open Scope fdist_scope.

Lemma step1 : (1 - esrc(P , sc)) = \sum_(x in no_failure) (P `^ k.+1)%fdist x.
Proof.
rewrite /SrcErrRate /no_failure /Pr.
set a := \sum_(_ | _) _.
set b := \sum_(_ | _) _.
suff : 1 = a + b by move=> ->; field.
rewrite /a {a}.
have -> : b = \sum_(i in [set i | dec sc (enc sc i) == i]) (P `^ k.+1)%fdist i.
  by apply eq_big => // i /=; rewrite inE.
rewrite -(FDist.f1 (P `^ k.+1)).
rewrite (bigID [pred a | a \in [set i0 | dec sc (enc sc i0) == i0]]) /= addrC.
by congr (_ + _); apply eq_bigl => t /=; rewrite !inE.
Qed.

Local Open Scope typ_seq_scope.

Lemma step2 : 1 - (esrc(P , sc)) =
  \sum_(x in 'rV[A]_k.+1 | x \in no_failure :&: ~: `TS P k.+1 delta) (P `^ k.+1)%fdist x +
  \sum_(x in 'rV[A]_k.+1 | x \in no_failure :&: `TS P k.+1 delta) (P `^ k.+1)%fdist x.
Proof.
rewrite step1 (bigID [pred x | x \in `TS P k.+1 delta]) /= addrC.
f_equal.
- by apply eq_bigl => x; rewrite in_setI in_setC.
- by apply eq_bigl => x; rewrite in_setI.
Qed.

Lemma step3 : 1 - (esrc(P , sc)) <=
  \sum_(x in 'rV[A]_k.+1 | x \in ~: `TS P k.+1 delta) (P `^ k.+1)%fdist x +
  \sum_(x in 'rV[A]_k.+1 | x \in no_failure :&: `TS P k.+1 delta) (P `^ k.+1)%fdist x.
Proof.
rewrite step2 lerD2r//.
apply: bigop_ext.ler_suml => //= i.
by rewrite in_setI => /andP[].
Qed.

Lemma step4 : 1 - (esrc(P , sc)) <= delta +
  #| no_failure :&: `TS P k.+1 delta|%:R * 2 `^ (- k.+1%:R * (`H P - delta)).
Proof.
apply/(le_trans step3); rewrite lerD//.
- move: Hk.
  rewrite !ge_max => /andP[] /andP[].
  move/(Pr_TS_1 Hdelta) => Hdelta _ _.
  rewrite -[in X in _ <= X](opprK delta) lerNr -(@lerD2l _ 1).
  apply: (le_trans Hdelta).
  by rewrite Pr_to_cplt lexx.
- apply (@le_trans _ _
    (\sum_(x in 'rV[A]_k.+1 | x \in no_failure :&: `TS P k.+1 delta)
      2 `^ (- k.+1%:R * (`H P - delta)))); last first.
    by rewrite big_const iter_addr mulr_natl addr0.
  apply ler_sum => /= i.
  rewrite in_setI => /andP[i_B i_TS].
  move: (typ_seq_definition_equiv2 i_TS) => /andP[+ _].
  rewrite -[in X in X -> _](@ler_nM2l _ (- (k.+1%:R))); last first.
    by rewrite ltrNl oppr0 ltr0n.
  rewrite mulrA mulrN !mulNr opprK divff ?pnatr_eq0// mul1r => H2.
  have := FDist.ge0 (P `^ k.+1) i.
  rewrite le_eqVlt => /predU1P[<-|Pki0]; first by rewrite powR_ge0.
  rewrite -ler_log ?posrE ?powR_gt0//.
  by rewrite log_powR log2 mulr1.
Qed.

Lemma step5 : 1 - (esrc(P , sc)) <= delta + 2 `^ (- k.+1%:R * (e0 - delta)).
Proof.
apply (@le_trans _ _ (delta + #| no_failure |%:R * 2 `^ (- k.+1%:R * (`H P - delta)))).
- apply/(le_trans step4); rewrite lerD2l ler_wpM2r ?powR_ge0// ler_nat.
  exact/subset_leqif_cards/subsetIl.
- rewrite lerD2l.
  apply (@le_trans _ _ (2 `^ (k.+1%:R * (`H P - e0)) * 2 `^ (- k.+1%:R * (`H P - delta))));
    last first.
    rewrite -powRD; last by rewrite pnatr_eq0 implybT.
    by rewrite gt1_ler_powRr ?ltr1n//; lra.
  by rewrite ler_wpM2r ?powR_ge0//; exact: no_failure_sup.
Qed.

Lemma step6 : 1 - 2 * delta <= esrc(P , sc).
Proof.
have H : (2 `^ (- k.+1%:R * (e0 - delta)) <= delta)%R; last first.
  suff : 1 - (esrc(P , sc)) <= delta + delta by move=> *; lra.
  by apply/(le_trans step5); rewrite lerD2l.
rewrite -ler_log ?posrE ?powR_gt0 ?Hdelta//.
rewrite log_powR log2 mulr1.
rewrite -(@ler_pM2r _ ((e0 - delta)^-1)) ?invr_gt0 ?subr_gt0//; last first.
  rewrite /e0 /delta /r.
  have H1 : (`H P - r) / 2 < `H P - r.
    rewrite -[X in _ < X]mulr1.
    rewrite ltr_pM2l ?subr_gt0 ?invf_lt1 ?ltr1n//.
    by case/andP : Hr.
    apply: (@minr_case_strong _ ((`H P - num%:R / den.+1%:R) / 2) (lambda / 2) (fun x => x < `H P - num%:R / den.+1%:R)) => H2.
      exact: H1.
    by rewrite (le_lt_trans H2)//.
rewrite -mulrA mulfV ?subr_eq0//; last first.
  apply/eqP.
  exact: e0_delta.
rewrite mulNr mulr1 lerNl.
by move: Hk; rewrite !ge_max => /andP[/andP[]].
Qed.

Theorem source_coding_converse' : epsilon <= esrc(P , sc).
Proof.
apply: (le_trans _ step6).
rewrite -[X in _ <= X]opprK lerNr opprB lerBlDr addrC.
rewrite -(@ler_pM2l _ (2^-1)%R) ?invr_gt0//.
rewrite mulrA mulVf ?mul1r /delta ?pnatr_eq0//.
have H1 : lambda / 2 <= 2^-1 * (1 - epsilon).
  apply (@le_trans _ _ lambda).
    by rewrite ler_pdivrMr// ler_peMr// ?ler1n// ltW// lambda0.
  by rewrite /lambda mulrC ge_min lexx.
apply: (@minr_case_strong _ ((`H P - r) / 2) (lambda / 2)
  (fun x => x <= 2^-1 * (1 - epsilon))) => //.
by move/le_trans; exact.
Qed.

End source_coding_converse'.

Section source_coding_converse.
Variables (A : finType) (P : {fdist A}).

Theorem source_coding_converse epsilon : 0 < epsilon < 1 ->
  forall nu de : nat, 0 < (nu%:R / de.+1%:R : Rdefinitions.R) < `H P ->
    forall n k (sc : scode_fl A k.+1 n),
      SrcRate sc = nu%:R / de%:R ->
      SrcConverseBound P nu de n epsilon <= k.+1%:R ->
      epsilon <= esrc(P , sc).
Proof.
move=> espilon01 nu de r_HP n k sc r_sc Hk_bound.
exact: (@source_coding_converse' _ _ nu de).
Qed.

End source_coding_converse.
