(* infotheo: information theory and error-correcting codes in Coq               *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later              *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg matrix.
Require Import Reals Lra.
Require Import ssrR Reals_ext logb Rbigop fdist proba entropy aep typ_seq.
Require Import source_code.

(******************************************************************************)
(*         Source coding theorem (fixed length, converse part)                *)
(*                                                                            *)
(* For details, see Reynald Affeldt, Manabu Hagiwara, and Jonas Sénizergues.  *)
(* Formalization of Shannon's theorems. Journal of Automated Reasoning,       *)
(* 53(1):63--103, 2014                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope source_code_scope.
Local Open Scope entropy_scope.
Local Open Scope reals_ext_scope.
Local Open Scope R_scope.

Section source_coding_converse'.

Variables (A : finType) (P : fdist A).
Variables num den : nat.
Let r := num%:R / den.+1%:R.
Hypothesis Hr : 0 < r < `H P.

Variable n : nat.
Variable k : nat.
Variable sc : scode_fl A k.+1 n.
Hypothesis r_sc : r = SrcRate sc.

Variable epsilon : R.
Hypothesis Hepsilon : 0 < epsilon < 1.

Local Notation "'max(' x ',' y ')'" := (Rmax x y) : reals_ext_scope.

Definition lambda := min((1 - epsilon) / 2, (`H P - r) / 2).
Definition delta := min((`H P - r) / 2, lambda / 2).

Definition SrcConverseBound := max(max(
  aep_bound P delta, - ((log delta) / (`H P - r - delta))), n%:R / r).

Hypothesis Hk : SrcConverseBound <= k.+1%:R.

Lemma Hr1 : 0 < (`H P - r) / 2.
Proof.
apply divR_gt0; last lra.
case: Hr => ? ?; lra.
Qed.

Lemma Hepsilon1 : 0 < (1 - epsilon) / 2.
Proof.
apply divR_gt0; last lra.
case: Hepsilon => ? ?; lra.
Qed.

Lemma lambda0 : 0 < lambda.
Proof. rewrite /lambda; apply P_Rmin => //; [exact Hepsilon1 | exact Hr1]. Qed.

Lemma Hdelta : 0 < delta.
Proof.
rewrite /delta.
apply Rmin_pos.
case: Hr => ? ?; apply divR_gt0; lra.
apply divR_gt0; [exact lambda0 | lra].
Qed.

Definition e0 := `H P - r.

Lemma e0_delta : e0 <> delta.
Proof.
rewrite /e0 /delta /lambda -/r.
apply Rmin_case_strong => H1; first by lra.
apply Rmin_case_strong => H2.
- apply/gtR_eqF; apply: leR_ltR_trans.
  + apply: (leR_trans _ H2).
    rewrite leR_pdivr_mulr //; apply leR_pmulr; [lra|exact/ltRW/Hepsilon1].
  * rewrite ltR_pdivr_mulr //; lra.
- rewrite /Rdiv -mulRA (_ : ( _ * / 2 ) = / 4); [lra | by field].
Qed.

Definition no_failure := [set x : 'rV[A]_k.+1 | dec sc (enc sc x) == x].

Lemma no_failure_sup : #| no_failure |%:R <= exp2 (k.+1%:R * (`H P - e0)).
Proof.
apply (@leR_trans (exp2 n%:R)).
  rewrite /no_failure.
  have Hsubset : [set x | dec sc (enc sc x) == x] \subset dec sc @: (enc sc @: [set: 'rV[A]_k.+1]).
    apply/subsetP => x.
    rewrite inE => Hx.
    apply/imsetP.
    exists (enc sc x).
    - apply mem_imset; by rewrite inE.
    - by move/eqP in Hx.
  apply (@leR_trans #| dec sc @: (enc sc @: [set: 'rV[A]_k.+1]) |%:R).
    by apply/le_INR/leP; case/subset_leqif_cards : Hsubset.
  apply (@leR_trans #| dec sc @: [set: 'rV[bool]_n] |%:R).
    apply/le_INR/leP/subset_leqif_cards/imsetS/subsetP => x Hx; by rewrite inE.
  apply (@leR_trans #| [set: 'rV[bool]_n] |%:R).
    apply/le_INR/leP/leq_imset_card.
    rewrite cardsT card_matrix /= card_bool natRexp2 mul1n; exact/leRR.
apply Exp_le_increasing => //.
rewrite /e0 [X in _ <= _ * X](_ : _ = r); last by field.
apply (@leR_pmul2r (1 / r)) => //.
apply divR_gt0; [lra | tauto].
rewrite -mulRA div1R mulRV ?mulR1; last by case: Hr => /ltRP; rewrite lt0R => /andP[].
by case/leR_max : Hk.
Qed.

Local Open Scope proba_scope.

Lemma step1 : (1 - esrc(P , sc)) = \sum_(x in no_failure) P `^ k.+1 x.
Proof.
rewrite /SrcErrRate /no_failure /Pr.
set a := \sum_(_ | _) _.
set b := \sum_(_ | _) _.
suff : 1 = a + b by move=> ->; field.
rewrite /a {a}.
have -> : b = \sum_(i in [set i | dec sc (enc sc i) == i]) P `^ k.+1 i.
  apply eq_big => // i /=; by rewrite inE.
rewrite -(FDist.f1 (P `^ k.+1)).
rewrite (bigID [pred a | a \in [set i0 | dec sc (enc sc i0) == i0]]) /= addRC.
by congr (_ + _); apply eq_bigl => t /=; rewrite !inE.
Qed.

Local Open Scope typ_seq_scope.

Lemma step2 : 1 - (esrc(P , sc)) =
  \sum_(x in 'rV[A]_k.+1 | x \in no_failure :&: ~: `TS P k.+1 delta) P `^ k.+1 x +
  \sum_(x in 'rV[A]_k.+1 | x \in no_failure :&: `TS P k.+1 delta) P `^ k.+1 x.
Proof.
rewrite step1 (bigID [pred x | x \in `TS P k.+1 delta]) /= addRC.
f_equal.
- apply eq_bigl => x; by rewrite in_setI in_setC.
- apply eq_bigl => x; by rewrite in_setI.
Qed.

Lemma step3 : 1 - (esrc(P , sc)) <=
  \sum_(x in 'rV[A]_k.+1 | x \in ~: `TS P k.+1 delta) P `^ k.+1 x +
  \sum_(x in 'rV[A]_k.+1 | x \in no_failure :&: `TS P k.+1 delta) P `^ k.+1 x.
Proof.
rewrite step2; apply/leR_add2r/leR_sumRl => //= i Hi.
exact/leRR.
by move: Hi; rewrite in_setI => /andP[].
Qed.

Lemma step4 : 1 - (esrc(P , sc)) <= delta +
  #| no_failure :&: `TS P k.+1 delta|%:R * exp2 (- k.+1%:R * (`H P - delta)).
Proof.
apply/(leR_trans step3)/leR_add.
- move/leRP : Hk; rewrite 2!leR_max' -andbA => /andP[/leRP].
  move/(Pr_TS_1 Hdelta) => Hdelta _.
  rewrite -[in X in _ <= X](oppRK delta) leR_oppr -(@leR_add2l 1) 2!addR_opp.
  move/leR_trans : Hdelta; apply.
  rewrite Pr_to_cplt; exact/leRR.
- apply (@leR_trans
    (\sum_(x in 'rV[A]_k.+1 | x \in no_failure :&: `TS P k.+1 delta)
      exp2 (- k.+1%:R * (`H P - delta)))).
    apply leR_sumR => /= i.
    rewrite in_setI => /andP[i_B i_TS].
    move: (typ_seq_definition_equiv2 i_TS) => [H1 _].
    apply (@Log_le_inv 2) => //.
    + move: i_TS.
      rewrite /`TS inE /typ_seq => /andP[/leRP i_TS _].
      exact: (ltR_leR_trans (exp2_gt0 _) i_TS).
    + rewrite /exp2 ExpK //.
      rewrite mulRC mulRN -mulNR -leR_pdivr_mulr; last exact/ltR0n.
      rewrite leR_oppr /Rdiv mulRC; by rewrite div1R mulNR in H1.
  by rewrite big_const iter_addR; exact/leRR.
Qed.

Lemma step5 : 1 - (esrc(P , sc)) <= delta + exp2 (- k.+1%:R * (e0 - delta)).
Proof.
apply (@leR_trans (delta + #| no_failure |%:R * exp2 (- k.+1%:R * (`H P - delta)))).
- apply/(leR_trans step4)/leR_add2l/leR_wpmul2r => //.
  exact/le_INR/leP/subset_leqif_cards/subsetIl.
- apply leR_add2l.
  apply (@leR_trans (exp2 (k.+1%:R * (`H P - e0)) * exp2 (- k.+1%:R * (`H P - delta))));
    last first.
    rewrite -ExpD; apply Exp_le_increasing => //; apply Req_le; by field.
  apply leR_wpmul2r => //; exact no_failure_sup.
Qed.

Lemma step6 : 1 - 2 * delta <= esrc(P , sc).
Proof.
have H : exp2 (- k.+1%:R * (e0 - delta)) <= delta.
  apply (@Log_le_inv 2) => //.
  - exact Hdelta.
  - rewrite /exp2 ExpK //.
    apply (@leR_pmul2r (1 / (e0 - delta))) => //.
    + apply divR_gt0; first lra.
      apply subR_gt0.
      rewrite /e0 /delta /r.
      have H1 : (`H P - r) / 2 < `H P - r.
        rewrite -[X in _ < X]mulR1.
        apply ltR_pmul2l; last lra.
        apply/ltRP; rewrite ltR_subRL' addR0; apply/ltRP; by case: Hr.
      apply Rmin_case_strong => H2 //; exact: (leR_ltR_trans H2 H1).
    + rewrite -mulRA div1R mulRV; last by rewrite subR_eq0'; exact/eqP/e0_delta.
      rewrite mulNR mulR1 leR_oppl.
      by move/leRP : Hk; rewrite 2!leR_max' => /andP[/andP[_ /leRP]].
suff : 1 - (esrc(P , sc)) <= delta + delta by move=> *; lra.
exact/(leR_trans step5)/leR_add2l.
Qed.

Theorem source_coding_converse' : epsilon <= esrc(P , sc).
Proof.
apply: (leR_trans _ step6).
rewrite -[X in _ <= X]oppRK leR_oppr oppRB leR_subl_addr addRC.
apply (@leR_pmul2l (/ 2)); first lra.
rewrite mulRA mulVR ?mul1R; last exact/eqP/gtR_eqF.
rewrite /delta.
have H1 : lambda / 2 <= / 2 * (1 - epsilon).
  apply (@leR_trans lambda).
    rewrite leR_pdivr_mulr //; apply leR_pmulr; [lra | exact/ltRW/lambda0].
 rewrite /lambda mulRC; exact: geR_minl.
apply Rmin_case_strong => ? //; exact: (@leR_trans (lambda / 2)).
Qed.

End source_coding_converse'.

Section source_coding_converse.

Variables (A : finType) (P : fdist A).

(** Source coding theorem (converse part) #<a name="label_source_coding_converse"> </a># *)

Theorem source_coding_converse : forall epsilon, 0 < epsilon < 1 ->
  forall r : Qplus, 0 < r < `H P ->
    forall n k (sc : scode_fl A k.+1 n),
      SrcRate sc = r ->
      SrcConverseBound P (num r) (den r) n epsilon <= k.+1%:R ->
      epsilon <= esrc(P , sc).
Proof.
move=> epsilon Hespilon r r_HP n k sc r_sc Hk_bound.
exact: (@source_coding_converse' _ _ (num r) (den r)).
Qed.

End source_coding_converse.
