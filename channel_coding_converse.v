(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import Reals_ext ssr_ext ssralg_ext log2 ln_facts Rssr Rbigop arg_rmax.
Require Import num_occ proba entropy types jtypes divergence.
Require Import conditional_divergence error_exponent channel_code channel.
Require Import success_decode_bound.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope channel_code_scope.
Local Open Scope channel_scope.
Local Open Scope entropy_scope.
Local Open Scope tuple_ext_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope types_scope.

Section channel_coding_converse_intermediate_lemma.

Variables A B : finType.
Variable W : `Ch_1*(A, B).
Variable cap : R.
Hypothesis Hc : capacity W cap.

Variable minRate : R.
Hypothesis HminRate : minRate > cap.

Let Anot0 : (0 < #|A|)%nat. Proof. by case: W. Qed.

Let Bnot0 : (0 < #|B|)%nat.
Proof.
case/card_gt0P : Anot0 => a _; exact (dist_support_not_empty (W a)).
Qed.

Lemma channel_coding_converse_gen : exists Delta, 0 < Delta /\ forall n',
  let n := n'.+1 in forall (M : finType) (c : code A B M n), (0 < #|M|)%nat ->
    minRate <= CodeRate c ->
      scha(W, c) <= INR (n.+1)^(#|A| + #|A| * #|B|) * exp2 (- INR n * Delta).
Proof.
move: error_exponent_bound => /(_ _ _ Bnot0 W _ Hc _ HminRate); case => Delta [Delta_pos HDelta].
exists Delta; split => // n' n M c Mnot0 H.
apply (Rle_trans _ _ _ (success_bound W Mnot0 c)).
set Pmax := arg_rmax _ _ _.
set tc :=  _.-typed_code _.
rewrite pow_add -mulRA.
apply Rmult_le_compat_l; first by apply pow_le, pos_INR.
apply (Rle_trans _ _ _ (typed_success_bound W Mnot0 (Pmax.-typed_code c))).
apply Rmult_le_compat_l; first by apply pow_le, pos_INR.
set Vmax := arg_rmax _ _ _.
rewrite /success_factor_bound /exp_cdiv.
case : ifP => Hcase; last by rewrite mul0R; exact/ltRW/exp2_pos.
rewrite -exp2_plus.
apply exp2_le_increasing.
rewrite -mulRDr 2!mulNR.
apply Ropp_le_contravar, Rmult_le_compat_l; first by apply pos_INR.
have {Hcase}Hcase : Vmax << W | Pmax.
  move=> a Hp b /eqP Hw.
  move/forallP : Hcase.
  by move/(_ a)/implyP/(_ Hp)/forallP/(_ b)/implyP/(_ Hw)/eqP.
apply (Rle_trans _ _ _ (HDelta Pmax Vmax Hcase)) => /=.
by apply Rplus_le_compat_l, Rle_max_compat_l, Rplus_le_compat_r.
Qed.

End channel_coding_converse_intermediate_lemma.

Section channel_coding_converse.

Variables A B : finType.
Variable W : `Ch_1*(A, B).
Variable cap : R.
Hypothesis w_cap : capacity W cap.

Variable epsilon : R.
Hypothesis eps_gt0 : 0 < epsilon.

Variable minRate : R.
Hypothesis minRate_cap : minRate > cap.

(** * Converse of the Channel Coding Theorem #<a name="label_channel_coding_converse"> </a># *)

Theorem channel_coding_converse : exists n0,
  forall n M (c : code A B M n),
    (0 < #|M|)%nat -> n0 < INR n -> minRate <= CodeRate c -> scha(W, c) < epsilon.
Proof.
case: (channel_coding_converse_gen w_cap minRate_cap) => Delta [Delta_pos HDelta].
pose K := (#|A| + #|A| * #|B|)%nat.
pose n0 := 2 ^ K * INR K.+1`! / ((Delta * ln 2) ^ K.+1) / epsilon.
exists n0 => n M c HM n0_n HminRate.
have Rlt0n : 0 < INR n.
  apply: (Rlt_trans _ _ _ _ n0_n).
  rewrite /n0.
  apply mulR_gt0; last by apply Rinv_0_lt_compat.
  rewrite /Rdiv -mulRA.
  apply mulR_gt0; first by apply pow_gt0; fourier.
  apply mulR_gt0; first by apply lt_0_INR; apply /ltP; apply fact_gt0.
  apply Rinv_0_lt_compat, pow_gt0, mulR_gt0 => //; by apply ln_2_pos.
destruct n as [|n'].
  by apply Rlt_irrefl in Rlt0n.
set n := n'.+1.
apply (Rle_lt_trans _ (INR n.+1 ^ K * exp2 (- INR n * Delta))).
  by apply HDelta.
move: (n0_n) => /(Rmult_lt_compat_l (/ INR n) _) => /(_ (Rinv_0_lt_compat (INR n) Rlt0n)).
rewrite Rinv_l; last by apply not_eq_sym, Rlt_not_eq.
move/(Rmult_lt_compat_l epsilon _) => /(_ eps_gt0); rewrite mulR1 => H1'.
apply: (Rle_lt_trans _ _ _ _ H1') => {H1'}.
rewrite /n0 [in X in _ <= X]mulRC -2![in X in _ <= X]mulRA.
rewrite Rinv_l; last by apply not_eq_sym, Rlt_not_eq.
rewrite mulR1.
apply Rge_le; rewrite mulRC -2!mulRA; apply Rle_ge.
set aux := INR _ * (_ * _).
have aux_gt0 : 0 < aux.
  apply mulR_gt0.
    apply lt_0_INR; apply/ltP; by apply fact_gt0.
  apply mulR_gt0.
  apply Rinv_0_lt_compat, pow_gt0, mulR_gt0 => //; by apply ln_2_pos.
  by apply Rinv_0_lt_compat.
apply (Rle_trans _ ((INR n.+1 / INR n) ^ K * aux)); last first.
  apply Rmult_le_compat => //.
  - apply pow_ge0, Rle_mult_inv_pos => //; by apply pos_INR.
  - by apply ltRW.
  - apply pow_incr; split.
    + apply Rle_mult_inv_pos => //; by apply pos_INR.
    + apply Rmult_le_reg_r with (INR n) => //.
      rewrite /Rdiv -mulRA -Rinv_l_sym; last by apply not_eq_sym, Rlt_not_eq.
      rewrite mulR1 (_ : 2 = INR 2) // -mult_INR; apply le_INR.
      rewrite (_ : 0 = INR 0) // in Rlt0n.
      apply INR_lt in Rlt0n.
      rewrite multE mul2n -addnn -addn1.
      apply/leP.
      by rewrite leq_add2l.
  - by apply Rle_refl.
rewrite pow_mult -mulRA.
apply Rmult_le_compat.
- by apply/pow_ge0/ltRW/lt_0_INR/ltP.
- exact/ltRW/exp2_pos.
- by apply Rle_refl.
- apply Rle_inv_conv.
  + by apply exp2_pos.
  + apply mulR_gt0; last exact aux_gt0.
    rewrite pow_inv; last by apply not_eq_sym, Rlt_not_eq.
    by apply Rinv_0_lt_compat, pow_gt0.
  + rewrite -exp2_Ropp mulNR oppRK /exp2.
    have nDeltaln2 : 0 <= INR n * Delta * ln 2.
      apply mulR_ge0; last exact/ltRW/ln_2_pos.
      apply mulR_ge0; [by apply pos_INR | exact/ltRW].
    apply: (Rle_trans _ _ _ _ (exp_lb (K.+1) nDeltaln2)) => {nDeltaln2}.
    apply Req_le.
    rewrite Rinv_mult_distr; last 2 first.
      by apply not_eq_sym, Rlt_not_eq, pow_gt0, Rinv_0_lt_compat.
      by apply not_eq_sym, Rlt_not_eq.
    rewrite mulRC Rinv_mult_distr; last 2 first.
      apply not_eq_sym, Rlt_not_eq, lt_0_INR; apply/ltP; by apply fact_gt0.
      apply not_eq_sym, Rlt_not_eq, mulR_gt0.
        apply Rinv_0_lt_compat, pow_gt0, mulR_gt0 => //; by apply ln_2_pos.
      by apply Rinv_0_lt_compat.
    rewrite -mulRA mulRC.
    rewrite Rinv_mult_distr; last 2 first.
    - apply not_eq_sym, Rlt_not_eq, Rinv_0_lt_compat, pow_gt0, mulR_gt0 => //; by apply ln_2_pos.
    - by apply not_eq_sym, Rlt_not_eq, Rinv_0_lt_compat.
    - rewrite invRK; last first.
        apply not_eq_sym, Rlt_not_eq, pow_gt0, mulR_gt0 => //; by apply ln_2_pos.
      rewrite invRK; last by apply not_eq_sym, Rlt_not_eq.
      rewrite (_ : / (/ INR n) ^ K = (INR n) ^ K); last first.
        rewrite -pow_inv; last first.
          by apply Rinv_neq_0_compat, not_eq_sym, Rlt_not_eq.
        rewrite invRK //; exact/not_eq_sym/Rlt_not_eq.
      rewrite /Rdiv; f_equal.
      rewrite !Rpow_mult_distr -(tech_pow_Rmult (INR n)).
      field.
Qed.

End channel_coding_converse.
