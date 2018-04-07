(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div choice fintype tuple finfun bigop prime.
From mathcomp Require Import binomial ssralg finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import Reals_ext Ranalysis_ext Rssr log2 ln_facts Rbigop proba entropy.
Require Import channel_code channel divergence conditional_divergence.
Require Import variation_dist pinsker.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope divergence_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope channel_scope.
Local Open Scope reals_ext_scope.

Section mutinfo_distance_bound.

Variable A B : finType.
Variables V W : `Ch_1(A, B).
Variable P : dist A.
Hypothesis V_dom_by_W : P|- V << W.
Hypothesis cdiv_ub : D(V || W | P) <= (exp(-2)) ^ 2 * / 2.

Let cdiv_bounds : 0 <= sqrt (2 * D(V || W | P)) <= exp (-2).
Proof.
split; first by apply sqrt_pos.
apply pow2_Rle_inv; [ by apply sqrt_pos | exact/ltRW/exp_pos | ].
rewrite [in X in X <= _]/= mulR1 sqrt_sqrt; last first.
  apply mulR_ge0; by [fourier | apply leq0cdiv].
apply/RleP; rewrite -(Rle_pmul2r (/ 2)); last exact/RltP/invR_gt0.
rewrite -mulRA mulRCA mulRV ?mulR1; last exact/eqP/gtR_eqF.
exact/RleP.
Qed.

Local Open Scope variation_distance_scope.

(** Distance from the output entropy of one channel to another: *)

Lemma out_entropy_dist_ub : Rabs (`H(P `o V) - `H(P `o W)) <=
  / ln 2 * INR #|B| * - xlnx (sqrt (2 * D(V || W | P))).
Proof.
rewrite 2!xlnx_entropy /Rminus.
rewrite -mulRN -mulRDr Rabs_mult Rabs_right; last first.
  rewrite -(mul1R (/ ln 2)); exact/Rle_ge/Rle_mult_inv_pos.
rewrite -mulRA; apply Rmult_le_compat_l.
  by rewrite -(mul1R (/ ln 2)); apply Rle_mult_inv_pos.
rewrite oppRK (big_morph _ morph_Ropp oppR0) -big_split /=.
apply: Rle_trans; first exact: ler_rsum_Rabs.
rewrite -iter_Rplus_Rmult -big_const.
apply ler_rsum => b _; rewrite addRC.
apply Rabs_xlnx => //.
- split; [exact/dist_nonneg | exact/dist_max].
- split; [exact/dist_nonneg | exact/dist_max].
- rewrite 2!OutDist.dE /Rminus (big_morph _ morph_Ropp oppR0) -big_split /=.
  apply: Rle_trans; first exact: ler_rsum_Rabs.
  apply (Rle_trans _ (d(`J(P , V), `J(P , W)))).
  + rewrite /var_dist /=.
    apply (Rle_trans _ (\rsum_(a : A) \rsum_(b : B) Rabs ((`J(P, V)) (a, b) - (`J(P, W)) (a, b)))); last first.
      apply Req_le; rewrite pair_bigA /=; apply eq_bigr; by case.
    apply: ler_rsum => a _.
    rewrite (bigD1 b) //= Rabs_minus_sym /Rminus -[X in X <= _]addR0.
    rewrite 2!JointDist.dE /=; apply/Rplus_le_compat_l/rsumr_ge0 => ? _; exact/Rabs_pos.
  + rewrite cdiv_is_div_joint_dist => //.
    exact/Pinsker_inequality_weak/joint_dom.
Qed.

(** Distance from the joint entropy of one channel to another: *)

Lemma joint_entropy_dist_ub : Rabs (`H(P , V) - `H(P , W)) <=
  / ln 2 * INR #|A| * INR #|B| * - xlnx (sqrt (2 * D(V || W | P))).
Proof.
rewrite 2!xlnx_entropy.
rewrite /Rminus -mulRN -mulRDr Rabs_mult Rabs_right; last first.
  by rewrite -(mul1R (/ ln 2)); apply Rle_ge, Rle_mult_inv_pos.
rewrite -2!mulRA; apply Rmult_le_compat_l.
  by rewrite -(mul1R (/ ln 2)); apply Rle_mult_inv_pos.
rewrite oppRK (big_morph _ morph_Ropp oppR0) -big_split /=.
apply: Rle_trans; first exact: ler_rsum_Rabs.
rewrite -2!iter_Rplus_Rmult -2!big_const pair_bigA /=.
apply: ler_rsum; case => a b _; rewrite addRC /=.
apply Rabs_xlnx => //.
- split; [exact: dist_nonneg | exact: dist_max].
- split; [exact: dist_nonneg | exact: dist_max].
- apply (Rle_trans _ (d(`J(P , V) , `J(P , W)))).
    rewrite /var_dist /R_dist (bigD1 (a, b)) //= Rabs_minus_sym /Rminus.
    rewrite -[X in X <= _]addR0.
    apply/Rplus_le_compat_l/rsumr_ge0 => ? _; exact/Rabs_pos.
  rewrite cdiv_is_div_joint_dist => //.
  exact/Pinsker_inequality_weak/joint_dom.
Qed.

(** * Distance from the mutual information of one channel to another *)

Lemma mut_info_dist_ub : Rabs (`I(P ; V) - `I(P ; W)) <=
  / ln 2 * (INR #|B| + INR #|A| * INR #|B|) * - xlnx (sqrt (2 * D(V || W | P))).
Proof.
rewrite /mut_info.
rewrite (_ : _ - _ = `H(P `o V) - `H(P `o W) + (`H(P , W) - `H(P , V))); last by field.
eapply Rle_trans; first by apply Rabs_triang.
rewrite -mulRA mulRDl mulRDr.
apply Rplus_le_compat.
- by rewrite mulRA; apply out_entropy_dist_ub.
- by rewrite Rabs_minus_sym 2!mulRA; apply joint_entropy_dist_ub.
Qed.

End mutinfo_distance_bound.

Section error_exponent_lower_bound.

Variables A B : finType.
Hypothesis Bnot0 : (0 < #|B|)%nat.
Variable W : `Ch_1(A, B).
Variable cap : R.
Hypothesis W_cap : capacity W cap.
Variable minRate : R.
Hypothesis minRate_cap : minRate > cap.

(** * Error exponent bound *)

Lemma error_exponent_bound : exists Delta, 0 < Delta /\
  forall P : dist A, forall V : `Ch_1(A, B),
    P |- V << W ->
    Delta <= D(V || W | P) +  +| minRate - `I(P ; V) |.
Proof.
set gamma := / (INR #|B| + INR #|A| * INR #|B|) * (ln 2 * ((minRate - cap) / 2)).
move: (continue_xlnx 0).
rewrite /continuity_pt /continue_in /limit1_in /limit_in.
move=> /(_ (min(exp (-2), gamma))).
have Htmp : min(exp (-2), gamma) > 0.
  apply Rmin_Rgt_r ; split ; apply Rlt_gt.
  - by apply exp_pos.
  - subst gamma ; apply mulR_gt0.
      apply/invR_gt0/Rplus_lt_le_0_compat.
      - exact/lt_0_INR/ltP.
      - apply mulR_ge0; exact/pos_INR.
    apply mulR_gt0 => //.
    apply mulR_gt0; last exact: invR_gt0.
    rewrite -(Rplus_opp_r cap) /Rminus; by apply Rplus_lt_compat_r.
move=> /(_ Htmp) {Htmp} [] /= mu [mu_pos mu_cond].
set x := min(mu / 2, exp (-2)).
move: {mu_cond}(mu_cond x).
have x_pos : 0 < x.
  subst x.
  apply Rmin_pos; last by apply exp_pos.
  apply mulR_gt0 => //; exact: invR_gt0.
have Htmp : D_x no_cond 0 x /\ R_dist x 0 < mu.
  split.
  - split => //; by apply Rlt_not_eq.
  - rewrite /R_dist subR0 Rabs_right; last exact/Rle_ge/ltRW.
    subst x.
    apply (Rle_lt_trans _ (mu * / 2)); first by apply Rmin_l.
    apply/RltP; rewrite ltR_pdivr_mulr //; apply/RltP; fourier.
move=> /(_ Htmp) {Htmp}.
rewrite /R_dist /Rminus {2}/xlnx ltRR oppR0 addR0 Rabs_left; last first.
  apply xlnx_neg.
  split => //; subst x.
  exact: Rle_lt_trans (Rmin_r _ _) ltRinve21.
move=> Hx.
set Delta := min((minRate - cap) / 2, x ^ 2 / 2).
exists Delta; split.
  apply Rmin_case.
    apply mulR_gt0; [exact: Rlt_Rminus | exact/invR_gt0].
  apply mulR_gt0; [exact: pow_gt0 | exact: invR_gt0].
move=> P V v_dom_by_w.
case/boolP : (Delta <b= D(V || W | P)).
  move/RleP => Hcase.
  apply (Rle_trans _ (D(V || W | P))) => //.
  rewrite -{1}(addR0 (D(V || W | P))).
  by apply Rplus_le_compat_l, Rmax_l.
move/RleP/(Rnot_le_lt _) => Hcase.
suff Htmp : (minRate - cap) / 2 <= minRate - (`I(P; V)).
  clear -Hcase v_dom_by_w Htmp.
  apply (Rle_trans _ +| minRate - `I(P ; V) |); last first.
    rewrite -[X in X <= _]add0R.
    apply Rplus_le_compat_r, leq0cdiv => b Hb ? ?; by apply v_dom_by_w.
  eapply Rle_trans; last by apply Rmax_r.
  eapply Rle_trans; first by apply Rmin_l.
  done.
have Htmp : `I(P ; V) <= cap + / ln 2 * (INR #|B| + INR #|A| * INR #|B|) *
                               (- xlnx (sqrt (2 * D(V || W | P)))).
  apply (Rle_trans _ (`I(P ; W) + / ln 2 * (INR #|B| + INR #|A| * INR #|B|) *
                                  - xlnx (sqrt (2 * D(V || W | P))))); last first.
    apply Rplus_le_compat_r.
    move: W_cap; rewrite /capacity /lub; case; by move/(_ P).
  apply (Rplus_le_reg_l (- `I(P ; W))).
  rewrite addRA Rplus_opp_l add0R addRC.
  apply (Rle_trans _ (Rabs (`I(P ; V) + - `I(P ; W)))); first apply Rle_abs.
  have Htmp : D(V || W | P) <= exp (-2) ^ 2 * / 2.
    clear -Hcase x_pos.
    apply/ltRW/(Rlt_le_trans _ _ _ Hcase).
    apply (Rle_trans _ (x ^ 2 * / 2)); first by apply Rmin_r.
    apply Rmult_le_compat_r; first exact/ltRW/invR_gt0.
    apply pow_incr.
    split; [exact: ltRW | exact: Rmin_r].
  by apply mut_info_dist_ub.
apply Ropp_le_contravar, (Rplus_le_compat_l minRate) in Htmp.
eapply Rle_trans; last by apply Htmp.
clear Htmp.
suff Htmp : - xlnx (sqrt (2 * (D(V || W | P)))) <= gamma.
  rewrite oppRD addRA.
  apply (Rplus_le_reg_l (- (minRate + - cap ))).
  rewrite [X in X <= _](_ : _ = - ((minRate + - cap) / 2)); last by field.
  apply Rge_le.
  rewrite addRA Rplus_opp_l add0R.
  apply Ropp_le_ge_contravar; rewrite -mulRA.
  apply/RleP; rewrite mulRC leR_pdivr_mulr //.
  rewrite mulRC -leR_pdivl_mulr; last first.
    by apply/RltP; rewrite -mult_INR -plus_INR plusE multE ltR0n addn_gt0 Bnot0.
  apply/RleP; by rewrite [in X in _ <= X]mulRC /Rdiv (mulRC _ (/ (_ + _))).
suff Htmp : xlnx x <= xlnx (sqrt (2 * (D(V || W | P)))).
  clear -Hx Htmp.
  apply Ropp_le_cancel; rewrite oppRK.
  apply (Rle_trans _ (xlnx x)) => //.
  apply Ropp_le_cancel; rewrite oppRK.
  apply/ltRW/(Rlt_le_trans _ _ _ Hx).
  subst gamma; by apply Rmin_r.
apply/ltRW/Rgt_lt.
have Htmp : sqrt (2 * D(V || W | P)) < x.
  apply pow2_Rlt_inv; [exact: sqrt_pos | exact: ltRW | ].
  rewrite [in X in X < _]/= mulR1 sqrt_sqrt; last first.
    apply mulR_ge0; first exact/ltRW.
    apply leq0cdiv=> a Ha ? ?; by apply v_dom_by_w.
  apply/RltP; rewrite mulRC -ltR_pdivl_mulr //.
  exact/RltP/(Rlt_le_trans _ _ _ Hcase)/Rmin_r.
apply xlnx_sdecreasing_0_Rinv_e => //.
- split; first by apply sqrt_pos.
  apply: (Rle_trans _ x _ (ltRW _ _ _)) => //.
  subst x.
  apply (Rle_trans _ (exp (-2))); first by apply Rmin_r.
  apply ltRW, exp_increasing, Ropp_lt_contravar; fourier.
- split; first exact: ltRW.
  apply (Rle_trans _ (exp (-2))); first by apply Rmin_r.
  apply ltRW, exp_increasing, Ropp_lt_contravar; fourier.
Qed.

End error_exponent_lower_bound.
