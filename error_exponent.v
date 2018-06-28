(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div choice fintype tuple finfun bigop prime.
From mathcomp Require Import binomial ssralg finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import ssrR Reals_ext Ranalysis_ext logb ln_facts Rbigop proba entropy.
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
apply/leRP; rewrite -(leR_pmul2r' (/ 2)); last exact/ltRP/invR_gt0.
rewrite -mulRA mulRCA mulRV ?mulR1; [exact/leRP | exact/eqP/gtR_eqF].
Qed.

Local Open Scope variation_distance_scope.

(** Distance from the output entropy of one channel to another: *)

Lemma out_entropy_dist_ub : `| `H(P `o V) - `H(P `o W) | <=
  / ln 2 * INR #|B| * - xlnx (sqrt (2 * D(V || W | P))).
Proof.
rewrite 2!xlnx_entropy.
rewrite /Rminus -mulRN -mulRDr normRM gtR0_norm; last exact/invR_gt0/ln2_gt0.
rewrite -mulRA; apply leR_pmul2l; first exact/invR_gt0/ln2_gt0.
rewrite oppRK (big_morph _ morph_Ropp oppR0) -big_split /=.
apply: leR_trans; first exact: ler_rsum_Rabs.
rewrite -iter_addR -big_const.
apply ler_rsum => b _; rewrite addRC.
apply Rabs_xlnx => //.
- split; [exact/dist_ge0 | exact/dist_max].
- split; [exact/dist_ge0 | exact/dist_max].
- rewrite 2!OutDist.dE /Rminus (big_morph _ morph_Ropp oppR0) -big_split /=.
  apply: leR_trans; first exact: ler_rsum_Rabs.
  apply (@leR_trans (d(`J(P , V), `J(P , W)))).
  + rewrite /var_dist /=.
    apply (@leR_trans (\rsum_(a : A) \rsum_(b : B) `| (`J(P, V)) (a, b) - (`J(P, W)) (a, b) |)); last first.
      apply Req_le; rewrite pair_bigA /=; apply eq_bigr; by case.
    apply: ler_rsum => a _.
    rewrite (bigD1 b) //= distRC -[X in X <= _]addR0.
    rewrite 2!JointDist.dE /=; apply/leR_add2l/rsumr_ge0 => ? _; exact/normR_ge0.
  + rewrite cdiv_is_div_joint_dist => //.
    exact/Pinsker_inequality_weak/joint_dom.
Qed.

(** Distance from the joint entropy of one channel to another: *)

Lemma joint_entropy_dist_ub : `| `H(P , V) - `H(P , W) | <=
  / ln 2 * INR #|A| * INR #|B| * - xlnx (sqrt (2 * D(V || W | P))).
Proof.
rewrite 2!xlnx_entropy.
rewrite /Rminus -mulRN -mulRDr normRM gtR0_norm; last exact/invR_gt0/ln2_gt0.
rewrite -2!mulRA; apply leR_pmul2l; first exact/invR_gt0/ln2_gt0.
rewrite oppRK (big_morph _ morph_Ropp oppR0) -big_split /=.
apply: leR_trans; first exact: ler_rsum_Rabs.
rewrite -2!iter_addR -2!big_const pair_bigA /=.
apply: ler_rsum; case => a b _; rewrite addRC /=.
apply Rabs_xlnx => //.
- split; [exact: dist_ge0 | exact: dist_max].
- split; [exact: dist_ge0 | exact: dist_max].
- apply (@leR_trans (d(`J(P , V) , `J(P , W)))).
    rewrite /var_dist /R_dist (bigD1 (a, b)) //= distRC.
    rewrite -[X in X <= _]addR0.
    apply/leR_add2l/rsumr_ge0 => ? _; exact/normR_ge0.
  rewrite cdiv_is_div_joint_dist => //.
  exact/Pinsker_inequality_weak/joint_dom.
Qed.

(** * Distance from the mutual information of one channel to another *)

Lemma mut_info_dist_ub : `| `I(P ; V) - `I(P ; W) | <=
  / ln 2 * (INR #|B| + INR #|A| * INR #|B|) * - xlnx (sqrt (2 * D(V || W | P))).
Proof.
rewrite /mut_info.
rewrite (_ : _ - _ = `H(P `o V) - `H(P `o W) + (`H(P , W) - `H(P , V))); last by field.
apply: leR_trans; first exact: Rabs_triang.
rewrite -mulRA mulRDl mulRDr.
apply leR_add.
- by rewrite mulRA; apply out_entropy_dist_ub.
- by rewrite distRC 2!mulRA; apply joint_entropy_dist_ub.
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
      apply/invR_gt0/addR_gt0wl.
      - exact/ltR0n.
      - apply mulR_ge0; exact/leR0n.
    apply mulR_gt0 => //; apply mulR_gt0; last exact: invR_gt0.
    by rewrite subR_gt0.
move=> /(_ Htmp) {Htmp} [] /= mu [mu_pos mu_cond].
set x := min(mu / 2, exp (-2)).
move: {mu_cond}(mu_cond x).
have x_pos : 0 < x.
  subst x.
  apply Rmin_pos; last by apply exp_pos.
  apply mulR_gt0 => //; exact: invR_gt0.
have Htmp : D_x no_cond 0 x /\ R_dist x 0 < mu.
  split.
  - split => //; exact/ltR_eqF.
  - rewrite /R_dist subR0 gtR0_norm //.
    subst x.
    apply (@leR_ltR_trans (mu * / 2)); first exact/geR_minl.
    apply/ltRP; rewrite ltR_pdivr_mulr //; apply/ltRP; fourier.
move=> /(_ Htmp) {Htmp}.
rewrite /R_dist {2}/xlnx ltRR' subR0 ltR0_norm; last first.
  apply xlnx_neg.
  split => //; subst x.
  exact: leR_ltR_trans (geR_minr _ _) ltRinve21.
move=> Hx.
set Delta := min((minRate - cap) / 2, x ^ 2 / 2).
exists Delta; split.
  apply Rmin_case.
    apply mulR_gt0; [exact/subR_gt0 | exact/invR_gt0].
  apply mulR_gt0; [exact: pow_gt0 | exact: invR_gt0].
move=> P V v_dom_by_w.
case/boolP : (Delta <b= D(V || W | P)).
  move/leRP => Hcase.
  apply (@leR_trans (D(V || W | P))) => //.
  rewrite -{1}(addR0 (D(V || W | P))); exact/leR_add2l/leR_maxl.
move/leRP/ltRNge => Hcase.
suff Htmp : (minRate - cap) / 2 <= minRate - (`I(P; V)).
  clear -Hcase v_dom_by_w Htmp.
  apply (@leR_trans +| minRate - `I(P ; V) |); last first.
    rewrite -[X in X <= _]add0R.
    apply/leR_add2r/leq0cdiv => b Hb ? ?; exact: v_dom_by_w.
  apply: leR_trans; last exact: leR_maxr.
  apply: (leR_trans _ Htmp); exact: geR_minl.
have Htmp : `I(P ; V) <= cap + / ln 2 * (INR #|B| + INR #|A| * INR #|B|) *
                               (- xlnx (sqrt (2 * D(V || W | P)))).
  apply (@leR_trans (`I(P ; W) + / ln 2 * (INR #|B| + INR #|A| * INR #|B|) *
                               - xlnx (sqrt (2 * D(V || W | P))))); last first.
    apply/leR_add2r.
    move: W_cap; rewrite /capacity /lub; case; by move/(_ P).
  rewrite addRC -leR_subl_addr.
  apply (@leR_trans `| `I(P ; V) + - `I(P ; W) |); first exact: Rle_abs.
  have Htmp : D(V || W | P) <= exp (-2) ^ 2 * / 2.
    clear -Hcase x_pos.
    apply/ltRW/(ltR_leR_trans Hcase).
    apply (@leR_trans (x ^ 2 * / 2)); first exact: geR_minr.
    apply leR_wpmul2r; first exact/ltRW/invR_gt0.
    apply pow_incr.
    split; [exact: ltRW | exact: geR_minr].
  by apply mut_info_dist_ub.
rewrite -[X in _ <= X]oppRK in Htmp.
apply leR_oppr in Htmp.
apply (@leR_add2l minRate) in Htmp.
apply: (leR_trans _ Htmp) => {Htmp}.
suff Htmp : - xlnx (sqrt (2 * (D(V || W | P)))) <= gamma.
  rewrite oppRD addRA addRC -leR_subl_addr.
  rewrite [X in X <= _](_ : _ = - ((minRate + - cap) / 2)); last by field.
  rewrite leR_oppr oppRK -mulRA mulRC.
  apply/leRP; rewrite leR_pdivr_mulr //.
  rewrite mulRC -leR_pdivl_mulr; last first.
    by apply/ltRP; rewrite -mult_INR -plus_INR plusE multE ltR0n' addn_gt0 Bnot0.
  apply/leRP; by rewrite [in X in _ <= X]mulRC /Rdiv (mulRC _ (/ (_ + _))).
suff Htmp : xlnx x <= xlnx (sqrt (2 * (D(V || W | P)))).
  clear -Hx Htmp.
  rewrite leR_oppl.
  apply (@leR_trans (xlnx x)) => //.
  rewrite leR_oppl.
  apply/ltRW/(ltR_leR_trans Hx).
  subst gamma; exact: geR_minr.
apply/ltRW/Rgt_lt.
have Htmp : sqrt (2 * D(V || W | P)) < x.
  apply pow2_Rlt_inv; [exact: sqrt_pos | exact: ltRW | ].
  rewrite [in X in X < _]/= mulR1 sqrt_sqrt; last first.
    apply mulR_ge0; first exact/ltRW.
    apply leq0cdiv=> a Ha ? ?; by apply v_dom_by_w.
  apply/ltRP; rewrite mulRC -ltR_pdivl_mulr //.
  exact/ltRP/(ltR_leR_trans Hcase)/geR_minr.
apply xlnx_sdecreasing_0_Rinv_e => //.
- split; first exact/sqrt_pos.
  apply: (@leR_trans x _ _ (ltRW _)) => //.
  subst x.
  apply (@leR_trans (exp (-2))); first exact: geR_minr.
  apply/ltRW/exp_increasing; fourier.
- split; first exact: ltRW.
  apply (@leR_trans (exp (-2))); first exact: geR_minr.
  apply/ltRW/exp_increasing; fourier.
Qed.

End error_exponent_lower_bound.
