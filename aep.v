(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import Reals_ext ssr_ext ssralg_ext log2 Rssr Rbigop proba entropy.

(** * Asymptotic Equipartition Property (AEP) *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope tuple_ext_scope.

Local Open Scope ring_scope.

Definition map_mlog A n (P : dist A) : 'rV[rvar A]_n :=
  \row_(i < n) --log P.

Local Open Scope vec_ext_scope.

Section map_mlog_prop.

Variable A : finType.
Variable P : dist A.

Lemma E_map_mlog k i : `E ((map_mlog k.+1 P) ``_ i) = `H P.
Proof.
rewrite ExE /entropy (big_morph _ morph_Ropp oppR0).
apply eq_bigr=> a _; by rewrite mxE /= mulNR mulRC.
Qed.

Definition aep_sigma2 := (\rsum_(a in A) P a * (log (P a))^2 - (`H P)^2)%R.

Lemma V_map_mlog k i : `V ((map_mlog k.+1 P) ``_ i) = aep_sigma2.
Proof.
rewrite /Var E_trans_id_rem E_map_mlog.
rewrite ExE /aep_sigma2 /map_mlog.
rewrite mxE /= -/(_ ^ 2).
transitivity
  (\rsum_(a in A) ((- log (P a))^2 * P a - 2 * `H P * - log (P a) * P a + `H P ^ 2 * P a))%R.
  apply eq_bigr => a _; by field.
rewrite big_split /= big_split /= -big_distrr /= (pmf1 P) mulR1.
set s := (\rsum_(a in A) - _)%R.
have {s}-> : s = (- (2 * `H P ^ 2))%R.
  rewrite /s -{1}(big_morph _ morph_Ropp oppR0).
  f_equal.
  rewrite [X in X = _](_ : _ = \rsum_(a in A) (2 * `H P) * (- (P a * log (P a))))%R; last first.
    apply eq_bigr => a _; by rewrite -!mulRA (mulRC (P a)) mulNR.
  by rewrite -big_distrr /= -{1}(big_morph _ morph_Ropp oppR0) -/(entropy P) mulR1 mulRA.
set s := \rsum_(a in A ) _.
rewrite (_ : \rsum_(a in A) _ = s); last by rewrite /s; apply eq_bigr => a _; field.
by field.
Qed.

Lemma aep_sigma2_pos : 0 <= aep_sigma2.
Proof.
rewrite -(@V_map_mlog O ord0) /Var; apply Ex_nonneg => a.
rewrite /map_mlog /mlog_rv /=.
by apply le_sq.
Qed.

End map_mlog_prop.

Definition sum_mlog_prod A (P : dist A) n : rvar [finType of 'rV[A]_n] :=
  mkRvar (P `^ n) (fun t => \rsum_(i < n) - log (P t ``_ i))%R.

Lemma sum_mlog_prod_isum_map_mlog A (P : dist A) : forall n,
  sum_mlog_prod P n.+1 \=isum map_mlog n.+1 P.
Proof.
elim.
- move: (@isum_n_1 A (\row_i --log P)).
  set mlogP := cast_rv _.
  move=> HmlogP.
  set mlogprodP := sum_mlog_prod _ _.
  suff -> : mlogprodP = mlogP.
    rewrite [X in _ \=isum X](_ : _ = \row_i --log P); last by apply val_inj.
    by apply isum_n_1.
  rewrite /mlogprodP /mlogP /sum_mlog_prod /cast_rv /=.
  rewrite /rvar2tuple1 /= mxE /=.
  f_equal.
  apply FunctionalExtensionality.functional_extensionality => ta.
  by rewrite big_ord_recl big_ord0 Rplus_0_r.
- move=> n IHn.
  rewrite [X in _ \=isum X](_ : _ = row_mx (\row_(i < 1) (--log P)) (map_mlog n.+1 P)); last first.
    apply/matrixP => a b; rewrite {a}(ord1 a) !mxE.
    case: splitP.
      move=> a; rewrite {a}(ord1 a) => _; by rewrite mxE.
    move=> k _; by rewrite mxE.
  eapply isum_n_cons; first by apply IHn.
  + rewrite /sum; split.
    * by apply joint_prod_n.
    * move=> ta.
      rewrite /= big_ord_recl /=.
      congr (_ + _)%R.
      apply eq_bigr => i _; by rewrite mxE.
  + rewrite /inde_rv => /= x y.
    have : id_dist P (map_mlog n.+2 P).
      rewrite /id_dist => i.
      by rewrite mxE /=.
    move/(inde_rv_tuple_pmf_dist x y) => Htmp.
    eapply trans_eq.
      eapply trans_eq; last by apply Htmp.
      apply Pr_ext; apply/setP => ta; rewrite 2!inE /=.
      apply andb_id2l => _.
      congr (_ == _).
      apply eq_bigr => i _.
      by rewrite !mxE /mlog_rv /=.
    congr (_ * _)%R.
    apply Pr_ext; apply/setP => ta /=; rewrite 2!inE.
    congr (_ == _).
    apply eq_bigr => i _; by rewrite !mxE /=.
Qed.

(** Constant used in the statement of AEP: *)

Section aep_k0_constant.

Variable A : finType.
Variable P : dist A.

Definition aep_bound epsilon := (aep_sigma2 P / epsilon ^ 3)%R.

Lemma aep_bound_pos e (_ : 0 < e) : 0 <= aep_bound e.
Proof. apply Rle_mult_inv_pos; by [apply aep_sigma2_pos | apply pow_lt]. Qed.

Lemma aep_bound_decreasing e e' : 0 < e' <= e -> aep_bound e <= aep_bound e'.
Proof.
case=> Oe' e'e.
apply Rmult_le_compat_l; first by apply aep_sigma2_pos.
apply leR_inv => //.
- rewrite inE; exact/RltP/pow_lt.
- apply pow_incr => //; split; [exact/ltRW | exact/e'e ].
Qed.

End aep_k0_constant.

Section AEP.

Variable A : finType.
Variable P : dist A.
Variable n : nat.
Variable epsilon : R.
Hypothesis Hepsilon : 0 < epsilon.

Lemma aep : aep_bound P epsilon <= INR n.+1 ->
  Pr (P `^ n.+1) [set t | (0 <b P `^ n.+1 t) &&
    (Rabs ((--log (P `^ n.+1) '/ n.+1) t - `H P) >b= epsilon) ] <= epsilon.
Proof.
move=> Hbound.
apply Rle_trans with (aep_sigma2 P / (INR n.+1 * epsilon ^ 2))%R; last first.
  rewrite /aep_bound in Hbound.
  apply (Rmult_le_compat_r (epsilon / INR n.+1)) in Hbound; last first.
    apply Rle_mult_inv_pos; [exact/ltRW/Hepsilon | exact/lt_0_INR/ltP].
  rewrite [in X in _ <= X]mulRCA mulRV ?INR_eq0 // ?mulR1 in Hbound.
  eapply Rle_trans; last by apply Hbound.
  apply Req_le; field.
  split; [exact: not_0_INR | exact: gtR_eqF].
move: (sum_mlog_prod_isum_map_mlog P n) => Hisum.
move: (wlln (@E_map_mlog _ P n) (@V_map_mlog _ P n) Hisum Hepsilon) => law_large.
eapply Rle_trans; last by apply law_large.
apply Pr_incl; apply/subsetP => ta; rewrite 2!inE.
case/andP => H1.
rewrite [--log _]lock /= -lock.
set p1 := (_ * _)%R.
set p2 := (_ * _)%R.
suff : p1 = p2 by move=> <-.
rewrite /p1 /p2 {p1 p2}.
congr (_ * _)%R.
rewrite /map_mlog /=.
rewrite TupleDist.dE.
apply log_rmul_rsum_mlog, (rprodr_gt0_inv (dist_nonneg P)).
move: H1; by rewrite TupleDist.dE => /RltP.
Qed.

End AEP.
