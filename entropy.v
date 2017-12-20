(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div fintype.
From mathcomp Require Import tuple finfun bigop.
Require Import Reals Fourier.
Require Import Reals_ext Rssr Rbigop log2 ln_facts proba divergence.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Entropy of a distribution *)

Section entropy_definition.

Variable A : finType.
Variable P : dist A.

Definition entropy := - \rsum_(a in A) P a * log (P a).
Local Notation "'`H'" := (entropy) (at level 5).

Lemma entropy_pos : 0 <= `H.
Proof.
rewrite /entropy big_endo; last 2 first.
  move=> *; by rewrite Ropp_plus_distr.
  by rewrite Ropp_0.
rewrite (_ : \rsum_(_ in _) _ = \rsum_(i in A | predT A) - (P i * log (P i))); last first.
  apply eq_bigl => i /=; by rewrite inE.
apply Rle_big_0_P_g => i _.
case: (Req_EM_T (P i) 0).
  (* NB: this step in a standard textbook would be handled as a
     consequence of lim x->0 x log x = 0 *)
  move=> ->.
  rewrite Rmult_0_l.
  fourier.
move=> Hi.
rewrite Rmult_comm -Ropp_mult_distr_l_reverse.
apply Rmult_le_pos; last by apply dist_nonneg.
apply Ropp_0_ge_le_contravar, Rle_ge.
rewrite -log_1.
apply log_increasing_le; last by apply dist_max.
apply Rlt_le_neq; by [apply dist_nonneg | auto].
Qed.

Hypothesis P_pos : forall b, 0 < P b.

Lemma entropy_pos_P_pos : 0 <= `H.
Proof.
rewrite /entropy big_endo; last 2 first.
  move=> *; by rewrite Ropp_plus_distr.
  by rewrite Ropp_0.
rewrite (_ : \rsum_(_ in _) _ = \rsum_(i in A | predT A) - (P i * log (P i))).
  apply Rle_big_0_P_g => i _.
  rewrite Rmult_comm -Ropp_mult_distr_l_reverse.
  apply Rmult_le_pos; last by apply dist_nonneg.
  apply Ropp_0_ge_le_contravar, Rle_ge.
  rewrite -log_1.
  apply log_increasing_le; by [apply P_pos | apply dist_max].
apply eq_bigl => i /=; by rewrite inE.
Qed.

End entropy_definition.

Notation "'`H'" := (entropy) (at level 5) : entropy_scope.

Local Open Scope entropy_scope.
Local Open Scope proba_scope.

Lemma entropy_Ex {A} (P : dist A) : `H P = `E (--log P).
Proof.
rewrite /entropy /mlog_rv ExE /= (big_morph _ morph_Ropp Ropp_0).
apply eq_bigr => a _; by rewrite mulRC -Ropp_mult_distr_l_reverse.
Qed.

Lemma xlnx_entropy {A} (P : dist A) :
  `H P = / ln 2 * - \rsum_(a : A) xlnx (P a).
Proof.
rewrite /entropy; f_equal; rewrite Ropp_mult_distr_r_reverse; f_equal.
rewrite (big_morph _ (morph_mulRDr _) (mulR0 _)).
apply eq_bigr => a _ ;rewrite /log /Rdiv mulRA mulRC; f_equal.
rewrite /xlnx; case : ifP => // /RltP Hcase.
have : P a = 0; last by move=> ->; rewrite mul0R.
case (Rle_lt_or_eq_dec 0 (P a)) => //; by apply dist_nonneg.
Qed.

Lemma entropy_uniform {A : finType} n (HA : #|A| = n.+1) :
  `H (Uniform.d HA) = log (INR #|A|).
Proof.
rewrite /entropy /Uniform.d /Uniform.f /=.
rewrite big_const iter_Rplus /Rdiv mul1R mulRA Rinv_r; last first.
  rewrite HA; by apply not_0_INR.
rewrite mul1R log_Rinv; last by rewrite HA; apply lt_0_INR; apply/ltP.
by rewrite Ropp_involutive.
Qed.

Local Open Scope reals_ext_scope.

Lemma entropy_max {A : finType} (P : dist A) : `H P <= log (INR #|A|).
Proof.
have [n HA] : exists n, #|A| = n.+1.
  exists (#|A|.-1); rewrite prednK //; by apply (dist_support_not_empty P).
have : P << (Uniform.d HA) by apply dom_by_uniform.
move/leq0div => H.
rewrite /div in H.
suff Htmp : 0 <= - `H P + log (INR #|A|) by fourier.
eapply Rle_trans; first by apply H.
apply Req_le.
transitivity (\rsum_(a|a \in A) P a * log (P a) + \rsum_(a|a \in A) P a * - log ((Uniform.d HA) a)).
  rewrite -big_split /=.
  apply eq_bigr => a _.
  by rewrite mulRDr.
rewrite /= /Uniform.f /= /Rdiv mul1R.
rewrite -[in X in _ + X = _]big_distrl /= pmf1 mul1R.
rewrite /entropy Ropp_involutive.
rewrite log_Rinv; last first.
  rewrite HA.
  apply lt_0_INR; by apply/ltP.
by rewrite Ropp_involutive.
Qed.
