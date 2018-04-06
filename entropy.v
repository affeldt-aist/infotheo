(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun bigop.
Require Import Reals Fourier.
Require Import Reals_ext Rssr Rbigop log2 ln_facts proba divergence.

(** * Entropy of a distribution *)

Reserved Notation "'`H'" (at level 5).

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section entropy_definition.

Variable A : finType.
Variable P : dist A.

Definition entropy := - \rsum_(a in A) P a * log (P a).
Local Notation "'`H'" := (entropy).

Lemma entropy_pos : 0 <= `H.
Proof.
rewrite /entropy big_endo ?oppR0 //; last by move=> *; rewrite oppRD.
rewrite (_ : \rsum_(_ in _) _ = \rsum_(i in A | predT A) - (P i * log (P i))); last first.
  apply eq_bigl => i /=; by rewrite inE.
apply rsumr_ge0 => i _.
case/boolP : (P i == 0) => [/eqP ->|Hi].
  (* NB: this step in a standard textbook would be handled as a
     consequence of lim x->0 x log x = 0 *)
  rewrite mul0R oppR0; exact: Rle_refl.
rewrite mulRC -mulNR.
apply mulR_ge0; last exact: dist_nonneg.
apply oppR_ge0.
rewrite /log -(Log_1 2).
apply Log_increasing_le => //; last exact: dist_max.
apply/RltP; rewrite lt0R Hi; exact/RleP/dist_nonneg.
Qed.

Hypothesis P_pos : forall b, 0 < P b.

Lemma entropy_pos_P_pos : 0 <= `H.
Proof.
rewrite /entropy big_endo ?oppR0 //; last by move=> *; rewrite oppRD.
rewrite (_ : \rsum_(_ in _) _ = \rsum_(i in A | predT A) - (P i * log (P i))).
  apply rsumr_ge0 => i _.
  rewrite mulRC -mulNR.
  apply mulR_ge0; last by apply dist_nonneg.
  apply oppR_ge0.
  rewrite /log -(Log_1 2).
  apply Log_increasing_le => //; by [by apply P_pos | exact: dist_max].
apply eq_bigl => i /=; by rewrite inE.
Qed.

End entropy_definition.

Notation "'`H'" := (entropy) : entropy_scope.

Local Open Scope entropy_scope.
Local Open Scope proba_scope.

Lemma entropy_Ex {A} (P : dist A) : `H P = `E (--log P).
Proof.
rewrite /entropy /mlog_rv ExE /= (big_morph _ morph_Ropp oppR0).
apply eq_bigr => a _; by rewrite mulRC -mulNR.
Qed.

Lemma xlnx_entropy {A} (P : dist A) :
  `H P = / ln 2 * - \rsum_(a : A) xlnx (P a).
Proof.
rewrite /entropy mulRN; f_equal.
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
rewrite big_const iter_Rplus div1R mulRA mulRV; last by rewrite INR_eq0 HA.
rewrite mul1R /log LogV ?oppRK //; by rewrite HA; apply/lt_0_INR/ltP.
Qed.

Local Open Scope reals_ext_scope.

Lemma entropy_max {A : finType} (P : dist A) : `H P <= log (INR #|A|).
Proof.
have [n HA] : exists n, #|A| = n.+1.
  exists (#|A|.-1); rewrite prednK //; by apply (dist_domain_not_empty P).
have : P << (Uniform.d HA) by apply dom_by_uniform.
move/leq0div => H.
rewrite /div in H.
suff Htmp : 0 <= - `H P + log (INR #|A|) by fourier.
eapply Rle_trans; first by apply H.
apply Req_le.
transitivity (\rsum_(a|a \in A) P a * log (P a) + \rsum_(a|a \in A) P a * - log ((Uniform.d HA) a)).
  rewrite -big_split /=.
  apply eq_bigr => a _; by rewrite mulRDr.
rewrite /= /Uniform.f /= div1R -[in X in _ + X = _]big_distrl /= pmf1 mul1R.
rewrite /entropy oppRK /log LogV ?oppRK // HA; apply/RltP; by rewrite ltR0n.
Qed.