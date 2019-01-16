From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.
Require Import Reals Fourier ProofIrrelevance FunctionalExtensionality.
Require Import ssrR Reals_ext ssr_ext ssralg_ext logb Rbigop.
Require Import proba convex.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope reals_ext_scope.

Section jensen_inequality.

Variable f : R -> R.
Variable D : convex_set R_convType.
Hypothesis convex_f : convex_function_in D f.
Variables A : finType.

Local Hint Resolve leRR.

Lemma jensen_dist (r : A -> R) (X : dist A) :
  (forall a, D (r a)) ->
  f (\rsum_(a in A) r a * X a) <= \rsum_(a in A) f (r a) * X a.
Proof.
move=> HDr.
apply (@proj1 _ (D (\rsum_(a in dist_supp X) r a * X a))).
rewrite [in X in _ <= X]rsum_dist_supp [in X in X <= _]rsum_dist_supp /=.
apply: (@dist_ind A (fun X =>
   f (\rsum_(a in dist_supp X) r a * X a) <=
   \rsum_(a in dist_supp X) f (r a) * X a /\ _)) => //.
move=> n IH {X}X b cardA Hb.
case/boolP : (X b == 1) => Xb1.
  move/dist_supp_singleP: (eqP Xb1) => /eqP ->.
  by rewrite !big_set1 (eqP Xb1) !mulR1.
have HXb1: (X b).~ != 0 by rewrite onem_neq0.
set d := D1Dist.d Xb1.
have HsumD1 q:
  \rsum_(a in dist_supp d) q a * d a =
  /(X b).~ * \rsum_(a in dist_supp d) q a * X a.
  rewrite (eq_bigr (fun a => /(X b).~ * (q a * X a))); last first.
    move=> i; rewrite inE D1Dist.dE.
    case: ifP => Hi; first by rewrite eqxx.
    by rewrite /Rdiv (mulRC (/ _)) mulRA.
  by rewrite -big_distrr.
have {HsumD1}HsumXD1 q:
  \rsum_(a in dist_supp X) q a * X a =
  q b * X b + (X b).~ * (\rsum_(a in dist_supp d) q a * d a).
  rewrite HsumD1 /d /D1Dist.f /= mulRA mulRV // mul1R (bigD1 b) ?inE //=.
  rewrite (eq_bigl (fun a : A => a \in dist_supp d)) //= => i.
  rewrite !inE /=.
  case HXi: (X i == 0) => //=.
    by rewrite (D1Dist.d_0 _ (eqP HXi)) eqxx.
  by rewrite D1Dist.d_eq0 // ?HXi // eq_sym.
rewrite 2!{}HsumXD1.
have /IH {IH}[IH HDd] : #|dist_supp d| = n.
  by rewrite D1Dist.card_dist_supp // cardA.
have HXb: 0 <= X b <= 1 by split; [exact/dist_ge0|exact/dist_max].
split; last by rewrite mulRC; exact: (interval_convex (Prob.mk HXb)).
rewrite mulRC [in X in _ <= X]mulRC.
move/leR_trans: (convex_f (Prob.mk HXb) (HDr b) HDd); apply => /=.
rewrite leR_add2l; apply leR_wpmul2l => //; apply/onem_ge0; by case: HXb.
Qed.

Local Open Scope proba_scope.

Lemma Jensen (P : dist A) (X : {RV P -> R}) : (forall x, D (X x)) ->
  f (`E X) <= `E (comp_RV X f).
Proof. move/jensen_dist; apply. Qed.

End jensen_inequality.

Section jensen_concave.

Variable f : R -> R.
Variable D : convex_set R_convType.
Hypothesis concave_f : concave_function_in D f.
Variable A : finType.

Let g x := - f x.

Let convex_g : convex_function_in D g.
Proof.
rewrite /convex_function_in => x y t Dx Dy.
apply concave_f => //; by case: t.
Qed.

Lemma jensen_dist_concave (r : A -> R) (X : dist A) :
  (forall x, D (r x)) ->
  \rsum_(a in A) f (r a) * X a <= f (\rsum_(a in A) r a * X a).
Proof.
move=> HDr.
rewrite -[X in _ <= X]oppRK leR_oppr.
apply/(leR_trans (jensen_dist convex_g X HDr))/Req_le.
rewrite (big_morph _ morph_Ropp oppR0); by apply eq_bigr => a _; rewrite mulNR.
Qed.

End jensen_concave.
