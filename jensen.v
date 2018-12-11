From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.
Require Import Reals Fourier ProofIrrelevance FunctionalExtensionality.
Require Import ssrR Reals_ext ssr_ext ssralg_ext logb Rbigop.
Require Import proba convex.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section jensen_inequality.

Variable f : R -> R.
Variable D : interval.
Hypothesis convex_f : convexf_in D f.
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
have HXb1: 1 - X b != 0.
  by apply: contra Xb1; rewrite subR_eq0 eq_sym.
set d := D1Dist.d Xb1.
have HsumD1 q:
  \rsum_(a in dist_supp d) q a * d a =
  /(1 - X b) * \rsum_(a in dist_supp d) q a * X a.
  rewrite (eq_bigr (fun a => /(1-X b) * (q a * X a))); last first.
    move=> i; rewrite inE D1Dist.dE.
    case: ifP => Hi; first by rewrite eqxx.
    by rewrite /Rdiv (mulRC (/ _)) mulRA.
  by rewrite -big_distrr.
have {HsumD1}HsumXD1 q:
  \rsum_(a in dist_supp X) q a * X a =
  q b * X b + (1 - X b) * (\rsum_(a in dist_supp d) q a * d a).
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
split; last by rewrite mulRC; apply interval_convex.
rewrite mulRC.
refine (leR_trans
  (@convex_f (r b) (\rsum_(i in dist_supp d) r i * d i) _ _ HDd HXb) _) => //.
rewrite mulRC.
apply /leR_add2l /leR_wpmul2l => //.
rewrite leR_subr_addr add0R; by apply HXb.
Qed.

Local Open Scope proba_scope.

Lemma Jensen (X : rvar A) : (forall x, D (X x)) ->
  f (`E X) <= `E (mkRvar (`p_ X) (fun x => f (X x))).
Proof. move=> HDX; rewrite !ExE /=; by apply jensen_dist. Qed.

End jensen_inequality.

Section jensen_concave.

Variable f : R -> R.
Variable D : interval.
Hypothesis concave_f : concavef_in D f.
Variable A : finType.

Let g x := - f x.

Let convex_g : convexf_in D g.
Proof. by []. Qed.

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
