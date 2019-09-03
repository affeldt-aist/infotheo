(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg matrix.
From mathcomp Require Import boolp.
Require Import Reals.
Require Import ssrR Reals_ext ssr_ext ssralg_ext logb Rbigop.
Require Import proba convex_choice.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.
Local Open Scope reals_ext_scope.
Local Open Scope convex_scope.

Section jensen_inequality.

Variable f : R -> R.
Variable D : {convex_set R}.
Hypothesis convex_f : convex_function_in D f.
Variables A : finType.

Local Hint Resolve leRR.

Lemma jensen_dist (r : A -> R) (X : fdist A) :
  (forall a, r a \in D) ->
  f (\sum_(a in A) X a * r a) <= \sum_(a in A) X a * f (r a).
Proof.
move=> HDr.
apply (@proj1 _ (\sum_(a in fdist_supp X) X a * r a \in D)).
rewrite [in X in _ <= X]rsum_fdist_supp [in X in X <= _]rsum_fdist_supp /=.
apply: (@fdist_ind A (fun X =>
   f (\sum_(a in fdist_supp X) X a * r a) <=
   \sum_(a in fdist_supp X) X a * f (r a) /\ _)) => //.
move=> n IH {X}X b cardA Hb.
case/boolP : (X b == 1) => [/eqP|]Xb1.
  move/eqP : (Xb1); rewrite FDist1.dE1 => /eqP ->.
  by rewrite FDist1.supp !big_set1 FDist1.dE !eqxx /= !mul1R.
have HXb1: (X b).~ != 0 by rewrite onem_neq0.
set d := D1FDist.d Xb1.
have HsumD1 q:
  \sum_(a in fdist_supp d) d a * q a =
  /(X b).~ * \sum_(a in fdist_supp d) X a * q a.
  rewrite (eq_bigr (fun a => /(X b).~ * (X a * q a))); last first.
    move=> i; rewrite inE D1FDist.dE.
    case: ifP => Hi; first by rewrite eqxx.
    by rewrite /Rdiv mulRCA mulRA.
 by rewrite -big_distrr.
have {HsumD1}HsumXD1 q:
  \sum_(a in fdist_supp X) X a * q a =
  X b * q b + (X b).~ * (\sum_(a in fdist_supp d) d a * q a).
  rewrite HsumD1 mulRA mulRV // mul1R (bigD1 b) ?inE //=.
  rewrite (eq_bigl (fun a : A => a \in fdist_supp d)) //= => i.
  rewrite !inE /=.
  case HXi: (X i == 0) => //=.
    by rewrite (D1FDist.d_0 _ (eqP HXi)) eqxx.
  by rewrite D1FDist.d_eq0 // ?HXi // eq_sym.
rewrite 2!{}HsumXD1.
have /IH {IH}[IH HDd] : #|fdist_supp d| = n.
  by rewrite D1FDist.card_fdist_supp // cardA.
split; last first.
  move/asboolP: (convex_setP D) => /(_ (r b) (\sum_(a in fdist_supp d) d a * r a) (probfdist X b)).
  exact.
move/leR_trans: (convex_f (probfdist X b) (HDr b) HDd); apply => /=.
by rewrite leR_add2l; apply leR_wpmul2l => //; apply/onem_ge0.
Qed.

Local Open Scope proba_scope.

Lemma Jensen (P : fdist A) (X : {RV P -> R}) : (forall x, X x \in D) ->
  f (`E X) <= `E (comp_RV X f).
Proof.
move=> H.
rewrite {2}/Ex; erewrite eq_bigr; last by move=> a _; rewrite mulRC; reflexivity.
rewrite {1}/Ex; erewrite eq_bigr; last by move=> a _; rewrite mulRC; reflexivity.
exact: jensen_dist H.
Qed.

End jensen_inequality.

Section jensen_concave.

Variable f : R -> R.
Variable D : {convex_set R}.
Hypothesis concave_f : concave_function_in D f.
Variable A : finType.

Let g x := - f x.

Let convex_g : convex_function_in D g.
Proof.
rewrite /convex_function_in => x y t Dx Dy.
apply /R_convex_function_atN/concave_f => //; by case: t.
Qed.

Lemma jensen_dist_concave (r : A -> R) (X : fdist A) :
  (forall x, r x \in D) ->
  \sum_(a in A) X a * f (r a) <= f (\sum_(a in A) X a * r a).
Proof.
move=> HDr.
rewrite -[X in _ <= X]oppRK leR_oppr.
apply/(leR_trans (jensen_dist convex_g X HDr))/Req_le.
rewrite big_morph_oppR; by apply eq_bigr => a _; rewrite mulRN.
Qed.

End jensen_concave.
