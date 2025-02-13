(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix.
From mathcomp Require Import mathcomp_extra boolp reals.
Require Import ssr_ext ssralg_ext realType_ext.
Require Import fdist proba convex.

(**md**************************************************************************)
(* # Jensen's inequality                                                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope convex_scope.
Local Open Scope fdist_scope.

Import Order.Theory GRing.Theory Num.Theory.

Section jensen_inequality.

Context {R : realType}.

Variable f : R^o -> R^o.
Variable D : {convex_set R^o}.
Hypothesis convex_f : convex_function_in D f.
Variables A : finType.

Lemma jensen_dist (r : A -> R) (X : R.-fdist A) :
  (forall a, r a \in D) ->
  f (\sum_(a in A) X a * r a) <= \sum_(a in A) X a * f (r a).
Proof.
move=> HDr.
apply (@proj1 _ (\sum_(a in fdist_supp X) X a * r a \in D)).
rewrite [in X in _ <= X]sum_fdist_supp [in X in X <= _]sum_fdist_supp /=.
apply: (@fdist_ind _ A (fun X =>
   f (\sum_(a in fdist_supp X) X a * r a) <=
   \sum_(a in fdist_supp X) X a * f (r a) /\ _)) => //.
move=> n IH {}X b cardA Hb.
case/boolP : (X b == 1) => [/eqP|]Xb1.
  move/eqP : (Xb1); rewrite fdist1E1 => /eqP ->.
  by rewrite supp_fdist1 !big_set1 fdist1xx !mul1r.
have HXb1: (X b).~ != 0 by rewrite onem_neq0.
set d := fdistD1 Xb1.
have HsumD1 q:
  \sum_(a in fdist_supp d) d a * q a =
  ((X b).~)^-1 * \sum_(a in fdist_supp d) X a * q a.
  rewrite (eq_bigr (fun a => ((X b).~)^-1 * (X a * q a))); last first.
    move=> i; rewrite inE fdistD1E.
    case: ifP => Hi; first by rewrite eqxx.
    by rewrite mulrCA mulrA onemE.
 by rewrite -big_distrr.
have {HsumD1}HsumXD1 q:
  \sum_(a in fdist_supp X) X a * q a =
  X b * q b + (X b).~ * (\sum_(a in fdist_supp d) d a * q a).
  rewrite HsumD1 mulrA mulfV // mul1r (bigD1 b) ?inE //=.
  rewrite (eq_bigl (fun a : A => a \in fdist_supp d)) //= => i.
  rewrite !inE /=.
  case HXi: (X i == 0) => //=.
    by rewrite (fdistD1_0 _ (eqP HXi)) eqxx.
  by rewrite fdistD1_eq0 // ?HXi // eq_sym.
rewrite 2!{}HsumXD1.
have /IH {IH}[IH HDd] : #|fdist_supp d| = n.
  by rewrite card_supp_fdistD1 // cardA.
split; last first.
  move/asboolP: (convex_setP D).
  move/(_ (r b) (\sum_(a in fdist_supp d) d a * r a) (probfdist X b)).
  by rewrite classical_sets.in_setE; apply; rewrite -classical_sets.in_setE.
have:= (convex_f (probfdist X b) (HDr b) HDd).
move/le_trans; apply.
by rewrite lerD2l; apply ler_wpM2l => //; rewrite onem_ge0.
Qed.

Local Open Scope proba_scope.

Lemma Jensen (P : R.-fdist A) (X : {RV P -> R}) : (forall x, X x \in D) ->
  f (`E X) <= `E (f `o X).
Proof.
move=> H.
rewrite {2}/Ex; erewrite eq_bigr; last by move=> a _; rewrite mulrC.
rewrite {1}/Ex; erewrite eq_bigr; last by move=> a _; rewrite mulrC.
exact: jensen_dist H.
Qed.

End jensen_inequality.

Section jensen_concave.
Context {R : realType}.

Variable f : R^o -> R^o.
Variable D : {convex_set R^o}.
Hypothesis concave_f : concave_function_in D f.
Variable A : finType.

Let g x := - f x.

Let convex_g : convex_function_in D g.
Proof.
rewrite /convex_function_in => x y t Dx Dy.
apply /R_convex_function_atN/concave_f => //; by case: t.
Qed.

Lemma jensen_dist_concave (r : A -> R) (X : R.-fdist A) :
  (forall x, r x \in D) ->
  \sum_(a in A) X a * f (r a) <= f (\sum_(a in A) X a * r a).
Proof.
move=> HDr.
rewrite -[X in _ <= X]opprK lerNr.
apply/(le_trans (jensen_dist convex_g X HDr)).
rewrite le_eqVlt -sumrN.
under [eqbLHS]eq_bigr do rewrite /g mulrN.
by rewrite eqxx.
Qed.

End jensen_concave.
