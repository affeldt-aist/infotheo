From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.
Require Import Reals Fourier ProofIrrelevance FunctionalExtensionality.
Require Import ssrR Reals_ext ssr_ext ssralg_ext logb Rbigop.
Require Import proba.

Require Import Ranalysis_ext jensen.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* NB(saikawa):
Assume f is twice differentiable on an open interval I.
Let Df and DDf be the first and second derivatives of f.
Further assume DDf is always positive.  By applying MVT, we have :
forall a x \in I, exists c1 \in [a,x], f(x) = f(a) + (x-a) * Df(c1).
Fix a and x.  Applying MVT again, we further get :
exists c2 \in (a,c1), Df(c1) = Df(a) + (c1-a) * DDf(c2).
The two equations combined is :
f(x) = f(a) + (x-a) * Df(a) + (x-a)(c1-a) * DDf(c2).
The last term is then positive thanks to the assumption on DDf.
Now this is an equivalent condition to the convexity of f.
 *)

Section twice_der_convex.

Variables (f : R -> R) (I : R -> Prop).
Hypothesis HDf : pderivable f I.
Variable Df : R -> R.
Hypothesis DfE : forall x (Hx : I x), Df x = derive_pt f x (HDf Hx).
Hypothesis HDDf : pderivable Df I.
Variable DDf : R -> R.
Hypothesis DDfE : forall x (Hx : I x), DDf x = derive_pt Df x (HDDf Hx).
Hypothesis DDf_gt0 : forall x, 0 <= DDf x.

Lemma tmp a x : a < x -> I a -> I x -> exists c1 c2,
  f x = f a + (x - a) * Df a + (x - a) * (c1 - a) * DDf c2.
Proof.
move=> ax Ia Ix.
have : exists c1, a <= c1 <= x /\ f(x) = f(a) + (x-a) * Df(c1).
(*  case: (@MVT_cor1_pderivable a x f HDf ax) => c1 [Hc1 [H1 ac1x]].
  exists c1; split.
    admit.
  apply/eqP; rewrite addRC -subR_eq H1 mulRC; apply/eqP; congr (_ * _).
  by rewrite -DfE.*)
  admit.
case => c1 [Hc1 H1].
have : exists c2, a <= c2 <= c1 /\ Df c1 = Df a + (c1 - a) * DDf c2.
(*  have ac1 : a < c1.
    admit.
  case: (@MVT_cor1_pderivable a _ Df HDDf ax) => c2 [Hc2 [H2 ac2x]].
  exists c2; split.
    admit.
  apply/eqP; rewrite addRC -subR_eq H2 mulRC; apply/eqP; congr (_ * _).
  by rewrite -DDfE.*)
  admit.
case => c2 [Hc2 H2]; exists c1, c2.
by rewrite H1 -addRA -mulRA -mulRDr -H2.
Admitted.

End twice_der_convex.

Section log_concave.

Lemma pderivable_log a x1 : pderivable log (fun x2 : R => a <= x2 <= x1).
Proof.
rewrite /pderivable => x Hx.
rewrite /log /Log.
Admitted.

Lemma f_concave_gt0 x y t :
  0 < x -> 0 < y -> 0 <= t <= 1 -> concave_leq log x y t.
Proof.
move=> x0 y0 t01.
rewrite /concave_leq.
set x1 := t * x.
set a := (1 - t) * x.
set Df := fun x => / x.
set DDf := fun x => - / x^2.
(*have : log x1 = log a + (x1 - a) * Df a + (x1 - a) * (c1 - a) * DDf c2.*)
move: (@tmp log).
(* TODO: use tmp *)
Abort.

End log_concave.
