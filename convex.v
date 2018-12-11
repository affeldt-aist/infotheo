(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.
Require Import Reals Fourier ProofIrrelevance FunctionalExtensionality.
Require Import ssrR Reals_ext Ranalysis_ext ssr_ext ssralg_ext logb Rbigop.
Require Import proba.

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

Local Open Scope reals_ext_scope.

Section interval.

Definition convex_interval (D : R -> Prop) := forall x y t,
  D x -> D y -> 0 <= t <= 1 -> D (t * x + t.~ * y).

Record interval := mkInterval {
  mem_interval :> R -> Prop;
  interval_convex : convex_interval mem_interval }.

End interval.

Lemma Rpos_convex : convex_interval (fun x => 0 < x).
Proof.
move=> x y t Hx Hy Ht.
case/boolP : (t == 0) => [/eqP ->| Ht0].
  by rewrite mul0R add0R (_ : _.~ = 1) ?mul1R // /onem subR0.
apply addR_gt0wl.
  apply mulR_gt0 => //.
  case/proj1: Ht Ht0 => // ->; by rewrite eqxx.
apply mulR_ge0; last exact: ltRW.
rewrite leR_subr_addr add0R; by case: Ht.
Qed.

Definition Rpos_interval := mkInterval Rpos_convex.

Section convex_function.

Implicit Types f : R -> R.

Definition convexf_leq f (x y t : R) :=
  f (t * x + t.~ * y) <= t * f x + t.~ * f y.

Definition convexf f := forall x y t : R, 0 <= t <= 1 -> convexf_leq f x y t.

Definition convexf_in (D : interval) f := forall x y t : R,
  D x -> D y -> 0 <= t <= 1 -> convexf_leq f x y t.

Definition strictly_convexf f := forall x y t : R,
  x != y -> 0 < t < 1 -> convexf_leq f x y t.

Lemma convexf_leqxx x t f :
  0 < x -> 0 <= t <= 1 -> convexf_leq f x x t.
Proof.
move=> x0 t01; rewrite /convexf_leq.
do 2 rewrite mulRBl mul1R addRCA addR_opp subRR addR0; exact/leRR.
Qed.

Lemma convexf_leq_onem x y t f : 0 < x -> 0 < y -> 0 <= t <= 1 -> x < y ->
  convexf_leq f x y t -> convexf_leq f y x t.~.
Proof.
move=> x0 y0 t01 xy; rewrite /convexf_leq => H.
rewrite onemK addRC; apply: (leR_trans H); rewrite addRC; exact/leRR.
Qed.

End convex_function.

Section concave_function.

Definition concavef_leq f := convexf_leq (fun x => - f x).

Lemma concavef_leqP f x y t : concavef_leq f x y t <->
  t * f x + t.~ * f y <=  f (t * x + t.~ * y).
Proof.
by rewrite /concavef_leq /convexf_leq leR_oppl oppRD 2!mulRN 2!oppRK.
Qed.

Lemma concavef_leqN f x y t : concavef_leq f x y t ->
  forall k, 0 <= k -> concavef_leq (fun x => f x * k) x y t.
Proof.
move=> H k k0; rewrite /concavef_leq /convexf_leq.
rewrite -3!mulNR 2!mulRA -mulRDl; exact: leR_wpmul2r.
Qed.

Definition concavef f := forall x y t : R, 0 <= t <= 1 -> concavef_leq f x y t.

Definition concavef_in (D : interval) f := forall x y t : R,
  D x -> D y -> 0 <= t <= 1 -> concavef_leq f x y t.

Definition strictly_concavef f := forall x y t : R,
  x != y -> 0 < t < 1 -> concavef_leq f x y t.

Lemma concavef_leq_xx x t f :
  0 < x -> 0 <= t <= 1 -> concavef_leq f x x t.
Proof. move=> *; rewrite /concavef_leq; exact: convexf_leqxx. Qed.

Lemma concavef_leq_onem x y t f :
  0 < x -> 0 < y -> 0 <= t <= 1 -> x < y ->
  concavef_leq f x y t -> concavef_leq f y x t.~.
Proof. move=> x0 y0 t01 xy; rewrite /concavef_leq; exact/convexf_leq_onem. Qed.

End concave_function.

(* ref: http://www.math.wisc.edu/~nagel/convexity.pdf *)
Section twice_derivable_convex.

Variables (f : R -> R) (a b : R).
Let I := fun x0 => a <= x0 <= b.
Hypothesis HDf : pderivable f I.
Variable Df : R -> R.
Hypothesis DfE : forall x (Hx : I x), Df x = derive_pt f x (HDf Hx).
Hypothesis HDDf : pderivable Df I.
Variable DDf : R -> R.
Hypothesis DDfE : forall x (Hx : I x), DDf x = derive_pt Df x (HDDf Hx).
Hypothesis DDf_ge0 : forall x, I x -> 0 <= DDf x.

Definition L (x : R) := f a + (x - a) / (b - a) * (f b - f a).

Hypothesis ab : a < b.

Lemma LE x : L x = (b - x) / (b - a) * f a + (x - a) / (b - a) * f b.
Proof.
rewrite /L mulRBr [in LHS]addRA addRAC; congr (_ + _).
rewrite addR_opp -{1}(mul1R (f a)) -mulRBl; congr (_ * _).
rewrite -(mulRV (b - a)); last by rewrite subR_eq0; exact/eqP/gtR_eqF.
by rewrite -mulRBl -addR_opp oppRB addRA subRK addR_opp.
Qed.

Lemma convexfP : (forall x, a <= x <= b -> 0 <= L x - f x) ->
  forall t, 0 <= t <= 1 -> convexf_leq f a b t.
Proof.
move=> H t t01; rewrite /convexf_leq.
set x := t * a + t.~ * b.
have : a <= x <= b.
  rewrite /x; split.
  - apply (@leR_trans (t * a + t.~ * a)).
      rewrite -mulRDl addRCA addR_opp subRR addR0 mul1R; exact/leRR.
    case/boolP : (t == 1) => [/eqP ->|t1].
      rewrite /onem subRR !mul0R !addR0; exact/leRR.
    rewrite leR_add2l; apply leR_wpmul2l; last exact/ltRW.
    rewrite subR_ge0; by case: t01.
  - apply (@leR_trans (t * b + t.~ * b)); last first.
      rewrite -mulRDl addRCA addR_opp subRR addR0 mul1R; exact/leRR.
    rewrite leR_add2r; apply leR_wpmul2l; [by case: t01 | exact/ltRW].
move/H; rewrite subR_ge0 => /leR_trans; apply.
rewrite LE //.
have -> : (b - x) / (b - a) = t.
  rewrite /x -addR_opp oppRD addRCA mulRBl mul1R oppRB (addRCA b).
  rewrite addR_opp subRR addR0 -mulRN addRC -mulRDr addR_opp.
  rewrite /Rdiv -mulRA mulRV ?mulR1 // subR_eq0; exact/eqP/gtR_eqF.
have -> : (x - a) / (b - a) = t.~.
  rewrite /x -addR_opp addRAC -{1}(oppRK a) mulRN -mulNR -{2}(mul1R (- a)).
  rewrite -mulRDl (addRC _ 1) addR_opp -mulRDr addRC addR_opp.
  rewrite /Rdiv -mulRA mulRV ?mulR1 // subR_eq0; exact/eqP/gtR_eqF.
exact/leRR.
Qed.

Lemma second_derivative_convexf : forall t, 0 <= t <= 1 -> convexf_leq f a b t.
Proof.
have note1 : forall x, 1 = (x - a) / (b - a) + (b - x) / (b - a).
  move=> x; rewrite -mulRDl addRC addRA subRK addR_opp mulRV // subR_eq0.
  exact/eqP/gtR_eqF.
have step1 : forall x, f x = (x - a) / (b - a) * f x + (b - x) / (b - a) * f x.
  by move=> x; rewrite -mulRDl -note1 mul1R.
apply convexfP => // x axb.
rewrite /L.
case: axb.
  rewrite leR_eqVlt => -[-> _|].
  rewrite /L subRR div0R mul0R addR0 subRR; exact/leRR.
move=> ax.
rewrite leR_eqVlt => -[->|].
rewrite /L /Rdiv mulRV ?mul1R; last by rewrite subR_eq0; exact/eqP/gtR_eqF.
rewrite addRC subRK subRR; exact/leRR.
move=> xb.
have {step1}step2 : L x - f x =
  (x - a) * (b - x) / (b - a) * ((f b - f x) / (b - x)) -
  (b - x) * (x - a) / (b - a) * ((f x - f a) / (x - a)).
  rewrite {1}step1 {step1}.
  rewrite -addR_opp oppRD addRA addRC addRA.
  rewrite LE //.
  rewrite {1}/Rdiv -(mulRN _ (f x)) -/(Rdiv _ _).
  rewrite addRA -mulRDr (addRC _ (f a)) (addR_opp (f a)).
  rewrite -mulRN -addRA -mulRDr (addR_opp (f b)).
  rewrite addRC.
  rewrite -(oppRK (f a - f x)) mulRN addR_opp oppRB.
  congr (_ + _).
  - rewrite {1}/Rdiv -!mulRA; congr (_ * _); rewrite mulRCA; congr (_ * _).
    rewrite mulRCA mulRV ?mulR1 // subR_eq0; exact/eqP/gtR_eqF.
  - rewrite -!mulNR -!mulRA; congr (_ * _); rewrite mulRCA; congr (_ * _).
    rewrite mulRCA mulRV ?mulR1 // subR_eq0; exact/eqP/gtR_eqF.
have [c2 [Ic2 Hc2]] : exists c2, x < c2 < b /\ (f b - f x) / (b - x) = Df c2.
  have H : pderivable f (fun x0 => x <= x0 <= b).
    move=> z [z1 z2]; apply HDf; split => //.
    apply (@leR_trans x) => //; exact: ltRW.
  case: (@MVT_cor1_pderivable x b f H xb) => c2 [Ic2 [H1 H2]].
  exists c2; split => //.
  rewrite H1 /Rdiv -mulRA mulRV ?mulR1; last first.
    by rewrite subR_eq0; exact/eqP/gtR_eqF.
  rewrite DfE; last by move=> ?; exact: proof_derive_irrelevance.
  split.
    apply (@leR_trans x); [exact/ltRW | by case: Ic2 H1].
  by case: H2 => _ /ltRW.
have [c1 [Ic1 Hc1]] : exists c1, a < c1 < x /\ (f x - f a) / (x - a) = Df c1.
  have H : pderivable f (fun x0 => a <= x0 <= x).
    move=> z [z1 z2]; apply HDf; split => //.
    apply (@leR_trans x) => //; exact: ltRW.
  case: (@MVT_cor1_pderivable a x f H ax) => c1 [Ic1 [H1 H2]].
  exists c1; split => //.
  rewrite H1 /Rdiv -mulRA mulRV ?mulR1; last first.
    by rewrite subR_eq0; exact/eqP/gtR_eqF.
  rewrite DfE; last by move=> ?; exact: proof_derive_irrelevance.
  split.
  - by case: H2 => /ltRW.
  - apply (@leR_trans x).
    by case: H2 => _ /ltRW.
    apply (@leR_trans c2); apply/ltRW; by case: Ic2.
have c1c2 : c1 < c2 by apply (@ltR_trans x); [case: Ic1 | case: Ic2].
have {step2 Hc1 Hc2}step3 : L x - f x =
  (b - x) * (x - a) * (c2 - c1) / (b - a) * ((Df c2 - Df c1) / (c2 - c1)).
  rewrite {}step2 Hc2 Hc1 (mulRC (x - a)) -mulRBr {1}/Rdiv -!mulRA.
  congr (_ * (_ * _)); rewrite mulRCA; congr (_ * _).
  rewrite mulRCA mulRV ?mulR1 // subR_eq0; by move/gtR_eqF/eqP : c1c2.
have [d [Id H]] : exists d, c1 < d < c2 /\ (Df c2 - Df c1) / (c2 - c1) = DDf d.
  have H : pderivable Df (fun x0 => c1 <= x0 <= c2).
    move=> z [z1 z2]; apply HDDf; split => //.
    - apply (@leR_trans c1) => //; by case: Ic1 => /ltRW.
    - apply (@leR_trans c2) => //; by case: Ic2 => _ /ltRW.
  case: (@MVT_cor1_pderivable c1 c2 Df H c1c2) => d [Id [H1 H2]].
  exists d; split => //.
  rewrite H1 /Rdiv -mulRA mulRV ?mulR1; last first.
    by rewrite subR_eq0; exact/eqP/gtR_eqF.
  rewrite DDfE; last by move=> ?; exact: proof_derive_irrelevance.
  split.
  - apply (@leR_trans c1); last by case: Id H1.
    apply/ltRW; by case: Ic1.
  - apply (@leR_trans c2); last by case: Ic2 => _ /ltRW.
    by case: H2 => _ /ltRW.
rewrite {}step3 {}H.
apply/mulR_ge0; last first.
  apply: DDf_ge0; split.
    apply (@leR_trans c1).
      apply/ltRW; by case: Ic1.
     by case: Id => /ltRW.
  apply (@leR_trans c2).
    by case: Id => _ /ltRW.
  apply/ltRW; by case: Ic2.
apply/mulR_ge0; last by apply/ltRW/invR_gt0; rewrite subR_gt0.
apply/mulR_ge0; last first.
  by rewrite subR_ge0; case: Id => Id1 Id2; apply (@leR_trans d); exact/ltRW.
apply/mulR_ge0; rewrite subR_ge0; exact/ltRW.
Qed.

End twice_derivable_convex.
