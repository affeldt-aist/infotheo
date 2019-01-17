(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.
Require Import Reals Lra ProofIrrelevance FunctionalExtensionality.
Require Import ssrR Reals_ext Ranalysis_ext ssr_ext ssralg_ext logb Rbigop.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "x <| p |> y" (format "x  <| p |>  y", at level 50).

Local Open Scope reals_ext_scope.

Module ConvexSpace.
Record class_of (car : Type) : Type := Class {
  conv : car -> car -> prob -> car ;
  _ : forall x y, conv x y (`Pr 1) = x ;
  _ : forall x p, conv x x p = x ;
  _ : forall x y p, conv x y p = conv y x (`Pr p.~) ;
  _ : forall (p q r s : prob) (d0 d1 d2 : car),
      p = (r * s)%R :> R -> (s.~ = p.~ * q.~)%R ->
      conv d0 (conv d1 d2 q) p = conv (conv d0 d1 r) d2 s
}.
Structure t : Type := Pack { car : Type ; class : class_of car }.
Module Exports.
Definition Conv (T : t) : car T -> car T -> prob -> car T :=
  let: Pack _ (Class x _ _ _ _) := T in x.
Arguments Conv {T} : simpl never.
Notation "x <| p |> y" := (Conv x y p) : convex_scope.
Notation convType := t.
Coercion car : convType >-> Sortclass.
End Exports.
End ConvexSpace.
Export ConvexSpace.Exports.

Local Open Scope convex_scope.

Section convex_space_lemmas.
Variables A : convType.
Lemma conv1 (x y : A) : x <| `Pr 1 |> y = x.
Proof. by case: A x y => ? []. Qed.
Lemma convmm (x : A) (p : prob) : x <| p |> x = x.
Proof. by case: A x => ? []. Qed.
Lemma convC (x y : A) (p : prob) : x <| p |> y = y <| `Pr p.~ |> x.
Proof. by case: A x y => ? []. Qed.
Lemma convA (p q r s : prob) (d0 d1 d2 : A) :
  p = (r * s)%R :> R -> (s.~ = p.~ * q.~)%R ->
  d0 <| p |> (d1 <| q |> d2) = (d0 <| r |> d1) <| s |> d2.
Proof.
case: A d0 d1 d2 p q r s => ? [] f H0 H1 H2 H3 d0 d1 d2 p q r s K1 K2.
by rewrite /Conv; rewrite (H3 _ _ _ _ _ _ _ K1 K2).
Qed.
End convex_space_lemmas.

Section convex_space_prop.
Variables A : convType.
Lemma conv0 (x y : A) : x <| `Pr 0 |> y = y.
Proof.
rewrite convC /= (_ : `Pr 0.~ = `Pr 1) ?conv1 //.
by apply prob_ext; rewrite /onem /= subR0.
Qed.
End convex_space_prop.

Definition avg (x y : R) (t : prob) := (t * x + t.~ * y)%R.
Lemma avg1 (x y : R) : avg x y (`Pr 1) = x.
Proof. by rewrite /avg /= mul1R /onem subRR mul0R addR0. Qed.
Lemma avgI (x : R) (p : prob) : avg x x p = x.
Proof. by rewrite /avg -mulRDl onemKC mul1R. Qed.
Lemma avgC (x y : R) (p : prob) : avg x y p = avg y x `Pr p.~.
Proof. by rewrite /avg onemK addRC. Qed.
Lemma avgA (p q r s : prob) (d0 d1 d2 : R) :
  p = (r * s)%R :> R ->
  s.~ = (p.~ * q.~)%R ->
  avg d0 (avg d1 d2 q) p = avg (avg d0 d1 r) d2 s.
Proof.
move: p q r s => -[p Hp] [q Hq] [r Hr] [s Hs] /= K1.
rewrite /avg /onem => K2 /=.
rewrite (mulRDr s) -addRA (mulRA s) (mulRC s r) -K1; congr (_ + _)%R.
rewrite K2 mulRDr -(mulRA (1 - p)%R); congr (_ + _)%R.
rewrite !mulRA; congr (_ * _)%R.
rewrite mulRBl mulRBr mulR1 (mulRC s r) -K1; lra.
Qed.

Definition R_convMixin := ConvexSpace.Class avg1 avgI avgC avgA.
Canonical R_convType := ConvexSpace.Pack R_convMixin.

Module FunConvType.
Variables (A:Type) (B:convType).

Definition T := A -> B.

Definition avg (x y : T) (t : prob) :=
  fun a : A => (x a <| t |> y a).
Lemma avg1 (x y : T) : avg x y (`Pr 1) = x.
Proof.
  apply FunctionalExtensionality.functional_extensionality => a.
  by apply conv1.
Qed.
Lemma avgI (x : T) (p : prob) : avg x x p = x.
Proof.
  apply FunctionalExtensionality.functional_extensionality => a.
  by apply convmm.
Qed.
Lemma avgC (x y : T) (p : prob) : avg x y p = avg y x `Pr p.~.
Proof.
  apply FunctionalExtensionality.functional_extensionality => a.
  by apply convC.
Qed.
Lemma avgA (p q r s : prob) (d0 d1 d2 : T) :
  p = (r * s)%R :> R ->
  s.~ = (p.~ * q.~)%R ->
  avg d0 (avg d1 d2 q) p = avg (avg d0 d1 r) d2 s.
Proof.
  move => *.
  apply FunctionalExtensionality.functional_extensionality => a.
  by apply convA.
Qed.

Definition Fun_convMixin := ConvexSpace.Class avg1 avgI avgC avgA.
Canonical Fun_convType := ConvexSpace.Pack Fun_convMixin.

End FunConvType.

Section convex_set.
Variable A : convType.
Definition is_convex_set (D : A -> Prop) := forall x y t, D x -> D y -> D (x <| t |> y).
Record convex_set := mkConvexSet {
  mem_interval :> A -> Prop;
  interval_convex : is_convex_set mem_interval }.
End convex_set.

Section convex_function_def.
Variables (A : convType) (f : A -> R).

Definition convex_function_at a0 a1 t := (f (a0 <| t |> a1) <= f a0 <| t |> f a1)%R.

Definition strictly_convexf_at := forall (x y : A) (t : prob),
  x <> y -> (0 < t < 1)%R -> convex_function_at x y t.

Definition convex_function := forall a0 a1 t, convex_function_at a0 a1 t.

Lemma convex_functionP : convex_function <-> forall x y t, convex_function_at x y t.
Proof. split => [H x y t|H x y t]; exact: H. Qed.

Lemma convex_function_atxx x t : convex_function_at x x t.
Proof. rewrite /convex_function_at !convmm; exact/leRR. Qed.

End convex_function_def.

Section convex_function_prop.
Variable (A : convType).

Lemma convex_function_sym (f : A -> R) x y : (forall t, convex_function_at f x y t) ->
  forall t, convex_function_at f y x t.
Proof.
move => H t; move: (H (`Pr t.~)).
by rewrite /convex_function_at /= convC -probK (convC (f x)) -probK.
Qed.

End convex_function_prop.

Section concave_function_def.
Variables (A : convType) (f : A -> R).
Definition concave_function_at := convex_function_at (fun x => - f x)%R.
Definition concave_function := convex_function (fun x => - f x)%R.
Definition strictly_concavef_at := forall (x y : A) (t : prob),
  x <> y -> (0 < t < 1)%R -> concave_function_at x y t.
End concave_function_def.

Section concave_function_prop.
Variable (A : convType).
Section prop.
Variable (f : A -> R).

Lemma concave_function_atxx x t : concave_function_at f x x t.
Proof. exact: convex_function_atxx. Qed.

Lemma convex_functionN : concave_function f -> convex_function (fun x => - f x)%R.
Proof. by []. Qed.

Lemma concave_functionN : convex_function f -> concave_function (fun x => - f x)%R.
Proof.
move=> H; rewrite /concave_function (_ : (fun x => - - f x)%R = f) //.
apply FunctionalExtensionality.functional_extensionality => ?; by rewrite oppRK.
Qed.
End prop.
Section prop2.
Lemma convex_functionB (f g : A -> R) :
  convex_function f -> concave_function g -> convex_function (fun x => f x - g x)%R.
Proof.
move=> H1 H2 p q t.
rewrite /convex_function_at /=.
rewrite {3}/Conv /= /avg /= (* TODO *) 2!mulRBr addRAC addRA.
move: (H1 p q t) => {H1}H1.
rewrite -addR_opp -addRA; apply leR_add => //.
rewrite -2!mulRN addRC; exact: H2.
Qed.
Lemma concave_functionB (f g : A -> R) :
  concave_function f -> convex_function g -> concave_function (fun x => f x - g x)%R.
Proof.
move=> H1 H2.
rewrite (_ : (fun _ => _) = (fun x => - (g x - f x)))%R; last first.
  apply FunctionalExtensionality.functional_extensionality => x; by rewrite oppRB.
exact/concave_functionN/convex_functionB.
Qed.
End prop2.
End concave_function_prop.

Section affine_function_def.
Variables (A : convType) (f : A -> R).
Definition affine_function := convex_function f /\ concave_function f.
End affine_function_def.

Section affine_function_prop.
Variables (A : convType) (f : A -> R).
Lemma affine_functionP : affine_function f <-> forall p q (t : prob),
  f (p <| t |> q) = f p <| t |> f q.
Proof.
split => [[H1 H2] p q t| H]; last first.
  split.
  - move=> p q t; rewrite /convex_function_at /= H //; exact/leRR.
  - move=> p q t; rewrite /convex_function_at H // oppRD -!mulRN; exact/leRR.
rewrite eqR_le; split; first exact/H1.
rewrite -[X in (X <= _)%R](oppRK _)leR_oppl oppRD -2!mulRN; exact/H2.
Qed.
Lemma affine_functiontN : affine_function f -> affine_function (fun x => - f x)%R.
Proof. case=> H1 H2; split => //; exact/concave_functionN. Qed.
End affine_function_prop.

Section convex_function_in_def.
Variables (A : convType) (D : convex_set A) (f : A -> R).
Definition convex_function_in := forall x y t, D x -> D y -> convex_function_at f x y t.
Definition concave_function_in := forall x y t, D x -> D y -> concave_function_at f x y t.
End convex_function_in_def.

Section convex_set_R.

Lemma Rpos_convex : is_convex_set (fun x => 0 < x)%R.
Proof.
move=> x y t Hx Hy.
case/boolP : (t == `Pr 0) => [/eqP ->| Ht0]; first by rewrite conv0.
apply addR_gt0wl; first by apply mulR_gt0 => //; exact/prob_gt0.
apply mulR_ge0; [exact/onem_ge0/prob_le1 | exact: ltRW].
Qed.

Definition Rpos_interval := mkConvexSet Rpos_convex.

Lemma Rnonneg_convex : is_convex_set (fun x => 0 <= x)%R.
Proof.
rewrite /is_convex_set => x y t Hx Hy.
apply addR_ge0; apply/mulR_ge0 => //; [exact/prob_ge0 | apply/onem_ge0; exact/prob_le1].
Qed.

Definition Rnonneg_interval := mkConvexSet Rnonneg_convex.

Lemma open_interval_convex a b (Hab : (a < b)%R) : is_convex_set (fun x => a < x < b)%R.
Proof.
move=> x y t [xa xb] [ya yb].
case/boolP : (t == `Pr 0) => [/eqP|]t0; first by rewrite t0 conv0.
case/boolP : (t == `Pr 1) => [/eqP|]t1; first by rewrite t1 conv1.
apply conj.
- rewrite -[X in (X < t * x + t.~ * y)%R]mul1R -(onemKC t) mulRDl.
  apply ltR_add; rewrite ltR_pmul2l //; [exact/prob_gt0 | exact/onem_gt0/prob_lt1].
- rewrite -[X in (_ + _ < X)%R]mul1R -(onemKC t) mulRDl.
  apply ltR_add; rewrite ltR_pmul2l //; [exact/prob_gt0 | exact/onem_gt0/prob_lt1].
Qed.

Lemma open_unit_interval_convex : is_convex_set (fun x => 0 < x < 1)%R.
Proof. apply /open_interval_convex /Rlt_0_1. Qed.

Definition open_unit_interval := mkConvexSet open_unit_interval_convex.

End convex_set_R.

Section convex_function_R.

Implicit Types f : R_convType -> R.

Lemma concave_function_atN f x y t : concave_function_at f x y t ->
  forall k, (0 <= k)%R -> concave_function_at (fun x => f x * k)%R x y t.
Proof.
move=> H k k0; rewrite /concave_function_at /convex_function_at.
rewrite {2}/Conv /= /avg /= (* TODO *).
rewrite -3!mulNR 2!mulRA -mulRDl; exact: leR_wpmul2r.
Qed.

Lemma convexf_at_onem x y (t : prob) f : (0 < x -> 0 < y -> x < y ->
  convex_function_at f x y t -> convex_function_at f y x (`Pr t.~))%R.
Proof.
move=> x0 y0 xy H; rewrite /convex_function_at.
rewrite {2}/Conv /= /avg /= onemK addRC.
rewrite /convex_function_at /Conv /= /avg /= in H.
rewrite /Conv /= /avg /= onemK addRC.
apply: (leR_trans H); rewrite addRC; exact/leRR.
Qed.

Lemma concavef_at_onem x y (t : prob) f : (0 < x -> 0 < y -> x < y ->
  concave_function_at f x y t -> concave_function_at f y x (`Pr t.~))%R.
Proof. move=> ? ? ?; exact/convexf_at_onem. Qed.

End convex_function_R.

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

(* ref: http://www.math.wisc.edu/~nagel/convexity.pdf *)
Section twice_derivable_convex.

Variables (f : R -> R) (a b : R).
Let I := fun x0 => (a <= x0 <= b)%R.
Hypothesis HDf : pderivable f I.
Variable Df : R -> R.
Hypothesis DfE : forall x (Hx : I x), Df x = derive_pt f x (HDf Hx).
Hypothesis HDDf : pderivable Df I.
Variable DDf : R -> R.
Hypothesis DDfE : forall x (Hx : I x), DDf x = derive_pt Df x (HDDf Hx).
Hypothesis DDf_ge0 : forall x, I x -> (0 <= DDf x)%R.

Definition L (x : R) := (f a + (x - a) / (b - a) * (f b - f a))%R.

Hypothesis ab : (a < b)%R.

Lemma LE x : L x = ((b - x) / (b - a) * f a + (x - a) / (b - a) * f b)%R.
Proof.
rewrite /L mulRBr [in LHS]addRA addRAC; congr (_ + _)%R.
rewrite addR_opp -{1}(mul1R (f a)) -mulRBl; congr (_ * _)%R.
rewrite -(mulRV (b - a)); last by rewrite subR_eq0; exact/eqP/gtR_eqF.
by rewrite -mulRBl -addR_opp oppRB addRA subRK addR_opp.
Qed.

Lemma convexf_ptP : (forall x, a <= x <= b -> 0 <= L x - f x)%R ->
  forall t : prob, convex_function_at f a b t.
Proof.
move=> H t; rewrite /convex_function_at.
set x := (t * a + t.~ * b)%R.
have : (a <= x <= b)%R.
  rewrite /x; split.
  - apply (@leR_trans (t * a + t.~ * a)).
      rewrite -mulRDl addRCA addR_opp subRR addR0 mul1R; exact/leRR.
    case/boolP : (t == `Pr 1) => [/eqP ->|t1].
      rewrite /onem subRR !mul0R !addR0; exact/leRR.
    rewrite leR_add2l; apply leR_wpmul2l; last exact/ltRW.
    exact/onem_ge0/prob_le1.
  - apply (@leR_trans (t * b + t.~ * b)); last first.
      rewrite -mulRDl addRCA addR_opp subRR addR0 mul1R; exact/leRR.
    rewrite leR_add2r; apply leR_wpmul2l; [exact/prob_ge0 | exact/ltRW].
move/H; rewrite subR_ge0 => /leR_trans; apply.
rewrite LE //.
have -> : ((b - x) / (b - a) = t)%R.
  rewrite /x -addR_opp oppRD addRCA mulRBl mul1R oppRB (addRCA b).
  rewrite addR_opp subRR addR0 -mulRN addRC -mulRDr addR_opp.
  rewrite /Rdiv -mulRA mulRV ?mulR1 // subR_eq0; exact/eqP/gtR_eqF.
have -> : ((x - a) / (b - a) = t.~)%R.
  rewrite /x -addR_opp addRAC -{1}(oppRK a) mulRN -mulNR -{2}(mul1R (- a)%R).
  rewrite -mulRDl (addRC _ R1) addR_opp -mulRDr addRC addR_opp.
  rewrite /Rdiv -mulRA mulRV ?mulR1 // subR_eq0; exact/eqP/gtR_eqF.
exact/leRR.
Qed.

Lemma second_derivative_convexf_pt : forall t : prob, convex_function_at f a b t.
Proof.
have note1 : forall x, R1 = ((x - a) / (b - a) + (b - x) / (b - a))%R.
  move=> x; rewrite -mulRDl addRC addRA subRK addR_opp mulRV // subR_eq0.
  exact/eqP/gtR_eqF.
have step1 : forall x, f x = ((x - a) / (b - a) * f x + (b - x) / (b - a) * f x)%R.
  by move=> x; rewrite -mulRDl -note1 mul1R.
apply convexf_ptP => // x axb.
rewrite /L.
case: axb.
  rewrite leR_eqVlt => -[-> _|].
  rewrite /L subRR div0R mul0R addR0 subRR; exact/leRR.
move=> ax.
rewrite leR_eqVlt => -[->|].
rewrite /L /Rdiv mulRV ?mul1R; last by rewrite subR_eq0; exact/eqP/gtR_eqF.
rewrite addRC subRK subRR; exact/leRR.
move=> xb.
have {step1}step2 : (L x - f x =
  (x - a) * (b - x) / (b - a) * ((f b - f x) / (b - x)) -
  (b - x) * (x - a) / (b - a) * ((f x - f a) / (x - a)))%R.
  rewrite {1}step1 {step1}.
  rewrite -addR_opp oppRD addRA addRC addRA.
  rewrite LE //.
  rewrite {1}/Rdiv -(mulRN _ (f x)) -/(Rdiv _ _).
  rewrite addRA -mulRDr (addRC _ (f a)) (addR_opp (f a)).
  rewrite -mulRN -addRA -mulRDr (addR_opp (f b)).
  rewrite addRC.
  rewrite -(oppRK (f a - f x)) mulRN addR_opp oppRB.
  congr (_ + _)%R.
  - rewrite {1}/Rdiv -!mulRA; congr (_ * _)%R; rewrite mulRCA; congr (_ * _)%R.
    rewrite mulRCA mulRV ?mulR1 // subR_eq0; exact/eqP/gtR_eqF.
  - rewrite -!mulNR -!mulRA; congr (_ * _)%R; rewrite mulRCA; congr (_ * _)%R.
    rewrite mulRCA mulRV ?mulR1 // subR_eq0; exact/eqP/gtR_eqF.
have [c2 [Ic2 Hc2]] : exists c2, (x < c2 < b /\ (f b - f x) / (b - x) = Df c2)%R.
  have H : pderivable f (fun x0 => x <= x0 <= b)%R.
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
have [c1 [Ic1 Hc1]] : exists c1, (a < c1 < x /\ (f x - f a) / (x - a) = Df c1)%R.
  have H : pderivable f (fun x0 => a <= x0 <= x)%R.
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
have c1c2 : (c1 < c2)%R by apply (@ltR_trans x); [case: Ic1 | case: Ic2].
have {step2 Hc1 Hc2}step3 : (L x - f x =
  (b - x) * (x - a) * (c2 - c1) / (b - a) * ((Df c2 - Df c1) / (c2 - c1)))%R.
  rewrite {}step2 Hc2 Hc1 (mulRC (x - a)%R) -mulRBr {1}/Rdiv -!mulRA.
  congr (_ * (_ * _))%R; rewrite mulRCA; congr (_ * _)%R.
  rewrite mulRCA mulRV ?mulR1 // subR_eq0; by move/gtR_eqF/eqP : c1c2.
have [d [Id H]] : exists d, (c1 < d < c2 /\ (Df c2 - Df c1) / (c2 - c1) = DDf d)%R.
  have H : pderivable Df (fun x0 => c1 <= x0 <= c2)%R.
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
