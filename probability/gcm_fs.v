Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice.
Require Import Reals_ext proba dist convex_choice.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import finmap set.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope convex_scope.

Section misc.
Definition set_of_fset (A : choiceType) (X : {fset A}) : set A :=
  [set a : A | a \in X].
End misc.

Module FSCSet.
Section def.
Variable A : convType.
Record mixin_of (car : {convex_set A}) := Mixin {


Module NECSet.
Section def.
Variable A : convType.
Record t : Type := mk {
  car : {convex_set A} ;
  H : `[< exists supp : {fset A}, supp != fset0 /\ car = CSet.mk (convex_hull [set a : A | a \in supp]) >]
}.
End def.
End NECSet.
Notation necset := NECSet.t.
Coercion NECSet.car : necset >-> convex_set_of.

Section necset_canonical.
Variable (A : convType).

Canonical necset_subType := [subType for @NECSet.car A].
Canonical necset_predType :=
  Eval hnf in mkPredType (fun t : necset A => (fun x => x \in NECSet.car t)).
Definition necset_eqMixin := Eval hnf in [eqMixin of (@necset A) by <:].
Canonical necset_eqType := Eval hnf in EqType (necset A) necset_eqMixin.
Definition necset_choiceMixin : Choice.mixin_of (necset A) := @gen_choiceMixin (necset A).
Canonical necset_choiceType : choiceType :=
  Eval hnf in Choice.Pack (Choice.Class necset_eqMixin necset_choiceMixin).
End necset_canonical.

Section necset_lemmas.
Variable A : convType.
Lemma necset_property (X : necset A) :
exists sX : {fset A}, sX != fset0 /\ NECSet.car X = CSet.mk (convex_hull [set a : A | a \in sX]).
Proof. by case: X => [car] /= /asboolP. Qed.
Lemma necset_neq0 (X : necset A) : X != cset0 _ :> {convex_set A}.
Proof.
apply/cset0PN/set0P.
case: (necset_property X) => sX [H ->] /=.
rewrite hull_eq0.
move/fset0Pn: H => [x Hx].
apply/eqP => H.
suff : ~ ((@set0 A) =i (@set0 A)) by apply.
rewrite -{1}H => /(_ x); rewrite !inE Hx.
move/(@asbool_eq_equiv true (set0 x)).
rewrite /set0 trueE; tauto.
Qed.
Definition necset_support (X : necset A) : {fset A} :=
(* axiom of choice *)
  let (sX, _) := constructive_indefinite_description (necset_property X) in sX.
Lemma cset_ext (X Y : {convex_set A}) : X = Y <-> CSet.car X = CSet.car Y.
Proof.
case: X => carX HX; case: Y => carY HY.
split => [-> // | /= H].
destruct H.
congr CSet.mk.
exact/Prop_irrelevance.
Qed.
Lemma necset_ext (X Y : necset A) : X = Y <-> NECSet.car X = NECSet.car Y.
Proof.
case: X => carX HX; case: Y => carY HY.
split => [-> // | /= H].
destruct H.
congr NECSet.mk.
exact/Prop_irrelevance.
Qed.
Lemma necset_support_hull_adj (X : necset A) (sY : {fset A}) :
  necset_support X = sY <-> X = CSet.mk (convex_hull [set a : A | a \in sY]) :> {convex_set A}.
Proof.
split.
- case: X => carX /=.
  case: carX => carX H H0.
  rewrite cset_ext /=.
  move <-.
  apply eqEsubset => a /=.

Lemma necset_support_neq0 (X : necset A) : necset_support X != fset0.
case: X => carX /= H.
rewrite /necset_support.


End necset_lemmas.

Section necset_convType.
Variable A : convType.
Let necset := necset A.
Local Open Scope bool_scope.
Local Open Scope fset_scope.
Definition support_conv (X Y : necset) (p : prob) : {fset A} :=
  (fun xy => xy.1 <| p |> xy.2) @` (necset_support X `*` necset_support Y).
Definition pre_conv (X Y : necset) (p : prob) : {convex_set A} :=
  CSet.mk (convex_hull [set a : A | a \in support_conv X Y p]).
Lemma support_conv_neq0 X Y p : support_conv X Y p != fset0.
Admitted.
Lemma pre_conv_neq0 X Y p : pre_conv X Y p != cset0 _.
Proof.
(*rewrite /pre_conv.
case: X => carX /= HX.
case: Y => carY /= HY.

case: X => carX /= /fset0Pn [x xX].
case: Y => carY /= /fset0Pn [y yY].
apply/fset0Pn.
exists ((x,y).1 <| p |> (x,y).2).
by rewrite in_imfset // inE xX yY.
Qed.
*)
Admitted.
Lemma pre_conv_support X Y p : 
  `[exists G : {fset A}, pre_conv X Y p == CSet.mk (convex_hull [set a : A | a \in G])].
Proof. rewrite /= existsbE asboolE. by exists (support_conv X Y p). Qed.
Lemma pre_conv_axiom X Y p :
  (pre_conv X Y p != cset0 _)  &&  `[exists G : {fset A}, pre_conv X Y p == CSet.mk (convex_hull [set a : A | a \in G])].
Proof. by apply/andP; split; [apply pre_conv_neq0 | apply pre_conv_support]. Qed.
Definition conv (X Y : necset) p : necset := NECSet.mk (pre_conv_axiom X Y p).
Lemma conv1 X Y : conv X Y `Pr 1 = X.
Proof.
case: X => carX HX; case: Y => carY HY.
rewrite necset_ext /=.  rewrite /pre_conv /=.
move: HX. => /andP. []. /cset0PN.  [x xX].
move: HY => /fset0Pn [y yY].
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP => a.
- move/imfsetP => -[xy /=]; by rewrite conv1 in_fsetM => /andP [Hx _] ->.
- move => aX; apply/imfsetP; exists (a,y); last by rewrite conv1.
  by rewrite inE aX yY .
Qed.
Lemma convmm X p : conv X X p = X.
Proof.
case: X => carX HX.
rewrite necset_ext /= /pre_conv /=.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP => x.
- move/imfsetP => -[xy /=].


>>>  BOOM! <<<


rewrite convmm in_fsetM.

Lemma convC a b p : conv a b p = conv b a `Pr p.~.
Lemma convA p q a b c :
  conv a (conv b c q) p = conv (conv a b [r_of p, q]) c [s_of p, q].

Definition necset_convMixin : ConvexSpace.class_of [choiceType of necset].
Proof.
apply (@ConvexSpace.Class _ conv).




Definition P : convType -> Type := 
End necset_convType.



(* non-empty convex sets of distributions *)
Notation "{ 'csdist+' T }" := (necset (Dist_convType T)) (format "{ 'csdist+'  T }") : convex_scope.

Section P_delta.
(* P = necset \o Dist, where
   - Dist is the free convex space functor, and
   - necset is the finitely-supported convex power functor. *)
Definition P : choiceType -> choiceType := fun x => [choiceType of necset (Dist_convType x)].

(* we now prove that P forms a convex space *)
Section P_convex_space.
Variable A : choiceType.
Axiom Conv2Pd : forall A : choiceType, P A -> P A -> Reals_ext.Prob.t -> P A.
Axiom Conv2Pconv1 : forall (A : choiceType) a b, @Conv2Pd A a b (`Pr 1) = a.
Axiom Conv2Pconvmm : forall (A : choiceType) a p, @Conv2Pd A a a p = a.
Axiom Conv2PconvC : forall (A : choiceType) a b p, @Conv2Pd A a b p = @Conv2Pd A b a (`Pr p.~).
Axiom Conv2PconvA' : forall (A : choiceType) p q a b c,
  @Conv2Pd A a (@Conv2Pd A b c q) p = @Conv2Pd A (@Conv2Pd A a b ([r_of p, q])) c ([s_of p, q]).
Definition P_convMixin :=
  @ConvexSpace.Class (P A) (@Conv2Pd A)
  (@Conv2Pconv1 A)
  (@Conv2Pconvmm A)
  (@Conv2PconvC A)
  (@Conv2PconvA' A).
Canonical P_convType := ConvexSpace.Pack P_convMixin.
End P_convex_space.

Canonical conv_lattType C := @SemiLattice.Pack (P_convType C) (P_semiLattClass _).

Definition PD := P \o Dist.

Section monad_mu.

Axiom eps0: forall {C : convType}, Dist C -> C (* p.164 *).
(* will be Convn? TODO  *)
Axiom eps1 : forall {L : semiLattType}, P L -> L (* just flattening of lattice joins? preserves oplus and convex hull*).
(* for an affine function f, returns a function F#f that to each convex set of dist returns its image by f, f needs to be affine *)
Axiom F : forall {X Y : convType}, (X -> Y) -> P X -> P Y.
Axiom F_preserves_affine : forall (X Y : convType) (f : X -> Y),
    affine_function f -> affine_function (F f).

Definition mu {T : choiceType} : PD (PD T) -> PD T := eps1 \o F eps0.

End monad_mu.

End P_delta.
