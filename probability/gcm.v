Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice.
Require Import Reals_ext proba dist convex_choice.
From mathcomp Require Import boolp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope convex_scope.

Module NECSet.
Section def.
Local Open Scope classical_set_scope.
Local Open Scope proba_scope.
Variable A : convType.
Record t : Type := mk {
  car : {convex_set A} ;
  H : car != cset0 _ }.
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
Canonical cont_choiceType : choiceType :=
  Eval hnf in Choice.Pack (Choice.Class necset_eqMixin necset_choiceMixin).

End necset_canonical.

(* non-empty convex sets of distributions *)
Notation "{ 'csdist+' T }" := (necset (Dist_convType T)) (format "{ 'csdist+'  T }") : convex_scope.

Module SemiLattice.
Section def.
(* a semilattice is a commutative semigroup with idempotence *)
Record class_of T := Class {
  op : T -> T -> T;
  _ : commutative op;
  _ : associative op;
  _ : idempotent op;
}.
Structure type :=
  Pack {sort : choiceType; _ : class_of sort}.
End def.
Module Exports.
Definition SemiLattOp (T : type) : sort T -> sort T -> sort T :=
  let: Pack _ (Class op _ _ _) := T in op.
(* Notation "x [+] y" := (SemiLattOp x y) (format "x  [+]  y", at level 50). *)
Notation semiLattType := type.
Coercion sort : semiLattType >-> choiceType.
End Exports.
End SemiLattice.
Export SemiLattice.Exports.

(* Our lattice operation SemiLattOp could either be join or meet,
   but we choose "join" for the names of lemmas because:
   1. we want to follow the naming scheme in finmap.order, and
   2. our intended use of the semilattice structure is for taking
      convex hulls, which looks more like a join than meet.
 *)
Section join_semilattice_lemmas.
(* naming scheme and proofs copied from finmap.order. *)
Variable (L : semiLattType).
Implicit Types (x y : L).

Notation join := SemiLattOp.
Notation "x `|` y" := (SemiLattOp x y) (format "x  `|`  y", at level 50).

Lemma joinC : commutative (@join L). Proof. by case: L => [?[]]. Qed.
Lemma joinA : associative (@join L). Proof. by case: L => [?[]]. Qed.
Lemma joinxx : idempotent (@join L). Proof. by case: L => [?[]]. Qed.

Lemma joinAC : right_commutative (@join L).
Proof. by move=> x y z; rewrite -!joinA [X in _ `|` X]joinC. Qed.
Lemma joinCA : left_commutative (@join L).
Proof. by move=> x y z; rewrite !joinA [X in X `|` _]joinC. Qed.
Lemma joinACA : interchange (@join L) (@join L).
Proof. by move=> x y z t; rewrite !joinA [X in X `|` _]joinAC. Qed.

Lemma joinKU y x : x `|` (x `|` y) = x `|` y.
Proof. by rewrite joinA joinxx. Qed.
Lemma joinUK y x : (x `|` y) `|` y = x `|` y.
Proof. by rewrite -joinA joinxx. Qed.
Lemma joinKUC y x : x `|` (y `|` x) = x `|` y.
Proof. by rewrite joinC joinUK joinC. Qed.
Lemma joinUKC y x : y `|` x `|` y = x `|` y.
Proof. by rewrite joinAC joinC joinxx. Qed.
End join_semilattice_lemmas.

Section P_delta.
(* we have defined convex spaces in convex_new_dist.v *)

(* we use the functor Dist *)
Definition P : choiceType -> choiceType := fun x => [choiceType of necset (Dist_convType x)].

Axiom eps0: forall {C : convType}, Dist C -> C (* p.164 *).
(* will be Convn? TODO  *)
Axiom eps1 : forall {L : semiLattType}, P L -> L (* just flattening of lattice joins? preserves oplus and convex hull*).
(* for an affine function f, returns a function F#f that to each convex set of dist returns its image by f, f needs to be affine *)
Axiom F : forall {X Y : convType}, (X -> Y) -> P X -> P Y.
Fail Axiom F_preserves_affine : forall (X Y : convType) (f : X -> Y),
    affine_function f -> affine_function (F f).

(* the outputs of P carries a semilattice structure
   (NB: this needs to be reviewed) *)
Axiom P_semiLattClass : forall X, SemiLattice.class_of (P X).
Canonical P_semiLattType X := SemiLattice.Pack (P_semiLattClass X).

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

Definition join {T : choiceType} : PD (PD T) -> PD T := eps1 \o F eps0.

End P_delta.
