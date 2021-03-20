Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice.
Require Import Reals_ext proba dist convex_choice.
From mathcomp Require Import boolp.
From mathcomp Require Import finmap set.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope convex_scope.

Module NEFSet.
Section def.
Variable A : choiceType.
Record t : Type := mk {
  car : {fset A} ;
  H : car != fset0 }.
End def.
End NEFSet.
Notation nefset := NEFSet.t.
Coercion NEFSet.car : nefset >-> finset_of.

Section nefset_canonical.
Variable A : choiceType.

Canonical nefset_subType := [subType for @NEFSet.car A].
Canonical nefset_predType :=
  Eval hnf in mkPredType (fun t : nefset A => (fun x => x \in NEFSet.car t)).
Definition nefset_eqMixin := Eval hnf in [eqMixin of (@nefset A) by <:].
Canonical nefset_eqType := Eval hnf in EqType (nefset A) nefset_eqMixin.
Definition nefset_choiceMixin : Choice.mixin_of (nefset A) := @gen_choiceMixin (nefset A).
Canonical nefset_choiceType : choiceType :=
  Eval hnf in Choice.Pack (Choice.Class nefset_eqMixin nefset_choiceMixin).
End nefset_canonical.

Section nefset_convType.
Variable A : convType.
Let nefset := nefset A.
Local Open Scope bool_scope.
Local Open Scope fset_scope.
Definition pre_conv (X Y : nefset) p : {fset A} :=
  (fun xy => xy.1 <| p |> xy.2) @` (X `*` Y).
Lemma pre_conv_nonempty (X Y : nefset) p : pre_conv X Y p != fset0.
Proof.
rewrite /pre_conv.
case: X => carX /= /fset0Pn [x xX].
case: Y => carY /= /fset0Pn [y yY].
apply/fset0Pn.
exists ((x,y).1 <| p |> (x,y).2).
by rewrite in_imfset // inE xX yY.
Qed.
Definition conv (X Y : nefset) p : nefset := NEFSet.mk (pre_conv_nonempty X Y p).
Lemma nefset_ext (X Y : nefset) : X = Y <-> NEFSet.car X = NEFSet.car Y.
Proof.
case: X => carX HX; case: Y => carY HY.
split => [-> // | /= H].
destruct H.
congr NEFSet.mk.
exact/Prop_irrelevance.
Qed.
Lemma conv1 X Y : conv X Y `Pr 1 = X.
Proof.
case: X => carX HX; case: Y => carY HY.
rewrite nefset_ext /= /pre_conv /=.
move: HX => /fset0Pn [x xX].
move: HY => /fset0Pn [y yY].
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP => a.
- move/imfsetP => -[xy /=]; by rewrite conv1 in_fsetM => /andP [Hx _] ->.
- move => aX; apply/imfsetP; exists (a,y); last by rewrite conv1.
  by rewrite inE aX yY .
Qed.
Lemma convmm X p : conv X X p = X.
Proof.
case: X => carX HX.
rewrite nefset_ext /= /pre_conv /=.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP => x.
- move/imfsetP => -[xy /=].


>>>  BOOM! <<<


rewrite convmm in_fsetM.

Lemma convC a b p : conv a b p = conv b a `Pr p.~.
Lemma convA p q a b c :
  conv a (conv b c q) p = conv (conv a b [r_of p, q]) c [s_of p, q].

Definition nefset_convMixin : ConvexSpace.class_of [choiceType of nefset].
Proof.
apply (@ConvexSpace.Class _ conv).




Definition P : convType -> Type := 
End nefset_convType.


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
