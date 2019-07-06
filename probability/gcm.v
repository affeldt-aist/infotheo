Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype finfun bigop.
Require Import Reals_ext Rbigop proba dist convex_choice.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import finmap set.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope convex_scope.

Reserved Notation "\joet_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \joet_ i '/  '  F ']'").
Reserved Notation "\joet_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \joet_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\joet_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \joet_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\joet_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \joet_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\joet_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \joet_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\joet_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \joet_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\joet_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\joet_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\joet_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \joet_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\joet_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \joet_ ( i  <  n )  F ']'").
Reserved Notation "\joet_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \joet_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\joet_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \joet_ ( i  'in'  A ) '/  '  F ']'").

Section misc.
Section dist_of_Dist.
Variable (A : choiceType) (P : Dist A).
Local Open Scope fset_scope.
Local Open Scope R_scope.
Local Open Scope reals_ext_scope.
Let D := [finType of finsupp P] : finType.
Let f := [ffun d : D => P (fsval d)].
Let f0 b : 0 <= f b. Proof. rewrite ffunE; by apply Dist.ge0. Qed.
Let f1 : \sum_(b in D) f b = 1.
Proof.
rewrite -(Dist.f1 P) big_seq_fsetE /=.
apply eq_bigr => a; by rewrite ffunE.
Qed.
Definition dist_of_Dist : dist D := proba.makeDist f0 f1.
End dist_of_Dist.

Lemma Dist_domain_not_empty (A : choiceType) (P : Dist A)
  : (0 < #|` finsupp P |)%nat.
Proof.
rewrite cardfE.
apply dist_domain_not_empty.
by apply dist_of_Dist.
Qed.

Section Convn_indexed_over_finType.
Local Open Scope R_scope.
Variables (A : convType) (T : finType) (d : {dist T}) (f : T -> A).
Let n := #| T |.
Let t0 : T.
Proof.
move/card_gt0P/xchoose: (dist_domain_not_empty d) => t0; exact t0.
Defined.
Let g : 'I_n -> T := fun i => nth t0 (index_enum T) i.
Let h := [ffun i => d (g i)].
Let h0 : forall b, 0 <= h b.
Proof.
move=> b.
rewrite ffunE.
by apply dist_ge0.
Qed.
Let h1 : \sum_(b in 'I_n) h b = 1.
Proof.
rewrite -(@epmf1 T d).
rewrite /h.
transitivity (\sum_(b in 'I_n) d (g b));
  first by apply eq_bigr => i; rewrite ffunE.
rewrite -big_image /=.
suff -> : (image_mem g (mem (ordinal n))) = index_enum T
  by done.
apply (eq_from_nth (x0 := t0)) => [ | i ];
  first by rewrite size_image /index_enum -enumT -cardT card_ord.
rewrite size_image => i_n.
rewrite (nth_image t0 g (Ordinal i_n)) /g /=.
congr nth.
by rewrite enum_val_ord /=.
Qed.
Let d' := proba.makeDist h0 h1.
Definition Convn_indexed_over_finType : A := Convn d' (f \o g).
End Convn_indexed_over_finType.
End misc.

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

Module UnitalSemiLattice.
Section def.
(* a semilattice is a commutative semigroup with idempotence *)
Record class_of (T : Type) : Type := Class {
  op : T -> T -> T;
  idx : T;
  _ : commutative op;
  _ : associative op;
  _ : idempotent op;
  _ : left_id idx op;
}.
Structure type :=
  Pack {sort : Type; _ : class_of sort}.
End def.
Module Exports.
Definition SemiLattUnit (T : type) : sort T :=
  let: Pack _ (Class _ idx _ _ _ _) := T in idx.
Definition SemiLattOp (T : type) : sort T -> sort T -> sort T :=
  let: Pack _ (Class op _ _ _ _ _) := T in op.
Notation "x [+] y" := (SemiLattOp x y) (format "x  [+]  y", at level 50).
Notation "`i" := SemiLattUnit : latt_scope.
Notation unitalSemiLattType := type.
Coercion sort : unitalSemiLattType >-> Sortclass.
End Exports.
End UnitalSemiLattice.
Export UnitalSemiLattice.Exports.

Section unital_semilattice_lemmas.
(* naming scheme and proofs copied from finmap.order. *)
Variable (L : unitalSemiLattType).
Implicit Types (x y : L).

Local Open Scope latt_scope.
Local Close Scope fset_scope.
Local Close Scope classical_set_scope.

Notation joet := SemiLattOp.

Notation "\joet_ ( i <- r | P ) F" :=
  (\big[@joet _ _/`i]_(i <- r | P%B) F) : latt_scope.
Notation "\joet_ ( i <- r ) F" :=
  (\big[@joet _ _/`i]_(i <- r) F) : latt_scope.
Notation "\joet_ ( i | P ) F" :=
  (\big[@joet _ _/`i]_(i | P%B) F) : latt_scope.
Notation "\joet_ i F" :=
  (\big[@joet _ _/`i]_i F) : latt_scope.
Notation "\joet_ ( i : I | P ) F" :=
  (\big[@joet _ _/`i]_(i : I | P%B) F) (only parsing) : latt_scope.
Notation "\joet_ ( i : I ) F" :=
  (\big[@joet _ _/`i]_(i : I) F) (only parsing) : latt_scope.
Notation "\joet_ ( m <= i < n | P ) F" :=
 (\big[@joet _ _/`i]_(m <= i < n | P%B) F) : latt_scope.
Notation "\joet_ ( m <= i < n ) F" :=
 (\big[@joet _ _/`i]_(m <= i < n) F) : latt_scope.
Notation "\joet_ ( i < n | P ) F" :=
 (\big[@joet _ _/`i]_(i < n | P%B) F) : latt_scope.
Notation "\joet_ ( i < n ) F" :=
 (\big[@joet _ _/`i]_(i < n) F) : latt_scope.
Notation "\joet_ ( i 'in' A | P ) F" :=
 (\big[@joet _ _/`i]_(i in A | P%B) F) : latt_scope.
Notation "\joet_ ( i 'in' A ) F" :=
 (\big[@joet _ _/`i]_(i in A) F) : latt_scope.

Lemma joetC : commutative (@joet L). Proof. by case: L => [?[]]. Qed.
Lemma joetA : associative (@joet L). Proof. by case: L => [?[]]. Qed.
Lemma joetxx : idempotent (@joet L). Proof. by case: L => [?[]]. Qed.

(* TODO: add right-unit *)

Lemma joetAC : right_commutative (@joet L).
Proof. by move=> x y z; rewrite -!joetA [X in _ [+] X]joetC. Qed.
Lemma joetCA : left_commutative (@joet L).
Proof. by move=> x y z; rewrite !joetA [X in X [+] _]joetC. Qed.
Lemma joetACA : interchange (@joet L) (@joet L).
Proof. by move=> x y z t; rewrite !joetA [X in X [+] _]joetAC. Qed.

Lemma joetKU y x : x [+] (x [+] y) = x [+] y.
Proof. by rewrite joetA joetxx. Qed.
Lemma joetUK y x : (x [+] y) [+] y = x [+] y.
Proof. by rewrite -joetA joetxx. Qed.
Lemma joetKUC y x : x [+] (y [+] x) = x [+] y.
Proof. by rewrite joetC joetUK joetC. Qed.
Lemma joetUKC y x : y [+] x [+] y = x [+] y.
Proof. by rewrite joetAC joetC joetxx. Qed.
End unital_semilattice_lemmas.

Module USLattConvType.
Section def.
Variable A : convType.
End def.
End USLattConvType.

Section P_delta.
(* P_delta = necset \o Dist, where
   - Dist is the free convex space functor, and
   - necset is the convex powerset functor. *)
Definition P_delta : choiceType -> choiceType := fun x => [choiceType of necset (Dist_convType x)].

(*
  eps0 is the counit of the adjunction (Dist -| coercion) and it is just Convn
  (* p.164 *).
*)
Definition eps0 : forall {C : convType}, Dist C -> C
  := fun C d => Convn_indexed_over_finType
                  (dist_of_Dist d)
                  (fun x : finsupp d => (fsval x)).

Axiom eps1 : forall {L : semiLattType}, P L -> L (* just flattening of lattice joins? preserves oplus and convex hull*).
(* for an affine function f, returns a function F#f that to each convex set of dist returns its image by f, f needs to be affine *)

(* for gcm.v *)
Definition eps1' : forall {L : lattConvType}, necset L -> L.
move => L X.
set CX := (FSCSet.car (NECSet.car X)).
Local Open Scope classical_set_scope.
Check \bigcup_(x in CX) x.


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
