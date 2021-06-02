Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype bigop.
Require Import Reals_ext proba dist convex_choice.
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
Definition set_of_fset (A : choiceType) (X : {fset A}) : set A :=
  [set a : A | a \in X].
Lemma cset_ext (A : convType) (X Y : {convex_set A}) :
  X = Y <-> (X = Y :> set A).
Proof.
case: X => carX HX; case: Y => carY HY.
split => [-> // | /= H].
destruct H.
congr CSet.mk.
exact/Prop_irrelevance.
Qed.
Lemma hull_monotone (A : convType) (X Y : set A) :
  (X `<=` Y)%classic -> (hull X `<=` hull Y)%classic.
Proof.
move=> H a.
case => n [g [d [H0 H1]]].
exists n, g, d.
split => //.
by eapply subset_trans; first by exact: H0.
Qed.
Lemma hull_eqEsubset (A : convType) (X Y : set A) :
  (X `<=` hull Y)%classic -> (Y `<=` hull X)%classic -> hull X = hull Y.
Proof.
move/hull_monotone; rewrite hullI => H.
move/hull_monotone; rewrite hullI => H0.
by apply/eqEsubset.
Qed.
End misc.

Module PreFSCSet.
Section def.
Variable A : convType.
Record class_of (car : {convex_set A}) : Type := Class {
  supp : {fset A} ;
  _ : car = CSet.mk (convex_hull [set a : A | a \in supp]) ;
}.
Structure t : Type := Pack { car : {convex_set A} ; _ : class_of car }.
End def.
Module Exports.
Notation prefscset := t.
Coercion car : prefscset >-> convex_set_of.
End Exports.
End PreFSCSet.
Export PreFSCSet.Exports.

Section prefscset_lemmas.
Variable A : convType.
Definition prefscset_supp (X : prefscset A) : {fset A} :=
  let: PreFSCSet.Pack _ (PreFSCSet.Class supp _) := X in supp.
Lemma prefscset_hull_supp (X : prefscset A) :
  X = CSet.mk (convex_hull [set a : A | a \in prefscset_supp X]) :> {convex_set A}.
Proof.
case: X => carX [supp H].
apply cset_ext => /=.
by rewrite H.
Qed.

Section canonical.
(*
Definition supp_prefscset (sX : {fset A}) : prefscset A :=
  @PreFSCSet.Pack
    _
    (CSet.mk (convex_hull [set a : A | a \in sX]))
    (PreFSCSet.Class erefl).
Lemma prefscset_suppK : cancel prefscset_supp supp_prefscset.
Proof.
rewrite /supp_prefscset.
case => car [supp H] /=.
Fail congr PreFSCSet.Pack.
Abort.
*)
Definition prefscset_eqMixin : Equality.mixin_of (prefscset A) := @gen_eqMixin (prefscset A).
Canonical prefscset_eqType := Eval hnf in EqType (prefscset A) prefscset_eqMixin.
Definition prefscset_choiceMixin : Choice.mixin_of (prefscset A) := @gen_choiceMixin (prefscset A).
Canonical prefscset_choiceType : choiceType :=
  Eval hnf in Choice.Pack (Choice.Class prefscset_eqMixin prefscset_choiceMixin).
End canonical.
End prefscset_lemmas.

Module FSCSet.
Section def.
Variable A : convType.
Record t : Type := mk {
  car : {convex_set A} ;
  _ : exists supp : {fset A}, car = CSet.mk (convex_hull [set a : A | a \in supp]) ;
}.
End def.
Module Exports.
Notation fscset := FSCSet.t.
Coercion FSCSet.car : fscset >-> convex_set_of.
End Exports.
End FSCSet.
Export FSCSet.Exports.

Section fscset_lemmas.
Variable (A : convType).

Section canonical.
Definition fscset_eqMixin : Equality.mixin_of (fscset A) := @gen_eqMixin (fscset A).
Canonical fscset_eqType := Eval hnf in EqType (fscset A) fscset_eqMixin.
Definition fscset_choiceMixin : Choice.mixin_of (fscset A) := @gen_choiceMixin (fscset A).
Canonical fscset_choiceType : choiceType :=
  Eval hnf in Choice.Pack (Choice.Class fscset_eqMixin fscset_choiceMixin).
End canonical.

Lemma fscset_ext (X Y : fscset A) : X = Y <-> (X = Y :> {convex_set A}).
Proof.
case: X => carX HX; case: Y => carY HY.
split => [-> // | /= H].
destruct H.
congr FSCSet.mk.
exact/Prop_irrelevance.
Qed.
Lemma fscset_property (X : fscset A) :
exists sX : {fset A}, X = CSet.mk (convex_hull [set a : A | a \in sX]) :> {convex_set A}.
Proof. by case: X.  Qed.
Definition fscset_supp (X : fscset A) : {fset A} :=
(* axiom of choice *)
  let (sX, _) := constructive_indefinite_description (fscset_property X) in sX.
Lemma fscset_hull_supp (X : fscset A) :
  X = CSet.mk (convex_hull [set a : A | a \in fscset_supp X]) :> {convex_set A}.
Proof. rewrite /fscset_supp. by case: (cid (fscset_property X)). Qed.

Lemma fscset_supp0E' (X : fscset A) :
  (fscset_supp X = fset0) <-> (X = cset0 _ :> {convex_set A}).
Proof.
split.
- move/(congr1 (fun Y => CSet.mk (convex_hull [set a : A | a \in Y]))).
  rewrite -fscset_hull_supp => ->.
  rewrite cset_ext /=.
  apply/eqP; rewrite hull_eq0; apply/eqP.
  apply funext => a.
  by rewrite inE falseE.
- move => H; apply/eqP; move/eqP : H.
  apply contraLR.
  case/fset0Pn => a Ha.
  apply/eqP; rewrite fscset_hull_supp cset_ext /=; apply/eqP.
  rewrite hull_eq0.
  apply/set0P.
  by exists a.
Qed.
Lemma fscset_supp0E (X : fscset A) :
  (fscset_supp X == fset0) = (X == cset0 _ :> {convex_set A}).
Proof. apply/eqP/eqP; by rewrite fscset_supp0E'. Qed.
End fscset_lemmas.

Module NECSet.
Section def.
Local Open Scope classical_set_scope.
Local Open Scope proba_scope.
Variable A : convType.
Record t : Type := mk {
  car : fscset A ;
  _ : car != cset0 _ :> {convex_set A}}.
End def.
Module Exports.
Notation necset := NECSet.t.
Coercion NECSet.car : necset >-> fscset.
End Exports.
End NECSet.
Export NECSet.Exports.

Section necset_canonical.
Variable (A : convType).

Canonical necset_subType := [subType for @NECSet.car A].
Canonical necset_predType :=
  Eval hnf in mkPredType (fun t : necset A => (fun x => x \in FSCSet.car (NECSet.car t))).
Definition necset_eqMixin := Eval hnf in [eqMixin of (@necset A) by <:].
Canonical necset_eqType := Eval hnf in EqType (necset A) necset_eqMixin.
Definition necset_choiceMixin : Choice.mixin_of (necset A) := @gen_choiceMixin (necset A).
Canonical necset_choiceType : choiceType :=
  Eval hnf in Choice.Pack (Choice.Class necset_eqMixin necset_choiceMixin).
End necset_canonical.

(* non-empty finitely supported convex sets of distributions *)
Notation "{ 'csdist+' T }" := (necset (Dist_convType T)) (format "{ 'csdist+'  T }") : convex_scope.

Section necset_lemmas.
Variable A : convType.

Lemma necset_ext (X Y : necset A) : X = Y <-> (X = Y :> {convex_set A}).
Proof.
case: X => carX HX; case: Y => carY HY.
split => [-> // | /= H].
move/fscset_ext: H => H.
destruct H.
congr NECSet.mk.
exact/Prop_irrelevance.
Qed.
Definition necset_supp (X : necset A) : {fset A} := fscset_supp X.
Lemma necset_hull_supp (X : necset A) :
  X = CSet.mk (convex_hull [set a : A | a \in necset_supp X]) :> {convex_set A}.
Proof. by rewrite fscset_hull_supp. Qed.
Lemma necset_neq0 (X : necset A) : X != cset0 _ :> {convex_set A}.
Proof. by case: X. Qed.
Lemma necset_supp_neq0 (X : necset A) : necset_supp X != fset0.
Proof. by rewrite fscset_supp0E necset_neq0. Qed.
End necset_lemmas.

Module necset_convType.
Section def.
Variable A : convType.
Let necset := necset A.
Local Open Scope bool_scope.
Local Open Scope fset_scope.
Definition conv_supp (X Y : necset) (p : prob) : {fset A} :=
  (fun xy => xy.1 <| p |> xy.2) @` (necset_supp X `*` necset_supp Y).
Lemma conv_supp1 X Y : conv_supp X Y `Pr 1 = fscset_supp X.
Proof.
case: X => carX HX; case: Y => carY HY.
move/idP: (HY); rewrite -{1}fscset_supp0E; case/fset0Pn => y yY.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP => a.
- move/imfsetP => -[xy /=]; by rewrite conv1 in_fsetM => /andP [Hx _] ->.
- move => aX; apply/imfsetP; exists (a,y); last by rewrite conv1.
  by rewrite inE aX yY .
Qed.
(* NB: It's impossible to obtain conv_suppmm. Because of this, the type of
   (finite) powersets of a convType cannot be a convType again. We need to
   take hulls. *)
Lemma conv_suppC X Y p : conv_supp X Y p = conv_supp Y X `Pr p.~.
Proof.
apply/eqP.
rewrite /conv_supp eqEfsubset.
apply/andP; split; apply/fsubsetP => a /imfsetP [[x y]]; rewrite !inE /= => /andP [H0 H1] ->; [rewrite convC | rewrite -convC]; change y with (y, x).1; change x with (y, x).2; rewrite in_imfset //= inE /=; by apply/andP.
Qed.
Definition pre_conv (X Y : necset) (p : prob) : fscset A.
apply (@FSCSet.mk _ (CSet.mk (convex_hull [set a : A | a \in conv_supp X Y p]))).
exists (conv_supp X Y p).
exact: erefl.
Defined.
Lemma conv_supp_neq0 X Y p : conv_supp X Y p != fset0.
Proof.
apply/fset0Pn.
case/fset0Pn: (necset_supp_neq0 X) => x xX.
case/fset0Pn: (necset_supp_neq0 Y) => y yY.
exists ((x,y).1 <|p|> (x,y).2).
by rewrite in_imfset // inE xX yY.
Qed.
Lemma pre_conv_neq0 X Y p : pre_conv X Y p != cset0 _ :> {convex_set A}.
Proof.
apply/eqP; move/cset_ext => /=; apply/eqP.
rewrite hull_eq0.
case/fset0Pn : (conv_supp_neq0 X Y p) => a Ha.
rewrite set0P.
by exists a.
Qed.
Definition conv (X Y : necset) p : necset := NECSet.mk (pre_conv_neq0 X Y p).
Lemma conv1 X Y : conv X Y `Pr 1 = X.
Proof. by rewrite necset_ext /= [in RHS]fscset_hull_supp conv_supp1. Qed.
Lemma convmm X p : conv X X p = X.
Proof.
case: X => carX HX.
rewrite necset_ext /= [in RHS]fscset_hull_supp cset_ext /=.
apply hull_eqEsubset => a.
- rewrite /conv_supp /necset_supp.
  case/imfsetP => -[a0 a1] /=.
  rewrite inE /= => /andP [Ha0 Ha1] ->.
  set Z:= ([set a : A | a \in fscset_supp carX])%classic.
  have -> : Z = (Z `|` Z)%classic by rewrite setUid.
  by rewrite -in_setE mem_hull_setU // /Z inE asboolE.
- move=> H.
  rewrite -in_setE; apply hull_mem; rewrite inE asboolE /conv_supp.
  by apply/imfsetP; exists (a, a); rewrite /= ?convmm // inE /=; apply/andP; split.
Qed.
Lemma convC X Y p : conv X Y p = conv Y X `Pr p.~.
Proof. by rewrite /conv necset_ext /= cset_ext /= conv_suppC. Qed.
Lemma convA p q X Y Z :
  conv X (conv Y Z q) p = conv (conv X Y [r_of p, q]) Z [s_of p, q].
Proof.
rewrite /conv necset_ext /= /conv_supp cset_ext /=.
apply hull_eqEsubset => a /imfsetP [[a0 a1]] /=; rewrite inE /= => /andP [Ha0 Ha1] ->.
Admitted.

Definition convMixin : ConvexSpace.class_of [choiceType of necset]
  := @ConvexSpace.Class _ conv conv1 convmm convC convA.

End def.
End necset_convType.
Canonical necset_convType A := ConvexSpace.Pack (necset_convType.convMixin A).

Module SemiLattice.
Section def.
(* a semilattice is a commutative semigroup with idempotence *)
Record class_of (T : choiceType) : Type := Class {
  op : T -> T -> T;
  _ : commutative op;
  _ : associative op;
  _ : idempotent op;
}.
Structure type :=
  Pack {sort : choiceType; _ : class_of sort}.
End def.
Module Exports.
Definition SemiLattOp {T : type} : sort T -> sort T -> sort T :=
  let: Pack _ (Class op _ _ _) := T in op.
Notation "x [+] y" := (SemiLattOp x y) (format "x  [+]  y", at level 50) : latt_scope.
Notation semiLattType := type.
Coercion sort : semiLattType >-> choiceType.
End Exports.
End SemiLattice.
Export SemiLattice.Exports.

Section semilattice_lemmas.
(* naming scheme and proofs copied from finmap.order. *)
Variable (L : semiLattType).
Implicit Types (x y : L).

Local Open Scope latt_scope.
Local Close Scope fset_scope.
Local Close Scope classical_set_scope.

Local Notation joet := SemiLattOp.

Lemma joetC : commutative (@joet L). Proof. by case: L => [?[]]. Qed.
Lemma joetA : associative (@joet L). Proof. by case: L => [?[]]. Qed.
Lemma joetxx : idempotent (@joet L). Proof. by case: L => [?[]]. Qed.

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

End semilattice_lemmas.

(* mimicking MonadAltProb *)
Module SemiLattConvType.
Local Open Scope convex_scope.
Local Open Scope latt_scope.
Record mixin_of (L : semiLattType) (op : L -> L -> prob -> L) := Mixin {
  _ : forall p, right_distributive (fun x y => op x y p) (@SemiLattOp L) ;
}.
Record class_of (T : choiceType) : Type := Class {
  base : SemiLattice.class_of T ;
  base2 : ConvexSpace.class_of (SemiLattice.Pack base) ;
  mixin : @mixin_of (SemiLattice.Pack base) (@Conv (ConvexSpace.Pack base2)) ;
}.
Structure t : Type := Pack { sort : choiceType ; class : class_of sort }.
Definition baseType (T : t) : semiLattType := SemiLattice.Pack (base (class T)).
Definition base2Type (T : t) : convType := ConvexSpace.Pack (base2 (class T)).
Module Exports.
Notation semiLattConvType := t.
Coercion baseType : semiLattConvType >-> semiLattType.
Coercion base2Type : semiLattConvType >-> convType.
(*
Canonical baseType.
Canonical base2Type.
*)
End Exports.
End SemiLattConvType.
Export SemiLattConvType.Exports.

Module necset_semiLattType.
Section def.
Local Open Scope classical_set_scope.
Variable (A : convType).
Definition pre_op (X Y : necset A) : {convex_set A}
  := CSet.mk (convex_hull ((X : {convex_set A}) `|` (Y : {convex_set A}))).
Lemma pre_op_neq0 X Y : pre_op X Y != cset0 A.
Proof.
move: X Y => [X HX] [Y HY]; apply/eqP => /(congr1 val) /=; apply/eqP.
rewrite hull_eq0; apply: contra HX => /eqP; rewrite setU_eq0 => -[X0 _].
exact/eqP/val_inj.
Qed.
Definition op X Y := NECSet.mk (pre_op_neq0 X Y).
Lemma opC : commutative op.
Proof. by move=> X Y; do 2 apply val_inj => /=; rewrite setUC. Qed.
Lemma opA : associative op.
Proof. by move=> X Y Z; do 2 apply val_inj => /=; rewrite hullUA. Qed.
Lemma opxx : idempotent op.
Proof. by move=> X; do 2 apply val_inj => /=; rewrite setUid hull_cset. Qed.
Definition semiLattMixin := SemiLattice.Class opC opA opxx.
End def.
End necset_semiLattType.
Canonical necset_semiLattType A := SemiLattice.Pack (necset_semiLattType.semiLattMixin A).

Local Open Scope latt_scope.

Module necset_semiLattConvType.
Section def.
Local Open Scope classical_set_scope.
Variable (A : convType).
Lemma axiom : forall p : prob,
    right_distributive
      (fun x : necset_semiLattType A => (necset_convType.conv x)^~ p) SemiLattOp.
Proof.
move=> p X Y Z.
have H : NECSet.car ((necset_convType.conv X Y p) [+] (necset_convType.conv X Z p))
          =  [set u | exists x0, exists x1, exists y, exists z, exists q, x0 \in X /\ x1 \in X /\ y \in Y /\ z \in Z /\ u = (x0 <| p |> y) <| q |> (x1 <| p |> z)] :> set A.
- rewrite /= hull_necsetU.
  apply eqEsubset => a.
  + case => u [] v [] q [].
    rewrite !in_setE !necset_convType.convE.
    case => x0 [] y [] x0X [] yY -> [] [] x1 [] z [] x1X [] zZ -> ->.
      by exists x0, x1, y, z, q.
  + case=> x0 [] x1 [] y [] z [] q [] x0X [] x1X [] yY [] zZ ->.
      by exists (x0 <| p |> y), (x1 <| p |> z), q; rewrite !in_setE !necset_convType.convE; split; [exists x0, y | split => //; exists x1, z].
have H0 : NECSet.car (necset_convType.conv X (Y [+] Z) p)
       = [set u | exists x, exists y, exists z, exists q, x \in X /\ y \in Y /\ z \in Z /\ u = x <| p |> (y <| q |> z)] :> set A.
- rewrite necset_convType.convE.
  apply eqEsubset => a.
  + case => x [] u [] xX []; rewrite in_setE /= hull_necsetU => -[] y [] z [] q [] yY [] zZ -> ->.
    by exists x, y, z, q.
  + case => x [] y [] z [] q [] xX [] yY [] zZ ->.
    by exists x, (y <| q |> z); split => //; rewrite in_setE /= hull_necsetU; split => //; exists y, z, q.
do 2 apply val_inj => /=; rewrite /= in H; rewrite {}H0 {}H.
apply eqEsubset => a;
  first by case => x [] y [] z [] q [] xX [] yY [] zZ H; exists x, x, y, z, q; rewrite commute convmm H.
by case => x0 [] x1 [] y [] z [] q [] x0X [] x1X [] yY [] zZ; rewrite commute => ->; exists (x0 <| q |> x1), y, z, q; split; first by move/asboolP: (CSet.H (NECSet.car X)); apply.
Qed.
Definition semiLattConvMixin := @SemiLattConvType.Class [choiceType of necset A] (necset_semiLattType.semiLattMixin A) (necset_convType.convMixin A) (SemiLattConvType.Mixin axiom).
End def.
End necset_semiLattConvType.
Canonical necset_semiLattConvType A := SemiLattConvType.Pack (necset_semiLattConvType.semiLattConvMixin A).


(* non-empty convex sets of distributions *)
Notation "{ 'csdist+' T }" := (necset (Dist_convType T)) (format "{ 'csdist+'  T }") : convex_scope.

Definition lattConvType := convType.

Section Pdelta.
(* Pdelta = necset \o Dist, where
   - Dist is the free convex space functor, and
   - necset is the finitely-supported convex power functor. *)
Definition Pdelta : choiceType -> lattConvType := fun x => necset_convType (Dist_convType x).

Variable x : choiceType.
Check Pdelta x : convType.

Section monad_eps.

(*
Convn : forall (A : convType) (n : nat), {dist fintype.ordinal n} -> (fintype.ordinal n -> A) -> A
*)

Definition eps0 : forall {C : convType}, Dist C -> C.
move=> C d.
set supp := finsupp d.
set n := #|` supp|.
have @c0 : C.
  admit.
set f : 'I_n -> C := fun i => nth c0 supp i.
have @d' : {dist 'I_n}.
  set f' : 'I_n -> R := d \o f.
  admit.
exact: (Convn d' f).
Admitted.

(* just flattening of lattice joins? preserves oplus and convex hull*)
Axiom eps1 : forall {L : lattConvType}, necset L -> L.


Module sldiff.
Section def.
Variable L : semiCompSemiLattType.
Definition DL := L -> L.

Definition addD (f g : DL) : DL := f \o g.

Lemma addDA : associative addD.
Proof. done. Qed.

Lemma addD0 f : addD f idfun = f.
Proof. done. Qed.

Lemma add0D f : addD idfun f = f.
Proof. done. Qed.

Canonical addD_monoid := Monoid.Law addDA add0D addD0.

Local Open Scope latt_scope.
Definition i (x : L) : DL := fun y => x [+] y.

Lemma i_morph : {morph i : x y / joet x y >-> addD x y}.
Proof. by move=> x y; apply funext => z; rewrite /i  /addD /= joetA. Qed.

(*
Lemma addDC : commutative addD.
Admitted.
Canonical addD_comoid := Monoid.ComLaw addDC.
*)
End def.
End sldiff.

Section eps1.
Local Open Scope classical_set_scope.
Definition eps1' : forall {L : semiCompSemiLattConvType}, necset L -> L.
Proof.
move => L [] X.
case/cset0PN/cid => x Xx.
(*
(* we need complete semilattice! *)

move:(\big[@sldiff.addD L/idfun]_(y in (X `\ x)) sldiff.i y).

set CX := CSet.car (NECSet.car X).
(*set CX := (FSCSet.car (NECSet.car X)).*)
Local Open Scope classical_set_scope.
Check \bigcup_(x in CX) id.
Check bigsetU .
Admitted.
*)
Abort.
End eps1.

Definition join1' (C : convType) (s : necset (necset_convType C)) : {convex_set C} := (CSet.mk (convex_hull (bigsetU (NECSet.car s) (fun x => if x \in s then NECSet.car x else cset0 _)))).

Lemma join1'_neq0 (C : convType) (s : necset (necset_convType C)) : join1' s != cset0 _.
Proof.
case: s => s Hs.
rewrite cset0P hull_eq0 set0P.
case/set0P: (Hs) => -[] y Hy /=.
case/set0P: (Hy) => x yx /= sy.
exists x; exists {| NECSet.car := y; NECSet.H := Hy |} => //=.
  by have -> : {| NECSet.car := y; NECSet.H := Hy |}
                 \in {| NECSet.car := s; NECSet.H := Hs |}
  by rewrite inE asboolE.
Qed.

Definition join1 (C : convType) (s : necset (necset_convType C)) : necset C :=
  NECSet.mk (join1'_neq0 s).

Lemma eps1_correct (C : convType) (s : necset (necset_convType C)) :
  eps1 s = join1 s.
Admitted.

(* the morphism part of necset *)
Definition necset_mor (A B : convType) (f : {affine A -> B}) : necset_convType A -> necset_convType B.
case=> car car0.
apply: (@NECSet.mk _ (@CSet.mk _ (f @` car) _)).
  rewrite /is_convex_set.
  apply/asboolP => x y p; rewrite 3!in_setE => -[a0 Ha0 <-{x}] [a1 Ha1 <-{y}].
  exists (a0 <|p|> a1) => //.
  by rewrite -in_setE; apply/mem_convex_set; rewrite in_setE.
  by rewrite (affine_functionP' f).
move=> H.
case/cset0PN : car0 => a carx.
apply/cset0PN; exists (f a) => /=; by exists a.
Defined.

(* the results of necset_mor are semiLattConvType-morphisms, i.e., are affine and preserve semilatt operations *)
Lemma necset_mor_affine (A B : convType) (f : {affine A -> B}) : affine_function (necset_mor f).
Admitted.

Lemma necset_mor_semilatt_morphism (A B : convType) (f : {affine A -> B}) : 
  {morph (necset_mor f) : x y / SemiLattOp x y >-> SemiLattOp x y}.
Admitted.

Section P_delta.
(* P_delta = necset \o Dist, where
   - Dist is the free convex space functor, and
   - necset is the convex powerset functor. *)
Definition P_delta : choiceType -> choiceType := fun x => [choiceType of necset (Dist_convType x)].

Variable C : choiceType.
Check @eps0 (Dist_convType C).
Check necset_mor (@eps0 (Dist_convType C)).

Definition join {T : choiceType} : P_delta (P_delta T) -> P_delta T := eps1 \o necset_mor eps0.

End P_delta.


!!!!!

(* for an affine function f, returns a function F#f that to each convex set of dist returns its image by f, f needs to be affine *)
Definition F0 : forall (X Y : choiceType), (X -> Y) -> Dist X -> Dist Y
  := fun X Y (f : X -> Y) (d : Dist X) => DistBind.d d ((@Dist1.d Y) \o f).
Local Open Scope fset_scope.
Definition F1 : forall {X Y : convType}, (X -> Y) -> necset X -> necset Y.
Proof.
move => X Y f.
case => carX Xneq0. 
set sX := (fscset_supp carX).
set sY := [fset f x | x in sX].
apply (@NECSet.mk Y (@FSCSet.mk Y (CSet.mk (convex_hull [set a : Y | a \in sY])) (ex_intro _ sY erefl))).
rewrite /=.
apply/eqP => -[].
apply/eqP; rewrite hull_eq0.
apply/set0P.
move: (Xneq0). rewrite -fscset_supp0E /sX.
case/fset0Pn => x' Hx'.
exists (f x').
by rewrite in_imfset.
Defined.
(*
Axiom F_preserves_affine : forall (X Y : convType) (f : X -> Y),
    affine_function f -> affine_function (F f).
*)

Check F1 eps0.

(*
mu : U0 U1 F1 F0 U0 U1 F1 F0 -> U0 U1 F1 F0.
eps : F1 F0 U0 U1 -> Id.
eps0 : F0 U0 -> Id.
eps1 : F1 U1 -> Id.
eps = eps1 \o (F1 eps0 U1)
mu = U0 U1 eps F1 F0

Pdelta (functorial action of Pdelta) = F1 F0
mu : F1 F0 F1 F0 -> F1 F0.
eps : F1 F0 -> Id.
eps0 : F0 -> Id.
eps1 : F1 -> Id.
eps = eps1 \o (F1 eps0)
mu = @eps (fun x => F1 (F0 x))
*)

Definition eps {T : choiceType} : Pdelta (Pdelta T) -> Pdelta T := eps1 \o F1 eps0.

Definition mu {T : choiceType} : Pdelta (Pdelta T) -> Pdelta T := eps.

End monad_eps.

End Pdelta.
