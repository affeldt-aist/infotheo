Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype finfun bigop.
Require Import Reals_ext Rbigop ssrR proba dist convex_choice.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import finmap set.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope convex_scope.

Module Rnneg.
Local Open Scope R_scope.
Record t := mk {
  v : R ;
  H : 0 <b= v }.
Definition K (r : t) := H r.
Arguments K : simpl never.
Module Exports.
Notation Rnneg := t.
Notation "'`Nneg' r" := (@mk r (@K _)) (format "'`Nneg'  r", at level 6).
Coercion v : t >-> R.
End Exports.
End Rnneg.
Export Rnneg.Exports.

Canonical Rnneg_subType := [subType for Rnneg.v].
Definition Rnneg_eqMixin := Eval hnf in [eqMixin of Rnneg by <:].
Canonical Rnneg_eqType := Eval hnf in EqType Rnneg Rnneg_eqMixin.
Definition Rnneg_choiceMixin := Eval hnf in [choiceMixin of Rnneg by <:].
Canonical Rnneg_choiceType := Eval hnf in ChoiceType Rnneg Rnneg_choiceMixin.

Section Rnneg_lemmas.
Local Open Scope R_scope.

Definition mkRnneg x H := @Rnneg.mk x (introT (leRP _ _) H).

Canonical Rnneg0 := @mkRnneg 0 (leRR 0).
Canonical Rnneg1 := @mkRnneg 1 Rle_0_1.

Lemma Rnneg_0le (x : Rnneg) : 0 <= x.
Proof. by case: x => p /= /leRP. Qed.

Lemma addRnneg_0le (x y : Rnneg) : 0 <b= x + y.
Proof. apply/leRP/addR_ge0; apply/Rnneg_0le. Qed.
Canonical addRnneg x y := Rnneg.mk (addRnneg_0le x y).

Lemma mulRnneg_0le (x y : Rnneg) : 0 <b= x * y.
Proof. by apply/leRP/mulR_ge0; apply/Rnneg_0le. Qed.
Canonical mulRnneg x y := Rnneg.mk (mulRnneg_0le x y).
End Rnneg_lemmas.

Section misc.
Lemma fsval_inj : forall A S x y, @fsval A S x = @fsval A S y -> x = y.
Proof.
move => A B -[x xP] -[y yP] /= xy.
move: xP yP.
rewrite xy => xP yP.
move: (bool_irrelevance xP yP) => xPyP.
case/boolP: (y \in B == true); move/eqP => HyB; by rewrite xPyP.
Qed.

Lemma cset_ext (A : convType) (X Y : {convex_set A}) :
  X = Y <-> (X = Y :> set A).
Proof.
case: X => carX HX; case: Y => carY HY.
split => [-> // | /= H].
destruct H.
congr CSet.mk.
exact/Prop_irrelevance.
Qed.

Section misc_prob.
Local Open Scope R_scope.
Lemma p_of_rs1 (r s : prob) :
  ([p_of r, s] == `Pr 1) = (r == `Pr 1) && (s == `Pr 1).
Proof.
apply/idP/idP; last by case/andP => /eqP -> /eqP ->; rewrite p_of_r1.
move/eqP/(congr1 Prob.p); rewrite /= p_of_rsE => /eqP.
apply contraLR => /nandP H.
wlog: r s H / r != `Pr 1;
  first by case: H;
  [ move => H /(_ r s); rewrite H; apply => //; by left
  | move => H /(_ s r); rewrite H mulRC; apply => //; by left ].
move=> Hr.
case/boolP: (r == `Pr 0);
  first by move/eqP ->; rewrite mul0R eq_sym; apply/eqP/R1_neq_R0.
case/prob_gt0/ltR_neqAle => /eqP; rewrite [in X in X -> _]eq_sym => /eqP Hr' _.
apply/eqP => /(@eqR_mul2r (/ r)).
move/(_ (invR_neq0 _ Hr')).
rewrite mulRAC mulRV ?mul1R; last exact/eqP.
move=> srV.
move: (prob_le1 s); rewrite srV.
move/eqP : Hr' => /prob_gt0 Hr'.
rewrite invR_le1 // => Hr''.
move: (prob_le1 r) => Hr'''.
suff: r = 1 :> R by apply/eqP; rewrite Hr.
by apply eqR_le.
Qed.

Lemma p_of_rs1P r s : reflect (r = `Pr 1 /\ s  = `Pr 1) ([p_of r, s] == `Pr 1).
Proof.
move: (p_of_rs1 r s) ->.
apply: (iffP idP);
  [by case/andP => /eqP -> /eqP -> | by case => -> ->; rewrite eqxx].
Qed.

Lemma prob10 : `Pr 1 <> `Pr 0.
Proof. by move/(congr1 Prob.p)/R1_neq_R0. Qed.
End misc_prob.

Lemma Dist_eval_affine (C : choiceType) (x : C) :
  affine_function (fun D : Dist C => D x).
Proof. by move=> a b p; rewrite /affine_function_at Conv2Dist.dE. Qed.

Section misc_hull.
Local Open Scope classical_set_scope.
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

(* hull (X `|` hull Y) = hull (hull (X `|` Y)) = hull (x `|` y);
   the first equality looks like a tensorial strength under hull
   Todo : Check why this is so. *)
Lemma hull_strr (A : convType) (X Y : set A) :
  hull (X `|` hull Y) = hull (X `|` Y).
Proof.
apply/hull_eqEsubset => a.
- case; first by rewrite -in_setE => H; rewrite -in_setE; apply mem_hull_setU_left.
  case=> n [d [g [H0 H1]]].
  exists n, d, g; split => //.
  apply (subset_trans H0) => b Hb.
  by right.
- by case; rewrite -in_setE => H; rewrite -in_setE; [ | rewrite setUC] ; apply mem_hull_setU_left => //; apply hull_mem.
Qed.

Lemma hull_strl (A : convType) (X Y : set A) :
  hull (hull X `|` Y) = hull (X `|` Y).
Proof. by rewrite [in LHS]setUC [in RHS]setUC hull_strr. Qed.

Lemma hullUA (A : convType) (X Y Z : {convex_set A}) :
  hull (X `|` hull (Y `|` Z)) = hull (hull (X `|` Y) `|` Z).
Proof. by rewrite hull_strr hull_strl setUA. Qed.
End misc_hull.

Section misc_scaled.
Import ScaledConvex.
Lemma scalept_addRnneg : forall (A : convType) (x : scaled_pt A),
    {morph (fun (r : Rnneg) => scalept r x) : r s / addRnneg r s >-> addpt r s}.
Proof. by move=> A x [] r /= /leRP Hr [] s /= /leRP Hs; apply scalept_addR. Qed.
Definition big_scaleptl (A : convType) (x : scaled_pt A) := 
  @big_morph
    (@scaled_pt A)
    Rnneg
    (fun r : Rnneg => scalept r x)
    (Zero A)
    (@addpt A)
    Rnneg0
    addRnneg
    (@scalept_addRnneg A x).
Local Open Scope R_scope.
Lemma big_scaleptl' (A : convType) (x : scaled_pt A) :
  scalept R0 x = Zero A ->
  forall (I : Type) (r : seq I) (P : pred I) (F : I -> R),
    (forall i : I, 0 <= F i) ->
    scalept (\big[Rplus/R0]_(i <- r | P i) F i) x =
    \big[addpt (A:=A)/Zero A]_(i <- r | P i) scalept (F i) x.
Proof.
move=> H I r P F H'.
transitivity (\big[addpt (A:=A)/Zero A]_(i <- r | P i) (fun r0 : Rnneg => scalept r0 x) (mkRnneg (H' i))); last by reflexivity.
rewrite -big_scaleptl ?scalept0 //.
congr scalept.
transitivity (\sum_(i <- r | P i) mkRnneg (H' i)); first by reflexivity.
apply (big_ind2 (fun x y => x = (Rnneg.v y))) => //.
by move=> x1 [v Hv] y1 y2 -> ->.
Qed.
End misc_scaled.
End misc.

Module dist_of_Dist.
Section def.
Variable (A : choiceType) (P : Dist A).
Local Open Scope fset_scope.
Local Open Scope R_scope.
Local Open Scope reals_ext_scope.
Definition D := [finType of finsupp P] : finType.
Definition f := [ffun d : D => P (fsval d)].
Lemma f0 b : 0 <= f b. Proof. rewrite ffunE; by apply Dist.ge0. Qed.
Lemma f1 : \sum_(b in D) f b = 1.
Proof.
rewrite -(Dist.f1 P) big_seq_fsetE /=.
apply eq_bigr => a; by rewrite ffunE.
Qed.
Definition dist_of_Dist : dist D := locked (proba.makeDist f0 f1).
End def.
Module Exports.
Notation dist_of_Dist := dist_of_Dist.
End Exports.
End dist_of_Dist.
Export dist_of_Dist.Exports.

Section dist_of_Dist_lemmas.
Variable (A : choiceType) (d : Dist A).
Lemma dist_of_DistE i : dist_of_Dist d i = d (fsval i).
Proof. by rewrite /dist_of_Dist; unlock; rewrite ffunE; reflexivity. Qed.
Lemma dist_of_DistDE : dist_of_Dist.D d = [finType of finsupp d].
Proof. reflexivity. Qed.
End dist_of_Dist_lemmas.

Module Convn_indexed_over_finType.
Section def.
Local Open Scope R_scope.
Variables (A : convType) (T : finType) (d : {dist T}) (f : T -> A).
Definition n := #| T |.
Definition t0 : T.
Proof.
move/card_gt0P/xchoose: (dist_domain_not_empty d) => t0; exact t0.
Defined.
Definition enum : 'I_n -> T := fun i => nth t0 (index_enum T) i.
Definition d_enum := [ffun i => d (enum i)].
Lemma d_enum0 : forall b, 0 <= d_enum b.
Proof.
move=> b.
rewrite ffunE.
by apply dist_ge0.
Qed.
Lemma d_enum1 : \sum_(b in 'I_n) d_enum b = 1.
Proof.
rewrite -(@epmf1 T d).
rewrite /d_enum.
transitivity (\sum_(b in 'I_n) d (enum b));
  first by apply eq_bigr => i; rewrite ffunE.
rewrite -big_image /=.
suff -> : (image_mem enum (mem (ordinal n))) = index_enum T
  by done.
apply (eq_from_nth (x0 := t0)) => [ | i ];
  first by rewrite size_image /index_enum -enumT -cardT card_ord.
rewrite size_image => i_n.
rewrite (nth_image t0 enum (Ordinal i_n)) /enum /=.
congr nth.
by rewrite enum_val_ord /=.
Qed.
Definition dist := proba.makeDist d_enum0 d_enum1.
Definition Convn_indexed_over_finType : A := Convn dist (f \o enum).
End def.
Module Exports.
Notation Convn_indexed_over_finType := Convn_indexed_over_finType.
End Exports.
End Convn_indexed_over_finType.
Export Convn_indexed_over_finType.Exports.

Section S1_Convn_indexed_over_finType.
Import ScaledConvex.
Variables (A : convType) (T : finType) (d : {dist T}) (f : T -> A).
Lemma S1_Convn_indexed_over_finType :
  S1 (Convn_indexed_over_finType d f)
  = \big[addpt (A:=A)/Zero A]_i scalept (d i) (S1 (f i)).
Proof.
rewrite /Convn_indexed_over_finType.
rewrite S1_convn /=.
evar (X : nat -> scaled_pt A).
transitivity (\big[addpt (A:=A)/Zero A]_(i < Convn_indexed_over_finType.n T) X i).
- apply eq_bigr => -[i Hi] _.
  set (i' := nat_of_ord (Ordinal Hi)).
  rewrite ffunE.
  rewrite /Convn_indexed_over_finType.enum /=.
  set F := (fun i => 
           scalept (d (nth (Convn_indexed_over_finType.t0 d) (index_enum T) i))
          (S1 (f (nth (Convn_indexed_over_finType.t0 d) (index_enum T) i)))).
  transitivity (F i'); by exact: erefl.
move: (@big_mkord
         (scaled_pt A)
         (@Zero _)
         (@addpt _)
         (Convn_indexed_over_finType.n T)
         xpredT
         X) => <-.
rewrite /Convn_indexed_over_finType.n cardE -filter_index_enum.
have -> : [seq x <- index_enum T | T x] = index_enum T.
- rewrite -[in RHS](filter_predT (index_enum T)).
  by congr filter.
set F := (fun x => scalept (d x) (S1 (f x))).
by move: (@big_nth
            (scaled_pt A)
            (@Zero _)
            (@addpt _)
            T
            (Convn_indexed_over_finType.t0 d)
            (index_enum T)
            xpredT
            F) <-.
Qed.
End S1_Convn_indexed_over_finType.

Section S1_proj_Convn_indexed_over_finType.
Import ScaledConvex.
Variables (A B : convType) (prj : A -> B).
Hypothesis prj_affine : affine_function prj.
Variables (T : finType) (d : {dist T}) (f : T -> A).

Lemma S1_proj_Convn_indexed_over_finType :
  S1 (prj (Convn_indexed_over_finType d f))
  = \big[@addpt B/Zero B]_i scalept (d i) (S1 (prj (f i))).
Proof.
set (prj' := AffineFunction.Pack (Phant (A -> B)) prj_affine).
move: (affine_function_Sum prj') => /= ->.
exact: S1_Convn_indexed_over_finType.
Qed.
End S1_proj_Convn_indexed_over_finType.

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

Section necset_lemmas.
Variable A : convType.
Lemma necset_ext (X Y : necset A) : X = Y <-> (X = Y :> {convex_set A}).
Proof.
case: X => carX HX; case: Y => carY HY.
split => [-> // | /= H].
destruct H.
congr NECSet.mk.
exact/Prop_irrelevance.
Qed.

Local Open Scope classical_set_scope.
Lemma hull_necsetU (X Y : necset A) : hull ((X : {convex_set A}) `|` (Y : {convex_set A})) = [set u | exists x, exists y, exists p, x \in X /\ y \in Y /\ u = x <| p |> y] :> set A.
Proof.
apply eqEsubset => a.
- rewrite -in_setE; case/hull_setU; try by apply/set0P/NECSet.H.
  move=> x [] xX [] y [] yY [] p ->.
  by exists x, y, p.
- by case => x [] y [] p [] xX [] yY ->; rewrite -in_setE; apply mem_hull_setU.
Qed.
End necset_lemmas.

(* non-empty convex sets of distributions *)
Notation "{ 'csdist+' T }" := (necset (Dist_convType T)) (format "{ 'csdist+'  T }") : convex_scope.

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

Module necset_convType.
Section def.
Variable A : convType.
Definition pre_pre_conv (X Y : necset A) (p : prob) : set A :=
  [set a : A | exists x, exists y, x \in X /\ y \in Y /\ a = x <| p |> y].
Lemma pre_pre_conv_convex X Y p : is_convex_set (pre_pre_conv X Y p).
Proof.
apply/asboolP => u v q.
rewrite inE => /asboolP [] x0 [] y0 [] x0X [] y0Y ->.
rewrite inE => /asboolP [] x1 [] y1 [] x1X [] y1Y ->.
rewrite commute inE asboolE.
exists (x0 <|q|> x1), (y0 <|q|> y1).
split; first by move/asboolP: (CSet.H (NECSet.car X)); apply.
by split; first by move/asboolP: (CSet.H (NECSet.car Y)); apply.
Qed.
Definition pre_conv X Y p : {convex_set A} :=
  CSet.mk (pre_pre_conv_convex X Y p).
Lemma pre_conv_neq0 X Y p : pre_conv X Y p != cset0 _.
Proof.
case/set0P: (NECSet.H X) => x; rewrite -in_setE => xX.
case/set0P: (NECSet.H Y) => y; rewrite -in_setE => yY.
apply/set0P; exists (x <| p |> y); rewrite -in_setE.
by rewrite inE asboolE; exists x, y.
Qed.
Definition conv X Y p : necset A := locked (NECSet.mk (pre_conv_neq0 X Y p)).
Lemma conv1 X Y : conv X Y `Pr 1 = X.
Proof.
rewrite/conv; unlock; rewrite necset_ext /= cset_ext /= ; apply/eqEsubset => a;
  first by case => x [] y [] xX [] yY ->; rewrite -in_setE conv1.
case/set0P: (NECSet.H Y) => y; rewrite -in_setE => yY.
rewrite -in_setE => aX.
by exists a, y; rewrite conv1.
Qed.
Lemma convmm X p : conv X X p = X.
Proof.
rewrite/conv; unlock; rewrite necset_ext /= cset_ext /=; apply eqEsubset => a.
- case => x [] y [] xX [] yY ->.
  by rewrite -in_setE; move/asboolP: (CSet.H (NECSet.car X)); apply => //.
- rewrite -in_setE => aX.
  by exists a, a; rewrite convmm.
Qed.
Lemma convC X Y p : conv X Y p = conv Y X `Pr p.~.
Proof.
by rewrite/conv; unlock; rewrite necset_ext /= cset_ext /=; apply eqEsubset => a; case => x [] y [] xX [] yY ->; exists y, x; [rewrite convC | rewrite -convC].
Qed.
Lemma convA p q X Y Z :
  conv X (conv Y Z q) p = conv (conv X Y [r_of p, q]) Z [s_of p, q].
Proof.
rewrite/conv; unlock; rewrite necset_ext /= cset_ext /=; apply eqEsubset => a; case => x [].
- move=> y [] xX [].
  rewrite in_setE => -[] y0 [] z0 [] y0Y [] z0Z -> ->.
  exists (x <| [r_of p, q] |> y0), z0.
  by rewrite inE asboolE /= convA; split; try exists x, y0.
- move=> z []; rewrite in_setE => -[] x0 [] y [] x0X [] yY -> [] zZ ->.
  exists x0, (y <| q |> z).
  split => //.
  by rewrite inE asboolE /= -convA; split; try exists y, z.
Qed.
Definition convMixin : ConvexSpace.class_of [choiceType of necset A]
  := @ConvexSpace.Class _ conv conv1 convmm convC convA.
End def.
Section lemmas.
Local Open Scope classical_set_scope.
Variable A : convType.
Lemma convE X Y p : (conv X Y p : {convex_set A})=
  [set a : A | exists x, exists y, x \in X /\ y \in Y /\ a = x <| p |> y]
    :> set A.
Proof. rewrite/conv; unlock; reflexivity. Qed.
End lemmas.
End necset_convType.
Canonical necset_convType A := ConvexSpace.Pack (necset_convType.convMixin A).

Module necset_semiLattType.
Section def.
Local Open Scope classical_set_scope.
Variable (A : convType).
Definition pre_op (X Y : necset A) : {convex_set A}
  := CSet.mk (convex_hull ((X : {convex_set A}) `|` (Y : {convex_set A}))).
Lemma pre_op_neq0 X Y : pre_op X Y != cset0 A.
Proof.
case: X => carX /= HX; case: Y => carY /= HY.
apply/eqP; rewrite cset_ext /=; apply/eqP; rewrite hull_eq0.
apply/eqP; rewrite setU_eq0.
move/eqP: HX; rewrite cset_ext => HX; move/eqP: HY; rewrite cset_ext => HY.
by case.
Qed.
Definition op X Y := NECSet.mk (pre_op_neq0 X Y).
Lemma opC : commutative op.
Proof. move=> X Y; by rewrite necset_ext /= cset_ext /= setUC. Qed.
Lemma opA : associative op.
Proof. by move=> X Y Z; rewrite necset_ext /= cset_ext /= hullUA. Qed.
Lemma opxx : idempotent op.
Proof.  by move=> X; rewrite necset_ext /= cset_ext /= setUid hull_cset. Qed.
Definition semiLattMixin := SemiLattice.Class opC opA opxx.
End def.
End necset_semiLattType.
Canonical necset_semiLattType A := SemiLattice.Pack (necset_semiLattType.semiLattMixin A).

Module necset_semiLattConvType.
Section def.
Local Open Scope classical_set_scope.
Variable (A : convType).
Lemma axiom : forall p : prob,
    right_distributive
      (fun x : necset_semiLattType A => (necset_convType.conv x)^~ p) SemiLattOp.
Proof.
move=> p X Y Z.
have H : NECSet.car (SemiLattOp (necset_convType.conv X Y p) (necset_convType.conv X Z p))
          =  [set u | exists x0, exists x1, exists y, exists z, exists q, x0 \in X /\ x1 \in X /\ y \in Y /\ z \in Z /\ u = (x0 <| p |> y) <| q |> (x1 <| p |> z)] :> set A.
- rewrite /= hull_necsetU.
  apply eqEsubset => a.
  + case => u [] v [] q [].
    rewrite !in_setE !necset_convType.convE.
    case => x0 [] y [] x0X [] yY -> [] [] x1 [] z [] x1X [] zZ -> ->.
      by exists x0, x1, y, z, q.
  + case=> x0 [] x1 [] y [] z [] q [] x0X [] x1X [] yY [] zZ ->.
      by exists (x0 <| p |> y), (x1 <| p |> z), q; rewrite !in_setE !necset_convType.convE; split; [exists x0, y | split => //; exists x1, z].
have H0 : NECSet.car (necset_convType.conv X (SemiLattOp Y Z) p)
       = [set u | exists x, exists y, exists z, exists q, x \in X /\ y \in Y /\ z \in Z /\ u = x <| p |> (y <| q |> z)] :> set A.
- rewrite necset_convType.convE.
  apply eqEsubset => a.
  + case => x [] u [] xX []; rewrite in_setE /= hull_necsetU => -[] y [] z [] q [] yY [] zZ -> ->.
    by exists x, y, z, q.
  + case => x [] y [] z [] q [] xX [] yY [] zZ ->.
    by exists x, (y <| q |> z); split => //; rewrite in_setE /= hull_necsetU; split => //; exists y, z, q.
move: H H0; rewrite necset_ext /= cset_ext /= => -> ->.
apply eqEsubset => a;
  first by case => x [] y [] z [] q [] xX [] yY [] zZ H; exists x, x, y, z, q; rewrite commute convmm H.
by case => x0 [] x1 [] y [] z [] q [] x0X [] x1X [] yY [] zZ; rewrite commute => ->; exists (x0 <| q |> x1), y, z, q; split; first by move/asboolP: (CSet.H (NECSet.car X)); apply.
Qed.
Definition semiLattConvMixin := @SemiLattConvType.Class [choiceType of necset A] (necset_semiLattType.semiLattMixin A) (necset_convType.convMixin A) (SemiLattConvType.Mixin axiom).
End def.
End necset_semiLattConvType.
Canonical necset_semiLattConvType A := SemiLattConvType.Pack (necset_semiLattConvType.semiLattConvMixin A).

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

(* morphism part of Dist *)
Definition Dist_mor' (A B : choiceType) (f : A -> B) (d : Dist A) : Dist B
  := DistBind.d d (fun a => Dist1.d (f a)).
Definition Dist_mor (A B : choiceType) (f : A -> B) : {affine Dist A -> Dist B}.
refine (@AffineFunction.Pack _ _ _ (Dist_mor' f) _).
move=> x y t.
rewrite/affine_function_at.
exact: Conv2Dist.bind_left_distr.
Defined.

(* Dist_mor induces maps between supports *)
Definition Dist_mor_supp (A B : choiceType) (f : A -> B) (d : Dist A) :
  [finType of finsupp d] -> [finType of finsupp ((Dist_mor f) d)].
Proof.
move=> x.
apply (@FSetSub _ _ (f (fsval x))).
rewrite /= /Dist_mor' DistBind.supp imfset_id.
apply/bigfcupP.
exists (Dist1.d (f (fsval x))).
- rewrite andbT.
  apply (in_imfset _ (fun x => Dist1.d (f x))) => /=.
  by move:x; case:d.
- rewrite mem_finsupp Dist1.dE /Dist1.f /= fsfunE inE eqxx.
  by apply/eqP/R1_neq_R0.
Defined.
Arguments Dist_mor_supp [A B] f d.
Lemma fsval_Dist_mor_supp (A B : choiceType) (f : A -> B) d i :
  fsval ((Dist_mor_supp f d) i) = f (fsval i).
Proof. by case: i. Qed.
  
(* join operator for Dist *)
Definition join0 (C : choiceType) (d : Dist (Dist C)) : Dist C :=
  DistBind.d d (Dist_mor idfun).

(* join0 is ((coercion) \o eps0) *)
Section eps0_correct.
Import ScaledConvex.
Local Open Scope R_scope.
Lemma eps0_correct (C : choiceType) (d : Dist (Dist C)) :
  eps0 d = join0 d.
Proof.
rewrite /join0 -DistBindA DistBindp1.
apply Dist_ext => x.
rewrite -[LHS]Scaled1RK /eps0.
rewrite (@S1_proj_Convn_indexed_over_finType _ _ (fun D : Dist C => D x));
  last by apply Dist_eval_affine.
rewrite big_scaleR.
rewrite DistBind.dE /DistBind.f fsfunE.
case: ifP => [_ | ].
- transitivity (\sum_(i : dist_of_Dist.D d | true) d (fsval i) * (fsval i) x).
  + apply eq_bigr => -[v vP] _.
    move/scaleR_scalept:(dist_ge0 (dist_of_Dist d) [` vP]%fset) ->.
    by rewrite Scaled1RK dist_of_DistE.
  suff -> : finsupp d = [seq fsval i | i in [finType of finsupp d]] :> seq _
    by rewrite big_image; apply eq_bigl => a; rewrite inE.
  by rewrite enum_fsetE /=.
- rewrite !imfset_id.
  move/bigfcupP => H.
  have H' : forall i : Dist C, i \in finsupp d -> x \notin finsupp i
      by move=> i Hi; apply/negP => Hx; apply H; exists i => //; rewrite andbT.
  have H0 : 0 = \sum_(i | true) 0
    by move=> t; rewrite big_const iter_addR mulR0.
  rewrite [in RHS](H0 (dist_of_Dist.D d)).
  apply eq_bigr => -[v vP] _.
  move/scaleR_scalept:(dist_ge0 (dist_of_Dist d) [`vP]%fset) ->.
  rewrite dist_of_DistE /= mul1R.
  suff -> : v x = 0 by rewrite mulR0.
  rewrite fsfun_dflt //.
  by apply H'.
Qed.
End eps0_correct.

Section eps0_natural.
Import ScaledConvex.
Local Open Scope fset_scope.
Local Open Scope R_scope.
Lemma eps0_natural (C D : convType) (f : {affine C -> D}) :
  f \o eps0 = eps0 \o (Dist_mor f).
Proof.
apply funext => d.
apply S1_inj.
rewrite S1_proj_Convn_indexed_over_finType; last by case: f.
rewrite S1_Convn_indexed_over_finType.
evar (Y : dist_of_Dist.D ((Dist_mor f) d) -> scaled_pt D).
transitivity (\big[addpt (A:=D)/Zero D]_i Y i); last first.
- apply eq_bigr => i _ /=.
  rewrite dist_of_DistE /=.
  rewrite DistBind.dE /DistBind.f imfset_id /=.
  rewrite fsfunE.
  have -> : fsval i \in (\bigcup_(d0 <- [fset Dist1.d (f a) | a in finsupp d]) finsupp d0)
    by case: i => v; rewrite DistBind.supp imfset_id.
  have H : scalept R0 (S1 (fsval i)) = Zero D by rewrite scalept0.
  have H0 : forall a : C, 0 <= d a * (Dist1.d (f a)) (fsval i)
      by move=> a; apply mulR_ge0; apply Dist.ge0.
  rewrite big_scaleptl'; [| done | done] => {H} {H0}.
  rewrite (bigID (fun i0 => fsval i == f i0)) /=.
  have -> :
    (\big[addpt (A:=D)/Zero D]_(i0 <- finsupp d | fsval i != f i0)
        scalept (d i0 * (Dist1.d (f i0)) (fsval i)) (S1 (fsval i))) = Zero _
    by rewrite big1 // => c /negbTE Hc; rewrite Dist1.dE /Dist1.f fsfunE inE Hc mulR0 scalept0.
  rewrite addpt0.
  rewrite big_seq_fsetE /=.
  exact: erefl.
rewrite /Y => {Y}.
set f' := (Dist_mor_supp f d).
transitivity (\big[addpt (A:=D)/Zero D]_i scalept (dist_of_Dist d i) (S1 (fsval (f' i)))); first by apply eq_bigr => *; rewrite fsval_Dist_mor_supp.
rewrite (@partition_big
           _ _ _ _ (dist_of_Dist.D ((Dist_mor f) d)) _ f' xpredT) /f' //=.
apply eq_bigr => -[i Hi] _ /=.
transitivity (\big[addpt (A:=D)/Zero D]_(i0 | Dist_mor_supp f d i0 == [` Hi])
               scalept (d (fsval i0) * (Dist1.d (f (fsval i0))) i) (S1 i)).
- apply eq_bigr => i0 /eqP.
  move/(congr1 (@fsval _ _)); rewrite fsval_Dist_mor_supp /= => Hi0.
  rewrite dist_of_DistE Dist1.dE /Dist1.f fsfunE /=.
  have -> : i \in [fset f (fsval i0)] by rewrite -Hi0  inE.
  by rewrite -Hi0 mulR1.
apply eq_bigl => i0.
apply/eqP/eqP; first by move/(congr1 (@fsval _ _)) => /= <-.
move=> H.
apply/fsval_inj.
by rewrite fsval_Dist_mor_supp /= H.
Qed.
End eps0_natural.

Axiom eps1 : forall {L : semiLattConvType}, necset L -> L (* just flattening of lattice joins? preserves oplus and convex hull*).
(* for an affine function f, returns a function F#f that to each convex set of dist returns its image by f, f needs to be affine *)

(* for gcm.v *)
Definition eps1' : forall {L : semiLattConvType}, necset L -> L.
move => L X.
set CX := CSet.car (NECSet.car X).
(*set CX := (FSCSet.car (NECSet.car X)).*)
Local Open Scope classical_set_scope.
Check \bigcup_(x in CX) id.
Admitted.

(*
Axiom F : forall {X Y : convType}, (X -> Y) -> P X -> P Y.
Fail Axiom F_preserves_affine : forall (X Y : convType) (f : X -> Y),
    affine_function f -> affine_function (F f).
*)

(* the outputs of P carries a semilattice structure
   (NB: this needs to be reviewed) *)
(*Axiom P_semiLattClass : forall X, SemiLattice.class_of (P_delta X).
Canonical P_semiLattType X := SemiLattice.Pack (P_semiLattClass X).*)

(*Canonical conv_lattType C := @SemiLattice.Pack (P_convType C) (P_semiLattClass _).*)

(*Definition PD := P_delta \o Dist.*)

Axiom F : forall {X Y : convType}, (X -> Y) -> necset X -> necset Y.

Definition join {T : choiceType} : P_delta (P_delta T) -> P_delta T := eps1 \o F eps0.

End P_delta.
