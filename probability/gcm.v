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

Section misc.
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
apply/eqP => /(@eqR_mul2r (/ r)) []; last by apply/invR_neq0. 
move/eqP: Hr' => Hr'.
rewrite mulRAC mulRV // !mul1R => srV.
move: (prob_le1 s); rewrite srV.
move/prob_gt0: Hr' => Hr'.
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

Section misc_dist_of_Dist.
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
End misc_dist_of_Dist.

Section misc_Convn_indexed_over_finType.
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
End misc_Convn_indexed_over_finType.
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
by rewrite inE asboolE; exists x, y; split; try split.
Qed.
Definition conv X Y p : necset A := NECSet.mk (pre_conv_neq0 X Y p).
Lemma conv1 X Y : conv X Y `Pr 1 = X.
Proof.
rewrite necset_ext /= cset_ext /= ; apply/eqEsubset => a;
  first by case => x [] y [] xX [] yY ->; rewrite -in_setE conv1.
case/set0P: (NECSet.H Y) => y; rewrite -in_setE => yY.
rewrite -in_setE => aX.
by exists a, y; split; try split; rewrite ?conv1.
Qed.
Lemma convmm X p : conv X X p = X.
Proof.
rewrite necset_ext /= cset_ext /=; apply eqEsubset => a.
- case => x [] y [] xX [] yY ->.
  by rewrite -in_setE; move/asboolP: (CSet.H (NECSet.car X)); apply => //.
- rewrite -in_setE => aX.
  by exists a, a; rewrite convmm; split; try split.
Qed.
Lemma convC X Y p : conv X Y p = conv Y X `Pr p.~.
Proof.
by rewrite necset_ext /= cset_ext /=; apply eqEsubset => a; case => x [] y [] xX [] yY ->; exists y, x; split => //; split => //; [rewrite convC | rewrite -convC].
Qed.
Lemma convA p q X Y Z :
  conv X (conv Y Z q) p = conv (conv X Y [r_of p, q]) Z [s_of p, q].
Proof.
rewrite necset_ext /= cset_ext /=; apply eqEsubset => a; case => x [].
- move=> y [] xX [].
  rewrite in_setE => -[] y0 [] z0 [] y0Y [] z0Z -> ->.
  exists (x <| [r_of p, q] |> y0), z0.
  split; first by  rewrite inE asboolE /=; exists x, y0; split; try split.
  split => //.
  by rewrite convA.
- move=> z []; rewrite in_setE => -[] x0 [] y [] x0X [] yY -> [] zZ ->.
  exists x0, (y <| q |> z).
  split => //.
  split; first by rewrite inE asboolE /=; exists y, z; split; try split.
  by rewrite -convA.
Qed.
Definition convMixin : ConvexSpace.class_of [choiceType of necset A]
  := @ConvexSpace.Class _ conv conv1 convmm convC convA.
End def.
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
Lemma op_C : commutative op.
Proof. move=> X Y; by rewrite necset_ext /= cset_ext /= setUC. Qed.
Lemma op_A : associative op.
Proof. by move=> X Y Z; rewrite necset_ext /= cset_ext /= hullUA. Qed.
Lemma op_xx : idempotent op.
Proof.  by move=> X; rewrite necset_ext /= cset_ext /= setUid hull_cset. Qed.
Definition semiLattMixin := SemiLattice.Class op_C op_A op_xx.
End def.
End necset_semiLattType.
Canonical necset_semiLattType A := SemiLattice.Pack (necset_semiLattType.semiLattMixin A).

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

Axiom eps1 : forall {L : semiLattConvType}, necset L -> L (* just flattening of lattice joins? preserves oplus and convex hull*).
(* for an affine function f, returns a function F#f that to each convex set of dist returns its image by f, f needs to be affine *)

(* for gcm.v *)
Definition eps1' : forall {L : semiLattConvType}, necset L -> L.
move => L X.
set CX := (FSCSet.car (NECSet.car X)).
Local Open Scope classical_set_scope.
Check \bigcup_(x in CX) x.


(*
Axiom F : forall {X Y : convType}, (X -> Y) -> P X -> P Y.
Fail Axiom F_preserves_affine : forall (X Y : convType) (f : X -> Y),
    affine_function f -> affine_function (F f).
*)

(* the outputs of P carries a semilattice structure
   (NB: this needs to be reviewed) *)
Axiom P_semiLattClass : forall X, SemiLattice.class_of (P X).
Canonical P_semiLattType X := SemiLattice.Pack (P_semiLattClass X).

Canonical conv_lattType C := @SemiLattice.Pack (P_convType C) (P_semiLattClass _).

Definition PD := P \o Dist.

Definition join {T : choiceType} : PD (PD T) -> PD T := eps1 \o F eps0.

End P_delta.
