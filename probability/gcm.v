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

Section misc_classical_sets.
Local Open Scope classical_set_scope.
Lemma eq_imagel (A B : Type) (f g : A -> B) (X : set A) :
  (forall a, X a -> f a = g a) -> f @` X = g @` X.
Proof.
by move=> H; apply eqEsubset=> a; case => x Xx <-; [rewrite H | rewrite -H] => //; exists x.
Qed.   
Lemma eq_imager (A B : Type) (f : A -> B) (X Y : set A) :
  X = Y -> f @` X = f @` Y.
Proof. by move ->. Qed.
Lemma imageA (A B C : Type) (f : A -> B) (g : B -> C) (X : set A) :
  g @` (f @` X) = (g \o f) @` X.
Proof.
apply eqEsubset => c.
- by case => b [] a Xa <- <-; apply/imageP.
- by case => a Xa <-; apply/imageP/imageP.
Qed.
Lemma image_idfun (A : Type) (X : set A) : idfun @` X = X.
Proof.
apply eqEsubset => a.
- by case=> /= x Xx <-.
- by exists a.
Qed.
Lemma image_setU (A B : Type) (f : A -> B) (X Y : set A) :
  f @` (X `|` Y) = f @` X `|` f @` Y.
Proof.
apply eqEsubset => b.
- by case=> a [] Ha <-; [left | right]; apply imageP.
- by case=> -[] a Ha <-; apply imageP; [left | right].
Qed.
Lemma image_set1 (A B : Type) (f : A -> B) (a : A) :
  f @` [set a] = [set f a].
Proof.
apply eqEsubset => b.
- by case=> a' -> <-.
- by move->; apply imageP.
Qed.
Lemma eq_bigcupl (A I : Type) (P Q : set I) (X : I -> set A) :
  P = Q -> bigsetU P X = bigsetU Q X.
Proof. by move ->. Qed.
Lemma eq_bigcupr (A I : Type) (P : set I) (X Y : I -> set A) :
  X =1 Y -> bigsetU P X = bigsetU P Y.
Proof. by move/funext ->. Qed.
Lemma eq_bigcup (A I : Type) (P Q : set I) (X Y : I -> set A) :
  P = Q -> X =1 Y -> bigsetU P X = bigsetU Q Y.
Proof. by move=> -> /funext ->. Qed.
Lemma bigcup_set1 (A I : Type) (P : set I) (f : I -> A) :
  \bigcup_(x in P) [set f x] = f @` P.
Proof.
apply eqEsubset=> a.
- by case=> i Pi ->; apply imageP.
- by case=> i Pi <-; exists i.
Qed.
Lemma bigcup0 (A I : Type) (X : I -> set A) : bigsetU set0 X = set0.
Proof. by apply eqEsubset => a // [] //. Qed.
Lemma bigcup1 (A I : Type) (i : I) (X : I -> set A) : bigsetU [set i] X = X i.
Proof.
apply eqEsubset => a.
- by case=> j ->.
- by exists i.
Qed.
Lemma bigcup_const (A I : Type) (P : set I) (X : I -> set A) (i : I) :
  P i -> (forall j, P j -> X j = X i) -> bigsetU P X = X i.
Proof.
move=> Pi H; apply eqEsubset=> a.
- by case=> j /H ->.
- by exists i.
Qed.

Lemma bigsubsetU (A I : Type) (P : set I) (X : I -> set A) (Y : set A) :
  (forall i, P i -> X i `<=` Y) <-> bigsetU P X `<=` Y.
Proof.
split.
- by move=> H a [] i Pi Xia; apply (H i).
- by move=> H i Pi a Xia; apply H; exists i.
Qed.

End misc_classical_sets.

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

Lemma hull_mem' (A : convType) (X : set A) : X `<=` hull X.
Proof. by move=> x; rewrite -in_setE; move/hull_mem; rewrite in_setE. Qed.

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
Local Open Scope R_scope.

Lemma scalept_conv (C : convType) (x y : R) (s : scaled_pt C) (p : prob):
  0 <= x -> 0 <= y ->
  scalept (x <|p|> y) s =
  (scalept x s : Scaled_convType C) <|p|> scalept y s.
Proof.
move=> Hx Hy.
move: (prob_ge0 p) => Hp.
move: (onem_ge0 (prob_le1 p)) => Hnp.
rewrite scalept_addR; try by apply mulR_ge0.
by rewrite /Conv /= /scaled_conv /= !scalept_comp.
Qed.

Lemma Dist_scalept_conv (C : convType) (x y : Dist C) (p : prob) (i : C) :
     scalept ((x <|p|> y) i) (S1 i) =
     ((scalept (x i) (S1 i)) : Scaled_convType C) <|p|> scalept (y i) (S1 i).
Proof.
rewrite Conv2Dist.dE.
change (p * x i + p.~ * y i) with (x i <|p|> y i).
by rewrite scalept_conv; try apply Dist.ge0.
Qed.

Lemma big_scalept_conv_split (C : convType) (I : Type) (r : seq I) (P : pred I)
      (F G : I -> Scaled_convType C) (p : prob):
  \big[addpt (A:=C)/Zero C]_(i <- r | P i)
   (F i  <|p|> G i) =
  ((\big[addpt (A:=C)/Zero C]_(i <- r | P i) F i) : Scaled_convType C)
    <|p|> (\big[addpt (A:=C)/Zero C]_(i <- r | P i) G i).
Proof.
by rewrite /Conv /= /scaled_conv big_split /= !big_scalept.
Qed.

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
Definition d : dist D := locked (proba.makeDist f0 f1).
End def.
Module Exports.
Notation dist_of_Dist := d.
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

Module NESet.
Section def.
Local Open Scope classical_set_scope.
Variable A : Type.
Record t : Type := mk {
  car : set A ;
  H : car != set0 }.
End def.
Module Exports.
Arguments H : simpl never.
Notation neset := t.
Coercion car : neset >-> set.
Notation "'`NE' s" := (@mk _ s (H _)) (format "'`NE'  s", at level 6).
End Exports.
End NESet.
Export NESet.Exports.

Section neset_canonical.
Variable A : Type.
Canonical neset_subType := [subType for @NESet.car A].
Canonical neset_predType :=
  Eval hnf in mkPredType (fun t : neset A => (fun x => x \in NESet.car t)).
Definition neset_eqMixin := Eval hnf in [eqMixin of (@neset A) by <:].
Canonical neset_eqType := Eval hnf in EqType (neset A) neset_eqMixin.
Definition neset_choiceMixin : Choice.mixin_of (neset A) := @gen_choiceMixin (neset A).
Canonical neset_choiceType : choiceType :=
  Eval hnf in Choice.Pack (Choice.Class neset_eqMixin neset_choiceMixin).
End neset_canonical.

Section misc.
Local Open Scope classical_set_scope.
Lemma bigcup_set0P (A I : Type) (S : set I) (F : I -> set A) :
  reflect (exists i, S i /\ F i !=set0) (bigsetU S F != set0).
Proof.
apply: (iffP idP).
- by case/set0P => a [] i Si Fia; exists i; split; [ | exists a].
- by case=> i [] Si [] a Fia; apply/set0P; exists a, i.
Qed.
End misc.

Section neset_lemmas.
Local Open Scope classical_set_scope.

Lemma set1_neq0 (T : Type) (x : T) : [set x] != set0.
Proof. by apply/set0P; exists x. Qed.

Lemma neset_bigsetU_neq0 (T I : Type) (S : neset I) (F : I -> neset T) :
      (bigsetU S F) != set0.
Proof.
apply/bigcup_set0P.
case: S => carS /= /set0P [] i Hi.
exists i; split => //.
by case: (F i) => carFi /= /set0P.
Qed.

Lemma neset_image_neq0 {A B} (f : A -> B) (X : neset A) : f @` X != set0.
Proof.
by apply/set0P; case: X => carX /= /set0P [] x Xx; exists (f x); apply/imageP.
Qed.

Lemma neset_setU_neq0 (T : Type) (X Y : neset T) : X `|` Y != set0.
Proof. by apply/set0P; case:X => catX /= [] /set0P [] x Xx; exists x; left. Qed.

Canonical neset1 {A} (x : A) := @NESet.mk A [set x] (set1_neq0 x).
Canonical bignesetU {A} (I : Type) (S : neset I) (F : I -> neset A) :=
  @NESet.mk _ (bigsetU S F) (neset_bigsetU_neq0 S F).
Canonical image_neset {A B} (f : A -> B) (X : neset A) :=
  @NESet.mk _ (f @` X) (neset_image_neq0 f X).
Canonical nesetU {T} (X Y : neset T) :=
  @NESet.mk _ (X `|` Y) (neset_setU_neq0 X Y).

Lemma neset_hull_neq0 (T : convType) (F : neset T) : hull F != set0.
Proof. by rewrite hull_eq0 NESet.H. Qed.

Canonical neset_hull (T : convType) (F : neset T) := @NESet.mk T (hull F) (neset_hull_neq0 F).

Lemma image_const (A B : Type) (X : neset A) (b : B) :
  (fun _ => b) @` X = [set b].
Proof.
apply eqEsubset=> b'.
- by case => ? _ ->.
- by case: X=> X /= /set0P [] a Xa ->; exists a.
Qed.

Lemma under_neset (T : Type) (X Y : set T) (Xneq0 : X != set0) (Yneq0 : Y != set0) : X = Y -> NESet.mk Xneq0 = NESet.mk Yneq0.
Proof. by move=> H; apply val_inj; rewrite /= H. Qed.

End neset_lemmas.
Notation underNE X Y := (@under_neset _ X Y (NESet.H _) (NESet.H _)).

Module NECSet.
Section def.
Local Open Scope classical_set_scope.
Local Open Scope proba_scope.
Variable A : convType.
Record t : Type := mk {
  car : convex_set A ;
  (*car : {convex_set A} ;*)
  H : car != cset0 _ }.
End def.
End NECSet.
Notation necset := NECSet.t.
Coercion NECSet.car : necset >-> convex_set.
(*Coercion NECSet.car : necset >-> convex_set_of.*)

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

Lemma necset_neq0 (t : necset A) : t != set0 :> set A.
Proof. by case: t => car; rewrite  /cset0P. Qed.

Canonical necset_neset (t : necset A) : neset A := NESet.mk (necset_neq0 t).

End necset_canonical.

Section necset_lemmas.
Variable A : convType.

Local Open Scope classical_set_scope.
Lemma hull_necsetU (X Y : necset A) : hull ((X : {convex_set A}) `|` (Y : {convex_set A})) = [set u | exists x, exists y, exists p, x \in X /\ y \in Y /\ u = x <| p |> y].
Proof.
apply eqEsubset => a.
- rewrite -in_setE; case/hull_setU; try by apply/set0P/NECSet.H.
  move=> x [] xX [] y [] yY [] p ->.
  by exists x, y, p.
- by case => x [] y [] p [] xX [] yY ->; rewrite -in_setE; apply mem_hull_setU.
Qed.

Lemma neset_hull_neq0' (T : convType) (F : neset T) :
  CSet.mk (convex_hull F) != cset0 _.
Proof. by rewrite cset0P /= neset_hull_neq0. Qed.
Canonical neset_hull_necset (T : convType) (F : neset T) := @NECSet.mk T (CSet.mk (convex_hull F)) (neset_hull_neq0' F).

End necset_lemmas.

(* non-empty convex sets of distributions *)
Notation "{ 'csdist+' T }" := (necset (Dist_convType T)) (format "{ 'csdist+'  T }") : convex_scope.


Module SemiCompleteSemiLattice.
Section def.
Local Open Scope classical_set_scope.
(* a semicomplete semilattice has an infinitary operation *)
Record class_of (T : choiceType) : Type := Class {
  op : neset T -> T;
  _ : forall x : T, op `NE [set x] = x;
  _ : forall (I : Type) (S : neset I) (F : I -> neset T),
               op (`NE (bigsetU S F)) = op (`NE (op @` (F @` S)));
}.
Structure type :=
  Pack {sort : choiceType; _ : class_of sort}.
End def.
Module Exports.
Definition Joet {T : type} : neset (sort T) -> sort T :=
  let: Pack _ (Class op _ _) := T in op.
Arguments Joet {T} : simpl never.
Notation semiCompSemiLattType := type.
Coercion sort : semiCompSemiLattType >-> choiceType.
End Exports.
End SemiCompleteSemiLattice.
Export SemiCompleteSemiLattice.Exports.

Section semicompletesemilattice_lemmas.
Local Open Scope classical_set_scope.

Variable (L : semiCompSemiLattType).

(*
[Reiterman]
- Commentationes Mathematicae Universitatis Carolinae
- Jan Reiterman
- On locally small based algebraic theories
- https://dml.cz/bitstream/handle/10338.dmlcz/106455/CommentatMathUnivCarol_027-1986-2_12.pdf
*)

(* [Reiterman] p.326, axiom 3 *)
Lemma Joet1 : forall x : L, Joet `NE [set x] = x.
Proof. by case: L => [? []]. Qed.
(* NB: bigsetU (bigsetI too) is the bind operator for the poserset monad *)
Lemma Joet_bigsetU : forall (I : Type) (S : neset I) (F : I -> neset L),
    Joet (bignesetU S F) = Joet `NE (Joet @` (F @` S)).
Proof. by case: L => [? []]. Qed.

Lemma Joet_bigcup (I : Type) (S : neset I) (F : I -> neset L) :
    Joet `NE (\bigcup_(i in S) F i) = Joet `NE (Joet @` (F @` S)).
Proof. by rewrite Joet_bigsetU. Qed.

Lemma setU_bigsetU T (I J : set T) : I `|` J = bigsetU [set I; J] idfun.
Proof.
apply eqEsubset => x; [case=> Hx; by [exists I => //; left | exists J => //; right] |].
by case=> K [] -> Hx; [left | right].
Qed.

Lemma nesetU_bigsetU T (I J : neset T) :
  `NE (I `|` J) = `NE (bigsetU [set I; J] idfun).
Proof.
apply/val_inj=> /=; apply eqEsubset => x; [case=> Hx; by [exists I => //; left | exists J => //; right] |].
by case=> K [] -> Hx; [left | right].
Qed.

Lemma Joet_setU (I J : neset L) : Joet `NE (I `|` J) = Joet `NE [set (Joet I); (Joet J)].
Proof.
rewrite nesetU_bigsetU Joet_bigsetU.
rewrite (underNE (Joet @` (idfun @` nesetU (neset1 I) (neset1 J))) [set Joet I; Joet J]) //.
by rewrite image_idfun /= image_setU !image_set1.
Qed.

(* NB: [Reiterman] p.326, axiom 1 is trivial, since our Joet operation receives
   a set but not a sequence. *)

(* [Reiterman] p.326, axiom 2 *)
Lemma Joet_flatten (F : neset (neset L)) : Joet `NE (Joet @` F) = Joet `NE (bigsetU F idfun).
Proof.
rewrite Joet_bigsetU (underNE (Joet @` F) (Joet @` (idfun @` F))) //.
apply eq_imager.
by rewrite image_idfun.
Qed.

Definition joet (x y : L) := Joet `NE [set x; y].
Global Arguments joet : simpl never.
Local Notation "x [+] y" := (joet x y) (format "x  [+]  y", at level 50) : latt_scope.
Local Open Scope latt_scope.

Lemma joetC : commutative joet.
Proof. by move=> x y; congr Joet; apply val_inj => /=; rewrite /joet setUC. Qed.
Lemma joetA : associative joet.
Proof.
by move=> x y z; rewrite /joet -[in LHS](Joet1 x) -[in RHS](Joet1 z) -!Joet_setU; congr Joet; apply val_inj => /=; rewrite setUA.
Qed.
Lemma joetxx : idempotent joet.
Proof.
by move=> x; rewrite -[in RHS](Joet1 x); congr Joet; apply val_inj => /=; rewrite setUid.
Qed.

Lemma joetAC : right_commutative joet.
Proof. by move=> x y z; rewrite -!joetA [X in _ [+] X]joetC. Qed.
Lemma joetCA : left_commutative joet.
Proof. by move=> x y z; rewrite !joetA [X in X [+] _]joetC. Qed.
Lemma joetACA : interchange joet joet.
Proof. by move=> x y z t; rewrite !joetA [X in X [+] _]joetAC. Qed.

Lemma joetKU y x : x [+] (x [+] y) = x [+] y.
Proof. by rewrite joetA joetxx. Qed.
Lemma joetUK y x : (x [+] y) [+] y = x [+] y.
Proof. by rewrite -joetA joetxx. Qed.
Lemma joetKUC y x : x [+] (y [+] x) = x [+] y.
Proof. by rewrite joetC joetUK joetC. Qed.
Lemma joetUKC y x : y [+] x [+] y = x [+] y.
Proof. by rewrite joetAC joetC joetxx. Qed.
End semicompletesemilattice_lemmas.
Notation "x [+] y" := (joet x y) (format "x  [+]  y", at level 50) : latt_scope.

Section Joet_morph.
Local Open Scope classical_set_scope.
Local Open Scope latt_scope.
Variable (L M : semiCompSemiLattType).
Definition Joet_morph (f : L -> M) :=
  forall (X : neset L), f (Joet X) = Joet `NE (f @` X).
Definition joet_morph (f : L -> M) :=
  forall (x y : L), f (x [+] y) = f x [+] f y.
Lemma Joet_joet_morph (f : L -> M) : Joet_morph f -> joet_morph f.
Proof.
move=> H x y.
move: (H `NE [set x; y]) => -> /=.
by rewrite (underNE (f @` [set x; y]) [set f x; f y]) // image_setU !image_set1.
Qed.
End Joet_morph.

Module JoetMorph.
Section ClassDef.
Local Open Scope classical_set_scope.
Variables (U V : semiCompSemiLattType).
Structure map (phUV : phant (U -> V)) :=
  Pack {apply : U -> V ; _ : Joet_morph apply}.
Local Coercion apply : map >-> Funclass.
Variables (phUV : phant (U -> V)) (f g : U -> V) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return Joet_morph cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.
End ClassDef.
Module Exports.
Coercion apply : map >-> Funclass.
Notation JoetMorph fA := (Pack (Phant _) fA).
Notation "{ 'Joet_morph' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'Joet_morph'  fUV }") : convex_scope.
Notation "[ 'Joet_morph' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'Joet_morph'  'of'  f  'as'  g ]") : convex_scope.
Notation "[ 'Joet_morph' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'Joet_morph'  'of'  f ]") : convex_scope.
End Exports.
End JoetMorph.
Export JoetMorph.Exports.

Module SemiCompSemiLattConvType.
Local Open Scope convex_scope.
Local Open Scope latt_scope.
Local Open Scope classical_set_scope.
Record mixin_of (L : semiCompSemiLattType) (op : L -> L -> prob -> L) := Mixin {
  _ : forall (p : prob) (x : L) (I : neset L), op x (Joet I) p = Joet `NE ((fun y => op x y p) @` I);
}.
Record class_of (T : choiceType) : Type := Class {
  base : SemiCompleteSemiLattice.class_of T ;
  base2 : ConvexSpace.class_of (SemiCompleteSemiLattice.Pack base) ;
  mixin : @mixin_of (SemiCompleteSemiLattice.Pack base) (@Conv (ConvexSpace.Pack base2)) ;
}.
Structure t : Type := Pack { sort : choiceType ; class : class_of sort }.
Definition baseType (T : t) : semiCompSemiLattType :=
  SemiCompleteSemiLattice.Pack (base (class T)).
Definition base2Type (T : t) : convType := ConvexSpace.Pack (base2 (class T)).
Module Exports.
Notation semiCompSemiLattConvType := t.
Coercion baseType : semiCompSemiLattConvType >-> semiCompSemiLattType.
Coercion base2Type : semiCompSemiLattConvType >-> convType.
Canonical baseType.
Canonical base2Type.
End Exports.
End SemiCompSemiLattConvType.
Export SemiCompSemiLattConvType.Exports.

Module JoetAffine.
Section ClassDef.
Local Open Scope classical_set_scope.
Variables (U V : semiCompSemiLattConvType).
Record class_of (f : U -> V) : Type := Class {
  _ : affine_function f ;
  _ : Joet_morph f ;
}.
Structure map (phUV : phant (U -> V)) :=
  Pack {apply : U -> V ; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.
Variables (phUV : phant (U -> V)) (f g : U -> V) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.
End ClassDef.
Module Exports.
Coercion apply : map >-> Funclass.
Notation JoetMorph fA := (Pack (Phant _) fA).
Notation "{ 'Joet_affine' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'Joet_affine'  fUV }") : convex_scope.
Notation "[ 'Joet_affine' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'Joet_affine'  'of'  f  'as'  g ]") : convex_scope.
Notation "[ 'Joet_affine' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'Joet_affine'  'of'  f ]") : convex_scope.
End Exports.
End JoetAffine.
Export JoetAffine.Exports.

Section semicompsemilattconvtype_lemmas.
Local Open Scope latt_scope.
Local Open Scope convex_scope.
Local Open Scope classical_set_scope.
Local Open Scope R_scope.

Variable L : semiCompSemiLattConvType.

Lemma JoetDr : forall (p : prob) (x : L) (Y : neset L),
    x <|p|> Joet Y = Joet `NE ((fun y => x <|p|> y) @` Y).
Proof. by case: L => ? [? ? []]. Qed.

Lemma JoetDl (p : prob) (X : neset L) (y : L) :
  Joet X <|p|> y = Joet `NE ((fun x => x <|p|> y) @` X).
Proof.
rewrite convC JoetDr.
congr Joet; apply/val_inj/eq_imagel=> x Xx.
by rewrite -convC.
Qed.
Lemma joetDr p : right_distributive (fun x y => x <|p|> y) (@joet L).
Proof.
move=> x y z.
rewrite JoetDr /=.
rewrite (underNE ((Conv x)^~ p @` [set y; z]) [set x <|p|> y; x <|p|> z]) //.
by rewrite image_setU !image_set1.
Qed.

Section convex_neset_lemmas.
(*
The three definitions below work more or less the same way,
although the lemmas are not sufficiently provided in classical_sets.v
to switch between these views.
Definition conv_pt_set (p : prob) (x : L) (Y : set L) :=
[set z | exists y, Y y /\ z = x <| p |> y].
Definition conv_pt_set (p : prob) (x : L) (Y : set L) :=
  \bigcup_(y in Y) [set x <| p |> y].
Definition conv_pt_set (p : prob) (x : L) (Y : set L) :=
  (fun y => x <| p |> y) @` Y.
*)
Definition conv_pt_set (p : prob) (x : L) (Y : set L) :=
  (fun y => x <| p |> y) @` Y.
Lemma conv_pt_setE p x Y :
  conv_pt_set p x Y = (fun y => x <| p |> y) @` Y.
Proof. reflexivity. Qed.
Definition conv_set (p : prob) (X Y : set L) :=
  \bigcup_(x in X) conv_pt_set p x Y.
Lemma conv_setE p X Y :
  conv_set p X Y = \bigcup_(x in X) conv_pt_set p x Y.
Proof. reflexivity. Qed.
Lemma conv_setC p X Y :
  conv_set p X Y = conv_set `Pr p.~ Y X.
Proof.
by apply eqEsubset=> u; case=> x Xx [] y Yy <-; exists y => //; exists x => //; rewrite -convC.
Qed.
Lemma conv_pt_set1 x (Y : neset L) : conv_pt_set `Pr 1 x Y = [set x].
Proof.
case: Y=> Y /= /set0P [] y Yy.
apply eqEsubset => u.
- by case=> y' Yy' <-; rewrite conv1.
- by move=> ->; exists y => //; rewrite conv1.
Qed.
Lemma conv_pt_set0 x (Y : set L) : conv_pt_set `Pr 0 x Y = Y.
Proof.
apply eqEsubset => u.
- by case=> y Yy <-; rewrite conv0.
- by move=> Yu; exists u=> //; rewrite conv0.
Qed.
Lemma conv_set1 X (Y : neset L) : conv_set `Pr 1 X Y = X.
Proof.
transitivity (\bigcup_(x in X) [set x]); last by rewrite bigcup_set1 image_idfun.
congr bigsetU; apply funext => x /=.
by rewrite (conv_pt_set1 x Y).
Qed.
Lemma conv_set0 (X : neset L) Y : conv_set `Pr 0 X Y = Y.
Proof.
rewrite conv_setC /= (_ : `Pr 0.~ = `Pr 1) ?conv_set1 //.
by apply prob_ext; rewrite /= onem0.
Qed.
Definition probset := @setT prob.
Definition natset := @setT nat.
Definition oplus_conv_set (X Y : set L) :=
  \bigcup_(p in probset) conv_set p X Y.
Fixpoint iter_conv_set (X : set L) (n : nat) :=
  match n with
  | O => X
  | S n' => oplus_conv_set X (iter_conv_set X n')
  end.
Lemma iter_conv_set0 (X : set L) : iter_conv_set X 0 = X.
Proof. reflexivity. Qed.
Lemma iter_conv_setS (X : set L) (n : nat) : iter_conv_set X (S n) = oplus_conv_set X (iter_conv_set X n).
Proof. reflexivity. Qed.
Lemma probset_neq0 : probset != set0.
Admitted.
Lemma natset_neq0 : natset != set0.
Admitted.
Lemma conv_pt_set_neq0 (p : prob) (x : L) (Y : neset L) : conv_pt_set p x Y != set0.
Admitted.
Lemma conv_set_neq0 (p : prob) (X Y : neset L) : conv_set p X Y != set0.
Admitted.
Lemma oplus_conv_set_neq0 (X Y : neset L) : oplus_conv_set X Y != set0.
Admitted.
Fixpoint iter_conv_set_neq0 (X : neset L) (n : nat) :
  iter_conv_set X n != set0 :=
  match n with
  | 0 => NESet.H X
  | S n' => oplus_conv_set_neq0 X (NESet.mk (iter_conv_set_neq0 X n'))
  end.
Global Canonical probset_neset := NESet.mk probset_neq0.
Global Canonical natset_neset := NESet.mk natset_neq0.
Global Canonical conv_pt_set_neset (p : prob) (x : L) (Y : neset L) :=
  NESet.mk (conv_pt_set_neq0 p x Y).
Global Canonical conv_set_neset (p : prob) (X Y : neset L) :=
  NESet.mk (conv_set_neq0 p X Y).
Global Canonical oplus_conv_set_neset (X Y : neset L) :=
  NESet.mk (oplus_conv_set_neq0 X Y).
Global Canonical iter_conv_set_neset (X : neset L) (n : nat) :=
  NESet.mk (iter_conv_set_neq0 X n).

Lemma iter_conv_set_superset (X : neset L) n : X `<=` iter_conv_set X n .
Proof.
move=> x Xx.
elim:n => // n IHn; rewrite iter_conv_setS.
exists `Pr 1 => //.
by rewrite conv_set1.
Qed.

Lemma Convn_iter_conv_set (n : nat) :
  forall (g : 'I_n -> L) (d : {dist 'I_n}) (X : set L),
    g @` setT `<=` X -> iter_conv_set X n (\Conv_d g).
Proof.
elim: n; first by move=> g d; move: (distI0_False d).
move=> n IHn g d X.
case/boolP: (X == set0);
  first by move/eqP => -> /(_ (g ord0)) H; apply False_ind; apply/H/imageP.
move=> Xneq0 gX; set X' := (NESet.mk Xneq0).
have gXi : forall i : 'I_n.+1, X (g i) by move=> i; apply/gX/imageP.
case/boolP: (d ord0 == 1).
- move/eqP=> d01.
  suff : X (\Conv_d g) by move/(@iter_conv_set_superset X' n.+1 (\Conv_d g)).
  rewrite (convn_proj g d01).
  by apply/gX/imageP.
- move=> d0n1; rewrite convnE //.
  exists (probdist d ord0) => //.
  exists (g ord0) => //.
  exists (\Conv_(DelDist.d d0n1) (fun x : 'I_n => g (DelDist.h ord0 x))) => //.
  apply IHn.
  move=> u [] i _ <-.
  by apply/gX/imageP.
Qed.
Lemma conv_pt_set_monotone (p : prob) (x : L) (Y Y' : set L) :
  Y `<=` Y' -> conv_pt_set p x Y `<=` conv_pt_set p x Y'.
Proof. by move=> YY' u [] y /YY' Y'y <-; exists y. Qed.
Lemma conv_set_monotone (p : prob) (X Y Y' : set L) :
  Y `<=` Y' -> conv_set p X Y `<=` conv_set p X Y'.
Proof. by move/conv_pt_set_monotone=> YY' u [] x Xx /YY' HY'; exists x. Qed.
Lemma oplus_conv_set_monotone (X Y Y' : set L) :
  Y `<=` Y' -> oplus_conv_set X Y `<=` oplus_conv_set X Y'.
Proof. by move/conv_set_monotone=> YY' u [] p _ /YY' HY'; exists p. Qed.
Lemma oplus_conv_setC (X Y : set L) :
  oplus_conv_set X Y = oplus_conv_set Y X.
Proof.
suff H : forall X' Y', oplus_conv_set X' Y' `<=` oplus_conv_set Y' X'
    by apply/eqEsubset/H.
move=> {X} {Y} X Y u [] p _.
rewrite conv_setC => H.
by exists (`Pr p.~) => //.
Qed.
Lemma conv_setmm (p : prob) (X : {convex_set L}) : conv_set p X X = X.
Proof.
apply eqEsubset=> x.
- case: X=> X /= /asboolP H.
  case => x0 Xx0 [] x1 Xx1 <-.
  by rewrite -in_setE; apply H; rewrite in_setE.
- by move=> Xx; exists x=> //; exists x=> //; rewrite convmm.
Qed.
Lemma oplus_conv_setmm (X : {convex_set L}) : oplus_conv_set X X = X.
Proof.
apply eqEsubset => x.
- case=> p _.
  by rewrite conv_setmm.
- move=> Xx.
  exists `Pr 0 => //.
  by rewrite conv_setmm.
Qed.
Lemma oplus_conv_set_hullmm (X : set L) :
  oplus_conv_set (hull X) (hull X) = hull X.
Proof. by rewrite (oplus_conv_setmm (CSet.mk (convex_hull X))). Qed.
Lemma hull_iter_conv_set (X : set L) : hull X = \bigcup_(i in natset) iter_conv_set X i.
Proof.
apply eqEsubset; first by move=> x [] n [] g [] d [] gX ->; exists n => //; apply Convn_iter_conv_set.
apply bigsubsetU.
elim; first by move=> _ /=; move: X; apply hull_mem'.
move=> n IHn _.
have H : iter_conv_set X n.+1 `<=` oplus_conv_set X (hull X) 
  by apply/oplus_conv_set_monotone/IHn.
apply (subset_trans H).
rewrite oplus_conv_setC.
have H' : oplus_conv_set (hull X) X `<=` oplus_conv_set (hull X) (hull X)
  by apply/oplus_conv_set_monotone/hull_mem'.
apply (subset_trans H').
by rewrite oplus_conv_set_hullmm.
Qed.
End convex_neset_lemmas.

Lemma Joet_conv_pt_setE p x (Y : neset L) :
  Joet `NE (conv_pt_set p x Y) = Joet `NE ((Conv x)^~ p @` Y).
Proof.
by rewrite (underNE (conv_pt_set p x Y) ((fun y => x <|p|> y) @` Y)) //.
Qed.
Lemma Joet_conv_pt_setD p x (Y : neset L) :
  Joet `NE (conv_pt_set p x Y) = x <|p|> Joet Y.
Proof. by rewrite Joet_conv_pt_setE -JoetDr. Qed.
Lemma Joet_conv_setE p (X Y : neset L) :
  Joet `NE (conv_set p X Y) =
  Joet `NE ((fun x => x <|p|> Joet Y) @` X).
Proof.
rewrite (underNE (conv_set p X Y)
                 (\bigcup_(x in X) conv_pt_set p x Y)) // Joet_bigcup.
rewrite (underNE (Joet @` ((conv_pt_set_neset p)^~ Y @` X))
                 ((fun x => x <|p|> Joet Y) @` X)) //.
rewrite imageA.
congr image.
apply funext=> x /=.
by rewrite Joet_conv_pt_setD.
Qed.
Lemma Joet_conv_setD p (X Y : neset L) :
  Joet `NE (conv_set p X Y) = Joet X <|p|> Joet Y.
Proof. by rewrite Joet_conv_setE JoetDl. Qed.
Lemma Joet_oplus_conv_setE (X Y : neset L) :
  Joet `NE (oplus_conv_set X Y) =
  Joet `NE ((fun p => Joet X <|p|> Joet Y) @` probset).
Proof.
rewrite (underNE (oplus_conv_set X Y)
                 (\bigcup_(p in probset) conv_set p X Y)) // Joet_bigcup.
rewrite (underNE (Joet @` ((fun i => `NE (conv_set i X Y)) @` probset))
                 ((fun p => Joet X <|p|> Joet Y) @` probset)) //.
rewrite imageA.
congr image.
apply funext=> p /=.
by rewrite Joet_conv_setD.
Qed.
Lemma Joet_iter_conv_set (X : neset L) (n : nat) :
  Joet `NE (iter_conv_set X n) = Joet X.
Proof.
elim: n; first by congr Joet; apply val_inj.
move=> n IHn /=.
rewrite Joet_oplus_conv_setE.
rewrite (underNE
           ((fun p => Joet X <|p|> Joet (iter_conv_set_neset X n)) @` probset)
           [set Joet X]) ?Joet1 //=.
transitivity ((fun _ => Joet X) @` probset);
  last by rewrite image_const.
by congr image; apply funext=> p; rewrite IHn convmm.
Qed.

Lemma Joet_hull (X : neset L) : Joet `NE (hull X) = Joet X.
Proof.
transitivity (Joet `NE (\bigcup_(i in natset) iter_conv_set X i));
  first by congr Joet; apply val_inj; rewrite /= hull_iter_conv_set.
rewrite Joet_bigsetU /=.
rewrite -[in RHS](Joet1 (Joet X)).
rewrite (underNE (Joet @` (iter_conv_set_neset X @` natset))
                 ((fun _ => Joet X) @` natset));
  first by congr Joet; apply/val_inj/image_const.
rewrite imageA; congr image; apply funext=> n /=.
by rewrite Joet_iter_conv_set.
Qed.
End semicompsemilattconvtype_lemmas.

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
split; first by move/asboolP: (CSet.H X); apply.
by split; first by move/asboolP: (CSet.H Y); apply.
Qed.
Definition pre_conv X Y p : convex_set A :=
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
rewrite /conv; unlock; do 2 apply val_inj => /=.
apply/eqEsubset => a;
  first by case => x [] y [] xX [] yY ->; rewrite -in_setE conv1.
case/set0P: (NECSet.H Y) => y; rewrite -in_setE => yY.
rewrite -in_setE => aX.
by exists a, y; rewrite conv1.
Qed.
Lemma convmm X p : conv X X p = X.
Proof.
rewrite/conv; unlock; do 2 apply val_inj => /=; apply eqEsubset => a.
- case => x [] y [] xX [] yY ->.
  by rewrite -in_setE; move/asboolP: (CSet.H X); apply => //.
- rewrite -in_setE => aX.
  by exists a, a; rewrite convmm.
Qed.
Lemma convC X Y p : conv X Y p = conv Y X `Pr p.~.
Proof.
by rewrite/conv; unlock; do 2 apply val_inj => /=; apply eqEsubset => a; case => x [] y [] xX [] yY ->; exists y, x; [rewrite convC | rewrite -convC].
Qed.
Lemma convA p q X Y Z :
  conv X (conv Y Z q) p = conv (conv X Y [r_of p, q]) Z [s_of p, q].
Proof.
rewrite/conv; unlock; do 2 apply val_inj => /=; apply eqEsubset => a; case => x [].
- move=> y [] xX [].
  rewrite in_setE => -[] y0 [] z0 [] y0Y [] z0Z -> ->.
  exists (x <| [r_of p, q] |> y0), z0.
  by rewrite inE asboolE /= convA; split; try exists x, y0.
- move=> z []; rewrite in_setE => -[] x0 [] y [] x0X [] yY -> [] zZ ->.
  exists x0, (y <| q |> z).
  split => //.
  by rewrite inE asboolE /= -convA; split; try exists y, z.
Qed.
Definition mixin : ConvexSpace.class_of [choiceType of necset A]
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
Canonical necset_convType A := ConvexSpace.Pack (necset_convType.mixin A).

Module necset_semiCompSemiLattType.
Section def.
Local Open Scope classical_set_scope.
Variable (A : convType).
Definition pre_op (X : neset (necset A)) : convex_set A
  := CSet.mk (convex_hull `NE (bigsetU X idfun)).
Lemma pre_op_neq0 X : pre_op X != cset0 A.
Proof. rewrite cset0P hull_eq0; exact: NESet.H. Qed.
Definition op X := NECSet.mk (pre_op_neq0 X).
Lemma op1 x : op `NE [set x] = x.
Proof. by do 2 apply val_inj => /=; rewrite bigcup1 hull_cset. Qed.
Lemma op_bigsetU (I : Type) (S : neset I) (F : I -> neset (necset A)) :
    op (bignesetU S F) = op `NE (op @` (F @` S)).
Proof.
do 2 apply val_inj => /=.
apply hull_eqEsubset => a.
- case => x [] i Si Fix xa.
  exists 1, (fun _ => a), (proba.Dist1.d ord0).
  split; last by rewrite convn1E.
  move=> a0 [] zero _ <-.
  exists (op (F i)); first by  do 2 apply imageP.
  by rewrite -in_setE hull_mem // in_setE /=; exists x.
- case => x [] u [] i Si Fiu <-.
  case => n [] g [] d [] /= gx ag.
  exists n, g, d; split => //.
  apply (subset_trans gx).
  move => a0 [] x0 ux0 x0a0.
  exists x0 => //.
  exists i => //.
  by rewrite Fiu.
Qed.
Definition mixin := SemiCompleteSemiLattice.Class op1 op_bigsetU.
End def.
End necset_semiCompSemiLattType.
Canonical necset_semiCompSemiLattType A := SemiCompleteSemiLattice.Pack (necset_semiCompSemiLattType.mixin A).

Module necset_semiCompSemiLattConvType.
Section def.
Local Open Scope classical_set_scope.
Variable (A : convType).
Let L := necset_semiCompSemiLattType A.
Lemma axiom : forall (p : prob) (x : L) (I : neset L),
    (necset_convType.conv x (Joet I) p) =
    Joet `NE ((fun y => necset_convType.conv x y p) @` I).
Proof.
Admitted.
Definition mixin := @SemiCompSemiLattConvType.Class [choiceType of necset A] (necset_semiCompSemiLattType.mixin A) (necset_convType.mixin A) (SemiCompSemiLattConvType.Mixin axiom).
End def.
End necset_semiCompSemiLattConvType.
Canonical necset_semiCompSemiLattConvType A := SemiCompSemiLattConvType.Pack (necset_semiCompSemiLattConvType.mixin A).

(*
  eps0 is the counit of the adjunction (Dist -| coercion) and it is just Convn
  (* p.164 *).
*)
Section eps0.
Definition eps0' : forall {C : convType}, Dist C -> C
  := fun C d => Convn_indexed_over_finType
                  (dist_of_Dist d)
                  (fun x : finsupp d => (fsval x)).

Import ScaledConvex.
Local Open Scope fset_scope.
Local Open Scope R_scope.
Lemma eps0'_affine  (C : convType) : affine_function (@eps0' C).
Proof.
move => x y p.
rewrite /affine_function_at.
case/boolP: (p == `Pr 0); first by move/eqP ->; rewrite !conv0.
move=> pn0.
case/boolP: (p == `Pr 1); first by move/eqP ->; rewrite !conv1.
move=> pn1.
move: (pn1) => /onem_neq0 opn0.
apply S1_inj.
rewrite S1_conv.
rewrite !S1_Convn_indexed_over_finType.
transitivity (\big[addpt (A:=C)/Zero C]_(i : dist_of_Dist.D (x <|p|> y))
               scalept ((x <|p|> y) (fsval i)) (S1 (fsval i)));
  first by apply eq_bigr => i; rewrite dist_of_DistE.
rewrite -(@big_seq_fsetE
            _ _ _ _ _ xpredT
            (fun i => scalept ((x <|p|> y) i) (S1 i))
         ) /=.
transitivity (\big[addpt (A:=C)/Zero C]_(i <- finsupp (x <|p|> y))
               ((scalept (x i) (S1 i) : Scaled_convType C) <|p|> scalept (y i) (S1 i))); first by apply eq_bigr => i _; rewrite Dist_scalept_conv.
rewrite big_seq_fsetE big_scalept_conv_split /=.
rewrite -(@big_seq_fsetE _ _ _ _ _ xpredT (fun i => scalept (x i) (S1 i))).
rewrite -(@big_seq_fsetE _ _ _ _ _ xpredT (fun i => scalept (y i) (S1 i))) /=.
have -> : \big[addpt (A:=C)/Zero C]_i scalept (dist_of_Dist x i) (S1 (fsval i))
          = \big[addpt (A:=C)/Zero C]_(i <- finsupp x) scalept (x i) (S1 i)
  by rewrite big_seq_fsetE /=; apply eq_bigr => i _; rewrite dist_of_DistE.
have -> : \big[addpt (A:=C)/Zero C]_i scalept (dist_of_Dist y i) (S1 (fsval i))
          = \big[addpt (A:=C)/Zero C]_(i <- finsupp y) scalept (y i) (S1 i)
  by rewrite big_seq_fsetE /=; apply eq_bigr => i _; rewrite dist_of_DistE.
have -> : \big[addpt (A:=C)/Zero C]_(i <- finsupp x) scalept (x i) (S1 i)
          = \big[addpt (A:=C)/Zero C]_(i <- finsupp (x <|p|> y)) scalept (x i) (S1 i).
- rewrite [in RHS](bigID (fun i => i \in (finsupp x))) /=.
  have -> : (\big[addpt (A:=C)/Zero C]_(i <- finsupp (x <|p|> y) | 
     i \notin finsupp x) scalept (x i) (S1 i)) = Zero C
    by rewrite big1 //= => i Hi; rewrite fsfun_dflt // scalept0.
  rewrite addpt0 [in RHS]big_fset_condE /=.
  suff H : finsupp x = [fset i | i in finsupp (x <|p|> y) & i \in finsupp x]
    by rewrite [in LHS]H.
  + have -> : [fset i | i in finsupp (x <|p|> y) & i \in finsupp x]
              = [fset i | i in finsupp x & i \in finsupp (x <|p|> y)]
      by apply eq_imfset => //; move => i /=; rewrite !inE andbC.
    apply/eqP; rewrite eqEfsubset; apply/andP; split; last by apply fset_sub.
    apply/fsubsetP => i Hi.
    move/fsubsetP: (Conv2Dist.incl_finsupp_conv2dist x y pn0).
    move/(_ i Hi) => Hi'.
    by rewrite !inE Hi Hi'.
have -> : \big[addpt (A:=C)/Zero C]_(i <- finsupp y) scalept (y i) (S1 i)
          = \big[addpt (A:=C)/Zero C]_(i <- finsupp (x <|p|> y)) scalept (y i) (S1 i).
- rewrite [in RHS](bigID (fun i => i \in (finsupp y))) /=.
  have -> : (\big[addpt (A:=C)/Zero C]_(i <- finsupp (x <|p|> y) | 
     i \notin finsupp y) scalept (y i) (S1 i)) = Zero C
    by rewrite big1 //= => i Hi; rewrite fsfun_dflt // scalept0.
  rewrite addpt0 [in RHS]big_fset_condE /=.
  suff H : finsupp y = [fset i | i in finsupp (x <|p|> y) & i \in finsupp y]
    by rewrite [in LHS]H.
  + have -> : [fset i | i in finsupp (x <|p|> y) & i \in finsupp y]
              = [fset i | i in finsupp y & i \in finsupp (x <|p|> y)]
      by apply eq_imfset => //; move => i /=; rewrite !inE andbC.
    apply/eqP; rewrite eqEfsubset; apply/andP; split; last by apply fset_sub.
    apply/fsubsetP => i Hi.
    move/fsubsetP: (Conv2Dist.incl_finsupp_conv2dist y x pn0).
    have Conv2Dist_supp : forall x0 y0 : Dist C, finsupp (x0 <|p|> y0) = finsupp x0 `|` finsupp y0.
    * (* TODO: factor this out as a lemma *)
      move=> x0 y0.
      apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP => j; rewrite !mem_finsupp !Conv2Dist.dE inE; first by move=> H; (have []: (x0 j != 0) \/ (y0 j != 0) by apply/nandP/negP; case/andP => /eqP H0 /eqP H1; move:H; rewrite H0 H1 !mulR0 addR0 eqxx) => H'; rewrite !mem_finsupp H' ?orTb ?orbT.
      have pge0 : 0 <= p by apply prob_ge0.
      move/prob_gt0: (pn0) => pgt0.
      have opge0 : 0 <= p.~ by apply prob_ge0.
      move/prob_gt0: (opn0) => /= opgt0.
      move/leRP : (Dist.ge0 x0 j) => xgeb0.
      move/leRP : (Dist.ge0 y0 j) => ygeb0.
      move: (Dist.ge0 x0 j) => xge0.
      move: (Dist.ge0 y0 j) => yge0.
      by case /orP; rewrite mem_finsupp => H; apply/eqP; apply gtR_eqF;
      [apply addR_gt0wl; [apply mulR_gt0|apply mulR_ge0] | apply addR_gt0wr; [apply mulR_ge0|apply mulR_gt0]] => //; apply /ltRP; rewrite ltR_neqAle'; apply/andP; split => //; rewrite eq_sym.
    have -> : finsupp (y <|p|> x) = finsupp (x <|p|> y)
        by rewrite !Conv2Dist_supp fsetUC.
    move/(_ i Hi) => Hi'.
    by rewrite !inE Hi Hi'.
done.  
Qed.

Definition eps0 (C : convType) : {affine Dist C -> C} := @AffineFunction.Pack (Dist_convType C) C (Phant (Dist C -> C)) (@eps0' C) (@eps0'_affine C).
End eps0.

Arguments eps0 [C].

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
exact/val_inj.
Qed.
End eps0_natural.

(*
  eps1 is the counit of the adjunction (necset -| coercion),
  where the coercion is from semiCompSemiLattConvType to convType.
*)
Section eps1.
Local Open Scope classical_set_scope.
Variable L : semiCompSemiLattConvType.

Definition eps1' (X : necset_semiCompSemiLattConvType L) : L := Joet `NE X.

Lemma eps1'_Joet_morph : Joet_morph eps1'.
Proof.
move=> F.
rewrite /eps1'.
transitivity (Joet `NE (Joet @` ((fun X : necset_semiCompSemiLattType L => `NE X) @` F))); last first.
- congr Joet.
  apply/val_inj/eqEsubset => x [] x0 Fx0 <-.
  + by case: Fx0 => x1 Fx1 <-; exists x1.
  + by exists `NE x0 => // ; exists x0.
transitivity (Joet `NE (hull (\bigcup_(x in F) x)));
  first by congr Joet; apply val_inj.
by rewrite Joet_hull Joet_bigcup.
Qed.

Lemma eps1'_affine : affine_function eps1'.
Proof.
move=> X Y p.
rewrite /affine_function_at /eps1'.
rewrite (underNE (X <|p|> Y) (conv_set p X Y)) ?Joet_conv_setD //.
rewrite conv_setE /Conv /= /necset_convType.conv /=; unlock => /=.
rewrite /necset_convType.pre_pre_conv.
apply eqEsubset=> u.
- case=> x [] y [] xX [] yY ->.
  exists x; first by rewrite -in_setE.
  by exists y; first by rewrite -in_setE.
- case=> x Xx [] y Yy <-.
  by exists x, y; rewrite !in_setE.
Qed.

Definition eps1 : {Joet_affine necset_semiCompSemiLattConvType L -> L} :=
  JoetAffine.Pack (Phant (necset_semiCompSemiLattConvType L -> L))
                  (JoetAffine.Class eps1'_affine eps1'_Joet_morph).
End eps1.
Arguments eps1 [L].

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

Lemma necset_mor_Joet_morph (A B : convType) (f : {affine A -> B}) : 
  Joet_morph (necset_mor f).
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
