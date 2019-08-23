Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype finfun bigop.
Require Import Reals_ext Rbigop ssrR proba dist convex_choice.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import finmap.

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

Section misc_fset.
Local Open Scope fset_scope.
Lemma bigfcup_fset1 (T I : choiceType) (P : {fset I}) (f : I -> T) :
  \bigcup_(x <- P) [fset f x] = f @` P.
Proof.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP=> x.
- case/bigfcupP=> i /andP [] iP _.
  rewrite inE => /eqP ->.
  by apply/imfsetP; exists i.
- case/imfsetP => i /= iP ->; apply/bigfcupP; exists i; rewrite ?andbT //.
  by apply/imfsetP; exists (f i); rewrite ?inE.
Qed.
Lemma set1_inj (C : choiceType) : injective (@set1 C).
Proof. by move=> a b; rewrite /set1 => /(congr1 (fun f => f a)) <-. Qed.
End misc_fset.

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
Lemma image_subset (A B : Type) (f : A -> B) (X : set A) (Y : set B) :
  f @` X `<=` Y <-> forall a, X a -> Y (f a).
Proof.
split=> H.
- by move=> a Xa; apply/H/imageP.
- by move=> b [] a Xa <-; apply H.
Qed.
Lemma fullimage_subset (A B : Type) (f : A -> B) (Y : set B) :
  f @` setT `<=` Y <-> forall a, Y (f a).
Proof.
rewrite (_ : (forall a, Y (f a)) <-> (forall a, setT a -> Y (f a))) ?image_subset //.
by firstorder.
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

Lemma bigcup_set0P (A I : Type) (S : set I) (F : I -> set A) :
  reflect (exists i, S i /\ F i !=set0) (bigsetU S F != set0).
Proof.
apply: (iffP idP).
- by case/set0P => a [] i Si Fia; exists i; split; [ | exists a].
- by case=> i [] Si [] a Fia; apply/set0P; exists a, i.
Qed.

Lemma is_convex_set_image (A B : convType) (f : {affine A -> B})
  (a : convex_set A) : is_convex_set (f @` a).
Proof.
rewrite /is_convex_set.
apply/asboolP => x y p; rewrite 3!in_setE => -[a0 Ha0 <-{x}] [a1 Ha1 <-{y}].
exists (a0 <|p|> a1) => //.
by rewrite -in_setE; apply/mem_convex_set; rewrite in_setE.
by rewrite (affine_functionP' f).
Qed.

Lemma is_convex_set_image' (A B : convType) (f : A -> B) (H : affine_function f)
  (a : convex_set A) : is_convex_set (f @` a).
Proof.
rewrite /is_convex_set.
apply/asboolP => x y p; rewrite 3!in_setE => -[a0 Ha0 <-{x}] [a1 Ha1 <-{y}].
exists (a0 <|p|> a1) => //.
by rewrite -in_setE; apply/mem_convex_set; rewrite in_setE.
by rewrite H.
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

Lemma add_prob_eq0 (p q : prob) : p + q = `Pr 0 <-> p = `Pr 0 /\ q = `Pr 0.
Proof.
split => [/paddR_eq0 | ].
- move=> /(_ (prob_ge0 _) (prob_ge0 _)) [p0 q0]; split; exact/prob_ext.
- by case => -> ->; rewrite addR0.
Qed.

Lemma add_prob_neq0 (p q : prob) : p + q != `Pr 0 <-> p != `Pr 0 \/ q != `Pr 0.
Proof.
split => [/paddR_neq0 | ].
- by move=> /(_ (prob_ge0 _) (prob_ge0 _)).
- by case; apply: contra => /eqP/add_prob_eq0 [] /eqP ? /eqP.
Qed.

End misc_prob.

Lemma finsupp_Conv2 (C : convType) p (p0 : p != `Pr 0) (p1 : p != `Pr 1) (d e : Dist C) :
  finsupp (d <|p|> e) = (finsupp d `|` finsupp e)%fset.
Proof.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP => j;
  rewrite !mem_finsupp !Conv2Dist.dE inE; first by (move=> H ;
    rewrite 2!mem_finsupp; apply/orP/(paddR_neq0 (Dist.ge0 _ _) (Dist.ge0 _ _));
    apply: contra H => /eqP/paddR_eq0 => /(_ (Dist.ge0 _ _ ))/(_ (Dist.ge0 _ _)) [-> ->];
    rewrite 2!mulR0 addR0).
have [pge0 opge0] := (prob_ge0 p, prob_ge0 (`Pr p.~)).
move/prob_gt0 in p0.
move: p1 => /onem_neq0 /prob_gt0 /= p1.
have [/leRP dgeb0 /leRP egeb0] := (Dist.ge0 d j, Dist.ge0 e j).
have [xge0 yge0] := (Dist.ge0 d j, Dist.ge0 e j).
rewrite 2!mem_finsupp => /orP[dj0|ej0]; apply/eqP/gtR_eqF;
  [apply/addR_gt0wl; last exact/mulR_ge0;
   apply/mulR_gt0 => //; apply/ltR_neqAle; split => //; exact/nesym/eqP |
   apply/addR_gt0wr; first exact/mulR_ge0;
   apply/mulR_gt0 => //; apply/ltR_neqAle; split => //; exact/nesym/eqP].
Qed.

Lemma Dist_eval_affine (C : choiceType) (x : C) :
  affine_function (fun D : Dist C => D x).
Proof. by move=> a b p; rewrite /affine_function_at Conv2Dist.dE. Qed.

Section misc_hull.
Implicit Types A B : convType.
Local Open Scope classical_set_scope.

Lemma hull_mem' A (X : set A) : X `<=` hull X.
Proof. by move=> x; rewrite -in_setE; move/hull_mem; rewrite in_setE. Qed.

Lemma hull_monotone A (X Y : set A) :
  (X `<=` Y)%classic -> (hull X `<=` hull Y)%classic.
Proof.
move=> H a.
case => n [g [d [H0 H1]]].
exists n, g, d.
split => //.
by eapply subset_trans; first by exact: H0.
Qed.

Lemma hull_eqEsubset A (X Y : set A) :
  (X `<=` hull Y)%classic -> (Y `<=` hull X)%classic -> hull X = hull Y.
Proof.
move/hull_monotone; rewrite hullI => H.
move/hull_monotone; rewrite hullI => H0.
by apply/eqEsubset.
Qed.

(* hull (X `|` hull Y) = hull (hull (X `|` Y)) = hull (x `|` y);
   the first equality looks like a tensorial strength under hull
   Todo : Check why this is so. *)
Lemma hullU_strr A (X Y : set A) : hull (X `|` hull Y) = hull (X `|` Y).
Proof.
apply/hull_eqEsubset => a.
- case; first by rewrite -in_setE => H; rewrite -in_setE; apply mem_hull_setU_left.
  case=> n [d [g [H0 H1]]].
  exists n, d, g; split => //.
  apply (subset_trans H0) => b Hb.
  by right.
- by case; rewrite -in_setE => H; rewrite -in_setE; [ | rewrite setUC] ; apply mem_hull_setU_left => //; apply hull_mem.
Qed.

Lemma hullU_strl A (X Y : set A) : hull (hull X `|` Y) = hull (X `|` Y).
Proof. by rewrite [in LHS]setUC [in RHS]setUC hullU_strr. Qed.

Lemma hullUA A (X Y Z : {convex_set A}) :
  hull (X `|` hull (Y `|` Z)) = hull (hull (X `|` Y) `|` Z).
Proof. by rewrite hullU_strr hullU_strl setUA. Qed.

Lemma image_preserves_convex_hull A B (f : {affine A -> B}) (Z : set A) :
  image f (hull Z) = hull (f @` Z).
Proof.
rewrite predeqE => b; split.
  case=> a [n [g [e [Hg]]]] ->{a} <-{b}.
  exists n, (f \o g), e; split.
    move=> b /= [i _] <-{b} /=.
    by exists (g i) => //; apply Hg; exists i.
  by rewrite affine_function_Sum.
case=> n [g [e [Hg]]] ->{b}.
suff [h Hh] : exists h : 'I_n -> A, forall i, h i \in Z /\ f (h i) = g i.
  exists (\Conv_e h).
    exists n; exists h; exists e; split => //.
    move=> a [i _] <-.
    move: (Hh i) => [].
    by rewrite in_setE.
  rewrite affine_function_Sum; apply eq_convn => // i /=.
  by case: (Hh i).
apply (@fin_all_exists _ _ (fun i hi => hi \in Z /\ f hi = g i)) => i.
case: (Hg (g i)); first by exists i.
move=> a // HZa Hfa.
exists a; split; by rewrite // in_setE.
Qed.

Lemma image_preserves_convex_hull' A B (f : A -> B) (Hf : affine_function f) (Z : set A) :
  image f (hull Z) = hull (f @` Z).
Proof. by rewrite (image_preserves_convex_hull (AffineFunction Hf)). Qed.
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
 (F G : I -> Scaled_convType C) (p : prob) :
  \ssum_(i <- r | P i) (F i <|p|> G i) =
  ((\ssum_(i <- r | P i) F i) : Scaled_convType C) <|p|> \ssum_(i <- r | P i) G i.
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
    scalept (\sum_(i <- r | P i) F i) x = \ssum_(i <- r | P i) scalept (F i) x.
Proof.
move=> H I r P F H'.
transitivity (\ssum_(i <- r | P i) (fun r0 : Rnneg => scalept r0 x) (mkRnneg (H' i))); last by reflexivity.
rewrite -big_scaleptl ?scalept0 //.
congr scalept.
transitivity (\sum_(i <- r | P i) mkRnneg (H' i)); first by reflexivity.
apply (big_ind2 (fun x y => x = (Rnneg.v y))) => //.
by move=> x1 [v Hv] y1 y2 -> ->.
Qed.
End misc_scaled.
End misc.

Module Convn_indexed_over_finType.
Section def.
Local Open Scope R_scope.
Variables (A : convType) (T : finType) (d : {dist T}) (f : T -> A).
Let n := #| T |.
Definition t0 : T.
Proof.
move/card_gt0P/xchoose: (dist_domain_not_empty d) => t0; exact t0.
Defined.
Let enum : 'I_n -> T := enum_val.
Definition d_enum := [ffun i => d (enum i)].
Lemma d_enum0 : forall b, 0 <= d_enum b.
Proof. move=> ?; rewrite ffunE; exact: dist_ge0. Qed.
Lemma d_enum1 : \sum_(b in 'I_n) d_enum b = 1.
Proof.
rewrite -(@epmf1 T d) (eq_bigr (d \o enum)); last by move=> i _; rewrite ffunE.
rewrite (@reindex _ _ _ _ _ enum_rank) //; last first.
  by exists enum_val => i; [rewrite enum_rankK | rewrite enum_valK].
apply eq_bigr => i _; congr (d _); by rewrite -[in RHS](enum_rankK i).
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
  S1 (Convn_indexed_over_finType d f) = \ssum_i scalept (d i) (S1 (f i)).
Proof.
rewrite /Convn_indexed_over_finType S1_convn /=.
rewrite (reindex_onto enum_rank enum_val) /=; last by move=> i _; rewrite enum_valK.
apply eq_big => /=; first by move=> i; rewrite enum_rankK eqxx.
move=> i _; rewrite /Convn_indexed_over_finType.d_enum ffunE.
by rewrite enum_rankK.
Qed.
End S1_Convn_indexed_over_finType.

Section S1_proj_Convn_indexed_over_finType.
Import ScaledConvex.
Variables (A B : convType) (prj : A -> B).
Hypothesis prj_affine : affine_function prj.
Variables (T : finType) (d : {dist T}) (f : T -> A).

Lemma S1_proj_Convn_indexed_over_finType :
  S1 (prj (Convn_indexed_over_finType d f)) =
  \ssum_i scalept (d i) (S1 (prj (f i))).
Proof.
set (prj' := AffineFunction.Pack (Phant (A -> B)) prj_affine).
move: (affine_function_Sum prj') => /= ->.
exact: S1_Convn_indexed_over_finType.
Qed.
End S1_proj_Convn_indexed_over_finType.

(* TODO: move to top of the file when deemed useful *)
Reserved Notation "'`NE' s" (format "'`NE'  s", at level 6).

Module NESet.
Section neset.
Local Open Scope classical_set_scope.
Variable A : Type.
Record class_of (X : set A) : Type := Class { _ : X != set0 }.
Record t : Type := Pack { car : set A ; class : class_of car }.
End neset.
Module Exports.
Notation neset := t.
Coercion car : neset >-> set.
Notation "'`NE' s" := (@Pack _ s (class _)).
End Exports.
End NESet.
Export NESet.Exports.

Section neset_canonical.
Variable A : Type.
Canonical neset_predType :=
  Eval hnf in mkPredType (fun t : neset A => (fun x => x \in (t : set _))).
Canonical neset_eqType := Equality.Pack (equality_mixin_of_Type (neset A)).
Canonical neset_choiceType := choice_of_Type (neset A).
End neset_canonical.

Section NESet_interface.
Variables (A : Type).
Lemma neset_neq0 (a : neset A) : a != set0 :> set _.
Proof. by case: a => [? []]. Qed.
Lemma neset_ext (a b : neset A) : a = b :> set _ -> a = b.
Proof.
move: a b => -[a Ha] -[b Hb] /= ?; subst a.
congr NESet.Pack; exact/Prop_irrelevance.
Qed.
End NESet_interface.

Section neset_lemmas.
Local Open Scope classical_set_scope.

Lemma set1_neq0 A (a : A) : [set a] != set0.
Proof. by apply/set0P; exists a. Qed.

Definition neset_repr A (X : neset A) : A.
Proof.
case: X => X [] /set0P /boolp.constructive_indefinite_description [x _]; exact x.
Defined.
Lemma repr_in_neset A (X : neset A) : (X : set A) (neset_repr X).
Proof. by case: X => X [] X0 /=; case: cid. Qed.
Global Opaque neset_repr.
Local Hint Resolve repr_in_neset.

Lemma image_const A B (X : neset A) (b : B) :
  (fun _ => b) @` X = [set b].
Proof. apply eqEsubset=> b'; [by case => ? _ -> | by move=> ?; eexists]. Qed.

Lemma neset_bigsetU_neq0 A B (X : neset A) (F : A -> neset B) : bigsetU X F != set0.
Proof. by apply/bigcup_set0P; eexists; split => //; eexists. Qed.

Lemma neset_image_neq0 A B (f : A -> B) (X : neset A) : f @` X != set0.
Proof. apply/set0P; eexists; exact/imageP. Qed.

Lemma neset_setU_neq0 A (X Y : neset A) : X `|` Y != set0.
Proof. by apply/set0P; eexists; left. Qed.

Canonical neset1 {A} (x : A) := NESet.Pack (NESet.Class (set1_neq0 x)).
Canonical bignesetU {A} I (S : neset I) (F : I -> neset A) :=
  NESet.Pack (NESet.Class (neset_bigsetU_neq0 S F)).
Canonical image_neset {A B} (f : A -> B) (X : neset A) :=
  NESet.Pack (NESet.Class (neset_image_neq0 f X)).
Canonical nesetU {T} (X Y : neset T) :=
  NESet.Pack (NESet.Class (neset_setU_neq0 X Y)).

Lemma neset_hull_neq0 (T : convType) (F : neset T) : hull F != set0.
Proof. by rewrite hull_eq0 neset_neq0. Qed.

Canonical neset_hull (T : convType) (F : neset T) :=
  NESet.Pack (NESet.Class (neset_hull_neq0 F)).

End neset_lemmas.
Hint Resolve repr_in_neset.
Arguments image_neset : simpl never.

Section convex_neset_lemmas.
Local Open Scope classical_set_scope.
Local Open Scope R_scope.
Variable L : convType.
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
Lemma conv_pt_setE p x Y : conv_pt_set p x Y = (fun y => x <| p |> y) @` Y.
Proof. by []. Qed.
Definition conv_set p (X Y : set L) := \bigcup_(x in X) conv_pt_set p x Y.
Lemma conv_setE p X Y : conv_set p X Y = \bigcup_(x in X) conv_pt_set p x Y.
Proof. by []. Qed.
Lemma convC_set p X Y : conv_set p X Y = conv_set `Pr p.~ Y X.
Proof.
by apply eqEsubset=> u; case=> x Xx [] y Yy <-; exists y => //; exists x => //; rewrite -convC.
Qed.
Lemma conv1_pt_set x (Y : neset L) : conv_pt_set `Pr 1 x Y = [set x].
Proof.
apply eqEsubset => u.
- by case => y _; rewrite conv1.
- by move=> ->; eexists => //; rewrite conv1.
Qed.
Lemma conv0_pt_set x (Y : set L) : conv_pt_set `Pr 0 x Y = Y.
Proof.
apply eqEsubset => u.
- by case=> y Yy <-; rewrite conv0.
- by move=> Yu; exists u=> //; rewrite conv0.
Qed.
Lemma conv1_set X (Y : neset L) : conv_set `Pr 1 X Y = X.
Proof.
transitivity (\bigcup_(x in X) [set x]); last by rewrite bigcup_set1 image_idfun.
congr bigsetU; apply funext => x /=.
by rewrite (conv1_pt_set x Y).
Qed.
Lemma conv0_set (X : neset L) Y : conv_set `Pr 0 X Y = Y.
Proof.
rewrite convC_set /= (_ : `Pr 0.~ = `Pr 1) ?conv1_set //.
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
Lemma iter0_conv_set (X : set L) : iter_conv_set X 0 = X.
Proof. by []. Qed.
Lemma iterS_conv_set (X : set L) (n : nat) : iter_conv_set X (S n) = oplus_conv_set X (iter_conv_set X n).
Proof. by []. Qed.
Lemma probset_neq0 : probset != set0.
Proof. by apply/set0P; exists `Pr 0. Qed.
Lemma natset_neq0 : natset != set0.
Proof. by apply/set0P; exists O. Qed.
Lemma conv_pt_set_neq0 p (x : L) (Y : neset L) : conv_pt_set p x Y != set0.
Proof. exact: neset_image_neq0. Qed.
Lemma conv_set_neq0 p (X Y : neset L) : conv_set p X Y != set0.
Proof. by rewrite neset_neq0. Qed.
Lemma oplus_conv_set_neq0 (X Y : neset L) : oplus_conv_set X Y != set0.
Proof. apply/set0P; eexists; exists `Pr 1 => //; by rewrite conv1_set. Qed.
Fixpoint iter_conv_set_neq0 (X : neset L) (n : nat) :
  iter_conv_set X n != set0 :=
  match n with
  | 0 => neset_neq0 X
  | S n' => oplus_conv_set_neq0 X (NESet.Pack (NESet.Class (iter_conv_set_neq0 X n')))
  end.
Canonical probset_neset := NESet.Pack (NESet.Class probset_neq0).
Canonical natset_neset := NESet.Pack (NESet.Class natset_neq0).
Canonical conv_pt_set_neset (p : prob) (x : L) (Y : neset L) :=
  NESet.Pack (NESet.Class (conv_pt_set_neq0 p x Y)).
Canonical conv_set_neset (p : prob) (X Y : neset L) :=
  NESet.Pack (NESet.Class (conv_set_neq0 p X Y)).
Canonical oplus_conv_set_neset (X Y : neset L) :=
  NESet.Pack (NESet.Class (oplus_conv_set_neq0 X Y)).
Canonical iter_conv_set_neset (X : neset L) (n : nat) :=
  NESet.Pack (NESet.Class (iter_conv_set_neq0 X n)).

Lemma conv_pt_set_monotone (p : prob) (x : L) (Y Y' : set L) :
  Y `<=` Y' -> conv_pt_set p x Y `<=` conv_pt_set p x Y'.
Proof. by move=> YY' u [] y /YY' Y'y <-; exists y. Qed.
Lemma conv_set_monotone (p : prob) (X Y Y' : set L) :
  Y `<=` Y' -> conv_set p X Y `<=` conv_set p X Y'.
Proof. by move/conv_pt_set_monotone=> YY' u [] x Xx /YY' HY'; exists x. Qed.
Lemma oplus_conv_set_monotone (X Y Y' : set L) :
  Y `<=` Y' -> oplus_conv_set X Y `<=` oplus_conv_set X Y'.
Proof. by move/conv_set_monotone=> YY' u [] p _ /YY' HY'; exists p. Qed.
Lemma iter_monotone_conv_set (X : neset L) (m : nat) :
  forall n, (m <= n)%N -> iter_conv_set X m `<=` iter_conv_set X n .
Proof.
elim: m.
- move=> n _.
  case: n => // n.
  rewrite iter0_conv_set iterS_conv_set.
  by exists `Pr 1 => //; rewrite conv1_set.
- move=> m IHm.
  case => // n /(IHm _) mn.
  rewrite iterS_conv_set=> a [] p _ H.
  exists p => //.
  by move: (@conv_set_monotone p X _ _ mn) => /(_ a); apply.
Qed.  
Lemma iter_bigcup_conv_set (X : neset L) (n : nat) :
  iter_conv_set X n `<=` \bigcup_(i in natset) iter_conv_set X i.
Proof. by move=> a H; exists n. Qed.

Lemma iter_conv_set_superset (X : neset L) n : X `<=` iter_conv_set X n .
Proof.
move=> x Xx; elim: n => // n IHn; rewrite iterS_conv_set.
by exists `Pr 1 => //; rewrite conv1_set.
Qed.

Lemma Convn_iter_conv_set (n : nat) :
  forall (g : 'I_n -> L) (d : {dist 'I_n}) (X : set L),
    g @` setT `<=` X -> iter_conv_set X n (\Conv_d g).
Proof.
elim: n; first by move=> g d; move: (distI0_False d).
move=> n IHn g d X.
case/boolP: (X == set0);
  first by move/eqP => -> /(_ (g ord0)) H; apply False_ind; apply/H/imageP.
move=> Xneq0 gX; set X' := NESet.Pack (NESet.Class Xneq0).
have gXi : forall i : 'I_n.+1, X (g i) by apply fullimage_subset.
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
Lemma oplus_convC_set (X Y : set L) :
  oplus_conv_set X Y = oplus_conv_set Y X.
Proof.
suff H : forall X' Y', oplus_conv_set X' Y' `<=` oplus_conv_set Y' X'
    by apply/eqEsubset/H.
move=> {X} {Y} X Y u [] p _.
rewrite convC_set => H.
by exists (`Pr p.~) => //.
Qed.
Lemma convmm_cset (p : prob) (X : {convex_set L}) : conv_set p X X = X.
Proof.
apply eqEsubset=> x.
- case => x0 Xx0 [] x1 Xx1 <-; rewrite -in_setE.
  move/asboolP : (convex_setP X); apply; by rewrite in_setE.
- by move=> Xx; exists x=> //; exists x=> //; rewrite convmm.
Qed.
Lemma oplus_convmm_cset (X : {convex_set L}) : oplus_conv_set X X = X.
Proof.
apply eqEsubset => x.
- case=> p _.
  by rewrite convmm_cset.
- move=> Xx.
  exists `Pr 0 => //.
  by rewrite convmm_cset.
Qed.
Lemma oplus_convmm_set_hull (X : set L) :
  oplus_conv_set (hull X) (hull X) = hull X.
Proof.
by rewrite (oplus_convmm_cset (CSet.Pack (CSet.Class (convex_hull X)))).
Qed.
Lemma hull_iter_conv_set (X : set L) : hull X = \bigcup_(i in natset) iter_conv_set X i.
Proof.
apply eqEsubset; first by move=> x [] n [] g [] d [] gX ->; exists n => //; apply Convn_iter_conv_set.
apply bigsubsetU.
elim; first by move=> _ /=; move: X; apply hull_mem'.
move=> n IHn _.
have H : iter_conv_set X n.+1 `<=` oplus_conv_set X (hull X)
  by apply/oplus_conv_set_monotone/IHn.
apply (subset_trans H).
rewrite oplus_convC_set.
have H' : oplus_conv_set (hull X) X `<=` oplus_conv_set (hull X) (hull X)
  by apply/oplus_conv_set_monotone/hull_mem'.
apply (subset_trans H').
by rewrite oplus_convmm_set_hull.
Qed.

(* tensorial strength for hull and conv_set *)
Lemma hull_conv_set_strr (p : prob) (X Y : set L) :
  hull (conv_set p X (hull Y)) = hull (conv_set p X Y).
Proof.
apply hull_eqEsubset=> u.
- case=> x Xx [] y [] n [] g [] d [] gY yg <-.
  exists n, (fun i => x <|p|> g i), d.
  rewrite -convnDr yg; split=> //.
  by move=> v [] i _ <-; exists x=> //; exists (g i) => //; apply/gY/imageP.
- case=> x Xx [] y Yy <-.
  rewrite -in_setE; apply hull_mem; rewrite in_setE.
  by exists x=> //; exists y=> //; rewrite -in_setE; apply hull_mem; rewrite in_setE.
Qed.
End convex_neset_lemmas.

Module NECSet.
Section def.
Local Open Scope classical_set_scope.
Variable A : convType.
Record class_of (X : set A) : Type := Class {
  base : CSet.class_of X ; mixin : NESet.class_of X }.
Record t : Type := Pack { car : set A ; class : class_of car }.
Definition baseType (M : t) := CSet.Pack (base (class M)).
Definition mixinType (M : t) := NESet.Pack (mixin (class M)).
End def.
Module Exports.
Notation necset := t.
Canonical baseType.
Canonical mixinType.
Coercion baseType : necset >-> convex_set.
Coercion mixinType : necset >-> neset.
Coercion car : necset >-> set.
End Exports.
End NECSet.
Export NECSet.Exports.

Section necset_canonical.
Variable (A : convType).
Canonical necset_predType :=
  Eval hnf in mkPredType (fun t : necset A => (fun x => x \in (t : set _))).
Canonical necset_eqType := Equality.Pack (equality_mixin_of_Type (necset A)).
Canonical necset_choiceType := choice_of_Type (necset A).
(* NB(rei): redundant *)
(*Canonical necset_neset (t : necset A) : neset A := NESet.mk (NECSet.mixin (NECSet.H t)).*)
End necset_canonical.

Section necset_lemmas.
Variable A : convType.

Lemma necset_ext (a b : necset A) : a = b :> set _ -> a = b.
Proof.
move: a b => -[a Ha] -[b Hb] /= ?; subst a.
congr NECSet.Pack; exact/Prop_irrelevance.
Qed.

Local Open Scope classical_set_scope.
Lemma hull_necsetU (X Y : necset A) : hull (X `|` Y) =
  [set u | exists x, exists y, exists p, x \in X /\ y \in Y /\ u = x <| p |> y].
Proof.
apply eqEsubset => a.
- rewrite -in_setE; case/hull_setU; try by apply/set0P/neset_neq0.
  move=> x [] xX [] y [] yY [] p ->.
  by exists x, y, p.
- by case => x [] y [] p [] xX [] yY ->; rewrite -in_setE; apply mem_hull_setU.
Qed.

Canonical neset_hull_necset (T : convType) (F : neset T) :=
  NECSet.Pack (NECSet.Class (CSet.Class (convex_hull F)) (NESet.Class (neset_hull_neq0 F))).

Canonical necset1 (T : convType) (x : T) :=
  Eval hnf in @NECSet.Pack _ [set x] (NECSet.Class (CSet.Class (is_convex_set1 x)) (NESet.Class (set1_neq0 x))).

End necset_lemmas.

(*
(* non-empty convex sets of distributions *)
Notation "{ 'csdist+' T }" := (necset (Dist_convType T)) (format "{ 'csdist+'  T }") : convex_scope.
*)

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

(* TODO: move to top when deemed useful *)
Reserved Notation "x [+] y" (format "x  [+]  y", at level 50).

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
apply/neset_ext => /=; apply eqEsubset => x.
  by case=> Hx; [exists I => //; left | exists J => //; right].
by case=> K [] -> Hx; [left | right].
Qed.

Lemma Joet_setU (I J : neset L) : Joet `NE (I `|` J) = Joet `NE [set (Joet I); (Joet J)].
Proof.
rewrite nesetU_bigsetU Joet_bigsetU.
congr (Joet `NE _); apply/neset_ext => /=.
by rewrite image_idfun /= image_setU !image_set1.
Qed.

(* NB: [Reiterman] p.326, axiom 1 is trivial, since our Joet operation receives
   a set but not a sequence. *)

(* [Reiterman] p.326, axiom 2 *)
Lemma Joet_flatten (F : neset (neset L)) : Joet `NE (Joet @` F) = Joet `NE (bigsetU F idfun).
Proof.
rewrite Joet_bigsetU; congr (Joet `NE _); apply/neset_ext => /=.
apply eq_imager; by rewrite image_idfun.
Qed.

Definition joet (x y : L) := Joet `NE [set x; y].
Global Arguments joet : simpl never.
Local Notation "x [+] y" := (joet x y).

Lemma joetC : commutative joet.
Proof. by move=> x y; congr Joet; apply neset_ext => /=; rewrite /joet setUC. Qed.
Lemma joetA : associative joet.
Proof.
by move=> x y z; rewrite /joet -[in LHS](Joet1 x) -[in RHS](Joet1 z) -!Joet_setU; congr Joet; apply neset_ext => /=; rewrite setUA.
Qed.
Lemma joetxx : idempotent joet.
Proof.
by move=> x; rewrite -[in RHS](Joet1 x); congr Joet; apply neset_ext => /=; rewrite setUid.
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
Variables (L M : semiCompSemiLattType).
Definition Joet_morph (f : L -> M) :=
  forall (X : neset L), f (Joet X) = Joet `NE (f @` X).
Definition joet_morph (f : L -> M) :=
  forall (x y : L), f (x [+] y) = f x [+] f y.
Lemma Joet_joet_morph (f : L -> M) : Joet_morph f -> joet_morph f.
Proof.
move=> H x y.
move: (H `NE [set x; y]) => ->.
transitivity (Joet `NE [set f x; f y]) => //.
congr (Joet `NE _); apply/neset_ext => /=.
by rewrite image_setU !image_set1.
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
Record class_of (f : U -> V) : Prop := Class {
  base : affine_function f ;
  base2 : Joet_morph f ;
}.
Structure map (phUV : phant (U -> V)) :=
  Pack {apply : U -> V ; class' : class_of apply}.
Definition baseType (phUV : phant (U -> V)) (f : map phUV) : {affine U -> V} :=
  AffineFunction (base (class' f)).
Definition base2Type (phUV : phant (U -> V)) (f : map phUV) : {Joet_morph U -> V} :=
  JoetMorph (base2 (class' f)).
Local Coercion apply : map >-> Funclass.
Variables (phUV : phant (U -> V)) (f g : U -> V) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.
End ClassDef.
Module Exports.
Coercion apply : map >-> Funclass.
Coercion baseType : map >-> AffineFunction.map.
Coercion base2Type : map >-> JoetMorph.map.
Canonical baseType.
Canonical base2Type.
Notation JoetAffine fA := (Pack (Phant _) fA).
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

Variable L : semiCompSemiLattConvType.

Lemma JoetDr : forall (p : prob) (x : L) (Y : neset L),
  x <|p|> Joet Y = Joet `NE ((fun y => x <|p|> y) @` Y).
Proof. by case: L => ? [? ? []]. Qed.
Lemma JoetDl (p : prob) (X : neset L) (y : L) :
  Joet X <|p|> y = Joet `NE ((fun x => x <|p|> y) @` X).
Proof.
rewrite convC JoetDr.
congr Joet; apply/neset_ext/eq_imagel=> x Xx.
by rewrite -convC.
Qed.
Lemma joetDr p : right_distributive (fun x y => x <|p|> y) (@joet L).
Proof.
move=> x y z.
rewrite JoetDr.
transitivity (Joet `NE [set x <|p|> y; x <|p|> z]) => //.
congr (Joet `NE _); apply/neset_ext => /=.
by rewrite image_setU !image_set1.
Qed.
Lemma Joet_conv_pt_setE p x (Y : neset L) :
  Joet `NE (conv_pt_set p x Y) = Joet `NE ((Conv x)^~ p @` Y).
Proof.
by congr (Joet `NE _); apply/neset_ext.
Qed.
Lemma Joet_conv_pt_setD p x (Y : neset L) :
  Joet `NE (conv_pt_set p x Y) = x <|p|> Joet Y.
Proof. by rewrite Joet_conv_pt_setE -JoetDr. Qed.
Lemma Joet_conv_setE p (X Y : neset L) :
  Joet `NE (conv_set p X Y) =
  Joet `NE ((fun x => x <|p|> Joet Y) @` X).
Proof.
transitivity (Joet `NE (\bigcup_(x in X) conv_pt_set p x Y)).
  by congr (Joet `NE _); apply neset_ext.
rewrite Joet_bigcup //; congr (Joet `NE _); apply neset_ext => /=.
rewrite imageA; congr image; apply funext => x /=.
by rewrite Joet_conv_pt_setD.
Qed.
Lemma Joet_conv_setD p (X Y : neset L) :
  Joet `NE (conv_set p X Y) = Joet X <|p|> Joet Y.
Proof. by rewrite Joet_conv_setE JoetDl. Qed.
Lemma Joet_oplus_conv_setE (X Y : neset L) :
  Joet `NE (oplus_conv_set X Y) =
  Joet `NE ((fun p => Joet X <|p|> Joet Y) @` probset).
Proof.
transitivity (Joet `NE (\bigcup_(p in probset_neset) conv_set p X Y)).
  by congr (Joet `NE _); apply/neset_ext.
rewrite Joet_bigcup //.
congr (Joet `NE _); apply/neset_ext => /=.
rewrite imageA; congr image; apply funext => p /=.
by rewrite Joet_conv_setD.
Qed.
Lemma Joet_iter_conv_set (X : neset L) (n : nat) :
  Joet `NE (iter_conv_set X n) = Joet X.
Proof.
elim: n => [|n IHn /=]; first by congr Joet; apply/neset_ext.
rewrite Joet_oplus_conv_setE.
transitivity (Joet `NE [set Joet X]); last by rewrite Joet1.
congr (Joet `NE _); apply/neset_ext => /=.
transitivity ((fun _ => Joet X) @` probset); last by rewrite image_const.
by congr image; apply funext=> p; rewrite IHn convmm.
Qed.

Lemma Joet_hull (X : neset L) : Joet `NE (hull X) = Joet X.
Proof.
transitivity (Joet `NE (\bigcup_(i in natset) iter_conv_set X i));
  first by congr Joet; apply neset_ext; rewrite /= hull_iter_conv_set.
rewrite Joet_bigsetU /=.
rewrite -[in RHS](Joet1 (Joet X)).
transitivity (Joet `NE ((fun _ => Joet X) @` natset)); last first.
  by congr Joet; apply/neset_ext/image_const.
congr (Joet `NE _); apply/neset_ext => /=.
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
split; [exact: mem_convex_set | split; [exact: mem_convex_set | by []]].
Qed.
Definition pre_conv X Y p : convex_set A :=
  CSet.Pack (CSet.Class (pre_pre_conv_convex X Y p)).
Lemma pre_conv_neq0 X Y p : pre_conv X Y p != set0 :> set _.
Proof.
case/set0P: (neset_neq0 X) => x; rewrite -in_setE => xX.
case/set0P: (neset_neq0 Y) => y; rewrite -in_setE => yY.
apply/set0P; exists (x <| p |> y); rewrite -in_setE.
by rewrite inE asboolE; exists x, y.
Qed.
Definition conv X Y p : necset A := locked
  (NECSet.Pack (NECSet.Class (CSet.Class (pre_pre_conv_convex X Y p))
               (NESet.Class (pre_conv_neq0 X Y p)))).
Lemma conv1 X Y : conv X Y `Pr 1 = X.
Proof.
rewrite /conv; unlock; apply necset_ext => /=; apply/eqEsubset => a.
  by case => x [] y [] xX [] yY ->; rewrite -in_setE conv1.
case/set0P: (neset_neq0 Y) => y; rewrite -in_setE => yY.
rewrite -in_setE => aX.
by exists a, y; rewrite conv1.
Qed.
Lemma convmm X p : conv X X p = X.
Proof.
rewrite/conv; unlock; apply necset_ext => /=; apply eqEsubset => a.
- case => x [] y [] xX [] yY ->.
  rewrite -in_setE; exact: mem_convex_set.
- rewrite -in_setE => aX.
  by exists a, a; rewrite convmm.
Qed.
Lemma convC X Y p : conv X Y p = conv Y X `Pr p.~.
Proof.
by rewrite/conv; unlock; apply necset_ext => /=; apply eqEsubset => a; case => x [] y [] xX [] yY ->; exists y, x; [rewrite convC | rewrite -convC].
Qed.
Lemma convA p q X Y Z :
  conv X (conv Y Z q) p = conv (conv X Y [r_of p, q]) Z [s_of p, q].
Proof.
rewrite/conv; unlock; apply/necset_ext => /=; apply eqEsubset => a; case => x [].
- move=> y [] xX [].
  rewrite in_setE => -[] y0 [] z0 [] y0Y [] z0Z -> ->.
  exists (x <| [r_of p, q] |> y0), z0.
  by rewrite inE asboolE /= convA; split; try exists x, y0.
- move=> z []; rewrite in_setE => -[] x0 [] y [] x0X [] yY -> [] zZ ->.
  exists x0, (y <| q |> z).
  split => //.
  by rewrite inE asboolE /= -convA; split; try exists y, z.
Qed.
Definition mixin : ConvexSpace.class_of [choiceType of necset A] :=
  @ConvexSpace.Class _ conv conv1 convmm convC convA.
End def.
Section lemmas.
Local Open Scope classical_set_scope.
Variable A : convType.
Lemma convE X Y p : conv X Y p =
  [set a : A | exists x, exists y, x \in X /\ y \in Y /\ a = x <| p |> y]
    :> set A.
Proof. rewrite/conv; unlock; reflexivity. Qed.
Lemma conv_conv_set X Y p : conv X Y p = conv_set p X Y :> set A.
Proof.
rewrite convE; apply eqEsubset=> u.
- by case=> x [] y; rewrite !in_setE; case=> Xx [] Yy ->; exists x => //; exists y.
- by case=> x Xx [] y Yy <-; exists x, y; rewrite !in_setE.
Qed.
End lemmas.
End necset_convType.
Canonical necset_convType A := ConvexSpace.Pack (necset_convType.mixin A).

Module necset_semiCompSemiLattType.
Section def.
Local Open Scope classical_set_scope.
Variable (A : convType).
Definition pre_op (X : neset (necset A)) : convex_set A :=
  CSet.Pack (CSet.Class (convex_hull `NE (bigsetU X idfun))).
Lemma pre_op_neq0 X : pre_op X != set0 :> set _.
Proof. by rewrite hull_eq0 neset_neq0. Qed.
Definition op (X : neset (necset A)) :=
  NECSet.Pack (NECSet.Class (CSet.Class (convex_hull `NE (bigsetU X idfun))) (NESet.Class (pre_op_neq0 X))).
Lemma op1 x : op `NE [set x] = x.
Proof. by apply necset_ext => /=; rewrite bigcup1 hull_cset. Qed.
Lemma op_bigsetU (I : Type) (S : neset I) (F : I -> neset (necset A)) :
    op (bignesetU S F) = op `NE (op @` (F @` S)).
Proof.
apply necset_ext => /=.
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
Lemma axiom (p : prob) (X : L) (I : neset L) :
    (necset_convType.conv X (Joet I) p) =
    Joet `NE ((fun Y => necset_convType.conv X Y p) @` I).
Proof.
apply necset_ext => /=.
rewrite -hull_cset necset_convType.conv_conv_set /= hull_conv_set_strr.
congr hull; apply eqEsubset=> u /=.
- case=> x Xx [] y []Y IY Yy <-.
  exists (necset_convType.conv X Y p); first by exists Y.
  rewrite necset_convType.conv_conv_set.
  by exists x=> //; exists y.
- by case=> U [] Y IY <-; rewrite necset_convType.convE=> -[] x [] y; rewrite !in_setE=> -[] Xx [] Yy ->; exists x=> //; exists y=> //; exists Y.
Qed.

Definition mixin := @SemiCompSemiLattConvType.Class [choiceType of necset A] (necset_semiCompSemiLattType.mixin A) (necset_convType.mixin A) (SemiCompSemiLattConvType.Mixin axiom).
End def.
End necset_semiCompSemiLattConvType.
Canonical necset_semiCompSemiLattConvType A := SemiCompSemiLattConvType.Pack (necset_semiCompSemiLattConvType.mixin A).
