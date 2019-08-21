Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype finfun bigop.
Require Import Reals_ext Rbigop ssrR proba dist convex_choice.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import finmap set.
Require category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope convex_scope.

(* choiceType as a category *)
(* Type as a category *)
Section choiceType_category.
Import category.
Definition choiceType_category_class : Category.class_of choiceType :=
@Category.Class choiceType id (fun _ _ _ => True) (fun _ => I) (fun _ _ _ _ _ _ _ => I).
Canonical choiceType_category := Category.Pack choiceType_category_class.
Definition hom_choiceType (a b : choiceType) (f : a -> b) : {hom a,b} := Hom (I : hom (f : El a -> El b)).
End choiceType_category.

(* free choiceType functor *)
Section gen_choiceType_functor.
Import category.

Definition gen_choiceType (T : Type) : choiceType :=
  Choice.Pack (Choice.Class (@gen_eqMixin T) (@gen_choiceMixin T)).

Local Notation m := gen_choiceType.
Local Notation CC := choiceType_category.

Definition gen_choiceType_mor (T U : Type_category) (f : {hom T, U}) :
  {hom m T, m U} := hom_choiceType (f : m T -> m U).
Lemma gen_choiceType_mor_id : FunctorLaws.id gen_choiceType_mor.
Proof. by move=> a; rewrite hom_ext. Qed.
Lemma gen_choiceType_mor_comp : FunctorLaws.comp gen_choiceType_mor.
Proof. by move=> a b c g h; rewrite hom_ext. Qed.
Definition gen_choiceType_functor :=
  Functor.Pack (Functor.Class gen_choiceType_mor_id gen_choiceType_mor_comp).

Lemma gen_choiceType_mor_comp_fun (a b c : Type) (g : {hom b, c})
      (h : {hom a, b}):
  [fun of gen_choiceType_mor [hom of [fun of g] \o [fun of h]]] =
  [fun of gen_choiceType_mor g] \o [fun of gen_choiceType_mor h].
Proof. by rewrite gen_choiceType_mor_comp. Qed.

Local Notation CT := Type_category.
Definition forget_choiceType : functor CC CT.
set (m := Choice.sort).
set (h := fun (a b : CC) (f : {hom CC; a, b}) =>
             @Hom.Pack CT a b _ (FId # f) I : {hom CT; m a , m b}).
refine (@Functor.Pack CC CT m _).
refine (@Functor.Class _ _  m h  _ _); by move=> *; apply hom_ext. 
Defined.
Lemma forget_choiceTypeE :
  (forall a : CC, forget_choiceType a = a)
  /\ (forall a b (f : {hom CC; a , b}), forget_choiceType # f = f :> (a -> b)).
Proof. done. Qed.
End gen_choiceType_functor.

Section epsC_etaC.
Import category.
(*Definition epsC (C : choiceType) : gen_choiceType (forget_choiceType C) -> C.*)
Definition epsC'' {C : choiceType} : gen_choiceType C -> C := idfun.
Definition epsC' : gen_choiceType_functor \O forget_choiceType ~~> FId :=
  fun T => @Hom.Pack choiceType_category _ _ _ (@epsC'' T) I.
Lemma epsC'_natural : naturality _ _ epsC'.
Proof. by []. Qed.
Definition epsC : gen_choiceType_functor \O forget_choiceType ~> FId :=
  locked (Natural.Pack (Natural.Class epsC'_natural)).
Lemma epsCE' : epsC = Natural epsC'_natural.
Proof. by rewrite /epsC; unlock. Qed.
Lemma epsCE (T : choiceType) : epsC T = idfun :> (_ -> _).
Proof. by rewrite /epsC; unlock. Qed.

Definition etaC': FId ~~> forget_choiceType \O gen_choiceType_functor :=
  fun _ => @Hom.Pack Type_category _ _ _ idfun I.
Lemma etaC'_natural : naturality _ _ etaC'.
Proof. by []. Qed.
Definition etaC: FId ~> forget_choiceType \O gen_choiceType_functor :=
  locked (Natural.Pack (Natural.Class etaC'_natural)).
Lemma etaCE' : etaC = Natural etaC'_natural.
Proof. by rewrite /etaC; unlock. Qed.
Lemma etaCE (T : Type) : etaC T = idfun :> (_ -> _).
Proof. by rewrite /etaC; unlock. Qed.

Import homcomp_notation.
Local Notation F := gen_choiceType_functor.
Local Notation G := forget_choiceType.
Lemma triLC c : (epsC (F c)) \o (F # etaC c) = idfun.
Proof. by rewrite etaCE epsCE. Qed.
Lemma triRC d : (G # epsC d) \o (etaC (G d)) = idfun.
Admitted.
End epsC_etaC.

(* convType as a category *)
Section convType_category.
Import category.
Lemma affine_function_comp_proof' :
  forall (A B C : convType) (f : A -> B) (g : B -> C),
    affine_function f -> affine_function g -> affine_function (g \o f).
Proof. by move=>A B C f g Hf Hg a b t; rewrite /affine_function_at funcompE Hf Hg. Qed.
Definition convType_category_class : Category.class_of convType :=
  Category.Class affine_function_id_proof affine_function_comp_proof'.
Canonical convType_category := Category.Pack convType_category_class.
End convType_category.

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
Lemma eq_fset1 (T : choiceType) (x y : T) : [fset x] = [fset y] -> x = y.
Proof.
move/eqP; rewrite eqEfsubset => /andP [] /fsubsetP /(_ x).
rewrite !inE=> H _.
by apply/eqP/H.
Qed.
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

(* TODO: move to ssrR *)
Lemma paddR_neq0 (p q : R) (p0 : 0 <= p) (q0 : 0 <= q) : p + q != 0 <-> p != 0 \/ q != 0.
Proof.
split => [H | /orP].
- apply/orP; rewrite -negb_and; apply: contra H => /andP[/eqP -> /eqP ->].
  by rewrite addR0.
- rewrite -negb_and; apply: contra => /eqP/paddR_eq0.
  case/(_ p0)/(_ q0) => -> ->; by rewrite eqxx.
Qed.

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

Section misc_Dist.
Local Open Scope R_scope.
Lemma eq_Dist1 (A : choiceType) (x y : A) : Dist1.d x = Dist1.d y -> x = y.
Proof.
move/(congr1 (fun (d : Dist A) => d x)).
rewrite !Dist1.dE /Dist1.f /= !fsfunE !inE eqxx=> H.
apply/eqP/negbNE/negP=> /negbTE xny.
move: H; rewrite xny.
exact: R1_neq_R0.
Qed.
End misc_Dist.
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
  S1 (Convn_indexed_over_finType d f) = \ssum_i scalept (d i) (S1 (f i)).
Proof.
rewrite /Convn_indexed_over_finType.
rewrite S1_convn /=.
evar (X : nat -> scaled_pt A).
transitivity (\ssum_(i < Convn_indexed_over_finType.n T) X i).
- apply eq_bigr => -[i Hi] _.
  set (i' := nat_of_ord (Ordinal Hi)).
  rewrite ffunE.
  rewrite /Convn_indexed_over_finType.enum /=.
  set F := (fun i =>
           scalept (d (nth (Convn_indexed_over_finType.t0 d) (index_enum T) i))
          (S1 (f (nth (Convn_indexed_over_finType.t0 d) (index_enum T) i)))).
  transitivity (F i'); exact: erefl.
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
Lemma conv_pt_set_monotone (p : prob) (x : L) (Y Y' : set L) :
  Y `<=` Y' -> conv_pt_set p x Y `<=` conv_pt_set p x Y'.
Proof. by move=> YY' u [] y /YY' Y'y <-; exists y. Qed.
Lemma conv_set_monotone (p : prob) (X Y Y' : set L) :
  Y `<=` Y' -> conv_set p X Y `<=` conv_set p X Y'.
Proof. by move/conv_pt_set_monotone=> YY' u [] x Xx /YY' HY'; exists x. Qed.
Lemma oplus_conv_set_monotone (X Y Y' : set L) :
  Y `<=` Y' -> oplus_conv_set X Y `<=` oplus_conv_set X Y'.
Proof. by move/conv_set_monotone=> YY' u [] p _ /YY' HY'; exists p. Qed.
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

(* semiCompSemiLattConvType as a category *)
Section semiCompSemiLattConvType_category.
Import category.
Local Notation U := semiCompSemiLattConvType.
Lemma Joet_affine_id_proof (A : U) : JoetAffine.class_of (@id A).
Proof.
apply JoetAffine.Class; first by exact: affine_function_id_proof.
by move=> x; congr Joet; apply neset_ext; rewrite /= image_idfun.
Qed.
Lemma Joet_affine_comp_proof (A B C : U) (f : A -> B) (g : B -> C) :
    JoetAffine.class_of f -> JoetAffine.class_of g ->
    JoetAffine.class_of (g \o f).
Proof. 
case => af jf [] ag jg.
apply JoetAffine.Class; first by exact: affine_function_comp_proof'.
move=> x; cbn.
rewrite jf jg.
congr Joet; apply neset_ext =>/=.
by rewrite imageA.
Qed.
Definition semiCompSemiLattConvType_category_class :
  Category.class_of U :=
  Category.Class Joet_affine_id_proof Joet_affine_comp_proof.
Canonical semiCompSemiLattConvType_category :=
  Category.Pack semiCompSemiLattConvType_category_class.
End semiCompSemiLattConvType_category.

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

Section apply_affine.
Import category.
Lemma apply_affine (K L : semiCompSemiLattConvType) (f : {hom K , L})
  (X : necset_semiCompSemiLattConvType K) :
  f (Joet `NE X) = Joet `NE (f @` X).
Proof. by case: f => f [? /= ->]. Qed.
End apply_affine.

Section Dist_functor.
Import category.
(*
Definition affine_hom (T U : convType) (f : {affine T -> U}) : {hom T, U}.
apply (@Hom.Pack convType_category _ _ _ f).
rewrite /Hom.axiom /=.
by case: f.
Defined.
*)

(* morphism part of Dist *)
Definition Dist_mor (A B : choiceType) (f : {hom A , B}) :
  {hom Dist_convType A , Dist B}.
refine (@Hom.Pack convType_category _ _ _ (Distfmap f) _).
move=> x y t.
by apply: Conv2Dist.bind_left_distr.
Defined.

(* Dist_mor induces maps between supports *)
Definition Dist_mor_supp (A B : choiceType) (f : A -> B(*{hom A , B}*)) (d : Dist A) :
  [finType of finsupp d] -> [finType of finsupp ((Dist_mor (hom_choiceType f)) d)].
Proof.
move=> x.
apply (@FSetSub _ _ (f (fsval x))).
rewrite /= DistBind.supp imfset_id.
apply/bigfcupP.
exists (Dist1.d (f (fsval x))).
- rewrite andbT.
  apply (in_imfset _ (fun x => Dist1.d (f x))) => /=.
  by move:x; case:d.
- rewrite mem_finsupp Dist1.dE /Dist1.f /= fsfunE inE eqxx.
  by apply/eqP/R1_neq_R0.
Defined.
Global Arguments Dist_mor_supp [A B] f d.
Lemma fsval_Dist_mor_supp (A B : choiceType) (f : {hom A , B}) d i :
  fsval ((Dist_mor_supp f d) i) = f (fsval i).
Proof. by case: i. Qed.

Lemma Dist_mor_id : FunctorLaws.id Dist_mor.
Proof.
by move=> a; rewrite hom_ext funeqE=> x /=; rewrite/idfun Distfmap_id.
Qed.
Lemma Dist_mor_comp : FunctorLaws.comp Dist_mor.
Proof. by move=> a b c g h; rewrite hom_ext /= Distfmap_comp. Qed.

Definition Dist_functor :=
  Functor.Pack (Functor.Class Dist_mor_id Dist_mor_comp).

Lemma Dist_mor_comp_fun (a b c : choiceType) (g : {hom b, c})
      (h : {hom a, b}):
  [fun of Dist_mor [hom of [fun of g] \o [fun of h]]] =
  [fun of Dist_mor g] \o [fun of Dist_mor h].
Proof. by rewrite Dist_mor_comp. Qed.

Local Notation CV := convType_category.
Local Notation CC := choiceType_category.
Definition forget_convType : functor CV CC.
set (m := [eta FId] : CV -> CC).
set (h := fun (a b : CV) (f : {hom CV; a, b}) =>
             @Hom.Pack CC a b _ (FId # f) I : {hom CC; m a , m b}).
refine (@Functor.Pack CV CC m _).
refine (@Functor.Class _ _  m h  _ _); by move=> *; apply hom_ext. 
Defined.

Lemma forget_convTypeE :
  (forall a : CV, forget_convType a = a)
  /\ (forall a b (f : {hom CV; a , b}), forget_convType # f = f :> (a -> b)).
Proof. done. Qed.
End Dist_functor.

(*
  eps0 is the counit of the adjunction (Dist -| coercion) and it is just Convn
  (* p.164 *).
*)
Section eps0_eta0.
Import category.
Import ScaledConvex.
Local Open Scope fset_scope.
Local Open Scope R_scope.

Definition eps0'' {C : convType} (d : Dist C) : C :=
  Convn_indexed_over_finType (dist_of_Dist d) (fun x : finsupp d => fsval x).

Lemma eps0''_affine (C : convType) : affine_function (@eps0'' C).
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
transitivity (\ssum_(i : dist_of_Dist.D (x <|p|> y))
              scalept ((x <|p|> y) (fsval i)) (S1 (fsval i)));
  first by apply eq_bigr => i; rewrite dist_of_DistE.
rewrite -(@big_seq_fsetE
            _ _ _ _ _ xpredT
            (fun i => scalept ((x <|p|> y) i) (S1 i))
         ) /=.
transitivity (\ssum_(i <- finsupp (x <|p|> y))
  ((scalept (x i) (S1 i) : Scaled_convType C) <|p|> scalept (y i) (S1 i))); first by apply eq_bigr => i _; rewrite Dist_scalept_conv.
rewrite big_seq_fsetE big_scalept_conv_split /=.
rewrite -(@big_seq_fsetE _ _ _ _ _ xpredT (fun i => scalept (x i) (S1 i))).
rewrite -(@big_seq_fsetE _ _ _ _ _ xpredT (fun i => scalept (y i) (S1 i))) /=.
have -> : \ssum_i scalept (dist_of_Dist x i) (S1 (fsval i)) =
         \ssum_(i <- finsupp x) scalept (x i) (S1 i)
  by rewrite big_seq_fsetE /=; apply eq_bigr => i _; rewrite dist_of_DistE.
have -> : \ssum_i scalept (dist_of_Dist y i) (S1 (fsval i)) =
         \ssum_(i <- finsupp y) scalept (y i) (S1 i)
  by rewrite big_seq_fsetE /=; apply eq_bigr => i _; rewrite dist_of_DistE.
have -> : \ssum_(i <- finsupp x) scalept (x i) (S1 i) =
         \ssum_(i <- finsupp (x <|p|> y)) scalept (x i) (S1 i).
- rewrite [in RHS](bigID (fun i => i \in (finsupp x))) /=.
  have -> : (\ssum_(i <- finsupp (x <|p|> y) | i \notin finsupp x) scalept (x i) (S1 i)) = Zero C
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
suff -> : \ssum_(i <- finsupp y) scalept (y i) (S1 i) =
         \ssum_(i <- finsupp (x <|p|> y)) scalept (y i) (S1 i) by [].
rewrite [in RHS](bigID (fun i => i \in (finsupp y))) /=.
have -> : (\ssum_(i <- finsupp (x <|p|> y) | i \notin finsupp y) scalept (y i) (S1 i)) = Zero C
  by rewrite big1 //= => i Hi; rewrite fsfun_dflt // scalept0.
rewrite addpt0 [in RHS]big_fset_condE /=.
suff H : finsupp y = [fset i | i in finsupp (x <|p|> y) & i \in finsupp y]
  by rewrite [in LHS]H.
+ have -> : [fset i | i in finsupp (x <|p|> y) & i \in finsupp y] =
           [fset i | i in finsupp y & i \in finsupp (x <|p|> y)]
    by apply eq_imfset => //; move => i /=; rewrite !inE andbC.
  apply/eqP; rewrite eqEfsubset; apply/andP; split; last by apply fset_sub.
  apply/fsubsetP => i Hi.
  by rewrite !inE /= Hi finsupp_Conv2 // inE Hi orbT.
Qed.

Lemma eps0''_natural (C D : convType) (f : {hom C, D}) :
  f \o eps0'' = eps0'' \o (Dist_functor \O forget_convType) # f.
Proof.
rewrite FCompE /= /id_f.
apply funext => d; apply S1_inj => /=.
rewrite S1_proj_Convn_indexed_over_finType; last by case: f.
rewrite S1_Convn_indexed_over_finType.
evar (Y : dist_of_Dist.D ((Distfmap f) d) -> scaled_pt D).
transitivity (\ssum_i Y i); last first.
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
  have -> : \ssum_(i0 <- finsupp d | fsval i != f i0)
             scalept (d i0 * (Dist1.d (f i0)) (fsval i)) (S1 (fsval i)) =
           Zero _
    by rewrite big1 // => c /negbTE Hc; rewrite Dist1.dE /Dist1.f fsfunE inE Hc mulR0 scalept0.
  rewrite addpt0.
  rewrite big_seq_fsetE /=.
  exact: erefl.
rewrite /Y => {Y}.
set f' := (Dist_mor_supp f d).
transitivity (\ssum_i scalept (dist_of_Dist d i) (S1 (fsval (f' i)))); first by apply eq_bigr => *; rewrite fsval_Dist_mor_supp.
rewrite (@partition_big
           _ _ _ _ (dist_of_Dist.D ((Distfmap f) d)) _ f' xpredT) /f' //=.
apply eq_bigr => -[i Hi] _ /=.
transitivity (\ssum_(i0 | Dist_mor_supp f d i0 == [` Hi])
               scalept (d (fsval i0) * (Dist1.d (f (fsval i0))) i) (S1 i)).
- apply eq_bigr => i0 /eqP.
  move/(congr1 (@fsval _ _)); rewrite fsval_Dist_mor_supp /= => Hi0.
  rewrite dist_of_DistE Dist1.dE /Dist1.f fsfunE /=.
  have -> : i \in [fset f (fsval i0)] by rewrite -Hi0 inE.
  by rewrite -Hi0 mulR1.
apply eq_bigl => i0.
apply/eqP/eqP; first by move/(congr1 (@fsval _ _)) => /= <-.
move=> H.
exact/val_inj.
Qed.

Definition eps0' : Dist_functor \O forget_convType ~~> FId :=
fun a => @Hom.Pack convType_category _ _ _ eps0'' (eps0''_affine (C:=FId a)).

Lemma eps0'E (C : convType) (d : Dist C) :
  eps0' C d = Convn_indexed_over_finType (dist_of_Dist d) (fun x : finsupp d => (fsval x)).
Proof. reflexivity. Qed.

Lemma eps0'_natural : naturality _ _ eps0'.
Proof. by move=> C D f; rewrite eps0''_natural. Qed.

Definition eps0 : Dist_functor \O forget_convType ~> FId :=
  locked (Natural.Pack (Natural.Class eps0'_natural)).

Lemma eps0E' : eps0 = Natural eps0'_natural.
Proof. by rewrite /eps0; unlock. Qed.
Lemma eps0E (C : convType) :
  eps0 C = (fun d => Convn_indexed_over_finType (dist_of_Dist d) (fun x : finsupp d => (fsval x))) :> (_ -> _).
Proof. by rewrite /eps0; unlock. Qed.

Definition eta0' : FId ~~> forget_convType \O Dist_functor :=
  fun C => @Hom.Pack choiceType_category _ _ _ (fun x : C => Dist1.d x) I.
Lemma eta0'_natural : naturality _ _ eta0'.
Proof.
move=> a b h; rewrite funeqE=> x.
by rewrite FIdf /eta0' /= /Distfmap /= DistBind1f.
Qed.
Definition eta0 : FId ~> forget_convType \O Dist_functor :=
  locked (Natural.Pack (Natural.Class eta0'_natural)).
Lemma eta0E' : eta0 = Natural eta0'_natural.
Proof. by rewrite /eta0; unlock. Qed.
Lemma eta0E (T : choiceType) : eta0 T = (@Dist1.d _) :> (_ -> _).
Proof. by rewrite /eta0; unlock. Qed.

Import homcomp_notation.
Import ScaledConvex.
Local Open Scope fset_scope.
Local Open Scope R_scope.
Local Notation F := Dist_functor.
Local Notation G := forget_convType.
Lemma triL0 c : (eps0 (F c)) \o (F # eta0 c) = idfun.
Proof.
apply funext=> x /=.

rewrite eps0E eta0E; apply: (@S1_inj _ _ x).
rewrite S1_Convn_indexed_over_finType /=.

have Y : forall (i : finsupp (Distfmap (Dist1.d (A:=c)) x)),
    exists a_x0 : prod (Dist (Dist c)) (FId c),
        a_x0.2 \in finsupp x /\
               a_x0.1 = Dist1.d (Dist1.d a_x0.2) /\
               fsval i \in finsupp a_x0.1.
- case=> i /= iP.
  move: iP; rewrite /Distfmap DistBind.supp=> /bigfcupP [] a /andP [].
  have-> : [fset Dist1.d (Dist1.d a0) | a0 in [fset a0 | a0 in finsupp x]] =
           [fset Dist1.d (Dist1.d a0) | a0 in finsupp x]
    by apply eq_imfset => //; move=> y/= ; rewrite inE /=.
  case/imfsetP=> x0 /= x0x ax0 _ ia.
  exists (a, x0).
  by split=> //; split.
set Ya := (fun i => match cid (Y i) with exist a_x0 _ => a_x0.1 end).
set Yx0 := (fun i => match cid (Y i) with exist a_x0 _ => a_x0.2 end).
set F := fun (i : finsupp (Distfmap (Dist1.d (A:=c)) x)) =>
           scalept (x (Yx0 i)) (S1 (fsval i)).
(*set F := fun (i0 : Dist_convType c) => scalept (x XX) (S1 i0).*)
(*evar (F : Dist c -> scaled_pt (Dist_convType c)).*)
rewrite (eq_bigr F); last first.
- move=> i _. 
  rewrite dist_of_DistE /Distfmap /=.
  rewrite /F /Yx0.
  case: i => i /= iP.
  case: (cid (Y.[iP])%fmap).
  case => a x0 /= [] x0x [] ax0 [] ia /=.
(*
  case=> i /= iP; rewrite dist_of_DistE /Distfmap /=.
  move: iP; rewrite /Distfmap DistBind.supp=> /bigfcupP [] a /andP [].
  have-> : [fset Dist1.d (Dist1.d a0) | a0 in [fset a0 | a0 in finsupp x]] =
           [fset Dist1.d (Dist1.d a0) | a0 in finsupp x]
    by apply eq_imfset => //; move=> y/= ; rewrite inE /=.
  case/imfsetP=> x0 /= x0x ax0 _ ia _.
*)
  suff -> : (DistBind.d x (fun a0 : c => Dist1.d (Dist1.d a0))) i = x x0 by done.
  rewrite DistBind.dE /DistBind.f fsfunE.
  have-> : [fset Dist1.d (Dist1.d a) | a in [fset a | a in finsupp x]] =
           [fset Dist1.d (Dist1.d a) | a in finsupp x]
    by apply eq_imfset => //; move=> y/= ; rewrite inE /=.
  have-> : \sum_(a0 <- finsupp x) x a0 * (Dist1.d (Dist1.d a0)) i =
           \sum_(a0 <- finsupp x) x a0 * (if i == Dist1.d a0 then 1 else 0)
    by apply eq_bigr=> a0 _; rewrite Dist1.dE /Dist1.f fsfunE inE.
  rewrite (bigID (fun a0 => i == Dist1.d a0)) /=.
  have-> : \sum_(i0 <- finsupp x | i != Dist1.d i0)
            x i0 * (if i == Dist1.d i0 then 1 else 0) = 0
    by rewrite big1 //= => a0; move/negbTE ->; rewrite mulR0.
  have-> : \sum_(i0 <- finsupp x | i == Dist1.d i0)
            x i0 * (if i == Dist1.d i0 then 1 else 0) =
           \sum_(i0 <- finsupp x | i == Dist1.d i0) x i0
    by apply eq_bigr=> a0 ->; rewrite mulR1.
  rewrite addR0.
  have/eqP -> : \bigcup_(d <- [fset Dist1.d (Dist1.d a) | a in finsupp x])
                 finsupp d  == [fset Dist1.d a | a in finsupp x].
  + rewrite eqEfsubset; apply/andP=> []; split; apply/fsubsetP=> a'.
    * case/bigfcupP=> x0' /andP [].
      case/imfsetP=> x1 /= Hx1 -> _.
      rewrite Dist1.supp inE=> /eqP ->.
      by apply/imfsetP; exists x1.
    * case/imfsetP=> x0' /= Hx0' ->; apply/bigfcupP.
      exists (Dist1.d (Dist1.d x0')) => //=; last by rewrite Dist1.supp inE.
      rewrite andbT; apply/imfsetP.
      by exists x0' => //; rewrite Dist1.supp inE.
  case: ifP.
  + case/imfsetP=> a' /= Ha' ia'; rewrite ia'.
    have-> : \sum_(i0 <- finsupp x | Dist1.d a' == Dist1.d i0) x i0 =
             \sum_(i0 <- finsupp x | a' == i0) x i0.
    * apply eq_bigl=> i0.
      apply/eqP; case: ifP; first by move/eqP ->.
      by move=> H /eq_Dist1 /eqP; rewrite H.
    have-> : \sum_(i0 <- finsupp x | a' == i0) x i0 =
             \sum_(i0 <- [:: a']) x i0 by admit.
    rewrite big_seq1.
    move: ia; rewrite ax0; rewrite Dist1.supp => /imfsetP [] x1 /=.
    rewrite inE => /eqP x1x0 ix1.
    by move: x1x0; rewrite -ix1 ia' => /eq_Dist1 ->.
  + move: ia; rewrite ax0 Dist1.supp=> /imfsetP [] x1 /=.
    rewrite inE=> /eqP x1x0 ix1.
    rewrite ix1 x1x0 /=.
    by rewrite in_imfset.
rewrite /F.
have H : finsupp (Distfmap (Dist1.d (A:=c)) x) =
         (@Dist1.d _) @` (finsupp x) by admit.
have H' : forall i, Dist1.d (Yx0 i) = fsval i by admit.
have H'' : forall x0 : FId c, Dist1.d x0 \in finsupp (Distfmap (@Dist1.d c) x)
    by admit.
set x0Y := fun x0 : FId c => FSetSub (H'' x0). 
have H''' : forall x0 : FId c, Yx0 (x0Y x0) = x0 by admit.
set D := Yx0 @` (dist_of_Dist.D (Distfmap (Dist1.d (A:=c)) x)).
Check D.
Check fun j : D => j.
Check \ssum_(j <- D) scalept (x j) (S1 (fsval (x0Y j))).
Check \ssum_(j : D) scalept (x (fsval j)) (S1 (fsval (x0Y (fsval j)))).
Check (@fsval ((@FId choiceType_category) c) D).
have -> : \ssum_i scalept (x (Yx0 i)) (S1 (fsval i)) =
          \ssum_(j <- D) scalept (x j) (S1 (fsval (x0Y j))) by admit.
Fail rewrite -S1_Convn_indexed_over_finType.
Admitted.

Lemma triR0 d : (G # eps0 d) \o (eta0 (G d)) = idfun.
Admitted.

End eps0_eta0.

Section join0.
Import category.
(* join operator for Dist *)
Definition join0 (C : choiceType) (d : Dist (Dist C)) : Dist C :=
  DistBind.d d (Dist_mor [hom of idfun]).

(* join0 is ((coercion) \o eps0) *)
Section eps0_correct.
Import ScaledConvex.
Local Open Scope R_scope.

Lemma eps0_correct (C : choiceType) (d : Dist (Dist C)) : eps0'' d = join0 d.
Proof.
rewrite /join0 -DistBindA DistBindp1; apply Dist_ext => c.
rewrite -[LHS]Scaled1RK /eps0''.
rewrite (@S1_proj_Convn_indexed_over_finType _ _ (fun D : Dist C => D c));
  last exact: Dist_eval_affine.
rewrite big_scaleR.
rewrite DistBind.dE /DistBind.f fsfunE.
case: ifP => [_ | ].
- transitivity (\sum_(i : dist_of_Dist.D d | true) d (fsval i) * (fsval i) c).
  + apply eq_bigr => -[v vP] _.
    move/scaleR_scalept:(dist_ge0 (dist_of_Dist d) [` vP]%fset) ->.
    by rewrite Scaled1RK dist_of_DistE.
  suff -> : finsupp d = [seq fsval i | i in [finType of finsupp d]] :> seq _
    by rewrite big_image; apply eq_bigl => a; rewrite inE.
  by rewrite enum_fsetE.
- rewrite !imfset_id.
  move/bigfcupP => H.
  have H' : forall i : Dist C, i \in finsupp d -> c \notin finsupp i
      by move=> i Hi; apply/negP => Hx; apply H; exists i => //; rewrite andbT.
  have H0 : 0 = \sum_(i | true) 0 by move=> t; rewrite big1.
  rewrite [in RHS](H0 (dist_of_Dist.D d)).
  apply eq_bigr => -[v vP] _.
  move/scaleR_scalept:(dist_ge0 (dist_of_Dist d) [`vP]%fset) ->.
  rewrite dist_of_DistE /= mul1R.
  suff -> : v c = 0 by rewrite mulR0.
  rewrite fsfun_dflt //.
  exact: H'.
Qed.
End eps0_correct.
End join0.

Section necset_functor.
Import category.

(* the morphism part of necset *)
Section necset_mor.
Variables (A B : convType) (f : {hom A , B}).

Definition necset_mor' : necset_convType A -> necset_convType B.
move=> car.
refine (NECSet.Pack (NECSet.Class (CSet.Class (@is_convex_set_image' _ _ f _ car)) (NESet.Class _))); first by case: f.
apply/set0P; exists (f (neset_repr car)) => /=.
exists (neset_repr car) => //; exact: repr_in_neset.
Defined.

(* the results of necset_mor are semiLattConvType-morphisms, i.e., are
   affine and preserve semilatt operations *)
Lemma necset_mor'_affine : affine_function necset_mor'.
Proof.
move=> a0 a1 p; apply necset_ext => /=; rewrite predeqE => b0; split.
- case=> a; rewrite necset_convType.convE => -[a0' [a1' [H0 [H1 ->{a}]]]] <-{b0}.
  rewrite necset_convType.convE; exists (f a0'); exists (f a1'); split.
    by rewrite in_setE /=; exists a0' => //; rewrite -in_setE.
  split; last by case: f => f' /= Hf; rewrite Hf.
  by rewrite in_setE /=; exists a1' => //; rewrite -in_setE.
- rewrite necset_convType.convE => -[b0' [b1']].
  rewrite !in_setE /= => -[[a0' H0] <-{b0'}] -[[a1' h1] <-{b1'}] ->{b0}.
  exists (a0' <|p|> a1').
  rewrite necset_convType.convE; exists a0', a1'; split; first by rewrite in_setE.
  by split => //; rewrite in_setE.
  by case: f => f' /= Hf; rewrite Hf.
Qed.

Lemma bigsetU_affine (X : neset (necset A)) :
  (f @` (\bigcup_(x in X) x) = \bigcup_(x in necset_mor' @` X) x)%classic.
Proof.
rewrite funeqE => b; rewrite propeqE; split.
- case => a [x Xx xa] <-{b}.
  have Hf : affine_function f by case: f.
  exists (NECSet.Pack
            (NECSet.Class
               (CSet.Class (@is_convex_set_image' _ _ f Hf x))
               (NESet.Class (neset_image_neq0 f x)))) => /=; last by exists a.
  by exists x => //=; exact/necset_ext.
- by case => b0 [a0 Xa0 <-{b0}] [a a0a <-{b}]; exists a => //; exists a0.
Qed.

Lemma necset_mor'_Joet_morph : Joet_morph necset_mor'.
Proof.
move=> /= X; apply necset_ext => /=; rewrite funeqE => b.
rewrite image_preserves_convex_hull'; last by case: f.
congr (hull _ b) => {b}.
exact: bigsetU_affine.
Qed.

Definition necset_mor :
  {hom necset_semiCompSemiLattConvType A, necset_semiCompSemiLattConvType B} :=
  locked (@Hom.Pack semiCompSemiLattConvType_category _ _ _ necset_mor' (JoetAffine.Class necset_mor'_affine necset_mor'_Joet_morph)).

Lemma necset_morE (X : necset_convType A) :
  NECSet.mixinType (necset_mor X) = image_neset f X.
Proof. by rewrite /necset_mor; unlock; apply neset_ext. Qed.

Lemma necset_morE' (X : necset_convType A) :
  NESet.car (NECSet.mixinType (necset_mor X)) = image_neset f X.
Proof. by rewrite /necset_mor; unlock. Qed.
End necset_mor.

(*
Definition Joet_affine_hom (T U : semiCompSemiLattConvType)
           (f : {Joet_affine T -> U}) : {hom T, U}.
apply (@Hom.Pack semiCompSemiLattConvType_category _ _ _ f).
rewrite /Hom.axiom /=.
by case: f.
Defined.
Definition convType_hom_affine (T U : convType) (f : {hom T, U}) :
  {affine T -> U}.
apply (@AffineFunction.Pack _ _ _ f).
by case: f.
Defined.
Definition necset_actm (T U : convType) (f : {hom T, U}) :
  {hom necset_semiCompSemiLattConvType T, necset_semiCompSemiLattConvType U} :=
  Joet_affine_hom (necset_mor (convType_hom_affine f)).
*)

Lemma necset_mor_id : FunctorLaws.id necset_mor.
Proof.
move=> a; rewrite hom_ext funeqE=> /= x /=.
apply necset_ext => /=.
by rewrite necset_morE' /= image_idfun.
Qed.
Lemma necset_mor_comp : FunctorLaws.comp necset_mor.
Proof.
move=> a b c [] g affine_g [] h affine_h; rewrite hom_ext funeqE => /= x /=.
apply necset_ext => /=.
rewrite 2!necset_morE' /= -imageA.
congr image.
by rewrite necset_morE'.
Qed.

Definition necset_functor :=
  Functor.Pack (Functor.Class necset_mor_id necset_mor_comp).

Lemma necset_mor_comp_fun (a b c : convType) (g : {hom b, c})
      (h : {hom a, b}):
  [fun of necset_mor [hom of [fun of g] \o [fun of h]]] =
  [fun of necset_mor g] \o [fun of necset_mor h].
Proof. by rewrite necset_mor_comp. Qed.

Local Notation CS := semiCompSemiLattConvType_category.
Local Notation CV := convType_category.

Definition forget_semiCompSemiLattConvType : functor CS CV.
set (m := [eta FId] : CS -> CV).
set (h := fun (a b : CS) (f : {hom CS; a, b}) =>
             @Hom.Pack CV a b _ (FId # f) (JoetAffine.base (Hom.class (FId # f))) : {hom CV; m a , m b}).
refine (@Functor.Pack CS CV m _).
refine (@Functor.Class _ _  m h  _ _); by move=> *; apply hom_ext. 
Defined.

Lemma forget_semiCompSemiLattConvTypeE :
  (forall a : CS, forget_convType a = a)
  /\ (forall a b (f : {hom CS; a , b}), forget_semiCompSemiLattConvType # f = f :> (a -> b)).
Proof. done. Qed.
End necset_functor.

(*
  eps1 is the counit of the adjunction (necset -| coercion),
  where the coercion is from semiCompSemiLattConvType to convType.
*)
Section eps1_eta1.
Import category.
Local Open Scope classical_set_scope.

Definition eps1'' {L : semiCompSemiLattConvType}
           (X : necset_semiCompSemiLattConvType L) : L := Joet `NE X.

Lemma eps1''_Joet_morph L : Joet_morph (@eps1'' L).
Proof.
move=> F.
rewrite /eps1''.
transitivity (Joet `NE (Joet @` ((fun X : necset_semiCompSemiLattType L => `NE X) @` F))); last first.
- congr Joet.
  apply/neset_ext/eqEsubset => x [] x0 Fx0 <-.
  + by case: Fx0 => x1 Fx1 <-; exists x1.
  + by exists `NE x0 => // ; exists x0.
transitivity (Joet `NE (hull (\bigcup_(x in F) x)));
  first by congr Joet; apply neset_ext.
by rewrite Joet_hull Joet_bigcup.
Qed.

Lemma eps1''_affine L : affine_function (@eps1'' L).
Proof.
move=> X Y p.
rewrite /affine_function_at /eps1''.
transitivity (Joet `NE (conv_set p X Y)); last by rewrite Joet_conv_setD.
congr (Joet `NE _); apply/neset_ext => /=.
rewrite conv_setE necset_convType.convE.
apply eqEsubset=> u.
- case=> x [] y [] xX [] yY ->.
  exists x; first by rewrite -in_setE.
  by exists y; first by rewrite -in_setE.
- case=> x Xx [] y Yy <-.
  by exists x, y; rewrite !in_setE.
Qed.

Lemma eps1''_natural (K L : semiCompSemiLattConvType) (f : {hom K , L}) :
  f \o eps1'' =
  eps1'' \o (necset_functor \O forget_semiCompSemiLattConvType) # f.
Proof.
rewrite FCompE /= /id_f.
rewrite funeqE => X /=; rewrite apply_affine.
congr (Joet `NE _); by rewrite necset_morE.
Qed.

Definition eps1' : necset_functor \O forget_semiCompSemiLattConvType ~~> FId :=
  fun L => @Hom.Pack semiCompSemiLattConvType_category _ _ _ (@eps1'' L) (JoetAffine.Class (@eps1''_affine L) (@eps1''_Joet_morph L)).

Lemma eps1'_natural : naturality _ _ eps1'.
Proof. by move=> K L f; rewrite eps1''_natural. Qed.

Definition eps1 : necset_functor \O forget_semiCompSemiLattConvType ~> FId :=
  locked (Natural.Pack (Natural.Class eps1'_natural)).

Lemma eps1E': eps1 = Natural eps1'_natural.
Proof. by rewrite /eps1; unlock. Qed.
Lemma eps1E (L : semiCompSemiLattConvType) :
  eps1 L = (fun X => Joet `NE X) :> (_ -> _).
Proof. by rewrite /eps1; unlock. Qed.

Definition eta1'' (C : convType) (x : C) : necset_convType C := necset1 x.
Lemma eta1''_affine (C : convType) : affine_function (@eta1'' C).
Proof.
move=> a b p; rewrite /affine_function_at /eta1'' /=.
apply/necset_ext/eqEsubset=> x /=.
- move->; rewrite necset_convType.convE.
  by exists a, b; rewrite !inE !asboolE /necset1 /=.
- rewrite necset_convType.convE => -[] a0 [] b0.
  by rewrite !inE !asboolE /necset1 /= => -[] -> [] -> ->.
Qed.
Definition eta1' : FId ~~> forget_semiCompSemiLattConvType \O necset_functor :=
  fun C => @Hom.Pack convType_category _ _ _ (@eta1'' C) (@eta1''_affine C).
Lemma eta1'_natural : naturality _ _ eta1'.
Proof.
move=> a b h; rewrite funeqE=> x; apply necset_ext => /=.
by rewrite /eta1' /= /id_f necset_morE'/= image_set1.
Qed.
Definition eta1 : FId ~> forget_semiCompSemiLattConvType \O necset_functor :=
  locked (Natural.Pack (Natural.Class eta1'_natural)).
Lemma eta1E': eta1 = Natural eta1'_natural.
Proof. by rewrite /eta1; unlock. Qed.
Lemma eta1E (C : convType) : eta1 C = (@necset1 _) :> (_ -> _).
Proof. by rewrite /eta1; unlock. Qed.

Import homcomp_notation.
Local Notation F := necset_functor.
Local Notation G := forget_semiCompSemiLattConvType.
Lemma triL1 c : (eps1 (F c)) \o (F # eta1 c) = idfun.
Admitted.
Lemma triR1 d : (G # eps1 d) \o (eta1 (G d)) = idfun.
Admitted.

End eps1_eta1.

Section join1.
Definition join1' (C : convType) (s : necset (necset_convType C)) : {convex_set C} :=
  CSet.Pack (CSet.Class (convex_hull (bigsetU s (fun x => if x \in s then (x : set _) else cset0 _)))).

Lemma join1'_neq0 (C : convType) (s : necset (necset_convType C)) : join1' s != set0 :> set _.
Proof.
rewrite hull_eq0 set0P.
case/set0P: (neset_neq0 s) => y.
case/set0P: (neset_neq0 y) => x yx sy.
exists x; exists y => //.
rewrite -in_setE in sy.
by rewrite sy.
Qed.

Definition join1 (C : convType) (s : necset (necset_convType C)) : necset C :=
  NECSet.Pack (NECSet.Class (CSet.Class (convex_hull _)) (NESet.Class (join1'_neq0 s))).

Lemma eps1_correct (C : convType) (s : necset (necset_convType C)) :
  eps1'' s = join1 s.
Proof.
rewrite /eps1'' /join1 /=; apply/necset_ext => /=; congr (hull _).
rewrite /bigsetU; rewrite funeqE => c; rewrite propeqE; split.
- by case=> X sX Xc; exists X => //; rewrite -in_setE in sX; rewrite sX.
- by case=> X sX; rewrite -in_setE in sX; rewrite sX => Xc; exists X => //; rewrite -in_setE.
Qed.
End join1.

(* TODO: move? *)
Lemma NECSet_mixinType_inj (A : convType) (a b : necset A) :
  NECSet.mixinType a = NECSet.mixinType b -> a = b.
Proof.
move: a b => -[a Ha] [b Hb] /= [ab]; subst a; congr NECSet.Pack; exact/Prop_irrelevance.
Qed.

(* (* NB(saikawa): this is just the functoriality of necset_functor *)
(* TODO: move? *)
Lemma necset_mor_eps0_Dist_mor (K L : convType) (f : {affine K -> L}) :
  necset_mor f \o necset_mor eps0 = necset_mor (affine_function_comp (Dist_mor f) eps0).
Proof.
rewrite funeqE => /= X.
apply NECSet_mixinType_inj; rewrite !necset_morE.
by apply/neset_ext => /=; rewrite imageA (eps0_natural f).
Qed.
*)

Section P_delta_functor.
Import category.
(* P_delta = (forget) \o necset \o Dist \o gen_choiceType, where
   - gen_choiceType is the free choiceType functor,
   - Dist is the free convex space functor, and
   - necset is the convex powerset functor. *)

Definition P_delta_left :=
  necset_functor \O Dist_functor \O gen_choiceType_functor.

Definition P_delta_right :=
  forget_choiceType
    \O forget_convType
    \O forget_semiCompSemiLattConvType.

(* action on objects *)
Definition P_delta_acto (T : Type) : Type := P_delta_left T.

Definition P_delta : functor Type_category Type_category :=
  P_delta_right \O P_delta_left.

Lemma eps0_Dist1 (A : Type) (d : P_delta_acto A) : eps0 _ (Dist1.d d) = d.
Proof.
rewrite eps0E; apply: (@ScaledConvex.S1_inj _ _ d).
rewrite S1_Convn_indexed_over_finType /=.
rewrite (eq_bigr (fun=> ScaledConvex.S1 d)); last first.
  move=> i _; rewrite dist_of_DistE Dist1.dE /Dist1.f fsfunE /= -(Dist1.supp d).
  rewrite fsvalP ScaledConvex.scalept1 /=; congr (ScaledConvex.S1 _).
  case: i => i Hi /=; rewrite Dist1.supp inE in Hi; exact/eqP.
by rewrite big_const (_ : #| _ | = 1) // -cardfE Dist1.supp cardfs1.
Qed.
End P_delta_functor.

Section P_delta_category_monad.
Import category.

Local Notation F1 := necset_functor.
Local Notation F0 := Dist_functor.
Local Notation FC := gen_choiceType_functor.
Local Notation UC := forget_choiceType.
Local Notation U0 := forget_convType.
Local Notation U1 := forget_semiCompSemiLattConvType.

Definition eps : P_delta_left \O P_delta_right ~> FId :=
  locked
  (eps1
     \v [NId F1 \O FId \O U1 , F1 \O U1]
     \v ((NId F1) \h eps0 \h (NId U1))
     \v [NId F1 \O F0 \O FId \O U0 \O U1 , F1 \O (F0 \O U0) \O U1 ]
     \v ((NId F1) \h (NId F0)\h epsC \h (NId U0) \h (NId U1))
     \v [NId P_delta_left \O P_delta_right , F1 \O F0 \O (FC \O UC) \O U0 \O U1]
  ).
Definition ret : FId ~> P_delta :=
  locked
  ([NId UC \O U0 \O (U1 \O F1) \O F0 \O FC , P_delta]
     \v ((NId UC) \h (NId U0) \h eta1 \h (NId F0) \h (NId FC))
     \v [NId UC \O (U0 \O F0) \O FC , UC \O U0 \O FId \O F0 \O FC]
     \v ((NId UC) \h eta0 \h (NId FC))
     \v [NId UC \O FC , UC \O FId \O FC]
     \v etaC
  ).

Import homcomp_notation.

Lemma epsE' :
  eps =
  eps1
    \v [NId F1 \O FId \O U1 , F1 \O U1]
    \v ((NId F1) \h eps0 \h (NId U1))
    \v [NId F1 \O F0 \O FId \O U0 \O U1 , F1 \O (F0 \O U0) \O U1 ]
    \v ((NId F1) \h (NId F0) \h epsC \h (NId U0) \h (NId U1))
    \v [NId P_delta_left \O P_delta_right , F1 \O F0 \O (FC \O UC) \O U0 \O U1].
Proof. by rewrite /eps; unlock. Qed.
Lemma retE' :
  ret =
  [NId UC \O U0 \O (U1 \O F1) \O F0 \O FC , P_delta]
     \v ((NId UC) \h (NId U0) \h eta1 \h (NId F0) \h (NId FC))
     \v [NId UC \O (U0 \O F0) \O FC , UC \O U0 \O FId \O F0 \O FC]
     \v ((NId UC) \h eta0 \h (NId FC))
     \v [NId UC \O FC , UC \O FId \O FC]
     \v etaC.
Proof. by rewrite /ret; unlock. Qed.

Lemma epsE'' (L : semiCompSemiLattConvType) : 
  eps L =
  [homcomp
     eps1 L
   , ((NId F1) \h eps0 \h (NId U1)) L
   , ((NId F1) \h (NId F0) \h epsC \h (NId U0) \h (NId U1)) L] :> (_ -> _).
Proof. by rewrite epsE'. Qed.

Lemma epsE (L : semiCompSemiLattConvType) :
  eps L =
  ((eps1 _) \o (necset_mor (eps0 _)) \o (necset_mor (Dist_mor (epsC _))))
    :> (_ -> _).
Proof.
rewrite epsE''; cbn.
congr funcomp; congr funcomp.
- rewrite 2!HCompE 2!homcomp_hom homcompA -functor_o_fun.
  rewrite !NIdE funcompidf functor_id.
  by congr [fun of necset_mor _]; rewrite hom_ext /= funcompfid.
- do 2 rewrite HCompE homcomp_hom NIdE functor_id funcompfid.
  by rewrite HCompE homcomp_hom -NIdO_HComp NIdE funcompidf.
Qed.

Lemma retE'' (T : Type) :
  ret T =
  [homcomp
     ((NId UC) \h (NId U0) \h eta1 \h (NId F0) \h (NId FC)) T
   , ((NId UC) \h eta0 \h (NId FC)) T
   , etaC T] :> (_ -> _).
Proof. by rewrite retE'. Qed.

Lemma retE (T : Type) :
  ret T = (@necset1 _) \o (@Dist1.d (gen_choiceType T)) :> (_ -> _).
Proof.
rewrite funeqE => x; apply necset_ext.
by rewrite /ret; unlock; rewrite /= etaCE eta0E eta1E /Distfmap /= DistBind1f.
Qed.

Definition join : P_delta \O P_delta ~> P_delta :=
  [NId P_delta_right \O FId \O P_delta_left, P_delta]
    \v ((NId P_delta_right) \h eps \h (NId P_delta_left))
    \v [NId P_delta \O P_delta ,
        (P_delta_right \O (P_delta_left \O P_delta_right)) \O P_delta_left].

Lemma joinE' (T : Type) :
  join T = ((NId P_delta_right) \h eps \h (NId P_delta_left)) T :> (_ -> _).
Proof. reflexivity. Qed.

Lemma joinE (T : Type) :
  join T = @eps (P_delta_left T) :> (_ -> _).
Proof.
rewrite /join.
do ! rewrite VCompE homcomp_hom.
rewrite funcompfid funcompidf.
rewrite HCompE homcomp_hom NIdE functor_id funcompfid.
by rewrite HCompE homcomp_hom NIdE funcompidf.
Qed.

Lemma ret_natural : JoinLaws.ret_naturality ret.
Proof. exact: (natural ret). Qed.
Lemma join_natural : JoinLaws.join_naturality join.
Proof. exact: (natural join). Qed.
Lemma join_left_unit : JoinLaws.join_left_unit ret join.
Proof.
rewrite /JoinLaws.join_left_unit => a.
rewrite funeqE=> d.
rewrite -homcompE joinE retE.
rewrite epsE funcompE -homcompE eps1E.
rewrite -[in RHS](Joet1 d); congr (Joet `NE _).
rewrite 2!necset_morE; apply/neset_ext => /=.
rewrite 2!image_set1 /Distfmap DistBind1f /=.
by rewrite epsCE eps0_Dist1.
Qed.
Lemma join_right_unit : JoinLaws.join_right_unit ret join.
Proof.
Admitted.

Lemma joinA : JoinLaws.join_associativity join.
Proof.
rewrite /JoinLaws.join_associativity=> a.
rewrite 2![in RHS]joinE (natural eps _ _ (eps (P_delta_left a))).
rewrite joinE FCompE.
(* NB: maybe worth factoring out? *)
have-> :
  forall x y (f : {hom x, y}) , P_delta # f = P_delta_left # f :> (_ -> _)
    by move=> x y f; apply funext.
congr funcomp; congr [fun of P_delta_left # _].
by rewrite hom_ext joinE funeqE.
Qed.

Definition P_delta_monadMixin : Monad.mixin_of P_delta :=
  Monad.Mixin
    ret_natural
    join_natural
    join_left_unit
    join_right_unit
    joinA.
Definition m := Monad_of_category_monad
                  (Monad.Pack (Monad.Class P_delta_monadMixin)).
End P_delta_category_monad.

From monae Require Import monad fail_monad proba_monad.

Section P_delta_monad.
End P_delta_monad.

Section P_delta_altProbMonad.
Local Open Scope R_scope.
Local Open Scope classical_set_scope.
Local Open Scope proba_scope.
Local Open Scope convex_scope.
Local Open Scope latt_scope.

Definition alt A (x y : m A) : m A := x [+] y.
Definition choice p A (x y : m A) : m A := x <|p|> y.

Lemma altA A : associative (@alt A).
Proof. by move=> x y z; rewrite /alt joetA. Qed.
Lemma bindaltDl : BindLaws.left_distributive (@Bind m) alt.
Proof.
Admitted.

Definition P_delta_monadAltMixin : MonadAlt.mixin_of m :=
  MonadAlt.Mixin altA bindaltDl.
Definition mA : altMonad := MonadAlt.Pack (MonadAlt.Class P_delta_monadAltMixin).

Lemma altxx A : idempotent (@Alt mA A).
Proof. by move=> x; rewrite /Alt /= /alt joetxx. Qed.
Lemma altC A : commutative (@Alt mA A).
Proof. by move=> a b; rewrite /Alt /= /alt /= joetC. Qed.

Definition P_delta_monadAltCIMixin : MonadAltCI.class_of mA :=
  MonadAltCI.Class (MonadAltCI.Mixin altxx altC).
Definition mACI : altCIMonad := MonadAltCI.Pack P_delta_monadAltCIMixin.

Lemma choice0 A (x y : m A) : choice `Pr 0 x y = y.
Proof. by rewrite /choice conv0. Qed.
Lemma choice1 A (x y : m A) : choice `Pr 1 x y = x.
  (* NB(sai): redundant given choice0 and choiceC, isnt' it? NB(rei): yes*)
Proof. by rewrite /choice conv1. Qed.
Lemma choiceC A p (x y : m A) : choice p x y = choice `Pr p.~ y x.
Proof. by rewrite /choice convC. Qed.
Lemma choicemm A p : idempotent (@choice p A).
Proof. by move=> m; rewrite /choice convmm. Qed.
Lemma choiceA A (p q r s : prob) (x y z : m A) :
  p = (r * s) :> R /\ s.~ = (p.~ * q.~)%R ->
  choice p x (choice q y z) = choice s (choice r x y) z.
Proof.
case=> H1 H2.
case/boolP : (r == `Pr 0) => r0.
  have p0 : p = `Pr 0 by apply/prob_ext => /=; rewrite H1 (eqP r0) mul0R.
  rewrite p0 choice0 (eqP r0) choice0 (_ : q = s) //; apply/prob_ext => /=.
  by move: H2; rewrite p0 onem0 mul1R => /(congr1 onem); rewrite !onemK.
case/boolP : (s == `Pr 0) => s0.
  have p0 : p = `Pr 0 by apply/prob_ext => /=; rewrite H1 (eqP s0) mulR0.
  rewrite p0 (eqP s0) 2!choice0 (_ : q = `Pr 0) ?choice0 //; apply/prob_ext.
  move: H2; rewrite p0 onem0 mul1R (eqP s0) onem0 => /(congr1 onem).
  by rewrite onemK onem1.
rewrite /choice convA (@r_of_pq_is_r _ _ r s) //; congr ((_ <| _ |> _) <| _ |> _).
by apply/prob_ext; rewrite s_of_pqE -H2 onemK.
Qed.
Lemma bindchoiceDl p : BindLaws.left_distributive (@Bind m) (@choice p).
Admitted.

Definition P_delta_monadProbMixin : MonadProb.mixin_of m :=
  MonadProb.Mixin choice0 choice1 choiceC choicemm choiceA bindchoiceDl.
Definition P_delta_monadProbMixin' : MonadProb.mixin_of (Monad.Pack (MonadAlt.base (MonadAltCI.base (MonadAltCI.class mACI)))) := P_delta_monadProbMixin.

(*Definition mp : probMonad := MonadProb.Pack (MonadProb.Class P_delta_monadProbMixin).*)

Lemma choicealtDr A (p : prob) :
  right_distributive (fun x y : mACI A => choice p x y) (fun x y => Alt x y).
Proof. by move=> x y z; rewrite /choice joetDr. Qed.

Definition P_delta_monadAltProbMixin : @MonadAltProb.mixin_of mACI choice :=
  MonadAltProb.Mixin choicealtDr.
Definition P_delta_monadAltProbMixin' : @MonadAltProb.mixin_of mACI (MonadProb.choice P_delta_monadProbMixin) := P_delta_monadAltProbMixin.
Definition mAP : altProbMonad := MonadAltProb.Pack (MonadAltProb.Class P_delta_monadAltProbMixin').
End P_delta_altProbMonad.
