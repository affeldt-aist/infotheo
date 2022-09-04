(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg fingroup perm finalg matrix.
From mathcomp Require Import boolp classical_sets Rstruct.
From mathcomp Require Import ssrnum ereal.
Require Import Reals.
Require Import ssrR Reals_ext Ranalysis_ext ssr_ext ssralg_ext logb Rbigop.
Require Import fdist jfdist.
Import Order.POrderTheory Num.Theory.

(******************************************************************************)
(*                              Convexity                                     *)
(*                                                                            *)
(* This file provides the definition of convex spaces over a choiceType and   *)
(* of real cones, and use them to define convex sets, hulls, to show that     *)
(* probability distributions form convex spaces, and to define convex         *)
(* functions.                                                                 *)
(*                                                                            *)
(* Convex spaces:                                                             *)
(*        convType == the type of convex spaces, i.e., a choiceType with an   *)
(*                    operator x <| p |> y where p is a probability           *)
(*                    satisfying the following axioms:                        *)
(*           conv1 == a <| 1%:pr |> b = a.                                    *)
(*          convmm == a <| p |> a = a.                                        *)
(*           convC == a <| p |> b = b <| p.~%:pr |> a.                        *)
(*           convA == a <| p |> (b <| q |> c) =                               *)
(*                    (a <| [r_of p, q] |> b) <| [s_of p, q] |> c.            *)
(* {affine T -> U} == affine function: homomorphism between convex spaces     *)
(*         <|>_d f == generalization of the operator . <| . |> . over a       *)
(*                    finite distribution d : {fdist 'I_n} for a sequence of  *)
(*                    points f : 'I_n -> A, where A is a convType             *)
(*         <$>_d f == indexed over a finType rather than the type of an       *)
(*                    ordinal as in Convn; defined as <|>_d (f \o enum_val)   *)
(*                    with d a finite distribution over a finite type T and f *)
(*                    a function from T to some convType A                    *)
(*                                                                            *)
(* Module ScaledConvex == the canonical embedding of convex spaces into real  *)
(*                        cones                                               *)
(* The type scale_pt associated with add_pt and scalept define a real cone    *)
(* [Varacca & Winskel, MSCS, 2006]:                                           *)
(*      scaled_pt == Zero or a pair of a positive real with a point in a      *)
(*                   convType (i.e., a "scaled point")                        *)
(*         add_pt == the addition of scaled points, i.e.,                     *)
(*                   rx + qy = (r+q)(x <| r/(r+q) |> y)                       *)
(*        scalept == scaling of a scaled point, i.e.,                         *)
(*                   scalept r qy = (r*q)y                                    *)
(*                                                                            *)
(* More lemmas about convex spaces, including key lemmas by Stone:            *)
(*        convACA == the entropic identity, i.e.,                             *)
(*                      (a <|q|> b) <|p|> (c <|q|> d) =                       *)
(*                      (a <|p|> c) <|q|> (b <|p|> d)                         *)
(*                                                                            *)
(*         hull X == the convex hull of set X : set T where T is a convType   *)
(*  is_convex_set == Boolean predicate that characterizes convex sets over a  *)
(*                   convType                                                 *)
(* {convex_set A} == an object X of type "set A" where A is a convType and X  *)
(*                   is convex                                                *)
(*                                                                            *)
(* Instances of convex spaces:                                                *)
(*      R_convType == R                                                       *)
(*     funConvType == functions A -> B with A a choiceType and B a convType   *)
(*  depfunConvType == functions forall (a:A), B a with A a choiceType and B i *)
(*                    is a A -> convType                                      *)
(*    pairConvType == pairs of convTypes                                      *)
(*  fdist_convType == finite distributions                                    *)
(*                                                                            *)
(* orderedConvType == a convType augmented with an order                      *)
(* Instances: R, T -> U (T convType, U orderedConvType), opposite (see mkOpp) *)
(*                                                                            *)
(* Reference: R. Affeldt, J. Garrigue, T. Saikawa. Formal adventures in       *)
(* convex and conical spaces. CICM 2020                                       *)
(*                                                                            *)
(* Definitions of convex, concave, affine functions                           *)
(*   affine_functionP == a function is affine iff it is convex and concave    *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(* image_preserves_convex_hull == the image of a convex hull is the convex    *)
(*                                hull of the image                           *)
(*                                                                            *)
(* Application to real analysis:                                              *)
(* Definition of convex sets for R                                            *)
(* Lemma second_derivative_convexf_pt == twice derivable is convex            *)
(******************************************************************************)

Reserved Notation "x <| p |> y" (format "x  <| p |>  y", at level 49).
Reserved Notation "{ 'convex_set' T }" (format "{ 'convex_set'  T }").
Reserved Notation "'<|>_' d f" (at level 36, f at level 36, d at level 0,
  format "<|>_ d  f").
Reserved Notation "'<$>_' d f" (at level 36, f at level 36, d at level 0,
  format "<$>_ d  f").
Reserved Notation "\ssum_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
  format "'[' \ssum_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\ssum_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
  format "'[' \ssum_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\ssum_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
  format "'[' \ssum_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\ssum_ i F"
  (at level 41, F at level 41, i at level 0, right associativity,
  format "'[' \ssum_ i '/  '  F ']'").
Reserved Notation "\ssum_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\ssum_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
  format "'[' \ssum_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\ssum_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
  format "'[' \ssum_ ( i  <  n ) '/  '  F ']'").

Declare Scope convex_scope.
Declare Scope ordered_convex_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.

(* TODO: the following lemmas are currently not in use. Maybe remove? *)
Section tmp.
Lemma ConvnFDist_Add
      (n m : nat) (d1 : {fdist 'I_n}) (d2 : {fdist 'I_m}) (p : prob)
      (A : finType) (g : 'I_n -> fdist A) (h : 'I_m -> fdist A) :
  ConvnFDist.d (AddFDist.d d1 d2 p)
    [ffun i => match fintype.split i with inl a => g a | inr a => h a end] =
  ConvFDist.d p (ConvnFDist.d d1 g) (ConvnFDist.d d2 h).
Proof.
apply/fdist_ext => a; rewrite !ConvFDist.dE !ConvnFDist.dE.
rewrite 2!big_distrr /= big_split_ord /=; congr (_ + _)%R;
  apply eq_bigr => i _; rewrite AddFDist.dE ffunE.
case: splitP => /= j ij.
rewrite mulRA; congr (_ * d1 _ * (g _) a)%R; exact/val_inj.
move: (ltn_ord i); by rewrite ij -ltn_subRL subnn ltn0.
case: splitP => /= j ij.
move: (ltn_ord j); by rewrite -ij -ltn_subRL subnn ltn0.
move/eqP : ij; rewrite eqn_add2l => /eqP ij.
rewrite mulRA; congr (_ * d2 _ * (h _) a)%R; exact/val_inj.
Qed.

Lemma DelDistConvex
      (A : finType) (n : nat) (g : 'I_n.+1 -> fdist A) (P : {fdist 'I_n.+1})
      (j : 'I_n.+1) (H : (0 <= P j <= 1)%R) (Pj1 : P j != 1%R) :
  let g' := fun i : 'I_n => g (DelFDist.f j i) in
  ConvnFDist.d P g =
    ConvFDist.d (Prob.mk_ H) (g j) (ConvnFDist.d (DelFDist.d Pj1) g').
Proof.
move=> g' /=; apply/fdist_ext => a.
rewrite ConvFDist.dE /= ConvnFDist.dE (bigD1 j) //=; congr (_ + _)%R.
rewrite ConvnFDist.dE big_distrr /=.
rewrite (bigID (fun i : 'I_n.+1 => (i < j)%nat)) //= (bigID (fun i : 'I_n => (i < j)%nat)) //=; congr (_ + _)%R.
  rewrite (@big_ord_narrow_cond _ _ _ j n.+1); first by rewrite ltnW.
  move=> jn; rewrite (@big_ord_narrow_cond _ _ _ j n xpredT); first by rewrite -ltnS.
  move=> jn'.
  apply/eq_big.
  by move=> /= i; apply/negP => /eqP/(congr1 val) /=; apply/eqP; rewrite ltn_eqF.
  move=> /= i _.
  rewrite DelFDist.dE /= ltn_ord D1FDist.dE /= ifF /=; last first.
    by apply/negP => /eqP/(congr1 val) /=; apply/eqP; rewrite ltn_eqF.
  rewrite mulRA mulRCA mulRV ?mulR1 ?onem_neq0 //.
  congr (P _ * _)%R; first exact/val_inj.
  rewrite /g' /DelFDist.f /= ltn_ord; congr (g _ a); exact/val_inj.
rewrite (eq_bigl (fun i : 'I_n.+1 => (j < i)%nat)); last first.
  move=> i; by rewrite -leqNgt eq_sym -ltn_neqAle.
rewrite (eq_bigl (fun i : 'I_n => (j <= i)%nat)); last first.
  move=> i; by rewrite -leqNgt.
rewrite big_mkcond.
rewrite big_ord_recl ltn0 /= add0R.
rewrite [in RHS]big_mkcond.
apply eq_bigr => i _.
rewrite /bump add1n ltnS; case: ifPn => // ji.
rewrite DelFDist.dE D1FDist.dE ltnNge ji /= ifF; last first.
  apply/eqP => /(congr1 val) => /=.
  rewrite /bump add1n => ij.
  move: ji; apply/negP; by rewrite -ij ltnn.
rewrite /Rdiv mulRAC [in RHS] mulRC -mulRA mulVR // ?mulR1 ?onem_neq0 //.
by rewrite /g' /DelFDist.f ltnNge ji.
Qed.
End tmp.

Module CodomDFDist.
Section def.
Local Open Scope classical_set_scope.
Variables (A : Type) (n : nat) (g : 'I_n -> A) (e : {fdist 'I_n}) (y : set A).
Definition f := [ffun i : 'I_n => if g i \in y then e i else 0%R].
Lemma f0 i : (0 <= f i)%R.
Proof. rewrite /f ffunE; case: ifPn => _ //; exact/leRR. Qed.
Lemma f1 (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, x (g i) -> e i = 0%R) :
  (\sum_(i < n) f i = 1)%R.
Proof.
rewrite /f -(FDist.f1 e) /=.
apply eq_bigr => i _; rewrite ffunE.
case: ifPn => // /negP; rewrite in_setE => ygi.
rewrite ge //.
have : (x `|` y) (g i) by apply/gX; by exists i.
by case.
Qed.
Definition d (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, x (g i) -> e i = 0%R) : {fdist 'I_n} :=
  locked (FDist.make f0 (f1 gX ge)).
Lemma dE (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, x (g i) -> e i = 0%R) i :
  d gX ge i = if g i \in y then e i else 0%R.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
Lemma f1' (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, (x (g i)) /\ (~ y (g i)) -> e i = 0%R) :
  (\sum_(i < n) f i = 1)%R.
Proof.
rewrite /f -(FDist.f1 e) /=; apply eq_bigr => i _; rewrite ffunE.
case: ifPn => // /negP; rewrite in_setE => giy.
rewrite ge //.
have : (x `|` y) (g i) by apply/gX; by exists i.
by case.
Qed.
Definition d' (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, (x (g i)) /\ (~ y (g i)) -> e i = 0%R) :=
  locked (FDist.make f0 (f1' gX ge)).
Lemma dE' (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, (x (g i)) /\ (~ y (g i)) -> e i = 0%R) i :
  d' gX ge i = if g i \in y then e i else 0%R.
Proof. by rewrite /d'; unlock; rewrite ffunE. Qed.
End def.
End CodomDFDist.

Module isConvexSpace_.
HB.mixin Record isConvexSpace (T : Type) := {
  convexspacechoiceclass : Choice.class_of T ;
  conv : prob -> T -> T -> T ;
  conv1 : forall a b, conv 1%:pr a b = a ;
  convmm : forall p a, conv p a a = a ;
  convC : forall p a b, conv p a b = conv p.~%:pr b a;
  convA : forall (p q : prob) (a b c : T),
      conv p a (conv q b c) = conv [s_of p, q] (conv [r_of p, q] a b) c }.

#[short(type=convType)]
HB.structure Definition ConvexSpace := {T of isConvexSpace T }.
End isConvexSpace_.
Export -(coercions) isConvexSpace_.

Coercion ConvexSpace.isConvexSpace__isConvexSpace_mixin :
  ConvexSpace.axioms_ >-> isConvexSpace.axioms_.

Canonical conv_eqType (T : convType) :=
  Eval hnf in EqType (ConvexSpace.sort T) convexspacechoiceclass.
Canonical conv_choiceType (T : convType) :=
  Eval hnf in ChoiceType (ConvexSpace.sort T) convexspacechoiceclass.
Coercion conv_choiceType : convType >-> choiceType.

Notation "a <| p |> b" := (conv p a b) : convex_scope.

Local Open Scope convex_scope.

Section convex_space_lemmas.
Variables A : convType.
Implicit Types a b : A.

Lemma conv0 a b : a <| 0%:pr |> b = b.
Proof.
by rewrite convC /= (_ : _ %:pr = 1%:pr) ?conv1 //; apply/val_inj/onem0.
Qed.
End convex_space_lemmas.

Section segment.
Variable A: convType.
Definition segment (x y: A) := image (@setT prob) (fun p => Conv p x y).

Lemma segment_sym u v x : segment u v x -> segment v u x.
Proof. by move=> [p _ <-]; exists (p.~%:pr); rewrite -?convC. Qed.

Lemma segmentC u v : segment u v = segment v u.
Proof. by rewrite eqEsubset; split=>x; apply segment_sym. Qed.

Lemma segmentL x y : segment x y x.
Proof. by exists 1%:pr; rewrite ?conv1. Qed.

Lemma segmentR x y : segment x y y.
Proof. by exists 0%:pr; rewrite ?conv0. Qed.
End segment.

Section convn.
Variable A : convType.
Fixpoint Convn n : {fdist 'I_n} -> ('I_n -> A) -> A :=
  match n return forall (e : {fdist 'I_n}) (g : 'I_n -> A), A with
  | O => fun e g => False_rect A (fdistI0_False e)
  | m.+1 => fun e g =>
    match Bool.bool_dec (e ord0 == 1%R) true with
    | left _ => g ord0
    | right H => let G := fun i => g (DelFDist.f ord0 i) in
      g ord0 <| probfdist e ord0 |> Convn (DelFDist.d (Bool.eq_true_not_negb _ H)) G
    end
  end.

End convn.
Notation "'<|>_' d f" := (Convn d f) : convex_scope.

(* Affine function: homomorphism between convex spaces *)

Definition affine (U V : convType) (f : U -> V) :=
  forall p, {morph f : a b / a <| p |> b >-> a <| p |> b}.

HB.mixin Record isAffine (U V : convType) (f : U -> V) := {
  affine_conv : affine f }.

HB.structure Definition Affine (U V : convType) :=
  {f of isAffine U V f}.

Notation "{ 'affine'  T '->'  R }" :=
  (Affine.type T R) (at level 36, T, R at next level,
    format "{ 'affine'  T  '->'  R }") : convex_scope.

Section affine_function_prop0.
Variables (U V W : convType) (f : {affine V -> W}) (h : {affine U -> V}).

Fact idfun_is_affine : affine (@idfun U).
Proof. by []. Qed.
HB.instance Definition _ (*idfun_affine*) := isAffine.Build _ _ idfun idfun_is_affine.

Fact comp_is_affine : affine (f \o h).
Proof. by move=> x y t /=; rewrite 2!affine_conv. Qed.
HB.instance Definition _ (*comp_affine*) := isAffine.Build _ _ (f \o h) comp_is_affine.

(* The following lemma is placed far below in this file
   since it is proved using ScaledConvex

Lemma affine_function_Sum T U (f : {affine T -> U}) n (g : 'I_n -> T) (d : {fdist 'I_n}) :
  f (<|>_d g) = <|>_d (f \o g).
*)

End affine_function_prop0.

(* TODO: this section is too long and contains lemmas to be moved to other files *)
Module ScaledConvex.
Section scaled_convex.
Variable A : convType.
Local Open Scope R_scope.
Local Open Scope convex_scope.

(* Note: we need the argument of Scaled to be an Rpos, because otherwise
   addpt cannot make a commutative monoid:
   1) if addpt (Scaled 0 x) (Scaled 0 y) = Scaled 0 x commutativity fails
      so at least we need addpt (Scaled 0 x) (Scaled 0 y) = Zero
   2) if addpt (Scaled 0 x) Zero = Zero then left/right identity fail
   2) if addpt (Scaled 0 x) Zero = Scaled 0 x then associativity fails
      addpt (Scaled 0 x) (addpt (Scaled 0 y) (Scaled 0 z)) = Scaled 0 x
      addpt (addpt (Scaled 0 x) (Scaled 0 y)) (Scaled 0 z) = Scaled 0 z
   So we cannot allow 0 as argument to Scaled.                             *)

Inductive scaled_pt := Scaled of Rpos & A | Zero.

Definition sum_of_scaled_pt (m : scaled_pt) : Rpos * A + unit :=
  match m with Scaled r a => inl _ (r, a) | Zero => inr _ tt end.

Definition scaled_pt_of_sum (m : (Rpos * A) + unit) :=
  match m with inl p => Scaled p.1 p.2 | inr n => Zero end.

Lemma sum_of_scaled_ptK : cancel sum_of_scaled_pt scaled_pt_of_sum.
Proof. by case. Qed.

Definition scaled_pt_eqMixin := CanEqMixin sum_of_scaled_ptK.
Canonical scaled_pt_eqType := Eval hnf in EqType scaled_pt scaled_pt_eqMixin.
Definition scaled_pt_choiceMixin := CanChoiceMixin sum_of_scaled_ptK.
Canonical scaled_pt_choiceType := Eval hnf in ChoiceType scaled_pt scaled_pt_choiceMixin.
Canonical scaled_pt_pointedType := PointedType _ Zero.

Local Notation "p *: a" := (Scaled p a).

Definition S1 (a  : A) : scaled_pt := 1%:pos *: a.

Lemma S1_neq0 a : S1 a != Zero. Proof. by []. Qed.

Lemma Scaled_inj p : injective (Scaled p).
Proof. by move=> x y []. Qed.

Definition S1_inj : injective S1 := @Scaled_inj Rpos1.

Definition raw_weight pt : R :=
  if pt is r *: _ then r else 0.

Lemma weight_ge0 pt : 0 <= raw_weight pt.
Proof. case: pt => /= [[x] /= /ltRP/ltRW //|]; by apply leRR. Qed.

Definition weight := mkNNFun weight_ge0.

Definition point pt : weight pt > 0 -> A.
destruct pt as [t c|].
- move=> _; exact c.
- case/ltRR.
Defined.

Lemma point_Scaled p x H : @point (p *: x) H = x.
Proof. by []. Qed.

Lemma Scaled_point x H : mkRpos H *: @point x H = x.
Proof.
case: x H => [p x|] H; by [congr Scaled; apply val_inj | elim: (ltRR 0)].
Qed.

Lemma weight_gt0 x : x != Zero -> (0 < weight x)%R.
Proof. by case: x => // p a _ /=. Qed.

Lemma weight_gt0b x : x != Zero -> (weight x >b 0)%R.
Proof. move=> ?; exact/ltRP/weight_gt0. Qed.

Definition weight_neq0 x (x0 : x != Zero) := Rpos.mk (weight_gt0b x0).

Local Notation "[ 'point' 'of' x ]" := (point (weight_gt0 x))
  (at level 0, format "[ 'point'  'of'  x ]").
Local Notation "[ 'weight' 'of' x ]" := (weight_neq0 x)
  (at level 0, format "[ 'weight'  'of'  x ]").

Lemma point_S1 a : [point of S1_neq0 a] = a.
Proof. by []. Qed.

Lemma weight0_Zero x : weight x = 0 -> x = Zero.
Proof. by case: x => //= r c /esym Hr; move/ltR_eqF: (Rpos_gt0 r) => /eqP. Qed.

(* In the following we annotate the lemmas with the corresponding
   axiom in definition 2.1 [Varacca & Winskell, MSCS, 2006] (the
   numbers are 1-7 and 13) *)

Definition addpt a b :=
  match a, b with
  | r *: x, q *: y => (r + q)%:pos *: (x <| ((r / (r + q))%:pos)%:pr |> y)
  | _, Zero => a
  | Zero, _ => b
  end.

Lemma addptE a b (a0 : a != Zero) (b0 : b != Zero) :
  let p := [weight of a0] in
  let q := [weight of b0] in
  let x := [point of a0] in
  let y := [point of b0] in
  addpt a b = (p + q)%:pos *: (x <| ((p / (p + q))%:pos)%:pr |> y).
Proof.
move: a b => [p x|//] [pb y|//] /= in a0 b0 *.
by congr (_ *: (_ <| _ |> _)); exact: val_inj.
Qed.

Local Notation "\ssum_ ( i <- r ) F" := (\big[addpt/Zero]_(i <- r) F).
Local Notation "\ssum_ ( i : t ) F" := (\big[addpt/Zero]_(i : t) F) (only parsing).
Local Notation "\ssum_ i F" := (\big[addpt/Zero]_i F).
Local Notation "\ssum_ ( i | P ) F" := (\big[addpt/Zero]_(i | P) F).
Local Notation "\ssum_ ( i < n | P ) F" := (\big[addpt/Zero]_(i < n | P%B) F).
Local Notation "\ssum_ ( i < n ) F" := (\big[addpt/Zero]_(i < n) F).

Definition scalept p (x : scaled_pt) :=
  match Rlt_dec 0 p, x with
  | left Hr, q *: y => (mkRpos Hr * q)%:pos *: y
  | _, _ => Zero
  end.

Lemma onem_divRxxy (r q : Rpos) : (r / (r + q)).~ = q / (q + r).
Proof. by rewrite /onem subR_eq (addRC r) -mulRDl mulRV // ?gtR_eqF. Qed.

(* 1 *)
Lemma addptC : commutative addpt.
Proof.
move=> [r x|] [q y|] //=; congr Scaled.
by apply val_inj; rewrite /= addRC.
by rewrite convC; congr (_ <| _ |> _); exact/val_inj/onem_divRxxy.
Qed.

Lemma s_of_Rpos_probA (p q r : Rpos) :
  [s_of (p / (p + (q + r)))%:pos%:pr, (q / (q + r))%:pos%:pr] =
  ((p + q) / (p + q + r))%:pos%:pr.
Proof.
apply val_inj; rewrite /= s_of_pqE /onem /=; field.
by split; exact/eqP/Rpos_neq0.
Qed.

Lemma r_of_Rpos_probA (p q r : Rpos) :
  [r_of (p / (p + (q + r)))%:pos%:pr, (q / (q + r))%:pos%:pr] =
  (p / (p + q))%:pos%:pr.
Proof.
apply/val_inj; rewrite /= r_of_pqE s_of_pqE /onem /=; field.
do 3 (split; first exact/eqP/Rpos_neq0).
rewrite (addRC p (q + r)) addRK {4}[in q + r]addRC addRK.
rewrite mulRC -mulRBr (addRC _ p) addRA addRK mulR_neq0.
split; exact/eqP/Rpos_neq0.
Qed.

(* 2 *)
Lemma addptA : associative addpt.
Proof.
move=> [p x|] [q y|] [r z|] //=.
congr Scaled. by apply val_inj; rewrite /= addRA.
rewrite convA; congr (_ <| _ |> _ ); first exact: s_of_Rpos_probA.
by congr (_ <| _ |> _); exact: r_of_Rpos_probA.
Qed.

(* 3 *)
Lemma addpt0 x : addpt x Zero = x.
Proof. by case: x. Qed.

(* 3' *)
Lemma add0pt x : addpt Zero x = x.
Proof. by case: x. Qed.

Canonical addpt_monoid := Monoid.Law addptA add0pt addpt0.
Canonical addpt_comoid := Monoid.ComLaw addptC.

Lemma weight_addpt : {morph weight : x y / addpt x y >-> x + y}.
Proof. move=> [p x|] [q y|] //=; by rewrite (add0R, addR0). Qed.

Lemma weight0 : weight Zero = 0.
Proof. by []. Qed.

Lemma scaleptR0 p : scalept p Zero = Zero.
Proof. by rewrite /scalept; case: Rlt_dec. Qed.

Lemma scalept_gt0 p (q : Rpos) x (H : 0 < p) :
  scalept p (q *: x) = (mkRpos H * q)%:pos *: x.
Proof.
rewrite /scalept; case: Rlt_dec => // Hr.
congr Scaled; by apply val_inj.
Qed.

(* 4 *)
Lemma scalept0 x : scalept 0 x = Zero.
Proof. rewrite /scalept; case: Rlt_dec => // Hr; by elim (ltRR 0). Qed.

(* 5 *)
Lemma scalept1 x : scalept 1 x = x.
Proof.
case: x => [r c|]; rewrite ?scaleptR0 // scalept_gt0.
congr Scaled; apply val_inj; by rewrite /= mul1R.
Qed.

Lemma scalept_Scaled p q x : scalept p (q *: x) = scalept (p * q) (S1 x).
Proof.
rewrite /scalept.
case: Rlt_dec => Hp; case: Rlt_dec => Hpq //.
- congr Scaled; apply val_inj; by rewrite /= mulR1.
- elim Hpq; by apply /mulR_gt0.
- elim Hp; move/pmulR_lgt0: Hpq; exact.
Qed.

Lemma scalept_weight p x : 0 <= p -> weight (scalept p x) = p * weight x.
Proof.
case=> Hp; last by rewrite -Hp scalept0 mul0R.
case: x => [r y|]; by [rewrite scalept_gt0 | rewrite scaleptR0 mulR0].
Qed.

(* 6 *)
Lemma scalept_addpt r : {morph scalept r : x y / addpt x y >-> addpt x y}.
Proof.
rewrite /scalept; case: Rlt_dec => // Hr x y.
case: x => [p x|]; last by rewrite !add0pt.
case: y => [q y|]; last by rewrite !addpt0.
congr Scaled. by apply val_inj => /=; rewrite mulRDr.
have Hr0 : r != 0 by apply gtR_eqF.
congr (_ <| _ |> _); apply val_inj; rewrite /= -mulRDr divRM //.
  by rewrite /Rdiv -(mulRAC r) mulRV ?mul1R //; exact/eqP.
exact/Rpos_neq0.
Qed.

Definition big_scalept q :=
  big_morph (scalept q) (scalept_addpt q) (scaleptR0 _).

(* 7 *)
Lemma scalept_comp p q x :
  0 <= p -> 0 <= q -> scalept p (scalept q x) = scalept (p * q) x.
Proof.
case=> Hp; last by rewrite -Hp mul0R !scalept0.
case=> Hq; last by rewrite -Hq mulR0 scalept0 scaleptR0.
case: x => [r x|]; rewrite ?scaleptR0 // !scalept_gt0; first by apply mulR_gt0.
move=> Hpq; congr Scaled; apply val_inj => /=; by rewrite mulRA.
Qed.

(* 13 *)
Lemma scalept_addR p q x :
  0 <= p -> 0 <= q ->
  scalept (p + q) x = addpt (scalept p x) (scalept q x).
Proof.
case=> Hp; last by rewrite -Hp scalept0 add0R add0pt.
case=> Hq; last by rewrite -Hq scalept0 addR0 addpt0.
case: x => [r c|]; last by rewrite !scaleptR0.
rewrite !scalept_gt0 => [|Hpq /=]; first by apply addR_gt0.
rewrite convmm; congr Scaled; apply val_inj; by rewrite /= mulRDl.
Qed.

Lemma scalept_rsum (B : finType) (P : pred B) (F : B ->R^+) x :
  scalept (\sum_(i | P i) (F i)) x = \ssum_(b | P b) scalept (F b) x.
Proof.
apply (@proj1 _ (0 <= \sum_(i | P i) F i)).
apply (big_ind2 (fun y q => scalept q x = y /\ 0 <= q)).
+ by rewrite scalept0.
+ move=> x1 x2 y1 y2 [Hx1 Hx2] [Hy1 Hy2].
  by rewrite -Hx1 -Hy1 scalept_addR //; split => //; exact: addR_ge0.
+ by move=> i _; split => //; exact/nneg_f_ge0.
Qed.

Definition barycenter (pts : seq scaled_pt) := \ssum_(x <- pts) x.

Lemma barycenter_big_fin (T : finType) (F : T -> scaled_pt) :
  barycenter [seq F i | i <- enum T] = \ssum_i F i.
Proof. by rewrite /barycenter big_map big_filter. Qed.

Lemma weight_bary pts : weight (barycenter pts) = \sum_(x <- pts) weight x.
Proof. by rewrite (big_morph weight weight_addpt weight0). Qed.

Lemma scalept_bary p (H : 0 <= p) pts :
  scalept p (barycenter pts) = barycenter (map (scalept p) pts).
Proof. by rewrite big_scalept /barycenter big_map. Qed.

Lemma barycenter_perm n (F : 'I_n -> scaled_pt) (pe : 'S_n) :
  \ssum_(i < n) F i = \ssum_(i < n) F (pe i).
Proof.
rewrite -!barycenter_big_fin /barycenter big_map map_comp big_map.
exact/perm_big/perm_eq_perm.
Qed.

Section convfdist.
Variables (n : nat) (B : finType).
Variable p : {fdist 'I_n}.
Variable q : 'I_n -> {fdist B}.
Variable h : B -> scaled_pt.

Lemma barycenter_convnfdist :
  (* TODO: \ssum_(j in B) notation? *)
  \ssum_(i < n) scalept (p i) (\ssum_(j <- enum B) scalept (q i j) (h j)) =
  \ssum_(j <- enum B) scalept (ConvnFDist.d p q j) (h j).
Proof.
rewrite (eq_bigr _ (fun i _ => big_scalept (p i) _ _ _)).
rewrite exchange_big /=; apply eq_bigr => j _; rewrite ConvnFDist.dE.
have HF i : 0 <= p i * q i j by exact/mulR_ge0.
rewrite (scalept_rsum _ (mkNNFun HF)) /=; apply eq_bigr => i _.
by rewrite scalept_comp.
Qed.
End convfdist.

Section convpt_convex_space.
Let convpt p x y := addpt (scalept p x) (scalept p.~ y).
Let convpt_conv1 a b : convpt 1 a b = a.
Proof. by rewrite /convpt onem1 scalept1 scalept0 addpt0. Qed.
Let convpt_convmm (p : prob) a : convpt p a a = a.
Proof. by rewrite /convpt -scalept_addR // onemKC scalept1. Qed.
Let convpt_convC (p : prob) a b : convpt p a b = convpt (p.~)%:pr b a.
Proof. by rewrite [RHS]addptC onemK. Qed.
Let convpt_convA (p q : prob) a b c :
  convpt p a (convpt q b c) = convpt [s_of p, q] (convpt [r_of p, q] a b) c.
Proof.
rewrite /convpt !scalept_addpt ?scalept_comp // -[RHS]addptA; congr addpt.
  by rewrite (p_is_rs p q) mulRC.
by rewrite pq_is_rs mulRC s_of_pqE onemK.
Qed.

HB.instance Definition _ := @isConvexSpace.Build scaled_pt
  (Choice.class scaled_pt_choiceType) convpt
  convpt_conv1 convpt_convmm convpt_convC convpt_convA.

Lemma convptE p (a b : scaled_pt) : a <| p |> b = convpt p a b.
Proof. by []. Qed.

End convpt_convex_space.

Section adjunction.
Variable p : prob.

Let adjunction_1 a b : S1 a <| 1%:pr |> S1 b = S1 (a <| 1%:pr |> b).
Proof. by rewrite convptE onem1 scalept0 scalept1 addpt0 conv1. Qed.

Lemma adjunction_2 x y : S1 x <| p |> S1 y = S1 (x <| p |> y).
Proof.
case/prob_ge0 : p => p0; last first.
  by rewrite (_ : p = 0%:pr) ?conv0 //; exact/val_inj.
case/prob_le1 : p => p1; last first.
  by rewrite (_ : p = 1%:pr) ?adjunction_1 //; exact/val_inj.
rewrite convptE (scalept_gt0 _ _ p0) (@scalept_gt0 p.~) => [|H].
  exact/onem_gt0.
congr Scaled => /=; first by apply val_inj; rewrite /= !mulR1 onemKC.
by congr (_ <| _ |> _); apply val_inj; rewrite /= !mulR1 addRC subRK divR1.
Qed.

Lemma S1_conv : {morph S1 : a b / a <|p|> b >-> a <|p|> b}.
Proof. move=> a b. by rewrite -adjunction_2. Qed.
End adjunction.

End scaled_convex.
Arguments Zero {A}.
End ScaledConvex.
Local Notation "a *: v" := (@ScaledConvex.Scaled _ a v).
Notation "[ 'point' 'of' x ]" := (ScaledConvex.point (ScaledConvex.weight_gt0 x))
  (at level 0, format "[ 'point'  'of'  x ]") : convex_scope.
Notation "[ 'weight' 'of' x ]" := (ScaledConvex.weight_neq0 x)
  (at level 0, format "[ 'weight'  'of'  x ]") : convex_scope.
Notation "\ssum_ ( i <- r | P ) F" :=
  (\big[(@ScaledConvex.addpt _)/(@ScaledConvex.Zero _)]_(i <- r | P%B) F) : convex_scope.
Notation "\ssum_ ( i <- r ) F" :=
  (\big[(@ScaledConvex.addpt _)/(@ScaledConvex.Zero _)]_(i <- r) F) : convex_scope.
Notation "\ssum_ ( i : t ) F" :=
  (\big[(@ScaledConvex.addpt _)/(@ScaledConvex.Zero _)]_(i : t) F)  (only parsing) : convex_scope.
Notation "\ssum_ ( i | P ) F" :=
  (\big[(@ScaledConvex.addpt _)/(@ScaledConvex.Zero _)]_(i | P%B) F) : convex_scope.
Notation "\ssum_ i F" :=
  (\big[(@ScaledConvex.addpt _)/(@ScaledConvex.Zero _)]_i F) : convex_scope.
Notation "\ssum_ ( i < n | P ) F" :=
  (\big[ScaledConvex.addpt/ScaledConvex.Zero]_(i < n | P%B) F) : convex_scope.
Notation "\ssum_ ( i < n ) F" :=
  (\big[(@ScaledConvex.addpt _)/(@ScaledConvex.Zero _)]_(i < n) F) : convex_scope.

Section convex_space_prop1.
Variables T : convType.
Implicit Types a b : T.

Lemma convA0 (p q r s : prob) a b c :
  p = (r * s)%R :> R -> (s.~ = p.~ * q.~)%R ->
  a <| p |> (b <| q |> c) = (a <| r |> b) <| s |> c.
Proof.
move=> H1 H2.
case/boolP : (r == 0%:pr) => r0.
  rewrite (eqP r0) conv0 (_ : p = 0%:pr) ?conv0; last first.
    by apply/val_inj; rewrite /= H1 (eqP r0) mul0R.
  congr (_ <| _ |> _); move: H2; rewrite H1 (eqP r0) mul0R onem0 mul1R.
  by move/(congr1 onem); rewrite !onemK => ?; exact/val_inj.
case/boolP : (s == 0%:pr) => s0.
  have p0 : p = 0%:pr by apply/val_inj; rewrite /= H1 (eqP s0) mulR0.
  rewrite (eqP s0) conv0 p0 // ?conv0.
  rewrite (_ : q = 0%:pr) ?conv0 //.
  move: H2; rewrite p0 onem0 mul1R => /(congr1 onem); rewrite !onemK => sq.
  by rewrite -(eqP s0); exact/val_inj.
rewrite convA; congr ((_ <| _ |> _) <| _ |> _).
  by apply val_inj; rewrite /= s_of_pqE -H2 onemK.
by rewrite (@r_of_pq_is_r  _ _ r s).
Qed.

Lemma convA' (r s : prob) a b c : a <| [p_of r, s] |> (b <| [q_of r, s] |> c) = (a <| r |> b) <| s |> c.
Proof.
case H: ([p_of r, s] == 1%:pr).
   move: H=>/p_of_rs1P [ -> -> ].
   by rewrite conv1 conv1 -{2}(conv1 a (b <|[q_of (1)%:pr, (1)%:pr]|> c)); congr Conv; rewrite p_of_1s.
move: H=>/negP/negP H; case/boolP : (s == 0%:pr) => s0.
- by rewrite (eqP s0) p_of_r0 conv0 q_of_r0 conv0 conv0.
- by rewrite convA s_of_pqK // r_of_pqK.
Qed.

Import ScaledConvex.

Lemma convACA (a b c d : T) p q :
  (a <|q|> b) <|p|> (c <|q|> d) = (a <|p|> c) <|q|> (b <|p|> d).
Proof.
apply S1_inj; rewrite ![in LHS]S1_conv !convptE.
rewrite !scalept_addpt ?scalept_comp //.
rewrite !(mulRC p) !(mulRC p.~) addptA addptC (addptC (scalept (q * p) _)).
rewrite !addptA -addptA -!scalept_comp -?scalept_addpt //.
by rewrite !(addptC (scalept _.~ _)) !S1_conv.
Qed.

Lemma convDr (x y z : T) (p q : prob) :
  x <| p |> (y <| q |> z) = (x <| p |> y) <| q |> (x <| p |> z).
Proof. by rewrite -{1}(convmm q x) convACA. Qed.

Lemma convACA' (a b c d : T) (p q r : prob) :
(*
  let p1 := (q * p)%:opr in
  let p2 := (q.~ * r)%:opr in
  let r1 := (q * p.~)%:opr in
  let r2 := (q.~ * r.~)%:opr in
  let q' := ((p1 + p2) / (p1 + p2 + (r1 + r2)))%:opr in
  let p' := (p1 / (p1 + p2))%:opr in
  let r' := (r1 / (r1 + r2))%:opr in
  (a <|p|> b) <|q|> (c <|r|> d) = (a <|p'|> c) <|q'|> (b <|r'|> d).
*)
  exists p' q' r', (a <|p|> b) <|q|> (c <|r|> d) = (a <|p'|> c) <|q'|> (b <|r'|> d).
Proof.
rewrite (convC p).
rewrite convA convC !convA.
set C0 := _.~%:pr; rewrite (_ : C0 = C0%:opr) //.
set C1 := _.~%:pr; rewrite (_ : C1 = C1%:opr) //.
rewrite -convA'_oprob (convC _ d) convC.
by eexists; eexists; eexists; congr ((_ <|_|> _) <|_|> (_ <|_|> _)).
Qed.

Local Open Scope vec_ext_scope.

Section with_affine_projection.
Variable U : convType.
Variable prj : {affine T -> U}.

Definition map_scaled (x : scaled_pt T) : scaled_pt U :=
  if x is p *: a then p *: prj a else @Zero U.

Lemma map_scaled_affine p :
  {morph map_scaled : x y / x <|p|> y >-> x <|p|> y}.
Proof.
move=> [q x|] [r y|] /=; rewrite 2!convptE ?scaleptR0 //.
+ rewrite !(scalept_Scaled p) !(scalept_Scaled p.~) /= /scalept.
  case: Rlt_dec => Hpq; case: Rlt_dec => Hpr //=; congr Scaled.
  by rewrite affine_conv.
+ rewrite !addpt0 !(scalept_Scaled p) /= /scalept; by case: Rlt_dec.
+ rewrite !add0pt !(scalept_Scaled p.~) /= /scalept; by case: Rlt_dec.
Qed.

Lemma S1_convn_proj n (points : 'I_n -> T) d :
  S1 (prj (<|>_d points)) =
  \ssum_(i < n) scalept (d i) (S1 (prj (points i))).
Proof.
elim: n points d => [|n IH] points d.
  by move: (FDist.f1 d); rewrite /= big_ord0 => /Rlt_not_eq; elim.
rewrite /=; case: Bool.bool_dec => [/eqP|/Bool.eq_true_not_negb]Hd.
  rewrite (bigD1 ord0) //= Hd big1 /=.
    rewrite addpt0 (@scalept_gt0 _ 1).
    by congr Scaled; apply val_inj; rewrite /= mulR1.
  move=> i Hi; have := FDist.f1 d.
  rewrite (bigD1 ord0) ?inE // Hd /= addRC => /(f_equal (Rminus^~ R1)).
  by rewrite addRK subRR => /psumR_eq0P -> //; rewrite scalept0.
set d' := DelFDist.d Hd.
set points' := fun i => points (DelFDist.f ord0 i).
rewrite /index_enum -enumT (bigD1_seq ord0) ?enum_uniq ?mem_enum //=.
rewrite -big_filter (perm_big (map (lift ord0) (enum 'I_n)));
  last by apply perm_filter_enum_ord.
rewrite affine_conv S1_conv; congr addpt.
rewrite IH -barycenter_big_fin scalept_bary //.
rewrite /barycenter 2!big_map [in RHS]big_map.
apply eq_bigr => i _.
rewrite scalept_comp // DelFDist.dE D1FDist.dE /=.
rewrite /Rdiv (mulRC (d _)) mulRA mulRV ?mul1R //.
by move: (Hd); apply contra => /eqP Hd'; rewrite -onem0 -Hd' onemK.
Qed.
End with_affine_projection.

Lemma S1_convn n (points : 'I_n -> T) d :
  S1 (<|>_d points) = \ssum_(i < n) scalept (d i) (S1 (points i)).
Proof. by rewrite (S1_convn_proj [the {affine _ ->_} of idfun]). Qed.

End convex_space_prop1.

Section convex_space_prop2.
Variables T U : convType.
Implicit Types a b : T.

Lemma affine_function_Sum (f : {affine T -> U}) n (g : 'I_n -> T) (d : {fdist 'I_n}) :
  f (<|>_d g) = <|>_d (f \o g).
Proof.
Import ScaledConvex.
by apply S1_inj; rewrite S1_convn S1_convn_proj.
Qed.

Lemma eq_convn n (g1 g2 : 'I_n -> T) (d1 d2 : {fdist 'I_n}) :
  g1 =1 g2 -> d1 =1 d2 -> <|>_d1 g1 = <|>_d2 g2.
Proof.
move=> Hg Hd; apply S1_inj; rewrite !S1_convn.
apply congr_big => // i _; by rewrite Hg Hd.
Qed.

Lemma convn_proj n (g : 'I_n -> T) (d : {fdist 'I_n}) i :
  d i = R1 -> <|>_d g = g i.
Proof.
move=> Hd; apply S1_inj.
rewrite S1_convn (bigD1 i) ?inE //=.
rewrite big1; first by rewrite addpt0 Hd scalept1.
move=> j Hj.
move/eqP/FDist1.P: Hd => -> //; by rewrite scalept0.
Qed.

Lemma ConvnFDist1 (n : nat) (j : 'I_n) (g : 'I_n -> T): <|>_(FDist1.d j) g = g j.
Proof. by apply convn_proj; rewrite FDist1.dE eqxx. Qed.

Lemma convn1E (g : 'I_1 -> T) (e : {fdist 'I_1}) : <|>_ e g = g ord0.
Proof.
rewrite /=; case: Bool.bool_dec => // /Bool.eq_true_not_negb H.
exfalso; move/eqP: H; apply.
by apply/eqP; rewrite FDist1.dE1 (FDist1.I1 e).
Qed.

Lemma convnE n (g : 'I_n.+1 -> T) (d : {fdist 'I_n.+1}) (i1 : d ord0 != 1%R) :
  <|>_d g = g ord0 <| probfdist d ord0 |>
            <|>_(DelFDist.d i1) (fun x => g (DelFDist.f ord0 x)).
Proof.
rewrite /=; case: Bool.bool_dec => /= [|/Bool.eq_true_not_negb] H.
exfalso; by rewrite (eqP H) eqxx in i1.
by rewrite (eq_irrelevance H i1).
Qed.

Lemma convn2E (g : 'I_2 -> T) (d : {fdist 'I_2}) :
  <|>_d g = g ord0 <| probfdist d ord0 |> g (lift ord0 ord0).
Proof.
case/boolP : (d ord0 == 1%R) => [|i1].
  rewrite FDist1.dE1 => /eqP ->; rewrite ConvnFDist1.
  rewrite (_ : probfdist _ _ = 1%:pr) ?conv1 //.
  by apply val_inj; rewrite /= FDist1.dE eqxx.
rewrite convnE; congr (_ <| _ |> _).
by rewrite convn1E /DelFDist.f ltnn.
Qed.

(* ref: M.H.Stone, postulates for the barycentric calculus, lemma 2 *)
Lemma Convn_perm (n : nat) (d : {fdist 'I_n}) (g : 'I_n -> T) (s : 'S_n) :
  <|>_d g = <|>_(PermFDist.d d s) (g \o s).
Proof.
apply S1_inj; rewrite !S1_convn (barycenter_perm _ s).
apply eq_bigr => i _; by rewrite PermFDist.dE.
Qed.

(* ref: M.H.Stone, postulates for the barycentric calculus, lemma 4 *)
Theorem Convn_convnfdist (n m : nat) (d : {fdist 'I_n})
        (e : 'I_n -> {fdist 'I_m}) (x : 'I_m -> T) :
  <|>_d (fun i => <|>_(e i) x) = <|>_(ConvnFDist.d d e) x.
Proof.
apply S1_inj; rewrite !S1_convn -[in RHS]big_enum -barycenter_convnfdist.
apply eq_bigr => i _; by rewrite big_enum S1_convn.
Qed.

Lemma convn_const (a : T) (n : nat) (d : {fdist 'I_n}) :
  <|>_d (fun _=> a) = a.
Proof.
elim: n d; first by move=> d; move/fdistI0_False: (d).
move=> n IHn d.
case/boolP: (d ord0 == 1%R); first by move/eqP/(convn_proj (fun _ => a)).
by move=> d0n0; rewrite convnE IHn convmm.
Qed.

Lemma convn_idem (a : T) (n : nat) (d : {fdist 'I_n}) (g : 'I_n -> T) :
  (forall i : 'I_n, (d i != 0)%R -> g i = a) -> <|>_d g = a.
Proof.
move=> Hg.
apply S1_inj.
rewrite S1_convn (eq_bigr (fun i => scalept (d i) (S1 a))).
  by rewrite -S1_convn convn_const.
move=> /= i _.
case/boolP: (d i == 0)%R => [/eqP | /Hg] -> //.
by rewrite !scalept0.
Qed.

Lemma convn_weak n m (u : 'I_m -> 'I_n) (d : {fdist 'I_m}) (g : 'I_n -> T) :
  <|>_d (g \o u) = <|>_(FDistMap.d u d) g.
Proof.
apply S1_inj.
rewrite !S1_convn (partition_big u (fun _=> true)) //=.
apply eq_bigr => i _.
rewrite FDistMap.dE /=.
have HF : forall a : 'I_m, (0 <= d a)%R by [].
rewrite (@scalept_rsum T _ _ (mkNNFun HF)) /=.
by apply eq_bigr => a /eqP ->.
Qed.

Lemma convnDr :
  forall (n : nat) (p : prob) (x : T) (g : 'I_n -> T) (d : {fdist 'I_n}),
    x <|p|> <|>_d g = <|>_d (fun i => x <|p|> g i).
Proof.
elim; first by move=> p x g d; move/fdistI0_False: (d).
move=> n IHn p x g d.
have [/eqP d01|d0n1] := boolP (d ord0 == 1%R).
  by rewrite (convn_proj g d01) (convn_proj (fun i => x <|p|> g i) d01).
rewrite !convnE !IHn.
congr Convn; apply funext=> i.
by rewrite convDr.
Qed.

Lemma convnDl:
  forall (n : nat) (p : prob) (x : T) (g : 'I_n -> T) (d : {fdist 'I_n}),
    <|>_d g <|p|> x = <|>_d (fun i => g i <|p|> x).
Proof.
move=> p x g d e.
rewrite convC convnDr; apply eq_convn=>// i.
by rewrite -convC.
Qed.

Lemma convnDlr:
  forall (n m : nat) (p : prob) (f : 'I_n -> T) (d : {fdist 'I_n}) (g: 'I_m -> T) (e: {fdist 'I_m}),
    <|>_d f <|p|> <|>_e g = <|>_(AddFDist.d d e p) (fun i => match fintype.split i with inl i => f i | inr i => g i end).
Proof.
move=>n m p f d g e.
apply S1_inj; rewrite S1_conv S1_convn S1_convn S1_convn convptE big_scalept big_scalept big_split_ord; congr addpt; apply congr_big=>// i _; rewrite scalept_comp // AddFDist.dE /fintype.split; case ltnP=>ilt.
   2: by exfalso; move: ilt=>/=; rewrite leqNgt=>/negP.
   2: by exfalso; move: ilt=>/=; rewrite addnC {2}[n]/(0+n) -/addn ltn_add2r ltn0.
   by have ->: Ordinal ilt = i by apply val_inj.
by have ->: Ordinal (split_subproof ilt) = i by apply val_inj; rewrite /= addnC {2}[n]/(0+n) -/addn subnDr /subn /subn_rec Nat.sub_0_r.
Qed.

End convex_space_prop2.

Section hull_def.
Local Open Scope classical_set_scope.
Definition hull (T : convType) (X : set T) : set T :=
  [set p : T | exists n (g : 'I_n -> T) d, g @` setT `<=` X /\ p = <|>_d g].
End hull_def.

Section hull_prop.
Local Open Scope classical_set_scope.
Variable A : convType.
Implicit Types X Y : set A.
Implicit Types a : A.

Lemma subset_hull X : X `<=` hull X.
Proof.
move=> x xX; rewrite /hull; exists 1, (fun=> x), (FDist1.d ord0).
split => [d [i _ <-] //|]; by rewrite convn1E.
Qed.

Lemma hull0 : hull set0 = set0 :> set A.
Proof.
rewrite funeqE => d; rewrite propeqE; split => //.
move=> [n [g [e [gX ->{d}]]]].
destruct n as [|n]; first by move: (fdistI0_False e).
exfalso; apply: (gX (g ord0)); exact/imageP.
Qed.

Lemma hull_eq0 X : (hull X == set0) = (X == set0).
Proof.
apply/idP/idP=> [/eqP abs|]; last by move=> /eqP ->; rewrite hull0.
apply/negPn/negP => /set0P[/= d] => dX.
move: abs; rewrite funeqE => /(_ d); rewrite propeqE /set0 => -[H _]; apply H.
exact/subset_hull.
Qed.

Lemma mem_hull_setU X Y a0 a1 p :
  X a0 -> Y a1 -> (hull (X `|` Y)) (a0 <| p |> a1).
Proof.
move=> a0X a1y.
exists 2, (fun i => if i == ord0 then a0 else a1), (I2FDist.d p); split => /=.
  move=> a2.
  case => i _ <-{a2} /=.
  case: ifPn => _; [by left | by right].
case: Bool.bool_dec => [/eqP|/Bool.eq_true_not_negb H].
  rewrite I2FDist.dE eqxx /= => p1.
  by rewrite (_ : p = 1%:pr) ?conv1 //; exact/val_inj.
congr (_ <| _ |> _); first by apply val_inj; rewrite /= I2FDist.dE eqxx.
case: Bool.bool_dec => // H'.
exfalso.
move: H'; rewrite DelFDist.dE D1FDist.dE (eq_sym (lift _ _)) (negbTE (neq_lift _ _)).
rewrite I2FDist.dE (eq_sym (lift _ _)) (negbTE (neq_lift _ _)) I2FDist.dE eqxx divRR ?eqxx //.
by move: H; rewrite I2FDist.dE eqxx onem_neq0.
Qed.

Lemma hull_monotone X Y : X `<=` Y -> hull X `<=` hull Y.
Proof.
move=> H a [n [g [d [H0 H1]]]]; exists n, g, d; split => //.
by eapply subset_trans; first exact: H0.
Qed.
End hull_prop.

(* Convex sets in a convex space *)

Section is_convex_set.
Local Open Scope classical_set_scope.
Variable T : convType.

Definition is_convex_set (D : set T) : bool :=
  `[<forall x y t, D x -> D y -> D (x <| t |> y)>].

Lemma is_convex_set0 : is_convex_set set0.
Proof. exact/asboolP. Qed.

Lemma is_convex_set1 a : is_convex_set [set a].
Proof. by apply/asboolP => x y p /= => -> ->; rewrite convmm. Qed.

Lemma is_convex_setT : is_convex_set setT.
Proof. exact/asboolP. Qed.

Definition is_convex_set_n (X : set T) : bool :=
  `[< forall n (g : 'I_n -> T) (d : {fdist 'I_n}),
    g @` setT `<=` X -> X (<|>_d g) >].

Lemma is_convex_setP (X : set T) : is_convex_set X = is_convex_set_n X.
Proof.
apply/idP/idP => H; apply/asboolP; last first.
  move=> x y p xX yX.
  case/boolP : (p == 1%:pr) => [/eqP ->|p1]; first by rewrite conv1.
  set g : 'I_2 -> T := fun i => if i == ord0 then x else y.
  have gX : g @` setT `<=` X by move=> a -[i _ <-]; rewrite /g; case: ifPn.
  move/asboolP : H => /(_ _ g (I2FDist.d p) gX).
  rewrite convnE; first by rewrite I2FDist.dE eqxx.
  move=> p1'.
  rewrite {1}/g eqxx (_ : probfdist _ _ = p); last first.
    by apply val_inj; rewrite /= I2FDist.dE eqxx.
  by rewrite (_ : <|>_ _ _ = y) // (_ : (fun _ => _) = (fun=> y)) ?convn1E.
elim => [g d|n IH g d]; first by move: (fdistI0_False d).
destruct n as [|n] => gX.
  rewrite {IH} (@convn_proj _ _ _ _ ord0) //.
  exact/gX/classical_sets.imageP.
  by apply/eqP; rewrite FDist1.dE1 (FDist1.I1 d).
case/boolP : (d ord0 == 1%R) => [/eqP|]d01.
  suff -> : <|>_d g = g ord0 by apply gX; exists ord0.
  by rewrite (@convn_proj _ _ _ _ ord0).
set D : {fdist 'I_n.+1} := DelFDist.d d01.
pose G (i : 'I_n.+1) : T := g (DelFDist.f (@ord0 _) i).
have : G @` setT `<=` X.
  by move=> x -[i _ <-{x}]; rewrite /G /DelFDist.f ltn0; apply gX; exists ((lift ord0 i)).
move/(IH _ D) => {}IH.
rewrite convnE //.
move/asboolP : H; apply => //; exact/gX/classical_sets.imageP.
Qed.

End is_convex_set.

Module CSet.
Section cset.
Variable A : convType.
Record mixin_of (X : set A) : Type := Mixin { _ : is_convex_set X }.
Record t : Type := Pack { car : set A ; class : mixin_of car }.
End cset.
Module Exports.
Notation convex_set := t.
Coercion car : convex_set >-> set.
End Exports.
End CSet.
Export CSet.Exports.

Definition convex_set_of (A : convType) :=
  fun phT : phant (ConvexSpace.sort A) => convex_set A.
Notation "{ 'convex_set' T }" := (convex_set_of (Phant T)) : convex_scope.

(* kludge 2022-04-14 *)
Definition choice_of_Type (T : Type) : choiceType :=
  Choice.Pack (Choice.Class (@gen_eqMixin T) gen_choiceMixin).

Section cset_canonical.
Variable (A : convType).
Canonical cset_predType := Eval hnf in
  PredType (fun t : convex_set A => (fun x => x \in CSet.car t)).
Canonical cset_eqType := Equality.Pack (@gen_eqMixin (convex_set A)).
Canonical cset_choiceType := choice_of_Type (convex_set A).
End cset_canonical.

Section CSet_interface.
Variable (A : convType).
Implicit Types X Y : {convex_set A}.
Lemma convex_setP X : is_convex_set X.
Proof. by case: X => X []. Qed.
Lemma cset_ext X Y : X = Y :> set _ -> X = Y.
Proof.
move: X Y => -[X HX] [Y HY] /= ?; subst Y.
congr (CSet.Pack _); exact/Prop_irrelevance.
Qed.
End CSet_interface.

Section CSet_prop.
Local Open Scope classical_set_scope.
Import ScaledConvex.
Variable A : convType.
Implicit Types X Y : {convex_set A}.
Implicit Types a : A.
Implicit Types x y : scaled_pt A.

Lemma mem_convex_set a1 a2 p X : a1 \in X -> a2 \in X -> a1 <|p|> a2 \in X.
Proof.
case: X => X [convX]; move: (convX) => convX_save.
move/asboolP : convX => convX Hx Hy.
by rewrite in_setE; apply: convX; rewrite -in_setE.
Qed.

Definition cset0 : {convex_set A} := CSet.Pack (CSet.Mixin (is_convex_set0 A)).

Lemma cset0P X : (X == cset0) = (X == set0 :> set _).
Proof.
case: X => x [Hx] /=; apply/eqP/eqP => [-[] //| ?]; subst x; exact: cset_ext.
Qed.

Lemma cset0PN X : X != cset0 <-> X !=set0.
Proof.
rewrite cset0P; case: X => //= x Hx; split; last first.
  case=> a xa; apply/eqP => x0; move: xa; by rewrite x0.
by case/set0P => /= d dx; exists d.
Qed.

Definition cset1 a : {convex_set A} := CSet.Pack (CSet.Mixin (is_convex_set1 a)).

Lemma cset1_neq0 a : cset1 a != cset0.
Proof. by apply/cset0PN; exists a. Qed.

End CSet_prop.

(* Lemmas on hull and convex set *)

Lemma is_convex_segmentP (A: convType) (X: set A): reflect (forall x y: A, X x -> X y -> (segment x y `<=` X)%classic) (is_convex_set X). 
Proof.
apply (iffP idP)=>conv.
   move=>x y xX yX z [p _ <-].
   by move: conv=>/asboolP/(_ x y p xX yX).
by apply/asboolP=>x y p xX yX; apply (conv x y xX yX); exists p.
Qed.

Lemma hull_sub_convex (A: convType) X (Y: {convex_set A}): (X `<=` Y -> hull X `<=` Y)%classic.
Proof.
move=>XY x [n [g [d [gX ->]]]].
move: (convex_setP Y); rewrite is_convex_setP /is_convex_set_n.
by move=> /asboolP/(_ _ g d (subset_trans gX XY)).
Qed.

Lemma hull_cset (A : convType) (X : {convex_set A}) : hull X = X.
Proof.
rewrite predeqE => d; split; [by apply hull_sub_convex | exact/subset_hull].
Qed.

Section hull_is_convex.
Variable A : convType.
Import ScaledConvex.

Lemma AddFDist_conv n m p (g : 'I_(n + m) -> A)
  (d : {fdist 'I_n}) (e : {fdist 'I_m}) :
  <|>_(AddFDist.d d e p) g =
  <|>_d (g \o @lshift n m) <|p|> <|>_e (g \o @rshift n m).
Proof.
apply S1_inj; rewrite S1_conv !S1_convn.
rewrite convptE big_split_ord !big_scalept /=.
congr addpt; apply eq_bigr => i _;
  rewrite (scalept_comp (S1 _) (prob_ge0 _) (FDist.ge0 _ _));
  by rewrite AddFDist.dE (split_lshift,split_rshift).
Qed.

Lemma segment_is_convex (x y: A): is_convex_set (segment x y).
Proof.
apply/asboolP=>u v p [q _ <-] [r _ <-].
move: (convACA' x y x y q p r)=>[q' [p' [r' ->]]].
by rewrite convmm convmm; exists p'.
Qed.

Lemma hull_is_convex (Z : set A) : is_convex_set (hull Z).
Proof.
apply/asboolP => x y p [n [g [d [gX ->{x}]]]] [m [h [e [hX ->{y}]]]].
exists (n + m).
exists [ffun i => match fintype.split i with inl a => g a | inr a => h a end].
exists (AddFDist.d d e p).
split.
  move=> a -[i _]; rewrite ffunE.
  case: splitP => j _ <-; by [apply gX; exists j | apply hX; exists j].
rewrite AddFDist_conv; congr (_ <| _ |> _); apply eq_convn => i //=;
  by rewrite ffunE (split_lshift,split_rshift).
Qed.

Canonical hull_is_convex_set (Z : set A) : convex_set A :=
  CSet.Pack (CSet.Mixin (hull_is_convex Z)).

End hull_is_convex.

Section hull_convex_set.
Local Open Scope classical_set_scope.
Variable A : convType.
Implicit Types X Y Z : set A.

Lemma segment_hull (x y: A): segment x y = hull [set x; y].
Proof.
rewrite eqEsubset; split.
   by move: (hull_is_convex [set x; y])=>/is_convex_segmentP/(_ x y); apply; apply subset_hull; [ left | right ].
by apply (@hull_sub_convex _ [set x; y] {| CSet.car := segment x y; CSet.class := CSet.Mixin (segment_is_convex x y) |})=>z; case=>->; [ apply segmentL | apply segmentR ].
Qed.

Lemma is_convex_hullE X: is_convex_set X = (hull X == X).
Proof.
apply/idP/idP.
   by move=>conv; apply /eqP; exact (hull_cset {| CSet.car := X; CSet.class := CSet.Mixin conv |}).
by move=>/eqP <-; apply hull_is_convex.
Qed.

Lemma hull_eqEsubset X Y :
  (X `<=` hull Y)%classic -> (Y `<=` hull X)%classic -> hull X = hull Y.
Proof.
move/hull_monotone; rewrite hull_cset /= => H1.
move/hull_monotone; rewrite hull_cset /= => H2.
by rewrite eqEsubset.
Qed.

(* hull (X `|` hull Y) = hull (hull (X `|` Y)) = hull (x `|` y);
   the first equality looks like a tensorial strength under hull
   Todo : Check why this is so. *)
Lemma hullU_strr X Y : hull (X `|` hull Y) = hull (X `|` Y).
Proof.
apply/hull_eqEsubset => a.
- case; first by move=> ?; apply/subset_hull; left.
  case=> n [d [g [H0 H1]]]; exists n, d, g; split => //.
  apply (subset_trans H0) => ? ?; by right.
- case => [?|?]; first by apply/subset_hull; left.
  apply/subset_hull; right. exact/subset_hull.
Qed.

Lemma hullU_strl X Y : hull (hull X `|` Y) = hull (X `|` Y).
Proof. by rewrite [in LHS]setUC [in RHS]setUC hullU_strr. Qed.

Lemma hullUA X Y Z :
  hull (X `|` hull (Y `|` Z)) = hull (hull (X `|` Y) `|` Z).
Proof. by rewrite hullU_strr hullU_strl setUA. Qed.

(* NB: hullI exhibits a fundamental
   algebraic property of hull, and since I expect there should be some
   cases where inference of canonical structure does not work well for hulls
   and a user needs to manually rewrite using such algebraic properties *)
Lemma hullI (X : set A) : hull (hull X) = hull X.
Proof.
rewrite predeqE => d; split.
- move=> -[n [g [e [gX ->{d}]]]].
  move: (hull_is_convex X).
  by rewrite is_convex_setP /is_convex_set_n => /asboolP/(_ _ g e gX).
- by move/subset_hull.
Qed.

End hull_convex_set.

Section hull_setU.
Local Open Scope classical_set_scope.
Variable T : convType.
Import ScaledConvex.
Implicit Types Z : set T.

Definition scaled_set Z := [set x | if x is p *: a then Z a else True].

Lemma scalept_scaled_set Z r x :
  x \in scaled_set Z -> scalept r x \in scaled_set Z.
Proof.
rewrite /scalept; case: Rlt_dec => //= Hr; by [case: x | rewrite !in_setE].
Qed.

Lemma scaled_set_extract Z x (x0 : x != Zero) :
  x \in scaled_set Z -> [point of x0] \in Z.
Proof. by case: x x0. Qed.

Lemma addpt_scaled_set (X : {convex_set T}) x y :
  x \in scaled_set X -> y \in scaled_set X -> addpt x y \in scaled_set X.
Proof.
case: x => [p x|]; case: y => [q y|] //=; exact: mem_convex_set.
Qed.

Lemma ssum_scaled_set n (P : pred 'I_n) (X : {convex_set T}) (d : {fdist 'I_n})
  (g : 'I_n -> T) : (forall j, P j -> g j \in X) ->
  \ssum_(i | P i) scalept (d i) (S1 (g i)) \in scaled_set X.
Proof.
move=> PX; apply big_ind.
- by rewrite in_setE.
- exact: addpt_scaled_set.
- by move=> i /PX => giX; exact: scalept_scaled_set.
Qed.

Local Open Scope reals_ext_scope.

Lemma hull_setU (z : T) (X Y : {convex_set T}) : X !=set0 -> Y !=set0 ->
  hull (X `|` Y) z ->
  exists2 x, x \in X & exists2 y, y \in Y & exists p, z = x <| p |> y.
Proof.
move=> [dx ?] [dy ?] [n -[g [d [gT zg]]]].
suff [a] : exists2 a, a \in scaled_set X & exists2 b, b \in scaled_set Y &
    S1 z = addpt a b.
  have [/eqP -> _ [b bY]|a0 aX [b]] := boolP (a == Zero).
    rewrite add0pt => S1zy.
    exists dx; rewrite ?in_setE //; exists z; last by exists 0%:pr; rewrite conv0.
    by rewrite -(point_S1 z); apply: scaled_set_extract; rewrite S1zy.
  have [/eqP -> _|b0 bY] := boolP (b == Zero).
    rewrite addpt0 => S1zx.
    exists z; last by exists dy; rewrite ?in_setE //; exists 1%:pr; rewrite conv1.
    by rewrite -(point_S1 z); apply: scaled_set_extract; rewrite S1zx.
  rewrite addptE => -[_ zxy].
  exists [point of a0]; first exact: (@scaled_set_extract _ a).
  exists [point of b0]; first exact: scaled_set_extract.
  by eexists; rewrite zxy.
move/(congr1 (@S1 _)): zg; rewrite S1_convn.
rewrite (bigID (fun i => g i \in X)) /=.
set b := \ssum_(i | _) _.
set c := \ssum_(i | _) _.
move=> zbc.
exists b; first exact: ssum_scaled_set.
exists c => //.
apply: (@ssum_scaled_set _ [pred i | g i \notin X]) => i /=.
move/asboolP; rewrite in_setE.
by case: (gT (g i) (imageP _ I)).
Qed.

End hull_setU.

Section R_convex_space.
Implicit Types p q : prob.
Let avg p a b := (p * a + p.~ * b)%R.
Let avg1 a b : avg 1%:pr a b = a.
Proof. by rewrite /avg /= mul1R onem1 mul0R addR0. Qed.
Let avgI p x : avg p x x = x.
Proof. by rewrite /avg -mulRDl onemKC mul1R. Qed.
Let avgC p x y : avg p x y = avg p.~%:pr y x.
Proof. by rewrite /avg onemK addRC. Qed.
Let avgA p q (d0 d1 d2 : R) :
  avg p d0 (avg q d1 d2) = avg [s_of p, q] (avg [r_of p, q] d0 d1) d2.
Proof.
rewrite /avg /onem.
set s := [s_of p, q].
set r := [r_of p, q].
rewrite (mulRDr s) -addRA (mulRA s) (mulRC s); congr (_ + _)%R.
  by rewrite (p_is_rs p q) -/s.
rewrite mulRDr (mulRA _ _ d2).
rewrite -/p.~ -/q.~ -/r.~ -/s.~.
rewrite {2}(s_of_pqE p q) onemK; congr (_ + _)%R.
rewrite 2!mulRA; congr (_ * _)%R.
by rewrite pq_is_rs -/r -/s mulRC.
Qed.
HB.instance Definition _ (*R_convMixin*) := @isConvexSpace.Build R
  (Choice.class _) _ avg1 avgI avgC avgA.
Lemma avgRE p (x y : R) : x <| p |> y = avg p x y. Proof. by []. Qed.
Lemma avgR_oppD p x y : (- x <| p |> - y = - (x <| p |> y))%R.
Proof. by rewrite avgRE /avg 2!mulRN -oppRD. Qed.
Lemma avgR_mulDr p : right_distributive Rmult (fun x y => x <| p |> y).
Proof. by move=> x ? ?; rewrite avgRE /avg mulRDr mulRCA (mulRCA x). Qed.
Lemma avgR_mulDl p : left_distributive Rmult (fun x y => x <| p |> y).
Proof. by move=> x ? ?; rewrite avgRE /avg mulRDl -mulRA -(mulRA p.~). Qed.
(* Introduce morphisms to prove avgnE *)
Import ScaledConvex.
Definition scaleR x : R := if x is p *: y then p * y else 0.
Lemma Scaled1RK : cancel (@S1 _) scaleR.
Proof. by move=> x /=; rewrite mul1R. Qed.
Lemma scaleR_addpt : {morph scaleR : x y / addpt x y >-> (x + y)%R}.
Proof.
move=> [p x|] [q y|] /=; rewrite ?(add0R,addR0) //.
rewrite avgRE /avg /divRposxxy /= onem_div /Rdiv; last by apply Rpos_neq0.
rewrite -!(mulRC (/ _)%R) mulRDr !mulRA mulRV; last by apply Rpos_neq0.
by rewrite !mul1R (addRC p) addRK.
Qed.
Lemma scaleR0 : scaleR Zero = R0. by []. Qed.
Lemma scaleR_scalept r x : (0 <= r -> scaleR (scalept r x) = r * scaleR x)%R.
Proof.
case: x => [q y|]; last by rewrite scaleptR0 mulR0.
case=> r0. by rewrite scalept_gt0 /= mulRA.
by rewrite -r0 scalept0 mul0R.
Qed.
Definition big_scaleR := big_morph scaleR scaleR_addpt scaleR0.
Definition avgnR n (g : 'I_n -> R) (e : {fdist 'I_n}) := (\sum_(i < n) e i * g i)%R.
Lemma avgnRE n (g : 'I_n -> R) e : <|>_e g = avgnR g e.
Proof.
rewrite -[LHS]Scaled1RK S1_convn big_scaleR.
by apply eq_bigr => i _; rewrite scaleR_scalept // Scaled1RK.
Qed.
End R_convex_space.

Section fun_convex_space.
Variables (A : choiceType) (B : convType).
Let T := A -> B.
Implicit Types p q : prob.
Let avg p (x y : T) := fun a : A => (x a <| p |> y a).
Let avg1 (x y : T) : avg 1%:pr x y = x.
Proof. rewrite funeqE => a; exact/conv1. Qed.
Let avgI p (x : T) : avg p x x = x.
Proof. rewrite funeqE => a; exact/convmm. Qed.
Let avgC p (x y : T) : avg p x y = avg p.~%:pr y x.
Proof. rewrite funeqE => a; exact/convC. Qed.
Let avgA p q (d0 d1 d2 : T) :
  avg p d0 (avg q d1 d2) = avg [s_of p, q] (avg [r_of p, q] d0 d1) d2.
Proof. move=> *; rewrite funeqE => a; exact/convA. Qed.
HB.instance Definition _ := @isConvexSpace.Build T (Choice.class _) _
  avg1 avgI avgC avgA.
End fun_convex_space.

Section depfun_convex_space.
Variables (A : choiceType) (B : A -> convType).
Let T := dep_arrow_choiceType B.
Implicit Types p q : prob.
Let avg p (x y : T) := fun a : A => (x a <| p |> y a).
Let avg1 (x y : T) : avg 1%:pr x y = x.
Proof.
apply FunctionalExtensionality.functional_extensionality_dep => a.
exact/conv1.
Qed.
Let avgI p (x : T) : avg p x x = x.
Proof.
apply FunctionalExtensionality.functional_extensionality_dep => a.
exact/convmm.
Qed.
Let avgC p (x y : T) : avg p x y = avg p.~%:pr y x.
Proof.
apply FunctionalExtensionality.functional_extensionality_dep => a.
exact/convC.
Qed.
Let avgA p q (d0 d1 d2 : T) :
  avg p d0 (avg q d1 d2) = avg [s_of p, q] (avg [r_of p, q] d0 d1) d2.
Proof.
move => *.
apply FunctionalExtensionality.functional_extensionality_dep => a.
exact/convA.
Qed.
HB.instance Definition _ (*depfunConvType*) := @isConvexSpace.Build _ (Choice.class _)
  _ avg1 avgI avgC avgA.
End depfun_convex_space.

Section pair_convex_space.
Variables (A B : convType).
Let T := (A * B)%type.
Implicit Types p q : prob.
Let avg p (x y : T) := (x.1 <| p |> y.1, x.2 <| p |> y.2).
Let avg1 (x y : T) : avg 1%:pr x y = x.
Proof. rewrite /avg (conv1 x.1) (conv1 x.2); by case x. Qed.
Let avgI p (x : T) : avg p x x = x.
Proof. rewrite /avg (convmm _ x.1) (convmm _ x.2); by case x. Qed.
Let avgC p (x y : T) : avg p x y = avg p.~%:pr y x.
Proof. by congr (pair _ _); apply convC. Qed.
Let avgA p q (d0 d1 d2 : T) :
  avg p d0 (avg q d1 d2) = avg [s_of p, q] (avg [r_of p, q] d0 d1) d2.
Proof. move => *; congr (pair _ _); by apply convA. Qed.

HB.instance Definition _ (*pairConvType*) :=
  @isConvexSpace.Build T (Choice.class _) avg avg1 avgI avgC avgA.

End pair_convex_space.

Section fdist_convex_space.
Variable A : finType.
HB.instance Definition _ (*fdist_convType*) := @isConvexSpace.Build
  (fdist A) (Choice.class (choice_of_Type (fdist A)))
  (@ConvFDist.d A)
  (@ConvFDist.d1 _)
  (@ConvFDist.idempotent _)
  (@ConvFDist.skewed_commute _)
  (@ConvFDist.quasi_assoc _).
End fdist_convex_space.

Section scaled_convex_lemmas_depending_on_T_convType.
Import ScaledConvex.
Local Open Scope R_scope.

Lemma scalept_conv (T : convType) (x y : R) (s : scaled_pt T) (p : prob):
  0 <= x -> 0 <= y ->
  scalept (x <|p|> y) s = scalept x s <|p|> scalept y s.
Proof.
move=> x0 y0; rewrite scalept_addR; [|exact/mulR_ge0|exact/mulR_ge0].
by rewrite convptE !scalept_comp.
Qed.

Lemma big_scalept_conv_split (T : convType) (I : Type) (r : seq I) (P : pred I)
  (F G : I -> scaled_pt T) (p : prob) :
    \ssum_(i <- r | P i) (F i <|p|> G i) =
    (\ssum_(i <- r | P i) F i) <|p|> \ssum_(i <- r | P i) G i.
Proof. by rewrite convptE big_split /= !big_scalept. Qed.

Lemma scalept_addRnneg (T : convType) (x : scaled_pt T) :
    {morph (fun (r : Rnneg) => scalept r x) : r s / addRnneg r s >-> addpt r s}.
Proof. by move=> -[] r /= /leRP Hr [] s /= /leRP Hs; apply scalept_addR. Qed.

Definition big_scaleptl (T : convType) (x : scaled_pt T) :=
  @big_morph
    (@scaled_pt T)
    Rnneg
    (fun r : Rnneg => scalept r x)
    Zero
    (@addpt T)
    Rnneg0
    addRnneg
    (@scalept_addRnneg T x).

Lemma big_scaleptl' (T : convType) (x : scaled_pt T) :
  scalept R0 x = Zero ->
  forall (I : Type) (r : seq I) (P : pred I) (F : I -> R),
    (forall i : I, 0 <= F i) ->
    scalept (\sum_(i <- r | P i) F i) x = \ssum_(i <- r | P i) scalept (F i) x.
Proof.
move=> H I r P F H'.
transitivity (\ssum_(i <- r | P i) (fun r0 : Rnneg => scalept r0 x) (mkRnneg (H' i))); last reflexivity.
rewrite -big_scaleptl ?scalept0 //.
congr scalept.
transitivity (\sum_(i <- r | P i) mkRnneg (H' i)); first reflexivity.
apply (big_ind2 (fun x y => x = (Rnneg.v y))) => //.
by move=> x1 [v Hv] y1 y2 -> ->.
Qed.

End scaled_convex_lemmas_depending_on_T_convType.

Module Convn_finType.
Section def.
Local Open Scope R_scope.
Variables (A : convType) (T : finType) (d' : {fdist T}) (f : T -> A).
Let n := #| T |.
Definition t0 : T.
Proof.
move/card_gt0P/xchoose: (fdist_card_neq0 d') => t0; exact t0.
Defined.
Let enum : 'I_n -> T := enum_val.
Definition d_enum := [ffun i => d' (enum i)].
Lemma d_enum0 : forall b, 0 <= d_enum b. Proof. by move=> ?; rewrite ffunE. Qed.
Lemma d_enum1 : \sum_(b in 'I_n) d_enum b = 1.
Proof.
rewrite -(@FDist.f1 T d') (eq_bigr (d' \o enum)); last by move=> i _; rewrite ffunE.
rewrite (@reindex _ _ _ _ _ enum_rank) //; last first.
  by exists enum_val => i; [rewrite enum_rankK | rewrite enum_valK].
apply eq_bigr => i _; congr (d' _); by rewrite -[in RHS](enum_rankK i).
Qed.
Definition d : {fdist 'I_n} := FDist.make d_enum0 d_enum1.
Definition Convn_finType : A := <|>_d (f \o enum).
End def.
Module Exports.
Notation "'<$>_' d f" := (Convn_finType d f) : convex_scope.
End Exports.
End Convn_finType.
Export Convn_finType.Exports.

Section S1_Convn_finType.
Import ScaledConvex.
Variables (A : convType) (T : finType) (d : {fdist T}) (f : T -> A).
Lemma S1_Convn_finType :
  S1 (<$>_d f) = \ssum_i scalept (d i) (S1 (f i)).
Proof.
rewrite /Convn_finType.Convn_finType S1_convn /=.
rewrite (reindex_onto enum_rank enum_val) /=; last by move=> i _; rewrite enum_valK.
apply eq_big => /=; first by move=> i; rewrite enum_rankK eqxx.
move=> i _; rewrite /Convn_finType.d_enum ffunE.
by rewrite enum_rankK.
Qed.
End S1_Convn_finType.

Section S1_proj_Convn_finType.
Import ScaledConvex.
Variables (A B : convType) (prj : {affine A -> B}).
Variables (T : finType) (d : {fdist T}) (f : T -> A).

Lemma S1_proj_Convn_finType :
  S1 (prj (<$>_d f)) = \ssum_i scalept (d i) (S1 (prj (f i))).
Proof. by rewrite affine_function_Sum /=; exact: S1_Convn_finType. Qed.
End S1_proj_Convn_finType.

(* Ordered convex space *)

HB.mixin Record isOrdered (T : Type) := {
  orderedchoiceclass : Choice.class_of T ;
  leconv : T -> T -> Prop ;
  leconvR : forall a, leconv a a;
  leconv_trans : forall b a c, leconv a b -> leconv b c -> leconv a c ;
  eqconv_le : forall a b, a = b <-> leconv a b /\ leconv b a }.

#[short(type=orderedConvType)]
HB.structure Definition OrderedConvexSpace := {T of isOrdered T & ConvexSpace T}.

Canonical ordered_eqType (T : orderedConvType) := EqType T orderedchoiceclass.
Canonical ordered_choiceType (T : orderedConvType) :=
  ChoiceType T orderedchoiceclass.

Arguments leconv_trans {s b a c}.

Notation "x <= y" := (leconv x y) : ordered_convex_scope.
Notation "x <= y <= z" := (leconv x y /\ leconv y z) : ordered_convex_scope.

HB.instance Definition _ (* R_orderedConvType *) :=
  @isOrdered.Build R (Choice.class _) Rle leRR leR_trans eqR_le.

Module FunLe.
Section lefun.
Local Open Scope ordered_convex_scope.
Variables (T : convType) (U : orderedConvType).
Definition lefun (f g : T -> U) := forall a, f a <= g a.
Lemma lefunR f : lefun f f.
Proof. move => *; exact: leconvR. Qed.
Lemma lefun_trans g f h : lefun f g -> lefun g h -> lefun f h.
Proof. move => Hfg Hgh a; move : (Hfg a) (Hgh a); exact: leconv_trans. Qed.
Lemma eqfun_le f g : f = g <-> lefun f g /\ lefun g f.
Proof.
split; [move ->; by move: lefunR |].
case=> Hfg Hgh; rewrite funeqE => a.
move : (Hfg a) (Hgh a) => Hfg' Hgh'; exact/eqconv_le.
Qed.
End lefun.
End FunLe.

Section fun_ordered_convex_space.
Variables (T : convType) (U : orderedConvType).
Import FunLe.
HB.instance Definition _ (*fun_orderedConvType*) := @isOrdered.Build (T -> U)
  (Choice.class _) (@lefun T U) (@lefunR T U) (@lefun_trans T U) (@eqfun_le T U).
End fun_ordered_convex_space.

Module OppositeOrderedConvexSpace.
Section def.
Variable A : orderedConvType.

CoInductive T := mkOpp : A -> T.

Lemma A_of_TK : cancel (fun t => let: mkOpp a := t in a) mkOpp.
Proof. by case. Qed.

Definition A_of_T_eqMixin := CanEqMixin A_of_TK.

Canonical A_of_T_eqType := Eval hnf in EqType T A_of_T_eqMixin.

Definition A_of_T_choiceMixin := CanChoiceMixin A_of_TK.

Canonical A_of_T_choiceType := Eval hnf in ChoiceType T A_of_T_choiceMixin.
End def.

Section leopp.
Local Open Scope ordered_convex_scope.
Variable A : orderedConvType.
Notation T := (T A).
Definition leopp (x y : T) :=
  match (x, y) with (mkOpp x', mkOpp y') => y' <= x' end.

Lemma leoppR x : leopp x x.
Proof. case x; exact: leconvR. Qed.

Lemma leopp_trans y x z : leopp x y -> leopp y z -> leopp x z.
Proof. by move: x y z => [x] [y] [z] ? yz; apply: (leconv_trans yz). Qed.

Lemma eqopp_le x y : x = y <-> leopp x y /\ leopp y x.
Proof.
by split; [move ->; move: leoppR |move: x y => [x'] [y'] => /eqconv_le ->].
Qed.

End leopp.

Section convtype.
Local Open Scope convex_scope.
Variable A : orderedConvType.
Notation T := (T A).
Implicit Types p q : prob.
Definition unbox (x : T) := match x with mkOpp x' => x' end.
Definition avg p a b := mkOpp (unbox a <| p |> unbox b).

Lemma avg1 a b : avg 1%:pr a b = a.
Proof. by case a;case b=>b' a';rewrite/avg/unbox/=conv1. Qed.

Lemma avgI p x : avg p x x = x.
Proof. by case x=>x';rewrite/avg/unbox/=convmm. Qed.

Lemma avgC p x y : avg p x y = avg p.~%:pr y x.
Proof. by case x;case y=>y' x'; rewrite/avg/unbox/=convC. Qed.

Lemma avgA p q d0 d1 d2 :
  avg p d0 (avg q d1 d2) = avg [s_of p, q] (avg [r_of p, q] d0 d1) d2.
Proof. by case d0;case d1;case d2=>d2' d1' d0';rewrite/avg/unbox/=convA. Qed.

#[export]
HB.instance Definition _ := @isConvexSpace.Build T (Choice.class _) _
  avg1 avgI avgC avgA.

End convtype.
End OppositeOrderedConvexSpace.
HB.export OppositeOrderedConvexSpace.

Section opposite_ordered_convex_space.
Import OppositeOrderedConvexSpace.
Variable A : orderedConvType.

HB.instance Definition _ (*oppConvType*):= @isOrdered.Build (T A)
  (Choice.class _) (@leopp A) (@leoppR A) (@leopp_trans A) (@eqopp_le A).

End opposite_ordered_convex_space.

Notation "'\opp{' a '}'" := (OppositeOrderedConvexSpace.mkOpp a)
  (at level 10, format "\opp{ a }") : ordered_convex_scope.

Section opposite_ordered_convex_space_prop.
Local Open Scope ordered_convex_scope.
Import OppositeOrderedConvexSpace.
Variable A : orderedConvType.

Lemma conv_leoppD (a b : A) t : \opp{a} <|t|> \opp{b} = \opp{a <|t|> b}.
Proof. by []. Qed.

Lemma unboxK (a : A) : unbox (\opp{a}) = a.
Proof. reflexivity. Qed.

Lemma leoppP (a b : T A) : a <= b <-> unbox b <= unbox a.
Proof. by case a;case b=>*;rewrite !unboxK. Qed.

End opposite_ordered_convex_space_prop.

Section convex_function_def.
Local Open Scope ordered_convex_scope.
Variables (T : convType) (U : orderedConvType).
Implicit Types f : T -> U.

Definition convex_function_at f a b p := f (a <| p |> b) <= f a <| p |> f b.

(* NB(rei): move from 'I_n -> A to 'rV[A]_n? *)
Definition convex_function_at_Convn f n (a : 'I_n -> T) (d : {fdist 'I_n}) :=
  f (<|>_d a) <= <|>_d (f \o a).

Definition strictly_convexf_at f := forall a b (t : prob),
  a <> b -> (0 < t < 1)%R -> convex_function_at f a b t.

Lemma convex_function_atxx f a t : convex_function_at f a a t.
Proof. rewrite /convex_function_at !convmm; exact/leconvR. Qed.

End convex_function_def.

Definition convex_function (U : convType) (V : orderedConvType) (f : U -> V) :=
 forall a b (t : prob), convex_function_at f a b t.

(* see Additive in ssralg *)
HB.mixin Record isConvexFunction
    (U : convType) (V : orderedConvType) (f : U -> V) := {
  convex_functionP : convex_function f }.

HB.structure Definition ConvexFunction (U : convType) (V : orderedConvType) :=
  { f of isConvexFunction U V f }.

Arguments convex_functionP {U V} s.

Notation "{ 'convex' T '->' R }" :=
  (ConvexFunction.type T R) (at level 36, T, R at next level,
    format "{ 'convex'  T  '->'  R }") : convex_scope.

Section convex_function_prop'.
Local Open Scope ordered_convex_scope.
Variable (T : convType) (U V : orderedConvType).

Lemma convex_function_sym (f : T -> U) a b : (forall t, convex_function_at f a b t) ->
  forall t, convex_function_at f b a t.
Proof.
move => H t; move: (H t.~%:pr).
by rewrite /convex_function_at /= convC -probK (convC _ (f a)) -probK.
Qed.

Lemma convex_function_comp (f : {convex T -> U}) (g : {convex U -> V})
  (g_monotone_on_hull_Im_f : forall a b t,
    (f (a <|t|> b) <= f a <|t|> f b) -> (g (f (a <|t|> b)) <= g (f a <|t|> f b)))
  : convex_function (fun a => g (f a)).
Proof.
move=> a b t.
move : (convex_functionP g (f a) (f b) t).
rewrite /convex_function_at => Hg.
eapply leconv_trans; [| exact Hg] => {Hg}.
apply g_monotone_on_hull_Im_f.
exact: (convex_functionP f).
Qed.

Lemma convex_function_comp' (f : {convex T -> U}) (g : {convex U -> V})
  (g_monotone : forall x y, (x <= y) -> (g x <= g y))
  : convex_function (fun a => g (f a)).
Proof.
apply convex_function_comp => // *.
by apply g_monotone.
Qed.

End convex_function_prop'.

Section convex_in_both.
Local Open Scope ordered_convex_scope.
Variables (T U : convType) (V : orderedConvType) (f : T -> U -> V).
Definition convex_in_both := convex_function (uncurry f).
Lemma convex_in_bothP :
  convex_in_both
  <->
  forall a0 a1 b0 b1 t,
    f (a0 <| t |> a1) (b0 <| t |> b1) <= f a0 b0 <| t |> f a1 b1.
Proof.
split => [H a0 a1 b0 b1 t | H];
  first by move: (H (a0,b0) (a1,b1) t); rewrite /convex_function_at /uncurry.
by case => a0 b0 [a1 b1] t; move:(H a0 a1 b0 b1 t).
Qed.
End convex_in_both.

Section biconvex_function.
Local Open Scope ordered_convex_scope.
Section definition.
Variables (T U : convType) (V : orderedConvType) (f : T -> U -> V).
Definition biconvex_function :=
  (forall a, convex_function (f a)) /\ (forall b, convex_function (f^~ b)).
(*
Lemma biconvex_functionP : biconvex_function <->
  convex_function f /\ @convex_function B (fun_orderedConvType A C) (fun b a => f a b).
Proof.
change ((forall (a : A) (a0 b : B) (t : prob),
   f a (a0 <|t|> b) <= f a a0 <|t|> f a b) /\
  (forall (b : B) (a b0 : A) (t : prob),
   f (a <|t|> b0) b <= f a b <|t|> f b0 b) <->
  (forall (a b : A) (t : prob) (a0 : B),
   f (a <|t|> b) a0 <= f a a0 <|t|> f b a0) /\
  (forall (a b : B) (t : prob) (a0 : A),
   f a0 (a <|t|> b) <= f a0 a <|t|> f a0 b)).
by split; case => [H0 H1]; split => *; try apply H0; try apply H1.
Qed.
 *)
End definition.
Section counterexample.
Local Open Scope R_scope.

Example biconvex_is_not_convex_in_both :
  exists f : R -> R -> R, biconvex_function f /\ ~ convex_in_both f.
Proof.
exists Rmult; split.
split => [a b0 b1 t | b a0 a1 t]; rewrite /convex_function_at /=; rewrite avgRE; [rewrite avgR_mulDr|rewrite avgR_mulDl]; exact: leRR.
move /convex_in_bothP /(_ (-1)%R 1%R 1%R (-1)%R (probinvn 1)).
rewrite /leconv /probinvn /= 3!avgRE /=.
rewrite !(mul1R,mulR1,mulRN1) -oppRD onemKC.
rewrite (_ : - / (1 + 1) + (/ (1 + 1)).~ = 0); last first.
  by rewrite /onem addRCA -oppRD -div1R eps2 addRN.
rewrite mul0R leR_oppr oppR0 leRNgt; exact.
Qed.
End counterexample.
End biconvex_function.

Section concave_function_def.
Local Open Scope ordered_convex_scope.
Variables (A : convType) (B : orderedConvType).
Implicit Types f : A -> B.
Definition concave_function_at f a b t := @convex_function_at A _
  (fun a => \opp{f a}) a b t.
Definition concave_function_at' f a b t := (f a <| t |> f b <= f (a <| t |> b)).
Definition strictly_concavef_at f := forall a b (t : prob),
  a <> b -> (0 < t < 1)%R -> concave_function_at f a b t.
Lemma concave_function_at'P f a b t :
  concave_function_at' f a b t <-> concave_function_at f a b t.
Proof.
rewrite /concave_function_at'/concave_function_at/convex_function_at.
by rewrite conv_leoppD leoppP.
Qed.
End concave_function_def.

Definition concave_function (U : convType) (V : orderedConvType) (f : U -> V) :=
 forall a b (t : prob), concave_function_at f a b t.

HB.mixin Record isConcaveFunction
    (U : convType) (V : orderedConvType) (f : U -> V) := {
  concave_functionP : concave_function f }.

HB.structure Definition ConcaveFunction (U : convType) (V : orderedConvType) :=
  { f of isConcaveFunction U V f }.

Arguments concave_functionP {U V} s.

Notation "{ 'concave' T '->' R }" :=
  (ConvexFunction.type T R) (at level 36, T, R at next level,
    format "{ 'concave'  T  '->'  R }") : convex_scope.

Section concave_function_prop.
Local Open Scope ordered_convex_scope.
Variable (T : convType) (V : orderedConvType).

Section prop.
Variable (f : T -> V).

Lemma concave_function_atxx a t : concave_function_at f a a t.
Proof. exact: convex_function_atxx. Qed.
End prop.

Section Rprop.
Implicit Types f : T -> R.

Lemma R_convex_function_atN f a b t :
  concave_function_at f a b t -> convex_function_at (fun x => - f x)%R a b t.
Proof. by rewrite /convex_function_at /leconv /= avgR_oppD leR_oppl oppRK. Qed.

Lemma R_concave_function_atN f a b t :
  convex_function_at f a b t -> concave_function_at (fun x => - f x)%R a b t.
Proof.
rewrite /concave_function_at /convex_function_at.
rewrite /leconv/= /OppositeOrderedConvexSpace.leopp/=.
rewrite avgR_oppD.
rewrite /leconv/=.
by rewrite leR_oppl oppRK.
Qed.

Lemma R_convex_functionN f :
  concave_function f -> convex_function (fun x => - f x)%R.
Proof. move=> H a b t; exact/R_convex_function_atN/H. Qed.

Lemma R_concave_functionN f :
  convex_function f -> concave_function (fun x => - f x)%R.
Proof. move=> H a b t; exact/R_concave_function_atN/H. Qed.

Lemma R_convex_function_atN' f a b t :
  concave_function_at (fun x => - f x)%R a b t -> convex_function_at f a b t.
Proof. by move/(R_convex_function_atN);rewrite/convex_function_at !oppRK. Qed.

Lemma R_concave_function_atN' f a b t :
  convex_function_at (fun x => - f x)%R a b t -> concave_function_at f a b t.
Proof.
move/(R_concave_function_atN).
by rewrite/concave_function_at/convex_function_at !oppRK.
Qed.

Lemma R_convex_functionN' f :
  concave_function (fun x => - f x)%R -> convex_function f.
Proof. move=> H a b t; exact/R_convex_function_atN'/H. Qed.

Lemma R_concave_functionN' f :
  convex_function (fun x => - f x)%R -> concave_function f.
Proof. move=> H a b t; exact/R_concave_function_atN'/H. Qed.

End Rprop.

Section Rprop2.

Lemma R_convex_functionB f (g : T -> R) :
  convex_function f -> concave_function g -> convex_function (fun x => f x - g x)%R.
Proof.
move=> H1 H2 p q t.
rewrite /convex_function_at /=.
rewrite avgRE 2!mulRBr addRAC addRA.
move: (H1 p q t) => {}H1.
rewrite -addR_opp -addRA; apply leR_add => //.
rewrite -2!mulRN addRC; exact: (R_convex_functionN H2).
Qed.

Lemma R_concave_functionB f (g : T -> R) :
  concave_function f -> convex_function g -> concave_function (fun x => f x - g x)%R.
Proof.
move=> H1 H2.
rewrite (_ : (fun _ => _) = (fun x => - (g x - f x)))%R; last first.
  apply FunctionalExtensionality.functional_extensionality => x; by rewrite oppRB.
exact/R_concave_functionN/R_convex_functionB.
Qed.

End Rprop2.

End concave_function_prop.

Section affine_function_prop.
Variables (T : convType) (U : orderedConvType).

Lemma affine_functionP (f : T -> U) :
  affine f <-> convex_function f /\ concave_function f.
Proof.
split => [H | [H1 H2] p q t].
  split.
  - move=> p q t; rewrite /convex_function_at /= H //; exact/leconvR.
  - move=> p q t; rewrite /concave_function_at/= /convex_function_at/= H //; exact/leconvR.
by rewrite eqconv_le; split; [exact/H1|exact/H2].
Qed.

End affine_function_prop.

Section affine_function_image.
Local Open Scope classical_set_scope.
Variables T U : convType.

Proposition image_preserves_convex_hull (f : {affine T -> U}) (Z : set T) :
  f @` (hull Z) = hull (f @` Z).
Proof.
rewrite predeqE => b; split.
  case=> a [n [g [e [Hg]]]] ->{a} <-{b}.
  exists n, (f \o g), e; split.
    move=> b /= [i _] <-{b} /=.
    by exists (g i) => //; apply Hg; exists i.
  by rewrite affine_function_Sum.
case=> n [g [e [Hg]]] ->{b}.
suff [h Hh] : exists h : 'I_n -> T, forall i, Z (h i) /\ f (h i) = g i.
  exists (<|>_e h).
    exists n; exists h; exists e; split => //.
    move=> a [i _] <-.
    by case: (Hh i).
  rewrite affine_function_Sum; apply eq_convn => // i /=.
  by case: (Hh i).
apply (@fin_all_exists _ _ (fun i hi => Z hi /\ f hi = g i)) => i.
case: (Hg (g i)); first by exists i.
move=> a // HZa Hfa; by exists a.
Qed.

Lemma is_convex_set_image (f : {affine T -> U}) (a : {convex_set T}) :
  is_convex_set (f @` a).
Proof.
rewrite /is_convex_set.
apply/asboolP => x y p [a0 Ha0 <-{x}] [a1 Ha1 <-{y}].
exists (a0 <|p|> a1); last by rewrite affine_conv.
by rewrite -in_setE; apply/mem_convex_set; rewrite in_setE.
Qed.

End affine_function_image.

Section R_affine_function_prop.
Variables (T : convType) (f : T -> R).
Lemma R_affine_functionN : affine f -> affine (fun x => - f x)%R.
Proof.
move/affine_functionP => [H1 H2]; rewrite affine_functionP.
split => //; [exact/R_convex_functionN|exact/R_concave_functionN].
Qed.
End R_affine_function_prop.

Section convex_function_in_def.
Variables (T : convType) (U : orderedConvType) (D : convex_set T) (f : T -> U).

Definition convex_function_in :=
  forall a b p, a \in D -> b \in D -> convex_function_at f a b p.

Definition concave_function_in :=
  forall a b p, a \in D -> b \in D -> concave_function_at f a b p.

End convex_function_in_def.

(*
Lemma Conv2DistdE (A : choiceType) (a b : Dist A) (p : prob) (x : A) :
  (a <| p |> b) x = a x <| p |> b x.
Proof. by rewrite Conv2Dist.dE. Qed.


Lemma DistBindConv (A : finType) (B : finType)(p : prob) (dx dy : dist A) (f : A -> dist B) :
  DistBind.d dx f <|p|> DistBind.d dy f = DistBind.d (dx <|p|> dy) f.
Proof.
apply/dist_ext => b0.
rewrite !(Conv2Dist.dE,DistBind.dE) !big_distrr -big_split; apply eq_bigr => a0 _ /=.
by rewrite Conv2Dist.dE mulRDl 2!mulRA.
Qed.

Lemma rsum_Conv (A : finType) (p : prob) (dx dy : dist A):
  \rsum_(a in A) (dx a <|p|> dy a) =
  \rsum_(a in A) dx a <|p|> \rsum_(a in A) dy a.
Proof. by rewrite /Conv /= /avg big_split /= -2!big_distrr. Qed.

TODO: see convex_type.v
*)

Section convex_set_R.

Lemma Rpos_convex : is_convex_set (fun x => 0 < x)%R.
Proof.
apply/asboolP => x y t Hx Hy.
case/boolP : (t == 0%:pr) => [/eqP ->| Ht0]; first by rewrite conv0.
apply addR_gt0wl; first by apply mulR_gt0 => //; exact/prob_gt0.
apply mulR_ge0 => //; exact: ltRW.
Qed.

Definition Rpos_interval : {convex_set R} := CSet.Pack (CSet.Mixin Rpos_convex).

Lemma Rnonneg_convex : is_convex_set (fun x => 0 <= x)%R.
Proof. apply/asboolP=> x y t Hx Hy; apply addR_ge0; exact/mulR_ge0. Qed.

Definition Rnonneg_interval := CSet.Pack (CSet.Mixin Rnonneg_convex).

Lemma open_interval_convex a b (Hab : (a < b)%R) : is_convex_set (fun x => a < x < b)%R.
Proof.
apply/asboolP => x y t [xa xb] [ya yb].
case/boolP : (t == 0%:pr) => [/eqP|]t0; first by rewrite t0 conv0.
case/boolP : (t == 1%:pr) => [/eqP|]t1; first by rewrite t1 conv1.
apply conj.
- rewrite -[X in (X < t * x + t.~ * y)%R]mul1R -(onemKC t) mulRDl.
  apply ltR_add; rewrite ltR_pmul2l //; [exact/prob_gt0 | exact/onem_gt0/prob_lt1].
- rewrite -[X in (_ + _ < X)%R]mul1R -(onemKC t) mulRDl.
  apply ltR_add; rewrite ltR_pmul2l //; [exact/prob_gt0 | exact/onem_gt0/prob_lt1].
Qed.

Lemma open_unit_interval_convex : is_convex_set (fun x => 0 < x < 1)%R.
Proof. exact: open_interval_convex. Qed.

Definition open_unit_interval := CSet.Pack (CSet.Mixin open_unit_interval_convex).

End convex_set_R.

Section convex_function_R.

Implicit Types f : R -> R.

Lemma concave_function_atN f x y t : concave_function_at f x y t ->
  forall k, (0 <= k)%R -> concave_function_at (fun x => f x * k)%R x y t.
Proof.
move=> H k k0; rewrite /concave_function_at /convex_function_at.
rewrite conv_leoppD leoppP avgRE.
rewrite /leconv /= -avgR_mulDl.
exact: leR_wpmul2r.
Qed.

Lemma convexf_at_onem x y (t : prob) f : (0 < x -> 0 < y -> x < y ->
  convex_function_at f x y t -> convex_function_at f y x t.~%:pr)%R.
Proof.
move=> x0 y0 xy H; rewrite /convex_function_at.
rewrite [in X in leconv _ X]avgRE /= onemK addRC.
rewrite /convex_function_at !avgRE in H.
rewrite avgRE /= onemK addRC.
apply: (leR_trans H); rewrite addRC; exact/leRR.
Qed.

Lemma concavef_at_onem x y (t : prob) f : (0 < x -> 0 < y -> x < y ->
  concave_function_at f x y t -> concave_function_at f y x t.~%:pr)%R.
Proof.
move=>x0 y0 xy; rewrite/concave_function_at/convex_function_at.
rewrite !conv_leoppD !leoppP/=.
rewrite !avgRE /= onemK.
by rewrite addRC [in X in leconv _ X -> _]addRC.
Qed.
End convex_function_R.

(* NB:
Assume f is twice differentiable on an open interval I.
Let Df and DDf be the first and second derivatives of f.
Further assume DDf is always positive.  By applying MVT, we have :
forall a x \in I, exists c1 \in [a,x], f(x) = f(a) + (x-a) * Df(c1).
Fix a and x.  Applying MVT again, we further get :
exists c2 \in (a,c1), Df(c1) = Df(a) + (c1-a) * DDf(c2).
The two equations combined is :
f(x) = f(a) + (x-a) * Df(a) + (x-a)(c1-a) * DDf(c2).
The last term is then positive thanks to the assumption on DDf.
Now this is an equivalent condition to the convexity of f.
 *)

(* ref: http://www.math.wisc.edu/~nagel/convexity.pdf *)
Section twice_derivable_convex.

Variables (f : R -> R) (a b : R).
Let I := fun x0 => (a <= x0 <= b)%R.
Hypothesis HDf : pderivable f I.
Variable Df : R -> R.
Hypothesis DfE : forall x (Hx : I x), Df x = derive_pt f x (HDf Hx).
Hypothesis HDDf : pderivable Df I.
Variable DDf : R -> R.
Hypothesis DDfE : forall x (Hx : I x), DDf x = derive_pt Df x (HDDf Hx).
Hypothesis DDf_ge0 : forall x, I x -> (0 <= DDf x)%R.

Definition L (x : R) := (f a + (x - a) / (b - a) * (f b - f a))%R.

Hypothesis ab : (a < b)%R.

Lemma LE x : L x = ((b - x) / (b - a) * f a + (x - a) / (b - a) * f b)%R.
Proof.
rewrite /L mulRBr [in LHS]addRA addRAC; congr (_ + _)%R.
rewrite addR_opp -{1}(mul1R (f a)) -mulRBl; congr (_ * _)%R.
rewrite -(mulRV (b - a)); last by rewrite subR_eq0'; exact/gtR_eqF.
by rewrite -mulRBl -addR_opp oppRB addRA subRK addR_opp.
Qed.

Lemma convexf_ptP : (forall x, a <= x <= b -> 0 <= L x - f x)%R ->
  forall t : prob, convex_function_at f a b t.
Proof.
move=> H t; rewrite /convex_function_at.
set x := (t * a + t.~ * b)%R.
have : (a <= x <= b)%R.
  rewrite /x; split.
  - apply (@leR_trans (t * a + t.~ * a)).
      rewrite -mulRDl addRCA addR_opp subRR addR0 mul1R; exact/leRR.
    case/boolP : (t == 1%:pr) => [/eqP ->|t1].
      rewrite /onem subRR !mul0R !addR0; exact/leRR.
    rewrite leR_add2l; apply leR_wpmul2l => //; exact/ltRW.
  - apply (@leR_trans (t * b + t.~ * b)); last first.
      rewrite -mulRDl addRCA addR_opp subRR addR0 mul1R; exact/leRR.
    rewrite leR_add2r; apply leR_wpmul2l => //; exact/ltRW.
move/H; rewrite subR_ge0 => /leR_trans; apply.
rewrite LE //.
have -> : ((b - x) / (b - a) = t)%R.
  rewrite /x -addR_opp oppRD addRCA mulRBl mul1R oppRB (addRCA b).
  rewrite addR_opp subRR addR0 -mulRN addRC -mulRDr addR_opp.
  rewrite /Rdiv -mulRA mulRV ?mulR1 // subR_eq0'; exact/gtR_eqF.
have -> : ((x - a) / (b - a) = t.~)%R.
  rewrite /x -addR_opp addRAC -{1}(oppRK a) mulRN -mulNR -{2}(mul1R (- a)%R).
  rewrite -mulRDl (addRC _ R1) addR_opp -mulRDr addRC addR_opp.
  rewrite /Rdiv -mulRA mulRV ?mulR1 // subR_eq0'; exact/gtR_eqF.
exact/leRR.
Qed.

Lemma second_derivative_convexf_pt : forall t : prob, convex_function_at f a b t.
Proof.
have note1 : forall x, R1 = ((x - a) / (b - a) + (b - x) / (b - a))%R.
  move=> x; rewrite -mulRDl addRC addRA subRK addR_opp mulRV // subR_eq0'.
  exact/gtR_eqF.
have step1 : forall x, f x = ((x - a) / (b - a) * f x + (b - x) / (b - a) * f x)%R.
  by move=> x; rewrite -mulRDl -note1 mul1R.
apply convexf_ptP => // x axb.
rewrite /L.
case: axb.
  rewrite leR_eqVlt => -[-> _|].
  rewrite /L subRR div0R mul0R addR0 subRR; exact/leRR.
move=> ax.
rewrite leR_eqVlt => -[->|].
rewrite /L /Rdiv mulRV ?mul1R; last by rewrite subR_eq0'; exact/gtR_eqF.
rewrite addRC subRK subRR; exact/leRR.
move=> xb.
have {step1}step2 : (L x - f x =
  (x - a) * (b - x) / (b - a) * ((f b - f x) / (b - x)) -
  (b - x) * (x - a) / (b - a) * ((f x - f a) / (x - a)))%R.
  rewrite {1}step1 {step1}.
  rewrite -addR_opp oppRD addRA addRC addRA.
  rewrite LE //.
  rewrite {1}/Rdiv -(mulRN _ (f x)) -/(Rdiv _ _).
  rewrite addRA -mulRDr (addRC _ (f a)) (addR_opp (f a)).
  rewrite -mulRN -addRA -mulRDr (addR_opp (f b)).
  rewrite addRC.
  rewrite -(oppRK (f a - f x)) mulRN addR_opp oppRB.
  congr (_ + _)%R.
  - rewrite {1}/Rdiv -!mulRA; congr (_ * _)%R; rewrite mulRCA; congr (_ * _)%R.
    rewrite mulRCA mulRV ?mulR1 // subR_eq0'; exact/gtR_eqF.
  - rewrite -!mulNR -!mulRA; congr (_ * _)%R; rewrite mulRCA; congr (_ * _)%R.
    rewrite mulRCA mulRV ?mulR1 // subR_eq0'; exact/gtR_eqF.
have [c2 [Ic2 Hc2]] : exists c2, (x < c2 < b /\ (f b - f x) / (b - x) = Df c2)%R.
  have H : pderivable f (fun x0 => x <= x0 <= b)%R.
    move=> z [z1 z2]; apply HDf; split => //.
    apply (@leR_trans x) => //; exact: ltRW.
  case: (@MVT_cor1_pderivable x b f H xb) => c2 [Ic2 [H1 H2]].
  exists c2; split => //.
  rewrite H1 /Rdiv -mulRA mulRV ?mulR1; last first.
    by rewrite subR_eq0'; exact/gtR_eqF.
  rewrite DfE; last by move=> ?; exact: proof_derive_irrelevance.
  split.
    apply (@leR_trans x); [exact/ltRW | by case: Ic2 H1].
  by case: H2 => _ /ltRW.
have [c1 [Ic1 Hc1]] : exists c1, (a < c1 < x /\ (f x - f a) / (x - a) = Df c1)%R.
  have H : pderivable f (fun x0 => a <= x0 <= x)%R.
    move=> z [z1 z2]; apply HDf; split => //.
    apply (@leR_trans x) => //; exact: ltRW.
  case: (@MVT_cor1_pderivable a x f H ax) => c1 [Ic1 [H1 H2]].
  exists c1; split => //.
  rewrite H1 /Rdiv -mulRA mulRV ?mulR1; last first.
    by rewrite subR_eq0'; exact/gtR_eqF.
  rewrite DfE; last by move=> ?; exact: proof_derive_irrelevance.
  split.
  - by case: H2 => /ltRW.
  - apply (@leR_trans x).
    by case: H2 => _ /ltRW.
    apply (@leR_trans c2); apply/ltRW; by case: Ic2.
have c1c2 : (c1 < c2)%R by apply (@ltR_trans x); [case: Ic1 | case: Ic2].
have {step2 Hc1 Hc2}step3 : (L x - f x =
  (b - x) * (x - a) * (c2 - c1) / (b - a) * ((Df c2 - Df c1) / (c2 - c1)))%R.
  rewrite {}step2 Hc2 Hc1 (mulRC (x - a)%R) -mulRBr {1}/Rdiv -!mulRA.
  congr (_ * (_ * _))%R; rewrite mulRCA; congr (_ * _)%R.
  rewrite mulRCA mulRV ?mulR1 // subR_eq0'; by move/gtR_eqF : c1c2.
have [d [Id H]] : exists d, (c1 < d < c2 /\ (Df c2 - Df c1) / (c2 - c1) = DDf d)%R.
  have H : pderivable Df (fun x0 => c1 <= x0 <= c2)%R.
    move=> z [z1 z2]; apply HDDf; split => //.
    - apply (@leR_trans c1) => //; by case: Ic1 => /ltRW.
    - apply (@leR_trans c2) => //; by case: Ic2 => _ /ltRW.
  case: (@MVT_cor1_pderivable c1 c2 Df H c1c2) => d [Id [H1 H2]].
  exists d; split => //.
  rewrite H1 /Rdiv -mulRA mulRV ?mulR1; last first.
    by rewrite subR_eq0'; exact/gtR_eqF.
  rewrite DDfE; last by move=> ?; exact: proof_derive_irrelevance.
  split.
  - apply (@leR_trans c1); last by case: Id H1.
    by apply/ltRW; case: Ic1.
  - apply (@leR_trans c2); last by case: Ic2 => _ /ltRW.
    by case: H2 => _ /ltRW.
rewrite {}step3 {}H.
apply/mulR_ge0; last first.
  apply: DDf_ge0; split.
    apply (@leR_trans c1).
      apply/ltRW; by case: Ic1.
     by case: Id => /ltRW.
  apply (@leR_trans c2).
    by case: Id => _ /ltRW.
  apply/ltRW; by case: Ic2.
apply/mulR_ge0; last by apply/invR_ge0; rewrite subR_gt0.
apply/mulR_ge0; last first.
  by rewrite subR_ge0; case: Id => Id1 Id2; apply (@leR_trans d); exact/ltRW.
by apply/mulR_ge0; rewrite subR_ge0; exact/ltRW.
Qed.

End twice_derivable_convex.

Section ereal_convex.
Local Open Scope proba_scope.
Local Open Scope ereal_scope.

Let conv_ereal (p : prob) x y := (p : R)%:E * x + p.~%:E * y.

Let conv_ereal_conv1 a b : conv_ereal 1%:pr a b = a.
Proof. by rewrite /conv_ereal probpK onem1 /= mul1e mul0e adde0. Qed.

Let conv_ereal_convmm p a : conv_ereal p a a = a.
Proof.
rewrite /conv_ereal; case/boolP : (a \is a fin_num) => [?|].
  by rewrite -muleDl// -EFinD /GRing.add /= probKC mul1e.
rewrite fin_numE negb_and !negbK => /predU1P[-> | /eqP->].
- rewrite -ge0_muleDl.
  + by rewrite -EFinD /GRing.add /= probKC mul1e.
  + by rewrite lee_fin; apply/RleP/prob_ge0.
  + by rewrite lee_fin; apply/RleP/prob_ge0.
- rewrite -ge0_muleDl.
  + by rewrite -EFinD /GRing.add /= probKC mul1e.
  + by rewrite lee_fin; apply/RleP/prob_ge0.
  + by rewrite lee_fin; apply/RleP/prob_ge0.
Qed.

Let conv_ereal_convC p a b : conv_ereal p a b = conv_ereal (p.~)%:pr b a.
Proof. by rewrite [in RHS]/conv_ereal onemK addeC. Qed.

Lemma oprob_sg1 (p : oprob) : Num.sg (Prob.p p) = 1%R.
Proof.
case/ltR2P: (OProb.O1 p)=> /[swap] _ /RltP /(conj Num.Theory.sgr_cp0) [] <-.
by move/eqP.
Qed.

Let conv_ereal_convA p q a b c :
  conv_ereal p a (conv_ereal q b c) =
  conv_ereal [s_of p, q] (conv_ereal [r_of p, q] a b) c.
Proof.
rewrite /conv_ereal.
apply (prob_trichotomy' p);
  [ by rewrite s_of_0q r_of_0q !mul0e !add0e !onem0 !mul1e
  | by rewrite s_of_1q r_of_1q !mul1e !onem1 !mul0e !adde0
  | rewrite {p}=> p].
apply (prob_trichotomy' q);
  [ by rewrite s_of_p0 r_of_p0_oprob onem1 onem0 mul0e !mul1e add0e adde0
  | by rewrite s_of_p1 r_of_p1 onem1 !mul1e mul0e !adde0
  | rewrite {q}=> q].
have sgp := oprob_sg1 p.
have sgq := oprob_sg1 q.
have sgonemp := oprob_sg1 p.~%:opr.
have sgonemq := oprob_sg1 q.~%:opr.
have sgrpq := oprob_sg1 [r_of p, q]%:opr.
have sgspq := oprob_sg1 [s_of p, q]%:opr.
have sgonemrpq := oprob_sg1 [r_of p, q].~%:opr.
have sgonemspq := oprob_sg1 [s_of p, q].~%:opr.
Ltac mulr_infty X := do ! (rewrite mulr_infty X mul1e).
set sg := (sgp,sgq,sgonemp,sgonemq,sgrpq,sgspq,sgonemrpq,sgonemspq).
case: a=> [a | | ]; case: b=> [b | | ]; case: c=> [c | | ];
  try by mulr_infty sg.
rewrite muleDr // addeA.
congr (_ + _)%E; last by rewrite s_of_pqE onemK EFinM muleA.
rewrite muleDr //.
congr (_ + _)%E; first  by rewrite (p_is_rs p q) mulRC EFinM muleA.
rewrite muleA -!EFinM.
rewrite /GRing.mul /= (pq_is_rs (OProb.p p) q).
rewrite mulRA.
by rewrite (mulRC [r_of p, q].~).
Qed.

HB.instance Definition _ (*ereal_convType*) := @isConvexSpace.Build (\bar R)
  (Choice.class _) _ conv_ereal_conv1 conv_ereal_convmm conv_ereal_convC conv_ereal_convA.

Lemma conv_erealE p (a b : \bar R) : a <| p |> b = conv_ereal p a b.
Proof. by []. Qed.

End ereal_convex.
