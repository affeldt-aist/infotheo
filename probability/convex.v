(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg fingroup perm matrix.
From mathcomp Require Import mathcomp_extra boolp classical_sets Rstruct.
From mathcomp Require Import ssrnum ereal.
From mathcomp Require Import lra Rstruct reals.
Require Import Reals.
Require Import ssrR Reals_ext Ranalysis_ext ssr_ext ssralg_ext logb.
Require Import realType_ext fdist.
From mathcomp Require vector.

Undelimit Scope R_scope.
Delimit Scope R_scope with coqR.

(******************************************************************************)
(*                              Convexity                                     *)
(*                                                                            *)
(* This file provides the definition of convex spaces over a choiceType and   *)
(* of real cones, and use them to define convex sets, hulls, to show that     *)
(* probability distributions form convex spaces, and to define convex         *)
(* functions.                                                                 *)
(*                                                                            *)
(* Convex spaces:                                                             *)
(*         convType == the type of convex spaces, i.e., a choiceType with an  *)
(*                     operator x <| p |> y where p is a probability          *)
(*                     satisfying the following axioms:                       *)
(*            conv1 == a <| 1%:pr |> b = a.                                   *)
(*           convmm == a <| p |> a = a.                                       *)
(*            convC == a <| p |> b = b <| p.~%:pr |> a.                       *)
(*            convA == a <| p |> (b <| q |> c) =                              *)
(*                     (a <| [r_of p, q] |> b) <| [s_of p, q] |> c.           *)
(*          <|>_d f == generalization of the conv operator . <| . |> .        *)
(*                     type: forall A n, {fdist 'I_n} -> ('I_n -> A) -> A     *)
(*                     d is a finite distribution {fdist 'I_n}, f is a        *)
(*                     sequence of points 'I_n -> A, A is a convType          *)
(*  {affine T -> U} == affine function: homomorphism between convex spaces    *)
(*          <$>_d f := <|>_d (f \o enum_val)                                  *)
(*                     type: forall A T, {fdist T} -> (T -> A) -> A           *)
(*                     d is a finite distribution {fdist T}, f is a sequence  *)
(*                     of points T -> A, A is a convType, T, is a finType     *)
(*      segment x y := (fun p => conv p x y) @` [set: prob]                   *)
(*                                                                            *)
(*           scaled == Zero or a pair of a positive real (Rpos) with a point  *)
(*                     in some type (i.e., a "scaled point" noted p *: a,     *)
(*                     scope scaled_scope                                     *)
(*             S1 a := 1%:pos *: a                                            *)
(*  isQuasiRealCone == mixin of quasi real cones                              *)
(*                     see Def. 4.5 of [Varacca & Winskell, MSCS, 2006]       *)
(*            addpt == addition                                               *)
(*          scalept == scaling                                                *)
(* \ssum_(i <- r) F == iterated addpt                                         *)
(*       isRealCone == mixin of real cones                                    *)
(*                     Def. 4.5 of [Varacca & Winskell, MSCS, 2006]           *)
(* The mixins for real cones are instantiated with the type scaled A where    *)
(* A is a convType, addpt := rx + qy = (r+q)(x <| r/(r+q) |> y), and          *)
(* scalept := scalept r qy = (r*q)y.                                          *)
(* Moreover, when A is a convType, scaled A can be equipped with a            *)
(* structure of convex space by taking                                        *)
(* convpt p x y := addpt (scalept p x) (scalept p.~ y). This is the canonical *)
(* embedding of convex spaces into real cones.                                *)
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
(* orderedconvType == ordered convex space, a convType augmented with an      *)
(*                    order                                                   *)
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
Reserved Notation "{ 'affine' T '->' R }"
  (at level 36, T, R at next level, format "{ 'affine'  T  '->'  R }").
Reserved Notation "p *: a" (at level 40).

Declare Scope convex_scope.
Declare Scope ordered_convex_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.

Import Order.POrderTheory GRing.Theory Num.Theory.

Local Notation "{ 'fdist' T }" := (_ .-fdist T) : fdist_scope.

#[export] Hint Extern 0 (0 <= _)%coqR =>
  solve [apply/RleP/(FDist.ge0 _)] : core.
#[export] Hint Extern 0 (_ <= 1)%coqR =>
  solve [apply/RleP/(FDist.le1 _)] : core.
#[export] Hint Extern 0 (0 <= Prob.p _)%coqR =>
  solve [apply/RleP/(prob_ge0 _)] : core.
#[export] Hint Extern 0 (Prob.p _ <= 1)%coqR =>
  solve [apply/RleP/(prob_le1 _)] : core.

#[export] Hint Extern 0 (onem _ <= 1)%coqR =>
  exact/RleP/onem_le1 : core.
#[export] Hint Extern 0 (0 <= onem _)%coqR =>
  exact/RleP/onem_ge0 : core.

Fixpoint Convn (A : Type) (f : {prob R} -> A -> A -> A) n : {fdist 'I_n} -> ('I_n -> A) -> A :=
  match n return forall (e : {fdist 'I_n}) (g : 'I_n -> A), A with
  | O => fun e g => False_rect A (fdistI0_False e)
  | m.+1 => fun e g =>
    match Bool.bool_dec (e ord0 == 1%coqR) true with
    | left _ => g ord0
    | right H => let G := fun i => g (fdist_del_idx ord0 i) in
      f (probfdist e ord0) (g ord0) (Convn f (fdist_del (Bool.eq_true_not_negb _ H)) G)
    end
  end.

HB.mixin Record isConvexSpace0 T of Choice T := {
  conv : {prob R} -> T -> T -> T ;
  convn : forall n, {fdist 'I_n} -> ('I_n -> T) -> T ;
  convnE : forall n d g, convn n d g = Convn conv d g ;
  conv1 : forall a b, conv 1%:pr a b = a ;
  convmm : forall p a, conv p a a = a ;
  convC : forall p a b, conv p a b = conv (onem (Prob.p p))%:pr b a ;
  convA : forall (p q : {prob R}) (a b c : T),
      conv p a (conv q b c) = conv [s_of p, q] (conv [r_of p, q] a b) c }.


#[short(type=convType)]
HB.structure Definition ConvexSpace := {T of isConvexSpace0 T & }.
Arguments convn {s n}.

Notation "a <| p |> b" := (conv p a b) : convex_scope.
Local Open Scope convex_scope.

Section convex_space_lemmas.
Variables A : convType.
Implicit Types a b : A.
Import Reals_ext.

Lemma conv0 a b : a <| 0%:pr |> b = b.
Proof.
by rewrite convC /= (_ : _ %:pr = 1%:pr) ?conv1 //; apply/val_inj/onem0.
Qed.

Let Convn_fdist1 (n : nat) (j : 'I_n) (g : 'I_n -> A) :
  convn (fdist1 j) g = g j.
Proof.
elim: n j g => [[] [] //|n IH j g /=].
rewrite convnE {1}/Convn.
case: Bool.bool_dec => [/eqP|/Bool.eq_true_not_negb b01].
  rewrite fdist1E; case j0 : (_ == _) => /=.
    by move=> _; rewrite (eqP j0).
  by move/eqP; rewrite eq_sym R1E oner_eq0.
rewrite (_ : probfdist _ _ = 0%:pr) ?conv0; last first.
  apply val_inj => /=; move: b01; rewrite !fdist1E => j0.
  by case j0' : (_ == _) => //; rewrite j0' eqxx in j0.
have j0 : ord0 != j by apply: contra b01 => /eqP <-; rewrite fdist1xx.
have j0' : 0 < j by rewrite lt0n; apply: contra j0 => /eqP j0; apply/eqP/val_inj.
move=> [:H]; have @j' : 'I_n.
  by apply: (@Ordinal _ j.-1 _); abstract: H; rewrite prednK // -ltnS.
rewrite (_ : fdist_del b01 = fdist1 j'); last first.
  apply/fdist_ext => /= k.
  rewrite fdist_delE fdistD1E /= !fdist1E /= (negbTE j0) subr0 divr1.
  congr (GRing.natmul _ (nat_of_bool _)).
  move R : (k == _) => [|].
  - apply/eqP/val_inj; rewrite /= /bump leq0n add1n.
    by move/eqP : R => -> /=; rewrite prednK // lt0n.
  - apply: contraFF R => /eqP.
    move/(congr1 val) => /=; rewrite /bump leq0n add1n => kj.
    by apply/eqP/val_inj; rewrite /= -kj.
rewrite -/(Convn _ _) -convnE IH /fdist_del_idx ltn0; congr g.
by apply val_inj; rewrite /= /bump leq0n add1n prednK // lt0n.
Qed.

Let ConvnIE n (g : 'I_n.+1 -> A) (d : {fdist 'I_n.+1}) (i1 : d ord0 != 1%coqR) :
  convn d g = (g ord0) <| probfdist d ord0 |>
                  (convn (fdist_del i1) (fun x => g (fdist_del_idx ord0 x))).
Proof.
rewrite !convnE /=; case: Bool.bool_dec => /= [|/Bool.eq_true_not_negb] H.
exfalso; by rewrite (eqP H) eqxx in i1.
by rewrite (eq_irrelevance H i1).
Qed.

Let ConvnI1E (g : 'I_1 -> A) (e : {fdist 'I_1}) : convn e g = g ord0.
Proof.
rewrite convnE /=; case: Bool.bool_dec => // /Bool.eq_true_not_negb H.
exfalso; move/eqP: H; apply.
by apply/eqP; rewrite fdist1E1 (fdist1I1 e).
Qed.

Let ConvnI2E (g : 'I_2 -> A) (d : {fdist 'I_2}) :
  convn d g = (g ord0) <| probfdist d ord0 |> (g (lift ord0 ord0)).
Proof.
have [/eqP|i1] := eqVneq (d ord0) 1%coqR.
  rewrite fdist1E1 => /eqP ->; rewrite Convn_fdist1.
  rewrite (_ : probfdist _ _ = 1%:pr) ?conv1 //.
  by apply val_inj; rewrite /= fdist1xx.
rewrite ConvnIE; congr (conv _ _ _).
by rewrite ConvnI1E /fdist_del_idx ltnn.
Qed.

End convex_space_lemmas.


Section segment.
Variable A : convType.
Definition segment (x y : A) : set A := (fun p => conv p x y) @` [set: {prob R}].

Lemma segment_sym u v : (segment u v `<=` segment v u)%classic.
Proof. by move=> x [p _ <-]; exists ((Prob.p p).~%:pr); rewrite -?convC. Qed.

Lemma segmentC u v : segment u v = segment v u.
Proof. by rewrite eqEsubset; split; exact: segment_sym. Qed.

Lemma segmentL x y : segment x y x. Proof. by exists 1%:pr; rewrite ?conv1. Qed.

Lemma segmentR x y : segment x y y. Proof. by exists 0%:pr; rewrite ?conv0. Qed.

End segment.


Definition affine (U V : convType) (f : U -> V) :=
  forall p, {morph f : a b / a <| p |> b >-> a <| p |> b}.

HB.mixin Record isAffine (U V : convType) (f : U -> V) := {
  affine_conv : affine f }.

HB.structure Definition Affine (U V : convType) := {f of isAffine U V f}.

Notation "{ 'affine' T '->' R }" := (Affine.type T R) : convex_scope.

Section affine_function_instances.
Variables (U V W : convType) (f : {affine V -> W}) (h : {affine U -> V}).

Let affine_idfun : affine (@idfun U). Proof. by []. Qed.
HB.instance Definition _ := isAffine.Build _ _ idfun affine_idfun.

Let affine_comp : affine (f \o h).
Proof. by move=> x y t /=; rewrite 2!affine_conv. Qed.

HB.instance Definition _ := isAffine.Build _ _ (f \o h) affine_comp.

End affine_function_instances.

Declare Scope scaled_scope.
Delimit Scope scaled_scope with scaled.

Section scaled.
Variable A : Type.

(* Note: we need the argument of Scaled to be an Rpos, because otherwise
   addpt cannot make a commutative monoid:
   1) if addpt (Scaled 0 x) (Scaled 0 y) = Scaled 0 x commutativity fails
      so at least we need addpt (Scaled 0 x) (Scaled 0 y) = Zero
   2) if addpt (Scaled 0 x) Zero = Zero then left/right identity fail
   2) if addpt (Scaled 0 x) Zero = Scaled 0 x then associativity fails
      addpt (Scaled 0 x) (addpt (Scaled 0 y) (Scaled 0 z)) = Scaled 0 x
      addpt (addpt (Scaled 0 x) (Scaled 0 y)) (Scaled 0 z) = Scaled 0 z
   So we cannot allow 0 as argument to Scaled.                             *)
Inductive scaled := Scaled of Rpos & A | Zero.

Definition sum_of_scaled (m : scaled) : Rpos * A + unit :=
  match m with Scaled r a => inl _ (r, a) | Zero => inr _ tt end.

Local Notation "p *: a" := (Scaled p a).

Definition scaled_of_sum (m : (Rpos * A) + unit) :=
  match m with inl p => p.1 *: p.2 | inr n => Zero end.

Lemma sum_of_scaledK : cancel sum_of_scaled scaled_of_sum.
Proof. by case. Qed.

Definition S1 a : scaled := 1%:pos *: a.

Lemma Scaled_inj p : injective (Scaled p).
Proof. by move=> x y []. Qed.

Definition S1_inj : injective S1 := @Scaled_inj Rpos1.

Definition raw_weight (pt : scaled) : R := if pt is r *: _ then r else 0.

Lemma weight_ge0 pt : (0 <= raw_weight pt)%coqR.
Proof. by case: pt => /= [[x] /= /RltP/ltRW //|]. Qed.

Definition weight := mkNNFun weight_ge0.

Definition point pt : (weight pt > 0)%coqR -> A :=
 match pt with
 | t *: a => fun=> a
 | Zero => fun H : (weight Zero > 0)%coqR => match ltRR 0 H with end
 end.

Lemma point_Scaled p x H : @point (p *: x) H = x.
Proof. by []. Qed.

Lemma Scaled_point x H : mkRpos H *: @point x H = x.
Proof.
by case: x H => [p x|] H; [congr (_ *: _); apply val_inj | case: (ltRR 0)].
Qed.

End scaled.
Arguments Zero {A}.
Arguments point {A} pt.
Arguments weight {A}.
Notation "p *: a" := (Scaled p a) : scaled_scope.

HB.instance Definition _ (A : eqType) := Equality.copy (scaled A) (can_type (@sum_of_scaledK A)).
HB.instance Definition _ (A : choiceType) := Choice.copy (scaled A) (can_type (@sum_of_scaledK A)).

Section scaled_eqType.
Variable A : eqType.

Lemma S1_neq0 a : S1 a != @Zero A. Proof. by []. Qed.

(* TODO: rm? *)
Lemma weight_gt0 a : a != @Zero A -> (0 < weight a)%coqR.
Proof. by case: a => // p x _ /=. Qed.

Lemma weight_gt0b a : a != @Zero A -> (weight a > 0)%mcR.
Proof. by move=> ?; exact/RltP/weight_gt0. Qed.

Definition weight_neq0 a (a0 : a != @Zero A) := Rpos.mk (weight_gt0b a0).

Local Notation "[ 'point' 'of' x ]" := (@point _ _ (@weight_gt0 _ x))
  (at level 0, format "[ 'point'  'of'  x ]").
Local Notation "[ 'weight' 'of' x ]" := (weight_neq0 x)
  (at level 0, format "[ 'weight'  'of'  x ]").

Lemma point_S1 a : [point of S1_neq0 a] = a.
Proof. by []. Qed.

Lemma weight0_Zero a : weight a = 0%coqR -> a = @Zero A.
Proof. by case: a => //= r c /esym Hr; move/ltR_eqF: (Rpos_gt0 r) => /eqP. Qed.

End scaled_eqType.
Notation "[ 'point' 'of' x ]" := (@point _ _ (@weight_gt0 _ _ x))
  (at level 0, format "[ 'point'  'of'  x ]").
Notation "[ 'weight' 'of' x ]" := (weight_neq0 x)
  (at level 0, format "[ 'weight'  'of'  x ]").

HB.mixin Record isQuasiRealCone A of Choice A := {
  addpt : A -> A -> A ;
  zero : A ;
  addptC : commutative addpt ;
  addptA : associative addpt ;
  addpt0 : right_id zero addpt ;
  scalept : R -> A -> A ;
  scale0pt : forall x, scalept 0%coqR x = zero ;
  scale1pt : forall x, scalept 1%coqR x = x ;
  scaleptDr : forall r, {morph scalept r : x y / addpt x y >-> addpt x y} ;
  scaleptA : forall p q x, (0 <= p)%coqR -> (0 <= q)%coqR ->
    scalept p (scalept q x) = scalept (p * q)%coqR x }.

#[short(type=quasiRealCone)]
HB.structure Definition QuasiRealCone := { A of isQuasiRealCone A & }.

Section quasireal_cone_theory.
Variable A : quasiRealCone.

Lemma add0pt : left_id (@zero A) addpt.
Proof. by move=> ?; rewrite addptC addpt0. Qed.

Lemma scalept0 p : (0 <= p)%coqR -> scalept p zero = @zero A.
Proof.
by move=> p0; rewrite -[in LHS](scale0pt zero) scaleptA// mulR0 scale0pt.
Qed.

HB.instance Definition _ :=
  Monoid.isComLaw.Build A (@zero A) (@addpt A) addptA addptC add0pt.

Definition big_morph_scalept q :=
  @big_morph _ _ (@scalept A q) zero addpt zero _ (@scaleptDr A q).

Local Notation "\ssum_ ( i <- r ) F" := (\big[addpt/@zero A]_(i <- r) F).
Local Notation "\ssum_ ( i : t ) F" := (\big[addpt/@zero A]_(i : t) F) (only parsing).
Local Notation "\ssum_ i F" := (\big[addpt/@zero A]_i F).
Local Notation "\ssum_ ( i | P ) F" := (\big[addpt/@zero A]_(i | P) F).
Local Notation "\ssum_ ( i < n | P ) F" := (\big[addpt/@zero A]_(i < n | P%B) F).
Local Notation "\ssum_ ( i < n ) F" := (\big[addpt/@zero A]_(i < n) F).

Definition barycenter (pts : seq A) := \ssum_(x <- pts) x.

Lemma barycenter_map (T : finType) (F : T -> A) :
  barycenter [seq F i | i <- enum T] = \ssum_i F i.
Proof. by rewrite /barycenter big_map big_filter. Qed.

Lemma scalept_barycenter p (H : (0 <= p)%coqR) pts :
  scalept p (barycenter pts) = barycenter [seq scalept p i | i <- pts].
Proof. by rewrite big_morph_scalept ?scalept0// /barycenter big_map. Qed.

Lemma ssum_perm n (F : 'I_n -> A) (pe : 'S_n) :
  \ssum_(i < n) F i = \ssum_(i < n) F (pe i).
Proof.
rewrite -!barycenter_map /barycenter big_map map_comp big_map.
exact/perm_big/perm_eq_perm.
Qed.

End quasireal_cone_theory.
Notation "\ssum_ ( i <- r ) F" := (\big[addpt/@zero _]_(i <- r) F).
Notation "\ssum_ ( i <- r | P ) F" := (\big[addpt/@zero _]_(i <- r | P ) F).
Notation "\ssum_ ( i : t ) F" := (\big[addpt/@zero _]_(i : t) F) (only parsing).
Notation "\ssum_ i F" := (\big[addpt/@zero _]_i F).
Notation "\ssum_ ( i | P ) F" := (\big[addpt/@zero _]_(i | P) F).
Notation "\ssum_ ( i < n | P ) F" := (\big[addpt/@zero _]_(i < n | P%B) F).
Notation "\ssum_ ( i < n ) F" := (\big[addpt/@zero _]_(i < n) F).

HB.mixin Record isRealCone A of QuasiRealCone A := {
  scaleptDl : forall (p q : R) (x : A), (0 <= p)%coqR -> (0 <= q)%coqR ->
    scalept (p + q)%coqR x = addpt (scalept p x) (scalept q x)
}.

#[short(type=realCone)]
HB.structure Definition RealCone := { A of isRealCone A & }.

Section real_cone_theory.
Variable A : realCone.

Lemma scalept_sum (B : finType) (P : pred B) (F : B ->R^+) (x : A) :
  scalept (\sum_(i | P i) F i) x = \ssum_(b | P b) scalept (F b) x.
Proof.
apply: (@proj1 _ (0 <= \sum_(i | P i) F i))%coqR.
apply: (big_ind2 (fun y q => scalept q x = y /\ (0 <= q)))%coqR.
+ by split; [rewrite scale0pt//|exact/Rle_refl].
+ move=> _ x2 _ y2 [<- ?] [<- ?].
  by rewrite scaleptDl //; split => //; exact: addR_ge0.
+ by move=> i _; split => //; exact/nneg_f_ge0.
Qed.

Section barycenter_fdist_convn.
Variables (n : nat) (B : finType).
Variable p : R.-fdist 'I_n.
Variable q : 'I_n -> R.-fdist B.
Variable h : B -> A.

Lemma ssum_fdist_convn :
  (* TODO: \ssum_(j in B) notation? *)
  \ssum_(i < n) scalept (p i) (\ssum_(j <- enum B) scalept (q i j) (h j)) =
  \ssum_(j <- enum B) scalept (fdist_convn p q j) (h j).
Proof.
transitivity (\ssum_i \ssum_(i0 <- enum B) scalept (p i) (scalept (q i i0) (h i0))).
  by apply eq_bigr => i _; rewrite big_morph_scalept// scalept0.
rewrite exchange_big /=; apply eq_bigr => j _; rewrite fdist_convnE.
have HF i : (0 <= p i * q i j)%coqR by exact/mulR_ge0.
rewrite (scalept_sum _ (mkNNFun HF)) /=; apply eq_bigr => i _.
by rewrite scaleptA.
Qed.

End barycenter_fdist_convn.

End real_cone_theory.

Section real_cone_instance.
Import Order.TotalTheory.

Variable A : convType.
Local Open Scope R_scope.
Local Open Scope convex_scope.
Local Open Scope scaled_scope.

Let addpt (a b : scaled A) :=
  match a, b with
  | r *: x, q *: y => (r + q)%:pos *: (x <| (((r / (r + q))%:pos))%:pr |> y)
  | _, Zero => a
  | Zero, _ => b
  end.

Let addptC' : commutative addpt.
Proof.
move=> [r x|] [q y|] //=; congr (_ *: _); first by apply: val_inj; rewrite /= addRC.
rewrite convC; congr (_ <| _ |> _); apply/val_inj => /=.
by rewrite RdivE' RplusE onem_divRxxy.
Qed.

Let addptA' : associative addpt.
Proof.
move=> [p x|] [q y|] [r z|] //=; congr (_ *: _); first by apply val_inj; rewrite /= addRA.
rewrite convA; congr (_<| _ |> _); first exact: s_of_Rpos_probA.
congr (_ <| _ |> _).
rewrite /=.
exact: r_of_Rpos_probA. (* TODO: clean *)
Qed.

Let addpt0 : right_id (@Zero A) addpt. Proof. by case. Qed.

Let add0pt : left_id (@Zero A) addpt. Proof. by case. Qed.

Let scalept p (x : scaled A) :=
  match Rlt_dec 0 p, x with
  | left Hr, q *: y => (mkRpos Hr * q)%:pos *: y
  | _, _ => Zero
  end.

Let scale0pt x : scalept 0 x = Zero.
Proof. by rewrite /scalept; case: Rlt_dec => // Hr; case: (ltRR 0). Qed.

Let scalept0 p : scalept p Zero = Zero.
Proof. by rewrite /scalept; case: Rlt_dec. Qed.

Let scale1pt x : scalept 1 x = x.
Proof.
case: x => [r c|]; last by rewrite scalept0.
by rewrite /scalept/=; case: Rlt_dec => //= ?; congr (_ *: _); apply/val_inj => /=; rewrite mul1R.
Qed.

Let scaleptDr r : {morph scalept r : x y / addpt x y >-> addpt x y}.
Proof.
rewrite /scalept; case: Rlt_dec => // r_gt0 x y.
case: x => [p x|]; last by rewrite !add0pt.
case: y => [q y|]; last by rewrite !addpt0.
congr (_ *: _); first by apply val_inj => /=; rewrite mulRDr.
congr (_ <| _ |> _); apply val_inj; rewrite /= -mulRDr divRM ?gtR_eqF//.
by rewrite /Rdiv -(mulRAC r) mulRV ?mul1R // gtR_eqF.
Qed.

Let scalept_gt0 p (q : Rpos) x (p_gt0 : 0 < p) :
  scalept p (q *: x) = (mkRpos p_gt0 * q)%:pos *: x.
Proof.
by rewrite /scalept; case: Rlt_dec => // Hr; congr (_ *: _); exact/val_inj.
Qed.

Let scaleptA p q x : 0 <= p -> 0 <= q -> scalept p (scalept q x) = scalept (p * q) x.
Proof.
case=> Hp; last by rewrite -Hp mul0R !scale0pt.
case=> Hq; last by rewrite -Hq mulR0 scale0pt scalept0.
case: x => [r x|]; rewrite ?scalept0 // !scalept_gt0; first exact: mulR_gt0.
by move=> Hpq; congr (_ *: _); apply val_inj => /=; rewrite mulRA.
Qed.

HB.instance Definition _ :=
  isQuasiRealCone.Build (scaled A) addptC' addptA' addpt0 scale0pt scale1pt scaleptDr scaleptA.

Let scaleptDl p q x : 0 <= p -> 0 <= q ->
  scalept (p + q) x = addpt (scalept p x) (scalept q x).
Proof.
case=> p0; last by rewrite -p0 scale0pt add0R add0pt.
case=> q0; last by rewrite -q0 scale0pt addR0 addpt0.
case: x => [r c|]; last by rewrite !scalept0.
rewrite !scalept_gt0 => [|pq0 /=]; first by apply addR_gt0.
by rewrite convmm; congr (_ *: _); apply val_inj; rewrite /= mulRDl.
Qed.

HB.instance Definition _ := @isRealCone.Build (scaled A) scaleptDl.

End real_cone_instance.

Section convpt_convex_space.
Variable A : convType.

Let convpt (p : {prob R}) (x y : scaled A) :=
  addpt (scalept (Prob.p p) x) (scalept (Prob.p p).~ y).

Let convpt1 a b : convpt (1%:pr) a b = a.
Proof. by rewrite /convpt onem1 scale1pt scale0pt addpt0. Qed.

Let convptmm (p : {prob R}) a : convpt p a a = a.
Proof.
rewrite /convpt -scaleptDl//.
by rewrite RplusE onemKC scale1pt //.
Qed.

Let convptC (p : {prob R}) a b : convpt p a b = convpt ((Prob.p p).~)%:pr b a.
Proof. by rewrite [RHS]addptC onemK. Qed.

Let convptA (p q : {prob R}) a b c :
  convpt p a (convpt q b c) = convpt [s_of p, q] (convpt [r_of p, q] a b) c.
Proof.
rewrite /convpt.
rewrite !scaleptDr !scaleptA //.
rewrite -[RHS]addptA; congr addpt.
  by rewrite (p_is_rs p q) mulRC.
rewrite RmultE pq_is_rs mulrC -RmultE.
by rewrite s_of_pqE onemK RmultE.
Qed.

Let convn := Convn convpt.

HB.instance Definition _ :=
  @isConvexSpace0.Build (scaled A) convpt convn (fun _ _ _ => erefl) convpt1 convptmm convptC convptA.

Lemma convptE p (a b : scaled A) : a <| p |> b = convpt p a b.
Proof. by []. Qed.

End convpt_convex_space.

Section scaled_convex.
Variable A : convType.
Local Open Scope R_scope.
Local Open Scope convex_scope.
Local Open Scope scaled_scope.

Lemma scalept_Scaled p q (x : A) : scalept p (q *: x) = scalept (p * q) (S1 x).
Proof.
rewrite /scalept /=.
case: Rlt_dec => Hp; case: Rlt_dec => Hpq //.
- congr (_ *: _); apply val_inj; by rewrite /= mulR1.
- elim Hpq; by apply /mulR_gt0.
- elim Hp; move/pmulR_lgt0: Hpq; exact.
Qed.

Lemma scalept_gt0 p (q : Rpos) (x : A) (H : 0 < p) :
  scalept p (q *: x) = (mkRpos H * q)%:pos *: x.
Proof.
rewrite /scalept /= ; case: Rlt_dec => // Hr.
by congr (_ *: _); apply val_inj.
Qed.

Lemma addptE a b (a0 : a != @Zero A) (b0 : b != Zero) :
  let p := [weight of a0] in
  let q := [weight of b0] in
  let x := [point of a0] in
  let y := [point of b0] in
  addpt a b = (p + q)%:pos *: (x <| ((p / (p + q))%:pos)%:pr |> y).
Proof.
move: a b => [p x|//] [pb y|//] /= in a0 b0 *.
by congr (_ *: (_ <| _ |> _)); exact: val_inj.
Qed.

Lemma weight_addpt : {morph @weight A : x y / addpt x y >-> x + y}.
Proof. move=> [p x|] [q y|] //=; by rewrite (add0R, addR0). Qed.

Lemma weight0 : weight (@Zero A) = 0. Proof. by []. Qed.

Lemma scalept_weight p (x : scaled A) : 0 <= p -> weight (scalept p x) = p * weight x.
Proof.
case=> [p0|<-]; last by rewrite scale0pt mul0R.
case: x => [r y|]; first by rewrite /= /scalept/=; case: Rlt_dec.
by rewrite scalept0 ?mulR0//; exact/ltRW.
Qed.

Lemma weight_barycenter (pts : seq (scaled A)) :
  weight (barycenter pts) = \sum_(x <- pts) weight x.
Proof. by rewrite (big_morph weight weight_addpt weight0). Qed.

Section adjunction.

Lemma affine_S1 : affine (@S1 A).
Proof.
move=> p x y.
have /RleP[p0|p0] := prob_ge0 p; last first.
  by rewrite (_ : p = 0%:pr) ?conv0 //; exact/val_inj.
have /RleP[p1|p1] := prob_le1 p; last first.
  by rewrite (_ : p = 1%:pr) ?conv1 //; exact/val_inj.
rewrite convptE (scalept_gt0 _ _ p0) (@scalept_gt0 (Prob.p p).~).
  exact/RltP/onem_gt0/RltP.
move=> mp0; congr (_ *: _) => /=.
  apply/val_inj => /=; rewrite !mulR1.
  by rewrite RplusE onemKC.
by congr (_ <| _ |> _); apply val_inj; rewrite /= !mulR1 addRC subRK divR1.
Qed.

HB.instance Definition _ := isAffine.Build _ _ (@S1 A) affine_S1.

End adjunction.

End scaled_convex.

Notation "'<|>_' d f" := (Convn (@conv _) d f) : convex_scope.

Section convex_space_prop1.
Variables T : convType.
Implicit Types a b : T.

Lemma convA0 (p q r s : {prob R}) a b c :
  Prob.p p = (Prob.p r * Prob.p s)%coqR :> R -> ((Prob.p s).~ = (Prob.p p).~ * (Prob.p q).~)%coqR ->
  a <| p |> (b <| q |> c) = (a <| r |> b) <| s |> c.
Proof.
move=> H1 H2.
have [r0|r0] := eqVneq r 0%:pr.
  rewrite r0 conv0 (_ : p = 0%:pr) ?conv0; last first.
    by apply/val_inj; rewrite /= H1 r0 mul0R.
  congr (_ <| _ |> _); move: H2; rewrite H1 r0 mul0R onem0 mul1R.
  by move/(congr1 (@onem R)); rewrite !onemK => ?; exact/val_inj.
have [s0|s0] := eqVneq s 0%:pr.
  have p0 : p = 0%:pr by apply/val_inj; rewrite /= H1 s0 mulR0.
  rewrite s0 conv0 p0 // ?conv0.
  rewrite (_ : q = 0%:pr) ?conv0 //.
  move: H2; rewrite p0 onem0 mul1R => /(congr1 (@onem R)); rewrite !onemK => sq.
  by rewrite -s0; exact/val_inj.
rewrite convA; congr ((_ <| _ |> _) <| _ |> _).
  apply val_inj; rewrite /= s_of_pqE.
  move/(congr1 (@onem R)) : H2.
  by rewrite onemK => ->.
exact: (@r_of_pq_is_r _ _ _ _ s).
Qed.

Lemma convA' (r s : {prob R}) a b c :
  a <| [p_of r, s] |> (b <| [q_of r, s] |> c) = (a <| r |> b) <| s |> c.
Proof.
have [/eqP|H] := eqVneq [p_of r, s] 1%:pr.
  by move=> /p_of_rs1P[-> ->]; rewrite p_of_r1 3!conv1.
have [->|s0] := eqVneq s 0%:pr; first by rewrite p_of_r0 q_of_r0 3!conv0.
by rewrite convA s_of_pqK// r_of_pqK.
Qed.

(* TODO: move *)
Lemma onem_probR_ge0 (p: {prob R}) : (0 <= (Prob.p p).~)%coqR.
Proof. exact/RleP/onem_ge0/prob_le1. Qed.
Hint Resolve onem_probR_ge0 : core.

Lemma convACA (a b c d : T) p q :
  (a <|q|> b) <|p|> (c <|q|> d) = (a <|p|> c) <|q|> (b <|p|> d).
Proof.
apply: S1_inj; rewrite ![in LHS]affine_conv/= !convptE.
rewrite !scaleptDr !scaleptA// !(mulRC (Prob.p p)) !(mulRC (Prob.p p).~) addptA addptC.
rewrite (addptC (scalept (Prob.p q * Prob.p p) _)) !addptA -addptA -!scaleptA -?scaleptDr//.
by rewrite !(addptC (scalept _.~ _)) !affine_conv.
Qed.

Lemma convDr (x y z : T) (p q : {prob R}) :
  x <| p |> (y <| q |> z) = (x <| p |> y) <| q |> (x <| p |> z).
Proof. by rewrite -{1}(convmm q x) convACA. Qed.

Lemma convACA' (a b c d : T) (p q r : {prob R}) :
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
rewrite (convC p) convA convC !convA.
set C0 := _.~%:pr.
set C1 := _.~%:pr.
rewrite -convA' (convC _ d) convC.
by eexists; eexists; eexists; congr ((_ <|_|> _) <|_|> (_ <|_|> _)).
Qed.

Local Open Scope vec_ext_scope.

Section with_affine_projection.
Variable U : convType.
Variable prj : {affine T -> U}.
Local Open Scope scaled_scope.

Definition map_scaled (x : scaled T) : scaled U :=
  if x is p *: a then p *: prj a else Zero.

Lemma affine_map_scaled : affine map_scaled.
Proof.
move=> p [q x|] [r y|] /=; rewrite 2!convptE ?scalept0 //.
- rewrite !(scalept_Scaled (Prob.p p)) !(scalept_Scaled (Prob.p p).~) /= /scalept /=.
  case: Rlt_dec => Hpq; case: Rlt_dec => Hpr //=; congr (_ *: _).
  by rewrite affine_conv.
- by rewrite !addpt0 !(scalept_Scaled (Prob.p p)) /= /scalept /=; case: Rlt_dec.
- by rewrite !add0pt !(scalept_Scaled (Prob.p p).~) /= /scalept/=; case: Rlt_dec.
Qed.

HB.instance Definition _ := isAffine.Build _ _ map_scaled affine_map_scaled.

Lemma S1_Convn_proj n (g : 'I_n -> T) d :
  S1 (prj (<|>_d g)) = \ssum_(i < n) scalept (d i) (S1 (prj (g i))).
Proof.
elim: n g d => [|n IH] g d.
  by move: (FDist.f1 d); rewrite /= big_ord0 => /Rlt_not_eq; case.
rewrite /=; case: Bool.bool_dec => [/eqP|/Bool.eq_true_not_negb]Hd.
  rewrite (bigD1 ord0) //= Hd big1 /=.
    rewrite addpt0 (@scalept_gt0 _ 1).
    by congr (_ *: _); apply val_inj; rewrite /= mulR1.
  move=> i Hi; have := FDist.f1 d.
  rewrite (bigD1 ord0) ?inE // Hd /= -RplusE addRC => /(f_equal (Rminus^~ R1)).
  rewrite addRK subRR => /eqP.
  rewrite psumr_eq0// => /allP/= => /(_ i).
  by rewrite mem_index_enum Hi implyTb => /(_ isT)/eqP ->; rewrite scale0pt.
set d' := fdist_del Hd.
set g' := fun i => g (fdist_del_idx ord0 i).
rewrite /index_enum -enumT (bigD1_seq ord0) ?enum_uniq ?mem_enum //=.
rewrite -big_filter (perm_big (map (lift ord0) (enum 'I_n))); last first.
  exact: perm_filter_enum_ord.
rewrite 2!affine_conv/=; congr addpt.
rewrite IH -barycenter_map scalept_barycenter //.
rewrite /barycenter 2!big_map [in RHS]big_map.
apply eq_bigr => i _.
rewrite scaleptA // fdist_delE fdistD1E /=.
rewrite (mulrC (fun_of_fin (FDist.f d) (lift ord0 i))).
rewrite RmultE mulrA mulrV ?mul1r //.
move: (Hd); apply contra; rewrite R0E R1E => /eqP Hd'.
by rewrite -onem0 -Hd' onemK.
Qed.

End with_affine_projection.

Lemma S1_Convn n (g : 'I_n -> T) d :
  S1 (<|>_d g) = \ssum_(i < n) scalept (d i) (S1 (g i)).
Proof. by rewrite (S1_Convn_proj [the {affine _ ->_} of idfun]). Qed.

Lemma fdist_convn_add n m p (g : 'I_(n + m) -> T) (d : {fdist 'I_n})
    (e : {fdist 'I_m}) :
  <|>_(fdist_add d e p) g =
  <|>_d (g \o @lshift n m) <| p |> <|>_e (g \o @rshift n m).
Proof.
apply: S1_inj; rewrite affine_conv/= !S1_Convn convptE big_split_ord/=.
do 2 rewrite [in RHS]big_morph_scalept ?scalept0//.
congr addpt; apply eq_bigr => i _;
  rewrite  (scaleptA _ _ (S1 _)) //;
  by rewrite fdist_addE (split_lshift, split_rshift).
Qed.

End convex_space_prop1.

Section convex_space_prop2.
Variables T U : convType.
Implicit Types a b : T.

Lemma Convn_comp (f : {affine T -> U}) n (g : 'I_n -> T) (d : {fdist 'I_n}) :
  f (<|>_d g) = <|>_d (f \o g).
Proof. by apply S1_inj; rewrite S1_Convn S1_Convn_proj. Qed.

Lemma eq_Convn n (g1 g2 : 'I_n -> T) (d1 d2 : {fdist 'I_n}) :
  g1 =1 g2 -> d1 =1 d2 -> <|>_d1 g1 = <|>_d2 g2.
Proof.
move=> Hg Hd; apply S1_inj; rewrite !S1_Convn.
by apply congr_big => // i _; rewrite Hg Hd.
Qed.

Lemma eq_dep_Convn n (g : 'I_n -> T) (d : {fdist 'I_n})
      n0 (g0 : 'I_n0 -> T) (d0 : {fdist 'I_n0}) (Hn : n = n0)
      (Hg : eq_rect n (fun m => 'I_m -> T) g n0 Hn = g0)
      (Hd : eq_rect n (fun m => {fdist 'I_m}) d n0 Hn = d0) :
  <|>_d g = <|>_d0 g0.
Proof.
refine (match Hd with erefl => _ end).
refine (match Hg with erefl => _ end).
refine (match Hn with erefl => _ end).
reflexivity.
Qed.

Lemma Convn_proj n (g : 'I_n -> T) (d : {fdist 'I_n}) i :
  d i = R1 -> <|>_d g = g i.
Proof.
move=> Hd; apply: S1_inj.
rewrite S1_Convn (bigD1 i)//=.
rewrite big1; first by rewrite addpt0 Hd scale1pt.
move=> j Hj.
by move/eqP/fdist1P: Hd => -> //; rewrite scale0pt.
Qed.

Lemma Convn_fdist1 (n : nat) (j : 'I_n) (g : 'I_n -> T) :
  <|>_(fdist1 j) g = g j.
Proof. by apply Convn_proj; rewrite fdist1xx. Qed.

Lemma ConvnI1E
  (g : 'I_1 -> T) (e : {fdist 'I_1}) : <|>_ e g = g ord0.
Proof.
rewrite /=; case: Bool.bool_dec => // /Bool.eq_true_not_negb H.
exfalso; move/eqP: H; apply.
by apply/eqP; rewrite fdist1E1 (fdist1I1 e).
Qed.

Lemma ConvnI1_eq_rect n (g : 'I_n -> T) (d : {fdist 'I_n}) (Hn1 : n = 1) :
  <|>_d g = eq_rect n (fun n => 'I_n -> T) g 1 Hn1 ord0.
Proof.
set d' := eq_rect n (fun n0 => {fdist 'I_n0}) d 1 Hn1.
set g' := eq_rect n (fun n0 => 'I_n0 -> T) g 1 Hn1.
suff -> : <|>_d g = <|>_d' g' by rewrite ConvnI1E.
by eapply eq_dep_Convn.
Qed.

Lemma ConvnI1_eq n (g : 'I_n -> T) (d : {fdist 'I_n})
      (n1 : n = 1) (i : 'I_n) : <|>_d g = g i.
Proof.
rewrite ConvnI1_eq_rect.
have -> /= : eq_rect n (fun n0 : nat => 'I_n0 -> T) g 1 n1 =
    g \o eq_rect 1 (fun n0 : nat => 'I_1 -> 'I_n0) idfun n (esym n1)
  by subst n.
have /(_ i) I_n_contr : forall a b : 'I_n, a = b
    by rewrite n1 => a b; rewrite (ord1 a) (ord1 b).
by rewrite -(I_n_contr (eq_rect 1 (fun n => 'I_1 -> 'I_n) idfun n (esym n1) ord0)).
Qed.
Global Arguments ConvnI1_eq [n g d n1].

Lemma ConvnIE n (g : 'I_n.+1 -> T) (d : {fdist 'I_n.+1}) (i1 : d ord0 != 1%coqR) :
  <|>_d g = g ord0 <| probfdist d ord0 |>
            <|>_(fdist_del i1) (fun x => g (fdist_del_idx ord0 x)).
Proof.
rewrite /=; case: Bool.bool_dec => /= [|/Bool.eq_true_not_negb] H.
exfalso; by rewrite (eqP H) eqxx in i1.
by rewrite (eq_irrelevance H i1).
Qed.

Lemma ConvnI2E' (g : 'I_2 -> T) (d : {fdist 'I_2}) :
  <|>_d g = g ord0 <| probfdist d ord0 |> g (lift ord0 ord0).
Proof.
have [/eqP|i1] := eqVneq (d ord0) 1%coqR.
  rewrite fdist1E1 => /eqP ->; rewrite Convn_fdist1.
  rewrite (_ : probfdist _ _ = 1%:pr) ?conv1 //.
  by apply val_inj; rewrite /= fdist1xx.
rewrite ConvnIE; congr (_ <| _ |> _).
by rewrite ConvnI1E /fdist_del_idx ltnn.
Qed.

Lemma ConvnI2E (g : 'I_2 -> T) (d : {fdist 'I_2}) :
  convn d g = (g ord0) <| probfdist d ord0 |> (g (lift ord0 ord0)).
Proof.
have [/eqP|i1] := eqVneq (d ord0) 1%coqR.
  rewrite fdist1E1 convnE => /eqP ->; rewrite Convn_fdist1.
  rewrite (_ : probfdist _ _ = 1%:pr) ?conv1 //.
  by apply val_inj; rewrite /= fdist1xx.
rewrite convnE ConvnIE; congr (conv _ _ _).
by rewrite ConvnI1E /fdist_del_idx ltnn.
Qed.
End convex_space_prop2.

HB.factory Record isConvexSpace T of Choice T := {
  conv : {prob R} -> T -> T -> T ;
  conv1 : forall a b, conv 1%:pr a b = a ;
  convmm : forall p a, conv p a a = a ;
  convC : forall p a b, conv p a b = conv (onem (Prob.p p))%:pr b a ;
  convA : forall (p q : {prob R}) (a b c : T),
      conv p a (conv q b c) = conv [s_of p, q] (conv [r_of p, q] a b) c }.

HB.builders Context T of isConvexSpace T.

Definition convn := Convn conv.

Let conv0 a b : conv 0%:pr a b = b.
Proof.
by rewrite convC /= (_ : _ %:pr = 1%:pr) ?conv1 //; apply/val_inj/onem0.
Qed.

Let Convn_fdist1 (n : nat) (j : 'I_n) (g : 'I_n -> T) :
  convn (fdist1 j) g = g j.
Proof.
elim: n j g => [[] [] //|n IH j g /=].
rewrite /convn {1}/Convn.
case: Bool.bool_dec => [/eqP|/Bool.eq_true_not_negb b01].
  rewrite fdist1E; case j0 : (_ == _) => /=.
    by move=> _; rewrite (eqP j0).
  by move/eqP; rewrite eq_sym R1E oner_eq0.
rewrite (_ : probfdist _ _ = 0%:pr) ?conv0; last first.
  apply val_inj => /=; move: b01; rewrite !fdist1E => j0.
  by case j0' : (_ == _) => //; rewrite j0' eqxx in j0.
have j0 : ord0 != j by apply: contra b01 => /eqP <-; rewrite fdist1xx.
have j0' : 0 < j by rewrite lt0n; apply: contra j0 => /eqP j0; apply/eqP/val_inj.
move=> [:H]; have @j' : 'I_n.
  by apply: (@Ordinal _ j.-1 _); abstract: H; rewrite prednK // -ltnS.
rewrite (_ : fdist_del b01 = fdist1 j'); last first.
  apply/fdist_ext => /= k.
  rewrite fdist_delE fdistD1E /= !fdist1E /= (negbTE j0) subr0 divr1.
  congr (GRing.natmul _ (nat_of_bool _)).
  move R : (k == _) => [|].
  - apply/eqP/val_inj; rewrite /= /bump leq0n add1n.
    by move/eqP : R => -> /=; rewrite prednK // lt0n.
  - apply: contraFF R => /eqP.
    move/(congr1 val) => /=; rewrite /bump leq0n add1n => kj.
    by apply/eqP/val_inj; rewrite /= -kj.
rewrite -/Convn.
rewrite -/convn.
rewrite IH /fdist_del_idx ltn0; congr g.
by apply val_inj; rewrite /= /bump leq0n add1n prednK // lt0n.
Qed.

Let ConvnIE n (g : 'I_n.+1 -> T) (d : {fdist 'I_n.+1}) (i1 : d ord0 != 1%coqR) :
  convn d g = conv (probfdist d ord0) (g ord0)
            (convn (fdist_del i1) (fun x => g (fdist_del_idx ord0 x))).
Proof.
rewrite /convn /=; case: Bool.bool_dec => /= [|/Bool.eq_true_not_negb] H.
exfalso; by rewrite (eqP H) eqxx in i1.
by rewrite (eq_irrelevance H i1).
Qed.

Let ConvnI1E (g : 'I_1 -> T) (e : {fdist 'I_1}) : convn e g = g ord0.
Proof.
rewrite /convn /=; case: Bool.bool_dec => // /Bool.eq_true_not_negb H.
exfalso; move/eqP: H; apply.
by apply/eqP; rewrite fdist1E1 (fdist1I1 e).
Qed.

Let ConvnI2E : forall (g : 'I_2 -> T) (d : {fdist 'I_2}),
  convn d g = conv (probfdist d ord0) (g ord0) (g (lift ord0 ord0)).
Proof.
move=> g d.
have [/eqP|i1] := eqVneq (d ord0) 1%coqR.
  rewrite fdist1E1 => /eqP ->.
  rewrite Convn_fdist1.
  rewrite (_ : probfdist _ _ = 1%:pr) ?conv1 //.
  by apply val_inj; rewrite /= fdist1xx.
rewrite ConvnIE; congr conv.
by rewrite ConvnI1E /fdist_del_idx ltnn.
Qed.

HB.instance Definition _ := @isConvexSpace0.Build T
  conv convn (fun _ _ _ => erefl) conv1 convmm convC convA.

HB.end.

Section convex_space_prop3.
Variables T U : convType.
Implicit Types a b : T.

(* ref: M.H.Stone, postulates for the barycentric calculus, lemma 2 *)
Lemma Convn_perm (n : nat) (d : {fdist 'I_n}) (g : 'I_n -> T) (s : 'S_n) :
  <|>_d g = <|>_(fdistI_perm d s) (g \o s).
Proof.
apply S1_inj; rewrite !S1_Convn (ssum_perm _ s).
by apply eq_bigr => i _; rewrite fdistI_permE.
Qed.

(* ref: M.H.Stone, postulates for the barycentric calculus, lemma 4 *)
Theorem Convn_fdist_convn (n m : nat) (d : {fdist 'I_n})
        (e : 'I_n -> {fdist 'I_m}) (x : 'I_m -> T) :
  <|>_d (fun i => <|>_(e i) x) = <|>_(fdist_convn d e) x.
Proof.
apply S1_inj; rewrite !S1_Convn -[in RHS]big_enum -ssum_fdist_convn.
by apply eq_bigr => i _; rewrite big_enum S1_Convn.
Qed.

Lemma Convn_cst (a : T) (n : nat) (d : {fdist 'I_n}) : <|>_d (fun=> a) = a.
Proof.
elim: n d; first by move=> d; move/fdistI0_False: (d).
move=> n IHn d.
have [|] := eqVneq (d ord0) 1%coqR; first by move/(Convn_proj (fun=> a)).
by move=> d0n0; rewrite ConvnIE IHn convmm.
Qed.

Lemma Convn_idem (a : T) (n : nat) (d : {fdist 'I_n}) (g : 'I_n -> T) :
  (forall i : 'I_n, (d i != 0)%coqR -> g i = a) -> <|>_d g = a.
Proof.
move=> Hg; apply: S1_inj.
rewrite S1_Convn (eq_bigr (fun i => scalept (d i) (S1 a))).
  by rewrite -S1_Convn Convn_cst.
move=> /= i _.
by have [-> //|/Hg ->//] := eqVneq (d i) 0%coqR; rewrite !scale0pt.
Qed.

Lemma Convn_weak n m (u : 'I_m -> 'I_n) (d : {fdist 'I_m}) (g : 'I_n -> T) :
  <|>_d (g \o u) = <|>_(fdistmap u d) g.
Proof.
apply S1_inj.
rewrite !S1_Convn (partition_big u (fun _=> true)) //=.
apply eq_bigr => i _.
rewrite fdistmapE /=.
have HF (a : 'I_m) : (0 <= d a)%coqR. by [].
rewrite (@scalept_sum _ _ _ (mkNNFun HF)) /=.
by apply eq_bigr => a /eqP ->.
Qed.

Lemma ConvnDr n (p : {prob R}) (x : T) (g : 'I_n -> T) (d : {fdist 'I_n}) :
  x <|p|> <|>_d g = <|>_d (fun i => x <|p|> g i).
Proof.
elim: n p x g d => [? ? ? d|n IHn p x g d]; first by move/fdistI0_False: (d).
have [d01|d0n1] := eqVneq (d ord0) 1%coqR.
  by rewrite (Convn_proj g d01) (Convn_proj (fun i => x <|p|> g i) d01).
by rewrite !ConvnIE !IHn; congr (<|>_ _ _); apply funext=> i; rewrite convDr.
Qed.

Lemma ConvnDl n (p : {prob R}) (x : T) (g : 'I_n -> T) (d : {fdist 'I_n}) :
  <|>_d g <|p|> x = <|>_d (fun i => g i <|p|> x).
Proof. by rewrite convC ConvnDr; apply eq_Convn =>// i; rewrite -convC. Qed.

Local Open Scope ring_scope.

Lemma ConvnDlr n m (p : {prob R}) (f : 'I_n -> T) (d : {fdist 'I_n})
                              (g : 'I_m -> T) (e : {fdist 'I_m}) :
  <|>_d f <|p|> <|>_e g =
  <|>_(fdist_add d e p)
      (fun i => match fintype.split i with inl i => f i | inr i => g i end).
Proof.
apply: S1_inj; rewrite affine_conv/= 3!S1_Convn convptE.
do 2 rewrite big_morph_scalept ?scalept0//.
rewrite big_split_ord/=.
congr addpt; apply: congr_big => //= i _; rewrite scaleptA// fdist_addE.
- case: fintype.splitP => [j/= /ord_inj ->//|k/= ink].
  by have := ltn_ord i; rewrite ink -ltn_subRL subnn.
- case: fintype.splitP => [j/= nij|k/=/eqP/[!eqn_add2l]/eqP/ord_inj ->//].
  by have := ltn_ord j; by rewrite -nij -ltn_subRL subnn.
Qed.

End convex_space_prop3.

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
move=> x xX; rewrite /hull; exists 1, (fun=> x), (fdist1 ord0).
split => [d [i _ <-] //|]; by rewrite ConvnI1E.
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
  X a0 -> Y a1 -> hull (X `|` Y) (a0 <| p |> a1).
Proof.
move=> a0X a1y.
exists 2, (fun i => if i == ord0 then a0 else a1), (fdistI2 p); split => /=.
  by move=> _ [i _ <-] /=; case: ifPn => _; [left | right].
case: Bool.bool_dec => [/eqP|/Bool.eq_true_not_negb H].
  rewrite fdistI2E eqxx /= => p1.
  by rewrite (_ : p = 1%:pr) ?conv1 //; exact/val_inj.
congr (_ <| _ |> _); first by apply val_inj; rewrite /= fdistI2E eqxx.
case: Bool.bool_dec => // H'.
exfalso.
move: H'; rewrite fdist_delE fdistD1E (eq_sym (lift _ _)) (negbTE (neq_lift _ _)).
rewrite fdistI2E (eq_sym (lift _ _)) (negbTE (neq_lift _ _)) fdistI2E.
rewrite eqxx mulrV ?eqxx //.
by move: H; rewrite fdistI2E eqxx onem_neq0.
Qed.

Lemma hull_monotone X Y : X `<=` Y -> hull X `<=` hull Y.
Proof.
move=> H a [n [g [d [H0 H1]]]]; exists n, g, d; split => //.
by eapply subset_trans; first exact: H0.
Qed.

End hull_prop.

Module ErealConvex.
Section ereal_convex.
Local Open Scope ereal_scope.

Let conv_ereal (p : {prob R}) x y := (Prob.p p : R)%:E * x + (Prob.p p).~%:E * y.

Let conv_ereal_conv1 a b : conv_ereal 1%:pr a b = a.
Proof. by rewrite /conv_ereal probpK onem1 /= mul1e mul0e adde0. Qed.

Let conv_ereal_convmm p a : conv_ereal p a a = a.
Proof.
rewrite /conv_ereal; case/boolP : (a \is a fin_num) => [?|].
  by rewrite -muleDl// -EFinD probKC mul1e.
rewrite fin_numE negb_and !negbK => /predU1P[-> | /eqP->].
- rewrite -ge0_muleDl.
  + by rewrite -EFinD probKC mul1e.
  + by rewrite lee_fin; apply/prob_ge0.
  + by rewrite lee_fin; apply/prob_ge0.
- rewrite -ge0_muleDl.
  + by rewrite -EFinD probKC mul1e.
  + by rewrite lee_fin; apply/prob_ge0.
  + by rewrite lee_fin; apply/prob_ge0.
Qed.

Let conv_ereal_convC p a b : conv_ereal p a b = conv_ereal ((Prob.p p).~)%:pr b a.
Proof. by rewrite [in RHS]/conv_ereal onemK addeC. Qed.

Lemma oprob_sg1 (p : {oprob R}) : Num.sg (oprob_to_real p) = 1%mcR.
Proof.
have /andP[] := OProb.O1 p; move=> /[swap] _. rewrite -sgr_cp0.
by move/eqP.
Qed.

Let conv_ereal_convA (p q: {prob R}) a b c :
  conv_ereal p a (conv_ereal q b c) =
  conv_ereal [s_of p, q] (conv_ereal [r_of p, q] a b) c.
Proof.
rewrite /conv_ereal.
apply (prob_trichotomy' p);
  [ by rewrite s_of_0q r_of_0q !mul0e !add0e !onem0 !mul1e
  | by rewrite s_of_1q r_of_1q !mul1e !onem1 !mul0e !adde0
  | rewrite {p}=> p].
apply (prob_trichotomy' q);
  [ by rewrite s_of_p0 Reals_ext.r_of_p0_oprob onem1 onem0 mul0e !mul1e add0e adde0
  | by rewrite s_of_p1 r_of_p1 onem1 !mul1e mul0e !adde0
  | rewrite {q}=> q].
have sgp := oprob_sg1 p.
have sgq := oprob_sg1 q.
have sgonemp := oprob_sg1 (Prob.p (OProb.p p)).~%:opr.
have sgonemq := oprob_sg1 (Prob.p (OProb.p q)).~%:opr.
have sgrpq := oprob_sg1 [r_of OProb.p p, OProb.p q]%:opr.
have sgspq := oprob_sg1 [s_of OProb.p p, OProb.p q]%:opr.
have sgonemrpq := oprob_sg1 (Prob.p [r_of OProb.p p, OProb.p q]).~%:opr.
have sgonemspq := oprob_sg1 (Prob.p [s_of OProb.p p, OProb.p q]).~%:opr.
Ltac mulr_infty X := do ! (rewrite mulr_infty X mul1e).
set sg := (sgp,sgq,sgonemp,sgonemq,sgrpq,sgspq,sgonemrpq,sgonemspq).
case: a=> [a | | ]; case: b=> [b | | ]; case: c=> [c | | ];
  try by mulr_infty sg.
rewrite muleDr // addeA.
congr (_ + _)%E; last by rewrite s_of_pqE onemK EFinM muleA.
rewrite muleDr //.
congr (_ + _)%E.
  by rewrite (p_is_rs (OProb.p p) (OProb.p q)) mulrC EFinM muleA.
rewrite muleA -!EFinM.
rewrite (pq_is_rs (OProb.p p) (OProb.p q)).
rewrite mulrA.
by rewrite (mulrC (Prob.p [r_of OProb.p p, OProb.p q]).~).
Qed.

#[export] HB.instance Definition _ := @isConvexSpace.Build (\bar R) conv_ereal conv_ereal_conv1 conv_ereal_convmm conv_ereal_convC conv_ereal_convA.

Lemma conv_erealE p (a b : \bar R) : a <| p |> b = conv_ereal p a b.
Proof. by []. Qed.

End ereal_convex.
End ErealConvex.
HB.export ErealConvex.

(* Convex sets in a convex space *)

Section is_convex_set.
Local Open Scope classical_set_scope.
Variable T : convType.

Definition is_convex_set (D : set T) : bool :=
  `[<forall x y t, D x -> D y -> D (x <| t |> y)>].

Lemma is_convex_set0 : is_convex_set set0. Proof. exact/asboolP. Qed.

Lemma is_convex_set1 a : is_convex_set [set a].
Proof. by apply/asboolP => x y p /= => -> ->; rewrite convmm. Qed.

Lemma is_convex_setT : is_convex_set setT.
Proof. exact/asboolP. Qed.

Definition is_convex_set_n (X : set T) : bool :=
  `[< forall n (g : 'I_n -> T) (d : {fdist 'I_n}),
    g @` setT `<=` X -> X (<|>_d g) >].

Lemma is_convex_setP (X : set T) : is_convex_set X = is_convex_set_n X.
Proof.
apply/idP/idP => H; apply/asboolP.
  elim => [g d|n IH g d]; first by move: (fdistI0_False d).
  case: n => [|n] in IH g d * => gX.
    rewrite {IH} (@Convn_proj _ _ _ _ ord0) //.
      exact/gX/classical_sets.imageP.
    by apply/eqP; rewrite fdist1E1 (fdist1I1 d).
  have [d01|d01] := eqVneq (d ord0) 1%coqR.
    suff -> : <|>_d g = g ord0 by apply gX; exists ord0.
    by rewrite (@Convn_proj _ _ _ _ ord0).
  set D : {fdist 'I_n.+1} := fdist_del d01.
  pose G (i : 'I_n.+1) : T := g (fdist_del_idx (@ord0 _) i).
  have /(IH _ D) {}IH : range G `<=` X.
    move=> x -[i _ <-{x}]; rewrite /G /fdist_del_idx ltn0; apply gX.
    by exists (lift ord0 i).
  rewrite ConvnIE //.
  by move/asboolP : H; apply => //; exact/gX/classical_sets.imageP.
move=> x y p xX yX.
have [->|p1] := eqVneq p 1%:pr; first by rewrite conv1.
set g : 'I_2 -> T := fun i => if i == ord0 then x else y.
have gX : range g `<=` X by move=> a -[i _ <-]; rewrite /g; case: ifPn.
move/asboolP : H => /(_ _ g (fdistI2 p) gX).
rewrite ConvnIE; first by rewrite fdistI2E eqxx.
move=> p1'.
rewrite {1}/g eqxx (_ : probfdist _ _ = p); last first.
  by apply val_inj; rewrite /= fdistI2E eqxx.
by rewrite (_ : <|>_ _ _ = y) // (_ : (fun _ => _) = (fun=> y)) ?ConvnI1E.
Qed.

Lemma is_convex_segmentP (X : set T) :
  reflect (forall x y, X x -> X y -> (segment x y `<=` X)%classic)
          (is_convex_set X).
Proof.
apply: (iffP idP) => conv.
  by move=> x y xX yX z [p _ <-]; move/asboolP : conv; apply.
by apply/asboolP => x y p xX yX; apply: (conv _ _ xX yX); exists p.
Qed.

Lemma segment_is_convex (x y : T) : is_convex_set (segment x y).
Proof.
apply/asboolP => u v p [q _ <-] [r _ <-].
have [q' [p' [r' ->]]] := convACA' x y x y q p r.
by rewrite convmm convmm; exists p'.
Qed.

End is_convex_set.

(* TODO:
Record ConvexSet (A : convType) := { convset_set :> set A ; _ : is_convex_set convset_set }.
HB.instance Definition _ A := [isSub of ConvexSet A for @convset_set A ].
*)
HB.mixin Record isConvexSet (A : convType) (X : set A) := { is_convex : is_convex_set X }.
HB.structure Definition ConvexSet A := { X of isConvexSet A X }.
Notation "{ 'convex_set' T }" := (ConvexSet.type T) : convex_scope.

Canonical cset_predType A := Eval hnf in
  PredType (fun t : {convex_set A} => (fun x => x \in ConvexSet.sort t)).

(*
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
*)

HB.instance Definition _ A := @gen_eqMixin {convex_set A}.

Section CSet_interface.
Variable (A : convType).
Implicit Types X Y : {convex_set A}.
Lemma convex_setP X : is_convex_set X.
Proof. by case: X => X [[]] /=. Qed.
Lemma cset_ext X Y : X = Y :> set _ -> X = Y.
Proof.
move: X Y => -[X [[HX]]] [Y [[HY]]] /= ?; subst Y.
do! [f_equal]; exact/Prop_irrelevance.
Qed.
End CSet_interface.

Section CSet_prop.
Local Open Scope classical_set_scope.
Variable A : convType.
Implicit Types X Y : {convex_set A}.
Implicit Types a : A.
Implicit Types x y : scaled A.

Lemma mem_convex_set a1 a2 p X : a1 \in X -> a2 \in X -> a1 <|p|> a2 \in X.
Proof.
have /asboolP C := @is_convex A X.
by rewrite !inE; apply: C.
Qed.

HB.instance Definition _ := isConvexSet.Build A set0 (is_convex_set0 A).

Lemma cset0P X : (X == set0) = (X == set0 :> set _).
Proof.
case: X => x [Hx] /=; apply/eqP/eqP => [-[] //| ?]; subst x; exact: cset_ext.
Qed.

Lemma cset0PN X : X != set0 <-> X !=set0.
Proof.
rewrite cset0P; case: X => //= x Hx; split; last first.
  case=> a xa; apply/eqP => x0; move: xa; by rewrite x0.
by case/set0P => /= d dx; exists d.
Qed.

HB.instance Definition _ a := isConvexSet.Build A [set a] (is_convex_set1 a).

Lemma cset1_neq0 a : [set a] != set0 :> {convex_set A}.
Proof. by apply/cset0PN; exists a. Qed.

HB.instance Definition _ x y := isConvexSet.Build _ (segment x y) (segment_is_convex x y).

End CSet_prop.

(* Lemmas on hull and convex set *)

Section hull_is_convex.
Variable A : convType.

Lemma hull_sub_convex (X : set A)(Y : {convex_set A}) :
  (X `<=` Y -> hull X `<=` Y)%classic.
Proof.
move=> XY x [n [g [d [gX ->]]]].
have := convex_setP Y; rewrite is_convex_setP /is_convex_set_n.
by move=> /asboolP/(_ _ g d (subset_trans gX XY)).
Qed.

Lemma hull_cset (X : {convex_set A}) : hull X = X.
Proof. by apply/seteqP; split; [exact/hull_sub_convex|exact/subset_hull]. Qed.

Lemma hull_is_convex (Z : set A) : is_convex_set (hull Z).
Proof.
apply/asboolP => x y p [n [g [d [gX ->{x}]]]] [m [h [e [hX ->{y}]]]].
exists (n + m).
exists [ffun i => match fintype.split i with inl a => g a | inr a => h a end].
exists (fdist_add d e p).
split.
  move=> a -[i _]; rewrite ffunE.
  by case: splitP => j _ <-; [apply gX; exists j | apply hX; exists j].
by rewrite fdist_convn_add; congr (_ <| _ |> _); apply eq_Convn => i //=;
  rewrite ffunE (split_lshift,split_rshift).
Qed.

HB.instance Definition _ (Z : set A) := isConvexSet.Build _ (hull Z) (hull_is_convex Z).

Lemma segment_hull (x y : A) : segment x y = hull [set x; y].
Proof.
rewrite eqEsubset; split.
  by have := hull_is_convex [set x; y] => /is_convex_segmentP/(_ x y); apply;
    apply subset_hull; [left | right].
(* BUG in HB: HB.pack only accepts types as subjects
   pose h : {convex_set A} := HB.pack _ (isConvexSet.Build _ _ (segment_is_convex x y)).*)
pose h : {convex_set A} := @ConvexSet.Pack _ _ (@ConvexSet.Class _ _ (isConvexSet.Build _ _ (segment_is_convex x y))).
by have := @hull_sub_convex [set x; y] h; apply => z -[] ->;
  [exact: segmentL|exact: segmentR].
Qed.

End hull_is_convex.

Section hull_convex_set.
Local Open Scope classical_set_scope.
Variable A : convType.
Implicit Types X Y Z : set A.

Lemma is_convex_hullE X : is_convex_set X = (hull X == X).
Proof.
apply/idP/idP => [conv|/eqP <-]; last exact: hull_is_convex.
(* BUG in HB *)
pose X' : {convex_set A} := @ConvexSet.Pack _ _ (@ConvexSet.Class _ _ (isConvexSet.Build _ _ conv)).
exact/eqP/(hull_cset X').
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
Local Open Scope scaled_scope.
Variable T : convType.
Implicit Types Z : set T.

Definition scaled_set Z := [set x | if x is p *: a then Z a else True].

Lemma scalept_scaled_set Z r x :
  x \in scaled_set Z -> scalept r x \in scaled_set Z.
Proof.
rewrite /scalept/=.
by case: Rlt_dec => //= Hr; [case: x | rewrite !in_setE].
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
  have [-> _ [b bY]|a0 aX [b]] := eqVneq a Zero.
    rewrite add0pt => S1zy.
    exists dx; rewrite ?in_setE //; exists z; last by exists 0%:pr; rewrite conv0.
    by rewrite -(point_S1 z); apply: scaled_set_extract; rewrite S1zy.
  have [-> _|b0 bY] := eqVneq b Zero.
    rewrite addpt0 => S1zx.
    exists z; last by exists dy; rewrite ?in_setE //; exists 1%:pr; rewrite conv1.
    by rewrite -(point_S1 z); apply: scaled_set_extract; rewrite S1zx.
  rewrite addptE => -[_ zxy].
  exists [point of a0]; first exact: (@scaled_set_extract _ a).
  exists [point of b0]; first exact: scaled_set_extract.
  by eexists; rewrite zxy.
move/(congr1 (@S1 T)): zg; rewrite S1_Convn.
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

(* TODO: move *)
Section split_prod.

Lemma unsplit_prodp (m n : nat) (i : 'I_m) (j : 'I_n) : (i * n + j < m * n)%nat.
Proof.
by rewrite -ltn_subRL -mulnBl (leq_trans (ltn_ord j))// leq_pmull// subn_gt0.
Qed.

Definition unsplit_prod (m n : nat) (i : 'I_m * 'I_n) : 'I_(m * n) :=
  let (i, j) := i in Ordinal (unsplit_prodp i j).

Definition split_prodpl (m n : nat) (i : 'I_(m * n)): (i %/ n < m)%nat.
Proof. by move: n i => [|n i]; [rewrite muln0 => -[]|rewrite ltn_divLR]. Qed.

Definition split_prodpr (m n : nat) (i : 'I_(m * n)): (i %% n < n)%nat.
Proof. by move: n i => [|n i]; [rewrite muln0 => -[]|rewrite ltn_pmod]. Qed.

Definition split_prod (m n : nat) (i : 'I_(m * n)): 'I_m * 'I_n :=
  (Ordinal (split_prodpl i), Ordinal (split_prodpr i)).

(* TODO: find a suitable name *)
Lemma big_prod_ord [R' : Type] [idx : R'] (op : Monoid.com_law idx) [m n : nat]
    (P : pred 'I_(m * n)) (F : 'I_(m * n) -> R') :
  \big[op/idx]_(i | P i) F i =
  \big[op/idx]_i \big[op/idx]_(j | P (unsplit_prod (i, j))) F (unsplit_prod (i, j)).
Proof.
elim: m =>[|m IHm] in P F *; first by rewrite 2!big_ord0.
rewrite big_ord_recl big_split_ord; congr (op _ _).
- apply congr_big => //=.
    by move=> i/=; congr P; exact: val_inj.
  by move=> i/= _; congr F; exact: val_inj.
- rewrite IHm; apply eq_bigr => i _.
  have e j : rshift n (unsplit_prod (i, j)) = Ordinal (unsplit_prodp (lift ord0 i) j).
    by apply val_inj => /=; rewrite /bump leq0n addnA.
  by apply: eq_big => // j; rewrite e.
Qed.

Lemma split_prodK n m : cancel (@split_prod n m) (@unsplit_prod n m).
Proof. by move=> i; apply val_inj => /=; rewrite -divn_eq. Qed.

Lemma unsplit_prodK n m : cancel (@unsplit_prod n m) (@split_prod n m).
Proof.
move: m => [[? [[]]]//|m [i j]]; congr (_, _); apply/val_inj => /=.
- by rewrite divnMDl// divn_small// addn0.
- by rewrite modnMDl modn_small.
Qed.

End split_prod.

Module LmoduleConvex.
Section lmodR_convex_space.
Variable E : lmodType R.
Implicit Type p q : {prob R}.
Local Open Scope ring_scope.

Let avg p (a b : E) := (Prob.p p) *: a + (Prob.p p).~ *: b.

Let avg1 a b : avg 1%:pr a b = a.
Proof. by rewrite /avg /= scale1r onem1 scale0r addr0. Qed.

Let avgI p x : avg p x x = x.
Proof.
rewrite /avg -scalerDl.
have -> : (Prob.p p) + (Prob.p p).~ = Rplus (Prob.p p) (Prob.p p).~ by [].
by rewrite RplusE onemKC scale1r.
Qed.

Let avgC p x y : avg p x y = avg (Prob.p p).~%:pr y x.
Proof. by rewrite /avg onemK addrC. Qed.

Let avgA p q (d0 d1 d2 : E) :
  avg p d0 (avg q d1 d2) = avg [s_of p, q] (avg [r_of p, q] d0 d1) d2.
Proof.
rewrite /avg /onem.
set s := Prob.p [s_of p, q].
set r := Prob.p [r_of p, q].
rewrite (scalerDr s) -addrA (scalerA s) (mulrC s); congr +%R.
  by rewrite (p_is_rs p q) -/s.
rewrite scalerDr (scalerA _ _ d2).
rewrite -/(Prob.p p).~ -/(Prob.p q).~ -/r.~ -/s.~.
rewrite {2}/s (s_of_pqE p q) onemK; congr +%R.
rewrite 2!scalerA; congr (_ *: _).
have ->: (Prob.p p).~ * Prob.p q = ((Prob.p p).~ * Prob.p q)%coqR by [].
by rewrite RmultE pq_is_rs -/r -/s mulrC.
Qed.

#[non_forgetful_inheritance] HB.instance Definition _ :=
  isConvexSpace.Build E avg1 avgI avgC avgA.

Lemma avgrE p (x y : E) : x <| p |> y = avg p x y. Proof. by []. Qed.
End lmodR_convex_space.
End LmoduleConvex.

Section lmodR_convex_space_prop.
Variable E : lmodType R.
Implicit Type p q : {prob R}.
Local Open Scope ring_scope.
Import LmoduleConvex.

Lemma avgr_addD p (a b c d : E) :
  (a + b) <|p|> (c + d) = (a <|p|> c) + (b <|p|> d).
Proof.
rewrite !avgrE !scalerDr !addrA; congr +%R; rewrite -!addrA; congr +%R.
exact: addrC.
Qed.

Lemma avgr_oppD p (x y : E) : - x <| p |> - y = - (x <| p |> y).
Proof. by rewrite avgrE 2!scalerN -opprD. Qed.

Lemma avgr_scalerDr p : right_distributive *:%R (fun x y : E => x <| p |> y).
Proof.
by move=> x ? ?; rewrite 2!avgrE scalerDr !scalerA; congr +%R; congr (_ *: _);
  exact: mulrC.
Qed.

Lemma avgr_scalerDl p :
  left_distributive *:%R (fun x y : (R^o : lmodType R) => x <|p|> y).
Proof. by move=> x ? ?; rewrite avgrE scalerDl -2!scalerA. Qed.

(* Introduce morphisms to prove avgnE *)

Definition scaler x : E := if x is (p *: y)%scaled then (Rpos.v p) *: y else 0.

Lemma Scaled1rK : cancel (@S1 (_ E)) scaler.
Proof. by move=> x /=; rewrite scale1r. Qed.

Lemma scaler_addpt : {morph scaler : x y / addpt x y >-> x + y}.
Proof.
move=> [p x|] [q y|] /=; rewrite ?(add0r,addr0) //.
rewrite avgrE /divRposxxy /= RdivE' onem_div; last exact: Rpos_neq0.
rewrite -!RmultE -!RinvE' -!(mulRC (/ _)%coqR) scalerDr !scalerA !mulrA.
have ->: (p + q)%coqR * (/ (p + q))%coqR = 1 by apply mulRV; last by apply Rpos_neq0.
by rewrite !mul1r (addRC p) addrK.
Qed.

(* TODO: the name conflicts with GRing.scaler0  *)
Lemma scaler0 : scaler Zero = 0. by []. Qed.

Lemma scaler_scalept r x : (0 <= r -> scaler (scalept r x) = r *: scaler x)%coqR.
Proof.
case: x => [q y|r0]; last first.
  by rewrite scalept0// scaler0 !GRing.scaler0.
case=> r0.
  by rewrite scalept_gt0 /= scalerA.
by rewrite -r0 scale0pt scale0r.
Qed.

Definition big_scaler := big_morph scaler scaler_addpt scaler0.

Definition avgnr n (g : 'I_n -> E) (e : {fdist 'I_n}) := \sum_(i < n) e i *: g i.

Lemma avgnrE n (g : 'I_n -> E) e : <|>_e g = avgnr g e.
Proof.
rewrite -[LHS]Scaled1rK S1_Convn big_scaler.
by apply eq_bigr => i _; rewrite scaler_scalept // Scaled1rK.
Qed.

(* TODO: Lemma preim_cancel: ... *)

Lemma avgnr_add n m (f : 'I_n -> E) (d : {fdist 'I_n}) (g : 'I_m -> E)
    (e : {fdist 'I_m}) :
  <|>_d f + <|>_e g = <|>_(fdistmap (@unsplit_prod n m) (d `x e))
                           (fun i => let (i, j) := split_prod i in f i + g j).
Proof.
rewrite -[<|>_e g]scale1r !avgnrE !/avgnr big_prod_ord.
rewrite -(FDist.f1 d) scaler_suml -big_split; apply congr_big=>// i _.
transitivity (d i *: (1%coqR *: f i + \sum_(i0 < m) e i0 *: g i0)).
   by rewrite scale1r scalerDr.
rewrite R1E -(FDist.f1 e) scaler_suml -big_split scaler_sumr; apply congr_big=>// j _.
rewrite scalerDr -!scalerDr scalerA unsplit_prodK; congr (_ *: _).
rewrite fdistmapE (big_pred1 (i, j)) /= ?fdist_prodE//.
move=>[i' j'] /=; rewrite xpair_eqE inE /=.
apply/eqP/andP => /=; last by case => /eqP -> /eqP ->.
move=>/(congr1 (@split_prod n m))/=.
by rewrite (unsplit_prodK (i, j)) (unsplit_prodK (i', j')) => -[-> ->].
Qed.

End lmodR_convex_space_prop.

Section freeN_combination.
Import ssrnum vector.
Variable (R : fieldType) (E : vectType R).
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Lemma freeN_combination n (s : n.-tuple E) : ~~ free s ->
  exists k : 'I_n -> R, (\sum_i k i *: s`_i = 0) /\ exists i, k i != 0.
Proof.
rewrite freeNE => /existsP[[i ilt] /coord_span /=].
move: (ilt) s.
have ne : (n = i.+1 + (n - i.+1))%nat by rewrite subnKC.
rewrite ne => ilt' s sin.
have hk m : (m < n - i.+1 -> m < i.+1 + (n - i.+1) - i.+1)%nat.
  by move=> mni; rewrite -addnBAC// subnn add0n.
pose k (x : 'I_(i.+1 + (n - i.+1))) :=
  match fintype.split x with
  | inl (@Ordinal _ m _) => if m == i then 1 else 0
  | inr (@Ordinal _ m i0) => - coord (drop_tuple i.+1 s) (Ordinal (hk m i0)) s`_i
  end.
exists k; split; last first.
  exists (Ordinal ilt'); rewrite /k; case: splitP.
    by case=> j ji/= <-; rewrite eqxx; exact/oner_neq0.
  by case=> j jni/= /eqP; rewrite lt_eqF// ltEnat/= addSn ltnS leq_addr.
rewrite big_split_ord big_ord_recr/= big1 ?add0r; last first.
  case=> j ji _; rewrite /k; case: splitP.
    by case=> m mi /= jm; rewrite -jm lt_eqF ?ltEnat// !scale0r.
  by case=> m mni /= jim; move: ji; rewrite jim addSnnS -ltn_subRL subnn.
rewrite {1}/k /=; case: splitP => /=; last first.
  by move=> m /eqP; rewrite lt_eqF// ltEnat/= addSn ltnS leq_addr.
case=> j/= ji ij; rewrite [in j == i]ij eqxx scale1r.
apply/eqP; rewrite addrC addr_eq0 sin -sumrN; apply/eqP.
have {}ne : (i.+1 + (n - i.+1) - i.+1 = n - i.+1)%nat by rewrite -addnBAC// subnn.
rewrite (index_enum_cast_ord ne) big_map; apply congr_big=>// [[x xlt]] _.
rewrite nth_drop -scaleNr; congr (_ *: _).
rewrite /k; case: splitP.
  by case=> m + /= ixm; rewrite -ixm -ltn_subRL subnn.
case=> m/= mni /eqP; rewrite eqn_add2l => /eqP kl.
by congr (- coord _ _ _); exact/val_inj.
Qed.

End freeN_combination.

Section caratheodory.
Import ssrnum vector.
Variable E : vectType R.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Import LmoduleConvex.

(* TODO: move? *)
Import Order.TotalTheory.

Lemma caratheodory (A : set (E : lmodType R)) x : x \in hull A ->
  exists (n : nat) (g : 'I_n -> (E : lmodType R)) (d : {fdist 'I_n}),
    [/\ (n <= (dimv (@fullv R E)).+1)%nat, range g `<=` A & x = <|>_d g].
Proof.
move=> /set_mem[n [g [d [gA ->]]]].
elim: n => [|n IHn] in g d gA *; first by case: (fdistI0_False d).
have [nsgt|nsgt] := leqP n (dimv (@fullv R E)).
   by exists n.+1, g, d.
have [mu [muR muE [i mui]]] : exists mu : 'I_n.+1 -> R,
  [/\ \sum_(i < n.+1) mu i = 0, \sum_(i < n.+1) (mu i) *: g i = 0 &
     exists i, mu i != 0 ].
  rewrite {IHn}.
  have [sf|/freeN_combination[mu [musum [i mui]]]] :=
      boolP (free [tuple g (lift ord0 i) - g ord0 | i < n]).
    have : basis_of fullv [tuple g (lift ord0 i) - g ord0 | i < n].
      by rewrite basisEfree size_tuple (ltnW nsgt) andbT sf subvf.
    rewrite in_tupleE basisEdim size_map => /andP[_].
    by move=> /leq_ltn_trans => /(_ _ nsgt); rewrite size_tuple ltnn.
  exists (fun i => if i is @Ordinal _ i.+1 ilt then mu (Ordinal (ltnSE ilt)) else - \sum_i mu i); split.
  - rewrite big_ord_recl /= addrC; apply/eqP; rewrite subr_eq0; apply/eqP.
    by apply: eq_bigr => j _; congr mu; exact/val_inj.
  - rewrite big_ord_recl /= scaleNr addrC scaler_suml -sumrB -{2}musum.
    apply: eq_bigr => j _; rewrite (nth_map j) ?size_tuple//.
    rewrite scalerBr; congr (mu _ *: g _ - _); apply/val_inj => //=.
    by rewrite nth_ord_enum.
  - by exists (lift ord0 i) => /=; rewrite (_ : Ordinal _ = i)//; exact/val_inj.
wlog: mu muR muE mui / mu i > 0.
   move=> H.
   have [mui0|mui0] := ltP 0%coqR (mu i); first exact: (H mu).
   apply (H (fun i => - mu i)).
   - by rewrite sumrN muR oppr0.
   - by under eq_bigr do rewrite scaleNr; rewrite sumrN muE oppr0.
   + by rewrite oppr_eq0.
   + by rewrite oppr_gt0 lt_neqAle mui.
move=>/(@arg_minP _ _ _ i (fun i => 0 < mu i) (fun i => d i / mu i)) [im muip muim] {i mui}.
wlog: g d gA mu muR muE im muip muim / (im == ord0)%N.
   set f := fun i : nat => if i == im :> nat then 0%nat else if i == 0%nat then nat_of_ord im else i.
   have fcan : cancel f f.
     move=> m; rewrite /f; have [->|mim] := eqVneq m im.
       by rewrite eqxx; case: ifPn => // /eqP.
     have [->|m0] := eqVneq m 0%N; first by rewrite eqxx.
     by rewrite (negbTE mim) (negbTE m0).
   have flt (i : 'I_n.+1) : (f i < n.+1)%nat.
     by rewrite /f; case: ifPn => // iim; case: ifPn.
   set f' := fun i => Ordinal (flt i).
   have fcan' : cancel f' f' by move=> [j jlt]; exact/val_inj/fcan.
   have fbij : bijective f' by exists f'; move=> [j jlt]; exact/fcan'.
   move=>/(_ (fun i => g (f' i)) (fdistmap f' d)).
   have gA' : [set g (f' i) | i in [set: 'I_n.+1]] `<=` A.
     by move=>y [i _ <-]; apply gA; eexists.
   move=>/(_ gA' (fun i => mu (f' i))).
   have mu'R : \sum_(i0 < n.+1) mu (f' i0) = 0.
     rewrite (perm_big _ (perm_map_bij _ fbij)) /=; [| exact nil ].
     by rewrite big_map -[in RHS]muR; apply congr_big=>// [[j jlt]] _; congr mu; apply fcan'.
   move=>/(_ mu'R).
   have mu'E: \sum_(i0 < n.+1) mu (f' i0) *: g (f' i0) = 0.
      rewrite (perm_big _ (perm_map_bij _ fbij)) /=; [| exact nil ].
      rewrite big_map -[in RHS]muE; apply congr_big=>// j _.
      by congr (mu _ *: g _); exact/fcan'.
   move=>/(_ mu'E (f' im)).
   have muip' : 0 < mu (f' (f' im)) by rewrite fcan'.
   move=>/(_ muip').
   have muim' (j : 'I_n.+1) :
     0 < mu (f' j) ->
     fdistmap f' d (f' im) / mu (f' (f' im)) <= fdistmap f' d j / mu (f' j).
     move=> /muim.
     rewrite fcan' fdistmapE (big_pred1 im) /=; last first.
       move=> i; apply/idP/idP; rewrite !inE; last by move=> /eqP ->.
       by move=> /eqP /(bij_inj fbij) /eqP.
     rewrite fdistmapE (big_pred1 (f' j)) //.
     by move=> /= i; apply/idP/idP; rewrite !inE => /eqP;
       [move=> <-; rewrite fcan' | move=> ->; rewrite fcan'].
   move=>/(_ muim').
   have im0 : f' im == ord0 by apply/eqP/val_inj => /=; rewrite /f eqxx.
   move=>/(_ im0) [n' [g' [d' [n'le g'A e]]]].
   exists n', g', d'; split=>//; rewrite -e.
   rewrite 2!avgnrE /avgnr.
   rewrite (perm_big _ (perm_map_bij _ fbij)); [| exact nil ].
   rewrite big_map; apply congr_big=>// j _.
   rewrite fdistmapE (big_pred1 (f' j))=>// k /=.
   by rewrite unfold_in=>/=; apply/eqP/eqP=>e'; apply (bij_inj fbij); rewrite fcan'.
move=>/eqP ime; move: muip muim; rewrite {im}ime => muip muim.
have mu0 : mu ord0 != 0 by apply /eqP=>mu0; move: muip; rewrite mu0 lt0r eq_refl.
have k0mu0 : d ord0 / mu ord0 * mu ord0 = d ord0.
  by rewrite -{2}[mu ord0]divr1 mulf_div [_*1]mulrC -mulf_div divr1 mulfV // mulr1.
set ef : 'I_n -> R := finfun (fun i => d (lift ord0 i) - d ord0 / mu ord0 * mu (lift ord0 i)).
have ef0 i : (0 <= ef i).
   rewrite /ef ffunE subr_ge0.
   have [mujp|mujp] := ltP 0 (mu (lift ord0 i)).
      by rewrite -ler_pdivlMr // muim.
   rewrite (@le_trans _ _ 0)//.
   by rewrite mulr_ge0_le0//= divr_ge0// ltW.
have ef1 : (\sum_(a in 'I_n) ef a = 1).
  rewrite -[1]subr0 -[in RHS](mulr0 (d ord0 / mu ord0)) -(FDist.f1 d) -[in _ * 0]muR mulr_sumr.
  rewrite -sumrB big_ord_recl k0mu0 subrr add0r.
  by apply eq_bigr => i _; rewrite /ef ffunE.
pose e := FDist.make ef0 ef1.
have /IHn - /(_ e): [set g (lift ord0 i) | i in [set: 'I_n]] `<=` A.
  by move=>y [i _ <-]; exact/gA.
move=> -[n' [g' [d' [n'le g'A' gde]]]].
exists n', g', d'; split=> //.
rewrite -gde 2!avgnrE /avgnr big_ord_recl -k0mu0 -scalerA.
move/eqP: muE; rewrite big_ord_recl addr_eq0 => /eqP ->.
rewrite scalerN -scaleNr scaler_sumr -big_split; apply congr_big=>// i _.
by rewrite scalerA /= -scalerDl; congr (_ *: _); rewrite addrC mulNr ffunE.
Qed.

End caratheodory.

Module LinearAffine.
Section linear_affine.
Open Scope ring_scope.
Variables (E F : lmodType R) (f : {linear E -> F}).
Import LmoduleConvex.
Let linear_is_affine: affine f.
Proof. by move=>p x y; rewrite linearD 2!linearZZ. Qed.

#[non_forgetful_inheritance] HB.instance Definition _ := isAffine.Build _ _ _ linear_is_affine.

End linear_affine.
End LinearAffine.

(* TOTHINK: Should we keep this section, only define R_convType, or something else ? *)
Module RConvex.
Section R_convex_space.
Implicit Types p q : {prob R}.
Import LmoduleConvex.
Let avg p (a b : (R^o : lmodType R)) := a <| p |> b.

Let avgE p a b : avg p a b = (Prob.p p * a + (Prob.p p).~ * b)%coqR.
Proof. by []. Qed.

Let avg1 a b : avg 1%:pr a b = a. Proof. by rewrite /avg conv1. Qed.

Let avgI p x : avg p x x = x. Proof. by rewrite /avg convmm. Qed.

Let avgC p x y : avg p x y = avg (Prob.p p).~%:pr y x. Proof. by rewrite /avg convC. Qed.

Let avgA p q (d0 d1 d2 : R) :
  avg p d0 (avg q d1 d2) = avg [s_of p, q] (avg [r_of p, q] d0 d1) d2.
Proof. by rewrite /avg convA. Qed.

#[export]
(* TODO(rei): attributed needed? *)
(*#[non_forgetful_inheritance]*) HB.instance Definition _ := @isConvexSpace.Build R _ avg1 avgI avgC avgA.

Lemma avgRE p (x y : R) : x <| p |> y = (Prob.p p * x + (Prob.p p).~ * y)%coqR. Proof. by []. Qed.

Lemma avgR_oppD p x y : (- x <| p |> - y = - (x <| p |> y))%coqR.
Proof. exact: (@avgr_oppD [lmodType R of R^o]). Qed.

Lemma avgR_mulDr p : right_distributive Rmult (fun x y => x <| p |> y).
Proof. exact: (@avgr_scalerDr [lmodType R of R^o]). Qed.

Lemma avgR_mulDl p : left_distributive Rmult (fun x y => x <| p |> y).
Proof. exact: @avgr_scalerDl. Qed.

(* Introduce morphisms to prove avgnE *)

Definition scaleR x : R := if x is (p *: y)%scaled then p * y else 0.

Lemma Scaled1RK : cancel (@S1 _) scaleR.
Proof. by move=> x /=; rewrite mul1R. Qed.

Lemma scaleR_addpt : {morph scaleR : x y / addpt x y >-> (x + y)%coqR}.
Proof.
move=> [p x|] [q y|] /=; rewrite ?(add0R,addR0) //.
rewrite avgRE /avg /divRposxxy /= RdivE' onem_div /Rdiv; last exact: Rpos_neq0.
rewrite -!RmultE -!RinvE' -!(mulRC (/ _)%coqR) mulRDr !mulRA mulRV; last exact: Rpos_neq0.
by rewrite !mul1R (addRC p) addrK.
Qed.

Lemma scaleR0 : scaleR Zero = R0. by []. Qed.

Lemma scaleR_scalept r x : (0 <= r -> scaleR (scalept r x) = r * scaleR x)%coqR.
Proof.
case: x => [q y|r0]; last by rewrite scalept0// mulR0.
case=> r0. by rewrite scalept_gt0 /= mulRA.
by rewrite -r0 scale0pt mul0R.
Qed.

Definition big_scaleR := big_morph scaleR scaleR_addpt scaleR0.

Definition avgnR n (g : 'I_n -> R) (e : {fdist 'I_n}) := (\sum_(i < n) e i * g i)%coqR.

Lemma avgnRE n (g : 'I_n -> R) e : <|>_e g = avgnR g e.
Proof.
rewrite -[LHS]Scaled1RK S1_Convn big_scaleR.
by apply eq_bigr => i _; rewrite scaleR_scalept // Scaled1RK.
Qed.

End R_convex_space.
End RConvex.
HB.export RConvex.

Module FunConvexSpace.
Section fun_convex_space.
Variables (A : choiceType) (B : convType).
Definition funT := A -> B.
Local Notation T := funT.
HB.instance Definition _ := Choice.on T.
Implicit Types p q : {prob R}.
Definition avg p (x y : T) := fun a : A => (x a <| p |> y a).
Let avg1 (x y : T) : avg 1%:pr x y = x.
Proof. rewrite funeqE => a; exact/conv1. Qed.
Let avgI p (x : T) : avg p x x = x.
Proof. rewrite funeqE => a; exact/convmm. Qed.
Let avgC p (x y : T) : avg p x y = avg (Prob.p p).~%:pr y x.
Proof. rewrite funeqE => a; exact/convC. Qed.
Let avgA p q (d0 d1 d2 : T) :
  avg p d0 (avg q d1 d2) = avg [s_of p, q] (avg [r_of p, q] d0 d1) d2.
Proof. move=> *; rewrite funeqE => a; exact/convA. Qed.
#[export] HB.instance Definition _ := @isConvexSpace.Build T avg avg1 avgI avgC avgA.
End fun_convex_space.
End FunConvexSpace.
HB.export FunConvexSpace.

Module DepfunConvexSpace.
Section depfun_convex_space.
Variables (A : choiceType) (B : A -> convType).
Let T := forall x : A, B x.
Implicit Types p q : {prob R}.
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
Let avgC p (x y : T) : avg p x y = avg (Prob.p p).~%:pr y x.
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

#[export] HB.instance Definition _ := isConvexSpace.Build (forall x : A, B x) avg1 avgI avgC avgA.

End depfun_convex_space.
End DepfunConvexSpace.
HB.export DepfunConvexSpace.

Module PairConvexSpace.
Section pair_convex_space.
Variables (A B : convType).
Let T := (A * B)%type.
Implicit Types p q : {prob R}.
Let avg p (x y : T) := (x.1 <| p |> y.1, x.2 <| p |> y.2).
Let avg1 (x y : T) : avg 1%:pr x y = x.
Proof. rewrite /avg (conv1 x.1) (conv1 x.2); by case x. Qed.
Let avgI p (x : T) : avg p x x = x.
Proof. rewrite /avg (convmm _ x.1) (convmm _ x.2); by case x. Qed.
Let avgC p (x y : T) : avg p x y = avg (Prob.p p).~%:pr y x.
Proof. by congr (pair _ _); apply convC. Qed.
Let avgA p q (d0 d1 d2 : T) :
  avg p d0 (avg q d1 d2) = avg [s_of p, q] (avg [r_of p, q] d0 d1) d2.
Proof. move => *; congr (pair _ _); by apply convA. Qed.

#[export] HB.instance Definition _ :=
  isConvexSpace.Build (A * B)%type avg1 avgI avgC avgA.

End pair_convex_space.
End PairConvexSpace.
HB.export PairConvexSpace.

Section fdist_convex_space.
Variable A : finType.
Implicit Types a b c : R.-fdist A.

Let conv1 a b : (a <| 1%:pr |> b)%fdist = a.
Proof.
by apply/fdist_ext => a0; rewrite fdist_convE /= onem1 mul1r mul0r addr0.
Qed.

Let convC p a b : (a <| p |> b = b <| (Prob.p p).~%:pr |> a)%fdist.
Proof. by apply/fdist_ext => a0 /=; rewrite 2!fdist_convE onemK addrC. Qed.

Let convmm p a : (a <| p |> a)%fdist = a.
Proof.
by apply/fdist_ext => a0; rewrite fdist_convE mulrBl mul1r addrCA addrN addr0.
Qed.

Open Scope ring_scope.

Let convA p q a b c :
  (a <| p |> (b <| q |> c) = (a <| [r_of p, q] |> b) <| [s_of p, q] |> c)%fdist.
Proof.
apply/fdist_ext => a0 /=; rewrite 4!fdist_convE /=.
set r := r_of_pq p q.  set s := s_of_pq p q.
transitivity (Prob.p p * a a0 + (Prob.p p).~ * Prob.p q * b a0 + (Prob.p p).~ * (Prob.p q).~ * c a0).
  by rewrite mulrDr !mulrA !addrA.
transitivity (Prob.p r * Prob.p s * a a0 + (Prob.p r).~ * Prob.p s * b a0 + (Prob.p s).~ * c a0); last first.
  by rewrite 2!(mulrC _ (Prob.p s)) -2!mulrA -mulrDr.
rewrite -!RmultE.
congr (_ + _ + _);
  [by rewrite (p_is_rs p q) |  | by rewrite s_of_pqE onemK].
by rewrite !RmultE pq_is_rs.
Qed.

HB.instance Definition _  := isConvexSpace.Build (R.-fdist A) conv1 convmm convC convA.

End fdist_convex_space.

Section scaled_convex_lemmas_depending_on_T_convType.
Local Open Scope R_scope.
Import RConvex.
Lemma scalept_conv (T : convType) (x y : R) (s : scaled T) (p : {prob R}):
  0 <= x -> 0 <= y ->
  scalept (x <|p|> y) s = scalept x s <|p|> scalept y s.
Proof.
move=> x0 y0; rewrite scaleptDl; [|exact/mulR_ge0|exact/mulR_ge0].
by rewrite convptE !scaleptA.
Qed.

Lemma big_scalept_conv_split (T : convType) (I : Type) (r : seq I) (P : pred I)
  (F G : I -> scaled T) (p : {prob R}) :
    \ssum_(i <- r | P i) (F i <|p|> G i) =
    (\ssum_(i <- r | P i) F i) <|p|> \ssum_(i <- r | P i) G i.
Proof.
rewrite convptE big_split /=.
by do 2 rewrite [in RHS]big_morph_scalept ?scalept0//.
Qed.

Lemma scalept_addRnng (T : convType) (x : scaled T) :
  {morph (fun (r : Rnng) => scalept r x) : r s / addRnneg r s >-> addpt r s}.
Proof. by move=> -[] r /= /RleP Hr [] s /= /RleP Hs; exact: scaleptDl. Qed.

Definition big_scaleptl (T : convType) (x : scaled T) :=
  @big_morph
    (@scaled T)
    Rnng
    (fun r : Rnng => scalept r x)
    Zero
    (@addpt [the realCone of scaled T])
    Rnng0
    addRnneg
    (@scalept_addRnng T x).

Lemma big_scaleptl' (T : convType) (x : scaled T) :
  scalept R0 x = Zero ->
  forall (I : Type) (r : seq I) (P : pred I) (F : I -> R),
    (forall i : I, 0 <= F i) ->
    scalept (\sum_(i <- r | P i) F i) x = \ssum_(i <- r | P i) scalept (F i) x.
Proof.
move=> H I r P F H'.
transitivity (\ssum_(i <- r | P i) (fun r0 : Rnng => scalept r0 x) (mkRnng (H' i))); last reflexivity.
rewrite -big_scaleptl ?scalept0 //.
congr scalept.
transitivity (\sum_(i <- r | P i) mkRnng (H' i)); first reflexivity.
apply (big_ind2 (fun x y => x = (Rnng.v y))) => //.
by move=> x1 [v Hv] y1 y2 -> ->.
Qed.

End scaled_convex_lemmas_depending_on_T_convType.

Module Convn_finType.
Section def.
Local Open Scope ring_scope.

Variables (A : convType) (T : finType) (d' : R.-fdist T) (f : T -> A).
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
rewrite -(@FDist.f1 R T d') (eq_bigr (d' \o enum)); last by move=> i _; rewrite ffunE.
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
Variables (A : convType) (T : finType) (d : R.-fdist T) (f : T -> A).

Lemma S1_Convn_finType : S1 (<$>_d f) = \ssum_i scalept (d i) (S1 (f i)).
Proof.
rewrite /Convn_finType.Convn_finType S1_Convn /=.
rewrite (reindex_onto enum_rank enum_val) /=; last by move=> i _; rewrite enum_valK.
apply eq_big => /=; first by move=> i; rewrite enum_rankK eqxx.
move=> i _; rewrite /Convn_finType.d_enum ffunE.
by rewrite enum_rankK.
Qed.

End S1_Convn_finType.

Section S1_proj_Convn_finType.
Variables (A B : convType) (prj : {affine A -> B}).
Variables (T : finType) (d : R.-fdist T) (f : T -> A).

Lemma S1_proj_Convn_finType :
  S1 (prj (<$>_d f)) = \ssum_i scalept (d i) (S1 (prj (f i))).
Proof. by rewrite Convn_comp; exact: S1_Convn_finType. Qed.

End S1_proj_Convn_finType.

Check convex_isConvexSpace__to__convex_isConvexSpace0.
(*convex_isConvexSpace__to__convex_isConvexSpace0
     : forall (A : choiceType) (B : convType),
       isConvexSpace0.axioms_ (A -> B) (HB_unnamed_mixin_131 A B) (HB_unnamed_mixin_130 A B)*)

HB.mixin Record isOrdered T of Choice T := {
  leconv : T -> T -> Prop ;
  leconvR : forall a, leconv a a;
  leconv_trans : forall b a c, leconv a b -> leconv b c -> leconv a c ;
  eqconv_le : forall a b, a = b <-> leconv a b /\ leconv b a }.

#[short(type=orderedConvType)]
HB.structure Definition OrderedConvexSpace := {T of isOrdered T & ConvexSpace T}.

Arguments leconv_trans {s b a c}.

Notation "x <= y" := (leconv x y) : ordered_convex_scope.
Notation "x <= y <= z" := (leconv x y /\ leconv y z) : ordered_convex_scope.

Import RConvex.
HB.instance Definition _ :=
  isOrdered.Build R Rle_refl leR_trans eqR_le.

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

HB.instance Definition _ := isOrdered.Build (T -> U) (@lefunR T U) (@lefun_trans T U) (@eqfun_le T U).

End fun_ordered_convex_space.


Module OppositeOrderedConvexSpace.
Section def.
Variable A : orderedConvType.

CoInductive oppT := mkOpp : A -> oppT.

Lemma A_of_TK : cancel (fun t => let: mkOpp a := t in a) mkOpp.
Proof. by case. Qed.

HB.instance Definition _ := Choice.copy oppT (can_type A_of_TK).

End def.

Section leopp.
Local Open Scope ordered_convex_scope.
Variable A : orderedConvType.
Notation T := (oppT A).
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
Notation T := (oppT A).
Implicit Types p q : {prob R}.

Definition unbox (x : T)  := match x with mkOpp x' => x' end.

Definition avg p a b := mkOpp (unbox a <| p |> unbox b).

Lemma avg1 a b : avg 1%:pr a b = a.
Proof. by case a;case b=>b' a';rewrite/avg/unbox/=conv1. Qed.

Lemma avgI p x : avg p x x = x.
Proof. by case x=>x';rewrite/avg/unbox/=convmm. Qed.

Lemma avgC p x y : avg p x y = avg (Prob.p p).~%:pr y x.
Proof. by case x;case y=>y' x'; rewrite/avg/unbox/=convC. Qed.

Lemma avgA p q d0 d1 d2 :
  avg p d0 (avg q d1 d2) = avg [s_of p, q] (avg [r_of p, q] d0 d1) d2.
Proof. by case d0;case d1;case d2=>d2' d1' d0';rewrite/avg/unbox/=convA. Qed.

#[export]
HB.instance Definition _ := isConvexSpace.Build T avg1 avgI avgC avgA.

End convtype.
End OppositeOrderedConvexSpace.
HB.export OppositeOrderedConvexSpace.

Section opposite_ordered_convex_space.
Import OppositeOrderedConvexSpace.
Variable A : orderedConvType.

HB.instance Definition _ := isOrdered.Build (oppT A) (@leoppR A) (@leopp_trans A) (@eqopp_le A).

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

Lemma leoppP (a b : oppT A) : a <= b <-> unbox b <= unbox a.
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

Definition strictly_convexf_at f := forall a b (t : {prob R}),
  a <> b -> (0 < Prob.p t < 1)%coqR -> convex_function_at f a b t.

Lemma convex_function_atxx f a t : convex_function_at f a a t.
Proof. rewrite /convex_function_at !convmm; exact/leconvR. Qed.

End convex_function_def.

Definition convex_function (U : convType) (V : orderedConvType) (f : U -> V) :=
 forall a b (t : {prob R}), convex_function_at f a b t.

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

Lemma convex_function_sym (f : T -> U) a b :
  (forall t, convex_function_at f a b t) ->
  (forall t, convex_function_at f b a t).
Proof.
move=> H t; move: (H (Prob.p t).~%:pr).
by rewrite /convex_function_at /= convC -probK (convC _ (f a)) -probK.
Qed.

Lemma convex_function_comp (f : {convex T -> U}) (g : {convex U -> V}) :
  (forall a b t, f (a <|t|> b) <= f a <|t|> f b ->
                 g (f (a <|t|> b)) <= g (f a <|t|> f b)) ->
  convex_function (g \o f).
Proof.
move=> fg a b t; have := convex_functionP g (f a) (f b) t.
by move=> Hg; apply/(leconv_trans _ Hg)/fg/convex_functionP.
Qed.

Lemma convex_function_comp' (f : {convex T -> U}) (g : {convex U -> V})
    (g_monotone : forall x y, x <= y -> g x <= g y) :
  convex_function (g \o f).
Proof. by apply convex_function_comp => // *; exact: g_monotone. Qed.

End convex_function_prop'.

Section convex_in_both.
Local Open Scope ordered_convex_scope.
Variables (T U : convType) (V : orderedConvType) (f : T -> U -> V).

Definition convex_in_both := convex_function (uncurry f).

Lemma convex_in_bothP : convex_in_both <->
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
Import RConvex.

Example biconvex_is_not_convex_in_both :
  exists f : R -> R -> R, @biconvex_function R R R f /\ ~ convex_in_both f.
Proof.
exists Rmult; split.
  by split => [a b0 b1 t | b a0 a1 t];
    rewrite /convex_function_at /=; rewrite avgRE;
    [rewrite avgR_mulDr|rewrite avgR_mulDl]; apply/RleP; rewrite lexx.
move/convex_in_bothP/(_ (-1)%coqR 1%coqR 1%coqR (-1)%coqR (probinvn 1)).
rewrite /leconv /probinvn /= 3!avgRE /=.
set a := / (1 + 1)%:R.
rewrite !(mul1R,mulR1,mulRN1) -oppRD (RplusE a a.~) onemKC.
rewrite (_ : - a + a.~ = 0)%coqR; last first.
  by rewrite /a/onem addRCA -oppRD -div1R eps2 addRN.
by rewrite mul0R leR_oppr oppR0 leRNgt; exact.
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
Definition strictly_concavef_at f := forall a b (t : {prob R}),
  a <> b -> (0 < Prob.p t < 1)%coqR -> concave_function_at f a b t.
Lemma concave_function_at'P f a b t :
  concave_function_at' f a b t <-> concave_function_at f a b t.
Proof.
rewrite /concave_function_at'/concave_function_at/convex_function_at.
by rewrite conv_leoppD leoppP.
Qed.
End concave_function_def.

Definition concave_function (U : convType) (V : orderedConvType) (f : U -> V) :=
 forall a b (t : {prob R}), concave_function_at f a b t.

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

Lemma concave_function_atxx (f : T -> V) a t :
  concave_function_at f a a t.
Proof. exact: convex_function_atxx. Qed.

Section Rprop.
Implicit Types f : T -> R.

Lemma R_convex_function_atN f a b t :
  concave_function_at f a b t -> convex_function_at (fun x => - f x)%coqR a b t.
Proof. by rewrite /convex_function_at /leconv /= avgR_oppD leR_oppl oppRK. Qed.

Lemma R_concave_function_atN f a b t :
  convex_function_at f a b t -> concave_function_at (fun x => - f x)%coqR a b t.
Proof.
rewrite /concave_function_at /convex_function_at.
by rewrite /leconv/= /leopp/= avgR_oppD /leconv/= leR_oppl oppRK.
Qed.

Lemma R_convex_functionN f :
  concave_function f -> convex_function (fun x => - f x)%coqR.
Proof. by move=> H a b t; exact/R_convex_function_atN/H. Qed.

Lemma R_concave_functionN f :
  convex_function f -> concave_function (fun x => - f x)%coqR.
Proof. by move=> H a b t; exact/R_concave_function_atN/H. Qed.

Lemma RNconvex_function_at f a b t :
  concave_function_at (fun x => - f x)%coqR a b t -> convex_function_at f a b t.
Proof. by move/(R_convex_function_atN); rewrite/convex_function_at !oppRK. Qed.

Lemma RNconcave_function_at f a b t :
  convex_function_at (fun x => - f x)%coqR a b t -> concave_function_at f a b t.
Proof.
move/(R_concave_function_atN).
by rewrite/concave_function_at/convex_function_at !oppRK.
Qed.

Lemma RNconvex_function f :
  concave_function (fun x => - f x)%coqR -> convex_function f.
Proof. move=> H a b t; exact/RNconvex_function_at/H. Qed.

Lemma RNconcave_function f :
  convex_function (fun x => - f x)%coqR -> concave_function f.
Proof. move=> H a b t; exact/RNconcave_function_at/H. Qed.

End Rprop.

Section Rprop2.

Lemma R_convex_functionB f (g : T -> R) :
  convex_function f -> concave_function g ->
  convex_function (fun x => f x - g x)%coqR.
Proof.
move=> Hf Hg p q t.
rewrite /convex_function_at /= avgRE 2!mulRBr addRAC addRA.
rewrite -addR_opp -addRA; apply: (leR_add _ _ _ _ (Hf _ _ _)).
by rewrite -2!mulRN addRC; exact: (R_convex_functionN Hg).
Qed.

Lemma R_concave_functionB f (g : T -> R) :
  concave_function f -> convex_function g ->
  concave_function (fun x => f x - g x)%coqR.
Proof.
move=> Hf Hg.
rewrite (_ : (fun _ => _) = (fun x => - (g x - f x)))%coqR; last first.
  by apply/funext => x; rewrite oppRB.
exact/R_concave_functionN/R_convex_functionB.
Qed.

End Rprop2.

End concave_function_prop.

Section affine_function_prop.
Variables (T : convType) (U : orderedConvType).

Lemma affine_functionP (f : T -> U) :
  affine f <-> convex_function f /\ concave_function f.
Proof.
split => [H | [H1 H2] p q t]; last first.
  by rewrite eqconv_le; split; [exact/H1|exact/H2].
split => p q t.
- by rewrite /convex_function_at H; exact/leconvR.
- by rewrite /concave_function_at/convex_function_at H; exact/leconvR.
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
  by rewrite Convn_comp.
case=> n [g [e [Hg]]] ->{b}.
suff [h Hh] : exists h : 'I_n -> T, forall i, Z (h i) /\ f (h i) = g i.
  exists (<|>_e h).
    exists n; exists h; exists e; split => //.
    move=> a [i _] <-.
    by case: (Hh i).
  rewrite Convn_comp; apply eq_Convn => // i /=.
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

Lemma preimage_subset_convex_hull (f: {affine T -> U}) (Z: set U): hull (f @^-1` Z) `<=` f @^-1` (hull Z).
Proof.
move=>x [n [g [d [gZ ->]]]] /=.
rewrite Convn_comp.
exists n, (f \o g), d; split=>//.
by move=>y [i _ <-]; apply gZ; exists i.
Qed.

End affine_function_image.

(* TODO: rename, move to mathcomp *)
Lemma factorize_range (A B C : Type) (f : B -> C) (g : A -> C) :
  (range g `<=` range f)%classic ->
  exists h : A -> B, g = f \o h.
Proof.
move=> gf; have [h gfh] : {h & forall a, g a = f (h a)}.
  apply: (@choice _ _ (fun a b => g a = f b)) => a.
  have /cid2[b _ <-] : range f (g a) by apply gf; exists a.
  by exists b.
by exists h; apply/funext => a; rewrite gfh.
Qed.

(* NB: PR has been merged into mathcomp-analysis *)
Lemma image2_subset {aT bT rT : Type} [f : aT -> bT -> rT] [A B: set aT] [C D : set bT] :
  (A `<=` B)%classic -> (C `<=` D)%classic ->
  ([set f x y | x in A & y in C] `<=` [set f x y | x in B & y in D])%classic.
Proof.
move=> AB CD x [a aA [c cC xe]]; subst x; exists a; (try by apply AB).
by exists c; (try by apply CD).
Qed.

Section linear_function_image0.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Variables (R : ringType) (T U : lmodType R).

(* TODO: move to mathcomp *)
Lemma preimage_add_ker (f : {linear T -> U}) (A: set U) :
  [set a + b | a in f @^-1` A & b in f @^-1` [set 0]] = f @^-1` A.
Proof.
rewrite eqEsubset; split.
-  move=> x [a /= aA] [b /= bker] xe; subst x.
   by rewrite linearD bker addr0.
- move=> x /= fx; exists x=>//.
  by exists 0; [ rewrite linear0 | rewrite addr0].
Qed.

End linear_function_image0.

Section linear_function_image.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Variables (T U : lmodType R).
Import LmoduleConvex.
(* TODO: find how to speak about multilinear maps. *)
Lemma hull_add (A B : set T) :
  hull [set a + b | a in A & b in B] =
  [set a + b | a in hull A & b in hull B].
Proof.
rewrite eqEsubset; split.
set xx := [set a + b | a in hull A & b in hull B].
- have conv : is_convex_set xx.
    apply/asboolP=>x y p [ax axA] [bx bxB] <- [ay ayA] [by' byB] <-.
    rewrite avgr_addD; exists (ax <|p|> ay).
       by move: (hull_is_convex A)=>/asboolP; apply.
    exists (bx <|p|> by')=>//.
    by move: (hull_is_convex B)=>/asboolP; apply.
  pose xx' : {convex_set T} := @ConvexSet.Pack T xx (@ConvexSet.Class _ _ (isConvexSet.Build _ _ conv)).
  apply: (@hull_sub_convex _ _ xx').
  by apply/image2_subset; exact (@subset_hull _ _).
move=>x [a [na [ga [da [gaA ->]]]]] [b [nb [gb [db [gbB ->]]]]] <-.
rewrite avgnr_add.
exists (na * nb)%nat,
  (fun i => let (i, j) := split_prod i in ga i + gb j),
  (fdistmap (unsplit_prod (n:=nb)) da `x db); split=>// y [i _ <-].
by case: split_prod => ia ib; exists (ga ia); [by apply gaA; exists ia |];
  exists (gb ib)=>//; apply gbB; exists ib.
Qed.

Import LinearAffine.
Proposition preimage_preserves_convex_hull (f : {linear T -> U}) (Z : set U) :
  Z `<=` range f -> f @^-1` (hull Z) = hull (f @^-1` Z).
Proof.
rewrite eqEsubset=>Zf; split; last by apply preimage_subset_convex_hull.
move=>x [n [g [d [gZ fx]]]].
move: Zf=>/(subset_trans gZ)/factorize_range [h ge]; subst g.
rewrite -preimage_add_ker hull_add.
exists (<|>_d h).
   by exists n, h, d; split=>// y [z _ <-] /=; apply gZ; exists z.
exists (x - <|>_d h).
   by apply subset_hull=>/=; rewrite linearB Convn_comp fx subrr.
by rewrite addrC -addrA [-_+_]addrC subrr addr0.
Qed.

End linear_function_image.

Section R_affine_function_prop.
Variables (T : convType) (f : T -> R).
Lemma R_affine_functionN : affine f -> affine (fun x => - f x)%coqR.
Proof.
move/affine_functionP => [H1 H2]; rewrite affine_functionP.
split => //; [exact/R_convex_functionN|exact/R_concave_functionN].
Qed.
End R_affine_function_prop.

Section convex_function_in_def.
Variables (T : convType) (U : orderedConvType) (D : {convex_set T}) (f : T -> U).

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

Definition Rpos_interval : set R := (fun x => 0 < x)%coqR.

Lemma Rpos_convex : is_convex_set Rpos_interval.
Proof.
apply/asboolP => x y t Hx Hy.
have [->|Ht0] := eqVneq t 0%:pr; first by rewrite conv0.
apply addR_gt0wl; first by apply mulR_gt0 => //; exact/RltP/prob_gt0.
apply mulR_ge0 => //; exact: ltRW.
Qed.

(*#[local]*)
HB.instance Definition _ := isConvexSet.Build R Rpos_interval Rpos_convex.

Definition Rnonneg_interval : set R := (fun x => 0 <= x)%coqR.

Lemma Rnonneg_convex : is_convex_set Rnonneg_interval.
Proof. apply/asboolP=> x y t Hx Hy; apply addR_ge0; exact/mulR_ge0. Qed.

(*#[local]*)
HB.instance Definition _ := isConvexSet.Build R Rnonneg_interval Rnonneg_convex.

Lemma open_interval_convex a b (Hab : (a < b)%coqR) :
  is_convex_set (fun x => a < x < b)%coqR.
Proof.
apply/asboolP => x y t [xa xb] [ya yb].
have [->|t0] := eqVneq t 0%:pr; first by rewrite conv0.
have [->|t1] := eqVneq t 1%:pr; first by rewrite conv1.
apply conj.
- rewrite -[X in (X < Prob.p t * x + (Prob.p t).~ * y)%coqR]mul1r -(onemKC (Prob.p t)).
  rewrite (mulrDl _ _ a) -RplusE.
  apply ltR_add; rewrite ltR_pmul2l //; [exact/RltP/prob_gt0 | exact/RltP/onem_gt0/prob_lt1].
- (*rewrite -[X in (_ + _ < X)%coqR]mul1R -(onemKC t) mulRDl.*)
rewrite -[X in (_ + _ < X)%coqR]mul1r.
rewrite -(onemKC (Prob.p t)).
rewrite mulrDl.
  apply ltR_add; rewrite ltR_pmul2l //; [exact/RltP/prob_gt0 | exact/RltP/onem_gt0/prob_lt1].
Qed.

Definition uniti : set R := (fun x => 0 < x < 1)%coqR.

Lemma open_unit_interval_convex : is_convex_set uniti.
Proof. exact: open_interval_convex. Qed.

HB.instance Definition _ := isConvexSet.Build R uniti open_unit_interval_convex.

End convex_set_R.

Section convex_function_R.

Implicit Types f : R -> R.

Lemma concave_function_atN f x y t : concave_function_at f x y t ->
  forall k, (0 <= k)%coqR -> concave_function_at (fun x => f x * k)%coqR x y t.
Proof.
move=> H k k0; rewrite /concave_function_at /convex_function_at.
rewrite conv_leoppD leoppP avgRE.
rewrite /leconv /= -avgR_mulDl.
exact: leR_wpmul2r.
Qed.

Lemma convexf_at_onem x y (t : {prob R}) f : (0 < x -> 0 < y -> x < y ->
  convex_function_at f x y t -> convex_function_at f y x (Prob.p t).~%:pr)%coqR.
Proof.
move=> x0 y0 xy H; rewrite /convex_function_at.
rewrite [in X in leconv _ X]avgRE /= onemK addRC.
rewrite /convex_function_at !avgRE in H.
rewrite avgRE /= onemK addRC.
by apply: (leR_trans H); rewrite addRC; apply/RleP; rewrite lexx.
Qed.

Lemma concavef_at_onem x y (t : {prob R}) f : (0 < x -> 0 < y -> x < y ->
  concave_function_at f x y t -> concave_function_at f y x (Prob.p t).~%:pr)%coqR.
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
Let I := fun x0 => (a <= x0 <= b)%coqR.
Hypothesis HDf : pderivable f I.
Variable Df : R -> R.
Hypothesis DfE : forall x (Hx : I x), Df x = derive_pt f x (HDf Hx).
Hypothesis HDDf : pderivable Df I.
Variable DDf : R -> R.
Hypothesis DDfE : forall x (Hx : I x), DDf x = derive_pt Df x (HDDf Hx).
Hypothesis DDf_ge0 : forall x, I x -> (0 <= DDf x)%coqR.

Definition L (x : R) := (f a + (x - a) / (b - a) * (f b - f a))%coqR.

Hypothesis ab : (a < b)%coqR.

Lemma LE x : L x = ((b - x) / (b - a) * f a + (x - a) / (b - a) * f b)%coqR.
Proof.
rewrite /L mulRBr [in LHS]addRA addRAC; congr (_ + _)%coqR.
rewrite addR_opp -{1}(mul1R (f a)) -mulRBl; congr (_ * _)%coqR.
rewrite -(mulRV (b - a)); last by rewrite subR_eq0'; exact/gtR_eqF.
by rewrite -mulRBl -addR_opp oppRB addRA subRK addR_opp.
Qed.

Lemma convexf_ptP : (forall x, a <= x <= b -> 0 <= L x - f x)%coqR ->
  forall t : {prob R}, convex_function_at f a b t.
Proof.
move=> H t; rewrite /convex_function_at.
set x := (Prob.p t * a + (Prob.p t).~ * b)%coqR.
have : (a <= x <= b)%coqR.
  rewrite /x; split.
  - apply (@leR_trans (Prob.p t * a + (Prob.p t).~ * a)).
      rewrite -mulRDl addRCA addR_opp subRR addR0 mul1R.
      by apply/RleP; rewrite lexx.
    have [->|t1] := eqVneq t 1%:pr.
      by rewrite mul1R onem1 2!mul0R; exact/RleP.
    rewrite leR_add2l; apply leR_wpmul2l => //; exact/ltRW.
  - apply (@leR_trans (Prob.p t * b + (Prob.p t).~ * b)); last first.
      rewrite -mulRDl addRCA addR_opp subRR addR0 mul1R.
      by apply/RleP; rewrite lexx.
    rewrite leR_add2r; apply leR_wpmul2l => //; exact/ltRW.
move/H; rewrite subR_ge0 => /leR_trans; apply.
rewrite LE //.
have -> : ((b - x) / (b - a) = Prob.p t)%coqR.
  rewrite /x -addR_opp oppRD addRCA mulRBl mul1R oppRB (addRCA b).
  rewrite addR_opp subRR addR0 -mulRN addRC -mulRDr addR_opp.
  rewrite /Rdiv -mulRA mulRV ?mulR1 // subR_eq0'; exact/gtR_eqF.
have -> : ((x - a) / (b - a) = (Prob.p t).~)%coqR.
  rewrite /x -addR_opp addRAC -{1}(oppRK a) mulRN -mulNR -{2}(mul1R (- a)%coqR).
  rewrite -mulRDl (addRC _ R1) addR_opp -mulRDr addRC addR_opp.
  rewrite /Rdiv -mulRA mulRV ?mulR1 // subR_eq0'; exact/gtR_eqF.
by apply/RleP; rewrite lexx.
Qed.

Lemma second_derivative_convexf_pt : forall t : {prob R}, convex_function_at f a b t.
Proof.
have note1 : forall x, R1 = ((x - a) / (b - a) + (b - x) / (b - a))%coqR.
  move=> x; rewrite -mulRDl addRC addRA subRK addR_opp mulRV // subR_eq0'.
  exact/gtR_eqF.
have step1 : forall x, f x = ((x - a) / (b - a) * f x + (b - x) / (b - a) * f x)%coqR.
  by move=> x; rewrite -mulRDl -note1 mul1R.
apply convexf_ptP => // x axb.
rewrite /L.
case: axb.
  rewrite leR_eqVlt => -[-> _|].
  by rewrite /L subRR div0R mul0R addR0 subRR.
move=> ax.
rewrite leR_eqVlt => -[->|xb].
  rewrite /L /Rdiv mulRV ?mul1R; last by rewrite subR_eq0'; exact/gtR_eqF.
  by rewrite addRC subRK subRR.
have {step1}step2 : (L x - f x =
  (x - a) * (b - x) / (b - a) * ((f b - f x) / (b - x)) -
  (b - x) * (x - a) / (b - a) * ((f x - f a) / (x - a)))%coqR.
  rewrite {1}step1 {step1}.
  rewrite -addR_opp oppRD addRA addRC addRA.
  rewrite LE //.
  rewrite {1}/Rdiv -(mulRN _ (f x)) -/(Rdiv _ _).
  rewrite addRA -mulRDr (addRC _ (f a)) (addR_opp (f a)).
  rewrite -mulRN -addRA -mulRDr (addR_opp (f b)).
  rewrite addRC.
  rewrite -(oppRK (f a - f x)) mulRN addR_opp oppRB.
  congr (_ + _)%coqR.
  - rewrite {1}/Rdiv -!mulRA; congr (_ * _)%coqR; rewrite mulRCA; congr (_ * _)%coqR.
    rewrite mulRCA mulRV ?mulR1 // subR_eq0'; exact/gtR_eqF.
  - rewrite -!mulNR -!mulRA; congr (_ * _)%coqR; rewrite mulRCA; congr (_ * _)%coqR.
    rewrite mulRCA mulRV ?mulR1 // subR_eq0'; exact/gtR_eqF.
have [c2 [Ic2 Hc2]] : exists c2, (x < c2 < b /\ (f b - f x) / (b - x) = Df c2)%coqR.
  have H : pderivable f (fun x0 => x <= x0 <= b)%coqR.
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
have [c1 [Ic1 Hc1]] : exists c1, (a < c1 < x /\ (f x - f a) / (x - a) = Df c1)%coqR.
  have H : pderivable f (fun x0 => a <= x0 <= x)%coqR.
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
have c1c2 : (c1 < c2)%coqR by apply (@ltR_trans x); [case: Ic1 | case: Ic2].
have {step2 Hc1 Hc2}step3 : (L x - f x =
  (b - x) * (x - a) * (c2 - c1) / (b - a) * ((Df c2 - Df c1) / (c2 - c1)))%coqR.
  rewrite {}step2 Hc2 Hc1 (mulRC (x - a)%coqR) -mulRBr {1}/Rdiv -!mulRA.
  congr (_ * (_ * _))%coqR; rewrite mulRCA; congr (_ * _)%coqR.
  rewrite mulRCA mulRV ?mulR1 // subR_eq0'; by move/gtR_eqF : c1c2.
have [d [Id H]] : exists d, (c1 < d < c2 /\ (Df c2 - Df c1) / (c2 - c1) = DDf d)%coqR.
  have H : pderivable Df (fun x0 => c1 <= x0 <= c2)%coqR.
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
