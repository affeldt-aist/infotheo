(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg fingroup perm finalg matrix.
From mathcomp Require Import boolp classical_sets.
Require Import Reals.
From mathcomp Require Import Rstruct.
Require Import ssrR Reals_ext Ranalysis_ext ssr_ext ssralg_ext logb Rbigop.
Require Import fdist jfdist fsdist convex.

(******************************************************************************)
(*                  Equivalence of Convexity Definitions                      *)
(*                                                                            *)
(*   naryConvType == type that provides a nary operator intended to represent *)
(*                   nary convex combination as found in standard             *)
(*                   of convex spaces such as [Bonchi 2017]; different        *)
(*                   axiomatics are possible, they are provided with their    *)
(*                   equivalencs by the module NaryConvexSpaceEquiv           *)
(*        <&>_d f == notation for the operator of naryConvType                *)
(*    a <& p &> b == binary instance of the <&>_ operator                     *)
(*                                                                            *)
(* Reference: R. Affeldt, J. Garrigue, T. Saikawa. Formal adventures in       *)
(* convex and conical spaces. CICM 2020                                       *)
(******************************************************************************)

Reserved Notation "'<&>_' d f" (at level 36, f at level 36, d at level 0,
  format "<&>_ d  f").
Reserved Notation "x <& p &> y" (format "x  <& p &>  y", at level 49).

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope convex_scope.

Module NaryConvexSpace.

HB.mixin Record isNaryConv (T : Type) := {
  narychoice : Choice.class_of T ;
  convn : forall n, {fdist 'I_n} -> ('I_n -> T) -> T
}.

#[short(type=naryConvType)]
HB.structure Definition NaryConv := {T & isNaryConv T}.

Notation "'<&>_' d f" := (convn _ d f) : convex_scope.

Canonical naryconv_eqType (T : naryConvType) := EqType T narychoice.
Canonical conv_choiceType (T : naryConvType) := ChoiceType T narychoice.

(*Record mixin_of (T : choiceType) : Type :=
  Mixin { convn : forall n, {fdist 'I_n} -> ('I_n -> T) -> T }.
Record class_of (T : Type) := Class {
  base : Choice.class_of T ;
  mixin : mixin_of (Choice.Pack base) }.
Structure t : Type := Pack { car : Type ; class : class_of car }.
Definition baseType (T : t) := Choice.Pack (base (class T)).
Module Exports.
Definition naryConv (T : t) : forall n, {fdist 'I_n} -> ('I_n -> car T) -> car T
  := match T with Pack _ (Class _ (Mixin x)) => x end.
Arguments naryConv {T} {n} : simpl never.
Notation "'<&>_' d f" := (naryConv d f) : convex_scope.
Notation naryConvType := t.
Coercion baseType : naryConvType >-> choiceType.
Canonical baseType.
End Exports.*)
End NaryConvexSpace.

Module NaryConvexSpaceEquiv.
Import NaryConvexSpace.

(* In this module we use funext to avoid explicitly handling the congruence
   of convn (cf. eq_convn in convex_choice.v for the iterated version). *)

(* These definitions about distributions should probably be elsewhere *)
Definition fdistE :=
  (FDistMap.dE,FDist1.dE,ProdFDist.dE,Swap.dI,Swap.dE,ConvnFDist.dE,Bivar.fstE).

Module FDistPart.
Section fdistpart.
Variables (n m : nat) (K : 'I_m -> 'I_n) (e : {fdist 'I_m}) (i : 'I_n).
Definition d :=
  CondJFDist.d (Swap.d (ProdFDist.d e (fun j : 'I_m => FDist1.d (K j)))) i.
Definition den :=
  Bivar.fst (Swap.d (ProdFDist.d e (fun j : 'I_m => FDist1.d (K j)))) i.

Lemma denE : den = FDistMap.d K e i.
Proof.
rewrite /den !fdistE [RHS]big_mkcond /=.
under eq_bigl do rewrite inE.
apply/eq_bigr => a _.
rewrite !fdistE /= (big_pred1 (a,i)) ?fdistE /=;
    last by case=> x y; rewrite /swap /= !xpair_eqE andbC.
rewrite eq_sym 2!inE.
by case: eqP => // _; rewrite (mulR0,mulR1).
Qed.

Lemma dE j :
  FDistMap.d K e i != 0%R ->
  d j = (e j * (i == K j)%:R / \sum_(j | K j == i) e j)%R.
Proof.
rewrite -denE => NE.
rewrite CondJFDist.dE // {NE} /jcPr /proba.Pr.
rewrite (big_pred1 (j,i)); last first.
  move=> k; by rewrite !inE [in RHS](surjective_pairing k) xpair_eqE.
rewrite (big_pred1 i); last by move=> k; rewrite !inE.
rewrite !fdistE big_mkcond [in RHS]big_mkcond /=.
congr (_ / _)%R.
under eq_bigr => k do rewrite {2}(surjective_pairing k).
rewrite -(pair_bigA _ (fun k l =>
          if l == i
          then ProdFDist.d e (fun j0 : 'I_m => FDist1.d (K j0)) (k, l)
          else R0))%R /=.
apply eq_bigr => k _.
rewrite -big_mkcond /= big_pred1_eq !fdistE /= eq_sym.
case: ifP; by rewrite (mulR1,mulR0).
Qed.
End fdistpart.

Lemma dK n m K (e : {fdist 'I_m}) j :
  e j = (\sum_(i < n) FDistMap.d K e i * d K e i j)%R.
Proof.
under eq_bigr => /= a _.
  case/boolP: (FDistMap.d K e a == 0%R) => Ka0.
    rewrite (eqP Ka0) mul0R.
    have <- : (e j * (a == K j)%:R = 0)%R.
      have [Kj|] := boolP (a == K j); last by rewrite mulR0.
      move/eqP: Ka0; rewrite fdistE /=.
      move/psumR_eq0P => -> //; by rewrite ?(mul0R,inE) // eq_sym.
  over.
  rewrite FDistPart.dE // fdistE /= mulRCA mulRV ?mulR1;
    last by rewrite fdistE in Ka0.
over.
move=> /=.
rewrite (bigD1 (K j)) //= eqxx mulR1.
by rewrite big1 ?addR0 // => i /negbTE ->; rewrite mulR0.
Qed.
End FDistPart.

Section Axioms.
Variable T : naryConvType.

Definition ax_bary :=
  forall n m (d : {fdist 'I_n}) (e : 'I_n -> {fdist 'I_m}) (g : 'I_m -> T),
    <&>_d (fun i => <&>_(e i) g) = <&>_(ConvnFDist.d d e) g.
Definition ax_proj :=
  forall  n (i : 'I_n) (g : 'I_n -> T), <&>_(FDist1.d i) g = g i.

(* Beaulieu's version [Beaulieu PhD 2008] *)
Definition ax_part :=
  forall n m (K : 'I_m -> 'I_n) (d : {fdist 'I_m}) (g : 'I_m -> T),
    <&>_d g = <&>_(FDistMap.d K d) (fun i => <&>_(FDistPart.d K d i) g).
Definition ax_idem :=
  forall (a : T) (n : nat) (d : {fdist 'I_n}) (g : 'I_n -> T),
    (forall i, i \in fdist_supp d -> g i = a) -> <&>_d g = a.

(* Alternative to ax_proj *)
Definition ax_map :=
  forall (n m : nat) (u : 'I_m -> 'I_n) (d : {fdist 'I_m}) (g : 'I_n -> T),
    <&>_d (g \o u) = <&>_(FDistMap.d u d) g.
Definition ax_const :=
  forall (a : T) (n : nat) (d : {fdist 'I_n}),
    <&>_d (fun _ => a) = a.

(* Alternative to ax_part, just a restriction of ax_barycenter *)
Definition ax_bary_part :=
  forall n m (d : {fdist 'I_n}) (e : 'I_n -> {fdist 'I_m}) (g : 'I_m -> T),
    (forall i j, i != j ->
                 fdist_supp (e i) :&: fdist_supp (e j) = finset.set0) ->
    <&>_d (fun i => <&>_(e i) g) = <&>_(ConvnFDist.d d e) g.

(* Restriction of ax_map to injective maps *)
Definition ax_inj_map :=
  forall (n m : nat) (u : 'I_m -> 'I_n) (d : {fdist 'I_m}) (g : 'I_n -> T),
    injective u -> <&>_d (g \o u) = <&>_(FDistMap.d u d) g.
End Axioms.

(* We will prove:
   binary axioms <-> ax_barycenter + ax_proj <-> ax_part + ax_idem
                 <-> ax_barycenter + ax_map + ax_const <-> ax_barycenter_part + ax_idem
   but (ax_barycenter + ax_const) and (ax_part + ax_proj) are weaker.
   Note that we have ax_idem -> ax_proj and ax_idem -> ax_const.
 *)

Module Type NaryConvSpace.
Parameter T : naryConvType.
Parameter axbary : ax_bary T.
Parameter axproj : ax_proj T.
End NaryConvSpace.

Module Type ConvSpace. Axiom T : convType. End ConvSpace.

(* First prove mutual definability using ax_barycenter / ax_proj *)

Module BinToNary(C : ConvSpace) <: NaryConvSpace.
Import NaryConvexSpace.
(*Definition naryConv_mixin : mixin_of [choiceType of C.T] := Mixin (@Convn C.T).*)

HB.instance Definition _ := @isNaryConv.Build _ (Choice.class _) (@Convn C.T).

(*Definition T : naryConvType := Pack (Class naryConv_mixin).*)
Definition T : naryConvType := Choice_sort__canonical__NaryConvexSpace_NaryConv.
Definition axbary := @Convn_convnfdist C.T.
Definition axproj := @ConvnFDist1 C.T.
End BinToNary.

Module NaryToBin(A : NaryConvSpace).
Export A.

(* axmap, axconst and axidem are consequences of axbary + axproj *)
Lemma axmap : ax_map T.
Proof.
move=> n m u d g.
have -> : FDistMap.d u d = ConvnFDist.d d (fun i : 'I_m => FDist1.d (u i)).
  by apply fdist_ext => i; rewrite /FDistMap.d FDistBind.dE ConvnFDist.dE.
rewrite -axbary.
by congr (<&>_ _ _); apply funext => i /=; rewrite axproj.
Qed.

Lemma axconst : ax_const T.
Proof.
move=> a n d.
by rewrite -(axproj (@ord0 0) (fun=>a)) axbary ConvnFDist.cst.
Qed.

Lemma axidem : ax_idem T.
Proof.
move=> a n d g Hd.
have /=[k Hk] := fdist_supp_mem d.
have -> : g = (fun i => <&>_(FDist1.d (if i \in fdist_supp d then k else i)) g).
  apply funext => i; rewrite axproj.
  case: ifP => // /Hd ->; by rewrite (Hd k).
rewrite axbary (_ : ConvnFDist.d _ _ = FDist1.d k) ?axproj ?Hd //.
apply fdist_ext => /= i; rewrite !fdistE rsum_fdist_supp.
under eq_bigr => j /= -> do rewrite fdistE.
by rewrite -rsum_fdist_supp -big_distrl FDist.f1 /= mul1R.
Qed.

(* axconst is also a corollary of axidem *)
Corollary axconst' : ax_const T.
Proof. by move=> a n d; apply axidem. Qed.

(* Definition of conv based on convn *)
Definition binconv p (a b : T) :=
  <&>_(I2FDist.d p) (fun x : 'I_2 => if x == ord0 then a else b).
Notation "a <& p &> b" := (binconv p a b).

Lemma binconvC p a b : a <& p &> b = b <& (p.~)%:pr &> a.
Proof.
rewrite /binconv.
set g1 := fun x => _.
set g2 := fun x => _.
have -> : g1 = g2 \o tperm ord0 (Ordinal (erefl (1 < 2))).
  rewrite /g1 /g2 /=.
  apply funext => i /=.
  by case/orP: (ord2 i) => /eqP -> /=; rewrite (tpermL,tpermR).
rewrite axmap.
congr (<&>_ _ _); apply fdist_ext => i.
rewrite FDistMap.dE (bigD1 (tperm ord0 (Ordinal (erefl (1 < 2))) i)) /=; last first.
  by rewrite !inE tpermK.
rewrite big1.
  rewrite addR0 !I2FDist.dE onemK.
  by case/orP: (ord2 i) => /eqP -> /=; rewrite (tpermL,tpermR).
move=> j /andP[] /eqP <-.
by rewrite tpermK eqxx.
Qed.

Lemma convn_if A n (p : A -> bool) (d1 d2 : {fdist 'I_n}) (g : _ -> T):
  (fun x => if p x then <&>_d1 g else <&>_d2 g) =
  (fun x => <&>_(if p x then d1 else d2) g).
Proof. apply funext => x; by rewrite (fun_if (fun d => <&>_d g)). Qed.

Lemma binconvA p q a b c :
  a <& p &> (b <& q &> c) = (a <& [r_of p, q] &> b) <& [s_of p, q] &> c.
Proof.
rewrite /binconv.
set g := fun i : 'I_3 => if i <= 0 then a else if i <= 1 then b else c.
rewrite [X in <&>_(I2FDist.d q) X](_ : _ = g \o lift ord0);
  last by apply funext => i; case/orP: (ord2 i) => /eqP ->.
rewrite [X in <&>_(I2FDist.d [r_of p, q]) X]
        (_ : _ = g \o (widen_ord (leqnSn 2)));
  last by apply funext => i; case/orP: (ord2 i) => /eqP ->.
rewrite 2!axmap.
set d1 := FDistMap.d _ _.
set d2 := FDistMap.d _ _.
set ord23 := Ordinal (ltnSn 2).
have -> : a = g ord0 by [].
have -> : c = g ord23 by [].
rewrite -2!axproj 2!convn_if 2!axbary.
congr (<&>_ _ _); apply fdist_ext => j.
rewrite !ConvnFDist.dE !big_ord_recl !big_ord0 /=.
rewrite !I2FDist.dE !FDistMap.dE !FDist1.dE !addR0 /=.
case: j => -[|[|[]]] //= Hj.
- rewrite [in RHS](big_pred1 ord0) //.
  rewrite big1; last by case => -[].
  by rewrite I2FDist.dE eqxx !(mulR0,addR0) mulR1 mulRC -p_is_rs.
- rewrite (big_pred1 ord0) // (big_pred1 (Ordinal (ltnSn 1))) //.
  rewrite !I2FDist.dE !eqxx !(mulR0,addR0,add0R).
  rewrite {2}/onem mulRDr mulR1 mulRN [in RHS]mulRC -p_is_rs s_of_pqE'.
  by rewrite (addRC p) -addRA addRN addR0.
- rewrite (big_pred1 (Ordinal (ltnSn 1))) //.
  rewrite big1; last by case => -[|[]].
  by rewrite !I2FDist.dE !(mulR0,addR0,add0R,mulR1) s_of_pqE onemK.
Qed.

Lemma T21 a b : binconv 1%:pr a b = a.
Proof.
apply axidem => i.
rewrite inE I2FDist.dE.
case: ifP => //=.
by rewrite /onem subRR eqxx.
Qed.

Lemma T22 p a : binconv p a a = a.
Proof.
apply axidem => i.
by case: ifP.
Qed.

(*Definition conv_mixin : ConvexSpace.mixin_of T.
apply (@ConvexSpace.Mixin _ binconv).
- move=> a b; apply axidem => i.
  rewrite inE I2FDist.dE.
  case: ifP => //=.
  by rewrite /onem subRR eqxx.
- move=> p a; apply axidem => i.
  by case: ifP.
- exact binconvC.
- exact binconvA.
Defined.

Definition T2 := ConvexSpace.Pack (ConvexSpace.Class conv_mixin).*)

#[export]
HB.instance Definition _ := @isConvexSpace.Build T (Choice.class _) binconv
  T21 T22 binconvC binconvA.

End NaryToBin.
HB.reexport NaryToBin.

(* Then prove BinToN and NToBin cancel each other:
   operations should coincide on both sides *)

Module Equiv1(C : ConvSpace).
Module A := BinToNary(C).
Module B := NaryToBin(A).
Import A B.

Lemma equiv_conv p (a b : T) : a <| p |> b = a <& p &> b.
Proof.
rewrite /binconv.
Import ScaledConvex.
apply S1_inj.
by rewrite S1_conv.
(*
 S1_convn.
by rewrite !big_ord_recl big_ord0 /= !I2FDist.dE /= addpt0.*)
Qed.
End Equiv1.

Module Equiv2(A : NaryConvSpace).
Module B := NaryToBin(A).
Import A B.

(*Local Canonical T2 := B.T2.*)

Lemma equiv_convn n (d : {fdist 'I_n}) g : <&>_d g = <|>_d g.
Proof.
elim: n d g.
  move=> d; move: (fdist_card_neq0 d).
  by rewrite card_ord.
move=> n IH d g /=.
case: Bool.bool_dec.
  rewrite FDist1.dE1 => /eqP ->.
  by rewrite axproj.
move=> b; rewrite -{}IH.
have -> : (fun i => g (DelFDist.f ord0 i)) = g \o lift ord0.
  apply funext => i; by rewrite /DelFDist.f ltn0.
symmetry; rewrite axmap (*/Conv*) /=.
rewrite /(_ <| _ |> _)/=.
rewrite /binconv.
set d' := FDistMap.d _ _.
rewrite -(axproj ord0).
rewrite convn_if axbary.
congr (<&>_ _ _); apply fdist_ext => i.
rewrite ConvnFDist.dE !big_ord_recl big_ord0 addR0 /= !I2FDist.dE /=.
rewrite FDist1.dE /d' FDistMap.dE /=.
case/boolP: (i == ord0) => [/eqP -> |].
  by rewrite big1 // mulR0 mulR1 addR0.
rewrite /= mulR0 add0R.
case: (unliftP ord0 i) => //= [j|] -> // Hj.
rewrite (big_pred1 j) //=.
rewrite DelFDist.dE D1FDist.dE /= /onem mulRC -mulRA mulVR ?mulR1 //.
apply/eqP => /(f_equal (Rplus (d ord0))).
rewrite addRCA addRN !addR0 => b'.
by elim b; rewrite -b' eqxx.
Qed.
End Equiv2.

Module Type MapConst.
Parameter T : naryConvType.
Parameter axmap : ax_map T.
Parameter axconst : ax_const T.
End MapConst.

(* axidem is a consequence of axmap + axconst *)
Module MapConstToIdem(A : MapConst).
Import A.

Lemma axidem : ax_idem T.
Proof.
move=> a n d g Ha.
set supp := fdist_supp d.
set f : 'I_#|supp| -> 'I_n := enum_val.
have [x Hx] := fdist_supp_mem d.
set f' : 'I_n -> 'I_#|supp| := enum_rank_in Hx.
set d' := FDistMap.d f' d.
have -> : d = FDistMap.d f d'.
  apply fdist_ext => i /=.
  rewrite FDistMap.comp FDistMap.dE /=.
  case/boolP: (i \in supp) => Hi.
  - rewrite (bigD1 i) /=; last first.
      by rewrite !inE /f /f' /= enum_rankK_in.
    rewrite big1; first by rewrite addR0.
    move=> j /andP[] /eqP <-.
    case/boolP: (j \in supp).
      by move=> Hj; rewrite /f /f' /= enum_rankK_in // eqxx.
    by rewrite inE negbK => /eqP.
  - rewrite big_pred0.
      move: Hi; by rewrite inE negbK => /eqP.
    move=> j; apply/negP => /eqP Hj.
    by move: Hi; rewrite -Hj enum_valP.
rewrite -axmap.
have -> : g \o f = fun=> a.
  apply funext => i; rewrite /f /= Ha //.
  move: (enum_valP i); by rewrite inE.
by rewrite axconst.
Qed.
End MapConstToIdem.

(* Prove equivalence of axioms with Beaulieu's presentation *)

Module Type BeaulieuSpace.
Parameter T : naryConvType.
Parameter axpart : ax_part T.
Parameter axidem : ax_idem T.
End BeaulieuSpace.

Module StandardToBeaulieu(A : NaryConvSpace) <: BeaulieuSpace.
Module B := NaryToBin(A).
Import A B.
Definition T := A.T.

Lemma axbarypart : ax_bary_part T.
Proof. by move=> *; apply axbary. Qed.

Lemma axidem : ax_idem T.
Proof. by move=> a n d g Hd; apply axidem => i; move: (Hd i); rewrite inE. Qed.

Lemma axpart : ax_part T.
Proof.
move=> n m K d g; rewrite axbary; congr (<&>_ _ _).
by apply fdist_ext => /= j; rewrite !fdistE -FDistPart.dK.
Qed.
End StandardToBeaulieu.

Module BeaulieuToStandard(B : BeaulieuSpace) <: NaryConvSpace.
Import B.
Definition T := B.T.

Lemma axproj : ax_proj T.
Proof. move=> *; apply axidem => j; by rewrite FDist1.supp inE => /eqP ->. Qed.

Lemma existb_sig (A : finType) (P : {pred A}) :
  [exists x, P x] -> {x | P x}.
Proof.
move=> He.
suff: [set x | P x] != finset.set0.
  case: (set_0Vmem [set x | P x]) => /=[/eqP -> // | [x]].
  rewrite inE => Hx _; by exists x.
case/existsP: He => x Px.
apply/eqP => /setP/(_ x).
by rewrite inE Px inE.
Qed.

Lemma axbarypart : ax_bary_part T.
Proof.
move=> n m d e g HP.
have [n0 Hn0] := fdist_supp_mem d.
set h' : 'I_n -> 'I_#|fdist_supp d| := enum_rank_in Hn0.
set h : 'I_#|fdist_supp d| -> 'I_n := enum_val.
have f j :
  {i | [forall i, j \notin fdist_supp (e (h i))]||(j \in fdist_supp (e (h i)))}.
  case/boolP: [forall i, j \notin fdist_supp (e (h i))].
    move=> _. by exists (proj1_sig (fdist_supp_mem (FDistMap.d h' d))).
  by rewrite -negb_exists negbK => /existb_sig.
rewrite /= in f.
rewrite [LHS](axpart h').
rewrite [RHS](axpart (fun j => proj1_sig (f j))).
have trivIK i j x : x \in fdist_supp (e i) -> x \in fdist_supp (e j) -> i = j.
  case/boolP: (i == j) => [/eqP // | ij] xi xj.
  move/setP/(_ x): (HP _ _ ij); by rewrite inE xi xj inE.
have neqj j a k :
  a \in fdist_supp (e (h j)) -> k != (h j) -> (d k * e k a = 0)%R.
  move=> Haj kj.
  case/boolP: (a \in fdist_supp (e k)) => [ak|].
    by rewrite (trivIK _ _ _ Haj ak) eqxx in kj.
  rewrite inE negbK => /eqP ->.
  by rewrite mulR0.
have Hmap' i : FDistMap.d h' d i = (\sum_j d (h i) * e (h i) j)%R.
  rewrite -big_distrr fdistE /= FDist.f1 /= mulR1.
  rewrite (bigD1 (h i)) /=; last by rewrite /h /h' !inE enum_valK_in eqxx.
  rewrite big1 /= ?addR0 // => j /andP[] /eqP <-.
  case /boolP: (j \in fdist_supp d) => Hj.
    by rewrite /h /h' (enum_rankK_in Hn0 Hj) eqxx.
  move: Hj; by rewrite inE negbK => /eqP.
have Hmap i :
  FDistMap.d (fun j : 'I_m => sval (f j)) (ConvnFDist.d d e) i =
  FDistMap.d h' d i.
  rewrite fdistE big_mkcond /=.
  under eq_bigr do rewrite fdistE.
  rewrite (eq_bigr (fun j => d (h i) * e (h i) j)%R).
    by rewrite Hmap'.
  move=> /= a _; rewrite !inE; case: (f a) => j /= /orP[/forallP /= |] Ha.
    have Ha0 k : (d k * e k a = 0)%R.
      case/boolP: (k \in fdist_supp d) => [Hk|].
        move: (Ha (h' k)).
        by rewrite inE negbK /h/h' enum_rankK_in // => /eqP ->; rewrite mulR0.
      by rewrite inE negbK => /eqP -> ; rewrite mul0R.
    rewrite (proj2 (psumR_eq0P _)) ?(if_same,Ha0,mulR0) // => k _.
    exact: mulR_ge0.
  case: ifPn => [/eqP/esym ->{i}|ji].
    by rewrite (bigD1 (h j)) //= big1 ?addR0 // => *; rewrite (neqj j).
  by rewrite (neqj j) //; apply: contra ji => /eqP/enum_val_inj ->.
congr (<&>_ _ _); first by apply fdist_ext => /= i; rewrite Hmap.
apply funext => i /=.
have HF : FDistMap.d h' d i != 0%R.
  rewrite fdistE /=.
  apply/eqP => /psumR_eq0P => H.
  have: h i \in fdist_supp d by apply enum_valP.
  by rewrite inE H ?eqxx // 2!inE /h /h' enum_valK_in.
rewrite (@axidem (<&>_(e (h i)) g)); last first.
  move=> /= j; rewrite inE.
  rewrite FDistPart.dE //.
  case/boolP: (j \in fdist_supp d) => [Hj|].
    case: (@eqP _ i) => [-> |].
      by rewrite /h /h' (enum_rankK_in _ Hj).
    by rewrite /Rdiv mulR0 mul0R eqxx.
  by rewrite inE negbK => /eqP ->; rewrite mul0R div0R eqxx.
congr (<&>_ _ _); apply fdist_ext => j.
rewrite FDistPart.dE; last first.
  rewrite !fdistE /=.
  under eq_bigr do rewrite fdistE.
  rewrite exchange_big /=.
  rewrite (bigD1 (h i)) //=.
  rewrite -big_distrr big_mkcond /=.
  rewrite (eq_bigr (e (h i))).
    rewrite FDist.f1 mulR1; apply paddR_neq0 => //.
      by apply/sumR_ge0 => *; apply/sumR_ge0 => *; apply/mulR_ge0.
    by left; move: (enum_valP i); rewrite inE.
  move=> /= k _; rewrite 2!inE; case: ifP => //.
  case: (f k) => /= x /orP[/forallP/(_ i)|Hkx Hx].
    by rewrite inE negbK => /eqP ->.
  case/boolP: (k \in fdist_supp (e (h i))) => [Hki |].
    move/eqP: (trivIK _ _ _ Hkx Hki) Hx.
    by rewrite (can_eq (enum_valK_in Hn0)) => ->.
  by rewrite inE negbK => /eqP ->.
move: (Hmap i).
rewrite fdistE /= => ->.
rewrite fdistE.
case: (f j) => /= k /orP[Hn|jk].
  move/forallP/(_ i): (Hn).
  rewrite inE negbK => /eqP ->.
  rewrite big1 /Rdiv ?mul0R //.
  move=> a _.
  move/forallP/(_ (h' a)): Hn.
  case/boolP: (a \in fdist_supp d).
    rewrite /h /h'.
    move/(enum_rankK_in _) ->.
    by rewrite inE negbK => /eqP ->; rewrite mulR0.
  by rewrite inE negbK => /eqP ->; rewrite mul0R.
rewrite (bigD1 (h k)) //= big1 ?addR0; last first.
  by move=> a Ha; apply (neqj k).
case/boolP: (j \in fdist_supp (e (h i))) => ji.
  have /enum_val_inj H := trivIK _ _ _ jk ji.
  subst k => {jk}.
  move: HF; rewrite eqxx mulR1 Hmap'.
  rewrite -big_distrr /= FDist.f1 mulR1 => HF.
  by rewrite /Rdiv mulRAC mulRV // mul1R.
case: eqP ji => [->|ik]; first by rewrite jk.
by rewrite inE negbK => /eqP ->; rewrite mulR0 div0R.
Qed.

Lemma axinjmap : ax_inj_map T.
Proof.
move=> n m u d g Hu.
have -> : FDistMap.d u d = ConvnFDist.d d (fun i : 'I_m => FDist1.d (u i)).
  apply fdist_ext => i; by rewrite /FDistMap.d FDistBind.dE ConvnFDist.dE.
rewrite -axbarypart.
- congr (<&>_ _ _); apply funext => j /=; symmetry; apply axidem => i.
  by rewrite FDist1.supp inE => /eqP ->.
- move=> x y xy.
  apply/setP => z.
  rewrite !FDist1.supp !inE.
  case: eqP => //= ->.
  rewrite eqtype.inj_eq //. exact: negbTE.
Qed.

Lemma axbary : ax_bary T.
Proof.
move=> n m d e g.
set f : 'I_n * 'I_m -> 'I_#|[finType of 'I_n * 'I_m]| := enum_rank.
set f' : 'I_#|[finType of 'I_n * 'I_m]| -> 'I_n * 'I_m := enum_val.
set h := fun k i => f (k, i).
set h' := fun i => snd (f' i).
rewrite (_ : (fun i => _) = (fun i => <&>_(FDistMap.d (h i) (e i)) (g \o h')));
  last first.
  apply funext => i.
  have {1}-> : g = (g \o h') \o h i.
    apply funext => j; by rewrite /h' /h /= /f' /f enum_rankK.
  rewrite axinjmap //.
  move=> x y; by rewrite /h => /enum_rank_inj [].
rewrite axbarypart; first last.
- move=> i j ij.
  apply/setP => x; rewrite !inE !fdistE.
  case/boolP: (i == (f' x).1) ij => [/eqP ->|] ij.
    rewrite [in X in _ && X]big_pred0 ?eqxx ?andbF //.
    move=> k; apply/eqP => hjk.
    move: ij; by rewrite -hjk /h /f /f' enum_rankK eqxx.
  rewrite big_pred0 ?eqxx //.
  move=> k; apply/eqP => hik.
  by move: ij; rewrite -hik /h /f /f' enum_rankK eqxx.
set e' := fun j : 'I_m =>
  FDistMap.d f (ProdFDist.d (CondJFDist.d (Swap.d (ProdFDist.d d e)) j)
                            (fun=> FDist1.d j)).
have {2}-> : g = (fun j => <&>_(e' j) (g \o h')).
  apply funext => j; apply/esym/axidem => k //.
  rewrite inE /e' fdistE (big_pred1 (f' k)) /=; last first.
    by move=> i; rewrite 2!inE -{1}(enum_valK k) /f (can_eq enum_rankK).
  rewrite !fdistE.
  case/boolP: (_ == j) => [/eqP <- // | Hj].
  by rewrite mulR0 eqxx.
rewrite [RHS]axbarypart; first last.
- move=> i j ij.
  apply/setP => x.
  rewrite inE [RHS]inE.
  case/boolP: (_ \in _) => kx //.
  case/boolP: (_ \in _) => ky //.
  rewrite !(inE,fdistE) /= in kx ky *.
  rewrite (big_pred1 (f' x)) in kx; last first.
    by move=> a; rewrite -{1}(enum_valK x) !inE (can_eq enum_rankK) eq_sym.
  rewrite (big_pred1 (f' x)) in ky; last first.
    by move=> a; rewrite -{1}(enum_valK x) !inE (can_eq enum_rankK) eq_sym.
  move: kx ky; rewrite !fdistE.
  case/boolP: ((f' x).2 == i) ij => [/eqP <-|] ij; last by rewrite mulR0 eqxx.
  by case/boolP: ((f' x).2 == j) ij => [/eqP <-|] //; rewrite mulR0 eqxx.
congr (<&>_ _ _); apply fdist_ext => k.
rewrite /d1 !fdistE.
under eq_bigr do rewrite fdistE big_distrr big_mkcond /=.
rewrite exchange_big /=; apply eq_bigr => j _.
rewrite !fdistE -big_mkcond /=.
rewrite (big_pred1 (f' k));
  last by move=> a; rewrite !inE -{1}(enum_valK k) /f (can_eq enum_rankK).
set p := f' k => /=.
case/boolP: (j == p.2) => [/eqP -> | Hj]; last first.
  rewrite big_pred0; first last.
    move=> i; apply/negbTE; apply: contra Hj.
    rewrite !inE -(enum_valK k) (can_eq enum_rankK).
    by rewrite (surjective_pairing (enum_val k)) => /eqP [] _ /eqP.
  by rewrite !fdistE eq_sym (negbTE Hj) !mulR0.
rewrite (big_pred1 p.1) /=; last first.
  move=> i; rewrite !inE -(enum_valK k) (can_eq enum_rankK).
  by rewrite (surjective_pairing (enum_val k)) xpair_eqE eqxx andbT.
case/boolP: (\sum_(i < n) d i * e i p.2 == 0)%R => [/eqP|] Hp.
  rewrite Hp mul0R (proj1 (psumR_eq0P _) Hp) //.
  move=> *; by apply mulR_ge0.
rewrite [RHS]mulRC !fdistE CondJFDist.dE !fdistE /=; last first.
  by under eq_bigr do rewrite Swap.dE ProdFDist.dE /=.
rewrite /jcPr /proba.Pr (big_pred1 p);
  last by move=> i; rewrite !inE -xpair_eqE -!surjective_pairing.
rewrite (big_pred1 p.2); last by move=> i; rewrite !inE.
rewrite eqxx mulR1 Bivar.sndE /= ProdFDist.dE.
under eq_bigr do rewrite ProdFDist.dE /=.
by rewrite -mulRA mulVR ?mulR1.
Qed.
End BeaulieuToStandard.
End NaryConvexSpaceEquiv.
