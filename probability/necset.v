(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import mathcomp_extra boolp classical_sets reals.
From mathcomp Require Import finmap.
Require Import realType_ext classical_sets_ext fdist fsdist convex.

(******************************************************************************)
(*       Semi-complete semilattice structures and non-empty convex sets       *)
(*                                                                            *)
(* neset T              == the type of non-empty sets over T                  *)
(* x%:ne                == try to infer whether x : set T is neset T          *)
(*                         (NB: worth moving to a dedicated file?)            *)
(* x <| p |>: Y         == (fun y => x <| p |> y) @` Y                        *)
(* X :<| p |>: Y        == \bigcup_(x in X) (x <| p |>: Y)                    *)
(*                                                                            *)
(* semiLattType         == type of (finitary) semilattice                     *)
(* semiCompSemiLattType == type of semicomplete semilattice, or infinitary    *)
(*                         semilattice which may come without a bottom        *)
(*                         element, provides an infinitary operator           *)
(*                         |_| : neset T -> T with the following axioms       *)
(*                         (inherits from semiLattice):                       *)
(*          1. |_| [set x] = x                                                *)
(*          2. |_| (\bigcup_(i in s) f i) = |_| (|_| @` (f @` s))             *)
(*          3. x [+] y = |_| [set x; y]                                       *)
(* {Biglub_morph U -> V} == Homomorphism between semicomplete semilattices    *)
(*                                                                            *)
(* semiLattConvType == semilattice convex space: This structure is a          *)
(*     combination of convex space and semilattice structures with the        *)
(*     distributive law of convex operation over lattice operation. This is   *)
(*     the algebra carried by the interface of combined choice monads, which  *)
(*     is described by MonadAltProb in monae. Although semilattice convex     *)
(*     space is what precisely corresponds to MonadAltProb, we prefer the     *)
(*     easiness of its completion (semicomplete semilattice convex space, the *)
(*     next module after this one) when defining our instance of MonadAltProb *)
(*     in monae (gcm_model.v, altprob_model.v).                               *)
(* semiCompSemiLattConvType == Semicomplete semilattice convex space: a       *)
(*     combination of convex space and semicomplete semilattice structures    *)
(*     with the distributive law of convex operation over lattice operation;  *)
(*     this is the algebra carried by the combined choice monad, which is     *)
(*     described in monae (files gcm_model.v and altprob_model.v),            *)
(*     extends semiCompSemiLattType and convType with the following axiom:    *)
(*          3. x <| p |> |_| I = |_| ((fun y => x <| p |> y) @` I)            *)
(*                                                                            *)
(* {Biglub_affine U -> V} == Homomorphism between semicomplete semilattice    *)
(*                           convex spaces                                    *)
(*                                                                            *)
(* necset T             == the type of non-empty convex sets over T, the      *)
(*                         object part of the third adjunction that appears   *)
(*                         in the definition of the combined choice monad     *)
(* structures on necset:                                                      *)
(* - convex space structure on necset (necset_convType A, instance of         *)
(*   convType) with elements of type necset A and with operator               *)
(*   X <| p |> Y = {x<|p|>y | x \in X, y \in Y}                               *)
(*   Notation: {necset A}                                                     *)
(* - semicomplete semilattice structure on necset, instance of                *)
(*   semiCompSemiLattType with elements of type necset A and with operator    *)
(*   |_| X = hull (bigsetU X idfun)                                           *)
(* - the combined structure on necset, instance of semiCompSemiLattConvType   *)
(*   with elements of type necset A                                           *)
(*                                                                            *)
(* necset_join, necset_bind == elementary definition of the multiplication    *)
(*                             and bind operations of the combined choice     *)
(*                             monad                                          *)
(*                                                                            *)
(* Section technical_corollaries == proofs of some subtle lemmas in the       *)
(*                                  literature                                *)
(******************************************************************************)

Declare Scope latt_scope.

Reserved Notation "x %:ne" (at level 0, format "x %:ne").
Reserved Notation "x <| p |>: Y" (format "x  <| p |>:  Y", at level 49).
Reserved Notation "X :<| p |>: Y" (format "X  :<| p |>:  Y", at level 49).
Reserved Notation "x [+] y" (format "x  [+]  y", at level 50).
Reserved Notation "'|_|' f" (at level 36, f at level 36, format "|_|  f").
Reserved Notation "{ 'necset' T }" (at level 0, format "{ 'necset'  T }").
Reserved Notation "{ 'Biglub_morph' T '->' R }"
  (at level 36, T, R at next level, format "{ 'Biglub_morph'  T  '->'  R }").
Reserved Notation "{ 'Biglub_affine' T '->' R }"
  (at level 36, T, R at next level, format "{ 'Biglub_affine'  T  '->'  R }").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope convex_scope.

HB.mixin Record isNESet (T : Type) (X : set T) := { is_nonempty : X != set0 }.
#[short(type=neset)]
HB.structure Definition NESet T := { X of isNESet T X }.
Notation "s %:ne" := ((s : neset _)%classic). (*(@Pack _ s (class _)).*)

Section neset_canonical.
Variable A : Type.
Canonical neset_predType :=
  Eval hnf in PredType (fun t : neset A => (fun x => x \in (t : set _))).
HB.instance Definition _ := gen_eqMixin (neset A).
HB.instance Definition _ := gen_choiceMixin (neset A).
(*
Canonical neset_eqType := Equality.Pack (Equality.Class (@gen_eqMixin (neset A))).
Canonical neset_choiceType := Choice.Pack (Choice.Class (@choice_of_Type (neset A).
*)
End neset_canonical.

Section NESet_interface.
Variables (A : Type).
Lemma neset_neq0 (a : neset A) : a != set0 :> set _.
Proof. by case: a => [? [[]]]. Qed.
Lemma neset_ext (a b : neset A) : a = b :> set _ -> a = b.
Proof.
move: a b => -[a [[Ha]]] -[b [[Hb]]] /= ?; subst a.
congr NESet.Pack; congr NESet.Class; f_equal; exact/Prop_irrelevance.
Qed.
End NESet_interface.

Section neset_lemmas.
Local Open Scope classical_set_scope.

Lemma set1_neq0 A (a : A) : [set a] != set0.
Proof. by apply/set0P; exists a. Qed.

Definition neset_repr A (X : neset A) : A.
Proof.
case: X => X [[]] /set0P /boolp.constructive_indefinite_description [x _]; exact x.
Defined.

Lemma repr_in_neset A (X : neset A) : (X : set A) (neset_repr X).
Proof. by case: X => X [[]] X0 /=; case: cid. Qed.

Global Opaque neset_repr.
Local Hint Resolve repr_in_neset : core.

Lemma image_const A B (X : neset A) (b : B) : (fun _ => b) @` X = [set b].
Proof.
rewrite eqEsubset; split=> b'; [by case => ? _ -> | by move=> ?; eexists].
Qed.

Lemma neset_bigsetU_neq0 A B (X : neset A) (F : A -> neset B) :
  \bigcup_(i in X) F i != set0.
Proof. by apply/bigcup_set0P; eexists; split => //; eexists. Qed.

Lemma neset_image_neq0 A B (f : A -> B) (X : neset A) : f @` X != set0.
Proof. apply/set0P; eexists; exact/imageP. Qed.

Lemma neset_setU_neq0 A (X Y : neset A) : X `|` Y != set0.
Proof. by apply/set0P; eexists; left. Qed.

(* Canonical neset1 *)
HB.instance Definition neset1 {A} (a : A) := isNESet.Build _ _ (set1_neq0 a).
(* Canonical bignesetU *)
HB.instance Definition _ {A} I (S : neset I) (F : I -> neset A) :=
  isNESet.Build _ _ (neset_bigsetU_neq0 S F).
(* Canonical image_neset *)
HB.instance Definition _ {A B} (f : A -> B) (X : neset A) :=
  isNESet.Build _ _ (neset_image_neq0 f X).
(* Canonical nesetU *)
HB.instance Definition _ {T} (X Y : neset T) :=
  isNESet.Build _ _  (neset_setU_neq0 X Y).

Lemma neset_hull_neq0 {R : realType} (T : convType R) (F : neset T) : hull F != set0.
Proof. by rewrite hull_eq0 neset_neq0. Qed.

(* Canonical neset_hull *)
HB.instance Definition _ {R : realType} (T : convType R) (F : neset T) :=
  isNESet.Build _ _ (neset_hull_neq0 F).

End neset_lemmas.
Local Hint Resolve repr_in_neset : core.
(*Arguments image_neset : simpl never.*)

#[short(type=necset)]
HB.structure Definition NECSet {R : realType} (A : convType R) :=
  {X of @isConvexSet R A X & @isNESet A X}.

Section conv_set_def.
Local Open Scope classical_set_scope.
Context {R : realType}.
Variable L : convType R.
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
Definition conv_pt_set (p : {prob R}) (x : L) (Y : set L) :=
  locked (fun y => x <| p |> y) @` Y.
Local Notation "x <| p |>: Y" := (conv_pt_set p x Y).

Lemma conv_pt_setE p x Y : x <| p |>: Y = (fun y => x <| p |> y) @` Y.
Proof. by rewrite /conv_pt_set; unlock. Qed.

Definition conv_set p (X Y : set L) := \bigcup_(x in X) (x <| p |>: Y).
End conv_set_def.

Notation "x <| p |>: Y" := (conv_pt_set p x Y) : convex_scope.
Notation "X :<| p |>: Y" := (conv_set p X Y) : convex_scope.

Section conv_set_lemmas.
Local Open Scope classical_set_scope.
Context {R : realType}.
Variables A : convType R.

Lemma conv_setE p (X Y : set A) :
  X :<| p |>: Y = \bigcup_(x in X) (x <| p |>: Y).
Proof. by []. Qed.

Lemma conv_in_conv_pt_set p (Y : set A) x y :
  Y y -> (x <| p |>: Y) (x <| p |> y).
Proof. by move=> ?; rewrite conv_pt_setE; exists y. Qed.

Lemma conv_in_conv_set p (X Y : set A) x y :
  X x -> Y y -> (X :<| p |>: Y) (x <| p |> y).
Proof. by move=> *; exists x=> //; rewrite conv_pt_setE; exists y. Qed.

Lemma conv_in_conv_set' p (X Y : set A) u :
 (X :<| p |>: Y) u -> exists x y, X x /\ Y y /\ u = x <| p |> y.
Proof.
by case=> x ?; rewrite conv_pt_setE=> -[] y ? <-; exists x, y.
Qed.

Lemma convC_set p (X Y : set A) : X :<| p |>: Y = Y :<| (Prob.p p).~%:pr |>: X.
Proof.
by rewrite eqEsubset; split=> u; case=> x Xx;
  rewrite conv_pt_setE => -[] y Yy <-;
  exists y => //; rewrite conv_pt_setE; exists x => //; rewrite -convC.
Qed.

Lemma convA_pt_set p q x (Y Z : set A) :
  x <|p|>: (Y :<|q|>: Z) = (x <|[r_of p, q]|>: Y) :<|[s_of p, q]|>: Z.
Proof.
rewrite eqEsubset; split=> u; rewrite conv_pt_setE.
- case=> yz [] y Yy; rewrite conv_pt_setE=> -[] z Zz <- <-.
  by rewrite convA; apply conv_in_conv_set=> //; apply conv_in_conv_pt_set.
- case=> xy [] y Yy <-; rewrite conv_pt_setE; case=> z Zz <-.
  by rewrite -convA; apply conv_in_conv_pt_set=> //; apply conv_in_conv_set.
Qed.

Lemma convA_set p q (X Y Z : set A) :
  X :<|p|>: (Y :<|q|>: Z) = (X :<|[r_of p, q]|>: Y) :<|[s_of p, q]|>: Z.
Proof.
rewrite eqEsubset; split=> u.
- by case=> x Xx; rewrite convA_pt_set=> -[] xy xYxy; exists xy=> //; exists x.
- by case=> xy -[] x Xx xYxy; exists x=> //; rewrite convA_pt_set; exists xy.
Qed.

Lemma conv_cset1 (p : {prob R}) (x y : A) :
  [set x] :<|p|>: [set y] = [set x <|p|> y].
Proof.
rewrite eqEsubset; split=> [u|u ->]; last exact: conv_in_conv_set.
by case/conv_in_conv_set'=> x' [] y' [] -> [] -> ->.
Qed.

Lemma conv1_pt_set x (Y : neset A) : x <| 1%:pr |>: Y = [set x].
Proof.
rewrite eqEsubset;split => u; rewrite conv_pt_setE.
- by case => y _; rewrite conv1.
- by move=> ->; eexists => //; rewrite conv1.
Qed.

Lemma conv0_pt_set x (Y : set A) : x <| 0%:pr |>: Y = Y.
Proof.
rewrite eqEsubset; split => u; rewrite conv_pt_setE.
- by case=> y Yy <-; rewrite conv0.
- by move=> Yu; exists u=> //; rewrite conv0.
Qed.

Lemma conv1_set X (Y : neset A) : X :<| 1%:pr |>: Y = X.
Proof.
transitivity (\bigcup_(x in X) [set x]); last by rewrite bigcup_imset1 image_id.
by apply :eq_bigcupr => x; rewrite conv1_pt_set.
Qed.

Lemma conv0_set (X : neset A) Y : X :<| 0%:pr |>: Y = Y.
Proof.
rewrite convC_set /= (_ : 0.~%:pr = 1%:pr) ?conv1_set //.
by apply val_inj; rewrite /= onem0.
Qed.

Definition probset := @setT {prob R}.

Definition natset := @setT nat.

Definition oplus_conv_set (X Y : set A) :=
  \bigcup_(p in probset) (X :<| p |>: Y).

Lemma conv_in_oplus_conv_set p (X Y : set A) x y :
  X x -> Y y -> (oplus_conv_set X Y) (x <|p|> y).
Proof. by move=> *; exists p=> //; exact: conv_in_conv_set. Qed.

Fixpoint iter_conv_set (X : set A) (n : nat) :=
  match n with
  | O => X
  | S n' => oplus_conv_set X (iter_conv_set X n')
  end.

Lemma iter0_conv_set (X : set A) : iter_conv_set X 0 = X.
Proof. by []. Qed.

Lemma iterS_conv_set (X : set A) (n : nat) :
  iter_conv_set X (S n) = oplus_conv_set X (iter_conv_set X n).
Proof. by []. Qed.

Lemma probset_neq0 : probset != set0.
Proof. by apply/set0P; exists 0%:pr. Qed.

Lemma natset_neq0 : natset != set0.
Proof. by apply/set0P; exists O. Qed.

Lemma conv_pt_set_neq0 p (x : A) (Y : neset A) : x <| p |>: Y != set0.
Proof. exact: neset_image_neq0. Qed.

Lemma conv_set_neq0 p (X Y : neset A) : X :<| p |>: Y != set0.
Proof. by rewrite neset_neq0. Qed.

Lemma oplus_conv_set_neq0 (X Y : neset A) : oplus_conv_set X Y != set0.
Proof. apply/set0P; eexists; exists 1%:pr => //; by rewrite conv1_set. Qed.

Fixpoint iter_conv_set_neq0 (X : neset A) (n : nat) :
  iter_conv_set X n != set0 :=
  if n is n'.+1 then
    oplus_conv_set_neq0 X (NESet.Pack (NESet.Class (isNESet.Build _ _  (iter_conv_set_neq0 X n'))))
  else neset_neq0 X.

(*Canonical probset_neset*)
HB.instance Definition _ := isNESet.Build _ _ probset_neq0.
(*Canonical natset_neset*)
HB.instance Definition _ := isNESet.Build _ _ natset_neq0.
(*Canonical conv_pt_set_neset*)
HB.instance Definition _ (p : {prob R}) (x : A) (Y : neset A) :=
  isNESet.Build _ _ (conv_pt_set_neq0 p x Y).
(*Canonical conv_set_neset*)
HB.instance Definition _ (p : {prob R}) (X Y : neset A) :=
  isNESet.Build _ _ (conv_set_neq0 p X Y).
(*Canonical oplus_conv_set_neset*)
HB.instance Definition _ (X Y : neset A) :=
  isNESet.Build _ _ (oplus_conv_set_neq0 X Y).
(*Canonical iter_conv_set_neset*)
HB.instance Definition _ (X : neset A) (n : nat) :=
  isNESet.Build _ _ (iter_conv_set_neq0 X n).

Let conv_pt_cset_is_convex (p : {prob R}) (x : A) (Y : {convex_set A}) :
  is_convex_set (conv_pt_set p x Y).
Proof.
apply/asboolP=> u v q.
rewrite conv_pt_setE /= => -[y0 Yy0 <-] [y1 Yy1 <-].
rewrite -convDr; apply/imageP.
by move/asboolP: (convex_setP Y); apply.
Qed.

(*Canonical conv_pt_cset*)
HB.instance Definition _ (p : {prob R}) (x : A) (Y : {convex_set A}) :=
  isConvexSet.Build R _ _ (conv_pt_cset_is_convex p x Y).

Lemma conv_cset_is_convex (p : {prob R}) (X Y : {convex_set A}) :
  is_convex_set (conv_set p X Y).
Proof.
apply/asboolP=> u v q.
case/conv_in_conv_set'=> x0 [] y0 [] ? [] ? ->.
case/conv_in_conv_set'=> x1 [] y1 [] ? [] ? ->.
by rewrite convACA; apply/conv_in_conv_set;
 [move/asboolP: (convex_setP X); apply | move/asboolP: (convex_setP Y); apply].
Qed.

HB.instance Definition _ (p : {prob R}) (X Y : {convex_set A}) :=
  isConvexSet.Build R _ _ (conv_cset_is_convex p X Y).

Lemma oplus_conv_cset_is_convex (X Y : {convex_set A}) :
  is_convex_set (oplus_conv_set X Y).
Proof.
apply/asboolP=> u v p.
case=> q _ [] xu Xxu; rewrite conv_pt_setE=> -[] yu Yyu <-.
case=> r _ [] xv Xxv; rewrite conv_pt_setE=> -[] yv Yyv <-.
apply (prob_trichotomy' p); rewrite ?conv0 ?conv1;
  [exact: conv_in_oplus_conv_set | exact: conv_in_oplus_conv_set | move=> op].
apply (prob_trichotomy' q) => [| |oq].
- rewrite conv0 (convC r) convA convC; apply conv_in_oplus_conv_set=> //.
  by move/asboolP: (convex_setP Y); apply.
- rewrite conv1 convA; apply conv_in_oplus_conv_set=> //.
  by move/asboolP: (convex_setP X); apply.
- apply (prob_trichotomy' r) => [| |or].
  + rewrite conv0 -convA' ?oprob_neq1 //; apply conv_in_oplus_conv_set=> //.
    by move/asboolP: (convex_setP Y); apply.
  + rewrite conv1 convC convA; apply conv_in_oplus_conv_set=> //.
    by move/asboolP: (convex_setP X); apply.
  + case: (convACA' xu yu xv yv (OProb.p oq) (OProb.p op) (OProb.p or)(*TODO: oprob coercions broken*))=> q' [] p' [] r' ->.
    by apply conv_in_oplus_conv_set; [move/asboolP: (convex_setP X); apply |
                                      move/asboolP: (convex_setP Y); apply].
Qed.

HB.instance Definition _ (X Y : {convex_set A}) :=
  isConvexSet.Build _ _ _ (oplus_conv_cset_is_convex X Y).

Fixpoint iter_conv_cset_is_convex (X : {convex_set A}) (n : nat) :
  is_convex_set (iter_conv_set X n) :=
  match n with
  | 0 => convex_setP X
  | n'.+1 => oplus_conv_cset_is_convex
               X (ConvexSet.Pack
                    (ConvexSet.Class
                       (isConvexSet.Build R _ _ (iter_conv_cset_is_convex X n'))))
  end.

HB.instance Definition _ (X : {convex_set A}) (n : nat) :=
  isConvexSet.Build R _ _ (iter_conv_cset_is_convex X n).

Lemma conv_pt_set_monotone (p : {prob R}) (x : A) (Y Y' : set A) :
  Y `<=` Y' -> x <| p |>: Y `<=` x <| p |>: Y'.
Proof. by move=> YY' u [] y /YY' Y'y <-; exists y. Qed.

Lemma conv_set_monotone (p : {prob R}) (X Y Y' : set A) :
  Y `<=` Y' -> X :<| p |>: Y `<=` X :<| p |>: Y'.
Proof. by move/conv_pt_set_monotone=> YY' u [] x Xx /YY' HY'; exists x. Qed.

Lemma oplus_conv_set_monotone (X Y Y' : set A) :
  Y `<=` Y' -> oplus_conv_set X Y `<=` oplus_conv_set X Y'.
Proof. by move/conv_set_monotone=> YY' u [] p _ /YY' HY'; exists p. Qed.

Lemma iter_monotone_conv_set (X : neset A) (m : nat) :
  forall n, (m <= n)%N -> iter_conv_set X m `<=` iter_conv_set X n.
Proof.
elim: m => [n _|m IHm].
- case: n => // n.
  rewrite iter0_conv_set iterS_conv_set.
  by exists 1%:pr => //; rewrite conv1_set.
- case => // n /(IHm _) mn.
  rewrite iterS_conv_set=> a [] p _ H.
  exists p => //.
  by move: (@conv_set_monotone p X _ _ mn) => /(_ a); apply.
Qed.

Lemma iter_bigcup_conv_set (X : neset A) (n : nat) :
  iter_conv_set X n `<=` \bigcup_(i in natset) iter_conv_set X i.
Proof. by move=> a H; exists n. Qed.

Lemma iter_conv_set_superset (X : neset A) n : X `<=` iter_conv_set X n .
Proof.
move=> x Xx; elim: n => // n IHn; rewrite iterS_conv_set.
by exists 1%:pr => //; rewrite conv1_set.
Qed.

Lemma Convn_iter_conv_set (n : nat) :
  forall (g : 'I_n -> A) (d : R.-fdist 'I_n) (X : set A),
    g @` setT `<=` X -> iter_conv_set X n (<|>_d g).
Proof.
elim: n => [g d|n IHn g d X]; first by have := fdistI0_False d.
have [->|Xneq0 gX] := eqVneq X set0.
  by move=> /(_ (g ord0)) H; exfalso; apply/H/imageP.
set X' := NESet.Pack (NESet.Class (isNESet.Build _ _ Xneq0)).
have gXi : forall i : 'I_n.+1, X (g i).
  by move=> i; move/subset_image : gX; apply.
have [d01|d0n1] := eqVneq (d ord0) 1%R.
- suff : X (<|>_d g) by move/(@iter_conv_set_superset X' n.+1 (<|>_d g)).
  by rewrite (Convn_proj g d01); exact/gX/imageP.
- rewrite ConvnIE //; exists (probfdist d ord0) => //; exists (g ord0) => //.
  rewrite conv_pt_setE.
  exists (<|>_(fdist_del d0n1) (fun x : 'I_n => g (fdist_del_idx ord0 x))) => //.
  by apply IHn => u [] i _ <-; exact/gX/imageP.
Qed.

Lemma oplus_convC_set (X Y : set A) : oplus_conv_set X Y = oplus_conv_set Y X.
Proof.
suff H : forall X' Y', oplus_conv_set X' Y' `<=` oplus_conv_set Y' X'
  by rewrite eqEsubset; split => // /H.
by move=> {X} {Y} X Y u [] p _; rewrite convC_set => H; exists (Prob.p p).~%:pr.
Qed.

Lemma convmm_cset (p : {prob R}) (X : {convex_set A}) : X :<| p |>: X = X.
Proof.
rewrite eqEsubset; split=> [x /conv_in_conv_set'[] | x ?].
- by move=> x0 [] x1 [] ? [] ? ->; move/asboolP : (convex_setP X); apply.
- by rewrite -(convmm p x); apply conv_in_conv_set.
Qed.

Lemma oplus_convmm_cset (X : {convex_set A}) : oplus_conv_set X X = X.
Proof.
rewrite eqEsubset; split => [x [p _]|x Xx].
- by rewrite convmm_cset.
- by exists 0%:pr => //; rewrite convmm_cset.
Qed.

Lemma oplus_convmm_set_hull (X : set A) :
  oplus_conv_set (hull X) (hull X) = hull X.
Proof. by rewrite oplus_convmm_cset. Qed.

Lemma hull_iter_conv_set (X : set A) :
  hull X = \bigcup_(i in natset) iter_conv_set X i.
Proof.
rewrite eqEsubset; split.
  by move=> x [] n [] g [] d [] gX ->; exists n => //; apply Convn_iter_conv_set.
apply bigsubsetU.
elim => [_|n IHn _]; first exact/subset_hull.
have H : iter_conv_set X n.+1 `<=` oplus_conv_set X (hull X).
  exact/oplus_conv_set_monotone/IHn.
apply (subset_trans H); rewrite oplus_convC_set.
have : oplus_conv_set (hull X) X `<=` oplus_conv_set (hull X) (hull X).
  exact/oplus_conv_set_monotone/subset_hull.
by move/subset_trans; apply; rewrite oplus_convmm_set_hull.
Qed.

(* tensorial strength for hull and conv_set *)
Lemma hull_conv_set_strr (p : {prob R}) (X Y : set A) :
  hull (X :<| p |>: hull Y) = hull (X :<| p |>: Y).
Proof.
apply: hull_eqEsubset => u.
- case=> x Xx; rewrite conv_pt_setE=> -[] y [] n [] g [] d [] gY yg <-.
  exists n, (fun i => x <|p|> g i), d; rewrite -ConvnDr yg; split=> //.
  by move=> v [] i _ <-; exists x=> //; apply/conv_in_conv_pt_set/gY/imageP.
- case=> x Xx [] y Yy <-; apply/subset_hull.
  by exists x=> //; exists y=> //; exact/subset_hull.
Qed.

End conv_set_lemmas.

Lemma affine_image_conv_set {R : realType} (A B : convType R)
    (f : {affine A -> B}) p (X Y : set A) :
  (f @` (X :<| p |>: Y) = f @` X :<| p |>: f @` Y)%classic.
Proof.
rewrite eqEsubset; split=> [u [v]|u].
- move=> /conv_in_conv_set' [] x [] y [] Xx [] Yy ->; rewrite affine_conv=> <-.
  by apply conv_in_conv_set; apply imageP.
- case/conv_in_conv_set'=> x [] y [] [] x0 Xx0 <- [] [] y0 Yy0 <- ->.
  by rewrite -affine_conv; apply/imageP/conv_in_conv_set.
Qed.

(* (saikawa) I am aware that ssreflect/order.v has definitions of porder and
   lattice. For now, I write down the following definition of semilattice
   independently of the two, as it seems hard to insert a new layer in the
   mathcomp hierarchy. *)
HB.mixin Record isSemiLattice (T : Type) of Choice T := {
  lub : T -> T -> T ;
  lubC : commutative lub;
  lubA : associative lub;
  lubxx : idempotent_op lub }.

#[short(type=semiLattType)]
HB.structure Definition SemiLattice := { T of isSemiLattice T & }.

Notation "x [+] y" := (lub x y) : latt_scope.

Local Open Scope latt_scope.

Section semilattice_lemmas.
Variable L : semiLattType.
Local Notation lub := (@lub L).

Lemma lubAC : right_commutative lub.
Proof. by move=> x y z; rewrite -!lubA [X in _ [+] X]lubC. Qed.

Lemma lubCA : left_commutative lub.
Proof. by move=> x y z; rewrite !lubA [X in X [+] _]lubC. Qed.

Lemma lubACA : interchange lub lub.
Proof. by move=> x y z t; rewrite !lubA [X in X [+] _]lubAC. Qed.

Lemma lubKU (y x : L) : x [+] (x [+] y) = x [+] y.
Proof. by rewrite lubA lubxx. Qed.

Lemma lubUK (y x : L) : (x [+] y) [+] y = x [+] y.
Proof. by rewrite -lubA lubxx. Qed.

Lemma lubKUC (y x : L) : x [+] (y [+] x) = x [+] y.
Proof. by rewrite lubC lubUK lubC. Qed.

Lemma lubUKC (y x : L) : y [+] x [+] y = x [+] y.
Proof. by rewrite lubAC lubC lubxx. Qed.

End semilattice_lemmas.

HB.mixin Record isSemiCompSemiLatt T of isSemiLattice T & Choice T := {
  biglub : neset T -> T ;
  (* [Reiterman] p.326, axiom 3 *)
  biglub1 : forall x : T, biglub [set x]%:ne = x ;
  biglub_bignesetU : forall I (s : neset I) (f : I -> neset T),
    biglub (\bigcup_(i in s) f i)%:ne = biglub (biglub @` (f @` s))%:ne ;
  lubE : forall x y, x [+] y = biglub [set x; y]%:ne }.

#[short(type=semiCompSemiLattType)]
HB.structure Definition SemiCompSemiLatt := { T of @isSemiCompSemiLatt T & }.

Notation "|_| f" := (biglub f) : latt_scope.
Local Open Scope latt_scope.

Section semicompsemilatt_lemmas.
Local Open Scope classical_set_scope.
Variable L : semiCompSemiLattType.

(*
[Reiterman]
- Commentationes Mathematicae Universitatis Carolinae
- Jan Reiterman
- On locally small based algebraic theories
- https://dml.cz/bitstream/handle/10338.dmlcz/106455/CommentatMathUnivCarol_027-1986-2_12.pdf
*)

(* NB: bigsetU (bigsetI too) is the bind operator for the powerset monad *)

Lemma biglub_bigcup (I : Type) (S : neset I) (F : I -> neset L) :
  |_| (\bigcup_(i in S) F i)%:ne = |_| (biglub @` (F @` S))%:ne.
Proof. by rewrite biglub_bignesetU. Qed.

Lemma nesetU_bigcup T (I J : neset T) :
  (I `|` J)%:ne = (\bigcup_(i in [set I; J]) idfun i)%:ne.
Proof.
apply/neset_ext => /=; rewrite eqEsubset; split => x.
  by case=> Hx; [exists I => //; left | exists J => //; right].
by case=> K [] -> Hx; [left | right].
Qed.

Lemma biglub_setU (I J : neset L) :
  |_| (I `|` J)%:ne = |_| [set |_| I; |_| J]%:ne.
Proof.
rewrite nesetU_bigcup biglub_bignesetU; congr (|_| _%:ne); apply/neset_ext => /=.
by rewrite image_id /= image_setU !image_set1.
Qed.

(* NB: [Reiterman] p.326, axiom 1 is trivial, since our |_| operator receives
   a set but not a sequence. *)

(* [Reiterman] p.326, axiom 2 *)
Lemma biglub_flatten (F : neset (neset L)) :
  |_| (biglub @` F)%:ne = |_| (\bigcup_(i in F) idfun i)%:ne.
Proof.
rewrite biglub_bignesetU; congr (|_| _%:ne); apply/neset_ext => /=.
by rewrite image_id.
Qed.

Let lub_binary (x y : L) := |_| [set x; y]%:ne.

Let lub_binaryC : commutative lub_binary.
Proof. by move=> x y; rewrite /lub_binary -!lubE lubC. Qed.

Let lub_binaryA : associative lub_binary.
Proof. by move=> x y z; rewrite /lub_binary -!lubE lubA. Qed.

Let lub_binaryxx : idempotent_op lub_binary.
Proof. by move=> x; rewrite /lub_binary -lubE lubxx. Qed.

End semicompsemilatt_lemmas.

Definition biglubmorph (U V : semiCompSemiLattType) (f : U -> V) :=
  forall (X : neset U), f (|_| X) = |_| (f @` X)%:ne.

HB.mixin Record isBiglubMorph (U V : semiCompSemiLattType) (f : U -> V) := {
  biglub_morph : biglubmorph f }.

HB.structure Definition BiglubMorph (U V : semiCompSemiLattType) :=
  {f of isBiglubMorph U V f}.

Notation "{ 'Biglub_morph' T '->' R }" := (BiglubMorph.type T R) : convex_scope.

Section biglub_morph.
Variables (L M : semiCompSemiLattType).

Local Open Scope classical_set_scope.
Local Open Scope latt_scope.

Definition lub_morph (f : L -> M) :=
  forall (x y : L), f (x [+] y) = f x [+] f y.

Lemma biglub_lub_morph (f : {Biglub_morph L -> M}) : lub_morph f.
Proof.
move=> x y; rewrite !lubE biglub_morph.
congr (|_| _%:ne); apply/neset_ext => /=.
by rewrite image_setU !image_set1.
Qed.

End biglub_morph.

Local Open Scope convex_scope.
Local Open Scope latt_scope.
Local Open Scope classical_set_scope.

HB.mixin Record isSemiLattConv {R : realType} L of ConvexSpace R L & SemiLattice L := {
  lubDr : forall (p : {prob R}) (x y z : L),
    conv p x (y [+] z) = (conv p x y) [+] (conv p x z) }.

#[short(type=semiLattConvType)]
HB.structure Definition SemiLattConv {R : realType} :=
  {L of isSemiLattConv R L & ConvexSpace R L & SemiLattice L}.

(* Homomorphism between semilattice convex spaces *)
(* TODO: define LubAffine for semiLattConvType *)

Section semilattconvtype_lemmas.
Local Open Scope latt_scope.
Local Open Scope convex_scope.
Context {R : realType}.

Variable L : semiLattConvType R.

Lemma lubDl p : left_distributive (fun x y => x <|p|> y) (@lub L).
Proof. by move=> x y z; rewrite convC lubDr -(convC _ x z) -(convC _ y z). Qed.

(*
  The proof of the next lemma is essentially based on the canonical order
  structure induced by semilattice structure: x <= y is defined to be
  x [+] y = y.
  Immediately from the definition,
    x [+] y  <=  x [+] y [+] x <|p|> y and
    x [+] y [+] x <|p|> y  <=  x [+] y [+] x <|p|> y [+] y <|p|> x holds.
  Now that x [+] y [+] x <|p|> y [+] y <|p|> x can be rewritten into x [+] y
  by distributivity, we can conclude x [+] y = x [+] y [+] x <|p|> y by
  antisymmmetry. This proof might be a motivation to base our semilattice over
  ssreflect.order.POrder.
 *)
Lemma lub_absorbs_conv (x y : L) p : x [+] y = x [+] y [+] x <|p|> y.
Proof.
have H : x [+] y = (x [+] y [+] x <|p|> y) [+] y <|p|> x.
  rewrite -[in LHS](convmm p (x [+] y)) lubDl 2!lubDr 2!convmm lubCA lubC.
  by rewrite (lubAC x).
rewrite {1}H.
have {2}<- : x [+] y [+] (x [+] y [+] x <|p|> y) = x [+] y [+] x <|p|> y
   by rewrite lubA lubxx.
rewrite [in RHS]lubC.
have <- : x [+] y [+] x <|p|> y [+] (x [+] y [+] x <|p|> y [+] y <|p|> x) =
    x [+] y [+] x <|p|> y [+] y <|p|> x
  by rewrite lubA lubxx.
by rewrite -H.
Qed.

(* The next lemma corresponds to biglub_hull.
   In order to type check its statement,
   we need some bigop-like machinery for semilattice,
   which is unfortunately only a semigroup and not a monoid *)
Local Notation "\lub_ ( i < n ) F" := False
         (at level 41, F at level 41, i, n at level 50,
          format "'[' \lub_ ( i  <  n ) '/  '  F ']'").
Fail Lemma lub_absorbs_convn (n : nat) (d : {fdist 'I_n}) (f : 'I_n -> L) :
  \lub_(i < n) f i = (\lub_(i < n) f i) [+] (<|>_d f).
End semilattconvtype_lemmas.

HB.mixin Record isSemiCompSemiLattConv {R : realType} L of SemiCompSemiLatt L &
                                            ConvexSpace R L := {
  biglubDr : forall (p : {prob R}) (x : L) (I : neset L),
    conv p x (|_| I) = |_| ((conv p x) @` I)%:ne
}.

#[short(type=semiCompSemiLattConvType)]
HB.structure Definition SemiCompSemiLattConv {R : realType} :=
  { L of isSemiCompSemiLattConv R L & SemiCompSemiLatt L & ConvexSpace R L &
         isSemiLattConv R L}.

HB.structure Definition BiglubAffine {R : realType} (U V : semiCompSemiLattConvType R) :=
  {f of @isAffine R U V f & isBiglubMorph U V f}.

Notation "{ 'Biglub_affine'  T '->'  R }" :=
  (BiglubAffine.type T R) : convex_scope.

Section biglub_affine_functor_laws.

Variables (R' : realType) (R S T : semiCompSemiLattConvType R')
  (f : {Biglub_affine S -> T}) (g : {Biglub_affine R -> S}).

Let biglubmorph_idfun : biglubmorph (@idfun R).
Proof.
by move=> x; congr (|_| _); apply neset_ext; rewrite /= image_id.
Qed.

HB.instance Definition _ := isBiglubMorph.Build _ _ _ biglubmorph_idfun.

Let biglubmorph_comp : biglubmorph (f \o g).
Proof.
move=> x; cbn; rewrite !biglub_morph.
by congr (|_| _); apply neset_ext => /=; rewrite image_comp.
Qed.

HB.instance Definition _ := isBiglubMorph.Build _ _ _ biglubmorph_comp.

End biglub_affine_functor_laws.

Section semicompsemilattconvtype_lemmas.
Local Open Scope latt_scope.
Local Open Scope convex_scope.
Local Open Scope classical_set_scope.
Context {R : realType}.

Variable L : semiCompSemiLattConvType R.

Lemma biglubDl (p : {prob R}) (X : neset L) (y : L) :
  |_| X <|p|> y = |_| ((fun x => x <|p|> y) @` X)%:ne.
Proof.
rewrite convC biglubDr; congr (|_| _); apply/neset_ext/eq_imagel=> x ?.
by rewrite -convC.
Qed.

Lemma biglub_conv_pt_setE p x (Y : neset L) :
  |_| (x <| p |>: Y)%:ne = |_| ((conv p x) @` Y)%:ne.
Proof.
by congr (|_| _%:ne); apply/neset_ext => /=; rewrite conv_pt_setE.
Qed.

Lemma biglub_conv_pt_setD p x (Y : neset L) :
  |_| (x <| p |>: Y)%:ne = x <|p|> |_| Y.
Proof. by rewrite biglub_conv_pt_setE -biglubDr. Qed.

Lemma biglub_conv_setE p (X Y : neset L) :
  |_| (X :<| p |>: Y)%:ne = |_| ((fun x => x <|p|> |_| Y) @` X)%:ne.
Proof.
transitivity (|_| (\bigcup_(x in X) (x <| p |>: Y))%:ne).
  by congr (|_| _%:ne); apply neset_ext.
rewrite biglub_bigcup //; congr (|_| _%:ne); apply neset_ext => /=.
rewrite image_comp; congr image; apply funext => x /=.
by rewrite biglub_conv_pt_setD.
Qed.

Lemma biglub_conv_setD p (X Y : neset L) :
  |_| (X :<| p |>: Y)%:ne = |_| X <|p|> |_| Y.
Proof. by rewrite biglub_conv_setE biglubDl. Qed.

Lemma biglub_oplus_conv_setE (X Y : neset L) :
  |_| (oplus_conv_set X Y)%:ne =
  |_| ((fun p => |_| X <|p|> |_| Y) @` probset)%:ne.
Proof.
transitivity (|_| (\bigcup_(p in probset) (X :<| p |>: Y))%:ne).
  by congr (|_| _%:ne); apply/neset_ext.
rewrite biglub_bigcup //; congr (|_| _%:ne); apply/neset_ext => /=.
rewrite image_comp; congr image; apply funext => p /=.
by rewrite biglub_conv_setD.
Qed.

Lemma biglub_iter_conv_set (X : neset L) (n : nat) :
  |_| (iter_conv_set X n)%:ne = |_| X.
Proof.
elim: n => [|n IHn /=]; first by congr (|_| _); apply/neset_ext.
rewrite (biglub_oplus_conv_setE _ (iter_conv_set X n)%:ne).
transitivity (|_| [set |_| X]%:ne); last by rewrite biglub1.
congr (|_| _%:ne); apply/neset_ext => /=.
transitivity ((fun _ => |_| X) @` @probset R); last by rewrite image_const.
by congr image; apply funext=> p; rewrite IHn convmm.
Qed.

Lemma biglub_hull (X : neset L) : |_| (hull X)%:ne = |_| X.
Proof.
transitivity (|_| (\bigcup_(i in natset) iter_conv_set X i)%:ne);
  first by congr (|_| _); apply neset_ext; rewrite /= hull_iter_conv_set.
rewrite biglub_bignesetU /= -[in RHS](biglub1 (|_| X)).
transitivity (|_| ((fun _ => |_| X) @` natset)%:ne); last first.
  by congr (|_| _); apply/neset_ext/image_const.
congr (|_| _%:ne); apply/neset_ext => /=.
rewrite image_comp; congr image; apply funext => n /=.
by rewrite biglub_iter_conv_set.
Qed.

Let lubDr p : right_distributive (fun x y => x <|p|> y) (@lub L).
Proof.
move=> x y z; rewrite !lubE biglubDr.
congr (|_| _%:ne); apply/neset_ext => /=.
by rewrite image_setU !image_set1.
Qed.

(* NB: was in the doc before *)
(* biglubDr_semiLattConvType == Semicomplete semilattice convex space is a    *)
(*                              semilattice convex space                      *)
(* NB: not needed?
HB.instance Definition _ (*biglubDr_semiLattConvType*) := @isSemiLattConv.Build
  L lubDr.
*)

End semicompsemilattconvtype_lemmas.

Section necset_canonical.
Context {R : realType}.
Variable (A : convType R).
Canonical necset_predType :=
  Eval hnf in PredType (fun t : necset A => (fun x => x \in (t : set _))).
HB.instance Definition _ := gen_eqMixin (necset A).
HB.instance Definition _ := gen_choiceMixin (necset A).
End necset_canonical.

Section necset_lemmas.
Context {R : realType}.
Variable A : convType R.

Lemma necset_ext (a b : necset A) : a = b :> set _ -> a = b.
Proof.
move: a b => -[a [[?] [?]]] -[b [[?] [?]]] /= ?; subst a.
congr NECSet.Pack; congr NECSet.Class; f_equal; exact/Prop_irrelevance.
Qed.

(*Canonical neset_hull_necset*)
HB.instance Definition _ (T : convType R) (F : neset T) :=
  isConvexSet.Build R _ _ (hull_is_convex F).
HB.instance Definition _ (T : convType R) (F : neset T) :=
  isNESet.Build _ _ (neset_hull_neq0 F).

(*Canonical necset1*)
HB.instance Definition _ (T : convType R) (x : T) :=
  isConvexSet.Build R _ _ (is_convex_set1 x).
HB.instance Definition _ (T : convType R) (x : T) :=
  isNESet.Build _ _ (set1_neq0 x).
End necset_lemmas.

Definition necset_convType_conv {R : realType} {A : convType R} p (X Y : necset A) :=
  X :<|p|>: Y.

HB.instance Definition _ {R : realType} {A : convType R} p (X Y : necset A) :=
  NESet.on (necset_convType_conv p X Y).

HB.instance Definition _ {R : realType} {A : convType R} p (X Y : necset A) :=
  ConvexSet.on (necset_convType_conv p X Y).

HB.instance Definition _ {R : realType} {A : convType R} (p : {prob R}) (X Y : necset A) :=
  isNESet.Build _ _ (conv_set_neq0 p X Y).

Module necset_convType.
Section def.
Context {R : realType}.
Variable A : convType R.

Definition conv p (X Y : necset A) : necset A := X :<|p|>: Y.

(*locked
  (NECSet.Pack (NECSet.Class (isConvexSet.Build _ _ (conv_cset_is_convex p X Y))
                             (isNESet.Build _ _ (conv_set_neq0 p X Y)))).*)

Lemma convE p (X Y : necset A) : conv p X Y = conv_set p X Y :> set A.
Proof. by rewrite /conv; unlock. Qed.

Lemma conv1 X Y : conv 1%R%:pr X Y = X.
Proof. by apply necset_ext; rewrite convE conv1_set. Qed.

Lemma convmm p X : conv p X X = X.
Proof. by apply necset_ext; rewrite convE convmm_cset. Qed.

Lemma convC p X Y : conv p X Y = conv (Prob.p p).~%:pr Y X.
Proof. by apply necset_ext; rewrite !convE convC_set. Qed.

Lemma convA p q X Y Z :
  conv p X (conv q Y Z) = conv [s_of p, q] (conv [r_of p, q] X Y) Z.
Proof. by apply: necset_ext; rewrite 2!convE convA_set. Qed.

End def.

Section lemmas.
Local Open Scope classical_set_scope.
Context {R : realType}.
Variable A : convType R.

(* This lemma is now trivial since we redefined conv directly by conv_set;
   now kept just for compatibility. *)
Lemma conv_conv_set p X Y : conv p X Y = X :<| p |>: Y :> set A.
Proof. by rewrite convE. Qed.

End lemmas.
End necset_convType.

HB.instance Definition necset_convType {R : realType} (A : convType R) :=
  @isConvexSpace.Build R (necset A)
                       (@necset_convType.conv R A)
                       (@necset_convType.conv1 R A)
                       (@necset_convType.convmm R A)
                       (@necset_convType.convC R A)
                       (@necset_convType.convA R A).

Definition Necset_to_convType {R : realType} (A : convType R) :=
  fun phT : phant (Choice.sort A) => necset A.
Local Notation "{ 'necset' T }" := (Necset_to_convType (Phant T)).

Module necset_semiCompSemiLattType.
Section def.
Local Open Scope classical_set_scope.
Context {R : realType}.
Variable (A : convType R).

Definition pre_op (X : neset {necset A}) : {convex_set A} :=
  hull (\bigcup_(i in X) idfun i)%:ne.

Lemma pre_op_neq0 X : pre_op X != set0 :> set _.
Proof. by rewrite hull_eq0 neset_neq0. Qed.

Definition biglub_necset (X : neset (necset A)) : necset A :=
  hull (\bigcup_(i in X) idfun i)%:ne.

Lemma biglub_necset1 x : biglub_necset [set x]%:ne = x.
Proof. by apply: necset_ext => /=; rewrite bigcup_set1 hull_cset. Qed.

Lemma biglub_necset_bigsetU (I : Type) (S : neset I) (F : I -> neset (necset A)) :
  biglub_necset (\bigcup_(i in S) F i) = biglub_necset (biglub_necset @` (F @` S))%:ne.
Proof.
apply necset_ext => /=.
apply: hull_eqEsubset => a.
- case => x [] i Si Fix xa.
  exists 1, (fun _ => a), (fdist1 ord0).
  split; last by rewrite ConvnI1E.
  move=> a0 [] zero _ <-.
  exists (biglub_necset (F i)); first by do 2 apply imageP.
  by apply/subset_hull; exists x.
- case => x [] u [] i Si Fiu <-.
  case => n [] g [] d [] /= gx ag.
  exists n, g, d; split => //.
  apply: (subset_trans gx).
  move => a0 [] x0 ux0 x0a0.
  exists x0 => //; exists i => //.
  by rewrite Fiu.
Qed.

Let lub_ (x y : necset A) : necset A := biglub_necset [set x; y]%:ne.

Let lub_E (x y : necset A) : lub_ x y = hull (x `|` y)%:ne.
Proof. by apply necset_ext; rewrite /= bigcup_setU !bigcup_set1. Qed.

Let lub_C : commutative lub_.
Proof.
by move=> x y; congr biglub_necset; apply neset_ext; rewrite /= setUC.
Qed.

Let lub_A : associative lub_.
Proof.
by move=> x y z; rewrite !lub_E; apply necset_ext => /=; exact: hullUA.
Qed.

Let lub_xx : idempotent_op lub_.
Proof.
by move=> x; rewrite lub_E; apply necset_ext => /=; rewrite setUid hull_cset.
Qed.

#[export]
HB.instance Definition _ := @isSemiLattice.Build (necset A)
  lub_ lub_C lub_A lub_xx.

Let lub_E' : forall x y, lub_ x y = biglub_necset [set x; y]%:ne.
Proof. by []. Qed.

#[export]
HB.instance Definition _ (*necset_semiCompSemiLattType*) :=
  @isSemiCompSemiLatt.Build (necset A)
    biglub_necset biglub_necset1 biglub_necset_bigsetU lub_E'.

End def.
End necset_semiCompSemiLattType.

HB.export necset_semiCompSemiLattType.

Module necset_semiCompSemiLattConvType.
Section def.
Context {R : realType}.
Variable A : convType R.
Let L := necset A.

Let biglubDr' (p : {prob R}) (X : L) (I : neset L) :
  necset_convType.conv p X (|_| I) = |_| ((necset_convType.conv p X) @` I)%:ne.
Proof.
apply necset_ext => /=.
rewrite -[LHS]hull_cset/=.
rewrite [X in hull X = _]necset_convType.conv_conv_set /=.
rewrite hull_conv_set_strr.
congr hull; rewrite eqEsubset; split=> u /=.
- case=> x Xx [] y []Y IY Yy <-.
  exists (necset_convType.conv p X Y); first by exists Y.
  rewrite necset_convType.conv_conv_set.
  by exists x=> //; exists y.
- case=> _ [] Y IY <-; rewrite necset_convType.convE.
  rewrite convC_set [in X in _ -> X]convC_set.
  by case=> y Yy yXu; exists y=> //; exists Y.
Qed.

Let lubDr' (p : {prob R}) (x y z : L) :
  x <|p|> (y [+] z) = (x <|p|> y) [+] (x <|p|> z).
Proof.
rewrite /conv /=; rewrite lubE biglubDr' lubE; congr (|_| _).
by apply/neset_ext => /=; rewrite image_setU !image_set1.
Qed.

#[export]
HB.instance Definition _ := @isSemiLattConv.Build R (necset A) lubDr'.

#[export]
HB.instance Definition _ := @isSemiCompSemiLattConv.Build R (necset A) biglubDr'.
End def.

End necset_semiCompSemiLattConvType.
HB.export necset_semiCompSemiLattConvType.

Definition Necset_to_semiCompSemiLattConvType {R : realType} (A : convType R) :=
  fun phT : phant (Choice.sort A) => [the semiCompSemiLattConvType R of necset A].
Notation "{ 'necset' T }" :=
  (Necset_to_semiCompSemiLattConvType (Phant T)) : convex_scope.

Module necset_join.
Section def.
Variable R : realType.
Local Open Scope classical_set_scope.
Local Open Scope proba_scope.
Definition F (T : Type) := {necset (R.-dist {classic T})}.
Variable T : Type.

Definition L := [the convType R of F T].

Definition FFT := F (F T).

Definition F1join0' (X : FFT) : set L := (@Convn_of_fsdist R L) @` X.

Lemma F1join0'_convex X : is_convex_set (F1join0' X).
Proof.
apply/asboolP=> x y p [] dx Xdx <-{x} [] dy Xdy <-{y}.
exists (dx <|p|>dy); first by move/asboolP: (convex_setP X); apply.
by rewrite Convn_of_fsdist_affine.
Qed.

Lemma F1join0'_neq0 X : (F1join0' X) != set0.
Proof.
apply/set0P.
case/set0P: (neset_neq0 X) => x Xx.
by exists (Convn_of_fsdist (x : R.-dist (F T))), x.
Qed.

Definition L' := necset L.

Definition F1join0 : FFT -> L' := fun X => NECSet.Pack (NECSet.Class
  (isConvexSet.Build R _ _ (F1join0'_convex X)) (isNESet.Build _ _ (F1join0'_neq0 X))).

Definition join1' (X : L')
    : {convex_set [the convType R of R.-dist {classic T}]} :=
  ConvexSet.Pack (ConvexSet.Class (isConvexSet.Build R _ _ (hull_is_convex
    (\bigcup_(i in X) if i \in X then (i : set _) else set0)))).

Lemma join1'_neq0 (X : L') : join1' X != set0 :> set _.
Proof.
rewrite hull_eq0 set0P.
case/set0P: (neset_neq0 X) => y.
case/set0P: (neset_neq0 y) => x yx sy.
exists x; exists y => //.
rewrite -in_setE in sy.
by rewrite sy.
Qed.

Definition join1 : L' -> L := fun X =>
  NECSet.Pack (NECSet.Class (isConvexSet.Build R _ _ (hull_is_convex _))
                            (isNESet.Build _ _ (join1'_neq0 X))).
Definition join : FFT -> L := join1 \o F1join0.
End def.
Module Exports.
Definition necset_join := Eval hnf in join.
End Exports.
End necset_join.
Export necset_join.Exports.

Section necset_bind.
Local Open Scope classical_set_scope.
Local Open Scope proba_scope.
Local Notation M := (necset_join.F).

Section ret.
Variable R : realType.
Variable a : Type.
Definition necset_ret (x : a) : M R a := [set (fsdist1 (x : {classic a}))].
End ret.

Section fmap.
Variables (R : realType) (a b : Type) (f : a -> b).

Let necset_fmap' (ma : M R a) :=
  (fsdistmap (f : {classic_ a} -> {classic b})) @` ma.

Lemma necset_fmap'_convex ma : is_convex_set (necset_fmap' ma).
Proof.
apply/asboolP=> x y p [] dx madx <-{x} [] dy mady <-{y}.
exists (dx <| p |> dy); last by rewrite affine_conv.
by move/asboolP: (convex_setP ma); apply.
Qed.

Lemma necset_fmap'_neq0 ma : (necset_fmap' ma) != set0.
Proof.
case/set0P : (neset_neq0 ma) => x max; apply/set0P.
by exists (fsdistmap (f : {classic a} -> {classic b}) x), x.
Qed.

Definition necset_fmap : M R a -> M R b := fun ma =>
  NECSet.Pack (NECSet.Class (isConvexSet.Build R _ _ (necset_fmap'_convex ma))
                            (isNESet.Build _ _ (necset_fmap'_neq0 ma))).
End fmap.

Section bind.
Variables (R : realType) (a b : Type).
Definition necset_bind (ma : M R a) (f : a -> M R b) : M R b :=
  necset_join (necset_fmap f ma).
End bind.
End necset_bind.

Section technical_corollaries.
Variable R : realType.
Variable L : semiCompSemiLattConvType R.

Corollary Varacca_Winskel_Lemma_5_6 (Y Z : neset L) :
  hull Y = hull Z -> |_| Y = |_| Z.
Proof.
move=> H; rewrite -[in LHS]biglub_hull -[in RHS]biglub_hull.
by congr (|_| _); apply neset_ext.
Qed.

Corollary Beaulieu_technical_equality (x y : L):
  x [+] y = |_| ((fun p => x <| p |> y) @` probset)%:ne.
Proof.
rewrite lubE -[in LHS]biglub_hull; congr (|_| _); apply neset_ext => /=.
rewrite eqEsubset; split=> i /=.
- have /set0P x0 := set1_neq0 x.
  have /set0P y0 := set1_neq0 y.
  move/(@hull_setU R _ _ (set1 x) (set1 y) x0 y0).
  by move=> [a /asboolP ->] [b /asboolP ->] [p ->]; exists p.
- by case=> p ? <-; exact/mem_hull_setU.
Qed.

End technical_corollaries.
