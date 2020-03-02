Require Import Reals.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import finmap.
Require Import Reals_ext classical_sets_ext Rbigop ssrR fdist fsdist.
Require Import convex_choice.

(******************************************************************************)
(*       Semi-complete semilattice structures and non-empty convex sets       *)
(*                                                                            *)
(* neset T              == the type of non-empty sets over T                  *)
(* x%:ne                == try to infer whether x : set T is neset T          *)
(* x <| p |>: Y         == (fun y => x <| p |> y) @` Y                        *)
(* X :<| p |>: Y        == \bigcup_(x in X) (x <| p |>: Y)                    *)
(*                                                                            *)
(* semiCompSemiLattType == the type of semi-complete semi-lattice provides    *)
(*                         an operator |_| : neset T -> T with the following  *)
(*                         axioms:                                            *)
(*          1. |_| [set x] = x                                                *)
(*          2. |_| (\bigcup_(i in s) f i) = |_| (|_| @` (f @` s))             *)
(*                                                                            *)
(* semiCompSemiLattConvType == extends semiCompSemiLattType and convType with *)
(*                         the following axiom:                               *)
(*          3. x <| p |> |_| I = |_| ((fun y => x <| p |> y) @` I)            *)
(*                                                                            *)
(*           <$>_d f == <|>_d (f \o enum_val) with d a finite distribution    *)
(*                      over a finite type T and f a function from T to some  *)
(*                      convType A                                            *)
(* Convn_of_FSDist d == <$>_(fdist_of_Dist d) (fun x : finsupp d => fsval x)  *)
(*                                                                            *)
(* necset T             == the type of non-empty convex sets over T           *)
(* necset_convType A    == instance of convType with elements of type         *)
(*                         necset A and with operator                         *)
(*                           X <| p |> Y = {x<|p|>y | x \in X, y \in Y}       *)
(* necset_semiCompSemiLattType == instance of semiCompSemiLattType with       *)
(*                         elements of type necset A and with operator        *)
(*                         |_| X = hull (bigsetU X idfun)                     *)
(*                                                                            *)
(* necset_semiCompSemiLattConvType == instance of semiCompSemiLattConvType    *)
(*                         with elements of type necset A                     *)
(*                                                                            *)
(* necset_join                                                                *)
(* necset_bind                                                                *)
(******************************************************************************)

Declare Scope latt_scope.

Reserved Notation "x %:ne" (at level 0, format "x %:ne").
Reserved Notation "x <| p |>: Y" (format "x  <| p |>:  Y", at level 50).
Reserved Notation "X :<| p |>: Y" (format "X  :<| p |>:  Y", at level 50).
Reserved Notation "x [+] y" (format "x  [+]  y", at level 50).
Reserved Notation "'<$>_' d f" (at level 36, f at level 36, d at level 0,
  format "<$>_ d  f").
Reserved Notation "'|_|' f" (at level 36, f at level 36, format "|_|  f").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope convex_scope.

Section moveme.
Local Open Scope classical_set_scope.
Lemma setU_bigsetU T (I J : set T) : I `|` J = bigsetU [set I; J] idfun.
Proof.
apply eqEsubset => x; [case=> Hx; by [exists I => //; left | exists J => //; right] |].
by case=> K [] -> Hx; [left | right].
Qed.
End moveme.

Section finmap_ext.
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
Section fbig_pred1_inj.
Variables (R : Type) (idx : R) (op : Monoid.com_law idx).
Lemma fbig_pred1_inj (A C : choiceType) h (k : A -> C) (d : {fset _}) a :
  a \in d -> injective k -> \big[op/idx]_(a0 <- d | k a0 == k a) h a0 = h a.
Proof.
move=> ad inj_k.
rewrite big_fset_condE -(big_seq_fset1 op); apply eq_fbig => // a0.
rewrite !inE /=; apply/idP/idP => [|/eqP ->]; last by rewrite eqxx andbT.
by case/andP => _ /eqP/inj_k ->.
Qed.
End fbig_pred1_inj.
Arguments fbig_pred1_inj [R] [idx] [op] [A] [C] [h] [k].
End finmap_ext.

Lemma finsupp_Conv (C : convType) p (p0 : p != 0%:pr) (p1 : p != 1%:pr) (d e : {dist C}) :
  finsupp (d <|p|> e) = (finsupp d `|` finsupp e)%fset.
Proof.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP => j;
  rewrite !mem_finsupp !ConvFSDist.dE inE; first by
    move=> H; rewrite 2!mem_finsupp; apply/orP/paddR_neq0 => //;
    apply: contra H => /eqP/paddR_eq0 => /(_ (FSDist.ge0 _ _ ))/(_ (FSDist.ge0 _ _)) [-> ->];
    rewrite 2!mulR0 addR0.
move/prob_gt0 in p0.
move: p1 => /onem_neq0 /prob_gt0 /= p1.
rewrite 2!mem_finsupp => /orP[dj0|ej0]; apply/eqP/gtR_eqF;
  [apply/addR_gt0wl; last exact/mulR_ge0;
   apply/mulR_gt0 => //; apply/ltR_neqAle; split => //; exact/nesym/eqP |
   apply/addR_gt0wr; first exact/mulR_ge0;
   apply/mulR_gt0 => //; apply/ltR_neqAle; split => //; exact/nesym/eqP].
Qed.

Lemma FSDist_eval_affine (C : choiceType) (x : C) :
  affine_function (fun D : {dist C} => D x).
Proof. by move=> a b p; rewrite /affine_function_at ConvFSDist.dE. Qed.

Section misc_scaled.
Import ScaledConvex.
Local Open Scope R_scope.

Lemma FSDist_scalept_conv (C : convType) (x y : {dist C}) (p : prob) (i : C) :
  scalept ((x <|p|> y) i) (S1 i) =
  ((scalept (x i) (S1 i)) : Scaled_convType C) <|p|> scalept (y i) (S1 i).
Proof. by rewrite ConvFSDist.dE scalept_conv. Qed.

End misc_scaled.

(* Convn indexed over a finType rather than the type of an ordinal as
   in Convn *)
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
Variables (A B : convType) (prj : A -> B).
Hypothesis prj_affine : affine_function prj.
Variables (T : finType) (d : {fdist T}) (f : T -> A).

Lemma S1_proj_Convn_finType :
  S1 (prj (<$>_d f)) = \ssum_i scalept (d i) (S1 (prj (f i))).
Proof.
set (prj' := AffineFunction.Pack (Phant (A -> B)) prj_affine).
move: (affine_function_Sum prj') => /= ->.
exact: S1_Convn_finType.
Qed.
End S1_proj_Convn_finType.

Module NESet.
Local Open Scope classical_set_scope.
Record mixin_of (T : Type) (X : set T) := Mixin {_ : X != set0 }.
Record t (T : Type) : Type := Pack { car : set T ; class : mixin_of car }.
Module Exports.
Notation neset := t.
Notation "s %:ne" := (@Pack _ s (class _)).
Coercion car : neset >-> set.
End Exports.
End NESet.
Export NESet.Exports.

Section neset_canonical.
Variable A : Type.
Canonical neset_predType :=
  Eval hnf in PredType (fun t : neset A => (fun x => x \in (t : set _))).
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
Local Hint Resolve repr_in_neset : core.

Lemma image_const A B (X : neset A) (b : B) :
  (fun _ => b) @` X = [set b].
Proof. apply eqEsubset=> b'; [by case => ? _ -> | by move=> ?; eexists]. Qed.

Lemma neset_bigsetU_neq0 A B (X : neset A) (F : A -> neset B) : bigsetU X F != set0.
Proof. by apply/bigcup_set0P; eexists; split => //; eexists. Qed.

Lemma neset_image_neq0 A B (f : A -> B) (X : neset A) : f @` X != set0.
Proof. apply/set0P; eexists; exact/imageP. Qed.

Lemma neset_setU_neq0 A (X Y : neset A) : X `|` Y != set0.
Proof. by apply/set0P; eexists; left. Qed.

Canonical neset1 {A} (x : A) := @NESet.Pack A [set x] (NESet.Mixin (set1_neq0 x)).
Canonical bignesetU {A} I (S : neset I) (F : I -> neset A) :=
  NESet.Pack (NESet.Mixin (neset_bigsetU_neq0 S F)).
Canonical image_neset {A B} (f : A -> B) (X : neset A) :=
  NESet.Pack (NESet.Mixin (neset_image_neq0 f X)).
Canonical nesetU {T} (X Y : neset T) :=
  NESet.Pack (NESet.Mixin (neset_setU_neq0 X Y)).

Lemma neset_hull_neq0 (T : convType) (F : neset T) : hull F != set0.
Proof. by rewrite hull_eq0 neset_neq0. Qed.

Canonical neset_hull (T : convType) (F : neset T) :=
  NESet.Pack (NESet.Mixin (neset_hull_neq0 F)).

End neset_lemmas.
Local Hint Resolve repr_in_neset : core.
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
  locked (fun y => x <| p |> y) @` Y.
Local Notation "x <| p |>: Y" := (conv_pt_set p x Y).
Lemma conv_pt_setE p x Y : x <| p |>: Y = (fun y => x <| p |> y) @` Y.
Proof. by rewrite /conv_pt_set; unlock. Qed.
Definition conv_set p (X Y : set L) := \bigcup_(x in X) (x <| p |>: Y).
Local Notation "X :<| p |>: Y" := (conv_set p X Y).
Lemma conv_setE p X Y : X :<| p |>: Y = \bigcup_(x in X) (x <| p |>: Y).
Proof. by []. Qed.
Lemma convC_set p X Y : X :<| p |>: Y = Y :<| p.~%:pr |>: X.
Proof.
by apply eqEsubset=> u; case=> x Xx; rewrite conv_pt_setE => -[] y Yy <-;
  exists y => //; rewrite conv_pt_setE; exists x => //; rewrite -convC.
Qed.
Lemma conv1_pt_set x (Y : neset L) : x <| 1%:pr |>: Y = [set x].
Proof.
apply eqEsubset => u; rewrite conv_pt_setE.
- by case => y _; rewrite conv1.
- by move=> ->; eexists => //; rewrite conv1.
Qed.
Lemma conv0_pt_set x (Y : set L) : x <| 0%:pr |>: Y = Y.
Proof.
apply eqEsubset => u; rewrite conv_pt_setE.
- by case=> y Yy <-; rewrite conv0.
- by move=> Yu; exists u=> //; rewrite conv0.
Qed.
Lemma conv1_set X (Y : neset L) : X :<| 1%:pr |>: Y = X.
Proof.
transitivity (\bigcup_(x in X) [set x]); last by rewrite bigcup_set1 image_idfun.
congr bigsetU; apply funext => x /=.
by rewrite (conv1_pt_set x Y).
Qed.
Lemma conv0_set (X : neset L) Y : X :<| 0%:pr |>: Y = Y.
Proof.
rewrite convC_set /= (_ : 0.~%:pr = 1%:pr) ?conv1_set //.
by apply prob_ext; rewrite /= onem0.
Qed.
Definition probset := @setT prob.
Definition natset := @setT nat.
Definition oplus_conv_set (X Y : set L) := \bigcup_(p in probset) (X :<| p |>: Y).
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
Proof. by apply/set0P; exists 0%:pr. Qed.
Lemma natset_neq0 : natset != set0.
Proof. by apply/set0P; exists O. Qed.
Lemma conv_pt_set_neq0 p (x : L) (Y : neset L) : x <| p |>: Y != set0.
Proof. exact: neset_image_neq0. Qed.
Lemma conv_set_neq0 p (X Y : neset L) : X :<| p |>: Y != set0.
Proof. by rewrite neset_neq0. Qed.
Lemma oplus_conv_set_neq0 (X Y : neset L) : oplus_conv_set X Y != set0.
Proof. apply/set0P; eexists; exists 1%:pr => //; by rewrite conv1_set. Qed.
Fixpoint iter_conv_set_neq0 (X : neset L) (n : nat) :
  iter_conv_set X n != set0 :=
  match n with
  | 0 => neset_neq0 X
  | S n' => oplus_conv_set_neq0 X (NESet.Pack (NESet.Mixin (iter_conv_set_neq0 X n')))
  end.
Canonical probset_neset := NESet.Pack (NESet.Mixin probset_neq0).
Canonical natset_neset := NESet.Pack (NESet.Mixin natset_neq0).
Canonical conv_pt_set_neset (p : prob) (x : L) (Y : neset L) :=
  NESet.Pack (NESet.Mixin (conv_pt_set_neq0 p x Y)).
Canonical conv_set_neset (p : prob) (X Y : neset L) :=
  NESet.Pack (NESet.Mixin (conv_set_neq0 p X Y)).
Canonical oplus_conv_set_neset (X Y : neset L) :=
  NESet.Pack (NESet.Mixin (oplus_conv_set_neq0 X Y)).
Canonical iter_conv_set_neset (X : neset L) (n : nat) :=
  NESet.Pack (NESet.Mixin (iter_conv_set_neq0 X n)).

Lemma conv_pt_set_monotone (p : prob) (x : L) (Y Y' : set L) :
  Y `<=` Y' -> x <| p |>: Y `<=` x <| p |>: Y'.
Proof. by move=> YY' u [] y /YY' Y'y <-; exists y. Qed.
Lemma conv_set_monotone (p : prob) (X Y Y' : set L) :
  Y `<=` Y' -> X :<| p |>: Y `<=` X :<| p |>: Y'.
Proof. by move/conv_pt_set_monotone=> YY' u [] x Xx /YY' HY'; exists x. Qed.
Lemma oplus_conv_set_monotone (X Y Y' : set L) :
  Y `<=` Y' -> oplus_conv_set X Y `<=` oplus_conv_set X Y'.
Proof. by move/conv_set_monotone=> YY' u [] p _ /YY' HY'; exists p. Qed.
Lemma iter_monotone_conv_set (X : neset L) (m : nat) :
  forall n, (m <= n)%N -> iter_conv_set X m `<=` iter_conv_set X n.
Proof.
elim: m.
- move=> n _.
  case: n => // n.
  rewrite iter0_conv_set iterS_conv_set.
  by exists 1%:pr => //; rewrite conv1_set.
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
by exists 1%:pr => //; rewrite conv1_set.
Qed.

Lemma Convn_iter_conv_set (n : nat) :
  forall (g : 'I_n -> L) (d : {fdist 'I_n}) (X : set L),
    g @` setT `<=` X -> iter_conv_set X n (<|>_d g).
Proof.
elim: n; first by move=> g d; move: (fdistI0_False d).
move=> n IHn g d X.
case/boolP: (X == set0);
  first by move/eqP => -> /(_ (g ord0)) H; apply False_ind; apply/H/imageP.
move=> Xneq0 gX; set X' := NESet.Pack (NESet.Mixin Xneq0).
have gXi : forall i : 'I_n.+1, X (g i) by apply fullimage_subset.
case/boolP: (d ord0 == 1).
- move/eqP=> d01.
  suff : X (<|>_d g) by move/(@iter_conv_set_superset X' n.+1 (<|>_d g)).
  rewrite (convn_proj g d01).
  by apply/gX/imageP.
- move=> d0n1; rewrite convnE //.
  exists (probfdist d ord0) => //.
  exists (g ord0) => //.
  rewrite conv_pt_setE.
  exists (<|>_(DelFDist.d d0n1) (fun x : 'I_n => g (DelFDist.f ord0 x))) => //.
  apply IHn.
  move=> u [] i _ <-.
  by apply/gX/imageP.
Qed.
Lemma oplus_convC_set (X Y : set L) : oplus_conv_set X Y = oplus_conv_set Y X.
Proof.
suff H : forall X' Y', oplus_conv_set X' Y' `<=` oplus_conv_set Y' X'
    by apply/eqEsubset/H.
move=> {X} {Y} X Y u [] p _.
rewrite convC_set => H.
by exists p.~%:pr => //.
Qed.
Lemma convmm_cset (p : prob) (X : {convex_set L}) : X :<| p |>: X = X.
Proof.
apply eqEsubset=> x.
- case => x0 Xx0; rewrite conv_pt_setE => -[] x1 Xx1 <-; rewrite -in_setE.
  by move/asboolP : (convex_setP X); rewrite in_setE; apply.
- by move=> Xx; exists x=> //; rewrite conv_pt_setE; exists x=> //; rewrite convmm.
Qed.
Lemma oplus_convmm_cset (X : {convex_set L}) : oplus_conv_set X X = X.
Proof.
apply eqEsubset => x.
- case=> p _.
  by rewrite convmm_cset.
- move=> Xx.
  exists 0%:pr => //.
  by rewrite convmm_cset.
Qed.
Lemma oplus_convmm_set_hull (X : set L) :
  oplus_conv_set (hull X) (hull X) = hull X.
Proof. by rewrite oplus_convmm_cset. Qed.
Lemma hull_iter_conv_set (X : set L) : hull X = \bigcup_(i in natset) iter_conv_set X i.
Proof.
apply eqEsubset; first by move=> x [] n [] g [] d [] gX ->; exists n => //; apply Convn_iter_conv_set.
apply bigsubsetU.
elim => [_|n IHn _]; first exact/subset_hull.
have H : iter_conv_set X n.+1 `<=` oplus_conv_set X (hull X)
  by apply/oplus_conv_set_monotone/IHn.
apply (subset_trans H).
rewrite oplus_convC_set.
have : oplus_conv_set (hull X) X `<=` oplus_conv_set (hull X) (hull X).
  exact/oplus_conv_set_monotone/subset_hull.
move/subset_trans; apply.
by rewrite oplus_convmm_set_hull.
Qed.

(* tensorial strength for hull and conv_set *)
Lemma hull_conv_set_strr (p : prob) (X Y : set L) :
  hull (X :<| p |>: hull Y) = hull (X :<| p |>: Y).
Proof.
apply hull_eqEsubset=> u.
- case=> x Xx; rewrite conv_pt_setE=> -[] y [] n [] g [] d [] gY yg <-.
  exists n, (fun i => x <|p|> g i), d.
  rewrite -convnDr yg; split=> //.
  by move=> v [] i _ <-; exists x=> //; rewrite conv_pt_setE; exists (g i) => //; apply/gY/imageP.
- case=> x Xx [] y Yy <-; apply/subset_hull.
  by exists x=> //; exists y=> //; exact/subset_hull.
Qed.
End convex_neset_lemmas.

Notation "x <| p |>: Y" := (conv_pt_set p x Y) : convex_scope.
Notation "X :<| p |>: Y" := (conv_set p X Y) : convex_scope.

(*Reserved Notation "'OP' s" (format "'OP'  s", at level 6).*)

Module SemiCompleteSemiLattice.
Section def.
Local Open Scope classical_set_scope.
(* a semicomplete semilattice has an infinitary operation *)
Record mixin_of (T : choiceType) : Type := Mixin {
  op : neset T -> T ;
  _ : forall x : T, op [set x]%:ne = x ;
  _ : forall I (s : neset I) (f : I -> neset T),
        op (\bigcup_(i in s) f i)%:ne = op (op @` (f @` s))%:ne }.
Structure type :=
  Pack {sort : choiceType; _ : mixin_of sort}.
End def.
Module Exports.
Definition lub_op {T : type} : neset (sort T) -> sort T :=
  let: Pack _ (Mixin op _ _) := T in op.
Arguments lub_op {T} : simpl never.
Notation semiCompSemiLattType := type.
Notation "|_| f" := (lub_op f) : latt_scope.
Coercion sort : semiCompSemiLattType >-> choiceType.
End Exports.
End SemiCompleteSemiLattice.
Export SemiCompleteSemiLattice.Exports.
Local Open Scope latt_scope.

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
Lemma lub_op1 : forall x : L, |_| [set x]%:ne = x.
Proof. by case: L => [? []]. Qed.
(* NB: bigsetU (bigsetI too) is the bind operator for the poserset monad *)
Lemma lub_op_bigsetU : forall (I : Type) (S : neset I) (F : I -> neset L),
    |_| (bignesetU S F) = |_| (lub_op @` (F @` S))%:ne.
Proof. by case: L => [? []]. Qed.

Lemma lub_op_bigcup (I : Type) (S : neset I) (F : I -> neset L) :
  |_| (\bigcup_(i in S) F i)%:ne = |_| (lub_op @` (F @` S))%:ne.
Proof. by rewrite lub_op_bigsetU. Qed.

Lemma nesetU_bigsetU T (I J : neset T) :
  (I `|` J)%:ne = (bigsetU [set I; J] idfun)%:ne.
Proof.
apply/neset_ext => /=; apply eqEsubset => x.
  by case=> Hx; [exists I => //; left | exists J => //; right].
by case=> K [] -> Hx; [left | right].
Qed.

Lemma lub_op_setU (I J : neset L) :
  |_| (I `|` J)%:ne = |_| [set |_| I; |_| J]%:ne.
Proof.
rewrite nesetU_bigsetU lub_op_bigsetU.
congr (|_| _%:ne); apply/neset_ext => /=.
by rewrite image_idfun /= image_setU !image_set1.
Qed.

(* NB: [Reiterman] p.326, axiom 1 is trivial, since our |_| operator receives
   a set but not a sequence. *)

(* [Reiterman] p.326, axiom 2 *)
Lemma lub_op_flatten (F : neset (neset L)) :
  |_| (lub_op @` F)%:ne = |_| (bigsetU F idfun)%:ne.
Proof.
rewrite lub_op_bigsetU; congr (|_| _%:ne); apply/neset_ext => /=.
by rewrite image_idfun.
Qed.

Definition lub_binary (x y : L) := |_| [set x; y]%:ne.
Global Arguments lub_binary : simpl never.
Local Notation "x [+] y" := (lub_binary x y).

Lemma lub_binaryC : commutative lub_binary.
Proof.
by move=> x y; congr lub_op; apply neset_ext => /=; rewrite /lub_binary setUC.
Qed.
Lemma lub_binaryA : associative lub_binary.
Proof.
move=> x y z; rewrite /lub_binary -[in LHS](lub_op1 x) -[in RHS](lub_op1 z).
by rewrite -!lub_op_setU; congr (|_| _); apply neset_ext => /=; rewrite setUA.
Qed.
Lemma lub_binaryxx : idempotent lub_binary.
Proof.
move=> x; rewrite -[in RHS](lub_op1 x); congr (|_| _); apply neset_ext => /=.
by rewrite setUid.
Qed.

Lemma lub_binaryAC : right_commutative lub_binary.
Proof. by move=> x y z; rewrite -!lub_binaryA [X in _ [+] X]lub_binaryC. Qed.
Lemma lub_binaryCA : left_commutative lub_binary.
Proof. by move=> x y z; rewrite !lub_binaryA [X in X [+] _]lub_binaryC. Qed.
Lemma lub_binaryACA : interchange lub_binary lub_binary.
Proof.
by move=> x y z t; rewrite !lub_binaryA [X in X [+] _]lub_binaryAC.
Qed.

Lemma lub_binaryKU y x : x [+] (x [+] y) = x [+] y.
Proof. by rewrite lub_binaryA lub_binaryxx. Qed.
Lemma lub_binaryUK y x : (x [+] y) [+] y = x [+] y.
Proof. by rewrite -lub_binaryA lub_binaryxx. Qed.
Lemma lub_binaryKUC y x : x [+] (y [+] x) = x [+] y.
Proof. by rewrite lub_binaryC lub_binaryUK lub_binaryC. Qed.
Lemma lub_binaryUKC y x : y [+] x [+] y = x [+] y.
Proof. by rewrite lub_binaryAC lub_binaryC lub_binaryxx. Qed.
End semicompletesemilattice_lemmas.
Notation "x [+] y" := (lub_binary x y) : latt_scope.

Section lub_op_morph.
Local Open Scope classical_set_scope.
Local Open Scope latt_scope.
Variables (L M : semiCompSemiLattType).
Definition lub_op_morph (f : L -> M) :=
  forall (X : neset L), f (|_| X) = |_| (f @` X)%:ne.
Definition lub_binary_morph (f : L -> M) :=
  forall (x y : L), f (x [+] y) = f x [+] f y.
Lemma lub_op_lub_binary_morph (f : L -> M) :
  lub_op_morph f -> lub_binary_morph f.
Proof.
move=> H x y.
move: (H [set x; y]%:ne) => ->.
transitivity (|_| [set f x; f y]%:ne) => //.
congr (|_| _%:ne); apply/neset_ext => /=.
by rewrite image_setU !image_set1.
Qed.
End lub_op_morph.

Module LubOpMorph.
Section ClassDef.
Local Open Scope classical_set_scope.
Variables (U V : semiCompSemiLattType).
Structure map (phUV : phant (U -> V)) :=
  Pack {apply : U -> V ; _ : lub_op_morph apply}.
Local Coercion apply : map >-> Funclass.
Variables (phUV : phant (U -> V)) (f g : U -> V) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return lub_op_morph cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.
End ClassDef.
Module Exports.
Coercion apply : map >-> Funclass.
Notation LubOpMorph fA := (Pack (Phant _) fA).
Notation "{ 'Lub_morph' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'Lub_morph'  fUV }") : convex_scope.
Notation "[ 'Lub_morph' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'Lub_morph'  'of'  f  'as'  g ]") : convex_scope.
Notation "[ 'Lub_morph' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'Lub_morph'  'of'  f ]") : convex_scope.
End Exports.
End LubOpMorph.
Export LubOpMorph.Exports.

Module SemiCompSemiLattConvType.
Local Open Scope convex_scope.
Local Open Scope latt_scope.
Local Open Scope classical_set_scope.
Record mixin_of (L : semiCompSemiLattType) (op : prob -> L -> L -> L) := Mixin {
  _ : forall (p : prob) (x : L) (I : neset L),
    op p x (|_| I) = |_| ((op p x) @` I)%:ne }.
Record class_of (T : choiceType) : Type := Class {
  base : SemiCompleteSemiLattice.mixin_of T ;
  base2 : ConvexSpace.mixin_of (SemiCompleteSemiLattice.Pack base) ;
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

Module LubOpAffine.
Section ClassDef.
Local Open Scope classical_set_scope.
Variables (U V : semiCompSemiLattConvType).
Record class_of (f : U -> V) : Prop := Class {
  base : affine_function f ;
  base2 : lub_op_morph f ;
}.
Structure map (phUV : phant (U -> V)) :=
  Pack {apply : U -> V ; class' : class_of apply}.
Definition baseType (phUV : phant (U -> V)) (f : map phUV) : {affine U -> V} :=
  AffineFunction (base (class' f)).
Definition base2Type (phUV : phant (U -> V)) (f : map phUV) : {Lub_morph U -> V} :=
  LubOpMorph (base2 (class' f)).
Local Coercion apply : map >-> Funclass.
Variables (phUV : phant (U -> V)) (f g : U -> V) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.
End ClassDef.
Module Exports.
Coercion apply : map >-> Funclass.
Coercion baseType : map >-> AffineFunction.map.
Coercion base2Type : map >-> LubOpMorph.map.
Canonical baseType.
Canonical base2Type.
Notation Lub_Affine fA := (Pack (Phant _) fA).
Notation "{ 'Lub_affine' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'Lub_affine'  fUV }") : convex_scope.
Notation "[ 'Lub_affine' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'Lub_affine'  'of'  f  'as'  g ]") : convex_scope.
Notation "[ 'Lub_affine' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'Lub_affine'  'of'  f ]") : convex_scope.
End Exports.
End LubOpAffine.
Export LubOpAffine.Exports.

Lemma lub_op_affine_id_proof (A : semiCompSemiLattConvType) : LubOpAffine.class_of (@id A).
Proof.
apply LubOpAffine.Class; first exact: affine_function_id_proof.
by move=> x; congr (|_| _); apply neset_ext; rewrite /= image_idfun.
Qed.
Lemma lub_op_affine_comp_proof (A B C : semiCompSemiLattConvType) (f : A -> B) (g : B -> C) :
  LubOpAffine.class_of f -> LubOpAffine.class_of g ->
  LubOpAffine.class_of (g \o f).
Proof.
case => af jf [] ag jg.
apply LubOpAffine.Class; first exact: affine_function_comp_proof'.
move=> x; cbn.
rewrite jf jg.
congr (|_| _); apply neset_ext =>/=.
by rewrite imageA.
Qed.

Section semicompsemilattconvtype_lemmas.
Local Open Scope latt_scope.
Local Open Scope convex_scope.
Local Open Scope classical_set_scope.

Variable L : semiCompSemiLattConvType.

Lemma lub_opDr : forall (p : prob) (x : L) (Y : neset L),
  x <|p|> |_| Y = |_| ((fun y => x <|p|> y) @` Y)%:ne.
Proof. by case: L => ? [? ? []]. Qed.
Lemma lub_opDl (p : prob) (X : neset L) (y : L) :
  |_| X <|p|> y = |_| ((fun x => x <|p|> y) @` X)%:ne.
Proof.
rewrite convC lub_opDr.
congr (|_| _); apply/neset_ext/eq_imagel=> x Xx.
by rewrite -convC.
Qed.
Lemma lub_binaryDr p : right_distributive (fun x y => x <|p|> y) (@lub_binary L).
Proof.
move=> x y z.
rewrite lub_opDr.
transitivity (|_| [set x <|p|> y; x <|p|> z]%:ne) => //.
congr (|_| _%:ne); apply/neset_ext => /=.
by rewrite image_setU !image_set1.
Qed.
Lemma lub_op_conv_pt_setE p x (Y : neset L) :
  |_| (x <| p |>: Y)%:ne = |_| ((Conv p x) @` Y)%:ne.
Proof.
by congr (|_| _%:ne); apply/neset_ext => /=; rewrite conv_pt_setE.
Qed.
Lemma lub_op_conv_pt_setD p x (Y : neset L) :
  |_| (x <| p |>: Y)%:ne = x <|p|> |_| Y.
Proof. by rewrite lub_op_conv_pt_setE -lub_opDr. Qed.
Lemma lub_op_conv_setE p (X Y : neset L) :
  |_| (X :<| p |>: Y)%:ne = |_| ((fun x => x <|p|> |_| Y) @` X)%:ne.
Proof.
transitivity (|_| (\bigcup_(x in X) (x <| p |>: Y))%:ne).
  by congr (|_| _%:ne); apply neset_ext.
rewrite lub_op_bigcup //; congr (|_| _%:ne); apply neset_ext => /=.
rewrite imageA; congr image; apply funext => x /=.
by rewrite lub_op_conv_pt_setD.
Qed.
Lemma lub_op_conv_setD p (X Y : neset L) :
  |_| (X :<| p |>: Y)%:ne = |_| X <|p|> |_| Y.
Proof. by rewrite lub_op_conv_setE lub_opDl. Qed.
Lemma lub_oplus_conv_setE (X Y : neset L) :
  |_| (oplus_conv_set X Y)%:ne =
  |_| ((fun p => |_| X <|p|> |_| Y) @` probset)%:ne.
Proof.
transitivity (|_| (\bigcup_(p in probset_neset) (X :<| p |>: Y))%:ne).
  by congr (|_| _%:ne); apply/neset_ext.
rewrite lub_op_bigcup //.
congr (|_| _%:ne); apply/neset_ext => /=.
rewrite imageA; congr image; apply funext => p /=.
by rewrite lub_op_conv_setD.
Qed.
Lemma lub_op_iter_conv_set (X : neset L) (n : nat) :
  |_| (iter_conv_set X n)%:ne = |_| X.
Proof.
elim: n => [|n IHn /=]; first by congr (|_| _); apply/neset_ext.
rewrite (lub_oplus_conv_setE _ (iter_conv_set X n)%:ne).
transitivity (|_| [set |_| X]%:ne); last by rewrite lub_op1.
congr (|_| _%:ne); apply/neset_ext => /=.
transitivity ((fun _ => |_| X) @` probset); last by rewrite image_const.
by congr image; apply funext=> p; rewrite IHn convmm.
Qed.

Lemma lub_op_hull (X : neset L) : |_| (hull X)%:ne = |_| X.
Proof.
transitivity (|_| (\bigcup_(i in natset) iter_conv_set X i)%:ne);
  first by congr (|_| _); apply neset_ext; rewrite /= hull_iter_conv_set.
rewrite lub_op_bigsetU /=.
rewrite -[in RHS](lub_op1 (|_| X)).
transitivity (|_| ((fun _ => |_| X) @` natset)%:ne); last first.
  by congr (|_| _); apply/neset_ext/image_const.
congr (|_| _%:ne); apply/neset_ext => /=.
rewrite imageA; congr image; apply funext => n /=.
by rewrite lub_op_iter_conv_set.
Qed.
End semicompsemilattconvtype_lemmas.

Section Convn_of_FSDist.
Local Open Scope classical_set_scope.
Variable C : convType.
Definition Convn_of_FSDist (d : {dist C}) : C :=
  <$>_(fdist_of_Dist d) (fun x : finsupp d => fsval x).
Import ScaledConvex.

Lemma ssum_seq_finsuppE'' (D : convType) (f : C -> D) (d x : {dist C}) :
  \ssum_(i : fdist_of_FSDist.D d) scalept (x (fsval i)) (S1 (f (fsval i))) =
  \ssum_(i <- finsupp d) scalept (x i) (S1 (f i)).
Proof.
by rewrite -(@big_seq_fsetE
               _ _ _ _ _ xpredT
               (fun i => scalept (x i) (S1 (f i)))).
Qed.

Lemma ssum_seq_finsuppE' (d x : {dist C}) :
  \ssum_(i : fdist_of_FSDist.D d) scalept (x (fsval i)) (S1 (fsval i)) =
  \ssum_(i <- finsupp d) scalept (x i) (S1 i).
Proof.
by rewrite (ssum_seq_finsuppE'' idfun).
Qed.

Lemma ssum_seq_finsuppE (d : {dist C}) :
  \ssum_i scalept (fdist_of_Dist d i) (S1 (fsval i)) =
  \ssum_(i <- finsupp d) scalept (d i) (S1 i).
Proof.
under eq_bigr do rewrite fdist_of_FSDistE.
by rewrite ssum_seq_finsuppE'.
Qed.

Lemma ssum_widen_finsupp (x : {dist C}) X :
  (finsupp x `<=` X)%fset ->
  \ssum_(i <- finsupp x) scalept (x i) (S1 i) =
  \ssum_(i <- X) scalept (x i) (S1 i).
Proof.
move=> xX.
rewrite [in RHS](bigID (fun i => i \in finsupp x)) /=.
have -> : (\ssum_(i <- X | i \notin finsupp x) scalept (x i) (S1 i)) = Zero C
  by rewrite big1 //= => i Hi; rewrite fsfun_dflt // scalept0.
rewrite addpt0 [in RHS]big_fset_condE /=.
suff H : finsupp x = [fset i | i in X & i \in finsupp x]%fset
  by rewrite [in LHS]H.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP=> c; rewrite !inE /=.
- by move=> cfx; move/fsubsetP/(_ c):xX ->.
- by case/andP.
Qed.

Lemma Convn_of_FSDist_affine : affine_function Convn_of_FSDist.
Proof.
move => x y p.
rewrite /affine_function_at.
case/boolP : (p == 0%:pr) => [|pn0]; first by move/eqP ->; rewrite !conv0.
case/boolP : (p == 1%:pr) => [|pn1]; first by move/eqP ->; rewrite !conv1.
have opn0 : p.~ != 0%:pr by apply onem_neq0.
apply S1_inj.
rewrite S1_conv.
rewrite !S1_Convn_finType.
rewrite ssum_seq_finsuppE.
under eq_bigr do rewrite FSDist_scalept_conv.
rewrite big_seq_fsetE big_scalept_conv_split /=.
rewrite 2!ssum_seq_finsuppE' 2!ssum_seq_finsuppE.
have -> : \ssum_(i <- finsupp x) scalept (x i) (S1 i) =
         \ssum_(i <- finsupp (x <|p|> y)) scalept (x i) (S1 i)
  by apply/ssum_widen_finsupp/ConvFSDist.incl_finsupp_conv2fsdist.
have -> : \ssum_(i <- finsupp y) scalept (y i) (S1 i) =
         \ssum_(i <- finsupp (x <|p|> y)) scalept (y i) (S1 i)
  by rewrite convC; apply/ssum_widen_finsupp/ConvFSDist.incl_finsupp_conv2fsdist.
done.
Qed.
End Convn_of_FSDist.


(*Section fset_misc.
Local Open Scope fset_scope.
Lemma fsetD1r (K : choiceType) (x a : K) (B : {fset K}) : x \in B `\ a -> x \in B.
Proof. by case/fsetD1P. Qed.
End fset_misc.*)

Section onem_misc.
Local Open Scope R_scope.
Lemma subR_onem x y : x - y.~ = x + y - 1.
Proof. rewrite /onem; ring. Qed.
End onem_misc.

Section fsdist_misc.
Local Open Scope R_scope.
Local Open Scope fset_scope.
Variables (C : choiceType) (d : {dist C}).
(* TODO: move? *)
Lemma FSDistfmap_FSDist1 (i : C) : FSDistfmap (FSDist1.d (A:=C)) d (FSDist1.d i) = d i.
Proof.
rewrite FSDistfmapE.
case/boolP: (i \in finsupp d)=> ifd; first by rewrite fbig_pred1_inj //; apply:FSDist1_inj.
transitivity(\sum_(a <- finsupp d | a == i) d a);
  first by apply eq_bigl=> j; apply/inj_eq/FSDist1_inj.
rewrite big_seq_cond big_pred0;
  last by move=> j; apply/andP; case=> jfd /eqP ji; move: jfd; rewrite ji (negbTE ifd).
by rewrite fsfun_dflt.
Qed.

Lemma FSDist_finsuppD1 (x : C) : \sum_(i <- finsupp d `\ x) d i = (d x).~.
Proof.
rewrite -subR_eq0 subR_onem.
case/boolP: (x \in finsupp d)=> xfd;
  first by rewrite addRC -big_fsetD1 //= FSDist.f1 subRR.
by rewrite fsfun_dflt // mem_fsetD1 // FSDist.f1 addR0 subRR.
Qed.

Definition FSDist_prob (x : C) : prob := Prob.mk (conj (FSDist.ge0 d x) (FSDist.le1 d x)).
End fsdist_misc.
Canonical FSDist_prob.

Section convex_misc.
Import ScaledConvex.
Local Open Scope fset_scope.
Local Open Scope R_scope.
Local Open Scope convex_scope.
Lemma Convn_of_FSDist_FSDist1 (C : convType) (x : C) :
  Convn_of_FSDist (FSDist1.d x) = x.
Proof.
apply: (@ScaledConvex.S1_inj _ _ x).
rewrite S1_Convn_finType /=.
rewrite (eq_bigr (fun=> ScaledConvex.S1 x)); last first.
  move=> i _; rewrite fdist_of_FSDistE FSDist1.dE /= -(FSDist1.supp x).
  rewrite fsvalP ScaledConvex.scalept1 /=; congr (ScaledConvex.S1 _).
  case: i => i Hi /=; rewrite FSDist1.supp inE in Hi; exact/eqP.
by rewrite big_const (_ : #| _ | = 1%N) // -cardfE FSDist1.supp cardfs1.
Qed.

Lemma Convn_of_FSDist_FSDistfmap (C D : convType) (f : C -> D) (d : {dist C}) :
  affine_function f -> f (Convn_of_FSDist d) = Convn_of_FSDist (FSDistfmap f d).
Proof.
move=> f_aff.
apply S1_inj => /=.
rewrite S1_proj_Convn_finType // S1_Convn_finType.
set X := LHS.
under eq_bigr do rewrite fdist_of_FSDistE.
rewrite ssum_seq_finsuppE' supp_FSDistfmap.
under eq_bigr do rewrite FSDistBind.dE imfset_id.
have Hsupp : forall y,
    y \in [fset f x | x in finsupp d] ->
    y \in \bigcup_(d0 <- [fset FSDist1.d (f a) | a in finsupp d]) finsupp d0.
- move=> y.
  case/imfsetP=> x /= xfd ->.
  apply/bigfcupP.
  exists (FSDist1.d (f x)); last by rewrite FSDist1.supp inE.
  by rewrite andbT; apply/imfsetP; exists x.
rewrite big_seq; under eq_bigr=> y Hy.
- rewrite (Hsupp y Hy).
  rewrite big_scaleptl'; [| by rewrite scalept0 | by move=> j; apply mulR_ge0].
  under eq_bigr=> i do rewrite FSDist1.dE inE.
  over.
rewrite -big_seq exchange_big /= big_seq; under eq_bigr=> x Hx.
- rewrite (big_fsetD1 (f x)) /=; last by apply/imfsetP; exists x.
  rewrite eqxx mulR1.
  rewrite big_seq.
  under eq_bigr=> y do [rewrite in_fsetD1=> /andP [] /negbTE -> Hy; rewrite mulR0 scalept0].
  rewrite big1 // addpt0.
  over.
rewrite /X.
under eq_bigr do rewrite fdist_of_FSDistE.
by rewrite ssum_seq_finsuppE'' big_seq.
Qed.
End convex_misc.

Section triangular_laws_left_convn.
Import ScaledConvex.
Local Open Scope fset_scope.
Local Open Scope R_scope.
Variable C : choiceType.
Lemma triangular_laws_left0 (d : {dist C}) :
  Convn_of_FSDist (FSDistfmap (@FSDist1.d C) d) = d.
Proof.
apply FSDist_ext=> x.
apply S1_inj.
rewrite (S1_proj_Convn_finType (FSDist_eval_affine x)).
under eq_bigr do rewrite fdist_of_FSDistE.
rewrite (ssum_seq_finsuppE'' (fun i : {dist C} => i x)).
rewrite supp_FSDistfmap.
rewrite big_imfset /=; last by move=> *; apply: FSDist1_inj.
under eq_bigr do rewrite FSDist1.dE inE FSDistfmap_FSDist1.
have nx0 :
  \ssum_(i <- finsupp d `\ x)
   scalept (d i) (S1 (if x == i then 1 else 0)) = scalept (d x).~ (S1 0).
- transitivity (scalept (\sum_(i <- finsupp d `\ x) (d i)) (S1 0)).
  + rewrite big_scaleptl' //; last by rewrite scalept0.
    erewrite eq_fbigr; first by reflexivity.
    by move=> y /fsetD1P []; rewrite eq_sym=> /negbTE ->.
  congr (_ _ _).
  by rewrite FSDist_finsuppD1.
case/boolP: (x \in finsupp d) => xfd.
- rewrite (big_fsetD1 x) //= nx0 eqxx.
  rewrite (adjunction_2 (d x)%:pr).
  congr (_ _).
  by rewrite /Conv /= /avg mulR0 addR0 mulR1.
by rewrite -(mem_fsetD1 xfd) nx0 fsfun_dflt // onem0 scalept1.
Qed.
End triangular_laws_left_convn.

Module NECSet.
Section def.
Variable A : convType.
Record class_of (X : set A) : Type := Class {
  base : CSet.mixin_of X ; mixin : NESet.mixin_of X }.
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
  Eval hnf in PredType (fun t : necset A => (fun x => x \in (t : set _))).
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
- case/hull_setU; try by apply/set0P/neset_neq0.
  move=> x [] xX [] y [] yY [] p ->; by exists x, y, p.
- by case => x [] y [] p [] xX [] yY ->; apply mem_hull_setU; rewrite -in_setE.
Qed.

Canonical neset_hull_necset (T : convType) (F : neset T) :=
  NECSet.Pack (NECSet.Class (CSet.Class (hull_is_convex F))
                            (NESet.Mixin (neset_hull_neq0 F))).

Canonical necset1 (T : convType) (x : T) := Eval hnf in
  @NECSet.Pack _ [set x] (NECSet.Class (CSet.Class (is_convex_set1 x))
                                       (NESet.Mixin (set1_neq0 x))).

End necset_lemmas.

(*
(* non-empty convex sets of distributions *)
Notation "{ 'csdist+' T }" := (necset (Dist_convType T)) (format "{ 'csdist+'  T }") : convex_scope.
*)

Module necset_convType.
Section def.
Variable A : convType.
Definition pre_pre_conv (X Y : necset A) (p : prob) : set A :=
  [set a : A | exists x, exists y, x \in X /\ y \in Y /\ a = x <| p |> y].
Lemma pre_pre_conv_convex X Y p : is_convex_set (pre_pre_conv X Y p).
Proof.
apply/asboolP => u v q.
rewrite -in_setE; rewrite inE => /asboolP [] x0 [] y0 [] x0X [] y0Y ->.
rewrite -in_setE; rewrite inE => /asboolP [] x1 [] y1 [] x1X [] y1Y ->.
rewrite -in_setE convACA inE asboolE.
exists (x0 <|q|> x1), (y0 <|q|> y1).
split; [exact: mem_convex_set | split; [exact: mem_convex_set | by []]].
Qed.
Definition pre_conv X Y p : {convex_set A} :=
  CSet.Pack (CSet.Class (pre_pre_conv_convex X Y p)).
Lemma pre_conv_neq0 X Y p : pre_conv X Y p != set0 :> set _.
Proof.
case/set0P: (neset_neq0 X) => x; rewrite -in_setE => xX.
case/set0P: (neset_neq0 Y) => y; rewrite -in_setE => yY.
apply/set0P; exists (x <| p |> y); rewrite -in_setE.
by rewrite inE asboolE; exists x, y.
Qed.
Definition conv p X Y : necset A := locked
  (NECSet.Pack (NECSet.Class (CSet.Class (pre_pre_conv_convex X Y p))
               (NESet.Mixin (pre_conv_neq0 X Y p)))).
Lemma conv1 X Y : conv 1%:pr X Y = X.
Proof.
rewrite /conv; unlock; apply necset_ext => /=; apply/eqEsubset => a.
  by case => x [] y [] xX [] yY ->; rewrite -in_setE conv1.
case/set0P: (neset_neq0 Y) => y; rewrite -in_setE => yY.
rewrite -in_setE => aX.
by exists a, y; rewrite conv1.
Qed.
Lemma convmm p X : conv p X X = X.
Proof.
rewrite/conv; unlock; apply necset_ext => /=; apply eqEsubset => a.
- case => x [] y [] xX [] yY ->.
  rewrite -in_setE; exact: mem_convex_set.
- rewrite -in_setE => aX.
  by exists a, a; rewrite convmm.
Qed.
Lemma convC p X Y : conv p X Y = conv p.~%:pr Y X.
Proof.
by rewrite/conv; unlock; apply necset_ext => /=; apply eqEsubset => a;
  case => x [] y [] xX [] yY ->; exists y, x; [rewrite convC | rewrite -convC].
Qed.
Lemma convA p q X Y Z :
  conv p X (conv q Y Z) = conv [s_of p, q] (conv [r_of p, q] X Y) Z.
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
Definition mixin : ConvexSpace.mixin_of [choiceType of necset A] :=
  @ConvexSpace.Class _ conv conv1 convmm convC convA.
End def.
Section lemmas.
Local Open Scope classical_set_scope.
Variable A : convType.
Lemma convE p (X Y : necset A) : conv p X Y =
  [set a : A | exists x, exists y, x \in X /\ y \in Y /\ a = x <| p |> y]
    :> set A.
Proof. by rewrite/conv; unlock. Qed.
Lemma conv_conv_set p X Y : conv p X Y = X :<| p |>: Y :> set A.
Proof.
rewrite convE; apply eqEsubset=> u.
- by case=> x [] y; rewrite !in_setE; case=> Xx [] Yy ->; exists x => //; rewrite conv_pt_setE; exists y.
- by case=> x Xx; rewrite conv_pt_setE => -[] y Yy <-; exists x, y; rewrite !in_setE.
Qed.
End lemmas.
End necset_convType.
Canonical necset_convType A := ConvexSpace.Pack (necset_convType.mixin A).

Module necset_semiCompSemiLattType.
Section def.
Local Open Scope classical_set_scope.
Variable (A : convType).
Definition pre_op (X : neset (necset A)) : {convex_set A} :=
  CSet.Pack (CSet.Class (hull_is_convex (bigsetU X idfun)%:ne)).
Lemma pre_op_neq0 X : pre_op X != set0 :> set _.
Proof. by rewrite hull_eq0 neset_neq0. Qed.
Definition lub_necset (X : neset (necset A)) : necset A :=
  NECSet.Pack (NECSet.Class (CSet.Class (hull_is_convex (bigsetU X idfun)%:ne))
                            (NESet.Mixin (pre_op_neq0 X))).
Lemma lub_necset1 x : lub_necset [set x]%:ne = x.
Proof. by apply necset_ext => /=; rewrite bigcup1 hull_cset. Qed.
Lemma lub_necset_bigsetU (I : Type) (S : neset I) (F : I -> neset (necset A)) :
  lub_necset (bignesetU S F) = lub_necset (lub_necset @` (F @` S))%:ne.
Proof.
apply necset_ext => /=.
apply hull_eqEsubset => a.
- case => x [] i Si Fix xa.
  exists 1, (fun _ => a), (FDist1.d ord0).
  split; last by rewrite convn1E.
  move=> a0 [] zero _ <-.
  exists (lub_necset (F i)); first by do 2 apply imageP.
  by apply/subset_hull; exists x.
- case => x [] u [] i Si Fiu <-.
  case => n [] g [] d [] /= gx ag.
  exists n, g, d; split => //.
  apply (subset_trans gx).
  move => a0 [] x0 ux0 x0a0.
  exists x0 => //; exists i => //.
  by rewrite Fiu.
Qed.
Definition mixin :=
  SemiCompleteSemiLattice.Mixin lub_necset1 lub_necset_bigsetU.
End def.
End necset_semiCompSemiLattType.
Canonical necset_semiCompSemiLattType A :=
  SemiCompleteSemiLattice.Pack (necset_semiCompSemiLattType.mixin A).

Module necset_semiCompSemiLattConvType.
Section def.
Local Open Scope classical_set_scope.
Variable (A : convType).
Let L := necset_semiCompSemiLattType A.
Lemma axiom (p : prob) (X : L) (I : neset L) :
  necset_convType.conv p X (|_| I) = |_| ((necset_convType.conv p X) @` I)%:ne.
Proof.
apply necset_ext => /=.
rewrite -hull_cset necset_convType.conv_conv_set /= hull_conv_set_strr.
congr hull; apply eqEsubset=> u /=.
- case=> x Xx [] y []Y IY Yy <-.
  exists (necset_convType.conv p X Y); first by exists Y.
  rewrite necset_convType.conv_conv_set.
  by exists x=> //; exists y.
- by case=> U [] Y IY <-; rewrite necset_convType.convE=> -[] x [] y;
    rewrite !in_setE=> -[] Xx [] Yy ->; exists x=> //; rewrite conv_pt_setE; exists y=> //; exists Y.
Qed.

Definition mixin := @SemiCompSemiLattConvType.Class [choiceType of necset A]
  (necset_semiCompSemiLattType.mixin A)
  (necset_convType.mixin A)
  (SemiCompSemiLattConvType.Mixin axiom).
End def.
End necset_semiCompSemiLattConvType.
Canonical necset_semiCompSemiLattConvType A := SemiCompSemiLattConvType.Pack
  (necset_semiCompSemiLattConvType.mixin A).

Module necset_join.
Section def.
Local Open Scope classical_set_scope.
Definition F (T : Type) := necset_convType (FSDist_convType (choice_of_Type T)).
Variable T : Type.
Definition L := F T.
Definition L' := necset (F T).
Definition LL := F (F T).
Definition F1join0' (X : LL) : set L := (@Convn_of_FSDist L) @` X.
Lemma F1join0'_convex X : is_convex_set (F1join0' X).
Proof.
apply/asboolP=> x y p [] dx Xdx <-{x} [] dy Xdy <-{y}.
exists (dx <|p|>dy); first by move/asboolP: (convex_setP X); apply.
by rewrite Convn_of_FSDist_affine.
Qed.
Lemma F1join0'_neq0 X : (F1join0' X) != set0.
Proof.
apply/set0P.
case/set0P: (neset_neq0 X) => x Xx.
by exists (Convn_of_FSDist (x : {dist (F T)})), x.
Qed.
Definition F1join0 : LL -> L' := fun X => NECSet.Pack (NECSet.Class (CSet.Class (F1join0'_convex X)) (NESet.Mixin (F1join0'_neq0 X))).

Definition join1' (X : L') : convex_set (FSDist_convType (choice_of_Type T)) :=
  CSet.Pack (CSet.Class (hull_is_convex (bigsetU X (fun x => if x \in X then (x : set _) else cset0 _)))).
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
  NECSet.Pack (NECSet.Class (CSet.Class (hull_is_convex _))
                            (NESet.Mixin (join1'_neq0 X))).
Definition join : LL -> L := join1 \o F1join0.
End def.
Module Exports.
Definition necset_join := Eval hnf in join.
End Exports.
End necset_join.
Export necset_join.Exports.

Section necset_bind.
Local Open Scope classical_set_scope.
Local Open Scope proba_scope.
Local Open Scope R_scope.
Local Notation M := (necset_join.F).
Section ret.
Variable a : Type.
Definition necset_ret (x : a) : M a := necset1 (FSDist1.d (x : choice_of_Type a)).
End ret.
Section fmap.
Variables (a b : Type) (f : a -> b).
Definition necset_fmap' (ma : M a) :=
  (FSDistfmap (f : choice_of_Type a -> choice_of_Type b)) @` ma.
Lemma FSDistfmap_affine :
  affine_function (FSDistfmap (f : choice_of_Type a -> choice_of_Type b)).
Proof.
by move=> *; rewrite /FSDistfmap /affine_function_at ConvFSDist.bind_left_distr.
Qed.
Lemma necset_fmap'_convex ma : is_convex_set (necset_fmap' ma).
Proof.
apply/asboolP=> x y p [] dx madx <-{x} [] dy mady <-{y}.
eexists; last exact: FSDistfmap_affine.
by move/asboolP: (convex_setP ma); apply.
Qed.
Lemma necset_fmap'_neq0 ma : (necset_fmap' ma) != set0.
Proof.
case/set0P : (neset_neq0 ma) => x max; apply/set0P.
by exists (FSDistfmap (f : choice_of_Type a -> choice_of_Type b) x), x.
Qed.
Definition necset_fmap : M a -> M b :=
  fun ma =>
    NECSet.Pack (NECSet.Class (CSet.Class (necset_fmap'_convex ma))
                              (NESet.Mixin (necset_fmap'_neq0 ma))).
End fmap.
Section bind.
Variables a b : Type.
Definition necset_bind (ma : M a) (f : a -> M b) : M b := necset_join (necset_fmap f ma).
End bind.
End necset_bind.

Section technical_corollaries.
Variable L : semiCompSemiLattConvType.
Corollary Varacca_Winskel_Lemma_5_6 (Y Z : neset L) :
  hull Y = hull Z -> |_| Y = |_| Z.
Proof.
move=> H.
rewrite-[in LHS]lub_op_hull -[in RHS]lub_op_hull.
by congr (|_| _); apply neset_ext.
Qed.

Corollary Beaulieu_technical_equality (x y : L):
  x [+] y = |_| ((fun p => x <| p |> y) @` probset)%:ne.
Proof.
rewrite /lub_binary -[in LHS]lub_op_hull.
congr (|_| _).
apply neset_ext => /=.
apply eqEsubset=> i /=.
- move/set0P: (set1_neq0 x)=> Hx.
  move/set0P: (set1_neq0 y)=> Hy.
  move/(@hull_setU _ _ (necset1 x) (necset1 y) Hx Hy)=> [] a [].
  rewrite inE=> /asboolP ->.
  case=> b []; rewrite inE=> /asboolP ->.
  case=> p ->.
  by eexists.
- case=> p ? <-.
  by apply/mem_hull_setU.
Qed.
End technical_corollaries.
