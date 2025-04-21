(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)

From mathcomp Require Import all_ssreflect ssralg finalg ssrnum matrix.
From mathcomp Require Import mathcomp_extra reals Rstruct zmodp ring lra.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond graphoid.

Import GRing.Theory.
Import Num.Theory.

(**md**************************************************************************)
(* # SMC "Useful Tools" probability lemmas                                    *)
(*                                                                            *)
(*     From: Information-theoretically Secure Number-product Protocol,        *)
(*           Sec. III.B  "Useful Tools"                                       *)
(*     SHEN, Chih-Hao, et al. In: 2007 International Conference on Machine    *)
(*     Learning and Cybernetics. IEEE, 2007. p. 3006-3011.                    *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Section more_rv_lemmas.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).
Variables (TA TB TC UA UB UC : eqType) (f : TA -> UA) (g : TB -> UB) (h: TC -> UC).
Variables (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z : {RV P -> TC}).

Local Notation "f × g" :=
  (fun xy => (f xy.1, g xy.2)) (at level 10).

Lemma comp_RV2_ACA : RV2 (f `o X) (g `o Y) = f × g `o RV2 X Y.
Proof. by []. Qed.

Lemma comp_RV3_ACA : [%h `o Z, [% (f `o X), (g `o Y)]] = h × (f × g) `o [%Z, [%X, Y]].
Proof. by []. Qed.
End more_rv_lemmas.

Section more_fdist.

Lemma fdistmapE' (R : realType) (A B : finType) (g : A -> B)
  (p : fdist R A) (b : B):
  fdistmap g p b = (\sum_(a in g @^-1: [set b]) p a).
Proof. by rewrite fdistmapE; apply: eq_bigl=> ?; rewrite !inE. Qed.

End more_fdist.

Section more_inde_RV.
Context {R : realType}.
Variables (A : finType) (P : R.-fdist A) (TA TB : finType).
Variables (X : {RV P -> TA}) (Y : {RV P -> TB}).

Definition inde_RV_ev :=
  forall E F,
    `Pr[ [% X, Y] \in E `* F] = `Pr[ X \in E ] * `Pr[ Y \in F ].

Lemma inde_RV_events' : P |= X _|_ Y <-> inde_RV_ev.
Proof.
split=> H; last by move=> *; rewrite -!pr_in1 -H setX1.
move=> E F; rewrite !pr_inE'.
rewrite [LHS]/Pr; under eq_bigr=> *.
  rewrite fdistmapE.
  under eq_bigl do rewrite !inE /=.
  over.
rewrite [in RHS]/Pr big_distrl /=.
under [RHS]eq_bigr=> i ?.
  rewrite big_distrr /=.
  under eq_bigr do rewrite -!pr_eqE' -H pr_eqE'.
  over.
rewrite -big_setX; apply: eq_bigr=> *.
by rewrite fdistmapE.
Qed.

End more_inde_RV.

Lemma preimg_tt {R : realType} {T TY : finType} (P : R.-fdist T)
    (Y : {RV P -> TY}) (y : TY) :
  [% unit_RV P, Y] @^-1: [set (tt, y)] = Y @^-1: [set y].
Proof. by apply/setP => ?; rewrite !inE. Qed.

Section more_inde_RV_lemmas.
Context {R : realType}.
Variables (A : finType) (P : R.-fdist A).

Local Notation "f × g" :=
  (fun xy => (f xy.1, g xy.2)) (at level 10).

(* Information-Theoretically Secure Number Protocol*)
(* Lemma 3.1 *)
Lemma inde_RV_comp (TA TB UA UB : finType) (X : {RV P -> TA}) (Y : {RV P -> TB})
  (f : TA -> UA) (g : TB -> UB) :
  P |= X _|_ Y -> P|= (f `o X) _|_ (g `o Y).
Proof.
move=> /inde_RV_events' inde_XY'; apply/inde_RV_events' => E F.
by rewrite (pr_in_comp' f) (pr_in_comp' g) -inde_XY' -preimsetX -pr_in_comp'.
Qed.

Lemma inde_RV2_comp (TA TB TC UA UB UC : finType)
  (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z : {RV P -> TC})
  (f : TA -> UA) (g : TB -> UB) (h : TC -> UC) :
  P|= X _|_ [% Y, Z] -> P|= (f `o X) _|_ [% (g `o Y), (h `o Z)].
Proof.
pose gh := (fun '(y, z) => (g y, h z)).
have ->: [% g `o Y, h `o Z] = gh `o [%Y, Z] by [].
exact: inde_RV_comp.
Qed.

Lemma inde_unit_RV (TA : finType) (X : {RV P -> TA}) : P |= unit_RV P _|_ X.
Proof. by move=> [] b; rewrite pr_eq_unit mul1r !pr_eqE -preimg_set1. Qed.

Lemma inde_RV_unit (TA : finType) (X : {RV P -> TA}) : P |= X _|_ unit_RV P.
Proof. exact/inde_RV_sym/inde_unit_RV. Qed.

Variables (TA TB TC TD : finType).
Variables (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z : {RV P -> TC}).
Variables (UA UB UC: finType) (f : TA -> UA) (g : TB -> UB) (h : TC -> UC).

(* Lemma 3.2 *)
Lemma RV2_inde_RV_snd : P |= [% X, Y] _|_ Z -> P |= Y _|_ Z.
Proof.
move=> H.
change Y with (snd `o [% X, Y]).
change Z with (idfun `o Z).
exact: inde_RV_comp.
Qed.

Lemma cpr_prd_unit_RV : X _|_ Y | [% unit_RV P, Z] -> X _|_ Y | Z.
Proof.
move=> + a b c => /(_ a b (tt, c))/=.
rewrite !(cpr_eq_pairCr _ (unit_RV P)) !cpr_eqE !pr_eq_pairA.
by rewrite !inde_RV_unit pr_eq_unit !mulr1.
Qed.

(* Lemma 3.3 *)
Lemma inde_RV2_cinde : P |= [% X, Z] _|_ Y -> X _|_ Y | Z.
Proof.
move=> /cinde_RV_unit/cinde_RV_sym.
move=> /weak_union /cinde_RV_sym.
by apply cpr_prd_unit_RV.
Qed.

Lemma cpr_eqE_mul a b :
  `Pr[ X = a | Y = b ] * `Pr[Y = b] = `Pr[ [% X, Y] = (a, b) ].
Proof.
rewrite cpr_eqE.
rewrite -mulrA.
have [Y0|?] := eqVneq `Pr[ Y = b ] 0.
  by rewrite Y0 !mulr0 pr_eq_domin_RV1.
by rewrite mulVf// mulr1.
Qed.

Lemma inde_rv_cprP : P |= X _|_ Y <->
  forall x y, `Pr[ Y = y ] != 0 -> `Pr[ X = x | Y = y] = `Pr[ X = x].
Proof.
rewrite /inde_RV.
split.
  move => H x y Hy.
  move/(_ x y):H. (* bring back H and apply it with x and y*)
  rewrite -cpr_eqE_mul.
  by apply /mulIf.
move => H x y0.
rewrite -cpr_eqE_mul.
case /boolP: (`Pr[ Y = y0 ] == 0) => Hy.
  rewrite (eqP Hy).
  by rewrite mulr0 mulr0.
by rewrite H.
Qed.

Lemma cinde_rv_cprP : P |= X _|_ Y | Z <->
  forall x y z, `Pr[[%Y, Z] = (y, z) ] != 0 ->
    `Pr[ X = x | [%Y, Z] = (y, z)] = `Pr[ X = x | Z = z].
Proof.
split.
  move => H x y z YZne0.
  apply: cinde_alt.
  exact: H.
  exact: YZne0.
move => H x y z.
move: (H x y z) => H2.
apply: inde_RV2_cinde.
rewrite /inde_RV => [[_a _b] _c].
Abort.

End more_inde_RV_lemmas.

Section XYZ.
Context {R : realType}.
Variables (A : finType) (P : R.-fdist A) (TA TB TC: finType).
Variables (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z : {RV P -> TC}).

Lemma inde_RV2_sym : P |= [%X, Y] _|_ Z <-> P |= [%Y, X] _|_ Z.
Proof.
by split => /cinde_RV_unit/cinde_RV_sym/cinde_drv_2C/cinde_RV_sym/cinde_RV_unit.
Qed.

End XYZ.

Section add_RV.
Context {R : realType}.
Variables (T : finType) (A : finZmodType) (P : R.-fdist T).
Variables (X Y : {RV P -> A}).

Definition add_RV : {RV P -> A} := X \+ Y.

(* better name? *)
Lemma pr_add_eqE' i :
  P |= X _|_ Y ->
  `Pr[ add_RV = i ] =
  (\sum_(k <- fin_img X) `Pr[ X = k ] * `Pr[ Y = (i - k)%R ]).
Proof.
move=> XY_indep.
rewrite -pr_in1 (reasoning_by_cases _ X); apply: eq_bigr=> a _.
rewrite setX1 pr_in1 -XY_indep !pr_eqE /Pr; apply: eq_bigl=> t /=.
rewrite !inE/= !xpair_eqE/= /add_RV/= andbC.
apply: andb_id2l=> /eqP->.
by rewrite [RHS]eq_sym subr_eq eq_sym addrC.
Qed.

Lemma big_fin_img :
  forall [R : Type] (op : SemiGroup.com_law R) (x : R) [I J : finType]
         (h : J -> I) (F : I -> R),
    \big[op/x]_(i <- fin_img h) F i = \big[op/x]_(i in fin_img h) F i.
Proof.
move=> *; rewrite -big_enum.
apply/esym/perm_big/uniq_perm; [exact: enum_uniq | exact: undup_uniq |].
exact: mem_enum.
Qed.

Lemma pr_add_eqE i :
  P |= X _|_ Y ->
  `Pr[ add_RV = i ] =
  (\sum_(k in A) `Pr[ X = k ] * `Pr[ Y = (i - k)%R ]).
Proof.
move/(pr_add_eqE' i)->; apply/esym.
rewrite big_fin_img/= (bigID (mem (fin_img X)))/= -[RHS]addr0.
by congr +%R; apply: big1=> ? H; rewrite (pr_eq0 H) mul0r.
Qed.

End add_RV.

Section lemma_3_4.
Context {R : realType}.
Variables (T : finType) (A: finZmodType).
Variable P : R.-fdist T.
Variable n : nat.
Variables (X Y : {RV P -> A}).

(* How to express "the distribution of random variable Y is uniform distribution" as a prop. *)
Hypothesis card_A : #|A| = n.+1.
Variable pY_unif : `p_ Y = fdist_uniform card_A.
Variable XY_indep : P |= X _|_ Y.

(* Add two random variables = add results from two functions. *)
(* We use this because add_RV is in coqR *)
Definition sub_RV : {RV P -> A} := X \- Y.
Definition neg_RV : {RV P -> A} := \0 \- X.

(* Lemma 3.4 *)
Lemma add_RV_unif : `p_ (add_RV X Y) = fdist_uniform card_A .
Proof.
apply: fdist_ext=> /= i.
rewrite fdist_uniformE -pr_eqE' pr_add_eqE; last exact: XY_indep.
under eq_bigr do rewrite (pr_eqE' Y) pY_unif fdist_uniformE.
by rewrite -big_distrl pr_eq1/= div1r.
Qed.

End lemma_3_4.

Global Arguments add_RV_unif [R T A P n].

Notation "X `+ Y" := (add_RV X Y) : proba_scope.

Section fdist_cond_prop.
Context {R : realType}.
Variables T TX TY TZ : finType.
Variables (P : R.-fdist T) (y : TY).
Variables (X : {RV P -> TX}) (Y : {RV P -> TY}) (Z : {RV P -> TZ}).

Hypothesis E0 : Pr P (Y @^-1: [set y]) != 0.

Variable (X' : {RV (fdist_cond E0) -> TX}).
Hypothesis EX' : X' = X :> (T -> TX).

Lemma Pr_fdist_cond_RV x : `Pr[ X' = x ] = `Pr[ X = x | Y = y ].
Proof. by rewrite pr_eqE_finType Pr_fdist_cond cPr_eq_finType EX'. Qed.

Hypothesis Z_XY_indep : P |= Z _|_ [%X, Y].

Lemma fdist_cond_indep : fdist_cond E0 |= X _|_ Z.
Proof.
move: Z_XY_indep => /cinde_RV_unit /weak_union.
rewrite /cinde_RV /= => H.
move => /= x z.
rewrite mulrC pr_eq_pairC.
have := H z x (tt,y).
by rewrite !pr_eqE_finType !Pr_fdist_cond !cPr_eq_finType preimg_tt.
Qed.

End fdist_cond_prop.

Section lemma_3_5.
Context {R : realType}.
Variable (T TY : finType) (TZ : finZmodType).
Variables (P : R.-fdist T) (X Z : {RV P -> TZ}) (Y : {RV P -> TY}).
Let XZ : {RV P -> TZ} := X `+ Z.

Variable Z_XY_indep : P |= Z _|_ [%X, Y].

Let Z_X_indep : P |= Z _|_ X.
Proof. exact/cinde_RV_unit/decomposition/cinde_RV_unit/Z_XY_indep. Qed.

Let Z_Y_indep : P |= Z _|_ Y.
Proof.
exact/cinde_RV_unit/decomposition/cinde_drv_2C/cinde_RV_unit/Z_XY_indep.
Qed.

Variable n : nat.
Hypothesis card_TZ : #|TZ| = n.+1.
Hypothesis pZ_unif : `p_ Z = fdist_uniform card_TZ.

Section iy.
Variable (y : TY).
Hypothesis Y0 : Pr P (Y @^-1: [set y]) != 0.

Let X' : {RV (fdist_cond Y0) -> TZ} := X.
Let Z' : {RV (fdist_cond Y0) -> TZ} := Z.
Let XZ' : {RV (fdist_cond Y0) -> TZ} := X' `+ Z'.

(* The paper way to prove P |= X \+ Z _|_ Y *)
Lemma lemma_3_5 z : `Pr[ XZ = z | Y = y] = `Pr[ XZ = z].
Proof.
rewrite -(Pr_fdist_cond_RV (X':=XZ')) //.
rewrite /XZ' pr_add_eqE'; last exact: fdist_cond_indep.
under eq_bigr => k _.
  rewrite (Pr_fdist_cond_RV (X:=X)) //.
  rewrite (Pr_fdist_cond_RV (X:=Z)) //.
  rewrite [X in _ * X]cpr_eqE.
  rewrite Z_Y_indep.
  rewrite -[(_/_)]mulrA mulfV; last by rewrite pr_eqE_finType.
  rewrite mulr1 [X in _ * X]pr_eqE' pZ_unif fdist_uniformE /=.
  over.
(* Pull the const part `Pr[ Y = (i - k) ] from the \sum_k *)
rewrite -big_distrl /=.
rewrite /X' cPr_1 ?mul1r//; last by rewrite pr_eqE_finType.
rewrite pr_eqE' (add_RV_unif X Z (card_TZ)) //.
- by rewrite fdist_uniformE.
- rewrite /inde_RV /= => /= z0 z1.
  by rewrite pr_eq_pairC/= Z_X_indep/= mulrC.
Qed.

End iy.

Lemma lemma_3_5' : P |= XZ _|_ Y.
Proof.
apply/inde_rv_cprP  => /= x y y0.
rewrite lemma_3_5//.
by rewrite -pr_eqE_finType.
Qed.

End lemma_3_5.

Section lemma_3_6.
Context {R : realType}.
Variables (T TY TX : finType) (TZ : finZmodType).
Variable P : R.-fdist T.
Variable n : nat.
Variables (i : TZ) (x1 : TX) (y : TY).
(* X2 means X2 to Xn-1 *)
Variables (X2 : {RV P -> TY}) (X1 : {RV P -> TX}) (Xn Z : {RV P -> TZ}).

Hypothesis card_TZ : #|TZ| = n.+1.
Variable pZ_unif : `p_ Z = fdist_uniform card_TZ.
Variable Z_Xs_indep : P |= Z _|_ [%X1, X2, Xn].

Let XnZ := Xn `+ Z.

Hypothesis X0 : `Pr[ [% XnZ, X2] = (i, y) ] != 0.

Lemma lemma_3_6 : `Pr[ X1 = x1 | [% X2, XnZ] = (y , i)] = `Pr[ X1 = x1 | X2 = y].
Proof.
have H := inde_RV2_cinde (X:=X1) (Z:=X2) (Y:=XnZ).
rewrite cpr_eq_pairCr.
apply: cinde_alt; last exact: X0.
rewrite (inde_RV2_sym X1 X2 XnZ) in H.
apply: H.
rewrite inde_RV2_sym.
rewrite inde_RV_sym.
apply: (@lemma_3_5' _ _ _ _ P Xn Z [% X1, X2] _ _ _ pZ_unif).
apply/cinde_RV_unit.
apply: cinde_drv_2C.
exact/cinde_RV_unit.
Qed.

End lemma_3_6.

Section theorem_3_7.
Context {R : realType}.
Variables (T TX TY1 TY2 : finType)(TZ : finZmodType).
Variable P : R.-fdist T.
Variables (X : {RV P -> TX}) (Z : {RV P -> TZ}).
Variables (f1 : TX -> TY1) (f2 : TX -> TY2) (fm : TX -> TZ).

Variable Z_X_indep : P |= Z _|_ X.

Let Y1 := f1 `o X.
Let Y2 := f2 `o X.  (* y2...ym-1*)
Let Ym := fm `o X.
Let YmZ := Ym `+ Z.
Let f x := (f1 x, f2 x, fm x).
Let Y := f `o X.

Variable n : nat.
Hypothesis card_TZ : #|TZ| = n.+1.
Variable pZ_unif : `p_ Z = fdist_uniform card_TZ.

(* Theorem 3.7:  masked_condition_removal *)
Theorem mc_removal_pr y1 y2 ymz:
  `Pr[ [% Y2, Ym `+ Z] = (y2, ymz) ] != 0 ->
  `Pr[Y1 = y1|[%Y2, YmZ] = (y2, ymz)] = `Pr[Y1 = y1 | Y2 = y2].
Proof.
have := @lemma_3_6 _ _ _ _ _ _ n ymz y1 y2 Y2 Y1 Ym Z card_TZ.
rewrite pr_eq_pairC.
apply.
  exact: pZ_unif.
rewrite (_ : [%_ , _] = Y) //.
rewrite (_ : Z = idfun `o Z) //. (* id vs. idfun*)
exact: inde_RV_comp.
Qed.

(*TODO: the Entropy part needs to be done in another file, not inside the probability directory. *)

End theorem_3_7.
