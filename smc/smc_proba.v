(* infotheo: information theory and error-correcting codes in Coq               *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later              *)

From mathcomp Require Import all_ssreflect ssralg finalg ssrnum matrix.
From mathcomp Require Import reals Rstruct zmodp ring lra.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond graphoid.

Import GRing.Theory.
Import Num.Theory.

(************************************************************************************)
(*                              SMC "Useful Tools" probability lemmas               *)
(*                                                                                  *)
(*     From: Information-theoretically Secure Number-product Protocol,              *)
(*           Sec. III.B  "Useful Tools"                                             *)
(*     SHEN, Chih-Hao, et al. In: 2007 International Conference on Machine          *)
(*     Learning and Cybernetics. IEEE, 2007. p. 3006-3011.                          *)
(*                                                                                  *)
(************************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Local Definition R := Rdefinitions.R.

Section conditionnally_independent_discrete_random_variables_extra.

Variables (U: finType) (P : R.-fdist U) (A B C: finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).

Lemma cinde_rv_sym :  X _|_  Y | Z -> Y _|_  X | Z.
Proof. move=>H a b c. by rewrite mulrC cpr_eq_pairC. Qed.

End conditionnally_independent_discrete_random_variables_extra.

Section more_rv_lemmas.
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

Section more_preimset.
Variables (aT1 aT2 aT3 rT1 rT2 rT3: finType).
Variables (f : aT1 -> rT1)  (g : aT2 -> rT2) (h : aT3 -> rT3).
Variables (A : {set rT1}) (B : {set rT2}) (C : {set rT3}).

Local Notation "f × g" :=
  (fun xy => (f xy.1, g xy.2)) (at level 10).

Lemma preimsetX :
  f × g @^-1: (A `* B) = f @^-1: A `* g @^-1: B.
Proof. by apply/setP=> -[] a b /=; rewrite !inE. Qed.

Lemma preimsetX2 :
  h × (f × g) @^-1: (C `* (A `* B)) = h @^-1: C `* (f @^-1: A `* g @^-1: B).
Proof. by apply/setP=> -[] a b /=; rewrite !inE. Qed.

Lemma in_preimset x (Y : {set rT1}) : (x \in f @^-1: Y) = (f x \in Y).
Proof. by rewrite !inE. Qed.
Lemma in_preimset1 x y : (x \in f @^-1: [set y]) = (f x == y).
Proof. by rewrite !inE. Qed.
End more_preimset.

Section more_pr_lemmas.
Variables (U : finType) (P : R.-fdist U).
Variables (TA UA : finType) (f : TA -> UA) (X : {RV P -> TA}).

Lemma pr_in_comp' E :
  `Pr[ (f `o X) \in E ]  = `Pr[ X \in f @^-1: E ].
Proof.
rewrite !pr_inE' /Pr.
rewrite partition_big_preimset /=.
apply: eq_bigr=> i iE.
under [RHS]eq_bigr=> j ?.
  rewrite fdistmapE.
  under eq_bigl do rewrite /= inE /=.
  over.
under eq_bigl do rewrite -in_preimset1.
rewrite -partition_big_preimset /= fdistmapE.
apply: eq_bigl=> j.
by rewrite !inE.
Qed.
End more_pr_lemmas.


Section more_fdist.
Lemma fdistmapE' (R : realType) (A B : finType) (g : A -> B)
  (p : fdist R A) (b : B):
  fdistmap g p b = (\sum_(a in g @^-1: [set b]) p a).
Proof. by rewrite fdistmapE; apply: eq_bigl=> ?; rewrite !inE. Qed.
End more_fdist.


Section more_inde_rv.
Variables (A : finType) (P : R.-fdist A) (TA TB : finType).
Variables (X : {RV P -> TA}) (Y : {RV P -> TB}).

Definition inde_rv_ev :=
  forall E F,
    `Pr[ [% X, Y] \in E `* F] = `Pr[ X \in E ] * `Pr[ Y \in F ].

Lemma inde_rv_events' : inde_rv X Y <-> inde_rv_ev.
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
End more_inde_rv.

Section more_independent_rv_lemmas.

Variables (A : finType) (P : R.-fdist A) (TA TB TC TD : finType).
Variables (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z : {RV P -> TC}).
Variables (UA UB UC: finType) (f : TA -> UA) (g : TB -> UB) (h : TC -> UC).

Local Notation "f × g" :=
  (fun xy => (f xy.1, g xy.2)) (at level 10).


Lemma RV2_indeC :
  P |= [% X, X] _|_ [% Z, Y] ->
  P |= [% X, Y] _|_ [% X, Z].
Proof.
rewrite /inde_rv => H [x1 y] [x2 z].
rewrite [LHS]pr_eq_pairAC.
rewrite -[LHS]pr_eq_pairA.
have H1 := H (x1, x2) (z, y).
rewrite -[LHS]pr_eq_pairA in H1.
Abort.

(* Information-Theoretically Secure Number Protocol*)
(* Lemma 3.1 *)
Lemma inde_rv_comp (UB' TB' : finType) (g' : TB' -> UB')(Y' : {RV P -> TB'}): P|= X _|_ Y' -> P|= (f `o X) _|_ (g' `o Y').
Proof.
move/inde_rv_events'.
rewrite /inde_rv_ev.
move=> H i j.
rewrite -[LHS]pr_in1.
rewrite comp_RV2_ACA /=.
rewrite pr_in_comp'.
rewrite -setX1.
rewrite preimsetX.
rewrite H. (* second to third line in the pencil-paper proof *)
rewrite -!pr_in_comp'.
by rewrite !pr_in1.
Qed.

Lemma inde_RV2_comp : P|= X _|_ [% Y, Z] -> P|= (f `o X) _|_ [% (g `o Y), (h `o Z)].
Proof.
pose gh := (fun '(y, z) => (g y, h z)).
have ->: [% g `o Y, h `o Z] = gh `o [%Y, Z] by [].
apply inde_rv_comp.
Qed.

(* Lemma 3.2 *)
Lemma RV2_inde_rv_snd : P |= [% X, Y] _|_ Z -> P |= Y _|_ Z.
Proof.
move/inde_rv_events'.
move=> H y z.
rewrite -[LHS]pr_in1 pr_inE'.
rewrite -(snd_RV2 X [% Y, Z]) Pr_fdist_snd.
rewrite -pr_inE'.
rewrite setTE -setX1.
rewrite pr_in_pairA.
rewrite H.
by rewrite -setTE pr_inE' -Pr_fdist_snd snd_RV2 -pr_inE' !pr_in1.
Qed.


Lemma cpr_prd_unit_RV : X _|_ Y | [% unit_RV P, Z] -> X _|_ Y | Z.
Proof.
move=>H a b c.
have:=H a b (tt,c).
Undo 2.
move=> + a  /[swap] b c.
Undo 1.
move=> + a b c => /(_ a b (tt,c)).
rewrite 3!cPr_eq_def.
have->: finset (preim [% unit_RV P, Z] (pred1 (tt, c))) = finset (preim Z (pred1 c)).
  apply /setP => x.
  by rewrite !inE.
by rewrite -!cPr_eq_def.
Qed.

(* Lemma 3.3 *)
Lemma inde_RV2_cinde : P |= [% X, Z] _|_ Y -> X _|_ Y | Z.
Proof.
move/cinde_rv_unit /cinde_rv_sym.
move/weak_union /cinde_rv_sym.
by apply cpr_prd_unit_RV.
Qed.

Lemma cpr_eqE_mul a b :
  `Pr[ X = a | Y = b ] * `Pr[Y = b] = `Pr[ [% X, Y] = (a, b) ].
Proof.
rewrite cpr_eqE.
rewrite -!mulrA.
have [|?] := eqVneq `Pr[ Y = b ] 0.
  move=>Y0.
  rewrite Y0.
  rewrite !mulr0.
  rewrite pr_eq_pairC.
  by rewrite pr_eq_domin_RV2.
rewrite mulVr //.
by rewrite mulr1.
Qed.

Lemma inde_rv_cprP : P |= X _|_ Y <-> forall x y, `Pr[ Y = y ] != 0 -> `Pr[ X = x | Y = y] = `Pr[ X = x].
Proof.
rewrite /inde_rv.
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

Lemma cinde_rv_cprP : P |= X _|_ Y | Z <-> forall x y z, `Pr[[%Y, Z] = (y, z) ] != 0 -> `Pr[ X = x | [%Y, Z] = (y, z)] = `Pr[ X = x | Z = z].
Proof.
split.
  move => H x y z YZne0.
  apply: cinde_alt.
  exact: H.
  exact: YZne0.
move => H x y z.
move: (H x y z) => H2.
apply: inde_RV2_cinde.
rewrite /inde_rv => [[_a _b] _c].
Abort.

End more_independent_rv_lemmas.

Section XY.

Variables (A : finType) (P : R.-fdist A) (TA TB: finType).
Variables (X : {RV P -> TA}) (Y : {RV P -> TB}).

Lemma inde_rv_sym:  P|= X _|_ Y <-> P|= Y _|_ X.
Proof. by split => /cinde_rv_unit/cinde_rv_sym/cinde_rv_unit. Qed.

End XY.

Section XYZ.

Variables (A : finType) (P : R.-fdist A) (TA TB TC: finType).
Variables (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z : {RV P -> TC}).

Lemma inde_RV2_sym : P|=[%X, Y] _|_ Z <-> P|=[%Y, X] _|_ Z.
Proof. by split => /cinde_rv_unit/cinde_rv_sym/cinde_drv_2C/cinde_rv_sym/cinde_rv_unit. Qed.

End XYZ.

Section lemma_3_4.

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
Definition add_RV : {RV P -> A} := X \+ Y.
Definition sub_RV : {RV P -> A} := X \- Y.
Definition neg_RV : {RV P -> A} := \0 \- X.

Lemma add_RV_mul i : `p_ add_RV i = (\sum_(k <- fin_img X) `Pr[ X = k ] * `Pr[ Y = (i - k)%R ]).
Proof.
transitivity (`Pr[add_RV \in [set i]]).
  by rewrite pr_inE' /Pr big_set1.
rewrite (reasoning_by_cases _ X).
transitivity (\sum_(k <- fin_img X) `Pr[ [% X, Y] \in ([set k] `* [set i-k]) ]).
  apply eq_bigr=> k _.
  rewrite !pr_inE.
  rewrite /Pr.
  apply: eq_bigl.
  move=>r /=.
  rewrite !inE /=.
  rewrite /add_RV.
  rewrite andbC; apply: andb_id2l.
  rewrite /=.
  move /eqP ->.
  rewrite [RHS]eq_sym.
  by rewrite subr_eq addrC eq_sym.
under eq_bigr do rewrite setX1 pr_in1 -cpr_eqE_mul.
under eq_bigr=> k _.
  (* Similar to `have->:`, set the wanted form *)
  rewrite (_ : _ * _ = `Pr[ X = k ] * `Pr[ Y = (i - k) ] ); last first.
  rewrite cpr_eqE.  (* To remove the form of conditional probability *)
  rewrite XY_indep. (* So we can split it from `Pr [% X, Y] to `Pr X and `Pr Y*)
  rewrite -!mulrA.
  (* case analysis on (`Pr[ Y = (i - k) ] == 0) *)
  have [|H] := eqVneq `Pr[ Y = (i - k) ] 0.
  - by move->; rewrite !mulr0.
  - by rewrite mulVr ?mulr1 //.
  over.
under eq_bigr=> k _.
  rewrite [X in _ * X]pr_eqE' /=.
  rewrite -cpr_eq_unit_RV.
  over.
done.
Qed.

(* Lemma 3.4 *)
Lemma add_RV_unif : `p_ add_RV = fdist_uniform card_A . 
Proof.
apply: fdist_ext=> /= i.
rewrite fdist_uniformE /=.
rewrite add_RV_mul.
under eq_bigr=> k _.
  rewrite [X in _ * X]pr_eqE' pY_unif fdist_uniformE /=.
  rewrite -cpr_eq_unit_RV.
  over.
rewrite -big_distrl /=.  (* Pull the const part `Pr[ Y = (i - k) ] from the \sum_k *)
by rewrite cPr_1 ?mul1r // pr_eq_unit oner_neq0.
Qed.

End lemma_3_4.

Global Arguments add_RV_unif [T A P n].

Notation "X `+ Y" := (add_RV X Y) : proba_scope.

Section fdist_cond_prop.
Variables T TX TY TZ : finType.
Variables (P : R.-fdist T) (y : TY).
Variables (X : {RV P -> TX}) (Y : {RV P -> TY}) (Z : {RV P -> TZ}).
                                                     
Let E := finset (Y @^-1 y).
Hypothesis E0 : Pr P E != 0.

Variable (X': {RV (fdist_cond E0) -> TX}).
Hypothesis EX' : X' = X :> (T -> TX).

Lemma Pr_fdist_cond_RV x : `Pr[ X' = x ] = `Pr[ X = x | Y = y ].
Proof. by rewrite pr_eqE Pr_fdist_cond cPr_eq_def EX'. Qed.

Hypothesis Z_XY_indep : inde_rv Z [%X, Y].

Lemma fdist_cond_indep : fdist_cond E0 |= X _|_ Z.
Proof.
move: Z_XY_indep => /cinde_rv_unit /weak_union.
rewrite /cinde_rv /= => H.
move => /= x z.
rewrite mulrC pr_eq_pairC.
have := H z x (tt,y).
rewrite !pr_eqE !Pr_fdist_cond !cPr_eq_def.
have -> // : finset (preim [% unit_RV P, Y] (pred1 (tt, y))) = E.
by apply/setP => e; rewrite !inE.
Qed.
End fdist_cond_prop.

Section lemma_3_5.
  
Variable (T TY: finType) (TZ: finZmodType).
Variable P : R.-fdist T.
Variable n : nat.

Variables (X Z: {RV P -> TZ}) (Y : {RV P -> TY} ).
Let XZ : {RV P -> TZ} := X `+ Z.

Hypothesis card_TZ : #|TZ| = n.+1.
Hypothesis pZ_unif : `p_ Z = fdist_uniform card_TZ.

Variable Z_XY_indep : inde_rv Z [%X, Y].

Let Z_X_indep : inde_rv Z X.
Proof. exact/cinde_rv_unit/decomposition/cinde_rv_unit/Z_XY_indep. Qed.
Let Z_Y_indep : inde_rv Z Y.
Proof. exact/cinde_rv_unit/decomposition/cinde_drv_2C/cinde_rv_unit/Z_XY_indep.
Qed.


Section iy.
Variables (i : TZ) (y : TY).
Let E := finset (Y @^-1 y).
Hypothesis Y0 : Pr P E != 0.

Let X': {RV (fdist_cond Y0) -> TZ} := X.
Let Z': {RV (fdist_cond Y0) -> TZ} := Z.
Let XZ': {RV (fdist_cond Y0) -> TZ} := X' `+ Z'.


Lemma lemma_3_5 : `Pr[ XZ = i | Y = y] = `Pr[ XZ = i].  (* The paper way to prove P |= X\+Z _|_ Y *)
Proof.
rewrite -(Pr_fdist_cond_RV (X':=XZ')) //.
rewrite pr_eqE' (@add_RV_mul _ _ _ X' Z'); last exact: fdist_cond_indep.
under eq_bigr => k _.
  rewrite (Pr_fdist_cond_RV (X:=X)) //.
  rewrite (Pr_fdist_cond_RV (X:=Z)) //.
  rewrite [X in _ * X]cpr_eqE.
  rewrite Z_Y_indep.
  rewrite -[(_/_)]mulrA mulrV; last by rewrite pr_eqE.
  rewrite mulr1 [X in _ * X]pr_eqE' pZ_unif fdist_uniformE /=.
  over.
rewrite -big_distrl /=.  (* Pull the const part `Pr[ Y = (i - k) ] from the \sum_k *)
rewrite /X' cPr_1 ?mul1r //; last by rewrite pr_eqE.
rewrite pr_eqE' (add_RV_unif X Z (card_TZ)) //.
- by rewrite fdist_uniformE.
- rewrite /inde_rv /= => /= x z.
  rewrite mulrC pr_eq_pairC. (* Swap X _|_ Z to Z _|_ X  so we can apply Z_X_indep *)
  exact: Z_X_indep.
Qed.

End iy.

Lemma lemma_3_5' : P |= XZ _|_ Y.
Proof.
apply/inde_rv_cprP.
move => /= x y0 Hy.
rewrite lemma_3_5 //.
by rewrite -pr_eqE.
Qed.

End lemma_3_5.

Section lemma_3_6.
 
Variables (T TY TX : finType)(TZ : finZmodType).
Variable P : R.-fdist T.
Variable n : nat.
Variables (i : TZ) (x1 : TX) (y : TY).
(* X2 means X2 to Xn-1 *)
Variables (X2 : {RV P -> TY}) (X1 : {RV P -> TX}) (Xn Z : {RV P -> TZ}).

Hypothesis card_TZ : #|TZ| = n.+1.
Variable pZ_unif : `p_ Z = fdist_uniform card_TZ.
Variable Z_Xs_indep : inde_rv Z [%X1, X2, Xn].
Variable Z_X1X2_indep : inde_rv Z [%X1, X2].
Let XnZ := Xn `+ Z.

Hypothesis X0 : `Pr[ [% XnZ, X2] = (i, y) ] != 0.

Lemma lemma_3_6 : `Pr[ X1 = x1 | [% X2, XnZ] = (y , i)] = `Pr[ X1 = x1 | X2 = y].
Proof.
have:= inde_RV2_cinde (X:=X1) (Z:=X2) (Y:=XnZ).
move => H.
rewrite cpr_eq_pairCr.
apply: cinde_alt.
rewrite (inde_RV2_sym X1 X2 XnZ) in H.
apply: H.
rewrite inde_RV2_sym. 
rewrite inde_rv_sym.
have:= (@lemma_3_5' _ _ TZ P n Xn Z [% X1, X2] card_TZ pZ_unif).
apply.
apply/cinde_rv_unit.
apply: cinde_drv_2C.
by apply/cinde_rv_unit.
exact: X0.
Qed.

End lemma_3_6.

Section theorem_3_7.

Variables (T TX TY1 TY2: finType)(TZ: finZmodType).
Variable P : R.-fdist T.
Variable n : nat.
Variables (X: {RV P -> TX}) (Z : {RV P -> TZ}).
Variables (f1 : TX -> TY1) (f2 : TX -> TY2) (fm : TX -> TZ). 

Variable Z_X_indep : inde_rv Z X.

Let Y1 := f1 `o X.
Let Y2 := f2 `o X.  (* y2...ym-1*)
Let Ym := fm `o X.
Let YmZ := Ym `+ Z.
Let f x := (f1 x, f2 x, fm x).
Let Y := f `o X.

Hypothesis card_TZ : #|TZ| = n.+1.
Variable pZ_unif : `p_ Z = fdist_uniform card_TZ.

(* Theorem 3.7:  masked_condition_removal *)
Theorem mc_removal_pr y1 y2 ymz:
  `Pr[ [% Y2, Ym `+ Z] = (y2, ymz) ] != 0 ->
  `Pr[Y1 = y1|[%Y2, YmZ] = (y2, ymz)] = `Pr[Y1 = y1 | Y2 = y2].
Proof.
have H:= (@lemma_3_6 _ _ _ TZ _ n ymz y1 y2 Y2 Y1 Ym Z card_TZ).
rewrite pr_eq_pairC in H.
apply H.
apply: pZ_unif.
rewrite (_:[%_ , _] = Y) //.
rewrite (_:Z = idfun `o Z) //. (* id vs. idfun*)
exact: inde_rv_comp.
Qed.

(*TODO: the Entropy part needs to be done in another file, not inside the probability directory. *)


End theorem_3_7.
