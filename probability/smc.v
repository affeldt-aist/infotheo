(* infotheo: information theory and error-correcting codes in Coq               *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later              *)

From mathcomp Require Import all_ssreflect ssralg ssrnum matrix.
From mathcomp Require Import reals Rstruct zmodp ring lra.
Require Import Reals.

Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond graphoid.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                              SMC Useful Tools                              *)
(*     From: Information-theoretically Secure Number-product Protocol         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Section more_independent_rv_lemmas.

Variables (A : finType) (P : R.-fdist A) (TA TB TC TD : finType).
Variables (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z : {RV P -> TC}).
Variables (UA UB : finType) (f : TA -> UA) (g : TB -> UB).

Local Notation "f × g" :=
  (fun xy => (f xy.1, g xy.2)) (at level 10).

(* Information-Theoretically Secure Number Protocol*)
(* Lemma 3.1 *)
Lemma inde_rv_comp : inde_rv X Y -> inde_rv (f `o X) (g `o Y).
Proof.
move/inde_rv_events'.
rewrite /inde_rv_ev.
move=> H i j.
rewrite -[LHS]pr_eq_set1.
rewrite comp_RV2_ACA /=.
rewrite pr_in_comp'.
rewrite -setX1.
rewrite preimsetX.
rewrite !/(_ @^-1: _).
rewrite H. (* second to third line in the pencil-paper proof *)
rewrite -!pr_in_comp'.
by rewrite !pr_eq_set1.
Qed.

(* Lemma 3.2 *)
Lemma RV2_inde_rv_snd : P |= [% X, Y] _|_ Z -> P |= Y _|_ Z.
Proof.
move/inde_rv_events'.
move=> H y z.
rewrite -[LHS]pr_eq_set1 pr_inE'.
rewrite -(snd_RV2 X [% Y, Z]) Pr_fdist_snd.
rewrite -pr_inE'.
rewrite setTE -setX1.
rewrite pr_in_pairA.
rewrite H.
by rewrite -setTE pr_inE' -Pr_fdist_snd snd_RV2 -pr_inE' !pr_eq_set1.
Qed.


Lemma cpr_prd_unit_RV : X _|_ Y | [% unit_RV P, Z] -> X _|_ Y | Z.
Proof.
move=>H a b c.
have:=H a b (tt,c).
Undo 2.
move=> + a  /[swap] b c.
Undo 1.
move=> + a b c => /(_ a b (tt,c)).
rewrite 3!cpr_eqE'.
have->: finset (preim [% unit_RV P, Z] (pred1 (tt, c))) = finset (preim Z (pred1 c)).
  apply /setP => x.
  by rewrite !inE.
by rewrite -!cpr_eqE'.
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
rewrite !coqRE.
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
  rewrite coqRE.
  by apply /mulIf.
move => H x y0.
rewrite -cpr_eqE_mul.
case /boolP: (`Pr[ Y = y0 ] == 0) => Hy.
  rewrite (eqP Hy).
  by rewrite mulR0 mulr0.
by rewrite H.
Qed.


End more_independent_rv_lemmas.

Section XY.

Variables (A : finType) (P : R.-fdist A) (TA TB: finType).
Variables (X : {RV P -> TA}) (Y : {RV P -> TB}).

(* TODO: do this in graphoid *)
Lemma inde_rv_sym:  P|= X _|_ Y = P|= Y _|_ X.
Proof.
Admitted.

End XY.

Section XYZ.

Variables (A : finType) (P : R.-fdist A) (TA TB TC: finType).
Variables (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z : {RV P -> TC}).

Lemma inde_RV2_sym : P|=[%X, Y] _|_ Z = P|=[%Y, X] _|_ Z.
Proof.
Fail apply/cinde_rv_unit.
Admitted.

End XYZ.

Section lemma_3_4.

Variable T : finType.
Variable P : R.-fdist T.
Variable n : nat.
Notation p := n.+1.
Variables (X Y : {RV P -> 'I_p}).

(* How to express "the distribution of random variable Y is uniform distribution" as a prop. *)
Variable pY_unif : `p_ Y = fdist_uniform (card_ord p).
Variable XY_indep : P |= X _|_ Y.

(* Add two random variables = add results from two functions. *)
(* We use this because add_RV is in coqR *)
Definition add_RV : {RV P -> 'I_p} := X \+ Y.

Lemma add_RV_mul i : `p_ add_RV i = (\sum_(k <- fin_img X) `Pr[ X = k ] * `Pr[ Y = (i - k)%mcR ]).
Proof.
transitivity (`Pr[add_RV \in [set i]]).
  by rewrite pr_inE' /Pr big_set1.
rewrite (reasoning_by_cases _ X).
transitivity (\sum_(k <- fin_img X) `Pr[ [% X, Y] \in ([set k] `* [set i-k]%mcR) ]).
  apply eq_bigr=> k _.
  rewrite !pr_eq_setE.
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
under eq_bigr do rewrite setX1 pr_eq_set1 -cpr_eqE_mul.
under eq_bigr=> k _.
  (* Similar to `have->:`, set the wanted form *)
  rewrite (_ : _ * _ = `Pr[ X = k ] * `Pr[ Y = (i - k)%mcR ] ); last first.
  rewrite cpr_eqE.  (* To remove the form of conditional probability *)
  rewrite XY_indep. (* So we can split it from `Pr [% X, Y] to `Pr X and `Pr Y*)
  rewrite !coqRE. (* Because / and * are in stdlib, not in mathcomp *)
  rewrite -!mulrA.
  (* case analysis on (`Pr[ Y = (i - k)%mcR ] == 0) *)
  have [|H] := eqVneq `Pr[ Y = (i - k)%mcR ] 0.
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
Lemma add_RV_unif : `p_ add_RV = fdist_uniform (card_ord p).
(* TODO: I cannot directly put X \+ Y in this lemma because the implicit P cannot be inferred. *)
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

Notation "X `+ Y" := (add_RV X Y) : proba_scope.

Section fdist_cond_prop.
Variables T TX TY TZ : finType.
Variables (P : R.-fdist T) (y : TY).
Variables (X : {RV P -> TX}) (Y : {RV P -> TY}) (Z : {RV P -> TZ}).
                                                     
Let E := finset (Y @^-1 y).
Hypothesis E0 : Pr P E != 0.

Variable (X': {RV (fdist_cond E0) -> TX}).
Hypothesis EX' : X' = X.

Lemma Pr_fdist_cond_RV x : `Pr[ X' = x ] = `Pr[ X = x | Y = y ].
Proof. by rewrite pr_eqE Pr_fdist_cond cpr_eqE' EX'. Qed.

Hypothesis Z_XY_indep : inde_rv Z [%X, Y].

Lemma fdist_cond_indep : fdist_cond E0 |= X _|_ Z.
Proof.
move: Z_XY_indep => /cinde_rv_unit /weak_union.
rewrite /cinde_rv /= => H.
move => /= x z.
rewrite mulRC pr_eq_pairC.
have := H z x (tt,y).
rewrite !pr_eqE !Pr_fdist_cond !cpr_eqE'.
have -> // : finset (preim [% unit_RV P, Y] (pred1 (tt, y))) = E.
by apply/setP => e; rewrite !inE.
Qed.
End fdist_cond_prop.

Section lemma_3_5.
  
Variable (T TY : finType).
Variable P : R.-fdist T.
Variable n : nat.
Notation p := n.+1.

Variables (X Z: {RV P -> 'I_p}) (Y : {RV P -> TY} ).
Let XZ : {RV P -> 'I_p} := X \+ Z.

Variable pZ_unif : `p_ Z = fdist_uniform (card_ord p).
Variable Z_XY_indep : inde_rv Z [%X, Y].

Let Z_X_indep : inde_rv Z X.
Proof. exact/cinde_rv_unit/decomposition/cinde_rv_unit/Z_XY_indep. Qed.
Let Z_Y_indep : inde_rv Z Y.
Proof. exact/cinde_rv_unit/decomposition/cinde_drv_2C/cinde_rv_unit/Z_XY_indep.
Qed.


Section iy.
Variables (i : 'I_p) (y : TY).
Let E := finset (Y @^-1 y).
Hypothesis Y0 : Pr P E != 0.

Let X': {RV (fdist_cond Y0) -> 'I_p} := X.
Let Z': {RV (fdist_cond Y0) -> 'I_p} := Z.


Let XZ': {RV (fdist_cond Y0) -> 'I_p} := X' \+ Z'.


Lemma lemma_3_5 : `Pr[ XZ = i | Y = y] = `Pr[ XZ = i].  (* The paper way to prove P |= X\+Z _|_ Y *)
Proof.
rewrite -(Pr_fdist_cond_RV (X':=XZ')) //.
rewrite pr_eqE' (@add_RV_mul _ _ _ X' Z'); last exact: fdist_cond_indep.
under eq_bigr => k _.
  rewrite (Pr_fdist_cond_RV (X:=X)) //.
  rewrite (Pr_fdist_cond_RV (X:=Z)) //.
  rewrite [X in _ * X]cpr_eqE.
  rewrite Z_Y_indep.
  rewrite -[(_/_)%coqR]mulRA mulRV; last by rewrite pr_eqE.
  rewrite mulR1 [X in _ * X]pr_eqE' pZ_unif fdist_uniformE /=.
  over.
rewrite -big_distrl /=.  (* Pull the const part `Pr[ Y = (i - k) ] from the \sum_k *)
rewrite /X' cPr_1 ?mul1r //; last by rewrite pr_eqE.
rewrite pr_eqE' (@add_RV_unif _ _ _ X Z) //.
- by rewrite fdist_uniformE.
- rewrite /inde_rv /= => /= x z.
  rewrite mulRC pr_eq_pairC. (* Swap X _|_ Z to Z _|_ X  so we can apply Z_X_indep *)
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

Variables (T TY TX : finType).
Variable P : R.-fdist T.
Variable n : nat.
Notation p := n.+1.
Variables (i : 'I_p) (x1 : TX) (y : TY).
Variables (X2toXn_1 : {RV P -> TY}) (X1 : {RV P -> TX}) (Xn Z : {RV P -> 'I_p}).


Variable pZ_unif : `p_ Z = fdist_uniform (card_ord p).
Variable Z_X1toXn_indep : inde_rv Z [%X1, X2toXn_1, Xn].
Variable Z_X1toXn_1_indep : inde_rv Z [%X1, X2toXn_1].
Let XnZ := Xn `+ Z.

Hypothesis X0 : `Pr[ [% XnZ, X2toXn_1] = (i, y) ] != 0.

Lemma lemma_3_6 : `Pr[ X1 = x1 | [% X2toXn_1, XnZ] = (y , i)] = `Pr[ X1 = x1 | X2toXn_1 = y].
Proof.
have:= inde_RV2_cinde (X:=X1) (Z:=X2toXn_1) (Y:=XnZ).
move => H.
rewrite cpr_eq_pairCr.
apply: cinde_alt.
rewrite (inde_RV2_sym X1 X2toXn_1 XnZ) in H.
apply: H.
rewrite inde_RV2_sym. 
rewrite inde_rv_sym.
have:= (@lemma_3_5' _ _ P n Xn Z [% X1, X2toXn_1] pZ_unif).
apply.
apply/cinde_rv_unit.
apply: cinde_drv_2C.
by apply/cinde_rv_unit.
exact: X0.
Qed.

End lemma_3_6.

Section theorem_3_7.

Variables (T TX TY1 TY2: finType).
Variable P : R.-fdist T.
Variable n : nat.
Notation p := n.+1.
Variables (X: {RV P -> TX}) (Z : {RV P -> 'I_p}).
Variables (f1 : TX -> TY1) (f2 : TX -> TY2) (fm : TX -> 'I_p). 
Variable pZ_unif : `p_ Z = fdist_uniform (card_ord p).
Variable Z_X_indep : inde_rv Z X.

Let Y1 := f1 `o X.
Let Y2 := f2 `o X.  (* y2...ym-1*)
Let Ym := fm `o X.
Let YmZ := Ym `+ Z.
Let f x := (f1 x, f2 x, fm x).
Let Y := f `o X.

(* inde_rv_comp : inde_rv X Y -> inde_rv (f `o X) (g `o Y). *)

Theorem theorem_3_7 y1 y2 ymz: `Pr[ [% Ym `+ Z, Y2] = (ymz, y2) ] != 0 ->
  `Pr[Y1 = y1|[%Y2, YmZ] = (y2, ymz)] = `Pr[Y1 = y1 | Y2 = y2].
Proof.
apply: lemma_3_6.
apply: pZ_unif.
rewrite (_:[%_ , _] = Y) //.
rewrite (_:Z = idfun `o Z) //. (* id vs. idfun*)
exact: inde_rv_comp.
Qed.
(*TODO: the Entropy part *)


End theorem_3_7.

