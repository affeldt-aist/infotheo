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

End more_independent_rv_lemmas.

Section lemma_3_4.

Lemma cpr_eqE_mul (U : finType) (P : {fdist U}) (TA TB : finType)
  (X : {RV P -> TA}) (Y : {RV P -> TB}) a b :
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
Definition add_RV' : {RV P -> 'I_p} := X \+ Y.

Lemma add_RV_mul i : `p_ add_RV' i = (\sum_(k <- fin_img X) `Pr[ X = k ] * `Pr[ Y = (i - k)%mcR ]).
Proof.
transitivity (`Pr[add_RV' \in [set i]]).
  by rewrite pr_inE' /Pr big_set1.
rewrite (reasoning_by_cases _ X).
transitivity (\sum_(k <- fin_img X) `Pr[ [% X, Y] \in ([set k] `* [set i-k]%mcR) ]).
  apply eq_bigr=> k _.
  rewrite !pr_eq_setE.
  rewrite /Pr.
  apply: eq_bigl.
  move=>r /=.
  rewrite !inE /=.
  rewrite /add_RV'.
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
Lemma add_RV_unif : `p_ add_RV' = fdist_uniform (card_ord p).
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
  
Variable T : finType.
Variable P : R.-fdist T.
Variable n : nat.
Notation p := n.+1.
Variable i y : 'I_p.
Variables (X Y Z: {RV P -> 'I_p}).

Variable pZ_unif : `p_ Z = fdist_uniform (card_ord p).
Variable Z_XY_indep : inde_rv Z [%X, Y].

Let Z_X_indep : inde_rv Z X.
Proof. exact/cinde_rv_unit/decomposition/cinde_rv_unit/Z_XY_indep. Qed.
Let Z_Y_indep : inde_rv Z Y.
Proof. exact/cinde_rv_unit/decomposition/cinde_drv_2C/cinde_rv_unit/Z_XY_indep.
Qed.

Let E := finset (Y @^-1 y).
Hypothesis Y0 : Pr P E != 0.

Let X': {RV (fdist_cond Y0) -> 'I_p} := X.
Let Z': {RV (fdist_cond Y0) -> 'I_p} := Z.

Let XZ : {RV P -> 'I_p} := X \+ Z.
Let XZ': {RV (fdist_cond Y0) -> 'I_p} := X' \+ Z'.

(* TODO: I cannot directly put X\+Z in lemma because it compains about:

   Cannot infer the implicit parameter P of pr_eq whose type is "R.-fdistT" in:.... *)


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

End lemma_3_5.
