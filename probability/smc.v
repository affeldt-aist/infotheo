(* infotheo: information theory and error-correcting codes in Coq               *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later              *)
From mathcomp Require Import all_ssreflect ssralg matrix.
Require Import Reals.
From mathcomp Require Import Rstruct zmodp.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond graphoid.
Import GRing.Theory.

(******************************************************************************)
(*                              SMC Useful Tools                              *)
(*     From: Information-theoretically Secure Number-product Protocol         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Section more_independent_rv_lemmas.
Notation R := real_realType.
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

Lemma lemma_3_2 : inde_rv [%X, Y] Z -> inde_rv Y Z.
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

(*
 X _|_ Z | [% unit_RV P, Y] -> X _|_ Z | Y
*)

Lemma cpr_prd_unit_RV : X _|_ Z | [% unit_RV P, Y] -> X _|_ Z | Y.
Proof.
move=>+ a b c.
move/(_ a b (tt,c)).
rewrite 3!cpr_eqE'.
have->: finset (preim [% unit_RV P, Y] (pred1 (tt, c))) = finset (preim Y (pred1 c)).
  apply /setP => x.
  by rewrite !inE.
by rewrite -!cpr_eqE'.
Qed.

Lemma lemma_3_3 : inde_rv [%X, Y] Z -> cinde_rv X Z Y.
Proof.
move/cinde_rv_unit /cinde_rv_sym.
move/weak_union /cinde_rv_sym.
by apply cpr_prd_unit_RV.
Qed.

End more_independent_rv_lemmas.

Section lemma_3_4.


Notation R := real_realType.
Lemma cpr_eqE_mul (U : finType) (P : {fdist U}) (TA TB : eqType)
  (X : {RV P -> TA}) (Y : {RV P -> TB}) a b :
  `Pr[ X = a | Y = b ] * `Pr[Y = b] = `Pr[ [% X, Y] = (a, b) ].
Proof.
rewrite cpr_eqE.
Admitted.

Variable T : finType.
Variable P : R.-fdist T.
Variable n : nat.
Notation p := n.+1.
Variables (X Y : {RV P -> 'I_p}).

(* How to express "the distribution of random variable X is uniform distribution" as a prop. *)
Variable pX_unif : `p_ X = fdist_uniform (card_ord p).
Variable pY_unif : `p_ Y = fdist_uniform (card_ord p).
Variable XY_indep : inde_rv X Y.

(* Add two random variables = add results from two functions. *)
Definition XY : {RV P -> 'I_p} := fun x => (X x + Y x)%mcR.

(* Map between random variables *)

(* Goal: a similar lemma for `Pr [X+Y in E] = \sum ... [X \in K `* Y \in I - K]*)
(* Need: get `i` from I so we can have i - k??*)
Fail Lemma reasoning_by_cases_XY:
  `Pr[ XY \in I ] = \sum_(k <- fin_img X) `Pr[ [% X, Y] \in ([set k] `* [set ik])].


Lemma pXY_unif : `p_ XY = fdist_uniform (card_ord p).
Proof.
apply: fdist_ext=> /= i.
rewrite fdist_uniformE /=.
transitivity (`Pr[XY \in [set i]]).
  rewrite pr_inE'.
  admit.
rewrite (reasoning_by_cases _ X).
transitivity (\sum_(k <- fin_img X) `Pr[ [% X, Y] \in ([set k] `* [set i-k]%mcR) ]).
  apply eq_bigr=> k _.
  rewrite !pr_eq_setE.
  rewrite /Pr.
  apply: eq_bigl.
  move=>r /=.
  rewrite !inE /=.
  rewrite /XY.
  rewrite andbC; apply: andb_id2l.
  move /eqP ->.
  rewrite [RHS]eq_sym.
  by rewrite subr_eq addrC eq_sym.
under eq_bigr do rewrite setX1 pr_eq_set1 -cpr_eqE_mul.
Abort.

End lemma_3_4.
