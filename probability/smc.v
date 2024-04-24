(* infotheo: information theory and error-correcting codes in Coq               *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later              *)
From mathcomp Require Import all_ssreflect ssralg matrix.
Require Import Reals.
From mathcomp Require Import Rstruct zmodp.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond graphoid.

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

Variable T : finType.
Variable P : R.-fdist T.
Variable n : nat.
Notation p := n.+1.
Variables (X Y : {RV P -> 'I_p}).

(* How to express "the distribution of random variable X is uniform distribution" as a prop. *)
Variable pX_unif : `p_ X = fdist_uniform (card_ord p).
Variable pY_unif : `p_ X = fdist_uniform (card_ord p).
Variable XY_indep : inde_rv X Y.

(* Add two random variables = add results from two functions. *)
Definition XY : {RV P -> 'I_p} := fun x => Zp_add (X x) (Y x).

Lemma pXY_unif : `p_ XY = fdist_uniform (card_ord p).
Proof.
apply: fdist_ext=> /= x.
rewrite fdist_uniformE /=.
rewrite fdistmapE /=.
under eq_bigr=> i /=.
  rewrite !inE /XY /=.
(* need a lemma to transit from Line 1 to Line 2 of the chained equations *)
  (* if we follow the paper lines, we need to have a k, and i - k in goal 2 ,
     and split XY by marginal? But this is different from [% X, Y] in lemma_3_2 *)
Abort.

Lemma 

End lemma_3_4.
