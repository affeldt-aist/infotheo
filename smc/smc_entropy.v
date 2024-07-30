From mathcomp Require Import all_ssreflect ssralg ssrnum fingroup finalg matrix.
Require Import Reals Lra.
From mathcomp Require Import Rstruct.
Require Import ssrR Reals_ext realType_ext logb ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy smc.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                              SMC Proofs in entroy                          *)
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
Local Open Scope chap2_scope.

Module smc_entropy_proofs.

Section pr_entropy.
  

Variables (T TW TV1 TV2: finType) (P : R.-fdist T).
Variable n : nat.
Notation p := n.+1.
Variables (W: {RV P -> TW}) (V1: {RV P -> TV1}) (V2: {RV P -> 'I_p}).

(* Cannot use fdist_uniform (#|TV2|) (TV2 could be empty if it is arbitrary finType. *)
Hypothesis pV2_unif : `p_ V2 = fdist_uniform (card_ord p).
Hypothesis V1V2indep : P|= V1 _|_ V2.

Lemma cpr_cond_entropy1_RV v1 v2:
  (forall w ,
  `Pr[ W = w | V1 = v1 ] = `Pr[ W = w | [%V1, V2] = (v1, v2) ]) ->
  cond_entropy1_RV V1 W v1 = cond_entropy1_RV [% V1, V2] W (v1, v2). 
Proof.
move => H.
case /boolP : ((`p_ [% V1, W])`1 v1 == 0)  => Hv1.
  rewrite /cond_entropy1_RV.
  rewrite /entropy.
  congr -%R.
  apply:eq_bigr => a _.
  (*rewrite jfdist_condE. -- it brings `(fdistmap [% V1, V2, W] P)`1 (v1, v2) != 0%coqR` so we cannot use it*)
  rewrite /jfdist_cond.
  have Hv2: ((`p_ [% V1, V2, W])`1 (v1, v2) == 0).
    rewrite fst_RV2.
    apply/eqP.
    move:(@Pr_domin_setX TV1 'I_p (`p_ [%V1, V2]) [set v1] [set v2]).
    rewrite !Pr_set1.
    rewrite setX1.
    rewrite !Pr_set1.
    rewrite fst_RV2.
    apply.
    rewrite fst_RV2 in Hv1.
    exact/eqP. 
  destruct (boolP _).
    exfalso.
    by rewrite Hv1 in i. 
  destruct (boolP _).
    exfalso.
    by rewrite Hv2 in i0. 
  by rewrite !fdist_uniformE.

rewrite cond_entropy1_RVE //.
rewrite cond_entropy1_RVE; last first.
  rewrite fst_RV2.
  rewrite fst_RV2 in Hv1.
  rewrite -pr_eqE'.
  rewrite V1V2indep.
  rewrite !pr_eqE'.
  rewrite mulR_neq0'.
  rewrite Hv1 /=.
  rewrite pV2_unif.
  rewrite fdist_uniformE /=.
  rewrite card_ord.
  rewrite invr_eq0.
  by rewrite pnatr_eq0.

rewrite /cond_entropy1.
rewrite /entropy.
congr -%R.
apply:eq_bigr => a _.
have -> // : \Pr_`p_ [% W, V1][[set a] | [set v1]] = \Pr_`p_ [% W, [%V1, V2]][[set a] | [set (v1, v2)]].
rewrite !jPr_Pr.
by rewrite !cpr_eq_set1.
Qed.

End pr_entropy.

Section theorem_3_7.

Variables (T TX TY1 TY2: finType).
Variable P : R.-fdist T.
Variable n : nat.
Notation p := n.+1.
Variables (X: {RV P -> TX}) (Z : {RV P -> 'I_p}).
Variables (f1 : TX -> TY1) (f2 : TX -> TY2) (fm : TX -> 'I_p). 
Hypothesis pZ_unif : `p_ Z = fdist_uniform (card_ord p).
Hypothesis Z_X_indep : inde_rv Z X.

Variables (y1 : TY1) (y2 : TY2) (ymz : 'I_p).

Let Y1 := f1 `o X.
Let Y2 := f2 `o X.  (* y2...ym-1*)
Let Ym := fm `o X.
Let YmZ := Ym `+ Z.
Let f x := (f1 x, f2 x, fm x).
Let Y := f `o X.

Hypothesis Hneq0 : `Pr[ [%YmZ, Y2] = (ymz, y2) ] != 0.
Hypothesis YmZ_unif : `p_ YmZ = fdist_uniform (card_ord p).
Hypothesis Y2YmZindep : P|= Y2 _|_ YmZ.

Theorem mc_removal_entropy :
  cond_entropy1_RV [%Y2, YmZ] Y1 (y2, ymz) =
  cond_entropy1_RV Y2 Y1 y2.
Proof.
simpl in *.
apply /esym /cpr_cond_entropy1_RV => //.
move => w.

have : cond_entropy1_RV [% Y2, YmZ] Y1 (y2, ymz) = cond_entropy1_RV Y2 Y1 y2.


have /= :=(cpr_cond_entropy1_RV YmZ_unif Y2YmZindep).
move/(_ TY1 Y1 y2 ymz).
have Ha :=(@mc_removal_pr _ _ _ _ P n X Z f1 f2 fm pZ_unif Z_X_indep y1 y2 ymz Hneq0).
rewrite -/Y1 -/Y2 -/YmZ in Ha.
symmetry in Ha.
move => Hb.
(* Cannot Hb Ha but can rewrite *)
rewrite Hb //.
Fail Check (Hb Ha).
Abort.

End theorem_3_7.

Section lemma_3_8.

Variables (T TX TY TZ: finType).
Variable P : R.-fdist T.
Variables (X : {RV P -> TX}) (Y : {RV P -> TY}) (f : TY -> TZ)
(x : TX) (y : TY) (z : TZ).

Let Z := f `o Y.
Hypothesis pr_eq_ZY_Y : `Pr[ [% Z, Y] = (f y, y) ] = `Pr[ Y = y ].
Hypothesis pr_Y_neq0 : `Pr[ Y = y ] != 0.
(* TODO tried to define it as `Pr[ Y = y ] > 0 and then use `Rlt_not_eq` in the proof,
   but this hypothesis would be wrapped by `is_true` that `Rlt_not_eq` cannot be applied directly. 
*)

(* H(f(Y)|X,Y) = H(f(Y)|Y) = 0 *)
(* Meaning: f(Y) is completely determined by Y.
   (Because `f` only has one input which is Y).

   And because it is completely determined by Y,
   `(X, Y)` won't increase the uncertanty.
*)
Lemma fun_cond_entropy_eq0 :
  cond_entropy1_RV Y Z y = 0.
Proof.
rewrite cond_entropy1_RVE.
rewrite /cond_entropy1.
rewrite big1 -1?oppr0 // => i _.
have [<-|] := eqVneq (f y) i.
set pZY := (X in (X * log X)%coqR).
have HpZY: pZY = 1.
  rewrite /pZY.
  rewrite jPr_Pr.
  rewrite cpr_eq_set1.
  rewrite cpr_eqE.
  rewrite coqRE.
  rewrite pr_eq_ZY_Y //=.
  by rewrite divff //=.
rewrite HpZY.
rewrite log1.
by rewrite mulR0 //.
move => Hfy_neq_i.
rewrite jPr_Pr.
rewrite cpr_eq_set1.
rewrite /Z.
have Hfy_eq0: `Pr[ (f `o Y) = i | Y = y ] = 0.
  rewrite cpr_eqE.
  Search comp_RV.
  rewrite coqRE.
  (* Not yet because we still have the joint probability not two `Pr(s)*)
  rewrite -[X in X / _](@pr_eq_comp T P TY TZ Y f y).


Abort.


(* H(X|Y,f(Y))=H(X|Y) *)
Lemma fun_cond_removal :
  cond_entropy1_RV [%Z, Y] X (z, y) =
  cond_entropy1_RV Y X y. 
Proof.
Search cond_entropy.
rewrite /cond_entropy1_RV.


  


End lemma_3_8.
  


End smc_entropy_proofs.
