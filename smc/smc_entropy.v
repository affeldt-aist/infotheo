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
Local Open Scope entropy_scope.

Module smc_entropy_proofs.
  
Section joint_entropyA.

Variables (A B C: finType) (P : {fdist A * B * C}).

About fdistA.

Lemma joint_entropyA : `H P = `H (fdistA P).
Proof.
congr (- _) => /=.
rewrite (eq_bigr (fun a => P (a.1.1, a.1.2, a.2) * log (P (a.1.1, a.1.2, a.2)))); last by case => -[].
rewrite -(pair_bigA _ (fun a1 a2 => P (a1.1, a1.2, a2) * log (P (a1.1, a1.2, a2)))) /=.
rewrite -(pair_bigA _ (fun a1 a2 => \sum_j P (a1, a2, j) * log (P (a1, a2, j)))) /=.
rewrite [RHS](eq_bigr (fun a => fdistA P (a.1, (a.2.1, a.2.2)) * log (fdistA P (a.1, (a.2.1, a.2.2))))); last by case => i [].
rewrite -(pair_bigA _ (fun a1 a2 => fdistA P (a1, (a2.1, a2.2)) * log (fdistA P (a1, (a2.1, a2.2))))) /=.
apply: eq_bigr => i _.
rewrite -(pair_bigA _ (fun a1 a2 => fdistA P (i, (a1, a2)) * log (fdistA P (i, (a1, a2))))) /=.
apply: eq_bigr => j _.
apply: eq_bigr => k _.
rewrite fdistAE //.
Qed.

End joint_entropyA.

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

Section lemma_3_8_prep.

Variables (T TX TY TZ: finType).
Variable P : R.-fdist T.
Variables (X : {RV P -> TX}) (Y : {RV P -> TY}) (f : TY -> TZ).
Let Z := f `o Y.

Section lemma_3_8_proof.
Variables (y : TY) (z : TZ).

Lemma pr_eq_ZY_Y :
  `Pr[ [% Z, Y] = (f y, y) ] = `Pr[ Y = y ].
Proof.
rewrite !pr_eqE.
congr (Pr P _).
apply/setP => t.
rewrite !inE.
rewrite xpair_eqE.
apply andb_idl => /eqP <- //.
Qed.

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
(*
  Search (`Pr[ _ = _ ])(`p_ _ _).
*)
Lemma fun_cond_entropy_eq0_RV :
  cond_entropy1_RV Y Z y = 0.
Proof.
(* If `Pr[Y = y] = 0, it makes the  \Pr_QP[[set b] | [set a]] zero because the condition will be never true; need to do this before the cond_entropy1RVE *)
(*
have [H|] := eqVneq (`Pr[ Y = y]) 0.
  rewrite /cond_entropy1_RV.
  rewrite /entropy.
  under eq_bigr => a _ .
    rewrite (_ : jfdist_cond _ _ _ = 0).
      rewrite mul0R.
      over.
    rewrite /jfdist_cond.
*)
rewrite cond_entropy1_RVE; last by rewrite fst_RV2 -pr_eqE'.
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
  by rewrite mulR0.
move => Hfy_neq_i.
rewrite jPr_Pr.
rewrite cpr_eq_set1.
rewrite /Z.
(* Try to state that because `f y != i`,  `Pr[ (f `o Y) = i | Y = y ] = 0 *)
have ->: `Pr[ (f `o Y) = i | Y = y ] = 0.
  rewrite cpr_eqE.
  rewrite pr_eqE.
  rewrite (_: finset _ = set0).
    by rewrite Pr_set0 div0R. 
  apply/setP => t.
  rewrite !inE.
  rewrite xpair_eqE.
  rewrite /comp_RV.
  apply/negbTE /negP => /andP [] /[swap] /eqP ->.
  by apply/negP.
by rewrite mul0R.
Qed.

End lemma_3_8_proof.

Lemma fun_cond_entropy_ZY_eq0:
  `H( Z | Y) = 0.
Proof.
rewrite /cond_entropy.
rewrite big1 // => i _.
rewrite snd_RV2.
have [->|Hi] := eqVneq (`p_ Y i) 0.
  by rewrite mul0R.
rewrite -cond_entropy1_RVE ?fst_RV2 //.
by rewrite fun_cond_entropy_eq0_RV ?mulR0 // pr_eqE'.
Qed.

End lemma_3_8_prep.

Section fun_cond_entropy_proof.

Variables (T TX TY TZ: finType).
Variable P : R.-fdist T.
Variables (X : {RV P -> TX}) (Y : {RV P -> TY}) (f : TY -> TZ).
Let Z := f `o Y.

Let pXYZ := `p_ [%X, Y, Z].
Let pX := `p_ X.
Let pYZ := `p_ [%Y, Z].
Let pY := pYZ`1.
Let pYZ_X :=  `p_ [%[%Y, Z], X].
Let pX_YZ := fdistX pYZ_X.
Let pZ_XY := `p_ [%Z, [%X, Y]].
Let pZY := fdistX pYZ.
Let pXY := `p_ [%X, Y].
Let pXY_Z := `p_ [%[%X, Y], Z].

Local Open Scope ring_scope.
About R.
Variable (P': R.-fdist (TX * TY * TZ)).

Lemma eq_joint_entropy_YZ_X_XY_Z:
 joint_entropy pYZ_X = joint_entropy pXY_Z.
Proof.
rewrite joint_entropyC.
rewrite /joint_entropy.
rewrite fdistX_RV2.
rewrite /pXY_Z /pXY_Z.
rewrite /entropy.
congr -%R.
Abort.

Lemma fun_cond_removal :
  cond_entropy pX_YZ = cond_entropy pXY.
Proof.
transitivity (joint_entropy pYZ_X - entropy pYZ). (* joint PQ = H P + cond QP*)
  apply/eqP.
  rewrite eq_sym.
  rewrite subr_eq.
  rewrite addrC.
  apply/eqP.
  have -> // : pX_YZ = fdistX pYZ_X.
    by rewrite /pYZ_X /pX_YZ.
  have -> // : pYZ = pYZ_X`1.
    by rewrite fst_RV2 /pYZ.
  rewrite -coqRE.
  by rewrite -chain_rule.
transitivity (joint_entropy pXY_Z - entropy pYZ). (* H(Y,f(Y),X) -> H(X,Y,f(Y))*)
  rewrite joint_entropyC.
  rewrite /joint_entropy.
  rewrite joint_entropyA.
  by rewrite fdistX_RV2 fdistA_RV3 .
transitivity (joint_entropy pXY + cond_entropy pZ_XY - entropy pY - cond_entropy pZY).
  rewrite [in LHS]chain_rule.
  rewrite !coqRE.
  rewrite fdistX_RV2.
  rewrite fst_RV2.
  rewrite -![in RHS]addrA.
  rewrite [RHS]addrCA.
  rewrite [RHS]addrC.
  rewrite [LHS]addrAC.
  congr (_ + _ + _).
  rewrite -opprD.
  congr (-_).
  exact:chain_rule.
transitivity (joint_entropy pXY - entropy pY).
  rewrite [LHS]addrAC.
  have -> // : cond_entropy pZY = 0.
    rewrite /pZY fdistX_RV2.
    exact:fun_cond_entropy_ZY_eq0.
  have -> // : cond_entropy pZ_XY = 0.
    rewrite /pZ_XY /Z.
    have -> // : f `o Y = (f \o snd) `o [%X, Y].
      by apply/boolp.funext => x //=.
    exact:fun_cond_entropy_ZY_eq0.
  by rewrite addrK.
rewrite joint_entropyC fdistX_RV2.
rewrite -/(joint_entropy `p_ [%Y, X]).
rewrite chain_rule coqRE.
rewrite fst_RV2 fdistX_RV2. 
rewrite addrAC.
by rewrite /pY fst_RV2 subrr add0r.
Qed.

(*
Variables (y : TY) (z : TZ).

(* H(X|Y,f(Y))=H(X|Y) *)
Lemma fun_cond_removal' :
  cond_entropy1_RV [%Z, Y] X (z, y) =
  cond_entropy1_RV Y X y. 
Proof.
rewrite /cond_entropy1_RV.
congr entropy.
rewrite /jfdist_cond.
rewrite fst_RV2.
rewrite jfdist_condE.
Search jfdist_cond.

*)

End fun_cond_entropy_proof.

Section pi2.

Variables (T : finType) (TX TY : finComRingType).
Variable P : R.-fdist T.
Variable n : nat.
Variables (x1 x2 s1 r1 x2' t y1 : {RV P -> 'rV[TX]_n}).

Lemma pi2:
  `H(x2|[%x1, s1, r1, x2', t, y1]) =  `H(x2|[%x1, s1, r1, x2', t]).
Proof.
simpl in * |- *.



  


End smc_entropy_proofs.
