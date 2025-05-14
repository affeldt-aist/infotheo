From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_proba.

Import GRing.Theory.
Import Num.Theory.

(************************************************************************************)
(*                              SMC Proofs in entropy                               *)
(*                                                                                  *)
(*     From: Information-theoretically Secure Number-product Protocol               *)
(*     SHEN, Chih-Hao, et al. In: 2007 International Conference on Machine          *)
(*     Learning and Cybernetics. IEEE, 2007. p. 3006-3011.                          *)
(*                                                                                  *)
(*                                                                                  *)
(* |   Definitions     |    | Meaning                                              |*)
(* |-------------------|----|------------------------------------------------------|*)
(* |    x \*d y        | == | dot product of two random vectors.                   |*)
(* | scalar_product    | == | The deterministic version of                         |*)
(* |                   |    | SMC scalar product protocol as a function.           |*)
(* | is_scalar_product | == | The correctness of the SMC scalar product results    |*)
(* |-------------------------------------------------------------------------------|*)
(*                                                                                  *)
(*                                                                                  *)
(* Lemmas:                                                                          *)
(*   pi2_bob_is_leakage_free_proof   == the proof shows that Bob's knowledge of     *)
(*                                      Alice's secret input x1 does not increase   *)
(*                                      by accessing random variables received      *)
(*                                      during the protocols execution              *)
(*   pi2_alice_is_leakage_free_proof == the proof shows that Alice's knowledge of   *)
(*                                      Bob's secret input x2 does not increase     *)
(*                                      by accessing random variables received      *)
(*                                      during the protocols execution              *)
(*   cpr_cond_entropy                == given a conditional probability removal     *)
(*                                      lemma P( X | (Y, Z))->P( X | Y ), shows that*)
(*                                      with some conditions met, there exists a    *)
(*                                      conditional entropy removal lemma           *)
(*                                      H( X | (Y, Z))->H( X | Y )                  *)
(*                                                                                  *)
(************************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

Reserved Notation "u *d w" (at level 40).
Reserved Notation "u \*d w" (at level 40).

Local Definition R := Rdefinitions.R.

Module smc_entropy_proofs.
  
Section extra_ring.

Variable V : zmodType.
Implicit Types x y : V.
  
End extra_ring.

  
Section extra_pr.

Variables (T TX TY: finType)(TX': finZmodType).
Variable P : R.-fdist T.
Variable n : nat.

Lemma pr_eq_diag (U : eqType) (X : {RV P -> U}) (x : U) :
  `Pr[ [% X, X] = (x, x) ] = `Pr[ X = x ].
Proof.
by rewrite !pr_eqE /Pr; apply: eq_bigl=> a; rewrite !inE xpair_eqE andbb.
(* After unfolding Pr use eq_bigl to focus on the preim and pred,
   use inE to keep only the pred and as booleaning expression,
   use xpair_eqE to separate the RV2 to two conditions,
   and show LHS and RHS will be only true.
*)
Qed.

Lemma cpr_eq_id (U : eqType) (X : {RV P -> U}) (x : U) :
  `Pr[ X = x ] != 0 -> `Pr[ X = x | X = x ] = 1.
Proof. by move=> ?; rewrite cpr_eqE pr_eq_diag divrr. Qed.

End extra_pr.

Section extra_pr2.
  
Variables (T TX TY TZ: finType).
Variable P : R.-fdist T.

Lemma fst_RV2_neq0 (X : {RV P -> TX}) (Y : {RV P -> TY}) x y:
  `Pr[[%X, Y] = (x, y)] != 0 -> `Pr[ X = x] != 0.
Proof.
apply: contra => /eqP /pr_eq_domin_RV2 H.
by apply/eqP.
Qed.

Lemma cpr_RV2_sym (X : {RV P -> TX}) (Y : {RV P -> TY}) (Z : {RV P -> TZ}) x y z:
  `Pr[ X = x | [% Y, Z] = (y, z) ] = `Pr[ X = x | [% Z, Y] = (z, y) ].
Proof.
rewrite !cpr_eqE.
rewrite [X in (_ / X)]pr_eq_pairC.
congr (_/_).
rewrite pr_eq_pairC.
rewrite [RHS]pr_eq_pairC.
rewrite !pr_eqE.
congr (Pr P _).
apply/setP => t.
rewrite !inE.
rewrite !xpair_eqE.
by rewrite [X in X && _]Bool.andb_comm.
Qed.

End extra_pr2.

Section extra_entropy.
  
Variable T : finType.
Variable P : R.-fdist T.

Lemma cond_entropyC (A B C : finType)
  (X: {RV P -> A}) (Y: {RV P -> B}) (Z: {RV P -> C}) :
  `H(X | [% Y, Z]) = `H(X | [% Z, Y]).
Proof.
rewrite /cond_entropy /=.
rewrite (reindex (fun p : C * B => (p.2, p.1))) /=; last first.
  by exists (fun p : B * C => (p.2, p.1)) => -[b c].
apply: eq_bigr => -[c b] _ /=.
rewrite !snd_RV2 -!pr_eqE' pr_eq_pairC.
congr (_ * _).
rewrite /cond_entropy1; congr (- _).
rewrite /jcPr !snd_RV2.
apply: eq_bigr => a _.
by rewrite !setX1 !Pr_set1 -!pr_eqE' !pr_eq_pairA pr_eq_pairAC (pr_eq_pairC Z).
Qed.

End extra_entropy.

Section entropy_with_indeRV.

Variables (T TX TY TZ: finType).
Variable P : R.-fdist T.

Lemma inde_rv_alt (X : {RV P -> TX}) (Y : {RV P -> TY}):
  inde_rv X Y <-> forall x y,`p_ [%X, Y] (x, y) = `p_ X x * `p_ Y y.
Proof.
rewrite /inde_rv.
split => H x y.
by rewrite -!pr_eqE'.
by rewrite !pr_eqE'.
Qed.

Lemma joint_entropy_indeRV (X : {RV P -> TX}) (Y : {RV P -> TY}):
  inde_rv X Y -> joint_entropy `p_[%X, Y] = `H (`p_X) + `H (`p_Y).
Proof.
rewrite /joint_entropy.
rewrite /entropy.
transitivity (- (\sum_(a in TX) \sum_(b in TY) `p_ [% X, Y] (a, b) * log (`p_ X a * `p_ Y b))).
  congr (- _).
  rewrite pair_big /=.
  apply eq_bigr => -[a b] _ /=.
  congr (_ * log _).
  by apply inde_rv_alt. (* cannot `apply: ` but can `apply `*)
transitivity (
  - (\sum_(a in TX) \sum_(b in TY) `p_ [%X, Y] (a, b) * log (`p_ X a))
  - (\sum_(a in TX) \sum_(b in TY) `p_ [%X, Y] (a, b) * log (`p_ Y b))).
  rewrite -[RHS]opprB.
  congr (- _).
  rewrite opprK.
  rewrite -big_split /=. (* merge two \sum_a...\sum_a in RHS so we can apply eq_bigr*)
  apply eq_bigr => a _.
  rewrite -big_split /=.
  apply eq_bigr => b _.
  have [->|H0] := eqVneq (`p_ [%X, Y](a, b)) 0.
    rewrite !mul0r.
    by rewrite add0r.
  rewrite [in log _]mulrC.
  rewrite logM //. (* from log (x*y) to log x + log y *)
  - by rewrite mulrDr.
  - rewrite -pr_eqE'.
    rewrite pr_eqE Pr_gt0P -pr_eqE.
    move: H0.
    rewrite -pr_eqE' pr_eq_pairC.
    exact: fst_RV2_neq0.
  - rewrite -pr_eqE'.
    rewrite pr_eqE Pr_gt0P -pr_eqE.
    move: H0.
    rewrite -pr_eqE'.
    exact: fst_RV2_neq0.
(* From \sum_a \sum_b `p_ [%X, Y](a, b) to \sum_a `p_ X a*)
under eq_bigr do rewrite -big_distrl -fdist_fstE fst_RV2 /=.
congr (- _ - _).
rewrite exchange_big /=.
apply: eq_bigr => i _.
by rewrite -big_distrl -fdist_sndE snd_RV2 /=.
Qed.

End entropy_with_indeRV.

  
Section joint_entropyA.

Variables (A B C: finType) (P : {fdist A * B * C}).

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
  

Variables (T TY1 TY2 TY3: finType)(P : R.-fdist T).
Variable n : nat.
Notation p := n.+2.
Variables (Y1: {RV P -> TY1}) (Y2: {RV P -> TY2}) (Y3: {RV P -> TY3}).

Hypothesis card_Y3 : #|TY3| = n.+1.
Hypothesis pY3_unif : `p_ Y3 = fdist_uniform card_Y3.
Hypothesis Y2Y3indep : P|= Y2 _|_ Y3.

Lemma cpr_cond_entropy1_RV y2 y3:
  (forall y1 ,
  `Pr[ Y1 = y1 | Y2 = y2 ] = `Pr[ Y1 = y1 | [%Y2, Y3] = (y2, y3) ]) ->
  cond_entropy1_RV Y2 Y1 y2 = cond_entropy1_RV [% Y2, Y3] Y1 (y2, y3).
Proof.
move => H.
case /boolP : ((`p_ [% Y2, Y1])`1 y2 == 0)  => Hy2.
  rewrite /cond_entropy1_RV.
  rewrite /entropy.
  congr -%R.
  apply:eq_bigr => a _.
  (*rewrite jfdist_condE. -- it brings `(fdistmap [% Y2, Y3, Y3] P)`1 (v1, v2) != 0%coqR` so we cannot use it*)
  rewrite /jfdist_cond.
  have Hy3: ((`p_ [% Y2, Y3, Y1])`1 (y2, y3) == 0).
    rewrite fst_RV2.
    apply/eqP.
    move:(@Pr_domin_setX _ TY2 TY3 (`p_ [%Y2, Y3]) [set y2] [set y3]).
    rewrite !Pr_set1.
    rewrite setX1.
    rewrite !Pr_set1.
    rewrite fst_RV2.
    apply.
    rewrite fst_RV2 in Hy2.
    exact/eqP. 
  destruct (boolP _).
    exfalso.
    by rewrite Hy2 in i.
  destruct (boolP _).
    exfalso.
    by rewrite Hy3 in i0. 
  by rewrite !fdist_uniformE.

rewrite cond_entropy1_RVE //.
rewrite cond_entropy1_RVE; last first.
  rewrite fst_RV2.
  rewrite fst_RV2 in Hy2.
  rewrite -pr_eqE'.
  rewrite Y2Y3indep.
  rewrite !pr_eqE'.
  rewrite mulf_neq0 //.
  rewrite pY3_unif.
  rewrite fdist_uniformE /=.
  rewrite card_Y3.
  rewrite invr_eq0.
  by rewrite pnatr_eq0.

rewrite /cond_entropy1.
rewrite /entropy.
congr -%R.
apply:eq_bigr => a _.
have -> // : \Pr_`p_ [% Y1, Y2][[set a] | [set y2]] = \Pr_`p_ [% Y1, [%Y2, Y3]][[set a] | [set (y2, y3)]].
rewrite !jPr_Pr.
by rewrite !cpr_eq_set1.
Qed.

Hypothesis Hy2y3 : forall y1 y2 y3, `Pr[[%Y2, Y3] = (y2, y3)] != 0 ->
  `Pr[ Y1 = y1 | [%Y2, Y3] = (y2, y3) ] = `Pr[ Y1 = y1 | Y2 = y2 ].

Lemma Pr_neq0_cond_removal : forall y1 y2 y3, `Pr[Y3 = y3] != 0 ->
  `Pr[ Y1 = y1 | [%Y2, Y3] = (y2, y3) ] = `Pr[ Y1 = y1 | Y2 = y2 ].
Proof.
move => y1 y2 y3 Hy3neq0.
have [Hy2|Hy2] := eqVneq `Pr[Y2 = y2] 0.
  rewrite !cpr_eqE Y2Y3indep.
  rewrite Hy2 mul0r.
  by rewrite invr0 !mulr0.
apply: Hy2y3.
by rewrite Y2Y3indep mulf_eq0 negb_or Hy2.
Qed.

Lemma snd_extra_indep y2 y3 :
  (`p_ [% Y1, [% Y2, Y3]])`2 (y2, y3) = (`p_ [% Y1, Y2])`2 y2 * `p_Y3 y3.
Proof.
rewrite !fdist_sndE big_distrl /=.
apply eq_bigr => y1 _.
have [Hy3|Hy3] := eqVneq `Pr[Y3 = y3] 0.
  rewrite -!pr_eqE' Hy3 mulr0 pr_eq_pairC pr_eq_domin_RV2 //.
  by rewrite pr_eq_pairC pr_eq_domin_RV2.
have := Pr_neq0_cond_removal y1 y2 Hy3.
rewrite !cpr_eqE Y2Y3indep -!pr_eqE'.
have [Hy2 _|Hy2] := eqVneq `Pr[Y2 = y2] 0.
  rewrite [in RHS]pr_eq_pairC [in LHS]pr_eq_pairC -pr_eq_pairA.
  by rewrite !(pr_eq_domin_RV2 _ _ Hy2) mul0r.
move/(f_equal (fun x => x * (`Pr[Y2 = y2] * `Pr[Y3 = y3]))).
rewrite -[in LHS]mulrA mulVf //; last by rewrite mulf_eq0 negb_or Hy2.
rewrite mulrA -(mulrA _ _^-1). (* Coq identify the A / B is ^-1.*)
by rewrite mulVf // !mulr1.
Qed.

End pr_entropy.

Section cpr_cond_entropy_proof.

Variables (T TY1 TY2 TY3: finType)(P : R.-fdist T).
Variables (Y1 : {RV (P) -> (TY1)})(Y2 : {RV (P) -> (TY2)})(Y3 : {RV (P) -> (TY3)}).

Lemma cpr_cond_entropy (n: nat)(card_TY3 : #|TY3| = n.+1):
  `p_ Y3 = fdist_uniform card_TY3 ->
  P |= Y2 _|_ Y3 ->
  (forall (y1 : TY1) (y2 : TY2) (y3 : TY3),
   `Pr[ [% Y2, Y3] = (y2, y3) ] != 0 ->
       `Pr[ Y1 = y1 | [% Y2, Y3] = (y2, y3) ] =
       `Pr[ Y1 = y1 | Y2 = y2 ]
  ) ->
  `H( Y1 | [% Y2, Y3]) = `H( Y1 | Y2).
Proof.
move => Hunif Hinde Hremoval.
rewrite /cond_entropy /=.
under eq_bigl do rewrite inE /=.
set f : TY2 -> TY3 -> R := fun y2 y3 =>
  (`p_[% Y1, Y2])`2 y2 * `p_Y3 y3 * cond_entropy1 `p_ [% Y1, Y2] y2.
transitivity (\sum_a f a.1 a.2).
  apply eq_bigr => a _.
  rewrite /f {1 2}(surjective_pairing a) /=.
  have [Ha|Ha] := eqVneq ((`p_ [% Y1, Y2])`2 a.1 * `p_Y3 a.2) 0.
    by rewrite Ha snd_extra_indep // Ha !mul0r.
  rewrite snd_extra_indep // -[in LHS]cond_entropy1_RVE; last first.
    by rewrite -fdistX2 fdistX_RV2 snd_extra_indep.
  have [Hy3|Hy3] := eqVneq `Pr[Y3 = a.2] 0.
    rewrite -pr_eqE' in Ha.
    by rewrite Hy3 mulr0 eqxx in Ha.
  have H' := fun w => Pr_neq0_cond_removal Hinde Hremoval w a.1 Hy3.
  rewrite -(cpr_cond_entropy1_RV Hunif Hinde) //.
  rewrite cond_entropy1_RVE ?coqRE //.
  by apply: contra Ha; rewrite mulf_eq0 -fdistX1 fdistX_RV2 => ->.
rewrite -pair_bigA /=.
apply: eq_bigr => y2 _.
by rewrite /f -big_distrl -big_distrr /= FDist.f1 mulr1.
Qed.


End cpr_cond_entropy_proof.

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
rewrite big1 1?oppr0 // => i _.
have [<-|] := eqVneq (f y) i.
  set pZY := (X in (X * log X)).
  have HpZY: pZY = 1.
    rewrite /pZY.
    rewrite jPr_Pr.
    rewrite cpr_eq_set1.
    rewrite cpr_eqE.
    rewrite pr_eq_ZY_Y //=.
    by rewrite divff //=.
  rewrite HpZY.
  rewrite log1.
  by rewrite mulr0.
move => Hfy_neq_i.
rewrite jPr_Pr.
rewrite cpr_eq_set1.
rewrite /Z.
(* Try to state that because `f y != i`,  `Pr[ (f `o Y) = i | Y = y ] = 0 *)
have ->: `Pr[ (f `o Y) = i | Y = y ] = 0.
  rewrite cpr_eqE.
  rewrite pr_eqE.
  rewrite (_: finset _ = set0).
    by rewrite Pr_set0 mul0r. 
  apply/setP => t.
  rewrite !inE.
  rewrite xpair_eqE.
  rewrite /comp_RV.
  apply/negbTE /negP => /andP [] /[swap] /eqP ->.
  by apply/negP.
by rewrite mul0r.
Qed.

End lemma_3_8_proof.

Lemma fun_cond_entropy_ZY_eq0:
  `H( Z | Y) = 0.
Proof.
rewrite /cond_entropy.
rewrite big1 // => i _.
rewrite snd_RV2.
have [->|Hi] := eqVneq (`p_ Y i) 0.
  by rewrite mul0r.
rewrite -cond_entropy1_RVE ?fst_RV2 //.
by rewrite fun_cond_entropy_eq0_RV ?mulr0 // pr_eqE'.
Qed.

End lemma_3_8_prep.

Section fun_cond_entropy_proof.

Variables (T TX TY TZ: finType).
Variable P : R.-fdist T.
Variables (X : {RV P -> TX}) (Y : {RV P -> TY}) (f : TY -> TZ).
Let Z := f `o Y.

Local Open Scope ring_scope.
Variable (P': R.-fdist (TX * TY * TZ)).

Lemma fun_cond_removal :
  `H(X|[% Y, Z]) = `H(X| Y ).
Proof.
transitivity (joint_entropy `p_[%Y, Z, X] - entropy `p_[%Y, Z]). (* joint PQ = H P + cond QP*)
  apply/eqP.
  rewrite eq_sym.
  rewrite subr_eq.
  rewrite addrC.
  apply/eqP.
  have -> // : `p_[%X, [%Y, Z]] = fdistX `p_[%[%Y, Z], X].
    by rewrite fdistX_RV2.
  have -> // : `p_[%Y, Z] = (`p_ [%[%Y, Z], X])`1.
    by rewrite fst_RV2.
  by rewrite -chain_rule.
transitivity (joint_entropy `p_[%[%X, Y], Z] - entropy `p_[%Y, Z]). (* H(Y,f(Y),X) -> H(X,Y,f(Y))*)
  rewrite joint_entropyC.
  rewrite /joint_entropy.
  rewrite joint_entropyA.
  by rewrite fdistX_RV2 fdistA_RV3 .
transitivity (joint_entropy `p_[%X,Y] + cond_entropy `p_[%Z, [%X, Y]] - entropy `p_Y - cond_entropy `p_[%Z, Y]).
  rewrite [in LHS]chain_rule.
  rewrite fdistX_RV2.
  rewrite fst_RV2.
  rewrite -![in RHS]addrA.
  rewrite [RHS]addrCA.
  rewrite [RHS]addrC.
  rewrite [LHS]addrAC.
  congr (_ + _ + _).
  rewrite -opprD.
  congr (-_).
  have -> // : `p_[%Z, Y] = fdistX `p_[%Y, Z].
    by rewrite fdistX_RV2.
  have -> // : `p_Y = (`p_[%Y, Z])`1.
    by rewrite fst_RV2.
  exact:chain_rule.
transitivity (joint_entropy `p_[%X, Y] - entropy `p_Y).
  rewrite [LHS]addrAC.
  have -> // : cond_entropy `p_[%Z, Y] = 0.
    exact:fun_cond_entropy_ZY_eq0.
  have -> // : cond_entropy `p_[%Z, [%X, Y]] = 0.
    rewrite /Z.
    have -> // : f `o Y = (f \o snd) `o [%X, Y].
      by apply/boolp.funext => x //=.
    exact:fun_cond_entropy_ZY_eq0.
  by rewrite addrK.
rewrite joint_entropyC fdistX_RV2.
rewrite -/(joint_entropy `p_ [%Y, X]).
rewrite chain_rule.
rewrite fst_RV2 fdistX_RV2. 
rewrite addrAC.
by rewrite subrr add0r.
Qed.

End fun_cond_entropy_proof.

Section cinde_rv_comp_removal.

Variables (T: finType)(TX TY TZ TO: finType)(x: TX)(y: TY)(z: TZ).
Variables (P: R.-fdist T)(X: {RV P -> TX})(Y: {RV P -> TY})(Z: {RV P -> TZ})(O: {RV P -> TO}).
Variables (fy: TO -> TY)(fz: TO -> TZ).

Hypothesis XYZ_cinde: X _|_ (fy `o O) | (fz `o O).
Hypothesis YZneq0: `Pr[ [% fy `o O, fz `o O] = (y, z) ] != 0.

Lemma cinde_rv_comp_removal:
   `Pr[ X = x | (fz `o O) = z ] = `Pr[ X = x | [% fy `o O, fz `o O ] = (y, z) ].
Proof.
have H:=cinde_alt x (b:=y) (c:=z) XYZ_cinde YZneq0.
symmetry in H.
apply H.
Qed.
                                     
End cinde_rv_comp_removal.

Section inde_ex.

Variables (A: finType)(m n: nat)(P : R.-fdist A).
Variables (TX1 TX2 TX3 : finType).
Variables (s1 : {RV P -> TX1}) (s2 : {RV P -> TX2}) (r: {RV P -> TX3}).
Variable (op: TX1 -> TX2 -> TX3).

Let rv_op (rv1:{RV P -> TX1})(rv2:{RV P -> TX2}) : {RV P -> TX3}  :=
  fun p => op (rv1 p)(rv2 p).

Hypothesis s1_s2_indep : P|= s1 _|_ s2.
Hypothesis s1s2_r_indep : P|= [%s1, s2] _|_ r.

Lemma pr_eqM x : `Pr[ (rv_op s1 s2) = x ] = \sum_(a<-fin_img s1) (\sum_(b<-fin_img s2|op a b == x) `Pr[ s1 = a ] * `Pr[ s2 = b]).
Proof.
rewrite -[LHS]pr_eq_set1.
rewrite (reasoning_by_cases _ s1).
apply eq_bigr => a _.
rewrite (reasoning_by_cases _ s2).
rewrite [RHS]big_mkcond /=.
apply eq_bigr => b _.
case: ifPn.
  move/eqP => <-.
  rewrite -s1_s2_indep.
  rewrite setX1 setX1.
  rewrite pr_eq_set1.
  pose f (p:TX1 * TX2) := (op p.1 p.2, p.1, p.2). 
  have f_inj : injective f.
     by move => [x1 x2] [? ?] [] _ -> -> /=.
  by rewrite (pr_eq_comp _ _ f_inj ).
move => Hneq.
rewrite setX1 setX1.
rewrite pr_eq_set1.
rewrite pr_eqE.
apply/Pr_set0P.
move => a'.
rewrite !inE /=.
move/eqP => [].
move => Heq1 Heq2 Heq3.
by rewrite -Heq3 -Heq2 -Heq1 eqxx in Hneq.
Qed.

Lemma pr_eqM2 x y : `Pr[ [%(rv_op s1 s2), r] = (x, y) ] = \sum_(a<-fin_img s1) (\sum_(b<-fin_img s2|op a b == x) `Pr[ s1 = a ] * `Pr[ s2 = b ] * `Pr[ r = y ]).
Proof.
rewrite -[LHS]pr_eq_set1.
rewrite (reasoning_by_cases _ s1).
apply eq_bigr => a _.
rewrite (reasoning_by_cases _ s2).
rewrite [RHS]big_mkcond /=.
apply eq_bigr => b _.
case: ifPn.
  move/eqP => <-.
  rewrite -s1_s2_indep -s1s2_r_indep.
  rewrite setX1 setX1.
  rewrite pr_eq_set1.
  pose f (p:TX1 * TX2 * TX3) := (op p.1.1 p.1.2, p.2, p.1.1, p.1.2). 
  have f_inj : injective f.
     by move => [[x1 x2] ?] [[? ?] ?] [] _ -> -> -> /=.
  by rewrite (pr_eq_comp _ _ f_inj ).
move => Hneq.
rewrite setX1 setX1.
rewrite pr_eq_set1.
rewrite pr_eqE.
apply/Pr_set0P.
move => a'.
rewrite !inE /=.
move/eqP => [].
move => Heq1 _ Heq2 Heq3.
by rewrite -Heq3 -Heq2 -Heq1 eqxx in Hneq.
Qed.

(* Different from lemma 3.5: latter doesn't require s1 _|_ s2 yet
   "brings" independence to s1+s2

   (X, Y) _|_ R -> X + R _|_ Y.
*)
Lemma s1Ms2_r_indep : P|= (rv_op s1 s2) _|_ r.
Proof.
rewrite /inde_rv.
move => x y.
rewrite pr_eqM pr_eqM2.
rewrite big_distrl /=.
apply eq_bigr => a _.
rewrite big_distrl /=.
by apply eq_bigr => b _.
Qed.

(* TODO: addition lemma; actually we didn't use anything about mul above (any binop works) *)
(* reasoning_by_cases depends on another lemma that is not general before (2024/12/05) -- these proof are not trivial actually. *)

End inde_ex.

Arguments s1Ms2_r_indep [_ _ _ _ _] s1 s2 r.

Section neg_RV_lemmas.

Variables (T: finType)(m n: nat)(P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].
Hypothesis card_TX : #|TX| = m.+2. 

Lemma sub_RV_eq (U : finZmodType) (X Y : {RV P -> U}):
  X \- Y = X \+ neg_RV Y.
Proof.
apply: boolp.funext=> i.
rewrite /neg_RV .
rewrite /=. (* from null_fun to 0 *)
by rewrite sub0r.
Qed.

Lemma neg_RV_dist_eq (X : {RV P -> TX}):
  `p_ X = fdist_uniform card_TX ->
  `p_ X = `p_ (neg_RV X).
Proof.
rewrite /dist_of_RV=> Hunif.
apply/val_inj/ffunP => x /=. (* these two steps eq to apply: fdist_ext.*)
rewrite [RHS](_: _ = fdistmap X P (-x)).
  by rewrite !Hunif !fdist_uniformE.
rewrite /fdistmap !fdistbindE.
apply: eq_bigr=> a ?.
by rewrite /neg_RV !fdist1E /= sub0r eqr_oppLR.
Qed.

Lemma neg_RV_inde_eq (U : finType)(V : finZmodType)(X : {RV P -> U})(Y : {RV P -> V}):
  P |= X _|_ Y ->
  P |= X _|_ neg_RV Y.
Proof.
move => H.
have ->: X = idfun `o X by [].
have ->: neg_RV Y = (fun y: V => 0 - y ) `o Y.
  exact: boolp.funext => ? //=.
apply: inde_rv_comp.
exact: H.
Qed.

End neg_RV_lemmas.

Section dotproduct.

Variable TX : ringType.
Variable n : nat.
Variable T : finType.

Definition dotproduct (a b:'rV[TX]_n) := (a *m b^T)``_ord0.

Definition dotproduct_rv (P: R.-fdist T) (A B: {RV P -> 'rV[TX]_n}) : {RV P -> TX} :=
  fun p => dotproduct (A p) (B p).

End dotproduct.

Notation "u *d w" := (dotproduct u w).
Notation "u \*d w" := (dotproduct_rv u w).

Arguments dotproduct {TX n}. 

Section unif_lemmas.

Variables (T: finType)(m n: nat)(P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].
Variables (s1 s2: {RV P -> 'rV[TX]_n})(r: {RV P -> TX}).
Hypothesis card_TX : #|TX| = m.+2. 
Hypothesis pr_unif: `p_ r = fdist_uniform card_TX.
Hypothesis s1_s2_indep : P|= s1 _|_ s2.
Hypothesis s1s2_r_indep : P|= [%s1, s2] _|_ r.

Lemma ps1_dot_s2_r_unif:
  @dist_of_RV _ T P TX (s1 \*d s2 \- r) = fdist_uniform card_TX.
Proof.
have ->: s1 \*d s2 \- r = s1 \*d s2 \+ (neg_RV r).
  by apply: boolp.funext=> ?; rewrite /neg_RV /= sub0r.
have Hnegr1unif: `p_ (neg_RV r) = fdist_uniform card_TX.
  have Ha := neg_RV_dist_eq pr_unif.
  symmetry in Ha.
  rewrite Ha.
  by rewrite pr_unif.
apply: add_RV_unif; first by rewrite -neg_RV_dist_eq.
apply: s1Ms2_r_indep; first by [].
exact: neg_RV_inde_eq.
Qed.

End unif_lemmas.

Section pi2.
  
  
Section scalar_product_def.

Variables (T: finType)(m n: nat)(P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].

Definition SMC := 'rV[TX]_n -> 'rV[TX]_n -> (TX * TX).

Definition is_scalar_product (sp: SMC) :=
  forall (xa xb: 'rV[TX]_n),
  (sp xa xb).1 + (sp xa xb).2 = xa *d xb.

Definition step_eqn2_ya : ('rV[TX]_n * 'rV[TX]_n * TX * 'rV[TX]_n * TX) -> TX := fun z =>
  let '(xa, sa, ra, xb', t) := z in t - (xb' *d sa) + ra.

Definition step_eqn3_t_with_offset : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX * TX) -> TX := fun z =>
  let '(xa, xb, sa, sb, ra, rb) := z in (xa + sa) *d xb + rb.

Definition scalar_product (sa sb: 'rV[TX]_n)(ra yb: TX)(xa xb: 'rV[TX]_n): (TX * TX) :=
  let xa' := xa + sa in (* Alice -> Bob *)
  let xb' := xb + sb in (* Bob -> Alice *)
  let rb := sa *d sb - ra in (* Commodity -> Bob *)
  let t_with_offset := step_eqn3_t_with_offset (xa, xb, sa, sb, ra, rb) in
  let t :=  t_with_offset - yb in (* Bob -> Alice *)
  let ya := step_eqn2_ya (xa, sa, ra, xb', t) in
  (ya, yb).

Lemma dot_productC (aa bb : 'rV[TX]_n) : aa *d bb = bb *d aa.
Proof.
rewrite /dotproduct.
rewrite !mxE.
apply: eq_bigr=> *.
by rewrite !mxE mulrC.
Qed.

Lemma dot_productDr (aa bb cc : 'rV[TX]_n) :
  aa *d (bb + cc) = aa *d bb + aa *d cc.
Proof.
rewrite /dotproduct !mxE.
rewrite -big_split /=.
apply: eq_bigr=> *.
by rewrite !mxE mulrDr.
Qed.

(*   xb *d (xa + sa) + (sa *d sb - ra) - yb - (xb + sb) *d sa + ra + yb = xa *d xb *)
Lemma scalar_product_correct (sa sb: 'rV[TX]_n)(ra yb: TX) :
  is_scalar_product (scalar_product sa sb ra yb).
Proof.
move=>/=xa xb/=.
rewrite (dot_productC (xa+sa) xb).
rewrite !dot_productDr.
rewrite dot_productC.
rewrite (dot_productC xb sa).
rewrite (dot_productC (xb+sb) sa).
rewrite dot_productDr.
ring.
Qed.
(*rewrite (@GRing.add R).[AC(2*2)(1*4*(3*2))].*)

End scalar_product_def.

Section eqn2_proof.

Variables (T: finType)(m n: nat)(P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].
Variables (r1 r2 y2: {RV P -> TX})(x1 x2 s1 s2: {RV P -> 'rV[TX]_n}).
Let x1' := x1 \+ s1.
Let x2' := x2 \+ s2.
Let t := x1' \*d x2 \+ r2 \- y2.
Let y1 := t \- x2' \*d s1 \+ r1.
Hypothesis card_TX : #|TX| = m.+2.

Let f: ('rV[TX]_n * 'rV[TX]_n * TX * 'rV[TX]_n * TX) -> TX := fun z =>
  let '(xa, sa, ra, xb', t) := z in t - (xb' *d sa) + ra.

Let y1_fcomp :
  y1 = f `o [%x1, s1, r1, x2', t].
Proof. by apply boolp.funext. Qed.

Lemma eqn2_proof:
  `H(x2|[%[%x1, s1, r1, x2', t], y1]) = `H(x2|[%x1, s1, r1, x2', t]).
Proof. rewrite y1_fcomp. exact: fun_cond_removal. Qed.

End eqn2_proof.

Section eqn3_proof.

Variables (T: finType)(m n: nat)(P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].
Hypothesis card_TX: #|TX| = m.+2.

Variables (r1 r2 y2: {RV P -> TX})(x1 x2 s1 s2: {RV P -> 'rV[TX]_n}).
Let x1' := x1 \+ s1.
Let x2' := x2 \+ s2.
Let t := x1' \*d x2 \+ r2 \- y2.
Let y1 := t \- x2' \*d s1 \+ r1.

(* Selected variables from scalar-product only for eqn3.
   Each equation has a such "focus" from all variables in the scalar-product.
*)
Let O := [%x1, x2, s1, s2, r1, r2].

(* f1 `o X in mc_removal_pr must be x2 in eq3 *)
Let f1 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX * TX) -> 'rV[TX]_n := fun z =>
  let '(x1, x2, s1, s2, r1, r2) := z in x2.

(* f2 `o X in mc_removal_pr must be (x1, s1, r1, x2 + s2) in eq3 *)
Let f2 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX * TX) -> ('rV[TX]_n * 'rV[TX]_n * TX * 'rV[TX]_n) := fun z =>
  let '(x1, x2, s1, s2, r1, r2) := z in (x1, s1, r1, x2 + s2).

Definition fm : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX * TX) -> TX := fun z =>
  let '(xa, xb, sa, sb, ra, rb) := z in (xa + sa) *d xb + rb.

(* in mc_removal_pr they are named as Y1 Y2 Ym but we already have Y so renaming them. *)
Let Z := neg_RV y2.
Let W1 := f1 `o O.  (* x2; It is okay in Alice's view has it because only used in condition. *)
Let W2 := f2 `o O.  (* [%x1, s1, r1, x2']; cannot have x2, s2, r2 here otherwise Alice knows the secret*)
Let Wm := fm `o O.  (* t-(neg_RV y2); t before it addes (neg_RV y2) in WmZ*)
Let WmZ := Wm `+ neg_RV y2. (* t *)

Let eq_W1_RV:
  f1 `o O = x2.
Proof. by apply boolp.funext. Qed.

Let eq_W2_RV:
  f2 `o O = [%x1, s1, r1, x2'].
Proof. by apply boolp.funext. Qed.

Let eq_Wm_RV:
  fm `o O = (x1 \+ s1) \*d x2 \+ r2.
Proof. by apply boolp.funext => a . Qed.

Let eq_WmZ_RV:
  fm `o O `+ (neg_RV y2) = t.
Proof.
rewrite /t /add_RV /neg_RV eq_Wm_RV /x1' /=.
apply boolp.funext => a /=.
rewrite sub0r.
by [].
Qed.

(* Because y2 is generated by Bob -- not related to any other variables. *)
Hypothesis Z_O_indep : inde_rv Z O. 
Hypothesis pZ_unif : `p_ Z = fdist_uniform card_TX. (* Assumption in the paper. *)

Let Z_OO_indep:
  P |= Z _|_ [% O, O].
Proof.
have ->: [%O, O] = (fun o => (o, o)) `o O by [].
have ->: Z = idfun `o Z by [].
exact: inde_rv_comp.
Qed.

Let Z_WmW2_indep:
  P |= Z _|_ [%Wm, W2].
Proof.
rewrite /Wm /W2.
rewrite (_:Z = idfun `o Z) //.
apply: inde_RV2_comp.
exact: Z_OO_indep.
Qed.

Let Z_W2_indep:
  P |= Z _|_ W2.
Proof.
rewrite (_:Z = idfun `o Z) //.
apply: inde_rv_comp.
by exact: Z_O_indep.
Qed.

Let Z_Wm_indep:
  P |= Z _|_ Wm.
Proof.
rewrite /Wm.
rewrite (_:Z = idfun `o Z) //.
apply: inde_rv_comp.
by exact: Z_O_indep.
Qed.

Let W2_WmZ_indep :
  P |= W2 _|_ WmZ.
Proof.
rewrite cinde_rv_unit.
apply:cinde_rv_sym.
rewrite -cinde_rv_unit.
rewrite /inde_rv.
rewrite /WmZ.
move => x y.
have H := lemma_3_5' pZ_unif Z_WmW2_indep x y.
apply H.
Qed.

Let pWmZ_unif:
  `p_ (Wm `+ neg_RV y2) = fdist_uniform card_TX.
Proof.
have H_ZWM := Z_Wm_indep.
rewrite inde_rv_sym in H_ZWM.
have H := add_RV_unif Wm Z card_TX pZ_unif H_ZWM.
by exact H.
Qed.


Lemma eqn3_proof:
  `H(x2|[%x1, s1, r1, x2', t]) = `H(x2|[%x1, s1, r1, x2']).
Proof.
rewrite -eq_W1_RV -eq_W2_RV -eq_WmZ_RV eq_Wm_RV.
have Ha := cpr_cond_entropy pWmZ_unif W2_WmZ_indep.
apply Ha => w w2 wmz Hneq0.
by have := mc_removal_pr f1 Z_O_indep pZ_unif w Hneq0.
Qed.

End eqn3_proof.

Section eqn4_proof.

Variables (T: finType)(m n: nat)(P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].
Hypothesis card_TX: #|TX| = m.+2.
Hypothesis card_rVTX : #|'rV[TX]_n| = (m.+2 ^ n)%nat.-1.+1.
(* Coq cannot unify `(m.+2^n)%nat.-1.+1` in the definition of fdist_uniform and `(m.+2^n)%nat`,
   so we cannot assume `(m.+2^n)%nat` here.

   Check fdist_uniform (n:=(m.+2^n)%nat.-1) card_rVTX.
*)

Variables (r1: {RV P -> TX})(x1 x2 s1 s2: {RV P -> 'rV[TX]_n}).
Let x2' := x2 \+ s2.

Let eqn4 := `H(x2|[%x1, s1, r1, x2']) = `H(x2|[%x1, s1, r1]).

Let O := [%x1, s1, r1, x2].
Let Z := s2.
Hypothesis pZ_unif : `p_ Z = fdist_uniform card_rVTX. (* Assumption in the paper. *)

Let W1 := snd `o O.   (* x2 *)
Let W2 := fst `o O.   (* [%x1, s1, r1] *)
Let Wm := snd `o O.   (* x2 *)
Let WmZ := Wm `+ s2. (* x2' = x2 + s2 *)

Variable Z_O_indep : inde_rv Z O. 

Let Z_OO_indep:
  P |= Z _|_ [% O, O].
Proof.
have ->: [%O, O] = (fun o => (o, o)) `o O by [].
have ->: Z = idfun `o Z by [].
exact: inde_rv_comp.
Qed.

Let Z_WmW2_indep:
  P |= Z _|_ [%Wm, W2].
Proof.
rewrite /Wm /W2.
rewrite (_:Z = idfun `o Z) //.
apply: inde_RV2_comp.
exact: Z_OO_indep.
Qed.

Let Z_Wm_indep:
  P |= Z _|_ Wm.
Proof.
rewrite /Wm.
rewrite (_:Z = idfun `o Z) //. (* id vs. idfun*)
apply: inde_rv_comp.
by exact: Z_O_indep.
Qed.

Let pWmZ_unif:
  (@dist_of_RV _ T P 'rV[TX]_n WmZ) = fdist_uniform card_rVTX.
Proof.
rewrite /WmZ.
have H_ZWM := Z_Wm_indep.
rewrite inde_rv_sym in H_ZWM.
have H := add_RV_unif Wm Z card_rVTX pZ_unif H_ZWM.
by exact H.
Qed.

Let W2_WmZ_indep :
  P |= W2 _|_ WmZ.
Proof.
rewrite cinde_rv_unit.
apply:cinde_rv_sym.
rewrite -cinde_rv_unit.
rewrite /inde_rv.
rewrite /WmZ.
move => x y.
have H := (@lemma_3_5' _ _ 'rV[TX]_n P (m.+2 ^ n)%nat.-1 Wm Z W2 card_rVTX pZ_unif Z_WmW2_indep x y).
apply H.
Qed.

Lemma eqn4_proof: eqn4.
Proof.
rewrite /eqn4.
have Ha := cpr_cond_entropy pWmZ_unif W2_WmZ_indep _.
apply Ha => w w2 wmz Hneq0.
simpl in *.
by have := mc_removal_pr snd Z_O_indep pZ_unif w Hneq0.
Qed.
  
End eqn4_proof.

Section eqn4_1_proof.

Variables (T: finType)(m n: nat)(P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].
Hypothesis card_TX: #|TX| = m.+2.
Variables (r1: {RV P -> TX})(x1 x2 s1: {RV P -> 'rV[TX]_n}).
Hypothesis x2_indep : P |= [% x1, s1, r1] _|_ x2.

Lemma eqn_4_1_proof:
  `H(x2|[%x1, s1, r1]) = entropy `p_ x2.
Proof.
transitivity (joint_entropy `p_ [%x1, s1, r1, x2] - `H `p_ [%x1, s1, r1]).
  apply/eqP.
  rewrite eq_sym subr_eq addrC.
  apply/eqP.
  have -> : `p_[%x2, [%x1, s1, r1]] = fdistX `p_[%x1, s1, r1, x2].
    by rewrite fdistX_RV2.
  by rewrite chain_rule fst_RV2.
rewrite joint_entropy_indeRV.
  by rewrite addrAC subrr add0r.
by exact: x2_indep.
Qed.

End eqn4_1_proof.

Section pi2_alice_is_leakage_free_proof.

Variables (T: finType)(m n: nat)(P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].
Hypothesis card_TX : #|TX| = m.+2.
Hypothesis card_rVTX : #|'rV[TX]_n| = (m.+2 ^ n)%nat.-1.+1.

Variables (r1 y2: {RV P -> TX})(x1 x2 s1 s2: {RV P -> 'rV[TX]_n}).
Let x1' := x1 \+ s1.
Let x2' := x2 \+ s2.
Let r2  := s1 \*d s2 \- r1.
Let t := x1' \*d x2 \+ r2 \- y2.
Let y1 := t \- x2' \*d s1 \+ r1.
Let AliceView := [%x1, s1, r1, x2', t, y1].

Hypothesis y2_x1x2s1s2r1_eqn3_indep : P |= y2 _|_ [%x1, x2, s1, s2, r1].
Hypothesis s2_x1s1r1x2_eqn4_indep : P |= s2 _|_ [%x1, s1, r1, x2].
Hypothesis x1s2r1_x2_indep: P |= [% x1, s1, r1] _|_ x2.
Hypothesis neg_py2_unif : `p_ (neg_RV y2) = fdist_uniform card_TX.
Hypothesis ps2_unif : `p_ s2 = fdist_uniform card_rVTX.
  
Let negy2_x1x2s1s2r1r2_eqn3_indep :
  P |= neg_RV y2 _|_ [%x1, x2, s1, s2, r1, r2].
Proof.
pose f (a: ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX) ) := let '(x1, x2, s1, s2, r1) := a in (a, s1 *d s2 - r1).
by move/(inde_rv_comp (fun (a : TX) => 0 - a) f):y2_x1x2s1s2r1_eqn3_indep.
Qed.

Lemma pi2_alice_is_leakage_free_proof:
  `H( x2 | AliceView) = `H `p_x2.
Proof.
transitivity (`H( x2 | [% x1, s1, r1, x2', t])).
  by rewrite eqn2_proof.
transitivity (`H( x2 | [% x1, s1, r1, x2'])).
  by rewrite (eqn3_proof negy2_x1x2s1s2r1r2_eqn3_indep neg_py2_unif).
transitivity (`H( x2 | [% x1, s1, r1])).
  by rewrite (eqn4_proof ps2_unif s2_x1s1r1x2_eqn4_indep).
by rewrite eqn_4_1_proof.
Qed.

End pi2_alice_is_leakage_free_proof.

Section eqn6_proof.

Variables (T: finType)(m n: nat)(P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].
Hypothesis card_TX: #|TX| = m.+2.

Variables (r1 y2: {RV P -> TX})(x1 x2 s1 s2: {RV P -> 'rV[TX]_n}).
Let x1' := x1 \+ s1.
Let r2  := s1 \*d s2 \- r1.

Let O := [%x1, x2, s1, s2, r2, y2].

Let f1 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX * TX) -> 'rV[TX]_n := fun z =>
  let '(x1, _, _, _, _, _) := z in x1.

Let f2 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX * TX) -> ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX) := fun z =>
  let '(x1, x2, s1, s2, r2, y2) := z in (x2, s2, x1 + s1, r2).

Let fm : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX * TX) -> TX := fun z =>
  let '(_, _, _, _, _, y2) := z in y2.

Let W1 := f1 `o O.  (* x1; It is okay in Bob's view has it because only used in condition. *)
Let W2 := f2 `o O.  (* [%x2, s2, x1', r2]; cannot have x1, s1 here otherwise Bob knows the secret*)
Let Wm := fm `o O.  (* y2 *)

Let eq_W1_RV:
  f1 `o O = x1.
Proof. by apply boolp.funext. Qed.

Let eq_W2_RV:
  f2 `o O = [%x2, s2, x1', r2].
Proof. by apply boolp.funext. Qed.

Let eq_Wm_RV:
  fm `o O = y2.
Proof. by apply boolp.funext. Qed.

(* Because y2 (Wm) is generated by Bob; not related to x2, s2, x1, s1, r2 at all*)
Hypothesis W2_Wm_indep: P|= W2 _|_ Wm.
(* Because x1 (W1) is from Alice and y2 (Wm) is from Bob *)
Hypothesis W1_Wm_indep: P|= W1 _|_ Wm.

(* Because y2 (Wm) is generated by Bob; not related to x2, s2, x1, s1, r2 at all*)
Hypothesis W1W2_Wm_indep: P|= [%W1, W2] _|_ Wm.
(* TODO: deduce other indeps from this one. *)

(* In the paper, y2 (Wm) is uniform distributed*)
Hypothesis pWm_unif: `p_ Wm = fdist_uniform card_TX.

Let W1WmW2_cinde : W1 _|_ Wm | W2.
Proof.
apply: inde_RV2_cinde. by exact: W1W2_Wm_indep.
Qed.

Lemma eqn6_proof:
  `H(x1|[%[%x2, s2, x1', r2], y2]) = `H(x1|[%x2, s2, x1', r2]).
Proof.
rewrite -eq_W1_RV -eq_W2_RV -eq_Wm_RV.
have Ha := cpr_cond_entropy pWm_unif W2_Wm_indep _.
apply Ha => w w2 wm Hneq0.
simpl in *.
rewrite pr_eq_pairC in Hneq0.
have Hb:=(@cinde_alt _ _ _ _ _ _ W1 Wm W2 w wm w2 W1WmW2_cinde Hneq0).
rewrite -/W1.
rewrite cpr_RV2_sym.
exact: Hb.
Qed.

End eqn6_proof.

Section eqn7_proof.

Variables (T: finType)(m n: nat)(P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].
Hypothesis card_TX: #|TX| = m.+2.

Variables (r1: {RV P -> TX})(x1 x2 s1 s2: {RV P -> 'rV[TX]_n}).
Let x1' := x1 \+ s1.
Let r2  := s1 \*d s2 \- r1.

Let O := [%x1, x2, s1, s2, r2].

Let f1 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX) -> 'rV[TX]_n := fun z =>
  let '(x1, x2, s1, s2, r2) := z in x1.

Let f2 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX) -> ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n) := fun z =>
  let '(x1, x2, s1, s2, r2) := z in (x2, s2, x1 + s1).

Let fm : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX) -> TX := fun z =>
  let '(x1, x2, s1, s2, r2) := z in r2.

Let W1 := f1 `o O.  (* x1; It is okay in Bob's view has it because only used in condition. *)
Let W2 := f2 `o O.  (* [%x2, s2, x1']; cannot have x1, s1 here otherwise Bob knows the secret*)
Let Wm := fm `o O.  (* r2 *)

Let eq_W1_RV:
  f1 `o O = x1.
Proof. by apply boolp.funext. Qed.

Let eq_W2_RV:
  f2 `o O = [%x2, s2, x1'].
Proof. by apply boolp.funext. Qed.

Let eq_Wm_RV:
  fm `o O = r2.
Proof. by apply boolp.funext. Qed.

Hypothesis W2_Wm_indep: P|= W2 _|_ Wm.
Hypothesis W1W2_Wm_indep : P|= [%W1, W2] _|_ Wm.

(* In the paper, r2 (Wm) is uniform distributed*)
Hypothesis pWm_unif: `p_ Wm = fdist_uniform card_TX.

Let W1WmW2_cinde : W1 _|_ Wm | W2.
Proof. apply: inde_RV2_cinde. by exact: W1W2_Wm_indep.
Qed.

Lemma eqn7_proof:
  `H(x1|[%[%x2, s2, x1'], r2]) = `H(x1|[%x2, s2, x1']).
Proof.
rewrite -eq_W1_RV -eq_W2_RV -eq_Wm_RV.
have Ha := cpr_cond_entropy pWm_unif W2_Wm_indep _.
apply Ha => w w2 wm Hneq0.
simpl in *.
rewrite pr_eq_pairC in Hneq0.
have Hb:=(@cinde_alt _ _ _ _ _ _ W1 Wm W2 w wm w2 W1WmW2_cinde Hneq0).
rewrite -/W1.
rewrite cpr_RV2_sym. 
apply Hb.
Qed.

(* Although in the paper eqn_7 needs Theorem 3.7 to prove,
   it actually only needs cinde_alt. Because r2 is not Wm+Z but just Wm.
*)
End eqn7_proof.

Section eqn8_proof.

Variables (T: finType)(m n: nat)(P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].
Hypothesis card_TX: #|TX| = m.+2.
Hypothesis card_rVTX: #|'rV[TX]_n| = (m.+2 ^ n)%nat.-1.+1.

Variables (x1 x2 s1 s2: {RV P -> 'rV[TX]_n}).
Let x1' := x1 \+ s1.

Let O := [%x1, x2, s1, s2].

(* f1 `o X in mc_removal_pr must be x1 in eqn8 *)
Let f1 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n) -> 'rV[TX]_n := fun z =>
  let '(x1, x2, s1, s2) := z in x1.

(* f2 `o X in mc_removal_pr must be (x2, s2) in eqn8 *)
Let f2 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n) -> ('rV[TX]_n * 'rV[TX]_n) := fun z =>
  let '(x1, x2, s1, s2) := z in (x2, s2).

(* (fm `o X)+Z in mc_removal_pr must be x1 in eqn8 *)
Let fm : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n) -> 'rV[TX]_n := fun z =>
  let '(x1, x2, s1, s2) := z in x1.

Let Z := s1.
Hypothesis pZ_unif : `p_ Z = fdist_uniform card_rVTX.

Let W1 := f1 `o O.   (* x1 *)
Let W2 := f2 `o O.   (* [%x2, s2] *)
Let Wm := fm `o O.   (* x1 *)
Let WmZ := fm `o O `+ s1.   (* must be x1': x1' = x1 + s1 *)

Let eq_W1_RV:
  f1 `o O = x1.
Proof. by apply boolp.funext. Qed.

Let eq_W2_RV:
  f2 `o O = [%x2, s2].
Proof. by apply boolp.funext. Qed.

Let eq_Wm_RV:
  fm `o O = x1.
Proof. by apply boolp.funext. Qed.

Let eq_WmZ_RV:
  fm `o O `+ s1 = x1'.
Proof. by rewrite /add_RV /neg_RV eq_Wm_RV /x1' //=. Qed.

Hypothesis Z_O_indep : inde_rv Z O. 

(* Because s1 and x1 are generated by different participants *)
Hypothesis Z_WmZ_indep: P |= Z _|_ WmZ.

(* Because [%x2, s2] and x1 are generated by different participants *)
Hypothesis W2_WmZ_indep: P |= W2 _|_ WmZ.

Let pWmZ_unif :
  `p_ WmZ = fdist_uniform card_rVTX.
Proof.
apply: add_RV_unif; last first.
  rewrite (_:s1 = idfun `o s1) //.
  apply: inde_rv_comp.
  rewrite inde_rv_sym.
  exact: Z_O_indep. 
exact: pZ_unif.
Qed.

Lemma eqn8_proof:
  `H(x1|[%[%x2, s2], x1']) = `H(x1|[%x2, s2]).
Proof.
rewrite -eq_W1_RV -eq_W2_RV -eq_WmZ_RV.
rewrite -/W1 -/W2 -/WmZ.
have Ha := cpr_cond_entropy pWmZ_unif W2_WmZ_indep _.
apply: Ha => w w2 wm Hneq0.
rewrite -/W1.
by have := (mc_removal_pr f1 Z_O_indep pZ_unif w Hneq0).
Qed.
  
End eqn8_proof.

Section eqn8_1_proof.

Variables (T: finType)(m n: nat)(P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].
Hypothesis card_TX: #|TX| = m.+2.
Hypothesis card_rVTX: #|'rV[TX]_n| = m.+2.

Variables (x1 x2 s2: {RV P -> 'rV[TX]_n}).

Hypothesis x2s2_x1_indep : P |= [% x2, s2] _|_ x1.

Lemma eqn_8_1_proof:
  `H(x1|[%x2, s2]) = entropy `p_ x1.
Proof.
transitivity (joint_entropy `p_ [%x2, s2, x1] - entropy `p_ [%x2, s2]).
  apply/eqP.
  rewrite eq_sym subr_eq addrC.
  apply/eqP.
  have -> : `p_ [%x1, [%x2, s2]] = fdistX `p_ [%[%x2, s2], x1].
    by rewrite fdistX_RV2.
  by rewrite chain_rule fst_RV2.
rewrite joint_entropy_indeRV.
  by rewrite addrAC subrr add0r.
by exact: x2s2_x1_indep.
Qed.

End eqn8_1_proof.

Section pi2_bob_view_is_leakage_free_proof.

Variables (T: finType)(m n: nat)(P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].
Hypothesis card_TX: #|TX| = m.+2.
Hypothesis card_rVTX: #|'rV[TX]_n| = (m.+2 ^ n)%nat.-1.+1.
Variables (r1 y2: {RV P -> TX})(x1 x2 s1 s2: {RV P -> 'rV[TX]_n}).
Let x1' := x1 \+ s1.
Let r2  := s1 \*d s2 \- r1.
  
(* Hypothese from the paper. *)
Hypothesis x2s2_x1'_indep : P |= [% x2, s2] _|_ x1'.
Hypothesis x2s2x1'r2_y2_eqn6_indep : P |= [%x2, s2, x1', r2] _|_ y2.
Hypothesis x1x2s2x1'r2_y2_eqn6_indep : P |= [%x1, [%x2, s2, x1', r2]] _|_ y2.
Hypothesis x2_s2_x1'_r2_eqn7_indep : P |= [%x2, s2, x1'] _|_ r2.
Hypothesis x1x2_s2_x1'_r2_eqn7_indep : P |= [%x1, [%x2, s2, x1']] _|_ r2.
(* TODO: Reduce: longer one can imply others *)
Hypothesis s1_x1x2s1s2_eqn8_indep : P |= s1 _|_ [%x1, x2, s1, s2].
Hypothesis x2s2_x1_indep : P |= [% x2, s2] _|_ x1.

Hypothesis s1s2_r1_indep : P|= [%s1, s2] _|_ r1.
Hypothesis s1_s2_indep : P|= s1 _|_ s2.
Hypothesis pr1_unif : `p_ r1 = fdist_uniform card_TX.
Hypothesis py2_unif : `p_ y2 = fdist_uniform card_TX.
Hypothesis ps1_unif : `p_ s1 = fdist_uniform card_rVTX.
  
Let pr2_unif := ps1_dot_s2_r_unif pr1_unif s1_s2_indep s1s2_r1_indep.
Let BobView := [%x2, s2, x1', r2, y2].

Lemma pi2_bob_is_leakage_free_proof:
  `H( x1 | BobView) = `H `p_ x1.
Proof.
transitivity (`H( x1 | [% x2, s2, x1', r2])).
  by rewrite (eqn6_proof x2s2x1'r2_y2_eqn6_indep x1x2s2x1'r2_y2_eqn6_indep py2_unif).
transitivity (`H(x1|[%x2, s2, x1'])).
  by rewrite (eqn7_proof x2_s2_x1'_r2_eqn7_indep x1x2_s2_x1'_r2_eqn7_indep pr2_unif).
transitivity (`H(x1|[%x2, s2])).
  by rewrite (eqn8_proof ps1_unif s1_x1x2s1s2_eqn8_indep).
by rewrite eqn_8_1_proof.
Qed.

End pi2_bob_view_is_leakage_free_proof.

End pi2.

(* TODO: Using graphoid for combinations of independ random variables. *)
Section mutual_indep.

(* Pairwise independence: Any collection of mutually independent random variables is pairwise independent

(But pairwise independence does not imply mutual independence.

How to express "a collection of any types of mutual independent random variables"?
RV2 is a collection. But it is not a sequence so cannot be used to generate arbitrary pairs of RVs.
Should RV2 supports to be traversed as a sequence??
*)

Variables (A: finType)(m n: nat)(P : R.-fdist A).
Variables (TX VX: finType).
Variables (x1 x2 s1 s2 r1 y2: {RV P -> TX}).
  
Hypothesis Hinde : {homo nth x1 [:: x1; x2; s1; s2] : i j / i < j >-> inde_rv i j}%nat.

Lemma x1_x2_inde:
    P|= x1 _|_ x2.
Proof.
have H := @Hinde 0 1.
apply H.
rewrite //.
Qed.

Hypothesis Hinde_all : forall i j, P|= nth x1 [:: x1; x2; s1; s2] i _|_ nth r1 [:: r1; y2] j.

Lemma x1_r1_inde:
    P|= x1 _|_ r1.
Proof.
have H := @Hinde_all 0 0.
apply H.
Qed.
  
End mutual_indep.

End smc_entropy_proofs.
