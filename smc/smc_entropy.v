From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
Require Import Reals Lra.
From mathcomp Require Import Rstruct.
Require Import ssrR Reals_ext realType_ext logb ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy smc graphoid.

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
Local Open Scope vec_ext_scope.

Reserved Notation "u *d w" (at level 40).
Reserved Notation "u \*d w" (at level 40).

Module smc_entropy_proofs.

  
Section extra_pr.

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
rewrite !coqRE.
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

End extra_pr.

Section cond_entropy_RV_dist.

(*

Variables (A B : finType) (QP : {fdist B * A}).

(* H(Y|X = x), see eqn 2.10 *)
Definition cond_entropy1 a := - \sum_(b in B)
  \Pr_QP [ [set b] | [set a] ] * log (\Pr_QP [ [set b] | [set a] ]).

Let P := QP`2.

(*eqn 2.11 *)
Definition cond_entropy := \sum_(a in A) P a * cond_entropy1 a.

Lemma cond_entropyE : cond_entropy = - \sum_(a in A) \sum_(b in B)
  PQ (a, b) * log (\Pr_QP [ [set b] | [set a]]).
Proof.

Variables (U A B : finType) (P : {fdist U}) (X : {RV P -> A}) (Y : {RV P -> B}).

Definition cond_entropy1_RV a := `H (`p_[% X, Y] `(| a )).

Lemma cond_entropy1_RVE a : (`p_[% X, Y])`1 a != 0 ->
  cond_entropy1_RV a = cond_entropy1 `p_[% Y, X] a.
Proof.
move=> a0.
rewrite /cond_entropy1_RV /cond_entropy1 /entropy; congr (- _).
by apply: eq_bigr => b _; rewrite jfdist_condE// fdistX_RV2.
Qed.

*)
  
Lemma eq_cond_entropy_to_cond_entropy1 (A1 A2 B1 B2: finType) (QP: {fdist A2 * A1}) (TS: {fdist B2 * B1}) a b:
  cond_entropy QP = cond_entropy TS -> cond_entropy1 QP a = cond_entropy1 TS b.
Proof.
rewrite /cond_entropy.
move => H.
Admitted.

End cond_entropy_RV_dist.

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
About boolp.eq_forall.

Lemma joint_entropy_indeRV (X : {RV P -> TX}) (Y : {RV P -> TY}):
  inde_rv X Y -> joint_entropy `p_[%X, Y] = `H (`p_X) + `H (`p_Y).
Proof.
rewrite /joint_entropy.
rewrite /entropy.
rewrite !coqRE.
transitivity (- (\sum_(a in TX) \sum_(b in TY) `p_ [% X, Y] (a, b) * log (`p_ X a * `p_ Y b))).
  congr (- _).
  rewrite pair_big /=.
  apply eq_bigr => -[a b] _ /=.
  congr (_ * log _).
  rewrite coqRE.
  by apply inde_rv_alt. (* cannot `apply: ` but can `apply `*)
transitivity (
  - (\sum_(a in TX) \sum_(b in TY) `p_ [%X, Y] (a, b) * log (`p_ X a))
  - (\sum_(a in TX) \sum_(b in TY) `p_ [%X, Y] (a, b) * log (`p_ Y b))).
  rewrite -[RHS]oppRB.
  congr (- _).
  rewrite -addR_opp.
  rewrite oppRK.
  rewrite -big_split /=. (* merge two \sum_a...\sum_a in RHS so we can apply eq_bigr*)
  apply eq_bigr => a _.
  rewrite -big_split /=.
  apply eq_bigr => b _.
  have [->|H0] := eqVneq (`p_ [%X, Y](a, b)) 0.
    rewrite !mul0r.
    by rewrite add0R.
  rewrite mulRC.
  rewrite logM //. (* from log (x*y) to log x + log y *)
  - by rewrite [LHS]mulRDr.
  - rewrite -pr_eqE'.
    rewrite pr_eqE Pr_gt0P -pr_eqE.
    move: H0.
    rewrite -pr_eqE' pr_eq_pairC coqRE.
    exact: fst_RV2_neq0.
  - rewrite -pr_eqE'.
    rewrite pr_eqE Pr_gt0P -pr_eqE.
    move: H0.
    rewrite -pr_eqE' coqRE.
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
  

Variables (T TW TV1: finType) (TV2: finZmodType) (P : R.-fdist T).
Variable n : nat.
Notation p := n.+2.
Variables (W: {RV P -> TW}) (V1: {RV P -> TV1}) (V2: {RV P -> TV2}).

Hypothesis card_A : #|TV2| = n.+1.
Hypothesis pV2_unif : `p_ V2 = fdist_uniform card_A.
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
    move:(@Pr_domin_setX TV1 TV2 (`p_ [%V1, V2]) [set v1] [set v2]).
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
  rewrite card_A.
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

Hypothesis H : forall w v1 v2,
    `Pr[ W = w | V1 = v1 ] = `Pr[ W = w | [%V1, V2] = (v1, v2) ].

Lemma snd_extra_indep v1 v2 :
  (`p_ [% W, [% V1, V2]])`2 (v1, v2) = (`p_ [% W, V1])`2 v1 * `p_V2 v2.
Proof.
rewrite !fdist_sndE big_distrl /=.
apply eq_bigr => w _.
have := H w v1 v2.
rewrite !cpr_eqE V1V2indep -!pr_eqE' !coqRE.
have [Hv1 _|Hv1] := eqVneq `Pr[V1 = v1] 0.
  rewrite [in RHS]pr_eq_pairC [in LHS]pr_eq_pairC -pr_eq_pairA.
  by rewrite !(pr_eq_domin_RV2 _ _ Hv1) mul0r.
have [Hv2 _|Hv2] := eqVneq `Pr[V2 = v2] 0.
  rewrite Hv2 mulr0 pr_eq_pairC pr_eq_domin_RV2 //.
  by rewrite pr_eq_pairC pr_eq_domin_RV2.
move/(f_equal (fun x => x * (`Pr[V1 = v1] * `Pr[V2 = v2]))).
rewrite -[in RHS]mulrA mulVf //; last by rewrite mulf_eq0 negb_or Hv1.
by rewrite mulrA -[X in X * _]mulrA mulVf // !mulr1.
Qed.

Lemma cpr_cond_entropy : `H(W | [%V1, V2]) = `H(W | V1).
Proof.
rewrite /cond_entropy /=.
under eq_bigl do rewrite inE /=.
set f : TV1 -> TV2 -> R := fun v1 v2 =>
  (`p_[% W, V1])`2 v1 * `p_V2 v2 * cond_entropy1 `p_ [% W, V1] v1.
transitivity (\sum_a f a.1 a.2).
  apply eq_bigr => -[i j] _.
  rewrite /f /=.
  have [Ha|Ha] := eqVneq ((`p_ [% W, V1])`2 i * `p_V2 j) 0.
    by rewrite Ha snd_extra_indep Ha !coqRE !mul0r.
  rewrite snd_extra_indep -[in LHS]cond_entropy1_RVE; last first.
    by rewrite -fdistX2 fdistX_RV2 snd_extra_indep.
  rewrite -cpr_cond_entropy1_RV // cond_entropy1_RVE ?coqRE //.
  by apply: contra Ha; rewrite mulf_eq0 -fdistX1 fdistX_RV2 => ->.
rewrite -pair_bigA /=.
apply: eq_bigr => v1 _.
by rewrite /f -big_distrl -big_distrr /= FDist.f1 mulr1 coqRE.
Qed.
End pr_entropy.

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
  rewrite -coqRE.
  by rewrite -chain_rule.
transitivity (joint_entropy `p_[%[%X, Y], Z] - entropy `p_[%Y, Z]). (* H(Y,f(Y),X) -> H(X,Y,f(Y))*)
  rewrite joint_entropyC.
  rewrite /joint_entropy.
  rewrite joint_entropyA.
  by rewrite fdistX_RV2 fdistA_RV3 .
transitivity (joint_entropy `p_[%X,Y] + cond_entropy `p_[%Z, [%X, Y]] - entropy `p_Y - cond_entropy `p_[%Z, Y]).
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
rewrite chain_rule coqRE.
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


Section pi2.

Variable m : nat.
Let TX := [the finComRingType of 'I_m.+2]. (* not .+1: at least need 0 and 1 *)

Variables (T: finType).
Variable P : R.-fdist T.
Variable n : nat.
Notation p := m.+2.

Variables (x1 x2 s1 s2 : {RV P -> 'rV[TX]_n}).
Variables (y2 r1: {RV P -> TX}).

Definition dotproduct (a b:'rV[TX]_n) := (a *m b^T)``_ord0.
Definition dotproduct_rv (A B:{RV P -> 'rV[TX]_n}) := fun p => dotproduct (A p) (B p).

Local Notation "u *d w" := (dotproduct u w).
Local Notation "u \*d w" := (dotproduct_rv u w).

Let x1' : {RV P -> 'rV[TX]_n} := x1 \+ s1.
Let x2' : {RV P -> 'rV[TX]_n} := x2 \+ s2.

Let r2  : {RV P -> TX} := s1 \*d s2 \+ r1.
Let t : ({RV P -> TX}) := x1'\*d x2 \+ r2 \- y2.
Let y1 : ({RV P -> TX}) := t \- x2' \*d s1 \+ r1.

(* Because we need values of random variables when expressing Pr(A = a). *)
Variable (_x1 _x2 _x1' _x2' _s1 _s2: 'rV[TX]_n)(_t _r1 _r2 _y1 _y2: TX).

Let AliceView := [%x1, s1, r1, x2', t, y1].

Let eqn1 := cond_entropy1_RV AliceView x2 (_x1, _s1, _r1, _x2', _t, _y1).

Let BobView := [%x2, s2, x1', r2, y2].

Let eqn5 := cond_entropy1_RV BobView x2 (_x2, _s2, _x1', _r2, _y2).

Section eqn2_proof.

Let f : ('rV[TX]_n * 'rV[TX]_n * TX * 'rV[TX]_n * TX) -> TX := fun z =>
  let '(x1, s1, r1, x2', t) := z in t - (x2' *d s1) + r1.

Lemma y1_fcomp :
  y1 = f `o [%x1, s1, r1, x2', t].
Proof. by apply boolp.funext. Qed.

Lemma eqn2_dist:
  `H(x2|[%[%x1, s1, r1, x2', t], y1]) = `H(x2|[%x1, s1, r1, x2', t]).
Proof. rewrite y1_fcomp. exact: fun_cond_removal. Qed.

Hypothesis Qneq0: (`p_ [% x1, s1, r1, x2', t, x2])`1 (_x1, _s1, _r1, _x2', _t) != 0.
Hypothesis Tneq0: (`p_ [% AliceView, x2])`1 (_x1, _s1, _r1, _x2', _t, _y1) != 0.

Lemma eqn2:
  cond_entropy1_RV AliceView x2 (_x1, _s1, _r1, _x2', _t, _y1) =
  cond_entropy1_RV [%x1, s1, r1, x2', t] x2 (_x1, _s1, _r1, _x2', _t).
Proof.
rewrite !cond_entropy1_RVE.
apply eq_cond_entropy_to_cond_entropy1.
apply eqn2_dist.
by exact: Qneq0.
by exact: Tneq0.
Qed.

End eqn2_proof.

Section eqn3_proof.

(* All variables t will be used. *)
(* Because in mc_removal_pr, only one joint random varaible can be fed to the lemma,
   for all composed f1, f2, fm which are also fed to the lemma.
   We need a common set of all used random variables.

   And note that r2 is not independent from others; it is calculated from s1, s2 and r1.
*)
Let O := [%x1, x2, s1, s2, r1, r2].

(* Random variables that indepent to each other. *)
Let O_indep := [%x1, x2, s1, s2, r1, y2].

(* f1 `o X in mc_removal_pr must be x2 in eq3 *)
Let f1 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX * TX) -> 'rV[TX]_n := fun z =>
  let '(x1, x2, s1, s2, r1, r2) := z in x2.

(* f2 `o X in mc_removal_pr must be (x1, s1, r1, x2 + s2) in eq3 *)
Let f2 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX * TX) -> ('rV[TX]_n * 'rV[TX]_n * TX * 'rV[TX]_n) := fun z =>
  let '(x1, x2, s1, s2, r1, r2) := z in (x1, s1, r1, x2 + s2).

(* (fm `o X)+Z in mc_removal_pr must be t+(-y2) in eq3 *)
Let fm : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX * TX) -> TX := fun z =>
  let '(x1, x2, s1, s2, r1, r2) := z in (x1 + s1) *d x2 + r2.

(* in mc_removal_pr they are named as Y1 Y2 Ym but we already have Y so renaming them. *)
Let Z := y2.
Let W1 := f1 `o O.  (* x2; It is okay in Alice's view has it because only used in condition. *)
Let W2 := f2 `o O.  (* [%x1, s1, r1, x2']; cannot have x2, s2, r2 here otherwise Alice knows the secret*)
Let Wm := fm `o O.  (* t-(neg_RV y2); t before it addes y2 in WmZ*)
Let WmZ := Wm `+ y2. (* t; It should be (neg_RV y2) but neg_RV requires the domain is R, not TX*)

Hypothesis card_TX : #|TX| = m.+1.

(* Because y2 is generated by Bob -- not related to any other variables. *)
Variable Z_O_indep : inde_rv Z O. 
Variable Z_WmW2_indep : inde_rv Z [%Wm, W2]. (* TODO: the same combination problem; generate them instead of listing them like this. *)
Variable pZ_unif : `p_ Z = fdist_uniform card_TX. (* Assumption in the paper. *)


Let Z_W2_indep:
  P |= Z _|_ W2.
Proof.
rewrite /W2.
rewrite (_:Z = idfun `o Z) //. (* id vs. idfun*)
apply: inde_rv_comp.
by exact: Z_O_indep.
Qed.

Let Z_Wm_indep:
  P |= Z _|_ Wm.
Proof.
rewrite /Wm.
rewrite (_:Z = idfun `o Z) //. (* id vs. idfun*)
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
have H := (@lemma_3_5' _ _ TX P m Wm Z W2 card_TX pZ_unif Z_WmW2_indep x y).
apply H.
Qed.

Let pWmZ_unif:
  `p_ WmZ = fdist_uniform card_TX.
Proof.
rewrite /WmZ.
have H_ZWM := Z_Wm_indep.
rewrite inde_rv_sym in H_ZWM.
have H := add_RV_unif Wm Z card_TX pZ_unif H_ZWM.
by exact H.
Qed.

Section eqn3_entropy1.

Variable (w1 : 'rV[TX]_n) (w2 : 'rV[TX]_n * 'rV[TX]_n * TX * 'rV[TX]_n) (wmz : 'I_p) .

Hypothesis Hneq0 : `Pr[ [%WmZ, W2] = (wmz, w2) ] != 0.

Lemma eqn3:
  cond_entropy1_RV [%W2, WmZ] W1 (w2, wmz) = cond_entropy1_RV W2 W1 w2.
Proof.
have Ha := (@cpr_cond_entropy1_RV _ _ _ TX P m W1 W2 WmZ card_TX pWmZ_unif W2_WmZ_indep w2 wmz).
symmetry in Ha.
apply Ha => w.
have Hb :=(@mc_removal_pr _ _ _ _ TX P m O Z f1 f2 fm Z_O_indep card_TX pZ_unif w w2 wmz Hneq0).
symmetry in Hb.
apply Hb.
Qed.

End eqn3_entropy1.

Lemma eqn3_dist:
  `H(x2|[%[%x1, s1, r1, x2'], t]) = `H(x2|[%x1, s1, r1, x2']).
Proof.
rewrite /cond_entropy /=.
under eq_bigr => a _.
  rewrite (surjective_pairing a) /=.
  rewrite fdist_sndE /=.
  under eq_bigr => i _.
    rewrite -pr_eqE'.
  About pr_eqE'.
Abort. (* Aborted because this needs mapping from dist back to RV, but folding back by rewrite fails.*)

End eqn3_proof.

Section eqn4_proof.

(* Almost the same in eqn3 except r2 is not used here. *)
Let O := [%x1, x2, s1, s2, r1].

(* f1 `o X in mc_removal_pr must be x2 in eq3 *)
Let f1 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX) -> 'rV[TX]_n := fun z =>
  let '(x1, x2, s1, s2, r1) := z in x2.

(* f2 `o X in mc_removal_pr must be (x1, s1, r1) in eq3 *)
Let f2 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX) -> ('rV[TX]_n * 'rV[TX]_n * TX) := fun z =>
  let '(x1, x2, s1, s2, r1) := z in (x1, s1, r1).

(* (fm `o X)+Z in mc_removal_pr must be x2+s2 in eq4 *)
Let fm : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX) -> 'rV[TX]_n := fun z =>
  let '(x1, x2, s1, s2, r1) := z in x2.

Let Z := s2.
Let W1 := f1 `o O.   (* x2 *)
Let W2 := f2 `o O.   (* [%x1, s1, r1]*)
Let Wm := fm `o O.   (* x2'-s2*)
Let WmZ := Wm `+ s2. (* x2'*)

Variable Z_O_indep : inde_rv Z O. 
Variable Z_WmW2_indep : inde_rv Z [%Wm, W2].

Variable (w2 : 'rV[TX]_n * 'rV[TX]_n * TX) (wmz : 'rV[TX]_n) .

(* Means we at least have (0,0...0) and (1,1,..1) of 'rV[TX]_n,
   so 'rV[TX]_n is a ring.
*) 
Hypothesis card_Z : #|'rV[TX]_n| = m.+2.
Hypothesis pZ_unif : `p_ Z = fdist_uniform card_Z. (* Assumption in the paper. *)
Hypothesis Hneq0 : `Pr[ [%WmZ, W2] = (wmz, w2) ] != 0.

Let Z_Wm_indep:
  P |= Z _|_ Wm.
Proof.
rewrite /Wm.
rewrite (_:Z = idfun `o Z) //. (* id vs. idfun*)
apply: inde_rv_comp.
by exact: Z_O_indep.
Qed.

Let pWmZ_unif:
  (@dist_of_RV T P 'rV[TX]_n WmZ) = fdist_uniform card_Z.
Proof.
rewrite /WmZ.
have H_ZWM := Z_Wm_indep.
rewrite inde_rv_sym in H_ZWM.
have H := add_RV_unif Wm Z card_Z pZ_unif H_ZWM.
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
have H := (@lemma_3_5' _ _ 'rV[TX]_n P m.+1 Wm Z W2 card_Z pZ_unif Z_WmW2_indep x y).
apply H.
Qed.

Lemma eqn4:
  cond_entropy1_RV [%W2, WmZ] W1 (w2, wmz) = cond_entropy1_RV W2 W1 w2.
Proof.
have Ha := (@cpr_cond_entropy1_RV _ _ _ 'rV[TX]_n P m.+1 W1 W2 WmZ card_Z pWmZ_unif W2_WmZ_indep w2 wmz).
symmetry in Ha.
apply Ha => w.
have Hb :=(@mc_removal_pr _ _ _ _ 'rV[TX]_n P m.+1 O Z f1 f2 fm Z_O_indep card_Z pZ_unif w w2 wmz Hneq0).
symmetry in Hb.
apply Hb.
Qed.
  
End eqn4_proof.

Section pi2_alice_view_is_leakage_free.

Hypothesis x2_indep : P |= [% x1, s1, r1] _|_ x2.

Lemma eqn_4_1:
  `H(x2|[%x1, s1, r1]) = entropy `p_ x2.
Proof.
transitivity (joint_entropy `p_ [%x1, s1, r1, x2] - entropy `p_ [%x1, s1, r1]).
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

Lemma pi2_alice_view_is_leakage_free_proof:
  eqn1 = entropy `p_ x2.
Proof.
rewrite /eqn1.
rewrite eqn2.
Fail rewrite eqn3.
Abort.

End pi2_alice_view_is_leakage_free.

Section eqn6_proof.

Let O := [%x1, x2, s1, s2, r2, y2].

Let f1 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX * TX) -> 'rV[TX]_n := fun z =>
  let '(x1, x2, s1, s2, r1, y2) := z in x1.

Let f2 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX * TX) -> ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX) := fun z =>
  let '(x1, x2, s1, s2, r2, y2) := z in (x2, s2, x1 + s1, r2).

Let fm : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX * TX) -> TX := fun z =>
  let '(x1, x2, s1, s2, r2, y2) := z in y2.

Let W1 := f1 `o O.  (* x1; It is okay in Bob's view has it because only used in condition. *)
Let W2 := f2 `o O.  (* [%x2, s2, x1', r2]; cannot have x1, s1 here otherwise Bob knows the secret*)
Let Wm := fm `o O.  (* y2 *)

Variable (w2 : 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX) (wm : TX).

(* Because y2 is generated by Bob; not related to x2, s2, x1, s1, r2 at all*)
Hypothesis W2_Wm_indep: P|= W2 _|_ Wm.
Hypothesis W1W2_Wm_indep : P|= [%W1, W2] _|_ Wm.

Hypothesis card_Wm: #|TX| = m.+2.
(* In the paper, y2 (Wm) is uniform distributed*)
Hypothesis pWm_unif: `p_ Wm = fdist_uniform card_Wm.

Let W1WmW2_cinde : W1 _|_ Wm | W2.
Proof. apply: inde_RV2_cinde. by exact: W1W2_Wm_indep.
Qed.

Hypothesis W2Wm_neq0 : `Pr[ [% Wm, W2] = (wm, w2) ] != 0.

Lemma eqn6:
  cond_entropy1_RV [%W2, Wm] W1 (w2, wm) = cond_entropy1_RV W2 W1 w2.
Proof.
have H := (@cpr_cond_entropy1_RV _ _ _ TX P m.+1 W1 W2 Wm card_Wm pWm_unif W2_Wm_indep w2 wm).
symmetry in H.
apply H.
move => w.
have H2:=(@cinde_alt _ _ _ _ _ W1 Wm W2 w wm w2 W1WmW2_cinde W2Wm_neq0).
symmetry in H2.
rewrite cpr_RV2_sym. 
apply H2.
Qed.

End eqn6_proof.

Section eqn7_proof.

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

Variable (w2 : 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n) (wm : TX).

(* Because r2 is generated by Bob; not related to x2, s2, x1, s1 at all*)
Hypothesis W2_Wm_indep: P|= W2 _|_ Wm.
Hypothesis W1W2_Wm_indep : P|= [%W1, W2] _|_ Wm.

Hypothesis card_Wm: #|TX| = m.+2.
(* In the paper, r2 (Wm) is uniform distributed*)
Hypothesis pWm_unif: `p_ Wm = fdist_uniform card_Wm.

Let W1WmW2_cinde : W1 _|_ Wm | W2.
Proof. apply: inde_RV2_cinde. by exact: W1W2_Wm_indep.
Qed.

Hypothesis W2Wm_neq0 : `Pr[ [% Wm, W2] = (wm, w2) ] != 0.
  
Lemma eqn7:
  cond_entropy1_RV [%W2, Wm] W1 (w2, wm) = cond_entropy1_RV W2 W1 w2.
Proof.
have H := (@cpr_cond_entropy1_RV _ _ _ TX P m.+1 W1 W2 Wm card_Wm pWm_unif W2_Wm_indep w2 wm).
symmetry in H.
apply H.
move => w.
have H2:=(@cinde_alt _ _ _ _ _ W1 Wm W2 w wm w2 W1WmW2_cinde W2Wm_neq0).
symmetry in H2.
rewrite cpr_RV2_sym. 
apply H2.
Qed.

(* Although in the paper eqn_7 needs Theorem 3.7 to prove,
   it actually only needs cinde_alt. Because r2 is not Wm+Z but just Wm.
*)
End eqn7_proof.

Section eqn8_proof.

Let O := [%x1, x2, s1, s2].

(* f1 `o X in mc_removal_pr must be x1 in eqn8 *)
Let f1 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n) -> 'rV[TX]_n := fun z =>
  let '(x1, x2, s1, s2) := z in x2.

(* f2 `o X in mc_removal_pr must be (x2, s2) in eqn8 *)
Let f2 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n) -> ('rV[TX]_n * 'rV[TX]_n) := fun z =>
  let '(x1, x2, s1, s2) := z in (x2, s2).

(* (fm `o X)+Z in mc_removal_pr must be x1'=x1+s1 in eqn8 *)
Let fm : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n) -> 'rV[TX]_n := fun z =>
  let '(x1, x2, s1, s2) := z in x1 + s1.

Let Z := s1.
Let W1 := f1 `o O.   (* x1 *)
Let W2 := f2 `o O.   (* [%x2, s2]*)
Let Wm := fm `o O.   (* x1'-s1*)
Let WmZ := Wm `+ s1. (* x1'*)

Variable Z_O_indep : inde_rv Z O. 
Variable Z_WmW2_indep : inde_rv Z [%Wm, W2].

Variable (w2 : 'rV[TX]_n * 'rV[TX]_n) (wmz : 'rV[TX]_n) .

Hypothesis card_Z : #|'rV[TX]_n| = m.+2.
Hypothesis pZ_unif : `p_ Z = fdist_uniform card_Z.
Hypothesis Hneq0 : `Pr[ [%WmZ, W2] = (wmz, w2) ] != 0.

Let Z_Wm_indep:
  P |= Z _|_ Wm.
Proof.
rewrite /Wm.
rewrite (_:Z = idfun `o Z) //.
apply: inde_rv_comp.
by exact: Z_O_indep.
Qed.

Let pWmZ_unif:
  (@dist_of_RV T P 'rV[TX]_n WmZ) = fdist_uniform card_Z.
Proof.
rewrite /WmZ.
have H_ZWM := Z_Wm_indep.
rewrite inde_rv_sym in H_ZWM.
have H := add_RV_unif Wm Z card_Z pZ_unif H_ZWM.
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
have H := (@lemma_3_5' _ _ 'rV[TX]_n P m.+1 Wm Z W2 card_Z pZ_unif Z_WmW2_indep x y).
apply H.
Qed.

Lemma eqn8:
  cond_entropy1_RV [%W2, WmZ] W1 (w2, wmz) = cond_entropy1_RV W2 W1 w2.
Proof.
have Ha := (@cpr_cond_entropy1_RV _ _ _ 'rV[TX]_n P m.+1 W1 W2 WmZ card_Z pWmZ_unif W2_WmZ_indep w2 wmz).
symmetry in Ha.
apply Ha => w.
have Hb :=(@mc_removal_pr _ _ _ _ 'rV[TX]_n P m.+1 O Z f1 f2 fm Z_O_indep card_Z pZ_unif w w2 wmz Hneq0).
symmetry in Hb.
apply Hb.
Qed.
  
End eqn8_proof.

Section eqn_bob_fin_proof.

Hypothesis x1_indep : P |= [% x2, s2] _|_ x1.
  
Lemma eqn_8_1:
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
by exact: x1_indep.
Qed.

End eqn_bob_fin_proof.

(* Using graphoid for combinations of independ random variables. *)
Section mutual_indep.

Hypothesis x1_indep1 : P|= x1 _|_ [%s1, r1, x2', t, y1].
Hypothesis x1_indep2 : P|= x1 _|_ [%x2, s1, s2, r1, y2].  (* from the paper. *)

About pairwise.

Hypothesis Hinde : {homo nth x1 [:: x1; x2; s1; s2] : i j / i < j >-> inde_rv i j}%nat.
Check @Hinde 0 1.

Hypothesis Hinde_r : P|= r1 _|_ y2.
Hypothesis Hinde_all : forall i j, P|= nth x1 [:: x1; x2; s1; s2] i _|_ nth r1 [:: r1; y2] j.
  
Lemma inde_cinde (X Y Z: {RV P-> TX}):
  inde_rv X Y -> inde_rv [%X, Y] Z -> cinde_rv X Y Z.
Proof.
Admitted.

End mutual_indep.

End pi2.

End smc_entropy_proofs.
