(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect all_algebra zmodp matrix.
Require Import Reals.
From mathcomp Require Import Rstruct.
Require Import ssrR Reals_ext ssr_ext ssralg_ext bigop_ext Rbigop fdist proba.
Require Import channel jfdist_cond.

(******************************************************************************)
(*                         Posterior Probability                              *)
(*                                                                            *)
(*          P.-receivable W == vectors that are receivable from input P and   *)
(*                             channel W                                      *)
(*          P `^^ W (x | y) == posterior probability in terms of a            *)
(*                             distribution of inputs P and of a channel W    *)
(* P ''_ n0 `^^ W ( a | y ) == marginal posterior probability                 *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*   post_probE == relation between P `^^ W (x | y) and the conditional       *)
(*                 probability w.r.t. the joint distribution P `X W ``^ n     *)
(******************************************************************************)

Reserved Notation "P '`^^' W '(' x '|' y ')'" (at level 10,
  W, x, y at next level).
Reserved Notation "P ''_' n0 '`^^' W '(' a '|' y ')'" (at level 10,
  n0, W, a, y at next level).
Reserved Notation "P .-receivable W" (at level 2, format "P .-receivable  W").

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope channel_scope.
Local Open Scope R_scope.

Section receivable.
Variables (A B : finType) (n : nat) (P : {fdist 'rV[A]_n}) (W : `Ch(A, B)).

Definition receivable_prop y := [exists x, (P x != 0) && (W ``(y | x) != 0)].

Record receivable := mkReceivable {
  receivable_rV :> 'rV[B]_n ;
  receivableP : receivable_prop receivable_rV
}.

End receivable.

Notation "P .-receivable W" := (receivable P W).

Section receivable_prop.
Variables (A B : finType) (n : nat) (P : {fdist 'rV[A]_n}) (W : `Ch(A, B)).

Lemma receivable_propE (y : P.-receivable W) :
  receivable_prop P W y = (\sum_(x in 'rV[A]_n) P x * W ``(y | x) != 0).
Proof.
apply/idP/idP => [|H].
- case/existsP => /= x /andP[Px0].
  apply: contra => /eqP/psumR_eq0P => /= H.
  apply/eqP; rewrite -(@eqR_mul2l (P x)); last exact/eqP.
  by rewrite mulR0 H // => /= x' _; exact: mulR_ge0.
- have /= : \sum_(x in setT) P x * W ``(y | x) != 0.
    apply: contra H => /eqP H; apply/eqP.
    rewrite -[RHS]H; apply/eq_bigl => /= x; by rewrite !inE.
  apply: contraNT.
  rewrite /receivable_prop negb_exists => /forallP /= {}H.
  apply/eqP/big1 => x _.
  by move: (H x); rewrite negb_and 2!negbK => /orP[|] /eqP ->;
     rewrite ?(mul0R,mulR0).
Qed.

End receivable_prop.

Section receivable_uniform.
Variables (A B : finType) (W : `Ch(A, B)) (n : nat) (x : 'rV[A]_n).
Variable C : {set 'rV[A]_n}.
Hypothesis HC : (0 < #| C |)%nat.
Variable y : 'rV[B]_n.

Lemma not_receivable_prop_uniform :
  ~~ receivable_prop (`U HC) W y = (\sum_(t0 in C) W ``(y | t0) == 0).
Proof.
apply/idP/idP => [|/eqP].
- rewrite negb_exists => /forallP H.
  rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 // => i iC.
  move: (H i).
  rewrite negb_and !negbK => /orP[|/eqP //].
  by rewrite -(negbK (_ == _)) fdist_uniform_supp_neq0 iC.
- have : forall i : 'rV_n, i \in C -> (0 <= W ``(y | i))%R by [].
  move/psumR_eq0P => H /H {}H.
  rewrite /receivable_prop; apply/negP.
  case/existsP => z /andP[].
  by rewrite fdist_uniform_supp_neq0 => /H ->; rewrite eqxx.
Qed.

End receivable_uniform.

Section fdist_posterior_probability.
Variables (A B : finType) (W : `Ch(A, B)) (n : nat) (P : {fdist 'rV[A]_n}).
Variable y : P.-receivable W.
Local Open Scope ring_scope.
Let den := \sum_(x in 'rV_n) P x * W ``(y | x).

Let f := [ffun x => P x * W ``(y | x) / den].

Definition fdist_post_prob_den_ge0 : 0 <= den.
Proof. by apply/RleP/sumR_ge0 => x _; exact: mulR_ge0. Qed.

Let f0 x : 0 <= f x.
Proof.
rewrite ffunE; apply/RleP; rewrite -RdivE//; last first.
  by rewrite /den -receivable_propE receivableP.
apply: divR_ge0; first exact: mulR_ge0.
apply/RltP; rewrite Num.Theory.lt0r {1}/den -receivable_propE receivableP.
exact/fdist_post_prob_den_ge0.
Qed.

Let f1 : \sum_(x in 'rV_n) f x = 1.
Proof.
under eq_bigr do rewrite ffunE /=.
rewrite -big_distrl /= -RmultE mulRC.
rewrite -RinvE; last first.
  by rewrite -receivable_propE receivableP.
by rewrite mulVR // -receivable_propE receivableP.
Qed.

Definition fdist_post_prob : {fdist 'rV[A]_n} := locked (FDist.make f0 f1).

Lemma fdist_post_probE x : fdist_post_prob x = P x * W ``(y | x) / den.
Proof. by rewrite /fdist_post_prob; unlock; rewrite ffunE. Qed.

End fdist_posterior_probability.
Notation "P '`^^' W '(' x '|' y ')'" :=
  (@fdist_post_prob _ _ W _ P y x) : proba_scope.

Section posterior_probabilityE.
Variables (A B : finType) (W : `Ch(A, B)) (n : nat) (P : {fdist 'rV[A]_n}).

Lemma post_probE (x : 'rV[A]_n) (y : P.-receivable W) :
  P `^^ W (x | y) = \Pr_(P `X (W ``^ n))[ [set x] | [set receivable_rV y]].
Proof.
rewrite fdist_post_probE /jcPr setX1 2!Pr_set1 fdist_prodE /=.
rewrite -RdivE; last first.
  rewrite -receivable_propE.
  by case: y.
congr (_ / _).
by rewrite fdist_sndE /=; apply eq_bigr => x' _; rewrite fdist_prodE /= -RmultE mulRC.
Qed.

End posterior_probabilityE.

Section posterior_probability_prop.
Variables (A B : finType) (W : `Ch(A, B)) (n : nat).
Variable (C : {set 'rV[A]_n}).
Hypothesis HC : (0 < #| C |)%nat.
Variable y : (`U HC).-receivable W.
Local Open Scope ring_scope.

Definition post_prob_uniform_cst := / \sum_(c in C) W ``(y | c).

Let K := post_prob_uniform_cst.

Lemma post_prob_uniformF (x : 'rV[A]_n) : x \notin C ->
  (`U HC) `^^ W (x | y) = 0.
Proof.
move=> xC; rewrite fdist_post_probE fdist_uniform_supp_notin //.
by rewrite -!RmultE !mul0R.
Qed.

Lemma post_prob_uniformT (x : 'rV[A]_n) : x \in C -> (`U HC) `^^ W (x | y) = K * W ``(y | x).
Proof.
move=> Ht.
have C0 : INR #|C| != 0 by rewrite INR_eq0' -lt0n.
rewrite fdist_post_probE fdist_uniform_supp_in //.
rewrite -RinvE; last first.
  by rewrite -INRE.
rewrite -!RmultE mulRC.
rewrite -RinvE; last first.
  rewrite -receivable_propE.
  by case: y.
rewrite mulRA.
congr (_ * _).
rewrite /den fdist_uniform_supp_restrict.
rewrite -invRM//.
3: by rewrite -INRE.
  rewrite /K /post_prob_uniform_cst; congr Rinv.
  rewrite !RmultE -INRE.
  rewrite big_distrl /=.
  apply eq_bigr => i iC.
  rewrite fdist_uniform_supp_in //.
  rewrite GRing.mulrAC INRE GRing.mulVr ?GRing.mul1r//.
  by rewrite GRing.unitfE -INRE.
rewrite (eq_bigr (fun t => 1 / INR #|C| * W ``(y | t))); last first.
  move=> *; rewrite fdist_uniform_supp_in//.
  by rewrite GRing.div1r INRE.
apply/eqP; rewrite -big_distrr /= mulR_eq0 => -[].
  by rewrite -RdivE// div1R; apply/invR_neq0/eqP.
by apply/eqP; rewrite -not_receivable_prop_uniform receivableP.
Qed.

Lemma post_prob_uniform_kernel (x : 'rV[A]_n) :
  (`U HC) `^^ W (x | y) = (K * (x \in C)%:R * W ``(y | x))%R.
Proof.
case/boolP : (x \in C) => xC.
- by rewrite post_prob_uniformT // ?inE // mulR1.
- by rewrite post_prob_uniformF ?inE // mulR0 mul0R.
Qed.

End posterior_probability_prop.
Arguments post_prob_uniform_cst {A} {B} {W} {n} _ {HC}.

Local Open Scope vec_ext_scope.

Section marginal_post_prob.
Variables (A B : finType) (W : `Ch(A, B)) (n : nat) (P : {fdist 'rV[A]_n}).
Variable y : P.-receivable W.
Local Open Scope ring_scope.

Let f' := fun x : 'rV_n => P `^^ W (x | y).

Definition marginal_post_prob_den : R := / \sum_(t in 'rV_n) f' t.

Let f'_neq0 : \sum_(t in 'rV_n) f' t <> 0.
Proof.
under eq_bigr do rewrite /f' fdist_post_probE /Rdiv.
rewrite -big_distrl /= mulR_eq0 => -[/eqP|].
- by apply/negP; rewrite -receivable_propE receivableP.
- rewrite -RinvE//; last first.
    rewrite -receivable_propE.
    by case: y.
- by apply/invR_neq0/eqP; rewrite -receivable_propE receivableP.
Qed.

Let f (i : 'I_n) := [ffun a =>  marginal_post_prob_den * \sum_(t in 'rV_n | t ``_ i == a) f' t].

Let f0 i a : 0 <= f i a.
Proof.
rewrite ffunE; apply/RleP/mulR_ge0.
- rewrite / marginal_post_prob_den.
  apply/invR_ge0/RltP; rewrite Num.Theory.lt0r/=; apply/andP; split; [apply/eqP |apply/RleP]; last first.
    exact: sumR_ge0.
  exact/f'_neq0.
- exact: sumR_ge0.
Qed.

Let f1 i : \sum_(a in A) f i a = 1.
Proof.
under eq_bigr do rewrite ffunE /=.
rewrite -big_distrr /= /marginal_post_prob_den.
set tmp1 := \sum_( _ | _ ) _.
set tmp2 := \sum_( _ | _ ) _.
suff : tmp1 = tmp2.
  move=> tp12; rewrite -tp12.
  by rewrite -RmultE mulVR //; exact/eqP/f'_neq0.
by rewrite {}/tmp1 {}/tmp2 (partition_big (fun x : 'rV_n => x ``_ i) xpredT).
Qed.

Definition fdist_marginal_post_prob i : {fdist A} := FDist.make (f0 i) (f1 i).

End marginal_post_prob.
Notation "P ''_' n0 '`^^' W '(' a '|' y ')'" :=
  (@fdist_marginal_post_prob _ _ W _ P y n0 a) : proba_scope.

Section marginal_post_prob_prop.
Variables (A B : finType) (W : `Ch(A, B)) (n : nat) (C : {set 'rV[A]_n}).
Hypothesis HC : (0 < #| C |)%nat.
Variable y : (`U HC).-receivable W.

Lemma fdist_marginal_post_probE b n0 : (`U HC) '_ n0 `^^ W (b | y) =
  marginal_post_prob_den y * (\sum_(t in 'rV_n | t ``_ n0 == b) (`U HC) `^^ W (t | y)).
Proof. by rewrite ffunE. Qed.

End marginal_post_prob_prop.

Notation "P ''_' n0 '`^^' W '(' a '|' y ')'" :=
  (@fdist_marginal_post_prob _ _ W _ P y n0 a) : proba_scope.
