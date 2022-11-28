(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg zmodp matrix.
Require Import Reals.
From mathcomp Require Import Rstruct.
Require Import ssrR Reals_ext ssr_ext ssralg_ext bigop_ext Rbigop fdist proba.
Require Import channel jfdist.

(******************************************************************************)
(*                         Posterior Probability                              *)
(*                                                                            *)
(* P `^^ W (x | y) == channel-based information-theoretic definition of       *)
(*                    posterior probability in terms of a distribution of     *)
(*                    inputs P and of a channel W                             *)
(* P ''_ n0 `^^ W ( a | y ) == marginal posterior probability                 *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*   ppE == relation between P `^^ W (x | y) and the conditional probability  *)
(*          w.r.t. the joint distribution `J(P, W ``^ n)                      *)
(******************************************************************************)

(* OUTLINE:
- Module Receivable.
- Section receivable_prop.
- Section receivable_uniform.
- Module PostProbability.
- Section post_proba_prop.
- Module MarginalPostProbabiliy.
- Section marginal_post_proba_prop.
*)

Reserved Notation "P '`^^' W '(' x '|' y ')'" (at level 10,
  W, x, y at next level).
Reserved Notation "P ''_' n0 '`^^' W '(' a '|' y ')'" (at level 10,
  n0, W, a, y at next level).

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope channel_scope.
Local Open Scope proba_scope.
Local Open Scope R_scope.

Module Receivable.
Section receivable.
Variables (A B : finType) (n : nat) (P : {fdist 'rV[A]_n}) (W : `Ch(A, B)).
Definition def y := [exists x, (P x != 0) && (W ``(y | x) != 0)].
Record t := mk {y :> 'rV[B]_n ; _ : def y }.
Lemma defE (y : t) : def y. Proof. by case: y. Qed.
End receivable.
End Receivable.
Coercion Receivable.y : Receivable.t >-> matrix.

Notation "P .-receivable W" := (Receivable.t P W) (at level 2,
  format "P .-receivable  W").

Section receivable_prop.

Variables (A B : finType) (n : nat) (P : {fdist 'rV[A]_n}) (W : `Ch(A, B)).

Lemma receivableE (y : P.-receivable W) :
  Receivable.def P W y = (\sum_(x in 'rV[A]_n) P x * W ``(y | x) != 0).
Proof.
apply/idP/idP => [|H].
- case/existsP => /= x /andP[Px0].
  apply: contra => /eqP/psumR_eq0P => /= H.
  apply/eqP; rewrite -(@eqR_mul2l (P x)); last exact/eqP.
  rewrite mulR0 H // => /= x' _; exact: mulR_ge0.
- have /= : \sum_(x in setT) P x * W ``(y | x) != 0.
    apply: contra H => /eqP H; apply/eqP.
    rewrite -[RHS]H; apply/eq_bigl => /= x; by rewrite !inE.
  apply: contraNT.
  rewrite /Receivable.def negb_exists => /forallP /= {}H.
  apply/eqP/big1 => x _.
  move: (H x); rewrite negb_and 2!negbK => /orP[|] /eqP ->;
    by rewrite ?(mul0R,mulR0).
Qed.

End receivable_prop.

Section receivable_uniform.

Variables (A B : finType) (W : `Ch(A, B)) (n : nat) (x : 'rV[A]_n).
Variable C : {set 'rV[A]_n}.
Hypothesis HC : (0 < #| C |)%nat.
Variable y : 'rV[B]_n.

Lemma not_receivable_uniformE :
  ~~ Receivable.def (`U HC) W y = (\sum_(t0 in C) W ``(y | t0) == 0).
Proof.
apply/idP/idP => [|/eqP].
- rewrite negb_exists => /forallP H.
  rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 // => i iC.
  move: (H i).
  rewrite negb_and !negbK => /orP[|/eqP //].
  by rewrite -(negbK (_ == _)) fdist_uniform_supp_neq0 iC.
- have : forall i : 'rV_n, i \in C -> (0 <= W ``(y | i))%R by [].
  move/psumR_eq0P => H /H {}H.
  rewrite /Receivable.def; apply/negP.
  case/existsP => z /andP[].
  by rewrite fdist_uniform_supp_neq0 => /H ->; rewrite eqxx.
Qed.

End receivable_uniform.

Module PosteriorProbability.
Section def.
Variables (A B : finType) (W : `Ch(A, B)) (n : nat) (P : {fdist 'rV[A]_n}).
Variable y : P.-receivable W.
Definition den := \sum_(x in 'rV_n) P x * W ``(y | x).

Definition f := [ffun x => P x * W ``(y | x) / den].

Lemma den_ge0 : 0 <= den. Proof. by apply sumR_ge0 => x _; exact: mulR_ge0. Qed.

Lemma f0 x : 0 <= f x.
Proof.
rewrite ffunE; apply divR_ge0; first exact: mulR_ge0.
apply/ltRP; rewrite lt0R {1}/den -receivableE Receivable.defE /=.
exact/leRP/den_ge0.
Qed.

Lemma f1 : \sum_(x in 'rV_n) f x = 1.
Proof.
under eq_bigr do rewrite ffunE /=.
by rewrite -big_distrl /= mulRC mulVR // -receivableE Receivable.defE.
Qed.

Definition d : {fdist 'rV[A]_n} := locked (FDist.make f0 f1).

Lemma dE x : d x = P x * W ``(y | x) / den.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
End def.
Local Notation "P '`^^' W '(' x '|' y ')'" := (@d _ _ W _ P y x).

Section chap2.
Variables (A B : finType) (W : `Ch(A, B)) (n : nat) (P : {fdist 'rV[A]_n}).
Local Open Scope channel_scope.
Lemma ppE (x : 'rV[A]_n) (y : P.-receivable W) :
  P `^^ W (x | y) = \Pr_(`J(P, W ``^ n))[[set x] | [set Receivable.y y]].
Proof.
rewrite dE /jcPr setX1 2!Pr_set1 JointFDistChan.dE /=; congr (_ / _).
rewrite fdist_sndE /=; apply eq_bigr => x' _; by rewrite JointFDistChan.dE /= mulRC.
Qed.
End chap2.

Section prop.
Variables (A B : finType) (W : `Ch(A, B)) (n : nat).
Variable (C : {set 'rV[A]_n}).
Hypothesis HC : (0 < #| C |)%nat.
Variable y : (`U HC).-receivable W.

Definition Kppu := / \sum_(c in C) W ``(y | c).

Lemma uniformEF (x : 'rV[A]_n) : x \notin C ->
  (`U HC) `^^ W (x | y) = 0.
Proof. move=> xC; by rewrite dE fdist_uniform_supp_notin // /Rdiv !mul0R. Qed.

Lemma uniformET (x : 'rV[A]_n) : x \in C ->
  (`U HC) `^^ W (x | y) = Kppu * W ``(y | x).
Proof.
move=> Ht.
rewrite dE fdist_uniform_supp_in // mulRC {1}/Rdiv -mulRA [in RHS]mulRC; congr (_ * _).
rewrite /den fdist_uniform_supp_restrict.
have C0 : INR #|C| != 0 by rewrite INR_eq0' -lt0n.
rewrite div1R -invRM //.
  rewrite /Kppu; congr Rinv; rewrite big_distrr /=; apply eq_bigr => i iC.
  by rewrite fdist_uniform_supp_in // div1R mulRA mulRV // mul1R.
rewrite (eq_bigr (fun t => 1 / INR #|C| * W ``(y | t))); last first.
  by move=> *; rewrite fdist_uniform_supp_in.
apply/eqP; rewrite -big_distrr /= mulR_eq0 => -[].
  by rewrite div1R; exact/invR_neq0/eqP.
by apply/eqP; rewrite -not_receivable_uniformE Receivable.defE.
Qed.

Lemma uniform_kernel (x : 'rV[A]_n) :
  (`U HC) `^^ W (x | y) = (Kppu * INR (x \in C) * W ``(y | x))%R.
Proof.
case/boolP : (x \in C) => xC.
- by rewrite uniformET // ?inE // mulR1.
- by rewrite uniformEF ?inE // mulR0 mul0R.
Qed.

End prop.
End PosteriorProbability.
Arguments PosteriorProbability.Kppu {A} {B} {W} {n} _ {HC}.

Notation "P '`^^' W '(' x '|' y ')'" :=
  (@PosteriorProbability.d _ _ W _ P y x) : proba_scope.

Local Open Scope vec_ext_scope.

Module MarginalPostProbability.
Section def.
Variables (A B : finType) (W : `Ch(A, B)) (n : nat) (P : {fdist 'rV[A]_n}).
Variable y : P.-receivable W.

Let f' := fun x : 'rV_n => P `^^ W (x | y).

Definition Kmpp : R := / \sum_(t in 'rV_n) f' t.

Lemma f'_neq0 : \sum_(t in 'rV_n) f' t <> 0.
Proof.
under eq_bigr do rewrite /f' PosteriorProbability.dE /Rdiv.
rewrite -big_distrl /= mulR_eq0 => -[/eqP|].
- by apply/negP; rewrite -receivableE Receivable.defE.
- by apply/invR_neq0/eqP; rewrite -receivableE Receivable.defE.
Qed.

Definition f (i : 'I_n) := [ffun a => Kmpp * \sum_(t in 'rV_n | t ``_ i == a) f' t].

Lemma f0 i a : 0 <= f i a.
Proof.
rewrite ffunE; apply mulR_ge0.
- rewrite /Kmpp.
  apply/invR_ge0/ltRP; rewrite lt0R; apply/andP; split; [apply/eqP |apply/leRP]; last first.
    by apply sumR_ge0 => /= ? _; exact: FDist.ge0.
  exact/f'_neq0.
- by apply sumR_ge0 => /= ? _; exact: FDist.ge0.
Qed.

Lemma f1 i : \sum_(a in A) f i a = 1.
Proof.
under eq_bigr do rewrite ffunE /=.
rewrite -big_distrr /= /Kmpp.
set tmp1 := \sum_( _ | _ ) _.
set tmp2 := \sum_( _ | _ ) _.
suff : tmp1 = tmp2.
  move=> tp12; rewrite -tp12 mulVR //; exact/eqP/f'_neq0.
by rewrite {}/tmp1 {}/tmp2 (partition_big (fun x : 'rV_n => x ``_ i) xpredT).
Qed.

Definition d i : fdist A := FDist.make (f0 i) (f1 i).

End def.
Local Notation "P ''_' n0 '`^^' W '(' a '|' y ')'" := (@d _ _ W _ P y n0 a).
Section prop.
Variables (A B : finType) (W : `Ch(A, B)).
Variables (n : nat) (C : {set 'rV[A]_n}).
Hypothesis HC : (0 < #| C |)%nat.

Variable y : (`U HC).-receivable W.

Lemma probaE b n0 : (`U HC) '_ n0 `^^ W (b | y) =
  Kmpp y * (\sum_(t in 'rV_n | t ``_ n0 == b) (`U HC) `^^ W (t | y)).
Proof. by rewrite ffunE. Qed.

End prop.
End MarginalPostProbability.

Notation "P ''_' n0 '`^^' W '(' a '|' y ')'" :=
  (@MarginalPostProbability.d _ _ W _ P y n0 a) : proba_scope.
