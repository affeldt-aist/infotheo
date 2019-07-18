(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg zmodp matrix.
Require Import Reals Lra.
Require Import ssrR Reals_ext ssr_ext ssralg_ext bigop_ext Rbigop proba channel.
Require Import cproba.

(** * Posterior Probability *)

(** OUTLINE:
- Section receivable_def.
- Section receivable_uniform.
- Module PostProbability.
- Section post_proba_prop.
- Module MarginalPostProbabiliy.
- Section marginal_post_proba_prop.
*)

Reserved Notation "P '`^^' W '(' x '|' Hy ')'" (at level 10,
  W, x, Hy at next level).
Reserved Notation "P ''_' n0 '`^^' W '(' a '|' Hy ')'" (at level 10,
  n0, W, a, Hy at next level).

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope channel_scope.
Local Open Scope proba_scope.
Local Open Scope R_scope.

Section receivable_def.

Variables (A B : finType) (W : `Ch(A, B)) (n : nat) (P : {dist 'rV[A]_n}).

Definition receivable y := [exists x, (P x != 0) && (W ``(y | x) != 0)].

Lemma receivableE (y : 'rV__) :
  receivable y = (\sum_(x in 'rV[A]_n) P x * W ``(y | x) != 0).
Proof.
apply/idP/idP => [|H].
- case/existsP => /= x /andP[Px0].
  apply: contra => /eqP/prsumr_eq0P => /= H.
  apply/eqP; rewrite -(@eqR_mul2l (P x)); last exact/eqP.
  rewrite mulR0 H // => /= x' _.
  apply mulR_ge0; exact: dist_ge0.
- have /= : \sum_(x in setT) P x * W ``(y | x) != 0.
    apply: contra H => /eqP H; apply/eqP.
    rewrite -[RHS]H; apply/eq_bigl => /= x; by rewrite !inE.
  apply: contraNT.
  rewrite /receivable negb_exists => /forallP /= {H}H.
  apply/eqP/big1 => x _.
  move: (H x); rewrite negb_and 2!negbK => /orP[|] /eqP ->;
    by rewrite ?(mul0R,mulR0).
Qed.

End receivable_def.

Section receivable_uniform.

Variables (A B : finType) (W : `Ch(A, B)) (n : nat) (x : 'rV[A]_n).
Variable C : {set 'rV[A]_n}.
Hypothesis HC : (0 < #| C |)%nat.
Variable y : 'rV[B]_n.

Lemma not_receivable_uniformE :
  ~~ receivable W (`U HC) y = (\sum_(t0 in C) W ``(y | t0) == 0).
Proof.
apply/idP/idP => [|/eqP].
- rewrite negb_exists => /forallP H.
  rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 // => i iC.
  move: (H i).
  rewrite negb_and !negbK => /orP[|/eqP //].
  by rewrite -(negbK (_ == _)) UniformSupport.neq0 iC.
- have : forall i : 'rV_n, i \in C -> (0 <= W ``(y | i))%R.
    move=> ? ?; exact: DMC_ge0.
  move/prsumr_eq0P => H /H {H} H.
  rewrite /receivable; apply/negP.
  case/existsP => z /andP[].
  rewrite UniformSupport.neq0 => /H ->; by rewrite eqxx.
Qed.

End receivable_uniform.

(* posterior probability *)
Module PosteriorProbability.
Section def.
Variables (A B : finType) (W : `Ch(A, B)) (n : nat) (P : {dist 'rV[A]_n}).
Variable y : 'rV[B]_n.
Definition den := \sum_(x in 'rV_n) P x * W ``(y | x).
Hypothesis receivable_y : receivable W P y.

Definition f := [ffun x => P x * W ``(y | x) / den].

Lemma den_ge0 : 0 <= den.
Proof.
apply rsumr_ge0 => x _; apply mulR_ge0; [exact/dist_ge0 | exact/DMC_ge0].
Qed.

Lemma f0 x : 0 <= f x.
Proof.
rewrite ffunE; apply divR_ge0; first by apply mulR_ge0; exact/dist_ge0.
apply/ltRP; rewrite lt0R {1}/den -receivableE receivable_y; exact/leRP/den_ge0.
Qed.

Lemma f1 : \sum_(x in 'rV_n) f x = 1.
Proof.
rewrite /f /Rdiv; evar (h : 'rV[A]_n -> R); rewrite (eq_bigr h); last first.
  move=> a _; rewrite ffunE /h; reflexivity.
by rewrite {}/h -big_distrl /= mulRC mulVR // -receivableE.
Qed.

Definition d : {dist 'rV[A]_n} := locked (makeDist f0 f1).

Lemma dE x : d x = P x * W ``(y | x) / den.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
End def.
Local Notation "P '`^^' W '(' x '|' Hy ')'" := (@d _ _ W _ P _ Hy x).

(* relation with channel-based information-theoretic definitions *)
Section chap2.
Variables (A B : finType) (W : `Ch(A, B)) (n : nat) (P : {dist 'rV[A]_n}).
Local Open Scope channel_scope.
Lemma ppE (x : 'rV[A]_n) (y : 'rV[B]_n) (Hy : receivable W P y) :
  P `^^ W (x | Hy) = \Pr_(`J(P, W ``^ n))[[set x]|[set y]].
Proof.
rewrite dE /cPr setX1 2!Pr_set1 JointDistChan.dE /=; congr (_ / _).
rewrite Bivar.sndE /=; apply eq_bigr => x' _; by rewrite JointDistChan.dE /= mulRC.
Qed.
End chap2.

Section prop.
Variables (A B : finType) (W : `Ch(A, B)) (n : nat).
Variable (C : {set 'rV[A]_n}).
Hypothesis HC : (0 < #| C |)%nat.
Variable y : 'rV[B]_n.
Hypothesis Hy : receivable W (`U HC) y.

Definition Kppu := / \sum_(c in C) W ``(y | c).

Lemma uniformEF (x : 'rV[A]_n) : x \notin C ->
  (`U HC) `^^ W (x | Hy) = 0.
Proof. move=> xC; by rewrite dE UniformSupport.dEN // /Rdiv !mul0R. Qed.

Lemma uniformET (x : 'rV[A]_n) : x \in C ->
  (`U HC) `^^ W (x | Hy) = Kppu * W ``(y | x).
Proof.
move=> Ht.
rewrite dE UniformSupport.dET // mulRC {1}/Rdiv -mulRA [in RHS]mulRC; congr (_ * _).
rewrite /den UniformSupport.restrict.
have C0 : INR #|C| != 0 by rewrite INR_eq0' -lt0n.
rewrite div1R -invRM.
  rewrite /Kppu; congr Rinv; rewrite big_distrr /=; apply eq_bigr => i iC.
  by rewrite UniformSupport.dET // div1R mulRA mulRV // mul1R.
  exact/eqP.
rewrite (eq_bigr (fun t => 1 / INR #|C| * W ``(y | t))); last first.
  by move=> *; rewrite UniformSupport.dET.
rewrite -big_distrr /= mulR_eq0 => -[].
  rewrite div1R; exact/invR_neq0/eqP.
by apply/eqP; rewrite -not_receivable_uniformE Hy.
Qed.

Lemma uniform_kernel (x : 'rV[A]_n) :
  (`U HC) `^^ W (x | Hy) = (Kppu * INR (x \in C) * W ``(y | x))%R.
Proof.
case/boolP : (x \in C) => xC.
- by rewrite uniformET // ?inE // mulR1.
- by rewrite uniformEF ?inE // mulR0 mul0R.
Qed.

End prop.
End PosteriorProbability.

Notation "P '`^^' W '(' x '|' Hy ')'" :=
  (@PosteriorProbability.d _ _ W _ P _ Hy x) : proba_scope.

Local Open Scope vec_ext_scope.

Module MarginalPostProbability.
Section def.
Variables (A B : finType) (W : `Ch(A, B)) (n : nat) (P : {dist 'rV[A]_n}).
Variable y : 'rV[B]_n.
Hypothesis Hy : receivable W P y.

Let f' := fun x : 'rV_n => P `^^ W (x | Hy).

Definition Kmpp : R := / \sum_(t in 'rV_n) f' t.

Lemma f'_neq0 : \sum_(t in 'rV_n) f' t <> 0.
Proof.
evar (x : 'rV[A]_n -> R).
rewrite (eq_bigr x); last first.
  move=> i _; rewrite /f' PosteriorProbability.dE /Rdiv /x; reflexivity.
rewrite -big_distrl { x} /= mulR_eq0 => -[/eqP|].
- apply/negP; by rewrite -receivableE.
- apply/invR_neq0/eqP; by rewrite -receivableE.
Qed.

Definition f (i : 'I_n) := [ffun a => Kmpp * \sum_(t in 'rV_n | t ``_ i == a) f' t].

Lemma f0 i a : 0 <= f i a.
Proof.
rewrite ffunE; apply mulR_ge0.
- rewrite /Kmpp.
  apply/ltRW/invR_gt0/ltRP; rewrite lt0R; apply/andP; split; [apply/eqP |apply/leRP]; last first.
    apply rsumr_ge0 => /= ? _; exact: dist_ge0.
  exact/f'_neq0.
- apply rsumr_ge0 => /= ? _; exact: dist_ge0.
Qed.

Lemma f1 i : \sum_(a in A) f i a = 1.
Proof.
rewrite /f; evar (h : A -> R); rewrite (eq_bigr h); last first.
  move=> a _; rewrite ffunE /h; reflexivity.
rewrite {}/h -big_distrr /= /Kmpp.
set tmp1 := \sum_( _ | _ ) _.
set tmp2 := \sum_( _ | _ ) _.
suff : tmp1 = tmp2.
  move=> tp12; rewrite -tp12 mulVR //; exact/eqP/f'_neq0.
by rewrite {}/tmp1 {}/tmp2 (partition_big (fun x : 'rV_n => x ``_ i) xpredT).
Qed.

Definition d i : dist A := makeDist (f0 i) (f1 i).

End def.
Local Notation "P ''_' n0 '`^^' W '(' a '|' Hy ')'" :=
  (@d _ _ W _ P _ Hy n0 a).
Section prop.
Variables (A B : finType) (W : `Ch(A, B)).
Variables (n : nat) (C : {set 'rV[A]_n}).
Hypothesis HC : (0 < #| C |)%nat.

Variable y : 'rV[B]_n.
Hypothesis Hy : receivable W (`U HC) y.

Lemma probaE b n0 :
  (`U HC) '_ n0 `^^ W (b | Hy) =
  Kmpp Hy * (\sum_(t in 'rV_n | t ``_ n0 == b) (`U HC) `^^ W (t | Hy)).
Proof. by rewrite ffunE. Qed.

End prop.
End MarginalPostProbability.

Notation "P ''_' n0 '`^^' W '(' a '|' Hy ')'" :=
  (@MarginalPostProbability.d _ _ W _ P _ Hy n0 a) : proba_scope.
