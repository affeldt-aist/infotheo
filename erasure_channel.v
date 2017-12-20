(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
From mathcomp Require Import div finfun bigop prime binomial ssralg finset fingroup finalg.
From mathcomp Require Import perm zmodp matrix.
Require Import Reals Fourier.
Require Import Reals_ext ssr_ext ssralg_ext Rssr log2 Rbigop proba entropy.
Require Import binary_entropy_function channel hamming channel_code.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Definition of erasure channel *)

Local Open Scope channel_scope.

Module EC.

Section EC_sect.

Variable A : finType.
Variable p : R.
Hypothesis p_01 : 0 <= p <= 1.

(** Definition of n-ary Erasure Channel (EC) *)

Definition f (a : A) := fun b =>
  if b is Some a' then
    if a == a' then 1 - p else 0
  else p.

Lemma f0 a b : 0 <= f a b.
Proof. rewrite /f.
  case: b => [a'|]; last by case: p_01.
  case: ifP => _. case: p_01 => ? ?; fourier.
  fourier.
Qed.

Lemma f1 (a : A) : \rsum_(a' : {:option A}) f a a' = 1.
Proof.
rewrite (bigD1 None) //=.
rewrite (bigD1 (Some a)) //=.
rewrite eqxx /=.
rewrite -Req_0_rmul. field.
rewrite /f; case=> [a'| //].
by case: ifP => /= [/eqP -> | //]; rewrite eqxx.
Qed.

Definition c : `Ch_1(A, [finType of option A]) :=
  fun a => makeDist (f0 a) (f1 a).

End EC_sect.

Section EC_prob.

Variable X : finType.
Hypothesis card_X : #|X| = 2%nat.
Variable P : dist X.
Variable erp : R.
Hypothesis erp_01 : 0 <= erp <= 1.

Let BEC := @EC.c X erp erp_01.
Local Notation X0 := (Two_set.val0 card_X).
Local Notation X1 := (Two_set.val1 card_X).
Let q := P(X0).
Local Notation W := (EC.f erp).
Local Notation P'W := (JointDist.f P BEC).
Local Notation PW := (OutDist.f P BEC).

Lemma EC_non_flip (a : X)(i : option_finType X):
(i != None) && (i != Some a) -> 0 = EC.f erp a i.
Proof.
case i => a' //=.
case: ifP => /eqP; last by [].
move=> ->.
by rewrite eqxx.
Qed.

End EC_prob.

End EC.
