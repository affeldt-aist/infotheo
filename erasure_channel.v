(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype div finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg perm zmodp matrix.
Require Import Reals Fourier.
Require Import ssrR Reals_ext ssr_ext ssralg_ext logb Rbigop proba entropy.
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
rewrite (bigD1 None) //= (bigD1 (Some a)) //= eqxx /= (proj2 (prsumr_eq0P _)).
- by field.
- rewrite /f; case => [a'|]; last by case: p_01.
  case: ifPn => [_ |*]; last exact/leRR.
  case: p_01 => ? ? _; fourier.
- case => //= a' aa'; case: ifPn => // /eqP ?; subst a'.
  move: aa'; by rewrite eqxx.
Qed.

Definition c : `Ch_1(A, [finType of option A]) :=
  fun a => makeDist (f0 a) (f1 a).

End EC_sect.

Section EC_prob.

Variable X : finType.
Hypothesis card_X : #|X| = 2%nat.
Variable P : dist X.
Variable p : R. (* erasure probability *)
Hypothesis p_01 : 0 <= p <= 1.

Let BEC := @EC.c X p p_01.
Let q := P (Set2.a card_X).
Local Notation W := (EC.f p).
Local Notation P'W := (JointDist.f P BEC).
Local Notation PW := (OutDist.f P BEC).

Lemma EC_non_flip (a : X) (i : option X):
  (i != None) && (i != Some a) -> 0 = EC.f p a i.
Proof.
case: i => //= x xa; case: ifP => // ax; move: xa; by rewrite (eqP ax) eqxx.
Qed.

End EC_prob.

End EC.
