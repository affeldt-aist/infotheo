(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect all_algebra matrix.
From mathcomp Require Import mathcomp_extra Rstruct.
Require Import ssr_ext ssralg_ext realType_ext realType_ln fdist.
Require Import entropy binary_entropy_function channel hamming channel_code.

(**md**************************************************************************)
(* # Definition of erasure channel                                            *)
(*                                                                            *)
(* ```                                                                        *)
(*    EC.c == definition of n-ary Erasure Channel (EC)                        *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory Num.Theory.

Local Open Scope channel_scope.
Local Open Scope reals_ext_scope.
Local Open Scope ring_scope.

Module EC.

Section EC_sect.
Variables (A : finType) (p : Rdefinitions.R).
Hypothesis p_01 : 0 <= p <= 1.
Local Open Scope ring_scope.

Definition f (a : A) := [ffun b =>
  if b is Some a' then
    if a == a' then p.~ else 0
  else p].

Lemma f0 a b : 0 <= f a b.
Proof.
rewrite /f ffunE.
case: b => [a'|]; last first.
  by case/andP: p_01.
case: ifP => _ //.
case/andP : p_01 => ? ? //.
exact/onem_ge0.
Qed.

Lemma f1 (a : A) : \sum_(a' : {:option A}) f a a' = 1.
Proof.
rewrite (bigD1 None) //= (bigD1 (Some a)) //= !ffunE eqxx /=.
rewrite [X in _ + (_ + X)](_ : _ = 0).
  by rewrite addr0 add_onemK.
apply/eqP; rewrite psumr_eq0/=; last first.
  rewrite /f; move => [a'|//].
  rewrite ffunE.
  case: ifPn => [_ _|//].
  by case/andP : p_01 => ? ?; exact/onem_ge0.
apply/allP; case => //= a' aa'; rewrite ffunE; case: ifPn => // /eqP ?.
  subst a'.
  by move: aa'; rewrite eqxx.
by rewrite eqxx implybT.
Qed.

Definition c : `Ch(A, option A) := fun a => FDist.make (f0 a) (f1 a).

End EC_sect.

Section EC_prob.
Local Open Scope fdist_scope.
Variable X : finType.
Hypothesis card_X : #|X| = 2%nat.
Variables (P : {fdist X}) (p : Rdefinitions.R) (* erasure probability *).
Hypothesis p_01 : 0 <= p <= 1.

Let BEC := @EC.c X p p_01.
Let q := P (Set2.a card_X).
Local Notation W := (EC.f p).
Local Notation P'W := (P `X BEC)%fdist.
Local Notation PW := (`O(P, BEC)).

Lemma EC_non_flip (a : X) (i : option X) :
  (i != None) && (i != Some a) -> 0 = EC.f p a i.
Proof.
case: i => //= x xa; rewrite ffunE; case: ifP => // ax; move: xa.
by rewrite (eqP ax) eqxx.
Qed.

End EC_prob.

End EC.
