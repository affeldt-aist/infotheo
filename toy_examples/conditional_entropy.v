(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum fingroup finalg matrix.
From mathcomp Require Import ring lra.
From mathcomp Require Import Rstruct reals.
Require Import ssr_ext ssralg_ext bigop_ext realType_ext realType_ln fdist.
Require Import proba jfdist_cond entropy.

(******************************************************************************)
(* Example 2.2.1 of T. M. Cover and J. A. Thomas. Elements of information     *)
(* theory. Wiley, 2006. 2nd edition                                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Import GRing.Theory Num.Theory Order.Theory.

Module conditional_entropy_example.
Definition R := Rdefinitions.R.
Definition zero : 'I_4 := ord0.
Definition one : 'I_4 := @Ordinal 4 1 isT.
Definition two : 'I_4 := @Ordinal 4 2 isT.
Definition three : 'I_4 := @Ordinal 4 3 isT.

Definition f := [ffun x : 'I_4 * 'I_4 => [eta (fun=>(0:R)) with
(zero, zero) |-> (1/8), (zero, one) |-> (1/16), (zero, two) |-> (1/16), (zero, three) |-> (1/4),
(one, zero) |-> (1/16), (one, one) |-> (1/8), (one, two) |-> (1/16), (one, three) |-> 0,
(two, zero) |-> (1/32), (two, one) |-> (1/32), (two, two) |-> (1/16), (two, three) |-> 0,
(three, zero) |-> (1/32), (three, one) |-> (1/32), (three, two) |-> (1/16), (three, three) |-> 0] x].

Lemma f0 x : 0 <= f x.
Proof.
rewrite ffunE; move: x.
case => -[ [? [[|[|[|[|[]//]]]]]
  | [? [[|[|[|[|[]//]]]]]
  | [? [[|[|[|[|[]//]]]]]
  | [? [[|[|[|[|[]//]]]]] | []//]]]]]; rewrite /f /=; try lra.
Qed.

Lemma f1 : \sum_(x in {: 'I_4 * 'I_4}) f x = 1.
Proof.
rewrite (eq_bigr (fun x => f (x.1, x.2))); last by case.
rewrite -(pair_bigA _ (fun x1 x2 => f (x1, x2))) /=.
by rewrite !big_ord_recl !big_ord0 /f /= !ffunE /=; field.
Qed.

Definition d : {fdist 'I_4 * 'I_4} := locked (FDist.make f0 f1).

Lemma dE x : d x = f x.
Proof. by rewrite /d; unlock. Qed.

Lemma conditional_entropyE : centropy d = 11/8.
Proof.
rewrite /centropy /=.
rewrite !big_ord_recl big_ord0 !fdist_sndE /=.
rewrite !big_ord_recl !big_ord0.
repeat (rewrite dE /f /= ffunE /=).
rewrite !(add0r,addr0).
rewrite /centropy1 /=.
rewrite !big_ord_recl big_ord0.
rewrite /jcPr /Pr.
repeat (rewrite big_setX /= !big_set1 dE /f /= ffunE /=).
rewrite !fdist_sndE /=.
rewrite !big_ord_recl !big_ord0.
repeat (rewrite dE /f /= ffunE /=).
rewrite !(add0r,addr0).
rewrite (_ : 1/32 + 1/32 = 1/16); last lra.
rewrite (addrCA (1/16)).
rewrite (addrA (1/16)).
rewrite (_ : 1/16 + 1/16 = 1/8); last lra.
rewrite (_ : 1/8 + 1/8 = 1/4); last lra.
rewrite invfM//.
repeat (rewrite logM; [|lra|lra]).
rewrite invrK invr1 !mul1r.
repeat (rewrite logV; last lra).
rewrite log1 log4 log8 log16 log32.
by field.
Qed.

End conditional_entropy_example.
