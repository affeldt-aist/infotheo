(* infotheo: information theory and error-correcting codes in Coq               *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later              *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg matrix.
Require Import Reals Lra.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop fdist.
Require Import proba jfdist entropy chap2.

(******************************************************************************)
(* Example 2.2.1 of T. M. Cover and J. A. Thomas. Elements of information     *)
(* theory. Wiley, 2006. 2nd edition                                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.
Local Open Scope proba_scope.

Module conditional_entropy_example.

Definition zero : 'I_4 := ord0.
Definition one : 'I_4 := @Ordinal 4 1 isT.
Definition two : 'I_4 := @Ordinal 4 2 isT.
Definition three : 'I_4 := @Ordinal 4 3 isT.

Definition f := [ffun x : 'I_4 * 'I_4 => [eta (fun=>0) with
(zero, zero) |-> (1/8), (zero, one) |-> (1/16), (zero, two) |-> (1/16), (zero, three) |-> (1/4),
(one, zero) |-> (1/16), (one, one) |-> (1/8), (one, two) |-> (1/16), (one, three) |-> 0,
(two, zero) |-> (1/32), (two, one) |-> (1/32), (two, two) |-> (1/16), (two, three) |-> 0,
(three, zero) |-> (1/32), (three, one) |-> (1/32), (three, two) |-> (1/16), (three, three) |-> 0] x].

Lemma f0 : forall x, 0 <= f x.
Proof.
move=> x; rewrite ffunE; move: x.
case => -[ [? [[|[|[|[|[]//]]]]]
  | [? [[|[|[|[|[]//]]]]]
  | [? [[|[|[|[|[]//]]]]]
  | [? [[|[|[|[|[]//]]]]] | []//]]]]]; rewrite /f /=; try lra.
Qed.

Lemma f1 : \sum_(x in {: 'I_4 * 'I_4}) f x = 1.
Proof.
rewrite (eq_bigr (fun x => f (x.1, x.2))); last by case.
rewrite -(pair_bigA _ (fun x1 x2 => f (x1, x2))) /=.
rewrite !big_ord_recl !big_ord0 /f /= !ffunE /=; field.
Qed.

Definition d : {fdist 'I_4 * 'I_4} := locked (FDist.make f0 f1).

Lemma dE x : d x = f x.
Proof. by rewrite /d; unlock. Qed.

Definition conditional_entropy := CondEntropy.h d.

Lemma conditional_entropyE : conditional_entropy = 11/8.
Proof.
rewrite /conditional_entropy /CondEntropy.h /=.
rewrite !big_ord_recl big_ord0 !Bivar.sndE /=.
rewrite !big_ord_recl !big_ord0 !dE /f /=.
rewrite /CondEntropy.h1 /=.
rewrite !big_ord_recl !big_ord0 /jcPr /Pr !(big_setX,big_set1) !dE /f /=.
rewrite !Bivar.sndE /=.
rewrite !big_ord_recl !big_ord0 !dE /f !ffunE /=.
rewrite !(addR0,add0R,div0R,mul0R).
repeat (rewrite logDiv; try lra).
rewrite !log1 !sub0R !log4 !log8 !log16 !log32.
rewrite [X in log X](_ : _ = 1/4); last lra.
rewrite !div1R logV; last lra.
rewrite !log4.
rewrite [X in log X](_ : _ = 1/4); last lra.
rewrite !div1R logV; last lra.
rewrite !log4.
rewrite [X in log X](_ : _ = 1/4); last lra.
rewrite !div1R logV; last lra.
rewrite !log4.
field.
Qed.

End conditional_entropy_example.
