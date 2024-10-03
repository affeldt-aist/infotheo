(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import reals exp sequences.
Require Import realType_ext.

(******************************************************************************)
(*                          log_n x and n ^ x                                 *)
(*                                                                            *)
(* Definitions and lemmas about the logarithm and the exponential in base n.  *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   log == Log in base 2                                                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Import Order.POrderTheory GRing.Theory Num.Theory.

Section ln_ext.
Context {R : realType}.
Implicit Type x : R.

Lemma ln2_gt0 : 0 < ln 2 :> R. Proof. by rewrite ln_gt0// ltr1n. Qed.

Lemma ln2_neq0 : ln 2 != 0 :> R. Proof. by rewrite gt_eqF// ln2_gt0. Qed.

Lemma ln2_ge0 : 0 <= ln 2 :> R. Proof. by rewrite ltW// ln2_gt0. Qed.

Lemma ln_id_cmp x : 0 < x -> ln x <= x - 1.
Proof.
move=> x0.
Admitted.

Lemma ln_id_eq x : 0 < x -> ln x = x - 1 -> x = 1 :> R.
Proof.
Admitted.

End ln_ext.

Section xlnx.
Context {R : realType}.

Definition xlnx (x : R) : R := if (0 < x)%mcR then x * ln x else 0.

Lemma xlnx_0 : xlnx 0 = 0.
Proof. by rewrite /xlnx mul0r ltxx. Qed.

Lemma xlnx_1 : xlnx 1 = 0.
Proof. by rewrite /xlnx ltr01 mul1r ln1. Qed.

End xlnx.


Section Log.
Context {R : realType}.

Definition Log (n : nat) x : R := ln x / ln n.-1.+1%:R.

Lemma Log1 (n : nat) : Log n 1 = 0 :> R.
Proof. by rewrite /Log ln1 mul0r. Qed.

Lemma ler_Log (n : nat) : (1 < n)%N  -> {in Num.pos &, {mono Log n : x y / x <= y :> R}}.
Proof.
move=> n1 x y x0 y0.
rewrite /Log ler_pdivrMr prednK ?(leq_trans _ n1)// ?ln_gt0 ?ltr1n//.
by rewrite -mulrA mulVf ?mulr1 ?gt_eqF ?ln_gt0 ?ltr1n// ler_ln.
Qed.

Lemma LogV n x : 0 < x -> Log n x^-1 = - Log n x.
Proof. by move=> x0; rewrite /Log lnV ?posrE// mulNr. Qed.

Lemma LogM n x y : 0 < x -> 0 < y -> Log n (x * y) = Log n x + Log n y.
Proof. by move=> *; rewrite /Log -mulrDl lnM. Qed.

Lemma LogDiv n x y : 0 < x -> 0 < y -> Log n (x / y) = Log n x - Log n y.
Proof. by move=> x0 y0; rewrite LogM ?invr_gt0// LogV. Qed.

End Log.


Section log.
Context {R : realType}.
Implicit Types x y : R.

Definition log {R : realType} (x : R) := Log 2 x.

Lemma log1 : log 1 = 0 :> R. Proof. by rewrite /log Log1. Qed.

Lemma ler_log : {in Num.pos &, {mono log : x y / x <= y :> R}}.
Proof. by move=> x y x0 y0; rewrite /log ler_Log. Qed.

Lemma logV x : 0 < x -> log x^-1 = - log x :> R.
Proof. by move=> x0; rewrite /log LogV. Qed.

Lemma logM x y : 0 < x -> 0 < y -> log (x * y) = log x + log y.
Proof. move=> x0 y0; exact: (@LogM _ 2 _ _ x0 y0). Qed.

Lemma logDiv x y : 0 < x -> 0 < y -> log (x / y) = log x - log y.
Proof. by move=> x0 y0; exact: (@LogDiv _ _ _ _ x0 y0). Qed.

(* TODO: rename, lemma for Log *)
Lemma logexp1E : log (expR 1) = (ln 2)^-1 :> R.
Proof. by rewrite /log /Log/= expRK div1r. Qed.

Lemma log_exp1_Rle_0 : 0 <= log (expR 1) :> R.
Proof.
rewrite logexp1E.
rewrite invr_ge0// ltW//.
by rewrite ln2_gt0//.
Qed.

Lemma log_id_cmp x : 0 < x -> log x <= (x - 1) * log (expR 1).
Proof.
move=> x0; rewrite logexp1E ler_wpM2r// ?invr_ge0//= ?(ltW (@ln2_gt0 _))//.
exact/ln_id_cmp.
Qed.


End log.
