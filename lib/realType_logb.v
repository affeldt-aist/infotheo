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

Lemma le_ln1Dx x : -1 < x -> ln (1 + x) <= x.
Proof.
(*this will be in MathComp-Analysis 1.5.0*)
Admitted.

Lemma expR_gt1Dx x : x != 0 -> 1 + x < expR x.
Proof.
(*this will be in MathComp-Analysis 1.5.0*)
Admitted.

(* TODO: add to MCA? *)
Lemma lt_ln1Dx x : 0 < x -> ln (1 + x) < x.
Proof.
move=> x1.
rewrite -ltr_expR lnK ?expR_gt1Dx//.
  by rewrite gt_eqF//.
by rewrite posrE addrC -ltrBlDr sub0r (le_lt_trans _ x1)// lerN10.
Qed.

Lemma ln_id_cmp x : 0 < x -> ln x <= x - 1.
Proof.
move=> x0; rewrite -{1}(GRing.subrK 1 x) addrC le_ln1Dx//.
by rewrite -ltrBlDr opprK addrC subrr.
Qed.

Lemma ln_id_eq x : 0 < x -> ln x = x - 1 -> x = 1 :> R.
Proof.
move=> x0 x1lnx.
have [x1|x1|//] := Order.TotalTheory.ltgtP x 1.
- exfalso.
  move: x1lnx; apply/eqP; rewrite lt_eqF//.
  rewrite -ltr_expR lnK//.
  rewrite -{1}(GRing.subrK 1 x) addrC.
  by rewrite expR_gt1Dx// subr_eq0 lt_eqF//.
- exfalso.
  move: x1lnx; apply/eqP; rewrite lt_eqF//.
  by rewrite -{1}(GRing.subrK 1 x) addrC lt_ln1Dx// subr_gt0.
Qed.

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

Section Exp.
Context {R : realType}.

Definition Exp (n : nat) (x : R) := expR (x * ln n%:R).

Lemma pow_Exp (x : nat) n : (0 < x)%N -> x%:R ^+ n = Exp x n%:R.
Proof. by move=> x0; rewrite /Exp expRM_natl lnK// posrE ltr0n. Qed.

Lemma LogK n x : (1 < n)%N -> 0 < x -> Exp n (Log n x) = x.
Proof.
move=> n1 x0.
rewrite /Log /Exp prednK// 1?ltnW// -mulrA mulVf// ?mulr1 ?lnK//.
by rewrite gt_eqF// -ln1 ltr_ln// ?posrE// ?ltr1n// ltr0n ltnW.
Qed.

Lemma Exp_oppr n x : Exp n (- x) = (Exp n x)^-1.
Proof. by rewrite /Exp mulNr expRN. Qed.

Lemma Exp_gt0 n x : 0 < Exp n x. Proof. by rewrite /Exp expR_gt0. Qed.

Lemma Exp_ge0 n x : 0 <= Exp n x. Proof. exact/ltW/Exp_gt0. Qed.

Lemma Exp_increasing n x y : (1 < n)%N -> x < y -> Exp n x < Exp n y.
Proof. by move=> ? ?; rewrite ltr_expR// ltr_pM2r// ln_gt0// ltr1n. Qed.

Lemma Exp_le_increasing n x y : (1 < n)%N -> x <= y -> Exp n x <= Exp n y.
Proof.
move=> n1; rewrite /Exp le_eqVlt => /predU1P[->//|].
by move/Exp_increasing => x_y; exact/ltW/x_y.
Qed.

End Exp.

Hint Extern 0 (0 < Exp _ _) => solve [exact/Exp_gt0] : core.

Hint Extern 0 (0 <= Exp _ _) => solve [exact/Exp_ge0] : core.

Section log.
Context {R : realType}.
Implicit Types x y : R.

Definition log {R : realType} (x : R) := Log 2 x.

Lemma log1 : log 1 = 0 :> R. Proof. by rewrite /log Log1. Qed.

Lemma log2 : log 2 = 1 :> R. Proof. by rewrite /log /Log prednK// divff// gt_eqF// ln2_gt0. Qed.

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

Lemma log_prodr_sumr_mlog {R : realType} {A : finType} (f : A -> R) s :
  (forall a, 0 <= f a) ->
  (forall i, 0 < f i) ->
  (- log (\prod_(i <- s) f i) = \sum_(i <- s) - log (f i))%R.
Proof.
move=> f0 f0'.
elim: s => [|h t ih].
  by rewrite !big_nil log1 oppr0.
rewrite big_cons logM//; last first.
  by apply/prodr_gt0 => a _.
by rewrite [RHS]big_cons opprD ih.
Qed.
