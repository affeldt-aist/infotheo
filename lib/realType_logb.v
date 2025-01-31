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

Lemma Log_increasing_le n x y : (1 < n)%N -> 0 < x -> x <= y -> Log n x <= Log n y.
Proof.
move=> n1 x0 xy.
apply ler_wpM2r.
  rewrite invr_ge0// ltW// ln_gt0//.
  by case: n n1 => //= n; rewrite ltr1n.
by rewrite ler_ln// posrE (lt_le_trans x0).
Qed.

End Log.

Section Exp.
Context {R : realType}.
Implicit Type x : R.

(* TODO: rename *)
Lemma pow_Exp (x : R) n : (0 <= x) -> x ^+ n = x `^ n%:R.
Proof. by move=> x0; rewrite powR_mulrn. Qed.

Lemma LogK n x : (1 < n)%N -> 0 < x -> n%:R `^ (Log n x) = x.
Proof.
move=> n1 x0.
rewrite /Log prednK// 1?ltnW//.
rewrite powRrM {1}/powR ifF; last first.
  by apply/negbTE; rewrite powR_eq0 negb_and pnatr_eq0 gt_eqF// ltEnat/= ltnW.
rewrite ln_powR mulrCA mulVf//.
  by rewrite mulr1 lnK ?posrE.
by rewrite gt_eqF// -ln1 ltr_ln ?posrE// ?ltr1n// ltr0n ltnW.
Qed.

(* TODO: rm *)
Lemma Exp_oppr n x : n `^ (- x) = (n `^ x)^-1.
Proof. by rewrite -powRN. Qed.

(* TODO: rm *)
Lemma Exp_gt0 n x : 0 < n -> 0 < n `^ x.
Proof. by move=> ?; rewrite powR_gt0. Qed.

(* TODO: rm *)
Lemma Exp_ge0 n x : 0 <= n `^ x. Proof. by rewrite powR_ge0. Qed.

(* TODO: rename *)
Lemma Exp_increasing n x y : 1 < n -> x < y -> n `^ x < n `^ y.
Proof.
move=> n1 xy; rewrite /powR ifF; last first.
  by apply/negbTE; rewrite gt_eqF// (lt_trans _ n1).
rewrite ifF//; last first.
  by apply/negbTE; rewrite gt_eqF// (lt_trans _ n1).
by rewrite ltr_expR// ltr_pM2r// ln_gt0// ltr1n.
Qed.

(* TODO: rename *)
Lemma Exp_le_increasing n x y : 1 < n -> x <= y -> n `^ x <= n `^ y.
Proof. by move=> n1 xy; rewrite ler_powR// ltW. Qed.

End Exp.

Hint Extern 0 (0 <= _ `^ _) => solve [exact/Exp_ge0] : core.

Section log.
Context {R : realType}.
Implicit Types x y : R.

Definition log {R : realType} (x : R) := Log 2 x.

Lemma log1 : log 1 = 0 :> R. Proof. by rewrite /log Log1. Qed.

Lemma log2 : log 2 = 1 :> R. Proof. by rewrite /log /Log prednK// divff// gt_eqF// ln2_gt0. Qed.

Lemma ler_log : {in Num.pos &, {mono log : x y / x <= y :> R}}.
Proof. by move=> x y x0 y0; rewrite /log ler_Log. Qed.

Lemma logK x : 0 < x -> 2 `^ (log x) = x.
Proof. by move=> x0; rewrite /log LogK. Qed.

Lemma logV x : 0 < x -> log x^-1 = - log x :> R.
Proof. by move=> x0; rewrite /log LogV. Qed.

Lemma logM x y : 0 < x -> 0 < y -> log (x * y) = log x + log y.
Proof. move=> x0 y0; exact: (@LogM _ 2 _ _ x0 y0). Qed.

Lemma logX2 n : log (2 ^+ n) = n%:R :> R.
Proof.
elim: n; rewrite ?expr0 ?log1// => n ih.
by rewrite exprS logM ?exprn_gt0// ih log2 nat1r.
Qed.

Lemma log4 : log 4 = 2 :> R.
Proof.
rewrite (_ : 4 = 2 ^+ 2); last by rewrite -natrX.
by rewrite logX2.
Qed.

Lemma log8 : log 8 = 3 :> R.
Proof.
rewrite (_ : 8 = 2 ^+ 3); last by rewrite -natrX.
by rewrite logX2.
Qed.

Lemma log16 : log 16 = 4 :> R.
Proof.
rewrite (_ : 16 = 2 ^+ 4); last by rewrite -natrX.
by rewrite logX2.
Qed.

Lemma log32 : log 32 = 5 :> R.
Proof.
rewrite (_ : 32 = 2 ^+ 5); last by rewrite -natrX.
by rewrite logX2.
Qed.

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

Lemma log_powR (a x : R) : log (a `^ x) = x * log a.
Proof.
by rewrite /log /Log ln_powR// mulrA.
Qed.

Lemma log_increasing (a b : R) : 0 < a -> a < b -> log a < log b.
Proof.
move=> Ha a_b.
rewrite /log /Log prednK// ltr_pM2r ?invr_gt0 ?ln2_gt0//.
by rewrite ltr_ln ?posrE// (lt_trans _ a_b).
Qed.

Lemma log_increasing_le x y : 0 < x -> x <= y -> log x <= log y.
Proof. by move=> x0 xy; exact: (@Log_increasing_le R 2 _ _ isT x0 xy). Qed.

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

From mathcomp Require Import topology normedtype.

Lemma exp_strict_lb {R : realType} (n : nat) (x : R) :
  0 < x -> x ^+ n / n`!%:R < expR x.
Proof.
move=> x0.
case: n => [|n].
  by rewrite expr0 fact0 mul1r invr1 pexpR_gt1.
rewrite exp.expRE.
rewrite (lt_le_trans _ (nondecreasing_cvgn_le _ _ n.+2))//=.
- rewrite /pseries/= /series/=.
  rewrite big_mkord big_ord_recr/=.
  rewrite [in ltRHS]mulrC ltrDr lt_neqAle; apply/andP; split.
    rewrite eq_sym psumr_neq0//=.
      apply/hasP; exists ord0.
        by rewrite mem_index_enum.
      by rewrite fact0 expr0 invr1 mulr1.
    move=> i _.
    by rewrite mulr_ge0 ?exprn_ge0 ?invr_ge0// ltW.
  rewrite sumr_ge0// => i _.
  by rewrite mulr_ge0 ?invr_ge0// exprn_ge0// ltW.
- move=> a b ab.
  rewrite /pseries/=.
  rewrite /series/=.
  rewrite -(subnKC ab).
  rewrite /index_iota !subn0.
  rewrite iotaD big_cat//=.
  rewrite ler_wpDr// sumr_ge0// => i _.
  by rewrite mulr_ge0 ?invr_ge0// exprn_ge0// ltW.
- have := is_cvg_series_exp_coeff_pos x0.
  rewrite /exp_coeff /pseries.
  rewrite /series/=.
  by under boolp.eq_fun do under eq_bigr do rewrite mulrC.
Qed.
