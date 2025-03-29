(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint archimedean.
From mathcomp Require Import interval.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import reals interval_inference topology normedtype.
From mathcomp Require Import derive sequences exp realfun.
Require Import ssralg_ext realType_ext derive_ext.

(**md**************************************************************************)
(* # log_n x and n ^ x                                                        *)
(*                                                                            *)
(* Definitions and lemmas about the logarithm and the exponential in base n.  *)
(* Results about the Analysis of ln:                                          *)
(*                                                                            *)
(* Definitions:                                                               *)
(* ```                                                                        *)
(*   log == Log in base 2                                                     *)
(* ```                                                                        *)
(*                                                                            *)
(* Section xlnx_sect:                                                         *)
(* - about the function x |-> x * ln x                                        *)
(* Section diff_xlnx:                                                         *)
(* - about the function x |-> xlnx (1 - x) - xlnx x                           *)
(* Section Rabs_xlnx:                                                         *)
(* - proof that | x - y | <= a implies | xlnx x - xlnx y | <= - xlnx a        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Import Order.TTheory GRing.Theory Num.Theory.

Import numFieldTopology.Exports.
Import numFieldNormedType.Exports.

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
rewrite -ltr_expR lnK.
  by rewrite expR_gt1Dx// gt_eqF.
by rewrite posrE addrC -ltrBlDr sub0r (le_lt_trans _ x1)// lerN10.
Qed.

Lemma ln_id_cmp x : 0 < x -> ln x <= x - 1.
Proof.
move=> x0.
rewrite -{1}(subrK 1 x) addrC le_ln1Dx//.
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

Section Log.
Context {R : realType}.
Implicit Type x : R.

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

(* TODO: deprecate; use ler_Log *)
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
Lemma powRrM' x (n : R) k : x `^ (n * k%:R) = (x `^ n) ^+ k.
Proof. by rewrite powRrM powR_mulrn// powR_ge0. Qed.

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

(* TODO: move to MCA? *)
Lemma gt1_ltr_powRr (n : R) x y : 1 < n -> x < y -> n `^ x < n `^ y.
Proof.
move=> n1 xy; rewrite /powR ifF; last first.
  by apply/negbTE; rewrite gt_eqF// (lt_trans _ n1).
rewrite ifF//; last first.
  by apply/negbTE; rewrite gt_eqF// (lt_trans _ n1).
by rewrite ltr_expR// ltr_pM2r// ln_gt0// ltr1n.
Qed.

(* TODO: move to MCA? *)
Lemma gt1_ler_powRr (n : R) x y : 1 < n -> x <= y -> n `^ x <= n `^ y.
Proof. by move=> n1 xy; rewrite ler_powR// ltW. Qed.

(* TODO: move *)
Lemma powR2D : {morph (fun x => 2 `^ x) : x y / x + y >-> x * y}.
Proof. by move=> ? ? /=; rewrite powRD// pnatr_eq0// implybT. Qed.

Lemma powR2sum (I : Type) (r : seq I) (P0 : pred I) (F : I -> R) :
  2 `^ (\sum_(i <- r | P0 i) F i) = \prod_(i <- r | P0 i) 2 `^ F i.
Proof.
by rewrite (big_morph [eta powR 2] powR2D (powRr0 2)).
Qed.

Lemma powRK n x : (1 < n)%N -> Log n (n%:R `^ x) = x :> R.
Proof.
move=> n1; rewrite /Log prednK// 1?ltnW// ln_powR mulrK //.
by apply/unitf_gt0/ln_gt0; rewrite ltr1n.
Qed.

End Exp.

Hint Extern 0 (0 <= _ `^ _) => solve [exact/powR_ge0] : core.
Hint Extern 0 (0 < _ `^ _) => solve [exact/powR_gt0] : core.

Section log.
Context {R : realType}.
Implicit Types x y : R.

Definition log x := Log 2 x.

Lemma log1 : log 1 = 0 :> R.
Proof. by rewrite /log Log1. Qed.

Lemma log2 : log 2 = 1 :> R.
Proof. by rewrite /log /Log divff// gt_eqF// ln2_gt0. Qed.

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
by rewrite logexp1E invr_ge0// ltW// ln2_gt0.
Qed.

Lemma log_id_cmp x : 0 < x -> log x <= (x - 1) * log (expR 1).
Proof.
move=> x0; rewrite logexp1E ler_wpM2r// ?invr_ge0//= ?(ltW (@ln2_gt0 _))//.
exact/ln_id_cmp.
Qed.

Lemma log_powR (a : R) x : log (a `^ x) = x * log a.
Proof.
by rewrite /log /Log ln_powR// mulrA.
Qed.

Lemma ltr_log (a b : R) : 0 < a -> a < b -> log a < log b.
Proof.
move=> Ha a_b.
rewrite /log /Log prednK// ltr_pM2r ?invr_gt0 ?ln2_gt0//.
by rewrite ltr_ln ?posrE// (lt_trans _ a_b).
Qed.

End log.

Lemma exists_frac_part {R : realType} (P : nat -> Prop) : (exists n, P n) ->
  forall num den, (0 < num)%N -> (0 < den)%N ->
  (forall n m, (n <= m)%N -> P n -> P m) ->
  exists n, P n /\
    frac_part (2 `^ (n%:R * (log num%:R / den%:R))) = 0 :> R.
Proof.
case=> n Pn num den Hden HP.
exists (n * den)%N.
split.
  apply H with n => //.
  by rewrite -{1}(muln1 n) leq_mul2l HP orbC.
rewrite natrM -mulrA (mulrCA den%:R) mulrV // ?mulr1; last first.
  by rewrite unitfE lt0r_neq0 // (ltr_nat R 0).
rewrite /frac_part mulrC powRrM.
rewrite (LogK (n:=2)) // ?ltr0n // powR_mulrn ?ler0n // -natrX.
by rewrite floorK ?subrr // intr_nat.
Qed.

Lemma log_prodr_sumr_mlog {R : realType} {A : finType} (f : A -> R) s :
  (forall a, 0 <= f a) ->
  (forall i, 0 < f i) ->
  - log (\prod_(i <- s) f i) = \sum_(i <- s) - log (f i).
Proof.
move=> f0 f0'.
elim: s => [|h t ih].
  by rewrite !big_nil log1 oppr0.
rewrite big_cons logM//; last exact/prodr_gt0.
by rewrite [RHS]big_cons opprD ih.
Qed.

Lemma log_exprz {R : realType} (n : nat) (r : R) :
  0 < r -> log (r ^ n) = n%:R * log r.
Proof.
elim: n => [|n' IH lt_0_r]; first by rewrite log1 mul0r.
rewrite exprSz logM ?exprn_gt0// IH//.
by rewrite -nat1r mulrDl mul1r.
Qed.

From mathcomp Require Import topology normedtype.

Lemma exp_strict_lb {R : realType} (n : nat) (x : R) :
  0 < x -> x ^+ n / n`!%:R < expR x.
Proof.
move=> x0.
case: n => [|n].
  by rewrite expr0 fact0 mul1r invr1 pexpR_gt1.
rewrite expRE.
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
  rewrite /pseries/= /series/=.
  rewrite -(subnKC ab) /index_iota !subn0 iotaD big_cat//=.
  rewrite ler_wpDr// sumr_ge0// => i _.
  by rewrite mulr_ge0 ?invr_ge0// exprn_ge0// ltW.
- have := is_cvg_series_exp_coeff_pos x0.
  rewrite /exp_coeff /pseries /series/=.
  by under boolp.eq_fun do under eq_bigr do rewrite mulrC.
Qed.

(* TODO: move to MCA *)
Lemma derivable_ln {R : realType} x : 0 < x -> derivable (@ln R) x 1.
Proof. by move=> x0; apply: ex_derive; exact: is_derive1_ln. Qed.

(* TODO: move *)
Lemma gt0_near_nbhs {R : realType} (x : R) : 0 < x ->
  \forall x0 \near nbhs x, 0 < x0.
Proof.
move=> x0.
exists (x / 2) => //=.
  by rewrite divr_gt0//.
move=> A/=.
have [//|A0] := ltP 0 A.
rewrite ltNge => /negP; rewrite boolp.falseE; apply.
rewrite ger0_norm ?subr_ge0; last first.
  by rewrite (le_trans A0)// ltW.
rewrite lerBrDr.
rewrite (@le_trans _ _ (x/2))//.
rewrite gerDl//.
by rewrite ler_piMr// ltW// invf_lt1// ltr1n.
Unshelve. all: by end_near. Qed.

(* TODO: PR to analysis *)
Lemma ltr0_derive1_decr (R : realType) (f : R -> R) (a b : R) :
  (forall x, x \in `]a, b[%R -> derivable f x 1) ->
  (forall x, x \in `]a, b[%R -> (f^`())%classic x < 0) ->
  {within `[a, b], continuous f}%classic ->
  forall x y, a <= x -> x < y -> y <= b -> f y < f x.
Proof.
move=> fdrvbl dflt0 ctsf x y leax ltxy leyb; rewrite -subr_gt0.
case: ltgtP ltxy => // xlty _.
have itvW : {subset `[x, y]%R <= `[a, b]%R}.
  by apply/subitvP; rewrite /<=%O /= /<=%O /= leyb leax.
have itvWlt : {subset `]x, y[%R <= `]a, b[%R}.
  by apply subitvP; rewrite /<=%O /= /<=%O /= leyb leax.
have fdrv z : z \in `]x, y[%R -> is_derive z 1 f (f^`() z)%classic.
  rewrite in_itv/= => /andP[xz zy]; apply: DeriveDef; last by rewrite derive1E.
  by apply: fdrvbl; rewrite in_itv/= (le_lt_trans _ xz)// (lt_le_trans zy).
have [] := @MVT _ f (f^`())%classic x y xlty fdrv.
  apply: (@continuous_subspaceW _ _ _ `[a, b]); first exact: itvW.
  by rewrite continuous_subspace_in.
move=> t /itvWlt dft dftxy; rewrite -oppr_lt0 opprB dftxy.
by rewrite pmulr_llt0 ?subr_gt0// dflt0.
Qed.

(* TODO: PR to analysis *)
Lemma gtr0_derive1_incr (R : realType) (f : R -> R) (a b : R) :
  (forall x, x \in `]a, b[%R -> derivable f x 1) ->
  (forall x, x \in `]a, b[%R -> 0 < (f^`())%classic x) ->
  {within `[a, b], continuous f}%classic ->
  forall x y, a <= x -> x < y -> y <= b -> f x < f y.
Proof.
move=> fdrvbl dfgt0 ctsf x y leax ltxy leyb.
rewrite -ltrN2; apply: (@ltr0_derive1_decr _ (\- f) a b).
- by move=> z zab; apply: derivableN; exact: fdrvbl.
- move=> z zab; rewrite derive1E deriveN; last exact: fdrvbl.
  by rewrite ltrNl oppr0 -derive1E dfgt0.
- by move=> z; apply: continuousN; exact: ctsf.
- exact: leax.
- exact: ltxy.
- exact: leyb.
Qed.

Section differentiable.

Lemma differentiable_ln {R : realType} (x : R) : 0 < x -> differentiable (@ln R) x.
Proof. move=>?; exact/derivable1_diffP/ex_derive/is_derive1_ln. Qed.

Lemma differentiable_Log {R : realType} (n : nat) (x : R) :
  0 < x -> (1 < n)%nat -> differentiable (@Log R n) x.
Proof.
move=> *.
apply: differentiableM.
  exact: differentiable_ln.
apply: differentiableV=> //.
rewrite prednK; last exact: (@ltn_trans 1).
by rewrite neq_lt ln_gt0 ?orbT// ltr1n.
Qed.

End differentiable.

Lemma is_derive1_Logf [R : realType] [f : R -> R] [n : nat] [x Df : R] :
  is_derive x 1 f Df -> 0 < f x -> (1 < n)%nat ->
  is_derive x 1 (Log n (R := R) \o f) ((ln n%:R)^-1 * Df / f x).
Proof.
move=> hf fx0 n1.
rewrite (mulrC _ Df) -mulrA mulrC.
apply: is_derive1_comp.
rewrite mulrC; apply: is_deriveM_eq.
  exact: is_derive1_ln.
rewrite scaler0 add0r prednK 1?(@ltn_trans 1)//.
by rewrite mulr_regl; exact: mulrC.
Qed.

Lemma is_derive1_Logf_eq [R : realType] [f : R -> R] [n : nat] [x Df D : R] :
  is_derive x 1 f Df -> 0 < f x -> (1 < n)%nat ->
  (ln n%:R)^-1 * Df / f x = D ->
  is_derive x 1 (Log n (R := R) \o f) D.
Proof. by move=> ? ? ? <-; exact: is_derive1_Logf. Qed.

Lemma is_derive1_LogfM [R : realType] [f g : R -> R] [n : nat] [x Df Dg : R] :
  is_derive x 1 f Df -> is_derive x 1 g Dg ->
  0 < f x -> 0 < g x -> (1 < n)%nat ->
  is_derive x 1 (Log n (R := R) \o (f * g)) ((ln n%:R)^-1 * (Df / f x + Dg / g x)).
Proof.
move=> hf hg fx0 gx0 n1.
apply: is_derive1_Logf_eq=> //.
  exact: mulr_gt0.
rewrite -!mulr_regr /(f * g) invfM /= -mulrA; congr (_ * _).
rewrite addrC (mulrC _^-1) mulrDl; congr (_ + _); rewrite -!mulrA;  congr (_ * _).
  by rewrite mulrA mulfV ?gt_eqF // div1r.
by rewrite mulrCA mulfV ?gt_eqF // mulr1.
Qed.

Lemma is_derive1_LogfM_eq [R : realType] [f g : R -> R] [n : nat] [x Df Dg D : R] :
  is_derive x 1 f Df -> is_derive x 1 g Dg ->
  0 < f x -> 0 < g x -> (1 < n)%nat ->
  (ln n%:R)^-1 * (Df / f x + Dg / g x) = D ->
  is_derive x 1 (Log n (R := R) \o (f * g)) D.
Proof. by move=> ? ? ? ? ? <-; exact: is_derive1_LogfM. Qed.

Lemma is_derive1_LogfV [R : realType] [f : R -> R] [n : nat] [x Df : R] :
  is_derive x 1 f Df -> 0 < f x -> (1 < n)%nat ->
  is_derive x 1 (Log n (R := R) \o (inv_fun f)) (- (ln n%:R)^-1 * (Df / f x)).
Proof.
move=> hf fx0 n1.
apply: is_derive1_Logf_eq=> //;
  [by apply/is_deriveV; rewrite gt_eqF | by rewrite invr_gt0 |].
rewrite invrK -mulr_regl !(mulNr,mulrN) -mulrA; congr (- (_ * _)).
by rewrite expr2 invfM mulrC !mulrA mulfV ?gt_eqF // div1r mulrC.
Qed.

Lemma is_derive1_LogfV_eq [R : realType] [f : R -> R] [n : nat] [x Df D : R] :
  is_derive x 1 f Df -> 0 < f x -> (1 < n)%nat ->
  - (ln n%:R)^-1 * (Df / f x) = D ->
  is_derive x 1 (Log n (R := R) \o (inv_fun f)) D.
Proof. by move=> ? ? ? <-; exact: is_derive1_LogfV. Qed.

Section xlnx_sect.

Section xlnx.
Context {R : realType}.

Definition xlnx_total (y : R) := y * ln y.

Lemma derivable_xlnx_total x : 0 < x -> derivable xlnx_total x 1.
Proof. by move=> x0; apply: derivableM => //; exact: derivable_ln. Qed.

Lemma xlnx_total_neg (x : R) : 0 < x < 1 -> xlnx_total x < 0.
Proof.
case/andP => lt0x ltx1.
rewrite -(opprK 0) ltrNr oppr0 -mulrN.
apply mulr_gt0 => //.
by rewrite ltrNr oppr0 ln_lt0// lt0x.
Qed.

Lemma continuous_at_xlnx_total (r : R) : 0 < r -> continuous_at r xlnx_total.
Proof. by move=> r0; apply: cvgM => //; exact: continuous_ln. Qed.

Definition xlnx (x : R) := if 0 < x then xlnx_total x else 0.

Lemma xlnx_0 : xlnx 0 = 0.
Proof. by rewrite /xlnx ltxx. Qed.

Lemma xlnx_1 : xlnx 1 = 0.
Proof. by rewrite /xlnx ltr01 /xlnx_total ln1 mulr0. Qed.

Lemma xlnx_neg x : 0 < x < 1 -> xlnx x < 0.
Proof. by move=> /andP[x0 x1]; rewrite /xlnx x0 xlnx_total_neg ?x0. Qed.

Lemma continuous_at_xlnx (r : R) : continuous_at r xlnx.
Proof.
apply/cvgrPdist_le => /= eps eps_pos.
have [r_gt0|r_lt0|<-{r}] := ltgtP 0 r.
- have := continuous_at_xlnx_total r_gt0.
  move=> /cvgrPdist_le/(_ _ eps_pos)[k/= k_pos Hk].
  exists (Num.min k r).
    by rewrite lt_min r_gt0 k_pos.
  move=> x/=; rewrite lt_min => /andP[rxk rxr].
  rewrite /xlnx r_gt0.
  have -> : 0 < x.
    rewrite -(addr0 x) -[in ltRHS](subrr r) addrA addrAC.
    apply (@le_lt_trans _ _ ((x + - r) + `| x + - r |)).
      by rewrite addrC -lerBlDr sub0r -normrN ler_norm.
    by rewrite ltrD2l distrC.
  exact: Hk.
- exists (- r).
    by rewrite ltrNr oppr0.
  move=> x/= rxr.
  rewrite /xlnx.
  have -> : 0 < x = false.
    apply/negbTE.
    rewrite -leNgt.
    rewrite -(addr0 x) -{1}(subrr r) addrA addrAC.
    apply (@le_trans _ _ ((x + - r) - `| x + - r |)).
      by rewrite lerD2l lerNr distrC ltW.
    by rewrite subr_le0 ler_norm.
  have -> : (0 < r) = false.
    by apply/negbTE; rewrite -leNgt; apply/ltW.
  by rewrite subrr normr0 ltW.
- exists (expR (- 2 / eps)); first by rewrite expR_gt0.
  move=> x/=; rewrite sub0r normrN => Hx2.
  rewrite /xlnx ltxx sub0r normrN.
  case: ifPn => Hcase; last by rewrite normr0 ltW.
  rewrite (ger0_norm (ltW Hcase)) in Hx2.
  rewrite -{1}(lnK Hcase).
  set X := ln x.
  have X_neg : X < 0.
    apply (@lt_trans _ _ (-2 / eps)).
      by rewrite -ltr_expR lnK.
    by rewrite mulNr ltrNl oppr0 divr_gt0//.
  apply/ltW.
  apply: (@lt_le_trans _ _ (2 / (- X))).
  + rewrite ltr0_norm; last first.
      by rewrite /xlnx_total pmulr_rlt0 ?expR_gt0 ?lnK.
    rewrite -mulrN.
    rewrite -(@ltr_pM2r _ ((- X)^-1)); last first.
      by rewrite invr_gt0 ltrNr oppr0.
    rewrite lnK// -mulrA divff ?mulr1; last first.
      by rewrite oppr_eq0 lt_eqF.
    rewrite -(invrK 2) -mulrA.
    rewrite invrN mulNr (mulrN (X^-1)) opprK -invfM -expr2 invrK.
    rewrite (_ : 2 = 2`!%:R)//.
    have := @exp_strict_lb _ 2 (- X).
    rewrite ltrNr oppr0 => /(_ X_neg).
    rewrite expRN.
    rewrite -[X in X < _ -> _]invrK.
    rewrite ltf_pV2 ?posrE ?expR_gt0 ?invr_gt0 ?mulr_gt0//=; last 3 first.
      by rewrite ltrNr oppr0.
      by rewrite ltrNr oppr0.
      by rewrite invr_gt0.
    by rewrite lnK// sqrrN invf_div.
  + move: Hx2.
    rewrite -ltr_ln ?posrE ?expR_gt0//.
    rewrite -/X.
    rewrite expRK.
    rewrite mulNr ltrNr.
    rewrite ltr_pdivrMr//.
    by rewrite -ltr_pdivrMl 1?ltrNr ?oppr0// mulrC => /ltW.
Qed.

Lemma derivable_xlnx x : 0 < x -> derivable xlnx x 1.
Proof.
move=> x0; rewrite (near_eq_derivable _ xlnx_total)//.
- exact: derivable_xlnx_total.
- near=> z.
  rewrite /xlnx ifT//.
  near: z.
  exact: gt0_near_nbhs.
Unshelve. all: by end_near. Qed.

Lemma derive_xlnxE x : 0 < x -> 'D_1 xlnx x = ln x + 1.
Proof.
move=> x_pos.
rewrite /xlnx.
transitivity ('D_1 (fun x0 : R^o => x0 * ln x0) x).
  apply: near_eq_derive.
    by rewrite oner_eq0.
  near=> z.
  rewrite ifT//.
  near: z.
  exact: gt0_near_nbhs.
rewrite deriveM//=; last exact: derivable_ln.
rewrite derive_val addrC; congr +%R.
  by rewrite /GRing.scale/= mulr1.
rewrite (@derive_val _ _ _ _ _ _ _ (is_derive1_ln x_pos)).
by rewrite -(@mulfV _ x)// gt_eqF.
Unshelve. all: by end_near. Qed.

(*
Lemma pderivable_Ropp_xlnx : pderivable (fun y => - xlnx y) (fun x => 0 < x <= exp (- 1)).
Proof.
move=> x /= Hx.
apply derivable_pt_opp.
apply derivable_pt_xlnx.
apply Hx.
Defined.

Lemma xlnx_sdecreasing_0_Rinv_e_helper : forall (t : R) (Ht : 0 < t <= exp (-1)),
  0 < (if t == exp (-1) then 1 else derive_pt (fun x => - xlnx x) t (pderivable_Ropp_xlnx Ht)).
Proof.
move=> t [t0 te]; case: ifPn => [//|] /eqP Hcase.
rewrite derive_pt_opp derive_pt_xlnx //.
rewrite ltR_oppr oppR0 addRC -ltR_subRL sub0R.
apply exp_lt_inv; by rewrite exp_ln // ltR_neqAle.
Qed.
*)

Lemma xlnx_sdecreasing_0_Rinv_e x y :
  0 <= x <= expR (-1) ->
  0 <= y <= expR (-1) -> x < y -> xlnx y < xlnx x.
Proof.
move=> /andP[x1 x2] /andP[y1 y2] xy.
have [->|x0] := eqVneq x 0.
- rewrite xlnx_0; apply xlnx_neg.
  rewrite (le_lt_trans x1 xy)/=.
  rewrite (le_lt_trans y2)//.
  by rewrite expR_lt1// ltrN10.
- rewrite -[X in _ < X]opprK ltrNr.
  have {}x0 : 0 < x.
    by rewrite lt_neqAle eq_sym x0 x1.
  have {x1 y1}y0 : 0 < y.
    by rewrite (le_lt_trans x1).
  apply: (@derivable1_mono _ (BRight 0) (BRight (expR (-1))) (fun x => - xlnx x)) => //.
  + by rewrite in_itv//= (x0).
  + by rewrite in_itv//= (y0).
  + move=> /= z.
    rewrite in_itv/= => /andP[z0 z1].
    apply: derivableN.
    by apply: derivable_xlnx => //.
  + move=> /= t.
    rewrite in_itv/= => /andP[tx ty].
    rewrite [ltRHS](_ : _ = 'D_1 (fun x : R => - (x * ln x)) t); last first.
      apply: near_eq_derive.
        by rewrite oner_eq0.
      near=> z.
      rewrite /xlnx.
      case: ifPn => z0 //.
      rewrite oppr0.
      by rewrite ln0 ?mulr0// ?oppr0// leNgt.
    rewrite deriveN; last first.
      apply: derivableM => //.
      apply: ex_derive.
      apply: is_derive1_ln.
      by rewrite (lt_trans _ tx).
    rewrite ltrNr oppr0.
    rewrite deriveM//; last first.
      apply: ex_derive.
      apply: is_derive1_ln.
      by rewrite (lt_trans _ tx).
    have := is_derive1_ln (lt_trans x0 tx).
    move/(@derive_val R R^o R^o) => ->.
    rewrite derive_id [X in X + _]mulfV ?gt_eqF//; last by rewrite (lt_trans x0).
    rewrite (@lt_le_trans _ _ (1 + ln y))//.
      rewrite ltrD2l.
      rewrite /GRing.scale/= mulr1.
      by rewrite ltr_ln ?posrE ?(lt_trans x0)// ltW.
    rewrite (@le_trans _ _ (1 + ln (expR (-1))))//.
      by rewrite lerD2l ler_ln ?posrE// expR_gt0.
      by rewrite expRK subrr.
Unshelve. all: by end_near. Qed.

Lemma xlnx_decreasing_0_Rinv_e x y :
  0 <= x <= expR (-1) -> 0 <= y <= expR (-1) -> x <= y -> xlnx y <= xlnx x.
Proof.
move=> Hx Hy Hxy.
have [->|/eqP H] := eqVneq x y; first by rewrite lexx.
apply/ltW/xlnx_sdecreasing_0_Rinv_e => //.
rewrite lt_neqAle Hxy andbT.
exact/eqP.
Qed.

End xlnx.

Section diff_xlnx.
Context {R : realType}.

Definition diff_xlnx (x : R) := xlnx (1 - x) - xlnx x.

Lemma derivable_pt_diff_xlnx x : 0 < x < 1 -> derivable diff_xlnx x 1.
Proof.
move=> /andP[x0 x1].
apply: derivableB.
  apply/derivable1_diffP.
  have := (@differentiable_comp _ _ _ _ (fun t : R^o => 1 - t)%R
    (xlnx: R^o -> R^o)).
  apply => //.
  apply/derivable1_diffP.
  apply: derivable_xlnx.
  by rewrite subr_gt0.
exact: derivable_xlnx.
Qed.

Lemma derive_pt_diff_xlnx x : 0 < x < 1 ->
  derivable diff_xlnx x 1 ->
  'D_1 diff_xlnx x = -(2 + ln (x * (1-x))).
Proof.
move=> /andP[] x0 x1 H.
rewrite deriveB/=; last 2 first.
  (* TODO: copy past *)
  apply/derivable1_diffP.
  have := (@differentiable_comp _ _ _ _ (fun t : R^o => 1 - t)%R xlnx).
  apply => //.
  apply/derivable1_diffP.
  apply: derivable_xlnx.
  by rewrite subr_gt0.
  exact: derivable_xlnx.
rewrite -derive1E derive1_comp; last 2 first.
  apply: derivableB.
    exact: derivable_cst.
  exact: derivable_id.
  apply: derivable_xlnx.
  by rewrite subr_gt0.
rewrite derive_xlnxE//.
rewrite [X in X * _]derive1E.
rewrite derive_xlnxE; last by rewrite subr_gt0.
rewrite derive1E deriveB; last 2 first.
  exact: derivable_cst.
  exact: derivable_id.
rewrite derive_cst derive_id sub0r mulrN1 -opprB; congr (- _).
rewrite opprK addrACA addrC; congr +%R.
by rewrite lnM// posrE subr_gt0.
Qed.

Lemma diff_xlnx_0 : diff_xlnx 0 = 0.
Proof. by rewrite /diff_xlnx subr0 xlnx_0 xlnx_1 subrr. Qed.

(*
Lemma diff_xlnx_1 : diff_xlnx 1 = 0.
Proof. by rewrite /diff_xlnx subRR xlnx_0 xlnx_1 subRR. Qed.
*)

Lemma derive_diff_xlnx_gt0 x : 0 < x < 1 -> x < expR (-2) -> 0 < 'D_1 diff_xlnx x.
Proof.
move=> /andP[x0 x1] xltexp2.
rewrite derive_pt_diff_xlnx; last 2 first.
  by rewrite x0.
  apply: derivable_pt_diff_xlnx.
  by rewrite x0.
rewrite ltrNr oppr0.
rewrite -[X in X + _]opprK addrC.
rewrite subr_lt0.
rewrite -ltr_expR lnK; last first.
  by rewrite posrE mulr_gt0// subr_gt0.
apply: (@lt_trans _ _ (expR (-2) * (1 - x))).
  by rewrite ltr_pM2r ?subr_gt0.
rewrite -[ltRHS]mulr1.
rewrite ltr_pM2l ?expR_gt0//.
by rewrite ltrBlDl addrC -ltrBlDl subrr.
Qed.

Lemma continuous_at_diff_xlnx (r : R) : continuous_at r diff_xlnx.
Proof.
move=> z.
apply: cvgB => //.
  apply: cvg_comp; last exact: continuous_at_xlnx.
  apply: cvgB => //.
  exact: cvg_cst.
by apply: continuous_at_xlnx.
Qed.

Lemma diff_xlnx_sincreasing_0_Rinv_e2 (x y : R) :
  0 <= x <= expR (-2) -> 0 <= y <= expR (-2) ->
  x < y -> diff_xlnx x < diff_xlnx y.
Proof.
move=> /andP[x0 x2] /andP[y0 y2] xy.
apply: (@gtr0_derive1_incr _ _ 0 (expR (- 2))) => //.
- move=> z; rewrite in_itv/= => /andP[z0 z2].
  apply: derivable_pt_diff_xlnx.
  by rewrite z0/= (lt_le_trans z2)// -[leRHS]expR0 ler_expR lerNl oppr0.
- move=> z; rewrite in_itv/= => /andP[z0 z2].
  rewrite derive1E derive_diff_xlnx_gt0// z0/=.
  by rewrite (lt_le_trans z2)// -[leRHS]expR0 ler_expR lerNl oppr0.
- apply: continuous_subspaceT => z.
  exact: continuous_at_diff_xlnx.
Qed.

Lemma xlnx_ineq (x : R) : 0 <= x <= expR (-2) -> xlnx x <= xlnx (1-x).
Proof.
move=> /andP[Hx1 Hx2].
rewrite -subr_ge0.
rewrite -diff_xlnx_0 -/(diff_xlnx x).
have [->|/eqP Hnot0] := eqVneq 0 x; first by rewrite lexx.
apply/ltW/diff_xlnx_sincreasing_0_Rinv_e2 => //.
  by rewrite lexx expR_ge0.
  by rewrite Hx1 Hx2.
rewrite lt_neqAle Hx1 andbT.
exact/eqP.
Qed.

End diff_xlnx.

Section Rabs_xlnx.
Context {R : realType}.

Definition xlnx_delta a (x : R) := xlnx (x + a) - xlnx x.

Lemma derivable_xlnx_delta (eps : R) (Heps : 0 < eps < 1) x (Hx : 0 < x < 1 - eps) :
  derivable (xlnx_delta eps) x 1.
Proof.
rewrite /xlnx_delta.
apply: derivableB => /=.
  apply/derivable1_diffP/differentiable_comp => //.
  apply/derivable1_diffP.
  apply: derivable_xlnx.
  move: Heps Hx => /andP[? _] /andP[? _].
  by rewrite addr_gt0.
apply: derivable_xlnx.
by case/andP : Hx.
Qed.

Lemma derive_pt_xlnx_delta eps (Heps : 0 < eps < 1) x (Hx : 0 < x < 1 - eps) :
  'D_1 (xlnx_delta eps) x = ln (x + eps) - ln x.
Proof.
rewrite deriveB//=; last 2 first.
  apply/derivable1_diffP/differentiable_comp => //.
  apply/derivable1_diffP.
  apply: derivable_xlnx.
  rewrite addr_gt0//.
  by case/andP: Hx.
  by case/andP: Heps.
  apply: derivable_xlnx.
  by case/andP : Hx.
rewrite derive_xlnxE; last first.
  by case/andP: Hx.
rewrite -derive1E.
rewrite derive1_comp//; last first.
  apply: derivable_xlnx.
  rewrite addr_gt0//.
  by case/andP: Hx.
  by case/andP: Heps.
rewrite derive1E derive_xlnxE; last first.
  rewrite addr_gt0//.
  by case/andP: Hx.
  by case/andP: Heps.
rewrite derive1E.
rewrite deriveD//.
rewrite derive_id derive_cst addr0 mulr1.
by rewrite opprD addrACA subrr addr0.
Qed.

Lemma continuous_at_xlnx_delta (r : R) eps : continuous_at r (xlnx_delta eps).
Proof.
move=> z.
apply: cvgB.
  apply: cvg_comp; last first.
    exact: continuous_at_xlnx.
  apply: cvgD.
    exact: cvg_id.
  exact: cvg_cst.
exact: continuous_at_xlnx.
Qed.

Lemma increasing_xlnx_delta eps (Heps : 0< eps < 1) :
  forall x y : R, 0 <= x <= 1 - eps -> 0 <= y <= 1 - eps -> x < y ->
                  xlnx_delta eps x < xlnx_delta eps y.
Proof.
move=> x y /andP[x0 x1] /andP[y0 y1] xy.
apply: (@gtr0_derive1_incr _ _ 0 (1 - eps)) => //.
- move=> z; rewrite in_itv/= => /andP[z0 z1].
  apply: derivable_xlnx_delta => //.
  by rewrite z0.
- move=> z; rewrite in_itv/= => /andP[z0 z1].
  rewrite derive1E derive_pt_xlnx_delta//.
    rewrite subr_gt0 ltr_ln ?posrE//.
      by rewrite ltrDl; case/andP : Heps.
    by rewrite addr_gt0//; case/andP : Heps.
  by rewrite z0.
- apply: continuous_subspaceT => z.
  exact: continuous_at_xlnx_delta.
Qed.

Lemma xlnx_delta_bound eps : 0 < eps <= expR (-2) ->
  forall x, 0 <= x <= 1 - eps -> `| xlnx_delta eps x | <= - xlnx eps.
Proof.
move=> /andP[Heps1 Heps2] x /andP[Hx1 Hx2].
rewrite ler_norml; apply/andP; split.
- rewrite opprK (_ : xlnx eps = xlnx_delta eps 0); last first.
    by rewrite /xlnx_delta add0r xlnx_0 subr0.
  have [->|xnot0] := eqVneq x 0; first by rewrite lexx.
  apply/ltW/increasing_xlnx_delta => //.
  + rewrite Heps1/=.
    by rewrite (le_lt_trans Heps2)// expR_lt1// ltrNl oppr0//.
  + rewrite lexx/= subr_ge0.
    rewrite (le_trans Heps2)//.
    by rewrite ltW// expR_lt1// ltrNl oppr0//.
  + by rewrite Hx1.
  + by rewrite lt_neqAle eq_sym xnot0.
- apply: (@le_trans _ _ (xlnx_delta eps (1 - eps))).
    have [->|xnot0] := eqVneq x (1 - eps); first by rewrite lexx.
    apply/ltW/increasing_xlnx_delta => //.
    + rewrite Heps1/=.
      by rewrite (le_lt_trans Heps2)// expR_lt1// ltrNl oppr0//.
    + by rewrite Hx1.
    + rewrite lexx andbT subr_ge0.
      rewrite (le_trans Heps2)//.
      by rewrite ltW// expR_lt1// ltrNl oppr0//.
    + by rewrite lt_neqAle xnot0/=.
  rewrite /xlnx_delta subrK xlnx_1 sub0r lerNr opprK.
  apply: xlnx_ineq.
  by rewrite (ltW Heps1)/=.
Qed.

(* TODO: rename *)
Lemma Rabs_xlnx (a : R) (Ha : 0 <= a <= expR (-2)) x y :
  0 <= x <= 1 -> 0 <= y <= 1 -> `| x - y | <= a ->
  `| xlnx x - xlnx y | <= - xlnx a.
Proof.
move=> /andP[Hx1 Hx2] /andP[Hy1 Hy2] H.
have [Hcase|Hcase|Hcase] := ltgtP x y.
- have Haux : y = x + `| x - y |.
    by rewrite distrC gtr0_norm ?subr_gt0 // addrC subrK.
  rewrite Haux -normrN opprD opprK addrC.
  apply (@le_trans _ _ (- xlnx `| x - y |)).
    apply xlnx_delta_bound.
    + apply/andP; split.
      * by rewrite distrC gtr0_norm ?subr_gt0.
      * apply (@le_trans _ _ a) => //.
        by case/andP: Ha.
    + by rewrite Hx1/= lerBrDr -Haux.
  rewrite lerNr opprK.
  apply xlnx_decreasing_0_Rinv_e => //.
  + apply/andP; split; first exact: normr_ge0.
    apply (@le_trans _ _ a) => //.
    apply (@le_trans _ _ (expR (- 2))).
      by case/andP: Ha.
    by rewrite ler_expR// lerN2 ler1n.
  + apply/andP; split.
      by case/andP : Ha.
    case/andP : Ha => Ha /le_trans; apply.
    by rewrite ler_expR// lerN2 ler1n.
- have Haux : x = y + `| x - y |.
    by rewrite gtr0_norm ?subr_gt0// addrCA subrr addr0.
  rewrite distrC in H Haux.
  rewrite Haux.
  apply (@le_trans _ _ (- xlnx `| y - x |)).
    apply xlnx_delta_bound.
    + apply/andP; split.
      * by rewrite distrC gtr0_norm ?subr_gt0.
      * rewrite (le_trans H)//.
        by case/andP : Ha.
    + by rewrite Hy1/= lerBrDr -Haux.
  rewrite lerNr opprK.
  apply xlnx_decreasing_0_Rinv_e => //.
    + apply/andP; split.
      * by rewrite ltr0_norm ?subr_lt0// opprB subr_ge0 ltW.
      * rewrite (le_trans H)//.
        case/andP : Ha => _ /le_trans; apply.
        by rewrite ler_expR lerN2 ler1n.
    + apply/andP; split.
        by case/andP : Ha.
      case/andP : Ha => _ /le_trans; apply.
      by rewrite ler_expR lerN2 ler1n.
- subst x ; rewrite subrr normr0 lerNr oppr0.
  have [<-|anot0] := eqVneq 0 a; first by rewrite xlnx_0 lexx.
  apply/ltW/xlnx_neg; apply/andP; split.
  + rewrite lt_neqAle anot0/=.
    by case/andP : Ha.
  + case/andP : Ha => _ /le_lt_trans; apply.
    by rewrite expR_lt1 ltrNl oppr0 ltr0n.
Qed.

End Rabs_xlnx.

End xlnx_sect.
