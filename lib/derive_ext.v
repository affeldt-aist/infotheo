(* infotheo: information theory and error-correcting codes in Coq               *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum interval.
From mathcomp Require Import ring lra.
From mathcomp Require Import mathcomp_extra classical_sets functions.
From mathcomp Require Import set_interval.
From mathcomp Require Import reals Rstruct topology normedtype.
From mathcomp Require Import realfun derive exp.
Require Import realType_ext realType_logb ssralg_ext.

(******************************************************************************)
(*        Additional lemmas about differentiation and derivatives             *)
(*                                                                            *)
(* Variants of lemmas (mean value theorem, etc.) from mathcomp-analysis       *)
(*                                                                            *)
(* TODO: document lemmas                                                      *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.

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

Section is_derive.

Lemma is_deriveD_eq [R : numFieldType] [V W : normedModType R] [f g : V -> W]
  [x v : V] [Df Dg D : W] :
  is_derive x v f Df -> is_derive x v g Dg -> Df + Dg = D ->
  is_derive x v (f + g) D.
Proof. by move=> ? ? <-; exact: is_deriveD. Qed.

Lemma is_deriveB_eq [R : numFieldType] [V W : normedModType R] [f g : V -> W]
  [x v : V] [Df Dg D : W] :
  is_derive x v f Df -> is_derive x v g Dg -> Df - Dg = D ->
  is_derive x v (f - g) D.
Proof. by move=> ? ? <-; exact: is_deriveB. Qed.

Lemma is_deriveN_eq [R : numFieldType] [V W : normedModType R] [f : V -> W]
  [x v : V] [Df D : W] :
  is_derive x v f Df -> - Df = D -> is_derive x v (- f) D.
Proof. by move=> ? <-; exact: is_deriveN. Qed.

Lemma is_deriveM_eq [R : numFieldType] [V : normedModType R] [f g : V -> R]
  [x v : V] [Df Dg D : R] :
  is_derive x v f Df -> is_derive x v g Dg ->
  f x *: Dg + g x *: Df = D ->
  is_derive x v (f * g) D.
Proof. by move=> ? ? <-; exact: is_deriveM. Qed.

Lemma is_deriveV_eq [R : realType] [f : R -> R] [x v Df D : R] :
  f x != 0 ->
  is_derive x v f Df ->
  - f x ^- 2 *: Df = D ->
  is_derive x v (inv_fun f) D.
Proof. by move=> ? ? <-; exact: is_deriveV. Qed.

Lemma is_deriveZ_eq [R : numFieldType] [V W : normedModType R] [f : V -> W]
  (k : R) [x v : V] [Df D : W] :
  is_derive x v f Df -> k *: Df = D ->
  is_derive x v (k \*: f) D.
Proof. by move=> ? <-; exact: is_deriveZ. Qed.

Lemma is_deriveX_eq [R : numFieldType] [V : normedModType R] [f : V -> R]
  (n : nat) [x v : V] [Df D: R] :
  is_derive x v f Df -> (n.+1%:R * f x ^+ n) *: Df = D ->
  is_derive x v (f ^+ n.+1) D.
Proof. by move=> ? <-; exact: is_deriveX. Qed.

Lemma is_derive_sum_eq [R : numFieldType] [V W : normedModType R] [n : nat]
  [h : 'I_n -> V -> W] [x v : V] [Dh : 'I_n -> W] [D : W] :
  (forall i : 'I_n, is_derive x v (h i) (Dh i)) ->
  \sum_(i < n) Dh i = D ->
  is_derive x v (\sum_(i < n) h i) D.
Proof. by move=> ? <-; exact: is_derive_sum. Qed.

Lemma is_derive1_lnf [R : realType] [f : R -> R] [x Df : R] :
  is_derive x 1 f Df -> 0 < f x ->
  is_derive x 1 (ln (R := R) \o f) (Df / f x).
Proof.
move=> hf fx0.
rewrite mulrC; apply: is_derive1_comp.
exact: is_derive1_ln.
Qed.

Lemma is_derive1_lnf_eq [R : realType] [f : R -> R] [x Df D : R] :
  is_derive x 1 f Df -> 0 < f x ->
  Df / f x = D ->
  is_derive x 1 (ln (R := R) \o f) D.
Proof. by move=> ? ? <-; exact: is_derive1_lnf. Qed.

Lemma is_derive1_Logf [R : realType] [f : R -> R] [n : nat] [x Df : R] :
  is_derive x 1 f Df -> 0 < f x -> (1 < n)%nat ->
  is_derive x 1 (Log n (R := R) \o f) ((ln n%:R)^-1 * Df / f x).
Proof.
move=> hf fx0 n1.
rewrite (mulrC _ Df) -mulrA mulrC.
apply: is_derive1_comp.
rewrite mulrC; apply: is_deriveM_eq.
  exact: is_derive1_ln.
by rewrite scaler0 add0r prednK ?mulr_regr // (@ltn_trans 1).
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

End is_derive.

Section derivable_monotone.

(* generalizing Ranalysis_ext.pderive_increasing_ax_{open_closed,closed_open} *)
Lemma derivable1_mono [R : realType] (a b : itv_bound R) (f : R -> R) (x y : R) :
  x \in Interval a b -> y \in Interval a b ->
  {in Interval a b, forall x, derivable f x 1} ->
  (forall t : R, forall Ht : t \in `]x, y[, 0 < 'D_1 f t) ->
  x < y -> f x < f y.
Proof.
rewrite !itv_boundlr=> /andP [ax xb] /andP [ay yb].
move=> derivable_f df_pos xy.
have HMVT1: ({within `[x, y], continuous f})%classic.
  apply: derivable_within_continuous=> z /[!itv_boundlr] /andP [xz zy].
  apply: derivable_f.
  by rewrite itv_boundlr (le_trans ax xz) (le_trans zy yb).
have HMVT0: forall z : R, z \in `]x, y[ -> is_derive z 1 f ('D_1 f z).
  move=> z /[!itv_boundlr] /andP [xz zy].
  apply/derivableP/derivable_f.
  rewrite itv_boundlr.
  rewrite (le_trans (le_trans ax (lexx x : BLeft x <= BRight x)%O) xz).
  by rewrite (le_trans (le_trans zy (lexx y : BLeft y <= BRight y)%O) yb).
rewrite -subr_gt0.
have[z xzy ->]:= MVT xy HMVT0 HMVT1.
by rewrite mulr_gt0// ?df_pos// subr_gt0.
Qed.

Lemma derivable1_homo [R : realType] (a b : itv_bound R) (f : R -> R) (x y : R) :
  x \in Interval a b -> y \in Interval a b ->
  {in Interval a b, forall x, derivable f x 1} ->
  (forall t:R, forall Ht : t \in `]x, y[, 0 <= 'D_1 f t) ->
  x <= y -> f x <= f y.
Proof.
rewrite !itv_boundlr=> /andP [ax xb] /andP [ay yb].
move=> derivable_f df_nneg xy.
have HMVT1: ({within `[x, y], continuous f})%classic.
  apply: derivable_within_continuous=> z /[!itv_boundlr] /andP [xz zy].
  apply: derivable_f.
  by rewrite itv_boundlr (le_trans ax xz) (le_trans zy yb).
have HMVT0: forall z : R, z \in `]x, y[ -> is_derive z 1 f ('D_1 f z).
  move=> z /[!itv_boundlr] /andP [xz zy].
  apply/derivableP/derivable_f.
  rewrite itv_boundlr.
  rewrite (le_trans (le_trans ax (lexx x : BLeft x <= BRight x)%O) xz).
  by rewrite (le_trans (le_trans zy (lexx y : BLeft y <= BRight y)%O) yb).
rewrite -subr_ge0.
move: xy; rewrite le_eqVlt=> /orP [/eqP-> | xy]; first by rewrite subrr.
have[z xzy ->]:= MVT xy HMVT0 HMVT1.
by rewrite mulr_ge0// ?df_nneg// subr_ge0 ltW.
Qed.

End derivable_monotone.