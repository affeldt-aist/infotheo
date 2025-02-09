(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum interval.
From mathcomp Require Import ring lra.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import set_interval.
From mathcomp Require Import reals Rstruct topology normedtype.
From mathcomp Require Import realfun derive exp.
Require Import realType_ext ssralg_ext.

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


End is_derive.

Section near_eq.

Lemma open_norm_subball (R : numFieldType) (M : normedModType R)
  (A : set M) (x : M) :
  open A -> A x ->
  \forall e \near ((0 : R)^')%classic, (ball x `|e| `<=` A)%classic.
Proof.
move/(@conj (open A) _)/[apply]/open_nbhs_nbhs/nbhsr0P.
rewrite -!nbhs_nearE=> H.
under [X in nbhs _ X]funext=> e.
  rewrite /subset.
  under eq_forall=> y do rewrite -ball_normE /=.
  over.
case: H=> e /= e0 He.
exists e=> //= e' /=.
rewrite distrC subr0=> e'e e'0 y xye'.
apply: (He `|e'|).
- by rewrite /= distrC subr0 normr_id.
- by rewrite normr_gt0.
- exact: ltW.
Qed.

Local Notation DQ f v a h := (h^-1 *: (f (h *: v + a) - f a)).

Let near_eq_difference_quotient (R : numFieldType) (V W : normedModType R)
  (f g : V -> W) (a v : V) :
  v != 0 -> (\near a, f a = g a) ->
  \forall h \near nbhs (0^')%classic, DQ f v a h = DQ g v a h.
Proof.
move=> vn0 fg.
have fg0: \forall h \near (0^')%classic, f (h *: v + a) = g (h *: v + a).
  have:= fg.
  rewrite -!nbhs_nearE nbhsE => -[] U [] oU Ua Ufg.
  have:= open_norm_subball oU Ua; case=> e /= e0 eU.
  exists (e * `|2 *: v|^-1)=> /=.
    rewrite mulr_gt0// invr_gt0 normrZ mulr_gt0// ?(normr_gt0 v)//.
    by rewrite normr_nat ltr0Sn.
  move=> h /= /[1!distrC] /[!subr0] he2v h0.
  apply/(Ufg (h *: v + a))/(eU (h * `| 2 *: v|)).
  - rewrite /= distrC subr0 normrM normr_id -ltr_pdivlMr//.
    rewrite normrZ mulr_gt0// ?(normr_gt0 v)//.
    by rewrite normr_nat ltr0Sn.
  - rewrite mulf_neq0// normrZ.
    rewrite mulf_neq0// normr_eq0//.
    by rewrite pnatr_eq0.
  - rewrite -ball_normE /=.
    rewrite opprD addrCA subrr addr0 normrN !normrZ !normr_id.
    rewrite mulrCA ltr_pMl// ?mulr_gt0// ?normr_gt0//.
    by rewrite [ltLHS](_ : 1 = 1%:R)// normr_nat ltr_nat.
have:= fg0 => /filterS; apply=> h ->.
move: fg.
by rewrite -nbhs_nearE nbhsE=> -[] U [] oU Ua /(_ a Ua) ->.
Qed.

Lemma near_eq_derive (R : numFieldType) (V W : normedModType R)
  (f g : V -> W) (a v : V) :
  v != 0 -> (\near a, f a = g a) -> 'D_v f a = 'D_v g a.
Proof.
move=> vn0 fg.
rewrite /derive.
suff-> : (DQ f v a h @[h --> 0^'])%classic = (DQ g v a h @[h --> 0^'])%classic
  by [].
have Dfg := near_eq_difference_quotient vn0 fg.
rewrite eqEsubset; split; apply: near_eq_cvg=> //.
by move/filterS: Dfg; apply=> ?; exact: fsym.
Qed.

Lemma near_eq_derivable (R : numFieldType) (V W : normedModType R)
  (f g : V -> W) (a v : V) :
  v != 0 -> (\near a, f a = g a) -> derivable f a v = derivable g a v.
Proof.
move=> vn0 nfg.
rewrite /derivable.
suff-> : (DQ f v a h @[h --> 0^'])%classic = (DQ g v a h @[h --> 0^'])%classic
  by [].
have Dfg := near_eq_difference_quotient vn0 nfg.
rewrite eqEsubset; split; apply: near_eq_cvg=> //.
by move/filterS: Dfg; apply=> ?; exact: fsym.
Qed.

Lemma near_eq_is_derive (R : numFieldType) (V W : normedModType R)
  (f g : V -> W) (a v : V) (df : W) :
  v != 0 -> (\near a, f a = g a) ->
  is_derive a v f df = is_derive a v g df.
Proof.
move=> vn0; move: f g.
suff fg f g (nfg : \near a, f a = g a) :
  is_derive a v f df -> is_derive a v g df.
  move=> f g nfg; apply: propext; split; apply: fg => //.
  suff->: (\near a, g a = f a) = (\near a, f a = g a) by [].
  by apply: eq_near=> ?; split; exact: esym.
move/[dup]/@ex_derive=> H.
move/@derive_val<-.
rewrite (near_eq_derive vn0 nfg).
apply/derivableP.
by rewrite -(near_eq_derivable vn0 nfg).
Qed.

End near_eq.
Arguments near_eq_derive [R V W] f g [a].
Arguments near_eq_derivable [R V W] f g [a].
Arguments near_eq_is_derive [R V W] f g [a].

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
