(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrfun ssrnat.
Require Import Reals Fourier.
Require Import Reals_ext Ranalysis_ext Rssr.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.

(** * Log base 2 *)

Lemma ln_2_pos : 0 < ln 2.
Proof. rewrite -ln_1; apply ln_increasing; fourier. Qed.

Lemma ln_2_neq0 : ln 2 <> 0.
Proof. by apply nesym, Rlt_not_eq, ln_2_pos. Qed.

Lemma ln_increasing_le a b : 0 < a -> a <= b -> ln a <= ln b.
Proof.
move=> Ha.
case/Rle_lt_or_eq_dec; last by move=> ->; exact: Rle_refl.
by move/(ln_increasing _ _ Ha)/ltRW.
Qed.

Lemma exp_le_inv x y : exp x <= exp y -> x <= y.
Proof.
case/Rle_lt_or_eq_dec; [move/exp_lt_inv => ?; exact/ltRW |
  move/exp_inv => ->; exact: Rle_refl].
Qed.

Lemma exp_pow n : forall k, exp (INR k * n) = (exp n) ^ k.
Proof.
elim => [|k IH]; first by rewrite mul0R exp_0.
by rewrite S_INR mulRDl mul1R exp_plus IH mulRC.
Qed.

(* NB: log is 0 for input < 0 *)
Definition log x := ln x / ln 2.

Lemma log_1 : log 1 = 0.
Proof. by rewrite /log ln_1 div0R. Qed.

Lemma log_2 : log 2 = 1.
Proof. rewrite /log /Rdiv mulRV //; exact: ln_2_neq0. Qed.

Lemma log_exp1_Rle_0 : 0 <= log (exp 1).
Proof.
rewrite /log ln_exp /Rdiv ; apply Rle_mult_inv_pos ; [fourier | apply ln_2_pos].
Qed.

Lemma log_mult x y : 0 < x -> 0 < y -> log (x * y) = log x + log y.
Proof. move=> *; rewrite /log ln_mult //; field; exact ln_2_neq0. Qed.

Lemma log_Rinv x : 0 < x -> log (/ x) = - log x.
Proof. move=> ?; rewrite /log ln_Rinv //; field; exact: ln_2_neq0. Qed.

Lemma log_increasing_le a b : 0 < a -> a <= b -> log a <= log b.
Proof.
move=> Ha.
case/Rle_lt_or_eq_dec; last by move=> ->; apply Rle_refl.
move/(ln_increasing _ _ Ha)/ltRW => a_b.
apply Rmult_le_compat_r => //; exact/ltRW/Rinv_0_lt_compat/ln_2_pos.
Qed.

Lemma log_increasing a b : 0 < a -> a < b -> log a < log b.
Proof.
move=> Ha a_b.
rewrite /log.
apply Rmult_lt_compat_r; last exact: ln_increasing.
by apply Rinv_0_lt_compat, ln_2_pos.
Qed.

Lemma log_inv x y : 0 < x -> 0 < y -> log x = log y -> x = y.
Proof.
move=> Hx Hy.
rewrite /log /Rdiv.
move/Rmult_eq_reg_r => H.
apply ln_inv => //; apply H.
by apply Rinv_neq_0_compat, ln_2_neq0.
Qed.

Lemma log_lt_inv x y : 0 < x -> 0 < y -> log x < log y -> x < y.
Proof.
move=> Hx Hy.
rewrite /log /Rdiv.
have H : 0 < / ln 2 by apply Rinv_0_lt_compat, ln_2_pos.
move/(Rmult_lt_reg_r _ _ _ H) => {H}?.
by apply ln_lt_inv.
Qed.

Lemma log_le_inv x y : 0 < x -> 0 < y -> log x <= log y -> x <= y.
Proof.
move=> Hx Hy.
case/Rle_lt_or_eq_dec; first by move/(log_lt_inv Hx Hy)/ltRW.
move/(log_inv Hx Hy) => ->; exact: Rle_refl.
Qed.

Lemma derivable_pt_log : forall x : R, 0 < x -> derivable_pt log x.
move=> x Hx.
rewrite /log.
rewrite /Rdiv.
apply derivable_pt_mult.
  by apply derivable_pt_ln.
apply derivable_pt_const.
Defined.

Lemma derive_pt_log : forall (a : R) (Ha : 0 < a),
  derive_pt log a (derivable_pt_log Ha) = / a * / ln 2.
move=> a Ha.
rewrite /log.
rewrite /Rdiv.
rewrite derive_pt_mult.
rewrite derive_pt_const.
rewrite derive_pt_ln.
rewrite mulR0 addR0.
reflexivity.
Defined.

(** * 2 ^ x *)

Definition exp2 (x : R) := exp (x * ln 2).

Lemma exp2_pos x : 0 < exp2 x.
Proof. rewrite /exp2; exact: exp_pos. Qed.

Lemma exp2_not_0 l : exp2 l <> 0.
Proof. apply not_eq_sym, Rlt_not_eq ; exact (exp2_pos l). Qed.

Lemma exp2_0 : exp2 0 = 1.
Proof. by rewrite /exp2 mul0R exp_0. Qed.

Lemma exp2_plus x y : exp2 (x + y) = exp2 x * exp2 y.
Proof. by rewrite /exp2 mulRDl exp_plus. Qed.

Lemma exp2_pow2 : forall m, exp2 (INR m) = INR (expn 2 m).
Proof.
elim => [|m IH]; first by rewrite /exp2 mul0R exp_0.
rewrite S_INR exp2_plus expnS mult_INR IH /exp2 mul1R exp_ln; by [rewrite mulRC | fourier].
Qed.

Lemma exp2_pow n k : exp2 (INR k * n) = (exp2 n) ^ k.
Proof. by rewrite /exp2 -mulRA exp_pow. Qed.

Lemma exp2_Ropp x : exp2 (- x) = / exp2 x.
Proof. by rewrite /exp2 mulNR exp_Ropp. Qed.

Lemma exp2_le_inv x y : exp2 x <= exp2 y -> x <= y.
Proof.
rewrite /exp2 => /exp_le_inv H.
apply (Rmult_le_reg_l _ _ _ ln_2_pos).
by rewrite mulRC -(mulRC y).
Qed.

Lemma exp2_increasing x y : x < y -> exp2 x < exp2 y.
Proof.
move=> x_y.
rewrite /exp2.
apply exp_increasing, Rmult_lt_compat_r => //.
by apply ln_2_pos.
Qed.

Lemma exp2_le_increasing x y : x <= y -> exp2 x <= exp2 y.
Proof.
case/Rle_lt_or_eq_dec.
move/exp2_increasing => x_y; exact/ltRW.
move=> ->; exact: Rle_refl.
Qed.

Lemma exp2_log x : 0 < x -> exp2 (log x) = x.
Proof.
move=> Hx.
rewrite /exp2 /log /Rdiv -mulRA mulVR ?mulR1 ?exp_ln //.
exact: ln_2_neq0.
Qed.

Lemma log_exp2 x : log (exp2 x) = x.
Proof.
rewrite /log /exp2 ln_exp /Rdiv -mulRA mulRV ?mulR1 //.
exact: ln_2_neq0.
Qed.

Local Open Scope Rb_scope.

Lemma Rle_exp2_log1_L a b : 0 < b -> exp2 a <b= b = (a <b= log b).
Proof.
move=> Hb; move H1 : (_ <b= _ ) => [|] /=.
- move/RleP in H1.
  have {H1}H1 : a <= log b.
    rewrite (_ : a = log (exp2 a)); last by rewrite log_exp2.
    apply log_increasing_le => //; exact: exp2_pos.
  move/RleP in H1; by rewrite H1.
- move H2 : (_ <b= _ ) => [|] //=.
  move/RleP in H2.
  rewrite -(log_exp2 a) in H2.
  apply log_le_inv in H2 => //; last exact: exp2_pos.
  move/RleP in H2.
  by rewrite H2 in H1.
Qed.

Lemma Rle_exp2_log2_R b c : 0 < b -> b <b= exp2 c = (log b <b= c).
Proof.
move=> Hb; move H1 : (_ <b= _ ) => [|] /=.
- move/RleP in H1.
  have {H1}H1 : log b <= c.
    rewrite (_ : c = log (exp2 c)); last by rewrite log_exp2.
    apply log_increasing_le => //; exact: exp2_pos.
  by move/RleP in H1.
- move H2 : (_ <b= _ ) => [|] //=.
  move/RleP in H2.
  rewrite -(log_exp2 c) in H2.
  apply log_le_inv in H2 => //; last exact: exp2_pos.
  move/RleP in H2.
  by rewrite H2 in H1.
Qed.

Lemma Rle2_exp2_log a b c : 0 < b ->
  exp2 a <b= b <b= exp2 c = (a <b= log b <b= c).
Proof.
move=> Hb; move H1 : (_ <b= _ ) => [|] /=.
- rewrite Rle_exp2_log1_L // in H1.
  by rewrite H1 /= Rle_exp2_log2_R.
- move H2 : (_ <b= _ ) => [|] //=.
  rewrite -Rle_exp2_log1_L // in H2.
  by rewrite H2 in H1.
Qed.

Lemma exists_frac_part (P : nat -> Prop) : (exists n, P n) ->
  forall num den, (0 < num)%nat -> (0 < den)%nat ->
  (forall n m, (n <= m)%nat -> P n -> P m) ->
  exists n, P n /\
    frac_part (exp2 (INR n * (log (INR num) / INR den))) = 0.
Proof.
case=> n Pn num den Hden HP.
exists (n * den)%nat.
split.
  apply H with n => //.
  by rewrite -{1}(muln1 n) leq_mul2l HP orbC.
rewrite mult_INR -mulRA (mulRCA (INR den)) mulRV // ?mulR1; last first.
  apply not_0_INR.
  move=> ?; by subst den.
rewrite exp2_pow exp2_log; last exact/lt_0_INR/ltP.
exact/frac_part_pow/frac_part_INR.
Qed.
