(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrfun ssrnat.
Require Import Reals Fourier.
Require Import Reals_ext Ranalysis_ext Rssr.

(** * log_2 x / 2 ^ x *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.

Lemma ln_pos x : 1 < x -> 0 < ln x.
Proof. move=> x0; rewrite -ln_1; apply ln_increasing => //; exact/Rlt_0_1. Qed.

Lemma ln_2_pos : 0 < ln 2.
Proof. apply ln_pos; fourier. Qed.

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

Definition Log (n : R) x := ln x / ln n.

Lemma ltR0Log n x : 1 < n -> 1 < x -> 0 < Log n x.
Proof. move=> ? ?; apply mulR_gt0; [exact/ln_pos | exact/invR_gt0/ln_pos]. Qed.

Lemma Log_1 (n : R) : Log n 1 = 0.
Proof. by rewrite /Log ln_1 div0R. Qed.

Lemma Log_n (n : R) : 1 < n -> Log n n = 1.
Proof. move=> n1; rewrite /Log /Rdiv mulRV //; exact/eqP/gtR_eqF/ln_pos. Qed.

Lemma LogV n x : 0 < x -> Log n (/ x) = - Log n x.
Proof.
by move=> x0; rewrite /Log ln_Rinv // -mulNR.
Qed.

Lemma Log_mult n x y : 0 < x -> 0 < y -> Log n (x * y) = Log n x + Log n y.
Proof. move=> *; by rewrite /Log -mulRDl ln_mult. Qed.

Lemma Log_increasing_le n x y : 1 < n -> 0 < x -> x <= y -> Log n x <= Log n y.
Proof.
move=> n1 x0 xy.
apply Rmult_le_compat_r; [exact/RleP/RltW/RltP/invR_gt0/ln_pos|].
by apply ln_increasing_le.
Qed.

Lemma Log_increasing n a b : 1 < n -> 0 < a -> a < b -> Log n a < Log n b.
Proof.
move=> n1 Ha a_b.
rewrite /Log.
apply Rmult_lt_compat_r; last exact: ln_increasing.
by apply/invR_gt0/ln_pos.
Qed.

Lemma Log_inv n x y : 1 < n -> 0 < x -> 0 < y -> Log n x = Log n y -> x = y.
Proof.
move=> n1 Hx Hy.
rewrite /Log /Rdiv.
move/Rmult_eq_reg_r => H.
apply ln_inv => //; apply H.
exact/Rinv_neq_0_compat/gtR_eqF/ln_pos.
Qed.

Lemma Log_lt_inv n x y : 1 < n -> 0 < x -> 0 < y -> Log n x < Log n y -> x < y.
Proof.
move=> n1 Hx Hy.
rewrite /Log /Rdiv.
have H : 0 < / ln n by apply/invR_gt0/ln_pos.
move/(Rmult_lt_reg_r _ _ _ H) => {H}?.
by apply ln_lt_inv.
Qed.

Lemma Log_le_inv n x y : 1 < n -> 0 < x -> 0 < y -> Log n x <= Log n y -> x <= y.
Proof.
move=> n1 Hx Hy.
case/Rle_lt_or_eq_dec; first by move/(Log_lt_inv n1 Hx Hy)/ltRW.
move/(Log_inv n1 Hx Hy) => ->; exact: Rle_refl.
Qed.

Lemma derivable_pt_Log n : forall x : R, 0 < x -> derivable_pt (Log n) x.
move=> x Hx.
rewrite /Log /Rdiv.
apply derivable_pt_mult.
  exact: derivable_pt_ln.
apply derivable_pt_const.
Defined.

Lemma derive_pt_log n : forall (a : R) (Ha : 0 < a),
  derive_pt (Log n) a (derivable_pt_Log n Ha) = / a * / ln n.
move=> a Ha.
rewrite /Log.
rewrite /Rdiv.
rewrite derive_pt_mult.
rewrite derive_pt_const.
rewrite derive_pt_ln.
rewrite mulR0 addR0.
reflexivity.
Defined.

(** Log base 2 *)

(* NB: log is 0 for input < 0 *)
Definition log x := Log 2 x.

Lemma Rlt_1_2 : 1 < 2. Proof. by fourier. Qed.
Hint Resolve Rlt_1_2.

Lemma logexp1E : log (exp 1) = / ln 2.
Proof. by rewrite /log /Log ln_exp div1R. Qed.

Lemma log_exp1_Rle_0 : 0 <= log (exp 1).
Proof. rewrite logexp1E; exact/RleP/RltW/RltP/invR_gt0/ln_2_pos. Qed.

Definition Exp (n : R) x := exp (x * ln n).

Lemma powE x n : 0 < x -> x ^ n = Exp x (INR n).
Proof. by move=> x0; rewrite /Exp exp_pow exp_ln. Qed.

Lemma LogK n x : 1 < n -> 0 < x -> Exp n (Log n x) = x.
Proof.
move=> n1 x0.
rewrite /Log /Exp -mulRA mulVR ?mulR1; last first.
  rewrite -ln_1.
  apply/eqP => /ln_inv H.
  have : 0 < n by fourier.
  move/H => /(_ Rlt_0_1) ?; fourier.
by rewrite exp_ln.
Qed.

Lemma ExpK n x : 1 < n -> Log n (Exp n x) = x.
Proof.
move=> n1.
rewrite /Log /Exp ln_exp /Rdiv -mulRA mulRV ?mulR1 //.
rewrite -ln_1; apply/eqP => /ln_inv H.
have : 0 < n by fourier.
move/H => /(_ Rlt_0_1) ?; fourier.
Qed.

Lemma Exp_pos n x : 0 < Exp n x.
Proof. rewrite /Exp; exact: exp_pos. Qed.

Lemma Exp_0 n : Exp n 0 = 1.
Proof. by rewrite /Exp mul0R exp_0. Qed.

Lemma ExpD n x y : Exp n (x + y) = Exp n x * Exp n y.
Proof. by rewrite /Exp mulRDl exp_plus. Qed.

(* TODO: rename *)
Lemma Exp_pow n : (0 < n)%nat -> forall m, Exp (INR n) (INR m) = INR (expn n m).
Proof.
move=> n0.
elim=> [|m IH]; first by rewrite /Exp mul0R exp_0.
rewrite S_INR ExpD expnS mult_INR IH /Exp mul1R exp_ln; [ by rewrite mulRC | ].
by apply/RltP; rewrite ltR0n.
Qed.

Lemma Exp_increasing n x y : 1 < n -> x < y -> Exp n x < Exp n y.
Proof.
move=> n1 x_y.
rewrite /Exp.
apply exp_increasing, Rmult_lt_compat_r => //.
exact/ln_pos.
Qed.

Lemma Exp_le_inv n x y : 1 < n -> Exp n x <= Exp n y -> x <= y.
Proof.
rewrite /Exp => n1 /exp_le_inv H.
apply (Rmult_le_reg_l _ _ _ (ln_pos n1)).
by rewrite mulRC -(mulRC y).
Qed.

Lemma Exp_le_increasing n x y : 1 < n -> x <= y -> Exp n x <= Exp n y.
Proof.
move=> n1; rewrite /Exp.
case/Rle_lt_or_eq_dec.
move/Exp_increasing => x_y; exact/ltRW/x_y.
move=> ->; exact: Rle_refl.
Qed.

Lemma Exp_Ropp n x : Exp n (- x) = / Exp n x.
Proof. by rewrite /Exp mulNR exp_Ropp. Qed.

(** 2 ^ x *)

Definition exp2 (x : R) := Exp 2 x.

Lemma exp2_pos x : 0 < exp2 x.
Proof. rewrite /exp2 -/(Exp 2 x); exact: Exp_pos. Qed.

Lemma exp2_not_0 l : exp2 l <> 0.
Proof. apply not_eq_sym, Rlt_not_eq ; exact (exp2_pos l). Qed.

Lemma exp2_0 : exp2 0 = 1.
Proof. by rewrite /exp2 -/(Exp 2 0) Exp_0. Qed.

Lemma exp2_pow2 : forall m, exp2 (INR m) = INR (expn 2 m).
Proof.
move=> m.
by rewrite /exp2 -/(Exp 2 (INR m)) (_ : 2 = INR 2) // Exp_pow.
Qed.

Lemma exp2_pow n k : exp2 (INR k * n) = (exp2 n) ^ k.
Proof. by rewrite /exp2 /Exp -mulRA exp_pow. Qed.

Lemma exp2_Ropp x : exp2 (- x) = / exp2 x.
Proof. by rewrite /exp2 Exp_Ropp. Qed.

Lemma logK x : 0 < x -> exp2 (log x) = x.
Proof. move=> Hx; by rewrite /exp2 -/(Exp 2 (log x)) /log -/(Log 2 _) LogK. Qed.

Lemma exp2K x : log (exp2 x) = x.
Proof. by rewrite /exp2 -/(Exp 2 x) /log -/(Log 2 _) ExpK. Qed.

Lemma Rle_exp2_log1_L a b : 0 < b -> exp2 a <b= b = (a <b= log b).
Proof.
move=> Hb; move H1 : (_ <b= _ ) => [|] /=.
- move/RleP in H1.
  have {H1}H1 : a <= log b.
    rewrite (_ : a = log (exp2 a)); last by rewrite exp2K.
    apply Log_increasing_le => //; exact: exp2_pos.
  move/RleP in H1; by rewrite H1.
- move H2 : (_ <b= _ ) => [|] //=.
  move/RleP in H2.
  rewrite -(@ExpK 2 a _) // in H2.
  apply Log_le_inv in H2 => //; last exact: exp2_pos.
  move/RleP in H2.
  by rewrite H2 in H1.
Qed.

Lemma Rle_exp2_log2_R b c : 0 < b -> b <b= exp2 c = (log b <b= c).
Proof.
move=> Hb; move H1 : (_ <b= _ ) => [|] /=.
- move/RleP in H1.
  have {H1}H1 : log b <= c.
    rewrite (_ : c = log (exp2 c)); last by rewrite exp2K.
    apply Log_increasing_le => //; exact: exp2_pos.
  by move/RleP in H1.
- move H2 : (_ <b= _ ) => [|] //=.
  move/RleP in H2.
  rewrite -(exp2K c) in H2.
  apply Log_le_inv in H2 => //; last exact: exp2_pos.
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
  by rewrite INR_eq0 -lt0n.
rewrite exp2_pow logK; last exact/lt_0_INR/ltP.
exact/frac_part_pow/frac_part_INR.
Qed.
