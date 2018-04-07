(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrfun ssrnat.
Require Import Reals Fourier.
Require Import Reals_ext Ranalysis_ext Rssr.

(** * log_n x and n ^ x *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.

Section addtional_lemmas_about_ln_exp.

Lemma ln_pos x : 1 < x -> 0 < ln x.
Proof. move=> x0; rewrite -ln_1; exact: ln_increasing. Qed.

Lemma ln2_gt0 : 0 < ln 2. Proof. apply ln_pos; fourier. Qed.
Local Hint Resolve ln2_gt0.

Lemma ln2_neq0 : ln 2 != 0.
Proof. exact/eqP/nesym/Rlt_not_eq. Qed.

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

Lemma leR2e : 2 <= exp 1.
Proof. apply Rlt_le, exp_ineq1; fourier. Qed.

Lemma ltRinve1 : exp (-1) < 1.
Proof. rewrite -[X in _ < X]exp_0. apply exp_increasing. fourier. Qed.

Lemma ltRinve21 : exp (-2) < 1.
Proof. rewrite -[X in _ < X]exp_0. apply exp_increasing. fourier. Qed.

Section exp_lower_bound.

Let exp_dev (n : nat) := fun x => exp x - x ^ n * / INR (n`!).

Let derivable_exp_dev (n : nat) : derivable (exp_dev n).
Proof.
rewrite /exp_dev => x.
apply derivable_pt_minus ; first by apply derivable_pt_exp.
apply derivable_pt_mult ; first by apply derivable_pt_pow.
by apply derivable_pt_const.
Defined.

Let exp_dev_rec n x : derive_pt (exp_dev n.+1) x (derivable_exp_dev n.+1 x) = exp_dev n x.
Proof.
rewrite /exp_dev derive_pt_minus derive_pt_exp; congr (_ - _).
rewrite derive_pt_mult derive_pt_const mulR0 addR0 derive_pt_pow.
rewrite mulRC mulRA mulRC; congr (_ * _).
rewrite factS mult_INR invRM; last 2 first.
  by apply/eqP; rewrite INR_eq0.
  by apply/eqP; rewrite INR_eq0 -lt0n fact_gt0.
by rewrite mulRC mulRA mulRV ?mul1R // INR_eq0.
Qed.

Let exp_dev_gt0 : forall n r, 0 < r -> 0 < exp_dev n r.
Proof.
elim => [r rpos | n IH r rpos].
- rewrite /exp_dev /= mul1R Rinv_1 -exp_0.
  by apply Rgt_lt, Rgt_minus, Rlt_gt, exp_increasing.
- apply: (Rlt_trans _ 1) ; first by fourier.
  rewrite (_ : 1 = exp_dev n.+1 0) ; last first.
    rewrite /exp_dev exp_0 pow_i ?mul0R ?subR0 //; by apply/ltP.
  move: derive_increasing_interv.
  move/(_ 0 r (exp_dev n.+1) (derivable_exp_dev n.+1) rpos).
  have Haux : forall t : R,
     0 < t < r -> 0 < derive_pt (exp_dev n.+1) t (derivable_exp_dev n.+1 t).
    move=>x Hx.
    rewrite exp_dev_rec.
    by apply IH, Hx.
  move/(_ Haux 0 r) => {Haux}.
  apply => //.
  - split; [exact: Rle_refl | exact: ltRW].
  - split; [exact: ltRW | exact: Rle_refl].
Qed.

Lemma exp_strict_lb (n : nat) x : 0 < x -> x ^ n * / INR (n`!) < exp x.
Proof. move=> xpos; by apply Rgt_lt, Rminus_gt, Rlt_gt, exp_dev_gt0. Qed.

Let exp_dev_ge0 n r : 0 <= r -> 0 <= exp_dev n r.
Proof.
move=> Hr.
case/boolP : (r == 0) => [/eqP ->|]; last first.
- move=> Hr2.
  have {Hr Hr2}R_pos : 0 < r by apply/RltP; rewrite lt0R Hr2 /=; exact/RleP.
  exact/ltRW/exp_dev_gt0.
- case: n.
  + rewrite /exp_dev exp_0 mul1R invR1 subRR; exact: Rle_refl.
  - move=> n.
    rewrite -(_ : 1 = exp_dev n.+1 0) //.
    rewrite /exp_dev exp_0 pow_i ?mul0R ?subR0 //; exact/ltP.
Qed.

Lemma exp_lb x (n : nat) : 0 <= x -> x ^ n / INR (n`!) <= exp x.
Proof. move=> xpos; by apply Rge_le, Rminus_ge, Rle_ge, exp_dev_ge0. Qed.

End exp_lower_bound.

End addtional_lemmas_about_ln_exp.
Hint Resolve ln2_gt0.

(** log_n x *)

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

Lemma LogM n x y : 0 < x -> 0 < y -> Log n (x * y) = Log n x + Log n y.
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
exact/eqP/invR_neq0/eqP/gtR_eqF/ln_pos.
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

Lemma derive_pt_Log n : forall (a : R) (Ha : 0 < a),
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

Lemma logexp1E : log (exp 1) = / ln 2.
Proof. by rewrite /log /Log ln_exp div1R. Qed.

Lemma log_exp1_Rle_0 : 0 <= log (exp 1).
Proof. rewrite logexp1E; exact/RleP/RltW/RltP/invR_gt0. Qed.

(** n ^ x *)
Definition Exp (n : R) x := exp (x * ln n).

Lemma pow_Exp x n : 0 < x -> x ^ n = Exp x (INR n).
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

Lemma Exp_gt0 n x : 0 < Exp n x. Proof. rewrite /Exp; exact: exp_pos. Qed.
Lemma Exp_ge0 n x : 0 <= Exp n x. Proof. exact/ltRW/Exp_gt0. Qed.
Hint Resolve Exp_gt0.
Hint Resolve Exp_ge0.

Lemma Exp_0 n : Exp n 0 = 1.
Proof. by rewrite /Exp mul0R exp_0. Qed.

Lemma ExpD n x y : Exp n (x + y) = Exp n x * Exp n y.
Proof. by rewrite /Exp mulRDl exp_plus. Qed.

Lemma Exp_INR n : (0 < n)%nat -> forall m, Exp (INR n) (INR m) = INR (expn n m).
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
apply/RleP; rewrite -(Rle_pmul2l (ln n)); last exact/RltP/ln_pos.
rewrite mulRC -(mulRC y); exact/RleP.
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

Lemma exp2_gt0 x : 0 < exp2 x. Proof. exact: Exp_gt0. Qed.
Lemma exp2_ge0 x : 0 <= exp2 x. Proof. exact: Exp_ge0. Qed.
Hint Resolve exp2_gt0.
Hint Resolve exp2_ge0.

Lemma exp2_neq0 l : exp2 l <> 0. Proof. exact/gtR_eqF. Qed.
Hint Resolve exp2_neq0.

Lemma exp2_0 : exp2 0 = 1.
Proof. by rewrite /exp2 -/(Exp 2 0) Exp_0. Qed.

Lemma exp2_INR : forall m, exp2 (INR m) = INR (expn 2 m).
Proof. move=> m; by rewrite -Exp_INR. Qed.

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
    exact: Log_increasing_le.
  move/RleP in H1; by rewrite H1.
- move H2 : (_ <b= _ ) => [|] //=.
  move/RleP in H2.
  rewrite -(@ExpK 2 a _) // in H2.
  apply Log_le_inv in H2 => //.
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
  apply Log_le_inv in H2 => //.
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
