(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrfun ssrnat.
Require Import Reals Lra.
Require Import ssrR Reals_ext.

(******************************************************************************)
(*                          log_n x and n ^ x                                 *)
(*                                                                            *)
(* Definitions and lemmas about the logarithm and the exponential in base n.  *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   Log == log_n x                                                           *)
(*   Exp == n ^ x                                                             *)
(*   log == Log in base 2                                                     *)
(*   exp2 == 2 ^ x                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.

Section addtional_lemmas_about_ln_exp.

Lemma ln_pos x : 1 < x -> 0 < ln x.
Proof. move=> x0; rewrite -ln_1; exact: ln_increasing. Qed.

Lemma ln2_gt0 : 0 < ln 2. Proof. apply ln_pos; lra. Qed.
Local Hint Resolve ln2_gt0 : core.

Lemma ln2_neq0 : ln 2 != 0. Proof. exact/eqP/gtR_eqF. Qed.

Lemma ln_expR (a : R) (n : nat) : 0 < a -> ln (a ^ n) = n%:R * ln a.
Proof.
move=> a0; elim: n => [|n IH]; first by rewrite expR0 ln_1 mul0R.
rewrite expRS ln_mult //; last exact: expR_gt0.
by rewrite IH S_INR mulRDl mul1R addRC.
Qed.

Lemma ln_increasing_le a b : 0 < a -> a <= b -> ln a <= ln b.
Proof.
move=> Ha.
case/Rle_lt_or_eq_dec; last by move=> ->; exact/leRR.
by move/(ln_increasing _ _ Ha)/ltRW.
Qed.

Lemma exp_le_inv x y : exp x <= exp y -> x <= y.
Proof.
case/Rle_lt_or_eq_dec; [move/exp_lt_inv => ?; exact/ltRW |
  move/exp_inv => ->; exact/leRR].
Qed.

Lemma exp_pow n : forall k, exp (k%:R * n) = (exp n) ^ k.
Proof.
elim => [|k IH]; first by rewrite mul0R exp_0.
by rewrite S_INR mulRDl mul1R exp_plus IH mulRC.
Qed.

Lemma leR2e : 2 <= exp 1. Proof. apply Rlt_le, exp_ineq1; lra. Qed.

Lemma ltRinve1 : exp (-1) < 1.
Proof. rewrite -[X in _ < X]exp_0. apply exp_increasing. lra. Qed.

Lemma ltRinve21 : exp (-2) < 1.
Proof. rewrite -[X in _ < X]exp_0. apply exp_increasing. lra. Qed.

Section exp_lower_bound.

Let exp_dev (n : nat) := fun x => exp x - x ^ n * / (n`!)%:R.

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
rewrite factS natRM invRM; last 2 first.
  exact/INR_eq0.
  apply/eqP; by rewrite INR_eq0' -lt0n fact_gt0.
by rewrite mulRC mulRA mulRV ?mul1R // INR_eq0'.
Qed.

Let exp_dev_gt0 : forall n r, 0 < r -> 0 < exp_dev n r.
Proof.
elim => [r rpos | n IH r rpos].
- rewrite /exp_dev /= mul1R Rinv_1 -exp_0.
  by apply subR_gt0, exp_increasing.
- apply: (@ltR_trans 1); first lra.
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
  - split; [exact/leRR | exact: ltRW].
  - split; [exact: ltRW | exact/leRR].
Qed.

Lemma exp_strict_lb (n : nat) x : 0 < x -> x ^ n * / (n`!)%:R < exp x.
Proof. move=> xpos; by apply Rgt_lt, Rminus_gt, Rlt_gt, exp_dev_gt0. Qed.

Let exp_dev_ge0 n r : 0 <= r -> 0 <= exp_dev n r.
Proof.
move=> Hr.
case/boolP : (r == 0) => [/eqP ->|]; last first.
- move=> Hr2.
  have {Hr Hr2}R_pos : 0 < r by apply/ltRP; rewrite lt0R Hr2 /=; exact/leRP.
  exact/ltRW/exp_dev_gt0.
- case: n.
  + rewrite /exp_dev exp_0 mul1R invR1 subRR; exact/leRR.
  - move=> n.
    rewrite -(_ : 1 = exp_dev n.+1 0) //.
    rewrite /exp_dev exp_0 pow_i ?mul0R ?subR0 //; exact/ltP.
Qed.

Lemma exp_lb x (n : nat) : 0 <= x -> x ^ n / (n`!)%:R <= exp x.
Proof. move=> xpos; by apply Rge_le, Rminus_ge, Rle_ge, exp_dev_ge0. Qed.

End exp_lower_bound.

End addtional_lemmas_about_ln_exp.
Hint Resolve ln2_gt0 : core.

Definition Log (n : R) x := ln x / ln n.

Lemma Log_expR (a b : R) (n : nat) : 0 < a -> Log b (a ^ n) = n%:R * Log b a.
Proof. by move=> a0; rewrite /Log ln_expR // mulRA. Qed.

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

Lemma LogDiv n x y : 0 < x -> 0 < y -> Log n (x / y) = Log n x - Log n y.
Proof. move=> *; rewrite LogM //; [by rewrite LogV | exact: invR_gt0]. Qed.

Lemma Log_increasing_le n x y : 1 < n -> 0 < x -> x <= y -> Log n x <= Log n y.
Proof.
move=> n1 x0 xy.
apply leR_wpmul2r; [exact/leRP/ltRW'/ltRP/invR_gt0/ln_pos|].
exact: ln_increasing_le.
Qed.

Lemma Log_increasing n a b : 1 < n -> 0 < a -> a < b -> Log n a < Log n b.
Proof.
move=> n1 Ha a_b.
rewrite /Log.
apply ltR_pmul2r; last exact: ln_increasing.
exact/invR_gt0/ln_pos.
Qed.

Lemma Log_inv n x y : 1 < n -> 0 < x -> 0 < y -> Log n x = Log n y -> x = y.
Proof.
move=> n1 Hx Hy.
rewrite /Log /Rdiv eqR_mul2r; last exact/invR_neq0/gtR_eqF/ln_pos.
apply ln_inv => //; exact: H.
Qed.

Lemma Log_lt_inv n x y : 1 < n -> 0 < x -> 0 < y -> Log n x < Log n y -> x < y.
Proof.
move=> n1 Hx Hy.
rewrite /Log /Rdiv.
have H : 0 < / ln n by exact/invR_gt0/ln_pos.
move/(ltR_pmul2r H); exact: ln_lt_inv.
Qed.

Lemma Log_le_inv n x y : 1 < n -> 0 < x -> 0 < y -> Log n x <= Log n y -> x <= y.
Proof.
move=> n1 Hx Hy.
case/Rle_lt_or_eq_dec; first by move/(Log_lt_inv n1 Hx Hy)/ltRW.
move/(Log_inv n1 Hx Hy) => ->; exact/leRR.
Qed.

(* NB: log is 0 for input < 0 *)
Definition log x := Log 2 x.

Lemma log1 : log 1 = 0. Proof. by rewrite /log Log_1. Qed.
Lemma log4 : log 4 = 2.
Proof.
rewrite (_ : 4 = 2 ^ 2); last lra.
rewrite /log Log_expR // /Log divRR ?ln2_neq0 // mulR1 !S_INR add0R; field.
Qed.
Lemma log8 : log 8 = 3.
Proof.
rewrite (_ : 8 = 2 ^ 3); last lra.
rewrite /log Log_expR // /Log divRR ?ln2_neq0 // mulR1 !S_INR add0R; field.
Qed.
Lemma log16 : log 16 = 4.
Proof.
rewrite (_ : 16 = 2 ^ 4); last lra.
rewrite /log Log_expR // /Log divRR ?ln2_neq0 // mulR1 !S_INR add0R; field.
Qed.
Lemma log32 : log 32 = 5.
Proof.
rewrite (_ : 32 = 2 ^ 5); last lra.
rewrite /log Log_expR // /Log divRR ?ln2_neq0 // mulR1 !S_INR add0R; field.
Qed.

Lemma logV x : 0 < x -> log (/ x) = - log x.
Proof. by move/(@LogV 2). Qed.

Lemma logM x y : 0 < x -> 0 < y -> log (x * y) = log x + log y.
Proof. move=> x0 y0; exact: (@LogM 2 _ _ x0 y0). Qed.

Lemma logDiv x y : 0 < x -> 0 < y -> log (x / y) = log x - log y.
Proof. move=> x0 y0; exact: (@LogDiv 2 _ _ x0 y0). Qed.

Lemma logexp1E : log (exp 1) = / ln 2.
Proof. by rewrite /log /Log ln_exp div1R. Qed.

Lemma log_exp1_Rle_0 : 0 <= log (exp 1).
Proof. rewrite logexp1E; exact/leRP/ltRW'/ltRP/invR_gt0. Qed.

Definition Exp (n : R) x := exp (x * ln n).

Lemma pow_Exp x n : 0 < x -> x ^ n = Exp x n%:R.
Proof. by move=> x0; rewrite /Exp exp_pow exp_ln. Qed.

Lemma LogK n x : 1 < n -> 0 < x -> Exp n (Log n x) = x.
Proof.
move=> n1 x0.
rewrite /Log /Exp -mulRA mulVR ?mulR1 ?exp_ln //.
rewrite -ln_1.
apply/eqP => /ln_inv H.
have : 0 < n by lra.
move/H => /(_ Rlt_0_1) ?; lra.
Qed.

Lemma ExpK n x : 1 < n -> Log n (Exp n x) = x.
Proof.
move=> n1.
rewrite /Log /Exp ln_exp /Rdiv -mulRA mulRV ?mulR1 //.
rewrite -ln_1; apply/eqP => /ln_inv H.
have : 0 < n by lra.
move/H => /(_ Rlt_0_1) ?; lra.
Qed.

Lemma Exp_gt0 n x : 0 < Exp n x. Proof. rewrite /Exp; exact: exp_pos. Qed.
Lemma Exp_ge0 n x : 0 <= Exp n x. Proof. exact/ltRW/Exp_gt0. Qed.
Hint Resolve Exp_gt0 : core.
Hint Resolve Exp_ge0 : core.

Lemma Exp_0 n : Exp n 0 = 1.
Proof. by rewrite /Exp mul0R exp_0. Qed.

Lemma ExpD n x y : Exp n (x + y) = Exp n x * Exp n y.
Proof. by rewrite /Exp mulRDl exp_plus. Qed.

Lemma natRExp n : (0 < n)%nat -> forall m, Exp n%:R m%:R = (expn n m)%:R.
Proof.
move=> n0.
elim=> [|m IH]; first by rewrite /Exp mul0R exp_0.
rewrite S_INR ExpD expnS natRM IH /Exp mul1R exp_ln;
  [by rewrite mulRC | exact/ltR0n].
Qed.

Lemma Exp_increasing n x y : 1 < n -> x < y -> Exp n x < Exp n y.
Proof. move=> ? ?; apply/exp_increasing/ltR_pmul2r => //; exact/ln_pos. Qed.

Lemma Exp_le_inv n x y : 1 < n -> Exp n x <= Exp n y -> x <= y.
Proof.
rewrite /Exp => n1 /exp_le_inv H.
apply/leRP; rewrite -(leR_pmul2l' (ln n)); last exact/ltRP/ln_pos.
rewrite mulRC -(mulRC y); exact/leRP.
Qed.

Lemma Exp_le_increasing n x y : 1 < n -> x <= y -> Exp n x <= Exp n y.
Proof.
move=> n1; rewrite /Exp; case/Rle_lt_or_eq_dec.
move/Exp_increasing => x_y; exact/ltRW/x_y.
move=> ->; exact/leRR.
Qed.

Lemma Exp_Ropp n x : Exp n (- x) = / Exp n x.
Proof. by rewrite /Exp mulNR exp_Ropp. Qed.

Definition exp2 (x : R) := Exp 2 x.

Lemma exp2_gt0 x : 0 < exp2 x. Proof. exact: Exp_gt0. Qed.
Lemma exp2_ge0 x : 0 <= exp2 x. Proof. exact: Exp_ge0. Qed.
Hint Resolve exp2_gt0 : core.
Hint Resolve exp2_ge0 : core.

Lemma exp2_neq0 l : exp2 l <> 0. Proof. exact/gtR_eqF. Qed.
Hint Resolve exp2_neq0 : core.

Lemma exp2_0 : exp2 0 = 1.
Proof. by rewrite /exp2 -/(Exp 2 0) Exp_0. Qed.

Lemma natRexp2 m : exp2 m%:R = (expn 2 m)%:R.
Proof. by rewrite -natRExp. Qed.

Lemma exp2_pow n k : exp2 (k%:R * n) = (exp2 n) ^ k.
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
- move/leRP in H1.
  have {}H1 : a <= log b.
    rewrite (_ : a = log (exp2 a)); last by rewrite exp2K.
    exact: Log_increasing_le.
  move/leRP in H1; by rewrite H1.
- move H2 : (_ <b= _ ) => [|] //=.
  move/leRP in H2.
  rewrite -(@ExpK 2 a _) // in H2.
  apply Log_le_inv in H2 => //.
  move/leRP in H2.
  by rewrite H2 in H1.
Qed.

Lemma Rle_exp2_log2_R b c : 0 < b -> b <b= exp2 c = (log b <b= c).
Proof.
move=> Hb; move H1 : (_ <b= _ ) => [|] /=.
- move/leRP in H1.
  have {}H1 : log b <= c.
    rewrite (_ : c = log (exp2 c)); last by rewrite exp2K.
    apply Log_increasing_le => //; exact: exp2_pos.
  by move/leRP in H1.
- move H2 : (_ <b= _ ) => [|] //=.
  move/leRP in H2.
  rewrite -(exp2K c) in H2.
  apply Log_le_inv in H2 => //.
  move/leRP in H2.
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
    frac_part (exp2 (n%:R * (log num%:R / den%:R))) = 0.
Proof.
case=> n Pn num den Hden HP.
exists (n * den)%nat.
split.
  apply H with n => //.
  by rewrite -{1}(muln1 n) leq_mul2l HP orbC.
rewrite natRM -mulRA (mulRCA den%:R) mulRV // ?mulR1; last first.
  by rewrite INR_eq0' -lt0n.
rewrite exp2_pow logK; [exact/frac_part_pow/frac_part_INR | exact/ltR0n].
Qed.
