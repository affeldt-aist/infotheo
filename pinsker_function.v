(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div fintype tuple finfun bigop.
Require Import Reals Fourier.
Require Import Reals_ext ssr_ext Ranalysis_ext log2 Rssr Rbigop proba.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Function used in the proof of Pinsker's inequality *)

Definition pinsker_fun p c := fun q =>
  p * log (div_fct (fun _ => p) id q) +
  (1 - p) * log (div_fct (fun _ => 1 - p) (fun q => 1 - q) q) -
  4 * c * comp (fun x => x ^2) (fun q => p - q) q.

Lemma derive_pinsker_fun (p : R) c : 0 < p < 1 ->
  pderivable (pinsker_fun p c) (fun q => 0 < q < 1).
Proof.
move=> [H0p Hp1] q /= [Hq1 Hq2].
rewrite /pinsker_fun.
apply derivable_pt_minus.
  apply derivable_pt_plus.
    apply derivable_pt_mult.
      apply derivable_pt_const.
    apply derivable_pt_comp.
      apply derivable_pt_mult.
        apply derivable_pt_const.
      apply derivable_pt_inv.
      by apply nesym, Rlt_not_eq.
      apply derivable_pt_id.
    apply derivable_pt_Log.
    by apply Rlt_mult_inv_pos.
  apply derivable_pt_mult.
    apply derivable_pt_const.
  apply derivable_pt_comp.
    apply derivable_pt_div.
      apply derivable_pt_const.
      apply derivable_pt_Rminus.
      move=> abs; fourier.
  apply derivable_pt_Log.
  apply Rlt_mult_inv_pos => //; fourier.
apply derivable_pt_mult.
  apply derivable_pt_const.
apply derivable_pt_comp.
  apply derivable_pt_Rminus.
apply derivable_pt_pow.
Defined.

Definition pinsker_fun' p c := fun q =>
  (q - p) * (inv_fct (fun q => (q * (1 - q) * ln 2)) q - 8 * c).

Lemma derive_pt_pinsker_fun p (Hp : 0 < p < 1) c q (Hq : 0 < q < 1)
  (pr : derivable_pt (pinsker_fun p c) q) :
  derive_pt (pinsker_fun p c) q pr = pinsker_fun' p c q.
Proof.
transitivity (derive_pt (pinsker_fun p c) q (@derive_pinsker_fun _ c Hp q Hq)).
  by apply proof_derive_irrelevance.
rewrite /pinsker_fun /derive_pinsker_fun.
case: Hp => Hp1 Hp2.
case: Hq => Hq1 Hq2.
rewrite !(derive_pt_minus,derive_pt_plus,derive_pt_comp,derive_pt_ln,derive_pt_const,derive_pt_mult,derive_pt_inv,derive_pt_id,derive_pt_div,derive_pt_pow).
rewrite !(mul0R,mulR0,addR0,add0R,Rminus_0_l) /= (_ : INR 2 = 2) //.
rewrite /pinsker_fun' /div_fct.
rewrite [X in _ = X]Rmult_minus_distr_l.
f_equal; last by field.
rewrite (_ : id q = q) //.
rewrite Rinv_Rdiv; last 2 first.
  move=> ?; fourier.
  move=> ?; fourier.
rewrite Rinv_Rdiv; last 2 first.
  move=> ?; fourier.
  move=> ?; fourier.
have -> : p * (q / p * / ln 2 * (p * (-1 / q²)) ) = - (p / q) * / ln 2.
  rewrite !mulRA /Rsqr.
  field.
  split; first by apply ln_2_neq0.
  split => ?; fourier.
have -> : (1 - p) * ((1 - q) / (1 - p) * / ln 2 * (- (-1 * (1 - p)) / (1 - q)²)) =
  (((1 - p) / (1 - q))) * / ln 2.
  rewrite /Rsqr.
  field.
  split; first by apply ln_2_neq0.
  split => ?; fourier.
rewrite /inv_fct.
field.
  split; first by apply ln_2_neq0.
  split => ?; fourier.
Qed.

Definition pinsker_function_spec c q := - log (1 - q) - 4 * c * q ^ 2.

Definition pinsker_function_spec' c q0 :=
   / ((1 - q0) * ln 2) - 8 * c * q0.

Lemma pderivable_pinsker_function_spec c :
  pderivable (pinsker_function_spec c) (fun q => 0 <= q < 1).
Proof.
move=> q0 Hq0.
rewrite /pinsker_function_spec.
apply derivable_pt_minus.
  apply derivable_pt_opp.
  apply derivable_pt_comp.
    apply derivable_pt_Rminus.
  apply derivable_pt_Log.
  rewrite /= in Hq0.
  decompose [and] Hq0; clear Hq0; fourier.
apply derivable_pt_mult.
  apply derivable_pt_const.
apply derivable_pt_pow.
Defined.

Lemma derive_pt_pinsker_function_spec c q0 (Hq0 : 0 <= q0 < 1)
  (pr : derivable_pt (pinsker_function_spec c) q0) :
  derive_pt (pinsker_function_spec c) q0 pr = pinsker_function_spec' c q0.
Proof.
rewrite (proof_derive_irrelevance _ (pderivable_pinsker_function_spec c Hq0)).
rewrite /pinsker_function_spec.
rewrite derive_pt_minus.
rewrite derive_pt_opp.
rewrite derive_pt_comp.
rewrite derive_pt_log.
rewrite derive_pt_mult.
rewrite derive_pt_pow.
rewrite derive_pt_const.
rewrite mul0R add0R /= /pinsker_function_spec' (_ : INR 2 = 2) //.
field.
split; first by apply ln_2_neq0.
case: Hq0 => ? ? ?; fourier.
Defined.

Lemma pinsker_fun_increasing_on_0_to_1 (c : R) (Hc : c <= / (2 * ln 2)) : forall x y,
  0 <= x < 1 -> 0 <= y < 1 -> x <= y -> pinsker_function_spec c x <= pinsker_function_spec c y.
Proof.
apply derive_increasing_interv_right with (pderivable_pinsker_function_spec c).
fourier.
move=> t Ht.
rewrite derive_pt_pinsker_function_spec // /pinsker_function_spec'.
apply Rle_trans with (/ ((1 - t) * ln 2) - 8 * t / (2 * ln 2)); last first.
  apply Rplus_le_compat_l.
  apply Ropp_le_contravar. (* NB:
                             Ropp_ge_le_contravar  forall r1 r2 : R, r1 >= r2 -> - r1 <= - r2
                             Ropp_le_contravar  forall r1 r2 : R, r2 <= r1 -> - r1 <= - r2
                             almost identical *)
  rewrite -mulRA /Rdiv -[X in _ <= X]mulRA.
  apply Rmult_le_compat_l; first by fourier.
  rewrite mulRC.
  apply Rmult_le_compat_l => //.
  by case: Ht.
apply Rle_trans with ((2 - 8 * t * (1 - t)) / (2 * (1 - t) * ln 2)); last first.
  apply Req_le.
  field.
  split; first by apply ln_2_neq0.
  case: Ht => ? ? ?; fourier.
apply Rle_mult_inv_pos; last first.
  rewrite mulRC mulRA.
  apply mulR_gt0.
    apply mulR_gt0; by [apply ln_2_pos | fourier].
  case: Ht => ? ?; fourier.
have H2 : -2 <= - 8 * t * (1 - t).
  rewrite !mulNR -mulRA.
  apply Ropp_le_contravar.
  rewrite [X in _ <= X](_ : 2 = 8 * 1 / 4); last by field.
  rewrite /Rdiv mulR1.
  apply Rmult_le_compat_l; first by fourier.
  rewrite -[X in _ <= X]mul1R; by apply x_x2_max.
apply Rle_trans with (2 - 2); first by fourier.
apply Rplus_le_compat; first by apply Rle_refl.
by rewrite -mulRA -mulNR mulRA.
Qed.

Lemma pinsker_function_spec_pos : forall c q,
  0 <= c <= / (2 * ln 2) ->
  0 <= q < 1 ->
  0 <= pinsker_function_spec c q.
Proof.
move=> c q0 Hc Hq0.
rewrite (_ : 0 = pinsker_function_spec c 0); last first.
rewrite /pinsker_function_spec /= subR0 /log Log_1; field.
apply pinsker_fun_increasing_on_0_to_1 => //.
by case: Hc.
split; fourier.
by case: Hq0.
Qed.

Section pinsker_function_analysis.

Variables p q : R.
Hypothesis Hp : 0 <= p <= 1.
Hypothesis Hq : 0 <= q <= 1.

Lemma pinsker_fun_p c : pinsker_fun p c p = 0.
Proof.
rewrite /pinsker_fun /= /div_fct /comp (_ : p - p = 0); last by rewrite Rminus_diag_eq.
rewrite mul0R mulR0 subR0.
case: Hp => Hp1 Hp2.
case/Rle_lt_or_eq_dec : Hp1 => Hp1; last first.
  subst p.
  rewrite mul0R !subR0 add0R mul1R.
  by rewrite /Rdiv Rinv_1 mulR1 /log Log_1.
case/Rle_lt_or_eq_dec : Hp2 => Hp2; last first.
  subst p.
  rewrite /Rdiv Rinv_1 mulR1 /log Log_1 mulR0.
  rewrite !Rminus_diag_eq // mul0R; field.
rewrite divRR; last by rewrite subR_eq0; apply/eqP/gtR_eqF.
rewrite /log Log_1 divRR; last exact/eqP/gtR_eqF.
rewrite /log Log_1; by field.
Qed.

Lemma pinsker_fun_pderivable1 c (Hp' : 0 < p < 1) :
  pderivable (fun x => - pinsker_fun p c x) (fun q => 0 < q <= p).
move=> x [Hx1 Hx2].
apply derivable_pt_opp.
apply: (@derive_pinsker_fun p c Hp').
case: Hp' => Hp'1 Hp'2.
split => //.
fourier.
Defined.

Lemma pinsker_fun_decreasing_on_0_to_p (c : R) (Hc : c <= / (2 * ln 2)) (Hp' : 0 < p < 1) :
  forall x y, 0 < x <= p -> 0 < y <= p -> x <= y -> pinsker_fun p c y <= pinsker_fun p c x.
Proof.
move=> x y Hx Hy xy.
apply Ropp_le_cancel.
move: x y Hx Hy xy.
apply derive_increasing_interv_left with (pinsker_fun_pderivable1 c Hp').
by case: Hp'.
move=> t [Ht1 Ht2].
rewrite /pinsker_fun_pderivable1.
rewrite derive_pt_opp.
destruct Hp' as [Hp'1 Hp'2].
rewrite derive_pt_pinsker_fun //; last by split; fourier.
rewrite /pinsker_fun' /div_fct.
have Hlocal : 0 <= / ln 2 by apply Rlt_le, Rinv_0_lt_compat, ln_2_pos.
have X : 0 <= (/ (t * (1 - t) * ln 2) - 8 * c).
  have : forall a b, b <= a -> 0 <= a - b. move=> *; fourier. apply.
  apply Rle_trans with (4 / ln 2).
    apply Rle_trans with (8 * / (2 * ln 2)).
    apply Rmult_le_compat_l => //; fourier.
    rewrite Rinv_mult_distr; last 2 first.
      move=> ?; fourier.
      by apply ln_2_neq0.
    rewrite mulRA.
    apply Rmult_le_compat_r => //; by fourier.
  rewrite Rinv_mult_distr; last 2 first.
    apply nesym, Rlt_not_eq, mulR_gt0; fourier.
    by apply ln_2_neq0.
  apply Rmult_le_compat_r => //.
  apply Rle_inv_conv; first by fourier.
  apply Rinv_0_lt_compat, mulR_gt0; fourier.
  rewrite invRK.
    rewrite -[X in _ <= X]mul1R; by apply x_x2_max.
  apply nesym, Rlt_not_eq, mulR_gt0; fourier.
rewrite /inv_fct -mulNR; apply mulR_ge0 => //; fourier.
Qed.

Lemma pinsker_fun_pderivable2 c (Hp' : 0 < p < 1) :
  pderivable (fun x : R => pinsker_fun p c x) (fun q : R => p <= q < 1).
move=> x [Hx1 Hx2].
apply: (@derive_pinsker_fun p c Hp').
split => //.
case: Hp' => Hp'1 Hp'2.
fourier.
Defined.

Lemma pinsker_fun_increasing_on_p_to_1 (c : R) (Hc : c <= / (2 * ln 2)) (Hp' : 0 < p < 1) :
  forall x y, p <= x < 1 -> p <= y < 1 -> x <= y -> pinsker_fun p c x <= pinsker_fun p c y.
Proof.
apply derive_increasing_interv_right with (pinsker_fun_pderivable2 c Hp').
  by case: Hp'.
move=> t [Ht1 Ht2].
rewrite /pinsker_fun_pderivable2.
destruct Hp' as [Hp'1 Hp'2].
rewrite derive_pt_pinsker_fun //; last by split; fourier.
rewrite /pinsker_fun' /div_fct.
have X : 0 <= (/ (t * (1 - t) * ln 2) - 8 * c).
  have : forall a b, b <= a -> 0 <= a - b by move=> *; fourier.
  apply.
  have Hlocal : 0 <= / ln 2 by apply Rlt_le, Rinv_0_lt_compat, ln_2_pos.
  have Hlocal2 : t * (1 - t) <> 0 by apply nesym, Rlt_not_eq, mulR_gt0; fourier.
  apply Rle_trans with (4 / ln 2).
    apply Rle_trans with (8 * / (2 * ln 2)).
      apply/RleP.
      rewrite Rle_pmul2l; last by apply/RltP; fourier.
      by apply/RleP.
    rewrite Rinv_mult_distr; last 2 first.
      move=> ?; fourier.
      by apply ln_2_neq0.
    rewrite mulRA.
    apply Rmult_le_compat_r => //; by fourier.
  rewrite Rinv_mult_distr //; last by apply ln_2_neq0.
  apply Rmult_le_compat_r => //.
  apply Rle_inv_conv.
  fourier.
  apply Rinv_0_lt_compat, mulR_gt0; fourier.
  rewrite invRK // -[X in _ <= X]mul1R; by apply x_x2_max.
rewrite /inv_fct; apply mulR_ge0 => //; fourier.
Qed.

End pinsker_function_analysis.

Local Open Scope proba_scope.
Local Open Scope reals_ext_scope.

Section pinsker_fun_pos_sect.

Variables p q : R.
Hypothesis p01 : 0 <= p <= 1.
Hypothesis q01 : 0 <= q <= 1.

Variable A : finType.
Hypothesis card_A : #|A| = 2%nat.
Hypothesis P_dom_by_Q : (Binary.d card_A p01) << (Binary.d card_A q01).

Lemma pinsker_fun_pos c : 0 <= c <= / (2 * ln 2) -> 0 <= pinsker_fun p c q.
Proof.
move=> Hc.
case: p01 => Hp0 Hp1.
case: q01 => Hq0 Hq1.
set a := Set2.a card_A. set b := Set2.b card_A.
case/Rle_lt_or_eq_dec : Hp0 => Hp0; last first.
  subst p.
  rewrite /pinsker_fun /div_fct /comp.
  rewrite !(mul0R,mulR0,addR0,add0R,Rminus_0_l,subR0).
  case/Rle_lt_or_eq_dec : Hq1 => Hq1; last first.
    subst q.
    exfalso.
    move: P_dom_by_Q.
    rewrite /dom_by /Binary.d /= => /(_ a).
    rewrite /Binary.f eqxx Rminus_diag_eq // => /(_ erefl) ?; fourier.
  eapply Rle_trans; first by apply (pinsker_function_spec_pos Hc (conj Hq0 Hq1)).
  rewrite /pinsker_function_spec.
  apply Req_le.
  rewrite mul1R div1R /log LogV; by [field | fourier].
case/Rle_lt_or_eq_dec : Hp1 => Hp1; last first.
  subst p.
  rewrite /pinsker_fun /div_fct /comp.
  rewrite (Rminus_diag_eq 1) //.
  rewrite mul0R addR0.
  case/Rle_lt_or_eq_dec : Hq0 => Hq0; last first.
    subst q.
    exfalso.
    move: P_dom_by_Q.
    rewrite /dom_by /Binary.d /= => /(_ b); rewrite /Binary.f.
    rewrite eq_sym (negbTE (Set2.a_neq_b card_A)) => /(_ erefl) ?; fourier.
  apply: Rle_trans.
    have : 0 <= 1 - q < 1 by split; fourier.
    by apply: pinsker_function_spec_pos Hc.
  rewrite /pinsker_function_spec.
  apply Req_le.
  rewrite mul1R div1R /log LogV; last by rewrite /id.
  rewrite /id (_ : 1 - (1 - q) = q) //; by field.
case/Rle_lt_or_eq_dec : Hq0 => Hq0; last first.
  subst q.
  rewrite /pinsker_fun /div_fct /comp.
  rewrite (_ : id 0 = 0) //.
  exfalso.
  move: P_dom_by_Q.
  rewrite /dom_by /Binary.d /= => /(_ b); rewrite /Binary.f.
  rewrite eq_sym (negbTE (Set2.a_neq_b card_A)) => /(_ erefl) ?; subst p.
  by move/Rlt_irrefl : Hp0.
case/Rle_lt_or_eq_dec : Hq1 => Hq1; last first.
  subst q.
  rewrite /pinsker_fun /div_fct /comp.
  exfalso.
  move: P_dom_by_Q.
  rewrite /dom_by /Binary.d /= => /(_ a).
  rewrite /Binary.f eqxx Rminus_diag_eq // => /(_ erefl) H1.
  have {H1}? : p = 1. fourier. subst p.
  by move/Rlt_irrefl : Hp1.
rewrite -(pinsker_fun_p p01 c).
case: (Rlt_le_dec q p) => qp.
  apply pinsker_fun_decreasing_on_0_to_p => //.
  - by case : Hc.
  - split; fourier.
  - split; fourier.
  - by apply Rlt_le.
apply pinsker_fun_increasing_on_p_to_1 => //.
- by case: Hc.
- split; fourier.
Qed.

End pinsker_fun_pos_sect.
