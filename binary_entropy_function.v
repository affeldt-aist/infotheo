(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div fintype tuple finfun bigop.
Require Import Reals Fourier.
Require Import Rssr Reals_ext Ranalysis_ext log2.

(** * The "natural entropy function" *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** We first find the maximum of the "natural entropy function"
    (the same the binary entropy function except that we replace
    the logarithm in base 2 by its natural version). *)

Definition H2ln := fun p => - p * ln p - (1 - p) * ln (1 - p).

Lemma derivable_pt_ln_Rminus x : x < 1 -> derivable_pt ln (1 - x).
Proof.
move=> Hx.
exists (/ (1 - x)).
apply derivable_pt_lim_ln, Rlt_Rminus.
assumption.
Defined.

Lemma pderivable_H2ln : pderivable H2ln (fun x => 0 < x <= 1/2).
Proof.
move=> x /= [Hx0 Hx1].
apply derivable_pt_minus.
apply derivable_pt_mult.
apply derivable_pt_Ropp.
apply derivable_pt_ln.
assumption.
apply derivable_pt_mult.
apply derivable_pt_Rminus.
apply derivable_pt_comp.
apply derivable_pt_Rminus.
apply derivable_pt_ln_Rminus.
fourier.
Defined.

(* NB: on peut pas utiliser derivable_pt_Ropp2? *)
Lemma pderivable_Ropp_H2ln : pderivable (fun x => - H2ln x) (fun x => 1/2 <= x < 1).
Proof.
rewrite /H2ln /pderivable => x [Hx0 Hx1].
apply derivable_pt_comp.
apply derivable_pt_minus.
apply derivable_pt_mult.
apply derivable_pt_Ropp.
apply derivable_pt_ln.
fourier.
apply derivable_pt_mult.
apply derivable_pt_Rminus.
apply derivable_pt_comp.
apply derivable_pt_Rminus.
apply derivable_pt_ln_Rminus.
assumption.
apply derivable_pt_Ropp.
Defined.

Lemma increasing_on_0_to_half : forall x y,
  0 < x <= 1/2 -> 0 < y <= 1/2 -> x <= y -> H2ln x <= H2ln y.
Proof.
apply derive_increasing_interv_left with (pr := pderivable_H2ln); first by fourier.
move=> t [Ht1 Ht2].
rewrite /H2ln /pderivable_H2ln derive_pt_minus 2!derive_pt_mult /=.
destruct (Rlt_le_dec 0 t) => /=; last first.
  suff : False by done.
  fourier.
rewrite derive_pt_comp /= mulRA.
apply Rle_trans with (- ln t + ln (1 - t)); last first.
  apply Req_le; field.
  split=> ?; fourier.
rewrite -ln_Rinv // -ln_mult; last 2 first.
  exact/invR_gt0.
  fourier.
rewrite -ln_1.
apply ln_increasing_le.
fourier.
apply Rmult_le_reg_l with t => //.
rewrite mulRA mulRV; last exact/eqP/gtR_eqF.
rewrite mulR1 mul1R; fourier.
Qed.

Lemma decreasing_on_half_to_1 : forall x y : R,
  1/2 <= x < 1 -> 1/2 <= y < 1 -> x <= y -> H2ln y <= H2ln x.
Proof.
move=> x y Hx Hy xy.
apply Ropp_le_cancel.
move: x y Hx Hy xy.
apply derive_increasing_interv_right with (pr := pderivable_Ropp_H2ln); first by fourier.
move=> t [Ht1 Ht2].
rewrite /H2ln /pderivable_Ropp_H2ln derive_pt_comp derive_pt_minus 2!derive_pt_mult /=.
destruct (Rlt_le_dec 0 t) => /=; last first.
  suff : False by done.
  fourier.
rewrite derive_pt_comp /= mulRA.
apply Rle_trans with (ln t - ln (1 - t)); last first.
  apply Req_le; field.
  split => abs; fourier.
suff : ln ( 1 - t) <= ln t.
  move=> ?; fourier.
apply ln_increasing_le; fourier.
Qed.

Lemma H2ln_max (q : R) : 0 < q < 1 -> - q * ln q - (1 - q) * ln (1 - q) <= ln 2.
Proof.
move=> [Hq0 Hq1].
apply Rle_trans with (H2ln (1/2)); last first.
  apply Req_le.
  rewrite /H2ln (_ : 1 - 1/2 = 1/2); last by field.
  rewrite -mulRBl (_ : - _ - _ = - 1); last by field.
  rewrite div1R ln_Rinv; [by field | by fourier].
rewrite -/(H2ln q).
case: (Rlt_le_dec q (1/2)) => H1.
- apply increasing_on_0_to_half => //.
  split; fourier.
  split; fourier.
  fourier.
- case/Rle_lt_or_eq_dec : H1 => H1.
  + apply decreasing_on_half_to_1 => //.
    split; fourier.
    split; fourier.
    fourier.
  + rewrite -H1; by apply Req_le.
Qed.

(** * The Binary Entropy Function *)

Definition H2 p := - (p * log p) + - ((1 - p) * log (1 - p)).

Lemma bin_ent_0eq0 : H2 0 = 0.
Proof.
rewrite /H2 /log.
by rewrite !(Log_1, mulR0, mul0R, oppR0, mul1R, mulR1,
                       add0R, addR0, subR0, Rplus_opp_r).
Qed.

Lemma bin_ent_1eq0 : H2 1 = 0.
Proof.
rewrite /H2 /log.
by rewrite /Rminus !(Log_1, mulR0, mul0R, oppR0, mul1R, mulR1,
                       add0R, addR0, subR0, Rplus_opp_r).
Qed.

(** The binary entropy function is bounded by 1: *)

Lemma H2_max : forall p, 0 < p < 1 -> H2 p <= 1.
Proof.
move=> p [Hp0 Hp1].
rewrite /H2.
apply Rmult_le_reg_l with (ln 2) => //.
rewrite mulR1 mulRDr /log -!mulNR !(mulRC (ln 2)) -!mulRA.
rewrite (mulVR _ ln2_neq0) !mulR1 (mulNR (1 - p)); exact/H2ln_max.
Qed.

Lemma H2_max' (x : R): 0 <= x <= 1 -> H2 x <= 1.
Proof.
move=> [x_0 x_1].
case: x_0 => [?|<-]; last by rewrite bin_ent_0eq0.
case: x_1 => [?|->]; last by rewrite bin_ent_1eq0.
exact: H2_max.
Qed.