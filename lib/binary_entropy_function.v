(* infotheo: information theory and error-correcting codes in Coq               *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later              *)
From mathcomp Require Import all_ssreflect.
Require Import Reals Lra.
Require Import ssrR Reals_ext Ranalysis_ext logb.

(******************************************************************************)
(*                    The natural entropy function                            *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   H2ln p == the binary entropy function except that we replace the         *)
(*             logarithm in base 2 by its natural version                     *)
(*   H2 p == the binary entropy function                                      *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*   H2ln_max == H2ln is upper bounded by ln 2                                *)
(*   H2_max   == the binary entropy function is bounded by 1                  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.

Definition H2ln := fun p => - p * ln p - (1 - p) * ln (1 - p).

Lemma derivable_pt_ln_Rminus x : x < 1 -> derivable_pt ln (1 - x).
Proof.
move=> Hx.
exists (/ (1 - x)).
apply derivable_pt_lim_ln, subR_gt0.
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
lra.
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
lra.
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
apply pderive_increasing_open_closed with (pr := pderivable_H2ln); first lra.
move=> t [Ht1 Ht2].
rewrite /H2ln /pderivable_H2ln derive_pt_minus 2!derive_pt_mult /=.
destruct (Rlt_le_dec 0 t) => /=; last by exfalso; lra.
rewrite derive_pt_comp /= mulRA.
apply (@leR_trans (- ln t + ln (1 - t))); last first.
  apply Req_le; field.
  by split=> ?; lra.
rewrite -ln_Rinv // -ln_mult; last 2 first.
  exact/invR_gt0.
  lra.
rewrite -ln_1.
apply ln_increasing_le; first lra.
apply (@leR_pmul2l t) => //.
by rewrite mulRA mulRV ?gtR_eqF // mulR1 mul1R; lra.
Qed.

Lemma decreasing_on_half_to_1 (x y : R) :
  1/2 <= x < 1 -> 1/2 <= y < 1 -> x <= y -> H2ln y <= H2ln x.
Proof.
move=> Hx Hy xy.
rewrite -[X in _ <= X]oppRK leR_oppr.
move: x y Hx Hy xy.
apply pderive_increasing_closed_open with (pr := pderivable_Ropp_H2ln); first lra.
move=> t [Ht1 Ht2].
rewrite /H2ln /pderivable_Ropp_H2ln derive_pt_comp derive_pt_minus 2!derive_pt_mult /=.
destruct (Rlt_le_dec 0 t) => /=; last first.
  by exfalso; lra.
rewrite derive_pt_comp /= mulRA.
apply (@leR_trans (ln t - ln (1 - t))); last first.
  apply Req_le; field.
  by split => ?; lra.
suff : ln ( 1 - t) <= ln t by move=> ?; lra.
by apply ln_increasing_le; lra.
Qed.

Lemma H2ln_max (q : R) : 0 < q < 1 -> - q * ln q - (1 - q) * ln (1 - q) <= ln 2.
Proof.
move=> [Hq0 Hq1].
apply (@leR_trans (H2ln (1/2))); last first.
  apply Req_le.
  rewrite /H2ln (_ : 1 - 1/2 = 1/2); last by field.
  rewrite -mulRBl (_ : - _ - _ = - 1); last by field.
  rewrite div1R ln_Rinv; [by field | lra].
rewrite -/(H2ln q).
case: (Rlt_le_dec q (1/2)) => [H1|].
- by apply increasing_on_0_to_half => //; lra.
- case/Rle_lt_or_eq_dec => [H1|<-]; last first.
    lra.
  by apply decreasing_on_half_to_1 => //; lra.
Qed.

Definition H2 p := - (p * log p) + - ((1 - p) * log (1 - p)).

Lemma bin_ent_0eq0 : H2 0 = 0.
Proof.
rewrite /H2 /log.
by rewrite !(Log_1, mulR0, mul0R, oppR0, mul1R, mulR1, add0R, addR0, subR0).
Qed.

Lemma bin_ent_1eq0 : H2 1 = 0.
Proof.
rewrite /H2 /log.
by rewrite !(Log_1, mulR0, mul0R, oppR0, mul1R, mulR1,
                       add0R, addR0, subR0, subRR).
Qed.

Lemma H2_max : forall p, 0 < p < 1 -> H2 p <= 1.
Proof.
move=> p [Hp0 Hp1].
rewrite /H2.
apply (@leR_pmul2l (ln 2)) => //.
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
