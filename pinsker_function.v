(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div fintype tuple finfun bigop.
Require Import Reals Lra.
Require Import ssrR Reals_ext ssr_ext Ranalysis_ext logb Rbigop proba.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Function used in the proof of Pinsker's inequality *)

Local Open Scope R_scope.

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
      exact/gtR_eqF.
      apply derivable_pt_id.
    apply derivable_pt_Log.
    exact: divR_gt0.
  apply derivable_pt_mult.
    apply derivable_pt_const.
  apply derivable_pt_comp.
    apply derivable_pt_div.
      apply derivable_pt_const.
      apply derivable_pt_Rminus.
      move=> abs; lra.
  apply derivable_pt_Log.
  apply divR_gt0 => //; lra.
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
rewrite /pinsker_fun' /div_fct [X in _ = X]mulRBr.
f_equal; last by field.
rewrite (_ : id q = q) //.
rewrite Rinv_Rdiv; last 2 first.
  move=> ?; lra.
  move=> ?; lra.
rewrite Rinv_Rdiv; last 2 first.
  move=> ?; lra.
  move=> ?; lra.
have -> : p * (/ ln 2 * (q / p) * (p * (-1 / q²))) = - (p / q) * / ln 2.
  rewrite !mulRA /Rsqr.
  field.
  split; [exact/eqP/ln2_neq0 | split => ?; lra].
have -> : (1 - p) * (/ ln 2 * ((1 - q) / (1 - p)) * (- (-1 * (1 - p)) / (1 - q)²)) =
  (((1 - p) / (1 - q))) * / ln 2.
  rewrite /Rsqr.
  field.
  split; [exact/eqP/ln2_neq0 | split => ?; lra].
rewrite /inv_fct.
field.
split; [exact/eqP/ln2_neq0 | split => ?; lra].
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
  decompose [and] Hq0; clear Hq0; lra.
apply derivable_pt_mult.
  apply derivable_pt_const.
apply derivable_pt_pow.
Defined.

Lemma derive_pt_pinsker_function_spec c q0 (Hq0 : 0 <= q0 < 1)
  (pr : derivable_pt (pinsker_function_spec c) q0) :
  derive_pt (pinsker_function_spec c) q0 pr = pinsker_function_spec' c q0.
Proof.
rewrite (proof_derive_irrelevance _ (pderivable_pinsker_function_spec c Hq0)) //.
rewrite /pinsker_function_spec.
rewrite derive_pt_minus.
rewrite derive_pt_opp.
rewrite derive_pt_comp.
rewrite derive_pt_Log.
rewrite derive_pt_mult.
rewrite derive_pt_pow.
rewrite derive_pt_const.
rewrite mul0R add0R /= /pinsker_function_spec' (_ : INR 2 = 2) //.
field.
split; [exact/eqP/ln2_neq0|case: Hq0 => ? ? ?; lra].
Defined.

Lemma pinsker_fun_increasing_on_0_to_1 (c : R) (Hc : c <= / (2 * ln 2)) : forall x y,
  0 <= x < 1 -> 0 <= y < 1 -> x <= y -> pinsker_function_spec c x <= pinsker_function_spec c y.
Proof.
apply derive_increasing_interv_right with (pderivable_pinsker_function_spec c).
lra.
move=> t Ht.
rewrite derive_pt_pinsker_function_spec // /pinsker_function_spec'.
apply (@leR_trans (/ ((1 - t) * ln 2) - 8 * t / (2 * ln 2))); last first.
  apply leR_add2l.
  rewrite leR_oppr oppRK -mulRA /Rdiv -[X in _ <= X]mulRA -/(Rdiv _ _).
  apply leR_wpmul2l; first lra.
  rewrite mulRC; apply leR_wpmul2l => //.
  by case: Ht.
apply (@leR_trans ((2 - 8 * t * (1 - t)) / (2 * (1 - t) * ln 2))); last first.
  apply Req_le.
  field.
  split; [exact/eqP/ln2_neq0 | case: Ht => ? ? ?; lra].
apply divR_ge0; last first.
  rewrite mulRC mulRA.
  apply mulR_gt0.
    apply mulR_gt0 => //; lra.
  case: Ht => ? ?; lra.
have H2 : -2 <= - 8 * t * (1 - t).
  rewrite !mulNR -mulRA.
  rewrite leR_oppr oppRK [X in _ <= X](_ : 2 = 8 * / 4); last by field.
  apply leR_wpmul2l; [lra | exact: x_x2_max].
apply (@leR_trans (2 - 2)); first lra.
apply leR_add; [exact/leRR | by rewrite -mulRA -mulNR mulRA].
Qed.

Lemma pinsker_function_spec_pos c q :
  0 <= c <= / (2 * ln 2) ->
  0 <= q < 1 ->
  0 <= pinsker_function_spec c q.
Proof.
move=> Hc [q0 q1].
rewrite (_ : 0 = pinsker_function_spec c 0); last first.
  rewrite /pinsker_function_spec /= subR0 /log Log_1; field.
apply pinsker_fun_increasing_on_0_to_1 => //.
by case: Hc.
lra.
Qed.

Section pinsker_function_analysis.

Variables p q : R.
Hypothesis Hp : 0 <= p <= 1.
Hypothesis Hq : 0 <= q <= 1.

Lemma pinsker_fun_p c : pinsker_fun p c p = 0.
Proof.
rewrite /pinsker_fun /= /div_fct /comp subRR mul0R mulR0 subR0.
case: Hp => Hp1 Hp2.
case/leR_eqVlt : Hp1 => [/esym ->|Hp1].
  by rewrite mul0R !subR0 add0R mul1R div1R invR1 /log Log_1.
case/leR_eqVlt : Hp2 => [->|Hp2].
  by rewrite divR1 /log Log_1 subRR mul0R mulR0 addR0.
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
lra.
Defined.

Lemma pinsker_fun_decreasing_on_0_to_p (c : R) (Hc : c <= / (2 * ln 2)) (Hp' : 0 < p < 1) :
  forall x y, 0 < x <= p -> 0 < y <= p -> x <= y -> pinsker_fun p c y <= pinsker_fun p c x.
Proof.
move=> x y Hx Hy xy.
rewrite -[X in _ <= X]oppRK leR_oppr.
move: x y Hx Hy xy.
apply derive_increasing_interv_left with (pinsker_fun_pderivable1 c Hp').
by case: Hp'.
move=> t [Ht1 Ht2].
rewrite /pinsker_fun_pderivable1.
rewrite derive_pt_opp.
destruct Hp' as [Hp'1 Hp'2].
rewrite derive_pt_pinsker_fun //; last lra.
rewrite /pinsker_fun' /div_fct.
have Hlocal : 0 <= / ln 2 by exact/ltRW/invR_gt0.
have X : 0 <= (/ (t * (1 - t) * ln 2) - 8 * c).
  have : forall a b, b <= a -> 0 <= a - b. move=> *; lra. apply.
  apply (@leR_trans (4 / ln 2)).
    apply (@leR_trans  (8 * / (2 * ln 2))).
      apply leR_wpmul2l => //; lra.
    rewrite invRM; last 2 first.
      move=> ?; lra.
      exact/eqP/ln2_neq0.
    rewrite mulRA.
    apply leR_wpmul2r => //; lra.
  rewrite invRM; last 2 first.
    apply/gtR_eqF/mulR_gt0; lra.
    exact/eqP/ln2_neq0.
  apply leR_wpmul2r => //.
  rewrite -(invRK 4) //.
  apply leR_inv => //.
    apply/mulR_gt0 => //; lra.
  exact: x_x2_max.
rewrite /inv_fct -mulNR; apply mulR_ge0 => //; lra.
Qed.

Lemma pinsker_fun_pderivable2 c (Hp' : 0 < p < 1) :
  pderivable (fun x : R => pinsker_fun p c x) (fun q : R => p <= q < 1).
move=> x [Hx1 Hx2].
apply: (@derive_pinsker_fun p c Hp').
split => //.
case: Hp' => Hp'1 Hp'2.
lra.
Defined.

Lemma pinsker_fun_increasing_on_p_to_1 (c : R) (Hc : c <= / (2 * ln 2)) (Hp' : 0 < p < 1) :
  forall x y, p <= x < 1 -> p <= y < 1 -> x <= y -> pinsker_fun p c x <= pinsker_fun p c y.
Proof.
apply derive_increasing_interv_right with (pinsker_fun_pderivable2 c Hp').
  by case: Hp'.
move=> t [Ht1 Ht2].
rewrite /pinsker_fun_pderivable2.
destruct Hp' as [Hp'1 Hp'2].
rewrite derive_pt_pinsker_fun //; last lra.
rewrite /pinsker_fun' /div_fct.
have X : 0 <= (/ (t * (1 - t) * ln 2) - 8 * c).
  have : forall a b, b <= a -> 0 <= a - b by move=> *; lra.
  apply.
  have Hlocal : 0 <= / ln 2 by exact/ltRW/invR_gt0.
  have Hlocal2 : t * (1 - t) <> 0 by apply/gtR_eqF/mulR_gt0; lra.
  apply (@leR_trans (4 / ln 2)).
    apply (@leR_trans (8 * / (2 * ln 2))).
      apply/leRP.
      rewrite leR_pmul2l'; [exact/leRP | by apply/ltRP; lra].
    rewrite invRM; last 2 first.
      move=> ?; lra.
      exact/eqP/ln2_neq0.
    rewrite mulRA.
    apply leR_wpmul2r => //; lra.
  rewrite invRM //; last exact/eqP/ln2_neq0.
  apply leR_wpmul2r => //.
  rewrite -(invRK 4) //=; apply leR_inv => //.
    apply/mulR_gt0; lra.
  exact: x_x2_max.
rewrite /inv_fct; apply mulR_ge0 => //; lra.
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
case/leR_eqVlt : Hp0 => [|] Hp0.
  subst p.
  rewrite /pinsker_fun /div_fct /comp.
  rewrite !(mul0R,mulR0,addR0,add0R,Rminus_0_l,subR0).
  case/leR_eqVlt : Hq1 => [|] Hq1.
    subst q.
    exfalso.
    move/dominatesP : P_dom_by_Q.
    rewrite /Binary.d /= /Binary.f /= subRR => /(_ a); rewrite eqxx.
    move/(_ erefl) => ?; lra.
  apply: leR_trans; first exact: (pinsker_function_spec_pos Hc (conj Hq0 Hq1)).
  rewrite /pinsker_function_spec.
  apply Req_le.
  rewrite mul1R div1R /log LogV; [by field | lra].
case/leR_eqVlt : Hp1 => [|] Hp1.
  subst p.
  rewrite /pinsker_fun /div_fct /comp subRR mul0R addR0.
  case/leR_eqVlt : Hq0 => [|] Hq0.
    subst q.
    exfalso.
    move/dominatesP : P_dom_by_Q.
    rewrite /Binary.d /= /Binary.f /= subRR => /(_ b).
    rewrite eq_sym (negbTE (Set2.a_neq_b card_A)) => /(_ erefl) ?; lra.
  apply: leR_trans.
    have : 0 <= 1 - q < 1 by lra.
    exact: pinsker_function_spec_pos Hc.
  rewrite /pinsker_function_spec.
  apply Req_le.
  rewrite mul1R div1R /log LogV; last by rewrite /id.
  rewrite /id (_ : 1 - (1 - q) = q) //; by field.
case/leR_eqVlt : Hq0 => [|] Hq0.
  subst q.
  rewrite /pinsker_fun /div_fct /comp.
  rewrite (_ : id 0 = 0) //.
  exfalso.
  move/dominatesP : P_dom_by_Q.
  rewrite /Binary.d /= /Binary.f /= => /(_ b).
  rewrite eq_sym (negbTE (Set2.a_neq_b card_A)) => /(_ erefl) ?; subst p.
  by move/ltRR : Hp0.
case/leR_eqVlt : Hq1 => [|] Hq1.
  subst q.
  rewrite /pinsker_fun /div_fct /comp.
  exfalso.
  move/dominatesP : P_dom_by_Q.
  rewrite /Binary.d /Binary.f /= subRR => /(_ a); rewrite eqxx.
  move/(_ erefl) => H1.
  have {H1}? : p = 1. lra. subst p.
  by move/ltRR : Hp1.
rewrite -(pinsker_fun_p p01 c).
case: (Rlt_le_dec q p) => qp.
  apply pinsker_fun_decreasing_on_0_to_p => //.
  - by case : Hc.
  - lra.
  - lra.
  - by apply Rlt_le.
apply pinsker_fun_increasing_on_p_to_1 => //.
- by case: Hc.
- lra.
Qed.

End pinsker_fun_pos_sect.
