(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum.
Require Import Reals Lra.
From mathcomp Require Import mathcomp_extra Rstruct reals.
Require Import ssrR Reals_ext realType_ext Ranalysis_ext ssr_ext.
Require Import logb ln_facts bigop_ext convex fdist divergence.
Require Import variation_dist partition_inequality.

(******************************************************************************)
(*                       Pinsker's Inequality                                 *)
(*                                                                            *)
(* pinkser_fun        == function used in the proof of Pinsker's inequality   *)
(* Pinsker_inequality == main lemma                                           *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope R_scope.
Local Open Scope fdist_scope.

Definition pinsker_fun p c := fun q =>
  p * log (div_fct (fun _ => p) id q) +
  (1 - p) * log (div_fct (fun _ => 1 - p) (fun q => 1 - q) q) -
  4 * c * comp (fun x => x ^2) (fun q => p - q) q.

Lemma derive_pinsker_fun (p : R) c : 0 < p < 1 ->
  pderivable (pinsker_fun p c) (fun q => 0 < q < 1).
Proof.
move=> [H0p Hp1] q /= [Hq1 Hq2].
rewrite /pinsker_fun.
apply: derivable_pt_minus.
  apply derivable_pt_plus.
    apply derivable_pt_mult.
      exact: derivable_pt_const.
    apply derivable_pt_comp.
      apply derivable_pt_mult.
        apply derivable_pt_const.
      apply derivable_pt_inv.
      exact/eqP/gtR_eqF.
      apply derivable_pt_id.
    apply derivable_pt_Log.
    exact: divR_gt0.
  apply derivable_pt_mult.
    exact: derivable_pt_const.
  apply derivable_pt_comp.
    apply derivable_pt_div.
      apply derivable_pt_const.
      apply derivable_pt_Rminus.
      move=> abs; lra.
  apply derivable_pt_Log.
  by apply divR_gt0 => //; lra.
apply derivable_pt_mult.
  exact: derivable_pt_const.
by apply: derivable_pt_comp; [exact: derivable_pt_Rminus|exact: derivable_pt_pow].
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
rewrite !(derive_pt_minus,derive_pt_plus,derive_pt_comp,derive_pt_ln,
  derive_pt_const,derive_pt_mult,derive_pt_inv,derive_pt_id,derive_pt_div,
  derive_pt_pow).
rewrite !(mul0R,mulR0,addR0,add0R,Rminus_0_l) /= (_ : INR 2 = 2) //.
rewrite /pinsker_fun' /div_fct [X in _ = X]mulRBr.
f_equal; last by field.
rewrite (_ : id q = q)// 2!Rinv_div.
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
by split; [exact/eqP/ln2_neq0 | split => ?; lra].
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
by apply: derivable_pt_mult; [exact: derivable_pt_const|exact: derivable_pt_pow].
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

Lemma pinsker_fun_increasing_on_0_to_1 (c : R) (Hc : c <= / (2 * ln 2)) :
  forall x y,
  0 <= x < 1 -> 0 <= y < 1 -> x <= y ->
  pinsker_function_spec c x <= pinsker_function_spec c y.
Proof.
apply pderive_increasing_closed_open with (pderivable_pinsker_function_spec c).
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
move: H2 => /RleP; rewrite -mulRA RmultE mulNr lerNl opprK.
by move=> /RleP; rewrite -!RmultE mulRA subR_ge0.
Qed.

Lemma pinsker_function_spec_pos c q :
  0 <= c <= / (2 * ln 2) ->
  0 <= q < 1 ->
  0 <= pinsker_function_spec c q.
Proof.
move=> Hc [q0 q1].
rewrite (_ : 0 = pinsker_function_spec c 0); last first.
  by rewrite /pinsker_function_spec /= subR0 /log Log_1; field.
apply pinsker_fun_increasing_on_0_to_1 => //.
by case: Hc.
Qed.

Section pinsker_function_analysis.
Variables p q : {prob R}.

Lemma pinsker_fun_p c : pinsker_fun (Prob.p p) c (Prob.p p) = 0.
Proof.
rewrite /pinsker_fun /= /div_fct /comp subRR mul0R mulR0 subR0.
have [->|p0] := eqVneq p 0%:pr.
  by rewrite mul0R !subR0 add0R mul1R div1R invR1 /log Log_1.
have [->|p1] := eqVneq p 1%:pr.
  by rewrite divR1 /log Log_1 subRR mul0R mulR0 addR0.
rewrite divRR; last by rewrite subR_eq0' eq_sym.
by rewrite /log Log_1 divRR // /log Log_1; field.
Qed.

Lemma pinsker_fun_pderivable1 c (Hp' : 0 < Prob.p p < 1) :
  pderivable (fun x => - pinsker_fun (Prob.p p) c x) (fun q => 0 < q <= Prob.p p).
move=> x [Hx1 Hx2].
apply derivable_pt_opp.
apply: (@derive_pinsker_fun _ c Hp').
case: Hp' => Hp'1 Hp'2.
split => //.
lra.
Defined.

Lemma pinsker_fun_decreasing_on_0_to_p (c : R) (Hc : c <= / (2 * ln 2))
  (p01 : 0 < Prob.p p < 1) :
  forall x y, 0 < x <= Prob.p p -> 0 < y <= Prob.p p -> x <= y ->
  pinsker_fun (Prob.p p) c y <= pinsker_fun (Prob.p p) c x.
Proof.
move=> x y Hx Hy xy.
rewrite -[X in _ <= X]oppRK leR_oppr.
move: x y Hx Hy xy.
apply pderive_increasing_open_closed with (pinsker_fun_pderivable1 c p01).
  by case: p01.
move=> t [t0 tp].
rewrite /pinsker_fun_pderivable1.
rewrite derive_pt_opp.
rewrite derive_pt_pinsker_fun //; last lra.
rewrite /pinsker_fun' /div_fct.
have Hlocal : 0 <= / ln 2 by exact/invR_ge0.
have X : 0 <= (/ (t * (1 - t) * ln 2) - 8 * c).
  rewrite subR_ge0; apply (@leR_trans (4 / ln 2)).
    apply (@leR_trans  (8 * / (2 * ln 2))).
      apply leR_wpmul2l => //; lra.
    rewrite invRM; last 2 first.
      by apply/eqP.
      exact/ln2_neq0.
    rewrite mulRA; apply leR_wpmul2r => //; lra.
  rewrite invRM; last 2 first.
    by apply/gtR_eqF/mulR_gt0; lra.
    exact/ln2_neq0.
  apply leR_wpmul2r => //.
  rewrite -(invRK 4).
  apply leR_inv => //.
    by apply/mulR_gt0 => //; lra.
  exact: x_x2_max.
by rewrite /inv_fct -mulNR; apply mulR_ge0 => //; lra.
Qed.

Lemma pinsker_fun_pderivable2 c (Hp' : 0 < Prob.p p < 1) :
  pderivable (fun x : R => pinsker_fun (Prob.p p) c x) (fun q : R => Prob.p p <= q < 1).
move=> x [Hx1 Hx2].
apply: (@derive_pinsker_fun _ c Hp').
split => //.
case: Hp' => Hp'1 Hp'2.
lra.
Defined.

Lemma pinsker_fun_increasing_on_p_to_1 (c : R) (Hc : c <= / (2 * ln 2))
  (p01 : 0 < Prob.p p < 1) :
  forall x y, Prob.p p <= x < 1 -> Prob.p p <= y < 1 -> x <= y ->
  pinsker_fun (Prob.p p) c x <= pinsker_fun (Prob.p p) c y.
Proof.
apply pderive_increasing_closed_open with (pinsker_fun_pderivable2 c p01).
  by case: p01.
move=> t [pt t1].
rewrite /pinsker_fun_pderivable2.
rewrite derive_pt_pinsker_fun //; last lra.
rewrite /pinsker_fun' /div_fct.
have X : 0 <= (/ (t * (1 - t) * ln 2) - 8 * c).
  have : forall a b, b <= a -> 0 <= a - b by move=> *; lra.
  apply.
  have Hlocal : 0 <= / ln 2 by exact/invR_ge0.
  have /eqP Hlocal2 : t * (1 - t) <> 0 by apply/eqP/gtR_eqF/mulR_gt0; lra.
  apply (@leR_trans (4 / ln 2)).
    apply (@leR_trans (8 * / (2 * ln 2))).
      apply/RleP.
      rewrite 2!RmultE ler_pM2l//; last first.
        by apply/RltP; rewrite (_ : 0%mcR = 0)//; lra.
      exact/RleP.
    rewrite invRM ?mulRA; last 2 first.
      exact/eqP.
      exact/ln2_neq0.
    by apply leR_wpmul2r => //; lra.
  rewrite invRM //; last exact/ln2_neq0.
  apply leR_wpmul2r => //.
  rewrite -(invRK 4) //=.
  apply leR_inv => //.
    by apply/mulR_gt0; lra.
  exact: x_x2_max.
rewrite /inv_fct; apply mulR_ge0 => //; lra.
Qed.

End pinsker_function_analysis.

Local Open Scope reals_ext_scope.

Section pinsker_fun_pos.
Variables p q : {prob R}.
Variable A : finType.
Hypothesis card_A : #|A| = 2%nat.
Hypothesis P_dom_by_Q :
  fdist_binary card_A p (Set2.a card_A) `<< fdist_binary card_A q (Set2.a card_A).

Lemma pinsker_fun_pos c : 0 <= c <= / (2 * ln 2) -> 0 <= pinsker_fun (Prob.p p) c (Prob.p q).
Proof.
move=> Hc.
set a := Set2.a card_A. set b := Set2.b card_A.
have [p0|p0] := eqVneq p 0%:pr.
  subst p.
  rewrite /pinsker_fun /div_fct /comp.
  rewrite !(mul0R,mulR0,addR0,add0R,Rminus_0_l,subR0).
  have [q1|q1] := eqVneq q 1%:pr.
    subst q.
    exfalso.
    move/dominatesP : P_dom_by_Q => /(_ a).
    by rewrite !fdist_binaryE !/onem subrr eqxx subr0 -R1E -R0E; lra.
  apply: leR_trans.
    apply: (@pinsker_function_spec_pos _ (Prob.p q) Hc); split=> //.
    by apply/RltP; rewrite -prob_lt1.
  rewrite /pinsker_function_spec.
  apply: Req_le.
  by rewrite mul1R div1R /log LogV; [field|
    rewrite subR_gt0; apply /RltP; rewrite -prob_lt1].
have [p1|p1] := eqVneq p 1%:pr.
  subst p.
  rewrite /pinsker_fun /div_fct /comp subRR mul0R addR0.
  have [q0|q0] := eqVneq q 0%:pr.
    subst q.
    exfalso.
    move/dominatesP : P_dom_by_Q => /(_ b).
    rewrite !fdist_binaryE /onem subrr eq_sym (negbTE (Set2.a_neq_b card_A)) /=.
    by move=> /(_ erefl)/eqP; rewrite oner_eq0.
  apply: leR_trans.
    have : 0 <= 1 - Prob.p q < 1.
      split; first by rewrite subR_ge0.
      by rewrite ltR_subl_addr -{1}(addR0 1) ltR_add2l; apply/RltP/ prob_gt0.
    exact: pinsker_function_spec_pos Hc.
  rewrite /pinsker_function_spec.
  apply Req_le.
  rewrite mul1R div1R /log LogV; [|by apply/RltP/prob_gt0].
  rewrite /id (_ : 1 - (1 - Prob.p q) = Prob.p q) //; by field.
have [q0|q0] := eqVneq q 0%:pr.
  subst q.
  rewrite /pinsker_fun /div_fct /comp.
  exfalso.
  move/dominatesP : P_dom_by_Q => /(_ b).
  rewrite !fdist_binaryE eq_sym (negbTE (Set2.a_neq_b card_A)) => /(_ erefl) p0_.
  by move/eqP : p0; apply; apply/val_inj; rewrite /= p0_.
have [q1|q1] := eqVneq q 1%:pr.
  subst q.
  exfalso.
  move/dominatesP : P_dom_by_Q => /(_ a).
  rewrite !fdist_binaryE /onem subrr eqxx subR_eq0 => /(_ erefl) p1_.
  by move/eqP : p1; apply; apply/val_inj; rewrite /= -p1_.
rewrite -(pinsker_fun_p p c).
case: (Rlt_le_dec (Prob.p q) (Prob.p p)) => qp.
  apply pinsker_fun_decreasing_on_0_to_p => //.
  - lra.
  - by split; apply/RltP; [rewrite -prob_gt0 | rewrite -prob_lt1].
  - by split; [apply/RltP/prob_gt0 | exact/ltRW].
  - split; [by apply/RltP/prob_gt0 | ].
    by apply/RleP; rewrite lexx.
  - exact/ltRW.
apply pinsker_fun_increasing_on_p_to_1 => //.
- lra.
- by split; apply/RltP; [rewrite -prob_gt0 |rewrite -prob_lt1].
- by split; [by apply/RleP; rewrite lexx |apply/RltP/prob_lt1].
- by split => //; apply/RltP; rewrite -prob_lt1.
Qed.

End pinsker_fun_pos.

Local Open Scope divergence_scope.
Local Open Scope variation_distance_scope.

Section Pinsker_2_bdist.
Variables p q : {prob R}.
Variable A : finType.
Hypothesis card_A : #|A| = 2%nat.

Let P := fdist_binary card_A p (Set2.a card_A).
Let Q := fdist_binary card_A q (Set2.a card_A).

Hypothesis P_dom_by_Q : P `<< Q.

Lemma pinsker_fun_p_eq c : pinsker_fun (Prob.p p) c (Prob.p q) = D(P || Q) - c * d(P , Q) ^ 2.
Proof.
pose a := Set2.a card_A. pose b := Set2.b card_A.
set pi := P a.
set pj := P b.
set qi := Q a.
set qj := Q b.
have Hpi : pi = 1 - Prob.p p by rewrite /pi /P fdist_binaryxx.
have Hqi : qi = 1 - Prob.p q by rewrite /qi /= fdist_binaryxx.
have Hpj : pj = Prob.p p.
  by rewrite /pj /= fdist_binaryE eq_sym (negbTE (Set2.a_neq_b card_A)).
have Hqj : qj = Prob.p q.
  by rewrite /qj /= fdist_binaryE eq_sym (negbTE (Set2.a_neq_b card_A)).
transitivity (D(P || Q) - c * (`| Prob.p p - Prob.p q | + `| (1 - Prob.p p) - (1 - Prob.p q) |) ^ 2).
  rewrite /pinsker_fun /div Set2sumE -/a -/b -/pi -/pj -/qi -/qj Hpi Hpj Hqi Hqj.
  set tmp := (`| _ | + _) ^ 2.
  have -> : tmp = 4 * (Prob.p p - Prob.p q) ^ 2.
    rewrite /tmp (_ : 1 - Prob.p p - (1 - Prob.p q) = Prob.p q - Prob.p p); last by field.
    rewrite sqrRD (distRC (Prob.p q) (Prob.p p)) -mulRA -{3}(pow_1 `| Prob.p p - Prob.p q |).
    rewrite -expRS sqR_norm; ring.
  rewrite [X in _ = _ + _ - X]mulRA.
  rewrite [in X in _ = _ + _ - X](mulRC c).
  congr (_ - _).
  case/boolP : (p == 0%:pr) => [/eqP |] p0.
    rewrite p0 !mul0R subR0 addR0 add0R !mul1R /log (*_Log_1*) /Rdiv.
    have [q1|q1] := eqVneq q 1%:pr.
      move/dominatesP : P_dom_by_Q => /(_ (Set2.a card_A)).
      rewrite -/pi -/qi Hqi q1 subRR => /(_ erefl).
      by rewrite Hpi p0 subR0 -R0E => ?; exfalso; lra.
    rewrite /log LogM; last 2 first.
      lra.
      by apply/invR_gt0; rewrite subR_gt0; apply/RltP/prob_lt1.
      rewrite LogV; last by apply/subR_gt0/RltP/prob_lt1.
      by rewrite Log_1.
  have [q0|q0] := eqVneq q 0%:pr.
    move/dominatesP : P_dom_by_Q => /(_ (Set2.b card_A)).
    rewrite -/pj -/qj Hqj q0 => /(_ erefl).
    rewrite Hpj => abs.
    have : p == 0%:pr by apply/eqP/val_inj.
    by rewrite (negbTE p0).
  rewrite /div_fct /comp /= (_ : id (Prob.p q) = Prob.p q) //.
  have [->|p1] := eqVneq p 1%:pr.
    rewrite subRR !mul0R /Rdiv /log LogM //; last first.
      apply/invR_gt0; by apply/RltP/prob_gt0.
      rewrite Log_1 /= mul1R LogV //; last by apply/RltP/prob_gt0.
      by rewrite !(add0R,mul1R,addR0,sub0R).
  rewrite /log LogM //; last 2 first.
    by apply/RltP/prob_gt0.
    by apply/invR_gt0/RltP/prob_gt0.
  rewrite LogV //; last by apply/RltP/prob_gt0.
  have [q1|q1] := eqVneq q 1%:pr.
    move/dominatesP : P_dom_by_Q => /(_ (Set2.a card_A)).
    rewrite -/pi -/qi Hqi q1 subRR => /(_ erefl).
    rewrite Hpi subR_eq0 => abs.
    have : p == 1%:pr by apply/eqP/val_inj.
    by rewrite (negbTE p1).
  rewrite /Rdiv LogM ?subR_gt0 //; last 2 first.
    by apply/RltP/prob_lt1.
    by apply/invR_gt0; rewrite subR_gt0; apply/RltP/prob_lt1.
  rewrite LogV; last by rewrite subR_gt0; apply/RltP/prob_lt1.
  ring.
congr (_ - _ * _).
by rewrite /var_dist Set2sumE // -/pi -/pj -/qi -/qj Hpi Hpj Hqi Hqj addRC.
Qed.

Lemma Pinsker_2_inequality_bdist : / (2 * ln 2) * d(P , Q) ^ 2 <= D(P || Q).
Proof.
set lhs := _ * _.
set rhs := D(_ || _).
rewrite -subR_ge0 -pinsker_fun_p_eq.
apply pinsker_fun_pos with A card_A => //.
by split; [exact/invR_ge0/mulR_gt0 | by apply/RleP; rewrite lexx].
Qed.

End Pinsker_2_bdist.

Section Pinsker_2.
Variables (A : finType) (P Q : {fdist A}).
Hypothesis card_A : #|A| = 2%nat.
Hypothesis P_dom_by_Q : P `<< Q.

Lemma Pinsker_2_inequality : / (2 * ln 2) * d(P , Q) ^ 2 <= D(P || Q).
Proof.
move: (charac_bdist P card_A) => [r1 Hp].
move: (charac_bdist Q card_A) => [r2 Hq].
rewrite Hp Hq.
apply Pinsker_2_inequality_bdist.
by rewrite -Hp -Hq.
Qed.

End Pinsker_2.

Section Pinsker.
Variables (A : finType) (P Q : {fdist A}).
Hypothesis P_dom_by_Q : P `<< Q.

Local Notation "0" := (false).
Local Notation "1" := (true).

Lemma bipart_dominates :
  let A_ := fun b => if b then [set a | (P a < Q a)%mcR]
                          else [set a | (Q a <= P a)%mcR] in
  forall (cov : A_ 0 :|: A_ 1 = [set: A]) (dis : A_ 0 :&: A_ 1 = set0),
  bipart dis cov P `<< bipart dis cov Q.
Proof.
move=> A_ cov dis; apply/dominatesP => /= b.
rewrite !ffunE => /psumr_eq0P H.
transitivity (\sum_(a | a \in A_ b) 0%R).
  apply eq_bigr => // a ?.
  by rewrite (dominatesE P_dom_by_Q) // H // => a' ?; exact/pos_ff_ge0.
by rewrite big_const iter_addR mulR0.
Qed.

Lemma Pinsker_inequality : / (2 * ln 2) * d(P , Q) ^ 2 <= D(P || Q).
Proof.
pose A0 := [set a | (Q a <= P a)%mcR].
pose A1 := [set a | (P a < Q a)%mcR].
pose A_ := fun b => match b with 0 => A0 | 1 => A1 end.
have cov : A_ 0 :|: A_ 1 = setT.
  rewrite /= /A0 /A1.
  have -> : [set x | (P x < Q x)%mcR] = ~: [set x | (Q x <= P x)%mcR].
    by apply/setP => a; rewrite in_set in_setC in_set ltNge.
  by rewrite setUCr.
have dis : A_ 0 :&: A_ 1 = set0.
  rewrite /A_ /A0 /A1.
  have -> : [set x | (P x < Q x)%mcR] = ~: [set x | (Q x <= P x)%mcR].
    by apply/setP => a; rewrite in_set in_setC in_set ltNge.
  by rewrite setICr.
pose P_A := bipart dis cov P.
pose Q_A := bipart dis cov Q.
have step1 : D(P_A || Q_A) <= D(P || Q).
  by apply partition_inequality; exact P_dom_by_Q.
suff : / (2 * ln 2) * d(P , Q) ^2 <= D(P_A || Q_A).
  move=> ?; apply (@leR_trans (D(P_A || Q_A))) => //; exact/Rge_le.
have -> : d( P , Q ) = d( P_A , Q_A ).
  rewrite /var_dist.
  transitivity (\sum_(a | a \in A0) `| P a - Q a | + \sum_(a | a \in A1) `| P a - Q a |).
    rewrite -big_union //; last by rewrite -setI_eq0 -dis /A_ setIC.
    apply eq_bigl => a; by rewrite cov in_set.
  transitivity (`| P_A 0 - Q_A 0 | + `| P_A 1 - Q_A 1 |).
    congr (_ + _).
    - rewrite /P_A /Q_A /bipart /= /bipart_pmf /=.
      transitivity (\sum_(a | a \in A0) (P a - Q a)).
        apply: eq_bigr => a; rewrite /A0 in_set => /RleP Ha.
        by rewrite geR0_norm ?subR_ge0.
      rewrite big_split /= geR0_norm; last first.
        rewrite subR_ge0; rewrite !ffunE.
        by apply leR_sumR => ?; rewrite inE => /RleP.
      by rewrite -big_morph_oppR // 2!ffunE addR_opp.
    - rewrite /P_A /Q_A /bipart /= !ffunE /=.
      have [A1_card | A1_card] : #|A1| = O \/ (0 < #|A1|)%nat.
        destruct (#|A1|); [tauto | by right].
      + move/eqP : A1_card; rewrite cards_eq0; move/eqP => A1_card.
        by rewrite A1_card !big_set0 subRR normR0.
      + transitivity (\sum_(a | a \in A1) - (P a - Q a)).
          apply eq_bigr => a; rewrite /A1 in_set => Ha.
          by rewrite ltR0_norm // subR_lt0; exact/RltP.
        rewrite -big_morph_oppR // big_split /= ltR0_norm; last first.
          rewrite subR_lt0; apply ltR_sumR_support => // a.
          by rewrite /A1 in_set => /RltP.
        by rewrite -big_morph_oppR.
  by rewrite big_bool /= /bipart_pmf !ffunE /=.
exact/(Pinsker_2_inequality card_bool)/bipart_dominates.
Qed.

Lemma Pinsker_inequality_weak : d(P , Q) <= sqrt (2 * D(P || Q)).
Proof.
rewrite -(sqrt_Rsqr (d(P , Q))); last exact/pos_var_dist.
apply sqrt_le_1_alt.
apply (@leR_pmul2l (/ 2)); first by apply invR_gt0; lra.
apply (@leR_trans (D(P || Q))); last first.
  rewrite mulRA mulVR // ?mul1R; [| exact/gtR_eqF].
  by apply/RleP; rewrite lexx.
apply: (leR_trans _ Pinsker_inequality).
rewrite (_ : forall x, Rsqr x = x ^ 2); last first.
  by move=> ?; rewrite /Rsqr /pow mulR1.
apply leR_wpmul2r; first exact: pow_even_ge0.
apply leR_inv => //; first exact/mulR_gt0.
rewrite -[X in _ <= X]mulR1.
apply leR_wpmul2l; first lra.
rewrite [X in _ <= X](_ : 1%R = ln (exp 1)); last by rewrite ln_exp.
by apply ln_increasing_le; [lra | exact leR2e].
Qed.

End Pinsker.
