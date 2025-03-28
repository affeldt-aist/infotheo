(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum interval ring lra.
From mathcomp Require Import mathcomp_extra classical_sets functions.
From mathcomp Require Import set_interval reals Rstruct topology normedtype.
From mathcomp Require Import sequences derive exp realfun.
Require Import ssr_ext ssralg_ext bigop_ext realType_ext realType_ln.
Require Import derive_ext.
Require Import fdist divergence variation_dist partition_inequality.

(**md**************************************************************************)
(* # Pinsker's Inequality                                                     *)
(*                                                                            *)
(* The main lemma is `Pinsker_inequality`.                                    *)
(*                                                                            *)
(* ```                                                                        *)
(*    pinkser_fun == function used in the proof of Pinsker's inequality       *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Section pinsker_fun_def.
Variable R : realType.

Definition pinsker_fun (p c q : R) :=
  p * log (p / q) +
  (1 - p) * log ((1 - p) / (1 - q)) -
  4 * c * (p - q) ^+ 2.

Definition pinsker_fun' (p c : R) := fun q =>
  (q - p) * ((q * (1 - q) * ln 2)^-1 - 8 * c).

Definition pinsker_function_spec (c q : R) :=
  - log (1 - q) - 4 * c * q ^+ 2.

Definition pinsker_function_spec' (c q : R) :=
   ((1 - q) * ln 2)^-1 - 8 * c * q.

Lemma pinsker_fun_p0 c q : q < 1 -> pinsker_fun 0 c q = pinsker_function_spec c q.
Proof.
move=> q1.
rewrite /pinsker_fun /pinsker_function_spec /=.
rewrite mul0r subr0 !add0r mul1r sqrrN.
by rewrite logDiv// ?subr_gt0// log1 add0r.
Qed.

Lemma pinsker_fun_onem p c q : pinsker_fun (1 - p) c (1 - q) = pinsker_fun p c q.
Proof.
rewrite /pinsker_fun [X in X + _ = _]addrC.
congr (_ + _ - _).
  by rewrite !opprD !opprK !addrA !subrr !add0r.
by rewrite -sqrrN !opprD !opprK addrCA !addrA subrr add0r.
Qed.

Lemma pinsker_fun_p p c : pinsker_fun p c p = 0.
Proof.
rewrite /pinsker_fun subrr expr0n /= mulr0 subr0.
have [->|p0] := eqVneq p 0.
  by rewrite mul0r !subr0 add0r mul1r div1r invr1 log1.
have [->|p1] := eqVneq p 1.
  by rewrite divr1 log1 subrr mul0r mulr0 addr0.
rewrite divff // divff ?subr_eq0 1?eq_sym//.
by rewrite log1 !mulr0 addr0.
Qed.

End pinsker_fun_def.

Section pinsker_function_analysis.
Variable R : realType.

Lemma derivable_pinsker_fun (p c v : R) : 0 < p < 1 ->
  {in [pred q | 0 < q < 1], forall q, derivable (pinsker_fun p c) q v}.
Proof.
move=> /andP [H0p Hp1] /= q /[!inE] /andP [Hq1 Hq2].
apply: diff_derivable.
rewrite /pinsker_fun.
apply: differentiableB; last by [].
apply: differentiableD.
  apply: differentiableM; first by [].
  apply: differentiable_comp.
    apply: differentiableM; first by [].
    by apply: differentiableV; rewrite // gt_eqF.
  apply: differentiable_Log=> //.
  exact: divr_gt0.
apply: differentiableM; first by [].
apply: differentiable_comp.
  apply: differentiableM=> //.
  apply: differentiableV=> //.
  lra.
apply: differentiable_Log=> //.
by apply: divr_gt0; lra.
Qed.

Lemma is_derive1_pinsker_fun
  (p : R) (Hp : 0 < p < 1) (c q : R) (Hq : 0 < q < 1) :
  is_derive q 1 (pinsker_fun p c) (pinsker_fun' p c q).
Proof.
case/andP: Hp => Hp1 Hp2.
case/andP: Hq => Hq1 Hq2.
rewrite /pinsker_fun /pinsker_fun'.
under [F in is_derive _ _ F]boolp.funext=> x.
  rewrite -sqrrN opprB.
  rewrite (_ : (x - p) ^+ 2 = ((fun x => x - p) ^+ 2) x); last by [].
  over.
rewrite mulrBr; apply: is_deriveB=> /=; last first.
  apply: is_deriveZ_eq.
  rewrite expr1 -!mulr_regl.
  ring.
rewrite (_ : q - p = p * (- (1 - q)) + (1 - p) * q ); last by ring.
rewrite mulrDl; apply: is_deriveD=> /=.
  rewrite -!mulrA; apply: is_deriveZ=> /=.
  apply: is_derive1_LogfM_eq=> //.
  - by apply: is_deriveV; rewrite gt_eqF.
  - by rewrite invr_gt0.
  - rewrite mulr_algl -mulr_regl; field.
    by rewrite ln2_neq0 /= subr_eq0 gt_eqF//= !gt_eqF.
rewrite -!mulrA; apply: is_deriveZ=> /=.
rewrite invfM mulrA mulfV ?gt_eqF//.
apply: is_derive1_LogfM_eq=> //=.
- by apply: is_deriveV; rewrite subr_eq0 gt_eqF.
- by rewrite subr_gt0.
- by rewrite invr_gt0 subr_gt0.
  rewrite -mulr_regl; field.
  by rewrite ln2_neq0 /= !subr_eq0 !gt_eqF.
Qed.

Lemma derive1_pinsker_fun (p : R) (Hp : 0 < p < 1) c q (Hq : 0 < q < 1) :
  'D_1 (pinsker_fun p c) q = pinsker_fun' p c q.
Proof. by have/@derive_val:= is_derive1_pinsker_fun Hp c Hq. Qed.

Lemma derivable_pinsker_function_spec (c v : R) :
  {in [pred q | 0 <= q < 1],
      forall q, derivable (pinsker_function_spec c) q v}.
Proof.
move=> q /[!inE] /andP [q0 q1].
apply: diff_derivable.
rewrite /pinsker_function_spec.
apply: differentiableB; last by [].
apply/differentiableN/differentiable_comp; first by [].
apply: differentiable_Log=> //.
by rewrite subr_gt0.
Qed.

Lemma is_derive1_pinsker_function_spec (c q : R) (Hq : 0 <= q < 1) :
  is_derive q 1 (pinsker_function_spec c) (pinsker_function_spec' c q).
Proof.
move: Hq=> /andP [q0 q1].
apply: is_deriveB.
  apply: is_deriveN_eq; first by apply: is_derive1_Logf=> //; rewrite subr_gt0.
  by simpl; field; rewrite ln2_neq0 subr_eq0 gt_eqF.
have->: 8 * c = 4 * c * 2 by ring.
apply: is_deriveZ_eq.
by rewrite -!mulr_regr; ring.
Qed.

Lemma derive1_pinsker_function_spec (c : R) q (Hq : 0 <= q < 1) :
  'D_1 (pinsker_function_spec c) q = pinsker_function_spec' c q.
Proof. by have/@derive_val:= is_derive1_pinsker_function_spec c Hq. Qed.

Lemma pinsker_fun_p0_increasing_on_0_to_1 (c : R) (Hc : c <= (2 * ln 2)^-1) :
  forall (x y : R),
  x \in `[0, 1[ -> y \in `[0, 1[ -> x <= y ->
  pinsker_fun 0 c x <= pinsker_fun 0 c y.
Proof.
move=> x y x01 y01.
have x1: x < 1 by have:= x01; rewrite in_itv /=; lra.
have y1: y < 1 by have:= y01; rewrite in_itv /=; lra.
rewrite !pinsker_fun_p0//.
apply: (derivable1_homo x01 y01).
  exact: derivable_pinsker_function_spec.
move=> q xqy.
move: x01 y01 xqy; rewrite !in_itv /==> x01 y01 xqy.
rewrite derive1_pinsker_function_spec; last lra.
rewrite /pinsker_function_spec'.
rewrite subr_ge0 mulrAC.
rewrite -ler_pdivlMl ?mulr_gt0//; last lra.
rewrite (le_trans Hc)//.
rewrite !invfM mulrA ler_pM2r ?invr_gt0 ?ln2_gt0//.
rewrite (_ : 8^-1 = 2^-1 * 4^-1); last by field.
rewrite -[leLHS]mulr1 -!mulrA ler_pM2l; last lra.  
rewrite -ler_pdivrMr -!invfM; last by rewrite invr_gt0 mulr_gt0; lra.
by rewrite invrK mul1r x_x2_max.
Qed.

Lemma pinsker_fun_p0_pos (c q : R) :
  0 <= c <= (2 * ln 2)^-1 ->
  q \in `[0, 1[ ->
  0 <= pinsker_fun 0 c q.
Proof.
move=> ? /[dup] q01 /[!in_itv] /= q01'.
rewrite [leLHS](_ : _ = pinsker_fun 0 c 0); last first.
  by rewrite pinsker_fun_p0 // /pinsker_function_spec /= subr0 log1; field.
apply pinsker_fun_p0_increasing_on_0_to_1=> //; [lra | | lra].
by rewrite in_itv /= lexx /=.
Qed.

Let derivableN_pinsker_fun (p c : R) v (Hp' : 0 < p < 1) :
  {in [pred q | 0 < q <= p],
      forall q, derivable (fun x => - pinsker_fun p c x) q v}.
Proof.
move=> x /[!inE] ?.
apply/derivableN/derivable_pinsker_fun=> //.
by rewrite inE; lra.
Qed.

Lemma pinsker_fun'_ge0 (p c q : R) :
  c <= (2 * ln 2)^-1 -> 0 < q < 1 -> p <= q -> 0 <= pinsker_fun' p c q.
Proof.
move=> Hc q01 pq.
rewrite /pinsker_fun' mulr_ge0 ?(subr_ge0 p)//.
rewrite (@le_trans _ _ (4 / ln 2 - 8 * c)) //.
  rewrite subr_ge0 -ler_pdivlMl//.
  by rewrite [leRHS](_ : _ = (2 * ln 2)^-1); last by lra.
rewrite lerB// invfM ler_pM// ?invr_ge0 ?ln2_ge0//.
rewrite -[leLHS]invrK lef_pV2 ?x_x2_max// posrE ?x_x2_pos//.
lra.
Qed.

Lemma pinsker_fun'_le0 (p c q : R) :
  c <= (2 * ln 2)^-1 -> 0 < q < 1 -> q <= p -> pinsker_fun' p c q <= 0.
Proof.
move=> Hc q01 qp.
rewrite /pinsker_fun' -opprB mulNr -oppr_ge0 opprK.
rewrite mulr_ge0 ?(subr_ge0 q)//.
rewrite (@le_trans _ _ (4 / ln 2 - 8 * c)) //.
  rewrite subr_ge0 -ler_pdivlMl//.
  by rewrite [leRHS](_ : _ = (2 * ln 2)^-1); last by lra.
rewrite lerB// invfM ler_pM// ?invr_ge0 ?ln2_ge0//.
rewrite -[leLHS]invrK lef_pV2 ?x_x2_max// posrE ?x_x2_pos//.
lra.
Qed.

Lemma pinsker_fun_decreasing_on_0_to_p (p c : R) (Hc : c <= (2 * ln 2)^-1)
  (p01 : 0 < p < 1) (x y : R) :
  x \in `]0, p] -> y \in `]0, p] -> x <= y ->
  pinsker_fun p c y <= pinsker_fun p c x.
Proof.
move=> /[dup] x0p /[1!in_itv] /= x0p' /[dup] y0p /[!in_itv] /= y0p' xy.
rewrite -lerN2.
set f := (fun x => -pinsker_fun p c x).
apply (derivable1_homo x0p y0p (derivableN_pinsker_fun p01))=> //.
move=> t /[dup] xty /[!in_itv] /= xty'; have: 0 < t < 1 by lra.
rewrite deriveN; last first.
  apply: derivable_pinsker_fun=> //.
  by rewrite inE; lra.
move /(is_derive1_pinsker_fun p01 c) /@derive_val ->.
by rewrite oppr_ge0 pinsker_fun'_le0; lra.
Qed.

Lemma pinsker_fun_increasing_on_p_to_1 (p c : R) (Hc : c <= (2 * ln 2)^-1)
  (p01 : 0 < p < 1) :
  forall x y, x \in `[p, 1[ -> y \in `[p, 1[ -> x <= y ->
  pinsker_fun p c x <= pinsker_fun p c y.
Proof.
move=> x y.
move=> /[dup] /[1!in_itv] /= ?; rewrite (_ : x = 1 - (1 - x)); [move=>? | ring].
move=> /[dup] /[1!in_itv] /= ?; rewrite (_ : y = 1 - (1 - y)); [move=>? | ring].
rewrite (_ : p = 1 - (1 - p)); last ring.
move=> ?.
set x' := 1 - x; set y' := 1 - y; set p' := 1 - p.
rewrite [leLHS]pinsker_fun_onem [leRHS]pinsker_fun_onem.
apply: (pinsker_fun_decreasing_on_0_to_p Hc); rewrite /x' /y' /p' ?in_itv /=; lra.
Qed.

End pinsker_function_analysis.


Local Open Scope reals_ext_scope.

Section pinsker_fun_pos.
Variable R : realType.
Variables p q : {prob R}.
Variable A : finType.
Hypothesis card_A : #|A| = 2%nat.
Hypothesis P_dom_by_Q :
  fdist_binary card_A p (Set2.a card_A) `<< fdist_binary card_A q (Set2.a card_A).

Lemma pinsker_fun_pos (c : R) : 0 <= c <= (2 * ln 2)^-1 -> 0 <= pinsker_fun p c q.
Proof.
move=> Hc.
set a := Set2.a card_A. set b := Set2.b card_A.
have [p0|p0] := eqVneq p 0%:pr.
  subst p.
  rewrite /pinsker_fun.
  rewrite !(mul0r,mulr0,addr0,add0r,sub0r,subr0).
  have [q1|q1] := eqVneq q 1%:pr.
    subst q.
    exfalso.
    move/dominatesP : P_dom_by_Q => /(_ a).
    by rewrite !fdist_binaryE !/onem subrr eqxx subr0; lra.
  apply: le_trans.
    apply: (@pinsker_fun_p0_pos _ _ q Hc).
    rewrite in_itv /=; apply/andP; split=> //.
    by rewrite -prob_lt1.
  rewrite pinsker_fun_p0 /pinsker_function_spec -?prob_lt1//.
  rewrite le_eqVlt; apply/orP; left; apply/eqP.
  by rewrite mul1r div1r logV; [field | rewrite subr_gt0 -prob_lt1].
have [p1|p1] := eqVneq p 1%:pr.
  subst p.
  rewrite /pinsker_fun subrr mul0r addr0.
  have [q0|q0] := eqVneq q 0%:pr.
    subst q.
    exfalso.
    move/dominatesP : P_dom_by_Q => /(_ b).
    rewrite !fdist_binaryE /onem subrr eq_sym (negbTE (Set2.a_neq_b card_A)) /=.
    by move=> /(_ erefl)/eqP; rewrite oner_eq0.
  apply: le_trans.
    have : 0 <= 1 - q < 1.
      apply/andP; split; first by rewrite subr_ge0.
      by rewrite ltrBlDr -{1}(addr0 1) ltrD2l; apply/prob_gt0.
    exact: pinsker_fun_p0_pos Hc.
  rewrite pinsker_fun_p0 /pinsker_function_spec; last first.
    by rewrite -[ltRHS]subr0 ltrD2l ltrN2 -prob_gt0.
  rewrite le_eqVlt; apply/orP; left; apply/eqP.
  rewrite mul1r div1r logV; [|by apply/prob_gt0].
  by rewrite (_ : 1 - (1 - q) = q :> R) //=; by field.
have [q0|q0] := eqVneq q 0%:pr.
  subst q.
  rewrite /pinsker_fun.
  exfalso.
  move/dominatesP : P_dom_by_Q => /(_ b).
  rewrite !fdist_binaryE eq_sym (negbTE (Set2.a_neq_b card_A)) => /(_ erefl) p0_.
  by move/eqP : p0; apply; apply/val_inj; rewrite /= p0_.
have [q1|q1] := eqVneq q 1%:pr.
  subst q.
  exfalso.
  move/dominatesP : P_dom_by_Q => /(_ a).
  rewrite !fdist_binaryE /onem subrr eqxx=> /(_ erefl) /eqP /[!subr_eq0] /eqP p1_.
  by move/eqP : p1; apply; apply/val_inj; rewrite /= -p1_.
rewrite -(pinsker_fun_p p c).
have/orP[qp|qp]:= le_total q p.
  apply pinsker_fun_decreasing_on_0_to_p => //.
  - lra.
  - by apply/andP; split; [rewrite -prob_gt0 | rewrite -prob_lt1].
  - by apply/andP; split; [apply/prob_gt0 | ].
  - by apply/andP; split; [exact/prob_gt0 | exact/lexx].
apply pinsker_fun_increasing_on_p_to_1 => //.
- lra.
- by apply/andP; split; [rewrite -prob_gt0 |rewrite -prob_lt1].
- by apply/andP; split; [by rewrite lexx |apply/prob_lt1].
- by apply/andP; split => //; rewrite -prob_lt1.
Qed.

End pinsker_fun_pos.

Local Open Scope divergence_scope.
Local Open Scope variation_distance_scope.

Section Pinsker_2_bdist.
Variable R : realType.
Variables p q : {prob R}.
Variable A : finType.
Hypothesis card_A : #|A| = 2%nat.

Let P := fdist_binary card_A p (Set2.a card_A).
Let Q := fdist_binary card_A q (Set2.a card_A).

Hypothesis P_dom_by_Q : P `<< Q.

Lemma pinsker_fun_p_eq c : pinsker_fun p c q = D(P || Q) - c * d(P , Q) ^+ 2.
Proof.
pose a := Set2.a card_A. pose b := Set2.b card_A.
set pi := P a.
set pj := P b.
set qi := Q a.
set qj := Q b.
have Hpi : pi = 1 - p by rewrite /pi /P fdist_binaryxx.
have Hqi : qi = 1 - q by rewrite /qi /= fdist_binaryxx.
have Hpj : pj = p.
  by rewrite /pj /= fdist_binaryE eq_sym (negbTE (Set2.a_neq_b card_A)).
have Hqj : qj = q.
  by rewrite /qj /= fdist_binaryE eq_sym (negbTE (Set2.a_neq_b card_A)).
transitivity (D(P || Q) - c * (`| (p : R) - q | + `| (1 - p) - (1 - q) |) ^+ 2).
  rewrite /pinsker_fun /div Set2sumE -/a -/b -/pi -/pj -/qi -/qj Hpi Hpj Hqi Hqj.
  set tmp := (`| _ | + _) ^+ 2.
  have -> : tmp = 4 * ((p : R) - q) ^+ 2.
    rewrite /tmp (_ : 1 - p - (1 - q) = (q : R) - p); last by simpl; ring.
    rewrite sqrrD (distrC (q : R) (p : R)) -{3}(expr1 `|(p : R) - q|).
    by rewrite -exprS real_normK ?num_real//; ring.
  rewrite [X in _ = _ + _ - X]mulrA.
  rewrite [in X in _ = _ + _ - X](mulrC c).
  congr (_ - _).
  case/boolP : (p == 0%:pr) => [/eqP |] p0;
    first by rewrite p0 !mul0r subr0 addr0 add0r !mul1r.
  have [q0|q0] := eqVneq q 0%:pr.
    move/dominatesP : P_dom_by_Q => /(_ (Set2.b card_A)).
    rewrite -/pj -/qj Hqj q0 => /(_ erefl).
    rewrite Hpj => abs.
    have : p == 0%:pr by exact/eqP/val_inj.
    by rewrite (negbTE p0).
  have [->|p1] := eqVneq p 1%:pr.
    rewrite subrr !mul0r logM //; last first.
      by rewrite invr_gt0; exact/prob_gt0.
    by rewrite !(add0r,mul1r,addr0,sub0r).
  rewrite logM //; [| exact/prob_gt0 | by rewrite invr_gt0; exact/prob_gt0].
  rewrite logV //; last exact/prob_gt0.
  have [q1|q1] := eqVneq q 1%:pr.
    move/dominatesP : P_dom_by_Q => /(_ (Set2.a card_A)).
    rewrite -/pi -/qi Hqi q1 subrr => /(_ erefl).
    by rewrite Hpi=> ->; rewrite mul0r addr0 add0r.
  rewrite logM ?invr_gt0 ?subr_gt0 -?prob_lt1//.
  rewrite logV ?subr_gt0-?prob_lt1//.
  by rewrite addrC.
congr (_ - _ * _).
by rewrite /var_dist Set2sumE // -/pi -/pj -/qi -/qj Hpi Hpj Hqi Hqj addrC.
Qed.

Lemma Pinsker_2_inequality_bdist : (2 * ln 2)^-1 * d(P , Q) ^+ 2 <= D(P || Q).
Proof.
set lhs := _ * _.
set rhs := D(_ || _).
rewrite -subr_ge0 -pinsker_fun_p_eq.
apply pinsker_fun_pos with A card_A => //.
by rewrite lexx andbT invr_ge0 mulr_ge0// ln2_ge0.
Qed.

End Pinsker_2_bdist.

Section Pinsker_2.
Variables (A : finType) (P Q : {fdist A}).
Hypothesis card_A : #|A| = 2%nat.
Hypothesis P_dom_by_Q : P `<< Q.

Lemma Pinsker_2_inequality : (2 * ln 2)^-1 * d(P , Q) ^+ 2 <= D(P || Q).
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
  let A_ := fun b => if b then [set a | P a < Q a]
                          else [set a | Q a <= P a] in
  forall (cov : A_ 0 :|: A_ 1 = [set: A]) (dis : A_ 0 :&: A_ 1 = finset.set0),
  bipart dis cov P `<< bipart dis cov Q.
Proof.
move=> A_ cov dis; apply/dominatesP => /= b.
rewrite !ffunE => /psumr_eq0P H.
by apply: big1=> ? ?; rewrite (dominatesE P_dom_by_Q) // ?H //.
Qed.

Lemma Pinsker_inequality : (2 * ln 2)^-1 * d(P , Q) ^+ 2 <= D(P || Q).
Proof.
pose A0 := [set a | Q a <= P a].
pose A1 := [set a | P a < Q a].
pose A_ := fun b => match b with 0 => A0 | 1 => A1 end.
have cov : A_ 0 :|: A_ 1 = finset.setT.
  rewrite /= /A0 /A1.
  have -> : [set x | P x < Q x] = ~: [set x | Q x <= P x].
    by apply/setP => a; rewrite finset.in_set finset.in_setC finset.in_set ltNge.
  by rewrite finset.setUCr.
have dis : A_ 0 :&: A_ 1 = finset.set0.
  rewrite /A_ /A0 /A1.
  have -> : [set x | P x < Q x] = ~: [set x | Q x <= P x].
    by apply/setP => a; rewrite finset.in_set finset.in_setC finset.in_set ltNge.
  by rewrite finset.setICr.
pose P_A := bipart dis cov P.
pose Q_A := bipart dis cov Q.
have step1 : D(P_A || Q_A) <= D(P || Q).
  by apply partition_inequality; exact P_dom_by_Q.
suff : (2 * ln 2)^-1 * d(P , Q) ^+ 2 <= D(P_A || Q_A).
  move=> ?; apply (@le_trans _ _ (D(P_A || Q_A))) => //; exact/ge_le.
have -> : d( P , Q ) = d( P_A , Q_A ).
  rewrite /var_dist.
  transitivity (\sum_(a | a \in A0) `| P a - Q a | + \sum_(a | a \in A1) `| P a - Q a |).
    rewrite -big_union //; last by rewrite -setI_eq0 -dis /A_ finset.setIC.
    apply eq_bigl => a; by rewrite cov finset.in_set.
  transitivity (`| P_A 0 - Q_A 0 | + `| P_A 1 - Q_A 1 |).
    congr (_ + _).
    - rewrite /P_A /Q_A /bipart /= /bipart_pmf /=.
      transitivity (\sum_(a | a \in A0) (P a - Q a)).
        apply: eq_bigr => a; rewrite /A0 finset.in_set => Ha.
        by rewrite ger0_norm ?subr_ge0.
      rewrite big_split /= ger0_norm; last first.
        rewrite subr_ge0; rewrite !ffunE.
        by apply ler_sum => ?; rewrite inE.
      by rewrite -big_morph_oppr // 2!ffunE.
    - rewrite /P_A /Q_A /bipart /= !ffunE /=.
      have [A1_card | A1_card] : #|A1| = O \/ (0 < #|A1|)%nat.
        destruct (#|A1|); [tauto | by right].
      + move/eqP : A1_card; rewrite cards_eq0; move/eqP => A1_card.
        by rewrite A1_card !big_set0 subrr normr0.
      + transitivity (\sum_(a | a \in A1) - (P a - Q a)).
          apply eq_bigr => a; rewrite /A1 finset.in_set => Ha.
          by rewrite ltr0_norm // subr_lt0.
        rewrite -big_morph_oppr // big_split /= ltr0_norm; last first.
          rewrite subr_lt0; apply: ltR_sumR_support => // a.
          by rewrite /A1 finset.in_set.
        by rewrite -big_morph_oppr.
  by rewrite big_bool /= /bipart_pmf !ffunE /=.
exact/(Pinsker_2_inequality card_bool)/bipart_dominates.
Qed.

Lemma Pinsker_inequality_weak : d(P , Q) <= Num.sqrt (2 * D(P || Q)).
Proof.
rewrite -[leLHS]ger0_norm ?pos_var_dist// -sqrtr_sqr.
rewrite ler_wsqrtr// -ler_pdivrMl//.
apply: (le_trans _ Pinsker_inequality).
rewrite invfM mulrAC ler_peMr//.
  by rewrite mulr_ge0// ?invr_ge0// sqr_ge0.
rewrite invf_ge1// ?ln2_gt0//.
rewrite -[leRHS]expRK.
by rewrite ler_ln ?posrE// ?expR_gt0// ltW// expR1_gt2.
Qed.

End Pinsker.
