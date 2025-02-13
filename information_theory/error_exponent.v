(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum lra ring.
From mathcomp Require Import Rstruct reals classical_sets topology normedtype.
From mathcomp Require Import sequences exp.
Require Import ssr_ext bigop_ext realType_ext realType_ln fdist.
Require Import entropy channel_code channel divergence conditional_divergence.
Require Import variation_dist pinsker.

(**md**************************************************************************)
(* # Error exponent bound                                                     *)
(*                                                                            *)
(* Documented in:                                                             *)
(* - Reynald Affeldt, Manabu Hagiwara, and Jonas Sénizergues. Formalization   *)
(*   of Shannon's theorems. Journal of Automated Reasoning, 53(1):63--103,    *)
(*   2014                                                                     *)
(*                                                                            *)
(* Main lemmas:                                                               *)
(* - Distance from the output entropy of one channel to another               *)
(*   (`out_entropy_dist_ub`)                                                  *)
(* - Distance from the joint entropy of one channel to another                *)
(*   (`joint_entropy_dist_ub`)                                                *)
(* - Distance from the mutual information of one channel to another           *)
(*   (`mut_info_dist_ub`)                                                     *)
(* - Intermediate step in the proof of the converse of the channel coding     *)
(*   theorem (`error_exponent_bound`)                                         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope divergence_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope channel_scope.
Local Open Scope reals_ext_scope.
Local Open Scope ring_scope.

Import Order.TTheory GRing.Theory Num.Theory.

Section mutinfo_distance_bound.
Let R := Rdefinitions.R.
Variables (A B : finType) (V W : `Ch(A, B)) (P : {fdist A}).
Hypothesis V_dom_by_W : P |- V << W.
Hypothesis cdiv_ub : D(V || W | P) <= (expR (-2) ^+ 2) / 2.

Let cdiv_bounds : 0 <= Num.sqrt (2 * D(V || W | P)) <= expR (-2).
Proof.
apply/andP; split.
  by rewrite sqrtr_ge0.
rewrite -(@ler_pXn2r _ 2) ?nnegrE ?expR_ge0 ?sqrtr_ge0//.
rewrite -(@ler_pM2r _ (2^-1)) ?invr_gt0//.
rewrite sqr_sqrtr; last by rewrite mulr_ge0// cdiv_ge0.
by rewrite mulrAC divff ?mul1r// pnatr_eq0.
Qed.

Local Open Scope variation_distance_scope.

Lemma out_entropy_dist_ub : `| `H(P `o V) - `H(P `o W) | <=
  (ln 2)^-1 * #|B|%:R * - xlnx (Num.sqrt (2 * D(V || W | P))).
Proof.
rewrite 2!xlnx_entropy.
rewrite -mulrN -mulrDr normrM gtr0_norm; last first.
  by rewrite invr_gt0// ln_gt0// ltr1n.
rewrite -mulrA ler_pM2l; last first.
  by rewrite invr_gt0// ln_gt0// ltr1n.
rewrite opprK big_morph_oppr -big_split /=.
apply: le_trans; first exact: ler_norm_sum.
rewrite -sum1_card.
rewrite natr_sum.
rewrite [leRHS]big_distrl/=.
apply: ler_sum => b _.
rewrite mul1r.
rewrite addrC.
apply: Rabs_xlnx => //.
  by apply/andP; split.
  by apply/andP; split.
rewrite 2!fdist_outE big_morph_oppr -big_split /=.
apply: le_trans; first exact: ler_norm_sum.
apply: (@le_trans _ _ (d((P `X V), (P `X W)))).
- rewrite /var_dist /=.
  apply (@le_trans _ _ (\sum_a \sum_b `| ((P `X V)) (a, b) - ((P `X W)) (a, b) | )); last first.
    by apply/eqW; rewrite pair_bigA /=; apply eq_bigr => -[].
  apply: ler_sum => a _.
  rewrite (bigD1 b) //= distrC -[X in X <= _]addr0.
  rewrite 2!fdist_prodE /= !(mulrC (P a)).
  by rewrite lerD2l sumr_ge0//.
- rewrite cdiv_is_div_joint_dist => //.
  exact/Pinsker_inequality_weak/dominates_prodl.
Qed.

Lemma joint_entropy_dist_ub : `| `H(P , V) - `H(P , W) | <=
  (ln 2)^-1 * #|A|%:R * #|B|%:R * - xlnx (Num.sqrt (2 * D(V || W | P))).
Proof.
rewrite 2!xlnx_entropy.
rewrite -mulrN -mulrDr normrM gtr0_norm; last first.
  by rewrite invr_gt0// ln_gt0 ?ltr1n.
rewrite -2!mulrA ler_pM2l//; last first.
  by rewrite invr_gt0// ln_gt0// ltr1n.
rewrite opprK big_morph_oppr -big_split /=.
apply: le_trans; first exact: ler_norm_sum.
rewrite -(sum1_card B).
rewrite natr_sum.
rewrite [in leRHS]big_distrl/=.
under [in leRHS]eq_bigr do rewrite mul1r.
rewrite -(sum1_card A).
rewrite natr_sum.
rewrite [in leRHS]big_distrl/=.
under [in leRHS]eq_bigr do rewrite mul1r.
rewrite pair_bigA/=.
apply: ler_sum; case => a b _; rewrite addrC /=.
apply: Rabs_xlnx => //.
  by rewrite FDist.ge0//=.
  by rewrite FDist.ge0//=.
apply: (@le_trans _ _ (d(P `X V, P `X W))).
- by rewrite /var_dist (bigD1 (a, b)) //= distrC ler_wpDr// sumr_ge0.
- rewrite cdiv_is_div_joint_dist => //.
  exact/Pinsker_inequality_weak/dominates_prodl.
Qed.

Lemma mut_info_dist_ub : `| `I(P, V) - `I(P, W) | <=
  (ln 2)^-1 * (#|B|%:R + #|A|%:R * #|B|%:R) *
  - xlnx (Num.sqrt (2 * D(V || W | P))).
Proof.
rewrite /mutual_info_chan.
rewrite (_ : _ - _ =
  `H(P `o V) - `H(P `o W) + (`H(P, W) - `H(P, V))); last by field.
apply: le_trans; first exact: ler_normD.
rewrite -mulrA mulrDl mulrDr lerD//.
- by rewrite mulrA; apply out_entropy_dist_ub.
- by rewrite distrC 2!mulrA; apply joint_entropy_dist_ub.
Qed.

End mutinfo_distance_bound.

Import numFieldTopology.Exports.
Import numFieldNormedType.Exports.

Section error_exponent_lower_bound.
Let R := Rdefinitions.R.
Variables A B : finType.
Hypothesis Bnot0 : (0 < #|B|)%nat.
Variables (W : `Ch(A, B)) (minRate : R).
Hypothesis minRate_cap : minRate > capacity W.
Hypothesis set_of_I_has_ubound :
  classical_sets.has_ubound (fun y => exists P, `I(P, W) = y).

Lemma error_exponent_bound : exists Delta, 0 < Delta /\
  forall P : {fdist A}, forall V : `Ch(A, B),
    P |- V << W ->
    Delta <= D(V || W | P) +  +| minRate - `I(P, V) |.
Proof.
set gamma :=
  (#|B|%:R + #|A|%:R * #|B|%:R)^-1 * (ln 2 * ((minRate - capacity W) / 2)).
rewrite /=.
have := @continuous_at_xlnx R 0 => /cvgrPdist_lt.
have : Num.min (expR (-2)) gamma > 0.
  rewrite lt_min expR_gt0/= mulr_gt0//.
  - by rewrite invr_gt0// ltr_wpDr ?ltr0n// mulr_ge0.
  - by rewrite mulr_gt0// ?ln2_gt0// divr_gt0// subr_gt0.
move=> /[swap] /[apply] -[]/= mu mu_gt0 mu_cond.
set x : R := Num.min (mu / 2) (expR (-2)).
have x_gt0 : 0 < x by rewrite lt_min expR_gt0 andbT divr_gt0.
have xmu : x < mu.
  by rewrite gt_min ltr_pdivrMr// ltr_pMr// ltr1n.
set Delta := Num.min ((minRate - capacity W) / 2) (x ^+ 2 / 2).
exists Delta; split.
  rewrite lt_min; apply/andP; split.
  - by rewrite divr_gt0// subr_gt0//.
  - by rewrite divr_gt0// exprn_gt0//.
move=> P V v_dom_by_w.
have [Hcase|Hcase] := leP Delta (D(V || W | P)).
  apply: (@le_trans _ _ (D(V || W | P))) => //.
  by rewrite ler_wpDr// le_max lexx.
suff HminRate : (minRate - capacity W) / 2 <= minRate - (`I(P, V)).
  clear -Hcase v_dom_by_w HminRate.
  apply (@le_trans _ _ +| minRate - `I(P, V) |); last first.
    by rewrite ler_wpDl// cdiv_ge0.
  rewrite le_max; apply/orP; right.
  by rewrite (le_trans _ HminRate)// ge_min lexx.
have : `I(P, V) <= capacity W + (ln 2)^-1 * (#|B|%:R + #|A|%:R * #|B|%:R) *
                                (- xlnx (Num.sqrt (2 * D(V || W | P)))).
  apply (@le_trans _ _ (`I(P, W) + (ln 2)^-1 * (#|B|%:R + #|A|%:R * #|B|%:R) *
                                   - xlnx (Num.sqrt (2 * D(V || W | P))))); last first.
    rewrite lerD2r//.
    apply/Rsup_ub; last exists P => //.
    split; first by exists (`I(P, W)), P.
    case: set_of_I_has_ubound => y Hy.
    by exists y => _ [Q _ <-]; apply Hy; exists Q.
  rewrite addrC -lerBlDr.
  apply (@le_trans _ _ `| `I(P, V) + - `I(P, W) |).
    by rewrite ler_norm.
  suff : D(V || W | P) <= expR (-2) ^+ 2 / 2 by apply mut_info_dist_ub.
  clear -Hcase x_gt0.
  apply/ltW/(lt_le_trans Hcase).
  apply (@le_trans _ _ (x ^+ 2 / 2)).
    by rewrite ge_min lexx orbT.
  rewrite ler_wpM2r ?invr_ge0// lerXn2r// ?nnegrE ?expR_ge0//.
  - exact: ltW.
  - by rewrite ge_min lexx orbT.
rewrite -[X in _ <= X]opprK.
rewrite -lerNr.
rewrite -(lerD2l minRate).
apply: le_trans.
suff x_gamma : - xlnx (Num.sqrt (2 * (D(V || W | P)))) <= gamma.
  rewrite opprD addrA [in leRHS]addrC -lerBlDr.
  rewrite [X in X <= _](_ : _ = - ((minRate + - capacity W) / 2)); last first.
    lra.
  rewrite lerNr opprK -mulrA mulrC.
  rewrite ler_pdivrMr ?ln2_gt0// mulrC -ler_pdivlMr; last first.
    by rewrite ltr_wpDr ?ltr0n// mulr_ge0.
  rewrite (le_trans x_gamma)//.
  by rewrite /gamma mulrC (mulrC (ln 2)).
suff x_D : xlnx x <= xlnx (Num.sqrt (2 * (D(V || W | P)))).
  rewrite lerNl (@le_trans _ _ (xlnx x))//.
  rewrite lerNl; apply/ltW.
  apply: (@lt_le_trans _ _ (Num.min (expR (-2)) gamma)).
    have /= := mu_cond x.
    rewrite sub0r normrN gtr0_norm// => /(_ xmu).
    rewrite xlnx_0 sub0r normrN.
    rewrite ltr0_norm//.
    rewrite /xlnx x_gt0.
    rewrite pmulr_rlt0//.
    rewrite (@le_lt_trans _ _ (ln (expR (-2))))//.
      by rewrite exp.ler_ln ?posrE// ?expR_gt0// ge_min lexx orbT.
    by rewrite exp.expRK ltrNl oppr0.
  by rewrite ge_min lexx orbT.
apply/ltW.
have ? : Num.sqrt (2 * D(V || W | P)) < x.
  rewrite -(@ltr_pXn2r _ 2) ?nnegrE ?sqrtr_ge0//; last exact/ltW.
  rewrite sqr_sqrtr//; last first.
    by rewrite mulr_ge0// cdiv_ge0.
  rewrite mulrC -ltr_pdivlMr //.
  apply: (lt_le_trans Hcase).
  by rewrite ge_min lexx orbT.
have xN1 : x <= expR (- 1).
  apply: (@le_trans _ _ (expR (-2))).
    by rewrite ge_min lexx orbT.
  by rewrite ler_expR lerN2 ler1n.
rewrite xlnx_sdecreasing_0_Rinv_e//.
- by rewrite sqrtr_ge0/= (le_trans _ xN1)// ltW.
- by rewrite (ltW x_gt0) xN1.
Qed.

End error_exponent_lower_bound.
