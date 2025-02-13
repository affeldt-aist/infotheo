(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix.
From mathcomp Require Import Rstruct reals exp.
Require Import ssr_ext ssralg_ext realType_ln num_occ.
Require Import fdist entropy types jtypes divergence conditional_divergence.
Require Import error_exponent channel_code channel success_decode_bound.

(**md**************************************************************************)
(* # Channel coding theorem (converse part)                                   *)
(*                                                                            *)
(* The main theorem is `channel_coding_converse`.                             *)
(*                                                                            *)
(* Documented in:                                                             *)
(* - Reynald Affeldt, Manabu Hagiwara, and Jonas Sénizergues. Formalization   *)
(*   of Shannon's theorems. Journal of Automated Reasoning, 53(1):63--103,    *)
(*   2014                                                                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope channel_code_scope.
Local Open Scope channel_scope.
Local Open Scope entropy_scope.
Local Open Scope tuple_ext_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope types_scope.
Local Open Scope divergence_scope.
Local Open Scope ring_scope.

Import Order.POrderTheory Num.Theory GRing.Theory.

Section channel_coding_converse_intermediate_lemma.
Let R := Rdefinitions.R.
Variables (A B : finType) (W : `Ch*(A, B)).
Variable minRate : R.
Hypothesis HminRate : minRate > capacity W.
Hypothesis set_of_I_has_ubound :
  classical_sets.has_ubound (fun y => exists P, `I(P, W) = y)(*TODO*).

Let Anot0 : (0 < #|A|)%nat. Proof. by case: W. Qed.

Let Bnot0 : (0 < #|B|)%nat.
Proof. case/card_gt0P : Anot0 => a _; exact: (fdist_card_neq0 (W a)). Qed.

Lemma channel_coding_converse_gen : exists Delta, 0 < Delta /\ forall n',
  let n := n'.+1 in forall (M : finType) (c : code A B M n), (0 < #|M|)%nat ->
    minRate <= CodeRate c ->
      scha(W, c) <= n.+1%:R ^+ (#|A| + #|A| * #|B|) * 2 `^ (- n%:R * Delta).
Proof.
move: error_exponent_bound => /(_ _ _ Bnot0 W _ HminRate set_of_I_has_ubound).
case => Delta [Delta_pos HDelta].
exists Delta; split => // n' n M c Mnot0 H.
apply: (le_trans (success_bound W Mnot0 c)).
set Pmax := [arg max_(P > _) _]%O.
set tc :=  _.-typed_code _.
rewrite exprD -mulrA.
apply ler_wpM2l.
  by rewrite exprn_ge0//.
apply: (le_trans (typed_success_bound W Mnot0 (Pmax.-typed_code c))).
apply ler_wpM2l.
  by rewrite exprn_ge0//.
set Vmax := [arg max_(V > _) _]%O.
rewrite /success_factor_bound /exp_cdiv.
case : ifP => Hcase; last by rewrite mul0r powR_ge0.
rewrite -powRD; last by rewrite pnatr_eq0 implybT.
rewrite ler_powR ?ler1n//.
rewrite -mulrDr 2!mulNr.
rewrite lerNr opprK; apply/ler_wpM2l; first exact/ler0n.
have {}Hcase : Pmax |- Vmax << W.
  move=> a Hp; apply/dominatesP => b /eqP Hw.
  move/forallP : Hcase.
  by move/(_ a)/implyP/(_ Hp)/forallP/(_ b)/implyP/(_ Hw)/eqP.
apply (le_trans (HDelta Pmax Vmax Hcase)) => /=.
rewrite lerD2l//.
(* TODO: lemma *)
rewrite Order.TotalTheory.ge_max.
apply/andP; split.
  by rewrite Order.TotalTheory.le_max lexx.
rewrite Order.TotalTheory.le_max.
apply/orP; right.
by rewrite lerB//.
Qed.

End channel_coding_converse_intermediate_lemma.

Section channel_coding_converse.
Let R := Rdefinitions.R.
Variables (A B : finType) (W : `Ch*(A, B)).
Variable minRate : R.
Hypothesis minRate_cap : minRate > capacity W.
Hypothesis set_of_I_has_ubound :
  classical_sets.has_ubound (fun y => exists P, `I(P, W) = y).

Variable epsilon : R. (* TODO: use posnum *)
Hypothesis eps_gt0 : 0 < epsilon.

Theorem channel_coding_converse : exists n0,
  forall n M (c : code A B M n),
    (0 < #|M|)%nat -> n0 < n%:R :> R -> minRate <= CodeRate c -> scha(W, c) < epsilon.
Proof.
case: (channel_coding_converse_gen minRate_cap set_of_I_has_ubound) => Delta [Delta_pos HDelta].
pose K := (#|A| + #|A| * #|B|)%nat.
pose n0 := 2 ^+ K * K.+1`!%:R / ((Delta * ln 2) ^+ K.+1) / epsilon.
exists n0 => n M c HM n0_n HminRate.
have Rlt0n : 0 < n%:R :> R.
  apply: (lt_trans _ n0_n).
  rewrite /n0.
  rewrite mulr_gt0// ?invr_gt0//.
  rewrite -mulrA mulr_gt0 ?exprn_gt0//.
  rewrite divr_gt0// ?ltr0n ?fact_gt0//.
  rewrite exprn_gt0//.
  by rewrite mulr_gt0// ln_gt0// ltr1n.
destruct n as [|n'].
  by rewrite ltxx in Rlt0n.
set n := n'.+1.
apply: (@le_lt_trans _ _ (n.+1%:R ^+ K * 2 `^ (- n%:R * Delta))).
  exact: HDelta.
move: (n0_n).
rewrite -[in X in X -> _](@ltr_pM2l _ n%:R^-1) ?invr_gt0 ?ltr0n//.
rewrite mulVf ?pnatr_eq0//.
rewrite -[in X in X -> _](@ltr_pM2l _ epsilon)// mulr1.
apply: le_lt_trans.
rewrite /n0.
rewrite [in X in _ <= X]mulrC.
rewrite -6![in X in _ <= X]mulrA.
rewrite mulVf ?gt_eqF// mulr1.
rewrite [leRHS]mulrC.
rewrite -2!mulrA.
set aux := _%:R * (_ * _).
have aux_gt0 : 0 < aux.
  rewrite mulr_gt0 ?ltr0n ?fact_gt0// divr_gt0//.
  by rewrite invr_gt0// exprn_gt0// mulr_gt0// ln_gt0 ?ltr1n.
apply (@le_trans _ _ ((n.+1%:R / n%:R) ^+ K * aux)); last first.
  rewrite ler_pM2r//.
  rewrite lerXn2r ?nnegrE ?divr_ge0//.
  rewrite ler_pdivrMr ?ltr0n//.
  by rewrite -[in leRHS]mulrC mulr_natr mulr2n -natr1 lerD2l ler1n.
rewrite expr_div_n -mulrA ler_wpM2l//.
- by rewrite exprn_ge0.
- rewrite -lef_pV2 ?posrE ?powR_gt0//; last first.
    by rewrite mulr_gt0// invr_gt0 exprn_gt0.
  rewrite -powRN mulNr opprK.
  have nDeltaln2 : 0 < n%:R * Delta * ln 2.
    by rewrite mulr_gt0// ?ln_gt0 ?ltr1n// mulr_gt0//.
  rewrite /exp.powR(* TODO *) pnatr_eq0/=.
  apply/ltW.
  apply: (le_lt_trans _ (exp_strict_lb K.+1 nDeltaln2)) => {nDeltaln2}.
  apply/eqW.
  rewrite invfM invrK.
  rewrite /aux.
  rewrite !invfM.
  rewrite mulrCA mulrC.
  congr (_ / _).
  rewrite invrK.
  rewrite mulrCA.
  rewrite invrK -exprSr.
  rewrite -exprMn_comm//; last by rewrite /GRing.comm [in RHS]mulrC.
  by rewrite mulrC mulrA.
Qed.

End channel_coding_converse.
