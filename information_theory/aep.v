(* infotheo: information theory and error-correcting codes in Coq               *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later              *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg matrix.
From mathcomp Require boolp.
Require Import Reals.
From mathcomp Require Import Rstruct.
Require Import ssrR Reals_ext ssr_ext ssralg_ext logb Rbigop fdist proba.
Require Import entropy.

(******************************************************************************)
(*              Asymptotic Equipartition Property (AEP)                       *)
(*                                                                            *)
(*         Lemma V_mlog == Var(-log P) = E((-log P)^2) - H(P)                 *)
(* Definition aep_bound == constant used in the statement of AEP              *)
(*            Lemma aep == AEP                                                *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.
Local Open Scope vec_ext_scope.

Section mlog_prop.
Variables (A : finType) (P : fdist A).
Local Open Scope R_scope.

Definition aep_sigma2 := `E ((--log P) `^2) - (`H P)^2.

Lemma aep_sigma2E : aep_sigma2 = \sum_(a in A) P a * (log (P a))^2 - (`H P)^2.
Proof.
rewrite /aep_sigma2 /Ex [in LHS]/mlog_RV /comp_RV.
by under eq_bigr do rewrite mulRC /ambient_dist sq_RV_pow2-mulRR Rmult_opp_opp mulRR.
Qed.
Lemma V_mlog : `V (--log P) = aep_sigma2.
Proof.
rewrite aep_sigma2E /Var E_trans_RV_id_rem -entropy_Ex E_trans_add_RV E_sub_RV -scaler_RV_natr.
rewrite !E_scaler_RV -INRE !entropy_Ex mulRC mulRR -addRR -addR_opp oppRD.
rewrite -!addRA -(addRC (`E --log P ^ 2)) addR_opp subRR addR0 addR_opp.
under eq_bigr=> i do rewrite mulRC -mulRR -(Rmult_opp_opp (log (P i)) (log (P i))) mulRR.
rewrite -/(Ex _ _) /mlog_RV.
congr (`E _ - _); apply boolp.funext=> u /=.
by rewrite sq_RV_pow2.
Qed.

Lemma aep_sigma2_ge0 : 0 <= aep_sigma2.
Proof.
by rewrite -V_mlog /Var; apply Ex_ge0 => ?; rewrite sq_RV_pow2; exact: pow_even_ge0.
Qed.

End mlog_prop.

Definition sum_mlog_prod A (P : fdist A) n : {RV (P `^ n) -> R} :=
  (fun t => \sum_(i < n) - log (P t ``_ i))%R.

Arguments sum_mlog_prod {A} _ _.

Lemma sum_mlog_prod_sum_map_mlog A (P : fdist A) n :
  sum_mlog_prod P n.+1 \=sum (\row_(i < n.+1) --log P).
Proof.
elim : n => [|n IH].
- move: (@sum_n_1 A P (\row_i --log P)).
  set mlogP := cast_rV1_fun_rV1 _.
  move => HmlogP.
  set mlogprodP := @sum_mlog_prod _ _ 1.
  suff -> : mlogprodP = mlogP by [].
  rewrite /mlogprodP /mlogP /sum_mlog_prod /cast_rV1_fun_rV1 /= mxE /=.
  by rewrite boolp.funeqE => ta; rewrite big_ord_recl big_ord0 addR0.
- rewrite [X in _ \=sum X](_ : _ =
      row_mx (\row_(i < 1) (--log P)) (\row_(i < n.+1) --log P)); last first.
    apply/rowP => b; rewrite !mxE; case: splitP.
      move=> a; rewrite {a}(ord1 a) => _; by rewrite mxE.
    move=> k _; by rewrite mxE.
  apply: (sum_n_cons IH _) => /= ta.
  rewrite /sum_mlog_prod /= big_ord_recl /=; congr (_ + _)%R.
  apply eq_bigr => i _; by rewrite mxE.
Qed.

Section aep_k0_constant.

Variables (A : finType) (P : {fdist A}).

Definition aep_bound epsilon := (aep_sigma2 P / epsilon ^ 3)%R.

Lemma aep_bound_ge0 e (_ : 0 < e) : 0 <= aep_bound e.
Proof. apply divR_ge0; [exact: aep_sigma2_ge0 | exact/pow_lt]. Qed.

Lemma aep_bound_decreasing e e' : 0 < e' <= e -> aep_bound e <= aep_bound e'.
Proof.
case=> Oe' e'e.
apply leR_wpmul2l; first exact: aep_sigma2_ge0.
apply leR_inv => //; first exact/pow_lt.
apply pow_incr => //; split; [exact/ltRW | exact/e'e ].
Qed.

End aep_k0_constant.

Section AEP.

Variables (A : finType) (P : {fdist A}) (n : nat) (epsilon : R).
Hypothesis Hepsilon : 0 < epsilon.

Lemma aep : aep_bound P epsilon <= n.+1%:R ->
  Pr (P `^ n.+1) [set t | (0 <b P `^ n.+1 t) &&
    (`| (--log (P `^ n.+1) `/ n.+1) t - `H P | >b= epsilon) ] <= epsilon.
Proof.
move=> Hbound.
apply (@leR_trans (aep_sigma2 P / (n.+1%:R * epsilon ^ 2))); last first.
  rewrite /aep_bound in Hbound.
  apply (@leR_wpmul2r (epsilon / n.+1%:R)) in Hbound; last first.
    apply divR_ge0; [exact/ltRW/Hepsilon | exact/ltR0n].
  rewrite [in X in _ <= X]mulRCA mulRV ?INR_eq0' // ?mulR1 in Hbound.
  apply/(leR_trans _ Hbound)/Req_le; field.
  by split; [by rewrite INR_eq0 | exact/eqP/gtR_eqF].
have Hsum := sum_mlog_prod_sum_map_mlog P n.
have H1 : forall k i, `E ((\row_(i < k.+1) --log P) ``_ i) = `H P.
  by move=> k i; rewrite mxE entropy_Ex.
have H2 : forall k i, `V ((\row_(i < k.+1) --log P) ``_ i) = aep_sigma2 P.
  by move=> k i; rewrite mxE V_mlog.
have {H1 H2} := (wlln (H1 n) (H2 n) Hsum Hepsilon).
move/(leR_trans _); apply.
apply/Pr_incl/subsetP => ta; rewrite 2!inE => /andP[H1].
set X := (X in X >b= _); set Y := (Y in ((_ <= Y)%O)).
suff -> : X = Y by move/leRP/RleP.
rewrite /X /Y /comp_RV /trans_min_RV.
rewrite /scalel_RV /GRing.add /GRing.mul /topology.cst /=.
congr `| _ * _ + _ |.
rewrite /sum_mlog_prod /mlog_RV TupleFDist.dE log_prodR_sumR_mlog //.
apply: (prodR_gt0_inv (FDist.ge0 P)).
by move: H1; rewrite TupleFDist.dE => /ltRP.
Qed.

End AEP.
