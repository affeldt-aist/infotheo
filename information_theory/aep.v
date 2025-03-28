(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix.
From mathcomp Require boolp.
From mathcomp Require Import reals exp Rstruct.
Require Import realType_ext ssr_ext bigop_ext ssralg_ext realType_ln.
Require Import fdist proba entropy.

(**md**************************************************************************)
(* # Asymptotic Equipartition Property (AEP)                                  *)
(*                                                                            *)
(* The AEP lemma is `aep`.                                                    *)
(*                                                                            *)
(* ```                                                                        *)
(*      aep_sigma2 := `E ((`-- (`log P)) `^2) - (`H P)^+2                     *)
(*   sum_mlog_prod == TODO                                                    *)
(*       aep_bound == constant used in the statement of AEP                   *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.
Local Open Scope vec_ext_scope.

Import Order.POrderTheory GRing.Theory Num.Theory.

Section mlog_prop.
Context {R : realType}.
Variables (A : finType) (P : R.-fdist A).

Definition aep_sigma2 : R := `E ((`-- (`log P)) `^2) - (`H P)^+2.

Lemma aep_sigma2E : aep_sigma2 = \sum_(a in A) P a * (log (P a))^+2 - (`H P)^+2.
Proof.
rewrite /aep_sigma2 /Ex [in LHS]/log_RV /sq_RV /comp_RV.
by under eq_bigr do rewrite mulrC /ambient_dist expr2 mulrNN -expr2.
Qed.

Lemma V_mlog : `V (`-- (`log P)) = aep_sigma2.
Proof.
rewrite aep_sigma2E /Var E_trans_RV_id_rem -entropy_Ex.
transitivity
    (\sum_(a in A) ((- log (P a))^+2 * P a - 2 * `H P * - log (P a) * P a +
                    `H P ^+ 2 * P a))%R.
  apply eq_bigr => a _.
  rewrite /scalel_RV /log_RV /opp_RV /trans_add_RV /sq_RV /comp_RV /= /sub_RV.
  by rewrite /ambient_dist -!mulrBl -mulrDl.
rewrite big_split /= big_split /= -big_distrr /= (FDist.f1 P) mulr1.
rewrite (_ : \sum_(a in A) - _ = - (2 * `H P ^+ 2))%R; last first.
  rewrite -{1}big_morph_oppr; congr (- _)%R.
  rewrite [X in X = _](_ : _ =
    \sum_(a in A) (2 * `H P) * (- (P a * log (P a))))%R; last first.
    by apply eq_bigr => a _; rewrite (mulrC (P a)) -[in RHS]mulNr mulrA.
  rewrite -big_distrr [in LHS]/= -{1}big_morph_oppr.
  by rewrite -/(entropy P) expr2 mulrA.
set s := ((\sum_(a in A ) _)%R in LHS).
rewrite (_ : \sum_(a in A) _ = s)%R; last first.
  by apply eq_bigr => a _; rewrite sqrrN mulrC.
by rewrite (mulr_natl _ 2) mulr2n opprD addrA subrK.
Qed.

Lemma aep_sigma2_ge0 : 0 <= aep_sigma2.
Proof. by rewrite -V_mlog /Var; apply: Ex_ge0 => ?; exact: sq_RV_ge0. Qed.
End mlog_prop.

Definition sum_mlog_prod {R : realType} (A : finType) (P : R.-fdist A) n :
    {RV ((P `^ n)%fdist)-> R} :=
  (fun t => \sum_(i < n) - log (P (t ``_ i)))%R.

Arguments sum_mlog_prod {R} {A} _ _.

Lemma sum_mlog_prod_sum_map_mlog {R : realType} (A : finType) (P : R.-fdist A) n :
  sum_mlog_prod P n.+1 \=sum (\row_(i < n.+1) `-- (`log P)).
Proof.
elim : n => [|n IH].
- move: (@sum_n_1 _ A P (\row_i `-- (`log P))).
  set mlogP := cast_fun_rV10 _.
  move => HmlogP.
  set mlogprodP := @sum_mlog_prod _ _ _ 1.
  suff -> : mlogprodP = mlogP by [].
  rewrite /mlogprodP /mlogP /sum_mlog_prod /cast_fun_rV10 /= mxE /=.
  by rewrite boolp.funeqE => ta; rewrite big_ord_recl big_ord0 addr0.
- rewrite [X in _ \=sum X](_ : _ =
      row_mx (\row_(i < 1) (`-- (`log P))) (\row_(i < n.+1) `-- (`log P))); last first.
    apply/rowP => b; rewrite !mxE; case: splitP.
      by move=> a; rewrite {a}(ord1 a) => _; rewrite mxE.
    by move=> k _; rewrite mxE.
  apply: (sum_n_cons IH _) => /= ta.
  rewrite /sum_mlog_prod /= big_ord_recl /=; congr (_ + _)%R.
  by apply eq_bigr => i _; rewrite mxE.
Qed.

Section aep_k0_constant.
Context {R : realType}.
Variables (A : finType) (P : R.-fdist A).

Definition aep_bound epsilon : R := (aep_sigma2 P / epsilon ^+ 3)%R.

Lemma aep_bound_ge0 e (_ : 0 < e) : 0 <= aep_bound e.
Proof. by apply divr_ge0; [exact: aep_sigma2_ge0 | apply/exprn_ge0/ltW]. Qed.

Lemma aep_bound_decreasing e e' : 0 < e' <= e -> aep_bound e <= aep_bound e'.
Proof.
case/andP=> Oe' e'e.
apply ler_wpM2l; first exact: aep_sigma2_ge0.
rewrite lef_pV2 ?posrE; [|apply/exprn_gt0..] => //; last first.
  by rewrite (lt_le_trans _ e'e).
by rewrite lerXn2r// ?nnegrE ltW// (lt_le_trans _ e'e).
Qed.

End aep_k0_constant.

Section AEP.
Context {R : realType}.
Variables (A : finType) (P : R.-fdist A) (n : nat) (epsilon : R).
Hypothesis Hepsilon : 0 < epsilon.

Lemma aep : aep_bound P epsilon <= n.+1%:R ->
  Pr (P `^ n.+1)%fdist [set t | (0 < (P `^ n.+1)%fdist t) &&
    (`| (`-- (`log (P `^ n.+1)%fdist) `/ n.+1) t - `H P | >= epsilon) ] <= epsilon.
Proof.
move=> Hbound.
apply (@le_trans _ _ (aep_sigma2 P / (n.+1%:R * epsilon ^+ 2))); last first.
  rewrite /aep_bound in Hbound.
  apply (@ler_wpM2r _ (epsilon / n.+1%:R)) in Hbound; last first.
    by rewrite divr_ge0// ltW.
  rewrite [in X in _ <= X]mulrCA mulfV ?pnatr_eq0// ?mulr1 in Hbound.
  apply/(le_trans _ Hbound).
  rewrite [in leRHS]mulrA [in leRHS]exprSr [in leRHS]invfM.
  rewrite -3![in leRHS]mulrA  (mulrA epsilon^-1) mulVf ?gt_eqF// mul1r.
  by rewrite (mulrC (n.+1%:R)) invfM.
have Hsum := sum_mlog_prod_sum_map_mlog P n.
have H1 k i : `E ((\row_(i < k.+1) `-- (`log P)) ``_ i) = `H P.
  by rewrite mxE entropy_Ex.
have H2 k i : `V ((\row_(i < k.+1) `-- (`log P)) ``_ i) = aep_sigma2 P.
  by rewrite mxE V_mlog.
have {H1 H2} := (wlln (H1 n) (H2 n) Hsum Hepsilon).
move/(le_trans _); apply.
apply/subset_Pr/subsetP => ta; rewrite 2!inE => /andP[H1].
rewrite /sum_mlog_prod [`-- (`log _)]lock /= -lock /scalel_RV /log_RV /opp_RV/=.
rewrite fdist_rVE log_prodr_sumr_mlog //.
apply/prod_gt0_inv.
  by move=> x; exact: FDist.ge0.
by move: H1; rewrite fdist_rVE.
Qed.

End AEP.
