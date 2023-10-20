(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg all_algebra reals.
Require Import Reals.
From mathcomp Require Import Rstruct.
Require Import ssrR Reals_ext ln_facts logb Rbigop fdist proba.

(******************************************************************************)
(*    Divergence (or the Kullback-Leibler distance or relative entropy)       *)
(*                                                                            *)
(* D(P || Q) == divergence between the (finite) probability distributions P   *)
(*              and Q                                                         *)
(* Lemmas:                                                                    *)
(*   div_ge0 == divergence is non-negative                                    *)
(*   divPP   == D(P || P) = 0                                                 *)
(*   div0P   == D(P || Q) = 0 <-> P = Q                                       *)
(******************************************************************************)

Reserved Notation "'D(' P '||' Q ')' " (at level 50, P, Q at next level,
  format "'D(' P  '||'  Q ')'").

Declare Scope divergence_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.
Local Open Scope fdist_scope.

(* TODO: rename, move? *)
Section log_facts.

Lemma div_diff_ub x y : 0 <= x -> (y = 0 -> x = 0) -> 0 <= y ->
                        x * (log (y / x)) <= (y - x) * log (exp 1).
Proof.
move=> x0 yx /leR_eqVlt[/esym|] y0.
- move: (yx y0) => ->; rewrite y0 subRR 2!mul0R; exact/leRR.
- case/leR_eqVlt : x0 => [/esym ->|x0].
  + rewrite mul0R subR0; apply mulR_ge0; [exact: ltRW | exact: log_exp1_Rle_0].
  + rewrite (_ : y - x = x * (y / x - 1)); last first.
      by rewrite mulRDr mulRCA mulRV ?mulR1 ?mulRN1 //; exact/gtR_eqF.
    rewrite -mulRA; apply (leR_wpmul2l (ltRW x0)).
    by apply/log_id_cmp/mulR_gt0 => //; exact/invR_gt0.
Qed.

Lemma log_id_diff x y : 0 <= x -> (y = 0 -> x = 0) -> 0 <= y ->
  x * (log (y / x)) = (y - x) * log (exp 1) -> x = y.
Proof.
move=> Hx Hxy /leR_eqVlt[/esym|] y0 Hxy2; first by rewrite y0 Hxy.
case/leR_eqVlt : Hx => [/esym|] x0.
- move/esym : Hxy2; rewrite x0 mul0R subR0 mulR_eq0 => -[] //.
  by rewrite logexp1E => /invR_eq0/eqP; rewrite (negbTE ln2_neq0).
- apply/esym; rewrite -(@eqR_mul2l (/ x)) //; last exact/nesym/eqP/ltR_eqF/invR_gt0.
  rewrite mulVR //; last exact/gtR_eqF.
  apply log_id_eq; first by apply mulR_gt0 => //; exact: invR_gt0.
  rewrite -(@eqR_mul2l x); last exact/eqP/gtR_eqF.
  rewrite {1}(mulRC _ y) Hxy2 mulRA mulRBr; congr (_ * _).
  field; exact/eqP/gtR_eqF.
Qed.

End log_facts.

Section divergence_def.

Variables (A : finType) (P Q : {fdist A}).

Definition div := \sum_(a in A) P a * log (P a / Q a).

End divergence_def.

Notation "'D(' P '||' Q ')' " := (div P Q) : divergence_scope.

Local Open Scope divergence_scope.
Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.

Section divergence_prop.

Variables (A : finType) (P Q : {fdist A}).
Hypothesis P_dom_by_Q : P `<< Q.

Lemma div_ge0 : 0 <= D(P || Q).
Proof.
rewrite /div [X in _ <= X](_ : _ =
    - \sum_(a | a \in A) P a * (log (Q a / P a))); last first.
  rewrite big_morph_oppR; apply eq_bigr => a _; rewrite -mulRN.
  case/boolP : (P a == 0) => [/eqP ->|H0]; first by rewrite !mul0R.
  congr (_ * _).
  have Qa0 := dominatesEN P_dom_by_Q H0.
  by rewrite -logV ?Rinv_div//; apply divR_gt0; apply /RltP; rewrite -fdist_gt0.
rewrite leR_oppr oppR0.
apply (@leR_trans ((\sum_(a | a \in A) (Q a - P a)) * log (exp 1))).
  rewrite (big_morph _ (morph_mulRDl _) (mul0R _)).
  apply leR_sumR => a _; apply div_diff_ub => //.
  by move/dominatesP : P_dom_by_Q; exact.
rewrite -{1}(mul0R (log (exp 1))); apply (leR_wpmul2r log_exp1_Rle_0).
by rewrite big_split /= -big_morph_oppR !FDist.f1 addR_opp subRR; exact/leRR.
Qed.

Lemma divPP : D(Q || Q) = 0.
Proof.
rewrite /div; apply big1 => a _.
case/boolP : (Q a == 0) => [/eqP ->|H0]; first by rewrite mul0R.
by rewrite divRR // /log /Log ln_1 div0R mulR0.
Qed.

Lemma div0P : D(P || Q) = 0 <-> P = Q.
Proof.
split => [HPQ | ->]; last by rewrite divPP.
apply/fdist_ext => a.
apply log_id_diff => //; first by move/dominatesP : P_dom_by_Q; exact.
apply/esym; move: a (erefl true); apply leR_sumR_eq.
- move=> a' _; apply div_diff_ub => //; move/dominatesP : P_dom_by_Q; exact.
- transitivity 0; last first.
    rewrite -{1}oppR0 -{1}HPQ big_morph_oppR.
    apply eq_bigr => a _; rewrite -mulRN.
    case/boolP : (P a == 0) => [/eqP ->| H0]; first by rewrite !mul0R.
    congr (_ * _).
    have Qa0 := dominatesEN P_dom_by_Q H0.
    by rewrite -logV ?Rinv_div//; apply divR_gt0; apply /RltP; rewrite -fdist_gt0.
  rewrite -(big_morph _ (morph_mulRDl _) (mul0R _)) big_split /=.
  by rewrite -big_morph_oppR !FDist.f1 addR_opp subRR mul0R.
Qed.

End divergence_prop.
