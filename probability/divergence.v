(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import Rstruct reals sequences exp.
Require Import realType_ext realType_ln fdist proba.

(**md**************************************************************************)
(* # Divergence (or the Kullback-Leibler distance or relative entropy)        *)
(*                                                                            *)
(* ```                                                                        *)
(* D(P || Q) == divergence between the (finite) probability distributions P   *)
(*              and Q                                                         *)
(* ```                                                                        *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(* ```                                                                        *)
(*   div_ge0 == divergence is non-negative                                    *)
(*     divPP == D(P || P) = 0                                                 *)
(*     div0P == D(P || Q) = 0 <-> P = Q                                       *)
(* ```                                                                        *)
(******************************************************************************)

Reserved Notation "'D(' P '||' Q ')' " (at level 50, P, Q at next level,
  format "'D(' P  '||'  Q ')'").

Declare Scope divergence_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import Order.POrderTheory GRing.Theory Num.Theory.

(* TODO: rename, move? *)
Section log_facts.
Context {R : realType}.

Lemma div_diff_ub x y : 0 <= x -> (y = 0 -> x = 0) -> 0 <= y ->
                        x * (log (y / x)) <= (y - x) * log (expR 1) :> R.
Proof.
move=> x0 yx; rewrite le_eqVlt => /predU1P[/esym|] y0.
- by rewrite y0 yx// subrr 2!mul0r.
- move: x0; rewrite le_eqVlt => /predU1P[/esym ->|x0].
  + rewrite mul0r subr0 mulr_ge0//; [exact: ltW | ].
    by rewrite log_exp1_Rle_0.
  + rewrite (_ : y - x = x * (y / x - 1)); last first.
      by rewrite mulrDr mulrCA mulfV ?gt_eqF// mulr1 mulrN1.
    rewrite -mulrA; apply (ler_wpM2l (ltW x0)).
    by rewrite log_id_cmp// divr_gt0.
Qed.

Lemma log_id_eq x : 0 < x -> log x = (x - 1) * log (expR 1) -> x = 1 :> R.
Proof.
move=> Hx'; rewrite logexp1E.
move=> /(congr1 (fun x => x * ln 2)).
rewrite -!mulrA mulVf// ?gt_eqF ?ln2_gt0//.
by rewrite !mulr1; exact: ln_id_eq.
Qed.

Lemma log_id_diff x y : 0 <= x -> (y = 0 -> x = 0) -> 0 <= y ->
  x * (log (y / x)) = (y - x) * log (expR 1) -> x = y :> R.
Proof.
move=> Hx Hxy; rewrite le_eqVlt => /predU1P[/esym|] y0 Hxy2; first by rewrite y0 Hxy.
move: Hx; rewrite le_eqVlt => /predU1P[/esym|] x0.
- move/esym : Hxy2; rewrite x0 mul0r subr0 => /eqP.
  rewrite mulf_eq0 => /predU1P[//|/eqP].
  rewrite logexp1E => /eqP.
  by rewrite gt_eqF// invr_gt0// ln2_gt0.
- apply/esym/divr1_eq.
  apply: log_id_eq; first by rewrite divr_gt0.
  move: Hxy2.
  move/(congr1 (fun z => x^-1 * z)).
  rewrite mulrA mulVf ?gt_eqF// mul1r => ->.
  by rewrite mulrA mulrBr mulVf ?gt_eqF// (mulrC _ y).
Qed.

End log_facts.

Section divergence_def.
Context {R : realType}.
Variables (A : finType) (P Q : R.-fdist A).

Definition div : R^o := \sum_(a in A) P a * log (P a / Q a).

End divergence_def.

(* TODO: rename, move *)
Lemma leR_sumR_eq {R : realType} (A : finType) (f g : A -> R) (P : pred A) :
   (forall a, P a -> f a <= g a) ->
   \sum_(a | P a) g a = \sum_(a | P a) f a ->
   (forall a, P a -> g a = f a).
Proof.
move=> H1 H2 i Hi; apply/eqP; rewrite -subr_eq0; apply/eqP.
move: i Hi; apply: psumr_eq0P.
  by move=> i Pi; rewrite Num.Theory.subr_ge0 H1.
by rewrite big_split/= sumrN; apply/eqP; rewrite subr_eq0 H2.
Qed.

Notation "'D(' P '||' Q ')' " := (div P Q) : divergence_scope.

Local Open Scope divergence_scope.
Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.

Section divergence_prop.
Context {R : realType}.
Variables (A : finType) (P Q : R.-fdist A).
Hypothesis P_dom_by_Q : P `<< Q.

Lemma div_ge0 : 0 <= D(P || Q).
Proof.
rewrite /div [X in _ <= X](_ : _ =
    - \sum_(a | a \in A) P a * (log (Q a / P a))); last first.
  rewrite -sumrN; apply: eq_bigr => a _; rewrite -mulrN.
  case/boolP : (P a == 0) => [/eqP ->|H0]; first by rewrite !mul0r.
  congr (_ * _).
  have Qa0 := dominatesEN P_dom_by_Q H0.
  by rewrite -logV ?invf_div// divr_gt0//; apply/fdist_gt0.
rewrite lerNr oppr0.
apply (@le_trans _ _ ((\sum_(a | a \in A) (Q a - P a)) * log (expR 1))).
  rewrite big_distrl/=.
  apply: ler_sum => a _; apply: div_diff_ub => //.
  - by move/dominatesP : P_dom_by_Q; exact.
rewrite -[leRHS](mul0r (log (expR 1))) ler_wpM2r// ?log_exp1_Rle_0//.
by rewrite big_split /= sumrN !FDist.f1 subrr.
Qed.

Lemma divPP : D(Q || Q) = 0.
Proof.
rewrite /div; apply big1 => a _.
case/boolP : (Q a == 0) => [/eqP ->|H0]; first by rewrite mul0r.
by rewrite divff // log1 mulr0.
Qed.

Lemma div0P : D(P || Q) = 0 <-> P = Q.
Proof.
split => [HPQ | ->]; last by rewrite divPP.
apply/fdist_ext => a.
apply log_id_diff => //.
- by move/dominatesP : P_dom_by_Q; exact.
- apply/esym; move: a (erefl true); apply leR_sumR_eq.
  + move=> a' _; apply div_diff_ub => //.
    * by move/dominatesP : P_dom_by_Q; exact.
  + apply: (@trans_eq _ _ 0%R); last first.
      rewrite -{1}oppr0 -{1}HPQ -sumrN.
      apply eq_bigr => a _; rewrite -mulrN.
      case/boolP : (P a == 0) => [/eqP ->| H0]; first by rewrite !mul0r.
      congr (_ * _).
      have Qa0 := dominatesEN P_dom_by_Q H0.
      by rewrite -logV ?invf_div// divr_gt0// -fdist_gt0.
    by rewrite -big_distrl/= big_split/= sumrN !FDist.f1 subrr mul0r.
Qed.

End divergence_prop.
