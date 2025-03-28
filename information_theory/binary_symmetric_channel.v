(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix lra.
From mathcomp Require Import mathcomp_extra classical_sets Rstruct reals.
Require Import ssr_ext ssralg_ext bigop_ext realType_ext realType_ln.
Require Import fdist entropy binary_entropy_function channel hamming.
Require Import channel_code pproba.

(**md**************************************************************************)
(* # Capacity of the binary symmetric channel                                 *)
(*                                                                            *)
(* This file shows that the capacity of a BSC is 1 - H p                      *)
(* (lemma `BSC_capacity`).                                                    *)
(*                                                                            *)
(* ```                                                                        *)
(*   BSC.c == Definition of the binary symmetric channel (BSC)                *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope channel_scope.
Local Open Scope ring_scope.

Module BSC.
Section BSC_sect.
Variable A : finType.
Hypothesis card_A : #|A| = 2%N.
Variable p : {prob Rdefinitions.R}.

Definition c : `Ch(A, A) := fdist_binary card_A p.

End BSC_sect.
End BSC.

Local Open Scope entropy_scope.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Section bsc_capacity_proof.
Variable A : finType.
Hypothesis card_A : #|A| = 2%N.
Variables (P : {fdist A}) (p : Rdefinitions.R).
Hypothesis p_01' : 0 < p < 1.

Let p_01'_ : 0 <= p <= 1.
by move: p_01' => /andP[/ltW -> /ltW ->].
Qed.

Let p_01 : {prob Rdefinitions.R} := Eval hnf in Prob.mk_ p_01'_.

Lemma HP_HPW : `H P - `H(P, BSC.c card_A p_01)%channel = - H2 p.
Proof.
rewrite {2}/entropy /=.
rewrite (eq_bigr (fun a => ((P `X (BSC.c card_A p_01))) (a.1, a.2) *
  log (((P `X (BSC.c card_A p_01))) (a.1, a.2)))); last first.
  case=> //=.
rewrite -(pair_big xpredT xpredT (fun a b => (P `X (BSC.c card_A p_01))
  (a, b) * log ((P `X (BSC.c card_A p_01)) (a, b)))) /=.
rewrite {1}/entropy .
set a := \sum_(_ in _) _. set b := \sum_(_ <- _) _.
apply trans_eq with (- (a + (-1) * b)); first by rewrite mulN1r opprB opprK addrC.
rewrite /b {b} big_distrr /= /a {a} -big_split /=.
rewrite !Set2sumE /= !fdist_prodE /BSC.c !fdist_binaryxx !fdist_binaryE/=.
rewrite eq_sym !(negbTE (Set2.a_neq_b card_A)) /H2 (* TODO *).
set a := Set2.a _. set b := Set2.b _.
have [H1|H1] := eqVneq (P a) 0.
  rewrite H1 !(mul0r, mulr0, addr0, add0r).
  move: (FDist.f1 P); rewrite Set2sumE /= -/a -/b.
  rewrite H1 add0r => ->.
  rewrite log1 !(mul0r, mulr0, addr0, add0r, mul1r, mulr1).
  by rewrite /onem mulN1r opprK opprB opprK addrC.
rewrite logM; last 2 first.
  by rewrite lt_neqAle eq_sym H1/=.
  by case/andP: p_01' => ? ?; exact/onem_gt0.
rewrite logM; last 2 first.
  by rewrite lt_neqAle eq_sym H1/=.
  by case/andP: p_01'.
have [H2|H2] := eqVneq (P b) 0.
  rewrite H2 !(mul0r, mulr0, addr0, add0r).
  move: (FDist.f1 P); rewrite Set2sumE /= -/a -/b.
  rewrite H2 addr0 => ->.
  rewrite log1 !(mul0r, mulr0, addr0, add0r, mul1r, mulr1).
  rewrite /onem/=.
  by rewrite mulN1r opprK opprB opprK addrC.
rewrite logM; last 2 first.
  by rewrite lt_neqAle eq_sym H2/=.
  by case/andP: p_01' => ? ?.
rewrite logM; last 2 first.
  by rewrite lt_neqAle eq_sym H2/=.
  by case/andP: p_01' => ? ?; exact/onem_gt0.
rewrite /onem.
transitivity (p * (P a + P b) * log p + (1 - p) * (P a + P b) * log (1 - p) ).
  rewrite /log.
  set l2Pa := Log 2 (P a).
  set l2Pb := Log 2 (P b).
  set l21p := Log 2 (1 - p).
  set l2p := Log 2 p.
  set Pa := P a.
  set Pb := P b.
  lra.
move: (FDist.f1 P).
rewrite Set2sumE /= -/a -/b.
rewrite -RplusE => ->.
rewrite !mulr1.
by rewrite opprB opprK addrC.
Qed.

Lemma IPW : `I(P, BSC.c card_A p_01) = `H(P `o BSC.c card_A p_01) - H2 p.
Proof. by rewrite /mutual_info_chan addrAC HP_HPW addrC. Qed.

Lemma H_out_max : `H(P `o BSC.c card_A p_01) <= 1.
Proof.
have-> : 1 = log#|A|%:R :> Rdefinitions.R by rewrite card_A log2.
exact:entropy_max.
Qed.

(*
Lemma bsc_out_H_half' : 0 < 1%:R / 2%:R < 1.
Proof.
rewrite /= (_ : 1%:R = 1) // (_ : 2%:R = 2) //.
split => //.
apply: divR_gt0 => //.
apply/ltR_pdivr_mulr => //.
by rewrite mul1R.
Qed.
*)

Lemma H_out_binary_uniform : `H(fdist_uniform card_A `o BSC.c card_A p_01) = 1.
Proof.
rewrite /entropy Set2sumE 2!fdist_outE 2!Set2sumE /=.
rewrite /BSC.c !fdist_binaryE.
rewrite 2!eqxx (eq_sym (Set2.b card_A)) (negbTE (Set2.a_neq_b card_A)).
rewrite 2!fdist_uniformE -!(mulrDl _ _ _^-1) (addrC _.~) add_onemK div1r.
rewrite card_A logV // log2.
by rewrite mulrC -splitr opprK.
Qed.

End bsc_capacity_proof.

(*
Section convex_ext.
Require Import entropy_convex.
Local Open Scope convex_scope.

Variables (A B : finType).
Hypothesis card_A : #|A| = 2%nat.

Lemma mutual_info_chan_uniform (W : A -> {fdist B}) :
  `I(P, W) <= `I(fdist_uniform card_A, W).
Proof.
rewrite !mutual_info_chanE -!mutual_info_sym.
have [Q [q ->]] : exists (Q : {fdist A}) (q : {prob R}),
    P = (fdist_uniform card_A) <|q|> Q.
  admit.
have B0: (0 < #|B|)%nat.
  admit.
set P' := (_ <|q|> _).
have:= mutual_information_concave W B0 P' W => /=.
rewrite /convex.concave_function /=.
End convex_ext.
*)

Section bsc_capacity_theorem.
Let R := Rdefinitions.R.
Variable A : finType.
Hypothesis card_A : #|A| = 2%N.
Variable p : R.
Hypothesis p_01' : 0 < p < 1.
Let p_01'_ : 0 <= p <= 1.
by move: p_01' => /andP[/ltW -> /ltW ->].
Qed.
Let p_01 : {prob R} := Eval hnf in Prob.mk_ p_01'_.

Theorem BSC_capacity : capacity (BSC.c card_A p_01) = 1 - H2 p.
Proof.
rewrite /capacity /image.
set E := (fun y : R => _).
set p' := Prob.mk_ p_01'_.
have has_sup_E : has_sup E.
  split.
    set d := fdist_binary card_A p' (Set2.a card_A).
    by exists (`I(d, BSC.c card_A p')), d.
  exists 1 => y [P _ <-{y}].
  have := IPW card_A P p_01'.
  set tmp := (X in `I(_, BSC.c _ X)).
  rewrite (_ : tmp = p_01)//; last first.
    by apply/val_inj => //.
  move=> ->.
  rewrite lerBlDr (le_trans (H_out_max card_A P p_01'))//.
  rewrite -lerBlDl subrr (_ : p = Prob.p p')// (entropy_H2 card_A).
  exact/entropy_ge0.
apply/eqP; rewrite eq_le; apply/andP; split.
  have [_ /(_ (1 - H2 p))] := Rsup_isLub (0 : R) has_sup_E.
  apply => x [d _ dx].
  suff : `H(d `o BSC.c card_A p_01) <= 1.
    have := IPW card_A d p_01'.
    set tmp := (X in `I(_, BSC.c _ X)).
    rewrite (_ : tmp = p_01)//; last first.
      by apply/val_inj => //.
    set tmp' := (X in _ = `H(d `o (BSC.c card_A X)) - _ -> _).
    rewrite (_ : tmp' = p_01)//; last first.
      by apply/val_inj => //.
    rewrite dx => -> ?.
    by rewrite lerBlDr subrK.
  have := H_out_max card_A d p_01'.
  set tmp' := (X in `H(d `o (BSC.c card_A X)) <= _ -> _).
  rewrite (_ : tmp' = p_01)//.
  by apply/val_inj.
move: (@IPW _ card_A (fdist_uniform card_A) _ p_01').
rewrite H_out_binary_uniform => <-.
apply/Rsup_ub => //=.
exists (fdist_uniform card_A) => //.
do 2 f_equal.
exact: val_inj.
Qed.

End bsc_capacity_theorem.

Section dH_BSC.

Let R := Rdefinitions.R.
Variable p : {prob R}.
Let card_F2 : #| 'F_2 | = 2%N. by rewrite card_Fp. Qed.
Let W := BSC.c card_F2 p.
Variables (M : finType) (n : nat) (f : encT 'F_2 M n).

Local Open Scope vec_ext_scope.

Lemma DMC_BSC_prop m y : let d := dH y (f m) in
  W ``(y | f m) = (1 - Prob.p p) ^+ (n - d) * Prob.p p ^+ d.
Proof.
move=> d; rewrite DMCE.
transitivity ((\prod_(i < n | (f m) ``_ i == y ``_ i) (1 - Prob.p p)) *
              (\prod_(i < n | (f m) ``_ i != y ``_ i) Prob.p p)).
  rewrite (bigID [pred i | (f m) ``_ i == y ``_ i]) /=; congr (_ * _).
    by apply eq_bigr => // i /eqP ->; rewrite /BSC.c fdist_binaryxx.
  apply eq_bigr => //= i /negbTE Hyi; by rewrite /BSC.c fdist_binaryE eq_sym Hyi.
congr (_ * _).
  by rewrite big_const /= iter_mulr /= card_dHC mulr1.
by rewrite big_const /= iter_mulr /= card_dH_vec mulr1.
Qed.

End dH_BSC.

(* moved from decoder.v; TODO: rename *)
Section bsc_prob_prop.
Local Open Scope reals_ext_scope.
Local Open Scope order_scope.

Let R := Rdefinitions.R.

(* This lemma is more or less stating that
   (log q <|n2 / n|> log r) <= (log q <|n1 / n|> log r) *)
Lemma expr_conv_mono n n1 n2 q r :
  0 < q :> R -> q <= r -> (n1 <= n2 <= n)%N ->
  r ^+ (n - n2) * q ^+ n2 <= r ^+ (n - n1) * q ^+ n1.
Proof.
move=> /[dup] /ltW q0 q1 qr /andP [] n12 n2n.
have r1 := lt_le_trans q1 qr.
have r0 := ltW r1.
rewrite [leLHS](_ : _ = q ^+ n1 * q ^+ (n2 - n1)%N * r ^+ (n - n2)%N);
  last by rewrite -exprD subnKC // mulrC.
rewrite [leRHS](_ : _ = q ^+ n1 * r ^+ (n2 - n1)%N * r ^+ (n - n2)%N);
  last by rewrite -mulrA -exprD addnBAC // subnKC // mulrC.
apply: ler_pM => //; [by apply/mulr_ge0; apply/exprn_ge0 | by apply/exprn_ge0 | ].
apply: ler_pM => //; [by apply/exprn_ge0 | by apply/exprn_ge0 |].
rewrite -[leLHS]mul1r -ler_pdivlMr ?exprn_gt0 // -expr_div_n.
apply: exprn_ege1.
by rewrite ler_pdivlMr // mul1r.
Qed.

Lemma bsc_prob_prop (p : {prob R}) n : Prob.p p < 1 / 2 ->
  forall n1 n2 : nat, (n1 <= n2 <= n)%N ->
  (1 - Prob.p p) ^+ (n - n2) * (Prob.p p) ^+ n2 <=
  (1 - Prob.p p) ^+ (n - n1) * (Prob.p p) ^+ n1.
Proof.
move=> p05 d1 d2 d1d2.
have [->|] := eqVneq p 0%:pr.
  rewrite probpK subr0 !expr1n !mul1r !expr0n.
  move: d1d2; case: d2; first by rewrite leqn0 => /andP [] ->.
  by case: (d1 == 0%N).
move/prob_gt0 => p1.
apply/expr_conv_mono => //.
lra.
Qed.

End bsc_prob_prop.

(* NB: moved from ldpc.v *)
Section post_proba_bsc_unif.
Local Open Scope reals_ext_scope.
Local Open Scope order_scope.
Local Open Scope proba_scope.
Local Open Scope vec_ext_scope.

Let R := Rdefinitions.R.

Variable A : finType.
Hypothesis card_A : #|A| = 2%N.
Variable p : R.
Hypothesis p_01' : 0 < p < 1.

Let p_01'_ : 0 <= p <= 1.
by move: p_01' => /andP [/ltW -> /ltW ->].
Qed.

Let p_01 : {prob R} := Eval hnf in Prob.mk_ p_01'_.

Let P := fdist_uniform (R:=R) card_A.
Variable a' : A.
Hypothesis Ha' : receivable_prop (P `^ 1) (BSC.c card_A p_01) (\row_(i < 1) a').

Lemma bsc_post (a : A) :
  (P `^ 1) `^^ (BSC.c card_A p_01) (\row_(i < 1) a | mkReceivable Ha') =
  if a == a' then 1 - p else p.
Proof.
rewrite fdist_post_probE /= !fdist_rVE DMCE big_ord_recl big_ord0.
rewrite (eq_bigr (fun x : 'M_1 => P a * (BSC.c card_A p_01) ``( (\row__ a') | x))); last first.
  by move=> i _; rewrite /P !fdist_rVE big_ord_recl big_ord0 !fdist_uniformE mulr1.
rewrite -big_distrr /= (_ : \sum_(_ | _) _ = 1); last first.
  transitivity (\sum_(i in 'M_1) fdist_binary card_A p_01 (i ``_ ord0) a').
    apply eq_bigr => i _.
    by rewrite DMCE big_ord_recl big_ord0 mulr1 /BSC.c mxE.
  apply/(@big_rV1_ord0 _ _ _ _ (fdist_binary card_A p_01 ^~ a')).
  by rewrite -sum_fdist_binary_swap // FDist.f1.
rewrite mxE mulr1 big_ord_recl big_ord0 /BSC.c fdist_binaryE /= eq_sym !mxE.
rewrite mulr1 onemE.
rewrite mulrAC mulfV ?mul1r // fdist_uniformE card_A invr_neq0 //.
by apply: lt0r_neq0; lra.
Qed.

End post_proba_bsc_unif.
