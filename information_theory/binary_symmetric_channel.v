(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum zmodp matrix lra.
From mathcomp Require Import mathcomp_extra classical_sets Rstruct reals.
Require Import Reals Lra.
Require Import ssrR Reals_ext realType_ext logb ssr_ext ssralg_ext bigop_ext.
Require Import fdist entropy binary_entropy_function channel hamming channel_code.
Require Import pproba.

(******************************************************************************)
(*                Capacity of the binary symmetric channel                    *)
(*                                                                            *)
(* BSC.c == Definition of the binary symmetric channel (BSC)                  *)
(*                                                                            *)
(* Lemma:                                                                     *)
(*   BSC_capacity == the capacity of a BSC is 1 - H p                         *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope channel_scope.
Local Open Scope R_scope.

Module BSC.
Section BSC_sect.
Variable A : finType.
Hypothesis card_A : #|A| = 2%nat.
Variable p : {prob R}.

Definition c : `Ch(A, A) := fdist_binary card_A p.

End BSC_sect.
End BSC.

Local Open Scope entropy_scope.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Section bsc_capacity_proof.
Variable A : finType.
Hypothesis card_A : #|A| = 2%nat.
Variables (P : {fdist A}) (p : R).
Hypothesis p_01' : (0 < p < 1)%mcR.

Let p_01'_ : (0 <= p <= 1)%mcR.
by move: p_01' => /andP[/ltW -> /ltW ->].
Qed.

Let p_01 : {prob R} := Eval hnf in Prob.mk_ p_01'_.

Lemma HP_HPW : `H P - `H(P, BSC.c card_A p_01) = - H2 p.
Proof.
rewrite {2}/entropy /=.
rewrite (eq_bigr (fun a => ((P `X (BSC.c card_A p_01))) (a.1, a.2) *
  log (((P `X (BSC.c card_A p_01))) (a.1, a.2)))); last by case.
rewrite -(pair_big xpredT xpredT (fun a b => (P `X (BSC.c card_A p_01))
  (a, b) * log ((P `X (BSC.c card_A p_01)) (a, b)))) /=.
rewrite {1}/entropy .
set a := \sum_(_ in _) _. set b := \sum_(_ <- _) _.
apply trans_eq with (- (a + (-1) * b)); first by field.
rewrite /b {b} big_distrr /= /a {a} -big_split /=.
rewrite !Set2sumE /= !fdist_prodE /BSC.c !fdist_binaryxx !fdist_binaryE/=.
rewrite eq_sym !(negbTE (Set2.a_neq_b card_A)) /H2 (* TODO *).
set a := Set2.a _. set b := Set2.b _.
case: (Req_EM_T (P a) 0) => H1.
  rewrite H1 !(mul0R, mulR0, addR0, add0R).
  move: (FDist.f1 P); rewrite Set2sumE /= -/a -/b.
  rewrite H1 add0r => ->.
  rewrite /log Log_1 -!RmultE !(mul0R, mulR0, addR0, add0R, mul1R, mulR1).
  rewrite /onem -RminusE (_ : 1%mcR = 1)//.
  field.
rewrite /log LogM; last 2 first.
  move/eqP in H1.
  have [+ _] := fdist_gt0 P a.
  by move/(_ H1) => /RltP.
  by case/andP: p_01' => ? ?; exact/RltP/onem_gt0.
rewrite /log LogM; last 2 first.
  move/eqP in H1.
  have [+ _] := fdist_gt0 P a.
  by move/(_ H1) => /RltP.
  by case/andP: p_01' => ? ?; exact/RltP.
case: (Req_EM_T (P b) 0) => H2.
  rewrite H2 !(mul0R, mulR0, addR0, add0R).
  move: (FDist.f1 P); rewrite Set2sumE /= -/a -/b.
  rewrite H2 addr0 => ->.
  rewrite /log Log_1 -!RmultE !(mul0R, mulR0, addR0, add0R, mul1R, mulR1).
  rewrite /onem -RminusE (_ : 1%mcR = 1)//.
  field.
rewrite /log LogM; last 2 first.
  move/eqP in H2.
  have [+ _] := fdist_gt0 P b.
  by move/(_ H2) => /RltP.
  by case/andP: p_01' => ? ?; exact/RltP.
rewrite /log LogM; last 2 first.
  move/eqP in H2.
  have [+ _] := fdist_gt0 P b.
  by move/(_ H2) => /RltP.
  by case/andP: p_01' => ? ?; exact/RltP/onem_gt0.
rewrite /log.
rewrite -!RmultE.
rewrite /onem -RminusE (_ : 1%mcR = 1)//.
transitivity (p * (P a + P b) * log p + (1 - p) * (P a + P b) * log (1 - p) ).
  rewrite /log.
  set l2Pa := Log 2 (P a).
  set l2Pb := Log 2 (P b).
  set l21p := Log 2 (1 - p).
  set l2p := Log 2 p.
  set Pa := P a.
  set Pb := P b.
  ring.
move: (FDist.f1 P).
rewrite Set2sumE /= -/a -/b.
rewrite -RplusE => ->.
rewrite !mulR1.
rewrite /log; field.
Qed.

Lemma IPW : `I(P, BSC.c card_A p_01) = `H(P `o BSC.c card_A p_01) - H2 p.
Proof.
rewrite /mutual_info_chan addRC.
set a := `H(_ `o _).
transitivity (a + (`H P - `H(P , BSC.c card_A p_01))); first by field.
by rewrite HP_HPW.
Qed.

Lemma H_out_max : `H(P `o BSC.c card_A p_01) <= 1.
Proof.
rewrite {1}/entropy /= Set2sumE /= !fdist_outE 2!Set2sumE /=.
set a := Set2.a _. set b := Set2.b _.
rewrite /BSC.c !fdist_binaryxx !fdist_binaryE /= !(eq_sym _ a).
rewrite (negbTE (Set2.a_neq_b card_A)).
move: (FDist.f1 P); rewrite Set2sumE /= -/a -/b => P1.
rewrite -!(RmultE,RplusE).
have -> : p * P a + (1 - p) * P b = 1 - ((1 - p) * P a + p * P b).
  rewrite -RplusE (_ : 1%mcR = 1)// in P1.
  rewrite -{2}P1.
  ring_simplify.
  congr (_ + _).
  by rewrite subRK.
case/andP: p_01' => /RltP Hp1 /RltP Hp2.
rewrite (_ : 0%mcR = 0%coqR)// in Hp1.
rewrite (_ : 1%mcR = 1%coqR)// in Hp2, P1.
have H01 : 0 < ((1 - p) * P a + p * P b) < 1.
  move: (FDist.ge0 P a) => /RleP H1.
  move: (FDist.le1 P b) => H4.
  move: (FDist.le1 P a) => H3.
  split.
    case/Rle_lt_or_eq_dec : H1 => H1; rewrite (_ : 0%mcR = 0)// in H1.
    - apply addR_gt0wl.
        apply: mulR_gt0 => //.
        by rewrite subR_gt0.
      apply: mulR_ge0 => //.
      exact: ltRW.
    - by rewrite -H1 mulR0 add0R (_ : P b = 1) ?mulR1 // -P1 -H1 add0r.
  rewrite -{2}P1.
  case: (Req_EM_T (P a) 0) => Hi.
    rewrite Hi mulR0 !add0R.
    rewrite Hi add0r in P1.
    by rewrite P1 mulR1 add0r.
  case: (Req_EM_T (P b) 0) => Hj.
    rewrite Hj addr0 in P1.
    rewrite Hj mulR0 !addR0 P1 mulR1.
    rewrite addr0.
    by rewrite ltR_subl_addr ltR_addl.
  case/Rle_lt_or_eq_dec : H1 => H1.
  - apply leR_lt_add.
    + rewrite -{2}(mul1R (P a)); apply leR_wpmul2r => //.
      by rewrite leR_subl_addr leR_addl; exact: ltRW.
    + rewrite -{2}(mul1R (P b)); apply ltR_pmul2r => //.
      by apply/RltP; rewrite lt0r; apply/andP; split; [exact/eqP|by []].
  - rewrite -H1 mulR0 add0R add0r.
    have -> : P b = 1 by rewrite -P1 -H1 add0r.
    by rewrite mulR1.
rewrite (_ : forall a b, - (a + b) = - a - b); last by move=> *; field.
rewrite -mulNR.
set q := (1 - p) * P a + p * P b.
apply: (@leR_trans (H2 q)); last exact: H2_max.
by rewrite /H2 !mulNR; apply Req_le; field.
Qed.

Lemma bsc_out_H_half' : 0 < 1%:R / 2%:R < 1.
Proof.
rewrite /= (_ : 1%:R = 1) // (_ : 2%:R = 2) //.
split => //.
apply: divR_gt0 => //.
apply/ltR_pdivr_mulr => //.
by rewrite mul1R.
Qed.

Lemma H_out_binary_uniform : `H(fdist_uniform card_A `o BSC.c card_A p_01) = 1.
Proof.
rewrite {1}/entropy !Set2sumE /= !fdist_outE !Set2sumE /=.
rewrite /BSC.c !fdist_binaryxx !fdist_binaryE (eq_sym _ (Set2.a _)) !fdist_uniformE.
rewrite (negbTE (Set2.a_neq_b card_A)).
rewrite -!mulrDl.
rewrite /onem subrK.
rewrite !mul1r.
rewrite addrC subrK.
have ? : 2%mcR != 0%mcR :> R.
  rewrite (_ : 2%mcR = 2)//.
  rewrite (_ : 0%mcR = 0)//.
  by apply/eqP.
rewrite -RdivE// ?card_A//.
rewrite div1R -RinvE//.
rewrite -!mulRDl /log LogV//.
rewrite Log_n //=.
rewrite (_ : 2%mcR = 2)//.
field.
Qed.

End bsc_capacity_proof.

Section bsc_capacity_theorem.
Variable A : finType.
Hypothesis card_A : #|A| = 2%nat.
Variable p : R.
Hypothesis p_01' : (0 < p < 1)%mcR.
Let p_01'_ : (0 <= p <= 1)%mcR.
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
  apply/RleP/leR_subl_addr/(leR_trans (H_out_max card_A P p_01')).
  rewrite addRC -leR_subl_addr subRR.
  by rewrite (entropy_H2 card_A (Prob.mk_ (p_01'_))); exact/entropy_ge0.
apply eqR_le; split.
  apply/RleP.
  have [_ /(_ (1 - H2 p))] := Rsup_isLub (0 : R) has_sup_E.
  apply => x [d _ dx]; apply/RleP.
  suff : `H(d `o BSC.c card_A p_01) <= 1.
  have := IPW card_A d p_01'.
  set tmp := (X in `I(_, BSC.c _ X)).
  rewrite (_ : tmp = p_01)//; last first.
    by apply/val_inj => //.
  set tmp' := (X in _ = `H(d `o (BSC.c card_A X)) - _ -> _).
  rewrite (_ : tmp' = p_01)//; last first.
    by apply/val_inj => //.
  rewrite dx => -> ?.
  by rewrite leR_subl_addr subRK.
  have := H_out_max card_A d p_01'.
  set tmp' := (X in `H(d `o (BSC.c card_A X)) <= _ -> _).
  rewrite (_ : tmp' = p_01)//.
  by apply/val_inj.
move: (@IPW _ card_A (fdist_uniform card_A) _ p_01').
rewrite H_out_binary_uniform => <-.
apply/RleP/Rsup_ub => //=.
exists (fdist_uniform card_A) => //.
do 2 f_equal.
exact: val_inj.
Qed.

End bsc_capacity_theorem.

Section dH_BSC.

Variable p : {prob R}.
Let card_F2 : #| 'F_2 | = 2%nat. by rewrite card_Fp. Qed.
Let W := BSC.c card_F2 p.
Variables (M : finType) (n : nat) (f : encT 'F_2 M n).

Local Open Scope vec_ext_scope.

Lemma DMC_BSC_prop m y : let d := dH y (f m) in
  W ``(y | f m) = ((1 - Prob.p p) ^ (n - d) * Prob.p p ^ d)%R.
Proof.
move=> d; rewrite DMCE.
transitivity ((\prod_(i < n | (f m) ``_ i == y ``_ i) (1 - Prob.p p)) *
              (\prod_(i < n | (f m) ``_ i != y ``_ i) Prob.p p))%R.
  rewrite (bigID [pred i | (f m) ``_ i == y ``_ i]) /=; congr (_ * _).
    by apply eq_bigr => // i /eqP ->; rewrite /BSC.c fdist_binaryxx.
  apply eq_bigr => //= i /negbTE Hyi; by rewrite /BSC.c fdist_binaryE eq_sym Hyi.
congr (_ * _).
  by rewrite big_const /= iter_mulR /= card_dHC.
by rewrite big_const /= iter_mulR /= card_dH_vec.
Qed.

End dH_BSC.

(* moved from decoder.v; TODO: rename *)
Section bsc_prob_prop.
Local Open Scope reals_ext_scope.
Local Open Scope ring_scope.
Local Open Scope order_scope.

(* This lemma is more or less stating that
   (log q <|n2 / n|> log r) <= (log q <|n1 / n|> log r) *)
Lemma expr_conv_mono n n1 n2 q r :
  0 < q :> R -> q <= r -> (n1 <= n2 <= n)%nat ->
  r ^+ (n - n2) * q ^+ n2 <= r ^+ (n - n1) * q ^+ n1.
Proof.
move=> /[dup] /ltW q0 q1 qr /andP [] n12 n2n.
have r1 := lt_le_trans q1 qr.
have r0 := ltW r1.
rewrite [leLHS](_ : _ = q ^+ n1 * q ^+ (n2 - n1)%nat * r ^+ (n - n2)%nat);
  last by rewrite -exprD subnKC // mulrC.
rewrite [leRHS](_ : _ = q ^+ n1 * r ^+ (n2 - n1)%nat * r ^+ (n - n2)%nat);
  last by rewrite -mulrA -exprD addnBAC // subnKC // mulrC.
apply: ler_pM => //; [by apply/mulr_ge0; apply/exprn_ge0 | by apply/exprn_ge0 | ].
apply: ler_pM => //; [by apply/exprn_ge0 | by apply/exprn_ge0 |].
rewrite -[leLHS]mul1r -ler_pdivlMr ?exprn_gt0 // -expr_div_n.
apply: exprn_ege1.
by rewrite ler_pdivlMr // mul1r.
Qed.

Lemma bsc_prob_prop (p : {prob R}) n : Prob.p p < 1 / 2 ->
  forall n1 n2 : nat, (n1 <= n2 <= n)%nat ->
  ((1 - Prob.p p) ^ (n - n2) * (Prob.p p) ^ n2 <= (1 - Prob.p p) ^ (n - n1) * (Prob.p p) ^ n1)%R.
Proof.
move=> p05 d1 d2 d1d2.
case/boolP: (p == 0%:pr).
  move/eqP->; rewrite !coqRE; apply/RleP.
  rewrite probpK subr0 !expr1n !mul1r !expr0n.
  move: d1d2; case: d2; first by rewrite leqn0 => /andP [] ->.
  by case: (d1 == 0%nat).
move/prob_gt0 => p1.
rewrite !coqRE.
apply/RleP/expr_conv_mono => //.
lra.
Qed.
End bsc_prob_prop.

(* moved from ldpc.v *)
Section post_proba_bsc_unif.
Local Open Scope reals_ext_scope.
Local Open Scope ring_scope.
Local Open Scope order_scope.
Local Open Scope proba_scope.
Local Open Scope vec_ext_scope.

Variable A : finType.
Hypothesis card_A : #|A| = 2%nat.
Variable p : R.
Hypothesis p_01' : 0 < p < 1.

Let p_01'_ : 0 <= p <= 1.
by move: p_01' => /andP [/ltW -> /ltW ->].
Qed.

Let p_01 : {prob R} := Eval hnf in Prob.mk_ p_01'_.
(*
Let p_01 := Eval hnf in Prob.mk_ (ltR2W p_01').
*)

Let P := fdist_uniform (R:=R) card_A.
Variable a' : A.
Hypothesis Ha' : receivable_prop (P `^ 1) (BSC.c card_A p_01) (\row_(i < 1) a').

Lemma bsc_post (a : A) :
  (P `^ 1) `^^ (BSC.c card_A p_01) (\row_(i < 1) a | mkReceivable Ha') =
  (if a == a' then 1 - p else p)%R.
Proof.
rewrite fdist_post_probE /= !fdist_rVE DMCE big_ord_recl big_ord0.
rewrite (eq_bigr (fun x : 'M_1 => P a * (BSC.c card_A p_01) ``( (\row__ a') | x))%R); last first.
  by move=> i _; rewrite /P !fdist_rVE big_ord_recl big_ord0 !fdist_uniformE mulr1.
rewrite -big_distrr /= (_ : \sum_(_ | _) _ = 1)%R; last first.
  transitivity (\sum_(i in 'M_1) fdist_binary card_A p_01 (i ``_ ord0) a')%R.
    apply eq_bigr => i _.
    by rewrite DMCE big_ord_recl big_ord0 mulR1 /BSC.c mxE.
  apply/(@big_rV1_ord0 _ _ _ _ (fdist_binary card_A p_01 ^~ a')).
  by rewrite -sum_fdist_binary_swap // FDist.f1.
rewrite mxE mulr1 big_ord_recl big_ord0 /BSC.c fdist_binaryE /= eq_sym !mxE.
rewrite !coqRE mulr1 onemE.
rewrite mulrAC mulfV ?mul1r // fdist_uniformE card_A invr_neq0 //.
by apply: lt0r_neq0; lra.
Qed.

End post_proba_bsc_unif.
