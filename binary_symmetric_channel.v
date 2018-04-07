(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg perm zmodp matrix.
Require Import Reals Fourier.
Require Import Rssr Reals_ext log2 ssr_ext ssralg_ext bigop_ext Rbigop proba.
Require Import entropy binary_entropy_function channel hamming channel_code.

(** * Capacity of the binary symmetric channel *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope channel_scope.

(** Definition of the Binary Symmetric Channel (BSC) *)

Module BSC.
Section BSC_sect.

Variable A : finType.
Hypothesis card_A : #|A| = 2%nat.
Variable p : R.
Hypothesis p_01 : 0 <= p <= 1.

Definition c : `Ch_1(A, A) :=
  fun a => locked (makeDist (Binary.f0 p_01 a) (Binary.f1 card_A p a)).

Lemma cE a : c a =1 Binary.f p a. Proof. rewrite /c; by unlock. Qed.

End BSC_sect.
End BSC.

Lemma closed p : 0 < p < 1 -> 0 <= p <= 1.
Proof. case => ?; split; by apply Rlt_le. Qed.

Local Open Scope channel_scope.
Local Open Scope entropy_scope.

Section bsc_capacity_proof.

Variable A : finType.
Hypothesis card_A : #|A| = 2%nat.
Variable P : dist A.
Variable p : R.
Hypothesis p_01' : 0 < p < 1.

Let p_01 := closed p_01'.

Lemma HP_HPW : `H P - `H(P , BSC.c card_A p_01) = - H2 p.
Proof.
rewrite {2}/entropy /=.
rewrite (eq_bigr (fun a => (`J( P, (BSC.c card_A p_01))) (a.1, a.2) *
  log ((`J( P, (BSC.c card_A p_01))) (a.1, a.2)))); last by case.
rewrite -(pair_big xpredT xpredT (fun a b => (`J( P, (BSC.c card_A p_01)))
  (a, b) * log ((`J( P, (BSC.c card_A p_01))) (a, b)))) /=.
rewrite {1}/entropy .
set a := \rsum_(_ in _) _. set b := \rsum_(_ <- _) _.
apply trans_eq with (- (a + (-1) * b)); first by field.
rewrite /b {b} big_distrr /= /a {a} -big_split /=.
rewrite !Set2sumE /= !JointDist.dE !BSC.cE /= !Binary.fxx.
rewrite /Binary.f eq_sym !(negbTE (Set2.a_neq_b card_A)) /H2.
set a := Set2.a _. set b := Set2.b _.
case: (Req_EM_T (P a) 0) => H1.
  rewrite H1 !(mul0R, mulR0, addR0, add0R).
  move: (pmf1 P); rewrite Set2sumE /= -/a -/b.
  rewrite H1 add0R => ->.
  rewrite /log Log_1 !(mul0R, mulR0, addR0, add0R, mul1R, mulR1); field.
rewrite /log LogM; last 2 first.
  case: p_01' => ? ?; fourier.
  move/eqP in H1.
  apply/RltP; rewrite lt0R H1; exact/RleP/dist_nonneg.
rewrite /log LogM; last 2 first.
  case: p_01' => ? ?; fourier.
  apply/RltP; rewrite lt0R; apply/andP; split; [exact/eqP|exact/RleP/dist_nonneg].
case: (Req_EM_T (P b) 0) => H2.
  rewrite H2 !(mul0R, mulR0, addR0, add0R).
  move: (pmf1 P); rewrite Set2sumE /= -/a -/b.
  rewrite H2 addR0 => ->.
  rewrite /log Log_1 !(mul0R, mulR0, addR0, add0R, mul1R, mulR1); field.
rewrite /log LogM; last 2 first.
  case: p_01' => ? ?; fourier.
  apply/RltP; rewrite lt0R; apply/andP; split; [exact/eqP|exact/RleP/dist_nonneg].
rewrite /log LogM; last 2 first.
  case: p_01' => ? ?; fourier.
  apply/RltP; rewrite lt0R; apply/andP; split; [exact/eqP|exact/RleP/dist_nonneg].
transitivity (p * (P a + P b) * log p + (1 - p) * (P a + P b) * log (1 - p) ).
  rewrite /log; by field.
move: (pmf1 P); rewrite Set2sumE /= -/a -/b => ->; rewrite /log; by field.
Qed.

Lemma IPW : `I(P ; BSC.c card_A p_01) = `H(P `o BSC.c card_A p_01) - H2 p.
Proof.
rewrite /mut_info addRC.
set a := `H(_ `o _).
apply trans_eq with (a + (`H P - `H(P , BSC.c card_A p_01))); first by field.
by rewrite HP_HPW.
Qed.

Lemma H_out_max : `H(P `o BSC.c card_A p_01) <= 1.
Proof.
rewrite {1}/entropy /= Set2sumE /= !OutDist.dE 2!Set2sumE /=.
set a := Set2.a _. set b := Set2.b _.
rewrite !BSC.cE !Binary.fxx /Binary.f /= !(eq_sym _ a).
rewrite (negbTE (Set2.a_neq_b card_A)).
move: (pmf1 P); rewrite Set2sumE /= -/a -/b => P1.
have -> : p * P a + (1 - p) * P b = 1 - ((1 - p) * P a + p * P b).
  rewrite -{2}P1; by field.
have H01 : 0 < ((1 - p) * P a + p * P b) < 1.
  move: (dist_nonneg P a) => H1.
  move: (dist_max P b) => H4.
  move: (dist_max P a) => H3.
  case: p_01' => Hp1 Hp2.
  split.
    case/Rle_lt_or_eq_dec : H1 => H1.
    - apply Rplus_lt_le_0_compat.
        by apply mulR_gt0; fourier.
      by apply mulR_ge0; fourier.
    - rewrite -H1 mulR0 add0R (_ : P b = 1) ?mulR1 //.
      by rewrite -P1 -H1 add0R.
  rewrite -{2}P1.
  case: (Req_EM_T (P a) 0) => Hi.
    rewrite Hi mulR0 !add0R.
    rewrite Hi add0R in P1.
    by rewrite P1 mulR1.
  case: (Req_EM_T (P b) 0) => Hj.
    rewrite Hj addR0 in P1.
    rewrite Hj mulR0 !addR0 P1 mulR1.
    fourier.
    case/Rle_lt_or_eq_dec : H1 => H1.
    - apply Rplus_le_lt_compat.
      + rewrite -{2}(mul1R (P a)); apply Rmult_le_compat_r; fourier.
      + rewrite -{2}(mul1R (P b)).
        apply Rmult_lt_compat_r => //.
        apply/RltP; rewrite lt0R; apply/andP; split; [exact/eqP|exact/RleP/dist_nonneg].
    - rewrite -H1 mulR0 2!add0R.
      have -> : P b = 1 by rewrite -P1 -H1 add0R.
      by rewrite mulR1.
rewrite (_ : forall a b, - (a + b) = - a - b); last by move=> *; field.
rewrite -mulNR.
set q := (1 - p) * P a + p * P b.
eapply (Rle_trans _ (H2 q)); last by apply H2_max.
rewrite /H2 !mulNR; apply Req_le; field.
Qed.

Lemma bsc_out_H_half' : 0 < INR 1 / INR 2 < 1.
Proof. rewrite /= (_ : INR 1 = 1) // (_ : INR 2 = 2) //; split; fourier. Qed.

Lemma H_out_binary_uniform :
  `H(Uniform.d card_A `o BSC.c card_A p_01) = 1.
Proof.
rewrite {1}/entropy !Set2sumE /= !OutDist.dE !Set2sumE /=.
rewrite !BSC.cE !Binary.fxx /Binary.f (eq_sym _ (Set2.a _)).
rewrite (negbTE (Set2.a_neq_b card_A)).
rewrite -!mulRDl (_ : 1 - p + p = 1); last by field.
rewrite mul1R (_ : p + (1 - p) = 1); last by field.
rewrite mul1R -!mulRDl /= /Uniform.f card_A /=.
rewrite (_ : INR 1 = 1) // (_ : INR 2 = 2) // div1R /log LogV; last by fourier.
rewrite Log_n //=; field.
Qed.

End bsc_capacity_proof.

Section bsc_capacity_theorem.

Variable A : finType.
Hypothesis card_A : #|A| = 2%nat.
Variable p : R.
Hypothesis p_01' : 0 < p < 1.
Let p_01 := closed p_01'.

(** The capacity of a Binary Symmetric Channel: *)

Theorem BSC_capacity : capacity (BSC.c card_A p_01) (1 - H2 p).
Proof.
rewrite /capacity; split.
- move=> d.
  move: (@IPW _ card_A d _ p_01') => tmp.
  suff : `H(d `o BSC.c card_A p_01) <= 1.
    move=> ?.
    unfold p_01 in *.
    fourier.
  by apply H_out_max.
- move=> d Hd.
  move: (@IPW _ card_A (Uniform.d card_A) _ p_01').
  rewrite H_out_binary_uniform => <-.
  by apply Hd.
Qed.

End bsc_capacity_theorem.

Section dH_BSC.

Variable p : R.
Hypothesis p_01 : (0 <= p <= 1)%R.

Let card_F2 : #| 'F_2 | = 2%nat. by rewrite card_Fp. Qed.

Let W := BSC.c card_F2 p_01.

Variables (M : finType) (n : nat) (f : encT [finType of 'F_2] M n).

Local Open Scope vec_ext_scope.

Lemma DMC_BSC_prop : forall m y,
  let d := dH y (f m) in
  W ``(y | (f m)) = ((1 - p) ^ (n - d) * p ^ d)%R.
Proof.
move=> m y d.
rewrite DMCE.
transitivity ((\rprod_(i < n | (f m) ``_ i == y ``_ i) (1 - p)) *
              (\rprod_(i < n | (f m) ``_ i != y ``_ i) p))%R.
  rewrite (bigID [pred i | (f m) ``_ i == y ``_ i]) /=.
  congr (_ * _).
  by apply eq_bigr => // i /eqP ->; rewrite BSC.cE Binary.fxx.
  apply eq_bigr => //= i /negbTE Htmp; rewrite BSC.cE /Binary.f eq_sym; by rewrite Htmp.
congr (_ * _).
by rewrite big_const /= iter_Rmult /= card_dHC.
by rewrite big_const /= iter_Rmult /= card_dH_vec.
Qed.

Local Close Scope vec_ext_scope.

End dH_BSC.
