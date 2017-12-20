(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg perm zmodp matrix.
Require Import Reals Fourier.
Require Import Reals_ext ssr_ext ssralg_ext Rssr log2 Rbigop proba entropy.
Require Import binary_entropy_function channel hamming channel_code.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Capacity of the binary symmetric channel *)

Local Open Scope channel_scope.

Module BSC.

Section BSC_sect.

Variable A : finType.
Hypothesis card_A : #|A| = 2%nat.
Variable p : R.
Hypothesis p_01 : 0 <= p <= 1.

(** Definition of the Binary Symmetric Channel (BSC) *)

(* NB: bdist <-> BSC? *)

Definition f (a : A) := fun a' => if a == a' then 1 - p else p.

Lemma f0 (a a' : A) : 0 <= f a a'.
Proof. rewrite /f. case: ifP => _; case: p_01 => ? ?; fourier. Qed.

Lemma f1 (a : A) : \rsum_(a' | a' \in A) f a a' = 1.
Proof.
move: (enum_uniq A).
move: (card_A).
rewrite /index_enum -enumT.
rewrite cardE.
case: (enum A) => // h [] // h' [] //= _.
rewrite inE andbC /= => h_h'.
rewrite big_cons /= big_cons /= big_nil.
rewrite /f.
case: ifP.
+ move/eqP => ?; subst h.
  rewrite (negbTE h_h'); by field.
+ move/negP/negP => a_h.
  suff : a == h' by move=> ->; by field.
  apply/negPn/negP => Habs.
  have : (3 <= #|A|)%nat.
    rewrite (cardD1 a) /= (cardD1 h) /= inE eqtype.eq_sym a_h /=.
    by rewrite (cardD1 h') /= inE eq_sym h_h' /= inE eq_sym Habs.
  by rewrite card_A.
Qed.

Definition c : `Ch_1(A, A) := fun a => locked (makeDist (f0 a) (f1 a)).

Lemma cE a : c a =1 f a.
Proof. rewrite /c; by unlock. Qed.

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
rewrite (eq_bigr (fun a => (`J( P, (BSC.c card_A p_01))) (a.1, a.2) * log ((`J( P, (BSC.c card_A p_01))) (a.1, a.2)))); last by case.
rewrite -(pair_big xpredT xpredT (fun a b => (`J( P, (BSC.c card_A p_01))) (a, b) * log ((`J( P, (BSC.c card_A p_01))) (a, b)))) /=.
rewrite {1}/entropy .
set a := \rsum_(_ in _) _. set b := \rsum_(_ <- _) _.
apply trans_eq with (- (a + (-1) * b)); first by field.
rewrite /b {b} big_distrr /= /a {a} -big_split /=.
rewrite /index_enum -enumT Two_set.enum.
rewrite big_cons /= big_cons /= big_cons /= big_cons /= big_nil /= big_cons /= big_cons /= big_nil /= big_nil /=.
rewrite !addR0 !JointDist.dE !BSC.cE /BSC.f /= !eqxx.
rewrite !(negbTE (Two_set.val0_neq_val1 card_A)).
move: (Two_set.val0_neq_val1 card_A).
rewrite eq_sym.
move/negbTE => ->.
rewrite /H2.
have Hpmf1 : P (Two_set.val0 card_A) + P (Two_set.val1 card_A) = 1.
  rewrite -(pmf1 P) /index_enum -enumT Two_set.enum big_cons /= big_cons /= big_nil /=; by field.
case: (Req_EM_T (P (Two_set.val0 card_A)) 0) => H1.
  rewrite H1.
  rewrite !(mul0R, mulR0, addR0, add0R).
  rewrite H1 add0R in Hpmf1.
  rewrite Hpmf1 log_1.
  rewrite !(mul0R, mulR0, addR0, add0R, mul1R, mulR1).
  field.
rewrite log_mult; last 2 first.
  case: p_01' => ? ?; fourier.
  move/eqP in H1.
Local Open Scope Rb_scope.
  by apply/RltP; rewrite Rlt_neqAle eq_sym H1 /=; apply/RleP/dist_nonneg.
rewrite log_mult; last 2 first.
  case: p_01' => ? ?; fourier.
  apply Rlt_le_neq; by [apply dist_nonneg | auto].
case: (Req_EM_T (P (Two_set.val1 card_A)) 0) => H2.
  rewrite H2.
  rewrite !(mul0R, mulR0, addR0, add0R).
  rewrite H2 addR0 in Hpmf1.
  rewrite Hpmf1.
  rewrite log_1.
  rewrite !(mul0R, mulR0, addR0, add0R, mul1R, mulR1).
  field.
rewrite log_mult; last 2 first.
  case: p_01' => ? ?; fourier.
  apply Rlt_le_neq; by [apply dist_nonneg | auto].
rewrite log_mult; last 2 first.
  case: p_01' => ? ?; fourier.
  apply Rlt_le_neq; by [apply dist_nonneg | auto].
transitivity (p * (P (Two_set.val0 card_A) + P (Two_set.val1 card_A)) * log p  + (1 - p) * (P (Two_set.val0 card_A) + P (Two_set.val1 card_A)) * log (1 - p) ).
  by field.
rewrite Hpmf1; by field.
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
rewrite {1}/entropy /=.
rewrite /index_enum -enumT Two_set.enum big_cons /= big_cons /= big_nil /= !addR0.
rewrite !OutDist.dE.
rewrite /index_enum -enumT Two_set.enum big_cons /= big_cons /= big_cons /=
  big_cons /= big_nil /= big_nil /= !addR0.
rewrite !BSC.cE /BSC.f !eqxx !(negbTE (Two_set.val0_neq_val1 card_A)).
move: (Two_set.val0_neq_val1 card_A).
rewrite eq_sym => /negbTE ->.
have P1 : P (Two_set.val0 card_A) + P (Two_set.val1 card_A) = 1.
  rewrite -(pmf1 P) /index_enum -enumT Two_set.enum big_cons /= big_cons /= big_nil /=; by field.
have -> : p * P (Two_set.val0 card_A) + (1 - p) * P (Two_set.val1 card_A) = 1 - ((1 - p) * P (Two_set.val0 card_A) + p * P (Two_set.val1 card_A)).
  rewrite -{2}P1; by field.
have H01 : 0 < ((1 - p) * P (Two_set.val0 card_A) + p * P (Two_set.val1 card_A)) < 1.
  move: (dist_nonneg P (Two_set.val0 card_A)) => H1.
  move: (dist_max P (Two_set.val1 card_A)) => H4.
  move: (dist_max P (Two_set.val0 card_A)) => H3.
  case: p_01' => Hp1 Hp2.
  split.
    case/Rle_lt_or_eq_dec : H1 => H1.
    - apply Rplus_lt_le_0_compat.
      apply Rmult_lt_0_compat; fourier.
      apply Rmult_le_pos; fourier.
    - rewrite -H1 mulR0 add0R.
      have -> : P (Two_set.val1 card_A) = 1 by rewrite -P1 -H1 add0R.
      by rewrite mulR1.
  rewrite -{2}P1.
  case: (Req_EM_T (P (Two_set.val0 card_A)) 0) => Hi.
    rewrite Hi mulR0 !add0R.
    rewrite Hi add0R in P1.
    by rewrite P1 mulR1.
  case: (Req_EM_T (P (Two_set.val1 card_A)) 0) => Hj.
    rewrite Hj addR0 in P1.
    rewrite Hj mulR0 !addR0 P1 mulR1.
    fourier.
    case/Rle_lt_or_eq_dec : H1 => H1.
    - apply Rplus_le_lt_compat.
      + rewrite -{2}(mul1R (P (Two_set.val0 card_A))).
        apply Rmult_le_compat_r; fourier.
      + rewrite -{2}(mul1R (P (Two_set.val1 card_A))).
        apply Rmult_lt_compat_r => //.
        apply Rlt_le_neq; by [apply dist_nonneg | auto].
    - rewrite -H1 mulR0 2!add0R.
      have -> : P (Two_set.val1 card_A) = 1 by rewrite -P1 -H1 add0R.
      by rewrite mulR1.
rewrite (_ : forall a b, - (a + b) = - a - b); last by move=> *; field.
rewrite -Ropp_mult_distr_l_reverse.
set q := (1 - p) * P (Two_set.val0 card_A) + p * P (Two_set.val1 card_A).
eapply (Rle_trans _ (H2 q)); last by apply H2_max.
rewrite /H2 !Ropp_mult_distr_l; apply Req_le; field.
Qed.

Lemma bsc_out_H_half' : 0 < INR 1 / INR 2 < 1.
Proof. rewrite /= (_ : INR 1 = 1) // (_ : INR 2 = 2) //; split; fourier. Qed.

Lemma H_out_binary_uniform :
  `H(Uniform.d card_A `o BSC.c card_A p_01) = 1.
Proof.
rewrite {1}/entropy.
rewrite /index_enum -enumT Two_set.enum.
rewrite big_cons /= big_cons /= big_nil /= !addR0.
rewrite !OutDist.dE.
rewrite /index_enum -enumT Two_set.enum.
(do 2 rewrite big_cons /= big_cons /= big_nil /=); rewrite !addR0.
rewrite !BSC.cE /BSC.f !eqxx !(negbTE (Two_set.val0_neq_val1 card_A)).
move: (Two_set.val0_neq_val1 card_A).
rewrite eq_sym => /negbTE ->.
rewrite -!mulRDl (_ : 1 - p + p = 1); last by field.
rewrite mul1R (_ : p + (1 - p) = 1); last by field.
rewrite mul1R -!mulRDl /Uniform.f card_A.
rewrite (_ : INR 1 = 1) // (_ : INR 2 = 2) // /Rdiv mul1R log_Rinv; last by fourier.
rewrite log_2 /=; field.
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
transitivity ((\rmul_(i < n | (f m) ``_ i == y ``_ i) (1 - p)) *
              (\rmul_(i < n | (f m) ``_ i != y ``_ i) p))%R.
  rewrite (bigID [pred i | (f m) ``_ i == y ``_ i]) /=.
  congr (_ * _).
  by apply eq_bigr => // i /eqP ->; rewrite BSC.cE /BSC.f eqxx.
  apply eq_bigr => //= i /negbTE Htmp; rewrite BSC.cE /BSC.f; by rewrite Htmp.
congr (_ * _).
by rewrite big_const /= iter_Rmult /= card_dHC.
by rewrite big_const /= iter_Rmult /= card_dH_vec.
Qed.

Local Close Scope vec_ext_scope.

End dH_BSC.
