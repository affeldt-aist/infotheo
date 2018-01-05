(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype finfun bigop finset.
Require Import Reals Fourier.
Require Import Reals_ext Ranalysis_ext ssr_ext log2 ln_facts Rbigop Rssr proba.
Require Import divergence log_sum variation_dist.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope divergence_scope.

Local Notation "0" := (false).
Local Notation "1" := (true).

Section bipart_sect.

Variable A : finType.
Variable A_ : bool -> {set A}.
Hypothesis dis : A_ 0 :&: A_ 1 = set0.
Hypothesis cov : A_ 0 :|: A_ 1 = [set: A].
Variable P : dist A.

Definition bipart_pmf i := \rsum_(a in A_ i) P a.

Definition bipart : dist [finType of bool].
apply makeDist with bipart_pmf.
- move=> a; apply: Rle_big_0_P_g. by move=> *; apply dist_nonneg.
- rewrite /index_enum -enumT Two_set.enum /=.
    symmetry; by rewrite card_bool.
  move=> HX.
  rewrite /bipart_pmf big_cons /= big_cons /= big_nil /= Rplus_0_r.
  set b0 := Two_set.val0 HX.
  set b1 := Two_set.val1 HX.
  have : b0 <> b1.
    apply/eqP.
    by apply Two_set.val0_neq_val1.
  wlog : b0 b1 / (b0 == false) && (b1 == true).
    move=> Hwlog b01.
    have : ((b0, b1) == (true, false)) || ((b0, b1) == (false, true)).
      move: b0 b1 b01; by case; case.
    case/orP; case/eqP => -> ->.
    - rewrite Rplus_comm; by apply Hwlog.
    - by apply Hwlog.
  case/andP => /eqP -> /eqP -> _.
  transitivity (\rsum_(a | (a \in A_ 0 :|: A_ 1)) P a).
    by rewrite [X in _ = X](@rsum_union _ (A_ 0) (A_ 1)) // -setI_eq0 setIC dis eqxx.
  rewrite cov -(pmf1 P).
  apply eq_bigl => /= x; by rewrite in_setT inE.
Defined.

End bipart_sect.

(** * Partition inequality (special case for distributions other sets with two elements) *)

Local Open Scope proba_scope.
Local Open Scope reals_ext_scope.

Section bipart_lem.

Variable A : finType.
Variable A_ : bool -> {set A}.
Hypothesis dis : A_ 0 :&: A_ 1 = set0.
Hypothesis cov : A_ 0 :|: A_ 1 = setT.
Variable P Q : dist A.
Hypothesis P_dom_by_Q : P << Q.

Let P_A := bipart dis cov P.
Let Q_A := bipart dis cov Q.

Lemma partition_inequality : D(P_A || Q_A) <= D(P || Q).
Proof.
have -> : D(P || Q) = \rsum_(a in A_ 0) P a * log (P a / Q a) +
                      \rsum_(a in A_ 1) P a * log (P a / Q a).
  rewrite /div -(@rsum_union _ _ _ [set: A]) //; last first.
    by rewrite -setI_eq0 setIC dis eqxx.
  apply eq_big => // a.
    by rewrite in_set inE.
  move=> _.
  case/Rle_lt_or_eq_dec: (dist_nonneg P a) => Pa.
    case/Rle_lt_or_eq_dec: (dist_nonneg Q a) => Qa.
      rewrite log_mult //; last by apply Rinv_0_lt_compat.
    by rewrite log_Rinv.
    symmetry in Qa. rewrite (P_dom_by_Q Qa) in Pa. by apply Rlt_irrefl in Pa.
  by rewrite -Pa 2!mul0R.
have step2 :
  (\rsum_(a in A_ 0) P a) * log ((\rsum_(a in A_ 0) P a) / \rsum_(a in A_ 0) Q a) +
  (\rsum_(a in A_ 1) P a) * log ((\rsum_(a in A_ 1) P a) / \rsum_(a in A_ 1) Q a) <=
  \rsum_(a in A_ 0) P a * log (P a / Q a) + \rsum_(a in A_ 1) P a * log (P a / Q a).
  apply Rplus_le_compat; by apply log_sum.
eapply Rle_trans; last by apply step2.
clear step2.
rewrite [X in _ <= X](_ : _ =
  P_A 0 * log ((P_A 0) / (Q_A 0)) + P_A 1 * log ((P_A 1) / (Q_A 1))) //.
rewrite /div /index_enum -enumT Two_set.enum.
  symmetry; by rewrite card_bool.
move=> b.
rewrite big_cons big_cons big_nil Rplus_0_r 2!(_ : _ \in _ = true) //.
move: (Two_set.val0_neq_val1 b).
set b0 := Two_set.val0 b.
set b1 := Two_set.val1 b.
wlog : b0 b1 / (b0 == 0) && (b1 == 1).
  move=> Hwlog i0i1.
  have : ((b0, b1) == (1, 0)) || ((b0, b1) == (0, 1)).
    destruct b0; destruct b1 => //.
    move: b0 b1 i0i1.
    case=> //.
      case=> // _ _.
      rewrite Rplus_comm.
      by apply Hwlog.
    case=> // _ _.
    by apply Hwlog.
case/andP => /eqP -> /eqP -> _.
clear b0 b1.
have [A0_P_neq0 | A0_P_0] : {0 < P_A 0} + {0%R = P_A 0}.
  apply Rle_lt_or_eq_dec; apply: Rle_big_0_P_g => i _; by apply dist_nonneg.
- have [A1_Q_neq0 | A1_Q_0] : {0 < Q_A 1} + {0%R = Q_A 1}.
    apply Rle_lt_or_eq_dec; apply: Rle_big_0_P_g => i _; by apply dist_nonneg.
  + have [A0_Q__neq0 | A0_Q_0] : {0 < Q_A 0} + {0%R = Q_A 0}.
      apply Rle_lt_or_eq_dec. apply: Rle_big_0_P_g => i _; by apply dist_nonneg.
    * rewrite /Rdiv log_mult; last 2 first.
        assumption.
        by apply Rinv_0_lt_compat.
      rewrite log_Rinv //.
      have [ A1_P_neq0 | A1_P_0] : {0 < P_A 1} + {0%R = P_A 1}.
        apply Rle_lt_or_eq_dec. apply: Rle_big_0_P_g => i _; by apply dist_nonneg.
      - rewrite log_mult; last 2 first.
          assumption.
          by apply Rinv_0_lt_compat.
        rewrite log_Rinv //.
        apply Req_le; by field.
      - rewrite -A1_P_0 !mul0R addR0; by apply Req_le.
    * move/(Req_0_rmul_inv (dist_nonneg Q)) in A0_Q_0.
      have {A0_Q_0}A0_Q_0 : forall i : A, i \in A_ 0 -> 0%R = P i.
        move=> i Hi; by rewrite P_dom_by_Q // -A0_Q_0.
      have Habs : P_A 0 = 0%R.
        transitivity (\rsum_(H|H \in A_ 0) 0%R).
          apply eq_big => // i Hi; by rewrite -A0_Q_0.
        by rewrite big_const iter_Rplus_Rmult mulR0.
      move: A0_P_neq0.
      rewrite Habs; by move/Rlt_irrefl.
  + have H2 : P_A 1 = 0%R.
      move/(Req_0_rmul_inv (dist_nonneg Q)) in A1_Q_0.
      rewrite /P_A /bipart /= /bipart_pmf (eq_bigr (fun=> 0%R)).
      by rewrite big_const iter_Rplus mulR0.
      move=> a a_A_1; by rewrite P_dom_by_Q // -A1_Q_0.
    rewrite H2 !mul0R !addR0.
    have H3 : Q_A 0 = 1%R.
      rewrite -[X in X = _]Rplus_0_r [X in _ + X = _]A1_Q_0 -(pmf1 Q).
      symmetry.
      rewrite -(@rsum_union _ _ _ [set: A]) //.
      apply eq_bigl => i; by rewrite in_set inE.
      by rewrite -setI_eq0 -dis setIC.
    rewrite H3 /Rdiv log_mult; last 2 first.
      assumption.
      fourier.
    rewrite log_Rinv; last by fourier.
    apply Req_le; by field.
- have H1 : P_A 1 = 1%R.
    rewrite -[X in X = _]Rplus_0_l [X in X + _ = _]A0_P_0 -(pmf1 P).
    symmetry.
    rewrite -(@rsum_union _ _ _ [set: A]) //.
    apply eq_bigl => i; by rewrite in_set inE.
    by rewrite -setI_eq0 -dis setIC.
  have [A1_Q_neq0 | A1_Q_0] : {0 < Q_A 1} + {0%R = Q_A 1}.
    apply Rle_lt_or_eq_dec. apply: Rle_big_0_P_g => i _; by apply dist_nonneg.
  + rewrite -A0_P_0 !mul0R !add0R H1 !mul1R.
    rewrite /Rdiv log_mult; last 2 first.
      fourier.
      by apply Rinv_0_lt_compat.
    rewrite log_Rinv //; apply Req_le; by field.
  + (* contradiction H1 / Bi_true_Q_0 *)
    move/(Req_0_rmul_inv (dist_nonneg Q)) in A1_Q_0.
    have : P_A 1 = 0%R.
      rewrite /P_A /bipart /= /bipart_pmf (eq_bigr (fun=> 0%R)).
      by rewrite big_const iter_Rplus mulR0.
      move=> a a_A_1; by rewrite P_dom_by_Q // -A1_Q_0.
    move=> abs; rewrite abs in H1. fourier.
Qed.

End bipart_lem.
