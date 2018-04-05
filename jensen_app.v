From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.

Require Import Reals Fourier ProofIrrelevance FunctionalExtensionality.
Require Import Rssr Reals_ext ssr_ext ssralg_ext log2 Rbigop.
Require Import proba jensen num_occ.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section string_concat.

Variable A : finType.

Definition minlen (s : seq A) :=
  \rsum_(c <- s) log (INR (size s) / INR (num_occ c s)).

Definition Hs0 (s : seq A) :=
  / INR (size s) * minlen s.

Lemma sum_num_occ (s : seq A) : \sum_(a in A) num_occ a s = size s.
Proof.
elim: s => [|a s IH] /=.
+ by apply big1_eq.
+ rewrite big_split /= IH -big_mkcond /= (big_pred1 a) //.
  by move=> i; rewrite eq_sym.
Qed.

Definition Hs (s : seq A) :=
 \rsum_(a in A)
  if num_occ a s == 0%nat then 0 else
  INR (num_occ a s) / INR (size s) * log (INR (size s) / INR (num_occ a s)).

Definition nHs (s : seq A) :=
 \rsum_(a in A)
  if num_occ a s == 0%nat then 0 else
  INR (num_occ a s) * log (INR (size s) / INR (num_occ a s)).

Lemma szHs_is_nHs s : INR (size s) * Hs s = nHs s.
Proof.
rewrite /Hs /nHs big_distrr.
apply eq_bigr => i _ /=.
case: ifP => Hnum.
  by rewrite mulR0.
rewrite /Rdiv (mulRC (INR (num_occ i s))) 2!(mulRA (INR _)).
rewrite !mulRV ?mul1R //.
apply not_0_INR => Hsz.
move: (count_size (pred1 i) s).
by rewrite Hsz leqn0 Hnum.
Qed.

Theorem concat_entropy s1 s2 :
  INR (size s1) * Hs s1 + INR (size s2) * Hs s2
  <= INR (size (s1 ++ s2)) * Hs (s1 ++ s2).
Proof.
rewrite !szHs_is_nHs.
rewrite /nHs -big_split /=.
apply ler_rsum => i _.
rewrite /num_occ count_cat size_cat.
case: ifP => Hs1.
  rewrite (eqP Hs1) !add0n add0R.
  case: ifP => Hs2.
    by apply Rle_refl.
  have cnt_s2_gt0: 0 < INR (count_mem i s2).
    apply lt_0_INR.
    apply /leP.
    by rewrite lt0n Hs2.
  have cnt_lt_size t: INR ((count_mem i) t) <= INR (size t).
    apply le_INR.
    apply/leP.
    by apply count_size.
  have sz_s2_gt0: 0 < INR (size s2).
    apply (Rlt_le_trans _ _ _ cnt_s2_gt0).
    by apply cnt_lt_size.
  apply Rmult_le_compat_l.
    by apply Rlt_le.
  apply log_increasing_le.
    by apply Rlt_mult_inv_pos.
  apply Rmult_le_compat_r.
    by apply Rlt_le, invR_gt0, cnt_s2_gt0.
  apply le_INR.
  apply /leP.
  by apply leq_addl.
have cnt_s1_gt0: 0 < INR (count_mem i s1).
  apply lt_0_INR.
  apply /leP.
  by rewrite lt0n Hs1.
have cnt_lt_size t: INR ((count_mem i) t) <= INR (size t).
  apply le_INR.
  apply/leP.
  by apply count_size.
have sz_s1_gt0: 0 < INR (size s1).
  apply (Rlt_le_trans _ _ _ cnt_s1_gt0).
  by apply cnt_lt_size.
case: ifP => Hs2.
  rewrite (eqP Hs2) !addn0 addR0 Hs1.
  apply Rmult_le_compat_l.
    by apply Rlt_le.
  apply log_increasing_le.
    by apply Rlt_mult_inv_pos.
  apply Rmult_le_compat_r.
    by apply Rlt_le, invR_gt0, cnt_s1_gt0.
  apply le_INR.
  apply /leP.
  by apply leq_addr.
case: ifP => Hs12.
  by rewrite addn_eq0 Hs1 in Hs12.
(* Then we should use jensen_dist *)
Abort.