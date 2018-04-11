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
rewrite !mulRV ?mul1R // ?INR_eq0.
apply/eqP => Hsz.
move: (count_size (pred1 i) s).
by rewrite Hsz leqn0 Hnum.
Qed.

Lemma log_concave_gt0 x y t :
  0 < x -> 0 < y -> 0 <= t <= 1 -> concave_leq log x y t.
Admitted.

Definition simplR := (add0R, addR0, subR0, mul0R, mulR0, mul1R, mulR1).

Lemma log_concave : concave_in (fun x => 0 < x) log.
Proof.
move=> x y t Hx Hy Ht.
split; first by apply log_concave_gt0.
case Ht0: (t == 0); first by rewrite (eqP Ht0) !simplR.
apply Rplus_lt_le_0_compat.
  apply mulR_gt0 => //.
  case/proj1: Ht Ht0 => // ->; by rewrite eqxx.
apply Rmult_le_pos; [apply (Rplus_le_reg_l t) | by apply Rlt_le].
rewrite addR0 Rplus_minus; exact/(proj2 Ht).
Qed.

Lemma num_occ_flatten (a:A) ss :
  num_occ a (flatten ss) = \sum_(s <- ss) num_occ a s.
Proof.
rewrite /num_occ.
elim: ss => [|s ss IH] /=.
  by rewrite big_nil.
by rewrite big_cons /= count_cat IH.
Qed.

Definition big_morph_plus_INR := big_morph INR morph_plus_INR (erefl (INR 0)).

Hint Resolve Rle_refl.

Theorem concats_entropy ss :
  \rsum_(s <- ss) INR (size s) * Hs s
       <= INR (size (flatten ss)) * Hs (flatten ss).
Proof.
(* First simplify formula *)
rewrite szHs_is_nHs.
rewrite (eq_bigr _ (fun i _ => szHs_is_nHs i)) exchange_big /=.
apply ler_rsum=> a _.
(* Remove string containing no occurences from the sums *)
rewrite (bigID (fun s => num_occ a s == O)) /=.
rewrite big1; last by move=> i ->.
rewrite num_occ_flatten add0R.
rewrite [in X in _ <= X](bigID (fun s => num_occ a s == O)).
rewrite [in X in _ <= X]big1 //=; last by move=> i /eqP.
rewrite (eq_bigr
       (fun i => log (INR (size i) / INR (num_occ a i)) * INR (num_occ a i)));
  last by move=> i /negbTE ->; rewrite mulRC.
rewrite -big_filter -[in X in _ <= X]big_filter add0n.
(* ss' contains only strings with ocurrences *)
set ss' := [seq s <- ss | num_occ a s != O].
case Hss': (ss' == [::]).
  by rewrite (eqP Hss') !big_nil eqxx.
have Hnum (s : seq A) : s \in ss' -> (num_occ a s > 0)%nat.
  by rewrite /ss' mem_filter lt0n => /andP [->].
have Hnum': 0 < INR (num_occ a (flatten ss')).
  apply /lt_0_INR /leP.
  destruct ss' => //=.
  rewrite /num_occ count_cat ltn_addr //.
  by rewrite Hnum // in_cons eqxx.
have Hsz: 0 < INR (size (flatten ss')).
  apply (Rlt_le_trans _ _ _ Hnum').
  by apply /le_INR /leP /count_size.
apply (Rle_trans _ (INR (\sum_(i <- ss') num_occ a i) *
    log (INR (size (flatten ss')) / INR (\sum_(i <- ss') num_occ a i))));
  last first.
  (* Not mentioned in the book: one has to compensate for the discarding
     of strings containing no occurences.
     Works thanks to monotonicity of log. *)
  case: ifP => Hsum.
    by rewrite (eqP Hsum) mul0R.
  apply Rmult_le_compat_l; first by apply pos_INR.
  apply Log_increasing_le; first by apply Rlt_1_2.
    apply Rlt_mult_inv_pos => //.
    apply/lt_0_INR/ltP.
    by rewrite lt0n Hsum.
  apply Rmult_le_compat_r.
    apply /Rlt_le /invR_gt0 /lt_0_INR /ltP.
    by rewrite lt0n Hsum.
  apply /le_INR /leP.
  rewrite !size_flatten !sumn_big_addn !big_map big_filter.
  rewrite [in X in (_ <= X)%nat](bigID (fun s => num_occ a s == O)) /=.
  by apply leq_addl.
(* Prepare to use jensen_dist_concave *)
set f := fun x =>
  INR (num_occ a (tnth (in_tuple ss') x)) / INR (num_occ a (flatten ss')).
set r := fun x =>
  INR (size (tnth (in_tuple ss') x)) / INR (num_occ a (tnth (in_tuple ss') x)).
have f_pos x : 0 < f x.
  apply Rlt_mult_inv_pos => //.
  apply /lt_0_INR /ltP.
  by rewrite Hnum // mem_tnth.
have f_nonneg x : 0 <= f x by apply Rlt_le.
have f_1 : \rsum_(a < size ss') (mkPosFun f_nonneg) a = 1.
  rewrite /= /f -big_distrl /= num_occ_flatten.
  rewrite big_morph_plus_INR mulRC big_tnth /= mulVR //.
  rewrite -big_morph_plus_INR INR_eq0.
  destruct ss' => //=.
  rewrite big_ord_recl /= (tnth_nth [::]) /=.
  by rewrite addn_eq0 negb_and -lt0n Hnum // in_cons eqxx.
set d := mkDist f_1.
have Hr: forall i, r i > 0.
  rewrite /r /= => i.
  apply Rlt_mult_inv_pos.
    apply /lt_0_INR /ltP /(@leq_trans (num_occ a (tnth (in_tuple ss') i))).
      by rewrite Hnum // mem_tnth.
    by apply count_size.
  apply /lt_0_INR /ltP.
  by rewrite Hnum // mem_tnth.
move: (jensen_dist_concave log_concave d Hr).
rewrite /d /f /r /=.
rewrite -(big_tuple _ _ _ xpredT
  (fun s =>
     log (INR (size s) / INR (num_occ a s)) *
     (INR (num_occ a s) / INR (num_occ a (flatten ss'))))).
rewrite -(big_tuple _ _ _ xpredT
  (fun s =>
     INR (size s) / INR (num_occ a s) *
     (INR (num_occ a s) / INR (num_occ a (flatten ss'))))) /=.
move/(Rmult_le_compat_r (INR (num_occ a (flatten ss'))) _ _ (pos_INR _)).
rewrite !big_distrl /=.
rewrite (eq_bigr
     (fun i => log (INR (size i) / INR (num_occ a i)) * INR (num_occ a i)));
  last first.
  move=> i _; rewrite !mulRA -mulRA mulVR ?mulR1 //.
  exact/eqP/gtR_eqF.
(* LHS do match *)
move/Rle_trans; apply.
rewrite mulRC -num_occ_flatten big_filter.
rewrite (eq_bigr
     (fun i => INR (size i) * / INR (num_occ a (flatten ss'))));
  last first.
  by move=> i Hi; rewrite !mulRA -(mulRA _ (/ _)) mulVR ?mulR1 // INR_eq0.
rewrite -big_filter -/ss' -big_distrl -big_morph_plus_INR /=.
by rewrite size_flatten sumn_big_addn big_map.
Qed.
    
End string_concat.
