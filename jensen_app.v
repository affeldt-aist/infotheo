From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.

Require Import Reals Fourier ProofIrrelevance FunctionalExtensionality.
Require Import Rssr Reals_ext ssr_ext ssralg_ext log2 Rbigop.
Require Import proba jensen num_occ.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope num_occ_scope.
Local Coercion INR : nat >-> R.

Reserved Notation "n %:R" (at level 2, left associativity, format "n %:R").
Local Notation "n %:R" := (INR n).

Section string_concat.

Variable A : finType.

Definition minlen (s : seq A) :=
  \rsum_(c <- s) log (size s / N(c|s)).

Definition Hs0 (s : seq A) :=
  / (size s) * minlen s.

Lemma sum_num_occ (s : seq A) : \sum_(a in A) N(a|s) = size s.
Proof.
elim: s => [|a s IH] /=.
+ by apply big1_eq.
+ rewrite big_split /= IH -big_mkcond /= (big_pred1 a) //.
  by move=> i; rewrite eq_sym.
Qed.

Definition Hs (s : seq A) :=
 \rsum_(a in A)
  if N(a|s) == 0%nat then 0 else
  N(a|s) / size s * log (size s / N(a|s)).


Definition nHs (s : seq A) :=
 \rsum_(a in A)
  if N(a|s) == 0%nat then 0 else
  N(a|s) * log (size s / N(a|s)).

Lemma szHs_is_nHs s : size s * Hs s = nHs s.
Proof.
rewrite /Hs /nHs big_distrr.
apply eq_bigr => i _ /=.
case: ifP => Hnum.
  by rewrite mulR0.
rewrite /Rdiv (mulRC N(i|s)) 2!(mulRA _%:R).
rewrite !mulRV ?mul1R // ?INR_eq0.
apply/eqP => Hsz.
move: (count_size (pred1 i) s).
by rewrite Hsz leqn0 Hnum.
Qed.

Lemma log_concave_gt0 x y t :
  0 < x -> 0 < y -> 0 <= t <= 1 -> concave_leq log x y t.
Admitted.

Definition simplR := (add0R, addR0, subR0, mul0R, mulR0, mul1R, mulR1).

Lemma Rpos_convex : convex_interval (fun x =>  0 < x).
Proof.
move=> x y t Hx Hy Ht.
case Ht0: (t == 0); first by rewrite (eqP Ht0) !simplR.
apply Rplus_lt_le_0_compat.
  apply mulR_gt0 => //.
  case/proj1: Ht Ht0 => // ->; by rewrite eqxx.
apply Rmult_le_pos; [apply (Rplus_le_reg_l t) | by apply Rlt_le].
rewrite addR0 Rplus_minus; exact/(proj2 Ht).
Qed.

Definition Rpos_interval := mkInterval Rpos_convex.

Lemma log_concave : concave_in Rpos_interval log.
Proof. by move=> x; apply log_concave_gt0. Qed.

Lemma num_occ_flatten (a:A) ss :
  N(a|flatten ss) = \sum_(s <- ss) N(a|s).
Proof.
rewrite /num_occ.
elim: ss => [|s ss IH] /=.
  by rewrite big_nil.
by rewrite big_cons /= count_cat IH.
Qed.

Definition big_morph_plus_INR := big_morph INR morph_plus_INR (erefl 0%:R).

Hint Resolve Rle_refl pos_INR.

Theorem concats_entropy ss :
  \rsum_(s <- ss) size s * Hs s
       <= size (flatten ss) * Hs (flatten ss).
Proof.
(* (1) First simplify formula *)
rewrite szHs_is_nHs.
rewrite (eq_bigr _ (fun i _ => szHs_is_nHs i)).
rewrite exchange_big /nHs /=.
(* (2) Move to per-character inequalities *)
apply ler_rsum=> a _.
(* Remove strings containing no occurrences *)
rewrite (bigID (fun s => N(a|s) == O)) /=.
rewrite big1; last by move=> i ->.
rewrite num_occ_flatten add0R.
rewrite [in X in _ <= X](bigID (fun s => N(a|s) == O)).
rewrite [in X in _ <= X]big1 //= ?add0n;
  last by move=> i /eqP.
rewrite (eq_bigr
       (fun i => log (size i / N(a|i)) * N(a|i)));
  last by move=> i /negbTE ->; rewrite mulRC.
rewrite -big_filter -[in X in _ <= X]big_filter.
(* ss' contains only strings with ocurrences *)
set ss' := [seq s <- ss | N(a|s) != O].
case Hss': (ss' == [::]).
  by rewrite (eqP Hss') !big_nil eqxx.
have Hnum s : s \in ss' -> (N(a|s) > 0)%nat.
  by rewrite /ss' mem_filter lt0n => /andP [->].
have Hnum': 0 < N(a|flatten ss').
  apply /lt_0_INR /leP.
  destruct ss' => //=.
  rewrite /num_occ count_cat ltn_addr //.
  by rewrite Hnum // in_cons eqxx.
have Hsz: 0 < size (flatten ss').
  apply (Rlt_le_trans _ _ _ Hnum').
  by apply /le_INR /leP /count_size.
apply (Rle_trans _ ((\sum_(i <- ss') N(a|i))%:R *
    log (size (flatten ss') /
      \sum_(i <- ss') N(a|i))));
  last first.
  (* Not mentioned in the book: one has to compensate for the discarding
     of strings containing no occurences.
     Works thanks to monotonicity of log. *)
  (* (3) Compensate for removed strings *)
  case: ifP => Hsum.
    by rewrite (eqP Hsum) mul0R.
  apply Rmult_le_compat_l => //.
  apply Log_increasing_le => //.
    apply Rlt_mult_inv_pos => //.
    apply/lt_0_INR/ltP.
    by rewrite lt0n Hsum.
  apply Rmult_le_compat_r.
    apply /Rlt_le /invR_gt0 /lt_0_INR /ltP.
    by rewrite lt0n Hsum.
  apply /le_INR /leP.
  rewrite !size_flatten !sumn_big_addn.
  rewrite !big_map big_filter.
  rewrite [in X in (_ <= X)%nat]
    (bigID (fun s => N(a|s) == O)) /=.
  by apply leq_addl.
(* (4) Prepare to use jensen_dist_concave *)
set f := fun i =>
  N(a|tnth (in_tuple ss') i) / N(a|flatten ss').
set r := fun i =>
  (size (tnth (in_tuple ss') i)) / N(a|tnth (in_tuple ss') i).
have f_pos i : 0 < f i.
  apply Rlt_mult_inv_pos => //.
  apply /lt_0_INR /ltP.
  by rewrite Hnum // mem_tnth.
have f_nonneg i : 0 <= f i by apply Rlt_le.
have f_1 : \rsum_(a < size ss')
    (mkPosFun f_nonneg) a = 1.
  rewrite /= /f -big_distrl /= num_occ_flatten.
  rewrite -big_morph_plus_INR.
  rewrite -(big_tnth _ _ _ xpredT).
  rewrite mulRV // INR_eq0.
  destruct ss' => //=.
  rewrite big_cons addn_eq0 negb_and -lt0n.
  by rewrite Hnum // in_cons eqxx.
set d := mkDist f_1.
have Hr: forall i, Rpos_interval (r i).
  rewrite /r /= => i.
  apply Rlt_mult_inv_pos.
    apply /lt_0_INR /ltP /(@leq_trans N(a|tnth (in_tuple ss') i)).
      by rewrite Hnum // mem_tnth.
    by apply count_size.
  by apply /lt_0_INR /ltP; rewrite Hnum // mem_tnth.
(* (5) Apply Jensen *)
move: (jensen_dist_concave log_concave d Hr).
rewrite /d /f /r /=.
rewrite -(big_tnth _ _ _ xpredT
  (fun s =>
     log ((size s) / N(a|s)) *
     (N(a|s) / N(a|flatten ss')))).
rewrite -(big_tnth _ _ _ xpredT
  (fun s =>
     (size s) / N(a|s) *
     (N(a|s) / N(a|flatten ss')))).
(* (6) Transform the statement to match the goal *)
move/(Rmult_le_compat_r N(a|flatten ss') _ _ (pos_INR _)).
rewrite !big_distrl /=.
rewrite (eq_bigr
     (fun i => log (size i / N(a|i)) * N(a|i)));
  last first.
  move=> i _; rewrite !mulRA -mulRA mulVR ?mulR1 //.
  exact/eqP/gtR_eqF.
move/Rle_trans; apply. (* LHS matches *)
rewrite mulRC -num_occ_flatten big_filter.
rewrite (eq_bigr
     (fun i => size i * / N(a|flatten ss')));
  last first.
  move=> i Hi; rewrite !mulRA -(mulRA _ (/ _)).
  by rewrite mulVR ?mulR1 // INR_eq0.
rewrite -big_filter -/ss' -big_distrl -big_morph_plus_INR /=.
by rewrite size_flatten sumn_big_addn big_map.
Qed.

End string_concat.

Section zero_order_empirical_entropy.

Local Open Scope proba_scope.

Variable A : finType.
Hypothesis A0 : (0 < #|A|)%nat.

Definition dist_of_seq (s : seq A) : {dist A}.
Proof.
case/card_gt0P/sigW : A0 => a _.
pose f := fun a => if a \in s then N(a|s)%:R / (size s)%:R else 0.
have f0 : forall a : A, 0 <= f a.
  move=> b; rewrite /f; case: ifPn => _; last exact/Rle_refl.
  apply mulR_ge0; first by apply/RleP; rewrite leR0n.
  apply/ltRW/invR_gt0.
  admit.
pose fpos := mkPosFun f0.
have f1 : \rsum_(a in A) f a = 1.
  rewrite (bigID [pred x | a \in s]) /=.
  admit.
exact: (makeDist f0 f1).
Admitted.

Require Import entropy.
Local Open Scope entropy_scope.

Definition H0 (s : seq A) := `H (dist_of_seq s).

Lemma H0E (s : seq A) : H0 s = Hs s.
Proof.
rewrite /H0 /entropy /Hs (big_morph _ morph_Ropp oppR0); apply/eq_bigr => a _.
(* TODO *)
Abort.

End zero_order_empirical_entropy.
