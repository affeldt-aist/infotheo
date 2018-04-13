From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.

Require Import Reals Fourier ProofIrrelevance FunctionalExtensionality.
Require Import Rssr Reals_ext ssr_ext ssralg_ext log2 Rbigop.
Require Import proba entropy jensen num_occ.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope num_occ_scope.
Local Open Scope entropy_scope.
Local Coercion INR : nat >-> R.

Reserved Notation "n %:R" (at level 2, left associativity, format "n %:R").
Local Notation "n %:R" := (INR n).

Lemma log_concave_gt0 x y t :
  0 < x -> 0 < y -> 0 <= t <= 1 -> concave_leq log x y t.
Admitted.

Section string.

Variable A : finType.

Definition simplR := (add0R, addR0, subR0, mul0R, mulR0, mul1R, mulR1).

Definition big_morph_plus_INR := big_morph INR morph_plus_INR (erefl 0%:R).

Hint Resolve Rle_refl pos_INR.

Section num_occ.

Lemma sum_num_occ s : \sum_(a in A) N(a|s) = size s.
Proof.
elim: s => [|a s IH] /=.
+ by apply big1_eq.
+ rewrite big_split /= IH -big_mkcond /= (big_pred1 a) //.
  by move=> i; rewrite eq_sym.
Qed.

Lemma num_occ_flatten (a:A) ss :
  N(a|flatten ss) = \sum_(s <- ss) N(a|s).
Proof.
rewrite /num_occ.
elim: ss => [|s ss IH] /=.
  by rewrite big_nil.
by rewrite big_cons /= count_cat IH.
Qed.

End num_occ.

Section seq_nat_dist.

Variable f : A -> nat.
Variable total : nat.
Hypothesis sum_f_total : \sum_(a in A) f a = total.
Hypothesis total_gt0 : total != O.

Let f_div_total (a : A) := f a / total.

Lemma f_div_total_pos c : 0 <= f_div_total c.
Proof.
apply mulR_ge0 => //.
apply /Rlt_le /invR_gt0.
apply /lt_0_INR /ltP.
by rewrite lt0n.
Qed.

Lemma f_div_total_1 : \rsum_(a in A) (mkPosFun f_div_total_pos) a = 1.
Proof.
rewrite /f_div_total -big_distrl -big_morph_plus_INR.
by rewrite sum_f_total /= mulRV // INR_eq0.
Qed.

Definition seq_nat_dist := mkDist f_div_total_1.

End seq_nat_dist.

Section entropy.

Variable S : seq A.
Hypothesis S_nonempty : size S != O.

Definition pchar c := N(c|S) / size S.

Definition pchar_dist := seq_nat_dist (sum_num_occ S) S_nonempty.

Definition Hs0 := `H pchar_dist.
End entropy.

Section string_concat.

(*
Definition Hs (s : seq A) :=
 \rsum_(a in A)
  if N(a|s) == 0%nat then 0 else
  N(a|s) / size s * log (size s / N(a|s)).
*)

Definition nHs (s : seq A) :=
 \rsum_(a in A)
  if N(a|s) == 0%nat then 0 else
  N(a|s) * log (size s / N(a|s)).

Definition mulnRdep (x : nat) (y : x != O -> R) : R.
case/boolP: (x == O) => Hx.
+ exact 0.  
+ exact (x * y Hx).
Defined.
Arguments mulnRdep x y : clear implicits.

Lemma mulnRdep_0 y : mulnRdep 0 y = 0.
Proof. rewrite /mulnRdep /=. by destruct boolP. Qed.

Lemma mulnRdep_nz x y (Hx : x != O) : mulnRdep x y = x * y Hx.
Proof.
rewrite /mulnRdep /=.
destruct boolP.
  by elimtype False; rewrite i in Hx.
do 2!f_equal.
apply eq_irrelevance.
Qed.

Lemma szHs_is_nHs s : mulnRdep (size s) (fun H => Hs0 H) = nHs s.
Proof.
rewrite /mulnRdep; destruct boolP.
  rewrite /nHs (eq_bigr (fun a => 0)); first by rewrite big1.
  move=> a _.
  suff -> : N(a|s) == O. done.
  by rewrite /num_occ -leqn0 -(eqP i) count_size.
rewrite /Hs0 /entropy /nHs /pchar_dist /=.
rewrite -mulRN1 big_distrl big_distrr /=.
apply eq_bigr => a _ /=.
case: ifP => [/eqP -> | Hnum].
  by rewrite !mulRA !simplR.
rewrite /Rdiv (mulRC N(a|s)) 3!(mulRA _%:R).
rewrite !mulRV ?mul1R // ?INR_eq0 //.
rewrite -mulRA mulRN1 /log /Log -mulNR.
rewrite -ln_Rinv.
  rewrite invRM ?invRK //.
  + by apply /eqP; rewrite INR_eq0.
  + by apply /eqP /invR_neq0; rewrite INR_eq0.
  + by apply /eqP; rewrite INR_eq0 Hnum.
apply mulR_gt0.
  by apply /invR_gt0 /lt_0_INR /ltP; rewrite lt0n.
by apply /lt_0_INR /ltP; rewrite lt0n Hnum.
Qed.

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

Theorem concats_entropy ss :
(*  \rsum_(s <- ss) size s * Hs s
       <= size (flatten ss) * Hs (flatten ss). *)
  \rsum_(s <- ss) mulnRdep (size s) (fun H => Hs0 H)
       <= mulnRdep (size (flatten ss)) (fun H => Hs0 H).
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
