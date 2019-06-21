(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.
Require Import Reals ProofIrrelevance FunctionalExtensionality.
Require Import ssrR Reals_ext ssr_ext ssralg_ext logb Rbigop.
Require Import proba entropy convex ln_facts jensen num_occ.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.
Local Open Scope num_occ_scope.
Local Open Scope entropy_scope.
Local Coercion INR : nat >-> R.

Definition simplR := (add0R, addR0, subR0, mul0R, mulR0, mul1R, mulR1).

Local Hint Resolve leRR.
Local Hint Resolve leR0n.

Section seq_nat_dist.

Variable A : finType.
Variable f : A -> nat.
Variable total : nat.
Hypothesis sum_f_total : (\sum_(a in A) f a)%nat = total.
Hypothesis total_gt0 : total != O.

Let f_div_total := [ffun a : A => f a / total].

Lemma f_div_total_pos c : 0 <= f_div_total c.
Proof.
rewrite ffunE; apply mulR_ge0 => //.
apply /Rlt_le /invR_gt0 /ltR0n.
by rewrite lt0n.
Qed.

Lemma f_div_total_1 : \sum_(a in A) [ffun a : A => f a / total] a = 1.
Proof.
evar (h : A -> R); rewrite (eq_bigr h); last first.
  move=> a _ /=; rewrite /f_div_total ffunE /h; reflexivity.
rewrite {}/h /f_div_total -big_distrl -big_morph_natRD.
by rewrite sum_f_total /= mulRV // INR_eq0'.
Qed.

Definition seq_nat_dist := makeDist f_div_total_pos f_div_total_1.

End seq_nat_dist.

Section string.

Variable A : finType.

(* TODO: move?*)
Section num_occ.

Lemma sum_num_occ s : (\sum_(a in A) N(a|s))%nat = size s.
Proof.
elim: s => [|a s IH] /=.
+ by apply big1_eq.
+ rewrite big_split /= IH -big_mkcond /= (big_pred1 a) //.
  by move=> i; rewrite eq_sym.
Qed.

Lemma num_occ_flatten (a:A) ss :
  N(a|flatten ss) = (\sum_(s <- ss) N(a|s))%nat.
Proof.
rewrite /num_occ.
elim: ss => [|s ss IH] /=; first by rewrite big_nil.
by rewrite big_cons /= count_cat IH.
Qed.

End num_occ.

Section entropy.
Variable S : seq A.
Hypothesis S_nonempty : size S != O.

Definition pchar c := N(c|S) / size S.

Definition num_occ_dist := seq_nat_dist (sum_num_occ S) S_nonempty.

Definition Hs0 := `H num_occ_dist.
End entropy.

Section string_concat.

(*
Definition Hs (s : seq A) :=
 \rsum_(a in A)
  if N(a|s) == 0%nat then 0 else
  N(a|s) / size s * log (size s / N(a|s)).
*)

Definition nHs (s : seq A) :=
 \sum_(a in A)
  if N(a|s) == 0%nat then 0 else
  N(a|s) * log (size s / N(a|s)).

Lemma szHs_is_nHs s (H : size s != O) :
  size s * `H (@num_occ_dist s H) = nHs s.
Proof.
rewrite /entropy /nHs /num_occ_dist /= -mulRN1 big_distrl big_distrr /=.
apply eq_bigr => a _ /=; rewrite ffunE.
case: ifPn => [/eqP -> | Hnum]; first by rewrite !mulRA !simplR.
rewrite {1}/Rdiv (mulRC N(a | s)) 3![in LHS]mulRA mulRV ?INR_eq0' // ?mul1R.
rewrite -mulRA mulRN1 -logV; last by apply divR_gt0; rewrite ltR0n lt0n.
rewrite Rinv_Rdiv //; apply/eqP; by rewrite INR_eq0'.
Qed.

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
do 2!f_equal; apply eq_irrelevance.
Qed.

Lemma szHs_is_nHs_full s : mulnRdep (size s) (fun H => Hs0 H) = nHs s.
Proof.
rewrite /mulnRdep; destruct boolP; last by apply szHs_is_nHs.
rewrite /nHs (eq_bigr (fun a => 0)); first by rewrite big1.
move=> a _; suff -> : N(a|s) == O by [].
by rewrite /num_occ -leqn0 -(eqP i) count_size.
Qed.

Theorem concats_entropy ss :
(*  \rsum_(s <- ss) size s * Hs s
       <= size (flatten ss) * Hs (flatten ss). *)
(* \rsum_(s <- ss) mulnRdep (size s) (fun H => Hs0 H)
       <= mulnRdep (size (flatten ss)) (fun H => Hs0 H). *)
  \sum_(s <- ss) nHs s <= nHs (flatten ss).
Proof.
(* (1) First simplify formula *)
(*rewrite szHs_is_nHs.
rewrite (eq_bigr _ (fun i _ => szHs_is_nHs i)).*)
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
       (fun i => N(a|i) * log (size i / N(a|i))));
  last by move=> i /negbTE ->.
rewrite -big_filter -[in X in _ <= X]big_filter.
(* ss' contains only strings with ocurrences *)
set ss' := [seq s <- ss | N(a|s) != O].
case/boolP: (ss' == [::]) => Hss'.
  by rewrite (eqP Hss') !big_nil eqxx.
have Hnum s : s \in ss' -> (N(a|s) > 0)%nat.
  by rewrite /ss' mem_filter lt0n => /andP [->].
have Hnum': 0 < N(a|flatten ss').
  apply /ltR0n; destruct ss' => //=.
  rewrite /num_occ count_cat ltn_addr //.
  by rewrite Hnum // in_cons eqxx.
have Hsz: 0 < size (flatten ss').
  apply (ltR_leR_trans Hnum').
  by apply /le_INR /leP /count_size.
apply (@leR_trans ((\sum_(i <- ss') N(a|i))%:R *
    log (size (flatten ss') /
      (\sum_(i <- ss') N(a|i))%nat)));
  last first.
  (* Not mentioned in the book: one has to compensate for the discarding
     of strings containing no occurences.
     Works thanks to monotonicity of log. *)
  (* (3) Compensate for removed strings *)
  case: ifP => Hsum.
    by rewrite (eqP Hsum) mul0R.
  apply leR_wpmul2l => //.
  apply Log_increasing_le => //.
    apply/mulR_gt0 => //.
    apply/invR_gt0/ltR0n.
    by rewrite lt0n Hsum.
  apply leR_wpmul2r.
    apply /Rlt_le /invR_gt0 /ltR0n.
    by rewrite lt0n Hsum.
  apply /le_INR /leP.
  rewrite !size_flatten !sumn_big_addn.
  rewrite !big_map big_filter.
  rewrite [in X in (_ <= X)%nat]
    (bigID (fun s => N(a|s) == O)) /=.
  by apply leq_addl.
(* (4) Prepare to use jensen_dist_concave *)
have Htotal := esym (num_occ_flatten a ss').
rewrite big_tnth in Htotal.
have Hnum2 : N(a|flatten ss') != O.
  rewrite -lt0n -ltR0n'; exact/ltRP.
set d := seq_nat_dist Htotal Hnum2.
set r := fun i =>
  (size (tnth (in_tuple ss') i))
  / N(a|tnth (in_tuple ss') i).
have Hr: forall i, r i \in Rpos_interval.
  rewrite /r /= => i.
  rewrite classical_sets.in_setE; apply Rlt_mult_inv_pos; apply /ltR0n.
    apply (@leq_trans N(a|tnth (in_tuple ss') i)).
      by rewrite Hnum // mem_tnth.
    by apply count_size.
  by apply /Hnum /mem_tnth.
(* (5) Apply Jensen *)
move: (jensen_dist_concave log_concave d Hr).
rewrite /d /r /=.
evar (h : 'I_(size ss') -> R); rewrite (eq_bigr h); last first.
  move=> i _; rewrite ffunE /h; reflexivity.
rewrite {}/h.
evar (h : 'I_(size ss') -> R); rewrite [X in _ <= log X -> _](eq_bigr h); last first.
  move=> i _; rewrite ffunE /h; reflexivity.
rewrite {}/h.
rewrite -(big_tnth _ _ _ xpredT
  (fun s => (N(a|s) / N(a|flatten ss')) *
           log ((size s) / N(a|s)))).
rewrite -(big_tnth _ _ _ xpredT
  (fun s => (N(a|s) / N(a|flatten ss')) *
           (size s / N(a|s)))).
(* (6) Transform the statement to match the goal *)
move/(@leR_wpmul2r N(a|flatten ss') _ _ (leR0n _)).
rewrite !big_distrl /=.
rewrite (eq_bigr
  (fun i => N(a|i) * log (size i / N(a|i))));
  last first.
  move=> i _.
  rewrite mulRAC -!mulRA (mulRA (/ _)) mulVR ?mul1R //.
  exact/eqP/gtR_eqF.
move/leR_trans; apply. (* LHS matches *)
rewrite mulRC -num_occ_flatten big_filter.
rewrite (eq_bigr
  (fun i => size i / N(a|flatten ss')));
  last first.
  move=> i Hi; rewrite mulRCA {1}/Rdiv mulRAC.
  by rewrite mulRV ?mul1R // INR_eq0'.
rewrite -big_filter -/ss' -big_distrl.
rewrite -big_morph_natRD /=.
by rewrite size_flatten sumn_big_addn big_map.
Qed.

End string_concat.

End string.

(* tentative definition *)
Section higher_order_empirical_entropy.

Variables (A : finType) (l : seq A).
Hypothesis A0 : (O < #|A|)%nat.
Let n := size l.
Let def : A. Proof. move/card_gt0P : A0 => /sigW[def _]; exact def. Defined.
Hypothesis l0 : n != O.

(* the string consisting of the concatenation of the symbols following w in s *)
Fixpoint takes {k : nat} (w : k.-tuple A) (s : seq A) {struct s} : seq A :=
  if s is _ :: t then
    let s' := takes w t in
    if take k s == w then nth def (drop k s) O :: s' else s'
  else
    [::].

(* sample ref: https://www.dcc.uchile.cl/~gnavarro/ps/jea08.2.pdf *)
Definition hoH (k : nat) := / n%:R *
  \sum_(w in {: k.-tuple A}) #|takes w l|%:R *
    match Bool.bool_dec (size w != O) true with
      | left H => `H (num_occ_dist H)
      | _ => 0
    end.

Lemma hoH_decr (k : nat) : hoH k.+1 <= hoH k.
Proof.
rewrite /hoH; apply/leRP; rewrite leR_pmul2l'; last first.
  by apply/ltRP/invR_gt0/ltRP; rewrite ltR0n' lt0n.
(* TODO *)
Abort.

End higher_order_empirical_entropy.
