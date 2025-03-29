(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import classical_sets reals exp interval_inference.
From mathcomp Require convex.
Require Import ssr_ext ssralg_ext realType_ext realType_ln.
Require Import fdist entropy convex jensen num_occ.

(**md**************************************************************************)
(* # String entropy                                                           *)
(*                                                                            *)
(* Documented in:                                                             *)
(* - Reynald Affeldt, Jacques Garrigue, and Takafumi Saikawa. Examples of     *)
(*   formal proofs about data compression. International Symposium on         *)
(*   Information Theory and Its Applications (ISITA 2018), Singapore,         *)
(*   October 28--31, 2018, pages 633--637. IEEE, Oct 2018                     *)
(*                                                                            *)
(* Main reference:                                                            *)
(* - Gonzalo Navarro. Compact Data Structures: A Practical Approach.          *)
(*   Cambridge University Press, 2016.                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope num_occ_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

Import Order.POrderTheory GRing.Theory Num.Theory.

(* coercions to R : realType do not seem to work *)
Local Notation "x /:R y" := (x%:R / y%:R) (at level 40, left associativity).

(* TODO: move to convex ? *)
Section log_concave.
Import (canonicals) analysis.convex.
Variable R : realType.

Definition i01_of_prob : {prob R} -> {i01 R}.
case => p H; exists p => /=.
by apply/andP; split => //; exact: num_real.
Defined.
Definition prob_of_i01 : {i01 R} -> {prob R}.
by case => p /andP[_ H]; exists p => //.
Defined.

Lemma i01_of_probK : cancel i01_of_prob prob_of_i01.
Proof.
by case => p H /=; case: (elimTF _ _) => /= _ ?; exact/val_inj.
Qed.
Lemma prob_of_i01K : cancel prob_of_i01 i01_of_prob.
Proof.
by case=> p H/=; case: (elimTF _ _) => _ ?; apply/val_inj.
Qed.

Lemma mc_convE (a b : R^o) (p : {prob R}) :
  conv p a b = mathcomp.analysis.convex.conv (i01_of_prob p) b a :> R^o.
Proof.
rewrite [LHS]addrC.
congr (_ .~  *: _ + _ *: _); by case: p.
Qed.

(* TODO: already in MathComp-Analysis?*)
Lemma log_concave : concave_function_in Rpos_interval (log : R^o -> R^o).
Proof.
move=> /= x y p Hx Hy.
rewrite /concave_function_at /convex_function_at.
rewrite !inE in Hx Hy.
have Hln := concave_ln (i01_of_prob p) Hy Hx.
rewrite -!mc_convE in Hln.
rewrite conv_leoppD leoppP /= /log /Log /=.
rewrite [in X in X <= _]avgRE !mulrA -mulrDl -avgRE.
by rewrite ler_wpM2r // invr_ge0 ln2_ge0.
Qed.
End log_concave.

Section seq_nat_fdist.
Variables (R : realType) (A : finType) (f : A -> nat).
(*
Let N2R x : R := x%:R.
#[reversible=yes] Local Coercion N2R' := N2R.
*)
Variable total : nat.
Hypothesis sum_f_total : (\sum_(a in A) f a)%N = total.
Hypothesis total_gt0 : total != O.

Let f_div_total := [ffun a : A => f a /:R total : R].

Lemma f_div_total_pos c : 0 <= f_div_total c.
Proof. by rewrite ffunE mulr_ge0 // invr_ge0 ler0n. Qed.

Lemma f_div_total_1 : \sum_(a in A) f_div_total a = 1.
Proof.
under eq_bigr do rewrite ffunE /=.
rewrite /f_div_total -big_distrl /= -natr_sum.
by rewrite sum_f_total divrr // unitfE pnatr_eq0.
Qed.

Definition seq_nat_fdist := FDist.make f_div_total_pos f_div_total_1.
End seq_nat_fdist.

Section string.
Variables (R : realType) (A : finType).

Section entropy.
Variable S : seq A.
Hypothesis S_nonempty : size S != O.

Definition pchar c : R := N(c|S) /:R size S.

Definition num_occ_dist := seq_nat_fdist R (sum_num_occ_size S) S_nonempty.

Definition Hs0 := `H num_occ_dist.
End entropy.

Section string_concat.

(*
Definition Hs (s : seq A) :=
 \rsum_(a in A)
  if N(a|s) == 0%nat then 0 else
  N(a|s) / size s * log (size s / N(a|s)).
*)

Definition nHs (s : seq A) : R :=
 \sum_(a in A)
  if N(a|s) == 0%N then 0 else
  N(a|s)%:R * log (size s /:R N(a|s)).

Lemma szHs_is_nHs s (H : size s != O) :
  (size s)%:R * `H (@num_occ_dist s H) = nHs s :> R.
Proof.
rewrite /entropy /nHs /num_occ_dist /=.
rewrite (big_morph _ (id1:=0) (@opprD _)) ?oppr0 // big_distrr /=.
apply eq_bigr => a _ /=; rewrite ffunE.
case: ifPn => [/eqP -> | Hnum]; first by rewrite !mul0r oppr0 mulr0.
rewrite (mulrC N(a | s)%:R) mulrN 3![in LHS]mulrA mulrV ?unitfE ?pnatr_eq0 //.
rewrite mul1r -mulrA -mulrN -logV 1?mulrC ?invf_div //.
by apply divr_gt0; rewrite ltr0n lt0n.
Qed.

Definition mulnrdep (x : nat) (y : x != O -> R) : R.
case/boolP: (x == O) => Hx.
+ exact 0.
+ exact (x%:R * y Hx).
Defined.
Arguments mulnrdep x y : clear implicits.

Lemma mulnrdep_0 y : mulnrdep 0 y = 0.
Proof. by rewrite /mulnrdep /=; destruct boolP. Qed.

Lemma mulnrdep_nz x y (Hx : x != O) : mulnrdep x y = x%:R * y Hx.
Proof.
rewrite /mulnrdep /=.
destruct boolP.
  by exfalso; rewrite i in Hx.
by do 2!f_equal; apply eq_irrelevance.
Qed.

Lemma szHs_is_nHs_full s : mulnrdep (size s) (fun H => Hs0 H) = nHs s.
Proof.
rewrite /mulnrdep; destruct boolP; last by apply szHs_is_nHs.
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
apply ler_sum => a _.
(* Remove strings containing no occurrences *)
rewrite (bigID (fun s => N(a|s) == O)) /=.
rewrite big1; last by move=> i ->.
rewrite num_occ_flatten add0r.
rewrite [in X in _ <= X](bigID (fun s => N(a|s) == O)).
rewrite [in X in _ <= X]big1 //= ?add0n;
  last by move=> i /eqP.
rewrite (eq_bigr
       (fun i => N(a|i)%:R * log (size i /:R N(a|i))));
  last by move=> i /negbTE ->.
rewrite -big_filter -[in X in _ <= X]big_filter.
(* ss' contains only strings with ocurrences *)
set ss' := [seq s <- ss | N(a|s) != O].
have [->|Hss'] := eqVneq ss' [::].
  by rewrite !big_nil eqxx.
have Hnum s : s \in ss' -> (N(a|s) > 0)%N.
  by rewrite /ss' mem_filter lt0n => /andP [->].
have Hnum' : (0:R) < N(a|flatten ss')%:R.
  rewrite ltr0n; destruct ss' => //=.
  rewrite /num_occ count_cat ltn_addr //.
  by rewrite Hnum // in_cons eqxx.
have Hsz: (0:R) < (size (flatten ss'))%:R.
  apply (lt_le_trans Hnum').
  by rewrite ler_nat; apply /count_size.
apply (@le_trans _ _ ((\sum_(i <- ss') N(a|i))%:R *
    log (size (flatten ss') /:R
      (\sum_(i <- ss') N(a | i))%N)));
  last first.
  (* Not mentioned in the book: one has to compensate for the discarding
     of strings containing no occurences.
     Works thanks to monotonicity of log. *)
  (* (3) Compensate for removed strings *)
  case: ifP => Hsum.
    by rewrite (eqP Hsum) mul0r.
  apply ler_wpM2l => //.
  apply Log_increasing_le => //.
    apply/mulr_gt0 => //.
    by rewrite invr_gt0 ltr0n lt0n Hsum.
  apply ler_wpM2r.
    by rewrite invr_ge0 ler0n.
  rewrite ler_nat !size_flatten !sumn_big_addn.
  rewrite !big_map big_filter.
  rewrite [leqRHS](bigID (fun s => N(a|s) == O)) /=.
  by apply leq_addl.
(* (4) Prepare to use jensen_dist_concave *)
have Htotal := esym (num_occ_flatten a ss').
rewrite big_tnth in Htotal.
have Hnum2 : N(a|flatten ss') != O.
  by rewrite -lt0n -(ltr0n R).
set d := seq_nat_fdist R Htotal Hnum2.
set r := fun i =>
  size (tnth (in_tuple ss') i)
  /:R N(a|tnth (in_tuple ss') i) : R.
(* Need convex for Rpos_interval *)
have Hr: forall i, r i \in Rpos_interval.
  rewrite /r /= => i.
  rewrite classical_sets.in_setE; apply/divr_gt0; rewrite ltr0n.
    apply (@leq_trans N(a|tnth (in_tuple ss') i)).
      by rewrite Hnum // mem_tnth.
    by apply count_size.
  by apply /Hnum /mem_tnth.
(* (5) Apply Jensen *)
move: (jensen_dist_concave (@log_concave R) d Hr).
rewrite /d /r /=.
under eq_bigr do rewrite ffunE /=.
under [X in _ <= log X -> _]eq_bigr do rewrite ffunE /=.
rewrite -(big_tnth _ _ _ xpredT
  (fun s => N(a|s) /:R N(a|flatten ss') *
           log (size s /:R N(a|s)))).
rewrite -(big_tnth _ _ _ xpredT
  (fun s => (N(a|s) /:R N(a|flatten ss')) *
           (size s /:R N(a|s)))).
(* (6) Transform the statement to match the goal *)
move/(@ler_wpM2r R N(a|flatten ss')%:R (ler0n _ _)).
rewrite !big_distrl /=.
rewrite (eq_bigr
  (fun i => N(a|i)%:R * log (size i /:R N(a|i))));
  last first.
  move=> i _; rewrite mulrAC -!mulrA (mulrA _^-1) mulVr ?mul1r //.
  by rewrite unitfE pnatr_eq0 -lt0n -(ltr0n R).
move/le_trans; apply. (* LHS matches *)
rewrite mulrC -num_occ_flatten big_filter.
rewrite (eq_bigr
  (fun i => size i /:R N(a|flatten ss')));
  last first.
  move=> i Hi; rewrite mulrCA mulrAC.
  by rewrite mulrV ?mul1r // unitfE pnatr_eq0.
rewrite -big_filter -/ss' -big_distrl /= -natr_sum.
by rewrite size_flatten sumn_big_addn big_map.
Qed.

End string_concat.

End string.

(* tentative definition *)
Section higher_order_empirical_entropy.

Variables (R : realType) (A : finType) (l : seq A).
Hypothesis A0 : (O < #|A|)%N.
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
Definition hoH (k : nat) := n%:R^-1 *
  \sum_(w in {: k.-tuple A}) #|takes w l|%:R *
    match Bool.bool_dec (size w != O) true with
      | left H => `H (num_occ_dist R H)
      | _ => 0
    end.

Lemma hoH_decr (k : nat) : hoH k.+1 <= hoH k.
Proof.
rewrite /hoH; rewrite ler_pM2l//; last first.
  by rewrite invr_gt0 ltr0n lt0n.
(* TODO *)
Abort.

End higher_order_empirical_entropy.
