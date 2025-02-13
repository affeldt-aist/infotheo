(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import Rstruct reals.
Require Import ssr_ext bigop_ext realType_ext realType_ln.
Require Import fdist divergence log_sum variation_dist.

(**md**************************************************************************)
(* # Partition inequality                                                     *)
(*                                                                            *)
(* Special case for distributions other sets with 2 elements, to be used in   *)
(* the proof of Pinsker's inequality.                                         *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope divergence_scope.
Local Open Scope fdist_scope.
Local Open Scope R_scope.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import Order.POrderTheory GRing.Theory Num.Theory.

Local Notation "0" := (false).
Local Notation "1" := (true).

Section bipart_sect.
Context {R : realType}.
Variable A : finType.
Variable A_ : bool -> {set A}.
Hypothesis dis : A_ 0 :&: A_ 1 = set0.
Hypothesis cov : A_ 0 :|: A_ 1 = [set: A].
Variable P : R.-fdist A.

Definition bipart_pmf := [ffun i => \sum_(a in A_ i) P a].

Definition bipart : R.-fdist bool.
apply (@FDist.make R _ bipart_pmf).
- by move=> a; rewrite ffunE; apply: sumr_ge0.
- rewrite big_bool /= /bipart_pmf /= !ffunE.
  transitivity (\sum_(a | (a \in A_ 0 :|: A_ 1)) P a).
    by rewrite [X in _ = X](@big_union _ _ _ _ (A_ 0) (A_ 1)) // -setI_eq0 setIC dis eqxx.
  by rewrite cov -(FDist.f1 P); apply eq_bigl => /= x; rewrite in_setT inE.
Defined.

End bipart_sect.

Local Open Scope reals_ext_scope.

Section bipart_lem.
Context {R : realType}.
Variable A : finType.
Variable A_ : bool -> {set A}.
Hypothesis dis : A_ 0 :&: A_ 1 = set0.
Hypothesis cov : A_ 0 :|: A_ 1 = setT.
Variable P Q : R.-fdist A.
Hypothesis P_dom_by_Q : P `<< Q.

Let P_A : R.-fdist bool := bipart dis cov P.
Let Q_A : R.-fdist bool:= bipart dis cov Q.

Lemma partition_inequality : D(P_A || Q_A) <= D(P || Q).
Proof.
have -> : D(P || Q) = \sum_(a in A_ 0) P a * log (P a / Q a) +
                      \sum_(a in A_ 1) P a * log (P a / Q a).
  rewrite /div -big_union //; last by rewrite -setI_eq0 setIC dis eqxx.
  apply eq_big => // a; first by rewrite cov in_set inE.
have step2 :
  (\sum_(a in A_ 0) P a) * log ((\sum_(a in A_ 0) P a) / \sum_(a in A_ 0) Q a) +
  (\sum_(a in A_ 1) P a) * log ((\sum_(a in A_ 1) P a) / \sum_(a in A_ 1) Q a) <=
  \sum_(a in A_ 0) P a * log (P a / Q a) + \sum_(a in A_ 1) P a * log (P a / Q a).
  by apply: lerD => //; exact: log_sum.
apply: (le_trans _ step2) => {step2}.
rewrite [X in _ <= X](_ : _ =
  P_A 0 * log ((P_A 0) / (Q_A 0)) + P_A 1 * log ((P_A 1) / (Q_A 1))); last first.
  by rewrite !ffunE.
rewrite /div big_bool.
rewrite [P_A]lock [Q_A]lock /= -!lock.
have := FDist.ge0 P_A 0.
rewrite le_eqVlt => /predU1P[/esym A0_P_0|A0_P_neq0]; last first.
- have := FDist.ge0 Q_A 1.
  rewrite le_eqVlt => /predU1P[/esym A1_Q_0|A1_Q_neq0]; last first.
  + have := FDist.ge0 Q_A 0.
    rewrite le_eqVlt => /predU1P[/esym A0_Q_0|A0_Q__neq0]; last first.
    * by rewrite logM// invr_gt0//.
    * rewrite ffunE in A0_Q_0; move/psumr_eq0P in A0_Q_0.
      have {}A0_Q_0 : forall i : A, i \in A_ 0 -> P i = 0%R.
        move=> i ?; rewrite (dominatesE P_dom_by_Q) // A0_Q_0 // => a ?; exact/pos_ff_ge0.
      have Habs : P_A 0 = 0%R.
        transitivity (\sum_(H|H \in A_ 0) (0:R))%R.
          rewrite ffunE.
          apply eq_big => // i Hi; by rewrite -A0_Q_0.
        by rewrite big1.
      by move: A0_P_neq0; rewrite Habs ltxx.
  + have H2 : P_A 1 = 0%R.
      rewrite ffunE in A1_Q_0; move/psumr_eq0P in A1_Q_0.
      rewrite /bipart /= ffunE /bipart_pmf (eq_bigr (fun=> 0%R)).
        by rewrite big1.
      by move=> a ?; rewrite (dominatesE P_dom_by_Q) // A1_Q_0 // => b ?; exact/pos_ff_ge0.
    rewrite H2 !mul0r !addr0.
    have H3 : Q_A 0 = 1%R.
      rewrite -[X in X = _]addr0 -[X in _ + X = _]A1_Q_0 -(FDist.f1 Q).
      rewrite !ffunE -big_union //.
      apply eq_bigl => i; by rewrite cov in_set inE.
      by rewrite -setI_eq0 -dis setIC.
    by rewrite H3 logM// invr1.
- have H1 : P_A 1 = 1%R.
    rewrite -[X in X = _]add0r -[X in X + _ = _]A0_P_0 -(FDist.f1 P).
    rewrite !ffunE -big_union //.
    apply eq_bigl => i; by rewrite cov in_set inE.
    by rewrite -setI_eq0 -dis setIC.
  have := FDist.ge0 Q_A 1.
  rewrite le_eqVlt => /predU1P[/esym A1_Q_0|A1_Q_neq0]; last first.
  + rewrite A0_P_0 !mul0r !add0r H1 !mul1r.
    by rewrite ler_log// ?posrE// invr_gt0.
  + (* contradiction H1 / Bi_true_Q_0 *)
    rewrite ffunE in A1_Q_0; move/psumr_eq0P in A1_Q_0.
    have : P_A 1 = 0%R.
      rewrite !ffunE /bipart /= /bipart_pmf (eq_bigr (fun=> 0%R)).
        by rewrite big1.
      by move=> a ?; rewrite (dominatesE P_dom_by_Q) // A1_Q_0 // => b ?; exact/pos_ff_ge0.
    by rewrite A0_P_0.
Qed.

End bipart_lem.
