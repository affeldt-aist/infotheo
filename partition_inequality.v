(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype finfun bigop finset.
Require Import Reals Fourier.
Require Import Rssr Reals_ext Ranalysis_ext ssr_ext log2 ln_facts bigop_ext.
Require Import Rbigop proba divergence log_sum variation_dist.

(** * Partition inequality (special case for distributions other sets with two elements) *)

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
- move=> a; apply: rsumr_ge0. by move=> *; exact/dist_nonneg.
  rewrite Set2sumE /= ?card_bool // => HX; rewrite /bipart_pmf.
  set a := Set2.a HX. set b := Set2.b HX.
  have : a <> b by apply/eqP/Set2.a_neq_b.
  wlog : a b / (a == false) && (b == true).
    move=> Hwlog b01.
    have : ((a, b) == (true, false)) || ((a, b) == (false, true)).
      move: a b b01; by case; case.
    case/orP; case/eqP => -> ->.
    - by rewrite addRC Hwlog.
    - exact: Hwlog.
  case/andP => /eqP -> /eqP -> _.
  transitivity (\rsum_(a | (a \in A_ 0 :|: A_ 1)) P a).
    by rewrite [X in _ = X](@big_union _ _ _ _ (A_ 0) (A_ 1)) // -setI_eq0 setIC dis eqxx.
  rewrite cov -(pmf1 P).
  apply eq_bigl => /= x; by rewrite in_setT inE.
Defined.

End bipart_sect.

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
  rewrite /div -big_union //; last by rewrite -setI_eq0 setIC dis eqxx.
  apply eq_big => // a; first by rewrite cov in_set inE.
  move=> _.
  case/Rle_lt_or_eq_dec: (dist_nonneg P a) => Pa.
    case/Rle_lt_or_eq_dec: (dist_nonneg Q a) => Qa.
      rewrite /log LogM // ?LogV //; exact/invR_gt0.
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
rewrite /div Set2sumE ?card_bool // => B.
rewrite [P_A]lock [Q_A]lock /= -!lock.
move: (Set2.a_neq_b B).
set a := Set2.a B. set b := Set2.b B.
wlog : a b / (a == 0) && (b == 1).
  move=> Hwlog i0i1.
  have : ((a, b) == (1, 0)) || ((a, b) == (0, 1)).
    destruct a; destruct b => //.
    move: a b i0i1.
    case=> //.
      case=> // _ _.
      rewrite Rplus_comm.
      by apply Hwlog.
    case=> // _ _.
    by apply Hwlog.
case/andP => /eqP -> /eqP -> _ {a b}.
have [A0_P_neq0 | /esym A0_P_0] : {0 < P_A 0} + {0%R = P_A 0}.
  apply Rle_lt_or_eq_dec; apply: rsumr_ge0 => i _; exact/dist_nonneg.
- have [A1_Q_neq0 | /esym A1_Q_0] : {0 < Q_A 1} + {0%R = Q_A 1}.
    apply Rle_lt_or_eq_dec; apply: rsumr_ge0 => i _; exact/dist_nonneg.
  + have [A0_Q__neq0 | /esym A0_Q_0] : {0 < Q_A 0} + {0%R = Q_A 0}.
      apply Rle_lt_or_eq_dec; apply: rsumr_ge0 => i _; exact/dist_nonneg.
    * rewrite /Rdiv /log LogM //; last exact/invR_gt0.
      rewrite LogV //.
      have [A1_P_neq0 | /esym A1_P_0] : {0 < P_A 1} + {0%R = P_A 1}.
        apply Rle_lt_or_eq_dec; apply: rsumr_ge0 => i _; exact/dist_nonneg.
      - rewrite /log LogM //; last exact/invR_gt0.
        rewrite LogV //.
        apply Req_le; by field.
      - rewrite A1_P_0 !mul0R addR0; exact/Req_le.
    * move/prsumr_eq0P in A0_Q_0.
      have {A0_Q_0}A0_Q_0 : forall i : A, i \in A_ 0 -> P i = 0%R.
        move=> i ?; rewrite P_dom_by_Q // A0_Q_0 // => a ?; exact/pos_f_nonneg.
      have Habs : P_A 0 = 0%R.
        transitivity (\rsum_(H|H \in A_ 0) 0%R).
          apply eq_big => // i Hi; by rewrite -A0_Q_0.
        by rewrite big_const iter_Rplus_Rmult mulR0.
      move: A0_P_neq0.
      rewrite Habs; by move/Rlt_irrefl.
  + have H2 : P_A 1 = 0%R.
      move/prsumr_eq0P in A1_Q_0.
      rewrite /bipart /= /bipart_pmf (eq_bigr (fun=> 0%R)).
        by rewrite big_const iter_Rplus mulR0.
      move=> a ?; rewrite P_dom_by_Q // A1_Q_0 // => b ?; exact/pos_f_nonneg.
    rewrite H2 !mul0R !addR0.
    have H3 : Q_A 0 = 1%R.
      rewrite -[X in X = _]addR0 -[X in _ + X = _]A1_Q_0 -(pmf1 Q).
      rewrite -big_union //.
      apply eq_bigl => i; by rewrite cov in_set inE.
      by rewrite -setI_eq0 -dis setIC.
    rewrite H3 /Rdiv /log LogM // ; last by fourier.
    rewrite LogV; last by fourier.
    apply Req_le; by field.
- have H1 : P_A 1 = 1%R.
    rewrite -[X in X = _]add0R -[X in X + _ = _]A0_P_0 -(pmf1 P).
    rewrite -big_union //.
    apply eq_bigl => i; by rewrite cov in_set inE.
    by rewrite -setI_eq0 -dis setIC.
  have [A1_Q_neq0 | /esym A1_Q_0] : {0 < Q_A 1} + {0%R = Q_A 1}.
    apply Rle_lt_or_eq_dec; apply: rsumr_ge0 => i _; exact/dist_nonneg.
  + rewrite A0_P_0 !mul0R !add0R H1 !mul1R.
    rewrite /Rdiv /log LogM; last 2 first.
      by fourier.
      exact/invR_gt0.
    rewrite /log LogV //; apply Req_le; by field.
  + (* contradiction H1 / Bi_true_Q_0 *)
    move/prsumr_eq0P in A1_Q_0.
    have : P_A 1 = 0%R.
      rewrite /bipart /= /bipart_pmf (eq_bigr (fun=> 0%R)).
      by rewrite big_const iter_Rplus mulR0.
      move=> a ?; rewrite P_dom_by_Q // A1_Q_0 // => b ?; exact/pos_f_nonneg.
    move=> abs; rewrite abs in H1. fourier.
Qed.

End bipart_lem.
