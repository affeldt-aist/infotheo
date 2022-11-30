(* infotheo: information theory and error-correcting codes in Coq               *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later              *)
From mathcomp Require Import all_ssreflect fingroup perm matrix.
Require Import Reals.
From mathcomp Require Import Rstruct.
Require Import ssrR Reals_ext ssr_ext ssralg_ext Rbigop bigop_ext logb ln_facts.
Require Import fdist proba jfdist binary_entropy_function divergence.

(******************************************************************************)
(*                        Entropy of a distribution                           *)
(*                                                                            *)
(* `H P == the entropy of the (finite) probability distribution P             *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*       entropy_ge0 == the entropy is non-negative                           *)
(*       entropy_max == the entropy is bounded by log |A| where A is the      *)
(*                      support of the distribution                           *)
(*        entropy_Ex == the entropy is the expectation of the negative        *)
(*                      logarithm                                             *)
(*      xlnx_entropy == the entropy is the natural entropy scaled by ln(2)    *)
(*   entropy_uniform == the entropy of a uniform distribution is just log     *)
(*        entropy_H2 == the binary entropy H2 is the entropy over {x, y}      *)
(******************************************************************************)

Reserved Notation "'`H'" (at level 5).

Declare Scope entropy_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.

Section entropy_definition.
Variables (A : finType) (P : fdist A).

Definition entropy := - \sum_(a in A) P a * log (P a).
Local Notation "'`H'" := (entropy).

Lemma entropy_ge0 : 0 <= `H.
Proof.
rewrite /entropy big_morph_oppR; apply sumR_ge0 => i _.
have [->|Hi] := eqVneq (P i) 0; first by rewrite mul0R oppR0; exact/leRR.
  (* NB: this step in a standard textbook would be handled as a consequence of lim x->0 x log x = 0 *)
rewrite mulRC -mulNR; apply mulR_ge0 => //; apply: oppR_ge0.
rewrite -log1; apply Log_increasing_le => //.
by apply/ltRP; rewrite lt0R Hi; exact/leRP.
Qed.

End entropy_definition.

Notation "'`H'" := (entropy) : entropy_scope.

Section entropy_theory.
Local Open Scope entropy_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Context (A : finType).

Lemma entropy_Ex (P : fdist A) : `H P = `E (`-- (`log P)).
Proof.
rewrite /entropy /log_RV /= big_morph_oppR.
by apply eq_bigr => a _; rewrite mulRC -mulNR.
Qed.

Lemma xlnx_entropy (P : fdist A) : `H P = / ln 2 * - \sum_(a : A) xlnx (P a).
Proof.
rewrite /entropy mulRN; congr (- _); rewrite big_distrr/=.
apply: eq_bigr => a _; rewrite /log /Rdiv mulRA mulRC; congr (_ * _).
rewrite /xlnx; case : ifP => // /ltRP Hcase.
have -> : P a = 0 by case (Rle_lt_or_eq_dec 0 (P a)).
by rewrite mul0R.
Qed.

Lemma entropy_uniform n (An1 : #|A| = n.+1) :
  `H (fdist_uniform An1) = log (INR #|A|).
Proof.
rewrite /entropy.
under eq_bigr do rewrite fdist_uniformE.
rewrite big_const iter_addR mulRA mulRV; last by rewrite INR_eq0' An1.
by rewrite mul1R logV ?oppRK//; rewrite An1; apply/ltR0n.
Qed.

Lemma entropy_H2 (card_A : #|A| = 2%nat) (p : prob) :
  H2 p = entropy (fdist_binary card_A p (Set2.a card_A)).
Proof.
rewrite /H2 /entropy Set2sumE /= fdist_binaryxx !fdist_binaryE.
by rewrite eq_sym (negbTE (Set2.a_neq_b _)) oppRD addRC.
Qed.

Lemma entropy_max (P : fdist A) : `H P <= log #|A|%:R.
Proof.
have [n An1] : exists n, #|A| = n.+1.
  by exists #|A|.-1; rewrite prednK //; exact: (fdist_card_neq0 P).
have /div_ge0 H := dom_by_uniform P An1.
rewrite -subR_ge0; apply/(leR_trans H)/Req_le.
transitivity (\sum_(a|a \in A) P a * log (P a) +
              \sum_(a|a \in A) P a * - log (fdist_uniform An1 a)).
  rewrite -big_split /=; apply eq_bigr => a _; rewrite -mulRDr.
  case/boolP : (P a == 0) => [/eqP ->|H0]; first by rewrite !mul0R.
  congr (_ * _); rewrite logDiv ?addR_opp //.
    by rewrite -fdist_gt0.
  by rewrite fdist_uniformE; apply/invR_gt0; rewrite An1; exact/ltR0n.
under [in X in _ + X]eq_bigr do rewrite fdist_uniformE.
rewrite -[in X in _ + X = _]big_distrl /= FDist.f1 mul1R.
by rewrite addRC /entropy /log LogV ?oppRK ?subR_opp // An1; exact/ltR0n.
Qed.

Lemma entropy_fdist_rV_of_prod n (P : {fdist A * 'rV[A]_n}) :
  `H (fdist_rV_of_prod P) = `H P.
Proof.
rewrite /entropy /=; congr (- _).
rewrite -(big_rV_cons_behead _ xpredT xpredT) /= pair_bigA /=.
apply eq_bigr => -[a b] _ /=.
by rewrite fdist_rV_of_prodE /= row_mx_row_ord0 rbehead_row_mx.
Qed.

Lemma entropy_fdist_prod_of_rV n (P : {fdist 'rV[A]_n.+1}) :
  `H (fdist_prod_of_rV P) = `H P.
Proof.
rewrite /entropy /=; congr (- _).
rewrite -(big_rV_cons_behead _ xpredT xpredT) /= pair_bigA /=.
apply eq_bigr => -[a b] _ /=; by rewrite fdist_prod_of_rVE /=.
Qed.

Lemma entropy_fdist_perm n (P : {fdist 'rV[A]_n}) (s : 'S_n) :
  `H (fdist_perm P s) = `H P.
Proof.
rewrite /entropy; congr (- _) => /=; apply/esym.
rewrite (@reindex_inj _ _ _ _ (@col_perm _ _ _ s) xpredT); last first.
  exact: col_perm_inj.
by apply eq_bigr => v _; rewrite fdist_permE.
Qed.

End entropy_theory.
