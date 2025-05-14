(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect all_algebra fingroup perm.
From mathcomp Require Import reals exp.
Require Import ssr_ext ssralg_ext bigop_ext realType_ext realType_ln.
Require Import fdist jfdist_cond proba binary_entropy_function divergence.

(**md**************************************************************************)
(* # Elements of Information Theory                                           *)
(*                                                                            *)
(* This file contains a Formalization of the chapter 2 of:                    *)
(* - Thomas M. Cover, Joy A. Thomas, Elements of Information Theory, Wiley,   *)
(*   2005                                                                     *)
(* It is completed by `entropy_convex.v`.                                     *)
(*                                                                            *)
(* ```                                                                        *)
(*                        `H P == the entropy of the (finite) probability     *)
(*                                distribution P                              *)
(*             joint_entropy P := `H P with P : R.-fdist (A * B)              *)
(*                                entropy of a joint distribution             *)
(*                    `H(X, Y) := joint_entropy `p_[% X, Y]                   *)
(*              centropy1 QP a == H(Y | X = a)                                *)
(*                                with QP : R.-fdist (B * A) and a : A        *)
(*                                conditional entropy of a joint distribution *)
(*                 centropy QP == H(Y | X)                                    *)
(*          centropy1_RV X Y a := `H (`p_[% X, Y] `(| a )).                   *)
(*              mutual_info PQ := D(PQ || P `x Q)                             *)
(*                   `I(X ; Y) == mutual information between RVs              *)
(*        cond_mutual_info PQR == conditional mutual information              *)
(*       cond_relative_entropy == TODO                                        *)
(*                markov_chain == TODO                                        *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "'`H'" (at level 0).
Reserved Notation "`H( X , Y )" (at level 10, X, Y at next level,
  format "`H( X ,  Y )").
Reserved Notation "`H( Y | X )" (at level 10, Y, X at next level).
Reserved Notation "`I( X ; Y )" (at level 50, format "`I( X ;  Y )").
Reserved Notation "`H[ Y | X = a ]" (at level 0, Y, X, a at next level,
  format "`H[  Y  |  X  =  a  ]").

Declare Scope entropy_scope.
Delimit Scope entropy_scope with entropy.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.

Import Order.POrderTheory GRing.Theory Num.Theory.

Section entropy_definition.
Variables (R : realType) (A : finType) (P : R.-fdist A).

Definition entropy : R^o := - \sum_(a in A) P a * log (P a).
Local Notation "'`H'" := (entropy).

(** the entropy is non-negative: *)
Lemma entropy_ge0 : 0 <= `H.
Proof.
rewrite /entropy big_morph_oppr; apply/sumr_ge0 => i _.
have [->|Hi] := eqVneq (P i) 0; first by rewrite mul0r oppr0.
(* NB: this step in a standard textbook would be handled as a consequence of
   lim x->0 x log x = 0 *)
rewrite mulrC -mulNr mulr_ge0// lerNr oppr0.
rewrite -log1 ler_log// ?posrE//.
by rewrite lt0r Hi/=.
Qed.

End entropy_definition.

Notation "'`H'" := (entropy) : entropy_scope.
Local Open Scope entropy_scope.

Section entropy_theory.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Context (R : realType) (A : finType).

(** the entropy is the expectation of the negative logarithm: *)
Lemma entropy_Ex (P : R.-fdist A) : `H P = `E (`-- (`log P)).
Proof.
rewrite /entropy /log_RV /= big_morph_oppr.
by apply eq_bigr => a _; rewrite mulrC -mulNr.
Qed.

(** the entropy is the natural entropy scaled by ln(2): *)
Lemma xlnx_entropy (P : R.-fdist A) :
  `H P = (ln 2)^-1 * - \sum_(a : A) xlnx (P a).
Proof.
rewrite /entropy mulrN; congr (- _); rewrite big_distrr/=.
apply: eq_bigr => a _; rewrite /xlnx /log /Log/=.
have := FDist.ge0 P a; rewrite le_eqVlt => /predU1P[<-|Pa0].
  by rewrite !mul0r ltxx mulr0.
by rewrite Pa0 mulrA mulrC.
Qed.

(** the entropy of a uniform distribution is just log: *)
Lemma entropy_uniform n (An1 : #|A| = n.+1) :
  `H (fdist_uniform An1) = log #|A|%:R :> R.
Proof.
rewrite /entropy.
under eq_bigr do rewrite fdist_uniformE.
rewrite big_const iter_addr addr0 logV; last by rewrite An1.
rewrite -mulNrn mulrN opprK -mulrnAr -(mulr_natr (log _) #|A|) mulrCA.
by rewrite mulVf ?mulr1// An1 pnatr_eq0.
Qed.

(** the binary entropy H2 is the entropy over {x, y}: *)
Lemma entropy_H2 (card_A : #|A| = 2%nat) (p : prob R) :
  H2 (Prob.p p) = entropy (fdist_binary card_A p (Set2.a card_A)).
Proof.
rewrite /H2 /entropy Set2sumE /= fdist_binaryxx !fdist_binaryE.
by rewrite eq_sym (negbTE (Set2.a_neq_b _)) opprD addrC.
Qed.

(** the entropy is bounded by log |A| where A is the support of the
    distribution: *)
Lemma entropy_max (P : R.-fdist A) : `H P <= log #|A|%:R.
Proof.
have [n An1] : exists n, #|A| = n.+1.
  by exists #|A|.-1; rewrite prednK //; exact: (fdist_card_neq0 P).
have /div_ge0 H := dom_by_uniform P An1.
rewrite -subr_ge0; apply/(le_trans H).
rewrite le_eqVlt; apply/orP; left; apply/eqP.
transitivity (\sum_(a|a \in A) P a * log (P a) +
              \sum_(a|a \in A) P a * - log (fdist_uniform An1 a)).
  rewrite -big_split /=; apply eq_bigr => a _; rewrite -mulrDr.
  have [->|Pa0] := eqVneq (P a) 0; first by rewrite !mul0r.
  congr (_ * _); rewrite logDiv//.
    by rewrite -fdist_gt0.
  by rewrite fdist_uniformE invr_gt0// An1 ltr0n.
under [in X in _ + X]eq_bigr do rewrite fdist_uniformE.
rewrite -[in X in _ + X = _]big_distrl /= FDist.f1 mul1r.
by rewrite addrC /entropy logV ?opprK// An1 ltr0n.
Qed.

Lemma entropy_fdist_rV_of_prod n (P : R.-fdist (A * 'rV[A]_n)) :
  `H (fdist_rV_of_prod P) = `H P.
Proof.
rewrite /entropy /=; congr (- _).
rewrite -(big_rV_cons_behead _ xpredT xpredT) /= pair_bigA /=.
apply eq_bigr => -[a b] _ /=.
by rewrite fdist_rV_of_prodE /= row_mx_row_ord0 rbehead_row_mx.
Qed.

Lemma entropy_fdist_prod_of_rV n (P : R.-fdist 'rV[A]_n.+1) :
  `H (fdist_prod_of_rV P) = `H P.
Proof.
rewrite /entropy /=; congr (- _).
rewrite -(big_rV_cons_behead _ xpredT xpredT) /= pair_bigA /=.
apply eq_bigr => -[a b] _ /=; by rewrite fdist_prod_of_rVE /=.
Qed.

Lemma entropy_fdist_perm n (P : R.-fdist 'rV[A]_n) (s : 'S_n) :
  `H (fdist_perm P s) = `H P.
Proof.
rewrite /entropy; congr (- _) => /=; apply/esym.
rewrite (@reindex_inj _ _ _ _ (@col_perm _ _ _ s) xpredT); last first.
  exact: col_perm_inj.
by apply eq_bigr => v _; rewrite fdist_permE.
Qed.

End entropy_theory.

Section entropy_fdistmap.
Context {R : realType}.

Lemma entropy_fdistmap
  (A B : finType) (f : A -> B) (P : R.-fdist A) :
  injective f -> `H (fdistmap f P) = `H P.
Proof.
move=> f_inj; congr -%R; set rhs := RHS.
rewrite (bigID (mem [set f a | a in A]))/=.
rewrite big_imset/=; last by move=> *; exact: f_inj.
under eq_bigr=> a _.
  rewrite fdistmapE;
  under eq_bigl do rewrite !inE/=;
  rewrite big_pred1_inj//.
  over.
rewrite -[RHS]addr0; congr +%R.
rewrite big1// => b.
move/imsetPn=> bfx.
rewrite fdistmapE/= big_pred0 ?mul0r// => a.
rewrite inE/= eq_sym.
exact/negP/negP/bfx.
Qed.

End entropy_fdistmap.

Section entropy_fdistA.
Context {R : realType} (A B C : finType) (P : R.-fdist (A * B * C)).

Lemma entropy_fdistA : `H (fdistA P) = `H P.
Proof. exact/entropy_fdistmap/inj_prodA. Qed.

End entropy_fdistA.

Section joint_entropy.
Variables (R : realType) (A B : finType) (P : R.-fdist (A * B)).

(* eqn 2.8 *)
Definition joint_entropy := `H P.

(* eqn 2.9 *)
Lemma joint_entropyE : joint_entropy = `E (`-- (`log P)).
Proof. by rewrite /joint_entropy entropy_Ex. Qed.

Lemma joint_entropyC : joint_entropy = `H (fdistX P).
Proof.
congr (- _) => /=.
rewrite (eq_bigr (fun a => P (a.1, a.2) * log (P (a.1, a.2)))); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => P (a1, a2) * log (P (a1, a2)))) /=.
by rewrite exchange_big pair_big; apply eq_bigr => -[a b] _; rewrite fdistXE.
Qed.

End joint_entropy.

Lemma entropy_rV (R : realType) (A : finType) n (P : R.-fdist 'rV[A]_n.+1) :
  `H P = joint_entropy (fdist_belast_last_of_rV P).
Proof.
rewrite /joint_entropy /entropy; congr (- _) => /=.
rewrite -(big_rV_belast_last _ xpredT xpredT) /=.
rewrite pair_big /=; apply eq_bigr => -[a b] _ /=.
by rewrite fdist_belast_last_of_rVE.
Qed.

Section joint_entropy_RV_def.
Variable R : realType.
Variables (U A B : finType) (P : R.-fdist U) (X : {RV P -> A}) (Y : {RV P -> B}).
Definition joint_entropy_RV := joint_entropy `p_[% X, Y].
End joint_entropy_RV_def.
Notation "'`H(' X ',' Y ')'" := (joint_entropy_RV X Y) : entropy_scope.

Section joint_entropy_RVCA.
Context {R : realType} {U A B C : finType} {P : R.-fdist U}.
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).

Lemma joint_entropy_RVC : `H(X, Y) = `H(Y, X).
Proof.
rewrite /joint_entropy_RV [LHS]joint_entropyC; congr -%R.
by apply: eq_bigr => -[a b] _; rewrite fdistX_RV2.
Qed.

Lemma joint_entropy_RVA : `H(X, [% Y, Z]) = `H([%X, Y], Z).
Proof.
by rewrite /joint_entropy_RV [in LHS]/joint_entropy -fdistA_RV3 entropy_fdistA.
Qed.

End joint_entropy_RVCA.

Section joint_entropy_RV_prop.
Variable R : realType.
Variables (U A B : finType) (P : R.-fdist U) (X : {RV P -> A}) (Y : {RV P -> B}).

(* 2.9 *)
Lemma eqn29 : `H(X, Y) = - `E (`log `p_[% X, Y]).
Proof. by rewrite /joint_entropy_RV joint_entropyE E_opp_RV. Qed.

End joint_entropy_RV_prop.

Section joint_entropy_prop.
Variable (R : realType) (A : finType) (P : R.-fdist A).

Lemma joint_entropy_self : joint_entropy (fdist_self P) = `H P.
Proof.
congr (- _).
rewrite (eq_bigr (fun a => fdist_self P (a.1, a.2) *
                           log (fdist_self P (a.1, a.2)))); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => fdist_self P (a1, a2) *
                                    log (fdist_self P (a1, a2)))) /=.
apply/eq_bigr => a _.
rewrite (bigD1 a) //= !fdist_selfE /= eqxx big1 ?addr0 //.
by move=> a' /negbTE; rewrite fdist_selfE /= eq_sym => ->; rewrite mul0r.
Qed.

End joint_entropy_prop.

(* definitions using probability distributions, see below for RVs *)
Section conditional_entropy_def.
Context {R : realType} {A B : finType}.
Variable QP : R.-fdist (B * A).

(* H(Y|X = x), see eqn 2.10 *)
Definition centropy1 a := - \sum_(b in B)
  \Pr_QP [ [set b] | [set a] ] * log (\Pr_QP [ [set b] | [set a] ]).

(*eqn 2.11 *)
Definition centropy : R^o := \sum_(a in A) (QP`2) a * centropy1 a.

End conditional_entropy_def.
#[deprecated(since="infotheo 0.9.2", note="renamed to `centropy1`")]
Notation cond_entropy1 := centropy1 (only parsing).
#[deprecated(since="infotheo 0.9.2", note="renamed to `centropy`")]
Notation cond_entropy := centropy (only parsing).

Section conditional_entropy_lemmas.
Variables (R : realType) (A B : finType) (QP : R.-fdist (B * A)).

Let P := QP`2.
Let PQ := fdistX QP.

(* cover&thomas 2.12 *)
Lemma centropyE : centropy QP = - \sum_(a in A) \sum_(b in B)
  PQ (a, b) * log (\Pr_QP [ [set b] | [set a]]).
Proof.
rewrite /centropy big_morph_oppr /=; apply eq_bigr => a _.
rewrite /centropy1 mulrN big_distrr /=; congr (- _); apply eq_bigr => b _.
rewrite mulrA; congr (_ * _).
by rewrite mulrC -(Pr_set1 P a) -jproduct_rule setX1 fdistXE Pr_set1.
Qed.

Lemma centropy1_ge0 a : 0 <= centropy1 QP a.
Proof.
rewrite /centropy1 big_morph_oppr; apply/sumr_ge0 => b _; rewrite -mulrN.
have [->|H0] := eqVneq (\Pr_QP[[set b]|[set a]]) 0.
  by rewrite mul0r.
apply/mulr_ge0; [exact: jcPr_ge0|].
by rewrite -oppr0 -log1 lerNr opprK ler_log ?posrE// ?jcPr_gt0// jcPr_le1.
Qed.

Lemma centropy_ge0 : 0 <= centropy QP.
Proof.
by apply/sumr_ge0 => a _; apply/mulr_ge0 => //; exact: centropy1_ge0.
Qed.

End conditional_entropy_lemmas.
#[deprecated(since="infotheo 0.9.2", note="renamed to `centropyE`")]
Notation cond_entropyE := centropyE (only parsing).
#[deprecated(since="infotheo 0.9.2", note="renamed to `centropy1_ge0`")]
Notation cond_entropy1_ge0 := centropy1_ge0 (only parsing).
#[deprecated(since="infotheo 0.9.2", note="renamed to `centropy_ge0`")]
Notation cond_entropy_ge0E:= centropy_ge0 (only parsing).

(* definitions using RVs *)
Section centropy1_RV_def.
Context {R : realType} {U A B : finType} {P : R.-fdist U}.
Variables (X : {RV P -> A}) (Y : {RV P -> B}).

Definition centropy1_RV a := centropy1 `p_[% Y, X] a.

Definition centropy_RV := centropy `p_[% Y, X].

End centropy1_RV_def.
Notation "`H[ Y | X = a ]" := (centropy1_RV X Y a).
Notation "`H( Y | X )" := (centropy_RV X Y).

Lemma centropyC {R : realType} (T : finType) (P : R.-fdist T)
    (A B C : finType) (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) :
  `H(X | [% Y, Z]) = `H(X | [% Z, Y]).
Proof.
rewrite /centropy_RV /centropy /=.
rewrite (reindex (fun p : C * B => (p.2, p.1))) /=; last first.
  by exists (fun p : B * C => (p.2, p.1)) => -[b c].
apply: eq_bigr => -[c b] _ /=.
rewrite !snd_RV2 -!pr_eqE' pr_eq_pairC.
congr (_ * _).
rewrite /centropy1; congr (- _).
rewrite /jcPr !snd_RV2.
apply: eq_bigr => a _.
by rewrite !setX1 !Pr_set1 -!pr_eqE' !pr_eq_pairA pr_eq_pairAC (pr_eq_pairC Z).
Qed.

Section conditional_entropy_RV_lemmas.
Context {R : realType} {U A B : finType} {P : R.-fdist U}.
Variables (X : {RV P -> A}) (Y : {RV P -> B}).

Lemma centropy_RVE' : `H(Y | X) = \sum_(a in A) `Pr[X = a] * `H[Y | X = a].
Proof. by apply: eq_bigr => a _; rewrite snd_RV2 -pr_eqE'. Qed.

(* cover&thomas 2.12 *)
Lemma centropy_RVE : `H(Y | X) = - \sum_(a in A) \sum_(b in B)
  `p_[% X, Y] (a, b) * log (\Pr_`p_[% Y, X] [ [set b] | [set a]]).
Proof.
rewrite /centropy_RV centropyE; congr (- _); apply: eq_bigr => a _.
by apply: eq_bigr => b _; rewrite fdistX_RV2.
Qed.

Lemma centropy1_RV_ge0 a : 0 <= `H[Y | X = a].
Proof. by rewrite /centropy1_RV centropy1_ge0. Qed.

Lemma centropy_RV_ge0 : 0 <= `H(Y | X).
Proof. by rewrite /centropy_RV centropy_ge0. Qed.

End conditional_entropy_RV_lemmas.

Section centropy1_RV_prop.
Context {R : realType} {U A B : finType} {P : R.-fdist U}.
Variables (X : {RV P -> A}) (Y : {RV P -> B}).

Lemma centropy1_RVE a : (`p_[% X, Y])`1 a != 0 ->
  `H[Y | X = a] = `H (`p_[% X, Y] `(| a )).
Proof.
move=> a0.
rewrite /centropy1_RV /centropy1 /entropy; congr (- _).
by apply: eq_bigr => b _; rewrite jfdist_condE// fdistX_RV2.
Qed.

End centropy1_RV_prop.

Section conditional_entropy_prop.
Variables (R : realType) (A B C : finType) (PQR : R.-fdist (A * B * C)).

Lemma centropy1_fdistAC b c : centropy1 (fdistA PQR) (b, c) =
                              centropy1 (fdistA (fdistAC PQR)) (c, b).
Proof.
rewrite /centropy1; congr (- _).
by apply eq_bigr => a _; rewrite -!setX1 jcPr_fdistA_AC.
Qed.

Lemma centropy_fdistA :
  centropy (fdistA PQR) = centropy (fdistA (fdistAC PQR)).
Proof.
rewrite /centropy /=.
rewrite (eq_bigr (fun a => (fdistA PQR)`2 (a.1, a.2) *
                           centropy1 (fdistA PQR) (a.1, a.2))); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => (fdistA PQR)`2 (a1, a2) *
                                    centropy1 (fdistA PQR) (a1, a2))) /=.
rewrite exchange_big pair_big /=; apply eq_bigr => -[c b] _ /=; congr (_ * _).
  by rewrite fdistA_AC_snd fdistXE.
by rewrite centropy1_fdistAC.
Qed.

End conditional_entropy_prop.
#[deprecated(since="infotheo 0.9.2", note="renamed to `centropy1_fdistAC`")]
Notation cond_entropy1_fdistAC := centropy1_fdistAC (only parsing).
#[deprecated(since="infotheo 0.9.2", note="renamed to `centropy_fdistA`")]
Notation cond_entropy_fdistA := centropy_fdistA (only parsing).

Section conditional_entropy_RV_prop.
Context {R : realType} {U A B C : finType} {P : R.-fdist U}.
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).

Let fdistA_fdistAC : fdistA (fdistAC `p_ [% X, Y, Z]) = `p_ [% X, [% Z, Y]].
Proof.
rewrite /fdistAC.
rewrite fdistC12_RV3.
rewrite fdistA_RV3.
rewrite fdistX_RV2.
by rewrite fdistA_RV3.
Qed.

Lemma centropy1_RV_fdistAC b c :
  `H[X | [% Y, Z] = (b, c)] = `H[X | [% Z, Y] = (c, b)].
Proof.
by rewrite /centropy1_RV -fdistA_RV3 centropy1_fdistAC fdistA_fdistAC.
Qed.

Lemma centropy_RV_fdistA : `H(X | [% Y, Z]) = `H(X | [% Z, Y]).
Proof.
by rewrite /centropy_RV -fdistA_RV3 centropy_fdistA fdistA_fdistAC.
Qed.

End conditional_entropy_RV_prop.

Section chain_rule.
Variables (R : realType) (A B : finType) (PQ : R.-fdist (A * B)).
Let P := PQ`1.
Let QP := fdistX PQ.

(** thm 2.1.1 *)
Lemma chain_rule : joint_entropy PQ = `H P + centropy QP. (* 2.14 *)
Proof.
rewrite /joint_entropy {1}/entropy.
transitivity (- (\sum_(a in A) \sum_(b in B)
    PQ (a, b) * log (P a * \Pr_QP [ [set b] | [set a] ]))). (* 2.16 *)
  congr (- _); rewrite pair_big /=; apply eq_bigr => -[a b] _ /=.
  congr (_ * log _); have [H0|H0] := eqVneq (P a) 0.
  - by rewrite (dom_by_fdist_fst _ H0) H0 mul0r.
  - rewrite -(Pr_set1 P a) /P -(fdistX2 PQ) mulrC -jproduct_rule setX1.
    by rewrite Pr_set1 fdistXE.
transitivity (
  - (\sum_(a in A) \sum_(b in B) PQ (a, b) * log (P a))
  - (\sum_(a in A) \sum_(b in B) PQ (a, b) * log (\Pr_QP [ [set b] | [set a] ]))). (* 2.17 *)
  rewrite -opprB; congr (- _); rewrite opprK -big_split /=.
  apply eq_bigr => a _; rewrite -big_split /=; apply eq_bigr => b _.
  have [->|H0] := eqVneq (PQ (a, b)) 0; first by rewrite !mul0r addr0.
  rewrite -mulrDr; congr (_ * _); rewrite mulrC logM //.
    by rewrite -Pr_jcPr_gt0 setX1 Pr_set1 fdistXE; rewrite -fdist_gt0.
  by rewrite -fdist_gt0; exact: dom_by_fdist_fstN H0.
rewrite [in X in _ + X = _]big_morph_oppr; congr (_ + _).
- rewrite /entropy; congr (- _); apply eq_bigr => a _.
  by rewrite -big_distrl /= -fdist_fstE.
- rewrite centropyE big_morph_oppr.
  by apply eq_bigr => a _; congr (- _); apply eq_bigr => b _; rewrite !fdistXE.
Qed.

End chain_rule.

Section chain_rule_RV.
Variable R : realType.
Variables (U A B : finType) (P : R.-fdist U) (X : {RV P -> A}) (Y : {RV P -> B}).

(** chain rule for entropy (thm 2.5.1): *)
Lemma chain_rule_RV : `H(X, Y) = `H `p_X + `H(Y | X).
Proof.
rewrite /joint_entropy_RV.
rewrite chain_rule fst_RV2.
congr (_ + _).
by rewrite fdistX_RV2.
Qed.

End chain_rule_RV.

Section chain_rule_generalization.

Local Open Scope ring_scope.

(* TODO: doc, mv? *)
Definition put_front (n : nat) (i : 'I_n.+1) : 'I_n.+1 -> 'I_n.+1 := fun j =>
  if j == i then ord0 else
    if (j < i)%nat then inord (j.+1) else
      j.

(* TODO: doc, mv? *)
Definition put_back (n : nat) (i : 'I_n.+1) : 'I_n.+1 -> 'I_n.+1 := fun j =>
  if j == ord0 then i else
    if (j <= i)%nat then inord (j.-1) else
      j.

Lemma put_backK n (i : 'I_n.+1) : cancel (put_front i) (put_back i).
Proof.
move=> j; rewrite /put_back /put_front; case: (ifPn (j == i)) => [ji|].
  rewrite eqxx; exact/esym/eqP.
rewrite neq_ltn => /orP[|] ji.
  rewrite ji ifF; last first.
    apply/negbTE/eqP => /(congr1 val) => /=.
    by rewrite inordK // ltnS (leq_trans ji) // -ltnS/=.
  rewrite inordK; last by rewrite ltnS (leq_trans ji) // -ltnS/=.
  by rewrite ji /=; apply val_inj => /=; rewrite inordK.
rewrite ltnNge (ltnW ji) /= ifF; last first.
  by apply/negbTE; rewrite -lt0n (leq_trans _ ji).
by rewrite leqNgt ji.
Qed.

Lemma put_front_inj (n : nat) (i : 'I_n.+1) : injective (put_front i).
Proof. exact: (can_inj (put_backK i)). Qed.
Arguments put_front_inj {n} _.

(* TODO: doc, mv? *)
Definition put_front_perm (n : nat) i : 'S_n.+1 := perm (put_front_inj i).

(* TODO: clean *)
Lemma fdist_col'_put_front n (R : realType) (A : finType)
    (P : R.-fdist 'rV[A]_n.+1) (i : 'I_n.+1) :
  i != ord0 ->
  fdist_col' P i = (fdist_prod_of_rV (fdist_perm P (put_front_perm i)))`2.
Proof.
move=> i0; apply/fdist_ext => /= v; rewrite fdist_col'E fdist_sndE.
destruct n as [|n']; first by rewrite (ord1 i) eqxx in i0.
transitivity (\sum_(x : A) P
  (\row_(k < n'.+2) (if k == i then x else v ``_ (inord (unbump i k)))))%R.
  rewrite (reindex_onto (fun a => \row_k (if k == i then a else v ``_ (inord (unbump i k))))
    (fun w => w ``_ i)); last first.
    move=> w wv.
    apply/rowP => j.
    rewrite !mxE; case: ifPn => [/eqP -> //|ji].
    rewrite -(eqP wv) mxE; congr (w _ _).
    move: ji; rewrite neq_ltn => /orP[|] ji.
      apply val_inj => /=.
      rewrite inordK; last first.
        by rewrite /unbump (ltnNge i j) (ltnW ji) subn0 (leq_trans ji) // -ltnS/=.
      by rewrite unbumpK //= inE ltn_eqF.
    apply val_inj => /=.
    rewrite inordK; last first.
      by rewrite /unbump ji subn1 prednK //; [rewrite -ltnS | rewrite (leq_ltn_trans _ ji)].
    by rewrite unbumpK //= inE gtn_eqF.
  apply eq_bigl => a /=.
  apply/andP; split.
    apply/eqP/rowP => k.
    rewrite !mxE eq_sym (negbTE (neq_lift _ _)).
    congr (v _ _).
    apply val_inj => /=.
    by rewrite bumpK inordK.
  by rewrite mxE eqxx.
under [RHS] eq_bigr do rewrite fdist_prod_of_rVE fdist_permE.
apply/eq_bigr => a _; congr (P _); apply/rowP => k /=.
rewrite /col_perm /= 2!mxE /=.
rewrite /put_front_perm /= permE /put_front.
case: ifPn => [ki|]; first by rewrite row_mx_row_ord0.
rewrite neq_ltn => /orP[|] ki.
  rewrite ki.
  rewrite (_ : inord _ = rshift 1 (inord k)); last first.
    apply/val_inj => /=.
    rewrite add1n inordK /=.
      by rewrite inordK // (leq_trans ki) // -ltnS/=.
    by rewrite ltnS (leq_trans ki) // -ltnS/=.
  rewrite (@row_mxEr _ _ 1); congr (v ``_ _).
  apply val_inj => /=.
  rewrite /unbump ltnNge (ltnW ki) subn0 inordK //.
  by rewrite (leq_trans ki) // -ltnS/=.
rewrite ltnNge (ltnW ki) /=; move: ki.
have [->//|k0] := eqVneq k ord0.
rewrite (_ : k = rshift 1 (inord k.-1)); last first.
  by apply val_inj => /=; rewrite add1n inordK ?prednK // ?lt0n // -ltnS.
rewrite (@row_mxEr _ 1 1) /=.
rewrite inordK ?prednK ?lt0n // -1?ltnS // ltnS add1n prednK ?lt0n // => ik.
by congr (v _ _); apply val_inj => /=; rewrite /unbump ik subn1.
Qed.

Lemma chain_rule_multivar (R : realType) (A : finType) (n : nat) (P : R.-fdist 'rV[A]_n.+1)
  (i : 'I_n.+1) : i != ord0 ->
  (`H P = `H (fdist_col' P i) +
    centropy (fdist_prod_of_rV (fdist_perm P (put_front_perm i))))%R.
Proof.
move=> i0; rewrite fdist_col'_put_front // -fdistX1.
rewrite -{2}(fdistXI (fdist_prod_of_rV _)) -chain_rule joint_entropyC fdistXI.
by rewrite entropy_fdist_prod_of_rV entropy_fdist_perm.
Qed.

End chain_rule_generalization.

Section entropy_chain_rule_corollary.
Variables (R : realType) (A B C : finType) (PQR : R.-fdist (A * B * C)).
Let PR : R.-fdist (A * C) := fdist_proj13 PQR.
Let QPR : R.-fdist (B * (A * C)) := fdistA (fdistC12 PQR).

(* eqn 2.21, H(X,Y|Z) = H(X|Z) + H(Y|X,Z) *)
Lemma chain_rule_corollary :
  centropy PQR = centropy PR + centropy QPR.
Proof.
rewrite !centropyE -opprD; congr (- _).
rewrite [in X in _ = _ + X](eq_bigr (fun j => \sum_(i in B) (fdistX QPR) ((j.1, j.2), i) *
                                                            log \Pr_QPR[[set i] | [set (j.1, j.2)]])); last by case.
rewrite -[in RHS](pair_bigA _ (fun j1 j2 => \sum_(i in B) (fdistX QPR ((j1, j2), i) *
                                                          log \Pr_QPR[[set i] | [set (j1, j2)]]))) /=.
rewrite [in X in _ = _ + X]exchange_big /= -big_split; apply eq_bigr => c _ /=.
rewrite [in LHS](eq_bigr (fun j => (fdistX PQR) (c, (j.1, j.2)) *
                                   log \Pr_PQR[[set (j.1, j.2)] | [set c]])); last by case.
rewrite -[in LHS](pair_bigA _ (fun j1 j2 => (fdistX PQR) (c, (j1, j2)) *
                                            log \Pr_PQR[[set (j1, j2)] | [set c]])) /=.
rewrite -big_split; apply eq_bigr => a _ /=.
rewrite fdistXE fdist_proj13E big_distrl /= -big_split; apply eq_bigr => b _ /=.
rewrite !(fdistXE,fdistAE,fdistC12E) /= -mulrDr.
have [->|H0] := eqVneq (PQR (a, b, c)) 0; first by rewrite !mul0r.
rewrite -logM; last 2 first.
  by rewrite -Pr_jcPr_gt0 lt0Pr setX1 Pr_set1; exact: fdist_proj13_dominN H0.
  by rewrite -Pr_jcPr_gt0 lt0Pr setX1 Pr_set1 fdistAE /= fdistC12E.
congr (_ * log _).
by rewrite -setX1 product_ruleC !setX1 mulrC.
Qed.

End entropy_chain_rule_corollary.

Section conditional_entropy_prop2. (* NB: here because use chain rule *)
Variables (R : realType) (A B : finType) (PQ : R.-fdist (A * B)).
Let P := PQ`1.
Let Q := PQ`2.
Let QP := fdistX PQ.

Lemma entropyB : `H P - centropy PQ = `H Q - centropy QP.
Proof.
apply/eqP; rewrite subr_eq addrAC -subr_eq opprK; apply/eqP.
rewrite -chain_rule joint_entropyC.
by rewrite -/(joint_entropy (fdistX PQ)) chain_rule fdistX1 -/Q fdistXI.
Qed.

End conditional_entropy_prop2.

Section conditional_entropy_prop3. (* NB: here because use chain rule *)
Variables (R : realType) (A : finType) (P : R.-fdist A).

Lemma cond_entropy_self : centropy (fdist_self P) = 0.
Proof.
move: (@chain_rule _ _ _ (fdist_self P)).
rewrite !fdist_self1 fdistX_self addrC => /eqP; rewrite -subr_eq => /eqP <-.
by rewrite joint_entropy_self subrr.
Qed.

End conditional_entropy_prop3.

Section mutual_information.
Local Open Scope divergence_scope.
Variables (R : realType) (A B : finType) (PQ : R.-fdist (A * B)).
Let P := PQ`1.
Let Q := PQ`2.
Let QP := fdistX PQ.

Definition mutual_info := D(PQ || P `x Q).

End mutual_information.

Section mutual_information_prop.
Variables (R : realType) (A B : finType) (PQ : R.-fdist (A * B)).
Let P := PQ`1.
Let Q := PQ`2.
Let QP := fdistX PQ.

(* 2.28 *)
Lemma mutual_infoE0 : mutual_info PQ =
  \sum_(a in A) \sum_(b in B) PQ (a, b) * log (PQ (a, b) / (P a * Q b)).
Proof.
rewrite /mutual_info /div pair_big /=; apply eq_bigr; case => a b _ /=.
have [->|H0] := eqVneq (PQ (a, b)) 0; first by rewrite !mul0r.
by rewrite fdist_prodE.
Qed.

(* 2.39 *)
Lemma mutual_infoE : mutual_info PQ = `H P - centropy PQ.
Proof.
rewrite mutual_infoE0.
transitivity (\sum_(a in A) \sum_(b in B)
    PQ (a, b) * log (\Pr_PQ [ [set a] | [set b] ] / P a)).
  apply eq_bigr => a _; apply eq_bigr => b _.
  rewrite /jcPr setX1 2!Pr_set1 /= -/Q.
  have [->|H0] := eqVneq (PQ (a, b)) 0; first by rewrite !mul0r.
  by congr (_ * log _); rewrite invfM mulrAC mulrA.
transitivity (- (\sum_(a in A) \sum_(b in B) PQ (a, b) * log (P a)) +
  \sum_(a in A) \sum_(b in B) PQ (a, b) * log (\Pr_PQ [ [set a] | [set b] ])). (* 2.37 *)
  rewrite big_morph_oppr -big_split; apply/eq_bigr => a _ /=.
  rewrite big_morph_oppr -big_split; apply/eq_bigr => b _ /=.
  rewrite addrC -mulrN -mulrDr.
  have [->|H0] := eqVneq (PQ (a, b)) 0; first by rewrite !mul0r.
  congr (_ * _); rewrite logDiv //.
  - by rewrite -Pr_jcPr_gt0 lt0Pr setX1 Pr_set1.
  - by rewrite -fdist_gt0; exact: dom_by_fdist_fstN H0.
congr (_ + _).
- rewrite /entropy; congr (- _); apply/eq_bigr => a _.
  by rewrite -big_distrl /= -fdist_fstE.
- rewrite /centropy exchange_big.
  rewrite big_morph_oppr; apply eq_bigr=> b _ /=.
  rewrite mulrN opprK.
  rewrite big_distrr /=; apply eq_bigr=> a _ /=.
  rewrite [in RHS]mulrCA mulrA; congr (_ * _); rewrite -/Q.
  by rewrite -[in LHS]Pr_set1 -setX1 jproduct_rule Pr_set1 -/Q mulrC.
Qed.

Lemma mutual_infoE2 : mutual_info PQ = `H Q - centropy QP. (* 2.40 *)
Proof. by rewrite mutual_infoE entropyB. Qed.

Lemma mutual_infoE3 : mutual_info PQ = `H P + `H Q - `H PQ. (* 2.41 *)
Proof.
rewrite mutual_infoE; have := chain_rule QP.
rewrite addrC => /eqP; rewrite -subr_eq -(fdistXI PQ) -/QP => /eqP <-.
by rewrite opprB fdistX1 -/Q addrA joint_entropyC.
Qed.

(* nonnegativity of mutual information 2.90 *)
Lemma mutual_info_ge0 : 0 <= mutual_info PQ.
Proof. exact/div_ge0/Prod_dominates_Joint. Qed.

Lemma mutual_info0P : mutual_info PQ = 0 <-> PQ = P `x Q.
Proof.
split; last by rewrite /mutual_info => <-; rewrite div0P //; exact: dominatesxx.
by rewrite /mutual_info div0P //; exact: Prod_dominates_Joint.
Qed.

End mutual_information_prop.

Section mutualinfo_RV_def.
Variable R : realType.
Variables (U A B : finType) (P : R.-fdist U) (X : {RV P -> A}) (Y : {RV P -> B}).

Definition mutual_info_RV := mutual_info `p_[% X, Y].

End mutualinfo_RV_def.
Notation "'`I(' X ';' Y ')'" := (mutual_info_RV X Y) : entropy_scope.

Section mutual_info0_indep.

Variable R : realType.
Variables (U A B : finType) (P : R.-fdist U) (X : {RV P -> A}) (Y : {RV P -> B}).

Lemma mutual_info0_indep:
  mutual_info_RV X Y = 0 -> P |= X _|_ Y.
Proof.
move/mutual_info0P.
rewrite fst_RV2 snd_RV2 => H x y.
by rewrite !pr_eqE' H fdist_prodE.
Qed.

Lemma mutual_info_RVE:
  `I(X;Y) = `H `p_X - `H(X | Y).
Proof. by rewrite /mutual_info_RV mutual_infoE fst_RV2. Qed.

End mutual_info0_indep.


(* TODO: example 2.3.1 *)

Section mutualinfo_prop.
Local Open Scope divergence_scope.

(* eqn 2.46 *)
Lemma mutual_info_sym (R : realType) (A B : finType) (PQ : R.-fdist (A * B)) :
  mutual_info PQ = mutual_info (fdistX PQ).
Proof. by rewrite !mutual_infoE entropyB fdistX1. Qed.

(* eqn 2.47 *)
Lemma mutual_info_self (R : realType) (A : finType) (P : R.-fdist A) :
  mutual_info (fdist_self P) = `H P.
Proof. by rewrite mutual_infoE cond_entropy_self subr0 fdist_self1. Qed.

End mutualinfo_prop.

Section chain_rule_for_entropy.
Local Open Scope vec_ext_scope.

Lemma entropy_head_of1 (R : realType) (A : finType) (P : R.-fdist 'M[A]_1) :
  `H P = `H (head_of_fdist_rV P).
Proof.
rewrite /entropy; congr (- _); apply: big_rV_1 => // a.
rewrite /head_of_fdist_rV fdist_fstE /= big_rV0_row_of_tuple fdist_prod_of_rVE/=;
congr (P _ * log (P _)); apply/rowP => i.
  by rewrite (ord1 i) !mxE; case: splitP => // i0; rewrite (ord1 i0) mxE.
by rewrite (ord1 i) !mxE; case: splitP => // i0; rewrite (ord1 i0) mxE.
Qed.

Lemma chain_rule_rV (R : realType) (A : finType) (n : nat) (P : R.-fdist 'rV[A]_n.+1) :
  `H P = \sum_(i < n.+1)
          if i == O :> nat then
            `H (head_of_fdist_rV P)
          else
            centropy (fdistX (fdist_belast_last_of_rV (fdist_take P (lift ord0 i)))).
Proof.
elim: n P => [P|n IH P].
  by rewrite big_ord_recl /= big_ord0 addr0 -entropy_head_of1.
rewrite entropy_rV chain_rule {}IH [in RHS]big_ord_recr /=.
rewrite fdist_take_all; congr (_ + _); apply eq_bigr => i _.
case: ifP => i0; first by rewrite head_of_fdist_rV_belast_last.
congr (centropy (fdistX (fdist_belast_last_of_rV _))).
rewrite /fdist_take /fdist_fst /fdist_belast_last_of_rV !fdistmap_comp.
congr (fdistmap _ P); rewrite boolp.funeqE => /= v.
apply/rowP => j; rewrite !mxE !castmxE /= !mxE /= cast_ord_id; congr (v _ _).
exact: val_inj.
Qed.

End chain_rule_for_entropy.

Section divergence_conditional_distributions.
Variables (R : realType) (A B C : finType) (PQR : R.-fdist (A * B * C)).

(* TODO: document *)
Definition cdiv1 z := \sum_(x in {: A * B})
  \Pr_PQR[[set x] | [set z]] * log (\Pr_PQR[[set x] | [set z]] /
    (\Pr_(fdist_proj13 PQR)[[set x.1] | [set z]] * \Pr_(fdist_proj23 PQR)[[set x.2] | [set z]])).

Local Open Scope divergence_scope.

Lemma cdiv1_is_div (c : C) (Hc  : (fdistX PQR)`1 c != 0)
                           (Hc1 : (fdistX (fdist_proj13 PQR))`1 c != 0)
                           (Hc2 : (fdistX (fdist_proj23 PQR))`1 c != 0) :
  cdiv1 c = D((fdistX PQR) `(| c ) ||
    ((fdistX (fdist_proj13 PQR)) `(| c )) `x ((fdistX (fdist_proj23 PQR)) `(| c ))).
Proof.
rewrite /cdiv1 /div; apply eq_bigr => -[a b] /= _; rewrite jfdist_condE //.
rewrite fdistXI.
have [->|H0] := eqVneq (\Pr_PQR[[set (a, b)]|[set c]]) 0; first by rewrite !mul0r.
by rewrite fdist_prodE /= jfdist_condE // jfdist_condE // !fdistXI.
Qed.

Lemma cdiv1_ge0 z : 0 <= cdiv1 z.
Proof.
have [z0|z0] := eqVneq (PQR`2 z) 0.
  apply/sumr_ge0 => -[a b] _.
  rewrite {1}/jcPr setX1 [X in X / _ * _]Pr_set1/= (dom_by_fdist_snd (a, b) z0).
  by rewrite !mul0r.
have Hc : (fdistX PQR)`1 z != 0 by rewrite fdistX1.
have Hc1 : (fdistX (fdist_proj13 PQR))`1 z != 0.
  by rewrite fdistX1 fdist_proj13_snd.
have Hc2 : (fdistX (fdist_proj23 PQR))`1 z != 0.
  by rewrite fdistX1 fdist_proj23_snd.
rewrite cdiv1_is_div //; apply div_ge0.
(* TODO: lemma *)
apply/dominatesP => -[a b].
rewrite fdist_prodE !jfdist_condE //= => /eqP; rewrite mulf_eq0 => /orP[|].
- rewrite /jcPr !setX1 !Pr_set1 !mulf_eq0 => /orP[|].
    rewrite !fdistXI => /eqP.
    by move/fdist_proj13_domin => ->; rewrite mul0r.
  rewrite !fdistXI => /eqP.
  by rewrite fdist_proj13_snd => ->; rewrite mulr0.
- rewrite /jcPr !setX1 !Pr_set1 mulf_eq0 => /orP[|].
    rewrite !fdistXI => /eqP.
    by move/fdist_proj23_domin => ->; rewrite mul0r.
  by rewrite !fdistXI fdist_proj23_snd => /eqP ->; rewrite mulr0.
Qed.

End divergence_conditional_distributions.

Section conditional_mutual_information.
Section def.
Variables (R : realType) (A B C : finType) (PQR : R.-fdist (A * B * C)).

(* I(X;Y|Z) = H(X|Z) - H(X|Y,Z) 2.60 *)
Definition cond_mutual_info :=
  centropy (fdist_proj13 PQR) - centropy (fdistA PQR).
End def.

Section prop.
Variables (R : realType) (A B C : finType) (PQR : R.-fdist (A * B * C)).

Lemma cond_mutual_infoE : cond_mutual_info PQR = \sum_(x in {: A * B * C}) PQR x *
  log (\Pr_PQR[[set x.1] | [set x.2]] /
       (\Pr_(fdist_proj13 PQR)[[set x.1.1] | [set x.2]] *
        \Pr_(fdist_proj23 PQR)[[set x.1.2] | [set x.2]])).
Proof.
rewrite /cond_mutual_info 2!centropyE /= big_morph_oppr.
rewrite (eq_bigr (fun a => \sum_(b in A) (fdistX (fdistA PQR)) (a.1, a.2, b) *
                                          log \Pr_(fdistA PQR)[[set b] | [set (a.1, a.2)]])); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => \sum_(b in A) (fdistX (fdistA PQR)) ((a1, a2), b) *
                                                   log \Pr_(fdistA PQR)[[set b] | [set (a1, a2)]])).
rewrite /= exchange_big /= opprK -big_split /=.
rewrite (eq_bigr (fun x => PQR (x.1, x.2) * log
(\Pr_PQR[[set x.1] | [set x.2]] /
        (\Pr_(fdist_proj13 PQR)[[set x.1.1] | [set x.2]] *
         \Pr_(fdist_proj23 PQR)[[set x.1.2] | [set x.2]])))); last by case.
rewrite -(pair_bigA _ (fun x1 x2 => PQR (x1, x2) * log
(\Pr_PQR[[set x1] | [set x2]] /
        (\Pr_(fdist_proj13 PQR)[[set x1.1] | [set x2]] *
         \Pr_(fdist_proj23 PQR)[[set x1.2] | [set x2]])))).
rewrite /= exchange_big; apply eq_bigr => c _.
rewrite big_morph_oppr /= exchange_big -big_split /=.
rewrite (eq_bigr (fun i => PQR ((i.1, i.2), c) * log
       (\Pr_PQR[[set (i.1, i.2)] | [set c]] /
        (\Pr_(fdist_proj13 PQR)[[set i.1] | [set c]] *
         \Pr_(fdist_proj23 PQR)[[set i.2] | [set c]])))); last by case.
rewrite -(pair_bigA _ (fun i1 i2 => PQR (i1, i2, c) * log
  (\Pr_PQR[[set (i1, i2)] | [set c]] /
  (\Pr_(fdist_proj13 PQR)[[set i1] | [set c]] * \Pr_(fdist_proj23 PQR)[[set i2] | [set c]])))).
apply eq_bigr => a _ /=.
rewrite fdistXE fdist_proj13E big_distrl /= big_morph_oppr -big_split.
apply eq_bigr => b _ /=.
rewrite fdistXE fdistAE /= -mulrN -mulrDr.
have [->|H0] := eqVneq (PQR (a, b, c)) 0; first by rewrite !mul0r.
congr (_ * _).
rewrite addrC -logDiv; last 2 first.
  by rewrite -Pr_jcPr_gt0 lt0Pr setX1 Pr_set1; exact: fdistA_dominN H0.
  by rewrite -Pr_jcPr_gt0 lt0Pr setX1 Pr_set1; exact: fdist_proj13_dominN H0.
congr (log _).
rewrite [in RHS]invfM mulrCA [RHS]mulrC; congr (_ / _).
rewrite -[in X in _ = X * _]setX1 jproduct_rule_cond setX1 -mulrA mulfV ?mulr1 //.
rewrite /jcPr mulf_neq0// ?setX1 !Pr_set1.
  exact: fdist_proj23_dominN H0.
by rewrite fdist_proj23_snd invr_eq0; exact: dom_by_fdist_sndN H0.
Qed.

Let PQR2 := (PQR`2).

Lemma cond_mutual_infoE2 : cond_mutual_info PQR = \sum_(z in C) PQR2 z * cdiv1 PQR z.
Proof.
rewrite cond_mutual_infoE.
rewrite (eq_bigr (fun x => PQR (x.1, x.2) * log
  (\Pr_PQR[[set x.1] | [set x.2]] /
    (\Pr_(fdist_proj13 PQR)[[set x.1.1] | [set x.2]] *
     \Pr_(fdist_proj23 PQR)[[set x.1.2] | [set x.2]])))); last by case.
rewrite -(pair_bigA _ (fun x1 x2 => PQR (x1, x2) * log
  (\Pr_PQR[[set x1] | [set x2]] /
    (\Pr_(fdist_proj13 PQR)[[set x1.1] | [set x2]] *
     \Pr_(fdist_proj23 PQR)[[set x1.2] | [set x2]])))).
rewrite exchange_big; apply eq_bigr => c _ /=.
rewrite big_distrr /=; apply eq_bigr => -[a b] _ /=; rewrite mulrA; congr (_ * _).
rewrite mulrC.
move: (jproduct_rule PQR [set (a, b)] [set c]); rewrite -/R Pr_set1 => <-.
by rewrite setX1 Pr_set1.
Qed.

(* 2.92 *)
Lemma cond_mutual_info_ge0 : 0 <= cond_mutual_info PQR.
Proof.
rewrite cond_mutual_infoE2; apply/sumr_ge0 => c _; apply/mulr_ge0 => //.
exact: cdiv1_ge0.
Qed.

Let P : R.-fdist A := (fdistA PQR)`1.
Let Q : R.-fdist B := (PQR`1)`2.

Lemma chain_rule_mutual_info : mutual_info PQR = mutual_info (fdist_proj13 PQR) +
                                                 cond_mutual_info (fdistX (fdistA PQR)).
Proof.
rewrite mutual_infoE.
have := chain_rule (PQR`1); rewrite /joint_entropy => ->.
rewrite (chain_rule_corollary PQR).
rewrite opprD addrCA 2!addrA -(addrA (- _ + _)); congr (_ + _).
  rewrite mutual_infoE addrC; congr (_ - _).
  by rewrite fdist_proj13_fst fdistA1.
rewrite /cond_mutual_info; congr (centropy _ - _).
  by rewrite /fdist_proj13 -/(fdistC13 _) fdistA_C13_snd.
(* TODO: lemma *)
rewrite /centropy.
rewrite (eq_bigr (fun a => (fdistA (fdistC12 PQR))`2 (a.1, a.2) *
                            centropy1 (fdistA (fdistC12 PQR)) (a.1, a.2))); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => (fdistA (fdistC12 PQR))`2 (a1, a2) *
                                     centropy1 (fdistA (fdistC12 PQR)) (a1, a2))).
rewrite exchange_big pair_big; apply eq_bigr => -[c a] _ /=; congr (_ * _).
  rewrite !fdist_sndE; apply eq_bigr => b _.
  by rewrite !(fdistXE,fdistAE,fdistC12E).
rewrite /centropy1; congr (- _).
by under eq_bigr do rewrite -setX1 jcPr_fdistA_C12 setX1.
Qed.
End prop.

End conditional_mutual_information.

Section conditional_relative_entropy.
Section def.
Variable R : realType.
Variables (A B : finType) (P Q : (R.-fdist A * (A -> R.-fdist B))).
Let Pj : R.-fdist (B * A) := fdistX (P.1 `X P.2).
Let Qj : R.-fdist (B * A) := fdistX (Q.1 `X Q.2).
Let P1 : R.-fdist A := P.1.

(* eqn 2.65 *)
Definition cond_relative_entropy := \sum_(x in A) P1 x * \sum_(y in B)
  \Pr_Pj[[set y]|[set x]] * log (\Pr_Pj[[set y]|[set x]] / \Pr_Qj[[set y]|[set x]]).

End def.

Section prop.
Local Open Scope divergence_scope.
Local Open Scope reals_ext_scope.
Variables (R : realType) (A B : finType) (P Q : (R.-fdist A * (A -> R.-fdist B))).
Let Pj : R.-fdist (B * A) := fdistX (P.1 `X P.2).
Let Qj : R.-fdist (B * A) := fdistX (Q.1 `X Q.2).
Let P1 : R.-fdist A := P.1.
Let Q1 : R.-fdist A := Q.1.

(** chain rule for relative entropy (thm 2.5.3): *)
Lemma chain_rule_relative_entropy :
  Pj `<< Qj -> D(Pj || Qj) = D(P1 || Q1) + cond_relative_entropy P Q.
Proof.
move=> PQ.
rewrite {2}/div /cond_relative_entropy -big_split /= {1}/div /=.
rewrite (eq_bigr (fun a => Pj (a.1, a.2) * (log (Pj (a.1, a.2) / (Qj (a.1, a.2)))))); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => Pj (a1, a2) * (log (Pj (a1, a2) / (Qj (a1, a2)))))) /=.
rewrite exchange_big; apply eq_bigr => a _ /=.
rewrite [in X in _ = X * _ + _](_ : P1 a = Pj`2 a); last by rewrite /P fdistX2 fdist_prod1.
rewrite fdist_sndE big_distrl /= big_distrr /= -big_split /=; apply eq_bigr => b _.
rewrite [X in _ = _ + X]mulrA [X in _ = _ + X * _](_ : P.1 a * _ = Pj (b, a)); last first.
  rewrite /jcPr Pr_set1 -/P1 mulrCA setX1 Pr_set1 {1}/Pj fdistX2 fdist_prod1.
  have [P2a0|P2a0] := eqVneq (P1 a) 0.
    have Pba0 : Pj (b, a) = 0.
      by rewrite /P fdistXE fdist_prodE P2a0 mul0r.
    by rewrite Pba0 mul0r.
  by rewrite mulfV // ?mulr1.
rewrite -mulrDr.
have [->|H0] := eqVneq (Pj (b, a)) 0; first by rewrite !mul0r.
congr (_ * _).
have P1a0 : P1 a != 0.
  apply: contra H0 => /eqP.
  by rewrite /P fdistXE fdist_prodE => ->; rewrite mul0r.
have Qba0 := dominatesEN PQ H0.
have Q2a0 : Q1 a != 0.
  apply: contra Qba0; rewrite /Q fdistXE fdist_prodE => /eqP ->; by rewrite mul0r.
rewrite -logM; last 2 first.
  by apply/divr_gt0; rewrite -fdist_gt0.
  by apply/divr_gt0; by rewrite -Pr_jcPr_gt0 setX1 Pr_set1; rewrite -fdist_gt0.
congr (log _).
rewrite /jcPr !setX1 !Pr_set1.
rewrite !fdistXE !fdistX2 !fdist_prod1 !fdist_prodE /=.
rewrite -/P1 -/Q1.
rewrite -(mulrA (Q1 a)) (mulrCA (Q1 a)) divff// mulr1.
rewrite -[in X in _ = _ * X](mulrA (P1 a)) (mulrCA (P1 a)) divff// mulr1.
rewrite -!mulrA; congr *%R.
rewrite mulrCA; congr *%R.
by rewrite invfM.
Qed.

End prop.

End conditional_relative_entropy.

Section chain_rule_for_information.
Variables (R : realType) (A : finType).
Let B := A. (* need in the do-not-delete-me step *)
Variables (n : nat) (PY : R.-fdist ('rV[A]_n.+1 * B)).
Let P : R.-fdist 'rV[A]_n.+1 := PY`1.
Let Y : R.-fdist B := PY`2.

Let f (i : 'I_n.+1) : R.-fdist (A * 'rV[A]_i * B) := fdistC12 (fdist_prod_take PY i).
Let fAC (i : 'I_n.+1) : R.-fdist (A * B * 'rV[A]_i) := fdistAC (f i).
Let fA (i : 'I_n.+1) : R.-fdist (A * ('rV[A]_i * B)) := fdistA (f i).

Local Open Scope vec_ext_scope.

(** chain rule for information (thm 2.5.2): *)
Lemma chain_rule_information :
  (* 2.62 *) mutual_info PY = \sum_(i < n.+1)
    if i == O :> nat then
      mutual_info (fdist_prod_nth PY ord0)
    else
      cond_mutual_info (fAC i).
Proof.
rewrite mutual_infoE chain_rule_rV.
have -> : centropy PY = \sum_(j < n.+1)
  if j == O :> nat then
    centropy (fdist_prod_nth PY ord0)
  else
    centropy (fA j).
  have := chain_rule (fdistX PY).
  rewrite fdistXI addrC => /eqP; rewrite -subr_eq fdistX1 -/Y => /eqP <-.
  rewrite /joint_entropy.
  (* do-not-delete-me *)
  set YP : R.-fdist 'rV[A]_n.+2 := fdist_rV_of_prod (fdistX PY).
  transitivity (`H YP - `H Y); first by rewrite /YP entropy_fdist_rV_of_prod.
  rewrite (chain_rule_rV YP).
  rewrite [in LHS]big_ord_recl /=.
  rewrite (_ : `H (head_of_fdist_rV YP) = `H Y); last first.
    by rewrite /YP /head_of_fdist_rV (fdist_prod_of_rVK (fdistX PY)) fdistX1.
  rewrite addrAC subrr add0r.
  apply eq_bigr => j _.
  case: ifPn => j0.
  - have {}j0 : j = ord0 by move: j0 => /eqP j0; exact/val_inj.
    subst j.
    rewrite /centropy /=.
    apply big_rV_1 => // a1.
    have H1 a : (fdistX (fdist_belast_last_of_rV (fdist_take YP (lift ord0 (lift ord0 ord0))))) (a, a1) =
       (fdist_prod_nth PY ord0) (a, a1 ``_ ord0).
      rewrite fdistXE fdist_belast_last_of_rVE.
      rewrite (fdist_takeE _ (lift ord0 (lift ord0 ord0))) fdist_prod_nthE /=.
      have H1 : (n.+2 - bump 0 (bump 0 0) = n)%nat.
        by rewrite /bump !leq0n !add1n subn2.
      rewrite (big_cast_rV H1).
      rewrite (eq_bigr (fun x => PY (x.1, x.2))); last by case.
      rewrite -(pair_big (fun i : 'rV_n.+1 => i ``_ ord0 == a) (fun i => i == a1 ``_ ord0) (fun i1 i2 => PY (i1, i2))) /=.
      rewrite [in RHS](eq_bigl (fun i : 'rV_n.+1 => (xpred1 a (i ``_ ord0)) && (xpredT i))); last first.
        move=> i; by rewrite andbT.
      rewrite -(big_rV_cons_behead (fun i => \sum_(j | j == a1 ``_ ord0) PY (i, j))
                                   (fun i => i == a) xpredT).
      rewrite exchange_big /=.
      apply eq_bigr => v _.
      rewrite big_pred1_eq.
      rewrite big_pred1_eq.
      rewrite /YP.
      rewrite fdist_rV_of_prodE fdistXE /=; congr (PY (_, _)).
        apply/rowP => i.
        rewrite mxE castmxE /=.
        move: (leq0n i); rewrite leq_eqVlt => /orP[/eqP|] i0.
          move=> [:Hi1].
          have @i1 : 'I_(bump 0 0).+1.
            apply: (@Ordinal _ i.+1); abstract: Hi1.
            by rewrite /bump leq0n add1n -i0.
          rewrite (_ : cast_ord _ _ = lshift (n.+2 - bump 0 (bump 0 0)) i1); last exact/val_inj.
          rewrite row_mxEl castmxE /= 2!cast_ord_id.
          rewrite (_ : cast_ord _ _ = rshift 1 (Ordinal (ltn_ord ord0))); last first.
            by apply val_inj => /=; rewrite add1n -i0.
          rewrite row_mxEr mxE.
          set i2 : 'I_1 := Ordinal (ltn_ord ord0).
          rewrite (_ : i = lshift n i2); last exact/val_inj.
          by rewrite (@row_mxEl _ _ 1) mxE.
        move=> [:Hi1].
        have @i1 : 'I_(n.+2 - bump 0 (bump 0 0)).
          apply: (@Ordinal _ i.-1); abstract: Hi1.
          by rewrite /bump !leq0n !add1n subn2 prednK //= -ltnS.
        rewrite (_ : cast_ord _ _ = rshift (bump 0 0).+1 i1); last first.
          by apply/val_inj => /=; rewrite /bump !leq0n !add1n add2n prednK.
        rewrite row_mxEr castmxE /= !cast_ord_id.
        have @i2 : 'I_n by apply: (@Ordinal _ i.-1); rewrite prednK // -ltnS.
        rewrite (_ : i = rshift 1 i2); last first.
          by apply/val_inj => /=; rewrite add1n prednK.
        rewrite (@row_mxEr _ _ 1) //; congr (v _ _); exact/val_inj.
      rewrite castmxE /=.
      rewrite (_ : cast_ord _ _ = lshift (n.+2 - bump 0 (bump 0 0)) (Ordinal (ltn_ord ord0))); last exact/val_inj.
      rewrite row_mxEl castmxE /= 2!cast_ord_id.
      rewrite (_ : cast_ord _ _ = lshift 1 (Ordinal (ltn_ord ord0))); last exact/val_inj.
      rewrite row_mxEl /=; congr (a1 ``_ _); exact/val_inj.
    congr (_ * _).
      rewrite 2!fdist_sndE; apply eq_bigr => a _; by rewrite H1.
    rewrite /centropy1; congr (- _).
    apply eq_bigr => a _; congr (_ * log _).
    + rewrite /jcPr /Pr !big_setX /= !big_set1.
      rewrite H1; congr (_ / _).
      rewrite !fdist_sndE; apply eq_bigr => a0 _.
      by rewrite H1.
    + rewrite /jcPr /Pr !big_setX /= !big_set1.
      rewrite H1; congr (_ / _).
      rewrite !fdist_sndE; apply eq_bigr => a0 _.
      by rewrite H1.
  - rewrite /fA /f.
    rewrite /centropy /=.
    have H1 : bump 0 j = j.+1 by rewrite /bump leq0n.
    rewrite (big_cast_rV H1) /=.
    rewrite -(big_rV_cons_behead _ xpredT xpredT) /= exchange_big /= pair_bigA.
    have H2 (v : 'rV_j) (b : B) (a : A) (H1' : (1 + j)%nat = lift ord0 j) :
      (fdistX (fdist_belast_last_of_rV (fdist_take YP (lift ord0 (lift ord0 j)))))
      (a, (castmx (erefl 1%nat, H1') (row_mx (\row__ b) v))) =
      (fdistA (fdistC12 (fdist_prod_take PY j))) (a, (v, b)).
      rewrite /YP /fdistX /fdist_belast_last_of_rV /fdist_take /fdist_rV_of_prod.
      rewrite /fdistA /fdistC12 /fdist_prod_take !fdistmap_comp !fdistmapE /=.
      apply eq_bigl => -[w b0]; rewrite /= !inE /=.
      rewrite (_ : rlast _ = w ``_ j); last first.
        rewrite /rlast !mxE !castmxE /= cast_ord_id.
        rewrite (_ : cast_ord _ _ = rshift 1%nat j); last exact/val_inj.
        by rewrite (@row_mxEr _ 1%nat 1%nat n.+1).
      rewrite !xpair_eqE; congr (_ && _).
      rewrite (_ : rbelast _ =
        row_take (lift ord0 j) (rbelast (row_mx (\row_(k<1) b0) w))); last first.
        apply/rowP => i; rewrite !mxE !castmxE /= esymK !cast_ord_id.
        by rewrite /rbelast mxE; congr (row_mx _ _ _ _); exact: val_inj.
      rewrite (_ : rbelast _ = row_mx (\row_(k<1) b0) (rbelast w)); last first.
        apply/rowP => i; rewrite mxE /rbelast.
        have [i0|i0] := eqVneq (i : nat) O.
          rewrite (_ : widen_ord _ _ = ord0); last exact: val_inj.
          rewrite (_ : i = ord0); last exact: val_inj.
          by rewrite 2!row_mx_row_ord0.
        have @k : 'I_n.+1.
          apply: (@Ordinal _ i.-1).
          by rewrite prednK // ?lt0n // -ltnS (leq_trans (ltn_ord i)).
        rewrite (_ : widen_ord _ _ = rshift 1%nat k); last first.
          by apply val_inj => /=; rewrite -subn1 subnKC // lt0n.
        rewrite (@row_mxEr _ 1%nat 1%nat n.+1).
        have @k' : 'I_n.
          apply: (@Ordinal _ i.-1).
          by rewrite prednK // ?lt0n // -ltnS (leq_trans (ltn_ord i)).
        rewrite (_ : i = rshift 1%nat k'); last first.
          by apply val_inj => /=; rewrite -subn1 subnKC // lt0n.
        rewrite (@row_mxEr _ 1%nat 1%nat n) mxE; congr (w ord0 _); exact: val_inj.
      apply/idP/idP; last first.
        move/andP => /= [/eqP <- /eqP ->].
        apply/eqP/rowP => k.
        rewrite !mxE !castmxE /= esymK !cast_ord_id.
        have [k0|k0] := eqVneq (nat_of_ord k) 0%N.
          rewrite (_ : cast_ord _ _ = ord0); last exact: val_inj.
          rewrite (_ : k = ord0); last exact: val_inj.
          by rewrite 2!row_mx_row_ord0.
        have @l : 'I_n.
          apply: (@Ordinal _ k.-1).
          by rewrite prednK // ?lt0n // -ltnS (leq_trans (ltn_ord k)).
        rewrite (_ : cast_ord _ _ = rshift 1%nat l); last first.
          by apply val_inj => /=; rewrite add1n prednK // lt0n.
        rewrite (@row_mxEr _ 1%nat 1%nat n) //.
        have @l0 : 'I_(widen_ord (leqnSn n.+1) j).
          apply: (@Ordinal _ k.-1).
          by rewrite prednK // ?lt0n // -ltnS (leq_trans (ltn_ord k)).
        rewrite (_ : k = rshift 1%nat l0); last first.
          by apply val_inj => /=; rewrite add1n prednK // lt0n.
        rewrite (@row_mxEr _ 1%nat 1%nat) //.
        rewrite !mxE !castmxE /= cast_ord_id; congr (w _ _).
        exact: val_inj.
      move/eqP/rowP => H.
      move: (H ord0).
      rewrite !mxE !castmxE /= 2!cast_ord_id esymK.
      rewrite (_ : cast_ord _ _ = ord0); last exact: val_inj.
      rewrite 2!row_mx_row_ord0 => ->; rewrite eqxx andbT.
      apply/eqP/rowP => k.
      have @k1 : 'I_(bump 0 j).
        apply: (@Ordinal _ k.+1).
        by rewrite /bump leq0n add1n ltnS.
      move: (H k1).
      rewrite !mxE !castmxE /= esymK !cast_ord_id.
      have @k2 : 'I_n.
        apply: (@Ordinal _ k).
        by rewrite (leq_trans (ltn_ord k)) // -ltnS (leq_trans (ltn_ord j)).
      rewrite (_ : cast_ord _ _ = rshift 1%nat k2); last first.
        by apply val_inj => /=; rewrite add1n.
      rewrite (@row_mxEr _ 1%nat 1%nat) mxE.
      rewrite (_ : cast_ord _ _ = widen_ord (leqnSn n) k2); last exact: val_inj.
      move=> ->.
      rewrite (_ : k1 = rshift 1%nat k); last by apply val_inj => /=; rewrite add1n.
      by rewrite row_mxEr.
    apply eq_bigr => -[v b] _ /=.
    rewrite 2!fdist_sndE; congr (_ * _).
      apply eq_bigr => a _.
      rewrite -H2.
      by rewrite (_ : esym H1 = H1).
    rewrite /centropy1; congr (- _).
    apply eq_bigr => a _.
    rewrite /jcPr /Pr !big_setX /= !big_set1.
    rewrite !H2 //=.
    congr (_ / _ * log (_ / _)).
    + by rewrite 2!fdist_sndE; apply eq_bigr => a' _; rewrite H2.
    + by rewrite 2!fdist_sndE; apply eq_bigr => a' _; rewrite H2.
rewrite big_morph_oppr -big_split /=; apply eq_bigr => j _ /=.
case: ifPn => j0.
- rewrite mutual_infoE; congr (`H _ - _).
  rewrite /head_of_fdist_rV /fdist_fst /fdist_rV_of_prod.
  by rewrite /fdist_prod_nth !fdistmap_comp.
- rewrite /cond_mutual_info /fA -/P; congr (_ - _).
  + congr centropy.
    by rewrite /fAC /f fdist_proj13_AC fdistC12_fst belast_last_take.
  + rewrite /fAC /f /fdistAC fdistC12I /centropy /=.
    rewrite (eq_bigr (fun a => (fdistA (fdistC12 (fdist_prod_take PY j)))`2 (a.1, a.2) *
       centropy1 (fdistA (fdistC12 (fdist_prod_take PY j))) (a.1, a.2))); last by case.
    rewrite -(pair_bigA _ (fun a1 a2 => (fdistA (fdistC12 (fdist_prod_take PY j)))`2 (a1, a2) *
       centropy1 (fdistA (fdistC12 (fdist_prod_take PY j))) (a1, a2))) /=.
    rewrite exchange_big pair_bigA /=; apply eq_bigr => -[b v] _ /=.
    congr (_ * _).
    * rewrite !fdist_sndE; apply eq_bigr=> a _.
      by rewrite !fdistAE /= fdistXE fdistC12E /= fdistAE.
    * (* TODO: lemma? *)
      rewrite /centropy1; congr (- _); apply eq_bigr => a _.
      by rewrite -!setX1 -jcPr_fdistA_AC /fdistAC fdistC12I.
Qed.

End chain_rule_for_information.

Section conditioning_reduces_entropy.
Section prop.
Variables (R : realType) (A B : finType) (PQ : R.-fdist (A * B)).
Let P := PQ`1.
Let Q := PQ`2.
Let QP := fdistX PQ.

(* 2.95 *)
Lemma information_cant_hurt : centropy PQ <= `H P.
Proof. by rewrite -subr_ge0 -mutual_infoE; exact: mutual_info_ge0. Qed.

Lemma condentropy_indep : PQ = P `x Q -> centropy PQ = `H P.
Proof.
by move/mutual_info0P; rewrite mutual_infoE => /eqP; rewrite subr_eq0 => /eqP <-.
Qed.

End prop.

Section prop2.
Variables (R : realType) (A B C : finType) (PQR : R.-fdist (A * B * C)).
Let P : R.-fdist A := (fdistA PQR)`1.
Let Q : R.-fdist B := (PQR`1)`2.
Lemma mi_bound : PQR`1 = P `x Q (* P and Q independent *) ->
  mutual_info (fdist_proj13 PQR) +
  mutual_info (fdist_proj23 PQR) <= mutual_info PQR.
Proof.
move=> PQ; rewrite chain_rule_mutual_info lerD2l /cond_mutual_info.
rewrite [X in _ <= X - _](_ : _ = `H Q); last first.
  rewrite condentropy_indep; last first.
    rewrite fdist_proj13_fst fdistA1 fdistX1 fdistA21 -/Q.
    rewrite fdist_proj13_snd fdistX2 -/P.
    rewrite -[RHS]fdistXI fdistX_prod -PQ.
    apply/fdist_ext => -[b a]. (* TODO: lemma? *)
    rewrite fdist_proj13E fdistXE fdist_fstE; apply eq_bigr => c _.
    by rewrite fdistXE fdistAE.
  by rewrite /fdist_proj13 fdistA21 fdistC12_fst fdistX1 fdistX2 fdistA21 -/Q.
rewrite mutual_infoE.
rewrite fdist_proj23_fst -/Q.
rewrite -[leLHS]opprB lerNl opprB lerD2r.
(* conditioning cannot increase entropy *)
(* Q|R,P <= Q|R, lemma *)
rewrite -subr_ge0.
move: (cond_mutual_info_ge0 (fdistC12 PQR)); rewrite /cond_mutual_info.
rewrite /fdist_proj13 fdistC12I -/(fdist_proj23 _).
by rewrite centropy_fdistA /fdistAC fdistC12I.
Qed.
End prop2.

End conditioning_reduces_entropy.

(* TODO: example 2.6.1 *)

Section independence_bound_on_entropy.
Variables (R : realType) (A : finType) (n : nat) (P : R.-fdist 'rV[A]_n.+1).

(* thm 2.6.6 TODO: with equality in case of independence *)
Lemma independence_bound_on_entropy : `H P <= \sum_(i < n.+1) `H (fdist_nth P i).
Proof.
rewrite chain_rule_rV; apply ler_sum => /= i _.
case: ifPn => [/eqP|] i0.
  rewrite (_ : i = ord0); last exact/val_inj.
  rewrite head_of_fdist_rV_fdist_nth.
  by rewrite lexx.
apply: le_trans; first exact: information_cant_hurt.
rewrite fdistX1 fdist_take_nth.
by rewrite lexx.
Qed.

End independence_bound_on_entropy.

Section markov_chain.
Variables (R : realType) (A B C : finType) (PQR : R.-fdist (A * B * C)).
Let P := PQR`1`1.
Let Q := PQR`1`2.
Let PQ := PQR`1.
Let QP := fdistX PQ.
Let RQ := fdistX ((fdistA PQR)`2).

(* cond. distr. of Z depends only on Y and conditionally independent of X *)
Definition markov_chain := forall (x : A) (y : B) (z : C),
  PQR (x, y, z) = P x * \Pr_QP[ [set y] | [set x]] * \Pr_RQ[ [set z] | [set y]].

Let PRQ := fdistAC PQR.

(* X and Z are conditionally independent given Y TODO: iff *)
Lemma markov_cond_mutual_info :
  markov_chain -> cond_mutual_info (PRQ : R.-fdist (A * C * B)) = 0.
Proof.
rewrite /markov_chain => mc.
rewrite cond_mutual_infoE (eq_bigr (fun=> 0)) ?big1// => x _.
have [->|H0] := eqVneq (PRQ x) 0; first by rewrite mul0r.
rewrite (_ : _ / _ = 1); first by rewrite log1 mulr0.
rewrite eqr_divrMr ?mul1r; last first.
  rewrite mulf_neq0//.
    (* TODO: lemma? *)
    rewrite /jcPr mulf_neq0 (* TODO: lemma divf_neq0 *) //.
      rewrite setX1 Pr_set1.
      case: x => [[x11 x12] x2] in H0 *.
      exact: fdist_proj13_dominN H0.
    rewrite invr_eq0 Pr_set1 fdist_proj13_snd.
    case: x => [x1 x2] in H0 *.
    exact: dom_by_fdist_sndN H0.
  (* TODO: lemma? *)
  rewrite /jcPr mulf_neq0 //.
    rewrite setX1 Pr_set1.
    case: x => [[x11 x12] x2] in H0 *.
    exact: fdist_proj23_dominN H0.
  rewrite invr_eq0.
  rewrite Pr_set1 fdist_proj23_snd.
  case: x => [x1 x2] in H0 *.
  exact: dom_by_fdist_sndN H0.
(* TODO: lemma? *) (* 2.118 *)
transitivity (Pr PRQ [set x] / Pr Q [set x.2]).
  rewrite /jcPr setX1 {2}/PRQ fdistAC2 -/Q; by case: x H0.
transitivity (Pr PQ [set (x.1.1,x.2)] * \Pr_RQ[[set x.1.2]|[set x.2]] / Pr Q [set x.2]).
  congr (_ / _).
  case: x H0 => [[a c] b] H0 /=.
  rewrite /PRQ [LHS]Pr_set1 fdistACE /= mc; congr (_ * _).
  rewrite /jcPr {2}/QP fdistX2 -/P Pr_set1 mulrCA mulfV ?mulr1; last first.
    apply dom_by_fdist_fstN with b.
    apply dom_by_fdist_fstN with c.
    by rewrite fdistACE in H0.
  by rewrite /QP Pr_fdistX setX1.
rewrite -mulrA mulrCA mulrC; congr (_ * _).
  rewrite /jcPr fdist_proj13_snd -/Q {2}/PRQ fdistAC2 -/Q; congr (_ / _).
  by rewrite /PRQ /PQ setX1 fdist_proj13_AC.
rewrite /jcPr fdist_proj23_snd; congr (_ / _).
- by rewrite /RQ /PRQ /fdist_proj23 fdistA_AC_snd.
- by rewrite /RQ fdistX2 fdistA21 /PRQ fdistAC2.
Qed.

Let PR := fdist_proj13 PQR.

(** thm 2.8.1: *)
Lemma data_processing_inequality : markov_chain ->
  mutual_info PR <= mutual_info PQ.
Proof.
move=> H.
have H1 : mutual_info (fdistA PQR) = mutual_info PR + cond_mutual_info PQR.
  rewrite /cond_mutual_info !mutual_infoE addrA; congr (_ - _).
  by rewrite -/PR subrK /PR fdist_proj13_fst.
have H2 : mutual_info (fdistA PQR) = mutual_info PQ + cond_mutual_info PRQ.
  transitivity (mutual_info (fdistA PRQ)).
    by rewrite !mutual_infoE fdistA_AC_fst centropy_fdistA.
  rewrite /cond_mutual_info !mutual_infoE addrA; congr (_ - _).
  by rewrite fdistA1 {1}/PRQ fdist_proj13_AC -/PQ subrK /PQ fdistAC_fst_fst.
have H3 : cond_mutual_info PRQ = 0 by rewrite markov_cond_mutual_info.
have H4 : 0 <= cond_mutual_info PQR by exact: cond_mutual_info_ge0.
move: H2; rewrite {}H3 addr0 => <-.
by rewrite {}H1 addrC -lerBlDr subrr.
Qed.

End markov_chain.

Section markov_chain_prop.
Variables (R : realType) (A B C : finType) (PQR : R.-fdist (A * B * C)).

Lemma markov_chain_order : markov_chain PQR -> markov_chain (fdistC13 PQR).
Proof.
rewrite /markov_chain => H c b a.
rewrite fdistC13E /=.
rewrite {}H.
rewrite fdistC13_fst_fst.
rewrite (jBayes _ [set a] [set b]).
rewrite fdistXI.
rewrite fdistX1 fdistX2.
rewrite (mulrC (_ a)) -[LHS]mulrA.
rewrite [in RHS]mulrCA -[in RHS]mulrA.
congr (_ * _).
  by rewrite fdistA_C13_snd.
rewrite (jBayes _ [set c] [set b]).
rewrite fdistXI.
rewrite [in LHS]mulrCA -[in LHS]mulrA.
rewrite [in RHS](mulrCA (_ c)).
rewrite -[in RHS]mulrA [in RHS]mulrCA.
congr (_ * _).
  congr (\Pr_ _ [_ | _]).
  by rewrite fdistC13_fst fdistXI.
rewrite !Pr_set1.
rewrite [in LHS]mulrCA.
rewrite [in RHS]mulrCA.
congr (_ * _).
  congr (_ a).
  by rewrite fdistA22 fdistC13_snd.
congr (_ / _).
  by rewrite fdistX1 fdistA22.
congr (_ a).
by rewrite fdistX2 fdistA21 fdistA_C13_snd fdistX1.
Qed.

End markov_chain_prop.

Section Han_inequality.

Local Open Scope ring_scope.

Lemma information_cant_hurt_cond (R : realType) (A : finType) (n' : nat) (n := n'.+1 : nat)
  (P : R.-fdist 'rV[A]_n) (i : 'I_n) (i0 : i != O :> nat) :
  centropy (fdist_prod_of_rV P) <=
  centropy (fdist_prod_of_rV (fdist_take P (lift ord0 i))).
Proof.
rewrite -subr_ge0.
set Q : R.-fdist (A * 'rV[A]_i * 'rV[A]_(n' - i)) := fdist_take_drop P i.
have H1 : fdist_proj13 (fdistAC Q) = fdist_prod_of_rV (fdist_take P (lift ord0 i)).
  rewrite /fdist_proj13 /fdistAC /fdist_prod_of_rV /fdist_take /fdist_snd /fdistA.
  rewrite /fdistC12 /fdistX /fdist_take_drop !fdistmap_comp; congr (fdistmap _ P).
  rewrite boolp.funeqE => /= v /=.
  congr (_, _).
  - rewrite mxE castmxE /= cast_ord_id; congr (v ord0 _); exact: val_inj.
  - apply/rowP => j.
    rewrite !mxE !castmxE /= !cast_ord_id !esymK mxE; congr (v ord0 _).
    exact: val_inj.
have H2 : centropy (fdistA (fdistAC Q)) = centropy (fdist_prod_of_rV P).
  rewrite -centropy_fdistA /centropy /=.
  rewrite (partition_big (@row_take A _ i) xpredT) //=.
  rewrite (eq_bigr (fun a => (fdistA Q)`2 (a.1, a.2) *
           centropy1 (fdistA Q) (a.1, a.2))%R); last by case.
  rewrite -(pair_bigA _ (fun a1 a2 => (fdistA Q)`2 (a1, a2) *
           centropy1 (fdistA Q) (a1, a2))%R) /=.
  apply eq_bigr => v _.
(* TODO: lemma *)
  rewrite (@reindex_onto _ _ _ 'rV[A]_n' 'rV[A]_(n' - i)
    (fun w => (castmx (erefl 1%nat, subnKC (ltnS' (ltn_ord i))) (row_mx v w)))
    (@row_drop A _ i)) /=; last first.
    move=> w wv; apply/rowP => j.
    rewrite castmxE /= cast_ord_id /row_drop mxE; case: splitP => [j0 /= jj0|k /= jik].
    - rewrite -(eqP wv) mxE castmxE /= cast_ord_id; congr (w _ _); exact: val_inj.
    - rewrite mxE /= castmxE /= cast_ord_id; congr (w _ _); exact: val_inj.
  apply eq_big => /= w.
    apply/esym/andP; split; apply/eqP/rowP => j.
    by rewrite !mxE !castmxE /= !cast_ord_id esymK cast_ordK row_mxEl.
    by rewrite !mxE !castmxE /= cast_ord_id esymK cast_ordK cast_ord_id row_mxEr.
  move=> _; congr (_ * _)%R.
  - rewrite !fdist_sndE; apply eq_bigr => a _.
    by rewrite fdistAE /= fdist_prod_of_rVE /= /Q fdist_take_dropE.
  - rewrite /centropy1; congr (- _)%R; apply eq_bigr => a _.
    congr (_ * log _)%R.
    + rewrite /jcPr !(Pr_set1,setX1) fdistAE /= /Q fdist_take_dropE /= fdist_prod_of_rVE /=.
      congr (_ / _)%R.
      rewrite !fdist_sndE; apply eq_bigr => a0 _.
      by rewrite fdistAE fdist_take_dropE fdist_prod_of_rVE.
    + rewrite /jcPr !(Pr_set1,setX1) fdistAE /= /Q fdist_take_dropE /= fdist_prod_of_rVE /=.
      congr (_ / _)%R.
      rewrite !fdist_sndE; apply eq_bigr => a0 _.
      by rewrite fdistAE fdist_take_dropE fdist_prod_of_rVE.
rewrite (_ : _ - _ = cond_mutual_info (fdistAC Q))%R; last by rewrite /cond_mutual_info H1 H2.
exact/cond_mutual_info_ge0.
Qed.

Lemma han_helper (R : realType) (A : finType) (n' : nat) (n := n'.+1 : nat)
  (P : R.-fdist 'rV[A]_n) (i : 'I_n) (i0 : i != O :> nat) :
  centropy (fdist_prod_of_rV (fdist_perm P (put_front_perm i))) <=
  centropy (fdistX (fdist_belast_last_of_rV (fdist_take P (lift ord0 i)))).
Proof.
rewrite (_ : fdistX _ = fdist_prod_of_rV (fdist_perm
    (fdist_take P (lift ord0 i)) (put_front_perm (inord i)))); last first.
  apply/fdist_ext => /= -[a v].
  rewrite fdistXE fdist_belast_last_of_rVE fdist_prod_of_rVE /= fdist_permE.
  rewrite !(fdist_takeE _ (lift ord0 i)); apply eq_bigr => /= w _; congr (P _); apply/rowP => k.
  rewrite !castmxE /= cast_ord_id.
  have [ki|ki] := ltnP k i.+1.
    have @k1 : 'I_i.+1 := Ordinal ki.
    rewrite (_ : cast_ord _ k = lshift (n - bump 0 i) k1); last exact/val_inj.
    rewrite 2!row_mxEl castmxE /= cast_ord_id [in RHS]mxE.
    have [ki'|] := ltnP k i.
      rewrite (_ : cast_ord _ _ = lshift 1%nat (Ordinal ki')) /=; last exact/val_inj.
      rewrite row_mxEl /put_front_perm permE /put_front ifF; last first.
        apply/negbTE/eqP => /(congr1 val) /=.
        by rewrite inordK // => /eqP; rewrite ltn_eqF.
      rewrite inordK //= ki' (_ : inord k.+1 = rshift 1%nat (Ordinal ki')); last first.
        by apply/val_inj => /=; rewrite inordK.
      by rewrite (@row_mxEr _ 1%nat 1%nat).
    rewrite permE /put_front leq_eqVlt => /orP[|] ik.
      rewrite ifT; last first.
        apply/eqP/val_inj => /=; rewrite inordK //; exact/esym/eqP.
      rewrite row_mx_row_ord0 (_ : cast_ord _ _ = rshift i ord0); last first.
        by apply val_inj => /=; rewrite addn0; apply/esym/eqP.
      by rewrite row_mxEr mxE.
    by move: (leq_ltn_trans ik ki); rewrite ltnn.
  move=> [:Hk1].
  have @k1 : 'I_(n - bump 0 i).
    apply: (@Ordinal _ (k - i.+1)).
    abstract: Hk1.
    by rewrite /bump leq0n add1n ltn_sub2r // (leq_ltn_trans _ (ltn_ord k)).
  rewrite (_ : cast_ord _ _ = rshift i.+1 k1); last by apply val_inj => /=; rewrite subnKC.
  by rewrite 2!row_mxEr.
rewrite (_ : fdist_perm (fdist_take _ _) _ =
  fdist_take (fdist_perm P (put_front_perm i)) (lift ord0 i)); last first.
  apply/fdist_ext => /= w.
  rewrite fdist_permE 2!(fdist_takeE _ (lift ord0 i)); apply eq_bigr => /= v _.
  rewrite fdist_permE; congr (P _); apply/rowP => /= k.
  rewrite /col_perm mxE !castmxE /= !cast_ord_id /=.
  have [ki|ki] := ltnP k (bump 0 i).
    rewrite (_ : cast_ord _ _ = lshift (n - bump 0 i) (Ordinal ki)); last exact/val_inj.
    rewrite row_mxEl mxE /put_front_perm !permE /= /put_front /=.
    have [ik|ik] := eqVneq k i.
      rewrite ifT; last first.
        by apply/eqP/val_inj => //=; rewrite ik inordK.
      rewrite (_ : cast_ord _ _ = lshift (n - bump 0 i) ord0); last exact/val_inj.
      by rewrite row_mxEl.
    rewrite ifF; last first.
      apply/negbTE/eqP => /(congr1 val) /=.
      by apply/eqP;rewrite inordK.
    have [{}ik|{}ik] := ltnP k i.
      rewrite inordK // ik.
      move=> [:Hk1].
      have @k1 : 'I_(bump 0 i).
        apply: (@Ordinal _ k.+1).
        abstract: Hk1.
        by rewrite /bump leq0n add1n.
      rewrite (_ : cast_ord _ _ = lshift (n - bump 0 i) k1); last first.
        apply/val_inj => /=; rewrite inordK // ltnS.
        by rewrite (leq_trans ik) // -ltnS.
      rewrite row_mxEl; congr (w _ _).
      by apply val_inj => /=; rewrite inordK.
    rewrite ifF; last first.
      apply/negbTE.
      by rewrite -leqNgt -ltnS inordK.
    rewrite (_ : cast_ord _ _ = lshift (n - bump 0 i) (Ordinal ki)); last exact/val_inj.
    by rewrite row_mxEl.
  rewrite /bump leq0n add1n in ki.
  move=> [:Hk1].
  have @k1 : 'I_(n - bump 0 i).
    apply: (@Ordinal _ (k - i.+1)).
    abstract: Hk1.
    by rewrite /bump leq0n add1n ltn_sub2r // (leq_trans _ (ltn_ord k)).
  rewrite (_ : cast_ord _ _ = rshift i.+1 k1); last by apply/val_inj => /=; rewrite subnKC.
  rewrite row_mxEr permE /put_front /= ifF; last first.
     by move: ki; rewrite ltnNge; apply: contraNF => /eqP ->.
  rewrite ltnNge (ltnW ki) /=.
  move=> [:Hk2].
  have @k2 : 'I_(n - bump 0 i).
    apply: (@Ordinal _ (k - i.+1)).
    abstract: Hk2.
    by rewrite /bump leq0n add1n ltn_sub2r // (leq_trans _ (ltn_ord k)).
  rewrite (_ : cast_ord _ _ = rshift (bump 0 i) k2); last first.
    by apply/val_inj => /=; rewrite /bump leq0n add1n subnKC.
  rewrite row_mxEr; congr (v _ _); exact/val_inj.
exact/information_cant_hurt_cond.
Qed.

Variables (R : realType) (A : finType) (n' : nat).
Let n := n'.+1.
Variable P : R.-fdist 'rV[A]_n.

(** Han's inequality: *)
Lemma han : n.-1%:R * `H P <= \sum_(i < n) `H (fdist_col' P i).
Proof.
rewrite -subn1 natrB // mulrBl mul1r.
rewrite lerBlDr {2}(chain_rule_rV P).
rewrite -big_split /= -{1}(card_ord n) -sum1_card.
rewrite natr_sum big_distrl /=.
apply ler_sum => i _; rewrite mul1r.
case: ifPn => [/eqP|] i0.
  rewrite (_ : i = ord0); last exact/val_inj.
  rewrite -tail_of_fdist_rV_fdist_col' /tail_of_fdist_rV /head_of_fdist_rV.
  rewrite -{1}(fdist_rV_of_prodK P) entropy_fdist_rV_of_prod.
  move: (chain_rule (fdist_prod_of_rV P)); rewrite /joint_entropy => ->.
  by rewrite [in X in (_ <= X)%R]addrC lerD2l -fdistX1; exact: information_cant_hurt.
rewrite (chain_rule_multivar _ i0) lerD2l.
exact/han_helper.
Qed.

End Han_inequality.
