(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg fingroup perm finalg matrix.
From mathcomp Require Import all_algebra vector reals normedtype.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
Require Import ssrR logb ssr_ext ssralg_ext bigop_ext Rbigop.
Import Order.POrderTheory Order.TotalTheory GRing.Theory Num.Theory.

Reserved Notation "p '.~'" (format "p .~", at level 5).
Reserved Notation "x %:pr" (at level 0, format "x %:pr").
Reserved Notation "x %:opr" (at level 0, format "x %:opr").
Reserved Notation "x %:pos" (at level 2, format "x %:pos").
Reserved Notation "x %:nng" (at level 2, format "x %:nng").
Reserved Notation "P '`<<' Q" (at level 51).

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
(* ---- onem ---- *)
Section onem.
  Local Open Scope ring_scope.
  Variable R : numDomainType.
  Definition onem (x: R) := 1 - x.

  Lemma onemK (x : R): onem (onem x) = x.
  Proof.
    by rewrite /onem opprB addrA addrC addrA (addrC (-1) 1) subrr add0r.
  Qed.

  Lemma onem_le1 x : 0 <= x -> onem x <= 1.
  Proof. move=> ?; by rewrite /onem ler_subl_addr -ler_subl_addl subrr. Qed.

  Lemma onem_ge0 x : x <= 1 -> 0 <= onem x.
  Proof. move=> ?; by rewrite /onem subr_ge0. Qed.

  Lemma onem0 : onem 0 = 1.
  Proof. by rewrite /onem subr0. Qed.

  Lemma onem1 : onem 1 = 0.
  Proof. by rewrite /onem subrr. Qed.

  Lemma onemKC r : r + (onem r) = 1.
  Proof. 
    by rewrite /onem addrC -addrA (addrC (-r) r) subrr addr0.
  Qed.

  Lemma onem_prob r : 0 <= r <= 1 -> 0 <= onem r <= 1.
  Proof.
    by move=> /andP [_0r r1]; apply /andP; split; [rewrite onem_ge0 | rewrite onem_le1].
  Qed.

  Lemma onem_eq0 r : (onem r = 0) <-> (r = 1).
  Proof.
  rewrite /onem. split; first by move /subr0_eq.
  by move=> ->; rewrite subrr.
  Qed.

  Lemma onem_neq0 r : (onem r != 0) <-> (r != 1).
  Proof. by split; apply: contra => /eqP/onem_eq0/eqP. Qed.
End onem.
Notation "p '.~'" := (onem p).
(* ---- onem ---- *)

(* ---- Prob ---- *)
Module Prob.
Record t (R : numDomainType) := mk {
  p :> R ;
  Op1 : (0 <= p <= 1)%R }.
Definition O1 (R : numDomainType) (x : t R) : (0 <= p x <= 1)%R := Op1 x.
Arguments O1 : simpl never.
Definition mk_ (R : numDomainType) (q : R) (Oq1 : (0 <= q <= 1)%R) := mk Oq1.
Module Exports.
Notation prob := t.
Notation "q %:pr" := (@mk _ q (@O1 _ _)).
Canonical prob_subType (R : numDomainType) := Eval hnf in [subType for @p R].
Definition prob_eqMixin (R : numDomainType) := [eqMixin of (prob R) by <:].
Canonical prob_eqType (R : numDomainType) := Eval hnf in EqType _ (prob_eqMixin R).
End Exports.
End Prob.
Export Prob.Exports.
Coercion Prob.p : prob >-> Num.NumDomain.sort.
Lemma probpK R p H : Prob.p (@Prob.mk R p H) = p. Proof. by []. Qed.

Section prob_lemmas.
Variable R : numDomainType.

Lemma OO1 : ((0 <= 0 :> R) && (0 <= 1 :> R))%R. Proof. by apply /andP; split. Qed.
Lemma O11 : ((0 <= 1 :> R) && (1 <= 1 :> R))%R. Proof. by apply /andP; split. Qed.

Canonical prob0 := Eval hnf in Prob.mk OO1.
Canonical prob1 := Eval hnf in Prob.mk O11.
Canonical probcplt (p : prob R) := Eval hnf in Prob.mk (onem_prob (Prob.O1 p)).

Lemma prob_ge0 (p : prob R) : (0 <= (p : R))%R.
Proof. by case: p => p /= /andP []. Qed.

Lemma prob_le1 (p : prob R) : ((p : R) <= 1)%R.
Proof. by case: p => p /= /andP []. Qed.
End prob_lemmas.
Global Hint Resolve prob_ge0 : core.
Global Hint Resolve prob_le1 : core.
Arguments prob0 {R}.
Arguments prob1 {R}.
(* ---- ---- *)
