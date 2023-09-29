(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg fingroup perm finalg matrix.
From mathcomp Require Import all_algebra vector reals normedtype.
From mathcomp Require Import boolp.
From mathcomp Require Import lra Rstruct.

Reserved Notation "p '.~'" (format "p .~", at level 5).
Reserved Notation "x %:pr" (at level 0, format "x %:pr").
Reserved Notation "x %:opr" (at level 0, format "x %:opr").
Reserved Notation "x %:pos" (at level 2, format "x %:pos").
Reserved Notation "x %:nng" (at level 2, format "x %:nng").
Reserved Notation "P '`<<' Q" (at level 51).

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import Order.POrderTheory Order.TotalTheory GRing.Theory Num.Theory.

(* ---- onem ---- *)
Section onem.
Local Open Scope ring_scope.
Variable R : realType.

Definition onem (x: R) := 1 - x.
Local Notation "p '.~'" := (onem p).

Lemma onem0 : onem 0 = 1. Proof. by rewrite /onem subr0. Qed.

Lemma onem1 : onem 1 = 0.   Proof. by rewrite /onem subrr. Qed.

Lemma onem_ge0 x : x <= 1 -> 0 <= onem x.
Proof. move=> ?; by rewrite /onem subr_ge0. Qed.

Lemma onem_le1 x : 0 <= x -> onem x <= 1.
Proof. move=> ?; by rewrite /onem ler_subl_addr -ler_subl_addl subrr. Qed.

Lemma onem_le  r s : (r <= s) = (s.~ <= r.~).
Proof.
apply/idP/idP => [|?]; first exact: ler_sub.
by rewrite -(opprK r) ler_oppl -(ler_add2l 1).
Qed.

Lemma onemE x : x.~ = 1 - x.  Proof. by []. Qed.

Lemma onem_lt  r s : r < s <-> s.~ < r.~. Proof. by rewrite !onemE; lra. Qed.

Lemma onemKC r : r + r.~ = 1. Proof. by rewrite !onemE; lra. Qed.
(*  Lemma onemKC r : r + (onem r) = 1.
  Proof. 
    by rewrite /onem addrC -addrA (addrC (-r) r) subrr addr0.
  Qed.*)

  Lemma onemK (x : R): onem (onem x) = x.
  Proof.
    by rewrite /onem opprB addrA addrC addrA (addrC (-1) 1) subrr add0r.
  Qed.

  Lemma onemD p q : (p + q).~ = p.~ + q.~ - 1.
  Proof. rewrite !onemE; lra. Qed.
  
  Lemma onemM p q : (p * q).~ = p.~ + q.~ - p.~ * q.~.
  Proof. rewrite !onemE/=; lra. Qed.

  Lemma onem_div p q : q != 0 -> (p / q).~ = (q - p)  /q.
  Proof.
    rewrite !onemE.
    move=> Hq.
    rewrite mulrDl.
    rewrite mulNr.
    rewrite -/(q / q).
    by rewrite divrr// unitfE.
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

  Lemma onem_eq1 r : r.~ = 1 <-> r = 0. Proof. rewrite onemE; lra. Qed.

  Lemma onem_neq0 r : (onem r != 0) <-> (r != 1).
  Proof. by split; apply: contra => /eqP/onem_eq0/eqP. Qed.

  Lemma onem_gt0 r : r < 1 -> 0 < r.~. Proof. rewrite /onem; lra. Qed.

  Lemma onem_lt1 r : 0 < r -> r.~ < 1. Proof. rewrite /onem; lra. Qed.

  Lemma onem_oprob r : 0 < r < 1 -> 0 < r.~ < 1.
  Proof.
    by move=> /andP [? ?]; apply/andP; rewrite onem_gt0 // onem_lt1.
  Qed.

  Lemma subr_onem r s : r - s.~ = r + s - 1.
  Proof. by rewrite /onem opprB addrA. Qed.

End onem.
Notation "p '.~'" := (onem p).
(* ---- onem ---- *)

(* ---- Prob ---- *)
Module Prob.
Record t (R : realType) := mk {
  p :> R ;
  Op1 : (0 <= p <= 1)%R }.
Definition O1 (R : realType) (x : t R) : (0 <= p x <= 1)%R := Op1 x.
Arguments O1 : simpl never.
Definition mk_ (R : realType) (q : R) (Oq1 : (0 <= q <= 1)%R) := mk Oq1.
Module Exports.
Notation prob := t.
Notation "q %:pr" := (@mk _ q (@O1 _ _)).
Canonical prob_subType (R : realType) := Eval hnf in [subType for @p R].
Definition prob_eqMixin (R : realType) := [eqMixin of (prob R) by <:].
Canonical prob_eqType (R : realType) := Eval hnf in EqType _ (prob_eqMixin R).
End Exports.
End Prob.
Export Prob.Exports.
Coercion Prob.p : prob >-> Real.sort.
Lemma probpK R p H : Prob.p (@Prob.mk R p H) = p. Proof. by []. Qed.

Reserved Notation "{ 'prob' T }" (at level 0, format "{ 'prob'  T }").
Definition prob_of (R : realType) := fun phT : phant (Num.NumDomain.sort (*Real.sort*)R) => @prob R.
Notation "{ 'prob' T }" := (@prob_of _ (Phant T)).
Definition prob_coercion (R: realType) (p : {prob R}) : R := Prob.p p.

Section prob_lemmas.
Import GRing.Theory.
Local Open Scope ring_scope.
Variable R : realType.
Implicit Types p q : {prob R}.



Lemma OO1 : ((0 <= 0 :> R) && (0 <= 1 :> R))%R.
Proof. by apply /andP; split; [rewrite lexx | rewrite ler01]. Qed.
Lemma O11 : ((0 <= 1 :> R) && (1 <= 1 :> R))%R.
Proof. by apply /andP; split; [rewrite ler01| rewrite lexx]. Qed.

Canonical prob0 := Eval hnf in Prob.mk OO1.
Canonical prob1 := Eval hnf in Prob.mk O11.
Canonical probcplt (p : prob R) := Eval hnf in Prob.mk (onem_prob (Prob.O1 p)).

Lemma prob_ge0 (p : prob R) : (0 <= (p : R))%R.
Proof. by case: p => p /= /andP []. Qed.

Lemma prob_le1 (p : prob R) : ((p : R) <= 1)%R.
Proof. by case: p => p /= /andP []. Qed.

Lemma prob_gt0 p : p != 0%:pr <-> 0 < Prob.p p.
Proof.
rewrite lt_neqAle; split=> [H|/andP[+ pge0]].
  by apply/andP; split; [rewrite eq_sym|exact: prob_ge0].
by apply: contra => /eqP ->.
Qed.

Lemma prob_gt0' p : p != 0 :> R <-> 0 < Prob.p p.
Proof. exact: prob_gt0. Qed.

Lemma prob_lt1 p : p != 1%:pr <-> Prob.p p < 1.
Proof.
rewrite lt_neqAle; split=> [H|/andP[+ pge0]].
  by apply/andP; split => //; exact: prob_le1.
by apply: contra => /eqP ->.
Qed.

Lemma prob_lt1' p : p != 1 :> R <-> Prob.p p < 1.
Proof. exact: prob_lt1. Qed.

Lemma prob_trichotomy p : p = 0%:pr \/ p = 1%:pr \/ 0 < Prob.p p < 1.
Proof.
have [/eqP ->|pneq0]:= boolP (p == 0%:pr); first by left.
right.
have [/eqP ->|pneq1] := boolP (p == 1%:pr); first by left.
by right; apply/andP; split; [exact/prob_gt0|exact/prob_lt1].
Qed.

Lemma probK p : p = (onem p).~%:pr.
Proof. by apply val_inj => /=; rewrite onemK. Qed.

Lemma probKC (p : {prob R}) : Prob.p p + p.~ = 1 :> R.
Proof. exact: onemKC. Qed.

Lemma probadd_eq0 p q : Prob.p p + Prob.p q = 0 <-> p = 0%:pr /\ q = 0%:pr.
Proof.
split; last by move=> [-> ->] /=; rewrite addr0.
move/eqP; rewrite paddr_eq0; [|exact: prob_ge0|exact: prob_ge0].
by move=> /andP[/eqP ? /eqP ?]; split; exact/val_inj.
Qed.

Lemma probadd_neq0 p q : Prob.p p + Prob.p q != 0 <-> p != 0%:pr \/ q != 0%:pr.
Proof.
(*split => [/paddR_neq0| ]; first by move=> /(_ _ _); apply.
by case; apply: contra => /eqP/probadd_eq0 [] /eqP ? /eqP.
Qed.*)
Admitted.

Lemma probmul_eq1 p q : Prob.p p * Prob.p q = 1 <-> p = 1%:pr /\ q = 1%:pr.
Proof.
split => [/= pq1|[-> ->]]; last by rewrite mulr1.
(*move: (oner_neq0 R); rewrite -{1}pq1 => /eqP; rewrite mulR_neq0' => /andP[].
move: R1_neq_R0; rewrite -{1}pq1 => /eqP; rewrite mulR_neq0' => /andP[].
rewrite 2!prob_gt0'=> p0 q0.
have /leR_eqVlt[p1|] := probR_le1 p; last first.
  by move/(ltR_pmul2r q0); rewrite mul1R => /(ltR_leR_trans);
     move/(_ _ (probR_le1 q))/ltR_neqAle => [].
have /leR_eqVlt[q1|] := probR_le1 q; last first.
  by move/(ltR_pmul2r p0); rewrite mul1R mulRC => /(ltR_leR_trans);
  move/(_ _ (probR_le1 p)) /ltR_neqAle => [].
by split; apply val_inj.
Qed.*)
Admitted.

End prob_lemmas.


Global Hint Resolve prob_ge0 : core.
Global Hint Resolve prob_le1 : core.

#[export] Hint Extern 0 (is_true (Prob.p _ <= 1)%R) =>
  exact/prob_le1 : core.
#[export] Hint Extern 0 (is_true (0 <= Prob.p _)%R) =>
  exact/prob_ge0 : core.

Arguments prob0 {R}.
Arguments prob1 {R}.
(* ---- ---- *)

Module OProb.
Section def.
Import GRing.Theory.
Local Open Scope ring_scope.
Record t (R: realType):= mk {
  p :> {prob R};
  Op1 : (0 < Prob.p p < 1)%R }.
Definition O1 (R: realType) (x : t R) : 0 < Prob.p (p x) < 1 := Op1 x.
Arguments O1 : simpl never.
End def.
Module Exports.
Notation oprob := t.
Notation "q %:opr" := (@mk _ q%:pr (@O1 _ _)).
Canonical oprob_subType (R: realType) := Eval hnf in [subType for @p R].
Definition oprob_eqMixin (R: realType) := [eqMixin of (oprob R) by <:].
Canonical oprob_eqType (R : realType) := Eval hnf in EqType _ (oprob_eqMixin R).
End Exports.
End OProb.
Export OProb.Exports.
(*Coercion OProb.p : oprob >-> prob.*)
Canonical oprobcplt [R: realType] (p : oprob R) := Eval hnf in OProb.mk (onem_oprob (OProb.O1 p)).


Reserved Notation "{ 'oprob' T }" (at level 0, format "{ 'oprob'  T }").
Definition oprob_of (R : realType) := fun phT : phant (Num.NumDomain.sort R) => @oprob R.
Notation "{ 'oprob' T }" := (@oprob_of _ (Phant T)).
Definition oprob_coercion (R: realType) (p : {oprob R}) : R := OProb.p p.
Notation oprob_to_real o := (Prob.p (OProb.p o)).
(*(R: realType) (o : {oprob R}) := Prob.p (OProb.p o).*)

Section oprob_lemmas.
Import GRing.Theory.
Local Open Scope ring_scope.
Variable R : realType.
Implicit Types p q : {oprob R}.

Lemma oprob_gt0 p : 0 < oprob_to_real p.
Proof. by case : p => p /= /andP []. Qed.

Lemma oprob_lt1 p : oprob_to_real p < 1.
Proof. by case: p => p /= /andP [] _. Qed.

(*Lemma oprob_ge0 p : 0 <= oprob_to_real p. Proof. exact/ltRW/oprob_gt0. Qed.

Lemma oprob_le1 p : p <= 1. Proof. exact/ltRW/oprob_lt1. Qed.*)

Import Order.POrderTheory Order.TotalTheory.

Lemma oprob_neq0 p : oprob_to_real p != 0 :> R.
Proof. by move:(oprob_gt0 p); rewrite lt_neqAle=> /andP -[] /eqP/nesym/eqP. Qed.

(*Lemma oprob_neq1 p : p != 1 :> R.
Proof. by move:(oprob_lt1 p); rewrite ltR_neqAle=> -[] /eqP. Qed.

Lemma oprobK p : p = (p.~).~%:opr.
Proof. by apply/val_inj/val_inj=> /=; rewrite onemK. Qed.*)


Lemma prob_trichotomy' (p : {prob R}) (P : {prob R} -> Prop) :
  P prob0 -> P prob1 -> (forall o : {oprob R}, P (OProb.p o)) -> P p.
Proof.
move=> p0 p1 po.
have [-> //|[->//|p01]] := prob_trichotomy p.
apply (po (@OProb.mk _ _ p01)).
Qed.
(*Lemma oprobadd_gt0 p q : 0 < p + q.
Proof. exact/addR_gt0/oprob_gt0/oprob_gt0. Qed.

Lemma oprobadd_neq0 p q : p + q != 0%R.
Proof. by move: (oprobadd_gt0 p q); rewrite ltR_neqAle => -[] /nesym /eqP. Qed.
Qed.*)

End oprob_lemmas.

