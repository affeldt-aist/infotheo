(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice fintype.
From mathcomp Require Import finfun bigop prime binomial ssralg.
Require Import Reals ssrR.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Delimit Scope R_scope with CR.

Definition Req_bool (a b : R) : bool :=
  match Req_EM_T a b with left _ => true | _ => false end.

Lemma eqRP : Equality.axiom Req_bool.
Proof.
move=> a b. apply: (iffP idP); rewrite /Req_bool; by case: (Req_EM_T a b).
Qed.

Canonical R_eqMixin := EqMixin eqRP.
Canonical R_eqType := EqType R R_eqMixin.

Axiom R_choiceMixin : Choice.mixin_of R.
Canonical R_choice := ChoiceType R R_choiceMixin.

Definition R_zmodMixin := ZmodMixin addRA addRC add0R Rplus_opp_l.
Canonical R_zmodType := ZmodType R R_zmodMixin.

Search (R1 <> R0).

Lemma R1dR0 : R1 != R0. Proof. apply/eqP; exact R1_neq_R0. Qed.

Definition R_ringMixin := RingMixin mulRA mul1R mulR1 mulRDl mulRDr R1dR0.
Canonical R_ringType := RingType R R_ringMixin.

Canonical R_comRingType := ComRingType R mulRC.

Lemma Rinv_r' : forall x : R, x != 0 -> Rinv x * x = 1.
Proof. by move=> x /eqP /Rinv_l_sym H; rewrite -[_ * _]H. Qed.

Axiom Rinv_R0 : (/ 0 = 0)%CR.

Definition R_unitRingMixin := FieldUnitMixin Rinv_r' Rinv_R0.
Canonical R_unitRingType := UnitRingType R R_unitRingMixin.

Canonical R_comUnitRingType := Eval hnf in [comUnitRingType of R].

Definition R_FieldMixin := @FieldMixin _ _ Rinv_r' Rinv_R0.
Definition R_IntegralMixin := FieldIdomainMixin R_FieldMixin.
Canonical R_idomainType := IdomainType R R_IntegralMixin.
Canonical R_fieldType := FieldType R R_FieldMixin.

From mathcomp Require Import ssrnum.

(*RealLeMixin
     : forall (R : idomainType) (le lt : rel R) (norm : R -> R),
       (forall x y : R, le 0 x -> le 0 y -> le 0 (x + y)) ->
       (forall x y : R, le 0 x -> le 0 y -> le 0 (x * y)) ->
       (forall x : R, le 0 x -> le x 0 -> x = 0) ->
       (forall x y : R, le 0 (y - x) = le x y) ->
       (forall x : R, le 0 x || le x 0) ->
       (forall x : R, norm (- x) = norm x) ->
       (forall x : R, le 0 x -> norm x = x) ->
       (forall x y : R, lt x y = (y != x) && le x y) -> Num.mixin_of R*)

Delimit Scope Rb_scope with Rb.
Lemma addR_ge0 : (forall x y : R, 0 <b= x -> 0 <b= y -> 0 <b= x + y)%Rb.
Proof.
move=> x y /RleP Hx /RleP Hy. apply/RleP. by apply ssrR.addR_ge0.
Qed.

Lemma mulR_ge0 : (forall x y : R, 0 <b= x -> 0 <b= y -> 0 <b= x * y)%Rb.
Proof.
move=> x y /RleP Hx /RleP Hy. apply/RleP. by apply ssrR.mulR_ge0.
Qed.

Lemma le_ge_0 : (forall x : R, 0 <b= x -> x <b= 0 -> x = 0)%Rb.
Proof. move=> x /RleP Hx /RleP Hy. by apply Rle_antisym. Qed.

Require Import Fourier.

Lemma subR_le0 : (forall x y : R, 0 <b= (y - x) = (x <b= y))%Rb.
Proof.
move=> x y.
move Hlhs : (0 <b= y - x)%Rb => [|].
  move/RleP in Hlhs.
  symmetry.
  apply/RleP.
  by fourier.
symmetry.
apply/RleP.
move/RleP in Hlhs.
contradict Hlhs.
by fourier.
Qed.

Lemma or_le0 : forall x : R, (0 <b= x)%Rb || (x <b= 0)%Rb.
Proof.
move=> x; apply/orP.
case: (Rle_or_lt 0 x).
left; by apply/RleP.
right; apply/RleP.
by apply Rlt_le.
Qed.

Lemma Rabs_le0 : (forall x : R, (0 <b= x)%Rb -> Rabs x = x).
Proof. move=> x /RleP. by apply Rabs_pos_eq. Qed.

Lemma Rltn_neqAle_new : forall m n : R, (m <b n)%Rb = (n != m) && (m <b= n)%Rb.
Proof. move=> x y. by rewrite Rlt_neqAle eq_sym. Qed.

Definition R_RealLeMixin := RealLeMixin addR_ge0 mulR_ge0 le_ge_0 subR_le0 or_le0 Rabs_Ropp Rabs_le0 Rltn_neqAle_new.

Canonical R_numDomainType := NumDomainType R R_RealLeMixin.
Canonical R_numFieldType := [numFieldType of R].
Canonical R_realDomainType := RealDomainType R or_le0.
Canonical R_realFieldType := [realFieldType of R].

(* TODO: archimedian also corresponds to a stucture *)
