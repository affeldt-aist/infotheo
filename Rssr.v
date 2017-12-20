(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import Reals.

Local Open Scope R_scope.

(** * SSReflect-like lemmas for Coq Reals *)

(** eqType for Coq Reals *)
Definition Req_bool (a b : R) : bool :=
  match Req_EM_T a b with left _ => true | _ => false end.

Lemma eqRP : Equality.axiom Req_bool.
Proof.
move=> a b.
apply: (iffP idP); rewrite /Req_bool; by case: (Req_EM_T a b).
Qed.

Canonical R_eqMixin := EqMixin eqRP.
Canonical R_eqType := Eval hnf in EqType R R_eqMixin.

Definition Rge_bool (a b : R) : bool :=
  match Rge_dec a b with left _ => true | _ => false end.

Definition Rle_bool a b := Rge_bool b a.

Definition Rlt_bool (a b : R) : bool :=
  match Rlt_dec a b with left _ => true | _ => false end.

Definition Rgt_bool a b := Rlt_bool b a.

Notation "a '>b=' b" := (Rge_bool a b) (at level 70) : Rb_scope.
Notation "a '<b=' b" := (Rle_bool a b) (at level 70) : Rb_scope.
Notation "a '<b=' b '<b=' c" := (Rle_bool a b && Rle_bool b c) (at level 70, b at next level) : Rb_scope.
Notation "a '<b' b" := (Rlt_bool a b) (at level 70) : Rb_scope.
Notation "a '<b' b '<b' c" := (Rlt_bool a b && Rlt_bool b c) (at level 70, b at next level) : Rb_scope.
Notation "a '>b' b" := (Rgt_bool a b) (at level 70) : Rb_scope.

Local Open Scope Rb_scope.

Lemma RgeP (a b : R) : reflect (a >= b) (a >b= b).
Proof.
move H : (a >b= b) => [|].
  constructor.
  rewrite /Rge_bool in H.
  by case: Rge_dec H.
constructor.
move/negP in H.
contradict H.
rewrite /Rge_bool.
by case: Rge_dec.
Qed.

Lemma RleP (a b : R) : reflect (a <= b) (a <b= b).
Proof.
move H : (a <b= b) => [|].
  constructor.
  rewrite /Rle_bool /Rge_bool in H.
  case: Rge_dec H => //.
  by move/Rge_le.
constructor.
move/negP in H.
contradict H.
rewrite /Rle_bool /Rge_bool.
case: Rge_dec => //.
rewrite /Rle in H.
rewrite /Rge /Rgt.
by intuition.
Qed.

Lemma RltP (a b : R) : reflect (a < b) (a <b b).
Proof.
move H : (a <b b) => [|].
  constructor.
  rewrite /Rlt_bool in H.
  by case: Rlt_dec H.
constructor.
move/negP in H.
contradict H.
rewrite /Rlt_bool.
by case: Rlt_dec.
Qed.

Definition add0R : left_id 0 Rplus := Rplus_0_l.
Definition addR0 : right_id 0 Rplus := Rplus_0_r.

Lemma addRC : commutative Rplus.
Proof. move=> m n; by rewrite Rplus_comm. Qed.

Lemma addRA : associative Rplus.
Proof. move=> m n p; by rewrite Rplus_assoc. Qed.

Definition subR0 : right_id 0 Rminus := Rminus_0_r.

Definition mul0R : left_zero 0 Rmult := Rmult_0_l.
Definition mulR0 : right_zero 0 Rmult := Rmult_0_r.
Definition mul1R : ssrfun.left_id 1%R Rmult := Rmult_1_l.
Definition mulR1 : ssrfun.right_id 1%R Rmult := Rmult_1_r.

Definition mulRC : commutative Rmult := Rmult_comm.

Lemma mulRDl : left_distributive Rmult Rplus.
Proof. move=> *; by rewrite Rmult_plus_distr_r. Qed.
Lemma mulRDr : right_distributive Rmult Rplus.
Proof. move=> *; by rewrite Rmult_plus_distr_l. Qed.

Lemma mulRA : associative Rmult.
Proof. move=> m n p; by rewrite Rmult_assoc. Qed.

Lemma leRR r : r <b= r.
Proof. apply/RleP. by apply Rle_refl. Qed.

(* Rnot_lt_le
     : forall r1 r2 : R, ~ r1 < r2 -> r2 <= r1 *)
(* Rlt_not_le
     : forall r1 r2 : R, r2 < r1 -> ~ r1 <= r2 *)
Lemma RleNgt m n : (m <b= n) = ~~ (n <b m).
Proof.
move H : (_ <b _) => [|].
  rewrite /=.
  apply/RleP.
  apply Rlt_not_le.
  by apply/RltP.
rewrite /=.
apply/RleP.
apply Rnot_lt_le.
apply/RltP.
by apply/negbT.
Qed.

Lemma RltNge m n : (m <b n) = ~~ (n <b= m).
Proof.
move H : (_ <b _) => [|].
  by apply/esym/RleP/Rlt_not_le/RltP.
by apply/esym/RleP/Rnot_lt_le/RltP/negbT.
Qed.

Lemma ltRR n : n <b n = false.
Proof.
apply/RltP.
by apply Rlt_irrefl.
Qed.

(* Rplus_le_compat. *)
Lemma Rle_add m1 m2 n1 n2 : m1 <b= n1 -> m2 <b= n2 -> m1 + m2 <b= n1 + n2.
Proof.
move=> H1 H2.
apply/RleP.
apply Rplus_le_compat; by apply/RleP.
Qed.

Lemma Rle_eqVlt m n : (m <b= n) = (m == n) || (m <b n).
Proof.
move Hlhs : (_ <b= _) => [].
  symmetry.
  move/RleP in Hlhs.
  case/Rle_lt_or_eq_dec : Hlhs => Hlhs.
    by apply/orP; right; apply/RltP.
  by rewrite Hlhs eqxx.
symmetry.
apply/negbTE.
rewrite negb_or.
apply/andP; split.
  apply/eqP => ?; subst m.
  by rewrite leRR in Hlhs.
rewrite -RleNgt.
move/negbT in Hlhs.
rewrite -RltNge in Hlhs.
apply/RleP.
apply Rlt_le.
by apply/RltP.
Qed.

Lemma Rlt_neqAle m n : (m <b n) = (m != n) && (m <b= n).
Proof. by rewrite RltNge Rle_eqVlt negb_or -RleNgt eq_sym. Qed.

Definition RltW m n : m < n -> m <= n := Rlt_le m n.

Lemma subRKC m n : m + (n - m) = n. Proof. ring. Qed.

(* Rplus_le_compat_r
     : forall r r1 r2 : R, r1 <= r2 -> r1 + r <= r2 + r*)

Lemma Rle_add2r p m n : (m + p <b= n + p) = (m <b= n).
Proof.
move Hlhs : (_ + _ <b= _) => [].
  symmetry.
  apply/RleP.
  apply Rplus_le_reg_r with p.
  by apply/RleP.
symmetry.
apply/negP.
move/negP in Hlhs.
contradict Hlhs.
apply/RleP.
apply Rplus_le_compat_r.
by apply/RleP.
Qed.

Lemma Rlt_add2r (p m n : R) : (m + p <b n + p) = (m <b n).
Proof.
move Hlhs : (_ + _ <b _) => [].
  symmetry.
  apply/RltP.
  apply Rplus_lt_reg_r with p.
  by apply/RltP.
symmetry.
apply/negP.
move/negP in Hlhs.
contradict Hlhs.
apply/RltP.
apply Rplus_lt_compat_r.
by apply/RltP.
Qed.

(* Rmult_le_compat_l
     : forall r r1 r2 : R, 0 <= r -> r1 <= r2 -> r * r1 <= r * r2 *)
(* Rmult_le_reg_l
     : forall r r1 r2 : R, 0 < r -> r * r1 <= r * r2 -> r1 <= r2 *)
Lemma Rle_pmul2l m n1 n2 : 0 <b m -> (m * n1 <b= m * n2)%R = (n1 <b= n2)%R.
Proof.
move=> Hm.
move Hlhs : (_ <b= _) => [].
  move/RleP : Hlhs.
  move/Rmult_le_reg_l.
  move/RltP in Hm.
  move/(_ Hm).
  by move/RleP.
symmetry.
apply/negP.
move/negP in Hlhs.
contradict Hlhs.
apply/RleP.
apply Rmult_le_compat_l.
  left.
  by apply/RltP.
by apply/RleP.
Qed.

(* Rmult_le_compat_r
     : forall r r1 r2 : R, 0 <= r -> r1 <= r2 -> r1 * r <= r2 * r *)
(* Rmult_le_reg_r
     : forall r r1 r2 : R, 0 < r -> r1 * r <= r2 * r -> r1 <= r2 *)

Lemma Rle_pmul2r m n1 n2 : 0 <b m -> (n1 * m <b= n2 * m) = (n1 <b= n2).
Proof.
move=> Hm.
move Hlhs : (_ <b= _) => [].
  move/RleP : Hlhs.
  move/Rmult_le_reg_r.
  move/RltP in Hm.
  move/(_ Hm).
  by move/RleP.
symmetry.
apply/negP.
move/negP in Hlhs.
contradict Hlhs.
apply/RleP.
apply Rmult_le_compat_r.
  left.
  by apply/RltP.
by apply/RleP.
Qed.

(*
Ropp_mult_distr_r_reverse

Ropp_mult_distr_l_reverse

Rinv_l_sym*)
