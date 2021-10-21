(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect.
Require Import Reals.
From mathcomp Require Import Rstruct.

(******************************************************************************)
(*                 SSReflect-like lemmas for Coq Reals                        *)
(*                                                                            *)
(* Various lemmas that make it a bit more comfortable to use the Reals of     *)
(* the Coq standard library with SSReflect.                                   *)
(*                                                                            *)
(* Basic ideas:                                                               *)
(* - Mostly renaming of lemmas for the standard library to mimick ssrnat,     *)
(*   ssrnum, etc.                                                             *)
(* - No ssralg instantiation so that the field and lra tactics remain         *)
(*   available.                                                               *)
(* - Use Prop instead of bool: = becomes <-> but rewrite is still             *)
(*   possible thanks to setoids and the view mechanism allows for apply/,     *)
(*   exact/, etc.                                                             *)
(* - Most lemmas come with a boolean counterpart (same name, ending with      *)
(*   "'"):                                                                    *)
(*   + Lemma ltR_neqAle' m n : (m <b n) = (m != n) && (m <b= n).              *)
(*     Lemma ltR_neqAle m n : (m < n) <-> (m <> n) /\ (m <= n).               *)
(*                                                                            *)
(* Details:                                                                   *)
(* - boolean relations:                                                       *)
(*   + they do not compute but can be used to write boolean predicates        *)
(*   + boolean equality for Reals as an eqtype                                *)
(*   + boolean inequalities:                                                  *)
(*     * notations: <b=, etc.                                                 *)
(*     * reflect predicates: leRP, etc.                                       *)
(* - ssrnat/ssrnum-like notations:                                            *)
(*   + %:R instead of INR                                                     *)
(* - ssrnat/ssrnum-like lemmas:                                               *)
(*   + mere renamings:                                                        *)
(*     * mulRA instead of Rmult_assoc                                         *)
(*     * subR0 instead of Rminus_0_r                                          *)
(*     * etc.                                                                 *)
(*   + examples:                                                              *)
(*     * ltRNge (for Reals) corresponds to ltnNge (from ssrnat)               *)
(*     * Lemma ltR0n n : (0 < n%:R) <-> (O < n)%nat. (for Reals)              *)
(*       corresponds to                                                       *)
(*       Lemma ltr0n n : (0 < n%:R :> R) = (0 < n)%N. (from ssrnum)           *)
(*       (instead of lt_0_INR : forall n : nat, (0 < n)%coq_nat -> 0 < INR n  *)
(*       in the standard library)                                             *)
(*     * Lemma INR_eq0 n : (n%:R = 0) <-> (n = O).                            *)
(*       instead of the one-sided INR_eq in the standard library              *)
(*     * Lemma leR_add2r {p m n} : m + p <= n + p <-> m <= n.                 *)
(* - ssr-like lemmas (not so good matches):                                   *)
(*   + Lemma invR_gt0 : forall x : R, 0 < x -> 0 < / x                        *)
(*     corresponds to                                                         *)
(*     Lemma invr_gt0 x : (0 < x^-1) = (0 < x).                               *)
(******************************************************************************)

Reserved Notation "a '>b=' b" (at level 70).
Reserved Notation "a '<b=' b" (at level 70).
Reserved Notation "a '<b' b" (at level 70).
Reserved Notation "a '>b' b" (at level 70).
Reserved Notation "a '<b=' b '<b=' c" (at level 70, b at next level).
Reserved Notation "a '<b' b '<b' c" (at level 70, b at next level).
Reserved Notation "n %:R" (at level 2, left associativity, format "n %:R").
Reserved Notation "'min(' x ',' y ')'" (format "'min(' x ','  y ')'").
Reserved Notation "'max(' x ',' y ')'" (format "'max(' x ','  y ')'").

Local Open Scope R_scope.

(* "^" = pow : R -> nat -> R *)
Notation "x ^- n" := (/ (x ^ n)) : R_scope.

Notation "`| x |" := (Rabs x) : R_scope.

Notation "n %:R" := (INR n) : R_scope.

Global Hint Resolve Rlt_R0_R2 :  core.
Global Hint Resolve Rlt_0_1 : core.
Global Hint Resolve Rle_0_1 : core.

Definition leRb a b := if Rle_dec a b is left _ then true else false.
Notation "a '<b=' b" := (leRb a b) : R_scope.

Definition geRb (a b : R) := leRb b a.
Notation "a '>b=' b" := (geRb a b) : R_scope.

Definition ltRb (a b : R) := if Rlt_dec a b is left _ then true else false.
Notation "a '<b' b" := (ltRb a b) : R_scope.

Definition gtRb a b := b <b a.
Notation "a '>b' b" := (gtRb a b) : R_scope.

Notation "a '<b=' b '<b=' c" := (leRb a b && leRb b c) : R_scope.
Notation "a '<b' b '<b' c" := (ltRb a b && ltRb b c) : R_scope.

Lemma leRP (a b : R) : reflect (a <= b) (a <b= b).
Proof. by apply: (iffP idP); rewrite /leRb; case: Rle_dec. Qed.

Lemma ltRP (a b : R) : reflect (a < b) (a <b b).
Proof. by apply: (iffP idP); rewrite /ltRb; case: Rlt_dec. Qed.

Lemma leR2P (a b c : R) : reflect (a <= b <= c) (a <b= b <b= c).
Proof.
by apply: (iffP idP) => [/andP[/leRP ? /leRP ?]|[/leRP-> /leRP->]].
Qed.

Lemma ltR2P (a b c : R) : reflect (a < b < c) (a <b b <b c).
Proof.
by apply: (iffP idP) => [/andP[/ltRP ? /ltRP ?]|[/ltRP-> /ltRP->]].
Qed.

Definition add0R : left_id 0 Rplus := Rplus_0_l.
Definition addR0 : right_id 0 Rplus := Rplus_0_r.

Lemma addRC : commutative Rplus.
Proof. by move=> m n; rewrite Rplus_comm. Qed.

Lemma addRA : associative Rplus.
Proof. by move=> m n p; rewrite Rplus_assoc. Qed.

Lemma addRCA : left_commutative Rplus. Proof. by move=> ? ? ?; ring. Qed.

Lemma addRAC : right_commutative Rplus. Proof. by move=> ? ? ?; ring. Qed.

Lemma addRK (a : R) : cancel (Rplus^~ a) (Rminus^~ a).
Proof. move=> ?; ring. Qed.

Lemma addRR r : r + r = 2 * r.
Proof. by field. Qed.

Lemma addRN r : r + - r = 0.
Proof. exact: Rplus_opp_r r. Qed.

Definition subR0 : right_id 0 Rminus := Rminus_0_r.
Definition sub0R := Rminus_0_l.

Lemma subRR a : a - a = 0. Proof. by rewrite Rminus_diag_eq. Qed.

Lemma subRKC m n : m + (n - m) = n. Proof. ring. Qed.

Lemma subRK m n : n - m + m = n. Proof. ring. Qed.

Lemma subR_eq0 (x y : R) : (x - y = 0) <-> (x = y).
Proof. by split => [/Rminus_diag_uniq //|->]; rewrite subRR. Qed.
Lemma subR_eq0' (x y : R) : (x - y == 0) = (x == y).
Proof. by apply/idP/idP => /eqP/subR_eq0/eqP. Qed.

Lemma subR_eq x y z : (x - z = y) <-> (x = y + z).
Proof. by split; [move=> <-; rewrite subRK|move=> ->; rewrite addRK]. Qed.
Lemma subR_eq' x y z : (x - z == y) = (x == y + z).
Proof. by apply/eqP/eqP => /subR_eq. Qed.

Lemma subRBA m n p : m - (n - p) = m + p - n.
Proof. by field. Qed.

Definition mul0R : left_zero 0 Rmult := Rmult_0_l.
Definition mulR0 : right_zero 0 Rmult := Rmult_0_r.
Definition mul1R : ssrfun.left_id 1%R Rmult := Rmult_1_l.
Definition mulR1 : ssrfun.right_id 1%R Rmult := Rmult_1_r.
Definition mulRN := Ropp_mult_distr_r_reverse.
Definition mulNR := Ropp_mult_distr_l_reverse.
Lemma mulRN1 x : x * -1 = -x. Proof. by rewrite mulRN mulR1. Qed.
Lemma mulN1R x : -1 * x = -x. Proof. by rewrite mulNR mul1R. Qed.

Definition mulRC : commutative Rmult := Rmult_comm.

Lemma mulRA : associative Rmult.
Proof. by move=> m n p; rewrite Rmult_assoc. Qed.

Lemma mulRCA : left_commutative Rmult. Proof. by move=> ? ? ?; ring. Qed.
Lemma mulRAC : right_commutative Rmult. Proof. by move=> ? ? ?; ring. Qed.

Lemma mulRDl : left_distributive Rmult Rplus.
Proof. by move=> *; rewrite Rmult_plus_distr_r. Qed.
Lemma mulRDr : right_distributive Rmult Rplus.
Proof. by move=> *; rewrite Rmult_plus_distr_l. Qed.
Lemma mulRBl : left_distributive Rmult Rminus.
Proof. by move=> *; ring. Qed.
Lemma mulRBr : right_distributive Rmult Rminus.
Proof. by move=> *; ring. Qed.

Lemma mulR_eq0 (x y : R) : (x * y = 0) <-> ((x = 0) \/ (y = 0)).
Proof.
split => [/Rmult_integral //| [] ->]; by rewrite ?mul0R ?mulR0.
Qed.
Lemma mulR_eq0' (x y : R) : (x * y == 0) = ((x == 0) || (y == 0)).
Proof.
apply/idP/idP => [/eqP/mulR_eq0[]/eqP-> //|]; first by rewrite orbT.
by case/orP => /eqP ->; rewrite ?mulR0 ?mul0R.
Qed.

Lemma mulR_neq0 (x y : R) : (x * y <> 0) <-> ((x <> 0) /\ (y <> 0)).
Proof. by rewrite mulR_eq0; tauto. Qed.
Lemma mulR_neq0' (x y : R) : (x * y != 0) = ((x != 0) && (y != 0)).
Proof. by rewrite mulR_eq0' negb_or. Qed.

Lemma eqR_mul2l {r r1 r2} : r <> 0 -> (r * r1 = r * r2) <-> (r1 = r2).
Proof. by move=> r0; split => [/Rmult_eq_reg_l/(_ r0) | ->]. Qed.

Lemma eqR_mul2r {r r1 r2} : r <> 0 -> (r1 * r = r2 * r) <-> (r1 = r2).
Proof. by move=> r0; split => [/Rmult_eq_reg_r/(_ r0)|->]. Qed.

Definition ltRR := Rlt_irrefl.
Lemma ltRR' n : (n <b n) = false.
Proof. by apply/ltRP/ltRR. Qed.

Definition ltRW {m n} : m < n -> m <= n := Rlt_le m n.
Lemma ltRW' {a b : R} : a <b b -> a <b= b.
Proof. by move/ltRP/Rlt_le/leRP. Qed.

Lemma ltR2W (a b c : R) : a < b < c -> a <= b <= c.
Proof.  by case=> ? ?; split; apply/ltRW. Qed.
Lemma ltR2W' (a b c : R) : a <b b <b c -> a <b= b <b= c.
Proof. by move/ltR2P/ltR2W/leR2P. Qed.
Arguments ltR2W {a b c}.
Arguments ltR2W' {a b c}.

Lemma gtR_eqF a b : a < b -> b != a.
Proof. by move=> ab; apply/eqP => ba; move: ab; rewrite ba => /ltRR. Qed.

Lemma ltR_eqF (r1 r2 : R) : r1 < r2 -> r1 != r2.
Proof. by move/Rlt_not_eq/eqP. Qed.

Definition leRR := Rle_refl.
Lemma leRR' r : r <b= r. Proof. exact/leRP/leRR. Qed.

Lemma ltR_trans y x z : x < y -> y < z -> x < z.
Proof. exact: Rlt_trans. Qed.
Arguments ltR_trans [_] [_] [_].

Lemma leR_trans y x z : x <= y -> y <= z -> x <= z.
Proof. exact: Rle_trans. Qed.
Arguments leR_trans [_] [_] [_].

Lemma leR_ltR_trans y x z : x <= y -> y < z -> x < z.
Proof. exact: Rle_lt_trans. Qed.
Arguments leR_ltR_trans [_] [_] [_].

Lemma ltR_leR_trans y x z : x < y -> y <= z -> x < z.
Proof. exact: Rlt_le_trans. Qed.
Arguments ltR_leR_trans [_] [_] [_].

Definition oppR0 := Ropp_0.
Definition oppRK := Ropp_involutive.

Lemma subR_opp x y : x - - y = x + y. Proof. by rewrite /Rminus oppRK. Qed.
Lemma addR_opp x y : x + - y = x - y. Proof. by []. Qed.

Definition oppRD := Ropp_plus_distr.
Definition oppRB := Ropp_minus_distr.
Lemma subRB x y z : x - (y - z) = x - y + z.
Proof. by rewrite -addR_opp oppRB addRA addRAC. Qed.
Lemma subRD x y z : x - (y + z) = x - y - z.
Proof. by rewrite -addR_opp oppRD addRA. Qed.

Lemma oppR_eq0 x : (- x == 0) = (x == 0).
Proof.
apply/idP/idP => [|/eqP ->]; last by rewrite oppR0.
by apply: contraTT; move/eqP/Ropp_neq_0_compat/eqP.
Qed.

Lemma addR_eq0 x y : (x + y = 0) <-> (x = - y).
Proof. by rewrite -[y in LHS]oppRK subR_eq0. Qed.
Lemma addR_eq0' x y : (x + y == 0) = (x == - y).
Proof. by apply/idP/idP => /eqP/addR_eq0/eqP. Qed.

Lemma eqR_opp x y : (- x == - y) = (x == y).
Proof. by apply/eqP/eqP => [Hopp|->//]; rewrite -[LHS]oppRK -[RHS]oppRK Hopp. Qed.

Lemma eqR_oppLR x y : (- x == y) = (x == - y).
Proof. by apply/eqP/eqP => [<-|->]; rewrite oppRK. Qed.

Lemma oppR_ge0 x : x <= 0 -> 0 <= - x.
Proof. by move/Rle_ge; exact: Ropp_0_ge_le_contravar. Qed.

Lemma oppR_lt0 x : 0 < x <-> 0 > - x.
Proof.
split; first exact: Ropp_0_lt_gt_contravar.
by move/Ropp_gt_lt_contravar; rewrite oppRK oppR0.
Qed.

Lemma oppR_gt0 x : 0 > x <-> 0 < - x.
Proof.
split; first exact: Ropp_0_gt_lt_contravar.
by move/Ropp_gt_lt_contravar; rewrite oppRK oppR0.
Qed.

Lemma leRNlt m n : (m <= n) <-> ~ (n < m).
Proof. split; [exact: Rle_not_lt | exact: Rnot_lt_le]. Qed.
Lemma leRNlt' m n : (m <b= n) = ~~ (n <b m).
Proof.
apply/idP/idP => [/leRP ? | /ltRP/Rnot_lt_le ?];
  [exact/ltRP/Rle_not_gt | exact/leRP].
Qed.

Lemma ltRNge m n : (m < n) <-> ~ (n <= m).
Proof. split; [exact: Rlt_not_le | exact: Rnot_le_lt]. Qed.
Lemma ltRNge' m n : (m <b n) = ~~ (n <b= m).
Proof. by rewrite leRNlt' negbK. Qed.

Lemma leRNgt (x y : R) : (x <= y) <-> ~ (y < x).
Proof. by rewrite leRNlt. Qed.
Lemma leRNgt' (x y : R) : (x <b= y) = ~~ (y <b x).
Proof. by rewrite ltRNge' negbK. Qed.

Lemma leR_eqVlt m n : (m <= n) <-> (m = n) \/ (m < n).
Proof.
split => [|[->|]]; [ |exact: leRR|exact: ltRW].
by case/Rle_lt_or_eq_dec => ?; [right|left].
Qed.
Lemma leR_eqVlt' m n : (m <b= n) = (m == n) || (m <b n).
Proof.
by apply/idP/idP => [/leRP/leR_eqVlt[/eqP -> //|/ltRP ->]|/orP[/eqP ->|/ltRP]];
  [rewrite orbT|rewrite leRR'|move/ltRP/ltRW'].
Qed.

Lemma ltR_neqAle' m n : (m <b n) = (m != n) && (m <b= n).
Proof. by rewrite ltRNge' leR_eqVlt' negb_or ltRNge' negbK eq_sym. Qed.
Lemma ltR_neqAle m n : (m < n) <-> (m <> n) /\ (m <= n).
Proof.
by split => [/ltRP|[/eqP H /leRP K]];
  [rewrite ltR_neqAle' => /andP[/eqP ? /leRP] |
   apply/ltRP; rewrite ltR_neqAle' H].
Qed.

Lemma lt0R x : (0 <b x) = (x != 0) && (0 <b= x).
Proof. by rewrite ltR_neqAle' eq_sym. Qed.

Lemma le0R x : (0 <b= x) = (x == 0) || (0 <b x).
Proof. by rewrite leR_eqVlt' eq_sym. Qed.

(* Lemma pnatr_eq0 n : (n%:R == 0 :> R) = (n == 0)%N. *)
Lemma INR_eq0 n : (n%:R = 0) <-> (n = O).
Proof. by split => [|-> //]; rewrite (_ : 0 = 0%:R) // => /INR_eq ->. Qed.
Lemma INR_eq0' n : (n%:R == 0) = (n == O).
Proof. by apply/idP/idP => /eqP/INR_eq0/eqP. Qed.

Lemma natRD m n : (m + n)%:R = m%:R + n%:R.
Proof. exact: plus_INR. Qed.
Lemma natRB m n : (n <= m)%nat -> (m - n)%:R = m%:R - n%:R.
Proof. by move=> nm; rewrite minus_INR //; exact/leP. Qed.
Lemma natRM m n : (m * n)%:R = m%:R * n%:R.
Proof. by rewrite mult_INR. Qed.

Lemma eqR_le x y : (x = y) <-> (x <= y <= x).
Proof. split => [->| [] ]; by [split; exact/leRR | exact: Rle_antisym]. Qed.

Lemma eqR_le_Ngt {x y} : x <= y -> ~ x < y -> y = x.
Proof. by case/leR_eqVlt. Qed.

Definition leR0n n : 0 <= n%:R := pos_INR n.
Lemma leR0n' n : (0 <b= n%:R). Proof. exact/leRP/leR0n. Qed.

Lemma ltR0n n : (0 < n%:R) <-> (O < n)%nat.
Proof.
by split => [/gtR_eqF/eqP/INR_not_0/Nat.neq_0_lt_0/ltP | /ltP/lt_0_INR].
Qed.
Lemma ltR0n' n : (0 <b n%:R) = (O < n)%nat.
Proof. by apply/idP/idP => [/ltRP/ltR0n|/ltR0n/ltRP]. Qed.

Lemma leR_oppr x y : (x <= - y) <-> (y <= - x).
Proof. by split; move/Ropp_le_contravar; rewrite oppRK. Qed.

Lemma leR_oppl x y : (- x <= y) <-> (- y <= x).
Proof. by split; move/Ropp_le_contravar; rewrite oppRK. Qed.

Lemma ltR_oppr x y : (x < - y) <-> (y < - x).
Proof. by split; move/Ropp_lt_contravar; rewrite oppRK. Qed.

Lemma ltR_oppl x y : (- x < y) <-> (- y < x).
Proof. by split; move/Ropp_lt_contravar; rewrite oppRK. Qed.

(* uninteresting lemmas? *)
(* NB: Ropp_gt_lt_contravar *)
(* NB: Ropp_le_ge_contravar *)
(* NB: Ropp_le_cancel *)
(* NB: Ropp_ll_cancel *)

(*****************************************)
(* inequalities and addition/subtraction *)
(*****************************************)

Definition addR_ge0 := Rplus_le_le_0_compat.   (* 0 <= r1 -> 0 <= r2 -> 0 <= r1 + r2 *)
Definition addR_gt0 := Rplus_lt_0_compat.      (* 0 < r1  -> 0 < r2  -> 0 < r1 + r2 *)
Definition addR_gt0wr := Rplus_le_lt_0_compat. (* 0 <= r1 -> 0 < r2  -> 0 < r1 + r2 *)
Definition addR_gt0wl := Rplus_lt_le_0_compat. (* 0 < r1  -> 0 <= r2 -> 0 < r1 + r2 *)

Definition leR_add := Rplus_le_compat. (* r1 <= r2 -> r3 <= r4 -> r1 + r3 <= r2 + r4 *)
Lemma leR_add' m1 m2 n1 n2 : m1 <b= n1 -> m2 <b= n2 -> m1 + m2 <b= n1 + n2.
Proof. by move=> ? ?; apply/leRP/Rplus_le_compat; exact/leRP. Qed.

Lemma leR_add2r {p m n} : m + p <= n + p <-> m <= n.
Proof. by split; [exact: Rplus_le_reg_r | exact: Rplus_le_compat_r]. Qed.
Lemma leR_add2r' p m n : (m + p <b= n + p) = (m <b= n).
Proof. by apply/idP/idP => [/leRP/leR_add2r/leRP //|/leRP/leR_add2r/leRP]. Qed.

Lemma leR_add2l {p m n} : p + m <= p + n <-> m <= n.
Proof. by split; [exact: Rplus_le_reg_l | exact: Rplus_le_compat_l]. Qed.

Definition ltR_add := Rplus_lt_compat. (* r1 < r2 -> r3 < r4 -> r1 + r3 < r2 + r4 *)

Lemma ltR_add2r {p m n} : m + p < n + p <-> m < n.
Proof. by split; [exact: Rplus_lt_reg_r | exact: Rplus_lt_compat_r]. Qed.
Lemma ltR_add2r' (p m n : R) : (m + p <b n + p) = (m <b n).
Proof. by apply/idP/idP => [/ltRP/ltR_add2r/ltRP // | /ltRP/ltR_add2r/ltRP]. Qed.

Lemma ltR_add2l {p m n} : p + m < p + n <-> m < n.
Proof. by split; [exact: Rplus_lt_reg_l | exact: Rplus_lt_compat_l]. Qed.

Definition leR_lt_add := Rplus_le_lt_compat. (* x <= y -> z < t -> x + z < y + t *)

Lemma ltR_subRL m n p : (n < p - m) <-> (m + n < p).
Proof.
split => H.
- by move/(@ltR_add2l m) : H; rewrite subRKC.
- by apply (@ltR_add2l m); rewrite subRKC.
Qed.
Lemma ltR_subRL' m n p : (n <b p - m) = (m + n <b p).
Proof. by apply/idP/idP => /ltRP/ltR_subRL/ltRP. Qed.

Lemma ltR_subl_addr x y z : (x - y < z) <-> (x < z + y).
Proof.
split => H; [apply (@ltR_add2r (-y)) | apply (@ltR_add2r y)]; last by rewrite subRK.
by rewrite -addRA; apply: (ltR_leR_trans H); rewrite Rplus_opp_r addR0; exact/leRR.
Qed.

Lemma leR_subr_addr x y z : (x <= y - z) <-> (x + z <= y).
Proof.
split => [|H]; first by move/leRP; rewrite -(leR_add2r' z) subRK => /leRP.
by apply/leRP; rewrite -(leR_add2r' z) subRK; exact/leRP.
Qed.
Lemma leR_subr_addr' x y z : (x <b= y - z) = (x + z <b= y).
Proof. by apply/idP/idP => /leRP/leR_subr_addr/leRP. Qed.

Lemma leR_subl_addr x y z : (x - y <= z) <-> (x <= z + y).
Proof.
split => [|H]; first by move/leRP; rewrite -(leR_add2r' y) subRK => /leRP.
by apply/leRP; rewrite -(leR_add2r' y) subRK; exact/leRP.
Qed.
Lemma leR_subl_addr' x y z : (x - y <b= z) = (x <b= z + y).
Proof. by apply/idP/idP => /leRP/leR_subl_addr/leRP. Qed.

Definition leR_sub_addr := (leR_subl_addr, leR_subr_addr).

Definition ltR_subr_addl := ltR_subRL.

Lemma ltR_subl_addl x y z : (x - y < z) <-> (x < y + z).
Proof.
split => [/(@ltR_add2r y)|/(@ltR_add2r (- y))]; first by rewrite subRK addRC.
by rewrite addR_opp (addRC y) addR_opp addRK.
Qed.

Lemma ltR_subr_addr x y z : (x < y - z) <-> (x + z < y).
Proof. by rewrite ltR_subr_addl addRC. Qed.

Lemma leR_addl x y : (x <= x + y) <-> (0 <= y).
Proof. by rewrite -{1}(addR0 x) leR_add2l. Qed.
Lemma leR_addr x y : (x <= y + x) <-> (0 <= y).
Proof. by rewrite -{1}(add0R x) leR_add2r. Qed.
Lemma ltR_addl x y : (x < x + y) <-> (0 < y).
Proof. by rewrite -{1}(addR0 x) ltR_add2l. Qed.

Lemma subR_gt0 x y : (0 < y - x) <-> (x < y).
Proof. by split; [exact: Rminus_gt_0_lt | exact: Rlt_Rminus]. Qed.
Lemma subR_lt0 x y : (y - x < 0) <-> (y < x).
Proof. by split; [exact: Rminus_lt | exact: Rlt_minus]. Qed.
Lemma subR_ge0 x y : (0 <= y - x) <-> (x <= y).
Proof.
split => [|?]; first by move/leR_subr_addr; rewrite add0R.
by apply/leR_subr_addr; rewrite add0R.
Qed.
Lemma subr_le0  x y : (y - x <= 0) <-> (y <= x).
Proof.
split => [|?]; first by move/leR_subl_addr; rewrite add0R.
by apply/leR_subl_addr; rewrite add0R.
Qed.

(***********************************)
(* inequalities and multiplication *)
(***********************************)

Definition mulR_ge0 := Rmult_le_pos.         (* 0 <= r1 -> 0 <= r2  -> 0 <= r1 * r2 *)
Definition mulR_gt0 := Rmult_lt_0_compat.    (* 0 < r1  -> 0 < r2   -> 0 < r1 * r2 *)

Definition leR_wpmul2l := Rmult_le_compat_l. (* 0 <= r  -> r1 <= r2 -> r * r1 <= r * r2 *)
Definition leR_wpmul2r := Rmult_le_compat_r. (* 0 <= r  -> r1 <= r2 -> r1 * r <= r2 * r *)
Definition leR_pmul    := Rmult_le_compat.   (* 0 <= r1 -> 0 <= r3  -> r1 <= r2 -> r3 <= r4 -> r1 * r3 <= r2 * r4 *)
Arguments leR_wpmul2l [_] [_] [_].
Arguments leR_wpmul2r [_] [_] [_].
Arguments leR_pmul [_] [_] [_] [_].

Definition ltR_pmul := Rmult_le_0_lt_compat. (* 0 <= r1 -> 0 <= r3 -> r1 < r2 -> r3 < r4 -> r1 * r3 < r2 * r4 *)

(* NB: Rmult_ge_compat_l? *)

Lemma paddR_eq0 (x y : R) :
  0 <= x -> 0 <= y -> (x + y = 0) <-> (x = 0) /\ (y = 0).
Proof.
move=> x0 y0; split => [|[-> ->]]; last by rewrite addR0.
move=> H; move: (H) => /Rplus_eq_0_l -> //.
by move: H; rewrite addRC => /Rplus_eq_0_l ->.
Qed.
Arguments paddR_eq0 {x} {y}.

Lemma paddR_neq0 (p q : R) (p0 : 0 <= p) (q0 : 0 <= q) : p + q != 0 <-> p != 0 \/ q != 0.
Proof.
split => [H | /orP].
- apply/orP; rewrite -negb_and; apply: contra H => /andP[/eqP -> /eqP ->].
  by rewrite addR0.
- rewrite -negb_and; apply: contra => /eqP/paddR_eq0.
  by case/(_ p0)/(_ q0) => -> ->; rewrite eqxx.
Qed.
Arguments paddR_neq0 {p} {q}.

Lemma leR_pmul2l m n1 n2 : 0 < m -> (m * n1 <= m * n2) <-> (n1 <= n2).
Proof.
by move=> m0; split; [exact: Rmult_le_reg_l | exact/Rmult_le_compat_l/ltRW].
Qed.
Lemma leR_pmul2l' m n1 n2 : 0 <b m -> (m * n1 <b= m * n2) = (n1 <b= n2).
Proof.
move=> /ltRP Hm.
apply/idP/idP; first by move/leRP/leR_pmul2l => /(_ Hm)/leRP.
by move/leRP/(leR_wpmul2l (ltRW Hm))/leRP.
Qed.

Lemma leR_pmul2r m n1 n2 : 0 < m -> (n1 * m <= n2 * m) <-> (n1 <= n2).
Proof.
by move=> m0; split; [exact: Rmult_le_reg_r | exact/Rmult_le_compat_r/ltRW].
Qed.

Lemma ltR_pmul2l m n1 n2 : 0 < m -> (m * n1 < m * n2) <-> (n1 < n2).
Proof. by move=> m0; split; [exact: Rmult_lt_reg_l | exact/Rmult_lt_compat_l]. Qed.

Lemma ltR_pmul2r m n1 n2 : 0 < m -> (n1 * m < n2 * m) <-> (n1 < n2).
Proof. by move=> m0; split; [exact: Rmult_lt_reg_r | exact/Rmult_lt_compat_r]. Qed.
Lemma leR_pmul2r' m n1 n2 : 0 <b m -> (n1 * m <b= n2 * m) = (n1 <b= n2).
Proof. by move=> Hm; rewrite -!(mulRC m) leR_pmul2l'. Qed.

Lemma pmulR_lgt0 x y : 0 < x -> (0 < y * x) <-> (0 < y).
Proof. by move=> x0; rewrite -{1}(mul0R x) ltR_pmul2r. Qed.

Arguments leR_pmul2l [_] [_] [_].
Arguments leR_pmul2r [_] [_] [_].
Arguments ltR_pmul2l [_] [_] [_].
Arguments ltR_pmul2r [_] [_] [_].
Arguments pmulR_lgt0 [_] [_].

Lemma leR_pmull m n : 1 <= n -> 0 <= m -> m <= n * m.
Proof.
move=> n1 m0; case/boolP : (m == 0) => [/eqP ->|m0']; first by rewrite mulR0; exact/leRR.
by rewrite -{1}(mul1R m) leR_pmul2r // ltR_neqAle; split => //; apply/eqP; rewrite eq_sym.
Qed.

Lemma leR_pmulr m n : 1 <= n -> 0 <= m -> m <= m * n.
Proof. by move=> n1 m0; rewrite mulRC; apply leR_pmull. Qed.

Lemma leR_nat m n : (m%:R <= n%:R) <-> (m <= n)%nat.
Proof. by split => [/INR_le/leP|/leP/le_INR]. Qed.
Lemma leR_nat' m n : (m%:R <b= n%:R) = (m <= n)%nat.
Proof. by apply/idP/idP => [/leRP/leR_nat|/leR_nat/leRP]. Qed.

Lemma ltR_nat m n : (m%:R < n%:R) <-> (m < n)%nat.
Proof. by split => [/INR_lt/ltP|/ltP/lt_INR]. Qed.
Lemma ltR_nat' m n : (m%:R <b n%:R) = (m < n)%nat.
Proof. by apply/idP/idP => [/ltRP/ltR_nat|/ltR_nat/ltRP]. Qed.

Lemma ltR0Sn n : 0 < n.+1%:R.
Proof. by move/ltR_nat: (ltn0Sn n). Qed.

Lemma lt0n_neqR0 n : (0 < n)%nat <-> n%:R != 0.
Proof. by rewrite lt0n; split => /eqP /INR_eq0 /eqP. Qed.

Lemma lt0n_neqR0' n : (0 < n)%nat = (n%:R != 0).
Proof. by apply/(sameP idP)/(iffP idP) => /lt0n_neqR0. Qed.

(*************)
(* invR/divR *)
(*************)

Lemma invR_gt0 x : 0 < x -> 0 < / x.
Proof. by move=> x0; apply Rinv_0_lt_compat. Qed.

(* Rinv_neq_0_compat : forall r : R, r <> 0 -> / r <> 0 *)
Lemma invR_neq0 (x : R) : x <> 0 -> / x <> 0.
Proof. exact: Rinv_neq_0_compat. Qed.
Lemma invR_neq0' (x : R) : x != 0 -> / x != 0.
Proof. by move/eqP/invR_neq0/eqP. Qed.

Lemma invR_eq0 (x : R) : / x = 0 -> x = 0.
Proof.
move/eqP=> H; apply/eqP; apply: contraTT H => H; exact/eqP/invR_neq0/eqP.
Qed.
Lemma invR_eq0' (x : R) : / x == 0 -> x == 0.
Proof. by move/eqP/invR_eq0/eqP. Qed.

Definition invR1 : / 1 = 1 := Rinv_1.

Definition invRK (r : R) : r != 0 -> / / r = r.
Proof. by move/eqP; exact: Rinv_involutive. Qed.

Lemma invRM (r1 r2 : R) : r1 != 0 -> r2 != 0 -> / (r1 * r2) = / r1 * / r2.
Proof. by move=> /eqP r10 /eqP r20; rewrite Rinv_mult_distr. Qed.

Lemma leR_inv x y : 0 < y -> y <= x -> / x <= / y.
Proof. by move=> x0 y0; apply/Rinv_le_contravar. Qed.
(* NB: Rle_Rinv does the same as Rinv_le_contravar with one more hypothesis *)
Lemma leR_inv' : {in [pred x | true] & [pred x | 0 <b x], {homo Rinv : a b /~ a <= b}}.
Proof. by move=> a b; rewrite !inE => _ /ltRP b0 ba; exact/Rinv_le_contravar. Qed.

Lemma invR_le x y : 0 < x -> 0 < y -> / y <= / x -> x <= y.
Proof.
move=> x0 y0 H.
rewrite -(invRK x); last exact/gtR_eqF.
rewrite -(invRK y); last exact/gtR_eqF.
by apply leR_inv => //; exact/invR_gt0.
Qed.

Lemma ltR_inv x y : 0 < x -> 0 < y -> y < x -> / x < / y.
Proof. by move=> xo y0; apply/Rinv_lt_contravar/mulR_gt0. Qed.

Lemma divRE x y : x / y = x * / y. Proof. by []. Qed.

Definition divRR (x : R) : x != 0 -> x / x = 1.
Proof. by move=> x0; rewrite /Rdiv Rinv_r //; exact/eqP. Qed.

Lemma divR1 (x : R) : x / 1 = x.
Proof. by rewrite /Rdiv invR1 mulR1. Qed.

Lemma div1R (x : R) : 1 / x = / x.
Proof. by rewrite /Rdiv mul1R. Qed.

Lemma div0R (x : R) : 0 / x = 0.
Proof. by rewrite /Rdiv mul0R. Qed.

Lemma divR_ge0 (x y : R) : 0 <= x -> 0 < y -> 0 <= x / y.
Proof. move=> x0 y0; apply mulR_ge0 => //; exact/ltRW/invR_gt0. Qed.

Lemma divR_gt0 (x y : R) : 0 < x -> 0 < y -> 0 < x / y.
Proof. exact: Rdiv_lt_0_compat x y. Qed.

Lemma divRM (r1 r2 x : R) : r1 != 0 -> r2 != 0 -> x / (r1 * r2) = x / r1 * / r2.
Proof. by move=> ? ?; rewrite {1}/Rdiv invRM // mulRA. Qed.

Lemma divR_neq0' (x y : R) : x != 0 -> y != 0 -> x / y != 0.
Proof. by move => x0 y0; rewrite mulR_neq0' x0 /= invR_neq0'. Qed.

Lemma divN1R x : -1 / x = - / x. Proof. by rewrite /Rdiv mulN1R. Qed.

Definition mulRV (x : R) : x != 0 -> x * / x = 1 := divRR x.

Lemma divRDl : left_distributive Rdiv Rplus.
Proof. by move=> *; rewrite /Rdiv -mulRDl. Qed.

Lemma divRBl : left_distributive Rdiv Rminus.
Proof. by move=> x y z; rewrite -[in RHS]addR_opp -mulNR divRDl. Qed.

(* Rinv_l_sym *)
Lemma mulVR (x : R) : x != 0 -> / x * x = 1.
Proof. by move=> x0; rewrite mulRC mulRV. Qed.

Lemma leR_pdivl_mulr z x y : 0 < z -> (x <= y / z) <-> (x * z <= y).
Proof.
move=> z0; split => [/(leR_wpmul2l (ltRW z0))|H].
- rewrite mulRC mulRCA mulRV ?mulR1 //; exact/gtR_eqF.
- apply/(@leR_pmul2r z) => //; rewrite -mulRA mulVR ?mulR1 //; exact/gtR_eqF.
Qed.
Lemma leR_pdivl_mulr' z x y : 0 < z -> (x <b= y / z) = (x * z <b= y).
Proof.
move=> z0; apply/idP/idP => /leRP.
- by rewrite leR_pdivl_mulr // => /leRP.
- by rewrite -leR_pdivl_mulr // => /leRP.
Qed.

Lemma ltR_pdivl_mulr z x y : 0 < z -> (x < y / z) <-> (x * z < y).
Proof.
move=> z0; split => [/(ltR_pmul2l z0)|H].
- by rewrite mulRC mulRCA mulRV ?mulR1 //; exact/gtR_eqF.
- by apply/(@ltR_pmul2r z) => //; rewrite -mulRA mulVR ?mulR1 //; exact/gtR_eqF.
Qed.
Lemma ltR_pdivl_mulr' z x y : 0 < z -> (x <b y / z) = (x * z <b y).
Proof.
move=> z0; apply/idP/idP => /ltRP.
- by rewrite ltR_pdivl_mulr // => /ltRP.
- by rewrite -ltR_pdivl_mulr // => /ltRP.
Qed.

Lemma eqR_divr_mulr z x y : z != 0 -> (y / z = x) <-> (y = x * z).
Proof.
move=> z0; split => [<-|->]; first by rewrite -mulRA mulVR // mulR1.
by rewrite /Rdiv -mulRA mulRV // mulR1.
Qed.

Lemma leR_pdivr_mulr z x y : 0 < z -> (y / z <= x) <-> (y <= x * z).
Proof.
move=> z0; split => [/(leR_wpmul2r (ltRW z0))|H].
- by rewrite -mulRA mulVR ?mulR1 //; exact/gtR_eqF.
- by apply/(@leR_pmul2r z) => //; rewrite -mulRA mulVR ?mulR1 //; exact/gtR_eqF.
Qed.
Lemma leR_pdivr_mulr' z x y : 0 < z -> (y / z <b= x) = (y <b= x * z).
Proof.
move=> z0; apply/idP/idP => /leRP.
- by rewrite leR_pdivr_mulr // => /leRP.
- by rewrite -leR_pdivr_mulr // => /leRP.
Qed.

Lemma ltR_pdivr_mulr z x y : 0 < z -> (y / z < x) <-> (y < x * z).
Proof.
move=> z0; split => [/(ltR_pmul2r z0)|H].
- by rewrite -mulRA mulVR ?mulR1 //; exact/gtR_eqF.
- by apply/(@ltR_pmul2r z) => //; rewrite -mulRA mulVR ?mulR1 //; exact/gtR_eqF.
Qed.
Lemma ltR_pdivr_mulr' z x y : 0 < z -> (y / z <b x) = (y <b x * z).
Proof.
move=> z0; apply/idP/idP => /ltRP.
- by rewrite ltR_pdivr_mulr // => /ltRP.
- by rewrite -ltR_pdivr_mulr // => /ltRP.
Qed.

Lemma invR_le1 x : 0 < x -> (/ x <= 1) <-> (1 <= x).
Proof. by move=> x0; rewrite -(div1R x) leR_pdivr_mulr // mul1R. Qed.
Lemma invR_le1' x : 0 < x -> (/ x <b= 1) = (1 <b= x).
Proof. by move=> x0; apply/idP/idP => /leRP/(invR_le1 _ x0)/leRP. Qed.

Lemma invR_gt1 x : 0 < x -> (1 < / x) <-> (x < 1).
Proof.
move=> x0; split => x1; last by rewrite -invR1; apply ltR_inv.
move/ltR_inv : x1; rewrite invRK ?invR1; last exact/gtR_eqF.
by apply => //; exact/invR_gt0.
Qed.
Lemma invR_gt1' x : 0 < x -> (1 <b / x) = (x <b 1).
Proof. by move=> x0; apply/idP/idP => /ltRP/(invR_gt1 _ x0)/ltRP. Qed.

(*******)
(* pow *)
(*******)

Lemma natRexp r n : r%:R ^ n = (expn r n)%:R.
Proof.
by elim: n => // n IH; rewrite (expnSr r n) natRM -addn1 pow_add /= mulR1 IH.
Qed.

Lemma expR0 (a : R) : a ^ 0 = 1. Proof. exact: pow_O. Qed.

Definition expRn_gt0 n x := pow_lt x n.

Lemma expR_eq0 x (n : nat) : (x ^ n.+1 == 0) = (x == 0).
Proof.
apply/idP/idP => [/eqP H|/eqP ->]; apply/eqP; last by rewrite pow_ne_zero.
by move: (pow_nonzero x n.+1); tauto.
Qed.

Lemma expR_gt0 x : 0 < x -> forall n : nat, 0 < x ^ n.
Proof. by move=> ?; elim => [/= | n IH] => //; exact: mulR_gt0. Qed.

Lemma expR_ge0 x : 0 <= x -> forall n : nat, 0 <= x ^ n.
Proof.
move=> x_pos; elim => [// | n IH].
by rewrite -(mulR0 0); apply leR_pmul => //; exact/leRR.
Qed.

Lemma expR_neq0 x (n : nat) : x != 0 -> x ^ n != 0.
Proof. by move/eqP/(pow_nonzero _ n)/eqP. Qed.

Lemma exp1R n : 1 ^ n = 1. Proof. exact: pow1. Qed.

Lemma expRS x (n : nat) : x ^ n.+1 = x * x ^ n.
Proof. by rewrite tech_pow_Rmult. Qed.

Lemma expR1 x : x ^ 1 = x. Proof. exact: pow_1. Qed.

Lemma mulRR x : x * x = x ^ 2. Proof. by rewrite expRS expR1. Qed.

Lemma expRV x (n : nat) : x != 0 -> (/ x ) ^ n = x ^- n.
Proof.
move=> x0; elim : n => /= [ | n IH]; first by rewrite Rinv_1.
by rewrite invRM //; [rewrite IH | exact/expR_neq0].
Qed.

(* forall (x y : R) (n : nat), (x * y) ^ n = x ^ n * y ^ n*)
Definition expRM := Rpow_mult_distr.

Lemma expRB (n m : nat) r : (m <= n)%nat -> r <> 0 -> r ^ (n - m) = r ^ n / (r ^ m).
Proof.
move=> Hr ab.
by rewrite (pow_RN_plus r _ m) // plusE -minusE subnK // powRV //; exact/eqP.
Qed.

Lemma leR_wiexpR2l x :
  0 <= x -> x <= 1 -> {homo (pow x) : m n / (n <= m)%nat >-> m <= n}.
Proof.
move/leRP; rewrite le0R => /orP[/eqP -> _ m n|/ltRP x0 x1 m n /leP nm].
  case: n => [|n nm].
    case: m => [_ |m _]; first exact/leRR.
    by rewrite pow_ne_zero.
  rewrite pow_ne_zero; last by case: m nm.
  by rewrite pow_ne_zero //; exact/leRR.
apply invR_le => //.
- exact/expR_gt0.
- exact/expR_gt0.
- rewrite -expRV; last exact/gtR_eqF.
  rewrite -expRV; last exact/gtR_eqF.
  apply Rle_pow => //.
  by rewrite -invR1; apply leR_inv => //; exact/ltRP.
Qed.

Lemma leR_weexpR2l x : 1 <= x -> {homo (pow x) : m n / (m <= n)%nat >-> m <= n}.
Proof. by move=> x1 m n /leP nm; exact/Rle_pow. Qed.

Lemma sqrRB a b : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2.
Proof. by rewrite /= !mulR1 !mulRDr !mulRBl /=; field. Qed.

Lemma sqrRD a b : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2.
Proof. by rewrite /= !mulR1 !mulRDl !mul1R !mulRDr /=; field. Qed.

Lemma subR_sqr x y : x ^ 2 - y ^ 2 = (x - y) * (x + y).
Proof.
rewrite mulRDr 2!mulRDl -addRA (addRA (- y * x)) (mulRC x y) (addRC _ (y * x)).
by rewrite mulNR addRN add0R mulNR addR_opp 2!mulRR.
Qed.

Definition normR0 : `| 0 | = 0 := Rabs_R0.
Definition normRN x : `|- x| = `|x| := Rabs_Ropp x.

Definition normR_ge0 x : 0 <= `|x| := Rabs_pos x.
Lemma normR0_eq0 r : `| r | = 0 -> r = 0.
Proof. by move: (Rabs_no_R0 r); tauto. Qed.

Lemma leR0_norm x : x <= 0 -> `|x| = - x. Proof. exact: Rabs_left1. Qed.
Lemma ltR0_norm x : x < 0 -> `|x| = - x. Proof. by move/ltRW/leR0_norm. Qed.
Lemma geR0_norm x : 0 <= x -> `|x| = x. Proof. exact: Rabs_pos_eq. Qed.
Lemma gtR0_norm x : 0 < x -> `|x| = x. Proof. by move/ltRW/geR0_norm. Qed.

Lemma normRM : {morph Rabs : x y / x * y : R}.
Proof. exact: Rabs_mult. Qed.

Definition sqR_norm x : `| x | ^ 2 = x ^ 2 := pow2_abs x.

Definition distRC x y : `|x - y| = `|y - x| := Rabs_minus_sym x y.

Notation "'min(' x ',' y ')'" := (Rmin x y) : R_scope.
Notation "'max(' x ',' y ')'" := (Rmax x y) : R_scope.

Module ROrder.

Lemma minRE x y : min(x, y) = if (x <b y)%R then x else y.
Proof.
by case: ifP => /ltRP; [move/ltRW/Rmin_left|rewrite -leRNgt => /Rmin_right].
Qed.

Lemma maxRE x y : max(x, y) = if (x <b y)%N then y else x.
Proof.
by case: ifP => /ltRP; [move/ltRW/Rmax_right|rewrite -leRNgt => /Rmax_left].
Qed.

Lemma ltR_def x y : (x <b y)%R = (y != x) && (x <b= y)%R.
Proof. by rewrite ltR_neqAle' eq_sym. Qed.

Lemma anti_leR : antisymmetric (fun x y => x <b= y).
Proof. by move=> x y /andP[/leRP xy /leRP yx]; rewrite eqR_le. Qed.

Lemma leR_trans : transitive (fun x y => x <b= y).
Proof. by move=> z x y => /leRP xz /leRP zy; apply/leRP/(leR_trans xz). Qed.

Lemma leR_total : forall x y, (x <b= y) || (y <b= x).
Proof.
by move => x y; case: (Rle_or_lt x y) => xy; apply/orP;
  [left; exact/leRP|right; exact/leRP/ltRW].
Qed.

End ROrder.

Definition maxRA : associative Rmax := Rmax_assoc.
Definition maxRC : commutative Rmax := Rmax_comm.

Lemma maxRR : idempotent Rmax.
Proof. move=> x; rewrite Rmax_left //; exact/leRR. Qed.

Definition leR_maxl m n : m <= max(m, n) := Rmax_l m n.
Definition leR_maxr m n : n <= max(m, n) := Rmax_r m n.
Definition geR_minl m n : min(m, n) <= m := Rmin_l m n.
Definition geR_minr m n : min(m, n) <= n := Rmin_r m n.

Lemma leR_max x y z : max(y, z) <= x <-> (y <= x) /\ (z <= x).
Proof.
split => [| [yx zx] ].
  move/leRP; rewrite leR_eqVlt' => /orP[/eqP <-|/ltRP/Rmax_Rlt].
    by split; [exact: leR_maxl | exact: leR_maxr].
  by case=> ?; split; exact/ltRW.
by rewrite -(Rmax_right _ _ yx); exact: Rle_max_compat_l.
Qed.

Lemma leR_max' x y z : (max(y, z) <b= x) = (y <b= x) && (z <b= x).
Proof.
apply/idP/idP => [/leRP/leR_max[] /leRP -> /leRP -> //|].
by case/andP=> /leRP ? /leRP ?; exact/leRP/leR_max.
Qed.
