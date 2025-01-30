(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
Require Import Reals.
From mathcomp Require Import lra.
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
(*                                                                            *)
(*    Instantiation of MathComp's canonical big operators with Coq reals      *)
(*                                                                            *)
(* Various lemmas for iterated sum, prod, and max                             *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "n %:R" (at level 2, left associativity, format "n %:R").
Reserved Notation "'min(' x ',' y ')'" (format "'min(' x ','  y ')'").
Reserved Notation "'max(' x ',' y ')'" (format "'max(' x ','  y ')'").

Notation "\sum_ ( i <- r | P ) F" := (\big[Rplus/R0]_(i <- r | P%B) F)
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \sum_ ( i  <-  r  |  P ) '/  '  F ']'") : R_scope.
Notation "\sum_ ( i <- r ) F" :=  (\big[Rplus/R0]_(i <- r) F)
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \sum_ ( i  <-  r ) '/  '  F ']'") : R_scope.
Notation "\sum_ ( m <= i < n | P ) F" := (\big[Rplus/R0]_(m <= i < n | P%B) F)
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \sum_ ( m  <=  i  <  n  |  P ) '/  '  F ']'") : R_scope.
Notation "\sum_ ( m <= i < n ) F" := (\big[Rplus/R0]_(m <= i < n) F)
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \sum_ ( m  <=  i  <  n ) '/  '  F ']'") : R_scope.
Notation "\sum_ ( i | P ) F" := (\big[Rplus/R0]_(i | P%B) F)
  (at level 41, F at level 41, i at level 50,
           format "'[' \sum_ ( i  |  P ) '/  '  F ']'") : R_scope .
Notation "\sum_ i F" := (\big[Rplus/R0]_i F)
  (at level 41, F at level 41, i at level 0, right associativity,
  format "'[' \sum_ i '/  '  F ']'") : R_scope.
Notation "\sum_ ( i : t | P ) F" := (\big[Rplus/R0]_(i : t | P%B) F)
  (at level 41, F at level 41, i at level 50,
           only parsing) : R_scope.
Notation "\sum_ ( i : t ) F" := (\big[Rplus/R0]_(i : t) F)
  (at level 41, F at level 41, i at level 50,
           only parsing) : R_scope.
Notation "\sum_ ( i < n | P ) F" := (\big[Rplus/R0]_(i < n | P%B) F)
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \sum_ ( i  <  n  |  P ) '/  '  F ']'") : R_scope.
Notation "\sum_ ( i < n ) F" := (\big[Rplus/R0]_(i < n) F)
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \sum_ ( i  <  n ) '/  '  F ']'") : R_scope.
Notation "\sum_ ( i 'in' A | P ) F" := (\big[Rplus/R0]_(i in A | P%B) F)
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \sum_ ( i  'in'  A  |  P ) '/  '  F ']'") : R_scope.
Notation "\sum_ ( i 'in' A ) F" := (\big[Rplus/R0]_(i in A) F)
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \sum_ ( i  'in'  A ) '/  '  F ']'") : R_scope.

Notation "\prod_ ( i <- r | P ) F" := (\big[Rmult/R1]_(i <- r | P%B) F)
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \prod_ ( i  <-  r  |  P ) '/  '  F ']'") : R_scope.
Notation "\prod_ ( i <- r ) F" :=  (\big[Rmult/R1]_(i <- r) F)
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \prod_ ( i  <-  r ) '/  '  F ']'") : R_scope.
Notation "\prod_ ( m <= i < n | P ) F" := (\big[Rmult/R1]_(m <= i < n | P%B) F)
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \prod_ ( m  <=  i  <  n  |  P ) '/  '  F ']'") : R_scope.
Notation "\prod_ ( m <= i < n ) F" := (\big[Rmult/R1]_(m <= i < n) F)
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \prod_ ( m  <=  i  <  n ) '/  '  F ']'") : R_scope.
Notation "\prod_ ( i | P ) F" := (\big[Rmult/R1]_(i | P%B) F)
  (at level 36, F at level 36, i at level 50,
           format "'[' \prod_ ( i  |  P ) '/  '  F ']'") : R_scope.
Notation "\prod_ i F" := (\big[Rmult/R1]_i F)
  (at level 36, F at level 36, i at level 0,
  format "'[' \prod_ i '/  '  F ']'") : R_scope.
Notation "\prod_ ( i : t | P ) F" := (\big[Rmult/R1]_(i : t | P%B) F)
  (at level 36, F at level 36, i at level 50,
           only parsing) : R_scope.
Notation "\prod_ ( i : t ) F" := (\big[Rmult/R1]_(i : t) F)
  (at level 36, F at level 36, i at level 50,
           only parsing) : R_scope.
Notation "\prod_ ( i < n | P ) F" := (\big[Rmult/R1]_(i < n | P%B) F)
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \prod_ ( i  <  n  |  P ) '/  '  F ']'") : R_scope.
Notation "\prod_ ( i < n ) F" := (\big[Rmult/R1]_(i < n) F)
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \prod_ ( i  <  n ) '/  '  F ']'") : R_scope.
Notation "\prod_ ( i 'in' A | P ) F" := (\big[Rmult/R1]_(i in A | P%B) F)
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \prod_ ( i  'in'  A  |  P ) '/  '  F ']'") : R_scope.
Notation "\prod_ ( i 'in' A ) F" := (\big[Rmult/R1]_(i in A) F)
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \prod_ ( i  'in'  A ) '/  '  F ']'") : R_scope.


Notation "\rmax_ ( i <- r | P ) F" := (\big[Rmax/R0]_(i <- r | P%B) F)
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \rmax_ ( i  <-  r  |  P ) '/  '  F ']'").
Notation "\rmax_ ( i <- r ) F" :=  (\big[Rmax/R0]_(i <- r) F)
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \rmax_ ( i  <-  r ) '/  '  F ']'").
Notation "\rmax_ ( i | P ) F" := (\big[Rmax/R0]_(i | P%B) F)
  (at level 41, F at level 41, i at level 50,
           format "'[' \rmax_ ( i  |  P ) '/  '  F ']'").
Notation "\rmax_ ( i : t | P ) F" := (\big[Rmax/R0]_(i : t | P%B) F)
  (at level 41, F at level 41, i at level 50,
           only parsing).
Notation "\rmax_ ( i : t ) F" := (\big[Rmax/R0]_(i : t) F)
  (at level 41, F at level 41, i at level 50,
           only parsing).
Notation "\rmax_ ( i 'in' A | P ) F" := (\big[Rmax/R0]_(i in A | P%B) F)
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \rmax_ ( i  'in'  A  |  P ) '/  '  F ']'").
Notation "\rmax_ ( i 'in' A ) F" := (\big[Rmax/R0]_(i in A) F)
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \rmax_ ( i  'in'  A ) '/  '  F ']'").
Reserved Notation "\min^ b '_(' a 'in' A ) F" (at level 41,
  F at level 41, a, A at level 50,
   format "'[' \min^ b '_(' a  'in'  A ) '/  '  F ']'").

Declare Scope min_scope.

Local Open Scope R_scope.
Delimit Scope ring_scope with mcR.

Import Order.POrderTheory GRing.Theory Num.Theory.

(* "^" = pow : R -> nat -> R *)
Notation "x ^- n" := (/ (x ^ n)) : R_scope.

Notation "`| x |" := (Rabs x) : R_scope.

Notation "n %:R" := (INR n) : R_scope.

Global Hint Resolve Rlt_R0_R2 :  core.
Global Hint Resolve Rlt_0_1 : core.
Global Hint Resolve Rle_0_1 : core.

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

Definition ltRW {m n} : m < n -> m <= n := Rlt_le m n.

Lemma gtR_eqF a b : a < b -> b != a.
Proof. by move=> ab; apply/eqP => ba; move: ab; rewrite ba => /ltRR. Qed.

Lemma ltR_eqF (r1 r2 : R) : r1 < r2 -> r1 != r2.
Proof. by move/Rlt_not_eq/eqP. Qed.

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

Lemma ltRNge m n : (m < n) <-> ~ (n <= m).
Proof. split; [exact: Rlt_not_le | exact: Rnot_le_lt]. Qed.

Lemma leRNgt (x y : R) : (x <= y) <-> ~ (y < x).
Proof. by rewrite leRNlt. Qed.

Lemma leR_eqVlt m n : (m <= n) <-> (m = n) \/ (m < n).
Proof.
split => [|[->|]]; [ |exact: Rle_refl|exact: ltRW].
by case/Rle_lt_or_eq_dec => ?; [right|left].
Qed.

Lemma ltR_neqAle m n : (m < n) <-> (m <> n) /\ (m <= n).
Proof.
split.
  by move=> /RltP; rewrite Order.POrderTheory.lt_neqAle => /andP[/eqP ? /RleP].
move=> [/eqP mn /RleP nm].
by apply/RltP; rewrite Order.POrderTheory.lt_neqAle mn.
Qed.

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
Proof. split => [->| [] ]; by [split; exact/Rle_refl | exact: Rle_antisym]. Qed.

Lemma eqR_le_Ngt {x y} : x <= y -> ~ x < y -> y = x.
Proof. by case/leR_eqVlt. Qed.

Definition leR0n n : 0 <= n%:R := pos_INR n.

Lemma leR01 : (R0 <= R1)%R.
Proof. by []. Qed.

Lemma ltR0n n : (0 < n%:R) <-> (O < n)%nat.
Proof.
by split => [/gtR_eqF/eqP/INR_not_0/Nat.neq_0_lt_0/ltP | /ltP/lt_0_INR].
Qed.

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

Lemma leR_add2r {p m n} : m + p <= n + p <-> m <= n.
Proof. by split; [exact: Rplus_le_reg_r | exact: Rplus_le_compat_r]. Qed.

Lemma leR_add2l {p m n} : p + m <= p + n <-> m <= n.
Proof. by split; [exact: Rplus_le_reg_l | exact: Rplus_le_compat_l]. Qed.

Definition ltR_add := Rplus_lt_compat. (* r1 < r2 -> r3 < r4 -> r1 + r3 < r2 + r4 *)

Lemma ltR_add2r {p m n} : m + p < n + p <-> m < n.
Proof. by split; [exact: Rplus_lt_reg_r | exact: Rplus_lt_compat_r]. Qed.

Lemma ltR_add2l {p m n} : p + m < p + n <-> m < n.
Proof. by split; [exact: Rplus_lt_reg_l | exact: Rplus_lt_compat_l]. Qed.

Definition leR_lt_add := Rplus_le_lt_compat. (* x <= y -> z < t -> x + z < y + t *)

Lemma ltR_subRL m n p : (n < p - m) <-> (m + n < p).
Proof.
split => H.
- by move/(@ltR_add2l m) : H; rewrite subRKC.
- by apply (@ltR_add2l m); rewrite subRKC.
Qed.

Lemma ltR_subl_addr x y z : (x - y < z) <-> (x < z + y).
Proof.
split => H; [apply (@ltR_add2r (-y)) | apply (@ltR_add2r y)]; last by rewrite subRK.
by rewrite -addRA; apply: (ltR_leR_trans H); rewrite Rplus_opp_r addR0; exact/Rle_refl.
Qed.

Lemma leR_subr_addr x y z : (x <= y - z) <-> (x + z <= y).
Proof.
split => [|H].
  by move=> /RleP; rewrite RminusE lerBrDr => /RleP.
by apply/RleP; rewrite RminusE lerBrDr; exact/RleP.
Qed.

Lemma leR_subl_addr x y z : (x - y <= z) <-> (x <= z + y).
Proof.
split => [|H].
  by move=> /RleP; rewrite RminusE lerBlDr => /RleP.
by apply/RleP; rewrite RminusE lerBlDr; exact/RleP.
Qed.

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
Lemma subR_le0 x y : (y - x <= 0) <-> (y <= x).
Proof.
by split => [/leR_subl_addr|?]; [|apply/leR_subl_addr]; rewrite add0R.
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

Lemma leR_pmul2r m n1 n2 : 0 < m -> (n1 * m <= n2 * m) <-> (n1 <= n2).
Proof.
by move=> m0; split; [exact: Rmult_le_reg_r | exact/Rmult_le_compat_r/ltRW].
Qed.

Lemma ltR_pmul2l m n1 n2 : 0 < m -> (m * n1 < m * n2) <-> (n1 < n2).
Proof. by move=> m0; split; [exact: Rmult_lt_reg_l | exact/Rmult_lt_compat_l]. Qed.

Lemma ltR_pmul2r m n1 n2 : 0 < m -> (n1 * m < n2 * m) <-> (n1 < n2).
Proof. by move=> m0; split; [exact: Rmult_lt_reg_r | exact/Rmult_lt_compat_r]. Qed.

Lemma pmulR_lgt0 x y : 0 < x -> (0 < y * x) <-> (0 < y).
Proof. by move=> x0; rewrite -{1}(mul0R x) ltR_pmul2r. Qed.

Lemma pmulR_lgt0' [x y : R] :  0 < y * x -> 0 <= x -> 0 < y.
Proof.
case/boolP: (x == 0) => [/eqP -> |]; first by rewrite mulR0 => /ltRR.
move=> /eqP /nesym ? /[swap] ? /pmulR_lgt0; apply.
by rewrite ltR_neqAle; split.
Qed.

Lemma pmulR_rgt0' [x y : R] :  0 < x * y -> 0 <= x -> 0 < y.
Proof. by rewrite mulRC; exact: pmulR_lgt0'. Qed.

Arguments leR_pmul2l [_] [_] [_].
Arguments leR_pmul2r [_] [_] [_].
Arguments ltR_pmul2l [_] [_] [_].
Arguments ltR_pmul2r [_] [_] [_].
Arguments pmulR_lgt0 [_] [_].

Lemma leR_pmull m n : 1 <= n -> 0 <= m -> m <= n * m.
Proof.
move=> n1 m0; case/boolP : (m == 0) => [/eqP ->|m0']; first by rewrite mulR0; exact/Rle_refl.
by rewrite -{1}(mul1R m) leR_pmul2r // ltR_neqAle; split => //; apply/eqP; rewrite eq_sym.
Qed.

Lemma leR_pmulr m n : 1 <= n -> 0 <= m -> m <= m * n.
Proof. by move=> n1 m0; rewrite mulRC; apply leR_pmull. Qed.

Lemma leR_nat m n : (m%:R <= n%:R) <-> (m <= n)%nat.
Proof. by split => [/INR_le/leP|/leP/le_INR]. Qed.

Lemma ltR_nat m n : (m%:R < n%:R) <-> (m < n)%nat.
Proof. by split => [/INR_lt/ltP|/ltP/lt_INR]. Qed.

Lemma ltR0n_neq0' n : (0 < n)%nat = (n%:R != 0).
Proof. by rewrite lt0n INR_eq0'. Qed.

(*************)
(* invR/divR *)
(*************)

Lemma invR_gt0 x : 0 < x -> 0 < / x.
Proof. by move=> x0; apply Rinv_0_lt_compat. Qed.

Lemma invR_ge0 x : 0 < x -> 0 <= / x.
Proof. by move=> x0; apply/ltRW/invR_gt0. Qed.

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

Definition invRK (r : R) : / / r = r.
Proof. exact: Rinv_inv. Qed.

Lemma invRM (r1 r2 : R) : r1 != 0 -> r2 != 0 -> / (r1 * r2) = / r1 * / r2.
Proof. by move=> /eqP r10 /eqP r20; rewrite Rinv_mult. Qed.

Lemma leR_inv x y : 0 < y -> y <= x -> / x <= / y.
Proof. by move=> x0 y0; apply/Rinv_le_contravar. Qed.

Lemma invR_le x y : 0 < x -> 0 < y -> / y <= / x -> x <= y.
Proof.
move=> x0 y0 H; rewrite -(invRK x) -(invRK y).
by apply leR_inv => //; exact/invR_gt0.
Qed.

Lemma ltR_inv x y : 0 < x -> 0 < y -> y < x -> / x < / y.
Proof. by move=> xo y0; apply/Rinv_lt_contravar/mulR_gt0. Qed.

Lemma divRE x y : x / y = x * / y. Proof. by []. Qed.

Delimit Scope R_scope with coqR.

Lemma R1E : 1%coqR = 1%mcR. Proof. by []. Qed.
Lemma R0E : 0%coqR = 0%mcR. Proof. by []. Qed.

(* TODO: PR to Rstruct as RsqrtE *)
Lemma RsqrtE' (x : Rdefinitions.R) : sqrt x = Num.sqrt x.
Proof.
set Rx := Rcase_abs x.
have RxE: Rx = Rcase_abs x by [].
rewrite /sqrt.
rewrite -RxE.
move: RxE.
case: Rcase_abs=> x0 RxE.
  by rewrite RxE; have/RltP/ltW/ler0_sqrtr-> := x0.
rewrite /Rx -/(sqrt _) RsqrtE //.
by have/Rge_le/RleP:= x0.
Qed.

Definition coqRE :=
  (R0E, R1E, INRE, IZRposE,
    RinvE, RoppE, RdivE, RminusE, RplusE, RmultE, RpowE, RsqrtE').

Definition divRR (x : R) : x != 0 -> x / x = 1.
Proof. by move=> x0; rewrite /Rdiv Rinv_r //; exact/eqP. Qed.

Lemma divR1 (x : R) : x / 1 = x.
Proof. by rewrite /Rdiv invR1 mulR1. Qed.

Lemma div1R (x : R) : 1 / x = / x.
Proof. by rewrite /Rdiv mul1R. Qed.

Lemma div0R (x : R) : 0 / x = 0.
Proof. by rewrite /Rdiv mul0R. Qed.

Lemma divR_ge0 (x y : R) : 0 <= x -> 0 < y -> 0 <= x / y.
Proof. move=> x0 y0; apply mulR_ge0 => //; exact/invR_ge0. Qed.

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

Lemma ltR_pdivl_mulr z x y : 0 < z -> (x < y / z) <-> (x * z < y).
Proof.
move=> z0; split => [/(ltR_pmul2l z0)|H].
- by rewrite mulRC mulRCA mulRV ?mulR1 //; exact/gtR_eqF.
- by apply/(@ltR_pmul2r z) => //; rewrite -mulRA mulVR ?mulR1 //; exact/gtR_eqF.
Qed.

Lemma eqR_divr_mulr z x y : z != 0 -> (y / z = x) <-> (y = x * z).
Proof.
move=> z0; split => [<-|->]; first by rewrite -mulRA mulVR // mulR1.
by rewrite /Rdiv -mulRA mulRV // mulR1.
Qed.

Lemma eqR_divl_mulr z x y : z != 0 -> (x = y / z) <-> (x * z = y).
Proof. by move=> z0; split; move/esym/eqR_divr_mulr => /(_ z0) ->. Qed.

Lemma leR_pdivr_mulr z x y : 0 < z -> (y / z <= x) <-> (y <= x * z).
Proof.
move=> z0; split => [/(leR_wpmul2r (ltRW z0))|H].
- by rewrite -mulRA mulVR ?mulR1 //; exact/gtR_eqF.
- by apply/(@leR_pmul2r z) => //; rewrite -mulRA mulVR ?mulR1 //; exact/gtR_eqF.
Qed.

Lemma ltR_pdivr_mulr z x y : 0 < z -> (y / z < x) <-> (y < x * z).
Proof.
move=> z0; split => [/(ltR_pmul2r z0)|H].
- by rewrite -mulRA mulVR ?mulR1 //; exact/gtR_eqF.
- by apply/(@ltR_pmul2r z) => //; rewrite -mulRA mulVR ?mulR1 //; exact/gtR_eqF.
Qed.

Lemma invR_le1 x : 0 < x -> (/ x <= 1) <-> (1 <= x).
Proof. by move=> x0; rewrite -(div1R x) leR_pdivr_mulr // mul1R. Qed.

Lemma invR_gt1 x : 0 < x -> (1 < / x) <-> (x < 1).
Proof.
move=> x0; split => x1; last by rewrite -invR1; apply ltR_inv.
move/ltR_inv : x1; rewrite invRK invR1.
by apply => //; exact/invR_gt0.
Qed.

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
by rewrite -(mulR0 0); apply leR_pmul => //; apply/RleP; rewrite Order.POrderTheory.lexx.
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
move/RleP; rewrite le0r => /orP[/eqP -> _ m n|/RltP x0 x1 m n /leP nm].
  case: n => [|n nm].
    case: m => [_ |m _].
      by apply/RleP; rewrite Order.POrderTheory.lexx.
    by rewrite pow_ne_zero.
  rewrite pow_ne_zero; last by case: m nm.
  rewrite pow_ne_zero //.
  by apply/RleP; rewrite Order.POrderTheory.lexx.
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

Lemma minRE x y : min(x, y) = if (x < y)%mcR then x else y.
Proof.
by case: ifP => /RltP; [move/ltRW/Rmin_left|rewrite -leRNgt => /Rmin_right].
Qed.

Lemma maxRE x y : max(x, y) = if (x < y)%mcR then y else x.
Proof.
by case: ifP => /RltP; [move/ltRW/Rmax_right|rewrite -leRNgt => /Rmax_left].
Qed.

End ROrder.

Definition maxRA : associative Rmax := Rmax_assoc.
Definition maxRC : commutative Rmax := Rmax_comm.

Lemma maxRR : idempotent Rmax.
Proof.
move=> x; rewrite Rmax_left //.
by apply/RleP; rewrite Order.POrderTheory.lexx.
Qed.

Definition leR_maxl m n : m <= max(m, n) := Rmax_l m n.
Definition leR_maxr m n : n <= max(m, n) := Rmax_r m n.
Definition geR_minl m n : min(m, n) <= m := Rmin_l m n.
Definition geR_minr m n : min(m, n) <= n := Rmin_r m n.

Lemma leR_max x y z : max(y, z) <= x <-> (y <= x) /\ (z <= x).
Proof.
split => [| [yx zx] ].
  move/RleP.
  rewrite Order.POrderTheory.le_eqVlt => /orP[/eqP <-|/RltP/Rmax_Rlt].
    by split; [exact: leR_maxl | exact: leR_maxr].
  by case=> ?; split; exact/ltRW.
by rewrite -(Rmax_right _ _ yx); exact: Rle_max_compat_l.
Qed.

(* NB: the following used to be in Rbigop.v *)

Lemma iter_mulR x (n : nat) : ssrnat.iter n (Rmult x) 1 = x ^ n.
Proof. elim : n => // n Hn ; by rewrite iterS Hn. Qed.

Lemma iter_addR x (n : nat) : ssrnat.iter n (Rplus x) 0 = n%:R * x.
Proof. by rewrite iter_addr addr0 -mulr_natr mulrC RmultE INRE. Qed.

Section temporary_lemmas.

Local Open Scope ring_scope.

Lemma sumRE (I : Type) (r : seq I) (P : pred I) (F : I -> R) :
  (\sum_(i <- r | P i) F i)%coqR = \sum_(i <- r | P i) F i.
Proof. by []. Qed.

Lemma bigmaxRE (I : Type) (r : seq I) (P : pred I) (F : I -> R) :
  \rmax_(i <- r | P i) F i = \big[Order.max/0]_(i <- r | P i) F i.
Proof.
rewrite /Rmax /Order.max/=.
congr bigop.body.
apply: boolp.funext=> i /=.
congr BigBody.
apply: boolp.funext=> x /=.
apply: boolp.funext=> y /=.
rewrite lt_neqAle.
case: (Rle_dec x y); move/RleP;
  first by case/boolP: (x == y) => /= [/eqP -> | _ ->].
by move/negPf->; rewrite andbF.
Qed.

End temporary_lemmas.

Lemma morph_oppR : {morph [eta Ropp] : x y / x + y}.
Proof. by move=> x y /=; field. Qed.

Definition big_morph_oppR := big_morph _ morph_oppR oppR0.

Lemma morph_natRD : {morph INR : x y / (x + y)%nat >-> x + y}.
Proof. move=> x y /=; by rewrite natRD. Qed.

Definition big_morph_natRD := big_morph INR morph_natRD (erefl 0%:R).

Lemma morph_natRM : {morph INR : x y / (x * y)%nat >-> x * y}.
Proof. move=> x y /=; by rewrite natRM. Qed.

Definition big_morph_natRM := big_morph INR morph_natRM (erefl 1%:R).

Lemma morph_mulRDr a : {morph [eta Rmult a] : x y / x + y}.
Proof. move=> * /=; by rewrite mulRDr. Qed.

Lemma morph_mulRDl a : {morph Rmult^~ a : x y / x + y}.
Proof. move=> x y /=; by rewrite mulRDl. Qed.

Lemma iter_Rmax a b (Hb : b <= a) k : ssrnat.iter k (Rmax b) a = a.
Proof. elim: k => // k Hk; by rewrite iterS Hk Rmax_right. Qed.

(** Rle, Rlt lemmas for big sums of reals *)

Lemma sumR_ord_setT (n : nat) (f : 'I_n -> R) :
  \sum_(i < n) f i = \sum_(i in [set: 'I_n]) f i.
Proof. by apply eq_bigl => i; rewrite inE. Qed.

Lemma sumR_neq0 (U : eqType) (P : U -> R) (s : seq.seq U) :
  (forall i, 0 <= P i) ->
  \sum_(a0 <- s) P a0 != 0 <-> exists i : U, i \in s /\ 0 < P i.
Proof.
move=> /(_ _) /RleP P0.
rewrite sumRE psumr_neq0 //.
under eq_has do rewrite andTb.
split; first by  move=> /hasP [x xs /RltP Px0]; exists x; split.
by case=> x [] xs /RltP Px0; apply/hasP; exists x.
Qed.

Lemma sumR_gt0 (A : finType) (f : A -> R) (HA : (0 < #|A|)%nat) :
  (forall a, 0 < f a) -> 0 < \sum_(a in A) f a.
Proof.
move=> f0; rewrite ltR_neqAle; split; last first.
  apply/RleP; rewrite sumRE.
  by apply/sumr_ge0 => a _; apply/RleP/ltRW.
apply/nesym/eqP/sumR_neq0; last by move/card_gt0P : HA => [a _]; exists a.
by move=> a; apply/ltRW/f0.
Qed.

Section leR_ltR_sumR.
Variable A : Type.
Implicit Types (f g : A -> R) (P Q : pred A).

Lemma leR_sumR r P f g : (forall i, P i -> f i <= g i) ->
  \sum_(i <- r | P i) f i <= \sum_(i <- r | P i) g i.
Proof.
move=> leE12.
elim/big_ind2: _ => //.
  exact: Rle_refl.
by move=> m1 m2 n1 n2; Lra.lra.
Qed.

End leR_ltR_sumR.

Section leR_ltR_sumR_finType.
Variables (A : finType) (f g : A -> R) (P Q : pred A).

Lemma leR_sumR_support (X : {set A}) :
  (forall i, i \in X -> P i -> f i <= g i) ->
  \sum_(i in X | P i) f i <= \sum_(i in X | P i) g i.
Proof.
move=> H; elim/big_rec2 : _ => //.
  exact: Rle_refl.
move=> a x y /andP[aX Pa] yx.
by apply leR_add => //; apply: H.
Qed.

Lemma leR_sumRl : (forall i, P i -> f i <= g i) ->
  (forall i, Q i -> 0 <= g i) -> (forall i, P i -> Q i) ->
  \sum_(i | P i) f i <= \sum_(i | Q i) g i.
Proof.
move=> f_g Qg H; elim: (index_enum _) => [| h t IH].
- rewrite !big_nil.
  by apply/RleP; rewrite lexx.
- rewrite !big_cons /=; case: ifP => [Ph|Ph].
    by rewrite (H _ Ph); apply leR_add => //; exact: f_g.
  case: ifP => // Qh; apply: (leR_trans IH).
  by rewrite -{1}[X in X <= _](add0R _); exact/leR_add2r/Qg.
Qed.

Lemma leR_sumRl_support (U : pred A) :
  (forall a, 0 <= f a) -> (forall i, P i -> Q i) ->
  \sum_(i in U | P i) f i <= \sum_(i in U | Q i) f i.
Proof.
move=> Hf P_Q; elim: (index_enum _) => [|h t IH].
- by rewrite !big_nil; apply/RleP; rewrite lexx.
- rewrite !big_cons; case: (h \in U) => //=; case: ifP => // Ph.
  + by case: ifP => [Qh|]; [rewrite leR_add2l | rewrite (P_Q _ Ph)].
  + by case: ifP => // Qh; rewrite -[X in X <= _]add0R; exact/leR_add.
Qed.

Lemma ltR_sumR_support (X : {set A}) : (0 < #|X|)%nat ->
  (forall i, i \in X -> f i < g i) ->
  \sum_(i in X) f i < \sum_(i in X) g i.
Proof.
move Hn : #|X| => n; elim: n X Hn => // n IH X Hn _ H.
move: (ltn0Sn n); rewrite -Hn card_gt0; case/set0Pn => a0 Ha0.
rewrite (@big_setD1 _ _ _ _ a0 _ f) //= (@big_setD1 _ _ _ _ a0 _ g) //=.
case: n => [|n] in IH Hn.
  rewrite (_ : X :\ a0 = set0); first by rewrite !big_set0 2!addR0; exact: H.
  move: Hn.
  by rewrite (cardsD1 a0) Ha0 /= add1n => -[] /eqP; rewrite cards_eq0 => /eqP.
apply ltR_add; first exact/H.
apply IH => //.
- by move: Hn; rewrite (cardsD1 a0) Ha0 /= add1n => -[].
- by move=> a; rewrite in_setD inE => /andP[_ ?]; exact: H.
Qed.

Lemma ltR_sumR : (O < #|A|)%nat -> (forall i, f i < g i) ->
  \sum_(i in A) f i < \sum_(i in A) g i.
Proof.
move=> A0 H0.
have : forall i : A, i \in [set: A] -> f i < g i by move=> a _; exact/H0.
move/ltR_sumR_support; rewrite cardsT => /(_ A0).
rewrite big_mkcond /= [in X in _ < X]big_mkcond /=.
rewrite (eq_bigr f) //; last by move=> *; rewrite inE.
by rewrite [in X in _ < X](eq_bigr g) // => *; rewrite inE.
Qed.

End leR_ltR_sumR_finType.

Lemma leR_sumR_Rabs (A : finType) f : `| \sum_a f a | <= \sum_(a : A) `| f a |.
Proof.
elim: (index_enum _) => [|h t IH].
  by rewrite 2!big_nil Rabs_R0; exact: Rle_refl.
rewrite 2!big_cons.
apply (@leR_trans (`| f h | + `| \sum_(j <- t) f j |));
  [exact/Rabs_triang |exact/leR_add2l].
Qed.

Lemma leR_sumR_predU (A : finType) (f : A -> R) (P Q : pred A) :
  (forall a, 0 <= f a) -> \sum_(i in A | [predU P & Q] i) f i <=
  \sum_(i in A | P i) f i + \sum_(i in A | Q i) f i.
Proof.
move=> Hf.
elim: (index_enum _) => [|h t IH /=]; first by rewrite !big_nil /=; Lra.lra.
rewrite !big_cons /=.
case: ifPn => /=.
- case/orP => [hP | hQ].
  + move: hP; rewrite unfold_in => ->.
    case: ifP => // Qh.
    * rewrite -addRA; apply leR_add2l.
      apply (leR_trans IH).
      have : forall a b c, 0 <= c -> a + b <= a + (c + b) by move=> *; Lra.lra.
      apply; by apply Hf.
    * rewrite -addRA; apply leR_add2l.
      exact/(leR_trans IH)/Req_le.
  + move: hQ; rewrite unfold_in => ->.
    case: ifP => // Ph.
    * rewrite -addRA; apply/leR_add2l/(leR_trans IH).
      have : forall a b c, 0 <= c -> a + b <= a + (c + b) by move=> *; Lra.lra.
      apply; by apply Hf.
    * rewrite -(addRC (f h + _)) -addRA; apply/leR_add2l/(leR_trans IH).
      by rewrite addRC; apply Req_le.
- rewrite negb_or.
  case/andP.
  rewrite !unfold_in; move/negbTE => -> /negbTE ->.
  exact/IH.
Qed.

(* TODO: factorize? rename? *)
Lemma leR_sumR_eq (A : finType) (f g : A -> R) (P : pred A) :
   (forall a, P a -> f a <= g a) ->
   \sum_(a | P a) g a = \sum_(a | P a) f a ->
   (forall a, P a -> g a = f a).
Proof.
move=> H1 H2 i Hi; rewrite -subR_eq0; move: i Hi; apply: psumr_eq0P.
  by move=> i Pi; rewrite RminusE subr_ge0; apply/RleP/H1.
by rewrite big_split/= -big_morph_oppR; apply/eqP; rewrite subr_eq0 H2.
Qed.

Section pascal.

Lemma factE n0 : fact n0 = n0 `!.
Proof. by elim: n0 => // n0 IH /=; rewrite IH factS mulSn -multE. Qed.

Lemma combinaisonE n0 m0 : (m0 <= n0)%nat -> C n0 m0 = 'C(n0, m0)%:R.
Proof.
move=> ?.
rewrite /C.
apply (@eqR_mul2r (INR (fact m0) * INR (fact (n0 - m0)%coq_nat))).
  move/eqP; rewrite mulR_eq0' !INR_eq0' => /orP[|] /eqP; exact/fact_neq_0.
set tmp := INR (fact m0) * _.
rewrite -mulRA mulVR ?mulR1; last first.
  by rewrite /tmp mulR_neq0' !INR_eq0' !factE -!lt0n !fact_gt0.
by rewrite /tmp -!natRM !factE !minusE bin_fact.
Qed.

Lemma sum_f_R0_sumR : forall n (f : nat -> R),
  sum_f_R0 f n = \sum_(i < n.+1) f i.
Proof.
elim => [f|n IH f] /=; first by rewrite big_ord_recl /= big_ord0 addR0.
by rewrite big_ord_recr /= IH.
Qed.

Theorem RPascal k (a b : R) :
  (a + b) ^ k = \sum_(i < k.+1) INR ('C(k, i))* (a ^ (k - i) * b ^ i).
Proof.
rewrite addRC Binomial.binomial sum_f_R0_sumR.
apply eq_bigr => i _.
rewrite combinaisonE; last by rewrite -ltnS.
rewrite -minusE; field.
Qed.

End pascal.

Section leR_ltR_rprod.

Lemma prodR_ge0 (A : finType) F : (forall a, 0 <= F a) ->
  0 <= \prod_(a : A) F a.
Proof. by move=> F0; elim/big_ind : _ => // x y ? ?; exact: mulR_ge0. Qed.

Lemma prodR_eq0 (A : finType) (p : pred A) (F : A -> R) :
  (exists2 i : A, p i & F i = 0%R) <-> \prod_(i : A | p i) F i = 0%R.
Proof.
split.
{ by case => [i Hi Hi0]; rewrite (bigD1 i) //= Hi0 mul0R. }
apply big_ind.
- by move=> K; exfalso; auto with real.
- by move=> ? ? ? ?; rewrite mulR_eq0 => -[]; tauto.
- by move=> i Hi Hi0; exists i.
Qed.

Lemma prodR_ge1 (A : finType) f : (forall a, 1 <= f a) ->
  1 <= \prod_(a : A) f a.
Proof.
elim/big_ind : _ => // [|x y Hx Hy *].
  by move=> _; apply/RleP; rewrite lexx.
by rewrite -{1}(mulR1 1); apply/leR_pmul => //; [exact: Hx | exact: Hy].
Qed.

Lemma prodR_constE (x0 : R) (k : nat) : \prod_(i < k) x0 = x0 ^ k.
Proof. by rewrite big_const cardT size_enum_ord iter_mulR. Qed.

Lemma prodR_card_constE (I : finType) (B : pred I) x0 : \prod_(i in B) x0 = x0 ^ #|B|.
Proof. by rewrite big_const iter_mulR. Qed.

Lemma prodRN (I : finType) (p : pred I) (F : I -> R) :
  \prod_(i in p) - F i = (-1) ^ #|p| * \prod_(i in p) F i.
Proof.
rewrite -prodR_card_constE.
apply: (big_rec3 (fun a b c => a = b * c)).
{ by rewrite mul1R. }
move=> i a b c Hi Habc; rewrite Habc; ring.
Qed.

Lemma leR_prodR (A : finType) f g : (forall a, 0 <= f a <= g a) ->
  \prod_a f a <= \prod_(a : A) g a.
Proof.
move=> fg.
have [/forallP Hf|] := boolP [forall i, f i != 0%R]; last first.
  rewrite negb_forall => /existsP[i0 /negPn/eqP fi0].
  rewrite (bigD1 i0) //= fi0 mul0R; apply prodR_ge0.
  by move=> i ; move: (fg i) => [Hi1 Hi2]; exact: (leR_trans Hi1 Hi2).
have Hprodf : 0 < \prod_(i : A) f i.
  apply/RltP. apply prodr_gt0 => a _. apply/RltP.
  move: (Hf a) (fg a) => {}Hf {fg}[Hf2 _].
  by apply/RltP; rewrite lt0r Hf/=; exact/RleP.
apply (@leR_pmul2r (1 * / \prod_(i : A) f i) _ _).
  apply divR_gt0 => //; lra.
rewrite mul1R mulRV; last exact/gtR_eqF.
set inv_spec := fun r => if r == 0 then 0 else / r.
rewrite (_ : / (\prod_(a : A) f a) = inv_spec (\prod_(a : A) f a)); last first.
  rewrite /inv_spec (_ : \prod_(a : A) f a == 0 = false) //.
  exact/negbTE/gtR_eqF.
rewrite (@big_morph _ _ (inv_spec) R1 Rmult R1 Rmult _); last 2 first.
  - move=> a b /=.
    case/boolP : ((a != 0) && (b != 0)).
    + move=> /andP [/negbTE Ha /negbTE Hb]; rewrite /inv_spec Ha Hb.
      move/negbT in Ha ; move/negbT in Hb.
      have -> : (a * b)%R == 0 = false by rewrite mulR_eq0' (negbTE Ha) (negbTE Hb).
      by rewrite invRM //; exact/eqP.
    + rewrite negb_and !negbK => /orP[|]/eqP ->;
      by rewrite /inv_spec !(eqxx,mul0R,mulR0).
  - by rewrite /inv_spec ifF ?invR1 //; exact/negbTE/eqP/R1_neq_R0.
rewrite -big_split /=; apply prodR_ge1 => a.
move/(_ a) in Hf.
move: fg => /(_ a) [Hf2 fg].
rewrite /inv_spec.
move/negbTE in Hf; rewrite Hf; move/negbT in Hf.
rewrite -(mulRV (f a)) //.
apply leR_wpmul2r => //.
rewrite -(mul1R (/ f a)).
by apply divR_ge0; [Lra.lra |by apply/RltP; rewrite lt0r Hf; exact/RleP].
Qed.

End leR_ltR_rprod.

Section bigmaxR.

Variables (A : eqType) (F : A -> R) (s : seq A).

Lemma leR_bigmaxR : forall m, m \in s -> F m <= \rmax_(m <- s) (F m).
Proof.
elim: s => // hd tl IH m; rewrite in_cons; case/orP.
- move/eqP => ->; rewrite big_cons; exact/leR_maxl.
- move/IH => H; rewrite big_cons; exact/(leR_trans H)/leR_maxr.
Qed.

Lemma bigmaxR_ge0 : (forall r, r \in s -> 0 <= F r) -> 0 <= \rmax_(m <- s) (F m).
Proof.
(* TODO: generalize Order.TotalTheory.bigmax_sup to seq? *)
case: s => [_ | hd tl Hr].
- by rewrite big_nil; exact/Rle_refl.
- apply (@leR_trans (F hd)); last by rewrite big_cons; exact: leR_maxl.
  by apply: Hr; rewrite in_cons eqxx.
Qed.

End bigmaxR.

Lemma bigmaxR_undup (I : eqType) g : forall (s : seq I),
   \rmax_(c <- s) g c = \rmax_(c <- undup s) g c.
Proof.
elim=> // hd tl IH /=.
rewrite big_cons.
case: ifP => Hcase.
- rewrite -IH Rmax_right //; exact: leR_bigmaxR.
- by rewrite big_cons IH.
Qed.

Lemma bigmaxR_cat (I : eqType) g : forall (s1 s2 : seq I),
  (forall x, x \in s1 ++ s2 -> 0 <= g x) ->
  \rmax_(c <- s1 ++ s2) g c = Rmax (\rmax_(c <- s1) g c) (\rmax_(c <- s2) g c).
Proof.
elim => [s2 Hg /= | h1 t1 IH s2 Hg /=].
  by rewrite big_nil Rmax_right //; exact: bigmaxR_ge0.
rewrite 2!big_cons IH ?maxRA // => x Hx; apply: Hg.
by rewrite /= in_cons Hx orbC.
Qed.

Lemma bigmaxR_perm (I : eqType) g : forall (s1 s2 : seq I),
  (forall r, r \in s2 -> 0 <= g r) ->
  perm_eq s1 s2 -> uniq s1 -> uniq s2 ->
  \rmax_(c0 <- s1) g c0 = \rmax_(c0 <- s2) g c0.
Proof.
(* used perm_big ?*)
move=> s1.
move H : (size s1) => n1.
elim: n1 s1 H => //.
  case=> // _ s _ Hs.
  suff -> : s = [::].
    move=> _ _; by rewrite !big_nil.
  destruct s => //.
  move/allP : Hs.
  move/(_ s).
  by rewrite /= inE eqxx /= => /(_ Logic.eq_refl) /= add1n.
move=> n1 IH1 [|h1 t1] // [] H1 s2 Hg Hs2 K1 K2.
rewrite big_cons.
have [h2 [t2 ht2]] : exists h2 t2, s2 = h2 ++ h1 :: t2.
  have /path.splitPr[h2 t2] : h1 \in s2 by rewrite -(perm_mem Hs2) in_cons eqxx.
  by exists h2, t2.
have Hs2' : perm_eq t1 (h2 ++ t2).
  rewrite ht2 in Hs2.
  rewrite -(perm_cons h1).
  eapply perm_trans; first by apply Hs2.
  by rewrite perm_catC /= perm_cons perm_catC.
have Hg' r : r \in h2 ++ t2 -> 0 <= g r.
  move=> rs2; apply Hg.
  rewrite ht2 mem_cat in_cons.
  rewrite mem_cat in rs2.
  case/orP : rs2 => [-> // | -> /=].
  by rewrite orbA orbC.
rewrite (IH1 _ H1 _ Hg' Hs2'); last 2 first.
  by case/andP : K1.
  rewrite ht2 cat_uniq /= in K2.
  case/andP : K2 => K2 /andP [] K4 /andP [] _ K3.
  rewrite cat_uniq K2 K3 /= andbC /=.
  rewrite negb_or in K4.
  by case/andP : K4.
rewrite bigmaxR_cat // maxRA (maxRC (g h1)) -maxRA ht2 bigmaxR_cat; last first.
  move=> x Hx; apply Hg; by rewrite ht2.
by rewrite big_cons.
Qed.

Lemma bigmaxR_eqi (I : finType) g (s1 s2 : seq I) :
  (forall r : I, r \in s1 -> 0 <= g r) -> s1 =i s2 ->
  \rmax_(c0 <- s1) g c0 = \rmax_(c0 <- s2) g c0.
Proof.
move=> Hg s1s2.
rewrite (bigmaxR_undup _ _ s1) (bigmaxR_undup _ g s2).
apply bigmaxR_perm; [ | | by rewrite undup_uniq | by rewrite undup_uniq].
- move=> r Hr; apply Hg.
  rewrite mem_undup in Hr.
  by rewrite s1s2.
- apply uniq_perm; [by rewrite undup_uniq | by rewrite undup_uniq | ].
  move=> i; by rewrite !mem_undup.
Qed.

Lemma bigmaxR_imset_helper (M I : finType) h (g : I -> R) (s : seq M) :
  (forall r : I, r \in enum [set h x | x in s] -> 0 <= g r) ->
  \rmax_(c0 <- enum [set h x | x in s]) g c0 = \rmax_(m <- s) g (h m).
Proof.
elim: s => [|hd tl IH Hg /=].
  rewrite big_nil.
  set tmp := enum _.
  suff -> : tmp = [::] by rewrite big_nil.
  rewrite /tmp -[in X in _ = X]enum0.
  apply eq_enum => a.
  rewrite !inE.
  apply/imsetP. case => m.
  by rewrite in_nil.
rewrite big_cons -IH; last first.
  move=> r Hr.
  apply Hg.
  rewrite mem_enum.
  apply/imsetP.
  rewrite mem_enum in Hr.
  case/imsetP : Hr => x xtl Hr.
  exists x => //.
  by rewrite in_cons xtl orbC.
transitivity (\rmax_(c0 <- h hd :: enum [set h x | x in tl]) g c0).
apply bigmaxR_eqi => // x.
rewrite inE !mem_enum.
move Hlhs : (x \in [set _ _ | _ in _]) => lhs.
destruct lhs.
  - case/imsetP : Hlhs => x0 Hx0 H.
    rewrite in_cons in Hx0.
    case/orP : Hx0 => Hx0.
      move/eqP : Hx0 => ?; subst x0.
      by rewrite H eqxx.
    symmetry.
    apply/orP; right.
    apply/imsetP; by exists x0.
  - symmetry.
    apply/negbTE.
    move/negbT : Hlhs.
    apply contra.
    case/orP => Hcase.
    + move/eqP in Hcase; subst x.
      apply/imsetP.
      exists hd => //.
      by rewrite inE eqxx.
    + apply/imsetP.
      case/imsetP : Hcase => x0 Hx0 ?; subst x.
      exists x0 => //.
      by rewrite inE Hx0 orbC.
by rewrite big_cons.
Qed.

Lemma bigmaxR_imset (M I : finType) h (g : I -> R) :
  (forall r : I, r \in [set h x | x in M] -> 0 <= g r) ->
  \rmax_(c0 in [set h x | x in M]) g c0 = \rmax_(m in M) g (h m).
Proof.
move=> Hg.
eapply trans_eq.
  eapply trans_eq; last first.
    apply (@bigmaxR_imset_helper _ I h g (enum M)).
    move=> r; rewrite mem_enum; case/imsetP => x; rewrite mem_enum => Hx ->.
    apply Hg; apply/imsetP; by exists x.
  rewrite big_filter /=.
  apply congr_big => //.
  move=> i /=.
  move Hlhs : (i \in _) => lhs.
  destruct lhs.
  - case/imsetP : Hlhs => x Hx ?; subst i.
    symmetry; apply/imsetP.
    exists x => //.
    by rewrite mem_enum.
  - symmetry.
    apply/negbTE.
    move/negbT : Hlhs; apply contra.
    case/imsetP => m Hm ?; subst i.
    apply/imsetP.
    by exists m.
apply congr_big => //; by rewrite enumT.
Qed.

Lemma leR_bigmaxRl (A : finType) (f : A -> R) (s : seq A) a :
  (forall a0, 0 <= f a0) ->
  (forall a0, a0 \in s -> f a0 <= f a) ->
  \rmax_(a0 <- s) f a0 <= f a.
Proof.
elim: s a => [a f0 _ | a0 s' IH a f0 Hf].
  rewrite big_nil; exact/f0.
rewrite big_cons; apply Rmax_lub.
- by apply Hf; rewrite mem_head.
- apply IH => // a1 a1s; apply Hf.
  by rewrite in_cons a1s orbC.
Qed.

Lemma bigmaxR_seq_eq (A : finType) (f : A -> R) (s : seq A) a :
  a \in s ->
  (forall a0, 0 <= f a0) ->
  (forall a0, a0 \in s -> f a0 <= f a) ->
  f a = \rmax_(a0 <- s) f a0.
Proof.
elim: s a => // hd tl IH a; rewrite in_cons; case/orP.
- move/eqP => -> Hhpos Hh.
  rewrite big_cons.
  rewrite Rmax_left //.
  apply leR_bigmaxRl => //.
  move=> c0 Hc0; apply Hh.
  by rewrite in_cons Hc0 orbC.
- move=> atl Hhpos Hh.
  rewrite big_cons Rmax_right //.
  + apply IH => //.
    move=> c0 Hc0; apply Hh.
    by rewrite in_cons Hc0 orbC.
  + rewrite -(IH a) //.
    * apply Hh.
      by rewrite in_cons eqxx.
    * move=> c0 Hc0.
      apply Hh.
      by rewrite in_cons Hc0 orbC.
Qed.

Lemma bigmaxR_eq (A : finType) (C : {set A}) a (f : A -> R):
  a \in C ->
  (forall a0, 0 <= f a0) ->
  (forall c, c \in C -> f c <= f a) ->
  f a = \rmax_(c | c \in C) f c.
Proof.
move=> aC f0 Hf.
rewrite -big_filter.
apply bigmaxR_seq_eq => //.
- by rewrite mem_filter aC /= mem_index_enum.
- by move=> a0; rewrite mem_filter mem_index_enum andbT => /Hf.
Qed.

Local Open Scope R_scope.

Lemma bigmaxR_distrr I a (a0 : 0 <= a) r (P : pred I) F :
  (a * \rmax_(i <- r | P i) F i) = \rmax_(i <- r | P i) (a * F i).
Proof.
elim: r => [| h t IH].
  by rewrite 2!big_nil mulR0.
rewrite 2!big_cons.
case: ifP => Qh //.
by rewrite -IH RmaxRmult.
Qed.

Lemma bigmaxR_distrl I a (a0 : 0 <= a) r (P : pred I) F :
  (\rmax_(i <- r | P i) F i) * a = \rmax_(i <- r | P i) (F i * a).
Proof.
by rewrite mulRC bigmaxR_distrr //; apply congr_big => // ?; rewrite mulRC.
Qed.

Notation "\min^ b '_(' a 'in' A ) F" :=
  ((fun a => F) (arg_min b (fun x => x \in A) (fun a => F))) : min_scope.

Local Open Scope min_scope.

Lemma leq_bigmin (A : finType) (C : {set A}) (cnot0 : {c0 | c0 \in C})
  a (Ha : a \in C) (h : A -> nat) :
  (\min^ (sval cnot0) _(c in C) h c <= h a)%nat.
Proof. by case: arg_minnP; [case: cnot0|move=> a0 a0C; exact]. Qed.

Lemma bigmaxR_bigmin_helper (A : finType) n (g : nat -> R) :
  (forall n1 n2, (n1 <= n2 <= n)%nat -> (g n2 <= g n1)%R) ->
  (forall r, 0 <= g r) ->
  forall (C : {set n.-tuple A}) c (_ : c \in C) (d : n.-tuple A -> nat)
  (_ : forall c, c \in C -> (d c <= n)%nat)
  (cnot0 : {c0 | c0 \in C}),
  d c = \min^ (sval cnot0) _(c in C) d c ->
  g (d c) = \rmax_(c in C) g (d c).
Proof.
move=> Hdecr Hr C c cC d Hd cnot0 H.
apply (@bigmaxR_eq _ C c (fun a => g (d a))) => //.
move=> /= c0 c0C.
apply/Hdecr/andP; split; [|exact: Hd].
rewrite H; exact: leq_bigmin.
Qed.

(* TODO: useful for? *)
Lemma bigmaxR_bigmin (A M : finType) n (f : {ffun M -> n.-tuple A}) (g : nat -> R)
  (cnot0 : {c0 | c0 \in f @: M } ) :
  (forall n1 n2, (n1 <= n2 <= n)%nat -> (g n2 <= g n1)%R) ->
  (forall r, 0 <= g r) ->
  forall m (d : n.-tuple A -> nat)
  (_ : forall c0 : n.-tuple A, c0 \in [set f x | x : M] -> (d c0 <= n)%nat),
  d (f m) = \min^ (sval cnot0) _(c in [set f x | x in M]) d c ->
  g (d (f m)) = \rmax_(m | m \in M) g (d (f m)).
Proof.
move=> n1n2 Hg m d H Hd.
transitivity (\rmax_(c in [set f x | x in M]) g (d c)); last by rewrite bigmaxR_imset.
apply bigmaxR_bigmin_helper with cnot0 => //.
apply/imsetP; by exists m.
Qed.

From mathcomp Require Import matrix.

Lemma bigmaxR_bigmin_vec_helper (A : finType) n (g : nat -> R) :
  (forall n1 n2, (n1 <= n2 <= n)%nat -> (g n2 <= g n1)%R) ->
  (forall r, 0 <= g r) ->
  forall (C : {set 'rV[A]_n}) c (_ : c \in C) (d : 'rV[A]_n -> nat)
  (_ : forall c, c \in C -> (d c <= n)%nat)
  (cnot0 : {c0 | c0 \in C}),
  d c = \min^ (sval cnot0) _(c in C) d c ->
  g (d c) = \rmax_(c in C) g (d c).
Proof.
move=> Hdecr Hr C c cC d Hd cnot0 H.
apply (@bigmaxR_eq _ C c (fun a => g (d a))) => //.
move=> /= c0 c0C.
apply/Hdecr/andP; split; [|exact: Hd].
rewrite H; exact: leq_bigmin.
Qed.

Lemma bigmaxR_bigmin_vec (A M : finType) n (f : {ffun M -> 'rV[A]_n}) (g : nat -> R)
  (cnot0 : {c0 | c0 \in f @: M } ) :
  (forall n1 n2, (n1 <= n2 <= n)%nat -> (g n2 <= g n1)%R) ->
  (forall r, 0 <= g r) ->
  forall m (d : 'rV[A]_n -> nat)
  (_ : forall c0 : 'rV[A]_n, c0 \in f @: M -> (d c0 <= n)%nat),
  d (f m) = \min^ (sval cnot0) _(c in f @: M) d c ->
  g (d (f m)) = \rmax_(m in M) g (d (f m)).
Proof.
move=> n1n2 Hg m d H Hd.
transitivity (\rmax_(c in f @: M) g (d c)); last by rewrite bigmaxR_imset.
apply bigmaxR_bigmin_vec_helper with cnot0 => //.
by apply/imsetP; exists m.
Qed.
