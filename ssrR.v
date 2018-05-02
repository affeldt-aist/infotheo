(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import Reals.

(** * SSReflect-like lemmas for Coq Reals *)

Reserved Notation "a '>b=' b" (at level 70).
Reserved Notation "a '<b=' b" (at level 70).
Reserved Notation "a '<b' b" (at level 70).
Reserved Notation "a '>b' b" (at level 70).
Reserved Notation "a '<b=' b '<b=' c" (at level 70, b at next level).
Reserved Notation "a '<b' b '<b' c" (at level 70, b at next level).

Local Open Scope R_scope.

(* "^" = pow : R -> nat -> R *)
Notation "x ^- n" := (/ (x ^ n)) : R_scope.

Notation "`| x |" := (Rabs x).

Hint Resolve Rlt_R0_R2.
Hint Resolve Rlt_0_1.
Hint Resolve Rle_0_1.

(** eqType for Coq Reals *)
Definition Req_bool (a b : R) : bool :=
  match Req_EM_T a b with left _ => true | _ => false end.

Lemma eqRP : Equality.axiom Req_bool.
Proof. move=> a b; apply: (iffP idP); rewrite /Req_bool; by case: Req_EM_T. Qed.

Canonical R_eqMixin := EqMixin eqRP.
Canonical R_eqType := Eval hnf in EqType R R_eqMixin.

Definition leR_bool a b := if Rle_dec a b is left _ then true else false.
Notation "a '<b=' b" := (leR_bool a b) : R_scope.

Definition geR_bool (a b : R) := leR_bool b a.
Notation "a '>b=' b" := (geR_bool a b) : R_scope.

Definition ltR_bool (a b : R) := if Rlt_dec a b is left _ then true else false.
Notation "a '<b' b" := (ltR_bool a b) : R_scope.

Definition gtR_bool a b := b <b a.
Notation "a '>b' b" := (gtR_bool a b) : R_scope.

Notation "a '<b=' b '<b=' c" := (leR_bool a b && leR_bool b c) : R_scope.
Notation "a '<b' b '<b' c" := (ltR_bool a b && ltR_bool b c) : R_scope.

Lemma leRP (a b : R) : reflect (a <= b) (a <b= b).
Proof. by apply: (iffP idP); rewrite /leR_bool; case: Rle_dec. Qed.

Lemma ltRP (a b : R) : reflect (a < b) (a <b b).
Proof. apply: (iffP idP); by rewrite /ltR_bool; case: Rlt_dec. Qed.

Definition add0R : left_id 0 Rplus := Rplus_0_l.
Definition addR0 : right_id 0 Rplus := Rplus_0_r.

Lemma addRC : commutative Rplus.
Proof. move=> m n; by rewrite Rplus_comm. Qed.

Lemma addRA : associative Rplus.
Proof. move=> m n p; by rewrite Rplus_assoc. Qed.

Lemma addRCA : left_commutative Rplus.
Proof. move=> a b c; by field. Qed.

Lemma addRAC : right_commutative Rplus.
Proof. move=> a b c; by field. Qed.

Lemma addRK (a : R) : cancel (Rplus^~ a) (Rminus^~ a).
Proof. move=> b; by field. Qed.

Definition subR0 : right_id 0 Rminus := Rminus_0_r.
Lemma subRR a : a - a = 0. Proof. by rewrite Rminus_diag_eq. Qed.

Lemma subRKC m n : m + (n - m) = n. Proof. ring. Qed.

Lemma subRK m n : n - m + m = n. Proof. ring. Qed.

Lemma subR_eq0 (x y : R) : (x - y == 0) = (x == y).
Proof.
apply/idP/idP => [|/eqP ->]; last by rewrite subRR.
by move/eqP/Rminus_diag_uniq => ->.
Qed.

Lemma subR_eq x y z : (x - z == y) = (x == y + z).
Proof.
apply/idP/idP => [/eqP <-|/eqP ->]; by [rewrite subRK | rewrite addRK].
Qed.

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
Proof. move=> m n p; by rewrite Rmult_assoc. Qed.

Lemma mulRCA : left_commutative Rmult. Proof. move=> a b c; by field. Qed.

Lemma mulRDl : left_distributive Rmult Rplus.
Proof. move=> *; by rewrite Rmult_plus_distr_r. Qed.
Lemma mulRDr : right_distributive Rmult Rplus.
Proof. move=> *; by rewrite Rmult_plus_distr_l. Qed.
Lemma mulRBl : left_distributive Rmult Rminus.
Proof. move=> *; field. Qed.

Lemma mulR_eq0 (x y : R) : (x * y == 0) = ((x == 0) || (y == 0)).
Proof.
apply/idP/idP => [/eqP/Rmult_integral[] ->| ]; try by rewrite eqxx // orbC.
case/orP => /eqP ->; by rewrite ?mulR0 ?mul0R.
Qed.

Lemma eqR_mul2l {r r1 r2} : r <> 0 -> (r * r1 = r * r2) <-> (r1 = r2).
Proof. by move=> r0; split => [/Rmult_eq_reg_l/(_ r0) | ->]. Qed.

Lemma eqR_mul2r {r r1 r2} : r <> 0 -> (r1 * r = r2 * r) <-> (r1 = r2).
Proof. by move=> r0; split => [/Rmult_eq_reg_r/(_ r0)|->]. Qed.

Lemma gtR_eqF a b : a < b -> b <> a.
Proof. move=> Hb He; rewrite He in Hb; by apply (Rlt_irrefl a). Qed.

Definition ltR_eqF := Rlt_not_eq.

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

Definition oppRD := Ropp_plus_distr.
Definition oppRB := Ropp_minus_distr.

Lemma oppR_eq0 x : (- x == 0) = (x == 0).
Proof.
apply/idP/idP => [|/eqP ->]; last by rewrite oppR0.
apply: contraTT; by move/eqP/Ropp_neq_0_compat/eqP.
Qed.

Lemma oppR_ge0 x : x <= 0 -> 0 <= - x.
Proof. move/Rle_ge; exact: Ropp_0_ge_le_contravar. Qed.

Lemma oppR_lt0 x : 0 < x -> 0 > - x.
Proof. exact: Ropp_0_lt_gt_contravar. Qed.

Lemma oppR_gt0 x : 0 > x -> 0 < - x.
Proof. exact: Ropp_0_gt_lt_contravar. Qed.

(* Rnot_lt_le
     : forall r1 r2 : R, ~ r1 < r2 -> r2 <= r1 *)
(* Rlt_not_le
     : forall r1 r2 : R, r2 < r1 -> ~ r1 <= r2 *)
Lemma leRNlt m n : (m <b= n) = ~~ (n <b m).
Proof.
apply/idP/idP.
move/leRP => ?; exact/ltRP/Rle_not_gt.
move/ltRP/Rnot_lt_le => ?; exact/leRP.
Qed.

Lemma ltRNge m n : (m <b n) = ~~ (n <b= m).
Proof. by rewrite leRNlt negbK. Qed.

Lemma leRNgt (x y : R) : (x <b= y) = ~~ (x >b y).
Proof. by rewrite /gtR_bool ltRNge negbK. Qed.

Lemma ltRR n : n <b n = false.
Proof. by apply/ltRP/Rlt_irrefl. Qed.

Definition ltRW {m n} : m < n -> m <= n := Rlt_le m n.
Lemma ltRW' {a b : R} : a <b b -> a <b= b.
Proof. by move/ltRP/Rlt_le/leRP. Qed.

Lemma leR_eqVlt m n : (m <b= n) = (m == n) || (m <b n).
Proof.
apply/idP/idP => [/leRP|/orP[/eqP ->|]].
  case/Rle_lt_or_eq_dec => ?; apply/orP; by [right; apply/ltRP|left; apply/eqP].
exact: leRR'.
exact: ltRW'.
Qed.

Lemma ltR_neqAle m n : (m <b n) = (m != n) && (m <b= n).
Proof. by rewrite ltRNge leR_eqVlt negb_or ltRNge negbK eq_sym. Qed.

Lemma lt0R x : (0 <b x) = (x != 0) && (0 <b= x).
Proof. by rewrite ltR_neqAle eq_sym. Qed.

Lemma le0R x : (0 <b= x) = (x == 0) || (0 <b x).
Proof. by rewrite leR_eqVlt eq_sym. Qed.

(* Lemma pnatr_eq0 n : (n%:R == 0 :> R) = (n == 0)%N. *)
Lemma INR_eq0 n : (INR n == 0) = (n == O).
Proof.
apply/idP/idP => [/eqP|/eqP -> //].
by rewrite (_ : 0 = INR 0) // => /INR_eq ->.
Qed.

Lemma leR0n n : (0 <b= INR n) = (O <= n)%nat.
Proof. exact/idP/idP/leRP/pos_INR. Qed.

Lemma ltR0n n : (0 <b INR n) = (O < n)%nat.
Proof.
apply/idP/idP => [/ltRP|/ltP/lt_0_INR/ltRP //].
by rewrite (_ : 0 = INR O) // => /INR_lt/ltP.
Qed.

Lemma leR_nat m n : (INR m <b= INR n) = (m <= n)%nat.
Proof. by apply/idP/idP => [/leRP/INR_le/leP//|/leP/le_INR/leRP]. Qed.

Lemma ltR_nat m n : (INR m <b INR n) = (m < n)%nat.
Proof. by apply/idP/idP => [/ltRP/INR_lt/ltP//|/ltP/lt_INR/ltRP]. Qed.

Lemma leR_oppr x y : (x <= - y) <-> (y <= - x).
Proof. split; move/Ropp_le_contravar; by rewrite oppRK. Qed.

Lemma leR_oppl x y : (- x <= y) <-> (- y <= x).
Proof. split; move/Ropp_le_contravar; by rewrite oppRK. Qed.

Lemma ltR_oppr x y : (x < - y) <-> (y < - x).
Proof. split; move/Ropp_lt_contravar; by rewrite oppRK. Qed.

Lemma ltR_oppl x y : (- x < y) <-> (- y < x).
Proof. split; move/Ropp_lt_contravar; by rewrite oppRK. Qed.

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
Proof. move=> ? ?; apply/leRP/Rplus_le_compat; exact/leRP. Qed.

Lemma leR_add2r {p m n} : m + p <= n + p <-> m <= n.
Proof. split; [exact: Rplus_le_reg_r | exact: Rplus_le_compat_r]. Qed.
Lemma leR_add2r' p m n : (m + p <b= n + p) = (m <b= n).
Proof. by apply/idP/idP => [/leRP/leR_add2r/leRP //|/leRP/leR_add2r/leRP]. Qed.

Lemma leR_add2l {p m n} : p + m <= p + n <-> m <= n.
Proof. split; [exact: Rplus_le_reg_l | exact: Rplus_le_compat_l]. Qed.

Definition ltR_add := Rplus_lt_compat. (* r1 < r2 -> r3 < r4 -> r1 + r3 < r2 + r4 *)

Lemma ltR_add2r {p m n} : m + p < n + p <-> m < n.
Proof. split; [exact: Rplus_lt_reg_r | exact: Rplus_lt_compat_r]. Qed.
Lemma ltR_add2r' (p m n : R) : (m + p <b n + p) = (m <b n).
 by apply/idP/idP => [/ltRP/ltR_add2r/ltRP // | /ltRP/ltR_add2r/ltRP]. Qed.

Lemma ltR_add2l {p m n} : p + m < p + n <-> m < n.
Proof. split; [exact: Rplus_lt_reg_l | exact: Rplus_lt_compat_l]. Qed.

Definition leR_lt_add := Rplus_le_lt_compat. (* x <= y -> z < t -> x + z < y + t *)

Lemma ltR_subRL m n p : (n <b p - m) = (m + n <b p).
Proof.
apply/idP/idP => /ltRP H; apply/ltRP.
  move/(@ltR_add2l m) : H; by rewrite addRCA Rplus_opp_r addR0.
by apply (@ltR_add2l m); rewrite addRCA Rplus_opp_r addR0.
Qed.

Lemma leR_subr_addr x y z : (x <= y - z) <-> (x + z <= y).
Proof.
split => [|H]; first by move/leRP; rewrite -(leR_add2r' z) subRK => /leRP.
apply/leRP; rewrite -(leR_add2r' z) subRK; exact/leRP.
Qed.
Lemma leR_subr_addr' x y z : (x <b= y - z) = (x + z <b= y).
Proof. by apply/idP/idP => /leRP/leR_subr_addr/leRP. Qed.

Lemma leR_subl_addr x y z : (x - y <= z) <-> (x <= z + y).
Proof.
split => [|H]; first by move/leRP; rewrite -(leR_add2r' y) subRK => /leRP.
apply/leRP; rewrite -(leR_add2r' y) subRK; exact/leRP.
Qed.
Lemma leR_subl_addr' x y z : (x - y <b= z) = (x <b= z + y).
Proof. by apply/idP/idP => /leRP/leR_subl_addr/leRP. Qed.

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

(* NB: Rmult_ge_compat_l? *)

Lemma leR_pmul2l m n1 n2 : 0 < m -> (m * n1 <= m * n2) <-> (n1 <= n2).
Proof.
move=> m0; split; [exact: Rmult_le_reg_l | exact/Rmult_le_compat_l/ltRW].
Qed.
Lemma leR_pmul2l' m n1 n2 : 0 <b m -> (m * n1 <b= m * n2) = (n1 <b= n2).
Proof.
move=> /ltRP Hm.
apply/idP/idP; first by move/leRP/leR_pmul2l => /(_ Hm)/leRP.
by move/leRP/(leR_wpmul2l (ltRW Hm))/leRP.
Qed.

Lemma leR_pmul2r m n1 n2 : 0 < m -> (n1 * m <= n2 * m) <-> (n1 <= n2).
Proof.
move=> m0; split; [exact: Rmult_le_reg_r | exact/Rmult_le_compat_r/ltRW].
Qed.

Lemma ltR_pmul2l m n1 n2 : 0 < m -> (m * n1 < m * n2) <-> (n1 < n2).
Proof. move=> m0; split; [exact: Rmult_lt_reg_l | exact/Rmult_lt_compat_l]. Qed.

Lemma ltR_pmul2r m n1 n2 : 0 < m -> (n1 * m < n2 * m) <-> (n1 < n2).
Proof. move=> m0; split; [exact: Rmult_lt_reg_r | exact/Rmult_lt_compat_r]. Qed.
Lemma leR_pmul2r' m n1 n2 : 0 <b m -> (n1 * m <b= n2 * m) = (n1 <b= n2).
Proof. move=> Hm; by rewrite -!(mulRC m) leR_pmul2l'. Qed.

Arguments leR_pmul2l [_] [_] [_].
Arguments leR_pmul2r [_] [_] [_].
Arguments ltR_pmul2l [_] [_] [_].
Arguments ltR_pmul2r [_] [_] [_].

(*************)
(* invR/divR *)
(*************)

Lemma invR_gt0 x : 0 < x -> 0 < / x.
Proof. move=> x0; by apply Rinv_0_lt_compat. Qed.

(* Rinv_neq_0_compat : forall r : R, r <> 0 -> / r <> 0 *)
Lemma invR_neq0 (x : R) : x != 0 -> / x != 0.
Proof. by move/eqP/Rinv_neq_0_compat/eqP. Qed.

Lemma invR_eq0 (x : R) : / x == 0 -> x == 0.
Proof.
move => H; apply: contraTT H => H.
exact/invR_neq0.
Qed.

Definition invR1 : / 1 = 1 := Rinv_1.

Definition invRK := Rinv_involutive.

Definition invRM := Rinv_mult_distr.

Lemma leR_inv x y : 0 < y -> y <= x -> / x <= / y.
Proof. by move=> x0 y0; apply/Rinv_le_contravar. Qed.
(* NB: Rle_Rinv does the same as Rinv_le_contravar with one more hypothesis *)
Lemma leR_inv' : {in [pred x | true] & [pred x | 0 <b x], {homo Rinv : a b /~ a <= b}}.
Proof. move=> a b; rewrite !inE => _ /ltRP b0 ba; exact/Rinv_le_contravar. Qed.

Lemma invR_le x y : 0 < x -> 0 < y -> / y <= / x -> x <= y.
Proof.
move=> x0 y0 H.
rewrite -(invRK x); last by apply not_eq_sym, Rlt_not_eq.
rewrite -(invRK y); last by apply not_eq_sym, Rlt_not_eq.
apply leR_inv => //; exact/invR_gt0.
Qed.

Lemma ltR_inv x y : 0 < x -> 0 < y -> y < x -> / x < / y.
Proof. by move=> xo y0; apply/Rinv_lt_contravar/mulR_gt0. Qed.

Definition divRR (x : R) : x != 0 -> x / x = 1.
Proof. move=> x0; rewrite /Rdiv Rinv_r //; exact/eqP. Qed.

Lemma divR1 (x : R) : x / 1 = x.
Proof. by rewrite /Rdiv invR1 mulR1. Qed.

Lemma div1R (x : R) : 1 / x = / x.
Proof. by rewrite /Rdiv mul1R. Qed.

Lemma div0R (x : R) : 0 / x = 0.
Proof. by rewrite /Rdiv mul0R. Qed.

Definition mulRV (x : R) : x != 0 -> x * / x = 1 := divRR x.

(* Rinv_l_sym *)
Lemma mulVR (x : R) : x != 0 -> / x * x = 1.
Proof. by move=> x0; rewrite mulRC mulRV. Qed.

Lemma leR_pdivl_mulr z x y : 0 < z -> (x <b= y / z) = (x * z <b= y).
Proof.
move=> z0; apply/idP/idP=> [|]/leRP.
  move/(leR_wpmul2l (ltRW z0)).
  rewrite mulRC mulRCA mulRV ?mulR1; by [move/leRP | exact/eqP/gtR_eqF].
move=> H; apply/leRP/(@leR_pmul2r z) => //.
rewrite -mulRA mulVR ?mulR1 //; exact/eqP/gtR_eqF.
Qed.

Lemma ltR_pdivl_mulr z x y : 0 < z -> (x <b y / z) = (x * z <b y).
Proof.
move=> z0; apply/idP/idP=> [|]/ltRP.
  move/(@ltR_pmul2l z) => /(_ z0).
  rewrite mulRC mulRCA mulRV ?mulR1; by [move/ltRP | exact/eqP/gtR_eqF].
move=> H; apply/ltRP/(@ltR_pmul2r z) => //.
rewrite -mulRA mulVR ?mulR1 //; exact/eqP/gtR_eqF.
Qed.

Lemma leR_pdivr_mulr z x y : 0 < z -> (y / z <b= x) = (y <b= x * z).
Proof.
move=> z0; apply/idP/idP => [|]/leRP.
  move/(leR_wpmul2r (ltRW z0)).
  rewrite -mulRA mulVR ?mulR1; [by move/leRP | exact/eqP/gtR_eqF].
move=> H; apply/leRP/(@leR_pmul2r z) => //.
rewrite -mulRA mulVR ?mulR1 //; exact/eqP/gtR_eqF.
Qed.

Lemma ltR_pdivr_mulr z x y : 0 < z -> (y / z <b x) = (y <b x * z).
Proof.
move=> z0; apply/idP/idP => [|]/ltRP.
  move/(@ltR_pmul2r z) => /(_ z0).
  rewrite -mulRA mulVR ?mulR1; by [move/ltRP | exact/eqP/gtR_eqF].
move=> H; apply/ltRP/(@ltR_pmul2r z) => //.
rewrite -mulRA mulVR ?mulR1 //; exact/eqP/gtR_eqF.
Qed.

Lemma invR_le1 x : 0 < x -> (/ x <b= 1) = (1 <b= x).
Proof. move=> x0; by rewrite -(div1R x) leR_pdivr_mulr // mul1R. Qed.

(*******)
(* pow *)
(*******)

Lemma pow_eq0 x (n : nat) : (x ^ n.+1 == 0) = (x == 0).
Proof.
apply/idP/idP => [/eqP H|/eqP ->]; apply/eqP; last by rewrite pow_ne_zero.
move: (pow_nonzero x n.+1); tauto.
Qed.

Lemma pow_not0 x (n : nat) : x != 0 -> x ^ n != 0.
Proof. by move/eqP/(pow_nonzero _ n)/eqP. Qed.

Lemma powRV x (n : nat) : x != 0 -> (/ x ) ^ n = x ^- n.
Proof.
move/eqP => x_not0.
elim : n => /= [ | n IH]; first by rewrite Rinv_1.
rewrite invRM //; by [rewrite IH | apply/eqP/pow_not0/eqP].
Qed.

(*Rpow_mult_distr : forall (x y : R) (n : nat), (x * y) ^ n = x ^ n * y ^ n*)
Definition powRM := Rpow_mult_distr.

Lemma normRM : {morph Rabs : x y / x * y : R}.
Proof. exact: Rabs_mult. Qed.

Lemma leR0_norm x : x <= 0 -> `|x| = - x. Proof. exact: Rabs_left1. Qed.
Lemma ltR0_norm x : x < 0 -> `|x| = - x. Proof. by move/ltRW/leR0_norm. Qed.
Lemma geR0_norm x : 0 <= x -> `|x| = x. Proof. exact: Rabs_pos_eq. Qed.
Lemma gtR0_norm x : 0 < x -> `|x| = x. Proof. by move/ltRW/geR0_norm. Qed.

Definition maxRA : associative Rmax := Rmax_assoc.
Definition maxRC : commutative Rmax := Rmax_comm.

(*Lemma geq_max m n1 n2 : (m >= maxn n1 n2) = (m >= n1) && (m >= n2).*)
Lemma leR_max x y z : (Rmax y z <b= x) = (y <b= x) && (z <b= x).
Proof.
apply/idP/idP => [/leRP|/andP[/leRP H1 /leRP H2]]; last first.
  apply/leRP; by apply Rmax_case_strong.
apply Rmax_case_strong => /leRP H1 /leRP H2.
  rewrite H2; apply/leRP/leR_trans; apply/leRP; by eauto.
rewrite H2 andbC; apply/leRP/leR_trans; apply/leRP; by eauto.
Qed.

Definition leR_maxl m n : m <= Rmax m n := Rmax_l m n.
Definition leR_maxr m n : n <= Rmax m n := Rmax_r m n.
Definition geR_minl m n : Rmin m n <= m := Rmin_l m n.
Definition geR_minr m n : Rmin m n <= n := Rmin_r m n.
