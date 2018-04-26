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

Definition Rge_bool (a b : R) := if Rge_dec a b is left _ then true else false.
Notation "a '>b=' b" := (Rge_bool a b) : R_scope.

Definition Rle_bool a b := b >b= a.
Notation "a '<b=' b" := (Rle_bool a b) : R_scope.

Definition Rlt_bool (a b : R) := if Rlt_dec a b is left _ then true else false.
Notation "a '<b' b" := (Rlt_bool a b) : R_scope.

Definition Rgt_bool a b := b <b a.
Notation "a '>b' b" := (Rgt_bool a b) : R_scope.

Notation "a '<b=' b '<b=' c" := (Rle_bool a b && Rle_bool b c) : R_scope.
Notation "a '<b' b '<b' c" := (Rlt_bool a b && Rlt_bool b c) : R_scope.

Lemma RgeP (a b : R) : reflect (a >= b) (a >b= b).
Proof. apply: (iffP idP); by rewrite /Rge_bool; case: Rge_dec. Qed.

Lemma RleP (a b : R) : reflect (a <= b) (a <b= b).
Proof.
apply: (iffP idP); rewrite /Rle_bool /Rge_bool; case: Rge_dec => //.
by move/Rge_le.
by move/Rnot_ge_gt/Rgt_not_le.
Qed.

Lemma RltP (a b : R) : reflect (a < b) (a <b b).
Proof. apply: (iffP idP); by rewrite /Rlt_bool; case: Rlt_dec. Qed.

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

Lemma gtR_eqF a b : a < b -> b <> a.
Proof. move=> Hb He; rewrite He in Hb; by apply (Rlt_irrefl a). Qed.

Definition ltR_eqF := Rlt_not_eq.

Lemma leRR r : r <b= r.
Proof. apply/RleP. by apply Rle_refl. Qed.

Lemma ltR_subRL m n p : (n <b p - m) = (m + n <b p).
Proof.
apply/idP/idP => /RltP H; apply/RltP.
  move/(Rplus_lt_compat_l m) : H.
  by rewrite addRCA Rplus_opp_r addR0.
by apply: (Rplus_lt_reg_l m); rewrite addRCA Rplus_opp_r addR0.
Qed.

Definition oppR0 := Ropp_0.
Definition oppRK := Ropp_involutive.

Definition oppRD := Ropp_plus_distr.

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
Lemma RleNgt m n : (m <b= n) = ~~ (n <b m).
Proof.
apply/idP/idP.
move/RleP => ?; by apply/RltP/Rle_not_gt.
move/RltP/Rnot_lt_le => ?; by apply/RleP.
Qed.

Lemma RltNge m n : (m <b n) = ~~ (n <b= m).
Proof. by rewrite RleNgt negbK. Qed.

Lemma ltRR n : n <b n = false.
Proof. by apply/RltP/Rlt_irrefl. Qed.

(* Rplus_le_compat. *)
Lemma Rle_add m1 m2 n1 n2 : m1 <b= n1 -> m2 <b= n2 -> m1 + m2 <b= n1 + n2.
Proof. move=> ? ?; apply/RleP/Rplus_le_compat; by apply/RleP. Qed.

Definition ltRW m n : m < n -> m <= n := Rlt_le m n.

Lemma RltW (a b : R) : a <b b -> a <b= b.
Proof. by move/RltP/Rlt_le/RleP. Qed.

Lemma leR_eqVlt m n : (m <b= n) = (m == n) || (m <b n).
Proof.
apply/idP/idP => [/RleP|/orP[/eqP ->|]].
  case/Rle_lt_or_eq_dec => ?; apply/orP; by [right; apply/RltP|left; apply/eqP].
by rewrite leRR.
by move/RltW.
Qed.

Lemma ltR_neqAle m n : (m <b n) = (m != n) && (m <b= n).
Proof. by rewrite RltNge leR_eqVlt negb_or -RleNgt eq_sym. Qed.

Lemma lt0R x : (0 <b x) = (x != 0) && (0 <b= x).
Proof. by rewrite ltR_neqAle eq_sym. Qed.

Lemma le0R x : (0 <b= x) = (x == 0) || (0 <b x).
Proof. by rewrite leR_eqVlt eq_sym. Qed.

Lemma INR_eq0 n : (INR n == 0) = (n == O).
Proof.
apply/idP/idP => [/eqP|/eqP -> //].
by rewrite (_ : 0 = INR 0) // => /INR_eq ->.
Qed.

Lemma leR0n n : (0 <b= INR n) = (O <= n)%nat.
Proof. exact/idP/idP/RleP/pos_INR. Qed.

Lemma ltR0n n : (0 <b INR n) = (O < n)%nat.
Proof.
apply/idP/idP => [/RltP|/ltP/lt_0_INR/RltP //].
by rewrite (_ : 0 = INR O) // => /INR_lt/ltP.
Qed.

Lemma leR_nat m n : (INR m <b= INR n) = (m <= n)%nat.
Proof. by apply/idP/idP => [/RleP/INR_le/leP//|/leP/le_INR/RleP]. Qed.

Lemma ltR_nat m n : (INR m <b INR n) = (m < n)%nat.
Proof. by apply/idP/idP => [/RltP/INR_lt/ltP//|/ltP/lt_INR/RltP]. Qed.

(* Rplus_le_compat_r
     : forall r r1 r2 : R, r1 <= r2 -> r1 + r <= r2 + r*)

Lemma Rle_add2r p m n : (m + p <b= n + p) = (m <b= n).
Proof.
apply/idP/idP => [/RleP/Rplus_le_reg_r/RleP //|].
by move/RleP/(Rplus_le_compat_r p)/RleP.
Qed.

Lemma Rlt_add2r (p m n : R) : (m + p <b n + p) = (m <b n).
Proof.
apply/idP/idP => [/RltP/Rplus_lt_reg_r/RltP // | ].
by move/RltP/(Rplus_lt_compat_r p)/RltP.
Qed.

Definition mulR_ge0 := Rmult_le_pos.
Definition mulR_gt0 := Rmult_lt_0_compat.
Definition addR_ge0 := Rplus_le_le_0_compat.

(* Rmult_le_compat_l
     : forall r r1 r2 : R, 0 <= r -> r1 <= r2 -> r * r1 <= r * r2 *)
(* Rmult_le_reg_l
     : forall r r1 r2 : R, 0 < r -> r * r1 <= r * r2 -> r1 <= r2 *)
Lemma Rle_pmul2l m n1 n2 : 0 <b m -> (m * n1 <b= m * n2) = (n1 <b= n2).
Proof.
move=> /RltP Hm.
apply/idP/idP; first by move/RleP/Rmult_le_reg_l => /(_ Hm)/RleP.
move/RleP/(Rmult_le_compat_l m); by move/ltRW : Hm => Hm /(_ Hm)/RleP.
Qed.

(* Rmult_le_compat_r
     : forall r r1 r2 : R, 0 <= r -> r1 <= r2 -> r1 * r <= r2 * r *)
(* Rmult_le_reg_r
     : forall r r1 r2 : R, 0 < r -> r1 * r <= r2 * r -> r1 <= r2 *)

Lemma Rle_pmul2r m n1 n2 : 0 <b m -> (n1 * m <b= n2 * m) = (n1 <b= n2).
Proof. move=> Hm; by rewrite -!(mulRC m) Rle_pmul2l. Qed.

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

Lemma leR_inv : {in [pred x | true] & [pred x | 0 <b x], {homo Rinv : a b /~ a <= b}}.
Proof. move=> a b; rewrite !inE => _ /RltP b0 ba; exact/Rinv_le_contravar. Qed.

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
move=> z0.
apply/idP/idP=> [|]/RleP.
  move/(Rmult_le_compat_l z) => /(_ (ltRW _ _ z0)).
  rewrite mulRC mulRCA mulRV ?mulR1; last exact/eqP/gtR_eqF.
  by move/RleP.
move=> H; apply/RleP/(Rmult_le_reg_r z) => //.
rewrite -mulRA mulVR ?mulR1 //; exact/eqP/gtR_eqF.
Qed.

Lemma ltR_pdivl_mulr z x y : 0 < z -> (x <b y / z) = (x * z <b y).
Proof.
move=> z0.
apply/idP/idP=> [|]/RltP.
  move/(Rmult_lt_compat_l z) => /(_ z0).
  rewrite mulRC mulRCA mulRV ?mulR1; last exact/eqP/gtR_eqF.
  by move/RltP.
move=> H; apply/RltP/(Rmult_lt_reg_r z) => //.
rewrite -mulRA mulVR ?mulR1 //; exact/eqP/gtR_eqF.
Qed.

Lemma leR_pdivr_mulr z x y : 0 < z -> (y / z <b= x) = (y <b= x * z).
Proof.
move=> z0.
apply/idP/idP => [|]/RleP.
  move/(Rmult_le_compat_r z) => /(_ (ltRW _ _ z0)).
  rewrite -mulRA mulVR ?mulR1; first by move/RleP.
  exact/eqP/gtR_eqF.
move=> H; apply/RleP/(Rmult_le_reg_r z) => //.
rewrite -mulRA mulVR ?mulR1 //; exact/eqP/gtR_eqF.
Qed.

Lemma ltR_pdivr_mulr z x y : 0 < z -> (y / z <b x) = (y <b x * z).
Proof.
move=> z0.
apply/idP/idP => [|]/RltP.
  move/(Rmult_lt_compat_r z) => /(_ z0).
  rewrite -mulRA mulVR ?mulR1; first by move/RltP.
  exact/eqP/gtR_eqF.
move=> H; apply/RltP/(Rmult_lt_reg_r z) => //.
rewrite -mulRA mulVR ?mulR1 //; exact/eqP/gtR_eqF.
Qed.

Lemma invR_le1 x : 0 < x -> (/ x <b= 1) = (1 <b= x).
Proof. move=> x0; by rewrite -(div1R x) leR_pdivr_mulr // mul1R. Qed.

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
