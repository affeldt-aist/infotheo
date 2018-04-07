(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import div fintype tuple finfun bigop prime finset.
From mathcomp Require Import binomial.
Require Import ProofIrrelevance Reals Fourier.
Require Import Rssr.

(** * Additional lemmas about Coq Reals *)

Reserved Notation "T '->' 'R+' " (at level 10, format "'[' T  ->  R+ ']'").
Reserved Notation "+| r |" (at level 0, r at level 99, format "+| r |").
Reserved Notation "P '<<' Q" (at level 10, Q at next level).
Reserved Notation "P '<<b' Q" (at level 10).

Notation "'min(' x ',' y ')'" := (Rmin x y) : reals_ext_scope.
Notation "'max(' x ',' y ')'" := (Rmax x y)
  (format "'max(' x ','  y ')'") : reals_ext_scope.
Notation "+| r |" := (Rmax 0 r) : reals_ext_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Arguments INR : simpl never.

Record pos_fun (T : Type) := mkPosFun {
  pos_f :> T -> R ;
  pos_f_nonneg : forall a, 0 <= pos_f a }.

Notation "T '->' 'R+' " := (pos_fun T) : reals_ext_scope.

Local Open Scope reals_ext_scope.

Lemma pos_fun_eq {C : Type} (f g : C -> R+) : pos_f f = pos_f g -> f = g.
Proof.
destruct f as [f Hf].
destruct g as [g Hg].
move=> /= ?; subst.
suff : Hf = Hg by move=> ->.
by apply proof_irrelevance.
Qed.

(* TODO: move? *)
Lemma Rlt_0_Rmult_inv a b : 0 < a * b -> 0 <= a -> 0 <= b -> 0 < a /\ 0 < b.
Proof.
move=> H Ha Hb.
split.
  apply Rnot_le_lt => abs.
  have : a = 0.
    clear -Ha abs.
    by apply Rle_antisym.
  move=> abs'; rewrite abs' mul0R in H.
  by move/Rlt_irrefl : H.
apply Rnot_le_lt => abs.
have : b = 0.
  clear -Hb abs.
  by apply Rle_antisym.
move=> abs'; rewrite abs' mulR0 in H.
by move/Rlt_irrefl : H.
Qed.

Lemma iter_Rmult_pow x : forall n : nat, ssrnat.iter n (Rmult x) 1 = x ^ n.
Proof. elim => // n Hn ; by rewrite iterS Hn. Qed.

Lemma iter_Rplus_Rmult x : forall n : nat, ssrnat.iter n (Rplus x) 0 = INR n * x.
Proof.
elim; first by rewrite mul0R.
move=> n Hn; by rewrite iterS Hn -{1}(mul1R x) -mulRDl addRC -S_INR.
Qed.

(*Lemma exp_not_0 l : (exp l <> 0)%R.
Proof. apply not_eq_sym, Rlt_not_eq ; exact (exp_pos l). Qed.*)

Lemma leR2e : 2 <= exp 1.
Proof. apply Rlt_le, exp_ineq1; fourier. Qed.

Lemma ltRinve1 : exp (-1) < 1.
Proof. rewrite -[X in _ < X]exp_0. apply exp_increasing. fourier. Qed.

Lemma ltRinve21 : exp (-2) < 1.
Proof. rewrite -[X in _ < X]exp_0. apply exp_increasing. fourier. Qed.

Lemma Rle_inv_conv x y : 0 < x -> 0 < y -> / y <= / x -> x <= y.
Proof.
move=> x_pos y_pos H.
rewrite -(invRK x); last by apply not_eq_sym, Rlt_not_eq.
rewrite -(invRK y); last by apply not_eq_sym, Rlt_not_eq.
apply Rinv_le_contravar => //; exact/invR_gt0.
Qed.

(* NB: see Rplus_lt_reg_pos_r in the standard library *)
Lemma Rplus_le_lt_reg_pos_r r1 r2 r3 : 0 < r2 -> r1 + r2 <= r3 -> r1 < r3.
Proof. move=> *. fourier. Qed.

Lemma INR_Zabs_nat x : (0 <= x)%Z -> INR (Zabs_nat x) = IZR x.
Proof. move=> Hx. by rewrite INR_IZR_INZ Zabs2Nat.id_abs Z.abs_eq. Qed.

Lemma leR_maxl x y z : (max(y, z) <b= x) = (y <b= x) && (z <b= x).
Proof.
apply/idP/idP => [/RleP|/andP[/RleP H1 /RleP H2]]; last first.
  apply/RleP; by apply Rmax_case_strong.
apply Rmax_case_strong => /RleP H1 /RleP H2.
  rewrite H2; apply/RleP/Rle_trans; apply/RleP; by eauto.
rewrite H2 andbC; apply/RleP/Rle_trans; apply/RleP; by eauto.
Qed.

Definition maxRA : associative Rmax := Rmax_assoc.

Definition maxRC : commutative Rmax := Rmax_comm.

(** non-negative rationals: *)

Record Qplus := mkRrat { num : nat ; den : nat }.

Definition Q2R (q : Qplus) := INR (num q) / INR (den q).+1.

Coercion Q2R : Qplus >-> R.

(** Lemmas about division *)

Lemma neq_Rdiv a b : a <> 0 -> b <> 0 -> b <> 1 -> a <> a / b.
Proof.
move=> Ha Hb Hb' abs.
rewrite -{1}[X in X = _]mulR1 in abs.
apply Rmult_eq_reg_l in abs => //.
apply Hb'.
apply Rmult_eq_reg_r with (/ b); last exact: Rinv_neq_0_compat.
rewrite mulRV ?mul1R //; exact/eqP.
Qed.

Lemma Rdiv_le a : 0 <= a -> forall r, 1 <= r -> a / r <= a.
Proof.
move=> Ha r Hr.
apply Rmult_le_reg_l with r; first by fourier.
rewrite /Rdiv mulRCA mulRV; last by apply/negP => /eqP ?; subst r; fourier.
rewrite -mulRC; apply Rmult_le_compat_r => //; fourier.
Qed.

Lemma Rdiv_lt a : 0 < a -> forall r : R, 1 < r -> a / r < a.
Proof.
move=> Ha r0 Hr0.
rewrite -[X in _ < X]mulR1.
apply Rmult_lt_compat_l => //.
rewrite -invR1.
apply Rinv_1_lt_contravar => //.
exact/Rle_refl.
Qed.

Lemma leR_subr_addr x y z : (x <b= y - z) = (x + z <b= y).
Proof. apply/idP/idP => /RleP ?; apply/RleP; fourier. Qed.

Lemma leR_subl_addr x y z : (x - y <b= z) = (x <b= z + y).
Proof. apply/idP/idP => /RleP ?; apply/RleP; fourier. Qed.

(** Lemmas about power *)

Lemma le_sq x : 0 <= x ^ 2.
Proof.
move=> /=; case: (Rle_dec 0 x) => H; rewrite mulR1.
by apply mulR_ge0.
rewrite -(oppRK x) Rmult_opp_opp.
apply mulR_ge0; by apply oppR_ge0, ltRW, Rnot_le_lt.
Qed.

Lemma sq_incr a b : 0 <= a -> 0 <= b -> a <= b -> a^2 <= b^2.
Proof. move=> Ha Hb H. by apply pow_incr. Qed.

Lemma pow2_Rle_inv a b : 0 <= a -> 0 <= b -> a^2 <= b^2 -> a <= b.
Proof.
move=> Ha Hb H.
apply sqrt_le_1 in H; last 2 first.
  by apply le_sq.
  by apply le_sq.
by rewrite /= !mulR1 !sqrt_square in H.
Qed.

Lemma pow2_Rlt_inv a b : 0 <= a -> 0 <= b -> a^2 < b^2 -> a < b.
Proof.
move=> Ha Hb H.
apply sqrt_lt_1 in H; last 2 first.
  by apply le_sq.
  by apply le_sq.
by rewrite /= !mulR1 !sqrt_square in H.
Qed.

Lemma Rabs_sq x : Rabs x ^ 2 = x ^ 2.
Proof.
move=> /=.
rewrite !mulR1 -Rabs_mult Rabs_pos_eq // (_ : _ * _ = x ^2 ).
apply le_sq.
by rewrite /= mulR1.
Qed.

Lemma id_rem a b : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2.
Proof. rewrite /= !mulR1 !mulRDr !mulRBl /=; field. Qed.

Lemma id_rem_plus a b : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2.
Proof. rewrite /= !mulR1 !mulRDl !mul1R !mulRDr /=; field. Qed.

Lemma x_x2_eq q : q * (1 - q) = 1 / 4 - 1 / 4 * (2 * q - 1) ^ 2.
Proof. field. Qed.

Lemma x_x2_max q : q * (1 - q) <= 1 / 4.
Proof.
rewrite x_x2_eq.
have : forall a b, 0 <= b -> a - b <= a. move=>  *; fourier.
apply.
apply mulR_ge0; [fourier | by apply le_sq].
Qed.

Section pow_sect.

Lemma pow0_inv : forall n x, x ^ n = 0 -> x = 0.
Proof.
elim => [x /= H | n IH x /= H].
fourier.
case/Rmult_integral : H => //; by move/IH.
Qed.

Lemma INR_pow_expn (r : nat) : forall n, INR r ^ n = INR (expn r n).
Proof.
elim => // n IH.
by rewrite (expnSr r n) mult_INR -addn1 pow_add /= mulR1 IH.
Qed.

Lemma pow_mult x y : forall n, (x * y) ^ n = x ^ n * y ^ n.
Proof.
elim=> /= [|n IH]; first by rewrite mul1R.
rewrite -2!mulRA; f_equal.
rewrite [in X in _ = X]mulRC -mulRA; f_equal.
by rewrite IH mulRC.
Qed.

Lemma pow_gt0 x : 0 < x -> forall n, 0 < x ^ n.
Proof.
move=> x_pos.
elim => [/= | n IH]; by [apply Rlt_0_1 | apply mulR_gt0].
Qed.

Lemma pow_ge0 x : 0 <= x -> forall n, 0 <= x ^ n.
Proof.
move=> x_pos.
elim => [/= | n IH]; first by apply Rlt_le, Rlt_0_1.
rewrite -(mulR0 0).
apply Rmult_le_compat => //; by apply Rle_refl.
Qed.

Lemma Rmult_pow_inv r a b : r <> 0 -> (b <= a)%nat -> r ^ a * (/ r) ^ b = r ^ (a - b).
Proof.
move=> Hr ab; symmetry.
rewrite (pow_RN_plus r _ b) // plusE -minusE subnK // expRV //; exact/eqP.
Qed.

End pow_sect.

(** Lemmas about up / Int_part / frac_part *)

Lemma up_pos r : 0 <= r -> (0 < up r)%Z.
Proof.
move=> Hr.
apply lt_IZR => /=.
move/Rgt_lt : (proj1 (archimed r)) => Hr'.
by apply Rle_lt_trans with r.
Qed.

Lemma Rle_up_pos r : 0 <= r -> r <= IZR (Zabs (up r)).
Proof.
move=> Hr.
rewrite Zabs_eq; last first.
  apply up_pos in Hr.
  by apply Z.lt_le_incl.
case: (base_Int_part r).
rewrite /Int_part minus_IZR => _ ?; fourier.
Qed.

Lemma Rle_up a : a <= IZR (Zabs (up a)).
Proof.
case: (Rlt_le_dec a 0) => Ha; last by apply Rle_up_pos.
apply Rle_trans with 0; first by fourier.
by apply IZR_le, Zabs_pos.
Qed.

Lemma up_Int_part r : (up r = Int_part r + 1)%Z.
Proof.
case: (base_Int_part r) => H1 H2.
rewrite -(up_tech r (Int_part r)) // plus_IZR //; fourier.
Qed.

Lemma Int_part_pos a : 0 <= a -> (0 <= Int_part a)%Z.
Proof.
move/up_pos => ?.
rewrite /Int_part.
rewrite (_ : 0 = Z.succ 0 - 1)%Z //.
apply Z.sub_le_mono => //.
by apply Zlt_le_succ.
Qed.

Lemma frac_part_INR m : frac_part (INR m) = 0.
Proof.
rewrite /frac_part /Int_part -(up_tech _ (Z_of_nat m)).
rewrite minus_IZR plus_IZR /= -INR_IZR_INZ; by field.
rewrite -INR_IZR_INZ; by apply Rle_refl.
rewrite {1}INR_IZR_INZ; apply IZR_lt.
by apply Z.lt_add_pos_r.
Qed.

Lemma frac_Int_part x : frac_part x = 0 -> IZR (Int_part x) = x.
Proof.
rewrite /frac_part.
set h := IZR _.
move=> H.
by rewrite -(addR0 h) -H Rplus_minus.
Qed.

Lemma frac_part_mult a b : frac_part a = 0 -> frac_part b = 0 ->
  frac_part (a * b) = 0.
Proof.
rewrite /frac_part /Int_part !minus_IZR //.
move=> Ha Hb.
have {Ha}Ha : IZR (up a) = a + 1.
  move: Ha.
  set x := IZR (up a).
  move=> Ha.
  rewrite -[X in X = _](add0R _) -Ha.
  by field.
have {Hb}Hb : IZR (up b) = b + 1.
  move: Hb.
  set x := IZR (up b).
  move=> Hb.
  rewrite -[X in X = _](add0R _) -Hb.
  by field.
rewrite -(tech_up _ ((up a - 1) * (up b - 1) + 1)).
  rewrite ?plus_IZR ?minus_IZR ?mult_IZR ?minus_IZR // Ha Hb.
  by field.
  rewrite ?plus_IZR ?minus_IZR ?mult_IZR ?minus_IZR // Ha Hb.
  rewrite (_ : forall a, a + 1 - 1 = a); last by move=> *; field.
  rewrite (_ : forall a, a + 1 - 1 = a); last by move=> *; field.
  fourier.
  rewrite ?plus_IZR ?minus_IZR ?mult_IZR ?minus_IZR // Ha Hb.
  rewrite (_ : forall a, a + 1 - 1 = a); last by move=> *; field.
  rewrite (_ : forall a, a + 1 - 1 = a); last by move=> *; field.
  by apply Rle_refl.
Qed.

Lemma frac_part_pow a : frac_part a = 0 -> forall n, frac_part (a ^ n) = 0.
Proof.
move=> Ha; elim=> /=.
by rewrite /frac_part (_ : 1 = INR 1) // Int_part_INR  Rminus_diag_eq.
move=> n IH; by apply frac_part_mult.
Qed.

(** P is dominated by Q: *)
Section dominance.

Definition dom_by {A : Type} (P Q : A -> R) := forall a, Q a = 0 -> P a = 0.

Definition dom_byb {A : finType} (P Q : A -> R) := [forall b, (Q b == 0) ==> (P b == 0)].

End dominance.

Notation "P '<<' Q" := (dom_by P Q) : reals_ext_scope.
Notation "P '<<b' Q" := (dom_byb P Q) : reals_ext_scope.

Lemma Rabs_eq0 r : Rabs r = 0 -> r = 0.
Proof. move: (Rabs_no_R0 r); tauto. Qed.

Lemma ltR_Rabsl a b : Rabs a <b b = (- b <b a <b b).
Proof.
apply/idP/idP => [/RltP/Rabs_def2[? ?]|/andP[]/RltP ? /RltP ?].
apply/andP; split; exact/RltP.
exact/RltP/Rabs_def1.
Qed.

Lemma leR_Rabsl a b : Rabs a <b= b = (- b <b= a <b= b).
Proof.
apply/idP/idP => [/RleP|]; last first.
  case/andP => /RleP H1 /RleP H2; exact/RleP/Rabs_le.
case: (Rlt_le_dec a 0) => h.
  rewrite Rabs_left // => ?.
  apply/andP; split; apply/RleP; fourier.
rewrite Rabs_right; last by apply Rle_ge.
move=> ?; apply/andP; split; apply/RleP; fourier.
Qed.

Section exp_lb_sect.

Let exp_dev n := fun x => exp x - x ^ n * / INR (n`!).

Let derivable_exp_dev n : derivable (exp_dev n).
Proof.
rewrite /exp_dev => x.
apply derivable_pt_minus ; first by apply derivable_pt_exp.
apply derivable_pt_mult ; first by apply derivable_pt_pow.
by apply derivable_pt_const.
Defined.

Let exp_dev_rec n x : derive_pt (exp_dev n.+1) x (derivable_exp_dev n.+1 x) = exp_dev n x.
Proof.
rewrite /exp_dev derive_pt_minus derive_pt_exp; congr (_ - _).
rewrite derive_pt_mult derive_pt_const mulR0 addR0 derive_pt_pow.
rewrite mulRC mulRA mulRC; congr (_ * _).
rewrite factS mult_INR Rinv_mult_distr; last 2 first.
  by apply/eqP; rewrite INR_eq0.
  by apply/eqP; rewrite INR_eq0 -lt0n fact_gt0.
by rewrite mulRC mulRA mulRV ?mul1R // INR_eq0.
Qed.

Let exp_dev_gt0 : forall n r, 0 < r -> 0 < exp_dev n r.
Proof.
elim => [r rpos | n IH r rpos].
- rewrite /exp_dev /= mul1R Rinv_1 -exp_0.
  by apply Rgt_lt, Rgt_minus, Rlt_gt, exp_increasing.
- apply: (Rlt_trans _ 1) ; first by fourier.
  rewrite (_ : 1 = exp_dev n.+1 0) ; last first.
    rewrite /exp_dev exp_0 pow_i ?mul0R ?subR0 //; by apply/ltP.
  move: derive_increasing_interv.
  move/(_ 0 r (exp_dev n.+1) (derivable_exp_dev n.+1) rpos).
  have Haux : forall t : R,
     0 < t < r -> 0 < derive_pt (exp_dev n.+1) t (derivable_exp_dev n.+1 t).
    move=>x Hx.
    rewrite exp_dev_rec.
    by apply IH, Hx.
  move/(_ Haux 0 r) => {Haux}.
  apply => //.
  - split; [exact: Rle_refl | exact: ltRW].
  - split; [exact: ltRW | exact: Rle_refl].
Qed.

Lemma exp_strict_lb n x : 0 < x -> x ^ n * / INR (n`!) < exp x.
Proof. move=> xpos; by apply Rgt_lt, Rminus_gt, Rlt_gt, exp_dev_gt0. Qed.

Let exp_dev_ge0 n r : 0 <= r -> 0 <= exp_dev n r.
Proof.
move=> Hr.
case/orP : (orbN (r == 0)) ; last first.
- move=> Hr2.
  have {Hr Hr2}R_pos : 0 < r by apply/RltP; rewrite lt0R Hr2 /=; exact/RleP.
  exact/ltRW/exp_dev_gt0.
- move=> /eqP ->.
  move:n ; case.
  - rewrite /exp_dev exp_0 /= Rinv_1 mul1R /Rminus Rplus_opp_r; by apply Rle_refl.
  - move=> n.
    rewrite -(_ : 1 = exp_dev n.+1 0); first by apply Rle_0_1.
    rewrite /exp_dev exp_0 pow_i; last by apply/ltP.
    rewrite mul0R; by ring.
Qed.

Lemma exp_lb n x : 0 <= x -> x ^ n / INR (n`!) <= exp x.
Proof. move=> xpos; by apply Rge_le, Rminus_ge, Rle_ge, exp_dev_ge0. Qed.

End exp_lb_sect.

(* TODO: rename, move *)
Lemma fact_Coq_SSR n0 : fact n0 = n0 `!.
Proof. elim: n0 => // n0 IH /=. by rewrite IH factS mulSn -multE. Qed.

Lemma combinaison_Coq_SSR n0 m0 : (m0 <= n0)%nat -> C n0 m0 = INR 'C(n0, m0).
Proof.
move=> ?.
rewrite /C.
apply Rmult_eq_reg_r with (INR (fact m0) * INR (fact (n0 - m0)%coq_nat)).
set tmp := INR (fact m0) * _.
rewrite -mulRA mulVR ?mulR1; last first.
  by rewrite /tmp mulR_eq0 negb_or !INR_eq0 !fact_Coq_SSR -!lt0n !fact_gt0.
by rewrite/tmp -!mult_INR !fact_Coq_SSR !multE !minusE bin_fact.
apply Rmult_integral_contrapositive.
split; apply/eqP; rewrite INR_eq0; exact/eqP/fact_neq_0.
Qed.
