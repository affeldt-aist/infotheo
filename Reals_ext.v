(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import div fintype tuple finfun bigop prime finset.
From mathcomp Require Import binomial.
Require Import ProofIrrelevance Reals Fourier.
Require Import ssrR.

(** * Additional lemmas about Coq Reals *)

Reserved Notation "T '->' 'R+' " (at level 10, format "'[' T  ->  R+ ']'").
Reserved Notation "+| r |" (at level 0, r at level 99, format "+| r |").
Reserved Notation "P '<<' Q" (at level 10, Q at next level).
Reserved Notation "P '<<b' Q" (at level 10).

Notation "'min(' x ',' y ')'" := (Rmin x y)
  (format "'min(' x ','  y ')'") : reals_ext_scope.
Notation "'max(' x ',' y ')'" := (Rmax x y)
  (format "'max(' x ','  y ')'") : reals_ext_scope.
Notation "+| r |" := (Rmax 0 r) : reals_ext_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Arguments INR : simpl never.

Lemma Rlt_1_2 : 1 < 2. Proof. by fourier. Qed.
Hint Resolve Rlt_1_2.

Record pos_fun (T : Type) := mkPosFun {
  pos_f :> T -> R ;
  pos_f_ge0 : forall a, 0 <= pos_f a }.

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

Definition onem (r : R) := (1 - r)%R.
Notation "p '.~'" := (onem p)%R (format "p .~", at level 5) : R_scope.

Lemma onem_ge0 (r : R) : r <= 1 -> 0 <= r.~.
Proof. move=> r1; rewrite /onem; fourier. Qed.

Lemma onemKC (r : R) : (r + r.~ = 1)%R.
Proof. rewrite /onem; by field. Qed.

Lemma onemK p : p.~.~ = p.
Proof. by rewrite /onem subRBA addRC addRK. Qed.

Lemma iter_mulR x (n : nat) : ssrnat.iter n (Rmult x) 1 = x ^ n.
Proof. elim : n => // n Hn ; by rewrite iterS Hn. Qed.

Lemma iter_addR x (n : nat) : ssrnat.iter n (Rplus x) 0 = INR n * x.
Proof.
elim : n ; first by rewrite mul0R.
move=> n Hn; by rewrite iterS Hn -{1}(mul1R x) -mulRDl addRC -S_INR.
Qed.

(* TODO: rename; move? *)
Lemma Rlt_0_Rmult_inv a b : 0 < a * b -> 0 <= a -> 0 <= b -> 0 < a /\ 0 < b.
Proof.
move=> H Ha Hb.
split.
- apply/ltRNge => abs.
  have abs' : a = 0 by rewrite eqR_le.
  by move: H; rewrite abs' mul0R => /ltRR.
- apply/ltRNge => abs.
  have abs' : b = 0 by rewrite eqR_le.
  by move: H; rewrite abs' mulR0 => /ltRR.
Qed.

(* NB: see Rplus_lt_reg_pos_r in the standard library *)
Lemma Rplus_le_lt_reg_pos_r r1 r2 r3 : 0 < r2 -> r1 + r2 <= r3 -> r1 < r3.
Proof. move=> *. fourier. Qed.

Lemma INR_Zabs_nat x : (0 <= x)%Z -> INR (Z.abs_nat x) = IZR x.
Proof. move=> Hx. by rewrite INR_IZR_INZ Zabs2Nat.id_abs Z.abs_eq. Qed.

(** non-negative rationals: *)

Record Qplus := mkRrat { num : nat ; den : nat }.

Definition Q2R (q : Qplus) := INR (num q) / INR (den q).+1.

Coercion Q2R : Qplus >-> R.

(** Lemmas about division *)

Lemma neq_Rdiv a b : a <> 0 -> b <> 0 -> b <> 1 -> a <> a / b.
Proof.
move=> Ha Hb Hb' abs.
rewrite -{1}[X in X = _]mulR1 in abs.
move/(eqR_mul2l Ha) in abs.
apply Hb'.
apply (@eqR_mul2r (/ b)); first exact/eqP/invR_neq0/eqP.
rewrite mulRV ?mul1R //; exact/eqP.
Qed.

Lemma Rdiv_le a : 0 <= a -> forall r, 1 <= r -> a / r <= a.
Proof.
move=> Ha r Hr.
apply (@leR_pmul2l r); first by fourier.
rewrite /Rdiv mulRCA mulRV; last by apply/negP => /eqP ?; subst r; fourier.
rewrite -mulRC; exact: leR_wpmul2r.
Qed.

Lemma Rdiv_lt a : 0 < a -> forall r : R, 1 < r -> a / r < a.
Proof.
move=> Ha r0 Hr0.
rewrite -[X in _ < X]mulR1.
apply ltR_pmul2l => //.
rewrite -invR1.
apply ltR_inv => //; fourier.
Qed.

(** Lemmas about power *)

Section pow_sect.

Lemma powS x (n : nat) : x ^ n.+1 = x * x ^ n.
Proof. by rewrite tech_pow_Rmult. Qed.

Lemma pow_even_ge0 (n : nat) x : ~~ odd n -> 0 <= x ^ n.
Proof.
move=> Hn; rewrite -(odd_double_half n) (negbTE Hn) {Hn} add0n.
move Hm : (_./2) => m {Hm n}; elim: m => [|m ih]; first by rewrite pow_O.
rewrite doubleS 2!powS mulRA; apply/mulR_ge0 => //.
rewrite -{2}(pow_1 x) -powS; exact: pow2_ge_0.
Qed.

Lemma pow2_Rle_inv a b : 0 <= a -> 0 <= b -> a ^ 2 <= b ^ 2 -> a <= b.
Proof.
move=> Ha Hb H.
apply sqrt_le_1 in H; try exact: pow_even_ge0.
by rewrite /= !mulR1 !sqrt_square in H.
Qed.

Lemma pow2_Rlt_inv a b : 0 <= a -> 0 <= b -> a ^ 2 < b ^ 2 -> a < b.
Proof.
move=> ? ? H.
apply sqrt_lt_1 in H; try exact: pow_even_ge0.
by rewrite /= !mulR1 !sqrt_square in H.
Qed.

Lemma x_x2_eq q : q * (1 - q) = / 4 - / 4 * (2 * q - 1) ^ 2.
Proof. field. Qed.

Lemma x_x2_max q : q * (1 - q) <= / 4.
Proof.
rewrite x_x2_eq.
have : forall a b, 0 <= b -> a - b <= a. move=>  *; fourier.
apply; apply mulR_ge0; [fourier | exact: pow_even_ge0].
Qed.

Lemma pow0_inv : forall (n : nat) x, x ^ n = 0 -> x = 0.
Proof.
elim => [x /= H | n IH x /= /eqP].
fourier.
by rewrite mulR_eq0 => /orP[/eqP //|/eqP/IH].
Qed.

Lemma INR_pow_expn r : forall n : nat, INR r ^ n = INR (expn r n).
Proof.
elim => // n IH.
by rewrite (expnSr r n) mult_INR -addn1 pow_add /= mulR1 IH.
Qed.

Lemma pow_gt0 x : 0 < x -> forall n : nat, 0 < x ^ n.
Proof. move=> ?; elim => [/= | n IH] => //; exact: mulR_gt0. Qed.

Lemma pow_ge0 x : 0 <= x -> forall n : nat, 0 <= x ^ n.
Proof.
move=> x_pos.
elim => [/= | n IH] => //.
rewrite -(mulR0 0); apply leR_pmul => //; exact/leRR.
Qed.

End pow_sect.

(** Lemmas about up / Int_part / frac_part *)

Lemma up_pos r : 0 <= r -> (0 < up r)%Z.
Proof.
move=> Hr.
apply lt_IZR => /=.
move/Rgt_lt : (proj1 (archimed r)) => Hr'.
exact: (leR_ltR_trans Hr).
Qed.

Lemma Rle_up_pos r : 0 <= r -> r <= IZR (Z.abs (up r)).
Proof.
move=> Hr.
rewrite Z.abs_eq; last first.
  apply up_pos in Hr.
  by apply Z.lt_le_incl.
case: (base_Int_part r).
rewrite /Int_part minus_IZR => _ ?; fourier.
Qed.

Lemma Rle_up a : a <= IZR (Z.abs (up a)).
Proof.
case: (Rlt_le_dec a 0) => Ha; last by apply Rle_up_pos.
apply (@leR_trans  0); first by fourier.
exact/IZR_le/Zabs_pos.
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
rewrite -INR_IZR_INZ; exact/leRR.
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
  exact/leRR.
Qed.

Lemma frac_part_pow a : frac_part a = 0 -> forall n : nat, frac_part (a ^ n) = 0.
Proof.
move=> Ha; elim=> /=.
by rewrite /frac_part (_ : 1 = INR 1) // Int_part_INR  subRR.
move=> n IH; exact: frac_part_mult.
Qed.

(** P is dominated by Q: *)
Section dominance.

Definition dom_by {A : Type} (P Q : A -> R) := forall a, Q a = 0 -> P a = 0.

Definition dom_byb {A : finType} (P Q : A -> R) := [forall b, (Q b == 0) ==> (P b == 0)].

End dominance.

Notation "P '<<' Q" := (dom_by P Q) : reals_ext_scope.
Notation "P '<<b' Q" := (dom_byb P Q) : reals_ext_scope.

Lemma ltR_Rabsl a b : `| a | <b b = (- b <b a <b b).
Proof.
apply/idP/idP => [/ltRP/Rabs_def2[? ?]|/andP[]/ltRP ? /ltRP ?].
apply/andP; split; exact/ltRP.
exact/ltRP/Rabs_def1.
Qed.

Lemma leR_Rabsl a b : `| a | <b= b = (- b <b= a <b= b).
Proof.
apply/idP/idP => [/leRP|]; last first.
  case/andP => /leRP H1 /leRP H2; exact/leRP/Rabs_le.
case: (Rlt_le_dec a 0) => h.
  rewrite ltR0_norm // => ?; apply/andP; split; apply/leRP; fourier.
rewrite geR0_norm // => ?; apply/andP; split; apply/leRP; fourier.
Qed.

(* TODO: rename *)
Lemma fact_Coq_SSR n0 : fact n0 = n0 `!.
Proof. elim: n0 => // n0 IH /=. by rewrite IH factS mulSn -multE. Qed.

Lemma combinaison_Coq_SSR n0 m0 : (m0 <= n0)%nat -> C n0 m0 = INR 'C(n0, m0).
Proof.
move=> ?.
rewrite /C.
apply (@eqR_mul2r (INR (fact m0) * INR (fact (n0 - m0)%coq_nat))).
  move/eqP; rewrite mulR_eq0 !INR_eq0' => /orP[|] /eqP; exact/fact_neq_0.
set tmp := INR (fact m0) * _.
rewrite -mulRA mulVR ?mulR1; last first.
  by rewrite /tmp mulR_eq0 negb_or !INR_eq0' !fact_Coq_SSR -!lt0n !fact_gt0.
by rewrite /tmp -!mult_INR !fact_Coq_SSR !multE !minusE bin_fact.
Qed.

Lemma normR_max a b c c' : 0 <= a <= c -> 0 <= b <= c' ->
  `| a - b | <= max(c, c').
Proof.
move=> [H1 H2] [H H3]; case: (Rtotal_order a b) => [H0|[H0|H0]].
- rewrite distRC gtR0_norm ?subR_gt0 //.
  apply: (@leR_trans b); [fourier | apply/(leR_trans H3)/leR_maxr; fourier].
- subst b; rewrite subRR normR0.
  exact/(leR_trans H1)/(leR_trans H2)/leR_maxl.
- rewrite geR0_norm; last by fourier.
  apply: (@leR_trans a); [fourier|exact/(leR_trans H2)/leR_maxl].
Qed.

Lemma Rplus_minus_assoc (r1 r2 r3 : R) : (r1 + r2 - r3 = r1 + (r2 - r3))%R.
Proof. by rewrite /Rminus Rplus_assoc. Qed.
