(* infotheo: information theory and error-correcting codes in Coq               *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import Rstruct.
From mathcomp Require boolp.
Require Import Reals Lra.
Require Import ssrR.

(******************************************************************************)
(*              Additional lemmas and definitions about Coq reals             *)
(*                                                                            *)
(* Section reals_ext.                                                         *)
(*   various lemmas about up, Int_part, frac_part, Rabs define ceil and floor *)
(*                                                                            *)
(* Section pos_finfun.                                                        *)
(*  T ->R^+/->R+ == functions that return non-negative reals.                 *)
(*                                                                            *)
(*     p.~ == 1 - p                                                           *)
(*                                                                            *)
(*    prob == type of "probabilities", i.e., reals p s.t. 0 <= p <= 1         *)
(*   x%:pr == tries to infer that x : R is actually of type prob              *)
(*                                                                            *)
(*    Qplus == type of non-negative rationals                                 *)
(*  P `<< Q == P is dominated by Q, i.e., forall a, Q a = 0 -> P a = 0        *)
(*                                                                            *)
(*     Rpos == type of positive reals                                         *)
(*   x%:pos == tries to infer that x : R is actually a Rpos                   *)
(*                                                                            *)
(*    Rnneg == Type of non-negative reals                                     *)
(*   x%:nng == tries to infer that x : R is actually a Rnneg                  *)
(*                                                                            *)
(******************************************************************************)

Declare Scope reals_ext_scope.

Reserved Notation "T '->R^+' " (at level 10, format "'[' T  ->R^+ ']'").
Reserved Notation "T '->R+' " (at level 10, format "'[' T  ->R+ ']'").
Reserved Notation "+| r |" (at level 0, r at level 99, format "+| r |").
Reserved Notation "P '`<<' Q" (at level 51).
Reserved Notation "P '`<<b' Q" (at level 51).
Reserved Notation "p '.~'" (format "p .~", at level 5).
Reserved Notation "'`Pr' p " (format "`Pr  p", at level 6).
Reserved Notation "x %:pr" (at level 0, format "x %:pr").
Reserved Notation "x %:opr" (at level 0, format "x %:opr").
Reserved Notation "x %:pos" (at level 0, format "x %:pos").
Reserved Notation "x %:nng" (at level 0, format "x %:nng").

Notation "+| r |" := (Rmax 0 r) : reals_ext_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Arguments INR : simpl never.

Local Open Scope R_scope.
Local Open Scope reals_ext_scope.

Lemma Rlt_1_2 : 1 < 2. Proof. lra. Qed.
Global Hint Resolve Rlt_1_2 : core.

Section reals_ext.

Lemma forallP_leRP (A : finType) (f : A -> R) : reflect (forall a, 0 <= f a) [forall a, 0 <b= f a].
Proof.
apply: (iffP idP) => [/forallP H a|H]; [exact/leRP/H|apply/forallP => a; exact/leRP].
Qed.

Lemma iter_mulR x (n : nat) : ssrnat.iter n (Rmult x) 1 = x ^ n.
Proof. elim : n => // n Hn ; by rewrite iterS Hn. Qed.

Lemma iter_addR x (n : nat) : ssrnat.iter n (Rplus x) 0 = INR n * x.
Proof.
elim : n ; first by rewrite mul0R.
move=> n Hn; by rewrite iterS Hn -{1}(mul1R x) -mulRDl addRC -S_INR.
Qed.

(* TODO: see Rplus_lt_reg_pos_r in the standard library *)
(*Lemma Rplus_le_lt_reg_pos_r r1 r2 r3 : 0 < r2 -> r1 + r2 <= r3 -> r1 < r3.
Proof. move=> *. lra. Qed.*)

Lemma INR_Zabs_nat x : (0 <= x)%Z -> INR (Z.abs_nat x) = IZR x.
Proof. move=> Hx. by rewrite INR_IZR_INZ Zabs2Nat.id_abs Z.abs_eq. Qed.

Section about_the_pow_function.

Lemma pow_even_ge0 (n : nat) x : ~~ odd n -> 0 <= x ^ n.
Proof.
move=> Hn; rewrite -(odd_double_half n) (negbTE Hn) {Hn} add0n.
move Hm : (_./2) => m {Hm n}; elim: m => [|m ih]; first by rewrite pow_O.
rewrite doubleS 2!expRS mulRA; apply/mulR_ge0 => //.
rewrite -{2}(pow_1 x) -expRS; exact: pow2_ge_0.
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
have : forall a b, 0 <= b -> a - b <= a. move=>  *; lra.
apply; apply mulR_ge0; [lra | exact: pow_even_ge0].
Qed.

(*Lemma pow0_inv : forall (n : nat) x, x ^ n = 0 -> x = 0.
Proof.
elim => [x /= H | n IH x /= /eqP]; first lra.
by rewrite mulR_eq0 => /orP[/eqP //|/eqP/IH].
Qed.*)

End about_the_pow_function.

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
rewrite /Int_part minus_IZR => _ ?; lra.
Qed.

Lemma Rle_up a : a <= IZR (Z.abs (up a)).
Proof.
case: (Rlt_le_dec a 0) => Ha; last by apply Rle_up_pos.
apply (@leR_trans  0); first lra.
exact/IZR_le/Zabs_pos.
Qed.

Lemma up_Int_part r : (up r = Int_part r + 1)%Z.
Proof.
case: (base_Int_part r) => H1 H2.
rewrite -(up_tech r (Int_part r)) // plus_IZR //; lra.
Qed.

Lemma Int_part_ge0 a : 0 <= a -> (0 <= Int_part a)%Z.
Proof.
move/up_pos => ?; rewrite /Int_part (_ : 0 = Z.succ 0 - 1)%Z //.
apply Z.sub_le_mono => //; exact/Zlt_le_succ.
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
have {}Ha : IZR (up a) = a + 1.
  move: Ha.
  set x := IZR (up a).
  move=> Ha.
  rewrite -[X in X = _](add0R _) -Ha.
  by field.
have {}Hb : IZR (up b) = b + 1.
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
  lra.
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

Definition ceil (r : R) : Z := if frac_part r == 0 then Int_part r else up r.

Definition floor : R -> Z := Int_part.

Lemma floorP (r : R) : r - 1 < IZR (floor r) <= r.
Proof. rewrite /floor; case: (base_Int_part r) => ? ?; split=> //; lra. Qed.

Lemma ceilP (r : R) : r <= IZR (ceil r) < r + 1.
Proof.
rewrite /ceil; case: ifPn => [|] /eqP r0.
  rewrite frac_Int_part //; lra.
case: (floorP r); rewrite /floor => H1 /Rle_lt_or_eq_dec[] H2.
  rewrite up_Int_part plus_IZR; lra.
by exfalso; apply/r0; rewrite subR_eq0.
Qed.

Lemma leR0ceil x : 0 <= x -> (0 <= ceil x)%Z.
Proof. move=> ?; case: (ceilP x) => K _; exact/le_IZR/(leR_trans _ K). Qed.

Lemma ltR_Rabsl a b : `| a | <b b = (- b <b a <b b).
Proof.
apply/idP/idP => [/ltRP/Rabs_def2[? ?]|/ltR2P[? ?]]; first exact/ltR2P.
exact/ltRP/Rabs_def1.
Qed.

Lemma leR_Rabsl a b : `| a | <b= b = (- b <b= a <b= b).
Proof.
apply/idP/idP => [/leRP|]; last by move=> /leR2P[? ?]; exact/leRP/Rabs_le.
case: (Rlt_le_dec a 0) => h; [
  by rewrite ltR0_norm // => ?; apply/leR2P; lra |
  by rewrite geR0_norm // => ?; apply/leR2P; lra ].
Qed.

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

Lemma normR_max a b c c' : 0 <= a <= c -> 0 <= b <= c' ->
  `| a - b | <= max(c, c').
Proof.
move=> [H1 H2] [H H3]; case: (Rtotal_order a b) => [H0|[H0|H0]].
- rewrite distRC gtR0_norm ?subR_gt0 //.
  apply: (@leR_trans b); [lra | apply/(leR_trans H3)/leR_maxr; lra].
- subst b; rewrite subRR normR0.
  exact/(leR_trans H1)/(leR_trans H2)/leR_maxl.
- rewrite geR0_norm; last lra.
  apply: (@leR_trans a); [lra|exact/(leR_trans H2)/leR_maxl].
Qed.

End reals_ext.

Section rExtrema.
Variables (I : finType) (i0 : I) (F : I -> R).

Lemma arg_rmax2 : forall j, (F j <= F [arg max_(i > i0) F i]%O)%O.
Proof.
move=> j; case: (@Order.TotalTheory.arg_maxP _ _ I i0 xpredT F isT) => i _.
exact.
Qed.

End rExtrema.

Section pos_finfun.
Variable (T : finType).

Record pos_ffun := mkPosFfun {
  pos_ff :> {ffun T -> R} ;
  _ : [forall a, 0 <b= pos_ff a] }.

Canonical pos_ffun_subType := Eval hnf in [subType for pos_ff].
Definition pos_ffun_eqMixin := [eqMixin of pos_ffun by <:].
Canonical pos_ffun_eqType := Eval hnf in EqType _ pos_ffun_eqMixin.
End pos_finfun.

Notation "T '->R+' " := (pos_ffun T) : reals_ext_scope.

Lemma pos_ff_ge0 (T : finType) (f : T ->R+) : forall a, 0 <= pos_ff f a.
Proof. by case: f => f /= /forallP H a; apply/leRP/H. Qed.

Record pos_fun (T : Type) := mkPosFun {
  pos_f :> T -> R ;
  pos_f_ge0 : forall a, 0 <= pos_f a }.

Notation "T '->R^+' " := (pos_fun T) : reals_ext_scope.

Lemma pos_fun_eq {C : Type} (f g : C ->R^+) : pos_f f = pos_f g -> f = g.
Proof.
destruct f as [f Hf].
destruct g as [g Hg].
move=> /= ?; subst.
suff : Hf = Hg by move=> ->.
exact/boolp.Prop_irrelevance.
Qed.

Section onem.

Implicit Type r : R.

Definition onem r := 1 - r.
Local Notation "p '.~'" := (onem p).

Lemma onem0 : 0.~ = 1. Proof. by rewrite /onem subR0. Qed.

Lemma onem1 : 1.~ = 0. Proof. by rewrite /onem subRR. Qed.

Lemma onem_ge0 r : r <= 1 -> 0 <= r.~. Proof. move=> ?; rewrite /onem; lra. Qed.

Lemma onem_le1 r : 0 <= r -> r.~ <= 1. Proof. move=> ?; rewrite /onem; lra. Qed.

Lemma onem_le  r s : r <= s <-> s.~ <= r.~.
Proof. by rewrite /onem; split=> ?; lra. Qed.
Lemma onem_lt  r s : r < s <-> s.~ < r.~.
Proof. by rewrite /onem; split=> ?; lra. Qed.

Lemma onemKC r : r + r.~ = 1. Proof. rewrite /onem; by field. Qed.

Lemma onemK r : r.~.~ = r.
Proof. by rewrite /onem subRBA addRC addRK. Qed.

Lemma onemD (p q : R) : ((p + q).~ = p.~ + q.~ - 1)%R.
Proof. rewrite /onem; field. Qed.

Lemma onemM (p q : R) : ((p * q).~ = p.~ + q.~ - p.~ * q.~)%R.
Proof. rewrite /onem; field. Qed.

Lemma onem_div p q : q != 0 -> (p/q).~ = (q-p)/q.
Proof.
move=> Hq.
by rewrite /onem -(divRR q) // /Rdiv /Rminus -mulNR -mulRDl.
Qed.

Lemma onem_prob r : (0%R <b= r <b= R1)%R -> (0%R <b= r.~ <b= R1)%R.
Proof.
case/andP=> /leRP rO /leRP r1; apply/andP; split; apply/leRP;
              by [rewrite leR_subr_addr add0R | rewrite leR_subl_addr -(addR0 1) leR_add2l].
Qed.

Lemma onem_oprob r : (0%R < r < R1)%R -> (0%R < r.~ < R1)%R.
Proof.
by case=> rO r1; split;
            by [rewrite ltR_subr_addr add0R | rewrite ltR_subl_addr -(addR0 1) ltR_add2l].
Qed.

Lemma onem_oprobb r : (0%R <b r <b R1)%R -> (0%R <b r.~ <b R1)%R.
Proof.
case/andP=> /ltRP rO /ltRP r1; apply/andP; split; apply/ltRP;
              by [rewrite ltR_subr_addr add0R | rewrite ltR_subl_addr -(addR0 1) ltR_add2l].
Qed.

Lemma onem_eq0 r : r.~ = 0 <-> r = 1. Proof. rewrite /onem; lra. Qed.

Lemma onem_eq1 r : r.~ = 1 <-> r = 0. Proof. rewrite /onem; lra. Qed.

Lemma onem_neq0 r : r.~ != 0 <-> r != 1.
Proof. by split; apply: contra => /eqP/onem_eq0/eqP. Qed.

Lemma onem_gt0 r : r < 1 -> 0 < r.~. Proof. rewrite /onem; lra. Qed.
Lemma onem_lt1 r : 0 < r -> r.~ < 1. Proof. rewrite /onem; lra. Qed.

Lemma subR_onem x y : x - y.~ = x + y - 1.
Proof. by rewrite /onem -addR_opp oppRB addRA. Qed.

End onem.

Notation "p '.~'" := (onem p) : reals_ext_scope.

Module Prob.
Record t := mk {
  p :> R ;
  Op1 : (0 <b= p <b= 1)%R }.
Definition O1 (p : t) : 0 <b= p <b= 1 := Op1 p.
(*Definition O1P (p : t) : 0 <= p <= 1 := elimT (@leR2P _ _ _) (O1 p).*)
Arguments O1 : simpl never.
Definition mk_ (q : R) (Oq1 : 0 <= q <= 1) := mk (introT (@leR2P _ _ _) Oq1).
Module Exports.
Notation prob := t.
Notation "q %:pr" := (@mk q (@O1 _)).
Canonical prob_subType := Eval hnf in [subType for p].
Definition prob_eqMixin := [eqMixin of prob by <:].
Canonical prob_eqType := Eval hnf in EqType _ prob_eqMixin.
End Exports.
End Prob.
Export Prob.Exports.
Coercion Prob.p : prob >-> R.

Lemma oprob_prob r : 0 < r < 1 -> 0 <= r <= 1.
Proof. by case=> /ltRW ? /ltRW ?; split. Qed.

Lemma oprob_oprobb x  : 0 < x < 1 -> 0 <b x <b 1.
Proof. by case=> *; apply/andP; split; apply/ltRP. Qed.
Lemma oprobb_oprob x  : 0 <b x <b 1 -> 0 < x < 1.
Proof. by case/andP=> /ltRP ? /ltRP ?; split. Qed.

Module OProb.
Section def.
Record t := mk {
  p :> prob ;
  Op1 : (0 <b p <b 1)%R }.
Definition O1 (p : t) : 0 <b p <b 1 := Op1 p.
Arguments O1 : simpl never.
(*
Lemma oprob_probMixin (p : R) : 0 < p < 1 -> 0 <b= p <b= 1.
Proof. by case => /ltRP /ltRW' -> /ltRP /ltRW' ->. Qed.
Definition mk_ (q : R) (Oq1 : 0 < q < 1) : t.
Proof.
refine (@mk (Prob.mk (oprob_probMixin Oq1))%:pr (match Oq1 with conj Oq q1 => _ end)).
simpl.
by move/ltRP: Oq ->; move/ltRP: q1 ->.
Defined.
*)
(*
Lemma oprob_probMixin (p : t) : 0 <b= p <b= 1.
Proof. by case/andP: (Op1 p) => /ltRW' -> /ltRW' ->. Qed.
*)
End def.
Module Exports.
Notation oprob := t.
Notation "q %:opr" := (@mk q%:pr (@O1 _)).
Canonical oprob_subType := Eval hnf in [subType for p].
Definition oprob_eqMixin := [eqMixin of oprob by <:].
Canonical oprob_eqType := Eval hnf in EqType _ oprob_eqMixin.
End Exports.
End OProb.
Export OProb.Exports.
Coercion OProb.p : oprob >-> prob.

Lemma probpK p H : Prob.p (@Prob.mk p H) = p. Proof. by []. Qed.

Lemma OO1 : (R0 <= R0 <= R1)%R. Proof. lra. Qed.

Lemma O11 : (R0 <= R1 <= R1)%R. Proof. lra. Qed.

Canonical prob0 := Eval hnf in Prob.mk_ OO1.
Canonical prob1 := Eval hnf in Prob.mk_ O11.
Canonical probcplt (p : prob) := Eval hnf in Prob.mk (onem_probb (Prob.O1 p)).
Canonical oprobcplt (p : oprob) := Eval hnf in OProb.mk (onem_oprobb (OProb.O1 p)).

Lemma prob_ge0 (p : prob) : 0 <= p%R.
Proof. by case: p => p /= /leR2P[]. Qed.
Global Hint Resolve prob_ge0 : core.

Lemma prob_le1 (p : prob) : (p <= 1)%R.
Proof. by case: p => p /= /leR2P[]. Qed.
Global Hint Resolve prob_le1 : core.

Section prob_lemmas.
Implicit Types p : prob.

Lemma prob_gt0 p : p != 0%:pr <-> (0 < p)%R.
Proof.
rewrite ltR_neqAle; split=> [H|[/eqP p0 _]].
split => //; exact/nesym/eqP.
by case: p p0 => p ?; apply: contra => /eqP[/= ->].
Qed.

Lemma oprob_gt0 (p : oprob) : 0 < p%R.
Proof. by case: p=> p /= /andP [] /ltRP. Qed.
Lemma oprob_lt1 (p : oprob) : (p < 1)%R.
Proof. by case: p=> p /= /andP [] _ /ltRP. Qed.
Lemma oprob_ge0 (p : oprob) : 0 <= p%R.
Proof. apply/ltRW/oprob_gt0. Qed.
Lemma oprob_le1 (p : oprob) : p <= 1%R.
Proof. apply/ltRW/oprob_lt1. Qed.
Lemma oprob_neq0 (p : oprob) : p != 0 :> R.
Proof. by move:(oprob_gt0 p); rewrite ltR_neqAle=> -[] /nesym /eqP. Qed.
Lemma oprob_neq1 (p : oprob) : p != 1 :> R.
Proof. by move:(oprob_lt1 p); rewrite ltR_neqAle=> -[] /eqP. Qed.

Lemma prob_gt0' p : p != 0 :> R <-> (0 < p)%R.
Proof. exact: prob_gt0. Qed.

Lemma prob_lt1 p : p != 1%:pr <-> (p < 1)%R.
Proof.
rewrite ltR_neqAle; split=> [H|[/eqP p1 _]].
by split => //; exact/eqP.
by case: p p1 => p ?; apply: contra => /eqP[/= ->].
Qed.

Lemma prob_lt1' p : p != 1 :> R <-> (p < 1)%R.
Proof. exact: prob_lt1. Qed.

Lemma prob_trichotomy (p : prob) : p = 0%:pr  \/ p = 1%:pr \/ 0 < p < 1.
Proof.
case/boolP: (p == 0%:pr); first by move/eqP ->; left.
move=> pneq0; right.
case/boolP: (p == 1%:pr); first by move/eqP ->; left.
by move=> pneq1; right; split; [apply prob_gt0 | apply prob_lt1].
Qed.

Lemma prob_trichotomy' (p : prob) (P : prob -> Prop) :
  P 0%:pr -> P 1%:pr -> (forall o : oprob, P o) -> P p.
Proof.
move=> p0 p1 po.
case: (prob_trichotomy p); first by move->.
case; first by move->.
move/oprob_oprobb=> H.
exact: (po (OProb.mk H)).
Qed.

End prob_lemmas.

Lemma probK t : t = (t.~).~%:pr :> prob.
Proof. by apply val_inj => /=; rewrite onemK. Qed.

Lemma oprobK t : t = (t.~).~%:opr :> oprob.
Proof. by apply val_inj => /=; rewrite onemK. Qed.

Lemma prob_IZR (p : positive) : (R0 <= / IZR (Zpos p) <= R1)%R.
Proof.
split; first exact/Rlt_le/Rinv_0_lt_compat/IZR_lt/Pos2Z.is_pos.
rewrite -[X in (_ <= X)%R]Rinv_1; apply Rle_Rinv => //.
- exact/IZR_lt/Pos2Z.is_pos.
- exact/IZR_le/Pos2Z.pos_le_pos/Pos.le_1_l.
Qed.

Canonical probIZR (p : positive) := Eval hnf in @Prob.mk_ _ (prob_IZR p).

Definition divRnnm n m := INR n / INR (n + m).

Lemma prob_divRnnm n m : (0 <= divRnnm n m <= 1)%R.
Proof.
rewrite /divRnnm.
have [/eqP ->|n0] := boolP (n == O); first by rewrite div0R; exact OO1.
split; first by apply divR_ge0; [exact: leR0n | rewrite ltR0n addn_gt0 lt0n n0].
by rewrite leR_pdivr_mulr ?mul1R ?leR_nat ?leq_addr // ltR0n addn_gt0 lt0n n0.
Qed.

Canonical probdivRnnm (n m : nat) :=
  Eval hnf in @Prob.mk_ (divRnnm n m) (prob_divRnnm n m).

Lemma prob_invn (m : nat) : (R0 <= / (1 + m)%:R <= R1)%R.
Proof.
rewrite -(mul1R (/ _)%R) (_ : 1%R = INR 1) // -/(Rdiv _ _); exact: prob_divRnnm.
Qed.

Lemma oprob_pdivRnnm n m : (0 < n)%nat -> (0 < m)%nat -> (0 < divRnnm n m < 1)%R.
Proof.
rewrite /divRnnm.
split; first by apply divR_gt0; [rewrite ltR0n | rewrite ltR0n addn_gt0 H orTb].
rewrite ltR_pdivr_mulr ?mul1R ?ltR_nat // ?ltR0n ?addn_gt0 ?H ?orTb //.
by rewrite -{1}(addn0 n) ltn_add2l.
Qed.

(* was Canonical *)
Definition probinvn (n : nat) :=
  Eval hnf in @Prob.mk_ (/ INR (1 + n)) (prob_invn n).

Lemma prob_invp (p : prob) : (0 <= 1 / (1 + p) <= 1)%R.
Proof.
split.
- by apply divR_ge0 => //; exact: addR_gt0wl.
- rewrite leR_pdivr_mulr ?mul1R; last exact: addR_gt0wl.
  by rewrite addRC -leR_subl_addr subRR.
Qed.
Definition Prob_invp (p : prob) := Prob.mk_ (prob_invp p).

Lemma prob_mulR (p q : prob) : (0 <= p * q <= 1)%R.
Proof. by split; [exact/mulR_ge0 |rewrite -(mulR1 1%R); apply leR_pmul]. Qed.

Canonical probmulR (p q : prob) :=
  Eval hnf in @Prob.mk_ (p * q) (prob_mulR p q).

Lemma oprob_mulR (p q : oprob) : (0 < p * q < 1)%R.
Proof.
split; first by apply/mulR_gt0/oprob_gt0/oprob_gt0.
by rewrite -(mulR1 1%R); apply ltR_pmul;
  [exact/oprob_ge0 | exact/oprob_ge0 | exact/oprob_lt1 | exact/oprob_lt1].
Qed.
Canonical oprobmulR (p q : oprob) :=
  Eval hnf in @OProb.mk (p * q)%:pr (oprob_oprobb (oprob_mulR p q)).

Lemma probadd_eq0 (p q : prob) : p + q = 0%:pr <-> p = 0%:pr /\ q = 0%:pr.
Proof.
split => [/paddR_eq0 | ].
- by move=> /(_ _)[] // /val_inj-> /val_inj->.
- by case => -> ->; rewrite addR0.
Qed.

Lemma probadd_neq0 (p q : prob) : p + q != 0%:pr <-> p != 0%:pr \/ q != 0%:pr.
Proof.
split => [/paddR_neq0| ]; first by move=> /(_ _ _); apply.
by case; apply: contra => /eqP/probadd_eq0 [] /eqP ? /eqP.
Qed.

Lemma oprobadd_gt0 (p q : oprob) : 0 < p + q%R.
Proof. by apply/addR_gt0/oprob_gt0/oprob_gt0. Qed.
Lemma oprobadd_neq0 (p q : oprob) : p + q != 0%R.
Proof. by move:(oprobadd_gt0 p q); rewrite ltR_neqAle => -[] /nesym /eqP. Qed.

Lemma probmul_eq1 (p q : prob) : p * q = 1%:pr <-> p = 1%:pr /\ q = 1%:pr.
Proof.
split; last by case=> -> ->; rewrite mulR1.
move=> /= pq1.
move: R1_neq_R0; rewrite -{1}pq1 => /eqP; rewrite mulR_neq0' => /andP[].
rewrite 2!prob_gt0'=> p0 q0.
case/leR_eqVlt: (prob_le1 p); last by
    move/(ltR_pmul2r q0); rewrite mul1R;
    move/(ltR_leR_trans); move/(_ _ (prob_le1 q)) /ltR_neqAle => [].
move=> p1.
case/leR_eqVlt: (prob_le1 q); last by
    move/(ltR_pmul2r p0); rewrite mul1R mulRC;
    move/(ltR_leR_trans); move/(_ _ (prob_le1 p)) /ltR_neqAle => [].
by move=> q1; split; apply val_inj.
Qed.

(* non-negative rationals *)
Record Qplus := mkRrat { num : nat ; den : nat }.

Definition Q2R (q : Qplus) := INR (num q) / INR (den q).+1.

Coercion Q2R : Qplus >-> R.

(*Lemma Rdiv_le a : 0 <= a -> forall r, 1 <= r -> a / r <= a.
Proof.
move=> Ha r Hr.
apply (@leR_pmul2l r); first lra.
rewrite /Rdiv mulRCA mulRV; last by apply/negP => /eqP ?; subst r; lra.
rewrite -mulRC; exact: leR_wpmul2r.
Qed.*)

Section dominance.

Definition dominates {A : Type} (Q P : A -> R) := locked (forall a, Q a = 0 -> P a = 0).

Local Notation "P '`<<' Q" := (dominates Q P).

Lemma dominatesP A (Q P : A -> R) : P `<< Q <-> forall a, Q a = 0 -> P a = 0.
Proof. by rewrite /dominates; unlock. Qed.

Lemma dominatesxx A (P : A -> R) : P `<< P.
Proof. by apply/dominatesP. Qed.

Let dominatesN A (Q P : A -> R) : P `<< Q -> forall a, P a != 0 -> Q a != 0.
Proof. by move/dominatesP => H a; apply: contra => /eqP /H ->. Qed.

Lemma dominatesE A (Q P : A -> R) a : P `<< Q -> Q a = 0 -> P a = 0.
Proof. move/dominatesP; exact. Qed.

Lemma dominatesEN A (Q P : A -> R) a : P `<< Q -> P a != 0 -> Q a != 0.
Proof. move/dominatesN; exact. Qed.

Lemma dominates_scale (A : finType) (Q P : A -> R) : P `<< Q ->
  forall k, k != 0 -> P `<< [ffun a : A => k * Q a].
Proof.
move=> PQ k k0; apply/dominatesP => a /eqP.
by rewrite ffunE mulR_eq0' (negbTE k0) /= => /eqP/(dominatesE PQ).
Qed.

Definition dominatesb {A : finType} (Q P : A -> R) := [forall b, (Q b == 0) ==> (P b == 0)].

End dominance.

Notation "P '`<<' Q" := (dominates Q P) : reals_ext_scope.
Notation "P '`<<b' Q" := (dominatesb Q P) : reals_ext_scope.

Module Rpos.
Record t := mk {
  v : R ;
  H : v >b 0 }.
Definition K (r : t) := H r.
Arguments K : simpl never.
Module Exports.
Notation Rpos := t.
Notation "r %:pos" := (@mk r (@K _)) : reals_ext_scope.
Coercion v : Rpos >-> R.
End Exports.
End Rpos.
Export Rpos.Exports.

Canonical Rpos_subType := [subType for Rpos.v].
Definition Rpos_eqMixin := Eval hnf in [eqMixin of Rpos by <:].
Canonical Rpos_eqType := Eval hnf in EqType Rpos Rpos_eqMixin.
Definition Rpos_choiceMixin := Eval hnf in [choiceMixin of Rpos by <:].
Canonical Rpos_choiceType := Eval hnf in ChoiceType Rpos Rpos_choiceMixin.

Definition mkRpos x H := @Rpos.mk x (introT (ltRP _ _) H).

Canonical Rpos1 := @mkRpos 1 Rlt_0_1.

Lemma Rpos_gt0 (x : Rpos) : 0 < x.
Proof. by case: x => p /= /ltRP. Qed.
Global Hint Resolve Rpos_gt0 : core.

Lemma Rpos_neq0 (x : Rpos) : val x != 0.
Proof. by case: x => p /=; rewrite /gtRb lt0R => /andP[]. Qed.

Lemma addRpos_gt0 (x y : Rpos) : x + y >b 0. Proof. exact/ltRP/addR_gt0. Qed.
Canonical addRpos x y := Rpos.mk (addRpos_gt0 x y).

Lemma mulRpos_gt0 (x y : Rpos) : x * y >b 0. Proof. exact/ltRP/mulR_gt0. Qed.
Canonical mulRpos x y := Rpos.mk (mulRpos_gt0 x y).

Lemma divRpos_gt0 (x y : Rpos) : x / y >b 0. Proof. exact/ltRP/divR_gt0. Qed.
Canonical divRpos x y := Rpos.mk (divRpos_gt0 x y).

Lemma Rpos_prob_Op1 (r q : Rpos) : 0 <= r / (r + q)%:pos <= 1.
Proof.
split; first exact/ltRW/divR_gt0.
apply leR_pdivr_mulr => //.
rewrite mul1R; exact/leR_addl/ltRW.
Qed.

Definition Rpos_prob (r q : Rpos) := Eval hnf in Prob.mk_ (Rpos_prob_Op1 r q).

Lemma Rpos_probC r q : Rpos_prob q r = (Rpos_prob r q).~%:pr.
Proof.
apply val_inj => /=; rewrite [in RHS]addRC onem_div ?addRK //.
exact: Rpos_neq0.
Qed.

Canonical oprob_Rpos (p : oprob) := @mkRpos p (oprob_gt0 p).

Lemma oprob_divRposxxy (x y : Rpos) : (0 < (x / (x + y)) < 1)%R.
Proof.
split; first by apply/divR_gt0.
rewrite ltR_pdivr_mulr ?mul1R; last exact/ltRP/addRpos_gt0.
by rewrite ltR_addl.
Qed.
Lemma prob_divRposxxy (x y : Rpos) : (0 <= (x / (x + y)) <= 1)%R.
Proof. by apply/oprob_prob/oprob_divRposxxy. Qed.
Canonical divRposxxt (x y : Rpos) :=
  Eval hnf in @Prob.mk _ (prob_probb (prob_divRposxxy x y)).
Canonical divRposxxt_oprob (x y : Rpos) :=
  Eval hnf in @OProb.mk _ (oprob_oprobb (oprob_divRposxxy x y)).


Module Rnneg.
Local Open Scope R_scope.
Record t := mk {
  v : R ;
  H : 0 <b= v }.
Definition K (r : t) := H r.
Arguments K : simpl never.
Module Exports.
Notation Rnneg := t.
Notation "r %:nng" := (@mk r (@K _)).
Coercion v : t >-> R.
End Exports.
End Rnneg.
Export Rnneg.Exports.

Canonical Rnneg_subType := [subType for Rnneg.v].
Definition Rnneg_eqMixin := Eval hnf in [eqMixin of Rnneg by <:].
Canonical Rnneg_eqType := Eval hnf in EqType Rnneg Rnneg_eqMixin.
Definition Rnneg_choiceMixin := Eval hnf in [choiceMixin of Rnneg by <:].
Canonical Rnneg_choiceType := Eval hnf in ChoiceType Rnneg Rnneg_choiceMixin.

Section Rnneg_lemmas.
Local Open Scope R_scope.

Definition mkRnneg x H := @Rnneg.mk x (introT (leRP _ _) H).

Canonical Rnneg0 := @mkRnneg 0 (leRR 0).
Canonical Rnneg1 := @mkRnneg 1 Rle_0_1.

Lemma Rnneg_0le (x : Rnneg) : 0 <= x.
Proof. by case: x => p /= /leRP. Qed.

Lemma addRnneg_0le (x y : Rnneg) : 0 <b= x + y.
Proof. apply/leRP/addR_ge0; apply/Rnneg_0le. Qed.
Canonical addRnneg x y := Rnneg.mk (addRnneg_0le x y).

Lemma mulRnneg_0le (x y : Rnneg) : 0 <b= x * y.
Proof. by apply/leRP/mulR_ge0; apply/Rnneg_0le. Qed.
Canonical mulRnneg x y := Rnneg.mk (mulRnneg_0le x y).
End Rnneg_lemmas.
