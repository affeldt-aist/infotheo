(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import Rstruct reals.
From mathcomp Require boolp.
From mathcomp Require Import all_algebra.
Require Import Reals Lra.
Require Import ssrR.
Import Order.TTheory Order.Syntax GRing.Theory Num.Theory.

(******************************************************************************)
(*              Additional lemmas and definitions about Coq reals             *)
(*                                                                            *)
(* Section reals_ext.                                                         *)
(*   various lemmas about up, Int_part, frac_part, Rabs define ceil and floor *)
(*                                                                            *)
(*  T ->R+ == finite functions that return non-negative reals.                *)
(* T ->R^+ == functions that return non-negative reals.                       *)
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
(*     Rnng == Type of non-negative reals                                     *)
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
Reserved Notation "x %:pos" (at level 2, format "x %:pos").
Reserved Notation "x %:nng" (at level 2, format "x %:nng").
Reserved Notation "[ 's_of' p , q ]" (format "[ 's_of'  p ,  q ]").
Reserved Notation "[ 'r_of' p , q ]" (format "[ 'r_of'  p ,  q ]").
Reserved Notation "[ 'p_of' r , s ]" (format "[ 'p_of'  r ,  s ]").
Reserved Notation "[ 'q_of' r , s ]" (format "[ 'q_of'  r ,  s ]").

Reserved Notation "{ 'Rpos' T }" (format "{ 'Rpos'  T }").

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

Lemma INR_Zabs_nat x : (0 <= x)%Z -> (Z.abs_nat x)%:R = IZR x.
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

Section nneg_finfun.
Variable (T : finType).

Record nneg_finfun := mkNNFinfun {
  nneg_ff :> {ffun T -> R} ;
  _ : [forall a, 0 <b= nneg_ff a] }.

Canonical nneg_finfun_subType := Eval hnf in [subType for nneg_ff].
Definition nneg_finfun_eqMixin := [eqMixin of nneg_finfun by <:].
Canonical nneg_finfun_eqType := Eval hnf in EqType _ nneg_finfun_eqMixin.
End nneg_finfun.

Notation "T '->R+' " := (nneg_finfun T) : reals_ext_scope.

Lemma nneg_finfun_ge0 (T : finType) (f : T ->R+) : forall a, 0 <= f a.
Proof. by case: f => f /= /forallP H a; apply/leRP/H. Qed.

Record nneg_fun (T : Type) := mkNNFun {
  nneg_f :> T -> R ;
  nneg_f_ge0 : forall a, 0 <= nneg_f a }.

Notation "T '->R^+' " := (nneg_fun T) : reals_ext_scope.

Lemma nneg_fun_eq {C : Type} (f g : C ->R^+) : nneg_f f = nneg_f g -> f = g.
Proof.
destruct f as [f Hf].
destruct g as [g Hg].
move=> /= ?; subst.
suff : Hf = Hg by move=> ->.
exact/boolp.Prop_irrelevance.
Qed.

Section onem.
From mathcomp Require Import ring.
Local Open Scope ring_scope.
Variable R : realType.
Implicit Types r s p q : R.

Definition onem r := 1 - r.
Local Notation "p '.~'" := (onem p).

Lemma onem0 : 0.~ = 1. Proof. by rewrite /onem subr0. Qed.

Lemma onem1 : 1.~ = 0. Proof. by rewrite /onem subrr. Qed.

Lemma onem_ge0 r : r <= 1 -> 0 <= r.~. Proof. move=> ?; by rewrite /onem subr_ge0. Qed.

Lemma onem_le1 r : 0 <= r -> r.~ <= 1.
Proof. move=> ?; by rewrite /onem ler_subl_addr -ler_subl_addl subrr. Qed.

Lemma onem_le  r s : r <= s <-> s.~ <= r.~.
Proof.
rewrite /onem; split=> sr.
 by rewrite ler_sub.
by move: sr; rewrite ler_subr_addl addrA ler_subl_addl ler_add2r.
Qed.

Lemma onem_lt  r s : r < s <-> s.~ < r.~.
Proof.
rewrite /onem; split.
Search (_ - _ < _ - _).
 by move=> sr; rewrite ler_lt_sub.
by rewrite ltr_subr_addl addrA ltr_subl_addl ltr_add2r.
Qed.

Lemma onemKC r : r + r.~ = 1.
Proof. 
by rewrite /onem addrC -addrA (addrC (-r) r) subrr addr0.
Qed.

Lemma onemK r : r.~.~ = r.
by rewrite /onem opprB addrA addrC addrA (addrC (-1) 1) subrr add0r.
Qed.

Lemma onemD p q : (p + q).~ = p.~ + q.~ - 1.
Proof.
by rewrite /onem (addrAC _ (1 - q) (-1)) subrKA opprD addrA.
Qed.

Lemma onemM p q : (p * q).~ = p.~ + q.~ - p.~ * q.~.
Proof. rewrite /onem; ring. Qed.

Lemma onem_div p q : q != 0 -> (p / q).~ = (q - p)  /q.
Proof.
by rewrite /onem; move=> q0; rewrite mulrBl divrr // unitfE.
Qed.


Lemma onem_prob r : 0 <= r <= 1 -> 0 <= r.~ <= 1.
Proof.
by move=> /andP [_0r r1]; apply /andP; split; [rewrite onem_ge0 | rewrite onem_le1].
Qed.

Lemma onem_oprob r : 0 < r < 1 -> 0 < r.~ < 1.
Proof.
rewrite /onem. move=> /andP [_0r r1]. apply /andP. split.
  by rewrite subr_gt0.
by rewrite -subr_gt0 opprB addrC -addrA addNr addr0.
Qed.

Lemma onem_eq0 r : r.~ = 0 <-> r = 1.
Proof.
rewrite /onem. split.
  by move=> /eqP; rewrite subr_eq0=> /eqP.
by move=> ->; rewrite subrr.
Qed.

Lemma onem_eq1 r : r.~ = 1 <-> r = 0.
Proof.
rewrite /onem. split.
  by move=> /esym /eqP; rewrite addrC -subr_eq subrr eq_sym oppr_eq0; move /eqP.
move=> ->. exact: subr0.
Qed.

Lemma onem_neq0 r : r.~ != 0 <-> r != 1.
Proof. by split; apply: contra => /eqP/onem_eq0/eqP. Qed.

Lemma onem_gt0 r : r < 1 -> 0 < r.~.
Proof. by rewrite /onem subr_gt0. Qed.

Lemma onem_lt1 r : 0 < r -> r.~ < 1.
Proof.
by rewrite /onem=> _0r; rewrite -subr_gt0 opprB addrC - addrA addNr addr0.
Qed.

Lemma subr_onem r s : r - s.~ = r + s - 1.
Proof. rewrite /onem. ring. Qed.

End onem.

Notation "p '.~'" := (onem p) : reals_ext_scope.

Local Open Scope ring_scope.
Module Prob.
Record t (R : realType) := mk {
  p :> R ;
  Op1 : 0 <= p <= 1 }.
Definition O1 (R : realType) (x : t R) : (0 <= p x <= 1) := Op1 x.
Arguments O1 : simpl never.
Definition mk_ (R : realType) (q : R) (Oq1 : (0 <= q <= 1)) := mk Oq1.
Module Exports.
Notation prob := t.
Notation "q %:pr" := (@mk _ q (@O1 _ _)).
Canonical prob_subType (R : realType) := Eval hnf in [subType for @p R].
Definition prob_eqMixin (R : realType) := [eqMixin of prob R by <:].
Canonical prob_eqType (R : realType) := Eval hnf in EqType (prob R) (prob_eqMixin R).
Definition prob_choiceMixin (R : realType) := [choiceMixin of (prob R) by <:].
Canonical prob_choiceType (R : realType) := Eval hnf in ChoiceType (prob R) (prob_choiceMixin R).

Definition prob_porderMixin (R : realType) := [porderMixin of (prob R) by <:].
Canonical prob_porderType (R : realType) := Eval hnf in POrderType ring_display (prob R) (prob_porderMixin R).

End Exports.
End Prob.
Export Prob.Exports.
Definition Probp (p : prob [realType of R]) : R := Prob.p p.
Coercion  Probp : prob >-> R.
Coercion Prob.p : prob >-> Real.sort.

Definition prob_of (R : realType) := 
  fun phT : phant (Real.sort R) => prob R.
Notation "{ 'prob' T }" := (prob_of (Phant T)) : reals_ext_scope.
Lemma probpK R p H : Prob.p (@Prob.mk R p H) = p. Proof. by []. Qed.

Section prob_lemmas.
Local Open Scope ring_scope .
Variable R : realType.

Lemma OO1 : ((0 <= 0 :> R) && (0 <= 1 :> R)). Proof. apply /andP; split => //. exact ler01. Qed.

Lemma O11 : ((0 <= 1 :> R) && (1 <= 1 :> R)). Proof. apply /andP; split => //. exact ler01. Qed.

Canonical prob0 := Eval hnf in Prob.mk OO1.
Canonical prob1 := Eval hnf in Prob.mk O11.
Canonical probcplt (p : prob R) := Eval hnf in Prob.mk (onem_prob (Prob.O1 p)).

Lemma prob_ge0 (p : prob R) : (0 <= p :> R).
Proof. by case: p => p /= /andP []. Qed.

Lemma prob_le1 (p : prob R) : ((p : R) <= 1).
Proof. by case: p => p /= /andP []. Qed.

Hint Resolve prob_ge0 : core.
Hint Resolve prob_le1 : core.

Implicit Types p q : prob R.

Lemma prob_gt0 p : p != 0%:pr <-> (0 < p :> R).
Proof.
rewrite lt_neqAle. split=>[H|/andP [ p0 _]].
  by rewrite eq_sym H /=.
by case: p p0 => p ?; apply: contra=> /eqP[/= ->].
Qed.

Lemma prob_gt0' p : p != 0 :> R <-> 0 < p :> R.
Proof. exact: prob_gt0. Qed.

Lemma prob_lt1 p : p != 1%:pr <-> p < 1 :> R.
Proof.
rewrite lt_neqAle; split=> [H|/andP [p1 _]].
  rewrite H /=; exact: prob_le1.
by case: p p1 => p ?; apply: contra => /eqP[/= ->].
Qed.

Lemma prob_lt1' p : p != 1 :> R <-> p < 1 :> R.
Proof. exact: prob_lt1. Qed.

Lemma prob_trichotomy p : p = 0%:pr \/ p = 1%:pr \/ (0 < p :> R) && (p < 1 :> R).
Proof.
have [/eqP ->|pneq0]:= boolP (p == 0%:pr); first by left.
right.
have [/eqP ->|pneq1] := boolP (p == 1%:pr); first by left.
by right; apply /andP; by rewrite -prob_gt0 -prob_lt1.
Qed.

Lemma probK p : p = (p.~).~%:pr.
Proof. by apply val_inj => /=; rewrite onemK. Qed.

Lemma probKC (p : prob R) : (p : R) + p.~ = 1 :> R.
Proof. by rewrite onemKC. Qed.


Lemma probadd_eq0 p q : (p : R) + (q : R) = 0 <-> p = 0%:pr /\ q = 0%:pr.
Proof.
split=> [/eqP |].
- by rewrite paddr_eq0 // => /andP [/eqP /val_inj -> /eqP /val_inj ->].
- by case => -> ->; rewrite addr0.
Qed.

Lemma probadd_neq0 p q : (p : R) + (q : R) != 0 <-> p != 0%:pr \/ q != 0%:pr.
Proof.
split.
- by rewrite paddr_eq0 // negb_and => /orP []; [left|right].
by case; apply: contra => /eqP/probadd_eq0 [] /eqP ? /eqP.
Qed.

Lemma probmul_eq1 p q : (p : R) * (q : R) = 1 <-> p = 1%:pr /\ q = 1%:pr.
Proof.
split => [/= pq1|[-> ->]]; last by rewrite mulr1.
move: (oner_neq0 R). rewrite -{1}pq1 mulf_eq0 negb_or => /andP[].
rewrite 2!prob_gt0'=> p0 q0.
have := prob_le1 p; rewrite le_eqVlt => /orP [/eqP p1|]; last first.
  rewrite -(ltr_pmul2r q0) mul1r => /lt_le_trans. 
  by move/(_ _ (prob_le1 q)); rewrite lt_neqAle pq1 eqxx.
move: pq1. rewrite p1 mul1r=> q1.
by split; apply: val_inj.
Qed.

End prob_lemmas.
Global Hint Resolve prob_ge0 : core.
Global Hint Resolve prob_le1 : core.
Arguments prob0 {R}.
Arguments prob1 {R}.


Lemma prob_IZR (p : positive) : R0 <= / IZR (Zpos p) <= R1.
Proof.
apply/leR2P; split; first exact/Rlt_le/Rinv_0_lt_compat/IZR_lt/Pos2Z.is_pos.
rewrite -[X in (_ <= X)%R]Rinv_1; apply Rle_Rinv => //.
- exact/IZR_lt/Pos2Z.is_pos.
- exact/IZR_le/Pos2Z.pos_le_pos/Pos.le_1_l.
Qed.

Canonical probIZR (p : positive) := Eval hnf in Prob.mk (prob_IZR p).

Definition divRnnm n m := (n%:R / (n + m)%:R) : R.
Local Open Scope ring_scope.
Lemma prob_divRnnm n m : (0 <= divRnnm n m <= 1).
Proof.
rewrite /divRnnm.
have [->|] := eqVneq n O; first rewrite mul0r //. exact: OO1.
have [/eqP ->|n0] := boolP (n == O); first by rewrite mul0r.
move=> _. apply /andP. split; first by rewrite divr_ge0 //; exact: ler0n.
rewrite ler_pdivr_mulr; first by rewrite mul1r ler_nat leq_addr.
by rewrite ltr0n addn_gt0 lt0n n0.
Qed.

Canonical probdivRnnm (n m : nat) :=
  Eval hnf in @Prob.mk _ (divRnnm n m) (prob_divRnnm n m).

Lemma prob_invn (m : nat) : (0 <= ((1 + m)%:R^-1 : R) <= 1).
Proof.
rewrite (_ : (1 + m)%:R^-1 = ((1%:R / (1 + m)%:R) : R)); last by rewrite mul1r.
exact: prob_divRnnm.
Qed.

Canonical probinvn (n : nat) :=
  Eval hnf in @Prob.mk _ ((1 + n)%:R ^-1) (prob_invn n).

Lemma prob_invp (p : {prob R}) : 0 <= 1 / (1 + p)%R <= 1.
Proof.
have ler01R := @ler01 [realType of R].
have le0p := prob_ge0 p.
have lt01p : 0 < 1 + (p : R); first by apply: ltr_spaddl => //; exact: ltr01.
have le01p : 0 <= 1 + (p : R); first by apply: addr_ge0.
by rewrite divr_ge0 // /= ler_pdivr_mulr // mul1r ler_addl.
Qed.

Definition Prob_invp (p : {prob R}) := Prob.mk (prob_invp p).

Lemma prob_mulR (p q : {prob R}) : (0 <= (p * q)%R <= 1).
Proof.
rewrite mulr_ge0 /= ?prob_ge0 //.
rewrite (_ : 1 = 1 * 1); last by rewrite mulr1.
by rewrite ler_pmul ?prob_ge0 ?prob_le1.
Qed.

Canonical probmulR (p q : {prob R}) :=
  Eval hnf in @Prob.mk _ (p * q)%R (prob_mulR p q).

Module OProb.
Record t (R : realType) := mk {
  p :> prob R;
  Op1 : 0 < (p: R) < 1 }.
Definition O1 (R : realType) (x : t R) : 0 < (p x: R) < 1 := Op1 x.
Arguments O1 : simpl never.
Module Exports.
Notation oprob := t.
Notation "q %:opr" := (@mk _ q%:pr (@O1 _ _)).
Canonical oprob_subType (R: realType) := Eval hnf in [subType for @p R].
Definition oprob_eqMixin (R: realType):= [eqMixin of oprob R by <:].
Canonical oprob_eqType (R:realType) := Eval hnf in EqType (oprob R) (oprob_eqMixin R).

Definition oprob_choiceMixin (R : realType) := [choiceMixin of (oprob R) by <:].
Canonical oprob_choiceType (R : realType) := Eval hnf in ChoiceType (oprob R) (oprob_choiceMixin R).

Definition oprob_porderMixin (R : realType) := [porderMixin of (oprob R) by <:].
Canonical oprob_porderType (R : realType) := Eval hnf in POrderType ring_display (oprob R) (oprob_porderMixin R).

End Exports.
End OProb.
Export OProb.Exports.
Definition OProbp (p : oprob [realType of R]) : R := OProb.p p.
Coercion OProbp : oprob >-> R.
Coercion OProb.p : oprob >-> Prob.t.

Canonical oprobcplt (R: realType)(p : oprob R) := Eval hnf in OProb.mk (onem_oprob (OProb.O1 p)).

Definition oprob_of (R : realType) := 
  fun phT : phant (Real.sort R) => oprob R.
Notation "{ 'oprob' T }" := (oprob_of (Phant T)) : reals_ext_scope.

Section oprob_lemmas.
Context (R : realType).
Implicit Types p q : oprob R.

Lemma oprob_gt0 p : 0 < p :> R.
Proof. by case: p => p /= /andP []. Qed.

Lemma oprob_lt1 p : p < 1 :> R.
Proof. by case: p => p /= /andP [] _ . Qed.

Lemma oprob_ge0 p : 0 <= p :> R. Proof. exact/ltW/oprob_gt0. Qed.

Lemma oprob_le1 p : p <= 1 :> R. Proof. exact/ltW/oprob_lt1. Qed.

Lemma oprob_neq0 p : p != 0 :> R.
Proof. by move/gt_eqF :(oprob_gt0 p) => ->. Qed.

Lemma oprob_neq1 p : p != 1 :> R.
Proof. by move/gt_eqF : (oprob_lt1 p); rewrite eq_sym => ->. Qed.

Lemma oprobK p : p = (p.~).~%:opr.
Proof. by apply/val_inj/val_inj=> /=; rewrite onemK. Qed.

Lemma prob_trichotomy' p (P : prob R -> Prop) :
  P 0%:pr -> P 1%:pr -> (forall o : oprob R, P o) -> P p.
Proof.
move=> p0 p1 po.
have [-> //|[->//|p01]] := prob_trichotomy p.
exact: po (OProb.mk p01).
Qed.

Lemma oprobadd_gt0 p q : 0 < (p : R) + (q : R).
Proof. exact/addr_gt0/oprob_gt0/oprob_gt0. Qed.

Lemma oprobadd_neq0 p q : (p : R) + (q : R) != 0.

Proof. by rewrite gt_eqF // oprobadd_gt0. Qed.

End oprob_lemmas.

Global Hint Resolve oprob_neq0 : core.
Global Hint Resolve oprob_neq1 : core.

Lemma oprob_divRnnm n m : (0 < n)%nat -> (0 < m)%nat -> (0 < divRnnm n m < 1).
Proof.
rewrite /divRnnm. move=> _0n _0m. apply/ andP.
have lt0addnm : 0 < (n + m)%:R; first by move=> R; rewrite ltr0n addn_gt0 _0n orTb.
split; first by apply divr_gt0; [rewrite ltr0n |exact: lt0addnm ].
rewrite ltr_pdivr_mulr; last exact: lt0addnm.
by rewrite mul1r ltr_nat -addn1 leq_add2l.
Qed.

Lemma oprob_mulR (p q : {oprob R}) : 0 < (p * q)%R < 1.
Proof.
apply/andP. split; first exact/mulr_gt0/oprob_gt0/oprob_gt0.
by apply: mulr_ilt1;
  [exact/oprob_ge0 | exact/oprob_ge0 | exact/oprob_lt1 | exact/oprob_lt1].
Qed.
  
Canonical oprobmulR (p q : {oprob R}) :=
  Eval hnf in @OProb.mk _ ((p: R) * q)%:pr (oprob_mulR p q).

Record Qplus := mkRrat { num : nat ; den : nat }.

Definition Q2R (q : Qplus) := INR (num q) / INR (den q).+1.

(*TODO: yoshihiro503
Coercion Q2R : Qplus >-> R.*)

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
Record t (R: realType) := mk {
  v : R ;
  H : v > 0 }.
Definition K (R : realType) (r : t R) := H r.
Arguments K : simpl never.
Module Exports.
Notation Rpos := t.
Notation "r %:pos" := (@mk _ r (@K _)) : reals_ext_scope.
Definition Rposv (x : Rpos [realType of R]) : R := Rpos.v x.
Coercion Rposv : Rpos >-> R.
End Exports.
End Rpos.
Export Rpos.Exports.

Canonical Rpos_subType (R: realType) := [subType for @Rpos.v R].
Definition Rpos_eqMixin (R: realType) := Eval hnf in [eqMixin of Rpos R by <:].
Canonical Rpos_eqType (R: realType) := Eval hnf in EqType (Rpos R) (Rpos_eqMixin R).
Definition Rpos_choiceMixin (R: realType) := Eval hnf in [choiceMixin of Rpos R by <:].
Canonical Rpos_choiceType (R: realType) := Eval hnf in ChoiceType (Rpos R) (Rpos_choiceMixin R).

Definition mkRpos (R: realType) (x: R) H := @Rpos.mk _ x H.

Definition Rpos_of (R : realType) := 
  fun phT : phant (Real.sort R) => Rpos R.
Notation "{ 'Rpos' T }" := (Rpos_of (Phant T)) : reals_ext_scope.

Canonical Rpos1 R := @Rpos.mk R 1 ltr01.

Lemma Rpos_gt0 (x : {Rpos R}) : 0 < (x : R). Proof. by case: x => p /=. Qed.
Global Hint Resolve Rpos_gt0 : core.

Lemma Rpos_neq0 (x : {Rpos R}) : val x != 0.
Proof. by case: x => p /=; exact: lt0r_neq0. Qed.

Lemma addRpos_gt0 (x y : {Rpos R}) : (x : R) + y > 0.
Proof. exact: addr_gt0. Qed.
Canonical addRpos x y := Rpos.mk (addRpos_gt0 x y).

Lemma mulRpos_gt0 (x y : {Rpos R}) : (x:R) * y > 0. Proof. exact/mulr_gt0. Qed.
Canonical mulRpos x y := Rpos.mk (mulRpos_gt0 x y).

Lemma divRpos_gt0 (x y : {Rpos R}) : (x:R) / (y:R) > 0.
Proof. exact/divr_gt0. Qed.
Canonical divRpos x y := Rpos.mk (divRpos_gt0 x y).

Canonical oprob_Rpos (p : {oprob R}) := @mkRpos _ p (oprob_gt0 p).

Lemma oprob_divRposxxy (x y : {Rpos R}) : 0 < (x: R) / ((x: R) + y) < 1.
Proof.
apply/andP. split; first by apply:divr_gt0 =>//; exact: addRpos_gt0.
rewrite ltr_pdivr_mulr; last exact:addRpos_gt0.
by rewrite mul1r ltr_addl.
Qed.

Lemma prob_divRposxxy (x y : {Rpos R}) : 0 <= (x:R) / ((x:R) + y) <= 1.
Proof.
move/andP: (oprob_divRposxxy x y) => [gt0 lt1].
by rewrite ltW //=; rewrite ltW.
Qed.

Canonical divRposxxy (x y : {Rpos R}) :=
  Eval hnf in Prob.mk (prob_divRposxxy x y).

Canonical divRposxxy_oprob (x y : {Rpos R}) :=
  Eval hnf in OProb.mk (oprob_divRposxxy x y).

Lemma divRposxxyC r q : divRposxxy q r = (divRposxxy r q).~%:pr.
Proof.
apply val_inj => /=. rewrite [in RHS]addrC onem_div ?addrK //.
exact/lt0r_neq0/addRpos_gt0.
Qed.

Lemma onem_divRxxy (r q : {Rpos R}) : ((r:R) / ((r:R) + q)).~ = (q:R) / ((q:R) + r).
Proof.
  rewrite /onem. apply /eqP.
  by rewrite subr_eq (addrC (r: R)) -mulrDl mulrV // unitf_gt0 // addRpos_gt0.
Qed.

Module Rnng.
Record t (R: realType):= mk {
  v : R ;
  H : 0 <= v }.
Definition K (R: realType) (r : t R) := H r.
Arguments K : simpl never.
Module Exports.
Notation Rnng := t.
Notation "r %:nng" := (@mk _ r (@K _)).
Definition Rnngv (x : Rnng [realType of R]) : R := Rnng.v x.
Coercion Rnngv : t >-> R.
End Exports.
End Rnng.
Export Rnng.Exports.

Canonical Rnng_subType (R: realType) := [subType for @Rnng.v R].
Definition Rnng_eqMixin (R: realType) := Eval hnf in [eqMixin of Rnng R by <:].
Canonical Rnng_eqType (R: realType) := Eval hnf in EqType (Rnng R) (Rnng_eqMixin R).
Definition Rnng_choiceMixin (R: realType) := Eval hnf in [choiceMixin of Rnng R by <:].
Canonical Rnng_choiceType (R: realType) := Eval hnf in ChoiceType (Rnng R) (Rnng_choiceMixin R).

Section Rnng_theory.

Definition mkRnng (R: realType) x H := @Rnng.mk R x H.

Definition Rnng_of (R : realType) :=
  fun phT : phant (Real.sort R) => Rnng R.
Notation "{ 'Rnng' T }" := (Rnng_of (Phant T)) : reals_ext_scope.

Lemma Rnng_ge0 (x : {Rnng R}) : 0 <= (x:R).
Proof. by case: x => p. Qed.
Local Hint Resolve Rnng_ge0 : core.

Canonical Rnng0 R := Eval hnf in @mkRnng R 0 (lexx 0).
Canonical Rnng1 R := Eval hnf in @mkRnng R 1 ler01.

Lemma addRnng_ge0 (x y : {Rnng R}) : 0 <= (x:R) + y.
Proof. exact: addr_ge0. Qed.
Canonical addRnneg x y := Rnng.mk (addRnng_ge0 x y).

Lemma mulRnng_ge0 (x y : {Rnng R}) : 0 <= (x:R) * y.
Proof. exact: mulr_ge0. Qed.
Canonical mulRnneg x y := Rnng.mk (mulRnng_ge0 x y).

End Rnng_theory.

Global Hint Resolve Rnng_ge0 : core.

Definition s_of_pq (p q : {prob R}) : {prob R} := locked (p.~ * q.~).~%:pr.

Notation "[ 's_of' p , q ]" := (s_of_pq p q) : reals_ext_scope.

Lemma s_of_pqE (p q : {prob R}) : [s_of p, q] = (p.~ * q.~).~ :> R.
Proof. by rewrite /s_of_pq; unlock. Qed.

Lemma s_of_pq_oprob (p q : {oprob R}) : 0 < ([s_of p, q]:R) < 1.
Proof.
rewrite s_of_pqE (_ : (p.~ * q.~).~ = (p.~ * q.~).~%:opr) //=; exact: OProb.O1.
Qed.
Canonical oprob_of_s_of_pq (p q : {oprob R}) := Eval hnf in @OProb.mk _ _ (s_of_pq_oprob p q).

Lemma s_of_p0 (p : {prob R}) : [s_of p, 0%:pr] = p :> R.
Proof. by rewrite s_of_pqE onem0 mulr1 onemK. Qed.

Lemma s_of_0q (q : {prob R}) : [s_of 0%:pr, q] = q :> R.
Proof. by rewrite s_of_pqE onem0 mul1r onemK. Qed.

Lemma s_of_p1 (p : {prob R}) : [s_of p, 1%:pr] = 1%:pr :> R.
Proof. by rewrite s_of_pqE onem1 mulr0 onem0. Qed.

Lemma s_of_1q (q : {prob R}) : [s_of 1%:pr, q] = 1%:pr :> R.
Proof. by rewrite s_of_pqE onem1 mul0r onem0. Qed.

Lemma s_of_pqE' (p q : {prob R}) : [s_of p, q] = (p:R) + p.~ * q :> R.
Proof. rewrite s_of_pqE /= /onem.
rewrite !mulrBl !mulrBr !mul1r !mulr1.
rewrite -addrA opprB. 
rewrite -(add0r (1 - (1 + _))) addrA (addrKA 1 0) add0r.
by rewrite (addrC (-(q:R))) 2!opprB !addrA (addrC (q:R) p).
Qed.

Lemma addr_gt0wl : forall [R : numDomainType] [x y : R],
    0 < x -> 0 <= y -> 0 < x + y.
Proof.
Admitted.

Lemma probR_ge0 (p: {prob R}) : 0 <= p :> R. Proof. exact: prob_ge0. Qed.
Global Hint Resolve probR_ge0 : core.
Lemma probR_le1 (p: {prob R}) : p <= 1 :> R. Proof. exact: prob_le1. Qed.
Global Hint Resolve probR_le1 : core.

Lemma s_of_gt0 (p q: {prob R}) : p != 0%:pr -> 0 < [s_of p, q] :> R.
Proof.
move=> ?; rewrite s_of_pqE';
  apply: addr_gt0wl; [exact/prob_gt0 | apply: mulr_ge0=>//].
exact: onem_ge0.
Qed.

Lemma s_of_gt0_oprob (p : {oprob R}) (q : {prob R}) : 0 < [s_of p, q] :> R.
Proof. by apply/s_of_gt0/oprob_neq0. Qed.

Lemma ge_s_of (p q : {prob R}) : p <= [s_of p, q] :> R.
Proof.
rewrite s_of_pqE' addrC -ler_subl_addr subrr.
apply mulr_ge0 => //. exact: onem_ge0.
Qed.

Lemma r_of_pq_prob (p q : {prob R}) : 0 <= (p:R) / ([s_of p, q]:R) <= 1.
Proof.
case/boolP : (p == 0%:pr :> {prob R}) => [/eqP p0 | p0].
  by rewrite p0 mul0r lexx ler01.
case/boolP : (q == 0%:pr :> {prob R}) => [/eqP q0 | q0].
  by rewrite q0 (s_of_p0 p) divrr // ler01 lexx.

rewrite divr_ge0 // ler_pdivr_mulr ?mul1r; [exact: ge_s_of | exact: s_of_gt0].
Qed.

Definition r_of_pq (p q : {prob R}) : {prob R} := locked (Prob.mk (r_of_pq_prob p q)).

Notation "[ 'r_of' p , q ]" := (r_of_pq p q) : reals_ext_scope.

Lemma r_of_pqE (p q : {prob R}) : [r_of p, q] = (p:R) / ([s_of p, q]:R) :> R.
Proof. by rewrite /r_of_pq; unlock. Qed.

#[global] Hint Extern 0 (is_true (0 < Probp (OProb.p _))) => solve [apply: oprob_gt0] : core.
#[global] Hint Extern 0 (is_true (Probp (OProb.p _) < 1)) => solve [apply: oprob_lt1] : core.
#[global] Hint Extern 0 (is_true (OProb.p _ != 0)) => solve [exact: oprob_neq0] : core.

Lemma r_of_pq_oprob (p q : {oprob R}) : 0 < ([r_of p, q]:R) < 1.
Proof.
rewrite r_of_pqE.
rewrite divr_gt0 //; last by rewrite s_of_gt0 // oprob_neq0.
rewrite ltr_pdivr_mulr ?mul1r; last by rewrite s_of_gt0 // oprob_neq0.
rewrite andTb lt_neqAle ge_s_of andbT.
rewrite s_of_pqE' lt_eqF // ltr_addl.
by apply/oprob_gt0.
Qed.
Canonical oprob_of_r_of_pq (p q : {oprob R}) := Eval hnf in @OProb.mk _ _ (r_of_pq_oprob p q).

Lemma r_of_p0 (p : {prob R}) : p != 0%:pr -> [r_of p, 0%:pr] = 1%:pr :> R.
Proof. by move=> p0; rewrite r_of_pqE s_of_p0 divrr. Qed.

Lemma r_of_p0_oprob (p : {oprob R}) : [r_of p, 0%:pr] = 1%:pr :> R.
Proof. by apply/r_of_p0/oprob_neq0. Qed.

Lemma r_of_0q (q : {prob R}) : [r_of 0%:pr, q] = 0%:pr :> R.
Proof. by rewrite r_of_pqE mul0r. Qed.

Lemma r_of_p1 (p : {prob R}) : [r_of p, 1%:pr] = p :> R.
Proof. by rewrite r_of_pqE s_of_p1 divr1. Qed.

Lemma r_of_1q (q : {prob R}) : [r_of 1%:pr, q] = 1%:pr :> R.
Proof. by rewrite r_of_pqE s_of_1q divr1. Qed.

Lemma p_is_rs (p q : {prob R}) : p = ([r_of p, q]:R) * [s_of p, q] :> R.
Proof.
case/boolP : (p == 0%:pr :> {prob R}) => p0; first by rewrite (eqP p0) r_of_0q mul0r.
case/boolP : (q == 0%:pr :> {prob R}) => q0.
  by rewrite (eqP q0) s_of_p0 r_of_p0 // mul1r.
rewrite r_of_pqE -mulrA mulVr ?mulr1 //.
by apply/unitf_gt0/s_of_gt0.
Qed.

Lemma r_of_pq_is_r (p q r s : {prob R}) : r != 0%:pr -> s != 0%:pr ->
  p = (r:R) * s :> R -> s.~ = p.~ * q.~ -> [r_of p, q] = r :> R.
Proof.
move=> r0 s0 H1 H2. rewrite r_of_pqE s_of_pqE.
by rewrite -H2 onemK H1 /= -mulrA divff // mulr1.
Qed.

Lemma r_of_pq_is_r_oprob (p q : {prob R}) (r s : {oprob R}) :
  p = (r:R) * s :> R -> s.~ = p.~ * q.~ -> [r_of p, q] = r :> R.
Proof. apply/r_of_pq_is_r/oprob_neq0/oprob_neq0. Qed.

Lemma p_of_rs_prob (r s : {prob R}) : 0 <= (r:R) * s <= 1.
Proof.
move: r s => -[] r /andP [] /leRP r0 /leRP r1 -[] s /= /andP [] /leRP s0 /leRP s1.
apply/andP; split; apply/leRP; [exact/mulR_ge0 | rewrite -(mulR1 1); exact: leR_pmul].
Qed.

Definition p_of_rs (r s : {prob R}) : {prob R} := locked (Prob.mk (p_of_rs_prob r s)).

Notation "[ 'p_of' r , s ]" := (p_of_rs r s) : reals_ext_scope.

Lemma p_of_rsE (r s : {prob R}) : [p_of r, s] = (r:R) * s :> R.
Proof. by rewrite /p_of_rs; unlock. Qed.

Lemma p_of_rs_oprob (r s : {oprob R}) : 0 < ([p_of r, s]:R) < 1.
Proof. by rewrite p_of_rsE; apply/OProb.O1. Qed.
Canonical oprob_of_p_of_rs (r s : {oprob R}) := Eval hnf in @OProb.mk _ _ (p_of_rs_oprob r s).

Lemma p_of_r1 (r : {prob R}) : [p_of r, 1%:pr] = r :> R.
Proof. by rewrite p_of_rsE mulr1. Qed.

Lemma p_of_1s (s : {prob R}) : [p_of 1%:pr, s] = s :> R.
Proof. by rewrite p_of_rsE mul1r. Qed.

Lemma p_of_r0 (r : {prob R}) : [p_of r, 0%:pr] = 0%:pr :> R.
Proof. by rewrite p_of_rsE mulr0. Qed.

Lemma p_of_0s (s : {prob R}) : [p_of 0%:pr, s] = 0%:pr :> R.
Proof. by rewrite p_of_rsE mul0r. Qed.

Lemma p_of_rsC (r s : {prob R}) : [p_of r, s] = [p_of s, r] :> R.
Proof. by rewrite !p_of_rsE mulrC. Qed.

Lemma p_of_neq1 (p q : {prob R}) : 0 < (p:R) < 1 -> [p_of q, p] != 1%:pr :> R.
Proof.
move/andP. case=> p0 p1. apply/eqP => pq1. move: (p1).
rewrite [X in _ < X -> _](_ : _ = Probp 1%:pr) //.
rewrite -pq1 p_of_rsE -ltr_pdivr_mulr // divff; last exact: lt0r_neq0.
apply/negP. by rewrite -leNgt.
Qed.

Lemma p_of_rs1 (r s : {prob R}) :
  ([p_of r, s] == 1%:pr :> {prob R}) = ((r == 1%:pr) && (s == 1%:pr)).
Proof.
(*TODO: 
apply/idP/idP; last by case/andP => /eqP -> /eqP ->; rewrite p_of_r1.
move/eqP/(congr1 Prob.p); rewrite /= p_of_rsE => /eqP.
apply contraLR => /nandP.
wlog : r s / r != 1%:pr by move=> H [|] ?; [|rewrite mulRC]; rewrite H //; left.
move=> r1 _.
have [/eqP->|/prob_gt0/ltR_neqAle[/nesym r0 _]] := boolP (r == 0%:pr :> prob).
  by rewrite mul0R eq_sym; apply/eqP.
apply/eqP => /(@eqR_mul2r (/ r)).
move/(_ (invR_neq0 _ r0)).
rewrite mulRAC mulRV ?mul1R; last exact/eqP.
move/eqP/prob_gt0 in r0.
move=> srV; move: (prob_le1 s); rewrite {}srV.
rewrite invR_le1 // => r_le1.
move: (prob_le1 r) => le_r1.
by move/eqP : r1; apply; apply/val_inj; apply eqR_le.
Qed.
*)
Admitted.


Lemma p_of_rs1P r s : reflect (r = 1%:pr /\ s = 1%:pr) ([p_of r, s] == 1%:pr).
Proof.
move: (p_of_rs1 r s) ->.
apply: (iffP idP);
  [by case/andP => /eqP -> /eqP -> | by case => -> ->; rewrite eqxx].
Qed.

Lemma q_of_rs_prob (r s : {prob R}) : 0 <= (r.~ * s) / ([p_of r, s]:R).~ <= 1.
Proof.
case/boolP : (r == 1%:pr :> {prob R}) => r1.
  rewrite (eqP r1) onem1 mul0r mul0r; apply/andP; split; apply/leRP => //; exact/leRR.
case/boolP : (s == 1%:pr :> {prob R}) => s1.
  by rewrite (eqP s1) mulr1 p_of_r1 divff ?onem_neq0 // ler01 lexx.
rewrite divr_ge0.
  - rewrite andTb ler_pdivr_mulr ?mul1r.
    + by rewrite p_of_rsE {2}/onem ler_subr_addr -mulrDl addrC onemKC mul1r.
    + rewrite p_of_rsE onem_gt0 //. apply: mulr_ilt1 => //;
        by [rewrite -prob_lt1| rewrite -prob_lt1].
  - by apply: mulr_ge0 => //; rewrite onem_ge0 //.
  - by rewrite p_of_rsE onem_ge0 //; exact: mulr_ile1.
Qed.

(* === 2023 03/31 ここまで === *)
Definition q_of_rs (r s : prob) : prob := locked (Prob.mk (q_of_rs_prob r s)).

Notation "[ 'q_of' r , s ]" := (q_of_rs r s) : reals_ext_scope.

Lemma q_of_rsE (r s : prob) : [q_of r, s] = (r.~ * s) / [p_of r, s].~ :> R.
Proof. by rewrite /q_of_rs; unlock. Qed.

Lemma q_of_rs_oprob (r s : oprob) : 0 <b [q_of r, s] <b 1.
Proof.
rewrite q_of_rsE p_of_rsE.
have->: r.~ * s / (r * s).~ = (s.~ / (r * s).~).~
  by rewrite /onem; field; move/eqP: (oprob_neq0 ((r * s).~)%:opr).
apply onem_oprob.
apply/andP; split; apply/ltRP.
- by apply/divR_gt0/oprob_gt0/oprob_gt0.
- apply/(@ltR_pmul2r (r * s).~); first by apply/oprob_gt0.
  rewrite divRE mulRAC -mulRA mulRV ?oprob_neq0 // mulR1 mul1R.
  rewrite -onem_lt.
  by rewrite -{2}(mul1R s) ltR_pmul2r; [apply/oprob_lt1 | apply/oprob_gt0].
Qed.
Canonical oprob_of_q_of_rs (r s : oprob) := Eval hnf in OProb.mk (q_of_rs_oprob r s).

Lemma q_of_r0 (r : prob) : [q_of r, 0%:pr] = 0%:pr.
Proof. by apply/val_inj => /=; rewrite q_of_rsE mulR0 div0R. Qed.

Lemma q_of_r1 (r : prob) : r != 1%:pr -> [q_of r, 1%:pr] = 1%:pr.
Proof.
move=> r1.
by apply/val_inj => /=; rewrite q_of_rsE /= mulR1 p_of_r1 divRR // onem_neq0.
Qed.

Lemma q_of_1s (s : prob) : [q_of 1%:pr, s] = 0%:pr.
Proof. by apply/val_inj => /=; rewrite q_of_rsE onem1 mul0R div0R. Qed.

Lemma pq_is_rs (p q : prob) : p.~ * q = [r_of p, q].~ * [s_of p, q].
Proof.
case/boolP : (p == 0%:pr :> prob) => p0.
  by rewrite (eqP p0) onem0 mul1R r_of_0q onem0 mul1R s_of_0q.
rewrite r_of_pqE [in RHS]mulRBl mul1R.
rewrite /Rdiv -mulRA mulVR ?mulR1; last first.
  rewrite prob_gt0; exact/s_of_gt0.
by rewrite s_of_pqE' addRC addRK.
Qed.

Lemma s_of_pqK r s : [p_of r, s] != 1%:pr ->
  [s_of [p_of r, s], [q_of r, s]] = s.
Proof.
move=> H.
apply/val_inj; rewrite /= s_of_pqE p_of_rsE q_of_rsE p_of_rsE /=.
rewrite /onem; field.
rewrite subR_eq0; apply/eqP; apply: contra H => /eqP rs1.
by apply/eqP/val_inj; rewrite /= p_of_rsE.
Qed.

Lemma s_of_pqK_oprob (r s : oprob) : [s_of [p_of r, s], [q_of r, s]] = s.
Proof. apply/s_of_pqK/oprob_neq1. Qed.

Lemma r_of_pqK (r s : prob) : [p_of r, s] != 1%:pr -> s != 0%:pr ->
  [r_of [p_of r, s], [q_of r, s]] = r.
Proof.
move=> H1 s0; apply/val_inj => /=.
rewrite !(r_of_pqE,s_of_pqE,q_of_rsE,p_of_rsE) /onem; field.
split; last first.
  by rewrite 2!subRB subRR add0R mulRBl mul1R addRC subRK; exact/eqP.
rewrite subR_eq0 => /esym.
apply/eqP; apply: contra H1 => /eqP H1.
by apply/eqP/val_inj; rewrite /= p_of_rsE.
Qed.

Lemma r_of_pqK_oprob (r s : oprob) : [r_of [p_of r, s], [q_of r, s]] = r.
Proof. apply/r_of_pqK/oprob_neq0/oprob_neq1. Qed.

Lemma s_of_Rpos_probA (p q r : Rpos) :
  [s_of (p / (p + (q + r)))%:pos%:pr, (q / (q + r))%:pos%:pr] =
  ((p + q) / (p + q + r))%:pos%:pr.
Proof.
apply val_inj; rewrite /= s_of_pqE /onem /=; field.
by split; exact/eqP/Rpos_neq0.
Qed.

Lemma r_of_Rpos_probA (p q r : Rpos) :
  [r_of (p / (p + (q + r)))%:pos%:pr, (q / (q + r))%:pos%:pr] =
  (p / (p + q))%:pos%:pr.
Proof.
apply/val_inj; rewrite /= r_of_pqE s_of_pqE /onem /=; field.
do 3 (split; first exact/eqP/Rpos_neq0).
rewrite (addRC p (q + r)) addRK {4}[in q + r]addRC addRK.
rewrite mulRC -mulRBr (addRC _ p) addRA addRK mulR_neq0.
split; exact/eqP/Rpos_neq0.
Qed.
