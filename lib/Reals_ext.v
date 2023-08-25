(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssrnum ssralg.
From mathcomp Require Import all_algebra vector reals normedtype ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
Require Import ssrR realType_ext.
Require Import Reals Lra.

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
Delimit Scope R_scope with coqR.

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
Implicit Types r s p q : R.

Definition Ronem r := @onem real_realType r.
(*Local Notation "p '.~'" := (Ronem p).*)

Lemma onem0 : 0.~ = 1. Proof. by rewrite /Ronem onem0. Qed.

Lemma onem1 : 1.~ = 0. Proof. by rewrite /Ronem onem1. Qed.

Lemma onem_ge0 r : r <= 1 -> 0 <= r.~.
Proof. rewrite /Ronem; move/RleP => r1; exact/RleP/onem_ge0. Qed.

Lemma onem_le1 r : 0 <= r -> r.~ <= 1.
Proof. move/RleP=> ?; rewrite /Ronem. exact/RleP/onem_le1. Qed.

Lemma onem_le  r s : r <= s <-> s.~ <= r.~.
Proof.
Admitted.

Lemma onem_lt  r s : r < s <-> s.~ < r.~.
(*Proof. by rewrite /onem; split=> ?; lra. Qed.*)
Admitted.

Lemma onemKC r : r + r.~ = 1. (*TODO Proof. rewrite /onem; by field. Qed.*)
Admitted.

Lemma onemK r : r.~.~ = r.
(*Proof. by rewrite /onem subRBA addRC addRK. Qed.*)
Admitted.

Lemma onemD p q : (p + q).~ = p.~ + q.~ - 1.
(*Proof. rewrite /onem; field. Qed.*)
Admitted.

Lemma onemM p q : (p * q).~ = p.~ + q.~ - p.~ * q.~.
(*Proof. rewrite /onem; field. Qed.*)
Admitted.

Lemma onem_div p q : q != 0 -> (p / q)%coqR.~ = (q - p)  /q.
Proof.
Admitted.
(*TODO
move=> Hq.
rewrite /nonem.
rewrite /Rdiv.
rewrite mulRDl.
rewrite mulNR.
rewrite -/(q / q).
rewrite divRR//.
Qed.*)

Lemma onem_prob r : R0 <b= r <b= R1 -> R0 <b= r.~ <b= R1.
Proof.
(*by case/leR2P=> ? ?; apply/leR2P; split;
   [rewrite leR_subr_addr add0R | rewrite leR_subl_addr -(addR0 1) leR_add2l].
Qed.*)
Admitted.

Lemma onem_oprob r : R0 <b r <b R1 -> R0 <b r.~ <b R1.
(*Proof.
by case/ltR2P=> ? ?; apply/ltR2P; split;
   [rewrite ltR_subr_addr add0R | rewrite ltR_subl_addr -(addR0 1) ltR_add2l].
Qed.*)
Admitted.

Lemma onem_eq0 r : r.~ = 0 <-> r = 1. (*Proof. rewrite /onem; lra. Qed.*)
Admitted.

Lemma onem_eq1 r : r.~ = 1 <-> r = 0. (*Proof. rewrite /onem; lra. Qed.*)
Admitted.

Lemma onem_neq0 r : r.~ != 0 <-> r != 1.
(*Proof. by split; apply: contra => /eqP/onem_eq0/eqP. Qed.*)
Admitted.

Lemma onem_gt0 r : r < 1 -> 0 < r.~. (*Proof. rewrite /onem; lra. Qed.*)
Admitted.

Lemma onem_lt1 r : 0 < r -> r.~ < 1. (*Proof. rewrite /onem; lra. Qed.*)
Admitted.

Lemma subR_onem r s : r - s.~ = r + s - 1.
(*Proof. by rewrite /onem -addR_opp oppRB addRA. Qed.*)
Admitted.

End onem.
(*Definition Ronem (p: R) := (@onem real_realType p).*)
(*Notation "p '.~'" := (Ronem p) : reals_ext_scope.*)

Module ProbR.
Definition mk_ (q : R) (Oq1 : 0 <= q <= 1) : {prob R}. (*TODO *) Admitted.
End ProbR.

(*Definition prob := prob real_realType.*)
(*Definition prob_coercion : @prob [realType of R] -> R := @Prob.p real_realType.
Coercion prob_coercion : prob >-> R.

#[global] Hint Extern 0 (Rle (IZR Z0) _) =>
  solve [apply/RleP/prob_ge0] : core.
#[global] Hint Extern 0 (Rle _ (IZR (Zpos xH))) =>
  solve [apply/RleP/prob_le1] : core.*)

(*Lemma probpK p H : Prob.p (@Prob.mk p H) = p. Proof. by []. Qed.

Lemma OO1 : R0 <b= R0 <b= R1. Proof. apply/leR2P; lra. Qed.

Lemma O11 : R0 <b= R1 <b= R1. Proof. apply/leR2P; lra. Qed.

Canonical prob0 := Eval hnf in Prob.mk OO1.
Canonical prob1 := Eval hnf in Prob.mk O11.
Canonical probcplt (p : prob) := Eval hnf in Prob.mk (onem_prob (Prob.O1 p)).

Lemma prob_ge0 (p : prob) : 0 <= p.
Proof. by case: p => p /= /leR2P[]. Qed.
Global Hint Resolve prob_ge0 : core.

Lemma prob_le1 (p : prob) : p <= 1.
Proof. by case: p => p /= /leR2P[]. Qed.
Global Hint Resolve prob_le1 : core.*)

(*Reserved Notation "{ 'prob' T }" (at level 0, format "{ 'prob'  T }").
Definition prob_of (R : realType) := fun phT : phant (Num.NumDomain.sort (*Real.sort*)R) => @prob R.*)
Notation "{ 'prob' T }" := (@prob_of _ (Phant T)).
Definition probR_coercion (p : {prob R}) : R := Prob.p p.
Local Coercion probR_coercion : prob_of >-> R.

Lemma probR_ge0 (p : {prob R}) : 0 <= p. Proof. exact/RleP/prob_ge0. Qed.
Lemma probR_le1 (p : {prob R}) :  p <= 1. Proof. exact/RleP/prob_le1. Qed.
#[global] Hint Extern 0 (Rle (IZR Z0) _) => solve [exact/probR_ge0] : core.
#[global] Hint Extern 0 (Rle _ (IZR (Zpos xH))) => solve [exact/probR_le1] : core.

Section prob_lemmas.
Implicit Types p q : {prob R}.

Canonical probR0 := Eval hnf in (@Prob.mk real_realType R0 (@OO1 _)).
Canonical probR1 := Eval hnf in (@Prob.mk real_realType R1 (@O11 _)).

Lemma probR_gt0 p : p != 0%:pr <-> 0 < p.
Proof.
rewrite ltR_neqAle; split=> [H|[/eqP p0 _]].
split => //; exact/nesym/eqP.
by case: p p0 => p ?; apply: contra => /eqP[/= ->].
Qed.

Lemma probR_gt0' p : p != 0 :> R <-> 0 < p.
Proof. exact: probR_gt0. Qed.

Lemma probR_lt1 p : p != 1%:pr <-> p < 1.
Proof.
rewrite ltR_neqAle; split=> [H|[/eqP p1 _]].
by split => //; exact/eqP.
by case: p p1 => p ?; apply: contra => /eqP[/= ->].
Qed.

Lemma probR_lt1' p : p != 1 :> R <-> p < 1.
Proof. exact: probR_lt1. Qed.

Lemma probR_trichotomy p : p = 0%:pr \/ p = 1%:pr \/ 0 < p < 1.
Proof.
have [/eqP ->|pneq0]:= boolP (p == 0%:pr); first by left.
right.
have [/eqP ->|pneq1] := boolP (p == 1%:pr); first by left.
by right; split; [apply probR_gt0 | apply probR_lt1].
Qed.

Lemma probRK p : p = (p.~).~%:pr.
Proof. by apply val_inj => /=; rewrite onemK. Qed.

Lemma probRKC (p : {prob R}) : p + p.~ = 1 :> R.
Proof. exact: onemKC. Qed.

Lemma probadd_eq0 p q : p + q = 0 <-> p = 0%:pr /\ q = 0%:pr.
Proof.
split => [/paddR_eq0 | ].
- by move=> /(_ _)[] // p0 q0; split; exact/val_inj.
- by case => -> ->; rewrite addR0.
Qed.

Lemma probadd_neq0 p q : p + q != 0 <-> p != 0%:pr \/ q != 0%:pr.
Proof.
split => [/paddR_neq0| ]; first by move=> /(_ _ _); apply.
by case; apply: contra => /eqP/probadd_eq0 [] /eqP ? /eqP.
Qed.

Lemma probmul_eq1 p q : p * q = 1 <-> p = 1%:pr /\ q = 1%:pr.
Proof.
split => [/= pq1|[-> ->]]; last by rewrite mulR1.
move: R1_neq_R0; rewrite -{1}pq1 => /eqP; rewrite mulR_neq0' => /andP[].
rewrite 2!probR_gt0'=> p0 q0.
have /leR_eqVlt[p1|] := probR_le1 p; last first.
  by move/(ltR_pmul2r q0); rewrite mul1R => /(ltR_leR_trans);
     move/(_ _ (probR_le1 q))/ltR_neqAle => [].
have /leR_eqVlt[q1|] := probR_le1 q; last first.
  by move/(ltR_pmul2r p0); rewrite mul1R mulRC => /(ltR_leR_trans);
  move/(_ _ (probR_le1 p)) /ltR_neqAle => [].
by split; apply val_inj.
Qed.

End prob_lemmas.

Lemma prob_IZR (p : positive) : (0 <= / IZR (Zpos p) <= 1)%coqR.
Proof.
split; first exact/Rlt_le/Rinv_0_lt_compat/IZR_lt/Pos2Z.is_pos.
rewrite -[X in (_ <= X)%coqR]Rinv_1; apply Rle_Rinv => //.
- exact/IZR_lt/Pos2Z.is_pos.
- exact/IZR_le/Pos2Z.pos_le_pos/Pos.le_1_l.
Qed.

Lemma prob_IZR' (p : positive) : (0 <= / IZR (Zpos p) <= 1)%O.
Proof.
have [/RleP ? /RleP ?] := prob_IZR p.
exact/andP.
Qed.

Canonical probIZR (p : positive) := Eval hnf in Prob.mk (prob_IZR' p).

Definition divRnnm n m := INR n / INR (n + m).

Lemma prob_divRnnm n m : R0 <= divRnnm n m <= R1.
Proof.
rewrite /divRnnm.
have [/eqP ->|n0] := boolP (n == O).
  rewrite div0R.
  by have /leR2P:= (@OO1 real_realType).
split; first by apply divR_ge0; [exact: leR0n | rewrite ltR0n addn_gt0 lt0n n0].
by rewrite leR_pdivr_mulr ?mul1R ?leR_nat ?leq_addr // ltR0n addn_gt0 lt0n n0.
Qed.

(*Lemma prob_divRnnm' n m : (@Order.le _ _ R0 (divRnnm n m) && @Order.le _ _ (divRnnm n m) R1)%coqR.*)
Lemma prob_divRnnm' n m : (R0 <= divRnnm n m <= R1)%O.
Proof.
have [/RleP ? /RleP ?] := prob_divRnnm n m. exact/andP.
Qed.

Canonical probdivRnnm (n m : nat) :=
  Eval hnf in @Prob.mk _ (divRnnm n m) (prob_divRnnm' n m).

Lemma prob_invn (m : nat) : (R0 <= / (1 + m)%:R <= R1)%coqR.
Proof.
apply/leR2P; rewrite -(mul1R (/ _)%coqR) (_ : 1%coqR = INR 1) // -/(Rdiv _ _); apply/leR2P; exact: prob_divRnnm.
Qed.

Lemma prob_invn' (m : nat) : (R0 <= / (1 + m)%:R <= R1)%O.
Proof.
have [/RleP ? /RleP ?] := prob_invn m. exact/andP.
Qed.

Canonical probinvn (n : nat) :=
  Eval hnf in @Prob.mk _ (/ INR (1 + n)) (prob_invn' n).

Lemma prob_invp (p : {prob R}) : (0 <= 1 / (1 + p) <= 1)%coqR.
Proof.
split.
- by apply divR_ge0 => //; exact: addR_gt0wl.
- rewrite leR_pdivr_mulr ?mul1R; last exact: addR_gt0wl.
  by rewrite addRC -leR_subl_addr subRR.
Qed.

Lemma prob_invp' (p : {prob R}) : (0 <= 1 / (1 + p) <= 1)%O.
Proof.
have [/RleP ? /RleP ?] := prob_invp p. exact/andP.
Qed.

Definition Prob_invp (p : {prob R}) := Prob.mk (prob_invp' p).

Lemma prob_mulR (p q : {prob R}) : (0 <= Prob.p p * Prob.p q <= 1)%coqR.
Proof.
by split; [exact/mulR_ge0 |rewrite -(mulR1 1%coqR); apply leR_pmul].
Qed.

Lemma prob_mulR' (p q : {prob R}) : (0 <= Prob.p p * Prob.p q <= 1)%O.
Proof.
have [/RleP ? /RleP ?] := prob_mulR p q. exact/andP.
Qed.

Canonical probmulR (p q : {prob R}) :=
  Eval hnf in @Prob.mk _ (prob_coercion p * Prob.p q) (prob_mulR' p q).

(*Module OProb.
Section def.
Record t := mk {
  p :> {prob R};
  Op1 : (0 <b Prob.p p <b 1)%coqR }.
Definition O1 (p : t) : 0 <b Prob.p p <b 1 := Op1 p.
Arguments O1 : simpl never.
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

Canonical oprobcplt (p : oprob) := Eval hnf in OProb.mk (onem_oprob (OProb.O1 p)). *)
Coercion OProb.p : oprob  >-> prob_of.

Section oprob_lemmas.
Implicit Types p q : {oprob R}.

Lemma oprob_gt0 p : 0 < p.
(*Proof. by case: p => p /= /andP [] /ltRP. Qed.*)
Admitted.

Lemma oprob_lt1 p : p < 1.
(*Proof. by case: p => p /= /andP [] _ /ltRP. Qed.*)
Admitted.

Lemma oprob_ge0 p : 0 <= p. Proof. exact/ltRW/oprob_gt0. Qed.

Lemma oprob_le1 p : p <= 1. Proof. exact/ltRW/oprob_lt1. Qed.

Lemma oprob_neq0 p : p != 0 :> R.
Proof. by move:(oprob_gt0 p); rewrite ltR_neqAle=> -[] /nesym /eqP. Qed.

Lemma oprob_neq1 p : p != 1 :> R.
Proof. by move:(oprob_lt1 p); rewrite ltR_neqAle=> -[] /eqP. Qed.

Lemma oprobK p : p = ((OProb.p p).~).~%:opr.
Proof. by apply/val_inj/val_inj=> /=; rewrite onemK. Qed.

Lemma prob_trichotomy' (p : {prob R}) (P : {prob R} -> Prop) :
  P 0%:pr -> P 1%:pr -> (forall o : {oprob R}, P o) -> P p.
Proof.
move=> p0 p1 po.
have [-> //|[->//| p01]] := prob_trichotomy p.
(*TODO
exact (po (OProb.mk p01)).
Qed.*)
Admitted.

Lemma oprobadd_gt0 p q : 0 < p + q.
Proof. exact/addR_gt0/oprob_gt0/oprob_gt0. Qed.

Lemma oprobadd_neq0 p q : p + q != 0%coqR.
Proof. by move: (oprobadd_gt0 p q); rewrite ltR_neqAle => -[] /nesym /eqP. Qed.

End oprob_lemmas.

Lemma oprob_divRnnm n m : (0 < n)%nat -> (0 < m)%nat -> (0 < divRnnm n m < 1)%coqR.
Proof.
rewrite /divRnnm.
split; first by apply divR_gt0; [rewrite ltR0n | rewrite ltR0n addn_gt0 H orTb].
rewrite ltR_pdivr_mulr ?mul1R ?ltR_nat // ?ltR0n ?addn_gt0 ?H ?orTb //.
by rewrite -[X in (X < _)%nat](addn0 n) ltn_add2l.
Qed.

Lemma oprob_mulR (p q : {oprob R}) : (0 <b p * q <b 1)%coqR.
Proof.
apply/ltR2P; split; first exact/mulR_gt0/oprob_gt0/oprob_gt0.
by rewrite -(mulR1 1%coqR); apply ltR_pmul;
  [exact/oprob_ge0 | exact/oprob_ge0 | exact/oprob_lt1 | exact/oprob_lt1].
Qed.

Lemma oprob_mulR' (p q : {oprob R}) : (0 < p * q < 1)%O.
Proof.
Admitted.

Canonical oprobmulR (p q : {oprob R}) :=
  Eval hnf in @OProb.mk _ (Prob.p (OProb.p p) * q)%:pr (oprob_mulR' p q).

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

Definition rpos_coercion (p : Rpos) : Real.sort real_realType := Rpos.v p.
Coercion rpos_coercion : Rpos >-> Real.sort.

Definition mkRpos x H := @Rpos.mk x (introT (ltRP _ _) H).

Canonical Rpos1 := @mkRpos 1 Rlt_0_1.

Lemma Rpos_gt0 (x : Rpos) : 0 < x. Proof. by case: x => p /= /ltRP. Qed.
Global Hint Resolve Rpos_gt0 : core.

Lemma Rpos_neq0 (x : Rpos) : val x != 0.
Proof. by case: x => p /=; rewrite /gtRb lt0R => /andP[]. Qed.

Lemma addRpos_gt0 (x y : Rpos) : x + y >b 0. Proof. exact/ltRP/addR_gt0. Qed.
Canonical addRpos x y := Rpos.mk (addRpos_gt0 x y).

Lemma mulRpos_gt0 (x y : Rpos) : x * y >b 0. Proof. exact/ltRP/mulR_gt0. Qed.
Canonical mulRpos x y := Rpos.mk (mulRpos_gt0 x y).

Lemma divRpos_gt0 (x y : Rpos) : x / y >b 0. Proof. exact/ltRP/divR_gt0. Qed.
Canonical divRpos x y := Rpos.mk (divRpos_gt0 x y).

(* TODO: Canonical oprob_Rpos (p : oprob) := @mkRpos p (oprob_gt0 p). *)

Lemma oprob_divRposxxy (x y : Rpos) : (0 < x / (x + y) < 1)%coqR.
Proof.
split; first by apply/divR_gt0.
rewrite ltR_pdivr_mulr ?mul1R; last exact/ltRP/addRpos_gt0.
by rewrite ltR_addl.
Qed.

Lemma oprob_divRposxxy' (x y : Rpos) : (0 < x / (x + y) < 1)%O.
Proof.
have [/RltP ? /RltP ?] := oprob_divRposxxy x y. exact/andP.
Qed.

Lemma prob_divRposxxy (x y : Rpos) : (0 <= x / (x + y) <= 1)%coqR.
Proof. by apply/ltR2W/oprob_divRposxxy. Qed.

Lemma prob_divRposxxy' (x y : Rpos) : (0 <= x / (x + y) <= 1)%O.
Proof.
have [/RleP ? /RleP ?] := prob_divRposxxy x y. exact/andP.
Qed.

Canonical divRposxxy (x y : Rpos) :=
  Eval hnf in Prob.mk (prob_divRposxxy' x y).

Lemma divRposxxyC r q : divRposxxy q r = (divRposxxy r q).~%:pr.
Proof.
(*apply val_inj => /=; rewrite [in RHS]addRC onem_div ?addRK //.
exact: Rpos_neq0.
Qed.*) Abort.

Lemma onem_divRxxy (r q : Rpos) : (rpos_coercion r / (rpos_coercion r + q)).~ = q / (q + r).
(* TODO
Proof. by rewrite /onem subR_eq (addRC r) -mulRDl mulRV // ?gtR_eqF. Qed.
*)
Admitted.

Module Rnng.
Local Open Scope R_scope.
Record t := mk {
  v : R ;
  H : 0 <b= v }.
Definition K (r : t) := H r.
Arguments K : simpl never.
Module Exports.
Notation Rnng := t.
Notation "r %:nng" := (@mk r (@K _)).
Coercion v : t >-> R.
End Exports.
End Rnng.
Export Rnng.Exports.

Canonical Rnng_subType := [subType for Rnng.v].
Definition Rnng_eqMixin := Eval hnf in [eqMixin of Rnng by <:].
Canonical Rnng_eqType := Eval hnf in EqType Rnng Rnng_eqMixin.
Definition Rnng_choiceMixin := Eval hnf in [choiceMixin of Rnng by <:].
Canonical Rnng_choiceType := Eval hnf in ChoiceType Rnng Rnng_choiceMixin.

Section Rnng_theory.
Local Open Scope R_scope.

Definition mkRnng x H := @Rnng.mk x (introT (leRP _ _) H).

Lemma Rnng_ge0 (x : Rnng) : 0 <= x.
Proof. by case: x => p /= /leRP. Qed.
Local Hint Resolve Rnng_ge0 : core.

Canonical Rnng0 := Eval hnf in @mkRnng 0 (leRR 0).
Canonical Rnng1 := Eval hnf in @mkRnng R1 Rle_0_1.

Lemma addRnng_ge0 (x y : Rnng) : 0 <b= x + y.
Proof. exact/leRP/addR_ge0. Qed.
Canonical addRnneg x y := Rnng.mk (addRnng_ge0 x y).

Lemma mulRnng_ge0 (x y : Rnng) : 0 <b= x * y.
Proof. exact/leRP/mulR_ge0. Qed.
Canonical mulRnneg x y := Rnng.mk (mulRnng_ge0 x y).

End Rnng_theory.

Global Hint Resolve Rnng_ge0 : core.

Unset Printing Notations.
Definition s_of_pq (p q : {prob R}) : {prob R} := locked (p.~ * q.~).~%:pr.

Notation "[ 's_of' p , q ]" := (s_of_pq p q) : reals_ext_scope.

Lemma s_of_pqE (p q : {prob R}) : Prob.p [s_of p, q] = (p.~ * q.~)%coqR.~ :> R.
Proof. by rewrite /s_of_pq; unlock. Qed.

Lemma s_of_pq_oprob (p q : {oprob R}) : 0 < [s_of p, q] < 1.
Proof.
(*rewrite s_of_pqE (_ : (p.~ * q.~).~ = (p.~ * q.~).~%:opr) //=; exact: OProb.O1.
Qed. TODO*)
Admitted.
Lemma s_of_pq_oprob' (p q : {oprob R}) : (0 < Prob.p [s_of p, q] < 1)%O.
Admitted. (*TODO*)
Canonical oprob_of_s_of_pq (p q : {oprob R}) := Eval hnf in OProb.mk (s_of_pq_oprob' p q).


Lemma s_of_p0 (p : {prob R}) : [s_of p, 0%:pr] = p.
Proof. (*by apply/val_inj; rewrite /= s_of_pqE onem0 mulR1 onemK. Qed.*) Admitted.

Lemma s_of_0q (q : {prob R}) : [s_of 0%:pr, q] = q.
Proof. (*by apply/val_inj; rewrite /= s_of_pqE onem0 mul1R onemK. Qed.*) Admitted.

Lemma s_of_p1 (p : {prob R}) : [s_of p, 1%:pr] = 1%:pr.
Proof. (*by apply/val_inj; rewrite /= s_of_pqE onem1 mulR0 onem0. Qed.*) Admitted.

Lemma s_of_1q (q : {prob R}) : [s_of 1%:pr, q] = 1%:pr.
Proof. (*by apply/val_inj; rewrite /= s_of_pqE onem1 mul0R onem0. Qed.*) Admitted.

Lemma s_of_pqE' (p q : {prob R}) : Prob.p [s_of p, q] = Prob.p p + p.~ * Prob.p q :> R.
Proof. (*rewrite s_of_pqE /= /onem; field. Qed.*) Admitted.

Lemma s_of_gt0 p q : p != 0%:pr -> 0 < Prob.p [s_of p, q].
Proof.
(*move=> ?; rewrite s_of_pqE';
  apply addR_gt0wl; [exact/prob_gt0 | exact: mulR_ge0].
Qed.*) Admitted.

(*Lemma s_of_gt0_oprob (p : oprob) (q : prob) : 0 < [s_of p, q].
Proof. by apply/s_of_gt0/oprob_neq0. Qed.*)

Lemma ge_s_of (p q : {prob R}) : Prob.p p <= Prob.p [s_of p, q].
Proof. (*rewrite s_of_pqE' addRC -leR_subl_addr subRR; exact/mulR_ge0. Qed.*) Admitted.

Lemma r_of_pq_prob (p q : {prob R}) : 0 <= Prob.p p / Prob.p [s_of p, q] <= 1.
(* TODO
Proof.
case/boolP : (p == 0%:pr :> prob) => p0.
  rewrite (eqP p0) div0R; apply/andP; split; apply/leRP => //; exact/leRR.
case/boolP : (q == 0%:pr :> prob) => q0.
  rewrite (eqP q0) (s_of_p0 p) divRR //; apply/andP; split; apply/leRP=> //; exact/leRR.
apply/andP; split; apply/leRP.
- apply divR_ge0 => //; exact/s_of_gt0.
- rewrite leR_pdivr_mulr ?mul1R; [exact: ge_s_of | exact: s_of_gt0].
Qed.
*)
Admitted.

Lemma r_of_pq_prob' (p q : {prob R}) : @Order.le _ _ 0 (Prob.p p / Prob.p [s_of p, q])
                                       && @Order.le _ _ (Prob.p p / Prob.p [s_of p, q]) 1.
Proof. (*TODO*) Admitted.

Definition r_of_pq (p q : {prob R}) : {prob R} := locked (Prob.mk (r_of_pq_prob' p q)).

Notation "[ 'r_of' p , q ]" := (r_of_pq p q) : reals_ext_scope.

Lemma r_of_pqE (p q : {prob R}) : Prob.p [r_of p, q] = Prob.p p / Prob.p [s_of p, q] :> R.
Proof. by rewrite /r_of_pq; unlock. Qed.

Lemma r_of_pq_oprob (p q : {oprob R}) : 0 < Prob.p [r_of OProb.p p, OProb.p q] < 1.
(*TODO: Proof.
rewrite r_of_pqE.
apply/andP; split; apply/ltRP; first by apply divR_gt0.
rewrite ltR_pdivr_mulr ?mul1R; last by apply/(oprob_gt0).
rewrite ltR_neqAle; split; last by apply/ge_s_of.
rewrite s_of_pqE'; apply/eqP/ltR_eqF/ltR_addl.
by apply/oprob_gt0.
Qed.*)
Admitted.
Lemma r_of_pq_oprob' (p q : {oprob R}) : (0 < Prob.p [r_of OProb.p p, OProb.p q] < 1)%O.
Admitted. (*TODO*)
Canonical oprob_of_r_of_pq (p q : {oprob R}) := Eval hnf in OProb.mk (r_of_pq_oprob' p q).


Lemma r_of_p0 (p : {prob R}) : p != 0%:pr -> [r_of p, 0%:pr] = 1%:pr.
(*Proof. by move=> p0; apply val_inj; rewrite /= r_of_pqE s_of_p0 divRR. Qed.*)
Admitted.

Lemma r_of_p0_oprob (p : {oprob R}) : [r_of OProb.p p, 0%:pr] = 1%:pr.
Proof. by apply/r_of_p0/oprob_neq0. Qed.

Lemma r_of_0q (q : {prob R}) : [r_of 0%:pr, q] = 0%:pr.
(*Proof. by apply/val_inj; rewrite /= r_of_pqE div0R. Qed.*)
Admitted.

Lemma r_of_p1 (p : {prob R}) : [r_of p, 1%:pr] = p.
(*Proof. by apply/val_inj; rewrite /= r_of_pqE s_of_p1 divR1. Qed.*)
Admitted.

Lemma r_of_1q (q : {prob R}) : [r_of 1%:pr, q] = 1%:pr.
(*Proof. by apply/val_inj; rewrite /= r_of_pqE s_of_1q divR1. Qed.*)
Admitted.

Lemma p_is_rs (p q : {prob R}) : Prob.p p = [r_of p, q] * [s_of p, q] :> R.
Proof.
case/boolP : (p == 0%:pr :> {prob R}) => p0; first by rewrite (eqP p0) r_of_0q mul0R.
case/boolP : (q == 0%:pr :> {prob R}) => q0.
  by rewrite (eqP q0) s_of_p0 r_of_p0 // mul1R.
(*TODO:
rewrite r_of_pqE /Rdiv -mulRA mulVR ?mulR1 //.
suff : Prob.p [s_of p, q] != 0 :> R by [].
by rewrite prob_gt0; apply/RltP/s_of_gt0.
Qed.*)
Admitted.

Lemma r_of_pq_is_r (p q r s : {prob R}) : r != 0%:pr -> s != 0%:pr ->
  Prob.p p = Prob.p r * Prob.p s :> R -> s.~ = p.~ * q.~ -> [r_of p, q] = r.
Proof.
move=> r0 s0 H1 H2; apply val_inj => /=.
(*rewrite r_of_pqE eqR_divr_mulr; last by rewrite s_of_pqE -H2 onemK.
rewrite (p_is_rs _ q) /= {1}s_of_pqE -H2 onemK r_of_pqE s_of_pqE.
by rewrite -H2 onemK /Rdiv -mulRA mulVR ?mulR1.
Qed.*)
Admitted.

(*Lemma r_of_pq_is_r_oprob (p q : prob) (r s : oprob) :
  p = r * s :> R -> s.~ = p.~ * q.~ -> [r_of p, q] = r.
Proof. apply/r_of_pq_is_r/oprob_neq0/oprob_neq0. Qed.*)

Lemma p_of_rs_prob (r s : {prob R}) : (0 <= Prob.p r * Prob.p s <= 1)%O.
Proof.
move: r s => -[] r /andP [] /leRP r0 /leRP r1 -[] s /= /andP [] /leRP s0 /leRP s1.
apply/andP; split; apply/leRP; [exact/mulR_ge0 | rewrite -(mulR1 1); exact: leR_pmul].
Qed.

Definition p_of_rs (r s : {prob R}) : {prob R} := locked (Prob.mk (p_of_rs_prob r s)).

Notation "[ 'p_of' r , s ]" := (p_of_rs r s) : reals_ext_scope.
Lemma p_of_rsE (r s : {prob R}) : Prob.p [p_of r, s] = Prob.p r * Prob.p s :> R.
Proof. by rewrite /p_of_rs; unlock. Qed.

(*Lemma p_of_rs_oprob (r s : oprob) : 0 <b [p_of r, s] <b 1.
Proof. by rewrite p_of_rsE; apply/OProb.O1. Qed.
Canonical oprob_of_p_of_rs (r s : oprob) := Eval hnf OProb.mk (p_of_rs_oprob r s).*)

Lemma p_of_r1 (r : {prob R}) : [p_of r, 1%:pr] = r.
(*Proof. by apply val_inj; rewrite /= p_of_rsE mulR1. Qed.*)
Admitted.

Lemma p_of_1s (s : {prob R}) : [p_of 1%:pr, s] = s.
(*Proof. by apply val_inj; rewrite /= p_of_rsE mul1R. Qed.*)
Admitted.

Lemma p_of_r0 (r : {prob R}) : [p_of r, 0%:pr] = 0%:pr.
(*Proof. by apply/val_inj; rewrite /= p_of_rsE mulR0. Qed.*)
Admitted.

Lemma p_of_0s (s : {prob R}) : [p_of 0%:pr, s] = 0%:pr.
(*Proof. by apply/val_inj; rewrite /= p_of_rsE mul0R. Qed.*)
Admitted.

Lemma p_of_rsC (r s : {prob R}) : [p_of r, s] = [p_of s, r].
(*Proof. by apply/val_inj; rewrite /= !p_of_rsE mulRC. Qed.*)
Admitted.

Lemma p_of_neq1 (p q : {prob R}) : 0 < Prob.p p < 1 -> [p_of q, p] != 1%:pr.
Proof.
case=> p0 p1; apply/eqP => pq1; move: (p1).
rewrite [X in _ < X -> _](_ : _ = Prob.p 1%:pr) //.
(*rewrite -pq1 p_of_rsE -ltR_pdivr_mulr // divRR ?prob_gt0 //.
by rewrite ltRNge; exact.
Qed.*)
Admitted.

Lemma p_of_rs1 (r s : {prob R}) :
  ([p_of r, s] == 1%:pr :> {prob R}) = ((r == 1%:pr) && (s == 1%:pr)).
Proof.
apply/idP/idP; last by case/andP => /eqP -> /eqP ->; rewrite p_of_r1.
(*move/eqP/(congr1 Prob.p); rewrite /= p_of_rsE => /eqP.
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
Qed.*)
Admitted.

Lemma p_of_rs1P r s : reflect (r = 1%:pr /\ s = 1%:pr) ([p_of r, s] == 1%:pr).
Proof.
move: (p_of_rs1 r s) ->.
apply: (iffP idP);
  [by case/andP => /eqP -> /eqP -> | by case => -> ->; rewrite eqxx].
Qed.

Lemma q_of_rs_prob (r s : {prob R}) : 0 <= (r.~ * s) / [p_of r, s].~ <= 1.
Proof.
case/boolP : (r == 1%:pr :> {prob R}) => r1.
  by rewrite (eqP r1) onem1 mul0R div0R; split.
case/boolP : (s == 1%:pr :> {prob R}) => s1.
  rewrite (eqP s1) mulR1 p_of_r1 divRR ?onem_neq0 //; split=> //; exact/leRR.
split.
(*TODO
  apply/divR_ge0; first exact/mulR_ge0.
  apply/onem_gt0; rewrite p_of_rsE -(mulR1 1); apply/ltR_pmul => //;
    by [rewrite -prob_lt1 | rewrite -prob_lt1].
rewrite leR_pdivr_mulr ?mul1R.
  by rewrite p_of_rsE {2}/onem leR_subr_addr -mulRDl addRC onemKC mul1R.
apply onem_gt0; rewrite p_of_rsE -(mulR1 1); apply/ltR_pmul => //;
  by [rewrite -prob_lt1 | rewrite -prob_lt1].
Qed.*)
Admitted.

Lemma q_of_rs_prob' (r s : {prob R}) : (0 <= (r.~ * Prob.p s) / [p_of r, s].~ <= 1)%O.
Proof.
case/boolP : (r == 1%:pr :> {prob R}) => r1.
  rewrite (eqP r1) onem1 mul0R div0R; apply/andP; split; apply/leRP => //; exact/leRR.
case/boolP : (s == 1%:pr :> {prob R}) => s1.
  rewrite (eqP s1) mulR1 p_of_r1 divRR ?onem_neq0 //; apply/andP; split; apply/leRP => //; exact/leRR.
apply/andP; split; apply/leRP.
(*TODO:
  apply/divR_ge0; first exact/mulR_ge0.
    apply/onem_gt0; rewrite p_of_rsE -(mulR1 1); apply/ltR_pmul => //;
      by [rewrite -prob_lt1 | rewrite -prob_lt1].
rewrite leR_pdivr_mulr ?mul1R.
  by rewrite p_of_rsE {2}/onem leR_subr_addr -mulRDl addRC onemKC mul1R.
apply onem_gt0; rewrite p_of_rsE -(mulR1 1); apply/ltR_pmul => //;
  by [rewrite -prob_lt1 | rewrite -prob_lt1].
Qed.*)
Admitted.

Definition q_of_rs (r s : {prob R}) : {prob R} := locked (Prob.mk (q_of_rs_prob' r s)).

Notation "[ 'q_of' r , s ]" := (q_of_rs r s) : reals_ext_scope.

Lemma q_of_rsE (r s : {prob R}) : Prob.p [q_of r, s] = (r.~ * Prob.p s) / [p_of r, s].~ :> R.
Proof. by rewrite /q_of_rs; unlock. Qed.

(*Lemma q_of_rs_oprob (r s : oprob) : 0 <b [q_of r, s] <b 1.
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
Canonical oprob_of_q_of_rs (r s : oprob) := Eval hnf in OProb.mk (q_of_rs_oprob r s).*)

Lemma q_of_r0 (r : {prob R}) : [q_of r, 0%:pr] = 0%:pr.
(*Proof. by apply/val_inj => /=; rewrite q_of_rsE mulR0 div0R. Qed.*)
Admitted.

Lemma q_of_r1 (r : {prob R}) : r != 1%:pr -> [q_of r, 1%:pr] = 1%:pr.
Proof.
move=> r1.
(*by apply/val_inj => /=; rewrite q_of_rsE /= mulR1 p_of_r1 divRR // onem_neq0.
Qed.*)
Admitted.

Lemma q_of_1s (s : {prob R}) : [q_of 1%:pr, s] = 0%:pr.
(*Proof. by apply/val_inj => /=; rewrite q_of_rsE onem1 mul0R div0R. Qed.*)
Admitted.

Lemma pq_is_rs (p q : {prob R}) : p.~ * Prob.p q = [r_of p, q].~ * Prob.p [s_of p, q].
Proof.
case/boolP : (p == 0%:pr :> {prob R}) => p0.
  by rewrite (eqP p0) onem0 mul1R r_of_0q onem0 mul1R s_of_0q.
(*rewrite r_of_pqE [in RHS]mulRBl mul1R.
rewrite /Rdiv -mulRA mulVR ?mulR1; last first.
  rewrite prob_gt0; exact/s_of_gt0.
by rewrite s_of_pqE' addRC addRK.
Qed.*)
Admitted.

Lemma s_of_pqK r s : [p_of r, s] != 1%:pr ->
  [s_of [p_of r, s], [q_of r, s]] = s.
Proof.
move=> H.
(*apply/val_inj; rewrite /= s_of_pqE p_of_rsE q_of_rsE p_of_rsE /=.
rewrite /onem; field.
rewrite subR_eq0; apply/eqP; apply: contra H => /eqP rs1.
by apply/eqP/val_inj; rewrite /= p_of_rsE.
Qed.*)
Admitted.

(*Lemma s_of_pqK_oprob (r s : oprob) : [s_of [p_of r, s], [q_of r, s]] = s.
Proof. apply/s_of_pqK/oprob_neq1. Qed.*)

Lemma r_of_pqK (r s : {prob R}) : [p_of r, s] != 1%:pr -> s != 0%:pr ->
  [r_of [p_of r, s], [q_of r, s]] = r.
Proof.
move=> H1 s0; apply/val_inj => /=.
(*rewrite !(r_of_pqE,s_of_pqE,q_of_rsE,p_of_rsE) /onem; field.
split; last first.
  by rewrite 2!subRB subRR add0R mulRBl mul1R addRC subRK; exact/eqP.
rewrite subR_eq0 => /esym.
apply/eqP; apply: contra H1 => /eqP H1.
by apply/eqP/val_inj; rewrite /= p_of_rsE.
Qed.*)
Admitted.

(*Lemma r_of_pqK_oprob (r s : oprob) : [r_of [p_of r, s], [q_of r, s]] = r.
Proof. apply/r_of_pqK/oprob_neq0/oprob_neq1. Qed.*)

Lemma s_of_Rpos_probA (p q r : Rpos) :
  [s_of (p / (p + (q + r)))%:pos%:pr, (q / (q + r))%:pos%:pr] =
  ((p + q) / (p + q + r))%:pos%:pr.
Proof.
(*apply val_inj; rewrite /= s_of_pqE /onem /=; field.
by split; exact/eqP/Rpos_neq0.
Qed.*)
Admitted.

Lemma r_of_Rpos_probA (p q r : Rpos) :
  [r_of (p / (p + (q + r)))%:pos%:pr, (q / (q + r))%:pos%:pr] =
  (p / (p + q))%:pos%:pr.
Proof.
(*apply/val_inj; rewrite /= r_of_pqE s_of_pqE /onem /=; field.
do 3 (split; first exact/eqP/Rpos_neq0).
rewrite (addRC p (q + r)) addRK {4}[in q + r]addRC addRK.
rewrite mulRC -mulRBr (addRC _ p) addRA addRK mulR_neq0.
split; exact/eqP/Rpos_neq0.
Qed.*)
Admitted.

