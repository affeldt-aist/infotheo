(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra vector reals normedtype.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import Rstruct.
Require Import ssrR realType_ext.
Require Import Reals Lra.
From mathcomp Require Import lra.

(******************************************************************************)
(*              Additional lemmas and definitions about Coq reals             *)
(*                                                                            *)
(* Section reals_ext.                                                         *)
(*   various lemmas about up, Int_part, frac_part, Rabs define ceil and floor *)
(*                                                                            *)
(*  T ->R^+ == functions that return non-negative reals.                      *)
(*                                                                            *)
(*    Qplus == type of non-negative rationals                                 *)
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
Reserved Notation "+| r |" (at level 0, r at level 99, format "+| r |").
Reserved Notation "x %:pos" (at level 2, format "x %:pos").
Reserved Notation "x %:nng" (at level 2, format "x %:nng").

Notation "+| r |" := (Rmax 0 r) : reals_ext_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Arguments INR : simpl never.

Import Order.Theory GRing.Theory Num.Theory.

#[export] Hint Extern 0 ((0 <= onem _)%coqR) =>
  solve [exact/RleP/onem_ge0/RleP] : core.

Local Open Scope R_scope.
Local Open Scope reals_ext_scope.

Lemma Rlt_1_2 : 1 < 2. Proof. Lra.lra. Qed.
Global Hint Resolve Rlt_1_2 : core.

Section reals_ext.

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
have : forall a b, 0 <= b -> a - b <= a. move=>  *; Lra.lra.
apply; apply mulR_ge0; [Lra.lra | exact: pow_even_ge0].
Qed.

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
rewrite /Int_part minus_IZR => _ ?; Lra.lra.
Qed.

Lemma Rle_up a : a <= IZR (Z.abs (up a)).
Proof.
case: (Rlt_le_dec a 0) => Ha; last by apply Rle_up_pos.
apply (@leR_trans  0); first Lra.lra.
exact/IZR_le/Zabs_pos.
Qed.

Lemma up_Int_part r : (up r = Int_part r + 1)%Z.
Proof.
case: (base_Int_part r) => H1 H2.
rewrite -(up_tech r (Int_part r)) // plus_IZR //; Lra.lra.
Qed.

Lemma Int_part_ge0 a : 0 <= a -> (0 <= Int_part a)%Z.
Proof.
move/up_pos => ?; rewrite /Int_part (_ : 0 = Z.succ 0 - 1)%Z //.
apply Z.sub_le_mono => //; exact/Zlt_le_succ.
Qed.

Lemma frac_part_INR m : frac_part (INR m) = 0.
Proof.
rewrite /frac_part /Int_part -(up_tech _ (Z_of_nat m)).
- by rewrite minus_IZR plus_IZR /= -INR_IZR_INZ; by field.
- rewrite -INR_IZR_INZ.
  by apply/RleP; rewrite Order.POrderTheory.lexx.
- rewrite {1}INR_IZR_INZ; apply IZR_lt.
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
  Lra.lra.
  rewrite ?plus_IZR ?minus_IZR ?mult_IZR ?minus_IZR // Ha Hb.
  rewrite (_ : forall a, a + 1 - 1 = a); last by move=> *; field.
  rewrite (_ : forall a, a + 1 - 1 = a); last by move=> *; field.
  by apply/RleP; rewrite Order.POrderTheory.lexx.
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
Proof. rewrite /floor; case: (base_Int_part r) => ? ?; split=> //; Lra.lra. Qed.

Lemma ceilP (r : R) : r <= IZR (ceil r) < r + 1.
Proof.
rewrite /ceil; case: ifPn => [|] /eqP r0.
  rewrite frac_Int_part //; Lra.lra.
case: (floorP r); rewrite /floor => H1 /Rle_lt_or_eq_dec[] H2.
  rewrite up_Int_part plus_IZR; Lra.lra.
by exfalso; apply/r0; rewrite subR_eq0.
Qed.

Lemma leR0ceil x : 0 <= x -> (0 <= ceil x)%Z.
Proof. move=> ?; case: (ceilP x) => K _; exact/le_IZR/(leR_trans _ K). Qed.

Lemma normR_max a b c c' : 0 <= a <= c -> 0 <= b <= c' ->
  `| a - b | <= max(c, c').
Proof.
move=> [H1 H2] [H H3]; case: (Rtotal_order a b) => [H0|[H0|H0]].
- rewrite distRC gtR0_norm ?subR_gt0 //.
  apply: (@leR_trans b); [Lra.lra | apply/(leR_trans H3)/leR_maxr; lra].
- subst b; rewrite subRR normR0.
  exact/(leR_trans H1)/(leR_trans H2)/leR_maxl.
- rewrite geR0_norm; last Lra.lra.
  apply: (@leR_trans a); [Lra.lra|exact/(leR_trans H2)/leR_maxl].
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
  _ : [forall a, (0 <= nneg_ff a)%mcR] }.

Canonical nneg_finfun_subType := Eval hnf in [subType for nneg_ff].
Definition nneg_finfun_eqMixin := [eqMixin of nneg_finfun by <:].
Canonical nneg_finfun_eqType := Eval hnf in EqType _ nneg_finfun_eqMixin.
End nneg_finfun.

Record nneg_fun (T : Type) := mkNNFun {
  nneg_f :> T -> R ;
  nneg_f_ge0 : forall a, 0 <= nneg_f a }.

Notation "T '->R^+' " := (nneg_fun T) : reals_ext_scope.

#[global] Hint Extern 0 (Rle (IZR Z0) _) => solve [exact/RleP/prob_ge0] : core.
#[global] Hint Extern 0 (Rle _ (IZR (Zpos xH))) => solve [exact/RleP/prob_le1] : core.

Lemma prob_IZR_subproof (p : positive) : (0 <= / IZR (Zpos p) <= 1)%O.
Proof.
have [/RleP ? /RleP ?] : (0 <= / IZR (Zpos p) <= 1)%coqR.
  split; first exact/Rlt_le/Rinv_0_lt_compat/IZR_lt/Pos2Z.is_pos.
  rewrite -[X in (_ <= X)%coqR]Rinv_1; apply Rle_Rinv => //.
  - exact/IZR_lt/Pos2Z.is_pos.
  - exact/IZR_le/Pos2Z.pos_le_pos/Pos.le_1_l.
exact/andP.
Qed.

Canonical probIZR (p : positive) := Eval hnf in Prob.mk (prob_IZR_subproof p).

Definition divRnnm n m := n%:R / (n + m)%:R.

Lemma prob_divRnnm_subproof n m : (R0 <= divRnnm n m <= R1)%O.
Proof.
apply/andP; split.
  by rewrite /divRnnm RdivE' divr_ge0// INRE ler0n.
rewrite /divRnnm RdivE' !INRE.
have [/eqP ->|n0] := boolP (n == O).
  by rewrite mul0r ler01.
rewrite ler_pdivrMr// ?ltr0n ?addn_gt0; last first.
  by rewrite lt0n n0.
by rewrite mul1r ler_nat leq_addr.
Qed.

Canonical probdivRnnm (n m : nat) :=
  Eval hnf in @Prob.mk _ (divRnnm n m) (prob_divRnnm_subproof n m).

Lemma prob_invn (m : nat) : (R0 <= / (1 + m)%:R <= R1)%mcR.
Proof.
rewrite -(mul1R (/ _)%coqR) (_ : 1%coqR = INR 1) // -/(Rdiv _ _).
exact: prob_divRnnm_subproof.
Qed.

Canonical probinvn (n : nat) :=
  Eval hnf in @Prob.mk _ (/ (1 + n)%:R) (prob_invn n).

Lemma prob_invp_subproof (p : {prob R}) : (0 <= 1 / (1 + Prob.p p) <= 1)%O.
Proof.
apply/andP; split.
  by rewrite RdivE' mul1r invr_ge0 ?addr_ge0.
rewrite RdivE' mul1r invf_le1//.
  by rewrite ler_addl.
rewrite (@lt_le_trans _ _ 1)//.
  by rewrite ltr01.
by rewrite ler_addl.
Qed.

Definition Prob_invp (p : {prob R}) := Prob.mk (prob_invp_subproof p).

Lemma prob_mulR_subproof (p q : {prob R}) : (0 <= Prob.p p * Prob.p q <= 1)%O.
Proof.
apply/andP; split.
  by rewrite mulr_ge0.
by rewrite mulr_ile1.
Qed.

Canonical probmulR (p q : {prob R}) :=
  Eval hnf in @Prob.mk _ (Prob.p p * Prob.p q) (prob_mulR_subproof p q).

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

Lemma oprob_gt0 p : 0 < Prob.p (OProb.p p).
Proof. by case: p => p /= /andP [] /RltP. Qed.

Lemma oprob_lt1 p : Prob.p (OProb.p p) < 1.
Proof. by case: p => p /= /andP [] _ /RltP. Qed.

Lemma oprob_ge0 p : 0 <= Prob.p (OProb.p p). Proof. exact/ltRW/oprob_gt0. Qed.

Lemma oprob_le1 p : Prob.p (OProb.p p) <= 1. Proof. exact/ltRW/oprob_lt1. Qed.

Lemma oprob_neq0 p : Prob.p (OProb.p p) != 0 :> R.
Proof. by move:(oprob_gt0 p); rewrite ltR_neqAle=> -[] /nesym /eqP. Qed.

Lemma oprob_neq1 p : Prob.p (OProb.p p) != 1 :> R.
Proof. by move:(oprob_lt1 p); rewrite ltR_neqAle=> -[] /eqP. Qed.

Lemma oprobK (p : {oprob R}) : p = ((Prob.p (OProb.p p)).~).~%:opr.
Proof. by apply/val_inj/val_inj=> /=; rewrite onemK. Qed.

Lemma prob_trichotomy' (p : {prob R}) (P : {prob R} -> Prop) :
  P 0%:pr -> P 1%:pr -> (forall o : {oprob R}, P o) -> P p.
Proof.
move=> p0 p1 po.
have [-> //|[->//| p01]] := prob_trichotomy p.
exact (po (OProb.mk p01)).
Qed.

Lemma oprobadd_gt0 p q : 0 < Prob.p (OProb.p p) + (Prob.p (OProb.p q)).
Proof. exact/addR_gt0/oprob_gt0/oprob_gt0. Qed.

Lemma oprobadd_neq0 p q : Prob.p (OProb.p p) + Prob.p (OProb.p q) != 0%coqR.
Proof. by move: (oprobadd_gt0 p q); rewrite ltR_neqAle => -[] /nesym /eqP. Qed.

End oprob_lemmas.

Lemma oprob_divRnnm n m : (0 < n)%nat -> (0 < m)%nat -> (0 < divRnnm n m < 1)%coqR.
Proof.
rewrite /divRnnm.
split; first by apply divR_gt0; [rewrite ltR0n | rewrite ltR0n addn_gt0 H orTb].
rewrite ltR_pdivr_mulr ?mul1R ?ltR_nat // ?ltR0n ?addn_gt0 ?H ?orTb //.
by rewrite -[X in (X < _)%nat](addn0 n) ltn_add2l.
Qed.

Lemma oprob_mulR_subproof (p q : {oprob R}) : (0 < Prob.p (OProb.p p) * Prob.p (OProb.p q) < 1)%O.
Proof.
apply/andP; split.
  by rewrite mulr_gt0//; apply/RltP/oprob_gt0.
by rewrite mulr_ilt1//; apply/RltP/oprob_lt1.
Qed.

Canonical oprobmulR (p q : {oprob R}) :=
  Eval hnf in @OProb.mk _ (Prob.p (OProb.p p) * q)%:pr (oprob_mulR_subproof p q).

Record Qplus := mkRrat { num : nat ; den : nat }.

Definition Q2R (q : Qplus) := INR (num q) / INR (den q).+1.

Coercion Q2R : Qplus >-> R.

Lemma s_of_pq_oprob_subproof (p q : {oprob R}) : (0 < Prob.p [s_of p, q] < 1)%O.
Proof.
rewrite s_of_pqE; apply/andP; split.
- rewrite onem_gt0//= mulr_ilt1 ?onem_ge0 ?onem_lt1//.
  by have /andP[] := OProb.O1 p.
  by have /andP[] := OProb.O1 q.
- rewrite onem_lt1// mulr_gt0// onem_gt0//.
  by have /andP[] := OProb.O1 p.
  by have /andP[] := OProb.O1 q.
Qed.

Canonical oprob_of_s_of_pq (p q : {oprob R}) :=
  Eval hnf in OProb.mk (s_of_pq_oprob_subproof p q).

Lemma s_of_gt0_oprob (p : {oprob R}) (q : {prob R}) : 0 < Prob.p [s_of p, q].
Proof. by apply/RltP; rewrite s_of_gt0//; exact/oprob_neq0. Qed.

Lemma r_of_pq_oprob_subproof (p q : {oprob R}) : (0 < Prob.p [r_of OProb.p p, OProb.p q] < 1)%O.
Proof.
rewrite r_of_pqE; apply/andP; split.
  rewrite divr_gt0////.
    exact/RltP/oprob_gt0.
  rewrite s_of_pqE//.
  have := OProb.O1 (((oprob_to_real p).~ * (oprob_to_real q).~).~)%:opr.
  by move/andP=> [] /=.
apply/RltP.
rewrite -RdivE'.
rewrite ltR_pdivr_mulr ?mul1R; last by apply/(oprob_gt0).
rewrite ltR_neqAle; split; last exact/RleP/ge_s_of.
rewrite s_of_pqE; apply/eqP/ltR_eqF.
rewrite onemM !onemK -!RplusE -RoppE -addRA.
apply/ltR_addl.
have := oprob_gt0 ((oprob_to_real p).~ * oprob_to_real q)%:opr.
by rewrite /= onemE mulrBl mul1r -RminusE//.
Qed.

Canonical oprob_of_r_of_pq (p q : {oprob R}) :=
  Eval hnf in OProb.mk (r_of_pq_oprob_subproof p q).

Lemma r_of_p0_oprob (p : {oprob R}) : [r_of OProb.p p, 0%:pr] = 1%:pr.
Proof. by apply/r_of_p0/oprob_neq0. Qed.

Lemma s_of_pqK (r s : {prob R}) : [p_of r, s] != 1%:pr ->
  [s_of [p_of r, s], [q_of r, s]] = s.
Proof.
move=> H.
apply/val_inj; rewrite /= s_of_pqE p_of_rsE q_of_rsE p_of_rsE /=.
rewrite /onem.
rewrite -!RminusE -RmultE.
rewrite (_ : 1%mcR = 1)// -!RmultE.
rewrite -RinvE'.
field.
rewrite subR_eq0; apply/eqP; apply: contra H => /eqP rs1.
by apply/eqP/val_inj; rewrite /= p_of_rsE.
Qed.

Lemma r_of_pqK (r s : {prob R}) : [p_of r, s] != 1%:pr -> s != 0%:pr ->
  [r_of [p_of r, s], [q_of r, s]] = r.
Proof.
move=> H1 s0; apply/val_inj => /=.
rewrite !(r_of_pqE,s_of_pqE,q_of_rsE,p_of_rsE) /onem.
rewrite -!RminusE -R1E -!RmultE -!RinvE'.
field.
split; last first.
  by rewrite 2!subRB subRR add0R mulRBl mul1R addRC subRK; exact/eqP.
rewrite subR_eq0 => /esym.
apply/eqP; apply: contra H1 => /eqP H1.
by apply/eqP/val_inj; rewrite /= p_of_rsE.
Qed.

Module Rpos.
Record t := mk {
  v : R ;
  H : (v > 0)%mcR }.
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

Definition mkRpos x H := @Rpos.mk x (introT (RltP _ _) H).

Canonical Rpos1 := @mkRpos 1 Rlt_0_1.

Lemma Rpos_gt0 (x : Rpos) : 0 < x. Proof. by case: x => p /= /RltP. Qed.
Global Hint Resolve Rpos_gt0 : core.

Lemma Rpos_neq0 (x : Rpos) : val x != 0.
Proof. by case: x => p /=; rewrite /RltP lt0r => /andP[]. Qed.

Lemma addRpos_gt0 (x y : Rpos) : ((x + y)%coqR > 0)%mcR.
Proof. exact/RltP/addR_gt0. Qed.
Canonical addRpos x y := Rpos.mk (addRpos_gt0 x y).

Lemma mulRpos_gt0 (x y : Rpos) : ((x * y)%coqR > 0)%mcR.
Proof. exact/RltP/mulR_gt0. Qed.
Canonical mulRpos x y := Rpos.mk (mulRpos_gt0 x y).

Lemma divRpos_gt0 (x y : Rpos) : (((x : R) / (y : R))%coqR > 0)%mcR.
Proof. exact/RltP/divR_gt0. Qed.
Canonical divRpos x y := Rpos.mk (divRpos_gt0 x y).

(* TODO: Canonical oprob_Rpos (p : oprob) := @mkRpos p (oprob_gt0 p). *)

Lemma oprob_divRposxxy (x y : Rpos) : (0 < x / (x + y) < 1)%coqR.
Proof.
split; first by apply/divR_gt0.
rewrite ltR_pdivr_mulr ?mul1R; last exact/RltP/addRpos_gt0.
by rewrite ltR_addl.
Qed.

Lemma oprob_divRposxxy' (x y : Rpos) : (0 < x / (x + y) < 1)%O.
Proof.
have [/RltP ? /RltP ?] := oprob_divRposxxy x y. exact/andP.
Qed.

Lemma prob_divRposxxy (x y : Rpos) : (0 <= x / (x + y) <= 1)%coqR.
Proof.
have [] := oprob_divRposxxy x y.
move/RltP/Order.POrderTheory.ltW/RleP => ?.
move/RltP/Order.POrderTheory.ltW/RleP => ?.
by [].
Qed.

Lemma prob_divRposxxy' (x y : Rpos) : (0 <= x / (x + y) <= 1)%O.
Proof.
have [/RleP ? /RleP ?] := prob_divRposxxy x y. exact/andP.
Qed.

Canonical divRposxxy (x y : Rpos) :=
  Eval hnf in Prob.mk (prob_divRposxxy' x y).

Lemma divRposxxyC r q : divRposxxy q r = (Prob.p (divRposxxy r q)).~%:pr.
Proof.
apply val_inj => /=; rewrite [in RHS]addRC.
rewrite [in RHS]RdivE' onem_div// ?addrK//.
  by rewrite RplusE RdivE'.
exact: Rpos_neq0.
Qed.

Lemma onem_divRxxy (r q : Rpos) : (rpos_coercion r / (rpos_coercion r + q)).~ = q / (q + r).
Proof.
rewrite /onem; apply/eqP; rewrite subr_eq.
rewrite !RplusE (addrC (r : R)) RdivE' -mulrDl divff//.
by rewrite gtR_eqF//; apply: addR_gt0.
Qed.

Module Rnng.
Local Open Scope R_scope.
Record t := mk {
  v : R ;
  H : (0 <= v)%mcR }.
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

Definition mkRnng x H := @Rnng.mk x (introT (RleP _ _) H).

Lemma Rnng_ge0 (x : Rnng) : 0 <= x.
Proof. by case: x => p /= /RleP. Qed.
Local Hint Resolve Rnng_ge0 : core.

Canonical Rnng0 := Eval hnf in @mkRnng 0 (Rle_refl 0).
Canonical Rnng1 := Eval hnf in @mkRnng R1 Rle_0_1.

Lemma addRnng_ge0 (x y : Rnng) : (0 <= (x : R) + y)%mcR.
Proof. exact/RleP/addR_ge0. Qed.
Canonical addRnneg x y := Rnng.mk (addRnng_ge0 x y).

Lemma mulRnng_ge0 (x y : Rnng) : (0 <= (x : R) * y)%mcR.
Proof. exact/RleP/mulR_ge0. Qed.
Canonical mulRnneg x y := Rnng.mk (mulRnng_ge0 x y).

End Rnng_theory.

Global Hint Resolve Rnng_ge0 : core.

Lemma s_of_Rpos_probA (p q r : Rpos) :
  [s_of (p / (p + (q + r)))%:pos%:pr, (q / (q + r))%:pos%:pr] =
  ((p + q) / (p + q + r))%:pos%:pr.
Proof.
apply val_inj; rewrite /= s_of_pqE /onem /=.
rewrite -!RminusE.
rewrite (_ : 1%mcR = 1)// -RmultE.
field.
by split; exact/eqP/Rpos_neq0.
Qed.

Lemma r_of_Rpos_probA (p q r : Rpos) :
  [r_of (p / (p + (q + r)))%:pos%:pr, (q / (q + r))%:pos%:pr] =
  (p / (p + q))%:pos%:pr.
Proof.
apply/val_inj; rewrite /= r_of_pqE s_of_pqE /onem /=.
rewrite -!RminusE -R1E -!RmultE -!RinvE'.
field.
do 3 (split; first exact/eqP/Rpos_neq0).
rewrite (addRC p (q + r)) addRK {4}[in q + r]addRC addRK.
rewrite mulRC -mulRBr (addRC _ p) addRA addRK mulR_neq0.
by split; exact/eqP/Rpos_neq0.
Qed.
