(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Rstruct boolp.
Require Import Reals Lra.
Require Import ssrR.

(******************************************************************************)
(*               Additional lemmas and definitions about Coq reals            *)
(*                                                                            *)
(* Section reals_ext.                                                         *)
(*   various lemmas about up, Int_part, frac_part, Rabs define ceil and floor *)
(* Section pos_finfun.                                                        *)
(*   T ->R^+/->R+ == functions that return non-negative reals.                *)
(* Section onem.                                                              *)
(*   p.~ == 1 - p                                                             *)
(* Module Prob.                                                               *)
(*   Type of "probabilities": reals p s.t. 0 <= p <= 1                        *)
(* non-negative rationals                                                     *)
(* Section dominance.                                                         *)
(* Module Rpos.                                                               *)
(*   Type of positive reals                                                   *)
(* Module Rnneg                                                               *)
(*   Type of non-negative reals                                               *)
(******************************************************************************)

Declare Scope reals_ext_scope.

Reserved Notation "T '->R^+' " (at level 10, format "'[' T  ->R^+ ']'").
Reserved Notation "T '->R+' " (at level 10, format "'[' T  ->R+ ']'").
Reserved Notation "+| r |" (at level 0, r at level 99, format "+| r |").
Reserved Notation "P '<<' Q" (at level 10, Q at next level).
Reserved Notation "P '<<b' Q" (at level 10).
Reserved Notation "p '.~'" (format "p .~", at level 5).
Reserved Notation "'`Pr' p " (format "`Pr  p", at level 6).

Notation "'min(' x ',' y ')'" := (Rmin x y)
  (format "'min(' x ','  y ')'") : reals_ext_scope.
Notation "'max(' x ',' y ')'" := (Rmax x y)
  (format "'max(' x ','  y ')'") : reals_ext_scope.
Notation "+| r |" := (Rmax 0 r) : reals_ext_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Arguments INR : simpl never.

Canonical R_choiceType := ChoiceType R Rstruct.R_choiceMixin.

Local Open Scope R_scope.
Local Open Scope reals_ext_scope.

Section reals_ext.

Lemma Rlt_1_2 : 1 < 2. Proof. lra. Qed.
Local Hint Resolve Rlt_1_2 : core.

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
apply/idP/idP => [/ltRP/Rabs_def2[? ?]|/andP[]/ltRP ? /ltRP ?].
apply/andP; split; exact/ltRP.
exact/ltRP/Rabs_def1.
Qed.

Lemma leR_Rabsl a b : `| a | <b= b = (- b <b= a <b= b).
Proof.
apply/idP/idP => [/leRP|]; last first.
  case/andP => /leRP H1 /leRP H2; exact/leRP/Rabs_le.
case: (Rlt_le_dec a 0) => h.
  rewrite ltR0_norm // => ?; apply/andP; split; apply/leRP; lra.
rewrite geR0_norm // => ?; apply/andP; split; apply/leRP; lra.
Qed.

Lemma factE n0 : fact n0 = n0 `!.
Proof. elim: n0 => // n0 IH /=. by rewrite IH factS mulSn -multE. Qed.

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
Hint Resolve Rlt_1_2 : core.

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

Lemma onem0 : 0.~ = 1.
Proof. by rewrite /onem subR0. Qed.

Lemma onem1 : 1.~ = 0.
Proof. by rewrite /onem subRR. Qed.

Lemma onem_ge0 r : r <= 1 -> 0 <= r.~.
Proof. move=> r1; rewrite /onem; lra. Qed.

Lemma onem_le1 r : 0 <= r -> r.~ <= 1.
Proof. move=> r0; rewrite /onem; lra. Qed.

Lemma onemKC r : r + r.~ = 1.
Proof. rewrite /onem; by field. Qed.

Lemma onemK r : r.~.~ = r.
Proof. by rewrite /onem subRBA addRC addRK. Qed.

Lemma onemD (p q : R) : ((p + q).~ = p.~ + q.~ - 1)%R.
Proof. rewrite /onem; field. Qed.

Lemma onemM (p q : R) : ((p * q).~ = p.~ + q.~ - p.~ * q.~)%R.
Proof. rewrite /onem; field. Qed.

Lemma onem_prob r : (0%R <= r <= R1)%R -> (0%R <= r.~ <= R1)%R.
Proof.
case=> rO r1; split; by [rewrite leR_subr_addr add0R|
  rewrite leR_subl_addr -(addR0 1) leR_add2l].
Qed.

Lemma onem_eq0 r : r.~ = 0 <-> r = 1.
Proof. rewrite /onem; lra. Qed.

Lemma onem_eq1 r : r.~ = 1 <-> r = 0.
Proof. rewrite /onem; lra. Qed.

Lemma onem_neq0 r : r.~ != 0 <-> r != 1.
Proof. by split; apply: contra => /eqP/onem_eq0/eqP. Qed.

Lemma onem_gt0 r : r < 1 -> 0 < r.~. Proof. rewrite /onem; lra. Qed.
Lemma onem_lt1 r : 0 < r -> r.~ < 1. Proof. rewrite /onem; lra. Qed.

End onem.

Notation "p '.~'" := (onem p) : reals_ext_scope.

Module Prob.
Record t := mk {
  p :> R ;
  Op1 : (0 <= p <= 1)%R }.
Definition O1 (p : t) := Op1 p.
Arguments O1 : simpl never.
Lemma ge0 (p : t) : 0 <= p.
Proof. by case: p => [? []]. Qed.
Module Exports.
Notation prob := t.
Notation "'`Pr' q" := (@mk q (@O1 _)).
End Exports.
End Prob.
Export Prob.Exports.
Coercion Prob.p : prob >-> R.

Hint Resolve Prob.ge0 : core.

Definition eqprob (x y : prob) := (x == y :> R).

Lemma eqprobP : Equality.axiom eqprob.
Proof.
move=> -[a Ha] -[b Hb]; rewrite /eqprob /=; apply: (iffP idP) => [/eqP ab| [->] //].
subst a; congr Prob.mk; exact: boolp.Prop_irrelevance.
Qed.

Canonical prob_eqMixin := EqMixin eqprobP.
Canonical prob_eqType := Eval hnf in EqType _ prob_eqMixin.

Lemma probpK p H : Prob.p (@Prob.mk p H) = p. Proof. by []. Qed.

Lemma OO1 : (R0 <= R0 <= R1)%R.
Proof. lra. Qed.

Lemma O11 : (R0 <= R1 <= R1)%R.
Proof. lra. Qed.

Canonical prob0 := Prob.mk OO1.
Canonical prob1 := Prob.mk O11.
Canonical probcplt (p : prob) := @Prob.mk p.~ (onem_prob (Prob.O1 p)).

Lemma prob_le1 (p : prob) : (p <= 1)%R.
Proof. by case: p => p []. Qed.

Lemma prob_gt0 (p : prob) : p != `Pr 0 <-> (0 < p)%R.
Proof.
rewrite ltR_neqAle; split=> [H|[/eqP p0 _]].
split => //; exact/nesym/eqP.
by case: p p0 => p ?; apply: contra => /eqP[/= ->].
Qed.

Lemma prob_lt1 (p : prob) : p != `Pr 1 <-> (p < 1)%R.
Proof.
rewrite ltR_neqAle; split=> [H|[/eqP p1 _]].
split; [exact/eqP|exact/prob_le1].
by case: p p1 => p ?; apply: contra => /eqP[/= ->].
Qed.

Lemma prob_ext (p q : prob) : p = q :> R -> p = q.
Proof.
move: p q => -[p Hp] [q Hq] /= ?; subst q.
by rewrite (@boolp.Prop_irrelevance _ Hp Hq).
Qed.

Lemma probK t : t = `Pr (t.~).~ :> prob.
Proof. by apply prob_ext => /=; rewrite onemK. Qed.

Lemma prob_IZR (p : positive) : (R0 <= / IZR (Zpos p) <= R1)%R.
Proof.
split; first exact/Rlt_le/Rinv_0_lt_compat/IZR_lt/Pos2Z.is_pos.
rewrite -[X in (_ <= X)%R]Rinv_1; apply Rle_Rinv.
- exact: Rlt_0_1.
- exact/IZR_lt/Pos2Z.is_pos.
- exact/IZR_le/Pos2Z.pos_le_pos/Pos.le_1_l.
Qed.

Canonical probIZR (p : positive) := @Prob.mk _ (prob_IZR p).

Definition divRnnm n m := INR n / INR (n + m).

Lemma prob_divRnnm n m : (0 <= divRnnm n m <= 1)%R.
Proof.
rewrite /divRnnm.
have [/eqP ->|n0] := boolP (n == O); first by rewrite div0R; exact OO1.
split; first by apply divR_ge0; [exact: leR0n | rewrite ltR0n addn_gt0 lt0n n0].
by rewrite leR_pdivr_mulr ?mul1R ?leR_nat ?leq_addr // ltR0n addn_gt0 lt0n n0.
Qed.

Canonical probdivRnnm (n m : nat) := @Prob.mk (divRnnm n m) (prob_divRnnm n m).

Lemma prob_invn (m : nat) : (R0 <= / INR (1 + m) <= R1)%R.
Proof.
rewrite -(mul1R (/ _)%R) (_ : 1%R = INR 1) // -/(Rdiv _ _); exact: prob_divRnnm.
Qed.

(* was Canonical *)
Definition probinvn (n : nat) := @Prob.mk (/ INR (1 + n)) (prob_invn n).

Lemma prob_mulR (p q : prob) : (0 <= p * q <= 1)%R.
Proof.
split; first exact/mulR_ge0.
rewrite -(mulR1 1%R); apply leR_pmul => //; [exact/prob_le1 | exact/prob_le1].
Qed.

Canonical probmuLR (p q : prob) := @Prob.mk (p * q) (prob_mulR p q).

Lemma probadd_eq0 (p q : prob) : p + q = `Pr 0 <-> p = `Pr 0 /\ q = `Pr 0.
Proof.
split => [/paddR_eq0 | ].
- move=> /(_ (Prob.ge0 _) (Prob.ge0 _)) [p0 q0]; split; exact/prob_ext.
- by case => -> ->; rewrite addR0.
Qed.

Lemma probadd_neq0 (p q : prob) : p + q != `Pr 0 <-> p != `Pr 0 \/ q != `Pr 0.
Proof.
split => [/paddR_neq0 | ].
- by move=> /(_ (Prob.ge0 _) (Prob.ge0 _)).
- by case; apply: contra => /eqP/probadd_eq0 [] /eqP ? /eqP.
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

(* P is dominated by Q: *)
Section dominance.

Definition dominates {A : Type} (Q P : A -> R) := locked (forall a, Q a = 0 -> P a = 0).

Local Notation "P '<<' Q" := (dominates Q P).

Lemma dominatesP A (Q P : A -> R) : P << Q <-> forall a, Q a = 0 -> P a = 0.
Proof. by rewrite /dominates; unlock. Qed.

Lemma dominatesxx A (P : A -> R) : P << P.
Proof. by apply/dominatesP. Qed.

Let dominatesN A (Q P : A -> R) : P << Q -> forall a, P a != 0 -> Q a != 0.
Proof. by move/dominatesP => H a; apply: contra => /eqP /H ->. Qed.

Lemma dominatesE A (Q P : A -> R) a : P << Q -> Q a = 0 -> P a = 0.
Proof. move/dominatesP; exact. Qed.

Lemma dominatesEN A (Q P : A -> R) a : P << Q -> P a != 0 -> Q a != 0.
Proof. move/dominatesN; exact. Qed.

Lemma dominates_scale (A : finType) (Q P : A -> R) : P << Q ->
  forall k, k != 0 -> P << [ffun a : A => k * Q a].
Proof.
move=> PQ k k0; apply/dominatesP => a /eqP.
by rewrite ffunE mulR_eq0' (negbTE k0) /= => /eqP/(dominatesE PQ).
Qed.

Definition dominatesb {A : finType} (Q P : A -> R) := [forall b, (Q b == 0) ==> (P b == 0)].

End dominance.

Notation "P '<<' Q" := (dominates Q P) : reals_ext_scope.
Notation "P '<<b' Q" := (dominatesb Q P) : reals_ext_scope.

Module Rpos.
Record t := mk {
  v : R ;
  H : v >b 0 }.
Definition K (r : t) := H r.
Arguments K : simpl never.
Module Exports.
Notation Rpos := t.
Notation "'`Pos' r" := (@mk r (@K _)) (format "'`Pos'  r", at level 6).
Coercion v : t >-> R.
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

Lemma Rpos_gt0 (x : Rpos) : x > 0.
Proof. by case: x => p /= /ltRP. Qed.

Lemma Rpos_neq0 (x : Rpos) : val x != 0.
Proof. case: x => p /=. by rewrite /gtRb lt0R => /andP []. Qed.

Lemma addRpos_gt0 (x y : Rpos) : x + y >b 0.
Proof. by apply/ltRP/addR_gt0; apply/Rpos_gt0. Qed.
Canonical addRpos x y := Rpos.mk (addRpos_gt0 x y).

Lemma mulRpos_gt0 (x y : Rpos) : x * y >b 0.
Proof. by apply/ltRP/mulR_gt0; apply/Rpos_gt0. Qed.
Canonical mulRpos x y := Rpos.mk (mulRpos_gt0 x y).

Lemma divRpos_gt0 (x y : Rpos) : x / y >b 0.
Proof. by apply/ltRP/divR_gt0; apply/Rpos_gt0. Qed.
Canonical divRpos x y := Rpos.mk (divRpos_gt0 x y).

Lemma prob_divRposxxy (x y : Rpos) : (0 <= `Pos (x / (x + y)) <= 1)%R.
Proof.
split.
  apply/divR_ge0; [exact/ltRW/Rpos_gt0 | exact/ltRP/addRpos_gt0].
rewrite leR_pdivr_mulr ?mul1R; last exact/ltRP/addRpos_gt0.
by rewrite leR_addl; apply/ltRW/Rpos_gt0.
Qed.

Canonical divRposxxt (x y : Rpos) := @Prob.mk _ (prob_divRposxxy x y).

Module Rnneg.
Local Open Scope R_scope.
Record t := mk {
  v : R ;
  H : 0 <b= v }.
Definition K (r : t) := H r.
Arguments K : simpl never.
Module Exports.
Notation Rnneg := t.
Notation "'`Nneg' r" := (@mk r (@K _)) (format "'`Nneg'  r", at level 6).
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
