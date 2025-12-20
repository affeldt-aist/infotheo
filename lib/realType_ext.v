(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg archimedean ssrnum ssrint.
From mathcomp Require Import reals normedtype sequences exp.
From mathcomp Require Import unstable mathcomp_extra boolp interval_inference.
From mathcomp Require Import ring lra.

(**md**************************************************************************)
(* # Additional definitions and lemmas about numeric types                    *)
(*                                                                            *)
(* TODO: doc incomplete                                                       *)
(*                                                                            *)
(* ```                                                                        *)
(*      +| r | := maxr 0 r                                                    *)
(*     P `<< Q == P is dominated by Q, i.e., forall a, Q a = 0 -> P a = 0     *)
(*    P `<<b Q == boolean version of P `<< Q                                  *)
(* frac_part x := x - (Num.floor x)%:~R                                       *)
(*    {prob R} == type of "probabilities", i.e., reals p s.t. 0 <= p <= 1     *)
(*   {oprob R} == type of "open unit interval", i.e., reals p s.t. 0 < p < 1  *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Declare Scope reals_ext_scope.

Reserved Notation "+| r |" (at level 0, r at level 99, format "+| r |").
Reserved Notation "p '.~'" (format "p .~", at level 1).
Reserved Notation "P '`<<' Q" (at level 51).
Reserved Notation "P '`<<b' Q" (at level 51).
Reserved Notation "{ 'prob' T }" (at level 0, format "{ 'prob'  T }").
Reserved Notation "x %:pr" (at level 1, format "x %:pr").
Reserved Notation "x %:opr" (at level 1, format "x %:opr").
Reserved Notation "[ 's_of' p , q ]" (format "[ 's_of'  p ,  q ]").
Reserved Notation "[ 'r_of' p , q ]" (format "[ 'r_of'  p ,  q ]").
Reserved Notation "[ 'p_of' r , s ]" (format "[ 'p_of'  r ,  s ]").
Reserved Notation "[ 'q_of' r , s ]" (format "[ 'q_of'  r ,  s ]").

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import Order.POrderTheory Order.TotalTheory GRing.Theory Num.Theory.

Definition ex2C (T : Type) (P Q : T -> Prop) : @ex2 T P Q <-> @ex2 T Q P.
Proof. by split; case=> x H0 H1; exists x. Qed.

Lemma asboolTE : `[< True >] = true.
Proof.
apply: (asbool_equiv_eqP (Q:=True)) => //.
by constructor.
Qed.

Notation "+| r |" := (Num.Def.maxr 0%R r) : reals_ext_scope.

(* TODO: move to "mathcomp_extra.v" *)
Section num_ext.
Local Open Scope ring_scope.
(* analogs of ssrR.(pmulR_lgt0', pmulR_rgt0') *)
Lemma wpmulr_lgt0 (R : numDomainType) (x y : R) : 0 <= x -> 0 < y * x -> 0 < y.
Proof.
rewrite le_eqVlt=> /orP [/eqP <- |].
  by rewrite mulr0 ltxx.
by move/pmulr_lgt0->.
Qed.

Lemma wpmulr_rgt0 (R : numDomainType) (x y : R) : 0 <= x -> 0 < x * y -> 0 < y.
Proof. by rewrite mulrC; exact: wpmulr_lgt0. Qed.
End num_ext.

Lemma eqr_divrMr {R : realType} (z x y : R) : z != 0%R ->
  (y / z = x)%R <-> (y = x * z)%R.
Proof.
move=> z0; split => [<-|->]; first by rewrite -mulrA mulVf // mulr1.
by rewrite -mulrA mulfV // mulr1.
Qed.

Lemma prodr_gt0 (R : numDomainType) (A : finType) (F : A -> R) :
  (forall a, 0 < F a)%R ->
  (0 < \prod_(a : A) F a)%R.
Proof. by move=> F0; elim/big_ind : _ => // x y ? ?; exact: mulr_gt0. Qed.

(* PR to mathcomp_extra.v? *)
Section onem.
Local Open Scope ring_scope.
Variable R : realFieldType.
Implicit Types r s : R.

Lemma onem_le r s : (r <= s) = (`1-s <= `1-r).
Proof.
apply/idP/idP => [|?]; first exact: lerB.
by rewrite -(opprK r) lerNl -(lerD2l 1).
Qed.

Lemma onem_lt  r s : (r < s) = (`1-s < `1-r).
Proof.
apply/idP/idP => [rs|]; first by rewrite ler_ltB.
by rewrite ltrBrDl addrCA -ltrBrDl subrr subr_lt0.
Qed.

Lemma onemE r : `1-r = 1 - r.  Proof. by []. Qed.

Lemma onem_div r s : s != 0 -> `1-(r / s) = (s - r) / s.
Proof. by rewrite !onemE => q0; rewrite mulrDl mulNr divff. Qed.

Lemma onem_prob r : 0 <= r <= 1 -> 0 <= onem r <= 1.
Proof.
by move=> /andP[r0 r1]; apply/andP; split; [rewrite onem_ge0|rewrite onem_le1].
Qed.

Lemma onem_eq0 r : (`1-r = 0) <-> (r = 1).
Proof. by rewrite /onem; split => [/subr0_eq//|->]; rewrite subrr. Qed.

Lemma onem_neq0 (r : R) : (`1-r != 0) <-> (r != 1).
Proof. by split; apply: contra => /eqP/onem_eq0/eqP. Qed.

Lemma onem_eq1 r : `1-r = 1 <-> r = 0. Proof. rewrite onemE; lra. Qed.

Lemma onem_oprob r : 0 < r < 1 -> 0 < `1-r < 1.
Proof. by move=> /andP [? ?]; apply/andP; rewrite onem_gt0 // onem_lt1. Qed.

Lemma subr_onem r s : r - `1-s = r + s - 1.
Proof. by rewrite /onem opprB addrA. Qed.

End onem.
Notation "p '.~'" := (onem p).

Section about_the_pow_function.
Local Open Scope ring_scope.

Lemma x_x2_eq {R : realFieldType} (q : R) :
  q * (1 - q) = 4^-1 - 4^-1 * (2 * q - 1) ^+ 2.
Proof. by field. Qed.

Lemma x_x2_max {R : realFieldType} (q : R) : q * (1 - q) <= 4^-1.
Proof.
rewrite x_x2_eq.
have : forall a b : R, 0 <= b -> a - b <= a. move=> *; lra.
apply; apply: mulr_ge0; [lra | exact: exprn_even_ge0].
Qed.

Lemma x_x2_pos {R : realFieldType} (q : R) : 0 < q < 1 -> 0 < q * (1 - q).
Proof.
move=> q01.
rewrite [ltRHS](_ : _ = - (q - 2^-1)^+2 + (2^-2)); last by field.
rewrite addrC subr_gt0 -exprVn -[ltLHS]real_normK ?num_real//.
rewrite ltr_pXn2r// ?nnegrE; [| lra].
have/orP[H|H]:= le_total (q - 2^-1) 0.
  rewrite (ler0_norm H); lra.
rewrite (ger0_norm H); lra.
Qed.

Lemma x_x2_nneg {R : realFieldType} (q : R) : 0 <= q <= 1 -> 0 <= q * (1 - q).
Proof.
case/andP=> q0 q1.
have[->|qneq0]:= eqVneq q 0; first lra.
have[->|qneq1]:= eqVneq q 1; first lra.
have: 0 < q < 1 by lra.
by move/x_x2_pos/ltW.
Qed.

End about_the_pow_function.

(* TODO: prove expR1_lt3 too; PR to mca *)
Lemma expR1_gt2 {R : realType} : (2 < expR 1 :> R)%R.
Proof. by rewrite (lt_le_trans (@expR_gt1Dx _ 1 _))// oner_eq0. Qed.

Section dominance_defs.

Definition dominates {R : realType} {A : Type} (Q P : A -> R) :=
  locked (forall a, Q a = 0 -> P a = 0)%R.

Local Notation "P '`<<' Q" := (dominates Q P).

Lemma dominatesP {R : realType} A (Q P : A -> R) :
  P `<< Q <-> forall a, Q a = 0%R -> P a = 0%R.
Proof. by rewrite /dominates; unlock. Qed.

End dominance_defs.

Notation "P '`<<' Q" := (dominates Q P).

Section dominance.
Context {R : realType}.

Lemma dominatesxx A (P : A -> R) : P `<< P.
Proof. by apply/dominatesP. Qed.

Let dominatesN A (Q P : A -> R) : P `<< Q -> forall a, P a != 0%R -> Q a != 0%R.
Proof. by move/dominatesP => H a; apply: contra => /eqP /H ->. Qed.

Lemma dominatesE A (Q P : A -> R) a : P `<< Q -> Q a = 0%R -> P a = 0%R.
Proof. move/dominatesP; exact. Qed.

Lemma dominatesEN A (Q P : A -> R) a : P `<< Q -> P a != 0%R -> Q a != 0%R.
Proof. move/dominatesN; exact. Qed.

Lemma dominates_scale (A : finType) (Q P : A -> R) : P `<< Q ->
  forall k : R, k != 0%R -> P `<< [ffun a : A => k * Q a]%R.
Proof.
move=> PQ k k0; apply/dominatesP => a /eqP.
by rewrite ffunE mulf_eq0 (negbTE k0)/= => /eqP/(dominatesE PQ).
Qed.

Definition dominatesb {A : finType} (Q P : A -> R) :=
  [forall b, (Q b == 0%R) ==> (P b == 0%R)].

End dominance.

Notation "P '`<<' Q" := (dominates Q P) : reals_ext_scope.
Notation "P '`<<b' Q" := (dominatesb Q P) : reals_ext_scope.

Module Prob.
Section prob.
Context {R : realType}.
Lemma O1 (p : {i01 R}) : (0 <= p%:num <= 1)%R.
Proof. by apply/andP; split. Qed.
Definition mk (q : R) (O1 : (0 <= q <= 1)%R) : {i01 R} :=
  Itv01 (andP O1).1 (andP O1).2.
#[deprecated(since="infotheo 0.9.7", note="use %:num instead")]
Definition p (t : {i01 R}) := t%:num%R.
End prob.
End Prob.

(* #[deprecated(since="infotheo 0.9.7", note="use %:i01 instead")]
Notation "q %:pr" := (q%:num)%R. *)
Notation "q %:pr" := (@Prob.mk _ q (@Prob.O1 _ _)).

#[deprecated(since="infotheo 0.9.7", note="use {i01 _} instead")]
Notation "'prob' R" := {i01 R} (at level 1).

(*#[deprecated(since="infotheo 0.9.7", note="use {i01 _} instead")]*)
Notation "{ 'prob' R }" := {i01 R}.

Section prob_lemmas.
Local Open Scope ring_scope.
Variable R : realType.
Implicit Types p q : {prob R}.

#[deprecated(since="infotheo 0.9.7", note="use 0%:i01 instead")]
Definition prob0 : {i01 R} := 0%:i01.
#[deprecated(since="infotheo 0.9.7", note="use 1%:i01 instead")]
Definition prob1 : {i01 R} := 1%:i01.

Canonical probcplt (p : {prob R}) :=
  Eval hnf in Prob.mk (onem_prob (Prob.O1 p)).

#[deprecated(since="infotheo 0.9.7", note="use ge0 instead")]
Lemma prob_ge0 (p : {prob R}) : (0 <= p%:num)%R.
Proof. done. Qed.

#[deprecated(since="infotheo 0.9.7", note="use le1 instead")]
Lemma prob_le1 (p : {prob R}) : (p%:num <= 1)%R.
Proof. done. Qed.

Lemma prob_gt0 (p : {prob R}) : p != 0%:i01 <-> 0 < p%:num.
Proof.
rewrite lt_neqAle; split=> [H|/andP[+ pge0]].
  by apply/andP; split; [rewrite eq_sym|exact: ge0].
by apply: contra => /eqP ->.
Qed.

(*Lemma prob_gt0' p : p != 0 :> R <-> 0 < Prob.p p.
Proof. exact: prob_gt0. Qed.*)

Lemma prob_lt1 (p : {prob R}) : p != 1%:i01 <-> p%:num < 1.
Proof.
rewrite lt_neqAle; split=> [H|/andP[+ pge0]].
  by apply/andP; split => //; exact: le1.
by apply: contra => /eqP ->.
Qed.

(*Lemma prob_lt1' p : p != 1 :> R <-> Prob.p p < 1.
Proof. exact: prob_lt1. Qed.*)

Lemma prob_trichotomy p : p = 0%:i01 \/ p = 1%:i01 \/ 0 < p%:num < 1.
Proof.
have [->|pneq0]:= eqVneq p 0%:i01; first by left.
right.
have [->|pneq1] := eqVneq p 1%:i01; first by left.
by right; apply/andP; split; [exact/prob_gt0|exact/prob_lt1].
Qed.

(* TODO: rename to prob_onemK and prob_onemKC? *)
Lemma probK p : p = (p%:num.~).~%:i01.
Proof. by apply: val_inj => /=; rewrite onemK. Qed.

Lemma probKC (p : {prob R}) : p%:num + p%:num.~ = 1 :> R.
Proof. exact: add_onemK. Qed.

Lemma probadd_eq0 p q : p%:num + q%:num = 0 <-> p = 0%:i01 /\ q = 0%:i01.
Proof.
split; last by move=> [-> ->] /=; rewrite addr0.
move/eqP; rewrite paddr_eq0; [|exact: ge0|exact: ge0].
by move=> /andP[/eqP ? /eqP ?]; split; exact/val_inj.
Qed.

Lemma probadd_neq0 p q : p%:num + q%:num != 0 <-> p != 0%:i01 \/ q != 0%:i01.
Proof.
apply/iff_not2; split=> [/negP/negPn/eqP/probadd_eq0[-> ->]|].
  by apply/not_orP; split; apply/negP/negPn.
move=> /not_orP[/negP/negPn/eqP -> /negP/negPn/eqP -> /=]; apply/negP/negPn.
by rewrite addr0.
Qed.

Lemma probmul_eq1 p q : p%:num * q%:num = 1 <-> p = 1%:i01 /\ q = 1%:i01.
Proof.
split => [/= pq1|[-> ->]]; last by rewrite mulr1.
move: (oner_neq0 R); rewrite -{1}pq1 mulf_eq0 negb_or => /andP[p0 q0].
have := prob_le1 p; rewrite le_eqVlt => /orP[/eqP p1|p1].
  by rewrite p1 mul1r in pq1; split; exact/val_inj.
have := prob_le1 q; rewrite le_eqVlt => /orP[/eqP q1|q1].
  by rewrite q1 mulr1 in pq1; split; exact/val_inj.
have {}p0 : 0 < p%:num by rewrite lt_neqAle ge0 eq_sym andbT.
by move: p1; rewrite -[in X in X -> _]pq1 (ltr_pMr _ p0) ltNge (ltW q1).
Qed.

End prob_lemmas.

Global Hint Resolve prob_ge0 : core.
Global Hint Resolve prob_le1 : core.

#[export] Hint Extern 0 (is_true (@Order.le ring_display _ _ _)) =>
  exact/prob_le1 : core.
#[export] Hint Extern 0 (is_true (@Order.le ring_display _ _ _)) =>
  exact/prob_ge0 : core.

Arguments prob0 {R}.
Arguments prob1 {R}.

Lemma prob_invn {R : realType} (m : nat) :
  (0 <= ((1 + m)%:R^-1 : R) <= 1)%R.
Proof.
apply/andP; split.
  by rewrite invr_ge0.
by rewrite invf_le1// natrD lerDl.
Qed.

Canonical probinvn {R : realType} (n : nat) :=
  Eval hnf in @Prob.mk _ ((1 + n)%:R^-1) (@prob_invn R n).

(* TODO: rename oprob to i01oo (and prob to i01cc) *)
Module OProb.
Section def.
Local Open Scope ring_scope.
Record t (R: realType):= mk {
  p :> {prob R};
  Op1 : (0 < p%:num < 1)%R }.
Definition O1 (R: realType) (x : t R) : 0 < (p x)%:num < 1 := Op1 x.
Arguments O1 : simpl never.
End def.
Module Exports.
Notation oprob := t.

Notation "q %:opr" := (@mk _ q (@O1 _ _)).
HB.instance Definition _ (R : realType) := [isSub for @p R].
HB.instance Definition _ (R : realType) := [Equality of t R by <:].
End Exports.
End OProb.
Export OProb.Exports.
(*Coercion OProb.p : oprob >-> prob.*)
Canonical oprobcplt [R: realType] (p : oprob R) :=
  Eval hnf in OProb.mk (onem_oprob (OProb.O1 p)).

Reserved Notation "{ 'oprob' T }" (at level 0, format "{ 'oprob'  T }").
Notation "{ 'oprob' T }" := (@oprob T).
Notation oprob_to_real o := ((OProb.p o)%:num)%R.

Section oprob_lemmas.
Local Open Scope ring_scope.
Variable R : realType.
Implicit Types p q : {oprob R}.

Lemma oprob_gt0 p : 0 < oprob_to_real p.
Proof. by case : p => p /= /andP []. Qed.

Lemma oprob_lt1 p : oprob_to_real p < 1.
Proof. by case: p => p /= /andP [] _. Qed.

Import Order.POrderTheory Order.TotalTheory.

Lemma oprob_neq0 p : oprob_to_real p != 0 :> R.
Proof. by move:(oprob_gt0 p); rewrite lt_neqAle=> /andP -[] /eqP/nesym/eqP. Qed.

Lemma oprob_neq1 p : oprob_to_real p != 1 :> R.
Proof. by move:(oprob_lt1 p); rewrite lt_neqAle=> /andP -[]. Qed.

Lemma oprob_onemK (p : {oprob R}) : p = ((oprob_to_real p).~).~%:pr%:opr.
Proof. by apply/val_inj/val_inj=> /=; rewrite onemK. Qed.

(* TODO: rename? *)
Lemma prob_trichotomy' (p : {prob R}) (P : {prob R} -> Prop) :
  P 0%:i01 -> P 1%:i01 -> (forall o : {oprob R}, P (OProb.p o)) -> P p.
Proof.
move=> p0 p1 po.
have [->//|[->//|p01]] := prob_trichotomy p.
exact: (po (@OProb.mk _ _ p01)).
Qed.

Lemma oprobadd_gt0 p q : 0 < oprob_to_real p + oprob_to_real q.
Proof. exact/addr_gt0/oprob_gt0/oprob_gt0. Qed.

Lemma oprobadd_neq0 p q : oprob_to_real p + oprob_to_real q != 0.
Proof.
by move: (oprobadd_gt0 p q); rewrite lt_neqAle => /andP -[] /eqP/nesym/eqP.
Qed.

End oprob_lemmas.

Section prob_lemmas2.
Local Open Scope ring_scope.
Variable R : realType.
Implicit Types p q : {prob R}.

Definition divrnnm n m := (n%:R / (n + m)%:R) : R.

Lemma prob_divrnnm_subproof n m : (0 <= divrnnm n m <= 1)%O.
Proof.
apply/andP; split.
  by rewrite /divrnnm divr_ge0.
rewrite /divrnnm.
have [->|n0] := eqVneq n 0.
  by rewrite mul0r ler01.
rewrite ler_pdivrMr// ?ltr0n ?addn_gt0; last first.
  by rewrite lt0n n0.
by rewrite mul1r ler_nat leq_addr.
Qed.

Canonical probdivrnnm (n m : nat) :=
  Eval hnf in @Prob.mk _ (divrnnm n m) (prob_divrnnm_subproof n m).

Lemma prob_invprob_subproof (p : {prob R}) : (0 <= 1 / (1 + p%:num) <= 1)%O.
Proof.
apply/andP; split.
  by rewrite mul1r invr_ge0 ?addr_ge0.
by rewrite mul1r invf_le1// lerDl.
Qed.

(* canonicalizing this definition breaks s_of_pq *)
Definition prob_invprob (p : {prob R}) := Prob.mk (prob_invprob_subproof p).

Lemma prob_mulr_subproof (p q : {prob R}) : (0 <= p%:num * q%:num <= 1)%R.
Proof.
apply/andP; split.
  by rewrite mulr_ge0.
by rewrite mulr_ile1.
Qed.

Canonical probmulr (p q : {prob R}) :=
  Eval hnf in @Prob.mk _ (p%:num * q%:num) (prob_mulr_subproof p q).

End prob_lemmas2.

Definition s_of_pq {R : realType} (p q : {prob R}) : {prob R} :=
  locked ((p%:num).~ * (q%:num).~).~%:i01%R.

Declare Scope reals_ext_scope.
Notation "[ 's_of' p , q ]" := (s_of_pq p q) : reals_ext_scope.

Local Open Scope reals_ext_scope.

Section s_of_pq_lemmas.
Variable R : realType.
Implicit Types p q : {prob R}.
Local Open Scope ring_scope.

Lemma s_of_pqE p q : [s_of p, q]%:num = ((p%:num).~ * (q%:num).~)%R.~ :> R.
Proof. by rewrite /s_of_pq; unlock. Qed.

Lemma s_of_0q q : [s_of 0%:i01, q] = q.
Proof. by apply/val_inj; rewrite /= s_of_pqE onem0 mul1r onemK. Qed.

Lemma s_of_1q q : [s_of 1%:i01, q] = 1%:i01.
Proof. by apply/val_inj; rewrite /= s_of_pqE onem1 mul0r onem0. Qed.

Lemma s_of_p0 p : [s_of p, 0%:i01] = p.
Proof. by apply/val_inj; rewrite /= s_of_pqE onem0 mulr1 onemK. Qed.

Lemma s_of_p1 p : [s_of p, 1%:i01] = 1%:i01.
Proof. by apply/val_inj; rewrite /= s_of_pqE onem1 mulr0 onem0. Qed.

Lemma s_of_gt0 p q : p != 0%:i01 -> (0 < [s_of p, q]%:num)%R.
Proof.
move=> p0; rewrite s_of_pqE; apply: onem_gt0.
have [->/=|q0] := eqVneq q 0%:i01.
  by rewrite onem0 mulr1 onem_lt1// lt0r p0/=.
rewrite mulr_ilte1 => //=.
  by rewrite onem_lt1// lt0r p0/=.
by rewrite onem_lt1// lt0r q0/=.
Qed.

Lemma ge_s_of p q : (p%:num <= [s_of p, q]%:num)%R.
Proof.
rewrite s_of_pqE.
rewrite onemE.
rewrite addrC.
rewrite -lerBlDr.
rewrite -opprB.
rewrite lerNl opprK.
rewrite -/(p%:num).~.
by rewrite ler_piMr.
Qed.

End s_of_pq_lemmas.

Lemma r_of_pq_subproof {R : realType} (p q : {prob R}) :
  (0 <= p%:num / [s_of p, q]%:num <= 1)%R.
Proof.
have [->|p0] := eqVneq p 0%:i01%R.
  by rewrite mul0r lexx ler01.
have [->|a0] := eqVneq q 0%:i01%R.
  by rewrite s_of_p0 divff// lexx ler01.
apply/andP; split.
  by rewrite divr_ge0.
rewrite ler_pdivrMr ?mul1r.
  exact: ge_s_of.
by rewrite s_of_gt0.
Qed.

Definition r_of_pq {R : realType} (p q : {prob R}) : {prob R} :=
  locked (Prob.mk (r_of_pq_subproof p q)).

Notation "[ 'r_of' p , q ]" := (r_of_pq p q) : reals_ext_scope.

Section r_of_pq_lemmas.
Variable R : realType.
Implicit Types p q : {prob R}.
Local Open Scope ring_scope.

Lemma r_of_pqE p q : [r_of p, q]%:num = p%:num / [s_of p, q]%:num :> R.
Proof. by rewrite /r_of_pq; unlock. Qed.

Lemma r_of_p0 p : p != 0%:i01 -> [r_of p, 0%:i01] = 1%:i01.
Proof. by move=> p0; apply: val_inj; rewrite /= r_of_pqE s_of_p0 divff. Qed.

Lemma r_of_0q q : [r_of 0%:i01, q] = 0%:i01.
Proof. by apply/val_inj; rewrite /= r_of_pqE mul0r. Qed.

Lemma r_of_p1 p : [r_of p, 1%:i01] = p.
Proof. by apply/val_inj; rewrite /= r_of_pqE s_of_p1 invr1 mulr1. Qed.

Lemma r_of_1q q : [r_of 1%:i01, q] = 1%:i01.
Proof. by apply/val_inj; rewrite /= r_of_pqE s_of_1q/= invr1 mulr1. Qed.

End r_of_pq_lemmas.

Lemma p_is_rs {R : realType} (p q : {prob R}) :
  p%:num%R = ([r_of p, q]%:num * [s_of p, q]%:num)%R :> R.
Proof.
have [->/=|p0] := eqVneq p 0%:i01%R; first by rewrite r_of_0q mul0r.
have [->/=|q0] := eqVneq q 0%:i01%R.
  by rewrite s_of_p0 r_of_p0 // mul1r.
rewrite r_of_pqE -mulrA mulVf ?mulr1 //.
suff : [s_of p, q]%:num%R != 0%R :> R by [].
by rewrite prob_gt0 s_of_gt0.
Qed.

Lemma p_of_rs_subproof {R : realType} (r s : {prob R}) :
  (0 <= r%:num * s%:num <= 1)%R.
Proof.
by apply/andP; split; [rewrite mulr_ge0|rewrite mulr_ile1].
Qed.

Definition p_of_rs {R : realType} (r s : {prob R}) : {prob R} :=
  locked (Prob.mk (p_of_rs_subproof r s)).

Notation "[ 'p_of' r , s ]" := (p_of_rs r s) : reals_ext_scope.

Section p_of_rs_lemmas.
Variable R : realType.
Implicit Types r s : {prob R}.
Local Open Scope ring_scope.

Lemma p_of_rsE r s : [p_of r, s]%:num = r%:num * s%:num :> R.
Proof. by rewrite /p_of_rs; unlock. Qed.

Lemma p_of_r1 r : [p_of r, 1%:i01] = r.
Proof. by apply: val_inj; rewrite /= p_of_rsE mulr1. Qed.

Lemma p_of_1s s : [p_of 1%:i01, s] = s.
Proof. by apply: val_inj; rewrite /= p_of_rsE mul1r. Qed.

Lemma p_of_r0 r : [p_of r, 0%:i01] = 0%:i01.
Proof. by apply/val_inj; rewrite /= p_of_rsE mulr0. Qed.

Lemma p_of_0s s : [p_of 0%:i01, s] = 0%:i01.
Proof. by apply/val_inj; rewrite /= p_of_rsE mul0r. Qed.

Lemma p_of_rsC r s : [p_of r, s] = [p_of s, r].
Proof. by apply/val_inj; rewrite /= !p_of_rsE mulrC. Qed.

Lemma p_of_neq1 r s : (0 < s%:num < 1)%R -> [p_of r, s] != 1%:i01.
Proof.
case/andP=> p0 p1; apply/eqP => pq1; move: (p1).
rewrite [X in (_ < X)%R -> _](_ : _ = 1%:i01%:num) //.
rewrite -pq1 p_of_rsE -ltr_pdivrMr // divff ?gt_eqF//.
by rewrite ltNge le1.
Qed.

Lemma p_of_rs1 r s :
  ([p_of r, s] == 1%:i01 :> {prob R}) = ((r == 1%:i01) && (s == 1%:i01)).
Proof.
rewrite -(inj_eq val_inj)/= p_of_rsE.
apply/idP/idP; last first.
  by case/andP => /eqP -> /eqP ->/=; rewrite mulr1.
by move/eqP/probmul_eq1 => -[<- <-]; rewrite !eqxx.
Qed.

Lemma p_of_rs1P r s : reflect (r = 1%:i01 /\ s = 1%:i01) ([p_of r, s] == 1%:i01).
Proof.
move: (p_of_rs1 r s) ->.
apply: (iffP idP);
  [by case/andP => /eqP -> /eqP -> | by case => -> ->; rewrite eqxx].
Qed.

End p_of_rs_lemmas.

Lemma q_of_rs_prob {R : realType} (r s : {prob R}) :
  (0 <= (r%:num.~ * s%:num) / [p_of r, s]%:num.~ <= 1)%R.
Proof.
Local Open Scope ring_scope.
have [->|r1] := eqVneq r 1%:i01.
  by rewrite onem1 !mul0r lexx ler01.
have [->|s1] := eqVneq s 1%:i01.
  rewrite mulr1 p_of_r1 divff ?onem_neq0//.
  by rewrite ler01// lexx.
apply/andP; split.
  by rewrite divr_ge0// mulr_ge0.
rewrite ler_pdivrMr// ?mul1r.
  by rewrite p_of_rsE {2}/onem lerBrDr -mulrDl addrC add_onemK mul1r.
rewrite onem_gt0// -prob_lt1.
apply/p_of_rs1P/not_andP; left.
exact/eqP.
Qed.

Lemma r_of_pq_is_r {R : realType} (p q r s : {prob R}) : r != 0%:i01 -> s != 0%:i01 ->
  (p%:num = r%:num * s%:num :> R ->
   (s%:num).~ = (p%:num).~ * (q%:num).~ -> [r_of p, q] = r)%R.
Proof.
move=> r0 s0 H1 H2; apply: val_inj => /=.
by rewrite r_of_pqE s_of_pqE -H2 onemK H1 -mulrA divff ?mulr1//.
Qed.

Definition q_of_rs {R : realType} (r s : {prob R}) : {prob R} :=
  locked (Prob.mk (q_of_rs_prob r s)).

Notation "[ 'q_of' r , s ]" := (q_of_rs r s) : reals_ext_scope.

Section q_of_rs_lemmas.
Variable R : realType.
Implicit Types r s : {prob R}.

Lemma q_of_rsE r s :
  [q_of r, s]%:num = ((r%:num.~ * s%:num) / [p_of r, s]%:num.~)%R :> R.
Proof.
by rewrite /q_of_rs; unlock.
Qed.

Lemma q_of_r0 r : [q_of r, 0%:i01] = 0%:i01.
Proof. by apply/val_inj => /=; rewrite q_of_rsE mulr0 mul0r. Qed.

Lemma q_of_r1 r : r != 1%:i01 -> [q_of r, 1%:i01] = 1%:i01.
Proof.
move=> r1.
by apply/val_inj => /=; rewrite q_of_rsE /= mulr1 p_of_r1 divff // onem_neq0.
Qed.

Lemma q_of_1s s : [q_of 1%:i01, s] = 0%:i01.
Proof. by apply/val_inj => /=; rewrite q_of_rsE onem1 !mul0r. Qed.

End q_of_rs_lemmas.

Lemma pq_is_rs {R : realType} (p q : {prob R}) :
  ((p%:num).~ * q%:num = ([r_of p, q]%:num).~ * [s_of p, q]%:num)%R.
Proof.
have [->|p0] := eqVneq p 0%:i01.
  by rewrite onem0 mul1r r_of_0q onem0 mul1r s_of_0q.
rewrite r_of_pqE [in RHS]mulrBl mul1r -mulrA mulVf ?mulr1; last first.
  by rewrite prob_gt0; exact/s_of_gt0.
rewrite s_of_pqE onemM !onemK /onem mulrBl mul1r [RHS]addrC !addrA.
lra.
Qed.

Lemma s_of_pqK {R : realType} (r s : {prob R}) : [p_of r, s] != 1%:i01 ->
  [s_of [p_of r, s], [q_of r, s]] = s.
Proof.
move=> H.
apply/val_inj; rewrite /= s_of_pqE p_of_rsE q_of_rsE p_of_rsE /=.
rewrite /onem.
field.
rewrite subr_eq0; apply: contra H => /eqP rs1.
by apply/eqP/val_inj; rewrite /= p_of_rsE.
Qed.

Lemma r_of_pqK {R : realType} (r s : {prob R}) :
  [p_of r, s] != 1%:i01 -> s != 0%:i01 ->
  [r_of [p_of r, s], [q_of r, s]] = r.
Proof.
move=> H1 s0; apply/val_inj => /=.
rewrite !(r_of_pqE,s_of_pqE,q_of_rsE,p_of_rsE) /onem.
suff rs_neq1 : (1 - r%:num * s%:num != 0)%R.
  (field; do ?[apply/andP; split]) => //.
  by rewrite mulrBl mul1r !opprB -!addrA addrC !addrA !subrK ?subrr ?add0r.
rewrite subr_eq0.
apply: contra H1 => /eqP H1.
by apply/eqP/val_inj; rewrite /= p_of_rsE.
Qed.

Lemma oprob_divrposxxy {R : realType} (x y : {posnum R}%R) :
  (0 < x%:num / (x%:num + y%:num) < 1)%R.
Proof.
rewrite divr_gt0//=.
by rewrite ltr_pdivrMr// mul1r ltrDl.
Qed.

Lemma prob_divrposxxy {R : realType} (x y : {posnum R}%R) :
  (0 <= x%:num / (x%:num + y%:num) <= 1)%R.
Proof.
have /andP[] := oprob_divrposxxy x y.
by move/ltW => -> /ltW ->.
Qed.

Canonical divrposxxy {R : realType} (x y : {posnum R}%R) :=
  Eval hnf in Prob.mk (prob_divrposxxy x y).

Lemma s_of_rpos_probA {R : realType} (p q r : {posnum R}%R) :
  [s_of divrposxxy p ((q%:num + r%:num)%:pos)%R, divrposxxy q r] =
  divrposxxy (p%:num + q%:num)%:pos%R r.
Proof.
apply: val_inj; rewrite /= s_of_pqE.
rewrite onemM !onemK/=.
by field; do ?[apply/andP; split].
Qed.

Lemma r_of_rpos_probA {R : realType} (p q r : {posnum R}%R) :
  [r_of divrposxxy p (q%:num + r%:num)%:pos%R, divrposxxy q r] =
  divrposxxy p q%R.
Proof.
apply/val_inj; rewrite /= r_of_pqE s_of_pqE /onem /=.
field; do ?[apply/andP; split]; do ?[by []].
rewrite (addrC p%:num (q%:num + r%:num)%:pos%:num)%R addrK {4}[in (q%:num + r%:num)%R]addrC addrK.
by rewrite mulrC -mulrBr (addrC _ p%:num%R) addrA addrK mulf_neq0//.
Qed.

Lemma r_of_p0_oprob {R : realType} (p : {oprob R}) :
  [r_of (OProb.p p), 0%:i01] = 1%:i01.
Proof. exact/r_of_p0/oprob_neq0. Qed.

Lemma onem_divrxxy {R : realType} (r q : {posnum R}%R) :
  (r%:num / (r%:num + q%:num)).~ = (q%:num / (q%:num + r%:num))%R.
Proof.
rewrite /onem; apply/eqP; rewrite subr_eq.
by rewrite (addrC (r%:num%R : R)) -mulrDl divff.
Qed.

Section leR_ltR_sumR_finType.
Context {R : realType}.
Variables (A : finType) (f g : A -> R) (P Q : pred A).
Local Open Scope ring_scope.

Lemma leR_sumR_support (X : {set A}) :
  (forall i, i \in X -> P i -> f i <= g i) ->
  \sum_(i in X | P i) f i <= \sum_(i in X | P i) g i.
Proof.
move=> H; elim/big_rec2 : _ => //.
move=> a x y /andP[aX Pa] yx.
by apply: lerD => //; apply: H.
Qed.

Lemma leR_sumRl : (forall i, P i -> f i <= g i) ->
  (forall i, Q i -> 0 <= g i) -> (forall i, P i -> Q i) ->
  \sum_(i | P i) f i <= \sum_(i | Q i) g i.
Proof.
move=> f_g Qg H; elim: (index_enum _) => [| h t IH].
- rewrite !big_nil.
  by rewrite lexx.
- rewrite !big_cons /=; case: ifP => [Ph|Ph].
    by rewrite (H _ Ph); apply: lerD => //; exact: f_g.
  case: ifP => // Qh; apply: (le_trans IH).
  by rewrite -{1}[X in X <= _](add0r _) lerD2r Qg.
Qed.

Lemma leR_sumRl_support (U : pred A) :
  (forall a, 0 <= f a) -> (forall i, P i -> Q i) ->
  \sum_(i in U | P i) f i <= \sum_(i in U | Q i) f i.
Proof.
move=> Hf P_Q; elim: (index_enum _) => [|h t IH].
- by rewrite !big_nil lexx.
- rewrite !big_cons; case: (h \in U) => //=; case: ifP => // Ph.
  + by case: ifP => [Qh|]; [rewrite lerD2l | rewrite (P_Q _ Ph)].
  + by case: ifP => // Qh; rewrite -[X in X <= _]add0r; exact/lerD.
Qed.

Lemma ltR_sumR_support (X : {set A}) : (0 < #|X|)%N ->
  (forall i, i \in X -> f i < g i) ->
  \sum_(i in X) f i < \sum_(i in X) g i.
Proof.
move Hn : #|X| => n; elim: n X Hn => // n IH X Hn _ H.
move: (ltn0Sn n); rewrite -Hn card_gt0; case/set0Pn => a0 Ha0.
rewrite (@big_setD1 _ _ _ _ a0 _ f) //= (@big_setD1 _ _ _ _ a0 _ g) //=.
case: n => [|n] in IH Hn.
  rewrite (_ : X :\ a0 = set0); first by rewrite !big_set0 2!addr0; exact: H.
  move: Hn.
  by rewrite (cardsD1 a0) Ha0 /= add1n => -[] /eqP; rewrite cards_eq0 => /eqP.
apply: ltrD; first exact/H.
apply: IH => //.
- by move: Hn; rewrite (cardsD1 a0) Ha0 /= add1n => -[].
- by move=> a; rewrite in_setD inE => /andP[_ ?]; exact: H.
Qed.

Lemma ltR_sumR : (O < #|A|)%N -> (forall i, f i < g i) ->
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

(* TODO: rename *)
Lemma leR_sumR_eq {R : realType} (A : finType) (f g : A -> R) (P : pred A) :
   (forall a, P a -> f a <= g a)%R ->
   (\sum_(a | P a) g a = \sum_(a | P a) f a)%R ->
   (forall a, P a -> g a = f a).
Proof.
move=> H1 H2 i Hi; apply/eqP; rewrite -subr_eq0; apply/eqP.
move: i Hi; apply: psumr_eq0P.
  by move=> i Pi; rewrite Num.Theory.subr_ge0 H1.
by rewrite big_split/= sumrN; apply/eqP; rewrite subr_eq0 H2.
Qed.

Definition frac_part {R : archiNumDomainType} (x : R) :=
 (x - (Num.floor x)%:~R)%R.

Section oprob_lemmas2.
Local Open Scope ring_scope.
Variable R : realType.
Implicit Types p q : {oprob R}.

Lemma oprob_mulr_subproof p q :
  (0 < (OProb.p p)%:num * (OProb.p q)%:num < 1)%O.
Proof.
apply/andP; split.
  by rewrite mulr_gt0//; apply/oprob_gt0.
by rewrite mulr_ilt1//; apply/oprob_lt1.
Qed.

Canonical oprobmulr p q :=
  Eval hnf in @OProb.mk R (probmulr (OProb.p p) (OProb.p q)) (oprob_mulr_subproof p q).

Lemma s_of_pq_oprob_subproof p q : (0 < [s_of (OProb.p p), (OProb.p q)]%:num < 1)%O.
Proof.
rewrite s_of_pqE; apply/andP; split.
- rewrite onem_gt0//= mulr_ilt1 ?onem_ge0 ?onem_lt1//.
  by have /andP[] := OProb.O1 p.
  by have /andP[] := OProb.O1 q.
- rewrite onem_lt1// mulr_gt0// onem_gt0//.
  by have /andP[] := OProb.O1 p.
  by have /andP[] := OProb.O1 q.
Qed.

Canonical oprob_of_s_of_pq p q :=
  Eval hnf in OProb.mk (s_of_pq_oprob_subproof p q).

Lemma r_of_pq_oprob_subproof p q : (0 < [r_of (OProb.p p), (OProb.p q)]%:num < 1)%O.
Proof.
rewrite r_of_pqE; apply/andP; split.
  by rewrite divr_gt0// oprob_gt0.
rewrite ltr_pdivrMr ?mul1r ?oprob_gt0//.
rewrite lt_neqAle; apply/andP; split; last exact/ge_s_of.
rewrite s_of_pqE lt_eqF//.
rewrite onemM !onemK -addrA ltrDl.
rewrite -[X in 0 < X - _]mul1r -mulrBl -onemE.
by rewrite mulr_gt0// oprob_gt0.
Qed.

Canonical oprob_of_r_of_pq p q :=
  Eval hnf in OProb.mk (r_of_pq_oprob_subproof p q).

Lemma s_of_gt0_oprob p q : 0 < [s_of (OProb.p p), (OProb.p q)]%:num.
Proof. by rewrite s_of_gt0// oprob_neq0. Qed.

End oprob_lemmas2.

Section i01_prob.
Variable R : realType.

#[deprecated(since="infotheo 0.9.7", note="{prob R} and {i01 R} are identical")]
Definition i01_of_prob (p : {prob R}) : {i01 R} := p.
#[deprecated(since="infotheo 0.9.7", note="{prob R} and {i01 R} are identical")]
Definition prob_of_i01 (p : {i01 R}) : {prob R} := p.
#[deprecated(since="infotheo 0.9.7", note="{prob R} and {i01 R} are identical")]
Lemma i01_of_probK : cancel i01_of_prob prob_of_i01.
Proof. by []. Qed.
#[deprecated(since="infotheo 0.9.7", note="{prob R} and {i01 R} are identical")]
Lemma prob_of_i01K : cancel prob_of_i01 i01_of_prob.
Proof. by []. Qed.

End i01_prob.
