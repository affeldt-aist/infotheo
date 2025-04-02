(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg archimedean ssrnum ssrint.
From mathcomp Require Import reals normedtype sequences exp.
From mathcomp Require Import mathcomp_extra boolp interval_inference.
From mathcomp Require Import lra ring Rstruct.

(**md**************************************************************************)
(* # Additional definitions and lemmas about numeric types                    *)
(*                                                                            *)
(* TODO: doc incomplete                                                       *)
(*                                                                            *)
(* ```                                                                        *)
(*     +| r | := maxr 0 r                                                     *)
(*    P `<< Q == P is dominated by Q, i.e., forall a, Q a = 0 -> P a = 0      *)
(*    P `<<b Q == boolean version of P `<< Q                                  *)
(* frac_part x := x - (Num.floor x)%:~R                                       *)
(*       prob == type of "probabilities", i.e., reals p s.t. 0 <= p <= 1      *)
(*      oprob == type of "open unit interval", i.e., reals p s.t. 0 < p < 1   *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Declare Scope reals_ext_scope.

Reserved Notation "+| r |" (at level 0, r at level 99, format "+| r |").
Reserved Notation "p '.~'" (format "p .~", at level 5).
Reserved Notation "P '`<<' Q" (at level 51).
Reserved Notation "P '`<<b' Q" (at level 51).
Reserved Notation "{ 'prob' T }" (at level 0, format "{ 'prob'  T }").
Reserved Notation "x %:pr" (at level 0, format "x %:pr").
Reserved Notation "x %:opr" (at level 0, format "x %:opr").
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
apply (asbool_equiv_eqP (Q:=True)) => //.
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
by move=> /andP[r0 r1]; apply /andP; split; [rewrite onem_ge0|rewrite onem_le1].
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
have : forall a b : R, 0 <= b -> a - b <= a. move=>  *; lra.
apply; apply mulr_ge0; [lra | exact: exprn_even_ge0].
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
Record t (R : realType) := mk {
  p :> R ;
  Op1 : (0 <= p <= 1)%R }.
Definition O1 (R : realType) (x : t R) : (0 <= p x <= 1)%R := Op1 x.
Arguments O1 : simpl never.
Definition mk_ (R : realType) (q : R) (Oq1 : (0 <= q <= 1)%R) := mk Oq1.
Module Exports.
Notation prob := t.
Notation "q %:pr" := (@mk _ q (@O1 _ _)).
HB.instance Definition _ (R : realType) := [isSub for @p R].
HB.instance Definition _ (R : realType) := [Choice of t R by <:].
End Exports.
End Prob.
Export Prob.Exports.
Coercion Prob.p : prob >-> Real.sort.
Lemma probpK R p H : Prob.p (@Prob.mk R p H) = p. Proof. by []. Qed.

Notation "{ 'prob' T }" := (@prob T).

HB.instance Definition _ (R : realType) := [Order of {prob R} by <:].

Definition to_numdomain (R : realType) (p : {prob R}) : Num.NumDomain.sort _ :=
  (p : R).
Coercion to_numdomain : prob >-> Num.NumDomain.sort.
Arguments to_numdomain /.

Definition to_zmodule (R : realType) (p : {prob R}) : GRing.Zmodule.sort _ :=
  (p : R).
Coercion to_zmodule : prob >-> GRing.Zmodule.sort.
Arguments to_zmodule /.

Definition to_ring (R : realType) (p : {prob R}) : GRing.Ring.sort _ :=
  (p : R).
Coercion to_ring : prob >-> GRing.Ring.sort.
Arguments to_ring /.

Section prob_lemmas.
Local Open Scope ring_scope.
Variable R : realType.
Implicit Types p q : {prob R}.

Lemma OO1 : ((0 <= 0 :> R) && (0 <= 1 :> R))%R.
Proof. by apply /andP; split; [rewrite lexx | rewrite ler01]. Qed.

Lemma O11 : ((0 <= 1 :> R) && (1 <= 1 :> R))%R.
Proof. by apply /andP; split; [rewrite ler01| rewrite lexx]. Qed.

Canonical prob0 := Eval hnf in Prob.mk OO1.
Canonical prob1 := Eval hnf in Prob.mk O11.
Canonical probcplt (p : prob R) := Eval hnf in Prob.mk (onem_prob (Prob.O1 p)).

Lemma prob_ge0 (p : prob R) : (0 <= (p : R))%R.
Proof. by case: p => p /= /andP []. Qed.

Lemma prob_le1 (p : prob R) : ((p : R) <= 1)%R.
Proof. by case: p => p /= /andP []. Qed.

Lemma prob_gt0 p : p != 0%:pr <-> 0 < Prob.p p.
Proof.
rewrite lt_neqAle; split=> [H|/andP[+ pge0]].
  by apply/andP; split; [rewrite eq_sym|exact: prob_ge0].
by apply: contra => /eqP ->.
Qed.

(*Lemma prob_gt0' p : p != 0 :> R <-> 0 < Prob.p p.
Proof. exact: prob_gt0. Qed.*)

Lemma prob_lt1 p : p != 1%:pr <-> Prob.p p < 1.
Proof.
rewrite lt_neqAle; split=> [H|/andP[+ pge0]].
  by apply/andP; split => //; exact: prob_le1.
by apply: contra => /eqP ->.
Qed.

(*Lemma prob_lt1' p : p != 1 :> R <-> Prob.p p < 1.
Proof. exact: prob_lt1. Qed.*)

Lemma prob_trichotomy p : p = 0%:pr \/ p = 1%:pr \/ 0 < Prob.p p < 1.
Proof.
have [->|pneq0]:= eqVneq p 0%:pr; first by left.
right.
have [->|pneq1] := eqVneq p 1%:pr; first by left.
by right; apply/andP; split; [exact/prob_gt0|exact/prob_lt1].
Qed.

(* TODO: rename to prob_onemK and prob_onemKC? *)
Lemma probK p : p = ((Prob.p p).~).~%:pr.
Proof. by apply val_inj => /=; rewrite onemK. Qed.

Lemma probKC (p : {prob R}) : Prob.p p + (Prob.p p).~ = 1 :> R.
Proof. exact: add_onemK. Qed.

Lemma probadd_eq0 p q : Prob.p p + Prob.p q = 0 <-> p = 0%:pr /\ q = 0%:pr.
Proof.
split; last by move=> [-> ->] /=; rewrite addr0.
move/eqP; rewrite paddr_eq0; [|exact: prob_ge0|exact: prob_ge0].
by move=> /andP[/eqP ? /eqP ?]; split; exact/val_inj.
Qed.

Lemma probadd_neq0 p q : Prob.p p + Prob.p q != 0 <-> p != 0%:pr \/ q != 0%:pr.
Proof.
apply/iff_not2; split=> [/negP/negPn/eqP/probadd_eq0[-> ->]|].
  by apply/not_orP; split; apply/negP/negPn.
move=> /not_orP[/negP/negPn/eqP -> /negP/negPn/eqP -> /=]; apply/negP/negPn.
by rewrite addr0.
Qed.

Lemma probmul_eq1 p q : Prob.p p * Prob.p q = 1 <-> p = 1%:pr /\ q = 1%:pr.
Proof.
split => [/= pq1|[-> ->]]; last by rewrite mulr1.
move: (oner_neq0 R); rewrite -{1}pq1 mulf_eq0 negb_or => /andP[p0 q0].
have := prob_le1 p; rewrite le_eqVlt => /orP[/eqP p1|p1].
  by rewrite p1 mul1r in pq1; split; exact/val_inj.
have := prob_le1 q; rewrite le_eqVlt => /orP[/eqP q1|q1].
  by rewrite q1 mulr1 in pq1; split; exact/val_inj.
have {}p0 : 0 < Prob.p p by rewrite lt_neqAle prob_ge0 eq_sym andbT.
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
  Op1 : (0 < Prob.p p < 1)%R }.
Definition O1 (R: realType) (x : t R) : 0 < Prob.p (p x) < 1 := Op1 x.
Arguments O1 : simpl never.
End def.
Module Exports.
Notation oprob := t.
Notation "q %:opr" := (@mk _ q%:pr (@O1 _ _)).
HB.instance Definition _ (R : realType) := [isSub for @p R].
HB.instance Definition _ (R : realType) := [Equality of t R by <:].
End Exports.
End OProb.
Export OProb.Exports.
Coercion OProb.p : oprob >-> prob.
Canonical oprobcplt [R: realType] (p : oprob R) :=
  Eval hnf in OProb.mk (onem_oprob (OProb.O1 p)).

Reserved Notation "{ 'oprob' T }" (at level 0, format "{ 'oprob'  T }").
Notation "{ 'oprob' T }" := (@oprob T).
Notation oprob_to_real o := (Prob.p (OProb.p o)).

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

Lemma oprob_onemK (p : {oprob R}) : p = ((oprob_to_real p).~).~%:opr.
Proof. by apply/val_inj/val_inj=> /=; rewrite onemK. Qed.

(* TODO: rename? *)
Lemma prob_trichotomy' (p : {prob R}) (P : {prob R} -> Prop) :
  P prob0 -> P prob1 -> (forall o : {oprob R}, P (OProb.p o)) -> P p.
Proof.
move=> p0 p1 po.
have [-> //|[->//|p01]] := prob_trichotomy p.
apply (po (@OProb.mk _ _ p01)).
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

Lemma prob_invprob_subproof (p : {prob R}) : (0 <= 1 / (1 + Prob.p p) <= 1)%O.
Proof.
apply/andP; split.
  by rewrite mul1r invr_ge0 ?addr_ge0.
rewrite mul1r invf_le1//.
  by rewrite lerDl.
rewrite (@lt_le_trans _ _ 1)//.
by rewrite lerDl.
Qed.

(* canonicalizing this definition breaks s_of_pq *)
Definition prob_invprob (p : {prob R}) := Prob.mk (prob_invprob_subproof p).

Lemma prob_mulr_subproof (p q : {prob R}) : (0 <= Prob.p p * Prob.p q <= 1)%R.
Proof.
apply/andP; split.
  by rewrite mulr_ge0.
by rewrite mulr_ile1.
Qed.

Canonical probmulr (p q : {prob R}) :=
  Eval hnf in @Prob.mk _ (Prob.p p * Prob.p q) (prob_mulr_subproof p q).

End prob_lemmas2.

Definition s_of_pq {R : realType} (p q : {prob R}) : {prob R} :=
  locked ((Prob.p p).~ * (Prob.p q).~).~%:pr.

Declare Scope reals_ext_scope.
Notation "[ 's_of' p , q ]" := (s_of_pq p q) : reals_ext_scope.

Local Open Scope reals_ext_scope.

Section s_of_pq_lemmas.
Variable R : realType.
Implicit Types p q : {prob R}.

Lemma s_of_pqE p q : Prob.p [s_of p, q] = ((Prob.p p).~ * (Prob.p q).~)%R.~ :> R.
Proof. by rewrite /s_of_pq; unlock. Qed.

Lemma s_of_0q q : [s_of 0%:pr, q] = q.
Proof. by apply/val_inj; rewrite /= s_of_pqE onem0 mul1r onemK. Qed.

Lemma s_of_1q q : [s_of 1%:pr, q] = 1%:pr.
Proof. by apply/val_inj; rewrite /= s_of_pqE onem1 mul0r onem0. Qed.

Lemma s_of_p0 p : [s_of p, 0%:pr] = p.
Proof. by apply/val_inj; rewrite /= s_of_pqE onem0 mulr1 onemK. Qed.

Lemma s_of_p1 p : [s_of p, 1%:pr] = 1%:pr.
Proof. by apply/val_inj; rewrite /= s_of_pqE onem1 mulr0 onem0. Qed.

Lemma s_of_gt0 p q : p != 0%:pr -> (0 < Prob.p [s_of p, q])%R.
Proof.
move=> p0; rewrite s_of_pqE; apply: onem_gt0.
have [->/=|q0] := eqVneq q 0%:pr.
  by rewrite onem0 mulr1 onem_lt1// lt0r p0/=.
rewrite mulr_ilte1 => //=.
  by rewrite onem_lt1// lt0r p0/=.
by rewrite onem_lt1// lt0r q0/=.
Qed.

Lemma ge_s_of p q : (Prob.p p <= Prob.p [s_of p, q])%R.
Proof.
rewrite s_of_pqE.
rewrite onemE.
rewrite addrC.
rewrite -lerBlDr.
rewrite -opprB.
rewrite lerNl opprK.
rewrite -/(Prob.p p).~.
by rewrite ler_piMr.
Qed.

End s_of_pq_lemmas.

Lemma r_of_pq_subproof {R : realType} (p q : {prob R}) :
  (0 <= Prob.p p / Prob.p [s_of p, q] <= 1)%R.
Proof.
have [->|p0] := eqVneq p 0%:pr.
  by rewrite mul0r lexx ler01.
have [->|a0] := eqVneq q 0%:pr.
  by rewrite s_of_p0 divff// lexx ler01.
apply/andP; split.
- by rewrite divr_ge0.
rewrite ler_pdivrMr ?mul1r.
  by apply: ge_s_of.
by rewrite s_of_gt0//.
Qed.

Definition r_of_pq {R : realType} (p q : {prob R}) : {prob R} :=
  locked (Prob.mk (r_of_pq_subproof p q)).

Notation "[ 'r_of' p , q ]" := (r_of_pq p q) : reals_ext_scope.

Section r_of_pq_lemmas.
Variable R : realType.
Implicit Types p q : {prob R}.

Lemma r_of_pqE p q : Prob.p [r_of p, q] = (Prob.p p / Prob.p [s_of p, q])%R :> R.
Proof. by rewrite /r_of_pq; unlock. Qed.

Lemma r_of_p0 p : p != 0%:pr -> [r_of p, 0%:pr] = 1%:pr.
Proof. by move=> p0; apply val_inj; rewrite /= r_of_pqE s_of_p0 divff. Qed.

Lemma r_of_0q q : [r_of 0%:pr, q] = 0%:pr.
Proof. by apply/val_inj; rewrite /= r_of_pqE mul0r. Qed.

Lemma r_of_p1 p : [r_of p, 1%:pr] = p.
Proof. by apply/val_inj; rewrite /= r_of_pqE s_of_p1 invr1 mulr1. Qed.

Lemma r_of_1q q : [r_of 1%:pr, q] = 1%:pr.
Proof. by apply/val_inj; rewrite /= r_of_pqE s_of_1q/= invr1 mulr1. Qed.

End r_of_pq_lemmas.

Lemma p_is_rs {R : realType} (p q : {prob R}) :
  Prob.p p = ((Prob.p [r_of p, q]) * Prob.p [s_of p, q])%R :> R.
Proof.
have [->/=|p0] := eqVneq p 0%:pr; first by rewrite r_of_0q mul0r.
have [->/=|q0] := eqVneq q 0%:pr.
  by rewrite s_of_p0 r_of_p0 // mul1r.
rewrite r_of_pqE -mulrA mulVf ?mulr1 //.
suff : Prob.p [s_of p, q] != 0%R :> R by [].
by rewrite prob_gt0 s_of_gt0.
Qed.

Lemma p_of_rs_subproof {R : realType} (r s : {prob R}) :
  (0 <= Prob.p r * Prob.p s <= 1)%R.
Proof.
by apply/andP; split; [rewrite mulr_ge0|rewrite mulr_ile1].
Qed.

Definition p_of_rs {R : realType} (r s : {prob R}) : {prob R} :=
  locked (Prob.mk (p_of_rs_subproof r s)).

Notation "[ 'p_of' r , s ]" := (p_of_rs r s) : reals_ext_scope.

Section p_of_rs_lemmas.
Variable R : realType.
Implicit Types r s : {prob R}.

Lemma p_of_rsE r s : Prob.p [p_of r, s] = (Prob.p r * Prob.p s)%R :> R.
Proof. by rewrite /p_of_rs; unlock. Qed.

Lemma p_of_r1 r : [p_of r, 1%:pr] = r.
Proof. by apply: val_inj; rewrite /= p_of_rsE mulr1. Qed.

Lemma p_of_1s s : [p_of 1%:pr, s] = s.
Proof. by apply: val_inj; rewrite /= p_of_rsE mul1r. Qed.

Lemma p_of_r0 r : [p_of r, 0%:pr] = 0%:pr.
Proof. by apply/val_inj; rewrite /= p_of_rsE mulr0. Qed.

Lemma p_of_0s s : [p_of 0%:pr, s] = 0%:pr.
Proof. by apply/val_inj; rewrite /= p_of_rsE mul0r. Qed.

Lemma p_of_rsC r s : [p_of r, s] = [p_of s, r].
Proof. by apply/val_inj; rewrite /= !p_of_rsE mulrC. Qed.

Lemma p_of_neq1 r s : (0 < Prob.p s < 1)%R -> [p_of r, s] != 1%:pr.
Proof.
case/andP=> p0 p1; apply/eqP => pq1; move: (p1).
rewrite [X in (_ < X)%R -> _](_ : _ = Prob.p 1%:pr) //.
rewrite -pq1 p_of_rsE -ltr_pdivrMr // divff ?gt_eqF//.
by rewrite ltNge prob_le1.
Qed.

Lemma p_of_rs1 r s :
  ([p_of r, s] == 1%:pr :> {prob R}) = ((r == 1%:pr) && (s == 1%:pr)).
Proof.
apply/idP/idP; last by case/andP => /eqP -> /eqP ->; rewrite p_of_r1.
move/eqP/(congr1 (@Prob.p _)).
rewrite /= p_of_rsE => /eqP.
apply contraLR => /nandP.
wlog : r s / r != 1%:pr by move=> H [|] ?; [|rewrite mulrC]; rewrite H //; left.
move=> r1 _.
have [->|] := eqVneq r 0%:pr.
  by rewrite mul0r eq_sym oner_eq0.
move/prob_gt0.
rewrite lt_neqAle => /andP[r0 _].
apply/eqP.
move/(congr1 (fun x => ((Prob.p r)^-1)%R * x))%R.
rewrite mulrA mulVr ?unitfE//; last by rewrite eq_sym.
rewrite mul1r mulr1.
rewrite eq_sym in r0.
move/prob_gt0 in r0.
move=> srV; move: (prob_le1 s); rewrite {}srV.
rewrite invr_le1// ?unitfE ?gt_eqF//.
apply/negP.
rewrite -ltNge.
by rewrite -prob_lt1.
Qed.

Lemma p_of_rs1P r s : reflect (r = 1%:pr /\ s = 1%:pr) ([p_of r, s] == 1%:pr).
Proof.
move: (p_of_rs1 r s) ->.
apply: (iffP idP);
  [by case/andP => /eqP -> /eqP -> | by case => -> ->; rewrite eqxx].
Qed.

End p_of_rs_lemmas.

Lemma q_of_rs_prob {R : realType} (r s : {prob R}) :
  (0 <= ((Prob.p r).~ * (Prob.p s)) / (Prob.p [p_of r, s]).~ <= 1)%R.
Proof.
have [->|r1] := eqVneq r 1%:pr.
  by rewrite onem1 !mul0r lexx ler01.
have [->|s1] := eqVneq s 1%:pr.
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

Lemma r_of_pq_is_r {R : realType} (p q r s : {prob R}) : r != 0%:pr -> s != 0%:pr ->
  (Prob.p p = Prob.p r * Prob.p s :> R ->
   (Prob.p s).~ = (Prob.p p).~ * (Prob.p q).~ -> [r_of p, q] = r)%R.
Proof.
move=> r0 s0 H1 H2; apply val_inj => /=.
by rewrite r_of_pqE s_of_pqE -H2 onemK H1 -mulrA divff ?mulr1//.
Qed.

Definition q_of_rs {R : realType} (r s : {prob R}) : {prob R} :=
  locked (Prob.mk (q_of_rs_prob r s)).

Notation "[ 'q_of' r , s ]" := (q_of_rs r s) : reals_ext_scope.

Section q_of_rs_lemmas.
Variable R : realType.
Implicit Types r s : {prob R}.

Lemma q_of_rsE r s :
  Prob.p [q_of r, s] = (((Prob.p r).~ * Prob.p s) / (Prob.p [p_of r, s]).~)%R :> R.
Proof.
by rewrite /q_of_rs; unlock.
Qed.

Lemma q_of_r0 r : [q_of r, 0%:pr] = 0%:pr.
Proof. by apply/val_inj => /=; rewrite q_of_rsE mulr0 mul0r. Qed.

Lemma q_of_r1 r : r != 1%:pr -> [q_of r, 1%:pr] = 1%:pr.
Proof.
move=> r1.
by apply/val_inj => /=; rewrite q_of_rsE /= mulr1 p_of_r1 divff // onem_neq0.
Qed.

Lemma q_of_1s s : [q_of 1%:pr, s] = 0%:pr.
Proof. by apply/val_inj => /=; rewrite q_of_rsE onem1 !mul0r. Qed.

End q_of_rs_lemmas.

Lemma pq_is_rs {R : realType} (p q : {prob R}) :
  ((Prob.p p).~ * Prob.p q = (Prob.p [r_of p, q]).~ * Prob.p [s_of p, q])%R.
Proof.
have [->|p0] := eqVneq p 0%:pr.
  by rewrite onem0 mul1r r_of_0q onem0 mul1r s_of_0q.
rewrite r_of_pqE [in RHS]mulrBl mul1r -mulrA mulVf ?mulr1; last first.
  by rewrite prob_gt0; exact/s_of_gt0.
rewrite s_of_pqE onemM !onemK /onem mulrBl mul1r [RHS]addrC !addrA.
lra.
Qed.

Lemma s_of_pqK {R : realType} (r s : {prob R}) : [p_of r, s] != 1%:pr ->
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
  [p_of r, s] != 1%:pr -> s != 0%:pr ->
  [r_of [p_of r, s], [q_of r, s]] = r.
Proof.
move=> H1 s0; apply/val_inj => /=.
rewrite !(r_of_pqE,s_of_pqE,q_of_rsE,p_of_rsE) /onem.
field.
apply/andP; split; last first.
  by rewrite mulrBl mul1r !opprB -!addrA addrC !addrA !subrK.
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
apply val_inj; rewrite /= s_of_pqE.
rewrite onemM !onemK/=.
field.
by apply/andP; split => //.
Qed.

Lemma r_of_rpos_probA {R : realType} (p q r : {posnum R}%R) :
  [r_of divrposxxy p (q%:num + r%:num)%:pos%R, divrposxxy q r] =
  divrposxxy p q%R.
Proof.
apply/val_inj; rewrite /= r_of_pqE s_of_pqE /onem /=.
field.
apply/and4P; split => //.
rewrite (addrC p%:num (q%:num + r%:num)%:pos%:num)%R addrK {4}[in (q%:num + r%:num)%R]addrC addrK.
by rewrite mulrC -mulrBr (addrC _ p%:num%R) addrA addrK mulf_neq0//.
Qed.

Lemma r_of_p0_oprob {R : realType} (p : {oprob R}) :
  [r_of OProb.p p, 0%:pr] = 1%:pr.
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
by apply lerD => //; apply: H.
Qed.

Lemma leR_sumRl : (forall i, P i -> f i <= g i) ->
  (forall i, Q i -> 0 <= g i) -> (forall i, P i -> Q i) ->
  \sum_(i | P i) f i <= \sum_(i | Q i) g i.
Proof.
move=> f_g Qg H; elim: (index_enum _) => [| h t IH].
- rewrite !big_nil.
  by rewrite lexx.
- rewrite !big_cons /=; case: ifP => [Ph|Ph].
    by rewrite (H _ Ph); apply lerD => //; exact: f_g.
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
apply ltrD; first exact/H.
apply IH => //.
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
  (0 < Prob.p (OProb.p p) * Prob.p (OProb.p q) < 1)%O.
Proof.
apply/andP; split.
  by rewrite mulr_gt0//; apply/oprob_gt0.
by rewrite mulr_ilt1//; apply/oprob_lt1.
Qed.

Canonical oprobmulr p q :=
  Eval hnf in @OProb.mk R (probmulr p q) (oprob_mulr_subproof p q).

Lemma s_of_pq_oprob_subproof p q : (0 < Prob.p [s_of p, q] < 1)%O.
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

Lemma r_of_pq_oprob_subproof p q : (0 < Prob.p [r_of OProb.p p, OProb.p q] < 1)%O.
Proof.
rewrite r_of_pqE; apply/andP; split.
  by rewrite divr_gt0// oprob_gt0.
rewrite ltr_pdivrMr ?mul1r ?oprob_gt0//.
rewrite lt_neqAle; apply/andP; split; last exact/ge_s_of.
rewrite s_of_pqE lt_eqF//.
rewrite onemM !onemK -addrA ltrDl.
by rewrite -[X in 0 < X - _]mul1r -mulrBl -onemE oprob_gt0.
Qed.

Canonical oprob_of_r_of_pq p q :=
  Eval hnf in OProb.mk (r_of_pq_oprob_subproof p q).

Lemma s_of_gt0_oprob  p q : 0 < Prob.p [s_of p, q].
Proof. by rewrite s_of_gt0// oprob_neq0. Qed.

End oprob_lemmas2.
