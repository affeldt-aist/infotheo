From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.

Require Import Reals Fourier ProofIrrelevance FunctionalExtensionality.
Require Import Rssr Reals_ext ssr_ext ssralg_ext log2 Rbigop.
Require Import proba.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section convex.

Definition convex_leq (f : R -> R) (x y t : R) :=
  f (t * x + (1 - t) * y) <= t * f x + (1 - t) * f y.

Definition convex (f : R -> R) := forall x y t : R,
  0 <= t <= 1 -> convex_leq f x y t.

Definition convex_in (D : R -> Prop) (f : R -> R) := forall x y t : R,
  D x -> D y -> 0 <= t <= 1 -> convex_leq f x y t /\ D (t * x + (1 - t) * y).

Definition strictly_convex (f : R -> R) := forall x y t : R,
  x != y -> 0 < t < 1 -> convex_leq f x y t.

End convex.

Section concave.

Definition concave_leq (f : R -> R) (x y t : R) :=
  t * f x + (1 - t) * f y <=  f (t * x + (1 - t) * y).

Definition concave (f : R -> R) := forall x y t : R,
  0 <= t <= 1 -> concave_leq f x y t.

Definition concave_in (D : R -> Prop) (f : R -> R) := forall x y t : R,
  D x -> D y -> 0 <= t <= 1 -> concave_leq f x y t /\ D (t * x + (1 - t) * y).

Definition strictly_concave (f : R -> R) := forall x y t : R,
  x != y -> 0 < t < 1 -> concave_leq f x y t.

End concave.

Lemma dist_ind (A : finType) (P : dist A -> Prop) :
  (forall a, #|dist_supp a| = 1%nat -> P a) ->
  (forall n : nat, (forall a, #|dist_supp a| = n -> P a) ->
    forall a, #|dist_supp a| = n.+1 -> P a) ->
  forall d, (0 < #|dist_supp d|)%nat -> P d.
Proof.
move=> H0 H1 d.
move: {-2}(#|dist_supp d|) (erefl (#|dist_supp d|)) => n; move: n d.
elim=> // -[_ d A2 _ | n IH d A3 n13]; first by apply H0.
apply (H1 n.+1) => // d' A2; by apply IH.
Qed.

Section jensen_inequality.

Variable f : R -> R.
Variable D : R -> Prop.
Hypothesis convex_f : convex_in D f.
Variable A : finType.

Lemma dist_supp_single X (a:A) : dist_supp X = [set a] -> X a = 1. 
Proof.
move=> Ha.
rewrite -(pmf1 X).
rewrite (eq_bigr (fun i => 1 * X i)); last by move=> *; rewrite mul1R.
by rewrite rsum_dist_supp Ha big_set1 mul1R.
Qed.

Definition dist_covered (r : A -> R) (X : dist A) :=
  forall a, a \in dist_supp X -> D (r a).

Lemma jensen_dist (r : A -> R) (X : dist A) :
  (0 < #|dist_supp X|)%nat -> dist_covered r X ->
  f (\rsum_(a in A) r a * X a) <= \rsum_(a in A) f (r a) * X a.
Proof.
move=> A1 HDX.
apply (@proj1 _ (D (\rsum_(a in dist_supp X) r a * X a))).
rewrite [in X in _ <= X]rsum_dist_supp [in X in X <= _]rsum_dist_supp /=.
apply: (@dist_ind A (fun X => dist_covered r X ->
   f (\rsum_(a in dist_supp X) r a * X a) <=
   \rsum_(a in dist_supp X) f (r a) * X a /\ _)) HDX => //.
  move=> {X A1}X /eqP/cards1P [b Hb] HDX.
  rewrite Hb !big_set1 dist_supp_single // !mulR1.
  split. by apply Rle_refl.
  by apply HDX; rewrite Hb inE eqxx.
move=> n IH {X A1} X cardA HDX.
have [b Hb] : exists b : A, X b != 0.
  suff : {x | x \in dist_supp X} by case => a; rewrite inE => ?; exists a.
  apply/sigW/set0Pn; by rewrite -cards_eq0 cardA.
case/boolP : (X b == 1) => [/eqP |] Xb1.
  (* NB: lemma? *)
  have H : forall a : A, a != b -> X a = 0.
    apply/(@prsumr_eq0P _ [pred x | x != b] X).
      move=> ? _; exact/dist_nonneg.
      move/eqP : (pmf1 X).
      by rewrite (bigD1 b) //= Xb1 eq_sym addRC -subR_eq subRR => /eqP <-.
  rewrite (bigD1 b) //=; last by rewrite inE Xb1; exact/eqP/R1_neq_R0.
  rewrite Xb1 big1; last by move=> a /andP[? ?]; rewrite H // ?mulR0.
  rewrite (bigD1 b) //=; last by rewrite inE Xb1; exact/eqP/R1_neq_R0.
  rewrite Xb1 big1; last by move=> a /andP[? ?]; rewrite H // ?mulR0.
  rewrite !addR0 !mulR1.
  by split; [apply Rle_refl | apply HDX; rewrite inE].
have HXb1: 1 - X b != 0.
  by apply: contra Xb1; rewrite subR_eq0 eq_sym.
set d := D1Dist.d Xb1.
have HsumD1 q:
  \rsum_(a in dist_supp d) q a * d a =
  /(1 - X b) * \rsum_(a in dist_supp d) q a * X a.
  rewrite (eq_bigr (fun a => /(1-X b) * (q a * X a))); last first.
    move=> i.
    rewrite inE /= /d /D1Dist.f /=.
    case: ifP => Hi; first by rewrite eqxx.
    by rewrite /Rdiv (mulRC (/ _)) mulRA.
  by rewrite -big_distrr.
have {HsumD1}HsumXD1 q:
  \rsum_(a in dist_supp X) q a * X a =
  q b * X b + (1 - X b) * (\rsum_(a in dist_supp d) q a * d a).
  rewrite HsumD1 /d /D1Dist.f /= mulRA mulRV // mul1R (bigD1 b) ?inE //=.
  rewrite (eq_bigl (fun a : A => a \in dist_supp d)) //= => i.
  rewrite !inE /=.
  case HXi: (X i == 0) => //=.
    by rewrite (D1Dist.f_0 _ (eqP HXi)) eqxx.
  by rewrite D1Dist.f_eq0 // ?HXi // eq_sym.
rewrite 2!{}HsumXD1.
have /IH H : #|dist_supp d| = n.
  by rewrite D1Dist.card_dist_supp // cardA.
have /H {IH H}[IH HDX1] : dist_covered r d.
  move=> a Ha.
  apply HDX; move: Ha.
  rewrite /dist_supp !inE /d /D1Dist.d /D1Dist.f /=.
  case: ifP => Ha; first by rewrite eqxx.
  move/eqP => HX; apply/eqP => HXa.
  by apply HX; rewrite HXa /Rdiv mul0R.
have HXb: 0 <= X b <= 1 by split; [exact/dist_nonneg|exact/dist_max].
split; last first.
  have HDb: D (r b) by apply HDX; rewrite inE.
  by rewrite mulRC; apply convex_f.
rewrite mulRC.
refine (Rle_trans _ _ _
 (proj1 (@convex_f (r b) (\rsum_(i in dist_supp d) r i * d i) _ _ HDX1 HXb)) _).
  by apply HDX; rewrite inE.
rewrite mulRC.
apply /Rplus_le_compat_l /Rmult_le_compat_l => //.
apply (Rplus_le_reg_l (X b)).
rewrite addR0 Rplus_minus.
by apply HXb.
Qed.

Local Open Scope proba_scope.

Lemma Jensen (X : rvar A) : (0 < #|dist_supp (`p_ X)|)%nat ->
  dist_covered (fun x => X x) (rv_dist X) ->
  f (`E X) <= `E (mkRvar (`p_ X) (fun x => f (X x))).
Proof. move=> A1 HDX; rewrite !ExE /=; by apply jensen_dist. Qed.

End jensen_inequality.

Section jensen_concave.

Variable f : R -> R.
Variable D : R -> Prop.
Hypothesis concave_f : concave_in D f.
Variable A : finType.

Let g x := - f x.

Lemma convex_g : convex_in D g.
Proof.
move=> x y t Hx Hy Ht.
rewrite /convex_leq /g.
rewrite !mulRN -oppRD.
split.
  apply Ropp_le_contravar.
  by apply concave_f.
by apply concave_f.
Qed.

Lemma jensen_dist_concave (r : A -> R) (X : dist A) :
  (0 < #|dist_supp X|)%nat -> dist_covered D r X ->
  \rsum_(a in A) f (r a) * X a <= f (\rsum_(a in A) r a * X a).
Proof.
move=> HX HDX.
apply Ropp_le_cancel.
move: (jensen_dist convex_g HX HDX).
rewrite /g.
rewrite [in X in _ <= X](eq_bigr (fun a => -1 * (f (r a) * X a))).
  rewrite -[in X in _ <= X]big_distrr /=.
  by rewrite mulNR mul1R.
move=> i _.
by rewrite !mulNR mul1R.
Qed.

End jensen_concave.
