From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.

Require Import Reals Fourier ProofIrrelevance FunctionalExtensionality.
Require Import Rssr Reals_ext ssr_ext ssralg_ext log2 Rbigop.
Require Import proba.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section interval.

Definition convex_interval (D : R -> Prop) := forall x y t,
  D x -> D y -> 0 <= t <= 1 -> D (t * x + (1-t) * y).

Record interval := mkInterval {
  mem_interval :> R -> Prop;
  interval_convex : convex_interval mem_interval }.

End interval.

Section convex.

Definition convex_leq (f : R -> R) (x y t : R) :=
  f (t * x + (1 - t) * y) <= t * f x + (1 - t) * f y.

Definition convex (f : R -> R) := forall x y t : R,
  0 <= t <= 1 -> convex_leq f x y t.

Definition convex_in (D : interval) (f : R -> R) := forall x y t : R,
  D x -> D y -> 0 <= t <= 1 -> convex_leq f x y t.

Definition strictly_convex (f : R -> R) := forall x y t : R,
  x != y -> 0 < t < 1 -> convex_leq f x y t.

End convex.

Section concave.

Definition concave_leq (f : R -> R) (x y t : R) :=
  t * f x + (1 - t) * f y <=  f (t * x + (1 - t) * y).

Definition concave (f : R -> R) := forall x y t : R,
  0 <= t <= 1 -> concave_leq f x y t.

Definition concave_in (D : interval) (f : R -> R) := forall x y t : R,
  D x -> D y -> 0 <= t <= 1 -> concave_leq f x y t.

Definition strictly_concave (f : R -> R) := forall x y t : R,
  x != y -> 0 < t < 1 -> concave_leq f x y t.

End concave.

Lemma dist_ind (A : finType) (P : dist A -> Prop) :
  (forall n : nat, (forall a, #|dist_supp a| = n -> P a) ->
    forall a b, #|dist_supp a| = n.+1 -> a b != 0 -> P a) ->
  forall d, P d.
Proof.
move=> H1 d.
move: {-2}(#|dist_supp d|) (erefl (#|dist_supp d|)) => n; move: n d.
elim=> [d /esym /card0_eq Hd0|].
  move: (pmf1 d).
  rewrite -[X in X = _]mul1R big_distrr rsum_dist_supp.
  rewrite big1 => [H01|a].
    by elim: (gtR_eqF _ _ Rlt_0_1).
  by rewrite Hd0.
move=> n IH d n13.
have [b Hb] : exists b : A, d b != 0.
  suff : {x | x \in dist_supp d} by case => a; rewrite inE => ?; exists a.
  apply/sigW/set0Pn; by rewrite -cards_eq0 -n13.
by refine (H1 n _ _ _ _ Hb) => // d' A2; apply IH.
Qed.

Section jensen_inequality.

Variable f : R -> R.
Variable D : interval.
Hypothesis convex_f : convex_in D f.
Variables A : finType.

Lemma dist_supp_singleP (X : dist A) a :
  reflect (X a = 1) (dist_supp X == [set a]).
Proof.
apply: (iffP idP).
  move/eqP => Ha.
  rewrite -(pmf1 X).
  rewrite (eq_bigr (fun i => 1 * X i)); last by move=> *; rewrite mul1R.
  by rewrite rsum_dist_supp Ha big_set1 mul1R.
move=> Xa1.
have H : forall b : A, b != a -> X b = 0.
  apply/(@prsumr_eq0P _ [pred x | x != a] X).
    move=> ? _; exact/dist_nonneg.
  move/eqP : (pmf1 X).
  by rewrite (bigD1 a) //= Xa1 eq_sym addRC -subR_eq subRR => /eqP <-.
apply/eqP/setP => b.
rewrite !inE.
case/boolP: (b == a) => Hb.
  rewrite (eqP Hb) Xa1; apply/eqP => Hb'.
  apply (Rlt_irrefl 1).
  by rewrite {1}Hb'.
by rewrite H // eqxx.
Qed.

Hint Resolve Rle_refl.

Lemma jensen_dist (r : A -> R) (X : dist A) :
  (forall a, D (r a)) ->
  f (\rsum_(a in A) r a * X a) <= \rsum_(a in A) f (r a) * X a.
Proof.
move=> HDr.
apply (@proj1 _ (D (\rsum_(a in dist_supp X) r a * X a))).
rewrite [in X in _ <= X]rsum_dist_supp [in X in X <= _]rsum_dist_supp /=.
apply: (@dist_ind A (fun X =>
   f (\rsum_(a in dist_supp X) r a * X a) <=
   \rsum_(a in dist_supp X) f (r a) * X a /\ _)) => //.
move=> n IH {X}X b cardA Hb.
case/boolP : (X b == 1) => Xb1.
  move/dist_supp_singleP: (eqP Xb1) => /eqP ->.
  by rewrite !big_set1 (eqP Xb1) !mulR1.
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
have /IH {IH}[IH HDd] : #|dist_supp d| = n.
  by rewrite D1Dist.card_dist_supp // cardA.
have HXb: 0 <= X b <= 1 by split; [exact/dist_nonneg|exact/dist_max].
split; last by rewrite mulRC; apply interval_convex.
rewrite mulRC.
refine (Rle_trans _ _ _
  (@convex_f (r b) (\rsum_(i in dist_supp d) r i * d i) _ _ HDd HXb) _) => //.
rewrite mulRC.
apply /Rplus_le_compat_l /Rmult_le_compat_l => //.
apply (Rplus_le_reg_l (X b)).
rewrite addR0 Rplus_minus.
by apply HXb.
Qed.

Local Open Scope proba_scope.

Lemma Jensen (X : rvar A) : (forall x, D (X x)) ->
  f (`E X) <= `E (mkRvar (`p_ X) (fun x => f (X x))).
Proof. move=> HDX; rewrite !ExE /=; by apply jensen_dist. Qed.

End jensen_inequality.

Section jensen_concave.

Variable f : R -> R.
Variable D : interval.
Hypothesis concave_f : concave_in D f.
Variable A : finType.

Let g x := - f x.

Lemma convex_g : convex_in D g.
Proof.
move=> x y t Hx Hy Ht.
rewrite /convex_leq /g.
rewrite !mulRN -oppRD.
apply Ropp_le_contravar.
by apply concave_f.
Qed.

Lemma jensen_dist_concave (r : A -> R) (X : dist A) :
  (forall x, D (r x)) ->
  \rsum_(a in A) f (r a) * X a <= f (\rsum_(a in A) r a * X a).
Proof.
move=> HDr.
apply Ropp_le_cancel.
move: (jensen_dist convex_g X HDr).
rewrite /g.
rewrite [in X in _ <= X](eq_bigr (fun a => -1 * (f (r a) * X a))).
  rewrite -[in X in _ <= X]big_distrr /=.
  by rewrite mulNR mul1R.
move=> i _.
by rewrite !mulNR mul1R.
Qed.

End jensen_concave.
