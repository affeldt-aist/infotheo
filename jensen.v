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
  f (\rsum_(a in A) r a * X a) <= \rsum_(a in A) f (r a) * X a /\
  D (\rsum_(a in A) r a * X a).
Proof.
move=> A1.
rewrite [in X in _ <= X]rsum_dist_supp [in X in X <= _]rsum_dist_supp /=
        [in X in _ /\ X]rsum_dist_supp.
apply: (@dist_ind A (fun X => dist_covered r X ->
   f (\rsum_(a in dist_supp X) r a * X a) <=
   \rsum_(a in dist_supp X) f (r a) * X a /\ _)) => //.
  move=> {X A1}X /eqP/cards1P [b Hb] HDX.
  rewrite Hb !big_set1 dist_supp_single // !mulR1.
  split.
    by apply Rle_refl.
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
  rewrite (eq_bigr (fun=> 0)); last by move=> a /andP[? ?]; rewrite H // ?mulR0.
  rewrite big_const iter_Rplus mulR0 addR0 (bigD1 b) //=; last first.
    rewrite inE Xb1; apply/eqP; exact: R1_neq_R0.
  rewrite (eq_bigr (fun=> 0)); last by move=> a /andP[? ?]; rewrite H // ?mulR0.
  split.
    by rewrite big_const iter_Rplus mulR0 addR0 Xb1 !mulR1; apply Rle_refl.
  rewrite Xb1 mulR1; apply HDX.
  by rewrite /dist_supp inE.
rewrite [in X in _ <= X](bigD1 b) //=; last by rewrite !inE.
set d := D1Dist.f X b.
have -> : \rsum_(i in dist_supp X | i != b) f (r i) * X i =
  (1 - X b) * \rsum_(i in dist_supp X | i != b) f (r i) * d i.
  rewrite big_distrr /=; apply eq_bigr => a /andP[Ha ab].
  rewrite mulRCA; congr (_ * _).
  rewrite /d /D1Dist.f (negbTE ab) mulRCA mulRV ?mulR1 //.
  by apply/eqP; apply: contra Xb1; rewrite subR_eq0 eq_sym.
have /IH H : #|dist_supp (D1Dist.d Xb1)| = n.
  by rewrite D1Dist.card_dist_supp // cardA.
have /H {H}[H HDX1] : dist_covered r (D1Dist.d Xb1).
  move=> a Ha.
  apply HDX.
  move: Ha; rewrite /dist_supp !inE.
  rewrite /D1Dist.d /D1Dist.f /=.
  case: ifP => Ha.
    by rewrite eqxx.
  move/eqP => HX.
  apply/eqP => HXa.
  by apply HX; rewrite HXa /Rdiv mul0R.
have HXb: 0 <= X b <= 1 by split; [exact/dist_nonneg|exact/dist_max].
split; last first.
  have HDb: D (r b).
    by apply HDX; rewrite inE.
  move/proj2: (convex_f HDb HDX1 HXb).
  rewrite /= /D1Dist.f /=.
  rewrite (eq_bigr (fun a => /(1-X b) * (r a * X a))); last first.
    move=> i.
    rewrite inE /= /D1Dist.f /=.
    case: ifP => Hi.
      by rewrite eqxx.
    by rewrite /Rdiv  (mulRC (/ _)) mulRA.
  rewrite -big_distrr /= mulRA mulRV.
    rewrite mul1R mulRC => HDXb.
    rewrite (bigD1 b) /=; last by rewrite inE.
    rewrite (eq_bigl (fun a : A => a \in dist_supp (D1Dist.d Xb1))) //= => i.
    rewrite !inE /=.
    case HXi: (X i == 0) => //=.
      by rewrite (D1Dist.f_0 _ (eqP HXi)) eqxx.
    by rewrite D1Dist.f_eq0 // ?HXi // eq_sym.
  move/(Rplus_eq_compat_l (X b)).
  rewrite addR0 Rplus_minus => HXb1.
  move: (Xb1).
  by rewrite HXb1 eqxx.
apply (@Rle_trans _ (f (r b) * X b +
                     (1 - X b) * f (\rsum_(i in A | i != b) (r i) * d i))); last first.
  apply/Rplus_le_compat_l/Rmult_le_compat_l.
    move: (dist_max X b) => ?; fourier.
  set x := (X in _ <= X) in H. set x' := (X in _ <= X).
  have <- : x = x'.
    rewrite /x /x' /D1Dist.d /d /=.
    rewrite big_seq_cond big_mkcond [in RHS]big_seq_cond [in RHS]big_mkcond /=.
    apply eq_bigr => a _.
    rewrite !inE /= mem_index_enum /=.
    case/boolP : (X a == 0) => [/eqP/D1Dist.f_0|/(D1Dist.f_eq0 Xb1)] -> /=;
      by [rewrite eqxx | rewrite eq_sym].
  apply/(Rle_trans _ _ _ _ H)/Req_le; congr f.
  rewrite big_seq_cond big_mkcond /= [in RHS]big_mkcond; apply eq_bigr => a _.
  rewrite mem_index_enum inE /d /=.
  case/boolP : (X a == 0) => [/eqP/D1Dist.f_0|/(D1Dist.f_eq0 Xb1)] -> /=;
    by [rewrite eqxx /= /d mulR0; case: ifP | rewrite eq_sym].
apply (@Rle_trans _ (f (X b * r b +
                    (1 - X b) * (\rsum_(i in A | i != b) (r i) * d i)))); last first.
  refine (Rle_trans _ _ _ 
    (proj1 (@convex_f (r b) (\rsum_(i in A | i != b) r i * d i) _ _ _ HXb)) _).
      by apply HDX; rewrite inE.
    rewrite (bigID (fun a => d a == 0)) /=.
    rewrite big1; last first.
      by move=> i /andP [_ /eqP ->]; rewrite mulR0.
    rewrite add0R.
    rewrite (eq_bigl (fun a : A => a \in dist_supp (D1Dist.d Xb1))) //= => i.
    case Hi: (i == b).
      by rewrite (eqP Hi) inE D1Dist.f_eq0 // eqxx.
    by rewrite inE.
  rewrite mulRC; exact/Rle_refl.
rewrite [in X in X <= _](bigD1 b) //=; last by rewrite !inE.
rewrite mulRC big_distrr /= [in X in _ <= X](eq_bigr (fun i => r i * X i)).
  apply Req_le; congr (f (_ + _)).
  rewrite [in RHS]rsum_dist_supp; by apply eq_bigl => i; rewrite andbC.
move=> a ab.
rewrite mulRCA; congr (_ * _).
rewrite /d /D1Dist.f (negbTE ab) mulRCA mulRV ?mulR1 //.
apply/eqP; apply: contra (Xb1); by rewrite subR_eq0 eq_sym.
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
move: (proj1 (jensen_dist convex_g HX HDX)).
rewrite /g.
rewrite [in X in _ <= X](eq_bigr (fun a => -1 * (f (r a) * X a))).
  rewrite -[in X in _ <= X]big_distrr /=.
  by rewrite mulNR mul1R.
move=> i _.
by rewrite !mulNR mul1R.
Qed.

End jensen_concave.
