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

Definition strictly_convex (f : R -> R) := forall x y t : R,
  x != y -> 0 < t < 1 -> convex_leq f x y t.

End convex.

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
Hypothesis convex_f : convex f.
Variable A : finType.

Lemma dist_supp_single X (a:A) : dist_supp X = [set a] -> X a = 1. 
Proof.
move=> Ha.
rewrite -(pmf1 X) (bigID (mem (dist_supp X))) /= Ha big_set1.
rewrite (eq_bigr(fun=>0)); first by rewrite big1 // addR0.
move=> i.
move: Ha.
rewrite /dist_supp => /setP /(_ i).
rewrite !inE.
by case: (i == a) => // /eqP.
Qed.

Lemma jensen_dist (r : A -> R) (X : dist A) : (0 < #|dist_supp X|)%nat ->
  f (\rsum_(a in A) r a * X a) <= \rsum_(a in A) f (r a) * X a.
Proof.
move=> A1.
rewrite [in X in _ <= X]rsum_dist_supp [in X in X <= _]rsum_dist_supp /=.
apply: (@dist_ind A (fun X => f (\rsum_(a in dist_supp X) r a * X a) <=
                              \rsum_(a in dist_supp X) f (r a) * X a)) => //.
  move=> {X A1}X A2.
  move/eqP/cards1P: A2 => [b Hb].
  rewrite Hb !big_set1 dist_supp_single // !mulR1.
  by apply Rle_refl.
move=> n IH {X A1} X cardA.
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
  by rewrite big_const iter_Rplus mulR0 addR0 Xb1 !mulR1; apply Rle_refl.
rewrite [in X in _ <= X](bigD1 b) //=; last by rewrite !inE.
set d := D1Dist.f X b.
rewrite (_ :  \rsum_(i in dist_supp X | i != b) f (r i) * X i =
  (1 - X b) * \rsum_(i in dist_supp X | i != b) f (r i) * d i); last first.
  rewrite big_distrr /=; apply eq_bigr => a /andP[Ha ab].
  rewrite mulRCA; congr (_ * _).
  rewrite /d /D1Dist.f (negbTE ab) mulRCA mulRV ?mulR1 //.
  by apply/eqP; apply: contra Xb1; rewrite subR_eq0 eq_sym.
apply (@Rle_trans _ (f (r b) * X b +
                     (1 - X b) * f (\rsum_(i in A | i != b) (r i) * d i))); last first.
  apply/Rplus_le_compat_l/Rmult_le_compat_l.
    move: (dist_max X b) => ?; fourier.
  have /IH H : #|dist_supp (D1Dist.d Xb1)| = n.
    by rewrite D1Dist.card_dist_supp // cardA.
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
  have : 0 <= X b <= 1 by split; [exact/dist_nonneg|exact/dist_max].
  move/(convex_f (r b) (\rsum_(i in A | i != b) r i * d i)).
  rewrite /convex_leq (mulRC _ (f (r b))) => /Rle_trans; apply.
  rewrite mulRC; exact/Rle_refl.
rewrite [in X in X <= _](bigD1 b) //=; last by rewrite !inE.
rewrite mulRC big_distrr /= [in X in _ <= X](eq_bigr (fun i => r i * X i)).
  apply Req_le; congr (f (_ + _)).
  rewrite [in RHS]rsum_dist_supp; by apply eq_bigl => i; rewrite andbC.
move=> a ab.
rewrite mulRCA; congr (_ * _).
rewrite /d /D1Dist.f (negbTE ab) mulRCA mulRV ?mulR1 //.
apply/eqP; apply: contra Xb1; by rewrite subR_eq0 eq_sym.
Qed.

Local Open Scope proba_scope.

Lemma Jensen (X : rvar A) : (0 < #|dist_supp (`p_ X)|)%nat ->
  f (`E X) <= `E (mkRvar (`p_ X) (fun x => f (X x))).
Proof. move=> A1; rewrite !ExE /=; by apply jensen_dist. Qed.

End jensen_inequality.
