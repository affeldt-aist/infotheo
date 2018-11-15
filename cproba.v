From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.
Require Import proba divergence entropy.

(* tentative definition of conditional probability,
   application to the formalization of Cover and Thomas, Chapter 2 *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Module Swap.
Section swap.
Variables (A B : finType) (P : {dist A * B}).

Definition f (x : B * A) := P (x.2, x.1).

Lemma f0 (x : B * A) : 0 <= f x. Proof. exact: pos_f_ge0. Qed.

Lemma f1 : \rsum_(x in {: B * A}) f x = 1.
Proof.
rewrite /f -(pair_big xpredT xpredT (fun x1 x2 => P (x2, x1))) exchange_big.
rewrite (pair_big xpredT xpredT) /= -(pmf1 P); apply eq_bigr; by case.
Qed.

Definition d : {dist (B * A)} := locked (makeDist f0 f1).

Lemma dE a b : d (b, a) = P (a, b). Proof. rewrite /d; unlock; by []. Qed.

Lemma fst : Bivar.fst d = Bivar.snd P.
Proof.
rewrite /Bivar.fst /d /Bivar.snd; unlock => /=; apply/dist_ext => b /=.
rewrite /Bivar.ml /Bivar.mr -(pair_big_fst _ _ (pred1 b)) //=.
by rewrite exchange_big /= pair_big; apply eq_bigr; case => a' b' /= /eqP ->.
Qed.

Lemma snd : Bivar.snd d = Bivar.fst P.
Proof.
rewrite /Bivar.fst /d /Bivar.snd; unlock => /=; apply/dist_ext => a /=.
rewrite /Bivar.mr /Bivar.mr -(pair_big_snd _ _ (pred1 a)) //=.
rewrite exchange_big /= pair_big /= (eq_bigl (fun x => x.1 == a)).
by apply eq_bigr; case => a' b' /= /eqP ->.
by case=> a' b' /=; rewrite inE andbT.
Qed.

End swap.

Lemma dI (A B : finType) (P : {dist A * B}) : d (d P) = P.
Proof. apply/dist_ext => -[a b]; by rewrite 2!dE. Qed.

End Swap.

Module Self.
Section self.
Variable (A : finType) (P : {dist A}).
Definition f (a : A * A) := if a.1 == a.2 then P a.1 else 0.
Lemma f0 x : 0 <= f x.
Proof.
rewrite /f; case: ifPn => [/eqP ->| _]; [exact: dist_ge0|exact: leRR].
Qed.
Lemma f1 : \rsum_(x in {: A * A}) f x = 1.
Proof.
rewrite (eq_bigr (fun a => f (a.1, a.2))); last by case.
rewrite -(pair_big xpredT xpredT (fun a1 a2 => f (a1, a2))) /=.
rewrite -(pmf1 P); apply/eq_bigr => a _.
rewrite /f /= (bigD1 a) //= eqxx.
rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 ?addR0 //.
by move=> a' /negbTE; rewrite eq_sym => ->.
Qed.
Definition d : {dist A * A} := locked (makeDist f0 f1).
Lemma dE a : d a = if a.1 == a.2 then P a.1 else 0.
Proof. by rewrite /d; unlock. Qed.
Lemma fst : Bivar.fst d = P.
Proof.
apply/dist_ext => a /=.
rewrite Bivar.fstE (bigD1 a) //= dE eqxx /=.
rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 ?addR0 //.
by move=> a' /negbTE; rewrite dE /= eq_sym => ->.
Qed.
Lemma swap : Swap.d d = d.
Proof.
apply/dist_ext => -[a1 a2].
by rewrite Swap.dE !dE /= eq_sym; case: ifPn => // /eqP ->.
Qed.
End self.
End Self.

Lemma Pr_swap (A B : finType) (P : {dist A * B}) a b :
  Pr P (setX a b) = Pr (Swap.d P) (setX b a).
Proof.
rewrite /Pr !big_setX exchange_big /=; apply eq_bigr => b' _.
apply eq_bigr => a' _; by rewrite Swap.dE.
Qed.

Module SwapHead.
Section swaphead.
Variables (A B C : finType) (P : {dist A * B * C}).

Definition f (x : B * A * C) : R := P (x.1.2, x.1.1, x.2).

Lemma f0 x : 0 <= f x. Proof. exact: dist_ge0. Qed.

Lemma f1 : \rsum_(x in {: B * A * C}) f x = 1.
Proof.
rewrite /f.
rewrite -(pair_big xpredT xpredT (fun x1 x2 => P ((fun x => (x.2, x.1)) x1, x2))) /=.
rewrite -(pmf1 (Swap.d (Bivar.fst P))).
apply eq_bigr; case => b a _ /=.
by rewrite Swap.dE /= Bivar.fstE.
Qed.

Definition d : {dist B * A * C} := locked (makeDist f0 f1).

Lemma dE x : d x = P (x.1.2, x.1.1, x.2).
Proof. by rewrite /d; unlock. Qed.

Lemma fst a b : (Bivar.fst d) (b, a) = (Bivar.fst P) (a, b).
Proof. rewrite !Bivar.fstE /d; unlock; exact: eq_bigr. Qed.

Lemma snd c : (Bivar.snd d) c = (Bivar.snd P) c.
Proof.
rewrite /Bivar.snd; unlock => /=; rewrite /Bivar.mr /d /= /f.
rewrite (eq_bigl (fun x => (xpredT x.1) && (x.2 == c))) //.
rewrite (eq_bigr (fun x => P (x.1, x.2))); last by case.
rewrite -(pair_big xpredT (pred1 c) (fun a b => P (a, b))) /=.
unlock.
rewrite -[in LHS](pair_big xpredT (pred1 c) (fun x1 x2 => P ((fun x => (x.2, x.1)) x1, x2))) /=.
rewrite -[in LHS](pair_big xpredT xpredT (fun x1 x2 => \rsum_(j | j == c) P (x2, x1, j))) /=.
rewrite exchange_big pair_big /=.
by apply eq_bigr; case.
Qed.

End swaphead.
End SwapHead.

Module DistA.
Section dista.
Variables (A B C : finType) (P : {dist A * B * C}).

Definition f (x : A * (B * C)) : R := P (x.1, x.2.1, x.2.2).

Lemma f0 x : 0 <= f x. Proof. exact: dist_ge0. Qed.

Lemma f1 : \rsum_(x in {: A * (B * C) }) f x = 1.
Proof.
rewrite /f (eq_bigr (fun x => P (x.1, x.2.1, x.2.2))); last by move=> -[? []].
rewrite -(pair_big xpredT xpredT (fun x1 x2 => P (x1, x2.1, x2.2))) /=.
evar (f : A -> R).
rewrite (eq_bigr f); last first.
  move=> a _; rewrite -(pair_big xpredT xpredT (fun x1 x2 => P (a, x1, x2))) /= /f; reflexivity.
rewrite {}/f !pair_big /= -(pmf1 P) /=; by apply eq_bigr => -[[]].
Qed.

Definition d : {dist A * (B * C)} := locked (makeDist f0 f1).

Lemma dE x : d x = P (x.1, x.2.1, x.2.2).
Proof. by rewrite /d; unlock. Qed.

Lemma dom_by a b c : d (a, (b, c)) = 0 -> P (a, b, c) = 0.
Proof. by rewrite dE. Qed.

Lemma dom_byN a b c : P (a, b, c) != 0 -> d (a, (b, c)) != 0.
Proof. by apply: contra => /eqP H; apply/eqP; apply: dom_by H. Qed.

Lemma fst_snd : Bivar.fst (Bivar.snd d) = Bivar.snd (Bivar.fst P).
Proof.
apply/dist_ext => b /=; rewrite Bivar.sndE Bivar.fstE.
evar (f : C -> R).
rewrite (eq_bigr f); last by move=> c _; rewrite Bivar.sndE /f; reflexivity.
rewrite {}/f exchange_big /=; apply eq_bigr => a _.
rewrite Bivar.fstE; apply eq_bigr => c _; by rewrite dE.
Qed.

Lemma fst : Bivar.fst d = Bivar.fst (Bivar.fst P).
Proof.
apply/dist_ext => a; rewrite 2!Bivar.fstE /=.
rewrite (eq_bigr (fun i => d (a, (i.1, i.2)))); last by case.
rewrite -(pair_big xpredT xpredT (fun i1 i2 => d (a, (i1, i2)))) /=.
apply eq_bigr => b _; rewrite Bivar.fstE; apply eq_bigr => c _; by rewrite dE.
Qed.

End dista.
End DistA.

Module Dist13.
Section dist13.
Variables (A B C : finType) (P : {dist A * B * C}).

Definition f (x : A * C) : R := \rsum_(b in B) P (x.1, b, x.2).

Lemma f0 x : 0 <= f x. Proof. apply rsumr_ge0 => b _; exact: dist_ge0. Qed.

Lemma f1 : \rsum_(x in {: A * C}) f x = 1.
Proof.
rewrite /f.
rewrite -(pair_big xpredT xpredT (fun x1 x2 => \rsum_(b in B) P (x1, b, x2))) /=.
evar (f : A -> R).
rewrite (eq_bigr f); last by move=> a _; rewrite exchange_big /= /f; reflexivity.
rewrite {}/f pair_big /= pair_big /= -(pmf1 P) /=; by apply eq_bigr => -[[]].
Qed.

Definition d : {dist A * C} := locked (makeDist f0 f1).

Lemma dE x : d x = \rsum_(b in B) P (x.1, b, x.2).
Proof. by rewrite /d; unlock. Qed.

Lemma dom_by a b c : d (a, c) = 0 -> P (a, b, c) = 0.
Proof. rewrite dE /= => /prsumr_eq0P -> // b' _; exact: dist_ge0. Qed.

Lemma dom_byN a b c : P (a, b, c) != 0 -> d (a, c) != 0.
Proof. by apply: contra => /eqP H; apply/eqP/dom_by. Qed.

Lemma snd : Bivar.snd d = Bivar.snd P.
Proof.
apply/dist_ext => c; rewrite !Bivar.sndE /=.
rewrite (eq_bigr (fun i => P (i.1, i.2, c))); last by case.
rewrite -(pair_big xpredT xpredT (fun i1 i2 => P (i1, i2, c))) /=.
by apply/eq_bigr => a _; rewrite dE; apply eq_bigr => b _.
Qed.

Lemma fst : Bivar.fst d = Bivar.fst (DistA.d P).
Proof.
apply/dist_ext => a; rewrite !Bivar.fstE /=.
rewrite [in RHS](eq_bigr (fun i => (DistA.d P) (a, (i.1, i.2)))); last by case.
rewrite -(pair_big xpredT xpredT (fun i1 i2 => (DistA.d P) (a, (i1, i2)))) /=.
rewrite exchange_big /=; apply eq_bigr => c _; rewrite dE /=; apply eq_bigr => b _.
by rewrite DistA.dE.
Qed.

End dist13.
End Dist13.

Module Swap23.
Section swap23.
Variables (A B C : finType) (P : {dist A * B * C}).

Definition f (x : A * C * B) : R := P (x.1.1, x.2, x.1.2).

Lemma f0 x : 0 <= f x. Proof. exact: dist_ge0. Qed.

Lemma f1 : \rsum_(x in {: A * C * B}) f x = 1.
Proof.
rewrite /f.
rewrite -(pair_big xpredT xpredT (fun x1 x2 => P (x1.1, x2, x1.2))) /=.
rewrite -(pair_big xpredT xpredT (fun x1 x2 => \rsum_(j | true) P (x1, j, x2))) /=.
rewrite -(pmf1 (DistA.d P)) /=.
rewrite (eq_bigr (fun x => (DistA.d P) (x.1, x.2))); last by case.
rewrite -(pair_big xpredT xpredT (fun x1 x2 => (DistA.d P) (x1, x2))) /=.
apply eq_bigr => a _.
rewrite exchange_big /= pair_big /=; apply eq_bigr => -[b c] _ /=.
by rewrite DistA.dE.
Qed.

Definition d : {dist A * C * B} := locked (makeDist f0 f1).

Lemma dE x : d x = P (x.1.1, x.2, x.1.2).
Proof. by rewrite /d; unlock. Qed.

Lemma snd : Bivar.snd d = Bivar.snd (Bivar.fst P).
Proof.
apply/dist_ext => b.
rewrite !Bivar.sndE /= (eq_bigr (fun i => d (i.1, i.2, b))); last by case.
rewrite -(pair_big xpredT xpredT (fun i1 i2 => d (i1, i2, b))) /=.
apply eq_bigr => a _; rewrite Bivar.fstE; apply eq_bigr => c _; by rewrite dE.
Qed.

Lemma fst : Bivar.fst (DistA.d d) = Bivar.fst (DistA.d P).
Proof.
apply/dist_ext => a; rewrite !Bivar.fstE.
rewrite (eq_bigr (fun i => (DistA.d d) (a, (i.1, i.2)))); last by case.
rewrite -(pair_big xpredT xpredT (fun i1 i2 => (DistA.d d) (a, (i1, i2)))).
rewrite exchange_big pair_big; apply eq_bigr => -[b c] _ /=.
by rewrite DistA.dE /= dE /= DistA.dE.
Qed.

Lemma fst2 : Bivar.fst (Bivar.fst d) = Bivar.fst (Bivar.fst P).
Proof.
apply/dist_ext => a; rewrite !Bivar.fstE /=.
evar (f : C -> R).
rewrite (eq_bigr f); last first.
  move=> c _; rewrite Bivar.fstE /f; reflexivity.
rewrite {}/f exchange_big /=; apply eq_bigr => b _.
by rewrite Bivar.fstE; apply eq_bigr => c _; rewrite dE.
Qed.

Lemma sndA : Bivar.snd (DistA.d d) = Swap.d (Bivar.snd (DistA.d P)).
Proof.
apply/dist_ext => -[c b].
rewrite Swap.dE !Bivar.sndE /=; apply eq_bigr => a _; by rewrite !DistA.dE /= dE.
Qed.

End swap23.
End Swap23.

Module Dist23.
Section dist23.
Variables (A B C : finType) (P : {dist A * B * C}).

Definition f (x : B * C) : R := \rsum_(a in A) P (a, x.1, x.2).

Lemma f0 x : 0 <= f x. Proof. apply rsumr_ge0 => b _; exact: dist_ge0. Qed.

Lemma f1 : \rsum_(x in {: B * C}) f x = 1.
Proof.
rewrite /f exchange_big /= -(pmf1 (DistA.d P)) /= pair_big /=.
apply eq_bigr => -[a [b c]] /=; by rewrite DistA.dE.
Qed.

Definition d : {dist B * C} := locked (makeDist f0 f1).

Lemma dE x : d x = \rsum_(a in A) P (a, x.1, x.2).
Proof. by rewrite /d; unlock. Qed.

Lemma dom_by a b c : d (b, c) = 0 -> P (a, b, c) = 0.
Proof. rewrite dE /= => /prsumr_eq0P -> // a' _; exact: dist_ge0. Qed.

Lemma dom_byN a b c : P (a, b, c) != 0 -> d (b, c) != 0.
Proof. by apply: contra => /eqP H; apply/eqP; apply: dom_by. Qed.

Lemma snd : Bivar.snd d = Bivar.snd P.
Proof.
apply/dist_ext => c; rewrite !Bivar.sndE /=.
rewrite (eq_bigr (fun i => P (i.1, i.2, c))); last by case.
rewrite -(pair_big xpredT xpredT (fun i1 i2 => P (i1, i2, c))) /=.
by rewrite exchange_big; apply/eq_bigr => a _; rewrite dE; apply eq_bigr => b _.
Qed.

End dist23.
End Dist23.

Section distributions_prop.

Variables (A B C : finType) (P : {dist A * B * C}).

Lemma Dist23Swap23 : Bivar.fst P = Dist13.d (Swap23.d P).
Proof.
apply/dist_ext => -[a b].
rewrite Dist13.dE Bivar.fstE; apply eq_bigr => c _; by rewrite Swap23.dE.
Qed.

End distributions_prop.

Section conditional_probability.

Variables (A B : finType) (P : {dist A * B}).

(* Pr(a | b) *)
Definition cPr (a : {set A}) (b : {set B}) :=
  Pr P (setX a b) / Pr (Bivar.snd P) b.

Lemma Pr_cPr (a : {set A}) (b : {set B}) :
  Pr P (setX a b) = cPr a b * Pr (Bivar.snd P) b.
Proof.
case/boolP : (Pr (Bivar.snd P) b == 0) => [/eqP H0|H0].
- by rewrite H0 mulR0 Pr_snd_eq0.
- by rewrite /cPr -mulRA mulVR // mulR1.
Qed.

Lemma cPr_setT (a : {set A}) : cPr a setT = Pr (Bivar.fst P) a.
Proof.
rewrite /cPr Pr_setT divR1 /Pr big_setX /=; apply eq_bigr => a' a'a.
by rewrite Bivar.fstE /=; apply eq_bigl => b; rewrite inE.
Qed.

Lemma cPr_ge0 (a : {set A}) (b : {set B}) : 0 <= cPr a b.
Proof.
rewrite /cPr.
case/boolP : (Pr (Bivar.snd P) b == 0) => [/eqP|] H0.
  suff -> : Pr P (setX a b) = 0 by rewrite div0R; exact: leRR.
  by rewrite Pr_snd_eq0.
apply divR_ge0; [exact: Pr_ge0 | by rewrite -Pr_neq0].
Qed.

Lemma cPr_max (a : {set A}) (b : {set B}) : cPr a b <= 1.
Proof.
rewrite /cPr.
case/boolP : (Pr (Bivar.snd P) b == 0) => [/eqP|] H0.
  by rewrite Pr_snd_eq0 // div0R.
rewrite leR_pdivr_mulr -?Pr_neq0 // mul1R /Pr big_setX /= exchange_big /=.
apply ler_rsum => b0 _.
rewrite Bivar.sndE; apply ler_rsum_l => // a0 _;
  [exact: leRR | exact: dist_ge0].
Qed.

Lemma cPr_gt0 (a : {set A}) (b : {set B}) : 0 < cPr a b <-> cPr a b != 0.
Proof.
split; rewrite /cPr; first by rewrite ltR_neqAle => -[/eqP H1 _]; rewrite eq_sym.
rewrite ltR_neqAle eq_sym => /eqP H; split => //; exact: cPr_ge0.
Qed.

Lemma cPr_Pr_setX_eq0 (a : {set A}) (b : {set B}) :
  0 < Pr P (setX a b) <-> 0 < cPr a b.
Proof.
rewrite -Pr_neq0; split => H; last first.
  move/cPr_gt0 : H; apply: contra.
  rewrite /cPr => /eqP ->; by rewrite div0R.
rewrite /cPr; apply/divR_gt0; first by rewrite -Pr_neq0.
rewrite -Pr_neq0; apply: contra H => /eqP H; by rewrite Pr_snd_eq0.
Qed.

End conditional_probability.

Notation "\Pr_ P [ A | B ]" := (cPr P A B) (at level 3, P, A, B at next level,
  format "\Pr_ P [ A  |  B ]").

Section conditional_probability_prop.

Variables (A B C : finType) (P : {dist A * B * C}).

Lemma Pr_Swap23 a b c : \Pr_(DistA.d P)[[set a] | [set (b, c)]] =
  \Pr_(DistA.d (Swap23.d P))[[set a] | [set (c, b)]].
Proof.
rewrite /cPr; congr (_ / _).
- by rewrite !Pr_setX1 !Pr_set1 !DistA.dE /= Swap23.dE.
- by rewrite Swap23.sndA -Pr_setX1 Pr_swap Pr_setX1.
Qed.

End conditional_probability_prop.

Module CondDist.
Section conddist.

Variables (A B : finType) (PQ : {dist A * B}) (b : B).
Hypothesis Hb : Bivar.snd PQ b != 0.

Lemma temp :
  \rsum_(i in A) Pr PQ (setX [set i] [set b]) = Pr (Bivar.snd PQ) [set b].
Proof.
rewrite /Pr (eq_bigr (fun i =>
    \rsum_(a in [set i]) \rsum_(j in [set b]) PQ (a, j))); last first.
  by move=> a _; rewrite big_setX.
rewrite pair_big_dep /= exchange_big /=; apply eq_bigr => b0 _.
rewrite Bivar.sndE (reindex_onto (fun x => (x, x)) fst); last first.
  by case => /= a b1; rewrite in_set1 => /eqP ->.
by rewrite /= (eq_bigl predT) // => a; rewrite !inE !eqxx.
Qed.

Definition f a := \Pr_PQ [[set a] | [set b]].

Lemma f0 a : 0 <= f a. Proof. exact: cPr_ge0. Qed.

Lemma f1 : \rsum_(a in A) f a = 1.
Proof. by rewrite /f /cPr -big_distrl /= temp mulRV // Pr_set1. Qed.

Definition d : {dist A} := locked (makeDist f0 f1).

Lemma dE a : d a = \Pr_PQ [[set a] | [set b]].
Proof. by rewrite /d; unlock. Qed.

End conddist.
End CondDist.

Arguments CondDist.d {A} {B} _ _ _.

Section total_probability_theorem.

Variables (A B : finType) (n : nat).
Variables (PQ : {dist A * B}) (a : 'I_n -> {set A}) (b : {set B}).
Let P := Bivar.fst PQ.
Let Q := Bivar.snd PQ.
Let QP := Swap.d PQ.

Lemma total_prob :
  (forall i j, i != j -> [disjoint a i & a j]) ->
  cover [set a i | i in 'I_n] = [set: A] ->
  Pr Q b = \rsum_(i < n) Pr P (a i) * \Pr_QP [b | a i].
Proof.
move=> H1 H2.
transitivity (\rsum_(i < n) Pr QP (setX b (a i))).
  transitivity (Pr QP (setX b (\bigcup_(i < n) a i))).
    rewrite Pr_cPr Swap.snd.
    move: H2; rewrite cover_imset => ->.
    by rewrite cPr_setT Pr_setT mulR1 Swap.fst.
  rewrite (@Pr_ext _ _ _ (\bigcup_(i < n) setX b (a i))); last first.
    apply/setP => -[x y] /=; rewrite !inE /=.
    apply/andP/bigcupP => [[K1] /bigcupP[/= i _ yai]|[/=i _]].
      exists i => //; by rewrite !inE /= K1.
    rewrite !inE /= => /andP[xb yai]; rewrite xb; split => //.
    apply/bigcupP; by exists i.
  rewrite Pr_big_union_disj // => i j ij.
  have := H1 _ _ ij.
  rewrite -!setI_eq0 => /set0Pn => K.
  apply/set0Pn => -[[b0 a0]]; rewrite !inE /= -andbA => /and4P[_ Ha0 _ Ha0'].
  by apply K; exists a0; rewrite !inE Ha0.
apply eq_bigr => i _; by rewrite Pr_cPr mulRC Swap.snd.
Qed.

End total_probability_theorem.

Section bayes_theorem.

Variables (A B : finType) (PQ : {dist A * B}).
Let P := Bivar.fst PQ.
Let Q := Bivar.snd PQ.
Let QP := Swap.d PQ.

Lemma bayes (a : {set A}) (b : {set B}) :
  \Pr_PQ[a | b] = \Pr_QP [b | a] * Pr P a / Pr Q b.
Proof.
rewrite /cPr -Pr_swap Swap.snd -/Q -/P.
case/boolP : (Pr P a == 0) => [/eqP|] H0.
  by rewrite Pr_fst_eq0 // !(mul0R,div0R).
- rewrite /Rdiv -!mulRA; congr (_ * _).
  by rewrite mulRCA mulRA mulRV // mul1R.
Qed.

Lemma bayes_family n (a : 'I_n -> {set A}) (b : {set B}) :
  (forall i j, i != j -> [disjoint a i & a j]) ->
  cover [set a i | i in 'I_n] = [set: A] ->
  forall i,
  \Pr_PQ [a i | b] = (\Pr_QP [b | a i] * Pr P (a i)) /
                     \rsum_(j < n) \Pr_ QP [ b | a j] * Pr P (a j).
Proof.
move=> H1 H2 i.
rewrite bayes (total_prob _ _ H1) //; congr (_ / _).
apply eq_bigr => j _; by rewrite mulRC.
Qed.

End bayes_theorem.

Module JointEntropy.
Section jointentropy.
Variables (A B : finType) (P : {dist A * B}).

(* joint entropy = entropy of joint distribution, cover&thomas 2.8 *)
Definition h := `H P.

(* alternative expression using expected value *)
Lemma hE : h = `E (--log P). (* cover&thomas 2.9 *)
Proof. by rewrite /h entropy_Ex. Qed.

Lemma hC : h = `H (Swap.d P).
Proof.
congr (- _) => /=.
rewrite (eq_bigr (fun a => P (a.1, a.2) * log (P (a.1, a.2)))); last by case.
rewrite -(pair_big xpredT xpredT (fun a1 a2 => P (a1, a2) * log (P (a1, a2)))) /=.
rewrite exchange_big pair_big; apply eq_bigr => -[a b] _; by rewrite Swap.dE.
Qed.

End jointentropy.
End JointEntropy.

Module CondEntropy.
Section condentropy.
Variables (A B : finType) (QP : {dist B * A}).

(* H(Y|X = a) *)
Definition h1 a := - \rsum_(b in B)
  \Pr_QP [ [set b] | [set a] ] * log (\Pr_QP [ [set b] | [set a] ]).

Let P := Bivar.snd QP.

(* Definition of conditional entropy, cover&thomas 2.10 *)
Definition h := \rsum_(a in A) P a * h1 a.

Let PQ := Swap.d QP.

(* cover&thomas 2.12 *)
Lemma hE : h = - \rsum_(a in A) \rsum_(b in B)
  PQ (a, b) * log (\Pr_QP [ [set b] | [set a]]).
Proof.
rewrite /h (big_morph _ morph_Ropp oppR0) /=; apply eq_bigr => a _.
rewrite /h1 mulRN big_distrr /=; congr (- _); apply eq_bigr => b _.
rewrite mulRA; congr (_ * _).
by rewrite mulRC -(Pr_set1 P a) -Pr_cPr Pr_setX1 Pr_set1 Swap.dE.
Qed.

Lemma h1_ge0 a : 0 <= h1 a.
Proof.
rewrite /h1 (big_morph _ morph_Ropp oppR0); apply rsumr_ge0 => b _.
rewrite -mulRN.
case/boolP : (\Pr_QP[[set b]|[set a]] == 0) => [/eqP|] H0.
  rewrite H0 mul0R; exact/leRR.
apply mulR_ge0; [exact: cPr_ge0|].
rewrite -oppR0 -(Log_1 2) /log leR_oppr oppRK.
apply Log_increasing_le => //; [by rewrite cPr_gt0 | exact: cPr_max].
Qed.

Lemma h_ge0 : 0 <= h.
Proof.
apply rsumr_ge0 => a _; apply mulR_ge0; [exact: dist_ge0 | exact: h1_ge0].
Qed.

End condentropy.
End CondEntropy.

Section cond_entropy_prop.

Variable (A : finType) (P : {dist A}).

Lemma joint_entropy_self : `H (Self.d P) = `H P.
Proof.
rewrite /entropy; congr (- _).
rewrite (eq_bigr  (fun a => Self.d P (a.1, a.2) * log (Self.d P (a.1, a.2)))); last by case.
rewrite -(pair_big xpredT xpredT (fun a1 a2 => Self.d P (a1, a2) * log (Self.d P (a1, a2)))) /=.
apply/eq_bigr => a _.
rewrite (bigD1 a) //= !Self.dE /= eqxx (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 ?addR0 //.
move=> a' /negbTE; rewrite Self.dE /= eq_sym => ->; by rewrite mul0R.
Qed.

End cond_entropy_prop.

Section entropy_chain_rule.
Variables (A B : finType) (PQ : {dist A * B}).
Let P := Bivar.fst PQ.
Let QP := Swap.d PQ.

Lemma entropy_chain_rule : JointEntropy.h PQ = `H P + CondEntropy.h QP.
Proof.
rewrite /JointEntropy.h {1}/entropy.
transitivity (- (\rsum_(a in A) \rsum_(b in B)
    PQ (a, b) * log (P a * \Pr_QP [ [set b] | [set a] ]))). (* 2.16 *)
  congr (- _); rewrite pair_big /=; apply eq_bigr => -[a b] _ /=.
  congr (_ * log _); case/boolP : (P a == 0) => [/eqP|] H0.
  - by rewrite (Bivar.dom_by_fst _ H0) H0 mul0R.
  - by rewrite -(Pr_set1 P a) /P -(Swap.snd PQ) mulRC -Pr_cPr Pr_setX1 Pr_set1 Swap.dE.
transitivity (
  - (\rsum_(a in A) \rsum_(b in B) PQ (a, b) * log (P a))
  - (\rsum_(a in A) \rsum_(b in B) PQ (a, b) * log (\Pr_QP [ [set b] | [set a] ]))). (* 2.17 *)
  rewrite -oppRB; congr (- _); rewrite -addR_opp oppRK -big_split /=.
  apply eq_bigr => a _; rewrite -big_split /=; apply eq_bigr => b _.
  case/boolP : (PQ (a, b) == 0) => [/eqP H0|H0].
  - by rewrite H0 !mul0R addR0.
  - rewrite -mulRDr; congr (_ * _); rewrite mulRC logM //.
    by rewrite -cPr_Pr_setX_eq0 Pr_setX1 Pr_set1 Swap.dE -dist_neq0.
    rewrite -dist_neq0; exact: Bivar.dom_by_fstN H0.
rewrite /CondEntropy.h [in X in _ + X = _](big_morph _ morph_Ropp oppR0); congr (_ + _).
- (* TODO: lemma? *)
  congr (- _); apply eq_bigr => a _.
  by rewrite -big_distrl /= -Bivar.fstE.
- apply eq_bigr => a _.
  rewrite /CondEntropy.h1 /= mulRN; congr (- _).
  rewrite big_distrr /=; apply eq_bigr => b _.
  rewrite mulRA; congr (_ * _).
  by rewrite -(Pr_set1 (Bivar.snd _) a) mulRC -Pr_cPr Pr_setX1 Pr_set1 Swap.dE.
Qed.

End entropy_chain_rule.

Section conditional_entropy_prop.

Variables (A B : finType) (PQ : {dist A * B}).
Let P := Bivar.fst PQ.
Let Q := Bivar.snd PQ.
Let QP := Swap.d PQ.

Lemma entropyB : `H P - CondEntropy.h PQ = `H Q - CondEntropy.h QP.
Proof.
apply/eqP; rewrite subR_eq addRAC -subR_eq subR_opp; apply/eqP.
rewrite -entropy_chain_rule JointEntropy.hC.
rewrite -/(JointEntropy.h (Swap.d PQ)) entropy_chain_rule.
by rewrite Swap.fst -/Q Swap.dI.
Qed.

End conditional_entropy_prop.

Section conditional_entropy_prop2.

Variables (A : finType) (P : {dist A}).

Lemma CondEntrop_self : CondEntropy.h (Self.d P) = 0.
Proof.
move: (@entropy_chain_rule _ _ (Self.d P)) => /eqP.
rewrite !Self.fst Self.swap addRC -subR_eq => /eqP <-.
by rewrite /JointEntropy.h joint_entropy_self subRR.
Qed.

End conditional_entropy_prop2.

Section conditional_entropy_prop3.

Variables (A B C : finType) (PQR : {dist A * B * C}).

Lemma h1Swap23 b c : CondEntropy.h1 (DistA.d PQR) (b, c) = CondEntropy.h1 (DistA.d (Swap23.d PQR)) (c, b).
Proof.
rewrite /CondEntropy.h1; congr (- _).
apply eq_bigr => a _.
suff H : \Pr_(DistA.d PQR)[[set a] | [set (b, c)]] = \Pr_(DistA.d (Swap23.d PQR))[[set a] | [set (c, b)]].
  rewrite H //.
by rewrite Pr_Swap23.
Qed.

Lemma hSwap23 : CondEntropy.h (DistA.d PQR) = CondEntropy.h (DistA.d (Swap23.d PQR)).
Proof.
rewrite /CondEntropy.h /=.
rewrite (eq_bigr (fun a => (Bivar.snd (DistA.d PQR)) (a.1, a.2) * CondEntropy.h1 (DistA.d PQR) (a.1, a.2))); last by case.
rewrite -(pair_big xpredT xpredT (fun a1 a2 => (Bivar.snd (DistA.d PQR)) (a1, a2) * CondEntropy.h1 (DistA.d PQR) (a1, a2))) /=.
rewrite exchange_big pair_big /=; apply eq_bigr => -[c b] _ /=; congr (_ * _).
  by rewrite Swap23.sndA Swap.dE.
by rewrite h1Swap23.
Qed.

End conditional_entropy_prop3.

Section entropy_chain_rule_corollary.
Variables (A B C : finType) (PQR : {dist A * B * C}).
Let PR : {dist A * C} := Dist13.d PQR.
Let QPR : {dist B * (A * C)} := DistA.d (SwapHead.d PQR).

(* H(X,Y|Z) = H(X|Z) + H(Y|X,Z) *)
Lemma chain_rule_corollary :
  CondEntropy.h PQR = CondEntropy.h PR + CondEntropy.h QPR.
Proof.
rewrite !CondEntropy.hE -oppRD; congr (- _).
rewrite [in X in _ = _ + X](eq_bigr (fun j => \rsum_(i in B) (Swap.d QPR) ((j.1, j.2), i) * log \Pr_QPR[[set i] | [set (j.1, j.2)]])); last by case.
rewrite -[in RHS](pair_big xpredT xpredT (fun j1 j2 => \rsum_(i in B) (Swap.d QPR ((j1, j2), i) * log \Pr_QPR[[set i] | [set (j1, j2)]]))) /=.
rewrite [in X in _ = _ + X]exchange_big /= -big_split; apply eq_bigr => c _ /=.
rewrite [in LHS](eq_bigr (fun j => (Swap.d PQR) (c, (j.1, j.2)) * log \Pr_PQR[[set (j.1, j.2)] | [set c]])); last by case.
rewrite -[in LHS](pair_big xpredT xpredT (fun j1 j2 => (Swap.d PQR) (c, (j1, j2)) * log \Pr_PQR[[set (j1, j2)] | [set c]])) /=.
rewrite -big_split; apply eq_bigr => a _ /=.
rewrite Swap.dE Dist13.dE big_distrl /= -big_split; apply eq_bigr => b _ /=.
rewrite !(Swap.dE,DistA.dE,SwapHead.dE) /= -mulRDr.
case/boolP : (PQR (a, b, c) == 0) => [/eqP H0|H0].
  by rewrite H0 !mul0R.
rewrite -logM; last 2 first.
  rewrite -cPr_Pr_setX_eq0 -Pr_neq0 Pr_setX1 Pr_set1; exact: Dist13.dom_byN H0.
  by rewrite -cPr_Pr_setX_eq0 -Pr_neq0 Pr_setX1 Pr_set1 DistA.dE /= SwapHead.dE.
congr (_ * log _).
(* TODO: lemma? *)
rewrite /cPr !Pr_setX1 !Pr_set1.
rewrite mulRCA -mulRA DistA.dE SwapHead.dE /=; congr (_ * _).
rewrite -invRM; last 2 first.
  apply/eqP; rewrite (@Bivar.dom_by_sndN _ _ _ a) //; exact: Dist13.dom_byN H0.
  apply/eqP; by rewrite (@Bivar.dom_by_sndN _ _ _ b) // DistA.dE /= SwapHead.dE.
suff -> : (Bivar.snd PR) c * (Bivar.snd QPR) (a, c) =
  PR (a, c) * (Bivar.snd PQR) c.
  rewrite invRM; last 2 first.
    apply/eqP; exact: Dist13.dom_byN H0.
    by apply/eqP; rewrite (@Bivar.dom_by_sndN _ _ _ (a, b)).
  rewrite mulRA mulRV ?mul1R //; exact: Dist13.dom_byN H0.
rewrite mulRC.
congr (_ * _).
  rewrite Dist13.dE Bivar.sndE; apply eq_bigr => b' _ /=.
  by rewrite DistA.dE SwapHead.dE.
rewrite !Bivar.sndE (eq_bigr (fun i => PQR ((i.1, i.2), c))); last by case.
rewrite -(pair_big xpredT xpredT (fun i1 i2 => PQR (i1, i2, c))) /=.
apply eq_bigr => a' _; by rewrite /PR Dist13.dE.
Qed.

End entropy_chain_rule_corollary.

(* TODO: move *)
Section joint_dom_by_prod.
Variables (A B : finType) (PQ : {dist A * B}).
Let P := Bivar.fst PQ.
Let Q := Bivar.snd PQ.

Local Open Scope reals_ext_scope.
Lemma Joint_dom_by_Prod : PQ << P `x Q.
Proof.
move=> -[a b].
rewrite ProdDist.dE /= => /eqP; rewrite mulR_eq0 => /orP[/eqP Pa0|/eqP Pb0];
  by [rewrite Bivar.dom_by_fst | rewrite Bivar.dom_by_snd].
Qed.

End joint_dom_by_prod.

Module MutualInfo.
Section mutualinfo.

Variables (A B : finType) (PQ : {dist A * B}).
Let P := Bivar.fst PQ.
Let Q := Bivar.snd PQ.
Let QP := Swap.d PQ.

Local Open Scope divergence_scope.

(* I(X;Y) *)
Definition mi := D( PQ || P `x Q).

(* 2.28 *)
Lemma miE : mi = \rsum_(a in A) \rsum_(b in B) PQ (a, b) * log (PQ (a, b) / (P a * Q b)).
Proof.
rewrite /mi /div (pair_big xpredT xpredT) /=; apply eq_bigr; case => a b _ /=.
case/boolP : (PQ (a, b) == 0) => [/eqP H0|H0].
- by rewrite H0 !mul0R.
- rewrite -[in X in _ = _ * (log (_ / X))]/((a, b).1).
  rewrite -[in X in _ = _ * (log (_ / X))]/((a, b).2).
  rewrite -(ProdDist.dE P Q); congr (_ * _).
  rewrite [in RHS]logDiv //.
  by rewrite -dist_neq0.
  rewrite -dist_neq0; apply: contra H0 => /eqP H0; exact/eqP/Joint_dom_by_Prod.
Qed.

(* 2.39 *)
Lemma miE2 : mi = `H P - CondEntropy.h PQ.
Proof.
rewrite miE.
transitivity (\rsum_(a in A) \rsum_(b in B)
    PQ (a, b) * log (\Pr_PQ [ [set a] | [set b] ] / P a)).
  apply eq_bigr => a _; apply eq_bigr => b _.
  rewrite /cPr Pr_setX1 2!Pr_set1 /= -/Q.
  case/boolP : (PQ (a, b) == 0) => [/eqP H0 | H0].
  - by rewrite H0 !mul0R.
  - congr (_ * log _).
    rewrite divRM; last 2 first.
      apply/eqP; exact: Bivar.dom_by_fstN H0.
      apply/eqP; exact: Bivar.dom_by_sndN H0.
    by rewrite mulRAC.
transitivity (- (\rsum_(a in A) \rsum_(b in B) PQ (a, b) * log (P a)) +
  \rsum_(a in A) \rsum_(b in B) PQ (a, b) * log (\Pr_PQ [ [set a] | [set b] ])). (* 2.37 *)
  rewrite (big_morph _ morph_Ropp oppR0) -big_split; apply/eq_bigr => a _ /=.
  rewrite (big_morph _ morph_Ropp oppR0) -big_split; apply/eq_bigr => b _ /=.
  rewrite addRC -mulRN -mulRDr addR_opp.
  case/boolP : (PQ (a, b) == 0) => [/eqP ->| H0].
  - by rewrite !mul0R.
  - congr (_ * _); rewrite logDiv //.
    + by rewrite -cPr_Pr_setX_eq0 -Pr_neq0 Pr_setX1 Pr_set1.
    + rewrite -dist_neq0; exact: Bivar.dom_by_fstN H0.
rewrite -subR_opp; congr (_ - _).
- rewrite /entropy; congr (- _); apply/eq_bigr => a _.
  by rewrite -big_distrl /= -Bivar.fstE.
- rewrite /CondEntropy.h exchange_big.
  rewrite (big_morph _ morph_Ropp oppR0); apply eq_bigr=> b _ /=.
  rewrite mulRN; congr (- _).
  rewrite big_distrr /=; apply eq_bigr=> a _ /=.
  rewrite mulRA; congr (_ * _); rewrite -/Q.
  by rewrite -[in LHS]Pr_set1 -Pr_setX1 Pr_cPr Pr_set1 -/Q mulRC.
Qed.

Lemma miE3 : mi = `H Q - CondEntropy.h QP. (* 2.40 *)
Proof. by rewrite miE2 entropyB. Qed.

Lemma miE4 : mi = `H P + `H Q - `H PQ. (* 2.41 *)
Proof.
rewrite miE2; move/eqP: (entropy_chain_rule QP).
rewrite addRC -subR_eq => /eqP; rewrite -(Swap.dI PQ) -/QP => <-.
rewrite -addR_opp oppRB Swap.fst -/Q addRA; congr (_ - _).
by rewrite JointEntropy.hC.
Qed.

(* nonnegativity of mutual information 2.90 *)
Lemma mi_ge0 : 0 <= mi.
Proof. apply div_ge0 => -[a b]; exact: Joint_dom_by_Prod. Qed.

Lemma mi0P : mi = 0 <-> PQ = P `x Q.
Proof.
split; last by rewrite /mi => <-; rewrite div0P.
rewrite /mi div0P //; exact: Joint_dom_by_Prod.
Qed.

End mutualinfo.
End MutualInfo.

Section mutualinfo_prop.

Local Open Scope divergence_scope.

(* 2.46 *)
Lemma mi_sym (A B : finType) (PQ : {dist A * B}) :
  let P := Bivar.fst PQ in
  let Q := Bivar.snd PQ in
  MutualInfo.mi PQ = MutualInfo.mi (Swap.d PQ).
Proof.
by move=> P Q; rewrite !MutualInfo.miE2 entropyB Swap.fst.
Qed.

(* self-information *)
Lemma mutual_info_self (A : finType) (P : dist A) :
  MutualInfo.mi (Self.d P) = `H P.
Proof.
by rewrite MutualInfo.miE2 CondEntrop_self subR0 Self.fst.
Qed.

End mutualinfo_prop.

Section divergence_conditional_distributions.

Variables (A B C : finType) (PQR : {dist A * B * C}).

Definition cdiv1 z := \rsum_(x in {: A * B})
  \Pr_PQR[[set x] | [set z]] * log (\Pr_PQR[[set x] | [set z]] /
    (\Pr_(Dist13.d PQR)[[set x.1] | [set z]] * \Pr_(Dist23.d PQR)[[set x.2] | [set z]])).

Local Open Scope divergence_scope.

Lemma cdiv1_is_div c
  (Hc : Bivar.snd PQR c != 0)
  (Hc1 : (Bivar.snd (Dist13.d PQR)) c != 0)
  (Hc2 : (Bivar.snd (Dist23.d PQR)) c != 0) :
  cdiv1 c = D(CondDist.d PQR c Hc ||
    (CondDist.d (Dist13.d PQR) c Hc1) `x (CondDist.d (Dist23.d PQR) c Hc2)).
Proof.
rewrite /cdiv1 /div; apply eq_bigr => -[a b] /= _; rewrite CondDist.dE.
case/boolP : (\Pr_PQR[[set (a, b)]|[set c]] == 0) => [/eqP ->|H0].
  by rewrite !mul0R.
congr (_ * _); rewrite -logDiv; last 2 first.
  by rewrite cPr_gt0.
  rewrite ProdDist.dE /=; apply mulR_gt0.
    (* TODO: lemma? *)
    rewrite CondDist.dE -cPr_Pr_setX_eq0 -Pr_neq0 Pr_setX1 Pr_set1.
    move: H0; rewrite /cPr /Rdiv mulR_neq0 => /andP[].
    rewrite Pr_setX1 Pr_set1; by move/Dist13.dom_byN.
  (* TODO: lemma? *)
  rewrite CondDist.dE -cPr_Pr_setX_eq0 -Pr_neq0 Pr_setX1 Pr_set1.
  move: H0; rewrite /cPr /Rdiv mulR_neq0 => /andP[].
  rewrite Pr_setX1 Pr_set1; by move/Dist23.dom_byN.
congr (log (_ / _)); by rewrite ProdDist.dE 2!CondDist.dE.
Qed.

Lemma cdiv1_ge0 z : 0 <= cdiv1 z.
Proof.
case/boolP : ((Bivar.snd PQR) z == 0) => [/eqP|] z0.
  apply rsumr_ge0 => -[a b] _.
  rewrite {1}/cPr Pr_setX1 Pr_set1 (Bivar.dom_by_snd _ z0) div0R mul0R.
  exact: leRR.
rewrite cdiv1_is_div.
  by rewrite Dist13.snd.
  by rewrite Dist23.snd.
move=> Hz1 Hz2; apply div_ge0 => -[a b].
rewrite ProdDist.dE !CondDist.dE /= => /eqP; rewrite mulR_eq0 => /orP[|].
(* TODO: lemma? *)
- rewrite /cPr !Pr_setX1 !Pr_set1 !mulR_eq0 => /orP[/eqP|].
  move/Dist13.dom_by => ->; by rewrite div0R.
  rewrite Dist13.snd => /eqP; rewrite /Rdiv => ->; by rewrite mulR0.
- rewrite /cPr !Pr_setX1 !Pr_set1 !mulR_eq0 => /orP[/eqP|].
  move/Dist23.dom_by => ->; by rewrite div0R.
  rewrite Dist23.snd => /eqP; rewrite /Rdiv => ->; by rewrite mulR0.
Qed.

End divergence_conditional_distributions.

Section conditional_mutual_information.

Variables (A B C : finType) (PQR : {dist A * B * C}).

(* I(X;Y|Z) = H(X|Z) - H(X|Y,Z) 2.60 *)
Definition cmi := CondEntropy.h (Dist13.d PQR) - CondEntropy.h (DistA.d PQR).

Lemma cmiE : cmi = \rsum_(x in {: A * B * C}) PQR x *
  log (\Pr_PQR[[set x.1] | [set x.2]] /
       (\Pr_(Dist13.d PQR)[[set x.1.1] | [set x.2]] * \Pr_(Dist23.d PQR)[[set x.1.2] | [set x.2]])).
Proof.
rewrite /cmi 2!CondEntropy.hE /= subR_opp (big_morph _ morph_Ropp oppR0).
rewrite (eq_bigr (fun a => \rsum_(b in A) (Swap.d (DistA.d PQR)) ((a.1, a.2), b) * log \Pr_(DistA.d PQR)[[set b] | [set (a.1, a.2)]])); last by case.
rewrite -(pair_big xpredT xpredT (fun a1 a2 => \rsum_(b in A) (Swap.d (DistA.d PQR)) ((a1, a2), b) * log \Pr_(DistA.d PQR)[[set b] | [set (a1, a2)]])).
rewrite exchange_big -big_split /=.
rewrite (eq_bigr (fun x => PQR (x.1, x.2) * log
(\Pr_PQR[[set x.1] | [set x.2]] /
        (\Pr_(Dist13.d PQR)[[set x.1.1] | [set x.2]] * \Pr_(Dist23.d PQR)[[set x.1.2] | [set x.2]])))); last by case.
rewrite -(pair_big xpredT xpredT (fun x1 x2 => PQR (x1, x2) * log
(\Pr_PQR[[set x1] | [set x2]] /
        (\Pr_(Dist13.d PQR)[[set x1.1] | [set x2]] * \Pr_(Dist23.d PQR)[[set x1.2] | [set x2]])))).
rewrite /= exchange_big; apply eq_bigr => c _.
rewrite (big_morph _ morph_Ropp oppR0) /= exchange_big -big_split /=.
rewrite (eq_bigr (fun i => PQR ((i.1, i.2), c) * log
       (\Pr_PQR[[set (i.1, i.2)] | [set c]] /
        (\Pr_(Dist13.d PQR)[[set i.1] | [set c]] * \Pr_(Dist23.d PQR)[[set i.2] | [set c]])))); last by case.
rewrite -(pair_big xpredT xpredT (fun i1 i2 => PQR ((i1, i2), c) * log
  (\Pr_PQR[[set (i1, i2)] | [set c]] /
  (\Pr_(Dist13.d PQR)[[set i1] | [set c]] * \Pr_(Dist23.d PQR)[[set i2] | [set c]])))).
apply eq_bigr => a _ /=.
rewrite Swap.dE Dist13.dE big_distrl /= (big_morph _ morph_Ropp oppR0) -big_split.
apply eq_bigr => b _ /=.
rewrite Swap.dE DistA.dE /= -mulRN -mulRDr.
case/boolP : (PQR (a, b, c) == 0) => [/eqP ->| H0]; first by rewrite !mul0R.
congr (_ * _).
rewrite addRC addR_opp -logDiv; last 2 first.
  rewrite -cPr_Pr_setX_eq0 -Pr_neq0 Pr_setX1 Pr_set1; exact: DistA.dom_byN H0.
  rewrite -cPr_Pr_setX_eq0 -Pr_neq0 Pr_setX1 Pr_set1; exact: Dist13.dom_byN H0.
congr (log _).
rewrite divRM; last 2 first.
  apply/eqP.
  rewrite -cPr_gt0 -cPr_Pr_setX_eq0 -Pr_neq0 Pr_setX1 Pr_set1; exact: Dist13.dom_byN H0.
  apply/eqP.
  rewrite -cPr_gt0 -cPr_Pr_setX_eq0 -Pr_neq0 Pr_setX1 Pr_set1; exact: Dist23.dom_byN H0.
rewrite {2}/Rdiv -mulRA mulRCA {1}/Rdiv [in LHS]mulRC; congr (_ * _).
(* TODO: lemma? *)
rewrite /cPr !Pr_setX1 !Pr_set1 DistA.dE /= {1 2}/Rdiv -mulRA; congr (_ * _).
rewrite -invRM; last 2 first.
  apply/eqP; exact: Bivar.dom_by_sndN H0.
  apply/eqP; rewrite mulR_neq0; apply/andP; split.
  exact: Dist23.dom_byN H0.
  move/Bivar.dom_by_sndN in H0; by rewrite invR_neq0 // Dist23.snd.
congr (/ _).
rewrite Dist23.snd mulRCA mulRV ?mulR1; last first.
  exact: Bivar.dom_by_sndN H0.
(* TODO: lemma? *)
rewrite Dist23.dE Bivar.sndE; apply eq_bigr => a' _; by rewrite DistA.dE.
Qed.

Let R := Bivar.snd PQR.

Lemma cmiE2 : cmi = \rsum_(z in C) R z * cdiv1 PQR z.
Proof.
rewrite cmiE.
rewrite (eq_bigr (fun x => PQR (x.1, x.2) * log
  (\Pr_PQR[[set x.1] | [set x.2]] /
    (\Pr_(Dist13.d PQR)[[set x.1.1] | [set x.2]] * \Pr_(Dist23.d PQR)[[set x.1.2] | [set x.2]])))); last by case.
rewrite -(pair_big xpredT xpredT (fun x1 x2 => PQR (x1, x2) * log
  (\Pr_PQR[[set x1] | [set x2]] /
    (\Pr_(Dist13.d PQR)[[set x1.1] | [set x2]] * \Pr_(Dist23.d PQR)[[set x1.2] | [set x2]])))).
rewrite exchange_big; apply eq_bigr => c _ /=.
rewrite big_distrr /=; apply eq_bigr => -[a b] _ /=; rewrite mulRA; congr (_ * _).
rewrite mulRC.
move: (Pr_cPr PQR [set (a, b)] [set c]); rewrite -/R Pr_set1 => <-.
by rewrite Pr_setX1 Pr_set1.
Qed.

(* 2.92 *)
Lemma cmi_ge0 : 0 <= cmi.
Proof.
rewrite cmiE2; apply rsumr_ge0 => c _.
apply mulR_ge0; [exact: dist_ge0 | exact: cdiv1_ge0].
Qed.

End conditional_mutual_information.

(* TODO: conditional relative entropy? *)

Section conditioning_reduces_entropy.

Variables (A B : finType) (PQ : {dist A * B}).
Let P := Bivar.fst PQ.
Let Q := Bivar.snd PQ.
Let QP := Swap.d PQ.

(* 2.95 *)
Lemma information_cant_hurt : CondEntropy.h PQ <= `H P.
Proof. rewrite -subR_ge0 -MutualInfo.miE2; exact: MutualInfo.mi_ge0. Qed.

End conditioning_reduces_entropy.

Section markov_chain.

Variables (A B C : finType) (PQR : {dist A * B * C}).
Let P := Bivar.fst (Bivar.fst PQR).
Let Q := Bivar.snd (Bivar.fst PQR).
Let PQ := Bivar.fst PQR.
Let QP := Swap.d PQ.
Let RQ := Swap.d (Bivar.snd (DistA.d PQR)).

(* cond. distr. of Z depends only on Y and conditionally independent of X *)
Definition markov_chain := forall (x : A) (y : B) (z : C),
  PQR (x, y, z) = P x * \Pr_QP[ [set y] | [set x]] * \Pr_RQ[ [set z] | [set y]].

Let PRQ := Swap23.d PQR.

(* X and Z are conditionally independent given Y *)
Lemma markov_cmi : markov_chain -> cmi (PRQ : {dist A * C * B}) = 0.
Proof.
rewrite /markov_chain => mc.
rewrite cmiE (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 //= => x _.
case/boolP : (PRQ x == 0) => [/eqP ->|H0]; first by rewrite mul0R.
rewrite (_ : _ / _ = 1); first by rewrite /log Log_1 mulR0.
rewrite eqR_divr_mulr ?mul1R; last first.
  rewrite mulR_neq0; apply/andP; split.
    (* TODO: lemma? *)
    rewrite /cPr mulR_neq0; apply/andP; split.
      (* TODO: lemma? *)
      rewrite Pr_setX1 Pr_set1.
      case: x => [[x11 x12] x2] in H0 *.
      exact: Dist13.dom_byN H0.
    rewrite invR_neq0 // Pr_set1 Dist13.snd.
    case: x => [x1 x2] in H0 *.
    exact: Bivar.dom_by_sndN H0.
  (* TODO: lemma? *)
  rewrite /cPr mulR_neq0; apply/andP; split.
    rewrite Pr_setX1 Pr_set1.
    case: x => [[x11 x12] x2] in H0 *.
    exact: Dist23.dom_byN H0.
  rewrite invR_neq0 // Pr_set1 Dist23.snd.
  case: x => [x1 x2] in H0 *.
  exact: Bivar.dom_by_sndN H0.
(* TODO: lemma? *) (* 2.118 *)
transitivity (Pr PRQ [set x] / Pr Q [set x.2]).
  rewrite /cPr Pr_setX1 {2}/PRQ Swap23.snd -/Q; by case: x H0.
transitivity (Pr PQ [set (x.1.1,x.2)] * \Pr_RQ[[set x.1.2]|[set x.2]] / Pr Q [set x.2]).
  congr (_ / _).
  case: x H0 => [[a c] b] H0 /=.
  rewrite /PRQ Pr_set1 Swap23.dE /= mc; congr (_ * _).
  rewrite /cPr {2}/QP Swap.snd -/P Pr_set1 mulRCA mulRV ?mulR1; last first.
    apply Bivar.dom_by_fstN with b.
    apply Bivar.dom_by_fstN with c.
    by rewrite Swap23.dE in H0.
  by rewrite /QP -Pr_swap Pr_setX1.
rewrite {1}/Rdiv -mulRA mulRCA mulRC; congr (_ * _).
  rewrite /cPr Dist13.snd -/Q {2}/PRQ Swap23.snd -/Q -/(Rdiv _ _); congr (_ / _).
  by rewrite /PRQ /PQ Pr_setX1 -Dist23Swap23.
rewrite /cPr Dist23.snd; congr (_ / _).
  (* TODO: lemma? *)
  apply eq_bigr => -[c b] _.
  rewrite /RQ Swap.dE Bivar.sndE Dist23.dE; apply/eq_bigr => a _.
  by rewrite DistA.dE /= Swap23.dE.
apply/eq_bigr => b _; by rewrite /RQ Swap.snd /PRQ Swap23.snd DistA.fst_snd.
Qed.

Let PR := Dist13.d PQR.

(* thm 2.8.1 *)
Lemma data_processing_inequality : markov_chain ->
  MutualInfo.mi PR <= MutualInfo.mi PQ.
Proof.
move=> H.
have H1 : MutualInfo.mi (DistA.d PQR) = MutualInfo.mi PR + cmi PQR.
  rewrite /cmi !MutualInfo.miE2 addRA; congr (_ - _).
  by rewrite -/PR subRK /PR Dist13.fst.
have H2 : MutualInfo.mi (DistA.d PQR) = MutualInfo.mi PQ + cmi PRQ.
  transitivity (MutualInfo.mi (DistA.d PRQ)).
    by rewrite !MutualInfo.miE2 Swap23.fst hSwap23.
  rewrite /cmi !MutualInfo.miE2 addRA; congr (_ - _).
  by rewrite DistA.fst {1}/PRQ -Dist23Swap23 -/PQ subRK /PQ Swap23.fst2.
have H3 : cmi PRQ = 0 by rewrite markov_cmi.
have H4 : 0 <= cmi PQR by exact: cmi_ge0.
move: H2; rewrite {}H3 addR0 => <-.
by rewrite {}H1 addRC -leR_subl_addr subRR.
Qed.

End markov_chain.

Require Import channel.

Local Open Scope channel_scope.

Section condentropychan_condentropy.

Variables (A B : finType) (W : `Ch_1(A, B)) (P : dist A).
Let PQ := JointDistChan.d P W.
Let QP := Swap.d PQ.

Lemma cond_entropy_chanE : (forall (a : A) (b : B), cPr QP [set b] [set a] = W a b) ->
  `H(W | P) = CondEntropy.h QP.
Proof.
move=> H.
rewrite CondEntropyChan.hE CondEntropy.hE (big_morph _ morph_Ropp oppR0).
apply eq_bigr => a _.
rewrite /entropy mulRN; congr (- _).
rewrite big_distrr /=; apply eq_bigr => b _.
rewrite !Swap.dE JointDistChan.dE /= mulRCA mulRA; congr (_ * log _).
by rewrite H.
Qed.

End condentropychan_condentropy.
