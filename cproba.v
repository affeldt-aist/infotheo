From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.
Require Import proba divergence entropy.

(* tentative definition of conditional probability *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Module SwapDist.
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

Lemma marg1_swap : Bivar.marg1 d = Bivar.marg2 P.
Proof.
rewrite /Bivar.marg1 /d /Bivar.marg2; unlock => /=.
apply/dist_eq/pos_fun_eq/FunctionalExtensionality.functional_extensionality => b /=.
rewrite /Bivar.ml /Bivar.mr -(pair_big_fst _ _ (pred1 b)) //=.
by rewrite exchange_big /= pair_big; apply eq_bigr; case => a' b' /= /eqP ->.
Qed.

Lemma marg2_swap : Bivar.marg2 d = Bivar.marg1 P.
Proof.
rewrite /Bivar.marg1 /d /Bivar.marg2; unlock => /=.
apply/dist_eq/pos_fun_eq/FunctionalExtensionality.functional_extensionality => a /=.
rewrite /Bivar.mr /Bivar.mr -(pair_big_snd _ _ (pred1 a)) //=.
rewrite exchange_big /= pair_big /=.
rewrite (eq_bigl (fun x => x.1 == a)); last by case=> a' b' /=; rewrite inE andbT.
by apply eq_bigr; case => a' b' /= /eqP ->.
Qed.

End swap.
End SwapDist.

Section conditional_probability.

Variables (A B : finType) (P : {dist A * B}).

(* Pr(a | b) *)
Definition cPr (a : {set A}) (b : {set B}) :=
  Pr P (setX a b) / Pr (Bivar.marg2 P) b.

Lemma Pr_cPr (a : {set A}) (b : {set B}) :
  Pr P (setX a b) = cPr a b * Pr (Bivar.marg2 P) b.
Proof.
case/boolP : (Pr (Bivar.marg2 P) b == 0) => [/eqP H0|H0].
- by rewrite H0 mulR0 Pr_marg2_eq0.
- by rewrite /cPr -mulRA mulVR // mulR1.
Qed.

Lemma cPr_setT (a : {set A}) : cPr a setT = Pr (Bivar.marg1 P) a.
Proof.
rewrite /cPr Pr_setT divR1 /Pr big_setX /=; apply eq_bigr => a' a'a.
by rewrite Bivar.marg1E /=; apply eq_bigl => b; rewrite inE.
Qed.

Lemma cPr_neq0 (a : {set A}) (b : {set B}) : 0 < cPr a b <-> cPr a b != 0.
Proof.
split; rewrite /cPr; first by rewrite ltR_neqAle => -[/eqP H1 _]; rewrite eq_sym.
rewrite ltR_neqAle eq_sym => /eqP H; split => //; apply divR_ge0; first exact: Pr_ge0.
move/eqP : H; rewrite eq_sym mulR_eq0 negb_or => /andP[H1 _].
rewrite -Pr_neq0; apply: contra H1 => /eqP; by move/Pr_marg2_eq0 => ->.
Qed.

Lemma cPr_Pr_setX_eq0 (a : {set A}) (b : {set B}) :
  0 < Pr P (setX a b) <-> 0 < cPr a b.
Proof.
rewrite -Pr_neq0; split => H; last first.
  move/cPr_neq0 : H; apply: contra.
  rewrite /cPr => /eqP ->; by rewrite div0R.
rewrite /cPr; apply/divR_gt0; first by rewrite -Pr_neq0.
rewrite -Pr_neq0; apply: contra H => /eqP H; by rewrite Pr_marg2_eq0.
Qed.

End conditional_probability.

Notation "\Pr_ P [ A | B ]" := (cPr P A B) (at level 3, P, A, B at next level,
  format "\Pr_ P [ A  |  B ]").

Section total_probability_theorem.

Variables (A B : finType) (n : nat).
Variables (PQ : {dist A * B}) (a : 'I_n -> {set A}) (b : {set B}).
Let Q := Bivar.marg2 PQ.
Let P := Bivar.marg1 PQ.
Let QP := SwapDist.d PQ.

Lemma total_prob :
  (forall i j, i != j -> [disjoint a i & a j]) ->
  cover [set a i | i in 'I_n] = [set: A] ->
  Pr Q b = \rsum_(i < n) Pr P (a i) * \Pr_QP [b | a i].
Proof.
move=> H1 H2.
transitivity (\rsum_(i < n) Pr QP (setX b (a i))).
  transitivity (Pr QP (setX b (\bigcup_(i < n) a i))).
    rewrite Pr_cPr SwapDist.marg2_swap.
    move: H2; rewrite cover_imset => ->.
    by rewrite cPr_setT Pr_setT mulR1 SwapDist.marg1_swap.
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
apply eq_bigr => i _; by rewrite Pr_cPr mulRC SwapDist.marg2_swap.
Qed.

End total_probability_theorem.

Section bayes_theorem.

Variables (A B : finType) (PQ : {dist A * B}).
Let P := Bivar.marg1 PQ.
Let Q := Bivar.marg2 PQ.
Let QP := SwapDist.d PQ.

Lemma bayes (a : {set A}) (b : {set B}) :
  \Pr_PQ[a | b] = \Pr_QP [b | a] * Pr P a / Pr Q b.
Proof.
rewrite /cPr.
have <- : Pr PQ (setX a b) = Pr QP (setX b a).
  (* TODO: lemma? *)
  rewrite /Pr !big_setX exchange_big /=; apply eq_bigr => b' _.
  apply eq_bigr => a' _; by rewrite SwapDist.dE.
rewrite SwapDist.marg2_swap -/Q -/P.
case/boolP : (Pr P a == 0) => [/eqP|] H0.
  by rewrite Pr_marg1_eq0 // !(mul0R,div0R).
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
Variables (A B : finType) (PQ : {dist A * B}).

(* joint entropy = entropy of joint distribution, cover&thomas 2.8 *)
Definition h := `H PQ.

(* alternative expression using expected value *)
Lemma hE2 : h = `E (--log PQ). (* cover&thomas 2.9 *)
Proof. by rewrite /h entropy_Ex. Qed.

End jointentropy.
End JointEntropy.

Module CondEntropy.
Section condentropy.
Variables (A B : finType) (QP : {dist B * A}).
Let PQ := SwapDist.d QP.

(* H(Y|X = a) *)
Definition h1 a := - \rsum_(b in B)
  \Pr_QP [ [set b] | [set a] ] * log (\Pr_QP [ [set b] | [set a] ]).

Let P := Bivar.marg2 QP.

(* Definition of conditional entropy, cover&thomas 2.10 *)
Definition h := \rsum_(a in A) P a * h1 a.

(* cover&thomas 2.12 *)
Lemma hE : h = - \rsum_(a in A) \rsum_(b in B)
  PQ (a, b) * log (\Pr_QP [ [set b] | [set a]]).
Proof.
rewrite /h (big_morph _ morph_Ropp oppR0) /=; apply eq_bigr => a _.
rewrite /h1 mulRN big_distrr /=; congr (- _); apply eq_bigr => b _.
rewrite mulRA; congr (_ * _).
by rewrite mulRC -(Pr_set1 P a) -Pr_cPr Pr_setX1 Pr_set1 SwapDist.dE.
Qed.

End condentropy.
End CondEntropy.

Section entropy_chain_rule.
Variables (A B : finType) (PQ : {dist (A * B)}).
Let P := Bivar.marg1 PQ.
Let QP := SwapDist.d PQ.

Lemma entropy_chain_rule : JointEntropy.h PQ = `H P + CondEntropy.h QP.
Proof.
rewrite /JointEntropy.h {1}/entropy.
transitivity (- (\rsum_(a in A) \rsum_(b in B)
    PQ (a, b) * log (P a * \Pr_QP [ [set b] | [set a] ]))). (* 2.16 *)
  congr (- _); rewrite pair_big /=; apply eq_bigr => -[a b] _ /=.
  congr (_ * log _); case/boolP : (P a == 0) => [/eqP H0|H0].
  - by rewrite (Bivar.marg1_eq0 _ H0) H0 mul0R.
  - by rewrite -(Pr_set1 P a) /P -(SwapDist.marg2_swap PQ) mulRC -Pr_cPr Pr_setX1 Pr_set1 SwapDist.dE.
transitivity (
  - (\rsum_(a in A) \rsum_(b in B) PQ (a, b) * log (P a))
  - (\rsum_(a in A) \rsum_(b in B) PQ (a, b) * log (\Pr_QP [ [set b] | [set a] ]))). (* 2.17 *)
  rewrite -oppRB; congr (- _); rewrite -addR_opp oppRK -big_split /=.
  apply eq_bigr => a _; rewrite -big_split /=; apply eq_bigr => b _.
  case/boolP : (PQ (a, b) == 0) => [/eqP H0|H0].
  - by rewrite H0 !mul0R addR0.
  - rewrite -mulRDr; congr (_ * _); rewrite mulRC logM //.
    by rewrite -cPr_Pr_setX_eq0 Pr_setX1 Pr_set1 SwapDist.dE -dist_neq0.
    rewrite -dist_neq0; exact: Bivar.marg1_eq0N H0.
rewrite /CondEntropy.h [in X in _ + X = _](big_morph _ morph_Ropp oppR0); congr (_ + _).
- (* TODO: lemma? *)
  congr (- _); apply eq_bigr => a _.
  by rewrite -big_distrl /= -Bivar.marg1E.
- apply eq_bigr => a _.
  rewrite /CondEntropy.h1 /= mulRN; congr (- _).
  rewrite big_distrr /=; apply eq_bigr => b _.
  rewrite mulRA; congr (_ * _).
  by rewrite -(Pr_set1 (Bivar.marg2 _) a) mulRC -Pr_cPr Pr_setX1 Pr_set1 SwapDist.dE.
Qed.

End entropy_chain_rule.

Module SwapHead.
Section swaphead.
Variables (A B C : finType) (P : {dist A * B * C}).

Definition f (x : B * A * C) : R := P (x.1.2, x.1.1, x.2).

Lemma f0 x : 0 <= f x. Proof. exact: dist_ge0. Qed.

Lemma f1 : \rsum_(x in {: B * A * C}) f x = 1.
Proof.
rewrite /f.
rewrite -(pair_big xpredT xpredT (fun x1 x2 => P ((fun x => (x.2, x.1)) x1, x2))) /=.
rewrite -(pmf1 (SwapDist.d (Bivar.marg1 P))).
apply eq_bigr; case => b a _ /=.
by rewrite SwapDist.dE /= Bivar.marg1E.
Qed.

Definition d : {dist B * A * C} := locked (makeDist f0 f1).

Lemma dE x : d x = P (x.1.2, x.1.1, x.2).
Proof. by rewrite /d; unlock. Qed.

Lemma dist_fst a b : (Bivar.marg1 P) (a, b) = (Bivar.marg1 d) (b, a).
Proof. rewrite !Bivar.marg1E /d; unlock; exact: eq_bigr. Qed.

Lemma dist_snd c : (Bivar.marg2 P) c = (Bivar.marg2 d) c.
Proof.
rewrite /Bivar.marg2; unlock => /=; rewrite /Bivar.mr /d /= /f.
rewrite (eq_bigl (fun x => (xpredT x.1) && (x.2 == c))) //.
rewrite (eq_bigr (fun x => P (x.1, x.2))); last by case.
rewrite -(pair_big xpredT (pred1 c) (fun a b => P (a, b))) /=.
apply/esym.
unlock.
rewrite -[in LHS](pair_big xpredT (pred1 c) (fun x1 x2 => P ((fun x => (x.2, x.1)) x1, x2))) /=.
rewrite -[in LHS](pair_big xpredT xpredT (fun x1 x2 => \rsum_(j | j == c) P (x2, x1, j))) /=.
rewrite exchange_big pair_big /=.
by apply eq_bigr; case.
Qed.

End swaphead.
End SwapHead.

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

Lemma eq0 a c : d (a, c) = 0 -> forall b, P (a, b, c) = 0.
Proof.
rewrite /d; unlock => /=; rewrite /f /= => H b.
move/prsumr_eq0P : H => -> // b' _; exact: dist_ge0.
Qed.

End dist13.
End Dist13.

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

End dista.
End DistA.

Section entropy_chain_rule_corollary.
Variables (A B C : finType) (PQR : {dist A * B * C}).
Let PR : {dist A * C} := Dist13.d PQR.
Let QPR : {dist B * (A * C)} := DistA.d (SwapHead.d PQR).

Lemma chain_rule_corollary :
  CondEntropy.h PQR = CondEntropy.h PR + CondEntropy.h QPR.
Proof.
rewrite !CondEntropy.hE -oppRD; congr (- _).
rewrite [in X in _ = _ + X](eq_bigr (fun j => \rsum_(i in B) (SwapDist.d QPR) ((j.1, j.2), i) * log \Pr_QPR[[set i] | [set (j.1, j.2)]])); last by case.
rewrite -[in RHS](pair_big xpredT xpredT (fun j1 j2 => \rsum_(i in B) (SwapDist.d QPR ((j1, j2), i) * log \Pr_QPR[[set i] | [set (j1, j2)]]))) /=.
rewrite [in X in _ = _ + X]exchange_big /= -big_split; apply eq_bigr => c _ /=.
rewrite [in LHS](eq_bigr (fun j => (SwapDist.d PQR) (c, (j.1, j.2)) * log \Pr_PQR[[set (j.1, j.2)] | [set c]])); last by case.
rewrite -[in LHS](pair_big xpredT xpredT (fun j1 j2 => (SwapDist.d PQR) (c, (j1, j2)) * log \Pr_PQR[[set (j1, j2)] | [set c]])) /=.
rewrite -big_split; apply eq_bigr => a _ /=.
rewrite SwapDist.dE Dist13.dE big_distrl /= -big_split; apply eq_bigr => b _ /=.
rewrite !(SwapDist.dE,DistA.dE,SwapHead.dE) /= -mulRDr.
case/boolP : (PQR (a, b, c) == 0) => [/eqP H0|H0].
  by rewrite H0 !mul0R.
rewrite -logM; last 2 first.
  rewrite -cPr_Pr_setX_eq0 -Pr_neq0 Pr_setX1 Pr_set1.
  by apply: contra H0 => /eqP /Dist13.eq0 => ->.
  by rewrite -cPr_Pr_setX_eq0 -Pr_neq0 Pr_setX1 Pr_set1 DistA.dE /= SwapHead.dE /=.
congr (_ * log _).
rewrite /cPr !Pr_setX1 !Pr_set1.
rewrite mulRCA -mulRA DistA.dE SwapHead.dE /=; congr (_ * _).
rewrite -invRM; last 2 first.
  apply/eqP; rewrite (@Bivar.marg2_eq0N _ _ _ a) //; apply: contra H0 => /eqP.
  by move/Dist13.eq0 => ->.
  apply/eqP; by rewrite (@Bivar.marg2_eq0N _ _ _ b) // DistA.dE /= SwapHead.dE.
suff -> : (Bivar.marg2 PR) c * (Bivar.marg2 QPR) (a, c) =
  PR (a, c) * (Bivar.marg2 PQR) c.
  rewrite invRM; last 2 first.
    by apply/eqP; apply: contra H0 => /eqP /Dist13.eq0 => ->.
    by apply/eqP; rewrite (@Bivar.marg2_eq0N _ _ _ (a, b)).
  rewrite mulRA mulRV ?mul1R //.
  by apply: contra H0 => /eqP /Dist13.eq0 => ->.
rewrite mulRC.
congr (_ * _).
  rewrite Dist13.dE.
  rewrite Bivar.marg2E.
  apply eq_bigr => b' _ /=.
  by rewrite DistA.dE SwapHead.dE /=.
rewrite !Bivar.marg2E.
rewrite (eq_bigr (fun i => PQR ((i.1, i.2), c))); last by case.
rewrite -(pair_big xpredT xpredT (fun i1 i2 => PQR (i1, i2, c))) /=.
apply eq_bigr => a' _.
by rewrite /PR Dist13.dE.
Qed.

End entropy_chain_rule_corollary.

Module MutualInfo.
Section mutualinfo.

Variables (A B : finType) (PQ : {dist A * B}).
Let P := Bivar.marg1 PQ.
Let Q := Bivar.marg2 PQ.
Let QP := SwapDist.d PQ.

Local Open Scope divergence_scope.

Definition mi := D( PQ || P `x Q).

(* 2.28 *)
Lemma miE : mi = \rsum_(a in A) \rsum_(b in B) PQ (a, b) * log (PQ (a, b) / (P a * Q b)).
Proof.
rewrite /mi /div (pair_big xpredT xpredT) /=; apply eq_bigr; case => a b _ /=.
case/boolP : (PQ (a, b) == 0) => [/eqP H0|H0].
- by rewrite H0 !mul0R.
- congr (_ * _).
  move=> [:H].
  rewrite [in RHS]logM; last 2 first.
    by rewrite -dist_neq0.
    apply/invR_gt0.
    abstract: H.
    apply/mulR_gt0.
    by rewrite -dist_neq0 (Bivar.marg1_eq0N H0).
    by rewrite -dist_neq0 (Bivar.marg2_eq0N H0).
  by rewrite logV.
Qed.

(* 2.39 *)
Lemma miE2 : mi = `H P - CondEntropy.h PQ.
Proof.
rewrite miE.
transitivity (\rsum_(a in A) \rsum_(b in B)
    PQ (a, b) * log (\Pr_PQ [ [set a] | [set b] ] / P a)).
  apply eq_bigr => a _; apply eq_bigr => b _.
  rewrite /cPr Pr_setX1 2!Pr_set1 /=.
  case/boolP : (PQ (a, b) == 0) => [/eqP H0 | H0].
  - by rewrite H0 !mul0R.
  - congr (_ * log _); rewrite {2 3}/Rdiv -mulRA -invRM; last 2 first.
      apply/eqP; exact: Bivar.marg2_eq0N H0.
      apply/eqP; exact: Bivar.marg1_eq0N H0.
    by rewrite (mulRC (P a)).
transitivity (- (\rsum_(a in A) \rsum_(b in B) PQ (a, b) * log (P a)) +
  \rsum_(a in A) \rsum_(b in B) PQ (a, b) * log (\Pr_PQ [ [set a] | [set b] ])). (* 2.37 *)
  rewrite (big_morph _ morph_Ropp oppR0) -big_split; apply/eq_bigr => a _ /=.
  rewrite (big_morph _ morph_Ropp oppR0) -big_split; apply/eq_bigr => b _ /=.
  rewrite addRC -mulRN -mulRDr.
  case/boolP : (PQ (a, b) == 0) => [/eqP H0 | H0].
  - by rewrite H0 !mul0R.
  - congr (_ * _); rewrite logM; last 2 first.
      rewrite /cPr Pr_setX1 2!Pr_set1; apply divR_gt0.
        by rewrite -dist_neq0.
        rewrite -dist_neq0; exact: Bivar.marg2_eq0N H0.
      apply invR_gt0; rewrite -dist_neq0; exact: Bivar.marg1_eq0N H0.
  rewrite logV // -dist_neq0; exact: Bivar.marg1_eq0N H0.
rewrite -subR_opp; congr (_ - _).
- rewrite /entropy; congr (- _); apply/eq_bigr => a _.
  by rewrite -big_distrl /= -Bivar.marg1E.
- rewrite /CondEntropy.h exchange_big.
  rewrite (big_morph _ morph_Ropp oppR0); apply eq_bigr=> b _ /=.
  rewrite mulRN; congr (- _).
  rewrite big_distrr /=; apply eq_bigr=> a _ /=.
  rewrite mulRA; congr (_ * _).
  rewrite /cPr !(Pr_setX1,Pr_set1) mulRCA.
  case/boolP : (PQ (a, b) == 0) => [/eqP H0 | H0].
    by rewrite H0 mul0R.
  rewrite mulRV ?mulR1 //; exact: Bivar.marg2_eq0N H0.
Qed.

End mutualinfo.
End MutualInfo.

Require Import channel.

Local Open Scope channel_scope.

Section condentropychan_condentropy.

Variables (A B : finType) (W : `Ch_1(A, B)) (P : dist A).
Let PQ := JointDistChan.d P W.
Let QP := SwapDist.d PQ.

Lemma cond_entropy_chanE : (forall (a : A) (b : B), cPr QP [set b] [set a] = W a b) ->
  `H(W | P) = CondEntropy.h QP.
Proof.
move=> H.
rewrite CondEntropyChan.hE CondEntropy.hE (big_morph _ morph_Ropp oppR0).
apply eq_bigr => a _.
rewrite /entropy mulRN; congr (- _).
rewrite big_distrr /=; apply eq_bigr => b _.
rewrite !SwapDist.dE JointDistChan.dE /= mulRCA mulRA; congr (_ * log _).
by rewrite H.
Qed.

End condentropychan_condentropy.
