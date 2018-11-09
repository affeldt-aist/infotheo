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

Definition d : {dist (B * A)} := makeDist f0 f1.

Lemma dE a b : d (b, a) = P (a, b). Proof. by []. Qed.

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

Variables A B : finType.

(* Pr(a | b) *)
Definition cPr (P : {dist (A * B)}) (a : {set A}) (b : {set B}) :=
  (Pr P (setX a b) / Pr (Bivar.marg2 P) b)%R.

Lemma cPr_ext (P : {dist (A * B)}) (a a' : {set A}) (b : {set B}) :
  a :=: a' -> cPr P a b = cPr P a' b.
Proof. by move=> ->. Qed.

End conditional_probability.

Notation "\Pr_ P [ A | B ]" := (cPr P A B) (at level 3, P, A, B at next level,
  format "\Pr_ P [ A  |  B ]").

Section conditional_probability_prop.

Variables A B : finType.
Variables (PQ : {dist (A * B)}) (a : {set A}) (b : {set B}).
Let P := Bivar.marg1 PQ.
Let Q := Bivar.marg2 PQ.
Let QP := SwapDist.d PQ.

Lemma cPrE : Pr Q b != 0 -> (Pr PQ (setX a b) = Pr Q b * \Pr_PQ[a | b])%R.
Proof. by move=> ?; rewrite /cPr mulRCA mulRV // mulR1. Qed.

Lemma bayes : \Pr_PQ[a | b] = \Pr_QP [b | a] * Pr P a / Pr Q b.
Proof.
rewrite /cPr.
have <- : Pr PQ (setX a b) = Pr QP (setX b a).
  by rewrite /SwapDist.d /= /Pr !big_setX /= exchange_big.
have -> : Pr (Bivar.marg2 QP) a = Pr P a.
  rewrite /Pr; apply eq_bigr => a' _ /=; by rewrite SwapDist.marg2_swap.
case/boolP : (Pr PQ (setX a b) == 0) => [/eqP H0|H0].
- by rewrite H0 !(mul0R,div0R).
- rewrite /Rdiv -!mulRA; congr (_ * _).
  rewrite mulRA mulVR ?mul1R //.
  by apply: contra H0 => /eqP /Pr_marg1_eq0 => ->.
Qed.

End conditional_probability_prop.

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
Variables (A B : finType) (PQ : {dist A * B}).
Let P := Bivar.marg1 PQ.
Let QP := SwapDist.d PQ.

(* H(Y|X = a) *)
Definition h1 a := - \rsum_(b in B)
  \Pr_QP [ [set b] | [set a] ] * log (\Pr_QP [ [set b] | [set a] ]).

(* Definition of conditional entropy, cover&thomas 2.10 *)
Definition h := \rsum_(a in A) P a * h1 a.

(* cover&thomas 2.12 *)
Lemma hE : h = - \rsum_(a in A) \rsum_(b in B)
  PQ (a, b) * log (\Pr_QP [ [set b] | [set a]]).
Proof.
rewrite /h (big_morph _ morph_Ropp oppR0) /=; apply eq_bigr => a _.
rewrite /h1 mulRN big_distrr /=; congr (- _); apply eq_bigr => b _.
rewrite mulRA; congr (_ * _); rewrite /cPr Pr_setX1 2!Pr_set1 mulRCA.
rewrite SwapDist.marg2_swap SwapDist.dE.
case/boolP : (P a == 0) => [/eqP H0 |H0].
- by rewrite (Bivar.marg1_eq0 _ H0) mul0R.
- by rewrite mulRV // mulR1.
Qed.

End condentropy.
End CondEntropy.

Section entropy_chain_rule.
Variables (A B : finType) (PQ : {dist (A * B)}).
Let P := Bivar.marg1 PQ.
Let QP := SwapDist.d PQ.

Lemma entropy_chain_rule : JointEntropy.h PQ = `H P + CondEntropy.h PQ.
Proof.
rewrite /JointEntropy.h {1}/entropy.
transitivity (- (\rsum_(a in A) \rsum_(b in B)
    PQ (a, b) * log (P a * \Pr_QP [ [set b] | [set a] ]))). (* 2.16 *)
  congr (- _); rewrite pair_big /=; apply eq_bigr => -[a b] _ /=.
  congr (_ * log _); case/boolP : (P a == 0) => [/eqP H0|H0].
  - by rewrite (Bivar.marg1_eq0 _ H0) H0 mul0R.
  - by rewrite /cPr Pr_setX1 2!Pr_set1 SwapDist.dE SwapDist.marg2_swap mulRCA mulRV // mulR1.
transitivity (
  - (\rsum_(a in A) \rsum_(b in B) PQ (a, b) * log (P a))
  - (\rsum_(a in A) \rsum_(b in B) PQ (a, b) * log (\Pr_QP [ [set b] | [set a] ]))). (* 2.17 *)
  rewrite -oppRB; congr (- _); rewrite -addR_opp oppRK -big_split /=.
  apply eq_bigr => a _; rewrite -big_split /=; apply eq_bigr => b _.
  case/boolP : (PQ (a, b) == 0) => [/eqP H0|H0].
  - by rewrite H0 !mul0R addR0.
  - rewrite -mulRDr; congr (_ * _); rewrite mulRC logM //.
    rewrite /cPr Pr_setX1 2!Pr_set1; apply divR_gt0; first by rewrite -dist_neq0.
    rewrite -dist_neq0 SwapDist.marg2_swap; exact: Bivar.marg1_eq0N H0.
    rewrite -dist_neq0; exact: Bivar.marg1_eq0N H0.
rewrite /CondEntropy.h [in X in _ + X = _](big_morph _ morph_Ropp oppR0); congr (_ + _).
- (* TODO: lemma? *)
  congr (- _); apply eq_bigr => a _.
  by rewrite -big_distrl /= -Bivar.marg1E.
- apply eq_bigr => a _.
  rewrite /CondEntropy.h1 /= mulRN; congr (- _).
  rewrite big_distrr /=; apply eq_bigr => b _.
  rewrite mulRA; congr (_ * _).
  case/boolP : (P a == 0) => [/eqP H0|H0].
  - by rewrite (Bivar.marg1_eq0 _ H0) H0 mul0R.
  - rewrite /cPr Pr_setX1 2!Pr_set1 SwapDist.dE SwapDist.marg2_swap.
    by rewrite mulRCA mulRV // mulR1.
Qed.

End entropy_chain_rule.

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
Lemma miE2 : mi = `H P - CondEntropy.h QP.
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
  + rewrite /cPr !(Pr_setX1,Pr_set1) mulRCA SwapDist.marg2_swap.
    case/boolP : (PQ (a, b) == 0) => [/eqP H0 | H0].
      by rewrite H0 !SwapDist.dE H0 mul0R.
    rewrite mulRV ?mulR1 // SwapDist.marg1_swap; exact: Bivar.marg2_eq0N H0.
  + rewrite (_ : SwapDist.d QP = PQ) //.
    (* TODO: lemma *)
    apply/dist_eq/pos_fun_eq/FunctionalExtensionality.functional_extensionality => -[x1 x2].
    by rewrite !SwapDist.dE.
Qed.

End mutualinfo.
End MutualInfo.
