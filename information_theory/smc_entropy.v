From mathcomp Require Import all_ssreflect all_algebra fingroup perm.
From mathcomp Require Import reals exp.
Require Import ssr_ext ssralg_ext bigop_ext realType_ext realType_ln.
Require Import fdist jfdist_cond proba binary_entropy_function divergence.
Require Import entropy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.

Section pr_entropy.
Context {R : realType}.
Variables (T TY1 TY2: finType) (TY3: finZmodType) (P : R.-fdist T).
Variable n : nat.
Notation p := n.+2.
Variables (Y1: {RV P -> TY1}) (Y2: {RV P -> TY2}) (Y3: {RV P -> TY3}).

Hypothesis card_Y3 : #|TY3| = n.+1.
Hypothesis pY3_unif : `p_ Y3 = fdist_uniform card_Y3.
Hypothesis Y2Y3indep : P|= Y2 _|_ Y3.

Lemma cpr_cond_entropy1_RV y2 y3:
  (forall y1,  `Pr[ Y1 = y1 | Y2 = y2 ] = `Pr[ Y1 = y1 | [%Y2, Y3] = (y2, y3) ]) ->
  `H[Y1 | Y2 = y2] = `H[Y1 | [% Y2, Y3] = (y2, y3)].
Proof.
move=> H.
rewrite /cond_entropy1_RV /cond_entropy1.
congr -%R.
apply: eq_bigr => a _.
by rewrite 2!jcPrE -2!cpr_inE' 2!cpr_eq_set1 H.
Qed.

End pr_entropy.
