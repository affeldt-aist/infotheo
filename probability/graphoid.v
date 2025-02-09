(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix.
From mathcomp Require Import reals.
Require Import ssr_ext ssralg_ext bigop_ext  realType_ext fdist.
Require Import proba jfdist_cond.

(**md**************************************************************************)
(* # Graphoid axioms                                                          *)
(*                                                                            *)
(* This file provides a formalization of the graphoid axioms (symmetry,       *)
(* decomposition, weak_union, contraction, and intersection) and derived      *)
(* rules.                                                                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Import GRing.Theory.

(* TODO: rename, mv *)
Module Proj124.
Section proj124.
Context {R : realType}.
Variables (A B D C : finType) (P : R.-fdist (A * B * D * C)).
Definition d : R.-fdist (A * B * C) := fdistX (fdistA (fdistX (fdistA P)))`2.
Lemma dE abc : d abc = \sum_(x in D) P (abc.1.1, abc.1.2, x, abc.2).
Proof.
case: abc => [[a b] c] /=.
rewrite /d fdistXE fdist_sndE; apply eq_bigr => d _.
by rewrite fdistAE /= fdistXE fdistAE.
Qed.
Lemma snd : d`2 = P`2.
Proof. by rewrite /fdist_snd /d !fdistmap_comp. Qed.
End proj124.
End Proj124.

Definition Proj14d {R : realType} (A B C D : finType) (d : R.-fdist (A * B * D * C)) :
  R.-fdist (A * C) :=
  fdist_proj13 (Proj124.d d).

(* TODO: rename, mv *)
Module QuadA23.
Section def.
Context {R : realType}.
Variables (A B C D : finType) (P : R.-fdist (A * B * D * C)).
Definition f (x : A * B * D * C) : A * (B * D) * C :=
  (x.1.1.1, (x.1.1.2, x.1.2), x.2).
Lemma inj_f : injective f.
Proof. by rewrite /f => -[[[? ?] ?] ?] [[[? ?] ?] ?] /= [-> -> -> ->]. Qed.
Definition d : R.-fdist (A * (B * D) * C) := fdistmap f P.
Lemma dE x : d x = P (x.1.1, x.1.2.1, x.1.2.2, x.2).
Proof.
case: x => -[a [b d] c]; rewrite /def.d fdistmapE /= -/(f (a, b, d, c)).
by rewrite (big_pred1_inj inj_f).
Qed.
End def.
Section prop.
Context {R : realType}.
Variables (A B C D : finType) (P : R.-fdist (A * B * D * C)).
Lemma snd : (QuadA23.d P)`2 = P`2.
Proof. by rewrite /fdist_snd /d fdistmap_comp. Qed.
End prop.
End QuadA23.

Section cinde_rv_prop.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma cinde_drv_2C : P |= X _|_ [% Y, W] | Z -> P |= X _|_ [% W, Y] | Z.
Proof.
move=> H a -[d b] c.
by rewrite cpr_eq_pairA cpr_eq_pairAC -cpr_eq_pairA H cpr_eq_pairC.
Qed.

Lemma cinde_drv_3C : P |= X _|_ Y | [% Z, W] -> P |= X _|_ Y | [% W, Z].
Proof.
move=> H; move=> a b -[d c]; move: (H a b (c, d)) => {}H.
by rewrite cpr_eq_pairCr H cpr_eq_pairCr; congr (_ * _); rewrite cpr_eq_pairCr.
Qed.

End cinde_rv_prop.

Section symmetry.

Context {R : realType}.
Variable (U : finType) (P : R.-fdist U).
Variables (A B C : finType) (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).

Lemma symmetry : P |= X _|_ Y | Z -> P |= Y _|_ X | Z.
Proof.
move=> H b a c.
rewrite /cinde_rv in H.
rewrite cpr_eq_pairC.
rewrite H.
by rewrite mulrC.
Qed.

End symmetry.

Section decomposition.

Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma decomposition : P |= X _|_ [% Y, W] | Z -> P |= X _|_ Y | Z.
Proof.
move=> H a b c.
transitivity (\sum_(d <- fin_img W) `Pr[ [% X, [% Y, W]] = (a, (b, d)) | Z = c]).
  rewrite -cpr_eq_set1.
  rewrite (creasoning_by_cases _ W); apply eq_bigr => /= d _.
  by rewrite setX1 cpr_eq_set1 cpr_eq_pairA.
transitivity (\sum_(d <- fin_img W)
  `Pr[ X = a | Z = c] * `Pr[ [% Y, W] = (b, d) | Z = c]).
  by apply eq_bigr => d _; rewrite H.
rewrite -big_distrr /=; congr (_ * _).
rewrite -cpr_eq_set1 (creasoning_by_cases _ W); apply eq_bigr => d _.
by rewrite setX1 cpr_eq_set1.
Qed.

End decomposition.

Section weak_union.

Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma weak_union : P |= X _|_ [% Y, W] | Z -> P |= X _|_ Y | [% Z, W].
Proof.
move=> H a b [c d].
transitivity (`Pr[ X = a | [% Y, Z, W] = (b, c, d)] *
  `Pr[ Y = b | [% Z, W] = (c, d)]).
  by rewrite cpr_eq_product_rule cpr_eq_pairAr.
transitivity (`Pr[ X = a | Z = c] * `Pr[ Y = b | [% Z, W] = (c, d)]).
  rewrite cpr_eq_pairACr.
  case/boolP : (`Pr[ [% Y, W, Z] = (b, d, c)] == 0) => [/eqP|] H0.
  - by rewrite [X in _ * X = _ * X]cpr_eqE pr_eq_pairA pr_eq_pairAC H0 mul0r !mulr0.
  - by rewrite (cinde_alt _ H).
case/boolP : (`Pr[ [% Z, W] = (c, d) ] == 0) => [/eqP|] ?.
- by rewrite [X in _ * X = _ * X]cpr_eqE (pr_eq_pairC _ Y) (pr_eq_domin_RV2 Y) ?(mul0r,mulr0).
- have {}H : P |= X _|_ W | Z by move/cinde_drv_2C : H; apply decomposition.
  by rewrite [in X in _ = X * _]cpr_eq_pairCr (cinde_alt _ H) // pr_eq_pairC.
Qed.

End weak_union.

Section contraction.

Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma contraction : P |= X _|_ W | [% Z, Y] -> P |= X _|_ Y | Z -> P |= X _|_ [% Y, W] | Z.
Proof.
move=> H1 H2 a [b d] c.
rewrite cpr_eq_product_rule.
transitivity (`Pr[X = a | [% Y, Z] = (b, c)] * `Pr[[% Y, W] = (b, d) | Z = c]).
  rewrite -cpr_eq_pairAr [in X in X * _ = _]cpr_eq_pairCr -cpr_eq_pairAr.
  case/boolP : (`Pr[ [% W, [% Z, Y]] = (d, (c, b))] == 0) => [/eqP|] H0.
    rewrite [in X in _ * X = _ * X]cpr_eqE.
    by rewrite -pr_eq_pairA pr_eq_pairC -pr_eq_pairA H0 mul0r !mulr0.
  by rewrite (cinde_alt _ H1) // cpr_eq_pairCr.
case/boolP : (`Pr[ [% Y, Z] = (b, c) ] == 0) => [/eqP|] H0.
- rewrite [X in _ * X = _ * X]cpr_eqE.
  by rewrite pr_eq_pairAC pr_eq_domin_RV2 ?mul0r ?mulr0.
- by rewrite (cinde_alt _ H2).
Qed.

End contraction.

(* Probabilistic Reasoning in Intelligent Systems: Networks of Plausible Inference, Pearl, p.88 *)
Section derived_rules.

Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma chaining_rule : P |= X _|_ Z | Y /\ P |= [% X, Y] _|_ W | Z -> P |= X _|_ W | Y.
Proof.
case=> ? ?.
suff : P |= X _|_ [% W, Z] | Y by move/decomposition.
apply/cinde_drv_2C/contraction => //.
exact/cinde_drv_3C/symmetry/weak_union/symmetry.
Qed.

Lemma mixing_rule : P |= X _|_ [% Y, W] | Z /\ P |= Y _|_ W | Z -> P |= [% X, W] _|_ Y | Z.
Proof.
case=> ? ?.
apply/symmetry/cinde_drv_2C/contraction; last by [].
exact/symmetry/weak_union.
Qed.

End derived_rules.

Section intersection.

Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Hypothesis P0 : forall b c d, `Pr[ [% Y, Z, W] = (b, c, d) ] != 0.
Hypothesis D_not_empty : D.

Lemma intersection : P |= X _|_ Y | [% Z, W] -> P |= X _|_ W | [% Z, Y] -> P |= X _|_ [% Y, W] | Z.
Proof.
move=> H1 H2.
suff : P |= X _|_ Y | Z by apply contraction.
move=> a b c; apply/esym.
rewrite -[in X in X * _ = _]cpr_eq_set1 [in X in X * _ = _](creasoning_by_cases _ W).
under eq_bigr do rewrite setX1.
under eq_bigr do rewrite cpr_eq_set1.
rewrite big_distrl /=.
have <- : \sum_(d <- fin_img W)
           `Pr[ [% X, Y] = (a, b) | Z = c] * `Pr[ W = d | Z = c] =
         \sum_(d <- fin_img W)
           `Pr[ [% X, W] = (a, d) | Z = c] * `Pr[ Y = b | Z = c].
  suff H : forall d, `Pr[ [% X, Y] = (a, b) | Z = c] / `Pr[ Y = b | Z = c ] =
                `Pr[ [% X, W] = (a, d) | Z = c] / `Pr[ W = d | Z = c ].
    apply eq_bigr => d _.
    rewrite -eqr_divr_mulr; last first.
      rewrite cpr_eqE mulf_neq0 //.
      - by move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 W d) ->.
      - move: (P0 b c d); apply: contra.
        rewrite invr_eq0;  move/eqP/(pr_eq_domin_RV2 [% Y, W] (b, d)).
        by rewrite pr_eq_pairCA pr_eq_pairA => ->.
    rewrite mulrAC (H d) -mulrA mulVf ?mulr1 //.
    rewrite cpr_eqE mulf_eq0 negb_or invr_eq0 pr_eq_pairC; apply/andP; split.
    - move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 Y b).
      by rewrite pr_eq_pairC pr_eq_pairA pr_eq_pairAC => ->.
    - move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 [% Y, W] (b, d)).
      by rewrite pr_eq_pairCA -pr_eq_pairA => ->.
  suff H : forall d, `Pr[ X = a | [% Y, Z] = (b, c)] =
                `Pr[ X = a | [% W, Z] = (d, c)].
    move=> d.
    rewrite cpr_eq_product_rule (H d).
    rewrite [in RHS]cpr_eq_product_rule.
    rewrite -mulrA mulfV; last first.
      rewrite cpr_eqE mulf_eq0 negb_or invr_eq0; apply/andP; split.
      - by move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 W d) ->.
      - move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 [% Y, W] (b, d)).
        by rewrite pr_eq_pairCA -pr_eq_pairA => ->.
    rewrite -[in RHS]mulrA mulfV // cpr_eqE mulf_eq0 negb_or invr_eq0; apply/andP; split.
    - move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 Y b).
      by rewrite pr_eq_pairC pr_eq_pairA pr_eq_pairAC => ->.
    - move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 [% Y, W] (b, d)).
      by rewrite pr_eq_pairCA -pr_eq_pairA => ->.
  have {}H2 : forall d, `Pr[ X = a | [% Y, Z] = (b, c)] =
                     `Pr[ X = a | [% W, Z, Y] = (d, c, b)].
    move=> d; move: {H2}(H2 a d (c, b)).
    rewrite cpr_eq_product_rule.
    have H0 : `Pr[ W = d | [% Z, Y] = (c, b)] != 0.
      rewrite cpr_eqE pr_eq_pairA pr_eq_pairAC -pr_eq_pairA.
      rewrite pr_eq_pairC mulf_eq0 negb_or invr_eq0.
      apply/andP; split; first by rewrite pr_eq_pairC.
      by move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 W d) ->.
    move/mulIf => /(_ H0){H0}/esym.
    by rewrite (cpr_eq_pairCr X Z) cpr_eq_pairAr.
  have {}H1 : forall d, `Pr[ X = a | [% W, Z] = (d, c)] =
                     `Pr[ X = a | [% Y, W, Z] = (b, d, c)].
    move=> d; move: {H1}(H1 a b (c, d)).
    rewrite cpr_eq_product_rule.
    have H0 : `Pr[ Y = b | [% Z, W] = (c, d)] != 0.
      rewrite cpr_eqE pr_eq_pairA mulf_eq0 negb_or invr_eq0 P0 /=.
      move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 Y b).
      by rewrite pr_eq_pairC -pr_eq_pairA => ->.
    move/mulIf => /(_ H0){H0}/esym.
    by rewrite (cpr_eq_pairCr X Z) cpr_eq_pairAr cpr_eq_pairACr.
  by move=> d; rewrite {H2}(H2 d) {}H1 cpr_eq_pairCr cpr_eq_pairAr.
rewrite -big_distrr /=.
rewrite cPr_1 ?mulr1 //.
move: (P0 b c D_not_empty); apply: contra.
rewrite pr_eq_pairAC => /eqP/(pr_eq_domin_RV2 [% Y, W] (b, D_not_empty)).
by rewrite pr_eq_pairC => ->.
Qed.

End intersection.
