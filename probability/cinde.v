(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg matrix.
Require Import Reals.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop fdist.
Require Import proba jfdist.

(******************************************************************************)
(*   Conditional independence over joint distributions and graphoid axioms    *)
(*                                                                            *)
(*         X _|_  Y | Z == X is conditionally independent of Y given Z in the *)
(*                      distribution P for all values a, b, and c (belonging  *)
(*                      resp. to the codomains of X, Y , and Z); equivalent   *)
(*                      to P |= X _|_ Y | Z from proba.v                      *)
(* \Pr[ X = a | Y = b ] == probability that the random variable X is a        *)
(*                         knowing that the random variable Y is b            *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*  Graphoid axioms: symmetry, decomposition, weak_union, contraction,        *)
(*  intersection, derived rules                                               *)
(******************************************************************************)

(*
contents:
- Various distributions (Proj124.d, Proj14d, QuadA23.d)
- Section pair_of_RVs.
- Section RV2_prop.
- Section RV3_prop.
- Section conditionnally_independent_discrete_random_variables.
*)

Reserved Notation "X _|_  Y | Z" (at level 50, Y, Z at next level).
Reserved Notation "\Pr[ X '\in' E | Y '\in' F ]" (at level 6, X, Y, E, F at next level,
  format "\Pr[  X  '\in'  E  |  Y  '\in'  F  ]").
Reserved Notation "\Pr[ X '\in' E | Y = b ]" (at level 6, X, Y, E, b at next level,
  format "\Pr[  X  '\in'  E  |  Y  =  b  ]").
Reserved Notation "\Pr[ X = a | Y '\in' F ]" (at level 6, X, Y, a, F at next level,
  format "\Pr[  X  =  a  |  Y  '\in'  F  ]").
Reserved Notation "\Pr[ X = a | Y = b ]" (at level 6, X, Y, a, b at next level,
  format "\Pr[  X  =  a  |  Y  =  b  ]").

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.
Local Open Scope proba_scope.

Module Proj124.
Section proj124.
Variables (A B D C : finType) (P : {fdist A * B * D * C}).
Definition d : {fdist A * B * C} :=
  Swap.d (Bivar.snd (TripA.d (Swap.d (TripA.d P)))).
Lemma dE abc : d abc = \sum_(x in D) P (abc.1.1, abc.1.2, x, abc.2).
Proof.
case: abc => [[a b] c] /=.
rewrite /d Swap.dE Bivar.sndE; apply eq_bigr => d _.
by rewrite TripA.dE /= Swap.dE TripA.dE.
Qed.
Lemma snd : Bivar.snd d = Bivar.snd P.
Proof. by rewrite /Bivar.snd /d !FDistMap.comp. Qed.
End proj124.
End Proj124.

Definition Proj14d (A B C D : finType) (d : {fdist A * B * D * C}) : {fdist A * C} :=
  Proj13.d (Proj124.d d).

Module QuadA23.
Section def.
Variables (A B C D : finType) (P : {fdist A * B * D * C}).
Definition f (x : A * B * D * C) : A * (B * D) * C :=
  (x.1.1.1, (x.1.1.2, x.1.2), x.2).
Lemma inj_f : injective f.
Proof. by rewrite /f => -[[[? ?] ?] ?] [[[? ?] ?] ?] /= [-> -> -> ->]. Qed.
Definition d : {fdist A * (B * D) * C} := FDistMap.d f P.
Lemma dE x : d x = P (x.1.1, x.1.2.1, x.1.2.2, x.2).
Proof.
case: x => -[a [b d] c]; rewrite /def.d FDistMap.dE /= -/(f (a, b, d, c)).
by rewrite (big_pred1_inj inj_f).
Qed.
End def.
Section prop.
Variables (A B C D : finType) (P : {fdist A * B * D * C}).
Lemma snd : Bivar.snd (QuadA23.d P) = Bivar.snd P.
Proof. by rewrite /Bivar.snd /d FDistMap.comp. Qed.
End prop.
End QuadA23.

Notation "\Pr[ X '\in' E | Y '\in' F ]" := (\Pr_(`d_[% X, Y])[ E | F ]).
Notation "\Pr[ X '\in' E | Y = b ]" := (\Pr[ X \in E | Y \in [set b]]).
Notation "\Pr[ X = a | Y '\in' F ]" := (\Pr[ X \in [set a] | Y \in F]).
Notation "\Pr[ X = a | Y = b ]" := (\Pr[ X \in [set a] | Y \in [set b]]).

Section RV2_prop.
Variables (U : finType) (P : fdist U).
Variables (A B : finType) (X : {RV P -> A}) (Y : {RV P -> B}).
Implicit Types (E : {set A}) (F : {set B}).

Goal forall a b, \Pr[ X = a | Y = b ] = \Pr_(FDistMap.d [% X, Y] P)[ [set a] | [set b] ].
by [].
Abort.

Lemma RV20 : fst \o [% X, unit_RV P] =1 X.
Proof. by []. Qed.

Lemma RV02 : snd \o [% unit_RV P, X] =1 X.
Proof. by []. Qed.

End RV2_prop.

Section RV3_prop.
Variables (U : finType) (P : fdist U).
Variables (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma Proj13_RV3 : Proj13.d `d_[% X, Y, Z] = `d_[% X, Z].
Proof.
by rewrite /Proj13.d /Bivar.snd /TripA.d /dist_of_RV /TripC12.d !FDistMap.comp.
Qed.

Lemma snd_RV3 : Bivar.snd `d_[% X, Y, Z] = Bivar.snd `d_[% X, Z].
Proof. by rewrite -Proj13.snd Proj13_RV3. Qed.

Lemma TripC12_RV3 : TripC12.d `d_[% X, Y, Z] = `d_[% Y, X, Z].
Proof. by rewrite /TripC12.d /dist_of_RV FDistMap.comp. Qed.

Lemma TripA_RV3 : TripA.d `d_[% X, Y, Z] = `d_[% X, [% Y, Z]].
Proof. by rewrite /TripC12.d /dist_of_RV /TripA.d FDistMap.comp. Qed.

End RV3_prop.

(* TODO: move *)
Section setX_structural_lemmas.
Variables (A B C : finType).
Variables (E : {set A}) (F : {set B}).

Lemma imset_fst b : b \in F -> [set x.1 | x in E `* F] = E.
Proof.
move=> bF; apply/setP => a; apply/imsetP/idP.
- by rewrite ex2C; move=> -[[a' b']] /= ->; rewrite inE => /andP [] ->.
- by move=> aE; exists (a, b); rewrite // inE; apply/andP; split.
Qed.

End setX_structural_lemmas.

Section conditionnally_independent_discrete_random_variables.

Variables (U : finType) (P : fdist U) (A B C : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).

Definition jcinde_rv := forall a b c,
  \Pr[ [% X, Y] = (a, b) | Z = c ] = \Pr[ X = a | Z = c ] * \Pr[ Y = b | Z = c].

End conditionnally_independent_discrete_random_variables.

Notation "X _|_  Y | Z" := (jcinde_rv X Y Z) : proba_scope.

Section cinde_rv_prop.

Variables (U : finType) (P : fdist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma jcinde_cinde_rv : X _|_ Y | Z <-> P |= X _|_ Y | Z.
Proof.
split; rewrite /jcinde_rv /cinde_rv; by
  move=> H a b c; have {H} := H a b c; rewrite 3!jcPrE -!cpr_inE' !cpr_eq_set1.
Qed.

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

Variable (U : finType) (P : fdist U).
Variables (A B C : finType) (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).

Lemma symmetry : P |= X _|_ Y | Z -> P |= Y _|_ X | Z.
Proof.
move=> H b a c.
rewrite /cinde_rv in H.
rewrite cpr_eq_pairC.
rewrite H.
by rewrite mulRC.
Qed.

End symmetry.

Section decomposition.

Variables (U : finType) (P : fdist U) (A B C D : finType).
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

Variables (U : finType) (P : fdist U) (A B C D : finType).
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
  - by rewrite [X in _ * X = _ * X]cpr_eqE pr_eq_pairA pr_eq_pairAC H0 div0R !mulR0.
  - by rewrite (cinde_alt _ H).
case/boolP : (`Pr[ [% Z, W] = (c, d) ] == 0) => [/eqP|] ?.
- by rewrite [X in _ * X = _ * X]cpr_eqE (pr_eq_pairC _ Y) (pr_eq_domin_RV2 Y) ?(div0R,mulR0).
- have {}H : P |= X _|_ W | Z by move/cinde_drv_2C : H; apply decomposition.
  by rewrite [in X in _ = X * _]cpr_eq_pairCr (cinde_alt _ H) // pr_eq_pairC.
Qed.

End weak_union.

Section contraction.

Variables (U : finType) (P : fdist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma contraction : P |= X _|_ W | [% Z, Y] -> P |= X _|_ Y | Z -> P |= X _|_ [% Y, W] | Z.
Proof.
move=> H1 H2 a [b d] c.
rewrite cpr_eq_product_rule.
transitivity (`Pr[X = a | [% Y, Z] = (b, c)] * `Pr[[% Y, W] = (b, d) | Z = c]).
  rewrite -cpr_eq_pairAr [in X in X * _ = _]cpr_eq_pairCr -cpr_eq_pairAr.
  case/boolP : (`Pr[ [% W, [% Z, Y]] = (d, (c, b))] == 0) => [/eqP|] H0.
    rewrite [in X in _ * X = _ * X]cpr_eqE.
    by rewrite -pr_eq_pairA pr_eq_pairC -pr_eq_pairA H0 div0R !mulR0.
  by rewrite (cinde_alt _ H1) // cpr_eq_pairCr.
case/boolP : (`Pr[ [% Y, Z] = (b, c) ] == 0) => [/eqP|] H0.
- rewrite [X in _ * X = _ * X]cpr_eqE.
  by rewrite pr_eq_pairAC pr_eq_domin_RV2 ?div0R ?mulR0.
- by rewrite (cinde_alt _ H2).
Qed.

End contraction.

(* Probabilistic Reasoning in Intelligent Systems: Networks of Plausible Inference, Pearl, p.88 *)
Section derived_rules.

Variables (U : finType) (P : fdist U) (A B C D : finType).
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

Variables (U : finType) (P : fdist U) (A B C D : finType).
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
    rewrite -eqR_divr_mulr; last first.
      rewrite cpr_eqE divR_neq0' //.
      - by move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 W d) ->.
      - move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 [% Y, W] (b, d)).
        by rewrite pr_eq_pairCA pr_eq_pairA => ->.
    rewrite {1}/Rdiv mulRAC -/(Rdiv _ _) (H d) mulRAC eqR_divr_mulr //.
    rewrite cpr_eqE divR_neq0' //.
    - move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 Y b).
      by rewrite pr_eq_pairC pr_eq_pairA pr_eq_pairAC => ->.
    - move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 [% Y, W] (b, d)).
      by rewrite pr_eq_pairCA -pr_eq_pairA => ->.
  suff H : forall d, `Pr[ X = a | [% Y, Z] = (b, c)] =
                `Pr[ X = a | [% W, Z] = (d, c)].
    move=> d.
    rewrite cpr_eq_product_rule (H d).
    rewrite [in RHS]cpr_eq_product_rule.
    rewrite {1}/Rdiv -mulRA mulRV; last first.
      rewrite cpr_eqE divR_neq0' //.
      - by move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 W d) ->.
      - move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 [% Y, W] (b, d)).
        by rewrite pr_eq_pairCA -pr_eq_pairA => ->.
    rewrite {1}/Rdiv -[in RHS]mulRA mulRV // cpr_eqE divR_neq0' //.
    - move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 Y b).
      by rewrite pr_eq_pairC pr_eq_pairA pr_eq_pairAC => ->.
    - move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 [% Y, W] (b, d)).
      by rewrite pr_eq_pairCA -pr_eq_pairA => ->.
  have {}H2 : forall d, `Pr[ X = a | [% Y, Z] = (b, c)] =
                     `Pr[ X = a | [% W, Z, Y] = (d, c, b)].
    move=> d; move: {H2}(H2 a d (c, b)).
    rewrite cpr_eq_product_rule.
    have /eqP H0 : `Pr[ W = d | [% Z, Y] = (c, b)] != 0.
      rewrite cpr_eqE pr_eq_pairA pr_eq_pairAC -pr_eq_pairA.
      rewrite pr_eq_pairC divR_neq0' //; first by rewrite pr_eq_pairC.
      by move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 W d) ->.
    move/eqR_mul2r => /(_ H0){H0}/esym.
    by rewrite [in LHS]cpr_eq_pairCr cpr_eq_pairAr.
  have {}H1 : forall d, `Pr[ X = a | [% W, Z] = (d, c)] =
                     `Pr[ X = a | [% Y, W, Z] = (b, d, c)].
    move=> d; move: {H1}(H1 a b (c, d)).
    rewrite cpr_eq_product_rule.
    have /eqP H0 : `Pr[ Y = b | [% Z, W] = (c, d)] != 0.
      rewrite cpr_eqE pr_eq_pairA divR_neq0' //.
      move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 Y b).
      by rewrite pr_eq_pairC -pr_eq_pairA => ->.
    move/eqR_mul2r => /(_ H0){H0}/esym.
    by rewrite [in LHS]cpr_eq_pairCr cpr_eq_pairAr cpr_eq_pairACr.
  by move=> d; rewrite {H2}(H2 d) {}H1 cpr_eq_pairCr cpr_eq_pairAr.
rewrite -big_distrr /=.
rewrite cPr_1 ?mulR1 //.
move: (P0 b c D_not_empty); apply: contra.
rewrite pr_eq_pairAC => /eqP/(pr_eq_domin_RV2 [% Y, W] (b, D_not_empty)).
by rewrite pr_eq_pairC => ->.
Qed.

End intersection.

(* wip*)

Section vector_of_RVs.
Variables (U : finType) (P : fdist U).
Variables (A : finType) (n : nat) (X : 'rV[{RV P -> A}]_n).
Local Open Scope ring_scope.
Local Open Scope vec_ext_scope.
Definition RVn : {RV P -> 'rV[A]_n} := fun x => \row_(i < n) (X ``_ i) x.
End vector_of_RVs.

Section prob_chain_rule.
Variables (U : finType) (P : {fdist U}).
Variables (A : finType) .
Local Open Scope vec_ext_scope.
Lemma prob_chain_rule : forall (n : nat) (X : 'rV[{RV P -> A}]_n.+1) x,
  `Pr[ (RVn X) = x ] =
  \prod_(i < n.+1)
    if i == ord0 then
      `Pr[ (X ``_ ord0) = (x ``_ ord0)   ]
    else
      \Pr[ (X ``_ i) = (x ``_ i) |
        (RVn (row_drop (inord (n - i.+1)) X)) = (row_drop (inord (n - i.+1)) x) ].
Proof.
elim => [X /= x|n ih X /= x].
  rewrite big_ord_recl big_ord0 mulR1.
  rewrite /pr_eq; unlock.
  apply eq_bigl => u.
  rewrite !inE /RVn.
  apply/eqP/eqP => [<-|H]; first by rewrite mxE.
  by apply/rowP => i; rewrite {}(ord1 i) !mxE.
rewrite big_ord_recr /=.
Abort.

End prob_chain_rule.
