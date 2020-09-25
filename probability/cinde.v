(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg matrix.
Require Import Reals.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop fdist.
Require Import proba jfdist.

(******************************************************************************)
(*   Conditional independence over joint distributions and graphoid axioms    *)
(*                                                                            *)
(* P |= X _|_  Y | Z == X is conditionally independent of Y given Z in the    *)
(*                      distribution P for all values a, b, and c (belonging  *)
(*                      resp. to the codomains of X, Y , and Z); equivalent   *)
(*                      to P `= X _|_ Y | Z from proba.v                      *)
(* \Pr[ X = a | Y = b ] == probability that the random variable X is a        *)
(*                         knowing that the random variable Y is b            *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*  Graphoid axioms: symmetry, decomposition, weak_union, contraction,        *)
(*  intersection                                                              *)
(******************************************************************************)

(*
contents:
- Various distributions (Proj124.d, Proj14d, QuadA23.d)
- Section pair_of_RVs.
- Section RV2_prop.
- Section RV3_prop.
- Section marginals.
- Section RV_domin.
- Section cPr_1_RV.
- Section reasoning_by_cases.
- Section conditionnally_independent_discrete_random_variables.
- Section cinde_drv_prop.
- Section symmetry.
- Section decomposition.
- Section weak_union.
- Section contraction.
- Section derived_rules.
- Section intersection.
*)

Reserved Notation "X _|_  Y | Z" (at level 10, Y, Z at next level).
Reserved Notation "P |= X _|_  Y | Z" (at level 10, X, Y, Z at next level).
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

Lemma Swap_RV2 : Swap.d `d_[% X, Y] = `d_[% Y, X].
Proof. by rewrite /Swap.d /dist_of_RV FDistMap.comp. Qed.

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

Section more_structural_lemmas_on_RV.

Lemma RV_jcPrE_set
  (U : finType) (P : fdist U) (B C : finType)
  (Y : {RV P -> B}) (Z : {RV P -> C}) (E : {set B}) (F : {set C}) :
  \Pr[ Y \in E | Z \in F ] = `Pr[ [% Y, Z] \in E `* F] / `Pr[ Z \in F ].
Proof.
by rewrite jcPrE -cpr_inE' cpr_inE.
Qed.

Lemma RV_jcPrE
  (U : finType) (P : fdist U) (B C : finType)
  (Y : {RV P -> B}) (Z : {RV P -> C}) b c :
  \Pr[ Y = b | Z = c ] = `Pr[ [% Y, Z] = (b, c) ] / `Pr[ Z = c ].
Proof.
by rewrite RV_jcPrE_set // pr_eq_set1 setX1 pr_eq_set1.
Qed.

Lemma RV_Pr_jcPr_unit_set (U : finType) (P : fdist U) (A : finType)
  (X : {RV P -> A}) E :
  `Pr[ X \in E ] = \Pr[ X \in E | (unit_RV P) = tt ].
Proof.
(*rewrite RV_jcPrE_set.*)
rewrite jcPrE.
rewrite setTE.
rewrite setTX.
rewrite cPrET.
rewrite pr_eq_setE.
rewrite /ambient_dist.
rewrite /dist_of_RV.
rewrite EsetT.
rewrite Pr_FDistMap_RV2.
congr Pr.
by apply/setP => u; rewrite !inE andbT.
Qed.

Lemma RV_Pr_jcPr_unit (U : finType) (P : fdist U) (A : finType)
  (X : {RV P -> A}) a :
  `Pr[ X = a ] = \Pr[ X = a | (unit_RV P) = tt ].
Proof.
by rewrite -RV_Pr_jcPr_unit_set pr_eq_set1.
Qed.

Lemma RV_set_product_rule
  (U : finType) (P : fdist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) E F G :
  \Pr[ [% X, Y] \in E `* F | Z \in G ] =
  \Pr[ X \in E | [% Y, Z] \in F `* G ] * \Pr[ Y \in F | Z \in G ].
Proof.
rewrite jproduct_rule_cond; congr (\Pr_ _ [_ | _] * _).
- by rewrite TripA_RV3.
- congr (\Pr_ _ [_ | _]); by rewrite /Proj23.d TripA_RV3 snd_RV2.
Qed.

(* TODO: move *)
Lemma RV_product_rule
  (U : finType) (P : fdist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) a b c :
  \Pr[ [% X, Y] = (a, b) | Z = c ] =
  \Pr[ X = a | [% Y, Z] = (b, c) ] * \Pr[ Y = b | Z = c ].
Proof.
rewrite -setX1 jproduct_rule_cond; congr (\Pr_ _ [_ | _] * _).
- by rewrite TripA_RV3.
- by rewrite setX1.
- congr (\Pr_ _ [_ | _]); by rewrite /Proj23.d TripA_RV3 snd_RV2.
Qed.

Lemma RV_Pr_lC (U : finType) (P : fdist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) a b G :
  \Pr[ [% Y, X] = (b, a) | Z \in G ] = \Pr[ [% X, Y] = (a, b) | Z \in G ].
Proof. by rewrite -setX1 -jcPr_TripC12 TripC12_RV3 setX1. Qed.

Lemma RV_Pr_lC_set (U : finType) (P : fdist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) E F G :
  \Pr[ [% Y, X] \in F `* E | Z \in G ] = \Pr[ [% X, Y] \in E `* F | Z \in G ].
Proof. by rewrite -jcPr_TripC12 TripC12_RV3. Qed.

Lemma RV_Pr_lA_set (U : finType) (P : fdist U) (A B C D : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}) E F G H:
  \Pr[ [% X, [% Y, Z]] \in E `* (F `* G) | W \in H] =
  \Pr[ [% [% X, Y], Z] \in (E `* F) `* G | W \in H].
Proof. by rewrite (Pr_FDistMap_l TripA.inj_f) TripA.imset FDistMap.comp. Qed.

Lemma RV_Pr_lA (U : finType) (P : fdist U) (A B C D : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}) a b c H:
  \Pr[ [% X, [% Y, Z]] = (a, (b, c)) | W \in H] =
  \Pr[ [% [% X, Y], Z] = ((a, b), c) | W \in H].
Proof. by rewrite -!setX1 RV_Pr_lA_set. Qed.

Lemma RV_Pr_rsetXunit (U : finType) (P : fdist U) (A B : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) E F :
  \Pr[ X \in E | [% Y, unit_RV P] \in F `* [set tt] ]
  = \Pr[ X \in E | Y \in F ].
Proof.
congr (_ / _).
- by rewrite -!pr_inE' pr_in_pairA -EsetT pr_eq_pair_setT.
- by rewrite !snd_RV2 -!pr_inE' -EsetT pr_eq_pair_setT.
Qed.

Lemma RV2_Pr_lcongr (U : finType) (P : fdist U) (A A' B B' C : finType)
  (X : {RV P -> A}) (X' : {RV P -> A'}) (Y : {RV P -> B}) (Y' : {RV P -> B'})
  (Z : {RV P -> C}) E E' F F' G :
  \Pr[ X \in E | [% Y, Z] \in F `* G] = \Pr[ X' \in E' | [% Y, Z] \in F `* G] ->
  \Pr[ Y \in F | [% X', Z] \in E' `* G] = \Pr[ Y' \in F' | [% X', Z] \in E' `* G] ->
  \Pr[ [% X, Y] \in E `* F | Z \in G ] = \Pr[ [% X', Y'] \in E' `* F' | Z \in G ].
Proof.
move=> EE' FF'.
transitivity \Pr[ [% X', Y] \in E' `* F | Z \in G ];
  first by rewrite !RV_set_product_rule EE'.
rewrite [in LHS]RV_Pr_lC_set [in RHS]RV_Pr_lC_set.
by rewrite !RV_set_product_rule FF'.
Qed.

Lemma RV2_Pr_lcongr' (U : finType) (P : fdist U) (A A' B B' C : finType)
  (X : {RV P -> A}) (X' : {RV P -> A'}) (Y : {RV P -> B}) (Y' : {RV P -> B'})
  (Z : {RV P -> C}) E E' F F' G :
  \Pr[ X \in E | [% Y', Z] \in F' `* G ] = \Pr[ X' \in E' | [% Y', Z] \in F' `* G ] ->
  \Pr[ Y \in F | [% X, Z] \in E `* G ] = \Pr[ Y' \in F' | [% X, Z] \in E `* G] ->
  \Pr[ [% X, Y] \in E `* F | Z \in G ] = \Pr[ [% X', Y'] \in E' `* F' | Z \in G].
Proof.
move=> EE' FF'.
transitivity \Pr[ [% X, Y'] \in E `* F' | Z \in G ];
  last by rewrite !RV_set_product_rule EE'.
rewrite [in LHS]RV_Pr_lC_set [in RHS]RV_Pr_lC_set.
by rewrite !RV_set_product_rule FF'.
Qed.

Lemma RV2_Pr_congr (U : finType) (P : fdist U) (A A' B B' : finType)
  (X : {RV P -> A}) (X' : {RV P -> A'}) (Y : {RV P -> B}) (Y' : {RV P -> B'})
  E E' F F' :
  \Pr[ X \in E | Y \in F ] = \Pr[ X' \in E' | Y \in F ] ->
  \Pr[ Y \in F | X' \in E' ] = \Pr[ Y' \in F' | X' \in E' ] ->
  `Pr[ [% X, Y] \in E `* F] = `Pr[ [% X', Y'] \in E' `* F'].
Proof.
move=> EE' FF'.
rewrite !RV_Pr_jcPr_unit_set.
apply RV2_Pr_lcongr; by rewrite !RV_Pr_rsetXunit.
Qed.

Lemma RV2_Pr_congr' (U : finType) (P : fdist U) (A A' B B' : finType)
  (X : {RV P -> A}) (X' : {RV P -> A'}) (Y : {RV P -> B}) (Y' : {RV P -> B'})
  E E' F F' :
  \Pr[ X \in E | Y' \in F' ] = \Pr[ X' \in E' | Y' \in F' ] ->
  \Pr[ Y \in F | X \in E ] = \Pr[ Y' \in F' | X \in E ] ->
  `Pr[ [% X, Y] \in E `* F] = `Pr[ [% X', Y'] \in E' `* F'].
Proof.
move=> EE' FF'.
rewrite !RV_Pr_jcPr_unit_set.
apply RV2_Pr_lcongr'; by rewrite !RV_Pr_rsetXunit.
Qed.

Lemma RV_Pr_lAC_set (U : finType) (P : fdist U) (A B C D : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}) E F G H:
  \Pr[ [% X, Y, Z] \in (E `* F) `* G | W \in H] =
  \Pr[ [% X, Z, Y] \in (E `* G) `* F | W \in H].
Proof.
rewrite -!RV_Pr_lA_set; apply RV2_Pr_lcongr => //; exact: RV_Pr_lC_set.
(* by rewrite (Pr_FDistMap_l TripC23.inj_f) imset_TripC23_f FDistMap.comp. *)
Qed.

Lemma RV_Pr_lAC (U : finType) (P : fdist U) (A B C D : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}) a b c H:
  \Pr[ [% X, Y, Z] = (a, b, c) | W \in H] =
  \Pr[ [% X, Z, Y] = (a, c, b) | W \in H].
Proof. by rewrite -!setX1 RV_Pr_lAC_set. Qed.

Lemma RV_Pr_lCA_set (U : finType) (P : fdist U) (A B C D : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}) E F G H:
  \Pr[ [% X, [% Y, Z]] \in E `* (F `* G) | W \in H] =
  \Pr[ [% X, [% Z, Y]] \in E `* (G `* F) | W \in H].
Proof. by rewrite RV_Pr_lA_set  RV_Pr_lAC_set -RV_Pr_lA_set. Qed.

Lemma RV_Pr_lCA (U : finType) (P : fdist U) (A B C D : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}) a b c H:
  \Pr[ [% X, [% Y, Z]] = (a, (b, c)) | W \in H] =
  \Pr[ [% X, [% Z, Y]] = (a, (c, b)) | W \in H].
Proof. by rewrite -!setX1 RV_Pr_lCA_set. Qed.

Lemma RV_Pr_rA (U : finType) (P : fdist U) (A B C D : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}) E b c d :
  \Pr[ X \in E | [% Y, [% Z, W]] = (b, (c, d)) ] =
  \Pr[ X \in E | [% Y, Z, W] = (b, c, d) ].
Proof.
by rewrite (Pr_FDistMap_r TripA.inj_f) /= !FDistMap.comp imset_set1.
Qed.

Lemma RV_Pr_rAC (U : finType) (P : fdist U) (A B C D : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}) E b c d :
  \Pr[ X \in E | [% Y, Z, W] = (b, c, d) ] =
  \Pr[ X \in E | [% Y, W, Z] = (b, d, c) ].
Proof.
by rewrite (Pr_FDistMap_r TripAC.inj_f) /= !FDistMap.comp imset_set1.
Qed.

Lemma RV_Pr_rCA (U : finType) (P : fdist U) (A B C D : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}) E b c d :
  \Pr[ X \in E | [% Y, [% Z, W]] = (b, (c, d)) ] =
  \Pr[ X \in E | [% Y, [% W, Z]] = (b, (d, c)) ].
Proof.
rewrite (Pr_FDistMap_r (inj_comp TripA.inj_f (inj_comp TripAC.inj_f TripA'.inj_f))).
by rewrite /= !FDistMap.comp // !imset_set1.
Qed.

Lemma RV_Pr_rC (U : finType) (P : fdist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) E b c :
  \Pr[ X \in E | [% Y, Z] = (b, c) ] =
  \Pr[ X \in E | [% Z, Y] = (c, b) ].
Proof.
by rewrite (Pr_FDistMap_r (bij_inj bij_swap)) !FDistMap.comp imset_set1.
Qed.

End more_structural_lemmas_on_RV.

Section Pr_jcPr_domin.
Lemma Pr_jcPr_domin (A B : finType) (P : {fdist A * B})
      (E : {set A}) (F : {set B}) :
  Pr (Bivar.snd P) F <> 0 ->
  Pr (Bivar.fst P) E = 0 -> \Pr_P[ E | F ] = 0.
Proof.
move=> Fn0 E0.
rewrite /jcPr.
rewrite -(eqR_mul2r Fn0) mul0R -mulRA mulVR; last by move/eqP:Fn0.
rewrite mulR1; by apply Pr_domin_setX.
Qed.
End Pr_jcPr_domin.

Section RV_domin.
Variables (U : finType) (P : fdist U) (A B : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}).

Lemma RV_Pr_jcPr_domin_set E F :
  `Pr[ Y \in F ] <> 0 -> `Pr[ X \in E ] = 0 -> \Pr[ X \in E | Y \in F ] = 0.
Proof.
move=> YF XE.
by apply Pr_jcPr_domin; [rewrite snd_RV2 -pr_inE' | rewrite fst_RV2 -pr_inE'].
Qed.

End RV_domin.

Section jcPr_1_RV.

Variables (U : finType) (P : fdist U) (A B : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}).

Lemma cPr_1 a : `Pr[X = a] != 0 ->
  \sum_(b <- fin_img Y) `Pr[ Y = b | X = a ] = 1.
Proof.
rewrite -pr_eq_set1 pr_inE' Pr_set1 -{1}(fst_RV2 _ Y) => Xa0.
set Q := `d_[% X, Y] `(| a ).
rewrite -(FDist.f1 Q) [in RHS](bigID (mem (fin_img Y))) /=.
rewrite [X in _ = _ + X](eq_bigr (fun=> 0)); last first.
  move=> b bY.
  rewrite /Q CondJFDist.dE // /jcPr /Pr !(big_setX,big_set1) /= Swap.dE Swap.snd fst_RV2.
  rewrite -!pr_eqE' !pr_eqE.
  rewrite /Pr big1 ?div0R // => u.
  rewrite inE => /eqP[Yub ?].
  exfalso.
  move/negP : bY; apply.
  rewrite mem_undup; apply/mapP; exists u => //; by rewrite mem_enum.
rewrite big_const iter_addR mulR0 addR0.
rewrite big_uniq; last by rewrite /fin_img undup_uniq.
apply eq_bigr => b; rewrite mem_undup => /mapP[u _ bWu].
rewrite /Q CondJFDist.dE // Swap_RV2.
rewrite jcPrE -cpr_inE'.
by rewrite cpr_eq_set1.
Qed.

(* NB: see also cPr_1 *)
Lemma jcPr_1_RV a : `Pr[X = a] != 0 ->
  \sum_(b <- fin_img Y) \Pr[ Y = b | X = a ] = 1.
Proof.
move/cPr_1 => <-.
apply/eq_bigr => b _.
by rewrite jcPrE -cpr_inE' cpr_eq_set1.
Qed.

End jcPr_1_RV.

Lemma jcreasoning_by_cases (U : finType) (P : fdist U)
  (A B C : finType) (Z : {RV P -> C}) (X : {RV P -> A}) (Y : {RV P -> B}) E F :
  \Pr[ X \in E | Y \in F ] = \sum_(z <- fin_img Z) \Pr[ [% X, Z] \in E `* [set z] | Y \in F ].
Proof.
rewrite jcPrE -cpr_inE' (creasoning_by_cases _ Z) //.
by apply eq_bigr => c _; rewrite jcPrE -cpr_inE'.
Qed.

Section conditionnally_independent_discrete_random_variables.

Variables (U : finType) (P : fdist U) (A B C : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).

Definition jcinde_rv := forall a b c,
  \Pr[ [% X, Y] = (a, b) | Z = c ] = \Pr[ X = a | Z = c ] * \Pr[ Y = b | Z = c].

End conditionnally_independent_discrete_random_variables.

Notation "X _|_  Y | Z" := (jcinde_rv X Y Z) : proba_scope.
Notation "P |= X _|_  Y | Z" := (@jcinde_rv _ P _ _ _ X Y Z) : proba_scope.

Lemma cinde_alt (U : finType) (P : {fdist U}) (A B C : finType) (X : {RV P -> A}) (Y : {RV P -> B}) {Z : {RV P -> C}} a b c :
  P |= X _|_ Y | Z ->
  `Pr[ [% Y, Z] = (b, c)] != 0 ->
  \Pr[ X = a | [% Y, Z] = (b, c)] = \Pr[X = a | Z = c].
Proof.
move=> K /eqP H0.
rewrite [in LHS]RV_jcPrE -(eqR_mul2r H0) -mulRA mulVR ?mulR1; last by apply/eqP.
have H1 : /(`Pr[ Z = c ]) <> 0.
  by apply invR_neq0; rewrite pr_eq_pairC in H0; move/(pr_eq_domin_RV2 Y b).
by rewrite -pr_eq_pairA -(eqR_mul2r H1) -mulRA -!divRE -!RV_jcPrE K.
Qed.

Section cinde_rv_prop.

Variables (U : finType) (P : fdist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma jcinde_cinde_rv : P |= X _|_ Y | Z <-> P `= X _|_ Y | Z.
Proof.
split; rewrite /jcinde_rv /cinde_rv; by
  move=> H a b c; have {H} := H a b c; rewrite 3!jcPrE -!cpr_inE' !cpr_eq_set1.
Qed.

Lemma cinde_drv_2C : X _|_ [% Y, W] | Z -> P |= X _|_ [% W, Y] | Z.
Proof.
move=> H a -[d b] c.
by rewrite RV_Pr_lA RV_Pr_lAC -RV_Pr_lA H RV_Pr_lC.
Qed.

Lemma cinde_drv_3C : X _|_ Y | [% Z, W] -> X _|_ Y | [% W, Z].
Proof.
move=> H; move=> a b -[d c]; move: (H a b (c, d)) => {}H.
by rewrite RV_Pr_rC H RV_Pr_rC; congr (_ * _); rewrite RV_Pr_rC.
Qed.

End cinde_rv_prop.

Section symmetry.

Variable (U : finType) (P : fdist U).
Variables (A B C : finType) (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).

Lemma symmetry : X _|_ Y | Z -> Y _|_ X | Z.
Proof.
move=> H b a c.
rewrite /jcinde_rv in H.
rewrite RV_Pr_lC.
rewrite H.
by rewrite mulRC.
Qed.

End symmetry.

Section decomposition.

Variables (U : finType) (P : fdist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma decomposition : X _|_ [% Y, W] | Z -> X _|_ Y | Z.
Proof.
move=> H a b c.
transitivity (\sum_(d <- fin_img W) \Pr[ [% X, [% Y, W]] = (a, (b, d)) | Z = c]).
  rewrite (jcreasoning_by_cases W); apply eq_bigr => /= d _.
  by rewrite RV_Pr_lA setX1.
transitivity (\sum_(d <- fin_img W)
  \Pr[ X = a | Z = c] * \Pr[ [% Y, W] = (b, d) | Z = c]).
  by apply eq_bigr => d _; rewrite H.
rewrite -big_distrr /=; congr (_ * _).
rewrite (jcreasoning_by_cases W); apply eq_bigr => d _.
by rewrite setX1.
Qed.

End decomposition.

Section weak_union.

Variables (U : finType) (P : fdist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma weak_union : X _|_ [% Y, W] | Z -> X _|_ Y | [% Z, W].
Proof.
move=> H a b [c d].
transitivity (\Pr[ X = a | [% Y, Z, W] = (b, c, d)] *
  \Pr[ Y = b | [% Z, W] = (c, d)]).
  by rewrite RV_product_rule RV_Pr_rA.
transitivity (\Pr[ X = a | Z = c] * \Pr[ Y = b | [% Z, W] = (c, d)]).
  rewrite RV_Pr_rAC.
  case/boolP : (`Pr[ [% Y, W, Z] = (b, d, c)] == 0) => [/eqP|] H0.
  - by rewrite [X in _ * X = _ * X]RV_jcPrE -pr_eq_pairA pr_eq_pairAC H0 div0R !mulR0.
  - by rewrite (cinde_alt _ H).
case/boolP : (`Pr[ [% Z, W] = (c, d) ] == 0) => [/eqP|] ?.
- by rewrite [X in _ * X = _ * X]RV_jcPrE pr_eq_pairC pr_eq_domin_RV2 ?(div0R,mulR0).
- have {}H : X _|_ W | Z by move/cinde_drv_2C : H; apply decomposition.
  by rewrite [in X in _ = X * _]RV_Pr_rC (cinde_alt _ H) // pr_eq_pairC.
Qed.

End weak_union.

Section contraction.

Variables (U : finType) (P : fdist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma contraction : X _|_ W | [% Z, Y] -> X _|_ Y | Z -> X _|_ [% Y, W] | Z.
Proof.
move=> H1 H2 a [b d] c.
rewrite RV_product_rule.
transitivity (\Pr[X = a | [% Y, Z] = (b, c)] * \Pr[[% Y, W] = (b, d) | Z = c]).
  rewrite -RV_Pr_rA [in X in X * _ = _]RV_Pr_rC -RV_Pr_rA.
  case/boolP : (`Pr[ [% W, [% Z, Y]] = (d, (c, b))] == 0) => [/eqP|] H0.
    rewrite [in X in _ * X = _ * X]RV_jcPrE.
    by rewrite pr_eq_pairA pr_eq_pairC pr_eq_pairA H0 div0R !mulR0.
  by rewrite (cinde_alt _ H1) // RV_Pr_rC.
case/boolP : (`Pr[ [% Y, Z] = (b, c) ] == 0) => [/eqP|] H0.
- rewrite [X in _ * X = _ * X]RV_jcPrE.
  by rewrite pr_eq_pairAC pr_eq_domin_RV2 ?div0R ?mulR0.
- by rewrite (cinde_alt _ H2).
Qed.

End contraction.

(* Probabilistic Reasoning in Intelligent Systems: Networks of Plausible Inference, Pearl, p.88 *)
Section derived_rules.

Variables (U : finType) (P : fdist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma chaining_rule : X _|_ Z | Y /\ [% X, Y] _|_ W | Z -> X _|_ W | Y.
Proof.
case=> ? ?.
suff : X _|_ [% W, Z] | Y by move/decomposition.
apply/cinde_drv_2C/contraction => //.
exact/cinde_drv_3C/symmetry/weak_union/symmetry.
Qed.

Lemma mixing_rule : X _|_ [% Y, W] | Z /\ Y _|_ W | Z -> [% X, W] _|_ Y | Z.
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

Lemma intersection : X _|_ Y | [% Z, W] -> X _|_ W | [% Z, Y] -> X _|_ [% Y, W] | Z.
Proof.
move=> H1 H2.
suff : X _|_ Y | Z by apply contraction.
move=> a b c; apply/esym.
rewrite [in X in X * _ = _](jcreasoning_by_cases W).
under eq_bigr do rewrite setX1.
rewrite big_distrl /=.
have <- : \sum_(d <- fin_img W)
           \Pr[ [% X, Y] = (a, b) | Z = c] * \Pr[ W = d | Z = c] =
         \sum_(d <- fin_img W)
           \Pr[ [% X, W] = (a, d) | Z = c] * \Pr[ Y = b | Z = c].
  suff H : forall d, \Pr[ [% X, Y] = (a, b) | Z = c] / \Pr[ Y = b | Z = c ] =
                \Pr[ [% X, W] = (a, d) | Z = c] / \Pr[ W = d | Z = c ].
    apply eq_bigr => d _.
    rewrite -eqR_divr_mulr; last first.
      rewrite RV_jcPrE divR_neq0' //.
      - by move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 W d) ->.
      - move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 [% Y, W] (b, d)).
        by rewrite pr_eq_pairCA pr_eq_pairA => ->.
    rewrite {1}/Rdiv mulRAC -/(Rdiv _ _) (H d) mulRAC eqR_divr_mulr //.
    rewrite RV_jcPrE divR_neq0' //.
    - move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 Y b).
      by rewrite pr_eq_pairC -pr_eq_pairA pr_eq_pairAC => ->.
    - move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 [% Y, W] (b, d)).
      by rewrite pr_eq_pairCA -pr_eq_pairA => ->.
  suff H : forall d, \Pr[ X = a | [% Y, Z] = (b, c)] =
                \Pr[ X = a | [% W, Z] = (d, c)].
    move=> d.
    rewrite RV_product_rule (H d).
    rewrite [in RHS]RV_product_rule.
    rewrite {1}/Rdiv -mulRA mulRV; last first.
      rewrite RV_jcPrE divR_neq0' //.
      - by move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 W d) ->.
      - move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 [% Y, W] (b, d)).
        by rewrite pr_eq_pairCA -pr_eq_pairA => ->.
    rewrite {1}/Rdiv -[in RHS]mulRA mulRV // RV_jcPrE divR_neq0' //.
    - move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 Y b).
      by rewrite pr_eq_pairC -pr_eq_pairA pr_eq_pairAC => ->.
    - move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 [% Y, W] (b, d)).
      by rewrite pr_eq_pairCA -pr_eq_pairA => ->.
  have {}H2 : forall d, \Pr[ X = a | [% Y, Z] = (b, c)] =
                     \Pr[ X = a | [% W, Z, Y] = (d, c, b)].
    move=> d; move: {H2}(H2 a d (c, b)).
    rewrite RV_product_rule.
    have /eqP H0 : \Pr[ W = d | [% Z, Y] = (c, b)] != 0.
      rewrite RV_jcPrE -pr_eq_pairA pr_eq_pairAC pr_eq_pairA.
      rewrite pr_eq_pairC divR_neq0' // pr_eq_pairC.
      by move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 W d) ->.
    move/eqR_mul2r => /(_ H0){H0}/esym.
    by rewrite [in LHS]RV_Pr_rC RV_Pr_rA.
  have {}H1 : forall d, \Pr[ X = a | [% W, Z] = (d, c)] =
                     \Pr[ X = a | [% Y, W, Z] = (b, d, c)].
    move=> d; move: {H1}(H1 a b (c, d)).
    rewrite RV_product_rule.
    have /eqP H0 : \Pr[ Y = b | [% Z, W] = (c, d)] != 0.
      rewrite RV_jcPrE -pr_eq_pairA divR_neq0' //.
      move: (P0 b c d); apply: contra => /eqP/(pr_eq_domin_RV2 Y b).
      by rewrite pr_eq_pairC -pr_eq_pairA => ->.
    move/eqR_mul2r => /(_ H0){H0}/esym.
    by rewrite [in LHS]RV_Pr_rC RV_Pr_rA RV_Pr_rAC.
  by move=> d; rewrite {H2}(H2 d) {}H1 RV_Pr_rC RV_Pr_rA.
rewrite -big_distrr /= jcPr_1_RV ?mulR1 //.
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
