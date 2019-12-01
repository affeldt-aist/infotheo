(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg matrix.
Require Import Reals.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop fdist.
Require Import jfdist.

(******************************************************************************)
(*           Conditional independence and graphoid axioms                     *)
(*                                                                            *)
(* P |= X _|_  Y | Z == X is conditionally independent of Y given Z in the    *)
(*                      distribution P for all values a, b, and c (belonging  *)
(*                      resp. to the codomains of X, Y , and Z)               *)
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
Reserved Notation "'[%' x , y , .. , z ']'" (at level 0,
  format "[%  x ,  y ,  .. ,  z ]").
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

(* TODO: move to lib/ssr_ext.v *)
Section toolbox.

Lemma bigcup_preimset (I : finType) (P : pred I)
      (A B : finType) (F : A -> B) (E : I -> {set B}) :
  \bigcup_(i | P i) F @^-1: E i = F @^-1: \bigcup_(i | P i) E i.
Proof.
rewrite/preimset.
apply/setP=> x; rewrite inE; apply/bigcupP/bigcupP => -[] i HPi; rewrite ?inE => HFxEi; exists i => //=; by rewrite inE.
Qed.

Lemma fin_img_imset (A B : finType) (f : A -> B) : fin_img f =i f @: A.
Proof.
apply/subset_eqP/andP; split; apply/subsetP => b; rewrite mem_undup; case/boolP : [exists a, b  == f a].
- by case/existsP => a /eqP ->; rewrite mem_imset.
- rewrite negb_exists; move/forallP=> bfx.
  case/mapP => a _ bfa.
    by move: (bfx a); rewrite bfa => /eqP.
- by case/existsP => a /eqP -> _; apply/mapP; exists a; rewrite // mem_enum.
- rewrite negb_exists; move/forallP=> bfx.
  case/imsetP => a _ bfa.
    by move: (bfx a); rewrite bfa => /eqP.
Qed.

End toolbox.

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

Section pair_of_RVs.
Variables (U : finType) (P : fdist U).
Variables (A : finType) (X : {RV P -> A}) (B : finType) (Y : {RV P -> B}).
Definition RV2 : {RV P -> A * B} := fun x => (X x, Y x).
End pair_of_RVs.

Notation "'[%' x , y , .. , z ']'" := (RV2 .. (RV2 x y) .. z).

Notation "\Pr[ X '\in' E | Y '\in' F ]" := (\Pr_(RVar.d [% X, Y])[ E | F ]).
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

Lemma Pr_RV2C E F :
  \Pr[ [% X, Y] \in setX E F] = \Pr[ [% Y, X] \in setX F E].
Proof.
rewrite -2!RVar.Pr_set.
rewrite /Pr !big_setX /= exchange_big /=; apply eq_bigr => b _.
apply/eq_bigr => a _; rewrite !RVar.dE /Pr; apply eq_bigl => u.
by rewrite !inE; apply/eqP/eqP => -[<- <-].
Qed.

Lemma fst_RV2 : Bivar.fst (RVar.d [% X, Y]) = RVar.d X.
Proof. by rewrite /Bivar.fst /RVar.d FDistMap.comp. Qed.

Lemma snd_RV2 : Bivar.snd (RVar.d [% X, Y]) = RVar.d Y.
Proof. by rewrite /Bivar.snd /RVar.d FDistMap.comp. Qed.

Lemma Swap_RV2 : Swap.d (RVar.d [% X, Y]) = RVar.d [% Y, X].
Proof. by rewrite /Swap.d /RVar.d FDistMap.comp. Qed.

End RV2_prop.

Section RV3_prop.
Variables (U : finType) (P : fdist U).
Variables (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma Proj13_RV3 : Proj13.d (RVar.d [% X, Y, Z]) = RVar.d [% X, Z].
Proof.
by rewrite /Proj13.d /Bivar.snd /TripA.d /RVar.d /TripC12.d !FDistMap.comp.
Qed.

Lemma snd_RV3 : Bivar.snd (RVar.d [% X, Y, Z]) = Bivar.snd (RVar.d [% X, Z]).
Proof. by rewrite -Proj13.snd Proj13_RV3. Qed.

Lemma TripC12_RV3 : TripC12.d (RVar.d [% X, Y, Z]) = RVar.d [% Y, X, Z].
Proof. by rewrite /TripC12.d /RVar.d FDistMap.comp. Qed.

Lemma TripA_RV3 : TripA.d (RVar.d [% X, Y, Z]) = RVar.d [% X, [% Y, Z]].
Proof. by rewrite /TripC12.d /RVar.d /TripA.d FDistMap.comp. Qed.

End RV3_prop.

Section more_structural_lemmas_on_RV.

Lemma RV_cPrE_set
  (U : finType) (P : fdist U) (B C : finType)
  (Y : {RV P -> B}) (Z : {RV P -> C}) (E : {set B}) (F : {set C}) :
  \Pr[ Y \in E | Z \in F ] = \Pr[ [% Y, Z] \in (setX E F)] / \Pr[ Z \in F ].
Proof.
rewrite /cPr snd_RV2 /RVar.d /pr_eq_set /Pr !partition_big_preimset /= /p_of.
congr (_ / _); first by apply eq_bigr => i Hi; rewrite FDistMap.dE; apply eq_bigr.
by apply eq_bigr => c Hc; rewrite FDistMap.dE.
Qed.
Lemma RV_cPrE
  (U : finType) (P : fdist U) (B C : finType)
  (Y : {RV P -> B}) (Z : {RV P -> C}) b c :
  \Pr[ Y = b | Z = c ] = \Pr[ [% Y, Z] = (b, c) ] / \Pr[ Z = c ].
Proof.
rewrite -!RVar.dE.
rewrite /cPr /pr_eq /Pr big_setX /=; congr (_ / _).
by rewrite !big_set1.
by rewrite big_set1 snd_RV2.
Qed.

(* NB: RV_cPr_comp? *)
Lemma RV_Pr_comp (U : finType) (P : fdist U) (A B : finType)
  (f : A -> B) a (X : {RV (P) -> A}) :
  injective f ->
  \Pr[ X = a ] = \Pr[ (comp_RV X f) = f a ].
Proof.
move=> inj_f.
rewrite -2!RVar.Pr !Pr_set1 /RVar.d !FDistMap.dE /comp_RV.
apply eq_bigl => u; rewrite !inE /=; by apply/eqP/eqP => [->//|/inj_f].
Qed.
Lemma RV_Pr_comp_set (U : finType) (P : fdist U) (A B : finType)
  (f : A -> B) E (X : {RV (P) -> A}) :
  injective f ->
  \Pr[ X \in E ] = \Pr[ (comp_RV X f) \in f @: E ].
Proof.
move=> inj_f.
rewrite -2!RVar.Pr_set /Pr big_imset /comp_RV /=; last by move=> *; apply inj_f.
apply eq_bigr => a Ha.
rewrite !FDistMap.dE; apply eq_bigl => u /=.
by apply/eqP/eqP => [->//|/inj_f].
Qed.

Definition unit_RV (U : finType) (P : fdist U) : {RV P -> unit} := (fun=> tt).

Lemma unit_RV1 (U : finType) (P : fdist U) : \Pr[ (unit_RV P) = tt ] = 1.
Proof. by rewrite -RVar.Pr Pr_set1; apply/eqP/FDist1.P; case. Qed.

Lemma RV_Pr_cPr_unit_set (U : finType) (P : fdist U) (A : finType)
  (X : {RV P -> A}) E :
  \Pr[ X \in E ] = \Pr[ X \in E | (unit_RV P) = tt ].
Proof.
rewrite RV_cPrE_set pr_eq_set1 unit_RV1 divR1.
rewrite (@RV_Pr_comp_set _ _ _ _ (fun a => (a, tt))); last by move=> u1 u2 -[].
by apply eq_bigl => u; rewrite setX1r.
Qed.

(* TODO: change the definition of \Pr[ X = a ] and obsolete pr_eq_set1 *)
Lemma RV_Pr_cPr_unit (U : finType) (P : fdist U) (A : finType)
  (X : {RV P -> A}) a :
  \Pr[ X = a ] = \Pr[ X = a | (unit_RV P) = tt ].
Proof. by rewrite -pr_eq_set1; apply RV_Pr_cPr_unit_set. Qed.

(* TODO: move *)
Lemma RV_product_rule
  (U : finType) (P : fdist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) a b c :
  \Pr[ [% X, Y] = (a, b) | Z = c ] =
  \Pr[ X = a | [% Y, Z] = (b, c) ] * \Pr[ Y = b | Z = c ].
Proof.
rewrite -setX1 product_rule; congr (cPr _ _ _ * _).
- by rewrite /TripA.d FDistMap.comp.
- by rewrite setX1.
- congr cPr; by rewrite /Proj23.d TripA_RV3 snd_RV2.
Qed.

Lemma RV_set_product_rule
  (U : finType) (P : fdist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) E F G :
  \Pr[ [% X, Y] \in setX E F | Z \in G ] =
  \Pr[ X \in E | [% Y, Z] \in setX F G ] * \Pr[ Y \in F | Z \in G ].
Proof.
rewrite product_rule; congr (cPr _ _ _ * _).
- by rewrite /TripA.d FDistMap.comp.
- congr cPr; by rewrite /Proj23.d TripA_RV3 snd_RV2.
Qed.

Lemma RV_Pr_lC (U : finType) (P : fdist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) a b G :
  \Pr[ [% Y, X] = (b, a) | Z \in G ] = \Pr[ [% X, Y] = (a, b) | Z \in G ].
Proof. by rewrite -setX1 -cPr_TripC12 TripC12_RV3 setX1. Qed.

Lemma RV_Pr_lC_set (U : finType) (P : fdist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) E F G :
  \Pr[ [% Y, X] \in setX F E | Z \in G ] = \Pr[ [% X, Y] \in setX E F | Z \in G ].
Proof. by rewrite -cPr_TripC12 TripC12_RV3. Qed.

Lemma RV_Pr_C (U : finType) (P : fdist U) (A B : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) a b :
  \Pr[ [% Y, X] = (b, a) ] = \Pr[ [% X, Y] = (a, b)].
Proof. by rewrite RV_Pr_cPr_unit RV_Pr_lC -RV_Pr_cPr_unit. Qed.

Lemma RV_Pr_C_set (U : finType) (P : fdist U) (A B : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) E F :
  \Pr[ [% Y, X] \in setX F E ] = \Pr[ [% X, Y] \in setX E F].
Proof. by rewrite RV_Pr_cPr_unit_set RV_Pr_lC_set -RV_Pr_cPr_unit_set. Qed.

Section setX_structural_lemmas.
Variables (A B C : finType).
Variables (E : {set A}) (F : {set B}) (G : {set C}).

Let ex2C (T : Type) (P Q : T -> Prop) : @ex2 T P Q <-> @ex2 T Q P.
Proof. by split; case=> x H0 H1; exists x. Qed.

Lemma imset_TripA_f :
  [set TripA.f x | x in setX (setX E F) G] = setX E (setX F G).
Proof.
apply/setP=> -[a [b c]]; apply/imsetP/idP.
- rewrite ex2C; move=> [[[a' b'] c']] /eqP.
  by rewrite /TripA.f !inE !xpair_eqE /= => /andP [] /eqP -> /andP [] /eqP -> /eqP -> /andP [] /andP [] -> -> ->.
- by rewrite !inE /= => /andP [aE /andP [bF cG]]; exists ((a, b), c); rewrite // !inE /= aE bF cG.
Qed.

Lemma imset_TripAC_f :
  [set TripAC.f x | x in setX (setX E F) G] = setX (setX E G) F.
Proof.
apply/setP => -[[a c] b]; apply/imsetP/idP.
- rewrite ex2C; move=> [[[a' b'] c']] /eqP.
  by rewrite /TripAC.f !inE !xpair_eqE /= => /andP [] /andP [] /eqP -> /eqP -> /eqP -> /andP [] /andP [] -> -> ->.
- by rewrite !inE /= => /andP [] /andP [] aE cG bF; exists ((a, b), c); rewrite // !inE  /= aE cG bF.
Qed.

Lemma imset_fst : (exists b : B, b \in F) -> [set x.1 | x in setX E F] = E.
Proof.
case=> b bF; apply/setP => a; apply/imsetP/idP.
- by rewrite ex2C; move=> -[[a' b']] /= ->; rewrite inE => /andP [] ->.
- by move=> aE; exists (a, b); rewrite // inE; apply/andP; split.
Qed.

End setX_structural_lemmas.

Lemma RV_Pr_lA_set (U : finType) (P : fdist U) (A B C D : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}) E F G H:
  \Pr[ [% X, [% Y, Z]] \in setX E (setX F G) | W \in H] =
  \Pr[ [% [% X, Y], Z] \in setX (setX E F) G | W \in H].
Proof. by rewrite (Pr_FDistMap_l TripA.inj_f) imset_TripA_f FDistMap.comp. Qed.

Lemma RV_Pr_lA (U : finType) (P : fdist U) (A B C D : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}) a b c H:
  \Pr[ [% X, [% Y, Z]] = (a, (b, c)) | W \in H] =
  \Pr[ [% [% X, Y], Z] = ((a, b), c) | W \in H].
Proof. by rewrite -!setX1 RV_Pr_lA_set. Qed.

Lemma RV_Pr_A (U : finType) (P : fdist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) a b c :
\Pr[ [% X, [% Y, Z]] = (a, (b, c)) ] = \Pr[ [% [% X, Y], Z] = ((a, b), c)].
Proof. by rewrite RV_Pr_cPr_unit RV_Pr_lA -RV_Pr_cPr_unit. Qed.

Lemma RV_Pr_A_set (U : finType) (P : fdist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) E F G :
\Pr[ [% X, [% Y, Z]] \in setX E (setX F G) ] = \Pr[ [% [% X, Y], Z] \in setX (setX E F) G].
Proof. by rewrite RV_Pr_cPr_unit_set RV_Pr_lA_set -RV_Pr_cPr_unit_set. Qed.

Lemma RV_Pr_setXunit (U : finType) (P : fdist U) (A : finType)
  (X : {RV P -> A}) E :
  \Pr[ [% X, unit_RV P] \in (setX E [set tt]) ]
  = \Pr[ X \in E ].
Proof.
rewrite -!RVar.Pr_set.
rewrite (Pr_FDistMap (f := fst)) /=; last by move => [a []] [a' []] /= ->.
rewrite imset_fst; last by exists tt; rewrite !inE.
apply eq_bigr => a aE.
by rewrite FDistMap.comp FDistMap.dE.
Qed.

Lemma RV_Pr_rsetXunit (U : finType) (P : fdist U) (A B : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) E F :
  \Pr[ X \in E | [% Y, unit_RV P] \in (setX F [set tt]) ]
  = \Pr[ X \in E | Y \in F ].
Proof.
congr (_ / _).
- by rewrite !RVar.Pr_set RV_Pr_A_set RV_Pr_setXunit.
- by rewrite !snd_RV2 !RVar.Pr_set RV_Pr_setXunit.
Qed.

Lemma RV2_Pr_lcongr (U : finType) (P : fdist U) (A A' B B' C : finType)
  (X : {RV P -> A}) (X' : {RV P -> A'}) (Y : {RV P -> B}) (Y' : {RV P -> B'})
  (Z : {RV P -> C}) E E' F F' G :
  \Pr[ X \in E | [% Y, Z] \in setX F G ] = \Pr[ X' \in E' | [% Y, Z] \in setX F G ] ->
  \Pr[ Y \in F | [% X', Z] \in setX E' G ] = \Pr[ Y' \in F' | [% X', Z] \in setX E' G ] ->
  \Pr[ [% X, Y] \in setX E F | Z \in G ] = \Pr[ [% X', Y'] \in setX E' F' | Z \in G ].
Proof.
move=> EE' FF'.
transitivity \Pr[ [% X', Y] \in (setX E' F) | Z \in G ];
  first by rewrite !RV_set_product_rule EE'.
rewrite [in LHS]RV_Pr_lC_set [in RHS]RV_Pr_lC_set.
by rewrite !RV_set_product_rule FF'.
Qed.

Lemma RV2_Pr_lcongr' (U : finType) (P : fdist U) (A A' B B' C : finType)
  (X : {RV P -> A}) (X' : {RV P -> A'}) (Y : {RV P -> B}) (Y' : {RV P -> B'})
  (Z : {RV P -> C}) E E' F F' G :
  \Pr[ X \in E | [% Y', Z] \in setX F' G ] = \Pr[ X' \in E' | [% Y', Z] \in setX F' G ] ->
  \Pr[ Y \in F | [% X, Z] \in setX E G ] = \Pr[ Y' \in F' | [% X, Z] \in setX E G ] ->
  \Pr[ [% X, Y] \in setX E F | Z \in G ] = \Pr[ [% X', Y'] \in setX E' F' | Z \in G ].
Proof.
move=> EE' FF'.
transitivity \Pr[ [% X, Y'] \in (setX E F') | Z \in G ];
  last by rewrite !RV_set_product_rule EE'.
rewrite [in LHS]RV_Pr_lC_set [in RHS]RV_Pr_lC_set.
by rewrite !RV_set_product_rule FF'.
Qed.

Lemma RV2_Pr_congr (U : finType) (P : fdist U) (A A' B B' : finType)
  (X : {RV P -> A}) (X' : {RV P -> A'}) (Y : {RV P -> B}) (Y' : {RV P -> B'})
  E E' F F' :
  \Pr[ X \in E | Y \in F ] = \Pr[ X' \in E' | Y \in F ] ->
  \Pr[ Y \in F | X' \in E' ] = \Pr[ Y' \in F' | X' \in E' ] ->
  \Pr[ [% X, Y] \in setX E F ] = \Pr[ [% X', Y'] \in setX E' F' ].
Proof.
move=> EE' FF'.
rewrite !RV_Pr_cPr_unit_set.
apply RV2_Pr_lcongr; by rewrite !RV_Pr_rsetXunit.
Qed.

Lemma RV2_Pr_congr' (U : finType) (P : fdist U) (A A' B B' : finType)
  (X : {RV P -> A}) (X' : {RV P -> A'}) (Y : {RV P -> B}) (Y' : {RV P -> B'})
  E E' F F' :
  \Pr[ X \in E | Y' \in F' ] = \Pr[ X' \in E' | Y' \in F' ] ->
  \Pr[ Y \in F | X \in E ] = \Pr[ Y' \in F' | X \in E ] ->
  \Pr[ [% X, Y] \in setX E F ] = \Pr[ [% X', Y'] \in setX E' F' ].
Proof.
move=> EE' FF'.
rewrite !RV_Pr_cPr_unit_set.
apply RV2_Pr_lcongr'; by rewrite !RV_Pr_rsetXunit.
Qed.

Lemma RV_Pr_lAC_set (U : finType) (P : fdist U) (A B C D : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}) E F G H:
  \Pr[ [% X, Y, Z] \in setX (setX E F) G | W \in H] =
  \Pr[ [% X, Z, Y] \in setX (setX E G) F | W \in H].
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
  \Pr[ [% X, [% Y, Z]] \in setX E (setX F G) | W \in H] =
  \Pr[ [% X, [% Z, Y]] \in setX E (setX G F) | W \in H].
Proof. by rewrite RV_Pr_lA_set  RV_Pr_lAC_set -RV_Pr_lA_set. Qed.

Lemma RV_Pr_lCA (U : finType) (P : fdist U) (A B C D : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}) a b c H:
  \Pr[ [% X, [% Y, Z]] = (a, (b, c)) | W \in H] =
  \Pr[ [% X, [% Z, Y]] = (a, (c, b)) | W \in H].
Proof. by rewrite -!setX1 RV_Pr_lCA_set. Qed.

Lemma RV_Pr_CA (U : finType) (P : fdist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) a b c :
\Pr[ [% X, [%Y, Z]] = (a, (b, c)) ] = \Pr[ [% X, [%Z, Y]] = (a, (c, b))].
Proof. by rewrite RV_Pr_cPr_unit RV_Pr_lCA -RV_Pr_cPr_unit. Qed.

Lemma RV_Pr_CA_set (U : finType) (P : fdist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) E F G :
\Pr[ [% X, [%Y, Z]] \in setX E (setX F G) ] = \Pr[ [% X, [%Z, Y]] \in setX E (setX G F)].
Proof. by rewrite RV_Pr_cPr_unit_set RV_Pr_lCA_set -RV_Pr_cPr_unit_set. Qed.

Lemma RV_Pr_AC (U : finType) (P : fdist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) a b c :
\Pr[ [% X, Y, Z] = (a, b, c) ] = \Pr[ [% X, Z, Y] = (a, c, b)].
Proof. by rewrite RV_Pr_cPr_unit RV_Pr_lAC -RV_Pr_cPr_unit. Qed.

Lemma RV_Pr_AC_set (U : finType) (P : fdist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) E F G :
\Pr[ [% X, Y, Z] \in setX (setX E F) G]
= \Pr[ [% X, Z, Y] \in setX (setX E G) F].
Proof. by rewrite RV_Pr_cPr_unit_set RV_Pr_lAC_set -RV_Pr_cPr_unit_set. Qed.

Lemma RV_Pr_rA (U : finType) (P : fdist U) (A B C D : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}) E b c d :
  \Pr[ X \in E | [% Y, [% Z, W]] = (b, (c, d)) ] =
  \Pr[ X \in E | [% Y, Z, W] = (b, c, d) ].
Proof.
by rewrite (Pr_FDistMap_r TripA.inj_f) /= /RVar.d !FDistMap.comp imset_set1.
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
by rewrite (Pr_FDistMap_r inj_swap) /RVar.d !FDistMap.comp imset_set1.
Qed.

Lemma RV_Pr_cPr_0
  (U : finType) (P : fdist U) (B C : finType)
  (Y : {RV P -> B}) (Z : {RV P -> C}) b c :
  \Pr[ [% Y, Z] = (b, c) ] = 0 ->
  \Pr[ Y = b | Z = c ] = 0.
Proof.
move=> H0.
by rewrite RV_cPrE H0 div0R.
Qed.

Lemma RV_Pr_cPr_0_set
  (U : finType) (P : fdist U) (B C : finType)
  (Y : {RV P -> B}) (Z : {RV P -> C}) F G :
  \Pr[ [% Y, Z] \in setX F G ] = 0 ->
  \Pr[ Y \in F | Z \in G ] = 0.
Proof.
move=> H0.
by rewrite RV_cPrE_set H0 div0R.
Qed.

End more_structural_lemmas_on_RV.

Section marginals.

Section marginal_RV3.
Variables (U : finType) (P : fdist U).
Variables (A B C D : finType).
Variables (W : {RV P -> D}) (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).

(*Lemma marginal_RV2_1 a :
  \sum_(u in X @^-1 a) P u = \sum_(b in B) (RVar.d [% X, Y]) (a, b).
Proof.
have -> : X @^-1 a = \bigcup_b [% X, Y] @^-1 (a, b).
  apply/setP=> u; rewrite !inE; apply/eqP/bigcupP.
  by move=> <- /=; exists (Y u) => //; rewrite inE.
  by case=> b _; rewrite inE => /eqP[] <- ?.
rewrite partition_disjoint_bigcup /=; last first.
  move=> b0 b1 b01; rewrite -setI_eq0; apply/eqP/setP => u; rewrite !inE.
  apply/negbTE/negP => /andP[] /eqP[<- Yub0] /eqP -[].
  rewrite Yub0; exact/eqP.
apply eq_bigr => b _; by rewrite RVar.dE.
Qed.*)

(*Lemma marginal_RV2_2 b :
  \sum_(u in Y @^-1 b) P u = \sum_(a in A) (RVar.d [% X, Y]) (a, b).
Proof.
have -> : Y @^-1 b = \bigcup_a [% X, Y] @^-1 (a, b).
  apply/setP => u; rewrite !inE; apply/eqP/bigcupP.
  by move=> <- /=; exists (X u) => //; rewrite inE.
  by case=> a _; rewrite inE => /eqP[] ? <-.
rewrite partition_disjoint_bigcup /=; last first.
  move=> a0 a1 a01; rewrite -setI_eq0; apply/eqP/setP => u; rewrite !inE.
  apply/negbTE/negP => /andP[] /eqP[Xua0 <-] /eqP -[].
  rewrite Xua0; exact/eqP.
by apply eq_bigr => a _; by rewrite RVar.dE.
Qed.*)

(*Lemma marginal_RV3_1 b c :
  \sum_(u in [% Y, Z] @^-1 (b, c)) P u =
  \sum_(d in D) (RVar.d [% W, Y, Z] (d, b, c)).
Proof.
have -> : ([% Y, Z] @^-1 (b, c)) = \bigcup_d [% W, Y, Z] @^-1 (d, b, c).
  apply/setP => u; rewrite !inE; apply/eqP/bigcupP.
  by case=> <- <- /=; exists (W u) => //; rewrite inE.
  by case=> d _; rewrite inE => /eqP[] ? <- <-.
rewrite partition_disjoint_bigcup /=; last first.
  move=> d0 d1 d01; rewrite -setI_eq0; apply/eqP/setP => u; rewrite !inE.
  apply/negbTE/negP => /andP[] /eqP[Wud0 <- <-] /eqP -[].
  rewrite Wud0; exact/eqP.
by apply eq_bigr => d _; rewrite RVar.dE.
Qed.*)

Lemma marginal_RV3_2_set F G :
  \Pr[ [% Y, Z] \in setX F G ] =
  \sum_(d in D) \Pr[ [% Y, W, Z] \in setX (setX F [set d]) G].
Proof.
rewrite /pr_eq_set.
have -> : ([% Y, Z] @^-1: setX F G)
          = \bigcup_d [% Y, W, Z] @^-1: setX (setX F [set d]) G.
  rewrite bigcup_preimset; apply/setP => u; rewrite !inE; apply/andP/bigcupP.
  by case=> HF HG; exists (W u) => //; rewrite !inE HF HG eqxx.
  by case => d _; rewrite !inE => /andP[] /andP[] -> _ ->.
rewrite bigcup_preimset /Pr /p_of partition_big_preimset /=.
rewrite partition_disjoint_bigcup /=; last first.
  move=> d0 d1 d01.
  rewrite -setI_eq0; apply/eqP/setP => u; rewrite !inE.
  apply/negbTE/negP=> /andP[] /andP[] /andP[] -> /eqP-> -> /=; move/negP: d01.
  by rewrite andbT; apply.
apply eq_bigr => d _.
by rewrite partition_big_preimset /=.
Qed.

Lemma marginal_RV3_2' b c :
  \Pr[ [% Y, Z] = (b, c) ] =
  \sum_(d in D) \Pr[ [% Y, W, Z] = (b, d, c)].
Proof.
by rewrite -pr_eq_set1 -setX1 marginal_RV3_2_set; apply eq_bigr => d _; rewrite !setX1 pr_eq_set1.
Qed.

Lemma marginal_RV3_2 b c :
  \sum_(u in [% Y, Z] @^-1 (b, c)) P u =
  \sum_(d in D) \Pr[ [% Y, W, Z] = (b, d, c)].
Proof. exact: marginal_RV3_2'. Qed.

Lemma marginal_RV3_3_set F G :
  \Pr[ [% Y, Z] \in setX F G ] =
  \sum_(d in D) \Pr[ [% Y, Z, W] \in setX (setX F G) [set d]].
Proof.
by rewrite marginal_RV3_2_set; apply eq_bigr => d _; rewrite RV_Pr_AC_set.
Qed.

Lemma marginal_RV3_3' b c :
  \Pr[ [% Y, Z] = (b, c) ] =
  \sum_(d in D) \Pr[ [% Y, Z, W] = (b, c, d)].
Proof.
by rewrite -pr_eq_set1 -setX1 marginal_RV3_3_set; apply eq_bigr => d _; rewrite !setX1 pr_eq_set1.
Qed.

Lemma marginal_RV3_3 b c :
  \sum_(u in [% Y, Z] @^-1 (b, c)) P u =
  \sum_(d in D) \Pr[ [% Y, Z, W] = (b, c, d)].
Proof. exact: marginal_RV3_3'. Qed.

End marginal_RV3.

Section marginal_RV4.
Variables (U : finType) (P : fdist U).
Variables (A B C D : finType).
Variables (W : {RV P -> D}) (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).

Lemma marginal_RV4_1_set E F G :
  \Pr[ [% X, Y, Z] \in setX (setX E F) G ] =
  \sum_(d in D) \Pr[ [% W, X, Y, Z] \in setX (setX (setX [set d] E) F) G].
Proof.
rewrite (marginal_RV3_2_set W [% X, Y] Z).
apply eq_bigr => d _.
apply RV2_Pr_congr => //.
by rewrite RV_Pr_lC_set RV_Pr_lA_set.
Qed.

Lemma marginal_RV4_1' a b c :
  \Pr[ [% X, Y, Z] = (a, b, c)] =
  \sum_(d in D) \Pr[ [% W, X, Y, Z] = (d, a, b, c)].
Proof.
by rewrite -pr_eq_set1 -!setX1 marginal_RV4_1_set; apply eq_bigr => d _; rewrite !setX1 pr_eq_set1.
Qed.

Lemma marginal_RV4_1 a b c :
  \sum_(u in [% X, Y, Z] @^-1 (a, b, c)) P u =
  \sum_(d in D) \Pr[ [% W, X, Y, Z] = (d, a, b, c)].
Proof. exact: marginal_RV4_1'. Qed.

Lemma marginal_RV4_3_set E F G :
  \Pr[ [% X, Y, Z] \in setX (setX E F) G ] =
  \sum_(d in D) \Pr[ [% X, Y, W, Z] \in setX (setX (setX E F) [set d]) G].
Proof. by rewrite (marginal_RV3_2_set W [% X, Y] Z). Qed.

Lemma marginal_RV4_3' a b c :
  \Pr[ [% X, Y, Z] = (a, b, c) ] =
  \sum_(d in D) \Pr[ [% X, Y, W, Z] = (a, b, d, c)].
Proof. by rewrite (marginal_RV3_2' W [% X, Y] Z). Qed.

Lemma marginal_RV4_3 a b c :
  \sum_(u in [% X, Y, Z] @^-1 (a, b, c)) P u =
  \sum_(d in D) \Pr[ [% X, Y, W, Z] = (a, b, d, c)].
Proof. exact: marginal_RV4_3'. Qed.

Lemma marginal_RV4_4_set E F G :
  \Pr[ [% X, Y, Z] \in setX (setX E F) G ] =
  \sum_(d in D) \Pr[ [% X, Y, Z, W] \in setX (setX (setX E F) G) [set d] ].
Proof. by rewrite (marginal_RV3_3_set W [% X, Y] Z). Qed.

Lemma marginal_RV4_4' a b c :
  \Pr[ [% X, Y, Z] = (a, b, c) ] =
  \sum_(d in D) \Pr[ [% X, Y, Z, W] = (a, b, c, d)].
Proof. by rewrite (marginal_RV3_3' W [% X, Y] Z). Qed.

Lemma marginal_RV4_4 a b c :
  \sum_(u in [% X, Y, Z] @^-1 (a, b, c)) P u =
  \sum_(d in D) \Pr[ [% X, Y, Z, W] = (a, b, c, d) ].
Proof. exact: marginal_RV4_4'. Qed.

End marginal_RV4.

End marginals.

(* TODO: move to cproba.v? *)
Section Pr_cPr_domin.
Lemma Pr_cPr_domin (A B : finType) (P : {fdist A * B})
      (E : {set A}) (F : {set B}) :
  Pr (Bivar.snd P) F <> 0 ->
  Pr (Bivar.fst P) E = 0 -> \Pr_P[ E | F ] = 0.
Proof.
move=> Fn0 E0.
rewrite /cPr.
rewrite -(eqR_mul2r Fn0) mul0R -mulRA mulVR; last by move/eqP:Fn0.
rewrite mulR1; by apply Pr_domin_fst.
Qed.
End Pr_cPr_domin.

Section RV_domin.
Variables (U : finType) (P : fdist U) (A B : finType).
Variables (X : {RV (P) -> (A)}) (Y : {RV (P) -> (B)}).

Lemma RV_Pr_domin_snd_set E F : \Pr[ Y \in F ] = 0 -> \Pr[ [% X, Y] \in setX E F ] = 0.
Proof.
move=> H.
by rewrite -RVar.Pr_set Pr_domin_snd // snd_RV2 RVar.Pr_set.
Qed.

Lemma RV_Pr_domin_fst_set E F : \Pr[ X \in E ] = 0 -> \Pr[ [% X, Y] \in setX E F ] = 0.
Proof.
move=> H.
by rewrite -RVar.Pr_set Pr_domin_fst // fst_RV2 RVar.Pr_set.
Qed.

Lemma RV_Pr_domin_snd a b : \Pr[ Y = b ] = 0 -> \Pr[ [% X, Y] = (a, b) ] = 0.
Proof.
move=> H.
by rewrite -RVar.Pr -setX1 Pr_domin_snd // snd_RV2 RVar.Pr.
Qed.

Lemma RV_Pr_domin_fst a b : \Pr[ X = a ] = 0 -> \Pr[ [% X, Y] = (a, b) ] = 0.
Proof.
move=> H.
by rewrite -RVar.Pr -setX1 Pr_domin_fst // fst_RV2 RVar.Pr.
Qed.

Lemma RV_Pr_cPr_domin_set E F :
  \Pr[ Y \in F ] <> 0 -> \Pr[ X \in E ] = 0 -> \Pr[ X \in E | Y \in F ] = 0.
Proof.
move=> YF XE.
by apply Pr_cPr_domin; [rewrite snd_RV2 RVar.Pr_set | rewrite fst_RV2 RVar.Pr_set].
Qed.

End RV_domin.

Section cPr_1_RV.

Variables (U : finType) (P : fdist U) (A B : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}).

(* NB: see also cPr_1 *)
Lemma cPr_1_RV a : \Pr[X = a] != 0 ->
  \sum_(b <- fin_img Y) \Pr[ Y = b | X = a ] = 1.
Proof.
rewrite -RVar.Pr Pr_set1 -{1}(fst_RV2 _ Y) => Xa0.
set Q := (RVar.d [% X, Y]) `(| a ).
rewrite -(FDist.f1 Q) [in RHS](bigID (fun b => b \in fin_img Y)) /=.
rewrite [X in _ = _ + X](eq_bigr (fun=> 0)); last first.
  move=> b bY.
  rewrite /Q CondJFDist.dE // /cPr /Pr !(big_setX,big_set1) /= Swap.dE Swap.snd fst_RV2.
  rewrite !RVar.dE /pr_eq /Pr big1 ?div0R // => u.
  rewrite inE => /eqP[Yub ?].
  exfalso.
  move/negP : bY; apply.
  rewrite mem_undup; apply/mapP; exists u => //; by rewrite mem_enum.
rewrite big_const iter_addR mulR0 addR0.
rewrite big_uniq; last by rewrite /fin_img undup_uniq.
apply eq_bigr => b; rewrite mem_undup => /mapP[u _ bWu].
by rewrite /Q CondJFDist.dE // Swap_RV2.
Qed.

End cPr_1_RV.

Section reasoning_by_cases.

Variables (U : finType) (P : fdist U).
Variables (A B C : finType) (Z : {RV P -> C}) (X : {RV P -> A}) (Y : {RV P -> B}).

Lemma total_RV2 E F :
  \Pr[ [% X, Y] \in setX E F] =
  \sum_(z <- fin_img Z) \Pr[ [% X, Z, Y] \in setX (setX E [set z]) F].
Proof.
rewrite (@marginal_RV3_2_set _ _ _ _ C Z).
rewrite (bigID (fun x => x \in fin_img Z)) /=.
rewrite [X in _ + X = _](eq_bigr (fun=> 0)); first
  by rewrite big_const iter_addR mulR0 addR0 big_uniq //; exact: undup_uniq.
move=> c; rewrite RV_Pr_AC_set => H.
apply RV_Pr_domin_snd_set.
by rewrite pr_eq_set1 pr_eq0.
Qed.

Lemma reasoning_by_cases E F :
  \Pr[ X \in E | Y \in F ] =
  \sum_(z <- fin_img Z) \Pr[ [% X, Z] \in setX E [set z] | Y \in F ].
Proof.
rewrite RV_cPrE_set total_RV2 -[in RHS]big_distrl /= (snd_RV3 _ Z); congr (_ / _).
by apply eq_bigr => c _; rewrite RVar.Pr_set.
by rewrite snd_RV2 RVar.Pr_set.
Qed.

End reasoning_by_cases.

Section conditionnally_independent_discrete_random_variables.

Variables (U : finType) (P : fdist U) (A B C : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).

Definition cinde_drv := forall a b c,
  \Pr[ [% X, Y] = (a, b) | Z = c ] = \Pr[ X = a | Z = c ] * \Pr[ Y = b | Z = c].

End conditionnally_independent_discrete_random_variables.

Notation "X _|_  Y | Z" := (cinde_drv X Y Z) : proba_scope.
Notation "P |= X _|_  Y | Z" := (@cinde_drv _ P _ _ _ X Y Z) : proba_scope.

Lemma cindeP (U : finType) (P : fdist U) (A B C : finType) (X : {RV P -> A}) (Y : {RV P -> B}) {Z : {RV P -> C}} a b c :
  P |= X _|_ Y | Z ->
  \Pr[ [% Y, Z] = (b, c)] != 0 ->
  \Pr[ X = a | [% Y, Z] = (b, c)] = \Pr[X = a | Z = c].
Proof.
move=> K /eqP H0.
rewrite RV_cPrE -(eqR_mul2r H0) -mulRA mulVR ?mulR1; last by apply/eqP.
have H1 : /(\Pr[ Z = c ]) <> 0 by apply invR_neq0; move/(RV_Pr_domin_snd Y b).
by rewrite RV_Pr_A -(eqR_mul2r H1) -mulRA -!divRE -!RV_cPrE K.
Qed.

Section cinde_drv_prop.

Variables (U : finType) (P : fdist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

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

End cinde_drv_prop.

Section symmetry.

Variable (U : finType) (P : fdist U).
Variables (A B C : finType) (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).

Lemma symmetry : X _|_ Y | Z -> Y _|_ X | Z.
Proof.
move=> H b a c.
rewrite /cinde_drv in H.
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
  rewrite (reasoning_by_cases W); apply eq_bigr => /= d _.
  by rewrite RV_Pr_lA setX1.
transitivity (\sum_(d <- fin_img W)
  \Pr[ X = a | Z = c] * \Pr[ [% Y, W] = (b, d) | Z = c]).
  by apply eq_bigr => d _; rewrite H.
rewrite -big_distrr /=; congr (_ * _).
rewrite (reasoning_by_cases W); apply eq_bigr => d _.
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
  case/boolP : (\Pr[ [% Y, W, Z] = (b, d, c)] == 0) => [/eqP|] H0.
  - by rewrite [X in _ * X = _ * X]RV_cPrE RV_Pr_A RV_Pr_AC H0 div0R !mulR0.
  - by rewrite (cindeP _ H).
case/boolP : (\Pr[ [% Z, W] = (c, d) ] == 0) => [/eqP|] ?.
- by rewrite [X in _ * X = _ * X]RV_cPrE RV_Pr_domin_snd ?(div0R,mulR0).
- have {}H : X _|_ W | Z by move/cinde_drv_2C : H; apply decomposition.
  by rewrite [in X in _ = X * _]RV_Pr_rC (cindeP _ H) // RV_Pr_C.
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
  case/boolP : (\Pr[ [% W, [% Z, Y]] = (d, (c, b))] == 0) => [/eqP|] H0.
    rewrite [in X in _ * X = _ * X]RV_cPrE.
    by rewrite -RV_Pr_A RV_Pr_C -RV_Pr_A H0 div0R !mulR0.
  by rewrite (cindeP _ H1) // RV_Pr_rC.
case/boolP : (\Pr[ [% Y, Z] = (b, c) ] == 0) => [/eqP|] H0.
- rewrite [X in _ * X = _ * X]RV_cPrE.
  by rewrite RV_Pr_AC RV_Pr_domin_fst ?div0R ?mulR0.
- by rewrite (cindeP _ H2).
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

Hypothesis P0 : forall b c d, \Pr[ [% Y, Z, W] = (b, c, d) ] != 0.
Hypothesis D_not_empty : D.

Lemma intersection : X _|_ Y | [% Z, W] -> X _|_ W | [% Z, Y] -> X _|_ [% Y, W] | Z.
Proof.
move=> H1 H2.
suff : X _|_ Y | Z by apply contraction.
move=> a b c; apply/esym.
rewrite [in X in X * _ = _](reasoning_by_cases W).
evar (h : D -> R); rewrite (eq_bigr h); last first.
  move=> d _; rewrite setX1 /h; reflexivity.
rewrite {}/h big_distrl /=.
have <- : \sum_(d <- fin_img W)
           \Pr[ [% X, Y] = (a, b) | Z = c] * \Pr[ W = d | Z = c] =
         \sum_(d <- fin_img W)
           \Pr[ [% X, W] = (a, d) | Z = c] * \Pr[ Y = b | Z = c].
  suff H : forall d, \Pr[ [% X, Y] = (a, b) | Z = c] / \Pr[ Y = b | Z = c ] =
                \Pr[ [% X, W] = (a, d) | Z = c] / \Pr[ W = d | Z = c ].
    apply eq_bigr => d _.
    rewrite -eqR_divr_mulr; last first.
      rewrite RV_cPrE divR_neq0' //.
      - move: (P0 b c d); apply: contra => /eqP/(RV_Pr_domin_snd W d).
        by rewrite RV_Pr_C -RV_Pr_A => ->.
      - move: (P0 b c d); apply: contra => /eqP/(RV_Pr_domin_snd [% Y, W] (b, d)).
        by rewrite RV_Pr_AC => ->.
    rewrite {1}/Rdiv mulRAC -/(Rdiv _ _) (H d) mulRAC eqR_divr_mulr //.
    rewrite RV_cPrE divR_neq0' //.
    - move: (P0 b c d); apply: contra => /eqP/(RV_Pr_domin_snd Y b).
      by rewrite RV_Pr_A RV_Pr_AC => ->.
    - move: (P0 b c d); apply: contra => /eqP/(RV_Pr_domin_snd [% Y, W] (b, d)).
      by rewrite RV_Pr_AC => ->.
  suff H : forall d, \Pr[ X = a | [% Y, Z] = (b, c)] =
                \Pr[ X = a | [% W, Z] = (d, c)].
    move=> d.
    rewrite RV_product_rule (H d).
    rewrite [in RHS]RV_product_rule.
    rewrite {1}/Rdiv -mulRA mulRV; last first.
      rewrite RV_cPrE divR_neq0' //.
      - move: (P0 b c d); apply: contra => /eqP/(RV_Pr_domin_snd W d).
        by rewrite RV_Pr_C => ->.
      - move: (P0 b c d); apply: contra => /eqP/(RV_Pr_domin_snd [% Y, W] (b, d)).
        by rewrite RV_Pr_AC => ->.
    rewrite {1}/Rdiv -[in RHS]mulRA mulRV // RV_cPrE divR_neq0' //.
    - move: (P0 b c d); apply: contra => /eqP/(RV_Pr_domin_fst Y b).
      by rewrite RV_Pr_C RV_Pr_A RV_Pr_AC => ->.
    - move: (P0 b c d); apply: contra => /eqP/(RV_Pr_domin_snd [% Y, W] (b, d)).
      by rewrite RV_Pr_AC => ->.
  have {}H2 : forall d, \Pr[ X = a | [% Y, Z] = (b, c)] =
                     \Pr[ X = a | [% W, Z, Y] = (d, c, b)].
    move=> d; move: {H2}(H2 a d (c, b)).
    rewrite RV_product_rule.
    have /eqP H0 : \Pr[ W = d | [% Z, Y] = (c, b)] != 0.
      rewrite RV_cPrE RV_Pr_CA RV_Pr_C divR_neq0' // RV_Pr_C.
      by move: (P0 b c d); apply: contra => /eqP/(RV_Pr_domin_fst W d) ->.
    move/eqR_mul2r => /(_ H0){H0}/esym.
    by rewrite RV_Pr_rC RV_Pr_rA.
  have {}H1 : forall d, \Pr[ X = a | [% W, Z] = (d, c)] =
                     \Pr[ X = a | [% Y, W, Z] = (b, d, c)].
    move=> d; move: {H1}(H1 a b (c, d)).
    rewrite RV_product_rule.
    have /eqP H0 : \Pr[ Y = b | [% Z, W] = (c, d)] != 0.
      rewrite RV_cPrE RV_Pr_A divR_neq0' //.
      move: (P0 b c d); apply: contra => /eqP/(RV_Pr_domin_snd Y b).
      by rewrite RV_Pr_A => ->.
    move/eqR_mul2r => /(_ H0){H0}/esym.
    by rewrite RV_Pr_rC RV_Pr_rA RV_Pr_rAC.
  by move=> d; rewrite {H2}(H2 d) {}H1 RV_Pr_rC RV_Pr_rA.
rewrite -big_distrr /= cPr_1_RV ?mulR1 //.
move: (P0 b c D_not_empty); apply: contra.
by rewrite RV_Pr_AC => /eqP/(RV_Pr_domin_snd [% Y, W] (b, D_not_empty)) ->.
Qed.

End intersection.
