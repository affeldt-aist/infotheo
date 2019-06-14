(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import Reals.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.
Require Import cproba.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.

(* tentative formalization of conditional independence
contents:
- Various distributions (Proj124.d, Proj14d, QuadA23.d)
- Section pair_of_RVs.
- Section marginals.
- Section RV2_prop.
- Section RV3_prop.
- Section trip_prop.
- Section conditionnally_independent_discrete_random_variables.
- Section reasoning_by_cases.
- Section cinde_drv_prop.
- Section cPr_1_RV.
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

Local Open Scope proba_scope.

Module Proj124.
Section proj124.
Variables (A B D C : finType) (P : {dist A * B * D * C}).
Definition d : {dist A * B * C} :=
  Swap.d (Bivar.snd (TripA.d (Swap.d (TripA.d P)))).
Lemma dE abc : d abc = \rsum_(x in D) P (abc.1.1, abc.1.2, x, abc.2).
Proof.
case: abc => [[a b] c] /=.
rewrite /d Swap.dE Bivar.sndE; apply eq_bigr => d _.
by rewrite TripA.dE /= Swap.dE TripA.dE.
Qed.
Lemma snd : Bivar.snd d = Bivar.snd P.
Proof. by rewrite /Bivar.snd /d !DistMap.comp. Qed.
End proj124.
End Proj124.

Definition Proj14d (A B C D : finType) (d : {dist A * B * D * C}) : {dist A * C} :=
  Proj13.d (Proj124.d d).

Module QuadA23.
Section def.
Variables (A B C D : finType) (P : {dist A * B * D * C}).
Definition f (x : A * B * D * C) : A * (B * D) * C :=
  (x.1.1.1, (x.1.1.2, x.1.2), x.2).
Lemma inj_f : injective f.
Proof. by rewrite /f => -[[[? ?] ?] ?] [[[? ?] ?] ?] /= [-> -> -> ->]. Qed.
Definition d : {dist A * (B * D) * C} := DistMap.d f P.
Lemma dE x : d x = P (x.1.1, x.1.2.1, x.1.2.2, x.2).
Proof.
case: x => -[a [b d] c]; rewrite /def.d DistMap.dE /= -/(f (a, b, d, c)).
by rewrite (big_pred1_inj inj_f).
Qed.
End def.
Section prop.
Variables (A B C D : finType) (P : {dist A * B * D * C}).
Lemma snd : Bivar.snd (QuadA23.d P) = Bivar.snd P.
Proof. by rewrite /Bivar.snd /d DistMap.comp. Qed.
End prop.
End QuadA23.

Section pair_of_RVs.
Variables (U : finType) (P : dist U).
Variables (A : finType) (X : {RV P -> A}) (B : finType) (Y : {RV P -> B}).
Definition RV2 : {RV P -> A * B} := fun x => (X x, Y x).
End pair_of_RVs.

Notation "'[%' x , y , .. , z ']'" := (RV2 .. (RV2 x y) .. z).

Section marginals.
Variables (U : finType) (P : dist U).
Variables (A B C D : finType).
Variables (W : {RV P -> D}) (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).

(*Lemma marginal_RV2_1 a :
  \rsum_(u in X @^-1 a) P u = \rsum_(b in B) (RVar.d [% X, Y]) (a, b).
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
  \rsum_(u in Y @^-1 b) P u = \rsum_(a in A) (RVar.d [% X, Y]) (a, b).
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
  \rsum_(u in [% Y, Z] @^-1 (b, c)) P u =
  \rsum_(d in D) (RVar.d [% W, Y, Z] (d, b, c)).
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

Lemma marginal_RV3_2 b c :
  \rsum_(u in [% Y, Z] @^-1 (b, c)) P u =
  \rsum_(d in D) (RVar.d [% Y, W, Z]) (b, d, c).
Proof.
have -> : [% Y, Z] @^-1 (b, c) = \bigcup_d [% Y, W, Z] @^-1 (b, d, c).
  apply/setP => u; rewrite !inE; apply/eqP/bigcupP.
  by case=> <- <- /=; exists (W u) => //; rewrite inE.
  by case=> d _; rewrite inE => /eqP[] <- ? <-.
rewrite partition_disjoint_bigcup /=; last first.
  move=> d0 d1 d01.
  rewrite -setI_eq0; apply/eqP/setP => u; rewrite !inE.
  apply/negbTE/negP => /andP[] /eqP[<- Wud0 <-] /eqP -[].
  rewrite Wud0; exact/eqP.
by apply eq_bigr => d  _; rewrite RVar.dE.
Qed.

Lemma marginal_RV3_3 b c :
  \rsum_(u in [% Y, Z] @^-1 (b, c)) P u =
  \rsum_(d in D) (RVar.d [% Y, Z, W]) (b, c, d).
Proof.
have -> : ([% Y, Z] @^-1 (b, c)) = \bigcup_d [% Y, Z, W] @^-1 (b, c, d).
  apply/setP => u; rewrite !inE; apply/eqP/bigcupP.
  by case=> <- <- /=; exists (W u) => //; rewrite inE.
  by case=> d _; rewrite inE => /eqP[] <- <-.
rewrite partition_disjoint_bigcup /=; last first.
  move=> d0 d1 d01.
  rewrite -setI_eq0; apply/eqP/setP => u; rewrite !inE.
  apply/negbTE/negP => /andP[] /eqP[<- <- Wud0] /eqP -[].
  rewrite Wud0; exact/eqP.
apply eq_bigr => d _; by rewrite RVar.dE.
Qed.

Lemma marginal_RV4_1 a b c :
  \rsum_(u in [% X, Y, Z] @^-1 (a, b, c)) P u =
  \rsum_(d in D) (RVar.d [% W, X, Y, Z]) (d, a, b, c).
Proof.
have -> : [% X, Y, Z] @^-1 (a, b, c) = \bigcup_d [% W, X, Y, Z] @^-1 (d, a, b, c).
  apply/setP => u; rewrite !inE; apply/eqP/bigcupP.
  by case=> <- <- <- /=; exists (W u) => //; rewrite inE.
  by case=> d _; rewrite inE => /eqP[] ? <- <- <-.
rewrite partition_disjoint_bigcup /=; last first.
  move=> d0 d1 d01.
  rewrite -setI_eq0; apply/eqP/setP => u; rewrite !inE.
  apply/negbTE/negP => /andP[] /eqP[Wud0 <- <- <-] /eqP -[].
  rewrite Wud0; exact/eqP.
by apply eq_bigr => d _; rewrite RVar.dE.
Qed.

Lemma marginal_RV4_3 a b c :
  \rsum_(u in [% X, Y, Z] @^-1 (a, b, c)) P u =
  \rsum_(d in D) (RVar.d [% X, Y, W, Z]) (a, b, d, c).
Proof.
have -> : [% X, Y, Z] @^-1 (a, b, c) = \bigcup_d [% X, Y, W, Z] @^-1 (a, b, d, c).
  apply/setP => u; rewrite !inE; apply/eqP/bigcupP.
  by case=> <- <- <- /=; exists (W u) => //; rewrite inE.
  by case=> d _; rewrite inE => /eqP[] <- <- ? <-.
rewrite partition_disjoint_bigcup /=; last first.
  move=> d0 d1 d01.
  rewrite -setI_eq0; apply/eqP/setP => u; rewrite !inE.
  apply/negbTE/negP => /andP[] /eqP[<- <- Wud0 <-] /eqP -[].
  rewrite Wud0; exact/eqP.
by apply eq_bigr => d _; rewrite RVar.dE.
Qed.

Lemma marginal_RV4_4 a b c :
  \rsum_(u in [% X, Y, Z] @^-1 (a, b, c)) P u =
  \rsum_(d in D) (RVar.d [% X, Y, Z, W]) (a, b, c, d).
Proof.
have -> : [% X, Y, Z] @^-1 (a, b, c) = \bigcup_d [% X, Y, Z, W] @^-1 (a, b, c, d).
  apply/setP => u; rewrite !inE; apply/eqP/bigcupP.
  by case=> <- <- <- /=; exists (W u) => //; rewrite inE.
  by case=> d _; rewrite inE => /eqP[] <- <- <- ?.
rewrite partition_disjoint_bigcup /=; last first.
  move=> d0 d1 d01.
  rewrite -setI_eq0; apply/eqP/setP => u; rewrite !inE.
  apply/negbTE/negP => /andP[] /eqP[<- <- <- Wud0] /eqP -[].
  rewrite Wud0; exact/eqP.
by apply eq_bigr => d _; rewrite RVar.dE.
Qed.

End marginals.

Section RV2_prop.
Variables (U : finType) (P : dist U).
Variables (A B : finType) (X : {RV P -> A}) (Y : {RV P -> B}).
Implicit Types (E : {set A}) (F : {set B}).

Lemma Pr_RV2C E F :
  Pr (RVar.d [% X, Y]) (setX E F) = Pr (RVar.d [% Y, X]) (setX F E).
Proof.
rewrite /Pr !big_setX /= exchange_big /=; apply eq_bigr => b _.
apply/eq_bigr => a _; rewrite !RVar.dE /Pr; apply eq_bigl => u.
by rewrite !inE; apply/eqP/eqP => -[<- <-].
Qed.
Lemma Pr_RV2C' E F :
  \Pr[ [% X, Y] \in setX E F ] = \Pr[ [% Y, X] \in setX F E ].
Proof. by rewrite -!RVar.Pr_set; apply Pr_RV2C. Qed.

Lemma fst_RV2 : Bivar.fst (RVar.d [% X, Y]) = RVar.d X.
Proof. by rewrite /Bivar.fst /RVar.d DistMap.comp. Qed.

Lemma snd_RV2 : Bivar.snd (RVar.d [% X, Y]) = RVar.d Y.
Proof. by rewrite /Bivar.snd /RVar.d DistMap.comp. Qed.

Lemma Swap_RV2 : Swap.d (RVar.d [% X, Y]) = RVar.d [% Y, X].
Proof. by rewrite /Swap.d /RVar.d DistMap.comp. Qed.

(*Lemma Pr_RV2_domin_fst E F : Pr (RVar.d X) E = 0 ->
  Pr (RVar.d [% X, Y]) (setX E F) = 0.
Proof. move=> H; apply Pr_domin_fst; by rewrite fst_RV2. Qed.*)

(*Lemma Pr_RV2_domin_snd a b : Pr (RVar.d Y) b = 0 ->
  Pr (RVar.d [% X, Y]) (setX a b) = 0.
Proof. move=> H; apply Pr_domin_snd; by rewrite snd_RV2. Qed.*)

End RV2_prop.

Section RV3_prop.
Variables (U : finType) (P : dist U).
Variables (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma snd_TripA_RV3 :
  Bivar.snd (TripA.d (RVar.d [% X, Y, Z])) = RVar.d [% Y, Z].
Proof. by rewrite /Bivar.snd /TripA.d /RVar.d !DistMap.comp. Qed.

Lemma snd_TripA_RV4 :
  Bivar.snd (TripA.d (RVar.d [% X, [% Y, W],  Z])) = RVar.d [% Y, W, Z].
Proof. by rewrite /Bivar.snd /TripA.d /RVar.d !DistMap.comp. Qed.

Lemma Proj13_RV3 : Proj13.d (RVar.d [% X, Y, Z]) = RVar.d [% X, Z].
Proof.
by rewrite /Proj13.d /Bivar.snd /TripA.d /RVar.d /TripC12.d !DistMap.comp.
Qed.

Lemma snd_RV3 : Bivar.snd (RVar.d [% X, Y, Z]) = Bivar.snd (RVar.d [% X, Z]).
Proof. by rewrite -Proj13.snd Proj13_RV3. Qed.

Lemma Proj23_RV3 : Proj23.d (RVar.d [% X, Y, Z]) = RVar.d [% Y, Z].
Proof. by rewrite /Proj23.d snd_TripA_RV3. Qed.

End RV3_prop.

Section trip_prop.
Variable (U : finType) (Q : dist U).
Variables (A B C : finType) (X : {RV Q -> A}) (Y : {RV Q -> B}) (Z : {RV Q -> C}).

Let P := RVar.d [% X, Y, Z].

Lemma TripC12_RV3 : TripC12.d P = RVar.d [% Y, X, Z].
Proof. by rewrite /TripC12.d /P /RVar.d DistMap.comp. Qed.

Lemma TripA_RV3 : TripA.d (RVar.d [% X, Y, Z]) = RVar.d [% X, [% Y, Z]].
Proof. by rewrite /TripC12.d /RVar.d /TripA.d DistMap.comp. Qed.

Lemma TripC23_RV3 : TripC23.d (RVar.d [% X, Y, Z]) = RVar.d [% X, Z, Y].
Proof.
by rewrite /TripC23.d /TripC12.d /TripA.d /RVar.d /Swap.d !DistMap.comp.
Qed.
End trip_prop.

Section conditionnally_independent_discrete_random_variables.

Variables (U : finType) (P : dist U) (A B C : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).
Let Q := RVar.d [% X, Y, Z].

Local Notation "\Pr[ X '\in' E | Y '\in' F ]" := (\Pr_(RVar.d [% X, Y])[ E | F ]).
Local Notation "\Pr[ X = a | Y = b ]" := (\Pr[ X \in [set a] | Y \in [set b]]).

Definition cinde_drv := forall a b c,
  \Pr[ [% X, Y] = (a, b) | Z = c ] = \Pr[ X = a | Z = c ] * \Pr[ Y = b | Z = c].

End conditionnally_independent_discrete_random_variables.

Notation "\Pr[ X '\in' E | Y '\in' F ]" := (\Pr_(RVar.d [% X, Y])[ E | F ]).
Notation "\Pr[ X '\in' E | Y = b ]" := (\Pr[ X \in E | Y \in [set b]]).
Notation "\Pr[ X = a | Y '\in' F ]" := (\Pr[ X \in [set a] | Y \in F]).
Notation "\Pr[ X = a | Y = b ]" := (\Pr[ X \in [set a] | Y \in [set b]]).

Notation "X _|_  Y | Z" := (cinde_drv X Y Z) : proba_scope.
Notation "P |= X _|_  Y | Z" := (@cinde_drv _ P _ _ _ X Y Z) : proba_scope.

Lemma cindeP (U : finType) (P : dist U) (A B C : finType) (X : {RV P -> A}) (Y : {RV P -> B}) {Z : {RV P -> C}} a b c :
  P |= X _|_ Y | Z ->
  \Pr[ [% Y, Z] = (b, c)] != 0 ->
  \Pr[ X = a | [% Y, Z] = (b, c)] = \Pr[X = a | Z = c].
Proof.
move=> K H0.
have H := K a b c.
rewrite -(@eqR_mul2r (\Pr[ Y = b | Z = c ])); last first.
  rewrite /cPr setX1 mulR_neq0; split.
  - rewrite Pr_set1 RVar.dE; exact/eqP.
  - apply/invR_neq0/eqP/(@Pr_domin_sndN _ _ _ [set b]).
    by rewrite setX1 Pr_set1 RVar.dE.
rewrite -{}H -[in RHS]setX1 product_rule; congr (_ * _).
- by rewrite setX1 /RVar.d /TripA.d DistMap.comp.
- by rewrite /Proj23.d /Bivar.snd !DistMap.comp.
Qed.

Section reasoning_by_cases.

Variables (U : finType) (P : dist U).
Variables (A B C : finType) (Z : {RV P -> C}) (X : {RV P -> A}) (Y : {RV P -> B}).

Lemma total_RV2 E F :
  Pr (RVar.d [% X, Y]) (setX E F) =
  \rsum_(z <- fin_img Z) Pr (RVar.d [% X, Z, Y]) (setX (setX E [set z]) F).
Proof.
apply/esym.
evar (e : C -> R); rewrite (eq_bigr e); last first.
  move=> r _; rewrite /Pr big_setX /=.
  rewrite (eq_bigl (fun x => x \in setX E [set r])); last first.
    move=> -[? ?]; by rewrite !inE.
  rewrite big_setX /= /e; reflexivity.
rewrite {}/e exchange_big /=.
rewrite [in RHS]/Pr [in RHS]big_setX /=; apply eq_bigr => a aE.
evar (e : C -> R); rewrite (eq_bigr e); last first.
  move=> r _; rewrite exchange_big /= /e; reflexivity.
rewrite {}/e exchange_big /=; apply eq_bigr => b _.
rewrite RVar.dE /pr_eq /Pr (marginal_RV3_2 Z).
rewrite [in RHS](bigID (fun x => x \in fin_img Z)) /=.
rewrite [X in _ = _ + X ](eq_bigr (fun=> 0)); last first.
  move=> d dZ; rewrite RVar.dE /=; apply pr_eq0.
  apply: contra dZ; rewrite /fin_img !mem_undup.
  case/mapP => u _ -[] Ha Hd Hb; apply/mapP.
  exists u => //; by rewrite mem_enum.
rewrite big_const iter_addR mulR0 addR0 big_uniq /=; last exact: undup_uniq.
apply eq_bigr => c cZ; by rewrite big_set1 !RVar.dE.
Qed.
Lemma total_RV2' E F :
  \Pr[ [% X, Y] \in setX E F] =
  \rsum_(z <- fin_img Z) \Pr[ [% X, Z, Y] \in setX (setX E [set z]) F].
Proof.
by rewrite -RVar.Pr_set total_RV2; apply eq_bigr=> *; rewrite RVar.Pr_set.
Qed.

Lemma reasoning_by_cases E F :
  \Pr[ X \in E | Y \in F ] =
  \rsum_(z <- fin_img Z) \Pr[ [% X, Z] \in (setX E [set z]) | Y \in F ].
Proof.
by rewrite {1}/cPr total_RV2 -[in RHS]big_distrl /= (snd_RV3 _ Z).
Qed.

End reasoning_by_cases.

Lemma RV_cPrE_set
  (U : finType) (P : dist U) (B C : finType)
  (Y : {RV P -> B}) (Z : {RV P -> C}) (E : {set B}) (F : {set C}) :
  \Pr[ Y \in E | Z \in F ] = \Pr[ [% Y, Z] \in (setX E F)] / \Pr[ Z \in F ].
Proof.
rewrite /cPr snd_RV2 /RVar.d /pr_set /Pr !partition_big_preimset /= /p_of.
congr (_ / _); first by apply eq_bigr => i Hi; rewrite DistMap.dE; apply eq_bigr.
by apply eq_bigr => c Hc; rewrite DistMap.dE.
Qed.
Lemma RV_cPrE
  (U : finType) (P : dist U) (B C : finType)
  (Y : {RV P -> B}) (Z : {RV P -> C}) b c :
  \Pr[ Y = b | Z = c ] = \Pr[ [% Y, Z] = (b, c) ] / \Pr[ Z = c ].
Proof.
rewrite -!RVar.dE.
rewrite /cPr /pr_eq /Pr big_setX /=; congr (_ / _).
by rewrite !big_set1.
by rewrite big_set1 snd_RV2.
Qed.

(* NB: RV_cPr_comp? *)
Lemma RV_Pr_comp (U : finType) (P : dist U) (A B : finType)
  (f : A -> B) a (X : {RV (P) -> A}) :
  injective f ->
  \Pr[ X = a ] = \Pr[ (comp_RV X f) = f a ].
Proof.
move=> inj_f.
rewrite -2!RVar.Pr !Pr_set1 /RVar.d !DistMap.dE /comp_RV.
apply eq_bigl => u; rewrite !inE /=; by apply/eqP/eqP => [->//|/inj_f].
Qed.

Definition unit_RV (U : finType) (P : dist U) : {RV P -> unit} := (fun=> tt).

Lemma unit_RV1 (U : finType) (P : dist U) : \Pr[ (unit_RV P) = tt ] = 1.
Proof. by rewrite -RVar.Pr Pr_set1; apply/eqP/Dist1.dist1P; case. Qed.

Lemma RV_Pr_cPr_unit (U : finType) (P : dist U) (A : finType)
  (X : {RV P -> A}) a :
  \Pr[ X = a ] = \Pr[ X = a | (unit_RV P) = tt ].
Proof.
rewrite RV_cPrE unit_RV1 divR1.
rewrite (@RV_Pr_comp _ _ _ _ (fun a => (a, tt))); last by move=> u1 u2 -[].
done.
Qed.

Lemma RV_Pr_lC (U : finType) (P : dist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) a b c :
  \Pr[ [% Y, X] = (b, a) | Z = c ] = \Pr[ [% X, Y] = (a, b) | Z = c ].
Proof. by rewrite -setX1 -cPr_TripC12 TripC12_RV3 setX1. Qed.

Lemma RV_Pr_C (U : finType) (P : dist U) (A B : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) a b :
  \Pr[ [% Y, X] = (b, a) ] = \Pr[ [% X, Y] = (a, b)].
Proof. by rewrite RV_Pr_cPr_unit RV_Pr_lC -RV_Pr_cPr_unit. Qed.

Lemma RV_Pr_lA (U : finType) (P : dist U) (A B C D : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}) a b c d:
  \Pr[ [% X, [% Y, Z]] = (a, (b, c)) | W = d] =
  \Pr[ [% [% X, Y], Z] = ((a, b), c) | W = d].
Proof.
by rewrite (Pr_DistMap_l TripA.inj_f) //= /RVar.d !DistMap.comp imset_set1.
Qed.

Lemma RV_Pr_lAC (U : finType) (P : dist U) (A B C D : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}) a b c d:
  \Pr[ [% X, Y, Z] = (a, b, c) | W = d] =
  \Pr[ [% X, Z, Y] = (a, c, b) | W = d].
Proof.
by rewrite (Pr_DistMap_l TripC23.inj_f) //= /RVar.d !DistMap.comp imset_set1.
Qed.

Lemma RV_Pr_A (U : finType) (P : dist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) a b c :
\Pr[ [% X, [% Y, Z]] = (a, (b, c)) ] = \Pr[ [% [% X, Y], Z] = ((a, b), c)].
Proof. by rewrite RV_Pr_cPr_unit RV_Pr_lA -RV_Pr_cPr_unit. Qed.

Lemma RV_Pr_lCA (U : finType) (P : dist U) (A B C D : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}) a b c d:
  \Pr[ [% X, [% Y, Z]] = (a, (b, c)) | W = d] =
  \Pr[ [% X, [% Z, Y]] = (a, (c, b)) | W = d].
Proof.
rewrite /cPr !snd_RV2; congr (_ / _).
rewrite (@Pr_DistMap _ _ (fun x : A * (B * C) * D => (x.1.1, (x.1.2.2, x.1.2.1), x.2))); last first.
  by move=> -[[a0 [b0 c0]] d0] -[[a1 [b1 c1]] d1] /= [-> -> -> ->].
rewrite /RVar.d !DistMap.comp; congr Pr => //.
apply/setP => -[[a0 [c0 b0]] d0].
rewrite !inE /=.
apply/idP/idP.
  case/imsetP => /= -[[a1 [b1 c1]] d1].
  rewrite !inE /= => /andP[/eqP[-> -> ->] /eqP ->] [-> -> -> ->]; by rewrite !eqxx.
case/andP => /eqP [-> -> -> /eqP ->].
by apply/imsetP; exists (a, (b, c), d) => //=; rewrite !inE !eqxx.
Qed.

Lemma RV_Pr_CA (U : finType) (P : dist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) a b c :
\Pr[ [% X, [%Y, Z]] = (a, (b, c)) ] = \Pr[ [% X, [%Z, Y]] = (a, (c, b))].
Proof.
by rewrite RV_Pr_cPr_unit RV_Pr_lCA -RV_Pr_cPr_unit.
Qed.

Lemma RV_Pr_AC (U : finType) (P : dist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) a b c :
\Pr[ [% X, Y, Z] = (a, b, c) ] = \Pr[ [% X, Z, Y] = (a, c, b)].
Proof.
by rewrite RV_Pr_cPr_unit RV_Pr_lAC -RV_Pr_cPr_unit.
Qed.

Lemma RV_Pr_rA (U : finType) (P : dist U) (A B C D : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}) a b c d :
  \Pr[ X = a | [% Y, [% Z, W]] = (b, (c, d)) ] =
  \Pr[ X = a | [% Y, Z, W] = (b, c, d) ].
Proof.
by rewrite (Pr_DistMap_r TripA.inj_f) /= /RVar.d !DistMap.comp imset_set1.
Qed.

Lemma RV_Pr_rAC (U : finType) (P : dist U) (A B C D : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}) a b c d :
  \Pr[ X = a | [% Y, Z, W] = (b, c, d) ] =
  \Pr[ X = a | [% Y, W, Z] = (b, d, c) ].
Proof.
by rewrite (Pr_DistMap_r TripC23.inj_f) /= !DistMap.comp imset_set1.
Qed.

Lemma RV_Pr_rCA (U : finType) (P : dist U) (A B C D : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}) a b c d :
  \Pr[ X = a | [% Y, [% Z, W]] = (b, (c, d)) ] =
  \Pr[ X = a | [% Y, [% W, Z]] = (b, (d, c)) ].
Proof.
rewrite (Pr_DistMap_r (inj_comp TripA.inj_f (inj_comp TripC23.inj_f TripA'.inj_f))).
by rewrite /= !DistMap.comp // !imset_set1.
Qed.

Lemma RV_Pr_rC (U : finType) (P : dist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) a b c :
  \Pr[ X = a | [% Y, Z] = (b, c) ] =
  \Pr[ X = a | [% Z, Y] = (c, b) ].
Proof.
by rewrite (Pr_DistMap_r inj_swap) /RVar.d !DistMap.comp imset_set1.
Qed.

(* TODO: move *)
Lemma RV_product_rule
  (U : finType) (P : dist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) a b c :
  \Pr[ [% X, Y] = (a, b) | Z = c ] =
  \Pr[ X = a | [% Y, Z] = (b, c) ] * \Pr[ Y = b | Z = c ].
Proof.
rewrite -setX1 product_rule; congr (cPr _ _ _ * _).
- by rewrite /TripA.d DistMap.comp.
- by rewrite setX1.
- congr cPr; by rewrite /Proj23.d TripA_RV3 snd_RV2.
Qed.

Lemma Pr_cPr_0
  (U : finType) (P : dist U) (B C : finType)
  (Y : {RV P -> B}) (Z : {RV P -> C}) b c :
  \Pr[ [% Y, Z] = (b, c) ] = 0 ->
  \Pr[ Y = b | Z = c ] = 0.
Proof.
move=> H0.
by rewrite RV_cPrE H0 div0R.
Qed.

Section RV_pair.
Variables (U : finType) (P : dist U) (A B : finType).
Variables (X : {RV (P) -> (A)}) (Y : {RV (P) -> (B)}).

Lemma RV_Pr_domin_snd  a b : \Pr[ Y = b ] = 0 -> \Pr[ [% X, Y] = (a, b) ] = 0.
Proof.
move=> H.
by rewrite -RVar.Pr -setX1 Pr_domin_snd // snd_RV2 RVar.Pr.
Qed.

Lemma RV_Pr_domin_fst a b : \Pr[ X = a ] = 0 -> \Pr[ [% X, Y] = (a, b) ] = 0.
Proof.
move=> H.
by rewrite -RVar.Pr -setX1 Pr_domin_fst // fst_RV2 RVar.Pr.
Qed.
End RV_pair.

Section cPr_1_RV.

Variables (U : finType) (P : dist U) (A B : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}).

(* NB: see also cPr_1 *)
Lemma cPr_1_RV a : \Pr[X = a] != 0 ->
  \rsum_(b <- fin_img Y) \Pr[ Y = b | X = a ] = 1.
Proof.
rewrite -RVar.Pr Pr_set1.
rewrite -{1}(fst_RV2 _ Y) => Xa0.
set Q := CondDist.d (RVar.d [% X, Y]) _ Xa0.
rewrite -(epmf1 Q) [in RHS](bigID (fun b => b \in fin_img Y)) /=.
rewrite [X in _ = _ + X](eq_bigr (fun=> 0)); last first.
  move=> b bY.
  rewrite /Q CondDist.dE /cPr /Pr !(big_setX,big_set1) /= Swap.dE Swap.snd fst_RV2.
  rewrite !RVar.dE /pr_eq /Pr big1 ?div0R // => u.
  rewrite inE => /eqP[Yub ?].
  exfalso.
  move/negP : bY; apply.
  rewrite mem_undup; apply/mapP; exists u => //; by rewrite mem_enum.
rewrite big_const iter_addR mulR0 addR0.
rewrite big_uniq; last by rewrite /fin_img undup_uniq.
apply eq_bigr => b; rewrite mem_undup => /mapP[u _ bWu].
by rewrite /Q CondDist.dE Swap_RV2.
Qed.

End cPr_1_RV.

Section cinde_drv_prop.

Variables (U : finType) (P : dist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma cinde_drv_2C : X _|_ [% Y, W] | Z -> P |= X _|_ [% W, Y] | Z.
Proof.
move=> H a -[d b] c.
by rewrite RV_Pr_lA RV_Pr_lAC -RV_Pr_lA H RV_Pr_lC.
Qed.

Lemma cinde_drv_3C : X _|_ Y | [% Z, W] -> X _|_ Y | [% W, Z].
Proof.
move=> H; move=> a b -[d c]; move: (H a b (c, d)) => {H}H.
by rewrite RV_Pr_rC H RV_Pr_rC; congr (_ * _); rewrite RV_Pr_rC.
Qed.

End cinde_drv_prop.

Section symmetry.

Variable (U : finType) (P : dist U).
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

Variables (U : finType) (P : dist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).
Let Q := RVar.d [% X, Y, W, Z].

Lemma decomposition : X _|_ [% Y, W] | Z -> X _|_ Y | Z.
Proof.
move=> H a b c.
transitivity (\rsum_(d <- fin_img W) \Pr[ [% X, [% Y, W]] = (a, (b, d)) | Z = c]).
  rewrite (reasoning_by_cases W); apply eq_bigr => /= d _.
  by rewrite RV_Pr_lA setX1.
transitivity (\rsum_(d <- fin_img W)
  \Pr[ X = a | Z = c] * \Pr[ [% Y, W] = (b, d) | Z = c]).
  by apply eq_bigr => d _; rewrite H.
rewrite -big_distrr /=; congr (_ * _).
rewrite (reasoning_by_cases W); apply eq_bigr => d _.
by rewrite setX1.
Qed.

End decomposition.

Section weak_union.

Variables (U : finType) (P : dist U) (A B C D : finType).
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
- have {H}H : X _|_ W | Z by move/cinde_drv_2C : H; apply decomposition.
  by rewrite [in X in _ = X * _]RV_Pr_rC (cindeP _ H) // RV_Pr_C.
Qed.

End weak_union.

Section contraction.

Variables (U : finType) (P : dist U) (A B C D : finType).
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

Variables (U : finType) (P : dist U) (A B C D : finType).
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

Variables (U : finType) (P : dist U) (A B C D : finType).
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
have <- : \rsum_(d <- fin_img W)
           \Pr[ [% X, Y] = (a, b) | Z = c] * \Pr[ W = d | Z = c] =
         \rsum_(d <- fin_img W)
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
  have {H2}H2 : forall d, \Pr[ X = a | [% Y, Z] = (b, c)] =
                     \Pr[ X = a | [% W, Z, Y] = (d, c, b)].
    move=> d; move: {H2}(H2 a d (c, b)).
    rewrite RV_product_rule.
    have /eqP H0 : \Pr[ W = d | [% Z, Y] = (c, b)] != 0.
      rewrite RV_cPrE RV_Pr_CA RV_Pr_C divR_neq0' // RV_Pr_C.
      by move: (P0 b c d); apply: contra => /eqP/(RV_Pr_domin_fst W d) ->.
    move/eqR_mul2r => /(_ H0){H0}/esym.
    by rewrite RV_Pr_rC RV_Pr_rA.
  have {H1}H1 : forall d, \Pr[ X = a | [% W, Z] = (d, c)] =
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
