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
- Various distributions (Proj124.d, Proj14d, Proj234.d, QuadA23.d, QuadA34.d,
  QuadA234.d)
- Section pair_of_RVs.
- Section marginals.
- Section RV2_prop.
- Section RV3_prop.
- Section trip_prop.
- Section quad_prop.
- Section conditionnally_independent_discrete_random_variables.
- Section cinde_drv_prop.
- Section reasoning_by_cases.
- Section symmetry.
- Section decomposition.
- Section weak_union.
- Section contraction.
- Section derived_rules.
- Section cPr_1_RV.
- Section intersection.
*)

Reserved Notation "X _|_  Y | Z" (at level 10, Y, Z at next level).
Reserved Notation "P |= X _|_  Y | Z" (at level 10, X, Y, Z at next level).
Reserved Notation "'[%' x , y , .. , z ']'" (at level 0,
  format "[%  x ,  y ,  .. ,  z ]").
Reserved Notation "\Pr[ X '\in' P | Y '\in' Q ]" (at level 6, X, Y, P, Q at next level,
  format "\Pr[  X  '\in'  P  |  Y  '\in'  Q  ]").
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

Module Proj234.
Section proj234.
Variables (A B D C : finType) (P : {dist A * B * C * D}).
Definition d : {dist B * C * D} := TripA'.d (Bivar.snd (TripA.d (TripA.d P))).
Lemma dE abc: d abc = \rsum_(x in A) P (x, abc.1.1, abc.1.2, abc.2).
Proof.
rewrite TripA'.dE Bivar.sndE; apply eq_bigr => a _; by rewrite 2!TripA.dE.
Qed.
End proj234.
End Proj234.

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

Module QuadA34.
Section def.
Variables (A B C D : finType) (P : {dist A * B * D * C}).
Definition d : {dist A * B * (D * C)} := TripA.d P.
Lemma dE x : d x = P (let: (a, b, (d, c)) := x in (a, b, d, c)).
Proof. by rewrite /d TripA.dE; move: x => -[[? ?] [? ?]]. Qed.
End def.
End QuadA34.

Module QuadA234.
Section def.
Variables (A B C D : finType) (P : {dist A * B * C * D}).
Definition f (x : A * B * C * D) : A * (B * C * D) :=
  let: (a, b, c, e) := x in (a, (b, c, e)).
Lemma inj_f : injective f.
Proof. by move=> [[[? ?] ?] ?] [[[? ?] ?] ?]; rewrite /f => -[-> -> -> ->]. Qed.
Definition d : {dist A * (B * C * D)} := DistMap.d f P.
Lemma dE a b c e : d (a, (b, c, e)) = P (a, b, c, e).
Proof.
rewrite /d DistMap.dE /= -/(f (a, b, c, e)) big_pred1_inj //; exact/inj_f.
Qed.
End def.
Section prop.
Variables (A B C D : finType) (P : {dist A * B * D * C}).
Lemma Pr (E : {set A}) (F : {set B}) (G : {set D}) (H : {set C}) :
  Pr (d P) (setX E (setX (setX F G) H)) =
  Pr (QuadA34.d P) (setX (setX E F) (setX G H)).
Proof.
rewrite /Pr !big_setX /=; apply eq_bigr => a _.
rewrite !big_setX /=; apply eq_bigr => b _; rewrite big_setX /=.
apply/eq_bigr => c _; apply eq_bigr => d _.
by rewrite QuadA34.dE QuadA234.dE.
Qed.
End prop.
End QuadA234.

Section QuadA_prop.
Variables (A B C D : finType) (P : {dist A * B * C * D}).

Lemma cPr_TripA_QuadA34 E F G H :
  \Pr_(TripA.d (QuadA34.d P))[ E | setX F (setX G H) ] =
  \Pr_(QuadA234.d P)[ E | setX (setX F G) H ].
Proof.
rewrite /cPr; congr (_ / _).
  by rewrite TripA.Pr QuadA234.Pr.
rewrite -TripA.Pr; congr Pr.
(* TODO: lemma? *)
apply/dist_ext => -[b [c d]].
rewrite TripA.dE 2!Bivar.sndE; apply eq_bigr => a _.
by rewrite TripA.dE QuadA234.dE /= QuadA34.dE.
Qed.

Lemma cPr_TripA_QuadA23 E F G H :
  \Pr_(TripA.d (QuadA23.d P))[ E | (setX (setX F G) H) ] =
  \Pr_(QuadA234.d P)[ E | setX (setX F G) H ].
Proof.
rewrite -cPr_TripA_QuadA34 /cPr; congr (_ / _).
  rewrite !TripA.Pr.
  rewrite /Pr; rewrite !big_setX; apply eq_bigr => a aE /=.
  rewrite !big_setX; apply eq_bigr => b bF /=; apply eq_bigr => c cG /=.
  by apply eq_bigr => d dH; rewrite QuadA23.dE.
rewrite -TripA.Pr; congr Pr.
(* TODO: lemma *)
by rewrite /TripA.d /Bivar.snd /QuadA23.d /QuadA34.d !DistMap.comp.
Qed.

Lemma cPr_QuadA23 E F G H :
  \Pr_(QuadA23.d P)[setX E (setX F G) | H] = \Pr_P[setX (setX E F) G | H].
Proof.
rewrite /cPr QuadA23.snd; congr (_ / _).
rewrite /Pr !big_setX /=; apply eq_bigr => a aE; rewrite big_setX.
apply eq_bigr => b bF; apply eq_bigr => c cG; apply eq_bigr => d dH.
by rewrite QuadA23.dE.
Qed.

End QuadA_prop.

Section QuadA_prop2.
Variables (A B C D : finType) (P : {dist A * B * C * D}).

Lemma cPr_TripA_QuadA23_TripC23 E F G H : \Pr_(QuadA234.d P)[E | setX (setX F G) H] =
  \Pr_(TripA.d (QuadA23.d (TripC23.d P)))[E | setX (setX F H) G].
Proof.
rewrite cPr_TripA_QuadA23.
rewrite /cPr; congr (_ / _).
  rewrite /Pr !big_setX; apply eq_bigr => a aE; rewrite !big_setX; apply eq_bigr => b bF.
  rewrite exchange_big; apply eq_bigr => d dH; apply eq_bigr => c cG.
  by rewrite !QuadA234.dE TripC23.dE.
rewrite /Pr !big_setX; apply eq_bigr => b bF; rewrite exchange_big; apply eq_bigr => d dH.
apply eq_bigr => c cG.
rewrite !Bivar.sndE; apply eq_bigr => a0 _.
by rewrite 2!QuadA234.dE TripC23.dE.
Qed.

End QuadA_prop2.

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

Lemma fst_RV2 : Bivar.fst (RVar.d [% X, Y]) = RVar.d X.
Proof. by rewrite /Bivar.fst /RVar.d DistMap.comp. Qed.

Lemma snd_RV2 : Bivar.snd (RVar.d [% X, Y]) = RVar.d Y.
Proof. by rewrite /Bivar.snd /RVar.d DistMap.comp. Qed.

Lemma Swap_RV2 : Swap.d (RVar.d [% X, Y]) = RVar.d [% Y, X].
Proof. by rewrite /Swap.d /RVar.d DistMap.comp. Qed.

Lemma Pr_RV2_domin_fst E F : Pr (RVar.d X) E = 0 ->
  Pr (RVar.d [% X, Y]) (setX E F) = 0.
Proof. move=> H; apply Pr_domin_fst; by rewrite fst_RV2. Qed.

Lemma Pr_RV2_domin_snd a b : Pr (RVar.d Y) b = 0 ->
  Pr (RVar.d [% X, Y]) (setX a b) = 0.
Proof. move=> H; apply Pr_domin_snd; by rewrite snd_RV2. Qed.

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

Section quad_prop.
Variables (U : finType) (P : dist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma QuadA23_RV4 : QuadA23.d (RVar.d [% X, Y, W, Z]) = RVar.d [% X, [% Y, W], Z].
Proof. by rewrite /QuadA23.d /RVar.d !DistMap.comp. Qed.

Lemma QuadA34_RV4 : QuadA34.d (RVar.d [% X, Y, Z, W]) = RVar.d [% X, Y, [% Z, W]].
Proof. by rewrite /QuadA23.d /RVar.d /QuadA34.d /TripA.d !DistMap.comp. Qed.

Lemma QuadA234_RV4 : QuadA234.d (RVar.d [% X, Y, Z, W]) = RVar.d [% X, [% Y, Z, W]].
Proof.
apply/dist_ext => -[a [[b c] d]]; rewrite QuadA234.dE !RVar.dE.
by apply eq_bigl => u; rewrite !inE; apply/eqP/eqP => -[<- <- <- <-].
Qed.

Lemma Proj14_RV4 : Proj14d (RVar.d [% X, Y, W, Z]) = RVar.d [% X, Z].
Proof.
rewrite /Proj14d /Proj13.d /Proj234.d /Proj124.d /Bivar.snd /TripA.d.
by rewrite /TripC12.d !DistMap.comp.
Qed.

Lemma Proj124_RV4 : Proj124.d (RVar.d [% X, Y, W, Z])= RVar.d [% X, Y, Z].
Proof. by rewrite /Proj124.d /RVar.d /TripA.d /Swap.d !DistMap.comp. Qed.

Lemma Proj234_RV4 :
  Proj234.d (RVar.d [% X, Y, W, Z]) = Proj23.d (RVar.d [% X, [% Y, W], Z]).
Proof.
by rewrite /Proj234.d /Proj23.d /Bivar.snd /TripA.d /TripA'.d !DistMap.comp.
Qed.

End quad_prop.

Section conditionnally_independent_discrete_random_variables.

Variables (U : finType) (P : dist U) (A B C : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).
Let Q := RVar.d [% X, Y, Z].

Local Notation "\Pr[ X '\in' P | Y '\in' Q ]" := (\Pr_(RVar.d [% X, Y])[ P | Q ]).
Local Notation "\Pr[ X = a | Y = b ]" := (\Pr[ X \in [set a] | Y \in [set b]]).

Definition cinde_drv := forall a b c,
  \Pr[ [% X, Y] = (a, b) | Z = c ] = \Pr[ X = a | Z = c ] * \Pr[ Y = b | Z = c].

End conditionnally_independent_discrete_random_variables.

Notation "\Pr[ X '\in' P | Y '\in' Q ]" := (\Pr_(RVar.d [% X, Y])[ P | Q ]).
Notation "\Pr[ X = a | Y = b ]" := (\Pr[ X \in [set a] | Y \in [set b]]).

Notation "X _|_  Y | Z" := (cinde_drv X Y Z) : proba_scope.
Notation "P |= X _|_  Y | Z" := (@cinde_drv _ P _ _ _ X Y Z) : proba_scope.

Lemma cindeP (U : finType) (P : dist U) (A B C : finType) (X : {RV P -> A}) (Y : {RV P -> B}) {Z : {RV P -> C}} a b c :
  P |= X _|_ Y | Z ->
  \Pr[ [% Y, Z] = (b, c)] != 0 ->
(*  \Pr[ Y = b | Z = c ] != 0 ->*)
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

Section cinde_drv_prop.

Variables (U : finType) (P : dist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma cinde_drv_2C : X _|_ [% Y, W] | Z -> P |= X _|_ [% W, Y] | Z.
Proof.
move=> H; move=> a -[d b] c; move: (H a (b, d) c) => {H}H.
transitivity (\Pr_(RVar.d [% X, [% Y, W], Z])[ [set (a, (b, d))] | [set c] ]).
  rewrite /cPr !snd_RV3; congr (_ / _).
  rewrite /Pr !big_setX /= !big_set1 !RVar.dE /Pr.
  apply eq_bigl => u; rewrite !inE; by apply/eqP/eqP => -[<- <- <- <-].
rewrite {}H; congr (_ * _).
rewrite /cPr !snd_RV2; congr (_ / _).
rewrite /Pr !big_setX /= !big_set1 !RVar.dE /Pr; apply eq_bigl => u.
by rewrite !inE; apply/eqP/eqP => -[<- <- <-].
Qed.

Lemma cinde_drv_3C : X _|_ Y | [% Z, W] -> X _|_ Y | [% W, Z].
Proof.
move=> H; move=> a b -[d c]; move: (H a b (c, d)) => {H}H.
transitivity (\Pr_(RVar.d [% X, Y, [% Z, W]])[[set (a, b)] | [set (c, d)]]).
  rewrite -TripA_RV3.
  rewrite -2!setX1.
  rewrite -cPr_TripA_TripC23.
  rewrite TripC23_RV3.
  rewrite -TripA_RV3.
  by rewrite -setX1.
rewrite H; congr (_ * _).
  rewrite -TripA_RV3.
  rewrite -2!setX1.
  rewrite -cPr_TripA_TripC23.
  by rewrite TripC23_RV3 -TripA_RV3.
rewrite -TripA_RV3.
rewrite -2!setX1.
rewrite -cPr_TripA_TripC23.
by rewrite TripC23_RV3 -TripA_RV3.
Qed.

End cinde_drv_prop.

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

Lemma reasoning_by_cases E F :
  \Pr_(RVar.d [% X, Y])[E | F] =
  \rsum_(z <- fin_img Z) \Pr_(RVar.d [% X, Z, Y])[setX E [set z] | F].
Proof.
by rewrite {1}/cPr total_RV2 -[in RHS]big_distrl /= (snd_RV3 _ Z).
Qed.

End reasoning_by_cases.

Lemma RV_cPrC (U : finType) (P : dist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) a b c :
  \Pr[ [% Y, X] = (b, a) | Z = c ] = \Pr[ [% X, Y] = (a, b) | Z = c ].
Proof. by rewrite -setX1 -cPr_TripC12 TripC12_RV3 setX1. Qed.

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
  \Pr[ X = a] = \Pr[ (comp_RV X f) = f a ].
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
  \Pr[ X = a ] = \Pr[ X = a | (unit_RV P) = tt].
Proof.
rewrite RV_cPrE unit_RV1 divR1.
rewrite (@RV_Pr_comp _ _ _ _ (fun a => (a, tt))); last by move=> u1 u2 -[].
done.
Qed.

Lemma RV_Pr_C (U : finType) (P : dist U) (A B : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) a b :
  \Pr[ [% Y, X] = (b, a) ] = \Pr[ [% X, Y] = (a, b)].
Proof.
by rewrite RV_Pr_cPr_unit RV_cPrC -RV_Pr_cPr_unit.
Qed.

Lemma RV_Pr_lA (U : finType) (P : dist U) (A B C D : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}) a b c d:
  \Pr[ [% X, [% Y, Z]] = (a, (b, c)) | W = d] =
  \Pr[ [% [% X, Y], Z] = ((a, b), c) | W = d].
Proof.
rewrite /cPr !snd_RV2; congr (_ / _).
rewrite (Pr_DistMap (@QuadA23.inj_f _ _ _ _)).
rewrite /RVar.d !DistMap.comp; congr Pr => //.
apply/setP => -[[a0 [b0 c0]] d0].
rewrite !inE /=.
apply/idP/idP.
  case/andP => /eqP [-> -> -> /eqP ->].
  apply/imsetP.
  exists (((a, b), c), d) => //.
  by rewrite !inE /= !eqxx.
case/imsetP => -[[[a1 b1] c1] d1].
rewrite !inE /= => /andP[/eqP [] -> -> -> /eqP ->].
case=> -> -> -> ->; by rewrite !eqxx.
Qed.

Lemma RV_Pr_A (U : finType) (P : dist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) a b c :
\Pr[ [% X, [% Y, Z]] = (a, (b, c)) ] = \Pr[ [% [% X, Y], Z] = ((a, b), c)].
Proof.
rewrite RV_Pr_cPr_unit.
rewrite RV_Pr_lA.
by rewrite -RV_Pr_cPr_unit.
Qed.

Section symmetry.

Variable (U : finType) (P : dist U).
Variables (A B C : finType) (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).

Lemma symmetry : X _|_ Y | Z -> Y _|_ X | Z.
Proof.
move=> H b a c.
rewrite /cinde_drv in H.
rewrite RV_cPrC.
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
  by rewrite [in RHS]RV_Pr_lA /cPr !setX1.
transitivity (\rsum_(d <- fin_img W)
  \Pr[ X = a | Z = c] * \Pr[ [% Y, W] = (b, d) | Z = c]).
  by apply eq_bigr => d _; rewrite H.
rewrite -big_distrr /=; congr (_ * _).
rewrite (reasoning_by_cases W); apply eq_bigr => d _.
by rewrite /cPr !setX1.
Qed.

End decomposition.

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


Lemma RV_Pr_AC (U : finType) (P : dist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) a b c :
\Pr[ [% X, Y, Z] = (a, b, c) ] = \Pr[ [% X, Z, Y] = (a, c, b)].
Proof.
rewrite -!RVar.Pr.
rewrite (Pr_DistMap TripC23.inj_f).
congr Pr.
by rewrite /RVar.d DistMap.comp.
by rewrite imset_set1.
Qed.

Lemma RV_Pr_RV2_domin_snd
(U : finType) (P : dist U) (A B : finType) (X : {RV (P) -> (A)}) (Y : {RV (P) -> (B)}) a b : \Pr[ Y = b ] = 0 -> \Pr[ [% X, Y] = (a, b) ] = 0.
Proof.
move=> H.
rewrite -RVar.Pr.
rewrite -setX1.
rewrite Pr_domin_snd //.
rewrite snd_RV2.
by rewrite RVar.Pr.
Qed.

Lemma RV_Pr_RV2_domin_fst
(U : finType) (P : dist U) (A B : finType) (X : {RV (P) -> (A)}) (Y : {RV (P) -> (B)}) a b : \Pr[ X = a ] = 0 -> \Pr[ [% X, Y] = (a, b) ] = 0.
Proof.
move=> H.
rewrite -RVar.Pr.
rewrite -setX1.
rewrite Pr_domin_fst //.
rewrite fst_RV2.
by rewrite RVar.Pr.
Qed.

Lemma RV_Pr_rA (U : finType) (P : dist U) (A B C D : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}) a b c d :
  \Pr[ X = a | [% Y, [% Z, W]] = (b, (c, d)) ] =
  \Pr[ X = a | [% Y, Z, W] = (b, c, d) ].
Proof.
by rewrite (cPr_cond TripA.inj_f) /= /RVar.d !DistMap.comp imset_set1.
Qed.

Lemma RV_Pr_rAC (U : finType) (P : dist U) (A B C D : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}) a b c d :
  \Pr[ X = a | [% Y, Z, W] = (b, c, d) ] =
  \Pr[ X = a | [% Y, W, Z] = (b, d, c) ].
Proof.
by rewrite (cPr_cond TripC23.inj_f) /= !DistMap.comp imset_set1.
Qed.

Lemma RV_Pr_rC (U : finType) (P : dist U) (A B C : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) a b c :
  \Pr[ X = a | [% Y, Z] = (b, c) ] =
  \Pr[ X = a | [% Z, Y] = (c, b) ].
Proof.
by rewrite (cPr_cond inj_swap) /RVar.d !DistMap.comp imset_set1.
Qed.

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
- by rewrite [X in _ * X = _ * X]RV_cPrE RV_Pr_RV2_domin_snd ?(div0R,mulR0).
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
  by rewrite RV_Pr_AC RV_Pr_RV2_domin_fst ?div0R ?mulR0.
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

Section cPr_1_RV.

Variables (U : finType) (P : dist U) (A B : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}).

(* NB: see also cPr_1 *)
Lemma cPr_1_RV a : (RVar.d X) a != 0 ->
  \rsum_(b <- fin_img Y) \Pr_(RVar.d [% Y, X])[ [set b] | [set a] ] = 1.
Proof.
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

Section intersection.

Variables (U : finType) (P : dist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Hypothesis Hpos : forall b c d, Pr (RVar.d [% Y, Z, W]) [set (b, c, d)] != 0.
Hypothesis D_not_empty : D.

Lemma intersection : X _|_ Y | [% Z, W] -> X _|_ W | [% Z, Y] -> X _|_ [% Y, W] | Z.
Proof.
move=> H1 H2; apply contraction => //; move=> a b c.
rewrite [in X in _ = X * _](reasoning_by_cases W).
have {H2}K1 : forall d, \Pr_(RVar.d [% X, [% Y, Z]])[[set a]|[set (b, c)]] =
       \Pr_(RVar.d [% X, [% W, Z, Y]])[[set a]|[set (d, c, b)]].
  move=> d; move: {H2}(H2 a d (c, b)).
  rewrite -setX1 product_rule Proj23_RV3 setX1.
  have /eqP H0 : \Pr_(RVar.d [% W, [% Z, Y]])[ [set d] | [set (c, b)] ] != 0.
    rewrite /cPr.
    rewrite -{1}setX1 -{1}TripA_RV3 TripA.Pr -TripC12_RV3 TripC12.Pr.
    rewrite -Swap_RV2 Swap.Pr Swap.dI -TripA_RV3 TripA.Pr 2!setX1.
    rewrite {1}/Rdiv mulR_neq0'; apply/andP; split; last first.
      rewrite invR_neq0' // snd_RV2 -setX1 Pr_RV2C setX1.
      apply: contra (Hpos b c d) => /eqP.
      by move/(Pr_RV2_domin_fst W [set d]); rewrite setX1 => ->.
    exact: Hpos.
  move/eqR_mul2r => /(_ H0){H0}.
  rewrite -QuadA34_RV4 -2!setX1 cPr_TripA_QuadA34 2!setX1 QuadA234_RV4 => ->.
  by rewrite -TripA_RV3 -setX1 -cPr_TripA_TripC23 TripC23_RV3 TripA_RV3.
have {H1}K2 : forall d, \Pr_(RVar.d [% X, [% W, Z]])[[set a]|[set (d, c)]] =
       \Pr_(RVar.d [% X, [% Y, W, Z]])[[set a]|[set (b, d, c)]].
  move=> d; move: {H1}(H1 a b (c, d)).
  rewrite -setX1 product_rule Proj23_RV3 setX1.
  have /eqP H0 : \Pr_(RVar.d [% Y, [% Z, W]])[ [set b] | [set (c, d)] ] != 0.
    rewrite /cPr -{1}TripA_RV3 -setX1 TripA.Pr 2!setX1 mulR_neq0'; apply/andP; split.
      exact/Hpos.
    rewrite invR_neq0' // snd_RV2.
    apply: contra (Hpos b c d) => /eqP/(Pr_RV2_domin_snd Y [set b]).
    by rewrite -TripA_RV3 TripA.Pr 2!setX1 => ->.
  move/eqR_mul2r => /(_ H0){H0}.
  move/esym.
  rewrite -TripA_RV3 -TripC23_RV3 -setX1 cPr_TripA_TripC23 setX1 TripA_RV3 => ->.
  rewrite -QuadA34_RV4 -2!setX1 cPr_TripA_QuadA34.
  by rewrite cPr_TripA_QuadA23_TripC23 2!setX1 TripC23_RV3 QuadA23_RV4 TripA_RV3.
have {K1 K2}K3 : forall d, \Pr_(RVar.d [% X, [% Y, Z]])[[set a]|[set (b, c)]] =
               \Pr_(RVar.d [% X, [% W, Z]])[[set a]|[set (d, c)]].
  move=> d; rewrite {K1}(K1 d) {}K2.
  rewrite -setX1 -TripA_RV3 -TripC12_RV3 cPr_TripA_TripC12.
  rewrite TripA_RV3 Swap_RV2 TripA_RV3 -QuadA234_RV4 -!setX1 -cPr_TripA_QuadA34.
  by rewrite QuadA34_RV4 TripA_RV3.
have {K3}K3 : forall d,
  \Pr_(RVar.d ([% [% X, Y], Z]))[[set (a, b)]|[set c]] / \Pr_(RVar.d [% Y, Z])[[set b]|[set c]] =
  \Pr_(RVar.d [% [% X, W], Z])[[set (a, d)]|[set c]] / \Pr_(RVar.d [% W, Z])[[set d]|[set c]].
  move=> d.
  rewrite -setX1 product_rule setX1 Proj23_RV3.
  rewrite TripA_RV3 (K3 d).
  apply/esym.
  rewrite -setX1 product_rule setX1 Proj23_RV3 TripA_RV3.
  rewrite {1}/Rdiv -mulRA mulRV; last first.
    rewrite /cPr mulR_neq0'; apply/andP; split.
      apply: contra (Hpos b c d) => /eqP Hpos'; apply/eqP.
      rewrite -2!setX1; apply Proj23.Pr_domin; by rewrite Proj23_RV3 Pr_RV2C.
    rewrite invR_neq0' //; apply: contra (Hpos b c d) => /eqP Hpos'; apply/eqP.
    rewrite -2!setX1 -TripA.Pr TripA_RV3 Pr_RV2C -TripA.Pr TripA_RV3; apply Pr_domin_fst.
    rewrite fst_RV2; by rewrite snd_RV2 in Hpos'.
  rewrite {1}/Rdiv -[in RHS]mulRA mulRV //.
  rewrite /cPr.
  rewrite snd_RV2 mulR_neq0'; apply/andP; split.
    apply: contra (Hpos b c d) => /eqP ?.
    by rewrite -setX1; apply/eqP/Pr_domin_fst; rewrite -setX1 fst_RV2.
  rewrite invR_neq0' //.
  move: (Hpos b c d); apply: contra => ?.
  rewrite -2!setX1.
  apply/eqP/Pr_domin_fst/Pr_domin_snd.
  rewrite fst_RV2 snd_RV2; exact/eqP.
have {K3}K3 :
  \rsum_(d <- fin_img W)
    \Pr_(RVar.d ([% [% X, Y], Z]))[[set (a, b)]|[set c]] * \Pr_(RVar.d [% W, Z])[[set d]|[set c]] =
  \rsum_(d <- fin_img W)
    \Pr_(RVar.d [% [% X, W], Z])[setX [set a] [set d]|[set c]] * \Pr_(RVar.d [% Y, Z])[[set b]|[set c]].
  apply eq_bigr => d _.
  rewrite -eqR_divr_mulr; last first.
    rewrite /cPr mulR_neq0'; apply/andP; split.
      apply: contra (Hpos b c d); rewrite -!setX1 => /eqP ?.
      by apply/eqP/Pr_domin_fst; rewrite fst_RV2.
    rewrite invR_neq0' //.
    apply: contra (Hpos b c d); rewrite snd_RV2 => /eqP ?.
    rewrite -!setX1; apply/eqP/Pr_domin_fst/Pr_domin_snd; by rewrite fst_RV2 snd_RV2.
  rewrite {1}/Rdiv.
  rewrite mulRAC.
  rewrite -/(Rdiv _ _).
  rewrite (K3 d).
  rewrite mulRAC.
  rewrite eqR_divr_mulr; last first.
    rewrite /cPr mulR_neq0'; apply/andP; split.
      rewrite Pr_RV2C; apply: contra (Hpos b c d) => /eqP ?.
      rewrite -!setX1; apply/eqP; rewrite -TripA.Pr; apply Pr_domin_snd.
      by rewrite TripA_RV3 snd_RV2.
    rewrite invR_neq0' // snd_RV2.
    apply: contra (Hpos b c d) => /eqP ?.
    rewrite -2!setX1 Pr_RV2C -TripA_RV3 TripA.Pr.
    apply/eqP/Pr_domin_snd.
    by rewrite snd_RV2.
  by rewrite setX1.
move: K3.
rewrite -big_distrr /=.
rewrite -[in X in _ = X -> _]big_distrl /=.
move=> <-.
rewrite cPr_1_RV ?mulR1 //.
rewrite -Pr_set1.
apply: contra (Hpos b c D_not_empty) => /eqP ?.
rewrite -!setX1.
apply/eqP/Pr_domin_fst/Pr_domin_snd.
by rewrite fst_RV2 snd_RV2.
Qed.

End intersection.
