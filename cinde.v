From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.
Require Import cproba.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* tentative formalization of conditional independence *)

Reserved Notation "X @= x" (at level 10).
Reserved Notation "X _|_  Y | Z" (at level 10, Y, Z at next level).
Reserved Notation "P |= X _|_  Y | Z" (at level 10, X, Y, Z at next level).
Reserved Notation "'[%' x , y , .. , z ']'" (at level 0,
  format "[%  x ,  y ,  .. ,  z ]").
Reserved Notation "{ 'RV' d -> T }" (at level 0, d, T at next level).

Notation "X @= x" := ([set h | X h == x]) : proba_scope.

Local Open Scope proba_scope.

Module Proj124.
Section def.
Variables (A B D C : finType) (P : {dist A * B * D * C}).
Definition f (abc : A * B * C) := \rsum_(x in D) P (abc.1.1, abc.1.2, x, abc.2).
Lemma f0 x : 0 <= f x. Proof. apply rsumr_ge0 => ? _; exact: dist_ge0. Qed.
Lemma f1 : \rsum_(x in {: A * B * C}) f x = 1.
Proof.
rewrite /f -(pmf1 P) /= pair_big /=.
rewrite (reindex (fun x => let: (a, b, c, d) := x in ((a, b, d), c))) /=; last first.
  exists (fun x => let: (a, b, d, c) := x in ((a, b, c), d)).
  by move=> -[[[]]].
  by move=> -[[[]]].
by apply eq_bigr => -[[[]]] *.
Qed.
Definition d : {dist A * B * C} := locked (makeDist f0 f1).
Lemma dE abc: d abc = \rsum_(x in D) P (abc.1.1, abc.1.2, x, abc.2).
Proof. by rewrite /d; unlock. Qed.
End def.
Section prop.
Variables (A B D C : finType) (P : {dist A * B * D * C}).
Lemma snd : Bivar.snd (Proj124.d P) = Bivar.snd P.
Proof.
apply/dist_ext => d.
rewrite 2!Bivar.sndE /=.
rewrite (eq_bigr (fun i => P (i.1, i.2, d))); last by case.
rewrite -(pair_bigA _ (fun i1 i2 => P (i1, i2, d))) /=.
apply eq_bigr => -[a b] _.
by rewrite dE; apply eq_bigr => c _.
Qed.
End prop.
End Proj124.

Definition Proj14d (A B C D : finType) (d : {dist A * B * D * C}) : {dist A * C} :=
  Proj13.d (Proj124.d d).

Module Proj234.
Section def.
Variables (A B D C : finType) (P : {dist A * B * C * D}).
Definition f (abc : B * C * D) := \rsum_(x in A) P (x, abc.1.1, abc.1.2, abc.2).
Lemma f0 x : 0 <= f x. Proof. apply rsumr_ge0 => ? _; exact: dist_ge0. Qed.
Lemma f1 : \rsum_(x in {: B * C * D}) f x = 1.
Proof.
rewrite -(pmf1 P) /=.
rewrite pair_big /=.
rewrite (reindex (fun x => let: (a, b, c, d) := x in (b, c, d, a))) /=; last first.
  exists (fun x => let: (b, c, d, a) := x in (a, b, c, d)).
  by move=> -[] [] [].
  by move=> -[] [] [].
by apply eq_bigr => -[[] []].
Qed.
Definition d : {dist B * C * D} := locked (makeDist f0 f1).
Lemma dE abc: d abc = \rsum_(x in A) P (x, abc.1.1, abc.1.2, abc.2).
Proof. by rewrite /d; unlock. Qed.
End def.
End Proj234.

Module QuadA23.
Section def.
Variables (A B C D : finType) (P : {dist A * B * D * C}).
Let g (x : A * (B * D) * C) := let: (a, (b, d), c) := x in (a, b, d, c).
Definition f (x : A * (B * D) * C) :=  P (g x).
Lemma f0 x : 0 <= f x.
Proof. move: x => -[[] ? [] ? ? ?]; exact/dist_ge0. Qed.
Lemma f1 : \rsum_(x in {: A * (B * D) * C}) f x = 1.
Proof.
rewrite /f -(pmf1 P) /= (reindex g) /=; last first.
  exists (fun x => let: (a, b, d, c) := x in (a, (b, d), c)).
  by move=> -[[] ? [] ? ? ?].
  by move=> -[[] [] ? ? ? ?].
by apply eq_bigr => -[[] ? [] ? ? ?].
Qed.
Definition d : {dist A * (B * D) * C} := locked (makeDist f0 f1).
Lemma dE x : d x = P (g x).
Proof. by rewrite /d /g; unlock => /=. Qed.
End def.
Section prop.
Variables (A B C D : finType) (P : {dist A * B * D * C}).
Lemma snd : Bivar.snd (QuadA23.d P) = Bivar.snd P.
Proof.
apply/dist_ext => c; rewrite 2!Bivar.sndE /=.
rewrite (reindex (fun x => let: (a, b, d) := x in (a, (b, d)))) /=; last first.
  exists (fun x => let: (a, (b, d)) := x in (a, b, d)).
  by move=> -[] [].
  by move=> -[] ? [].
apply eq_bigr => -[[]] a b d _; by rewrite dE.
Qed.
End prop.
End QuadA23.

Module QuadA34.
Section def.
Variables (A B C D : finType) (P : {dist A * B * D * C}).
Let g (x : A * B * (D * C)) := let: (a, b, (d, c)) := x in (a, b, d, c).
Definition f (x : A * B * (D * C)) :=  P (g x).
Lemma f0 x : 0 <= f x.
Proof. move: x => -[[] ? ? [] ? ?]; exact/dist_ge0. Qed.
Lemma f1 : \rsum_(x in {: A * B * (D * C)}) f x = 1.
Proof.
rewrite /f -(pmf1 P) /= (reindex g) /=; last first.
  exists (fun x => let: (a, b, d, c) := x in (a, b, (d, c))).
  by move=> -[[] ? ? [] ? ?].
  by move=> -[[] [] ? ? ? ?].
by apply eq_bigr => -[[] ? ? [] ? ?].
Qed.
Definition d : {dist A * B * (D * C)} := locked (makeDist f0 f1).
Lemma dE x : d x = P (g x).
Proof. by rewrite /d /g; unlock => /=. Qed.
End def.
End QuadA34.

Module QuadA234.
Section def.
Variables (A B C D : finType) (P : {dist A * B * D * C}).
Let g (x : A * (B * D * C)) := let: (a, (b, d, c)) := x in (a, b, d, c).
Definition f (x : A * (B * D * C)) :=  P (g x).
Lemma f0 x : 0 <= f x.
Proof. move: x => -[? [] [] ? ? ?]; exact/dist_ge0. Qed.
Lemma f1 : \rsum_(x in {: A * (B * D * C)}) f x = 1.
Proof.
rewrite /f -(pmf1 P) /= (reindex g) /=; last first.
  exists (fun x => let: (a, b, d, c) := x in (a, (b, d, c))).
  by move=> -[? [] [] ? ? ?].
  by move=> -[[] [] ? ? ? ?].
by apply eq_bigr => -[? [] [] ? ?].
Qed.
Definition d : {dist A * (B * D * C)} := locked (makeDist f0 f1).
Lemma dE x : d x = P (g x).
Proof. by rewrite /d /g; unlock => /=. Qed.
End def.
End QuadA234.

Section QuadA_prop.
Variables (A B C D : finType) (P : {dist A * B * C * D}).

Lemma cPr_TripA_QuadA34 E F G H :
  \Pr_(TripA.d (QuadA34.d P))[ E | setX F (setX G H) ] =
  \Pr_(QuadA234.d P)[ E | setX (setX F G) H ].
Proof.
rewrite /cPr.
congr (_ / _).
  rewrite TripA.Pr /Pr !big_setX /=; apply eq_bigr => a _.
  rewrite !big_setX /=; apply eq_bigr => b _; rewrite big_setX /=.
  apply/eq_bigr => c _; apply eq_bigr => d _.
  by rewrite QuadA34.dE QuadA234.dE.
rewrite /Pr !big_setX /=; apply eq_bigr => b _.
rewrite !big_setX /=; apply eq_bigr => c _.
apply eq_bigr=> d _.
rewrite !Bivar.sndE; apply eq_bigr => a _.
by rewrite TripA.dE QuadA234.dE QuadA34.dE.
Qed.

End QuadA_prop.

Definition RV {U : finType} (P : dist U) (A : finType) := U -> A.

Definition RV_of {U : finType} (P : dist U) {A : finType} :=
  fun phT : phant (Finite.sort A) => @RV U P A.

Notation "{ 'RV' d -> T }" := (RV_of d (Phant T)) : proba_scope.

Module RVar.
Section def.
Variables (U A : finType) (P : dist U) (X : {RV P -> A}).
Definition f a := Pr P (X @= a).
Lemma f0 a : 0 <= f a. Proof. exact/Pr_ge0. Qed.
Lemma f1 : \rsum_(a in A) (f a) = 1.
Proof.
rewrite /f /Pr -(pmf1 P) (sum_parti_finType _ X) /=.
rewrite (bigID (fun x => x \in fin_img X)) /=.
rewrite [X in _ + X = _](eq_bigr (fun=> 0)); last first.
  move=> a aX; rewrite big1 // => u; rewrite inE => /eqP Xua.
  move: aX; rewrite /fin_img mem_undup.
  case/mapP; exists u => //; by rewrite mem_enum.
rewrite big_const iter_addR mulR0 addR0 big_uniq /=; last exact: undup_uniq.
apply eq_bigr => a aX; by apply eq_bigl => u; rewrite inE.
Qed.
Definition d : {dist A} := locked (makeDist f0 f1).
Lemma dE a : d a = Pr P (X @= a). Proof. by rewrite /d; unlock. Qed.
End def.
End RVar.

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

Lemma marginal_RV2_1 a :
  \rsum_(u in X @= a) P u = \rsum_(b in B) (RVar.d [% X, Y]) (a, b).
Proof.
have -> : (X @= a) = \bigcup_b [% X, Y] @= (a, b).
  apply/setP=> u; rewrite !inE; apply/eqP/bigcupP.
  by case=> <- /=; exists (Y u) => //; rewrite inE.
  by case=> b _; rewrite inE => /eqP[] <- ?.
rewrite partition_disjoint_bigcup /=; last first.
  move=> b0 b1 b01; rewrite -setI_eq0; apply/eqP/setP => u; rewrite !inE.
  apply/negbTE/negP => /andP[] /eqP[<- Yub0] /eqP -[].
  rewrite Yub0; exact/eqP.
apply eq_bigr => b _; by rewrite RVar.dE.
Qed.

Lemma marginal_RV2_2 b :
  \rsum_(u in Y @= b) P u = \rsum_(a in A) (RVar.d [% X, Y]) (a, b).
Proof.
have -> : (Y @= b) = \bigcup_a [% X, Y] @= (a, b).
  apply/setP => u; rewrite !inE; apply/eqP/bigcupP.
  by case=> <- /=; exists (X u) => //; rewrite inE.
  by case=> a _; rewrite inE => /eqP[] ? <-.
rewrite partition_disjoint_bigcup /=; last first.
  move=> a0 a1 a01; rewrite -setI_eq0; apply/eqP/setP => u; rewrite !inE.
  apply/negbTE/negP => /andP[] /eqP[Xua0 <-] /eqP -[].
  rewrite Xua0; exact/eqP.
by apply eq_bigr => a _; by rewrite RVar.dE.
Qed.

Lemma marginal_RV3_1 b c :
  \rsum_(u in [% Y, Z] @= (b, c)) P u =
  \rsum_(d in D) (RVar.d [% W, Y, Z] (d, b, c)).
Proof.
have -> : ([% Y, Z] @= (b, c)) = \bigcup_d [% W, Y, Z] @= (d, b, c).
  apply/setP => u; rewrite !inE; apply/eqP/bigcupP.
  by case=> <- <- /=; exists (W u) => //; rewrite inE.
  by case=> d _; rewrite inE => /eqP[] ? <- <-.
rewrite partition_disjoint_bigcup /=; last first.
  move=> d0 d1 d01; rewrite -setI_eq0; apply/eqP/setP => u; rewrite !inE.
  apply/negbTE/negP => /andP[] /eqP[Wud0 <- <-] /eqP -[].
  rewrite Wud0; exact/eqP.
by apply eq_bigr => d _; rewrite RVar.dE.
Qed.

Lemma marginal_RV3_2 b c :
  \rsum_(u in [% Y, Z] @= (b, c)) P u =
  \rsum_(d in D) (RVar.d [% Y, W, Z]) (b, d, c).
Proof.
have -> : ([% Y, Z] @= (b, c)) = \bigcup_d [% Y, W, Z] @= (b, d, c).
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
  \rsum_(u in [% Y, Z] @= (b, c)) P u =
  \rsum_(d in D) (RVar.d [% Y, Z, W]) (b, c, d).
Proof.
have -> : ([% Y, Z] @= (b, c)) = \bigcup_d [% Y, Z, W] @= (b, c, d).
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
  \rsum_(u in [% X, Y, Z] @= (a, b, c)) P u =
  \rsum_(d in D) (RVar.d [% W, X, Y, Z]) (d, a, b, c).
Proof.
have -> : ([% X, Y, Z] @= (a, b, c)) = \bigcup_d [% W, X, Y, Z] @= (d, a, b, c).
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
  \rsum_(u in [% X, Y, Z] @= (a, b, c)) P u =
  \rsum_(d in D) (RVar.d [% X, Y, W, Z]) (a, b, d, c).
Proof.
have -> : ([% X, Y, Z] @= (a, b, c)) = \bigcup_d [% X, Y, W, Z] @= (a, b, d, c).
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
  \rsum_(u in [% X, Y, Z] @= (a, b, c)) P u =
  \rsum_(d in D) (RVar.d [% X, Y, Z, W]) (a, b, c, d).
Proof.
have -> : ([% X, Y, Z] @= (a, b, c)) = \bigcup_d [% X, Y, Z, W] @= (a, b, c, d).
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
Proof.
apply/dist_ext => ?; by rewrite Bivar.fstE RVar.dE /Pr -marginal_RV2_1.
Qed.

Lemma snd_RV2 : Bivar.snd (RVar.d [% X, Y]) = RVar.d Y.
Proof.
apply/dist_ext => ?; by rewrite Bivar.sndE RVar.dE /Pr (marginal_RV2_2 X).
Qed.

Lemma Pr_RV2_domin_fst E F : Pr (RVar.d X) E = 0 ->
  Pr (RVar.d [% X, Y]) (setX E F) = 0.
Proof. move=> H; apply Pr_fst_eq0; by rewrite fst_RV2. Qed.

Lemma Pr_RV2_domin_snd a b : Pr (RVar.d Y) b = 0 ->
  Pr (RVar.d [% X, Y]) (setX a b) = 0.
Proof. move=> H; apply Pr_snd_eq0; by rewrite snd_RV2. Qed.

End RV2_prop.

Section RV3_prop.
Variables (U : finType) (P : dist U).
Variables (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma snd_TripA_RV3 :
  Bivar.snd (TripA.d (RVar.d [% X, Y, Z])) = RVar.d [% Y, Z].
Proof.
apply/dist_ext => -[b c].
rewrite Bivar.sndE RVar.dE /Pr (marginal_RV3_1 X).
by apply eq_bigr => a _; rewrite TripA.dE.
Qed.

Lemma snd_TripA_RV4 :
  Bivar.snd (TripA.d (RVar.d [% X, [% Y, W],  Z])) = RVar.d [% Y, W, Z].
Proof.
apply/dist_ext => -[[b d c]].
rewrite Bivar.sndE RVar.dE /Pr (marginal_RV4_1 X); apply/eq_bigr => a _.
rewrite TripA.dE /= !RVar.dE /Pr; apply eq_bigl => u.
by rewrite !inE; apply/eqP/eqP => -[<- <- <- <-].
Qed.

Lemma Proj13_RV3 : Proj13.d (RVar.d [% X, Y, Z]) = RVar.d [% X, Z].
Proof.
apply/dist_ext => -[a c].
by rewrite Proj13.dE RVar.dE /Pr /= (marginal_RV3_2 Y).
Qed.

Lemma snd_RV3 : Bivar.snd (RVar.d [% X, Y, Z]) = Bivar.snd (RVar.d [% X, Z]).
Proof. by rewrite -Proj13.snd Proj13_RV3. Qed.

Lemma Proj23_RV3 : Proj23.d (RVar.d [% X, Y, Z]) = RVar.d [% Y, Z].
Proof. by rewrite Proj23.def snd_TripA_RV3. Qed.

End RV3_prop.

Section trip_prop.
Variable (U : finType) (Q : dist U).
Variables (A B C : finType) (X : {RV Q -> A}) (Y : {RV Q -> B}) (Z : {RV Q -> C}).
Let P := RVar.d [% X, Y, Z].
Lemma TripC12_RV3 : TripC12.d P = RVar.d [% Y, X, Z].
Proof.
apply/dist_ext => -[[b a] c]; rewrite TripC12.dE /= !RVar.dE.
congr (Pr _ _); apply/setP => u; rewrite !inE; rewrite /RV2.
by apply/idP/idP => /eqP -[-> -> ->].
Qed.
End trip_prop.

Section quad_prop.
Variables (U : finType) (P : dist U).
Variables (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma Proj124_RV4 : Proj124.d (RVar.d [% X, Y, W, Z])= RVar.d [% X, Y, Z].
Proof.
apply/dist_ext => -[[a b] c].
by rewrite Proj124.dE /= RVar.dE /= {1}/Pr -marginal_RV4_3.
Qed.

Lemma Proj14_Rvar4 : (RVar.d [% X, Z]) = Proj14d (RVar.d [% X, Y, W, Z]).
Proof.
rewrite /Proj14d; apply/dist_ext => -[a c].
rewrite !Proj13.dE /= RVar.dE {1}/Pr (marginal_RV3_2 Y); apply eq_bigr => b _.
by rewrite RVar.dE {1}/Pr Proj124.dE (marginal_RV4_3 W); apply eq_bigr.
Qed.

Lemma QuadA12d_RV4 : QuadA23.d (RVar.d [% X, Y, W, Z]) = RVar.d [% X, [% Y, W], Z].
Proof.
apply/dist_ext => -[] [] ? [] ? ? ?.
rewrite QuadA23.dE /= !RVar.dE; congr Pr.
apply/setP => u.
rewrite !inE /RV2 /= /RV2.
apply/eqP/eqP; by move=> -[] <- <- <- <-.
Qed.

Lemma Proj234_RV4 :
  Proj234.d (RVar.d [% X, Y, W, Z]) = Proj23.d (RVar.d [% X, [% Y, W], Z]).
Proof.
rewrite -QuadA12d_RV4.
apply/dist_ext => -[[] b d c].
rewrite Proj23.dE Proj234.dE; apply eq_bigr => a _ /=.
by rewrite !(RVar.dE,QuadA23.dE).
Qed.

Lemma QuadA34_RV4 :
  QuadA34.d (RVar.d [% X, Y, Z, W]) = RVar.d [% X, Y, [% Z, W]].
Proof.
apply/dist_ext => -[[a0 b0] [c0 d0]].
rewrite !(RVar.dE,QuadA34.dE).
rewrite /Pr; apply eq_bigl => u; rewrite !inE.
by apply/eqP/eqP => -[<- <- <- <-].
Qed.

Lemma QuadA234_RV4 :
  QuadA234.d (RVar.d [% X, Y, Z, W]) = RVar.d [% X, [% Y, Z, W]].
Proof.
apply/dist_ext => -[a0 [[b0 c0] d0]].
rewrite !(RVar.dE,QuadA234.dE).
rewrite /Pr; apply eq_bigl => u; rewrite !inE.
by apply/eqP/eqP => -[<- <- <- <-].
Qed.

End quad_prop.

Section conditionnally_independent_discrete_random_variables.

Variables (U : finType) (P : dist U) (A B C : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).
Let Q := RVar.d [% X, Y, Z].

Definition cinde_drv := forall a b c,
  \Pr_Q[ [set (a, b)] | [set c] ] =
  \Pr_(Proj13.d Q) [ [set a] | [set c] ] * \Pr_(Proj23.d Q) [ [set b] | [set c] ].

End conditionnally_independent_discrete_random_variables.

Notation "X _|_  Y | Z" := (cinde_drv X Y Z) : proba_scope.
Notation "P |= X _|_  Y | Z" := (@cinde_drv _ P _ _ _ X Y Z) : proba_scope.

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
rewrite {}H 2!Proj13_RV3 2!Proj23_RV3; congr (_ * _).
rewrite /cPr !snd_RV2; congr (_ / _).
rewrite /Pr !big_setX /= !big_set1 !RVar.dE /Pr; apply eq_bigl => u.
by rewrite !inE; apply/eqP/eqP => -[<- <- <-].
Qed.

Lemma cinde_drv_3C : X _|_ Y | [% Z, W] -> X _|_ Y | [% W, Z].
Proof.
move=> H; move=> a b -[d c]; move: (H a b (c, d)) => {H}.
rewrite 2!Proj13_RV3 2!Proj23_RV3 => H.
Admitted.

End cinde_drv_prop.

Section reasoning_by_cases_RV2.

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
rewrite RVar.dE /Pr (marginal_RV3_2 Z).
rewrite [in RHS](bigID (fun x => x \in fin_img Z)) /=.
rewrite [X in _ = _ + X ](eq_bigr (fun=> 0)); last first.
  move=> d dZ.
  rewrite RVar.dE /= /Pr (eq_bigl (fun=> false)) ?big_pred0 // => a0.
  rewrite !inE; apply/negbTE.
  apply: contra dZ => /eqP -[? <- ?].
  rewrite mem_undup; apply/mapP; exists a0 => //; by rewrite mem_enum.
rewrite big_const iter_addR mulR0 addR0 big_uniq /=; last exact: undup_uniq.
apply eq_bigr => c cZ; by rewrite big_set1 !RVar.dE.
Qed.

Lemma reasoning_by_cases_RV2 E F :
  \Pr_(RVar.d [% X, Y])[E | F] =
  \rsum_(z <- fin_img Z) \Pr_(RVar.d [% X, Z, Y])[setX E [set z] | F].
Proof.
by rewrite {1}/cPr total_RV2 -[in RHS]big_distrl /= (snd_RV3 _ Z).
Qed.

End reasoning_by_cases_RV2.

Section symmetry.

Variable (U : finType) (P : dist U).
Variables (A B C : finType) (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).

Lemma symmetry : X _|_ Y | Z -> Y _|_ X | Z.
Proof.
rewrite /cinde_drv => /= H b a c.
rewrite mulRC.
have -> : Proj23.d (RVar.d [% Y, X, Z]) = Proj13.d (RVar.d [% X, Y, Z]).
  by rewrite Proj23_RV3 Proj13_RV3.
have -> : Proj13.d (RVar.d [% Y, X, Z]) = Proj23.d (RVar.d [% X, Y, Z]).
  by rewrite Proj13_RV3 Proj23_RV3.
rewrite Pr_TripC12 TripC12_RV3.
rewrite -H.
congr cPr.
apply/setP => -[a0 b0]; rewrite !inE.
apply/imsetP/idP.
- by case => -[b1 a1]; rewrite inE => /eqP -[-> ->] ->.
- by case/eqP => -> ->; exists (b, a) => //; rewrite inE.
Qed.

End symmetry.

Section decomposition.

Variables (U : finType) (P : dist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).
Let Q := RVar.d [% X, Y, W, Z].

Lemma decomposition : X _|_ [% Y, W] | Z -> X _|_ Y | Z.
Proof.
move=> H; rewrite /cinde_drv => a b c /=.
transitivity (\rsum_(d <- fin_img W)
    \Pr_(QuadA23.d Q) [ setX [set a] (setX [set b] [set d]) | [set c] ]).
  rewrite (reasoning_by_cases_RV2 W); apply eq_bigr => /= d _.
  rewrite !setX1.
  rewrite /cPr; congr (_ / _).
  - by rewrite /Pr !(big_setX,big_set1) /= !(RVar.dE,QuadA23.dE).
  - by rewrite QuadA23.snd.
transitivity (\rsum_(d <- fin_img W)
  \Pr_(Proj14d Q)[ [set a] | [set c] ] *
  \Pr_(Proj234.d Q)[ (setX [set b] [set d]) | [set c] ]).
  apply eq_bigr => d _.
  rewrite QuadA12d_RV4.
  rewrite 2!setX1.
  rewrite H.
  rewrite Proj13_RV3.
  rewrite Proj23_RV3.
  rewrite -Proj14_Rvar4.
  by rewrite Proj234_RV4 Proj23_RV3.
rewrite -big_distrr /=; congr (_ * _).
  by rewrite /Proj14d Proj124_RV4.
rewrite Proj23_RV3.
rewrite (reasoning_by_cases_RV2 W).
apply eq_bigr => d _.
by rewrite Proj234_RV4 Proj23_RV3.
Qed.

End decomposition.

Section weak_union.

Variables (U : finType) (P : dist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma weak_union : X _|_ [% Y, W] | Z -> X _|_ Y | [% Z, W].
Proof.
move=> H; move=> a b -[c d].
rewrite Proj13_RV3.
rewrite Proj23_RV3.
transitivity (
  \Pr_(RVar.d [% X, [% Y, Z, W]]) [ [set a] | [set (b, c, d)] ] *
  \Pr_(RVar.d [% Y, [% Z, W]]) [ [set b] | [set (c, d)] ]).
  rewrite -2!setX1.
  rewrite product_rule.
  rewrite -QuadA34_RV4.
  rewrite cPr_TripA_QuadA34.
  rewrite QuadA34_RV4.
  rewrite Proj23_RV3.
  rewrite !setX1.
  by rewrite QuadA234_RV4.
transitivity (\Pr_(RVar.d [% X, Z])[ [set a] | [set c] ] *
  \Pr_(RVar.d [% Y, [% Z,  W]]) [ [set b] | [set (c, d)] ]).
  move: (H a (b, d) c) => {H}; rewrite Proj13_RV3 Proj23_RV3.
  rewrite -!setX1.
  case/boolP : (\Pr_(RVar.d [% W, Z])[ [set d] | [set c] ] == 0) => Htmp.
    move=> _.
    move: Htmp.
    rewrite {1}/cPr snd_RV2 => /eqP; rewrite mulR_eq0 => -[].
      move=> Htmp.
      rewrite {2 4}/cPr.
      by rewrite Pr_RV2_domin_snd ?div0R ?mulR0 // Pr_RV2C.
    move/eqP/invR_eq0/eqP => Htmp.
    rewrite {2 4}/cPr.
    by rewrite Pr_RV2_domin_snd ?div0R ?mulR0 // Pr_RV2_domin_fst.
  rewrite product_rule Proj23_RV3.
  rewrite product_rule Proj23_RV3.
  rewrite [in X in X = _ -> _]mulRA.
  rewrite [in X in _ = X -> _]mulRA.
  rewrite eqR_mul2r; last exact/eqP.
  move=> H.
  transitivity (
    \Pr_(TripA.d (RVar.d [% X, [% Y, W], Z]))[ [set a] | (setX (setX [set b] [set d]) [set c]) ] *
    \Pr_(TripA.d (RVar.d [% Y, W, Z]))[ [set b] | (setX [set d] [set c]) ]).
    congr (_ * _).
      rewrite /cPr.
      rewrite snd_RV2.
      rewrite snd_TripA_RV3.
      congr (_ / _).
        rewrite /Pr !(big_setX,big_set1) /= TripA.dE /= !RVar.dE.
        by rewrite /Pr; apply eq_bigl => w0; rewrite !inE; apply/eqP/eqP => -[<- <- <- <-].
      rewrite /Pr !(big_setX,big_set1) /= !RVar.dE /Pr.
      by apply eq_bigl => w0; rewrite !inE; apply/eqP/eqP => -[<- <- <-].
    rewrite /cPr; congr (_ / _).
      rewrite /Pr !(big_setX,big_set1) TripA.dE /= !RVar.dE /Pr.
      by apply eq_bigl => w0; rewrite !inE; apply/eqP/eqP => -[<- <- <-].
    rewrite /Pr !(big_setX,big_set1) !Bivar.sndE; apply eq_bigr => b0 _.
    rewrite TripA.dE /= !RVar.dE /Pr; apply eq_bigl => u.
    by rewrite !inE; apply/eqP/eqP => -[<- <- <-].
  rewrite {}H; congr (_ * _).
  rewrite /cPr.
  rewrite snd_RV2.
  rewrite snd_TripA_RV3.
  congr (_ * / _).
    rewrite /Pr !(big_setX,big_set1) TripA.dE /=.
    rewrite !RVar.dE /Pr; apply eq_bigl => w0; rewrite !inE.
    by apply/eqP/eqP => -[<- <- <-].
  by rewrite Pr_RV2C.
have {H}H : X _|_ W | Z by move/cinde_drv_2C : H; apply decomposition.
case/boolP : (\Pr_(RVar.d [% W, Z])[ [set d] | [set c] ] == 0) => [|Htmp].
  rewrite {1}/cPr.
  rewrite snd_RV2.
  move/eqP.
  rewrite mulR_eq0 => -[].
    move=> Htmp.
    rewrite /cPr !snd_RV2.
    rewrite Pr_RV2C in Htmp.
    have : Pr (RVar.d [% Y, [% Z, W] ]) (setX [set b] [set (c, d)]) = 0.
      apply Pr_RV2_domin_snd.
      by rewrite -setX1.
    by move=> ->; rewrite !div0R !mulR0.
  move/eqP/invR_eq0 => /eqP Htmp.
  rewrite /cPr !snd_RV2.
  have : Pr (RVar.d [% Y, [% Z, W]]) (setX [set b] [set (c, d)]) = 0.
    apply Pr_RV2_domin_snd.
    rewrite -setX1.
    by apply Pr_RV2_domin_fst.
  move=> ->.
  by rewrite !div0R !mulR0.
congr (_ * _).
move: (H a d c); rewrite Proj13_RV3 Proj23_RV3.
rewrite -setX1 product_rule Proj23_RV3.
rewrite eqR_mul2r; last exact/eqP.
move=> <-.
rewrite /cPr !snd_RV2.
rewrite snd_TripA_RV3 Pr_RV2C; congr (_ / _).
  rewrite /Pr !(big_setX,big_set1) TripA.dE /= !RVar.dE /Pr.
  by apply eq_bigl => w0; rewrite !inE; apply/eqP/eqP => -[<- <- <-].
by rewrite setX1.
Qed.

End weak_union.

Section contraction.

Variables (U : finType) (P : dist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma contraction : X _|_ W | [% Z, Y] -> X _|_ Y | Z -> X _|_ [% Y, W] | Z.
Proof.
move=> H1 H2; move=> a -[b d] c.
rewrite Proj13_RV3 Proj23_RV3.
rewrite -setX1 product_rule Proj23_RV3.
transitivity (
  \Pr_(TripA.d (RVar.d [%X, Y, Z]))[ [set a] | (setX [set b] [set c]) ] *
  \Pr_(RVar.d [%Y, W, Z])[ [set (b, d)] | [set c] ]
).
  move: {H1}(H1 a d (c, b)).
  rewrite Proj13_RV3 Proj23_RV3.
  rewrite -!setX1 product_rule Proj23_RV3 => H1.
  rewrite product_ruleC Proj13_RV3.
  rewrite mulRA.
  transitivity (
    \Pr_(TripA.d (RVar.d [%X, W, [%Z, Y]]))[ [set a] | (setX [set d] (setX [set c] [set b])) ] *
    \Pr_(RVar.d [%W, [%Z, Y]])[ [set d] | (setX [set c] [set b]) ] *
    \Pr_(RVar.d [%Y, Z])[ [set b] | [set c] ]).
    congr (_ * _ * _).
      rewrite -QuadA34_RV4 cPr_TripA_QuadA34 QuadA234_RV4.
      rewrite /cPr.
      congr (_ / _).
        rewrite TripA.Pr.
        rewrite /Pr !(big_setX,big_set1).
        rewrite !RVar.dE.
        rewrite /Pr; apply eq_bigl => w0.
        by rewrite !inE; apply/eqP/eqP => -[<- <- <- <-].
      rewrite snd_TripA_RV3.
      rewrite /Pr.
      rewrite !(big_setX,big_set1).
      rewrite Bivar.sndE.
      rewrite RVar.dE.
      rewrite /Pr.
      rewrite -marginal_RV2_2.
      apply eq_bigl => w0.
      by rewrite !inE; apply/eqP/eqP => -[<- <- <-].
    rewrite /cPr.
    congr (_ / _).
      rewrite TripA.Pr.
      rewrite /Pr.
      rewrite !(big_setX,big_set1) /=.
      rewrite TripC12.dE /= !RVar.dE /Pr.
      apply eq_bigl => u.
      by rewrite !inE; apply/eqP/eqP => -[<- <- <-].
    rewrite -Proj13.def.
    rewrite snd_RV2.
    rewrite Proj13_RV3.
    by rewrite Pr_RV2C.
  rewrite {}H1.
  rewrite mulRA.
  congr (_ * _ * _).
    rewrite /cPr.
    congr (_ / _).
      rewrite /Pr.
      rewrite !(big_setX, big_set1) TripA.dE /=.
      rewrite !RVar.dE /Pr.
      apply eq_bigl => w0.
      by rewrite !inE; apply/eqP/eqP => -[<- <- <-].
    rewrite snd_RV2.
    rewrite -Proj23.def.
    rewrite Proj23_RV3.
    by rewrite Pr_RV2C.
  rewrite /cPr.
  congr (_ / _).
    rewrite /Pr.
    rewrite !(big_setX,big_set1) TripA.dE TripC12.dE /= !RVar.dE /Pr.
    apply eq_bigl => u.
    by rewrite !inE; apply/eqP/eqP => -[<- <- <-].
  rewrite snd_RV2.
  rewrite -Proj13.def.
  by rewrite Proj13_RV3 Pr_RV2C.
move: {H2}(H2 a b c).
rewrite Proj13_RV3.
rewrite Proj23_RV3.
rewrite -setX1.
rewrite product_rule.
rewrite Proj23_RV3 => H2.
rewrite -setX1.
rewrite product_ruleC.
rewrite Proj13_RV3.
rewrite mulRCA H2.
by rewrite mulRCA.
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

Require Import chap2.

Section cPr_1.

Variables (U : finType) (P : dist U) (A B : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}).

Lemma cPr_1 a : (RVar.d X) a != 0 ->
  \rsum_(b <- fin_img Y) \Pr_(RVar.d [% Y, X])[ [set b] | [set a] ] = 1.
Proof.
rewrite -{1}(snd_RV2 Y) => Xa0.
set Q := CondDist.d (RVar.d [% Y, X]) _ Xa0.
rewrite -(pmf1 Q) [in RHS](bigID (fun b => b \in fin_img Y)) /=.
rewrite [X in _ = _ + X](eq_bigr (fun=> 0)); last first.
  move=> b bY.
  rewrite /Q CondDist.dE /cPr /Pr !(big_setX,big_set1) /= snd_RV2.
  rewrite !RVar.dE /Pr big1 ?div0R // => u.
  rewrite inE => /eqP[Yub ?].
  exfalso.
  move/negP : bY; apply.
  rewrite mem_undup; apply/mapP; exists u => //; by rewrite mem_enum.
rewrite big_const iter_addR mulR0 addR0.
rewrite big_uniq; last by rewrite /fin_img undup_uniq.
apply eq_bigr => b; rewrite mem_undup => /mapP[u _ bWu].
by rewrite /Q CondDist.dE.
Qed.

End cPr_1.
