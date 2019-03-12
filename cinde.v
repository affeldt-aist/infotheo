(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
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

Reserved Notation "X _|_  Y | Z" (at level 10, Y, Z at next level).
Reserved Notation "P |= X _|_  Y | Z" (at level 10, X, Y, Z at next level).
Reserved Notation "'[%' x , y , .. , z ']'" (at level 0,
  format "[%  x ,  y ,  .. ,  z ]").

Local Open Scope proba_scope.

Module Proj124.
Section def.
Variables (A B D C : finType) (P : {dist A * B * D * C}).
Definition f := [ffun abc : A * B * C => \rsum_(x in D) P (abc.1.1, abc.1.2, x, abc.2)].
Lemma f0 x : 0 <= f x.
Proof. rewrite ffunE; apply rsumr_ge0 => ? _; exact: dist_ge0. Qed.
Lemma f1 : \rsum_(x in {: A * B * C}) f x = 1.
Proof.
rewrite /f -(epmf1 P) /=.
evar (h : A * B * C -> R); rewrite (eq_bigr h); last first.
  move=> i _; rewrite ffunE /h; reflexivity.
rewrite {}/h pair_big /=.
rewrite (reindex (fun x => let: (a, b, c, d) := x in ((a, b, d), c))) /=; last first.
  exists (fun x => let: (a, b, d, c) := x in ((a, b, c), d)).
  by move=> -[[[]]].
  by move=> -[[[]]].
by apply eq_bigr => -[[[]]] *.
Qed.
Definition d : {dist A * B * C} := locked (makeDist f0 f1).
Lemma dE abc: d abc = \rsum_(x in D) P (abc.1.1, abc.1.2, x, abc.2).
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
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
Definition f := [ffun abc : B * C * D => \rsum_(x in A) P (x, abc.1.1, abc.1.2, abc.2)].
Lemma f0 x : 0 <= f x. Proof. rewrite ffunE; apply rsumr_ge0 => ? _; exact: dist_ge0. Qed.
Lemma f1 : \rsum_(x in {: B * C * D}) f x = 1.
Proof.
rewrite -(epmf1 P) /= /f.
evar (h : B * C * D -> R); rewrite (eq_bigr h); last first.
  move=> i _; rewrite ffunE /h; reflexivity.
rewrite {}/h pair_big /=.
rewrite (reindex (fun x => let: (a, b, c, d) := x in (b, c, d, a))) /=; last first.
  exists (fun x => let: (b, c, d, a) := x in (a, b, c, d)).
  by move=> -[] [] [].
  by move=> -[] [] [].
by apply eq_bigr => -[[] []].
Qed.
Definition d : {dist B * C * D} := locked (makeDist f0 f1).
Lemma dE abc: d abc = \rsum_(x in A) P (x, abc.1.1, abc.1.2, abc.2).
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
End def.
End Proj234.

Module QuadA23.
Section def.
Variables (A B C D : finType) (P : {dist A * B * D * C}).
Let g (x : A * (B * D) * C) := let: (a, (b, d), c) := x in (a, b, d, c).
Definition f := [ffun x : A * (B * D) * C =>  P (g x)].
Lemma f0 x : 0 <= f x.
Proof. rewrite ffunE; move: x => -[[] ? [] ? ? ?]; exact/dist_ge0. Qed.
Lemma f1 : \rsum_(x in {: A * (B * D) * C}) f x = 1.
Proof.
rewrite /f -(epmf1 P) /= (reindex g) /=; last first.
  exists (fun x => let: (a, b, d, c) := x in (a, (b, d), c)).
  by move=> -[[] ? [] ? ? ?].
  by move=> -[[] [] ? ? ? ?].
evar (h : A * (B * D) * C -> R); rewrite (eq_bigr h); last first.
  move=> i _; rewrite ffunE /h; reflexivity.
rewrite {}/h.
by apply eq_bigr => -[[] ? [] ? ? ?].
Qed.
Definition d : {dist A * (B * D) * C} := locked (makeDist f0 f1).
Lemma dE x : d x = P (g x).
Proof. by rewrite /d /g; unlock; rewrite ffunE. Qed.
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
Definition f := [ffun x : A * B * (D * C) =>  P (g x)].
Lemma f0 x : 0 <= f x.
Proof. rewrite ffunE; move: x => -[[] ? ? [] ? ?]; exact/dist_ge0. Qed.
Lemma f1 : \rsum_(x in {: A * B * (D * C)}) f x = 1.
Proof.
rewrite /f -(epmf1 P) /= (reindex g) /=; last first.
  exists (fun x => let: (a, b, d, c) := x in (a, b, (d, c))).
  by move=> -[[] ? ? [] ? ?].
  by move=> -[[] [] ? ? ? ?].
evar (h : A * B * (D * C) -> R); rewrite (eq_bigr h); last first.
  move=> i _; rewrite ffunE /h; reflexivity.
rewrite {}/h.
by apply eq_bigr => -[[] ? ? [] ? ?].
Qed.
Definition d : {dist A * B * (D * C)} := locked (makeDist f0 f1).
Lemma dE x : d x = P (g x).
Proof. by rewrite /d /g; unlock; rewrite ffunE. Qed.
End def.
End QuadA34.

Module QuadA234.
Section def.
Variables (A B C D : finType) (P : {dist A * B * D * C}).
Let g (x : A * (B * D * C)) := let: (a, (b, d, c)) := x in (a, b, d, c).
Definition f := [ffun x : A * (B * D * C) =>  P (g x)].
Lemma f0 x : 0 <= f x.
Proof. rewrite ffunE; move: x => -[? [] [] ? ? ?]; exact/dist_ge0. Qed.
Lemma f1 : \rsum_(x in {: A * (B * D * C)}) f x = 1.
Proof.
rewrite /f -(epmf1 P) /= (reindex g) /=; last first.
  exists (fun x => let: (a, b, d, c) := x in (a, (b, d, c))).
  by move=> -[? [] [] ? ? ?].
  by move=> -[[] [] ? ? ? ?].
evar (h : A * (B * D * C) -> R); rewrite (eq_bigr h); last first.
  move=> i _; rewrite ffunE /h; reflexivity.
rewrite {}/h.
by apply eq_bigr => -[? [] [] ? ?].
Qed.
Definition d : {dist A * (B * D * C)} := locked (makeDist f0 f1).
Lemma dE x : d x = P (g x).
Proof. by rewrite /d /g; unlock; rewrite ffunE. Qed.
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
(* TODO: lemma *)
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
  rewrite !big_setX; apply eq_bigr => b bF; rewrite big_setX /=.
  apply eq_bigr => c cG; apply eq_bigr => d dH.
  by rewrite QuadA34.dE QuadA23.dE.
rewrite -TripA.Pr; congr Pr.
(* TODO: lemma *)
apply/dist_ext => -[b [c d]].
rewrite TripA.dE /= 2!Bivar.sndE; apply  eq_bigr => a _ /=.
by rewrite !TripA.dE /= QuadA23.dE QuadA34.dE.
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

Lemma marginal_RV2_1 a :
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
Qed.

Lemma marginal_RV2_2 b :
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
Qed.

Lemma marginal_RV3_1 b c :
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
Qed.

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
Proof.
apply/dist_ext => ?; by rewrite Bivar.fstE RVar.dE /Pr -marginal_RV2_1.
Qed.

Lemma snd_RV2 : Bivar.snd (RVar.d [% X, Y]) = RVar.d Y.
Proof.
apply/dist_ext => ?; rewrite Bivar.sndE RVar.dE.
by rewrite /pr_eq /Pr (marginal_RV2_2 X).
Qed.

Lemma Swap_RV2 : Swap.d (RVar.d [% X, Y]) = RVar.d [% Y, X].
Proof.
apply/dist_ext => -[b a]; rewrite Swap.dE 2!RVar.dE.
by rewrite /Pr; apply eq_bigl => u; rewrite !inE; apply/eqP/eqP => -[<- <-].
Qed.

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
Proof.
apply/dist_ext => -[b c].
rewrite Bivar.sndE RVar.dE /pr_eq /Pr (marginal_RV3_1 X).
by apply eq_bigr => a _; rewrite TripA.dE.
Qed.

Lemma snd_TripA_RV4 :
  Bivar.snd (TripA.d (RVar.d [% X, [% Y, W],  Z])) = RVar.d [% Y, W, Z].
Proof.
apply/dist_ext => -[[b d c]].
rewrite Bivar.sndE RVar.dE /pr_eq /Pr (marginal_RV4_1 X); apply/eq_bigr => a _.
rewrite TripA.dE /= !RVar.dE /Pr; apply eq_bigl => u.
by rewrite !inE; apply/eqP/eqP => -[<- <- <- <-].
Qed.

Lemma Proj13_RV3 : Proj13.d (RVar.d [% X, Y, Z]) = RVar.d [% X, Z].
Proof.
apply/dist_ext => -[a c].
by rewrite Proj13.dE RVar.dE /pr_eq /Pr /= (marginal_RV3_2 Y).
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
by apply eq_bigl => u; rewrite !inE; apply/eqP/eqP => -[<- <- <-].
Qed.

Lemma TripA_RV3 : TripA.d (RVar.d [% X, Y, Z]) = RVar.d [% X, [% Y, Z]].
Proof.
apply/dist_ext => -[a [b c]]; rewrite TripA.dE /= !RVar.dE.
by apply eq_bigl => u; rewrite !inE; apply/eqP/eqP => -[<- <- <-].
Qed.

Lemma TripC23_RV3 : TripC23.d (RVar.d [% X, Y, Z]) = RVar.d [% X, Z, Y].
Proof.
apply/dist_ext => -[[a c] b]; rewrite TripC23.dE /= !RVar.dE.
by apply eq_bigl => u; rewrite !inE; apply/eqP/eqP => -[<- <- <-].
Qed.
End trip_prop.

Section quad_prop.
Variables (U : finType) (P : dist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma QuadA23_RV4 : QuadA23.d (RVar.d [% X, Y, W, Z]) = RVar.d [% X, [% Y, W], Z].
Proof.
apply/dist_ext => -[] [] ? [] ? ? ?; rewrite QuadA23.dE /= !RVar.dE.
by apply eq_bigl => u; rewrite !inE; apply/eqP/eqP; move=> -[<- <- <- <-].
Qed.

Lemma QuadA34_RV4 : QuadA34.d (RVar.d [% X, Y, Z, W]) = RVar.d [% X, Y, [% Z, W]].
Proof.
apply/dist_ext => -[[a b] [c d]]; rewrite !(RVar.dE,QuadA34.dE).
by apply eq_bigl => u; rewrite !inE; apply/eqP/eqP => -[<- <- <- <-].
Qed.

Lemma QuadA234_RV4 : QuadA234.d (RVar.d [% X, Y, Z, W]) = RVar.d [% X, [% Y, Z, W]].
Proof.
apply/dist_ext => -[a [[b c] d]]; rewrite !(RVar.dE,QuadA234.dE).
by apply eq_bigl => u; rewrite !inE; apply/eqP/eqP => -[<- <- <- <-].
Qed.

Lemma Proj14_RV4 : Proj14d (RVar.d [% X, Y, W, Z]) = RVar.d [% X, Z].
Proof.
rewrite /Proj14d; apply/dist_ext => -[a c].
rewrite !Proj13.dE /= RVar.dE {1}/pr_eq {1}/Pr (marginal_RV3_2 Y); apply eq_bigr => b _.
by rewrite RVar.dE {1}/pr_eq {1}/Pr Proj124.dE (marginal_RV4_3 W); apply eq_bigr.
Qed.

Lemma Proj124_RV4 : Proj124.d (RVar.d [% X, Y, W, Z])= RVar.d [% X, Y, Z].
Proof.
apply/dist_ext => -[[a b] c].
by rewrite Proj124.dE /= RVar.dE /= {1}/pr_eq {1}/Pr -marginal_RV4_3.
Qed.

Lemma Proj234_RV4 :
  Proj234.d (RVar.d [% X, Y, W, Z]) = Proj23.d (RVar.d [% X, [% Y, W], Z]).
Proof.
rewrite -QuadA23_RV4; apply/dist_ext => -[[] b d c].
rewrite Proj23.dE Proj234.dE; apply eq_bigr => a _ /=.
by rewrite !(RVar.dE,QuadA23.dE).
Qed.

End quad_prop.

Reserved Notation "\Pr[ X = a | Y = b ]" (at level 6, X, Y, a, b at next level,
  format "\Pr[  X =  a  |  Y  =  b  ]").

Section conditionnally_independent_discrete_random_variables.

Variables (U : finType) (P : dist U) (A B C : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).
Let Q := RVar.d [% X, Y, Z].

Local Notation "\Pr[ X = a | Y = b ]" := (\Pr_(RVar.d [% X, Y])[ [set a] | [set b]]).

Definition cinde_drv := forall a b c,
  \Pr[ [% X, Y] = (a, b) | Z = c ] = \Pr[ X = a | Z = c ] * \Pr[ Y = b | Z = c].

End conditionnally_independent_discrete_random_variables.

Notation "\Pr[ X = a | Y = b ]" := (\Pr_(RVar.d [% X, Y])[ [set a] | [set b]]).

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
rewrite {}H (*2!Proj13_RV3 2!Proj23_RV3*); congr (_ * _).
rewrite /cPr !snd_RV2; congr (_ / _).
rewrite /Pr !big_setX /= !big_set1 !RVar.dE /Pr; apply eq_bigl => u.
by rewrite !inE; apply/eqP/eqP => -[<- <- <-].
Qed.

Lemma cinde_drv_3C : X _|_ Y | [% Z, W] -> X _|_ Y | [% W, Z].
Proof.
move=> H; move=> a b -[d c]; move: (H a b (c, d)) => {H}.
(*rewrite 2!Proj13_RV3 2!Proj23_RV3*)move => H.
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
rewrite /cinde_drv => H b a c.
rewrite -setX1 -cPr_TripC12 setX1 TripC12_RV3.
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
move=> H; rewrite /cinde_drv => a b c.
transitivity (\rsum_(d <- fin_img W) \Pr_(QuadA23.d Q)[[set (a, (b, d))] | [set c]]).
  rewrite (reasoning_by_cases_RV2 W); apply eq_bigr => /= d _.
  by rewrite -2![in RHS]setX1 cPr_QuadA23 -setX1.
transitivity (\rsum_(d <- fin_img W)
  \Pr_(Proj14d Q)[[set a] | [set c]] * \Pr_(Proj234.d Q)[[set (b, d)] | [set c]]).
  apply eq_bigr => d _.
  by rewrite QuadA23_RV4 H Proj14_RV4 Proj234_RV4 Proj23_RV3.
rewrite -big_distrr /=; congr (_ * _).
  by rewrite /Proj14d Proj124_RV4 Proj13_RV3.
rewrite (reasoning_by_cases_RV2 W); apply eq_bigr => d _.
by rewrite Proj234_RV4 Proj23_RV3 setX1.
Qed.

End decomposition.

Section weak_union.

Variables (U : finType) (P : dist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma weak_union : X _|_ [% Y, W] | Z -> X _|_ Y | [% Z, W].
Proof.
move=> H; move=> a b -[c d].
transitivity (\Pr_(RVar.d [% X, [% Y, Z, W]]) [[set a] | [set (b, c, d)]] *
  \Pr_(RVar.d [% Y, [% Z, W]]) [[set b] | [set (c, d)]]).
  rewrite -1!setX1 product_rule Proj23_RV3; congr (_ * _).
  by rewrite -QuadA34_RV4 -setX1 cPr_TripA_QuadA34 QuadA234_RV4 !setX1.
transitivity (\Pr_(RVar.d [% X, Z])[ [set a] | [set c] ] *
  \Pr_(RVar.d [% Y, [% Z,  W]]) [[set b] | [set (c, d)]]).
  move: {H}(H a (b, d) c).
  case/boolP : (\Pr_(RVar.d [% W, Z])[ [set d] | [set c] ] == 0) => [H0 _|H0].
    move: H0.
    rewrite {1}/cPr snd_RV2 => /eqP; rewrite mulR_eq0 => -[Htmp|/invR_eq0 H0].
    - by rewrite {2 4}/cPr -!setX1 Pr_RV2_domin_snd ?div0R ?mulR0 // Pr_RV2C.
    - by rewrite {2 4}/cPr -setX1 Pr_RV2_domin_snd ?div0R ?mulR0 // Pr_RV2_domin_fst.
  rewrite -setX1 product_rule Proj23_RV3.
  rewrite -setX1 product_rule Proj23_RV3.
  rewrite [in X in X = _ -> _]mulRA.
  rewrite [in X in _ = X -> _]mulRA.
  rewrite eqR_mul2r; last exact/eqP.
  rewrite 3![in X in X -> _]setX1 => {H0}H.
  transitivity (\Pr_(TripA.d (RVar.d [% X, [% Y, W], Z]))[[set a] | [set (b, d, c)]] *
                \Pr_(TripA.d (RVar.d [% Y, W, Z]))[[set b] | [set (d, c)]]).
    congr (_ * _).
      rewrite -QuadA234_RV4 -2!setX1 cPr_TripA_QuadA23_TripC23 TripC23_RV3.
      by rewrite -QuadA23_RV4 2!setX1.
    by rewrite -TripC23_RV3 -!setX1 cPr_TripA_TripC23 TripA_RV3.
  rewrite {}H; congr (_ * _).
  by rewrite -TripC23_RV3 -!setX1 cPr_TripA_TripC23 TripA_RV3.
have {H}H : X _|_ W | Z by move/cinde_drv_2C : H; apply decomposition.
case/boolP : (\Pr_(RVar.d [% W, Z])[ [set d] | [set c] ] == 0) => [|H0].
  rewrite {1}/cPr snd_RV2 => /eqP; rewrite mulR_eq0 => -[H0|/invR_eq0 H0].
    suff : Pr (RVar.d [% Y, [% Z, W] ]) [set (b, (c, d))] = 0.
      by rewrite {2 4}/cPr !snd_RV2 setX1 => ->; rewrite !div0R !mulR0.
    by rewrite -setX1; apply Pr_RV2_domin_snd; rewrite -setX1 Pr_RV2C.
  suff : Pr (RVar.d [% Y, [% Z, W]]) [set (b, (c, d))] = 0.
    by rewrite {2 4}/cPr !snd_RV2 !setX1 => ->; rewrite !div0R !mulR0.
  rewrite -setX1; apply Pr_RV2_domin_snd; rewrite -setX1; exact: Pr_RV2_domin_fst.
congr (_ * _).
move: (H a d c).
rewrite -setX1 product_rule Proj23_RV3.
rewrite eqR_mul2r; last exact/eqP.
move=> <-.
by rewrite -TripC23_RV3 cPr_TripA_TripC23 TripA_RV3 setX1.
Qed.

End weak_union.

Section contraction.

Variables (U : finType) (P : dist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma contraction : X _|_ W | [% Z, Y] -> X _|_ Y | Z -> X _|_ [% Y, W] | Z.
Proof.
move=> H1 H2; move=> a -[b d] c.
rewrite -setX1 product_rule Proj23_RV3.
transitivity (
  \Pr_(TripA.d (RVar.d [%X, Y, Z]))[ [set a] | (setX [set b] [set c]) ] *
  \Pr_(RVar.d [%Y, W, Z])[ [set (b, d)] | [set c] ]).
  move: {H1}(H1 a d (c, b)).
  rewrite -!setX1 product_rule Proj23_RV3 => H1.
  rewrite product_ruleC Proj13_RV3.
  rewrite mulRA.
  transitivity (
    \Pr_(TripA.d (RVar.d [%X, W, [%Z, Y]]))[[set a] | [set (d, (c, b))]] *
    \Pr_(RVar.d [%W, [%Z, Y]])[[set d] | [set (c, b)]] *
    \Pr_(RVar.d [%Y, Z])[[set b] | [set c]]).
    congr (_ * _ * _).
      rewrite TripA_RV3 -QuadA234_RV4 -cPr_TripA_QuadA34.
      rewrite QuadA34_RV4 -TripC23_RV3 cPr_TripA_TripC23.
      rewrite TripA_RV3 -QuadA234_RV4 -cPr_TripA_QuadA34.
      by rewrite !setX1 QuadA34_RV4.
    rewrite cPr_TripA_TripC12 setX1; congr (cPr _ _).
    by rewrite TripA_RV3 Swap_RV2 TripA_RV3.
  rewrite -3!setX1 {}H1 mulRA.
  congr (_ * _ * _).
    by rewrite -TripA_RV3 -TripC23_RV3 cPr_TripA_TripC23.
  by rewrite cPr_TripA_TripC12 TripA_RV3 Swap_RV2 TripA_RV3.
move: {H2}(H2 a b c).
rewrite -setX1 product_rule Proj23_RV3 => H2.
rewrite -setX1 product_ruleC Proj13_RV3.
by rewrite mulRCA H2 mulRCA.
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
(* NB(rei): tentative *)

Variables (U : finType) (P : dist U) (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Hypothesis Hpos : forall b c d, Pr (RVar.d [% Y, Z, W]) [set (b, c, d)] != 0.
Hypothesis D_not_empty : D.

Lemma intersection : X _|_ Y | [% Z, W] -> X _|_ W | [% Z, Y] -> X _|_ [% Y, W] | Z.
Proof.
move=> H1 H2; apply contraction => //; move=> a b c.
rewrite [in X in _ = X * _](reasoning_by_cases_RV2 W).
have {H2}K1 : forall d, \Pr_(RVar.d [% X, [% Y, Z]])[[set a]|[set (b, c)]] =
       \Pr_(RVar.d [% X, [% W, Z, Y]])[[set a]|[set (d, c, b)]].
  move=> d; move: {H2}(H2 a d (c, b))(*; rewrite Proj13_RV3 Proj23_RV3*).
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
  move=> d; move: {H1}(H1 a b (c, d))(*; rewrite Proj13_RV3 Proj23_RV3*).
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
