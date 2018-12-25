From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.
Require Import proba divergence entropy cproba.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "X @= x" (at level 10).
Reserved Notation "P |= X _|_  Y | Z" (at level 10, X, Y, Z at next level).

Notation "X @= x" := ([set h | X h == x]) : proba_scope.

Local Open Scope proba_scope.

Definition Rvar {A} (d : dist A) (TA : finType) := A -> TA.

Module RvarDist.
Section rvardist.
Variables (A TA : finType) (P : dist A) (X : Rvar P TA).
Definition f a := Pr P (X @= a).
Lemma f0 a : 0 <= f a. Proof. exact/Pr_ge0. Qed.
Lemma f1 : \rsum_(a in TA) (f a) = 1.
Proof.
rewrite /f /Pr -(pmf1 P) (sum_parti_finType _ X) /=.
rewrite (bigID (fun x => x \in fin_img X)) /=.
rewrite [X in _ + X = _](eq_bigr (fun=> 0)); last first.
  move=> ta taX; rewrite big1 // => a; rewrite inE => /eqP Xata.
  move: taX; rewrite /fin_img mem_undup.
  case/mapP; exists a => //; by rewrite mem_enum.
rewrite big_const iter_addR mulR0 addR0 big_uniq /=; last exact: undup_uniq.
apply eq_bigr => ta Hta; by apply eq_bigl => a; rewrite inE.
Qed.
Definition d : {dist TA} := locked (makeDist f0 f1).
Lemma dE a : d a = Pr P (X @= a). Proof. by rewrite /d; unlock. Qed.
End rvardist.
End RvarDist.

Reserved Notation "<{ X , Y }>" (at level 5, X, Y at next level).

Section pair_of_rvars.
Variables (Omega : finType) (P : dist Omega).
Variables (TA : finType) (X : Rvar P TA) (TB : finType) (Y : Rvar P TB).
Definition Rvar2 : Rvar P [finType of TA * TB] := fun x => (X x, Y x).
End pair_of_rvars.

Notation "<{ X , Y }>" := (Rvar2 X Y).

Section triple_of_rvars.
Variables (Omega : finType) (P : dist Omega).
Variables (TA TB TC TD : finType) (X : Rvar P TA) (Y : Rvar P TB) (Z : Rvar P TC).
Definition Rvar3 : Rvar P [finType of TA * TB * TC] := fun x => (<{X, Y}> x, Z x).
End triple_of_rvars.

Section tuples_of_rvars.
Variables (Omega : finType) (P : dist Omega).
Variables (TA : finType) (X : Rvar P TA) (TB : finType) (Y : Rvar P TB).

Variables (TC : finType) (Z : Rvar P TC).

Variables (TD : finType) (W : Rvar P TD).
Definition Rvar4 : Rvar P [finType of TA * TB * TC * TD] := fun x => (Rvar3 X Y Z x, W x).
End tuples_of_rvars.

Section marginals.
Variables (A : finType) (P : dist A).
Variables (TA TB TC TD : finType).
Variables (W : Rvar P TD) (X : Rvar P TA) (Y : Rvar P TB) (Z : Rvar P TC).

Lemma marginal_Rvar2_1 a :
  \rsum_(a0 in X @= a) P a0 = \rsum_(i in TB) (RvarDist.d <{ X, Y }>) (a, i).
Proof.
have -> : (X @= a) = \bigcup_x0 (Rvar2 X Y) @= (a, x0).
  apply/setP => b0; rewrite !inE; apply/eqP/bigcupP.
  by case=> <- /=; exists (Y b0) => //; rewrite inE.
  by case=> d _; rewrite inE => /eqP[] <- ?.
rewrite partition_disjoint_bigcup /=; last first.
  move=> d0 d1 d01; rewrite -setI_eq0; apply/eqP/setP => a0; rewrite !inE.
  apply/negbTE/negP => /andP[] /eqP[<- Hd0] /eqP -[].
  rewrite Hd0; exact/eqP.
apply eq_bigr => d _; by rewrite RvarDist.dE.
Qed.

Lemma marginal_Rvar2_2 b :
  \rsum_(a in Y @= b) P a = \rsum_(i in TA) (RvarDist.d <{ X, Y }>) (i, b).
Proof.
have -> : (Y @= b) = \bigcup_x0 (Rvar2 X Y) @= (x0, b).
  apply/setP => a0; rewrite !inE; apply/eqP/bigcupP.
  by case=> <- /=; exists (X a0) => //; rewrite inE.
  by case=> d _; rewrite inE => /eqP[] ? <-.
rewrite partition_disjoint_bigcup /=; last first.
  move=> d0 d1 d01; rewrite -setI_eq0; apply/eqP/setP => a0; rewrite !inE.
  apply/negbTE/negP => /andP[] /eqP[Hd0 <-] /eqP -[].
  rewrite Hd0; exact/eqP.
apply eq_bigr => d _; by rewrite RvarDist.dE.
Qed.

Lemma marginal_Rvar3_1 b c :
  \rsum_(a0 in <{Y, Z}> @= (b, c)) P a0 =
  \rsum_(x in TD) (RvarDist.d (Rvar3 W Y Z) (x, b, c)).
Proof.
have -> : ((Rvar2 Y Z) @= (b, c)) = \bigcup_x0 (Rvar3 W Y Z) @= (x0, b, c).
  apply/setP => a0; rewrite !inE; apply/eqP/bigcupP.
  by case=> <- <- /=; exists (W a0) => //; rewrite inE.
  by case=> d _; rewrite inE => /eqP[] ? <- <-.
rewrite partition_disjoint_bigcup /=; last first.
  move=> d0 d1 d01; rewrite -setI_eq0; apply/eqP/setP => a0; rewrite !inE.
  apply/negbTE/negP => /andP[] /eqP[Hd0 <- <-] /eqP -[].
  rewrite Hd0; exact/eqP.
apply eq_bigr => d _; by rewrite RvarDist.dE.
Qed.

Lemma marginal_Rvar3_2 b c :
  \rsum_(a0 in (Rvar2 Y Z) @= (b, c)) P a0 =
  \rsum_(x in TD) (RvarDist.d (Rvar3 Y W Z)) (b, x, c).
Proof.
have -> : ((Rvar2 Y Z) @= (b, c)) = \bigcup_x0 (Rvar3 Y W Z) @= (b, x0, c).
  apply/setP => a0; rewrite !inE; apply/eqP/bigcupP.
  by case=> <- <- /=; exists (W a0) => //; rewrite inE.
  by case=> d _; rewrite inE => /eqP[] <- ? <-.
rewrite partition_disjoint_bigcup /=; last first.
  move=> d0 d1 d01.
  rewrite -setI_eq0; apply/eqP/setP => a0; rewrite !inE.
  apply/negbTE/negP => /andP[] /eqP[<- Hd0 <-] /eqP -[].
  rewrite Hd0; exact/eqP.
apply eq_bigr => d _; by rewrite RvarDist.dE.
Qed.

Lemma marginal_Rvar3_3 b c :
  \rsum_(a0 in (Rvar2 Y Z) @= (b, c)) P a0 =
  \rsum_(x in TD) (RvarDist.d (Rvar3 Y Z W)) (b, c, x).
Proof.
have -> : ((Rvar2 Y Z) @= (b, c)) = \bigcup_x0 (Rvar3 Y Z W) @= (b, c, x0).
  apply/setP => a0; rewrite !inE; apply/eqP/bigcupP.
  by case=> <- <- /=; exists (W a0) => //; rewrite inE.
  by case=> d _; rewrite inE => /eqP[] <- <-.
rewrite partition_disjoint_bigcup /=; last first.
  move=> d0 d1 d01.
  rewrite -setI_eq0; apply/eqP/setP => a0; rewrite !inE.
  apply/negbTE/negP => /andP[] /eqP[<- <- Hd0] /eqP -[].
  rewrite Hd0; exact/eqP.
apply eq_bigr => d _; by rewrite RvarDist.dE.
Qed.

Lemma marginal_Rvar4_1 a b c :
  \rsum_(a0 in (Rvar3 X Y Z) @= (a, b, c)) P a0 =
  \rsum_(x in TD) (RvarDist.d (Rvar4 W X Y Z)) (x, a, b, c).
Proof.
have -> : ((Rvar3 X Y Z) @= (a, b, c)) = \bigcup_d (Rvar4 W X Y Z) @= (d, a, b, c).
  apply/setP => a0; rewrite !inE; apply/eqP/bigcupP.
  by case=> <- <- <- /=; exists (W a0) => //; rewrite inE.
   by case=> d _; rewrite inE => /eqP[] ? <- <- <-.
rewrite partition_disjoint_bigcup /=; last first.
  move=> d0 d1 d01.
  rewrite -setI_eq0; apply/eqP/setP => a0; rewrite !inE.
  apply/negbTE/negP => /andP[] /eqP[Hd0 <- <- <-] /eqP -[].
  rewrite Hd0; exact/eqP.
apply eq_bigr => d _; by rewrite RvarDist.dE.
Qed.

Lemma marginal_Rvar4_3 a b c :
  \rsum_(a0 in (Rvar3 X Y Z) @= (a, b, c)) P a0 =
  \rsum_(x in TD) (RvarDist.d (Rvar4 X Y W Z)) (a, b, x, c).
Proof.
have -> : ((Rvar3 X Y Z) @= (a, b, c)) = \bigcup_x0 (Rvar4 X Y W Z) @= (a, b, x0, c).
  apply/setP => a0; rewrite !inE; apply/eqP/bigcupP.
  by case=> <- <- <- /=; exists (W a0) => //; rewrite inE.
  by case=> d _; rewrite inE => /eqP[] <- <- ? <-.
rewrite partition_disjoint_bigcup /=; last first.
  move=> d0 d1 d01.
  rewrite -setI_eq0; apply/eqP/setP => a0; rewrite !inE.
  apply/negbTE/negP => /andP[] /eqP[<- <- Hd0 <-] /eqP -[].
  rewrite Hd0; exact/eqP.
apply eq_bigr => d _; by rewrite RvarDist.dE.
Qed.

Lemma marginal_Rvar4_4 a b d :
  \rsum_(a0 in (Rvar3 X Y Z) @= (a, b, d)) P a0 =
  \rsum_(x in TD) (RvarDist.d (Rvar4 X Y Z W)) (a, b, d, x).
Proof.
have -> : ((Rvar3 X Y Z) @= (a, b, d)) = \bigcup_x0 (Rvar4 X Y Z W) @= (a, b, d, x0).
  apply/setP => a0; rewrite !inE; apply/eqP/bigcupP.
  by case=> <- <- <- /=; exists (W a0) => //; rewrite inE.
  by case=> c _; rewrite inE => /eqP[] <- <- <- ?.
rewrite partition_disjoint_bigcup /=; last first.
  move=> d0 d1 d01.
  rewrite -setI_eq0; apply/eqP/setP => a0; rewrite !inE.
  apply/negbTE/negP => /andP[] /eqP[<- <- <- Hd0] /eqP -[].
  rewrite Hd0; exact/eqP.
by apply eq_bigr => c _; rewrite RvarDist.dE.
Qed.

End marginals.

Section rvar2_prop.
Variables (A : finType) (P : dist A).
Variables (TA TB : finType).
Variables (X : Rvar P TA) (Y : Rvar P TB).

Lemma Pr_Rvar2C a b :
  Pr (RvarDist.d <{ X, Y }>) (setX a b) = Pr (RvarDist.d <{ Y, X }>) (setX b a).
Proof.
rewrite /Pr !big_setX /= exchange_big /=; apply eq_bigr => b0 _.
apply/eq_bigr => a0 _; rewrite !RvarDist.dE /Pr; apply eq_bigl => w0.
by rewrite !inE; apply/eqP/eqP => -[<- <-].
Qed.

Lemma fst_Rvar2 : Bivar.fst (RvarDist.d (Rvar2 X Y)) = RvarDist.d X.
Proof.
apply/dist_ext => b.
by rewrite Bivar.fstE RvarDist.dE /Pr -marginal_Rvar2_1.
Qed.

Lemma snd_Rvar2 : Bivar.snd (RvarDist.d (Rvar2 X Y)) = RvarDist.d Y.
Proof.
apply/dist_ext => b.
by rewrite Bivar.sndE RvarDist.dE /Pr (marginal_Rvar2_2 X).
Qed.

Lemma Pr_Rvar2_domin_fst a b : Pr (RvarDist.d X) a = 0 ->
  Pr (RvarDist.d <{ X, Y }>) (setX a b) = 0.
Proof. move=> H; apply Pr_fst_eq0; by rewrite fst_Rvar2. Qed.

Lemma Pr_Rvar2_domin_snd a b : Pr (RvarDist.d Y) b = 0 ->
  Pr (RvarDist.d <{ X, Y }>) (setX a b) = 0.
Proof. move=> H; apply Pr_snd_eq0; by rewrite snd_Rvar2. Qed.

End rvar2_prop.

Section rvar3_prop.
Variables (A : finType) (P : dist A).
Variables (TA TB TC TD : finType).
Variables (X : Rvar P TA) (Y : Rvar P TB) (Z : Rvar P TC) (W : Rvar P TD).

Lemma snd_TripA_Rvar3 :
  Bivar.snd (TripA.d (RvarDist.d (Rvar3 X Y Z))) = RvarDist.d (Rvar2 Y Z).
Proof.
apply/dist_ext => -[b c].
rewrite Bivar.sndE RvarDist.dE /Pr (marginal_Rvar3_1 X).
by apply eq_bigr => a _; rewrite TripA.dE.
Qed.

Lemma snd_TripA_Rvar3A :
  Bivar.snd (TripA.d (RvarDist.d (Rvar3 X (Rvar2 Y W) Z))) = RvarDist.d (Rvar3 Y W Z).
Proof.
apply/dist_ext => -[[b d c]].
rewrite Bivar.sndE RvarDist.dE /Pr (marginal_Rvar4_1 X); apply/eq_bigr => a _.
rewrite TripA.dE /= !RvarDist.dE /Pr; apply eq_bigl => a0.
by rewrite !inE; apply/eqP/eqP => -[<- <- <- <-].
Qed.

Lemma snd_Rvar3 : Bivar.snd (RvarDist.d (Rvar3 Y W Z)) = Bivar.snd (RvarDist.d (Rvar2 Y Z)).
Proof.
apply/dist_ext => c.
rewrite !Bivar.sndE /=.
rewrite (eq_bigr (fun i => (RvarDist.d (Rvar3 Y W Z)) (i.1, i.2, c))); last by case.
rewrite -(pair_bigA _ (fun i1 i2 => (RvarDist.d (Rvar3 Y W Z)) (i1, i2, c))).
apply eq_bigr => b _ /=.
rewrite RvarDist.dE /Pr (marginal_Rvar3_2 W); exact/eq_bigr.
Qed.

Lemma Proj13_Rvar3 : Proj13.d (RvarDist.d (Rvar3 X Y Z)) = RvarDist.d (Rvar2 X Z).
Proof.
apply/dist_ext => -[a c].
by rewrite Proj13.dE RvarDist.dE /Pr /= (marginal_Rvar3_2 Y).
Qed.

Lemma Proj23_Rvar3 : Proj23.d (RvarDist.d (Rvar3 X Y Z)) = RvarDist.d (Rvar2 Y Z).
Proof.
apply/dist_ext => -[a c].
by rewrite Proj23.dE RvarDist.dE /Pr /= (marginal_Rvar3_1 X).
Qed.

End rvar3_prop.

Section conditionnally_independent_discrete_random_variables.

Variable (Omega : finType) (P : dist Omega).
Variables (TA TB TC : finType).
Variables (X : Rvar P TA) (Y : Rvar P TB) (Z : Rvar P TC).
Let Q : {dist TA * TB * TC} := RvarDist.d (Rvar3 X Y Z).

Definition cinde_drv := forall (a : TA) (b : TB) (c : TC),
  \Pr_Q[ [set (a, b)] | [set c] ] =
  \Pr_(Proj13.d Q) [ [set a] | [set c] ] * \Pr_(Proj23.d Q) [ [set b] | [set c] ].

End conditionnally_independent_discrete_random_variables.

Arguments cinde_drv {Omega} _ {TA} {TB} {TC}.

Notation "P |= X _|_  Y | Z" := (cinde_drv P X Y Z) : proba_scope.

Definition swap {A B : finType} (ab : A * B) := (ab.2, ab.1).

Lemma injective_swap (A B : finType) (E : {set A * B}) : {in E &, injective swap}.
Proof. by case=> a b [a0 b0] /= _ _ [-> ->]. Qed.

Lemma set_swap (A B : finType) (P : B -> A -> bool) :
  [set h : {: B * A} | P h.1 h.2 ] = swap @: [set h | P h.2 h.1].
Proof.
apply/setP => /= -[b a]; rewrite !inE /=; apply/idP/imsetP => [H|].
- by exists (a, b) => //=; rewrite inE.
- by case => -[a0 b0]; rewrite inE /= => ? [-> ->].
Qed.

Section tripc12_prop.
Variable (Omega : finType) (Q : dist Omega).
Variables (TA TB TC : finType) (X : Rvar Q TA) (Y : Rvar Q TB) (Z : Rvar Q TC).
Let P : {dist TA * TB * TC} := RvarDist.d (Rvar3 X Y Z).
Lemma TripC12_Rvar3 : TripC12.d P = RvarDist.d (Rvar3 Y X Z).
Proof.
apply/dist_ext => -[[a b] c]; rewrite TripC12.dE /= !RvarDist.dE.
congr (Pr _ _).
apply/setP => a0; rewrite !inE; rewrite /Rvar3 /Rvar2.
by apply/idP/idP => /eqP -[-> -> ->].
Qed.
Lemma Pr_TripC12 (c : TC) (E : {set TA * TB}) :
  \Pr_P[E | [set c]] = \Pr_(TripC12.d P)[swap @: E | [set c]].
Proof.
rewrite /cPr TripC12.snd; congr (_ / _).
rewrite /Pr 2!big_setX /= [in LHS]exchange_big /= [in RHS]exchange_big /=.
apply eq_bigr => c' Zc'c; rewrite (big_imset _ (@injective_swap _ _ E)) /=.
apply eq_bigr => -[? ?] _; by rewrite TripC12.dE.
Qed.
End tripc12_prop.

Section symmetry.

Variable (Omega : finType) (P : dist Omega).
Variables (TA TB TC : finType) (X : Rvar P TA) (Y : Rvar P TB) (Z : Rvar P TC).
Let Q : {dist TA * TB * TC} := RvarDist.d (Rvar3 X Y Z).

Lemma symmetry : P |= X _|_ Y | Z -> P |= Y _|_ X | Z.
Proof.
rewrite /cinde_drv -/Q => /= H y x z.
rewrite [in RHS]mulRC.
have -> : Proj23.d (RvarDist.d (Rvar2 (Rvar2 Y X) Z)) = Proj13.d Q.
  by rewrite Proj23.def Proj13.def /Q TripC12_Rvar3.
have -> : Proj13.d (RvarDist.d (Rvar2 (Rvar2 Y X) Z)) = Proj23.d Q.
  by rewrite Proj23.def Proj13.def /Q TripC12_Rvar3.
rewrite Pr_TripC12 TripC12_Rvar3 -/Q.
rewrite -H.
congr cPr.
apply/setP => -[a0 b0]; rewrite !inE.
apply/imsetP/idP.
- by case => -[tb ta]; rewrite inE => /eqP -[-> ->] ->.
- by case/eqP => -> ->; exists (y, x) => //; rewrite inE.
Qed.

End symmetry.

Module Proj124.
Section proj124.
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
End proj124.
End Proj124.

Lemma snd_Proj124 (A B C D : finType) (P : {dist A * B * C * D}) :
  Bivar.snd (Proj124.d P) = Bivar.snd P.
Proof.
apply/dist_ext => d.
rewrite 2!Bivar.sndE /=.
rewrite (eq_bigr (fun i => P (i.1, i.2, d))); last by case.
rewrite -(pair_bigA _ (fun i1 i2 => P (i1, i2, d))) /=.
apply eq_bigr => -[a b] _.
by rewrite Proj124.dE; apply eq_bigr => c _.
Qed.

Definition Proj14d (A B C D : finType) (d : {dist A * B * D * C}) : {dist A * C} :=
  Proj13.d (Proj124.d d).

Section proj124_rvar4.
Variables (A : finType) (P : dist A).
Variables (TA TB TC TD : finType).
Variables (X : Rvar P TA) (Y : Rvar P TB) (Z : Rvar P TC) (W : Rvar P TD).

Lemma Proj124_Rvar4 : Proj124.d (RvarDist.d (Rvar4 X Y W Z))= RvarDist.d (Rvar3 X Y Z).
Proof.
apply/dist_ext => -[[a b] c].
by rewrite Proj124.dE /= RvarDist.dE /= {1}/Pr -marginal_Rvar4_3.
Qed.
End proj124_rvar4.

Section Proj14.
Variables (A : finType) (P : dist A).
Variables (TA TB TC TD : finType).
Variables (X : Rvar P TA) (Y : Rvar P TB) (Z : Rvar P TC) (W : Rvar P TD).
Let YW := Rvar2 Y W.

Lemma Proj14_Rvar4 : Proj13.d (RvarDist.d (Rvar3 X YW Z)) = Proj14d (RvarDist.d (Rvar4 X Y W Z)).
Proof.
rewrite /Proj14d; apply/dist_ext => -[a c].
rewrite !Proj13.dE /=.
rewrite (eq_bigr (fun b => (RvarDist.d (Rvar3 X YW Z)) (a, (b.1, b.2), c))); last by case.
rewrite -(pair_bigA _ (fun b1 b2 => (RvarDist.d (Rvar3 X YW Z)) (a, (b1, b2), c))) /=.
apply eq_bigr => b _.
rewrite Proj124.dE /=; apply eq_bigr => d _.
rewrite !RvarDist.dE /Pr.
apply eq_bigl => a0; rewrite !inE /Rvar4 /Rvar3 /Rvar2 /YW.
by apply/eqP/eqP => -[<- <- <- <-].
Qed.

End Proj14.

Module Proj234.
Section proj234.
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
End proj234.
End Proj234.

Section proj234_rvar4.
Variables (A : finType) (P : dist A).
Variables (TA TB TC TD : finType).
Variables (X : Rvar P TA) (Y : Rvar P TB) (Z : Rvar P TC) (W : Rvar P TD).
Let YW := Rvar2 Y W.
Lemma Proj234_Rvar4 :
  Proj234.d (RvarDist.d (Rvar4 X Y W Z)) = Proj23.d (RvarDist.d (Rvar3 X YW Z)).
Proof.
apply/dist_ext => -[[] b d c].
rewrite Proj23.dE Proj234.dE; apply eq_bigr => a _ /=.
rewrite !RvarDist.dE; congr Pr.
apply/setP => a0; by rewrite !inE !xpair_eqE !andbA.
Qed.
End proj234_rvar4.

Module QuadA12.
Section quada12.
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
End quada12.
End QuadA12.

Lemma snd_QuadA12 (A B D C : finType) (P : {dist A * B * D * C}) :
  Bivar.snd P = Bivar.snd (QuadA12.d P).
Proof.
apply/dist_ext => c; rewrite 2!Bivar.sndE /=.
rewrite (reindex (fun x => let: (a, b, d) := x in (a, (b, d)))) /=; last first.
  exists (fun x => let: (a, (b, d)) := x in (a, b, d)).
  by move=> -[] [].
  by move=> -[] ? [].
apply eq_bigr => -[[]] a b d _; by rewrite QuadA12.dE.
Qed.

Section quada12_prop.
Variables (A : finType) (P : dist A).
Variables (TA TB TC TD : finType).
Variables (X : Rvar P TA) (Y : Rvar P TB) (Z : Rvar P TC) (W : Rvar P TD).
Let YW := Rvar2 Y W.

Lemma QuadA12d_Rvar4 : QuadA12.d (RvarDist.d (Rvar4 X Y W Z)) = RvarDist.d (Rvar3 X YW Z).
Proof.
apply/dist_ext => -[] [] ? [] ? ? ?.
rewrite QuadA12.dE /= !RvarDist.dE; congr Pr.
apply/setP => a0.
rewrite !inE /Rvar4 /Rvar3 /Rvar2 /= /YW /Rvar2.
apply/eqP/eqP; by move=> -[] <- <- <- <-.
Qed.
End quada12_prop.

Section reasoning_by_cases_Rvar2.

Variables (A : finType) (P : dist A).
Variables (TA TB TC : finType).
Variables (Z : Rvar P TC) (X : Rvar P TA) (Y : Rvar P TB) .

Lemma total_Rvar2 E F :
  Pr (RvarDist.d (Rvar2 X Y)) (setX E F) =
  \rsum_(z <- fin_img Z) Pr (RvarDist.d (Rvar3 X Z Y)) (setX (setX E [set z]) F).
Proof.
apply/esym.
evar (e : TC -> R); rewrite (eq_bigr e); last first.
  move=> r _; rewrite /Pr big_setX /=.
  rewrite (eq_bigl (fun x => x \in setX E [set r])); last first.
    move=> -[? ?]; by rewrite !inE.
  rewrite big_setX /= /e; reflexivity.
rewrite {}/e exchange_big /=.
rewrite [in RHS]/Pr [in RHS]big_setX /=; apply eq_bigr => a aE.
evar (e : TC -> R); rewrite (eq_bigr e); last first.
  move=> r _; rewrite exchange_big /= /e; reflexivity.
rewrite {}/e exchange_big /=; apply eq_bigr => b _.
rewrite RvarDist.dE /Pr (marginal_Rvar3_2 Z).
rewrite [in RHS](bigID (fun x => x \in fin_img Z)) /=.
rewrite [X in _ = _ + X ](eq_bigr (fun=> 0)); last first.
  move=> d dZ.
  rewrite RvarDist.dE /= /Pr (eq_bigl (fun=> false)) ?big_pred0 // => a0.
  rewrite !inE; apply/negbTE.
  apply: contra dZ => /eqP -[? <- ?].
  rewrite mem_undup; apply/mapP; exists a0 => //; by rewrite mem_enum.
rewrite big_const iter_addR mulR0 addR0 big_uniq /=; last exact: undup_uniq.
apply eq_bigr => c cZ; by rewrite big_set1 !RvarDist.dE.
Qed.

Lemma reasoning_by_cases_Rvar2 E F :
  \Pr_(RvarDist.d (Rvar2 X Y))[E | F] =
  \rsum_(z <- fin_img Z) \Pr_(RvarDist.d (Rvar3 X Z Y))[setX E [set z] | F].
Proof.
by rewrite {1}/cPr total_Rvar2 -[in RHS]big_distrl /= (snd_Rvar3 _ _ Z).
Qed.

End reasoning_by_cases_Rvar2.

Section reasoning_by_cases_Rvar3.

Variables (A : finType) (P : dist A).
Variables (TA TB TC TD : finType).
Variables (Z : Rvar P TC) (X : Rvar P TA) (Y : Rvar P TB) (W : Rvar P TD).
Let Q := RvarDist.d (Rvar4 X Y Z W).

Lemma total_Rvar3 E F :
  Pr (RvarDist.d (Rvar3 X Y W)) (setX E F) =
  \rsum_(z <- fin_img Z) Pr Q (setX (setX E [set z]) F).
Proof.
apply/esym.
evar (e : TC -> R); rewrite (eq_bigr e); last first.
  move=> r _; rewrite /Pr big_setX /=.
  rewrite (eq_bigl (fun x => x \in setX E [set r])); last first.
    move=> -[[a0 b0] c0]; by rewrite !inE.
  rewrite big_setX /= /e; reflexivity.
rewrite {}/e exchange_big /=.
rewrite [in RHS]/Pr [in RHS]big_setX /=.
apply eq_bigr => -[a b] _.
evar (e : TC -> R); rewrite (eq_bigr e); last first.
  move=> r _; rewrite exchange_big /= /e; reflexivity.
rewrite {}/e exchange_big /=; apply eq_bigr => d _.
rewrite RvarDist.dE /Pr (marginal_Rvar4_4 Z).
rewrite [in RHS](bigID (fun x => x \in fin_img Z)) /=.
rewrite [X in _ = _ + X ](eq_bigr (fun=> 0)); last first.
  move=> c cZ.
  rewrite /Q RvarDist.dE /= /Pr (eq_bigl (fun=> false)) ?big_pred0 // => a0.
  rewrite !inE; apply/negbTE.
  apply: contra cZ => /eqP -[? ? ? <-].
  rewrite mem_undup; apply/mapP; exists a0 => //; by rewrite mem_enum.
rewrite big_const iter_addR mulR0 addR0 big_uniq /=; last exact: undup_uniq.
apply eq_bigr => c cZ.
rewrite big_set1 !RvarDist.dE; congr Pr.
apply/setP => a0.
rewrite !inE /= /Rvar4 /Rvar3 /Rvar2; by apply/idP/idP => /eqP -[-> -> -> ->].
Qed.

Lemma reasoning_by_cases_Rvar3 E F :
  \Pr_(RvarDist.d (Rvar3 X Y W))[E | F] =
  \rsum_(z <- fin_img Z) \Pr_Q[setX E [set z] | F].
Proof.
rewrite /Q {1}/cPr total_Rvar3 -[in RHS]big_distrl /= -(Proj124_Rvar4 _ _ _ Z).
by rewrite snd_Proj124.
Qed.

End reasoning_by_cases_Rvar3.

Section decomposition.

Variables (Omega : finType) (P : dist Omega) (TA TB TC TD : finType).
Variables (X : Rvar P TA) (Y : Rvar P TB) (Z : Rvar P TC) (W : Rvar P TD).
Let YW := Rvar2 Y W.
Let Q := RvarDist.d (Rvar4 X Y W Z).

Lemma decomposition : P |= X _|_ YW | Z -> P |= X _|_ Y | Z.
Proof.
move=> Hinde; rewrite /cinde_drv => x y z /=.
transitivity (\rsum_(w <- fin_img W)
    \Pr_(QuadA12.d Q) [ (setX [set x] (setX [set y] [set w])) | [set z] ]).
  rewrite (reasoning_by_cases_Rvar3 W); apply eq_bigr => /= r _.
  rewrite /cPr; congr (_ / _).
  - by rewrite /Pr !(big_setX,big_set1) /= !(RvarDist.dE,QuadA12.dE).
  - by rewrite snd_QuadA12.
transitivity (\rsum_(w <- fin_img W) \Pr_(Proj14d Q)[ [set x] | [set z] ] *
  \Pr_(Proj234.d Q)[ (setX [set y] [set w]) | [set z] ]).
  apply eq_bigr => w _.
  move: Hinde; rewrite /cinde_drv /= => /(_ x (y, w) z) => Hinde.
  rewrite QuadA12d_Rvar4.
  transitivity (\Pr_(RvarDist.d (Rvar3 X YW Z))[ [set (x, (y, w))] | [set z] ]).
    rewrite /cPr; congr (Pr _ _ / _).
    apply/setP => ?; by rewrite !inE -!xpair_eqE.
  rewrite Hinde.
  congr (_ * _).
    by rewrite /Q Proj14_Rvar4.
  congr cPr.
  by rewrite /Q Proj234_Rvar4.
  by apply/setP => -[i1 i2]; rewrite !inE.
rewrite -big_distrr /=; congr (_ * _).
  by rewrite /Proj14d Proj124_Rvar4.
rewrite /Q Proj234_Rvar4 Proj23.def snd_TripA_Rvar3A.
rewrite Proj23.def snd_TripA_Rvar3.
by rewrite (reasoning_by_cases_Rvar2 W).
Qed.

End decomposition.

(* WIP *)

Section conditional_probability.

Variables (A B C : finType) (P : {dist A * B * C}).

Lemma Pr_TripA (E : {set A}) (F : {set B}) (G : {set C}) :
 Pr P (setX (setX E F) G) = Pr (TripA.d P) (setX E (setX F G)).
Proof.
rewrite /Pr !big_setX /=; apply eq_bigr => a aE; rewrite big_setX /=.
by apply eq_bigr => b bF; apply eq_bigr => c cG; rewrite TripA.dE.
Qed.

Lemma Pr_Proj23_domin (a : {set A}) (b : {set B}) (c : {set C}) :
  Pr (Proj23.d P) (setX b c) = 0 -> Pr P (setX (setX a b) c) = 0.
Proof.
move/Pr_set0P => H; apply/Pr_set0P => -[[? ?] ?].
rewrite !inE /= -andbA => /and3P[Ha Hb Hc].
by apply/Proj23.domin/H; rewrite inE /= Hb Hc.
Qed.

Lemma product_rule (a : {set A}) (b : {set B}) (c : {set C}) :
  \Pr_P [ setX a b | c] = \Pr_(TripA.d P) [a | setX b c] * \Pr_(Proj23.d P) [b | c].
Proof.
rewrite /cPr; rewrite !mulRA; congr (_ * _); last by rewrite Proj23.snd.
rewrite -mulRA -Proj23.def Pr_TripA.
case/boolP : (Pr (Proj23.d P) (setX b c) == 0) => H; last by rewrite mulVR ?mulR1.
suff -> : Pr (TripA.d P) (setX a (setX b c)) = 0 by rewrite mul0R.
rewrite -Pr_TripA; exact/Pr_Proj23_domin/eqP.
Qed.

End conditional_probability.

Section tmp.
Variables (Omega : finType) (P : dist Omega) (TA TB TC TD : finType).
Variables (X : Rvar P TA) (Y : Rvar P TB) (Z : Rvar P TC) (W : Rvar P TD).

Lemma cPr_TripA a b c d :
  \Pr_(TripA.d (RvarDist.d (Rvar3 X Y <{ Z, W }>)))[ a | setX b (setX c d) ] =
  \Pr_(RvarDist.d <{ X, (Rvar3 Y Z W) }>)[ a | setX (setX b c) d ].
Proof.
rewrite /cPr.
rewrite snd_TripA_Rvar3 snd_Rvar2; congr (_ / _).
  rewrite /Pr !big_setX /=; apply eq_bigr => a0 _.
  rewrite !big_setX /=; apply eq_bigr => b0 _.
  rewrite big_setX; apply eq_bigr => c0 _ /=.
  apply eq_bigr => d0 _.
  rewrite TripA.dE /= !RvarDist.dE /=.
  rewrite /Pr /=; apply eq_bigl => w0; rewrite !inE.
  by apply/eqP/eqP => -[<- <- <- <-].
rewrite /Pr !big_setX /=; apply eq_bigr => b0 _.
rewrite big_setX; apply eq_bigr => c0 _; apply eq_bigr => d0 _.
rewrite !RvarDist.dE; rewrite /Pr; apply eq_bigl => a0; rewrite !inE.
by apply/eqP/eqP => -[<- <- <-].
Qed.

End tmp.

Section weak_union.

Variables (Omega : finType) (P : dist Omega) (TA TB TC TD : finType).
Variables (X : Rvar P TA) (Y : Rvar P TB) (Z : Rvar P TC) (W : Rvar P TD).

Lemma helper :  P |= X _|_ Y | Z -> P |= X _|_ Y | W ->
  P |= X _|_ Y | <{ Z , W }>.
Proof.
move=> HZ HW; move=> a b -[c d].
move: (HZ a b c) => {HZ}.
move: (HW a b d) => {HW}.
rewrite /cPr.
rewrite !(Pr_setX1, Pr_set1) 3!snd_Rvar3 3!Proj13_Rvar3 3!snd_Rvar2 3!Proj23_Rvar3 3!snd_Rvar2.
rewrite !RvarDist.dE => HW HZ.
Abort.

Lemma weak_union : P |= X _|_ (Rvar2 Y W) | Z -> P |= X _|_ Y | (Rvar2 Z W).
Proof.
move=> Hinde.
move=> a b -[c d].
transitivity (
  \Pr_(RvarDist.d (Rvar2 X (Rvar3 Y Z W)))[ [set a] | [set (b, c, d)] ] *
  \Pr_(RvarDist.d (Rvar2 Y (Rvar2 Z W))) [ [set b] | [set (c, d)] ]).
  by rewrite -!setX1 product_rule cPr_TripA Proj23_Rvar3.
transitivity (\Pr_(RvarDist.d (Rvar2 X Z))[ [set a] | [set c] ] *
  \Pr_(RvarDist.d (Rvar2 Y (Rvar2 Z W))) [ [set b] | [set (c, d)] ]).
  move: (Hinde a (b, d) c) => {Hinde}.
  rewrite Proj13_Rvar3.
  rewrite Proj23_Rvar3.
  rewrite -!setX1.
  case/boolP : (\Pr_(Proj23.d (RvarDist.d <{ (<{ Y, W }>), Z }>))[ [set d] | [set c] ] == 0) => Htmp.
    move=> _.
    move: Htmp.
    rewrite {1}/cPr.
    rewrite Proj23_Rvar3 snd_Rvar2.
    move/eqP; rewrite mulR_eq0 => -[].
      move=> Htmp.
      rewrite {2 4}/cPr.
      by rewrite Pr_Rvar2_domin_snd ?div0R ?mulR0 // Pr_Rvar2C.
    move/eqP/invR_eq0/eqP => Htmp.
    rewrite {2 4}/cPr.
    rewrite Pr_Rvar2_domin_snd ?div0R ?mulR0 //.
    by rewrite Pr_Rvar2_domin_fst.
  rewrite product_rule.
  rewrite Proj23_Rvar3.
  rewrite product_rule.
  rewrite [in X in X = _ -> _]mulRA.
  rewrite [in X in _ = X -> _]mulRA.
  rewrite eqR_mul2r; last first.
    exact/eqP.
  move=> Hinde.
  transitivity (
    \Pr_(TripA.d (RvarDist.d (Rvar3 X <{ Y, W }> Z)))[ [set a] | (setX
                                                                        (setX [set b] [set d])
                                                                        [set c]) ] *
          \Pr_(TripA.d (RvarDist.d <{ (<{ Y, W }>), Z }>))[ [set b] | (setX [set d] [set c]) ]
  ).
    congr (_ * _).
      rewrite /cPr.
      rewrite snd_Rvar2.
      rewrite snd_TripA_Rvar3A.
      congr (_ / _).
        rewrite /Pr !(big_setX,big_set1) /= TripA.dE /= !RvarDist.dE.
        by rewrite /Pr; apply eq_bigl => w0; rewrite !inE; apply/eqP/eqP => -[<- <- <- <-].
      rewrite /Pr !(big_setX,big_set1) /= !RvarDist.dE /Pr.
      by apply eq_bigl => w0; rewrite !inE; apply/eqP/eqP => -[<- <- <-].
    rewrite /cPr; congr (_ / _).
      rewrite /Pr !(big_setX,big_set1) TripA.dE /= !RvarDist.dE /Pr.
      by apply eq_bigl => w0; rewrite !inE; apply/eqP/eqP => -[<- <- <-].
    rewrite /Pr !(big_setX,big_set1) !Bivar.sndE; apply eq_bigr => b0 _.
    rewrite TripA.dE /= !RvarDist.dE /Pr; apply eq_bigl => w0.
    by rewrite !inE; apply/eqP/eqP => -[<- <- <-].
  rewrite Hinde.
  congr (_ * _).
  rewrite /cPr.
  rewrite snd_Rvar2.
  rewrite snd_TripA_Rvar3; congr (_ * _).
    rewrite /Pr !(big_setX,big_set1) TripA.dE /=.
    rewrite !RvarDist.dE /Pr; apply eq_bigl => w0; rewrite !inE.
    by apply/eqP/eqP => -[<- <- <-].
  by rewrite Pr_Rvar2C.
congr (_ * _); last first.
  by rewrite Proj23.def snd_TripA_Rvar3.
have Hdecomp : P |= X _|_ W | Z.
  apply decomposition with TB Y.
  move=> a0 -[d0 b0] c0.
  move: (Hinde a0 (b0, d0) c0) => {Hinde}Hinde.
  transitivity (
      \Pr_(RvarDist.d (Rvar3 X <{ Y, W }> Z))[ [set (a0, (b0, d0))] | [set c0] ]
      ).
    rewrite /cPr !snd_Rvar3; congr (_ / _).
    rewrite /Pr !big_setX /= !big_set1 !RvarDist.dE /Pr.
    apply eq_bigl => w0; rewrite !inE.
    by apply/eqP/eqP => -[<- <- <- <-].
  rewrite {}Hinde 2!Proj13_Rvar3 2!Proj23_Rvar3; congr (_ * _).
  rewrite /cPr !snd_Rvar2; congr (_ / _).
  rewrite /Pr !big_setX /= !big_set1 !RvarDist.dE /Pr; apply eq_bigl => w0.
  by rewrite !inE; apply/eqP/eqP => -[<- <- <-].
move: (Hdecomp a d c) => {Hdecomp}.
Abort.

End weak_union.
