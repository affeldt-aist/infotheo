From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.
Require Import entropy proba cproba.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

(* wip *)

Reserved Notation "P |= X _|_  Y | Z" (at level 10, X, Y, Z at next level).

Section conditionnally_independent_discrete_random_variables.

Variable (A B C : finType) (P : {dist A * B * C}).
Variables (TA TB TC : eqType).
Variables (X : {rvar A, TA}) (Y : {rvar B, TB}) (Z : {rvar C, TC}).

Definition cinde_drv:= forall a b c,
  \Pr_P[ [set i | (X i.1 == a) && (Y i.2 == b)] | Z @= c ] =
    \Pr_(Proj13.d P) [X @= a | Z @= c] *
    \Pr_(Proj23.d P) [Y @= b | Z @= c].

End conditionnally_independent_discrete_random_variables.

Notation "P |= X _|_  Y | Z" := (cinde_drv P X Y Z) : proba_scope.

Lemma set_swap (A B : finType) (P : B -> A -> bool) :
  [set h : {: B * A} | P h.1 h.2 ] = swap @: [set h | P h.2 h.1].
Proof.
apply/setP => /= -[b a]; rewrite !inE /=; apply/idP/imsetP => [H|].
- by exists (a, b) => //=; rewrite inE.
- by case => -[a0 b0]; rewrite inE /= => ? [-> ->].
Qed.

Section symmetry.

Variables (A B C : finType) (TA TB TC : eqType) (P : {dist A * B * C}).
Variables (X : {rvar A, TA}) (Y : {rvar B, TB}) (Z : {rvar C, TC}).

Lemma symmetry : P |= X _|_ Y | Z -> (TripC12.d P) |= Y _|_ X | Z.
Proof.
rewrite /cinde_drv => /= H y x z.
rewrite [in RHS]mulRC.
have -> : Proj23.d (TripC12.d P) = Proj13.d P by rewrite Proj23.def -Proj13.def.
have -> : Proj13.d (TripC12.d P) = Proj23.d P by rewrite Proj13.def Proj23.def TripC12.dI.
rewrite -H.
rewrite [in RHS]Pr_TripC12.
congr cPr.
rewrite (set_swap (fun a b => (Y a == y) && (X b == x))).
set lhs := [set h | _]. set rhs := [set h | _]. suff : lhs = rhs by move=> ->.
apply/setP => -[? ?] /=; by rewrite 2!inE andbC.
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

Definition Proj14d (A B C D : finType) (d : {dist A * B * D * C}) : {dist A * C} :=
  Proj13.d (Proj124.d d).

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

Lemma snd_Proj234 (A B C D : finType) (P : {dist A * B * C * D}) :
  Bivar.snd (Proj23.d (Proj124.d P)) = Bivar.snd (Proj234.d P).
Proof.
apply/dist_ext => d; rewrite 2!Bivar.sndE /=.
rewrite (eq_bigr (fun i => (Proj234.d P) (i.1, i.2, d))); last by case.
rewrite -(pair_bigA _ (fun i1 i2 => (Proj234.d P) (i1, i2, d))) /=.
apply eq_bigr => b _; rewrite Proj23.def.
rewrite Bivar.sndE /=.
evar (e : C -> R); rewrite (eq_bigr e); last first.
  move=> c _.
  rewrite Proj234.dE /e; reflexivity.
rewrite {}/e exchange_big; apply eq_bigr => a _.
by rewrite TripA.dE Proj124.dE.
Qed.

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

Lemma Proj13_QuadA12 (A B C D : finType) (P : {dist A * B * D * C}) :
  Proj13.d (QuadA12.d P) = Proj13.d (Proj124.d P).
Proof.
apply/dist_ext => -[a c]; rewrite !Proj13.dE /=.
rewrite (eq_bigr (fun b => (QuadA12.d P) (a, (b.1, b.2), c))); last by case.
rewrite -(pair_bigA _ (fun b1 b2 => (QuadA12.d P) (a, (b1, b2), c))) /=.
apply eq_bigr => b _; rewrite Proj124.dE /=; apply eq_bigr => d _.
by rewrite QuadA12.dE.
Qed.

Lemma Proj23_QuadA12 (A B C D : finType) (P : {dist A * B * D * C}) :
  Proj23.d (QuadA12.d P) = Proj234.d P.
Proof.
apply/dist_ext => -[[b d] c]; rewrite Proj23.dE Proj234.dE.
apply eq_bigr => /= a _.
by rewrite QuadA12.dE.
Qed.

(*Module QuadA12K.
Section quada12k.
Variables (A B C D : finType) (P : {dist A * (B * D) * C}).
Let g (x : A * B * D * C) := let: (a, b, d, c) := x in (a, (b, d), c).
Definition f (x : A * B * D * C) :=  P (g x).
Lemma f0 x : 0 <= f x.
Proof. move: x => -[[[]]] *; exact/dist_ge0. Qed.
Lemma f1 : \rsum_(x in {: A * B * D * C}) f x = 1.
Proof.
rewrite /f -(pmf1 P) /= (reindex g) /=; last first.
  exists (fun x => let: (a, (b, d), c) := x in (a,b,d,c)).
  by move=> /= [[[? ?] ?] ?].
  by move=> [] [? []] *.
by apply eq_bigr => -[[[]]].
Qed.
Definition d : {dist A * B * D * C} := locked (makeDist f0 f1).
Lemma dE x : d x = P (g x).
Proof. by rewrite /d /g; unlock => /=. Qed.
End quada12k.
End QuadA12K.*)

(* not used *)
(*Lemma snd_Proj124_QuadA12K (A B C D : finType) (P : {dist A * (B * C) * D}) :
  Bivar.snd (Proj124.d (QuadA12K.d P)) = Bivar.snd P.
Proof.
apply/dist_ext => d.
rewrite 2!Bivar.sndE /=; apply/esym.
rewrite (eq_bigr (fun i => P (i.1, i.2, d))); last by case.
rewrite -(pair_bigA _ (fun i1 i2 => P (i1, i2, d))) /=.
rewrite (eq_bigr (fun i => (Proj124.d (QuadA12K.d P)) (i.1, i.2, d))); last by case.
rewrite -(pair_bigA _ (fun i1 i2 => (Proj124.d (QuadA12K.d P)) (i1, i2, d))).
apply eq_bigr => a _ /=.
rewrite (eq_bigr (fun i => P (a, (i.1, i.2), d))); last by case.
rewrite -(pair_bigA _ (fun i1 i2 => P (a, (i1, i2), d))) /=.
apply eq_bigr => b _; rewrite Proj124.dE; apply: eq_bigr => c _.
by rewrite QuadA12K.dE.
Qed.*)

(* not used *)
(*Lemma snd_QuadA12K (A B C D : finType) (P : {dist A * (B * D) * C}) :
  Bivar.snd (QuadA12K.d P) = Bivar.snd P.
Proof.
apply/dist_ext => c; rewrite !Bivar.sndE /=.
rewrite (eq_bigr (fun i => (QuadA12K.d P) (i.1, i.2, c))); last by case.
rewrite -(pair_bigA _ (fun i1 i2 => (QuadA12K.d P) (i1, i2, c))) /=.
rewrite (eq_bigr (fun i => \rsum_(j | true) (QuadA12K.d P) (i.1, i.2, j, c))); last by case.
rewrite -(pair_bigA _ (fun i1 i2 => \rsum_(j | true) (QuadA12K.d P) (i1, i2, j, c))) /=.
rewrite (eq_bigr (fun i => P (i.1, i.2, c))); last by case.
rewrite -(pair_bigA _ (fun i1 i2 => P (i1, i2, c))) /=.
apply eq_bigr => a _.
rewrite (eq_bigr (fun i => P (a, (i.1, i.2), c))); last by case.
rewrite -(pair_bigA _ (fun i1 i2 => P (a, (i1, i2), c))) /=.
apply eq_bigr => b _; apply eq_bigr => d _; by rewrite QuadA12K.dE.
Qed.*)

(* not used *)
(*Module QuadA34K.
Section quada34.
Variables (A B C D : finType) (P : {dist A * (B * D) * C}).
Let g (x : A * B * (D * C)) := let: (a, b, (d, c)) := x in (a, (b, d), c).
Definition f (x : A * B * (D * C)) := P (g x).
Lemma f0 x : 0 <= f x.
Proof. move: x => -[[] ? ? [] ? ?]; exact/dist_ge0. Qed.
Lemma f1 : \rsum_(x in {: A * B * (D * C)}) f x = 1.
Proof.
rewrite /f -(pmf1 P) /= (reindex g) /=; last first.
  exists (fun x => let: (a, (b, d), c) := x in (a,b,(d,c))).
  by move=> /= -[[] ? ? [] ? ?].
  by move=> -[] [] ? [] ? ? ?.
by apply eq_bigr => -[[] ? ? [] ? ?].
Qed.
Definition d : {dist A * B * (D * C)} := locked (makeDist f0 f1).
Lemma dE x : d x = P (g x).
Proof. by rewrite /d /g; unlock. Qed.
End quada34.
End QuadA34K.*)

Module QuadA34.
Section quada34.
Variables (A B C D : finType) (P : {dist A * B * D * C}).
Let g (x : A * B * (D * C)) := let: (a, b, (d, c)) := x in (a, b, d, c).
Definition f (x : A * B * (D * C)) := P (g x).
Lemma f0 x : 0 <= f x.
Proof. move: x => -[[] ? ? [] ? ?]; exact/dist_ge0. Qed.
Lemma f1 : \rsum_(x in {: A * B * (D * C)}) f x = 1.
Proof.
rewrite /f -(pmf1 P) /= (reindex g) /=; last first.
  exists (fun x => let: (a, b, d, c) := x in (a,b,(d,c))).
  by move=> /= -[[] ? ? [] ? ?].
  by move=> -[] [] [].
by apply eq_bigr => -[[] ? ? [] ? ?].
Qed.
Definition d : {dist A * B * (D * C)} := locked (makeDist f0 f1).
Lemma dE x : d x = P (g x).
Proof. by rewrite /d /g; unlock. Qed.
End quada34.
End QuadA34.

(* not used *)
(*Lemma snd_TripA_TripC12 (A B C D : finType) (P : {dist A * (B * D) * C}) :
  Bivar.snd (TripA.d (TripC12.d P)) = Bivar.snd (TripA.d (TripC12.d (Proj124.d (QuadA12K.d P)))).
Proof.
apply/dist_ext => -[a0 c0]; rewrite 2!Bivar.sndE /=.
rewrite (eq_bigr (fun i => (TripA.d (TripC12.d P)) (i.1, i.2, (a0, c0)))); last by case.
rewrite -(pair_bigA _ (fun i1 i2 => (TripA.d (TripC12.d P)) (i1, i2, (a0, c0)))) /=.
apply eq_bigr => b _; rewrite TripA.dE /= TripC12.dE /= Proj124.dE /=.
by apply eq_bigr => d _; rewrite TripA.dE /= TripC12.dE /= QuadA12K.dE.
Qed.*)

Section total_fst.

Variables (A B : finType) (T : eqType)(P : {dist A * B}) (g : B -> T).
Let Y := mkRvar (Bivar.snd P) g.

Lemma total_fst E :
  Pr (Bivar.fst P) E = \rsum_(y <- fin_img Y) Pr P (setX E (Y @= y)).
Proof.
apply/esym; rewrite {1}/Pr.
evar (e : T -> R); rewrite (eq_bigr e); last first.
  by move=> r _; rewrite big_setX /= /e; reflexivity.
rewrite {}/e exchange_big /=; apply eq_bigr => a _.
rewrite Bivar.fstE.
rewrite (sum_parti_finType _ g) /=.
apply eq_bigr => r _; apply eq_bigl => b /=; by rewrite inE.
Qed.

End total_fst.

Section reasoning_by_cases_fst.

Variables (A B C : finType) (T : eqType) (P : {dist A * B * C}) (Z : {rvar C, T}).

Lemma reasoning_by_cases_fst E F : \Pr_(Bivar.fst P)[ E | F ] =
  \rsum_(z <- fin_img Z) \Pr_(TripC23.d P)[ setX E (Z @= z) | F ].
Proof.
rewrite {1}/cPr.
transitivity (\rsum_(z <- fin_img Z) Pr P (setX (setX E F) (Z @= z)) /
    Pr (Bivar.snd (Bivar.fst P)) F).
  by rewrite (total_fst _ Z) /= -big_distrl.
by apply eq_bigr => /= r _; rewrite /cPr TripC23.snd Pr_setXA.
Qed.

End reasoning_by_cases_fst.

Section total_proj124.

Variables (A B C D : finType) (T : eqType) (P : {dist A * B * C * D}).
Variable Z : {rvar C, T}.

Lemma total_proj124 E F : Pr (Proj124.d P) (setX E F) =
  \rsum_(z <- fin_img Z) Pr P (setX (setX E (Z @= z)) F).
Proof.
apply/esym.
evar (e : T -> R); rewrite (eq_bigr e); last first.
  move=> r _; rewrite /Pr big_setX /=.
  rewrite (eq_bigl (fun x => x \in setX E (Z @= r))); last first.
    move=> -[[a0 b0] c0]; by rewrite !inE.
  rewrite big_setX /= /e; reflexivity.
rewrite {}/e exchange_big /=.
rewrite [in RHS]/Pr [in RHS]big_setX /=.
apply eq_bigr => -[a0 b0] _.
evar (e : T -> R); rewrite (eq_bigr e); last first.
  move=> r _; rewrite exchange_big /= /e; reflexivity.
rewrite {}/e exchange_big /=; apply eq_bigr => d _.
rewrite Proj124.dE /= (sum_parti_finType _ Z) /=.
apply eq_bigr => r _; apply eq_bigl.
by move=> c; rewrite inE.
Qed.

Lemma reasoning_by_cases_proj124 E F : \Pr_(Proj124.d P)[E | F] =
  \rsum_(z <- fin_img Z) \Pr_P[setX E (Z @= z) | F].
Proof.
by rewrite {1}/cPr total_proj124 -[in RHS]big_distrl /= snd_Proj124.
Qed.

End total_proj124.

Section total_proj23_proj124.

Variables (A B C D : finType) (T : eqType) (P : {dist A * B * C * D}).
Variable Z : {rvar C, T}.

Lemma total_proj23_proj124 E F :
  Pr (Proj23.d (Proj124.d P)) (setX E F) =
  \rsum_(z <- fin_img Z) Pr (Proj234.d P) (setX (setX E (Z @= z)) F).
Proof.
apply/esym.
evar (e : T -> R); rewrite (eq_bigr e); last first.
  move=> r _; rewrite {1}/Pr 2!big_setX /= /e; reflexivity.
rewrite {}/e exchange_big /= [in RHS]/Pr [in RHS]big_setX /=; apply eq_bigr => b _.
evar (e : T -> R); rewrite (eq_bigr e); last first.
  move=> r _; rewrite exchange_big /= /e; reflexivity.
rewrite {}/e exchange_big /=; apply eq_bigr => d _.
transitivity (\rsum_(z <- fin_img Z) \rsum_(i | Z i == z) (Proj234.d P) (b, i, d)).
  by apply eq_bigr => r _; apply eq_bigl => c; rewrite inE.
rewrite -sum_parti_finType /=.
evar (e : C -> R); rewrite (eq_bigr e); last first.
  move=> c _; rewrite Proj234.dE /e; reflexivity.
rewrite {}/e exchange_big.
rewrite Proj23.def Bivar.sndE.
apply eq_bigr => a _.
rewrite TripA.dE /= Proj124.dE /=.
by apply eq_bigr => c _.
Qed.

Lemma reasoning_by_cases_proj23_proj124 E F :
  \Pr_(Proj23.d (Proj124.d P))[E | F] =
  \rsum_(z <- fin_img Z) \Pr_(Proj234.d P)[ setX E (Z @= z) | F ].
Proof.
rewrite {1}/cPr total_proj23_proj124.
rewrite -big_distrl /=.
congr (_ / Pr _ _).
by rewrite snd_Proj234.
Qed.

End total_proj23_proj124.

Section decomposition.

Variables (A B C D : finType) (TA TB TC TD : eqType) (P : {dist A * B * D * C}).
Variables (X : {rvar A, TA}) (Y : {rvar B, TB}) (Z : {rvar C, TC}) (W : {rvar D, TD}).
Variable YW : {rvar B * D, TB * TD}.
Hypothesis HYW : forall x, YW x = (Y x.1, W x.2).

Lemma decomposition : (QuadA12.d P |= X _|_ YW | Z) -> (Proj124.d P) |= X _|_ Y | Z.
Proof.
move=> Hinde; rewrite /cinde_drv => x y z /=.
transitivity (\rsum_(w <- fin_img W) \Pr_P
  [ [set abc | (X abc.1.1 == x) && (Y abc.1.2 == y) && (W abc.2 == w)] | Z @= z ]).
  rewrite (reasoning_by_cases_proj124 P W); apply eq_bigr => /= r _.
  congr (cPr _ _); by apply/setP => -[[a0 b0] d0]; rewrite !inE.
transitivity (\rsum_(w <- fin_img W) \Pr_(Proj14d P)[ X @= x | Z @= z ] *
  \Pr_(Proj234.d P)[ [set x | (Y x.1 == y) && (W x.2 == w)] | Z @= z ]).
  apply eq_bigr => w _.
  move: Hinde; rewrite /cinde_drv /= => /(_ x (y, w) z) => Hinde.
  transitivity (\Pr_(QuadA12.d P)[ [set h | X h.1 == x & YW h.2 == (y, w)] | Z @= z ]).
    rewrite /cPr; congr (_ / _).
      rewrite [in LHS]/Pr big_setX exchange_big /=.
      rewrite [in RHS]/Pr big_setX exchange_big /=.
      apply eq_bigr => c _.
      rewrite (reindex (fun x => let: (a, b, c) := x in (a, (b, c)))) /=; last first.
        exists (fun x => let: (a, (b, c)) := x in (a, b, c)).
        by move=> -[[]].
        by move=> -[? []].
      apply eq_big.
      - by move=> -[[a0 b0] d0]; rewrite !inE /= HYW /= xpair_eqE andbA.
      - by move=> -[[a0 b0] d0] _; rewrite QuadA12.dE.
    by rewrite -snd_QuadA12.
  rewrite Hinde.
  congr (_ * _).
    by rewrite /Proj14d Proj13_QuadA12.
  congr cPr.
  by rewrite Proj23_QuadA12.
 by apply/setP => -[b0 d0]; rewrite !inE /= HYW xpair_eqE.
rewrite -big_distrr /=; congr (_ * _).
rewrite (reasoning_by_cases_proj23_proj124 P W).
apply eq_bigr => r _; congr (cPr _ _); by apply/setP => -[b0 d0]; rewrite !inE.
Qed.

End decomposition.

Section weak_union.

Variables (A B C D : finType) (TA TB TC TD : eqType) (P : {dist A * B * D * C}).
Variables (X : {rvar A, TA}) (Y : {rvar B, TB}) (W : {rvar D, TD}) (Z : {rvar C, TC}).
Variable YW : {rvar B * D, TB * TD}.
Hypothesis HYW : forall x, YW x = (Y x.1, W x.2).
Variable WZ : {rvar D * C, TD * TC}.
Hypothesis HWZ : forall x, WZ x = (W x.1, Z x.2).

Lemma weak_union : (QuadA12.d P |= X _|_ YW | Z) -> (QuadA34.d P |= X _|_ Y | WZ).
Proof.
move=> Hinde; rewrite /cinde_drv => x y wz /=.
evar (P1 : {dist A * (B * (D * C))}).
transitivity (
\Pr_ P1 [ (X @= x) | [set i | Y i.1 == y & WZ i.2 == wz]] *
\Pr_ (TripA.d (Proj234.d P)) [ (Y @= y) | (WZ @= wz) ]
).
  admit. (* use bayes *)
evar (P3: {dist A * C}).
transitivity (
\Pr_ P3 [ (X @= x) | (Z @= wz.2) ] *
\Pr_ (Proj23.d (QuadA34.d P)) [ (Y @= y) | (WZ @= wz) ]
).
  admit. (* use independence property *)
congr (_ * _).
admit. (* because X _|_ Y | Z holds by decomposition *)
Abort.

End weak_union.
