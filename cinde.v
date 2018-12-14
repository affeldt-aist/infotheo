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

Reserved Notation "X @= x" (at level 10).
Reserved Notation "P |= X _|_  Y | Z" (at level 6).

Notation "X @= x" := ([set h | X h == x]) : proba_scope.

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

(* TODO: relation inde_cdrv inde_rv *)

Definition swap {A B : finType} (ab : A * B) := (ab.2, ab.1).

Lemma injective_swap (A B : finType) (E : {set A * B}) : {in E &, injective swap}.
Proof. by case=> a b [a0 b0] /= _ _ [-> ->]. Qed.

Lemma Pr_Swap12 (A B C : finType) (T : eqType) (Z : rvar C T) (P : {dist A * B * C}) (c : T) (E : {set A * B}) :
  \Pr_P[E | Z @= c] = \Pr_(Swap12.d P)[swap @: E | Z @= c].
Proof.
rewrite /cPr Swap12.snd; congr (_ / _).
rewrite /Pr 2!big_setX /= [in LHS]exchange_big /= [in RHS]exchange_big /=.
apply eq_bigr => c' Zc'c; rewrite (big_imset _ (@injective_swap _ _ E)) /=.
apply eq_bigr => -[? ?] _; by rewrite Swap12.dE.
Qed.

Lemma set_swap (A B : finType) (P : B -> A -> bool) :
  [set h : {: B * A} | P h.1 h.2 ] = swap @: [set h | P h.2 h.1].
Proof.
apply/setP => /= -[b a]; rewrite !inE /=; apply/idP/imsetP => [H|].
- by exists (a, b) => //=; rewrite inE.
- by case => -[a0 b0]; rewrite inE /= => ? [-> ->].
Qed.

Section symmetry.

Variables (A B C D : finType) (T : eqType) (P : {dist A * B * C}).
Variables (X : {rvar A, T}) (Y : {rvar B, T}) (Z : {rvar C, T}).

Lemma symmetry : P |= X _|_ Y | Z -> (Swap12.d P) |= Y _|_ X | Z.
Proof.
rewrite /cinde_drv => /= H x y z.
rewrite [in RHS]mulRC.
have -> : Proj23.d (Swap12.d P) = Proj13.d P by rewrite Proj23.def -Proj13.def.
have -> : Proj13.d (Swap12.d P) = Proj23.d P by rewrite Proj13.def Proj23.def Swap12.dI.
rewrite -H.
rewrite [in RHS]Pr_Swap12.
congr cPr.
rewrite (set_swap (fun a b => (Y a == x) && (X b == y))).
set lhs := [set h | _]. set rhs := [set h | _]. suff : lhs = rhs by move=> ->.
apply/setP => -[? ?] /=; by rewrite 2!inE andbC.
Qed.

End symmetry.

Module Proj124.
Section proj124.
Variables (A B D C : finType) (P : {dist A * (B * D) * C}).
Definition f (abc : A * B * C) := \rsum_(x in D) P (abc.1.1, (abc.1.2, x), abc.2).
Lemma f0 x : 0 <= f x.
Proof. apply rsumr_ge0 => ? _; exact: dist_ge0. Qed.
Lemma f1 : \rsum_(x in {: A * B * C}) f x = 1.
Proof.
rewrite /f -(pmf1 P) /= pair_big /=.
rewrite (reindex (fun x => let: (a, b, c, d) := x in (a, (b, d), c))) /=; last first.
  exists (fun x => let: (a, (b, d), c) := x in (a,b,c,d)).
  by move=> /= [[[? ?] ?] ?].
  by move=> [] [? []] *.
by apply eq_bigr => -[[[]]] *.
Qed.
Definition d : {dist A * B * C} := locked (makeDist f0 f1).
Lemma dE abc: d abc = \rsum_(x in D) P (abc.1.1, (abc.1.2, x), abc.2).
Proof. by rewrite /d; unlock. Qed.
End proj124.
End Proj124.

Module Pair4A.
Section pair4a.
Variables (A B C D : finType) (P : {dist A * (B * D) * C}).
Definition f (x : A * B * D * C) := let: (a, b, d, c) := x in P (a, (b, d), c).
Lemma f0 x : 0 <= f x.
Proof. move: x => -[[[]]] *; exact/dist_ge0. Qed.
Lemma f1 : \rsum_(x in {: A * B * D * C}) f x = 1.
Proof.
rewrite /f -(pmf1 P) /=.
rewrite (reindex (fun x => let: (a, b, d, c) := x in (a, (b, d), c))) /=; last first.
  exists (fun x => let: (a, (b, d), c) := x in (a,b,d,c)).
  by move=> /= [[[? ?] ?] ?].
  by move=> [] [? []] *.
by apply eq_bigr => -[[[]]].
Qed.
Definition d : {dist A * B * D * C} := locked (makeDist f0 f1).
Lemma dE x : d x = let: (a, b, d, c) := x in P (a, (b, d), c).
Proof. by rewrite /d; unlock. Qed.
End pair4a.
End Pair4A.

Definition Proj14d (A B C D : finType) (d : {dist A * (B * D) * C}) : {dist A * C} :=
  Proj13.d d.

Definition Proj234d (A B C D : finType) (d : {dist A * (B * D) * C}) : {dist B * D * C} :=
  Bivar.snd (PairA.d d).

Section Pr_Swap23.

Variables A B C : finType.
Variable P : {dist A * B * C}.
Variables (E : {set A}) (F : {set B}) (G : {set C}).

Lemma Pr_Swap23 :
  Pr P (setX (setX E F) G) = Pr (Swap23.d P) (setX (setX E G) F).
Proof.
rewrite /Pr !big_setX /=; apply eq_bigr => a aE.
rewrite exchange_big /=; apply eq_bigr => c cG.
by apply eq_bigr => b bF; rewrite Swap23.dE.
Qed.

End Pr_Swap23.

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
  \rsum_(z <- fin_img Z) \Pr_(Swap23.d P)[ setX E (Z @= z) | F ].
Proof.
rewrite {1}/cPr.
transitivity (\rsum_(z <- fin_img Z) Pr P (setX (setX E F) (Z @= z)) /
    Pr (Bivar.snd (Bivar.fst P)) F).
  by rewrite (total_fst _ Z) /= -big_distrl.
by apply eq_bigr => /= r _; rewrite /cPr Swap23.snd Pr_Swap23.
Qed.

End reasoning_by_cases_fst.

Section total_proj124.

Variables (A B C D : finType) (T : eqType) (P : {dist A * (B * C) * D}).
Variable Z : {rvar C, T}.

Lemma total_proj124 E F : Pr (Proj124.d P) (setX E F) =
  \rsum_(z <- fin_img Z) Pr (Pair4A.d P) (setX (setX E (Z @= z)) F).
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
apply eq_bigr => r _; apply eq_big.
by move=> c; rewrite inE.
by move=> c _; rewrite Pair4A.dE.
Qed.

Lemma reasoning_by_cases_proj124 E F : \Pr_(Proj124.d P)[E | F] =
  \rsum_(z <- fin_img Z) \Pr_(Pair4A.d P)[setX E (Z @= z) | F].
Proof.
rewrite {1}/cPr total_proj124 -[in RHS]big_distrl /=; congr (_ / Pr _ _).
(* TODO: lemma *)
apply/dist_ext => d.
rewrite !Bivar.sndE /=; apply/esym.
rewrite (eq_bigr (fun i => (Pair4A.d P) (i.1, i.2, d))); last by case.
rewrite -(pair_bigA _ (fun i1 i2 => (Pair4A.d P) (i1, i2, d))) /=.
apply eq_bigr => -[a b] _.
rewrite Proj124.dE /=; apply eq_bigr => c _.
by rewrite Pair4A.dE.
Qed.

End total_proj124.

Section total_proj23_proj124.

Variables (A B C D : finType) (T : eqType) (P : {dist A * (B * C) * D}).
Variable Z : {rvar C, T}.

Lemma total_proj23_proj124 E F :
  Pr (Proj23.d (Proj124.d P)) (setX E F) =
  \rsum_(z <- fin_img Z) Pr (Proj234d P) (setX (setX E (Z @= z)) F).
Proof.
apply/esym.
evar (e : T -> R); rewrite (eq_bigr e); last first.
  move=> r _; rewrite {1}/Pr 2!big_setX /= /e; reflexivity.
rewrite {}/e exchange_big /= [in RHS]/Pr [in RHS]big_setX /=; apply eq_bigr => b _.
evar (e : T -> R); rewrite (eq_bigr e); last first.
  move=> r _; rewrite exchange_big /= /e; reflexivity.
rewrite {}/e exchange_big /=; apply eq_bigr => d _.
transitivity (\rsum_(z <- fin_img Z) \rsum_(i | Z i == z) (Proj234d P) (b, i, d)).
  by apply eq_bigr => r _; apply eq_bigl => c; rewrite inE.
rewrite -sum_parti_finType /=.
rewrite {1}/Proj234d /=.
evar (e : C -> R); rewrite (eq_bigr e); last first.
  move=> c _; rewrite Bivar.sndE /e; reflexivity.
rewrite {}/e exchange_big.
rewrite Proj23.def Bivar.sndE.
apply eq_bigr => a _.
rewrite PairA.dE /= Proj124.dE /=.
apply eq_bigr => c _.
by rewrite PairA.dE.
Qed.

Lemma reasoning_by_cases_proj23_proj124 E F :
  \Pr_(Proj23.d (Proj124.d P))[E | F] =
  \rsum_(z <- fin_img Z) \Pr_(Proj234d P)[ setX E (Z @= z) | F ].
Proof.
rewrite {1}/cPr total_proj23_proj124.
rewrite -big_distrl /=.
congr (_ / Pr _ _).
(* TODO: lemma *)
rewrite /Proj234d.
rewrite Proj23.def.
apply/dist_ext => d.
rewrite !Bivar.sndE /=; apply/esym.
rewrite (eq_bigr (fun i => (Bivar.snd (PairA.d P)) (i.1, i.2, d))); last by case.
rewrite -(pair_bigA _ (fun i1 i2 => (Bivar.snd (PairA.d P)) (i1, i2, d))) /=.
apply eq_bigr => b _.
rewrite Bivar.sndE.
evar (e : C -> R).
rewrite (eq_bigr e); last first.
  move=> c _.
  rewrite Bivar.sndE.
  rewrite /e; reflexivity.
rewrite {}/e.
rewrite exchange_big.
apply eq_bigr => a _.
rewrite PairA.dE /= Proj124.dE /=; apply eq_bigr => c _.
by rewrite PairA.dE.
Qed.

End total_proj23_proj124.

Section decomposition.

Variables (A B C D : finType) (T : eqType) (P : {dist A * (B * D) * C}).
Variables (X : {rvar A, T}) (Y : {rvar B, T}) (Z : {rvar C, T}) (W : {rvar D, T}).
Variable YW : {rvar B * D, T * T}.
Hypothesis HYW : forall x, YW x = (Y x.1, W x.2).

Lemma decomposition :
  (P |= X _|_ YW | Z) -> (Proj124.d P) |= X _|_ Y | Z.
Proof.
move=> Hinde.
rewrite /cinde_drv => x y z /=.
transitivity (\rsum_(w <- fin_img W) \Pr_(Pair4A.d P) [
  [set abc | (X abc.1.1 == x) && (Y abc.1.2 == y) && (W abc.2 == w)] | Z @= z ]).
  rewrite (reasoning_by_cases_proj124 P W); apply eq_bigr => /= r _.
  congr (cPr _ _); by apply/setP => -[[a0 b0] d0]; rewrite !inE.
transitivity (\rsum_(w <- fin_img W)
  \Pr_(Proj14d P)[ X @= x | Z @= z] *
  \Pr_(Proj234d P)[ [set x | (Y x.1 == y) && (W x.2 == w)] | Z @= z ]).
  apply eq_bigr => w _.
  move: Hinde; rewrite /cinde_drv /= => /(_ x (y, w) z) => Hinde.
  transitivity (\Pr_P[[set h | X h.1 == x & YW h.2 == (y, w)] | Z @= z ]).
    rewrite /cPr; congr (_ / _).
      rewrite {1}/Pr big_setX exchange_big /=.
      rewrite {1}/Pr big_setX exchange_big /=.
      apply eq_bigr => c _.
      rewrite (reindex (fun x => let: (a, b, c) := x in (a, (b, c)))) /=; last first.
        exists (fun x => let: (a, (b, c)) := x in (a, b, c)).
        by move=> -[[]].
        by move=> -[? []].
      apply eq_big.
      - by move=> -[[a0 b0] d0]; rewrite !inE /= HYW /= xpair_eqE andbA.
      - by move=> -[[a0 b0] d0] _; rewrite Pair4A.dE.
    congr (Pr _  _).
    (* TODO: lemma *)
    apply/dist_ext => c.
    rewrite !Bivar.sndE /=.
    rewrite (eq_bigr (fun i => (Pair4A.d P) (i.1, i.2, c))); last by case.
    rewrite -(pair_bigA _ (fun i1 i2 => (Pair4A.d P) (i1, i2, c))) /=.
    rewrite (eq_bigr (fun i => \rsum_(j | true) (Pair4A.d P) (i.1, i.2, j, c))); last by case.
    rewrite -(pair_bigA _ (fun i1 i2 => \rsum_(j | true) (Pair4A.d P) (i1, i2, j, c))) /=.
    rewrite (eq_bigr (fun i => P (i.1, i.2, c))); last by case.
    rewrite -(pair_bigA _ (fun i1 i2 => P (i1, i2, c))) /=.
    apply eq_bigr => a _.
    rewrite (eq_bigr (fun i => P (a, (i.1, i.2), c))); last by case.
    rewrite -(pair_bigA _ (fun i1 i2 => P (a, (i1, i2), c))) /=.
    apply eq_bigr => b _.
    apply eq_bigr => d _.
    by rewrite Pair4A.dE.
  rewrite Hinde; congr (_ * _).
  rewrite /cPr; congr (_ / _).
    rewrite /Proj234d Proj23.def; congr Pr.
    apply/setP => -[[b0 d0] c0]; by rewrite !inE /= HYW xpair_eqE.
  by rewrite /Proj234d Proj23.def.
rewrite -big_distrr /=; congr (_ * _).
  rewrite /Proj14d; congr cPr.
  (* TODO: lemma *)
  apply/dist_ext => -[a0 c0].
  rewrite !Proj13.dE /= (eq_bigr (fun b => P (a0, (b.1, b.2), c0))); last by case.
  rewrite -(pair_bigA _ (fun i1 i2 => P (a0, (i1, i2), c0))) /=.
  by apply eq_bigr => b _; rewrite Proj124.dE.
rewrite (reasoning_by_cases_proj23_proj124 P W).
apply eq_bigr => r _; congr (cPr _ _); by apply/setP => -[b0 d0]; rewrite !inE.
Qed.

End decomposition.
