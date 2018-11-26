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

Section conditionnally_independent_discrete_random_variables.

Variables (A : finType) (f : A -> R).
Variables (B : finType) (g : B -> R).
Variables (C : finType) (h : C -> R).
Variable PQR : dist [finType of A * B * C].
Let X := mkRvar (Bivar.fst (Bivar.fst PQR)) f.
Let Y := mkRvar (Bivar.snd (Bivar.fst PQR)) g.
Let Z := mkRvar (Bivar.snd PQR) h.

Local Notation "X ?= x" := ([set h | X h == x]).

Definition cinde_drv := forall (a : R) (b : R) (c : R),
  \Pr_PQR[ [set h | (X h.1 == a) && (Y h.2 == b)] | Z ?= c ] =
    \Pr_(Proj13.d PQR) [ X ?= a | Z ?= c ] *
    \Pr_(Proj23.d PQR) [ Y ?= b | Z ?= c ].

End conditionnally_independent_discrete_random_variables.

Notation "P |= X _|_  Y | Z" := (cinde_drv X Y Z P) (at level 6) : proba_scope.

(* TODO: relation inde_cdrv inde_rv *)

Section symmetry.

Variables (A : finType) (X : rvar A).
Variables (B : finType) (Y : rvar B).
Variables (C : finType) (Z : rvar C).

Lemma symmetry (P : {dist A * B * C}) :
  P |= X _|_ Y | Z -> (Swap12.d P) |= Y _|_ X | Z.
Proof.
rewrite /cinde_drv => /= H a b c.
rewrite [in RHS]mulRC.
have -> : Proj23.d (Swap12.d P) = Proj13.d P.
  (* TODO: lemma? *) by rewrite Proj23.def -Proj13.def.
have -> : Proj13.d (Swap12.d P) = Proj23.d P.
  (* TODO: lemma? *) by rewrite Proj13.def Proj23.def Swap12.dI.
rewrite -H.
have -> : forall EAB, \Pr_P[EAB | [set h | Z h == c] ] =
       \Pr_(Swap12.d P)[ (fun x => (x.2, x.1)) @: EAB | [set h | Z h == c] ].
  move=> /= EAB.
  rewrite /cPr Swap12.snd.
  congr (_ / _).
  rewrite /Pr !big_setX /= exchange_big /= [in RHS]exchange_big /=.
  apply eq_bigr => c' Zc'c.
  rewrite big_imset /=.
    by apply: eq_bigr => -[? ?] _; rewrite Swap12.dE.
  by case=> x1 x2 [y1 y2] /= _ _ [-> ->].
congr cPr; apply/setP => /= i.
rewrite !inE.
apply/idP/idP => [/andP[/eqP <- /eqP <-]|].
  apply/imsetP.
  exists (i.2, i.1); last by case: i.
  by rewrite inE /= !eqxx.
case/imsetP; case=> a' b'; rewrite inE /= => /andP[/eqP <- /eqP <- ->].
by rewrite /= !eqxx.
Qed.

End symmetry.
