From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.
Require Import entropy proba cproba cinde.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope proba_scope.

Section weak_union.

Variables (Omega : finType) (P : dist Omega) (TA TB TC TD : finType).
Variables (X : Rvar P TA) (Y : Rvar P TB) (Z : Rvar P TC) (W : Rvar P TD).

Lemma weak_union : P |= X _|_ (Rvar2 Y W) | Z -> P |= X _|_ Y | (Rvar2 Z W).
Proof.
Abort.

End weak_union.

Section contraction.

Variables (Omega : finType) (P : dist Omega) (TA TB TC TD : finType).
Variables (X : Rvar P TA) (Y : Rvar P TB) (Z : Rvar P TC) (W : Rvar P TD).

Lemma contraction : P |= X _|_ W | (Rvar2 Z Y) -> P |= X _|_ (Rvar2 Y W) | Z.
Proof.
Abort.

End contraction.
