(* infotheo: information theory and error-correcting codes in Coq               *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp classical_sets.

(******************************************************************************)
(*                   Additional lemmas about classical sets                   *)
(******************************************************************************)

Section PR_to_classical_sets.

Variable T U : Type.
Implicit Types A B C : set T.

Local Open Scope classical_set_scope.

Lemma eq_imagel (f g : T -> U) A :
  (forall a, A a -> f a = g a) -> f @` A = g @` A.
Proof.
by move=> H; rewrite eqEsubset; split=> a;
  case => x Xx <-; [rewrite H | rewrite -H] => //; exists x.
Qed.

Lemma subset_image (f : T -> U) A (Y : set U) :
  f @` A `<=` Y <-> forall a, A a -> Y (f a).
Proof.
split=> H.
- by move=> a Xa; apply/H/imageP.
- by move=> b [] a Xa <-; apply H.
Qed.

Lemma eq_bigcupr (P : set U) (X Y : U -> set T) :
  X =1 Y -> bigsetU P X = bigsetU P Y.
Proof. by move/funext ->. Qed.

Lemma eq_bigcup (P Q : set U) (X Y : U -> set T) :
  P = Q -> X =1 Y -> bigsetU P X = bigsetU Q Y.
Proof. by move=> -> /funext ->. Qed.

Lemma bigcup_of_singleton (P : set U) (f : U -> T) :
  \bigcup_(x in P) [set f x] = f @` P.
Proof.
rewrite eqEsubset; split=> a;
  by [case=> i Pi ->; apply imageP | case=> i Pi <-; exists i].
Qed.

Lemma bigcup_image V (P : set V) (f : V -> U) (X : U -> set T) :
  \bigcup_(x in f @` P) X x = \bigcup_(x in P) X (f x).
Proof.
rewrite eqEsubset; split=> x.
- by case=> j [] i pi <- Xfix; exists i.
- by case=> i Pi Xfix; exists (f i); first by  exists i.
Qed.

Lemma bigcup_of_const (P : set U) (X : U -> set T) (i : U) :
  P i -> (forall j, P j -> X j = X i) -> \bigcup_(j in P) X j = X i.
Proof.
move=> Pi H; rewrite eqEsubset; split=> a; by [case=> j /H -> | exists i].
Qed.

Lemma bigsubsetU (P : set U) (X : U -> set T) (Y : set T) :
  (forall i, P i -> X i `<=` Y) <-> bigsetU P X `<=` Y.
Proof.
split.
- by move=> H a [] i Pi Xia; apply (H i).
- by move=> H i Pi a Xia; apply H; exists i.
Qed.

Lemma bigcup_set0P (P : set U) (F : U -> set T) :
  reflect (exists i, P i /\ F i !=set0) (bigsetU P F != set0).
Proof.
apply: (iffP idP).
- by case/set0P => a [] i Si Fia; exists i; split; [ | exists a].
- by case=> i [] Si [] a Fia; apply/set0P; exists a, i.
Qed.

Lemma bigcupset2E (A B : set T) : \bigcup_(i in [set A; B]) i = A `|` B.
Proof.
(* TODO: use bigcup2E when available through mathcomp-analysis? *)
rewrite eqEsubset;split => x.
  by case=> K [] -> Hx; [left | right].
by case=> ?; [exists A => //; left|exists B => //; right].
Qed.

End PR_to_classical_sets.

(*Notation imageA := (deprecate imageA image_comp _) (only parsing).
Notation image_idfun := (deprecate image_idfun image_id _) (only parsing).
Notation bigcup0 := (deprecate bigcup0 bigcup_set0 _) (only parsing).
Notation bigcup1 := (deprecate bigcup1 bigcup_set1 _) (only parsing).
Notation bigcup_const := (deprecate bigcup_const bigcup_of_const _) (only parsing).*)
