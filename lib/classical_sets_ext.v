(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp classical_sets.

(******************************************************************************)
(*                   Additional lemmas about classical sets                   *)
(******************************************************************************)

Section PR_to_classical_sets.

Variable T U : Type.
Implicit Types A B C : set T.

Local Open Scope classical_set_scope.

Lemma subset_image (f : T -> U) A (Y : set U) :
  f @` A `<=` Y <-> forall a, A a -> Y (f a).
Proof.
split=> H.
- by move=> a Xa; apply/H/imageP.
- by move=> b [] a Xa <-; apply: H.
Qed.

Lemma bigcup_of_const (P : set U) (X : U -> set T) (i : U) :
  P i -> (forall j, P j -> X j = X i) -> \bigcup_(j in P) X j = X i.
Proof.
move=> Pi H; rewrite eqEsubset; split=> a; by [case=> j /H -> | exists i].
Qed.

Lemma bigsubsetU (P : set U) (X : U -> set T) (Y : set T) :
  (forall i, P i -> X i `<=` Y) <-> \bigcup_(i in P) X i `<=` Y.
Proof.
split.
- by move=> H a [] i Pi Xia; apply: (H i).
- by move=> H i Pi a Xia; apply: H; exists i.
Qed.

Lemma bigcup_set0P (P : set U) (F : U -> set T) :
  reflect (exists i, P i /\ F i !=set0) (\bigcup_(i in P) F i != set0).
Proof.
apply: (iffP idP).
- by case/set0P => a [] i Si Fia; exists i; split; [ | exists a].
- by case=> i [] Si [] a Fia; apply/set0P; exists a, i.
Qed.

Lemma set1_inj (x y : T) : [set x] = [set y] -> x = y.
Proof. by case/seteqP; move/(_ x)/(_ erefl) ->. Qed.

End PR_to_classical_sets.
