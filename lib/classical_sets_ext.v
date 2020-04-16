(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp classical_sets.

(* Additional lemmas about classical sets *)

Section PR_to_classical_sets.

Variable T U : Type.
Implicit Types A B C : set T.

Local Open Scope classical_set_scope.

Lemma subset0 A : (A `<=` set0) = (A = set0).
Proof. rewrite propeqE; split => [?|-> //]; exact/eqEsubset. Qed.

Lemma subUset A B C : (B `|` C `<=` A) = ((B `<=` A) /\ (C `<=` A)).
Proof.
rewrite propeqE; split => [H|H]; first by split => x Hx; apply H; [left|right].
move=> x [] Hx; [exact: (proj1 H)|exact: (proj2 H)].
Qed.

Lemma set0P A : (A != set0) <-> (A !=set0).
Proof.
split; [move=> A_neq0|by case=> t tA; apply/negP => /eqP A0; rewrite A0 in tA].
apply/existsp_asboolP; rewrite -(negbK `[exists _, _]); apply/negP.
rewrite existsbE => /forallp_asboolPn H.
move/negP : A_neq0; apply; apply/eqP; rewrite funeqE => t; rewrite propeqE.
move: (H t); by rewrite asboolE.
Qed.

Lemma eq_imagel (f g : T -> U) A :
  (forall a, A a -> f a = g a) -> f @` A = g @` A.
Proof.
by move=> H; apply eqEsubset=> a;
  case => x Xx <-; [rewrite H | rewrite -H] => //; exists x.
Qed.

Lemma image_comp V (f : T -> U) (g : U -> V) A : g @` (f @` A) = (g \o f) @` A.
Proof.
apply eqEsubset => c.
- by case => b [] a Xa <- <-; apply/imageP.
- by case => a Xa <-; apply/imageP/imageP.
Qed.

Lemma image_id A : id @` A = A.
Proof. by apply eqEsubset => a; [case=> /= x Xx <-|exists a]. Qed.

Lemma image_setU (f : T -> U) A B : f @` (A `|` B) = f @` A `|` f @` B.
Proof.
apply eqEsubset => b.
- by case=> a [] Ha <-; [left | right]; apply imageP.
- by case=> -[] a Ha <-; apply imageP; [left | right].
Qed.

Lemma image_set1 (f : T -> U) (t : T) : f @` [set t] = [set f t].
Proof. by apply eqEsubset => b; [case=> a' -> <- | move->; apply imageP]. Qed.

Lemma image_subset (f : T -> U) A (Y : set U) :
  f @` A `<=` Y <-> forall a, A a -> Y (f a).
Proof.
split=> H.
- by move=> a Xa; apply/H/imageP.
- by move=> b [] a Xa <-; apply H.
Qed.

Lemma fullimage_subset (f : T -> U) (Y : set U) :
  f @` setT `<=` Y <-> forall t, Y (f t).
Proof.
rewrite (_ : (forall a, Y (f a)) <-> (forall a, setT a -> Y (f a))) ?image_subset //.
by firstorder.
Qed.

Lemma eq_bigcupl (P Q : set U) (X : U -> set T) :
  P = Q -> bigsetU P X = bigsetU Q X.
Proof. by move ->. Qed.

Lemma eq_bigcupr (P : set U) (X Y : U -> set T) :
  X =1 Y -> bigsetU P X = bigsetU P Y.
Proof. by move/funext ->. Qed.

Lemma eq_bigcup (P Q : set U) (X Y : U -> set T) :
  P = Q -> X =1 Y -> bigsetU P X = bigsetU Q Y.
Proof. by move=> -> /funext ->. Qed.

Lemma bigcup_set1 (P : set U) (f : U -> T) :
  \bigcup_(x in P) [set f x] = f @` P.
Proof.
apply eqEsubset=> a.
- by case=> i Pi ->; apply imageP.
- by case=> i Pi <-; exists i.
Qed.

Lemma bigcup0 (X : U -> set T) : bigsetU set0 X = set0.
Proof. by apply eqEsubset => a // [] //. Qed.

Lemma bigcup1 (i : U) (X : U -> set T) : bigsetU [set i] X = X i.
Proof.
apply eqEsubset => a.
- by case=> j ->.
- by exists i.
Qed.

Lemma bigcup_const (P : set U) (X : U -> set T) (i : U) :
  P i -> (forall j, P j -> X j = X i) -> bigsetU P X = X i.
Proof.
move=> Pi H; apply eqEsubset=> a.
- by case=> j /H ->.
- by exists i.
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

Lemma bigcup_image V (P : set V) (f : V -> U) (X : U -> set T) :
  \bigcup_(x in f @` P) X x = \bigcup_(x in P) X (f x).
Proof.
apply eqEsubset=> x.
- by case=> j [] i pi <- Xfix; exists i.
- by case=> i Pi Xfix; exists (f i); first by  exists i.
Qed.

End PR_to_classical_sets.

Notation imageA := (deprecate imageA image_comp _) (only parsing).
Notation image_idfun := (deprecate image_idfun image_id _) (only parsing).
