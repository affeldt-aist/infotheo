(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import reals.
Require Import fdist.

(**md**************************************************************************)
(* # The Variation Distance                                                   *)
(*                                                                            *)
(* ```                                                                        *)
(*   'd(P, Q) == The variation distance of two distributions P and Q          *)
(* ```                                                                        *)
(******************************************************************************)

Reserved Notation "'d(' P ',' Q ')'".

Declare Scope variation_distance_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Import GRing.Theory Num.Theory.

Section variation_distance.

Context {R : realType}.
Variable A : finType.

Definition var_dist (P Q : R.-fdist A) := \sum_(a : A) `| P a - Q a |.

Local Notation "'d(' P ',' Q ')' " := (var_dist P Q).

Lemma symmetric_var_dist p q : d(p , q) = d(q , p).
Proof. rewrite /var_dist; apply eq_bigr => ? _; by rewrite distrC. Qed.

Lemma pos_var_dist p q : 0 <= d(p , q).
Proof. by apply/sumr_ge0 => ? _; apply/normr_ge0. Qed.

Lemma def_var_dist p q : d( p , q) = 0 -> p = q.
Proof.
rewrite /var_dist => H; apply/fdist_ext => a.
apply/eqP; rewrite -subr_eq0; apply/eqP/normr0_eq0; move: H.
move/eqP; rewrite (bigD1 a) //= paddr_eq0 //; first by case/andP=> /eqP->.
by apply/sumr_ge0 => ? _; apply/normr_ge0.
Qed.

Lemma leq_var_dist (p q : R.-fdist A) x : `| p x - q x | <= d( p , q ).
Proof.
rewrite /var_dist (bigD1 x) //= -{1}(addr0 `| p x - q x |).
by rewrite lerD2l sumr_ge0.
Qed.

End variation_distance.

Notation "'d(' P ',' Q ')'" := (var_dist P Q) : variation_distance_scope.
