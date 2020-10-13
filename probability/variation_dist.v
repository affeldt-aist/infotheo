(* infotheo: information theory and error-correcting codes in Coq               *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later              *)
From mathcomp Require Import all_ssreflect.
Require Import Reals.
Require Import ssrR Reals_ext Ranalysis_ext logb Rbigop fdist ln_facts.

(******************************************************************************)
(*                        The Variation Distance                              *)
(*                                                                            *)
(* 'd(P, Q) == The variation distance of two distributions P and Q            *)
(******************************************************************************)

Reserved Notation "'d(' P ',' Q ')'".

Declare Scope variation_distance_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.

Section variation_distance.

Variable A : finType.

Definition var_dist (P Q : fdist A) := \sum_(a : A) `| P a - Q a |.

Local Notation "'d(' P ',' Q ')' " := (var_dist P Q).

Lemma symmetric_var_dist p q : d(p , q) = d(q , p).
Proof. rewrite /var_dist; apply eq_bigr => ? _; by rewrite distRC. Qed.

Lemma pos_var_dist p q : 0 <= d(p , q).
Proof. by apply: sumR_ge0 => ? _ ; exact: normR_ge0. Qed.

Lemma def_var_dist p q : d( p , q) = 0 -> p = q.
Proof.
rewrite /var_dist => H; apply/fdist_ext => a.
rewrite -subR_eq0; apply/normR0_eq0; move: H.
rewrite (bigD1 a) //= paddR_eq0 => [[] // | |  ]; first exact/normR_ge0.
by apply: sumR_ge0 => ? _ ; exact/normR_ge0.
Qed.

Lemma leq_var_dist (p q : fdist A) x : `| p x - q x | <= d( p , q ).
Proof.
rewrite /var_dist (bigD1 x) //= -{1}(addR0 `| p x - q x |).
by apply/leR_add2l/sumR_ge0 => ? _; exact/normR_ge0.
Qed.

End variation_distance.

Notation "'d(' P ',' Q ')'" := (var_dist P Q) : variation_distance_scope.
