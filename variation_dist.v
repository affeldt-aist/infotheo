(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div fintype tuple finfun bigop.
Require Import Reals Fourier.
Require Import ssrR Reals_ext Ranalysis_ext logb Rbigop proba ln_facts.

(** * The Variation Distance *)

Reserved Notation "'d(' P ',' Q ')'".

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section variation_distance.

Variable A : finType.

(** The variation distance of two distributions P and Q on X: *)
Definition var_dist (P Q : dist A) := \rsum_(a : A) `| P a - Q a |.

Local Notation "'d(' P ',' Q ')' " := (var_dist P Q).

Lemma symmetric_var_dist p q : d(p , q) = d(q , p).
Proof. rewrite /var_dist; apply eq_bigr => ? _; by rewrite distRC. Qed.

Lemma pos_var_dist p q : 0 <= d(p , q).
Proof. apply: rsumr_ge0 => ? _ ; exact: normR_ge0. Qed.

Lemma def_var_dist p q : d( p , q) = 0 -> p = q.
Proof.
rewrite /var_dist => H.
apply dist_eq, pos_fun_eq, FunctionalExtensionality.functional_extensionality => x0.
apply/eqP; rewrite -subR_eq0; apply/eqP/normR0_eq0; move: H.
rewrite (bigD1 x0) //=.
apply Rplus_eq_0_l; first exact/normR_ge0.
apply: rsumr_ge0 => ? _ ; exact/normR_ge0.
Qed.

Lemma leq_var_dist (p q : dist A) x : `| p x - q x | <= d( p , q ).
Proof.
rewrite /var_dist (bigD1 x) //= -{1}(addR0 `| p x - q x |).
apply/leR_add2l/rsumr_ge0 => ? _; exact/normR_ge0.
Qed.

End variation_distance.

Notation "'d(' P ',' Q ')'" := (var_dist P Q) : variation_distance_scope.
