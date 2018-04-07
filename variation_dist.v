(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div fintype tuple finfun bigop.
Require Import Reals Fourier Rpower.
Require Import Reals_ext Ranalysis_ext log2 Rbigop proba ln_facts.

(** * The Variation Distance *)

Reserved Notation "'d(' P ',' Q ')' ".

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section variation_distance.

Variable A : finType.

(** The variation distance of two distributions P and Q on X: *)

Definition var_dist (P Q : dist A) := \rsum_(a : A) Rabs (P a - Q a).

Local Notation "'d(' P ',' Q ')' " := (var_dist P Q).

Lemma symmetric_var_dist p q : d(p , q) = d(q , p).
Proof.
rewrite /var_dist ; apply eq_bigr => x0 _.
by rewrite Rabs_minus_sym.
Qed.

Lemma pos_var_dist p q : 0 <= d(p , q).
Proof. apply: rsumr_ge0 => ? _ ; exact: Rabs_pos. Qed.

Lemma def_var_dist p q : d( p , q) = 0 -> p = q.
Proof.
rewrite /var_dist => H.
apply dist_eq, pos_fun_eq, FunctionalExtensionality.functional_extensionality => x0.
apply Rminus_diag_uniq, Rabs_eq0; move: H.
rewrite (bigD1 x0) //=.
apply Rplus_eq_0_l; first exact/Rabs_pos.
apply: rsumr_ge0 => ? _ ; exact/Rabs_pos.
Qed.

Lemma leq_var_dist (p q : dist A) x : Rabs (p x - q x ) <= d( p , q ).
Proof.
rewrite /var_dist (bigD1 x) //=.
rewrite -{1}(Rplus_0_r (Rabs (p x - q x))).
apply/Rplus_le_compat_l/rsumr_ge0 => ? _; exact/Rabs_pos.
Qed.

End variation_distance.

Notation "'d(' P ',' Q ')' " := (var_dist P Q) : variation_distance_scope.
