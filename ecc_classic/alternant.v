(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg finalg poly polydiv.
From mathcomp Require Import cyclic perm matrix mxpoly vector mxalgebra zmodp.
From mathcomp Require Import finfield falgebra fieldext.
Require Import ssr_ext ssralg_ext linearcode.
Require Import dft poly_decoding grs bch.

(**md**************************************************************************)
(* Work in progress about alternant and Goppa codes                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Local Open Scope vec_ext_scope.

Section location_polynomial.
Variables (n : nat) (F : finFieldType) (a : 'rV[F]_n).

(** the values of the location polynomial at points a``_i,
   they determine uniquely the location polynomial of size n (i.e., deg <= n.-1) *)
Definition location_polynomial_points :=
  \row_i \prod_(j < n | j != i) (a ``_ i - a ``_ j).

End location_polynomial.

(* NB: the notation GRS_k(kappa, g) in the classification book *)
Section grs_polynomial.
Variables (n : nat) (F : finFieldType) (a : 'rV[F]_n).
Variable g : {poly F}.
Let b := \row_(i < n) (((location_polynomial_points a) ``_ i)^-1 * g.[a ``_ i]).
Variable (r : nat).

Definition GRS_PCM_polynomial := @GRS.PCM _ F a b r.

End grs_polynomial.

Section injection_into_extension_field.
Variables (F0 : finFieldType) (F1 : fieldExtType F0).

Definition ext_inj : {rmorphism F0 -> F1} :=
 [the {rmorphism F0 -> F1} of @GRing.in_alg _ _].

Definition ext_inj_tmp : {rmorphism F0 -> (FinFieldExtType F1)} := ext_inj.

Variable n : nat.

Definition ext_inj_rV : 'rV[F0]_n -> 'rV[F1]_n := @map_mx _ _ ext_inj 1 n.

End injection_into_extension_field.

Section alternant_code.
(** declare F_q *)
Variable p u' : nat.
Let u := u'.+1.
Hypothesis primep : prime p.

Let Fq : finFieldType := GF u primep.
Let q := p ^ u.
Let p_char : p \in [char Fq].
Proof. apply char_GFqm. Qed.

(** declare F_{q^m} *)
Variable m' : nat.
Let m := m'.+1.
Variable Fqm : fieldExtType Fq.
Hypothesis card_Fqm : #| FinFieldExtType Fqm | = q ^ m.

(** build GRS_k(kappa, g) *)
Variable n : nat.
Variable a : 'rV[Fqm]_n.
Variable g : {poly Fqm}.
Variable k : nat.

Definition alternant_PCM : 'M_(k, n) := @GRS_PCM_polynomial n (FinFieldExtType Fqm) a g k.

Definition alternant_code := Rcode.t (@ext_inj_tmp Fq Fqm) (kernel alternant_PCM).

(** Goppa codes are a special case of alternant codes *)
Definition goppa_code_condition := size g = (n - k).+1.

End alternant_code.

Section narrow_sense_BCH_are_Goppa.
(** declare F_q *)
Variable p u' : nat.
Let u := u'.+1.
Hypothesis primep : prime p.

Let Fq : finFieldType := GF u primep.
Let q := p ^ u.
Let p_char : p \in [char Fq].
Proof. apply char_GFqm. Qed.

(** declare F_{q^m} *)
Variable m' : nat.
Let m := m'.+1.
Variable Fqm : fieldExtType Fq.
Hypothesis card_Fqm : #| FinFieldExtType Fqm | = q ^ m.

(** we are talking about narrow-sense Goppa codes *)
Let n : nat := (q^m).-1.
Variable e : Fqm.
Hypothesis e_prim : n.-primitive_root e.
Let a : 'rV[Fqm]_n := rVexp e n.
Variable t : nat.

(** we have to instantiate Goppa codes with a monomial to recover BCH codes *)
Let g : {poly (FinFieldExtType Fqm)} := 'X^(n - t).

(** from the Goppa code condition, we have only one choice for its degree *)
Let goppa_code_condition_check : goppa_code_condition n g t.
Proof. by rewrite /goppa_code_condition size_polyXn. Qed.

(* NB: we only have binary BCH codes, so we should maybe restrict q at
this point *)

(** wip *)
Lemma narrow_sense_BCH_are_Goppa :
  @BCH.PCM (FinFieldExtType _) _ a t =
  @alternant_PCM _ u' primep Fqm _ a g t(*?*).
Proof.
rewrite /BCH.code /alternant_code.
Abort.

End narrow_sense_BCH_are_Goppa.
