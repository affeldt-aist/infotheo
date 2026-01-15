(******************************************************************************)
(*                                                                            *)
(* Benaloh as Homomorphic Encryption HB Instance                              *)
(*                                                                            *)
(* This file shows that Benaloh implements the HE structure from              *)
(* he_sig.v using Hierarchy Builder (HB).                                     *)
(*                                                                            *)
(* Structure:                                                                 *)
(*   Section Benaloh_HE - HB instance for Benaloh encryption                  *)
(*                                                                            *)
(* == Informal guide ==                                                       *)
(*                                                                            *)
(* HE structure asks for existential homomorphism laws:                        *)
(*   ∃ randomness r, Emul(E(m1;r1),E(m2;r2)) = E(m1+m2; r)                     *)
(*   ∃ randomness r, Epow(E(m1;r),m2) = E(m1*m2; r)                            *)
(*                                                                            *)
(* For Benaloh, the witnesses are concrete: u1*u2 and u^k, because             *)
(*   E(m;u) = y^m · u^r  (mod n)                                               *)
(* makes the randomness compose by multiplication / exponentiation.            *)
(*                                                                            *)
(* Section Benaloh_Extra provides stronger equalities as definitional lemmas   *)
(* (no exists), plus a small coercion bridge between ring-multiplication on    *)
(* Z_r and scalar-multiplication ( *+ ).                                       *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg zmodp.
From infotheo Require Import homomorphic_encryption.benaloh1994.benaloh_enc.
From infotheo Require Import homomorphic_encryption.he_sig.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*                        Benaloh HB Instance                                  *)
(* ========================================================================== *)

Section Benaloh_HE.

Variables (n r : nat).
Hypothesis n_gt1 : (1 < n)%N.
Hypothesis r_gt1 : (1 < r)%N.
Variable y : 'Z_n.
Hypothesis y_order_r : y ^+ r = 1.

Definition Benaloh_HE_types : HE_types := MkHE 'Z_r 'Z_n 'Z_n.

Definition benaloh_he_enc (m : 'Z_r) (u : 'Z_n) : 'Z_n := benaloh_enc y m u.

(* Homomorphic addition: ring multiplication on ciphertexts *)
Definition benaloh_Emul (c1 c2 : 'Z_n) : 'Z_n := c1 * c2.

(* Homomorphic scalar multiplication: ring exponentiation *)
Definition benaloh_Epow (c : 'Z_n) (m : 'Z_r) : 'Z_n := c ^+ (m : nat).

Lemma benaloh_Emul_eq_add : forall (m1 m2 : 'Z_r) (r1 r2 : 'Z_n),
  exists rr : 'Z_n, benaloh_Emul (benaloh_he_enc m1 r1) (benaloh_he_enc m2 r2) 
    = benaloh_he_enc (m1 + m2) rr.
Proof.
  move=> m1 m2 u1 u2.
  exists (u1 * u2).
  rewrite /benaloh_Emul.
  exact: (enc_mul_dist r_gt1 y_order_r).
Qed.

Lemma benaloh_Epow_eq_mul : forall (m1 m2 : 'Z_r) (rr : 'Z_n),
  exists r' : 'Z_n, benaloh_Epow (benaloh_he_enc m1 rr) m2 
    = benaloh_he_enc (m1 * m2) r'.
Proof.
  move=> m1 m2 u.
  exists (u ^+ m2).
  rewrite /benaloh_Epow (enc_exp_dist r_gt1 y_order_r).
  (* Need: m1 *+ (m2 : nat) = m1 * m2 *)
  congr (benaloh_enc _ _ _).
  rewrite mulrC -[m2 in m2 * _]natr_Zp mulr_natl.
  reflexivity.
Qed.

HB.instance Definition Benaloh_HE_isHE : isHE Benaloh_HE_types := 
  @isHE.phant_Build Benaloh_HE_types benaloh_he_enc benaloh_Emul benaloh_Epow 
    benaloh_Emul_eq_add benaloh_Epow_eq_mul.

End Benaloh_HE.

(* ========================================================================== *)
(*                        Additional Benaloh Properties                        *)
(* ========================================================================== *)

(* These lemmas provide stronger results than HE (concrete randomness) *)

Section Benaloh_Extra.

Variables (n r : nat).
Hypothesis n_gt1 : (1 < n)%N.
Hypothesis r_gt1 : (1 < r)%N.
Variable y : 'Z_n.
Hypothesis y_order_r : y ^+ r = 1.

Definition benaloh_extra_enc (m : 'Z_r) (u : 'Z_n) : 'Z_n := benaloh_enc y m u.

(* Concrete randomness formulas *)
Lemma Emul_randomness : forall (m1 m2 : 'Z_r) (u1 u2 : 'Z_n),
  benaloh_extra_enc m1 u1 * benaloh_extra_enc m2 u2 = benaloh_extra_enc (m1 + m2) (u1 * u2).
Proof. exact: (enc_mul_dist r_gt1 y_order_r). Qed.

Lemma Epow_randomness : forall (m : 'Z_r) (k : nat) (u : 'Z_n),
  (benaloh_extra_enc m u) ^+ k = benaloh_extra_enc (m *+ k) (u ^+ k).
Proof. exact: (enc_exp_dist r_gt1 y_order_r). Qed.

(* Ring multiplication version of scalar homomorphism *)
Lemma scalar_eq_ring_mul : forall (m1 m2 : 'Z_r),
  m1 * m2 = m1 *+ (m2 : nat).
Proof.
  move=> m1 m2.
  rewrite mulrC -[m2 in m2 * _]natr_Zp mulr_natl.
  reflexivity.
Qed.

(* Epow with ring exponent *)
Lemma Epow_ring : forall (m1 m2 : 'Z_r) (u : 'Z_n),
  exists u' : 'Z_n, (benaloh_extra_enc m1 u) ^+ (m2 : nat) = benaloh_extra_enc (m1 * m2) u'.
Proof.
  move=> m1 m2 u.
  exists (u ^+ m2).
  rewrite (enc_exp_dist r_gt1 y_order_r).
  by rewrite scalar_eq_ring_mul.
Qed.

End Benaloh_Extra.
