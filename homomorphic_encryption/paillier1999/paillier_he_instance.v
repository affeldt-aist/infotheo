(******************************************************************************)
(*                                                                            *)
(* Paillier as Homomorphic Encryption HB Instance                             *)
(*                                                                            *)
(* This file shows that Paillier implements the HE structure from             *)
(* he_sig.v using Hierarchy Builder (HB).                                     *)
(*                                                                            *)
(* Structure:                                                                 *)
(*   Section Paillier_HE - HB instance for Paillier encryption                *)
(*                                                                            *)
(* == Informal guide ==                                                       *)
(*                                                                            *)
(* HE structure exposes homomorphic laws with existential randomness.         *)
(* For Paillier, the witnesses are concrete because                           *)
(*   E(m;r) = g^m * r^n  (mod n^2)                                            *)
(* implies:                                                                   *)
(*   E(m1;r1)*E(m2;r2) = E(m1+m2; r1r2)                                       *)
(*   E(m;r)^k = E(m *+ k; r^k)                                                *)
(*                                                                            *)
(* Section Paillier_Extra provides stronger "concrete randomness" identities  *)
(* (no exists), plus a coercion bridge between ring multiplication on Z_n     *)
(* and scalar multiplication ( *+ ).                                          *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg zmodp.
From infotheo Require Import homomorphic_encryption.paillier1999.paillier_enc.
From infotheo Require Import homomorphic_encryption.he_sig.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*                        Paillier HB Instance                                 *)
(* ========================================================================== *)

Section Paillier_HE.

Variable n : nat.
Hypothesis n_gt1 : (1 < n)%N.
Let n2 := (n * n)%N.

(* n^2 > 1 follows from n > 1 *)
Lemma n2_gt1 : (1 < n2)%N.
Proof.
  rewrite /n2 -[X in (X < _)%N]muln1.
  by apply: ltn_mul.
Qed.

Variable g : 'Z_n2.
Hypothesis g_order_n : g ^+ n = 1.

Definition Paillier_HE_types : HE_types := MkHE 'Z_n 'Z_n2 'Z_n2.

Definition paillier_he_enc (m : 'Z_n) (r : 'Z_n2) : 'Z_n2 := paillier_enc g m r.

(* Homomorphic addition: ring multiplication on ciphertexts *)
Definition paillier_Emul (c1 c2 : 'Z_n2) : 'Z_n2 := c1 * c2.

(* Homomorphic scalar multiplication: ring exponentiation *)
Definition paillier_Epow (c : 'Z_n2) (m : 'Z_n) : 'Z_n2 := c ^+ (m : nat).

Lemma paillier_Emul_eq_add : forall (m1 m2 : 'Z_n) (r1 r2 : 'Z_n2),
  exists rr : 'Z_n2, paillier_Emul (paillier_he_enc m1 r1) (paillier_he_enc m2 r2) 
    = paillier_he_enc (m1 + m2) rr.
Proof.
  move=> m1 m2 r1 r2.
  exists (r1 * r2).
  rewrite /paillier_Emul.
  exact: (enc_mul_dist n_gt1 g_order_n).
Qed.

Lemma paillier_Epow_eq_mul : forall (m1 m2 : 'Z_n) (rr : 'Z_n2),
  exists r' : 'Z_n2, paillier_Epow (paillier_he_enc m1 rr) m2 
    = paillier_he_enc (m1 * m2) r'.
Proof.
  move=> m1 m2 r.
  exists (r ^+ m2).
  rewrite /paillier_Epow (enc_exp_dist n_gt1 g_order_n).
  congr (paillier_enc _ _ _).
  rewrite mulrC -[m2 in m2 * _]natr_Zp mulr_natl.
  reflexivity.
Qed.

HB.instance Definition Paillier_HE_isHE : isHE Paillier_HE_types := 
  @isHE.phant_Build Paillier_HE_types paillier_he_enc paillier_Emul paillier_Epow 
    paillier_Emul_eq_add paillier_Epow_eq_mul.

End Paillier_HE.

(* ========================================================================== *)
(*                        Additional Paillier Properties                       *)
(* ========================================================================== *)

(* These lemmas provide stronger results than HE (concrete randomness) *)

Section Paillier_Extra.

Variable n : nat.
Hypothesis n_gt1 : (1 < n)%N.
Let n2 := (n * n)%N.
Variable g : 'Z_n2.
Hypothesis g_order_n : g ^+ n = 1.

Definition paillier_extra_enc (m : 'Z_n) (r : 'Z_n2) : 'Z_n2 := paillier_enc g m r.

(* Concrete randomness formulas *)
Lemma Emul_randomness : forall (m1 m2 : 'Z_n) (r1 r2 : 'Z_n2),
  paillier_extra_enc m1 r1 * paillier_extra_enc m2 r2 = paillier_extra_enc (m1 + m2) (r1 * r2).
Proof. exact: (enc_mul_dist n_gt1 g_order_n). Qed.

Lemma Epow_randomness : forall (m : 'Z_n) (k : nat) (r : 'Z_n2),
  (paillier_extra_enc m r) ^+ k = paillier_extra_enc (m *+ k) (r ^+ k).
Proof. exact: (enc_exp_dist n_gt1 g_order_n). Qed.

(* Ring multiplication version of scalar homomorphism *)
Lemma scalar_eq_ring_mul : forall (m1 m2 : 'Z_n),
  m1 * m2 = m1 *+ (m2 : nat).
Proof.
  move=> m1 m2.
  rewrite mulrC -[m2 in m2 * _]natr_Zp mulr_natl.
  reflexivity.
Qed.

(* Epow with ring exponent *)
Lemma Epow_ring : forall (m1 m2 : 'Z_n) (r : 'Z_n2),
  exists r' : 'Z_n2, (paillier_extra_enc m1 r) ^+ (m2 : nat) = paillier_extra_enc (m1 * m2) r'.
Proof.
  move=> m1 m2 r.
  exists (r ^+ m2).
  rewrite (enc_exp_dist n_gt1 g_order_n).
  by rewrite scalar_eq_ring_mul.
Qed.

End Paillier_Extra.
