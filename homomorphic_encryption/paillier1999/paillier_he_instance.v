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
(* HE structure requires concrete randomness formulas:                         *)
(*   Emul(E(m1;r1), E(m2;r2)) = E(m1+m2; r1*r2)                               *)
(*   Epow(E(m1;r), m2) = E(m1*m2; r^(m2:nat))                                 *)
(*                                                                            *)
(* For Paillier, E(m;r) = g^m * r^n (mod n^2) makes the randomness compose    *)
(* by multiplication / exponentiation.                                         *)
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

(* Coercion from message to nat for exponentiation *)
Definition paillier_msg_nat (m : 'Z_n) : nat := m.

(* Concrete randomness formula for homomorphic addition *)
Lemma paillier_Emul_eq_add : forall (m1 m2 : 'Z_n) (r1 r2 : 'Z_n2),
  paillier_Emul (paillier_he_enc m1 r1) (paillier_he_enc m2 r2) 
    = paillier_he_enc (m1 + m2) (r1 * r2).
Proof.
  move=> m1 m2 r1 r2.
  rewrite /paillier_Emul.
  exact: (enc_mul_dist n_gt1 g_order_n).
Qed.

(* Ring multiplication equals scalar multiplication in Z_n *)
Lemma scalar_eq_ring_mul : forall (m1 m2 : 'Z_n),
  m1 * m2 = m1 *+ (m2 : nat).
Proof.
  move=> m1 m2.
  rewrite mulrC -[m2 in m2 * _]natr_Zp mulr_natl.
  reflexivity.
Qed.

(* Concrete randomness formula for homomorphic scalar multiplication *)
Lemma paillier_Epow_eq_mul : forall (m1 m2 : 'Z_n) (r : 'Z_n2),
  paillier_Epow (paillier_he_enc m1 r) m2 = paillier_he_enc (m1 * m2) (r ^+ (m2 : nat)).
Proof.
  move=> m1 m2 r.
  rewrite /paillier_Epow (enc_exp_dist n_gt1 g_order_n).
  by rewrite scalar_eq_ring_mul.
Qed.

HB.instance Definition Paillier_HE_isHE : isHE Paillier_HE_types := 
  @isHE.phant_Build Paillier_HE_types paillier_he_enc paillier_Emul paillier_Epow 
    paillier_msg_nat paillier_Emul_eq_add paillier_Epow_eq_mul.

End Paillier_HE.
