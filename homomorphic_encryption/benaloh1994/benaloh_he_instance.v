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
(* HE structure requires concrete randomness formulas:                         *)
(*   Emul(E(m1;u1), E(m2;u2)) = E(m1+m2; u1*u2)                                *)
(*   Epow(E(m1;u), m2) = E(m1*m2; u^(m2:nat))                                  *)
(*                                                                            *)
(* For Benaloh, E(m;u) = y^m · u^r (mod n) makes the randomness compose        *)
(* by multiplication / exponentiation.                                         *)
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

(* Coercion from message to nat for exponentiation *)
Definition benaloh_msg_nat (m : 'Z_r) : nat := m.

(* Concrete randomness formula for homomorphic addition *)
Lemma benaloh_Emul_eq_add : forall (m1 m2 : 'Z_r) (u1 u2 : 'Z_n),
  benaloh_Emul (benaloh_he_enc m1 u1) (benaloh_he_enc m2 u2) 
    = benaloh_he_enc (m1 + m2) (u1 * u2).
Proof.
  move=> m1 m2 u1 u2.
  rewrite /benaloh_Emul.
  exact: (enc_mul_dist r_gt1 y_order_r).
Qed.

(* Ring multiplication equals scalar multiplication in Z_r *)
Lemma scalar_eq_ring_mul : forall (m1 m2 : 'Z_r),
  m1 * m2 = m1 *+ (m2 : nat).
Proof.
  move=> m1 m2.
  rewrite mulrC -[m2 in m2 * _]natr_Zp mulr_natl.
  reflexivity.
Qed.

(* Concrete randomness formula for homomorphic scalar multiplication *)
Lemma benaloh_Epow_eq_mul : forall (m1 m2 : 'Z_r) (u : 'Z_n),
  benaloh_Epow (benaloh_he_enc m1 u) m2 = benaloh_he_enc (m1 * m2) (u ^+ (m2 : nat)).
Proof.
  move=> m1 m2 u.
  rewrite /benaloh_Epow (enc_exp_dist r_gt1 y_order_r).
  by rewrite scalar_eq_ring_mul.
Qed.

HB.instance Definition Benaloh_HE_isHE : isHE Benaloh_HE_types := 
  @isHE.phant_Build Benaloh_HE_types benaloh_he_enc benaloh_Emul benaloh_Epow 
    benaloh_msg_nat benaloh_Emul_eq_add benaloh_Epow_eq_mul.

End Benaloh_HE.
