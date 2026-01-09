(******************************************************************************)
(*                                                                            *)
(* Benaloh as Homomorphic Encryption Instance                                 *)
(*                                                                            *)
(* This file connects the Benaloh cryptosystem to the abstract homomorphic    *)
(* encryption interface. It shows that Benaloh's concrete operations satisfy  *)
(* the same algebraic properties as the idealized Emul/Epow operations.       *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg zmodp.
Require Import benaloh_enc.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Section benaloh_he_connection.

Variable n r : nat.
Hypothesis n_gt1 : (1 < n)%N.
Hypothesis r_gt1 : (1 < r)%N.
Variable y : 'Z_n.
Hypothesis y_order_r : y ^+ r = 1.

(* Benaloh satisfies additive homomorphism: 
   multiplying ciphertexts adds plaintexts.
   
   Corresponds to abstract: Emul (E i m1) (E i m2) = E i (m1 + m2)
   
   The existential captures that resulting randomness depends on inputs. *)
Lemma benaloh_Emul_correct : forall (m1 m2 : 'Z_r) (u1 u2 : 'Z_n),
  exists u : 'Z_n,
    benaloh_enc y m1 u1 * benaloh_enc y m2 u2 = benaloh_enc y (m1 + m2) u.
Proof.
  move=> m1 m2 u1 u2.
  exists (u1 * u2).
  exact: (enc_mul_dist r_gt1 y_order_r).
Qed.

(* Benaloh satisfies scalar homomorphism:
   exponentiating ciphertext multiplies plaintext by scalar.
   
   Benaloh uses nat exponent: E(m1)^k = E(m1 *+ k) where k : nat
   Abstract Epow uses ring exponent: Epow (E i m1) m2 = E i (m1 * m2) where m2 : msg
   
   These are compatible for 'Z_r: see scalar_eq_ring_mul below. *)
Lemma benaloh_Epow_correct : forall (m1 : 'Z_r) (k : nat) (u : 'Z_n),
  exists u' : 'Z_n,
    (benaloh_enc y m1 u) ^+ k = benaloh_enc y (m1 *+ k) u'.
Proof.
  move=> m1 k u.
  exists (u ^+ k).
  exact: (enc_exp_dist r_gt1 y_order_r).
Qed.

(* Connection between scalar multiplication and ring multiplication for 'Z_r.
   This shows that abstract Epow (using m1 * m2) and Benaloh (using m1 *+ k)
   compute the same result when the exponent is coerced appropriately.
   
   For m2 : 'Z_r, we have: m1 * m2 = m1 *+ (m2 : nat) in 'Z_r *)
Lemma scalar_eq_ring_mul : forall (m1 m2 : 'Z_r),
  m1 * m2 = m1 *+ (m2 : nat).
Proof.
  move=> m1 m2.
  (* Use natr_Zp: for 'Z_r, x%:R = x *)
  rewrite mulrC -[m2 in m2 * _]natr_Zp mulr_natl.
  reflexivity.
Qed.

(* Benaloh with ring exponent (matching abstract Epow signature) *)
Lemma benaloh_Epow_ring : forall (m1 m2 : 'Z_r) (u : 'Z_n),
  exists u' : 'Z_n,
    (benaloh_enc y m1 u) ^+ (m2 : nat) = benaloh_enc y (m1 * m2) u'.
Proof.
  move=> m1 m2 u.
  exists (u ^+ m2).
  rewrite (enc_exp_dist r_gt1 y_order_r).
  by rewrite scalar_eq_ring_mul.
Qed.

(* Concrete randomness computation for Emul *)
Lemma benaloh_Emul_randomness : forall (m1 m2 : 'Z_r) (u1 u2 : 'Z_n),
  benaloh_enc y m1 u1 * benaloh_enc y m2 u2 = benaloh_enc y (m1 + m2) (u1 * u2).
Proof. exact: (enc_mul_dist r_gt1 y_order_r). Qed.

(* Concrete randomness computation for Epow *)
Lemma benaloh_Epow_randomness : forall (m1 : 'Z_r) (k : nat) (u : 'Z_n),
  (benaloh_enc y m1 u) ^+ k = benaloh_enc y (m1 *+ k) (u ^+ k).
Proof. exact: (enc_exp_dist r_gt1 y_order_r). Qed.

End benaloh_he_connection.
