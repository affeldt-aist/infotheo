(******************************************************************************)
(*                                                                            *)
(* Benaloh Homomorphic Encryption - Homomorphic Properties                    *)
(*                                                                            *)
(* This file proves the two core homomorphic properties of the Benaloh        *)
(* cryptosystem:                                                              *)
(*   1. Additive: E[m1] * E[m2] = E[m1 + m2]                                  *)
(*   2. Scalar:   E[m1]^m2 = E[m1 * m2]                                       *)
(*                                                                            *)
(* These properties enable computation on encrypted data without decryption.  *)
(*                                                                            *)
(* == Informal "why it works" (math) ==                                       *)
(*                                                                            *)
(* Benaloh encryption has the form                                             *)
(*                                                                            *)
(*   E(m;u) = y^m · u^r   (mod n)                                              *)
(*                                                                            *)
(* with y^r = 1. Multiplying ciphertexts adds exponents and multiplies masks: *)
(*                                                                            *)
(*   E(m1;u1)·E(m2;u2) = y^{m1+m2}·(u1u2)^r = E(m1+m2; u1u2).                  *)
(*                                                                            *)
(* Exponentiating a ciphertext scales the plaintext (repeated addition):       *)
(*                                                                            *)
(*   E(m;u)^k = y^{m·k}·(u^k)^r = E(m *+ k; u^k).                              *)
(*                                                                            *)
(* This file simply packages those identities as theorems (by reusing the     *)
(* core lemmas from benaloh_enc.v).                                           *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg zmodp.
From infotheo Require Import homomorphic_encryption.benaloh1994.benaloh_enc.

Import GRing.Theory.
Import Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*                       Homomorphic Property Theorems                         *)
(* ========================================================================== *)

Section benaloh_homomorphic.

Variable n : nat.
Variable r : nat.
(* These hypotheses ensure 'Z_n and 'Z_r are valid types *)
Hypothesis n_gt1 : (1 < n)%N.
Hypothesis r_gt1 : (1 < r)%N.
Variable y : 'Z_n.
(* Key cryptographic constraint: y has order dividing r *)
Hypothesis y_order_r : y ^+ r = 1.

(*
=== MATHEMATICAL PROOF STRATEGY ===

Statement: E[m1] * E[m2] = E[(m1 + m2) mod r]

Why it's true:
  E[m1] * E[m2] = [y^m1 * u1^r] * [y^m2 * u2^r]
               = y^[m1+m2] * [u1*u2]^r         [by commutativity and exp laws]
               = E[m1+m2, u1*u2]

Proof approach: Direct application of enc_mul_dist axiom.

===================================
*)

(** Additive Homomorphism:
    Multiplying two ciphertexts yields a ciphertext of the sum of plaintexts.
    This enables addition on encrypted data. *)
Theorem benaloh_additive_homo : forall (m1 m2 : 'Z_r) (u1 u2 : 'Z_n),
  benaloh_enc y m1 u1 * benaloh_enc y m2 u2 = 
  benaloh_enc y (m1 + m2) (u1 * u2).
Proof.
  (* Goal: benaloh_enc m1 u1 * benaloh_enc m2 u2 = benaloh_enc [m1 + m2] [u1 * u2] *)
  move=> m1 m2 u1 u2.
  (* Apply the multiplication distribution lemma *)
  exact: (enc_mul_dist r_gt1 y_order_r).
Qed.

(*
=== MATHEMATICAL PROOF STRATEGY ===

Statement: E[m1]^m2 = E[(m1 * m2) mod r]

Why it's true:
  E[m1]^m2 = [y^m1 * u^r]^m2
          = y^[m1*m2] * u^[r*m2]              [by exponent distribution]
          = y^[m1*m2] * [u^m2]^r              [by exponent associativity]
          = E[m1*m2, u^m2]

Proof approach: Direct application of enc_exp_dist axiom.

===================================
*)

(** Scalar Multiplication Homomorphism:
    Exponentiating a ciphertext yields a ciphertext of the product of plaintexts.
    This enables scalar multiplication on encrypted data. *)
Theorem benaloh_scalar_homo : forall (m1 : 'Z_r) (m2 : nat) (u : 'Z_n),
  (benaloh_enc y m1 u) ^+ m2 = 
  benaloh_enc y (m1 *+ m2) (u ^+ m2).
Proof.
  (* Goal: [benaloh_enc m1 u] ^+ m2 = benaloh_enc [m1 *+ m2] [u ^+ m2] *)
  move=> m1 m2 u.
  (* Apply the exponentiation distribution lemma *)
  exact: (enc_exp_dist r_gt1 y_order_r).
Qed.

(** Corollary: Repeated addition equals scalar multiplication.
    Adding a message to itself k times is the same as scalar multiplication by k. *)
Corollary benaloh_repeated_add : forall (m : 'Z_r) (k : nat) (u : 'Z_n),
  iter k (fun c => c * benaloh_enc y m u) (benaloh_enc y (0 : 'Z_r) (1 : 'Z_n)) =
  benaloh_enc y (m *+ k) (u ^+ k).
Proof.
  (* This follows from additive_homo by induction on k *)
  move=> m k u.
  elim: k => [|k IHk].
  - (* Base case: k = 0 *)
    (* Goal: iter 0 ... = benaloh_enc 0 1 = benaloh_enc [m *+ 0] [u ^+ 0] *)
    by rewrite /= mulr0n expr0.
  - (* Inductive case: k = k.+1 *)
    (* Goal: iter k.+1 ... = benaloh_enc [m *+ k.+1] [u ^+ k.+1] *)
    rewrite iterS IHk mulrSr exprS (enc_mul_dist r_gt1 y_order_r).
    (* Apply commutativity for the randomness *)
    by rewrite mulrC.
Qed.

End benaloh_homomorphic.
