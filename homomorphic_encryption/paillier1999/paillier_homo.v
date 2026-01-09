(******************************************************************************)
(*                                                                            *)
(* Paillier Homomorphic Encryption - Homomorphic Properties                   *)
(*                                                                            *)
(* This file proves the two core homomorphic properties of the Paillier       *)
(* cryptosystem:                                                              *)
(*   1. Additive: E[m1] * E[m2] = E[m1 + m2]                                  *)
(*   2. Scalar:   E[m1]^k = E[m1 * k]                                         *)
(*                                                                            *)
(* These properties enable computation on encrypted data without decryption.  *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg zmodp.
Require Import paillier_enc.

Import GRing.Theory.
Import Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*                       Homomorphic Property Theorems                         *)
(* ========================================================================== *)

Section paillier_homomorphic.

Variable n : nat.
Hypothesis n_gt1 : (1 < n)%N.

Let n2 := (n * n)%N.

Variable g : 'Z_n2.
Hypothesis g_order_n : g ^+ n = 1.

(** Additive Homomorphism:
    Multiplying two ciphertexts yields a ciphertext of the sum of plaintexts.
    This enables addition on encrypted data. *)
Theorem paillier_additive_homo : forall (m1 m2 : 'Z_n) (r1 r2 : 'Z_n2),
  paillier_enc g m1 r1 * paillier_enc g m2 r2 = 
  paillier_enc g (m1 + m2) (r1 * r2).
Proof.
  move=> m1 m2 r1 r2.
  exact: (enc_mul_dist n_gt1 g_order_n).
Qed.

(** Scalar Multiplication Homomorphism:
    Exponentiating a ciphertext yields a ciphertext of the scaled plaintext.
    This enables scalar multiplication on encrypted data. *)
Theorem paillier_scalar_homo : forall (m1 : 'Z_n) (k : nat) (r : 'Z_n2),
  (paillier_enc g m1 r) ^+ k = 
  paillier_enc g (m1 *+ k) (r ^+ k).
Proof.
  move=> m1 k r.
  exact: (enc_exp_dist n_gt1 g_order_n).
Qed.

(** Corollary: Repeated addition equals scalar multiplication. *)
Corollary paillier_repeated_add : forall (m : 'Z_n) (k : nat) (r : 'Z_n2),
  iter k (fun c => c * paillier_enc g m r) (paillier_enc g (0 : 'Z_n) (1 : 'Z_n2)) =
  paillier_enc g (m *+ k) (r ^+ k).
Proof.
  move=> m k r.
  elim: k => [|k IHk].
  - by rewrite /= mulr0n expr0.
  - rewrite iterS IHk mulrSr exprS (enc_mul_dist n_gt1 g_order_n).
    by rewrite mulrC.
Qed.

End paillier_homomorphic.
