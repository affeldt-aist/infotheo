(******************************************************************************)
(*                                                                            *)
(* Paillier as Homomorphic Encryption Instance                                *)
(*                                                                            *)
(* This file connects the Paillier cryptosystem to the abstract homomorphic   *)
(* encryption interface. It shows that Paillier's concrete operations satisfy *)
(* the same algebraic properties as the idealized Emul/Epow operations.       *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg zmodp.
Require Import paillier_enc.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Section paillier_he_connection.

Variable n : nat.
Hypothesis n_gt1 : (1 < n)%N.

Let n2 := (n * n)%N.

Variable g : 'Z_n2.
Hypothesis g_order_n : g ^+ n = 1.

(* Paillier satisfies additive homomorphism: 
   multiplying ciphertexts adds plaintexts.
   
   Corresponds to abstract: Emul (E i m1) (E i m2) = E i (m1 + m2)
   
   The existential captures that resulting randomness depends on inputs. *)
Lemma paillier_Emul_correct : forall (m1 m2 : 'Z_n) (r1 r2 : 'Z_n2),
  exists r : 'Z_n2,
    paillier_enc g m1 r1 * paillier_enc g m2 r2 = paillier_enc g (m1 + m2) r.
Proof.
  move=> m1 m2 r1 r2.
  exists (r1 * r2).
  exact: (enc_mul_dist n_gt1 g_order_n).
Qed.

(* Paillier satisfies scalar homomorphism:
   exponentiating ciphertext multiplies plaintext by scalar.
   
   Paillier uses nat exponent: E(m1)^k = E(m1 *+ k) where k : nat
   Abstract Epow uses ring exponent: Epow (E i m1) m2 = E i (m1 * m2) where m2 : msg
   
   These are compatible for 'Z_n: see scalar_eq_ring_mul below. *)
Lemma paillier_Epow_correct : forall (m1 : 'Z_n) (k : nat) (r : 'Z_n2),
  exists r' : 'Z_n2,
    (paillier_enc g m1 r) ^+ k = paillier_enc g (m1 *+ k) r'.
Proof.
  move=> m1 k r.
  exists (r ^+ k).
  exact: (enc_exp_dist n_gt1 g_order_n).
Qed.

(* Connection between scalar multiplication and ring multiplication for 'Z_n.
   For m2 : 'Z_n, we have: m1 * m2 = m1 *+ (m2 : nat) in 'Z_n *)
Lemma scalar_eq_ring_mul : forall (m1 m2 : 'Z_n),
  m1 * m2 = m1 *+ (m2 : nat).
Proof.
  move=> m1 m2.
  rewrite mulrC -[m2 in m2 * _]natr_Zp mulr_natl.
  reflexivity.
Qed.

(* Paillier with ring exponent (matching abstract Epow signature) *)
Lemma paillier_Epow_ring : forall (m1 m2 : 'Z_n) (r : 'Z_n2),
  exists r' : 'Z_n2,
    (paillier_enc g m1 r) ^+ (m2 : nat) = paillier_enc g (m1 * m2) r'.
Proof.
  move=> m1 m2 r.
  exists (r ^+ m2).
  rewrite (enc_exp_dist n_gt1 g_order_n).
  by rewrite scalar_eq_ring_mul.
Qed.

(* Concrete randomness computation for Emul *)
Lemma paillier_Emul_randomness : forall (m1 m2 : 'Z_n) (r1 r2 : 'Z_n2),
  paillier_enc g m1 r1 * paillier_enc g m2 r2 = paillier_enc g (m1 + m2) (r1 * r2).
Proof. exact: (enc_mul_dist n_gt1 g_order_n). Qed.

(* Concrete randomness computation for Epow *)
Lemma paillier_Epow_randomness : forall (m1 : 'Z_n) (k : nat) (r : 'Z_n2),
  (paillier_enc g m1 r) ^+ k = paillier_enc g (m1 *+ k) (r ^+ k).
Proof. exact: (enc_exp_dist n_gt1 g_order_n). Qed.

End paillier_he_connection.
