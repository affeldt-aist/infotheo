(******************************************************************************)
(*                                                                            *)
(* Homomorphic Encryption Module Signature                                    *)
(*                                                                            *)
(* This file defines HE_SIG, the module type for additively homomorphic       *)
(* encryption schemes used in protocol proofs.                                *)
(*                                                                            *)
(* Requirements:                                                              *)
(*   - msg, ct must be finComNzRingType for probability distributions         *)
(*   - Homomorphic properties: E(m1)*E(m2) = E(m1+m2), E(m)^k = E(m*+k)       *)
(*                                                                            *)
(* Implementations:                                                           *)
(*   - Benaloh_HE (benaloh1994/benaloh_he_instance.v)                         *)
(*   - Paillier_HE (paillier1999/paillier_he_instance.v)                      *)
(*                                                                            *)
(* Note: For party-labeled encryption (used by dsdp), see Section he_ideal    *)
(* in homomorphic_encryption.v which provides E, D, Emul, Epow with party     *)
(* labels.                                                                    *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*                     Homomorphic Encryption Module Signature                 *)
(* ========================================================================== *)

Module Type HE_SIG.
  (* Message space: finite commutative non-zero ring (for probability distributions) *)
  Parameter msg : finComNzRingType.
  
  (* Ciphertext space: finite commutative non-zero ring 
     - Finite for probability distributions in protocol proofs
     - Ring for homomorphic operations (ct multiplication = msg addition) *)
  Parameter ct : finComNzRingType.
  
  (* Randomness type for probabilistic encryption *)
  Parameter rand : Type.
  
  (* Encryption function: msg -> randomness -> ciphertext *)
  Parameter enc : msg -> rand -> ct.
  
  (* Homomorphic properties:
     - Additive: E(m1) * E(m2) = E(m1 + m2)
     - Scalar:   E(m)^k = E(m *+ k)
     
     Stated with existential randomness to accommodate:
     - Deterministic encryption (rand = unit)
     - Probabilistic encryption (rand = 'Z_n etc.) *)
  
  Axiom Emul_hom : forall (m1 m2 : msg) (r1 r2 : rand),
    exists r : rand, enc m1 r1 * enc m2 r2 = enc (m1 + m2) r.
  
  Axiom Epow_hom : forall (m : msg) (k : nat) (r : rand),
    exists r' : rand, (enc m r) ^+ k = enc (m *+ k) r'.
  
End HE_SIG.
