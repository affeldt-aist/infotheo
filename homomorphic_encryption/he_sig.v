(******************************************************************************)
(*                                                                            *)
(* Homomorphic Encryption Module Signature                                    *)
(*                                                                            *)
(* This file defines HE_SIG, the module type for additively homomorphic       *)
(* encryption schemes.                                                        *)
(*                                                                            *)
(* Implementations:                                                           *)
(*   - Ideal_HE (homomorphic_encryption.v)                                    *)
(*   - Benaloh_HE (benaloh1994/benaloh_he_instance.v)                         *)
(*   - Paillier_HE (paillier1999/paillier_he_instance.v)                      *)
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
  (* Message space: a commutative ring *)
  Parameter msg : comRingType.
  
  (* Ciphertext space: a ring for homomorphic operations *)
  Parameter ct : ringType.
  
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
