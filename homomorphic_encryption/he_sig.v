(******************************************************************************)
(*                                                                            *)
(* Homomorphic Encryption Module Signature                                    *)
(*                                                                            *)
(* This file defines HE_SIG, the module type for additively homomorphic       *)
(* encryption schemes.                                                        *)
(*                                                                            *)
(* == Architecture ==                                                         *)
(*                                                                            *)
(*   HE_SIG provides:                                                         *)
(*     - enc : msg -> rand -> ct       (encryption)                           *)
(*     - Emul : ct -> ct -> ct         (homomorphic addition)                 *)
(*     - Epow : ct -> msg -> ct        (homomorphic scalar multiplication)    *)
(*                                                                            *)
(*   Party_HE(HE_SIG) adds party labels:                                      *)
(*     - penc = (party * ct)           (party-labeled ciphertext)             *)
(*     - E : party -> msg -> penc      (party-labeled encryption)             *)
(*     - D : pkey -> penc -> option msg (decryption)                          *)
(*                                                                            *)
(* == Implementations ==                                                      *)
(*                                                                            *)
(*   - Ideal_HE (homomorphic_encryption.v) - ct = msg, for protocol proofs    *)
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
  (* Message space: finite commutative non-zero ring *)
  Parameter msg : finComNzRingType.
  
  (* Ciphertext space: finite type for probability distributions *)
  Parameter ct : finType.
  
  (* Randomness type for probabilistic encryption *)
  Parameter rand : Type.
  
  (* Encryption function *)
  Parameter enc : msg -> rand -> ct.
  
  (* Homomorphic addition on ciphertexts: Emul(E(m1), E(m2)) = E(m1 + m2) *)
  Parameter Emul : ct -> ct -> ct.
  
  (* Homomorphic scalar multiplication: Epow(E(m1), m2) = E(m1 * m2) *)
  Parameter Epow : ct -> msg -> ct.
  
  (* Homomorphic properties *)
  Axiom Emul_hom : forall (m1 m2 : msg) (r1 r2 : rand),
    exists r : rand, Emul (enc m1 r1) (enc m2 r2) = enc (m1 + m2) r.
  
  Axiom Epow_hom : forall (m1 m2 : msg) (r : rand),
    exists r' : rand, Epow (enc m1 r) m2 = enc (m1 * m2) r'.
  
End HE_SIG.
