(******************************************************************************)
(*                                                                            *)
(* Additively Homomorphic Encryption - Encryption/Decryption Mixin            *)
(*                                                                            *)
(* This file defines the isPartyHE_EncDec mixin providing basic encryption    *)
(* operations for party-labeled homomorphic encryption schemes.               *)
(*                                                                            *)
(* These operations use the `phe_` prefix (party HE) since encryption,        *)
(* decryption, and key generation are generic operations not specific to      *)
(* additive homomorphism.                                                     *)
(*                                                                            *)
(* == Operations ==                                                           *)
(*                                                                            *)
(*   phe_E : party -> msg -> rand -> enc    (encryption)                      *)
(*   phe_K : party -> key -> msg -> pkey    (key generation)                  *)
(*   phe_D : pkey -> enc -> option msg      (decryption)                      *)
(*                                                                            *)
(* == Properties ==                                                           *)
(*                                                                            *)
(*   phe_dec_correct : D(K(p,Dec,sk), E(p,m,r)) = Some m                      *)
(*                                                                            *)
(* == Related Files ==                                                        *)
(*                                                                            *)
(*   ahe_types.v     - Type definitions (Party_HE_types)                      *)
(*   ahe_homo_ops.v  - Homomorphic operations mixin (isPartyAHE_HomoOps)      *)
(*   ahe_algebra.v   - Algebraic properties mixin (isPartyAHE_Algebra)        *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From infotheo Require Import homomorphic_encryption.ahe_types.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*                   Encryption/Decryption Mixin                               *)
(* ========================================================================== *)

(* HB mixin for party-labeled encryption operations.
   Uses phe_ prefix since E/D/K are generic encryption operations,
   not specific to additive homomorphism. *)
HB.mixin Record isPartyHE_EncDec (T : Party_HE_types) := {
  (* Encryption: party -> message -> randomness -> ciphertext *)
  phe_E : phe_party T -> phe_msg T -> phe_rand T -> phe_enc T ;
  
  (* Key generation: party -> key type -> secret -> party key *)
  phe_K : phe_party T -> key -> phe_msg T -> phe_pkey T ;
  
  (* Decryption: party key -> ciphertext -> optional message *)
  phe_D : phe_pkey T -> phe_enc T -> option (phe_msg T) ;
  
  (* Decryption correctness: decrypting an encryption yields the message.
     Note: For concrete instances (Benaloh, Paillier), this may require
     implementing actual decryption or using an axiom placeholder. *)
  phe_dec_correct : forall (p : phe_party T) (m : phe_msg T) (r : phe_rand T) (sk : phe_msg T),
    phe_D (phe_K p Dec sk) (phe_E p m r) = Some m
}.

#[short(type=Party_HE_EncDec_scheme)]
HB.structure Definition Party_HE_EncDec := { T of isPartyHE_EncDec T }.
