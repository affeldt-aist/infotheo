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
(*   enc : party -> msg -> rand -> enc    (encryption)                        *)
(*   key : party -> key -> msg -> pkey    (key generation)                    *)
(*   dec : pkey -> enc -> option msg      (decryption)                        *)
(*                                                                            *)
(* == Properties ==                                                           *)
(*                                                                            *)
(*   dec_correct : dec (key (p,Dec,sk), enc(p,m,r)) = Some m                  *)
(*                                                                            *)
(* == Related Files ==                                                        *)
(*                                                                            *)
(*   he_types.v     - Type definitions (HETypes)                              *)
(*   ahe_enc.v  - Homomorphic operations mixin (isAHEnc)                      *)
(*   ahe_algebra.v   - Algebraic properties mixin (isAHEAlgebra)              *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
Require Import he_types.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*                   Encryption/Decryption Mixin                               *)
(* ========================================================================== *)

HB.mixin Record isEncDec (T : HETypes) := {
  (* Encryption: party -> message -> randomness -> ciphertext *)
  enc : party T -> plain T -> rand T -> party_cipher T ;
  
  (* Key generation: party -> key type -> secret -> party key *)
  key : party T -> key_type -> plain T -> pkey T ;
  
  (* Decryption: party key -> ciphertext -> optional message *)
  dec : pkey T -> party_cipher T -> option (plain T) ;
  
  (* Decryption correctness: decrypting an encryption yields the message.
     Note: For concrete instances (Benaloh, Paillier), this may require
     implementing actual decryption or using an axiom placeholder. *)
  dec_correct : forall (p : party T) (m : plain T) (r : rand T) (sk : plain T),
    dec (key p Dec sk) (enc p m r) = Some m
}.

#[short(type=EncDec_scheme)]
HB.structure Definition EncDec := { T of isEncDec T }.
