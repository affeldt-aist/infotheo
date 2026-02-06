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
(*                   Encryption/Decryption Mixin                              *)
(*                                                                            *)
(* This mixin has been instantiated twice in benaloh1994/benaloh_ahe.v and    *)
(* paillier1999/paillier_ahe.v.                                               *)
(* ========================================================================== *)

HB.mixin Record isEncDec (T : HETypes) := {
  gen_key : rand T -> key T * key T;
  enc : key T -> plain T -> rand T -> cipher T ;
  dec : key T -> cipher T -> option (plain T) ;
  
  dec_correct : forall (rand_for_key rand_for_enc : rand T) (m : plain T),
    dec ((gen_key rand_for_key).2) (* Note: HB limitation so we cannot use let...in *)
      (enc (gen_key rand_for_key).1 m rand_for_enc) = Some m ;
}.

#[short(type=EncDecType)]
HB.structure Definition EncDec := { T of isEncDec T }.
