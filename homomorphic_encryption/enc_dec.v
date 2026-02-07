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
  enc : pub_key T -> plain T -> rand T -> cipher T ;
  dec : priv_key T -> cipher T -> option (plain T) ;

  (* Associate the pub key and priv key *)
  (* RSA, ElGamal, ECDSA/ECC, DSA, Kyber, Dilthium also have this property *)
  pub_of_priv : priv_key T -> pub_key T ;
  
  dec_correct : forall dk r m, 
    dec dk (enc (pub_of_priv dk) m r) = Some m ;
}.

#[short(type=EncDecType)]
HB.structure Definition EncDec := { T of isEncDec T }.
