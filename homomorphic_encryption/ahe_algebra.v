(******************************************************************************)
(*                                                                            *)
(* Additively Homomorphic Encryption - Algebraic Properties Mixin             *)
(*                                                                            *)
(* This file defines the isPartyAHE_Algebra mixin providing algebraic         *)
(* properties for the homomorphic operations (Emul), and the final            *)
(* Party_AHE structure combining all three mixins.                            *)
(*                                                                            *)
(* == Properties ==                                                           *)
(*                                                                            *)
(*   pahe_Emul_assoc : Emul(Emul(e1,e2), e3) = Emul(e1, Emul(e2,e3))          *)
(*   pahe_Emul_comm  : Emul(e1, e2) = Emul(e2, e1)                            *)
(*   pahe_Emul_id    : Emul(e, E(p,0,r)) = e (identity element)               *)
(*                                                                            *)
(* == Structure ==                                                            *)
(*                                                                            *)
(*   Party_AHE_scheme : bundles Party_HE_types with all three mixins          *)
(*     - isPartyHE_EncDec   (encryption/decryption)                           *)
(*     - isPartyAHE_HomoOps (homomorphic operations)                          *)
(*     - isPartyAHE_Algebra (algebraic properties)                            *)
(*                                                                            *)
(* == Related Files ==                                                        *)
(*                                                                            *)
(*   ahe_types.v     - Type definitions (Party_HE_types)                      *)
(*   ahe_enc_dec.v   - Encryption/decryption mixin (isPartyHE_EncDec)         *)
(*   ahe_homo_ops.v  - Homomorphic operations mixin (isPartyAHE_HomoOps)      *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra ssrfun.
From infotheo Require Import homomorphic_encryption.ahe_types.
From infotheo Require Import homomorphic_encryption.ahe_enc_dec.
From infotheo Require Import homomorphic_encryption.ahe_homo_ops.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*                   Algebraic Properties Mixin                                *)
(* ========================================================================== *)

(* HB mixin for algebraic properties of the homomorphic operations.
   Uses pahe_ prefix since these properties are about pahe_Emul.
   
   Note: Full commutativity (Emul e1 e2 = Emul e2 e1) is NOT required because
   party-labeled ciphertexts carry metadata that doesn't commute. The underlying
   ciphertext multiplication is commutative, but the party label comes from the
   first argument. Implementations may prove same-party commutativity separately.
   
   The identity property uses a specific "unit randomness" value rather than
   requiring E(p, 0, r) to be identity for ALL r. For most schemes:
   - Benaloh: r_unit = 1, since benaloh_enc y 0 1 = y^0 * 1^r = 1
   - Paillier: r_unit = 1, since paillier_enc g 0 1 = g^0 * 1^n = 1 *)
HB.mixin Record isPartyAHE_Algebra (T : Party_AHE_HomoOps_scheme) := {
  (* Associativity of homomorphic addition *)
  pahe_Emul_assoc : forall (e1 e2 e3 : phe_enc T),
    pahe_Emul (pahe_Emul e1 e2) e3 = pahe_Emul e1 (pahe_Emul e2 e3) ;
  
  (* Unit randomness for identity element *)
  pahe_rand_unit : phe_rand T ;
    
  (* Right identity element for homomorphic addition.
     E(p, 0, rand_unit) encrypts zero with unit randomness, yielding the
     multiplicative identity (1) in the ciphertext space. *)
  pahe_Emul_id : forall (p : phe_party T) (e : phe_enc T),
    pahe_Emul e (phe_E p 0 pahe_rand_unit) = e
}.

(* ========================================================================== *)
(*                   Final Party_AHE Structure                                 *)
(* ========================================================================== *)

(* The complete Party_AHE structure bundles all three mixins:
   - isPartyHE_EncDec   : E, D, K, dec_correct
   - isPartyAHE_HomoOps : Emul, Epow, Emul_addM, Epow_mulM
   - isPartyAHE_Algebra : Emul_assoc, Emul_comm, Emul_id *)
#[short(type=Party_AHE_scheme)]
HB.structure Definition Party_AHE := { T of isPartyAHE_Algebra T }.
