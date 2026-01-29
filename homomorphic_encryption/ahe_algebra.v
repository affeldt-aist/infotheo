(******************************************************************************)
(*                                                                            *)
(* Additively Homomorphic Encryption - Algebraic Properties Mixin             *)
(*                                                                            *)
(* This file defines the isAHEAlgebra mixin providing algebraic               *)
(* properties for the homomorphic operations (Emul), and the final            *)
(* AHEAlgebra structure combining all three mixins.                           *)
(*                                                                            *)
(* == Properties ==                                                           *)
(*                                                                            *)
(*   Emul_assoc      : Emul(Emul(e1,e2), e3) = Emul(e1, Emul(e2,e3))          *)
(*   Emul_id         : Emul(e, enc(p,0,rand_unit)) = e (identity element)     *)
(*   enc_cipher      : party_cipher -> cipher (extracts raw ciphertext)       *)
(*   Emul_comm_cipher: cipher(Emul(e1,e2)) = cipher(Emul(e2,e1))              *)
(*                                                                            *)
(* == Structure ==                                                            *)
(*                                                                            *)
(*   AHEAlgebra_scheme : bundles HETypes with all three mixins                *)
(*     - isEncDec     (encryption/decryption)                                 *)
(*     - isAHEnc      (homomorphic operations)                                *)
(*     - isAHEAlgebra (algebraic properties)                                  *)
(*                                                                            *)
(* == Related Files ==                                                        *)
(*                                                                            *)
(*   he_types.v   - Type definitions (HETypes)                                *)
(*   enc_dec.v    - Encryption/decryption mixin (isEncDec)                    *)
(*   ahe_enc.v    - Homomorphic operations mixin (isAHEnc)                    *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra ssrfun.
Require Import he_types.
Require Import enc_dec.
Require Import ahe_enc.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*                   Algebraic Properties Mixin                               *)
(* ========================================================================== *)

(* HB mixin for algebraic properties of the homomorphic operations.
   
   Note: Full commutativity (Emul e1 e2 = Emul e2 e1) is NOT required because
   party-labeled ciphertexts carry metadata that doesn't commute. The underlying
   ciphertext multiplication is commutative, but the party label comes from the
   first argument. However, we DO require cipher-level commutativity via
   pahe_enc_cipher projection.
   
   The identity property uses a specific "unit randomness" value rather than
   requiring E(p, 0, r) to be identity for ALL r. For most schemes:
   - Benaloh: r_unit = 1, since benaloh_enc y 0 1 = y^0 * 1^r = 1
   - Paillier: r_unit = 1, since paillier_enc g 0 1 = g^0 * 1^n = 1 *)
HB.mixin Record isAHEAlgebra (T : AHEnc_scheme) := {
  (* Associativity of homomorphic addition *)
  Emul_assoc : forall (e1 e2 e3 : party_cipher T),
    Emul (Emul e1 e2) e3 = Emul e1 (Emul e2 e3) ;
  
  (* Unit randomness for identity element *)
  rand_unit : rand T ;
    
  (* Right identity element for homomorphic addition.
     E(p, 0, rand_unit) encrypts zero with unit randomness, yielding the
     multiplicative identity (1) in the ciphertext space. *)
  Emul_id : forall (p : party T) (e : party_cipher T),
    Emul e (enc p 0 rand_unit) = e ;
  
  (* Projection to extract the raw ciphertext without party label.
     For (party, cipher) pairs, this extracts the cipher component. *)
  enc_cipher : party_cipher T -> cipher T ;
  
  (* Cipher-level commutativity: the raw ciphertext part commutes even though
     the full party-labeled ciphertext does not (due to party label ordering). *)
  Emul_comm_cipher : forall (e1 e2 : party_cipher T),
    enc_cipher (Emul e1 e2) = enc_cipher (Emul e2 e1)
}.

(* ========================================================================== *)
(*                   Final Party_AHE Structure                                 *)
(* ========================================================================== *)

(* The complete AHEAlgebra structure bundles all three mixins:
   - isEncDec      : enc, dec, key, dec_correct
   - isAHEnc       : Emul, Epow, rand_pow, Emul_addM, Epow_mulM
   - isAHEAlgebra  : Emul_assoc, Emul_id, enc_cipher, Emul_comm_cipher *)
#[short(type=AHEAlgebra_scheme)]
HB.structure Definition AHEAlgebra := { T of isAHEAlgebra T }.
