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
(*   AHEScheme : bundles HETypes with all three mixins                *)
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
From mathcomp Require Import all_boot all_order all_algebra ssrfun.
Require Import he_types.
Require Import enc_dec.
Require Import ahe_enc.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(*
   - Benaloh: r_unit = 1, since benaloh_enc y 0 1 = y^0 * 1^r = 1
   - Paillier: r_unit = 1, since paillier_enc g 0 1 = g^0 * 1^n = 1
*)

HB.mixin Record isAHEMonoid (T : AHEncType) := {
  rand_id : rand T ;
  Emul_assoc : associative (@Emul T); 
  Emul_comm : commutative (@Emul T);
  Emul_id : forall k : key T, left_id (E[k; rand_id] 0) (@Emul T);
}.

(* ========================================================================== *)
(*                   Final Party_AHE Structure                                 *)
(* ========================================================================== *)

(* The complete AHEMonoid structure bundles all three mixins:
   - isEncDec      : enc, dec, key, dec_correct
   - isAHEnc       : Emul, Epow, rand_pow, Emul_addM, Epow_mulM
   - isAHEMonoid   : Emul_assoc, Emul_com, Emul_id *)
#[short(type=AHEMonoidType)]
HB.structure Definition AHEMonoid := { T of isAHEMonoid T }.

(* TODO: factory error.

HB.instance Definition _ (T : AHEMonoidType) (k : key T) := 
  GRing.isZmodule.Build (cipher T)
    (@Emul_assoc T) 
    (@Emul_comm T) 
    (@Emul_id T k).
*)
