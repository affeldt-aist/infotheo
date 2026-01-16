(******************************************************************************)
(*                                                                            *)
(* Homomorphic Encryption HB Structure                                        *)
(*                                                                            *)
(* This file defines HE_types and isHE, the Hierarchy Builder structure for   *)
(* additively homomorphic encryption schemes.                                 *)
(*                                                                            *)
(* == Architecture ==                                                         *)
(*                                                                            *)
(*   HE_types bundles three types:                                            *)
(*     - he_msg : finComNzRingType    (message space)                         *)
(*     - he_ct : finType              (ciphertext space)                      *)
(*     - he_rand : Type               (randomness type)                       *)
(*                                                                            *)
(*   isHE mixin provides operations:                                          *)
(*     - he_enc : msg -> rand -> ct       (encryption)                        *)
(*     - he_Emul : ct -> ct -> ct         (homomorphic addition)              *)
(*     - he_Epow : ct -> msg -> ct        (homomorphic scalar multiplication) *)
(*                                                                            *)
(*   HE structure bundles HE_types with isHE mixin.                           *)
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
(*                     Homomorphic Encryption HB Structure                     *)
(* ========================================================================== *)

(* Record bundling the three HE types *)
Record HE_types := MkHE {
  he_msg : finComNzRingType ;
  he_ct : finType ;
  he_rand : Type
}.

(* HB mixin for homomorphic encryption operations *)
HB.mixin Record isHE (T : HE_types) := {
  he_enc : he_msg T -> he_rand T -> he_ct T ;
  he_Emul : he_ct T -> he_ct T -> he_ct T ;
  he_Epow : he_ct T -> he_msg T -> he_ct T ;
  he_Emul_eq_add : forall (m1 m2 : he_msg T) (r1 r2 : he_rand T),
    exists r : he_rand T, 
      he_Emul (he_enc m1 r1) (he_enc m2 r2) = he_enc (m1 + m2) r ;
  he_Epow_eq_mul : forall (m1 m2 : he_msg T) (r : he_rand T),
    exists r' : he_rand T, 
      he_Epow (he_enc m1 r) m2 = he_enc (m1 * m2) r'
}.

#[short(type=HE_scheme)]
HB.structure Definition HE := { T of isHE T }.
