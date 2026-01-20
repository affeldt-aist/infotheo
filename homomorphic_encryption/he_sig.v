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
(*     - he_rand : ringType           (randomness space, ring for r1*r2)      *)
(*                                                                            *)
(*   isHE mixin provides operations and concrete randomness properties:       *)
(*     - he_enc : msg -> rand -> ct       (encryption)                        *)
(*     - he_Emul : ct -> ct -> ct         (homomorphic addition)              *)
(*     - he_Epow : ct -> msg -> ct        (homomorphic scalar multiplication) *)
(*     - he_Emul_eq_add : Emul(E(m1,r1), E(m2,r2)) = E(m1+m2, r1*r2)          *)
(*     - he_Epow_eq_mul : Epow(E(m1,r), m2) = E(m1*m2, r^(m2:nat))            *)
(*                                                                            *)
(*   HE structure bundles HE_types with isHE mixin.                           *)
(*                                                                            *)
(* == Implementations ==                                                      *)
(*                                                                            *)
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
  he_rand : ringType  (* ringType enables r1*r2 and r^+k operations *)
}.

(* HB mixin for homomorphic encryption operations with concrete randomness *)
HB.mixin Record isHE (T : HE_types) := {
  he_enc : he_msg T -> he_rand T -> he_ct T ;
  he_Emul : he_ct T -> he_ct T -> he_ct T ;
  he_Epow : he_ct T -> he_msg T -> he_ct T ;
  (* Conversion to nat for use in r ^+ he_msg_nat m2 *)
  he_msg_nat : he_msg T -> nat ;
  he_Emul_eq_add : forall (m1 m2 : he_msg T) (r1 r2 : he_rand T),
    he_Emul (he_enc m1 r1) (he_enc m2 r2) = he_enc (m1 + m2) (r1 * r2) ;
  he_Epow_eq_mul : forall (m1 m2 : he_msg T) (r : he_rand T),
    he_Epow (he_enc m1 r) m2 = he_enc (m1 * m2) (r ^+ he_msg_nat m2)
}.

#[short(type=HE_scheme)]
HB.structure Definition HE := { T of isHE T }.
