(******************************************************************************)
(*                                                                            *)
(* Additively Homomorphic Encryption - Homomorphic Operations Mixin           *)
(*                                                                            *)
(* This file defines the isPartyAHE_HomoOps mixin providing the additive      *)
(* homomorphic operations for party-labeled encryption schemes.               *)
(*                                                                            *)
(* These operations use the `pahe_` prefix (party AHE) since they are         *)
(* specific to additive homomorphism:                                         *)
(*   - Emul: ciphertext multiplication corresponds to plaintext addition      *)
(*   - Epow: ciphertext exponentiation corresponds to plaintext scalar mult   *)
(*                                                                            *)
(* == Operations ==                                                           *)
(*                                                                            *)
(*   pahe_Emul : enc -> enc -> enc     (homomorphic addition via mult)        *)
(*   pahe_Epow : enc -> msg -> enc     (homomorphic scalar mult via power)    *)
(*                                                                            *)
(* == Properties (using mathcomp's morphism_2) ==                             *)
(*                                                                            *)
(*   pahe_Emul_addM : morphism_2 (phe_E_curry p) msg_rand_add pahe_Emul       *)
(*   pahe_Epow_mulM : Epow(E(p,m1,r), m2) = E(p, m1*m2, r^(m2:nat))           *)
(*                                                                            *)
(* == Helper Definitions ==                                                   *)
(*                                                                            *)
(*   phe_E_curry p : (msg * rand) -> enc                                      *)
(*   msg_rand_add : (msg * rand) -> (msg * rand) -> (msg * rand)              *)
(*                                                                            *)
(* == Related Files ==                                                        *)
(*                                                                            *)
(*   ahe_types.v     - Type definitions (Party_HE_types)                      *)
(*   ahe_enc_dec.v   - Encryption/decryption mixin (isPartyHE_EncDec)         *)
(*   ahe_algebra.v   - Algebraic properties mixin (isPartyAHE_Algebra)        *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra ssrfun.
From infotheo Require Import homomorphic_encryption.ahe_types.
From infotheo Require Import homomorphic_encryption.ahe_enc_dec.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*                   Helper Definitions for morphism_2                         *)
(* ========================================================================== *)

(* Curried encryption: for fixed party p, maps (msg, rand) pairs to enc.
   This allows us to use mathcomp's morphism_2.
   Defined with explicit T argument for use in HB mixins. *)
Definition phe_E_curry (T : Party_HE_EncDec_scheme) (p : phe_party T) 
    : (phe_msg T * phe_rand T) -> phe_enc T :=
  fun mr => phe_E p mr.1 mr.2.

(* Operation on (msg, rand) pairs: add messages, multiply randomness.
   This is the domain operation for the additive homomorphism.
   Defined with explicit T argument for use in HB mixins. *)
Definition msg_rand_add (T : Party_HE_EncDec_scheme)
    (mr1 mr2 : phe_msg T * phe_rand T) : phe_msg T * phe_rand T :=
  (mr1.1 + mr2.1, mr1.2 * mr2.2).

(* Make T explicit in these definitions *)
Arguments phe_E_curry : clear implicits.
Arguments msg_rand_add : clear implicits.

(* ========================================================================== *)
(*                   Homomorphic Operations Mixin                              *)
(* ========================================================================== *)

(* HB mixin for additive homomorphic operations.
   Uses pahe_ prefix since Emul and Epow are AHE-specific operations. *)
HB.mixin Record isPartyAHE_HomoOps (T : Party_HE_types) of isPartyHE_EncDec T := {
  (* Homomorphic addition: ciphertext multiplication = plaintext addition *)
  pahe_Emul : phe_enc T -> phe_enc T -> phe_enc T ;
  
  (* Homomorphic scalar multiplication: ciphertext power = plaintext scalar mult *)
  pahe_Epow : phe_enc T -> phe_msg T -> phe_enc T ;
  
  (* Additive homomorphism using mathcomp's morphism_2:
     For each party p, phe_E_curry p is a morphism from 
     (msg*rand, msg_rand_add) to (enc, pahe_Emul).
     
     Expands to: forall mr1 mr2, 
       phe_E_curry T p (msg_rand_add T mr1 mr2) = 
       pahe_Emul (phe_E_curry T p mr1) (phe_E_curry T p mr2) *)
  pahe_Emul_addM : forall (p : phe_party T),
    morphism_2 (phe_E_curry T p) (msg_rand_add T) pahe_Emul ;
    
  (* Scalar multiplication homomorphism:
     Epow(E(p,m1,r), m2) = E(p, m1*m2, r^(m2:nat)) *)
  pahe_Epow_mulM : forall (p : phe_party T) (m1 m2 : phe_msg T) (r : phe_rand T),
    pahe_Epow (phe_E p m1 r) m2 = phe_E p (m1 * m2) (r ^+ phe_msg_nat m2)
}.

#[short(type=Party_AHE_HomoOps_scheme)]
HB.structure Definition Party_AHE_HomoOps := { T of isPartyAHE_HomoOps T & }.

(* ========================================================================== *)
(*                   Convenience Lemmas                                        *)
(* ========================================================================== *)

Section AHE_lemmas.

Variable T : Party_AHE_HomoOps_scheme.

(* Uncurried form of the additive homomorphism, for ease of use.
   Uses _E suffix following mathcomp convention for equation form. *)
Lemma pahe_Emul_addE (p : phe_party T) (m1 m2 : phe_msg T) (r1 r2 : phe_rand T) :
  pahe_Emul (phe_E p m1 r1) (phe_E p m2 r2) = phe_E p (m1 + m2) (r1 * r2).
Proof.
  have H := pahe_Emul_addM p (m1, r1) (m2, r2).
  rewrite /phe_E_curry /msg_rand_add /= in H.
  exact (esym H).
Qed.

End AHE_lemmas.
