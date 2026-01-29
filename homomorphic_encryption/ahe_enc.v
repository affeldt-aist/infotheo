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
(*   Emul     : enc -> enc -> enc     (homomorphic addition via mult)         *)
(*   Epow     : enc -> msg -> enc     (homomorphic scalar mult via pow)       *)
(*   rand_pow : rand -> msg -> rand   (randomness exponentiation by msg)      *)
(*                                                                            *)
(* == Properties (using mathcomp's {morph ...} notation) ==                   *)
(*                                                                            *)
(*   Emul_addM : {morph E[p] : x y / x +mr y >-> Emul x y}      (morphism_2)  *)
(*   Epow_mulM : {morph E[p] : mr / (...) >-> Epow mr m}        (morphism_1)  *)
(*                                                                            *)
(* == Helper Definitions ==                                                   *)
(*                                                                            *)
(*   enc_curry p    : (msg * rand) -> enc                                     *)
(*   msg_rand_add   : (msg * rand) -> (msg * rand) -> (msg * rand)            *)
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
Require Import he_types.
Require Import enc_dec.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*                   Helper Definitions for morphism notation                 *)
(* ========================================================================== *)

(* Curried encryption: for fixed party p, maps (msg, rand) pairs to enc.
   This allows us to use mathcomp's morphism notation.
   Defined with explicit T argument for use in HB mixins. *)
Definition enc_curry (T : EncDec_scheme) (p : party T) 
    : (plain T * rand T) -> party_cipher T :=
  fun mr => enc p mr.1 mr.2.

(* Operation on (msg, rand) pairs: add messages, multiply randomness.
   This is the domain operation for the additive homomorphism (morphism_2).
   Defined with explicit T argument for use in HB mixins. *)
Definition msg_rand_add (T : EncDec_scheme)
    (mr1 mr2 : plain T * rand T) : plain T * rand T :=
  (mr1.1 + mr2.1, mr1.2 * mr2.2).

(* Make T explicit in these definitions *)
Arguments enc_curry : clear implicits.
Arguments msg_rand_add : clear implicits.

(* ========================================================================== *)
(*                   Homomorphic Operations Mixin                             *)
(* ========================================================================== *)

(* Notations for morphism statements. Uses _ for type inference from context.
   E[p]   : curried encryption for party p
   x +mr y : add messages, multiply randomness (for morphism_2) *)
Notation "E[ p ]" := (enc_curry _ p) (at level 10, p at level 9).
Notation "x +mr y" := (msg_rand_add _ x y) (at level 50, left associativity).

(* HB mixin for additive homomorphic operations.
   Uses pahe_ prefix since Emul and Epow are AHE-specific operations. *)
HB.mixin Record isAHEnc (T : HETypes) of isEncDec T := {
  (* Homomorphic addition: ciphertext multiplication = plaintext addition *)
  Emul : party_cipher T -> party_cipher T -> party_cipher T ;
  
  (* Homomorphic scalar multiplication: ciphertext power =
     plaintext scalar mult *)
  Epow : party_cipher T -> plain T -> party_cipher T ;
  
  (* Randomness exponentiation by message: r ^^ m
     Abstracts the operation of raising randomness to a message power.
     For concrete schemes, this is typically r ^+ (m : nat). *)
  rand_pow : rand T -> plain T -> rand T ;
  
  (* Additive homomorphism using mathcomp's morphism_2:
     For each party p, enc_curry p is a morphism from 
     (msg*rand, msg_rand_add) to (enc, Emul).
     
     Expands to: forall mr1 mr2, 
       enc_curry T p (msg_rand_add T mr1 mr2) = 
       Emul (enc_curry T p mr1) (enc_curry T p mr2) *)
  Emul_addM : forall (p : party T),
    {morph E[p] : x y / x +mr y >-> Emul x y} ;
    
  (* Scalar multiplication homomorphism using mathcomp's morphism_1:
     For each party p and scalar m, enc_curry p is a morphism from
     (mr => (mr.1 * m, rand_pow mr.2 m)) to (c => Epow c m).
     
     Expands to: forall mr,
       enc p (mr.1 * m) (rand_pow mr.2 m) = Epow (enc p mr.1 mr.2) m *)
  Epow_mulM : forall (p : party T) (m : plain T),
    {morph E[p] : mr / (mr.1 * m, rand_pow mr.2 m) >-> Epow mr m}
}.

#[short(type=AHEnc_scheme)]
HB.structure Definition AHEnc := { T of isAHEnc T & }.

(* ========================================================================== *)
(*                   Convenience Lemmas                                       *)
(* ========================================================================== *)

Section AHE_lemmas.

Variable T : AHEnc_scheme.

(* Uncurried form of the additive homomorphism, for ease of use.
   Uses _E suffix following mathcomp convention for equation form. *)
Lemma Emul_addE (p : party T) (m1 m2 : plain T) (r1 r2 : rand T) :
  Emul (enc p m1 r1) (enc p m2 r2) = enc p (m1 + m2) (r1 * r2).
Proof.
  have H := Emul_addM p (m1, r1) (m2, r2).
  rewrite /enc_curry /msg_rand_add /= in H.
  exact (esym H).
Qed.

End AHE_lemmas.
