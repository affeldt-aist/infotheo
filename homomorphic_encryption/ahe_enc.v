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
(*   Emul_addM : {morph E[p] : x y / x (+) y >-> Emul x y}      (morphism_2)  *)
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
From mathcomp Require Import all_boot all_order all_algebra ssrfun.
Require Import he_types.
Require Import enc_dec.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* Note: Emul Epow require all encrypted values enc by the same enc key *)
Definition enc_curry (T : EncDecType) (k : key T) (r : rand T) 
    : plain T -> cipher T :=
  fun m => enc k m r.

(* Make T explicit in these definitions *)
Arguments enc_curry : clear implicits.

(* ========================================================================== *)
(*                   Homomorphic Operations Mixin                             *)
(* ========================================================================== *)

Notation "E[ k ; r ]" := (enc_curry _ k r) (at level 10).

HB.mixin Record isAHEnc (T : HETypes) of isEncDec T := {
  Emul : cipher T -> cipher T -> cipher T ;
  Epow : cipher T -> plain T -> cipher T ;
    
  (* Since rand is a Type, need operations *)
  rand_pow : rand T -> plain T -> rand T ;
  rand_mul : rand T -> rand T -> rand T ;

  (* E(m1 + m2) = E(m1) * E(m2) with extra constraint on randomness *)
  Emul_addM :
    forall (k : key T) (r1 r2 : rand T),
    {morph E[k ; (rand_mul r1 r2) ] : m1 m2 / m1 + m2 >-> Emul m1 m2} ;

  (* E(m * j) = E(m) ^ j with extra constraint on randomness *)
  Epow_scalarM :
    forall (k : key T) (j : plain T) (r : rand T),
    {morph E[k ; (rand_pow r j) ] : m / m * j >-> Epow m j} ;
}.

#[short(type=AHEncType)]
HB.structure Definition AHEnc := { T of isAHEnc T & }.

(* NOTE: these are properties on the mixin, so by the limitation of HB
   we cannot write them in the mixin. We need to use them in the instance.
   The reason why rand_pow needs to be on the mixin while msg_rand_add
   doesn't need, is because the ring type guarantees that msg_rand_add works.*)
Local Notation "x (.) y" := (Emul x y) (at level 40, left associativity).
Local Notation "x (^) y" := (Epow x y) (at level 40, left associativity).
Local Notation "x {^} y" := (rand_pow x y) (at level 40, left associativity).
Local Notation "x {*} y" := (rand_mul x y) (at level 40, left associativity).

