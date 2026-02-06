(******************************************************************************)
(*                                                                            *)
(* Additively Homomorphic Encryption - Type Definitions                       *)
(*                                                                            *)
(* This file defines the base types for party-labeled homomorphic encryption: *)
(*   - key_type type (Dec | Enc) with HB instances                                 *)
(*   - HETypes record bundling carrier types                                  *)
(*                                                                            *)
(* == Types ==                                                                *)
(*                                                                            *)
(*   HETypes bundles six types:                                               *)
(*     - party : finType            (party/participant space)                 *)
(*     - plain : finComNzRingType   (message/plaintext space)                 *)
(*     - rand : ringType            (randomness space, ring for r1*r2)        *)
(*     - cipher : ringType          (raw ciphertext without party label)      *)
(*     - party_cipher : finType     (party-labeled ciphertext space)          *)
(*     - pkey : Type                (party-labeled key space)                 *)
(*                                                                            *)
(* == Related Files ==                                                        *)
(*                                                                            *)
(*   enc_dec.v       - Encryption/decryption mixin (isEncDec)                 *)
(*   ahe_enc.v       - Homomorphic operations mixin (isAHEnc)                 *)
(*   ahe_algebra.v   - Algebraic properties mixin (isAHEAlgebra)              *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Record HETypes := MkHE {
  plain : finComNzRingType ;  (* message/plaintext space *)
  rand :  ringType ;          (* randomness space,
                                 ringType enables r1*r2 and r^+k *)
  cipher : ringType ;         (* raw ciphertext values without party label *)
  key : finType ;            (* key space *)
}.
