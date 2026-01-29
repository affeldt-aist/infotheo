(******************************************************************************)
(*                                                                            *)
(* Additively Homomorphic Encryption - Type Definitions                       *)
(*                                                                            *)
(* This file defines the base types for party-labeled homomorphic encryption: *)
(*   - key type (Dec | Enc) with HB instances                                 *)
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
From mathcomp Require Import all_ssreflect all_algebra.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*                            Key Type Definition                              *)
(* ========================================================================== *)

Section key_def.

Inductive key := Dec | Enc.

Definition key_eqb_subproof (k1 k2: key) : { k1 = k2 } + { k1 <> k2 }.
Proof. decide equality. Defined.

Definition key_eqb (k1 k2: key) : bool :=
  if key_eqb_subproof k1 k2 then true else false. 

Lemma key_eqP : Equality.axiom key_eqb.
Proof.
move=> k1 k2.
rewrite /key_eqb.
by case: key_eqb_subproof => /= H;constructor.
Qed.

HB.instance Definition _ := hasDecEq.Build key key_eqP.

Definition key_to_nat (a : key) : nat :=
  match a with Dec => 0 | Enc => 1 end.

Definition nat_to_key (a : nat) : key :=
  match a with 0 => Dec | _ => Enc end.

Lemma key_natK : cancel key_to_nat nat_to_key.
Proof. by case. Qed.

HB.instance Definition _ : isCountable key := CanIsCountable key_natK.

Definition key_enum := [:: Dec; Enc].

Lemma key_enumP : Finite.axiom key_enum.
Proof. by case. Qed.

HB.instance Definition _ := isFinite.Build key key_enumP.

End key_def.

(* ========================================================================== *)
(*                   Party-Labeled HE Type Bundle                              *)
(* ========================================================================== *)

Record HETypes := MkHE {
  party : finType ;           (* party/participant type *)
  plain : finComNzRingType ;  (* message/plaintext space *)
  rand :  ringType ;          (* randomness space,
                                 ringType enables r1*r2 and r^+k *)
  cipher : ringType ;         (* raw ciphertext values without party label *)
  party_cipher : finType ;    (* party-labeled ciphertext *)
  pkey : Type ;               (* party-labeled key *)
}.
