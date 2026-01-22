(******************************************************************************)
(*                                                                            *)
(* Additively Homomorphic Encryption - Type Definitions                       *)
(*                                                                            *)
(* This file defines the base types for party-labeled homomorphic encryption: *)
(*   - key type (Dec | Enc) with HB instances                                 *)
(*   - Party_HE_types record bundling carrier types                           *)
(*                                                                            *)
(* These types use the `phe_` prefix (party HE) since they are not specific   *)
(* to additive homomorphism - the same type structure could support           *)
(* multiplicative HE or other variants.                                       *)
(*                                                                            *)
(* == Types ==                                                                *)
(*                                                                            *)
(*   Party_HE_types bundles five types:                                       *)
(*     - phe_party : finType          (party/participant space)               *)
(*     - phe_msg : finComNzRingType   (message/plaintext space)               *)
(*     - phe_rand : ringType          (randomness space, ring for r1*r2)      *)
(*     - phe_enc : finType            (party-labeled ciphertext space)        *)
(*     - phe_pkey : Type              (party-labeled key space)               *)
(*                                                                            *)
(* == Related Files ==                                                        *)
(*                                                                            *)
(*   ahe_enc_dec.v   - Encryption/decryption mixin (isPartyHE_EncDec)         *)
(*   ahe_homo_ops.v  - Homomorphic operations mixin (isPartyAHE_HomoOps)      *)
(*   ahe_algebra.v   - Algebraic properties mixin (isPartyAHE_Algebra)        *)
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

(* Record bundling the party-labeled HE types.
   Uses phe_ prefix (party HE) since these types are generic and could
   support any form of homomorphic encryption, not just additive. *)
Record Party_HE_types := MkPartyHE {
  phe_party : finType ;           (* party/participant type *)
  phe_msg : finComNzRingType ;    (* message/plaintext space *)
  phe_rand : ringType ;           (* randomness space, ringType enables r1*r2 and r^+k *)
  phe_enc : finType ;             (* party-labeled ciphertext *)
  phe_pkey : Type ;               (* party-labeled key *)
}.
