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
  (* Identity: enc of rand_id 0 is identity for Emul *)
  Emul_id : forall k : pub_key T, left_id (E[ k ] (0, rand_id)) (@Emul T);
}.

#[short(type=AHEMonoidType)]
HB.structure Definition AHEMonoid := { T of isAHEMonoid T }.

Declare Scope emul_scope.
Delimit Scope emul_scope with E.

(* Notation for Emul operation - consistent with local notation in ahe_enc.v *)
Notation "x (.) y" := (Emul x y) (at level 40, left associativity) : emul_scope.

Section cipher_monoid.

Variable (T : AHEMonoidType) (k : pub_key T).

Definition e_id := E[k](0, rand_id).

HB.instance Definition _ := @Monoid.isComLaw.Build
  (cipher T) e_id Emul Emul_assoc Emul_comm (Emul_id k).

End cipher_monoid.

(* Notation for cipher monoid identity - use 1%E *)
Notation "1" := (e_id _) : emul_scope.

(* === Custom bigop notations (like \sum_, \prod_ in MathComp) === *)
(* The key k is explicit because the identity e_id depends on it. *)

Reserved Notation "\Emul[ k ]_ ( i <- r | P ) F"
  (at level 41, F at level 41, k at level 0, i, r at level 50,
   format "'[' \Emul[ k ]_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\Emul[ k ]_ ( i <- r ) F"
  (at level 41, F at level 41, k at level 0, i, r at level 50,
   format "'[' \Emul[ k ]_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\Emul[ k ]_ ( i < n | P ) F"
  (at level 41, F at level 41, k at level 0, i, n at level 50,
   format "'[' \Emul[ k ]_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\Emul[ k ]_ ( i < n ) F"
  (at level 41, F at level 41, k at level 0, i, n at level 50,
   format "'[' \Emul[ k ]_ ( i  <  n ) '/  '  F ']'").

Notation "\Emul[ k ]_ ( i <- r | P ) F" :=
  (\big[Emul/e_id k]_(i <- r | P) F) : emul_scope.
Notation "\Emul[ k ]_ ( i <- r ) F" :=
  (\big[Emul/e_id k]_(i <- r) F) : emul_scope.
Notation "\Emul[ k ]_ ( i < n | P ) F" :=
  (\big[Emul/e_id k]_(i < n | P) F) : emul_scope.
Notation "\Emul[ k ]_ ( i < n ) F" :=
  (\big[Emul/e_id k]_(i < n) F) : emul_scope.

Section test_bigop.

Variable (T : AHEMonoidType) (k : pub_key T).

Local Open Scope emul_scope.

(* Bigop over a finite index *)
Variable (n : nat) (f : 'I_n -> cipher T).
Check \Emul[k]_(i < n) f i.

(* Bigop over a list of ciphertexts *)
Variable (cs : seq (cipher T)).
Check \Emul[k]_(c <- cs) c.

(* Folding encrypted values: sum of encryptions *)
Variable (ms : seq (plain T)) (rs : seq (rand T)).
Check \Emul[k]_(mr <- zip ms rs) E[k](mr.1, mr.2).

(* Simple lemma using monoid properties *)
Lemma Emul_big_cons (c : cipher T) :
  \Emul[k]_(x <- c :: cs) x = c (.) (\Emul[k]_(x <- cs) x).
Proof. by rewrite big_cons. Qed.

End test_bigop.

