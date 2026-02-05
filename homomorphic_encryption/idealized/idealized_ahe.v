(******************************************************************************)
(*                                                                            *)
(* Idealized Party-Labeled AHE Instance                                       *)
(*                                                                            *)
(* This file provides an idealized AHEAlgebra_scheme where encryption is      *)
(* deterministic: enc(p, m, r) = (p, m). Randomness is ignored.               *)
(*                                                                            *)
(* Use cases:                                                                 *)
(* - Computational correctness proofs via reflexivity                         *)
(* - Security analysis (information flow)                                     *)
(* - Rapid prototyping before instantiating with real schemes                 *)
(*                                                                            *)
(* Unlike concrete schemes (Benaloh, Paillier), this idealized model:         *)
(* - Has no cryptographic security guarantees                                 *)
(* - Enables simple reflexivity-based proofs for protocol correctness         *)
(* - Serves as a specification for what real schemes should implement         *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg ssrfun.
Require Import he_types.
Require Import enc_dec.
Require Import ahe_enc.
Require Import ahe_algebra.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*                   Idealized Party AHE Instance                             *)
(* ========================================================================== *)

Section Idealized_Party_AHE.

Variable partyT : finType.
Variable msgT : finComNzRingType.

(* Type definitions *)
Definition idealized_enc_party := (partyT * msgT)%type.
Definition idealized_pkey := (partyT * key_type * msgT)%type.

(* ========================================================================== *)
(*                   Type Bundle                                              *)
(* ========================================================================== *)

Definition Idealized_HETypes : HETypes := 
  MkHE partyT       (* party type *)
       msgT         (* plain type = message space *)
       msgT         (* rand type = message (randomness ignored but needs a type) *)
       msgT         (* cipher type = message (raw cipher without party label) *)
       idealized_enc_party  (* party_cipher = (party * msg) *)
       idealized_pkey.      (* pkey type *)

(* ========================================================================== *)
(*                   Encryption/Decryption Operations                         *)
(* ========================================================================== *)

(* Deterministic encryption: ignores randomness, just pairs party with message *)
Definition idealized_enc (p : partyT) (m r : msgT) :
  idealized_enc_party := (p, m).

Definition idealized_key (p : partyT) (k : key_type) (s : msgT) :
  idealized_pkey :=  (p, k, s).

Definition idealized_dec (dk : idealized_pkey) (e : idealized_enc_party) :
  option msgT := match dk, e with
    | (i, k, _), (j, m) => if (i == j) && (k == Dec) then Some m else None
    end.

(* Decryption correctness - straightforward computation *)
Lemma idealized_dec_correct : forall (p : partyT) (m r sk : msgT),
  idealized_dec (idealized_key p Dec sk) (idealized_enc p m r) = Some m.
Proof.
  move=> p m r sk.
  rewrite /idealized_dec /idealized_key /idealized_enc /=.
  by rewrite eq_refl.
Qed.

(* ========================================================================== *)
(*                   isEncDec Instance                                        *)
(* ========================================================================== *)

HB.instance Definition Idealized_isEncDec : isEncDec Idealized_HETypes := 
  @isEncDec.Build Idealized_HETypes 
    idealized_enc idealized_key idealized_dec
    idealized_dec_correct.

(* ========================================================================== *)
(*                   Homomorphic Operations                                   *)
(* ========================================================================== *)

(* Homomorphic addition: adds the message components.
   Like Benaloh, we take the party from e1 and ignore e2's party.
   This ensures associativity holds unconditionally. *)
Definition idealized_Emul (e1 e2 : idealized_enc_party) :
  idealized_enc_party := 
    let (p1, m1) := e1 in
    let (_, m2) := e2 in
    (p1, m1 + m2).

(* Homomorphic scalar multiplication: multiplies message by scalar *)
Definition idealized_Epow (e : idealized_enc_party) (k : msgT) :
  idealized_enc_party :=
    match e with
    | (p, m) => (p, m * k)
    end.

(* Randomness exponentiation - trivial since randomness is ignored *)
Definition idealized_rand_pow (r m : msgT) : msgT := r * m.

(* -------------------------------------------------------------------------- *)
(*  Local notations for compact {morph} syntax                                *)
(* -------------------------------------------------------------------------- *)

Local Notation IT := Idealized_HETypes.
Local Notation "E[ p ]" := (enc_curry IT p) (at level 10, p at level 9).
Local Notation "x {+} y" := (msg_rand_add IT x y)
  (at level 50, left associativity).
Local Notation "x {^}  y" := (unpair_mul_rand_op IT x y idealized_rand_pow)
  (at level 50, left associativity).
Local Notation "x (.) y" := (idealized_Emul x y)
  (at level 40, left associativity).
Local Notation "x (^) y" := (idealized_Epow x y)
  (at level 40, left associativity).

(* Additive homomorphism: E(m1,r1) * E(m2,r2) = E(m1+m2, r1*r2) 
   For idealized: (p, m1) *E (p, m2) = (p, m1+m2)
   Since encryption ignores randomness, this is trivially true. *)
Lemma idealized_Emul_addM : forall (p : partyT),
  {morph E[ p ] : x y / x {+} y >-> x (.) y}.
Proof.
  move=> p [m1 r1] [m2 r2].
  by rewrite /enc_curry /msg_rand_add /idealized_Emul /idealized_enc /=.
Qed.

(* Scalar multiplication homomorphism:
   E(m*k, r^k) = E(m,r) ^ k
   For idealized: (p, m*k) = (p, m) ^ k, which is true by definition. *)
Lemma idealized_Epow_mulM : forall (p : partyT) (k : msgT),
  {morph E[ p ] : mr / mr {^} k >-> mr (^) k}.
Proof.
  move=> p k [m r].
  rewrite /enc_curry /idealized_Epow /idealized_rand_pow /=.
  rewrite /idealized_enc /=.
  by rewrite mulrC.
Qed.

(* ========================================================================== *)
(*                   isAHEnc Instance                                         *)
(* ========================================================================== *)

HB.instance Definition Idealized_isAHEnc : isAHEnc Idealized_HETypes := 
  @isAHEnc.Build Idealized_HETypes 
    idealized_Emul idealized_Epow idealized_rand_pow
    idealized_Emul_addM idealized_Epow_mulM.

(* ========================================================================== *)
(*                   Algebraic Properties                                      *)
(* ========================================================================== *)

(* Associativity: (e1 *E e2) *E e3 = e1 *E (e2 *E e3) *)
Lemma idealized_Emul_assoc : forall (e1 e2 e3 : idealized_enc_party),
  idealized_Emul (idealized_Emul e1 e2) e3 = idealized_Emul e1 (idealized_Emul e2 e3).
Proof.
  move=> [p1 m1] [p2 m2] [p3 m3].
  by rewrite /idealized_Emul /= addrA.
Qed.

(* Unit randomness: 1 (or any value, since randomness is ignored) *)
Definition idealized_rand_unit : msgT := 1.

(* Right identity: e *E E(p, 0, 1) = e *)
Lemma idealized_Emul_id : forall (p : partyT) (e : idealized_enc_party),
  idealized_Emul e (idealized_enc p 0 idealized_rand_unit) = e.
Proof.
  move=> p [q m].
  by rewrite /idealized_Emul /idealized_enc /= addr0.
Qed.

(* Cipher projection: extracts the message component *)
Definition idealized_enc_cipher (e : idealized_enc_party) : msgT :=
  match e with (_, m) => m end.

(* Cipher-level commutativity: the message part commutes *)
Lemma idealized_Emul_comm_cipher : forall (e1 e2 : idealized_enc_party),
  idealized_enc_cipher (idealized_Emul e1 e2) = 
  idealized_enc_cipher (idealized_Emul e2 e1).
Proof.
  move=> [p1 m1] [p2 m2].
  by rewrite /idealized_enc_cipher /idealized_Emul /= addrC.
Qed.

(* ========================================================================== *)
(*                   isAHEAlgebra Instance                                    *)
(* ========================================================================== *)

HB.instance Definition Idealized_isAHEAlgebra : isAHEAlgebra Idealized_HETypes := 
  @isAHEAlgebra.Build Idealized_HETypes 
    idealized_Emul_assoc idealized_rand_unit idealized_Emul_id
    idealized_enc_cipher idealized_Emul_comm_cipher.

End Idealized_Party_AHE.
