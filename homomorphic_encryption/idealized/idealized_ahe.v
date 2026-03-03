(******************************************************************************)
(*                                                                            *)
(* Idealized AHE Instance                                                     *)
(*                                                                            *)
(* This file provides an idealized AHEScheme where encryption is              *)
(* deterministic: enc(pk, m, r) = m. Randomness is ignored.                   *)
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
Require Import ahe_monoid.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*                   Idealized AHE Instance                                   *)
(* ========================================================================== *)

Section Idealized_AHE.

Variable msgT : finComNzRingType.

(* ========================================================================== *)
(*                   Type Bundle                                              *)
(* ========================================================================== *)

(* Following the Benaloh/Paillier pattern:
   MkHE plain rand cipher pub_key priv_key *)
Definition Idealized_HETypes : HETypes :=
  MkHE msgT         (* plain type = message space *)
       msgT         (* rand type = message (randomness ignored but needs a type) *)
       msgT         (* cipher type = message *)
       msgT         (* pub_key type - trivial *)
       msgT.        (* priv_key type - trivial *)

(* ========================================================================== *)
(*                   Encryption/Decryption Operations                         *)
(* ========================================================================== *)

(* Deterministic encryption: ignores randomness and key, just returns message *)
Definition idealized_enc (pk : msgT) (m r : msgT) : msgT := m.

(* Decryption: just returns the ciphertext as the message *)
Definition idealized_dec (dk : msgT) (c : msgT) : option msgT := Some c.

(* pub_of_priv: identity, since keys are trivial *)
Definition idealized_pub_of_priv (dk : msgT) : msgT := dk.

(* Decryption correctness - straightforward computation *)
Lemma idealized_dec_correct : forall (dk : msgT) (r m : msgT),
  idealized_dec dk (idealized_enc (idealized_pub_of_priv dk) m r) = Some m.
Proof. by []. Qed.

(* ========================================================================== *)
(*                   isEncDec Instance                                        *)
(* ========================================================================== *)

HB.instance Definition Idealized_isEncDec : isEncDec Idealized_HETypes :=
  @isEncDec.Build Idealized_HETypes
    idealized_enc idealized_dec idealized_pub_of_priv
    idealized_dec_correct.

(* ========================================================================== *)
(*                   Homomorphic Operations                                   *)
(* ========================================================================== *)

(* Homomorphic addition: adds the message components *)
Definition idealized_Emul (c1 c2 : msgT) : msgT := c1 + c2.

(* Homomorphic scalar multiplication: multiplies message by scalar *)
Definition idealized_Epow (c : msgT) (k : msgT) : msgT := c * k.

(* Randomness exponentiation - trivial since randomness is ignored *)
Definition idealized_rand_pow (r : msgT) (m : msgT) : msgT := r * m.

(* Randomness multiplication - trivial *)
Definition idealized_rand_mul (r1 r2 : msgT) : msgT := r1 * r2.

(* -------------------------------------------------------------------------- *)
(*  Local notations for compact {morph} syntax                                *)
(* -------------------------------------------------------------------------- *)

Local Notation IT := Idealized_HETypes.

Lemma idealized_Emul_addM :
    forall (k : pub_key IT),
    {morph enc_curry IT k
      : mr1 mr2 / mr_bop IT +%R idealized_rand_mul mr1 mr2
      >-> idealized_Emul mr1 mr2}.
Proof.
  move=> p [m1 r1] [m2 r2].
  by rewrite /mr_bop /enc_curry /idealized_Emul /idealized_enc /idealized_rand_mul /=.
Qed.

Lemma idealized_Epow_scalarM :
    forall (k : pub_key IT) (j : plain IT),
    {morph enc_curry IT k
      : mr / mr_bop_rplain IT *%R idealized_rand_pow mr j
      >-> idealized_Epow mr j}.
Proof.
  move=> p j [m r].
  rewrite /mr_bop_rplain /enc_curry /idealized_Epow /idealized_rand_pow /idealized_enc /=.
  by rewrite mulrC.
Qed.

(* ========================================================================== *)
(*                   isAHEnc Instance                                         *)
(* ========================================================================== *)

HB.instance Definition Idealized_isAHEnc : isAHEnc Idealized_HETypes :=
  @isAHEnc.Build Idealized_HETypes
    idealized_Emul idealized_Epow idealized_rand_pow idealized_rand_mul
    idealized_Emul_addM idealized_Epow_scalarM.

(* ========================================================================== *)
(*                   Algebraic Properties (isAHEMonoid)                       *)
(* ========================================================================== *)

Definition idealized_rand_id : msgT := 1.

Lemma idealized_Emul_assoc : associative idealized_Emul.
Proof. by move=> x y z; rewrite /idealized_Emul addrA. Qed.

Lemma idealized_Emul_comm : commutative idealized_Emul.
Proof. by move=> x y; rewrite /idealized_Emul addrC. Qed.

Lemma idealized_Emul_id :
  forall k : pub_key IT, left_id (enc_curry IT k (0, idealized_rand_id)) idealized_Emul.
Proof.
  move=> k x.
  by rewrite /enc_curry /idealized_enc /idealized_Emul /= add0r.
Qed.

HB.instance Definition Idealized_isAHEMonoid : isAHEMonoid Idealized_HETypes :=
  @isAHEMonoid.Build Idealized_HETypes
    idealized_rand_id
    idealized_Emul_assoc idealized_Emul_comm idealized_Emul_id.

End Idealized_AHE.
