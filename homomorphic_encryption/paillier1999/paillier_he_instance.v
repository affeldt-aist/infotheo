(******************************************************************************)
(*                                                                            *)
(* Paillier as Homomorphic Encryption Instance                                *)
(*                                                                            *)
(* This file shows that Paillier implements the HE_SIG interface from         *)
(* homomorphic_encryption.v using Coq's module functor pattern.               *)
(*                                                                            *)
(* Structure:                                                                 *)
(*   Paillier_Params - Module type for Paillier parameters                    *)
(*   Paillier_HE     - Functor: Paillier_Params -> HE_SIG                     *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg zmodp.
From infotheo Require Import homomorphic_encryption.paillier1999.paillier_enc.
From infotheo Require Import homomorphic_encryption.he_sig.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*                       Paillier Parameter Module Type                        *)
(* ========================================================================== *)

Module Type Paillier_Params.
  Parameter n : nat.
  Parameter n_gt1 : (1 < n)%N.
  Definition n2 := (n * n)%N.
  Parameter g : 'Z_n2.
  Parameter g_order_n : g ^+ n = 1.
End Paillier_Params.

(* ========================================================================== *)
(*                     Paillier HE_SIG Functor                                 *)
(* ========================================================================== *)

(* Given Paillier parameters, produce an HE_SIG implementation *)
Module Paillier_HE (P : Paillier_Params) <: HE_SIG.
  
  Definition msg : comRingType := 'Z_P.n.
  Definition ct : ringType := 'Z_P.n2.
  Definition rand : Type := 'Z_P.n2.
  
  Definition enc (m : msg) (r : rand) : ct := paillier_enc P.g m r.
  
  Lemma Emul_hom : forall (m1 m2 : msg) (r1 r2 : rand),
    exists r : rand, enc m1 r1 * enc m2 r2 = enc (m1 + m2) r.
  Proof.
    move=> m1 m2 r1 r2.
    exists (r1 * r2).
    exact: (enc_mul_dist P.n_gt1 P.g_order_n).
  Qed.
  
  Lemma Epow_hom : forall (m : msg) (k : nat) (r : rand),
    exists r' : rand, (enc m r) ^+ k = enc (m *+ k) r'.
  Proof.
    move=> m k r.
    exists (r ^+ k).
    exact: (enc_exp_dist P.n_gt1 P.g_order_n).
  Qed.

End Paillier_HE.

(* ========================================================================== *)
(*                        Additional Paillier Properties                       *)
(* ========================================================================== *)

(* These lemmas provide stronger results than HE_SIG (concrete randomness) *)

Module Paillier_Extra (P : Paillier_Params).
  
  Definition msg := 'Z_P.n.
  Definition ct := 'Z_P.n2.
  Definition rand := 'Z_P.n2.
  Definition enc (m : msg) (r : rand) : ct := paillier_enc P.g m r.
  
  (* Concrete randomness formulas *)
  Lemma Emul_randomness : forall (m1 m2 : msg) (r1 r2 : rand),
    enc m1 r1 * enc m2 r2 = enc (m1 + m2) (r1 * r2).
  Proof. exact: (enc_mul_dist P.n_gt1 P.g_order_n). Qed.
  
  Lemma Epow_randomness : forall (m : msg) (k : nat) (r : rand),
    (enc m r) ^+ k = enc (m *+ k) (r ^+ k).
  Proof. exact: (enc_exp_dist P.n_gt1 P.g_order_n). Qed.
  
  (* Ring multiplication version of scalar homomorphism *)
  Lemma scalar_eq_ring_mul : forall (m1 m2 : msg),
    m1 * m2 = m1 *+ (m2 : nat).
  Proof.
    move=> m1 m2.
    rewrite mulrC -[m2 in m2 * _]natr_Zp mulr_natl.
    reflexivity.
  Qed.
  
  (* Epow with ring exponent *)
  Lemma Epow_ring : forall (m1 m2 : msg) (r : rand),
    exists r' : rand, (enc m1 r) ^+ (m2 : nat) = enc (m1 * m2) r'.
  Proof.
    move=> m1 m2 r.
    exists (r ^+ m2).
    rewrite (enc_exp_dist P.n_gt1 P.g_order_n).
    by rewrite scalar_eq_ring_mul.
  Qed.

End Paillier_Extra.
