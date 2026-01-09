(******************************************************************************)
(*                                                                            *)
(* Benaloh as Homomorphic Encryption Instance                                 *)
(*                                                                            *)
(* This file shows that Benaloh implements the HE_SIG interface from          *)
(* homomorphic_encryption.v using Coq's module functor pattern.               *)
(*                                                                            *)
(* Structure:                                                                 *)
(*   Benaloh_Params - Module type for Benaloh parameters                      *)
(*   Benaloh_HE     - Functor: Benaloh_Params -> HE_SIG                       *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg zmodp.
From infotheo Require Import homomorphic_encryption.benaloh1994.benaloh_enc.
From infotheo Require Import homomorphic_encryption.he_sig.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*                        Benaloh Parameter Module Type                        *)
(* ========================================================================== *)

Module Type Benaloh_Params.
  Parameter n : nat.
  Parameter r : nat.
  Parameter n_gt1 : (1 < n)%N.
  Parameter r_gt1 : (1 < r)%N.
  Parameter y : 'Z_n.
  Parameter y_order_r : y ^+ r = 1.
End Benaloh_Params.

(* ========================================================================== *)
(*                     Benaloh HE_SIG Functor                                  *)
(* ========================================================================== *)

(* Given Benaloh parameters, produce an HE_SIG implementation *)
Module Benaloh_HE (P : Benaloh_Params) <: HE_SIG.
  
  Definition msg : comRingType := 'Z_P.r.
  Definition ct : ringType := 'Z_P.n.
  Definition rand : Type := 'Z_P.n.
  
  Definition enc (m : msg) (u : rand) : ct := benaloh_enc P.y m u.
  
  Lemma Emul_hom : forall (m1 m2 : msg) (r1 r2 : rand),
    exists r : rand, enc m1 r1 * enc m2 r2 = enc (m1 + m2) r.
  Proof.
    move=> m1 m2 u1 u2.
    exists (u1 * u2).
    exact: (enc_mul_dist P.r_gt1 P.y_order_r).
  Qed.
  
  Lemma Epow_hom : forall (m : msg) (k : nat) (r : rand),
    exists r' : rand, (enc m r) ^+ k = enc (m *+ k) r'.
  Proof.
    move=> m k u.
    exists (u ^+ k).
    exact: (enc_exp_dist P.r_gt1 P.y_order_r).
  Qed.

End Benaloh_HE.

(* ========================================================================== *)
(*                        Additional Benaloh Properties                        *)
(* ========================================================================== *)

(* These lemmas provide stronger results than HE_SIG (concrete randomness) *)

Module Benaloh_Extra (P : Benaloh_Params).
  
  Definition msg := 'Z_P.r.
  Definition ct := 'Z_P.n.
  Definition rand := 'Z_P.n.
  Definition enc (m : msg) (u : rand) : ct := benaloh_enc P.y m u.
  
  (* Concrete randomness formulas *)
  Lemma Emul_randomness : forall (m1 m2 : msg) (u1 u2 : rand),
    enc m1 u1 * enc m2 u2 = enc (m1 + m2) (u1 * u2).
  Proof. exact: (enc_mul_dist P.r_gt1 P.y_order_r). Qed.
  
  Lemma Epow_randomness : forall (m : msg) (k : nat) (u : rand),
    (enc m u) ^+ k = enc (m *+ k) (u ^+ k).
  Proof. exact: (enc_exp_dist P.r_gt1 P.y_order_r). Qed.
  
  (* Ring multiplication version of scalar homomorphism *)
  Lemma scalar_eq_ring_mul : forall (m1 m2 : msg),
    m1 * m2 = m1 *+ (m2 : nat).
  Proof.
    move=> m1 m2.
    rewrite mulrC -[m2 in m2 * _]natr_Zp mulr_natl.
    reflexivity.
  Qed.
  
  (* Epow with ring exponent *)
  Lemma Epow_ring : forall (m1 m2 : msg) (u : rand),
    exists u' : rand, (enc m1 u) ^+ (m2 : nat) = enc (m1 * m2) u'.
  Proof.
    move=> m1 m2 u.
    exists (u ^+ m2).
    rewrite (enc_exp_dist P.r_gt1 P.y_order_r).
    by rewrite scalar_eq_ring_mul.
  Qed.

End Benaloh_Extra.
