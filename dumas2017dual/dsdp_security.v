From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap matrix lra.
Require Import rouche_capelli.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter smc_tactics.
Require Import smc_proba homomorphic_encryption.
Require Import dsdp_program dsdp_extra dsdp_algebra dsdp_entropy.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* Formalization of:                                                          *)
(*                                                                            *)
(* Dumas, J. G., Lafourcade, P., Orfila, J. B., & Puys, M. (2017).            *)
(* Dual protocols for private multi-party matrix multiplication               *)
(* and trust computations.                                                    *)
(* Computers & security, 71, 51-70.                                           *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

Local Definition R := Rdefinitions.R.

Section dsdp_security.

(* TODO: Add final security theorems combining algebraic and entropy results *)

(** ** Main Security Theorem *)

(*
Theorem dsdp_security_bounded_leakage :
  `H(v2 | alice_view) = log (m%:R) /\
  `H(v2 | alice_view) > 0.
Proof.
split.
- (* Equality *)
  rewrite -pair_entropy_equals_component.
  rewrite pair_entropy_via_conditioning.
  exact: pair_entropy_from_uniformity.
- (* Positive bound *)
  rewrite -pair_entropy_equals_component.
  rewrite pair_entropy_via_conditioning.
  rewrite pair_entropy_from_uniformity.
  (* log(m) > 0 since m >= 2 *)
  apply: log_gt0.
  rewrite ltr1n.
  (* m = m_minus_2.+2 >= 2 *)
  by [].
Qed.
*)

(** ** Interpretation *)

(* The adversary learns log(m) bits about v2, not 0 bits (perfect secrecy)
   but also not log(m^2) bits (complete knowledge).
   
   This is because:
   - There are m possible values for v2
   - Each is equally likely given alice_view
   - Entropy = log(m) bits
   
   Security holds despite information leakage.
*)

End dsdp_security.


