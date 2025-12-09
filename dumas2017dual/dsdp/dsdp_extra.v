From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap matrix lra.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter smc_tactics.

(* Import general lemmas from refactored files *)
Require Export extra_algebra extra_proba extra_entropy.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* DSDP-specific helper lemmas for formalization of:                          *)
(*                                                                            *)
(* Dumas, J. G., Lafourcade, P., Orfila, J. B., & Puys, M. (2017).            *)
(* Dual protocols for private multi-party matrix multiplication               *)
(* and trust computations.                                                    *)
(* Computers & security, 71, 51-70.                                           *)
(*                                                                            *)
(* NOTE: General lemmas have been refactored to:                              *)
(*   - extra_algebra.v : Log, bigop, Zp unit lemmas                           *)
(*   - extra_proba.v   : Conditional probability, RV permutation lemmas       *)
(*   - extra_entropy.v : Zero entropy, conditional independence lemmas        *)
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

Reserved Notation "u *h w" (at level 40).
Reserved Notation "u ^h w" (at level 40).

(* ========================================================================== *)
(*                     DSDP-specific helper lemmas                             *)
(* ========================================================================== *)

(* This file is now a thin wrapper that re-exports general lemmas
   and provides any DSDP-specific helpers that don't fit elsewhere.
   
   Most content has been moved to:
   - extra_algebra.v
   - extra_proba.v  
   - extra_entropy.v
   
   For Z/pqZ specific fiber entropy, see:
   - fiber_zpq.v
*)
