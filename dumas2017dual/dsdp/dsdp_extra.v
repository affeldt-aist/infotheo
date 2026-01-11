From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap matrix lra reals.
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

Section inde_entropy_lemmas.

Context {R : realType}.

(* Independence implies conditional entropy equals unconditional: H(X|V) = H(X) *)
Lemma inde_cond_entropy (U A B : finType) (P : R.-fdist U)
  (View : {RV P -> A}) (X : {RV P -> B}) :
  P |= View _|_ X ->
  `H(X | View) = `H `p_ X.
Proof.
move=> Hinde; rewrite /centropy_RV.
have Hprod := inde_dist_of_RV2 Hinde.
have Hprod2 : (`p_[%X, View]) = (((`p_[%X, View])`1) `x ((`p_[%X, View])`2))%fdist.
  by rewrite fst_RV2 snd_RV2 -fdistX_RV2 Hprod fdistX_prod.
by rewrite (centropy_indep Hprod2) fst_RV2.
Qed.

End inde_entropy_lemmas.
