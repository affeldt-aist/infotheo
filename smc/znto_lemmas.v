From HB Require Import structures.
Require Import Reals.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring.
Require Import ssrR Reals_ext realType_ext logb ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_proba smc_entropy.

Import GRing.Theory.
Import Num.Theory.

(************************************************************************************)
(*                 Lemmas for Proving the SMC Zn-to-Z2 Protoco                      *)
(*                                                                                  *)
(*     The SMC Zn-to-Z2 protocl is from:                                            *)
(*                                                                                  *)
(*         Information-theoretically Secure Number-product Protocol                 *)
(*                                                                                  *)
(*     SHEN, Chih-Hao, et al.                                                       *)
(*     In: 2008 IEEE International Conference on Granular Computing.                *)
(*     IEEE, 2008. p. 556-561.                                                      *)
(*                                                                                  *)
(************************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope chap2_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

Reserved Notation "u *zn w" (at level 40).
Reserved Notation "u \*zn w" (at level 40).

Section znto_def.
  
Variable TX : ringType.
Variable n : nat.
Variable T : finType.

Definition zntoz2 (a b:'rV[TX]_n) := (a *m b^T)``_ord0.

Definition zntoz2_rv (P: R.-fdist T) (A B: {RV P -> 'rV[TX]_n}) : {RV P -> TX} :=
  fun p => dotproduct (A p) (B p).
  
End znto_def.
