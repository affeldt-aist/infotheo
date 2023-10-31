(* infotheo: information theory and error-correcting codes in Coq               *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later              *)
From mathcomp Require Import all_ssreflect ssralg perm matrix.
From mathcomp Require boolp.
Require Import Reals Lra.
From mathcomp Require Import Rstruct.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop fdist.
Require Import proba jfdist_cond divergence entropy.

(******************************************************************************)
(*                Chapter 2 of Elements of Information Theory                 *)
(*                                                                            *)
(* Formalization of the chapter 2 of:                                         *)
(* Thomas M. Cover, Joy A. Thomas, Elements of Information Theory, Wiley,     *)
(* 2005                                                                       *)
(* See also entropy.v and convex_fdist.v                                      *)
(*                                                                            *)
(*                 mutual_info == mutual information (`I(X ; Y))              *)
(*               chain_rule_rV == chain rule for entropy (thm 2.5.1)          *)
(*      chain_rule_information == chain rule for information (thm 2.5.2)      *)
(* chain_rule_relative_entropy == chain rule for relative entropy (thm 2.5.3) *)
(*  data_processing_inequality == (thm 2.8.1)                                 *)
(*                                                                            *)
(* Extra lemma:                                                               *)
(*  han == Han's inequality                                                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Declare Scope chap2_scope.
Delimit Scope chap2_scope with chap2.

Reserved Notation "`H( X , Y )" (at level 10, X, Y at next level,
  format "`H( X ,  Y )").
Reserved Notation "`H( Y | X )" (at level 10, Y, X at next level).
Reserved Notation "`I( X ; Y )" (at level 50, format "`I( X ;  Y )").

Local Open Scope R_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.
