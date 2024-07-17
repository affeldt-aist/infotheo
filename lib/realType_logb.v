(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import reals exp.
Require Import realType_ext.

(******************************************************************************)
(*                          log_n x and n ^ x                                 *)
(*                                                                            *)
(* Definitions and lemmas about the logarithm and the exponential in base n.  *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   log == Log in base 2                                                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Import Order.POrderTheory GRing.Theory Num.Theory.

Definition Log {R : realType} (n : R) x := ln x / ln n.

Definition log {R : realType} (x : R) := Log 2 x.
