(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2026 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum.
From Stdlib Require Reals.
From mathcomp Require Import arithmetic_tactic.
From mathcomp Require Import Rstruct.

Import Order.POrderTheory GRing.Theory Num.Theory.

(*Delimit Scope R_scope with coqR.*)
(*Delimit Scope ring_scope with mcR.*)

#[deprecated(since="infotheo 0.9.10", note="use `Rstruct.R1E`")]
Lemma R1E : (Rdefinitions.IZR (BinNums.Zpos BinNums.xH)) (*1%coqR*) = 1%R.
Proof. by []. Qed.

#[deprecated(since="infotheo 0.9.10", note="use `Rstruct.R0E`")]
Lemma R0E : (Rdefinitions.IZR BinNums.Z0) (*0%coqR*) = 0%R.
Proof. by []. Qed.

#[deprecated(since="infotheo 0.9.10", note="use `Rstruct.RealsE` or `Rstruct_topology.RealsE")]
Definition coqRE :=
  (R0E, R1E, INRE, IZRposE,
    RinvE, RoppE, RdivE, RminusE, RplusE, RmultE, RpowE, RsqrtE).
