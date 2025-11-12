(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From Coq Require Reals.
From mathcomp Require Import lra.
From mathcomp Require Import Rstruct.

Import Order.POrderTheory GRing.Theory Num.Theory.

(*Delimit Scope R_scope with coqR.*)
(*Delimit Scope ring_scope with mcR.*)

Lemma R1E : (Rdefinitions.IZR (BinNums.Zpos BinNums.xH)) (*1%coqR*) = 1%R.
Proof. by []. Qed.

Lemma R0E : (Rdefinitions.IZR BinNums.Z0) (*0%coqR*) = 0%R.
Proof. by []. Qed.

Definition coqRE :=
  (R0E, R1E, INRE, IZRposE,
    RinvE, RoppE, RdivE, RminusE, RplusE, RmultE, RpowE, RsqrtE).
