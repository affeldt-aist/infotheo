(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
Require Import Reals.
From mathcomp Require Import lra.
From mathcomp Require Import Rstruct.

Import Order.POrderTheory GRing.Theory Num.Theory.

Delimit Scope R_scope with coqR.
Delimit Scope ring_scope with mcR.

Lemma R1E : 1%coqR = 1%mcR. Proof. by []. Qed.
Lemma R0E : 0%coqR = 0%mcR. Proof. by []. Qed.

Definition coqRE :=
  (R0E, R1E, INRE, IZRposE,
    RinvE, RoppE, RdivE, RminusE, RplusE, RmultE, RpowE, RsqrtE).
