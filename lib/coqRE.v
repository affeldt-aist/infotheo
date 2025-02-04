(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
Require Import Reals.
From mathcomp Require Import lra.
From mathcomp Require Import Rstruct.

Local Open Scope R_scope.
Delimit Scope ring_scope with mcR.

Import Order.POrderTheory GRing.Theory Num.Theory.

Delimit Scope R_scope with coqR.

Lemma R1E : 1%coqR = 1%mcR. Proof. by []. Qed.
Lemma R0E : 0%coqR = 0%mcR. Proof. by []. Qed.

(* NB: PR https://github.com/math-comp/analysis/pull/1461 in progress in MCA *)
Lemma RsqrtE' (x : Rdefinitions.R) : sqrt x = Num.sqrt x.
Proof.
set Rx := Rcase_abs x.
have RxE: Rx = Rcase_abs x by [].
rewrite /sqrt.
rewrite -RxE.
move: RxE.
case: Rcase_abs=> x0 RxE.
  by rewrite RxE; have/RltP/ltW/ler0_sqrtr-> := x0.
rewrite /Rx -/(sqrt _) RsqrtE //.
by have/Rge_le/RleP:= x0.
Qed.

Definition coqRE :=
  (R0E, R1E, INRE, IZRposE,
    RinvE, RoppE, RdivE, RminusE, RplusE, RmultE, RpowE, RsqrtE').
