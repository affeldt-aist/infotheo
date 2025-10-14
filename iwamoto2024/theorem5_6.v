From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import mathcomp_extra contra Rstruct ring reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.

(* iwamoto2024:

  "Information-Theoretic Perspectives for Simulation-Based Security
  in Multi-Party Computation"

  https://doi.org/10.1587/transfun.2023TAI0001
*)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

Reserved Notation "u *d w" (at level 40).
Reserved Notation "u \*d w" (at level 40).

Section theorem5_6.

About markov_chain.

(* Note: Markov chain in infotheo has no RV version, so for now we need to
stick to distribution instead of random variables *)
Variables (R : realType) (TA TB TC : finType) (C'CP : R.-fdist (TA * TB * TC)).
Let C' := C'CP`1`1.
Let C := C'CP`1`2.
Let C'C := C'CP`1.
Let C'P := fdistX C'C.
Let PC' := fdistX ((fdistA C'CP)`2).

Let c := markov_chain C'CP.



End theorem5_6.
