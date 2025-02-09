(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect all_algebra lra.
From mathcomp Require Import mathcomp_extra classical_sets Rstruct reals.
From mathcomp Require Import topology normedtype derive exp realfun.
Require Import ssr_ext ssralg_ext realType_ext realType_ln derive_ext.

(**md**************************************************************************)
(* # The natural entropy function                                             *)
(*                                                                            *)
(* ```                                                                        *)
(*   H2ln p == the binary entropy function except that we replace the         *)
(*             logarithm in base 2 by its natural version                     *)
(*     H2 p == the binary entropy function                                    *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Import Order.POrderTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Definition H2ln {R : realType} : R -> R :=
  fun p : R => (- p * exp.ln p - (1 - p) * exp.ln (1 - p))%R.

Definition H2 {R : realType} (p : R) : R :=
  (- (p * log p) + - ((1 - p) * log (1 - p)))%R.

Section differentiation_continuity.
Context {R : realType}.

Definition sig_derive1_H2 (x : R) :
  {D : R | x \in `]0, 1[%classic -> is_derive x 1 H2 D}.
Proof.
evar (D0 : (R : Type)); evar (D1 : (R : Type)); exists D0.
rewrite inE /= => /andP [] x0 x1.
suff->: D0 = D1.
  rewrite /H2.
  apply: is_deriveD.
    apply: is_deriveN.
    apply: is_deriveM.
      exact: is_derive_id.
    exact: is_derive1_Logf.
  apply: is_deriveN.
  apply: is_deriveM.
  apply: is_derive1_comp.
  apply: is_derive1_Logf=> //.
  by rewrite subr_gt0 //.
have ? : x != 0 by exact: lt0r_neq0.
have ? : 1 - x != 0 by rewrite lt0r_neq0// subr_gt0.
rewrite /D1.
rewrite -!mulr_regl !(add0r, mul1r, mulr1, mulrN, mulNr, opprD, opprK).
rewrite mulrCA divff// mulrCA divff//.
rewrite !mulr1 addrCA !addrA subrr add0r addrC.
by instantiate (D0 := log (1 - x) - log x).
Defined.

Definition sig_derive1_nH2 (x : R) :
  {D : R | x \in `]0, 1[%classic -> is_derive x 1 (\- H2) D}.
Proof.
evar (D0 : (R : Type)); evar (D1 : (R : Type)); exists D0.
move/(svalP (sig_derive1_H2 x))=> is_derive1_H2.
suff->: D0 = D1.
  exact: is_deriveN.
rewrite /D1 /= opprB.
by instantiate (D0 := log x - log (1 - x)).
Defined.

Lemma derivable_nH2 v : {in `]0, 1[%classic, forall x : R, derivable (\- H2) x v}.
Proof.
move=> x /(svalP (sig_derive1_nH2 x))/@ex_derive.
by move/derivable1_diffP/diff_derivable.
Qed.

Local Notation DnH2 := (fun x : R => log x - log (1 - x)).

Lemma DnH2E : {in `]0, 1[%classic, forall x : R, 'D_1 (\- H2) x = DnH2 x}.
Proof. by move=> x /(svalP (sig_derive1_nH2 x))/@derive_val. Qed.

Lemma near_DnH2E :
  {in `]0, 1[%classic, forall x : R, \near x, 'D_1 (\- H2) x = DnH2 x}.
Proof.
apply: open_in_nearW; first exact: (@itv_open _ (R : realFieldType)).
exact: DnH2E.
Qed.

Definition sig_derive1_DnH2 (x : R) :
  {D : R | x \in `]0, 1[%classic -> is_derive x 1 ('D_1 (\- H2)) D}.
Proof.
evar (D0 : (R : Type)); evar (D1 : (R : Type)); exists D0.
move/[dup]=> x01.
rewrite inE /= => /andP [] x0 x1.
rewrite (near_eq_is_derive _ DnH2) ?oner_neq0//; last exact: near_DnH2E.
suff->: D0 = D1.
  apply: is_deriveB.
    exact: is_derive1_Logf.
  apply: is_derive1_Logf=> //.
  by rewrite subr_gt0.
have ? : x != 0 by exact: lt0r_neq0.
have ? : 1 - x != 0 by rewrite lt0r_neq0// subr_gt0.
rewrite /D1.
rewrite !(add0r, mul1r, mulr1, mulrN, mulNr) opprK -mulrDr.
by instantiate (D0 := (ln 2)^-1 * (x^-1 + (1 - x)^-1)).
Defined.

Local Notation DDnH2 := (fun x : R => (ln 2)^-1 * (x^-1 + (1 - x)^-1)).

Lemma DDnH2E : {in `]0, 1[%classic, forall x : R, 'D_1 ('D_1 (\- H2)) x = DDnH2 x}.
Proof. by move=> x /(svalP (sig_derive1_DnH2 x))/@derive_val. Qed.

Lemma DDnH2_nonneg : {in `]0, 1[%classic, forall x : R, 0 <= DDnH2 x}.
Proof.
move=> x; rewrite inE /= => /andP [] x0 x1.
rewrite mulr_ge0//.
  by rewrite invr_ge0 ln2_ge0.
by rewrite addr_ge0// invr_ge0 ltW // subr_gt0.
Qed.

Lemma derivable_DnH2 v : {in `]0, 1[%classic, forall x : R, derivable ('D_1 (\- H2)) x v}.
Proof.
move=> x /(svalP (sig_derive1_DnH2 x))/@ex_derive.
by move/derivable1_diffP/diff_derivable.
Qed.

(* TODO: move to analysis *)
Lemma continuous_id (T : topologicalType) : continuous (@idfun T).
Proof. exact/continuousP. Qed.

Lemma continuous_log (x : R) : 0 < x -> {for x, continuous log}.
Proof. by move=> x0 y; exact/differentiable_continuous/differentiable_Log. Qed.

Lemma continuous_onem : continuous (@onem R).
Proof.
move=> ?; by apply: continuousB; [exact: cst_continuous | exact: continuous_id].
Qed.

Lemma continuous_H2 : {in `]0, 1[%classic, forall x : R, {for x, continuous H2}}.
Proof.
move=> x /(svalP (sig_derive1_H2 x)) /@ex_derive.
by move/derivable1_diffP/differentiable_continuous.
Qed.

End differentiation_continuity.
