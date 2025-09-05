(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Rstruct.  (* Remove this line when requiring Rocq >= 9.2 *)
From mathcomp Require Import all_ssreflect ssralg ssrnum lra ring.
From mathcomp Require Import Rstruct reals.
Require Import fdist proba.

(* Coq/SSReflect/MathComp, Morikita, Sect. 7.2 *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope reals_ext_scope.
Local Open Scope ring_scope.
Local Open Scope ring_scope.

Import GRing.Theory.

Local Definition R := Rdefinitions.R.

Definition pmf : {ffun 'I_3 -> R} := [ffun i =>
  [fun x => 0 with inord 0 |-> 1/2, inord 1 |-> 1/3, inord 2 |-> 1/6] i].

CoInductive I3_spec : 'I_3 -> bool -> bool -> bool -> Prop :=
| I2_0 : I3_spec (inord 0) true false false
| I2_1 : I3_spec (inord 1) false true false
| I2_2 : I3_spec (inord 2) false false true.

Ltac I3_neq := rewrite (_ : _ == _ = false); last by
              apply/negbTE/negP => /eqP/(congr1 (@nat_of_ord 3));
              rewrite !inordK.

Lemma I3P i : I3_spec i (i == inord 0) (i == inord 1) (i == inord 2).
Proof.
have : i \in map inord (iota 0 3).
  apply/mapP.
  exists (nat_of_ord i).
  by rewrite mem_iota leq0n add0n ltn_ord.
  by rewrite inord_val.
rewrite inE => /orP[/eqP ->|].
  rewrite eqxx.
  do 2 I3_neq.
  exact: I2_0.
rewrite inE => /orP[/eqP ->|].
  rewrite eqxx.
  I3_neq.
  I3_neq.
  exact: I2_1.
rewrite inE => /eqP ->.
rewrite eqxx.
I3_neq.
I3_neq.
exact: I2_2.
Qed.

Lemma pmf_ge0 : [forall a : 'I_3, 0 <= pmf a].
Proof.
apply/forallPP; first by move=> x; exact/RleP.
case/I3P.
- rewrite /f ffunE /= eqxx; apply/RleP; lra.
- rewrite /f ffunE /= ifF; last by I3_neq.
  rewrite eqxx; apply/RleP; lra.
- rewrite /f ffunE /= ifF; last by I3_neq.
  rewrite ifF; last by I3_neq.
  rewrite eqxx; apply/RleP; lra.
Qed.

Ltac I3_eq := rewrite (_ : _ == _ = true); last by
              apply/eqP/val_inj => /=; rewrite inordK.

Lemma pmf01 : [forall a, 0 <= pmf a] && (\sum_(a in 'I_3) pmf a == 1).
Proof.
apply/andP; split; first exact: pmf_ge0.
apply/eqP.
do 3 rewrite big_ord_recl.
rewrite big_ord0 addr0 /=.
rewrite /f !ffunE /= ifT; last by I3_eq.
rewrite ifF; last by I3_neq.
rewrite ifT; last by I3_eq.
rewrite ifF; last by I3_neq.
rewrite ifF; last by I3_neq.
rewrite ifT; last by I3_eq.
(* 1 / 2 + (1 / 3 + 1 / 6) = 1 *)
lra.
Qed.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Definition d : {fdist 'I_3} := FDist.mk pmf01.

Definition X : {RV d -> R} := (fun i => i.+1%:R).

Lemma expected : `E X = 5/3.
Proof.
rewrite /Ex.
do 3 rewrite big_ord_recl.
rewrite big_ord0 addr0.
rewrite /X mul1r.
rewrite /f !ffunE /= ifT; last by I3_eq.
rewrite (_ : (bump 0 0).+1%:R = 2) //.
rewrite /= ifF; last by I3_neq.
rewrite ifT; last by I3_eq.
rewrite (_ : (bump 0 (bump 0 0)).+1%:R = 3)//.
rewrite /f /= ifF; last by I3_neq.
rewrite ifF; last by I3_neq.
rewrite ifT; last by I3_eq.
lra.
Qed.

Lemma variance : `V X = 5/9.
Proof.
rewrite VarE.
rewrite expected.
rewrite /Ex /X.
do 3 rewrite big_ord_recl.
rewrite big_ord0 addr0 /=.
rewrite /sq_RV /comp_RV /=.
rewrite expr1n mul1r.
rewrite {1}/pmf !ffunE /=.
rewrite ifT; last by I3_eq.
rewrite (_ : (bump 0 0).+1%:R = 2) //.
rewrite /f /=.
rewrite ifF; last by I3_neq.
rewrite ifT; last by I3_eq.
rewrite (_ : (bump 0 (bump 0 0)).+1%:R = 3)//.
rewrite ifF; last by I3_neq.
rewrite ifF; last by I3_neq.
rewrite ifT; last by I3_eq.
lra.
Qed.
