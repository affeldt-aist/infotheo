(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssrnum.
Require Import Reals Lra.
From mathcomp Require Import Rstruct.
Require Import ssrR Reals_ext Rbigop fdist proba.

(* Coq/SSReflect/MathComp, Morikita, Sect. 7.2 *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope reals_ext_scope.
Local Open Scope R_scope.
Local Open Scope ring_scope.

Definition f : {ffun 'I_3 -> R} := [ffun i =>
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

Lemma f_nonneg : [forall a : 'I_3, 0 <= f a].
Proof.
apply/forallP_leRP.
case/I3P.
- rewrite /f ffunE /= eqxx; lra.
- rewrite /f ffunE /= ifF; last by I3_neq.
  rewrite eqxx; lra.
- rewrite /f ffunE /= ifF; last by I3_neq.
  rewrite ifF; last by I3_neq.
  rewrite eqxx; lra.
Qed.

Definition pmf : [finType of 'I_3] ->R+ := mkNNFinfun f_nonneg.

Ltac I3_eq := rewrite (_ : _ == _ = true); last by
              apply/eqP/val_inj => /=; rewrite inordK.

Lemma pmf01 : [forall a, 0 <= pmf a] && (\sum_(a in 'I_3) pmf a == 1).
Proof.
apply/andP; split.
  exact: f_nonneg.
apply/eqP.
do 3 rewrite big_ord_recl.
rewrite big_ord0 addR0 /=.
rewrite /f !ffunE /= ifT; last by I3_eq.
rewrite ifF; last by I3_neq.
rewrite ifT; last by I3_eq.
rewrite ifF; last by I3_neq.
rewrite ifF; last by I3_neq.
rewrite ifT; last by I3_eq.
(* 1 / 2 + (1 / 3 + 1 / 6) = 1 *)
by field.
Qed.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Definition d : {fdist 'I_3} := FDist.mk pmf01.

Definition X : {RV d -> R} := (fun i => INR i.+1).

Lemma expected : `E X = 5/3.
Proof.
rewrite /Ex.
do 3 rewrite big_ord_recl.
rewrite big_ord0 addR0.
rewrite /X mul1R.
rewrite /f !ffunE /= ifT; last by I3_eq.
rewrite (_ : INR _ = 2) //.
rewrite /= ifF; last by I3_neq.
rewrite ifT; last by I3_eq.
rewrite (_ : INR _ = 3); last first.
  rewrite S_INR (_ : INR _ = 2) //; by field.
rewrite /f /= ifF; last by I3_neq.
rewrite ifF; last by I3_neq.
rewrite ifT; last by I3_eq.
field.
Qed.

Lemma variance : `V X = 5/9.
Proof.
rewrite VarE.
rewrite expected.
rewrite /Ex /X.
do 3 rewrite big_ord_recl.
rewrite big_ord0 addR0 /=.
rewrite /sq_RV /comp_RV /=.
rewrite !mul1R.
rewrite {1}/f !ffunE /=.
rewrite ifT; last by I3_eq.
rewrite (_ : INR _ = 2) // mulR1.
rewrite /f /=.
rewrite ifF; last by I3_neq.
rewrite ifT; last by I3_eq.
rewrite (_ : INR _ = 3); last first.
  rewrite S_INR (_ : INR _ = 2) //; by field.
rewrite ifF; last by I3_neq.
rewrite ifF; last by I3_neq.
rewrite ifT; last by I3_eq.
field.
Qed.
