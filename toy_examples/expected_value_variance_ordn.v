(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum lra ring.
From mathcomp Require Import Rstruct reals.
Require Import realType_ext fdist proba.

(* Coq/SSReflect/MathComp, Morikita, Sect. 7.2, without inord *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope reals_ext_scope.
Local Open Scope tuple_ext_scope.
Local Open Scope ring_scope.

Import GRing.Theory Num.Theory Order.Theory.

Definition ord1 {n} := lift ord0 (@ord0 n).
Definition ord2 {n} := lift ord0 (@ord1 n).

Lemma ord0E n : 0%nat = @ord0 n. Proof. done. Qed.
Lemma ord1E n : 1%nat = @ord1 n. Proof. done. Qed.
Lemma ord2E n : 2%nat = @ord2 n. Proof. done. Qed.

Local Definition R := Rdefinitions.R.

Definition pmf : {ffun 'I_3 -> R} :=
  finfun [fun x => 0 with ord0 |-> 1/2, ord1 |-> 1/3, ord2 |-> 1/6].

Lemma pmf_ge0 : [forall a : 'I_3, 0 <= pmf a].
Proof.
apply/forallP => a.
rewrite /pmf ffunE /=.
apply/RleP.
by do! case: ifP => _; apply/RleP; lra.
Qed.

Lemma pmf01 : [forall a, 0 <= pmf a] && (\sum_(a in 'I_3) pmf a == 1).
Proof.
apply/andP; split; first exact: pmf_ge0.
by apply/eqP; rewrite 3!big_ord_recl big_ord0 /= /pmf !ffunE /=; lra.
Qed.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Definition P : {fdist 'I_3} := FDist.mk pmf01.

Definition X : {RV P -> R} := (fun i => i.+1%:R).

Lemma expected : `E X = 5/3.
Proof.
rewrite /Ex.
rewrite 3!big_ord_recl big_ord0 /=.
rewrite /pmf /X !ffunE /= /bump /=.
by field.
Qed.

Lemma variance : `V X = 5/9.
Proof.
rewrite VarE expected /Ex /X /sq_RV /comp_RV /=.
rewrite 3!big_ord_recl big_ord0 /=.
rewrite !ffunE /bump /=.
by field.
Qed.
