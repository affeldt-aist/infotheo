(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
Require Import Reals Lra.
From mathcomp Require Import all_ssreflect ssrnum.
From mathcomp Require Import Rstruct.
Require Import Reals_ext ssrR Rbigop fdist proba.

(* Coq/SSReflect/MathComp, Morikita, Sect. 7.2, without inord *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope reals_ext_scope.
Local Open Scope tuple_ext_scope.
Local Open Scope R_scope.
Local Open Scope ring_scope.

Definition ord1 {n} := lift ord0 (@ord0 n).
Definition ord2 {n} := lift ord0 (@ord1 n).

Lemma ord0E n : 0%nat = @ord0 n. Proof. done. Qed.
Lemma ord1E n : 1%nat = @ord1 n. Proof. done. Qed.
Lemma ord2E n : 2%nat = @ord2 n. Proof. done. Qed.

Definition p : {ffun 'I_3 -> R} :=
  finfun [fun x => 0 with ord0 |-> 1/2, ord1 |-> 1/3, ord2 |-> 1/6].

Lemma p_nonneg : [forall a : 'I_3, 0 <b= p a].
Proof.
apply/forallP => a.
rewrite /p ffunE /=.
apply/leRP.
do! case: ifP => _; lra.
Qed.

Definition p' : [finType of 'I_3] ->R+ := mkNNFinfun p_nonneg.

Lemma p_sum01 : [forall a, 0 <= p' a] && (\sum_(a in 'I_3) p' a == 1).
Proof.
apply/andP; split; first exact: p_nonneg.
by apply/eqP; rewrite 3!big_ord_recl big_ord0 /= /p !ffunE /=; field.
Qed.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Definition P : {fdist 'I_3} := FDist.mk p_sum01.

Definition X : {RV P -> R} := (fun i => INR i.+1).

Lemma expected : `E X = 5/3.
Proof.
rewrite /Ex.
rewrite 3!big_ord_recl big_ord0 /=.
rewrite /p /X !ffunE /= /bump /=.
rewrite !S_INR (_ : 0%:R = 0) //.
by field.
Qed.

Lemma variance : `V X = 5/9.
Proof.
rewrite VarE expected /Ex /X /sq_RV /comp_RV /=.
rewrite 3!big_ord_recl big_ord0 /=.
rewrite !ffunE /bump /=.
rewrite !S_INR (_ : 0%:R = 0) //.
by field.
Qed.
