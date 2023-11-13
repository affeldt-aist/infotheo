(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
Require Import Reals Lra.
From mathcomp Require Import all_ssreflect ssrnum.
From mathcomp Require Import Rstruct.
Require Import Reals_ext ssrR realType_ext Rbigop fdist proba.

(* Coq/SSReflect/MathComp, Morikita, Sect. 7.2, using tuple *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope reals_ext_scope.
Local Open Scope tuple_ext_scope.
Local Open Scope R_scope.
Local Open Scope ring_scope.

Definition ps := [tuple 1/2; 1/3; 1/6].
Definition p : {ffun 'I_3 -> R} := [ffun i => tnth ps i].

Lemma p_nonneg : [forall a : 'I_3, (0 <= p a)%mcR].
Proof.
apply/forallP => a.
rewrite /p ffunE.
apply/all_tnthP: a => /=.
rewrite !andb_idr => * //; apply/RleP; lra.
Qed.

Definition p' : [finType of 'I_3] ->R+ := mkNNFinfun p_nonneg.

Lemma p_sum01 : [forall a, 0 <= p' a] && (\sum_(a in 'I_3) p' a == 1).
Proof.
apply/andP; split; first exact/p_nonneg.
apply/eqP.
by rewrite 3!big_ord_recl big_ord0 /= /p !ffunE !(tnth_nth 0) /=; field.
Qed.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Definition P : {fdist 'I_3} := FDist.mk p_sum01.

Definition X : {RV P -> R} := (fun i => INR i.+1).

Lemma expected : `E X = 5/3.
Proof.
rewrite /Ex.
rewrite 3!big_ord_recl big_ord0 /=.
rewrite /X !ffunE !(tnth_nth 0) /=.
cbv; by field.
Qed.

Lemma variance : `V X = 5/9.
Proof.
rewrite VarE expected /Ex /X /sq_RV /comp_RV /=.
rewrite 3!big_ord_recl big_ord0 /=.
rewrite !ffunE !(tnth_nth 0) /=.
cbv; by field.
Qed.
