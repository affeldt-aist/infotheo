(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ring lra.
From mathcomp Require Import Rstruct reals.
Require Import realType_ext fdist proba.

(* Coq/SSReflect/MathComp, Morikita, Sect. 7.2, using tuple *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope reals_ext_scope.
Local Open Scope tuple_ext_scope.
Local Open Scope ring_scope.

Local Definition R := Rdefinitions.R.

Definition ps := [tuple (1/2:R); 1/3; 1/6].
Definition p : {ffun 'I_3 -> R} := [ffun i => tnth ps i].

Lemma p_nonneg : [forall a : 'I_3, 0 <= p a].
Proof.
apply/forallP => a.
rewrite /p ffunE.
apply/all_tnthP: a => /=.
rewrite !andb_idr => * //; lra.
Qed.

Lemma p_sum01 : [forall a, 0 <= p a] && (\sum_(a in 'I_3) p a == 1).
Proof.
apply/andP; split; first exact/p_nonneg.
apply/eqP.
by rewrite 3!big_ord_recl big_ord0 /= /p !ffunE !(tnth_nth 0) /=; field.
Qed.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Definition P : {fdist 'I_3} := FDist.mk p_sum01.

Definition X : {RV P -> R} := (fun i => i.+1%:R).

Lemma expected : `E X = 5/3.
Proof.
rewrite /Ex.
rewrite 3!big_ord_recl big_ord0 /=.
rewrite /X !ffunE !(tnth_nth 0) /=.
rewrite (_ : (bump 0 0).+1%:R = 2)//.
rewrite (_ : (bump 0 _).+1%:R = 3)//.
lra.
Qed.

Lemma variance : `V X = 5/9.
Proof.
rewrite VarE expected /Ex /X /sq_RV /comp_RV /=.
rewrite 3!big_ord_recl big_ord0 /=.
rewrite !ffunE !(tnth_nth 0) /=.
rewrite (_ : (bump 0 0).+1%:R = 2)//.
rewrite (_ : (bump 0 _).+1%:R = 3)//.
lra.
Qed.
