Require Import Reals Lra.
From mathcomp Require Import all_ssreflect.
From infotheo Require Import Reals_ext ssrR Rbigop proba.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Coq/SSReflect/MathComp, Morikita, Sect. 7.2, without inord *)

Local Open Scope reals_ext_scope.
Local Open Scope tuple_ext_scope.
Local Open Scope R_scope.

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

Definition p' : [finType of 'I_3] ->R+ := mkPosFfun p_nonneg.

Lemma p_sum1 : \sum_(i in 'I_3) p' i == 1.
Proof.
apply/eqP.
rewrite 3!big_ord_recl big_ord0 /=.
rewrite /p !ffunE /=.
by field.
Qed.

Local Open Scope proba_scope.

Definition P : {dist 'I_3} := mkDist p_sum1.

Definition X : {RV P -> R} := (fun i => INR i.+1).

Lemma expected : `E X = 5/3.
Proof.
rewrite /Ex.
rewrite 3!big_ord_recl big_ord0 /=.
rewrite /p /X !ffunE /= /bump /=.
rewrite !S_INR (_ : 0%:R = 0) //.
by field.
Qed.

Lemma variance : Var P X = 5/9.
Proof.
rewrite VarE expected /Ex /X /sq_RV /comp_RV /=.
rewrite 3!big_ord_recl big_ord0 /=.
rewrite !ffunE /bump /=.
rewrite !S_INR (_ : 0%:R = 0) //.
by field.
Qed.
