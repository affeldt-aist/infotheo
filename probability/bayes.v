(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import all_ssreflect ssralg fingroup perm finalg matrix.
From mathcomp Require boolp.
Require Import Reals. (* Lra Nsatz. *)
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop.
Require Import fdist cinde.

Local Open Scope tuple_ext_scope.
Local Open Scope proba_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* wip *)

Module BN.
Section bn.
Variable U : finType.
Variable P : fdist U.
Variable n : nat.

Variant aRV := mkRV : forall A : finType, {RV P -> A} -> aRV. 
Definition aRV_type (v : aRV) :=
  let: mkRV A V := v in A.

Definition aRV2 (x y : aRV) :=
  let: mkRV A X := x in
  let: mkRV B Y := y in
  mkRV [% X, Y].

Definition aRV0 := mkRV (fun _ => tt).

Section topological.
Variable parent : rel 'I_n.
Definition topological := forall i j : 'I_n, parent i j -> i < j.
End topological.

Record t :=
  { vars: 'I_n -> aRV;
    parent: rel 'I_n;
    topo: topological parent;
    indep: forall i j : 'I_n,
        ~~ closure parent [set i] j ->
        let: mkRV A X := vars i in
        let: mkRV B Y := vars j in
        let: mkRV C Z :=
           \big[aRV2/aRV0]_(k < n | closure parent [set k] i) vars k in
        X _|_ Y | Z }.
End bn.
End BN.
