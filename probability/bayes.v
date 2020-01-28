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

Definition aRV0 := mkRV (RV0 P).

Section topological.
Variable parent : rel 'I_n.
Definition topological := forall i j : 'I_n, parent i j -> i < j.
End topological.

(* Koller and Friedman, Definition 3.1, page 57 *)

Variable types : 'I_n -> finType.

Record t := mkBN
  { vars : forall i, {RV P -> types i};
    parent: rel 'I_n;
    topo: topological parent;
    indep: forall i j : 'I_n,
        ~~ closure parent [set i] j ->
        let X := vars i in
        let Y := vars j in
        let: mkRV C Z :=
           \big[aRV2/aRV0]_(k < n | closure parent [set k] i) mkRV (vars k) in
        X _|_ Y | Z }.
End bn.
End BN.

Section Factorization.
Import BN.
Variable U : finType.
Variable P : fdist U.
Variable n : nat.
Variable types : 'I_n -> finType.
Variable bn : t P types.

Definition RV_domains :=
  [seq types i | i <- [tuple i | i < n]].

Definition RV_domain := foldr prod_finType unit_finType RV_domains.

Variant aRVV := mkRVV : forall V : aRV P, aRV_type V -> aRVV.

Variables vals : forall i, types i.

Definition preim_vars (I : {set 'I_n}) :=
  \bigcap_(i < n) if i \in I then vars bn i @^-1 (vals i) else setT.

(* Theorem 3.1, page 62 *)

Theorem BN_factorization :
  Pr P (preim_vars setT) =
  \big[Rmult/R1]_(i < n)
   let parents := [set k | closure (parent bn) [set k] i] in
   `Pr_ P [ preim_vars [set i] | preim_vars parents ].
Abort.

End Factorization.
