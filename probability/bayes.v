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
Variable types : 'I_n -> finType.
Variable vars : forall i, {RV P -> types i}.

Section Imap.
Variable parent : rel 'I_n.
Variable vals : forall i, types i.

Definition topological := forall i j : 'I_n, parent i j -> i < j.

Definition preim_vars (I : {set 'I_n}) :=
  \bigcap_(i < n) if i \in I then vars i @^-1 (vals i) else setT.

Definition independence (i j : 'I_n) :=
  ~~ closure parent [set i] j ->
  let E := preim_vars [set i] in
  let F := preim_vars [set j] in
  let parents := [set k | closure parent [set k] i] in
  let G := preim_vars parents in
  (`Pr_ P [ E :&: F | G ] = `Pr_ P [ E | G ] * `Pr_ P [ F | G ])%R.
End Imap.

(* Koller and Friedman, Definition 3.1, page 57 *)

Record t := mkBN
  { parent: rel 'I_n;
    topo: topological parent;
    indep: forall vals i j, independence parent vals i j
  }.
End bn.
End BN.

Section Factorization.
Import BN.
Variable U : finType.
Variable P : fdist U.
Variable n : nat.
Variable types : 'I_n -> finType.
Variable vars : forall i, {RV P -> types i}.
Variable bn : t vars.

(* Theorem 3.1, page 62 *)
Local Open Scope R_scope.

Theorem BN_factorization vals :
  Pr P (preim_vars vars vals setT) =
  \prod_(i < n)
   let parents := [set k | closure (parent bn) [set k] i] in
   `Pr_ P [ preim_vars vars vals [set i] | preim_vars vars vals parents ].
Abort.

End Factorization.
