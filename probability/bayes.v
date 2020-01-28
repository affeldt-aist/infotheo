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

Definition topological := forall i j : 'I_n, parent i j -> i < j.

Definition preim_vars (I : {set 'I_n}) (vals : forall i, types i) :=
  \bigcap_(i in I) vars i @^-1 (vals i).

Definition cinde_preim (e f g : {set 'I_n}) :=
  forall vals,
    let E := preim_vars e vals in
    let F := preim_vars f vals in
    let G := preim_vars g vals in
    (`Pr_ P [ E :&: F | G ] = `Pr_ P [ E | G ] * `Pr_ P [ F | G ])%R.

Definition independence (i j : 'I_n) :=
  ~~ closure parent [set i] j ->
  let parents := [set k | closure parent [set k] i] in
  cinde_preim [set i] [set j] parents.
End Imap.

(* Koller and Friedman, Definition 3.1, page 57 *)

Record t := mkBN
  { parent: rel 'I_n;
    topo: topological parent;
    indep: forall i j, independence parent i j
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
  Pr P (preim_vars vars setT vals) =
  \prod_(i < n)
   let parents := [set k | closure (parent bn) [set k] i] in
   `Pr_ P [ preim_vars vars [set i] vals | preim_vars vars parents vals ].
Abort.

End Factorization.
