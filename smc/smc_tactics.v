From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
From Ltac2 Require Import Message.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring.
Require Import realType_ext realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_proba.

Import GRing.Theory.
Import Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope chap2_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

Local Definition R := Rdefinitions.R.

Ltac2 bar () := let x := '(3+4) in constr:($x + 5).

Ltac2 show_type () :=
  (* this is desugared into something more primitive from Pattern *)
  match! goal with
  | [ |- forall _ : ?e, _ ] =>
    (*Memo: note how it pattern match the goal and use the symbol inside.*)
    Message.print (Message.of_constr e)
  end.

Goal forall (n:nat), n = n.
Proof.
  show_type ().
Abort.


(* Maybe: Goal is  `[% vecRV_a, vecRV_b, oneRV_a, oneRV_b...] _|_ rv`
   Define a tactic to automatically generate sub-goals: vec_RV_a _|_ rv , vecRV_b _|_ rv...
   Meanwhile, we need a lemma to show that mutual independence implies pairwise independence.

   Not sure if we really need Ltac, though. If we can generate arbitrary sub-goals in other ways?
*)

Section boole.

Variables (A: finType)(m n: nat)(P : R.-fdist A).
Variables (TX VX: finType).
Variables (x1 x2 s1 s2: {RV P -> TX})(y1 r1: {RV P -> VX}).

Inductive boole := fact | lie.

Ltac2 rec print_list x := match x with
| a :: t => print (of_constr a); print_list t
| [] => ()
end.
Ltac2 Notation "ex2" x(list1(constr, ",")) := print_list x.
Goal true.
Proof.
ex2 [%x1, r1, s2].
ex2 x1, r1, s2.
Abort.
End boole.


Ltac RVs_to_tuple vs :=
  let rec iter vs :=
    match vs with
    | RV2 ?x ?y =>
        let ires := iter x in
        constr: ((ires, y))
    | ?z => z
    end in
  iter vs.

Ltac apply_inde_rv_comp f g :=
  match goal with
  | [ |- _ |= ?v1l _|_ ?v1r -> _ |= ?v2l _|_ ?v2r ] =>
      let H := fresh "H" in
      move => H;
      (have-> : v2l = f `o v1l by apply: boolp.funext => ? //=);
      (have-> : v2r = g `o v1r by apply: boolp.funext => ? //=);
      exact: (inde_rv_comp f g H)
  | _ =>
      fail
  end.

(*
Section test.
Variables (A: finType)(m n: nat)(P : R.-fdist A).
Variables (TX VX: finType).
Variables (x1 x2 s1 s2: {RV P -> TX})(y1 r1: {RV P -> VX}).

Ltac test vs :=
  let result := RVs_to_tuple vs in
  idtac result.

Eval cbv in ltac: (test [% x1, x2]).
End test.
*)
