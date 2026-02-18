From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
From Ltac2 Require Import Message.
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import reals ring.
Require Import realType_ext realType_ext realType_ln ssr_ext ssralg_ext.
Require Import bigop_ext fdist proba jfdist_cond entropy graphoid spp_proba.

Import GRing.Theory.
Import Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

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
      exact: (inde_RV_comp f g H)
  | _ =>
      fail
  end.

