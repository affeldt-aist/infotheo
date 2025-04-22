From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg ring.
From mathcomp Require Import Rstruct reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_proba smc_entropy smc_interpreter.

(**md***************************************************************************)
(* # SMC Program for the SMC Scalar Product Protocol                           *)
(*                                                                             *)
(* |   Definitions     |    | Meaning                                        | *)
(* |-------------------|----|------------------------------------------------| *)
(* | pcoserv           | == | The Commodity server process in the protocol.  | *)
(* | palice            | == | The Alice (Party#1) process in the protocol.   | *)
(* | pbob              | == | The Bob (Party#2) process in the protocol.     | *)
(* | is_scalar_product | == | The correctness of the SMC scalar product      | *)
(* |                   |    | results                                        | *)
(* |-------------------------------------------------------------------------| *)
(*                                                                             *)
(*                                                                             *)
(* Formalization for:                                                          *)
(* A practical approach to solve secure multi-party computation problems       *)
(* Du, W., Zhan, J.Z.                                                          *)
(* In: Workshop on New Security Paradigms (NSPW 2002), Virginia Beach, VA, USA *)
(* September 23-26, 2002. pp. 127–135. ACM (2002).                             *)
(* https://doi.org/10.1145/844102.844125                                       *)
(*                                                                             *)
(*******************************************************************************)


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

Section scalar_product.
Variable m : nat.
Variable TX : finComRingType.
Variable VX : lmodType TX. (* vector is not ringType (mul)*)
Variable dotproduct : VX -> VX -> TX.
Local Notation "u *d w" := (dotproduct u w).

Definition alice : nat := 0.
Definition bob : nat := 1.
Definition coserv : nat := 2.

Definition data := (TX + VX)%type.
Definition one x : data := inl x.
Definition vec x : data := inr x.

Definition Recv_one frm f : proc data :=
  Recv frm (fun x => if x is inl v then f v else Fail).
Definition Recv_vec frm f : proc data :=
  Recv frm (fun x => if x is inr v then f v else Fail).

Definition pcoserv (sa sb: VX) (ra : TX) : proc data :=
  Init (vec sa) (
  Init (vec sb) (
  Init (one ra) (
  Send alice (vec sa) (
  Send alice (one ra) (
  Send bob (vec sb) (
  Send bob (one (sa *d sb - ra)) Finish)))))).

Definition palice (xa : VX) : proc data :=
  Init (vec xa) (
  Recv_vec coserv (fun sa =>
  Recv_one coserv (fun ra =>
  Send bob (vec (xa + sa)) (
  Recv_vec bob (fun xb' =>
  Recv_one bob (fun t =>
  Ret (one (t - (xb' *d sa) + ra)))))))).

Definition pbob (xb : VX) (yb : TX) : proc data :=
  Init (vec xb) (
  Init (one yb) (
  Recv_vec coserv (fun sb =>
  Recv_one coserv (fun rb =>
  Recv_vec alice (fun xa' =>
  let t := xa' *d xb + rb - yb in
    Send alice (vec (xb + sb))
    (Send alice (one t) (Ret (one yb)))))))).

Variables (sa sb: VX) (ra yb: TX) (xa xb: VX).

Definition smc_scalar_product h :=
  (interp h [:: palice xa; pbob xb yb; pcoserv sa sb ra] [::[::];[::];[::]]).

Goal (smc_scalar_product 11).2 = ([::]).
cbv -[GRing.add GRing.opp GRing.Ring.sort (*Equality.eqtype_hasDecEq_mixin*) ].
Undo 1.
rewrite /smc_scalar_product.
rewrite (lock (11 : nat)) /=.
rewrite -lock (lock (10 : nat)) /=.
rewrite -lock (lock (9 : nat)) /=.
rewrite -lock (lock (8 : nat)) /=.
rewrite -lock (lock (7 : nat)) /=.
rewrite -lock (lock (6 : nat)) /=.
rewrite -lock (lock (5 : nat)) /=.
rewrite -lock (lock (4 : nat)) /=.
rewrite -lock (lock (3 : nat)) /=.
rewrite -lock (lock (2 : nat)) /=.
rewrite -lock (lock (1 : nat)) /=.
rewrite -lock (lock (0 : nat)) /=.
Abort.

Definition smc_scalar_product_traces :=
  interp_traces 11 [:: palice xa; pbob xb yb; pcoserv sa sb ra].

Definition smc_scalar_product_tracesT := 11.-bseq data.

Definition smc_scalar_product_party_tracesT :=
  3.-tuple smc_scalar_product_tracesT.

Definition is_scalar_product (trs: smc_scalar_product_party_tracesT) :=
  let '(ya, xa) :=
    if tnth trs 0 is Bseq [:: inl ya; _; _; _; _; inr xa] _ then (ya, xa)
    else (0,0) in
  let '(yb, xb) :=
    if tnth trs 1 is Bseq [:: inl yb; _; _; _; _; inr xb] _ then (yb, xb)
    else (0,0) in
  xa *d xb = ya + yb.

End scalar_product.

