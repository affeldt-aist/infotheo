From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
Require Import Reals.
From mathcomp Require Import Rstruct ring.
Require Import ssrR Reals_ext realType_ext logb ssr_ext ssralg_ext bigop_ext fdist.
Require Import fdist proba jfdist_cond entropy smc graphoid.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(*     Interpreter for Secure Multiparty Protocols                            *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope vec_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Reserved Notation "u *d w" (at level 40).
Reserved Notation "u \*d w" (at level 40).

Section interp.
Variable data : Type.

Inductive proc : Type :=
  | Send : nat -> data -> proc -> proc
  | Recv : nat -> (data -> proc) -> proc
  | Ret : data -> proc
  | Fail : proc.

Inductive log : Type :=
  | Log : nat -> data -> log.

Definition step (A : Type) (ps : seq proc) (logs : seq log) (yes no : proc * seq log -> A * seq log) (i : nat) : A * seq log:=
  let p := nth Fail ps i in
    if p is Recv frm f then
        if nth Fail ps frm is Send dst v _ then
          if dst == i then (no ((f v), logs)) else (no (p, logs))
        else (no (p, logs))
    else if p is Send dst w next then
      if nth Fail ps dst is Recv frm _ then
        if frm == i then (yes (next, logs)) else (no (p, logs))
      else (no (p, logs))
    else
      (no (p, logs)).
About step.

(* Extract log in Send because only in send we have both dst and v: data;
   in Recv we only have f, no data.
*)
Fixpoint interp h (ps : seq proc) (logs : seq log) :=
  let logger :=  (fun p => if p.1 is Send dst v _ then (p.1, Log dst v :: p.2) else p) in
  if h is h.+1 then
    if has (fun i => fst (@step bool ps logs (fun=>(true, logs)) (fun=>(false, logs)) i)) (iota 0 (size ps)) then
      let pslogs' := map (@step proc ps [::] logger logger) (iota 0 (size ps)) in
      let ps' := unzip1 pslogs' in
      let logs' := unzip2 pslogs' in
        interp h ps' ((foldr (fun pclogs acc => pclogs ++ acc) logs) logs')
    else (ps, logs)
  else (ps, logs).
About interp.
End interp.

Section scalar_product.
Variable TX VX : ringType.
Variable T : finType.
Variable P : R.-fdist T.
Variable dotproduct : VX -> VX -> TX.
Variable dotproduct_rv : {RV P -> VX} -> {RV P -> VX} -> {RV P -> TX}.
Notation "u *d w" := (dotproduct u w).
Notation "u \*d w" := (dotproduct_rv u w).

Definition alice : nat := 0.
Definition bob : nat := 1.
Definition coserv : nat := 2.
(*Note: notation will make cbv fail.*)

Definition data := option ({RV P -> TX} + {RV P -> VX}).
Definition one x : data := Some (inl x).
Definition vec x : data := Some (inr x).
Definition Recv_one frm f : proc data :=
  Recv frm (fun x => if x is Some (inl v) then f v else Ret None).
Definition Recv_vec frm f : proc data :=
  Recv frm (fun x => if x is Some (inr v) then f v else Ret None).

Definition palice (xa : {RV P -> VX}) : proc data :=
  Recv_vec coserv (fun sa =>
  Recv_one coserv (fun ra =>
  Send bob (vec (xa \+ sa)) (
  Recv_vec bob (fun xb' =>
  Recv_one bob (fun t =>
  Ret (one (t \- (xb' \*d sa) \+ ra))))))).
Definition pbob (xb : {RV P -> VX}) : proc data :=
  Recv_vec coserv (fun sb =>
  Recv_one coserv (fun yb =>
  Recv_one coserv (fun rb =>
  Recv_vec alice (fun xa' =>
  let t := xa' \*d xb \+ rb \- yb in
    Send alice (vec (xb \+ sb))
    (Send alice (one t) (Ret (one yb))))))).
Definition pcoserv (sa sb: {RV P -> VX}) (ra yb: {RV P -> TX}) : proc data :=
  Send alice (vec sa) (
  Send alice (one ra) (
  Send bob (vec sb) (
  Send bob (one yb) (
  Send bob (one (sa \*d sb \- ra)) (Ret None))))).

Variables (sa sb: {RV P -> VX}) (ra yb: {RV P -> TX}) (xa xb: {RV P -> VX}).
Definition scalar_product h :=
  interp h [:: palice xa; pbob xb; pcoserv sa sb ra yb] [::].

About scalar_product.

Goal scalar_product 8 = ([:: (Fail _); (Fail _); (Fail _)], [::]).
cbv -[GRing.add GRing.opp GRing.Ring.sort].
fold bob alice.
Undo 2.
rewrite /scalar_product.
rewrite (lock (8 : nat)) /=.
rewrite -lock (lock (7 : nat)) /=.
rewrite -lock (lock (6 : nat)) /=.
rewrite -lock (lock (5 : nat)) /=.
Abort.

Lemma scalar_product_ok :
  scalar_product 8 =
  ([:: Ret (one ((xa \+ sa) \*d xb \+ (sa \*d sb \- ra) \- yb \- (xb \+ sb) \*d sa \+ ra));
       Ret (one yb);
       Ret None]
  , [::
       Log alice (Some (inl ((xa \+ sa) \*d xb \+ (sa \*d sb \- ra) \- yb)));
       Log alice (Some (inr (xb \+ sb)));
       Log bob (Some (inr (xa \+ sa)));
       Log bob (Some (inr (xa \+ sa)));
       Log bob (Some (inl (sa \*d sb \- ra)));
       Log bob (Some (inr (xa \+ sa)));
       Log bob (Some (inl yb));
       Log bob (Some (inr (xa \+ sa)));
       Log bob (Some (inr sb));
       Log alice (Some (inl ra))]).
Proof. reflexivity. Qed.
End scalar_product.
