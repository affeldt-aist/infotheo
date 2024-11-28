From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
Require Import Reals.
From mathcomp Require Import Rstruct ring.
Require Import ssrR Reals_ext realType_ext logb ssr_ext ssralg_ext bigop_ext.
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

Reserved Notation "u *d w" (at level 40).
Reserved Notation "u \*d w" (at level 40).

Section interp.
Variable data : eqType.
Inductive proc : Type :=
  | Send : nat -> data -> proc -> proc
  | Recv : nat -> (data -> proc) -> proc
  | Ret : data -> proc
  | Fail : proc.

Fixpoint interp h (ps : seq proc) : seq proc :=
  if h is h.+1 then
    let step A (yes : proc -> A) (no : proc -> A) i :=
      let p := nth Fail ps i in
      if p is Send dst _ next then
        if nth Fail ps dst is Recv frm _ then
          if frm == i then yes next else no p
        else no p
      else no
       (if p is Recv frm f then
          if nth Fail ps frm is Send dst v _ then
            if dst == i then f v else p
          else p
        else  p)
    in
    if has (step bool (fun=>true) (fun=>false)) (iota 0 (size ps)) then
      let ps' := map (step proc idfun idfun) (iota 0 (size ps))
      in interp h ps'
    else
      ps
  else ps.
End interp.

Section scalar_product.
Variable TX VX : ringType.
Variable dotproduct : VX -> VX -> TX.
Notation "u *d w" := (dotproduct u w).

Definition alice : nat := 0.
Definition bob : nat := 1.
Definition coserv : nat := 2.
Definition data := option (TX + VX).
Definition one x : data := Some (inl x).
Definition vec x : data := Some (inr x).
Definition Recv_one frm f : proc data :=
  Recv frm (fun x => if x is Some (inl v) then f v else Ret None).
Definition Recv_vec frm f : proc data :=
  Recv frm (fun x => if x is Some (inr v) then f v else Ret None).

Definition palice (xa : VX) : proc data :=
  Recv_vec coserv (fun sa =>
  Recv_one coserv (fun ra =>
  Send bob (vec (xa + sa)) (
  Recv_vec bob (fun xb' =>
  Recv_one bob (fun t =>
  Ret (one (t - (xb' *d sa) + ra))))))).
Definition pbob (xb : VX) : proc data :=
  Recv_vec coserv (fun sb =>
  Recv_one coserv (fun yb =>
  Recv_one coserv (fun rb =>
  Recv_vec alice (fun xa' =>
  let t := xa' *d xb + rb - yb in
    Send alice (vec (xb + sb))
    (Send alice (one t) (Ret (one yb))))))).
Definition pcoserv (sa sb: VX) (ra yb: TX) : proc data :=
  Send alice (vec sa) (
  Send alice (one ra) (
  Send bob (vec sb) (
  Send bob (one yb) (
  Send bob (one (sa *d sb - ra)) (Ret None))))).

Variables (sa sb: VX) (ra yb: TX) (xa xb: VX).
Definition scalar_product h :=
  interp h [:: palice xa; pbob xb; pcoserv sa sb ra yb].

Goal scalar_product 8 = [:: Fail _; Fail _; Fail _].
rewrite /scalar_product.
rewrite (lock (4 : nat)) /=.
rewrite -lock /=.
Abort.

Lemma scalar_product_ok :
  scalar_product 8 =
  [:: Ret (one ((xa + sa) *d xb + (sa *d sb - ra) - yb - (xb + sb) *d sa + ra));
      Ret (one yb); Ret None].
Proof. reflexivity. Qed.
End scalar_product.
