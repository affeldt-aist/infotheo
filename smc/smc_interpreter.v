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
  | Log : nat -> nat -> data -> log.

Definition step (A : Type) (ps : seq proc) (logs : seq log) (yes no : proc -> A)
  (logger : nat -> data -> seq log -> seq log)
  (i : nat) : A * seq log:=
  let p := nth Fail ps i in
    if p is Recv frm f then
        if nth Fail ps frm is Send dst v _ then
          if dst == i then (no (f v), logger i v logs) else (no p, logs)
        else (no p, logs)
    else if p is Send dst w next then
      if nth Fail ps dst is Recv frm _ then
        if frm == i then (yes next, logs) else (no p, logs)
      else (no p, logs)
    else
      (no p, logs).
About step.

(* Extract log in Send because only in send we have both dst and v: data;
   in Recv we only have f, no data.
*)
Fixpoint interp h (ps : seq proc) (logs : seq log) :=
  let logger := (fun round => (fun pid d logs => Log round pid d :: logs)) in
  if h is h.+1 then
    if has (fun i => fst (@step bool ps [::] (fun=>true) (fun=>false) (logger h) i))
        (iota 0 (size ps)) then
      let pslogs' := map (@step proc ps [::] idfun idfun (logger h)) (iota 0 (size ps)) in
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
Notation "u *d w" := (dotproduct u w).

Definition alice : nat := 0.
Definition bob : nat := 1.
Definition coserv : nat := 2.
(*Note: notation will make cbv fail.*)

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
Definition pbob (xb : VX) (yb : TX) : proc data :=
  Recv_vec coserv (fun sb =>
  Recv_one coserv (fun rb =>
  Recv_vec alice (fun xa' =>
  let t := xa' *d xb + rb - yb in
    Send alice (vec (xb + sb))
    (Send alice (one t) (Ret (one yb)))))).
Definition pcoserv (sa sb: VX) (ra : TX) : proc data :=
  Send alice (vec sa) (
  Send alice (one ra) (
  Send bob (vec sb) (
  Send bob (one (sa *d sb - ra)) (Ret None)))).

Variables (sa sb: VX) (ra yb: TX) (xa xb: VX).
Definition scalar_product h :=
  interp h [:: palice xa; pbob xb yb; pcoserv sa sb ra] [::].

About scalar_product.

Goal scalar_product 8 = ([:: (Fail _); (Fail _); (Fail _)], [::]).
cbv -[GRing.add GRing.opp GRing.Ring.sort].
Fail rewrite [X in Log _ X _]/alice.
(*fold coserv bob alice.*)
Undo 2.
rewrite /scalar_product.
rewrite (lock (8 : nat)) /=.
rewrite -lock (lock (7 : nat)) /=.
rewrite -lock (lock (6 : nat)) /=.
rewrite -lock (lock (5 : nat)) /=.
rewrite -lock (lock (4 : nat)) /=.
rewrite -lock (lock (3 : nat)) /=.
Abort.

(* Bug: the first Send is not in the logs *)
Lemma scalar_product_ok :
  scalar_product 8 =
  ([:: Ret (one ((xa + sa) *d xb + (sa *d sb - ra) - yb - (xb + sb) *d sa + ra));
       Ret (one yb);
       Ret None]
  ,[:: Log 1 0 (Some (inl ((xa + sa) *d xb + (sa *d sb - ra) - yb)));
       Log 2 0 (Some (inr (xb + sb)));
       Log 3 1 (Some (inr (xa + sa)));
       Log 4 1 (Some (inl (sa *d sb - ra)));
       Log 5 1 (Some (inr sb));
       Log 6 0 (Some (inl ra));
       Log 7 0 (Some (inr sa))
  ]).
Proof. reflexivity. Qed.

End scalar_product.

Section information_leakage_proof.

Variable TX VX : ringType.

Record alice_view :=
  AliceView {
    x1  : option (VX + unit);
    s1  : option (VX + unit);
    r1  : option (TX + unit);
    x2' : option (VX + unit);
    t   : option (TX + unit);
    y1  : option (TX + unit);
  }.

Definition set_x1 (view :alice_view) (v : VX) : alice_view :=
  AliceView (Some (inl v)) (s1 view) (r1 view) (x2' view) (t view) (y1 view).

Definition set_s1 (view :alice_view) (v : VX) : alice_view :=
  AliceView (x1 view) (Some (inl v)) (r1 view) (x2' view) (t view) (y1 view).

Definition set_r1 (view :alice_view) (v : TX) : alice_view :=
  AliceView (x1 view) (s1 view) (Some (inl v)) (x2' view) (t view) (y1 view).

Definition set_x2' (view :alice_view) (v : VX) : alice_view :=
  AliceView (x1 view) (s1 view) (r1 view) (Some (inl v)) (t view) (y1 view).

Definition set_t (view :alice_view) (v : TX) : alice_view :=
  AliceView (x1 view) (s1 view) (r1 view) (x2' view) (Some (inl v)) (y1 view).

Definition set_y1 (view :alice_view) (v : TX) : alice_view :=
  AliceView (x1 view) (s1 view) (r1 view) (x2' view) (y1 view) (Some (inl v)).

Definition build_alice_view (logs : seq (log (data TX VX))) (acc : option (alice_view + unit)) : option (alice_view + unit) :=
  let s1 := nth (inr tt) logs 0 in
  let r1 := nth (inr tt) logs 1 in
  foldr 

  if acc is Some (inl view) then
    (* Each log line can only provide one field -- we need a temporary building view here.
    *)
    Some (inl view)
  else
    Some (inr tt).
  

End information_leakage_proof.
