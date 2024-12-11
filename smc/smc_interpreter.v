From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
Require Import Reals.
From mathcomp Require Import Rstruct ring.
Require Import ssrR Reals_ext realType_ext logb ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy smc graphoid.

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
Variable data : eqType.
Variable m : Type.

Inductive proc : Type :=
  (*| Init : nat -> (m -> data) -> (data -> proc) -> proc*)
  | Init : nat -> data -> proc -> proc
  | Wait : proc -> proc
  | Send : nat -> data -> proc -> proc
  | Recv : nat -> (data -> proc) -> proc
  | Ret : data -> proc
  | Fail : proc.

Inductive log : Type :=
  | Log : nat -> nat -> data -> log
  | NoLog.

Definition log_eq (l1 l2: log) :=
  if l1 is Log round1 party1 d1 then
    if l2 is Log round2 party2 d2 then
        (round1 == round2) && (party1 == party2) && (d1 == d2)
    else
      false
  else
    if l2 is NoLog then true else false.

Lemma log_eqP : Equality.axiom log_eq.
Proof.
move => l1 l2.
apply: (iffP idP); last first.
  move->.
  rewrite /log_eq.
Admitted.

HB.instance Definition _ := hasDecEq.Build _ log_eqP.

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
    else if p is Init i d next then
      (yes next, logger i d logs)
    else if p is Wait next then
      (yes next, logs)
    else if p is Ret v then
      (yes p, logger i v logs)
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
Variable m : nat.
Variable TX : finComRingType.
Variable VX : lmodType TX. (* vector is not ringType (mul)*)
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
  Init alice (vec xa) (
  Wait (
  Wait (

  Recv_vec coserv (fun sa =>
  Recv_one coserv (fun ra =>
  Send bob (vec (xa + sa)) (
  Recv_vec bob (fun xb' =>
  Recv_one bob (fun t =>
  Ret (one (t - (xb' *d sa) + ra)))))))))).
Definition pbob (xb : VX) (yb : TX) : proc data :=
  Init bob (vec xb) (
  Wait (
  Wait (

  Recv_vec coserv (fun sb =>
  Recv_one coserv (fun rb =>
  Recv_vec alice (fun xa' =>
  let t := xa' *d xb + rb - yb in
    Send alice (vec (xb + sb))
    (Send alice (one t) (Ret (one yb))))))))).
Definition pcoserv (sa sb: VX) (ra : TX) : proc data :=
  Init coserv (vec sa) (
  Init coserv (vec sb) (
  Init coserv (one ra) (

  Send alice (vec sa) (
  Send alice (one ra) (
  Send bob (vec sb) (
  Send bob (one (sa *d sb - ra)) (Ret None))))))).

Variables (sa sb: VX) (ra yb: TX) (xa xb: VX).
Definition scalar_product h :=
  interp h [:: palice xa; pbob xb yb; pcoserv sa sb ra] [::].

About scalar_product.

Goal scalar_product 11 = ([:: (Fail _); (Fail _); (Fail _)], [::]).
cbv -[GRing.add GRing.opp GRing.Ring.sort].
Fail rewrite [X in Log _ X _]/alice.
(*fold coserv bob alice.*)
Undo 2.
rewrite /scalar_product.
rewrite (lock (11 : nat)) /=.
rewrite -lock (lock (10 : nat)) /=.
rewrite -lock (lock (9 : nat)) /=.
Abort.

(* Bug: the first Send is not in the logs *)
Lemma scalar_product_ok :
  scalar_product 11 =
  ([:: Ret (one ((xa + sa) *d xb + (sa *d sb - ra) - yb - (xb + sb) *d sa + ra));
       Ret (one yb);
       Ret None],
   [:: Log 0 0 (Some (inl ((xa + sa) *d xb + (sa *d sb - ra) - yb - (xb + sb) *d sa + ra)));
       Log 0 1 (Some (inl yb));
       Log 0 2 None;
       Log 1 0 (Some (inl ((xa + sa) *d xb + (sa *d sb - ra) - yb))); 
       Log 1 2 None;
       Log 2 0 (Some (inr (xb + sb)));
       Log 2 2 None;
       Log 3 1 (Some (inr (xa + sa)));
       Log 3 2 None;
       Log 4 1 (Some (inl (sa *d sb - ra)));
       Log 5 1 (Some (inr sb));
       Log 6 0 (Some (inl ra));
       Log 7 0 (Some (inr sa));
       Log 8 2 (Some (inl ra));
       Log 9 2 (Some (inr sb));
       Log 10 0 (Some (inr xa));
       Log 10 1 (Some (inr xb));
       Log 10 2 (Some (inr sa))
    ]
  ).
Proof. reflexivity. Qed.

End scalar_product.

Section information_leakage_proof.

Variable n m : nat.
Variable T : finType.
Variable P : R.-fdist T.
Let TX := [the finComRingType of 'I_m.+2]. 
Let VX := 'rV[TX]_n.

Definition dotproduct (a b:VX) : TX := (a *m b^T)``_ord0.

Variables (S1 S2 X1 X2: {RV P -> VX}) (R1 Y2: {RV P -> TX}).

Definition scalar_product_uncurry (o: VX * VX * TX * TX * VX * VX) : seq (log (data VX)) :=
  let '(sa, sb, ra, yb, xa, xb) := o in
  (scalar_product dotproduct sa sb ra yb xa xb 11).2.

Definition scalar_product_RV :=
  comp_RV scalar_product_uncurry [%S1, S2, R1, Y2, X1, X2] (TA:=(VX * VX * TX * TX * VX * VX)%type) (TB:=seq (log (data VX))).

Section alice_leakage_free_proof.

Record alice_view :=
  AliceView {
    x1  : option VX;
    s1  : option VX;
    r1  : option TX;
    x2' : option VX;
    t   : option TX;
    y1  : option TX;
  }.

(* Note: the timing we use comp_RV = the timing we done the measurment
   Measurement: needs to provide RV inputs.
*)

About alice.

Definition set_s1 (view :alice_view) (v : option VX) : alice_view :=
  AliceView (x1 view) v (r1 view) (x2' view) (t view) (y1 view).

Definition set_r1 (view :alice_view) (v : option TX) : alice_view :=
  AliceView (x1 view) (s1 view) v (x2' view) (t view) (y1 view).

Definition set_x2' (view :alice_view) (v : option VX) : alice_view :=
  AliceView (x1 view) (s1 view) (r1 view) v (t view) (y1 view).

Definition set_t (view :alice_view) (v : option TX) : alice_view :=
  AliceView (x1 view) (s1 view) (r1 view) (x2' view) v (y1 view).

Definition set_y1 (view :alice_view) (v : option TX) : alice_view :=
  AliceView (x1 view) (s1 view) (r1 view) (x2' view) (y1 view) v.

Definition build_alice_view (logs : seq (log (data VX))) (acc : option (alice_view)) : option (alice_view) :=
  let y1  := if nth (NoLog (data VX)) logs 0   is Log 0 alice (Some (inr ya)) then Some ya else None in
  let x1  := if nth (NoLog (data VX)) logs 15  is Log 10 alice (Some (inr xa)) then Some xa else None in
  let s1  := if nth (NoLog (data VX)) logs 17  is Log 7 alice (Some (inr sa)) then Some sa else None in
  let r1  := if nth (NoLog (data VX)) logs 13  is Log 6 alice (Some (inl ra)) then Some ra else None in
  let x2' := if nth (NoLog (data VX)) logs 5   is Log 2 alice (Some (inr xb')) then Some xb' else None in
  let t   := if nth (NoLog (data VX)) logs 3   is Log 1 alice (Some (inl t)) then Some t else None in
  if acc is Some view then
    Some (set_s1 (set_r1 (set_x2' (set_t (set_y1 view y1) t) x2') r1) s1)
  else
    None.

Lemma build_alice_view : (scalar_product dotproduct 10).1 (scalar_product 8).2 (AliceView None None None None None None) = (AliceView None None None None None None).
  
End alice_leakage_free_proof.

  

End information_leakage_proof.
