From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix Rstruct ring.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter.

Import GRing.Theory.
Import Num.Theory.

(*******************************************************************************************)
(*                                                                                         *)
(* Formalization of:                                                                       *)
(*                                                                                         *)
(* Dumas, J. G., Lafourcade, P., Orfila, J. B., & Puys, M. (2017).                         *)
(* Dual protocols for private multi-party matrix multiplication and trust computations.    *)
(* Computers & security, 71, 51-70.                                                        *)
(*                                                                                         *)
(*******************************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

Local Definition R := Rdefinitions.R.

Reserved Notation "u *h w" (at level 40).
Reserved Notation "u ^h w" (at level 40).

Section he.

Variable msg : finComRingType.  (* TODO message must be modulo M *)

Inductive enc : Type :=
  | E : nat -> msg -> enc.

Definition enc_eq (e1 e2 : enc) : bool :=
  match e1, e2 with
  | E i1 m1, E i2 m2 => (i1 == i2) && (m1 == m2)
  end.

Lemma enc_eqP : Equality.axiom enc_eq.
Proof.
move => e1 e2.
rewrite /enc_eq.
case e1 => n1 s1.
case e2 => n2 s2.
apply: (iffP idP).
  move/andP => [/eqP Ha /eqP Hb].
  by rewrite Ha Hb.
move => H.
injection H => Hs Hn. (* Note: get n, s assumptions from from E n1 s1 = E n2 s2*)
rewrite Hs Hn.
apply/andP => //=.
Qed.

HB.instance Definition _ := hasDecEq.Build enc enc_eqP.

Definition D (p : nat) (e : enc) : msg :=
  match e with
  | E i m => if i == p then m else 0
  (* TODO: returning 0 instead of making it an option because it is
     troublesome when mixing with Send, Recv, etc.
  *)
  end.

Definition Emul (e1 e2 : enc) : enc := 
  match (e1, e2) with
  | (E i1 m1, E i2 m2) => if i1 == i2 then E i1 (m1 + m2) else E 0 0 (* TODO: mod M?*)
  end.

Definition Epow (e : enc) (m2 : msg) : enc :=
  match e with
  | E i m1 => E i (m1 * m2) (* TODO: mod M?*)
  end.

End he.

Section dsdp.

Variable msg : finComRingType.

Let enc := enc msg.

Notation "u *h w" := (Emul u w).
Notation "u ^h w" := (Epow u w).

Definition alice : nat := 0.
Definition bob : nat := 1.
Definition charlie : nat := 2.

Definition data := (msg + enc)%type.
Definition d x : data := inl x.
Definition e x : data := inr x.

Definition Recv_enc frm f : proc data :=
  Recv frm (fun x => if x is inr v then f v else Fail).

Definition pbob (v2 : msg) : proc data :=
  Init (d v2) (
  Send alice (e (E bob v2)) (
  Recv_enc alice (fun a2 =>
  Recv_enc alice (fun a3 =>
  let d2 := D bob a2 in  
    Send charlie (e (a3 *h (E charlie d2))) (
  Finish))))).

Definition pcharlie (v3 : msg) : proc data :=
  Init (d v3) (
  Send alice (e (E charlie v3)) (
  Recv_enc bob (fun b3 => (
  let d3 := D charlie b3 in
    Send alice (e (E alice d3))
  Finish)))).

Definition palice (v1 u1 u2 u3 r2 r3: msg) : proc data :=
  Init (d v1) (
  Init (d u1) (
  Init (d u2) (
  Init (d u3) (
  Init (d r2) (
  Init (d r3) (
  Recv_enc bob (fun c2 =>
  Recv_enc charlie (fun c3 =>
  let a2 := (c2 ^h u2 *h (E bob r2)) in
  let a3 := (c3 ^h u3 *h (E charlie r3)) in
    Send bob (e a2) (
    Send bob (e a3) (
    Recv_enc charlie (fun g =>
    Ret (d ((D alice g) - r2 - r3 + u1 * v1))))))))))))).
  
Variables (v1 v2 v3 u1 u2 u3 r2 r3 : msg).
Definition dsdp h :=
  (interp h [:: palice v1 u1 u2 u3 r2 r3; pbob v2; pcharlie v3] [::[::];[::];[::]]).


(* Different from SMC scalar product: has much less calculations *)
Goal (dsdp 15).2 = ([::]).
rewrite /dsdp.
rewrite (lock (15 : nat)) /=.
rewrite -lock (lock (14 : nat)) /=.
rewrite -lock (lock (13 : nat)) /=.
rewrite -lock (lock (12 : nat)) /=.
rewrite -lock (lock (11 : nat)) /=.
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
rewrite !/Emul /=.
Abort.

Lemma dsdp_ok :
  dsdp 15 = 
  ([:: Finish; Finish; Finish],
   [:: [:: d (v3 * u3 + r3 + (v2 * u2 + r2) - r2 - r3 + u1 * v1);
           e (E alice (v3 * u3 + r3 + (v2 * u2 + r2))); 
           e (E charlie v3);
           e (E bob v2);
           d r3; d r2; d u3; d u2; d u1; d v1];
       [:: e (E charlie (v3 * u3 + r3));
           e (E bob (v2 * u2 + r2)); d v2];  (* Eventually will be recorded in Recv or Ret*)
       [:: e (E charlie (v3 * u3 + r3 + (v2 * u2 + r2))); d v3]
  ]).
Proof. reflexivity. Qed.

Definition dsdp_traceT := (15.-bseq data).
Definition dsdp_tracesT := 3.-tuple dsdp_traceT.

Definition dsdp_traces :=
  interp_traces 15 [:: palice v1 u1 u2 u3 r2 r3; pbob v2; pcharlie v3].

Definition is_dsdp (trs : dsdp_tracesT) :=
  let '(s, u3, u2, u1, v1) :=
    if tnth trs 0 is Bseq [:: inl s; _; _; _; _; _; inl u3; inl u2; inl u1; inl v1] _
    then (s, u3, u2, u1, v1) else (0, 0, 0, 0, 0) in
  let '(v2) :=
    if tnth trs 1 is Bseq [:: _; _; inl v2] _
    then (v2) else (0) in
  let '(_v3) :=
    if tnth trs 2 is Bseq [:: _; inl v3] _
    then (v3) else (0) in
  s = v3 * u3 + v2 * u2 + v1 * u1.

Lemma dsdp_traces_ok :
  dsdp_traces =
    [tuple
       [bseq d (v3 * u3 + r3 + (v2 * u2 + r2) - r2 - r3 + u1 * v1);
             e (E alice (v3 * u3 + r3 + (v2 * u2 + r2)));
             e (E charlie v3);
             e (E bob v2);
             d r3; d r2; d u3; d u2; d u1; d v1];
       [bseq e (E charlie (v3 * u3 + r3));
             e (E bob (v2 * u2 + r2)); d v2];
       [bseq e (E charlie (v3 * u3 + r3 + (v2 * u2 + r2))); d v3]].
Proof. by apply/val_inj/(inj_map val_inj); rewrite interp_traces_ok. Qed.

Lemma dsdp_is_correct:
  is_dsdp dsdp_traces.
Proof. rewrite dsdp_traces_ok /is_dsdp /=.
ring.
Qed.

End dsdp.

Section dsdp_information_leakage_proof.

Variable T : finType.
Variable P : R.-fdist T.
Variable msg : finComRingType.

Let enc := enc msg.

Notation "u *h w" := (Emul u w).
Notation "u ^h w" := (Epow u w).


Definition dsdp_uncurry (o: msg * msg * msg * msg * msg * msg * msg * msg)
  : dsdp_tracesT msg :=
  let '(_v1, v2, v3, u1, u2, u3, r2, r3) := o in
  (dsdp_traces _v1 v2 v3 u1 u2 u3 r2 r3).

Record dsdp_random_inputs :=
  DSDPRandomInputs {
    v1 : {RV P -> msg};
    v2 : {RV P -> msg};
    v3 : {RV P -> msg};
    u1 : {RV P -> msg};
    u2 : {RV P -> msg};
    u3 : {RV P -> msg};
    r2 : {RV P -> msg};
    r3 : {RV P -> msg};
      
    (* About independence of inputs:
      if a RV is generated by party#i then it is independent of all party#j *)
}.

Variable inputs : dsdp_random_inputs.

Definition dsdp_RV (inputs : dsdp_random_inputs) :
  {RV P -> dsdp_tracesT msg} :=
    dsdp_uncurry `o
    [%v1 inputs, v2 inputs, v3 inputs,
      u1 inputs, u2 inputs, u3 inputs, r2 inputs, r3 inputs].

Let alice_traces : RV (dsdp_traceT msg) P :=
      (fun t => tnth t 0) `o dsdp_RV inputs.

Let _v1 := v1 inputs.
(* BUG: v1 in a RV2 list or in let '(...) will cause syntax error *)
Let v2 := v2 inputs.
Let v3 := v3 inputs.
Let u1 := u1 inputs.
Let u2 := u2 inputs.
Let u3 := u3 inputs.
Let r2 := r2 inputs.
Let r3 := r3 inputs.
Let vu2 : {RV P -> msg} := v2 \* u2.
Let vu3 : {RV P -> msg} := v3 \* u3.
Let d2  : {RV P -> msg} := vu2 \+ r2.
Let vu3r : {RV P -> msg} := vu3 \+ r3.
Let d3 : {RV P -> msg} := d2 \+ vu3r.
Let s : {RV P -> msg} := d3 \- r2 \- r3 \+ u1 \* _v1.
Let data := (msg + enc)%type.
Let d x : data := inl x.
Let e x : data := inr x.

Check (E alice) `o d3.

Let alice_traces_from_view v : 15.-bseq _ :=
    let '(s, _v1, u1, u2, u3, r2, r3, E_alice_d3, E_charlie_v3, E_bob_v2) := v in
    [bseq d s;
            e (E_alice_d3);
            e (E_charlie_v3);
            e (E_bob_v2);
            d r3; d r2; d u3; d u2; d u1; d _v1].

Lemma alice_traces_ok :
  alice_traces = alice_traces_from_view `o
                   [%s, _v1, u1, u2, u3, r2, r3,
                     (E alice) `o d3, (E charlie) `o v3, (E bob) `o v2 ].
Proof.
apply: boolp.funext => x /=.
rewrite /alice_traces /dsdp_RV /comp_RV /=.
Fail by rewrite dsdp_traces_ok.
Abort.

End dsdp_information_leakage_proof.
