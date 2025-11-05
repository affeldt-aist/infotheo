From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter smc_tactics.
Require Import smc_proba homomorphic_encryption.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* Formalization of:                                                          *)
(*                                                                            *)
(* Dumas, J. G., Lafourcade, P., Orfila, J. B., & Puys, M. (2017).            *)
(* Dual protocols for private multi-party matrix multiplication               *)
(* and trust computations.                                                    *)
(* Computers & security, 71, 51-70.                                           *)
(*                                                                            *)
(******************************************************************************)

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

Section dsdp.

Variable F : finFieldType.
Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Hypothesis prime_m : prime m.

Local Notation msg := 'F_m.  (* Finite field with m elements *)
Let card_msg : #|msg| = m.
Proof. by rewrite card_Fp // pdiv_id. Qed.

Let enc := enc party msg.
Let pkey := pkey party msg.

Notation "u *h w" := (Emul u w).
Notation "u ^h w" := (Epow u w).

Definition alice : party := Alice.
Definition bob : party := Bob.
Definition charlie : party := Charlie.

Definition data := (msg + enc + pkey)%type.
Definition d x : data := inl (inl x).
Definition e x : data := inl (inr x).
Definition k x : data := inr x.

(* Should receive something the party can decrypt *)
Definition Recv_dec frm pkey f : proc data :=
  Recv frm (fun x => if x is inl (inr v) then
                       if D pkey v is Some v' then f v' else Fail
                     else Fail).

(* Should receive something the party cannot decrypt,
   but can do HE computation over it.
*)
Definition Recv_enc frm f : proc data :=
  Recv frm (fun x => if x is inl (inr v) then f v else Fail).

Definition pbob (dk : pkey)(v2 : msg) : proc data :=
  Init (k dk) (
  Init (d v2) (
  Send n(alice) (e (E bob v2)) (
  Recv_dec n(alice) dk (fun d2 =>
  Recv_enc n(alice) (fun a3 =>
    Send n(charlie) (e (a3 *h (E charlie d2))) (
  Finish)))))).

Definition pcharlie (dk : pkey)(v3 : msg) : proc data :=
  Init (k dk) (
  Init (d v3) (
  Send n(alice) (e (E charlie v3)) (
  Recv_dec n(bob) dk (fun d3 => (
    Send n(alice) (e (E alice d3))
  Finish))))).

Definition palice (dk : pkey)(v1 u1 u2 u3 r2 r3: msg) : proc data :=
  Init (k dk) (
  Init (d v1) (
  Init (d u1) (
  Init (d u2) (
  Init (d u3) (
  Init (d r2) (
  Init (d r3) (
  Recv_enc n(bob) (fun c2 =>
  Recv_enc n(charlie) (fun c3 =>
  let a2 := (c2 ^h u2 *h (E bob r2)) in
  let a3 := (c3 ^h u3 *h (E charlie r3)) in
    Send n(bob) (e a2) (
    Send n(bob) (e a3) (
    Recv_dec n(charlie) dk (fun g =>
    Ret (d ((g - r2 - r3 + u1 * v1))))))))))))))).
  
Variables (k_a k_b k_c v1 v2 v3 u1 u2 u3 r2 r3 : msg).

(* Note: must be with concrete values otherwise computation won't go *)
Let dk_a : pkey := (Alice, Dec, k_a). 
Let dk_b : pkey := (Bob, Dec, k_b). 
Let dk_c : pkey := (Charlie, Dec, k_c). 

Definition dsdp h :=
  (interp h [:: palice dk_a v1 u1 u2 u3 r2 r3; pbob dk_b v2; pcharlie dk_c v3] [::[::];[::];[::]]).

(* Different from SMC scalar product: has much less calculations *)
Goal (dsdp 15) = ([::],[::]).
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
(* Because we use nat as party ID as well --
   it confuses Rocq: what we are going to compute? The party ID or step? *)
rewrite -lock [X in interp X.+1](lock (2 : nat)) /=.
rewrite -lock (lock (1 : nat)) /=.
rewrite -lock (lock (0 : nat)) /=.
Abort.

Lemma dsdp_ok :
  dsdp 15 = 
  ([:: Finish; Finish; Finish],
   [:: [:: d (v3 * u3 + r3 + (v2 * u2 + r2) - r2 - r3 + u1 * v1);
           e (E alice (v3 * u3 + r3 + (v2 * u2 + r2))); 
           e (E charlie v3);
           e (E bob v2);
           d r3; d r2; d u3; d u2; d u1; d v1; k dk_a];
       [:: e (E charlie (v3 * u3 + r3));
           e (E bob (v2 * u2 + r2)); d v2; k dk_b];
       [:: e (E charlie (v3 * u3 + r3 + (v2 * u2 + r2))); d v3; k dk_c]
  ]).
Proof. reflexivity. Qed.

(* Fuel for the interpreter != size of tuple we need
   But it must be sized as the number of fuel.
*)
Notation dsdp_traceT := (15.-bseq data).
Notation dsdp_tracesT := (3.-tuple dsdp_traceT).

Definition dsdp_traces : dsdp_tracesT :=
  interp_traces 15 [:: palice dk_a v1 u1 u2 u3 r2 r3;
    pbob dk_b v2; pcharlie dk_c v3].

Definition is_dsdp (trs : dsdp_tracesT) :=
  let '(s, u3, u2, u1, v1) :=
    if tnth trs 0 is Bseq [:: inl (inl s); _; _; _; _; _;
                           inl (inl u3); inl (inl u2); inl (inl u1);
                           inl (inl v1); _] _
    then (s, u3, u2, u1, v1) else (0, 0, 0, 0, 0) in
  let '(v2) :=
    if tnth trs 1 is Bseq [:: _; _; inl (inl v2); _] _
    then (v2) else (0) in
  let '(_v3) :=
    if tnth trs 2 is Bseq [:: _; inl (inl v3); _] _
    then (v3) else (0) in
  s = v3 * u3 + v2 * u2 + v1 * u1.

Lemma dsdp_traces_ok :
  dsdp_traces =
    [tuple
       [bseq d (v3 * u3 + r3 + (v2 * u2 + r2) - r2 - r3 + u1 * v1);
             e (E alice (v3 * u3 + r3 + (v2 * u2 + r2)));
             e (E charlie v3);
             e (E bob v2);
             d r3; d r2; d u3; d u2; d u1; d v1; k dk_a];
       [bseq e (E charlie (v3 * u3 + r3));
             e (E bob (v2 * u2 + r2)); d v2; k dk_b];
       [bseq e (E charlie (v3 * u3 + r3 + (v2 * u2 + r2))); d v3; k dk_c]].
Proof. by apply/val_inj/(inj_map val_inj); rewrite interp_traces_ok. Qed.

Lemma dsdp_is_correct:
  is_dsdp dsdp_traces.
Proof. rewrite dsdp_traces_ok /is_dsdp /=.
ring.
Qed.

End dsdp.

