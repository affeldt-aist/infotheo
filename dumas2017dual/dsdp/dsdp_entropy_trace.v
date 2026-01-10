From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap matrix lra.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter smc_tactics.
Require Import smc_proba homomorphic_encryption.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* DSDP Trace-based Entropy Analysis for Z/pqZ                                *)
(*                                                                            *)
(* This file provides trace-related entropy lemmas for the DSDP protocol      *)
(* over composite modulus Z/pqZ (Benaloh cryptosystem).                       *)
(*                                                                            *)
(* Key results:                                                               *)
(*   - dsdp_traces_zpq: Protocol trace structure for Z/pqZ                    *)
(*   - centropy_AliceTraces_AliceView: H(v|AliceTraces) = H(v|AliceView)       *)
(*                                                                            *)
(* These lemmas establish that conditioning on protocol traces equals         *)
(* conditioning on Alice's view, allowing security proofs to work with        *)
(* the simpler view representation.                                           *)
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

Section dsdp_traces_zpq.

(* Z/pqZ parameters - composite modulus for Benaloh cryptosystem *)
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Hypothesis prime_p : prime p.
Hypothesis prime_q : prime q.
Hypothesis coprime_pq : coprime p q.
Local Notation m := (p * q).

(* Z/pqZ ring structure for composite modulus arithmetic *)
Local Notation msg := 'Z_m.

(* m = p * q > 1 since p, q >= 2 *)
Let m_gt1 : (1 < m)%N.
Proof.
have Hp2: (1 < p)%N by [].
have Hq2: (1 < q)%N by [].
by rewrite (ltn_trans Hp2) // -{1}(muln1 p) ltn_pmul2l // ltnS.
Qed.

Let card_msg : #|msg| = m.
Proof. by rewrite card_ord Zp_cast. Qed.

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

(* Trace types for DSDP protocol *)
Notation dsdp_traceT := (15.-bseq data).
Notation dsdp_tracesT := (3.-tuple dsdp_traceT).

Variables (k_a k_b k_c v1 v2 v3 u1 u2 u3 r2 r3 : msg).

(* Decryption keys as public key records *)
Let dk_a : pkey := (Alice, Dec, k_a). 
Let dk_b : pkey := (Bob, Dec, k_b). 
Let dk_c : pkey := (Charlie, Dec, k_c). 

(* Protocol traces for Z/pqZ - same structure as F_m version but with 'Z_m *)
Definition dsdp_traces_zpq : dsdp_tracesT :=
  [tuple
     [bseq d (v3 * u3 + r3 + (v2 * u2 + r2) - r2 - r3 + u1 * v1);
           e (E alice (v3 * u3 + r3 + (v2 * u2 + r2)));
           e (E charlie v3);
           e (E bob v2);
           d r3; d r2; d u3; d u2; d u1; d v1; k dk_a];
     [bseq e (E charlie (v3 * u3 + r3));
           e (E bob (v2 * u2 + r2)); d v2; k dk_b];
     [bseq e (E charlie (v3 * u3 + r3 + (v2 * u2 + r2))); d v3; k dk_c]].

(* Protocol correctness: the final result S satisfies S = u1*v1 + u2*v2 + u3*v3 *)
Definition is_dsdp_zpq (trs : dsdp_tracesT) :=
  let '(s, u3', u2', u1', v1') :=
    if tnth trs 0 is Bseq [:: inl (inl s); _; _; _; _; _;
                           inl (inl u3'); inl (inl u2'); inl (inl u1');
                           inl (inl v1'); _] _
    then (s, u3', u2', u1', v1') else (0, 0, 0, 0, 0) in
  let '(v2') :=
    if tnth trs 1 is Bseq [:: _; _; inl (inl v2'); _] _
    then (v2') else (0) in
  let '(v3') :=
    if tnth trs 2 is Bseq [:: _; inl (inl v3'); _] _
    then (v3') else (0) in
  s = v3' * u3' + v2' * u2' + v1' * u1'.

Lemma dsdp_is_correct_zpq:
  is_dsdp_zpq dsdp_traces_zpq.
Proof. rewrite /is_dsdp_zpq /dsdp_traces_zpq /=. ring. Qed.

End dsdp_traces_zpq.

(******************************************************************************)
(* Trace-based Entropy Analysis                                               *)
(*                                                                            *)
(* These lemmas establish the connection between protocol traces and          *)
(* Alice's view for entropy calculations.                                     *)
(******************************************************************************)

Section trace_entropy_analysis.

(* Z/pqZ parameters *)
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Hypothesis prime_p : prime p.
Hypothesis prime_q : prime q.
Hypothesis coprime_pq : coprime p q.
Local Notation m := (p * q).
Local Notation msg := 'Z_m.

(* m = p * q > 1 since p, q >= 2 *)
Let m_gt1 : (1 < m)%N.
Proof.
have Hp2: (1 < p)%N by [].
have Hq2: (1 < q)%N by [].
by rewrite (ltn_trans Hp2) // -{1}(muln1 p) ltn_pmul2l // ltnS.
Qed.

Let card_msg : #|msg| = m.
Proof. by rewrite card_ord Zp_cast. Qed.

Let enc := enc party msg.
Let pkey := pkey party msg.
Let data := (msg + enc + pkey)%type.
Let d x : data := inl (inl x).
Let e x : data := inl (inr x).
Let k x : data := inr x.

Notation dsdp_traceT := (15.-bseq data).
Notation dsdp_tracesT := (3.-tuple dsdp_traceT).

Variable T : finType.
Variable P : R.-fdist T.

(* Random variable definitions *)
Variables (Dk_a : {RV P -> Alice.-key Dec msg})
          (Dk_b : {RV P -> Bob.-key Dec msg})
          (Dk_c : {RV P -> Charlie.-key Dec msg}).

Variables (V1 V2 V3 U1 U2 U3 R2 R3 : {RV P -> msg}).

Let VU2 : {RV P -> msg} := V2 \* U2.
Let VU3 : {RV P -> msg} := V3 \* U3.
Let D2  : {RV P -> msg} := VU2 \+ R2.
Let VU3R : {RV P -> msg} := VU3 \+ R3.
Let D3 : {RV P -> msg} := VU3R \+ D2.
Let S : {RV P -> msg} := D3 \- R2 \- R3 \+ U1 \* V1.

Let E_alice_d3 : {RV P -> Alice.-enc msg} := E' alice `o D3.
Let E_charlie_v3 : {RV P -> Charlie.-enc msg} := E' charlie `o V3.
Let E_bob_v2 : {RV P -> Bob.-enc msg} := E' bob `o V2.

(* Alice's inputs type *)
Let alice_inputsT := (Alice.-key Dec msg * msg * msg * msg *
  msg * msg * msg)%type.
Let AliceInputsView : {RV P -> alice_inputsT} := [% Dk_a, V1, U1, U2, U3, R2, R3].

(* Alice's full view type *)
Let alice_view_valuesT := (Alice.-key Dec msg * msg * msg * msg * msg * msg *
  msg * msg * Alice.-enc msg * Charlie.-enc msg * Bob.-enc msg)%type.

Let AliceView : {RV P -> alice_view_valuesT} :=
  [% Dk_a, S, V1, U1, U2, U3, R2, R3, E_alice_d3, E_charlie_v3, E_bob_v2].

(* Uncurry function for trace construction *)
Definition dsdp_uncurry_zpq (o: Alice.-key Dec msg * Bob.-key Dec msg *
  Charlie.-key Dec msg * msg * msg * msg * msg * msg * msg * msg * msg)
  : dsdp_tracesT :=
  let '(dk_a, dk_b, dk_c, v1, v2, v3, u1, u2, u3, r2, r3) := o in
  dsdp_traces_zpq dk_a.2 dk_b.2 dk_c.2 v1 v2 v3 u1 u2 u3 r2 r3.

(* Protocol trace as random variable *)
Definition DSDP_RV_zpq : {RV P -> dsdp_tracesT} :=
  dsdp_uncurry_zpq `o
  [% Dk_a, Dk_b, Dk_c, V1, V2, V3, U1, U2, U3, R2, R3].

(* Alice's trace: first component of protocol traces *)
Let AliceTraces : {RV P -> dsdp_traceT} :=
  (fun t => tnth t 0) `o DSDP_RV_zpq.

(* Reconstruct trace from Alice's view *)
Let AliceTraces_values_from_view
  (v : alice_view_valuesT) : 15.-bseq _ :=
    let '(dk_a, s, v1, u1, u2, u3, r2, r3,
      E_alice_d3, E_charlie_v3, E_bob_v2) := v in
    [bseq d s;
            e (E_alice_d3 : enc);
            e (E_charlie_v3 : enc);
            e (E_bob_v2 : enc);
            d r3; d r2; d u3; d u2; d u1; d v1; k (dk_a : pkey)].

(* AliceTraces is a function of AliceView: the protocol trace can be 
   reconstructed from Alice's view (her inputs and received messages). *)
Lemma AliceTraces_from_viewP :
  AliceTraces = AliceTraces_values_from_view `o AliceView.
Proof.
apply: boolp.funext => x /=.
rewrite /AliceTraces /DSDP_RV_zpq /comp_RV /dsdp_uncurry_zpq
        /dsdp_traces_zpq /=.
rewrite /AliceView /AliceTraces_values_from_view /=.
rewrite tnth0 /=.
by case: Dk_a => t.
Qed.

(* Extract Alice's view from trace *)
Local Definition AliceView_values_from_trace (xs : dsdp_traceT) :
  alice_view_valuesT :=
    let failtrace := (KeyOf Alice Dec 0,
                        0, 0, 0, 0, 0, 0, 0,
                        E' Alice 0, E' Charlie 0, E' Bob 0) in
    if xs is Bseq [:: inl (inl s);
           inl (inr E_alice_d3);
           inl (inr E_charlie_v3);
           inl (inr E_bob_v2);
           inl (inl r3); inl (inl r2); inl (inl u3);
           inl (inl u2); inl (inl u1); inl (inl v1); inr dk_a] _
    then 
         if (E_alice_d3, E_charlie_v3, E_bob_v2, dk_a) is
              ((Alice, d3), (Charlie, v3'), (Bob, v2'), (Alice, Dec, k_a)) then
            (KeyOf Alice Dec k_a, s, v1, u1, u2, u3, r2, r3,
               E' Alice d3, E' Charlie v3', E' Bob v2')
         else failtrace
    else failtrace.

(* AliceView_values_from_trace is left-inverse of AliceTraces_values_from_view.
   This establishes a bijection: AliceView ↔ AliceTraces (no information loss). *)
Lemma AliceView_values_from_traceP:
   cancel AliceTraces_values_from_view AliceView_values_from_trace.
Proof.
move => [] [] [] [] [] [] [] [] [] [] dk s v1' u1' u2' u3' r2' r3' a c b //=.
case: a => -[a' ma] /=.
case: c => -[c' mc] /=.
case: b => -[b' mb] /=.
case: dk => -[dk' mdk] /=.
by [].
Qed.

(* Conditional entropy equivalence: conditioning on AliceTraces equals 
   conditioning on AliceView. They carry the same information. *)
Lemma centropy_AliceTraces_AliceView (w : finType) (v : {RV P -> w}) :
  `H(v | AliceTraces ) = `H(v | AliceView ).
Proof.
simpl in *.
transitivity (`H(v | [% AliceTraces, AliceView])).
  have -> : AliceView = AliceView_values_from_trace `o AliceTraces.
    by apply: boolp.funext => x /= ;
       rewrite AliceTraces_from_viewP /comp_RV AliceView_values_from_traceP.
  by rewrite centropy_RV_contraction.
by rewrite AliceTraces_from_viewP centropyC centropy_RV_contraction.
Qed.

(******************************************************************************)
(* Bob's Trace-to-View Lifting                                                *)
(*                                                                            *)
(* Bob's trace: [e (E charlie (v3*u3+r3)); e (E bob (v2*u2+r2)); d v2; k dk_b] *)
(* Bob sees: encrypted value from Charlie (can't decrypt), his own encrypted  *)
(* computation, his private input v2, and his decryption key.                 *)
(******************************************************************************)

(* Bob's trace: element 1 of dsdp_traces *)
Let BobTraces : {RV P -> dsdp_traceT} :=
  (fun t => tnth t 1) `o DSDP_RV_zpq.

(* Encrypted values Bob receives *)
Let E_charlie_vur3 : {RV P -> Charlie.-enc msg} := E' charlie `o (VU3 \+ R3).
Let E_bob_d2 : {RV P -> Bob.-enc msg} := E' bob `o D2.

(* Bob's view type - what Bob knows:
   - His decryption key dk_b
   - His private input v2
   - Encrypted value from Charlie (can't decrypt): E_charlie(v3*u3+r3)
   - His own encrypted computation: E_bob(v2*u2+r2) *)
Let bob_view_valuesT := (Bob.-key Dec msg * msg * 
  Charlie.-enc msg * Bob.-enc msg)%type.

Let BobView : {RV P -> bob_view_valuesT} :=
  [% Dk_b, V2, E_charlie_vur3, E_bob_d2].

(* Reconstruct Bob's trace from his view *)
Definition BobTraces_values_from_view (v : bob_view_valuesT) : 15.-bseq data :=
  let '(dk_b, v2, e_charlie_vur3, e_bob_d2) := v in
  [bseq e (e_charlie_vur3 : enc); e (e_bob_d2 : enc); d v2; k (dk_b : pkey)].

(* BobTraces is a function of BobView *)
Lemma BobTraces_from_viewP :
  BobTraces = BobTraces_values_from_view `o BobView.
Proof.
apply: boolp.funext => x /=.
rewrite /BobTraces /DSDP_RV_zpq /comp_RV /dsdp_uncurry_zpq
        /dsdp_traces_zpq /=.
rewrite /BobView /BobTraces_values_from_view /=.
by case: Dk_b => t.
Qed.

(* Extract Bob's view from trace *)
Definition BobView_values_from_trace (xs : dsdp_traceT) : bob_view_valuesT :=
  let failtrace := (KeyOf Bob Dec 0, 0, E' Charlie 0, E' Bob 0) in
  if xs is Bseq [:: inl (inr e_charlie_vur3);
                    inl (inr e_bob_d2);
                    inl (inl v2);
                    inr dk_b] _
  then 
    if (e_charlie_vur3, e_bob_d2, dk_b) is
         ((Charlie, vur3), (Bob, d2), (Bob, Dec, k_b)) then
      (KeyOf Bob Dec k_b, v2, E' Charlie vur3, E' Bob d2)
    else failtrace
  else failtrace.

(* BobView_values_from_trace is left-inverse of BobTraces_values_from_view *)
Lemma BobView_values_from_traceP :
  cancel BobTraces_values_from_view BobView_values_from_trace.
Proof.
move => [] [] [] dk v2' ec eb /=.
case: ec => -[c' mc] /=.
case: eb => -[b' mb] /=.
case: dk => -[dk' mdk] /=.
by [].
Qed.

(* Conditional entropy equivalence for Bob: conditioning on BobTraces equals 
   conditioning on BobView. *)
Lemma centropy_BobTraces_BobView (w : finType) (v : {RV P -> w}) :
  `H(v | BobTraces) = `H(v | BobView).
Proof.
simpl in *.
transitivity (`H(v | [% BobTraces, BobView])).
  have -> : BobView = BobView_values_from_trace `o BobTraces.
    by apply: boolp.funext => x /=;
       rewrite BobTraces_from_viewP /comp_RV BobView_values_from_traceP.
  by rewrite centropy_RV_contraction.
by rewrite BobTraces_from_viewP centropyC centropy_RV_contraction.
Qed.

(******************************************************************************)
(* Charlie's Trace-to-View Lifting                                            *)
(*                                                                            *)
(* Charlie's trace: [e (E charlie (v3*u3+r3+(v2*u2+r2))); d v3; k dk_c]        *)
(* Charlie sees: encrypted aggregate (can decrypt), his private input v3,     *)
(* and his decryption key.                                                    *)
(******************************************************************************)

(* Charlie's trace: element 2 of dsdp_traces *)
Let CharlieTraces : {RV P -> dsdp_traceT} :=
  (fun t => tnth t 2) `o DSDP_RV_zpq.

(* Encrypted value Charlie receives - the aggregate D3 = v3*u3+r3+(v2*u2+r2) *)
Let E_charlie_d3 : {RV P -> Charlie.-enc msg} := E' charlie `o D3.

(* Charlie's view type - what Charlie knows:
   - His decryption key dk_c
   - His private input v3
   - Encrypted aggregate: E_charlie(v3*u3+r3+(v2*u2+r2)) *)
Let charlie_view_valuesT := (Charlie.-key Dec msg * msg * Charlie.-enc msg)%type.

Let CharlieView : {RV P -> charlie_view_valuesT} :=
  [% Dk_c, V3, E_charlie_d3].

(* Reconstruct Charlie's trace from his view *)
Definition CharlieTraces_values_from_view (v : charlie_view_valuesT) 
  : 15.-bseq data :=
  let '(dk_c, v3, e_charlie_d3) := v in
  [bseq e (e_charlie_d3 : enc); d v3; k (dk_c : pkey)].

(* CharlieTraces is a function of CharlieView *)
Lemma CharlieTraces_from_viewP :
  CharlieTraces = CharlieTraces_values_from_view `o CharlieView.
Proof.
apply: boolp.funext => x /=.
rewrite /CharlieTraces /DSDP_RV_zpq /comp_RV /dsdp_uncurry_zpq
        /dsdp_traces_zpq /=.
rewrite /CharlieView /CharlieTraces_values_from_view /=.
by case: Dk_c => t.
Qed.

(* Extract Charlie's view from trace *)
Definition CharlieView_values_from_trace (xs : dsdp_traceT) 
  : charlie_view_valuesT :=
  let failtrace := (KeyOf Charlie Dec 0, 0, E' Charlie 0) in
  if xs is Bseq [:: inl (inr e_charlie_d3);
                    inl (inl v3);
                    inr dk_c] _
  then 
    if (e_charlie_d3, dk_c) is
         ((Charlie, d3), (Charlie, Dec, k_c)) then
      (KeyOf Charlie Dec k_c, v3, E' Charlie d3)
    else failtrace
  else failtrace.

(* CharlieView_values_from_trace is left-inverse of CharlieTraces_values_from_view *)
Lemma CharlieView_values_from_traceP :
  cancel CharlieTraces_values_from_view CharlieView_values_from_trace.
Proof.
move => [] [] dk v3' ec /=.
case: ec => -[c' mc] /=.
case: dk => -[dk' mdk] /=.
by [].
Qed.

(* Conditional entropy equivalence for Charlie: conditioning on CharlieTraces 
   equals conditioning on CharlieView. *)
Lemma centropy_CharlieTraces_CharlieView (w : finType) (v : {RV P -> w}) :
  `H(v | CharlieTraces) = `H(v | CharlieView).
Proof.
simpl in *.
transitivity (`H(v | [% CharlieTraces, CharlieView])).
  have -> : CharlieView = CharlieView_values_from_trace `o CharlieTraces.
    by apply: boolp.funext => x /=;
       rewrite CharlieTraces_from_viewP /comp_RV CharlieView_values_from_traceP.
  by rewrite centropy_RV_contraction.
by rewrite CharlieTraces_from_viewP centropyC centropy_RV_contraction.
Qed.

End trace_entropy_analysis.
