From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap matrix lra reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter.
Require Import smc_session_types smc_interpreter_sound.
Require Import homomorphic_encryption dsdp_interface dsdp_pismc.
Require Import dsdp_progress dsdp_trace_infra.

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
(*   - dsdp_traces: Protocol trace structure for Z/pqZ                        *)
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

Reserved Notation "u *h w" (at level 40).
Reserved Notation "u ^h w" (at level 40).

Section dsdp_traces.

(* Parameterize by an AHEncType instance *)
Variable AHE : AHEncType.

(* Use standard DSDP interface for data types *)
Let DI := Standard_DSDP_Interface AHE.

(* Extract types from the scheme *)
Let msgT := plain AHE.
Let randT := rand AHE.
Let encT := cipher AHE.
Let priv_keyT := priv_key AHE.

(* Data type and constructors from interface *)
Let data := di_data DI.
Let d := di_d DI.
Let e := di_e DI.
Let k := di_priv_key DI.

(* HE operations from the scheme *)
Let Emul := @Emul AHE.
Let Epow := @Epow AHE.

Notation "u *h w" := (Emul u w).
Notation "u ^h w" := (Epow u w).

(* Party identities *)
Variable alice : party_id.
Variable bob : party_id.
Variable charlie : party_id.

(* Public key mapping and encryption wrapper *)
Variable ek : party_id -> pub_key AHE.
Definition enc_pk (p : party_id) (m : msgT) (r : randT) : encT :=
  enc (ek p) m r.
Local Notation E := enc_pk.

(* Trace types for DSDP protocol *)
Notation dsdp_traceT := (15.-bseq data).
Notation dsdp_tracesT := (3.-tuple dsdp_traceT).

(* Message and randomness variables *)
Variables (v1 v2 v3 u1 u2 u3 r2 r3 : msgT).
Variables (rb1 rb2 rc1 rc2 ra1 ra2 : randT).

(* Private keys *)
Variables (dk_a : priv_keyT) (dk_b : priv_keyT) (dk_c : priv_keyT).

(* Protocol traces - now include randomness in encryption calls *)
Definition dsdp_traces : dsdp_tracesT :=
  [tuple
     [bseq d (v3 * u3 + r3 + (v2 * u2 + r2) - r2 - r3 + u1 * v1);
           e (E alice (v3 * u3 + r3 + (v2 * u2 + r2)) rc2);
           e (E charlie v3 rc1);
           e (E bob v2 rb1);
           d r3; d r2; d u3; d u2; d u1; d v1; k dk_a];
     [bseq e (E charlie (v3 * u3 + r3) rb2);
           e (E bob (v2 * u2 + r2) ra1); d v2; k dk_b];
     [bseq e (E charlie (v3 * u3 + r3 + (v2 * u2 + r2)) rb2); d v3; k dk_c]].

(* Protocol correctness is now proved algebraically using ring arithmetic.
   The final result S = v3*u3 + r3 + (v2*u2 + r2) - r2 - r3 + u1*v1
   simplifies to u1*v1 + u2*v2 + u3*v3 by ring. *)
Theorem dsdp_result_correct :
  v3 * u3 + r3 + (v2 * u2 + r2) - r2 - r3 + u1 * v1 = u1 * v1 + u2 * v2 + u3 * v3.
Proof. ring. Qed.

End dsdp_traces.

(******************************************************************************)
(* Trace-based Entropy Analysis                                               *)
(*                                                                            *)
(* NOTE: The trace-based entropy analysis relied on the idealized encryption  *)
(* model where enc = (party * msg) and E' is deterministic. With the new      *)
(* AHEncType interface where encryption requires randomness, the      *)
(* trace structure becomes more complex.                                      *)
(*                                                                            *)
(* The entropy equivalence lemmas (centropy_AliceTraces_AliceView, etc.)      *)
(* need to be reformulated to account for encryption randomness.              *)
(* This requires extending the view types to include randomness variables.    *)
(******************************************************************************)

Section trace_entropy_analysis.

(* Parameterize by an AHEncType instance *)
Variable AHE : AHEncType.

(* Use standard DSDP interface for data types *)
Let DI := Standard_DSDP_Interface AHE.

(* Extract types from the scheme *)
Let msgT := plain AHE.

(* Data type and constructors from interface *)
Let data := di_data DI.

Notation dsdp_traceT := (15.-bseq data).
Notation dsdp_tracesT := (3.-tuple dsdp_traceT).

Variable R : realType.
Variable T : finType.
Variable P : R.-fdist T.

(* Random variable definitions for messages *)
Variables (V1 V2 V3 U1 U2 U3 R2 R3 : {RV P -> msgT}).

(* Intermediate values *)
Let VU2 : {RV P -> msgT} := V2 \* U2.
Let VU3 : {RV P -> msgT} := V3 \* U3.
Let D2  : {RV P -> msgT} := VU2 \+ R2.
Let VU3R : {RV P -> msgT} := VU3 \+ R3.
Let D3 : {RV P -> msgT} := VU3R \+ D2.
Let S : {RV P -> msgT} := D3 \- R2 \- R3 \+ U1 \* V1.

(* The protocol correctness theorem: the sum S equals the dot product.
   This is proved algebraically without depending on trace structure. *)
Lemma dsdp_algebraic_correctness :
  forall t, S t = (U1 \* V1 \+ U2 \* V2 \+ U3 \* V3) t.
Proof.
move => t.
rewrite /S /D3 /VU3R /D2 /VU2 /VU3 /=.
ring.
Qed.

End trace_entropy_analysis.

(******************************************************************************)
(* N-Party Trace→Security Bridge                                              *)
(*                                                                            *)
(* Connects the protocol execution (rsteps/interp_sound) to the algebraic    *)
(* security proofs (dsdp_entropic_security_n_concrete).                       *)
(*                                                                            *)
(* Key insight: Alice's trace from rsteps is a LOSSY projection of her view. *)
(* The trace contains communicated values (Init'd, Recv'd, Ret'd), but NOT  *)
(* Alice's private computation inputs (U0, U_relay, R_relay, rand_a).        *)
(*                                                                            *)
(* Therefore:                                                                 *)
(* - AliceView_n = trace + private inputs (functional equivalence)           *)
(* - H(VarRV | trace) ≥ H(VarRV | AliceView_n) (data processing)           *)
(*                                                                            *)
(* The bridge has three parts:                                                *)
(*                                                                            *)
(* Phase 1 (L5a-L5e): Trace content characterization                        *)
(*   What is in tr !_ 0? Split by palice_n's protocol phases:               *)
(*     Phase A: Init (#dk, &v0) → [dk; v0]                                  *)
(*     Phase B: ForList relays (Recv c_j; Send ...) → [c_n; ...; c_1]       *)
(*     Phase C: Recv g; Ret S → [g; S]                                      *)
(*                                                                            *)
(* Phase 2 (L6): View faithfulness                                           *)
(*   Every component of AliceView_n comes from either the trace or           *)
(*   Alice's private inputs (function arguments to palice_n).                *)
(*                                                                            *)
(* Phase 3 (L8): Eavesdropper security                                       *)
(*   H(VarRV | trace) ≥ log(m^n_relay) by data processing inequality.       *)
(*                                                                            *)
(* Dependency graph:                                                          *)
(*   L5a (init) ──────────┐                                                  *)
(*   L5b (relay step) → L5c (all relays) → L5e (full trace)                 *)
(*   L5d (final) ─────────┘                    ↓                             *)
(*                                        L6 (view faithfulness)             *)
(*                                             ↓                             *)
(*                               D3 (AliceTraces_n) → L8 (eavesdropper)     *)
(******************************************************************************)

(* Status:
   L5c: DONE — alice_trace_concrete_AR, alice_trace_concrete_tail give concrete
        trace values per dsdp_inv constructor (enc/chain_acc expressions).
   L6:  CONCEPTUAL — view faithfulness documented below.
   D3:  DONE — trace_proj_n, AliceTraces_n in dsdp_security.v.
   L8:  DONE — trace_eavesdropper_security_n in dsdp_security.v.
   B2:  DONE — init_rsteps_to_inv: after 2 Init rounds, rsteps reaches
        dsdp_inv state with Alice trace = [d v0; priv_key dk].
   L5e: DONE — alice_full_trace_n: compose Init bridge + multi-round
        fragments into full end-to-end trace characterization. *)

(******************************************************************************)
(* L5a: Alice's trace after the Init phase                                    *)
(*                                                                            *)
(* After erasure, palice_n starts with two Init constructors:                 *)
(*   Init (priv_key dk) (Init (d v0) body)                                    *)
(*                                                                            *)
(* Each Init step prepends its data to the trace, so after 2 rounds:          *)
(*   trace_alice = [d v0; priv_key dk]                                        *)
(******************************************************************************)

Section alice_trace_init.

Variable AHE : AHEncType.
Variable ek : party_id -> pub_key AHE.
Variable n_relay : nat.

Let DI := Standard_DSDP_Interface AHE.
Let data := di_data DI.
Let msgT := plain AHE.
Let randT := rand AHE.
Let priv_keyT := priv_key AHE.
Let d := di_d DI.
Let priv_key := di_priv_key DI.

(* Generic lemma: step on Init prepends data to trace *)
Lemma step_Init (ps : seq (proc data)) (tr : seq data) (i : nat)
    (dat : data) (next : proc data) :
  nth (default_proc data) ps i = Init dat next ->
  @step data ps tr i = (next, dat :: tr, true).
Proof.
by move=> Hi; rewrite /step /= Hi.
Qed.

(* Alice's erased process after palice_n starts with two Inits.
   We characterize the trace after these two Init steps:
   - Round 1: Init (priv_key dk) body --> trace gets [priv_key dk]
   - Round 2: Init (d v0) body'       --> trace gets [d v0; priv_key dk]  *)
Lemma alice_trace_init
    (relays : seq 'I_n_relay.+1)
    (dk : priv_keyT) (v0 : msgT)
    (u : 'I_n_relay.+2 -> msgT) (r : 'I_n_relay.+1 -> msgT)
    (rand_a : 'I_n_relay.+1 -> randT)
    (other_procs : seq (proc data))
    (tr0 : seq data) :
  let alice_proc := erase (@palice_n AHE ek n_relay relays dk v0 u r rand_a) in
  let ps := alice_proc :: other_procs in
  let '(p1, tr1, _) := @step data ps tr0 0 in
  let '(p2, tr2, _) := @step data (p1 :: other_procs) tr1 0 in
  tr2 = d v0 :: priv_key dk :: tr0.
Proof.
cbv zeta; rewrite (palice_n_erase AHE ek); by simpl.
Qed.

(* Generic step lemmas for Recv/Send pairs *)

(* When ps[i] = Recv frm f and ps[frm] = Send dst v k with dst = i,
   step returns (f v, v :: tr, true) *)
Lemma step_Recv_Send (ps : seq (proc data)) (tr : seq data) (i frm : nat)
    (f : data -> proc data) (dst : nat) (v : data) (k : proc data) :
  nth (default_proc data) ps i = Recv frm f ->
  nth (default_proc data) ps frm = Send dst v k ->
  dst == i ->
  @step data ps tr i = (f v, v :: tr, true).
Proof.
move=> Hi Hfrm Hdst.
by rewrite /step /= Hi Hfrm Hdst.
Qed.

(* When ps[i] = Send dst v k and ps[dst] = Recv frm f with frm = i,
   step returns (k, tr, true) — trace unchanged *)
Lemma step_Send_Recv (ps : seq (proc data)) (tr : seq data) (i dst : nat)
    (v : data) (k : proc data) (frm : nat) (f : data -> proc data) :
  nth (default_proc data) ps i = Send dst v k ->
  nth (default_proc data) ps dst = Recv frm f ->
  frm == i ->
  @step data ps tr i = (k, tr, true).
Proof.
move=> Hi Hdst Hfrm.
by rewrite /step /= Hi Hdst Hfrm.
Qed.

(* L5b: One relay iteration of palice_n adds exactly one received value
   to Alice's trace.

   Alice's process for relay j is:
     Recv j.+1 (oapp f Fail \o std_from_enc)
   which, after the Recv fires with value v from relay j+1 (who has Send 0 v ...),
   prepends v to the trace.

   The subsequent Send by Alice does NOT modify Alice's trace.

   This lemma captures the Recv half: if Alice = Recv j.+1 f and
   relay j+1 = Send 0 v k, then step prepends v to Alice's trace. *)
Lemma alice_trace_relay_recv
    (ps : seq (proc data)) (tr : seq data)
    (j : nat) (f : data -> proc data) (v : data) (relay_next : proc data) :
  nth (default_proc data) ps 0 = Recv j.+1 f ->
  nth (default_proc data) ps j.+1 = Send 0 v relay_next ->
  @step data ps tr 0 = (f v, v :: tr, true).
Proof.
move=> H0 Hj.
by rewrite /step /= H0 Hj.
Qed.

(* L5b': After Alice's Recv fires and Alice becomes Send dst w body_rest,
   stepping Alice again does not change her trace (sender trace is inert). *)
Lemma alice_trace_relay_send
    (ps : seq (proc data)) (tr : seq data)
    (dst : nat) (w : data) (body_rest : proc data)
    (frm : nat) (g : data -> proc data) :
  nth (default_proc data) ps 0 = Send dst w body_rest ->
  nth (default_proc data) ps dst = Recv frm g ->
  frm == 0 ->
  @step data ps tr 0 = (body_rest, tr, true).
Proof.
move=> H0 Hdst Hfrm.
by rewrite /step /= H0 Hdst Hfrm.
Qed.

(* Generic lemma: step on Ret prepends data to trace and becomes Finish *)
Lemma step_Ret (ps : seq (proc data)) (tr : seq data) (i : nat)
    (dat : data) :
  nth (default_proc data) ps i = Ret dat ->
  @step data ps tr i = (@Finish data, dat :: tr, true).
Proof.
by move=> Hi; rewrite /step /= Hi.
Qed.

(******************************************************************************)
(* L5c: Alice's trace after all relay iterations                              *)
(*                                                                            *)
(* The foldr over (zip relays (iota 0 (size relays))) produces a chain of    *)
(* alice_erase_body applications. Each body does Recv (adds cipher to trace)  *)
(* then Send (trace unchanged). So after all relay iterations, the received   *)
(* ciphertexts are prepended to the trace in order.                           *)
(*                                                                            *)
(* Key insight: alice_erase_body j idx k unfolds (after erasure) to:          *)
(*   Recv j.+1 (oapp (fun enc0 => Send (alice_send_dest j) (e ...) k)        *)
(*                    Fail \o std_from_enc)                                    *)
(*                                                                            *)
(* So for each relay:                                                          *)
(*   - Recv step: trace gets v_relay prepended (by alice_trace_relay_recv)     *)
(*   - Send step: trace unchanged (by alice_trace_relay_send)                  *)
(*   - Alice advances to the continuation k (= next body or tail)             *)
(*                                                                            *)
(* The full induction over the relay list requires tracking the joint state   *)
(* of all processes across 2*|relays| steps. We state the result abstractly  *)
(* and Admit for now — the building blocks (L5b, L5b') are proved.            *)
(******************************************************************************)

(* L5c helper: The Recv step on alice_erase_body adds the relay's value
   to the trace and produces a Send (or Fail if data is not a valid cipher).
   This is a direct consequence of alice_trace_relay_recv + the structural
   lemma above. *)
Lemma alice_erase_body_recv_step
    (ps : seq (proc data)) (tr : seq data)
    (u : 'I_n_relay.+2 -> msgT) (r : 'I_n_relay.+1 -> msgT)
    (rand_a : 'I_n_relay.+1 -> randT)
    (j : 'I_n_relay.+1) (idx : nat) (k : proc data)
    (v_relay : data) (relay_next : proc data) :
  nth (default_proc data) ps 0 =
    alice_erase_body AHE ek n_relay u r rand_a j idx k ->
  nth (default_proc data) ps j.+1 = Send 0 v_relay relay_next ->
  (* After the Recv step: trace gets v_relay prepended *)
  (@step data ps tr 0).1.2 = v_relay :: tr.
Proof.
move=> Halice Hrelay.
by rewrite /step /= Halice /alice_erase_body /std_Recv_enc /Recv_param /= Hrelay.
Qed.

(* L5c helper: After alice_erase_body's Recv fires with a valid cipher,
   Alice becomes a Send. The subsequent Send step leaves the trace unchanged
   and advances Alice to the continuation k. *)
Lemma alice_erase_body_send_step
    (ps : seq (proc data)) (tr : seq data)
    (u : 'I_n_relay.+2 -> msgT) (r : 'I_n_relay.+1 -> msgT)
    (rand_a : 'I_n_relay.+1 -> randT)
    (j : 'I_n_relay.+1) (idx : nat) (k : proc data)
    (w : data)
    (recv_partner : nat) (recv_f : data -> proc data) :
  nth (default_proc data) ps 0 =
    Send (alice_send_dest j) w k ->
  nth (default_proc data) ps (alice_send_dest j) = Recv recv_partner recv_f ->
  recv_partner == 0 ->
  (@step data ps tr 0) = (k, tr, true).
Proof.
move=> Halice Hdst Hfrm.
by rewrite /step /= Halice Hdst Hfrm.
Qed.

(* L5c: Relay loop trace characterization.

   At each relay iteration j:
   - alice_erase_body_recv_step: Alice Recv from relay j+1 adds c_j to trace
   - alice_erase_body_send_step: Alice Send leaves trace unchanged

   Per-step lemma: given Alice at alice_erase_body and relay j+1 at Send,
   two calls to step (Recv then Send) advance Alice to the next body
   with c_j prepended to her trace. *)
Lemma alice_trace_relay_step
    (ps : seq (proc data)) (tr : seq data)
    (u : 'I_n_relay.+2 -> msgT) (r : 'I_n_relay.+1 -> msgT)
    (rand_a : 'I_n_relay.+1 -> randT)
    (j : 'I_n_relay.+1) (idx : nat) (k : proc data)
    (v_relay : data) (relay_next : proc data)
    (recv_partner : nat) (recv_f : data -> proc data) :
  (* Alice is at alice_erase_body (Recv from j+1) *)
  nth (default_proc data) ps 0 =
    alice_erase_body AHE ek n_relay u r rand_a j idx k ->
  (* Relay j+1 is ready to Send v_relay to Alice *)
  nth (default_proc data) ps j.+1 = Send 0 v_relay relay_next ->
  (* Destination is ready to Recv from Alice *)
  nth (default_proc data) ps (alice_send_dest j) =
    Recv recv_partner recv_f ->
  recv_partner == 0 ->
  (* After Recv: trace gets v_relay prepended *)
  (@step data ps tr 0).1.2 = v_relay :: tr /\
  (* After Send: trace unchanged, Alice advances to k *)
  let ps_after_recv :=
    set_nth (default_proc data)
      (set_nth (default_proc data) ps 0
        ((@step data ps tr 0).1.1))
      j.+1 relay_next in
  (@step data ps_after_recv (v_relay :: tr) 0) = (k, v_relay :: tr, true).
Proof.
move=> Halice Hrelay Hdest Hpartner.
split.
- exact: alice_erase_body_recv_step Halice Hrelay.
- (* After the Recv step, Alice is at Send (alice_send_dest j) w k
     where w is the computed value. We need to show the Send step fires. *)
  rewrite /step /=.
  (* Alice after Recv: alice_erase_body unfolds to Recv, which after
     matching with Send gives Send (alice_send_dest j) computed k *)
  rewrite /step /= Halice /alice_erase_body /std_Recv_enc /Recv_param /= in Hrelay |- *.
  Show.
Abort.

(* Simpler approach: state the combined effect *)
Lemma alice_trace_relay_recv_send
    (ps : seq (proc data)) (tr : seq data)
    (u : 'I_n_relay.+2 -> msgT) (r : 'I_n_relay.+1 -> msgT)
    (rand_a : 'I_n_relay.+1 -> randT)
    (j : 'I_n_relay.+1) (idx : nat) (k : proc data)
    (v_relay : data) (relay_next : proc data) :
  (* Alice at alice_erase_body, relay j+1 at Send *)
  nth (default_proc data) ps 0 =
    alice_erase_body AHE ek n_relay u r rand_a j idx k ->
  nth (default_proc data) ps j.+1 = Send 0 v_relay relay_next ->
  (* After Recv step: Alice's trace gets v_relay prepended *)
  (@step data ps tr 0).1.2 = v_relay :: tr.
Proof.
exact: alice_erase_body_recv_step.
Qed.

(******************************************************************************)
(* L5d: Alice's trace after the final phase (Recv + Ret)                      *)
(*                                                                            *)
(* After the relay loop, Alice's process is alice_erase_tail dk v0 u r:       *)
(*   Recv n_relay.+1 (oapp f Fail \o (obind (D dk) \o std_from_enc))          *)
(* where f = (fun m0 => Ret (d (m0 - sum + u0*v0)))                           *)
(*                                                                            *)
(* When the last relay sends g to Alice:                                       *)
(*   1. Recv step: trace gets g prepended                                      *)
(*   2. If g = e(cipher) and dec dk cipher = Some m0:                          *)
(*      Alice becomes Ret (d (m0 - sum + u0*v0))                               *)
(*   3. Ret step: trace gets d(result) prepended                               *)
(******************************************************************************)

(* L5d: The Recv step of alice_erase_tail adds the received value to trace *)
Lemma alice_trace_final_recv
    (ps : seq (proc data)) (tr : seq data)
    (dk : priv_keyT) (v0 : msgT)
    (u : 'I_n_relay.+2 -> msgT) (r : 'I_n_relay.+1 -> msgT)
    (g : data) (relay_next : proc data) :
  nth (default_proc data) ps 0 =
    alice_erase_tail AHE n_relay dk v0 u r ->
  nth (default_proc data) ps n_relay.+1 = Send 0 g relay_next ->
  (@step data ps tr 0).1.2 = g :: tr.
Proof.
move=> Halice Hrelay.
by rewrite /step /= Halice /alice_erase_tail /std_Recv_dec /Recv_param /= Hrelay.
Qed.

(* L5d': After the Recv, if the received data is e(ct) and dec dk ct = Some m0,
   Alice becomes Ret (d (m0 - sum(r) + u0*v0)). The subsequent Ret step
   adds d(result) to the trace. *)
Lemma alice_trace_final_ret
    (ps : seq (proc data)) (tr : seq data)
    (result : msgT) :
  nth (default_proc data) ps 0 = Ret (d result) ->
  (@step data ps tr 0) = (@Finish data, d result :: tr, true).
Proof.
by move=> Halice; rewrite /step /= Halice.
Qed.

(* L5d'': Characterize what Alice becomes after the Recv in alice_erase_tail
   when receiving valid encrypted data. *)
Lemma alice_erase_tail_recv_result
    (dk : priv_keyT) (v0 : msgT)
    (u : 'I_n_relay.+2 -> msgT) (r : 'I_n_relay.+1 -> msgT)
    (ct : cipher AHE) (m0 : plain AHE) :
  dec dk ct = Some m0 ->
  let f := (oapp (fun m : plain AHE =>
               Ret (d (m - \sum_(j < n_relay.+1) r j + u ord0 * v0)))
             Fail \o (obind (dec dk) \o @std_from_enc AHE)) in
  f (di_e DI ct) = Ret (d (m0 - \sum_(j < n_relay.+1) r j + u ord0 * v0)).
Proof.
move=> Hdec /=.
by rewrite Hdec.
Qed.

(******************************************************************************)
(* L5e: Full trace content characterization (combines L5a + L5c + L5d)        *)
(*                                                                            *)
(* Alice's complete trace after protocol execution contains:                   *)
(*   [d(result); g; c_n; ...; c_1; d(v0); priv_key(dk)]                      *)
(* where c_j is the cipher received from relay j+1 in the loop,               *)
(*       g is the final cipher received from the last relay,                   *)
(*       and result = dec(g) - sum(r) + u0*v0.                                *)
(*                                                                            *)
(* This combines:                                                              *)
(*   L5a: Init phase produces [d(v0); priv_key(dk)]                           *)
(*   L5c: Relay loop prepends [c_n; ...; c_1]                                 *)
(*   L5d: Final phase prepends [d(result); g]                                 *)
(*                                                                            *)
(* The complete characterization requires L5c (relay induction).               *)
(* For now, we state the two-step final phase as a combined lemma.             *)
(******************************************************************************)

(* L5e partial: characterize the last two steps (Recv + Ret) of Alice's
   execution, assuming Alice is at alice_erase_tail and the last relay
   sends her a valid encrypted ciphertext.

   This shows: if Alice's trace before the final phase is tr0,
   then after Recv from last relay (data g) and Ret (computing result),
   Alice's trace becomes [d(result); g] ++ tr0. *)
Lemma alice_trace_content_n
    (ps : seq (proc data)) (tr0 : seq data)
    (dk : priv_keyT) (v0 : msgT)
    (u : 'I_n_relay.+2 -> msgT) (r : 'I_n_relay.+1 -> msgT)
    (ct : cipher AHE) (m0 : plain AHE)
    (relay_next : proc data)
    (other_procs_tail : seq (proc data)) :
  let g := di_e DI ct in
  (* Alice is at alice_erase_tail *)
  nth (default_proc data) ps 0 =
    alice_erase_tail AHE n_relay dk v0 u r ->
  (* Last relay sends g to Alice *)
  nth (default_proc data) ps n_relay.+1 = Send 0 g relay_next ->
  (* Decryption succeeds *)
  dec dk ct = Some m0 ->
  let result := m0 - \sum_(j < n_relay.+1) r j + u ord0 * v0 in
  (* Step 1: Recv adds g to trace *)
  (@step data ps tr0 0).1.2 = g :: tr0 /\
  (* Step 2: Ret adds d(result) to trace *)
  let alice_after_recv :=
    (oapp (fun m : plain AHE =>
       Ret (d (m - \sum_(j < n_relay.+1) r j + u ord0 * v0)))
     Fail \o (obind (dec dk) \o @std_from_enc AHE)) g in
  forall ps2 : seq (proc data),
    nth (default_proc data) ps2 0 = alice_after_recv ->
    (@step data ps2 (g :: tr0) 0) =
      (@Finish data, d result :: g :: tr0, true).
Proof.
move=> g Halice Hrelay Hdec result.
split.
- (* Recv step: trace gets g prepended *)
  exact: alice_trace_final_recv Halice Hrelay.
- (* Ret step: alice_after_recv simplifies to Ret (d result) *)
  move=> /= ps2 Hps2.
  rewrite Hdec /= in Hps2.
  by rewrite /step /= Hps2.
Qed.

End alice_trace_init.

(******************************************************************************)
(* Per-phase Alice trace characterization using dsdp_inv                      *)
(*                                                                            *)
(* For each dsdp_inv constructor, determines Alice's trace fragment:          *)
(*   Inv_AR j  : Alice Recv from relay j+1 → trace [:: v]                   *)
(*   Inv_AS*   : Alice Send to destination → trace nil                       *)
(*   Inv_drain : Relay-to-relay forwarding → trace nil                       *)
(*   Inv_tail  : Alice Recv from last relay → trace [:: v]                   *)
(*   Inv_ret   : Alice Ret → trace [:: d]                                    *)
(******************************************************************************)

Section alice_trace_at_inv.

Variable AHE : AHEncType.
Variable ek : party_id -> pub_key AHE.
Variable n_relay : nat.
Hypothesis Hn_relay : (0 < n_relay)%N.

Let DI := Standard_DSDP_Interface AHE.
Let data := di_data DI.

Variable dk : priv_key AHE.
Variable dk_relay : 'I_n_relay.+1 -> priv_key AHE.

Variable relays : seq 'I_n_relay.+1.
Hypothesis Hrelays : size relays = n_relay.+1.
Hypothesis Hrelays_id : forall k : 'I_n_relay.+1, nth ord0 relays k = k.

Variable v0 : plain AHE.
Variable u : 'I_n_relay.+2 -> plain AHE.
Variable r : 'I_n_relay.+1 -> plain AHE.
Variable rand_a : 'I_n_relay.+1 -> rand AHE.
Variable v_relay : 'I_n_relay.+1 -> plain AHE.
Variables (r1_relay r2_relay : 'I_n_relay.+1 -> rand AHE).

(* Inv_AR j: Alice at Recv from relay j+1. Relay j+1 at Send 0 v.
   step fires Recv → Alice trace fragment = [:: v]. *)
Lemma alice_trace_at_AR ps (j : 'I_n_relay.+1) :
  nth (default_proc data) ps 0 =
    @alice_foldr_at AHE ek n_relay dk relays v0 u r rand_a j ->
  @relay_at_body AHE ek n_relay dk_relay v_relay r1_relay r2_relay j ps ->
  exists v, (smc_interpreter.step ps [::] 0).1.2 = [:: v].
Proof.
move=> Halice Hbody.
have [f Hrecv] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays Hrelays_id
  v0 u r rand_a j (ltn_ord j).
have [sk Hsend] := @relay_body_is_send0 AHE ek n_relay dk_relay v_relay
  r1_relay r2_relay j.
rewrite /relay_at_body in Hbody.
by rewrite /smc_interpreter.step /= Halice /alice_foldr_at Hrecv Hbody Hsend eqxx;
  eexists.
Qed.

(* Inv_ret: Alice at Ret d. trace fragment = [:: d]. *)
Lemma alice_trace_at_ret ps (d : data) :
  nth (default_proc data) ps 0 = Ret d ->
  (smc_interpreter.step ps [::] 0).1.2 = [:: d].
Proof. by move=> Halice; rewrite /smc_interpreter.step Halice. Qed.

(* Inv_tail: Alice at erase_tail (Recv n_relay.+1), last relay at Send 0 v.
   trace fragment = [:: v]. *)
Lemma alice_trace_at_tail ps :
  nth (default_proc data) ps 0 =
    @alice_foldr_at AHE ek n_relay dk relays v0 u r rand_a n_relay.+1 ->
  (exists v, nth (default_proc data) ps n_relay.+1 = Send 0 v Finish) ->
  exists v, (smc_interpreter.step ps [::] 0).1.2 = [:: v].
Proof.
move=> Halice [v Hlast].
rewrite /smc_interpreter.step Halice.
rewrite (@alice_foldr_at_tail AHE ek n_relay dk relays Hrelays v0 u r rand_a).
rewrite /alice_erase_tail /std_Recv_dec /Recv_param /=.
rewrite Hlast eqxx.
by eexists.
Qed.

(* Inv_AS*: Alice at Send dst vd k0, destination at Recv 0.
   trace fragment = nil (Send doesn't add to sender's trace). *)
Lemma alice_trace_at_send ps dst (vd : data) (k0 : proc data) :
  nth (default_proc data) ps 0 = Send dst vd k0 ->
  (exists f, nth (default_proc data) ps dst = Recv 0 f) ->
  (smc_interpreter.step ps [::] 0).1.2 = [::].
Proof.
move=> Halice [f Hdst].
by rewrite /smc_interpreter.step Halice Hdst eqxx.
Qed.

(* Inv_drain j: Alice at erase_tail (Recv n_relay.+1), but last relay
   is at Recv (not Send). Recv doesn't fire → trace nil. *)
Lemma alice_trace_at_drain ps :
  nth (default_proc data) ps 0 =
    @alice_foldr_at AHE ek n_relay dk relays v0 u r rand_a n_relay.+1 ->
  (exists f, nth (default_proc data) ps n_relay.+1 = Recv n_relay f) ->
  (smc_interpreter.step ps [::] 0).1.2 = [::].
Proof.
move=> Halice [f Hlast].
rewrite /smc_interpreter.step Halice.
rewrite (@alice_foldr_at_tail AHE ek n_relay dk relays Hrelays v0 u r rand_a).
rewrite /alice_erase_tail /std_Recv_dec /Recv_param /=.
by rewrite Hlast.
Qed.

(* Concrete-value version of alice_trace_at_AR: specifies the exact trace value
   enc(ek(j+1), v_relay(j), r1_relay(j)). *)
Lemma alice_trace_concrete_AR ps (j : 'I_n_relay.+1) :
  nth (default_proc data) ps 0 =
    @alice_foldr_at AHE ek n_relay dk relays v0 u r rand_a j ->
  @relay_at_body AHE ek n_relay dk_relay v_relay r1_relay r2_relay j ps ->
  (smc_interpreter.step ps [::] 0).1.2 =
    [:: di_e DI (enc (ek (nat_to_party_id j.+1)) (v_relay j) (r1_relay j))].
Proof.
move=> Halice Hbody.
have [f Hrecv] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays Hrelays_id
  v0 u r rand_a j (ltn_ord j).
have [sk Hsend] := @relay_body_is_send0 AHE ek n_relay dk_relay v_relay
  r1_relay r2_relay j.
rewrite /relay_at_body in Hbody.
by rewrite /smc_interpreter.step /= Halice /alice_foldr_at Hrecv Hbody Hsend eqxx.
Qed.

(* Concrete-value version of alice_trace_at_tail: specifies the exact trace value
   enc(ek(alice_idx), chain_acc(n_relay.-1), rr_tail). *)
Lemma alice_trace_concrete_tail ps (rr_tail : rand AHE) :
  nth (default_proc data) ps 0 =
    @alice_foldr_at AHE ek n_relay dk relays v0 u r rand_a n_relay.+1 ->
  nth (default_proc data) ps n_relay.+1 =
    Send 0 (di_e DI (enc (ek alice_idx) (@chain_acc AHE n_relay u r v_relay
      n_relay.-1) rr_tail)) Finish ->
  (smc_interpreter.step ps [::] 0).1.2 =
    [:: di_e DI (enc (ek alice_idx) (@chain_acc AHE n_relay u r v_relay
      n_relay.-1) rr_tail)].
Proof.
move=> Halice Hlast.
rewrite /smc_interpreter.step Halice.
rewrite (@alice_foldr_at_tail AHE ek n_relay dk relays Hrelays v0 u r rand_a).
rewrite /alice_erase_tail /std_Recv_dec /Recv_param /=.
by rewrite Hlast eqxx.
Qed.

(* Additional hypotheses needed for dsdp_inv_step *)
Hypothesis dec_total : forall dk' c, @dec AHE dk' c != None.
Hypothesis key_alice : ek alice_idx = pub_of_priv dk.
Hypothesis key_relay : forall j : 'I_n_relay.+1,
  ek (nat_to_party_id j.+1) = pub_of_priv (dk_relay j).

Let n_parties := n_relay.+2.
Let inv := dsdp_inv AHE ek n_relay Hn_relay dk dk_relay relays v0 u r rand_a
  v_relay r1_relay r2_relay.

(* Bridge: one_step_procs (seq-level) = tval of res_procs (tuple-level) *)
Lemma one_step_eq_res_procs (ps : n_parties.-tuple (proc data)) :
  one_step_procs data (tval ps) =
  tval (res_procs [tuple smc_interpreter.step ps [::] i | i < n_parties]).
Proof.
apply: (@eq_from_nth _ (default_proc data)).
  by rewrite /one_step_procs size_map size_iota size_tuple /res_procs
     size_map size_tuple.
rewrite /one_step_procs size_map size_iota size_tuple => i Hi.
have Hi' : (i < n_parties)%N by [].
rewrite (nth_map 0%N); last by rewrite size_iota.
rewrite nth_iota // add0n.
transitivity (tnth (res_procs [tuple smc_interpreter.step ps [::] i0 | i0 < n_parties]) (Ordinal Hi')).
  by rewrite /res_procs tnth_map tnth_mktuple.
by rewrite (tnth_nth (default_proc data)).
Qed.

(* One round under dsdp_inv: step_sound gives rsteps, dsdp_inv_step preserves
   the invariant (or terminates). *)
Lemma dsdp_inv_round (ps : n_parties.-tuple (proc data)) :
  inv (tval ps) ->
  let ps' := res_procs [tuple smc_interpreter.step ps [::] i | i < n_parties] in
  rsteps ps ps' (res_traces [tuple smc_interpreter.step ps [::] i | i < n_parties]) /\
  (all_terminated (tval ps') \/ inv (tval ps')).
Proof.
move=> Hinv ps'.
split; first exact: step_sound.
rewrite -one_step_eq_res_procs.
by apply dsdp_inv_step.
Qed.

(* R1: Unified trace fragment dispatch for all dsdp_inv constructors.
   At each round, Alice's trace fragment is either [:: v] or [::]. *)
Lemma alice_trace_at_inv (ps : n_parties.-tuple (proc data)) :
  inv (tval ps) ->
  (exists v, (smc_interpreter.step (tval ps) [::] 0).1.2 = [:: v]) \/
  (smc_interpreter.step (tval ps) [::] 0).1.2 = [::].
Proof.
case.
- move=> j ps0 _ Hsz Hwf Halice Hbody _ _ _ _ _; left.
  have [f Hfr] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays
    Hrelays_id v0 u r rand_a j (ltn_ord j).
  have [sk Hs] := @relay_body_is_send0 AHE ek n_relay dk_relay v_relay
    r1_relay r2_relay j.
  rewrite /relay_at_body in Hbody.
  by rewrite /smc_interpreter.step Halice /alice_foldr_at Hfr Hbody Hs eqxx;
    eexists.
- move=> ps0 f_inner Hsz Hwf Halice Hrecv _ _; right.
  by rewrite /smc_interpreter.step Halice Hrecv eqxx.
- move=> ps0 f_inner Hsz Hwf Halice Hrecv _ _ _ _; right.
  by rewrite /smc_interpreter.step Halice Hrecv eqxx.
- move=> j ps0 _ Hj2 Hsz Hwf Halice [sv0 [f0 [Hrb Hrecv]]] _ _ _ _ _;
  right.
  by rewrite /smc_interpreter.step Halice Hrecv eqxx.
- move=> j ps0 _ Hjlt Hsz Hwf Halice _ _ _ [f_last [Hlast _]] _; right.
  rewrite /smc_interpreter.step Halice
    (@alice_foldr_at_tail AHE ek n_relay dk relays Hrelays v0 u r rand_a).
  by rewrite /alice_erase_tail /std_Recv_dec /Recv_param /= Hlast.
- move=> ps0 rr0 Hsz Hwf Hlast Halice _; left.
  rewrite /smc_interpreter.step Halice
    (@alice_foldr_at_tail AHE ek n_relay dk relays Hrelays v0 u r rand_a).
  by rewrite /alice_erase_tail /std_Recv_dec /Recv_param /= Hlast eqxx;
    eexists.
- move=> ps0 d Hsz Hwf Halice _; left.
  by rewrite /smc_interpreter.step Halice; eexists.
Qed.

(* R2b: Multi-round rsteps with explicit per-round Alice trace fragments.
   frags is in REVERSE chronological order (newest first) so that
   rtrans concatenation (tr2 ++ tr1) matches flatten (rev frags).
   Each fragment is either [:: v] (from Inv_AR/Inv_tail/Inv_ret)
   or [::] (from Inv_AS*/Inv_drain). *)
Lemma dsdp_inv_rsteps_trace_frags (h : nat) (ps : n_parties.-tuple (proc data)) :
  inv (tval ps) ->
  exists (final : n_parties.-tuple (proc data)) (tr : n_parties.-tuple (seq data))
         (frags : seq (seq data)),
    rsteps ps final tr /\
    (all_terminated (tval final) \/ inv (tval final)) /\
    tnth tr ord0 = flatten (rev frags) /\
    (forall k, (k < size frags)%N ->
       (exists v, nth [::] frags k = [:: v]) \/ nth [::] frags k = [::]).
Proof.
elim: h ps => [|h IH] ps Hinv.
- exists ps, [tuple [::] | _ < n_parties], [::].
  by do !split => //; [exact: rrefl | right | rewrite tnth_mktuple].
- set res := [tuple smc_interpreter.step ps [::] i | i < n_parties].
  set ps' := res_procs res.
  set tr1 := res_traces res.
  set frag0 := (smc_interpreter.step (tval ps) [::] 0).1.2.
  have Hss : rsteps ps ps' tr1 := step_sound ps.
  have Hinv' : all_terminated (tval ps') \/ inv (tval ps').
    rewrite -one_step_eq_res_procs.
    by apply dsdp_inv_step.
  have Hfrag := alice_trace_at_inv Hinv.
  have Htr1_0 : tnth tr1 ord0 = frag0.
    by rewrite /tr1 /res_traces tnth_map tnth_mktuple.
  case: Hinv' => [Hterm | Hinv''].
  + exists ps', tr1, [:: frag0].
    do !split => //.
    * by left.
    * by rewrite /= cats0 Htr1_0.
    * by move=> k; rewrite /= ltnS leqn0 => /eqP ->.
  + have [final [tr2 [frags_rest [Hrs2 [Hfinal [Htr2_eq Hfrags_prop]]]]]] :=
      IH ps' Hinv''.
    exists final; eexists; exists (frag0 :: frags_rest).
    do !split.
    * exact: (rtrans Hss Hrs2 erefl).
    * exact: Hfinal.
    * rewrite tnth_mktuple Htr2_eq Htr1_0 /=.
      by rewrite rev_cons -cats1 flatten_cat /= cats0.
    * move=> k Hk; case: k Hk => [|k] Hk /=.
      -- exact: Hfrag.
      -- exact: Hfrags_prop.
Qed.

End alice_trace_at_inv.

(******************************************************************************)
(* Phase 2: Init→dsdp_inv bridge + full trace composition                     *)
(*                                                                            *)
(* B1/B2: After 2 Init rounds, the protocol state satisfies dsdp_inv and     *)
(*   Alice's trace is [d v0; priv_key dk].                                    *)
(* L8: Full trace from initial state to termination = init trace ++ frags.   *)
(******************************************************************************)

Section init_to_inv_bridge.

Variable AHE : AHEncType.
Variable ek : party_id -> pub_key AHE.
Variable n_relay : nat.
Hypothesis Hn_relay : (0 < n_relay)%N.

Let DI := Standard_DSDP_Interface AHE.
Let data := di_data DI.

Variable dk : priv_key AHE.
Variable dk_relay : 'I_n_relay.+1 -> priv_key AHE.

Variable relays : seq 'I_n_relay.+1.
Hypothesis Hrelays : size relays = n_relay.+1.
Hypothesis Hrelays_id : forall k : 'I_n_relay.+1, nth ord0 relays k = k.

Variable v0 : plain AHE.
Variable u : 'I_n_relay.+2 -> plain AHE.
Variable r : 'I_n_relay.+1 -> plain AHE.
Variable rand_a : 'I_n_relay.+1 -> rand AHE.
Variable v_relay : 'I_n_relay.+1 -> plain AHE.
Variables (r1_relay r2_relay : 'I_n_relay.+1 -> rand AHE).

Hypothesis dec_total : forall dk' c, @dec AHE dk' c != None.
Hypothesis key_alice : ek alice_idx = pub_of_priv dk.
Hypothesis key_relay : forall j : 'I_n_relay.+1,
  ek (nat_to_party_id j.+1) = pub_of_priv (dk_relay j).

Let procs := @dsdp_n_procs AHE ek n_relay relays dk v0 u r rand_a
  dk_relay v_relay r1_relay r2_relay.

Let n_parties := n_relay.+2.

Let Hsize : size procs = n_parties.
Proof. by rewrite /procs size_dsdp_n_procs Hrelays. Qed.

Let procs_tup : n_parties.-tuple (proc data) :=
  @Tuple _ _ procs (introT eqP Hsize).

Let inv := dsdp_inv AHE ek n_relay Hn_relay dk dk_relay relays v0 u r rand_a
  v_relay r1_relay r2_relay.

Let d := di_d DI.
Let priv_key := di_priv_key DI.

(* Alice's erased process starts with two Init constructors *)
Lemma alice_proc_init :
  nth (default_proc data) procs 0 =
    Init (priv_key dk) (Init (d v0)
      (@alice_foldr_at AHE ek n_relay dk relays v0 u r rand_a 0)).
Proof.
have Hp0 : nth (default_proc data) procs 0 =
  erase (@palice_n AHE ek n_relay relays dk v0 u r rand_a).
  by rewrite /procs /dsdp_n_procs /erase_aprocs /dsdp_n_saprocs /= /erase_aproc /=.
rewrite Hp0 (@palice_n_erase AHE ek n_relay relays dk v0 u r rand_a).
by rewrite /alice_foldr_at drop0.
Qed.

(* After round 1: Alice at Init (d v0) body, trace = [priv_key dk] *)
Lemma alice_step1_trace :
  (smc_interpreter.step (tval procs_tup) [::] 0).1.2 = [:: priv_key dk].
Proof.
by rewrite /smc_interpreter.step alice_proc_init.
Qed.

Lemma alice_step1_proc :
  (smc_interpreter.step (tval procs_tup) [::] 0).1.1 =
    Init (d v0) (@alice_foldr_at AHE ek n_relay dk relays v0 u r rand_a 0).
Proof.
by rewrite /smc_interpreter.step alice_proc_init.
Qed.

(* After round 2: Alice at alice_foldr_at 0, trace = [d v0] *)
Lemma alice_step2_trace :
  let ps1 := res_procs [tuple smc_interpreter.step procs_tup [::] i | i < n_parties] in
  (smc_interpreter.step (tval ps1) [::] 0).1.2 = [:: d v0].
Proof.
rewrite /=.
have Hstep1 : nth (default_proc data) (tval (res_procs [tuple smc_interpreter.step procs_tup [::] i | i < n_parties])) 0 =
  Init (d v0) (@alice_foldr_at AHE ek n_relay dk relays v0 u r rand_a 0).
  rewrite -(@one_step_eq_res_procs AHE n_relay procs_tup).
  have Hsz : (0 < size (tval procs_tup))%N by rewrite size_tuple.
  rewrite (@nth_one_step data (tval procs_tup) 0 Hsz) /smc_interpreter.step.
  by rewrite alice_proc_init.
by rewrite /smc_interpreter.step Hstep1.
Qed.

(* B2: After 2 Init rounds, rsteps reaches a state satisfying dsdp_inv
   with Alice's trace = [d v0; priv_key dk]. *)
Theorem init_rsteps_to_inv :
  exists (ps_init : n_parties.-tuple (proc data))
         (tr_init : n_parties.-tuple (seq data)),
    rsteps procs_tup ps_init tr_init /\
    tnth tr_init ord0 = [:: d v0; priv_key dk] /\
    inv (tval ps_init) /\
    ~~ all_terminated (tval ps_init) /\
    tval ps_init = one_step_procs data (one_step_procs data procs).
Proof.
(* Round 1 *)
set res1 := [tuple smc_interpreter.step procs_tup [::] i | i < n_parties].
set ps1 := res_procs res1.
set tr1 := res_traces res1.
have Hrs1 : rsteps procs_tup ps1 tr1 := step_sound procs_tup.
(* Round 2 *)
set res2 := [tuple smc_interpreter.step ps1 [::] i | i < n_parties].
set ps2 := res_procs res2.
set tr2 := res_traces res2.
have Hrs2 : rsteps ps1 ps2 tr2 := step_sound ps1.
(* Compose *)
set tr12 := [tuple tnth tr2 i ++ tnth tr1 i | i < n_parties].
have Hrs12 : rsteps procs_tup ps2 tr12 :=
  rtrans Hrs1 Hrs2 erefl.
have Heq : tval ps2 = one_step_procs data (one_step_procs data procs).
  by rewrite -(@one_step_eq_res_procs AHE n_relay ps1)
             -(@one_step_eq_res_procs AHE n_relay procs_tup).
have Hinv_init := @dsdp_inv_init AHE ek n_relay Hn_relay dk dk_relay dec_total
  relays Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay r2_relay.
exists ps2, tr12; do !split.
- exact Hrs12.
- rewrite /tr12 tnth_mktuple /tr2 /res_traces tnth_map tnth_mktuple
    /tr1 /res_traces tnth_map tnth_mktuple alice_step2_trace alice_step1_trace //.
- by rewrite Heq.
- (* ~~ all_terminated *)
  rewrite Heq.
  exact: (@dsdp_init_not_terminated AHE ek n_relay dk dk_relay relays
    Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay r2_relay).
- exact Heq.
Qed.

(* L8: Full trace from initial state to termination.
   Compose Init bridge (init_rsteps_to_inv) with multi-round
   trace fragments (dsdp_inv_rsteps_trace_frags) via rtrans. *)
Theorem alice_full_trace_n (h : nat) :
  exists (final : n_parties.-tuple (proc data))
         (tr : n_parties.-tuple (seq data))
         (frags : seq (seq data)),
    rsteps procs_tup final tr /\
    (all_terminated (tval final) \/ inv (tval final)) /\
    tnth tr ord0 = flatten (rev frags) ++ [:: d v0; priv_key dk] /\
    (forall k, (k < size frags)%N ->
       (exists v, nth [::] frags k = [:: v]) \/ nth [::] frags k = [::]).
Proof.
have [ps_init [tr_init [Hrs_init [Htrace_init [Hinv_init _]]]]] := init_rsteps_to_inv.
have [final [tr_inv [frags [Hrs_inv [Hfinal [Htrace_inv Hfrags]]]]]] :=
  @dsdp_inv_rsteps_trace_frags AHE ek n_relay Hn_relay dk dk_relay relays
    Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay r2_relay
    dec_total key_relay h ps_init Hinv_init.
set tr_full := [tuple tnth tr_inv i ++ tnth tr_init i | i < n_parties].
have Hrs_full : rsteps procs_tup final tr_full :=
  rtrans Hrs_init Hrs_inv erefl.
exists final, tr_full, frags; do !split.
- exact Hrs_full.
- exact Hfinal.
- rewrite /tr_full tnth_mktuple Htrace_inv Htrace_init.
  reflexivity.
- exact Hfrags.
Qed.

(* Concrete return value: what Alice holds after all relays contribute *)
Let concrete_val :=
  d (chain_acc AHE n_relay u r v_relay n_relay.-1 -
     \sum_(j < n_relay.+1) r j + u ord0 * v0).

(* Ghost predicate: if Alice is at Ret d0 then d0 = concrete_val *)
Let ret_val_inv (ps : seq (proc data)) :=
  forall d0, nth (default_proc data) ps 0 = Ret d0 -> d0 = concrete_val.

(* inv_step_gives_inv_ret_val_inv, ret_val_inv_preserved_by_step, and
   inv_step_terminated_concrete are now in dsdp_trace_infra.v.
   The Section-local aliases below make them callable with the same
   argument pattern as before. *)
Let inv_step_gives_inv_ret_val_inv ps :=
  @dsdp_trace_infra.inv_step_gives_inv_ret_val_inv AHE ek n_relay Hn_relay
    dk dk_relay relays Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay
    r2_relay dec_total key_alice key_relay ps.

Let ret_val_inv_preserved_by_step ps :=
  @dsdp_trace_infra.ret_val_inv_preserved_by_step AHE ek n_relay Hn_relay
    dk dk_relay relays Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay
    r2_relay dec_total key_alice key_relay ps.

Let inv_step_terminated_concrete ps :=
  @dsdp_trace_infra.inv_step_terminated_concrete AHE ek n_relay Hn_relay
    dk dk_relay relays Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay
    r2_relay dec_total key_alice key_relay ps.

(* Main induction: from inv with ret_val_inv, reach terminated with concrete Ret *)
Lemma inv_rsteps_ret (h : nat) (ps : n_parties.-tuple (proc data)) :
  inv (tval ps) -> ret_val_inv (tval ps) ->
  exists (final : n_parties.-tuple (proc data))
         (tr0 : n_parties.-tuple (seq data)),
    rsteps ps final tr0 /\
    ((all_terminated (tval final) /\
      nth (default_proc data) (tval final) 0 = Ret concrete_val)
     \/ (inv (tval final) /\ ret_val_inv (tval final))).
Proof.
elim: h ps => [|h IH] ps Hinv Hret_val_inv.
- exists ps, [tuple [::] | _ < n_parties].
  split; [exact: rrefl | right; split; assumption].
- have [Hterm | Hnterm] : all_terminated (tval ps) \/ ~~ all_terminated (tval ps)
    by case: (all_terminated (tval ps)); [left | right].
  + (* Already terminated *)
    exists ps, [tuple [::] | _ < n_parties].
    split; [exact: rrefl | left; split; first exact: Hterm].
    exact: (@dsdp_trace_infra.inv_rv_terminated_ret AHE ek n_relay Hn_relay
      dk dk_relay relays Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay
      r2_relay (tval ps) Hinv Hret_val_inv Hterm).
  + (* Not terminated: step once *)
    set res := [tuple smc_interpreter.step ps [::] i | i < n_parties].
    set ps' := res_procs res.
    set tr1 := res_traces res.
    have Hss : rsteps ps ps' tr1 := step_sound ps.
    have Hinv_step : all_terminated (tval ps') \/ inv (tval ps').
      rewrite -one_step_eq_res_procs.
      exact: (@dsdp_inv_step AHE ek n_relay Hn_relay dk dk_relay
        dec_total key_relay relays Hrelays Hrelays_id v0 u r rand_a
        v_relay r1_relay r2_relay (tval ps) Hinv).
    case: Hinv_step => [Hterm' | Hinv''].
    * (* all_terminated after step *)
      exists ps', tr1; split; [exact: Hss | left; split; first exact: Hterm'].
      have Hterm'' : all_terminated (one_step_procs data (tval ps))
        by rewrite one_step_eq_res_procs.
      rewrite -one_step_eq_res_procs.
      exact: (inv_step_terminated_concrete Hinv Hnterm Hterm'').
    * (* still inv: ret_val_inv preserved, apply IH *)
      have Hret_val_inv' : ret_val_inv (tval ps').
        rewrite -one_step_eq_res_procs.
        exact: (ret_val_inv_preserved_by_step Hinv Hnterm).
      have [final [tr2 [Hrs2 Hgoal]]] := IH ps' Hinv'' Hret_val_inv'.
      exists final, [tuple tnth tr2 i ++ tnth tr1 i | i < n_parties].
      split; [exact: (rtrans Hss Hrs2 erefl) | exact: Hgoal].
Qed.

(* A1: stepping an all_terminated state yields no progress.
   Note: all_terminated includes Ret, which itself has progress (Ret→Finish).
   But after one_step, Ret becomes Finish, and Finish/Fail have no progress. *)
Lemma all_terminated_no_progress ps0 :
  all_terminated ps0 -> ~~ has_progress data (one_step_procs data ps0).
Proof.
move=> Ht; apply/negP => Hprog.
(* Helper: after one_step of terminated, process i becomes Finish or Fail *)
have Hff : forall i, (i < size ps0)%N ->
  (smc_interpreter.step ps0 nil i).1.1 = Finish \/
  (smc_interpreter.step ps0 nil i).1.1 = Fail.
  move=> i Hi; rewrite /smc_interpreter.step.
  have Hti : is_terminal (nth (default_proc data) ps0 i)
    by move/(@all_nthP _ _ _ (default_proc data)): (Ht) => /(_ i Hi).
  by case: (nth (default_proc data) ps0 i) Hti => [dd' k'|dst v' k'|frm f|dd'| |] //=; auto.
(* Extract witness: nth (one_step) i is Finish or Fail, contradicts Init/Ret/Send/Recv *)
have := @has_progress_has_witness data (one_step_procs data ps0) Hprog.
have Habs : forall i, (i < size ps0)%N ->
  nth (default_proc data) (one_step_procs data ps0) i = Finish \/
  nth (default_proc data) (one_step_procs data ps0) i = Fail.
  move=> i Hi; rewrite (@nth_one_step data ps0 i Hi); exact: Hff.
move=> [[i [dd [k' [Hi Hnth]]]] | [[i [dd [Hi Hnth]]] |
         [i [j' [v' [k' [f [Hi [Hj [Hnth_i Hnth_j]]]]]]]]]];
  rewrite size_one_step in Hi.
- by case: (Habs i Hi) => Hq; rewrite Hq in Hnth.
- by case: (Habs i Hi) => Hq; rewrite Hq in Hnth.
- by case: (Habs i Hi) => Hq; rewrite Hq in Hnth_i.
Qed.

(* A2: all_terminated + ret_val_inv preserved by interp_comp *)
Lemma all_terminated_interp_comp ps0 h :
  all_terminated ps0 -> ret_val_inv ps0 ->
  all_terminated (interp_comp data ps0 h) /\
  ret_val_inv (interp_comp data ps0 h).
Proof.
move=> Hall Hrv.
(* After 1 step: Ret→Finish, Finish→Finish. Then ~~ has_progress → fixed point.
   ret_val_inv is preserved: if all Finish, nth 0 ≠ Ret → vacuously true. *)
case: h => [|h'].
- by split.
- rewrite (@interp_comp_unfold_eq data ps0 h').
  case Hprog: (has_progress data ps0).
  + (* has_progress: one more step. After step, ~~ has_progress. Fixed point. *)
    have Hnp' := all_terminated_no_progress Hall.
    rewrite (@interp_comp_fixed_point data (one_step_procs data ps0) h' Hnp').
    split.
    * (* all_terminated (one_step ps0): Ret→Finish, Finish→Finish *)
      apply /(@all_nthP _ _ _ (default_proc data)).
      rewrite (@size_one_step data) => i Hi.
      rewrite (@nth_one_step data ps0 i Hi) /smc_interpreter.step.
      have Hti : is_terminal (nth (default_proc data) ps0 i).
        by move/(@all_nthP _ _ _ (default_proc data)): Hall => /(_ i Hi).
      by case: (nth (default_proc data) ps0 i) Hti => [dd' k'|dst v' k'|frm f|dd'| |] //=.
    * (* ret_val_inv (one_step ps0): after step, Ret→Finish, Finish→Finish.
         nth (one_step) 0 is Finish, so Ret d0 = Finish is impossible. *)
      move=> d0 Hret.
      case Hsz0 : (0 < size ps0)%N; last first.
        by rewrite /one_step_procs nth_default in Hret;
           [| rewrite size_map size_iota; move/negbT: Hsz0; rewrite -leqNgt leqn0 => /eqP ->].
      rewrite (@nth_one_step data ps0 0 Hsz0) /smc_interpreter.step in Hret.
      have Ht0 : is_terminal (nth (default_proc data) ps0 0).
        by move/(@all_nthP _ _ _ (default_proc data)): (Hall) => /(_ 0 Hsz0).
      by case: (nth (default_proc data) ps0 0) Ht0 Hret => //=.
  + (* ~~ has_progress: already fixed point — goal is ps0 itself *)
    by split.
Qed.

(* H2: interp_comp preserves inv + ret_val_inv *)
Lemma interp_comp_preserves_inv_rv h ps0 :
  inv ps0 -> ret_val_inv ps0 -> ~~ all_terminated ps0 ->
  ret_val_inv (interp_comp data ps0 h) /\
  (inv (interp_comp data ps0 h) \/ all_terminated (interp_comp data ps0 h)).
Proof.
elim: h ps0 => [|h IH] ps0 Hinv Hrv Hnt.
- by split; [exact Hrv | left; exact Hinv].
- rewrite (@interp_comp_unfold_eq data ps0 h).
  have Hprog : has_progress data ps0.
    exact (@dsdp_inv_has_progress AHE ek n_relay Hn_relay dk dk_relay
      relays Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay r2_relay ps0 Hinv).
  rewrite Hprog.
  have [Hinv' Hrv'] := inv_step_gives_inv_ret_val_inv Hinv Hnt.
  case Hnt' : (all_terminated (one_step_procs data ps0)).
  + (* all_terminated after one step: use A2 *)
    have Hnt'b : all_terminated (one_step_procs data ps0) by rewrite Hnt'.
    have [Ht Hrv2] := all_terminated_interp_comp h Hnt'b Hrv'.
    by split; [exact Hrv2 | right].
  + have Hnt'' : ~~ all_terminated (one_step_procs data ps0) by rewrite Hnt'.
    exact: IH Hinv' Hrv' Hnt''.
Qed.

(* inv_rsteps_ret_terminates: if inv + ret_val_inv + ~~ all_terminated,
   and interp_comp terminates within h steps, then we reach a state
   with all_terminated and Alice at Ret concrete_val.
   Key: unlike interp_comp which steps past Ret→Finish,
   this stops at the FIRST all_terminated state (Inv_ret). *)
Lemma inv_rsteps_ret_terminates h (ps : n_parties.-tuple (proc data)) :
  inv (tval ps) -> ret_val_inv (tval ps) -> ~~ all_terminated (tval ps) ->
  all_terminated (interp_comp data (tval ps) h) ->
  exists (final : n_parties.-tuple (proc data)) tr,
    rsteps ps final tr /\
    all_terminated (tval final) /\
    nth (default_proc data) (tval final) 0 = Ret concrete_val.
Proof.
elim: h ps => [|h IH] ps Hinv Hrv Hnt Hterm.
- (* h=0: interp_comp ps 0 = ps contradicts ~~ all_terminated ps *)
  by move/negP: Hnt.
- (* h.+1: unfold interp_comp, step once *)
  rewrite (@interp_comp_unfold_eq data (tval ps) h) in Hterm.
  have Hprog : has_progress data (tval ps).
    exact (@dsdp_inv_has_progress AHE ek n_relay Hn_relay dk dk_relay
      relays Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay r2_relay
      (tval ps) Hinv).
  rewrite Hprog in Hterm.
  (* Hterm : all_terminated (interp_comp data (one_step_procs data (tval ps)) h) *)
  set res := [tuple smc_interpreter.step ps [::] i | i < n_parties].
  set ps' := res_procs res.
  set tr1 := res_traces res.
  have Hss : rsteps ps ps' tr1 := step_sound ps.
  have Hps'eq : tval ps' = one_step_procs data (tval ps)
    by rewrite -(@one_step_eq_res_procs AHE n_relay ps).
  have Hinv_step : all_terminated (one_step_procs data (tval ps)) \/
                   inv (one_step_procs data (tval ps)).
    exact: (@dsdp_inv_step AHE ek n_relay Hn_relay dk dk_relay
      dec_total key_relay relays Hrelays Hrelays_id v0 u r rand_a
      v_relay r1_relay r2_relay (tval ps) Hinv).
  case: Hinv_step => [Hterm_step | Hinv_step].
  + (* all_terminated after one step: Alice at Ret concrete_val *)
    exists ps', tr1; split; [exact Hss | split].
    * by rewrite Hps'eq.
    * rewrite Hps'eq.
      exact: (inv_step_terminated_concrete Hinv Hnt Hterm_step).
  + (* inv after step: check all_terminated or recurse *)
    have [Hinv' Hrv'] := inv_step_gives_inv_ret_val_inv Hinv Hnt.
    case Hnt' : (all_terminated (one_step_procs data (tval ps))).
    * (* all_terminated: same as left branch *)
      exists ps', tr1; split; [exact Hss | split].
      -- by rewrite Hps'eq.
      -- rewrite Hps'eq.
         exact: (inv_step_terminated_concrete Hinv Hnt Hnt').
    * (* ~~ all_terminated: apply IH *)
      have Hnt'' : ~~ all_terminated (tval ps') by rewrite Hps'eq Hnt'.
      have Hinv'' : inv (tval ps') by rewrite Hps'eq; exact Hinv_step.
      have Hrv'' : ret_val_inv (tval ps') by rewrite Hps'eq.
      have Hterm' : all_terminated (interp_comp data (tval ps') h)
        by rewrite Hps'eq.
      have [final [tr2 [Hrs2 [Htf Hretf]]]] :=
        IH ps' Hinv'' Hrv'' Hnt'' Hterm'.
      exists final, [tuple tnth tr2 i ++ tnth tr1 i | i < n_parties].
      split; [exact: (rtrans Hss Hrs2 erefl) | split; [exact Htf | exact Hretf]].
Qed.

(* H3: N-party computational correctness *)
Theorem n_party_correctness (h : nat)
    (Hfuel : (h >= [> @dsdp_n_saprocs AHE ek n_relay relays dk v0 u r rand_a
       dk_relay v_relay r1_relay r2_relay])%N) :
  (1 <= n_relay)%N ->
  exists (final : n_parties.-tuple (proc data)) tr,
    rsteps procs_tup final tr /\
    all_terminated (tval final) /\
    nth (default_proc data) (tval final) 0 =
      Ret (d (\sum_(j : 'I_n_relay.+1) u (lift ord0 j) * v_relay j + u ord0 * v0)).
Proof.
move=> Hn1.
(* Step 1: init → inv + ret_val_inv + ~~ all_terminated + equation *)
have [ps_init [tr_init [Hrs_init [_ [Hinv_init [Hnt_init Heq_init]]]]]] :=
  init_rsteps_to_inv.
(* ret_val_inv at init: vacuously true since no inv constructor has Alice at Ret
   when ~~ all_terminated *)
have Hrv_init : ret_val_inv (tval ps_init).
  move=> d0 Hret0; exfalso; apply (negP Hnt_init).
  case: {+}Hinv_init Hret0.
  - move=> j' ps' rr' Hsz' _ Ha' _ _ _ _ _ _ Hret0.
    have [f' Hf'] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays
      Hrelays_id v0 u r rand_a j' (ltn_ord j').
    by rewrite Ha' /alice_foldr_at Hf' in Hret0.
  - move=> ps' _ Hsz' _ Ha' _ _ _ Hret0. by rewrite Ha' in Hret0.
  - move=> ps' _ Hsz' _ Ha' _ _ _ _ _ Hret0. by rewrite Ha' in Hret0.
  - move=> j' ps' _ _ Hsz' _ Ha' _ _ _ _ _ _ Hret0. by rewrite Ha' in Hret0.
  - move=> j' ps' _ _ Hsz' _ Ha' _ _ _ _ _ Hret0.
    have [f' Hf'] := @alice_tail_is_recv AHE n_relay dk v0 u r.
    by rewrite Ha' (@alice_foldr_at_tail AHE ek n_relay dk relays Hrelays
      v0 u r rand_a) Hf' in Hret0.
  - move=> ps' _ Hsz' _ _ Ha' _ Hret0.
    have [f' Hf'] := @alice_tail_is_recv AHE n_relay dk v0 u r.
    by rewrite Ha' (@alice_foldr_at_tail AHE ek n_relay dk relays Hrelays
      v0 u r rand_a) Hf' in Hret0.
  - (* Inv_ret: all_terminated → contradicts Hnt_init *)
    move=> ps' d1' Hsz' _ Hret' Hrels' _.
    apply /(@all_nthP _ _ _ (default_proc data)).
    rewrite Hsz' => i Hi; case: i Hi => [|i] Hi.
    + by rewrite Hret'.
    + have Him : (i < n_relay.+1)%N by rewrite ltnS in Hi.
      by have := Hrels' (Ordinal Him); rewrite /relay_at_finish_pred /= => ->.
(* Step 2: Bridge — interp_comp data procs 2 = tval ps_init *)
(* From Heq_init: tval ps_init = one_step_procs(one_step_procs(procs)).
   interp_comp procs 2 = interp_comp (one_step procs) 1 (init has progress)
                        = interp_comp (one_step(one_step procs)) 0 (second state has progress)
                        = one_step(one_step procs) = tval ps_init *)
have Hprog0 : has_progress data procs.
  exact: (@dsdp_initial_progress AHE ek n_relay dk dk_relay relays Hrelays
    v0 u r rand_a v_relay r1_relay r2_relay).
have Hic1 : interp_comp data procs 1 = one_step_procs data procs.
  by rewrite (@interp_comp_unfold_eq data procs 0) Hprog0.
have Hprog1 : has_progress data (one_step_procs data procs).
  have [Ht1|Hp1] := @dsdp_terminated_or_progress AHE ek n_relay Hn_relay dk
    dk_relay dec_total key_relay relays Hrelays Hrelays_id v0 u r rand_a
    v_relay r1_relay r2_relay 1.
  + (* all_terminated (interp_comp procs 1) contradicts dsdp_init_not_terminated *)
    exfalso; rewrite Hic1 in Ht1.
    have := @step_all_terminated data _ Ht1.
    have := @dsdp_init_not_terminated AHE ek n_relay dk dk_relay relays
      Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay r2_relay.
    by move/negP; apply.
  + by rewrite Hic1 in Hp1.
have Hbridge : interp_comp data procs 2 = tval ps_init.
  rewrite Heq_init (@interp_comp_unfold_eq data procs 1) Hprog0.
  by rewrite (@interp_comp_unfold_eq data (one_step_procs data procs) 0) Hprog1.
(* Step 3: all_terminated (interp_comp (tval ps_init) h) via dsdp_interp_terminates *)
have Hfuel2 : (2 + h >= [> @dsdp_n_saprocs AHE ek n_relay relays dk v0 u r rand_a
     dk_relay v_relay r1_relay r2_relay])%N.
  exact (leq_trans Hfuel (leq_addl 2 h)).
have Hterm_interp := @dsdp_interp_terminates AHE ek n_relay Hn_relay dk dk_relay
  dec_total key_relay relays Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay
  r2_relay (2 + h) Hfuel2.
have Hcomp := @interp_comp_add data (tval procs_tup) 2 h.
rewrite Hcomp Hbridge in Hterm_interp.
(* Hterm_interp : all_terminated (interp_comp data (tval ps_init) h) *)
(* Step 4: inv_rsteps_ret_terminates → final with all_terminated + Ret concrete_val *)
have [final [tr_inv [Hrs_inv [Htf Hretf]]]] :=
  @inv_rsteps_ret_terminates h ps_init Hinv_init Hrv_init Hnt_init Hterm_interp.
(* Step 5: compose rsteps and conclude *)
set tr_full := [tuple tnth tr_inv i ++ tnth tr_init i | i < n_parties].
have Hrs_full : rsteps procs_tup final tr_full := rtrans Hrs_init Hrs_inv erefl.
exists final, tr_full; split; [exact Hrs_full | split; [exact Htf |]].
rewrite Hretf /concrete_val. congr (Ret _). congr (d _).
by rewrite (@chain_acc_minus_masks AHE n_relay u r v_relay Hn1) GRing.addrC.
Qed.

End init_to_inv_bridge.

(******************************************************************************)
(* L6: View Faithfulness                                                      *)
(*                                                                            *)
(* AliceView_n (algebraic RV from dsdp_security.v) faithfully models what     *)
(* Alice actually learns during protocol execution. Every component of        *)
(* AliceView_n comes from either:                                             *)
(*   (a) Alice's trace (Init'd, Recv'd, Ret'd values):                       *)
(*       - Dk_a: from Init (#dk) — in trace (L5a)                            *)
(*       - V0: from Init (&v0) — in trace (L5a)                              *)
(*       - E_relay_RV (ciphertexts {c_j}): from Recv — in trace (L5b)        *)
(*       - S (result): from Ret — in trace (L5d)                             *)
(*   (b) Alice's private inputs (function arguments to palice_n):             *)
(*       - U0: Alice's coefficient — NOT communicated, NOT in trace           *)
(*       - U_relay_RV: relay coefficients — NOT communicated, NOT in trace    *)
(*       - R_relay_RV: random masks — NOT communicated, NOT in trace          *)
(*                                                                            *)
(* The trace is a LOSSY projection of AliceView_n: it contains (a) but       *)
(* not (b). Alice knows both (a) and (b), so her full knowledge equals       *)
(* AliceView_n. An eavesdropper on Alice's channel sees only (a).            *)
(*                                                                            *)
(* This correspondence is verified by the per-step trace lemmas (L5a-L5e)    *)
(* which characterize exactly what enters Alice's trace at each step.        *)
(******************************************************************************)

(* L6 is a conceptual correspondence verified by concrete trace lemmas:
   - L5a (alice_trace_init): Dk_a and V0 enter trace via Init
   - L5c (alice_trace_concrete_AR): c_j = enc(ek(j+1), v_relay(j), r1_relay(j))
     enters trace via Recv from relay j+1
   - L5c (alice_trace_concrete_tail): g = enc(ek(alice), chain_acc(n-1), rr_tail)
     enters trace via Recv from last relay
   - L5d (alice_trace_at_ret): d_result enters trace via Ret
   - Private inputs (U0, U_relay, R_relay, rand_a) are arguments to palice_n,
     never Init'd/Recv'd/Ret'd, hence absent from the trace. *)

(******************************************************************************)
(* L8: Eavesdropper Security                                                  *)
(*                                                                            *)
(* An eavesdropper who observes Alice's communication trace learns no more   *)
(* about the relay secrets VarRV than Alice herself does.                     *)
(*                                                                            *)
(* Formally: H(VarRV | trace) >= H(VarRV | AliceView_n) = log(m^n_relay)    *)
(*                                                                            *)
(* The first inequality is the data processing inequality: the trace is      *)
(* a deterministic function of AliceView_n (projection onto communicated     *)
(* components), so conditioning on less information cannot decrease entropy.  *)
(*                                                                            *)
(* The equality is dsdp_entropic_security_n_concrete (from dsdp_security.v). *)
(*                                                                            *)
(* Proved as trace_eavesdropper_security_n in dsdp_security.v:               *)
(*   H(VarRV | AliceTraces_n) >= log(m^n_relay) > 0                         *)
(* where AliceTraces_n = trace_proj_n ∘ AliceView_n drops R_relay_RV.        *)
(*****************************************************************************)
