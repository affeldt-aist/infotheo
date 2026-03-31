From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap matrix lra reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter.
Require Import smc_session_types homomorphic_encryption dsdp_interface dsdp_pismc.

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

(* TODO: Implement L5b-L5e, L6, D3, L8 per the plan.
   These require:
   - step_res_trace_inert / step_res_trace_disjoint from smc_interpreter_sound.v
   - palice_n structure from dsdp_pismc.v
   - dsdp_entropic_security_n_concrete from dsdp_security.v
   - data processing inequality for entropy *)

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

End alice_trace_init.
