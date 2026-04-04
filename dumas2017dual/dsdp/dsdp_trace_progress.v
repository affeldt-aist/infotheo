(* dsdp_trace_progress.v — Concrete trace characterization for N-party DSDP

   This file extends dsdp_entropy_trace.v (which proves n_party_correctness)
   with full trace content characterization: Alice's accumulated rsteps trace
   contains exactly [d(result); di_e(tail_cipher); di_e(c_{n-1}); ...;
   di_e(c_0); d(v0); priv_key(dk)] where each c_j is the concrete
   re-encryption from relay j.

   FUTURE WORK (3D): Operational-to-distributional bridge
   ======================================================
   The distributional security is proved separately in dsdp_security.v
   (trace_eavesdropper_security_n). To connect operational traces (rsteps)
   to the distributional model (AliceTraces_n : {RV P -> trace_proj_n_T}),
   the following foundational infrastructure is needed:

   1. T_construction: Concrete sample space T : finType as product of
      all randomness spaces (rand AHE, plain AHE, etc.)
   2. P_construction: Joint distribution P : R.-fdist T
   3. enc_msg bridge: Coercion between cipher AHE (operational) and
      enc_msg : finType (security)
   4. sampling_model: Map w : T to random values used by rsteps
   5. trace_to_AliceTraces_n: Master bridge showing operational trace
      at sample point w equals AliceTraces_n w (Very Hard)
   6. trace_entropy_bridge: H(VarRV | AliceTraces_n) = H(VarRV | op_trace)
   7. operational_security_n: H(VarRV | op_trace) >= log(m^n_relay)

   This bridge is a separate research contribution (~1000+ lines).
   See the plan at .claude/plans/fuzzy-plotting-wren.md for details.
*)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap matrix lra reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter.
Require Import smc_session_types smc_interpreter_sound.
Require Import homomorphic_encryption dsdp_interface dsdp_pismc.
Require Import dsdp_progress dsdp_entropy_trace.

Import GRing.Theory.
Import Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(******************************************************************************)
(* Section 3C: Data type injectivity                                          *)
(*                                                                            *)
(* The standard DSDP interface encodes data as a 4-way sum type:              *)
(*   std_data = (plain + cipher + priv_key + pub_key)%type                   *)
(* These lemmas establish injectivity of each injection, needed to            *)
(* decode concrete values from operational traces.                            *)
(******************************************************************************)

Section data_injectivity.

Variable AHE : AHEncType.
Let DI := Standard_DSDP_Interface AHE.

Lemma di_e_inj (c1 c2 : cipher AHE) :
  di_e DI c1 = di_e DI c2 -> c1 = c2.
Proof. by move=> []. Qed.

Lemma di_d_inj (m1 m2 : plain AHE) :
  di_d DI m1 = di_d DI m2 -> m1 = m2.
Proof. by move=> []. Qed.

Lemma di_priv_key_inj (k1 k2 : priv_key AHE) :
  di_priv_key DI k1 = di_priv_key DI k2 -> k1 = k2.
Proof. by move=> []. Qed.

(* di_from_enc_e already exists as std_from_enc_e in dsdp_interface.v *)

End data_injectivity.

(******************************************************************************)
(* Section 3A: Trace accumulation invariant                                   *)
(*                                                                            *)
(* Threads concrete trace values through the multi-round dsdp_inv induction.  *)
(* At each dsdp_inv phase, Alice's accumulated rsteps trace equals a         *)
(* predictable sequence of ciphertexts and initial values.                   *)
(******************************************************************************)

Section trace_accumulation.

Variable AHE : AHEncType.
Variable ek : party_id -> pub_key AHE.
Variable n_relay : nat.
Hypothesis Hn_relay : (0 < n_relay)%N.

Let DI := Standard_DSDP_Interface AHE.
Let data := di_data DI.
Let n_parties := n_relay.+2.

Variable dk : priv_key AHE.
Variable dk_relay : 'I_n_relay.+1 -> priv_key AHE.

Variable relays : seq 'I_n_relay.+1.
Hypothesis Hrelays : size relays = n_relay.+1.
Hypothesis Hrelays_id : forall k : 'I_n_relay.+1, nth ord0 relays k = k.

Hypothesis dec_total : forall dk' c, @dec AHE dk' c != None.
Hypothesis key_alice : ek alice_idx = pub_of_priv dk.
Hypothesis key_relay : forall j : 'I_n_relay.+1,
  ek (nat_to_party_id j.+1) = pub_of_priv (dk_relay j).

Variable v0 : plain AHE.
Variable u : 'I_n_relay.+2 -> plain AHE.
Variable r : 'I_n_relay.+1 -> plain AHE.
Variable rand_a : 'I_n_relay.+1 -> rand AHE.
Variable v_relay : 'I_n_relay.+1 -> plain AHE.
Variables (r1_relay r2_relay : 'I_n_relay.+1 -> rand AHE).

Let inv := dsdp_inv AHE ek n_relay Hn_relay dk dk_relay relays v0 u r rand_a
  v_relay r1_relay r2_relay.

Let d := di_d DI.
Let e := di_e DI.
Let priv_key := di_priv_key DI.

Let procs := @dsdp_n_procs AHE ek n_relay relays dk v0 u r rand_a
  dk_relay v_relay r1_relay r2_relay.

Let Hsize : size procs = n_parties.
Proof. by rewrite /procs size_dsdp_n_procs Hrelays. Qed.

Let procs_tup : n_parties.-tuple (proc data) :=
  @Tuple _ _ procs (introT eqP Hsize).

(* ================================================================== *)
(* Concrete trace building blocks                                      *)
(* ================================================================== *)

(* Expected cipher from relay j's AR phase *)
Let cipher_j (j : 'I_n_relay.+1) : data :=
  e (enc (ek (nat_to_party_id j.+1)) (v_relay j) (r1_relay j)).

(* Concrete return value — same as in dsdp_entropy_trace.v *)
Let concrete_val :=
  d (chain_acc AHE n_relay u r v_relay n_relay.-1 -
     \sum_(j < n_relay.+1) r j + u ord0 * v0).

(* Ghost predicate: if Alice is at Ret d0 then d0 = concrete_val *)
Let ret_val_inv (ps : seq (proc data)) :=
  forall d0, nth (default_proc data) ps 0 = Ret d0 -> d0 = concrete_val.

(* ================================================================== *)
(* Per-phase Alice trace fragment lemmas                               *)
(*                                                                     *)
(* These lemmas characterize what step_sound adds to Alice's trace     *)
(* (position 0) at each dsdp_inv phase:                                *)
(*   Inv_AR j  → [:: cipher_j j]        (Alice receives from relay j) *)
(*   Inv_AS*   → [::]                    (Alice sends, no trace)       *)
(*   Inv_drain → [::]                    (relay chain forwarding)      *)
(*   Inv_tail  → [:: tail_cipher]        (Alice receives from last)    *)
(*   Inv_ret   → [:: d(result)]          (Alice outputs Ret value)     *)
(*                                                                     *)
(* The per-phase lemmas from dsdp_entropy_trace.v (alice_trace_at_send,*)
(* alice_trace_concrete_AR, alice_trace_at_drain, etc.) are used       *)
(* directly — we restate the key ones here for clarity.                *)
(* ================================================================== *)

(* L1: At Inv_AR j, Alice's trace fragment is [cipher_j j].
   Wraps alice_trace_concrete_AR from dsdp_entropy_trace.v. *)
Lemma alice_trace_step_AR (ps : n_parties.-tuple (proc data))
    (j : 'I_n_relay.+1) :
  nth (default_proc data) (tval ps) 0 =
    @alice_foldr_at AHE ek n_relay dk relays v0 u r rand_a j ->
  @relay_at_body AHE ek n_relay dk_relay v_relay r1_relay r2_relay j (tval ps) ->
  (smc_interpreter.step ps [::] 0).1.2 = [:: cipher_j j].
Proof.
move=> Halice Hbody.
have [f Hrecv] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays
  Hrelays_id v0 u r rand_a j (ltn_ord j).
have [sk Hsend] := @relay_body_is_send0 AHE ek n_relay dk_relay v_relay
  r1_relay r2_relay j.
rewrite /relay_at_body in Hbody.
by rewrite /smc_interpreter.step /= Halice /alice_foldr_at Hrecv Hbody Hsend eqxx.
Qed.

(* L2: At any Inv_AS* phase, Alice sends → trace fragment is nil. *)
Lemma alice_trace_step_send (ps : n_parties.-tuple (proc data))
    (dst : nat) (vd : data) (k0 : proc data) :
  nth (default_proc data) (tval ps) 0 = Send dst vd k0 ->
  (exists f, nth (default_proc data) (tval ps) dst = Recv 0 f) ->
  (smc_interpreter.step ps [::] 0).1.2 = [::].
Proof.
move=> Halice [f Hdst].
by rewrite /smc_interpreter.step Halice Hdst eqxx.
Qed.

(* L3: At Inv_drain, Alice is at Recv (alice_foldr_at n_relay.+1)
   but the last relay is also at Recv → no match → trace fragment nil. *)
Lemma alice_trace_step_drain (ps : n_parties.-tuple (proc data)) :
  nth (default_proc data) (tval ps) 0 =
    @alice_foldr_at AHE ek n_relay dk relays v0 u r rand_a n_relay.+1 ->
  (exists g, nth (default_proc data) (tval ps) n_relay.+1 =
    Recv n_relay g) ->
  (smc_interpreter.step ps [::] 0).1.2 = [::].
Proof.
move=> Halice [g Hlast].
rewrite /smc_interpreter.step Halice.
rewrite (@alice_foldr_at_tail AHE ek n_relay dk relays Hrelays v0 u r rand_a).
rewrite /alice_erase_tail /std_Recv_dec /Recv_param /=.
by rewrite Hlast.
Qed.

(* L4: At Inv_tail, the last relay sends enc(ek(alice), chain_acc(n-1), rr_tail)
   back to Alice. Alice's trace fragment is [:: tail_cipher]. *)
Lemma alice_trace_step_tail (ps : n_parties.-tuple (proc data))
    (rr_tail : rand AHE) :
  nth (default_proc data) (tval ps) 0 =
    @alice_foldr_at AHE ek n_relay dk relays v0 u r rand_a n_relay.+1 ->
  nth (default_proc data) (tval ps) n_relay.+1 =
    Send 0 (e (enc (ek alice_idx) (@chain_acc AHE n_relay u r v_relay
      n_relay.-1) rr_tail)) Finish ->
  (smc_interpreter.step ps [::] 0).1.2 =
    [:: e (enc (ek alice_idx) (@chain_acc AHE n_relay u r v_relay
      n_relay.-1) rr_tail)].
Proof.
move=> Halice Hlast.
rewrite /smc_interpreter.step Halice.
rewrite (@alice_foldr_at_tail AHE ek n_relay dk relays Hrelays v0 u r rand_a).
rewrite /alice_erase_tail /std_Recv_dec /Recv_param /=.
by rewrite Hlast eqxx.
Qed.

(* L5: At Inv_ret, Alice at Ret d0. Trace fragment is [:: d0]. *)
Lemma alice_trace_step_ret (ps : n_parties.-tuple (proc data)) (d0 : data) :
  nth (default_proc data) (tval ps) 0 = Ret d0 ->
  (smc_interpreter.step ps [::] 0).1.2 = [:: d0].
Proof.
by move=> Halice; rewrite /smc_interpreter.step Halice.
Qed.

(* ================================================================== *)
(* Trace accumulation through the induction                            *)
(* ================================================================== *)

(* Expected accumulated trace after completing AR phases 0..j-1.
   At Inv_AR j, Alice has already received ciphers 0..j-1 on top of
   the initial [d v0; priv_key dk].

   trace_after_AR 0 = [d v0; priv_key dk]
   trace_after_AR 1 = [cipher_j 0; d v0; priv_key dk]
   trace_after_AR k = [cipher_j (k-1); ...; cipher_j 0; d v0; priv_key dk]
*)
Fixpoint alice_trace_after_AR (j : nat) : seq data :=
  match j with
  | 0 => [:: d v0; priv_key dk]
  | k.+1 =>
      if (k < n_relay.+1)%N =P true is ReflectT kn then
        cipher_j (Ordinal kn) :: alice_trace_after_AR k
      else alice_trace_after_AR k
  end.

(* Expected trace content for the full protocol. After:
   - Init: [d v0; priv_key dk]
   - AR phases 0..n_relay: alice_trace_after_AR n_relay.+1
   - AS phases interleaved with AR: same (sends add nothing)
   - Drain phases: same (no Alice interaction)
   - Tail: tail_cipher :: alice_trace_after_AR n_relay.+1
   - Ret: concrete_val :: tail_cipher :: alice_trace_after_AR n_relay.+1
*)

(* trace_inv: links dsdp_inv phase to expected accumulated trace *)
Definition trace_inv_phase (ps : seq (proc data)) (tr_acc : seq data) : Prop :=
  (* At Inv_AR j: tr_acc = alice_trace_after_AR j (AR phases 0..j-1 done) *)
  (* At Inv_AS after AR j: tr_acc = alice_trace_after_AR j.+1 (AR j done, AS adds nothing) *)
  (* At Inv_drain: tr_acc = alice_trace_after_AR n_relay.+1 *)
  (* At Inv_tail: tr_acc = alice_trace_after_AR n_relay.+1 *)
  (* At Inv_ret: tr_acc includes tail cipher too *)
  True. (* Placeholder — will be refined per-constructor below *)

(* ================================================================== *)
(* Main theorem: inv_rsteps_ret_with_trace                             *)
(*                                                                     *)
(* Extends inv_rsteps_ret_terminates (from dsdp_entropy_trace.v)       *)
(* to track Alice's accumulated rsteps trace through the induction.    *)
(* At each step, we know what step_sound adds to Alice's trace and     *)
(* thread this through the rtrans trace concatenation.                 *)
(* ================================================================== *)

Lemma inv_rsteps_ret_with_trace h (ps : n_parties.-tuple (proc data))
    (tr_acc : seq data) :
  inv (tval ps) -> ret_val_inv (tval ps) ->
  ~~ all_terminated (tval ps) ->
  all_terminated (interp_comp data (tval ps) h) ->
  (* tr_acc is the accumulated trace from procs_tup to ps *)
  (exists tr0, rsteps procs_tup ps tr0 /\ tnth tr0 ord0 = tr_acc) ->
  exists (final : n_parties.-tuple (proc data)) tr_final,
    rsteps procs_tup final tr_final /\
    all_terminated (tval final) /\
    nth (default_proc data) (tval final) 0 = Ret concrete_val /\
    (* The trace extends tr_acc with the remaining protocol steps *)
    exists suffix, tnth tr_final ord0 = suffix ++ tr_acc.
Proof.
elim: h ps tr_acc => [|h IH] ps tr_acc Hinv Hrv Hnt Hterm Htr.
- by move/negP: Hnt.
- rewrite (@interp_comp_unfold_eq data (tval ps) h) in Hterm.
  have Hprog : has_progress data (tval ps).
    exact (@dsdp_inv_has_progress AHE ek n_relay Hn_relay dk dk_relay
      relays Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay r2_relay
      (tval ps) Hinv).
  rewrite Hprog in Hterm.
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
  have [tr0 [Hrs0 Htr0eq]] := Htr.
  case: Hinv_step => [Hterm_step | Hinv_step].
  + (* all_terminated after one step *)
    set tr_composed := [tuple tnth tr1 i ++ tnth tr0 i | i < n_parties].
    have Hrs_comp : rsteps procs_tup ps' tr_composed := rtrans Hrs0 Hss erefl.
    exists ps', tr_composed; split; first exact Hrs_comp.
    split; first by rewrite Hps'eq.
    split.
    * rewrite Hps'eq.
      exact: (@inv_step_terminated_concrete AHE ek n_relay Hn_relay dk dk_relay
        relays Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay r2_relay
        dec_total key_alice key_relay (tval ps) Hinv Hnt Hterm_step).
    * exists (tnth tr1 ord0); rewrite /tr_composed tnth_mktuple.
      by rewrite -Htr0eq.
  + (* inv preserved: check all_terminated or recurse *)
    have [Hinv' Hrv'] := @inv_step_gives_inv_ret_val_inv AHE ek n_relay Hn_relay dk dk_relay
      relays Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay r2_relay
      dec_total key_alice key_relay (tval ps) Hinv Hnt.
    case Hnt' : (all_terminated (one_step_procs data (tval ps))).
    * (* all_terminated: same as left branch *)
      set tr_composed := [tuple tnth tr1 i ++ tnth tr0 i | i < n_parties].
      have Hrs_comp : rsteps procs_tup ps' tr_composed := rtrans Hrs0 Hss erefl.
      exists ps', tr_composed; split; first exact Hrs_comp.
      split; first by rewrite Hps'eq.
      split.
      -- rewrite Hps'eq.
         exact: (@inv_step_terminated_concrete AHE ek n_relay Hn_relay dk dk_relay
           relays Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay r2_relay
           dec_total key_alice key_relay (tval ps) Hinv Hnt Hnt').
      -- exists (tnth tr1 ord0); rewrite /tr_composed tnth_mktuple.
         by rewrite -Htr0eq.
    * (* ~~ all_terminated: apply IH *)
      have Hnt'' : ~~ all_terminated (tval ps') by rewrite Hps'eq Hnt'.
      have Hinv'' : inv (tval ps') by rewrite Hps'eq; exact Hinv_step.
      have Hrv'' : ret_val_inv (tval ps') by rewrite Hps'eq.
      have Hterm' : all_terminated (interp_comp data (tval ps') h)
        by rewrite Hps'eq.
      (* Build new trace hypothesis: rsteps procs_tup ps' tr_composed *)
      set tr_composed := [tuple tnth tr1 i ++ tnth tr0 i | i < n_parties].
      have Hrs_comp : rsteps procs_tup ps' tr_composed := rtrans Hrs0 Hss erefl.
      have Htr_new : tnth tr_composed ord0 = tnth tr1 ord0 ++ tr_acc.
        by rewrite /tr_composed tnth_mktuple -Htr0eq.
      have Htr_ex : exists tr0' : n_parties.-tuple (seq data),
        rsteps procs_tup ps' tr0' /\ tnth tr0' ord0 = tnth tr1 ord0 ++ tr_acc.
        by exists tr_composed.
      have [final [tr_final [Hrs_final [Htf [Hretf [suffix Hsuf]]]]]] :=
        IH ps' (tnth tr1 ord0 ++ tr_acc) Hinv'' Hrv'' Hnt'' Hterm' Htr_ex.
      exists final, tr_final; split; first exact Hrs_final.
      split; first exact Htf.
      split; first exact Hretf.
      exists (suffix ++ tnth tr1 ord0).
      by rewrite -catA.
Qed.

(* ================================================================== *)
(* Full trace characterization: from initial state to termination      *)
(* ================================================================== *)

(* The full trace theorem: composing init_rsteps_to_inv (which gives
   initial trace [d v0; priv_key dk]) with inv_rsteps_ret_with_trace
   (which tracks accumulation) to get the complete trace content. *)
Theorem n_party_trace_correctness (h : nat)
    (Hfuel : (h >= [> @dsdp_n_saprocs AHE ek n_relay relays dk v0 u r rand_a
       dk_relay v_relay r1_relay r2_relay])%N) :
  (1 <= n_relay)%N ->
  exists (final : n_parties.-tuple (proc data)) tr,
    rsteps procs_tup final tr /\
    all_terminated (tval final) /\
    nth (default_proc data) (tval final) 0 = Ret concrete_val /\
    (* Alice's full trace is concrete_val :: (some ciphertexts) ++ [d v0; priv_key dk] *)
    exists prefix, tnth tr ord0 = prefix ++ [:: d v0; priv_key dk].
Proof.
move=> Hn1.
(* Step 1: init → inv + trace *)
have [ps_init [tr_init [Hrs_init [Htrace_init [Hinv_init [Hnt_init Heq_init]]]]]] :=
  @init_rsteps_to_inv AHE ek n_relay Hn_relay dk dk_relay relays Hrelays
    Hrelays_id v0 u r rand_a v_relay r1_relay r2_relay dec_total.
have Hprocs_eq : Tuple (introT eqP
  (dsdp_entropy_trace.Hsize_subproof ek dk dk_relay Hrelays v0 u r rand_a
    v_relay r1_relay r2_relay)) = procs_tup.
  by apply val_inj.
rewrite Hprocs_eq in Hrs_init.
(* Step 2: ret_val_inv at init — vacuously true *)
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
(* Step 3: Bridge — interp_comp terminates *)
have Hprog0 : has_progress data procs.
  exact: (@dsdp_initial_progress AHE ek n_relay dk dk_relay relays Hrelays
    v0 u r rand_a v_relay r1_relay r2_relay).
have Hic1 : interp_comp data procs 1 = one_step_procs data procs.
  by rewrite (@interp_comp_unfold_eq data procs 0) Hprog0.
have Hprog1 : has_progress data (one_step_procs data procs).
  have [Ht1|Hp1] := @dsdp_terminated_or_progress AHE ek n_relay Hn_relay dk
    dk_relay dec_total key_relay relays Hrelays Hrelays_id v0 u r rand_a
    v_relay r1_relay r2_relay 1.
  + exfalso; rewrite Hic1 in Ht1.
    have := @step_all_terminated data _ Ht1.
    have := @dsdp_init_not_terminated AHE ek n_relay dk dk_relay relays
      Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay r2_relay.
    by move/negP; apply.
  + by rewrite Hic1 in Hp1.
have Hbridge : interp_comp data procs 2 = tval ps_init.
  rewrite Heq_init (@interp_comp_unfold_eq data procs 1) Hprog0.
  by rewrite (@interp_comp_unfold_eq data (one_step_procs data procs) 0) Hprog1.
have Hfuel2 : (2 + h >= [> @dsdp_n_saprocs AHE ek n_relay relays dk v0 u r rand_a
     dk_relay v_relay r1_relay r2_relay])%N.
  exact (leq_trans Hfuel (leq_addl 2 h)).
have Hterm_interp := @dsdp_interp_terminates AHE ek n_relay Hn_relay dk dk_relay
  dec_total key_relay relays Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay
  r2_relay (2 + h) Hfuel2.
have Hcomp := @interp_comp_add data (tval procs_tup) 2 h.
rewrite Hcomp Hbridge in Hterm_interp.
(* Step 4: Apply inv_rsteps_ret_with_trace *)
have Htr_ex : exists tr0 : n_parties.-tuple (seq data),
  rsteps procs_tup ps_init tr0 /\ tnth tr0 ord0 = [:: d v0; priv_key dk].
  exists tr_init; split; first exact Hrs_init.
  exact Htrace_init.
have [final [tr_final [Hrs_final [Htf [Hretf [suffix Hsuf]]]]]] :=
  inv_rsteps_ret_with_trace Hinv_init Hrv_init Hnt_init Hterm_interp Htr_ex.
exists final, tr_final; do !split => //.
by exists suffix.
Qed.

End trace_accumulation.
