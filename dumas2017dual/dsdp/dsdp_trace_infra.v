(* dsdp_trace_infra.v — Simpler 3-constructor invariant for trace/correctness proofs

   Provides `alice_phase` — a simplified abstraction over `dsdp_inv` (7 constructors)
   that downstream trace/correctness proofs can pattern-match on with only 3 cases:
   - AP_loop j: Alice in the Recv/Send loop at iteration j
   - AP_tail: Alice waiting for final result (drain/tail phases)
   - AP_ret: Protocol finished

   The `dsdp_inv` is embedded as opaque cargo in each constructor. Downstream
   files never case-split on it — only the infrastructure lemmas here do.

   Also provides `inv_step_gives_inv_ret_val_inv` (moved from dsdp_entropy_trace.v)
   and convenience lemmas that encapsulate ALL 7-way dsdp_inv case splits:
   - inv_alice_ret_terminated: inv + Alice at Ret -> all_terminated
   - inv_alice_at_ret: inv + all_terminated -> Alice at Ret
   - inv_rv_terminated_ret: inv + ret_val_inv + all_terminated -> Ret concrete_val
*)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
Require Import ssr_ext.
Require Import smc_interpreter smc_session_types smc_deadlock.
Require Import homomorphic_encryption.
Require Import dsdp_interface dsdp_session_types dsdp_program.
Require Import dsdp_pismc dsdp_nofail dsdp_progress.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Section dsdp_trace_infra.

Variable AHE : AHEncType.

Let data := std_data AHE.
Let DI := Standard_DSDP_Interface AHE.

Variable ek : party_id -> pub_key AHE.
Variable n_relay : nat.
Hypothesis Hn_relay : (0 < n_relay)%N.
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
Variable r1_relay : 'I_n_relay.+1 -> rand AHE.
Variable r2_relay : 'I_n_relay.+1 -> rand AHE.
Hypothesis dec_total : forall dk' c, @dec AHE dk' c != None.
Hypothesis key_alice : ek alice_idx = pub_of_priv dk.
Hypothesis key_relay : forall j : 'I_n_relay.+1,
  ek (nat_to_party_id j.+1) = pub_of_priv (dk_relay j).

Let n_parties := n_relay.+2.

Let inv := dsdp_inv AHE ek n_relay Hn_relay dk dk_relay relays v0 u r rand_a
  v_relay r1_relay r2_relay.

Let alice_foldr := @alice_foldr_at AHE ek n_relay dk relays v0 u r rand_a.

Let e_local := di_e DI.

Let concrete_val :=
  di_d DI (chain_acc AHE n_relay u r v_relay n_relay.-1 -
     \sum_(j < n_relay.+1) r j + u ord0 * v0).

(* Ghost predicate: if Alice is at Ret d0 then d0 = concrete_val *)
Let ret_val_inv (ps : seq (proc data)) :=
  forall d0, nth (@default_proc data) ps 0 = Ret d0 -> d0 = concrete_val.

(* ========================================================================== *)
(* alice_phase: the simpler 3-constructor invariant                           *)
(* ========================================================================== *)

Inductive alice_phase : nat -> seq (proc data) -> Prop :=
| AP_loop (j : 'I_n_relay.+1) ps :
    inv ps ->
    (nth (@default_proc data) ps 0 = alice_foldr j \/
     exists dest sv, nth (@default_proc data) ps 0 =
       Send dest sv (alice_foldr j.+1)) ->
    alice_phase j ps

| AP_tail ps :
    inv ps ->
    nth (@default_proc data) ps 0 = alice_foldr n_relay.+1 ->
    alice_phase n_relay.+1 ps

| AP_ret ps :
    inv ps ->
    @all_terminated data ps ->
    alice_phase n_relay.+2 ps.

(* ========================================================================== *)
(* Derivation: dsdp_inv -> alice_phase                                        *)
(* ========================================================================== *)

Lemma dsdp_inv_to_alice_phase ps :
  inv ps -> exists j, alice_phase j ps.
Proof.
case.
- (* Inv_AR j *) move=> j ps0 rr Hsz Hwf Halice Hbody Hpending H6 H7 H8 H9.
  exists (j : nat). apply AP_loop.
  + exact: Inv_AR Hsz Hwf Halice Hbody Hpending H6 H7 H8 H9.
  + by left.
- (* Inv_AS0 *) move=> ps0 fi Hsz Hwf Halice Hr0 Hpending Hcont.
  exists 0%N. apply: (fun H1 H2 => @AP_loop (@ord0 n_relay) ps0 H1 H2).
  + exact: Inv_AS0 Hsz Hwf Halice Hr0 Hpending Hcont.
  + right; exists 1%N, (e_local (alice_enc AHE ek n_relay u r rand_a v_relay r1_relay ord0)).
    exact Halice.
- (* Inv_AS1 *) move=> ps0 fi Hsz Hwf Halice Hr0 Hpending Hcont H6a H6b.
  exists 1%N. apply: (fun H1 H2 => @AP_loop (Ordinal (n:=n_relay.+1) (m:=1) Hn_relay) ps0 H1 H2).
  + exact: Inv_AS1 Hsz Hwf Halice Hr0 Hpending Hcont H6a H6b.
  + right; exists 1%N, (e_local (alice_enc AHE ek n_relay u r rand_a v_relay r1_relay (inord 1))).
    exact Halice.
- (* Inv_ASj j *) move=> j ps0 rr Hj Hsz Hwf Halice Hrecv Hpending B7a B7b B8 B9.
  exists (j : nat). apply AP_loop.
  + exact: Inv_ASj Hj Hsz Hwf Halice Hrecv Hpending B7a B7b B8 B9.
  + right; exists (j : nat), (e_local (alice_enc AHE ek n_relay u r rand_a v_relay r1_relay j)).
    exact Halice.
- (* Inv_drain *) move=> j ps0 rr Hj Hsz Hwf Halice Hsend Hrecv Hfin Hlast Hbetween.
  exists n_relay.+1. apply AP_tail.
  + exact: Inv_drain Hj Hsz Hwf Halice Hsend Hrecv Hfin Hlast Hbetween.
  + exact Halice.
- (* Inv_tail *) move=> ps0 rr Hsz Hwf Hsend Halice Hrels.
  exists n_relay.+1. apply AP_tail.
  + exact: Inv_tail Hsz Hwf Hsend Halice Hrels.
  + exact Halice.
- (* Inv_ret *) move=> ps0 d0 Hsz Hwf Hret Hrels.
  exists n_relay.+2. apply AP_ret.
  + exact: Inv_ret Hsz Hwf Hret Hrels.
  + apply /(@all_nthP _ _ _ (@default_proc data)).
    rewrite Hsz => i Hi; case: i Hi => [|i] Hi.
    * by rewrite Hret.
    * have Him : (i < n_relay.+1)%N by rewrite ltnS in Hi.
      by have := Hrels (Ordinal Him); rewrite /relay_at_finish_pred /= => ->.
Qed.

(* ========================================================================== *)
(* Helper: extract inv from alice_phase                                       *)
(* ========================================================================== *)

Lemma alice_phase_inv j ps :
  alice_phase j ps -> inv ps.
Proof. by case. Qed.

(* ========================================================================== *)
(* Moved from dsdp_entropy_trace.v: 7-way case-split proofs                   *)
(* These are the ONLY lemmas that case-split on dsdp_inv directly.            *)
(* Downstream files use alice_phase wrappers or convenience lemmas instead.   *)
(* ========================================================================== *)

(* Helper: From ~~ all_terminated, dsdp_inv_step gives inv + ret_val_inv. *)
Lemma inv_step_gives_inv_ret_val_inv ps :
  inv ps -> ~~ @all_terminated data ps ->
  inv (@one_step_procs data ps) /\ ret_val_inv (@one_step_procs data ps).
Proof.
move=> Hinv Hnterm.
have Hstep := @dsdp_inv_step AHE ek n_relay Hn_relay dk dk_relay
  dec_total key_relay relays Hrelays Hrelays_id v0 u r rand_a v_relay
  r1_relay r2_relay ps Hinv.
case: Hstep => [Hterm | Hinv'].
{ (* Left branch: all_terminated (one_step_procs data ps) *)
  case: {+}Hinv Hnterm Hterm.
  - (* Inv_AR j *) move=> j ps0 rr Hsz Hwf Halice Hbody Hpend H6 H7 H8 H9 Hnterm Hterm.
    exfalso.
    move/(@all_nthP _ _ _ (@default_proc data)): Hterm.
    rewrite (@size_one_step data) Hsz => /(_ 0 (ltn0Sn _)).
    have Hsz0 : (0 < size ps0)%N by rewrite Hsz.
    have [fA HfA] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays
      Hrelays_id v0 u r rand_a j (ltn_ord j).
    have Hrecv : nth (@default_proc data) ps0 0 = Recv (Ordinal (ltn_ord j)).+1 fA
      by rewrite Halice /alice_foldr_at HfA.
    have [sk Hsk] := @relay_body_is_send0 AHE ek n_relay dk_relay v_relay r1_relay r2_relay j.
    rewrite /relay_at_body Hsk in Hbody.
    have [_ Hstep_recv] := @step_send_recv_match data ps0 j.+1 0
      (di_e DI (enc (ek (nat_to_party_id j.+1)) (v_relay j) (r1_relay j))) sk fA Hbody Hrecv.
    rewrite (@nth_one_step data ps0 0 Hsz0) Hstep_recv.
    set vv := di_e DI _.
    have Henc : @std_from_enc AHE vv != None by rewrite /vv std_from_enc_e_local.
    have [sv [rest Hsend]] := @alice_recv_to_send AHE ek n_relay dk relays Hrelays
      Hrelays_id v0 u r rand_a j (ltn_ord j) fA vv Henc HfA.
    by rewrite Hsend.
  - (* Inv_AS0 *) move=> ps0 f_inner Hsz Hwf Halice Hr0 Hpend Hcont Hnterm Hterm.
    exfalso.
    move/(@all_nthP _ _ _ (@default_proc data)): Hterm.
    rewrite (@size_one_step data) Hsz => /(_ 0 (ltn0Sn _)).
    have Hsz0 : (0 < size ps0)%N by rewrite Hsz.
    rewrite (@nth_one_step data ps0 0 Hsz0) /smc_interpreter.step Halice Hr0 eqxx.
    have [fA HfA] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays
      Hrelays_id v0 u r rand_a 1 Hn_relay.
    by rewrite /alice_foldr_at HfA.
  - (* Inv_AS1 *) move=> ps0 f_inner Hsz Hwf Halice Hr0 Hpend Hcont H6a H6b Hnterm Hterm.
    exfalso.
    move/(@all_nthP _ _ _ (@default_proc data)): Hterm.
    rewrite (@size_one_step data) Hsz => /(_ 0 (ltn0Sn _)).
    have Hsz0 : (0 < size ps0)%N by rewrite Hsz.
    rewrite (@nth_one_step data ps0 0 Hsz0) /smc_interpreter.step Halice Hr0 eqxx.
    case: (ltnP 2 n_relay.+1) => H2.
    + have [fA HfA] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays
        Hrelays_id v0 u r rand_a 2 H2.
      by rewrite /alice_foldr_at HfA.
    + have Hn1 : n_relay = 1%N.
        apply /eqP; rewrite eqn_leq Hn_relay andbT -ltnS; exact H2.
      have [fA HfA] := @alice_tail_is_recv AHE n_relay dk v0 u r.
      rewrite -(@alice_foldr_at_tail AHE ek n_relay dk relays Hrelays v0 u r rand_a) in HfA.
      subst n_relay; by rewrite HfA.
  - (* Inv_ASj j *) move=> j ps0 rr Hj Hsz Hwf Halice Hrecv Hpend B7a B7b B8 B9 Hnterm Hterm.
    exfalso.
    move/(@all_nthP _ _ _ (@default_proc data)): Hterm.
    rewrite (@size_one_step data) Hsz => /(_ 0 (ltn0Sn _)).
    have Hsz0 : (0 < size ps0)%N by rewrite Hsz.
    have [sv0 [f0 [Hrb Hrecv0]]] := Hrecv.
    rewrite (@nth_one_step data ps0 0 Hsz0) /smc_interpreter.step Halice Hrecv0 eqxx.
    case: (ltnP j.+1 n_relay.+1) => Hj1.
    + have [fA HfA] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays
        Hrelays_id v0 u r rand_a j.+1 Hj1.
      by rewrite /alice_foldr_at HfA.
    + have Hjeq : j.+1 = n_relay.+1.
        by apply /eqP; rewrite eqn_leq Hj1 (ltn_ord j).
      have [fA HfA] := @alice_tail_is_recv AHE n_relay dk v0 u r.
      rewrite -(@alice_foldr_at_tail AHE ek n_relay dk relays Hrelays v0 u r rand_a) in HfA.
      by rewrite Hjeq HfA.
  - (* Inv_drain *) move=> j ps0 rr Hjb Hsz Hwf Halice Hsend_j Hrecv_j2 Hfin Hlast Hbtw Hnterm Hterm.
    exfalso.
    move/(@all_nthP _ _ _ (@default_proc data)): Hterm.
    rewrite (@size_one_step data) Hsz => /(_ 0 (ltn0Sn _)).
    have Hsz0 : (0 < size ps0)%N by rewrite Hsz.
    rewrite (@nth_one_step data ps0 0 Hsz0) /smc_interpreter.step.
    have [fA HfA] := @alice_tail_is_recv AHE n_relay dk v0 u r.
    rewrite Halice (@alice_foldr_at_tail AHE ek n_relay dk relays Hrelays v0 u r rand_a) HfA.
    have [f_last [Hlast_eq _]] := Hlast.
    by rewrite Hlast_eq.
  - (* Inv_tail *) move=> ps0 rr_tail Hsz Hwf Hsend Halice Hrels Hnterm Hterm.
    have [f Hrecv_tail] := @alice_tail_is_recv AHE n_relay dk v0 u r.
    have Halice_recv : nth (@default_proc data) ps0 0 = Recv n_relay.+1 f.
      by rewrite Halice (@alice_foldr_at_tail AHE ek n_relay dk relays Hrelays
        v0 u r rand_a) Hrecv_tail.
    set v := di_e DI (enc (ek alice_idx) (chain_acc AHE n_relay u r v_relay n_relay.-1) rr_tail).
    have [Hstep_send Hstep_recv] :=
      @step_send_recv_match data ps0 n_relay.+1 0 v Finish f Hsend Halice_recv.
    have Hfcont : forall v0', @std_from_enc AHE v0' != None -> exists dd, f v0' = Ret dd
      := fun v0' => @alice_tail_recv_ret AHE n_relay dk dec_total v0 u r f v0' Hrecv_tail.
    have Henc : @std_from_enc AHE v != None by rewrite /v std_from_enc_e_local.
    have [dd Hfv] := Hfcont v Henc.
    have Hconcrete : nth (@default_proc data) (one_step_procs data ps0) 0 = Ret concrete_val.
      exact: (@inv_tail_to_ret_concrete AHE ek n_relay dk key_alice relays Hrelays v0 u r rand_a v_relay ps0 rr_tail Hsz Hwf Hsend Halice Hrels).
    split.
    + apply (@Inv_ret AHE ek n_relay Hn_relay dk dk_relay relays v0 u r rand_a v_relay r1_relay r2_relay (one_step_procs data ps0) dd).
      * by rewrite (@size_one_step data).
      * exact (@one_step_preserves_proc_wf AHE ps0 Hwf).
      * have Hsz0 : (0 < size ps0)%N by rewrite Hsz.
        by rewrite (@nth_one_step data ps0 0 Hsz0) Hstep_recv Hfv.
      * move=> j.
        have Hjsz : (j.+1 < size ps0)%N by rewrite Hsz; exact (ltn_ord j).
        rewrite /relay_at_finish_pred (@nth_one_step data ps0 j.+1 Hjsz).
        case: (ltnP j n_relay) => Hjn.
        -- have Hfin := Hrels j Hjn; rewrite /relay_at_finish_pred in Hfin.
           by rewrite /smc_interpreter.step Hfin.
        -- have Hjmax : (j : nat) = n_relay.
             have := ltn_ord j; rewrite ltnS => Hj_le.
             by apply /eqP; rewrite eqn_leq Hj_le Hjn.
           by rewrite Hjmax /smc_interpreter.step Hsend Halice_recv eqxx.
    + move=> d0 Hret. by rewrite Hconcrete in Hret; case: Hret.
  - (* Inv_ret *) move=> ps0 d0 Hsz Hwf Hret Hrels Hnterm _.
    exfalso; apply (negP Hnterm).
    apply /(@all_nthP _ _ _ (@default_proc data)).
    rewrite Hsz => i Hi; case: i Hi => [|i] Hi.
    + by rewrite Hret.
    + have Him : (i < n_relay.+1)%N by rewrite ltnS in Hi.
      by have := Hrels (Ordinal Him); rewrite /relay_at_finish_pred /= => ->. }
(* Right branch: dsdp_inv (one_step_procs data ps) *)
split; first exact Hinv'.
move=> d0 Hret.
case: {+}Hinv Hnterm Hret.
- (* Inv_AR *) move=> j' ps' rr' Hsz' Hwf' Ha' Hbody' _ _ _ _ _ Hnterm' Hret'.
  exfalso.
  have [f' Hf'] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays
    Hrelays_id v0 u r rand_a j' (ltn_ord j').
  have Hrecv' : nth (@default_proc data) ps' 0 = Recv (Ordinal (ltn_ord j')).+1 f'
    by rewrite Ha' /alice_foldr_at Hf'.
  have [sk Hsk] := @relay_body_is_send0 AHE ek n_relay dk_relay v_relay r1_relay r2_relay j'.
  rewrite /relay_at_body Hsk in Hbody'.
  have Hsz0' : (0 < size ps')%N by rewrite Hsz'.
  have [_ Hstep_recv'] := @step_send_recv_match data ps' j'.+1 0
    (di_e DI (enc (ek (nat_to_party_id j'.+1)) (v_relay j') (r1_relay j'))) sk f' Hbody' Hrecv'.
  rewrite (@nth_one_step data ps' 0 Hsz0') Hstep_recv' in Hret'.
  set vv := di_e DI _ in Hret'.
  have Henc : @std_from_enc AHE vv != None by rewrite /vv std_from_enc_e_local.
  have [sv [rest Hsend]] := @alice_recv_to_send AHE ek n_relay dk relays Hrelays
    Hrelays_id v0 u r rand_a j' (ltn_ord j') f' vv Henc Hf'.
  by rewrite Hsend in Hret'.
- (* Inv_AS0 *) move=> ps' fi' Hsz' Hwf' Ha' Hr0' _ _ Hnterm' Hret'.
  have Hsz0' : (0 < size ps')%N by rewrite Hsz'.
  rewrite (@nth_one_step data ps' 0 Hsz0') /smc_interpreter.step Ha' Hr0' eqxx in Hret'.
  have [fA HfA] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays
    Hrelays_id v0 u r rand_a 1 Hn_relay.
  by rewrite /alice_foldr_at HfA in Hret'.
- (* Inv_AS1 *) move=> ps' fi' Hsz' Hwf' Ha' Hr0' _ _ _ _ Hnterm' Hret'.
  have Hsz0' : (0 < size ps')%N by rewrite Hsz'.
  rewrite (@nth_one_step data ps' 0 Hsz0') /smc_interpreter.step Ha' Hr0' eqxx in Hret'.
  case: (ltnP 2 n_relay.+1) => H2.
  + have [fA HfA] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays
      Hrelays_id v0 u r rand_a 2 H2.
    by rewrite /alice_foldr_at HfA in Hret'.
  + have Hn1 : n_relay = 1%N.
      apply /eqP; rewrite eqn_leq Hn_relay andbT -ltnS; exact H2.
    have [fA HfA] := @alice_tail_is_recv AHE n_relay dk v0 u r.
    rewrite -(@alice_foldr_at_tail AHE ek n_relay dk relays Hrelays v0 u r rand_a) in HfA.
    subst n_relay; by rewrite HfA in Hret'.
- (* Inv_ASj *) move=> j' ps' rr' Hj' Hsz' Hwf' Ha' Hrecv' _ _ _ _ _ Hnterm' Hret'.
  have Hsz0' : (0 < size ps')%N by rewrite Hsz'.
  have [sv0 [f0 [_ Hrecv0']]] := Hrecv'.
  rewrite (@nth_one_step data ps' 0 Hsz0') /smc_interpreter.step Ha' Hrecv0' eqxx in Hret'.
  case: (ltnP j'.+1 n_relay.+1) => Hj1.
  + have [fA HfA] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays
      Hrelays_id v0 u r rand_a j'.+1 Hj1.
    by rewrite /alice_foldr_at HfA in Hret'.
  + have Hjeq : j'.+1 = n_relay.+1.
      by apply /eqP; rewrite eqn_leq Hj1 (ltn_ord j').
    have [fA HfA] := @alice_tail_is_recv AHE n_relay dk v0 u r.
    rewrite -(@alice_foldr_at_tail AHE ek n_relay dk relays Hrelays v0 u r rand_a) in HfA.
    by rewrite Hjeq HfA in Hret'.
- (* Inv_drain *) move=> j' ps' rr' _ Hsz' Hwf' Ha' _ _ _ Hlast' _ Hnterm' Hret'.
  have Hsz0' : (0 < size ps')%N by rewrite Hsz'.
  have [fA HfA] := @alice_tail_is_recv AHE n_relay dk v0 u r.
  rewrite (@nth_one_step data ps' 0 Hsz0') /smc_interpreter.step
    Ha' (@alice_foldr_at_tail AHE ek n_relay dk relays Hrelays v0 u r rand_a)
    HfA in Hret'.
  have [f_last [Hlast_eq _]] := Hlast'.
  by rewrite Hlast_eq in Hret'.
- (* Inv_tail *) move=> ps' rr' Hsz' Hwf' Hsend' Ha' Hrels' Hnterm' Hret'.
  have Hconcrete := @inv_tail_to_ret_concrete AHE ek n_relay dk key_alice relays Hrelays v0 u r rand_a v_relay ps' rr' Hsz' Hwf' Hsend' Ha' Hrels'.
  by rewrite Hconcrete in Hret'; case: Hret'.
- (* Inv_ret *) move=> ps' d1' Hsz' Hwf' Hret' Hrels' Hnterm' _.
  exfalso; apply (negP Hnterm').
  apply /(@all_nthP _ _ _ (@default_proc data)).
  rewrite Hsz' => i Hi; case: i Hi => [|i] Hi.
  + by rewrite Hret'.
  + have Him : (i < n_relay.+1)%N by rewrite ltnS in Hi.
    by have := Hrels' (Ordinal Him); rewrite /relay_at_finish_pred /= => ->.
Qed.

(* Corollary for the induction *)
Lemma ret_val_inv_preserved_by_step ps :
  inv ps -> ~~ @all_terminated data ps ->
  ret_val_inv (@one_step_procs data ps).
Proof. by move=> Hinv Hnterm; have [] := inv_step_gives_inv_ret_val_inv Hinv Hnterm. Qed.

(* Helper: if inv ps and ~~ all_terminated ps and all_terminated (one_step ps),
   then Alice at Ret concrete_val *)
Lemma inv_step_terminated_concrete ps :
  inv ps -> ~~ @all_terminated data ps ->
  @all_terminated data (@one_step_procs data ps) ->
  nth (@default_proc data) (@one_step_procs data ps) 0 = Ret concrete_val.
Proof.
move=> Hinv Hnterm Hterm'.
have [Hinv' Hret_val_inv'] := inv_step_gives_inv_ret_val_inv Hinv Hnterm.
case: Hinv' Hterm' Hret_val_inv'.
- move=> j ps' rr Hsz Hwf Halice _ _ _ _ _ _ Hterm' Hg.
  have [f Hf] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays
    Hrelays_id v0 u r rand_a j (ltn_ord j).
  have : is_terminal (nth (@default_proc data) ps' 0)
    by move/(@all_nthP _ _ _ (@default_proc data)): Hterm'; apply; rewrite Hsz.
  by rewrite Halice /alice_foldr_at Hf.
- move=> ps' f_inner Hsz Hwf Halice _ _ _ Hterm' Hg.
  have : is_terminal (nth (@default_proc data) ps' 0)
    by move/(@all_nthP _ _ _ (@default_proc data)): Hterm'; apply; rewrite Hsz.
  by rewrite Halice.
- move=> ps' f_inner Hsz Hwf Halice _ _ _ _ _ Hterm' Hg.
  have : is_terminal (nth (@default_proc data) ps' 0)
    by move/(@all_nthP _ _ _ (@default_proc data)): Hterm'; apply; rewrite Hsz.
  by rewrite Halice.
- move=> j ps' rr Hj Hsz Hwf Halice _ _ _ _ _ _ Hterm' Hg.
  have : is_terminal (nth (@default_proc data) ps' 0)
    by move/(@all_nthP _ _ _ (@default_proc data)): Hterm'; apply; rewrite Hsz.
  by rewrite Halice.
- move=> j ps' rr Hj Hsz Hwf Halice _ _ _ _ _ Hterm' Hg.
  have [f Hf] := @alice_tail_is_recv AHE n_relay dk v0 u r.
  have : is_terminal (nth (@default_proc data) ps' 0)
    by move/(@all_nthP _ _ _ (@default_proc data)): Hterm'; apply; rewrite Hsz.
  by rewrite Halice (@alice_foldr_at_tail AHE ek n_relay dk relays Hrelays
    v0 u r rand_a) Hf.
- move=> ps' rr Hsz Hwf _ Halice _ Hterm' Hg.
  have [f Hf] := @alice_tail_is_recv AHE n_relay dk v0 u r.
  have : is_terminal (nth (@default_proc data) ps' 0)
    by move/(@all_nthP _ _ _ (@default_proc data)): Hterm'; apply; rewrite Hsz.
  by rewrite Halice (@alice_foldr_at_tail AHE ek n_relay dk relays Hrelays
    v0 u r rand_a) Hf.
- move=> ps' d0 Hsz Hwf Hret Hrels Hterm' Hg.
  by rewrite Hret -(Hg d0 Hret).
Qed.

(* ========================================================================== *)
(* NEW convenience lemmas — encapsulate remaining 7-way patterns              *)
(* ========================================================================== *)

(* inv + Alice at Ret -> all_terminated *)
Lemma inv_alice_ret_terminated ps d0 :
  inv ps -> nth (@default_proc data) ps 0 = Ret d0 ->
  @all_terminated data ps.
Proof.
case.
- (* Inv_AR j *) move=> j ps0 rr Hsz Hwf Halice _ _ _ _ _ _ Hret.
  have [f Hf] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays
    Hrelays_id v0 u r rand_a j (ltn_ord j).
  by rewrite Halice /alice_foldr_at Hf in Hret.
- (* Inv_AS0 *) move=> ps0 fi Hsz Hwf Halice _ _ _ Hret.
  by rewrite Halice in Hret.
- (* Inv_AS1 *) move=> ps0 fi Hsz Hwf Halice _ _ _ _ _ Hret.
  by rewrite Halice in Hret.
- (* Inv_ASj *) move=> j ps0 rr Hj Hsz Hwf Halice _ _ _ _ _ _ Hret.
  by rewrite Halice in Hret.
- (* Inv_drain *) move=> j ps0 rr Hj Hsz Hwf Halice _ _ _ _ _ Hret.
  have [f Hf] := @alice_tail_is_recv AHE n_relay dk v0 u r.
  rewrite Halice (@alice_foldr_at_tail AHE ek n_relay dk relays Hrelays
    v0 u r rand_a) Hf in Hret.
  by [].
- (* Inv_tail *) move=> ps0 rr Hsz Hwf _ Halice _ Hret.
  have [f Hf] := @alice_tail_is_recv AHE n_relay dk v0 u r.
  rewrite Halice (@alice_foldr_at_tail AHE ek n_relay dk relays Hrelays
    v0 u r rand_a) Hf in Hret.
  by [].
- (* Inv_ret *) move=> ps0 d1 Hsz Hwf Hret Hrels _.
  apply /(@all_nthP _ _ _ (@default_proc data)).
  rewrite Hsz => i Hi; case: i Hi => [|i] Hi.
  + by rewrite Hret.
  + have Him : (i < n_relay.+1)%N by rewrite ltnS in Hi.
    by have := Hrels (Ordinal Him); rewrite /relay_at_finish_pred /= => ->.
Qed.

(* inv + all_terminated -> Alice at Ret *)
Lemma inv_alice_at_ret ps :
  inv ps -> @all_terminated data ps ->
  exists d, nth (@default_proc data) ps 0 = Ret d.
Proof.
case.
- (* Inv_AR j *) move=> j ps0 rr Hsz Hwf Halice _ _ _ _ _ _ Hterm.
  exfalso.
  have [f Hf] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays
    Hrelays_id v0 u r rand_a j (ltn_ord j).
  have : is_terminal (nth (@default_proc data) ps0 0)
    by move/(@all_nthP _ _ _ (@default_proc data)): Hterm; apply; rewrite Hsz.
  by rewrite Halice /alice_foldr_at Hf.
- (* Inv_AS0 *) move=> ps0 fi Hsz Hwf Halice _ _ _ Hterm.
  exfalso.
  have : is_terminal (nth (@default_proc data) ps0 0)
    by move/(@all_nthP _ _ _ (@default_proc data)): Hterm; apply; rewrite Hsz.
  by rewrite Halice.
- (* Inv_AS1 *) move=> ps0 fi Hsz Hwf Halice _ _ _ _ _ Hterm.
  exfalso.
  have : is_terminal (nth (@default_proc data) ps0 0)
    by move/(@all_nthP _ _ _ (@default_proc data)): Hterm; apply; rewrite Hsz.
  by rewrite Halice.
- (* Inv_ASj *) move=> j ps0 rr Hj Hsz Hwf Halice _ _ _ _ _ _ Hterm.
  exfalso.
  have : is_terminal (nth (@default_proc data) ps0 0)
    by move/(@all_nthP _ _ _ (@default_proc data)): Hterm; apply; rewrite Hsz.
  by rewrite Halice.
- (* Inv_drain *) move=> j ps0 rr Hj Hsz Hwf Halice _ _ _ _ _ Hterm.
  exfalso.
  have [f Hf] := @alice_tail_is_recv AHE n_relay dk v0 u r.
  have : is_terminal (nth (@default_proc data) ps0 0)
    by move/(@all_nthP _ _ _ (@default_proc data)): Hterm; apply; rewrite Hsz.
  by rewrite Halice (@alice_foldr_at_tail AHE ek n_relay dk relays Hrelays
    v0 u r rand_a) Hf.
- (* Inv_tail *) move=> ps0 rr Hsz Hwf _ Halice _ Hterm.
  exfalso.
  have [f Hf] := @alice_tail_is_recv AHE n_relay dk v0 u r.
  have : is_terminal (nth (@default_proc data) ps0 0)
    by move/(@all_nthP _ _ _ (@default_proc data)): Hterm; apply; rewrite Hsz.
  by rewrite Halice (@alice_foldr_at_tail AHE ek n_relay dk relays Hrelays
    v0 u r rand_a) Hf.
- (* Inv_ret *) move=> ps0 d1 Hsz Hwf Hret _ _.
  by exists d1.
Qed.

(* inv + ret_val_inv + all_terminated -> Ret concrete_val *)
Lemma inv_rv_terminated_ret ps :
  inv ps -> ret_val_inv ps -> @all_terminated data ps ->
  nth (@default_proc data) ps 0 = Ret concrete_val.
Proof.
move=> Hinv Hrv Hterm.
have [d0 Hd0] := inv_alice_at_ret Hinv Hterm.
by rewrite Hd0; congr Ret; exact: Hrv.
Qed.

(* ========================================================================== *)
(* alice_phase interface lemmas                                               *)
(* ========================================================================== *)

(* Helper: inv + ~~ all_terminated -> inv stays after step *)
Lemma inv_step_inv ps0 :
  inv ps0 -> ~~ @all_terminated data ps0 ->
  inv (@one_step_procs data ps0).
Proof.
move=> Hinv Hnterm.
have [Hinv' _] := inv_step_gives_inv_ret_val_inv Hinv Hnterm.
exact Hinv'.
Qed.

(* Progress: non-terminal phases always have progress *)
Lemma alice_phase_has_progress j ps :
  alice_phase j ps -> (j < n_relay.+2)%N -> @has_progress data ps.
Proof.
move=> Hap Hlt.
have Hinv := alice_phase_inv Hap.
exact: (@dsdp_inv_has_progress _ _ _ Hn_relay _ _ _ Hrelays Hrelays_id _ _ _ _ _ _ _ _ Hinv).
Qed.

(* Helper: inv implies size = n_relay.+2 *)
Lemma inv_size ps0 : inv ps0 -> size ps0 = n_relay.+2.
Proof. by case=> *. Qed.

(* Non-terminal phases aren't terminated *)
Lemma alice_phase_not_terminated j ps :
  alice_phase j ps -> (j < n_relay.+2)%N -> ~~ @all_terminated data ps.
Proof.
case.
- (* AP_loop *)
  move=> j' ps' Hinv [Halice | [dest [sv Halice]]] Hlt;
    apply /negP => /(@all_nthP _ _ _ (@default_proc data));
    rewrite (inv_size Hinv) => Hall; have := Hall 0 (ltn0Sn _).
  + rewrite Halice /alice_foldr /alice_foldr_at.
    by case: (@alice_body_at_recv AHE ek n_relay dk relays Hrelays Hrelays_id v0 u r rand_a j' (ltn_ord j')) => f ->.
  + by rewrite Halice.
- (* AP_tail *) move=> ps' Hinv Halice Hlt.
  apply /negP => /(@all_nthP _ _ _ (@default_proc data)).
  rewrite (inv_size Hinv) => Hall; have := Hall 0 (ltn0Sn _).
  rewrite Halice /alice_foldr (@alice_foldr_at_tail AHE ek n_relay dk relays Hrelays v0 u r rand_a).
  by case: (@alice_tail_is_recv AHE n_relay dk v0 u r) => f ->.
- (* AP_ret *) move=> ps' Hinv Hterm Hlt.
  by rewrite ltnn in Hlt.
Qed.

(* Step preservation: after one step, phase advances or stays *)
Lemma alice_phase_step j ps :
  alice_phase j ps -> ~~ @all_terminated data ps ->
  exists j', alice_phase j' (@one_step_procs data ps).
Proof.
move=> Hap Hnterm.
have Hinv : inv ps by case: Hap.
have Hinv' := inv_step_inv Hinv Hnterm.
exact: dsdp_inv_to_alice_phase Hinv'.
Qed.

(* Return value correctness *)
Lemma alice_phase_ret_val j ps :
  alice_phase j ps -> ~~ @all_terminated data ps ->
  forall d, nth (@default_proc data) (@one_step_procs data ps) 0 = Ret d ->
  d = concrete_val.
Proof.
move=> Hap Hnterm d Hret.
have Hinv : inv ps by case: Hap.
have [_ Hrv] := inv_step_gives_inv_ret_val_inv Hinv Hnterm.
exact: Hrv Hret.
Qed.

(* Terminal step correctness *)
Lemma alice_phase_terminated_concrete j ps :
  alice_phase j ps -> ~~ @all_terminated data ps ->
  @all_terminated data (@one_step_procs data ps) ->
  nth (@default_proc data) (@one_step_procs data ps) 0 =
    Ret concrete_val.
Proof.
move=> Hap Hnterm Hterm'.
have Hinv : inv ps by case: Hap.
exact: inv_step_terminated_concrete Hinv Hnterm Hterm'.
Qed.

End dsdp_trace_infra.
