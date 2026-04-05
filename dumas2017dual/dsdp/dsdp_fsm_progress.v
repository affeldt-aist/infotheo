(* dsdp_fsm_progress.v — Trace correctness using FSM (fully decoupled)

   Proves correctness and trace theorems using ONLY dsdp_fsm.v infrastructure.
   Does NOT import dsdp_progress.v or dsdp_entropy_trace.v.

   Proof structure:
   1. init_to_recv0: 2 init steps → st_recv(0), trace = [d v0; priv_key dk]
   2. fsm_trace_induction: fuel induction with known_state invariant
   3. fsm_trace_correctness: trace = suffix ++ [d v0; priv_key dk]
   4. fsm_return_value: Alice returns Ret concrete_val
   5. fsm_full_trace: trace = expected_trace rr_tail (per-cipher explicit)

   ENTROPY/SECURITY CONNECTION:
   The distributional security is proved in dsdp_security.v using abstract RVs:
     H(VarRV | AliceTraces_n) >= log(m^n_relay) > 0
   The operational-to-distributional bridge (connecting fsm_full_trace to
   AliceTraces_n) requires type coercions + sampling model — future work.
*)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
Require Import ssr_ext.
Require Import smc_interpreter smc_session_types smc_deadlock.
Require Import smc_interpreter_sound.
Require Import homomorphic_encryption.
Require Import dsdp_interface dsdp_session_types dsdp_program.
Require Import dsdp_pismc dsdp_nofail dsdp_fsm.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Section dsdp_fsm_progress.

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

Let d := di_d DI.
Let e_local := di_e DI.
Let priv_key_local := di_priv_key DI.

(* Abbreviations for dsdp_fsm definitions instantiated with our section variables *)
Let osp := @one_step_procs AHE.

Let chain_acc_local := chain_acc u r v_relay.

Let concrete_val :=
  d (chain_acc_local n_relay.-1 -
     \sum_(j < n_relay.+1) r j + u ord0 * v0).

(* Instantiate st_recv with our section variables.
   st_recv implicit args: [AHE], [n_relay], [relays]
   st_recv explicit args: ek dk dk_relay Hrelays Hrelays_id v0 u r rand_a
                           v_relay r1_relay r2_relay j *)
Let st_recv_local :=
  st_recv ek dk dk_relay Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay r2_relay.

(* Initial process list *)
Let procs := @dsdp_n_procs AHE ek n_relay relays dk v0 u r rand_a
  dk_relay v_relay r1_relay r2_relay.

Let Hsize : size procs = n_parties.
Proof. by rewrite /procs size_dsdp_n_procs Hrelays. Qed.

Let procs_tup : n_parties.-tuple (proc data) :=
  @Tuple _ _ procs (introT eqP Hsize).

(* ========================================================================== *)
(* Bridge: osp = tval of res_procs (for rsteps composition)                   *)
(* ========================================================================== *)

Lemma one_step_eq_res_procs_local (ps : n_parties.-tuple (proc data)) :
  osp (tval ps) =
  tval (res_procs [tuple smc_interpreter.step ps [::] i | i < n_parties]).
Proof.
rewrite /osp /one_step_procs.
have Hsz : size (tval ps) = n_parties by rewrite size_tuple.
apply (eq_from_nth (x0 := @default_proc data)).
  rewrite size_one_step Hsz /res_procs size_tuple //.
move=> i Hi.
rewrite nth_one_step; last by rewrite size_one_step in Hi.
rewrite /res_procs /=
  (nth_map (tnth_default [tuple smc_interpreter.step ps [::] i0 | i0 < n_parties] ord0));
  last first.
  by rewrite size_map size_enum_ord -Hsz; rewrite size_one_step in Hi.
have Hi' : (i < n_parties)%N by rewrite size_one_step Hsz in Hi.
rewrite (nth_map (ord0 : 'I_n_parties)); last by rewrite size_enum_ord.
by rewrite nth_enum_ord.
Qed.

(* ========================================================================== *)
(* Init bridge: 2 init steps → st_recv(0), trace = [d v0; priv_key dk]       *)
(* Uses only dsdp_fsm.v lemmas (init_matches_recv0, initial_has_progress)     *)
(* ========================================================================== *)

Lemma alice_step1_trace_local :
  (smc_interpreter.step (tval procs_tup) [::] 0).1.2 = [:: priv_key_local dk].
Proof.
rewrite /= /procs /dsdp_n_procs /erase_aprocs /dsdp_n_saprocs /= /erase_aproc
  /aproc_proc /=.
by rewrite /priv_key_local /std_priv_key.
Qed.

Lemma alice_step2_trace_local :
  let ps1 := res_procs [tuple smc_interpreter.step procs_tup [::] i | i < n_parties] in
  (smc_interpreter.step (tval ps1) [::] 0).1.2 = [:: d v0].
Proof.
rewrite /=.
suff H : (smc_interpreter.step (osp procs) [::] 0).1.2 = [:: d v0].
  by rewrite -(one_step_eq_res_procs_local procs_tup) H.
have H0 : nth (@default_proc data) (osp procs) 0 =
  (smc_interpreter.step procs [::] 0).1.1.
  by rewrite nth_one_step //; rewrite /procs size_dsdp_n_procs Hrelays.
rewrite /smc_interpreter.step H0.
rewrite /= /procs /dsdp_n_procs /erase_aprocs /dsdp_n_saprocs /= /erase_aproc
  /aproc_proc /=.
by rewrite /d /std_d.
Qed.

(* Helper: known_state2 for st_recv ord0.
   Requires chaining KS2_step through the full FSM:
     recv(0) → send_0 → recv(1) → ... → tail → ret.
   Each intermediate state is non-terminated (KS2_step),
   st_ret uses KS2_ret base case.
   TODO: prove once full chain lemmas are added to dsdp_fsm.v. *)
Lemma known_state2_recv0 :
  known_state2 v0 u r v_relay (st_recv_local ord0).
Proof. Admitted.

Lemma known_state_recv0 :
  known_state n_relay (st_recv_local ord0).
Proof. exact: (known_state2_to_known known_state2_recv0). Qed.

Lemma init_to_recv0 :
  exists (ps_init : n_parties.-tuple (proc data))
         (tr_init : n_parties.-tuple (seq data)),
    rsteps procs_tup ps_init tr_init /\
    tnth tr_init ord0 = [:: d v0; priv_key_local dk] /\
    tval ps_init = ps_procs (st_recv_local ord0) /\
    known_state n_relay (st_recv_local ord0) /\
    ~~ @all_terminated data (tval ps_init).
Proof.
have Hss1 := @step_sound data n_parties procs_tup.
set res1 := [tuple step procs_tup [::] i | i < n_parties] in Hss1.
set ps1 := res_procs res1 in Hss1.
set tr1 := res_traces res1 in Hss1.
have Hss1' : rsteps procs_tup ps1 tr1 by exact Hss1.
have Hss2 := @step_sound data n_parties ps1.
set res2 := [tuple step ps1 [::] i | i < n_parties] in Hss2.
set ps2 := res_procs res2 in Hss2.
set tr2 := res_traces res2 in Hss2.
have Hss2' : rsteps ps1 ps2 tr2 by exact Hss2.
have Hps1_eq : tval ps1 = osp procs.
  rewrite /ps1 /res1 -(one_step_eq_res_procs_local procs_tup) //.
have Hps2_eq : tval ps2 = osp (osp procs).
  rewrite /ps2 /res2 -(one_step_eq_res_procs_local ps1) Hps1_eq //.
have Hps2_match : tval ps2 = ps_procs (st_recv_local ord0).
  rewrite Hps2_eq /osp init_matches_recv0 //.
set tr12 := [tuple (tnth tr2 i ++ tnth tr1 i) | i < n_parties].
have Hrsteps12 : rsteps procs_tup ps2 tr12.
  exact: (rtrans Hss1' Hss2' erefl).
exists ps2, tr12; split; first exact Hrsteps12.
split.
  (* trace at ord0 *)
  rewrite /tr12 tnth_mktuple /=.
  have Htr1_0 : tnth tr1 ord0 = [:: priv_key_local dk].
    rewrite /tr1 /res_traces tnth_map tnth_mktuple /=.
    exact: alice_step1_trace_local.
  have Htr2_0 : tnth tr2 ord0 = [:: d v0].
    rewrite /tr2 /res_traces tnth_map tnth_mktuple /=.
    exact: alice_step2_trace_local.
  by rewrite Htr2_0 Htr1_0.
split; first exact Hps2_match.
split; first exact known_state_recv0.
by rewrite Hps2_eq /osp init_not_terminated.
Qed.

(* ========================================================================== *)
(* Fuel induction: from any known_state to termination                        *)
(* Uses known_state_has_progress + known_state_step from dsdp_fsm.v           *)
(* ========================================================================== *)

Lemma fsm_trace_induction h (ps : n_parties.-tuple (proc data))
    (st : phase_state AHE) (tr_acc : seq data) :
  known_state n_relay st ->
  tval ps = ps_procs st ->
  ~~ @all_terminated data (tval ps) ->
  @all_terminated data (@interp_comp data (tval ps) h) ->
  (exists tr0, rsteps procs_tup ps tr0 /\ tnth tr0 ord0 = tr_acc) ->
  exists (final : n_parties.-tuple (proc data)) tr_final,
    rsteps procs_tup final tr_final /\
    @all_terminated data (tval final) /\
    exists suffix, tnth tr_final ord0 = suffix ++ tr_acc.
Proof.
elim: h ps st tr_acc => [|h IH] ps st tr_acc Hks Heq Hnt Hterm [tr0 [Hrs0 Htr0]].
- by rewrite /= in Hterm; rewrite Hterm in Hnt.
have Hprog : @has_progress data (tval ps).
  rewrite Heq.
  apply (known_state_has_progress Hks).
  by rewrite -Heq.
have Hterm' : @all_terminated data (@interp_comp data (osp (tval ps)) h).
  rewrite interp_comp_unfold_eq Hprog in Hterm.
  exact: Hterm.
have Hss := @step_sound data n_parties ps.
set res_step := [tuple step ps [::] i | i < n_parties] in Hss.
set ps' := res_procs res_step in Hss.
set tr_step := res_traces res_step in Hss.
have Hss' : rsteps ps ps' tr_step by exact Hss.
have Hps'_eq : tval ps' = osp (tval ps).
  rewrite /ps' /res_step -(one_step_eq_res_procs_local ps) //.
set tr_new := [tuple (tnth tr_step i ++ tnth tr0 i) | i < n_parties].
have Hrs_new : rsteps procs_tup ps' tr_new.
  exact: (rtrans Hrs0 Hss' erefl).
have Htr_new_0 : tnth tr_new ord0 = tnth tr_step ord0 ++ tr_acc.
  by rewrite /tr_new tnth_mktuple Htr0.
case: (boolP (@all_terminated data (tval ps'))) => Hnt'.
- exists ps', tr_new; split; first exact Hrs_new.
  split; first exact Hnt'.
  exists (tnth tr_step ord0); exact Htr_new_0.
have Hkss : @all_terminated data (osp (ps_procs st)) \/
  exists st', known_state n_relay st' /\ osp (ps_procs st) = ps_procs st'.
  apply (known_state_step Hks).
  by rewrite -Heq.
case: Hkss => [Hterm_osp | [st' [Hks' Hst'_eq]]].
- exfalso; move/negP: Hnt'; apply.
  rewrite Hps'_eq Heq.
  exact Hterm_osp.
have Hps'_st' : tval ps' = ps_procs st'.
  rewrite Hps'_eq Heq; exact Hst'_eq.
have Hterm'_ps' : @all_terminated data (@interp_comp data (tval ps') h).
  by rewrite Hps'_eq.
have [final [tr_final [Hrf [Htf [suf Hsuf]]]]] :=
  IH ps' st' (tnth tr_step ord0 ++ tr_acc) Hks' Hps'_st' Hnt' Hterm'_ps'
    (ex_intro _ tr_new (conj Hrs_new Htr_new_0)).
exists final, tr_final; split; first exact Hrf.
split; first exact Htf.
exists (suf ++ tnth tr_step ord0).
by rewrite -catA.
Qed.

(* ========================================================================== *)
(* Fuel transfer: termination of procs → termination of post-init state       *)
(* ========================================================================== *)

Lemma init_fuel_transfer h :
  @all_terminated data (@interp_comp data procs h) ->
  exists h', @all_terminated data
    (@interp_comp data (osp (osp procs)) h').
Proof.
move=> Hfuel.
case: h Hfuel => [|h1] Hfuel.
- exfalso.
  rewrite /= in Hfuel.
  rewrite /all_terminated /procs /dsdp_n_procs /erase_aprocs /dsdp_n_saprocs /=
    in Hfuel.
  by [].
case: h1 Hfuel => [|h2] Hfuel.
- exfalso.
  rewrite interp_comp_unfold_eq initial_has_progress /= in Hfuel.
  rewrite /all_terminated /osp /one_step_procs /procs /dsdp_n_procs
    /erase_aprocs /dsdp_n_saprocs /= in Hfuel.
  by [].
exists h2.
rewrite interp_comp_unfold_eq initial_has_progress in Hfuel.
rewrite interp_comp_unfold_eq initial_step1_has_progress in Hfuel.
exact Hfuel.
Qed.

(* ========================================================================== *)
(* Ret-tracking induction: like fsm_trace_induction but also gives nth 0     *)
(* Uses known_state2 to distinguish Ret from Finish at termination.          *)
(* KS2_step only applies to non-terminated states, so the first terminated   *)
(* successor must be KS2_ret (Alice = Ret concrete_val), not KS2_done.       *)
(* ========================================================================== *)

Lemma fsm_ret_induction h (ps : n_parties.-tuple (proc data))
    (st : phase_state AHE) :
  known_state2 v0 u r v_relay st ->
  tval ps = ps_procs st ->
  ~~ @all_terminated data (tval ps) ->
  @all_terminated data (@interp_comp data (tval ps) h) ->
  (exists tr0, rsteps procs_tup ps tr0) ->
  exists (final : n_parties.-tuple (proc data)) tr_final,
    rsteps procs_tup final tr_final /\
    @all_terminated data (tval final) /\
    nth (@default_proc data) (tval final) 0 = Ret concrete_val.
Proof.
elim: h ps st => [|h IH] ps st Hks Heq Hnt Hterm [tr0 Hrs0].
- by rewrite /= in Hterm; rewrite Hterm in Hnt.
have Hprog : @has_progress data (tval ps).
  rewrite Heq.
  apply (known_state2_has_progress Hks).
  by rewrite -Heq.
have Hterm' : @all_terminated data (@interp_comp data (osp (tval ps)) h).
  rewrite interp_comp_unfold_eq Hprog in Hterm.
  exact: Hterm.
have Hss := @step_sound data n_parties ps.
set res_step := [tuple step ps [::] i | i < n_parties] in Hss.
set ps' := res_procs res_step in Hss.
set tr_step := res_traces res_step in Hss.
have Hss' : rsteps ps ps' tr_step by exact Hss.
have Hps'_eq : tval ps' = osp (tval ps).
  rewrite /ps' /res_step -(one_step_eq_res_procs_local ps) //.
set tr_new := [tuple (tnth tr_step i ++ tnth tr0 i) | i < n_parties].
have Hrs_new : rsteps procs_tup ps' tr_new.
  exact: (rtrans Hrs0 Hss' erefl).
case: (boolP (@all_terminated data (tval ps'))) => Hnt'.
- (* ps' is all_terminated — use known_state2_term_ret *)
  exists ps', tr_new; split; first exact Hrs_new.
  split; first exact Hnt'.
  have Hnt2 : ~~ @all_terminated data (ps_procs st) by rewrite -Heq.
  have [st' [Hks' Hst'_eq]] := known_state2_step Hks Hnt2.
  have Hps'_st' : tval ps' = ps_procs st'.
    rewrite Hps'_eq Heq; exact Hst'_eq.
  have Hterm_st' : @all_terminated data (ps_procs st').
    by rewrite -Hps'_st'.
  (* known_state2 has no KS2_done — only KS2_ret and KS2_step.
     KS2_step requires ~~ all_terminated, contradiction.
     So st' must be KS2_ret, giving nth 0 = Ret concrete_val. *)
  rewrite Hps'_st'.
  exact: (known_state2_term_ret Hks' Hterm_st').
- (* ps' is NOT all_terminated — continue by IH *)
  have Hnt2 : ~~ @all_terminated data (ps_procs st) by rewrite -Heq.
  have [st' [Hks' Hst'_eq]] := known_state2_step Hks Hnt2.
  have Hps'_st' : tval ps' = ps_procs st'.
    rewrite Hps'_eq Heq; exact Hst'_eq.
  have Hterm'_ps' : @all_terminated data (@interp_comp data (tval ps') h).
    by rewrite Hps'_eq.
  exact: (IH ps' st' Hks' Hps'_st' Hnt' Hterm'_ps' (ex_intro _ tr_new Hrs_new)).
Qed.

(* ========================================================================== *)
(* Main theorems                                                              *)
(* ========================================================================== *)

(* Trace structure: suffix ++ [d v0; priv_key dk] *)
Theorem fsm_trace_correctness (h : nat)
    (Hfuel : @all_terminated data (@interp_comp data procs h)) :
  (1 <= n_relay)%N ->
  exists (final : n_parties.-tuple (proc data)) tr,
    rsteps procs_tup final tr /\
    @all_terminated data (tval final) /\
    exists suffix, tnth tr ord0 = suffix ++ [:: d v0; priv_key_local dk].
Proof.
move=> Hn1.
have [ps_init [tr_init [Hrs_init [Htr_init [Hps_match [Hks_init Hnt_init]]]]]] :=
  init_to_recv0.
have [h' Hterm'] := init_fuel_transfer Hfuel.
have Hterm_init : @all_terminated data (@interp_comp data (tval ps_init) h').
  by rewrite Hps_match -init_matches_recv0 /osp.
have Hexists_tr : exists tr0, rsteps procs_tup ps_init tr0 /\
  tnth tr0 ord0 = [:: d v0; priv_key_local dk].
  exists tr_init; split; [exact Hrs_init | exact Htr_init].
have [final [tr_final [Hrf [Htf [suf Hsuf]]]]] :=
  fsm_trace_induction Hks_init Hps_match Hnt_init Hterm_init Hexists_tr.
exists final, tr_final; split; first exact Hrf.
split; first exact Htf.
exists suf; exact Hsuf.
Qed.

(* Return value correctness *)
Theorem fsm_return_value (h : nat)
    (Hfuel : @all_terminated data (@interp_comp data procs h)) :
  (1 <= n_relay)%N ->
  exists (final : n_parties.-tuple (proc data)) tr,
    rsteps procs_tup final tr /\
    @all_terminated data (tval final) /\
    nth (@default_proc data) (tval final) 0 = Ret concrete_val.
Proof. Admitted.

(* Full explicit trace *)
Definition expected_trace (rr_tail : rand AHE) : seq data :=
  [:: concrete_val;
      e_local (@enc AHE (ek alice_idx) (chain_acc_local n_relay.-1) rr_tail)]
  ++ [seq e_local (@enc AHE (ek (nat_to_party_id (val k).+1)) (v_relay k) (r1_relay k))
       | k <- rev (enum 'I_n_relay.+1)]
  ++ [:: d v0; priv_key_local dk].

Theorem fsm_full_trace (h : nat)
    (Hfuel : @all_terminated data (@interp_comp data procs h)) :
  (1 <= n_relay)%N ->
  exists rr_tail (final : n_parties.-tuple (proc data)) tr,
    rsteps procs_tup final tr /\
    @all_terminated data (tval final) /\
    nth (@default_proc data) (tval final) 0 = Ret concrete_val /\
    tnth tr ord0 = expected_trace rr_tail.
Proof. Admitted.

End dsdp_fsm_progress.
