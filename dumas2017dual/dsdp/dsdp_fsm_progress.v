(* dsdp_fsm_progress.v — Trace correctness using FSM + dsdp_inv

   Proves the full trace theorem:
     From initial state, protocol terminates with trace ending
     in [d v0; priv_key dk].

   Proof structure:
   1. init_to_inv: 2 init steps → dsdp_inv holds, trace = [d v0; priv_key dk]
   2. fsm_trace_induction: fuel induction threading dsdp_inv + trace accumulator
   3. fsm_trace_correctness: compose init bridge + induction → full trace
*)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
Require Import ssr_ext.
Require Import smc_interpreter smc_session_types smc_deadlock.
Require Import smc_interpreter_sound.
Require Import homomorphic_encryption.
Require Import dsdp_interface dsdp_session_types dsdp_program.
Require Import dsdp_pismc dsdp_nofail dsdp_progress.

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

(* Abbreviation for dsdp_progress.one_step_procs *)
Let osp := dsdp_progress.one_step_procs data.

(* Abbreviation for the dsdp_inv invariant *)
Let inv := dsdp_inv AHE ek n_relay Hn_relay dk dk_relay relays v0 u r rand_a
  v_relay r1_relay r2_relay.

(* Initial process list *)
Let procs := @dsdp_n_procs AHE ek n_relay relays dk v0 u r rand_a
  dk_relay v_relay r1_relay r2_relay.

Let Hsize : size procs = n_parties.
Proof. by rewrite /procs size_dsdp_n_procs Hrelays. Qed.

Let procs_tup : n_parties.-tuple (proc data) :=
  @Tuple _ _ procs (introT eqP Hsize).

(* ========================================================================== *)
(* Bridge: one_step_procs (seq) = tval of res_procs (tuple)                  *)
(* ========================================================================== *)

Lemma one_step_eq_res_procs_local (ps : n_parties.-tuple (proc data)) :
  osp (tval ps) =
  tval (res_procs [tuple smc_interpreter.step ps [::] i | i < n_parties]).
Proof.
apply: (@eq_from_nth _ (default_proc data)).
  by rewrite /osp /dsdp_progress.one_step_procs size_map size_iota
    size_tuple /res_procs size_map size_tuple.
move=> i.
rewrite /osp /dsdp_progress.one_step_procs size_map size_iota size_tuple => Hi.
rewrite (nth_map 0) ?size_iota // nth_iota // add0n /res_procs.
set mt := map_tuple _ _.
have -> : nth (default_proc data) mt i = tnth mt (Ordinal Hi)
  by rewrite (tnth_nth (default_proc data)).
by rewrite /mt tnth_map tnth_mktuple.
Qed.

(* ========================================================================== *)
(* Alice's erased structure and init step traces                              *)
(* ========================================================================== *)

(* Alice's initial process is Init(priv_key dk, Init(d v0, body)) *)
Lemma alice_proc_init_local :
  nth (default_proc data) procs 0 =
  Init (priv_key_local dk) (Init (d v0)
    (foldr (fun (fi : 'I_n_relay.+1 * nat) (cont : proc data) =>
              @alice_erase_body AHE ek n_relay u r rand_a fi.1 fi.2 cont)
           (@alice_erase_tail AHE n_relay dk v0 u r)
           (zip relays (iota 0 (size relays))))).
Proof.
rewrite /procs /dsdp_n_procs /erase_aprocs /dsdp_n_saprocs /= /erase_aproc /=.
exact: (@palice_n_erase AHE ek n_relay relays dk v0 u r rand_a).
Qed.

(* Step 1 trace at Alice (position 0): [priv_key dk] *)
Lemma alice_step1_trace_local :
  (smc_interpreter.step (tval procs_tup) [::] 0).1.2 = [:: priv_key_local dk].
Proof. by rewrite /smc_interpreter.step alice_proc_init_local. Qed.

(* Step 1 result at Alice: Init(d v0, body) *)
Lemma alice_step1_proc_local :
  (smc_interpreter.step (tval procs_tup) [::] 0).1.1 =
  Init (d v0)
    (foldr (fun (fi : 'I_n_relay.+1 * nat) (cont : proc data) =>
              @alice_erase_body AHE ek n_relay u r rand_a fi.1 fi.2 cont)
           (@alice_erase_tail AHE n_relay dk v0 u r)
           (zip relays (iota 0 (size relays)))).
Proof. by rewrite /smc_interpreter.step alice_proc_init_local. Qed.

(* Step 2 trace at Alice (position 0): [d v0] *)
Lemma alice_step2_trace_local :
  let ps1 := res_procs [tuple smc_interpreter.step procs_tup [::] i | i < n_parties] in
  (smc_interpreter.step (tval ps1) [::] 0).1.2 = [:: d v0].
Proof.
rewrite /=.
have Hstep1 : nth (default_proc data) (tval (res_procs [tuple smc_interpreter.step procs_tup [::] i | i < n_parties])) 0 =
  Init (d v0)
    (foldr (fun (fi : 'I_n_relay.+1 * nat) (cont : proc data) =>
              @alice_erase_body AHE ek n_relay u r rand_a fi.1 fi.2 cont)
           (@alice_erase_tail AHE n_relay dk v0 u r)
           (zip relays (iota 0 (size relays)))).
  rewrite -(@one_step_eq_res_procs_local procs_tup).
  have Hsz : (0 < size (tval procs_tup))%N by rewrite size_tuple.
  rewrite (@dsdp_progress.nth_one_step data (tval procs_tup) 0 Hsz)
    /smc_interpreter.step.
  by rewrite alice_proc_init_local.
by rewrite /smc_interpreter.step Hstep1.
Qed.

(* ========================================================================== *)
(* Init bridge: 2 init steps → dsdp_inv, trace = [d v0; priv_key dk]        *)
(* ========================================================================== *)

Lemma init_to_inv :
  exists (ps_init : n_parties.-tuple (proc data))
         (tr_init : n_parties.-tuple (seq data)),
    rsteps procs_tup ps_init tr_init /\
    tnth tr_init ord0 = [:: d v0; priv_key_local dk] /\
    inv (tval ps_init) /\
    ~~ @all_terminated data (tval ps_init) /\
    tval ps_init = osp (osp procs).
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
have Hrs12 : rsteps procs_tup ps2 tr12 := rtrans Hrs1 Hrs2 erefl.
have Heq : tval ps2 = osp (osp procs).
  by rewrite -(@one_step_eq_res_procs_local ps1)
             -(@one_step_eq_res_procs_local procs_tup).
exists ps2, tr12; do !split.
- exact Hrs12.
- rewrite /tr12 tnth_mktuple /tr2 /res_traces tnth_map tnth_mktuple
    /tr1 /res_traces tnth_map tnth_mktuple.
  by rewrite alice_step2_trace_local alice_step1_trace_local.
- rewrite Heq.
  exact: (@dsdp_inv_init AHE ek n_relay Hn_relay dk dk_relay dec_total
    relays Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay r2_relay).
- rewrite Heq.
  exact: (@dsdp_init_not_terminated AHE ek n_relay dk dk_relay relays
    Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay r2_relay).
- exact Heq.
Qed.

(* ========================================================================== *)
(* Fuel induction: from any invariant state to termination                    *)
(* ========================================================================== *)

Lemma fsm_trace_induction h (ps : n_parties.-tuple (proc data))
    (tr_acc : seq data) :
  inv (tval ps) ->
  ~~ all_terminated (tval ps) ->
  all_terminated (interp_comp data (tval ps) h) ->
  (exists tr0, rsteps procs_tup ps tr0 /\ tnth tr0 ord0 = tr_acc) ->
  exists (final : n_parties.-tuple (proc data)) tr_final,
    rsteps procs_tup final tr_final /\
    all_terminated (tval final) /\
    exists suffix, tnth tr_final ord0 = suffix ++ tr_acc.
Proof.
elim: h ps tr_acc => [|h IH] ps tr_acc Hinv Hnt Hterm Htr.
- by move/negP: Hnt.
- rewrite (@dsdp_progress.interp_comp_unfold_eq data (tval ps) h) in Hterm.
  have Hprog : has_progress data (tval ps).
    exact (@dsdp_inv_has_progress AHE ek n_relay Hn_relay dk dk_relay
      relays Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay r2_relay
      (tval ps) Hinv).
  rewrite Hprog in Hterm.
  set res := [tuple smc_interpreter.step ps [::] i | i < n_parties].
  set ps' := res_procs res.
  set tr1 := res_traces res.
  have Hss : rsteps ps ps' tr1 := step_sound ps.
  have Hps'eq : tval ps' = osp (tval ps)
    by rewrite -(@one_step_eq_res_procs_local ps).
  have Hinv_step : all_terminated (osp (tval ps)) \/
                   inv (osp (tval ps)).
    exact: (@dsdp_inv_step AHE ek n_relay Hn_relay dk dk_relay
      dec_total key_relay relays Hrelays Hrelays_id v0 u r rand_a
      v_relay r1_relay r2_relay (tval ps) Hinv).
  have [tr0 [Hrs0 Htr0eq]] := Htr.
  set tr_composed := [tuple tnth tr1 i ++ tnth tr0 i | i < n_parties].
  have Hrs_comp : rsteps procs_tup ps' tr_composed := rtrans Hrs0 Hss erefl.
  case: Hinv_step => [Hterm_step | Hinv_step].
  + (* all_terminated after one step *)
    exists ps', tr_composed; split; first exact Hrs_comp.
    split; first by rewrite Hps'eq.
    exists (tnth tr1 ord0); rewrite /tr_composed tnth_mktuple.
    by rewrite -Htr0eq.
  + (* inv preserved: recurse *)
    case Hnt' : (all_terminated (osp (tval ps))).
    * (* all_terminated *)
      exists ps', tr_composed; split; first exact Hrs_comp.
      split; first by rewrite Hps'eq.
      exists (tnth tr1 ord0); rewrite /tr_composed tnth_mktuple.
      by rewrite -Htr0eq.
    * (* ~~ all_terminated: apply IH *)
      have Hnt'' : ~~ all_terminated (tval ps') by rewrite Hps'eq Hnt'.
      have Hinv'' : inv (tval ps') by rewrite Hps'eq; exact Hinv_step.
      have Hterm' : all_terminated (interp_comp data (tval ps') h)
        by rewrite Hps'eq.
      have Htr_new : tnth tr_composed ord0 = tnth tr1 ord0 ++ tr_acc.
        by rewrite /tr_composed tnth_mktuple -Htr0eq.
      have Htr_ex : exists tr0' : n_parties.-tuple (seq data),
        rsteps procs_tup ps' tr0' /\ tnth tr0' ord0 = tnth tr1 ord0 ++ tr_acc.
        by exists tr_composed.
      have [final [tr_final [Hrs_final [Htf [suffix Hsuf]]]]] :=
        IH ps' (tnth tr1 ord0 ++ tr_acc) Hinv'' Hnt'' Hterm' Htr_ex.
      exists final, tr_final; split; first exact Hrs_final.
      split; first exact Htf.
      exists (suffix ++ tnth tr1 ord0).
      by rewrite -catA.
Qed.

(* ========================================================================== *)
(* Main theorem: full trace correctness                                       *)
(* ========================================================================== *)

(* Fuel monotonicity: if interp_comp procs h terminates, then so does
   interp_comp (osp(osp(procs))) h' for a suitable h'. *)
Lemma init_fuel_transfer h :
  all_terminated (interp_comp data procs h) ->
  exists h', all_terminated (interp_comp data (osp (osp procs)) h').
Proof.
move=> Hterm; exists h.
have Hprog0 : has_progress data procs.
  exact: (@dsdp_initial_progress AHE ek n_relay dk dk_relay relays Hrelays
    v0 u r rand_a v_relay r1_relay r2_relay).
have Hic1 : interp_comp data procs 1 = osp procs.
  by rewrite (@interp_comp_unfold_eq data procs 0) Hprog0.
have Hprog1 : has_progress data (osp procs).
  have [Ht1|Hp1] := @dsdp_terminated_or_progress AHE ek n_relay Hn_relay dk
    dk_relay dec_total key_relay relays Hrelays Hrelays_id v0 u r rand_a
    v_relay r1_relay r2_relay 1.
  + exfalso; rewrite Hic1 in Ht1.
    have := @step_all_terminated data _ Ht1.
    have := @dsdp_init_not_terminated AHE ek n_relay dk dk_relay relays
      Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay r2_relay.
    by move/negP; apply.
  + by rewrite Hic1 in Hp1.
have Hbridge : interp_comp data procs 2 = osp (osp procs).
  rewrite (@interp_comp_unfold_eq data procs 1) Hprog0.
  by rewrite (@interp_comp_unfold_eq data (osp procs) 0) Hprog1.
rewrite -Hbridge -(@interp_comp_add data procs 2 h).
suff Hmono : forall ps k1 k2, all_terminated (interp_comp data ps k1) ->
  all_terminated (interp_comp data ps (k1 + k2)).
  rewrite addnC; exact: (Hmono _ h 2 Hterm).
move=> ps k1 k2 Ht; rewrite (@interp_comp_add data ps k1 k2).
suff Habs : forall qs k, all_terminated qs -> all_terminated (interp_comp data qs k).
  exact: Habs.
move=> qs k; elim: k qs => [|k IH] qs Htq //.
rewrite (@interp_comp_unfold_eq data qs k).
case: ifPn => Hhas.
- apply IH; exact: (@step_all_terminated data qs Htq).
- exact: Htq.
Qed.

Theorem fsm_trace_correctness (h : nat)
    (Hfuel : all_terminated (interp_comp data procs h)) :
  (1 <= n_relay)%N ->
  exists (final : n_parties.-tuple (proc data)) tr,
    rsteps procs_tup final tr /\
    all_terminated (tval final) /\
    exists suffix, tnth tr ord0 = suffix ++ [:: d v0; priv_key_local dk].
Proof.
move=> Hn1.
have [ps_init [tr_init [Hrs_init [Htrace_init [Hinv_init [Hnt_init Heq_init]]]]]] :=
  init_to_inv.
(* Get fuel for post-init state *)
have [h' Hterm_init] := init_fuel_transfer Hfuel.
have Hterm_init' : all_terminated (interp_comp data (tval ps_init) h').
  by rewrite Heq_init.
have Htr_ex : exists tr0, rsteps procs_tup ps_init tr0 /\
  tnth tr0 ord0 = [:: d v0; priv_key_local dk].
  by exists tr_init.
have [final [tr_final [Hrs_final [Htf [suffix Hsuf]]]]] :=
  fsm_trace_induction Hinv_init Hnt_init Hterm_init' Htr_ex.
exists final, tr_final; do !split.
exact Hrs_final.
exact Htf.
by exists suffix.
Qed.

End dsdp_fsm_progress.
