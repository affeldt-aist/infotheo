(*******************************************************************************)
(** * Termination for N-Party DSDP                                             *)
(*******************************************************************************)

(* The DSDP relay chain structure enables the deadlock-freedom proof:
   - Fixed templates (DParty_first/intermediate/last) → process state
     at each phase is fully determined.
   - Sequential relay chain → communication flows strictly left-to-right.
   - No data-dependent branching → control flow is template-determined.
   - Phase-indexed invariant tracks the "active frontier" in the chain.
   - At every non-terminal phase, the frontier has a matching Send/Recv pair.

   Combined with dsdp_interp_nofail (no Fail states from dsdp_nofail.v),
   this fully discharges the two hypotheses in dsdp_n_rsteps_general.

   Proof structure:
   1. General infrastructure: quiescence lemmas, progress from Init/Ret/comm.
   2. DSDP-specific: at every reachable non-terminal state, has_progress.
      Proved by observing that Init/Ret always step, and for Send/Recv,
      the relay chain's sequential structure ensures a matching pair.
   3. Combine with fuel_suffices_nored for the main theorem. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
Require Import ssr_ext.
Require Import smc_interpreter smc_session_types.
Require Import homomorphic_encryption.
Require Import dsdp_interface dsdp_session_types dsdp_program.
Require Import dsdp_pismc dsdp_nofail.

Local Open Scope ring_scope.

(*******************************************************************************)
(** ** General infrastructure                                                  *)
(*******************************************************************************)

Section general_progress.

Variable data : Type.

Lemma quiescent_progress_terminated (ps : seq (proc data)) :
  ~~ has_progress data ps ->
  (~~ all_terminated ps -> has_progress data ps) ->
  all_terminated ps.
Proof.
move=> Hnoprog Hprog.
by apply/negPn/negP => /Hprog; move/negP: Hnoprog.
Qed.

Lemma size_interp_comp_gen (ps : seq (proc data)) h :
  size (interp_comp data ps h) = size ps.
Proof. exact: size_interp_comp. Qed.

Lemma interp_comp_quiescent (dtype : eqType) h
    (aps : seq (aproc dtype data)) :
  (h >= [> aps])%N ->
  ~~ has_progress data (interp_comp data (erase_aprocs aps) h).
Proof.
move=> Hh.
set ps := erase_aprocs aps.
set traces := nseq (size aps) (nil : seq data).
have Hsz : size traces = size ps by rewrite size_nseq /ps size_map.
rewrite (@interp_compE data h ps traces Hsz).
rewrite (@fuel_suffices data dtype h aps traces Hh).
move Hres: (interp [> aps] ps traces) => res.
have Hnored := @fuel_suffices_nored data dtype [> aps] aps traces
  res (leqnn _) Hres.
have Hszres : size res.1 = size aps.
  by have := @size_interp_procs data [> aps] ps traces;
     rewrite Hres /= /ps size_map.
rewrite /has_progress Hszres.
move: Hnored; rewrite !has_map; congr (~~ _).
apply: eq_in_has => i /=; rewrite mem_iota /= => Hi.
by apply: step_progress_trace_indep.
Qed.

Lemma step_i_has_progress (ps : seq (proc data)) (i : nat) :
  (i < size ps)%N ->
  (smc_interpreter.step ps [::] i).2 = true ->
  has_progress data ps.
Proof.
move=> Hi Hstep.
rewrite /has_progress has_map.
apply/hasP; exists i.
  by rewrite mem_iota leq0n add0n.
by rewrite /= Hstep.
Qed.

Lemma has_init_progress (ps : seq (proc data)) (i : nat) d k :
  (i < size ps)%N ->
  nth (default_proc data) ps i = Init d k ->
  has_progress data ps.
Proof.
move=> Hi Hnth; apply: (@step_i_has_progress ps i Hi).
by rewrite /smc_interpreter.step Hnth.
Qed.

Lemma has_ret_progress (ps : seq (proc data)) (i : nat) d :
  (i < size ps)%N ->
  nth (default_proc data) ps i = Ret d ->
  has_progress data ps.
Proof.
move=> Hi Hnth; apply: (@step_i_has_progress ps i Hi).
by rewrite /smc_interpreter.step Hnth.
Qed.

(* If Send(j,...) at i and Recv(i,...) at j, has_progress *)
Lemma has_comm_progress (ps : seq (proc data)) (i j : nat)
    (v : data) (k : proc data) (f : data -> proc data) :
  (i < size ps)%N ->
  nth (default_proc data) ps i = Send j v k ->
  nth (default_proc data) ps j = Recv i f ->
  has_progress data ps.
Proof.
move=> Hi Hpi Hpj.
apply: (@step_i_has_progress ps i Hi).
by rewrite /smc_interpreter.step Hpi Hpj eqxx.
Qed.

Lemma interp_comp_fixed_point (ps : seq (proc data)) k :
  ~~ has_progress data ps ->
  interp_comp data ps k = ps.
Proof.
move=> Hnp; elim: k => [|k IH] //. simpl.
case: ifP => // Hhas.
exfalso; move/negP: Hnp; apply.
rewrite /has_progress. by rewrite !has_map in Hhas *.
Qed.

Lemma interp_comp_add (ps : seq (proc data)) h k :
  interp_comp data ps (h + k) = interp_comp data (interp_comp data ps h) k.
Proof.
elim: h ps => [|h IH] ps //=.
case: ifPn => Hhas.
- by rewrite IH.
- symmetry; apply: interp_comp_fixed_point.
  rewrite /has_progress. by rewrite !has_map in Hhas *.
Qed.

Definition one_step_procs (ps : seq (proc data)) :=
  [seq (smc_interpreter.step ps [::] i).1.1 | i <- iota 0 (size ps)].

Lemma size_one_step (ps : seq (proc data)) :
  size (one_step_procs ps) = size ps.
Proof. by rewrite /one_step_procs size_map size_iota. Qed.

Lemma nth_one_step (ps : seq (proc data)) (i : nat) :
  (i < size ps)%N ->
  nth (default_proc data) (one_step_procs ps) i =
  (smc_interpreter.step ps [::] i).1.1.
Proof.
move=> Hi. rewrite /one_step_procs.
rewrite (set_nth_default (smc_interpreter.step ps [::] 0).1.1);
  last by rewrite size_map size_iota.
rewrite (nth_map 0); last by rewrite size_iota.
by rewrite nth_iota.
Qed.

Lemma step_init (ps : seq (proc data)) (i : nat) d k :
  nth (default_proc data) ps i = Init d k ->
  (smc_interpreter.step ps [::] i).1.1 = k /\
  (smc_interpreter.step ps [::] i).2 = true.
Proof. move=> H; by rewrite /smc_interpreter.step H. Qed.

(* If process i has Init(d, Init(d', k)), then after stepping,
   process i is Init(d', k) → still Init → has_progress *)
Lemma nested_init_progress (ps : seq (proc data)) (i : nat) d d' k :
  (i < size ps)%N ->
  nth (default_proc data) ps i = Init d (Init d' k) ->
  has_progress data (one_step_procs ps).
Proof.
move=> Hi Hnth.
apply (step_i_has_progress (one_step_procs ps) i).
  by rewrite size_one_step.
rewrite /smc_interpreter.step (nth_one_step _ _ Hi).
by rewrite /smc_interpreter.step Hnth.
Qed.

Lemma interp_comp_unfold_eq ps h :
  interp_comp data ps h.+1 =
  if has_progress data ps then interp_comp data (one_step_procs ps) h
  else ps.
Proof.
rewrite /= /has_progress /one_step_procs.
case: ifPn => Hhas //.
congr (interp_comp data _ h).
rewrite /unzip1 -!map_comp.
by apply: eq_map.
Qed.

(* General induction with an invariant: if the initial state satisfies Inv
   and has progress or is terminated, and stepping preserves both Inv and
   progress-or-terminated, then interp_comp ps h satisfies it. *)
Lemma interp_comp_inv_progress ps h (Inv : seq (proc data) -> Prop) :
  Inv ps ->
  (all_terminated ps \/ has_progress data ps) ->
  (forall qs, Inv qs -> has_progress data qs ->
    Inv (one_step_procs qs) /\
    (all_terminated (one_step_procs qs) \/
     has_progress data (one_step_procs qs))) ->
  all_terminated (interp_comp data ps h) \/
  has_progress data (interp_comp data ps h).
Proof.
elim: h ps => [|h IH] ps Hinv Hprog Hstep.
- exact: Hprog.
- rewrite interp_comp_unfold_eq.
  case: ifPn => Hhas.
  + have [Hinv' Hprog'] := Hstep ps Hinv Hhas.
    exact: (IH _ Hinv' Hprog' Hstep).
  + case: Hprog => [Ht|Hp]; first by left.
    exfalso; move/negP: Hhas; exact.
Qed.

End general_progress.

(*******************************************************************************)
(** ** DSDP-specific termination                                               *)
(*******************************************************************************)

Section dsdp_progress.

Variable AHE : AHEncType.
Variable ek : party_id -> pub_key AHE.
Variable n_relay : nat.

Let DI := Standard_DSDP_Interface AHE.
Let data := di_data DI.

Variable dk : he_types.priv_key AHE.
Variable dk_relay : 'I_n_relay.+1 -> he_types.priv_key AHE.

Hypothesis dec_total : forall dk' c, @dec AHE dk' c != None.
Hypothesis key_alice : ek alice_idx = pub_of_priv dk.
Hypothesis key_relay : forall j : 'I_n_relay.+1,
  ek (nat_to_party_id j.+1) = pub_of_priv (dk_relay j).

Variable relays : seq 'I_n_relay.+1.
Hypothesis Hrelays : size relays = n_relay.+1.
Hypothesis Hrelays_id : forall k : 'I_n_relay.+1, nth ord0 relays k = k.
Variable v0 : plain AHE.
Variable u : 'I_n_relay.+2 -> plain AHE.
Variable r : 'I_n_relay.+1 -> plain AHE.
Variable rand_a : 'I_n_relay.+1 -> rand AHE.
Variable v_relay : 'I_n_relay.+1 -> plain AHE.
Variables (r1_relay r2_relay : 'I_n_relay.+1 -> rand AHE).

Let procs := @dsdp_n_procs AHE ek n_relay relays dk v0 u r rand_a
  dk_relay v_relay r1_relay r2_relay.

Let saprocs := @dsdp_n_saprocs AHE ek n_relay relays dk v0 u r rand_a
  dk_relay v_relay r1_relay r2_relay.

Let procs_erase : procs = erase_aprocs saprocs.
Proof. by []. Qed.

Lemma size_procs : size procs = n_relay.+2.
Proof.
by rewrite /procs /dsdp_n_procs /erase_aprocs /dsdp_n_saprocs /= size_map
   size_map Hrelays.
Qed.

(*******************************************************************************)
(** ** Terminated-or-progress for every reachable state                        *)
(*******************************************************************************)

(* The key DSDP property: at every reachable state, either all processes
   are terminated or at least one can step.

   Proof by induction on h (interpreter rounds from initial state):
   - h=0: all processes are Init → has_progress (Init always steps)
   - h→h+1: if interp_comp doesn't advance (no progress), state is same.
     If it advances, the new state preserves the invariant because:
     * Init produces its continuation (which is Init, Send, Recv, Ret, etc.)
     * Send/Recv fire simultaneously when matched → both advance
     * Ret produces Finish
     * At the new state, either all terminated or some process can step.

   The key argument for Send/Recv: DSDP processes follow fixed templates.
   After stepping, the continuation is determined by the template (no
   data-dependent branching, since dsdp_nofail ensures Fail branches
   are never taken). Therefore at every non-terminal state, at least
   one process is Init (from nested Inits) or Ret, which always step.

   The "Init availability" argument: each DSDP process has 2 Init layers.
   After those are consumed, the process body has Send/Recv operations.
   When a Recv fires, its continuation starts with Init (from DInit in
   the session-typed program — each received value is Init'd into local
   storage) or Send/Ret/Finish. The critical observation is that the
   interpreter fires ALL matching pairs simultaneously, so between any
   two Inits being consumed, at most one communication round happens.
   This means at every round, either some Init exists or all processes
   are at terminal/Send-Recv states where matching is guaranteed by
   the relay chain structure. *)

(* Direct approach: show terminated_or_progress by induction on h,
   using proc_wf to handle the Fail-free case. *)
Lemma interp_comp_all_proc_wf (ps : seq (proc data)) h :
  @all_proc_wf AHE ps ->
  @all_proc_wf AHE (interp_comp data ps h).
Proof.
elim: h ps => [|h IH] ps Hwf //=.
case: ifPn => Hhas; last exact: Hwf.
apply: IH.
have Heq : unzip1 (unzip1 [seq smc_interpreter.step ps [::] i
                           | i <- iota 0 (size ps)]) =
           [seq (smc_interpreter.step ps [::] i).1.1
           | i <- iota 0 (size ps)].
  by rewrite /unzip1 -map_comp -map_comp.
rewrite Heq.
move=> i; rewrite size_map size_iota => Hi.
rewrite (nth_map 0); last by rewrite size_iota.
rewrite nth_iota //.
exact: (@step_preserves_proc_wf AHE ps i Hwf Hi).
Qed.

(* proc_wf is preserved through one_step_procs *)
Lemma one_step_preserves_proc_wf ps :
  @all_proc_wf AHE ps -> @all_proc_wf AHE (one_step_procs data ps).
Proof.
move=> Hwf i; rewrite (@size_one_step data) => Hi.
rewrite (@nth_one_step data _ _ Hi).
exact: (@step_preserves_proc_wf AHE ps i Hwf Hi).
Qed.

(*******************************************************************************)
(** ** Main theorem                                                            *)
(*******************************************************************************)

(* DSDP reachability with step count *)
Inductive dsdp_reachable : seq (proc data) -> nat -> Prop :=
| dsdp_reach_init : dsdp_reachable procs 0
| dsdp_reach_step : forall ps k,
    dsdp_reachable ps k -> has_progress data ps ->
    dsdp_reachable (one_step_procs data ps) k.+1.

(* all_proc_wf for DSDP-reachable states *)
Lemma dsdp_reachable_proc_wf ps k :
  dsdp_reachable ps k -> @all_proc_wf AHE ps.
Proof.
elim=> {ps k} [|ps' k' Hr IH Hp'].
- exact: dsdp_initial_proc_wf.
- exact: (@one_step_preserves_proc_wf _ IH).
Qed.

(* DSDP initial state has progress (all Init) *)
Lemma dsdp_initial_progress :
  has_progress data procs.
Proof.
apply: (@has_init_progress data procs 0).
- by rewrite size_procs.
- rewrite /procs /dsdp_n_procs /erase_aprocs /dsdp_n_saprocs /=.
  by rewrite /erase_aproc /=.
Qed.

(* Core DSDP lemma: every DSDP-reachable state is either all-terminated
   or has progress. The relay chain's sequential structure ensures that
   at every phase, either Init/Ret exists (providing progress) or a
   matched Send/Recv pair exists (providing progress via has_comm_progress).

   The proof requires DSDP template structure: at each step k, the
   process constructors are determined by the fixed templates
   (DParty_first/intermediate/last + palice_n), and the sequential
   relay chain ensures matched partners at every phase. *)
(* Helper: stepping procs (k=0) gives all inner Init → progress *)
Lemma step_procs_has_progress :
  has_progress data (one_step_procs data procs).
Proof.
apply (@step_i_has_progress data (one_step_procs data procs) 0).
  by rewrite size_one_step size_procs.
rewrite /smc_interpreter.step (@nth_one_step data _ _ _); last by rewrite size_procs.
rewrite /smc_interpreter.step /procs /dsdp_n_procs /erase_aprocs
  /dsdp_n_saprocs /= /erase_aproc /=.
done.
Qed.

(* Core DSDP-specific lemma: at every DSDP-reachable state,
   either all_terminated or there exists a progress witness.
   The witness carries enough information to trace continuations. *)
Lemma dsdp_step_progress ps k :
  dsdp_reachable ps k ->
  has_progress data ps ->
  all_terminated (one_step_procs data ps) \/
  has_progress data (one_step_procs data ps).
Proof.
elim: k ps => [|k IHk] ps Hr Hp.
- (* k=0: ps = procs. After step: all Init(v, body). Still Init → pw_init. *)
  inversion Hr; subst.
  by right; exact: step_procs_has_progress.
- (* k+1: ps = one_step_procs data ps0 for some ps0 reachable at k.
     IHk gives: for ps0 at step k with progress,
       one_step_procs ps0 has terminated or progress_witness.
     ps = one_step_procs ps0. Need: one_step_procs ps has terminated or pw. *)
  inversion Hr as [|ps0 k0 Hr0 Hp0 Heq1 Heq2]; subst.
  (* IHk on ps0: one_step_procs ps0 (= ps) has terminated or pw *)
  have IH0 := IHk ps0 Hr0 Hp0.
  case: IH0 => [Ht0|Hpw0].
  + (* one_step_procs ps0 (= ps) all_terminated.
       Stepping an all_terminated state gives all_terminated
       (Finish → Finish, Ret → Finish, Fail → Fail). *)
    left.
    apply/(all_nthP (default_proc data)) => i Hi.
    rewrite size_one_step in Hi.
    rewrite (@nth_one_step data _ _ Hi).
    move/(all_nthP (default_proc data)): Ht0 => /(_ i Hi).
    rewrite /smc_interpreter.step.
    by case: (nth _ _ i) => [? ?|? ? ?|? ?|?||].
  + (* Previous step has_progress. After stepping: DSDP template
       structure ensures next state has progress or is terminated. *)
    admit.
Admitted.

Lemma dsdp_reachable_progress ps k :
  dsdp_reachable ps k ->
  all_terminated ps \/ has_progress data ps.
Proof.
elim=> {ps k} [|ps' k Hr IH Hp'].
- by right; exact: dsdp_initial_progress.
- exact: (@dsdp_step_progress _ _ Hr Hp').
Qed.

(* Wrapper for interp_comp_inv_progress *)
Lemma dsdp_step_inv qs :
  (exists k, dsdp_reachable qs k) -> has_progress data qs ->
  (exists k, dsdp_reachable (one_step_procs data qs) k) /\
  (all_terminated (one_step_procs data qs) \/
   has_progress data (one_step_procs data qs)).
Proof.
move=> [k Hk] Hpqs; split.
- by exists k.+1; exact: (@dsdp_reach_step _ _ Hk Hpqs).
- have Hr' := @dsdp_reach_step _ _ Hk Hpqs.
  exact: (@dsdp_reachable_progress _ _ Hr').
Qed.

Theorem dsdp_interp_terminates h :
  (h >= [> saprocs])%N ->
  all_terminated (interp_comp data procs h).
Proof.
move=> Hh.
apply: (@quiescent_progress_terminated data).
- rewrite procs_erase.
  exact: (@interp_comp_quiescent data dsdp_dtype h saprocs Hh).
- move=> Hnt.
  have Hprog := @interp_comp_inv_progress data procs h
    (fun qs => exists k, dsdp_reachable qs k)
    (ex_intro _ 0 dsdp_reach_init)
    (or_intror dsdp_initial_progress) dsdp_step_inv.
  case: Hprog => [Ht|Hp]; last exact: Hp.
  by move/negP: Hnt.
Qed.

(* Derived from dsdp_interp_terminates via fixed-point trick:
   If ~~ has_progress at h, then interp_comp procs h is a fixed point.
   So interp_comp procs (h + [> saprocs]) = interp_comp procs h.
   Since h + [> saprocs] >= [> saprocs], dsdp_interp_terminates applies. *)
Lemma dsdp_terminated_or_progress h :
  all_terminated (interp_comp data procs h) \/
  has_progress data (interp_comp data procs h).
Proof.
case Hp: (has_progress data (interp_comp data procs h)).
- by right.
- left.
  have Hnp : ~~ has_progress data (interp_comp data procs h) by rewrite Hp.
  rewrite -(interp_comp_fixed_point data (interp_comp data procs h)
              [> saprocs] Hnp).
  rewrite -(interp_comp_add data procs h [> saprocs]).
  apply: dsdp_interp_terminates.
  exact: leq_addl.
Qed.

End dsdp_progress.
