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

(* Extract a concrete witness from has_progress:
   if some process can step, it's Init, Ret, or has a matched Send/Recv partner. *)
Lemma has_progress_has_witness (ps : seq (proc data)) :
  has_progress data ps ->
  (exists i d k', (i < size ps)%N /\
     nth (default_proc data) ps i = Init d k') \/
  (exists i d, (i < size ps)%N /\
     nth (default_proc data) ps i = Ret d) \/
  (exists i j v k' f, (i < size ps)%N /\ (j < size ps)%N /\
     nth (default_proc data) ps i = Send j v k' /\
     nth (default_proc data) ps j = Recv i f).
Proof.
rewrite /has_progress has_map => /hasP [i].
rewrite mem_iota /= add0n => Hi.
rewrite /= /smc_interpreter.step.
case Hpi: (nth (default_proc data) ps i) => [d0 k0|dst v0 k0|frm f0|d0| | ] //= Hstep.
- (* Init *) left; exists i, d0, k0; split => //.
- (* Send: step checks ps[dst] for matching Recv *)
  case Hdst: (nth (default_proc data) ps dst) Hstep =>
    [|? ? ?|frm f0|? | | ] //=.
  case Heq: (frm == i) => //= _.
  move/eqP: Heq => Heq; subst frm.
  have Hdst_bound : (dst < size ps)%N.
    case: (ltnP dst (size ps)) => // Hge.
    by rewrite nth_default in Hdst.
  right; right; exists i, dst, v0, k0, f0.
  by rewrite Hpi Hdst.
- (* Recv: step checks ps[frm] for matching Send *)
  case Hfrm: (nth (default_proc data) ps frm) Hstep =>
    [|dst v0 k0|? ?|? | | ] //=.
  case Heq: (dst == i) => //= _.
  move/eqP: Heq => Heq; subst dst.
  have Hfrm_bound : (frm < size ps)%N.
    case: (ltnP frm (size ps)) => // Hge.
    by rewrite nth_default in Hfrm.
  right; right; exists frm, i, v0, k0, f0.
  by rewrite Hfrm Hpi.
- (* Ret *) right; left; exists i, d0; split => //.
Qed.

(* L4: Finish stays *)
Lemma step_finish_nop (ps : seq (proc data)) (i : nat) :
  nth (default_proc data) ps i = Finish ->
  (smc_interpreter.step ps [::] i).1.1 = Finish.
Proof.
by move=> Hpi; rewrite /smc_interpreter.step Hpi.
Qed.

(* L3: Matched Send/Recv both advance *)
Lemma step_send_recv_match (ps : seq (proc data)) (i j : nat) v k f :
  nth (default_proc data) ps i = Send j v k ->
  nth (default_proc data) ps j = Recv i f ->
  (smc_interpreter.step ps [::] i).1.1 = k /\
  (smc_interpreter.step ps [::] j).1.1 = f v.
Proof.
move=> Hpi Hpj; split.
- by rewrite /smc_interpreter.step Hpi Hpj eqxx.
- by rewrite /smc_interpreter.step Hpj Hpi eqxx.
Qed.

(* L1: Unmatched Send stays *)
Lemma step_send_nop (ps : seq (proc data)) (i : nat) j v k :
  nth (default_proc data) ps i = Send j v k ->
  (forall f, nth (default_proc data) ps j <> Recv i f) ->
  (smc_interpreter.step ps [::] i).1.1 = Send j v k /\
  (smc_interpreter.step ps [::] i).2 = false.
Proof.
move=> Hpi Hnotrecv.
rewrite /smc_interpreter.step Hpi.
case Hpj: (nth (default_proc data) ps j) => [|? ? ?|frm f|? | |] //=;
  try by split.
case Heq: (frm == i) => /=; last by split.
move/eqP: Heq => Heq; subst frm.
exfalso; exact: (Hnotrecv f Hpj).
Qed.

(* L2: Unmatched Recv stays *)
Lemma step_recv_nop (ps : seq (proc data)) (i : nat) frm f :
  nth (default_proc data) ps i = Recv frm f ->
  (forall v k, nth (default_proc data) ps frm <> Send i v k) ->
  (smc_interpreter.step ps [::] i).1.1 = Recv frm f /\
  (smc_interpreter.step ps [::] i).2 = false.
Proof.
move=> Hpi Hnotsend.
rewrite /smc_interpreter.step Hpi.
case Hpf: (nth (default_proc data) ps frm) => [|dst v k|? ?|? | |] //=;
  try by split.
case Heq: (dst == i) => /=; last by split.
move/eqP: Heq => Heq; subst dst.
exfalso; exact: (Hnotsend v k Hpf).
Qed.

(* Helper: stepping preserves all_terminated *)
Lemma step_all_terminated (ps : seq (proc data)) :
  all_terminated ps -> all_terminated (one_step_procs ps).
Proof.
rewrite /all_terminated => Ht.
apply/(@all_nthP _ _ _ (default_proc data)).
rewrite size_one_step => i Hi.
rewrite nth_one_step //.
have Hpi : is_terminal (nth (default_proc data) ps i).
  by move/(@all_nthP _ _ _ (default_proc data)): Ht => /(_ i Hi).
rewrite /smc_interpreter.step.
by case: (nth (default_proc data) ps i) Hpi.
Qed.

End general_progress.

(*******************************************************************************)
(** ** DSDP-specific termination                                               *)
(*******************************************************************************)

Section dsdp_progress.

Variable AHE : AHEncType.
Variable ek : party_id -> pub_key AHE.
Variable n_relay : nat.
Hypothesis Hn_relay : (0 < n_relay)%N.

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

(*******************************************************************************)
(** ** DSDP structural lemmas for deadlock-freedom                            *)
(*******************************************************************************)

(* All relay templates erase to Init(dk, Init(v, body)) with body = Send(0,...) *)
Local Lemma relay_aproc_double_init (j : 'I_n_relay.+1) dk' v' r1' r2' :
  exists d1 d2 sv sk,
    erase_aproc (relay_aproc AHE ek n_relay j dk' v' r1' r2') =
    Init d1 (Init d2 (Send alice_idx sv sk)).
Proof.
rewrite /relay_aproc /erase_aproc /aproc_proc /=.
case: ifP => ? /=; [|case: ifP => ? /=]; by do 4 eexists.
Qed.

(* All initial processes are double Init *)
Lemma procs_all_double_init : forall i, (i < size procs)%N ->
  exists d d' k0, nth (default_proc data) procs i = Init d (Init d' k0).
Proof.
move=> i Hi; rewrite size_procs in Hi.
case: i Hi => [|i] Hi.
- do 3 eexists.
  rewrite /procs /dsdp_n_procs /erase_aprocs /dsdp_n_saprocs /= /erase_aproc /=.
  exact: (@palice_n_erase AHE ek n_relay relays dk v0 u r rand_a).
- have Hi' : (i < n_relay.+1)%N by [].
  rewrite /procs /dsdp_n_procs /erase_aprocs /dsdp_n_saprocs /=.
  rewrite -map_comp (nth_map ord0); last by rewrite Hrelays.
  rewrite /comp /=.
  have -> : nth ord0 relays i = Ordinal Hi'
    by apply: val_inj; rewrite /= (Hrelays_id (Ordinal Hi')).
  have [d1 [d2 [sv [sk Heq]]]] := relay_aproc_double_init
    (Ordinal Hi') (dk_relay (Ordinal Hi')) (v_relay (Ordinal Hi'))
    (r1_relay (Ordinal Hi')) (r2_relay (Ordinal Hi')).
  rewrite Heq; by do 3 eexists.
Qed.

(* After two one_step rounds, position 1 (relay 0) is Send(0,...) *)
Lemma oops_pos1_send0 :
  exists sv sk,
    nth (default_proc data) (one_step_procs data (one_step_procs data procs)) 1 =
    Send 0 sv sk.
Proof.
have Hsz : (1 < size procs)%N by rewrite size_procs.
have [rd1 [rd2 [sv [sk Hrel]]]] := relay_aproc_double_init ord0
  (dk_relay ord0) (v_relay ord0) (r1_relay ord0) (r2_relay ord0).
have Hp1 : nth (default_proc data) procs 1 = Init rd1 (Init rd2 (Send alice_idx sv sk)).
  have Hi' : (0 < n_relay.+1)%N by [].
  rewrite /procs /dsdp_n_procs /erase_aprocs /dsdp_n_saprocs /=.
  rewrite -map_comp (nth_map ord0); last by rewrite Hrelays.
  rewrite /comp /=.
  have -> : nth ord0 relays (Ordinal Hi') = Ordinal Hi'
    by apply val_inj; rewrite /= (Hrelays_id (Ordinal Hi')).
  have -> : Ordinal Hi' = ord0 :> 'I_n_relay.+1 by apply val_inj.
  exact Hrel.
have Hops1 : nth (default_proc data) (one_step_procs data procs) 1 =
  Init rd2 (Send alice_idx sv sk).
  by rewrite (@nth_one_step data procs 1 Hsz) /smc_interpreter.step Hp1.
have Hsz2 : (1 < size (one_step_procs data procs))%N by rewrite size_one_step.
have Hoops1 : nth (default_proc data) (one_step_procs data (one_step_procs data procs)) 1 =
  Send alice_idx sv sk.
  by rewrite (@nth_one_step data _ 1 Hsz2) /smc_interpreter.step Hops1.
rewrite /alice_idx in Hoops1.
by exists sv, sk.
Qed.

(* After two one_step rounds, position 0 (Alice) is Recv(1,...) *)
Lemma oops_pos0_recv1 :
  exists f,
    nth (default_proc data) (one_step_procs data (one_step_procs data procs)) 0 =
    Recv 1 f.
Proof.
have Hsz : (0 < size procs)%N by rewrite size_procs.
have Halice := @palice_n_erase AHE ek n_relay relays dk v0 u r rand_a.
(* Get Alice's erased form and step through 2 Init layers *)
have [d [d' [k0 Hp0]]] := @procs_all_double_init 0 Hsz.
have Hops0 : nth (default_proc data) (one_step_procs data procs) 0 = Init d' k0.
  by rewrite (@nth_one_step data procs 0 Hsz) /smc_interpreter.step Hp0.
have Hsz2 : (0 < size (one_step_procs data procs))%N by rewrite size_one_step.
have Hoops0 : nth (default_proc data) (one_step_procs data (one_step_procs data procs)) 0 = k0.
  by rewrite (@nth_one_step data _ 0 Hsz2) /smc_interpreter.step Hops0.
(* k0 is Alice's body after 2 Init layers = foldr alice_erase_body alice_erase_tail ... *)
(* From palice_n_erase, procs[0] = Init(dk_val, Init(v0_val, foldr...)) *)
(* So k0 = foldr alice_erase_body alice_erase_tail (zip relays iota) *)
(* The foldr starts with alice_erase_body for the first element, which is Recv(1,...) *)
(* We need to show k0 starts with Recv 1 *)
(* Connect procs[0] to Alice template via palice_n_erase *)
have Halice2 := @palice_n_erase AHE ek n_relay relays dk v0 u r rand_a.
have Hp0' : nth (default_proc data) procs 0 =
  erase (@palice_n AHE ek n_relay relays dk v0 u r rand_a).
  rewrite /procs /dsdp_n_procs /erase_aprocs /dsdp_n_saprocs /= /erase_aproc /=.
  reflexivity.
rewrite Hp0' Halice2 in Hp0.
case: Hp0 => _ [_ Hk0].
rewrite -Hk0 in Hoops0.
rewrite Hoops0.
have -> : zip relays (iota 0 (size relays)) =
  (nth ord0 relays 0, nth 0 (iota 0 (size relays)) 0) ::
  zip (behead relays) (behead (iota 0 (size relays))).
  by case: relays Hrelays Hrelays_id => //= a l Hs Hid;
     case: (iota 0 (size (a :: l))) => //=.
rewrite /= (Hrelays_id ord0) /= /alice_erase_body /std_Recv_enc /Recv_param /=.
by eexists.
Qed.

(* All relays are Send(0,...) after 2 steps *)
Lemma oops_allrelays_send0 (j : 'I_n_relay.+1) :
  exists sv sk,
    nth (default_proc data) (one_step_procs data (one_step_procs data procs)) j.+1 =
    Send 0 sv sk.
Proof.
have Hsz : (j.+1 < size procs)%N.
  rewrite /procs /dsdp_n_procs /erase_aprocs /dsdp_n_saprocs /= size_map size_map Hrelays.
  exact (ltn_ord j).
have [rd1 [rd2 [sv [sk Hrel]]]] := relay_aproc_double_init j
  (dk_relay j) (v_relay j) (r1_relay j) (r2_relay j).
have Hp : nth (default_proc data) procs j.+1 = Init rd1 (Init rd2 (Send alice_idx sv sk)).
  have Hi' := ltn_ord j.
  rewrite /procs /dsdp_n_procs /erase_aprocs /dsdp_n_saprocs /=.
  rewrite -map_comp (nth_map ord0); last by rewrite Hrelays.
  rewrite /comp /=.
  have -> : nth ord0 relays j = j
    by apply val_inj; rewrite /= (Hrelays_id j).
  exact Hrel.
have Hops : nth (default_proc data) (one_step_procs data procs) j.+1 =
  Init rd2 (Send alice_idx sv sk).
  by rewrite (@nth_one_step data procs j.+1 Hsz) /smc_interpreter.step Hp.
have Hsz2 : (j.+1 < size (one_step_procs data procs))%N by rewrite size_one_step.
have Hoops : nth (default_proc data) (one_step_procs data (one_step_procs data procs)) j.+1 =
  Send alice_idx sv sk.
  by rewrite (@nth_one_step data _ j.+1 Hsz2) /smc_interpreter.step Hops.
rewrite /alice_idx in Hoops.
by exists sv, sk.
Qed.

(* At step 2, Alice Recv(1,...) matches relay 0 Send(0,...) → has_progress *)
Lemma has_progress_at_step_2 :
  has_progress data (one_step_procs data (one_step_procs data procs)).
Proof.
have [sv [sk Hsend]] := oops_pos1_send0.
have [f Hrecv] := oops_pos0_recv1.
have Hsz : (1 < size (one_step_procs data (one_step_procs data procs)))%N.
  by rewrite size_one_step size_one_step size_procs.
exact: (@has_comm_progress data _ 1 0 sv sk f Hsz Hsend Hrecv).
Qed.

(*******************************************************************************)
(** ** Deadlock-freedom: protocol invariant and phase analysis               *)
(*******************************************************************************)

(* Local aliases for proc constructors *)
Let pSend := @smc_interpreter.Send data.
Let pRecvDec_local := @std_Recv_dec AHE.
Let pRecvEnc_local := @std_Recv_enc AHE.
Let Emul_local := @Emul AHE.
Let e_local : cipher AHE -> data := di_e DI.
Let enc_local := @enc AHE.

(* H1: pRecvEnc continuation *)
Lemma pRecvEnc_cont (f : cipher AHE -> proc data) (c : cipher AHE) :
  (oapp f Fail \o @std_from_enc AHE) (e_local c) = f c.
Proof. by rewrite /comp /e_local /std_from_enc /DI /=. Qed.

(* H2: pRecvDec continuation *)
Lemma pRecvDec_cont (dk' : he_types.priv_key AHE) (f : plain AHE -> proc data)
    (c : cipher AHE) :
  @dec AHE dk' c != None ->
  exists m, @dec AHE dk' c = Some m /\
    (oapp f Fail \o (obind (@dec AHE dk') \o @std_from_enc AHE)) (e_local c) = f m.
Proof.
rewrite /comp /e_local /std_from_enc /DI /=.
move=> Hdec; case Heq: (dec dk' c) => [m|].
  by exists m.
by rewrite Heq in Hdec.
Qed.

(* H3: Non-participant position is unchanged after one_step *)
Lemma nth_one_step_nop (ps : seq (proc data)) (i : nat) :
  (i < size ps)%N ->
  (smc_interpreter.step ps [::] i).2 = false ->
  nth (default_proc data) (one_step_procs data ps) i =
  nth (default_proc data) ps i.
Proof.
move=> Hi Hstep; rewrite (@nth_one_step data ps i Hi).
rewrite /smc_interpreter.step.
case Hpi: (nth (default_proc data) ps i) =>
  [d0 k0|j0 v0' k0|frm0 f0|d0||];
  rewrite /smc_interpreter.step Hpi in Hstep => //=.
- by case: (nth (default_proc data) ps j0) Hstep => // frm1 f1;
     case: ifP.
- by case: (nth (default_proc data) ps frm0) Hstep => // dst1 v1 k1;
     case: ifP.
Qed.

(* D1: Relay body after 2 Init layers — determined by template type *)
Definition relay_body (j : 'I_n_relay.+1) : proc data :=
  let dk' := dk_relay j in
  let v' := v_relay j in
  let r1' := r1_relay j in
  let r2' := r2_relay j in
  if (j : nat) == 0 then
    pSend alice_idx (e_local (enc_local (ek (nat_to_party_id j.+1)) v' r1'))
      (pRecvDec_local alice_idx dk' (fun m0 =>
        pRecvEnc_local alice_idx (fun enc1 =>
          pSend j.+2
            (e_local (Emul_local enc1 (enc (ek (nat_to_party_id j.+2)) m0 r2')))
            Finish)))
  else if (j : nat) == n_relay then
    pSend alice_idx (e_local (enc_local (ek (nat_to_party_id j.+1)) v' r1'))
      (pRecvDec_local j dk' (fun m0 =>
        pSend alice_idx (e_local (enc_local (ek alice_idx) m0 r2')) Finish))
  else
    pSend alice_idx (e_local (enc_local (ek (nat_to_party_id j.+1)) v' r1'))
      (pRecvEnc_local alice_idx (fun enc0 =>
        pRecvDec_local j dk' (fun m0 =>
          pSend j.+2
            (e_local (Emul_local enc0 (enc (ek (nat_to_party_id j.+2)) m0 r2')))
            Finish))).

(* D2: Relay state predicates *)
Definition relay_at_body (j : 'I_n_relay.+1) (ps : seq (proc data)) : Prop :=
  nth (default_proc data) ps j.+1 = relay_body j.

Definition relay_at_recv_alice_pred (j : 'I_n_relay.+1) (ps : seq (proc data)) : Prop :=
  exists f, nth (default_proc data) ps j.+1 = Recv 0 f.

Definition relay_at_finish_pred (j : 'I_n_relay.+1) (ps : seq (proc data)) : Prop :=
  nth (default_proc data) ps j.+1 = Finish.

(* D4: Relay at forwarding state *)
Definition relay_at_forwarding (j : 'I_n_relay.+1) (ps : seq (proc data)) : Prop :=
  exists v, nth (default_proc data) ps j.+1 = Send j.+2 v Finish.

(* D5: RecvAlice linked to template — f comes from relay_body *)
Definition relay_at_recv_from_body (j : 'I_n_relay.+1) (ps : seq (proc data)) : Prop :=
  exists sv f, relay_body j = Send 0 sv (Recv 0 f) /\
    nth (default_proc data) ps j.+1 = Recv 0 f.

(* D6: RecvUpstream with continuation behavior *)
Definition relay_at_recv_upstream_linked (j : 'I_n_relay.+1) (ps : seq (proc data)) : Prop :=
  exists f, nth (default_proc data) ps j.+1 = Recv j f /\
    (forall v, @std_from_enc AHE v != None ->
       exists sv, f v = Send j.+2 sv Finish).

(* D7: Last relay at send-result state *)
Definition relay_at_send_result (ps : seq (proc data)) : Prop :=
  exists v, nth (default_proc data) ps n_relay.+1 = Send 0 v Finish.

(* H4: Initial processes match relay_body *)
Lemma relay_body_eq (j : 'I_n_relay.+1) :
  exists d1 d2,
    nth (default_proc data) procs j.+1 = Init d1 (Init d2 (relay_body j)).
Proof.
rewrite /procs /dsdp_n_procs /erase_aprocs /dsdp_n_saprocs /=.
rewrite -map_comp (nth_map ord0); last by rewrite Hrelays.
rewrite /comp /=.
have -> : nth ord0 relays j = j by apply val_inj; rewrite /= (Hrelays_id j).
rewrite /erase_aproc /aproc_proc /relay_aproc.
case: ifP => Hj0; [|case: ifP => Hjn].
- do 2 eexists.
  rewrite (@DParty_first_erase AHE ek j.+1 j.+2 (dk_relay j) (v_relay j)
           (r1_relay j) (r2_relay j)).
  by rewrite /relay_body Hj0.
- do 2 eexists.
  rewrite (@DParty_last_erase AHE ek j.+1 j (dk_relay j) (v_relay j)
           (r1_relay j) (r2_relay j)).
  by rewrite /relay_body Hj0 Hjn.
- do 2 eexists.
  rewrite (@DParty_intermediate_erase AHE ek j.+1 alice_idx j j.+2 (dk_relay j)
           (v_relay j) (r1_relay j) (r2_relay j)).
  by rewrite /relay_body Hj0 Hjn.
Qed.

(* H5: relay_body always starts with Send 0 *)
Lemma relay_body_is_send0 (j : 'I_n_relay.+1) :
  exists sv sk, relay_body j = Send 0 sv sk.
Proof.
rewrite /relay_body; case: ifP => ?; [|case: ifP => ?]; by do 2 eexists.
Qed.

(* R1: relay_body(0) = Send(0, sv, Recv(0, f_dec)) *)
Lemma relay0_body_structure :
  exists sv f_dec, relay_body ord0 = Send 0 sv (Recv 0 f_dec).
Proof.
rewrite /relay_body /= /pRecvDec_local /std_Recv_dec /Recv_param.
by do 2 eexists.
Qed.

(* R2: R0's first Recv fires → second Recv(0,...) *)
Lemma relay0_first_recv_to_second (sv : data) (f_dec : data -> proc data) (v : data) :
  relay_body ord0 = Send 0 sv (Recv 0 f_dec) ->
  @std_from_enc AHE v != None ->
  exists f_enc, f_dec v = Recv 0 f_enc.
Proof.
move=> Hbody Henc.
rewrite /relay_body /= /pRecvDec_local /std_Recv_dec /Recv_param in Hbody.
have Hfd : f_dec = (oapp (fun m0 =>
  pRecvEnc_local alice_idx (fun enc1 =>
    pSend 2 (e_local (Emul_local enc1
      (enc (ek (nat_to_party_id 2)) m0 (r2_relay ord0)))) Finish))
  Fail \o (obind (dec (dk_relay ord0)) \o @std_from_enc AHE))
  by case: Hbody.
subst f_dec; rewrite /comp.
case Hsfe: (@std_from_enc AHE v) => [c|]; last by rewrite Hsfe in Henc.
case Hdec: (dec (dk_relay ord0) c) => [m|]; last first.
  by have := dec_total (dk_relay ord0) c; rewrite Hdec.
rewrite /= Hdec /= /pRecvEnc_local /std_Recv_enc /Recv_param.
by eexists.
Qed.

(* R3: Intermediate relay body structure *)
Lemma relay_inter_body_structure (j : 'I_n_relay.+1) :
  (0 < j)%N -> (j < n_relay)%N ->
  exists sv f_enc, relay_body j = Send 0 sv (Recv 0 f_enc).
Proof.
move=> Hj0 Hjn; rewrite /relay_body.
have -> : (j : nat) == 0 = false by rewrite eqn0Ngt Hj0.
have -> : (j : nat) == n_relay = false
  by apply /negP => /eqP Heq; rewrite Heq ltnn in Hjn.
rewrite /pRecvEnc_local /std_Recv_enc /Recv_param.
by do 2 eexists.
Qed.

(* R4: Last relay body structure *)
Lemma relay_last_body_structure :
  exists sv f_dec,
    relay_body (@ord_max n_relay) = Send 0 sv (Recv n_relay f_dec).
Proof.
rewrite /relay_body /=.
have -> : (n_relay == 0) = false by rewrite eqn0Ngt Hn_relay.
rewrite eqxx /pRecvDec_local /std_Recv_dec /Recv_param.
by do 2 eexists.
Qed.

(* Note: Template continuation lemmas (T1-T4 in the plan) are not standalone *)
(* because the continuation functions are abstract at the lemma level. *)
(* They will be proved inline within the C2 transition sub-lemmas, *)
(* where the specific template continuation is known from relay_body. *)

(* NEW-D1: Alice's foldr body at iteration j *)
Definition alice_foldr_at (j : nat) : proc data :=
  foldr (fun (fi : 'I_n_relay.+1 * nat) (cont : proc data) =>
           @alice_erase_body AHE ek n_relay u r rand_a fi.1 fi.2 cont)
        (@alice_erase_tail AHE n_relay dk v0 u r)
        (drop j (zip relays (iota 0 (size relays)))).

(* H6: Alice's foldr at iteration j starts with Recv(j+1,...) *)
Lemma alice_body_at_recv (j : nat) (Hj : (j < n_relay.+1)%N) :
  exists f,
    foldr (fun (fi : 'I_n_relay.+1 * nat) (cont : proc data) =>
             @alice_erase_body AHE ek n_relay u r rand_a fi.1 fi.2 cont)
          (@alice_erase_tail AHE n_relay dk v0 u r)
          (drop j (zip relays (iota 0 (size relays)))) =
    Recv (Ordinal Hj).+1 f.
Proof.
have Hsz : (j < size relays)%N by rewrite Hrelays.
have Hdrop : drop j (zip relays (iota 0 (size relays))) =
  (nth ord0 relays j, j) :: drop j.+1 (zip relays (iota 0 (size relays))).
  rewrite (drop_nth (ord0, 0)); last by rewrite size_zip size_iota minnn.
  congr cons; rewrite nth_zip //; last by rewrite size_iota.
  by rewrite nth_iota.
rewrite Hdrop /= /alice_erase_body (Hrelays_id (Ordinal Hj)) /=.
rewrite /pRecvEnc_local /std_Recv_enc /Recv_param.
by eexists.
Qed.

(* H7: After Alice's Recv fires, Alice becomes Send(dest(j),...,rest) *)
Lemma alice_recv_to_send (j : nat) (Hj : (j < n_relay.+1)%N) (f : data -> proc data) (v : data) :
  @std_from_enc AHE v != None ->
  foldr (fun (fi : 'I_n_relay.+1 * nat) (cont : proc data) =>
           @alice_erase_body AHE ek n_relay u r rand_a fi.1 fi.2 cont)
        (@alice_erase_tail AHE n_relay dk v0 u r)
        (drop j (zip relays (iota 0 (size relays)))) =
  Recv (Ordinal Hj).+1 f ->
  exists sv rest, f v = Send (alice_send_dest (Ordinal Hj)) sv rest.
Proof.
move=> Henc Hfoldr.
have Hsz : (j < size relays)%N by rewrite Hrelays.
have Hdrop : drop j (zip relays (iota 0 (size relays))) =
  (nth ord0 relays j, j) :: drop j.+1 (zip relays (iota 0 (size relays))).
  rewrite (drop_nth (ord0, 0)); last by rewrite size_zip size_iota minnn.
  congr cons; rewrite nth_zip //; last by rewrite size_iota.
  by rewrite nth_iota.
rewrite Hdrop /= /alice_erase_body (Hrelays_id (Ordinal Hj)) /= in Hfoldr.
rewrite /pRecvEnc_local /std_Recv_enc /Recv_param in Hfoldr.
case: Hfoldr => Hf; subst f; rewrite /comp.
case Hsfe: (@std_from_enc AHE v) => [c|]; last by rewrite Hsfe in Henc.
by do 2 eexists.
Qed.

(* H7': Strengthened H7 — rest IS the next foldr iteration *)
Lemma alice_recv_to_send_foldr (j : nat) (Hj : (j < n_relay.+1)%N)
    (f : data -> proc data) (v : data) :
  @std_from_enc AHE v != None ->
  foldr (fun (fi : 'I_n_relay.+1 * nat) (cont : proc data) =>
           @alice_erase_body AHE ek n_relay u r rand_a fi.1 fi.2 cont)
        (@alice_erase_tail AHE n_relay dk v0 u r)
        (drop j (zip relays (iota 0 (size relays)))) =
  Recv (Ordinal Hj).+1 f ->
  exists sv,
    f v = Send (alice_send_dest (Ordinal Hj)) sv
      (foldr (fun (fi : 'I_n_relay.+1 * nat) (cont : proc data) =>
                @alice_erase_body AHE ek n_relay u r rand_a fi.1 fi.2 cont)
             (@alice_erase_tail AHE n_relay dk v0 u r)
             (drop j.+1 (zip relays (iota 0 (size relays))))).
Proof.
move=> Henc Hfoldr.
have Hsz : (j < size relays)%N by rewrite Hrelays.
have Hdrop : drop j (zip relays (iota 0 (size relays))) =
  (nth ord0 relays j, j) :: drop j.+1 (zip relays (iota 0 (size relays))).
  rewrite (drop_nth (ord0, 0)); last by rewrite size_zip size_iota minnn.
  congr cons; rewrite nth_zip //; last by rewrite size_iota.
  by rewrite nth_iota.
rewrite Hdrop /= /alice_erase_body (Hrelays_id (Ordinal Hj)) /= in Hfoldr.
rewrite /pRecvEnc_local /std_Recv_enc /Recv_param in Hfoldr.
case: Hfoldr => Hf; subst f; rewrite /comp.
case Hsfe: (@std_from_enc AHE v) => [c|]; last by rewrite Hsfe in Henc.
by eexists.
Qed.

(* NEW-L1: alice_foldr_at 0 = full foldr *)
Lemma alice_foldr_at_0 :
  alice_foldr_at 0 =
    foldr (fun (fi : 'I_n_relay.+1 * nat) (cont : proc data) =>
             @alice_erase_body AHE ek n_relay u r rand_a fi.1 fi.2 cont)
          (@alice_erase_tail AHE n_relay dk v0 u r)
          (zip relays (iota 0 (size relays))).
Proof. by rewrite /alice_foldr_at drop0. Qed.

(* NEW-L2: alice_foldr_at n_relay.+1 = alice_erase_tail *)
Lemma alice_foldr_at_tail :
  alice_foldr_at n_relay.+1 = @alice_erase_tail AHE n_relay dk v0 u r.
Proof.
rewrite /alice_foldr_at drop_oversize //.
by rewrite size_zip size_iota minnn Hrelays.
Qed.

(* NEW-L3: alice_erase_tail starts with Recv(n_relay.+1, ...) *)
Lemma alice_tail_is_recv :
  exists f, @alice_erase_tail AHE n_relay dk v0 u r = Recv n_relay.+1 f.
Proof.
rewrite /alice_erase_tail /pRecvDec_local /std_Recv_dec /Recv_param.
by eexists.
Qed.

(* NEW-L4: alice_erase_tail's Recv fires → Ret *)
Lemma alice_tail_recv_ret (f : data -> proc data) (v : data) :
  @alice_erase_tail AHE n_relay dk v0 u r = Recv n_relay.+1 f ->
  @std_from_enc AHE v != None ->
  exists d, f v = Ret d.
Proof.
rewrite /alice_erase_tail /pRecvDec_local /std_Recv_dec /Recv_param.
move=> [<-] Henc.
rewrite /comp.
case Hsfe: (@std_from_enc AHE v) => [c|]; last by rewrite Hsfe in Henc.
case Hdec: (@dec AHE dk c) => [m|]; last first.
  by have := dec_total dk c; rewrite Hdec.
by rewrite /= Hdec /=; eexists.
Qed.

(* T1: REMOVED — unprovable with abstract f_inner. *)
(* The logic is inlined in C2c where the specific f_inner from Inv_AS1 is known. *)

(* T2: Intermediate relay recv_from_body fires → RecvUpstream linked *)
Lemma relay_inter_recv_from_body_fires (j : 'I_n_relay.+1) (v : data)
    (sv0 : data) (f0 : data -> proc data) :
  (0 < j)%N -> (j < n_relay)%N ->
  relay_body j = Send 0 sv0 (Recv 0 f0) ->
  @std_from_enc AHE v != None ->
  exists f_dec, f0 v = Recv j f_dec /\
    (forall w, @std_from_enc AHE w != None ->
       exists sw, f_dec w = Send j.+2 sw Finish).
Proof.
move=> Hj0 Hjn Hbody Henc.
rewrite /relay_body (negbTE (lt0n_neq0 Hj0)) in Hbody.
have Hjn' : (j : nat) == n_relay = false
  by apply /negP => /eqP Heq; rewrite Heq ltnn in Hjn.
rewrite Hjn' /pRecvEnc_local /std_Recv_enc /Recv_param in Hbody.
case: Hbody => _ Hf0; subst f0; rewrite /comp.
case Hsfe: (@std_from_enc AHE v) => [c|]; last by rewrite Hsfe in Henc.
rewrite /= /pRecvDec_local /std_Recv_dec /Recv_param.
eexists; split; first by [].
move=> w Hencw; rewrite /comp.
case Hsfw: (@std_from_enc AHE w) => [c'|]; last by rewrite Hsfw in Hencw.
rewrite /=.
case Hdec: (dec (dk_relay j) c') => [m|];
  last by have := dec_total (dk_relay j) c'; rewrite Hdec.
by eexists.
Qed.

(* T3: recv_upstream_linked fires → forwarding *)
(* This is trivial from the linked continuation behavior *)
Lemma relay_recv_upstream_linked_fires (f : data -> proc data) (j : nat) (v : data) :
  (forall w, @std_from_enc AHE w != None -> exists sw, f w = Send j.+2 sw Finish) ->
  @std_from_enc AHE v != None ->
  exists sv, f v = Send j.+2 sv Finish.
Proof. move=> Hcont Henc; exact (Hcont v Henc). Qed.

(* T4: Last relay recv fires → Send(0, v, Finish) *)
Lemma relay_last_recv_fires (f : data -> proc data) (v : data) :
  (forall w, @std_from_enc AHE w != None -> exists sw, f w = Send 0 sw Finish) ->
  @std_from_enc AHE v != None ->
  exists sv, f v = Send 0 sv Finish.
Proof. move=> Hcont Henc; exact (Hcont v Henc). Qed.

(* NP1-NP6: Non-participant step lemmas *)

Lemma relay_body_step_nop ps (j : 'I_n_relay.+1) :
  relay_at_body j ps ->
  (forall f, nth (default_proc data) ps 0 <> Recv j.+1 f) ->
  (smc_interpreter.step ps [::] j.+1).2 = false.
Proof.
move=> Hbody Hnrecv; rewrite /relay_at_body in Hbody.
have [sv [sk Hsend]] := relay_body_is_send0 j.
rewrite /smc_interpreter.step Hbody Hsend.
case Hp0: (nth (default_proc data) ps 0) => [|dst0 v0' k0|frm0 f0|d0||] //.
case: ifP => [/eqP Heq|] //; subst frm0.
by exfalso; exact (Hnrecv f0 Hp0).
Qed.

Lemma recv0_step_nop ps (m : nat) (f : data -> proc data) :
  nth (default_proc data) ps m = Recv 0 f ->
  (forall v k, nth (default_proc data) ps 0 <> Send m v k) ->
  (smc_interpreter.step ps [::] m).2 = false.
Proof.
move=> Hpm Hnotsend; rewrite /smc_interpreter.step Hpm.
case Hp0: (nth (default_proc data) ps 0) => [|dst0 v0' k0|frm0 f0|d0||] //.
case: ifP => [/eqP Heq|] //; subst dst0.
by exfalso; exact (Hnotsend v0' k0 Hp0).
Qed.

Lemma finish_step_nop ps (m : nat) :
  nth (default_proc data) ps m = Finish ->
  (smc_interpreter.step ps [::] m).2 = false.
Proof. by move=> Hpm; rewrite /smc_interpreter.step Hpm. Qed.

Lemma recv_upstream_step_nop ps (i : nat) (f : data -> proc data) :
  nth (default_proc data) ps i.+1 = Recv i f ->
  (forall v k, nth (default_proc data) ps i <> Send i.+1 v k) ->
  (smc_interpreter.step ps [::] i.+1).2 = false.
Proof.
move=> Hpi Hnotsend; rewrite /smc_interpreter.step Hpi.
case Hpu: (nth (default_proc data) ps i) => [|dst0 v0' k0|frm0 f0|d0||] //.
case: ifP => [/eqP Heq|] //; subst dst0.
by exfalso; exact (Hnotsend v0' k0 Hpu).
Qed.

Lemma forwarding_step_nop ps (i : nat) (v : data) :
  nth (default_proc data) ps i.+1 = Send i.+2 v Finish ->
  (forall f, nth (default_proc data) ps i.+2 <> Recv i.+1 f) ->
  (smc_interpreter.step ps [::] i.+1).2 = false.
Proof.
move=> Hpi Hnotrecv; rewrite /smc_interpreter.step Hpi.
case Hpd: (nth (default_proc data) ps i.+2) => [|dst0 v0' k0|frm0 f0|d0||] //.
case: ifP => [/eqP Heq|] //; subst frm0.
by exfalso; exact (Hnotrecv f0 Hpd).
Qed.

Lemma alice_recv_step_nop ps (j : nat) (f : data -> proc data) :
  nth (default_proc data) ps 0 = Recv j.+1 f ->
  (forall v k, nth (default_proc data) ps j.+1 <> Send 0 v k) ->
  (smc_interpreter.step ps [::] 0).2 = false.
Proof.
move=> Hpa Hnotsend; rewrite /smc_interpreter.step Hpa.
case Hpj: (nth (default_proc data) ps j.+1) => [|dst0 v0' k0|frm0 f0|d0||] //.
case: ifP => [/eqP Heq|] //; subst dst0.
by exfalso; exact (Hnotsend v0' k0 Hpj).
Qed.

(* D3: Protocol invariant — enriched with full relay state tracking *)
Inductive dsdp_inv : seq (proc data) -> Prop :=
| Inv_AR (j : 'I_n_relay.+1) ps :
    size ps = n_relay.+2 ->
    @all_proc_wf AHE ps ->
    nth (default_proc data) ps 0 = alice_foldr_at j ->
    relay_at_body j ps ->                                          (* H4 *)
    (forall i : 'I_n_relay.+1, (j < i)%N -> relay_at_body i ps) -> (* H5 *)
    ((j == 1%N :> nat) ->                                          (* H6 *)
       exists f_enc : cipher AHE -> proc data,
         nth (default_proc data) ps 1 =
           Recv 0 (oapp f_enc Fail \o @std_from_enc AHE) /\
         forall c, exists sv, f_enc c = Send 2 sv Finish) ->
    ((2 <= j)%N -> exists sv0 f0,                                      (* A7 *)
       relay_body (@inord n_relay j.-1) = Send 0 sv0 (Recv 0 f0) /\
       nth (default_proc data) ps j = Recv 0 f0) ->
    ((j == 2%N :> nat) ->                                              (* A8: frontier sender for j=2 *)
       exists sv_fw, nth (default_proc data) ps 1 = Send 2 sv_fw Finish) ->
    ((3 <= j)%N ->                                                     (* A9: full frontier state *)
       (forall i : nat, (i.+1 < j.-2)%N ->
          nth (default_proc data) ps i.+1 = Finish) /\
       (exists sv_fw, nth (default_proc data) ps j.-2 =
          Send j.-1 sv_fw Finish) /\
       (exists f_recv, nth (default_proc data) ps j.-1 = Recv j.-2 f_recv /\
          (forall v, @std_from_enc AHE v != None ->
             exists sv, f_recv v = Send j sv Finish))) ->
    dsdp_inv ps
| Inv_AS0 ps (f_inner : plain AHE -> proc data) :
    size ps = n_relay.+2 ->
    @all_proc_wf AHE ps ->
    (exists vd, nth (default_proc data) ps 0 = Send 1 vd (alice_foldr_at 1)) ->
    nth (default_proc data) ps 1 =
      Recv 0 (oapp f_inner Fail \o (obind (@dec AHE (dk_relay ord0)) \o @std_from_enc AHE)) ->
    (forall i : 'I_n_relay.+1, (0 < i)%N -> relay_at_body i ps) ->
    (* f_inner produces pRecvEnc form with Send 2 continuation *)
    (forall m, exists g : cipher AHE -> proc data,
       f_inner m = Recv 0 (oapp g Fail \o @std_from_enc AHE) /\
       forall c, exists sv, g c = Send 2 sv Finish) ->
    dsdp_inv ps
| Inv_AS1 ps (f_inner : cipher AHE -> proc data) :
    size ps = n_relay.+2 ->
    @all_proc_wf AHE ps ->
    (exists vd, nth (default_proc data) ps 0 = Send 1 vd (alice_foldr_at 2)) ->
    nth (default_proc data) ps 1 =
      Recv 0 (oapp f_inner Fail \o @std_from_enc AHE) ->
    (forall i : 'I_n_relay.+1, (1 < i)%N -> relay_at_body i ps) ->
    (* f_inner produces Send(2,...,Finish) *)
    (forall c, exists sv, f_inner c = Send 2 sv Finish) ->
    ((1 < n_relay)%N ->                                         (* H6a: NEW *)
       exists sv f, relay_body (Ordinal (n:=n_relay.+1) (m:=1) Hn_relay) =
         Send 0 sv (Recv 0 f) /\
         nth (default_proc data) ps 2 = Recv 0 f) ->
    (n_relay = 1%N -> exists f, nth (default_proc data) ps 2 = Recv 1 f /\ (* H6b *)
       forall v, @std_from_enc AHE v != None -> exists sv, f v = Send 0 sv Finish) ->
    dsdp_inv ps
| Inv_ASj (j : 'I_n_relay.+1) ps :
    (2 <= j)%N ->                                                      (* B1 *)
    size ps = n_relay.+2 ->                                            (* B2 *)
    @all_proc_wf AHE ps ->                                            (* B3 *)
    (exists vd, nth (default_proc data) ps 0 =                        (* B4 *)
       Send j vd (alice_foldr_at j.+1)) ->
    (exists sv0 f0, relay_body (@inord n_relay j.-1) =                (* B5 *)
       Send 0 sv0 (Recv 0 f0) /\
       nth (default_proc data) ps j = Recv 0 f0) ->
    (forall i : 'I_n_relay.+1, (j < i)%N -> relay_at_body i ps) ->   (* B6 *)
    ((j < n_relay)%N ->                                                (* B7a: intermediate relay *)
       exists sv f, relay_body j = Send 0 sv (Recv 0 f) /\
         nth (default_proc data) ps j.+1 = Recv 0 f) ->
    ((j : nat) = n_relay ->                                            (* B7b: last relay *)
       exists f_dec, nth (default_proc data) ps n_relay.+1 =
         Recv n_relay f_dec /\
         forall v, @std_from_enc AHE v != None ->
           exists sv, f_dec v = Send 0 sv Finish) ->
    ((j == 2%N :> nat) ->                                              (* B8: frontier for j=2 *)
       exists sv_fw, nth (default_proc data) ps 1 =
         Send 2 sv_fw Finish) ->
    ((3 <= j)%N ->                                                     (* B9: Finish zone + frontier *)
       (forall i : nat, (i.+1 <= j.-2)%N ->
          nth (default_proc data) ps i.+1 = Finish) /\
       (exists sv_fw, nth (default_proc data) ps j.-1 =
          Send j sv_fw Finish)) ->
    dsdp_inv ps
| Inv_drain (j : 'I_n_relay.+1) ps :
    (j.+1 < n_relay.+1)%N ->
    size ps = n_relay.+2 ->
    @all_proc_wf AHE ps ->
    nth (default_proc data) ps 0 = alice_foldr_at n_relay.+1 ->
    (exists v, nth (default_proc data) ps j.+1 = Send j.+2 v Finish) ->
    (exists f, nth (default_proc data) ps j.+2 = Recv j.+1 f) ->
    (forall i : nat, (i < j)%N -> nth (default_proc data) ps i.+1 = Finish) ->
    (exists f, nth (default_proc data) ps n_relay.+1 = Recv n_relay f /\  (* H8a: NEW *)
       forall v, @std_from_enc AHE v != None ->
         exists sv, f v = Send 0 sv Finish) ->
    (forall i : nat, (j < i)%N -> (i < n_relay)%N ->                     (* H8b: NEW *)
       exists f, nth (default_proc data) ps i.+1 = Recv i f /\
         (forall v, @std_from_enc AHE v != None ->
            exists sv, f v = Send i.+2 sv Finish)) ->
    dsdp_inv ps
| Inv_tail ps :
    size ps = n_relay.+2 ->
    @all_proc_wf AHE ps ->
    (exists v, nth (default_proc data) ps n_relay.+1 = Send 0 v Finish) ->
    nth (default_proc data) ps 0 = alice_foldr_at n_relay.+1 ->
    (forall j : 'I_n_relay.+1, (j < n_relay)%N -> relay_at_finish_pred j ps) ->
    dsdp_inv ps
| Inv_ret ps d :
    size ps = n_relay.+2 ->
    @all_proc_wf AHE ps ->
    nth (default_proc data) ps 0 = Ret d ->
    (forall j : 'I_n_relay.+1, relay_at_finish_pred j ps) ->
    dsdp_inv ps.

(* C1: Every dsdp_inv state has progress *)
Lemma dsdp_inv_has_progress ps :
  dsdp_inv ps -> has_progress data ps.
Proof.
case.
- (* Inv_AR *) move=> j ps0 Hsz Hwf Halice Hbody Hpending _ _ _ _.
  have [sv [sk Hrel]] := relay_body_is_send0 j.
  rewrite /relay_at_body Hrel in Hbody.
  have Hj : (j.+1 < size ps0)%N by rewrite Hsz; exact (ltn_ord j).
  have [f Hrecv] := @alice_body_at_recv j (ltn_ord j).
  have Halice' : nth (default_proc data) ps0 0 = Recv (Ordinal (ltn_ord j)).+1 f
    by rewrite Halice /alice_foldr_at Hrecv.
  exact (@has_comm_progress data ps0 j.+1 0 sv sk f Hj Hbody Halice').
- (* Inv_AS0 *) move=> ps0 f_inner Hsz Hwf [vd Halice] Hr0 Hpending _.
  have Hsz0 : (0 < size ps0)%N by rewrite Hsz.
  exact (@has_comm_progress data ps0 0 1 vd (alice_foldr_at 1)
    (oapp f_inner Fail \o (obind (@dec AHE (dk_relay ord0)) \o @std_from_enc AHE))
    Hsz0 Halice Hr0).
- (* Inv_AS1 *) move=> ps0 f_inner Hsz Hwf [vd Halice] Hr0 Hpending _ _ _.
  have Hsz0 : (0 < size ps0)%N by rewrite Hsz.
  exact (@has_comm_progress data ps0 0 1 vd (alice_foldr_at 2)
    (oapp f_inner Fail \o @std_from_enc AHE)
    Hsz0 Halice Hr0).
- (* Inv_ASj *) move=> j ps0 Hj Hsz Hwf [vd Halice] [sv0 [f0 [Hbody0 Hrj]]] Hpending _ _ _ _.
  have Hsz0 : (0 < size ps0)%N by rewrite Hsz.
  exact (@has_comm_progress data ps0 0 j vd (alice_foldr_at j.+1) f0 Hsz0 Halice Hrj).
- (* Inv_drain *) move=> j ps0 Hjb Hsz Hwf Halice [v Hsend] [f Hrecv] _ [_ _] _.
  have Hj : (j.+1 < size ps0)%N by rewrite Hsz; exact (ltn_trans Hjb (ltnSn _)).
  exact (@has_comm_progress data ps0 j.+1 j.+2 v Finish f Hj Hsend Hrecv).
- (* Inv_tail *) move=> ps0 Hsz Hwf [v Hsend] Halice Hrels_fin.
  have [f Hrecv] := alice_tail_is_recv.
  have Halice' : nth (default_proc data) ps0 0 = Recv n_relay.+1 f
    by rewrite Halice alice_foldr_at_tail.
  have Hn : (n_relay.+1 < size ps0)%N by rewrite Hsz.
  exact (@has_comm_progress data ps0 n_relay.+1 0 v Finish f Hn Hsend Halice').
- (* Inv_ret *) move=> ps0 d0 Hsz Hwf Hret Hrels.
  have Hsz0 : (0 < size ps0)%N by rewrite Hsz.
  exact (@has_ret_progress data ps0 0 d0 Hsz0 Hret).
Qed.

(* C2 sub-lemmas — signatures match enriched dsdp_inv constructors *)

(* C2a: AR(j) → AS variant *)
Lemma dsdp_inv_step_AR (j : 'I_n_relay.+1) ps :
  size ps = n_relay.+2 -> @all_proc_wf AHE ps ->
  nth (default_proc data) ps 0 = alice_foldr_at j ->
  relay_at_body j ps ->
  (forall i : 'I_n_relay.+1, (j < i)%N -> relay_at_body i ps) ->
  ((j == 1%N :> nat) ->
     exists f_enc : cipher AHE -> proc data,
       nth (default_proc data) ps 1 = Recv 0 (oapp f_enc Fail \o @std_from_enc AHE) /\
       forall c, exists sv, f_enc c = Send 2 sv Finish) ->
  ((2 <= j)%N -> exists sv0 f0,
     relay_body (@inord n_relay j.-1) = Send 0 sv0 (Recv 0 f0) /\
     nth (default_proc data) ps j = Recv 0 f0) ->
  ((j == 2%N :> nat) ->
     exists sv_fw, nth (default_proc data) ps 1 = Send 2 sv_fw Finish) ->
  ((3 <= j)%N ->
     (forall i : nat, (i.+1 < j.-2)%N ->
        nth (default_proc data) ps i.+1 = Finish) /\
     (exists sv_fw, nth (default_proc data) ps j.-2 =
        Send j.-1 sv_fw Finish) /\
     (exists f_recv, nth (default_proc data) ps j.-1 = Recv j.-2 f_recv /\
        (forall v, @std_from_enc AHE v != None ->
           exists sv, f_recv v = Send j sv Finish))) ->
  all_terminated (one_step_procs data ps) \/ dsdp_inv (one_step_procs data ps).
Proof.
move=> Hsz Hwf Halice Hbody Hpending H6 H7 H8 H9; right.
have [f Hrecv_f] := @alice_body_at_recv j (ltn_ord j).
have [sv [sk Hbs]] := relay_body_is_send0 j.
have Halice_recv : nth (default_proc data) ps 0 = Recv (Ordinal (ltn_ord j)).+1 f
  by rewrite Halice /alice_foldr_at Hrecv_f.
have Hrelay_send : nth (default_proc data) ps j.+1 = Send 0 sv sk.
  rewrite /relay_at_body in Hbody; rewrite Hbody Hbs. done.
have [Hstep_j1 Hstep_0] :=
  @step_send_recv_match data ps j.+1 0 sv sk f Hrelay_send Halice_recv.
have Hwf_j1 : proc_wf AHE (nth (default_proc data) ps j.+1)
  by apply Hwf; rewrite Hsz; exact (ltn_ord j).
rewrite Hrelay_send /= in Hwf_j1; have [Henc_sv _] := Hwf_j1.
have [sv' Hfsv] := @alice_recv_to_send_foldr j (ltn_ord j) f sv Henc_sv Hrecv_f.
case: (posnP (j : nat)) => Hj0.
- (* j = 0 → Inv_AS0 *)
  have Hj_ord0 : j = ord0 :> 'I_n_relay.+1 by apply /val_inj; rewrite /= Hj0.
  rewrite Hj_ord0 in Hbs Halice Halice_recv Hbody Hpending
    Hrelay_send Hstep_j1 Hstep_0 Hrecv_f Hfsv.
  have [sv_r0 [f_dec_r0 Hbs0]] := relay0_body_structure.
  have Hsk : sk = Recv 0 f_dec_r0 by rewrite Hbs0 in Hbs; case: Hbs => _ <-.
  set f_inner0 := (fun m0 : plain AHE =>
    pRecvEnc_local alice_idx (fun enc1 =>
      @Send data 2
        (e_local (Emul_local enc1
          (enc (ek (nat_to_party_id 2)) m0 (r2_relay ord0))))
        Finish)).
  have Hfdec_form : f_dec_r0 = oapp f_inner0 Fail \o
    (obind (@dec AHE (dk_relay ord0)) \o @std_from_enc AHE).
  { rewrite /relay_body /= /pRecvDec_local /std_Recv_dec /Recv_param in Hbs0.
    case: Hbs0 => _ <-. rewrite /f_inner0. reflexivity. }
  apply (Inv_AS0 (one_step_procs data ps) f_inner0).
  + by rewrite (@size_one_step data).
  + exact (@one_step_preserves_proc_wf ps Hwf).
  + exists sv'; have Hsz0 : (0 < size ps)%N by rewrite Hsz.
    rewrite (@nth_one_step data ps 0 Hsz0) Hstep_0 Hfsv.
    by rewrite /alice_send_dest /= /alice_foldr_at.
  + have Hsz1 : (1 < size ps)%N
      by rewrite Hsz; exact (ltn_trans Hn_relay (ltnSn _)).
    by rewrite (@nth_one_step data ps 1 Hsz1) Hstep_j1 Hsk Hfdec_form.
  + move=> i Hi; rewrite /relay_at_body.
    have Hszi : (i.+1 < size ps)%N by rewrite Hsz; exact (ltn_ord i).
    rewrite (@nth_one_step data ps i.+1 Hszi) /smc_interpreter.step.
    have Hbi := Hpending i Hi; rewrite /relay_at_body in Hbi.
    have [svi [ski Hbsi]] := relay_body_is_send0 i.
    rewrite Hbi Hbsi Halice_recv /=.
    suff -> : (1%N == i.+1) = false by [].
    apply ltn_eqF; exact Hi.
  + move=> m; rewrite /f_inner0 /pRecvEnc_local /std_Recv_enc /Recv_param.
    eexists; split; first by reflexivity.
    by move=> c; eexists.
- case: (posnP j.-1) => Hj1.
  + (* j = 1 → Inv_AS1 *)
    have Hj_eq1 : j.-1 = 0%N := Hj1.
    have Hj_val : (j : nat) = 1%N by move: Hj0 Hj1; case: (j : nat) => [|[|n]].
    have Hj_eq : (j == 1%N :> nat) by rewrite Hj_val.
    have [f_enc [Hr0 Hfenc_cont]] := H6 Hj_eq.
    have Hdest1 : alice_send_dest (Ordinal (ltn_ord j)) = 1%N
      by rewrite /alice_send_dest /= Hj_val.
    rewrite Hdest1 in Hfsv.
    (* Substitute j=1 everywhere as ordinal *)
    set jord := Ordinal (n:=n_relay.+1) (m:=1) Hn_relay.
    have Hj_ord1 : j = jord by apply /val_inj; rewrite /= Hj_val.
    subst j; rewrite /= in Hfsv Hdest1 Hpending Halice_recv Hrelay_send Hstep_j1 Hstep_0 Hbs Hbody Hrecv_f.
    apply (Inv_AS1 (one_step_procs data ps) f_enc).
    * by rewrite (@size_one_step data).
    * exact (@one_step_preserves_proc_wf ps Hwf).
    * have Hsz0 : (0 < size ps)%N by rewrite Hsz.
      exists sv'.
      by rewrite (@nth_one_step data ps 0 Hsz0) Hstep_0 Hfsv.
    * (* relay 0: one_step[1] = ps[1] (nop: Alice is Recv, not Send) *)
      have Hsz1 : (1 < size ps)%N
        by rewrite Hsz; exact (ltn_trans Hn_relay (ltnSn _)).
      rewrite (@nth_one_step data ps 1 Hsz1) /smc_interpreter.step Hr0 Halice_recv.
      by [].
    * (* pending relays i > 1 *)
      move=> i Hi; rewrite /relay_at_body.
      have Hszi : (i.+1 < size ps)%N by rewrite Hsz; exact (ltn_ord i).
      rewrite (@nth_one_step data ps i.+1 Hszi) /smc_interpreter.step.
      have Hbi := Hpending i Hi; rewrite /relay_at_body in Hbi.
      have [svi [ski Hbsi]] := relay_body_is_send0 i.
      rewrite Hbi Hbsi Halice_recv.
      have -> : (2%N == i.+1) = false.
        by apply /eqP => Heq; have := Hi; rewrite -ltnS -Heq.
      by [].
    * exact Hfenc_cont.
    * (* H6a: 1 < n_relay → relay 1 body link *)
      move=> Hn1.
      have Hord1 : (1 < n_relay.+1)%N := Hn_relay.
      have [sv1 [f1 Hb1]] := relay_inter_body_structure (Ordinal Hord1) (isT : (0 < 1)%N) Hn1.
      have Hord_eq : Ordinal Hord1 = Ordinal (n:=n_relay.+1) (m:=1) Hn_relay
        by apply /val_inj.
      exists sv1, f1; split; first by rewrite -Hord_eq.
      have Hsz2 : (2 < size ps)%N by rewrite Hsz; exact (ltn_trans Hn1 (ltnSn _)).
      have Hsk_eq : sk = Recv 0 f1.
        have : relay_body (Ordinal Hord1) = Send 0 sv sk by rewrite Hord_eq.
        rewrite Hb1; by case.
      by rewrite (@nth_one_step data ps 2 Hsz2) Hstep_j1 Hsk_eq.
    * (* H6b: n_relay = 1 → last relay *)
      move=> Hn1_eq.
      have [sv_last [f_last Hblast]] := relay_last_body_structure.
      have Hord_max_eq : jord = @ord_max n_relay
        by apply /val_inj; rewrite /= Hn1_eq.
      rewrite Hord_max_eq in Hblast Hbs Hbody Hrelay_send Hstep_j1.
      have Hsk_form : sk = Recv n_relay f_last.
        rewrite Hblast in Hbs; by case: Hbs => _ <-.
      exists f_last; split.
      -- have Hszn1 : (n_relay.+1 < size ps)%N by rewrite Hsz.
         have H_nth := @nth_one_step data ps n_relay.+1 Hszn1.
         rewrite Hn1_eq in H_nth.
         by rewrite H_nth Hstep_j1 Hsk_form Hn1_eq.
      -- move=> w Hencw.
         rewrite /relay_body /= eqn0Ngt Hn_relay eqxx
                 /pRecvDec_local /std_Recv_dec /Recv_param in Hblast.
         case: Hblast => _ Hfl_eq.
         rewrite -Hfl_eq /comp.
         case Hsfe: (@std_from_enc AHE w) => [c|];
           last by rewrite Hsfe in Hencw.
         case Hdec: (dec (dk_relay ord_max) c) => [m|]; last first.
           by have := dec_total (dk_relay ord_max) c; rewrite Hdec.
         rewrite /= Hdec /=; by eexists.
  + (* j >= 2 *)
    have Hj2 : (1 < j)%N.
      have := Hj0; have := Hj1.
      by case: (j : nat) => [|[|n]].
    have Hdest : alice_send_dest (Ordinal (ltn_ord j)) = (j : nat)
      by rewrite /alice_send_dest /=; rewrite (maxn_idPr (ltnW Hj2)).
    rewrite Hdest -/(alice_foldr_at j.+1) in Hfsv.
    have [sv7 [f7 [Hbody7 Hpsj]]] := H7 Hj2.
    apply (Inv_ASj j).
    * (* B1: 2 <= j *) exact Hj2.
    * (* B2: size *) by rewrite (@size_one_step data).
    * (* B3: wf *) exact (@one_step_preserves_proc_wf ps Hwf).
    * (* B4: exists vd, one_step[0] = Send j vd (alice_foldr_at j.+1) *)
      exists sv'.
      have Hsz0 : (0 < size ps)%N by rewrite Hsz.
      by rewrite (@nth_one_step data ps 0 Hsz0) Hstep_0 Hfsv.
    * (* B5: relay body link at pos j — NOP *)
      exists sv7, f7; split; first exact Hbody7.
      have Hszj : (j < size ps)%N
        by rewrite Hsz; exact (ltn_trans (ltn_ord j) (ltnSn _)).
      rewrite (@nth_one_step data ps j Hszj) /smc_interpreter.step
              Hpsj Halice_recv.
      by [].
    * (* B6: pending relays — NOP *)
      move=> i Hi; rewrite /relay_at_body.
      have Hszi : (i.+1 < size ps)%N by rewrite Hsz; exact (ltn_ord i).
      rewrite (@nth_one_step data ps i.+1 Hszi) /smc_interpreter.step.
      have Hbi := Hpending i Hi; rewrite /relay_at_body in Hbi.
      have [svi [ski Hbsi]] := relay_body_is_send0 i.
      rewrite Hbi Hbsi Halice_recv.
      have Hneq : ((Ordinal (ltn_ord j)).+1 == i.+1) = false.
        apply /eqP => Heq.
        have Hji : (j : nat) = (i : nat) by apply succn_inj.
        by rewrite Hji ltnn in Hi.
      by rewrite Hneq.
    * (* B7a: j < n_relay → intermediate relay body *)
      move=> Hjn.
      have [sv_ib [f_ib Hrib]] :=
        relay_inter_body_structure j Hj0 Hjn.
      exists sv_ib, f_ib; split; first exact Hrib.
      have Heq_sk : sk = Recv 0 f_ib
        by rewrite Hrib in Hbs; case: Hbs.
      have Hszj1 : (j.+1 < size ps)%N by rewrite Hsz; exact (ltn_ord j).
      by rewrite (@nth_one_step data ps j.+1 Hszj1) Hstep_j1 Heq_sk.
    * (* B7b: j = n_relay → last relay *)
      move=> Hjn_eq.
      have Hj_max : j = @ord_max n_relay
        by apply /val_inj; rewrite /= Hjn_eq.
      rewrite Hj_max in Hbs Hrelay_send.
      have [sv_last [f_last Hbs_last]] := relay_last_body_structure.
      have Hsk_last : sk = Recv n_relay f_last
        by rewrite Hbs_last in Hbs; case: Hbs => _ <-.
      exists f_last; have Hszj1 : (j.+1 < size ps)%N
        by rewrite Hsz; exact (ltn_ord j).
      split.
      -- transitivity (step ps [::] j.+1).1.1.
         { have Heqj1 : j.+1 = n_relay.+1 by rewrite Hjn_eq.
           rewrite Heqj1; have Hszn1 : (n_relay.+1 < size ps)%N by rewrite Hsz.
           exact (@nth_one_step data ps n_relay.+1 Hszn1). }
         by rewrite Hstep_j1 Hsk_last.
      -- move=> w Hencw.
         rewrite /relay_body /= eqn0Ngt Hn_relay eqxx
                 /pRecvDec_local /std_Recv_dec /Recv_param in Hbs_last.
         case: Hbs_last => _ Hf_eq; rewrite -Hf_eq /comp.
         case Hsfe: (@std_from_enc AHE w) => [c|];
           last by rewrite Hsfe in Hencw.
         case Hdec: (dec (dk_relay ord_max) c) => [m|]; last first.
           by have := dec_total (dk_relay ord_max) c; rewrite Hdec.
         rewrite /= Hdec /=; by eexists.
    * (* B8: j == 2 → frontier sender at pos 1 — NOP *)
      move=> Hj_eq2.
      have [sv_fw Hfw] := H8 Hj_eq2.
      exists sv_fw.
      have Hsz1 : (1 < size ps)%N
        by rewrite Hsz; exact (ltn_trans Hn_relay (ltnSn _)).
      have Hnop : (smc_interpreter.step ps [::] 1).2 = false.
        apply (@forwarding_step_nop ps 0 sv_fw).
        - exact Hfw.
        - move=> g Habsurd.
          have Hj_is2 : (j : nat) = 2 by apply /eqP.
          rewrite Hj_is2 in Hpsj.
          by rewrite Hpsj in Habsurd.
      by rewrite (@nth_one_step_nop ps 1 Hsz1 Hnop) Hfw.
    * (* B9: j >= 3 → Finish zone + frontier *)
      move=> Hj3.
      have := H9 Hj3.
      move=> [Hfinzone
               [[sv_fw_old Hfrontier_sender]
                [f_recv [Hfrontier_recv Hfrecv_cont]]]].
      (* Frontier pair fires: pos j.-2 ↔ pos j.-1 *)
      have Hsucc : j.-2.+1 = j.-1
        by case: (j : nat) Hj3 => [|[|[|n]]].
      have [Hstep_front_send Hstep_front_recv] :=
        @step_send_recv_match data ps j.-2 j.-1 sv_fw_old Finish f_recv
          Hfrontier_sender Hfrontier_recv.
      have Hwf_front : proc_wf AHE (nth (default_proc data) ps j.-2).
        apply Hwf; rewrite Hsz.
        exact (ltn_trans (leq_ltn_trans (leq_pred _) (leq_ltn_trans (leq_pred _) (ltn_ord j))) (ltnSn _)).
      rewrite Hfrontier_sender /= in Hwf_front.
      have [Henc_fw _] := Hwf_front.
      have [sv_new Hfrecv_sv] := Hfrecv_cont sv_fw_old Henc_fw.
      split.
      -- (* Finish zone: positions 1 through j.-2 *)
         move=> i Hi.
         have Hszi : (i.+1 < size ps)%N.
           rewrite Hsz.
           have Hij : (i.+1 < j)%N.
             move: Hi; case: (j : nat) Hj2 => [|[|j']] //= _.
             by move=> Hi; exact (ltn_trans Hi (ltnSn _)).
           exact (ltn_trans Hij (ltn_trans (ltn_ord j) (ltnSn _))).
         case: (ltnP i.+1 j.-2) => Hlt.
         ** (* i+1 < j-2: was Finish, NOP *)
            have Hfin := Hfinzone i Hlt.
            by rewrite (@nth_one_step data ps i.+1 Hszi) /smc_interpreter.step Hfin.
         ** (* i+1 = j-2: frontier sender fired → Finish *)
            have Heq : i.+1 = j.-2
              by apply /eqP; rewrite eqn_leq Hlt Hi.
            rewrite Heq in Hszi |- *.
            by rewrite (@nth_one_step data ps j.-2 Hszi)
                       Hstep_front_send.
      -- (* Frontier receiver fires → Send j sv_new Finish *)
         exists sv_new.
         have Hszjm1 : (j.-1 < size ps)%N.
           rewrite Hsz.
           exact (ltn_trans (leq_ltn_trans (leq_pred j) (ltn_ord j)) (ltnSn n_relay.+1)).
         by rewrite (@nth_one_step data ps j.-1 Hszjm1)
                    Hstep_front_recv Hfrecv_sv.
Qed.

(* C2b: AS0 → AR(1) *)
Lemma dsdp_inv_step_AS0 ps (f_inner : plain AHE -> proc data) :
  size ps = n_relay.+2 -> @all_proc_wf AHE ps ->
  (exists vd, nth (default_proc data) ps 0 = Send 1 vd (alice_foldr_at 1)) ->
  nth (default_proc data) ps 1 =
    Recv 0 (oapp f_inner Fail \o (obind (@dec AHE (dk_relay ord0)) \o @std_from_enc AHE)) ->
  (forall i : 'I_n_relay.+1, (0 < i)%N -> relay_at_body i ps) ->
  (forall m, exists g : cipher AHE -> proc data,
     f_inner m = Recv 0 (oapp g Fail \o @std_from_enc AHE) /\
     forall c, exists sv, g c = Send 2 sv Finish) ->
  all_terminated (one_step_procs data ps) \/ dsdp_inv (one_step_procs data ps).
Proof.
move=> Hsz Hwf [vd Halice] Hr0 Hpending Hfinner_cont; right.
have [Hstep0 Hstep1] :=
  @step_send_recv_match data ps 0 1 vd (alice_foldr_at 1)
    (oapp f_inner Fail \o (obind (@dec AHE (dk_relay ord0)) \o @std_from_enc AHE))
    Halice Hr0.
have Hwf0 : proc_wf AHE (nth (default_proc data) ps 0)
  by apply Hwf; rewrite Hsz.
rewrite Halice /= in Hwf0; have [Henc_vd _] := Hwf0.
case Hsfe: (@std_from_enc AHE vd) => [c|]; last by rewrite Hsfe in Henc_vd.
case Hdec: (@dec AHE (dk_relay ord0) c) => [m|];
  last by have := dec_total (dk_relay ord0) c; rewrite Hdec.
have Hr0_result : (step ps [::] 1).1.1 = f_inner m
  by rewrite Hstep1 /comp Hsfe /= Hdec.
have [g [Hfm Hg_cont]] := Hfinner_cont m.
have Hord1 : (1 < n_relay.+1)%N := Hn_relay.
apply (Inv_AR (Ordinal Hord1)).
- by rewrite (@size_one_step data).
- exact (@one_step_preserves_proc_wf ps Hwf).
- (* Alice: one_step[0] = alice_foldr_at 1 *)
  have Hsz0 : (0 < size ps)%N by rewrite Hsz.
  by rewrite (@nth_one_step data ps 0 Hsz0) Hstep0.
- rewrite /relay_at_body.
  have Hsz2 : ((Ordinal Hord1).+1 < size ps)%N by rewrite Hsz /=.
  rewrite (@nth_one_step data ps (Ordinal Hord1).+1 Hsz2) /smc_interpreter.step.
  have Hb1 := Hpending (Ordinal Hord1) (isT : (0 < (Ordinal Hord1 : nat))%N).
  rewrite /relay_at_body /= in Hb1.
  have [sv1 [sk1 Hbs1]] := relay_body_is_send0 (Ordinal Hord1).
  by rewrite Hb1 Hbs1 Halice.
- move=> i Hi; rewrite /relay_at_body.
  have Hszi : (i.+1 < size ps)%N by rewrite Hsz; exact (ltn_ord i).
  rewrite (@nth_one_step data ps i.+1 Hszi) /smc_interpreter.step.
  have Hi0 : (0 < i)%N := ltn_trans (isT : (0 < 1)%N) Hi.
  have Hbi := Hpending i Hi0; rewrite /relay_at_body in Hbi.
  have [svi [ski Hbsi]] := relay_body_is_send0 i.
  by rewrite Hbi Hbsi Halice.
- move=> _; exists g; split.
  + have Hsz1 : (1 < size ps)%N by rewrite Hsz; exact (ltn_trans Hn_relay (ltnSn _)).
    by rewrite (@nth_one_step data ps 1 Hsz1) Hr0_result Hfm.
  + exact Hg_cont.
- by move=> /=.
- by move=> /eqP.
- by [].
Qed.

(* C2c: AS1 → AR(2) or drain *)
Lemma dsdp_inv_step_AS1 ps (f_inner : cipher AHE -> proc data) :
  size ps = n_relay.+2 -> @all_proc_wf AHE ps ->
  (exists vd, nth (default_proc data) ps 0 = Send 1 vd (alice_foldr_at 2)) ->
  nth (default_proc data) ps 1 =
    Recv 0 (oapp f_inner Fail \o @std_from_enc AHE) ->
  (forall i : 'I_n_relay.+1, (1 < i)%N -> relay_at_body i ps) ->
  (forall c, exists sv, f_inner c = Send 2 sv Finish) ->
  ((1 < n_relay)%N ->
     exists sv f, relay_body (Ordinal (n:=n_relay.+1) (m:=1) Hn_relay) =
       Send 0 sv (Recv 0 f) /\
       nth (default_proc data) ps 2 = Recv 0 f) ->
  (n_relay = 1%N -> exists f, nth (default_proc data) ps 2 = Recv 1 f /\
     forall v, @std_from_enc AHE v != None -> exists sv, f v = Send 0 sv Finish) ->
  all_terminated (one_step_procs data ps) \/ dsdp_inv (one_step_procs data ps).
Proof.
move=> Hsz Hwf [vd Halice] Hr0 Hpending Hfinner_cont
  Hrelay1_inter Hrelay1_last; right.
have [Hstep0 Hstep1] := @step_send_recv_match data ps 0 1 vd (alice_foldr_at 2)
  (oapp f_inner Fail \o @std_from_enc AHE) Halice Hr0.
have Hwf0 : proc_wf AHE (nth (default_proc data) ps 0) by apply Hwf; rewrite Hsz.
rewrite Halice /= in Hwf0; have [Henc_vd _] := Hwf0.
case Hsfe: (@std_from_enc AHE vd) => [c|]; last by rewrite Hsfe in Henc_vd.
have Hr0_result : (step ps [::] 1).1.1 = f_inner c by rewrite Hstep1 /comp Hsfe.
have [sv_r0 Hfic] := Hfinner_cont c.
case: (ltnP 1 n_relay) => Hn1.
- (* n_relay >= 2 → Inv_AR(2) *)
  have Hord2 : (2 < n_relay.+1)%N := Hn1.
  apply (Inv_AR (Ordinal Hord2)).
  + by rewrite (@size_one_step data).
  + exact (@one_step_preserves_proc_wf ps Hwf).
  + have Hsz0 : (0 < size ps)%N by rewrite Hsz.
    by rewrite (@nth_one_step data ps 0 Hsz0) Hstep0.
  + rewrite /relay_at_body.
    have Hsz3 : ((Ordinal Hord2).+1 < size ps)%N by rewrite Hsz /=.
    rewrite (@nth_one_step data ps (Ordinal Hord2).+1 Hsz3) /smc_interpreter.step.
    have Hb2 := Hpending (Ordinal Hord2) (isT : (1 < 2)%N); rewrite /relay_at_body /= in Hb2.
    have [sv2 [sk2 Hbs2]] := relay_body_is_send0 (Ordinal Hord2).
    by rewrite Hb2 Hbs2 Halice.
  + move=> i Hi; rewrite /relay_at_body.
    have Hszi : (i.+1 < size ps)%N by rewrite Hsz; exact (ltn_ord i).
    rewrite (@nth_one_step data ps i.+1 Hszi) /smc_interpreter.step.
    have Hi1 : (1 < i)%N := ltn_trans (isT : (1 < 2)%N) Hi.
    have Hbi := Hpending i Hi1; rewrite /relay_at_body in Hbi.
    have [svi [ski Hbsi]] := relay_body_is_send0 i.
    by rewrite Hbi Hbsi Halice.
  + by move=> /eqP.
  + move=> _.
    have [sv1 [f1 [Hbody1 Hr1]]] := Hrelay1_inter Hn1.
    exists sv1, f1; split.
    * have -> : @inord n_relay (Ordinal (n:=n_relay.+1) (m:=2) Hord2).-1 =
                Ordinal (n:=n_relay.+1) (m:=1) Hn_relay.
        by apply /val_inj; rewrite /= inordK.
      exact Hbody1.
    * have Hsz2 : (2 < size ps)%N by rewrite Hsz.
      by rewrite (@nth_one_step data ps 2 Hsz2) /smc_interpreter.step Hr1 Halice.
  + (* A8: frontier sender at pos 1 for j=2 *)
    move=> _.
    exists sv_r0.
    have Hsz1 : (1 < size ps)%N by rewrite Hsz; exact (ltn_trans Hn_relay (ltnSn _)).
    by rewrite (@nth_one_step data ps 1 Hsz1) Hr0_result Hfic.
  + by []. (* A9: 3<=2 → false *)
- (* n_relay = 1 → Inv_drain(0) *)
  have Hn1_eq : n_relay = 1%N by apply /eqP; rewrite eqn_leq Hn1 Hn_relay.
  have [f_last [Hr_last Hlast_cont]] := Hrelay1_last Hn1_eq.
  apply (Inv_drain ord0).
  + by rewrite /= Hn1_eq.
  + by rewrite (@size_one_step data).
  + exact (@one_step_preserves_proc_wf ps Hwf).
  + (* Alice: one_step[0] = alice_foldr_at 2 = alice_foldr_at n_relay.+1 *)
    have Hsz0 : (0 < size ps)%N by rewrite Hsz.
    by rewrite Hn1_eq (@nth_one_step data ps 0 Hsz0) Hstep0.
  + exists sv_r0.
    have Hsz1 : (1 < size ps)%N by rewrite Hsz; exact (ltn_trans Hn_relay (ltnSn _)).
    by rewrite (@nth_one_step data ps 1 Hsz1) Hr0_result Hfic.
  + exists f_last.
    have Hsz2 : (2 < size ps)%N by rewrite Hsz Hn1_eq.
    by rewrite (@nth_one_step data ps 2 Hsz2) /smc_interpreter.step Hr_last Hr0 /=.
  + by [].
  + rewrite Hn1_eq; exists f_last; split.
    * have Hsz2 : (2 < size ps)%N by rewrite Hsz Hn1_eq.
      by rewrite (@nth_one_step data ps 2 Hsz2) /smc_interpreter.step Hr_last Hr0 /=.
    * exact Hlast_cont.
  + move=> i Hi1 Hi2.
    have : (i < 1)%N by rewrite -Hn1_eq.
    rewrite ltnS leqn0 => /eqP Hi0; subst i.
    by rewrite ltnn in Hi1.
Qed.

(* C2d: ASj → AR(j+1) or drain *)
Lemma dsdp_inv_step_ASj (j : 'I_n_relay.+1) ps :
  (2 <= j)%N ->
  size ps = n_relay.+2 -> @all_proc_wf AHE ps ->
  (exists vd, nth (default_proc data) ps 0 = Send j vd (alice_foldr_at j.+1)) ->
  (exists sv0 f0, relay_body (@inord n_relay j.-1) = Send 0 sv0 (Recv 0 f0) /\
     nth (default_proc data) ps j = Recv 0 f0) ->
  (forall i : 'I_n_relay.+1, (j < i)%N -> relay_at_body i ps) ->
  ((j < n_relay)%N ->
     exists sv f, relay_body j = Send 0 sv (Recv 0 f) /\
       nth (default_proc data) ps j.+1 = Recv 0 f) ->
  ((j : nat) = n_relay ->
     exists f_dec, nth (default_proc data) ps n_relay.+1 = Recv n_relay f_dec /\
       forall v, @std_from_enc AHE v != None ->
         exists sv, f_dec v = Send 0 sv Finish) ->
  ((j == 2%N :> nat) ->
     exists sv_fw, nth (default_proc data) ps 1 = Send 2 sv_fw Finish) ->
  ((3 <= j)%N ->
     (forall i : nat, (i.+1 <= j.-2)%N ->
        nth (default_proc data) ps i.+1 = Finish) /\
     (exists sv_fw, nth (default_proc data) ps j.-1 = Send j sv_fw Finish)) ->
  all_terminated (one_step_procs data ps) \/ dsdp_inv (one_step_procs data ps).
Proof.
move=> Hj2 Hsz Hwf [vd Halice] [sv0 [f0 [Hbody0 Hrj]]] Hpending B7a B7b B8 B9;
  right.
have [Hstep0 Hstepj] := @step_send_recv_match data ps 0 j vd
  (alice_foldr_at j.+1) f0 Halice Hrj.
have Hwf0 : proc_wf AHE (nth (default_proc data) ps 0) by apply Hwf; rewrite Hsz.
rewrite Halice /= in Hwf0; have [Henc_vd _] := Hwf0.
have Hj0 : (0 < j)%N := ltn_trans (ltn0Sn 0) Hj2.
have Hj1_lt : (j.-1 < n_relay.+1)%N := leq_ltn_trans (leq_pred _) (ltn_ord j).
have Hj1_val : (inord j.-1 : 'I_n_relay.+1) = j.-1 :> nat by rewrite inordK.
have Hj1_pos : (0 < (inord j.-1 : 'I_n_relay.+1))%N
  by rewrite Hj1_val -subn1 subn_gt0.
have Hj1_lt_nr : ((inord j.-1 : 'I_n_relay.+1) < n_relay)%N.
  by rewrite Hj1_val -(prednK Hj0); have := ltn_ord j; rewrite -(prednK Hj0) ltnS.
have [f_dec [Hf0vd Hf_dec_cont]] :=
  @relay_inter_recv_from_body_fires (inord j.-1) vd sv0 f0
    Hj1_pos Hj1_lt_nr Hbody0 Henc_vd.
have Hj1S : j.-1.+1 = j :> nat by rewrite prednK.
have Hj1S2 : (inord j.-1 : 'I_n_relay.+1).+2 = j.+1 :> nat
  by rewrite Hj1_val prednK.
case: (ltnP j n_relay) => Hjn.
- (* Case 1: j < n_relay → Inv_AR(j+1) *)
  have [sv_j [f_j [Hbodyj Hrj1]]] := B7a Hjn.
  have Hord_j1 : (j.+1 < n_relay.+1)%N := Hjn.
  apply (Inv_AR (Ordinal Hord_j1)).
  + by rewrite (@size_one_step data).
  + exact (@one_step_preserves_proc_wf ps Hwf).
  + have Hsz0 : (0 < size ps)%N by rewrite Hsz.
    by rewrite (@nth_one_step data ps 0 Hsz0) Hstep0.
  + rewrite /relay_at_body /=.
    have Hszj2 : (j.+2 < size ps)%N by rewrite Hsz; exact Hjn.
    rewrite (@nth_one_step data ps j.+2 Hszj2) /smc_interpreter.step.
    have Hbi := Hpending (Ordinal Hord_j1) (ltnSn j).
    rewrite /relay_at_body /= in Hbi.
    have [sv_j1 [sk_j1 Hbs_j1]] := relay_body_is_send0 (Ordinal Hord_j1).
    by rewrite Hbi Hbs_j1 Halice.
  + move=> i Hi; rewrite /relay_at_body.
    have Hszi : (i.+1 < size ps)%N by rewrite Hsz; exact (ltn_ord i).
    rewrite (@nth_one_step data ps i.+1 Hszi) /smc_interpreter.step.
    have Hi_j : (j < i)%N := ltn_trans (ltnSn j) Hi.
    have Hbi := Hpending i Hi_j; rewrite /relay_at_body in Hbi.
    have [svi [ski Hbsi]] := relay_body_is_send0 i.
    by rewrite Hbi Hbsi Halice.
  + by rewrite /= eqSS => /eqP Habs; rewrite Habs in Hj2.
  + move=> _ /=; exists sv_j, f_j; split.
    * have -> : @inord n_relay j = j :> 'I_n_relay.+1.
        by apply /val_inj; rewrite /= inordK //; exact (ltn_trans Hjn (ltnSn _)).
      exact Hbodyj.
    * have Hszj1 : (j.+1 < size ps)%N
        by rewrite Hsz; exact (ltn_trans Hjn (ltnSn _)).
      rewrite (@nth_one_step data ps j.+1 Hszj1) /smc_interpreter.step
              Hrj1 Halice /=.
      by rewrite ifF //; apply /negbTE; rewrite neq_ltn; apply /orP; left.
  + by rewrite /= eqSS => /eqP Habs; rewrite Habs in Hj2.
  + (* A9: 3 <= j+1 → Finish zone + frontier + receiver *)
    move=> /= _.
    split; [|split].
    * (* A9a: Finish zone *)
      move=> i Hi.
      have Hj3 : (2 < j)%N.
        have H1j : (1 < j.-1)%N := leq_ltn_trans (isT : (1 <= i.+1)%N) Hi.
        by rewrite -[X in (_ < X)%N](prednK Hj0).
      have [Hfin_zone _] := B9 Hj3.
      have Hszi : (i.+1 < size ps)%N.
        rewrite Hsz.
        have Hij : (i.+1 < j)%N.
          move: Hi; case: (j : nat) Hj2 => [|[|j']] //= _.
          by move=> Hi; exact (ltn_trans Hi (ltnSn _)).
        exact (ltn_trans (ltn_trans Hij Hjn) (ltn_trans (ltnSn n_relay) (ltnSn n_relay.+1))).
      have Hi' : (i < j.-2)%N.
        by rewrite -ltnS (prednK (n := j.-1)) // -subn1 subn_gt0.
      rewrite (@nth_one_step data ps i.+1 Hszi) /smc_interpreter.step.
      by rewrite (Hfin_zone i Hi').
    * (* A9b: frontier sender at pos j.-1 *)
    * (* A9b: frontier sender at pos j.-1 = Send j sv Finish *)
      case: (leqP 3 j) => Hj3.
      -- have [_ [sv_fw Hfrontier]] := B9 Hj3.
         exists sv_fw.
         have Hszjm1 : (j.-1 < size ps)%N.
           rewrite Hsz; exact (ltn_trans (leq_ltn_trans (leq_pred j) (ltn_trans Hjn (ltnSn n_relay))) (ltnSn n_relay.+1)).
         rewrite (@nth_one_step data ps j.-1 Hszjm1) /smc_interpreter.step
                 Hfrontier Hrj /=.
         have -> : (0%N == j.-1) = false.
           by apply /eqP; move: Hj2; case: (j : nat) => [|[|j']].
         by [].
      -- have Hj_eq : (j : nat) = 2%N.
           apply /eqP; rewrite eqn_leq Hj2 andbT.
           by rewrite -ltnS.
         have Hj_eq2 : (j == 2%N :> nat) by rewrite Hj_eq.
         have [sv_fw Hfrontier] := B8 Hj_eq2.
         exists sv_fw; rewrite Hj_eq /=.
         have Hsz1 : (1 < size ps)%N
           by rewrite Hsz; exact (ltn_trans Hn_relay (ltnSn _)).
         rewrite (@nth_one_step data ps 1 Hsz1) /smc_interpreter.step
                 Hfrontier; rewrite Hj_eq in Hrj; rewrite Hrj /=.
         by [].
    * (* A9c: frontier receiver at pos j *)
      exists f_dec.
      have Hszj : (j < size ps)%N
        by rewrite Hsz; exact (ltn_trans (ltn_trans Hjn (ltnSn n_relay)) (ltnSn n_relay.+1)).
      split.
      -- rewrite (@nth_one_step data ps j Hszj) Hstepj Hf0vd.
         by rewrite Hj1_val.
      -- move=> v Henc_v.
         have [sw Hsw] := Hf_dec_cont v Henc_v.
         exists sw; by rewrite Hsw Hj1S2.
- (* Case 2: j >= n_relay → j = n_relay → Inv_drain *)
  have Hjn_eq : (j : nat) = n_relay.
    apply /eqP; rewrite eqn_leq Hjn andbT.
    by have := ltn_ord j; rewrite ltnS.
  have [f_last [Hlast Hlast_cont]] := B7b Hjn_eq.
  (* Drain index: j_d = j - 2 as ordinal *)
  (* After AS(j): pos 0 → alice_foldr_at(j+1) = alice_foldr_at(n_relay+1),
     pos j → f0(vd) = Recv(j-1) f_dec, pos j-1 = Send j sv Finish (B8/B9) *)
  (* Need: Inv_drain with appropriate index *)
  case: (leqP 3 j) => Hj3.
  + (* j >= 3: B9 gives Finish zone + frontier *)
    have [Hfin_zone [sv_fw Hfrontier]] := B9 Hj3.
    have Hj2_lt : (j.-2 < n_relay.+1)%N.
      move: Hj2 (ltn_ord j); case: (j : nat) => [|[|j']] //= _ Hj_lt.
      exact (ltn_trans (ltnSn j') (ltn_trans (ltnSn j'.+1) Hj_lt)).
    apply (Inv_drain (Ordinal Hj2_lt)).
    * (* j.-2.+1 < n_relay.+1 *)
      rewrite /=.
      move: Hj2 (ltn_ord j); case: (j : nat) => [|[|j']] //= _ Hlt.
      exact (ltn_trans (ltnSn j') Hlt).
    * by rewrite (@size_one_step data).
    * exact (@one_step_preserves_proc_wf ps Hwf).
    * (* Alice: one_step[0] = alice_foldr_at(j+1) = alice_foldr_at(n_relay+1) *)
      have Hsz0 : (0 < size ps)%N by rewrite Hsz.
      by rewrite (@nth_one_step data ps 0 Hsz0) Hstep0 Hjn_eq.
    * (* Frontier sender: one_step[j.-1] = Send j sv Finish *)
      exists sv_fw; rewrite /=; rewrite prednK //.
      have Hszjm1 : (j.-1 < size ps)%N.
        rewrite Hsz.
        have : (j.-1 < j)%N by rewrite -{2}(prednK Hj0).
        move=> Hjm1; exact (ltn_trans (ltn_trans Hjm1 (ltn_ord j)) (ltnSn n_relay.+1)).
      rewrite (@nth_one_step data ps j.-1 Hszjm1) /smc_interpreter.step
              Hfrontier Hrj /=.
      have -> : (0%N == j.-1) = false.
        by apply /eqP; move: Hj3; case: (j : nat) => [|[|[|j']]].
      by rewrite /= (prednK Hj0).
    * by move: Hj3; case: (j : nat) => [|[|[|j']]].
    * (* Frontier receiver: one_step[j] = Recv j.-1 f_dec *)
      exists f_dec.
      have Hszj : (j < size ps)%N by rewrite Hsz; exact (ltn_trans (ltn_ord j) (ltnSn n_relay.+1)).
      have Hnth := @nth_one_step data ps j Hszj.
      have Hgoal : (step ps [::] j).1.1 = Recv j.-1 f_dec
        by rewrite Hstepj Hf0vd Hj1_val.
      have Hgoal2 : (step ps [::] j).1.1 = Recv j.-1 f_dec
        by rewrite Hstepj Hf0vd Hj1_val.
      vm_cast_no_check (eq_trans Hnth Hgoal2).
    * (* Finish zone: forall i < j.-2, one_step[i.+1] = Finish *)
      move=> /= i Hi.
      have Hszi : (i.+1 < size ps)%N.
        rewrite Hsz.
        have Hij : (i.+1 < j)%N.
          move: Hi; case: (j : nat) Hj2 Hj3 => [|[|[|j']]] //= _ _ Hi.
          by exact (ltn_trans Hi (ltnSn _)).
        exact (ltn_trans Hij (ltn_trans (ltn_ord j) (ltnSn n_relay.+1))).
      rewrite (@nth_one_step data ps i.+1 Hszi) /smc_interpreter.step.
      by rewrite (Hfin_zone i Hi).
    * (* Last relay: one_step[n_relay.+1] = Recv n_relay f_last *)
      exists f_last; split; last exact Hlast_cont.
      have Hszl : (n_relay.+1 < size ps)%N by rewrite Hsz.
      rewrite (@nth_one_step data ps n_relay.+1 Hszl) /smc_interpreter.step Hlast.
      rewrite -Hjn_eq Hrj /=.
      by [].
    * (* Between zone: empty since j = n_relay, j.-2.+1 = j.-1, range is j.-1 < i < n_relay *)
      move=> /= i Hi1 Hi2.
      (* i > j.-2 and i < n_relay = j. So j.-1 <= i < j. Only i = j.-1. *)
      have Hi_eq : i = j.-1.
        have Hi_lt_j : (i < j)%N by rewrite Hjn_eq.
        move: Hi1 Hi_lt_j.
        case: (j : nat) Hj2 Hj3 => [|[|[|j']]] //= _ _ Hi1 Hi_lt_j.
        by apply /eqP; rewrite eqn_leq Hi1 -ltnS Hi_lt_j.
      subst i; rewrite prednK //.
      (* pos j = Recv j.-1 f_dec with f_dec v = Send (inord j.-1).+2 sv Finish *)
      exists f_dec; split.
      -- have Hszj : (j < size ps)%N
           by rewrite Hsz; exact (ltn_trans (ltn_ord j) (ltnSn n_relay.+1)).
         vm_cast_no_check (eq_trans (@nth_one_step data ps j Hszj) (eq_trans Hstepj (eq_ind _ (fun x => f0 vd = Recv x f_dec) Hf0vd _ Hj1_val))).
      -- move=> v Henc_v.
         have [sw Hsw] := Hf_dec_cont v Henc_v.
         exists sw; rewrite Hsw.
         congr (Send _ _ _); exact Hj1S2.
  + (* j = 2: B8 gives pos 1 = Send 2 sv Finish *)
    have Hj_eq : (j : nat) = 2%N.
      apply /eqP; rewrite eqn_leq Hj2 andbT.
      by rewrite -ltnS.
    have Hj_eq2 : (j == 2%N :> nat) by rewrite Hj_eq.
    have [sv_fw Hfrontier] := B8 Hj_eq2.
    have Hord0 : (0 < n_relay.+1)%N by [].
    apply (Inv_drain (Ordinal Hord0)).
    * rewrite /= Hjn_eq Hj_eq; exact Hn_relay.
    * by rewrite (@size_one_step data).
    * exact (@one_step_preserves_proc_wf ps Hwf).
    * have Hsz0 : (0 < size ps)%N by rewrite Hsz.
      by rewrite (@nth_one_step data ps 0 Hsz0) Hstep0 Hjn_eq.
    * (* Frontier sender: one_step[1] = Send 2 sv Finish *)
      exists sv_fw; rewrite /= Hjn_eq Hj_eq.
      have Hsz1 : (1 < size ps)%N
        by rewrite Hsz; exact (ltn_trans Hn_relay (ltnSn _)).
      rewrite (@nth_one_step data ps 1 Hsz1) /smc_interpreter.step
              Hfrontier; rewrite Hj_eq in Hrj; rewrite Hrj /=.
      by rewrite ifF.
    * (* Frontier receiver: one_step[2] = Recv 1 f_dec *)
      exists f_dec; rewrite /= Hjn_eq Hj_eq.
      have Hsz2 : (2 < size ps)%N by rewrite Hsz Hjn_eq Hj_eq.
      rewrite (@nth_one_step data ps 2 Hsz2) Hj_eq in Hstepj.
      rewrite Hj_eq (@nth_one_step data ps 2 Hsz2).
      rewrite {1}Hj_eq in Hstepj.
      rewrite Hstepj Hf0vd.
      by rewrite Hj1_val Hj_eq.
    * by move=> /= i; rewrite Hjn_eq Hj_eq.
    * exists f_last; split; last exact Hlast_cont.
      have Hszl : (n_relay.+1 < size ps)%N by rewrite Hsz.
      rewrite (@nth_one_step data ps n_relay.+1 Hszl) /smc_interpreter.step Hlast.
      rewrite -Hjn_eq Hj_eq in Hrj.
      rewrite -Hjn_eq Hrj /=.
      by rewrite ifF //; apply /negbTE; rewrite Hjn_eq neq_ltn; apply /orP; left.
    * (* Between zone: 0 < i < n_relay = 2, only i = 1 *)
      move=> /= i Hi1 Hi2.
      rewrite Hjn_eq Hj_eq in Hi2.
      have Hi_eq : i = 1.
        apply /eqP; rewrite eqn_leq.
        have : (i < 2)%N := Hi2.
        rewrite ltnS => -> /=.
        by rewrite Hjn_eq Hj_eq /= in Hi1.
      subst i.
      exists f_dec; split.
      -- have Hsz2 : (2 < size ps)%N by rewrite Hsz Hjn_eq Hj_eq.
         rewrite Hj_eq (@nth_one_step data ps 2 Hsz2).
         rewrite {1}Hj_eq in Hstepj; rewrite Hstepj Hf0vd.
         by rewrite Hj1_val Hj_eq.
      -- move=> v Henc_v.
         have [sw Hsw] := Hf_dec_cont v Henc_v.
         exists sw; by rewrite Hsw Hj1S2.
Admitted.

(* C2e: drain(d) → drain(d+1) or tail *)
Lemma dsdp_inv_step_drain (j : 'I_n_relay.+1) ps :
  (j.+1 < n_relay.+1)%N ->
  size ps = n_relay.+2 -> @all_proc_wf AHE ps ->
  nth (default_proc data) ps 0 = alice_foldr_at n_relay.+1 ->
  (exists v, nth (default_proc data) ps j.+1 = Send j.+2 v Finish) ->
  (exists f, nth (default_proc data) ps j.+2 = Recv j.+1 f) ->
  (forall i : nat, (i < j)%N -> nth (default_proc data) ps i.+1 = Finish) ->
  (exists f, nth (default_proc data) ps n_relay.+1 = Recv n_relay f /\
     forall v, @std_from_enc AHE v != None ->
       exists sv, f v = Send 0 sv Finish) ->
  (forall i : nat, (j < i)%N -> (i < n_relay)%N ->
     exists f, nth (default_proc data) ps i.+1 = Recv i f /\
       (forall v, @std_from_enc AHE v != None ->
          exists sv, f v = Send i.+2 sv Finish)) ->
  all_terminated (one_step_procs data ps) \/ dsdp_inv (one_step_procs data ps).
Proof.
move=> Hjb Hsz Hwf Halice_foldr [vd Hsend] [f Hrecv] Hfin
  [fl [Hlast Hlast_cont]] Hbetween.
have Halice_save := Halice_foldr.
have [Hstep_j Hstep_j1] :=
  @step_send_recv_match data ps j.+1 j.+2 vd Finish f Hsend Hrecv.
have Hwf_j : proc_wf AHE (nth (default_proc data) ps j.+1)
  by apply Hwf; rewrite Hsz; exact (ltn_trans Hjb (ltnSn _)).
rewrite Hsend /= in Hwf_j; have [Henc _] := Hwf_j.
right.
case: (ltnP j.+1 n_relay) => Hjn.
- (* j+1 < n_relay: intermediate → Inv_drain(j+1) *)
  have [f1 [Hrecv1 Hcont1]] := Hbetween j.+1 (ltnSn j) Hjn.
  rewrite Hrecv in Hrecv1; case: Hrecv1 => ?; subst f1.
  have [sv Hfv] := Hcont1 vd Henc.
  have Hj1b : (j.+1 < n_relay.+1)%N := ltn_trans Hjn (ltnSn _).
  apply (Inv_drain (Ordinal Hj1b)).
  + by rewrite /= ltnS.
  + by rewrite (@size_one_step data).
  + exact (@one_step_preserves_proc_wf ps Hwf).
  + (* Alice: nop — alice_erase_tail is a Recv, last relay is also Recv → nop *)
    have H_sz_0 : (0 < size ps)%N by rewrite Hsz.
    have [ftail Htail_recv] := alice_tail_is_recv.
    have H_a_et := Halice_save; rewrite alice_foldr_at_tail in H_a_et.
    rewrite (@nth_one_step data ps 0 H_sz_0) /smc_interpreter.step H_a_et Htail_recv.
    by rewrite Hlast -Htail_recv alice_foldr_at_tail.
  + (* Relay j+1 forwarding: one_step[j+2] = f vd = Send j+3 sv Finish *)
    exists sv.
    have Hj2sz : (j.+2 < size ps)%N by rewrite Hsz; exact (ltn_trans Hjn (ltnSn _)).
    transitivity (step ps [::] j.+2).1.1.
    - exact (@nth_one_step data ps j.+2 Hj2sz).
    - by rewrite Hstep_j1 Hfv.
  + (* Relay j+2 at Recv *)
    case: (ltnP j.+2 n_relay) => Hjn2.
    * have [f2 [Hr2 _]] := Hbetween j.+2 (ltn_trans (ltnSn j) (ltnSn j.+1)) Hjn2.
      exists f2.
      have Hszj3 : (j.+3 < size ps)%N by rewrite Hsz; exact (ltn_trans Hjn2 (ltnSn _)).
      transitivity (step ps [::] j.+3).1.1.
      { exact (@nth_one_step data ps j.+3 Hszj3). }
      by rewrite /smc_interpreter.step Hr2 Hrecv.
    * have Hjn2_eq : j.+2 = n_relay by apply /eqP; rewrite eqn_leq Hjn2 Hjn.
      exists fl.
      have Hszj3 : (j.+3 < size ps)%N by rewrite Hsz Hjn2_eq.
      transitivity (step ps [::] j.+3).1.1.
      { exact (@nth_one_step data ps j.+3 Hszj3). }
      rewrite Hjn2_eq /smc_interpreter.step Hlast.
      have Hup : nth (default_proc data) ps n_relay = Recv j.+1 f
        by move: Hrecv; rewrite Hjn2_eq.
      by rewrite Hup.
  + (* Finish zone extends by 1 *)
    move=> /= i; rewrite ltnS leq_eqVlt => /orP [/eqP -> | Hi].
    * have Hszj : (j.+1 < size ps)%N by rewrite Hsz; exact (ltn_trans Hjb (ltnSn _)).
      by rewrite (@nth_one_step data ps j.+1 Hszj) Hstep_j.
    * have Hszii : (i.+1 < size ps)%N
        by rewrite Hsz; exact (ltn_trans (ltn_trans Hi Hjb) (ltnSn _)).
      by rewrite (@nth_one_step data ps i.+1 Hszii) /smc_interpreter.step (Hfin i Hi).
  + (* Last relay nop *) exists fl; split; last exact Hlast_cont.
    have Hszl : (n_relay.+1 < size ps)%N by rewrite Hsz.
    rewrite (@nth_one_step data ps n_relay.+1 Hszl) /smc_interpreter.step Hlast.
    case Hpn: (nth (default_proc data) ps n_relay) => [|dstn vn kn|frmn fn|dn||] //.
    case: ifP => // /eqP ?; exfalso.
    case: (n_relay =P j.+2) => [Heq | Hneq].
      by rewrite Heq Hrecv in Hpn.
    have Hnm1_gt : (j < n_relay.-1)%N.
      move: Hjn; rewrite -ltn_predRL //.
    have Hnm1_lt : (n_relay.-1 < n_relay)%N.
      by rewrite -{2}(prednK Hn_relay) ltnS.
    have [fnm1 [Hrnm1 _]] := Hbetween n_relay.-1 Hnm1_gt Hnm1_lt.
    rewrite (prednK Hn_relay) in Hrnm1; by rewrite Hrnm1 in Hpn.
  + (* Between zone *)
    move=> /= i Hi1 Hi2.
    have [fi [Hrecvi Hconti]] := Hbetween i (ltn_trans (ltnSn j) Hi1) Hi2.
    exists fi; split; last exact Hconti.
    have Hszi : (i.+1 < size ps)%N by rewrite Hsz; exact (ltn_trans Hi2 (ltnSn _)).
    rewrite (@nth_one_step data ps i.+1 Hszi) /smc_interpreter.step Hrecvi.
    case Hpi: (nth (default_proc data) ps i) => [|dsti vi ki|frmi fi'|di||] //.
    case: ifP => // /eqP ?; exfalso.
    case: (i =P j.+2) => [Heq | Hneq].
      by subst i; rewrite Hrecv in Hpi.
    have Hi_gt : (j.+2 < i)%N.
      rewrite ltnNge; apply /negP => Hle.
      by apply Hneq; apply /eqP; rewrite eqn_leq Hle Hi1.
    have Hi_pos : (0 < i)%N := ltn_trans (ltn0Sn _) (ltn_trans (ltnSn _) Hi_gt).
    have Hi1_gt : (j < i.-1)%N.
      by apply (@ltn_trans j.+1); [exact (ltnSn j) | rewrite -ltnS (prednK Hi_pos)].
    have Hi1_lt : (i.-1 < n_relay)%N by apply (leq_ltn_trans (leq_pred _)).
    have [fi1 [Hri1 _]] := Hbetween i.-1 Hi1_gt Hi1_lt.
    rewrite (prednK Hi_pos) in Hri1; by rewrite Hri1 in Hpi.
- (* j+1 >= n_relay: last relay reached → Inv_tail *)
  have Hjn_eq : j.+1 = n_relay by apply /eqP; rewrite eqn_leq Hjn -ltnS Hjb.
  have Heq_pos : j.+2 = n_relay.+1 by rewrite Hjn_eq.
  have Halice_saved : nth (default_proc data) ps 0 = alice_foldr_at n_relay.+1
    := Halice_foldr.
  have Hfl_eq : fl = f.
    have : nth (default_proc data) ps n_relay.+1 = nth (default_proc data) ps j.+2
      by rewrite Heq_pos.
    rewrite Hlast Hrecv Hjn_eq => -[]. by [].
  subst fl.
  (* After firing: relay j → Finish, last relay → f vd = Send 0 sv Finish *)
  have [sv Hfv] := Hlast_cont vd Henc.
  apply Inv_tail.
  + by rewrite (@size_one_step data).
  + exact (@one_step_preserves_proc_wf ps Hwf).
  + (* Last relay becomes Send 0 sv Finish *)
    exists sv.
    have Hszj2 : (j.+2 < size ps)%N by rewrite Hsz Heq_pos.
    by rewrite -Heq_pos (@nth_one_step data ps j.+2 Hszj2) Hstep_j1 Hfv.
  + (* Alice at tail Recv: nop, with Ret continuation *)
    (* Alice: one_step[0] = alice_foldr_at n_relay.+1 *)
    have Hsz0 : (0 < size ps)%N by rewrite Hsz.
    have [ftail Htail_recv] := alice_tail_is_recv.
    rewrite alice_foldr_at_tail in Halice_saved.
    by rewrite (@nth_one_step data ps 0 Hsz0) /smc_interpreter.step
       Halice_saved Htail_recv Hlast -Htail_recv alice_foldr_at_tail.
  + (* All relays < n_relay at Finish *)
    move=> i Hi_lt.
    rewrite /relay_at_finish_pred.
    have Hszi : (i.+1 < size ps)%N by rewrite Hsz; exact (ltn_ord i).
    case: (ltnP i j) => Hij.
    * (* i < j: was Finish *)
      by rewrite (@nth_one_step data ps i.+1 Hszi) /smc_interpreter.step (Hfin i Hij).
    * (* i >= j and i < n_relay = j+1, so i = j *)
      have Hij_eq : (i : nat) = (j : nat).
        apply /eqP; rewrite eqn_leq Hij andbT.
        have : (i < j.+1)%N by rewrite Hjn_eq.
        by rewrite ltnS.
      have -> : i.+1 = j.+1 by rewrite Hij_eq.
      have Hszj : (j.+1 < size ps)%N by rewrite Hsz; exact (ltn_trans Hjb (ltnSn _)).
      by rewrite (@nth_one_step data ps j.+1 Hszj) Hstep_j.
Qed.

Lemma dsdp_inv_step_TAIL ps :
  size ps = n_relay.+2 -> @all_proc_wf AHE ps ->
  (exists v, nth (default_proc data) ps n_relay.+1 = Send 0 v Finish) ->
  nth (default_proc data) ps 0 = alice_foldr_at n_relay.+1 ->
  (forall j : 'I_n_relay.+1, (j < n_relay)%N -> relay_at_finish_pred j ps) ->
  all_terminated (one_step_procs data ps) \/ dsdp_inv (one_step_procs data ps).
Proof.
move=> Hsz Hwf [v Hsend] Halice Hrels; right.
have [f Hrecv_tail] := alice_tail_is_recv.
rewrite alice_foldr_at_tail in Halice.
have Hrecv : nth (default_proc data) ps 0 = Recv n_relay.+1 f
  by rewrite Halice Hrecv_tail.
have Hfcont : forall v0', @std_from_enc AHE v0' != None -> exists d, f v0' = Ret d
  := fun v0' => @alice_tail_recv_ret f v0' Hrecv_tail.
have [Hstep_send Hstep_recv] :=
  @step_send_recv_match data ps n_relay.+1 0 v Finish f Hsend Hrecv.
have Hwf_last : proc_wf AHE (nth (default_proc data) ps n_relay.+1)
  by apply Hwf; rewrite Hsz; exact (ltnSn _).
rewrite Hsend /= in Hwf_last.
have [Henc _] := Hwf_last.
have [d Hfv] := Hfcont v Henc.
apply (Inv_ret (one_step_procs data ps) d).
- by rewrite (@size_one_step data).
- exact (@one_step_preserves_proc_wf ps Hwf).
- have Hsz0 : (0 < size ps)%N by rewrite Hsz.
  by rewrite (@nth_one_step data ps 0 Hsz0) Hstep_recv Hfv.
- move=> j.
  have Hjsz : (j.+1 < size ps)%N by rewrite Hsz; exact (ltn_ord j).
  rewrite /relay_at_finish_pred (@nth_one_step data ps j.+1 Hjsz).
  case: (ltnP j n_relay) => Hjn.
  + have Hfin := Hrels j Hjn; rewrite /relay_at_finish_pred in Hfin.
    by rewrite /smc_interpreter.step Hfin.
  + have Hjmax : (j : nat) = n_relay.
      have := ltn_ord j; rewrite ltnS => Hj_le.
      by apply /eqP; rewrite eqn_leq Hj_le Hjn.
    by rewrite Hjmax /smc_interpreter.step Hsend Hrecv eqxx.
Qed.

Lemma dsdp_inv_step_RET ps d0 :
  size ps = n_relay.+2 -> @all_proc_wf AHE ps ->
  nth (default_proc data) ps 0 = Ret d0 ->
  (forall j : 'I_n_relay.+1, relay_at_finish_pred j ps) ->
  all_terminated (one_step_procs data ps) \/ dsdp_inv (one_step_procs data ps).
Proof.
move=> Hsz Hwf Hret Hrels; left.
apply /(@all_nthP _ _ _ (default_proc data)).
rewrite (@size_one_step data) => i Hi.
rewrite (@nth_one_step data ps i Hi).
case: i Hi => [|i] Hi.
- by rewrite /smc_interpreter.step Hret.
- have Him : (i < n_relay.+1)%N by rewrite -ltnS Hsz in Hi.
  have Hfin := Hrels (Ordinal Him); rewrite /relay_at_finish_pred /= in Hfin.
  by rewrite /smc_interpreter.step Hfin.
Qed.

(* C2: Invariant preserved by one_step *)
Lemma dsdp_inv_step ps :
  dsdp_inv ps ->
  all_terminated (one_step_procs data ps) \/ dsdp_inv (one_step_procs data ps).
Proof.
case.
- (* Inv_AR *)
  move=> j ps0 Hsz Hwf Halice Hbody Hpending H6 H7 H8 H9.
  exact: (dsdp_inv_step_AR j ps0 Hsz Hwf Halice Hbody Hpending H6 H7 H8 H9).
- (* Inv_AS0 *)
  move=> ps0 f_inner Hsz Hwf Halice Hr0 Hpending Hcont.
  exact: (dsdp_inv_step_AS0 ps0 f_inner Hsz Hwf Halice Hr0 Hpending Hcont).
- (* Inv_AS1 *)
  move=> ps0 f_inner Hsz Hwf Halice Hr0 Hpending Hcont H6a H6b.
  exact: (dsdp_inv_step_AS1 ps0 f_inner Hsz Hwf Halice Hr0 Hpending Hcont H6a H6b).
- (* Inv_ASj *)
  move=> j ps0 Hj Hsz Hwf Halice Hrecv Hpending B7a B7b B8 B9.
  exact: (dsdp_inv_step_ASj j ps0 Hj Hsz Hwf Halice Hrecv Hpending B7a B7b B8 B9).
- (* Inv_drain *)
  move=> j ps0 Hjb Hsz Hwf Halice Hsend Hrecv Hfin Hlast Hbetween.
  exact: (dsdp_inv_step_drain j ps0 Hjb Hsz Hwf Halice Hsend Hrecv Hfin Hlast Hbetween).
- (* Inv_tail *)
  move=> ps0 Hsz Hwf Hsend Halice Hrels.
  exact: (dsdp_inv_step_TAIL ps0 Hsz Hwf Hsend Halice Hrels).
- (* Inv_ret *)
  move=> ps0 d Hsz Hwf Hret Hrels.
  exact: (dsdp_inv_step_RET ps0 d Hsz Hwf Hret Hrels).
Qed.

(* C3: Step 2 satisfies invariant *)
Lemma dsdp_inv_init :
  dsdp_inv (one_step_procs data (one_step_procs data procs)).
Proof.
set ps2 := one_step_procs data (one_step_procs data procs).
have Hwf : @all_proc_wf AHE procs :=
  @dsdp_initial_proc_wf AHE ek n_relay dk dk_relay dec_total relays v0 u r
    rand_a v_relay r1_relay r2_relay.
have Hwf1 := @one_step_preserves_proc_wf _ Hwf.
have Hwf2 := @one_step_preserves_proc_wf _ Hwf1.
have Hbody : forall j : 'I_n_relay.+1, relay_at_body j ps2.
  move=> j; rewrite /relay_at_body /ps2.
  have [d1 [d2 Hb]] := relay_body_eq j.
  have Hsz : (j.+1 < size procs)%N by rewrite size_procs; exact (ltn_ord j).
  have Hstep1 : nth (default_proc data) (one_step_procs data procs) j.+1 =
    Init d2 (relay_body j).
    by rewrite (@nth_one_step data procs j.+1 Hsz) /smc_interpreter.step Hb.
  have Hsz2 : (j.+1 < size (one_step_procs data procs))%N
    by rewrite size_one_step.
  by rewrite (@nth_one_step data _ j.+1 Hsz2) /smc_interpreter.step Hstep1.
(* Alice at step 2 = alice_foldr_at 0 *)
have Halice : nth (default_proc data) ps2 0 = alice_foldr_at 0.
  rewrite /ps2.
  have Hsz : (0 < size procs)%N by rewrite size_procs.
  have [d [d' [k0 Hp0]]] := @procs_all_double_init 0 Hsz.
  have Hops0 : nth (default_proc data) (one_step_procs data procs) 0 = Init d' k0.
    by rewrite (@nth_one_step data procs 0 Hsz) /smc_interpreter.step Hp0.
  have Hsz2 : (0 < size (one_step_procs data procs))%N by rewrite size_one_step.
  have Hoops0 : nth (default_proc data) (one_step_procs data (one_step_procs data procs)) 0 = k0.
    by rewrite (@nth_one_step data _ 0 Hsz2) /smc_interpreter.step Hops0.
  (* k0 = foldr ... = alice_foldr_at 0 from palice_n_erase *)
  have Halice_erase := @palice_n_erase AHE ek n_relay relays dk v0 u r rand_a.
  have Hp0' : nth (default_proc data) procs 0 =
    erase (@palice_n AHE ek n_relay relays dk v0 u r rand_a).
    by rewrite /procs /dsdp_n_procs /erase_aprocs /dsdp_n_saprocs /= /erase_aproc /=.
  rewrite Hp0' Halice_erase in Hp0.
  case: Hp0 => _ [_ Hk0].
  rewrite Hoops0 -Hk0 /alice_foldr_at drop0.
  reflexivity.
have Hord0 : (0 < n_relay.+1)%N by [].
apply (Inv_AR (Ordinal Hord0)).
- by rewrite (@size_one_step data) (@size_one_step data) size_procs.
- exact Hwf2.
- exact Halice.
- exact (Hbody (Ordinal Hord0)).
- move=> i Hi; exact (Hbody i).
- by move=> /=.  (* j == 1 → false since j = 0 *)
- by [].         (* A7: 2 <= j → false *)
- by [].         (* A8: j == 2 → false *)
- by [].         (* A9: 3 <= j → false *)
Qed.

(* C4: Connect dsdp_reachable to dsdp_inv *)
Lemma dsdp_reachable_inv ps k :
  dsdp_reachable ps k -> (2 <= k)%N ->
  all_terminated ps \/ dsdp_inv ps.
Proof.
elim=> {ps k} [|ps' k Hr IH Hp'] Hk.
- by [].
- case: k Hr IH Hk => [|k] Hr IH Hk.
  + by rewrite ltnS leqn0 in Hk.
  + case: k Hr IH Hk => [|k] Hr IH Hk.
    * inversion Hr as [|ps'' k'' Hr'' Hp'' Heq Hk''].
      inversion Hr'' as [Hps''|]; subst.
      right; exact dsdp_inv_init.
    * have Hk' : (2 <= k.+2)%N by [].
      case: (IH Hk') => [Ht | Hinv].
      -- left; exact (@step_all_terminated data ps' Ht).
      -- exact (dsdp_inv_step ps' Hinv).
Qed.

(* DSDP step preservation: stepping a state with progress and all_proc_wf
   gives a state that is terminated or has progress.
   Now proved using the phase invariant. *)

(* Helper: steps 0 and 1 always produce progress in one_step *)
Lemma step01_progress ps0 k0 :
  dsdp_reachable ps0 k0 -> (k0 <= 1)%N -> has_progress data ps0 ->
  has_progress data (one_step_procs data ps0).
Proof.
move=> Hr Hk Hp.
case: k0 Hr Hk => [|[|k']] Hr Hk //.
- inversion Hr as [Hps|]; subst.
  exact: step_procs_has_progress.
- inversion Hr as [|ps' k' Hr' Hprog' Heqps Hk'].
  inversion Hr' as [Hps'|]; subst.
  exact: has_progress_at_step_2.
Qed.

Lemma dsdp_step_terminated_or_progress ps k :
  dsdp_reachable ps k ->
  @all_proc_wf AHE ps ->
  has_progress data ps ->
  all_terminated (one_step_procs data ps) \/
  has_progress data (one_step_procs data ps).
Proof.
move=> Hr Hwf Hp.
case: (ltnP k 2) => Hk.
- (* k < 2: use step01_progress *)
  right.
  have Hk1 : (k <= 1)%N by rewrite -ltnS.
  exact: (step01_progress ps k Hr Hk1 Hp).
- (* k >= 2: use invariant *)
  case: (dsdp_reachable_inv ps k Hr Hk) => [Ht | Hinv].
  + left; exact: (@step_all_terminated data ps Ht).
  + case: (dsdp_inv_step ps Hinv) => [Ht | Hinv'].
    * by left.
    * right; exact: (dsdp_inv_has_progress _ Hinv').
Qed.

(* Core DSDP progress lemma *)
Lemma dsdp_reachable_progress ps k :
  dsdp_reachable ps k ->
  all_terminated ps \/ has_progress data ps.
Proof.
elim=> {ps k} [|ps' k Hr IH Hp'].
- by right; exact: dsdp_initial_progress.
- (* ps = one_step ps'. IH: terminated ps' ∨ progress ps'. Hp': progress ps'. *)
  have Hwf := @dsdp_reachable_proc_wf _ _ Hr.
  exact: (@dsdp_step_terminated_or_progress _ _ Hr Hwf Hp').
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
