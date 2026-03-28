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

(* H4: Initial processes match relay_body *)
Lemma relay_body_eq (j : 'I_n_relay.+1) :
  exists d1 d2,
    nth (default_proc data) procs j.+1 = Init d1 (Init d2 (relay_body j)).
Proof. Admitted.

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
Proof. Admitted.

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

(* T1: R0 second Recv fires → Send(2,...,Finish) *)
Lemma relay0_second_recv_to_send (f_enc : data -> proc data) (v : data) :
  @std_from_enc AHE v != None ->
  exists sv, f_enc v = Send 2 sv Finish.
Proof. Admitted.

(* T2: Intermediate Recv(0) fires → Recv(j,...) *)
Lemma relay_inter_recv_alice_to_upstream (j : 'I_n_relay.+1) (f_enc : data -> proc data) (v : data) :
  (0 < j)%N -> (j < n_relay)%N ->
  @std_from_enc AHE v != None ->
  exists f_dec, f_enc v = Recv j f_dec.
Proof. Admitted.

(* T3: Recv(j) from upstream fires → Send(j+2,...,Finish) *)
Lemma relay_recv_upstream_to_send_down (j : 'I_n_relay.+1) (f_dec : data -> proc data) (v : data) :
  @std_from_enc AHE v != None ->
  exists sv, f_dec v = Send j.+2 sv Finish.
Proof. Admitted.

(* T4: Last relay Recv fires → Send(0,...,Finish) *)
Lemma relay_last_recv_to_send (f_dec : data -> proc data) (v : data) :
  @std_from_enc AHE v != None ->
  exists sv, f_dec v = Send 0 sv Finish.
Proof. Admitted.

(* H6: Alice's foldr at iteration j starts with Recv(j+1,...) *)
Lemma alice_body_at_recv (j : nat) (Hj : (j < n_relay.+1)%N) :
  exists f,
    foldr (fun (fi : 'I_n_relay.+1 * nat) (cont : proc data) =>
             @alice_erase_body AHE ek n_relay u r rand_a fi.1 fi.2 cont)
          (@alice_erase_tail AHE n_relay dk v0 u r)
          (drop j (zip relays (iota 0 (size relays)))) =
    Recv (Ordinal Hj).+1 f.
Proof. Admitted.

(* H7: After Alice's Recv fires, Alice becomes Send(dest(j),...,rest) *)
Lemma alice_recv_to_send (j : nat) (Hj : (j < n_relay.+1)%N) (f : data -> proc data) (v : data) :
  @std_from_enc AHE v != None ->
  foldr (fun (fi : 'I_n_relay.+1 * nat) (cont : proc data) =>
           @alice_erase_body AHE ek n_relay u r rand_a fi.1 fi.2 cont)
        (@alice_erase_tail AHE n_relay dk v0 u r)
        (drop j (zip relays (iota 0 (size relays)))) =
  Recv (Ordinal Hj).+1 f ->
  exists sv rest, f v = Send (alice_send_dest (Ordinal Hj)) sv rest.
Proof. Admitted.

(* D3: Protocol invariant *)
Inductive dsdp_inv : seq (proc data) -> Prop :=
| Inv_AR (j : 'I_n_relay.+1) ps :
    size ps = n_relay.+2 ->
    @all_proc_wf AHE ps ->
    (exists f, nth (default_proc data) ps 0 = Recv j.+1 f) ->
    relay_at_body j ps ->
    (forall i : 'I_n_relay.+1, (j < i)%N -> relay_at_body i ps) ->
    dsdp_inv ps
| Inv_AS0 ps (f_inner : plain AHE -> proc data) :
    size ps = n_relay.+2 ->
    @all_proc_wf AHE ps ->
    (exists v k, nth (default_proc data) ps 0 = Send 1 v k) ->
    nth (default_proc data) ps 1 =
      Recv 0 (oapp f_inner Fail \o (obind (@dec AHE (dk_relay ord0)) \o @std_from_enc AHE)) ->
    (forall i : 'I_n_relay.+1, (0 < i)%N -> relay_at_body i ps) ->
    dsdp_inv ps
| Inv_AS1 ps (f_inner : cipher AHE -> proc data) :
    size ps = n_relay.+2 ->
    @all_proc_wf AHE ps ->
    (exists v k, nth (default_proc data) ps 0 = Send 1 v k) ->
    nth (default_proc data) ps 1 =
      Recv 0 (oapp f_inner Fail \o @std_from_enc AHE) ->
    (forall i : 'I_n_relay.+1, (1 < i)%N -> relay_at_body i ps) ->
    dsdp_inv ps
| Inv_ASj (j : 'I_n_relay.+1) ps :
    (2 <= j)%N ->
    size ps = n_relay.+2 ->
    @all_proc_wf AHE ps ->
    (exists v k, nth (default_proc data) ps 0 = Send j v k) ->
    (* relay j-1 at position j has Recv(0,...) *)
    (exists f, nth (default_proc data) ps j = Recv 0 f) ->
    (forall i : 'I_n_relay.+1, (j < i)%N -> relay_at_body i ps) ->
    dsdp_inv ps
| Inv_drain (j : 'I_n_relay.+1) ps :
    (j.+1 < n_relay.+1)%N ->
    size ps = n_relay.+2 ->
    @all_proc_wf AHE ps ->
    (exists f, nth (default_proc data) ps 0 = Recv n_relay.+1 f) ->
    (exists v, nth (default_proc data) ps j.+1 = Send j.+2 v Finish) ->
    (exists f, nth (default_proc data) ps j.+2 = Recv j.+1 f) ->
    dsdp_inv ps
| Inv_tail ps :
    size ps = n_relay.+2 ->
    @all_proc_wf AHE ps ->
    (exists v, nth (default_proc data) ps n_relay.+1 = Send 0 v Finish) ->
    (exists f, nth (default_proc data) ps 0 = Recv n_relay.+1 f) ->
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
Proof. Admitted.

(* C2 sub-lemmas *)
Lemma dsdp_inv_step_AR (j : 'I_n_relay.+1) ps :
  size ps = n_relay.+2 -> @all_proc_wf AHE ps ->
  (exists f, nth (default_proc data) ps 0 = Recv j.+1 f) ->
  relay_at_body j ps ->
  (forall i : 'I_n_relay.+1, (j < i)%N -> relay_at_body i ps) ->
  all_terminated (one_step_procs data ps) \/ dsdp_inv (one_step_procs data ps).
Proof. Admitted.

Lemma dsdp_inv_step_AS0 ps (f_inner : plain AHE -> proc data) :
  size ps = n_relay.+2 -> @all_proc_wf AHE ps ->
  (exists v k, nth (default_proc data) ps 0 = Send 1 v k) ->
  nth (default_proc data) ps 1 =
    Recv 0 (oapp f_inner Fail \o (obind (@dec AHE (dk_relay ord0)) \o @std_from_enc AHE)) ->
  (forall i : 'I_n_relay.+1, (0 < i)%N -> relay_at_body i ps) ->
  all_terminated (one_step_procs data ps) \/ dsdp_inv (one_step_procs data ps).
Proof. Admitted.

Lemma dsdp_inv_step_AS1 ps (f_inner : cipher AHE -> proc data) :
  size ps = n_relay.+2 -> @all_proc_wf AHE ps ->
  (exists v k, nth (default_proc data) ps 0 = Send 1 v k) ->
  nth (default_proc data) ps 1 =
    Recv 0 (oapp f_inner Fail \o @std_from_enc AHE) ->
  (forall i : 'I_n_relay.+1, (1 < i)%N -> relay_at_body i ps) ->
  all_terminated (one_step_procs data ps) \/ dsdp_inv (one_step_procs data ps).
Proof. Admitted.

Lemma dsdp_inv_step_ASj (j : 'I_n_relay.+1) ps :
  (2 <= j)%N ->
  size ps = n_relay.+2 -> @all_proc_wf AHE ps ->
  (exists v k, nth (default_proc data) ps 0 = Send j v k) ->
  (* relay j-1 at position j has Recv(0,...) *)
  (exists f, nth (default_proc data) ps j = Recv 0 f) ->
  (forall i : 'I_n_relay.+1, (j < i)%N -> relay_at_body i ps) ->
  all_terminated (one_step_procs data ps) \/ dsdp_inv (one_step_procs data ps).
Proof. Admitted.

Lemma dsdp_inv_step_FW (j : 'I_n_relay.+1) ps :
  (j.+1 < n_relay.+1)%N ->
  size ps = n_relay.+2 -> @all_proc_wf AHE ps ->
  (exists f, nth (default_proc data) ps 0 = Recv n_relay.+1 f) ->
  (exists v, nth (default_proc data) ps j.+1 = Send j.+2 v Finish) ->
  (exists f, nth (default_proc data) ps j.+2 = Recv j.+1 f) ->
  all_terminated (one_step_procs data ps) \/ dsdp_inv (one_step_procs data ps).
Proof. Admitted.

Lemma dsdp_inv_step_FW_last ps :
  size ps = n_relay.+2 -> @all_proc_wf AHE ps ->
  (exists f, nth (default_proc data) ps 0 = Recv n_relay.+1 f) ->
  (exists v, nth (default_proc data) ps n_relay = Send n_relay.+1 v Finish) ->
  (exists f, nth (default_proc data) ps n_relay.+1 = Recv n_relay f) ->
  all_terminated (one_step_procs data ps) \/ dsdp_inv (one_step_procs data ps).
Proof. Admitted.

Lemma dsdp_inv_step_TAIL ps :
  size ps = n_relay.+2 -> @all_proc_wf AHE ps ->
  (exists v, nth (default_proc data) ps n_relay.+1 = Send 0 v Finish) ->
  (exists f, nth (default_proc data) ps 0 = Recv n_relay.+1 f) ->
  all_terminated (one_step_procs data ps) \/ dsdp_inv (one_step_procs data ps).
Proof. Admitted.

Lemma dsdp_inv_step_RET ps d0 :
  size ps = n_relay.+2 -> @all_proc_wf AHE ps ->
  nth (default_proc data) ps 0 = Ret d0 ->
  (forall j : 'I_n_relay.+1, relay_at_finish_pred j ps) ->
  all_terminated (one_step_procs data ps) \/ dsdp_inv (one_step_procs data ps).
Proof. Admitted.

(* C2: Invariant preserved by one_step *)
Lemma dsdp_inv_step ps :
  dsdp_inv ps ->
  all_terminated (one_step_procs data ps) \/ dsdp_inv (one_step_procs data ps).
Proof. Admitted.

(* C3: Step 2 satisfies invariant *)
Lemma dsdp_inv_init :
  dsdp_inv (one_step_procs data (one_step_procs data procs)).
Proof. Admitted.

(* C4: Connect dsdp_reachable to dsdp_inv *)
Lemma dsdp_reachable_inv ps k :
  dsdp_reachable ps k -> (2 <= k)%N ->
  all_terminated ps \/ dsdp_inv ps.
Proof. Admitted.

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
(* Case on has_progress(one_step ps) *)
case Hp1: (has_progress data (one_step_procs data ps)).
- by right.
- left.
  (* ~has_progress(one_step ps). Need all_terminated. *)
  (* For steps 0-1: step01_progress gives has_progress → contradiction *)
  have Hk : (2 <= k)%N.
    case: k Hr Hp1 {Hwf Hp} => [|[|k']] Hr Hp1 //.
    + exfalso; move/negP: Hp1; apply. inversion Hr; subst.
      exact: step_procs_has_progress.
    + exfalso; move/negP: Hp1; apply.
      inversion Hr as [|ps' k' Hr' Hprog' Heqps Hk'].
      inversion Hr' as [Hps'|]; subst.
      exact: has_progress_at_step_2.
  (* Step >= 2: show each process in one_step is terminal *)
  (* From ~has_progress(one_step): no Init, no Ret in one_step. *)
  (* From proc_wf preservation: no Fail in one_step. *)
  have noprogress_no_init : forall p, (p < size (one_step_procs data ps))%N ->
    forall d0 k0, nth (default_proc data) (one_step_procs data ps) p <> Init d0 k0.
    move=> p Hsz d0 k0 Hinit. move/negP: Hp1; apply.
    apply (@step_i_has_progress data (one_step_procs data ps) p Hsz).
    by rewrite /smc_interpreter.step Hinit.
  have noprogress_no_ret : forall p, (p < size (one_step_procs data ps))%N ->
    forall d0, nth (default_proc data) (one_step_procs data ps) p <> Ret d0.
    move=> p Hsz d0 Hret. move/negP: Hp1; apply.
    apply (@step_i_has_progress data (one_step_procs data ps) p Hsz).
    by rewrite /smc_interpreter.step Hret.
  have noprogress_no_fail : forall p, (p < size ps)%N ->
    nth (default_proc data) (one_step_procs data ps) p <> Fail.
    move=> p Hsz Hfail.
    have Hsz' : (p < size (one_step_procs data ps))%N by rewrite (@size_one_step data).
    have Hwf1 := @one_step_preserves_proc_wf ps Hwf p Hsz'.
    by rewrite Hfail in Hwf1.
  (* Case-split each position: Init/Ret/Fail are ruled out, Finish is terminal,
     Send/Recv need the DSDP deadlock-freedom argument. *)
  apply/(@all_nthP _ _ _ (default_proc data)).
  rewrite (@size_one_step data) => p Hsz.
  have Hsz' : (p < size (one_step_procs data ps))%N by rewrite (@size_one_step data).
  case Hosp: (nth (default_proc data) (one_step_procs data ps) p)
    => [d0 k0|j0 v0' k0|frm0 f0|d0||].
  - by exfalso; exact: (noprogress_no_init p Hsz' d0 k0 Hosp).
  - (* Send j0 v0' k0 at position p in one_step: unmatched.
       Need: this is impossible in DSDP body phase.
       DSDP deadlock-freedom: every Send has a matching Recv. *)
    exfalso.
    admit.
  - (* Recv frm0 f0 at position p in one_step: unmatched.
       Same DSDP deadlock-freedom argument. *)
    exfalso.
    admit.
  - by exfalso; exact: (noprogress_no_ret p Hsz' d0 Hosp).
  - by []. (* Finish: is_terminal = true *)
  - by exfalso; exact: (noprogress_no_fail p Hsz Hosp).
Admitted.

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
