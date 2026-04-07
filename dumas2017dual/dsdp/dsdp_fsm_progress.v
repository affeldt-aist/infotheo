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

(* Aliases for Records and helper definitions from dsdp_fsm.v that take
   section variables as explicit params after section closure. *)
Local Notation recv_phase :=
  (recv_phase ek dk_relay u r rand_a v_relay r1_relay r2_relay).
Local Notation send_phase :=
  (send_phase ek dk_relay u r v_relay r1_relay r2_relay).
Local Notation drain_phase :=
  (drain_phase ek u r rand_a v_relay r1_relay r2_relay).
Local Notation tail_phase :=
  (tail_phase ek u r v_relay).
Local Notation bg_s_of :=
  (@bg_s_of AHE ek n_relay dk dk_relay relays v0 u r rand_a v_relay r1_relay r2_relay).
Local Notation bg'_of :=
  (@bg'_of AHE ek n_relay dk dk_relay relays v0 u r rand_a v_relay r1_relay r2_relay).
Local Notation known_ret_state := (@known_ret_state AHE n_relay v0 u r v_relay).
Local Notation KnownRetBase := (@KnownRetBase AHE n_relay v0 u r v_relay).
Local Notation drain_steppable :=
  (@drain_steppable AHE ek n_relay dk relays Hrelays v0 u r rand_a v_relay).
Local Notation recv_send_steppable :=
  (@recv_send_steppable AHE ek n_relay dk dk_relay relays Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay r2_relay).
Local Notation bg_nop_recv :=
  (@bg_nop_recv AHE ek n_relay dk dk_relay relays v0 u r rand_a v_relay r1_relay r2_relay).
Local Notation bg_nop_send :=
  (@bg_nop_send AHE ek n_relay dk dk_relay relays v0 u r rand_a v_relay r1_relay r2_relay).

(* Re-declare Arguments for record field projections so that the record
   instance is the first positional (non-implicit) arg inside this section.
   This avoids having to write `(d:=dp)` everywhere after section closure. *)
Arguments dp_j {AHE ek n_relay u r rand_a v_relay r1_relay r2_relay} d.
Arguments dp_rr_drain {AHE ek n_relay u r rand_a v_relay r1_relay r2_relay} d.
Arguments dp_bg {AHE ek n_relay u r rand_a v_relay r1_relay r2_relay} d _.
Arguments dp_safe {AHE ek n_relay u r rand_a v_relay r1_relay r2_relay} d v k _.
Arguments dp_j_lt {AHE ek n_relay u r rand_a v_relay r1_relay r2_relay} d.
Arguments dp_sender {AHE ek n_relay u r rand_a v_relay r1_relay r2_relay} d.
Arguments dp_finish {AHE ek n_relay u r rand_a v_relay r1_relay r2_relay} d _ _.
Arguments dp_last {AHE ek n_relay u r rand_a v_relay r1_relay r2_relay} d.
Arguments dp_between {AHE ek n_relay u r rand_a v_relay r1_relay r2_relay} d _ _ _.
Arguments sp_j {AHE ek n_relay dk_relay u r v_relay r1_relay r2_relay} s.
Arguments sp_rr_fw {AHE ek n_relay dk_relay u r v_relay r1_relay r2_relay} s.
Arguments sp_bg {AHE ek n_relay dk_relay u r v_relay r1_relay r2_relay} s _.
Arguments sp_j_ge2 {AHE ek n_relay dk_relay u r v_relay r1_relay r2_relay} s.
Arguments sp_active {AHE ek n_relay dk_relay u r v_relay r1_relay r2_relay} s.
Arguments sp_ahead {AHE ek n_relay dk_relay u r v_relay r1_relay r2_relay} s _ _ _.
Arguments sp_next_behind {AHE ek n_relay dk_relay u r v_relay r1_relay r2_relay} s _.
Arguments sp_last {AHE ek n_relay dk_relay u r v_relay r1_relay r2_relay} s _.
Arguments sp_sender2 {AHE ek n_relay dk_relay u r v_relay r1_relay r2_relay} s _.
Arguments sp_sender {AHE ek n_relay dk_relay u r v_relay r1_relay r2_relay} s _.
Arguments tp_rr_tail {AHE ek n_relay u r v_relay} t.
Arguments tp_bg {AHE ek n_relay u r v_relay} t _.
Arguments tp_last {AHE ek n_relay u r v_relay} t.
Arguments tp_finish {AHE ek n_relay u r v_relay} t _ _.
Arguments rp_j {AHE ek n_relay dk_relay u r rand_a v_relay r1_relay r2_relay} r.
Arguments rp_rr_fw {AHE ek n_relay dk_relay u r rand_a v_relay r1_relay r2_relay} r.
Arguments rp_bg {AHE ek n_relay dk_relay u r rand_a v_relay r1_relay r2_relay} r _.
Arguments rp_ahead {AHE ek n_relay dk_relay u r rand_a v_relay r1_relay r2_relay} r {i} _ _.
Arguments rp_behind {AHE ek n_relay dk_relay u r rand_a v_relay r1_relay r2_relay} r _.
Arguments rp_finish {AHE ek n_relay dk_relay u r rand_a v_relay r1_relay r2_relay} r {i} _.
Arguments rp_sender {AHE ek n_relay dk_relay u r rand_a v_relay r1_relay r2_relay} r _.
Arguments rp_sender2 {AHE ek n_relay dk_relay u r rand_a v_relay r1_relay r2_relay} r _.
Arguments rp_receiver {AHE ek n_relay dk_relay u r rand_a v_relay r1_relay r2_relay} r _.
Arguments rp_j1_recv {AHE ek n_relay dk_relay u r rand_a v_relay r1_relay r2_relay} r _.

(* Next index for recv_phase advancement (used by mk_next_* lemmas) *)
Let next_j (rp : recv_phase) (Hjn : (rp_j rp < n_relay)%N) : 'I_n_relay.+1 :=
  @inord n_relay (rp_j rp).+1.
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
(* Section-closed aliases mirroring dsdp_fsm.v Section dsdp_fsm_chain.         *)
(* Required for the Record-based progress proofs migrated from dsdp_fsm.v.    *)
(* ========================================================================== *)

Let st_ret_local := @st_ret AHE n_relay v0 u r v_relay.
Let st_tail_local := fun rr =>
  @st_tail AHE ek n_relay dk relays Hrelays v0 u r rand_a v_relay rr.
Let st_drain_gen_local := fun j rr bg Hbg =>
  @st_drain_gen AHE ek n_relay dk relays Hrelays v0 u r rand_a v_relay
    j rr bg Hbg.

Local Notation recv_st :=
  (st_recv_gen ek dk dk_relay Hrelays Hrelays_id
     v0 u r rand_a v_relay r1_relay r2_relay).
Local Notation send_st :=
  (@st_send_gen AHE ek n_relay dk dk_relay relays
     v0 u r rand_a v_relay r1_relay r2_relay).
Local Notation drain_st :=
  (@st_drain_gen AHE ek n_relay dk relays Hrelays
     v0 u r rand_a v_relay).
Local Notation tail_st :=
  (@st_tail AHE ek n_relay dk relays Hrelays
     v0 u r rand_a v_relay).

Let recv_procs_gen_local := @recv_procs_gen AHE ek n_relay dk dk_relay relays
    v0 u r rand_a v_relay r1_relay r2_relay.
Let send_procs_gen_local := @send_procs_gen AHE ek n_relay dk dk_relay relays
    v0 u r rand_a v_relay r1_relay r2_relay.
Let relay_body_local := @relay_body AHE ek n_relay dk_relay v_relay r1_relay r2_relay.
Let bg_init_local := @bg_init AHE ek n_relay dk_relay v_relay r1_relay r2_relay.
Let alice_enc_local := @alice_enc AHE ek n_relay u r rand_a v_relay r1_relay.
Let term_local := @term AHE n_relay u r v_relay.

Let e_loc := @di_e _ DI.  (* cipher -> std_data wrapper *)

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

(* Helper: tail state is not terminated (last relay still active) *)
Lemma tail_not_terminated (rr : rand AHE) :
  ~~ @all_terminated data (ps_procs (st_tail_local rr)).
Proof.
rewrite /st_tail_local /= /all_terminated /tail_procs.
rewrite all_cat /= andbF.
by rewrite andbF.
Qed.

(* known_ret_tail: the tail state is in known_ret_state *)
Lemma known_ret_tail (rr : rand AHE) : known_ret_state (st_tail_local rr).
Proof.
apply (KnownRetStep KnownRetBase).
- exact: (@step_ok_tail_ret AHE ek n_relay Hn_relay dk relays Hrelays
            v0 u r rand_a v_relay key_alice rr).
- exact: (@tail_has_progress AHE ek n_relay dk relays Hrelays
            v0 u r rand_a v_relay rr).
- exact: (tail_not_terminated rr).
Qed.

(* recv states are not all-terminated (Alice at position 0 is Recv, not terminal) *)
Lemma recv_not_terminated_gen (j : 'I_n_relay.+1) (bg : nat -> proc (std_data AHE)) :
  ~~ @all_terminated data (ps_procs (recv_st j bg)).
Proof.
rewrite /= /all_terminated /recv_procs_gen.
have Hj := ltn_ord j.
have [f ->] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays Hrelays_id v0 u r rand_a (j : nat) Hj.
by [].
Qed.

(* send states are not all-terminated (Alice at position 0 is Send, not terminal) *)
Lemma send_not_terminated_gen (j : 'I_n_relay.+1) (bg : nat -> proc (std_data AHE)) :
  ~~ @all_terminated data (ps_procs (send_st j bg)).
Proof.
by rewrite /= /all_terminated /send_procs_gen.
Qed.

(* NOP condition for recv: if for all i != j, bg(i) is either
   Send 0 _ _ or Recv 0 _ or Finish, then bg_nop_recv j bg holds.
   This is because position 0 is Recv j.+1, so:
   - Send 0 at i+1: destination 0 has Recv j.+1, frm=j.+1 != i.+1 (since i!=j). NOP.
   - Recv 0 at i+1: source 0 has Recv (not Send). NOP.
   - Finish at i+1: always NOP. *)
Lemma bg_nop_recv_safe (j : 'I_n_relay.+1) (bg : nat -> proc (std_data AHE)) :
  (forall i, (i < n_relay.+1)%N -> i != (j : nat) ->
    match bg i with
    | Send 0 _ _ => True
    | Recv 0 _ => True
    | Finish => True
    | _ => False
    end) ->
  bg_nop_recv j bg.
Proof.
move=> Hsafe i Hi Hneq.
rewrite /is_nop /recv_procs_gen /smc_interpreter.step /=.
have Hj := ltn_ord j.
have [f Haf] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays Hrelays_id v0 u r rand_a (j : nat) Hj.
rewrite nth_mkseq; last exact Hi.
rewrite (negbTE Hneq).
have Hsafei := Hsafe i Hi Hneq.
case Hbgi : (bg i) Hsafei => [d0 next|dst w next|frm ff|d0| |] //=.
- (* Send dst w next *)
  case: dst Hbgi => [|dst'] Hbgi Hsafei.
  + (* Send 0: check if receiver matches *)
    rewrite Haf /=.
    have -> : ((Ordinal Hj).+1 == i.+1) = false.
      apply /eqP. move=> H. apply (negP Hneq).
      by apply /eqP; apply succn_inj.
    by [].
  + by case: Hsafei.
- (* Recv frm ff *)
  case: frm Hbgi => [|frm'] Hbgi Hsafei.
  + (* Recv 0: position 0 is Recv, not Send. NOP. *)
    rewrite Haf /=. by [].
  + by case: Hsafei.
Qed.

(* bg_init satisfies the NOP condition for any j *)
Lemma bg_nop_recv_init (j : 'I_n_relay.+1) :
  bg_nop_recv j (@bg_init AHE ek n_relay dk_relay v_relay r1_relay r2_relay).
Proof.
apply bg_nop_recv_safe.
move=> i Hi _.
rewrite /bg_init.
have [sk ->] := @relay_body_is_send0 AHE ek n_relay dk_relay v_relay r1_relay r2_relay (inord i).
by [].
Qed.

(* relay_body is always Send 0 ... *)
Lemma relay_body_send0 (j : 'I_n_relay.+1) :
  exists v k, @relay_body AHE ek n_relay dk_relay v_relay r1_relay r2_relay j = Send 0 v k.
Proof.
have [sk Hsk] := @relay_body_is_send0 AHE ek n_relay dk_relay v_relay r1_relay r2_relay j.
by eexists; eexists; exact Hsk.
Qed.

(* interp_chain_known_ret: if interp_comp reaches st_ret in fuel+1 steps
   with progress and non-termination at every intermediate step,
   then the starting state is known_ret_state. *)
Lemma interp_chain_known_ret (fuel : nat) (st : phase_state AHE) :
  @interp_comp (std_data AHE) (ps_procs st) fuel.+1 = ps_procs st_ret_local ->
  (forall k, (k < fuel.+1)%N ->
    @has_progress (std_data AHE) (@interp_comp (std_data AHE) (ps_procs st) k)) ->
  (forall k, (k < fuel.+1)%N ->
    ~~ @all_terminated (std_data AHE) (@interp_comp (std_data AHE) (ps_procs st) k)) ->
  known_ret_state st.
Proof.
elim: fuel st => [|fuel IH] st Hreach Hprog Hnt.
- (* fuel = 0 *)
  rewrite interp_comp_unfold_eq in Hreach.
  case Hhas : (has_progress (std_data AHE) (ps_procs st)); last first.
    by exfalso; move: (Hprog 0 (ltn0Sn _)); rewrite Hhas.
  rewrite Hhas in Hreach.
  exact (KnownRetStep KnownRetBase Hreach Hhas (Hnt 0 (ltn0Sn _))).
- (* fuel = n+1 *)
  rewrite interp_comp_unfold_eq in Hreach.
  case Hhas : (has_progress (std_data AHE) (ps_procs st)); last first.
    by exfalso; move: (Hprog 0 (ltn0Sn _)); rewrite Hhas.
  rewrite Hhas in Hreach.
  set st' := @PhaseState AHE (one_step_procs (ps_procs st))
    ((smc_interpreter.step (one_step_procs (ps_procs st)) [::] 0).1.2) erefl.
  have Hst' : ps_procs st' = one_step_procs (ps_procs st) by [].
  refine (KnownRetStep _ (esym Hst') Hhas (Hnt 0 (ltn0Sn _))).
  apply IH.
  + by rewrite Hst'.
  + move=> k Hk. move: (Hprog k.+1 Hk). by rewrite interp_comp_unfold_eq Hhas.
  + move=> k Hk. move: (Hnt k.+1 Hk). by rewrite interp_comp_unfold_eq Hhas.
Qed.

(* relay_after_send0 j produces a safe form at position j.
   For j < n_relay, it's Recv 0 with safe callback.
   For j = n_relay, it's Recv n_relay with callback → Send 0 ... Finish. *)
Lemma relay_after_send0_safe (j : 'I_n_relay.+1) :
  (j < n_relay)%N ->
  bg_safe_form j (@relay_after_send0 AHE ek n_relay dk_relay v_relay r1_relay r2_relay j).
Proof.
move=> Hjn.
rewrite /relay_after_send0.
case: ifP => Hj0.
- (* j = 0 *)
  apply BSF_recv0 => v0'.
  rewrite /std_Recv_dec /Recv_param /= /std_from_enc /=.
  case: v0' => [[[m|c]|p]|dd].
  + by apply BSF_fail.
  + case Hdec: (dec (dk_relay j) c) => [m0|].
    * rewrite /= /std_Recv_enc /Recv_param /=.
      rewrite Hdec /=.
      apply BSF_recv0 => v1'.
      rewrite /= /std_from_enc.
      case: v1' => [[[m'|c']|p']|dd'] /=;
        [by apply BSF_fail | by apply BSF_send |
         by apply BSF_fail | by apply BSF_fail].
    * exfalso. move/eqP: (dec_total (dk_relay j) c). by rewrite Hdec.
  + by apply BSF_fail.
  + by apply BSF_fail.
- case: ifP => Hjn'.
  + (* j = n_relay: contradicts Hjn *)
    exfalso. move/eqP: Hjn' => Hjn'.
    rewrite Hjn' in Hjn. by rewrite ltnn in Hjn.
  + (* intermediate j *)
    apply BSF_recv0 => v0'.
    rewrite /std_Recv_enc /Recv_param /= /std_from_enc /=.
    case: v0' => [[[m|c]|p]|dd].
    * by apply BSF_fail.
    * apply BSF_recv_i => v1'.
      rewrite /std_Recv_dec /Recv_param /= /std_from_enc /=.
      case: v1' => [[[m'|c']|p']|dd'].
      -- by apply BSF_fail.
      -- case Hdec: (dec (dk_relay j) c') => [m0|].
         ** rewrite /= Hdec /=. by apply BSF_send.
         ** exfalso. move/eqP: (dec_total (dk_relay j) c'). by rewrite Hdec.
      -- by apply BSF_fail.
      -- by apply BSF_fail.
    * by apply BSF_fail.
    * by apply BSF_fail.
Qed.

(* bg_safe_form processes always step to bg_safe_form processes,
   regardless of what's in the process list.
   Key insight: all bg_safe_form constructors either produce terminal forms
   (Finish, Fail) or communicate on specific channels. If a pair fires,
   the callback output also satisfies bg_safe_form by the inductive
   closure in BSF_recv0/BSF_recv_i. *)
Lemma bg_safe_form_step_any (ps : seq (proc (std_data AHE))) (i : nat)
    (p : proc (std_data AHE)) :
  nth (@default_proc (std_data AHE)) ps i.+1 = p ->
  bg_safe_form i p ->
  bg_safe_form i (smc_interpreter.step ps [::] i.+1).1.1.
Proof.
move=> Hnth Hbsf.
rewrite /smc_interpreter.step Hnth.
elim: Hbsf => {p Hnth} [i0|i0|i0 v|i0 f Hf IH|i0 f Hf IH].
- by apply BSF_finish.
- by apply BSF_fail.
- case: (nth _ ps i0.+2) => [d0 next|dst' w next'|frm ff|d0| |] //=;
    try by apply BSF_send.
  case: ifP => _; [by apply BSF_finish | by apply BSF_send].
- case: (nth _ ps 0) => [d0' next'|dst' w' next'|frm' ff'|d0'| |] //=;
    try by (apply BSF_recv0 => v'; exact: Hf).
  case: ifP => Hdst'; [exact: Hf | by apply BSF_recv0 => v'; exact: Hf].
- case: (nth _ ps i0) => [d0' next'|dst' w' next'|frm' ff'|d0'| |] //=;
    try by (apply BSF_recv_i => v'; exact: Hf).
  case: ifP => Hdst'; [exact: Hf | by apply BSF_recv_i => v'; exact: Hf].
Qed.

(* Type-level sig variant of relay_after_send0_recv0, needed to construct
   sp_active and sp_next_behind in send_phase (which use sig, not exists). *)
Lemma relay_after_send0_recv0_sig (k : 'I_n_relay.+1) :
  (k < n_relay)%N ->
  { f | @relay_after_send0 AHE ek n_relay dk_relay v_relay r1_relay r2_relay k
        = Recv 0 f }.
Proof.
move=> Hkn.
rewrite /relay_after_send0.
case: ifP => Hk0.
  rewrite /std_Recv_dec /Recv_param /=. by eexists.
case: ifP => Hkn'.
  by move/eqP: Hkn' => Hkn'; rewrite Hkn' ltnn in Hkn.
rewrite /std_Recv_enc /Recv_param /=. by eexists.
Qed.

(* Helper: drain states are not all-terminated (Alice tail Recv is not terminal) *)
Lemma drain_not_terminated_gen (j : 'I_n_relay.+1) (rr : rand AHE)
    (bg : nat -> proc data)
    (Hbg_safe : forall v k, bg n_relay <> Send 0 v k) :
  ~~ @all_terminated data (ps_procs (drain_st j rr (bg:=bg) Hbg_safe)).
Proof.
rewrite /= /all_terminated /drain_procs_gen /=.
rewrite alice_foldr_at_tail; last exact: Hrelays.
have [f Hf] := @alice_tail_is_recv AHE n_relay dk v0 u r.
rewrite Hf.
by [].
Qed.

(* known_ret_drain_chain: if drain chain evidence exists, drain is in known_ret_state *)
Lemma known_ret_drain_chain (j : 'I_n_relay.+1) (rr : rand AHE)
    (bg : nat -> proc (std_data AHE))
    (Hbg_safe : forall v k, bg n_relay <> Send 0 v k) :
  drain_steppable j rr bg ->
  known_ret_state (drain_st j rr (bg:=bg) Hbg_safe).
Proof.
move=> Hds; induction Hds as
  [j0 rr0 bg0 Hs0 rr0' Hstep0 Hprog0 Hnt0
  |j0 rr0 bg0 Hs0 rr0' bg0' Hs0' Hstep0 Hprog0 Hnt0 _ IH].
- have Hirr : ps_procs (drain_st j0 rr0 (bg:=bg0) Hs0) =
              ps_procs (drain_st j0 rr0 (bg:=bg0) Hbg_safe) by [].
  apply (KnownRetStep (known_ret_tail rr0')); rewrite -Hirr //.
- have Hirr : ps_procs (drain_st j0 rr0 (bg:=bg0) Hs0) =
              ps_procs (drain_st j0 rr0 (bg:=bg0) Hbg_safe) by [].
  apply (KnownRetStep (IH Hs0')); rewrite -Hirr //.
Qed.

(* known_ret_recv_gen: if recv/send chain evidence exists, recv is in known_ret_state *)
Lemma known_ret_recv_gen (j : 'I_n_relay.+1) (bg : nat -> proc (std_data AHE)) :
  recv_send_steppable j bg ->
  known_ret_state (recv_st j bg).
Proof.
move=> Hrss; induction Hrss as
  [j0 bg0 bg_s0 rr_d0 bg_d0 Hs_d0
     Hprog_r0 Hnt_r0 Hstep_rs0
     Hprog_s0 Hnt_s0 Hstep_sd0 Hds0
  |j0 bg0 bg_s0 j0' bg0'
     Hprog_r0 Hnt_r0 Hstep_rs0
     Hprog_s0 Hnt_s0 Hstep_sr0 _ IH
  |j0 bg0 Hks2].
- refine (KnownRetStep _ Hstep_rs0 Hprog_r0 Hnt_r0).
  refine (KnownRetStep _ Hstep_sd0 Hprog_s0 Hnt_s0).
  exact (@known_ret_drain_chain _ _ _ Hs_d0 Hds0).
- refine (KnownRetStep _ Hstep_rs0 Hprog_r0 Hnt_r0).
  exact (KnownRetStep IH Hstep_sr0 Hprog_s0 Hnt_s0).
- exact Hks2.
Qed.

(* H1: rp_ahead — relays beyond j+1 are untouched *)
Lemma mk_next_ahead (rp : recv_phase) (Hjn : (rp_j rp < n_relay)%N) :
  let j := rp_j rp in
  forall i, (j.+1 < i)%N -> (i < n_relay.+1)%N ->
    bg'_of rp i = relay_body_local (inord i).
Proof.
move=> /= i Hij Hi.
set j := rp_j rp.
have Hji : (j < i)%N by apply (ltn_trans (ltnSn j) Hij).
have Hbg_s_i : bg_s_of rp i = relay_body_local (inord i).
  rewrite /bg_s_of /=. apply bg_relay_ahead_recv => //.
  exact: (rp_ahead rp Hji Hi).
rewrite /bg'_of /=.
transitivity (bg_s_of rp i); last exact Hbg_s_i.
apply (@bg_relay_ahead_send AHE ek n_relay dk dk_relay relays
  v0 u r rand_a v_relay r1_relay r2_relay j (bg_s_of rp) i) => //.
Qed.

(* H2: rp_behind — strengthened to match A7 of Inv_AR.
   Returns the SPECIFIC callback f0 from relay_body's second continuation. *)
Lemma mk_next_behind (rp : recv_phase) (Hjn : (rp_j rp < n_relay)%N) :
  (2 <= next_j Hjn)%N ->
  exists sv0 f0,
    relay_body_local (inord (next_j Hjn).-1) = Send 0 sv0 (Recv 0 f0) /\
    bg'_of rp (next_j Hjn).-1 = Recv 0 f0.
Proof.
set j := rp_j rp.
have Hinord : (next_j Hjn : nat) = j.+1 by rewrite /next_j inordK.
rewrite Hinord => Hj1.
have Hjpos : (0 < j)%N by exact Hj1.
(* relay_body j = Send 0 v (relay_after_send0 j), relay_after_send0 j = Recv 0 f *)
have Hrb := @relay_body_send0_cont AHE ek n_relay dk_relay v_relay r1_relay r2_relay j.
have [f_ras Hras_eq] := @relay_after_send0_recv0 AHE ek n_relay dk_relay
  v_relay r1_relay r2_relay j Hjn.
have Hinord_j : (inord j : 'I_n_relay.+1) = j by apply val_inj; rewrite /= inordK.
exists (e_loc (enc (ek (nat_to_party_id j.+1)) (v_relay j) (r1_relay j))).
exists f_ras.
split.
- (* relay_body (inord j) = Send 0 ... (Recv 0 f_ras) *)
  rewrite /relay_body_local Hinord_j Hrb.
  by rewrite Hras_eq.
- (* bg'_of rp j = Recv 0 f_ras *)
  rewrite /bg'_of /bg_s_of /=.
  rewrite /send_procs_gen /step /=.
  rewrite nth_mkseq; last exact (ltn_ord j).
  rewrite eqxx Hinord_j Hras_eq /=.
  (* alice_send_dest j != j.+1 since j >= 1 *)
  have Hdst : (alice_send_dest j == j.+1) = false.
    apply /eqP. rewrite /alice_send_dest /maxn.
    case: ltnP => Hlt Heq.
    + have Habs : (j : nat) = (j : nat).+1 by exact Heq.
      by move: (neq_succn (esym Habs)).
    + (* Heq : 1 = j.+1, but j >= 1 *)
      have : (j : nat) = 0%N by apply succn_inj.
      move=> Hj0_abs. by rewrite Hj0_abs in Hjpos.
  by rewrite Hdst.
Qed.

(* H3: rp_finish — finish zone preserved *)
Lemma mk_next_finish (rp : recv_phase) (Hjn : (rp_j rp < n_relay)%N) :
  forall i, (i.+1 < (next_j Hjn).-2)%N -> bg'_of rp i = Finish.
Proof.
have Hinord : (next_j Hjn : nat) = (rp_j rp).+1 by rewrite /next_j inordK.
rewrite Hinord => i Hi.
have Hi' : (i.+1 < (rp_j rp).-1)%N by exact Hi.
have Hi1j : (i.+1 < rp_j rp)%N := leq_trans Hi' (leq_pred _).
have Hij : (i < rp_j rp)%N := ltn_trans (ltnSn i) Hi1j.
have Hineq : (i != (rp_j rp : nat))%N by rewrite neq_ltn Hij.
have Hi_bound : (i < n_relay.+1)%N := ltn_trans Hij (ltn_ord _).
case: (boolP (i.+1 < (rp_j rp).-2)%N) => [Hi_deep | Hi_border].
- (* Deep finish zone *)
  have Hfin : rp_bg rp i = Finish by apply (rp_finish rp Hi_deep).
  rewrite /bg'_of /bg_s_of /send_procs_gen_local /recv_procs_gen_local /=.
  set bg_s_local := (fun i0 : nat => _).
  have Hbg_s_i : bg_s_local i = Finish.
    rewrite /bg_s_local. by apply bg_finish_nop_recv.
  by apply: bg_finish_nop_send Hbg_s_i.
- (* Border case: i = (rp_j rp - 3)%N, frontier sender fires *)
  rewrite -ltnNge in Hi_border.
  have Hj3 : (3 <= rp_j rp)%N.
    have Hjm1_2 : (2 <= (rp_j rp).-1)%N by apply: leq_trans Hi'.
    have Hjpos : (0 < rp_j rp)%N := ltn_trans (ltn0Sn i) Hi1j.
    by rewrite -(prednK Hjpos) ltnS.
  have Hi_eq : i = ((rp_j rp : nat) - 3)%N.
    apply anti_leq.
    apply /andP; split.
    + rewrite leq_subRL.
        have Hjpos : (0 < rp_j rp)%N := ltn_trans (ltn0Sn _) Hi1j.
        have Hhi : (i.+3 <= rp_j rp)%N by rewrite -(prednK Hjpos) ltnS; exact Hi'.
        by rewrite addnC addn3.
      exact Hj3.
    + rewrite leq_subLR.
      have H2 : ((rp_j rp).-2 + 2 <= i + 3)%N.
        have : ((rp_j rp).-2 + 2 <= i.+1 + 2)%N by rewrite leq_add2r; exact Hi_border.
        by rewrite addnS addn2 addn3 ltnS.
      rewrite -subn2 in H2.
      rewrite subnK in H2; last by exact (ltnW Hj3).
      by rewrite addnC.
  rewrite /bg'_of /bg_s_of /send_procs_gen_local /recv_procs_gen_local /=.
  have Hsnd := (rp_sender rp) Hj3.
  have [f_r [Hrcv _]] := (rp_receiver rp) Hj3.
  rewrite Hi_eq.
  have Hbg_s : (step (recv_procs_gen ek dk dk_relay relays v0 u r rand_a
    v_relay r1_relay r2_relay (rp_j rp) (rp_bg rp)) [::] ((rp_j rp : nat) - 3).+1).1.1 = Finish.
    by apply: bg_frontier_sender_fires Hsnd Hrcv.
  apply: bg_finish_nop_send Hbg_s.
  - apply (leq_ltn_trans (leq_subr 3 _) (ltn_ord _)).
  - apply /eqP => Habs.
    have : (rp_j rp - 3 < rp_j rp)%N by rewrite ltn_subrL /= (ltn_trans _ Hj3).
    by rewrite Habs ltnn.
Qed.

(* H4: rp_sender — frontier sender at (j+1)-3.
   The randomness rr_fw' is fresh per phase (Type-level sig so it can be
   destructed during Record construction): it equals
   rand_mul (alice_rr (j-1)) (r2_relay (j-2)) for the new phase j' = j+1. *)
Lemma mk_next_sender (rp : recv_phase) (Hjn : (rp_j rp < n_relay)%N) :
  let j' := next_j Hjn in
  (3 <= j')%N ->
  { rr_fw' : rand AHE | bg'_of rp ((j' : nat) - 3)%N = Send j'.-1
    (e_loc (@enc AHE (ek (nat_to_party_id j'.-1))
                 (chain_acc_local ((j' : nat) - 3)%N) rr_fw')) Finish }.
Proof.
move=> /=. set j := rp_j rp.
have Hinord : ((next_j Hjn : nat) = j.+1) by rewrite /next_j inordK.
rewrite Hinord => Hj3.
have Hj2 : (2 <= j)%N by exact Hj3.
case: (boolP ((j : nat) == 2%N)) => [Hj2eq | Hjne].
  (* j = 2 case: result follows from rp_sender2 via NOPs *)
  exists (rp_rr_fw rp).
  have Hjz : (j : nat) = 2%N by exact (eqP Hj2eq).
  have Hsub : (j.+1 - 3)%N = 0%N by rewrite Hjz.
  rewrite Hsub.
  have Hpred : j.+1.-1 = 2%N by rewrite Hjz.
  rewrite Hpred.
  have Hbg0 := (rp_sender2 rp) Hj2eq.
  rewrite -/j in Hbg0.
  have [sv0 [f0 [_ Hbg1]]] := (rp_behind rp) Hj2.
  rewrite -/j in Hbg1.
  have Hjm1z : (j.-1 = 1%N)%N by rewrite Hjz.
  rewrite Hjm1z in Hbg1.
  rewrite /bg'_of /=. set bgs := bg_s_of rp.
  have Hbgs0 : bgs 0 = rp_bg rp 0.
    rewrite /bgs /bg_s_of /recv_procs_gen_local /recv_procs_gen /step /=.
    rewrite nth_mkseq; last by [].
    have -> : (0 == j :> nat) = false by rewrite eq_sym Hjz.
    rewrite Hbg0 /=.
    rewrite (nth_map 0); last by rewrite size_iota.
    rewrite nth_iota //=.
    have -> : (1 == j :> nat) = false by rewrite eq_sym Hjz.
    by rewrite Hbg1.
  have Hbgs1 : bgs 1 = rp_bg rp 1.
    rewrite /bgs /bg_s_of /recv_procs_gen_local /recv_procs_gen /step /=.
    rewrite (nth_map 0); last by rewrite size_iota.
    rewrite nth_iota //=.
    have -> : (1 == j :> nat) = false by rewrite eq_sym Hjz.
    rewrite Hbg1 /=.
    have [f_alice Halice_eq] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays
      Hrelays_id v0 u r rand_a (rp_j rp) (ltn_ord _).
    by rewrite Halice_eq.
  rewrite /send_procs_gen_local /send_procs_gen /step /=.
  rewrite (nth_map 0); last by rewrite size_iota.
  rewrite nth_iota //=.
  have -> : (0 == j :> nat) = false by rewrite eq_sym Hjz.
  rewrite Hbgs0 Hbg0 /=.
  rewrite (nth_map 0); last by rewrite size_iota.
  rewrite nth_iota //=.
  have -> : (1 == j :> nat) = false by rewrite eq_sym Hjz.
  by rewrite Hbgs1 Hbg1 /=.
(* j >= 3 case: use rp_sender + rp_receiver + Emul_addM *)
have Hj3' : (3 <= j)%N.
  rewrite ltn_neqAle Hj2 andbT eq_sym. exact Hjne.
have [rr_a Halice] := @alice_enc_value AHE ek n_relay u r rand_a v_relay r1_relay (inord j.-1).
exists (rand_mul rr_a (r2_relay (inord ((j : nat) - 2)%N))).
have Hsub : (j.+1 - 3)%N = ((j : nat) - 2)%N.
  change 3%N with 2.+1. by rewrite subSS.
rewrite Hsub.
have Hsnd := (rp_sender rp) Hj3'.
rewrite -/j in Hsnd.
have [f_recv [Hrcv Hf_recv_eq]] := (rp_receiver rp) Hj3'.
rewrite -/j in Hrcv Hf_recv_eq.
have Hbgs_jm2 : bg_s_of rp ((j : nat) - 2)%N =
  f_recv (e_loc (enc (ek j.-1) (chain_acc_local ((j : nat) - 3)) (rp_rr_fw rp))).
  exact: bg_frontier_receiver_fires Hsnd Hrcv.
have [sv0 [f0 [_ Hbg_jm1]]] := (rp_behind rp) (ltnW Hj3').
rewrite -/j in Hbg_jm1.
have Hbgs_jm1 : bg_s_of rp j.-1 = rp_bg rp j.-1.
  rewrite /bg_s_of /recv_procs_gen_local /recv_procs_gen /step /=.
  rewrite (nth_map 0); last first.
    by rewrite size_iota; apply (leq_ltn_trans (leq_pred _) (ltn_ord _)).
  rewrite nth_iota; last by apply (leq_ltn_trans (leq_pred _) (ltn_ord _)).
  rewrite add0n.
  have -> : (j.-1 == j :> nat) = false.
    apply /eqP => H.
    have : (j.-1 < j)%N by rewrite ltn_predL (ltn_trans _ Hj3').
    by rewrite H ltnn.
  rewrite Hbg_jm1 /=.
  have [f_alice Halice_eq] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays
    Hrelays_id v0 u r rand_a (rp_j rp) (ltn_ord _).
  by rewrite Halice_eq.
rewrite /bg'_of /=. set bgs := bg_s_of rp.
rewrite /send_procs_gen_local /send_procs_gen /step /=.
rewrite (nth_map 0); last first.
  by rewrite size_iota; apply (leq_ltn_trans (leq_subr 2 j) (ltn_ord _)).
rewrite nth_iota; last by apply (leq_ltn_trans (leq_subr 2 j) (ltn_ord _)).
rewrite add0n.
have -> : ((j - 2)%N == j) = false.
  apply /eqP => Heq.
  have : ((j : nat) - 2 < j)%N by rewrite ltn_subrL /= (ltn_trans _ Hj3').
  by rewrite Heq ltnn.
have Hbgs_jm2' : bgs ((j : nat) - 2)%N =
  f_recv (e_loc (enc (ek j.-1) (chain_acc_local ((j : nat) - 3)) (rp_rr_fw rp))).
  by rewrite /bgs -Hbgs_jm2.
rewrite Hbgs_jm2' Hf_recv_eq /=.
rewrite nth_cons_pos; last by exact (ltn_trans (ltn0Sn _) Hj3').
rewrite (nth_map 0); last first.
  by rewrite size_iota; apply (leq_ltn_trans (leq_pred _) (ltn_ord _)).
rewrite nth_iota; last by apply (leq_ltn_trans (leq_pred _) (ltn_ord _)).
rewrite add0n.
have -> : (j.-1 == j :> nat) = false.
  apply /eqP => H.
  have : (j.-1 < j)%N by rewrite ltn_predL (ltn_trans _ Hj3').
  by rewrite H ltnn.
have Hbgs_jm1' : bgs j.-1 = rp_bg rp j.-1 by rewrite /bgs.
rewrite Hbgs_jm1' Hbg_jm1 /=.
(* Algebraic identity: Emul + chain_acc *)
rewrite /alice_enc_local Halice.
have Hek_eq : ek ((inord j.-1 : 'I_n_relay.+1) : nat).+1 = ek j.
  congr ek. rewrite inordK; first by rewrite prednK // (ltn_trans _ Hj3').
  by rewrite (leq_ltn_trans (leq_pred _) (ltn_ord _)).
rewrite Hek_eq.
rewrite !enc_curry_eq -(@Emul_addM AHE).
rewrite /mr_bop /=.
congr (Send _ _ Finish).
congr (e_loc _).
congr (E[ _] _).
congr ( _, _).
have Hjm2_pred : ((j : nat) - 2)%N = ((j : nat) - 3).+1.
  case: (j : nat) Hj3' => [|[|[|n']]] // _.
  by rewrite subSS subSS subSn // subn0.
rewrite /chain_acc_local Hjm2_pred /chain_acc -/chain_acc.
rewrite GRing.addrC.
congr (_ + _).
congr (term _ _ _ _).
apply val_inj => /=.
have Hjm1_lt : (j.-1 < n_relay.+1)%N := leq_ltn_trans (leq_pred _) (ltn_ord _).
have Hjm2_pred_lt : ((j - 3).+1 < n_relay.+1)%N.
  by rewrite -Hjm2_pred (leq_ltn_trans (leq_subr 2 _) (ltn_ord _)).
rewrite !inordK //.
- case: (j : nat) Hj3' => [|[|[|n']]] // _.
  by rewrite /= !subSS subn0.
- have -> : ((j : nat) - 3).+2 = j.-1.
    case: (j : nat) Hj3' => [|[|[|n']]] // _.
    by rewrite /= !subSS subn0.
  exact Hjm1_lt.
Qed.

(* H5: rp_sender2 — j+1=2 special case. New randomness from alice/r2 mix. *)
Lemma mk_next_sender2 (rp : recv_phase) (Hjn : (rp_j rp < n_relay)%N) :
  (next_j Hjn == 2%N :> nat) ->
  { rr_fw' : rand AHE | bg'_of rp 0 = Send 2
    (e_loc (@enc AHE (ek (nat_to_party_id 2))
                 (chain_acc_local 0) rr_fw')) Finish }.
Proof.
move=> Hj1.
have Hjz : (rp_j rp : nat) = 1%N.
  apply succn_inj.
  by rewrite -(eqP Hj1) /next_j inordK //; exact (ltn_trans Hjn (ltnSn _)).
have [rr_a Halice] := @alice_enc_value AHE ek n_relay u r rand_a v_relay r1_relay (rp_j rp).
exists (rand_mul rr_a (r2_relay ord0)).
have Hj_eq : (rp_j rp == 1%N :> nat) by rewrite Hjz.
have [f_enc [Hbg0 Hf_enc_eq]] := (rp_j1_recv rp) Hj_eq.
rewrite /bg'_of /=. set bgs := bg_s_of rp.
have Hbgs0 : bgs 0 = rp_bg rp 0.
  rewrite /bgs /bg_s_of /recv_procs_gen_local /recv_procs_gen /step /=.
  rewrite nth_mkseq; last by [].
  have -> : (0 == rp_j rp :> nat) = false by rewrite eq_sym Hjz.
  rewrite Hbg0 /=.
  have Halice_recv := @alice_body_at_recv AHE ek n_relay dk relays Hrelays
    Hrelays_id v0 u r rand_a (rp_j rp) (ltn_ord _).
  have [f_alice Halice_eq] := Halice_recv.
  by rewrite Halice_eq /=.
rewrite /send_procs_gen_local /send_procs_gen /step /=.
rewrite nth_mkseq; last by [].
have -> : (0 == rp_j rp :> nat) = false by rewrite eq_sym Hjz.
rewrite Hbgs0 Hbg0 /=.
have -> : alice_send_dest (rp_j rp) = 1 by rewrite /alice_send_dest /maxn Hjz.
rewrite eqxx /=.
rewrite Hf_enc_eq Halice.
have H2 : (rp_j rp).+1 = 2%N by rewrite Hjz.
rewrite H2 !enc_curry_eq -(@Emul_addM AHE).
rewrite /mr_bop /=.
have Hjeqi : rp_j rp = (inord 1 : 'I_n_relay.+1).
  apply val_inj => /=. by rewrite Hjz inordK.
by rewrite /term_local Hjeqi GRing.addrC.
Qed.

(* H6: rp_receiver — frontier receiver at (j+1)-2 *)
Lemma mk_next_receiver (rp : recv_phase) (Hjn : (rp_j rp < n_relay)%N) :
  let j' := next_j Hjn in
  (3 <= j')%N ->
  exists f_recv, bg'_of rp ((j' : nat) - 2)%N = Recv j'.-2 f_recv /\
  forall m rr,
    f_recv (e_loc (@enc AHE (ek (nat_to_party_id j'.-1)) m rr)) =
    Send j' (e_loc (@Emul AHE (alice_enc_local (inord j'.-1))
      (@enc AHE (ek (nat_to_party_id j')) m (r2_relay (inord ((j' : nat) - 2)%N)))))
    Finish.
Proof.
move=> /=.
set j := rp_j rp.
have Hinord : ((next_j Hjn : nat) = j.+1)%N by rewrite /next_j inordK.
rewrite Hinord => Hj3.
have Hj2 : (1 < j)%N by exact Hj3.
have Hj1pos : (0 < j)%N := ltnW Hj2.
have [sv0 [f0 [Hbody Hbg]]] := (rp_behind rp) Hj2.
have Hsub : (j.+1 - 2 = j.-1)%N by rewrite subSS subn1.
have Hpred : j.+1.-2 = j.-1 by rewrite -subn2 subSS subn1.
rewrite Hsub Hpred.
have Hjm1 : (j.-1 < n_relay.+1)%N by apply (leq_ltn_trans (leq_pred _) (ltn_ord _)).
have Hjm1_ne : j.-1 != (j : nat).
  apply /eqP => Habs.
  have : (j.-1 < j)%N by rewrite ltn_predL.
  by rewrite Habs ltnn.
have Hbg_s_jm1 : (step (recv_procs_gen ek dk dk_relay relays v0 u r rand_a
    v_relay r1_relay r2_relay j (rp_bg rp)) [::] j.-1.+1).1.1 = Recv 0 f0.
  by apply: bg_recv0_nop_recv Hbg.
have Hadt : alice_send_dest j = j.-1.+1.
  rewrite /alice_send_dest /maxn.
  case: ltnP => H; first by rewrite prednK.
  have Habs : j = 1 :> nat by apply anti_leq; rewrite Hj1pos H.
  by rewrite Habs in Hj2.
have Hbg' : bg'_of rp j.-1 = f0 (e_loc (alice_enc ek u r rand_a v_relay r1_relay j)).
  rewrite /bg'_of /bg_s_of /send_procs_gen_local /recv_procs_gen_local /=.
  set bg_s_local := (fun i => _).
  have Hbg_s_local : bg_s_local j.-1 = Recv 0 f0 by exact Hbg_s_jm1.
  by apply: bg_recv0_fire_send Hbg_s_local _.
have Hjm1_pos : (0 < j.-1)%N by rewrite -subn1 subn_gt0.
have Hjm1_lt : (j.-1 < n_relay)%N by rewrite -ltnS prednK //; exact (ltn_trans Hjn (ltnSn _)).
have Hjm1_inord : ((inord j.-1 : 'I_n_relay.+1) : nat) = j.-1
  by rewrite inordK //; exact (ltnW Hjm1_lt).
have Hjm1_ne0 : ((inord j.-1 : 'I_n_relay.+1) : nat) != 0%N by rewrite Hjm1_inord -lt0n.
have Hjm1_ne_n : ((inord j.-1 : 'I_n_relay.+1) : nat) != n_relay
  by rewrite Hjm1_inord; apply /eqP => Habs; rewrite Habs ltnn in Hjm1_lt.
rewrite /relay_body_local /relay_body in Hbody.
rewrite (negbTE Hjm1_ne0) (negbTE Hjm1_ne_n) Hjm1_inord in Hbody.
move: Hbody. rewrite /alice_idx. case=> _ Hf0_eq.
rewrite /std_Recv_enc /Recv_param in Hf0_eq.
have Hf0_apply : forall c, f0 (e_loc c) =
  std_Recv_dec j.-1 (dk_relay (inord (rp_j rp).-1))
    (fun m0 => Send j.-1.+2 (e_loc (Emul c (enc (ek (nat_to_party_id j.-1.+2)) m0
                                                (r2_relay (inord (rp_j rp).-1))))) Finish).
  move=> c. rewrite -Hf0_eq /=. rewrite /e_loc /std_from_enc /=.
  reflexivity.
rewrite Hbg' Hf0_apply.
rewrite /std_Recv_dec /Recv_param /=.
eexists. split.
- reflexivity.
- move=> m rr.
  rewrite /= /std_from_enc /=.
  have Hkr := key_relay (inord (rp_j rp).-1).
  rewrite /j Hjm1_inord prednK // in Hkr.
  rewrite -/j in Hkr.
  rewrite Hkr dec_correct /=.
  have Hjp : j.-1.+2 = j.+1 by rewrite (prednK Hj1pos).
  rewrite Hjp.
  congr (Send _ (e_loc (Emul _ (enc _ _ _))) Finish).
  + rewrite /alice_enc_local.
    have -> : (inord j : 'I_n_relay.+1) = j by apply val_inj; rewrite /= inordK.
    by [].
  + case Hjval : (j : nat) => [|[|jv]] //=.
    by rewrite Hjval in Hj2.
Qed.

(* H7: rp_j1_recv — j+1=1 special case *)
Lemma mk_next_j1_recv (rp : recv_phase) (Hjn : (rp_j rp < n_relay)%N) :
  (next_j Hjn == 1%N :> nat) ->
  exists f_enc, bg'_of rp 0 = Recv 0 (oapp f_enc Fail \o @std_from_enc AHE) /\
  forall c, f_enc c = Send 2
    (e_loc (@Emul AHE c (@enc AHE (ek (nat_to_party_id 2))
                               (term_local ord0) (r2_relay ord0)))) Finish.
Proof.
move=> Hj1.
have Hjz : (rp_j rp : nat) = 0%N.
  apply succn_inj.
  by rewrite -(eqP Hj1) /next_j inordK //; exact (ltn_trans Hjn (ltnSn _)).
have [f_ras Hras] := @relay_after_send0_recv0 AHE ek n_relay dk_relay v_relay
  r1_relay r2_relay (rp_j rp) Hjn.
rewrite /bg'_of /=. set bgs := bg_s_of rp.
rewrite /send_procs_gen_local /send_procs_gen /step /=.
rewrite nth_mkseq; last by [].
rewrite Hjz eqxx /=.
have Hinord_zero : (inord 0 : 'I_n_relay.+1) = rp_j rp.
  apply val_inj => /=. by rewrite Hjz inordK.
rewrite Hinord_zero Hras /=.
move: Hras. rewrite /relay_after_send0 Hjz /=.
rewrite /std_Recv_dec /Recv_param /=.
case=> Hf_ras_eq.
rewrite -Hf_ras_eq /=.
have [rr_a Halice] := @alice_enc_value AHE ek n_relay u r rand_a v_relay
  r1_relay (rp_j rp).
rewrite Halice.
have Hkey := @key_relay (rp_j rp).
rewrite Hkey dec_correct /=.
rewrite /std_Recv_enc /Recv_param /=.
have Hjord : rp_j rp = (ord0 : 'I_n_relay.+1) by apply val_inj.
rewrite Hjord.
eexists. split; first reflexivity. by [].
Qed.

(* mk_recv_next_exists: construct recv_phase at j+1 from recv_phase at j.
   Requires j < n_relay so there is a next relay to step into.
   The new rp_rr_fw is freshly chosen from the active mk_next_sender/sender2
   existential (only one applies at a time, based on next_j's value). *)
Lemma mk_recv_next_exists (rp : recv_phase) (Hjn : (rp_j rp < n_relay)%N) :
  exists rp' : recv_phase,
    rp_j rp' = next_j Hjn /\ rp_bg rp' = bg'_of rp.
Proof.
(* Case-split on next_j to choose the right rr_fw' *)
case: (boolP ((next_j Hjn : nat) == 2%N)) => [Hnj2 | Hnne].
  (* next_j = 2: use mk_next_sender2 *)
  have [rr_fw' Hrr] := @mk_next_sender2 rp Hjn Hnj2.
  refine (ex_intro _ (@MkRecvPhase AHE ek n_relay dk_relay u r rand_a v_relay r1_relay r2_relay (next_j Hjn) rr_fw' (bg'_of rp)
    _ _ _ _ _ _ _) (conj erefl erefl)).
  - move=> i Hij Hi.
    have Hinord : (next_j Hjn : nat) = (rp_j rp).+1 by rewrite /next_j inordK.
    rewrite Hinord in Hij. exact: (mk_next_ahead Hjn Hij Hi).
  - exact (@mk_next_behind rp Hjn).
  - exact (@mk_next_finish rp Hjn).
  - move=> Hj3. by rewrite (eqP Hnj2) in Hj3.
  - move=> _. exact Hrr.
  - exact (@mk_next_receiver rp Hjn).
  - exact (@mk_next_j1_recv rp Hjn).
case: (boolP ((3 <= next_j Hjn)%N)) => [Hj3 | Hlt].
  (* next_j >= 3: use mk_next_sender *)
  have [rr_fw' Hrr] := @mk_next_sender rp Hjn Hj3.
  refine (ex_intro _ (@MkRecvPhase AHE ek n_relay dk_relay u r rand_a v_relay r1_relay r2_relay (next_j Hjn) rr_fw' (bg'_of rp)
    _ _ _ _ _ _ _) (conj erefl erefl)).
  - move=> i Hij Hi.
    have Hinord : (next_j Hjn : nat) = (rp_j rp).+1 by rewrite /next_j inordK.
    rewrite Hinord in Hij. exact: (mk_next_ahead Hjn Hij Hi).
  - exact (@mk_next_behind rp Hjn).
  - exact (@mk_next_finish rp Hjn).
  - move=> _. exact Hrr.
  - move=> /eqP H. by rewrite H in Hnne.
  - exact (@mk_next_receiver rp Hjn).
  - exact (@mk_next_j1_recv rp Hjn).
(* next_j = 1 (or 0, but 0 impossible since next_j > 0): use placeholder *)
refine (ex_intro _ (@MkRecvPhase AHE ek n_relay dk_relay u r rand_a v_relay r1_relay r2_relay (next_j Hjn) (rp_rr_fw rp) (bg'_of rp)
  _ _ _ _ _ _ _) (conj erefl erefl)).
- move=> i Hij Hi.
  have Hinord : (next_j Hjn : nat) = (rp_j rp).+1 by rewrite /next_j inordK.
  rewrite Hinord in Hij. exact: (mk_next_ahead Hjn Hij Hi).
- exact (@mk_next_behind rp Hjn).
- exact (@mk_next_finish rp Hjn).
- move=> Hj3. by rewrite Hj3 in Hlt.
- move=> /eqP H. by rewrite H in Hnne.
- exact (@mk_next_receiver rp Hjn).
- exact (@mk_next_j1_recv rp Hjn).
Qed.

(* L4: drain_phase_step — wraps step_ok_drain_drain_gen and rebuilds Record fields.
   PROOF SKETCH (~150 lines):
   1. Extract dp.(dp_sender), dp.(dp_finish), dp.(dp_last), dp.(dp_between).
   2. Get the active receiver f_act from dp_between at i=(dp_j dp).+1.
   3. Get the next receiver from dp_between at i=(dp_j dp).+2 (or dp_last if = n_relay).
   4. Discharge the NOP hypothesis: positions in [0..n_relay] except dp_j and (dp_j).+1
      are NOPs in the drain_procs_gen step. Sub-cases:
      - i < dp_j: dp_bg i = Finish (from dp_finish) → trivially NOP.
      - i = dp_j or i = (dp_j).+1: excluded by hypothesis.
      - (dp_j).+1 < i < n_relay: dp_bg i = Recv i f (from dp_between) — Recv at frm=i
        checks position i which is also a Recv (or Finish), not a Send → NOP.
      - i = n_relay: dp_bg n_relay = Recv n_relay f_last (from dp_last) — same NOP reasoning.
   5. Apply step_ok_drain_drain_gen with the discharged hypotheses to get rr', bg', Hsafe'
      and Hstep_eq : one_step_procs ... = ps_procs (drain_st (inord (dp_j dp).+1) ...).
   6. Build the new drain_phase' fields:
      - dp_j' = inord (dp_j dp).+1
      - dp_rr_drain' = rr'
      - dp_bg' = bg'
      - dp_safe' = Hsafe'
      - dp_j_lt': follows from Hjlt
      - dp_sender': bg' (dp_j' = (dp_j dp).+1) is computed from f_act fired with cipher_j;
        by Emul_addM + chain_acc_shift, equals Send (dp_j' .+2) (chain_acc(dp_j')) rr'
      - dp_finish': for i < (dp_j).+1, either i < dp_j (was Finish, NOP keeps Finish) or
        i = dp_j (sender fired to Finish per step_ok_drain_drain_gen's Hstepj proof)
      - dp_between': for (dp_j).+1 < i < n_relay, NOP keeps the Recv shape from old dp_between
      - dp_last': position n_relay was NOP, so unchanged from old dp_last
   7. Return the sig with Hstep_eq.

   OBSTACLES discovered during attempts:
   - Section-closed implicit args: every section-defined function (drain_procs_gen,
     step_ok_drain_drain_gen, etc.) takes 11+ section vars after closure. Must use
     @-form everywhere.
   - Record projections under `Set Implicit Arguments`: dp_safe has implicit `d`, so
     `dp_safe dp` parses as `dp_safe (d:=?) dp` putting dp in the wrong slot. Use
     `dp_safe dp` or the (d:=dp) named form.
   - The `is_nop` discharge for the new lemma's NOP hypothesis requires unfolding the
     drain_procs_gen at non-active positions and showing each Recv has frm pointing
     to a non-Send. This is ~30-50 lines of manual case analysis.
   - Reconstructing dp_sender' for the new phase requires knowing that
     bg' (dp_j).+1 = f_act cipher_j, then applying Hf_act + Emul_addM + chain_acc_shift.
     But step_ok_drain_drain_gen returns bg' as an OPAQUE (fun i => step ... i.+1).1.1,
     not exposing the per-position values. Need additional reasoning to extract them. *)
Lemma drain_phase_step (dp : drain_phase) :
  ((dp_j dp : nat).+1 < n_relay)%N ->
  { dp' : drain_phase |
    (dp_j dp' : nat) = (dp_j dp).+1 /\
    one_step_procs (ps_procs (drain_st (dp_j dp) (dp_rr_drain dp)
                                       (bg := dp_bg dp) (dp_safe dp))) =
    ps_procs (drain_st (dp_j dp') (dp_rr_drain dp')
                       (bg := dp_bg dp') (dp_safe dp')) }.
Proof.
move=> Hjlt.
set j := dp_j dp.
set rr := dp_rr_drain dp.
set bg := dp_bg dp.
have Hsafe : forall v k, bg n_relay <> Send 0 v k := dp_safe dp.
have Hjp1_lt_nrp1 : (j.+1 < n_relay.+1)%N by rewrite ltnS; exact: ltnW Hjlt.
have Hjp2_lt_nrp1 : (j.+2 < n_relay.+1)%N by rewrite ltnS; exact: Hjlt.
have Hj_lt_nr : (j < n_relay)%N by exact: ltnW Hjlt.
have Hsender : bg j = Send j.+2
    (e_loc (@enc AHE (ek (nat_to_party_id j.+2)) (chain_acc_local j) rr)) Finish
  := dp_sender dp.
have Hjp1_lt_nr : (j.+1 < n_relay)%N by exact Hjlt.
have [f_act [Hbg_act Hf_act]] := dp_between dp j.+1 (ltnSn _) Hjp1_lt_nr.
have Hinord_j2 : ((inord j.+2 : 'I_n_relay.+1) : nat) = j.+2 by rewrite inordK //.
have [rr0 Halice2] :=
  @alice_enc_value AHE ek n_relay u r rand_a v_relay r1_relay (inord j.+2).
have Hek_inord : ek (inord j.+2 : 'I_n_relay.+1).+1 = ek j.+3
  by congr ek; rewrite Hinord_j2.
have Hchain_step : chain_acc_local j.+1 = chain_acc_local j + term_local (inord j.+2).
  by rewrite /chain_acc_local /term_local /chain_acc -/chain_acc.
have Hbg_act_hyp : { f : data -> proc data & { rr_next : rand AHE |
   bg j.+1 = Recv j.+1 f /\
   f (e_loc (enc (ek (nat_to_party_id j.+2)) (chain_acc_local j) rr)) =
   Send j.+3
     (e_loc (enc (ek (nat_to_party_id j.+3)) (chain_acc_local j.+1) rr_next))
     Finish }}.
  exists f_act, (rand_mul rr0 (r2_relay (inord j.+1))).
  split; first by rewrite -/bg.
  rewrite (Hf_act (chain_acc_local j) rr).
  rewrite /alice_enc_local Halice2 Hek_inord.
  rewrite !enc_curry_eq -(@Emul_addM AHE).
  rewrite /mr_bop /=.
  congr (Send _ _ Finish).
  congr (e_loc _).
  congr (E[ _] _).
  congr ( _, _).
  by rewrite GRing.addrC.
have Hbg_next_hyp : { f_next : data -> proc data | bg j.+2 = Recv j.+2 f_next }.
  case: (ltnP j.+2 n_relay) => Hjp2cmp.
    have Hj_lt_jp2 : ((dp_j dp : nat) < j.+2)%N by rewrite -/j; exact: ltnW.
    have [f2 [Hbg_f2 _]] := dp_between dp j.+2 Hj_lt_jp2 Hjp2cmp.
    by exists f2; rewrite -/bg.
  have Hjp2_eq : j.+2 = n_relay
    by apply/eqP; rewrite eqn_leq Hjp2cmp andbT; exact Hjp2_lt_nrp1.
  have [f_last [Hbg_last _]] := dp_last dp.
  exists f_last. by rewrite Hjp2_eq -/bg.
have Hsafe_j : forall v k, bg j <> Send 0 v k.
  by move=> v k; rewrite Hsender.
have Hnop : forall i, (i < n_relay.+1)%N -> i != (j : nat) -> i != j.+1 ->
  is_nop (drain_procs_gen ek dk relays v0 u r rand_a v_relay j rr bg) i.+1.
  move=> i Hi Hneqj Hneqj1.
  have Hbgi_recv : (j < i)%N -> { ff | bg i = Recv i ff }.
    move=> Hji.
    case: (boolP (i == n_relay :> nat)) => [/eqP Hieq | Hin].
      have [f_l [Hbg_l _]] := dp_last dp.
      by exists f_l; rewrite Hieq.
    have Hilt : (i < n_relay)%N by rewrite ltn_neqAle Hin /=.
    have [f_b [Hbg_b _]] := dp_between dp i Hji Hilt.
    by exists f_b.
  rewrite /is_nop /drain_procs_gen /smc_interpreter.step /=.
  rewrite nth_mkseq; last exact Hi.
  rewrite (negbTE Hneqj) (negbTE Hneqj1).
  case: (ltnP i j) => Hij.
    have Hbgi_fin : bg i = Finish by exact: (dp_finish dp).
    by rewrite -/bg Hbgi_fin.
  have Hji : (j < i)%N
    by rewrite ltn_neqAle Hij andbT eq_sym; exact: Hneqj.
  have Hji1 : (j.+1 < i)%N
    by rewrite ltn_neqAle Hji andbT eq_sym; exact: Hneqj1.
  have [ff Hbgi] := Hbgi_recv Hji.
  rewrite -/bg Hbgi /=.
  have Hipos : (0 < i)%N by apply: leq_ltn_trans Hji; exact: leq0n.
  rewrite nth_cons_pos //.
  rewrite nth_mkseq; last exact: leq_ltn_trans (leq_pred _) Hi.
  have Hi_eq : i = (i.-1).+1 by rewrite prednK.
  have Hi1_neq_j : (i.-1 == (j : nat)) = false.
    apply/eqP => Habs.
    by move: Hji1; rewrite Hi_eq Habs ltnn.
  rewrite Hi1_neq_j.
  case: (boolP (i.-1 == j.+1)) => Hi1eq.
    have Hbgj1_recv : bg j.+1 = Recv j.+1 f_act by rewrite -/bg in Hbg_act.
    by rewrite Hbgj1_recv //.
  have Hji1_strict : (j.+1 < i.-1)%N.
    rewrite ltn_neqAle; apply/andP; split; first by rewrite eq_sym.
    by rewrite -ltnS -Hi_eq.
  have Hi1_lt : (i.-1 < n_relay.+1)%N by exact: leq_ltn_trans (leq_pred _) Hi.
  case: (boolP (i.-1 == n_relay :> nat)) => [/eqP Hi1n | Hi1n].
    have [f_l [Hbg_l _]] := dp_last dp.
    have Hbgi1eq : bg i.-1 = Recv n_relay f_l by rewrite Hi1n; exact Hbg_l.
    by rewrite Hbgi1eq.
  have Hi1_lt_nr : (i.-1 < n_relay)%N
    by rewrite ltn_neqAle Hi1n /=; rewrite -ltnS.
  have Hj_lt_i1 : ((dp_j dp : nat) < i.-1)%N by exact: ltn_trans Hji1_strict.
  have [f_b [Hbg_b _]] := dp_between dp i.-1 Hj_lt_i1 Hi1_lt_nr.
  have Hbgi1eq : bg i.-1 = Recv i.-1 f_b by exact Hbg_b.
  by rewrite Hbgi1eq.
have [rr' [bg' [Hsafe' [Hstep_eq [Hbgj_fin [Hbgj1_send Hnop_eq]]]]]] :=
  @step_ok_drain_drain_gen AHE ek n_relay dk relays Hrelays v0 u r rand_a
    v_relay j rr bg Hsafe Hjp2_lt_nrp1 Hbg_act_hyp Hbg_next_hyp Hsafe_j Hnop.
have Hjp1_lt_nrp1' : ((inord j.+1 : 'I_n_relay.+1).+1 < n_relay.+1)%N
  by rewrite (@inordK n_relay j.+1) //.
have Hinord_eq : ((inord j.+1 : 'I_n_relay.+1) : nat) = j.+1 by rewrite inordK.
have Hsender' : bg' (inord j.+1 : 'I_n_relay.+1) =
  Send (inord j.+1 : 'I_n_relay.+1).+2
    (e_loc (@enc AHE (ek (nat_to_party_id (inord j.+1 : 'I_n_relay.+1).+2))
                 (chain_acc_local (inord j.+1 : 'I_n_relay.+1)) rr')) Finish.
  by rewrite Hinord_eq Hbgj1_send.
have Hfinish' : forall i, (i < (inord j.+1 : 'I_n_relay.+1))%N -> bg' i = Finish.
  move=> i Hi.
  rewrite Hinord_eq in Hi.
  case: (boolP (i == (j : nat))) => [/eqP Hieq | Hineqj].
    by rewrite Hieq.
  have Hineqj1 : i != j.+1.
    apply/eqP => Habs.
    by move: Hi; rewrite Habs ltnn.
  have Hi_bound : (i < n_relay.+1)%N.
    apply: leq_trans (ltnW Hjp1_lt_nrp1).
    by rewrite -ltnS; exact: leq_trans Hi (ltnSn _).
  have Hbg_eq : bg' i = bg i by exact: Hnop_eq.
  rewrite Hbg_eq.
  have Hi_lt_j : (i < j)%N by rewrite ltn_neqAle Hineqj.
  by exact: (dp_finish dp).
have Hn_neq_j : (n_relay : nat) != j by rewrite eq_sym neq_ltn Hj_lt_nr.
have Hn_neq_j1 : (n_relay : nat) != j.+1 by rewrite eq_sym neq_ltn Hjlt.
have Hlast' : { f | bg' n_relay = Recv n_relay f /\
    forall m rr1, f (e_loc (@enc AHE (ek (nat_to_party_id n_relay.+1)) m rr1)) =
      Send 0 (e_loc (@enc AHE (ek alice_idx) m
        (r2_relay (inord n_relay)))) Finish }.
  have [f_l [Hbg_l Hf_l]] := dp_last dp.
  exists f_l. split; last exact Hf_l.
  have Hbgnl : bg n_relay = Recv n_relay f_l by exact Hbg_l.
  by rewrite Hnop_eq // Hbgnl.
have Hbetween' : forall i,
    ((inord j.+1 : 'I_n_relay.+1) < i)%N -> (i < n_relay)%N ->
    { f | bg' i = Recv i f /\
      forall m rr1, f (e_loc (@enc AHE (ek (nat_to_party_id i.+1)) m rr1)) =
        Send i.+2 (e_loc (@Emul AHE (alice_enc_local (inord i.+1))
          (@enc AHE (ek (nat_to_party_id i.+2)) m
            (r2_relay (inord i))))) Finish }.
  move=> i Hi1lt Hilt.
  rewrite Hinord_eq in Hi1lt.
  have Hi_bound : (i < n_relay.+1)%N by exact: ltnW.
  have Hi_neq_j : i != (j : nat).
    apply/eqP => Habs; subst i.
    by move: Hi1lt; rewrite ltnNge leqnSn.
  have Hi_neq_j1 : i != j.+1.
    apply/eqP => Habs; subst i.
    by move: Hi1lt; rewrite ltnn.
  have Hbgi_eq : bg' i = bg i by exact: Hnop_eq.
  have Hj_lt_i : ((dp_j dp : nat) < i)%N.
    rewrite -/j.
    by exact: ltn_trans Hi1lt.
  have [f_b [Hbg_b Hf_b]] := dp_between dp i Hj_lt_i Hilt.
  exists f_b. split; last exact Hf_b.
  have Hbgi : bg i = Recv i f_b by exact Hbg_b.
  by rewrite Hbgi_eq Hbgi.
refine (exist _ (@MkDrainPhase AHE ek n_relay u r rand_a v_relay r1_relay r2_relay (inord j.+1 : 'I_n_relay.+1) rr' bg' Hsafe'
  Hjp1_lt_nrp1' Hsender' Hfinish' Hlast' Hbetween') _).
simpl.
split; first by rewrite Hinord_eq.
exact Hstep_eq.
Qed.

(* L1: recv_phase_to_send_phase — one recv→send step produces a send_phase
   Record at the same j, using bg_s_of rp as the new bg. *)
Lemma recv_phase_to_send_phase (rp : recv_phase) :
  (2 <= rp_j rp)%N ->
  { sp : send_phase |
    (sp_j sp : nat) = (rp_j rp : nat) /\
    one_step_procs (ps_procs (recv_st (rp_j rp) (rp_bg rp))) =
    ps_procs (send_st (rp_j rp) (sp_bg sp)) }.
Proof.
move=> Hj2.
set j := rp_j rp.
set bg := rp_bg rp.
set bgs := bg_s_of rp.
have Hj_lt : (j < n_relay.+1)%N := ltn_ord _.
(* Step equation: concrete recv→send transition *)
have Hstep : one_step_procs (recv_procs_gen_local j bg) = send_procs_gen_local j bgs.
  by exact: step_ok_recv_send_concrete.
have Hjpos : (0 < j)%N := ltn_trans (ltn0Sn _) Hj2.
have Hjm1_ne : (j.-1 != (j : nat)).
  apply/eqP => H.
  have : (j.-1 < j)%N by rewrite ltn_predL.
  by rewrite H ltnn.
have Hjm1_lt : (j.-1 < n_relay.+1)%N
  by apply (leq_ltn_trans (leq_pred _) Hj_lt).
have Hjm1_lt_nr : (j.-1 < n_relay)%N.
  by rewrite prednK // -ltnS; exact: (ltn_trans Hj_lt (ltnSn _)).
have Hinord_jm1 : ((inord j.-1 : 'I_n_relay.+1) : nat) = j.-1 by rewrite inordK.
(* Field sp_active: Use relay_after_send0_recv0_sig to get a Type-level witness
   for f_ras, then use rp_behind (Prop) to bridge bg j.-1 = Recv 0 f_ras. *)
have [f_ras Hras_eq] := @relay_after_send0_recv0_sig (inord j.-1 : 'I_n_relay.+1)
  (eq_ind _ (fun n => (n < n_relay)%N) Hjm1_lt_nr _ (esym Hinord_jm1)).
have Hsp_active : { sv0_f0 : data * (data -> proc data) |
    relay_body_local (inord j.-1) = Send 0 sv0_f0.1 (Recv 0 sv0_f0.2) /\
    bgs j.-1 = Recv 0 sv0_f0.2 }.
  exists (e_loc (enc (ek (nat_to_party_id (inord j.-1 : 'I_n_relay.+1).+1))
                 (v_relay (inord j.-1 : 'I_n_relay.+1))
                 (r1_relay (inord j.-1 : 'I_n_relay.+1))), f_ras).
  split.
  { rewrite /relay_body_local
      (@relay_body_send0_cont AHE ek n_relay dk_relay v_relay r1_relay r2_relay (inord j.-1))
      Hras_eq.
    by []. }
  simpl.
  (* Derive bg j.-1 = Recv 0 f_ras by matching Prop rp_behind with our f_ras. *)
  have Hbg_jm1_eq : bg j.-1 = Recv 0 f_ras.
  { have [sv0 [f0 [Hbody0 Hbg0]]] := (rp_behind rp) Hj2.
    rewrite /relay_body_local in Hbody0.
    rewrite (@relay_body_send0_cont AHE ek n_relay dk_relay v_relay r1_relay r2_relay (inord j.-1))
      Hras_eq in Hbody0.
    case: Hbody0 => _ Heq_f.
    rewrite /bg Hbg0. by rewrite Heq_f. }
  rewrite /bgs /bg_s_of /recv_procs_gen_local -/j -/bg.
  by apply: bg_recv0_nop_recv Hbg_jm1_eq.
(* Field sp_ahead *)
have Hsp_ahead : forall i, (j < i)%N -> (i < n_relay.+1)%N ->
    bgs i = relay_body_local (inord i).
  move=> i Hji Hi.
  rewrite /bgs /bg_s_of /recv_procs_gen_local -/j -/bg.
  apply bg_relay_ahead_recv => //.
  exact: (rp_ahead rp Hji Hi).
(* Field sp_next_behind: j < n_relay case *)
have Hsp_next_behind : (j < n_relay)%N ->
  { sv_f : data * (data -> proc data) |
    relay_body_local (inord j) = Send 0 sv_f.1 (Recv 0 sv_f.2) /\
    bgs j = Recv 0 sv_f.2 }.
  move=> Hjn.
  have Hinord_j : ((inord j : 'I_n_relay.+1) : nat) = j by rewrite inordK //.
  have Hjn_inord : ((inord j : 'I_n_relay.+1) < n_relay)%N by rewrite Hinord_j.
  have [f_ras2 Hras2_eq] := @relay_after_send0_recv0_sig (inord j : 'I_n_relay.+1) Hjn_inord.
  exists (e_loc (enc (ek (nat_to_party_id (inord j : 'I_n_relay.+1).+1))
                 (v_relay (inord j : 'I_n_relay.+1))
                 (r1_relay (inord j : 'I_n_relay.+1))), f_ras2).
  simpl.
  split.
  { rewrite /relay_body_local
      (@relay_body_send0_cont AHE ek n_relay dk_relay v_relay r1_relay r2_relay (inord j))
      Hras2_eq.
    by []. }
  rewrite /bgs /bg_s_of /recv_procs_gen_local -/j -/bg
          /recv_procs_gen /smc_interpreter.step /=.
  rewrite nth_mkseq; last exact Hj_lt.
  rewrite eqxx.
  rewrite (@relay_body_send0_cont AHE ek n_relay dk_relay v_relay r1_relay r2_relay (inord j))
          Hras2_eq /=.
  have [f_alice Halice_eq] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays
    Hrelays_id v0 u r rand_a j Hj_lt.
  rewrite Halice_eq /=.
  by rewrite eqxx.
(* Field sp_last: j = n_relay case *)
have Hsp_last : ((j : nat) = n_relay) ->
  { f_dec | bgs n_relay = Recv n_relay f_dec /\
    forall m rr, f_dec (e_loc (@enc AHE (ek (nat_to_party_id n_relay.+1)) m rr)) =
      Send 0 (e_loc (@enc AHE (ek alice_idx) m
        (r2_relay (inord n_relay)))) Finish }.
  move=> Hjn.
  (* Helper: show bgs n_relay = relay_after_send0 j for any resulting f_dec
     that matches the relay_after_send0 body shape. *)
  have Hbgs_last_fn : forall f_dec,
    relay_after_send0 ek dk_relay v_relay r1_relay r2_relay j = Recv n_relay f_dec ->
    bgs n_relay = Recv n_relay f_dec.
  { move=> f_dec Hrs_eq.
    rewrite -Hjn.
    rewrite /bgs /bg_s_of /recv_procs_gen_local -/j -/bg
            /recv_procs_gen /smc_interpreter.step /=.
    rewrite nth_mkseq; last exact Hj_lt.
    rewrite eqxx.
    have Hinord_j_val : (inord j : 'I_n_relay.+1) = j by apply val_inj; rewrite /= inordK.
    rewrite (@relay_body_send0_cont AHE ek n_relay dk_relay v_relay r1_relay r2_relay (inord j)) /=.
    have [f_alice Halice_eq] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays
      Hrelays_id v0 u r rand_a j Hj_lt.
    rewrite Halice_eq /=.
    rewrite Hinord_j_val Hrs_eq /=.
    rewrite eqxx /=.
    by rewrite Hjn. }
  eexists.
  split.
  { apply Hbgs_last_fn.
    rewrite /relay_after_send0.
    have -> : ((j : nat) == 0) = false.
      by apply/eqP => H; rewrite H in Hj2.
    have -> : ((j : nat) == n_relay) by apply/eqP; exact Hjn.
    rewrite /std_Recv_dec /Recv_param /=.
    rewrite Hjn.
    reflexivity. }
  move=> m rr.
  rewrite /= /std_from_enc /=.
  have Hkr : ek n_relay.+1 = pub_of_priv (dk_relay j).
    rewrite -Hjn. exact: (key_relay j).
  rewrite Hkr dec_correct /=.
  have Hj_inord : j = inord n_relay :> 'I_n_relay.+1.
    apply val_inj => /=. by rewrite inordK // Hjn.
  by rewrite Hj_inord.
(* Field sp_sender2: j = 2 case — inherits from rp_sender2 via NOP *)
have Hsp_sender2 : (j == 2%N :> nat) ->
  bgs 0 = Send 2
    (e_loc (@enc AHE (ek (nat_to_party_id 2)) (chain_acc_local 0) (rp_rr_fw rp))) Finish.
  move=> Hj2eq.
  have Hbg0 : bg 0 = Send 2 (e_loc (enc (ek 2%N) (chain_acc_local 0) (rp_rr_fw rp))) Finish.
    rewrite /bg. exact: (rp_sender2 rp Hj2eq).
  have Hjz : (j : nat) = 2%N by exact (eqP Hj2eq).
  rewrite /bgs /bg_s_of /recv_procs_gen_local -/j -/bg
          /recv_procs_gen /smc_interpreter.step /=.
  rewrite nth_mkseq; last exact (ltn0Sn _).
  have -> : (0 == j :> nat) = false by rewrite eq_sym Hjz.
  rewrite Hbg0 /=.
  have [sv0_b [f_beh' [_ Hbg_beh']]] := (rp_behind rp) Hj2.
  have Hjm1z : (j.-1 = 1%N) by rewrite Hjz.
  rewrite Hjm1z in Hbg_beh'.
  have Hbg1 : bg 1 = Recv 0 f_beh' by rewrite /bg.
  rewrite (nth_map 0); last by rewrite size_iota.
  rewrite nth_iota // add1n.
  have -> : (1%N == j :> nat) = false by rewrite eq_sym Hjz.
  rewrite Hbg1 /=.
  by [].
(* Now case-split on (j = 2) vs (3 ≤ j) to pick sp_rr_fw *)
case: (boolP ((j : nat) == 2%N)) => [Hj2eq | Hjne2].
  (* j = 2: sp_rr_fw := rp_rr_fw rp *)
  have Hsp_sender_vac : (3 <= j)%N ->
    (forall i, (i.+3 <= j)%N -> bgs i = Finish) /\
    bgs ((j : nat) - 2)%N = Send j
      (e_loc (@enc AHE (ek (nat_to_party_id j)) (chain_acc_local ((j : nat) - 2)%N) (rp_rr_fw rp))) Finish.
    move=> Hj3. exfalso. move/eqP: Hj2eq => Hjz. by rewrite Hjz in Hj3.
  refine (exist _ (@MkSendPhase AHE ek n_relay dk_relay u r v_relay r1_relay r2_relay j (rp_rr_fw rp) bgs Hj2 Hsp_active
    Hsp_ahead Hsp_next_behind Hsp_last Hsp_sender2 Hsp_sender_vac) _).
  split; first by [].
  exact Hstep.
(* j != 2, so j ≥ 3 *)
have Hj3 : (3 <= j)%N.
  rewrite ltn_neqAle Hj2 andbT eq_sym. exact Hjne2.
(* Build the fresh sp_rr_fw from alice_enc_value *)
have [rr_a Halice] := @alice_enc_value AHE ek n_relay u r rand_a v_relay r1_relay (inord j.-1).
pose sp_rr := rand_mul rr_a (r2_relay (inord ((j : nat) - 2)%N)).
(* sp_sender2 vacuous: j != 2 *)
have Hsp_sender2_vac : (j == 2%N :> nat) ->
  bgs 0 = Send 2
    (e_loc (@enc AHE (ek (nat_to_party_id 2)) (chain_acc_local 0) sp_rr)) Finish.
  move=> Habs. by rewrite Habs in Hjne2.
(* sp_sender: at j-2, shifted sender; Finish zone at i.+3 ≤ j
   Note: rp_receiver is Prop-level exists, so we can only destructure it
   inside Prop-level sub-goals (Hsp_sender_fin, Hsp_sender_snd). *)
have Hsnd : bg ((j : nat) - 3)%N = Send j.-1
    (e_loc (@enc AHE (ek (nat_to_party_id j.-1)) (chain_acc_local ((j : nat) - 3)) (rp_rr_fw rp))) Finish.
  rewrite /bg. exact: (rp_sender rp Hj3).
have Hsp_sender_fin : forall i, (i.+3 <= j)%N -> bgs i = Finish.
  move=> i Hi3.
  have Hij : (i < j)%N by apply: ltn_trans Hi3; apply ltnW; rewrite ltnS.
  have Hi_ne_j : (i != (j : nat)) by rewrite neq_ltn Hij.
  have Hi_bound : (i < n_relay.+1)%N := ltn_trans Hij Hj_lt.
  case: (boolP (i.+2 == j.-1 :> nat)) => [Hieq | Hi_ne].
  + (* Border: i = j - 3 *)
    have Hi_eq : i = ((j : nat) - 3)%N.
      have Hj_val : (j : nat) = i.+3.
        have Hjm1_eq : j.-1 = i.+2 by move/eqP: Hieq => ->.
        by rewrite -(prednK Hjpos) Hjm1_eq.
      rewrite Hj_val. by rewrite !subSS subn0.
    rewrite Hi_eq /bgs /bg_s_of /recv_procs_gen_local -/j -/bg.
    have [f_recv [Hrcv _]] := (rp_receiver rp) Hj3.
    rewrite -/j in Hrcv.
    exact: bg_frontier_sender_fires Hsnd Hrcv.
  + (* Deep: i.+2 < j.-1, use rp_finish *)
    have Hi2_le_jm1 : (i.+2 <= j.-1)%N.
      rewrite -ltnS prednK; last by apply: (ltn_trans _ Hj3).
      exact Hi3.
    have Hi2_lt_jm1 : (i.+2 < j.-1)%N by rewrite ltn_neqAle Hi_ne.
    have Hjm2p1 : (j.-2).+1 = j.-1.
      by case: (j : nat) Hj3 => [|[|[|jv]]] //= _.
    have Hi1_lt_jm2 : (i.+1 < j.-2)%N.
      by rewrite -(ltn_add2r 1) !addn1 Hjm2p1.
    have Hbgi : bg i = Finish by apply: (rp_finish rp).
    rewrite /bgs /bg_s_of /recv_procs_gen_local -/j -/bg.
    by apply: bg_finish_nop_recv Hbgi.
have Hsp_sender_snd : bgs ((j : nat) - 2)%N = Send j
    (e_loc (@enc AHE (ek (nat_to_party_id j)) (chain_acc_local ((j : nat) - 2)%N) sp_rr)) Finish.
  have [f_recv [Hrcv Hf_recv_eq]] := (rp_receiver rp) Hj3.
  rewrite -/j in Hrcv Hf_recv_eq.
  have Hbgs_jm2 : bgs ((j : nat) - 2)%N =
    f_recv (e_loc (enc (ek j.-1) (chain_acc_local ((j : nat) - 3)) (rp_rr_fw rp))).
    rewrite /bgs /bg_s_of /recv_procs_gen_local -/j -/bg.
    exact: bg_frontier_receiver_fires Hsnd Hrcv.
  rewrite Hbgs_jm2 Hf_recv_eq.
  (* Algebraic identity: Emul + chain_acc shift *)
  rewrite /alice_enc_local Halice.
  have Hek_eq : ek ((inord j.-1 : 'I_n_relay.+1) : nat).+1 = ek j.
    congr ek. rewrite inordK; first by rewrite prednK // (ltn_trans _ Hj3).
    by rewrite (leq_ltn_trans (leq_pred _) Hj_lt).
  rewrite Hek_eq.
  rewrite !enc_curry_eq -(@Emul_addM AHE).
  rewrite /mr_bop /=.
  congr (Send _ _ Finish).
  congr (e_loc _).
  congr (E[ _] _).
  congr ( _, _).
  have Hjm2_pred : ((j : nat) - 2)%N = ((j : nat) - 3).+1.
    case: (j : nat) Hj3 => [|[|[|n']]] // _.
    by rewrite subSS subSS subSn // subn0.
  rewrite /chain_acc_local Hjm2_pred /chain_acc -/chain_acc.
  rewrite GRing.addrC.
  congr (_ + _).
  congr (term _ _ _ _).
  apply val_inj => /=.
  have Hjm1_lt' : (j.-1 < n_relay.+1)%N
    := leq_ltn_trans (leq_pred _) Hj_lt.
  have Hjm2_pred_lt : ((j - 3).+1 < n_relay.+1)%N.
    by rewrite -Hjm2_pred (leq_ltn_trans (leq_subr 2 _) Hj_lt).
  rewrite !inordK //.
  - case: (j : nat) Hj3 => [|[|[|n']]] // _.
    by rewrite /= !subSS subn0.
  - have -> : ((j : nat) - 3).+2 = j.-1.
      case: (j : nat) Hj3 => [|[|[|n']]] // _.
      by rewrite /= !subSS subn0.
    exact Hjm1_lt'.
have Hsp_sender : (3 <= j)%N ->
  (forall i, (i.+3 <= j)%N -> bgs i = Finish) /\
  bgs ((j : nat) - 2)%N = Send j
    (e_loc (@enc AHE (ek (nat_to_party_id j)) (chain_acc_local ((j : nat) - 2)%N) sp_rr)) Finish.
  by move=> _; split; [exact: Hsp_sender_fin | exact: Hsp_sender_snd].
refine (exist _ (@MkSendPhase AHE ek n_relay dk_relay u r v_relay r1_relay r2_relay j sp_rr bgs Hj2 Hsp_active
  Hsp_ahead Hsp_next_behind Hsp_last Hsp_sender2_vac Hsp_sender) _).
split; first by [].
exact Hstep.
Qed.

(* L2: send_phase_to_drain_phase_last
   At j = n_relay (with n_relay >= 3), the send_phase advances to a drain_phase
   at index n_relay - 2.  The active firing pair is Alice (Send n_relay)
   and bg(n_relay - 1) (Recv 0 f0).  All other positions are NOPs:
   - bg(i) = Finish for i < n_relay - 2 (from sp_sender Finish zone).
   - bg(n_relay - 2) = Send n_relay ... Finish (frontier sender, NOP because
     its target n_relay = bg(n_relay - 1) is a Recv 0, frm 0 != n_relay - 1).
   - bg(n_relay) is replaced by relay_after_send0(inord n_relay) inside
     send_procs_gen; it is a Recv n_relay ..., NOP.
   Resulting bg':
   - bg'(n_relay - 1) = f0 (e_loc (alice_enc n_relay)) which is the
     decryption Recv (n_relay - 1) producing Send (n_relay + 1) (Emul ...) Finish.
   - all other bg' positions match either bg or relay_after_send0(inord n_relay). *)
Lemma send_phase_to_drain_phase_last (sp : send_phase) :
  (sp_j sp : nat) = n_relay ->
  (3 <= n_relay)%N ->
  { dp : drain_phase |
    (dp_j dp : nat) = (n_relay - 2)%N /\
    one_step_procs (ps_procs (send_st (sp_j sp) (sp_bg sp))) =
    ps_procs (drain_st (dp_j dp) (dp_rr_drain dp) (bg := dp_bg dp) (dp_safe dp)) }.
Proof.
move=> Hjn Hnr3.
set j := sp_j sp.
set bg := sp_bg sp.
set rr := sp_rr_fw sp.
set bgs := fun i => (smc_interpreter.step (send_procs_gen_local j bg) [::] i.+1).1.1.
have Hj_lt : (j < n_relay.+1)%N := ltn_ord _.
have Hj3 : (3 <= j)%N by rewrite -/j Hjn.
have Hj2 : (2 <= j)%N := ltnW Hj3.
have Hjpos : (0 < j)%N := ltn_trans (ltn0Sn _) Hj2.
have Hnrpos : (0 < n_relay)%N := Hn_relay.
have [[sv0 f0] [Hbody0 Hbg_jm1]] := sp_active sp.
simpl in Hbody0, Hbg_jm1.
have [f_dec [Hbg_n Hf_dec_eq]] := sp_last sp Hjn.
have [Hsp_fin Hsp_snd] := sp_sender sp Hj3.
(* The drain index n_relay - 2 fits inside 'I_n_relay.+1 *)
have Hjpred_lt : ((n_relay - 2)%N < n_relay.+1)%N
  by apply (leq_ltn_trans (leq_subr _ _)); exact: ltnSn.
have Hjpred_succ_lt : (((n_relay - 2)%N).+1 < n_relay.+1)%N.
  rewrite ltnS subnS prednK; first by exact: leq_subr.
  by rewrite subn_gt0; exact: (ltnW Hnr3).
(* Active receiver fact: alice_send_dest j = n_relay = (j-1)+1, so f0 fires *)
have Hadt : alice_send_dest j = n_relay.
  rewrite /alice_send_dest /maxn -/j Hjn.
  case: ltnP => H //.
  by apply anti_leq; rewrite Hnrpos H.
have Hjm1_lt : (j.-1 < n_relay.+1)%N
  by apply (leq_ltn_trans (leq_pred _) Hj_lt).
have Hjm1_ne : j.-1 != (j : nat).
  apply/eqP => H. have : (j.-1 < j)%N by rewrite ltn_predL.
  by rewrite H ltnn.
have Hjm1_lt_n : (j.-1 < n_relay)%N.
  apply (@leq_trans (j : nat)); first by rewrite ltn_predL.
  by rewrite Hjn.
have Hjm1_ne_n : (j.-1 != n_relay :> nat).
  by rewrite neq_ltn Hjm1_lt_n.
have Hadt_jm1 : alice_send_dest j = j.-1.+1.
  rewrite Hadt. transitivity (j : nat); first by [].
  by rewrite (prednK Hjpos).
have Hbgs_jm1 : bgs j.-1 = f0 (e_loc (alice_enc_local j)).
  rewrite /bgs /send_procs_gen_local.
  apply: bg_recv0_fire_send Hjm1_lt Hjm1_ne Hbg_jm1 Hadt_jm1.
(* Unfold f0 from the relay_body (intermediate position) *)
have Hjm1_inord : ((inord j.-1 : 'I_n_relay.+1) : nat) = j.-1.
  apply inordK. by apply: leq_trans Hjm1_lt (leqnn _).
have Hjm1_pos : (0 < j.-1)%N by rewrite -subn1 subn_gt0.
have Hjm1_ne0 : ((inord j.-1 : 'I_n_relay.+1) : nat) != 0%N
  by rewrite Hjm1_inord -lt0n.
have Hjm1_ne_n_inord : ((inord j.-1 : 'I_n_relay.+1) : nat) != n_relay
  by rewrite Hjm1_inord.
rewrite /relay_body_local /relay_body in Hbody0.
rewrite (negbTE Hjm1_ne0) (negbTE Hjm1_ne_n_inord) Hjm1_inord in Hbody0.
case: Hbody0 => _ Hf0_eq.
have Hjm1S : (j.-1).+1 = j by rewrite (prednK Hjpos).
(* Finish zone for bgs *)
have Hbgs_finish : forall i, (i.+2 < j)%N -> bgs i = Finish.
  move=> i Hi.
  have Hbgi : bg i = Finish by rewrite /bg; exact: (Hsp_fin i Hi).
  have Hi_lt : (i < n_relay.+1)%N.
    apply: ltn_trans Hj_lt. apply: ltn_trans Hi. by rewrite ltnS leqnSn.
  have Hi_ne : i != (j : nat).
    apply/eqP => Heq. rewrite Heq in Hi.
    by move: Hi; rewrite ltnNge => /negP; apply; rewrite ltnW // ltnW.
  rewrite /bgs /send_procs_gen_local.
  by apply: bg_finish_nop_send Hi_lt Hi_ne Hbgi.
(* H1 (DONE): bgs (j - 2) is a Send n_relay ... Finish. The background bg has
   Send j v Finish at position j-2 (from sp_sender); in send_procs_gen, position
   j-2 steps a Send to dst = j. nth sp j = bg(j-1) = Recv 0 f0 (from sp_active)
   which is a Recv from frm=0. Since frm=0 != (j-2)+1 = j-1 (because j >= 3),
   the Send is NOP and the result equals bg(j-2) unchanged. *)
have Hj2_lt : ((j : nat) - 2 < n_relay.+1)%N
  by apply: (leq_ltn_trans (leq_subr _ _)); exact Hj_lt.
have Hj2_ne : (((j : nat) - 2)%N != (j : nat)).
  apply/eqP => H.
  have Hjgt : ((j : nat) - 2 < j)%N by rewrite ltn_subrL.
  by rewrite H ltnn in Hjgt.
have Hbg_jm2 : bg ((j:nat) - 2)%N = Send j
    (e_loc (@enc AHE (ek (nat_to_party_id j)) (chain_acc_local ((j:nat) - 2)%N) rr)) Finish.
  by rewrite /bg /rr; exact: Hsp_snd.
have Hbgs_snd_eq : bgs ((j : nat) - 2)%N = Send j
    (e_loc (@enc AHE (ek (nat_to_party_id j)) (chain_acc_local ((j:nat) - 2)%N) rr)) Finish.
  rewrite /bgs /send_procs_gen_local /send_procs_gen /smc_interpreter.step /=.
  rewrite nth_mkseq; last exact Hj2_lt.
  rewrite (negbTE Hj2_ne).
  rewrite Hbg_jm2 /=.
  rewrite nth_cons_pos //.
  rewrite nth_mkseq //.
  have Hj1nej : (j.-1 == (j : nat)) = false.
    by apply negbTE; rewrite neq_ltn ltn_predL Hjpos.
  rewrite Hj1nej.
  have -> : bg j.-1 = Recv 0 f0 by rewrite /bg; exact: Hbg_jm1.
  by [].
(* H2 (DONE): bgs n_relay = Recv n_relay f_n for some f_n. The background at
   position n_relay in send_procs_gen is REPLACED by relay_after_send0 (inord n_relay)
   (since the send_procs_gen does `if i == j then relay_after_send0 ...`). With
   j = n_relay and inord n_relay = n_relay, relay_after_send0 expands to
   std_Recv_dec n_relay ... which is Recv n_relay f_n. This Recv is a NOP in the
   step because its frm (n_relay) looks at bg(n_relay-1) = Recv 0 f0, which is
   not a Send, so the Recv is preserved unchanged. *)
have Hinord_n : ((inord n_relay : 'I_n_relay.+1) : nat) = n_relay
  by rewrite inordK // ltnSn.
have Hras_n_sig : { f' | relay_after_send0 ek dk_relay v_relay r1_relay r2_relay (inord n_relay : 'I_n_relay.+1) = Recv n_relay f' }.
  rewrite /relay_after_send0 Hinord_n.
  have Hnn : (n_relay == 0) = false by rewrite eqn0Ngt Hnrpos.
  rewrite Hnn eqxx.
  rewrite /std_Recv_dec /Recv_param /=. by eexists.
have [f_n Hras_n_eq] := Hras_n_sig.
have Hbgs_n_recv : bgs n_relay = Recv n_relay f_n.
  rewrite /bgs /send_procs_gen_local /send_procs_gen.
  rewrite /smc_interpreter.step.
  rewrite nth_cons_pos //.
  rewrite nth_mkseq //.
  have Hnj : (n_relay == (j : nat)) by apply/eqP; rewrite Hjn.
  rewrite Hnj.
  rewrite Hras_n_eq.
  set body_n := nth _ _ _.
  have Hbody_n : body_n = Recv 0 f0.
    rewrite /body_n.
    rewrite nth_cons_pos; last exact: Hnrpos.
    rewrite nth_mkseq; last by rewrite -ltnS prednK.
    have Hnmj : (n_relay.-1 == (j : nat)) = false.
      apply negbTE. rewrite Hjn neq_ltn. apply/orP; left. by rewrite ltn_predL.
    rewrite Hnmj.
    rewrite /bg. move: Hbg_jm1. by rewrite -/j Hjn.
  rewrite Hbody_n /=.
  done.
(* H5 (dp_safe witness): bgs n_relay is a Recv, not a Send. *)
have Hsafe : forall v k, bgs n_relay <> Send 0 v k.
  move=> v k. rewrite Hbgs_n_recv. discriminate.
(* H3: bgs j.-1 fired by Alice's enc, becomes Recv j.-1 with the Emul-forwarding
   callback (the inner std_Recv_dec from relay_body's intermediate branch). *)
have Hbgs_jm1_recv : { f_recv : data -> proc data |
  bgs j.-1 = Recv j.-1 f_recv /\
  forall m rr0, f_recv (e_loc (@enc AHE (ek (nat_to_party_id j)) m rr0)) =
    Send j.+1 (e_loc (@Emul AHE (alice_enc_local j)
      (@enc AHE (ek (nat_to_party_id j.+1)) m
        (r2_relay (inord j.-1))))) Finish }.
{ rewrite Hbgs_jm1 -Hf0_eq /=.
  rewrite /std_Recv_dec /Recv_param /=.
  eexists. split; first by reflexivity.
  move=> m rr0.
  rewrite /= /std_from_enc /=.
  have Hkey : ek j = pub_of_priv (dk_relay (inord j.-1)).
    have Hjm1S' : (inord j.-1 : 'I_n_relay.+1).+1 = j :> nat by rewrite /= Hjm1_inord Hjm1S.
    transitivity (ek (inord j.-1 : 'I_n_relay.+1).+1).
      by rewrite Hjm1S'.
    exact: (key_relay (inord j.-1)).
  rewrite Hkey dec_correct /=.
  congr (Send _ _ Finish); first by rewrite Hjm1S.
  congr (e_loc (Emul _ _)).
  by case: (j : nat) Hj3 => [|[|[|n']]]. }
(* Final assembly: build the drain_phase Record fields. *)
have [f_recv [Hf_recv_eq Hf_recv_cb]] := Hbgs_jm1_recv.
pose dp_j_ord : 'I_n_relay.+1 := Ordinal Hjpred_lt.
have Hjm2_n : ((j : nat) - 2)%N = (n_relay - 2)%N by rewrite Hjn.
have Hj_eq3 : (j : nat) = ((j : nat) - 2).+2.
  by case: (j : nat) Hj3 => [|[|[|n']]] // _.
have Hdp_sender_eq : bgs dp_j_ord = Send dp_j_ord.+2
    (e_loc (@enc AHE (ek (nat_to_party_id dp_j_ord.+2))
                 (chain_acc_local dp_j_ord) rr)) Finish.
{ rewrite /dp_j_ord /=.
  rewrite -Hjm2_n.
  rewrite Hbgs_snd_eq.
  congr (Send _ (e_loc (enc (ek _) _ _)) _).
  - by [].
  - by case: (j : nat) Hj3 => [|[|[|n']]]. }
have Hdp_finish_eq : forall i : nat, (i < dp_j_ord)%N -> bgs i = Finish.
{ move=> i Hi.
  apply: Hbgs_finish.
  have Hi' : (i < (j : nat) - 2)%N by rewrite Hjm2_n.
  rewrite Hj_eq3 !ltnS.
  by rewrite -ltnS in Hi'. }
have Hdp_last_sig : { f | bgs n_relay = Recv n_relay f /\
    forall m rr0, f (e_loc (@enc AHE (ek (nat_to_party_id n_relay.+1)) m rr0)) =
      Send 0 (e_loc (@enc AHE (ek alice_idx) m (r2_relay (inord n_relay)))) Finish }.
{ exists f_n. split; first exact Hbgs_n_recv.
  move=> m rr0.
  move: Hras_n_eq.
  rewrite /relay_after_send0 Hinord_n.
  have Hnn : (n_relay == 0) = false by rewrite eqn0Ngt Hnrpos.
  rewrite Hnn eqxx.
  rewrite /std_Recv_dec /Recv_param /=.
  case=> Hf_n_eq.
  rewrite -Hf_n_eq /=.
  rewrite /std_from_enc /=.
  have Hkey_n : ek n_relay.+1 = pub_of_priv (dk_relay (inord n_relay)).
    transitivity (ek (inord n_relay : 'I_n_relay.+1).+1).
      by rewrite /= Hinord_n.
    exact: (key_relay (inord n_relay)).
  rewrite Hkey_n dec_correct /=.
  reflexivity. }
have Hdp_between_sig : forall i : 'I_n_relay.+1, (dp_j_ord < i)%N -> (i < n_relay)%N ->
  { f | bgs i = Recv i f /\
    forall m rr0, f (e_loc (@enc AHE (ek (nat_to_party_id i.+1)) m rr0)) =
      Send i.+2 (e_loc (@Emul AHE (alice_enc_local (inord i.+1))
        (@enc AHE (ek (nat_to_party_id i.+2)) m
          (r2_relay (inord i))))) Finish }.
{ move=> i Hilow Hihigh.
  have Hi_eq : (i : nat) = (j : nat).-1.
    apply: anti_leq.
    have Hjpredval : (j : nat).-1 = (n_relay - 1)%N by rewrite Hjn subn1.
    have Hnm2 : ((n_relay - 2)%N.+1 = (n_relay - 1)%N).
      by case: n_relay Hnr3 => [|[|[|n']]] // _; rewrite ?subSS ?subn0.
    apply/andP; split.
    - rewrite Hjpredval subn1.
      by rewrite -ltnS prednK.
    - rewrite Hjpredval -Hnm2. exact: Hilow.
  have Hi1 : (i.+1 = j :> nat) by rewrite Hi_eq prednK.
  exists f_recv. split.
  - rewrite Hi_eq. exact Hf_recv_eq.
  - move=> m rr0.
    have Hekeq : ek (nat_to_party_id i.+1) = ek j by rewrite Hi1.
    rewrite Hekeq Hi_eq Hf_recv_cb.
    have Hjjm1S : j.-1.+2 = j.+1 by rewrite -Hjm1S.
    have Hinordj : (inord j.-1.+1 : 'I_n_relay.+1) = j.
      by apply val_inj => /=; rewrite inordK ?Hjm1S //; exact: ltn_ord.
    rewrite Hjjm1S Hinordj.
    by rewrite -Hjm1S. }
have Hdp_between_sig2 : forall i : nat, (dp_j_ord < i)%N -> (i < n_relay)%N ->
  { f | bgs i = Recv i f /\
    forall m rr0, f (e_loc (@enc AHE (ek (nat_to_party_id i.+1)) m rr0)) =
      Send i.+2 (e_loc (@Emul AHE (alice_enc_local (inord i.+1))
        (@enc AHE (ek (nat_to_party_id i.+2)) m
          (r2_relay (inord i))))) Finish }.
{ move=> i Hilow Hihigh.
  have Hi_lt : (i < n_relay.+1)%N := ltn_trans Hihigh (ltnSn _).
  have := Hdp_between_sig (Ordinal Hi_lt) Hilow Hihigh.
  by []. }
unshelve refine (exist _ (@MkDrainPhase AHE ek n_relay u r rand_a v_relay r1_relay r2_relay dp_j_ord rr bgs Hsafe Hjpred_succ_lt Hdp_sender_eq Hdp_finish_eq Hdp_last_sig Hdp_between_sig2) _).
split; first by [].
(* H4: main step equation via eq_from_nth. *)
simpl.
rewrite /one_step_procs /ps_procs /send_st /drain_st.
rewrite /send_procs_gen_local /send_procs_gen /drain_procs_gen.
rewrite /unzip1 -2!map_comp.
set sp_list := (Send (alice_send_dest j) _ _ :: _).
have Hszsp : size sp_list = n_relay.+2.
  by rewrite /sp_list /= size_map size_iota.
apply (@eq_from_nth _ (@Finish data)).
  by rewrite size_map size_iota Hszsp /= size_map size_iota.
move=> k Hk.
rewrite size_map size_iota Hszsp in Hk.
rewrite (nth_map 0); last by rewrite size_iota Hszsp.
rewrite nth_iota; last by rewrite Hszsp.
rewrite add0n /comp /=.
case: k Hk => [|k] Hk.
- (* Position 0: Alice fires *)
  rewrite /sp_list /smc_interpreter.step /=.
  rewrite Hadt.
  rewrite nth_cons_pos //.
  rewrite nth_mkseq; last by rewrite -ltnS prednK //; exact: ltnW.
  have Hjm1nej : (n_relay.-1 == j) = false.
    by rewrite Hjn; apply negbTE; rewrite neq_ltn ltn_predL Hnrpos.
  rewrite Hjm1nej.
  have -> : bg n_relay.-1 = Recv 0 f0.
    by rewrite -Hjn -/j; exact Hbg_jm1.
  rewrite eqxx /=.
  by rewrite Hjn.
- (* Position k.+1 *)
  have Hkn : (k < n_relay.+1)%N by [].
  rewrite nth_cons_pos //.
  rewrite nth_mkseq //=.
  have Hbgs_eq : (smc_interpreter.step sp_list [::] k.+1).1.1 = bgs k by [].
  rewrite Hbgs_eq.
  case Heq1 : (k == (n_relay - 2)%N).
  + (* k = n_relay - 2: this is the dp_j_ord position *)
    move/eqP: Heq1 => Heq1.
    have Hk_jm2 : k = ((j : nat) - 2)%N by rewrite Heq1 -Hjm2_n.
    rewrite Hk_jm2 Hbgs_snd_eq.
    have Hjeq3 : (j : nat) = (n_relay - 2).+2.
      by rewrite Hjn; case: n_relay Hnr3 => [|[|[|n']]] // _.
    have Hjnp : nat_to_party_id (j : nat) = match (n_relay - 2)%N with 0%N => Charlie | _.+1 => NoParty end.
      rewrite Hjeq3.
      by case: n_relay Hnr3 => [|[|[|n']]] // _.
    congr (Send _ (std_e (enc (ek _) _ _)) _).
    * by rewrite -Hjeq3.
    * by rewrite -Hjnp.
    * by rewrite -Hjm2_n.
  + case Heq2 : (k == (n_relay - 2).+1).
    * (* k = n_relay - 1 *)
      move/eqP: Heq2 => Heq2.
      rewrite {1}Heq2.
      have Hkp1 : ((n_relay - 2)%N.+1 = j.-1).
        rewrite Hjn.
        by case: n_relay Hnr3 => [|[|[|n']]] // _; rewrite ?subSS ?subn0.
      rewrite Hkp1 Hf_recv_eq -Hkp1.
      by [].
    * by [].
Qed.

(* L3: send_phase_to_drain_phase_n2
   At j = 2 with n_relay = 2, the send_phase advances to a drain_phase
   at index 0. The active firing pair is Alice (Send 2) and bg(1) (Recv 0 f0).
   - bg(0) = Send 2 ... Finish (sp_sender2 frontier sender, NOP because target
     bg(2) = Recv 2 ..., not a Recv 0).
   - bg(2) is replaced by relay_after_send0(inord 2), a Recv 2 NOP.
   The Finish zone is vacuous (i < 0). *)
Lemma send_phase_to_drain_phase_n2 (sp : send_phase) :
  (sp_j sp : nat) = 2 ->
  n_relay = 2 ->
  { dp : drain_phase |
    (dp_j dp : nat) = 0 /\
    one_step_procs (ps_procs (send_st (sp_j sp) (sp_bg sp))) =
    ps_procs (drain_st (dp_j dp) (dp_rr_drain dp) (bg := dp_bg dp) (dp_safe dp)) }.
Proof.
move=> Hjn Hnr2.
set j := sp_j sp.
set bg := sp_bg sp.
set rr := sp_rr_fw sp.
set bgs := fun i => (smc_interpreter.step (send_procs_gen_local j bg) [::] i.+1).1.1.
have Hj_lt : (j < n_relay.+1)%N := ltn_ord _.
have Hj2 : (j : nat) = 2%N by rewrite -/j Hjn.
have Hj2eq : (sp_j sp == 2%N :> nat) by apply/eqP; exact Hjn.
have Hjpos : (0 < j)%N by rewrite -/j Hjn.
have Hnrpos : (0 < n_relay)%N := Hn_relay.
have [[sv0 f0] [Hbody0 Hbg_jm1]] := sp_active sp.
simpl in Hbody0, Hbg_jm1.
have Hjeqn : (j : nat) = n_relay by rewrite Hj2 Hnr2.
have [f_dec [Hbg_n Hf_dec_eq]] := sp_last sp Hjeqn.
have Hsp_snd2 := sp_sender2 sp Hj2eq.
have Hadt : alice_send_dest j = (j : nat).
  by rewrite /alice_send_dest /maxn -/j Hj2.
have Hjm1_lt : (j.-1 < n_relay.+1)%N
  by apply (leq_ltn_trans (leq_pred _) Hj_lt).
have Hjm1_ne : j.-1 != (j : nat).
  apply/eqP => H. have : (j.-1 < j)%N by rewrite ltn_predL.
  by rewrite H ltnn.
have Hjm1_lt_n : (j.-1 < n_relay)%N.
  apply (@leq_trans (j : nat)); first by rewrite ltn_predL.
  by rewrite Hjeqn.
have Hjm1_ne_n : (j.-1 != n_relay :> nat).
  by rewrite neq_ltn Hjm1_lt_n.
have Hadt_jm1 : alice_send_dest j = j.-1.+1.
  rewrite Hadt. transitivity (j : nat); first by [].
  by rewrite (prednK Hjpos).
have Hbgs_jm1 : bgs j.-1 = f0 (e_loc (alice_enc_local j)).
  rewrite /bgs /send_procs_gen_local.
  apply: bg_recv0_fire_send Hjm1_lt Hjm1_ne Hbg_jm1 Hadt_jm1.
have Hjm1_inord : ((inord j.-1 : 'I_n_relay.+1) : nat) = j.-1.
  apply inordK. by apply: leq_trans Hjm1_lt (leqnn _).
have Hjm1_pos : (0 < j.-1)%N by rewrite -subn1 subn_gt0 -/j Hj2.
have Hjm1_ne0 : ((inord j.-1 : 'I_n_relay.+1) : nat) != 0%N
  by rewrite Hjm1_inord -lt0n.
have Hjm1_ne_n_inord : ((inord j.-1 : 'I_n_relay.+1) : nat) != n_relay
  by rewrite Hjm1_inord.
rewrite /relay_body_local /relay_body in Hbody0.
rewrite (negbTE Hjm1_ne0) (negbTE Hjm1_ne_n_inord) Hjm1_inord in Hbody0.
case: Hbody0 => _ Hf0_eq.
have Hjm1S : (j.-1).+1 = j by rewrite (prednK Hjpos).
have H0_lt : (0 < n_relay.+1)%N by [].
have H0_ne_j : 0%N != (j : nat).
  apply/eqP => H. by rewrite -H in Hjpos.
have Hbg_0 : bg 0 = Send 2
    (e_loc (@enc AHE (ek (nat_to_party_id 2)) (chain_acc_local 0) rr)) Finish.
  by rewrite /bg /rr; exact: Hsp_snd2.
have Hbgs_0 : bgs 0%N = Send 2
    (e_loc (@enc AHE (ek (nat_to_party_id 2)) (chain_acc_local 0) rr)) Finish.
  rewrite /bgs /send_procs_gen_local /send_procs_gen /smc_interpreter.step /=.
  rewrite nth_mkseq //.
  rewrite (negbTE H0_ne_j).
  rewrite Hbg_0 /=.
  have H1_ne_j : (1%N != (j : nat)).
    by rewrite neq_ltn -/j Hj2.
  have H1_lt : (1 < n_relay)%N by rewrite Hnr2.
  rewrite (nth_map 0%N); last by rewrite size_iota.
  rewrite nth_iota //.
  rewrite (negbTE H1_ne_j).
  have Hbg1 : bg 1 = Recv 0 f0.
    have HH : sp_bg sp (sp_j sp).-1 = Recv 0 f0 by exact: Hbg_jm1.
    have Hpredeq : (sp_j sp).-1 = 1%N by rewrite Hjn.
    by rewrite -/bg Hpredeq in HH.
  rewrite Hbg1 /=.
  by [].
have Hinord_n : ((inord n_relay : 'I_n_relay.+1) : nat) = n_relay
  by rewrite inordK // ltnSn.
have Hras_n_sig : { f' | relay_after_send0 ek dk_relay v_relay r1_relay r2_relay (inord n_relay : 'I_n_relay.+1) = Recv n_relay f' }.
  rewrite /relay_after_send0 Hinord_n.
  have Hnn : (n_relay == 0) = false by rewrite eqn0Ngt Hnrpos.
  rewrite Hnn eqxx.
  rewrite /std_Recv_dec /Recv_param /=. by eexists.
have [f_n Hras_n_eq] := Hras_n_sig.
have Hbgs_n_recv : bgs n_relay = Recv n_relay f_n.
  rewrite /bgs /send_procs_gen_local /send_procs_gen.
  rewrite /smc_interpreter.step.
  rewrite nth_cons_pos //.
  rewrite (nth_map 0%N); last by rewrite size_iota.
  rewrite nth_iota; last by [].
  rewrite add0n.
  have Hnj : ((n_relay : nat) == (j : nat)) by apply/eqP; rewrite Hjeqn.
  rewrite Hnj.
  rewrite Hras_n_eq.
  set body_n := nth _ _ _.
  have Hbody_n : body_n = Recv 0 f0.
    rewrite /body_n.
    rewrite nth_cons_pos; last exact: Hnrpos.
    rewrite (nth_map 0%N); last by rewrite size_iota -ltnS prednK.
    rewrite nth_iota; last by rewrite -ltnS prednK.
    rewrite add0n.
    have Hnmj : (n_relay.-1 == (j : nat)) = false.
      apply negbTE. rewrite Hjeqn neq_ltn. apply/orP; left. by rewrite ltn_predL.
    rewrite Hnmj.
    rewrite /bg. move: Hbg_jm1. by rewrite -/j Hjeqn.
  rewrite Hbody_n /=.
  done.
have Hsafe : forall v k, bgs n_relay <> Send 0 v k.
  move=> v k. rewrite Hbgs_n_recv. discriminate.
have Hbgs_jm1_recv : { f_recv : data -> proc data |
  bgs j.-1 = Recv j.-1 f_recv /\
  forall m rr0, f_recv (e_loc (@enc AHE (ek (nat_to_party_id j)) m rr0)) =
    Send j.+1 (e_loc (@Emul AHE (alice_enc_local j)
      (@enc AHE (ek (nat_to_party_id j.+1)) m
        (r2_relay (inord j.-1))))) Finish }.
{ rewrite Hbgs_jm1 -Hf0_eq /=.
  rewrite /std_Recv_dec /Recv_param /=.
  eexists. split; first by reflexivity.
  move=> m rr0.
  rewrite /= /std_from_enc /=.
  have Hkey : ek j = pub_of_priv (dk_relay (inord j.-1)).
    have Hjm1S' : (inord j.-1 : 'I_n_relay.+1).+1 = j :> nat by rewrite /= Hjm1_inord Hjm1S.
    transitivity (ek (inord j.-1 : 'I_n_relay.+1).+1).
      by rewrite Hjm1S'.
    exact: (key_relay (inord j.-1)).
  rewrite Hkey dec_correct /=.
  congr (Send _ _ Finish); first by rewrite Hjm1S.
  congr (e_loc (Emul _ _)).
  by case: (j : nat) Hj2 => [|[|[|n']]]. }
have [f_recv [Hf_recv_eq Hf_recv_cb]] := Hbgs_jm1_recv.
pose dp_j_ord : 'I_n_relay.+1 := Ordinal H0_lt.
have Hdp_j_lt : (dp_j_ord.+1 < n_relay.+1)%N.
  by rewrite /dp_j_ord /= Hnr2.
have Hdp_sender_eq : bgs dp_j_ord = Send dp_j_ord.+2
    (e_loc (@enc AHE (ek (nat_to_party_id dp_j_ord.+2))
                 (chain_acc_local dp_j_ord) rr)) Finish.
{ rewrite /dp_j_ord /=. exact: Hbgs_0. }
have Hdp_finish_eq : forall i : nat, (i < dp_j_ord)%N -> bgs i = Finish.
{ move=> i Hi. by rewrite /dp_j_ord /= ltn0 in Hi. }
have Hdp_last_sig : { f | bgs n_relay = Recv n_relay f /\
    forall m rr0, f (e_loc (@enc AHE (ek (nat_to_party_id n_relay.+1)) m rr0)) =
      Send 0 (e_loc (@enc AHE (ek alice_idx) m (r2_relay (inord n_relay)))) Finish }.
{ exists f_n. split; first exact Hbgs_n_recv.
  move=> m rr0.
  move: Hras_n_eq.
  rewrite /relay_after_send0 Hinord_n.
  have Hnn : (n_relay == 0) = false by rewrite eqn0Ngt Hnrpos.
  rewrite Hnn eqxx.
  rewrite /std_Recv_dec /Recv_param /=.
  case=> Hf_n_eq.
  rewrite -Hf_n_eq /=.
  rewrite /std_from_enc /=.
  have Hkey_n : ek n_relay.+1 = pub_of_priv (dk_relay (inord n_relay)).
    transitivity (ek (inord n_relay : 'I_n_relay.+1).+1).
      by rewrite /= Hinord_n.
    exact: (key_relay (inord n_relay)).
  rewrite Hkey_n dec_correct /=.
  reflexivity. }
have Hdp_between_sig : forall i : nat, (dp_j_ord < i)%N -> (i < n_relay)%N ->
  { f | bgs i = Recv i f /\
    forall m rr0, f (e_loc (@enc AHE (ek (nat_to_party_id i.+1)) m rr0)) =
      Send i.+2 (e_loc (@Emul AHE (alice_enc_local (inord i.+1))
        (@enc AHE (ek (nat_to_party_id i.+2)) m
          (r2_relay (inord i))))) Finish }.
{ move=> i Hilow Hihigh.
  have Hi_lt2 : (i < 2)%N.
    have Hcopy : (i < n_relay)%N := Hihigh.
    rewrite Hnr2 in Hcopy. exact Hcopy.
  have Hi_eq : i = 1%N.
    apply: anti_leq. apply/andP; split; first by [].
    by [].
  have Hi_jm1 : i = (j : nat).-1 by rewrite Hi_eq Hjn.
  exists f_recv. split.
  - by rewrite Hi_jm1.
  - move=> m rr0.
    have Hekeq : ek (nat_to_party_id i.+1) = ek j.
      by rewrite Hi_eq Hj2.
    rewrite Hekeq Hi_jm1 Hf_recv_cb.
    rewrite Hjm1S.
    have Hinordj : (inord j : 'I_n_relay.+1) = j.
      by apply val_inj => /=; rewrite inordK.
    rewrite Hinordj.
    by [].  }
unshelve refine (exist _ (@MkDrainPhase AHE ek n_relay u r rand_a v_relay r1_relay r2_relay dp_j_ord rr bgs Hsafe Hdp_j_lt Hdp_sender_eq Hdp_finish_eq Hdp_last_sig Hdp_between_sig) _).
split; first by [].
simpl.
rewrite /one_step_procs /ps_procs /send_st /drain_st.
rewrite /send_procs_gen_local /send_procs_gen /drain_procs_gen.
rewrite /unzip1 -2!map_comp.
set sp_list := (Send (alice_send_dest j) _ _ :: _).
have Hszsp : size sp_list = n_relay.+2.
  by rewrite /sp_list /= size_map size_iota.
apply (@eq_from_nth _ (@Finish data)).
  by rewrite size_map size_iota Hszsp /= size_map size_iota.
move=> k Hk.
rewrite size_map size_iota Hszsp in Hk.
rewrite (nth_map 0); last by rewrite size_iota Hszsp.
rewrite nth_iota; last by rewrite Hszsp.
rewrite add0n /comp /=.
case: k Hk => [|k] Hk.
- (* Position 0: Alice fires *)
  rewrite /sp_list /smc_interpreter.step /=.
  rewrite Hadt.
  rewrite nth_cons_pos //.
  rewrite nth_mkseq; last by rewrite -ltnS prednK //; exact: ltnW.
  rewrite (negbTE Hjm1_ne).
  have -> : bg j.-1 = Recv 0 f0 by rewrite /bg; exact Hbg_jm1.
  rewrite eqxx /=.
  by rewrite Hjeqn.
- have Hkn : (k < n_relay.+1)%N by [].
  rewrite nth_cons_pos //.
  rewrite nth_mkseq //=.
  have Hbgs_eq : (smc_interpreter.step sp_list [::] k.+1).1.1 = bgs k by [].
  rewrite Hbgs_eq.
  case Heq0 : (k == 0%N).
  + move/eqP: Heq0 => Heq0; subst k.
    rewrite Hbgs_0.
    by [].
  + case Heq1 : (k == 1%N).
    * move/eqP: Heq1 => Heq1; subst k.
      have Hbgs_1 : bgs 1%N = Recv 1 f_recv.
        have HH : bgs (j : nat).-1 = Recv (j : nat).-1 f_recv := Hf_recv_eq.
        have Hpredeq : (j : nat).-1 = 1%N by rewrite Hjn.
        by rewrite Hpredeq in HH.
      rewrite Hbgs_1.
      by [].
    * by [].
Qed.

(* L7: known_ret_state of any tail_phase. Trivial — delegates to known_ret_tail. *)
Lemma known_ret_of_tail_phase (tp : tail_phase) :
  known_ret_state (tail_st (tp_rr_tail tp)).
Proof. exact: known_ret_tail. Qed.

(* L5: a drain_phase whose active forwarder is the second-to-last relay
   takes one drain step and reaches a tail_phase. Wraps step_ok_drain_tail_gen. *)
Lemma drain_phase_to_tail_phase (dp : drain_phase) :
  ((dp_j dp : nat).+1 = n_relay) ->
  { tp : tail_phase |
    one_step_procs (ps_procs (drain_st (dp_j dp) (dp_rr_drain dp)
                                       (bg := dp_bg dp) (dp_safe dp))) =
    ps_procs (tail_st (tp_rr_tail tp)) }.
Proof.
move=> Hjeq.
set j := dp_j dp.
set rr := dp_rr_drain dp.
set bg := dp_bg dp.
have Hsafe : forall v k, bg n_relay <> Send 0 v k := dp_safe dp.
have [f_l [Hbg_l Hf_l]] := dp_last dp.
have Hjm : (j : nat) = n_relay.-1.
  apply: succn_inj. rewrite (prednK Hn_relay). exact: Hjeq.
have Hbg_finish : forall i, (i < n_relay.+1)%N -> i != (j : nat) -> i != j.+1 -> bg i = Finish.
  move=> i Hi Hneqj Hneqj1.
  apply: (dp_finish dp).
  have Hi_lt_jp1 : (i < j.+1)%N.
    rewrite ltn_neqAle Hneqj1 /=.
    have : (i < (j.+1).+1)%N by rewrite Hjeq.
    by [].
  by rewrite ltn_neqAle Hneqj /= -ltnS.
have Hbg_l_at_jp1 : bg j.+1 = Recv j.+1 f_l.
  have : (j.+1 : nat) = n_relay by rewrite Hjeq.
  by move=> ->.
have Hek_eq : ek j.+2 = ek n_relay.+1.
  have : j.+2 = n_relay.+1 by rewrite Hjeq.
  by move=> ->.
have Hca_eq : chain_acc_local n_relay.-1 = chain_acc_local j by rewrite Hjm.
have Hcb : f_l (e_loc (enc (ek j.+2) (chain_acc_local j) rr)) =
  Send 0 (e_loc (enc (ek alice_idx) (chain_acc_local n_relay.-1) (r2_relay (inord n_relay)))) Finish.
  rewrite Hek_eq Hca_eq.
  exact: (Hf_l (chain_acc_local j) rr).
have Hsig : { f : data -> proc data & { rr_next : rand AHE |
   bg j.+1 = Recv j.+1 f /\
   f (e_loc (enc (ek j.+2) (chain_acc_local j) rr)) =
   Send 0 (e_loc (enc (ek alice_idx) (chain_acc_local n_relay.-1) rr_next)) Finish }}.
  exists f_l, (r2_relay (inord n_relay)). by split.
have [rr' Hstep_eq] := @step_ok_drain_tail_gen AHE ek n_relay dk relays Hrelays
  v0 u r rand_a v_relay j rr bg Hsafe Hjeq Hsig Hbg_finish.
pose tp_bg' := fun i : nat => if i == n_relay then
  Send 0 (e_loc (enc (ek alice_idx) (chain_acc_local n_relay.-1) rr')) Finish
  else @Finish data.
have Htp_last : tp_bg' n_relay = Send 0
  (e_loc (@enc AHE (ek alice_idx) (chain_acc_local n_relay.-1) rr')) Finish.
  by rewrite /tp_bg' eqxx.
have Htp_finish : forall j0 : 'I_n_relay.+1, (j0 < n_relay)%N -> tp_bg' j0 = Finish.
  move=> j0 Hj0. rewrite /tp_bg'.
  by have -> : (j0 == n_relay :> nat) = false by rewrite ltn_eqF.
pose tp := @MkTailPhase AHE ek n_relay u r v_relay rr' tp_bg' Htp_last Htp_finish.
exists tp. simpl.
exact Hstep_eq.
Qed.

(* L6: every drain_phase is in known_ret_state.
   Proof by induction on the measure n_relay.-1 - dp_j dp. *)
Lemma known_ret_of_drain_phase (dp : drain_phase) :
  known_ret_state (drain_st (dp_j dp) (dp_rr_drain dp) (bg := dp_bg dp) (dp_safe dp)).
Proof.
move E : (n_relay.-1 - (dp_j dp : nat))%N => m.
elim: m dp E => [|m IH] dp Hm.
- (* Base: dp_j dp = n_relay.-1, so (dp_j dp).+1 = n_relay *)
  have Hjp1 : ((dp_j dp : nat).+1 = n_relay).
    have Hge : (n_relay.-1 <= (dp_j dp : nat))%N by rewrite -subn_eq0 Hm.
    have Hjlt : ((dp_j dp : nat) < n_relay)%N
      by rewrite -ltnS; exact: dp_j_lt dp.
    apply: anti_leq.
    rewrite Hjlt /=.
    by rewrite -ltnS (prednK Hn_relay) in Hge.
  have [tp Hstep] := @drain_phase_to_tail_phase dp Hjp1.
  apply (KnownRetStep (known_ret_of_tail_phase tp) Hstep).
  + apply: (@drain_has_progress_gen AHE ek n_relay dk relays Hrelays
              v0 u r rand_a v_relay (dp_j dp) (dp_rr_drain dp) (dp_bg dp) (dp_safe dp)).
    * exact: (dp_j_lt dp).
    * have [f_l [Hbg_l _]] := dp_last dp.
      exists n_relay, f_l. by rewrite Hjp1.
  + exact: (@drain_not_terminated_gen (dp_j dp) (dp_rr_drain dp) (dp_bg dp) (dp_safe dp)).
- (* Step: m.+1, so (dp_j dp).+1 < n_relay *)
  have Hjp1lt : ((dp_j dp : nat).+1 < n_relay)%N.
    have Hsub_pos : (0 < n_relay.-1 - (dp_j dp : nat))%N by rewrite Hm.
    rewrite subn_gt0 in Hsub_pos.
    by rewrite -ltnS (prednK Hn_relay) in Hsub_pos.
  have [dp' [Hjeq Hstep]] := @drain_phase_step dp Hjp1lt.
  have Hm' : (n_relay.-1 - (dp_j dp' : nat))%N = m.
    rewrite Hjeq.
    have Hcopy : (n_relay.-1 - dp_j dp = m.+1)%N := Hm.
    by rewrite subnS Hcopy.
  apply (KnownRetStep (IH dp' Hm') Hstep).
  + apply: (@drain_has_progress_gen AHE ek n_relay dk relays Hrelays
              v0 u r rand_a v_relay (dp_j dp) (dp_rr_drain dp) (dp_bg dp) (dp_safe dp)).
    * exact: (dp_j_lt dp).
    * have [f_act [Hbg_act _]] := dp_between dp (dp_j dp).+1 (ltnSn _) Hjp1lt.
      by exists (dp_j dp).+1, f_act.
  + exact: (@drain_not_terminated_gen (dp_j dp) (dp_rr_drain dp) (dp_bg dp) (dp_safe dp)).
Qed.

(* L8: known_ret_state directly for the n_relay=1 special case.
   At n_relay=1, j=1, the chain from recv_st(1) has 4 op steps:
     recv_st(1) bg
       --[step_ok_recv_send_concrete]-->
     send_st(1) bg_s    where bg_s(0) = Recv 0 f_enc, bg_s(1) = relay_after_send0 1
       --[manual eq_from_nth, ALGEBRAIC SHIFT]-->
     drain_st(0) bg_s2  where bg_s2(0) = Send 2 (enc(ek 2)(chain_acc 0)(rand_mul rr_a r2 0))
                              bg_s2(1) = relay_after_send0 1
       --[L5/step_ok_drain_tail_gen]-->
     tail_st rr_t
       --[KnownRetStep + known_ret_tail]-->
     known_ret_state

   PARTIAL PROGRESS: setup + Hstep_rs + Hbg_s_0 (NOP for bg(0)) + Hbg_s_1
   (post-active-fire shape) + Hbg_s2_0 (the SHIFTED sender at bg_s2(0), which
   contains the key algebraic identity Emul_addM + chain_acc commutativity)
   are all built. The remaining work is:
     1. Hbg_s2_1: bg_s2(1) = bg_s(1) (NOP for second position, ~30 lines)
     2. Build drain_phase Record at dp_j=0 with dp_bg := bg_s2 (~50 lines for
        dp_safe and dp_last witnesses)
     3. Prove the send→drain step equation via eq_from_nth at 3 positions (~80 lines)
     4. Chain via 2 KnownRetStep calls + known_ret_of_drain_phase (~20 lines)

   The algebraic core (Hbg_s2_0) is the hardest part and IS proven below; the
   remainder is mechanical position-by-position case work analogous to L3
   (send_phase_to_drain_phase_n2) but at j=1 instead of j=2. *)
Lemma tail_phase_from_recv_phase_n1 (rp : recv_phase) :
  n_relay = 1 ->
  (rp_j rp : nat) = 1 ->
  known_ret_state (recv_st (rp_j rp) (rp_bg rp)).
Proof.
move=> Hnr Hjeq.
set j := rp_j rp; set bg := rp_bg rp.
have Hj1 : (j == 1%N :> nat) by rewrite /j Hjeq.
have [f_enc [Hbg0 Hf_enc_eq]] := (rp_j1_recv rp) Hj1.
rewrite -/bg in Hbg0.
set bg_s := fun i => (smc_interpreter.step (recv_procs_gen_local j bg) [::] i.+1).1.1.
have Hstep_rs : one_step_procs (ps_procs (recv_st j bg)) = ps_procs (send_st j bg_s)
  by exact: step_ok_recv_send_concrete.
have Hbg_s_0 : bg_s 0%N = bg 0%N.
{ rewrite /bg_s /recv_procs_gen_local /recv_procs_gen /smc_interpreter.step /=.
  rewrite nth_mkseq //.
  have -> : (0%N == j :> nat) = false by rewrite eq_sym (eqP Hj1).
  rewrite Hbg0 /=.
  have [f_a Hf_a] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays
    Hrelays_id v0 u r rand_a (j : nat) (ltn_ord j).
  by rewrite Hf_a.
}
have Hinord_j : (inord 1 : 'I_n_relay.+1) = j.
{ apply: val_inj => /=. by rewrite inordK ?(eqP Hj1) // Hnr. }
set sp_list := send_procs_gen_local j bg_s.
set bg_s2 := fun i => (smc_interpreter.step sp_list [::] i.+1).1.1.
have Hadt : alice_send_dest j = 1.
{ rewrite /alice_send_dest /maxn (eqP Hj1). by []. }
have [rr_a Halice_eq] := @alice_enc_value AHE ek n_relay u r rand_a v_relay r1_relay j.
have Hbg_s2_0 : bg_s2 0%N = Send 2 (e_loc (enc (ek (nat_to_party_id 2))
  (chain_acc_local 0) (rand_mul rr_a (r2_relay ord0)))) Finish.
{ rewrite /bg_s2 /sp_list /send_procs_gen_local /send_procs_gen /smc_interpreter.step /=.
  rewrite Hadt /=.
  rewrite (nth_map 0%N); last by rewrite size_iota.
  rewrite nth_iota //=.
  have -> : (0%N == j :> nat) = false by rewrite eq_sym (eqP Hj1).
  rewrite Hbg_s_0 Hbg0 /=.
  rewrite Hf_enc_eq Halice_eq.
  rewrite /chain_acc_local /chain_acc.
  have Hek_eq : ek j.+1 = ek 2%N by congr ek; rewrite (eqP Hj1).
  rewrite Hek_eq !enc_curry_eq -(@Emul_addM AHE) /mr_bop /=.
  congr (Send _ _ Finish).
  congr (e_loc _).
  congr ((E[ _]) _).
  rewrite /term_local GRing.addrC.
  by rewrite Hinord_j.
}
(* Step A: Prepare witnesses for the drain_phase Record. *)
have Hjnat : (j : nat) = 1 := eqP Hj1.
have Hinord_n_eq : ((inord n_relay : 'I_n_relay.+1) : nat) = n_relay
  by rewrite inordK // ltnSn.
have Hras_n_sig : { f' | relay_after_send0 ek dk_relay v_relay r1_relay r2_relay (inord n_relay : 'I_n_relay.+1) = Recv n_relay f' }.
{ rewrite /relay_after_send0 Hinord_n_eq.
  have Hnn : (n_relay == 0) = false by rewrite Hnr.
  rewrite Hnn eqxx /std_Recv_dec /Recv_param /=. by eexists. }
have [f_n Hras_n_eq] := Hras_n_sig.
(* Step B: bg_s 1 and bg_s2 1 both equal relay_after_send0 (inord 1). *)
have Hbg_s_1 : bg_s 1%N = relay_after_send0 ek dk_relay v_relay r1_relay r2_relay (inord 1 : 'I_n_relay.+1).
{ rewrite /bg_s /recv_procs_gen_local /recv_procs_gen /smc_interpreter.step /=.
  rewrite (nth_map 0%N); last by rewrite size_iota Hnr.
  rewrite nth_iota; last by rewrite Hnr.
  rewrite addn0 /=.
  have -> : (1%N == j :> nat) by rewrite eq_sym (eqP Hj1).
  have Hsend := @relay_body_send0_cont AHE ek n_relay dk_relay v_relay r1_relay r2_relay (inord 1 : 'I_n_relay.+1).
  rewrite Hsend /=.
  have [f_a Hf_a] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays
    Hrelays_id v0 u r rand_a (j : nat) (ltn_ord j).
  rewrite Hf_a /=.
  have -> : (j.+1 == 2%N) = true by apply/eqP; rewrite (eqP Hj1).
  by [].
}
have Hbg_s2_1 : bg_s2 1%N = relay_after_send0 ek dk_relay v_relay r1_relay r2_relay (inord 1 : 'I_n_relay.+1).
{ rewrite /bg_s2 /sp_list /send_procs_gen_local /send_procs_gen /smc_interpreter.step /=.
  rewrite Hadt /=.
  rewrite (nth_map 0%N); last by rewrite size_iota Hnr.
  rewrite nth_iota; last by rewrite Hnr.
  rewrite addn0 /=.
  have -> : (1%N == j :> nat) by rewrite eq_sym (eqP Hj1).
  have Hinord1_val : (inord 1 : 'I_n_relay.+1) = 1 :> nat by rewrite inordK ?ltnS ?Hnr.
  rewrite {1}/relay_after_send0 Hinord1_val.
  have -> : (1%N == 0%N) = false by [].
  have -> : (1%N == n_relay) = true by rewrite Hnr.
  rewrite /std_Recv_dec /Recv_param /=.
  rewrite (nth_map 0%N); last by rewrite size_iota Hnr.
  rewrite nth_iota; last by rewrite Hnr.
  rewrite add0n /=.
  have -> : (0%N == j :> nat) = false by rewrite eq_sym (eqP Hj1).
  rewrite Hbg_s_0 Hbg0 /=.
  by [].
}
have Hinord1n : (inord 1 : 'I_n_relay.+1) = (inord n_relay : 'I_n_relay.+1).
{ apply: val_inj => /=. by rewrite !inordK ?Hnr // ltnS ?Hnr. }
have Hbg_s2_1_recv : bg_s2 1%N = Recv 1 f_n.
{ rewrite Hbg_s2_1 Hinord1n Hras_n_eq.
  by have -> : n_relay = 1 by rewrite Hnr. }
(* Step C: Build the drain_phase Record at dp_j = 0. *)
have H0lt : (0 < n_relay.+1)%N by [].
pose dp_j_ord : 'I_n_relay.+1 := Ordinal H0lt.
have Hdp_j_lt : (dp_j_ord.+1 < n_relay.+1)%N by rewrite /dp_j_ord /= Hnr.
have Hsafe : forall v k, bg_s2 n_relay <> Send 0 v k.
{ move=> v k. rewrite Hnr Hbg_s2_1_recv. by []. }
have Hdp_sender_eq : bg_s2 dp_j_ord = Send dp_j_ord.+2
  (e_loc (@enc AHE (ek (nat_to_party_id dp_j_ord.+2))
               (chain_acc_local dp_j_ord) (rand_mul rr_a (r2_relay ord0)))) Finish.
{ rewrite /dp_j_ord /=. exact: Hbg_s2_0. }
have Hdp_finish_eq : forall i : nat, (i < dp_j_ord)%N -> bg_s2 i = Finish.
{ move=> i Hi. by rewrite /dp_j_ord /= ltn0 in Hi. }
have Hdp_last_sig : { f | bg_s2 n_relay = Recv n_relay f /\
    forall m rr0, f (e_loc (@enc AHE (ek (nat_to_party_id n_relay.+1)) m rr0)) =
      Send 0 (e_loc (@enc AHE (ek alice_idx) m
        (r2_relay (inord n_relay)))) Finish }.
{ exists f_n. split.
  - rewrite Hnr Hbg_s2_1_recv. by [].
  - move=> m rr0.
    move: Hras_n_eq.
    rewrite /relay_after_send0 Hinord_n_eq.
    have Hnn : (n_relay == 0) = false by rewrite Hnr.
    rewrite Hnn eqxx /std_Recv_dec /Recv_param /=.
    case=> Hf_n_eq.
    rewrite -Hf_n_eq /=.
    rewrite /std_from_enc /=.
    have Hkey_n : ek n_relay.+1 = pub_of_priv (dk_relay (inord n_relay)).
    { transitivity (ek (inord n_relay : 'I_n_relay.+1).+1).
        by rewrite /= Hinord_n_eq.
      exact: (key_relay (inord n_relay)). }
    rewrite Hkey_n dec_correct /=.
    by [].
}
have Hdp_between_sig : forall i : nat, (dp_j_ord < i)%N -> (i < n_relay)%N ->
  { f | bg_s2 i = Recv i f /\
    forall m rr0, f (e_loc (@enc AHE (ek (nat_to_party_id i.+1)) m rr0)) =
      Send i.+2 (e_loc (@Emul AHE (alice_enc_local (inord i.+1))
        (@enc AHE (ek (nat_to_party_id i.+2)) m
          (r2_relay (inord i))))) Finish }.
{ move=> i Hilow Hihigh.
  exfalso. rewrite /dp_j_ord /= in Hilow. rewrite Hnr in Hihigh.
  by have := leq_trans Hilow Hihigh. }
pose dp : drain_phase := @MkDrainPhase AHE ek n_relay u r rand_a v_relay r1_relay r2_relay dp_j_ord (rand_mul rr_a (r2_relay ord0))
  bg_s2 Hsafe Hdp_j_lt Hdp_sender_eq Hdp_finish_eq Hdp_last_sig Hdp_between_sig.
have Hks2_drain := known_ret_of_drain_phase dp.
(* Step D: send→drain step equation via eq_from_nth at 3 positions. *)
have Hstep_sd : one_step_procs (ps_procs (send_st j bg_s)) =
  ps_procs (drain_st (dp_j dp) (dp_rr_drain dp) (bg := dp_bg dp) (dp_safe dp)).
{ rewrite /one_step_procs /ps_procs /send_st /drain_st.
  rewrite /send_procs_gen_local /send_procs_gen /drain_procs_gen.
  rewrite /unzip1 -2!map_comp.
  set splist := (Send (alice_send_dest j) _ _ :: _).
  have Hszsp : size splist = n_relay.+2.
    by rewrite /splist /= size_map size_iota.
  apply (@eq_from_nth _ (@Finish data)).
    by rewrite size_map size_iota Hszsp /= size_map size_iota.
  move=> k Hk.
  rewrite size_map size_iota Hszsp in Hk.
  rewrite (nth_map 0); last by rewrite size_iota Hszsp.
  rewrite nth_iota; last by rewrite Hszsp.
  rewrite add0n /comp /=.
  case: k Hk => [|k] Hk.
  - (* Position 0: Alice fires, output is alice_foldr (j+1) = alice_foldr n_relay+1 *)
    rewrite /splist /smc_interpreter.step /=.
    rewrite Hadt.
    rewrite nth_cons_pos //.
    rewrite nth_mkseq; last by rewrite Hnr.
    have H0nej : (0%N == j :> nat) = false by rewrite eq_sym (eqP Hj1).
    rewrite H0nej.
    rewrite Hbg_s_0 Hbg0 /=.
    by have -> : (j.+1 : nat) = n_relay.+1 by rewrite (eqP Hj1) Hnr.
  - (* Position k.+1: bg_s2 k = drain_procs entry at index k. *)
    have Hbgs2_eq : (smc_interpreter.step splist [::] k.+1).1.1 = bg_s2 k by [].
    rewrite Hbgs2_eq.
    rewrite nth_cons_pos //.
    have Hkbnd : (k < n_relay.+1)%N by [].
    rewrite nth_mkseq //=.
    case Heq0 : (k == 0%N).
    + move/eqP: Heq0 => Heq0; subst k. rewrite Hbg_s2_0. by [].
    + case Heq1 : (k == 1%N).
      * move/eqP: Heq1 => Heq1; subst k. rewrite Hbg_s2_1_recv. by [].
      * move: Hkbnd. rewrite Hnr.
        move=> Hkl. exfalso.
        by case: k Heq0 Heq1 Hkl Hk Hbgs2_eq => [|[|k']] // _ _ _ _ _.
}
(* Step E: Hdest for send_has_progress_gen + final KnownRetStep chain. *)
have Hdest : exists f, nth (@Finish (std_data AHE))
    (send_procs_gen_local j bg_s) (alice_send_dest j) = Recv 0 f.
{ rewrite Hadt /send_procs_gen_local /send_procs_gen /=.
  rewrite nth_mkseq /=; last by rewrite Hnr.
  have -> : (0%N == j :> nat) = false by rewrite eq_sym (eqP Hj1).
  rewrite Hbg_s_0 Hbg0.
  by eexists. }
refine (KnownRetStep _ Hstep_rs _ _).
- exact: (KnownRetStep Hks2_drain Hstep_sd
            (send_has_progress_gen Hdest)
            (send_not_terminated_gen _ _)).
- by apply: recv_has_progress_gen.
- by apply: recv_not_terminated_gen.
Qed.

(* recv_phase_to_known: if we have a recv_phase Record, its state is known_ret_state.
   Proof by induction on n_relay - rp_j, using Record field extraction. *)
Lemma recv_phase_to_known (k : nat) (rp : recv_phase) :
  (rp_j rp + k = n_relay)%N ->
  known_ret_state (recv_st (rp_j rp) (rp_bg rp)).
Proof.
elim: k rp => [|k IH] rp Hjk;
set j := rp_j rp; set bg := rp_bg rp.
- (* Base case: k=0, j = n_relay. Compose L1 (recv→send) → L2/L3 (send→drain)
     → L6 (known_ret_of_drain_phase) for n_relay >= 2; L8 for n_relay = 1. *)
  have Hjeq : (rp_j rp : nat) = n_relay by move: Hjk; rewrite addn0.
  case: (leqP 2 n_relay) => Hnr2; first last.
  + (* n_relay = 1 *)
    have Hnr1 : n_relay = 1 by apply/eqP; rewrite eqn_leq Hn_relay andbT -ltnS.
    rewrite /j /bg.
    apply: tail_phase_from_recv_phase_n1 => //.
    by rewrite Hjeq Hnr1.
  + (* n_relay >= 2 *)
    have Hj2 : (2 <= rp_j rp)%N by rewrite Hjeq.
    have [sp [Hsj Hstep1]] := recv_phase_to_send_phase (rp:=rp) Hj2.
    have Hsj_eq : (sp_j sp : nat) = n_relay by rewrite Hsj.
    have Hsj_ord : sp_j sp = rp_j rp :> 'I_n_relay.+1 by exact: val_inj.
    (* Construct Hdest: bg_s' destination is Recv 0 (from sp_active) *)
    have Hdest : exists f, nth (@Finish (std_data AHE))
        (send_procs_gen_local (rp_j rp) (sp_bg sp))
        (alice_send_dest (rp_j rp)) = Recv 0 f.
      have [[sv0 f0] [_ Hbg_jm1]] := sp_active sp.
      simpl in Hbg_jm1.
      rewrite Hsj in Hbg_jm1.
      have Hjpos : (0 < rp_j rp)%N by exact: ltn_trans (ltn0Sn _) Hj2.
      have Had : alice_send_dest (rp_j rp) = (rp_j rp : nat).
        rewrite /alice_send_dest /maxn. case: ltnP => H //.
        by apply: anti_leq; rewrite H Hjpos.
      rewrite Had /send_procs_gen_local /send_procs_gen /=.
      rewrite nth_cons_pos //.
      rewrite nth_mkseq.
      2: { have := ltn_ord (rp_j rp). rewrite -ltnS prednK //.
           by move/ltnW. }
      have -> : ((rp_j rp).-1 == (rp_j rp : nat)) = false.
        by apply/negP; rewrite ltn_eqF // ltn_predL.
      by exists f0.
    case: (leqP 3 n_relay) => Hnr3.
    * (* n_relay >= 3: use L2 (send_phase_to_drain_phase_last) *)
      have [dp [_ Hstep2]] :=
        send_phase_to_drain_phase_last (sp:=sp) Hsj_eq Hnr3.
      rewrite Hsj_ord in Hstep2.
      have Hks2_drain := known_ret_of_drain_phase dp.
      rewrite /j /bg.
      refine (KnownRetStep _ Hstep1 _ _).
      -- exact: (KnownRetStep Hks2_drain Hstep2
                   (send_has_progress_gen Hdest)
                   (send_not_terminated_gen _ _)).
      -- by apply: recv_has_progress_gen.
      -- by apply: recv_not_terminated_gen.
    * (* n_relay = 2: use L3 (send_phase_to_drain_phase_n2) *)
      have Hnr_eq2 : n_relay = 2 by apply: anti_leq; rewrite Hnr2 -ltnS Hnr3.
      have Hsj2 : (sp_j sp : nat) = 2 by rewrite Hsj_eq Hnr_eq2.
      have [dp [_ Hstep2]] :=
        send_phase_to_drain_phase_n2 (sp:=sp) Hsj2 Hnr_eq2.
      rewrite Hsj_ord in Hstep2.
      have Hks2_drain := known_ret_of_drain_phase dp.
      rewrite /j /bg.
      refine (KnownRetStep _ Hstep1 _ _).
      -- exact: (KnownRetStep Hks2_drain Hstep2
                   (send_has_progress_gen Hdest)
                   (send_not_terminated_gen _ _)).
      -- by apply: recv_has_progress_gen.
      -- by apply: recv_not_terminated_gen.
- (* Step case: j + k.+1 = n_relay, j < n_relay *)
  have Hjn : (j < n_relay)%N.
    by rewrite -(ltn_add2r k.+1) Hjk addnS ltnS leq_addr.
  (* recv → send (unconditional) *)
  set bg_s := fun i => (smc_interpreter.step (recv_procs_gen_local j bg) [::] i.+1).1.1.
  have Hstep_rs : one_step_procs (recv_procs_gen_local j bg) =
    send_procs_gen_local j bg_s by exact: step_ok_recv_send_concrete.
  have Hstep_rs' : one_step_procs (ps_procs (recv_st j bg)) =
    ps_procs (send_st j bg_s) by exact Hstep_rs.
  (* send destination has Recv 0 *)
  have Hdest : exists f, nth (@Finish (std_data AHE))
      (send_procs_gen_local j bg_s) (alice_send_dest j) = Recv 0 f.
    apply send_dest_recv0 => //.
    move=> Hj0.
    (* Case split on j = 1 vs j >= 2 *)
    have Hcase : (j == 1%N :> nat) \/ (2 <= j)%N.
      case: (ltnP 1 j) => H; first by right.
      by left; apply /eqP; apply anti_leq; rewrite Hj0 H.
    have Hj_ne : (j.-1 == j :> nat) = false
      by apply negbTE; rewrite neq_ltn; apply /orP; left; rewrite prednK // ltnSn.
    have Hj_bound : (j.-1 < n_relay.+1)%N
      by apply (leq_ltn_trans (leq_pred j) (ltn_ord j)).
    have [f_alice Haf] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays
      Hrelays_id v0 u r rand_a (j : nat) (ltn_ord j).
    case: Hcase => [Hj1 | Hj2].
    + (* j = 1: use rp_j1_recv *)
      have [f_enc [Hf _]] := (rp_j1_recv rp) Hj1.
      rewrite -/bg in Hf.
      exists (oapp f_enc Fail \o @std_from_enc AHE).
      have Hj1' : (j : nat) = 1%N by exact (eqP Hj1).
      rewrite /bg_s /recv_procs_gen_local /recv_procs_gen /smc_interpreter.step /=.
      rewrite nth_mkseq // Hj_ne /=.
      have -> : j.-1 = 0%N by rewrite Hj1'.
      rewrite Hf /=.
      by rewrite Haf.
    + (* j >= 2: use rp_behind *)
      have [sv0 [f [_ Hf]]] := (rp_behind rp) Hj2.
      rewrite -/bg -/j in Hf.
      exists f. rewrite /bg_s /recv_procs_gen_local /recv_procs_gen /smc_interpreter.step /=.
      rewrite nth_mkseq // Hj_ne Hf /=.
      by rewrite Haf.
  have Hprog_s : @has_progress (std_data AHE) (ps_procs (send_st j bg_s))
    by apply send_has_progress_gen.
  have Hbg_next : bg_s j.+1 = relay_body_local (inord j.+1).
    rewrite /bg_s. apply bg_relay_ahead_recv => //.
    exact: (rp_ahead rp (ltnSn j) Hjn).
  (* send → recv(j+1) *)
  set bg' := fun i => (step (send_procs_gen_local j bg_s) [::] i.+1).1.1.
  have Hstep_sr : one_step_procs (ps_procs (send_st j bg_s)) =
    ps_procs (recv_st (inord j.+1) bg') by apply step_ok_send_recv_explicit.
  have Hinord : (inord j.+1 : 'I_n_relay.+1) = j.+1 :> nat by rewrite inordK.
  (* Chain: recv → send → recv' via KnownRetStep *)
  have Hprog_r := @recv_has_progress_gen AHE ek n_relay dk dk_relay relays
    Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay r2_relay j bg.
  suff Hks2s : known_ret_state (send_st j bg_s).
    exact (KnownRetStep Hks2s Hstep_rs' Hprog_r (recv_not_terminated_gen j bg)).
  suff Hks2_recv' : known_ret_state (recv_st (inord j.+1) bg').
    exact (KnownRetStep Hks2_recv' Hstep_sr Hprog_s (send_not_terminated_gen j bg_s)).
  (* Apply IH to next recv_phase via mk_recv_next_exists *)
  have [rp' [Hrpj Hrpbg]] := mk_recv_next_exists Hjn.
  have Hnj : (next_j Hjn : nat) = j.+1 by rewrite /next_j inordK.
  have Hjk' : (rp_j rp' + k = n_relay)%N.
    rewrite Hrpj Hnj.
    by rewrite addSn -addnS; exact Hjk.
  have Hks2' := IH rp' Hjk'.
  rewrite Hrpj Hrpbg in Hks2'.
  (* bg'_of rp and bg' are definitionally equal *)
  suff -> : recv_st (inord j.+1) bg' = recv_st (next_j Hjn) (bg'_of rp) by [].
  by rewrite /bg'_of /bg_s_of /= -/bg -/j /bg_s.
Qed.

(* mk_recv_init: initial recv_phase at j=0 — all frontier fields vacuous *)
Definition mk_recv_init : recv_phase.
Proof.
refine (@MkRecvPhase AHE ek n_relay dk_relay u r rand_a v_relay r1_relay r2_relay ord0 (r2_relay ord0) bg_init_local _ _ _ _ _ _ _).
- move=> i Hi0 Hi. by rewrite /bg_init_local /bg_init.
- by move=> /=.
- by move=> i.
- by [].
- by move/eqP.
- by [].
- by move/eqP.
Defined.

(* known_ret_recv_at_j0: the initial recv state is in known_ret_state. *)
Lemma known_ret_recv_at_j0 : known_ret_state (st_recv_local ord0).
Proof.
exact (@recv_phase_to_known n_relay mk_recv_init (add0n _)).
Qed.

(* known_ret_state_terminal: if a known_ret_state is all-terminated,
   its process list is that of st_ret *)
Lemma known_ret_state_terminal st :
  known_ret_state st -> @all_terminated data (ps_procs st) ->
  ps_procs st = ps_procs st_ret_local.
Proof.
move=> Hks2 Hat.
case: Hks2 Hat.
- by [].
- move=> st0 st' _ _ _ Hnt Hat.
  by rewrite Hat in Hnt.
Qed.

(* Helper: known_ret_state for st_recv ord0.
   Requires chaining KnownRetStep through the full FSM:
     recv(0) → send_0 → recv(1) → ... → tail → ret.
   Each intermediate state is non-terminated (KnownRetStep),
   st_ret uses KnownRetBase base case.
   TODO: prove once full chain lemmas are added to dsdp_fsm.v. *)
Lemma known_ret_state_recv_at_j0 :
  known_ret_state (st_recv_local ord0).
Proof.
exact: known_ret_recv_at_j0.
Qed.

Lemma known_ret_state_to_known st :
  known_ret_state st -> known_state n_relay st.
Proof.
move=> Hks; elim: Hks.
- apply: KS_step.
  + exact: KS_done.
  + exact: step_ok_ret_done.
  + exact: ret_has_progress.
- move=> st0 st' _ IH Hstep Hprog _.
  exact: (KS_step IH Hstep Hprog).
Qed.

Lemma known_ret_state_has_progress st :
  known_ret_state st -> ~~ @all_terminated data (ps_procs st) ->
  @has_progress data (ps_procs st).
Proof.
move=> Hks Hnt; case: Hks Hnt.
- rewrite /= /ret_procs /all_terminated /=.
  by rewrite all_nseq /= orbT.
- by move=> st0 st' _ _ Hprog _ _.
Qed.

Lemma known_ret_state_step st :
  known_ret_state st -> ~~ @all_terminated data (ps_procs st) ->
  exists st', known_ret_state st' /\
              one_step_procs (ps_procs st) = ps_procs st'.
Proof.
move=> Hks Hnt; case: Hks Hnt.
- rewrite /= /ret_procs /all_terminated /=.
  by rewrite all_nseq /= orbT.
- move=> st0 st' Hks' Hstep _ _ _.
  exists st'; split => //.
Qed.

Lemma known_state_recv0 :
  known_state n_relay (st_recv_local ord0).
Proof. exact: (known_ret_state_to_known known_ret_state_recv_at_j0). Qed.

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
(* Uses known_ret_state to distinguish Ret from Finish at termination.          *)
(* KnownRetStep only applies to non-terminated states, so the first terminated   *)
(* successor must be KnownRetBase (Alice = Ret concrete_val), not KS2_done.       *)
(* ========================================================================== *)

Lemma fsm_ret_induction h (ps : n_parties.-tuple (proc data))
    (st : phase_state AHE) :
  known_ret_state st ->
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
  apply (known_ret_state_has_progress Hks).
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
- (* ps' is all_terminated — use known_ret_state_terminal *)
  exists ps', tr_new; split; first exact Hrs_new.
  split; first exact Hnt'.
  have Hnt2 : ~~ @all_terminated data (ps_procs st) by rewrite -Heq.
  have [st' [Hks' Hst'_eq]] := known_ret_state_step Hks Hnt2.
  have Hps'_st' : tval ps' = ps_procs st'.
    rewrite Hps'_eq Heq; exact Hst'_eq.
  have Hterm_st' : @all_terminated data (ps_procs st').
    by rewrite -Hps'_st'.
  (* known_ret_state has no KS2_done — only KnownRetBase and KnownRetStep.
     KnownRetStep requires ~~ all_terminated, contradiction.
     So st' must be KnownRetBase, giving nth 0 = Ret concrete_val. *)
  rewrite Hps'_st' (known_ret_state_terminal Hks' Hterm_st') /=.
  by [].
- (* ps' is NOT all_terminated — continue by IH *)
  have Hnt2 : ~~ @all_terminated data (ps_procs st) by rewrite -Heq.
  have [st' [Hks' Hst'_eq]] := known_ret_state_step Hks Hnt2.
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
