(* dsdp_fsm.v — Explicit FSM-Trace Architecture for N-party DSDP

   States = Record values bundling process list + trace fragment + correctness.
   Transitions = ONE inductive (phase_trans).

   Design:
   - Each state (st_init1, st_recv j, st_send j, ...) is a phase_state Record
     value carrying its process list, its Alice trace fragment, and a proof
     that the fragment matches the interpreter output.
   - The transition relation phase_trans connects states, with one constructor
     per FSM edge.
   - phase_trans_step_ok proves that one_step_procs on the source state's
     process list equals the target state's process list.

   FSM-TO-TRACE CONNECTION:
   Each state determines a specific trace fragment (from its Record field).
   Transitions follow a fixed order forced by the program structure.
   Induction on fuel accumulates fragments along the transition path.
   The full trace = concatenation of fragments in transition order.

   Self-contained: does not import dsdp_progress.v or dsdp_entropy_trace.v.
*)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
Require Import ssr_ext.
Require Import smc_interpreter smc_session_types smc_deadlock.
Require Import homomorphic_encryption.
Require Import dsdp_interface dsdp_session_types dsdp_program.
Require Import dsdp_pismc dsdp_nofail.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Section dsdp_fsm.

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
Let e_local := di_e DI.
Let d := di_d DI.
Let priv_key_local := di_priv_key DI.

(* ========================================================================== *)
(* Copied helpers from dsdp_progress.v / dsdp_pismc.v                         *)
(* These are the building blocks for defining concrete process lists.         *)
(* ========================================================================== *)

(* alice_foldr j: Alice's erased process starting from iteration j.
   Copied from dsdp_progress.v (section-local, not exported). *)
Definition alice_foldr (j : nat) : proc data :=
  foldr (fun (fi : 'I_n_relay.+1 * nat) (cont : proc data) =>
           @alice_erase_body AHE ek n_relay u r rand_a fi.1 fi.2 cont)
        (@alice_erase_tail AHE n_relay dk v0 u r)
        (drop j (zip relays (iota 0 (size relays)))).

(* relay_body j: relay j's erased body (the Send 0 ... structure).
   Copied from dsdp_progress.v (section-local, not exported). *)
Definition relay_body (j : 'I_n_relay.+1) : proc data :=
  let dk' := dk_relay j in
  let v' := v_relay j in
  let r1' := r1_relay j in
  let r2' := r2_relay j in
  if (j : nat) == 0 then
    @smc_interpreter.Send data alice_idx
      (e_local (@enc AHE (ek (nat_to_party_id j.+1)) v' r1'))
      (@std_Recv_dec AHE alice_idx dk' (fun m0 =>
        @std_Recv_enc AHE alice_idx (fun enc1 =>
          @smc_interpreter.Send data j.+2
            (e_local (@Emul AHE enc1 (@enc AHE (ek (nat_to_party_id j.+2)) m0 r2')))
            Finish)))
  else if (j : nat) == n_relay then
    @smc_interpreter.Send data alice_idx
      (e_local (@enc AHE (ek (nat_to_party_id j.+1)) v' r1'))
      (@std_Recv_dec AHE j dk' (fun m0 =>
        @smc_interpreter.Send data alice_idx
          (e_local (@enc AHE (ek alice_idx) m0 r2')) Finish))
  else
    @smc_interpreter.Send data alice_idx
      (e_local (@enc AHE (ek (nat_to_party_id j.+1)) v' r1'))
      (@std_Recv_enc AHE alice_idx (fun enc0 =>
        @std_Recv_dec AHE j dk' (fun m0 =>
          @smc_interpreter.Send data j.+2
            (e_local (@Emul AHE enc0 (@enc AHE (ek (nat_to_party_id j.+2)) m0 r2')))
            Finish))).

(* relay_after_send0 j: relay j's state after its initial Send 0 to Alice.
   This is the continuation sk from relay_body j = Send 0 v sk. *)
Definition relay_after_send0 (j : 'I_n_relay.+1) : proc data :=
  let dk' := dk_relay j in
  let v' := v_relay j in
  let r1' := r1_relay j in
  let r2' := r2_relay j in
  if (j : nat) == 0 then
    @std_Recv_dec AHE alice_idx dk' (fun m0 =>
      @std_Recv_enc AHE alice_idx (fun enc1 =>
        @smc_interpreter.Send data j.+2
          (e_local (@Emul AHE enc1 (@enc AHE (ek (nat_to_party_id j.+2)) m0 r2')))
          Finish))
  else if (j : nat) == n_relay then
    @std_Recv_dec AHE j dk' (fun m0 =>
      @smc_interpreter.Send data alice_idx
        (e_local (@enc AHE (ek alice_idx) m0 r2')) Finish)
  else
    @std_Recv_enc AHE alice_idx (fun enc0 =>
      @std_Recv_dec AHE j dk' (fun m0 =>
        @smc_interpreter.Send data j.+2
          (e_local (@Emul AHE enc0 (@enc AHE (ek (nat_to_party_id j.+2)) m0 r2')))
          Finish)).

Lemma relay_body_send0_cont (j : 'I_n_relay.+1) :
  relay_body j = Send 0
    (e_local (@enc AHE (ek (nat_to_party_id j.+1)) (v_relay j) (r1_relay j)))
    (relay_after_send0 j).
Proof.
rewrite /relay_body /relay_after_send0; by case: ifP => ?; [|case: ifP => ?].
Qed.

(* relay_after_send0 always starts with Recv *)
Lemma relay_after_send0_is_recv (j : 'I_n_relay.+1) :
  exists frm f, relay_after_send0 j = Recv frm f.
Proof.
rewrite /relay_after_send0 /std_Recv_dec /std_Recv_enc /Recv_param.
case: ifP => ?; [|case: ifP => ?]; by do 2 eexists.
Qed.

(* alice_enc j: the concrete ciphertext Alice sends in round j.
   Copied from dsdp_progress.v (section-local, not exported). *)
Definition alice_enc (j : 'I_n_relay.+1) : cipher AHE :=
  @Emul AHE
    (@Epow AHE (@enc AHE (ek (nat_to_party_id j.+1)) (v_relay j) (r1_relay j))
               (u (lift ord0 j)))
    (@enc AHE (ek (nat_to_party_id j.+1)) (r j) (rand_a j)).

(* Initial process list *)
Let procs := @dsdp_n_procs AHE ek n_relay relays dk v0 u r rand_a
  dk_relay v_relay r1_relay r2_relay.

(* D1: term j = u_{j+1} * v_relay_j + r_j *)
Definition term (j : 'I_n_relay.+1) : plain AHE :=
  u (lift ord0 j) * v_relay j + r j.

(* D2: Accumulated plaintext after relay chain processing *)
Fixpoint chain_acc (j : nat) : plain AHE :=
  match j with
  | 0 => term ord0 + term (inord 1)
  | j'.+1 => chain_acc j' + term (inord j.+1)
  end.

(* Concrete return value *)
Let concrete_val :=
  d (chain_acc n_relay.-1 -
     \sum_(j < n_relay.+1) r j + u ord0 * v0).

(* One-step function: advance all processes by one round.
   Corresponds to one iteration of interp_comp from dsdp_pismc.v. *)
Definition one_step_procs (ps : seq (proc data)) : seq (proc data) :=
  unzip1 (unzip1 [seq smc_interpreter.step ps [::] i | i <- iota 0 (size ps)]).

(* ========================================================================== *)
(* The Record: bundles process list + trace fragment + correctness proof       *)
(* ========================================================================== *)

Record phase_state := PhaseState {
  ps_procs  : seq (proc data);
  ps_frag   : seq data;
  ps_frag_ok : (smc_interpreter.step ps_procs [::] 0).1.2 = ps_frag;
}.

(* Local abbreviations matching dsdp_progress.v conventions *)
Let pSend := @smc_interpreter.Send data.
Let pRecvDec_local := @std_Recv_dec AHE.
Let pRecvEnc_local := @std_Recv_enc AHE.
Let enc_local := @enc AHE.

(* H4.5: relay erasure gives Init(dk, Init(v, relay_body j)) *)
Lemma relay_erase_eq (j : 'I_n_relay.+1) :
  erase_aproc (relay_aproc AHE ek n_relay j
    (dk_relay j) (v_relay j) (r1_relay j) (r2_relay j)) =
  Init (priv_key_local (dk_relay j)) (Init (d (v_relay j)) (relay_body j)).
Proof.
rewrite /relay_aproc /erase_aproc.
case: ifP => Hj0.
- change (erase (aproc_proc (mk_aproc (DParty_first AHE ek j.+1 j.+2
    (dk_relay j) (v_relay j) (r1_relay j) (r2_relay j))))) with
    (erase (DParty_first AHE ek j.+1 j.+2
    (dk_relay j) (v_relay j) (r1_relay j) (r2_relay j))).
  rewrite DParty_first_erase.
  rewrite /relay_body Hj0 /priv_key_local /d /e_local /enc_local /DI /=.
  by rewrite /nat_to_party_id.
case: ifP => Hjn.
- change (erase (aproc_proc (mk_aproc (DParty_last AHE ek j.+1 j
    (dk_relay j) (v_relay j) (r1_relay j) (r2_relay j))))) with
    (erase (DParty_last AHE ek j.+1 j
    (dk_relay j) (v_relay j) (r1_relay j) (r2_relay j))).
  rewrite DParty_last_erase.
  rewrite /relay_body Hj0 Hjn /priv_key_local /d /e_local /enc_local /DI /=.
  by rewrite /nat_to_party_id /alice_idx.
- change (erase (aproc_proc (mk_aproc (DParty_intermediate AHE ek j.+1
    alice_idx j j.+2 (dk_relay j) (v_relay j) (r1_relay j) (r2_relay j))))) with
    (erase (DParty_intermediate AHE ek j.+1 alice_idx j j.+2
    (dk_relay j) (v_relay j) (r1_relay j) (r2_relay j))).
  rewrite DParty_intermediate_erase.
  rewrite /relay_body Hj0 Hjn /priv_key_local /d /e_local /enc_local /DI /=.
  by rewrite /nat_to_party_id.
Qed.

(* H5: relay_body always starts with Send 0 *)
Lemma relay_body_is_send0 (j : 'I_n_relay.+1) :
  exists sk,
    relay_body j = Send 0
      (e_local (enc_local (ek (nat_to_party_id j.+1)) (v_relay j) (r1_relay j))) sk.
Proof.
rewrite /relay_body; case: ifP => ?; [|case: ifP => ?]; by eexists.
Qed.

(* H6: Alice's foldr at iteration j starts with Recv(j+1,...) *)
Lemma alice_body_at_recv (j : nat) (Hj : (j < n_relay.+1)%N) :
  exists f, alice_foldr j = Recv (Ordinal Hj).+1 f.
Proof.
rewrite /alice_foldr.
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

(* NEW-L2: alice_foldr n_relay.+1 = alice_erase_tail *)
Lemma alice_foldr_at_tail :
  alice_foldr n_relay.+1 = @alice_erase_tail AHE n_relay dk v0 u r.
Proof.
rewrite /alice_foldr drop_oversize //.
by rewrite size_zip size_iota minnn Hrelays.
Qed.

(* NEW-L3: alice_erase_tail starts with Recv(n_relay.+1, ...) *)
Lemma alice_tail_is_recv :
  exists f, @alice_erase_tail AHE n_relay dk v0 u r = Recv n_relay.+1 f.
Proof.
rewrite /alice_erase_tail /pRecvDec_local /std_Recv_dec /Recv_param.
by eexists.
Qed.

(* std_from_enc_e_local: extracting a ciphertext from e_local *)
Lemma std_from_enc_e_local (c : cipher AHE) :
  @std_from_enc AHE (e_local c) = Some c.
Proof. by rewrite /e_local /std_from_enc /DI /=. Qed.

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

(* ========================================================================== *)
(* Concrete process lists per state                                           *)
(* ========================================================================== *)

(* Helper: build a process list by specifying what each position holds.
   Position 0 = Alice, position j+1 = relay j. *)

(* done_procs: all positions Finish *)
Definition done_procs : seq (proc data) :=
  nseq n_relay.+2 Finish.

(* ret_procs: Alice returns concrete_val, all relays Finish *)
Definition ret_procs : seq (proc data) :=
  Ret concrete_val :: nseq n_relay.+1 Finish.

(* tail_procs rr: Alice waiting at tail, last relay sends result,
   all other relays Finish *)
Definition tail_procs (rr : rand AHE) : seq (proc data) :=
  alice_foldr n_relay.+1 ::
  nseq n_relay Finish ++
  [:: Send 0 (e_local (enc_local (ek alice_idx) (chain_acc n_relay.-1) rr)) Finish].

(* ========================================================================== *)
(* Parametric process lists for recv/send/drain phases                        *)
(*                                                                            *)
(* The relay states at non-active positions depend on the full protocol       *)
(* history (HE computations, forwarding chain, etc.).  Rather than defining   *)
(* these concrete states, we parametrize by a "background" function           *)
(* bg : nat -> proc data that gives each non-active relay's state.            *)
(*                                                                            *)
(* The step_ok lemmas are proved under a "NOP condition": bg values don't     *)
(* participate in any communication during the current step.                  *)
(* ========================================================================== *)

(* recv_procs_gen j bg: Alice awaiting relay j's response.
   Position 0: alice_foldr j (= Recv (j+1) f)
   Position j+1: relay_body j (= Send 0 ...) — the active relay
   Position i+1 for i != j: bg i — background (non-active) relays *)
Definition recv_procs_gen (j : 'I_n_relay.+1)
    (bg : nat -> proc data) : seq (proc data) :=
  alice_foldr j ::
  mkseq (fun i =>
    if (i == j :> nat) then relay_body (inord i)
    else bg i) n_relay.+1.

(* send_procs_gen j bg: Alice sending to relay at alice_send_dest j.
   Position 0: Send(dest(j), alice_enc(j), alice_foldr(j+1))
   Position j+1: relay_after_send0 j — relay j in post-Send-to-Alice state
   Position i+1 for i != j: bg i — background relays *)
Definition send_procs_gen (j : 'I_n_relay.+1)
    (bg : nat -> proc data) : seq (proc data) :=
  Send (alice_send_dest j) (e_local (alice_enc j)) (alice_foldr j.+1) ::
  mkseq (fun i =>
    if (i == j :> nat) then relay_after_send0 (inord i)
    else bg i) n_relay.+1.

(* drain_procs j rr bg: Draining (forwarding chain) phase.
   Position 0: alice_foldr (n_relay+1) — Alice waiting for final result
   Position j+1: active forwarder (Send to relay j+1)
   Position j+2: receiver (Recv from relay j)
   Position i+1 for i != j, i != j+1: bg i *)
Definition drain_procs_gen (j : 'I_n_relay.+1) (rr_drain : rand AHE)
    (bg : nat -> proc data) : seq (proc data) :=
  alice_foldr n_relay.+1 ::
  mkseq (fun i =>
    if (i == j :> nat) then
      Send j.+2 (e_local (enc_local (ek (nat_to_party_id j.+2))
                                     (chain_acc j) rr_drain)) Finish
    else if (i == j.+1 :> nat) then
      match bg j.+1 with
      | Recv _ f => Recv j.+1 f
      | _ => Finish
      end
    else bg i) n_relay.+1.

(* Initial background: all relays in their initial state *)
Definition bg_init : nat -> proc data :=
  fun i => relay_body (inord i).

(* recv_procs and send_procs_0 are specializations of the parametric versions *)
Definition recv_procs (j : 'I_n_relay.+1) : seq (proc data) :=
  recv_procs_gen j bg_init.

Definition send_procs_0 : seq (proc data) :=
  send_procs_gen ord0 bg_init.

(* For backward compatibility, keep send_procs_general as a Definition
   that matches the old signature but with correct content *)
Definition send_procs_general (j : 'I_n_relay.+1)
    (bg : nat -> proc data) : seq (proc data) :=
  send_procs_gen j bg.

(* drain_procs: backward-compatible alias *)
Definition drain_procs (j : 'I_n_relay.+1) (rr_drain : rand AHE)
    (bg : nat -> proc data) : seq (proc data) :=
  drain_procs_gen j rr_drain bg.

(* ========================================================================== *)
(* NOP condition: background relays don't interfere with active communication *)
(* ========================================================================== *)

(* A relay state p at position i+1 is a NOP in process list ps if
   stepping it returns false (no progress). *)
Definition is_nop (ps : seq (proc data)) (i : nat) : bool :=
  ~~ (smc_interpreter.step ps [::] i).2.

(* bg_nop_recv j bg: all background relays are NOPs in recv_procs_gen j bg.
   This ensures only the Alice-relay j pair fires during the recv step. *)
Definition bg_nop_recv (j : 'I_n_relay.+1) (bg : nat -> proc data) : Prop :=
  forall i, (i < n_relay.+1)%N -> i != (j : nat) ->
    is_nop (recv_procs_gen j bg) i.+1.

(* bg_nop_send j bg: all background relays are NOPs in send_procs_gen j bg. *)
Definition bg_nop_send (j : 'I_n_relay.+1) (bg : nat -> proc data) : Prop :=
  forall i, (i < n_relay.+1)%N -> i != (j : nat) ->
    is_nop (send_procs_gen j bg) i.+1.

(* ========================================================================== *)
(* Fragment correctness proofs (per state)                                    *)
(* ========================================================================== *)

Lemma frag_ok_done :
  (smc_interpreter.step done_procs [::] 0).1.2 = [::].
Proof. by rewrite /done_procs /step /=. Qed.

Lemma frag_ok_ret :
  (smc_interpreter.step ret_procs [::] 0).1.2 = [:: concrete_val].
Proof. by rewrite /ret_procs /step /=. Qed.

Lemma frag_ok_tail (rr : rand AHE) :
  (smc_interpreter.step (tail_procs rr) [::] 0).1.2 =
  [:: e_local (enc_local (ek alice_idx) (chain_acc n_relay.-1) rr)].
Proof.
rewrite /tail_procs alice_foldr_at_tail /alice_erase_tail
  /pRecvDec_local /std_Recv_dec /Recv_param /step /=.
by rewrite nth_cat size_nseq ltnn subnn /=.
Qed.

(* The fragment depends only on Alice (position 0) and relay j (position j+1),
   not on bg. So the proof works for any bg. *)
Lemma frag_ok_recv_gen (j : 'I_n_relay.+1) (bg : nat -> proc data) :
  (smc_interpreter.step (recv_procs_gen j bg) [::] 0).1.2 =
  [:: e_local (enc_local (ek (nat_to_party_id j.+1)) (v_relay j) (r1_relay j))].
Proof.
rewrite /recv_procs_gen /step /=.
have Hj := ltn_ord j.
have [f ->] := alice_body_at_recv Hj.
have -> : (Ordinal Hj).+1 = j.+1 :> nat by [].
rewrite /= nth_mkseq /=; last by [].
rewrite eqxx.
have [sk ->] := relay_body_is_send0 (inord (nat_of_ord j)).
rewrite inordK /=; last by exact (ltn_ord j).
by rewrite inord_val.
Qed.

Lemma frag_ok_recv (j : 'I_n_relay.+1) :
  (smc_interpreter.step (recv_procs j) [::] 0).1.2 =
  [:: e_local (enc_local (ek (nat_to_party_id j.+1)) (v_relay j) (r1_relay j))].
Proof. exact: frag_ok_recv_gen. Qed.

Lemma frag_ok_send_gen (j : 'I_n_relay.+1) (bg : nat -> proc data) :
  (smc_interpreter.step (send_procs_gen j bg) [::] 0).1.2 = [::].
Proof.
rewrite /send_procs_gen /step /=.
set X := nth _ _ _. by case: X => //= n0 f; case: ifP.
Qed.

Lemma frag_ok_send_0 :
  (smc_interpreter.step send_procs_0 [::] 0).1.2 = [::].
Proof. exact: frag_ok_send_gen. Qed.

(* Alice's drain fragment is [::] because Alice is Recv(n_relay.+1) and the
   relay at position n_relay.+1 is NOT sending to Alice (dst != 0).
   This requires that the relay at position n_relay.+1 is not Send 0.
   In the actual protocol, the last relay is always in Recv state during drain. *)
Lemma frag_ok_drain_gen (j : 'I_n_relay.+1) (rr_drain : rand AHE)
    (bg : nat -> proc data)
    (Hbg_safe : forall v k, bg n_relay <> Send 0 v k) :
  (smc_interpreter.step (drain_procs_gen j rr_drain bg) [::] 0).1.2 = [::].
Proof.
rewrite /drain_procs_gen alice_foldr_at_tail /alice_erase_tail
  /pRecvDec_local /std_Recv_dec /Recv_param /step /=.
set X := nth _ _ _.
rewrite /X nth_mkseq //=.
case: ifP => [/eqP Heq|Hneq1].
  by have -> : (j.+2 == 0%N) = false by [].
case: ifP => [/eqP Heq2|Hneq2].
  by case: (bg j.+1) => [d0 next|dst w next|frm f|d0| |] //=.
case Hbgn : (bg n_relay) => [d0 next|dst w next|frm f|d0| |] //=.
case: ifP => //= /eqP Hdst.
exfalso; by apply (Hbg_safe w next); rewrite -Hdst Hbgn.
Qed.

(* ========================================================================== *)
(* Concrete state definitions (Record instances)                              *)
(* ========================================================================== *)

Definition st_done : phase_state :=
  PhaseState frag_ok_done.

Definition st_ret : phase_state :=
  PhaseState frag_ok_ret.

Definition st_tail (rr : rand AHE) : phase_state :=
  PhaseState (frag_ok_tail rr).

Definition st_recv_gen (j : 'I_n_relay.+1) (bg : nat -> proc data) : phase_state :=
  PhaseState (frag_ok_recv_gen j bg).

Definition st_recv (j : 'I_n_relay.+1) : phase_state :=
  st_recv_gen j bg_init.

Definition st_send_gen (j : 'I_n_relay.+1) (bg : nat -> proc data) : phase_state :=
  PhaseState (frag_ok_send_gen j bg).

Definition st_send_0 : phase_state :=
  st_send_gen ord0 bg_init.

Definition st_drain_gen (j : 'I_n_relay.+1) (rr_drain : rand AHE)
    (bg : nat -> proc data)
    (Hbg_safe : forall v k, bg n_relay <> Send 0 v k) : phase_state :=
  PhaseState (frag_ok_drain_gen j rr_drain Hbg_safe).

(* ========================================================================== *)
(* Per-transition step correctness                                            *)
(* ========================================================================== *)

(* Parametric step_ok: recv(j) → send(j) under NOP condition on bg.
   The active pair (Alice at 0, relay j at j+1) fires.
   All other positions are NOPs (by bg_nop_recv). *)
Lemma step_ok_recv_send_gen (j : 'I_n_relay.+1) (bg : nat -> proc data) :
  bg_nop_recv j bg ->
  one_step_procs (ps_procs (st_recv_gen j bg)) =
  ps_procs (st_send_gen j bg).
Proof.
move=> Hnop.
set rp := recv_procs_gen j bg.
have Hszrp : size rp = n_relay.+2
  by rewrite /rp /recv_procs_gen /= size_map size_iota.
have Hj := ltn_ord j.
have Hinord : inord (nat_of_ord j) = j :> 'I_n_relay.+1 by exact: inord_val.
have [f Haf] := alice_body_at_recv Hj.
have HjO : Ordinal Hj = j by apply val_inj.
(* Helper: NOP means step returns the process at that position *)
have Hnop_step : forall i, (i < n_relay.+1)%N -> i != (j : nat) ->
  (step rp [::] i.+1).1.1 = bg i.
  move=> i Hi Hneq.
  have Hnopi := Hnop i Hi Hneq.
  rewrite /is_nop in Hnopi.
  rewrite /rp /recv_procs_gen /step /= in Hnopi |- *.
  rewrite nth_mkseq in Hnopi |- *; try exact Hi.
  rewrite (negbTE Hneq) in Hnopi |- *.
  move: Hnopi.
  case: (bg i) => [d0 next|dst w next|frm ff|d0| |] //=.
    case: (nth _ _ dst) => [? ?|? ? ?|? ?|?| |] //=.
    by case: ifP.
    case: (nth _ _ frm) => [? ?|? ? ?|? ?|?| |] //=.
    by case: ifP.
(* Step at position j+1: relay j fires *)
have Hstepj : (step rp [::] j.+1).1.1 = relay_after_send0 j.
  rewrite /rp /recv_procs_gen /step /= nth_mkseq; last by [].
  rewrite eqxx (relay_body_send0_cont (inord j)) Hinord /=.
  rewrite Haf HjO /=.
  by rewrite eqxx.
(* Step at position 0: Alice *)
have Hf : forall c, f (e_local c) =
  Send (alice_send_dest j)
    (e_local (Emul (Epow c (u (lift ord0 j)))
                   (enc (ek (nat_to_party_id j.+1)) (r j) (rand_a j))))
    (alice_foldr j.+1).
  move=> c; move: (Haf).
  rewrite /alice_foldr.
  set zipped := zip relays (iota 0 (size relays)).
  have Hsz' : (j < size zipped)%N
    by rewrite /zipped size_zip size_iota minnn Hrelays.
  rewrite (drop_nth (ord0, 0) Hsz').
  rewrite nth_zip; last by rewrite /zipped size_iota Hrelays.
  rewrite (Hrelays_id (Ordinal Hj)).
  have -> : (iota 0 (size relays))`_j = (j : nat)
    by rewrite /= nth_iota // Hrelays.
  rewrite /= /alice_erase_body /pRecvEnc_local /std_Recv_enc /Recv_param /=.
  move=> [Hfeq]; rewrite -Hfeq /= /e_local /= /std_from_enc /DI /=.
  congr (Send _ _ _). congr (std_e _). by rewrite HjO.
have Hstep0 : (step rp [::] 0).1.1 =
  Send (alice_send_dest j) (e_local (alice_enc j)) (alice_foldr j.+1).
  rewrite /rp /recv_procs_gen /step /= Haf /= nth_mkseq; last by [].
  rewrite eqxx (relay_body_send0_cont (inord j)) Hinord /=.
  by rewrite Hf /alice_enc /nat_to_party_id.
(* Main goal: eq_from_nth *)
rewrite /one_step_procs /ps_procs /st_recv_gen -/rp Hszrp
        /ps_procs /st_send_gen /send_procs_gen.
rewrite /unzip1 -2!map_comp.
apply (@eq_from_nth _ (@Finish data)).
  by rewrite size_map size_iota /= size_map size_iota.
move=> i.
rewrite size_map size_iota => Hi.
rewrite (nth_map 0) ?size_iota // nth_iota // add0n.
rewrite /comp /=.
case: i Hi => [|i] Hi.
  by rewrite Hstep0.
rewrite /= nth_mkseq; last by rewrite ltnS in Hi.
case Heq : (i == (j : nat)).
  move/eqP: Heq => Heq; subst i.
  by rewrite Hinord Hstepj.
have Hilt : (i < n_relay.+1)%N by rewrite ltnS in Hi.
have Hineq : i != (j : nat) by rewrite Heq.
by rewrite Hnop_step.
Qed.

(* Special case: recv(0) → send_0 is the parametric lemma with bg_init *)
Lemma step_ok_recv_send0 :
  one_step_procs (ps_procs (st_recv ord0)) = ps_procs st_send_0.
Proof.
apply step_ok_recv_send_gen.
move=> i Hi Hneq.
rewrite /is_nop /recv_procs_gen /step /=.
have [f Haf] := alice_body_at_recv (ltn_ord (@ord0 n_relay)).
rewrite nth_mkseq; last by [].
have -> : (i == 0 :> nat) = false by rewrite (negbTE Hneq).
rewrite /bg_init.
rewrite (relay_body_send0_cont (inord i)) /=.
rewrite Haf /=.
have -> : (Ordinal (ltn_ord ord0)).+1 = 1 :> nat by [].
have -> : (1 == i.+1) = false.
  by have -> : (1 = 0.+1) by []; rewrite eqSS eq_sym (negbTE Hneq).
by [].
Unshelve. exact 0.
Qed.

(* Parametric step_ok: recv(j) → send(j) for j >= 1 *)
Lemma step_ok_recv_send (j : 'I_n_relay.+1) (bg : nat -> proc data) :
  (1 <= j)%N ->
  bg_nop_recv j bg ->
  one_step_procs (ps_procs (st_recv_gen j bg)) =
  ps_procs (st_send_gen j bg).
Proof. move=> _ Hnop; exact: step_ok_recv_send_gen. Qed.

(* Parametric step_ok: send(j) → next state under NOP condition.
   The active pair is Alice (Send to alice_send_dest j) and the relay
   at that position. *)
Lemma step_ok_send_gen (j : 'I_n_relay.+1) (bg : nat -> proc data)
    (target_relay : proc data)
    (Htarget : nth (@Finish data) (send_procs_gen j bg) (alice_send_dest j) =
               target_relay)
    (Htarget_recv : exists frm f, target_relay = Recv frm f /\ frm == 0) :
  bg_nop_send j bg ->
  (smc_interpreter.step (send_procs_gen j bg) [::] 0).2 = true.
Proof.
move=> _.
rewrite /send_procs_gen /step /=.
have Hlt : (alice_send_dest j < n_relay.+2)%N.
  rewrite /alice_send_dest /maxn.
  case: ifP => _ //.
  by apply ltn_trans with n_relay.+1; [exact: ltn_ord | exact: ltnSn].
have Hsd : nth (default_proc data)
  (Send (alice_send_dest j) (e_local (alice_enc j)) (alice_foldr j.+1) ::
   mkseq (fun i => if i == j then relay_after_send0 (inord i) else bg i)
         n_relay.+1)
  (alice_send_dest j) = target_relay.
  rewrite -(Htarget) /send_procs_gen.
  apply set_nth_default.
  by rewrite /= /mkseq size_map size_iota.
rewrite Hsd.
have [frm [ff [Heq Hfrm]]] := Htarget_recv.
rewrite Heq /=.
by move/eqP: Hfrm => ->.
Qed.

(* Helper: n.+1 <> n for any nat n *)
Lemma neq_succn (n : nat) : n.+1 = n -> False.
Proof. by move=> H; have := congr1 (subn^~ n) H; rewrite subSnn subnn. Qed.

Lemma step_ok_tail_ret (rr : rand AHE) :
  one_step_procs (ps_procs (st_tail rr)) = ps_procs st_ret.
Proof.
rewrite /one_step_procs /= size_cat size_nseq /= addn1.
set aet := alice_foldr n_relay.+1.
rewrite /tail_procs -/aet.
have Haet : aet = Recv n_relay.+1
  (oapp (fun m0 : plain AHE =>
    Ret (d (m0 - \sum_(j < n_relay.+1) r j + u ord0 * v0)))
    Fail \o (obind (dec dk) \o @std_from_enc AHE)).
  rewrite /aet alice_foldr_at_tail /alice_erase_tail.
  by rewrite /pRecvDec_local /std_Recv_dec /Recv_param /d /DI /=.
rewrite Haet /step /= nth_cat size_nseq.
have -> : (n_relay < n_relay)%N = false by rewrite ltnn.
rewrite subnn /=.
rewrite /enc_local key_alice (@enc_dec.dec_correct AHE) /=.
rewrite /ret_procs /concrete_val; congr cons.
rewrite nth_cat size_nseq Hn_relay nth_nseq Hn_relay /=; congr cons.
set ps := (Recv _ _ :: nseq n_relay Finish ++ [:: Send 0 _ Finish]).
rewrite /unzip1 -map_comp -map_comp.
suff Hfst : forall i, i \in iota 2 n_relay ->
  (step ps [::] i).1.1 = @Finish data.
  transitivity [seq @Finish data | _ <- iota 2 n_relay].
    by apply eq_in_map => i Hi; exact: Hfst.
  have Hmc : forall (T T' : Type) (c : T') (s : seq T),
    [seq c | _ <- s] = nseq (size s) c
    by move=> T T' c; elim => //= a s0 ->.
  by rewrite Hmc size_iota.
move=> i; rewrite mem_iota => /andP [Hi2 Hin].
rewrite /step /ps /=.
case: i Hi2 Hin => [//|[//|i']] _ Hin /=.
rewrite nth_cat size_nseq.
case: ltnP => Hi'; first by rewrite nth_nseq Hi'.
have Hi'eq : i'.+1 = n_relay.
  by apply anti_leq; rewrite Hi' andbT -(@ltn_add2r 2) addn2 addnC.
by rewrite Hi'eq subnn /= eqxx.
Qed.

Lemma step_ok_ret_done :
  one_step_procs (ps_procs st_ret) = ps_procs st_done.
Proof.
rewrite /one_step_procs /= size_nseq /done_procs.
have Hunz : forall m (p : proc data) (t : seq data) (b : bool),
  unzip1 (unzip1 (nseq m (p, t, b))) = nseq m p
  by elim => //= m' IH p t b; congr cons.
have Hmc : forall (T T' : Type) (c : T') (s : seq T),
  [seq c | _ <- s] = nseq (size s) c
  by move=> T T' c; elim => //= a s0 ->.
suff -> : [seq step ret_procs [::] i | i <- iota 2 n_relay] =
  nseq n_relay (@Finish data, @nil data, false).
  by congr cons; congr cons; rewrite Hunz.
transitivity [seq (@Finish data, @nil data, false) | _ <- iota 2 n_relay];
  last by rewrite Hmc size_iota.
apply eq_in_map => i; rewrite mem_iota => /andP [Hi2 Hin].
rewrite /step /ret_procs /=.
case: i Hi2 Hin => [//|[//|i']] _ Hin /=.
rewrite nth_nseq.
by have -> : (i' < n_relay)%N = true
  by rewrite -(@ltn_add2r 2) addn2 addnC.
Qed.

(* ========================================================================== *)
(* Missing step_ok: send → recv, send → drain, drain → drain, drain → tail   *)
(* These prove extensional list equality for the remaining transitions.       *)
(* ========================================================================== *)

(* send(j) → recv(j+1): general send→recv transition.
   Requires: j < n_relay (not the last), NOP condition on bg,
   the target position has a Recv from Alice,
   and the next relay is still in its initial state. *)
Lemma step_ok_send_recv_gen (j : 'I_n_relay.+1) (bg : nat -> proc data) :
  (j < n_relay)%N ->
  bg_nop_send j bg ->
  (exists f, nth (@Finish data) (send_procs_gen j bg) (alice_send_dest j) =
             Recv 0 f) ->
  bg j.+1 = relay_body (inord j.+1) ->
  exists bg',
    one_step_procs (ps_procs (st_send_gen j bg)) =
    ps_procs (st_recv_gen (inord j.+1) bg').
Proof.
move=> Hjn Hnop [ff Hrecv] Hbg_next.
set sp := send_procs_gen j bg.
have Hszsp : size sp = n_relay.+2
  by rewrite /sp /send_procs_gen /= size_map size_iota.
have Hinord : (inord j.+1 : 'I_n_relay.+1) = j.+1 :> nat
  by rewrite inordK // ltnS.
exists (fun i => (step sp [::] i.+1).1.1).
rewrite /one_step_procs /ps_procs /st_send_gen -/sp Hszsp
        /st_recv_gen /recv_procs_gen /unzip1 -2!map_comp.
apply (@eq_from_nth _ (@Finish data)).
  by rewrite size_map size_iota /= size_map size_iota.
move=> i; rewrite size_map size_iota => Hi.
rewrite (nth_map 0) ?size_iota // nth_iota // add0n /comp /=.
case: i Hi => [|i] Hi.
  (* Position 0: Alice's Send fires *)
  rewrite /= /step /sp /send_procs_gen /=.
  have -> : nth (default_proc data)
    (Send (alice_send_dest j) (e_local (alice_enc j)) (alice_foldr j.+1) ::
     mkseq (fun i => if i == j then relay_after_send0 (inord i) else bg i)
       n_relay.+1)
    (alice_send_dest j) = Recv 0 ff.
    rewrite -(Hrecv) /send_procs_gen; apply set_nth_default.
    rewrite /= size_map size_iota /alice_send_dest /maxn.
    case: ifP => _ //.
    by apply ltn_trans with n_relay.+1; [exact: ltn_ord | exact: ltnSn].
  by rewrite /= Hinord.
(* Position i.+1: relay positions *)
rewrite /= nth_mkseq; last by rewrite ltnS in Hi.
case Heq : (i == (inord j.+1 : 'I_n_relay.+1) :> nat).
  (* i == j.+1: relay_body at position j.+2, NOP since Alice is Send *)
  move/eqP: Heq => Heq; subst i.
  rewrite Hinord /sp /step /send_procs_gen /=.
  have Hjlt : (j < size (iota 1 n_relay))%N by rewrite size_iota.
  rewrite (nth_map 0) // nth_iota // add1n.
  have -> : (j.+1 == j :> nat) = false by rewrite gtn_eqF.
  rewrite Hbg_next (relay_body_send0_cont (inord j.+1)) /=.
  by [].
by [].
Qed.

(* send_0 → recv(1): special case with bg_init *)
Lemma step_ok_send0_recv1 :
  (0 < n_relay)%N ->
  exists bg',
    one_step_procs (ps_procs st_send_0) =
    ps_procs (st_recv_gen (inord 1) bg').
Proof.
move=> Hn1.
apply (step_ok_send_recv_gen (j := ord0) (bg := bg_init)) => //.
- move=> i Hi Hneq.
  rewrite /is_nop /send_procs_gen /step /=.
  rewrite nth_mkseq; last by [].
  have -> : (i == 0 :> nat) = false by rewrite (negbTE Hneq).
  rewrite /bg_init (relay_body_send0_cont (inord i)) /=.
  have [frm [f Hras]] := relay_after_send0_is_recv (inord 0 : 'I_n_relay.+1).
  by [].
- rewrite /send_procs_gen /alice_send_dest /= /mkseq /=.
  rewrite /relay_after_send0 inordK //=.
  rewrite /pRecvDec_local /std_Recv_dec /Recv_param /=.
  by eexists.
Qed.

(* Helper: nth on cons with positive index *)
Lemma nth_cons_pos (T : Type) (x0 : T) (a : T) (s : seq T) (n : nat) :
  (0 < n)%N -> nth x0 (a :: s) n = nth x0 s n.-1.
Proof. by case: n. Qed.

(* send(last) → drain(0): last send triggers drain phase.
   Requires: NOP condition, the target has matching Recv,
   and bg(0) already has the right Send form for drain. *)
Lemma step_ok_send_last_drain (bg : nat -> proc data) :
  bg_nop_send ord_max bg ->
  (exists f, nth (@Finish data) (send_procs_gen (@ord_max n_relay) bg)
             (alice_send_dest (@ord_max n_relay)) = Recv 0 f) ->
  (* bg(0) is the drain-phase Send from relay 0 to relay 1 *)
  (exists rr0, bg 0 = Send 2
    (e_local (enc_local (ek (nat_to_party_id 2)) (chain_acc 0) rr0)) Finish) ->
  (* bg(1) is a Recv from position 1 (next drain receiver) *)
  (exists f1, bg 1 = Recv 1 f1) ->
  (* bg n_relay does not Send to Alice *)
  (forall v k, bg n_relay.-1 <> Send 0 v k) ->
  exists (rr' : rand AHE) (bg' : nat -> proc data)
         (Hsafe : forall v k, bg' n_relay <> Send 0 v k),
    one_step_procs (ps_procs (@st_send_gen (@ord_max n_relay) bg)) =
    ps_procs (@st_drain_gen ord0 rr' bg' Hsafe).
Proof.
move=> Hnop [ff Hrecv] [rr0 Hbg0] [f1 Hbg1] Hbg_safe.
set sp := send_procs_gen ord_max bg.
have Hszsp : size sp = n_relay.+2
  by rewrite /sp /send_procs_gen /= size_map size_iota.
have Hmaxn : alice_send_dest (@ord_max n_relay) = n_relay.
  rewrite /alice_send_dest /maxn.
  case: ltnP => H //.
  by apply anti_leq; rewrite Hn_relay H.
(* Derive bg n_relay.-1 = Recv 0 ff from Hrecv *)
have Hbgnr : bg n_relay.-1 = Recv 0 ff.
  move: Hrecv; rewrite Hmaxn /sp /send_procs_gen.
  rewrite nth_cons_pos //.
  rewrite nth_mkseq; last by apply (leq_ltn_trans (leq_pred _)).
  by rewrite ltn_eqF; last rewrite prednK.
(* NOP helper *)
have Hnop_step : forall i, (i < n_relay.+1)%N -> i != (ord_max : 'I_n_relay.+1) :> nat ->
  (step sp [::] i.+1).1.1 = bg i.
  move=> i Hi Hneq.
  have Hnopi := Hnop i Hi Hneq.
  rewrite /is_nop in Hnopi.
  rewrite /sp /send_procs_gen /step /= in Hnopi |- *.
  rewrite nth_mkseq in Hnopi |- *; try exact Hi.
  rewrite (negbTE Hneq) in Hnopi |- *.
  move: Hnopi.
  case: (bg i) => [d0 next|dst w next|frm ff0|d0| |] //=.
    case: (nth _ _ dst) => [? ?|? ? ?|? ?|?| |] //=.
    by case: ifP.
    case: (nth _ _ frm) => [? ?|? ? ?|? ?|?| |] //=.
    by case: ifP.
(* Step at position 0: Alice fires *)
have Hstep0 : (step sp [::] 0).1.1 = alice_foldr n_relay.+1.
  rewrite /sp /send_procs_gen /step /=.
  have -> : nth (default_proc data)
    (Send (alice_send_dest n_relay) (e_local (alice_enc ord_max))
       (alice_foldr n_relay.+1) ::
     mkseq (fun i => if i == n_relay then relay_after_send0 (inord i) else bg i)
       n_relay.+1)
    (alice_send_dest n_relay) = Recv 0 ff.
    have Hasd : alice_send_dest n_relay = alice_send_dest (@ord_max n_relay) by [].
    rewrite Hasd -(Hrecv) /send_procs_gen; apply set_nth_default.
    rewrite /= size_map size_iota Hmaxn.
    by apply ltn_trans with n_relay.+1; [exact: ltnSn | exact: ltnSn].
  by [].
(* Existentials *)
exists rr0.
exists (fun i => (step sp [::] i.+1).1.1).
(* Hsafe: step at n_relay.+1 is NOP, result is Recv, not Send 0 *)
have Hstep_last_nop : (step sp [::] n_relay.+1).2 = false.
  rewrite /sp /send_procs_gen /step /=.
  rewrite nth_mkseq; last by [].
  rewrite eqxx /relay_after_send0.
  have Hn0 : (n_relay == 0) = false by rewrite eqn0Ngt Hn_relay.
  rewrite inordK //= Hn0 eqxx /pRecvDec_local /std_Recv_dec /Recv_param /=.
  have -> : nth (default_proc data)
    (Send (alice_send_dest n_relay) (e_local (alice_enc ord_max))
       (alice_foldr n_relay.+1) ::
     mkseq (fun i => if i == n_relay then relay_after_send0 (inord i) else bg i)
       n_relay.+1)
    n_relay = Recv 0 ff.
    have Hasd : alice_send_dest n_relay = alice_send_dest (@ord_max n_relay) by [].
    have Hnr : nth Finish sp n_relay = Recv 0 ff.
      move: Hrecv; by rewrite Hmaxn.
    rewrite /sp /send_procs_gen in Hnr.
    rewrite -(Hnr); apply set_nth_default.
    rewrite /= size_map size_iota.
    by apply ltn_trans with n_relay.+1; [exact: ltnSn | exact: ltnSn].
  by [].
have Hsafe_pf : forall v k, (step sp [::] n_relay.+1).1.1 <> Send 0 v k.
  move=> v k.
  rewrite /sp /send_procs_gen /step /=.
  rewrite nth_mkseq; last by [].
  rewrite eqxx /relay_after_send0.
  have Hn0 : (n_relay == 0) = false by rewrite eqn0Ngt Hn_relay.
  rewrite inordK //= Hn0 eqxx /pRecvDec_local /std_Recv_dec /Recv_param /=.
  have -> : nth (default_proc data)
    (Send (alice_send_dest n_relay) (e_local (alice_enc ord_max))
       (alice_foldr n_relay.+1) ::
     mkseq (fun i => if i == n_relay then relay_after_send0 (inord i) else bg i)
       n_relay.+1)
    n_relay = Recv 0 ff.
    have Hnr : nth Finish sp n_relay = Recv 0 ff.
      move: Hrecv; by rewrite Hmaxn.
    rewrite /sp /send_procs_gen in Hnr.
    rewrite -(Hnr); apply set_nth_default.
    rewrite /= size_map size_iota.
    by apply ltn_trans with n_relay.+1; [exact: ltnSn | exact: ltnSn].
  by [].
exists Hsafe_pf.
(* Main goal: eq_from_nth *)
rewrite /one_step_procs /ps_procs /st_send_gen -/sp Hszsp
        /st_drain_gen /drain_procs_gen /unzip1 -2!map_comp.
apply (@eq_from_nth _ (@Finish data)).
  by rewrite size_map size_iota /= size_map size_iota.
move=> i; rewrite size_map size_iota => Hi.
rewrite (nth_map 0) ?size_iota // nth_iota // add0n /comp /=.
case: i Hi => [|i] Hi.
  (* Position 0: Alice *)
  by rewrite Hstep0.
(* Position i.+1: relay positions *)
rewrite /= nth_mkseq; last by rewrite ltnS in Hi.
case Heq0 : (i == 0 :> nat).
  (* i == 0: drain active sender position *)
  move/eqP: Heq0 => Heq0; subst i.
  have H0lt : (0 < n_relay.+1)%N by [].
  have H0nr : (0 : nat) != (ord_max : 'I_n_relay.+1) :> nat.
    by rewrite eq_sym eqn0Ngt Hn_relay.
  by rewrite (Hnop_step 0 H0lt H0nr) Hbg0.
case Heq1 : (i == 1 :> nat).
  (* i == 1: drain receiver position *)
  move/eqP: Heq1 => Heq1; subst i.
  (* need (step sp [::] 2).1.1 = match (step sp [::] 2).1.1 with Recv _ f => Recv 1 f | ... *)
  (* Derive 1 != n_relay from Hbgnr + Hbg0 contradiction *)
  have Hineq1 : (1 : nat) != (ord_max : 'I_n_relay.+1) :> nat.
    apply/negP => /eqP Hnr1.
    have Hnr1' : n_relay = 1 by rewrite /= in Hnr1; exact (esym Hnr1).
    by move: Hbgnr; rewrite Hnr1' /= Hbg0.
  rewrite Hnop_step // Hbg1 /=.
  by [].
(* All other positions: NOP and bg match *)
case Heqnr : (i == (ord_max : 'I_n_relay.+1) :> nat).
  (* i == n_relay: this is the position that was the receiver of Alice's send.
     After stepping, it became ff(alice_enc ord_max).
     In drain_procs_gen, this position is bg' i where i != 0, i != 1. *)
  by [].
by [].
Qed.

(* drain(j) → drain(j+1): relay j forwards cipher to j+1.
   The callback hypothesis says what bg j.+1 does when receiving the chain.
   Hcallback: relay j+1 receives, computes, and produces a Send. *)
Lemma step_ok_drain_drain_gen (j : 'I_n_relay.+1) (rr : rand AHE)
    (bg : nat -> proc data)
    (Hsafe : forall v k, bg n_relay <> Send 0 v k) :
  let cipher_j := e_local (enc_local (ek (nat_to_party_id j.+2))
                                      (chain_acc j) rr) in
  (j.+2 < n_relay.+1)%N ->
  (* bg j.+1 is a Recv whose callback produces a Send *)
  (exists f rr_next,
     bg j.+1 = Recv (j : nat) f /\
     f cipher_j =
       Send j.+3
         (e_local (enc_local (ek (nat_to_party_id j.+3))
                              (chain_acc j.+1) rr_next))
         Finish) ->
  (* bg j.+2 is a Recv from j.+1 (for the next drain receiver) *)
  (exists f_next, bg j.+2 = Recv j.+2 f_next) ->
  (* Finish (from stepped relay j) doesn't Send to Alice *)
  (forall v k, bg j <> Send 0 v k) ->
  (* All non-active positions are NOPs *)
  (forall i, (i < n_relay.+1)%N -> i != (j : nat) -> i != j.+1 ->
     is_nop (drain_procs_gen j rr bg) i.+1) ->
  exists (rr' : rand AHE) (bg' : nat -> proc data)
         (Hsafe' : forall v k, bg' n_relay <> Send 0 v k),
    one_step_procs (ps_procs (@st_drain_gen j rr bg Hsafe)) =
    ps_procs (@st_drain_gen (inord j.+1) rr' bg' Hsafe').
Proof.
move=> cipher_j Hjlt [f [rr_next [Hbg1 Hcallback]]] [f_next Hbg2] Hbg_safe_j Hnop.
set dp := drain_procs_gen j rr bg.
have Hszdp : size dp = n_relay.+2
  by rewrite /dp /drain_procs_gen /= size_map size_iota.
have Hinord : (inord j.+1 : 'I_n_relay.+1) = j.+1 :> nat
  by rewrite inordK // ltnS; exact (ltnW Hjlt).
have Hjn : (j : nat) != n_relay.
  rewrite neq_ltn; apply/orP; left.
  by apply (leq_trans (ltnSn _) (ltnW Hjlt)).
have Hj1n : j.+1 != n_relay
  by rewrite ltnS in Hjlt; rewrite neq_ltn; apply/orP; left.
(* NOP helper: background positions step to themselves *)
have Hnop_step : forall i, (i < n_relay.+1)%N -> i != (j : nat) -> i != j.+1 ->
  (step dp [::] i.+1).1.1 = bg i.
  move=> i Hi Hneq Hneq2.
  have Hnopi := Hnop i Hi Hneq Hneq2.
  rewrite /is_nop in Hnopi.
  rewrite /dp /drain_procs_gen /step /= in Hnopi |- *.
  rewrite nth_mkseq in Hnopi |- *; try exact Hi.
  rewrite (negbTE Hneq) in Hnopi |- *.
  rewrite (negbTE Hneq2) in Hnopi |- *.
  move: Hnopi.
  case: (bg i) => [d0 next|dst w next|frm ff|d0| |] //=.
    case: (nth _ _ dst) => [? ?|? ? ?|? ?|?| |] //=.
    by case: ifP.
    case: (nth _ _ frm) => [? ?|? ? ?|? ?|?| |] //=.
    by case: ifP.
(* Step at j+1: the Send fires, result is Finish *)
have Hstepj : (step dp [::] j.+1).1.1 = Finish.
  rewrite /dp /drain_procs_gen /step /= nth_mkseq; last exact (ltn_ord j).
  rewrite eqxx /=.
  have Hnthdst : nth (default_proc data)
    (drain_procs_gen j rr bg) j.+2 = Recv j.+1 f.
    rewrite /drain_procs_gen nth_cons_pos // nth_mkseq //.
    have -> : (j.+1 == (j : nat)) = false by rewrite gtn_eqF.
    by rewrite eqxx Hbg1.
  - by exact (ltnW Hjlt).
  - rewrite (nth_map 0) ?size_iota;
      last by apply (leq_trans (ltnSn _) (ltnW Hjlt)).
    rewrite nth_iota;
      last by apply (leq_trans (ltnSn _) (ltnW Hjlt)).
    rewrite add1n.
    have -> : (j.+1 == (j : nat)) = false by rewrite gtn_eqF.
    by rewrite eqxx Hbg1 /= eqxx.
(* Step at j+2: the Recv fires, result is f cipher_j *)
have Hstepj2 : (step dp [::] j.+2).1.1 = f cipher_j.
  rewrite /dp /drain_procs_gen /step nth_cons_pos // nth_mkseq //.
  have -> : (j.+1 == (j : nat)) = false by rewrite gtn_eqF.
  rewrite eqxx Hbg1 /=.
  change j.+2.-1 with j.+1.
  rewrite nth_mkseq; last exact (ltn_ord j).
  by rewrite eqxx /= eqxx /cipher_j.
  by exact (ltnW Hjlt).
(* Step at 0: Alice is NOP *)
have Hstep0 : (step dp [::] 0).1.1 = alice_foldr n_relay.+1.
  rewrite /dp /drain_procs_gen alice_foldr_at_tail /alice_erase_tail
    /pRecvDec_local /std_Recv_dec /Recv_param /step /=.
  set X := nth _ _ _.
  rewrite /X nth_mkseq //=.
  case: ifP => [/eqP Heq|Hneq1].
    by have -> : (j.+2 == 0%N) = false by [].
  case: ifP => [/eqP Heq2|Hneq2].
    by case: (bg j.+1) => [d0 next|dst w next|frm ff|d0| |] //=.
  case Hbgn : (bg n_relay) => [d0 next|dst w next|frm ff|d0| |] //=.
  - case: ifP => /eqP Hdst //.
    exfalso; apply (Hsafe w next); rewrite -Hdst; exact Hbgn.
(* Existentials *)
exists rr_next.
exists (fun i => (step dp [::] i.+1).1.1).
(* Safety *)
have Hsafe_pf : forall v k, (step dp [::] n_relay.+1).1.1 <> Send 0 v k.
  move=> v k.
  rewrite Hnop_step; first exact (Hsafe v k).
  - by [].
  - by rewrite eq_sym (negbTE Hjn).
  - by rewrite eq_sym (negbTE Hj1n).
exists Hsafe_pf.
(* Main goal: eq_from_nth *)
rewrite /one_step_procs /ps_procs /st_drain_gen -/dp Hszdp
        /drain_procs_gen /unzip1 -2!map_comp.
apply (@eq_from_nth _ (@Finish data)).
  by rewrite size_map size_iota /= size_map size_iota.
move=> i; rewrite size_map size_iota => Hi.
rewrite (nth_map 0) ?size_iota // nth_iota // add0n /comp /=.
case: i Hi => [|i] Hi.
  by rewrite Hstep0.
(* Position i.+1: relay positions *)
rewrite /= nth_mkseq; last by rewrite ltnS in Hi.
case Heqj1 : (i == (inord j.+1 : 'I_n_relay.+1) :> nat).
  move/eqP: Heqj1 => Heqj1; rewrite Heqj1 Hinord.
  by rewrite Hstepj2 Hcallback.
case Heqj2 : (i == (inord j.+1 : 'I_n_relay.+1).+1 :> nat).
  move/eqP: Heqj2 => Heqj2; rewrite Heqj2 Hinord.
  have Hj2neqj : j.+2 != (j : nat) by rewrite gtn_eqF.
  have Hj2neqj1 : j.+2 != j.+1 by rewrite gtn_eqF.
  rewrite Hnop_step // Hbg2 //.
by [].
Qed.

(* drain(last) → tail: last relay sends result to Alice.
   The callback hypothesis says what bg j.+1 produces. *)
Lemma step_ok_drain_tail_gen (j : 'I_n_relay.+1) (rr : rand AHE)
    (bg : nat -> proc data)
    (Hsafe : forall v k, bg n_relay <> Send 0 v k) :
  let cipher_j := e_local (enc_local (ek (nat_to_party_id j.+2))
                                      (chain_acc j) rr) in
  (j.+1 = n_relay)%N ->
  (* bg j.+1 is a Recv whose callback produces Send to Alice *)
  (exists f rr_next,
     bg j.+1 = Recv (j : nat) f /\
     f cipher_j =
       Send 0 (e_local (enc_local (ek alice_idx)
                                   (chain_acc n_relay.-1) rr_next))
              Finish) ->
  (* All non-active relay positions are Finish *)
  (forall i, (i < n_relay.+1)%N -> i != (j : nat) -> i != j.+1 -> bg i = Finish) ->
  exists rr',
    one_step_procs (ps_procs (@st_drain_gen j rr bg Hsafe)) =
    ps_procs (st_tail rr').
Proof.
move=> cipher_j Hjeq [f [rr_next [Hbg1 Hcallback]]] Hbg_finish.
set dp := drain_procs_gen j rr bg.
have Hszdp : size dp = n_relay.+2
  by rewrite /dp /drain_procs_gen /= size_map size_iota.
have Hstepj : (step dp [::] j.+1).1.1 = Finish.
  rewrite /dp /drain_procs_gen /step /= nth_mkseq; last exact (ltn_ord j).
  rewrite eqxx /=.
  have Hnthdst : nth (default_proc data)
    (drain_procs_gen j rr bg) j.+2 = Recv j.+1 f.
    rewrite /drain_procs_gen nth_cons_pos // nth_mkseq; last by rewrite Hjeq.
    have -> : (j.+1 == (j : nat)) = false by rewrite gtn_eqF.
    by rewrite eqxx Hbg1.
  - rewrite (nth_map 0) ?size_iota; last by rewrite Hjeq.
    rewrite nth_iota; last by rewrite Hjeq.
    rewrite add1n.
    have -> : (j.+1 == (j : nat)) = false by rewrite gtn_eqF.
    by rewrite eqxx Hbg1 /= eqxx.
have Hstepj2 : (step dp [::] j.+2).1.1 = f cipher_j.
  rewrite /dp /drain_procs_gen /step nth_cons_pos // nth_mkseq;
    last by rewrite Hjeq.
  have -> : (j.+1 == (j : nat)) = false by rewrite gtn_eqF.
  rewrite eqxx Hbg1 /=.
  change j.+2.-1 with j.+1.
  rewrite nth_mkseq; last exact (ltn_ord j).
  by rewrite eqxx /= eqxx /cipher_j.
have Hstep0 : (step dp [::] 0).1.1 = alice_foldr n_relay.+1.
  rewrite /dp /drain_procs_gen alice_foldr_at_tail /alice_erase_tail
    /pRecvDec_local /std_Recv_dec /Recv_param /step /=.
  set X := nth _ _ _.
  rewrite /X nth_mkseq //=.
  case: ifP => [/eqP Heq|Hneq1].
    by have -> : (j.+2 == 0%N) = false by [].
  case: ifP => [/eqP Heq2|Hneq2].
    by case: (bg j.+1) => [d0 next|dst w next|frm ff|d0| |] //=.
  have Hbgnr : bg n_relay = Finish.
    apply Hbg_finish; first by [].
    - by rewrite Hneq1.
    - by rewrite Hneq2.
  by rewrite Hbgnr.
exists rr_next.
rewrite /one_step_procs /ps_procs /st_drain_gen -/dp Hszdp
        /tail_procs /unzip1 -2!map_comp.
apply (@eq_from_nth _ (@Finish data)).
  rewrite size_map size_iota /= /tail_procs size_cat size_nseq /= addn1 //.
move=> i; rewrite size_map size_iota => Hi.
rewrite (nth_map 0) ?size_iota // nth_iota // add0n /comp /= /tail_procs.
case: i Hi => [|i] Hi.
  by rewrite Hstep0.
rewrite /= nth_cat size_nseq.
case: ltnP => Hinr.
  rewrite nth_nseq Hinr.
  rewrite /dp /drain_procs_gen /step /= nth_mkseq; last by rewrite ltnS in Hi.
  case Heqj : (i == (j : nat)).
    move/eqP: Heqj => Heqj; subst i.
    have Hnthdst : nth (default_proc data) dp j.+2 = Recv j.+1 f.
      rewrite /dp /drain_procs_gen nth_cons_pos // nth_mkseq;
        last by rewrite Hjeq.
      have -> : (j.+1 == (j : nat)) = false by rewrite gtn_eqF.
      by rewrite eqxx Hbg1.
    rewrite -/(dp) Hnthdst /= eqxx //.
  case Heqj1 : (i == j.+1).
    move/eqP: Heqj1 => Heqj1.
    exfalso; move: Hinr; rewrite Heqj1 Hjeq ltnn //.
  have Hbgi : bg i = Finish.
    apply Hbg_finish; first by rewrite ltnS in Hi.
    - by rewrite Heqj.
    - by rewrite Heqj1.
  by rewrite Hbgi.
have Hieq : i = n_relay.
  apply anti_leq; rewrite Hinr /= -ltnS.
  rewrite andbT; by rewrite ltnS in Hi.
rewrite Hieq subnn /=.
rewrite -Hjeq -/(dp) -/(step dp [::] j.+2) Hstepj2 Hcallback Hjeq //.
Qed.

(* ========================================================================== *)
(* Progress: every non-done state has progress                                *)
(* ========================================================================== *)

(* recv: Alice (Recv j+1) and relay j (Send 0) always form a matching pair *)
Lemma recv_has_progress_gen (j : 'I_n_relay.+1) (bg : nat -> proc data) :
  has_progress data (ps_procs (st_recv_gen j bg)).
Proof.
rewrite /has_progress /= /recv_procs_gen size_map size_iota.
set rp := alice_foldr j :: _.
suff H0 : (step rp [::] 0).2 = true by rewrite H0.
rewrite /step /rp /=.
have Hj := ltn_ord j.
have [f ->] := alice_body_at_recv Hj.
have -> : (Ordinal Hj).+1 = j.+1 :> nat by [].
rewrite /= nth_mkseq; last by [].
rewrite eqxx.
have [sk ->] := relay_body_is_send0 (inord (nat_of_ord j)).
rewrite inordK; last by exact (ltn_ord j).
by rewrite inord_val eqxx.
Qed.

Lemma recv_has_progress (j : 'I_n_relay.+1) :
  has_progress data (ps_procs (st_recv j)).
Proof. exact: recv_has_progress_gen. Qed.

(* send_0: Alice (Send 1) and relay 0 (Recv 0) form a matching pair *)
Lemma send_0_has_progress :
  has_progress data (ps_procs st_send_0).
Proof.
rewrite /has_progress /= /send_procs_gen size_map size_iota.
set sp := Send 1 _ _ :: _.
suff H0 : (step sp [::] 0).2 = true by rewrite H0.
rewrite /step /sp /=.
rewrite /relay_after_send0.
suff -> : @inord n_relay 0 = ord0
  by rewrite /pRecvDec_local /std_Recv_dec /Recv_param /= /alice_idx.
by apply val_inj; rewrite /= inordK.
Qed.

(* send_gen: Alice sends to alice_send_dest j; the receiver is either
   relay_after_send0 j (if dest = j+1) or bg(dest-1).
   For any bg where the receiver is a Recv from Alice, there is progress. *)
Lemma send_has_progress_gen (j : 'I_n_relay.+1) (bg : nat -> proc data) :
  (* The relay at alice_send_dest j starts with Recv 0 *)
  (exists f, nth (@Finish data) (send_procs_gen j bg) (alice_send_dest j) =
             Recv 0 f) ->
  has_progress data (ps_procs (st_send_gen j bg)).
Proof.
move=> [ff Hrecv].
rewrite /has_progress /= /send_procs_gen /= /mkseq size_map size_iota.
set sp := Send _ _ _ :: _.
suff H0 : (step sp [::] 0).2 = true by rewrite H0.
rewrite /step /sp /=.
have Hlt : (alice_send_dest j < n_relay.+2)%N.
  rewrite /alice_send_dest /maxn.
  case: ifP => _ //.
  by apply ltn_trans with n_relay.+1; [exact: ltn_ord | exact: ltnSn].
have Hsp : sp = send_procs_gen j bg by rewrite /sp /send_procs_gen /mkseq.
have -> : nth (default_proc data) sp (alice_send_dest j) = Recv 0 ff.
  rewrite Hsp -(Hrecv).
  apply set_nth_default.
  by rewrite /send_procs_gen /= /mkseq size_map size_iota.
by [].
Qed.

(* drain: relay j (Send j+2) and relay j+1 (Recv j+1) form a matching pair *)
Lemma drain_has_progress_gen (j : 'I_n_relay.+1) (rr_drain : rand AHE)
    (bg : nat -> proc data)
    (Hbg_safe : forall v k, bg n_relay <> Send 0 v k) :
  (j.+1 < n_relay.+1)%N ->
  (* relay j+1 in bg starts with Recv *)
  (exists frm f, bg j.+1 = Recv frm f) ->
  has_progress data (ps_procs (st_drain_gen j rr_drain Hbg_safe)).
Proof.
move=> Hjlt [frm [f Hbg]].
rewrite /has_progress /= /drain_procs_gen /= /mkseq size_map size_iota.
set dp := alice_foldr _ :: _.
suff Hprog : (step dp [::] j.+1).2 = true.
  apply /orP; right.
  rewrite has_map.
  have Hj := ltn_ord j.
  case: (boolP (nat_of_ord j == 0)) => [/eqP Hj0 | Hjneq0].
    rewrite Hj0 /= in Hprog.
    by rewrite Hprog.
  have Hjgt : (0 < nat_of_ord j)%N by rewrite lt0n.
  apply /orP; right.
  apply /hasP.
  exists j.+1.
    rewrite mem_iota.
    apply /andP; split => /=.
      by rewrite ltn_neqAle eq_sym Hjneq0.
    rewrite addnC addn2.
    exact (ltn_trans Hjlt (ltnSn _)).
  rewrite /= Hprog //.
have Hdp : dp = drain_procs_gen j rr_drain bg.
  by rewrite /dp /drain_procs_gen /mkseq.
have Hnthj : nth (default_proc data) dp j.+1 =
  Send j.+2 (e_local (enc_local (ek (nat_to_party_id j.+2))
    (chain_acc j) rr_drain)) Finish.
  rewrite Hdp /drain_procs_gen /= nth_mkseq //.
  by rewrite eqxx.
have Hnthj2 : nth (default_proc data) dp j.+2 = Recv j.+1 f.
  rewrite Hdp /drain_procs_gen /mkseq -/(mkseq _ _).
  change (nth (default_proc data) (_ :: mkseq ?f ?n) j.+2)
    with (nth (default_proc data) (mkseq f n) j.+1).
  rewrite nth_mkseq //.
  have -> : (j.+1 == j :> nat) = false by rewrite gtn_eqF.
  by rewrite eqxx Hbg.
rewrite /step Hnthj Hnthj2.
by rewrite eqxx.
Qed.

(* tail: the last relay sends to Alice (position 0), forming a matching pair *)
Lemma tail_has_progress (rr : rand AHE) :
  has_progress data (ps_procs (st_tail rr)).
Proof.
rewrite /has_progress /= /tail_procs.
set tp := alice_foldr n_relay.+1 :: _.
suff Hprog : (step tp [::] n_relay.+1).2 = true.
  apply /orP; right.
  rewrite size_cat size_nseq /= addn1 has_map.
  apply /hasP; exists n_relay.+1.
    by rewrite mem_iota /= ltnSn.
  by rewrite /= Hprog.
rewrite /step /tp /=.
rewrite nth_cat size_nseq.
have -> : (n_relay < n_relay)%N = false by rewrite ltnn.
rewrite subnn /=.
rewrite alice_foldr_at_tail /alice_erase_tail
  /pRecvDec_local /std_Recv_dec /Recv_param /=.
by rewrite eqxx.
Qed.

(* ret: Alice (Ret) always fires *)
Lemma ret_has_progress :
  has_progress data (ps_procs st_ret).
Proof.
rewrite /has_progress /= /ret_procs /=.
by [].
Qed.

(* ========================================================================== *)
(* Termination: the FSM eventually reaches st_done                            *)
(* ========================================================================== *)

(* Note: The termination and full-trace connection require concrete bg
   functions that track the protocol's actual relay states through the
   recv/send/drain phases. This involves HE algebraic correctness
   (homomorphic operations produce the expected plaintexts/ciphertexts).

   The parametric step_ok lemmas above provide the building blocks:
   once the concrete bg is supplied and the NOP condition verified,
   the full transition chain follows by composition.

   For now, we state termination for the initial case (recv 0 → done)
   using the concrete definitions, which suffices for the initial state. *)

Inductive phase_reaches : phase_state -> phase_state -> Prop :=
| pr_refl s : phase_reaches s s
| pr_step s1 s2 s3 :
    (one_step_procs (ps_procs s1) = ps_procs s2) ->
    phase_reaches s2 s3 -> phase_reaches s1 s3.

(* ========================================================================== *)
(* Generic interpreter lemmas (copied from dsdp_progress.v / smc_deadlock.v)  *)
(* These work for ANY seq (proc data), not DSDP-specific.                     *)
(* ========================================================================== *)

Lemma nth_one_step (ps : seq (proc data)) (i : nat) :
  (i < size ps)%N ->
  nth (@default_proc data) (one_step_procs ps) i =
  (smc_interpreter.step ps [::] i).1.1.
Proof.
move=> Hi.
rewrite /one_step_procs /unzip1 -!map_comp.
rewrite (nth_map 0); last by rewrite size_iota.
by rewrite nth_iota // add0n.
Qed.

Lemma size_one_step (ps : seq (proc data)) :
  size (one_step_procs ps) = size ps.
Proof. by rewrite /one_step_procs /unzip1 -!map_comp size_map size_iota. Qed.

(* interp_comp: iterated stepping. Defined in smc_deadlock.v or smc_interpreter.v.
   We copy the key unfolding lemma. *)
Lemma interp_comp_unfold_eq (ps : seq (proc data)) (h : nat) :
  @interp_comp data ps h.+1 =
  if @has_progress data ps then @interp_comp data (one_step_procs ps) h
  else ps.
Proof. by rewrite /= /has_progress /one_step_procs. Qed.

Lemma step_all_terminated (ps : seq (proc data)) :
  @all_terminated data ps -> @all_terminated data (one_step_procs ps).
Proof.
rewrite /all_terminated => Ht.
apply/(@all_nthP _ _ _ (default_proc data)).
rewrite size_one_step => i Hi.
rewrite nth_one_step //.
have Hpi : is_terminal (nth (default_proc data) ps i)
  by move/(@all_nthP _ _ _ (default_proc data)): Ht => /(_ i Hi).
rewrite /smc_interpreter.step.
by case: (nth (default_proc data) ps i) Hpi.
Qed.

Lemma interp_comp_add (ps : seq (proc data)) (h1 h2 : nat) :
  @interp_comp data ps (h1 + h2) = @interp_comp data (@interp_comp data ps h1) h2.
Proof.
elim: h1 ps => [|h1 IH] ps //=.
case: ifPn => Hhas.
- by rewrite IH.
- symmetry.
  clear IH; move: Hhas; elim: h2 => [|h2' IH2] //= Hhas.
  by rewrite (negbTE Hhas).
Qed.

(* ========================================================================== *)
(* Algebraic correctness: chain_acc_minus_masks                               *)
(* Copied from dsdp_progress.v. Proves that subtracting all relay masks       *)
(* from the accumulated chain gives the sum of relay dot products.            *)
(* ========================================================================== *)

Lemma chain_acc_eq k :
  (k.+2 <= n_relay.+1)%N ->
  chain_acc k = \sum_(j < k.+2) term (inord j).
Proof.
elim: k => [|k IHk] Hk.
- rewrite /= big_ord_recr big_ord1 /=.
  by have -> : inord 0 = ord0 :> 'I_n_relay.+1
    by apply /val_inj; rewrite /= inordK.
- rewrite /= IHk; last by exact (ltnW Hk).
  by rewrite [RHS]big_ord_recr /=.
Qed.

Lemma chain_acc_sum :
  (1 <= n_relay)%N ->
  chain_acc n_relay.-1 = \sum_(j < n_relay.+1) term j.
Proof.
move=> Hn1.
rewrite chain_acc_eq; last by rewrite prednK.
rewrite prednK //.
apply eq_bigr => j _.
by rewrite inord_val.
Qed.

Lemma chain_acc_minus_masks :
  (1 <= n_relay)%N ->
  chain_acc n_relay.-1 - \sum_(j < n_relay.+1) r j =
  \sum_(j : 'I_n_relay.+1) u (lift ord0 j) * v_relay j.
Proof.
move=> Hn1.
rewrite chain_acc_sum //.
rewrite /term.
rewrite big_split /=.
by rewrite GRing.addrK.
Qed.

(* ========================================================================== *)
(* known_state: the FSM invariant for fuel induction                          *)
(* Replaces dsdp_inv — tracks which concrete state we're at.                 *)
(* ========================================================================== *)

Inductive known_state : phase_state -> Prop :=
| KS_done : known_state st_done
| KS_step st st' :
    known_state st' ->
    one_step_procs (ps_procs st) = ps_procs st' ->
    @has_progress data (ps_procs st) ->
    known_state st.

(* Every known non-done state has progress *)
Lemma known_state_has_progress st :
  known_state st -> ~~ @all_terminated data (ps_procs st) ->
  @has_progress data (ps_procs st).
Proof.
move=> Hks Hnt; case: Hks Hnt.
- rewrite /= /done_procs /all_terminated all_nseq.
  by rewrite /= orbT.
- by move=> st0 st' _ _ Hprog _.
Qed.

(* Every known non-terminated state steps to another known state *)
Lemma known_state_step st :
  known_state st -> ~~ @all_terminated data (ps_procs st) ->
  @all_terminated data (one_step_procs (ps_procs st)) \/
  exists st', known_state st' /\
    one_step_procs (ps_procs st) = ps_procs st'.
Proof.
move=> Hks Hnt; case: Hks Hnt.
- rewrite /= /done_procs /all_terminated all_nseq.
  by rewrite /= orbT.
- move=> st0 st' Hks' Hstep Hprog _.
  right; exists st'; split => //.
Qed.

(* Helper: all processes in procs are double-Init *)
Lemma procs_all_double_init (i : nat) :
  (i < size procs)%N ->
  exists d1 d2 k0, nth (@default_proc data) procs i = Init d1 (Init d2 k0).
Proof.
have Hsz : size procs = n_relay.+2
  by rewrite /procs /dsdp_n_procs /erase_aprocs /dsdp_n_saprocs /= size_map size_map Hrelays.
rewrite Hsz => Hi.
case: i Hi => [|i'] Hi.
- do 3 eexists.
  rewrite /procs /dsdp_n_procs /erase_aprocs /dsdp_n_saprocs /= /erase_aproc /=.
  exact: (@palice_n_erase AHE ek n_relay relays dk v0 u r rand_a).
- have Hi' : (i' < n_relay.+1)%N by [].
  rewrite /procs /dsdp_n_procs /erase_aprocs /dsdp_n_saprocs /=.
  rewrite -map_comp (nth_map ord0); last by rewrite Hrelays.
  rewrite /comp /= /erase_aproc /aproc_proc /relay_aproc.
  set j := nth ord0 relays (Ordinal Hi').
  case: ifP => Hj0.
    rewrite /DParty_first /=; by do 3 eexists.
  case: ifP => Hjn.
    rewrite /DParty_last /=; by do 3 eexists.
  rewrite /DParty_intermediate /=; by do 3 eexists.
Qed.

(* Helper: one_step on a list of Init processes strips one Init layer *)
Lemma one_step_all_init (ps : seq (proc data)) :
  (forall i, (i < size ps)%N ->
     exists d' next, nth (@default_proc data) ps i = Init d' next) ->
  one_step_procs ps =
    [seq match p with Init _ next => next | _ => p end | p <- ps].
Proof.
move=> Hall.
apply (eq_from_nth (x0 := default_proc data)).
  by rewrite size_one_step size_map.
move=> i Hi; rewrite size_one_step in Hi.
rewrite nth_one_step //.
have [d' [next Hnth]] := Hall i Hi.
rewrite /smc_interpreter.step Hnth /=.
rewrite (nth_map (default_proc data)); last by [].
by rewrite Hnth.
Qed.

(* Initial process list has progress (Alice at Init) *)
Lemma initial_has_progress :
  @has_progress data procs.
Proof.
rewrite /has_progress /procs /dsdp_n_procs /dsdp_n_saprocs /erase_aprocs /=.
by [].
Qed.

(* After one step, still has progress *)
Lemma initial_step1_has_progress :
  @has_progress data (one_step_procs procs).
Proof.
rewrite /has_progress /one_step_procs /procs /dsdp_n_procs /dsdp_n_saprocs
  /erase_aprocs /=.
by [].
Qed.

(* After 2 init steps, state matches st_recv ord0 *)
Lemma init_matches_recv0 :
  one_step_procs (one_step_procs procs) = ps_procs (st_recv ord0).
Proof.
rewrite /= /st_recv /st_recv_gen /=.
have Hszp : size procs = n_relay.+2.
  by rewrite /procs /dsdp_n_procs /erase_aprocs /dsdp_n_saprocs /= size_map size_map Hrelays.
have Hprocs0 : exists d1 d2, nth (@default_proc data) procs 0 = Init d1 (Init d2 (alice_foldr 0)).
  do 2 eexists.
  rewrite /procs /dsdp_n_procs /erase_aprocs /dsdp_n_saprocs /= /erase_aproc /aproc_proc.
  rewrite (@palice_n_erase AHE ek n_relay relays dk v0 u r rand_a).
  congr (Init _ (Init _ _)). by rewrite /alice_foldr drop0.
have Hprocsi : forall i (Hi : (i < n_relay.+1)%N),
  exists d1 d2, nth (@default_proc data) procs i.+1 = Init d1 (Init d2 (relay_body (nth ord0 relays (Ordinal Hi)))).
  move=> i Hi0; do 2 eexists.
  rewrite /procs /dsdp_n_procs /erase_aprocs /dsdp_n_saprocs /=.
  rewrite -map_comp (nth_map ord0); last by rewrite Hrelays.
  rewrite /comp /=. exact: relay_erase_eq.
have H1 : forall i, (i < size procs)%N -> exists d' next, nth (@default_proc data) procs i = Init d' next.
  move=> i Hi; rewrite Hszp in Hi.
  case: i Hi => [|i'] Hi.
    have [d1 [d2 H]] := Hprocs0; by exists d1, (Init d2 (alice_foldr 0)).
  have Hi' : (i' < n_relay.+1)%N by [].
  have [d1 [d2 H]] := Hprocsi i' Hi'; by exists d1, (Init d2 (relay_body (nth ord0 relays (Ordinal Hi')))).
rewrite (one_step_all_init H1).
set ps1 := [seq _ | _ <- procs].
have Hsz1 : size ps1 = n_relay.+2 by rewrite /ps1 size_map.
have H2 : forall i, (i < size ps1)%N -> exists d' next, nth (@default_proc data) ps1 i = Init d' next.
  move=> i Hi; rewrite Hsz1 in Hi.
  have Hi' : (i < size procs)%N by rewrite Hszp.
  have [d1 [next Hk]] := H1 i Hi'.
  rewrite /ps1 (nth_map (@default_proc data)) // Hk /=.
  case: i Hi Hi' Hk => [|i'] Hi Hi' Hk.
    have [d1' [d2' Hk0]] := Hprocs0.
    rewrite Hk0 in Hk; case: Hk => _ <-.
    by exists d2', (alice_foldr 0).
  have Hi'n : (i' < n_relay.+1)%N by [].
  have [d1' [d2' Hk']] := Hprocsi i' Hi'n.
  rewrite Hk' in Hk; case: Hk => _ <-.
  by exists d2', (relay_body (nth ord0 relays (Ordinal Hi'n))).
rewrite (one_step_all_init H2).
apply (eq_from_nth (x0 := default_proc data)).
  by rewrite size_map Hsz1 /recv_procs_gen /= size_map size_iota.
rewrite size_map Hsz1 => i Hi.
rewrite (nth_map (@default_proc data)); last by rewrite Hsz1.
have Hi2 : (i < size ps1)%N by rewrite Hsz1.
have [d' [next Hnth]] := H2 i Hi2.
rewrite Hnth /=.
case: i Hi Hi2 Hnth => [|i'] Hi Hi2 Hnth.
- rewrite /recv_procs_gen /=.
  have [d1 [d2 Hk0]] := Hprocs0.
  have Hps1_0 : nth (@default_proc data) ps1 0 = Init d2 (alice_foldr 0).
    rewrite /ps1 (nth_map (@default_proc data)); last by rewrite Hszp.
    by rewrite Hk0.
  rewrite Hps1_0 in Hnth; case: Hnth => _ ->.
  by [].
- have Hi'n : (i' < n_relay.+1)%N by [].
  rewrite /recv_procs_gen /= nth_mkseq //.
  rewrite /bg_init; case: ifP => _ //.
  + have [d1 [d2 Hk']] := Hprocsi i' Hi'n.
    have Hps1_i : nth (@default_proc data) ps1 i'.+1 = Init d2 (relay_body (nth ord0 relays (Ordinal Hi'n))).
      rewrite /ps1 (nth_map (@default_proc data)); last by rewrite Hszp; exact Hi.
      by rewrite Hk'.
    have : d' = d2 /\ next = relay_body (nth ord0 relays (Ordinal Hi'n)).
      by rewrite Hps1_i in Hnth; case: Hnth.
    case=> _ ->; congr relay_body.
    rewrite (Hrelays_id (Ordinal Hi'n)).
    by apply val_inj; rewrite /= inordK.
  + have [d1 [d2 Hk']] := Hprocsi i' Hi'n.
    have Hps1_i : nth (@default_proc data) ps1 i'.+1 = Init d2 (relay_body (nth ord0 relays (Ordinal Hi'n))).
      rewrite /ps1 (nth_map (@default_proc data)); last by rewrite Hszp; exact Hi.
      by rewrite Hk'.
    have : d' = d2 /\ next = relay_body (nth ord0 relays (Ordinal Hi'n)).
      by rewrite Hps1_i in Hnth; case: Hnth.
    case=> _ ->; congr relay_body.
    rewrite (Hrelays_id (Ordinal Hi'n)).
    by apply val_inj; rewrite /= inordK.
Qed.

(* After 2 init steps, not terminated *)
Lemma init_not_terminated :
  ~~ @all_terminated data (one_step_procs (one_step_procs procs)).
Proof.
rewrite init_matches_recv0 /= /all_terminated /recv_procs_gen /=.
have Hord0 := ltn_ord (@ord0 n_relay).
have [f ->] := alice_body_at_recv Hord0.
by [].
Qed.

(* Concrete return value: what chain_acc - masks + u0*v0 equals *)
Let concrete_val_eq :=
  d (\sum_(j : 'I_n_relay.+1) u (lift ord0 j) * v_relay j + u ord0 * v0).

Lemma concrete_val_sum :
  (1 <= n_relay)%N -> concrete_val = concrete_val_eq.
Proof.
move=> Hn1; rewrite /concrete_val /concrete_val_eq.
by rewrite chain_acc_minus_masks // GRing.addrC.
Qed.

(* relay_after_send0 j for j < n_relay is Recv 0 *)
Lemma relay_after_send0_recv0 (j : 'I_n_relay.+1) :
  (j < n_relay)%N ->
  exists f, relay_after_send0 j = Recv 0 f.
Proof.
move=> Hjn.
rewrite /relay_after_send0.
case: ifP => Hj0.
  rewrite /pRecvDec_local /std_Recv_dec /Recv_param /=.
  by eexists.
case: ifP => Hjn'.
  by move/eqP: Hjn' => Hjn'; rewrite Hjn' ltnn in Hjn.
rewrite /pRecvEnc_local /std_Recv_enc /Recv_param /=.
by eexists.
Qed.

(* Unconditional recv → send step: no NOP condition needed *)
Lemma step_ok_recv_send_uncond (j : 'I_n_relay.+1) (bg : nat -> proc data) :
  exists bg_s,
    one_step_procs (recv_procs_gen j bg) =
    send_procs_gen j bg_s.
Proof.
exists (fun i => (step (recv_procs_gen j bg) [::] i.+1).1.1).
set rp := recv_procs_gen j bg.
have Hszrp : size rp = n_relay.+2
  by rewrite /rp /recv_procs_gen /= size_map size_iota.
have Hj := ltn_ord j.
have Hinord : inord (nat_of_ord j) = j :> 'I_n_relay.+1 by exact: inord_val.
have [f Haf] := alice_body_at_recv Hj.
have HjO : Ordinal Hj = j by apply val_inj.
have Hstepj : (step rp [::] j.+1).1.1 = relay_after_send0 j.
  rewrite /rp /recv_procs_gen /step /= nth_mkseq; last by [].
  rewrite eqxx (relay_body_send0_cont (inord j)) Hinord /=.
  rewrite Haf HjO /=.
  by rewrite eqxx.
have Hf : forall c, f (e_local c) =
  Send (alice_send_dest j)
    (e_local (Emul (Epow c (u (lift ord0 j)))
                   (enc (ek (nat_to_party_id j.+1)) (r j) (rand_a j))))
    (alice_foldr j.+1).
  move=> c; move: (Haf).
  rewrite /alice_foldr.
  set zipped := zip relays (iota 0 (size relays)).
  have Hsz' : (j < size zipped)%N
    by rewrite /zipped size_zip size_iota minnn Hrelays.
  rewrite (drop_nth (ord0, 0) Hsz').
  rewrite nth_zip; last by rewrite /zipped size_iota Hrelays.
  rewrite (Hrelays_id (Ordinal Hj)).
  have -> : (iota 0 (size relays))`_j = (j : nat)
    by rewrite /= nth_iota // Hrelays.
  rewrite /= /alice_erase_body /pRecvEnc_local /std_Recv_enc /Recv_param /=.
  move=> [Hfeq]; rewrite -Hfeq /= /e_local /= /std_from_enc /DI /=.
  congr (Send _ _ _). congr (std_e _). by rewrite HjO.
have Hstep0 : (step rp [::] 0).1.1 =
  Send (alice_send_dest j) (e_local (alice_enc j)) (alice_foldr j.+1).
  rewrite /rp /recv_procs_gen /step /= Haf /= nth_mkseq; last by [].
  rewrite eqxx (relay_body_send0_cont (inord j)) Hinord /=.
  by rewrite Hf /alice_enc /nat_to_party_id.
rewrite /one_step_procs -/rp Hszrp /send_procs_gen.
rewrite /unzip1 -2!map_comp.
apply (@eq_from_nth _ (@Finish data)).
  by rewrite size_map size_iota /= size_map size_iota.
move=> i.
rewrite size_map size_iota => Hi.
rewrite (nth_map 0) ?size_iota // nth_iota // add0n.
rewrite /comp /=.
case: i Hi => [|i] Hi.
  by rewrite Hstep0.
rewrite /= nth_mkseq; last by rewrite ltnS in Hi.
case Heq : (i == (j : nat)).
  move/eqP: Heq => Heq; subst i.
  by rewrite Hinord Hstepj.
by [].
Qed.

(* Concrete version: same as step_ok_recv_send_uncond but with
   the witness inlined, so bg_s is transparent (reducible). *)
Lemma step_ok_recv_send_concrete (j : 'I_n_relay.+1) (bg : nat -> proc data) :
  one_step_procs (recv_procs_gen j bg) =
  send_procs_gen j (fun i => (step (recv_procs_gen j bg) [::] i.+1).1.1).
Proof.
set rp := recv_procs_gen j bg.
have Hszrp : size rp = n_relay.+2
  by rewrite /rp /recv_procs_gen /= size_map size_iota.
have Hj := ltn_ord j.
have Hinord : inord (nat_of_ord j) = j :> 'I_n_relay.+1 by exact: inord_val.
have [f Haf] := alice_body_at_recv Hj.
have HjO : Ordinal Hj = j by apply val_inj.
have Hstepj : (step rp [::] j.+1).1.1 = relay_after_send0 j.
  rewrite /rp /recv_procs_gen /step /= nth_mkseq; last by [].
  rewrite eqxx (relay_body_send0_cont (inord j)) Hinord /=.
  rewrite Haf HjO /=.
  by rewrite eqxx.
have Hf : forall c, f (e_local c) =
  Send (alice_send_dest j)
    (e_local (Emul (Epow c (u (lift ord0 j)))
                   (enc (ek (nat_to_party_id j.+1)) (r j) (rand_a j))))
    (alice_foldr j.+1).
  move=> c; move: (Haf).
  rewrite /alice_foldr.
  set zipped := zip relays (iota 0 (size relays)).
  have Hsz' : (j < size zipped)%N
    by rewrite /zipped size_zip size_iota minnn Hrelays.
  rewrite (drop_nth (ord0, 0) Hsz').
  rewrite nth_zip; last by rewrite /zipped size_iota Hrelays.
  rewrite (Hrelays_id (Ordinal Hj)).
  have -> : (iota 0 (size relays))`_j = (j : nat)
    by rewrite /= nth_iota // Hrelays.
  rewrite /= /alice_erase_body /pRecvEnc_local /std_Recv_enc /Recv_param /=.
  move=> [Hfeq]; rewrite -Hfeq /= /e_local /= /std_from_enc /DI /=.
  congr (Send _ _ _). congr (std_e _). by rewrite HjO.
have Hstep0 : (step rp [::] 0).1.1 =
  Send (alice_send_dest j) (e_local (alice_enc j)) (alice_foldr j.+1).
  rewrite /rp /recv_procs_gen /step /= Haf /= nth_mkseq; last by [].
  rewrite eqxx (relay_body_send0_cont (inord j)) Hinord /=.
  by rewrite Hf /alice_enc /nat_to_party_id.
rewrite /one_step_procs -/rp Hszrp /send_procs_gen.
rewrite /unzip1 -2!map_comp.
apply (@eq_from_nth _ (@Finish data)).
  by rewrite size_map size_iota /= size_map size_iota.
move=> i.
rewrite size_map size_iota => Hi.
rewrite (nth_map 0) ?size_iota // nth_iota // add0n.
rewrite /comp /=.
case: i Hi => [|i] Hi.
  by rewrite Hstep0.
rewrite /= nth_mkseq; last by rewrite ltnS in Hi.
case Heq : (i == (j : nat)).
  move/eqP: Heq => Heq; subst i.
  by rewrite Hinord Hstepj.
by [].
Qed.

(* Unconditional send → recv step (no NOP condition) *)
Lemma step_ok_send_recv_uncond (j : 'I_n_relay.+1) (bg : nat -> proc data) :
  (j < n_relay)%N ->
  (exists f, nth (@Finish data) (send_procs_gen j bg) (alice_send_dest j) =
             Recv 0 f) ->
  bg j.+1 = relay_body (inord j.+1) ->
  exists bg',
    one_step_procs (send_procs_gen j bg) =
    recv_procs_gen (inord j.+1) bg'.
Proof.
move=> Hjn [ff Hrecv] Hbg_next.
set sp := send_procs_gen j bg.
have Hszsp : size sp = n_relay.+2
  by rewrite /sp /send_procs_gen /= size_map size_iota.
have Hinord : (inord j.+1 : 'I_n_relay.+1) = j.+1 :> nat
  by rewrite inordK // ltnS.
exists (fun i => (step sp [::] i.+1).1.1).
rewrite /one_step_procs /ps_procs /st_send_gen -/sp Hszsp
        /st_recv_gen /recv_procs_gen /unzip1 -2!map_comp.
apply (@eq_from_nth _ (@Finish data)).
  by rewrite size_map size_iota /= size_map size_iota.
move=> i; rewrite size_map size_iota => Hi.
rewrite (nth_map 0) ?size_iota // nth_iota // add0n /comp /=.
case: i Hi => [|i] Hi.
  rewrite /= /step /sp /send_procs_gen /=.
  have -> : nth (default_proc data)
    (Send (alice_send_dest j) (e_local (alice_enc j)) (alice_foldr j.+1) ::
     mkseq (fun i => if i == j then relay_after_send0 (inord i) else bg i)
       n_relay.+1)
    (alice_send_dest j) = Recv 0 ff.
    rewrite -(Hrecv) /send_procs_gen; apply set_nth_default.
    rewrite /= size_map size_iota /alice_send_dest /maxn.
    case: ifP => _ //.
    by apply ltn_trans with n_relay.+1; [exact: ltn_ord | exact: ltnSn].
  by rewrite /= Hinord.
rewrite /= nth_mkseq; last by rewrite ltnS in Hi.
case Heq : (i == (inord j.+1 : 'I_n_relay.+1) :> nat).
  move/eqP: Heq => Heq; subst i.
  rewrite Hinord /sp /step /send_procs_gen /=.
  have Hjlt : (j < size (iota 1 n_relay))%N by rewrite size_iota.
  rewrite (nth_map 0) // nth_iota // add1n.
  have -> : (j.+1 == j :> nat) = false by rewrite gtn_eqF.
  rewrite Hbg_next (relay_body_send0_cont (inord j.+1)) /=.
  by [].
by [].
Qed.

(* Same as uncond but with explicit bg' in conclusion *)
Lemma step_ok_send_recv_explicit (j : 'I_n_relay.+1) (bg : nat -> proc data) :
  (j < n_relay)%N ->
  (exists f, nth (@Finish data) (send_procs_gen j bg) (alice_send_dest j) =
             Recv 0 f) ->
  bg j.+1 = relay_body (inord j.+1) ->
  one_step_procs (send_procs_gen j bg) =
  recv_procs_gen (inord j.+1)
    (fun i => (step (send_procs_gen j bg) [::] i.+1).1.1).
Proof.
move=> Hjn [ff Hrecv] Hbg_next.
set sp := send_procs_gen j bg.
have Hszsp : size sp = n_relay.+2
  by rewrite /sp /send_procs_gen /= size_map size_iota.
have Hinord : (inord j.+1 : 'I_n_relay.+1) = j.+1 :> nat
  by rewrite inordK // ltnS.
rewrite /one_step_procs /ps_procs /st_send_gen -/sp Hszsp
        /st_recv_gen /recv_procs_gen /unzip1 -2!map_comp.
apply (@eq_from_nth _ (@Finish data)).
  by rewrite size_map size_iota /= size_map size_iota.
move=> i; rewrite size_map size_iota => Hi.
rewrite (nth_map 0) ?size_iota // nth_iota // add0n /comp /=.
case: i Hi => [|i] Hi.
  rewrite /= /step /sp /send_procs_gen /=.
  have -> : nth (default_proc data)
    (Send (alice_send_dest j) (e_local (alice_enc j)) (alice_foldr j.+1) ::
     mkseq (fun i => if i == j then relay_after_send0 (inord i) else bg i)
       n_relay.+1)
    (alice_send_dest j) = Recv 0 ff.
    rewrite -(Hrecv) /send_procs_gen; apply set_nth_default.
    rewrite /= size_map size_iota /alice_send_dest /maxn.
    case: ifP => _ //.
    by apply ltn_trans with n_relay.+1; [exact: ltn_ord | exact: ltnSn].
  by rewrite /= Hinord.
rewrite /= nth_mkseq; last by rewrite ltnS in Hi.
case Heq : (i == (inord j.+1 : 'I_n_relay.+1) :> nat).
  move/eqP: Heq => Heq; subst i.
  rewrite Hinord /sp /step /send_procs_gen /=.
  have Hjlt : (j < size (iota 1 n_relay))%N by rewrite size_iota.
  rewrite (nth_map 0) // nth_iota // add1n.
  have -> : (j.+1 == j :> nat) = false by rewrite gtn_eqF.
  rewrite Hbg_next (relay_body_send0_cont (inord j.+1)) /=.
  by [].
by [].
Qed.

(* Relay ahead of active position j is NOP in recv: preserved *)
Lemma bg_relay_ahead_recv (j : 'I_n_relay.+1) (bg : nat -> proc data)
    (i : nat) :
  (j < i)%N -> (i < n_relay.+1)%N ->
  bg i = relay_body (inord i) ->
  (step (recv_procs_gen j bg) [::] i.+1).1.1 = relay_body (inord i).
Proof.
move=> Hji Hi Hbgi.
rewrite /recv_procs_gen /step /=.
rewrite nth_mkseq; last exact Hi.
have -> : (i == j :> nat) = false.
  by apply /eqP => Heq; rewrite Heq ltnn in Hji.
rewrite Hbgi.
have [sk Hsk] := relay_body_is_send0 (inord i).
rewrite Hsk /=.
have Hj := ltn_ord j.
have [f Haf] := alice_body_at_recv Hj.
rewrite Haf /=.
have -> : ((Ordinal Hj).+1 == i.+1) = false.
  apply /eqP => H. apply succn_inj in H.
  move: H => /= H; rewrite H ltnn in Hji. by [].
by [].
Qed.

(* Relay ahead of active position j is NOP in send: preserved *)
Lemma bg_relay_ahead_send (j : 'I_n_relay.+1) (bg : nat -> proc data)
    (i : nat) :
  (j < i)%N -> (i < n_relay.+1)%N ->
  bg i = relay_body (inord i) ->
  (step (send_procs_gen j bg) [::] i.+1).1.1 = bg i.
Proof.
move=> Hji Hi Hbgi.
rewrite /send_procs_gen /step /=.
rewrite nth_mkseq; last exact Hi.
have -> : (i == j :> nat) = false.
  by apply /eqP => Heq; rewrite Heq ltnn in Hji.
rewrite Hbgi.
have [sk Hsk] := relay_body_is_send0 (inord i).
rewrite Hsk /=.
by [].
Qed.

(* Destination in send_procs_gen has Recv 0 *)
Lemma send_dest_recv0 (j : 'I_n_relay.+1) (bg : nat -> proc data) :
  (j < n_relay)%N ->
  ((0 < j)%N -> exists f, bg j.-1 = Recv 0 f) ->
  exists f, nth (@Finish data) (send_procs_gen j bg) (alice_send_dest j) = Recv 0 f.
Proof.
move=> Hjn Hbehind.
rewrite /send_procs_gen /alice_send_dest.
case Hj0 : (j == 0 :> nat)%N.
  move/eqP: Hj0 => Hj0.
  have -> : maxn 1 (j : nat) = 1 by rewrite Hj0.
  rewrite /= nth_mkseq //=.
  have -> : (0 == j :> nat) = true by rewrite Hj0.
  have Hinord0 : inord 0 = j :> 'I_n_relay.+1.
    apply val_inj; rewrite /= inordK //.
  rewrite Hinord0.
  exact: (relay_after_send0_recv0 Hjn).
have Hj0' : (0 < j)%N by rewrite lt0n Hj0.
have [f Hf] := Hbehind Hj0'.
rewrite /maxn.
case: ltnP => Hlt.
  rewrite nth_cons_pos; last by apply ltn_trans with 1.
  rewrite nth_mkseq; last first.
    rewrite -ltnS prednK //.
    exact: (ltn_trans (ltn_ord j) (ltnSn _)).
  have -> : (j.-1 == j :> nat) = false.
    apply /eqP => Heq. have := prednK Hj0'.
    rewrite Heq. exact: neq_succn.
  by exists f.
have Hj1 : j = 1 :> nat by apply anti_leq; rewrite Hj0' Hlt.
rewrite /= nth_mkseq //.
have -> : (0 == j :> nat) = false by rewrite Hj1.
rewrite Hj1 /= in Hf.
by exists f.
Qed.

End dsdp_fsm.

(* ========================================================================== *)
(* Section dsdp_fsm_chain: known_state2 — post-section chain invariant        *)
(* Uses fully section-closed lemmas from dsdp_fsm.                            *)
(* ========================================================================== *)

Section dsdp_fsm_chain.

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

(* Local abbreviations for section-closed state constructors *)
Let local_st_ret := @st_ret AHE n_relay v0 u r v_relay.
Let local_st_tail := fun rr =>
  @st_tail AHE ek n_relay dk relays Hrelays v0 u r rand_a v_relay rr.
Let local_st_drain_gen := fun j rr bg Hbg =>
  @st_drain_gen AHE ek n_relay dk relays Hrelays v0 u r rand_a v_relay
    j rr bg Hbg.
Let local_st_recv := fun j =>
  @st_recv AHE ek n_relay dk dk_relay relays Hrelays Hrelays_id
    v0 u r rand_a v_relay r1_relay r2_relay j.

(* known_state2: chain invariant with st_ret as terminal state.
   Unlike known_state (which uses st_done), this tracks all_terminated
   explicitly and terminates at st_ret (the actual final protocol state). *)
Inductive known_state2 : phase_state AHE -> Prop :=
| KS2_ret : known_state2 local_st_ret
| KS2_step st st' :
    known_state2 st' ->
    one_step_procs (ps_procs st) = ps_procs st' ->
    @has_progress data (ps_procs st) ->
    ~~ @all_terminated data (ps_procs st) ->
    known_state2 st.

(* Helper: tail state is not terminated (last relay still active) *)
Lemma tail_not_terminated (rr : rand AHE) :
  ~~ @all_terminated data (ps_procs (local_st_tail rr)).
Proof.
rewrite /local_st_tail /= /all_terminated /tail_procs.
rewrite all_cat /= andbF.
by rewrite andbF.
Qed.

(* ks2_tail: the tail state is in known_state2 *)
Lemma ks2_tail (rr : rand AHE) : known_state2 (local_st_tail rr).
Proof.
apply (KS2_step KS2_ret).
- exact: (@step_ok_tail_ret AHE ek n_relay Hn_relay dk relays Hrelays
            v0 u r rand_a v_relay key_alice rr).
- exact: (@tail_has_progress AHE ek n_relay dk relays Hrelays
            v0 u r rand_a v_relay rr).
- exact: (tail_not_terminated rr).
Qed.

(* Local notations for section-closed state constructors *)
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

(* drain_steppable: inductive evidence that a drain chain reaches tail.
   Each constructor carries one drain step plus evidence for the rest. *)
Inductive drain_steppable :
  forall (j : 'I_n_relay.+1) (rr : rand AHE)
         (bg : nat -> proc (std_data AHE)), Prop :=
| DS_last (j : 'I_n_relay.+1) (rr : rand AHE)
    (bg : nat -> proc (std_data AHE))
    (Hsafe : forall (v : std_data AHE) (k : proc (std_data AHE)),
       bg n_relay <> Send 0 v k)
    (rr' : rand AHE) :
    one_step_procs (ps_procs (drain_st j rr (bg:=bg) Hsafe)) =
    ps_procs (tail_st rr') ->
    @has_progress (std_data AHE)
      (ps_procs (drain_st j rr (bg:=bg) Hsafe)) ->
    ~~ @all_terminated (std_data AHE)
      (ps_procs (drain_st j rr (bg:=bg) Hsafe)) ->
    drain_steppable j rr bg
| DS_step (j : 'I_n_relay.+1) (rr : rand AHE)
    (bg : nat -> proc (std_data AHE))
    (Hsafe : forall (v : std_data AHE) (k : proc (std_data AHE)),
       bg n_relay <> Send 0 v k)
    (rr' : rand AHE) (bg' : nat -> proc (std_data AHE))
    (Hsafe' : forall (v : std_data AHE) (k : proc (std_data AHE)),
       bg' n_relay <> Send 0 v k) :
    one_step_procs (ps_procs (drain_st j rr (bg:=bg) Hsafe)) =
    ps_procs (drain_st (inord j.+1) rr' (bg:=bg') Hsafe') ->
    @has_progress (std_data AHE)
      (ps_procs (drain_st j rr (bg:=bg) Hsafe)) ->
    ~~ @all_terminated (std_data AHE)
      (ps_procs (drain_st j rr (bg:=bg) Hsafe)) ->
    drain_steppable (inord j.+1) rr' bg' ->
    drain_steppable j rr bg.

(* ks2_drain_chain: if drain chain evidence exists, drain is in known_state2 *)
Lemma ks2_drain_chain (j : 'I_n_relay.+1) (rr : rand AHE)
    (bg : nat -> proc (std_data AHE))
    (Hbg_safe : forall v k, bg n_relay <> Send 0 v k) :
  drain_steppable j rr bg ->
  known_state2 (drain_st j rr (bg:=bg) Hbg_safe).
Proof.
move=> Hds; induction Hds as
  [j0 rr0 bg0 Hs0 rr0' Hstep0 Hprog0 Hnt0
  |j0 rr0 bg0 Hs0 rr0' bg0' Hs0' Hstep0 Hprog0 Hnt0 _ IH].
- have Hirr : ps_procs (drain_st j0 rr0 (bg:=bg0) Hs0) =
              ps_procs (drain_st j0 rr0 (bg:=bg0) Hbg_safe) by [].
  apply (KS2_step (ks2_tail rr0')); rewrite -Hirr //.
- have Hirr : ps_procs (drain_st j0 rr0 (bg:=bg0) Hs0) =
              ps_procs (drain_st j0 rr0 (bg:=bg0) Hbg_safe) by [].
  apply (KS2_step (IH Hs0')); rewrite -Hirr //.
Qed.

(* recv_send_steppable: inductive evidence that recv/send loop reaches drain.
   Each constructor carries one recv→send step plus evidence for the rest. *)
Inductive recv_send_steppable :
  forall (j : 'I_n_relay.+1) (bg : nat -> proc (std_data AHE)), Prop :=
| RSS_to_drain (j : 'I_n_relay.+1) (bg bg_s : nat -> proc (std_data AHE))
    (rr_d : rand AHE) (bg_d : nat -> proc (std_data AHE))
    (Hsafe_d : forall (v : std_data AHE) (k : proc (std_data AHE)),
       bg_d n_relay <> Send 0 v k) :
    @has_progress (std_data AHE) (ps_procs (recv_st j bg)) ->
    ~~ @all_terminated (std_data AHE) (ps_procs (recv_st j bg)) ->
    one_step_procs (ps_procs (recv_st j bg)) =
      ps_procs (send_st j bg_s) ->
    @has_progress (std_data AHE) (ps_procs (send_st j bg_s)) ->
    ~~ @all_terminated (std_data AHE) (ps_procs (send_st j bg_s)) ->
    one_step_procs (ps_procs (send_st j bg_s)) =
      ps_procs (drain_st ord0 rr_d (bg:=bg_d) Hsafe_d) ->
    drain_steppable ord0 rr_d bg_d ->
    recv_send_steppable j bg
| RSS_continue (j : 'I_n_relay.+1) (bg bg_s : nat -> proc (std_data AHE))
    (j' : 'I_n_relay.+1) (bg' : nat -> proc (std_data AHE)) :
    @has_progress (std_data AHE) (ps_procs (recv_st j bg)) ->
    ~~ @all_terminated (std_data AHE) (ps_procs (recv_st j bg)) ->
    one_step_procs (ps_procs (recv_st j bg)) =
      ps_procs (send_st j bg_s) ->
    @has_progress (std_data AHE) (ps_procs (send_st j bg_s)) ->
    ~~ @all_terminated (std_data AHE) (ps_procs (send_st j bg_s)) ->
    one_step_procs (ps_procs (send_st j bg_s)) =
      ps_procs (recv_st j' bg') ->
    recv_send_steppable j' bg' ->
    recv_send_steppable j bg
| RSS_known (j : 'I_n_relay.+1) (bg : nat -> proc (std_data AHE)) :
    known_state2 (recv_st j bg) ->
    recv_send_steppable j bg.

(* ks2_recv_gen: if recv/send chain evidence exists, recv is in known_state2 *)
Lemma ks2_recv_gen (j : 'I_n_relay.+1) (bg : nat -> proc (std_data AHE)) :
  recv_send_steppable j bg ->
  known_state2 (recv_st j bg).
Proof.
move=> Hrss; induction Hrss as
  [j0 bg0 bg_s0 rr_d0 bg_d0 Hs_d0
     Hprog_r0 Hnt_r0 Hstep_rs0
     Hprog_s0 Hnt_s0 Hstep_sd0 Hds0
  |j0 bg0 bg_s0 j0' bg0'
     Hprog_r0 Hnt_r0 Hstep_rs0
     Hprog_s0 Hnt_s0 Hstep_sr0 _ IH
  |j0 bg0 Hks2].
- refine (KS2_step _ Hstep_rs0 Hprog_r0 Hnt_r0).
  refine (KS2_step _ Hstep_sd0 Hprog_s0 Hnt_s0).
  exact (@ks2_drain_chain _ _ _ Hs_d0 Hds0).
- refine (KS2_step _ Hstep_rs0 Hprog_r0 Hnt_r0).
  exact (KS2_step IH Hstep_sr0 Hprog_s0 Hnt_s0).
- exact Hks2.
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
  @bg_nop_recv AHE ek n_relay dk dk_relay relays v0 u r rand_a v_relay r1_relay r2_relay j bg.
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
  @bg_nop_recv AHE ek n_relay dk dk_relay relays v0 u r rand_a v_relay r1_relay r2_relay j
    (@bg_init AHE ek n_relay dk_relay v_relay r1_relay r2_relay).
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

(* interp_chain_ks2: if interp_comp reaches st_ret in fuel+1 steps
   with progress and non-termination at every intermediate step,
   then the starting state is known_state2. *)
Lemma interp_chain_ks2 (fuel : nat) (st : phase_state AHE) :
  @interp_comp (std_data AHE) (ps_procs st) fuel.+1 = ps_procs local_st_ret ->
  (forall k, (k < fuel.+1)%N ->
    @has_progress (std_data AHE) (@interp_comp (std_data AHE) (ps_procs st) k)) ->
  (forall k, (k < fuel.+1)%N ->
    ~~ @all_terminated (std_data AHE) (@interp_comp (std_data AHE) (ps_procs st) k)) ->
  known_state2 st.
Proof.
elim: fuel st => [|fuel IH] st Hreach Hprog Hnt.
- (* fuel = 0 *)
  rewrite interp_comp_unfold_eq in Hreach.
  case Hhas : (has_progress (std_data AHE) (ps_procs st)); last first.
    by exfalso; move: (Hprog 0 (ltn0Sn _)); rewrite Hhas.
  rewrite Hhas in Hreach.
  exact (KS2_step KS2_ret Hreach Hhas (Hnt 0 (ltn0Sn _))).
- (* fuel = n+1 *)
  rewrite interp_comp_unfold_eq in Hreach.
  case Hhas : (has_progress (std_data AHE) (ps_procs st)); last first.
    by exfalso; move: (Hprog 0 (ltn0Sn _)); rewrite Hhas.
  rewrite Hhas in Hreach.
  set st' := @PhaseState AHE (one_step_procs (ps_procs st))
    ((smc_interpreter.step (one_step_procs (ps_procs st)) [::] 0).1.2) erefl.
  have Hst' : ps_procs st' = one_step_procs (ps_procs st) by [].
  refine (KS2_step _ (esym Hst') Hhas (Hnt 0 (ltn0Sn _))).
  apply IH.
  + by rewrite Hst'.
  + move=> k Hk. move: (Hprog k.+1 Hk). by rewrite interp_comp_unfold_eq Hhas.
  + move=> k Hk. move: (Hnt k.+1 Hk). by rewrite interp_comp_unfold_eq Hhas.
Qed.

(* Local aliases for section-closed lemmas *)
Let local_recv_procs_gen := @recv_procs_gen AHE ek n_relay dk dk_relay relays
    v0 u r rand_a v_relay r1_relay r2_relay.
Let local_send_procs_gen := @send_procs_gen AHE ek n_relay dk dk_relay relays
    v0 u r rand_a v_relay r1_relay r2_relay.
Let local_relay_body := @relay_body AHE ek n_relay dk_relay v_relay r1_relay r2_relay.
Let local_bg_init := @bg_init AHE ek n_relay dk_relay v_relay r1_relay r2_relay.

(* bg_safe_form i p: process p at relay position i has a "safe" form
   that doesn't interfere with active communication and will eventually
   terminate through the drain chain.
   The inductive structure ensures Recv callbacks produce safe forms. *)
Inductive bg_safe_form : nat -> proc (std_data AHE) -> Prop :=
| BSF_finish i : bg_safe_form i Finish
| BSF_fail i : bg_safe_form i Fail
| BSF_send i v : bg_safe_form i (Send i.+2 v Finish)
| BSF_recv0 i f :
    (forall v, bg_safe_form i (f v)) ->
    bg_safe_form i (Recv 0 f)
| BSF_recv_i i f :
    (forall v, bg_safe_form i (f v)) ->
    bg_safe_form i (Recv i f).

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
  case: v0' => [[[m|c]|p]|d].
  + by apply BSF_fail.
  + case Hdec: (dec (dk_relay j) c) => [m0|].
    * rewrite /= /std_Recv_enc /Recv_param /=.
      rewrite Hdec /=.
      apply BSF_recv0 => v1'.
      rewrite /= /std_from_enc.
      case: v1' => [[[m'|c']|p']|d'] /=;
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
    case: v0' => [[[m|c]|p]|d].
    * by apply BSF_fail.
    * apply BSF_recv_i => v1'.
      rewrite /std_Recv_dec /Recv_param /= /std_from_enc /=.
      case: v1' => [[[m'|c']|p']|d'].
      -- by apply BSF_fail.
      -- case Hdec: (dec (dk_relay j) c') => [m0|].
         ** rewrite /= Hdec /=. by apply BSF_send.
         ** exfalso. move/eqP: (dec_total (dk_relay j) c'). by rewrite Hdec.
      -- by apply BSF_fail.
      -- by apply BSF_fail.
    * by apply BSF_fail.
    * by apply BSF_fail.
Qed.

Lemma ks2_recv0_gen (k : nat) (j : 'I_n_relay.+1)
    (bg : nat -> proc (std_data AHE)) :
  (j + k = n_relay)%N ->
  (forall i, (j < i)%N -> (i < n_relay.+1)%N ->
     bg i = local_relay_body (inord i)) ->
  ((0 < j)%N -> exists f, bg j.-1 = Recv 0 f) ->
  (forall i, (i < j)%N -> bg_safe_form i (bg i)) ->
  known_state2 (recv_st j bg).
Proof.
elim: k j bg => [|k IH] j bg Hjk Hahead Hbehind Hsafe.
- (* Base case: k=0, j = n_relay = ord_max *)
  have Hjmax : j = n_relay :> nat by have := Hjk; rewrite addn0.
  admit.
- (* Inductive case: j + k.+1 = n_relay, so j < n_relay *)
  have Hjn : (j < n_relay)%N.
    by rewrite -(ltn_add2r k.+1) Hjk addnS ltnS leq_addr.
  (* Step 1: recv → send — bg_s defined transparently *)
  set bg_s := fun i => (smc_interpreter.step (local_recv_procs_gen j bg) [::] i.+1).1.1.
  have Hstep_rs : one_step_procs (local_recv_procs_gen j bg) =
    local_send_procs_gen j bg_s.
    exact: step_ok_recv_send_concrete.
  (* Step 2: send destination has Recv 0 *)
  have Hdest : exists f, nth (@Finish (std_data AHE))
      (local_send_procs_gen j bg_s) (alice_send_dest j) = Recv 0 f.
    apply send_dest_recv0 => //.
    (* Hbehind for bg_s: bg_s(j-1) = Recv 0 f *)
      move=> Hj0.
      have [f Hf] := Hbehind Hj0.
      exists f. rewrite /bg_s /local_recv_procs_gen.
      rewrite /recv_procs_gen /smc_interpreter.step /=.
      rewrite nth_mkseq; last by apply (leq_ltn_trans (leq_pred j) (ltn_ord j)).
      have -> : (j.-1 == j :> nat) = false.
        apply negbTE. rewrite neq_ltn. apply /orP. left.
        by rewrite prednK // ltnSn.
      rewrite Hf /=.
      have Hj_lt := ltn_ord j.
      have [f_alice Haf] := @alice_body_at_recv AHE ek n_relay dk relays Hrelays
        Hrelays_id v0 u r rand_a (j : nat) Hj_lt.
      by rewrite Haf.
  (* Step 3: send has progress *)
  have Hprog_s : @has_progress (std_data AHE) (ps_procs (send_st j bg_s)).
    apply send_has_progress_gen => //.
  (* Step 4: bg_s(j+1) = relay_body *)
  have Hbg_next : bg_s j.+1 = local_relay_body (inord j.+1)
    by rewrite /bg_s; apply bg_relay_ahead_recv => //; exact: Hahead (ltnSn j) Hjn.
  (* Step 5: send → recv(j+1) using explicit bg' *)
  set bg' := fun i => (step (local_send_procs_gen j bg_s) [::] i.+1).1.1.
  have Hstep_sr :
    one_step_procs (ps_procs (send_st j bg_s)) =
    ps_procs (recv_st (inord j.+1) bg').
    apply step_ok_send_recv_explicit => //.
  have Hinord : (inord j.+1 : 'I_n_relay.+1) = j.+1 :> nat
    by rewrite inordK.
  (* Step 6: known_state2 via recv → send → recv' chain *)
  have Hprog_r := @recv_has_progress_gen AHE ek n_relay dk dk_relay relays
    Hrelays Hrelays_id v0 u r rand_a v_relay r1_relay r2_relay j bg.
  have Hnt_r := recv_not_terminated_gen j bg.
  have Hstep_rs' : one_step_procs (ps_procs (recv_st j bg)) =
    ps_procs (send_st j bg_s) by exact Hstep_rs.
  refine (KS2_step _ Hstep_rs' Hprog_r Hnt_r).
  refine (KS2_step _ Hstep_sr Hprog_s (send_not_terminated_gen j bg_s)).
  apply IH.
  + by rewrite Hinord addSnnS.
  + (* Hahead for bg': relay ahead preserved *)
    move=> i Hi1 Hi2.
    rewrite Hinord in Hi1.
    rewrite /bg'.
    have Hij : (j < i)%N by apply ltn_trans with j.+1 => //.
    have Hbg_si : bg_s i = local_relay_body (inord i)
      by rewrite /bg_s; apply bg_relay_ahead_recv => //; exact: (Hahead i Hij Hi2).
    by rewrite -Hbg_si; apply bg_relay_ahead_send => //.
  + (* Hbehind for bg': bg'(j) = Recv 0 f *)
    rewrite Hinord => _.
    rewrite /bg' /local_send_procs_gen /send_procs_gen.
    rewrite /smc_interpreter.step /= nth_mkseq; last by [].
    rewrite eqxx.
    have Hinord_j : inord (nat_of_ord j) = j :> 'I_n_relay.+1 by exact: inord_val.
    have Hjn' : ((inord j : 'I_n_relay.+1) < n_relay)%N by rewrite Hinord_j.
    have [f_ras Hras] := @relay_after_send0_recv0 AHE ek n_relay dk_relay
      v_relay r1_relay r2_relay (inord j) Hjn'.
    rewrite Hras /=.
    case: ifP => Hdst.
    * (* j = 0: step fires, callback gives Recv 0 *)
      rewrite /relay_after_send0 Hinord_j in Hras.
      have Hj0 : (j : nat) == 0.
        rewrite /alice_send_dest in Hdst.
        case: (j : nat) Hdst => [|n] //=.
        rewrite /maxn. case: ltnP => // _. move/eqP => Habs.
        exfalso. move: Habs. exact: n_Sn.
      rewrite Hj0 /= /std_Recv_dec /Recv_param /= in Hras.
      case: Hras => Hras_eq. rewrite /= -Hras_eq /= /std_from_enc /=.
      set c_val := alice_enc _ _ _ _ _ _ _.
      have Hdec2 := dec_total (dk_relay j) c_val.
      case Hdc2: (dec (dk_relay j) c_val) => [m2|]; last by rewrite Hdc2 in Hdec2.
      rewrite /= /std_Recv_enc /Recv_param /=.
      by eexists.
    * (* j >= 1: NOP *)
      by eexists.
  + (* Hsafe for bg': bg_safe_form i (bg' i) for i < j.+1 *)
    move=> i.
    rewrite Hinord => Hi.
    rewrite ltnS leq_eqVlt in Hi.
    case/orP: Hi => [/eqP Hi_eq | Hi_lt].
    * (* i = j: bg'(j) = Recv 0 f — proved in Hbehind bullet *)
      subst i.
      rewrite /bg' /local_send_procs_gen /send_procs_gen.
      rewrite /smc_interpreter.step /= nth_mkseq; last by [].
      rewrite eqxx.
      have Hinord_j : inord (nat_of_ord j) = j :> 'I_n_relay.+1 by exact: inord_val.
      have Hjn' : ((inord j : 'I_n_relay.+1) < n_relay)%N by rewrite Hinord_j.
      have [f_ras Hras] := @relay_after_send0_recv0 AHE ek n_relay dk_relay
        v_relay r1_relay r2_relay (inord j) Hjn'.
      rewrite Hras /=.
      case: ifP => Hdst.
      -- (* j = 0: after recv, becomes Recv 0 *)
         rewrite /relay_after_send0 Hinord_j in Hras.
         have Hj0 : (j : nat) == 0.
           rewrite /alice_send_dest in Hdst.
           case: (j : nat) Hdst => [|n] //=.
           rewrite /maxn. case: ltnP => // _. move/eqP => Habs.
           exfalso. move: Habs. exact: n_Sn.
         rewrite Hj0 /= /std_Recv_dec /Recv_param /= in Hras.
         case: Hras => Hras_eq. rewrite /= -Hras_eq /= /std_from_enc /=.
         set c_val := alice_enc _ _ _ _ _ _ _.
         have Hdec2 := dec_total (dk_relay j) c_val.
         case Hdc2: (dec (dk_relay j) c_val) => [m2|]; last by rewrite Hdc2 in Hdec2.
         rewrite /= /std_Recv_enc /Recv_param /=.
         apply BSF_recv0 => v0'.
         rewrite /std_from_enc /=.
         case: v0' => [[[m'|c']|p']|d'] /=;
           [by apply BSF_fail | by apply BSF_send |
            by apply BSF_fail | by apply BSF_fail].
      -- (* j >= 1: NOP, stays as Recv 0 *)
         rewrite /=. rewrite -Hras Hinord_j.
         exact: relay_after_send0_safe.
    * (* i < j: bg'(i) evolves from bg(i) through recv then send steps *)
      admit. (* bg_safe_form propagation for i < j *)
Admitted.

(* ks2_recv0: the initial recv state is in known_state2. *)
Lemma ks2_recv0 : known_state2 (local_st_recv ord0).
Proof.
apply (ks2_recv0_gen (k := n_relay) (j := ord0) (bg := local_bg_init)).
- by rewrite add0n.
- move=> i Hi0 Hi. by rewrite /local_bg_init /bg_init.
- by move=> /=.
- by move=> i /=.
Qed.

(* known_state2_term_ret: if a known_state2 is all-terminated,
   its process list is that of st_ret *)
Lemma known_state2_term_ret st :
  known_state2 st -> @all_terminated data (ps_procs st) ->
  ps_procs st = ps_procs local_st_ret.
Proof.
move=> Hks2 Hat.
case: Hks2 Hat.
- by [].
- move=> st0 st' _ _ _ Hnt Hat.
  by rewrite Hat in Hnt.
Qed.

End dsdp_fsm_chain.
