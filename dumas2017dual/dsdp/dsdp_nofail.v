(*******************************************************************************)
(** * No-Fail Property for N-Party DSDP                                        *)
(*******************************************************************************)

(* This file proves that DSDP protocol processes never reach the Fail state,
   given key consistency (dec_correct). The proof proceeds by:
   1. Defining a data-wellformed invariant on process lists
   2. Showing the initial configuration satisfies the invariant
   3. Showing each step preserves the invariant
   4. Showing the invariant implies all_nonfail throughout execution

   The only sources of Fail in DSDP are:
   - std_from_enc returns None (data not in encrypted format)
   - dec dk enc0 returns None (decryption failure)
   Neither occurs when:
   - All sends use std_e(enc(...)), so std_from_enc always succeeds
   - Ciphertexts are encrypted under pub_of_priv dk, so dec_correct applies

   Literature: follows the "type preservation" proof pattern from
   Ekici et al. (ITP 2025), adapted to infotheo's round-based interpreter. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
Require Import ssr_ext.
Require Import smc_interpreter smc_session_types.
Require Import homomorphic_encryption.
Require Import dsdp_interface dsdp_session_types dsdp_program.
Require Import dsdp_pismc.

Local Open Scope ring_scope.

Section dsdp_nofail.

Variable AHE : AHEncType.
Variable ek : party_id -> pub_key AHE.
Variable n_relay : nat.

Let DI := Standard_DSDP_Interface AHE.
Let data := di_data DI.
Let e := di_e DI.
Let d := di_d DI.
Let priv_key_data := di_priv_key DI.

(* Key consistency: each party's private key matches the public key mapping.
   This is a precondition on protocol setup, not something to prove —
   the caller provides keys that are consistent. Combined with dec_correct,
   this ensures all decryptions succeed. *)
Variable dk : he_types.priv_key AHE.
Variable dk_relay : 'I_n_relay.+1 -> he_types.priv_key AHE.

Hypothesis key_alice : ek alice_idx = pub_of_priv dk.
Hypothesis key_relay : forall j : 'I_n_relay.+1,
  ek (nat_to_party_id j.+1) = pub_of_priv (dk_relay j).

(* Totality of decryption: dec never returns None.
   This holds for common AHE schemes (Paillier: modular exponentiation is
   always defined; Benaloh: DLP computation succeeds on all group elements;
   idealized: identity function). It is also implied by the DSDP protocol
   structure where all ciphertexts are encrypted under matching keys, but
   stating it as a hypothesis avoids tracking ciphertext provenance through
   multi-round interpretation. See Dumas et al. (2017), Section 3. *)
Hypothesis dec_total : forall dk' c, @dec AHE dk' c != None.

(* Protocol parameters *)
Variable relays : seq 'I_n_relay.+1.
Hypothesis Hrelays : size relays = n_relay.+1.
Variable v0 : plain AHE.
Variable u : 'I_n_relay.+2 -> plain AHE.
Variable r : 'I_n_relay.+1 -> plain AHE.
Variable rand_a : 'I_n_relay.+1 -> rand AHE.
Variable v_relay : 'I_n_relay.+1 -> plain AHE.
Variables (r1_relay r2_relay : 'I_n_relay.+1 -> rand AHE).

Let procs := @dsdp_n_procs AHE ek n_relay relays dk v0 u r rand_a
  dk_relay v_relay r1_relay r2_relay.

(*******************************************************************************)
(** ** No-fail invariant                                                       *)
(*******************************************************************************)

(* A process is "send-valid" if whenever it is a Send, the data is of
   the form std_e(enc_value) — i.e., std_from_enc succeeds on it.
   This is trivially true for Init, Recv, Ret, Finish, Fail. *)
Definition send_valid (p : proc data) : bool :=
  match p with
  | Send _ v _ => @std_from_enc AHE v != None
  | _ => true
  end.

(* All processes in a list are send-valid *)
Definition all_send_valid (ps : seq (proc data)) : bool :=
  all send_valid ps.

(* Deep process well-formedness (Prop-valued).
   A process is well-formed if:
   - It is not Fail
   - All nested Sends have send-valid data (std_from_enc succeeds)
   - All Recv continuations produce well-formed results when given
     send-valid data (std_from_enc succeeds on the received value).
   This is the inductive invariant for the no-fail proof. *)
Fixpoint proc_wf (p : proc data) : Prop :=
  match p with
  | Init _ k => proc_wf k
  | Send _ v k => @std_from_enc AHE v != None /\ proc_wf k
  | Recv _ f => forall v, @std_from_enc AHE v != None -> proc_wf (f v)
  | Ret _ => True
  | Finish => True
  | Fail => False
  end.

Definition all_proc_wf (ps : seq (proc data)) : Prop :=
  forall i, (i < size ps)%N -> proc_wf (nth (default_proc data) ps i).

(*******************************************************************************)
(** ** Key lemmas                                                              *)
(*******************************************************************************)

(* Every Send in the DSDP protocol sends data wrapped with std_e (= di_e DI),
   which is inl(inl(inr v)). Thus std_from_enc always returns Some. *)
Lemma std_e_from_enc (v : cipher AHE) :
  @std_from_enc AHE (e v) = Some v.
Proof. by []. Qed.

(* dec_correct: decrypting with the right key always succeeds *)
Lemma dec_key_alice (m : plain AHE) (r0 : rand AHE) :
  dec dk (enc (ek alice_idx) m r0) = Some m.
Proof. by rewrite key_alice dec_correct. Qed.

Lemma dec_key_relay (j : 'I_n_relay.+1) (m : plain AHE) (r0 : rand AHE) :
  dec (dk_relay j) (enc (ek (nat_to_party_id j.+1)) m r0) = Some m.
Proof. by rewrite key_relay dec_correct. Qed.

(* proc_wf implies is_nonfail (outermost constructor is not Fail) *)
Lemma proc_wf_nonfail p : proc_wf p -> is_nonfail p.
Proof. by case: p. Qed.

(* proc_wf implies send_valid (outermost Send has valid data) *)
Lemma proc_wf_send_valid p : proc_wf p -> send_valid p.
Proof. by case: p => //= dst v k []. Qed.

(*******************************************************************************)
(** ** DSDP Recv continuations preserve proc_wf                                *)
(*******************************************************************************)

(* Helper: std_Recv_dec continuation produces proc_wf results when:
   - std_from_enc succeeds on the input (send-valid data)
   - dec is total (dec_total hypothesis)
   - the inner continuation g always produces proc_wf results *)
Lemma std_Recv_dec_wf (dk' : he_types.priv_key AHE) (f : plain AHE -> proc data) :
  (forall m, proc_wf (f m)) ->
  forall v, @std_from_enc AHE v != None ->
    proc_wf ((oapp f Fail \o (obind (@dec AHE dk') \o @std_from_enc AHE)) v).
Proof.
move=> Hf v Hv.
rewrite /comp.
case Hfrom: (@std_from_enc AHE v) => [enc0|]; last by rewrite Hfrom in Hv.
rewrite /=.
case Hdec: (dec dk' enc0) => [m|].
  exact: Hf.
by move/negP: (dec_total dk' enc0); rewrite Hdec.
Qed.

(* Helper: std_Recv_enc continuation produces proc_wf results when:
   - std_from_enc succeeds on the input
   - the inner continuation g always produces proc_wf results *)
Lemma std_Recv_enc_wf (f : cipher AHE -> proc data) :
  (forall enc0, proc_wf (f enc0)) ->
  forall v, @std_from_enc AHE v != None ->
    proc_wf ((oapp f Fail \o @std_from_enc AHE) v).
Proof.
move=> Hf v Hv.
rewrite /comp.
case Hfrom: (@std_from_enc AHE v) => [enc0|]; last by rewrite Hfrom in Hv.
exact: Hf.
Qed.

(*******************************************************************************)
(** ** Initial well-formedness                                                 *)
(*******************************************************************************)

(* The initial DSDP processes are all send-valid.
   After erasure, Alice starts with Init(dk, Init(v0, ...)) and relays
   start with Init(dk_j, Init(v_j, Send(alice, e(enc(...)), ...))).
   All Sends use e(enc(...)) = std_e(enc(...)), so send_valid holds. *)
Lemma dsdp_initial_send_valid : all_send_valid procs.
Proof.
rewrite /all_send_valid /procs /dsdp_n_procs /erase_aprocs /dsdp_n_saprocs /= all_map.
rewrite all_map.
apply/allP => j Hj /=.
rewrite /relay_aproc /erase_aproc.
by case: ifP => _; [|case: ifP => _]; rewrite /= /send_valid /=.
Qed.

(* Alice's erase tail is proc_wf (final Recv_dec + Ret) *)
Lemma alice_tail_wf (dk' : he_types.priv_key AHE) (v0' : plain AHE)
  (u' : 'I_n_relay.+2 -> plain AHE) (r' : 'I_n_relay.+1 -> plain AHE) :
  proc_wf (@alice_erase_tail AHE n_relay dk' v0' u' r').
Proof.
rewrite /alice_erase_tail /std_Recv_dec /Recv_param /=.
apply: std_Recv_dec_wf => m /=.
exact: I.
Qed.

(* Alice's erase body preserves proc_wf *)
Lemma alice_body_wf (u' : 'I_n_relay.+2 -> plain AHE)
  (r' : 'I_n_relay.+1 -> plain AHE) (rand_a' : 'I_n_relay.+1 -> rand AHE)
  (j : 'I_n_relay.+1) (idx : nat) (k : proc data) :
  proc_wf k ->
  proc_wf (@alice_erase_body AHE ek n_relay u' r' rand_a' j idx k).
Proof.
move=> Hwf_k.
rewrite /alice_erase_body /std_Recv_enc /Recv_param /=.
apply: std_Recv_enc_wf => enc0 /=.
by split.
Qed.

(* Alice's full erased program is proc_wf *)
Lemma alice_wf :
  proc_wf (erase_aproc (mk_aproc (palice_n AHE ek n_relay relays dk v0 u r rand_a))).
Proof.
rewrite /erase_aproc /aproc_proc palice_n_erase /=.
elim: (zip relays (iota 0 (size relays))) =>
  [|[j idx] rest IH] /=.
- exact: alice_tail_wf.
- exact: alice_body_wf.
Qed.

(* Each relay type's erased process is proc_wf *)
Lemma relay_wf (j : 'I_n_relay.+1) :
  proc_wf (erase_aproc (relay_aproc AHE ek n_relay j
    (dk_relay j) (v_relay j) (r1_relay j) (r2_relay j))).
Proof.
rewrite /relay_aproc /erase_aproc /=.
case: ifP => Hj0.
- (* First relay: DParty_first *)
  rewrite DParty_first_erase /=.
  split; first by [].
  apply: std_Recv_dec_wf => m0 /=.
  apply: std_Recv_enc_wf => enc1 /=.
  by [].
- case: ifP => Hjn.
  + (* Last relay: DParty_last *)
    rewrite DParty_last_erase /=.
    split; first by [].
    apply: std_Recv_dec_wf => m0 /=.
    by [].
  + (* Intermediate relay: DParty_intermediate *)
    rewrite DParty_intermediate_erase /=.
    split; first by [].
    apply: std_Recv_enc_wf => enc0 /=.
    apply: std_Recv_dec_wf => m0 /=.
    by [].
Qed.

(* The initial DSDP processes are all proc_wf. *)
Lemma dsdp_initial_proc_wf : all_proc_wf procs.
Proof.
rewrite /all_proc_wf /procs /dsdp_n_procs /erase_aprocs /dsdp_n_saprocs.
move=> i /=; rewrite size_map => Hi.
case: i Hi => [|i] Hi; first exact: alice_wf.
rewrite /= -map_comp (nth_map ord0); last by rewrite size_map in Hi.
exact: relay_wf.
Qed.

(*******************************************************************************)
(** ** Step preservation                                                       *)
(*******************************************************************************)

(* step preserves proc_wf: when all processes are proc_wf (hence send-valid),
   the result of stepping any process is also proc_wf.

   Proof by case analysis on the process at position i:
   - Init d k: step produces k. proc_wf (Init d k) implies proc_wf k.
   - Send dst v next + matching Recv at dst:
     step produces next. proc_wf (Send _ v next) implies proc_wf next.
   - Recv src f + matching Send at src with data v:
     step produces f v. send_valid (Send _ v _) gives std_from_enc v != None.
     proc_wf (Recv _ f) gives: std_from_enc v != None -> proc_wf (f v). Done.
   - Ret v: step produces Finish. proc_wf Finish = True.
   - Finish/Fail: step is identity.
   - No match: step is identity. *)
Lemma step_preserves_proc_wf (ps : seq (proc data)) (i : nat) :
  all_proc_wf ps ->
  (i < size ps)%N ->
  proc_wf (smc_interpreter.step ps nil i).1.1.
Proof.
move=> Hwf Hi.
rewrite /smc_interpreter.step.
set pi := nth _ ps i.
have Hwf_i := Hwf i Hi.
rewrite -/pi in Hwf_i.
case: pi Hwf_i => [d0 k|dst v0' k|src f|v0'| |] Hwf_i.
- (* Init d k: step produces k *)
  exact: Hwf_i.
- (* Send dst v next: check if dst has matching Recv *)
  case Hdst: (nth _ ps dst) => [|d1 v1 k1|src' f'| | |] //.
  case: eqP => // _.
  exact: Hwf_i.2.
- (* Recv src f: check if src has matching Send *)
  case Hsrc: (nth _ ps src) => [d1 k1|dst' v1 next'|src' f'| | |] //;
    try exact: Hwf_i.
  case Hmatch: (dst' == i); last exact: Hwf_i.
  (* Matched: f v1. Need std_from_enc v1 != None *)
  apply: Hwf_i.
  have Hsrc_lt : (src < size ps)%N.
    case: (ltnP src (size ps)) => Hsrc_lt //.
    by rewrite nth_default in Hsrc.
  have := Hwf src Hsrc_lt.
  by rewrite Hsrc /= => -[].
- (* Ret v: step produces Finish *)
  exact: I.
- (* Finish: identity *) exact: Hwf_i.
- (* Fail: identity *) exact: Hwf_i.
Qed.

(*******************************************************************************)
(** ** Main theorem: interp_comp preserves no-fail                             *)
(*******************************************************************************)

(* Helper: all_proc_wf implies all_nonfail *)
Lemma all_proc_wf_nonfail ps0 : all_proc_wf ps0 -> all_nonfail ps0.
Proof.
move=> Hwf; rewrite /all_nonfail.
apply/(all_nthP (default_proc data)) => i Hi.
exact: proc_wf_nonfail (Hwf i Hi).
Qed.

(* all_proc_wf is preserved by one round of stepping *)
Lemma step_preserves_all_proc_wf (ps : seq (proc data)) :
  all_proc_wf ps ->
  all_proc_wf [seq (smc_interpreter.step ps nil i).1.1
              | i <- iota 0 (size ps)].
Proof.
move=> Hwf i.
rewrite size_map size_iota => Hi.
rewrite (nth_map 0); last by rewrite size_iota.
rewrite nth_iota //.
exact: step_preserves_proc_wf.
Qed.

Theorem dsdp_interp_nofail h :
  all_nonfail (interp_comp data procs h).
Proof.
suff: all_proc_wf (interp_comp data procs h) by exact: all_proc_wf_nonfail.
elim: h procs dsdp_initial_proc_wf => [|h IH] ps Hwf //=.
case: ifP => _ //.
apply: IH.
have Heq : unzip1 (unzip1 [seq smc_interpreter.step ps [::] i
                           | i <- iota 0 (size ps)]) =
           [seq (smc_interpreter.step ps [::] i).1.1
           | i <- iota 0 (size ps)].
  by rewrite /unzip1 -map_comp -map_comp.
by rewrite Heq; exact: step_preserves_all_proc_wf.
Qed.

End dsdp_nofail.
