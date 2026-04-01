(*******************************************************************************)
(** * N-Party DSDP rsteps from Proved Theorems                                *)
(*******************************************************************************)

(* General n-party rsteps theorem. No-fail and termination are derived from
   the proved theorems in dsdp_nofail.v and dsdp_progress.v, given:
   - Key consistency (key_alice, key_relay)
   - Decryption totality (dec_total)
   - Relay enumeration identity (Hrelays_id)
   - Sufficient fuel (h >= [> saprocs])

   This file is separate from dsdp_pismc.v to avoid a circular import:
   dsdp_nofail.v and dsdp_progress.v both import dsdp_pismc.v. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
Require Import ssr_ext.
Require Import smc_interpreter smc_session_types.
Require Import homomorphic_encryption.
Require Import dsdp_interface dsdp_session_types dsdp_program.
Require Import dsdp_pismc dsdp_nofail dsdp_progress.

Local Open Scope ring_scope.

Section dsdp_n_rsteps_general.

Variable AHE : AHEncType.  (* Additively homomorphic encryption scheme *)
Variable ek : party_id -> pub_key AHE.  (* Public key mapping per party *)
Variable n_relay : nat.  (* Number of relay parties; total parties = n_relay + 2 *)
Hypothesis Hn_relay : (0 < n_relay)%N.  (* >= 3 parties for deadlock-freedom *)

Let DI := Standard_DSDP_Interface AHE.
Let data := di_data DI.  (* Protocol data type: plain + cipher + keys *)

(* Key material *)
Variables (dk : priv_key AHE) (v0 : plain AHE).  (* Alice's key and input *)
Variable dk_relay : 'I_n_relay.+1 -> priv_key AHE.  (* Relay private keys *)

(* Key consistency: each party's private key matches the public key mapping *)
Hypothesis key_alice : ek alice_idx = pub_of_priv dk.
Hypothesis key_relay : forall j : 'I_n_relay.+1,
  ek (nat_to_party_id j.+1) = pub_of_priv (dk_relay j).

(* Decryption totality: dec never returns None *)
Hypothesis dec_total : forall dk' c, @dec AHE dk' c != None.

(* Protocol parameters: mirrors dsdp_n_procs construction *)
Variable relays : seq 'I_n_relay.+1.
Hypothesis Hrelays : size relays = n_relay.+1.
Hypothesis Hrelays_id : forall k : 'I_n_relay.+1, nth ord0 relays k = k.

Variable u : 'I_n_relay.+2 -> plain AHE.  (* Per-party blinding factors *)
Variable r : 'I_n_relay.+1 -> plain AHE.  (* Per-relay random masks *)
Variable rand_a : 'I_n_relay.+1 -> rand AHE.  (* Alice's encryption randomness *)
Variable v_relay : 'I_n_relay.+1 -> plain AHE.  (* Relay input values *)
Variables (r1_relay r2_relay : 'I_n_relay.+1 -> rand AHE).  (* Relay randomness *)

Let procs := @dsdp_n_procs AHE ek n_relay relays dk v0 u r rand_a
  dk_relay v_relay r1_relay r2_relay.

Let saprocs := @dsdp_n_saprocs AHE ek n_relay relays dk v0 u r rand_a
  dk_relay v_relay r1_relay r2_relay.

Let n_parties := (n_relay.+1).+1.  (* = n_relay + 2: Alice + (n_relay+1) relays *)

(* Cast to tuple: interp_sound requires n.-tuple, not seq *)
Let Hsize : size procs = n_parties.
Proof. by rewrite /procs size_dsdp_n_procs Hrelays. Qed.

Let procs_tup : n_parties.-tuple (proc data) :=
  @Tuple _ _ procs (introT eqP Hsize).

(* Fuel for the interpreter: must be at least the sum of all process fuels *)
Variable h : nat.
Hypothesis Hfuel : (h >= [> saprocs])%N.

(* Derive no-fail from dsdp_nofail.v
   Note: key_alice, key_relay, Hrelays are not used by dsdp_interp_nofail
   (dropped during section closure — the no-fail proof only needs dec_total). *)
Let dsdp_no_fail : all_nonfail (interp_comp data procs h) :=
  @dsdp_interp_nofail AHE ek n_relay dk dk_relay
    dec_total relays v0 u r rand_a v_relay r1_relay r2_relay h.

(* Derive termination from dsdp_progress.v *)
Let dsdp_terminates : all_terminated (interp_comp data procs h) :=
  @dsdp_interp_terminates AHE ek n_relay Hn_relay dk dk_relay dec_total
    relays Hrelays Hrelays_id v0 u r rand_a v_relay
    r1_relay r2_relay h Hfuel.

(* N-party rsteps with real traces: the protocol admits a valid
   multi-step reduction sequence where each party's trace contains
   the actual communicated data (init values, ciphertexts, return values).

   Proof strategy: interp_sound provides rsteps + traces for any fuel h,
   with process states matching interp_comp. No-fail and termination are
   derived from the proved theorems above. *)
Theorem dsdp_n_rsteps :
  exists (final : n_parties.-tuple (proc data)) tr,
    rsteps procs_tup final tr /\
    all_terminated (tval final) /\
    all_nonfail (tval final).
Proof.
have [final [tr [Hrsteps Hfinal]]] :=
  @interp_sound data n_parties h procs_tup.
exists final, tr; split; first exact: Hrsteps.
by rewrite Hfinal.
Qed.

End dsdp_n_rsteps_general.
