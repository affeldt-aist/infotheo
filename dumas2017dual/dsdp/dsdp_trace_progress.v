(* dsdp_trace_progress.v — Concrete trace characterization for N-party DSDP

   This file extends dsdp_entropy_trace.v (which proves n_party_correctness)
   with full trace content characterization: Alice's accumulated rsteps trace
   contains exactly [d(result); di_e(tail_cipher); di_e(c_{n-1}); ...;
   di_e(c_0); d(v0); priv_key(dk)] where each c_j is the concrete
   re-encryption from relay j.

   FUTURE WORK (3D): Operational-to-distributional bridge
   ======================================================
   The distributional security is proved separately in dsdp_security.v
   (trace_eavesdropper_security_n). To connect operational traces (rsteps)
   to the distributional model (AliceTraces_n : {RV P -> trace_proj_n_T}),
   the following foundational infrastructure is needed:

   1. T_construction: Concrete sample space T : finType as product of
      all randomness spaces (rand AHE, plain AHE, etc.)
   2. P_construction: Joint distribution P : R.-fdist T
   3. enc_msg bridge: Coercion between cipher AHE (operational) and
      enc_msg : finType (security)
   4. sampling_model: Map w : T to random values used by rsteps
   5. trace_to_AliceTraces_n: Master bridge showing operational trace
      at sample point w equals AliceTraces_n w (Very Hard)
   6. trace_entropy_bridge: H(VarRV | AliceTraces_n) = H(VarRV | op_trace)
   7. operational_security_n: H(VarRV | op_trace) >= log(m^n_relay)

   This bridge is a separate research contribution (~1000+ lines).
   See the plan at .claude/plans/fuzzy-plotting-wren.md for details.
*)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap matrix lra reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter.
Require Import smc_session_types smc_interpreter_sound.
Require Import homomorphic_encryption dsdp_interface dsdp_pismc.
Require Import dsdp_progress dsdp_entropy_trace.

Import GRing.Theory.
Import Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(* Section 3C: Data type injectivity                                          *)
(*                                                                            *)
(* The standard DSDP interface encodes data as a 4-way sum type:              *)
(*   std_data = (plain + cipher + priv_key + pub_key)%type                   *)
(* These lemmas establish injectivity of each injection, needed to            *)
(* decode concrete values from operational traces.                            *)
(******************************************************************************)

Section data_injectivity.

Variable AHE : AHEncType.
Let DI := Standard_DSDP_Interface AHE.

Lemma di_e_inj (c1 c2 : cipher AHE) :
  di_e DI c1 = di_e DI c2 -> c1 = c2.
Proof. by move=> []. Qed.

Lemma di_d_inj (m1 m2 : plain AHE) :
  di_d DI m1 = di_d DI m2 -> m1 = m2.
Proof. by move=> []. Qed.

Lemma di_priv_key_inj (k1 k2 : priv_key AHE) :
  di_priv_key DI k1 = di_priv_key DI k2 -> k1 = k2.
Proof. by move=> []. Qed.

(* di_from_enc_e already exists as std_from_enc_e in dsdp_interface.v *)

End data_injectivity.

(******************************************************************************)
(* Section 3A: Trace accumulation invariant                                   *)
(*                                                                            *)
(* Threads concrete trace values through the multi-round dsdp_inv induction.  *)
(* At each dsdp_inv phase, Alice's accumulated rsteps trace equals a         *)
(* predictable sequence of ciphertexts and initial values.                   *)
(******************************************************************************)

Section trace_accumulation.

Variable AHE : AHEncType.
Variable ek : party_id -> pub_key AHE.
Variable n_relay : nat.
Hypothesis Hn_relay : (0 < n_relay)%N.

Let DI := Standard_DSDP_Interface AHE.
Let data := di_data DI.
Let n_parties := n_relay.+2.

Variable dk : priv_key AHE.
Variable dk_relay : 'I_n_relay.+1 -> priv_key AHE.

Variable relays : seq 'I_n_relay.+1.
Hypothesis Hrelays : size relays = n_relay.+1.
Hypothesis Hrelays_id : forall k : 'I_n_relay.+1, nth ord0 relays k = k.

Hypothesis dec_total : forall dk' c, @dec AHE dk' c != None.
Hypothesis key_alice : ek alice_idx = pub_of_priv dk.
Hypothesis key_relay : forall j : 'I_n_relay.+1,
  ek (nat_to_party_id j.+1) = pub_of_priv (dk_relay j).

Variable v0 : plain AHE.
Variable u : 'I_n_relay.+2 -> plain AHE.
Variable r : 'I_n_relay.+1 -> plain AHE.
Variable rand_a : 'I_n_relay.+1 -> rand AHE.
Variable v_relay : 'I_n_relay.+1 -> plain AHE.
Variables (r1_relay r2_relay : 'I_n_relay.+1 -> rand AHE).

Let inv := dsdp_inv AHE ek n_relay Hn_relay dk dk_relay relays v0 u r rand_a
  v_relay r1_relay r2_relay.

Let d := di_d DI.
Let e := di_e DI.
Let priv_key_inj := di_priv_key DI.

Let procs := @dsdp_n_procs AHE ek n_relay relays dk v0 u r rand_a
  dk_relay v_relay r1_relay r2_relay.

Let Hsize : size procs = n_parties.
Proof. by rewrite /procs size_dsdp_n_procs Hrelays. Qed.

Let procs_tup : n_parties.-tuple (proc data) :=
  @Tuple _ _ procs (introT eqP Hsize).

(* The accumulated trace invariant: at each dsdp_inv state, Alice's
   rsteps trace (tnth tr ord0) equals the expected sequence of
   concrete ciphertexts prepended to the initial [d v0; priv_key dk]. *)

(* Expected cipher from relay j's AR phase *)
Let cipher_j (j : 'I_n_relay.+1) : data :=
  e (enc (ek (nat_to_party_id j.+1)) (v_relay j) (r1_relay j)).

(* Expected accumulated trace after completing AR phases 0..j-1 *)
Fixpoint alice_trace_after_AR (j : nat) : seq data :=
  match j with
  | 0 => [:: d v0; priv_key_inj dk]
  | k.+1 =>
      if (k < n_relay.+1)%N =P true is ReflectT kn then
        cipher_j (Ordinal kn) :: alice_trace_after_AR k
      else alice_trace_after_AR k
  end.

(* TODO: Prove the trace accumulation lemmas.
   These require threading alice_trace_concrete_AR / alice_trace_concrete_tail
   through the inv_rsteps_ret_terminates induction. See the plan for details. *)

End trace_accumulation.
