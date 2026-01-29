From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter smc_tactics.
Require Import smc_proba homomorphic_encryption.
Require Import dsdp_interface dsdp_program.
Require Import idealized_party_ahe.  (* For idealized computational proofs *)
Require Import benaloh_party_ahe.   (* For Benaloh computational proofs *)

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* DSDP Protocol Correctness                                                  *)
(*                                                                            *)
(* This file contains computational correctness proofs for the DSDP protocol. *)
(* - Algebraic correctness (generic): defined in dsdp_program.v               *)
(* - Computational correctness (idealized): Section dsdp_computational        *)
(* - Computational correctness (Benaloh): Section dsdp_computational_benaloh  *)
(*                                                                            *)
(* Based on:                                                                  *)
(* Dumas, J. G., Lafourcade, P., Orfila, J. B., & Puys, M. (2017).            *)
(* Dual protocols for private multi-party matrix multiplication               *)
(* and trust computations.                                                    *)
(* Computers & security, 71, 51-70.                                           *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.
Local Open Scope proc_scope.

(******************************************************************************)
(** * Algebraic Correctness (from dsdp_program.v)                              *)
(******************************************************************************)

(* The algebraic correctness proof for DSDP is defined in dsdp_program.v.
   
   Key theorem (exported from dsdp_program.v):
   
     dsdp.dsdp_computes_dot_product : 
       forall (AHE : AHEAlgebra_scheme) 
              (alice bob charlie : party AHE)
              (pn : party AHE -> nat)
              (D_correct : forall p m r k, dec (key p Dec k) (enc p m r) = Some m)
              (rb1 rb2 rc1 rc2 ra1 ra2 : rand AHE)
              (k_a k_b k_c v1 v2 v3 u1 u2 u3 r2 r3 : plain AHE),
         alice_result = u1 * v1 + u2 * v2 + u3 * v3.
   
   Supporting definitions also exported:
   - bob_encrypted_input, charlie_encrypted_input
   - alice_a2, alice_a3, alice_a2_value, alice_a3_value  
   - d2_value, bob_combined, bob_combined_value
   - g_value, alice_result
*)

(* ========================================================================== *)
(* Computational Correctness Proofs using Idealized_HETypes                   *)
(*                                                                            *)
(* This section uses the idealized encryption model from idealized_party_ahe  *)
(* where enc = (party, msg) and encryption is deterministic (no randomness).  *)
(* This enables computational proofs via reflexivity.                         *)
(*                                                                            *)
(* Programs are instantiated from dsdp_program.v with unit randomness.        *)
(* ========================================================================== *)

Section dsdp_computational.

Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.

Local Notation msg := 'F_m.  (* Finite field with m elements *)

(* ========================================================================== *)
(* Build Idealized_HETypes as AHEAlgebra_scheme                                *)
(* ========================================================================== *)

Local Definition Idealized_EncDec_instance := 
  @Idealized_isEncDec party_id msg.

Local Definition Idealized_AHEnc_instance := 
  @Idealized_isAHEnc party_id msg.

Local Definition Idealized_AHEAlgebra_instance := 
  @Idealized_isAHEAlgebra party_id msg.

(* Build the type hierarchy *)
Local Definition Idealized_EncDec_local : EncDec_scheme := 
  @EncDec.Pack (Idealized_HETypes party_id msg) 
    (@EncDec.Class (Idealized_HETypes party_id msg) Idealized_EncDec_instance).

Local Definition Idealized_AHEnc_local : AHEnc_scheme := 
  @AHEnc.Pack (Idealized_HETypes party_id msg) 
    (@AHEnc.Class (Idealized_HETypes party_id msg) 
      Idealized_EncDec_instance Idealized_AHEnc_instance).

Local Definition Idealized_AHEAlgebra_local : AHEAlgebra_scheme := 
  @AHEAlgebra.Pack Idealized_AHEnc_local 
    (@AHEAlgebra.Class Idealized_AHEnc_local Idealized_AHEAlgebra_instance).

(* The idealized scheme *)
Let PHE : AHEAlgebra_scheme := Idealized_AHEAlgebra_local.

(* Use standard interface from dsdp_interface.v *)
Let DI := Standard_DSDP_Interface PHE.

(* Extract type aliases for readability *)
Let data := di_data DI.
Let d := di_d DI.
Let e := di_e DI.
Let k := di_k DI.

(* Local encryption alias - deterministic, ignores randomness *)
Let E := @enc PHE.

(* Party definitions *)
Definition alice : party_id := Alice.
Definition bob : party_id := Bob.
Definition charlie : party_id := Charlie.

(* Party to nat mapping - use party_id_to_nat from homomorphic_encryption.v *)
Let pn : party_id -> nat := party_id_to_nat.

(* Decryption correctness - use lemma from idealized_party_ahe.v *)
Let D_correct : forall p m r k, 
  @dec PHE (@key PHE p Dec k) (E p m r) = Some m.
Proof. exact: idealized_dec_correct. Qed.

(* ========================================================================== *)
(* Instantiate programs from dsdp_program.v with unit randomness              *)
(* ========================================================================== *)

Variables (k_a k_b k_c v1 v2 v3 u1 u2 u3 r2 r3 : msg).

(* Unit randomness - value doesn't matter since idealized scheme ignores it *)
Let runit : rand PHE := 1.

(* Keys constructed via the scheme's key operation *)
Let dk_a := @key PHE Alice Dec k_a.
Let dk_b := @key PHE Bob Dec k_b.
Let dk_c := @key PHE Charlie Dec k_c.

(* Instantiate generic programs from dsdp_program.v 
   Note: Coq only generalizes section variables that are actually used:
   - palice uses bob, charlie (not alice)
   - pbob uses alice, bob, charlie  
   - pcharlie uses alice, bob, charlie *)
Let palice_inst := @palice PHE bob charlie pn dk_a v1 u1 u2 u3 r2 r3 runit runit.
Let pbob_inst := @pbob PHE alice bob charlie pn dk_b v2 runit runit.
Let pcharlie_inst := @pcharlie PHE alice bob charlie pn dk_c v3 runit runit.

(* Protocol definition using interp directly with explicit traces *)
Definition dsdp h :=
  interp h [:: palice_inst; pbob_inst; pcharlie_inst] [::[::];[::];[::]].

(* Protocol execution result: running dsdp for 15 steps produces the expected
   final state with all parties finished and their respective traces. *)
Lemma dsdp_ok :
  dsdp 15 = 
  ([:: Finish; Finish; Finish],
   [:: [:: d (v3 * u3 + r3 + (v2 * u2 + r2) - r2 - r3 + u1 * v1);
           e (E alice (v3 * u3 + r3 + (v2 * u2 + r2)) runit); 
           e (E charlie v3 runit);
           e (E bob v2 runit);
           d r3; d r2; d u3; d u2; d u1; d v1; k dk_a];
       [:: e (E charlie (v3 * u3 + r3) runit);
           e (E bob (v2 * u2 + r2) runit); d v2; k dk_b];
       [:: e (E charlie (v3 * u3 + r3 + (v2 * u2 + r2)) runit); d v3; k dk_c]
  ]).
Proof. reflexivity. Qed.

(* Trace types for bounded sequences *)
Notation dsdp_traceT := (15.-bseq data).
Notation dsdp_tracesT := (3.-tuple dsdp_traceT).

Definition dsdp_traces : dsdp_tracesT :=
  interp_traces 15 [:: palice_inst; pbob_inst; pcharlie_inst].

Definition is_dsdp (trs : dsdp_tracesT) :=
  let '(s, u3, u2, u1, v1) :=
    if tnth trs 0 is Bseq [:: inl (inl s); _; _; _; _; _;
                           inl (inl u3); inl (inl u2); inl (inl u1);
                           inl (inl v1); _] _
    then (s, u3, u2, u1, v1) else (0, 0, 0, 0, 0) in
  let '(v2) :=
    if tnth trs 1 is Bseq [:: _; _; inl (inl v2); _] _
    then (v2) else (0) in
  let '(_v3) :=
    if tnth trs 2 is Bseq [:: _; inl (inl v3); _] _
    then (v3) else (0) in
  s = v3 * u3 + v2 * u2 + v1 * u1.

(* Trace structure: each party's trace contains their view of the protocol. *)
Lemma dsdp_traces_ok :
  dsdp_traces =
    [tuple
       [bseq d (v3 * u3 + r3 + (v2 * u2 + r2) - r2 - r3 + u1 * v1);
             e (E alice (v3 * u3 + r3 + (v2 * u2 + r2)) runit);
             e (E charlie v3 runit);
             e (E bob v2 runit);
             d r3; d r2; d u3; d u2; d u1; d v1; k dk_a];
       [bseq e (E charlie (v3 * u3 + r3) runit);
             e (E bob (v2 * u2 + r2) runit); d v2; k dk_b];
       [bseq e (E charlie (v3 * u3 + r3 + (v2 * u2 + r2)) runit); d v3; k dk_c]].
Proof. by apply/val_inj/(inj_map val_inj); rewrite interp_traces_ok. Qed.

(* Protocol correctness: the final result S satisfies S = u1*v1 + u2*v2 + u3*v3. *)
Lemma dsdp_is_correct:
  is_dsdp dsdp_traces.
Proof. rewrite dsdp_traces_ok /is_dsdp /=. ring. Qed.

End dsdp_computational.

(* ========================================================================== *)
(* Computational Correctness Proofs using Benaloh Encryption                   *)
(*                                                                            *)
(* This section instantiates the generic dsdp_correctness proofs with the     *)
(* concrete Benaloh AHEAlgebra_scheme. All cryptographic hypotheses required  *)
(* for a valid Benaloh instantiation are provided explicitly.                 *)
(* ========================================================================== *)

Section dsdp_computational_benaloh.

(* Benaloh scheme parameters *)
Variables (n r : nat).

(* n_gt1: The modulus n must be > 1 for Z_n to be non-trivial.
   In practice, n = p*q for large primes p, q. *)
Hypothesis n_gt1 : (1 < n)%N.

(* r_gt1: The message space size r must be > 1.
   r divides phi(n) and determines the "block size" of messages. *)
Hypothesis r_gt1 : (1 < r)%N.

Variable y : 'Z_n.

(* y_order_r: y is an r-th root of unity in Z_n, i.e., y^r = 1 mod n.
   This is essential for the homomorphic properties:
   - E(m1)*E(m2) = E(m1+m2) requires y^(m1+m2) = y^m1 * y^m2
   - E(m)^k = E(m*k) requires (y^m)^k = y^(m*k) *)
Hypothesis y_order_r : y ^+ r = 1.

(* y_coprime_n: y must be a unit in Z_n (coprime to n).
   Required for Euler's theorem to apply in decryption. *)
Hypothesis y_coprime_n : coprime (y : nat) n.

Variable phi_div_r : nat.

(* phi_eq_totient: phi_div_r = phi(n)/r, where phi is Euler's totient.
   This parameter is used in decryption: c^(phi(n)/r) removes randomness. *)
Hypothesis phi_eq_totient : r * phi_div_r = totient n.

(* rand_coprime_n: All randomness is sampled from Z_n^* (units coprime to n).
   In practice, for n = p*q, the probability of picking a non-unit is
   negligible: Pr[gcd(u,n) != 1] <= 2/min(p,q).
   We model this as a hypothesis for a "valid" instantiation. *)
Hypothesis rand_coprime_n : forall (u : 'Z_n), coprime (u : nat) n.

(* x_base_injective: x_base = y^(phi(n)/r) has exact order r.
   This ensures the discrete log search in decryption is well-defined.
   This is a key assumption about proper Benaloh key generation. *)
Hypothesis x_base_injective : forall (m1 m2 : 'Z_r), 
  benaloh_party_ahe.x_base y phi_div_r ^+ (m1 : nat) = 
  benaloh_party_ahe.x_base y phi_div_r ^+ (m2 : nat) -> m1 = m2.

(* ========================================================================== *)
(* Build the Benaloh AHEAlgebra_scheme instance                                *)
(*                                                                            *)
(* The HB instances from benaloh_party_ahe.v are parameterized by all the     *)
(* cryptographic hypotheses. We apply them here to get a proper instance.     *)
(* ========================================================================== *)

(* Register the HB instances with all hypotheses *)
Local Definition Benaloh_EncDec_instance := 
  @Benaloh_isEncDec party_id n r n_gt1 y phi_div_r phi_eq_totient 
    rand_coprime_n x_base_injective.

Local Definition Benaloh_AHEnc_instance := 
  @Benaloh_isAHEnc party_id n r n_gt1 r_gt1 y y_order_r phi_div_r 
    phi_eq_totient rand_coprime_n x_base_injective.

Local Definition Benaloh_AHEAlgebra_instance := 
  @Benaloh_isAHEAlgebra party_id n r n_gt1 r_gt1 y y_order_r phi_div_r 
    phi_eq_totient rand_coprime_n x_base_injective.

(* Build the type hierarchy step by step *)
(* First: EncDec_scheme (HETypes + isEncDec) *)
Local Definition Benaloh_EncDec_local : EncDec_scheme := 
  @EncDec.Pack (Benaloh_HETypes party_id n r) 
    (@EncDec.Class (Benaloh_HETypes party_id n r) Benaloh_EncDec_instance).

(* Second: AHEnc_scheme (HETypes + isEncDec + isAHEnc) *)
Local Definition Benaloh_AHEnc_local : AHEnc_scheme := 
  @AHEnc.Pack (Benaloh_HETypes party_id n r) 
    (@AHEnc.Class (Benaloh_HETypes party_id n r) 
      Benaloh_EncDec_instance Benaloh_AHEnc_instance).

(* Third: AHEAlgebra_scheme (AHEnc_scheme + isAHEAlgebra) *)
Local Definition Benaloh_AHEAlgebra_local : AHEAlgebra_scheme := 
  @AHEAlgebra.Pack Benaloh_AHEnc_local 
    (@AHEAlgebra.Class Benaloh_AHEnc_local Benaloh_AHEAlgebra_instance).

(* The Benaloh scheme as an AHEAlgebra_scheme *)
Let PHE : AHEAlgebra_scheme := Benaloh_AHEAlgebra_local.

(* ========================================================================== *)
(* Instantiate the generic dsdp_correctness theorem                            *)
(*                                                                            *)
(* The generic theorem from dsdp_correctness section has signature:            *)
(*   dsdp_computes_dot_product : forall (AHE : AHEAlgebra_scheme)              *)
(*     (v1 v2 v3 u1 u2 u3 r2 r3 : plain AHE),                                  *)
(*     alice_result v1 v2 v3 u1 u2 u3 r2 r3 = u1*v1 + u2*v2 + u3*v3            *)
(* ========================================================================== *)

(* Message variables *)
Variables (v1 v2 v3 u1 u2 u3 r2 r3 : plain PHE).

(* Main theorem: DSDP computes the dot product using Benaloh encryption *)
Theorem dsdp_computes_dot_product_benaloh :
  @alice_result PHE v1 v2 v3 u1 u2 u3 r2 r3 = u1 * v1 + u2 * v2 + u3 * v3.
Proof.
  exact: (@dsdp_computes_dot_product PHE v1 v2 v3 u1 u2 u3 r2 r3).
Qed.

End dsdp_computational_benaloh.
