From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter.
Require Import homomorphic_encryption.
Require Import smc_session_types.
Require Import dsdp_interface dsdp_program.
Require Import idealized_ahe.  (* For idealized computational proofs *)
Require Import benaloh_ahe.   (* For Benaloh computational proofs *)
Require Import paillier_ahe.  (* For Paillier computational proofs *)

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
(* - Computational correctness (Paillier): Section dsdp_computational_paillier*)
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
Local Open Scope sproc_scope.

(* ========================================================================== *)
(* Computational Correctness Proofs using Idealized_HETypes                   *)
(*                                                                            *)
(* This section uses the idealized encryption model from idealized_ahe.v      *)
(* where enc(pk, m, r) = m and encryption is deterministic.                   *)
(* This enables computational proofs via reflexivity.                         *)
(*                                                                            *)
(* Programs are instantiated from dsdp_program.v with unit randomness.        *)
(* ========================================================================== *)

Section dsdp_computational.

Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.

Local Notation msg := 'F_m.  (* Finite field with m elements *)

(* ========================================================================== *)
(* Build Idealized_HETypes as AHEncType                                   *)
(* ========================================================================== *)

Local Definition Idealized_EncDec_instance :=
  @Idealized_isEncDec msg.

Local Definition Idealized_AHEnc_instance :=
  @Idealized_isAHEnc msg.

(* Build the type hierarchy *)
Local Definition Idealized_EncDec_local : EncDecType :=
  @EncDec.Pack (Idealized_HETypes msg)
    (@EncDec.Class (Idealized_HETypes msg) Idealized_EncDec_instance).

Local Definition Idealized_AHEnc_local : AHEncType :=
  @AHEnc.Pack (Idealized_HETypes msg)
    (@AHEnc.Class (Idealized_HETypes msg)
      Idealized_EncDec_instance Idealized_AHEnc_instance).

(* The idealized scheme *)
Let AHE : AHEncType := Idealized_AHEnc_local.

(* Use standard interface from dsdp_interface.v *)
Let DI := Standard_DSDP_Interface AHE.

(* Extract type aliases for readability *)
Let data := di_data DI.
Let d := di_d DI.
Let e := di_e DI.
Let k := di_priv_key DI.

(* Party definitions *)
Definition alice : party_id := Alice.
Definition bob : party_id := Bob.
Definition charlie : party_id := Charlie.

(* Party to nat mapping - use party_id_to_nat from homomorphic_encryption.v *)
Let pn : party_id -> nat := party_id_to_nat.

(* ========================================================================== *)
(* Instantiate programs from dsdp_program.v with unit randomness              *)
(* ========================================================================== *)

Variables (k_a k_b k_c v1 v2 v3 u1 u2 u3 r2 r3 : msg).

(* Unit randomness - value doesn't matter since idealized scheme ignores it *)
Let runit : rand AHE := 1.

(* Private keys are just msg values in idealized *)
Let dk_a : priv_key AHE := k_a.
Let dk_b : priv_key AHE := k_b.
Let dk_c : priv_key AHE := k_c.

(* Public keys derived from private keys via pub_of_priv *)
Let pkof := @enc_dec.pub_of_priv AHE.
Let ek (p : party_id) : pub_key AHE :=
  match p with
  | Alice => pkof dk_a
  | Bob => pkof dk_b
  | Charlie => pkof dk_c
  | NoParty => pkof dk_a
  end.

(* Instantiate generic programs from dsdp_program.v
   Note: Coq only generalizes section variables that are actually used:
   - palice uses bob, charlie (not alice)
   - pbob uses alice, bob, charlie
   - pcharlie uses alice, bob, charlie *)
Let palice_inst := @palice AHE bob charlie pn ek dk_a v1 u1 u2 u3 r2 r3 runit runit.
Let pbob_inst := @pbob AHE alice bob charlie pn ek dk_b v2 runit runit.
Let pcharlie_inst := @pcharlie AHE alice bob charlie pn ek dk_c v3 runit runit.

(* Session-typed processes packed via [aprocs ...].
   See dsdp_program.v for detailed explanation of why this pattern is needed. *)
Let dsdp_saprocs : seq (aproc dsdp_dtype data) :=
  [aprocs palice_inst ; pbob_inst ; pcharlie_inst].

Let dsdp_procs : seq (proc data) := erase_aprocs dsdp_saprocs.

(* Protocol definition using interp directly with explicit traces *)
Definition dsdp h := interp h dsdp_procs [::[::];[::];[::]].

(* Protocol execution result: running dsdp for 15 steps produces the expected
   final state with all parties finished and their respective traces.
   In the idealized scheme, enc(pk, m, r) = m, so ciphertexts are just messages. *)
Lemma dsdp_ok :
  dsdp 15 =
  ([:: Finish; Finish; Finish],
   [:: [:: d (v3 * u3 + r3 + (v2 * u2 + r2) - r2 - r3 + u1 * v1);
           e (v3 * u3 + r3 + (v2 * u2 + r2));
           e v3;
           e v2;
           d r3; d r2; d u3; d u2; d u1; d v1; k dk_a];
       [:: e (v3 * u3 + r3);
           e (v2 * u2 + r2); d v2; k dk_b];
       [:: e (v3 * u3 + r3 + (v2 * u2 + r2)); d v3; k dk_c]
  ]).
Proof. reflexivity. Qed.

(* Trace types for bounded sequences *)
Notation dsdp_traceT := (15.-bseq data).
Notation dsdp_tracesT := (3.-tuple dsdp_traceT).

Definition dsdp_traces : dsdp_tracesT :=
  interp_traces 15 dsdp_procs.

Definition is_dsdp (trs : dsdp_tracesT) :=
  let '(s, u3, u2, u1, v1) :=
    if tnth trs 0 is Bseq [:: inl (inl (inl s)); _; _; _;
                           _; _; inl (inl (inl u3)); inl (inl (inl u2));
                           inl (inl (inl u1)); inl (inl (inl v1)); _] _
    then (s, u3, u2, u1, v1) else (0, 0, 0, 0, 0) in
  let '(v2) :=
    if tnth trs 1 is Bseq [:: _; _; inl (inl (inl v2)); _] _
    then (v2) else (0) in
  let '(_v3) :=
    if tnth trs 2 is Bseq [:: _; inl (inl (inl v3)); _] _
    then (v3) else (0) in
  s = v3 * u3 + v2 * u2 + v1 * u1.

(* Trace structure: each party's trace contains their view of the protocol. *)
Lemma dsdp_traces_ok :
  dsdp_traces =
    [tuple
       [bseq d (v3 * u3 + r3 + (v2 * u2 + r2) - r2 - r3 + u1 * v1);
             e (v3 * u3 + r3 + (v2 * u2 + r2));
             e v3;
             e v2;
             d r3; d r2; d u3; d u2; d u1; d v1; k dk_a];
       [bseq e (v3 * u3 + r3);
             e (v2 * u2 + r2); d v2; k dk_b];
       [bseq e (v3 * u3 + r3 + (v2 * u2 + r2)); d v3; k dk_c]].
Proof. by apply/val_inj/(inj_map val_inj); rewrite interp_traces_ok. Qed.

(* Protocol correctness:
  the final result S satisfies S = u1*v1 + u2*v2 + u3*v3. *)
Lemma dsdp_is_correct:
  is_dsdp dsdp_traces.
Proof. rewrite dsdp_traces_ok /is_dsdp /=. ring. Qed.

End dsdp_computational.

(* ========================================================================== *)
(* Computational Correctness Proofs using Benaloh Encryption                  *)
(*                                                                            *)
(* This section instantiates the algebraic dsdp_computes_dot_product theorem  *)
(* with the concrete Benaloh AHEncType.                                   *)
(*                                                                            *)
(* The parameters n, r, n_gt1, r_gt1 are needed to construct the type         *)
(* hierarchy (plain AHE = 'Z_r). The algebraic theorem itself only uses       *)
(* ring operations on plain AHE, so no keys or encryption are involved.       *)
(* ========================================================================== *)

Section dsdp_computational_benaloh.

(* Benaloh scheme parameters *)
Variables (n r : nat).
Hypothesis n_gt1 : (1 < n)%N.
Hypothesis r_gt1 : (1 < r)%N.

(* Build the Benaloh AHEncType instance *)
Local Definition Benaloh_EncDec_local : EncDecType :=
  @EncDec.Pack (BenalohHETypes n r)
    (@EncDec.Class (BenalohHETypes n r) (@Benaloh_isEncDec n r)).

Local Definition Benaloh_AHEnc_local : AHEncType :=
  @AHEnc.Pack (BenalohHETypes n r)
    (@AHEnc.Class (BenalohHETypes n r)
      (@Benaloh_isEncDec n r) (@Benaloh_isAHEnc n r r_gt1)).

Let AHE : AHEncType := Benaloh_AHEnc_local.

(* Message variables *)
Variables (v1 v2 v3 u1 u2 u3 r2 r3 : plain AHE).

(* Main theorem: DSDP computes the dot product using Benaloh encryption *)
Theorem dsdp_computes_dot_product_benaloh :
  @alice_result AHE v1 v2 v3 u1 u2 u3 r2 r3 = u1 * v1 + u2 * v2 + u3 * v3.
Proof. exact: @dsdp_computes_dot_product. Qed.

End dsdp_computational_benaloh.


(* ========================================================================== *)
(* Computational Correctness Proofs using Paillier Encryption                 *)
(*                                                                            *)
(* This section instantiates the algebraic dsdp_computes_dot_product theorem  *)
(* with the concrete Paillier AHEMonoidType.                                  *)
(*                                                                            *)
(* The parameters n, n_gt1 are needed to construct the type hierarchy         *)
(* (plain AHE = 'Z_n). The algebraic theorem itself only uses ring            *)
(* operations on plain AHE, so no keys or encryption are involved.            *)
(* ========================================================================== *)

Section dsdp_computational_paillier.

(* Paillier scheme parameters *)
Variable n : nat.
Hypothesis n_gt1 : (1 < n)%N.

(* Build the Paillier AHEMonoidType instance *)
Local Definition Paillier_EncDec_local : EncDecType :=
  @EncDec.Pack (PaillierHETypes n)
    (@EncDec.Class (PaillierHETypes n) (@Paillier_isEncDec n)).

Local Definition Paillier_AHEnc_local : AHEncType :=
  @AHEnc.Pack (PaillierHETypes n)
    (@AHEnc.Class (PaillierHETypes n)
      (@Paillier_isEncDec n) (@Paillier_isAHEnc n n_gt1)).

Local Definition Paillier_AHEMonoid_local : AHEMonoidType :=
  @AHEMonoid.Pack Paillier_AHEnc_local
    (@AHEMonoid.Class Paillier_AHEnc_local (@Paillier_isAHEMonoid n n_gt1)).

Let AHE : AHEMonoidType := Paillier_AHEMonoid_local.

(* Message variables *)
Variables (v1 v2 v3 u1 u2 u3 r2 r3 : plain AHE).

(* Main theorem: DSDP computes the dot product using Paillier encryption *)
Theorem dsdp_computes_dot_product_paillier :
  @alice_result AHE v1 v2 v3 u1 u2 u3 r2 r3 = u1 * v1 + u2 * v2 + u3 * v3.
Proof. exact: @dsdp_computes_dot_product. Qed.

End dsdp_computational_paillier.
