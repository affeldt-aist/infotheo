From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter smc_tactics.
Require Import smc_proba homomorphic_encryption.
Require Import dsdp_program dsdp_program_alt_syntax.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* DSDP Protocol Correctness                                                  *)
(*                                                                            *)
(* This file contains the correctness proofs for the DSDP protocol.           *)
(* The protocol programs are defined in dsdp_program_alt_syntax.v             *)
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

Local Definition R := Rdefinitions.R.

Section dsdp_correctness.

Variable F : finFieldType.
Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Hypothesis prime_m : prime m.

Local Notation msg := 'F_m.
Let card_msg : #|msg| = m.
Proof. by rewrite card_Fp // pdiv_id. Qed.

Let enc := enc party msg.
Let pkey := pkey party msg.

Notation "u *h w" := (Emul u w) (at level 40).
Notation "u ^h w" := (Epow u w) (at level 40).

(* Data type and wrappers - same as in dsdp_program_alt_syntax *)
Definition alice : party := Alice.
Definition bob : party := Bob.
Definition charlie : party := Charlie.

Definition data := (msg + enc + pkey)%type.
Definition d x : data := inl (inl x).
Definition e x : data := inl (inr x).
Definition k x : data := inr x.

(* Specialized receive operations - fuel-indexed *)
Definition Recv_dec {n} frm pkey (f : msg -> proc data n) : proc data n.+1 :=
  Recv frm (fun x => if x is inl (inr v) then
                       if D pkey v is Some v' then f v' else Fail
                     else Fail).

Definition Recv_enc {n} frm (f : enc -> proc data n) : proc data n.+1 :=
  Recv frm (fun x => if x is inl (inr v) then f v else Fail).

(* Import program definitions from dsdp_program_alt_syntax.
   These are the programs written with the alternative syntax.
   Note: pbob, pcharlie, palice only depend on m_minus_2, not F *)
Let pbob := @dsdp_program_alt_syntax.pbob m_minus_2.
Let pcharlie := @dsdp_program_alt_syntax.pcharlie m_minus_2.
Let palice := @dsdp_program_alt_syntax.palice m_minus_2.

(* Import original program definitions from dsdp_program for comparison *)
Let pbob_orig := @dsdp_program.pbob m_minus_2.
Let pcharlie_orig := @dsdp_program.pcharlie m_minus_2.
Let palice_orig := @dsdp_program.palice m_minus_2.

(******************************************************************************)
(** * Cross-file equivalence: dsdp_program = dsdp_program_alt_syntax          *)
(******************************************************************************)

(* Verify that the alt_syntax programs are definitionally equal to the original *)
Lemma pbob_cross_eq dk v : pbob dk v = pbob_orig dk v.
Proof. reflexivity. Qed.

Lemma pcharlie_cross_eq dk v : pcharlie dk v = pcharlie_orig dk v.
Proof. reflexivity. Qed.

Lemma palice_cross_eq dk v1' u1' u2' u3' r2' r3' : 
  palice dk v1' u1' u2' u3' r2' r3' = palice_orig dk v1' u1' u2' u3' r2' r3'.
Proof. reflexivity. Qed.

(******************************************************************************)

Variables (k_a k_b k_c v1 v2 v3 u1 u2 u3 r2 r3 : msg).

(* Note: must be with concrete values otherwise computation won't go *)
Let dk_a : pkey := (Alice, Dec, k_a). 
Let dk_b : pkey := (Bob, Dec, k_b). 
Let dk_c : pkey := (Charlie, Dec, k_c). 

(* Pack processes into aproc list using [procs ...] notation *)
Definition dsdp_procs : seq (aproc data) :=
  [procs palice dk_a v1 u1 u2 u3 r2 r3; pbob dk_b v2; pcharlie dk_c v3].

Definition dsdp h :=
  interp h dsdp_procs (nseq 3 [::]).

(* Fuel bound computed from program structure:
   - palice: 14, pbob: 7, pcharlie: 6, Total: 27 *)
Definition dsdp_max_fuel : nat := 27.

(* Verify the computed fuel matches *)
Lemma dsdp_max_fuel_ok : dsdp_max_fuel = [> dsdp_procs].
Proof. reflexivity. Qed.

(* Protocol execution result: running dsdp with computed fuel produces the expected
   final state with all parties finished and their respective traces. *)
Lemma dsdp_ok :
  dsdp [> dsdp_procs] = 
  ([:: pack Finish; pack Finish; pack Finish],
   [:: [:: d (v3 * u3 + r3 + (v2 * u2 + r2) - r2 - r3 + u1 * v1);
           e (E alice (v3 * u3 + r3 + (v2 * u2 + r2))); 
           e (E charlie v3);
           e (E bob v2);
           d r3; d r2; d u3; d u2; d u1; d v1; k dk_a];
       [:: e (E charlie (v3 * u3 + r3));
           e (E bob (v2 * u2 + r2)); d v2; k dk_b];
       [:: e (E charlie (v3 * u3 + r3 + (v2 * u2 + r2))); d v3; k dk_c]
  ]).
Proof. reflexivity. Qed.

(* With fuel equal to sum_fuel, evaluation reaches a final state *)
Lemma dsdp_terminates :
  all_final (dsdp [> dsdp_procs]).1.
Proof. reflexivity. Qed.

Notation dsdp_traceT := (dsdp_max_fuel.-bseq data).
Notation dsdp_tracesT := (3.-tuple dsdp_traceT).

Definition dsdp_traces : dsdp_tracesT :=
  interp_traces dsdp_max_fuel dsdp_procs.

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

(* Trace structure: each party's trace contains their view of the protocol.
   Alice sees: final sum S, encrypted values, randoms r2/r3, coefficients u_i, her input v1.
   Bob sees: encrypted partial sums, his input v2.
   Charlie sees: encrypted partial sum, his input v3. *)
Lemma dsdp_traces_ok :
  dsdp_traces =
    [tuple
       [bseq d (v3 * u3 + r3 + (v2 * u2 + r2) - r2 - r3 + u1 * v1);
             e (E alice (v3 * u3 + r3 + (v2 * u2 + r2)));
             e (E charlie v3);
             e (E bob v2);
             d r3; d r2; d u3; d u2; d u1; d v1; k dk_a];
       [bseq e (E charlie (v3 * u3 + r3));
             e (E bob (v2 * u2 + r2)); d v2; k dk_b];
       [bseq e (E charlie (v3 * u3 + r3 + (v2 * u2 + r2))); d v3; k dk_c]].
Proof. by apply/val_inj/(inj_map val_inj); rewrite interp_traces_ok. Qed.

(* Protocol correctness: the final result S satisfies S = u1*v1 + u2*v2 + u3*v3.
   This verifies the DSDP protocol computes the intended dot product. *)
Lemma dsdp_is_correct:
  is_dsdp dsdp_traces.
Proof. rewrite dsdp_traces_ok /is_dsdp /=.
ring.
Qed.

End dsdp_correctness.
