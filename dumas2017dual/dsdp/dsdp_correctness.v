From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter smc_tactics.
Require Import smc_proba smc_session_types homomorphic_encryption.
Require Import dsdp_interface dsdp_program dsdp_program_alt_syntax.

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

Section dsdp_correctness.

(* Parameterize by an AHEAlgebra_scheme instance *)
Variable PHE : AHEAlgebra_scheme.

(* Use standard DSDP interface for data types *)
Let DI := Standard_DSDP_Interface PHE.

(* Extract types from the scheme *)
Let partyT := party PHE.
Let msg := plain PHE.
Let rand := rand PHE.
Let encT := party_cipher PHE.
Let pkey := pkey PHE.

(* Data type and constructors from interface *)
Let data := di_data DI.
Let d := di_d DI.
Let e := di_e DI.
Let k := di_k DI.
Let Recv_dec {n} := @di_Recv_dec PHE DI n.
Let Recv_enc {n} := @di_Recv_enc PHE DI n.

(* HE operations from the scheme - using @ to provide scheme explicitly *)
Let E := @enc PHE.
Let K := @key PHE.
Let D := @dec PHE.
Let Emul := @Emul PHE.
Let Epow := @Epow PHE.

Notation "u *h w" := (Emul u w) (at level 40).
Notation "u ^h w" := (Epow u w) (at level 40).

(* Party identities - variables of the scheme's party type *)
Variable alice : partyT.
Variable bob : partyT.
Variable charlie : partyT.

(* Party to nat mapping for Send/Recv indices *)
Variable pn : partyT -> nat.

(* Decryption correctness: D inverts E for matching party and Dec key *)
Hypothesis D_correct : forall p m r k,
  D (K p Dec k) (E p m r) = Some m.

(* Note: Program definitions now include randomness parameters.
   Since both files are parameterized by the same PHE/alice/bob/charlie/pn,
   we can compare them at this level. *)

(******************************************************************************)
(** * Cross-file equivalence: dsdp_program = dsdp_program_alt_syntax          *)
(******************************************************************************)

(* Both dsdp_program.v and dsdp_program_alt_syntax.v define the same programs
   (with same signatures and semantics) when instantiated with the same 
   AHEAlgebra_scheme and party variables. The equivalence can be verified 
   by checking definitions match after section instantiation. *)

(******************************************************************************)
(** * Algebraic Correctness Proof                                              *)
(******************************************************************************)

(* The homomorphic properties from AHEAlgebra_scheme - using mixin directly *)
Let Emul_eq_add := @Emul_addM PHE.
Let Epow_eq_mul := @Epow_mulM PHE.
Let enc_curry_eq := @enc_as_curry PHE.

(* Message and randomness variables *)
Variables (k_a k_b k_c v1 v2 v3 u1 u2 u3 r2 r3 : msg).
Variables (rb1 rb2 rc1 rc2 ra1 ra2 : rand).

(* Decryption keys constructed using the scheme's K operation *)
Let dk_a : pkey := K alice Dec k_a.
Let dk_b : pkey := K bob Dec k_b.
Let dk_c : pkey := K charlie Dec k_c.

(* Key intermediate values in the protocol *)
Definition bob_encrypted_input : encT := E bob v2 rb1.
Definition charlie_encrypted_input : encT := E charlie v3 rc1.

(* Alice's computation on Bob's ciphertext *)
Definition alice_a2 : encT := 
  (bob_encrypted_input ^h u2) *h (E bob r2 ra1).

(* Alice's computation on Charlie's ciphertext *)  
Definition alice_a3 : encT :=
  (charlie_encrypted_input ^h u3) *h (E charlie r3 ra2).

(* Lemma: alice_a2 encrypts v2*u2 + r2 *)
Lemma alice_a2_value : exists rr,
  alice_a2 = E bob (v2 * u2 + r2) rr.
Proof.
  rewrite /alice_a2 /bob_encrypted_input /Epow /E /Emul.
  rewrite !enc_curry_eq.
  rewrite -Epow_eq_mul -Emul_eq_add.
  by eexists.
Qed.

(* Lemma: alice_a3 encrypts v3*u3 + r3 *)
Lemma alice_a3_value : exists rr,
  alice_a3 = E charlie (v3 * u3 + r3) rr.
Proof.
  rewrite /alice_a3 /charlie_encrypted_input /Epow /E /Emul.
  rewrite !enc_curry_eq.
  rewrite -Epow_eq_mul -Emul_eq_add.
  by eexists.
Qed.

(* Value Bob decrypts from a2 *)
Definition d2_value : msg := v2 * u2 + r2.

(* Bob's computation: a3 combined with encrypted d2 *)
Definition bob_combined (a3_enc : encT) : encT :=
  a3_enc *h (E charlie d2_value rb2).

(* Lemma: Bob's combined ciphertext encrypts the sum *)
Lemma bob_combined_value : exists rr,
  bob_combined alice_a3 = E charlie (v3 * u3 + r3 + d2_value) rr.
Proof.
  rewrite /bob_combined /Emul /E.
  have [rr3 Ha3] := alice_a3_value.
  rewrite /E in Ha3.
  rewrite Ha3 !enc_curry_eq -Emul_eq_add.
  by eexists.
Qed.

(* Value Charlie decrypts *)
Definition g_value : msg := v3 * u3 + r3 + d2_value.

(* Final computation by Alice *)
Definition alice_result : msg := g_value - r2 - r3 + u1 * v1.

(* Main correctness theorem: Alice computes the dot product *)
Theorem dsdp_computes_dot_product :
  alice_result = u1 * v1 + u2 * v2 + u3 * v3.
Proof.
  rewrite /alice_result /g_value /d2_value.
  ring.
Qed.

End dsdp_correctness.

(* ========================================================================== *)
(* Computational Correctness Proofs using Concrete Party_Enc_Types            *)
(*                                                                            *)
(* This section uses the idealized encryption model where enc = (party * msg) *)
(* and E is deterministic. This enables computational proofs via reflexivity. *)
(*                                                                            *)
(* NOTE: This section is currently disabled due to incompatibility between    *)
(* the simple proc type and session-typed aproc/interp constructs.            *)
(* It requires refactoring to use either:                                     *)
(*   1. Session-typed sproc instead of proc, or                               *)
(*   2. A non-session-typed interpreter                                       *)
(* ========================================================================== *)

(*
Section dsdp_computational.

Variable F : finFieldType.
Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Hypothesis prime_m : prime m.

Local Notation msg := 'F_m.  (* Finite field with m elements *)
Let card_msg : #|msg| = m.
Proof. by rewrite card_Fp // pdiv_id. Qed.

(* Use concrete Party_Enc_Types model *)
Let encT := party_enc party_id msg.
Let pkeyT := party_pkey party_id msg.

(* Wrap concrete D to match expected signature *)
Let D' : pkeyT -> encT -> option msg := @party_D party_id msg.

(* Use party_E for idealized encryption constructor *)
Let E := @party_E party_id msg.

Notation "u *h w" := (party_Emul u w).
Notation "u ^h w" := (party_Epow u w).

Let alice : party_id := Alice.
Let bob : party_id := Bob.
Let charlie : party_id := Charlie.

(* Party to nat mapping for Send/Recv indices *)
Let n (p : party_id) : nat :=
  match p with Alice => 0 | Bob => 1 | Charlie => 2 | NoParty => 3 end.

Let data := (msg + encT + pkeyT)%type.
Let d x : data := inl (inl x).
Let e x : data := inl (inr x).
Let k x : data := inr x.

(* Extract enc from data *)
Let from_enc (x : data) : option encT :=
  if x is inl (inr v) then Some v else None.

(* Use parameterized Recv operations from dsdp_program *)
Let Recv_dec frm := @Recv_dec_param msg encT pkeyT D' data from_enc frm.
Let Recv_enc frm := @Recv_enc_param encT data from_enc frm.

(* Programs using concrete E (deterministic, no randomness needed) *)
Let pbob (dk : pkeyT)(v2 : msg) : proc data :=
  Init (k dk) (
  Init (d v2) (
  Send (n alice) (e (E bob v2)) (
  Recv_dec (n alice) dk (fun d2 =>
  Recv_enc (n alice) (fun a3 =>
    Send (n charlie) (e (a3 *h (E charlie d2))) (
  Finish)))))).

Let pcharlie (dk : pkeyT)(v3 : msg) : proc data :=
  Init (k dk) (
  Init (d v3) (
  Send (n alice) (e (E charlie v3)) (
  Recv_dec (n bob) dk (fun d3 => (
    Send (n alice) (e (E alice d3))
  Finish))))).

Let palice (dk : pkeyT)(v1 u1 u2 u3 r2 r3: msg) : proc data :=
  Init (k dk) (
  Init (d v1) (
  Init (d u1) (
  Init (d u2) (
  Init (d u3) (
  Init (d r2) (
  Init (d r3) (
  Recv_enc (n bob) (fun c2 =>
  Recv_enc (n charlie) (fun c3 =>
  let a2 := (c2 ^h u2 *h (E bob r2)) in
  let a3 := (c3 ^h u3 *h (E charlie r3)) in
    Send (n bob) (e a2) (
    Send (n bob) (e a3) (
    Recv_dec (n charlie) dk (fun g =>
    Ret (d ((g - r2 - r3 + u1 * v1))))))))))))))).
  
Variables (k_a k_b k_c v1 v2 v3 u1 u2 u3 r2 r3 : msg).

(* Concrete keys *)
Let dk_a : pkeyT := (Alice, Dec, k_a). 
Let dk_b : pkeyT := (Bob, Dec, k_b). 
Let dk_c : pkeyT := (Charlie, Dec, k_c). 

(* Pack processes into aproc list *)
Let dsdp_procs : seq (aproc data) :=
  [procs palice dk_a v1 u1 u2 u3 r2 r3; pbob dk_b v2; pcharlie dk_c v3].

Let dsdp h :=
  interp h dsdp_procs (nseq 3 [::]).

Let dsdp_max_fuel : nat := 27.

(* Verify the computed fuel matches *)
Lemma dsdp_max_fuel_ok : dsdp_max_fuel = [> dsdp_procs].
Proof. reflexivity. Qed.

(* Protocol execution result *)
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

(* Evaluation reaches a final state *)
Lemma dsdp_terminates :
  all_final (dsdp [> dsdp_procs]).1.
Proof. reflexivity. Qed.

Notation dsdp_traceT := (dsdp_max_fuel.-bseq data).
Notation dsdp_tracesT := (3.-tuple dsdp_traceT).

Let dsdp_traces : dsdp_tracesT :=
  interp_traces dsdp_max_fuel dsdp_procs.

Let is_dsdp (trs : dsdp_tracesT) :=
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

(* Trace structure *)
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

(* Protocol correctness: S = u1*v1 + u2*v2 + u3*v3 *)
Lemma dsdp_is_correct:
  is_dsdp dsdp_traces.
Proof. rewrite dsdp_traces_ok /is_dsdp /=.
ring.
Qed.

End dsdp_computational.
*)
