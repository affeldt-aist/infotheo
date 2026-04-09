(******************************************************************************)
(*                                                                            *)
(*   DSDP Stepwise Bridge — Raw proc branch (Phase 1 skeleton)                *)
(*                                                                            *)
(*   This file bridges the declarative phase lists in dsdp_stepwise.v         *)
(*   (dsdp_n_program, dsdp_n_phase0..4, dsdp_n_first_relay,                   *)
(*   dsdp_n_intermediate, dsdp_n_last_relay) to a hand-written set of raw     *)
(*   `proc data` templates via a deterministic, structural translator        *)
(*   `translate_raw`. The translator acts like a manual interpreter that      *)
(*   walks each party's raw proc tree and emits the corresponding             *)
(*   `(party_id * dsdp_action)` actions in the same phase order as            *)
(*   `dsdp_n_program`.                                                        *)
(*                                                                            *)
(*   Scope (locked):                                                          *)
(*   - Raw `proc data` templates only (no sproc, no session types).           *)
(*   - N-generic via Section variables (mirrors dsdp_stepwise.v).             *)
(*   - List-equality bridge only — no sw_global_state, no interp, no fuel.   *)
(*   - Link to dsdp_n_procs via *_erase deferred.                             *)
(*                                                                            *)
(*   Phase 1 status: skeleton — all lemmas (R-L1..R-L8, R-M1..R-M5, R-TH1)    *)
(*   are stated and Admitted. Definitions type-check.                         *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import smc_interpreter smc_session_types homomorphic_encryption.
Require Import dsdp_interface dsdp_session_types dsdp_program dsdp_stepwise.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fset_scope.
Local Open Scope ring_scope.

Section dsdp_stepwise_bridge.

Variable AHE : AHEncType.

(* Local abbreviations matching dsdp_stepwise.v *)
Let DI := Standard_DSDP_Interface AHE.
Let msgT := plain AHE.
Let randT := rand AHE.
Let encT := cipher AHE.
Let priv_keyT := priv_key AHE.
Let pub_keyT := pub_key AHE.

(* Data type carrier and constructors from the standard interface.
   These mirror dsdp_pismc.v's `Let data := di_data DI` etc. We use the
   raw std_* underlying functions so that the slice-helper projections
   can pattern-match on the underlying Recv shape if needed. *)
Let data := std_data AHE.
Let d : msgT -> data := @std_d AHE.
Let e : encT -> data := @std_e AHE.
Let priv_key : priv_keyT -> data := @std_priv_key AHE.

Let Emul := @Emul AHE.
Let Epow := @Epow AHE.

Local Notation "u *h w" := (Emul u w) (at level 40).
Local Notation "u ^h w" := (Epow u w) (at level 40).

(* nat_to_party_id is already a coercion (declared in dsdp_pismc.v / dsdp_stepwise.v). *)

(* Section variables — same shape as dsdp_stepwise.v so the bridge file
   instantiates one-to-one against the existing phase lemmas. *)
Variable n_relay : nat.
Variable dk_alice : priv_keyT.
Variable v_alice  : msgT.
Variable dk : 'I_n_relay.+1 -> priv_keyT.
Variable v  : 'I_n_relay.+1 -> msgT.
Variable u  : 'I_n_relay.+2 -> msgT.
Variable r  : 'I_n_relay.+1 -> msgT.
Variable ra  : 'I_n_relay.+1 -> randT.
Variable rb1 : 'I_n_relay.+1 -> randT.
Variable rb2 : 'I_n_relay.+1 -> randT.
Variable r_tail : randT.

(* Local instances of the values defined in dsdp_stepwise.v.
   We re-bind the closed-form named values to local functions so the
   raw templates and slice helpers can refer to them by short names.
   Each just calls the corresponding stepwise definition with the
   matching section parameters. *)
Local Notation alice := (@alice).
Local Notation R := (@R).

(* We refer to sw_* values directly via the dsdp_stepwise.v exports.
   Since the section variables here are bound to the same names with
   the same types, Rocq's implicit-argument inference will fill them
   in automatically when we write `sw_alpha j`, `sw_pk_of i`, etc.
   This avoids hand-listing each section parameter at the call site. *)

(* Opacity: keep the wrapped Recv combinators opaque so slice functions
   pattern-match on `std_Recv_dec frm dk f` / `std_Recv_enc frm f` as
   if they were super-constructors. *)
Arguments std_Recv_dec : simpl never.
Arguments std_Recv_enc : simpl never.
Arguments Recv_param : simpl never.

(* ========================================================================== *)
(* R-T1..R-T5: Raw proc templates                                             *)
(* ========================================================================== *)

(* Helper: alpha-as-a-function-of-the-received-cipher (placeholder used in
   the alice raw body). We don't try to express the homomorphic computation
   structurally inside palice_raw — we just feed the closed form sw_alpha j
   into the Send. This is enough for the list-equality bridge because the
   slice helper supplies the same closed form on the dsdp_n_phase2 side. *)

Definition alice_dest_of (idx : nat) : nat := maxn 1 idx.

(* R-T1. Alice. Fixpoint over the relay list. *)
Fixpoint palice_raw_body (relays : seq 'I_n_relay.+1) (idx : nat)
    (tail : proc data) : proc data :=
  match relays with
  | [::] => tail
  | j :: rest =>
      std_Recv_enc (val j).+1 (fun _ =>
        Send (alice_dest_of idx) (e (sw_alpha dk_alice dk v u r ra rb1 j))
          (palice_raw_body rest idx.+1 tail))
  end.

Definition palice_raw_tail : proc data :=
  std_Recv_dec n_relay.+1 dk_alice (fun _ =>
    Ret (d (sw_Delta v u r (ord_max : 'I_n_relay.+1)
            - (\sum_(k < n_relay.+1) r k)
            + u ord0 * v_alice))).

Definition palice_raw (relays : seq 'I_n_relay.+1) : proc data :=
  Init (priv_key dk_alice)
  (Init (d v_alice)
    (palice_raw_body relays 0 palice_raw_tail)).

(* R-T2. First relay. *)
Definition first_relay_raw (j : 'I_n_relay.+1)
    (dk_j : priv_keyT) (v_j : msgT) (r1_j r2_j : randT) : proc data :=
  Init (priv_key dk_j)
  (Init (d v_j)
    (Send 0 (e (enc (sw_pk_of dk_alice dk (lift ord0 j)) v_j r1_j))
      (std_Recv_dec 0 dk_j (fun _ =>
        std_Recv_enc 0 (fun _ =>
          Send 2
            (e (sw_beta dk_alice dk v u r ra rb1 rb2 ord0 j))
            Finish))))).

(* R-T3. Intermediate relay. *)
Definition intermediate_relay_raw (j : 'I_n_relay.+1)
    (dk_j : priv_keyT) (v_j : msgT) (r1_j r2_j : randT) : proc data :=
  Init (priv_key dk_j)
  (Init (d v_j)
    (Send 0 (e (enc (sw_pk_of dk_alice dk (lift ord0 j)) v_j r1_j))
      (std_Recv_enc 0 (fun _ =>
        std_Recv_dec (val j) dk_j (fun _ =>
          Send (val j).+2
            (e (sw_beta dk_alice dk v u r ra rb1 rb2 j j))
            Finish))))).

(* R-T4. Last relay. *)
Definition last_relay_raw (j : 'I_n_relay.+1)
    (dk_j : priv_keyT) (v_j : msgT) (r1_j r2_j : randT) : proc data :=
  Init (priv_key dk_j)
  (Init (d v_j)
    (Send 0 (e (enc (sw_pk_of dk_alice dk (lift ord0 j)) v_j r1_j))
      (std_Recv_dec n_relay dk_j (fun _ =>
        Send 0 (e (sw_gamma dk_alice dk v u r r_tail)) Finish)))).

(* R-T5. Case-split + list assembly. *)
Definition relay_raw (j : 'I_n_relay.+1) : proc data :=
  if val j == 0 then
    first_relay_raw j (dk j) (v j) (rb1 j) (rb2 j)
  else if val j == n_relay then
    last_relay_raw j (dk j) (v j) (rb1 j) (rb2 j)
  else
    intermediate_relay_raw j (dk j) (v j) (rb1 j) (rb2 j).

Definition dsdp_raw_procs : seq (proc data) :=
  palice_raw (enum 'I_n_relay.+1)
    :: [seq relay_raw j | j : 'I_n_relay.+1].

(* ========================================================================== *)
(* R-T6: Translator + slice helpers                                           *)
(* ========================================================================== *)

(* Projection helpers: extract the (frm, dk, f) / (frm, f) tuple out of an
   opaque std_Recv_dec / std_Recv_enc node. Implemented by matching on the
   underlying Recv shape. Note: because std_Recv_{dec,enc} are opaque
   Definitions (not constructors), we cannot directly pattern-match — we
   inspect the underlying Recv frm <continuation> shape and rely on the
   one-line correctness lemmas std_Recv_*_proj_eq below. *)

(* For phase 1 we keep these as stub helpers returning [::] on any
   non-matching shape. The structural extraction is sufficient for the
   skeleton: real correctness is established only in Phase 2. *)

Definition init_slice (p : party_id) (pr : proc data)
    : seq (party_id * dsdp_action AHE) :=
  match pr with
  | Init _ (Init _ _) =>
      (* We extract by pattern only the outer two Inits and emit the
         declarative AInit; in this skeleton we don't try to crack the
         payloads back into msgT/priv_keyT — phase2 lemmas will introduce
         the correct extractors. For type-checking only, return [::]. *)
      [::]
  | _ => [::]
  end.

Definition first_send_slice (p : party_id) (pr : proc data)
    : seq (party_id * dsdp_action AHE) := [::].

(* Phase 1 stub: in Phase 2 this becomes a Fixpoint that walks the loop
   body, threading expected ciphers through each Recv continuation. *)
Definition alice_loop_slice (body : proc data) (idx : nat)
    : seq (party_id * dsdp_action AHE) := [::].

Definition first_relay_beta_slice (pr : proc data)
    : seq (party_id * dsdp_action AHE) := [::].

Definition intermediate_beta_slice (j : 'I_n_relay.+1) (pr : proc data)
    : seq (party_id * dsdp_action AHE) := [::].

Definition last_relay_beta_slice (pr : proc data)
    : seq (party_id * dsdp_action AHE) := [::].

Definition alice_tail_slice (tail : proc data)
    : seq (party_id * dsdp_action AHE) := [::].

(* Helpers: walk past Alice's two Inits to expose the loop body, and walk
   past the loop body to expose the tail. Phase 1 stubs. *)
Definition alice_body_of (pr : proc data) : proc data :=
  match pr with
  | Init _ (Init _ body) => body
  | _ => Fail
  end.

Definition alice_tail_of (pr : proc data) : proc data :=
  match pr with
  | Init _ (Init _ _) => palice_raw_tail
  | _ => Fail
  end.

(* Phase sub-definitions, named so R-M1..R-M5 reference them directly
   without a phaseK_of projection (audit point 6). *)

Definition translate_raw_phase0 (ps : seq (proc data))
    : seq (party_id * dsdp_action AHE) :=
  let alice_pr := nth Fail ps 0 in
  let relay_prs := behead ps in
  init_slice alice alice_pr
    ++ flatten [seq init_slice (R (val j)) (nth Fail relay_prs (val j))
               | j : 'I_n_relay.+1].

Definition translate_raw_phase1 (ps : seq (proc data))
    : seq (party_id * dsdp_action AHE) :=
  let relay_prs := behead ps in
  flatten [seq first_send_slice (R (val j)) (nth Fail relay_prs (val j))
          | j : 'I_n_relay.+1].

Definition translate_raw_phase2 (ps : seq (proc data))
    : seq (party_id * dsdp_action AHE) :=
  let alice_pr := nth Fail ps 0 in
  alice_loop_slice (alice_body_of alice_pr) 0.

Definition translate_raw_phase3 (ps : seq (proc data))
    : seq (party_id * dsdp_action AHE) :=
  let relay_prs := behead ps in
  first_relay_beta_slice (nth Fail relay_prs 0)
    ++ flatten [seq intermediate_beta_slice j
                    (nth Fail relay_prs (val j))
               | j <- enum 'I_n_relay.+1 & (0 < val j < n_relay)%N]
    ++ last_relay_beta_slice (nth Fail relay_prs n_relay).

Definition translate_raw_phase4 (ps : seq (proc data))
    : seq (party_id * dsdp_action AHE) :=
  let alice_pr := nth Fail ps 0 in
  alice_tail_slice (alice_tail_of alice_pr).

Definition translate_raw (ps : seq (proc data))
    : seq (party_id * dsdp_action AHE) :=
  translate_raw_phase0 ps
    ++ translate_raw_phase1 ps
    ++ translate_raw_phase2 ps
    ++ translate_raw_phase3 ps
    ++ translate_raw_phase4 ps.

(* ========================================================================== *)
(* R-L1..R-L8: Slice helper lemmas (stubs)                                    *)
(* ========================================================================== *)

(* R-L1. Phase0 alice slice. *)
Lemma init_slice_alice_eq :
  init_slice alice (palice_raw (enum 'I_n_relay.+1))
  = [:: (alice, AInit v_alice dk_alice)].
Proof. Admitted.

(* R-L2. Phase0 relay slice — uniform across first/intermediate/last. *)
Lemma init_slice_relay_eq (j : 'I_n_relay.+1) :
  init_slice (R (val j)) (relay_raw j)
  = [:: (R (val j), AInit (v j) (dk j))].
Proof. Admitted.

(* R-L3. Phase1 relay slice — uniform across the three relay shapes. *)
Lemma first_send_slice_relay_eq (j : 'I_n_relay.+1) :
  first_send_slice (R (val j)) (relay_raw j)
  = [:: (R (val j), AEnc (sw_pk_of dk_alice dk (lift ord0 j)) (v j) (rb1 j))
      ; (R (val j), ASend alice (sw_c dk_alice dk v rb1 j))].
Proof. Admitted.

(* R-L4. Phase2 alice loop slice — N-generic via Fixpoint induction. *)
(* The plan's Section dsdp_n_phase2 in dsdp_stepwise.v uses a `flatten map`
   over `enum 'I_n_relay.+1`. This lemma states the loop slice on the full
   palice_raw_body matches dsdp_n_phase2. The proof in Phase 3 will be by
   induction on the relay list with the F1 strengthened invariant. *)
Lemma alice_loop_slice_eq :
  alice_loop_slice
    (palice_raw_body (enum 'I_n_relay.+1) 0 palice_raw_tail) 0
  = dsdp_n_phase2 dk_alice dk v u r ra rb1.
Proof. Admitted.

(* R-L5. Phase3 first-relay slice. *)
Lemma first_relay_beta_slice_eq (j : 'I_n_relay.+1) (Hj : val j = 0) :
  first_relay_beta_slice (relay_raw j)
  = dsdp_n_first_relay dk_alice dk v u r ra rb1 rb2.
Proof. Admitted.

(* R-L6. Phase3 intermediate-relay slice. *)
Lemma intermediate_beta_slice_eq (j : 'I_n_relay.+1) :
  (0 < val j < n_relay)%N ->
  intermediate_beta_slice j (relay_raw j)
  = dsdp_n_intermediate dk_alice dk v u r ra rb1 rb2 j.
Proof. Admitted.

(* R-L7. Phase3 last-relay slice. *)
Lemma last_relay_beta_slice_eq (j : 'I_n_relay.+1) (Hj : val j = n_relay) :
  last_relay_beta_slice (relay_raw j)
  = dsdp_n_last_relay dk_alice dk v u r ra rb1 rb2 r_tail.
Proof. Admitted.

(* R-L8. Phase4 alice tail slice. *)
Lemma alice_tail_slice_eq :
  alice_tail_slice palice_raw_tail
  = dsdp_n_phase4 dk_alice v_alice dk v u r r_tail.
Proof. Admitted.

(* ========================================================================== *)
(* R-M1..R-M5: Per-phase main lemmas (stubs)                                  *)
(* ========================================================================== *)

Lemma translate_raw_phase0_eq :
  translate_raw_phase0 dsdp_raw_procs
  = dsdp_n_phase0 dk_alice v_alice dk v.
Proof. Admitted.

Lemma translate_raw_phase1_eq :
  translate_raw_phase1 dsdp_raw_procs
  = dsdp_n_phase1 dk_alice dk v rb1.
Proof. Admitted.

Lemma translate_raw_phase2_eq :
  translate_raw_phase2 dsdp_raw_procs
  = dsdp_n_phase2 dk_alice dk v u r ra rb1.
Proof. Admitted.

Lemma translate_raw_phase3_eq :
  translate_raw_phase3 dsdp_raw_procs
  = dsdp_n_phase3 dk_alice dk v u r ra rb1 rb2 r_tail.
Proof. Admitted.

Lemma translate_raw_phase4_eq :
  translate_raw_phase4 dsdp_raw_procs
  = dsdp_n_phase4 dk_alice v_alice dk v u r r_tail.
Proof. Admitted.

(* ========================================================================== *)
(* R-TH1: Headline list equality                                              *)
(* ========================================================================== *)

Lemma dsdp_raw_translate_eq :
  translate_raw dsdp_raw_procs
  = dsdp_n_program dk_alice v_alice dk v u r ra rb1 rb2 r_tail.
Proof. Admitted.

End dsdp_stepwise_bridge.
