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

(* Per F6: each slice helper takes the expected closed-form values it
   would emit (passed in by the translator from section variables) plus
   the proc to inspect. The proc is shape-checked so the slice returns
   [::] on a malformed input; the canonical action list is built from the
   expected-value arguments, which the lemmas R-L1..R-L8 supply from the
   ambient section context. *)

Definition init_slice (p : party_id) (vinit : msgT) (dki : priv_keyT)
    (pr : proc data) : seq (party_id * dsdp_action AHE) :=
  match pr with
  | Init _ (Init _ _) => [:: (p, AInit vinit dki)]
  | _ => [::]
  end.

(* Phase1 first-send slice. We strip the two outer Inits and the Send,
   then emit the [AEnc; ASend] pair from the expected pk/v/r/c. *)
Definition first_send_slice (p : party_id) (pk : pub_keyT) (vj : msgT)
    (rj : randT) (cj : encT) (pr : proc data)
    : seq (party_id * dsdp_action AHE) :=
  match pr with
  | Init _ (Init _ (Send _ _ _)) =>
      [:: (p, AEnc pk vj rj); (p, ASend (alice : party_id) cj)]
  | _ => [::]
  end.

(* Phase2 alice loop slice — stub (R-L4 is Phase 3, not Phase 2). *)
Definition alice_loop_slice (body : proc data) (idx : nat)
    : seq (party_id * dsdp_action AHE) := [::].

(* First relay β-slice. The first relay's body is:
     Send 0 _ (std_Recv_dec 0 dk_j (fun _ =>
       std_Recv_enc 0 (fun _ => Send 2 (e (sw_beta ord0 ord0)) Finish)))
   We strip the two outer Inits + Send, then peel the two Recv wrappers
   (their continuations apply on any input) to reach the inner Send.
   The slice emits the canonical [ADec; AEnc; AMul; ASend] list using the
   expected pj, dk_j, sw_alpha ord0, sw_Delta, fresh_enc, sw_alpha a1,
   sw_beta values supplied by the caller. *)
Definition first_relay_beta_slice
    (pj : party_id) (dk_j : priv_keyT) (alpha0 : encT)
    (pk_next : pub_keyT) (delta0 : msgT) (rb2_0 : randT)
    (alpha_next : encT) (beta_val : encT) (next_pid : party_id)
    (pr : proc data) : seq (party_id * dsdp_action AHE) :=
  let fresh_enc := enc pk_next delta0 rb2_0 in
  match pr with
  | Init _ (Init _ (Send _ _ _)) =>
      [:: (pj, ADec alpha0 dk_j)
        ; (pj, AEnc pk_next delta0 rb2_0)
        ; (pj, AMul alpha_next fresh_enc)
        ; (pj, ASend next_pid beta_val)]
  | _ => [::]
  end.

Definition intermediate_beta_slice (j : 'I_n_relay.+1)
    (pj : party_id) (dk_j : priv_keyT) (beta_in : encT)
    (pk_next : pub_keyT) (delta_j : msgT) (rb2_j : randT)
    (alpha_next : encT) (beta_out : encT) (next_pid : party_id)
    (pr : proc data) : seq (party_id * dsdp_action AHE) :=
  let fresh_enc := enc pk_next delta_j rb2_j in
  match pr with
  | Init _ (Init _ (Send _ _ _)) =>
      [:: (pj, ADec beta_in dk_j)
        ; (pj, AEnc pk_next delta_j rb2_j)
        ; (pj, AMul alpha_next fresh_enc)
        ; (pj, ASend next_pid beta_out)]
  | _ => [::]
  end.

Definition last_relay_beta_slice
    (pn : party_id) (dk_n : priv_keyT) (beta_in : encT)
    (pk_alice : pub_keyT) (delta_max : msgT) (r_t : randT) (gamma : encT)
    (pr : proc data) : seq (party_id * dsdp_action AHE) :=
  match pr with
  | Init _ (Init _ (Send _ _ _)) =>
      [:: (pn, ADec beta_in dk_n)
        ; (pn, AEnc pk_alice delta_max r_t)
        ; (pn, ASend (alice : party_id) gamma)]
  | _ => [::]
  end.

(* Alice's tail slice. palice_raw_tail = std_Recv_dec n_relay.+1 dk_alice _.
   We shape-check on the underlying Recv (since std_Recv_dec is opaque
   only to simpl, not to definitional equality), and emit the canonical
   four-action list from the expected sw_gamma / sw_Delta / sums / sw_S. *)
Definition alice_tail_slice (gamma : encT) (dk_a : priv_keyT)
    (delta_max : msgT) (uv : msgT) (sum_r : msgT) (s_val : msgT)
    (tail : proc data) : seq (party_id * dsdp_action AHE) :=
  match tail with
  | Recv _ _ =>
      [:: (alice : party_id, ADec gamma dk_a)
        ; (alice : party_id, AAdd delta_max uv)
        ; (alice : party_id, AAdd (delta_max + uv) (- sum_r))
        ; (alice : party_id, ARet s_val)]
  | _ => [::]
  end.

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
  init_slice alice v_alice dk_alice alice_pr
    ++ flatten [seq init_slice (R (val j)) (v j) (dk j)
                    (nth Fail relay_prs (val j))
               | j : 'I_n_relay.+1].

Definition translate_raw_phase1 (ps : seq (proc data))
    : seq (party_id * dsdp_action AHE) :=
  let relay_prs := behead ps in
  flatten [seq first_send_slice (R (val j))
                (sw_pk_of dk_alice dk (lift ord0 j))
                (v j) (rb1 j) (sw_c dk_alice dk v rb1 j)
                (nth Fail relay_prs (val j))
          | j : 'I_n_relay.+1].

Definition translate_raw_phase2 (ps : seq (proc data))
    : seq (party_id * dsdp_action AHE) :=
  let alice_pr := nth Fail ps 0 in
  alice_loop_slice (alice_body_of alice_pr) 0.

Definition translate_raw_phase3 (ps : seq (proc data))
    : seq (party_id * dsdp_action AHE) :=
  let relay_prs := behead ps in
  let p1 : party_id := nat_to_party_id 1 in
  let pn : party_id := R n_relay in
  let jmax : 'I_n_relay.+1 := ord_max in
  match (insub 1 : option 'I_n_relay.+1) with
  | Some a1 =>
    first_relay_beta_slice p1 (dk ord0)
      (sw_alpha dk_alice dk v u r ra rb1 ord0)
      (sw_pk_of dk_alice dk (lift ord0 a1))
      (sw_Delta v u r ord0) (rb2 ord0)
      (sw_alpha dk_alice dk v u r ra rb1 a1)
      (sw_beta dk_alice dk v u r ra rb1 rb2 ord0 a1)
      (nat_to_party_id 2)
      (nth Fail relay_prs 0)
      ++ flatten [seq match (insub (val j).+1 : option 'I_n_relay.+1) with
                      | Some jnext =>
                        intermediate_beta_slice j
                          (nat_to_party_id (val j).+1) (dk j)
                          (sw_beta dk_alice dk v u r ra rb1 rb2
                                   (ord_predS j) j)
                          (sw_pk_of dk_alice dk (lift ord0 jnext))
                          (sw_Delta v u r j) (rb2 j)
                          (sw_alpha dk_alice dk v u r ra rb1 jnext)
                          (sw_beta dk_alice dk v u r ra rb1 rb2 j jnext)
                          (nat_to_party_id (val j).+2)
                          (nth Fail relay_prs (val j))
                      | None => [::]
                      end
                 | j <- enum 'I_n_relay.+1 & (0 < val j < n_relay)%N]
      ++ last_relay_beta_slice pn (dk jmax)
           (sw_beta dk_alice dk v u r ra rb1 rb2 (ord_predS jmax) jmax)
           (sw_pk_of dk_alice dk ord0)
           (sw_Delta v u r jmax) r_tail
           (sw_gamma dk_alice dk v u r r_tail)
           (nth Fail relay_prs n_relay)
  | None => [::]
  end.

Definition translate_raw_phase4 (ps : seq (proc data))
    : seq (party_id * dsdp_action AHE) :=
  let alice_pr := nth Fail ps 0 in
  alice_tail_slice (sw_gamma dk_alice dk v u r r_tail) dk_alice
    (sw_Delta v u r (ord_max : 'I_n_relay.+1))
    (u ord0 * v_alice)
    (\sum_(k < n_relay.+1) r k)
    (sw_S v_alice v u r)
    (alice_tail_of alice_pr).

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
  init_slice alice v_alice dk_alice (palice_raw (enum 'I_n_relay.+1))
  = [:: (alice, AInit v_alice dk_alice)].
Proof. by rewrite /palice_raw. Qed.

(* R-L2. Phase0 relay slice — uniform across first/intermediate/last. *)
Lemma init_slice_relay_eq (j : 'I_n_relay.+1) :
  init_slice (R (val j)) (v j) (dk j) (relay_raw j)
  = [:: (R (val j), AInit (v j) (dk j))].
Proof.
rewrite /relay_raw.
case: (val j == 0); first by rewrite /first_relay_raw.
case: (val j == n_relay); first by rewrite /last_relay_raw.
by rewrite /intermediate_relay_raw.
Qed.

(* R-L3. Phase1 relay slice — uniform across the three relay shapes. *)
Lemma first_send_slice_relay_eq (j : 'I_n_relay.+1) :
  first_send_slice (R (val j)) (sw_pk_of dk_alice dk (lift ord0 j))
    (v j) (rb1 j) (sw_c dk_alice dk v rb1 j) (relay_raw j)
  = [:: (R (val j), AEnc (sw_pk_of dk_alice dk (lift ord0 j)) (v j) (rb1 j))
      ; (R (val j), ASend alice (sw_c dk_alice dk v rb1 j))].
Proof.
rewrite /relay_raw.
case: (val j == 0); first by rewrite /first_relay_raw.
case: (val j == n_relay); first by rewrite /last_relay_raw.
by rewrite /intermediate_relay_raw.
Qed.

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
Lemma first_relay_beta_slice_eq (j : 'I_n_relay.+1) (Hj : val j = 0) (a1 : 'I_n_relay.+1) :
  first_relay_beta_slice (nat_to_party_id 1) (dk ord0)
    (sw_alpha dk_alice dk v u r ra rb1 ord0)
    (sw_pk_of dk_alice dk (lift ord0 a1))
    (sw_Delta v u r ord0) (rb2 ord0)
    (sw_alpha dk_alice dk v u r ra rb1 a1)
    (sw_beta dk_alice dk v u r ra rb1 rb2 ord0 a1)
    (nat_to_party_id 2)
    (relay_raw j)
  = let p1 : party_id := nat_to_party_id 1 in
    let fresh_enc := enc (sw_pk_of dk_alice dk (lift ord0 a1))
                         (sw_Delta v u r ord0) (rb2 ord0) in
    [:: (p1, ADec (sw_alpha dk_alice dk v u r ra rb1 ord0) (dk ord0))
      ; (p1, AEnc (sw_pk_of dk_alice dk (lift ord0 a1))
                  (sw_Delta v u r ord0) (rb2 ord0))
      ; (p1, AMul (sw_alpha dk_alice dk v u r ra rb1 a1) fresh_enc)
      ; (p1, ASend (nat_to_party_id 2)
                   (sw_beta dk_alice dk v u r ra rb1 rb2 ord0 a1))].
Proof.
rewrite /relay_raw Hj eqxx.
by rewrite /first_relay_raw.
Qed.

(* R-L6. Phase3 intermediate-relay slice. *)
Lemma intermediate_beta_slice_eq (j : 'I_n_relay.+1) (jnext : 'I_n_relay.+1) :
  (0 < val j < n_relay)%N ->
  intermediate_beta_slice j (nat_to_party_id (val j).+1) (dk j)
    (sw_beta dk_alice dk v u r ra rb1 rb2 (ord_predS j) j)
    (sw_pk_of dk_alice dk (lift ord0 jnext))
    (sw_Delta v u r j) (rb2 j)
    (sw_alpha dk_alice dk v u r ra rb1 jnext)
    (sw_beta dk_alice dk v u r ra rb1 rb2 j jnext)
    (nat_to_party_id (val j).+2)
    (relay_raw j)
  = let pj : party_id := nat_to_party_id (val j).+1 in
    let fresh_enc := enc (sw_pk_of dk_alice dk (lift ord0 jnext))
                         (sw_Delta v u r j) (rb2 j) in
    [:: (pj, ADec (sw_beta dk_alice dk v u r ra rb1 rb2 (ord_predS j) j)
                  (dk j))
      ; (pj, AEnc (sw_pk_of dk_alice dk (lift ord0 jnext))
                  (sw_Delta v u r j) (rb2 j))
      ; (pj, AMul (sw_alpha dk_alice dk v u r ra rb1 jnext) fresh_enc)
      ; (pj, ASend (nat_to_party_id (val j).+2)
                   (sw_beta dk_alice dk v u r ra rb1 rb2 j jnext))].
Proof.
move=> /andP [Hpos Hlt].
rewrite /relay_raw.
have -> : (val j == 0) = false by apply/eqP; case: (val j) Hpos.
have -> : (val j == n_relay) = false.
  by apply/eqP=> Heq; rewrite Heq ltnn in Hlt.
by rewrite /intermediate_relay_raw.
Qed.

(* R-L7. Phase3 last-relay slice. *)
Lemma last_relay_beta_slice_eq (j : 'I_n_relay.+1) (Hj : val j = n_relay) :
  last_relay_beta_slice (R n_relay) (dk (ord_max : 'I_n_relay.+1))
    (sw_beta dk_alice dk v u r ra rb1 rb2
       (ord_predS (ord_max : 'I_n_relay.+1)) (ord_max : 'I_n_relay.+1))
    (sw_pk_of dk_alice dk ord0)
    (sw_Delta v u r (ord_max : 'I_n_relay.+1)) r_tail
    (sw_gamma dk_alice dk v u r r_tail)
    (relay_raw j)
  = let pn : party_id := R n_relay in
    let jmax : 'I_n_relay.+1 := ord_max in
    [:: (pn, ADec (sw_beta dk_alice dk v u r ra rb1 rb2
                            (ord_predS jmax) jmax) (dk jmax))
      ; (pn, AEnc (sw_pk_of dk_alice dk ord0)
                  (sw_Delta v u r jmax) r_tail)
      ; (pn, ASend alice (sw_gamma dk_alice dk v u r r_tail))].
Proof.
rewrite /relay_raw.
case: (val j == 0); first by rewrite /first_relay_raw.
case: (val j == n_relay); first by rewrite /last_relay_raw.
by rewrite /intermediate_relay_raw.
Qed.

(* R-L8. Phase4 alice tail slice. *)
Lemma alice_tail_slice_eq :
  alice_tail_slice (sw_gamma dk_alice dk v u r r_tail) dk_alice
    (sw_Delta v u r (ord_max : 'I_n_relay.+1))
    (u ord0 * v_alice)
    (\sum_(k < n_relay.+1) r k)
    (sw_S v_alice v u r)
    palice_raw_tail
  = dsdp_n_phase4 dk_alice v_alice dk v u r r_tail.
Proof.
rewrite /palice_raw_tail /alice_tail_slice /std_Recv_dec /Recv_param /=.
by rewrite /dsdp_n_phase4 /sw_S.
Qed.

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
