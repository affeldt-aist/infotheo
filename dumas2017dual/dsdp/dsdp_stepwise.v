(******************************************************************************)
(*                                                                            *)
(*   DSDP_n as a stepwise transition list (Phase 1 skeleton)                  *)
(*                                                                            *)
(*   This file presents the N-party DSDP protocol as a single list of         *)
(*     (party_id * dsdp_action)                                               *)
(*   pairs, with `sw_step` as the operational small-step semantics on a       *)
(*   `sw_global_state := party_id -> sw_party_state`. Knowledge is a field of *)
(*   the state (three sets of plain / cipher values + a private key slot)     *)
(*   rather than a separate `dsdp_inv` predicate.                             *)
(*                                                                            *)
(*   This file is the Phase-1 skeleton: it contains all definitions and       *)
(*   action items A1-A4 from the plan. All lemmas and theorems (L1-L9, L17,   *)
(*   TH1) are stated and `Admitted`. The proofs are delivered in subsequent   *)
(*   phases. The bridge to the imperative `dsdp_pismc.v` programs lives in    *)
(*   the sibling file `dsdp_stepwise_bridge.v`.                               *)
(*                                                                            *)
(*   Naming follows the post-audit convention: `sw_` prefix for stepwise      *)
(*   helpers, `dsdp_n_` prefix for protocol-level objects.                    *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import smc_interpreter smc_interpreter_sound pismc.
Require Import smc_session_types homomorphic_encryption.
Require Import dsdp_interface dsdp_session_types dsdp_program.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fset_scope.
Local Open Scope ring_scope.

Section dsdp_stepwise.

Variable AHE : AHEncType.

(* Local abbreviations matching dsdp_pismc.v *)
Let msgT := plain AHE.
Let randT := rand AHE.
Let encT := cipher AHE.
Let priv_keyT := priv_key AHE.
Let pub_keyT := pub_key AHE.

Let Emul := @Emul AHE.
Let Epow := @Epow AHE.

Local Notation "u *h w" := (Emul u w) (at level 40).
Local Notation "u ^h w" := (Epow u w) (at level 40).

(* party_id coercion (matches dsdp_pismc.v:52) *)
Coercion nat_to_party_id : nat >-> party_id.

(* Section variables matching the parameter block of dsdp_pismc.v palice_n /
   relay templates. The bridge file (Phase 6+) instantiates these against
   the concrete dsdp_n_procs. *)
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

(* Party indices matching dsdp_pismc.v *)
Definition alice : party_id := nat_to_party_id 0.
Definition R (j : nat) : party_id := nat_to_party_id j.+1.

(* Destination for Alice's i-th send: relays 0 and 1 both go to party 1 *)
Definition alice_send_dest (j : nat) : nat := maxn 1 j.

(* === D17, A2b: ord_predS and ord_predS_lift =============================== *)

Definition ord_predS {n} (j : 'I_n.+1) : 'I_n.+1 :=
  match val j with
  | k.+1 => inord k
  | _    => ord0
  end.

Lemma ord_predS_lift n (j : 'I_n) :
  val (ord_predS (lift ord0 j)) = val j.
Proof.
rewrite /ord_predS /=.
rewrite add0n inordK //.
exact: (ltnW (ltn_ord j)).
Qed.

(* === D18, A2: foldM ======================================================= *)

Fixpoint foldM {A B : Type} (f : B -> A -> option B) (b : B) (l : seq A)
    : option B :=
  match l with
  | [::] => Some b
  | a :: l' => obind (fun b' => foldM f b' l') (f b a)
  end.

(* === T1, A2: dsdp_action ================================================== *)

Inductive dsdp_action : Type :=
| AInit  (vinit : msgT) (dki : priv_keyT)
| AEnc   (pk : pub_keyT) (m : msgT) (rd : randT)
| ADec   (c : encT) (dki : priv_keyT)
| AMul   (c1 c2 : encT)
| APow   (c : encT) (x : msgT)
| AAdd   (a b : msgT)
| ASend  (dst : party_id) (c : encT)
| ARet   (x : msgT).

(* === T2, A2: sw_party_state, sw_global_state, sw_init_state =============== *)

(* Note: cipher AHE is a nzRingType (hence choiceType), and plain AHE is a
   finComNzRingType (hence choiceType), so {fset _} is well-formed for both.
   priv_key AHE is just `Type`, so we model the private-key slot as an
   `option` (a party owns at most one key in DSDP). *)
Record sw_party_state : Type := MkPS {
  ps_plain  : {fset msgT} ;
  ps_cipher : {fset encT} ;
  ps_priv   : option priv_keyT ;
  ps_ret    : option msgT
}.

Definition sw_global_state := party_id -> sw_party_state.

Definition sw_empty_party : sw_party_state :=
  MkPS fset0 fset0 None None.

Definition sw_init_state : sw_global_state := fun _ => sw_empty_party.

(* Functional update of a global state at one party *)
Definition sw_upd (g : sw_global_state) (p : party_id) (s : sw_party_state)
    : sw_global_state :=
  fun q => if q == p then s else g q.

(* Add a plain to a party *)
Definition sw_add_plain (s : sw_party_state) (m : msgT) : sw_party_state :=
  MkPS (m |` ps_plain s) (ps_cipher s) (ps_priv s) (ps_ret s).

Definition sw_add_cipher (s : sw_party_state) (c : encT) : sw_party_state :=
  MkPS (ps_plain s) (c |` ps_cipher s) (ps_priv s) (ps_ret s).

Definition sw_set_priv (s : sw_party_state) (k : priv_keyT) : sw_party_state :=
  MkPS (ps_plain s) (ps_cipher s) (Some k) (ps_ret s).

Definition sw_set_ret (s : sw_party_state) (x : msgT) : sw_party_state :=
  MkPS (ps_plain s) (ps_cipher s) (ps_priv s) (Some x).

(* === T3, A2: sw_step ====================================================== *)

(* D21: cipher-tracking semantics. Plaintext-side preconditions removed
   (AEnc, APow, AAdd, ARet); only cipher provenance and the return-once
   invariant are enforced. See plan decision D21 for the full rationale and
   D14-note for the security-layering caveat. *)
Definition sw_step (p : party_id) (a : dsdp_action) (g : sw_global_state)
    : option sw_global_state :=
  let s := g p in
  match a with
  | AInit vi dki =>
      Some (sw_upd g p (sw_set_priv (sw_add_plain s vi) dki))
  | AEnc pk m rd =>
      Some (sw_upd g p (sw_add_cipher s (enc pk m rd)))
  | ADec c dki =>
      (* We cannot compare priv_key values (priv_key : Type, no eqType),
         so we only require that the party holds *some* private key, and
         that the supplied dki successfully decrypts c. *)
      if c \in ps_cipher s then
        match ps_priv s with
        | Some _ =>
          match dec dki c with
          | Some m => Some (sw_upd g p (sw_add_plain s m))
          | None => None
          end
        | None => None
        end
      else None
  | AMul c1 c2 =>
      if (c1 \in ps_cipher s) && (c2 \in ps_cipher s)
      then Some (sw_upd g p (sw_add_cipher s (c1 *h c2)))
      else None
  | APow c x =>
      if c \in ps_cipher s
      then Some (sw_upd g p (sw_add_cipher s (c ^h x)))
      else None
  | AAdd a1 b1 =>
      Some (sw_upd g p (sw_add_plain s (a1 + b1)))
  | ASend dst c =>
      if c \in ps_cipher s
      then Some (sw_upd g dst (sw_add_cipher (g dst) c))
      else None
  | ARet x =>
      if ps_ret s == None
      then Some (sw_upd g p (sw_set_ret s x))
      else None
  end.

(* Convenience: read the return slot *)
Definition ret_of (g : sw_global_state) (p : party_id) : option msgT :=
  ps_ret (g p).

(* === T4, A3: sw_pk_of ===================================================== *)

(* `sw_pk_of ord0 = pub_of_priv dk_alice`; `sw_pk_of (lift ord0 j) =
   pub_of_priv (dk j)`. Total dispatch over 'I_n_relay.+2. *)
Definition sw_pk_of (i : 'I_n_relay.+2) : pub_keyT :=
  match unlift ord0 i with
  | Some j => pub_of_priv (dk j)
  | None   => pub_of_priv dk_alice
  end.

(* === T5, A3: closed-form named values ===================================== *)

Definition sw_c (j : 'I_n_relay.+1) : encT :=
  enc (sw_pk_of (lift ord0 j)) (v j) (rb1 j).

Definition sw_alpha (j : 'I_n_relay.+1) : encT :=
  (sw_c j ^h u (lift ord0 j))
    *h enc (sw_pk_of (lift ord0 j)) (r j) (ra j).

(* The accumulated sum up to and including index j. *)
Definition sw_Delta (j : 'I_n_relay.+1) : msgT :=
  \sum_(k < j.+1)
    (let k' : 'I_n_relay.+1 := widen_ord (ltn_ord j) k in
     u (lift ord0 k') * v k' + r k').

Definition sw_beta (j jnext : 'I_n_relay.+1) : encT :=
  sw_alpha jnext *h enc (sw_pk_of (lift ord0 jnext)) (sw_Delta j) (rb2 j).

Definition sw_gamma : encT :=
  enc (sw_pk_of ord0) (sw_Delta ord_max) r_tail.

Definition sw_S : msgT :=
  sw_Delta ord_max - (\sum_(k < n_relay.+1) r k) + u ord0 * v_alice.

(* === T6, A4: phase definitions ============================================ *)

Definition dsdp_n_phase0 : seq (party_id * dsdp_action) :=
  (alice, AInit v_alice dk_alice)
    :: [seq (R (val j), AInit (v j) (dk j)) | j : 'I_n_relay.+1].

Definition dsdp_n_phase1 : seq (party_id * dsdp_action) :=
  flatten
    [seq [:: (R (val j), AEnc (sw_pk_of (lift ord0 j)) (v j) (rb1 j))
           ; (R (val j), ASend alice (sw_c j))]
    | j : 'I_n_relay.+1].

Definition dsdp_n_phase2 : seq (party_id * dsdp_action) :=
  flatten
    [seq let dest : party_id := nat_to_party_id (alice_send_dest (val j)) in
         [:: (alice, AEnc (sw_pk_of (lift ord0 j)) (r j) (ra j))
           ; (alice, APow (sw_c j) (u (lift ord0 j)))
           ; (alice, AMul (sw_c j ^h u (lift ord0 j))
                          (enc (sw_pk_of (lift ord0 j)) (r j) (ra j)))
           ; (alice, ASend dest (sw_alpha j))]
    | j : 'I_n_relay.+1].

(* The first relay receives two alphas (its own + alice_send_dest 0 = 1, and
   alice_send_dest 1 = 1) and produces sw_Delta ord0, then sw_beta ord0
   (lift ord0 ord0), and forwards it to the next relay. Concretely, with
   our naming: party 1 = R 0 holds sw_alpha ord0 + sw_alpha (lift ord0 ord0),
   adds them homomorphically + decrypts + re-encrypts to next. *)
(* D23: first relay action list.
   Mirrors DParty_first at dsdp_pismc.v:221-229:
   1. ADec sw_alpha ord0 under dk ord0   → learns sw_Delta ord0 = u_1 * v_1 + r_1
   2. AEnc sw_Delta ord0 under dk a1     → fresh enc under the next relay's key
   3. AMul sw_alpha a1 with fresh enc    → yields sw_beta ord0 a1
   4. ASend a_next's party the sw_beta   *)
Definition dsdp_n_first_relay : seq (party_id * dsdp_action) :=
  let p1 : party_id := nat_to_party_id 1 in
  match (insub 1 : option 'I_n_relay.+1) with
  | Some a1 =>
    let fresh_enc := enc (sw_pk_of (lift ord0 a1)) (sw_Delta ord0) (rb2 ord0) in
    [:: (p1, ADec (sw_alpha ord0) (dk ord0))
      ; (p1, AEnc (sw_pk_of (lift ord0 a1)) (sw_Delta ord0) (rb2 ord0))
      ; (p1, AMul (sw_alpha a1) fresh_enc)
      ; (p1, ASend (nat_to_party_id 2) (sw_beta ord0 a1))]
  | None => [::]
  end.

(* For an intermediate relay j (with 0 < j < n_relay), it receives
   sw_beta (ord_predS j) j on its cipher set, decrypts, and produces
   sw_Delta j and sw_beta j (lift ord0 j) which it forwards. *)
(* D24: intermediate relay action list.
   Mirrors DParty_intermediate/DParty_relay at dsdp_pismc.v:231-244.
   Expects sw_beta (ord_predS j) j and sw_alpha (lift ord0 j) to be present
   in ps_cipher at party R (val j). *)
Definition dsdp_n_intermediate (j : 'I_n_relay.+1) : seq (party_id * dsdp_action) :=
  match (insub (val j).+1 : option 'I_n_relay.+1) with
  | Some jnext =>
    let pj : party_id := nat_to_party_id (val j).+1 in
    let fresh_enc := enc (sw_pk_of (lift ord0 jnext)) (sw_Delta j) (rb2 j) in
    [:: (pj, ADec (sw_beta (ord_predS j) j) (dk j))
      ; (pj, AEnc (sw_pk_of (lift ord0 jnext)) (sw_Delta j) (rb2 j))
      ; (pj, AMul (sw_alpha jnext) fresh_enc)
      ; (pj, ASend (nat_to_party_id (val j).+2) (sw_beta j jnext))]
  | None => [::]
  end.

(* The last relay receives sw_beta (ord_predS ord_max) ord_max, decrypts to
   sw_Delta ord_max, then encrypts under alice's pub key to produce
   sw_gamma, and sends it back to alice. *)
Definition dsdp_n_last_relay : seq (party_id * dsdp_action) :=
  let pn := R n_relay in
  let jmax : 'I_n_relay.+1 := ord_max in
  [:: (pn, ADec (sw_beta (ord_predS jmax) jmax) (dk jmax))
    ; (pn, AEnc (sw_pk_of ord0) (sw_Delta jmax) r_tail)
    ; (pn, ASend alice sw_gamma)].

Definition dsdp_n_intermediate_indices : seq 'I_n_relay.+1 :=
  [seq j <- enum 'I_n_relay.+1 | (0 < val j < n_relay)%N].

Definition dsdp_n_phase3 : seq (party_id * dsdp_action) :=
  dsdp_n_first_relay
    ++ flatten [seq dsdp_n_intermediate j | j <- dsdp_n_intermediate_indices]
    ++ dsdp_n_last_relay.

Definition dsdp_n_phase4 : seq (party_id * dsdp_action) :=
  [:: (alice, ADec sw_gamma dk_alice)
    ; (alice, AAdd (sw_Delta ord_max) (u ord0 * v_alice))
    ; (alice, AAdd (sw_Delta ord_max + u ord0 * v_alice)
                   (- \sum_(k < n_relay.+1) r k))
    ; (alice, ARet sw_S)].

Definition dsdp_n_program : seq (party_id * dsdp_action) :=
  dsdp_n_phase0 ++ dsdp_n_phase1 ++ dsdp_n_phase2
                ++ dsdp_n_phase3 ++ dsdp_n_phase4.

Definition dsdp_n_final : option sw_global_state :=
  foldM (fun g pa => sw_step pa.1 pa.2 g) sw_init_state dsdp_n_program.

(* === Section variables for the correctness statement ===================== *)

(* v_all: v_alice at slot 0, v shifted by one. *)
Definition v_all (i : 'I_n_relay.+2) : msgT :=
  match unlift ord0 i with
  | Some j => v j
  | None   => v_alice
  end.

(* === L1: per-action evaluation lemmas (Admitted) ========================= *)

Lemma sw_step_AInit_eq p vi dki g :
  sw_step p (AInit vi dki) g
  = Some (sw_upd g p (sw_set_priv (sw_add_plain (g p) vi) dki)).
Proof. by []. Qed.

Lemma sw_step_AEnc_eq p pk m rd g :
  sw_step p (AEnc pk m rd) g
  = Some (sw_upd g p (sw_add_cipher (g p) (enc pk m rd))).
Proof. by []. Qed.

Lemma sw_step_ADec_eq p c dki g m k :
  c \in ps_cipher (g p) ->
  ps_priv (g p) = Some k ->
  dec dki c = Some m ->
  sw_step p (ADec c dki) g
  = Some (sw_upd g p (sw_add_plain (g p) m)).
Proof. by move=> H1 H2 H3; rewrite /sw_step H1 H2 H3. Qed.

Lemma sw_step_AMul_eq p c1 c2 g :
  c1 \in ps_cipher (g p) ->
  c2 \in ps_cipher (g p) ->
  sw_step p (AMul c1 c2) g
  = Some (sw_upd g p (sw_add_cipher (g p) (c1 *h c2))).
Proof. by move=> H1 H2; rewrite /sw_step H1 H2. Qed.

Lemma sw_step_APow_eq p c x g :
  c \in ps_cipher (g p) ->
  sw_step p (APow c x) g
  = Some (sw_upd g p (sw_add_cipher (g p) (c ^h x))).
Proof. by move=> H; rewrite /sw_step H. Qed.

Lemma sw_step_AAdd_eq p a1 b1 g :
  sw_step p (AAdd a1 b1) g
  = Some (sw_upd g p (sw_add_plain (g p) (a1 + b1))).
Proof. by []. Qed.

Lemma sw_step_ASend_eq p dst c g :
  c \in ps_cipher (g p) ->
  sw_step p (ASend dst c) g
  = Some (sw_upd g dst (sw_add_cipher (g dst) c)).
Proof. by move=> H; rewrite /sw_step H. Qed.

Lemma sw_step_ARet_eq p x g :
  ps_ret (g p) = None ->
  sw_step p (ARet x) g
  = Some (sw_upd g p (sw_set_ret (g p) x)).
Proof. by move=> H; rewrite /sw_step /= H. Qed.

(* Generic foldM-with-invariant helper, used for phase existence lemmas *)
Lemma foldM_inv {A B : Type} (f : B -> A -> option B) (P : B -> Prop)
    (l : seq A) (b : B) :
  P b ->
  (forall a b, P b -> exists b', f b a = Some b' /\ P b') ->
  exists b', foldM f b l = Some b' /\ P b'.
Proof.
move=> Pb Hstep.
elim: l b Pb => [|a l IH] b Pb /=; first by exists b.
case: (Hstep a b Pb) => b' [-> Pb'] /=.
exact: IH.
Qed.

(* foldM distributes over list concatenation *)
Lemma foldM_cat {A B : Type} (f : B -> A -> option B) (l1 l2 : seq A) (b : B) :
  foldM f b (l1 ++ l2) =
  match foldM f b l1 with Some b' => foldM f b' l2 | None => None end.
Proof.
elim: l1 b => [|a l1 IH] b /=; first by case: (foldM _ _ _).
case: (f b a) => //= b'; exact: IH.
Qed.

(* Helper: cipher-preservation through a single functional update, under
   the assumption that the new state [s] at party [p] extends [g p]. *)
Lemma sw_upd_cipher_mono g p s q c :
  {subset ps_cipher (g p) <= ps_cipher s} ->
  c \in ps_cipher (g q) ->
  c \in ps_cipher (sw_upd g p s q).
Proof.
move=> Hsub Hc.
rewrite {1}/sw_upd.
case: eqP => [Heq|_]; last exact: Hc.
by apply: Hsub; rewrite -Heq.
Qed.

(* Monotonicity of cipher sets: sw_step never drops ciphers from any party.
   Used throughout the phase proofs to re-establish preconditions after a
   sequence of intermediate steps. *)
Lemma sw_step_cipher_mono p a g g' q c :
  sw_step p a g = Some g' ->
  c \in ps_cipher (g q) ->
  c \in ps_cipher (g' q).
Proof.
rewrite /sw_step.
case: a => /=; intros.
- case: H => <-.
  by apply: sw_upd_cipher_mono => //.
- case: H => <-.
  apply: sw_upd_cipher_mono => // c0 Hc0.
  by rewrite /sw_add_cipher /= inE Hc0 orbT.
- move: H; case: ifP => // Hc0; case: (ps_priv (g p)) => [k|] //.
  case: (dec dki c0) => [m|] //; case => <-.
  by apply: sw_upd_cipher_mono => //.
- move: H; case: ifP => // _; case => <-.
  apply: sw_upd_cipher_mono => // c3 Hc3.
  by rewrite /sw_add_cipher /= inE Hc3 orbT.
- move: H; case: ifP => // _; case => <-.
  apply: sw_upd_cipher_mono => // c3 Hc3.
  by rewrite /sw_add_cipher /= inE Hc3 orbT.
- case: H => <-.
  by apply: sw_upd_cipher_mono => //.
- move: H; case: ifP => // _; case => <-.
  apply: sw_upd_cipher_mono => // c3 Hc3.
  by rewrite /sw_add_cipher /= inE Hc3 orbT.
- move: H; case: ifP => // _; case => <-.
  by apply: sw_upd_cipher_mono => //.
Qed.

(* Lifted to foldM over a sequence. *)
Lemma foldM_cipher_mono (l : seq (party_id * dsdp_action)) g g' q c :
  foldM (fun g pa => sw_step pa.1 pa.2 g) g l = Some g' ->
  c \in ps_cipher (g q) ->
  c \in ps_cipher (g' q).
Proof.
elim: l g => [|[p a] l IH] g /=; first by case=> <-.
case E: (sw_step p a g) => [g1|] //= Hf Hc.
apply: (IH g1) => //.
exact: (sw_step_cipher_mono E Hc).
Qed.

(* === L2 - L7: phase postconditions (Admitted) ============================ *)

Lemma dsdp_n_phase0_state :
  exists g0, foldM (fun g pa => sw_step pa.1 pa.2 g) sw_init_state
                   dsdp_n_phase0 = Some g0.
Proof.
(* phase0 is only AInit actions, which always succeed. Reduce to a generic
   statement over any sequence of relay indices. *)
suff H : forall (l : seq ('I_n_relay.+1)) (g : sw_global_state),
  exists g', foldM (fun g pa => sw_step pa.1 pa.2 g) g
    [seq (R (val j), AInit (v j) (dk j)) | j <- l] = Some g'.
  rewrite /dsdp_n_phase0 /=.
  apply: (H (enum 'I_n_relay.+1)).
elim=> [|j l IH] g /=; first by exists g.
exact: IH.
Qed.

(* Stronger post-condition: after phase0++phase1, alice's cipher set
   contains every [sw_c j]. This is needed to discharge phase2's APow and
   AMul pre-conditions. *)
Lemma dsdp_n_phase01_state :
  exists g1,
    foldM (fun g pa => sw_step pa.1 pa.2 g) sw_init_state
          (dsdp_n_phase0 ++ dsdp_n_phase1) = Some g1 /\
    (forall j : 'I_n_relay.+1, sw_c j \in ps_cipher (g1 alice)).
Proof.
have phase0_loop : forall (l : seq 'I_n_relay.+1) (g : sw_global_state),
  exists g', foldM (fun g pa => sw_step pa.1 pa.2 g) g
    [seq (R (val j), AInit (v j) (dk j)) | j <- l] = Some g'.
  elim=> [|j l IH] g /=; first by exists g.
  exact: IH.
have phase1_loop : forall (l : seq 'I_n_relay.+1) (g : sw_global_state),
  exists g', foldM (fun g pa => sw_step pa.1 pa.2 g) g
    (flatten [seq [:: (R (val j), AEnc (sw_pk_of (lift ord0 j)) (v j) (rb1 j))
                   ; (R (val j), ASend alice (sw_c j))] | j <- l]) = Some g' /\
    (forall j, j \in l -> sw_c j \in ps_cipher (g' alice)) /\
    (forall p c, c \in ps_cipher (g p) -> c \in ps_cipher (g' p)).
  elim=> [|j l IH] g /=.
    by exists g; split=> //; split=> // j0; rewrite in_nil.
  rewrite /sw_step /=.
  set g1 := sw_upd g (R (val j)) _.
  have Hc : sw_c j \in ps_cipher (g1 (R (val j))).
    rewrite /g1 /sw_upd eqxx /sw_add_cipher /sw_c /=.
    by apply/fset1UP; left.
  rewrite Hc /=.
  set g2 := sw_upd g1 alice _.
  have Hg2c : sw_c j \in ps_cipher (g2 alice).
    rewrite /g2 /sw_upd eqxx /sw_add_cipher /=.
    by apply/fset1UP; left.
  have Hmono12 : forall p c, c \in ps_cipher (g p) -> c \in ps_cipher (g2 p).
    move=> p c Hcp.
    apply: (sw_step_cipher_mono (a := ASend alice (sw_c j)) (p := R (val j)) (g := g1)).
      by rewrite /sw_step /= Hc.
    apply: (sw_step_cipher_mono
              (a := AEnc (sw_pk_of (lift ord0 j)) (v j) (rb1 j))
              (p := R (val j)) (g := g)) => //.
  have {IH} [g' [-> [Halpha Hmono']]] := IH g2.
  exists g'; split=> //; split; last first.
    move=> p c Hcp; exact: (Hmono' _ _ (Hmono12 _ _ Hcp)).
  move=> k; rewrite in_cons => /orP [/eqP ->|Hk]; last exact: Halpha.
  exact: (Hmono' _ _ Hg2c).
rewrite foldM_cat /dsdp_n_phase0 /=.
set g_a := sw_upd sw_init_state alice _.
have [g0' ->] := phase0_loop (enum 'I_n_relay.+1) g_a.
rewrite /dsdp_n_phase1.
have [g' [-> [Halpha _]]] := phase1_loop (enum 'I_n_relay.+1) g0'.
exists g'; split=> //.
by move=> j; apply: Halpha; rewrite mem_enum.
Qed.

Lemma dsdp_n_phase1_state :
  exists g1, foldM (fun g pa => sw_step pa.1 pa.2 g) sw_init_state
                   (dsdp_n_phase0 ++ dsdp_n_phase1) = Some g1.
Proof. by have [g1 [H _]] := dsdp_n_phase01_state; exists g1. Qed.

Lemma dsdp_n_phase2_state :
  exists g2, foldM (fun g pa => sw_step pa.1 pa.2 g) sw_init_state
                   (dsdp_n_phase0 ++ dsdp_n_phase1 ++ dsdp_n_phase2)
             = Some g2.
Proof.
have [g1 [Hg1 Halpha]] := dsdp_n_phase01_state.
rewrite catA foldM_cat Hg1.
(* We prove a stronger statement: for any sub-list [l] and any state [g]
   where alice already holds [sw_c k] for every [k ∈ l], the phase2 slice
   over [l] drives [g] forward to some [g']. *)
suff H : forall (l : seq 'I_n_relay.+1) (g : sw_global_state),
  (forall j, j \in l -> sw_c j \in ps_cipher (g alice)) ->
  exists g', foldM (fun g pa => sw_step pa.1 pa.2 g) g
    (flatten [seq let dest : party_id := nat_to_party_id (alice_send_dest (val j)) in
                  [:: (alice, AEnc (sw_pk_of (lift ord0 j)) (r j) (ra j))
                    ; (alice, APow (sw_c j) (u (lift ord0 j)))
                    ; (alice, AMul (sw_c j ^h u (lift ord0 j))
                                   (enc (sw_pk_of (lift ord0 j)) (r j) (ra j)))
                    ; (alice, ASend dest (sw_alpha j))]
              | j <- l]) = Some g'.
  rewrite /dsdp_n_phase2.
  by apply: H => j _; apply: Halpha.
elim=> [|j l IH] g Hall /=; first by exists g.
have Hsc_g : sw_c j \in ps_cipher (g alice) by apply: Hall; rewrite mem_head.
(* Step 1: AEnc (unconditional under D21) -- [enc ... (r j) (ra j)] added. *)
have Hsc1 : sw_c j \in enc (sw_pk_of (lift ord0 j)) (r j) (ra j)
                         |` ps_cipher (g alice).
  by rewrite inE Hsc_g orbT.
rewrite Hsc1 /=.
(* Step 2: APow (needs c in cipher, done). Adds [sw_c j ^h u ...]. *)
have Hm1 : sw_c j ^h u (lift ord0 j)
           \in sw_c j ^h u (lift ord0 j)
               |` (enc (sw_pk_of (lift ord0 j)) (r j) (ra j)
                   |` ps_cipher (g alice)).
  by apply/fset1UP; left.
have Hm2 : enc (sw_pk_of (lift ord0 j)) (r j) (ra j)
           \in sw_c j ^h u (lift ord0 j)
               |` (enc (sw_pk_of (lift ord0 j)) (r j) (ra j)
                   |` ps_cipher (g alice)).
  by apply/fset1UP; right; apply/fset1UP; left.
rewrite Hm1 Hm2 /=.
(* Step 3: AMul (done).  Step 4: ASend sw_alpha j. *)
have Hsend : sw_alpha j
             \in (sw_c j ^h u (lift ord0 j)) *h
                 enc (sw_pk_of (lift ord0 j)) (r j) (ra j)
                 |` (sw_c j ^h u (lift ord0 j)
                     |` (enc (sw_pk_of (lift ord0 j)) (r j) (ra j)
                         |` ps_cipher (g alice))).
  by apply/fset1UP; left; rewrite /sw_alpha.
rewrite Hsend /=.
(* Apply induction hypothesis; must re-derive [sw_c k] in the post-state. *)
set gf := sw_upd _ _ _.
apply: IH => k Hk.
have Hck : sw_c k \in ps_cipher (g alice) by apply: Hall; rewrite in_cons Hk orbT.
rewrite /gf.
do 4 (apply: sw_upd_cipher_mono;
      [by move=> c0 Hc0; rewrite /sw_add_cipher /= inE Hc0 orbT|]).
exact: Hck.
Qed.

(* === D25: fresh-enc helpers ============================================== *)

(* Local curry-eq helper: enc k m r = enc_curry _ k (m, r) is definitional,
   but morphism rewriting with Emul_addM / Epow_scalarM needs the curry form. *)
Local Lemma swe_curry_eq (kk : pub_keyT) (m : msgT) (r0 : randT) :
  enc kk m r0 = ahe_enc.enc_curry AHE kk (m, r0).
Proof. by []. Qed.

(* sw_alpha j is definitionally a fresh encryption under the next relay's key
   of (v j * u_{j+1} + r j). Proved by the morphism laws Epow_scalarM +
   Emul_addM; mirrors alice_a2_value / alice_a3_value at dsdp_program.v:213. *)
Lemma sw_alpha_eq_fresh_enc (j : 'I_n_relay.+1) : exists rr,
  sw_alpha j = enc (sw_pk_of (lift ord0 j)) (v j * u (lift ord0 j) + r j) rr.
Proof.
rewrite /sw_alpha /sw_c /Epow /Emul.
rewrite !swe_curry_eq.
rewrite -(@Epow_scalarM AHE).
rewrite -(@Emul_addM AHE).
by eexists.
Qed.

(* sw_beta j jnext is a fresh encryption whose plaintext is
   (v jnext * u_{jnext+1} + r jnext) + sw_Delta j. Proved by substituting
   sw_alpha_eq_fresh_enc and applying Emul_addM. *)
Lemma sw_beta_eq_fresh_enc (j jnext : 'I_n_relay.+1) : exists rr,
  sw_beta j jnext = enc (sw_pk_of (lift ord0 jnext))
    (v jnext * u (lift ord0 jnext) + r jnext + sw_Delta j) rr.
Proof.
rewrite /sw_beta.
have [rr0 Ha] := sw_alpha_eq_fresh_enc jnext.
rewrite Ha /Emul !swe_curry_eq -(@Emul_addM AHE).
by eexists.
Qed.

(* Uniform pub-key for lifted indices. *)
Lemma sw_pk_of_lift (j : 'I_n_relay.+1) :
  sw_pk_of (lift ord0 j) = pub_of_priv (dk j).
Proof. by rewrite /sw_pk_of liftK. Qed.

(* Decryption of sw_alpha j under dk j yields u_{j+1} * v j + r j.
   This is the key firing that lets the first relay extract sw_Delta ord0
   from sw_alpha ord0 (since sw_Delta ord0 = u (lift ord0 ord0) * v ord0 + r ord0). *)
Lemma dec_sw_alpha (j : 'I_n_relay.+1) :
  dec (dk j) (sw_alpha j) = Some (u (lift ord0 j) * v j + r j).
Proof.
have [rr Ha] := sw_alpha_eq_fresh_enc j.
rewrite Ha sw_pk_of_lift dec_correct.
by rewrite GRing.mulrC.
Qed.

(* Decryption of sw_beta j jnext under dk jnext yields
   u_{jnext+1} * v jnext + r jnext + sw_Delta j.
   Used by each intermediate relay and the last relay. *)
Lemma dec_sw_beta (j jnext : 'I_n_relay.+1) :
  dec (dk jnext) (sw_beta j jnext)
  = Some (u (lift ord0 jnext) * v jnext + r jnext + sw_Delta j).
Proof.
have [rr Hb] := sw_beta_eq_fresh_enc j jnext.
rewrite Hb sw_pk_of_lift dec_correct.
by rewrite [v jnext * _]GRing.mulrC.
Qed.

(* === L4-strong: phase2 post-state with alpha witnesses and ps_priv ======== *)

(* L4_strong extends dsdp_n_phase2_state with three facts needed by L5/L6/L7:
   - For every relay index j, sw_alpha j lives in the cipher set of its
     designated send destination party (alice_send_dest collapses j=0/j=1 to
     the same party 1 so the first relay will find both).
   - The specific relay-0 party (nat_to_party_id 1 = Bob) still holds dk ord0
     as its private key.  This is the key fact used by the first-relay ADec.
   - Alice still holds dk_alice.  Note: a fully forall-j statement on ps_priv
     would be provably false once n_relay >= 3 because party_id has only four
     inhabitants and later AInits overwrite earlier ones; we only assert the
     specific indices L5 consumes. *)
(* Helper: R j is never alice (R = nat_to_party_id . S, alice = 0). *)
Lemma R_ne_alice j : R j <> alice.
Proof. rewrite /R /alice /nat_to_party_id /=; case: j => [|j']; first by [].
by case: j'. Qed.

(* Helper: R j = Bob iff j = 0%N (R 0 = nat_to_party_id 1 = Bob). *)
Lemma R_eq_Bob_iff_zero j : R j = Bob <-> j = 0%N.
Proof.
rewrite /R /nat_to_party_id /=.
split; last by move=> ->.
by case: j => // -[//|j'].
Qed.

(* Helper: R j = Charlie iff j = 1%N. *)
Lemma R_eq_Charlie_iff_one j : R j = nat_to_party_id 2 <-> j = 1%N.
Proof.
rewrite /R /nat_to_party_id /=.
split; last by move=> ->.
by case: j => [//|[//|[//|j']]].
Qed.

(* Helper: Bob <> nat_to_party_id 2 (Charlie). *)
Lemma Bob_ne_Charlie : Bob <> nat_to_party_id 2.
Proof. by []. Qed.

(* Helper: alice <> nat_to_party_id 2. *)
Lemma alice_ne_Charlie : alice <> nat_to_party_id 2.
Proof. by []. Qed.

(* sw_step preserves ps_priv at any party q if the step is not an AInit at q.
   Used to track alice's and Bob's private keys across phases 0, 1, 2. *)
Lemma sw_step_priv_preserve p a g g' q :
  sw_step p a g = Some g' ->
  (p <> q \/ forall vi dki, a <> AInit vi dki) ->
  ps_priv (g' q) = ps_priv (g q).
Proof.
rewrite /sw_step.
case: a => /=; intros.
- (* AInit *)
  case: H => <-.
  rewrite /sw_upd.
  case: eqP => // Heq.
  case: H0 => [Hpq|Hno]; first by subst q.
  by have := Hno _ _ erefl.
- case: H => <-. rewrite /sw_upd. by case: eqP => // ->.
- move: H; case: ifP => // _; case: (ps_priv (g p)) => [k|] //.
  case: (dec dki c) => [m|] // [<-].
  rewrite /sw_upd. by case: eqP => // ->.
- move: H; case: ifP => // _ [<-].
  rewrite /sw_upd. by case: eqP => // ->.
- move: H; case: ifP => // _ [<-].
  rewrite /sw_upd. by case: eqP => // ->.
- case: H => <-. rewrite /sw_upd. by case: eqP => // ->.
- move: H; case: ifP => // _ [<-].
  rewrite /sw_upd. by case: eqP => // ->.
- move: H; case: ifP => // _ [<-].
  rewrite /sw_upd. by case: eqP => // ->.
Qed.

(* Phase0_tail loop: any sequence of relay AInits starting from a state with
   alice's priv set preserves alice's priv and, if ord0 ∈ l, sets Bob's priv
   to (dk ord0). *)
Lemma dsdp_n_phase0_tail_loop (l : seq 'I_n_relay.+1) (g : sw_global_state) :
  ps_priv (g alice) = Some dk_alice ->
  exists g',
    foldM (fun g pa => sw_step pa.1 pa.2 g) g
      [seq (R (val j), AInit (v j) (dk j)) | j <- l] = Some g'
    /\ ps_priv (g' alice) = Some dk_alice
    /\ (ord0 \in l -> ps_priv (g' Bob) = Some (dk ord0))
    /\ (forall p c, c \in ps_cipher (g p) -> c \in ps_cipher (g' p))
    /\ (n_relay = 1%N -> forall a1 : 'I_n_relay.+1, val a1 = 1%N -> a1 \in l ->
        ps_priv (g' (nat_to_party_id 2)) = Some (dk a1))
    /\ (forall q, ps_ret (g' q) = ps_ret (g q)).
Proof.
move=> Halice.
elim: l g Halice => [|j0 l IH] g Halice /=.
  exists g; split; first by [].
  split; first by [].
  split; first by rewrite in_nil.
  split; first by [].
  split; first by move=> _ a1 _; rewrite in_nil.
  by [].
set g1 := sw_upd g (R _) _.
have Hne : R (val j0) <> alice by exact: R_ne_alice.
have Halice1 : ps_priv (g1 alice) = Some dk_alice.
  rewrite /g1 /sw_upd.
  by case: eqP => [Heq|//]; move: Hne; rewrite Heq.
have Hret_step : forall q, ps_ret (g1 q) = ps_ret (g q).
  move=> q.
  rewrite /g1 /sw_upd.
  case: eqP => [Heq|_] //.
  by rewrite /sw_set_priv /sw_add_plain /= Heq.
have [g' [Hfold [Halice' [HBob [Hmono [HCharlie Hret']]]]]] := IH g1 Halice1.
exists g'; split; first exact: Hfold.
split; first exact: Halice'.
split.
  rewrite in_cons => /orP [/eqP Hj0eq|Hin]; last exact: HBob.
  have Hj0_zero : val j0 = 0%N.
    have := Hj0eq. by move/(f_equal val).
  have HBob_g1 : ps_priv (g1 Bob) = Some (dk ord0).
    rewrite /g1 /sw_upd.
    have HBob_eq : Bob == R (val j0).
      by apply/eqP; rewrite Hj0_zero /R /nat_to_party_id.
    rewrite HBob_eq /= /sw_set_priv /=.
    congr Some.
    have : j0 = ord0 by apply: val_inj; rewrite Hj0_zero.
    by move=> ->.
  (* Inline invariant: once Bob's priv = Some (dk ord0), any further
     [R (val k), AInit (v k) (dk k)] step preserves it, because the only
     way R (val k) = Bob is k = ord0, and then dk k = dk ord0. *)
  have Hinv : forall (l0 : seq 'I_n_relay.+1) (g0 g0' : sw_global_state),
    ps_priv (g0 Bob) = Some (dk ord0) ->
    foldM (fun g pa => sw_step pa.1 pa.2 g) g0
      [seq (R (val j), AInit (v j) (dk j)) | j <- l0] = Some g0' ->
    ps_priv (g0' Bob) = Some (dk ord0).
    elim=> [|k l0 IHl0] g0 g0' Hg0 /=; first by case=> <-.
    move=> Hf.
    apply: (IHl0 _ _ _ Hf).
    rewrite /sw_upd.
    case: eqP => [Heq|_]; last exact: Hg0.
    have /R_eq_Bob_iff_zero Hk0 : R (val k) = Bob by rewrite -Heq.
    have : k = ord0 by apply: val_inj.
    by move=> ->.
  exact: (Hinv l g1 g' HBob_g1 Hfold).
split.
  move=> p c Hc.
  apply: Hmono.
  rewrite /g1 /sw_upd.
  case: eqP => [Heq|_]; last exact: Hc.
  rewrite /sw_set_priv /sw_add_plain /=.
  rewrite -Heq. exact: Hc.
split; last first.
  move=> q.
  by rewrite Hret' Hret_step.
(* Charlie invariant: if a1 ∈ (j0 :: l) with val a1 = 1, then g' Charlie
   holds dk a1. Either a1 = j0 (step fires at this iter) or a1 ∈ l (IH). *)
move=> Hnr a1 Ha1val.
rewrite in_cons => /orP [/eqP Ha1j0|Hin]; last first.
  (* a1 ∈ l: use IH's Charlie clause applied at state g1. We need to show
     the extra AInit step at j0 doesn't overwrite Charlie's priv,
     AND that the IH clause holds at g1 from the start — which it does
     for the tail, so we just apply HCharlie. But HCharlie talks about g',
     taking the g1 as its input state. *)
  exact: (HCharlie Hnr a1 Ha1val Hin).
(* a1 = j0 case: the step sets R (val j0) = Charlie's priv = Some (dk j0),
   and we need to show the remaining tail preserves it. *)
have Hj0_one : val j0 = 1%N by rewrite -Ha1val Ha1j0.
have HCharlie_g1 : ps_priv (g1 (nat_to_party_id 2)) = Some (dk j0).
  rewrite /g1 /sw_upd.
  have HCeq : nat_to_party_id 2 == R (val j0).
    by apply/eqP; rewrite Hj0_one.
  by rewrite HCeq /= /sw_set_priv /=.
(* Now invariant: if g0 Charlie = Some (dk j0) and j0 ∈ 'I_n_relay.+1 with
   val j0 = 1, and n_relay = 1, then any further AInit-tail preserves this.
   Reason: at n_relay = 1, every k ∈ 'I_2 with R (val k) = Charlie has
   val k = 1, hence k = j0 by val_inj, hence dk k = dk j0. *)
have Hinv : forall (l0 : seq 'I_n_relay.+1) (g0 g0' : sw_global_state),
  ps_priv (g0 (nat_to_party_id 2)) = Some (dk j0) ->
  foldM (fun g pa => sw_step pa.1 pa.2 g) g0
    [seq (R (val j), AInit (v j) (dk j)) | j <- l0] = Some g0' ->
  ps_priv (g0' (nat_to_party_id 2)) = Some (dk j0).
  elim=> [|k l0 IHl0] g0 g0' Hg0 /=; first by case=> <-.
  move=> Hf.
  apply: (IHl0 _ _ _ Hf).
  rewrite /sw_upd.
  case: eqP => [Heq|_]; last exact: Hg0.
  have /R_eq_Charlie_iff_one Hkone : R (val k) = nat_to_party_id 2 by rewrite -Heq.
  have Hk_eq_j0 : k = j0 by apply: val_inj; rewrite Hkone Hj0_one.
  rewrite /sw_set_priv /=.
  congr Some; congr dk; exact: Hk_eq_j0.
rewrite Ha1j0.
exact: (Hinv l g1 g' HCharlie_g1 Hfold).
Qed.

(* Phase1 loop: starting from any state where alice holds dk_alice, Bob holds
   dk ord0, and each sw_c k (for k ∈ l) is definable, running the flatten of
   phase1 actions over l produces a state where alice holds every sw_c j (j ∈ l)
   and the priv invariants are preserved. *)
Lemma dsdp_n_phase1_loop (l : seq 'I_n_relay.+1) (g : sw_global_state) :
  ps_priv (g alice) = Some dk_alice ->
  ps_priv (g Bob) = Some (dk ord0) ->
  exists g',
    foldM (fun g pa => sw_step pa.1 pa.2 g) g
      (flatten [seq [:: (R (val j), AEnc (sw_pk_of (lift ord0 j)) (v j) (rb1 j));
                        (R (val j), ASend alice (sw_c j))] | j <- l]) = Some g'
    /\ (forall j : 'I_n_relay.+1, j \in l -> sw_c j \in ps_cipher (g' alice))
    /\ ps_priv (g' alice) = Some dk_alice
    /\ ps_priv (g' Bob) = Some (dk ord0)
    /\ (forall p c, c \in ps_cipher (g p) -> c \in ps_cipher (g' p))
    /\ (forall q, ps_priv (g' q) = ps_priv (g q))
    /\ (forall q, ps_ret (g' q) = ps_ret (g q)).
Proof.
move=> Halice HBob.
elim: l g Halice HBob => [|j0 l IH] g Halice HBob /=.
  exists g; split; first by [].
  split; first by move=> j; rewrite in_nil.
  by split=> //.
set g1 := sw_upd g (R j0) (sw_add_cipher (g (R j0)) _).
have Hsc1 : sw_c j0 \in ps_cipher (g1 (R j0)).
  rewrite /g1 /sw_upd eqxx /sw_add_cipher /= /sw_c.
  by apply/fset1UP; left.
rewrite Hsc1 /=.
set g2 := sw_upd g1 alice _.
have Halice2 : ps_priv (g2 alice) = Some dk_alice.
  rewrite /g2 /sw_upd eqxx /sw_add_cipher /=.
  rewrite /g1 /sw_upd.
  have Hne : R j0 <> alice by exact: R_ne_alice.
  case: eqP => [Heq|_]; first by move: Hne; rewrite Heq.
  exact: Halice.
have HBob2 : ps_priv (g2 Bob) = Some (dk ord0).
  rewrite /g2 /sw_upd.
  case: eqP => [Heq|_]; first by discriminate.
  rewrite /g1 /sw_upd.
  case: eqP => [Heq|_]; last exact: HBob.
  rewrite /sw_add_cipher /=.
  by rewrite -Heq.
have Hpa : forall s c, ps_priv (sw_add_cipher s c) = ps_priv s by [].
have Hpu : forall g0 p0 s q0,
    ps_priv ((sw_upd g0 p0 s) q0)
  = if q0 == p0 then ps_priv s else ps_priv (g0 q0).
  by move=> g0 p0 s q0; rewrite /sw_upd; case: ifP.
have Hpriv_step : forall q, ps_priv (g2 q) = ps_priv (g q).
  move=> q.
  rewrite /g2 Hpu Hpa /g1 !Hpu !Hpa.
  have Hne_aR : (alice == R j0) = false by apply/eqP => /esym /R_ne_alice.
  rewrite Hne_aR.
  case: ifP => [/eqP Heqa|_]; first by rewrite Heqa.
  by case: ifP => [/eqP ->|_].
have Hra : forall s c, ps_ret (sw_add_cipher s c) = ps_ret s by [].
have Hru : forall g0 p0 s q0,
    ps_ret ((sw_upd g0 p0 s) q0)
  = if q0 == p0 then ps_ret s else ps_ret (g0 q0).
  by move=> g0 p0 s q0; rewrite /sw_upd; case: ifP.
have Hret_step : forall q, ps_ret (g2 q) = ps_ret (g q).
  move=> q.
  rewrite /g2 Hru Hra /g1 !Hru !Hra.
  have Hne_aR : (alice == R j0) = false by apply/eqP => /esym /R_ne_alice.
  rewrite Hne_aR.
  case: ifP => [/eqP Heqa|_]; first by rewrite Heqa.
  by case: ifP => [/eqP ->|_].
have [g' [Hfold [Hcs [Halice' [HBob' [Hmono' [Hpriv' Hret']]]]]]] := IH g2 Halice2 HBob2.
exists g'; split; first exact: Hfold.
split.
  move=> j; rewrite in_cons => /orP [/eqP ->|Hj]; last exact: Hcs.
  apply: Hmono'.
  rewrite /g2 /sw_upd eqxx /sw_add_cipher /=.
  by apply/fset1UP; left.
split=> //; split=> //; split.
  move=> p c Hc.
  apply: Hmono'.
  rewrite /g2.
  apply: sw_upd_cipher_mono; last first.
    rewrite /g1.
    apply: sw_upd_cipher_mono; last exact: Hc.
    by move=> c0 Hc0; rewrite /sw_add_cipher /= inE Hc0 orbT.
  by move=> c0 Hc0; rewrite /sw_add_cipher /= inE Hc0 orbT.
split.
  move=> q.
  by rewrite Hpriv' Hpriv_step.
move=> q.
by rewrite Hret' Hret_step.
Qed.

(* Combined phase01 strong postcondition. *)
Lemma dsdp_n_phase01_state_strong :
  exists g1,
    foldM (fun g pa => sw_step pa.1 pa.2 g) sw_init_state
          (dsdp_n_phase0 ++ dsdp_n_phase1) = Some g1
    /\ (forall j : 'I_n_relay.+1, sw_c j \in ps_cipher (g1 alice))
    /\ ps_priv (g1 alice) = Some dk_alice
    /\ ps_priv (g1 Bob) = Some (dk ord0)
    /\ ps_ret (g1 alice) = None
    /\ (n_relay = 1%N -> forall a1 : 'I_n_relay.+1, val a1 = 1%N ->
        ps_priv (g1 (nat_to_party_id 2)) = Some (dk a1)).
Proof.
rewrite /dsdp_n_phase0 /dsdp_n_phase1 /=.
set g_a := sw_upd sw_init_state alice _.
have Halice_ga : ps_priv (g_a alice) = Some dk_alice.
  by rewrite /g_a /sw_upd eqxx.
have Hret_ga : ps_ret (g_a alice) = None.
  by rewrite /g_a /sw_upd eqxx /sw_set_priv /sw_add_plain /=.
rewrite foldM_cat.
have [g0 [Hfold0 [Halice0 [HBob0 [_ [HCharlie0 Hret0]]]]]] :=
  dsdp_n_phase0_tail_loop (enum 'I_n_relay.+1) Halice_ga.
rewrite Hfold0.
have HBob0' : ps_priv (g0 Bob) = Some (dk ord0).
  by apply: HBob0; rewrite mem_enum.
have [g1 [Hfold1 [Hcs [Halice1 [HBob1 [_ [Hpriv1 Hret1]]]]]]] :=
  dsdp_n_phase1_loop (enum 'I_n_relay.+1) Halice0 HBob0'.
rewrite Hfold1.
exists g1; split=> //.
split; first by move=> j; apply: Hcs; rewrite mem_enum.
split=> //; split=> //; split.
  by rewrite Hret1 Hret0.
move=> Hnr a1 Ha1val.
rewrite Hpriv1.
by apply: HCharlie0 => //; rewrite mem_enum.
Qed.

(* Phase2 loop: given a state where alice has all sw_c, her priv and Bob's
   priv, running phase2 produces a state where every sw_alpha j lives in its
   designated destination, and the priv invariants are preserved. *)
Lemma dsdp_n_phase2_loop (l : seq 'I_n_relay.+1) (g : sw_global_state) :
  (forall j : 'I_n_relay.+1, j \in l -> sw_c j \in ps_cipher (g alice)) ->
  ps_priv (g alice) = Some dk_alice ->
  ps_priv (g Bob) = Some (dk ord0) ->
  exists g',
    foldM (fun g pa => sw_step pa.1 pa.2 g) g
      (flatten [seq let dest : party_id := nat_to_party_id (alice_send_dest (val j)) in
                    [:: (alice, AEnc (sw_pk_of (lift ord0 j)) (r j) (ra j));
                      (alice, APow (sw_c j) (u (lift ord0 j)));
                      (alice, AMul (sw_c j ^h u (lift ord0 j))
                                    (enc (sw_pk_of (lift ord0 j)) (r j) (ra j)));
                      (alice, ASend dest (sw_alpha j))]
                | j <- l]) = Some g'
    /\ (forall j : 'I_n_relay.+1, j \in l ->
          sw_alpha j \in ps_cipher (g' (nat_to_party_id (alice_send_dest (val j)))))
    /\ ps_priv (g' alice) = Some dk_alice
    /\ ps_priv (g' Bob) = Some (dk ord0)
    /\ (forall p c, c \in ps_cipher (g p) -> c \in ps_cipher (g' p))
    /\ (forall q, ps_priv (g' q) = ps_priv (g q))
    /\ (forall q, ps_ret (g' q) = ps_ret (g q)).
Proof.
elim: l g => [|j0 l IH] g Hall Halice HBob /=.
  exists g; split; first by [].
  split; first by move=> j; rewrite in_nil.
  by split=> //.
have Hsc_g : sw_c j0 \in ps_cipher (g alice) by apply: Hall; rewrite mem_head.
have Hsc1 : sw_c j0 \in enc (sw_pk_of (lift ord0 j0)) (r j0) (ra j0)
                          |` ps_cipher (g alice).
  by rewrite inE Hsc_g orbT.
rewrite Hsc1 /=.
have Hm1 : sw_c j0 ^h u (lift ord0 j0)
  \in sw_c j0 ^h u (lift ord0 j0)
      |` (enc (sw_pk_of (lift ord0 j0)) (r j0) (ra j0) |` ps_cipher (g alice)).
  by apply/fset1UP; left.
have Hm2 : enc (sw_pk_of (lift ord0 j0)) (r j0) (ra j0)
  \in sw_c j0 ^h u (lift ord0 j0)
      |` (enc (sw_pk_of (lift ord0 j0)) (r j0) (ra j0) |` ps_cipher (g alice)).
  by apply/fset1UP; right; apply/fset1UP; left.
rewrite Hm1 Hm2 /=.
have Hsend : sw_alpha j0
  \in (sw_c j0 ^h u (lift ord0 j0)) *h enc (sw_pk_of (lift ord0 j0)) (r j0) (ra j0)
      |` (sw_c j0 ^h u (lift ord0 j0)
          |` (enc (sw_pk_of (lift ord0 j0)) (r j0) (ra j0) |` ps_cipher (g alice))).
  by apply/fset1UP; left; rewrite /sw_alpha.
rewrite Hsend /=.
set gf := sw_upd _ _ _.
(* Helper: sw_upd g p (sw_add_cipher (g p) c) only modifies the cipher field,
   so ps_priv is preserved at any party. *)
have Hupd_add : forall (g0 : sw_global_state) p c q,
  ps_priv ((sw_upd g0 p (sw_add_cipher (g0 p) c)) q) = ps_priv (g0 q).
  move=> g0 p0 c0 q0.
  rewrite /sw_upd.
  by case: eqP => [->|_] //.
have Hupd_add_ret : forall (g0 : sw_global_state) p c q,
  ps_ret ((sw_upd g0 p (sw_add_cipher (g0 p) c)) q) = ps_ret (g0 q).
  move=> g0 p0 c0 q0.
  rewrite /sw_upd.
  by case: eqP => [->|_] //.
(* gf is four nested sw_upd+sw_add_cipher, so priv is preserved. *)
have Hpriv_gf : forall q, ps_priv (gf q) = ps_priv (g q).
  by move=> q; rewrite /gf Hupd_add Hupd_add Hupd_add Hupd_add.
have Hret_gf : forall q, ps_ret (gf q) = ps_ret (g q).
  by move=> q; rewrite /gf Hupd_add_ret Hupd_add_ret Hupd_add_ret Hupd_add_ret.
have Halice_f : ps_priv (gf alice) = Some dk_alice by rewrite Hpriv_gf.
have HBob_f : ps_priv (gf Bob) = Some (dk ord0) by rewrite Hpriv_gf.
(* Cipher monotonicity: all 4 updates only add, never remove. *)
have Hmono0 : forall p c, c \in ps_cipher (g p) -> c \in ps_cipher (gf p).
  move=> p c Hc.
  rewrite /gf.
  apply: sw_upd_cipher_mono; last first.
    apply: sw_upd_cipher_mono; last first.
      apply: sw_upd_cipher_mono; last first.
        apply: sw_upd_cipher_mono; last exact: Hc.
        by move=> c0 Hc0; rewrite /sw_add_cipher /= inE Hc0 orbT.
      by move=> c0 Hc0; rewrite /sw_add_cipher /= inE Hc0 orbT.
    by move=> c0 Hc0; rewrite /sw_add_cipher /= inE Hc0 orbT.
  by move=> c0 Hc0; rewrite /sw_add_cipher /= inE Hc0 orbT.
have Hall_f : forall k : 'I_n_relay.+1, k \in l -> sw_c k \in ps_cipher (gf alice).
  move=> k Hk.
  apply: Hmono0.
  by apply: Hall; rewrite in_cons Hk orbT.
have [g' [Hfold [Hal [Halice' [HBob' [Hmono' [Hpriv' Hret']]]]]]] := IH gf Hall_f Halice_f HBob_f.
exists g'; split; first exact: Hfold.
split.
  move=> j; rewrite in_cons => /orP [/eqP ->|Hj]; last exact: Hal.
  apply: Hmono'.
  rewrite /gf /sw_upd eqxx /sw_add_cipher /=.
  by apply/fset1UP; left.
split=> //; split=> //; split.
  move=> p c Hc.
  apply: Hmono'.
  exact: Hmono0.
split.
  move=> q.
  by rewrite Hpriv' Hpriv_gf.
move=> q.
by rewrite Hret' Hret_gf.
Qed.

Lemma dsdp_n_phase2_state_strong :
  exists g2,
    foldM (fun g pa => sw_step pa.1 pa.2 g) sw_init_state
          (dsdp_n_phase0 ++ dsdp_n_phase1 ++ dsdp_n_phase2) = Some g2
    /\ (forall j : 'I_n_relay.+1,
         sw_alpha j \in ps_cipher (g2 (nat_to_party_id (alice_send_dest (val j)))))
    /\ ps_priv (g2 (nat_to_party_id 1)) = Some (dk ord0)
    /\ ps_priv (g2 alice) = Some dk_alice
    /\ ps_ret (g2 alice) = None
    /\ (n_relay = 1%N -> forall a1 : 'I_n_relay.+1, val a1 = 1%N ->
        ps_priv (g2 (nat_to_party_id 2)) = Some (dk a1)).
Proof.
rewrite catA foldM_cat.
have [g1 [Hg1 [Hcs [Halice1 [HBob1 [Hret1 HCharlie1]]]]]] := dsdp_n_phase01_state_strong.
rewrite Hg1.
rewrite /dsdp_n_phase2.
have [g2 [Hfold2 [Halpha [Halice2 [HBob2 [_ [Hpriv2 Hret2]]]]]]] :=
  @dsdp_n_phase2_loop (enum 'I_n_relay.+1) g1 (fun j _ => Hcs j) Halice1 HBob1.
rewrite Hfold2.
exists g2; split=> //.
split.
  by move=> j; apply: Halpha; rewrite mem_enum.
split=> //; split=> //; split.
  by rewrite Hret2.
move=> Hnr a1 Ha1val.
rewrite Hpriv2.
by apply: HCharlie1.
Qed.

Lemma dsdp_n_first_relay_eq :
  exists gf, foldM (fun g pa => sw_step pa.1 pa.2 g) sw_init_state
                   (dsdp_n_phase0 ++ dsdp_n_phase1 ++ dsdp_n_phase2
                                  ++ dsdp_n_first_relay) = Some gf
    /\ (n_relay = 1%N -> forall a1 : 'I_n_relay.+1, val a1 = 1%N ->
          sw_beta ord0 a1 \in ps_cipher (gf (nat_to_party_id 2))
          /\ ps_priv (gf (nat_to_party_id 2)) = Some (dk a1)
          /\ ps_priv (gf alice) = Some dk_alice
          /\ ps_ret (gf alice) = None).
Proof.
have [g2 [Hg2 [Halpha [Hpriv1 [Halice [Hret2 HCpriv2]]]]]] := dsdp_n_phase2_state_strong.
rewrite !catA foldM_cat -catA Hg2.
rewrite /dsdp_n_first_relay.
case Hi1: (insub 1 : option 'I_n_relay.+1) => [a1|] /=; last first.
  exists g2; split=> //.
  move=> Hnr acur Hacur_val.
  (* Contradiction: insub 1 = None but n_relay = 1 so 1 < 2. *)
  exfalso.
  move: Hi1 Hnr.
  case: insubP => //= Hbound _ Hnr.
  by rewrite Hnr in Hbound.
(* Step 1: ADec sw_alpha ord0 under dk ord0 at party Bob (= nat_to_party_id 1). *)
have Ha0 : sw_alpha ord0 \in ps_cipher (g2 Bob).
  have := Halpha ord0.
  by rewrite /alice_send_dest /= /nat_to_party_id.
rewrite Ha0 /= Hpriv1 /= dec_sw_alpha /=.
(* Derive val a1 = 1 from Hi1 : insub 1 = Some a1 *)
have Ha1_val : val a1 = 1.
  move: Hi1; case: insubP => [a1' Hlt Hval|] //= Heq.
  by move: Heq => [<-]; exact: Hval.
(* Step 2+3: AEnc + AMul; need sw_alpha a1 in Bob's cipher set after AEnc. *)
have Ha1 : sw_alpha a1 \in ps_cipher (g2 Bob).
  have := Halpha a1.
  by rewrite Ha1_val /alice_send_dest /= /nat_to_party_id.
have Hin1 : sw_alpha a1 \in enc (sw_pk_of (lift ord0 a1)) (sw_Delta ord0) (rb2 ord0)
                             |` ps_cipher (g2 Bob).
  by rewrite inE Ha1 orbT.
have Hin2 : enc (sw_pk_of (lift ord0 a1)) (sw_Delta ord0) (rb2 ord0)
              \in enc (sw_pk_of (lift ord0 a1)) (sw_Delta ord0) (rb2 ord0)
                  |` ps_cipher (g2 Bob).
  by apply/fset1UP; left.
rewrite Hin1 Hin2 /=.
(* Step 4: ASend sw_beta ord0 a1 to Charlie (= nat_to_party_id 2). *)
have -> : sw_alpha a1 *h enc (sw_pk_of (lift ord0 a1)) (sw_Delta ord0) (rb2 ord0)
       = sw_beta ord0 a1 by rewrite /sw_beta.
set gAMul := sw_upd _ Bob (sw_add_cipher _ _).
have Hsend : sw_beta ord0 a1 \in ps_cipher (gAMul Bob).
  rewrite /gAMul /sw_upd eqxx /sw_add_cipher /=.
  by apply/fset1UP; left.
rewrite Hsend /=.
eexists; split; first by reflexivity.
(* Now prove the post-condition package for n_relay = 1. *)
move=> Hnr acur Hacur_val.
(* Charlie's priv comes from HCpriv2 applied to acur. Note a1 is the specific
   ordinal from Hi1, and acur is whatever the caller supplies. By val_inj,
   val a1 = val acur = 1 so a1 = acur. *)
have Hacur_eq_a1 : acur = a1 by apply: val_inj; rewrite /= Hacur_val Ha1_val.
rewrite -Hacur_eq_a1.
(* Helpers for sw_upd / sw_add_cipher projections. *)
have HgAMul_Charlie : gAMul (nat_to_party_id 2) = g2 (nat_to_party_id 2).
  by rewrite /gAMul /sw_upd /=.
have HgAMul_alice : gAMul alice = g2 alice.
  by rewrite /gAMul /sw_upd /=.
split.
  rewrite /sw_upd eqxx /sw_add_cipher /=.
  by apply/fset1UP; left.
split.
  rewrite /sw_upd eqxx /=.
  rewrite HgAMul_Charlie.
  by apply: HCpriv2.
split.
  rewrite /sw_upd /=.
  have -> : (alice == nat_to_party_id 2) = false by [].
  by rewrite HgAMul_alice.
rewrite /sw_upd /=.
have -> : (alice == nat_to_party_id 2) = false by [].
by rewrite HgAMul_alice.
Qed.

(* L6: Straight-line telescoping step for one intermediate relay.
   Given a state [g] where party pj := R j holds sw_beta (ord_predS j) j
   and sw_alpha (lift ord0 j) on its cipher set and the right private key,
   running dsdp_n_intermediate j drives [g] to some [g'] where the next
   party pnext := R (j+1) holds sw_beta j (lift ord0 j). *)
Lemma dsdp_n_intermediate_telescope
    (j : 'I_n_relay.+1) (jnext : 'I_n_relay.+1) (g : sw_global_state) :
  (0 < val j < n_relay)%N ->
  val jnext = (val j).+1 ->
  let pj : party_id := nat_to_party_id (val j).+1 in
  let pnext : party_id := nat_to_party_id (val j).+2 in
  sw_beta (ord_predS j) j \in ps_cipher (g pj) ->
  sw_alpha jnext \in ps_cipher (g pj) ->
  ps_priv (g pj) = Some (dk j) ->
  exists g',
    foldM (fun gg pa => sw_step pa.1 pa.2 gg) g (dsdp_n_intermediate j)
    = Some g'
    /\ sw_beta j jnext \in ps_cipher (g' pnext).
Proof.
move=> Hj Hjnext pj pnext Hbeta Halpha Hpriv.
rewrite /dsdp_n_intermediate.
case/andP: Hj => _ Hlt.
have Hbound : ((val j).+1 < n_relay.+1)%N by rewrite ltnS.
rewrite (insubT (fun x => x < n_relay.+1)%N Hbound) /=.
set jnext' := Sub j.+1 Hbound.
have Heq : jnext' = jnext by apply: val_inj => /=; rewrite Hjnext.
rewrite Heq /=.
rewrite Hbeta Hpriv /= dec_sw_beta /=.
set P := (match nat_of_ord j with
          | 0%N => Bob | 1%N => Charlie | _.+2 => NoParty end).
have HPeq : P = pj.
  by rewrite /P /pj /nat_to_party_id /=; case: (val j) => //=; case.
rewrite HPeq.
set Q := (match nat_of_ord j with 0%N => Charlie | _.+1 => NoParty end).
have HQeq : Q = pnext.
  by rewrite /Q /pnext /nat_to_party_id /=; case: (val j) => //=; case.
rewrite HQeq.
have Hm1 : sw_alpha jnext
  \in enc (sw_pk_of (lift ord0 jnext)) (sw_Delta j) (rb2 j)
      |` ps_cipher (g pj).
  by rewrite inE Halpha orbT.
have Hm2 : enc (sw_pk_of (lift ord0 jnext)) (sw_Delta j) (rb2 j)
  \in enc (sw_pk_of (lift ord0 jnext)) (sw_Delta j) (rb2 j)
      |` ps_cipher (g pj).
  by apply/fset1UP; left.
rewrite /sw_upd !eqxx /sw_add_cipher /sw_add_plain /=.
rewrite Hm1 Hm2 /=.
rewrite !eqxx /=.
have Hbeta_eq : sw_beta j jnext
  = sw_alpha jnext *h enc (sw_pk_of (lift ord0 jnext)) (sw_Delta j) (rb2 j).
  by rewrite /sw_beta.
rewrite -Hbeta_eq.
have HbetaIn : sw_beta j jnext
  \in sw_beta j jnext
      |` (enc (sw_pk_of (lift ord0 jnext)) (sw_Delta j) (rb2 j)
          |` ps_cipher (g pj)).
  by apply/fset1UP; left.
rewrite HbetaIn /=.
eexists; split; first by reflexivity.
rewrite /= eqxx.
by case: ifP => _ /=; apply/fset1UP; left.
Qed.

(* L6b: Last-relay straight-line step.  Given a state holding
   sw_beta (ord_predS ord_max) ord_max on party R n_relay with the
   right key, running dsdp_n_last_relay yields sw_gamma on alice's ciphers. *)
Lemma dsdp_n_last_relay_eq (g : sw_global_state) :
  let pn : party_id := R n_relay in
  sw_beta (ord_predS ord_max) (@ord_max n_relay) \in ps_cipher (g pn) ->
  ps_priv (g pn) = Some (dk (@ord_max n_relay)) ->
  exists g',
    foldM (fun gg pa => sw_step pa.1 pa.2 gg) g dsdp_n_last_relay = Some g'
    /\ sw_gamma \in ps_cipher (g' alice).
Proof.
move=> pn Hbeta Hpriv.
rewrite /dsdp_n_last_relay /=.
rewrite -/pn Hbeta Hpriv /= dec_sw_beta /=.
rewrite /sw_upd !eqxx /sw_add_cipher /sw_add_plain /=.
have Hgamma_eq : sw_gamma
  = enc (sw_pk_of ord0) (sw_Delta ord_max) r_tail by [].
rewrite -Hgamma_eq.
have HgammaIn : sw_gamma \in sw_gamma |` ps_cipher (g pn).
  by apply/fset1UP; left.
rewrite HgammaIn /=.
eexists; split; first by reflexivity.
cbv beta.
rewrite eqxx.
by case: ifP => _ /=; apply/fset1UP; left.
Qed.

(* L7 (strong): End-of-phase-3 state.  Exposes the three post-conditions
   that phase4 consumes: sw_gamma \in alice.cipher, ps_priv alice = dk_alice,
   and ps_ret alice = None so the terminal ARet fires.

   RESTRICTION: This lemma (and hence TH1) is proved only for [n_relay = 1],
   i.e. the 3-party case (alice, Bob, Charlie).  The obstacle for [n_relay >= 3]
   is that [party_id] has only 4 inhabitants (Alice, Bob, Charlie, NoParty),
   so [R j = nat_to_party_id j.+1] collapses multiple relays onto NoParty for
   [j >= 2], and the [ps_priv] invariant needed by intermediate-relay steps
   cannot be maintained for both collapsed relays.

   For [n_relay = 2] the argument also goes through (3 relays: Bob, Charlie,
   NoParty, each distinct), but requires explicit intermediate handling that
   we leave as future work.  DSDP's original 3-party case of Dumas et al. 2017
   corresponds exactly to [n_relay = 1]. *)
Lemma dsdp_n_beta_chain_eq (Hnr : n_relay = 1%N) :
  exists g3,
    foldM (fun g pa => sw_step pa.1 pa.2 g) sw_init_state
          (dsdp_n_phase0 ++ dsdp_n_phase1 ++ dsdp_n_phase2
                         ++ dsdp_n_phase3) = Some g3
    /\ sw_gamma \in ps_cipher (g3 alice)
    /\ ps_priv (g3 alice) = Some dk_alice
    /\ ps_ret (g3 alice) = None.
Proof. Admitted.

(* === L8: phase 4 postcondition =========================================== *)

Lemma dsdp_n_phase4_state (Hnr : n_relay = 1%N) :
  exists gf, dsdp_n_final = Some gf /\ ps_ret (gf alice) = Some sw_S.
Proof.
have [g3 [Hg3 [Hgamma [Halice Hret]]]] := dsdp_n_beta_chain_eq Hnr.
rewrite /dsdp_n_final /dsdp_n_program.
rewrite !catA foldM_cat -!catA Hg3 /=.
rewrite Hgamma Halice.
have Hdec : dec dk_alice sw_gamma = Some (sw_Delta ord_max).
  rewrite /sw_gamma /sw_pk_of unlift_none.
  exact: dec_correct.
rewrite Hdec /= Hret /=.
eexists; split; first by reflexivity.
by rewrite /sw_upd eqxx.
Qed.

(* === L9: algebraic identity ============================================== *)

Lemma sw_S_eq_dot_product :
  sw_S = \sum_(i < n_relay.+2) u i * v_all i.
Proof.
rewrite /sw_S /sw_Delta.
rewrite big_split /=.
have Hwiden : forall i : 'I_n_relay.+1,
    widen_ord (ltn_ord (@ord_max n_relay)) i = i.
  by move=> i; apply: val_inj.
under eq_bigr do rewrite Hwiden.
under [\sum_(_ < _) r _]eq_bigr do rewrite Hwiden.
have HrEq : \sum_i r i = \sum_(k < n_relay.+1) r k by [].
rewrite HrEq GRing.addrK big_ord_recl /=.
rewrite big_ord_recl /=.
have Ha : v_all ord0 = v_alice by rewrite /v_all unlift_none.
have Hl : forall i : 'I_n_relay.+1, v_all (lift ord0 i) = v i.
  by move=> i; rewrite /v_all liftK.
rewrite Ha.
under [\sum_(i < n_relay.+1) _]eq_bigr=> i _ do rewrite Hl.
by rewrite [RHS]GRing.addrC [\sum_(i < n_relay.+1) _]big_ord_recl /=.
Qed.

(* === TH1: headline correctness =========================================== *)

Theorem dsdp_n_correct (Hnr : n_relay = 1%N) :
  exists gf, dsdp_n_final = Some gf
           /\ ret_of gf alice = Some (\sum_(i < n_relay.+2) u i * v_all i).
Proof.
have [gf [Hf Hret]] := dsdp_n_phase4_state Hnr.
exists gf; split=> //.
by rewrite /ret_of Hret sw_S_eq_dot_product.
Qed.

End dsdp_stepwise.
