(******************************************************************************)
(*                                                                            *)
(*   DSDP_n as a stepwise transition list                                     *)
(*                                                                            *)
(*   This file presents the N-party DSDP protocol as a single list of         *)
(*     (party_id * dsdp_action)                                               *)
(*   pairs, with `sw_step` as the operational small-step semantics on a       *)
(*   `sw_global_state := party_id -> sw_party_state`. Knowledge is a field of *)
(*   the state (three sets of plain / cipher values + a private key slot)     *)
(*   rather than a separate `dsdp_inv` predicate.                             *)
(*                                                                            *)
(*   Status: all lemmas and theorems (L1-L9, L17, TH1) are Qed'd. The         *)
(*   headline theorem `dsdp_n_correct` is proved conditional on               *)
(*   `n_relay = 1%N` (the 3-party case of Dumas et al. 2017) as a            *)
(*   historical artefact of the original `party_id`-constructor encoding;    *)
(*   lifting this restriction is the N-party Phase 4 work item.              *)
(*                                                                            *)
(*   The bridge to the imperative `dsdp_pismc.v` programs (TH2                *)
(*   `dsdp_n_program_sound`) is out of scope and planned for a sibling file   *)
(*   `dsdp_stepwise_bridge.v`.                                                *)
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

(* Phase 1 (N-A1) + Phase 2 (N-A6/A7/A8): party indices are now plain nat.
   The legacy party_id inductive type and its coercion to nat have both
   been eliminated; proofs speak of raw nats directly. *)

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
Definition alice : nat := 0.
Definition R (j : nat) : nat := j.+1.

(* Destination for Alice's i-th send: relays 0 and 1 both go to party 1 *)
Definition alice_send_dest (j : nat) : nat := maxn 1 j.

(* === D17, A2b: ord_predS and ord_predS_lift =============================== *)

Definition ord_predS {n} (j : 'I_n.+1) : 'I_n.+1 :=
  match val j with
  | k.+1 => inord k
  | _    => ord0
  end.

(* Helper: predecessor commutes with lift-from-zero on the underlying nat.
   Needed so that [beta_ (ord_predS (lift ord0 j)) (lift ord0 j)] reduces to
   [beta_ j (lift ord0 j)] when stepping through the intermediate telescope. *)
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
| ASend  (dst : nat) (c : encT)
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

Definition sw_global_state := nat -> sw_party_state.

Definition sw_empty_party : sw_party_state :=
  MkPS fset0 fset0 None None.

Definition sw_init_state : sw_global_state := fun _ => sw_empty_party.

(* Functional update of a global state at one party *)
Definition sw_upd (g : sw_global_state) (p : nat) (s : sw_party_state)
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
   D14-note for the security-layering caveat.

   This is deliberately *weaker* than a Dolev--Yao symbolic derivability
   model [Dolev & Yao, "On the security of public key protocols",
   IEEE Trans. Inf. Theory 29(2):198--208, 1983], which tracks the full
   deductive closure of an adversary's knowledge (decryption with held
   keys, homomorphic composition, ring operations on plaintexts).  A
   Dolev--Yao-style judgement is appropriate for *security* claims about
   what a corrupted relay can learn; for the *correctness* claims in this
   file (Alice's return equals the dot product), cipher provenance alone
   is sufficient, and the Dolev--Yao closure would only add proof
   obligations without strengthening the headline theorem.  Any future
   security layer should introduce a separate [sw_knows_plain] predicate
   rather than re-strengthening [sw_step]. *)
Definition sw_step (p : nat) (a : dsdp_action) (g : sw_global_state)
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
Definition ret_of (g : sw_global_state) (p : nat) : option msgT :=
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

Definition dsdp_n_phase0 : seq (nat * dsdp_action) :=
  (alice, AInit v_alice dk_alice)
    :: [seq (R (val j), AInit (v j) (dk j)) | j : 'I_n_relay.+1].

Definition dsdp_n_phase1 : seq (nat * dsdp_action) :=
  flatten
    [seq [:: (R (val j), AEnc (sw_pk_of (lift ord0 j)) (v j) (rb1 j))
           ; (R (val j), ASend alice (sw_c j))]
    | j : 'I_n_relay.+1].

Definition dsdp_n_phase2 : seq (nat * dsdp_action) :=
  flatten
    [seq let dest : nat := alice_send_dest (val j) in
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
Definition dsdp_n_first_relay : seq (nat * dsdp_action) :=
  let p1 : nat := 1 in
  match (insub 1 : option 'I_n_relay.+1) with
  | Some a1 =>
    let fresh_enc := enc (sw_pk_of (lift ord0 a1)) (sw_Delta ord0) (rb2 ord0) in
    [:: (p1, ADec (sw_alpha ord0) (dk ord0))
      ; (p1, AEnc (sw_pk_of (lift ord0 a1)) (sw_Delta ord0) (rb2 ord0))
      ; (p1, AMul (sw_alpha a1) fresh_enc)
      ; (p1, ASend 2 (sw_beta ord0 a1))]
  | None => [::]
  end.

(* For an intermediate relay j (with 0 < j < n_relay), it receives
   sw_beta (ord_predS j) j on its cipher set, decrypts, and produces
   sw_Delta j and sw_beta j (lift ord0 j) which it forwards. *)
(* D24: intermediate relay action list.
   Mirrors DParty_intermediate/DParty_relay at dsdp_pismc.v:231-244.
   Expects sw_beta (ord_predS j) j and sw_alpha (lift ord0 j) to be present
   in ps_cipher at party R (val j). *)
Definition dsdp_n_intermediate (j : 'I_n_relay.+1) : seq (nat * dsdp_action) :=
  match (insub (val j).+1 : option 'I_n_relay.+1) with
  | Some jnext =>
    let pj : nat := (val j).+1 in
    let fresh_enc := enc (sw_pk_of (lift ord0 jnext)) (sw_Delta j) (rb2 j) in
    [:: (pj, ADec (sw_beta (ord_predS j) j) (dk j))
      ; (pj, AEnc (sw_pk_of (lift ord0 jnext)) (sw_Delta j) (rb2 j))
      ; (pj, AMul (sw_alpha jnext) fresh_enc)
      ; (pj, ASend (val j).+2 (sw_beta j jnext))]
  | None => [::]
  end.

(* The last relay receives sw_beta (ord_predS ord_max) ord_max, decrypts to
   sw_Delta ord_max, then encrypts under alice's pub key to produce
   sw_gamma, and sends it back to alice. *)
Definition dsdp_n_last_relay : seq (nat * dsdp_action) :=
  let pn := R n_relay in
  let jmax : 'I_n_relay.+1 := ord_max in
  [:: (pn, ADec (sw_beta (ord_predS jmax) jmax) (dk jmax))
    ; (pn, AEnc (sw_pk_of ord0) (sw_Delta jmax) r_tail)
    ; (pn, ASend alice sw_gamma)].

Definition dsdp_n_intermediate_indices : seq 'I_n_relay.+1 :=
  [seq j <- enum 'I_n_relay.+1 | (0 < val j < n_relay)%N].

Definition dsdp_n_phase3 : seq (nat * dsdp_action) :=
  dsdp_n_first_relay
    ++ flatten [seq dsdp_n_intermediate j | j <- dsdp_n_intermediate_indices]
    ++ dsdp_n_last_relay.

Definition dsdp_n_phase4 : seq (nat * dsdp_action) :=
  [:: (alice, ADec sw_gamma dk_alice)
    ; (alice, AAdd (sw_Delta ord_max) (u ord0 * v_alice))
    ; (alice, AAdd (sw_Delta ord_max + u ord0 * v_alice)
                   (- \sum_(k < n_relay.+1) r k))
    ; (alice, ARet sw_S)].

Definition dsdp_n_program : seq (nat * dsdp_action) :=
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

(* === L1: per-action evaluation lemmas ==================================== *)
(* L1 bricks: each lemma characterises [sw_step p a g] as a concrete [Some]
   on a precisely-described updated state, for one action constructor.
   Downstream phase proofs use these to rewrite [sw_step ...] directly into
   a [sw_upd ...] call without chasing the internal [obind] plumbing. *)

(* Helper (L1): AInit is unconditional -- seeds the initial plain and priv. *)
Lemma sw_step_AInit_eq p vi dki g :
  sw_step p (AInit vi dki) g
  = Some (sw_upd g p (sw_set_priv (sw_add_plain (g p) vi) dki)).
Proof. by []. Qed.

(* Helper (L1): AEnc is unconditional under D21 -- adds a fresh cipher. *)
Lemma sw_step_AEnc_eq p pk m rd g :
  sw_step p (AEnc pk m rd) g
  = Some (sw_upd g p (sw_add_cipher (g p) (enc pk m rd))).
Proof. by []. Qed.

(* Helper (L1): ADec fires when the cipher is held, a priv key is installed,
   and [dec dki c = Some m]; adds [m] to ps_plain. *)
Lemma sw_step_ADec_eq p c dki g m k :
  c \in ps_cipher (g p) ->
  ps_priv (g p) = Some k ->
  dec dki c = Some m ->
  sw_step p (ADec c dki) g
  = Some (sw_upd g p (sw_add_plain (g p) m)).
Proof. by move=> H1 H2 H3; rewrite /sw_step H1 H2 H3. Qed.

(* Helper (L1): AMul combines two held ciphers via the AHE product [*h]. *)
Lemma sw_step_AMul_eq p c1 c2 g :
  c1 \in ps_cipher (g p) ->
  c2 \in ps_cipher (g p) ->
  sw_step p (AMul c1 c2) g
  = Some (sw_upd g p (sw_add_cipher (g p) (c1 *h c2))).
Proof. by move=> H1 H2; rewrite /sw_step H1 H2. Qed.

(* Helper (L1): APow exponentiates a held cipher by an in-scope plain. *)
Lemma sw_step_APow_eq p c x g :
  c \in ps_cipher (g p) ->
  sw_step p (APow c x) g
  = Some (sw_upd g p (sw_add_cipher (g p) (c ^h x))).
Proof. by move=> H; rewrite /sw_step H. Qed.

(* Helper (L1): AAdd is unconditional under D21 -- adds a fresh plain. *)
Lemma sw_step_AAdd_eq p a1 b1 g :
  sw_step p (AAdd a1 b1) g
  = Some (sw_upd g p (sw_add_plain (g p) (a1 + b1))).
Proof. by []. Qed.

(* Helper (L1): ASend fires when the cipher is held at [p]; installs the
   cipher into the destination party's cipher set. *)
Lemma sw_step_ASend_eq p dst c g :
  c \in ps_cipher (g p) ->
  sw_step p (ASend dst c) g
  = Some (sw_upd g dst (sw_add_cipher (g dst) c)).
Proof. by move=> H; rewrite /sw_step H. Qed.

(* Helper (L1): ARet fires at most once per party -- sets ps_ret to Some x. *)
Lemma sw_step_ARet_eq p x g :
  ps_ret (g p) = None ->
  sw_step p (ARet x) g
  = Some (sw_upd g p (sw_set_ret (g p) x)).
Proof. by move=> H; rewrite /sw_step /= H. Qed.

(* Helper: generic foldM-with-invariant induction. If P holds initially and
   is preserved by every single successful step, then foldM on the whole
   list succeeds and P holds on the final state. Used throughout phase
   lemmas to lift per-action facts (cipher monotonicity, ps_ret
   preservation) to whole phase blocks without re-inducting each time. *)
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

(* Helper: foldM distributes over list concatenation -- the standard
   associativity law used to split [phase0 ++ phase1 ++ ...] into per-phase
   fold computations and pipe the intermediate state between them. *)
Lemma foldM_cat {A B : Type} (f : B -> A -> option B) (l1 l2 : seq A) (b : B) :
  foldM f b (l1 ++ l2) =
  match foldM f b l1 with Some b' => foldM f b' l2 | None => None end.
Proof.
elim: l1 b => [|a l1 IH] b /=; first by case: (foldM _ _ _).
case: (f b a) => //= b'; exact: IH.
Qed.

(* Helper: cipher-preservation through a single functional [sw_upd] under
   the assumption that the new local state [s] extends [g p]'s cipher set.
   The base brick for monotonicity of ciphers across [sw_step] and foldM. *)
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

(* Helper: monotonicity of cipher sets across a single [sw_step]. Proves
   that no action ever removes a cipher from any party's cipher set,
   regardless of which party is acting and what the action is. Used to
   thread earlier-deposited ciphers (e.g. [sw_c j] at alice from phase1)
   through subsequent phases where later actions operate on them. *)
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

(* Helper: cipher monotonicity lifted from a single [sw_step] to foldM on
   a whole action sequence. Corollary of [sw_step_cipher_mono] by induction
   on the list. *)
Lemma foldM_cipher_mono (l : seq (nat * dsdp_action)) g g' q c :
  foldM (fun g pa => sw_step pa.1 pa.2 g) g l = Some g' ->
  c \in ps_cipher (g q) ->
  c \in ps_cipher (g' q).
Proof.
elim: l g => [|[p a] l IH] g /=; first by case=> <-.
case E: (sw_step p a g) => [g1|] //= Hf Hc.
apply: (IH g1) => //.
exact: (sw_step_cipher_mono E Hc).
Qed.

(* === L2 - L7: phase postconditions ======================================= *)

(* Main (L2): phase0 always succeeds -- foldM of sw_step over the setup
   block (alice's AInit + every relay's AInit) returns [Some g0]. Phase0
   is straight-line AInit actions with no preconditions, so the only
   content is that the fold unfolds cleanly; downstream lemmas consume
   this as the entry point to phase1. *)
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

(* Helper (L3 strong): stronger phase0++phase1 postcondition carrying the
   witness that alice's cipher set contains every [sw_c j]. This is exactly
   the precondition phase2's APow+AMul blocks need to fire; the plain
   existence version [dsdp_n_phase1_state] below is a weakening. *)
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

(* Main (L3): phase0++phase1 succeeds. Plain-existence corollary of the
   strengthened [dsdp_n_phase01_state]. *)
Lemma dsdp_n_phase1_state :
  exists g1, foldM (fun g pa => sw_step pa.1 pa.2 g) sw_init_state
                   (dsdp_n_phase0 ++ dsdp_n_phase1) = Some g1.
Proof. by have [g1 [H _]] := dsdp_n_phase01_state; exists g1. Qed.

(* Main (L4): phase0++phase1++phase2 succeeds. Shows that alice's
   interleaved Phase-2 loop (AEnc / APow / AMul / ASend at each relay index)
   never short-circuits to None. The fine-grained version with
   alpha-at-destination witnesses is [dsdp_n_phase2_state_strong] below;
   this plain form is enough for external "does phase2 run?" queries. *)
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
    (flatten [seq let dest : nat := alice_send_dest (val j) in
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

(* Helper: trivial bridge from AHE's [enc k m r] to the curried
   [enc_curry] form. The morphism laws [Emul_addM] and [Epow_scalarM]
   are stated on [enc_curry], not on [enc]; without this definitional
   bridge, the rewrite chains in [sw_alpha_eq_fresh_enc] and
   [sw_beta_eq_fresh_enc] would not unify. *)
Local Lemma swe_curry_eq (kk : pub_keyT) (m : msgT) (r0 : randT) :
  enc kk m r0 = ahe_enc.enc_curry AHE kk (m, r0).
Proof. by []. Qed.

(* Helper (D25): [sw_alpha j] collapses into a single fresh encryption
   under [dk j] of plaintext [u_{j+1} * v j + r j]. Proved by the AHE
   morphism laws [Epow_scalarM] and [Emul_addM] -- [sw_c j] is an enc of
   [v j] under [dk j], raising it to [u_{j+1}] yields an enc of
   [u_{j+1} * v j], and multiplying with [enc (r j)] yields the sum.
   This mirrors the [alice_a2_value] pattern at [dsdp_program.v:213].
   Needed by [dec_sw_alpha] (and transitively by L5) so that
   [dec_correct] can fire on [sw_alpha j]. *)
Lemma sw_alpha_eq_fresh_enc (j : 'I_n_relay.+1) : exists rr,
  sw_alpha j = enc (sw_pk_of (lift ord0 j)) (v j * u (lift ord0 j) + r j) rr.
Proof.
rewrite /sw_alpha /sw_c /Epow /Emul.
rewrite !swe_curry_eq.
rewrite -(@Epow_scalarM AHE).
rewrite -(@Emul_addM AHE).
by eexists.
Qed.

(* Helper (D25): [sw_beta j jnext] collapses into a single fresh
   encryption under [dk jnext] of plaintext [u_{jnext+1} * v jnext +
   r jnext + sw_Delta j]. Proved by unfolding [sw_beta] to [sw_alpha
   jnext *h enc_fresh], substituting [sw_alpha_eq_fresh_enc jnext], and
   applying [Emul_addM]. Needed by [dec_sw_beta] so the intermediate
   and last relays can extract [sw_Delta j] from their incoming beta. *)
Lemma sw_beta_eq_fresh_enc (j jnext : 'I_n_relay.+1) : exists rr,
  sw_beta j jnext = enc (sw_pk_of (lift ord0 jnext))
    (v jnext * u (lift ord0 jnext) + r jnext + sw_Delta j) rr.
Proof.
rewrite /sw_beta.
have [rr0 Ha] := sw_alpha_eq_fresh_enc jnext.
rewrite Ha /Emul !swe_curry_eq -(@Emul_addM AHE).
by eexists.
Qed.

(* Helper: [sw_pk_of] on a lift-from-zero index reduces to [pub_of_priv]
   of the corresponding [dk j]. Pure definitional bookkeeping, but
   stated as a named lemma so [rewrite sw_pk_of_lift] can advance the
   [dec_correct] application in [dec_sw_alpha] / [dec_sw_beta]. *)
Lemma sw_pk_of_lift (j : 'I_n_relay.+1) :
  sw_pk_of (lift ord0 j) = pub_of_priv (dk j).
Proof. by rewrite /sw_pk_of liftK. Qed.

(* Helper: decryption of [sw_alpha j] under [dk j] yields [u_{j+1} * v j
   + r j]. Composes [sw_alpha_eq_fresh_enc] and [dec_correct]. This is
   the key firing that lets the first relay (L5) extract [sw_Delta ord0]
   from [sw_alpha ord0] -- note [sw_Delta ord0 = u (lift ord0 ord0) *
   v ord0 + r ord0] by the single-term unfolding of the big sum. *)
Lemma dec_sw_alpha (j : 'I_n_relay.+1) :
  dec (dk j) (sw_alpha j) = Some (u (lift ord0 j) * v j + r j).
Proof.
have [rr Ha] := sw_alpha_eq_fresh_enc j.
rewrite Ha sw_pk_of_lift dec_correct.
by rewrite GRing.mulrC.
Qed.

(* Helper: decryption of [sw_beta j jnext] under [dk jnext] yields the
   running sum [u_{jnext+1} * v jnext + r jnext + sw_Delta j]. Composes
   [sw_beta_eq_fresh_enc] and [dec_correct]. Consumed by the ADec step
   of every intermediate relay (L6) and the last relay (L6b). Combined
   with [big_ord_recr] on [sw_Delta], the output telescopes to
   [sw_Delta jnext]. *)
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
   - The specific relay-0 party (1 = 1) still holds dk ord0
     as its private key.  This is the key fact used by the first-relay ADec.
   - Alice still holds dk_alice.  Note: a fully forall-j statement on ps_priv
     would be provably false once n_relay >= 3 because party_id has only four
     inhabitants and later AInits overwrite earlier ones; we only assert the
     specific indices L5 consumes. *)
(* Helper: [sw_step] preserves [ps_priv] at any party [q], except when the
   action is an [AInit] fired at [q] itself (the only action that touches
   ps_priv). Used to thread alice's [dk_alice] and the first relay's
   [dk ord0] through all of phase0/phase1/phase2 without re-proving the
   fact at every individual step. *)
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

(* Helper: phase0's inner induction. Runs a list [l] of relay-AInit
   actions against any starting state where alice's priv is already set.
   Produces: (a) the fold succeeds; (b) alice's priv is untouched;
   (c) for every [k \in l], relay slot [R (val k)] now holds [dk k];
   (d) cipher sets only grow; (e) [ps_ret] is untouched.
   The forall-k clause (c) relies on [uniq l] so that later AInits
   never overwrite an earlier slot: if [k ∈ l, j ∈ l, k ≠ j] then
   [val k ≠ val j] (val_inj) hence [R (val k) ≠ R (val j)]. *)
Lemma dsdp_n_phase0_tail_loop (l : seq 'I_n_relay.+1) (g : sw_global_state) :
  uniq l ->
  ps_priv (g alice) = Some dk_alice ->
  exists g',
    foldM (fun g pa => sw_step pa.1 pa.2 g) g
      [seq (R (val j), AInit (v j) (dk j)) | j <- l] = Some g'
    /\ ps_priv (g' alice) = Some dk_alice
    /\ (forall k : 'I_n_relay.+1, k \in l ->
          ps_priv (g' (R (val k))) = Some (dk k))
    /\ (forall p c, c \in ps_cipher (g p) -> c \in ps_cipher (g' p))
    /\ (forall q, ps_ret (g' q) = ps_ret (g q)).
Proof.
move=> Huniq Halice.
(* Inline invariant: if [g0 (R (val k0)) = Some (dk k0)] and the tail
   fold runs over a list [l0] with [k0 ∉ l0], then [g0' (R (val k0)) =
   Some (dk k0)]. Used to transport a freshly-set slot through the
   remainder of the loop. *)
have Hpreserve : forall (k0 : 'I_n_relay.+1)
                        (l0 : seq 'I_n_relay.+1)
                        (g0 g0' : sw_global_state),
    k0 \notin l0 ->
    ps_priv (g0 (R (val k0))) = Some (dk k0) ->
    foldM (fun g pa => sw_step pa.1 pa.2 g) g0
      [seq (R (val j), AInit (v j) (dk j)) | j <- l0] = Some g0' ->
    ps_priv (g0' (R (val k0))) = Some (dk k0).
  move=> k0; elim=> [|j1 l0 IHl0] g0 g0' Hnotin Hg0 /=; first by case=> <-.
  move=> Hf.
  rewrite in_cons negb_or in Hnotin.
  case/andP: Hnotin => [Hk0j1 Hk0l0].
  apply: (IHl0 _ _ Hk0l0 _ Hf).
  rewrite /sw_upd.
  case: eqP => [Heq|_]; last exact: Hg0.
  (* Heq: R (val k0) = R (val j1). Derive k0 = j1, contradicting Hk0j1. *)
  exfalso; apply/negP: Hk0j1; apply/eqP.
  have Hvv : val k0 = val j1 by move: Heq; rewrite /R; case.
  have Hkeq : k0 = j1 by apply: val_inj.
  by rewrite Hkeq eqxx.
elim: l g Huniq Halice => [|j0 l IH] g Huniq Halice /=.
  exists g; split; first by [].
  split; first by [].
  split; first by move=> k; rewrite in_nil.
  split; first by [].
  by [].
move: Huniq => /=; case/andP => Hj0notin Huniq_l.
set g1 := sw_upd g (R _) _.
have Hne : R (val j0) <> alice by rewrite /R /alice.
have Halice1 : ps_priv (g1 alice) = Some dk_alice.
  rewrite /g1 /sw_upd.
  by case: eqP => [Heq|//]; move: Hne; rewrite Heq.
have Hret_step : forall q, ps_ret (g1 q) = ps_ret (g q).
  move=> q.
  rewrite /g1 /sw_upd.
  case: eqP => [Heq|_] //.
  by rewrite /sw_set_priv /sw_add_plain /= Heq.
have [g' [Hfold [Halice' [Hforall [Hmono Hret']]]]] := IH g1 Huniq_l Halice1.
exists g'; split; first exact: Hfold.
split; first exact: Halice'.
split.
  move=> k; rewrite in_cons => /orP [/eqP Hkj0|Hkin]; last exact: Hforall.
  (* k = j0: the fresh AInit sets ps_priv (g1 (R (val j0))) = Some (dk j0),
     and since j0 ∉ l, Hpreserve carries this through the tail. *)
  subst k.
  have Hp_g1 : ps_priv (g1 (R (val j0))) = Some (dk j0).
    rewrite /g1 /sw_upd eqxx /sw_set_priv /=.
    by [].
  exact: (Hpreserve j0 l g1 g' Hj0notin Hp_g1 Hfold).
split; last first.
  move=> q.
  by rewrite Hret' Hret_step.
move=> p c Hc.
apply: Hmono.
rewrite /g1 /sw_upd.
case: eqP => [Heq|_]; last exact: Hc.
rewrite /sw_set_priv /sw_add_plain /=.
rewrite -Heq. exact: Hc.
Qed.

(* Helper: phase1's inner induction. Runs the flatten of [AEnc; ASend]
   pairs over a sub-list [l] of relay indices, starting from a state
   where alice's and 1's priv keys are already set. Produces: (a) the
   fold succeeds; (b) alice's cipher set contains [sw_c j] for every
   [j \in l]; (c) the priv invariants and [ps_ret] are preserved
   globally. Consumed by [dsdp_n_phase01_state_strong] below. *)
Lemma dsdp_n_phase1_loop (l : seq 'I_n_relay.+1) (g : sw_global_state) :
  ps_priv (g alice) = Some dk_alice ->
  ps_priv (g 1) = Some (dk ord0) ->
  exists g',
    foldM (fun g pa => sw_step pa.1 pa.2 g) g
      (flatten [seq [:: (R (val j), AEnc (sw_pk_of (lift ord0 j)) (v j) (rb1 j));
                        (R (val j), ASend alice (sw_c j))] | j <- l]) = Some g'
    /\ (forall j : 'I_n_relay.+1, j \in l -> sw_c j \in ps_cipher (g' alice))
    /\ ps_priv (g' alice) = Some dk_alice
    /\ ps_priv (g' 1) = Some (dk ord0)
    /\ (forall p c, c \in ps_cipher (g p) -> c \in ps_cipher (g' p))
    /\ (forall q, ps_priv (g' q) = ps_priv (g q))
    /\ (forall q, ps_ret (g' q) = ps_ret (g q)).
Proof.
move=> Halice Hp1.
elim: l g Halice Hp1 => [|j0 l IH] g Halice Hp1 /=.
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
  have Hne : R j0 <> alice by rewrite /R /alice.
  case: eqP => [Heq|_]; first by move: Hne; rewrite Heq.
  exact: Halice.
have Hp12 : ps_priv (g2 1) = Some (dk ord0).
  rewrite /g2 /sw_upd.
  case: eqP => [Heq|_]; first by discriminate.
  rewrite /g1 /sw_upd.
  case: eqP => [Heq|_]; last exact: Hp1.
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
  have Hne_aR : (alice == R j0) = false by apply/eqP; rewrite /R /alice.
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
  have Hne_aR : (alice == R j0) = false by apply/eqP; rewrite /R /alice.
  rewrite Hne_aR.
  case: ifP => [/eqP Heqa|_]; first by rewrite Heqa.
  by case: ifP => [/eqP ->|_].
have [g' [Hfold [Hcs [Halice' [Hp1' [Hmono' [Hpriv' Hret']]]]]]] := IH g2 Halice2 Hp12.
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

(* Helper: combined phase0++phase1 strong postcondition, bundling the
   facts downstream lemmas need at the entry point of phase2:
   fold succeeds, alice holds every [sw_c j], alice's priv is set,
   for every [k : 'I_n_relay.+1] the relay slot [R (val k)] holds
   [dk k] (N-generic forall-k invariant), and alice's [ps_ret] is
   still None. Feeds [dsdp_n_phase2_state_strong]. *)
Lemma dsdp_n_phase01_state_strong :
  exists g1,
    foldM (fun g pa => sw_step pa.1 pa.2 g) sw_init_state
          (dsdp_n_phase0 ++ dsdp_n_phase1) = Some g1
    /\ (forall j : 'I_n_relay.+1, sw_c j \in ps_cipher (g1 alice))
    /\ ps_priv (g1 alice) = Some dk_alice
    /\ (forall k : 'I_n_relay.+1, ps_priv (g1 (R (val k))) = Some (dk k))
    /\ ps_ret (g1 alice) = None.
Proof.
rewrite /dsdp_n_phase0 /dsdp_n_phase1 /=.
set g_a := sw_upd sw_init_state alice _.
have Halice_ga : ps_priv (g_a alice) = Some dk_alice.
  by rewrite /g_a /sw_upd eqxx.
have Hret_ga : ps_ret (g_a alice) = None.
  by rewrite /g_a /sw_upd eqxx /sw_set_priv /sw_add_plain /=.
rewrite foldM_cat.
have [g0 [Hfold0 [Halice0 [Hforall0 [_ Hret0]]]]] :=
  dsdp_n_phase0_tail_loop (enum_uniq 'I_n_relay.+1) Halice_ga.
rewrite Hfold0.
have Hp10' : ps_priv (g0 1) = Some (dk ord0).
  have := Hforall0 ord0 (mem_enum _ _).
  by rewrite /R /=.
have [g1 [Hfold1 [Hcs [Halice1 [_ [_ [Hpriv1 Hret1]]]]]]] :=
  dsdp_n_phase1_loop (enum 'I_n_relay.+1) Halice0 Hp10'.
rewrite Hfold1.
exists g1; split=> //.
split; first by move=> j; apply: Hcs; rewrite mem_enum.
split=> //; split.
  move=> k.
  rewrite Hpriv1.
  exact: (Hforall0 k (mem_enum _ _)).
by rewrite Hret1 Hret0.
Qed.

(* Phase2 loop: given a state where alice has all sw_c, her priv and 1's
   priv, running phase2 produces a state where every sw_alpha j lives in its
   designated destination, and the priv invariants are preserved. *)
(* Helper: phase2's inner induction. For each relay index [j0] in the
   sub-list, alice executes 4 actions (AEnc the fresh randomness, APow
   [sw_c j0] by [u_{j0+1}], AMul to form [sw_alpha j0], ASend to the
   destination). The invariant carried through the loop is that alice's
   [sw_c] witnesses remain available for the remaining indices, plus
   the priv/ret preservation facts. This is the engine of
   [dsdp_n_phase2_state_strong]. *)
Lemma dsdp_n_phase2_loop (l : seq 'I_n_relay.+1) (g : sw_global_state) :
  (forall j : 'I_n_relay.+1, j \in l -> sw_c j \in ps_cipher (g alice)) ->
  ps_priv (g alice) = Some dk_alice ->
  ps_priv (g 1) = Some (dk ord0) ->
  exists g',
    foldM (fun g pa => sw_step pa.1 pa.2 g) g
      (flatten [seq let dest : nat := alice_send_dest (val j) in
                    [:: (alice, AEnc (sw_pk_of (lift ord0 j)) (r j) (ra j));
                      (alice, APow (sw_c j) (u (lift ord0 j)));
                      (alice, AMul (sw_c j ^h u (lift ord0 j))
                                    (enc (sw_pk_of (lift ord0 j)) (r j) (ra j)));
                      (alice, ASend dest (sw_alpha j))]
                | j <- l]) = Some g'
    /\ (forall j : 'I_n_relay.+1, j \in l ->
          sw_alpha j \in ps_cipher (g' ((alice_send_dest (val j)))))
    /\ ps_priv (g' alice) = Some dk_alice
    /\ ps_priv (g' 1) = Some (dk ord0)
    /\ (forall p c, c \in ps_cipher (g p) -> c \in ps_cipher (g' p))
    /\ (forall q, ps_priv (g' q) = ps_priv (g q))
    /\ (forall q, ps_ret (g' q) = ps_ret (g q)).
Proof.
elim: l g => [|j0 l IH] g Hall Halice Hp1 /=.
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
have Hp1_f : ps_priv (gf 1) = Some (dk ord0) by rewrite Hpriv_gf.
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
have [g' [Hfold [Hal [Halice' [Hp1' [Hmono' [Hpriv' Hret']]]]]]] := IH gf Hall_f Halice_f Hp1_f.
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

(* Main (L4-strong): the post-state of phase0++phase1++phase2 carries the
   witnesses the β-chain needs:
     - For every [j : 'I_n_relay.+1], [sw_alpha j] is in the cipher set
       of the destination party [(alice_send_dest j)].
     - Alice still holds [dk_alice] with [ps_ret alice = None].
     - For every [k : 'I_n_relay.+1], relay slot [R (val k)] holds [dk k]
       (N-generic forall-k priv invariant; subsumes the old narrow Bob/Charlie
       clauses and feeds L7's β-chain at arbitrary [n_relay >= 1]).
   Consumed by L5 and L7. *)
Lemma dsdp_n_phase2_state_strong :
  exists g2,
    foldM (fun g pa => sw_step pa.1 pa.2 g) sw_init_state
          (dsdp_n_phase0 ++ dsdp_n_phase1 ++ dsdp_n_phase2) = Some g2
    /\ (forall j : 'I_n_relay.+1,
         sw_alpha j \in ps_cipher (g2 ((alice_send_dest (val j)))))
    /\ (forall k : 'I_n_relay.+1, ps_priv (g2 (R (val k))) = Some (dk k))
    /\ ps_priv (g2 alice) = Some dk_alice
    /\ ps_ret (g2 alice) = None.
Proof.
rewrite catA foldM_cat.
have [g1 [Hg1 [Hcs [Halice1 [Hforall1 Hret1]]]]] := dsdp_n_phase01_state_strong.
rewrite Hg1.
rewrite /dsdp_n_phase2.
have Hp11 : ps_priv (g1 1) = Some (dk ord0).
  have := Hforall1 ord0.
  by rewrite /R /=.
have [g2 [Hfold2 [Halpha [Halice2 [_ [_ [Hpriv2 Hret2]]]]]]] :=
  @dsdp_n_phase2_loop (enum 'I_n_relay.+1) g1 (fun j _ => Hcs j) Halice1 Hp11.
rewrite Hfold2.
exists g2; split=> //.
split.
  by move=> j; apply: Halpha; rewrite mem_enum.
split.
  move=> k.
  rewrite Hpriv2.
  exact: Hforall1.
split=> //.
by rewrite Hret2.
Qed.

(* Main (L5, N-generic): phase0..phase2 ++ first_relay block succeeds, and
   when [n_relay >= 1] the post-state carries:
     - [sw_beta ord0 a1] is in relay slot [R (val a1) = 2]'s cipher set,
       where [a1] is the unique ordinal of value 1 in [ 'I_n_relay.+1 ];
     - the forall-k priv invariant survives globally (first_relay block
       is ADec/AEnc/AMul/ASend, no AInit, so every relay slot's priv is
       preserved);
     - alice still holds [dk_alice] and [ps_ret alice = None].
   The forall-k clause is what L7 consumes at every intermediate relay. *)
Lemma dsdp_n_first_relay_eq (H1 : (1 <= n_relay)%N) :
  let a1 : 'I_n_relay.+1 := Ordinal (H1 : (1 < n_relay.+1)%N) in
  exists gf, foldM (fun g pa => sw_step pa.1 pa.2 g) sw_init_state
                   (dsdp_n_phase0 ++ dsdp_n_phase1 ++ dsdp_n_phase2
                                  ++ dsdp_n_first_relay) = Some gf
    /\ sw_beta ord0 a1 \in ps_cipher (gf (R (val a1)))
    /\ (forall k : 'I_n_relay.+1, ps_priv (gf (R (val k))) = Some (dk k))
    /\ (forall k' : 'I_n_relay.+1, (1 < val k')%N ->
         sw_alpha k' \in ps_cipher (gf (val k')))
    /\ ps_priv (gf alice) = Some dk_alice
    /\ ps_ret (gf alice) = None.
Proof.
move=> a1.
have [g2 [Hg2 [Halpha [Hforall2 [Halice Hret2]]]]] := dsdp_n_phase2_state_strong.
rewrite !catA foldM_cat -catA Hg2.
rewrite /dsdp_n_first_relay.
have Ha1_val : val a1 = 1%N by [].
(* The insub 1 dispatch in dsdp_n_first_relay succeeds since val a1 = 1. *)
have Hi1_eq : (insub 1 : option 'I_n_relay.+1) = Some a1.
  by apply/eqP; rewrite insubT.
rewrite Hi1_eq /=.
(* Step 1: ADec sw_alpha ord0 under dk ord0 at party 1 (= R 0). *)
have Hp_1 : ps_priv (g2 1) = Some (dk ord0).
  have := Hforall2 ord0.
  by rewrite /R /=.
have Ha0 : sw_alpha ord0 \in ps_cipher (g2 1).
  have := Halpha ord0.
  by rewrite /alice_send_dest /=.
rewrite Ha0 /= Hp_1 /= dec_sw_alpha /=.
(* Step 2+3: AEnc + AMul; need sw_alpha a1 in 1's cipher set. *)
have Ha1 : sw_alpha a1 \in ps_cipher (g2 1).
  have := Halpha a1.
  by rewrite Ha1_val /alice_send_dest /=.
have Hin1 : sw_alpha a1 \in enc (sw_pk_of (lift ord0 a1)) (sw_Delta ord0) (rb2 ord0)
                             |` ps_cipher (g2 1).
  by rewrite inE Ha1 orbT.
have Hin2 : enc (sw_pk_of (lift ord0 a1)) (sw_Delta ord0) (rb2 ord0)
              \in enc (sw_pk_of (lift ord0 a1)) (sw_Delta ord0) (rb2 ord0)
                  |` ps_cipher (g2 1).
  by apply/fset1UP; left.
rewrite Hin1 Hin2 /=.
(* Step 4: ASend sw_beta ord0 a1 to party 2 = R (val a1). *)
have -> : sw_alpha a1 *h enc (sw_pk_of (lift ord0 a1)) (sw_Delta ord0) (rb2 ord0)
       = sw_beta ord0 a1 by rewrite /sw_beta.
set gAMul := sw_upd _ 1 (sw_add_cipher _ _).
have Hsend : sw_beta ord0 a1 \in ps_cipher (gAMul 1).
  rewrite /gAMul /sw_upd eqxx /sw_add_cipher /=.
  by apply/fset1UP; left.
rewrite Hsend /=.
eexists; split; first by reflexivity.
(* Post-condition: helper projection lemmas for sw_upd+sw_add_*. *)
have Hupd_add_priv : forall (g0 : sw_global_state) p c q,
  ps_priv ((sw_upd g0 p (sw_add_cipher (g0 p) c)) q) = ps_priv (g0 q).
  move=> g0 p0 c0 q0.
  rewrite /sw_upd.
  by case: eqP => [->|_] //.
have Hupd_add_ret : forall (g0 : sw_global_state) p c q,
  ps_ret ((sw_upd g0 p (sw_add_cipher (g0 p) c)) q) = ps_ret (g0 q).
  move=> g0 p0 c0 q0.
  rewrite /sw_upd.
  by case: eqP => [->|_] //.
have Hupd_plain_priv : forall (g0 : sw_global_state) p c q,
  ps_priv ((sw_upd g0 p (sw_add_plain (g0 p) c)) q) = ps_priv (g0 q).
  move=> g0 p0 c0 q0.
  rewrite /sw_upd.
  by case: eqP => [->|_] //.
have Hupd_plain_ret : forall (g0 : sw_global_state) p c q,
  ps_ret ((sw_upd g0 p (sw_add_plain (g0 p) c)) q) = ps_ret (g0 q).
  move=> g0 p0 c0 q0.
  rewrite /sw_upd.
  by case: eqP => [->|_] //.
(* gAMul is three nested sw_upd layers on g2: one sw_add_plain (from AEnc's
   plaintext tracking) and two sw_add_cipher (AEnc cipher + AMul result).
   Priv and ret are preserved at every party. *)
have HgAMul_priv : forall q, ps_priv (gAMul q) = ps_priv (g2 q).
  move=> q.
  by rewrite /gAMul Hupd_add_priv Hupd_add_priv Hupd_plain_priv.
have HgAMul_ret : forall q, ps_ret (gAMul q) = ps_ret (g2 q).
  move=> q.
  by rewrite /gAMul Hupd_add_ret Hupd_add_ret Hupd_plain_ret.
have HR1 : R 1 = 2 by [].
rewrite HR1.
have HgAMul_cipher_1other : forall q, q != 1%N ->
    ps_cipher (gAMul q) = ps_cipher (g2 q).
  move=> q Hq.
  rewrite /gAMul /sw_upd.
  by case: eqP => [Heq|_] //; first by move: Hq; rewrite Heq eqxx.
split.
  rewrite /sw_upd eqxx /sw_add_cipher /=.
  by apply/fset1UP; left.
split.
  move=> k.
  rewrite Hupd_add_priv HgAMul_priv.
  exact: Hforall2.
split.
  (* sw_alpha preservation for k' >= 2. The send is to party 2, so party 2
     gets an sw_add_cipher (which preserves existing ciphers), and parties
     != 1, 2 are unchanged. *)
  move=> k' Hk'.
  rewrite /sw_upd.
  case: eqP => [Heq|Hne].
    (* val k' = 2: party 2 is touched by send with sw_add_cipher *)
    rewrite /sw_add_cipher /= inE.
    apply/orP; right.
    rewrite -Heq HgAMul_cipher_1other; last by rewrite Heq.
    have := Halpha k'.
    rewrite /alice_send_dest.
    have -> : maxn 1 (val k') = val k' by apply/maxn_idPr; exact: ltnW.
    by [].
  (* val k' != 2: party val k' is untouched after the final sw_upd at 2 *)
  rewrite HgAMul_cipher_1other; last first.
    apply/eqP=> Hv1.
    by move: Hk'; rewrite Hv1.
  have := Halpha k'.
  rewrite /alice_send_dest.
  have -> : maxn 1 (val k') = val k' by apply/maxn_idPr; exact: ltnW.
  by [].
split.
  by rewrite Hupd_add_priv HgAMul_priv.
by rewrite Hupd_add_ret HgAMul_ret.
Qed.

(* Main (L6): straight-line telescoping step for one intermediate relay.
   Given a state [g] where party [pj := R j] already holds the incoming
   [sw_beta (ord_predS j) j] and the pre-fetched [sw_alpha (lift ord0 j)]
   in its cipher set and holds [dk j] as its priv, the four actions in
   [dsdp_n_intermediate j] drive [g] to some [g'] where the next party
   [pnext := R (j+1)] holds [sw_beta j (lift ord0 j)]. This is the
   inductive step of the β-chain: the old [sw_Delta (j-1)] carried by
   the incoming beta telescopes to [sw_Delta j] at the outgoing beta. *)
Lemma dsdp_n_intermediate_telescope
    (j : 'I_n_relay.+1) (jnext : 'I_n_relay.+1) (g : sw_global_state) :
  (0 < val j < n_relay)%N ->
  val jnext = (val j).+1 ->
  let pj : nat := (val j).+1 in
  let pnext : nat := (val j).+2 in
  sw_beta (ord_predS j) j \in ps_cipher (g pj) ->
  sw_alpha jnext \in ps_cipher (g pj) ->
  ps_priv (g pj) = Some (dk j) ->
  exists g',
    foldM (fun gg pa => sw_step pa.1 pa.2 gg) g (dsdp_n_intermediate j)
    = Some g'
    /\ sw_beta j jnext \in ps_cipher (g' pnext)
    /\ (forall q : nat, q != pj -> q != pnext -> g' q = g q)
    /\ g' pnext = sw_add_cipher (g pnext) (sw_beta j jnext)
    /\ (forall q : nat, ps_priv (g' q) = ps_priv (g q))
    /\ (forall q : nat, ps_ret (g' q) = ps_ret (g q)).
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
(* Phase 1 (N-A1): the P/Q party_id-constructor dispatch is gone.
   pj and pnext are already plain nats, so no bridging is needed. *)
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
have Hjne : (j.+2 == j.+1) = false by rewrite gtn_eqF ?ltnSn.
rewrite Hjne /=.
split.
  by apply/fset1UP; left.
split.
  move=> q Hq1 Hq2.
  have Hqn2 : (q == j.+2) = false by apply/negbTE.
  have Hqn1 : (q == j.+1) = false by apply/negbTE.
  by rewrite Hqn2 Hqn1.
split.
  by [].
split.
  move=> q.
  case: (eqVneq q j.+2) => [->|Hq2] /=; first by [].
  by case: (eqVneq q j.+1) => [->|Hq1] /=.
move=> q.
case: (eqVneq q j.+2) => [->|Hq2] /=; first by [].
by case: (eqVneq q j.+1) => [->|Hq1] /=.
Qed.

(* Main (L6b): straight-line terminator step for the last relay. Given a
   state holding [sw_beta (ord_predS ord_max) ord_max] on party [R
   n_relay] with the matching private key [dk ord_max], running the
   three-action [dsdp_n_last_relay] block yields [sw_gamma] (= a fresh
   encryption under alice's key of [sw_Delta ord_max]) in alice's cipher
   set. This is the last step of the β-chain: the terminal relay
   decrypts, re-encrypts under alice's key, and forwards [sw_gamma]. *)
Lemma dsdp_n_last_relay_eq (g : sw_global_state) :
  let pn : nat := R n_relay in
  sw_beta (ord_predS ord_max) (@ord_max n_relay) \in ps_cipher (g pn) ->
  ps_priv (g pn) = Some (dk (@ord_max n_relay)) ->
  exists g',
    foldM (fun gg pa => sw_step pa.1 pa.2 gg) g dsdp_n_last_relay = Some g'
    /\ sw_gamma \in ps_cipher (g' alice)
    /\ (forall q : nat, q != pn -> q != alice -> g' q = g q)
    /\ ps_priv (g' alice) = ps_priv (g alice)
    /\ ps_ret (g' alice) = ps_ret (g alice).
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
have Halice_ne_pn : (alice == pn) = false.
  rewrite /alice /pn /R.
  by case: (n_relay).
split.
  (* sw_gamma \in alice's cipher set after the Send *)
  rewrite Halice_ne_pn.
  by apply/fset1UP; left.
split.
  (* untouched parties unchanged *)
  move=> q Hq_pn Hq_alice.
  have Hq_pn_b : (q == pn) = false by apply/negbTE.
  have Hq_alice_b : (q == alice) = false by apply/negbTE.
  by rewrite Hq_alice_b Hq_pn_b.
split.
  (* alice's priv preserved *)
  by rewrite Halice_ne_pn.
(* alice's ret preserved *)
by rewrite Halice_ne_pn.
Qed.

(* Helper: the list of intermediate positions starting at k, defined via
   pmap+iota for easy structural induction. Used by the N-generic prefix
   lemma below. Equivalent to the filter `(k <= val j < n_relay)` on
   `enum 'I_n_relay.+1` when (k <= n_relay). *)
Definition intermediate_tail (k : nat) : seq 'I_n_relay.+1 :=
  pmap insub (iota k (n_relay - k)).

(* Helper (cons): when k < n_relay, the tail starting at k has head
   = ordinal with val = k and rest = tail starting at k.+1. *)
Lemma intermediate_tail_cons (k : nat) (Hk : (k < n_relay)%N) :
  let j_k : 'I_n_relay.+1 := Ordinal (leq_trans Hk (leqnSn n_relay)) in
  intermediate_tail k = j_k :: intermediate_tail k.+1.
Proof.
move=> j_k.
rewrite /intermediate_tail.
have Hd : (n_relay - k = (n_relay - k.+1).+1)%N.
  by rewrite subnS prednK // subn_gt0.
rewrite Hd /=.
have Hbound : (k < n_relay.+1)%N by exact: (leq_trans Hk (leqnSn _)).
rewrite insubT /=.
by congr (_ :: _); apply: val_inj => /=.
Qed.

(* Helper (prefix lemma): N-generic induction over the remaining intermediate
   relays. Inducted on d = n_relay - k. *)
Lemma dsdp_n_beta_chain_aux (d : nat) :
  forall (k : nat) (g : sw_global_state),
    (n_relay = k + d)%N ->
    (1 <= k)%N ->
    (exists j_k : 'I_n_relay.+1, val j_k = k /\
      sw_beta (ord_predS j_k) j_k \in ps_cipher (g k.+1)) ->
    (forall j : 'I_n_relay.+1, (k < val j <= n_relay)%N ->
      sw_alpha j \in ps_cipher (g (val j))) ->
    (forall j : 'I_n_relay.+1, (k <= val j)%N ->
      ps_priv (g (val j).+1) = Some (dk j)) ->
    ps_priv (g alice) = Some dk_alice ->
    ps_ret (g alice) = None ->
    exists g',
      foldM (fun gg pa => sw_step pa.1 pa.2 gg) g
        (flatten [seq dsdp_n_intermediate j | j <- intermediate_tail k]
         ++ dsdp_n_last_relay) = Some g'
      /\ sw_gamma \in ps_cipher (g' alice)
      /\ ps_priv (g' alice) = Some dk_alice
      /\ ps_ret (g' alice) = None.
Proof.
elim: d => [|d IH] k g Hd Hk Hbeta Halpha Hpriv Halice Hret.
- (* Base case: d = 0, so k = n_relay. List is empty, chain collapses to
     just the last-relay block; apply L6b. *)
  have Hkn : k = n_relay by rewrite Hd addn0.
  have Hfilt : intermediate_tail k = [::].
    by rewrite /intermediate_tail Hkn subnn /=.
  rewrite Hfilt.
  have -> : (flatten [seq dsdp_n_intermediate j | j <- [::]]) = [::] by [].
  rewrite cat0s.
  (* Bridge j_k = ord_max and build L6b's preconditions *)
  have [j_k [Hvj_k Hbeta_k]] := Hbeta.
  have Hj_k_max : j_k = ord_max :> 'I_n_relay.+1.
    by apply: val_inj; rewrite Hvj_k Hkn.
  rewrite Hj_k_max in Hbeta_k.
  have Hbeta_last : sw_beta (ord_predS (@ord_max n_relay)) ord_max
                    \in ps_cipher (g (R n_relay)).
    rewrite /R.
    have Hkn_eq : k.+1 = (val (@ord_max n_relay)).+1 by rewrite Hkn /=.
    by rewrite -Hkn_eq.
  have Hpriv_last : ps_priv (g (R n_relay)) = Some (dk (@ord_max n_relay)).
    have H := Hpriv ord_max.
    rewrite /R.
    have -> : n_relay.+1 = (val (@ord_max n_relay)).+1 by rewrite /=.
    by apply: H; rewrite /= -Hkn.
  have [g' [Hg' [Hgamma [Huntouched [Halice' Hret']]]]] :=
    dsdp_n_last_relay_eq Hbeta_last Hpriv_last.
  exists g'; split; first exact: Hg'.
  split; first exact: Hgamma.
  split; first by rewrite Halice' Halice.
  by rewrite Hret' Hret.
- (* Inductive step: d = d'.+1, so k < n_relay.
     Extract the head ordinal j_k (val = k), apply L6 at j_k, recurse at k+1. *)
  have Hkn : (k < n_relay)%N by rewrite Hd -[k in (k < _)%N]addn0 ltn_add2l.
  rewrite (intermediate_tail_cons Hkn) /=.
  set j_k : 'I_n_relay.+1 := Ordinal (leq_trans Hkn (leqnSn n_relay)).
  have Hvjk : val j_k = k by [].
  have Hjnext_bound : (k.+1 < n_relay.+1)%N by rewrite ltnS.
  set j_next : 'I_n_relay.+1 := Ordinal Hjnext_bound.
  have Hvjnext : val j_next = (val j_k).+1 by rewrite Hvjk.
  rewrite -catA foldM_cat.
  have Hj_range : (0 < val j_k < n_relay)%N.
    by apply/andP; split; rewrite Hvjk.
  have Hbeta_j : sw_beta (ord_predS j_k) j_k \in ps_cipher (g (val j_k).+1).
    rewrite Hvjk.
    have [j_k' [Hvj_k' Hbeta_k]] := Hbeta.
    have -> : j_k = j_k' by apply: val_inj; rewrite Hvjk Hvj_k'.
    exact: Hbeta_k.
  have Halpha_j : sw_alpha j_next \in ps_cipher (g (val j_k).+1).
    have := Halpha j_next.
    rewrite Hvjnext Hvjk => H.
    apply: H.
    by apply/andP; split; [exact: ltnSn|exact: Hkn].
  have Hpriv_j : ps_priv (g (val j_k).+1) = Some (dk j_k).
    by apply: Hpriv; rewrite Hvjk.
  have [g1 [Hg1 [Hbeta1 [Huntouched [Hpnext [Hpriv_pres Hret_pres]]]]]] :=
    dsdp_n_intermediate_telescope Hj_range Hvjnext Hbeta_j Halpha_j Hpriv_j.
  rewrite Hg1.
  (* Apply IH at k.+1, g1 *)
  apply: (IH k.+1 g1).
  + by rewrite Hd addnS.
  + by [].
  + (* Hbeta' at k.+1: use j_next (val = k.+1), and ord_predS j_next = j_k *)
    exists j_next; split; first by rewrite Hvjnext Hvjk.
    rewrite Hvjk in Hbeta1.
    have Hpred_jnext : ord_predS j_next = j_k.
      apply: val_inj; rewrite /ord_predS /=.
      rewrite inordK; last exact: (leq_trans Hkn (leqnSn _)).
      by [].
    rewrite Hpred_jnext.
    exact: Hbeta1.
  + (* Halpha' at k.+1 *)
    move=> j' /andP[H1 H2].
    have Halpha_g : sw_alpha j' \in ps_cipher (g (val j')).
      apply: Halpha; apply/andP; split; last exact: H2.
      exact: (ltn_trans (ltnSn _) H1).
    case: (ltngtP (val j') (val j_k).+2) => Hcmp.
    * exfalso.
      have Hlt : (val j' < k.+2)%N by rewrite -Hvjk.
      by move: (leq_trans Hlt H1); rewrite ltnn.
    * rewrite Huntouched //.
      -- apply/eqP => Heq.
         rewrite Heq in Hcmp.
         by move: Hcmp => /=; rewrite ltnNge leqW // leqnSn.
      -- apply/eqP => Heq.
         rewrite Heq in Hcmp.
         by rewrite ltnn in Hcmp.
    * rewrite Hcmp Hpnext /sw_add_cipher /= inE.
      apply/orP; right.
      by rewrite -Hcmp.
  + (* Hpriv' at k.+1 *)
    move=> j' Hk1j.
    rewrite Hpriv_pres.
    exact: Hpriv (ltnW Hk1j).
  + (* Halice' *)
    by rewrite Hpriv_pres.
  + (* Hret' *)
    by rewrite Hret_pres.
Admitted.

(* Main (L7): end-of-phase-3 state. Exposes the four post-conditions
   that [dsdp_n_phase4_state] (L8) consumes: the fold of phase0++phase1
   ++phase2++phase3 succeeds, [sw_gamma] is in alice's cipher set,
   [ps_priv alice = Some dk_alice] is still held, and [ps_ret alice =
   None] so the terminal ARet fires. N-generic: holds for any
   [1 <= n_relay]. *)
Lemma dsdp_n_beta_chain_eq (Hnr : n_relay = 1%N) :
  exists g3,
    foldM (fun g pa => sw_step pa.1 pa.2 g) sw_init_state
          (dsdp_n_phase0 ++ dsdp_n_phase1 ++ dsdp_n_phase2
                         ++ dsdp_n_phase3) = Some g3
    /\ sw_gamma \in ps_cipher (g3 alice)
    /\ ps_priv (g3 alice) = Some dk_alice
    /\ ps_ret (g3 alice) = None.
Proof.
rewrite /dsdp_n_phase3.
have H1le : (1 <= n_relay)%N by rewrite Hnr.
have [gf [Hgf [Hbeta [Hforall [Halpha_pres [Halice Hret]]]]]] := dsdp_n_first_relay_eq H1le.
have Hint : dsdp_n_intermediate_indices = [::].
  rewrite /dsdp_n_intermediate_indices.
  apply/eqP; rewrite -size_eq0 size_filter.
  rewrite Hnr.
  by rewrite enum_ordSl enum_ordSl enum_ord0 /=.
have -> : flatten [seq dsdp_n_intermediate j | j <- dsdp_n_intermediate_indices]
        = [::] by rewrite Hint.
rewrite cat0s.
rewrite [in X in foldM _ _ X]catA [in X in foldM _ _ X]catA
        [in X in foldM _ _ X]catA.
rewrite foldM_cat.
rewrite !catA in Hgf.
rewrite Hgf /=.
(* At n_relay = 1, the concrete ordinal (Ordinal H1le) coincides with
   ord_max. We rewrite Hbeta to refer to ord_max so it matches the
   phase3 last-relay block. *)
have Hmax_val : val (@ord_max n_relay) = 1%N by rewrite /= Hnr.
have HRn : R n_relay = 2 by rewrite /R Hnr.
have Ha1_ordmax : Ordinal (H1le : (1 < n_relay.+1)%N) = @ord_max n_relay.
  by apply: val_inj; rewrite /= Hnr.
rewrite Ha1_ordmax in Hbeta.
have Hp_Rn : ps_priv (gf (R n_relay)) = Some (dk ord_max).
  have := Hforall ord_max.
  by rewrite /=.
have Hbeta' : sw_beta ord0 ord_max \in ps_cipher (gf (R n_relay)).
  by move: Hbeta; rewrite /=.
have Hpred_om : ord_predS (@ord_max n_relay) = ord0.
  by apply: val_inj; rewrite /ord_predS /= Hnr /= inordK // Hnr.
rewrite Hpred_om Hbeta' Hp_Rn /= dec_sw_beta /=.
have Hgamma_eq : sw_gamma = enc (sw_pk_of ord0) (sw_Delta ord_max) r_tail by [].
rewrite -Hgamma_eq.
have HgammaIn : sw_gamma \in sw_gamma |` ps_cipher (gf (R n_relay))
  by apply/fset1UP; left.
(* The inner check fires at (R n_relay) on the sw_upd'd state after the ASend;
   we supply Hin directly. *)
have Hin : sw_gamma \in ps_cipher
  (sw_upd
     (sw_upd gf (R n_relay)
        (sw_add_plain (gf (R n_relay))
           (u (lift ord0 ord_max) * v ord_max + r ord_max + sw_Delta ord0)))
     (R n_relay)
     (sw_add_cipher
        (sw_upd gf (R n_relay)
           (sw_add_plain (gf (R n_relay))
              (u (lift ord0 ord_max) * v ord_max + r ord_max + sw_Delta ord0))
           (R n_relay)) sw_gamma) (R n_relay)).
  rewrite /sw_upd eqxx /sw_add_cipher /=.
  by apply/fset1UP; left.
rewrite Hin /=.
eexists; split; first by reflexivity.
split.
  rewrite /sw_upd eqxx /sw_add_cipher /=.
  by apply/fset1UP; left.
split.
  rewrite /sw_upd eqxx /sw_add_cipher /=.
  rewrite /sw_upd /=.
  by rewrite Halice.
rewrite /sw_upd eqxx /sw_add_cipher /=.
rewrite /sw_upd /=.
by rewrite Hret.
Qed.

(* === L8: phase 4 postcondition =========================================== *)

(* Main (L8): after phase0..phase4, alice's [ps_ret] is [Some sw_S].
   Composes [dsdp_n_beta_chain_eq] (which puts [sw_gamma] in alice's
   cipher set) with the four phase4 actions: ADec [sw_gamma] to extract
   [sw_Delta ord_max], two AAdds to form [sw_S = sw_Delta ord_max + u_1
   * v_1 - \sum r], and ARet. *)
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

(* Main (L9): the algebraic identity at the heart of DSDP correctness.
   [sw_S] is defined as [sw_Delta ord_max - \sum r + u ord0 * v_alice];
   [sw_Delta ord_max = \sum_k (u_{k+1} * v_k + r_k)]; so [sw_S] telescopes
   to [\sum_(i < n_relay.+2) u i * v_all i], which is the dot product.
   Pure ring algebra; independent of [sw_step] and of [n_relay = 1]. *)
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

(* Main (TH1, headline theorem): running the whole [dsdp_n_program]
   from [sw_init_state] via [foldM sw_step] succeeds, and the return
   value alice emits is exactly the dot product [\sum_i u_i * v_i].
   One-line corollary composing [dsdp_n_phase4_state] (final state has
   [ps_ret alice = Some sw_S]) with [sw_S_eq_dot_product]. Restricted
   to [n_relay = 1] by the same [party_id] 4-constructor finiteness
   argument flagged in L7's comment. *)
Theorem dsdp_n_correct (Hnr : n_relay = 1%N) :
  exists gf, dsdp_n_final = Some gf
           /\ ret_of gf alice = Some (\sum_(i < n_relay.+2) u i * v_all i).
Proof.
have [gf [Hf Hret]] := dsdp_n_phase4_state Hnr.
exists gf; split=> //.
by rewrite /ret_of Hret sw_S_eq_dot_product.
Qed.

End dsdp_stepwise.
