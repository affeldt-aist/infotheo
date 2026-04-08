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

Definition sw_step (p : party_id) (a : dsdp_action) (g : sw_global_state)
    : option sw_global_state :=
  let s := g p in
  match a with
  | AInit vi dki =>
      Some (sw_upd g p (sw_set_priv (sw_add_plain s vi) dki))
  | AEnc pk m rd =>
      if m \in ps_plain s
      then Some (sw_upd g p (sw_add_cipher s (enc pk m rd)))
      else None
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
      if (c \in ps_cipher s) && (x \in ps_plain s)
      then Some (sw_upd g p (sw_add_cipher s (c ^h x)))
      else None
  | AAdd a1 b1 =>
      if (a1 \in ps_plain s) && (b1 \in ps_plain s)
      then Some (sw_upd g p (sw_add_plain s (a1 + b1)))
      else None
  | ASend dst c =>
      if c \in ps_cipher s
      then Some (sw_upd g dst (sw_add_cipher (g dst) c))
      else None
  | ARet x =>
      if (ps_ret s == None) && (x \in ps_plain s)
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
    [seq let dest := R (alice_send_dest (val j)) in
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
Definition dsdp_n_first_relay : seq (party_id * dsdp_action) :=
  let p1 := R 0 in
  match (insub 1 : option 'I_n_relay.+1) with
  | Some j1 =>
    [:: (p1, AMul (sw_alpha ord0) (sw_alpha j1))
      ; (p1, ADec (sw_alpha ord0 *h sw_alpha j1) (dk ord0))
      ; (p1, AEnc (sw_pk_of (lift ord0 j1)) (sw_Delta ord0) (rb2 ord0))
      ; (p1, ASend (R 1) (sw_beta ord0 j1))]
  | None => [::]
  end.

(* For an intermediate relay j (with 0 < j < n_relay), it receives
   sw_beta (ord_predS j) j on its cipher set, decrypts, and produces
   sw_Delta j and sw_beta j (lift ord0 j) which it forwards. *)
Definition dsdp_n_intermediate (j : 'I_n_relay.+1) : seq (party_id * dsdp_action) :=
  match (insub (val j).+1 : option 'I_n_relay.+1) with
  | Some jnext =>
    [:: (R (val j), AMul (sw_beta (ord_predS j) j) (sw_alpha j))
      ; (R (val j), ADec (sw_beta (ord_predS j) j *h sw_alpha j) (dk j))
      ; (R (val j), AEnc (sw_pk_of (lift ord0 jnext)) (sw_Delta j) (rb2 j))
      ; (R (val j), ASend (R (val j).+1) (sw_beta j jnext))]
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
  m \in ps_plain (g p) ->
  sw_step p (AEnc pk m rd) g
  = Some (sw_upd g p (sw_add_cipher (g p) (enc pk m rd))).
Proof. by move=> H; rewrite /sw_step H. Qed.

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
  x \in ps_plain (g p) ->
  sw_step p (APow c x) g
  = Some (sw_upd g p (sw_add_cipher (g p) (c ^h x))).
Proof. by move=> H1 H2; rewrite /sw_step H1 H2. Qed.

Lemma sw_step_AAdd_eq p a1 b1 g :
  a1 \in ps_plain (g p) ->
  b1 \in ps_plain (g p) ->
  sw_step p (AAdd a1 b1) g
  = Some (sw_upd g p (sw_add_plain (g p) (a1 + b1))).
Proof. by move=> H1 H2; rewrite /sw_step H1 H2. Qed.

Lemma sw_step_ASend_eq p dst c g :
  c \in ps_cipher (g p) ->
  sw_step p (ASend dst c) g
  = Some (sw_upd g dst (sw_add_cipher (g dst) c)).
Proof. by move=> H; rewrite /sw_step H. Qed.

Lemma sw_step_ARet_eq p x g :
  ps_ret (g p) = None ->
  x \in ps_plain (g p) ->
  sw_step p (ARet x) g
  = Some (sw_upd g p (sw_set_ret (g p) x)).
Proof. by move=> H1 H2; rewrite /sw_step /= H1 /= H2. Qed.

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

Lemma dsdp_n_phase1_state :
  exists g1, foldM (fun g pa => sw_step pa.1 pa.2 g) sw_init_state
                   (dsdp_n_phase0 ++ dsdp_n_phase1) = Some g1.
Proof.
(* phase0 produces a state where each v j is in ps_plain of R (val j), and
   phase1 then advances through AEnc/ASend pairs, each of whose preconditions
   is maintained by the invariant. *)
have phase0_loop : forall (l : seq 'I_n_relay.+1) (g : sw_global_state),
  exists g', foldM (fun g pa => sw_step pa.1 pa.2 g) g
    [seq (R (val j), AInit (v j) (dk j)) | j <- l] = Some g' /\
    (forall j, j \in l -> v j \in ps_plain (g' (R (val j)))) /\
    (forall p m, m \in ps_plain (g p) -> m \in ps_plain (g' p)).
  elim=> [|j l IH] g /=; first by exists g; split=> //; split=> // j0; rewrite in_nil.
  set g1 := sw_upd g (R (val j)) _.
  have {IH} [g' [-> [Hin Hmg]]] := IH g1.
  exists g'; split=> //; split.
    move=> k; rewrite in_cons => /orP [/eqP ->|Hk]; last exact: Hin.
    apply: Hmg; rewrite /g1 /sw_upd eqxx /= /sw_set_priv /sw_add_plain /=.
    exact: fset1U1.
  move=> p m Hm; apply: Hmg.
  rewrite /g1 /sw_upd.
  case E: (p == R (val j)); last exact: Hm.
  have {Hm} : m \in ps_plain (g (R (val j))) by move/eqP: E => <-.
  move=> Hm; rewrite /sw_set_priv /sw_add_plain /=.
  by rewrite inE Hm orbT.
have phase1_loop : forall (l : seq 'I_n_relay.+1) (g : sw_global_state),
  (forall j, j \in l -> v j \in ps_plain (g (R (val j)))) ->
  exists g', foldM (fun g pa => sw_step pa.1 pa.2 g) g
    (flatten [seq [:: (R (val j), AEnc (sw_pk_of (lift ord0 j)) (v j) (rb1 j))
                   ; (R (val j), ASend alice (sw_c j))] | j <- l]) = Some g'.
  elim=> [|j l IH] g Hall /=; first by exists g.
  have Hj : v j \in ps_plain (g (R (val j))) by apply: Hall; rewrite mem_head.
  rewrite /sw_step Hj /=.
  set g1 := sw_upd g (R (val j)) _.
  have Hc : sw_c j \in ps_cipher (g1 (R (val j))).
    rewrite /g1 /sw_upd eqxx /sw_add_cipher /sw_c /=.
    by apply/fset1UP; left.
  rewrite Hc /=.
  set g2 := sw_upd g1 alice _.
  apply: IH => k Hk.
  rewrite /g2 /sw_upd.
  case E1: (R (val k) == alice).
    rewrite /sw_add_cipher /=.
    move/eqP: E1 => <-.
    rewrite /g1 /sw_upd.
    case E3: (R (val k) == R (val j)).
      rewrite /sw_add_cipher /=.
      have Hv : v k \in ps_plain (g (R (val k)))
        by apply: Hall; rewrite in_cons Hk orbT.
      by rewrite -(eqP E3).
    by apply: Hall; rewrite in_cons Hk orbT.
  rewrite /g1 /sw_upd.
  case E2: (R (val k) == R (val j)).
    rewrite /sw_add_cipher /=.
    rewrite -(eqP E2).
    by apply: Hall; rewrite in_cons Hk orbT.
  by apply: Hall; rewrite in_cons Hk orbT.
rewrite foldM_cat /dsdp_n_phase0 /=.
set g_a := sw_upd sw_init_state alice _.
have [g0' [-> [Hin _]]] := phase0_loop (enum 'I_n_relay.+1) g_a.
rewrite /dsdp_n_phase1.
apply: phase1_loop => k _.
by apply: Hin; rewrite mem_enum.
Qed.

Lemma dsdp_n_phase2_state :
  exists g2, foldM (fun g pa => sw_step pa.1 pa.2 g) sw_init_state
                   (dsdp_n_phase0 ++ dsdp_n_phase1 ++ dsdp_n_phase2)
             = Some g2.
Proof. Admitted.

Lemma dsdp_n_first_relay_eq :
  exists gf, foldM (fun g pa => sw_step pa.1 pa.2 g) sw_init_state
                   (dsdp_n_phase0 ++ dsdp_n_phase1 ++ dsdp_n_phase2
                                  ++ dsdp_n_first_relay) = Some gf.
Proof. Admitted.

Lemma dsdp_n_intermediate_telescope (j : 'I_n_relay.+1) :
  (0 < val j < n_relay)%N ->
  True.  (* Placeholder: real statement requires the pre-state predicate
            from the inductive hypothesis; spelled out in Phase 4. *)
Proof. Admitted.

Lemma dsdp_n_beta_chain_eq :
  exists g3, foldM (fun g pa => sw_step pa.1 pa.2 g) sw_init_state
                   (dsdp_n_phase0 ++ dsdp_n_phase1 ++ dsdp_n_phase2
                                  ++ dsdp_n_phase3) = Some g3.
Proof. Admitted.

(* === L8: phase 4 postcondition =========================================== *)

Lemma dsdp_n_phase4_state :
  exists gf, dsdp_n_final = Some gf /\ ps_ret (gf alice) = Some sw_S.
Proof. Admitted.

(* === L9: algebraic identity ============================================== *)

Lemma sw_S_eq_dot_product :
  sw_S = \sum_(i < n_relay.+2) u i * v_all i.
Proof. Admitted.

(* === TH1: headline correctness =========================================== *)

Theorem dsdp_n_correct :
  exists gf, dsdp_n_final = Some gf
           /\ ret_of gf alice = Some (\sum_(i < n_relay.+2) u i * v_all i).
Proof. Admitted.

End dsdp_stepwise.
