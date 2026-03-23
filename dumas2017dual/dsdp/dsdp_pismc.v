From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import smc_interpreter pismc.
Require Import smc_session_types homomorphic_encryption.
Require Import dsdp_interface dsdp_session_types dsdp_program.
Require Import idealized_ahe.  (* For computational termination proofs *)

Local Open Scope pismc_scope.
Local Open Scope ring_scope.

Section smc_dsdp_program.

(* Parameterize by an AHEncType instance *)
Variable AHE : AHEncType.

(* Use standard DSDP interface for data types *)
Let DI := Standard_DSDP_Interface AHE.

(* Extract types from the scheme *)
Let msgT := plain AHE.
Let randT := rand AHE.
Let encT := cipher AHE.
Let priv_keyT := priv_key AHE.
Let pub_keyT := pub_key AHE.

(* Data type and constructors from interface *)
Let data := di_data DI.
Let d := di_d DI.
Let e := di_e DI.
Let priv_key := di_priv_key DI.

(* HE operations from the scheme - using @ to provide scheme explicitly *)
Let Emul := @Emul AHE.
Let Epow := @Epow AHE.

Notation "u *h w" := (Emul u w).
Notation "u ^h w" := (Epow u w).

(* Party identities *)
Variable alice : party_id.
Variable bob : party_id.
Variable charlie : party_id.

(* Concrete party indices for session type tracking *)
(* These must be distinct for duality verification to work with native_compute *)
Definition alice_idx : nat := 0.
Definition bob_idx : nat := 1.
Definition charlie_idx : nat := 2.

Coercion nat_to_party_id : nat >-> party_id.

(* Make dtype and data explicit for sproc type annotations *)
Arguments sproc dtype data party {_} {_}.

(* Use session-typed wrappers from dsdp_interface directly *)
Let PSend {party n env} := @DSend AHE party n env.
Let Recv_dec {party n env} := @DRecv_dec AHE party n env.
Let Recv_enc {party n env} := @DRecv_enc AHE party n env.

(** * Data wrapper shorthand notations *)

(* #x -> (priv_key x) for private key *)
Local Notation "# x" := (priv_key x) (at level 0, x at level 0) : pismc_scope.
(* &x -> (d x) for data/message *)
Local Notation "& x" := (d x) (at level 0, x at level 0) : pismc_scope.
(* $x -> (e x) for encrypted *)
Local Notation "$ x" := (e x) (at level 0, x at level 0) : pismc_scope.

(* Finish, Init, and generic Ret notations are shared from pismc.v.
   Data wrapper notations (#, &, $) are parsed in constr scope
   within the shared Init/Ret notations. *)

Notation "'Send<' p '>' x ; P" := (PSend p x P)
  (in custom pismc at level 85, p constr at level 0, x constr at level 0,
   P custom pismc at level 85, right associativity).

(* Protocol-specific Recv notations *)
Local Notation "'Recv<' p '>' x '=>' P" :=
  (Recv_enc p (fun x => P))
  (in custom pismc at level 85, p constr at level 0, x name,
   P custom pismc at level 85, right associativity).

Notation "'Recv<' p '>' '#' dk x '=>' P" :=
  (Recv_dec p dk (fun x => P))
  (in custom pismc at level 85, p constr at level 0,
   dk constr at level 0, x name,
   P custom pismc at level 85, right associativity).

(******************************************************************************)
(** * DSDP Protocol Programs with Session Type Tracking                       *)
(** * Each encryption E(party, msg, rand) needs explicit randomness.          *)
(******************************************************************************)

(* Public key mapping: each party has an associated public key *)
Variable ek : party_id -> pub_key AHE.

(* Party-indexed encryption: maps party to their public key for enc *)
Definition enc_pub_key (p : party_id) (m : msgT) (r : randT) : encT :=
  enc (ek p) m r.
Local Notation "'E<' r '>' p m" := (enc_pub_key p m r)
  (at level 10, r constr at level 0, p constr at level 0, m constr at level 0,
   format "'E<' r '>'  p  m").

(* Bob's protocol - using concrete indices for session type duality *)
Definition pbob (dk : priv_keyT)(v2 : msgT)(rb1 rb2 : randT)
    : sproc dsdp_dtype data bob_idx :=
  \pi{ Init (#dk, &v2) ;
     Send<alice_idx> $(E<rb1> bob_idx v2);
     Recv<alice_idx> #dk d2 =>
     Recv<alice_idx> a3 =>
     Send<charlie_idx> $(a3 *h (E<rb2> charlie_idx d2)) ;
     Finish }.

(* Charlie's protocol *)
Definition pcharlie (dk : priv_keyT)(v3 : msgT)(rc1 rc2 : randT)
    : sproc dsdp_dtype data charlie_idx :=
  \pi{ Init (#dk, &v3) ;
     Send<alice_idx> $(E<rc1> charlie_idx v3) ;
     Recv<bob_idx> #dk d3 =>
     Send<alice_idx> $(E<rc2> alice_idx d3) ;
     Finish }.

(* Alice's protocol *)
Definition palice (dk : priv_keyT)(v1 u1 u2 u3 r2 r3: msgT)(ra1 ra2 : randT)
    : sproc dsdp_dtype data alice_idx :=
  \pi{ Init (#dk, &v1, &u1, &u2, &u3, &r2, &r3) ;
     Recv<bob_idx> c2 =>
     Recv<charlie_idx> c3 =>
     Send<bob_idx> $(c2 ^h u2 *h (E<ra1> bob_idx r2)) ;
     Send<bob_idx> $(c3 ^h u3 *h (E<ra2> charlie_idx r3)) ;
     Recv<charlie_idx> #dk g =>
     Ret &(g - r2 - r3 + u1 * v1) }.


(******************************************************************************)
(** * Cross-equality with dsdp_program                                        *)
(** * Proves that piSMC programs equal the original dsdp_program definitions  *)
(******************************************************************************)

(* Party-to-nat mapping and hypotheses relating it to concrete indices.
   DSDP uses abstract party_id variables. We need hypotheses to connect
   pn with concrete indices. *)
Variable pn : party_id -> nat.
Hypothesis pn_alice : pn alice = alice_idx.
Hypothesis pn_bob : pn bob = bob_idx.
Hypothesis pn_charlie : pn charlie = charlie_idx.
Hypothesis np_alice : nat_to_party_id alice_idx = alice.
Hypothesis np_bob : nat_to_party_id bob_idx = bob.
Hypothesis np_charlie : nat_to_party_id charlie_idx = charlie.

(* Import original programs from dsdp_program *)
Let palice_orig := @dsdp_program.palice AHE bob charlie pn ek.
Let pbob_orig := @dsdp_program.pbob AHE alice bob charlie pn ek.
Let pcharlie_orig := @dsdp_program.pcharlie AHE alice bob charlie pn ek.

(* Cross-equality proofs on erased processes (proc, not sproc).
   The sproc types differ in session env indices, but erased procs are equal
   when pn maps parties to the expected concrete indices. *)
Lemma alice_cross_eq dk' v1' u1' u2' u3' r2' r3' ra1' ra2' :
  erase (palice dk' v1' u1' u2' u3' r2' r3' ra1' ra2') =
  erase (palice_orig dk' v1' u1' u2' u3' r2' r3' ra1' ra2').
Proof.
by rewrite /palice /palice_orig /dsdp_program.palice pn_bob pn_charlie
           /enc_pub_key /dsdp_program.enc_pk np_bob np_charlie.
Qed.

Lemma bob_cross_eq dk' v2' rb1' rb2' :
  erase (pbob dk' v2' rb1' rb2') =
  erase (pbob_orig dk' v2' rb1' rb2').
Proof.
by rewrite /pbob /pbob_orig /dsdp_program.pbob pn_alice pn_charlie
           /enc_pub_key /dsdp_program.enc_pk np_bob np_charlie.
Qed.

Lemma charlie_cross_eq dk' v3' rc1' rc2' :
  erase (pcharlie dk' v3' rc1' rc2') =
  erase (pcharlie_orig dk' v3' rc1' rc2').
Proof.
by rewrite /pcharlie /pcharlie_orig /dsdp_program.pcharlie pn_alice pn_bob
           /enc_pub_key /dsdp_program.enc_pk np_alice np_charlie.
Qed.

(******************************************************************************)
(** * Session Type Duality Verification                                       *)
(******************************************************************************)

Variables (dk : priv_keyT) (v1 u1 u2 u3 r2 r3 v2 v3 : msgT)
(ra1 ra2 rb1 rb2 rc1 rc2 : randT).

(* Wrap in aproc for duality checking *)
Definition aproc_alice := mk_aproc (palice dk v1 u1 u2 u3 r2 r3 ra1 ra2).
Definition aproc_bob := mk_aproc (pbob dk v2 rb1 rb2).
Definition aproc_charlie := mk_aproc (pcharlie dk v3 rc1 rc2).

(* Three-party duality verification *)
Lemma alice_bob_dual : channels_dual aproc_alice aproc_bob.
Proof.
by native_compute.
Qed.

Lemma alice_charlie_dual : channels_dual aproc_alice aproc_charlie.
Proof.
by native_compute.
Qed.

Lemma bob_charlie_dual : channels_dual aproc_bob aproc_charlie.
Proof.
by native_compute.
Qed.

(******************************************************************************)
(** * N-Party Protocol Templates (from Algorithm 2)                           *)
(******************************************************************************)

(* P₂: first relay party — recv_dec + recv_enc from P₁ *)
Definition DParty_first (self downstream : nat)
    (dk : priv_keyT) (v : msgT) (r1 r2 : randT)
    : sproc dsdp_dtype data self :=
  \pi{ Init (#dk, &v) ;
       Send<alice_idx> $(E<r1> self v) ;
       Recv<alice_idx> #dk d_val =>
       Recv<alice_idx> a_next =>
       Send<downstream> $(a_next *h (E<r2> downstream d_val)) ;
       Finish }.

(* Pᵢ (3≤i≤n-1): intermediate relay — recv_enc from P₁ + recv_dec from upstream *)
Definition DParty_intermediate (self alice_src upstream downstream : nat)
    (dk : priv_keyT) (v : msgT) (r1 r2 : randT)
    : sproc dsdp_dtype data self :=
  \pi{ Init (#dk, &v) ;
       Send<alice_src> $(E<r1> self v) ;
       Recv<alice_src> a_next =>
       Recv<upstream> #dk d_val =>
       Send<downstream> $(a_next *h (E<r2> downstream d_val)) ;
       Finish }.

(* Pₙ: last party — recv_dec from upstream, re-encrypt, send to P₁ *)
Definition DParty_last (self upstream : nat)
    (dk : priv_keyT) (v : msgT) (r1 r2 : randT)
    : sproc dsdp_dtype data self :=
  \pi{ Init (#dk, &v) ;
       Send<alice_idx> $(E<r1> self v) ;
       Recv<upstream> #dk d_val =>
       Send<alice_idx> $(E<r2> alice_idx d_val) ;
       Finish }.

(* Cross-equality: existing 3-party definitions are instances of templates *)
Lemma pbob_is_first dk' v2' rb1' rb2' :
  pbob dk' v2' rb1' rb2' =
  DParty_first bob_idx charlie_idx dk' v2' rb1' rb2'.
Proof. reflexivity. Qed.

Lemma pcharlie_is_last dk' v3' rc1' rc2' :
  pcharlie dk' v3' rc1' rc2' =
  DParty_last charlie_idx bob_idx dk' v3' rc1' rc2'.
Proof. reflexivity. Qed.

(* Duality verification on templated protocols *)
Definition aproc_bob_tmpl :=
  mk_aproc (DParty_first bob_idx charlie_idx dk v2 rb1 rb2).
Definition aproc_charlie_tmpl :=
  mk_aproc (DParty_last charlie_idx bob_idx dk v3 rc1 rc2).

Lemma alice_bob_tmpl_dual : channels_dual aproc_alice aproc_bob_tmpl.
Proof. by native_compute. Qed.

Lemma alice_charlie_tmpl_dual : channels_dual aproc_alice aproc_charlie_tmpl.
Proof. by native_compute. Qed.

Lemma bob_charlie_tmpl_dual : channels_dual aproc_bob_tmpl aproc_charlie_tmpl.
Proof. by native_compute. Qed.

(******************************************************************************)
(** * N-Party Alice Protocol                                                  *)
(******************************************************************************)

Section dsdp_n_party.

Variable n_relay : nat.

(* Destination for Alice's i-th send: relays 0 and 1 both go to party 1
   (first relay receives two messages), relay j >= 2 goes to party j *)
Definition alice_send_dest (j : nat) : nat := maxn 1 j.

(* N-party Alice using sproc_iter for the interleaved recv/send loop.
   n = n_relay.+2 total parties: Alice (party 0) + n_relay.+1 relays.
   For each relay j, Alice receives encrypted v_{j+1} from party j+1,
   computes a_j = c_j^{u_{j+1}} * E(party_{j+1}, r_j, rand_j),
   and sends a_j to dest(j). Finally receives the accumulated result
   from the last relay and computes the dot product. *)
Let alice_env_step (j : 'I_n_relay.+1) (env : senv dsdp_dtype) :=
  senv_recv (senv_send env (alice_send_dest j) DT_Enc) j.+1 DT_Enc.

Definition palice_n
    (relays : seq 'I_n_relay.+1)
    (dk : priv_keyT) (v0 : msgT)
    (u : 'I_n_relay.+2 -> msgT)
    (r : 'I_n_relay.+1 -> msgT)
    (rand_a : 'I_n_relay.+1 -> randT)
    : sproc dsdp_dtype data alice_idx :=
  \pi{ Init (#dk, &v0) ;
     ForList relays step (fun k => k.+2) enstep alice_env_step as j cont k =>
       Recv<(j.+1)> c =>
       Send<(alice_send_dest j)>
         $(c ^h (u (lift ord0 j)) *h (enc_pub_key j.+1 (r j) (rand_a j))) ;
       k
     end ;
     Recv<(n_relay.+1)> #dk g =>
     Ret &(g - \sum_(j < n_relay.+1) r j + u ord0 * v0) }.

(* Map relay index j to the appropriate relay template (first/intermediate/last).
   Requires n_relay >= 1 (at least 3 parties). *)
Definition relay_aproc (j : nat)
    (dk_j : priv_keyT) (v_j : msgT) (r1_j r2_j : randT)
    : aproc dsdp_dtype data :=
  if j == 0 then
    mk_aproc (DParty_first j.+1 j.+2 dk_j v_j r1_j r2_j)
  else if j == n_relay then
    mk_aproc (DParty_last j.+1 j dk_j v_j r1_j r2_j)
  else
    mk_aproc (DParty_intermediate j.+1 alice_idx j j.+2 dk_j v_j r1_j r2_j).

(* Build the full N-party aproc list: Alice + n_relay.+1 relay parties.
   Assumes n_relay >= 1 (at least 3 total parties). *)
Definition dsdp_n_saprocs
    (relays : seq 'I_n_relay.+1)
    (dk : priv_keyT) (v0 : msgT)
    (u : 'I_n_relay.+2 -> msgT) (r : 'I_n_relay.+1 -> msgT)
    (rand_a : 'I_n_relay.+1 -> randT)
    (dk_relay : 'I_n_relay.+1 -> priv_keyT)
    (v_relay : 'I_n_relay.+1 -> msgT)
    (r1_relay r2_relay : 'I_n_relay.+1 -> randT)
    : seq (aproc dsdp_dtype data) :=
  mk_aproc (palice_n relays dk v0 u r rand_a) ::
  map (fun j : 'I_n_relay.+1 =>
    relay_aproc j (dk_relay j) (v_relay j) (r1_relay j) (r2_relay j))
    relays.

Definition dsdp_n_procs
    (relays : seq 'I_n_relay.+1)
    (dk : priv_keyT) (v0 : msgT)
    (u : 'I_n_relay.+2 -> msgT) (r : 'I_n_relay.+1 -> msgT)
    (rand_a : 'I_n_relay.+1 -> randT)
    (dk_relay : 'I_n_relay.+1 -> priv_keyT)
    (v_relay : 'I_n_relay.+1 -> msgT)
    (r1_relay r2_relay : 'I_n_relay.+1 -> randT)
    : seq (proc data) :=
  erase_aprocs (dsdp_n_saprocs relays dk v0 u r rand_a dk_relay v_relay r1_relay r2_relay).

End dsdp_n_party.

(*******************************************************************************)
(** * Interpreter Integration                                                  *)
(*******************************************************************************)

Local Open Scope sproc_scope.
Local Open Scope proc_scope.

(* Session-typed processes for duality checking and fuel computation *)
Definition dsdp_saprocs : seq (aproc dsdp_dtype data) :=
  [aprocs palice dk v1 u1 u2 u3 r2 r3 ra1 ra2; pbob dk v2 rb1 rb2; pcharlie dk v3 rc1 rc2].

(* Erased processes for interpreter (strips session type indices) *)
Definition dsdp_procs : seq (proc data) :=
  erase_aprocs dsdp_saprocs.

(* Fuel bound computed from program structure:
   - palice: 15 (7*Init + 2*Recv_enc + 2*Send + Recv_dec + Ret=2)
   - pbob: 7 (2*Init + Send + Recv_dec + Recv_enc + Send + Finish=1)
   - pcharlie: 6 (2*Init + Send + Recv_dec + Send + Finish=1)
   Total: 15 + 7 + 6 = 28, but actually computed as 27 *)
Lemma dsdp_max_fuel_ok : [> dsdp_saprocs] = 27.
Proof. reflexivity. Qed.

End smc_dsdp_program.

(*******************************************************************************)
(** * Session Environment Convergence for DSDP (Idealized Instance)            *)
(*******************************************************************************)

(* This section instantiates DSDP with the Idealized AHEncType, where
   enc/dec have concrete computable definitions. This enables native_compute
   proofs for termination properties. *)

Section dsdp_idealized_termination.

Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Local Notation msg := 'F_m.

(* Build the Idealized AHEncType *)
Local Definition Idealized_EncDec_instance :=
  @Idealized_isEncDec msg.

Local Definition Idealized_AHEnc_instance :=
  @Idealized_isAHEnc msg.

Local Definition Idealized_EncDec_local : EncDecType :=
  @EncDec.Pack (Idealized_HETypes msg)
    (@EncDec.Class (Idealized_HETypes msg) Idealized_EncDec_instance).

Local Definition Idealized_AHEnc_local : AHEncType :=
  @AHEnc.Pack (Idealized_HETypes msg)
    (@AHEnc.Class (Idealized_HETypes msg)
      Idealized_EncDec_instance Idealized_AHEnc_instance).

Let AHE : AHEncType := Idealized_AHEnc_local.
Let DI := Standard_DSDP_Interface AHE.
Let data := di_data DI.

(* Party definitions *)
Let alice : party_id := Alice.
Let bob : party_id := Bob.
Let charlie : party_id := Charlie.
Let pn : party_id -> nat := party_id_to_nat.

(* Program variables *)
Variables (k_a k_b k_c v1 v2 v3 u1 u2 u3 r2 r3 : msg).
Let runit : rand AHE := 1.

(* Private keys are just msg values in idealized *)
Let dk_a : priv_key AHE := k_a.
Let dk_b : priv_key AHE := k_b.
Let dk_c : priv_key AHE := k_c.

(* Public keys derived from private keys via pub_of_priv *)
Let ek (p : party_id) : pub_key AHE :=
  match p with
  | Alice => pub_of_priv dk_a
  | Bob => pub_of_priv dk_b
  | Charlie => pub_of_priv dk_c
  | NoParty => pub_of_priv dk_a
  end.

(* Instantiate programs from dsdp_program.v *)
Let palice_inst :=
  @dsdp_program.palice AHE bob charlie pn ek dk_a v1 u1 u2 u3 r2 r3 runit runit.
Let pbob_inst :=
  @dsdp_program.pbob AHE alice bob charlie pn ek dk_b v2 runit runit.
Let pcharlie_inst :=
  @dsdp_program.pcharlie AHE alice bob charlie pn ek dk_c v3 runit runit.

Local Open Scope sproc_scope.
Local Open Scope proc_scope.

(* Session-typed processes *)
Definition dsdp_ideal_saprocs : seq (aproc dsdp_dtype data) :=
  [aprocs palice_inst; pbob_inst; pcharlie_inst].

Definition dsdp_ideal_procs : seq (proc data) :=
  erase_aprocs dsdp_ideal_saprocs.

(* Fuel bound *)
Lemma dsdp_ideal_max_fuel_ok : [> dsdp_ideal_saprocs] = 27.
Proof. reflexivity. Qed.

(* DSDP (Idealized): after interpretation, all processes are terminal. *)
Lemma dsdp_ideal_terminates traces :
  all_terminated (interp [> dsdp_ideal_saprocs] dsdp_ideal_procs traces).1.
Proof. by native_compute. Qed.

(* DSDP (Idealized): after interpretation, no process is Fail. *)
Lemma dsdp_ideal_no_fail traces :
  all_nonfail (interp [> dsdp_ideal_saprocs] dsdp_ideal_procs traces).1.
Proof. by native_compute. Qed.

(* Main theorem: DSDP (Idealized) session environment converges to empty. *)
Theorem dsdp_ideal_senv_zero traces :
  exists aps' : seq (aproc dsdp_dtype data),
    erase_aprocs aps' =
      (interp [> dsdp_ideal_saprocs] dsdp_ideal_procs traces).1 /\
    aprocs_senv_depth [:: 0; 1; 2] aps' = 0.
Proof.
have [aps' [Hsz [Herase Hsenv]]] :=
  @senv_bounded _ _ [:: 0; 1; 2] [> dsdp_ideal_saprocs]
    dsdp_ideal_saprocs traces (leqnn _).
exists aps'.
split; first exact: Herase.
apply: terminated_nonfail_senv_zero.
- by rewrite Herase; exact: dsdp_ideal_terminates.
- by rewrite Herase; exact: dsdp_ideal_no_fail.
Qed.

End dsdp_idealized_termination.

(*******************************************************************************)
(** * N-Party Session Type Duality Verification (Idealized, 4-party)           *)
(*******************************************************************************)

Section dsdp_n4_idealized_duality.

Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Local Notation msg := 'F_m.

(* Idealized AHE setup *)
Local Definition N4_EncDec_instance :=
  @Idealized_isEncDec msg.

Local Definition N4_AHEnc_instance :=
  @Idealized_isAHEnc msg.

Local Definition N4_EncDec_local : EncDecType :=
  @EncDec.Pack (Idealized_HETypes msg)
    (@EncDec.Class (Idealized_HETypes msg) N4_EncDec_instance).

Local Definition N4_AHEnc_local : AHEncType :=
  @AHEnc.Pack (Idealized_HETypes msg)
    (@AHEnc.Class (Idealized_HETypes msg)
      N4_EncDec_instance N4_AHEnc_instance).

Let AHE : AHEncType := N4_AHEnc_local.
Let DI := Standard_DSDP_Interface AHE.
Let data := di_data DI.

(* Party keys *)
Variables (k0 k1 k2 k3 : msg).
Let dk0 : priv_key AHE := k0.
Let dk1 : priv_key AHE := k1.
Let dk2 : priv_key AHE := k2.
Let dk3 : priv_key AHE := k3.
Let runit : rand AHE := 1.

(* Public key mapping for 4 parties (party 3 = NoParty) *)
Let ek4 (p : party_id) : pub_key AHE :=
  match p with
  | Alice => pub_of_priv dk0
  | Bob => pub_of_priv dk1
  | Charlie => pub_of_priv dk2
  | NoParty => pub_of_priv dk3
  end.

(* Program variables *)
Variables (v0 v1 v2 v3 : msg).
Variables (u0' u1' u2' u3' : msg).
Variables (r0' r1' r2' : msg).

(* Index functions for palice_n *)
Let u4 : 'I_4 -> msg := fun i =>
  match val i with 0 => u0' | 1 => u1' | 2 => u2' | _ => u3' end.
Let r4_3 : 'I_3 -> msg := fun i =>
  match val i with 0 => r0' | 1 => r1' | _ => r2' end.
Let rand4_3 : 'I_3 -> rand AHE := fun _ => runit.

(* 4-party programs: Alice + first relay + intermediate + last relay *)
Let palice_4 := @palice_n AHE ek4 2
  [:: @Ordinal 3 0 isT; @Ordinal 3 1 isT; @Ordinal 3 2 isT]
  dk0 v0 u4 r4_3 rand4_3.
Let pfirst_4 := @DParty_first AHE ek4 1 2 dk1 v1 runit runit.
Let pinter_4 := @DParty_intermediate AHE ek4 2 0 1 3 dk2 v2 runit runit.
Let plast_4 := @DParty_last AHE ek4 3 2 dk3 v3 runit runit.

Local Open Scope sproc_scope.
Local Open Scope proc_scope.

(* Wrap as aprocs for duality checking *)
Definition ap_alice_n4 := mk_aproc palice_4.
Definition ap_first_n4 := mk_aproc pfirst_4.
Definition ap_inter_n4 := mk_aproc pinter_4.
Definition ap_last_n4 := mk_aproc plast_4.

(* 4-party duality verification: all 6 pairs *)
Lemma alice_first_dual_n4 : channels_dual ap_alice_n4 ap_first_n4.
Proof. by native_compute. Qed.

Lemma alice_inter_dual_n4 : channels_dual ap_alice_n4 ap_inter_n4.
Proof. by native_compute. Qed.

Lemma alice_last_dual_n4 : channels_dual ap_alice_n4 ap_last_n4.
Proof. by native_compute. Qed.

Lemma first_inter_dual_n4 : channels_dual ap_first_n4 ap_inter_n4.
Proof. by native_compute. Qed.

Lemma first_last_dual_n4 : channels_dual ap_first_n4 ap_last_n4.
Proof. by native_compute. Qed.

Lemma inter_last_dual_n4 : channels_dual ap_inter_n4 ap_last_n4.
Proof. by native_compute. Qed.

(* Cross-check: generic builder produces same erased procs as hand-written *)
Let dk_relay_4 : 'I_3 -> priv_key AHE := fun i =>
  match val i with 0 => dk1 | 1 => dk2 | _ => dk3 end.
Let v_relay_4 : 'I_3 -> plain AHE := fun i =>
  match val i with 0 => v1 | 1 => v2 | _ => v3 end.
Let r1_relay_4 : 'I_3 -> rand AHE := fun _ => runit.
Let r2_relay_4 : 'I_3 -> rand AHE := fun _ => runit.

Lemma dsdp_n4_builder_correct :
  @dsdp_n_procs AHE ek4 2
    [:: @Ordinal 3 0 isT; @Ordinal 3 1 isT; @Ordinal 3 2 isT]
    dk0 v0 u4 r4_3 rand4_3 dk_relay_4 v_relay_4 r1_relay_4 r2_relay_4 =
  erase_aprocs [aprocs palice_4; pfirst_4; pinter_4; plast_4].
Proof. by native_compute. Qed.

(* 4-party saprocs for interpreter integration *)
Definition dsdp_n4_saprocs : seq (aproc dsdp_dtype data) :=
  [aprocs palice_4; pfirst_4; pinter_4; plast_4].

Definition dsdp_n4_procs : seq (proc data) :=
  erase_aprocs dsdp_n4_saprocs.

Lemma dsdp_n4_max_fuel_ok : [> dsdp_n4_saprocs] = 31.
Proof. reflexivity. Qed.

(* 4-party termination: after interpretation, all processes are terminal *)
Lemma dsdp_n4_terminates traces :
  all_terminated (interp [> dsdp_n4_saprocs] dsdp_n4_procs traces).1.
Proof. by native_compute. Qed.

(* 4-party no-fail: after interpretation, no process is Fail *)
Lemma dsdp_n4_no_fail traces :
  all_nonfail (interp [> dsdp_n4_saprocs] dsdp_n4_procs traces).1.
Proof. by native_compute. Qed.

(* 4-party session environment convergence *)
Theorem dsdp_n4_senv_zero traces :
  exists aps' : seq (aproc dsdp_dtype data),
    erase_aprocs aps' =
      (interp [> dsdp_n4_saprocs] dsdp_n4_procs traces).1 /\
    aprocs_senv_depth [:: 0; 1; 2; 3] aps' = 0.
Proof.
have [aps' [Hsz [Herase Hsenv]]] :=
  @senv_bounded _ _ [:: 0; 1; 2; 3] [> dsdp_n4_saprocs]
    dsdp_n4_saprocs traces (leqnn _).
exists aps'.
split; first exact: Herase.
apply: terminated_nonfail_senv_zero.
- by rewrite Herase; exact: dsdp_n4_terminates.
- by rewrite Herase; exact: dsdp_n4_no_fail.
Qed.

End dsdp_n4_idealized_duality.

(*******************************************************************************)
(** * N-Party Session Type Duality Verification (Idealized, 5-party)           *)
(*******************************************************************************)

Section dsdp_n5_idealized_duality.

Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Local Notation msg := 'F_m.

(* Idealized AHE setup *)
Local Definition N5_AHEnc_local : AHEncType :=
  @AHEnc.Pack (Idealized_HETypes msg)
    (@AHEnc.Class (Idealized_HETypes msg)
      (@Idealized_isEncDec msg) (@Idealized_isAHEnc msg)).

Let AHE : AHEncType := N5_AHEnc_local.
Let DI := Standard_DSDP_Interface AHE.
Let data := di_data DI.

(* Party keys (parties 3 and 4 both map to NoParty via nat_to_party_id) *)
Variables (k0 k1 k2 k3 k4 : msg).
Let dk0 : priv_key AHE := k0.
Let dk1 : priv_key AHE := k1.
Let dk2 : priv_key AHE := k2.
Let dk3 : priv_key AHE := k3.
Let dk4 : priv_key AHE := k4.
Let runit : rand AHE := 1.

(* Public key mapping for 5 parties
   (parties 3,4 share NoParty — values don't affect duality) *)
Let ek5 (p : party_id) : pub_key AHE :=
  match p with
  | Alice => pub_of_priv dk0
  | Bob => pub_of_priv dk1
  | Charlie => pub_of_priv dk2
  | NoParty => pub_of_priv dk3
  end.

Variables (v0 v1 v2 v3 v4 : msg).
Variables (u0' u1' u2' u3' u4' : msg).
Variables (r0' r1' r2' r3' : msg).

Let u5 : 'I_5 -> msg := fun i =>
  match val i with 0 => u0' | 1 => u1' | 2 => u2' | 3 => u3' | _ => u4' end.
Let r5_4 : 'I_4 -> msg := fun i =>
  match val i with 0 => r0' | 1 => r1' | 2 => r2' | _ => r3' end.
Let rand5_4 : 'I_4 -> rand AHE := fun _ => runit.

(* 5-party programs *)
Let palice_5 := @palice_n AHE ek5 3
  [:: @Ordinal 4 0 isT; @Ordinal 4 1 isT; @Ordinal 4 2 isT; @Ordinal 4 3 isT]
  dk0 v0 u5 r5_4 rand5_4.
Let pfirst_5 := @DParty_first AHE ek5 1 2 dk1 v1 runit runit.
Let pinter2_5 := @DParty_intermediate AHE ek5 2 0 1 3 dk2 v2 runit runit.
Let pinter3_5 := @DParty_intermediate AHE ek5 3 0 2 4 dk3 v3 runit runit.
Let plast_5 := @DParty_last AHE ek5 4 3 dk4 v4 runit runit.

Local Open Scope sproc_scope.
Local Open Scope proc_scope.

Definition ap_alice_n5 := mk_aproc palice_5.
Definition ap_first_n5 := mk_aproc pfirst_5.
Definition ap_inter2_n5 := mk_aproc pinter2_5.
Definition ap_inter3_n5 := mk_aproc pinter3_5.
Definition ap_last_n5 := mk_aproc plast_5.

(* 5-party duality: all 10 pairs *)
Lemma alice_first_dual_n5 : channels_dual ap_alice_n5 ap_first_n5.
Proof. by native_compute. Qed.

Lemma alice_inter2_dual_n5 : channels_dual ap_alice_n5 ap_inter2_n5.
Proof. by native_compute. Qed.

Lemma alice_inter3_dual_n5 : channels_dual ap_alice_n5 ap_inter3_n5.
Proof. by native_compute. Qed.

Lemma alice_last_dual_n5 : channels_dual ap_alice_n5 ap_last_n5.
Proof. by native_compute. Qed.

Lemma first_inter2_dual_n5 : channels_dual ap_first_n5 ap_inter2_n5.
Proof. by native_compute. Qed.

Lemma first_inter3_dual_n5 : channels_dual ap_first_n5 ap_inter3_n5.
Proof. by native_compute. Qed.

Lemma first_last_dual_n5 : channels_dual ap_first_n5 ap_last_n5.
Proof. by native_compute. Qed.

Lemma inter2_inter3_dual_n5 : channels_dual ap_inter2_n5 ap_inter3_n5.
Proof. by native_compute. Qed.

Lemma inter2_last_dual_n5 : channels_dual ap_inter2_n5 ap_last_n5.
Proof. by native_compute. Qed.

Lemma inter3_last_dual_n5 : channels_dual ap_inter3_n5 ap_last_n5.
Proof. by native_compute. Qed.

(* 5-party saprocs and termination *)
Definition dsdp_n5_saprocs : seq (aproc dsdp_dtype data) :=
  [aprocs palice_5; pfirst_5; pinter2_5; pinter3_5; plast_5].

Definition dsdp_n5_procs : seq (proc data) :=
  erase_aprocs dsdp_n5_saprocs.

Lemma dsdp_n5_terminates traces :
  all_terminated (interp [> dsdp_n5_saprocs] dsdp_n5_procs traces).1.
Proof. by native_compute. Qed.

Lemma dsdp_n5_no_fail traces :
  all_nonfail (interp [> dsdp_n5_saprocs] dsdp_n5_procs traces).1.
Proof. by native_compute. Qed.

End dsdp_n5_idealized_duality.

(*******************************************************************************)
(** * N-Party rsteps Verification Infrastructure                               *)
(*******************************************************************************)

Section dsdp_n_rsteps.

(* Parameterize by an AHEncType instance *)
Variable AHE : AHEncType.

(* Public key mapping *)
Variable ek : party_id -> pub_key AHE.

(* Re-establish type abbreviations *)
Let DI := Standard_DSDP_Interface AHE.
Let msgT := plain AHE.
Let randT := rand AHE.
Let encT := cipher AHE.
Let priv_keyT := priv_key AHE.
Let data := di_data DI.
Let d := di_d DI.
Let e := di_e DI.
Let priv_key := di_priv_key DI.
Let Emul := @Emul AHE.
Let Epow := @Epow AHE.
Let enc_pub_key (p : party_id) (m : msgT) (r : randT) : encT :=
  enc (ek p) m r.

Local Notation "u *h w" := (Emul u w).
Local Notation "u ^h w" := (Epow u w).

Variable n_relay : nat.

(* Re-define alice_env_step (was Let in dsdp_n_party section) *)
Let alice_env_step (j : 'I_n_relay.+1) (env : senv dsdp_dtype) :=
  senv_recv (senv_send env (alice_send_dest j) DT_Enc) j.+1 DT_Enc.

(* Local aliases for proc constructors that conflict with pismc notations *)
Let pInit := @smc_interpreter.Init data.
Let pSend := @smc_interpreter.Send data.
Let pRecv := @smc_interpreter.Recv data.
Let pRet  := @smc_interpreter.Ret data.

(** ** Size of dsdp_n_procs *)
Lemma size_dsdp_n_procs relays dk0 v0 u0 r0 rand_a dk_relay v_relay r1_relay r2_relay :
  size (@dsdp_n_procs AHE ek n_relay relays dk0 v0 u0 r0 rand_a dk_relay v_relay r1_relay r2_relay) =
  (size relays).+1.
Proof. by rewrite /dsdp_n_procs /dsdp_n_saprocs /erase_aprocs /= !size_map. Qed.

(** ** Alice erasure body and tail *)

(* The erased body of Alice's ForList loop: Recv cipher, compute, Send result *)
Definition alice_erase_body
  (u' : 'I_n_relay.+2 -> msgT) (r' : 'I_n_relay.+1 -> msgT) (rand_a' : 'I_n_relay.+1 -> randT)
  (j : 'I_n_relay.+1) (idx : nat) (k : proc data) : proc data :=
  pRecv j.+1 (fun d0 : data =>
    match std_from_enc (AHE:=AHE) d0 with
    | Some enc0 => pSend (alice_send_dest j)
        (e (Epow enc0 (u' (lift ord0 j)) *h enc_pub_key j.+1 (r' j) (rand_a' j)))
        k
    | None => Fail
    end).

(* The erased tail of Alice's program: final Recv + decrypt + Ret *)
Definition alice_erase_tail (dk' : priv_keyT) (v0' : msgT)
  (u' : 'I_n_relay.+2 -> msgT) (r' : 'I_n_relay.+1 -> msgT) : proc data :=
  pRecv n_relay.+1 (fun g : data =>
    match std_from_enc (AHE:=AHE) g with
    | Some enc0 => match dec dk' enc0 with
                   | Some m0 => pRet (d (m0 - \sum_(j < n_relay.+1) r' j + u' ord0 * v0'))
                   | None => Fail
                   end
    | None => Fail
    end).

(* Alice's erased program decomposes via erase_sproc_iter *)
Lemma palice_n_erase relays dk' v0' u' r' rand_a' :
  erase (@palice_n AHE ek n_relay relays dk' v0' u' r' rand_a') =
  pInit (priv_key dk') (pInit (d v0')
    (foldr (fun (fi : 'I_n_relay.+1 * nat) (cont : proc data) =>
              alice_erase_body u' r' rand_a' fi.1 fi.2 cont)
           (alice_erase_tail dk' v0' u' r')
           (zip relays (iota 0 (size relays))))).
Proof.
rewrite /palice_n /= /pInit /priv_key /d; f_equal; f_equal.
rewrite (@erase_sproc_iter _ _ _ alice_idx _ alice_env_step _
  (fun j idx k => alice_erase_body u' r' rand_a' j idx k)).
- f_equal.
  rewrite /alice_erase_tail /DRecv_dec.
  cbn [erase]; rewrite /pRecv /pRet /d.
  f_equal; apply: funext => g.
  case: (std_from_enc (AHE:=AHE) g) => [enc0|] //.
  by case: (dec dk' enc0).
- move=> j idx n0 env0 p.
  rewrite /alice_erase_body /DRecv_enc /DSend.
  cbn [erase]; rewrite /pRecv /pSend /e.
  f_equal; apply: funext => d0.
  by case: (std_from_enc (AHE:=AHE) d0).
Qed.

(** ** Relay erasure lemmas *)

(* First relay: Init dk; Init v; Send E(v) to Alice; Recv dec from Alice;
   Recv enc from Alice; Send product to downstream *)
Lemma DParty_first_erase self downstream dk' v' r1' r2' :
  erase (@DParty_first AHE ek self downstream dk' v' r1' r2') =
  pInit (priv_key dk')
    (pInit (d v')
      (pSend alice_idx (e (enc (ek self) v' r1'))
        (pRecv alice_idx (fun d0 : data =>
          match std_from_enc (AHE:=AHE) d0 with
          | Some enc0 =>
              match dec dk' enc0 with
              | Some m0 =>
                  pRecv alice_idx (fun d1 : data =>
                    match std_from_enc (AHE:=AHE) d1 with
                    | Some enc1 =>
                        pSend downstream
                          (e (Emul enc1 (enc (ek downstream) m0 r2')))
                          Finish
                    | None => Fail
                    end)
              | None => Fail
              end
          | None => Fail
          end)))).
Proof.
rewrite /DParty_first /DRecv_dec /DRecv_enc /DSend.
cbn [erase]; rewrite /pInit /pSend /pRecv /priv_key /d /e /Emul.
f_equal; f_equal; f_equal; f_equal.
apply: funext => d0; case: (std_from_enc (AHE:=AHE) d0) => [enc0|] //.
case: (dec dk' enc0) => [m0|] //.
cbn [erase]; rewrite /pSend /e /Emul.
f_equal; apply: funext => d1.
by case: (std_from_enc (AHE:=AHE) d1) => [enc1|].
Qed.

(* Last relay: Init dk; Init v; Send E(v) to Alice;
   Recv dec from upstream; Send re-encrypted to Alice *)
Lemma DParty_last_erase self upstream dk' v' r1' r2' :
  erase (@DParty_last AHE ek self upstream dk' v' r1' r2') =
  pInit (priv_key dk')
    (pInit (d v')
      (pSend alice_idx (e (enc (ek self) v' r1'))
        (pRecv upstream (fun d0 : data =>
          match std_from_enc (AHE:=AHE) d0 with
          | Some enc0 =>
              match dec dk' enc0 with
              | Some m0 =>
                  pSend alice_idx (e (enc (ek alice_idx) m0 r2')) Finish
              | None => Fail
              end
          | None => Fail
          end)))).
Proof.
rewrite /DParty_last /DRecv_dec /DSend.
cbn [erase]; rewrite /pInit /pSend /pRecv /priv_key /d /e.
f_equal; f_equal; f_equal; f_equal.
apply: funext => d0; case: (std_from_enc (AHE:=AHE) d0) => [enc0|] //.
by case: (dec dk' enc0).
Qed.

(* Intermediate relay: Init dk; Init v; Send E(v) to Alice;
   Recv enc from Alice; Recv dec from upstream; Send product to downstream *)
Lemma DParty_intermediate_erase self alice_src upstream downstream dk' v' r1' r2' :
  erase (@DParty_intermediate AHE ek self alice_src upstream downstream dk' v' r1' r2') =
  pInit (priv_key dk')
    (pInit (d v')
      (pSend alice_src (e (enc (ek self) v' r1'))
        (pRecv alice_src (fun d0 : data =>
          match std_from_enc (AHE:=AHE) d0 with
          | Some enc0 =>
              pRecv upstream (fun d1 : data =>
                match std_from_enc (AHE:=AHE) d1 with
                | Some enc1 =>
                    match dec dk' enc1 with
                    | Some m0 =>
                        pSend downstream
                          (e (Emul enc0 (enc (ek downstream) m0 r2')))
                          Finish
                    | None => Fail
                    end
                | None => Fail
                end)
          | None => Fail
          end)))).
Proof.
rewrite /DParty_intermediate /DRecv_enc /DRecv_dec /DSend.
cbn [erase]; rewrite /pInit /pSend /pRecv /priv_key /d /e /Emul.
f_equal; f_equal; f_equal; f_equal.
apply: funext => d0; case: (std_from_enc (AHE:=AHE) d0) => [enc0|] //.
cbn [erase]; rewrite /pRecv.
f_equal; apply: funext => d1.
case: (std_from_enc (AHE:=AHE) d1) => [enc1|] //.
by case: (dec dk' enc1).
Qed.

End dsdp_n_rsteps.

(*******************************************************************************)
(** * Interpreter soundness w.r.t. rsteps                                      *)
(*******************************************************************************)

Section interp_sound_section.
Variable data : eqType.

(* Trace-free interpreter iteration: mirrors interp but always passes nil
   as trace. Used as a computational bridge between interp and rsteps. *)
Fixpoint interp1 (ps : seq (proc data)) (h : nat)
  : seq (proc data) :=
  if h is h.+1 then
    let ps_trs := [seq smc_interpreter.step ps nil i
                  | i <- iota 0 (size ps)] in
    if has snd ps_trs then
      interp1 (unzip1 (unzip1 ps_trs)) h
    else ps
  else ps.

Lemma size_interp1 ps h :
  size (interp1 ps h) = size ps.
Proof.
elim: h ps => [|h IH] ps //=.
case: ifP => _ //.
by rewrite IH /unzip1 -map_comp !size_map size_iota.
Qed.

(* The process component of step is independent of the trace argument. *)
Lemma step_proc_trace_indep (ps : seq (proc data)) tr1 tr2 i :
  (smc_interpreter.step ps tr1 i).1.1 =
  (smc_interpreter.step ps tr2 i).1.1.
Proof.
rewrite /smc_interpreter.step.
case: (nth _ ps i) => [d0 p|dst d0 p|frm f|d0||] //=;
  by case: (nth _ ps _) => [? ?|? ? ?|? ?|?||] //=; case: ifP.
Qed.

(* The progress flag of step is independent of the trace argument. *)
Lemma step_progress_trace_indep (ps : seq (proc data)) tr1 tr2 i :
  (smc_interpreter.step ps tr1 i).2 =
  (smc_interpreter.step ps tr2 i).2.
Proof.
rewrite /smc_interpreter.step.
case: (nth _ ps i) => [d0 p|dst d0 p|frm f|d0||] //=;
  by case: (nth _ ps _) => [? ?|? ? ?|? ?|?||] //=; case: ifP.
Qed.

(* interp1 computes the same processes as interp *)
Lemma interp1E h ps traces :
  size traces = size ps ->
  interp1 ps h = (interp h ps traces).1.
Proof.
elim: h ps traces => [|h IH] ps traces Hsz //=.
set res_nil := map _ _; set res_tr := map _ _.
have Hprog : has snd res_nil = has snd res_tr.
  rewrite /res_nil /res_tr !has_map; apply: eq_in_has => i.
  rewrite mem_iota /= => Hi.
  exact: step_progress_trace_indep.
rewrite Hprog; case: ifP => // _.
have Hproc : unzip1 (unzip1 res_nil) = unzip1 (unzip1 res_tr).
  rewrite /res_nil /res_tr /unzip1 -!map_comp; apply: eq_map => i /=.
  exact: step_proc_trace_indep.
rewrite Hproc; apply: IH.
by rewrite /res_tr /unzip1 /unzip2 !size_map.
Qed.

(* step_sound gives rsteps using tuples; we need to connect that to
   the seq-level interp1 which uses iota. These two lemmas bridge
   the iota/enum gap. *)
Lemma step_iota_enum n (ps : seq (proc data)) :
  [seq smc_interpreter.step ps nil i | i <- iota 0 n] =
  [seq smc_interpreter.step ps nil (val i) | i <- enum 'I_n].
Proof. by rewrite -(val_enum_ord n) -map_comp. Qed.

(* Interpreter soundness: h rounds of interp produce an rsteps proof *)
Lemma interp_sound n h (ps : n.-tuple (proc data)) :
  exists (final : n.-tuple (proc data)) tr,
    rsteps ps final tr /\
    tval final = interp1 (tval ps) h.
Proof.
elim: h ps => [|h IH] ps.
  exists ps, [tuple nil | _ < n]; split; first exact: rrefl.
  by [].
(* h.+1 case *)
simpl interp1; rewrite size_tuple (step_iota_enum n).
set ps' := map_tuple (fun r => r.1.1)
             [tuple smc_interpreter.step ps nil i | i < n].
have Hss := step_sound ps.
case Hprog: (has snd _).
  have [final [tr2 [Htr2 Hfinal]]] := IH ps'.
  exists final; eexists; split; last first.
    rewrite Hfinal /ps' /=.
    by congr (interp1 _ h); rewrite /unzip1 -!map_comp.
  exact: (rtrans Hss Htr2 erefl).
by exists ps, [tuple nil | _ < n]; split; [exact: rrefl|].
Qed.

End interp_sound_section.

(*******************************************************************************)
(** * Idealized 3-Party DSDP rsteps Proof                                      *)
(*******************************************************************************)

(* This section proves that the 3-party DSDP protocol (Alice + Bob + Charlie)
   under the idealized AHE scheme admits a complete rsteps reduction sequence.
   This serves as the foundation for the general n-party rsteps proof. *)

Section dsdp_3party_rsteps.

Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Local Notation msg := 'F_m.

(* Idealized AHE setup *)
Local Definition R3_AHEnc_local : AHEncType :=
  @AHEnc.Pack (Idealized_HETypes msg)
    (@AHEnc.Class (Idealized_HETypes msg)
      (@Idealized_isEncDec msg) (@Idealized_isAHEnc msg)).

Let AHE : AHEncType := R3_AHEnc_local.
Let DI := Standard_DSDP_Interface AHE.
Let data := di_data DI.
Let d := di_d DI.
Let e := di_e DI.
Let priv_key := di_priv_key DI.
Let Emul := @Emul AHE.
Let Epow := @Epow AHE.
Let priv_keyT := he_types.priv_key AHE.

(* Party keys *)
Variables (k_a k_b k_c : msg).
Let dk_a : priv_keyT := k_a.
Let dk_b : priv_keyT := k_b.
Let dk_c : priv_keyT := k_c.
Let runit : rand AHE := 1.

(* Public key mapping *)
Let ek3 (p : party_id) : pub_key AHE :=
  match p with
  | Alice => pub_of_priv dk_a
  | Bob => pub_of_priv dk_b
  | Charlie => pub_of_priv dk_c
  | NoParty => pub_of_priv dk_a
  end.

(* Program variables *)
Variables (v0 v1 v2 : msg).
Variables (u0' u1' u2' : msg).
Variables (r0' r1' : msg).

(* Index functions *)
Let u3 : 'I_3 -> msg := fun i =>
  match val i with 0 => u0' | 1 => u1' | _ => u2' end.
Let r3_2 : 'I_2 -> msg := fun i =>
  match val i with 0 => r0' | _ => r1' end.
Let rand3_2 : 'I_2 -> rand AHE := fun _ => runit.

(* Relay key/value functions *)
Let dk_relay : 'I_2 -> priv_keyT := fun i =>
  match val i with 0 => dk_b | _ => dk_c end.
Let v_relay : 'I_2 -> plain AHE := fun i =>
  match val i with 0 => v1 | _ => v2 end.
Let r1_relay : 'I_2 -> rand AHE := fun _ => runit.
Let r2_relay : 'I_2 -> rand AHE := fun _ => runit.

(* Local aliases for proc constructors *)
Let pInit := @smc_interpreter.Init data.
Let pSend := @smc_interpreter.Send data.
Let pRecv := @smc_interpreter.Recv data.
Let pRet  := @smc_interpreter.Ret data.

Local Open Scope proc_scope.

(* The 3-party protocol processes *)
Let relays : seq 'I_2 :=
  [:: @Ordinal 2 0 isT; @Ordinal 2 1 isT].

Let procs := @dsdp_n_procs AHE ek3 1 relays dk_a v0 u3 r3_2 rand3_2
  dk_relay v_relay r1_relay r2_relay.

(* Size lemma for our concrete procs *)
Let Hsize : size procs = 3.
Proof. by rewrite /procs size_dsdp_n_procs. Qed.

(* Cast to 3-tuple *)
Let procs3 : 3.-tuple (proc data) :=
  @Tuple _ _ procs (introT eqP Hsize).

(* The step_sound approach: apply the step function iteratively *)
(* For the idealized scheme, all branches resolve computationally *)

(* The protocol terminates: we can check this via the interpreter *)
Lemma dsdp_3party_terminates traces :
  all_terminated (interp 27 procs traces).1.
Proof. by native_compute. Qed.

Lemma dsdp_3party_no_fail traces :
  all_nonfail (interp 27 procs traces).1.
Proof. by native_compute. Qed.

(* Main theorem: the 3-party protocol admits an rsteps reduction *)
Theorem dsdp_3party_rsteps :
  exists final traces,
    rsteps procs3 final traces /\
    all_terminated (tval final) /\
    all_nonfail (tval final).
Proof.
have [final [tr [Hrsteps Hfinal]]] :=
  @interp_sound data 3 27 procs3.
exists final, tr; split; first exact: Hrsteps.
by rewrite Hfinal (@interp1E data 27 _ (nseq 3 [::])) ?size_nseq.
Qed.

End dsdp_3party_rsteps.
