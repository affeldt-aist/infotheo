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
Local Notation E := enc_pub_key.

(* Bob's protocol - using concrete indices for session type duality *)
Definition pbob (dk : priv_keyT)(v2 : msgT)(rb1 rb2 : randT)
    : sproc dsdp_dtype data bob_idx :=
  \pi{ Init (#dk, &v2) ;
     Send<alice_idx> $(E bob v2 rb1);
     Recv<alice_idx> #dk d2 =>
     Recv<alice_idx> a3 =>
     Send<charlie_idx> $(a3 *h (E charlie d2 rb2)) ;
     Finish }.

(* Charlie's protocol *)
Definition pcharlie (dk : priv_keyT)(v3 : msgT)(rc1 rc2 : randT)
    : sproc dsdp_dtype data charlie_idx :=
  \pi{ Init (#dk, &v3) ;
     Send<alice_idx> $(E charlie v3 rc1) ;
     Recv<bob_idx> #dk d3 =>
     Send<alice_idx> $(E alice d3 rc2) ;
     Finish }.

(* Alice's protocol *)
Definition palice (dk : priv_keyT)(v1 u1 u2 u3 r2 r3: msgT)(ra1 ra2 : randT)
    : sproc dsdp_dtype data alice_idx :=
  \pi{ Init (#dk, &v1, &u1, &u2, &u3, &r2, &r3) ;
     Recv<bob_idx> c2 =>
     Recv<charlie_idx> c3 =>
     Send<bob_idx> $(c2 ^h u2 *h (E bob r2 ra1)) ;
     Send<bob_idx> $(c3 ^h u3 *h (E charlie r3 ra2)) ;
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
Proof. by rewrite /palice_orig /dsdp_program.palice pn_bob pn_charlie. Qed.

Lemma bob_cross_eq dk' v2' rb1' rb2' :
  erase (pbob dk' v2' rb1' rb2') =
  erase (pbob_orig dk' v2' rb1' rb2').
Proof. by rewrite /pbob_orig /dsdp_program.pbob pn_alice pn_charlie. Qed.

Lemma charlie_cross_eq dk' v3' rc1' rc2' :
  erase (pcharlie dk' v3' rc1' rc2') =
  erase (pcharlie_orig dk' v3' rc1' rc2').
Proof. by rewrite /pcharlie_orig /dsdp_program.pcharlie pn_alice pn_bob. Qed.

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
