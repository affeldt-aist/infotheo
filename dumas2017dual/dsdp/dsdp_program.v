From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter.
Require Import smc_session_types spp_proba homomorphic_encryption.
Require Import dsdp_interface dsdp_session_types.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* Formalization of:                                                          *)
(*                                                                            *)
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

Reserved Notation "u *h w" (at level 40).
Reserved Notation "u ^h w" (at level 40).

Section dsdp.

(* Party identifiers.
   Because AHE requires party type but for session type it requires nat. *)
Definition alice_idx : nat := 0.
Definition bob_idx : nat := 1.
Definition charlie_idx : nat := 2.

(* Parameterize by an AHEncType instance *)
Variable AHE : AHEncType.

(* Use standard DSDP interface for data types *)
Let DI := Standard_DSDP_Interface AHE.

(* Extract types from the AHEncType *)
Let msgT := plain AHE.
Let randT := rand AHE.
Let encT := cipher AHE.
Let priv_keyT := priv_key AHE.

(* Data type and constructors from interface *)
Let data := di_data DI.
Let d := di_d DI.
Let e := di_e DI.
Let k := di_priv_key DI.
Let Recv_dec := @di_Recv_dec AHE DI.
Let Recv_enc := @di_Recv_enc AHE DI.

(* HE operations from the AHEncType - using @ to provide AHEncType explicitly *)
Let Emul := @Emul AHE.
Let Epow := @Epow AHE.

Notation "u *h w" := (Emul u w).
Notation "u ^h w" := (Epow u w).

Variable alice : party_id.
Variable bob : party_id.
Variable charlie : party_id.

(* Party to nat mapping for Send/Recv indices *)
Variable pn : party_id -> nat.

(* Public key mapping: each party has an associated public key *)
Variable ek : party_id -> pub_key AHE.

(* Party-indexed encryption: maps party to their public key for enc *)
Definition enc_pk (p : party_id) (m : msgT) (r : randT) : encT :=
  enc (ek p) m r.
Local Notation E := enc_pk.

Definition pbob (dk : priv_keyT)(v2 : msgT)(rb1 rb2 : randT) :
  @sproc dsdp_dtype data bob_idx _ _ :=
  DInit (k dk) (
  DInit (d v2) (
  DSend (pn alice) (e (E bob v2 rb1)) (
  DRecv_dec (pn alice) dk (fun d2 =>
  DRecv_enc (pn alice) (fun a3 =>
    DSend (pn charlie) (e (a3 *h (E charlie d2 rb2))) (
  DFinish)))))).

Definition pcharlie (dk : priv_keyT)(v3 : msgT)(rc1 rc2 : randT) :
  @sproc dsdp_dtype data charlie_idx _ _ :=
  DInit (k dk) (
  DInit (d v3) (
  DSend (pn alice) (e (E charlie v3 rc1)) (
  DRecv_dec (pn bob) dk (fun d3 => (
    DSend (pn alice) (e (E alice d3 rc2))
  DFinish))))).

Definition palice (dk : priv_keyT)(v1 u1 u2 u3 r2 r3: msgT)(ra1 ra2 : randT) :
  @sproc dsdp_dtype data alice_idx _ _ :=
  DInit (k dk) (
  DInit (d v1) (
  DInit (d u1) (
  DInit (d u2) (
  DInit (d u3) (
  DInit (d r2) (
  DInit (d r3) (
  DRecv_enc (pn bob) (fun c2 =>
  DRecv_enc (pn charlie) (fun c3 =>
  let a2 := (c2 ^h u2 *h (E bob r2 ra1)) in
  let a3 := (c3 ^h u3 *h (E charlie r3 ra2)) in
    DSend (pn bob) (e a2) (
    DSend (pn bob) (e a3) (
    DRecv_dec (pn charlie) dk (fun g =>
    DRet (d ((g - r2 - r3 + u1 * v1))))))))))))))).
  
(* Randomness variables for each party's encryptions *)
Variables (rb1 rb2 rc1 rc2 ra1 ra2 : randT).
Variables (dk_a dk_b dk_c : priv_keyT).
Variables (v1 v2 v3 u1 u2 u3 r2 r3 : msgT).

(* Session-typed processes packed via [aprocs ...].

   Why not use [procs ...] directly with sproc?
   - Each sproc has different type indices (party, fuel, session env)
   - Coq unifies list element types BEFORE applying coercions
   - sproc 0 n1 env1 and sproc 1 n2 env2 cannot unify
   See: https://github.com/coq/coq/issues/10898

   The aproc wrapper solves this:
   - aproc existentially packages the indices, making all elements
     have the same type: aproc dsdp_dtype data
   - [> dsdp_saprocs] computes total fuel from packaged indices
   - erase_aprocs converts to seq (proc data) for the interpreter
   See also: https://github.com/coq/coq/issues/4593 (uniform inheritance) *)
Definition dsdp_saprocs : seq (aproc dsdp_dtype data) :=
  [aprocs palice dk_a v1 u1 u2 u3 r2 r3 ra1 ra2; 
          pbob dk_b v2 rb1 rb2; 
          pcharlie dk_c v3 rc1 rc2].

(* Erased processes for interpreter (strips session type indices) *)
Definition dsdp_procs : seq (proc data) :=
  erase_aprocs dsdp_saprocs.

Definition dsdp h :=
  interp h dsdp_procs (nseq 3 [::]).

(* Fuel bound computed from program structure:
   - palice: 14 (Init*7 + Recv_enc*2 + Send*2 + Recv_dec + Ret=2)
   - pbob: 7 (Init*2 + Send + Recv_dec + Recv_enc + Send + Finish=1)
   - pcharlie: 6 (Init*2 + Send + Recv_dec + Send + Finish=1)
   Total: 14 + 7 + 6 = 27 *)
Definition dsdp_max_fuel : nat := 27.

(* ========================================================================== *)
(* Algebraic correctness proof using homomorphic properties                    *)
(* ========================================================================== *)

(* The homomorphic properties from AHEncType - using mixin directly *)
Let Emul_eq_add := @Emul_addM AHE.
Let Epow_eq_mul := @Epow_scalarM AHE.

(* enc k m r = enc_curry _ k (m, r) is definitional, but morphism
   rewriting needs syntactic enc_curry form *)
Local Lemma enc_curry_eq (kk : pub_key AHE) (m : msgT) (r : randT) :
  enc kk m r = ahe_enc.enc_curry AHE kk (m, r).
Proof. by []. Qed.

(* 
   Protocol correctness theorem (algebraic version):
   
   The DSDP protocol computes the dot product u1*v1 + u2*v2 + u3*v3.
   
   Proof sketch using homomorphic properties:
   1. Bob sends c2 = E(bob, v2, rb1) to Alice
   2. Charlie sends c3 = E(charlie, v3, rc1) to Alice  
   3. Alice computes:
      a2 = Epow(c2, u2) *h E(bob, r2, ra1)
         = E(bob, v2*u2, _) *h E(bob, r2, _)     [by Epow_eq_mul]
         = E(bob, v2*u2 + r2, _)                  [by Emul_eq_add]
      a3 = Epow(c3, u3) *h E(charlie, r3, ra2)
         = E(charlie, v3*u3 + r3, _)              [similarly]
   4. Bob decrypts a2: d2 = v2*u2 + r2           [by D_correct]
   5. Bob computes: a3 *h E(charlie, d2, rb2)
         = E(charlie, v3*u3 + r3 + v2*u2 + r2, _) [by Emul_eq_add]
   6. Charlie decrypts: g = v3*u3 + r3 + v2*u2 + r2 [by D_correct]
   7. Alice computes: g - r2 - r3 + u1*v1
         = v3*u3 + v2*u2 + u1*v1                  [ring algebra]
*)

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
  rewrite /alice_a2 /bob_encrypted_input /Epow /enc_pk /Emul.
  rewrite !enc_curry_eq.
  rewrite -Epow_eq_mul -Emul_eq_add.
  by eexists.
Qed.

(* Lemma: alice_a3 encrypts v3*u3 + r3 *)
Lemma alice_a3_value : exists rr,
  alice_a3 = E charlie (v3 * u3 + r3) rr.
Proof.
  rewrite /alice_a3 /charlie_encrypted_input /Epow /enc_pk /Emul.
  rewrite !enc_curry_eq.
  rewrite -Epow_eq_mul -Emul_eq_add.
  by eexists.
Qed.

(* Value Bob decrypts from a2 *)
Definition d2_value : msgT := v2 * u2 + r2.

(* Bob's computation: a3 combined with encrypted d2 *)
Definition bob_combined (a3_enc : encT) : encT :=
  a3_enc *h (E charlie d2_value rb2).

(* Lemma: Bob's combined ciphertext encrypts the sum *)
Lemma bob_combined_value : exists rr,
  bob_combined alice_a3 = E charlie (v3 * u3 + r3 + d2_value) rr.
Proof.
  rewrite /bob_combined /Emul /enc_pk.
  have [rr3 Ha3] := alice_a3_value.
  rewrite /enc_pk in Ha3.
  rewrite Ha3 !enc_curry_eq -Emul_eq_add.
  by eexists.
Qed.

(* Value Charlie decrypts *)
Definition g_value : msgT := v3 * u3 + r3 + d2_value.

(* Final computation by Alice *)
Definition alice_result : msgT := g_value - r2 - r3 + u1 * v1.

(* Main correctness theorem: Alice computes the dot product *)
Theorem dsdp_computes_dot_product :
  alice_result = u1 * v1 + u2 * v2 + u3 * v3.
Proof.
  rewrite /alice_result /g_value /d2_value.
  ring.
Qed.

(* ========================================================================== *)
(* N-party generalization of algebraic correctness                            *)
(* ========================================================================== *)

(* N-party DSDP: n_relay.+2 total parties (Alice + n_relay.+1 relays).
   n_relay = 1 gives the standard 3-party protocol. *)
Section dsdp_n.

Variable n_relay : nat.

Variable v : 'I_n_relay.+2 -> msgT.
Variable u : 'I_n_relay.+2 -> msgT.
Variable r : 'I_n_relay.+1 -> msgT.

(* Accumulated ciphertext value that Alice receives from the relay chain.
   Each relay party i (indexed 1..n_relay.+1) contributes u_i * v_i + r_i. *)
Definition g_value_n : msgT :=
  \sum_(i : 'I_n_relay.+1) (u (lift ord0 i) * v (lift ord0 i) + r i).

(* Alice's final computation: subtract all masking values, add own term *)
Definition alice_result_n : msgT :=
  g_value_n - \sum_(i : 'I_n_relay.+1) r i + u ord0 * v ord0.

(* N-party correctness: Alice computes the dot product *)
Theorem dsdp_computes_dot_product_n :
  alice_result_n = \sum_(i < n_relay.+2) u i * v i.
Proof.
rewrite /alice_result_n /g_value_n big_split /= addrK [RHS]big_ord_recl.
by rewrite addrC.
Qed.

End dsdp_n.

End dsdp.
