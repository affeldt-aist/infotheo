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

(* Parameterize by an AHEAlgebra_scheme instance *)
Variable AHE : AHEAlgebra_scheme.

(* Use standard DSDP interface for data types *)
Let DI := Standard_DSDP_Interface AHE.

(* Extract types from the scheme *)
Let partyT := party AHE.
Let msgT := plain AHE.
Let randT := rand AHE.
Let encT := party_cipher AHE.
Let pkeyT := pkey AHE.

(* Data type and constructors from interface *)
Let data := di_data DI.
Let d := di_d DI.
Let e := di_e DI.
Let k := di_k DI.
Let Recv_dec := @di_Recv_dec AHE DI.
Let Recv_enc := @di_Recv_enc AHE DI.

(* HE operations from the scheme - using @ to provide scheme explicitly *)
Let E := @enc AHE.
Let K := @key AHE.
Let D := @dec AHE.
Let Emul := @Emul AHE.
Let Epow := @Epow AHE.


Notation "u *h w" := (Emul u w).
Notation "u ^h w" := (Epow u w).

(* Party identities - these are variables of the scheme's party type.
   For concrete instances like Benaloh_Party_HE, partyT = party. *)
Variable alice : partyT.
Variable bob : partyT.
Variable charlie : partyT.

(* Party to nat mapping for Send/Recv indices *)
Variable pn : partyT -> nat.

(* Decryption correctness: D inverts E for matching party and Dec key *)
Hypothesis D_correct : forall p m r k,
  D (K p Dec k) (E p m r) = Some m.

Definition pbob (dk : pkeyT)(v2 : msgT)(rb1 rb2 : randT) :
  @sproc dsdp_dtype data bob_idx _ _ :=
  DInit (k dk) (
  DInit (d v2) (
  DSend (pn alice) (e (E bob v2 rb1)) (
  DRecv_dec (pn alice) dk (fun d2 =>
  DRecv_enc (pn alice) (fun a3 =>
    DSend (pn charlie) (e (a3 *h (E charlie d2 rb2))) (
  DFinish)))))).

Definition pcharlie (dk : pkeyT)(v3 : msgT)(rc1 rc2 : randT) :
  @sproc dsdp_dtype data charlie_idx _ _ :=
  DInit (k dk) (
  DInit (d v3) (
  DSend (pn alice) (e (E charlie v3 rc1)) (
  DRecv_dec (pn bob) dk (fun d3 => (
    DSend (pn alice) (e (E alice d3 rc2))
  DFinish))))).

Definition palice (dk : pkeyT)(v1 u1 u2 u3 r2 r3: msgT)(ra1 ra2 : randT) :
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
Variables (k_a k_b k_c v1 v2 v3 u1 u2 u3 r2 r3 : msgT).

(* Keys constructed using the scheme's K operation *)
Let dk_a : pkeyT := K alice Dec k_a.
Let dk_b : pkeyT := K bob Dec k_b.
Let dk_c : pkeyT := K charlie Dec k_c.

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

(* The homomorphic properties from AHEAlgebra_scheme - using mixin directly *)
Let Emul_eq_add := @Emul_addM AHE.
Let Epow_eq_mul := @Epow_mulM AHE.
Let enc_curry_eq := @enc_as_curry AHE.

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
Definition d2_value : msgT := v2 * u2 + r2.

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

End dsdp.
