From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import smc_interpreter pismc.
Require Import smc_session_types homomorphic_encryption.
Require Import dsdp_interface dsdp_session_types dsdp_program.

Local Open Scope pismc_scope.
Local Open Scope ring_scope.

Section smc_dsdp_program.

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

(* HE operations from the scheme - using @ to provide scheme explicitly *)
Let E := @enc PHE.
Let K := @key PHE.
Let D := @dec PHE.
Let Emul := @Emul PHE.
Let Epow := @Epow PHE.

Notation "u *h w" := (Emul u w).
Notation "u ^h w" := (Epow u w).

(* Party identities - variables of the scheme's party type *)
Variable alice : partyT.
Variable bob : partyT.
Variable charlie : partyT.

(* Concrete party indices for session type tracking *)
(* These must be distinct for duality verification to work with native_compute *)
Definition alice_idx : nat := 0.
Definition bob_idx : nat := 1.
Definition charlie_idx : nat := 2.

(* Use session-typed wrappers from dsdp_interface directly *)
Let PInit {party n env} := @DInit PHE party n env.
Let PSend {party n env} := @DSend PHE party n env.
Let PRet {party} := @DRet PHE party.
Let Recv_dec {party n env} := @DRecv_dec PHE party n env.
Let Recv_enc {party n env} := @DRecv_enc PHE party n env.

(** * Data wrapper shorthand notations *)

(* #x -> (k x) for key *)
Local Notation "# x" := (k x) (at level 0, x at level 0) : pismc_scope.
(* &x -> (d x) for data/message *)
Local Notation "& x" := (d x) (at level 0, x at level 0) : pismc_scope.
(* $x -> (e x) for encrypted *)
Local Notation "$ x" := (e x) (at level 0, x at level 0) : pismc_scope.

(* Finish - terminal state (session-typed) *)
Notation "'Finish'" := SFinish (in custom pismc at level 0).

Notation "'Send<' p '>' x ; P" := (PSend p x P)
  (in custom pismc at level 85, p constr at level 0, x constr at level 0,
   P custom pismc at level 85, right associativity).

(* Protocol-specific Recv notations *)
Local Notation "'Recv_enc<' p '>' 'fun' x '=>' P" :=
  (Recv_enc p (fun x => P))
  (in custom pismc at level 85, p constr at level 0, x name,
   P custom pismc at level 85, right associativity).

Notation "'Recv_dec<' p '>' dk 'fun' x '=>' P" :=
  (Recv_dec p dk (fun x => P))
  (in custom pismc at level 85, p constr at level 0, 
   dk constr at level 0, x name,
   P custom pismc at level 85, right associativity).

(* Ret - return a value *)
Local Notation "'Ret' x" := (PRet x) 
  (in custom pismc at level 80, x constr at level 0).

(* Single Init with continuation *)
Notation "'Init' x ; P" := (PInit x P)
  (in custom pismc at level 85, x constr at level 0,
   P custom pismc at level 85, right associativity).

(* Multi-var Init using tuple syntax *)
Local Notation "'Init' '(' x ',' .. ',' y ')' ; P" := (PInit x .. (PInit y P) ..)
  (in custom pismc at level 85,
   x constr at level 0, y constr at level 0,
   P custom pismc at level 85, right associativity).

(******************************************************************************)
(** * DSDP Protocol Programs with Session Type Tracking                       *)
(** * Each encryption E(party, msg, rand) needs explicit randomness.          *)
(******************************************************************************)

(* Bob's protocol - using concrete indices for session type duality *)
Definition pbob (dk : pkey)(v2 : msg)(rb1 rb2 : rand) 
    : @sproc dsdp_dtype data bob_idx _ _ :=
  pi{ Init (#dk, &v2) ;
     Send<alice_idx> $(E bob v2 rb1);
     Recv_dec<alice_idx> dk fun d2 =>
     Recv_enc<alice_idx> fun a3 =>
     Send<charlie_idx> $(a3 *h (E charlie d2 rb2)) ;
     Finish }.

(* Charlie's protocol *)
Definition pcharlie (dk : pkey)(v3 : msg)(rc1 rc2 : rand) 
    : @sproc dsdp_dtype data charlie_idx _ _ :=
  pi{ Init (#dk, &v3) ;
     Send<alice_idx> $(E charlie v3 rc1) ;
     Recv_dec<bob_idx> dk fun d3 =>
     Send<alice_idx> $(E alice d3 rc2) ;
     Finish }.

(* Alice's protocol *)
Definition palice (dk : pkey)(v1 u1 u2 u3 r2 r3: msg)(ra1 ra2 : rand) 
    : @sproc dsdp_dtype data alice_idx _ _ :=
  pi{ Init (#dk, &v1, &u1, &u2, &u3, &r2, &r3) ;
     Recv_enc<bob_idx> fun c2 =>
     Recv_enc<charlie_idx> fun c3 =>
     Send<bob_idx> $(c2 ^h u2 *h (E bob r2 ra1)) ;
     Send<bob_idx> $(c3 ^h u3 *h (E charlie r3 ra2)) ;
     Recv_dec<charlie_idx> dk fun g =>
     Ret &(g - r2 - r3 + u1 * v1) }.


(******************************************************************************)
(** * Cross-equality with dsdp_program                                        *)
(** * Proves that piSMC programs equal the original dsdp_program definitions  *)
(******************************************************************************)

(* Party-to-nat mapping and hypotheses relating it to concrete indices.
   Unlike SPP where parties are concrete nats, DSDP uses an abstract party type
   from the HE scheme. We need hypotheses to connect pn with concrete indices. *)
Variable pn : partyT -> nat.
Hypothesis pn_alice : pn alice = alice_idx.
Hypothesis pn_bob : pn bob = bob_idx.
Hypothesis pn_charlie : pn charlie = charlie_idx.

(* Import original programs from dsdp_program *)
Let palice_orig := @dsdp_program.palice PHE bob charlie pn.
Let pbob_orig := @dsdp_program.pbob PHE alice bob charlie pn.
Let pcharlie_orig := @dsdp_program.pcharlie PHE alice bob charlie pn.

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

Variables (dk : pkey) (v1 u1 u2 u3 r2 r3 v2 v3 : msg)
(ra1 ra2 rb1 rb2 rc1 rc2 : rand).

(* Wrap in aproc for duality checking *)
Definition aproc_alice := mk_aproc (palice dk v1 u1 u2 u3 r2 r3 ra1 ra2).
Definition aproc_bob := mk_aproc (pbob dk v2 rb1 rb2).
Definition aproc_charlie := mk_aproc (pcharlie dk v3 rc1 rc2).

(* Three-party duality verification *)
Lemma alice_bob_dual : channels_dual aproc_alice aproc_bob = true.
Proof.
by native_compute.
Qed.

Lemma alice_charlie_dual : channels_dual aproc_alice aproc_charlie = true.
Proof.
by native_compute.
Qed.

Lemma bob_charlie_dual : channels_dual aproc_bob aproc_charlie = true.
Proof.
by native_compute.
Qed.

End smc_dsdp_program.
