From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg ring.
From mathcomp Require Import Rstruct reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_proba smc_entropy.
Require Import smc_interpreter smc_session_types scalar_product_interface.

(**md**************************************************************************)
(* # SMC Program for the SMC Scalar Product Protocol                          *)
(*                                                                            *)
(* Now with session types for protocol verification!                          *)
(*                                                                            *)
(* |   Definitions     |    | Meaning                                        |*)
(* |-------------------|----|------------------------------------------------|*)
(* | pcoserv           | == | The Commodity server process in the protocol.  |*)
(* | palice            | == | The Alice (Party#1) process in the protocol.   |*)
(* | pbob              | == | The Bob (Party#2) process in the protocol.     |*)
(* | is_scalar_product | == | The correctness of the SMC scalar product      |*)
(* |                   |    | results                                        |*)
(* |-------------------------------------------------------------------------|*)
(*                                                                            *)
(* Session type verification:                                                 *)
(* - coserv_alice_dual: proves coserv and alice have dual session types      *)
(* - coserv_bob_dual: proves coserv and bob have dual session types          *)
(* - alice_bob_dual: proves alice and bob have dual session types            *)
(*                                                                            *)
(* Formalization for:                                                         *)
(* A practical approach to solve secure multi-party computation problems      *)
(* Du, W., Zhan, J.Z.                                                         *)
(* In: Workshop on New Security Paradigms (NSPW 2002), Virginia Beach, VA, USA*)
(* September 23-26, 2002. pp. 127-135. ACM (2002).                            *)
(* https://doi.org/10.1145/844102.844125                                      *)
(*                                                                            *)
(******************************************************************************)


Import GRing.Theory.
Import Num.Theory.

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

Section scalar_product.
Variable m : nat.
Variable TX : finComRingType.
Variable VX : lmodType TX. (* vector is not ringType (mul)*)
Variable dotproduct : VX -> VX -> TX.
Local Notation "u *d w" := (dotproduct u w).

(* Import definitions from scalar_product_interface *)
Let alice := @scalar_product_interface.alice.
Let bob := @scalar_product_interface.bob.
Let coserv := @scalar_product_interface.coserv.
Let data := data TX VX.
Let one := @one TX VX.
Let vec := @vec TX VX.
Let SRecv_one := @scalar_product_interface.SRecv_one TX VX.
Let SRecv_vec := @scalar_product_interface.SRecv_vec TX VX.

(******************************************************************************)
(** * Session-Typed Protocol Definitions                                      *)
(******************************************************************************)

(* Commodity server's protocol - session typed *)
(* Fuel and session environment are automatically inferred via _ *)
Definition pcoserv (sa sb: VX) (ra : TX) : @sproc sp_dtype data coserv _ _ :=
  SInit (vec sa)
  (SInit (vec sb)
  (SInit (one ra)
  (SSend alice DT_Vec (vec sa)
  (SSend alice DT_One (one ra)
  (SSend bob DT_Vec (vec sb)
  (SSend bob DT_One (one (sa *d sb - ra)) SFinish)))))).

(* Alice's protocol - session typed *)
Definition palice (xa : VX) : @sproc sp_dtype data alice _ _ :=
  SInit (vec xa)
  (SRecv_vec coserv (fun sa =>
   SRecv_one coserv (fun ra =>
   SSend bob DT_Vec (vec (xa + sa))
   (SRecv_vec bob (fun xb' =>
    SRecv_one bob (fun t =>
    SRet (one (t - (xb' *d sa) + ra)))))))).

(* Bob's protocol - session typed *)
Definition pbob (xb : VX) (yb : TX) : @sproc sp_dtype data bob _ _ :=
  SInit (vec xb)
  (SInit (one yb)
  (SRecv_vec coserv (fun sb =>
   SRecv_one coserv (fun rb =>
   SRecv_vec alice (fun xa' =>
   let t := xa' *d xb + rb - yb in
   SSend alice DT_Vec (vec (xb + sb))
   (SSend alice DT_One (one t)
   (SRet (one yb)))))))).

(******************************************************************************)
(** * Session Type Duality Verification                                       *)
(******************************************************************************)

Variables (sa sb: VX) (ra yb: TX) (xa xb: VX).

(* Wrap processes in session-typed aproc for duality checking *)
Definition saproc_coserv := mk_aproc (pcoserv sa sb ra).
Definition saproc_alice := mk_aproc (palice xa).
Definition saproc_bob := mk_aproc (pbob xb yb).

(* Duality proofs - verified by computation *)
Lemma coserv_alice_dual : channels_dual saproc_coserv saproc_alice = true.
Proof. by native_compute. Qed.

Lemma coserv_bob_dual : channels_dual saproc_coserv saproc_bob = true.
Proof. by native_compute. Qed.

Lemma alice_bob_dual : channels_dual saproc_alice saproc_bob = true.
Proof. by native_compute. Qed.

(******************************************************************************)
(** * Interpreter Integration (via Erasure)                                   *)
(******************************************************************************)

(* Session-typed processes for duality checking and fuel computation *)
Definition smc_saprocs : seq (aproc sp_dtype data) :=
  [aprocs palice xa; pbob xb yb; pcoserv sa sb ra].

(* Erased processes for interpreter (strips session type indices) *)
Definition smc_procs : seq (proc data) :=
  erase_aprocs smc_saprocs.

Definition smc_scalar_product h :=
  interp h smc_procs (nseq 3 [::]).

(* Fuel bound computed from program structure: 8 + 9 + 8 = 25
   - palice: 8 (Init + 2*Recv + Send + 2*Recv + Ret=2)
   - pbob: 9 (2*Init + 2*Recv + Recv + Send + Send + Ret=2)
   - pcoserv: 8 (3*Init + 4*Send + Finish=1) *)
Definition smc_max_fuel : nat := 25.

(* Verify the computed fuel matches *)
Lemma smc_max_fuel_ok : smc_max_fuel = [> smc_saprocs].
Proof. reflexivity. Qed.

Definition smc_scalar_product_traces :=
  interp_traces [> smc_saprocs] smc_procs.

Definition smc_scalar_product_tracesT := smc_max_fuel.-bseq data.

Definition smc_scalar_product_party_tracesT :=
  3.-tuple smc_scalar_product_tracesT.

Definition is_scalar_product (trs: smc_scalar_product_party_tracesT) :=
  let '(ya, xa) :=
    if tnth trs 0 is Bseq [:: inl ya; _; _; _; _; inr xa] _ then (ya, xa)
    else (0,0) in
  let '(yb, xb) :=
    if tnth trs 1 is Bseq [:: inl yb; _; _; _; _; inr xb] _ then (yb, xb)
    else (0,0) in
  xa *d xb = ya + yb.

End scalar_product.
