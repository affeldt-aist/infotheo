From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg ring.
From mathcomp Require Import Rstruct reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_proba smc_entropy.
Require Import smc_interpreter.

(**md**************************************************************************)
(* # SMC Program for the SMC Scalar Product Protocol                          *)
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
(*                                                                            *)
(* Formalization for:                                                         *)
(* A practical approach to solve secure multi-party computation problems      *)
(* Du, W., Zhan, J.Z.                                                         *)
(* In: Workshop on New Security Paradigms (NSPW 2002), Virginia Beach, VA, USA*)
(* September 23-26, 2002. pp. 127–135. ACM (2002).                            *)
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

Section scalar_product.
Variable m : nat.
Variable TX : finComRingType.
Variable VX : lmodType TX. (* vector is not ringType (mul)*)
Variable dotproduct : VX -> VX -> TX.
Local Notation "u *d w" := (dotproduct u w).

Definition alice : nat := 0.
Definition bob : nat := 1.
Definition coserv : nat := 2.

Definition data := (TX + VX)%type.
Definition one x : data := inl x.
Definition vec x : data := inr x.

(* Recv wrappers for fuel-indexed proc type *)
Definition Recv_one {n} frm (f : TX -> proc data n) : proc data n.+1 :=
  Recv frm (fun x => if x is inl v then f v else Fail).
Definition Recv_vec {n} frm (f : VX -> proc data n) : proc data n.+1 :=
  Recv frm (fun x => if x is inr v then f v else Fail).

(* Fuel is automatically inferred via _ *)
Definition pcoserv (sa sb: VX) (ra : TX) : proc data _ :=
  Init (vec sa) (
  Init (vec sb) (
  Init (one ra) (
  Send alice (vec sa) (
  Send alice (one ra) (
  Send bob (vec sb) (
  Send bob (one (sa *d sb - ra)) Finish)))))).

Definition palice (xa : VX) : proc data _ :=
  Init (vec xa) (
  Recv_vec coserv (fun sa =>
  Recv_one coserv (fun ra =>
  Send bob (vec (xa + sa)) (
  Recv_vec bob (fun xb' =>
  Recv_one bob (fun t =>
  Ret (one (t - (xb' *d sa) + ra)))))))).

Definition pbob (xb : VX) (yb : TX) : proc data _ :=
  Init (vec xb) (
  Init (one yb) (
  Recv_vec coserv (fun sb =>
  Recv_one coserv (fun rb =>
  Recv_vec alice (fun xa' =>
  let t := xa' *d xb + rb - yb in
    Send alice (vec (xb + sb))
    (Send alice (one t) (Ret (one yb)))))))).

Variables (sa sb: VX) (ra yb: TX) (xa xb: VX).

(* Pack processes into aproc list using [procs ...] notation *)
Definition smc_procs : seq (aproc data) :=
  [procs palice xa; pbob xb yb; pcoserv sa sb ra].

Definition smc_scalar_product h :=
  interp h smc_procs (nseq 3 [::]).

(* Fuel bound computed from program structure: 8 + 9 + 8 = 25
   - palice: 8 (Init + 2*Recv + Send + 2*Recv + Ret=2)
   - pbob: 9 (2*Init + 2*Recv + Recv + Send + Send + Ret=2)
   - pcoserv: 8 (3*Init + 4*Send + Finish=1) *)
Definition smc_max_fuel : nat := 25.

(* Verify the computed fuel matches *)
Lemma smc_max_fuel_ok : smc_max_fuel = [> smc_procs].
Proof. reflexivity. Qed.

Definition smc_scalar_product_traces :=
  interp_traces [> smc_procs] smc_procs.

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

