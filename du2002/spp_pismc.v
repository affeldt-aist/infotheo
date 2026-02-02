From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import spp_proba spp_entropy.
Require Import smc_interpreter smc_session_types pismc.
Require Import spp_interface spp_program spp_session_types.

Local Open Scope pismc_scope.
Local Open Scope ring_scope.

Section spp_pismc_programs.

Variable m : nat.
Variable TX : finComRingType.
Variable VX : lmodType TX. (* vector is not ringType (mul)*)
Variable dotproduct : VX -> VX -> TX.
Local Notation "u *d w" := (dotproduct u w).
Let data := @spp_interface.data TX VX.
Let alice := @spp_interface.alice.
Let bob := @spp_interface.bob.
Let coserv := @spp_interface.coserv.
Let one := @spp_interface.one TX VX.
Let vec := @spp_interface.vec TX VX.

Let SRecv_one {TX VX party n env} := @spp_interface.SRecv_one TX VX party n env.
Let SRecv_vec {TX VX party n env} := @spp_interface.SRecv_vec TX VX party n env.
Let SPSendVec {TX VX party n env} := @spp_interface.SPSendVec TX VX party n env.
Let SPSendOne {TX VX party n env} := @spp_interface.SPSendOne TX VX party n env.
Let SPInit {TX VX party n env} := @spp_interface.SPInit TX VX party n env.
Let SPRet {party} := @spp_interface.SPRet TX VX party.

(* Data wrapper shorthand notations - in standard scope, not custom entry *)
(* These must be in standard scope so Init ( &x, !y ) works with constr parsing *)
Local Notation "& x" := (vec x) (at level 0, x at level 0) : pismc_scope.
Local Notation "! x" := (one x) (at level 0, x at level 0) : pismc_scope.

Local Notation "'Send<' p '>' '&' x ; P" := (SPSendVec p x P)
  (in custom pismc at level 85, p constr at level 0, x constr at level 0,
   P custom pismc at level 85, right associativity).

Local Notation "'Send<' p '>' '!' x ; P" := (SPSendOne p x P)
  (in custom pismc at level 85, p constr at level 0, x constr at level 0,
   P custom pismc at level 85, right associativity).

(* Protocol-specific Recv notations *)
Local Notation "'Recv_vec<' p '>' 'fun' x '=>' P" :=
  (SRecv_vec p (fun x => P))
  (in custom pismc at level 85, p constr at level 0, x name,
   P custom pismc at level 85, right associativity).

Local Notation "'Recv_one<' p '>' 'fun' x '=>' P" :=
  (SRecv_one p (fun x => P))
  (in custom pismc at level 85, p constr at level 0, x name,
   P custom pismc at level 85, right associativity).

(* Return notation for scalar values *)
Local Notation "'Ret' '!' x" := (SRet (one x))
  (in custom pismc at level 80, x constr).
Local Notation "'Ret' '&' x" := (SRet (vec x))
  (in custom pismc at level 80, x constr).

(* Finish notation *)
Local Notation "'Finish'" := SFinish (in custom pismc at level 0).

(* Single Init with continuation *)
Notation "'Init' '&' x ; P" := (SPInit (vec x) P)
  (in custom pismc at level 85, x constr at level 0,
   P custom pismc at level 85, right associativity).
Notation "'Init' '!' x ; P" := (SPInit (one x) P)
  (in custom pismc at level 85, x constr at level 0,
   P custom pismc at level 85, right associativity).

(* Multi-var Init using tuple syntax - data values directly *)
(* x and y are parsed in constr where &/! notations are defined in pismc_scope *)
Local Notation "'Init' '(' x ',' .. ',' y ')' ; P" :=
  (SPInit x .. (SPInit y P) ..)
  (in custom pismc at level 85,
   x constr at level 0, y constr at level 0,
   P custom pismc at level 85, right associativity).


(******************************************************************************)
(** * SMC-SPP Programs - piSMC Version                                        *)
(******************************************************************************)

(* Commodity server's protocol - piSMC version with session types *)
(* Fuel and session environment automatically inferred *)
Definition pcoserv (sa sb: VX) (ra : TX) : @sproc sp_dtype data coserv _ _ :=
 pi{ Init (&sa, &sb, !ra) ;
     Send<alice> &sa ;
     Send<alice> !ra ;
     Send<bob> &sb ;
     Send<bob> !(sa *d sb - ra) ;
     Finish }.

(* Alice's protocol - piSMC version with session types *)
Definition palice (xa : VX) : @sproc sp_dtype data alice _ _ :=
 pi{ Init &xa ;
     Recv_vec<coserv> fun sa =>
     Recv_one<coserv> fun ra =>
     Send<bob> &(xa + sa) ;
     Recv_vec<bob> fun xb' =>
     Recv_one<bob> fun t =>
     Ret !(t - (xb' *d sa) + ra) }.

(* Bob's protocol - piSMC version with session types *)
Definition pbob (xb : VX) (yb : TX) : @sproc sp_dtype data bob _ _ :=
 pi{ Init (&xb, !yb) ;
     Recv_vec<coserv> fun sb =>
     Recv_one<coserv> fun rb =>
     Recv_vec<alice> fun xa' =>
     Send<alice> &(xb + sb) ;
     Send<alice> !(xa' *d xb + rb - yb) ;
     Ret !yb }.

(* Import original program definitions from spp_program *)
Let pcoserv_orig := @spp_program.pcoserv TX VX dotproduct.
Let palice_orig := @spp_program.palice TX VX dotproduct.
Let pbob_orig := @spp_program.pbob TX VX dotproduct.

About spp_program.palice.

(* Prove that alt_syntax programs equal the original programs! *)
(* This works because both use the same types from spp_interface *)
Lemma pcoserv_cross_eq sa sb ra : 
  pcoserv sa sb ra = pcoserv_orig sa sb ra.
Proof. reflexivity. Qed.

Lemma palice_cross_eq xa : 
  palice xa = palice_orig xa.
Proof. reflexivity. Qed.

Lemma pbob_cross_eq xb yb : 
  pbob xb yb = pbob_orig xb yb.
Proof. reflexivity. Qed.

(******************************************************************************)
(** * Session Type Duality Verification                                       *)
(******************************************************************************)

Variables (sa sb: VX) (ra yb: TX) (xa xb: VX).

(* Wrap in aproc for duality checking *)
Definition saproc_coserv := mk_aproc (pcoserv sa sb ra).
Definition saproc_alice := mk_aproc (palice xa).
Definition saproc_bob := mk_aproc (pbob xb yb).

(* Duality proofs - verified by computation *)
Lemma coserv_alice_dual : channels_dual saproc_coserv saproc_alice.
Proof. by native_compute. Qed.

Lemma coserv_bob_dual : channels_dual saproc_coserv saproc_bob.
Proof. by native_compute. Qed.

Lemma alice_bob_dual : channels_dual saproc_alice saproc_bob.
Proof. by native_compute. Qed.

(******************************************************************************)
(** * Interpreter Integration                                                 *)
(******************************************************************************)

Local Open Scope sproc_scope.
Local Open Scope proc_scope.

(* Session-typed processes for duality checking and fuel computation *)
Definition spp_saprocs : seq (aproc sp_dtype data) :=
  [aprocs palice xa; pbob xb yb; pcoserv sa sb ra].

(* Erased processes for interpreter (strips session type indices) *)
Definition spp_procs : seq (proc data) :=
  erase_aprocs spp_saprocs.

(* Fuel bound computed from program structure: 8 + 9 + 8 = 25
   - palice: 8 (Init + 2*Recv + Send + 2*Recv + Ret=2)
   - pbob: 9 (2*Init + 2*Recv + Recv + Send + Send + Ret=2)
   - pcoserv: 8 (3*Init + 4*Send + Finish=1) *)
Lemma spp_max_fuel_ok : [> spp_saprocs] = 25.
Proof. reflexivity. Qed.

(*******************************************************************************)
(** * Session Environment Convergence for SPP                                   *)
(*******************************************************************************)

(* SPP-specific: after interpretation, all processes are terminal (Finish, Ret, or Fail).

   For SPP with co-dual session types and sufficient fuel, interpretation
   terminates with all processes in their final state. *)
Lemma spp_terminates traces :
  all_terminated (interp [> spp_saprocs] spp_procs traces).1.
Proof. by native_compute. Qed.

(* SPP-specific: after interpretation, no process is Fail.

   This follows from the structure of SPP programs:
   - None of the programs (pcoserv, palice, pbob) use SFail explicitly
   - The programs use direct SRecv, not SRecv_check (which could fail)
   - All channels are co-dual, so communications always match

   Therefore, no SFail can appear in the final state. *)
Lemma spp_no_fail traces :
  all_nonfail (interp [> spp_saprocs] spp_procs traces).1.
Proof. by native_compute. Qed.

(* Main theorem: SPP session environment converges to empty.

   Combines the general terminated_nonfail_senv_zero lemma with
   SPP-specific termination and no-fail properties. *)
Theorem spp_senv_zero traces :
  exists aps' : seq (aproc sp_dtype data),
    erase_aprocs aps' = (interp [> spp_saprocs] spp_procs traces).1 /\
    aprocs_senv_depth [:: 0; 1; 2] aps' = 0.
Proof.
(* Use senv_bounded to get annotated processes for the final state *)
have [aps' [Hsz [Herase Hsenv]]] :=
  @senv_bounded _ _ [:: 0; 1; 2] [> spp_saprocs] spp_saprocs traces (leqnn _).
exists aps'.
split; first exact: Herase.
(* Apply terminated_nonfail_senv_zero: need all_terminated and all_nonfail *)
apply: terminated_nonfail_senv_zero.
- (* all_terminated: rewrite using Herase and apply spp_terminates *)
  by rewrite Herase; exact: spp_terminates.
- (* all_nonfail: rewrite using Herase and apply spp_no_fail *)
  by rewrite Herase; exact: spp_no_fail.
Qed.

End spp_pismc_programs.
