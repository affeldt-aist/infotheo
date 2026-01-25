From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg ring.
From mathcomp Require Import Rstruct reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_proba smc_entropy.
Require Import smc_interpreter smc_session_types.
Require Import scalar_product_interface scalar_product_program.

(**md**************************************************************************)
(* # SMC Scalar Product Protocol - Alternative Syntax with Session Types      *)
(*                                                                            *)
(* This file contains the same protocol definitions as scalar_product_program *)
(* but written using a custom syntax for improved readability.                *)
(* Now with session type verification!                                        *)
(*                                                                            *)
(* Unicode vs ASCII Fallback Table:                                           *)
(*                                                                            *)
(* | Unicode         | ASCII Fallback   | Description                      |  *)
(* |-----------------|------------------|----------------------------------|  *)
(* | ·               | ;                | Sequencing operator              |  *)
(* | λ x ·           | fun x =>         | Lambda binder                    |  *)
(* | ⟨n⟩             | <n>              | Party angle brackets             |  *)
(* | x　y　z          | (x, y, z)        | Multi-var Init separator         |  *)
(*                                                                            *)
(* Data Wrapper Notations:                                                    *)
(*   &x  ->  sends vector x with DT_Vec (via SPSendVec)                       *)
(*   !x  ->  sends scalar x with DT_One (via SPSendOne)                       *)
(*                                                                            *)
(* How to type Unicode characters:                                            *)
(*   · Middle dot: macOS Option+Shift+9, or copy-paste: ·                     *)
(*   λ Lambda: macOS Option+g on Greek keyboard, or copy-paste: λ             *)
(*   ⟨⟩ Angle brackets: copy-paste: ⟨ ⟩                                       *)
(*   　 Full-width space: CJK input or Character Viewer, or copy-paste: 　     *)
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

(******************************************************************************)
(** * Custom Syntax Declarations                                              *)
(******************************************************************************)

Declare Scope smc_scope.
Declare Custom Entry smc.

(* Entry/exit delimiters *)
Notation "'{|' e '|}'" := e (e custom smc at level 99) : smc_scope.

Local Open Scope smc_scope.

(******************************************************************************)
(** * Scalar Product Section with Session-Typed Programs                      *)
(******************************************************************************)

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
Let SPSendVec := @scalar_product_interface.SPSendVec TX VX.
Let SPSendOne := @scalar_product_interface.SPSendOne TX VX.
Let SPInit := @scalar_product_interface.SPInit TX VX.
Let SPRet := @scalar_product_interface.SPRet TX VX.

(** * Data wrapper shorthand notations (used in Init and Ret) *)

(* !x -> (one x) for scalar - "exactly one" *)
Notation "! x" := (one x) (at level 0, x at level 0) : smc_scope.
(* &x -> (vec x) for vector - "collection" *)
Notation "& x" := (vec x) (at level 0, x at level 0) : smc_scope.

(** * Basic custom syntax notations *)

(* Finish - terminal state *)
Notation "'Finish'" := SFinish (in custom smc at level 0).

(* Ret - return a value with explicit wrapper *)
(* Use @SPRet _ to explicitly mark 'me' as inference hole *)
Notation "'Ret_one' x" := (@SPRet _ (one x)) 
  (in custom smc at level 80, x constr).
Notation "'Ret_vec' x" := (@SPRet _ (vec x)) 
  (in custom smc at level 80, x constr).

(* Fail - error state *)  
Notation "'Fail'" := SFail (in custom smc at level 0).

(** * Sequencing with · (middle dot) or ; (semicolon as ASCII fallback) *)

(* Multi-var Init using tuple syntax - data values directly *)
Notation "'Init' '(' x ',' .. ',' y ')' · P" := (SPInit x .. (SPInit y P) ..)
  (in custom smc at level 85,
   x constr at level 0, y constr at level 0,
   P custom smc at level 85, right associativity).
Notation "'Init' '(' x ',' .. ',' y ')' ; P" := (SPInit x .. (SPInit y P) ..)
  (in custom smc at level 85,
   x constr at level 0, y constr at level 0,
   P custom smc at level 85, right associativity).

(* Single Init with continuation *)
Notation "'Init' '&' x · P" := (SPInit (vec x) P)
  (in custom smc at level 85, x constr at level 0,
   P custom smc at level 85, right associativity).
Notation "'Init' '!' x · P" := (SPInit (one x) P)
  (in custom smc at level 85, x constr at level 0,
   P custom smc at level 85, right associativity).
Notation "'Init' '&' x ; P" := (SPInit (vec x) P)
  (in custom smc at level 85, x constr at level 0,
   P custom smc at level 85, right associativity).
Notation "'Init' '!' x ; P" := (SPInit (one x) P)
  (in custom smc at level 85, x constr at level 0,
   P custom smc at level 85, right associativity).

(** * Send with automatic dtype from & or ! *)

(* Send vector - ASCII angle brackets *)
Notation "'Send<' p '>' '&' x · P" := (SPSendVec p x P)
  (in custom smc at level 85, p constr at level 0, x constr at level 0,
   P custom smc at level 85, right associativity).
Notation "'Send<' p '>' '&' x ; P" := (SPSendVec p x P)
  (in custom smc at level 85, p constr at level 0, x constr at level 0,
   P custom smc at level 85, right associativity).

(* Send scalar - ASCII angle brackets *)
Notation "'Send<' p '>' '!' x · P" := (SPSendOne p x P)
  (in custom smc at level 85, p constr at level 0, x constr at level 0,
   P custom smc at level 85, right associativity).
Notation "'Send<' p '>' '!' x ; P" := (SPSendOne p x P)
  (in custom smc at level 85, p constr at level 0, x constr at level 0,
   P custom smc at level 85, right associativity).

(* Send vector - Unicode angle brackets *)
Notation "'Send⟨' p '⟩' '&' x · P" := (SPSendVec p x P)
  (in custom smc at level 85, p constr at level 0, x constr at level 0,
   P custom smc at level 85, right associativity).
Notation "'Send⟨' p '⟩' '&' x ; P" := (SPSendVec p x P)
  (in custom smc at level 85, p constr at level 0, x constr at level 0,
   P custom smc at level 85, right associativity).

(* Send scalar - Unicode angle brackets *)
Notation "'Send⟨' p '⟩' '!' x · P" := (SPSendOne p x P)
  (in custom smc at level 85, p constr at level 0, x constr at level 0,
   P custom smc at level 85, right associativity).
Notation "'Send⟨' p '⟩' '!' x ; P" := (SPSendOne p x P)
  (in custom smc at level 85, p constr at level 0, x constr at level 0,
   P custom smc at level 85, right associativity).

(** * Recv_one and Recv_vec operations *)

(* Recv_one - ASCII angle brackets *)
Notation "'Recv_one<' p '>' 'λ' x · P" := (SRecv_one p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_one<' p '>' 'λ' x ; P" := (SRecv_one p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_one<' p '>' 'fun' x '=>' P" := (SRecv_one p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).

(* Recv_one - Unicode angle brackets *)
Notation "'Recv_one⟨' p '⟩' 'λ' x · P" := (SRecv_one p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_one⟨' p '⟩' 'λ' x ; P" := (SRecv_one p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_one⟨' p '⟩' 'fun' x '=>' P" := (SRecv_one p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).

(* Recv_vec - ASCII angle brackets *)
Notation "'Recv_vec<' p '>' 'λ' x · P" := (SRecv_vec p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_vec<' p '>' 'λ' x ; P" := (SRecv_vec p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_vec<' p '>' 'fun' x '=>' P" := (SRecv_vec p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).

(* Recv_vec - Unicode angle brackets *)
Notation "'Recv_vec⟨' p '⟩' 'λ' x · P" := (SRecv_vec p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_vec⟨' p '⟩' 'λ' x ; P" := (SRecv_vec p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_vec⟨' p '⟩' 'fun' x '=>' P" := (SRecv_vec p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).

(** * Variable reference *)
Notation "x" := x (in custom smc at level 0, x ident).

(******************************************************************************)
(** * Scalar Product Protocol Programs - Unicode Version                      *)
(******************************************************************************)

(* Commodity server's protocol - Unicode version with session types *)
(* Fuel and session environment automatically inferred *)
(* Note: No explicit [DT_Vec] or [DT_One] needed - & and ! determine dtype! *)
Definition pcoserv (sa sb: VX) (ra : TX) : @sproc sp_dtype data coserv _ _ :=
  {| Init (&sa, &sb, !ra) ·
     Send⟨alice⟩ &sa ·
     Send⟨alice⟩ !ra ·
     Send⟨bob⟩ &sb ·
     Send⟨bob⟩ !(sa *d sb - ra) ·
     Finish |}.

(* Alice's protocol - Unicode version with session types *)
Definition palice (xa : VX) : @sproc sp_dtype data alice _ _ :=
  {| Init &xa ·
     Recv_vec⟨coserv⟩ λ sa ·
     Recv_one⟨coserv⟩ λ ra ·
     Send⟨bob⟩ &(xa + sa) ·
     Recv_vec⟨bob⟩ λ xb' ·
     Recv_one⟨bob⟩ λ t ·
     Ret_one (t - (xb' *d sa) + ra) |}.

(* Bob's protocol - Unicode version with session types *)
Definition pbob (xb : VX) (yb : TX) : @sproc sp_dtype data bob _ _ :=
  {| Init (&xb, !yb) ·
     Recv_vec⟨coserv⟩ λ sb ·
     Recv_one⟨coserv⟩ λ rb ·
     Recv_vec⟨alice⟩ λ xa' ·
     Send⟨alice⟩ &(xb + sb) ·
     Send⟨alice⟩ !(xa' *d xb + rb - yb) ·
     Ret_one yb |}.

(******************************************************************************)
(** * Scalar Product Protocol Programs - ASCII Version                        *)
(******************************************************************************)

(* Commodity server's protocol - ASCII version with session types *)
Definition pcoserv_ascii (sa sb: VX) (ra : TX) : @sproc sp_dtype data coserv _ _ :=
  {| Init (&sa, &sb, !ra) ;
     Send<alice> &sa ;
     Send<alice> !ra ;
     Send<bob> &sb ;
     Send<bob> !(sa *d sb - ra) ;
     Finish |}.

(* Alice's protocol - ASCII version with session types *)
Definition palice_ascii (xa : VX) : @sproc sp_dtype data alice _ _ :=
  {| Init &xa ;
     Recv_vec<coserv> fun sa =>
     Recv_one<coserv> fun ra =>
     Send<bob> &(xa + sa) ;
     Recv_vec<bob> fun xb' =>
     Recv_one<bob> fun t =>
     Ret_one (t - (xb' *d sa) + ra) |}.

(* Bob's protocol - ASCII version with session types *)
Definition pbob_ascii (xb : VX) (yb : TX) : @sproc sp_dtype data bob _ _ :=
  {| Init (&xb, !yb) ;
     Recv_vec<coserv> fun sb =>
     Recv_one<coserv> fun rb =>
     Recv_vec<alice> fun xa' =>
     Send<alice> &(xb + sb) ;
     Send<alice> !(xa' *d xb + rb - yb) ;
     Ret_one yb |}.

(* Verify ASCII and Unicode versions are equivalent *)
Lemma pcoserv_ascii_eq sa sb ra : pcoserv sa sb ra = pcoserv_ascii sa sb ra.
Proof. reflexivity. Qed.

Lemma palice_ascii_eq xa : palice xa = palice_ascii xa.
Proof. reflexivity. Qed.

Lemma pbob_ascii_eq xb yb : pbob xb yb = pbob_ascii xb yb.
Proof. reflexivity. Qed.

(******************************************************************************)
(** * Cross-file Equality: alt_syntax = scalar_product_program                *)
(******************************************************************************)

(* Import original program definitions from scalar_product_program *)
Let pcoserv_orig := @scalar_product_program.pcoserv TX VX dotproduct.
Let palice_orig := @scalar_product_program.palice TX VX dotproduct.
Let pbob_orig := @scalar_product_program.pbob TX VX dotproduct.

(* Prove that alt_syntax programs equal the original programs! *)
(* This works because both use the same types from scalar_product_interface *)
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
Lemma coserv_alice_dual : channels_dual saproc_coserv saproc_alice = true.
Proof. by native_compute. Qed.

Lemma coserv_bob_dual : channels_dual saproc_coserv saproc_bob = true.
Proof. by native_compute. Qed.

Lemma alice_bob_dual : channels_dual saproc_alice saproc_bob = true.
Proof. by native_compute. Qed.

(******************************************************************************)
(** * Interpreter Integration                                                 *)
(******************************************************************************)

Local Open Scope sproc_scope.
Local Open Scope proc_scope.

(* Pack session-typed processes into erased aproc list for interpreter *)
Definition smc_procs : seq (smc_interpreter.aproc data) :=
  [sprocs palice xa; pbob xb yb; pcoserv sa sb ra].

(* Fuel bound: 8 + 9 + 8 = 25 *)
Lemma smc_max_fuel_ok : [> smc_procs] = 25.
Proof. reflexivity. Qed.

End scalar_product.
