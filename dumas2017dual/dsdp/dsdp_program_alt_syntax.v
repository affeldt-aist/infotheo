From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter smc_tactics.
Require Import smc_proba smc_session_types homomorphic_encryption.
Require Import dsdp_interface dsdp_program.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* DSDP Programs with Alternative Custom Syntax                               *)
(*                                                                            *)
(* This file provides paper-like syntax for DSDP protocol programs using      *)
(* Coq custom entries. Based on:                                              *)
(*                                                                            *)
(* Dumas, J. G., Lafourcade, P., Orfila, J. B., & Puys, M. (2017).            *)
(* Dual protocols for private multi-party matrix multiplication               *)
(* and trust computations.                                                    *)
(* Computers & security, 71, 51-70.                                           *)
(*                                                                            *)
(* Unicode characters and their ASCII fallbacks:                              *)
(*                                                                            *)
(* | Unicode          | ASCII fallback | Usage                                *)
(* |------------------|----------------|--------------------------------------*)
(* | · (U+00B7)       | ; (semicolon)  | Sequencing                           *)
(* | λ (U+03BB)       | fun x =>       | Lambda binder                        *)
(* | ⟨⟩ (U+27E8/E9)   | < >            | Send/Recv party brackets             *)
(* | 　 (U+3000)       | (x, y, z)      | Multi-var Init separator             *)
(*                                                                            *)
(* How to type Unicode characters:                                            *)
(*                                                                            *)
(* · Middle dot: macOS Option+Shift+9, or copy-paste: ·                       *)
(* λ Lambda: macOS Option+g on Greek keyboard, or copy-paste: λ               *)
(* ⟨⟩ Angle brackets: copy-paste: ⟨ ⟩                                         *)
(* 　 Full-width space: CJK input or Character Viewer, or copy-paste: 　       *)
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

Local Definition R := Rdefinitions.R.

Reserved Notation "u *h w" (at level 40).
Reserved Notation "u ^h w" (at level 40).

(******************************************************************************)
(** * Custom Syntax Declarations                                              *)
(******************************************************************************)

Declare Scope dsdp_scope.
Declare Custom Entry dsdp.

(* Entry/exit delimiters *)
Notation "{| e |}" := e (e custom dsdp at level 99) : dsdp_scope.

Local Open Scope dsdp_scope.

(******************************************************************************)
(** * DSDP Section with Programs                                              *)
(******************************************************************************)

Section dsdp.

(* Parameterize by a Party_AHE_scheme instance *)
Variable PHE : Party_AHE_scheme.

(* Use standard DSDP interface for data types *)
Let DI := Standard_DSDP_Interface PHE.

(* Extract types from the scheme *)
Let partyT := phe_party PHE.
Let msg := phe_msg PHE.
Let rand := phe_rand PHE.
Let enc := phe_enc PHE.
Let pkey := phe_pkey PHE.

(* Data type and constructors from interface *)
Let data := di_data DI.
Let d := di_d DI.
Let e := di_e DI.
Let k := di_k DI.

(* HE operations from the scheme - using @ to provide scheme explicitly *)
Let E := @phe_E PHE.
Let K := @phe_K PHE.
Let D := @phe_D PHE.
Let Emul := @pahe_Emul PHE.
Let Epow := @pahe_Epow PHE.

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

(* Local wrappers for session-typed proc constructors *)
Let DPSendEnc' {me n env} := @DPSendEnc PHE me n env.
Let DPInit' {me n env} := @DPInit PHE me n env.
Let DPRet' {me} := @DPRet PHE me.
Let DRecv_dec' {me n env} := @DRecv_dec PHE me n env.
Let DRecv_enc' {me n env} := @DRecv_enc PHE me n env.

(* Session-typed wrappers for notations *)
Definition PInit {me n env} (x : data) (p : @sproc dsdp_dtype data me n env) 
    : @sproc dsdp_dtype data me n.+1 env := DPInit' x p.
Definition PSend {me n env} (party_idx : nat) (x : enc)
    (p : @sproc dsdp_dtype data me n env)
    : @sproc dsdp_dtype data me n.+1 (senv_send env party_idx DT_Enc) := 
  DPSendEnc' party_idx x p.
Definition PRet {me} (x : data) : @sproc dsdp_dtype data me 2 senv_end := DPRet' x.
Let Recv_dec {me n env} (src_idx : nat) := DRecv_dec' src_idx.
Let Recv_enc {me n env} (src_idx : nat) := DRecv_enc' src_idx.

(** * Data wrapper shorthand notations *)

(* #x -> (k x) for key *)
Notation "# x" := (k x) (at level 0, x at level 0) : dsdp_scope.
(* &x -> (d x) for data/message *)
Notation "& x" := (d x) (at level 0, x at level 0) : dsdp_scope.
(* $x -> (e x) for encrypted *)
Notation "$ x" := (e x) (at level 0, x at level 0) : dsdp_scope.

(** * Basic custom syntax notations *)

(* Finish - terminal state (session-typed) *)
Notation "'Finish'" := SFinish (in custom dsdp at level 0).

(* Ret - return a value *)
Notation "'Ret' x" := (PRet x) 
  (in custom dsdp at level 80, x constr at level 0).

(* Fail - error state *)  
Notation "'Fail'" := Fail (in custom dsdp at level 0).

(** * Sequencing with · (middle dot) or ; (semicolon as ASCII fallback) *)

(* Multi-var Init using full-width space 　 (U+3000) - must be defined BEFORE single-var *)
Notation "'Init' x '　' .. '　' y · P" := (PInit x .. (PInit y P) ..)
  (in custom dsdp at level 85, 
   x constr at level 0, y constr at level 0,
   P custom dsdp at level 85, right associativity).
Notation "'Init' x '　' .. '　' y ; P" := (PInit x .. (PInit y P) ..)
  (in custom dsdp at level 85, 
   x constr at level 0, y constr at level 0,
   P custom dsdp at level 85, right associativity).

(* Multi-var Init using tuple syntax *)
Notation "'Init' '(' x ',' .. ',' y ')' · P" := (PInit x .. (PInit y P) ..)
  (in custom dsdp at level 85,
   x constr at level 0, y constr at level 0,
   P custom dsdp at level 85, right associativity).
Notation "'Init' '(' x ',' .. ',' y ')' ; P" := (PInit x .. (PInit y P) ..)
  (in custom dsdp at level 85,
   x constr at level 0, y constr at level 0,
   P custom dsdp at level 85, right associativity).

(* Single Init with continuation *)
Notation "'Init' x · P" := (PInit x P)
  (in custom dsdp at level 85, x constr at level 0,
   P custom dsdp at level 85, right associativity).
Notation "'Init' x ; P" := (PInit x P)
  (in custom dsdp at level 85, x constr at level 0,
   P custom dsdp at level 85, right associativity).


(** * Send with concrete party indices for session type tracking *)

(* Send - ASCII angle brackets *)
Notation "'Send<' p '>' x · P" := (PSend p x P)
  (in custom dsdp at level 85, p constr at level 0, x constr at level 0,
   P custom dsdp at level 85, right associativity).
Notation "'Send<' p '>' x ; P" := (PSend p x P)
  (in custom dsdp at level 85, p constr at level 0, x constr at level 0,
   P custom dsdp at level 85, right associativity).

(* Send - Unicode angle brackets *)
Notation "'Send⟨' p '⟩' x · P" := (PSend p x P)
  (in custom dsdp at level 85, p constr at level 0, x constr at level 0,
   P custom dsdp at level 85, right associativity).
Notation "'Send⟨' p '⟩' x ; P" := (PSend p x P)
  (in custom dsdp at level 85, p constr at level 0, x constr at level 0,
   P custom dsdp at level 85, right associativity).

(** * Specialized Recv operations with concrete party indices *)

(* Recv_dec notation - ASCII angle brackets *)
Notation "'Recv_dec<' p '>' dk 'λ' x · P" := (Recv_dec p dk (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, 
   dk constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
Notation "'Recv_dec<' p '>' dk 'λ' x ; P" := (Recv_dec p dk (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, 
   dk constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
(* Recv_dec with fun - ASCII fallback *)
Notation "'Recv_dec<' p '>' dk 'fun' x '=>' P" := (Recv_dec p dk (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, 
   dk constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(* Recv_dec notation - Unicode angle brackets *)
Notation "'Recv_dec⟨' p '⟩' dk 'λ' x · P" := (Recv_dec p dk (fun x => P))
  (in custom dsdp at level 85, p constr at level 0,
   dk constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
Notation "'Recv_dec⟨' p '⟩' dk 'λ' x ; P" := (Recv_dec p dk (fun x => P))
  (in custom dsdp at level 85, p constr at level 0,
   dk constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
(* Recv_dec with fun - Unicode brackets, ASCII fallback *)
Notation "'Recv_dec⟨' p '⟩' dk 'fun' x '=>' P" := (Recv_dec p dk (fun x => P))
  (in custom dsdp at level 85, p constr at level 0,
   dk constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(* Recv_enc notation - ASCII angle brackets *)
Notation "'Recv_enc<' p '>' 'λ' x · P" := (Recv_enc p (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
Notation "'Recv_enc<' p '>' 'λ' x ; P" := (Recv_enc p (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
(* Recv_enc with fun - ASCII fallback *)
Notation "'Recv_enc<' p '>' 'fun' x '=>' P" := (Recv_enc p (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(* Recv_enc notation - Unicode angle brackets *)
Notation "'Recv_enc⟨' p '⟩' 'λ' x · P" := (Recv_enc p (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
Notation "'Recv_enc⟨' p '⟩' 'λ' x ; P" := (Recv_enc p (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
(* Recv_enc with fun - Unicode brackets, ASCII fallback *)
Notation "'Recv_enc⟨' p '⟩' 'fun' x '=>' P" := (Recv_enc p (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(** * Variable reference *)
Notation "x" := x (in custom dsdp at level 0, x ident).

(******************************************************************************)
(** * DSDP Protocol Programs with Session Type Tracking                       *)
(** * Each encryption E(party, msg, rand) needs explicit randomness.          *)
(******************************************************************************)

(* Bob's protocol - using concrete indices for session type duality *)
Definition pbob (dk : pkey)(v2 : msg)(rb1 rb2 : rand) 
    : @sproc dsdp_dtype data bob_idx _ _ :=
  {| Init (#dk, &v2) ;
     Send<alice_idx> (E bob v2 rb1) ;
     Recv_dec<alice_idx> dk fun d2 =>
     Recv_enc<alice_idx> fun a3 =>
     Send<charlie_idx> (a3 *h (E charlie d2 rb2)) ;
     Finish |}.

(* Charlie's protocol *)
Definition pcharlie (dk : pkey)(v3 : msg)(rc1 rc2 : rand) 
    : @sproc dsdp_dtype data charlie_idx _ _ :=
  {| Init (#dk, &v3) ;
     Send<alice_idx> (E charlie v3 rc1) ;
     Recv_dec<bob_idx> dk fun d3 =>
     Send<alice_idx> (E alice d3 rc2) ;
     Finish |}.

(* Alice's protocol *)
Definition palice (dk : pkey)(v1 u1 u2 u3 r2 r3: msg)(ra1 ra2 : rand) 
    : @sproc dsdp_dtype data alice_idx _ _ :=
  {| Init (#dk, &v1, &u1, &u2, &u3, &r2, &r3) ;
     Recv_enc<bob_idx> fun c2 =>
     Recv_enc<charlie_idx> fun c3 =>
     Send<bob_idx> (c2 ^h u2 *h (E bob r2 ra1)) ;
     Send<bob_idx> (c3 ^h u3 *h (E charlie r3 ra2)) ;
     Recv_dec<charlie_idx> dk fun g =>
     Ret &(g - r2 - r3 + u1 * v1) |}.

(******************************************************************************)
(** * Session Type Duality Verification                                       *)
(******************************************************************************)

Variables (dk : pkey) (v1 u1 u2 u3 r2 r3 v2 v3 : msg) (ra1 ra2 rb1 rb2 rc1 rc2 : rand).

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

End dsdp.
