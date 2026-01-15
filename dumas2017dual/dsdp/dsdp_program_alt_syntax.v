From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter smc_tactics.
Require Import smc_proba homomorphic_encryption.

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

Variable F : finFieldType.
Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Hypothesis prime_m : prime m.

Local Notation msg := 'F_m.  (* Finite field with m elements *)
Let card_msg : #|msg| = m.
Proof. by rewrite card_Fp // pdiv_id. Qed.

Let enc := enc party msg.
Let pkey := pkey party msg.

Notation "u *h w" := (Emul u w).
Notation "u ^h w" := (Epow u w).

Definition alice : party := Alice.
Definition bob : party := Bob.
Definition charlie : party := Charlie.

Definition data := (msg + enc + pkey)%type.
Definition d x : data := inl (inl x).
Definition e x : data := inl (inr x).
Definition k x : data := inr x.

(* Local wrappers for proc constructors - fuel-indexed *)
Definition PInit {n} (x : data) (p : proc data n) : proc data n.+1 := Init x p.
Definition PSend {n} (party : nat) (x : data) (p : proc data n) : proc data n.+1 := Send party x p.
Definition PRecv {n} (party : nat) (f : data -> proc data n) : proc data n.+1 := Recv party f.
Definition PRet (x : data) : proc data 2 := Ret x.

(** * Data wrapper shorthand notations *)

(* #x -> (k x) for key *)
Notation "# x" := (k x) (at level 0, x at level 0) : dsdp_scope.
(* &x -> (d x) for data/message *)
Notation "& x" := (d x) (at level 0, x at level 0) : dsdp_scope.
(* $x -> (e x) for encrypted *)
Notation "$ x" := (e x) (at level 0, x at level 0) : dsdp_scope.

(** * Basic custom syntax notations *)

(* Finish - terminal state *)
Notation "'Finish'" := Finish (in custom dsdp at level 0).

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


(** * Send/Recv with implicit n(...) in angle brackets *)

(* Send - ASCII angle brackets, implicit n(...) *)
Notation "'Send<' p '>' x · P" := (PSend n(p) x P)
  (in custom dsdp at level 85, p constr at level 0, x constr at level 0,
   P custom dsdp at level 85, right associativity).
Notation "'Send<' p '>' x ; P" := (PSend n(p) x P)
  (in custom dsdp at level 85, p constr at level 0, x constr at level 0,
   P custom dsdp at level 85, right associativity).

(* Send - Unicode angle brackets, implicit n(...) *)
Notation "'Send⟨' p '⟩' x · P" := (PSend n(p) x P)
  (in custom dsdp at level 85, p constr at level 0, x constr at level 0,
   P custom dsdp at level 85, right associativity).
Notation "'Send⟨' p '⟩' x ; P" := (PSend n(p) x P)
  (in custom dsdp at level 85, p constr at level 0, x constr at level 0,
   P custom dsdp at level 85, right associativity).

(* Recv with λ binder - ASCII angle brackets *)
Notation "'Recv<' p '>' 'λ' x · P" := (PRecv n(p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
Notation "'Recv<' p '>' 'λ' x ; P" := (PRecv n(p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
(* Recv with fun binder - ASCII angle brackets, ASCII fallback *)
Notation "'Recv<' p '>' 'fun' x '=>' P" := (PRecv n(p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(* Recv with λ binder - Unicode angle brackets *)
Notation "'Recv⟨' p '⟩' 'λ' x · P" := (PRecv n(p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
Notation "'Recv⟨' p '⟩' 'λ' x ; P" := (PRecv n(p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
(* Recv with fun binder - Unicode angle brackets, ASCII fallback *)
Notation "'Recv⟨' p '⟩' 'fun' x '=>' P" := (PRecv n(p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(** * Specialized Recv operations *)

(* Recv_dec: receive encrypted, decrypt with key, continue with decrypted value - fuel-indexed *)
Definition Recv_dec {n} frm pkey (f : msg -> proc data n) : proc data n.+1 :=
  Recv frm (fun x => if x is inl (inr v) then
                       if D pkey v is Some v' then f v' else Fail
                     else Fail).

(* Recv_enc: receive encrypted (cannot decrypt), do HE computation - fuel-indexed *)
Definition Recv_enc {n} frm (f : enc -> proc data n) : proc data n.+1 :=
  Recv frm (fun x => if x is inl (inr v) then f v else Fail).

(* Recv_dec notation - ASCII angle brackets, implicit n(...) *)
Notation "'Recv_dec<' p '>' dk 'λ' x · P" := (Recv_dec n(p) dk (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, 
   dk constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
Notation "'Recv_dec<' p '>' dk 'λ' x ; P" := (Recv_dec n(p) dk (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, 
   dk constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
(* Recv_dec with fun - ASCII fallback *)
Notation "'Recv_dec<' p '>' dk 'fun' x '=>' P" := (Recv_dec n(p) dk (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, 
   dk constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(* Recv_dec notation - Unicode angle brackets, implicit n(...) *)
Notation "'Recv_dec⟨' p '⟩' dk 'λ' x · P" := (Recv_dec n(p) dk (fun x => P))
  (in custom dsdp at level 85, p constr at level 0,
   dk constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
Notation "'Recv_dec⟨' p '⟩' dk 'λ' x ; P" := (Recv_dec n(p) dk (fun x => P))
  (in custom dsdp at level 85, p constr at level 0,
   dk constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
(* Recv_dec with fun - Unicode brackets, ASCII fallback *)
Notation "'Recv_dec⟨' p '⟩' dk 'fun' x '=>' P" := (Recv_dec n(p) dk (fun x => P))
  (in custom dsdp at level 85, p constr at level 0,
   dk constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(* Recv_enc notation - ASCII angle brackets, implicit n(...) *)
Notation "'Recv_enc<' p '>' 'λ' x · P" := (Recv_enc n(p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
Notation "'Recv_enc<' p '>' 'λ' x ; P" := (Recv_enc n(p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
(* Recv_enc with fun - ASCII fallback *)
Notation "'Recv_enc<' p '>' 'fun' x '=>' P" := (Recv_enc n(p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(* Recv_enc notation - Unicode angle brackets, implicit n(...) *)
Notation "'Recv_enc⟨' p '⟩' 'λ' x · P" := (Recv_enc n(p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
Notation "'Recv_enc⟨' p '⟩' 'λ' x ; P" := (Recv_enc n(p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
(* Recv_enc with fun - Unicode brackets, ASCII fallback *)
Notation "'Recv_enc⟨' p '⟩' 'fun' x '=>' P" := (Recv_enc n(p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(** * Variable reference *)
Notation "x" := x (in custom dsdp at level 0, x ident).

(******************************************************************************)
(** * DSDP Protocol Programs - Unicode Version                                *)
(******************************************************************************)

(* Bob's protocol - Unicode version, fuel auto-inferred *)
Definition pbob (dk : pkey)(v2 : msg) : proc data _ :=
  {| Init #dk　&v2 ·
     Send⟨alice⟩ $(E bob v2) ·
     Recv_dec⟨alice⟩ dk λ d2 ·
     Recv_enc⟨alice⟩ λ a3 ·
     Send⟨charlie⟩ $(a3 *h (E charlie d2)) ·
     Finish |}.

(* Charlie's protocol - Unicode version *)
Definition pcharlie (dk : pkey)(v3 : msg) : proc data _ :=
  {| Init #dk　&v3 ·
     Send⟨alice⟩ $(E charlie v3) ·
     Recv_dec⟨bob⟩ dk λ d3 ·
     Send⟨alice⟩ $(E alice d3) ·
     Finish |}.

(* Alice's protocol - Unicode version *)
Definition palice (dk : pkey)(v1 u1 u2 u3 r2 r3: msg) : proc data _ :=
  {| Init #dk　&v1　&u1　&u2　&u3　&r2　&r3 ·
     Recv_enc⟨bob⟩ λ c2 ·
     Recv_enc⟨charlie⟩ λ c3 ·
     Send⟨bob⟩ $(c2 ^h u2 *h (E bob r2)) ·
     Send⟨bob⟩ $(c3 ^h u3 *h (E charlie r3)) ·
     Recv_dec⟨charlie⟩ dk λ g ·
     Ret &(g - r2 - r3 + u1 * v1) |}.

(******************************************************************************)
(** * DSDP Protocol Programs - ASCII Version                                  *)
(******************************************************************************)

(* Bob's protocol - ASCII version *)
Definition pbob_ascii (dk : pkey)(v2 : msg) : proc data _ :=
  {| Init (#dk, &v2) ;
     Send<alice> $(E bob v2) ;
     Recv_dec<alice> dk fun d2 =>
     Recv_enc<alice> fun a3 =>
     Send<charlie> $(a3 *h (E charlie d2)) ;
     Finish |}.

(* Charlie's protocol - ASCII version *)
Definition pcharlie_ascii (dk : pkey)(v3 : msg) : proc data _ :=
  {| Init (#dk, &v3) ;
     Send<alice> $(E charlie v3) ;
     Recv_dec<bob> dk fun d3 =>
     Send<alice> $(E alice d3) ;
     Finish |}.

(* Alice's protocol - ASCII version *)
Definition palice_ascii (dk : pkey)(v1 u1 u2 u3 r2 r3: msg) : proc data _ :=
  {| Init (#dk, &v1, &u1, &u2, &u3, &r2, &r3) ;
     Recv_enc<bob> fun c2 =>
     Recv_enc<charlie> fun c3 =>
     Send<bob> $(c2 ^h u2 *h (E bob r2)) ;
     Send<bob> $(c3 ^h u3 *h (E charlie r3)) ;
     Recv_dec<charlie> dk fun g =>
     Ret &(g - r2 - r3 + u1 * v1) |}.

(* Verify ASCII and Unicode versions are equivalent *)
Lemma pbob_ascii_eq dk v2 : pbob dk v2 = pbob_ascii dk v2.
Proof. reflexivity. Qed.

Lemma pcharlie_ascii_eq dk v3 : pcharlie dk v3 = pcharlie_ascii dk v3.
Proof. reflexivity. Qed.

Lemma palice_ascii_eq dk v1 u1 u2 u3 r2 r3 : 
  palice dk v1 u1 u2 u3 r2 r3 = palice_ascii dk v1 u1 u2 u3 r2 r3.
Proof. reflexivity. Qed.

(******************************************************************************)
(** * Equivalence with original definitions                                   *)
(******************************************************************************)

Local Close Scope dsdp_scope.

(* Verify pbob expands to the original nested structure *)
Lemma pbob_eq dk v2 : pbob dk v2 = 
  PInit (k dk) (
  PInit (d v2) (
  PSend n(alice) (e (E bob v2)) (
  Recv_dec n(alice) dk (fun d2 =>
  Recv_enc n(alice) (fun a3 =>
    PSend n(charlie) (e (a3 *h (E charlie d2))) (
  Finish)))))).
Proof. reflexivity. Qed.

(* Verify pcharlie expands correctly *)
Lemma pcharlie_eq dk v3 : pcharlie dk v3 = 
  PInit (k dk) (
  PInit (d v3) (
  PSend n(alice) (e (E charlie v3)) (
  Recv_dec n(bob) dk (fun d3 => (
    PSend n(alice) (e (E alice d3))
  Finish))))).
Proof. reflexivity. Qed.

(* Verify palice expands correctly - note: let expressions are inlined *)
Lemma palice_eq dk v1 u1 u2 u3 r2 r3 : palice dk v1 u1 u2 u3 r2 r3 = 
  PInit (k dk) (PInit (d v1) (PInit (d u1) (PInit (d u2) (PInit (d u3) 
  (PInit (d r2) (PInit (d r3) (Recv_enc n(bob) (fun c2 =>
  Recv_enc n(charlie) (fun c3 =>
    PSend n(bob) (e (c2 ^h u2 *h (E bob r2)))
   (PSend n(bob) (e (c3 ^h u3 *h (E charlie r3)))
   (Recv_dec n(charlie) dk (fun g =>
    PRet (d (g - r2 - r3 + (u1 * v1))))))))))))))).
Proof. reflexivity. Qed.

End dsdp.
