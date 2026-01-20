From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter smc_tactics.
Require Import smc_proba homomorphic_encryption dsdp_interface dsdp_program.

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

(* Parameterize by a Party_HE_scheme instance *)
Variable PHE : Party_HE_scheme.

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
Let Emul := @phe_Emul PHE.
Let Epow := @phe_Epow PHE.

Notation "u *h w" := (Emul u w).
Notation "u ^h w" := (Epow u w).

(* Party identities - variables of the scheme's party type *)
Variable alice : partyT.
Variable bob : partyT.
Variable charlie : partyT.

(* Party to nat mapping for Send/Recv indices *)
Variable pn : partyT -> nat.

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


(** * Send/Recv with pn(...) for party to nat conversion *)

(* Send - ASCII angle brackets *)
Notation "'Send<' p '>' x · P" := (PSend (pn p) x P)
  (in custom dsdp at level 85, p constr at level 0, x constr at level 0,
   P custom dsdp at level 85, right associativity).
Notation "'Send<' p '>' x ; P" := (PSend (pn p) x P)
  (in custom dsdp at level 85, p constr at level 0, x constr at level 0,
   P custom dsdp at level 85, right associativity).

(* Send - Unicode angle brackets *)
Notation "'Send⟨' p '⟩' x · P" := (PSend (pn p) x P)
  (in custom dsdp at level 85, p constr at level 0, x constr at level 0,
   P custom dsdp at level 85, right associativity).
Notation "'Send⟨' p '⟩' x ; P" := (PSend (pn p) x P)
  (in custom dsdp at level 85, p constr at level 0, x constr at level 0,
   P custom dsdp at level 85, right associativity).

(* Recv with λ binder - ASCII angle brackets *)
Notation "'Recv<' p '>' 'λ' x · P" := (PRecv (pn p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
Notation "'Recv<' p '>' 'λ' x ; P" := (PRecv (pn p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
(* Recv with fun binder - ASCII angle brackets, ASCII fallback *)
Notation "'Recv<' p '>' 'fun' x '=>' P" := (PRecv (pn p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(* Recv with λ binder - Unicode angle brackets *)
Notation "'Recv⟨' p '⟩' 'λ' x · P" := (PRecv (pn p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
Notation "'Recv⟨' p '⟩' 'λ' x ; P" := (PRecv (pn p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
(* Recv with fun binder - Unicode angle brackets, ASCII fallback *)
Notation "'Recv⟨' p '⟩' 'fun' x '=>' P" := (PRecv (pn p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(** * Specialized Recv operations from interface *)

Let Recv_dec {n} := @di_Recv_dec PHE DI n.
Let Recv_enc {n} := @di_Recv_enc PHE DI n.

(* Recv_dec notation - ASCII angle brackets *)
Notation "'Recv_dec<' p '>' dk 'λ' x · P" := (Recv_dec (pn p) dk (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, 
   dk constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
Notation "'Recv_dec<' p '>' dk 'λ' x ; P" := (Recv_dec (pn p) dk (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, 
   dk constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
(* Recv_dec with fun - ASCII fallback *)
Notation "'Recv_dec<' p '>' dk 'fun' x '=>' P" := (Recv_dec (pn p) dk (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, 
   dk constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(* Recv_dec notation - Unicode angle brackets *)
Notation "'Recv_dec⟨' p '⟩' dk 'λ' x · P" := (Recv_dec (pn p) dk (fun x => P))
  (in custom dsdp at level 85, p constr at level 0,
   dk constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
Notation "'Recv_dec⟨' p '⟩' dk 'λ' x ; P" := (Recv_dec (pn p) dk (fun x => P))
  (in custom dsdp at level 85, p constr at level 0,
   dk constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
(* Recv_dec with fun - Unicode brackets, ASCII fallback *)
Notation "'Recv_dec⟨' p '⟩' dk 'fun' x '=>' P" := (Recv_dec (pn p) dk (fun x => P))
  (in custom dsdp at level 85, p constr at level 0,
   dk constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(* Recv_enc notation - ASCII angle brackets *)
Notation "'Recv_enc<' p '>' 'λ' x · P" := (Recv_enc (pn p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
Notation "'Recv_enc<' p '>' 'λ' x ; P" := (Recv_enc (pn p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
(* Recv_enc with fun - ASCII fallback *)
Notation "'Recv_enc<' p '>' 'fun' x '=>' P" := (Recv_enc (pn p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(* Recv_enc notation - Unicode angle brackets *)
Notation "'Recv_enc⟨' p '⟩' 'λ' x · P" := (Recv_enc (pn p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
Notation "'Recv_enc⟨' p '⟩' 'λ' x ; P" := (Recv_enc (pn p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).
(* Recv_enc with fun - Unicode brackets, ASCII fallback *)
Notation "'Recv_enc⟨' p '⟩' 'fun' x '=>' P" := (Recv_enc (pn p) (fun x => P))
  (in custom dsdp at level 85, p constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(** * Variable reference *)
Notation "x" := x (in custom dsdp at level 0, x ident).

(******************************************************************************)
(** * DSDP Protocol Programs - ASCII Version (Default)                        *)
(** * Each encryption E(party, msg, rand) needs explicit randomness.          *)
(******************************************************************************)

(* Bob's protocol - ASCII version *)
Definition pbob (dk : pkey)(v2 : msg)(rb1 rb2 : rand) : proc data _ :=
  {| Init (#dk, &v2) ;
     Send<alice> $(E bob v2 rb1) ;
     Recv_dec<alice> dk fun d2 =>
     Recv_enc<alice> fun a3 =>
     Send<charlie> $(a3 *h (E charlie d2 rb2)) ;
     Finish |}.

(* Charlie's protocol - ASCII version *)
Definition pcharlie (dk : pkey)(v3 : msg)(rc1 rc2 : rand) : proc data _ :=
  {| Init (#dk, &v3) ;
     Send<alice> $(E charlie v3 rc1) ;
     Recv_dec<bob> dk fun d3 =>
     Send<alice> $(E alice d3 rc2) ;
     Finish |}.

(* Alice's protocol - ASCII version *)
Definition palice (dk : pkey)(v1 u1 u2 u3 r2 r3: msg)(ra1 ra2 : rand) : proc data _ :=
  {| Init (#dk, &v1, &u1, &u2, &u3, &r2, &r3) ;
     Recv_enc<bob> fun c2 =>
     Recv_enc<charlie> fun c3 =>
     Send<bob> $(c2 ^h u2 *h (E bob r2 ra1)) ;
     Send<bob> $(c3 ^h u3 *h (E charlie r3 ra2)) ;
     Recv_dec<charlie> dk fun g =>
     Ret &(g - r2 - r3 + u1 * v1) |}.

(******************************************************************************)
(** * DSDP Protocol Programs - Unicode Version                                *)
(******************************************************************************)

(* Bob's protocol - Unicode version, fuel auto-inferred *)
Definition pbob_unicode (dk : pkey)(v2 : msg)(rb1 rb2 : rand) : proc data _ :=
  {| Init #dk　&v2 ·
     Send⟨alice⟩ $(E bob v2 rb1) ·
     Recv_dec⟨alice⟩ dk λ d2 ·
     Recv_enc⟨alice⟩ λ a3 ·
     Send⟨charlie⟩ $(a3 *h (E charlie d2 rb2)) ·
     Finish |}.

(* Charlie's protocol - Unicode version *)
Definition pcharlie_unicode (dk : pkey)(v3 : msg)(rc1 rc2 : rand) : proc data _ :=
  {| Init #dk　&v3 ·
     Send⟨alice⟩ $(E charlie v3 rc1) ·
     Recv_dec⟨bob⟩ dk λ d3 ·
     Send⟨alice⟩ $(E alice d3 rc2) ·
     Finish |}.

(* Alice's protocol - Unicode version *)
Definition palice_unicode (dk : pkey)(v1 u1 u2 u3 r2 r3: msg)(ra1 ra2 : rand) : proc data _ :=
  {| Init #dk　&v1　&u1　&u2　&u3　&r2　&r3 ·
     Recv_enc⟨bob⟩ λ c2 ·
     Recv_enc⟨charlie⟩ λ c3 ·
     Send⟨bob⟩ $(c2 ^h u2 *h (E bob r2 ra1)) ·
     Send⟨bob⟩ $(c3 ^h u3 *h (E charlie r3 ra2)) ·
     Recv_dec⟨charlie⟩ dk λ g ·
     Ret &(g - r2 - r3 + u1 * v1) |}.

(* Verify ASCII and Unicode versions are equivalent *)
Lemma pbob_unicode_eq dk v2 rb1 rb2 : pbob dk v2 rb1 rb2 = pbob_unicode dk v2 rb1 rb2.
Proof. reflexivity. Qed.

Lemma pcharlie_unicode_eq dk v3 rc1 rc2 : pcharlie dk v3 rc1 rc2 = pcharlie_unicode dk v3 rc1 rc2.
Proof. reflexivity. Qed.

Lemma palice_unicode_eq dk v1 u1 u2 u3 r2 r3 ra1 ra2 : 
  palice dk v1 u1 u2 u3 r2 r3 ra1 ra2 = palice_unicode dk v1 u1 u2 u3 r2 r3 ra1 ra2.
Proof. reflexivity. Qed.

(******************************************************************************)
(** * Equivalence with original definitions                                   *)
(******************************************************************************)

Local Close Scope dsdp_scope.

(* Verify pbob expands to the original nested structure *)
Lemma pbob_eq dk v2 rb1 rb2 : pbob dk v2 rb1 rb2 = 
  PInit (k dk) (
  PInit (d v2) (
  PSend (pn alice) (e (E bob v2 rb1)) (
  Recv_dec (pn alice) dk (fun d2 =>
  Recv_enc (pn alice) (fun a3 =>
    PSend (pn charlie) (e (a3 *h (E charlie d2 rb2))) (
  Finish)))))).
Proof. reflexivity. Qed.

(* Verify pcharlie expands correctly *)
Lemma pcharlie_eq dk v3 rc1 rc2 : pcharlie dk v3 rc1 rc2 = 
  PInit (k dk) (
  PInit (d v3) (
  PSend (pn alice) (e (E charlie v3 rc1)) (
  Recv_dec (pn bob) dk (fun d3 => (
    PSend (pn alice) (e (E alice d3 rc2))
  Finish))))).
Proof. reflexivity. Qed.

(* Verify palice expands correctly - note: let expressions are inlined *)
Lemma palice_eq dk v1 u1 u2 u3 r2 r3 ra1 ra2 : palice dk v1 u1 u2 u3 r2 r3 ra1 ra2 = 
  PInit (k dk) (PInit (d v1) (PInit (d u1) (PInit (d u2) (PInit (d u3) 
  (PInit (d r2) (PInit (d r3) (Recv_enc (pn bob) (fun c2 =>
  Recv_enc (pn charlie) (fun c3 =>
    PSend (pn bob) (e (c2 ^h u2 *h (E bob r2 ra1)))
   (PSend (pn bob) (e (c3 ^h u3 *h (E charlie r3 ra2)))
   (Recv_dec (pn charlie) dk (fun g =>
    PRet (d (g - r2 - r3 + (u1 * v1))))))))))))))).
Proof. reflexivity. Qed.

End dsdp.
