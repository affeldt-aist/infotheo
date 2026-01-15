From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg ring.
From mathcomp Require Import Rstruct reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_proba smc_entropy.
Require Import smc_interpreter scalar_product_program.

(**md**************************************************************************)
(* # SMC Scalar Product Protocol - Alternative Syntax                         *)
(*                                                                            *)
(* This file contains the same protocol definitions as scalar_product_program *)
(* but written using a custom syntax for improved readability.                *)
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
(*   !x  ->  (one x)   scalar/singleton wrapper                               *)
(*   &x  ->  (vec x)   vector/collection wrapper                              *)
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
Notation "{| e |}" := e (e custom smc at level 99) : smc_scope.

Local Open Scope smc_scope.

(******************************************************************************)
(** * Scalar Product Section with Programs                                    *)
(******************************************************************************)

Section scalar_product.

Variable m : nat.
Variable TX : finComRingType.
Variable VX : lmodType TX. (* vector is not ringType (mul)*)
Variable dotproduct : VX -> VX -> TX.
Local Notation "u *d w" := (dotproduct u w).

(* Party identifiers *)
Definition alice : nat := 0.
Definition bob : nat := 1.
Definition coserv : nat := 2.

(* Data type: scalar + vector *)
Definition data := (TX + VX)%type.
Definition one x : data := inl x.
Definition vec x : data := inr x.

(* Local wrappers for proc constructors to work around ssreflect syntax *)
(* Now fuel-indexed *)
Definition PInit {n} (x : data) (p : proc data n) : proc data n.+1 := Init x p.
Definition PSend {n} (party : nat) (x : data) (p : proc data n) : proc data n.+1 := Send party x p.
Definition PRecv {n} (party : nat) (f : data -> proc data n) : proc data n.+1 := Recv party f.
Definition PRet (x : data) : proc data 2 := Ret x.

(* Specialized receive operations - fuel-indexed *)
Definition Recv_one {n} frm (f : TX -> proc data n) : proc data n.+1 :=
  Recv frm (fun x => if x is inl v then f v else Fail).
Definition Recv_vec {n} frm (f : VX -> proc data n) : proc data n.+1 :=
  Recv frm (fun x => if x is inr v then f v else Fail).

(** * Data wrapper shorthand notations *)

(* !x -> (one x) for scalar - "exactly one" *)
Notation "! x" := (one x) (at level 0, x at level 0) : smc_scope.
(* &x -> (vec x) for vector - "collection" *)
Notation "& x" := (vec x) (at level 0, x at level 0) : smc_scope.

(** * Basic custom syntax notations *)

(* Finish - terminal state *)
Notation "'Finish'" := Finish (in custom smc at level 0).

(* Ret - return a value *)
Notation "'Ret' x" := (PRet x) 
  (in custom smc at level 80, x constr at level 0).

(* Fail - error state *)  
Notation "'Fail'" := Fail (in custom smc at level 0).

(** * Sequencing with · (middle dot) or ; (semicolon as ASCII fallback) *)

(* Multi-var Init using full-width space 　 (U+3000) - must be defined BEFORE single-var *)
Notation "'Init' x '　' .. '　' y · P" := (PInit x .. (PInit y P) ..)
  (in custom smc at level 85, 
   x constr at level 0, y constr at level 0,
   P custom smc at level 85, right associativity).
Notation "'Init' x '　' .. '　' y ; P" := (PInit x .. (PInit y P) ..)
  (in custom smc at level 85, 
   x constr at level 0, y constr at level 0,
   P custom smc at level 85, right associativity).

(* Multi-var Init using tuple syntax *)
Notation "'Init' '(' x ',' .. ',' y ')' · P" := (PInit x .. (PInit y P) ..)
  (in custom smc at level 85,
   x constr at level 0, y constr at level 0,
   P custom smc at level 85, right associativity).
Notation "'Init' '(' x ',' .. ',' y ')' ; P" := (PInit x .. (PInit y P) ..)
  (in custom smc at level 85,
   x constr at level 0, y constr at level 0,
   P custom smc at level 85, right associativity).

(* Single Init with continuation *)
Notation "'Init' x · P" := (PInit x P)
  (in custom smc at level 85, x constr at level 0,
   P custom smc at level 85, right associativity).
Notation "'Init' x ; P" := (PInit x P)
  (in custom smc at level 85, x constr at level 0,
   P custom smc at level 85, right associativity).

(** * Send/Recv with angle brackets *)

(* Send - ASCII angle brackets *)
Notation "'Send<' p '>' x · P" := (PSend p x P)
  (in custom smc at level 85, p constr at level 0, x constr at level 0,
   P custom smc at level 85, right associativity).
Notation "'Send<' p '>' x ; P" := (PSend p x P)
  (in custom smc at level 85, p constr at level 0, x constr at level 0,
   P custom smc at level 85, right associativity).

(* Send - Unicode angle brackets *)
Notation "'Send⟨' p '⟩' x · P" := (PSend p x P)
  (in custom smc at level 85, p constr at level 0, x constr at level 0,
   P custom smc at level 85, right associativity).
Notation "'Send⟨' p '⟩' x ; P" := (PSend p x P)
  (in custom smc at level 85, p constr at level 0, x constr at level 0,
   P custom smc at level 85, right associativity).

(* Recv with λ binder - ASCII angle brackets *)
Notation "'Recv<' p '>' 'λ' x · P" := (PRecv p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv<' p '>' 'λ' x ; P" := (PRecv p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv<' p '>' 'fun' x '=>' P" := (PRecv p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).

(* Recv with λ binder - Unicode angle brackets *)
Notation "'Recv⟨' p '⟩' 'λ' x · P" := (PRecv p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv⟨' p '⟩' 'λ' x ; P" := (PRecv p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv⟨' p '⟩' 'fun' x '=>' P" := (PRecv p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).

(** * Specialized Recv_one and Recv_vec operations *)

(* Recv_one - ASCII angle brackets *)
Notation "'Recv_one<' p '>' 'λ' x · P" := (Recv_one p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_one<' p '>' 'λ' x ; P" := (Recv_one p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_one<' p '>' 'fun' x '=>' P" := (Recv_one p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).

(* Recv_one - Unicode angle brackets *)
Notation "'Recv_one⟨' p '⟩' 'λ' x · P" := (Recv_one p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_one⟨' p '⟩' 'λ' x ; P" := (Recv_one p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_one⟨' p '⟩' 'fun' x '=>' P" := (Recv_one p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).

(* Recv_vec - ASCII angle brackets *)
Notation "'Recv_vec<' p '>' 'λ' x · P" := (Recv_vec p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_vec<' p '>' 'λ' x ; P" := (Recv_vec p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_vec<' p '>' 'fun' x '=>' P" := (Recv_vec p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).

(* Recv_vec - Unicode angle brackets *)
Notation "'Recv_vec⟨' p '⟩' 'λ' x · P" := (Recv_vec p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_vec⟨' p '⟩' 'λ' x ; P" := (Recv_vec p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_vec⟨' p '⟩' 'fun' x '=>' P" := (Recv_vec p (fun x => P))
  (in custom smc at level 85, p constr at level 0, x name,
   P custom smc at level 85, right associativity).

(** * Variable reference *)
Notation "x" := x (in custom smc at level 0, x ident).

(******************************************************************************)
(** * Scalar Product Protocol Programs - Unicode Version                      *)
(******************************************************************************)

(* Commodity server's protocol - Unicode version *)
(* Fuel automatically inferred *)
Definition pcoserv (sa sb: VX) (ra : TX) : proc data _ :=
  {| Init &sa　&sb　!ra ·
     Send⟨alice⟩ &sa ·
     Send⟨alice⟩ !ra ·
     Send⟨bob⟩ &sb ·
     Send⟨bob⟩ !(sa *d sb - ra) ·
     Finish |}.

(* Alice's protocol - Unicode version *)
Definition palice (xa : VX) : proc data _ :=
  {| Init &xa ·
     Recv_vec⟨coserv⟩ λ sa ·
     Recv_one⟨coserv⟩ λ ra ·
     Send⟨bob⟩ &(xa + sa) ·
     Recv_vec⟨bob⟩ λ xb' ·
     Recv_one⟨bob⟩ λ t ·
     Ret !(t - (xb' *d sa) + ra) |}.

(* Bob's protocol - Unicode version *)
Definition pbob (xb : VX) (yb : TX) : proc data _ :=
  {| Init &xb　!yb ·
     Recv_vec⟨coserv⟩ λ sb ·
     Recv_one⟨coserv⟩ λ rb ·
     Recv_vec⟨alice⟩ λ xa' ·
     Send⟨alice⟩ &(xb + sb) ·
     Send⟨alice⟩ !(xa' *d xb + rb - yb) ·
     Ret !yb |}.

(******************************************************************************)
(** * Scalar Product Protocol Programs - ASCII Version                        *)
(******************************************************************************)

(* Commodity server's protocol - ASCII version *)
Definition pcoserv_ascii (sa sb: VX) (ra : TX) : proc data _ :=
  {| Init (&sa, &sb, !ra) ;
     Send<alice> &sa ;
     Send<alice> !ra ;
     Send<bob> &sb ;
     Send<bob> !(sa *d sb - ra) ;
     Finish |}.

(* Alice's protocol - ASCII version *)
Definition palice_ascii (xa : VX) : proc data _ :=
  {| Init &xa ;
     Recv_vec<coserv> fun sa =>
     Recv_one<coserv> fun ra =>
     Send<bob> &(xa + sa) ;
     Recv_vec<bob> fun xb' =>
     Recv_one<bob> fun t =>
     Ret !(t - (xb' *d sa) + ra) |}.

(* Bob's protocol - ASCII version *)
Definition pbob_ascii (xb : VX) (yb : TX) : proc data _ :=
  {| Init (&xb, !yb) ;
     Recv_vec<coserv> fun sb =>
     Recv_one<coserv> fun rb =>
     Recv_vec<alice> fun xa' =>
     Send<alice> &(xb + sb) ;
     Send<alice> !(xa' *d xb + rb - yb) ;
     Ret !yb |}.

(* Verify ASCII and Unicode versions are equivalent *)
Lemma pcoserv_ascii_eq sa sb ra : pcoserv sa sb ra = pcoserv_ascii sa sb ra.
Proof. reflexivity. Qed.

Lemma palice_ascii_eq xa : palice xa = palice_ascii xa.
Proof. reflexivity. Qed.

Lemma pbob_ascii_eq xb yb : pbob xb yb = pbob_ascii xb yb.
Proof. reflexivity. Qed.

(******************************************************************************)
(** * Equivalence with original definitions                                   *)
(******************************************************************************)

Local Close Scope smc_scope.

(* Verify pcoserv expands to the original nested structure *)
Lemma pcoserv_eq sa sb ra : pcoserv sa sb ra = 
  PInit (vec sa) (PInit (vec sb) (PInit (one ra)
    (PSend alice (vec sa) (PSend alice (one ra)
      (PSend bob (vec sb) (PSend bob (one (sa *d sb - ra)) Finish)))))).
Proof. reflexivity. Qed.

(* Verify palice expands correctly *)
Lemma palice_eq xa : palice xa = 
  PInit (vec xa)
    (Recv_vec coserv (fun sa =>
    (Recv_one coserv (fun ra =>
      (PSend bob (vec (xa + sa))
      (Recv_vec bob (fun xb' =>
      (Recv_one bob (fun t =>
        PRet (one (t - (xb' *d sa) + ra))))))))))).
Proof. reflexivity. Qed.

(* Verify pbob expands correctly *)
Lemma pbob_eq xb yb : pbob xb yb = 
  PInit (vec xb) (PInit (one yb)
    (Recv_vec coserv (fun sb =>
    (Recv_one coserv (fun rb =>
    (Recv_vec alice (fun xa' =>
      (PSend alice (vec (xb + sb))
      (PSend alice (one (xa' *d xb + rb - yb))
        (PRet (one yb))))))))))).
Proof. reflexivity. Qed.

(******************************************************************************)
(** * Cross-file equivalence: scalar_product_program = scalar_product_alt_syntax *)
(******************************************************************************)

(* Import original program definitions from scalar_product_program for comparison.
   Note: The original pcoserv, palice, pbob are parameterized by TX, VX, dotproduct
   (m is a section variable but not used by these definitions). *)
Let pcoserv_orig := @scalar_product_program.pcoserv TX VX dotproduct.
Let palice_orig := @scalar_product_program.palice TX VX dotproduct.
Let pbob_orig := @scalar_product_program.pbob TX VX dotproduct.

(* Verify that the alt_syntax programs are definitionally equal to the original *)
Lemma pcoserv_cross_eq sa sb ra : pcoserv sa sb ra = pcoserv_orig sa sb ra.
Proof. reflexivity. Qed.

Lemma palice_cross_eq xa : palice xa = palice_orig xa.
Proof. reflexivity. Qed.

Lemma pbob_cross_eq xb yb : pbob xb yb = pbob_orig xb yb.
Proof. reflexivity. Qed.

End scalar_product.
