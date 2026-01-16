(******************************************************************************)
(*                                                                            *)
(* Demo: Custom Entry Syntax for SMC Programs                                 *)
(*                                                                            *)
(* This file demonstrates using Coq custom entries to achieve paper-like      *)
(* syntax for secure multiparty computation protocols.                        *)
(*                                                                            *)
(* Target syntax for scalar product:                                          *)
(*   {| Init (&sa, &sb, !ra) · Send⟨alice⟩ &sa · Recv_vec⟨bob⟩ λ x · Ret !r |}*)
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

(** * Minimal proc type (self-contained for demo) *)

Section proc_type.
Variable data : Type.

Inductive proc : Type :=
  | PInit : data -> proc -> proc
  | PSend : nat -> data -> proc -> proc
  | PRecv : nat -> (data -> proc) -> proc
  | PRet : data -> proc
  | PFinish : proc
  | PFail : proc.

End proc_type.

Arguments PFinish {data}.
Arguments PFail {data}.


(** * Scope and Custom Entry Declaration *)

Declare Scope smc_scope.
Declare Custom Entry smc.

(** * Entry/Exit Notations *)

(* Use {| |} as delimiters for entering the custom smc syntax *)
Notation "{| e |}" := e (e custom smc at level 99) : smc_scope.

(* Alternative keyword delimiter *)
Notation "'PROC' e 'END'" := e (e custom smc at level 99) : smc_scope.

Local Open Scope smc_scope.

(** * Basic Constructs *)

(* Finish - terminal state *)
Notation "'Finish'" := PFinish (in custom smc at level 0).

(* Ret - return a value *)
Notation "'Ret' x" := (PRet x) 
  (in custom smc at level 80, x constr at level 0).

(* Fail - error state *)  
Notation "'Fail'" := PFail (in custom smc at level 0).

(** * Sequencing with · (middle dot) *)

(* Single Init with continuation - Unicode middle dot *)
Notation "'Init' x · P" := (PInit x P)
  (in custom smc at level 85, x constr at level 0,
   P custom smc at level 85, right associativity).

(* Single Init - ASCII semicolon fallback *)
Notation "'Init' x ; P" := (PInit x P)
  (in custom smc at level 85, x constr at level 0,
   P custom smc at level 85, right associativity).

(* Send with continuation - ASCII angle brackets <n> *)
Notation "'Send<' n '>' x · P" := (PSend n x P)
  (in custom smc at level 85, n constr at level 0, x constr at level 0,
   P custom smc at level 85, right associativity).
Notation "'Send<' n '>' x ; P" := (PSend n x P)
  (in custom smc at level 85, n constr at level 0, x constr at level 0,
   P custom smc at level 85, right associativity).

(* Send with continuation - Unicode angle brackets ⟨n⟩ *)
Notation "'Send⟨' n '⟩' x · P" := (PSend n x P)
  (in custom smc at level 85, n constr at level 0, x constr at level 0,
   P custom smc at level 85, right associativity).
Notation "'Send⟨' n '⟩' x ; P" := (PSend n x P)
  (in custom smc at level 85, n constr at level 0, x constr at level 0,
   P custom smc at level 85, right associativity).

(* Recv with λ binder - ASCII angle bracket style *)
Notation "'Recv<' n '>' 'λ' x · P" := (PRecv n (fun x => P))
  (in custom smc at level 85, n constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv<' n '>' 'λ' x ; P" := (PRecv n (fun x => P))
  (in custom smc at level 85, n constr at level 0, x name,
   P custom smc at level 85, right associativity).

(* Recv with λ binder - Unicode angle bracket style *)
Notation "'Recv⟨' n '⟩' 'λ' x · P" := (PRecv n (fun x => P))
  (in custom smc at level 85, n constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv⟨' n '⟩' 'λ' x ; P" := (PRecv n (fun x => P))
  (in custom smc at level 85, n constr at level 0, x name,
   P custom smc at level 85, right associativity).

(* Recv with fun binder - ASCII fallback *)
Notation "'Recv<' n '>' 'fun' x '=>' P" := (PRecv n (fun x => P))
  (in custom smc at level 85, n constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv⟨' n '⟩' 'fun' x '=>' P" := (PRecv n (fun x => P))
  (in custom smc at level 85, n constr at level 0, x name,
   P custom smc at level 85, right associativity).

(** * Recv_one and Recv_vec - specialized receive operations for scalar product *)

(* In scalar product protocol, data is a sum type: TX + VX (scalar + vector)
   Recv_one: receive scalar value
   Recv_vec: receive vector value *)

(* Recv_one: Receive scalar from party n, fail if not scalar *)
Definition PRecv_one {data : Type} (is_scalar : data -> option data)
    (n : nat) (f : data -> proc data) : proc data :=
  PRecv n (fun x => 
    match is_scalar x with
    | Some v => f v
    | None => PFail
    end).

(* Recv_vec: Receive vector from party n, fail if not vector *)
Definition PRecv_vec {data : Type} (is_vector : data -> option data)
    (n : nat) (f : data -> proc data) : proc data :=
  PRecv n (fun x => 
    match is_vector x with
    | Some v => f v
    | None => PFail
    end).

(* Recv_one with λ binder - ASCII *)
Notation "'Recv_one<' n '>' chk 'λ' x · P" := (PRecv_one chk n (fun x => P))
  (in custom smc at level 85, n constr at level 0, 
   chk constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_one<' n '>' chk 'λ' x ; P" := (PRecv_one chk n (fun x => P))
  (in custom smc at level 85, n constr at level 0, 
   chk constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_one<' n '>' chk 'fun' x '=>' P" := (PRecv_one chk n (fun x => P))
  (in custom smc at level 85, n constr at level 0, 
   chk constr at level 0, x name,
   P custom smc at level 85, right associativity).

(* Recv_one with λ binder - Unicode *)
Notation "'Recv_one⟨' n '⟩' chk 'λ' x · P" := (PRecv_one chk n (fun x => P))
  (in custom smc at level 85, n constr at level 0,
   chk constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_one⟨' n '⟩' chk 'λ' x ; P" := (PRecv_one chk n (fun x => P))
  (in custom smc at level 85, n constr at level 0,
   chk constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_one⟨' n '⟩' chk 'fun' x '=>' P" := (PRecv_one chk n (fun x => P))
  (in custom smc at level 85, n constr at level 0,
   chk constr at level 0, x name,
   P custom smc at level 85, right associativity).

(* Recv_vec with λ binder - ASCII *)
Notation "'Recv_vec<' n '>' chk 'λ' x · P" := (PRecv_vec chk n (fun x => P))
  (in custom smc at level 85, n constr at level 0, 
   chk constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_vec<' n '>' chk 'λ' x ; P" := (PRecv_vec chk n (fun x => P))
  (in custom smc at level 85, n constr at level 0, 
   chk constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_vec<' n '>' chk 'fun' x '=>' P" := (PRecv_vec chk n (fun x => P))
  (in custom smc at level 85, n constr at level 0, 
   chk constr at level 0, x name,
   P custom smc at level 85, right associativity).

(* Recv_vec with λ binder - Unicode *)
Notation "'Recv_vec⟨' n '⟩' chk 'λ' x · P" := (PRecv_vec chk n (fun x => P))
  (in custom smc at level 85, n constr at level 0,
   chk constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_vec⟨' n '⟩' chk 'λ' x ; P" := (PRecv_vec chk n (fun x => P))
  (in custom smc at level 85, n constr at level 0,
   chk constr at level 0, x name,
   P custom smc at level 85, right associativity).
Notation "'Recv_vec⟨' n '⟩' chk 'fun' x '=>' P" := (PRecv_vec chk n (fun x => P))
  (in custom smc at level 85, n constr at level 0,
   chk constr at level 0, x name,
   P custom smc at level 85, right associativity).

(** * Multi-variable Init *)

(* Style 1: Using 　 (U+3000, full-width space) as separator - looks like real spaces *)
(* Notation: Init x 　 .. 　 y · P  expands to PInit x (.. (PInit y P) ..) *)
Notation "'Init' x '　' .. '　' y · P" := (PInit x .. (PInit y P) ..)
  (in custom smc at level 85, 
   x constr at level 0, y constr at level 0,
   P custom smc at level 85, right associativity).
Notation "'Init' x '　' .. '　' y ; P" := (PInit x .. (PInit y P) ..)
  (in custom smc at level 85, 
   x constr at level 0, y constr at level 0,
   P custom smc at level 85, right associativity).

(* Style 2: Using tuple-like syntax Init (x, y, z) · P *)
Notation "'Init' '(' x ',' .. ',' y ')' · P" := (PInit x .. (PInit y P) ..)
  (in custom smc at level 85,
   x constr at level 0, y constr at level 0,
   P custom smc at level 85, right associativity).
Notation "'Init' '(' x ',' .. ',' y ')' ; P" := (PInit x .. (PInit y P) ..)
  (in custom smc at level 85,
   x constr at level 0, y constr at level 0,
   P custom smc at level 85, right associativity).

(** * Variable reference *)

Notation "x" := x (in custom smc at level 0, x ident).


(******************************************************************************)
(** * TESTS                                                                   *)
(******************************************************************************)

Section tests.

Variable data : Type.
Variables (v1 v2 v3 : data).

(** Test 1: Simple Finish *)
Definition test_finish : proc data := {| Finish |}.

(** Test 2: Simple Ret *)
Definition test_ret : proc data := {| Ret v1 |}.

(** Test 3: Single Init with · sequencing *)
Definition test_init_one : proc data := {| Init v1 · Finish |}.

(** Test 4: Multiple Init - chained with · *)
Definition test_init_chained : proc data := 
  {| Init v1 · Init v2 · Init v3 · Finish |}.

(** Test 5: Multiple Init - tuple style *)
Definition test_init_tuple : proc data := 
  {| Init (v1, v2, v3) · Finish |}.

(** Test 6: Send with ASCII angle brackets *)
Definition test_send_ascii : proc data := 
  {| Init v1 · Send<0> v1 · Finish |}.

(** Test 7: Send with Unicode angle brackets *)
Definition test_send_unicode : proc data := 
  {| Init v1 · Send⟨0⟩ v1 · Finish |}.

(** Test 8: Recv with λ binder - ASCII *)
Definition test_recv_lambda_ascii : proc data := 
  {| Recv<0> λ x · Ret x |}.

(** Test 9: Recv with λ binder - Unicode *)
Definition test_recv_lambda_unicode : proc data := 
  {| Recv⟨0⟩ λ x · Ret x |}.

(** Test 10: Recv with fun binder - ASCII fallback *)
Definition test_recv_fun : proc data := 
  {| Recv<0> fun x => Ret x |}.

(** Verify desugaring *)
Lemma test_finish_eq : test_finish = PFinish.
Proof. reflexivity. Qed.

Lemma test_ret_eq : test_ret = PRet v1.
Proof. reflexivity. Qed.

Lemma test_init_one_eq : test_init_one = PInit v1 PFinish.
Proof. reflexivity. Qed.

Lemma test_init_chained_eq : test_init_chained = PInit v1 (PInit v2 (PInit v3 PFinish)).
Proof. reflexivity. Qed.

Lemma test_init_tuple_eq : test_init_tuple = PInit v1 (PInit v2 (PInit v3 PFinish)).
Proof. reflexivity. Qed.

Lemma test_send_ascii_eq : test_send_ascii = PInit v1 (PSend 0 v1 PFinish).
Proof. reflexivity. Qed.

Lemma test_send_unicode_eq : test_send_unicode = PInit v1 (PSend 0 v1 PFinish).
Proof. reflexivity. Qed.

Lemma test_recv_lambda_ascii_eq : test_recv_lambda_ascii = PRecv 0 (fun x => PRet x).
Proof. reflexivity. Qed.

Lemma test_recv_unicode_eq : test_recv_lambda_unicode = PRecv 0 (fun x => PRet x).
Proof. reflexivity. Qed.

Lemma test_recv_fun_eq : test_recv_fun = PRecv 0 (fun x => PRet x).
Proof. reflexivity. Qed.

(** Test: ASCII and Unicode versions are equivalent *)
Lemma send_ascii_unicode_eq : test_send_ascii = test_send_unicode.
Proof. reflexivity. Qed.

Lemma recv_ascii_unicode_eq : test_recv_lambda_ascii = test_recv_lambda_unicode.
Proof. reflexivity. Qed.

End tests.


(******************************************************************************)
(** * Data Wrapper Tests (for scalar product: !x = scalar, &x = vector)        *)
(******************************************************************************)

Section wrapper_tests.

Variable T : Type.

(* Local wrapper definitions *)
Definition one_wrap (x : T) : T := x.
Definition vec_wrap (x : T) : T := x.

(* Shorthand notations *)
(* !x for one (scalar) - "exactly one" *)
Local Notation "! x" := (one_wrap x) (at level 0, x at level 0).
(* &x for vec (vector) - "collection" *)
Local Notation "& x" := (vec_wrap x) (at level 0, x at level 0).

Variables (sa sb ra : T).

(** Test: '!x' for scalar wrapper *)
Definition test_scalar_wrapper : proc T := {| Init !ra · Finish |}.

(** Test: '&x' for vector wrapper *)
Definition test_vector_wrapper : proc T := {| Init &sa · Finish |}.

(** Test: Combined wrappers with tuple-style Init *)
Definition test_wrappers_combined : proc T :=
  {| Init (&sa, &sb, !ra) · Send<0> &sa · Finish |}.

(** Test: Combined wrappers with full-width space Init *)
Definition test_wrappers_fullwidth : proc T :=
  {| Init &sa　&sb　!ra · Send<0> &sa · Finish |}.

(** Verify desugaring *)
Lemma test_scalar_wrapper_eq : test_scalar_wrapper = PInit (one_wrap ra) PFinish.
Proof. reflexivity. Qed.

Lemma test_vector_wrapper_eq : test_vector_wrapper = PInit (vec_wrap sa) PFinish.
Proof. reflexivity. Qed.

Lemma test_wrappers_combined_eq : test_wrappers_combined = 
  PInit (vec_wrap sa) (PInit (vec_wrap sb) (PInit (one_wrap ra) (PSend 0 (vec_wrap sa) PFinish))).
Proof. reflexivity. Qed.

Lemma test_wrappers_fullwidth_eq : test_wrappers_fullwidth = 
  PInit (vec_wrap sa) (PInit (vec_wrap sb) (PInit (one_wrap ra) (PSend 0 (vec_wrap sa) PFinish))).
Proof. reflexivity. Qed.

(** Test: Tuple and fullwidth versions are equivalent *)
Lemma wrappers_tuple_fullwidth_eq : test_wrappers_combined = test_wrappers_fullwidth.
Proof. reflexivity. Qed.

End wrapper_tests.


(******************************************************************************)
(** * Recv_one and Recv_vec Tests                                              *)
(******************************************************************************)

Section recv_one_vec_tests.

Variable T : Type.
Variable is_scalar : T -> option T.
Variable is_vector : T -> option T.

Variables (v1 v2 : T).

(** Test: Recv_one ASCII *)
Definition test_recv_one_ascii : proc T :=
  {| Recv_one<0> is_scalar λ x · Ret x |}.

(** Test: Recv_one Unicode *)
Definition test_recv_one_unicode : proc T :=
  {| Recv_one⟨0⟩ is_scalar λ x · Ret x |}.

(** Test: Recv_vec ASCII *)
Definition test_recv_vec_ascii : proc T :=
  {| Recv_vec<0> is_vector λ x · Ret x |}.

(** Test: Recv_vec Unicode *)
Definition test_recv_vec_unicode : proc T :=
  {| Recv_vec⟨0⟩ is_vector λ x · Ret x |}.

(** Test: Recv_one with fun binder *)
Definition test_recv_one_fun : proc T :=
  {| Recv_one<0> is_scalar fun x => Ret x |}.

(** Verify desugaring *)
Lemma test_recv_one_ascii_eq : test_recv_one_ascii = PRecv_one is_scalar 0 (fun x => PRet x).
Proof. reflexivity. Qed.

Lemma test_recv_vec_ascii_eq : test_recv_vec_ascii = PRecv_vec is_vector 0 (fun x => PRet x).
Proof. reflexivity. Qed.

(** Test: ASCII and Unicode versions are equivalent *)
Lemma recv_one_ascii_unicode_eq : test_recv_one_ascii = test_recv_one_unicode.
Proof. reflexivity. Qed.

Lemma recv_vec_ascii_unicode_eq : test_recv_vec_ascii = test_recv_vec_unicode.
Proof. reflexivity. Qed.

End recv_one_vec_tests.


(******************************************************************************)
(** * Example: Scalar Product Protocol Style                                   *)
(******************************************************************************)

Section scalar_product_example.

Variable T : Type.
Variable dotproduct : T -> T -> T.
Local Notation "u *d w" := (dotproduct u w) (at level 40).

(* Data wrappers *)
Definition one (x : T) : T := x.
Definition vec (x : T) : T := x.

Local Notation "! x" := (one x) (at level 0, x at level 0).
Local Notation "& x" := (vec x) (at level 0, x at level 0).

(* Party identifiers *)
Definition alice : nat := 0.
Definition bob : nat := 1.
Definition coserv : nat := 2.

Variables (sa sb xa xb : T) (ra : T).

(** Unicode version of pcoserv-like program *)
Definition demo_pcoserv_unicode : proc T :=
  {| Init &sa　&sb　!ra ·
     Send⟨alice⟩ &sa ·
     Send⟨alice⟩ !ra ·
     Send⟨bob⟩ &sb ·
     Send⟨bob⟩ !(sa *d sb) ·
     Finish |}.

(** ASCII version of pcoserv-like program *)
Definition demo_pcoserv_ascii : proc T :=
  {| Init (&sa, &sb, !ra) ;
     Send<alice> &sa ;
     Send<alice> !ra ;
     Send<bob> &sb ;
     Send<bob> !(sa *d sb) ;
     Finish |}.

(** Verify equivalence *)
Lemma demo_pcoserv_eq : demo_pcoserv_unicode = demo_pcoserv_ascii.
Proof. reflexivity. Qed.

(** Verify desugaring *)
Lemma demo_pcoserv_structure : demo_pcoserv_unicode = 
  PInit (vec sa) (PInit (vec sb) (PInit (one ra)
    (PSend alice (vec sa) (PSend alice (one ra)
      (PSend bob (vec sb) (PSend bob (one (sa *d sb)) PFinish)))))).
Proof. reflexivity. Qed.

End scalar_product_example.


(******************************************************************************)
(** * Comparison: Unicode vs ASCII Syntax                                     *)
(******************************************************************************)

Section unicode_vs_ascii.

Variable T : Type.
Variables (v1 v2 v3 a b : T).

(* Local wrapper definitions for demo *)
Definition ow (x : T) : T := x.  (* one wrapper *)
Definition vw (x : T) : T := x.  (* vec wrapper *)

Local Notation "! x" := (ow x) (at level 0, x at level 0).
Local Notation "& x" := (vw x) (at level 0, x at level 0).

(*--------------------------------------------------------------------------*)
(* Unicode Version - prettier, paper-like                                    *)
(*   · = middle dot (Option+Shift+9 on macOS)                                *)
(*   λ = lambda                                                              *)
(*   ⟨⟩ = angle brackets                                                     *)
(*   　 = full-width space (CJK input)                                        *)
(*--------------------------------------------------------------------------*)

Definition example_unicode : proc T :=
  {| Init &v1　&v2　!v3 ·
     Send⟨1⟩ &a ·
     Recv⟨2⟩ λ x ·
     Send⟨1⟩ !b ·
     Finish |}.

(*--------------------------------------------------------------------------*)
(* ASCII Version - portable, no special characters needed                    *)
(*   ; = semicolon (replaces ·)                                              *)
(*   fun x => = function (replaces λ x ·)                                    *)
(*   <> = angle brackets (replaces ⟨⟩)                                       *)
(*   (x, y, z) = tuple (replaces 　 full-width space)                         *)
(*--------------------------------------------------------------------------*)

Definition example_ascii : proc T :=
  {| Init (&v1, &v2, !v3) ;
     Send<1> &a ;
     Recv<2> fun x =>
     Send<1> !b ;
     Finish |}.

(* Both versions produce identical terms *)
Lemma unicode_ascii_eq : example_unicode = example_ascii.
Proof. reflexivity. Qed.

(*--------------------------------------------------------------------------*)
(* Mixed Usage - you can mix ASCII and Unicode in the same program           *)
(*--------------------------------------------------------------------------*)

Definition example_mixed : proc T :=
  {| Init (&v1, &v2, !v3) ;      (* ASCII tuple and semicolon *)
     Send⟨1⟩ &a ·                (* Unicode brackets and dot *)
     Recv<2> λ x ;               (* ASCII brackets, Unicode lambda, ASCII semi *)
     Send<1> !b ·                (* ASCII brackets, Unicode dot *)
     Finish |}.

(* Mixed usage also produces the same term *)
Lemma mixed_eq : example_mixed = example_unicode.
Proof. reflexivity. Qed.

End unicode_vs_ascii.


(******************************************************************************)
(** * Summary of Available Syntax                                             *)
(******************************************************************************)

(*
   Unicode vs ASCII Fallback Table:
   +-----------------+------------------+----------------------------------+
   | Unicode         | ASCII Fallback   | Description                      |
   +-----------------+------------------+----------------------------------+
   | ·               | ;                | Sequencing operator              |
   | λ x ·           | fun x =>         | Lambda binder                    |
   | ⟨n⟩             | <n>              | Party angle brackets             |
   | x　y　z          | (x, y, z)        | Multi-var Init separator         |
   +-----------------+------------------+----------------------------------+
   
   Delimiters:
     {| ... |}                  - Enter custom smc syntax
     PROC ... END               - Keyword alternative delimiter
   
   Init (one or more variables):
     Init x · P                 - Initialize one variable
     Init x　y　z · P           - Multiple vars (　= U+3000 full-width space)
     Init (x, y, z) · P         - Multiple vars (tuple style) - ASCII friendly
     Init x ; P                 - ASCII: semicolon instead of middle dot
   
   Send:
     Send<n> v · P              - ASCII angle brackets
     Send⟨n⟩ v · P              - Unicode angle brackets
     Send<n> v ; P              - ASCII semicolon
   
   Recv:
     Recv<n> λ x · P            - ASCII brackets, Unicode lambda/dot
     Recv⟨n⟩ λ x · P            - Unicode brackets/lambda/dot
     Recv<n> fun x => P         - Pure ASCII version
   
   Recv_one/Recv_vec (for scalar product):
     Recv_one<n> chk λ x · P    - ASCII brackets, receive scalar
     Recv_one⟨n⟩ chk λ x · P    - Unicode brackets
     Recv_vec<n> chk λ x · P    - ASCII brackets, receive vector
     Recv_vec⟨n⟩ chk λ x · P    - Unicode brackets
     (also with fun x => and ; variants)
   
   Terminal:
     Ret v                      - Return value v
     Finish                     - Terminate successfully
     Fail                       - Terminate with failure
   
   Data wrapper shorthand (for scalar product):
     !x                         - (one x) scalar wrapper - "exactly one"
     &x                         - (vec x) vector wrapper - "collection"
*)

Print test_wrappers_combined.
