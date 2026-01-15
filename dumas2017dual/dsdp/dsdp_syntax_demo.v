(******************************************************************************)
(*                                                                            *)
(* Demo: Custom Entry Syntax for DSDP Programs                                *)
(*                                                                            *)
(* This file demonstrates using Coq custom entries to achieve paper-like      *)
(* syntax for secure multiparty computation protocols.                        *)
(*                                                                            *)
(* Target syntax:                                                             *)
(*   {| Init (v₁, u₁, u₂, u₃, r₂, r₃) · Recv⟨B⟩ λ c₂ · Send⟨B⟩ a₂ · Ret r |}  *)
(*                                                                            *)
(* How to type special characters:                                            *)
(*                                                                            *)
(* Middle dot · (U+00B7) for sequencing:                                      *)
(*   - macOS: Option + Shift + 9                                              *)
(*   - Windows: Alt + 0183 (numpad)                                           *)
(*   - Linux: Ctrl+Shift+U, 00b7, Enter                                       *)
(*   - Or copy-paste: ·                                                       *)
(*                                                                            *)
(* Full-width space 　 (U+3000) for Init separator:                            *)
(*   - macOS: Switch to CJK input, press Space; or Character Viewer           *)
(*   - Windows: Alt + 12288 (numpad) or Character Map                         *)
(*   - Linux: Ctrl+Shift+U, 3000, Enter                                       *)
(*   - Or copy-paste: 　                                                       *)
(*                                                                            *)
(* Unicode angle brackets ⟨⟩ (U+27E8, U+27E9) for Send/Recv:                  *)
(*   - macOS: Character Viewer, search "angle bracket"                        *)
(*   - Linux: Ctrl+Shift+U, 27e8/27e9, Enter                                  *)
(*   - Or copy-paste: ⟨ ⟩                                                     *)
(*   - ASCII alternative: < > also works                                      *)
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

Declare Scope dsdp_scope.
Declare Custom Entry dsdp.

(** * Entry/Exit Notations *)

(* Use {| |} as delimiters for entering the custom dsdp syntax *)
Notation "{| e |}" := e (e custom dsdp at level 99) : dsdp_scope.

(* Alternative keyword delimiter *)
Notation "'PROC' e 'END'" := e (e custom dsdp at level 99) : dsdp_scope.

Local Open Scope dsdp_scope.

(** * Basic Constructs *)

(* Finish - terminal state *)
Notation "'Finish'" := PFinish (in custom dsdp at level 0).

(* Ret - return a value *)
Notation "'Ret' x" := (PRet x) 
  (in custom dsdp at level 80, x constr at level 0).

(* Fail - error state *)  
Notation "'Fail'" := PFail (in custom dsdp at level 0).

(** * Sequencing with · (middle dot) *)

(* Single Init with continuation *)
Notation "'Init' x · P" := (PInit x P)
  (in custom dsdp at level 85, x constr at level 0,
   P custom dsdp at level 85, right associativity).

(* Send with continuation - ASCII angle brackets <n> *)
Notation "'Send<' n '>' x · P" := (PSend n x P)
  (in custom dsdp at level 85, n constr at level 0, x constr at level 0,
   P custom dsdp at level 85, right associativity).

(* Send with continuation - Unicode angle brackets ⟨n⟩ *)
Notation "'Send⟨' n '⟩' x · P" := (PSend n x P)
  (in custom dsdp at level 85, n constr at level 0, x constr at level 0,
   P custom dsdp at level 85, right associativity).

(* Recv with λ binder - ASCII angle bracket style *)
Notation "'Recv<' n '>' 'λ' x · P" := (PRecv n (fun x => P))
  (in custom dsdp at level 85, n constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(* Recv with λ binder - Unicode angle bracket style *)
Notation "'Recv⟨' n '⟩' 'λ' x · P" := (PRecv n (fun x => P))
  (in custom dsdp at level 85, n constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(* Recv with fun binder - ASCII *)
Notation "'Recv<' n '>' 'fun' x '=>' P" := (PRecv n (fun x => P))
  (in custom dsdp at level 85, n constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(* Recv with fun binder - Unicode *)
Notation "'Recv⟨' n '⟩' 'fun' x '=>' P" := (PRecv n (fun x => P))
  (in custom dsdp at level 85, n constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(** * Recv_dec and Recv_enc - specialized receive operations *)

(* In the real DSDP protocol, data is a sum type: msg + enc + pkey
   Recv_dec: receive encrypted, decrypt with key, continue with decrypted value
   Recv_enc: receive encrypted (cannot decrypt), continue with encrypted value
   
   For the demo, we model these with a simpler structure. The decrypt function
   is passed explicitly to make the notation work. *)

(* Recv_dec: Receive from party n, decrypt with key dk using dec function, bind decrypted value *)
Definition PRecv_dec {data : Type} (dec : data -> data -> option data)
    (n : nat) (dk : data) (f : data -> proc data) : proc data :=
  PRecv n (fun x => 
    match dec dk x with
    | Some v => f v
    | None => PFail
    end).

(* Recv_enc: Receive encrypted value from party n (no decryption) *)
Definition PRecv_enc {data : Type} (n : nat) (f : data -> proc data) : proc data :=
  PRecv n f.  (* Simplified: just pass through *)

(* Recv_dec with λ binder - ASCII *)
(* The dec function is passed as the first argument after the party id *)
Notation "'Recv_dec<' n '>' dec dk 'λ' x · P" := (PRecv_dec dec n dk (fun x => P))
  (in custom dsdp at level 85, n constr at level 0, 
   dec constr at level 0, dk constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(* Recv_dec with λ binder - Unicode *)
Notation "'Recv_dec⟨' n '⟩' dec dk 'λ' x · P" := (PRecv_dec dec n dk (fun x => P))
  (in custom dsdp at level 85, n constr at level 0,
   dec constr at level 0, dk constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(* Recv_enc with λ binder - ASCII *)
Notation "'Recv_enc<' n '>' 'λ' x · P" := (PRecv_enc n (fun x => P))
  (in custom dsdp at level 85, n constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(* Recv_enc with λ binder - Unicode *)
Notation "'Recv_enc⟨' n '⟩' 'λ' x · P" := (PRecv_enc n (fun x => P))
  (in custom dsdp at level 85, n constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(** * Multi-variable Init *)

(* Style 1: Using 　 (U+3000, full-width space) as separator - looks like real spaces *)
(* Notation: Init x 　 .. 　 y · P  expands to PInit x (.. (PInit y P) ..) *)
Notation "'Init' x '　' .. '　' y · P" := (PInit x .. (PInit y P) ..)
  (in custom dsdp at level 85, 
   x constr at level 0, y constr at level 0,
   P custom dsdp at level 85, right associativity).
Notation "'Init' x '　' .. '　' y ; P" := (PInit x .. (PInit y P) ..)
  (in custom dsdp at level 85, 
   x constr at level 0, y constr at level 0,
   P custom dsdp at level 85, right associativity).

(* Style 2: Using tuple-like syntax Init (x, y, z) · P *)
Notation "'Init' '(' x ',' .. ',' y ')' · P" := (PInit x .. (PInit y P) ..)
  (in custom dsdp at level 85,
   x constr at level 0, y constr at level 0,
   P custom dsdp at level 85, right associativity).
Notation "'Init' '(' x ',' .. ',' y ')' ; P" := (PInit x .. (PInit y P) ..)
  (in custom dsdp at level 85,
   x constr at level 0, y constr at level 0,
   P custom dsdp at level 85, right associativity).

(* NOTE: Escape notation for arbitrary Coq terms is tricky with custom entries.
   The constr at level 0 expects simple tokens, not complex expressions.
   For complex terms, use section variables or let-bindings outside the syntax. *)

(** * Variable reference *)

Notation "x" := x (in custom dsdp at level 0, x ident).

(******************************************************************************)
(** * ASCII Fallback Notations (semicolon instead of middle dot)              *)
(******************************************************************************)

(* Single Init - ASCII semicolon *)
Notation "'Init' x ; P" := (PInit x P)
  (in custom dsdp at level 85, x constr at level 0,
   P custom dsdp at level 85, right associativity).

(* Send - ASCII angle brackets with semicolon *)
Notation "'Send<' n '>' v ; P" := (PSend n v P)
  (in custom dsdp at level 85, n constr at level 0, v constr at level 0,
   P custom dsdp at level 85, right associativity).

(* Send - Unicode angle brackets with semicolon *)
Notation "'Send⟨' n '⟩' v ; P" := (PSend n v P)
  (in custom dsdp at level 85, n constr at level 0, v constr at level 0,
   P custom dsdp at level 85, right associativity).

(* Recv - ASCII angle brackets with semicolon *)
Notation "'Recv<' n '>' 'λ' x ; P" := (PRecv n (fun x => P))
  (in custom dsdp at level 85, n constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(* Recv - Unicode angle brackets with semicolon *)
Notation "'Recv⟨' n '⟩' 'λ' x ; P" := (PRecv n (fun x => P))
  (in custom dsdp at level 85, n constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(* Recv_dec - ASCII with semicolon *)
Notation "'Recv_dec<' n '>' dec dk 'λ' x ; P" := (PRecv_dec dec n dk (fun x => P))
  (in custom dsdp at level 85, n constr at level 0,
   dec constr at level 0, dk constr at level 0, x name,
   P custom dsdp at level 85, right associativity).

(* Recv_enc - ASCII with semicolon *)
Notation "'Recv_enc<' n '>' 'λ' x ; P" := (PRecv_enc n (fun x => P))
  (in custom dsdp at level 85, n constr at level 0, x name,
   P custom dsdp at level 85, right associativity).


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

(** Test 5: Multiple Init using 　 (full-width space U+3000) *)
Definition test_init_space : proc data := {| Init v1 　 v2 　 v3 · Finish |}.

(** Test 6: Multiple Init using tuple syntax Init (x, y, z) *)
Definition test_init_tuple : proc data := {| Init (v1, v2, v3) · Finish |}.

(** Test 7: Send with · *)
Definition test_send : proc data := {| Init v1 · Send<0> v1 · Finish |}.

(** Test 8: Recv with λ binder *)
Definition test_recv_lambda : proc data := {| Recv<0> λ x · Ret x |}.

(** Test 9: Recv with fun binder (alternative) *)
Definition test_recv_fun : proc data := {| Recv<0> fun x => Ret x |}.

(** Test 10: Combining Init, Send, Recv *)
Definition test_combined : proc data := 
  {| Init v1 · Send<1> v1 · Recv<1> λ x · Ret x |}.

(** Test 11: Using ASCII delimiter *)
Definition test_ascii : proc data := PROC Init v1 · Finish END.

(** Verify the desugaring is correct *)

(* test_init_space should desugar to nested Init *)
Lemma test_init_space_eq : test_init_space = PInit v1 (PInit v2 (PInit v3 PFinish)).
Proof. reflexivity. Qed.

(* test_init_tuple should desugar to same as test_init_space *)
Lemma test_init_tuple_eq : test_init_tuple = test_init_space.
Proof. reflexivity. Qed.

(* test_init_chained same as test_init_space *)
Lemma test_init_chained_eq : test_init_chained = test_init_space.
Proof. reflexivity. Qed.

(* test_recv_lambda should desugar to Recv with fun *)
Lemma test_recv_lambda_eq : test_recv_lambda = PRecv 0 (fun x => PRet x).
Proof. reflexivity. Qed.

End tests.

(******************************************************************************)
(** * Tests for Recv_dec and Recv_enc                                         *)
(******************************************************************************)

Section recv_dec_enc_tests.

Variable data : Type.
Variable decrypt : data -> data -> option data.
Variables (v1 dk : data).

(** Test 12: Recv_dec - receive and decrypt *)
(* Syntax: Recv_dec<party> decrypt_fn key λ var · P *)
Definition test_recv_dec : proc data := 
  {| Recv_dec<0> decrypt dk λ x · Ret x |}.

(** Test 13: Recv_enc - receive encrypted *)
Definition test_recv_enc : proc data := 
  {| Recv_enc<0> λ x · Ret x |}.

(** Test 14: Combined with Init and Send *)
Definition test_dsdp_like : proc data :=
  {| Init (dk, v1) · 
     Recv_enc<1> λ c · 
     Send<1> c · 
     Recv_dec<2> decrypt dk λ result · 
     Ret result |}.

(** Verify the desugaring is correct *)
Lemma test_recv_dec_eq : test_recv_dec = 
  PRecv 0 (fun x => match decrypt dk x with Some v => PRet v | None => PFail end).
Proof. reflexivity. Qed.

Lemma test_recv_enc_eq : test_recv_enc = PRecv 0 (fun x => PRet x).
Proof. reflexivity. Qed.

End recv_dec_enc_tests.

(******************************************************************************)
(** * Tests for data wrapper shorthand notations                              *)
(******************************************************************************)

Section wrapper_tests.

(** Test data wrapper shorthand notations: #x -> (k x), *'x -> (d x), $x -> (e x)
    
    In real DSDP, these are defined as:
      Definition d x : data := inl (inl x).
      Definition e x : data := inl (inr x).  
      Definition k x : data := inr x.
    
    For this demo, we use identity wrappers *)

Variable T : Type.

(* Local wrapper definitions *)
Definition k_wrap (x : T) : T := x.
Definition d_wrap (x : T) : T := x.
Definition e_wrap (x : T) : T := x.

(* Shorthand notations - defined as regular Coq notations *)
Local Notation "# x" := (k_wrap x) (at level 0, x at level 0).
Local Notation "& x" := (d_wrap x) (at level 0, x at level 0).  (* using & instead of * *)
Local Notation "$ x" := (e_wrap x) (at level 0, x at level 0).

Variables (dk v1 v2 a : T).

(** Test 15: '#x' for key wrapper *)
Definition test_key_wrapper : proc T := {| Init #dk · Finish |}.

(** Test 16: '&x' for data wrapper *)
Definition test_data_wrapper : proc T := {| Init &v1 · Finish |}.

(** Test 17: '$x' for encrypted wrapper *)
Definition test_enc_wrapper : proc T := {| Init $a · Finish |}.

(** Test 18: Combined wrappers with tuple-style Init *)
Definition test_wrappers_combined : proc T :=
  {| Init (#dk, &v1, &v2) · Send<0> $a · Finish |}.

(** Test 19: Combined wrappers with full-width space Init *)
Definition test_wrappers_fullwidth : proc T :=
  {| Init #dk　&v1　&v2 · Send<0> $a · Finish |}.

(** Verify desugaring *)
Lemma test_key_wrapper_eq : test_key_wrapper = PInit (k_wrap dk) PFinish.
Proof. reflexivity. Qed.

Lemma test_data_wrapper_eq : test_data_wrapper = PInit (d_wrap v1) PFinish.
Proof. reflexivity. Qed.

Lemma test_enc_wrapper_eq : test_enc_wrapper = PInit (e_wrap a) PFinish.
Proof. reflexivity. Qed.

End wrapper_tests.

(******************************************************************************)
(** * Example: Simple Two-Party Protocol                                      *)
(******************************************************************************)

Section two_party_example.

Variable msg : Type.
Variable secret : msg.

(* Party A: Initialize, send to B, wait for response, return *)
Definition partyA : proc msg :=
  {| Init secret · Send<1> secret · Recv<1> λ response · Ret response |}.

(* Party B: Receive from A, process, send back *)
Definition partyB : proc msg :=
  {| Recv<0> λ x · Send<0> x · Finish |}.

(* Verify structure *)
Lemma partyA_structure : 
  partyA = PInit secret (PSend 1 secret (PRecv 1 (fun response => PRet response))).
Proof. reflexivity. Qed.

Lemma partyB_structure :
  partyB = PRecv 0 (fun x => PSend 0 x PFinish).
Proof. reflexivity. Qed.

End two_party_example.

(******************************************************************************)
(** * Comparison: Unicode vs ASCII Syntax                                     *)
(******************************************************************************)

Section unicode_vs_ascii.

Variable T : Type.
Variables (dk v1 v2 v3 a b : T).

(* Local wrapper definitions for demo *)
Definition kw (x : T) : T := x.
Definition dw (x : T) : T := x.
Definition ew (x : T) : T := x.

Local Notation "# x" := (kw x) (at level 0, x at level 0).
Local Notation "& x" := (dw x) (at level 0, x at level 0).
Local Notation "$ x" := (ew x) (at level 0, x at level 0).

(*--------------------------------------------------------------------------*)
(* Unicode Version - prettier, paper-like                                    *)
(*   · = middle dot (Option+Shift+9 on macOS)                                *)
(*   λ = lambda                                                              *)
(*   ⟨⟩ = angle brackets                                                     *)
(*   　 = full-width space (CJK input)                                        *)
(*--------------------------------------------------------------------------*)

Definition example_unicode : proc T :=
  {| Init #dk　&v1　&v2 ·
     Send⟨1⟩ $a ·
     Recv⟨2⟩ λ x ·
     Send⟨1⟩ $b ·
     Finish |}.

(*--------------------------------------------------------------------------*)
(* ASCII Version - portable, no special characters needed                    *)
(*   ; = semicolon (replaces ·)                                              *)
(*   fun x => = function (replaces λ x ·)                                    *)
(*   <> = angle brackets (replaces ⟨⟩)                                       *)
(*   (x, y, z) = tuple (replaces 　 full-width space)                         *)
(*--------------------------------------------------------------------------*)

Definition example_ascii : proc T :=
  {| Init (#dk, &v1, &v2) ;
     Send<1> $a ;
     Recv<2> fun x =>
     Send<1> $b ;
     Finish |}.

(* Both versions produce identical terms *)
Lemma unicode_ascii_eq : example_unicode = example_ascii.
Proof. reflexivity. Qed.

(*--------------------------------------------------------------------------*)
(* Mixed Usage - you can mix ASCII and Unicode in the same program           *)
(*--------------------------------------------------------------------------*)

Definition example_mixed : proc T :=
  {| Init (#dk, &v1, &v2) ;      (* ASCII tuple and semicolon *)
     Send⟨1⟩ $a ·                (* Unicode brackets and dot *)
     Recv<2> λ x ;               (* ASCII brackets, Unicode lambda, ASCII semi *)
     Send<1> $b ·                (* ASCII brackets, Unicode dot *)
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
     {| ... |}                  - Enter custom dsdp syntax
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
   
   Recv_dec/Recv_enc:
     Recv_dec<n> D dk λ x · P   - ASCII brackets
     Recv_dec⟨n⟩ D dk λ x · P   - Unicode brackets
     Recv_dec<n> D dk fun x => P - Pure ASCII
     (same patterns for Recv_enc)
   
   Terminal:
     Ret v                      - Return value v
     Finish                     - Terminate successfully
     Fail                       - Terminate with failure
   
   Data wrapper shorthand (regular Coq notations):
     #x                         - (k x) key wrapper
     &x                         - (d x) data/message wrapper  
     $x                         - (e x) encrypted wrapper
*)

Print test_combined.
