From HB Require Import structures.
From mathcomp Require Import all_boot all_order.
Require Import smc_session_types.

(* Scope and custom entry *)
Declare Scope pismc_scope.
Declare Custom Entry pismc.

Section sendable_def.

(* Sendable: wrapped data that knows its dtype tag for session type tracking *)
Structure Sendable {dtype : eqType} {data : Type} := {
  sendable_tag : dtype;
  sendable_data : data;
}.

(* Generic piSend using Sendable *)
(* Use it like: piSend 3 ({| sendable_tag := 0; sendable_data := 1 |}) ...*)
Definition piSend {dtype data party n env} (dst : nat) 
    (s : Sendable)
    (p : @sproc dtype data party n env)
    : @sproc dtype data party n.+1 (senv_send env dst (sendable_tag s)) :=
  SSend dst (sendable_tag s) (sendable_data s) p.

End sendable_def.

Arguments piSend {dtype data party n env} dst s p.

Section sp_wrapper.

(* Init wrapper for session-typed processes - accepts Sendable, extracts data *)
Definition SPInit {party n env data} (s : @Sendable sp_dtype data)
  (p : @sproc sp_dtype data party n env) :
  @sproc sp_dtype data party n.+1 env := SInit (sendable_data s) p.

(* Ret wrapper *)
Definition SPRet {data} {party : nat} (x : data) :
  @sproc sp_dtype data party 2 senv_end := SRet x.

End sp_wrapper.

(* Program delimiter.
   Note that `{| e |}` is conflicting with the Rocq structure syntax.
   So we use `pi{ e }` instead. *)
Notation "'pi{' e '}'" := e (e custom pismc at level 99) : pismc_scope.

(* Terminal states - use SFinish/SFail directly *)
Notation "'Finish'" := SFinish (in custom pismc at level 0).
Notation "'Fail'" := SFail (in custom pismc at level 0).

(* Single-var Init: Init x ; P *)
Notation "'Init' x ; P" := (SPInit x P)
  (in custom pismc at level 85,
   x constr at level 0,
   P custom pismc at level 85, right associativity).

(* Multi-var Init using tuple syntax: Init (x, y, z) ; P *)
Notation "'Init' '(' x ',' .. ',' y ')' ; P" := (SPInit x .. (SPInit y P) ..)
  (in custom pismc at level 85,
   x constr at level 0, y constr at level 0,
   P custom pismc at level 85, right associativity).

(* Generic Send - uses piSend with Sendable *)
Notation "'Send<' p '>' x ; P" := (piSend p x P)
  (in custom pismc at level 85, p constr at level 0, x constr at level 0,
   P custom pismc at level 85, right associativity).

(* Generic Ret - uses SRet directly *)
Notation "'Ret' x" := (SRet x)
  (in custom pismc at level 80, x constr).

(* Variable reference *)
Notation "x" := x (in custom pismc at level 0, x ident).
