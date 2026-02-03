From HB Require Import structures.
From mathcomp Require Import all_boot all_order.
Require Import smc_session_types.

(* TODO: move more notations and wrappers here. *)

(* Scope and custom entry *)
Declare Scope pismc_scope.
Declare Custom Entry pismc.

(* Program delimiter.
   Note that `{| e |}` is conflicting with the Rocq structure syntax.
   So we use `\pi{ e }` instead. *)
Notation "'\pi{' e '}'" := e (e custom pismc at level 99) : pismc_scope.

