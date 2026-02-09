From HB Require Import structures.
From mathcomp Require Import all_boot all_order.
Require Import smc_session_types.

(* Scope and custom entry *)
Declare Scope pismc_scope.
Declare Custom Entry pismc.

(* Program delimiter.
   Note that `{| e |}` is conflicting with the Rocq structure syntax.
   So we use `\pi{ e }` instead. *)
Notation "'\pi{' e '}'" := e (e custom pismc at level 99) : pismc_scope.

(* Shared piSMC notations - protocol-independent constructors.
   Send/Recv notations are protocol-specific (dtype-dependent) and
   remain in each protocol's _pismc.v file. *)

(* Terminal state *)
Notation "'Finish'" := SFinish (in custom pismc at level 0).

(* Return a value *)
Notation "'Ret' x" := (SRet x)
  (in custom pismc at level 80, x constr at level 0).

(* Init - single value *)
Notation "'Init' x ; P" := (SInit x P)
  (in custom pismc at level 85, x constr at level 0,
   P custom pismc at level 85, right associativity).

(* Init - multi-var tuple *)
Notation "'Init' '(' x ',' .. ',' y ')' ; P" :=
  (SInit x .. (SInit y P) ..)
  (in custom pismc at level 85,
   x constr at level 0, y constr at level 0,
   P custom pismc at level 85, right associativity).

