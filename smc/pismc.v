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

(* ForEach - iterate over finType elements using sproc_iter.
   Usage: ForEach 'I_n as f, i => (fun n env cont => ...) ; P
   - fT: the finType to enumerate
   - f: bound variable for each element
   - i: bound variable for the index
   - body: function (n : nat) (env : senv dtype) (cont : sproc ...) -> sproc ...
   - fuel_step = S (hardcoded); use sproc_iter directly for other fuel steps *)
Notation "'ForEach' fT 'as' f ',' i '=>' body ; P" :=
  (sproc_iter _ S _ (fun f i => body) (enum fT) 0 P)
  (in custom pismc at level 85, fT constr at level 0, f name, i name,
   body constr at level 0,
   P custom pismc at level 85, right associativity).

