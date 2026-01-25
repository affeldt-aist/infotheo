From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
Require Import smc_interpreter.

(**md**************************************************************************)
(* # Session Types for SMC Protocols                                          *)
(*                                                                            *)
(* Binary session types for verifying communication protocols in SMC.         *)
(* Type-indexed session types where both fuel AND session environment are     *)
(* automatically inferred by Coq's unification.                               *)
(*                                                                            *)
(* Based on:                                                                  *)
(* Kohei Honda, Vasco T. Vasconcelos, and Makoto Kubo.                        *)
(* "Language Primitives and Type Discipline for Structured                    *)
(*  Communication-Based Programming."                                         *)
(* In ESOP 1998, LNCS 1381, pp. 122-138. Springer, 1998.                      *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(** * Session Type Definitions                                                *)
(******************************************************************************)

Section stype_def.

(* dtype: user-defined data kind type (e.g., DT_Vec | DT_One) *)
Variable dtype : eqType.

(* Session type: parameterized by dtype to avoid combinatorial explosion *)
Inductive stype : Type :=
  | STSend : dtype -> stype -> stype   (* !d.S - send data of kind d *)
  | STRecv : dtype -> stype -> stype   (* ?d.S - receive data of kind d *)
  | STEnd : stype.                     (* end - session finished *)

(* Session environment: maps party ID to session type with that party *)
Definition senv : Type := nat -> stype.

(* Empty environment: no communication with anyone *)
Definition senv_end : senv := fun _ => STEnd.

(* Prepend a Send to environment for specific party *)
Definition senv_send (env : senv) (dst : nat) (d : dtype) : senv :=
  fun p => if p == dst then STSend d (env p) else env p.

(* Prepend a Recv to environment for specific party *)
Definition senv_recv (env : senv) (src : nat) (d : dtype) : senv :=
  fun p => if p == src then STRecv d (env p) else env p.

End stype_def.

(* Make stype arguments explicit for clarity *)
Arguments STSend {dtype}.
Arguments STRecv {dtype}.
Arguments STEnd {dtype}.
Arguments senv_end {dtype}.
Arguments senv_send {dtype}.
Arguments senv_recv {dtype}.

(******************************************************************************)
(** * Session-Indexed Process Type                                            *)
(******************************************************************************)

Section sproc_def.

Variable dtype : eqType.
Variable data : Type.
Variable classify : data -> dtype.  (* Maps data value to its kind - MUST be transparent *)

(* Process indexed by: which party I am (me), fuel (n), session environment (env) *)
(* Both fuel AND env are inferred by Coq's unification! *)
Inductive sproc (me : nat) : nat -> senv dtype -> Type :=

  (* Finish: base case, empty session environment *)
  | SFinish : sproc me 1 senv_end
  
  (* Ret: returns value, empty session environment *)
  | SRet : data -> sproc me 2 senv_end
  
  (* Init: doesn't affect session types, just initializes local data *)
  | SInit : forall n env,
      data -> 
      sproc me n env -> 
      sproc me n.+1 env
  
  (* Send: prepends STSend to session with dst *)
  (* dtype is explicit (like SRecv) to avoid scope issues with data values *)
  | SSend : forall n env dst (dt : dtype),
      data ->
      sproc me n env ->
      sproc me n.+1 (senv_send env dst dt)
  
  (* Recv: prepends STRecv to session with src *)
  (* dtype is explicit because it cannot be inferred from continuation *)
  | SRecv : forall n env src (dt : dtype),
      (data -> sproc me n env) ->
      sproc me n.+1 (senv_recv env src dt)
  
  (* Fail: polymorphic in env for error handling *)
  | SFail : forall n env, sproc me n env.

End sproc_def.

(* Note: classify is not used in constructors, so not included as parameter *)
Arguments SFinish {dtype data me}.
Arguments SRet {dtype data me}.
Arguments SInit {dtype data me n env}.
Arguments SSend {dtype data me n env} dst dt.
Arguments SRecv {dtype data me n env} src dt.
Arguments SFail {dtype data me n env}.

(******************************************************************************)
(** * Phase 1 Test: Minimal Example to Verify Unification                     *)
(******************************************************************************)

Section test_inference.

(* Simple dtype for testing: just two kinds *)
Inductive test_dtype : Type := DT_A | DT_B.

(* Make test_dtype an eqType - following pattern from homomorphic_encryption.v *)
Definition test_dtype_eqb_subproof (d1 d2 : test_dtype) : { d1 = d2 } + { d1 <> d2 }.
Proof. decide equality. Defined.

Definition test_dtype_eqb (d1 d2 : test_dtype) : bool :=
  if test_dtype_eqb_subproof d1 d2 then true else false.

Lemma test_dtype_eqP : Equality.axiom test_dtype_eqb.
Proof.
move=> d1 d2.
rewrite /test_dtype_eqb.
by case: test_dtype_eqb_subproof => /= H; constructor.
Qed.

HB.instance Definition _ := hasDecEq.Build test_dtype test_dtype_eqP.

(* Simple data type: just nat for testing *)
Definition test_data := nat.

(* Simple classifier: even -> DT_A, odd -> DT_B *)
Definition test_classify (d : test_data) : test_dtype :=
  if odd d then DT_B else DT_A.

(* Party identifiers for testing *)
Definition party0 : nat := 0.
Definition party1 : nat := 1.

(* TEST 1: Simple Finish - should infer fuel=1, env=senv_end *)
(* Use @ for explicit application to make type arguments clear *)
(* sproc now takes: dtype, data, me, fuel, senv (no classify) *)
Definition test1 : @sproc test_dtype test_data party0 _ _ :=
  SFinish.

(* Verify test1's inferred types *)
Check test1.
(* Should show: sproc ... party0 1 senv_end *)

(* TEST 2: Send then Finish - should infer fuel=2, env with one Send *)
(* SSend now takes: dst, dtype, data, continuation *)
Definition test2 : @sproc test_dtype test_data party0 _ _ :=
  SSend party1 DT_A 42 SFinish.

Check test2.
(* Should show: sproc ... party0 2 (senv_send senv_end party1 DT_A) *)

(* TEST 3: Two Sends then Finish *)
Definition test3 : @sproc test_dtype test_data party0 _ _ :=
  SSend party1 DT_B 1 (SSend party1 DT_A 2 SFinish).

Check test3.

(* TEST 4: Init then Send then Finish *)
Definition test4 : @sproc test_dtype test_data party0 _ _ :=
  SInit 100 (SSend party1 DT_A 42 SFinish).

Check test4.

(* TEST 5: Recv then Finish - need explicit dtype *)
Definition test5 : @sproc test_dtype test_data party0 _ _ :=
  SRecv party1 DT_A (fun _ => SFinish).

Check test5.

(* TEST 6: Send to party1, Recv from party1 - mixed communication *)
Definition test6 : @sproc test_dtype test_data party0 _ _ :=
  SSend party1 DT_A 10 (SRecv party1 DT_B (fun _ => SFinish)).

Check test6.

(* TEST 7: More complex - communication with multiple parties *)
Definition party2 : nat := 2.

Definition test7 : @sproc test_dtype test_data party0 _ _ :=
  SRecv party2 DT_A (fun x =>
  SRecv party2 DT_B (fun y =>
  SSend party1 DT_A (x + y) SFinish)).

Check test7.

(* Verify we can extract session type information *)
Definition get_stype {dtype : eqType} {data : Type}
    {me : nat} {n : nat} {env : senv dtype} 
    (p : @sproc dtype data me n env) (them : nat) : stype dtype :=
  env them.

(* Check session type of test7 with party1 *)
Eval compute in get_stype test7 party1.
(* Should show: STSend DT_A STEnd (since we send even number to party1) *)

(* Check session type of test7 with party2 *)
Eval compute in get_stype test7 party2.
(* Should show: STRecv DT_A (STRecv DT_B STEnd) *)

End test_inference.

(******************************************************************************)
(** * Duality (Phase 2 preview)                                               *)
(******************************************************************************)

Section duality.

Variable dtype : eqType.

(* Duality: send becomes recv, recv becomes send *)
Fixpoint dual (s : stype dtype) : stype dtype :=
  match s with
  | STSend d k => STRecv d (dual k)
  | STRecv d k => STSend d (dual k)
  | STEnd => STEnd
  end.

(* Duality is involutive *)
Lemma dual_involutive : forall s : stype dtype, dual (dual s) = s.
Proof.
move=> s.
elim: s => //=.
- move=> d s IH.
  rewrite IH.
  reflexivity.
- move=> d s IH.
  rewrite IH.
  reflexivity.
Qed.

End duality.

(******************************************************************************)
(** * Existential Process Wrapper (aproc)                                     *)
(******************************************************************************)

Section aproc_def.

Variable dtype : eqType.
Variable data : Type.

(* aproc: existentially wraps me, fuel, and senv so processes can be stored in lists *)
Definition aproc : Type := { me : nat & { n : nat & { env : senv dtype & @sproc dtype data me n env }}}.

(* Smart constructor *)
Definition mk_aproc {me : nat} {n : nat} {env : senv dtype} 
    (p : @sproc dtype data me n env) : aproc :=
  existT _ me (existT _ n (existT _ env p)).

(* Accessors *)
Definition aproc_me (ap : aproc) : nat := projT1 ap.
Definition aproc_fuel (ap : aproc) : nat := projT1 (projT2 ap).
Definition aproc_env (ap : aproc) : senv dtype := projT1 (projT2 (projT2 ap)).
Definition aproc_proc (ap : aproc) : @sproc dtype data (aproc_me ap) (aproc_fuel ap) (aproc_env ap) :=
  projT2 (projT2 (projT2 ap)).

(* Get session type with specific party *)
Definition aproc_stype (ap : aproc) (them : nat) : stype dtype :=
  aproc_env ap them.

End aproc_def.

Arguments mk_aproc {dtype data me n env}.
Arguments aproc_me {dtype data}.
Arguments aproc_fuel {dtype data}.
Arguments aproc_env {dtype data}.
Arguments aproc_proc {dtype data}.
Arguments aproc_stype {dtype data}.

(******************************************************************************)
(** * Session Type Decidable Equality                                         *)
(******************************************************************************)

Section stype_eq.

Variable dtype : eqType.

(* Decidable equality for session types *)
Fixpoint stype_eqb (s1 s2 : stype dtype) : bool :=
  match s1, s2 with
  | STEnd, STEnd => true
  | STSend d1 k1, STSend d2 k2 => (d1 == d2) && stype_eqb k1 k2
  | STRecv d1 k1, STRecv d2 k2 => (d1 == d2) && stype_eqb k1 k2
  | _, _ => false
  end.

Lemma stype_eqP : Equality.axiom stype_eqb.
Proof.
move=> s1 s2.
elim: s1 s2 => [d1 k1 IH|d1 k1 IH|] [d2 k2|d2 k2|] //=; try by constructor.
- case: (d1 =P d2) => [<-|Hneq] /=.
  + case: (IH k2) => [<-|Hneq]; first by constructor.
    constructor. by case.
  + constructor. by case.
- case: (d1 =P d2) => [<-|Hneq] /=.
  + case: (IH k2) => [<-|Hneq]; first by constructor.
    constructor. by case.
  + constructor. by case.
Qed.

HB.instance Definition _ := hasDecEq.Build (stype dtype) stype_eqP.

End stype_eq.

(******************************************************************************)
(** * Duality Checking                                                        *)
(******************************************************************************)

Section duality_check.

Variable dtype : eqType.

(* Check if two session types are dual *)
Definition are_dual (s1 s2 : stype dtype) : bool := s1 == dual s2.

(* Check if two aprocs have dual session types for communication between them *)
Definition channels_dual {data : Type} (ap1 ap2 : aproc dtype data) : bool :=
  let me1 := aproc_me ap1 in
  let me2 := aproc_me ap2 in
  (* ap1's view of me2 should be dual to ap2's view of me1 *)
  are_dual (aproc_stype ap1 me2) (aproc_stype ap2 me1).

End duality_check.

Arguments are_dual {dtype}.
Arguments channels_dual {dtype data}.

(******************************************************************************)
(** * Phase 2 Tests                                                           *)
(******************************************************************************)

Section test_phase2.

(* Reuse test_dtype from Phase 1 tests *)
Let dtype := test_dtype.
Let data := test_data.

(* Two-party protocol test *)
(* Party 0 sends to Party 1, then finishes *)
Definition proto_p0 : @sproc dtype data 0 _ _ :=
  SSend 1 DT_A 42 SFinish.

(* Party 1 receives from Party 0, then finishes *)
Definition proto_p1 : @sproc dtype data 1 _ _ :=
  SRecv 0 DT_A (fun _ => SFinish).

(* Wrap in aproc *)
Definition aproc_p0 : aproc dtype data := mk_aproc proto_p0.
Definition aproc_p1 : aproc dtype data := mk_aproc proto_p1.

(* Test: Extract session types *)
Eval compute in aproc_stype aproc_p0 1.  (* Should be: STSend DT_A STEnd *)
Eval compute in aproc_stype aproc_p1 0.  (* Should be: STRecv DT_A STEnd *)

(* Test: Check duality *)
Eval compute in channels_dual aproc_p0 aproc_p1.  (* Should be: true *)

(* Verify duality mathematically *)
Lemma proto_dual_correct : channels_dual aproc_p0 aproc_p1 = true.
Proof. by native_compute. Qed.

End test_phase2.

(******************************************************************************)
(** * Specialized Recv Wrappers                                               *)
(******************************************************************************)

(* These wrappers provide type-safe receive operations that:
   1. Specify the expected dtype for session type tracking
   2. Pattern match on data to extract the expected form
   3. Use SFail if the data doesn't match the expected form *)

Section recv_wrappers.

Variable dtype : eqType.
Variable data : Type.

(* A "checker" function that extracts a typed value from data, or fails *)
(* For example: is_scalar : data -> option TX *)
Variable T : Type.                    (* Target type (e.g., TX for scalars) *)
Variable dt : dtype.                  (* dtype for session tracking *)
Variable check : data -> option T.    (* Checker: data -> option T *)

(* Specialized receive: receive from src, check data, continue with typed value *)
Definition SRecv_check {me : nat} {n : nat} {env : senv dtype} 
    (src : nat) (f : T -> @sproc dtype data me n env) : @sproc dtype data me n.+1 (senv_recv env src dt) :=
  SRecv src dt (fun d => 
    match check d with
    | Some v => f v
    | None => SFail
    end).

End recv_wrappers.

Arguments SRecv_check {dtype data T dt check me n env} src.

(* Example instantiation for scalar product data types *)
Section recv_wrappers_example.

(* Define dtype for scalar product: vectors vs scalars *)
Inductive sp_dtype : Type := DT_Vec | DT_One.

Definition sp_dtype_eqb_subproof (d1 d2 : sp_dtype) : { d1 = d2 } + { d1 <> d2 }.
Proof. decide equality. Defined.

Definition sp_dtype_eqb (d1 d2 : sp_dtype) : bool :=
  if sp_dtype_eqb_subproof d1 d2 then true else false.

Lemma sp_dtype_eqP : Equality.axiom sp_dtype_eqb.
Proof.
move=> d1 d2. rewrite /sp_dtype_eqb.
by case: sp_dtype_eqb_subproof => /= H; constructor.
Qed.

HB.instance Definition _ := hasDecEq.Build sp_dtype sp_dtype_eqP.

(* Data type for scalar product: sum of vector and scalar *)
Variable TX : Type.  (* scalar type *)
Variable VX : Type.  (* vector type *)
Let sp_data := (TX + VX)%type.

(* Checkers *)
Definition is_scalar (d : sp_data) : option TX :=
  match d with inl v => Some v | inr _ => None end.

Definition is_vector (d : sp_data) : option VX :=
  match d with inr v => Some v | inl _ => None end.

(* Specialized receivers for scalar product *)
Definition SRecv_one {me n env} (src : nat) (f : TX -> @sproc sp_dtype sp_data me n env) 
    : @sproc sp_dtype sp_data me n.+1 (senv_recv env src DT_One) :=
  @SRecv_check sp_dtype sp_data TX DT_One is_scalar me n env src f.

Definition SRecv_vec {me n env} (src : nat) (f : VX -> @sproc sp_dtype sp_data me n env)
    : @sproc sp_dtype sp_data me n.+1 (senv_recv env src DT_Vec) :=
  @SRecv_check sp_dtype sp_data VX DT_Vec is_vector me n env src f.

End recv_wrappers_example.

(******************************************************************************)
(** * Phase 4: Erasure to Original proc Type                                  *)
(******************************************************************************)

(* Use proc type from smc_interpreter *)

Section erasure.

Variable data : Type.
Variable dtype : eqType.

(* Erasure: convert session-typed sproc to fuel-indexed proc *)
(* This erases the session environment index, keeping only fuel *)
Fixpoint erase {me : nat} {n : nat} {env : senv dtype} 
    (p : @sproc dtype data me n env) : smc_interpreter.proc data n :=
  match p in @sproc _ _ _ m _ return smc_interpreter.proc data m with
  | SFinish => Finish
  | SRet d => Ret d
  | @SInit _ _ _ n' env' d k => Init d (erase k)
  | @SSend _ _ _ n' env' dst dt d k => Send dst d (erase k)
  | @SRecv _ _ _ n' env' src dt f => Recv src (fun d => erase (f d))
  | @SFail _ _ _ n' env' => @Fail data n'
  end.

(* Erase session-typed aproc to smc_interpreter.aproc *)
Definition erase_aproc (ap : aproc dtype data) : smc_interpreter.aproc data :=
  let me := aproc_me ap in
  let n := aproc_fuel ap in
  let env := aproc_env ap in
  let p := aproc_proc ap in
  pack (erase p).

End erasure.

Arguments erase {data dtype me n env}.
Arguments erase_aproc {data dtype}.

(******************************************************************************)
(** * Notations for Session-Typed Process Lists                               *)
(******************************************************************************)

(* Declare scope for session-typed processes *)
Declare Scope sproc_scope.

(* Notation for packing session-typed processes into erased aproc list *)
(* Mirrors [procs p;..;q] from smc_interpreter but with session type erasure *)
(* Usage: [sprocs p ; .. ; q ] where p,q are sproc values *)
Notation "[sprocs p ; .. ; q ]" := 
  (cons (erase_aproc (mk_aproc p)) .. (cons (erase_aproc (mk_aproc q)) nil) ..)
  (at level 0) : sproc_scope.

(* For fuel computation, use sum_fuel from smc_interpreter directly *)
(* [> ps] notation is already available from smc_interpreter *)

Local Open Scope sproc_scope.

(******************************************************************************)
(** * Phase 4 Tests: Erasure Verification                                     *)
(******************************************************************************)

Section test_erasure.

(* Test with concrete types *)
Let dtype := test_dtype.
Let data := test_data.

(* Test erasure on simple process *)
Definition erase_test1 : proc data 1 := erase test1.
Check erase_test1.

Definition erase_test2 : proc data 2 := erase test2.
Check erase_test2.

(* Test that erased process has same fuel *)
Lemma erase_preserves_fuel : forall {me n env} (p : @sproc dtype data me n env),
  True. (* Fuel is preserved by construction - it's the same index n *)
Proof. done. Qed.

(* The erased processes can now be used with the original interpreter *)
(* by importing smc_interpreter and using:
   
   From infotheo Require Import smc_interpreter.
   
   Definition run_scalar_product sa sb ra xa xb yb :=
     let procs := [procs 
       erase_aproc (sp_aproc_coserv sa sb ra);
       erase_aproc (sp_aproc_alice xa);
       erase_aproc (sp_aproc_bob xb yb)
     ] in
     run_interp [> procs] procs.
*)

End test_erasure.

(******************************************************************************)
(** * Summary: Session Type System                                            *)
(******************************************************************************)

(*
This file provides a session type system for SMC protocols with the following
key properties:

1. AUTOMATIC INFERENCE: Both fuel AND session environment are automatically
   inferred by Coq's type unification. Users write programs without explicit
   type annotations for these indices.

2. PARAMETERIZED TYPES: Session types (stype) are parameterized by a user-
   defined dtype to avoid combinatorial explosion when adding new data kinds.

3. DUALITY VERIFICATION: The channels_dual function verifies that two parties
   have dual session types, ensuring protocol correctness.

4. ERASURE: Session-typed programs can be erased to the original fuel-indexed
   proc type for execution with the existing interpreter.

Usage:
  1. Define your dtype (e.g., DT_Vec | DT_One for scalar product)
  2. Define your data type (e.g., TX + VX)
  3. Write programs using sproc with _ for fuel and senv indices
  4. Verify duality using channels_dual and native_compute
  5. Erase to proc for execution with smc_interpreter

Example:
  Definition my_sender : @sproc my_dtype my_data 0 _ _ :=
    SSend 1 DT_A 42 SFinish.
  
  Lemma sender_receiver_dual : 
    channels_dual (mk_aproc my_sender) (mk_aproc my_receiver) = true.
  Proof. by native_compute. Qed.
*)

