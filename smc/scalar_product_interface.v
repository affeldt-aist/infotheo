From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg ring.
From mathcomp Require Import Rstruct reals.
Require Import smc_interpreter smc_session_types.

(**md**************************************************************************)
(* # Scalar Product Interface                                                 *)
(*                                                                            *)
(* Shared type definitions for the scalar product protocol.                   *)
(* This file eliminates duplication across scalar_product_program.v and       *)
(* scalar_product_alt_syntax.v, enabling cross-file equality proofs.          *)
(*                                                                            *)
(* Components:                                                                *)
(*   sp_dtype       - Data type kind (DT_Vec | DT_One) with eqType instance   *)
(*   alice/bob/coserv - Party identifiers                                     *)
(*   data/one/vec   - Data type and constructors                              *)
(*   SRecv_one/vec  - Session-typed receive wrappers                          *)
(*   SPSendVec/One  - Session-typed send wrappers (auto dtype from &/!)       *)
(*                                                                            *)
(******************************************************************************)

Import GRing.Theory.
Import Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(******************************************************************************)
(** * Session Data Type Kind (outside section - no TX/VX dependency)          *)
(******************************************************************************)

(* Data type kinds for session types in scalar product protocol *)
Inductive sp_dtype : Type := DT_Vec | DT_One.

(* Decidable equality for sp_dtype *)
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

(******************************************************************************)
(** * Scalar Product Types (parameterized by TX, VX)                          *)
(******************************************************************************)

Section scalar_product_types.

Variable TX : finComRingType.
Variable VX : lmodType TX.
Variable dotproduct : VX -> VX -> TX.

(* Party identifiers *)
Definition alice : nat := 0.
Definition bob : nat := 1.
Definition coserv : nat := 2.

(* Data type: scalar + vector *)
Definition data := (TX + VX)%type.
Definition one (x : TX) : data := inl x.
Definition vec (x : VX) : data := inr x.

(******************************************************************************)
(** * Session-Typed Receive Wrappers                                          *)
(******************************************************************************)

(* Receive scalar (TX) value *)
Definition SRecv_one {party n env} (src : nat) 
    (f : TX -> @sproc sp_dtype data party n env) 
    : @sproc sp_dtype data party n.+1 (senv_recv env src DT_One) :=
  SRecv src DT_One (fun d => match d with inl v => f v | inr _ => SFail end).

(* Receive vector (VX) value *)
Definition SRecv_vec {party n env} (src : nat)
    (f : VX -> @sproc sp_dtype data party n env)
    : @sproc sp_dtype data party n.+1 (senv_recv env src DT_Vec) :=
  SRecv src DT_Vec (fun d => match d with inr v => f v | inl _ => SFail end).

(******************************************************************************)
(** * Session-Typed Send Wrappers (auto dtype from type)                      *)
(******************************************************************************)

(* Send vector - takes VX directly, applies vec wrapper and DT_Vec *)
Definition SPSendVec {party n env} (dst : nat) (x : VX) 
    (p : @sproc sp_dtype data party n env) 
    : @sproc sp_dtype data party n.+1 (senv_send env dst DT_Vec) := 
  SSend dst DT_Vec (vec x) p.

(* Send scalar - takes TX directly, applies one wrapper and DT_One *)
Definition SPSendOne {party n env} (dst : nat) (x : TX)
    (p : @sproc sp_dtype data party n env)
    : @sproc sp_dtype data party n.+1 (senv_send env dst DT_One) := 
  SSend dst DT_One (one x) p.

(******************************************************************************)
(** * Init Wrapper                                                            *)
(******************************************************************************)

(* Init wrapper for session-typed processes *)
Definition SPInit {party n env} (x : data) (p : @sproc sp_dtype data party n env) 
    : @sproc sp_dtype data party n.+1 env := SInit x p.

(* Ret wrapper *)
Definition SPRet {party : nat} (x : data) : @sproc sp_dtype data party 2 senv_end := SRet x.

End scalar_product_types.

(* Argument declarations for convenient usage *)
(* Note: alice, bob, coserv don't depend on section variables *)
Arguments data TX VX : clear implicits.
Arguments one {TX VX}.
Arguments vec {TX VX}.
Arguments SRecv_one {TX VX party n env}.
Arguments SRecv_vec {TX VX party n env}.
Arguments SPSendVec {TX VX party n env}.
Arguments SPSendOne {TX VX party n env}.
Arguments SPInit {TX VX party n env}.
Arguments SPRet {TX VX party}.
