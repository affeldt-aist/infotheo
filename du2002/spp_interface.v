From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg ring.
From mathcomp Require Import reals.
Require Import smc_interpreter smc_session_types pismc.

(**md**************************************************************************)
(* # SMC-SPP Interface                                                        *)
(*                                                                            *)
(* Shared type definitions for the SMC-SPP.                                   *)
(* This file eliminates duplication across spp_program.v and spp_pismc.v,     *)
(* enabling cross-file equality proofs.                                       *)
(*                                                                            *)
(* Components:                                                                *)
(*   sp_dtype       - Reuses smc_session_types.sp_dtype (DT_Vec | DT_One)     *)
(*   alice/bob/coserv - Party identifiers                                     *)
(*   data/one/vec   - Data type and constructors                              *)
(*   SRecv_one/vec  - Session-typed receive wrappers                          *)
(*   SPSendVec/One  - Session-typed send wrappers (auto dtype from &/!)       *)
(*   spp_sendable_vec/one - Sendable constructors for piSMC notation          *)
(*                                                                            *)
(******************************************************************************)

Import GRing.Theory.
Import Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* sp_dtype (DT_Vec | DT_One) is imported from smc_session_types *)

(******************************************************************************)
(** * SMC-SPP Types (parameterized by TX, VX)                                *)
(******************************************************************************)

Section smc_spp_types.

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

Definition SPInit {party n env} (x : data)
    (p : @sproc sp_dtype data party n env)
    : @sproc sp_dtype data party n.+1 env := SInit x p.

Definition SPRet {party : nat} (x : data) : @sproc sp_dtype data party 2 senv_end := 
  SRet x.

End smc_spp_types.

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
