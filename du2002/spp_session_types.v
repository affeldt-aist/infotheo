From HB Require Import structures.
From mathcomp Require Import all_boot all_order.
Require Import ssr_ext.
Require Import smc_session_types.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(** * SMC-SPP Receive Wrappers                                               *)
(******************************************************************************)

Section smc_spp_recv_wrappers.

(* Define dtype for SMC-SPP: vectors vs scalars *)
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

(* Data type for SMC-SPP: sum of vector and scalar *)
Variable TX : Type.  (* scalar type *)
Variable VX : Type.  (* vector type *)
Let sp_data := (TX + VX)%type.

(* Checkers *)
Definition is_scalar (d : sp_data) : option TX :=
  match d with inl v => Some v | inr _ => None end.

Definition is_vector (d : sp_data) : option VX :=
  match d with inr v => Some v | inl _ => None end.

(* Specialized receivers for SMC-SPP *)
Definition SRecv_one {party n env} (src : nat) (f : TX -> @sproc sp_dtype sp_data party n env) 
    : @sproc sp_dtype sp_data party n.+1 (senv_recv env src DT_One) :=
  @SRecv_check sp_dtype sp_data TX DT_One is_scalar party n env src f.

Definition SRecv_vec {party n env} (src : nat) (f : VX -> @sproc sp_dtype sp_data party n env)
    : @sproc sp_dtype sp_data party n.+1 (senv_recv env src DT_Vec) :=
  @SRecv_check sp_dtype sp_data VX DT_Vec is_vector party n env src f.

End smc_spp_recv_wrappers.
