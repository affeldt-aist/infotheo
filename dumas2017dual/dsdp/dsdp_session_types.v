From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
Require Import ssr_ext.
Require Import smc_session_types homomorphic_encryption.
Require Import dsdp_interface.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ========================================================================== *)
(* Session-Typed Wrappers for SMC-DSDP                                        *)
(* ========================================================================== *)

(* Session-typed versions using sproc from smc_session_types.
   These coexist with the proc-based wrappers above. *)

Section smc_dsdp_session_types.

Variable PHE : AHEAlgebra_scheme.

Let data := di_data (Standard_DSDP_Interface PHE).
Let e := di_e (Standard_DSDP_Interface PHE).
Let D := @dec PHE.

(* Receive encrypted - pattern match data, use SFail on mismatch *)
Definition DRecv_enc {party n env} (src : nat)
    (f : party_cipher PHE -> @sproc dsdp_dtype data party n env)
    : @sproc dsdp_dtype data party n.+1 (senv_recv env src DT_Enc) :=
  SRecv src DT_Enc (fun d => 
    match @std_from_enc PHE d with
    | Some enc => f enc
    | None => SFail
    end).

(* Receive encrypted and decrypt - still tracks as DT_Enc (what's on the wire) *)
(* NOTE: D returns option msg, so need nested match for decrypt failure *)
Definition DRecv_dec {party n env} (src : nat) (dk : pkey PHE)
    (f : plain PHE -> @sproc dsdp_dtype data party n env)
    : @sproc dsdp_dtype data party n.+1 (senv_recv env src DT_Enc) :=
  SRecv src DT_Enc (fun d => 
    match @std_from_enc PHE d with
    | Some enc => match D dk enc with
                  | Some msg => f msg
                  | None => SFail  (* decrypt failure *)
                  end
    | None => SFail  (* not an encrypted value *)
    end).

Definition DSend {party n env} (dst : nat) (x : data)
    (p : @sproc dsdp_dtype data party n env)
    : @sproc dsdp_dtype data party n.+1 (senv_send env dst DT_Enc) :=
  SSend dst DT_Enc x p.

(* Init/Ret wrappers - can init any data kind (msg, enc, key) *)
(* Init doesn't affect session env since it's local storage *)
Definition DInit {party n env} (x : data) (p : @sproc dsdp_dtype data party n env)
    : @sproc dsdp_dtype data party n.+1 env := 
  SInit x p.

Definition DRet {party : nat} (x : data) : @sproc dsdp_dtype data party 2 senv_end := 
  SRet x.

Definition DFinish {party : nat} : @sproc dsdp_dtype data party 1 senv_end := 
  SFinish.

End smc_dsdp_session_types.

(* Arguments declarations for implicit parameters *)
Arguments DRecv_enc {PHE party n env}.
Arguments DRecv_dec {PHE party n env}.
Arguments DSend {PHE party n env}.
Arguments DInit {PHE party n env}.
Arguments DRet {PHE party}.
Arguments DFinish {PHE party}.
