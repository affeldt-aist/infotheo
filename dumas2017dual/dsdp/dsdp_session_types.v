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

Variable AHE : AHEncType.

Let data := di_data (Standard_DSDP_Interface AHE).
Let e := di_e (Standard_DSDP_Interface AHE).
Let D := @dec AHE.

(* Receive encrypted - pattern match data, use SFail on mismatch *)
Definition DRecv_enc {party n env} (src : nat)
    (f : cipher AHE -> @sproc dsdp_dtype data party n env)
    : @sproc dsdp_dtype data party n.+1 (senv_recv env src DT_Enc) :=
  SRecv src DT_Enc (fun d => 
    match @std_from_enc AHE d with
    | Some enc => f enc
    | None => SFail
    end).

(* Receive encrypted and decrypt - still tracks as DT_Enc (what's on the wire) *)
(* NOTE: D returns option msg, so need nested match for decrypt failure *)
Definition DRecv_dec {party n env} (src : nat) (dk : priv_key AHE)
    (f : plain AHE -> @sproc dsdp_dtype data party n env)
    : @sproc dsdp_dtype data party n.+1 (senv_recv env src DT_Enc) :=
  SRecv src DT_Enc (fun d => 
    match @std_from_enc AHE d with
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

(* Init/Ret wrappers - can init any data kind (msg, enc, priv_key) *)
(* Init doesn't affect session env since it's local storage *)
Definition DInit {party n env} (x : data) (p : @sproc dsdp_dtype data party n env)
    : @sproc dsdp_dtype data party n.+1 env := 
  SInit x p.

Definition DRet {party : nat} (x : data) : @sproc dsdp_dtype data party 2 senv_end := 
  SRet x.

Definition DFinish {party : nat} : @sproc dsdp_dtype data party 1 senv_end := 
  SFinish.

(* Iteration wrapper: send encrypted data to each party in a list.
   dst maps each element to a destination party index.
   payload maps each element to the data to send. *)
Definition DSend_iter {T} (party : nat) (dst : T -> nat) (payload : T -> data)
    (elems : seq T) {n} {env : senv dsdp_dtype}
    (cont : @sproc dsdp_dtype data party n env)
    : @sproc dsdp_dtype data party (iter (size elems) S n)
        (fold_senv (fun f e => senv_send e (dst f) DT_Enc) elems env) :=
  sproc_iter party S
    (fun f e => senv_send e (dst f) DT_Enc)
    (fun f _ _ _ cont => SSend (dst f) DT_Enc (payload f) cont)
    elems 0 cont.

(* Iteration wrapper: receive encrypted data from each party in a list.
   src maps each element to a source party index.
   The received ciphertext is discarded (useful for accumulator patterns). *)
Definition DRecv_enc_iter {T} (party : nat) (src : T -> nat)
    (handler : T -> cipher AHE -> data)
    (elems : seq T) {n} {env : senv dsdp_dtype}
    (cont : @sproc dsdp_dtype data party n env)
    : @sproc dsdp_dtype data party (iter (size elems) (fun k => k.+2) n)
        (fold_senv (fun f e => senv_recv e (src f) DT_Enc) elems env) :=
  sproc_iter party (fun k => k.+2)
    (fun f e => senv_recv e (src f) DT_Enc)
    (fun f _ _ _ cont =>
      SRecv (src f) DT_Enc (fun d =>
        match @std_from_enc AHE d with
        | Some enc => SInit (handler f enc) cont
        | None => SFail
        end))
    elems 0 cont.

End smc_dsdp_session_types.

(* Arguments declarations for implicit parameters *)
Arguments DRecv_enc {AHE party n env}.
Arguments DRecv_dec {AHE party n env}.
Arguments DSend {AHE party n env}.
Arguments DInit {AHE party n env}.
Arguments DRet {AHE party}.
Arguments DFinish {AHE party}.
Arguments DSend_iter {AHE T} party dst payload elems {n env} cont.
Arguments DRecv_enc_iter {AHE T} party src handler elems {n env} cont.
