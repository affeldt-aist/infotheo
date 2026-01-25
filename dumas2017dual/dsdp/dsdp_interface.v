From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap.
Require Import smc_interpreter smc_session_types homomorphic_encryption.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* DSDP Data Interface                                                        *)
(*                                                                            *)
(* This file provides a unified interface for DSDP protocol data types,       *)
(* eliminating duplication across dsdp_program.v, dsdp_correctness.v,         *)
(* dsdp_program_alt_syntax.v, and dsdp_entropy_trace.v.                       *)
(*                                                                            *)
(* Components:                                                                *)
(*   Recv_dec_param  - Parameterized receive-and-decrypt operation            *)
(*   Recv_enc_param  - Parameterized receive-encrypted operation              *)
(*   DSDP_Interface  - Record bundling data type and operations               *)
(*   Standard_DSDP_Interface - Canonical sum-type implementation              *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope proc_scope.

(* ========================================================================== *)
(* Parameterized Recv operations - defined once, reused everywhere            *)
(* ========================================================================== *)

(* Recv_dec: receive encrypted value, decrypt with key, continue with decrypted value *)
Definition Recv_dec_param {msg enc pkey : Type}
  (D : pkey -> enc -> option msg)
  (data : Type) (from_enc : data -> option enc)
  {n} (frm : nat) (dk : pkey) (f : msg -> proc data n) : proc data n.+1 :=
  Recv frm (fun x => match from_enc x with
                     | Some v => match D dk v with
                                 | Some v' => f v'
                                 | None => Fail
                                 end
                     | None => Fail
                     end).

(* Recv_enc: receive encrypted value (cannot decrypt), do HE computation *)
Definition Recv_enc_param {enc : Type}
  (data : Type) (from_enc : data -> option enc)
  {n} (frm : nat) (f : enc -> proc data n) : proc data n.+1 :=
  Recv frm (fun x => match from_enc x with
                     | Some v => f v
                     | None => Fail
                     end).

(* ========================================================================== *)
(* Session Data Type Kind (outside section - no PHE dependency)               *)
(* ========================================================================== *)

(* Only encrypted values are communicated - single dtype suffices *)
Inductive dsdp_dtype : Type := DT_Enc.

(* Decidable equality for dsdp_dtype *)
Definition dsdp_dtype_eqb (d1 d2 : dsdp_dtype) : bool := true.

Lemma dsdp_dtype_eqP : Equality.axiom dsdp_dtype_eqb.
Proof.
move=> [] [].
constructor.
reflexivity.
Qed.

HB.instance Definition _ := hasDecEq.Build dsdp_dtype dsdp_dtype_eqP.

(* ========================================================================== *)
(* DSDP Interface Record                                                      *)
(* ========================================================================== *)

(** Parameterized record bundling all DSDP data operations.
    This eliminates the need to repeat data/d/e/k/from_enc/Recv_dec/Recv_enc
    definitions in every DSDP file. *)
Record DSDP_Interface (PHE : Party_AHE_scheme) := MkDSDP_Interface {
  (* The carrier data type *)
  di_data : Type ;
  
  (* Constructors: wrap msg/enc/pkey into data *)
  di_d : phe_msg PHE -> di_data ;
  di_e : phe_enc PHE -> di_data ;
  di_k : phe_pkey PHE -> di_data ;
  
  (* Extractor: get enc from data *)
  di_from_enc : di_data -> option (phe_enc PHE) ;
  
  (* Specialized Recv operations *)
  di_Recv_dec : forall {n : nat}, 
    nat -> phe_pkey PHE -> (phe_msg PHE -> proc di_data n) -> 
    proc di_data n.+1 ;
  di_Recv_enc : forall {n : nat},
    nat -> (phe_enc PHE -> proc di_data n) -> 
    proc di_data n.+1 ;
}.

Arguments di_data {PHE} _.
Arguments di_d {PHE} _ _.
Arguments di_e {PHE} _ _.
Arguments di_k {PHE} _ _.
Arguments di_from_enc {PHE} _ _.
Arguments di_Recv_dec {PHE} _ {n} _ _ _.
Arguments di_Recv_enc {PHE} _ {n} _ _.

(* ========================================================================== *)
(* Standard DSDP Interface using Sum Types                                    *)
(* ========================================================================== *)

Section Standard_DSDP_Interface.

Variable PHE : Party_AHE_scheme.

Let msg := phe_msg PHE.
Let enc := phe_enc PHE.
Let pkey := phe_pkey PHE.
Let D := @phe_D PHE.

(* Standard sum-type data encoding: (msg + enc + pkey) *)
Definition std_data := (msg + enc + pkey)%type.
Definition std_d (x : msg) : std_data := inl (inl x).
Definition std_e (x : enc) : std_data := inl (inr x).
Definition std_k (x : pkey) : std_data := inr x.

Definition std_from_enc (x : std_data) : option enc :=
  if x is inl (inr v) then Some v else None.

Definition std_Recv_dec {n} (frm : nat) (dk : pkey) 
    (f : msg -> proc std_data n) : proc std_data n.+1 :=
  @Recv_dec_param msg enc pkey D std_data std_from_enc n frm dk f.

Definition std_Recv_enc {n} (frm : nat) 
    (f : enc -> proc std_data n) : proc std_data n.+1 :=
  @Recv_enc_param enc std_data std_from_enc n frm f.

(** The canonical standard interface instance *)
Definition Standard_DSDP_Interface : DSDP_Interface PHE := {|
  di_data := std_data ;
  di_d := std_d ;
  di_e := std_e ;
  di_k := std_k ;
  di_from_enc := std_from_enc ;
  di_Recv_dec := @std_Recv_dec ;
  di_Recv_enc := @std_Recv_enc ;
|}.

End Standard_DSDP_Interface.

(* ========================================================================== *)
(* Correctness Lemmas for Standard Interface                                  *)
(* ========================================================================== *)

Section Standard_Interface_Properties.

Variable PHE : Party_AHE_scheme.
Let DI := Standard_DSDP_Interface PHE.

Lemma std_from_enc_e (x : phe_enc PHE) : 
  di_from_enc DI (di_e DI x) = Some x.
Proof. by []. Qed.

Lemma std_from_enc_d (x : phe_msg PHE) : 
  di_from_enc DI (di_d DI x) = None.
Proof. by []. Qed.

Lemma std_from_enc_k (x : phe_pkey PHE) : 
  di_from_enc DI (di_k DI x) = None.
Proof. by []. Qed.

End Standard_Interface_Properties.

(* ========================================================================== *)
(* Session-Typed Wrappers for DSDP                                            *)
(* ========================================================================== *)

(* Session-typed versions using sproc from smc_session_types.
   These coexist with the proc-based wrappers above. *)

Section Session_Typed_DSDP.

Variable PHE : Party_AHE_scheme.

Let data := std_data PHE.
Let D := @phe_D PHE.

(* Receive encrypted - pattern match data, use SFail on mismatch *)
Definition DRecv_enc {me n env} (src : nat)
    (f : phe_enc PHE -> @sproc dsdp_dtype data me n env)
    : @sproc dsdp_dtype data me n.+1 (senv_recv env src DT_Enc) :=
  SRecv src DT_Enc (fun d => 
    match @std_from_enc PHE d with
    | Some enc => f enc
    | None => SFail
    end).

(* Receive encrypted and decrypt - still tracks as DT_Enc (what's on the wire) *)
(* NOTE: D returns option msg, so need nested match for decrypt failure *)
Definition DRecv_dec {me n env} (src : nat) (dk : phe_pkey PHE)
    (f : phe_msg PHE -> @sproc dsdp_dtype data me n env)
    : @sproc dsdp_dtype data me n.+1 (senv_recv env src DT_Enc) :=
  SRecv src DT_Enc (fun d => 
    match @std_from_enc PHE d with
    | Some enc => match D dk enc with
                  | Some msg => f msg
                  | None => SFail  (* decrypt failure *)
                  end
    | None => SFail  (* not an encrypted value *)
    end).

(* Send encrypted - the only send variant needed *)
Definition DPSendEnc {me n env} (party : nat) (x : phe_enc PHE)
    (p : @sproc dsdp_dtype data me n env)
    : @sproc dsdp_dtype data me n.+1 (senv_send env party DT_Enc) :=
  SSend party DT_Enc (@std_e PHE x) p.

(* Init/Ret wrappers - can init any data kind (msg, enc, key) *)
(* Init doesn't affect session env since it's local storage *)
Definition DPInit {me n env} (x : data) (p : @sproc dsdp_dtype data me n env)
    : @sproc dsdp_dtype data me n.+1 env := 
  SInit x p.

Definition DPRet {me : nat} (x : data) : @sproc dsdp_dtype data me 2 senv_end := 
  SRet x.

End Session_Typed_DSDP.

(* Arguments declarations for implicit parameters *)
Arguments DRecv_enc {PHE me n env}.
Arguments DRecv_dec {PHE me n env}.
Arguments DPSendEnc {PHE me n env}.
Arguments DPInit {PHE me n env}.
Arguments DPRet {PHE me}.

(* ========================================================================== *)
(* Notation shortcuts for use in client files                                 *)
(* ========================================================================== *)

(* These can be used with: Let data := di_data DI. etc. *)
Notation "'data_of' DI" := (di_data DI) (at level 10, only parsing).
Notation "'d_of' DI" := (di_d DI) (at level 10, only parsing).
Notation "'e_of' DI" := (di_e DI) (at level 10, only parsing).
Notation "'k_of' DI" := (di_k DI) (at level 10, only parsing).
