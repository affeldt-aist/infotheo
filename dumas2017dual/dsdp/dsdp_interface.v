From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap.
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
(*   Recv_param      - Single parametric receive combinator                   *)
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
(* Parameterized Recv combinator - instantiated in two ways:                  *)
(*   1. Recv-and-decrypt: extract ciphertext, decrypt, continue with plaintext*)
(*   2. Recv-for-HE: extract ciphertext, continue with it for HE computation  *)
(* ========================================================================== *)

Section Recv_param.

Variable (T : Type).
Variable (data : Type).
Variable (extract : data -> option T).

(* Recv_param: receive data, extract value of type T, continue with it *)
Definition Recv_param (frm : nat) (f : T -> proc data) : proc data :=
  Recv frm (oapp f Fail \o extract).

End Recv_param.

Arguments Recv_param {T} data extract frm f.

(* ========================================================================== *)
(* Session Data Type Kind (outside section - no AHE dependency)               *)
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
Record DSDP_Interface (AHE : AHEAlgebra_scheme) := MkDSDP_Interface {
  (* The carrier data type *)
  di_data : Type ;
  
  (* Constructors: wrap msg/enc/pkey into data *)
  di_d : plain AHE -> di_data ;
  di_e : party_cipher AHE -> di_data ;
  di_k : pkey AHE -> di_data ;
  
  (* Extractor: get enc from data *)
  di_from_enc : di_data -> option (party_cipher AHE) ;
  
  (* Specialized Recv operations (proc is now unindexed) *)
  di_Recv_dec : 
    nat -> pkey AHE -> (plain AHE -> proc di_data) -> 
    proc di_data ;
  di_Recv_enc :
    nat -> (party_cipher AHE -> proc di_data) -> 
    proc di_data ;
}.

Arguments di_data {AHE} _.
Arguments di_d {AHE} _ _.
Arguments di_e {AHE} _ _.
Arguments di_k {AHE} _ _.
Arguments di_from_enc {AHE} _ _.
Arguments di_Recv_dec {AHE} _ _ _ _.
Arguments di_Recv_enc {AHE} _ _ _.

(* ========================================================================== *)
(* Standard DSDP Interface using Sum Types                                    *)
(* ========================================================================== *)

Section Standard_DSDP_Interface.

Variable AHE : AHEAlgebra_scheme.

Let msgT := plain AHE.
Let encT := party_cipher AHE.
Let pkeyT := pkey AHE.
Let D := @dec AHE.

(* Standard sum-type data encoding: (msgT + encT + pkeyT) *)
Definition std_data := (msgT + encT + pkeyT)%type.
Definition std_d (x : msgT) : std_data := inl (inl x).
Definition std_e (x : encT) : std_data := inl (inr x).
Definition std_k (x : pkeyT) : std_data := inr x.

Definition std_from_enc (x : std_data) : option encT :=
  if x is inl (inr v) then Some v else None.

(* Recv-and-decrypt: extract ciphertext, decrypt, continue with plaintext *)
Definition std_Recv_dec (frm : nat) (dk : pkeyT) 
    (f : msgT -> proc std_data) : proc std_data :=
  Recv_param std_data (obind (D dk) \o std_from_enc) frm f.

(* Recv-for-HE: extract ciphertext, continue with it for HE computation *)
Definition std_Recv_enc (frm : nat) 
    (f : encT -> proc std_data) : proc std_data :=
  Recv_param std_data std_from_enc frm f.

(** The canonical standard interface instance *)
Definition Standard_DSDP_Interface : DSDP_Interface AHE := {|
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

Variable AHE : AHEAlgebra_scheme.
Let DI := Standard_DSDP_Interface AHE.

Lemma std_from_enc_e (x : party_cipher AHE) : 
  di_from_enc DI (di_e DI x) = Some x.
Proof. by []. Qed.

Lemma std_from_enc_d (x : plain AHE) : 
  di_from_enc DI (di_d DI x) = None.
Proof. by []. Qed.

Lemma std_from_enc_k (x : pkey AHE) : 
  di_from_enc DI (di_k DI x) = None.
Proof. by []. Qed.

End Standard_Interface_Properties.


(* ========================================================================== *)
(* Notation shortcuts for use in client files                                 *)
(* ========================================================================== *)

(* These can be used with: Let data := di_data DI. etc. *)
Notation "'data_of' DI" := (di_data DI) (at level 10, only parsing).
Notation "'d_of' DI" := (di_d DI) (at level 10, only parsing).
Notation "'e_of' DI" := (di_e DI) (at level 10, only parsing).
Notation "'k_of' DI" := (di_k DI) (at level 10, only parsing).
