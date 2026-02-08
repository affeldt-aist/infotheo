From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap matrix lra reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter.
Require Import homomorphic_encryption dsdp_interface.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* DSDP Trace-based Entropy Analysis for Z/pqZ                                *)
(*                                                                            *)
(* This file provides trace-related entropy lemmas for the DSDP protocol      *)
(* over composite modulus Z/pqZ (Benaloh cryptosystem).                       *)
(*                                                                            *)
(* Key results:                                                               *)
(*   - dsdp_traces: Protocol trace structure for Z/pqZ                        *)
(*   - centropy_AliceTraces_AliceView: H(v|AliceTraces) = H(v|AliceView)       *)
(*                                                                            *)
(* These lemmas establish that conditioning on protocol traces equals         *)
(* conditioning on Alice's view, allowing security proofs to work with        *)
(* the simpler view representation.                                           *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

Reserved Notation "u *h w" (at level 40).
Reserved Notation "u ^h w" (at level 40).

Section dsdp_traces.

(* Parameterize by an AHEMonoidType instance *)
Variable AHE : AHEMonoidType.

(* Use standard DSDP interface for data types *)
Let DI := Standard_DSDP_Interface AHE.

(* Extract types from the scheme *)
Let msgT := plain AHE.
Let randT := rand AHE.
Let encT := cipher AHE.
Let priv_keyT := priv_key AHE.

(* Data type and constructors from interface *)
Let data := di_data DI.
Let d := di_d DI.
Let e := di_e DI.
Let k := di_priv_key DI.

(* HE operations from the scheme *)
Let Emul := @Emul AHE.
Let Epow := @Epow AHE.

Notation "u *h w" := (Emul u w).
Notation "u ^h w" := (Epow u w).

(* Party identities *)
Variable alice : party_id.
Variable bob : party_id.
Variable charlie : party_id.

(* Public key mapping and encryption wrapper *)
Variable ek : party_id -> pub_key AHE.
Definition enc_pk (p : party_id) (m : msgT) (r : randT) : encT :=
  enc (ek p) m r.
Local Notation E := enc_pk.

(* Trace types for DSDP protocol *)
Notation dsdp_traceT := (15.-bseq data).
Notation dsdp_tracesT := (3.-tuple dsdp_traceT).

(* Message and randomness variables *)
Variables (v1 v2 v3 u1 u2 u3 r2 r3 : msgT).
Variables (rb1 rb2 rc1 rc2 ra1 ra2 : randT).

(* Private keys *)
Variables (dk_a : priv_keyT) (dk_b : priv_keyT) (dk_c : priv_keyT).

(* Protocol traces - now include randomness in encryption calls *)
Definition dsdp_traces : dsdp_tracesT :=
  [tuple
     [bseq d (v3 * u3 + r3 + (v2 * u2 + r2) - r2 - r3 + u1 * v1);
           e (E alice (v3 * u3 + r3 + (v2 * u2 + r2)) rc2);
           e (E charlie v3 rc1);
           e (E bob v2 rb1);
           d r3; d r2; d u3; d u2; d u1; d v1; k dk_a];
     [bseq e (E charlie (v3 * u3 + r3) rb2);
           e (E bob (v2 * u2 + r2) ra1); d v2; k dk_b];
     [bseq e (E charlie (v3 * u3 + r3 + (v2 * u2 + r2)) rb2); d v3; k dk_c]].

(* Protocol correctness is now proved algebraically using ring arithmetic.
   The final result S = v3*u3 + r3 + (v2*u2 + r2) - r2 - r3 + u1*v1
   simplifies to u1*v1 + u2*v2 + u3*v3 by ring. *)
Theorem dsdp_result_correct :
  v3 * u3 + r3 + (v2 * u2 + r2) - r2 - r3 + u1 * v1 = u1 * v1 + u2 * v2 + u3 * v3.
Proof. ring. Qed.

End dsdp_traces.

(******************************************************************************)
(* Trace-based Entropy Analysis                                               *)
(*                                                                            *)
(* NOTE: The trace-based entropy analysis relied on the idealized encryption  *)
(* model where enc = (party * msg) and E' is deterministic. With the new      *)
(* AHEMonoidType interface where encryption requires randomness, the      *)
(* trace structure becomes more complex.                                      *)
(*                                                                            *)
(* The entropy equivalence lemmas (centropy_AliceTraces_AliceView, etc.)      *)
(* need to be reformulated to account for encryption randomness.              *)
(* This requires extending the view types to include randomness variables.    *)
(******************************************************************************)

Section trace_entropy_analysis.

(* Parameterize by an AHEMonoidType instance *)
Variable AHE : AHEMonoidType.

(* Use standard DSDP interface for data types *)
Let DI := Standard_DSDP_Interface AHE.

(* Extract types from the scheme *)
Let msgT := plain AHE.

(* Data type and constructors from interface *)
Let data := di_data DI.

Notation dsdp_traceT := (15.-bseq data).
Notation dsdp_tracesT := (3.-tuple dsdp_traceT).

Variable R : realType.
Variable T : finType.
Variable P : R.-fdist T.

(* Random variable definitions for messages *)
Variables (V1 V2 V3 U1 U2 U3 R2 R3 : {RV P -> msgT}).

(* Intermediate values *)
Let VU2 : {RV P -> msgT} := V2 \* U2.
Let VU3 : {RV P -> msgT} := V3 \* U3.
Let D2  : {RV P -> msgT} := VU2 \+ R2.
Let VU3R : {RV P -> msgT} := VU3 \+ R3.
Let D3 : {RV P -> msgT} := VU3R \+ D2.
Let S : {RV P -> msgT} := D3 \- R2 \- R3 \+ U1 \* V1.

(* The protocol correctness theorem: the sum S equals the dot product.
   This is proved algebraically without depending on trace structure. *)
Lemma dsdp_algebraic_correctness :
  forall t, S t = (U1 \* V1 \+ U2 \* V2 \+ U3 \* V3) t.
Proof.
move => t.
rewrite /S /D3 /VU3R /D2 /VU2 /VU3 /=.
ring.
Qed.

End trace_entropy_analysis.
