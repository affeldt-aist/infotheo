From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap matrix lra.
Require Import rouche_capelli.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter smc_tactics.
Require Import smc_proba homomorphic_encryption.
Require Import dsdp_program dsdp_extra dsdp_algebra dsdp_entropy.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* Formalization of:                                                          *)
(*                                                                            *)
(* Dumas, J. G., Lafourcade, P., Orfila, J. B., & Puys, M. (2017).            *)
(* Dual protocols for private multi-party matrix multiplication               *)
(* and trust computations.                                                    *)
(* Computers & security, 71, 51-70.                                           *)
(*                                                                            *)
(******************************************************************************)

(******************************************************************************)
(* Security Analysis: Connecting Algebraic and Information-Theoretic Views   *)
(*                                                                            *)
(* This file bridges two perspectives on DSDP protocol security:              *)
(*                                                                            *)
(* 1. ALGEBRAIC (dsdp_algebra.v):                                             *)
(*    - Linear constraint: s = u1*v1 + u2*v2 + u3*v3                          *)
(*    - Solution pairs form affine subspace of size m                         *)
(*    - Matrix rank and kernel dimension determine degrees of freedom         *)
(*                                                                            *)
(* 2. INFORMATION-THEORETIC (dsdp_entropy.v):                                 *)
(*    - Conditional entropy: H(V2,V3 | V1,U1,U2,U3,S) = log(m)                *)
(*    - Uniform distribution over solution pairs maximizes entropy            *)
(*    - Independence properties ensure no information leakage                 *)
(*                                                                            *)
(* KEY INSIGHT: Algebraic structure determines information-theoretic bounds.  *)
(* The constraint reduces joint space from m² to m solution pairs, giving     *)
(* exactly log(m) bits of entropy. Uniform distribution over this affine      *)
(* subspace provides maximum uncertainty for adversary.                       *)
(*                                                                            *)
(* FIELD APPROXIMATION: Uses finFieldType (prime field 'F_m) to model         *)
(* Benaloh's Z/(p*q). For cryptographic p,q ≥ 2^1024, statistical distance   *)
(* < 2^-1000 (negligible). Enables field-based linear algebra while           *)
(* preserving security for ring-based implementation. See notes/ for details. *)
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

Local Definition R := Rdefinitions.R.

Section dsdp_security.

Variable F : finFieldType.
Variable T : finType.
Variable P : R.-fdist T.

Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Hypothesis prime_m : prime m.

Local Notation msg := 'F_m.  (* Consistent with all other DSDP files *)
Let card_msg : #|msg| = m.
Proof. by rewrite card_Fp // pdiv_id. Qed.

Variable inputs : dsdp_entropy.dsdp_random_inputs P prime_m.

Let Dk_a := dsdp_entropy.Dk_a inputs.
Let Dk_b := dsdp_entropy.Dk_b inputs.
Let Dk_c := dsdp_entropy.Dk_c inputs.
Let V1 := dsdp_entropy.V1 inputs.
Let V2 := dsdp_entropy.V2 inputs.
Let V3 := dsdp_entropy.V3 inputs.
Let U1 := dsdp_entropy.U1 inputs.
Let U2 := dsdp_entropy.U2 inputs.
Let U3 := dsdp_entropy.U3 inputs.
Let R2 := dsdp_entropy.R2 inputs.
Let R3 := dsdp_entropy.R3 inputs.

Let VU2 : {RV P -> msg} := V2 \* U2.
Let VU3 : {RV P -> msg} := V3 \* U3.
Let D2  : {RV P -> msg} := VU2 \+ R2.
Let VU3R : {RV P -> msg} := VU3 \+ R3.
Let D3 : {RV P -> msg} := VU3R \+ D2.
Let S : {RV P -> msg} := D3 \- R2 \- R3 \+ U1 \* V1.

(* Encryption operations *)
Let E_alice_d3 := E' alice `o D3.
Let E_charlie_v3 := E' charlie `o V3.
Let E_bob_v2 := E' bob `o V2.

(* Alice's view of the protocol *)
Let alice_inputsT := (Alice.-key Dec msg * msg * msg * msg * msg * msg * msg)%type.
Let AliceInputsView := [% Dk_a, V1, U1, U2, U3, R2, R3].
Let alice_view_valuesT := 
  (Alice.-key Dec msg * msg * msg * msg * msg * msg * msg * msg * 
   Alice.-enc msg * Charlie.-enc msg * Bob.-enc msg)%type.
Let AliceView : {RV P -> alice_view_valuesT} :=
  [% Dk_a, S, V1, U1, U2, U3, R2, R3, E_alice_d3, E_charlie_v3, E_bob_v2].

(* Protocol assumptions needed for security *)

Let CondRV : {RV P -> (msg * msg * msg * msg * msg)} :=
  [% V1, U1, U2, U3, S].
Let VarRV : {RV P -> (msg * msg)} := [%V2, V3].

Hypothesis constraint_holds :
  forall t, satisfies_constraint (CondRV t) (VarRV t).

Hypothesis U3_nonzero : forall t, U3 t != 0.

Hypothesis uniform_over_solutions : forall t v1 u1 u2 u3 s,
  U1 t = u1 -> U2 t = u2 -> U3 t = u3 ->
  V1 t = v1 -> S t = s ->
  forall v2 v3,
    (v2, v3) \in dsdp_fiber u1 u2 u3 v1 s ->
    `Pr[ [% V2, V3] = (v2, v3) | [% V1, U1, U2, U3, S] = 
         (v1, u1, u2, u3, s) ] =
    #|dsdp_fiber u1 u2 u3 v1 s|%:R^-1.

(* Additional hypotheses for privacy_by_bonded_leakage *)
Let Dec_view : {RV P -> (alice_inputsT * msg)} :=
  [% Dk_a, S, V1, U1, U2, U3, R2, R3].

Hypothesis Pr_AliceView_neq0 :
  forall
    (x : alice_inputsT * msg * Alice.-enc msg * Charlie.-enc msg)
    (e : Bob.-enc msg),
  `Pr[ [% Dec_view, E_alice_d3, E_charlie_v3, E_bob_v2] = (x, e) ] != 0.

Hypothesis Pr_Eqn1View_neq0 :
  forall
    (x : alice_inputsT * msg * Alice.-enc msg)
    (e : Charlie.-enc msg),
  `Pr[ [% Dec_view, E_alice_d3, E_charlie_v3] = (x, e) ] != 0.

Hypothesis Pr_Eqn2View_neq0 :
  forall
    (x : (alice_inputsT * msg))
    (e : Alice.-enc msg),
  `Pr[ [% Dec_view, E_alice_d3] = (x, e) ] != 0.

Hypothesis cinde_V2V3 :
  P |= [% Dk_a, R2, R3] _|_ [% V2, V3] | [% V1, U1, U2, U3, S].

Hypothesis cinde_V2 :
  P |= [% Dk_a, R2, R3] _|_ V2 | [% V1, U1, U2, U3, S, V2].

(* V3 is determined by other variables via the linear constraint *)
Definition compute_v3 : msg * msg * msg * msg * msg * msg -> msg :=
  fun '(v1, u1, u2, u3, s, v2) => 
    if u3 == 0 then 0 else (s - u1 * v1 - u2 * v2) / u3.

Hypothesis V3_determined : 
  V3 = compute_v3 `o [% V1, U1, U2, U3, S, V2].

(** ** Intermediate Entropy Results *)

Theorem dsdp_entropy_result :
  `H(VarRV | CondRV) = log (m%:R : R).
Proof.
exact (@dsdp_centropy_uniform_solutions m_minus_2 prime_m T P 
         V1 V2 V3 U1 U2 U3 S 
         constraint_holds U3_nonzero uniform_over_solutions).
Qed.

(* Bridge lemma: AliceView conditioning equals base conditioning for [V2,V3] *)
Lemma AliceView_entropy_connection :
  `H([% V2, V3] | AliceView) = `H([% V2, V3] | [% V1, U1, U2, U3, S]).
Proof.
(* AliceView = [Dk_a, S, V1, U1, U2, U3, R2, R3, E_alice_d3, E_charlie_v3, E_bob_v2]
   The additional information [Dk_a, R2, R3, encryptions] is conditionally 
   independent of [V2,V3] given [V1,U1,U2,U3,S], so it doesn't affect the entropy *)
admit. (* TODO: Apply E_enc_ce_removal and conditional independence *)
Admitted.

(** ** Main Security Theorem *)

Theorem dsdp_security_bounded_leakage :
  `H(V2 | AliceView) = log (m%:R : R) /\
  `H(V2 | AliceView) > 0.
Proof.
split.
- (* Equality: H(V2 | AliceView) = log(m) *)
  (* Step 1: Use privacy_by_bonded_leakage to reduce joint to single variable *)
  
  (* Step 2: Connect AliceView conditioning to base conditioning *)
  (*rewrite AliceView_entropy_connection.*)
  
  (* Step 3: Apply the main entropy result *)
  (*exact: dsdp_entropy_result.*)
Admitted.

(** ** Interpretation *)

(* The adversary learns log(m) bits about v2, not 0 bits (perfect secrecy)
   but also not log(m^2) bits (complete knowledge).
   
   This is because:
   - There are m possible values for v2
   - Each is equally likely given alice_view
   - Entropy = log(m) bits
   
   Security holds despite information leakage.
*)

End dsdp_security.


