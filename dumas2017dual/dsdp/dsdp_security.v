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
(*    - Solution pairs form affine subspace of size m = p*q                   *)
(*    - Matrix rank and kernel dimension determine degrees of freedom         *)
(*                                                                            *)
(* 2. INFORMATION-THEORETIC (dsdp_entropy.v):                                 *)
(*    - Conditional entropy: H(V2,V3 | V1,U1,U2,U3,S) = log(m)                *)
(*    - Uniform distribution over solution pairs maximizes entropy            *)
(*    - Independence properties ensure no information leakage                 *)
(*                                                                            *)
(* KEY INSIGHT: Algebraic structure determines information-theoretic bounds.  *)
(* The constraint reduces joint space from m^2 to m solution pairs, giving    *)
(* exactly log(m) bits of entropy. Uniform distribution over this affine      *)
(* subspace provides maximum uncertainty for adversary.                       *)
(*                                                                            *)
(* Z/pqZ APPROACH: Uses composite modulus m = p*q directly via CRT. The       *)
(* fiber cardinality |{(v2,v3) : u2*v2 + u3*v3 = target}| = m is proven       *)
(* in fiber_zpq.v using CRT decomposition. Security condition 0 < U3 < min(p,q)*)
(* ensures U3 is coprime to m, hence invertible. See notes/ for details.      *)
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

Variable T : finType.
Variable P : R.-fdist T.

(* Z/pqZ parameters - composite modulus for Benaloh cryptosystem *)
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Hypothesis prime_p : prime p.
Hypothesis prime_q : prime q.
Hypothesis coprime_pq : coprime p q.
Local Notation m := (p * q).

(* Z/pqZ ring structure for composite modulus arithmetic *)
Local Notation msg := 'Z_m.

(* m = p * q > 1 since p, q >= 2 *)
Let m_gt1 : (1 < m)%N.
Proof.
have Hp2: (1 < p)%N by [].
have Hq2: (1 < q)%N by [].
by rewrite (ltn_trans Hp2) // -{1}(muln1 p) ltn_pmul2l // ltnS.
Qed.

Let card_msg : #|msg| = m.
Proof. by rewrite card_ord Zp_cast. Qed.

(* Use dsdp_random_inputs record to enable reuse of alice_view_to_cond *)
Variable inputs : dsdp_random_inputs P p_minus_2 q_minus_2.

(* Extract random variables from the record *)
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

(* Use Z/pqZ definitions from dsdp_entropy for constraint and fiber *)
Hypothesis constraint_holds :
  forall t, satisfies_constraint_zpq (CondRV t) (VarRV t).

(* U3 must be coprime to m for invertibility in Z/pqZ *)
Hypothesis U3_coprime_m : forall t, coprime (val (U3 t)) m.

Hypothesis uniform_over_solutions : forall t v1 u1 u2 u3 s,
  U1 t = u1 -> U2 t = u2 -> U3 t = u3 ->
  V1 t = v1 -> S t = s ->
  forall v2 v3,
    (v2, v3) \in dsdp_fiber_full_zpq u1 u2 u3 v1 s ->
    `Pr[ [% V2, V3] = (v2, v3) | [% V1, U1, U2, U3, S] = 
         (v1, u1, u2, u3, s) ] =
    #|dsdp_fiber_full_zpq u1 u2 u3 v1 s|%:R^-1.

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

(* Additional hypotheses for Z/pqZ entropy theorem:
   U3 must be positive and less than min(p,q) to ensure invertibility *)
Hypothesis U3_pos : forall t, (0 < val (U3 t))%N.
Hypothesis U3_lt_minpq : forall t, (val (U3 t) < minn p q)%N.

(* Core entropy bound: H((V2,V3) | constraint view) = log(m).
   Instantiates the general DSDP entropy analysis with security hypotheses.
   Shows Alice learns exactly log(m) bits about Bob/Charlie's joint input,
   not the full log(m^2) bits - proving bounded information leakage.
*)
Theorem dsdp_constraint_centropy_eqlogm :
  `H(VarRV | CondRV) = log (m%:R : R).
Proof.
(* Goal: `H(VarRV | CondRV) = log (m%:R : R)
   where VarRV = [% V2, V3], CondRV = [% V1, U1, U2, U3, S] *)
(* Apply dsdp_centropy_uniform_zpq from dsdp_entropy.v with all section params *)
apply: dsdp_centropy_uniform_zpq.
(* === 6 subgoals from section parameters === *)
- exact: prime_p.
- exact: prime_q.
- exact: constraint_holds.
- exact: uniform_over_solutions.
- exact: U3_pos.
- exact: U3_lt_minpq.
Qed.

(* V3 is determined by V2 and CondRV, so joint entropy equals single.
   Uses chain rule and the fact that V3 = compute_v3(CondRV, V2).
   Follows exact pattern from dsdp_entropy.v V3_determined_centropy_v2. *)
Lemma V3_determined_centropy_v2_local :
  `H([% V2, V3] | CondRV) = `H(V2 | CondRV).
Proof.
rewrite /CondRV.
have ->: `H([% V2, V3] | [% V1, U1, U2, U3, S]) =
  `H([% V1, U1, U2, U3, S], [% V2, V3]) - `H `p_ [% V1, U1, U2, U3, S].
  by rewrite chain_rule_RV addrAC subrr add0r.
rewrite V3_determined.
have ->: `H([% V1, U1, U2, U3, S],
    [% V2, compute_v3 `o [% V1, U1, U2, U3, S, V2]]) =
  `H `p_[% V1, U1, U2, U3, S, V2].
  by rewrite joint_entropy_RVA joint_entropy_RV_comp.
have ->: `H(V2 | [% V1, U1, U2, U3, S]) =
  `H([% V1, U1, U2, U3, S], V2) - `H `p_ [% V1, U1, U2, U3, S].
  by rewrite chain_rule_RV addrAC subrr add0r.
by [].
Qed.

(* DSDP security guarantee: H(V2 | AliceView) = log(m) > 0.
   Alice cannot learn Bob's private input V2 with certainty.
   The conditional entropy log(m) means V2 remains uniformly distributed
   over m values from Alice's perspective - she gains no advantage over
   random guessing. The protocol leaks V3's determination but not V2. *)
Theorem dsdp_security_bounded_leakage :
  `H(V2 | AliceView) = log (m%:R : R) /\
  `H(V2 | AliceView) > 0.
Proof.
(* Proof chain: H(V2|AliceView) = H(V2|CondRV) = H([V2,V3]|CondRV) = log(m) *)
have H_v2_logm: `H(V2 | AliceView) = log (m%:R : R).
  (* Use alice_view_to_cond from dsdp_entropy.v with the record *)
  rewrite (alice_view_to_cond Pr_AliceView_neq0 Pr_Eqn1View_neq0 Pr_Eqn2View_neq0
             (decomposition cinde_V2V3)).
  rewrite -V3_determined_centropy_v2_local.
  exact: dsdp_constraint_centropy_eqlogm.
split.
- (* Goal 1: H(V2 | AliceView) = log(m) *)
  exact: H_v2_logm.
- (* Goal 2: H(V2 | AliceView) > 0 *)
  rewrite H_v2_logm.
  (* Goal: log(m) > 0, where m = p * q > 1 *)
  rewrite -log1.
  apply: ltr_log.
    by [].  (* 0 < 1 *)
  (* Goal: 1 < m%:R, use ltr1n: (1 < n%:R) = (1 < n)%N *)
  rewrite ltr1n.
  exact: m_gt1.
Qed.

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


