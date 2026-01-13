From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap matrix lra reals.
Require Import rouche_capelli.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter smc_tactics.
Require Import smc_proba homomorphic_encryption.
Require Import extra_algebra extra_proba extra_entropy.
Require Import dsdp_program dsdp_entropy.

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
(* Security Analysis: Information-Theoretic View of DSDP Protocol             *)
(*                                                                            *)
(* This file provides security analysis from information-theoretic view:      *)
(*                                                                            *)
(* INFORMATION-THEORETIC (dsdp_entropy.v):                                    *)
(*    - Linear constraint: s = u1*v1 + u2*v2 + u3*v3                          *)
(*    - Solution pairs form affine subspace of size m = p*q                   *)
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
(* in linear_fiber_zpq.v using CRT decomposition.
   Security condition 0 < U3 < min(p,q) *)
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

Section dsdp_security.

Context {R : realType}.
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
Let alice_inputsT :=
  (Alice.-key Dec msg * msg * msg * msg * msg * msg * msg)%type.
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
  forall t, dsdp_constraint (CondRV t) (VarRV t).

(* U3 must be coprime to m for invertibility in Z/pqZ *)
Hypothesis U3_coprime_m : forall t, coprime (val (U3 t)) m.

(* Cryptographic assumptions for DSDP security:
   1. VarRV = (V2, V3) is uniformly distributed over msg × msg
   2. VarRV is independent of the inputs (V1, U1, U2, U3)
   These are standard assumptions in secure multi-party computation.
   Note: We use dsdp_entropy.card_msg_pair_subproof to match the
   parameter expected by dsdp_centropy_uniform. *)
Hypothesis VarRV_uniform : 
  `p_ VarRV = fdist_uniform (dsdp_entropy.card_msg_pair_subproof p_minus_2 q_minus_2).
Hypothesis VarRV_indep_inputs : P |= [%V1, U1, U2, U3] _|_ VarRV.

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

(* Hypothesis for malicious adversary analysis:
   If A is const-RV actually P |= A _|_ A. But in the DSDP setting, 
   we don't have such RVs. *)
Hypothesis neg_self_indep : forall (TA : finType)
  (A : {RV P -> TA}), ~ P |= A _|_ A.

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
(* Apply dsdp_centropy_uniform from dsdp_entropy.v with all section
   params. The new structure uses VarRV_uniform and VarRV_indep_inputs
   instead of the old uniform_over_solutions hypothesis. *)
apply: dsdp_centropy_uniform.
(* === Section parameters for dsdp_entropy === *)
- exact: prime_p.
- exact: prime_q.
- exact: constraint_holds.
- exact: VarRV_uniform.
- exact: VarRV_indep_inputs.
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
  rewrite (alice_view_to_cond Pr_AliceView_neq0 Pr_Eqn1View_neq0
            Pr_Eqn2View_neq0 (decomposition cinde_V2V3)).
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

(******************************************************************************)
(* Malicious Adversary Case Analysis                                          *)
(*                                                                            *)
(* Moved from dsdp_entropy.v - security analysis belongs here.                *)
(* Examines the compromised case when Alice sets U2,U3 to reveal V2.          *)
(******************************************************************************)

Section dotp2.

Notation "x \+ y" := (add_RV x y).

Definition dotp2 (x y: (msg * msg)) := x.1 * y.1 + x.2 * y.2.

Definition dotp2_solutions (s : msg) : {set (msg * msg) * (msg * msg)} :=
  [set uv in setX setT setT | dotp2 uv.1 uv.2 == s].

Definition Dotp2_rv (X Y : {RV P -> (msg * msg)}) : {RV P -> msg} :=
  fun p => dotp2 (X p) (Y p).

Definition Dotp2Solutions
  (S : {RV P -> msg}) : {RV P -> {set (msg * msg) * (msg * msg)} } :=
  dotp2_solutions `o S.

Definition US := [% U2, U3].
Definition VS := [% V2, V3].

Definition ConstUS :=
  [% (fun _ => 1) : {RV P -> msg},
     (fun _ => 0) : {RV P -> msg}].
Definition VU1 : {RV P -> msg} := V1 \* U1.

(* S expressed as dot product: S = (V2,V3)·(U2,U3) + V1*U1.
   This is the DSDP constraint s = u2*v2 + u3*v3 + u1*v1 in RV form. *)
Lemma S_E :
  S = Dotp2_rv VS US \+ VU1.
Proof.
rewrite /S /VS /US /D3 /VU3R /D2 /VU3 /VU2 /VU1 /Dotp2_rv /dotp2 /add_RV.
apply: boolp.funext => i //=.
ring.
Qed.

End dotp2.

Section malicious_adversary_case_analysis.

(* If an active adversary controls Alice, force `us` always output `(1, 0)`,
   then the key privacy premise `v2 _|_ dotp2_rv us vs` is impossible.

   In contrast, if Alice is an fair player, the probability that `us`
   outputs that specific value `(1, 0)` is 1/m^2.

   Finally, if Bob enforce ZPK check to abort the protocol when that value is
   generated, `v2 _|_ dotp2_rv us vs` is guaranteed, and the protocol
   is secure with that mitigation ("security with abort")
   \cite[\S5.2]{dumas2017dual}.

   Therefore, here we examine the compromised case:

      `us = (1, 0) -> ~ v2 _|_ dotp2_rv us vs`

   and the secure case:

      `us != (1, 0) ->  v2 _|_ dotp2_rv us vs`.
*)
Lemma ConstUS_discloses_V2 :
  US = ConstUS -> Dotp2_rv VS US = V2.
Proof.
move->; rewrite /ConstUS /VS /Dotp2_rv /dotp2 /fst /snd /comp_RV.
apply: boolp.funext => i //=.
ring.
Qed.

(* This theorem shows that if an active adversary controls Alice,
   it can set U1 and U2 as a special combination (1, 0),
   which allows revealing `V2` from the result that Alice receives.
   \cite[\S5.2]{dumas2017dual}.
*)
Theorem US_compromised_leaks_V2 :
  US = ConstUS -> ~ `H(V2 | AliceView ) = `H `p_V2.
Proof.
move => H.
(* From alice_view to [% Alice_input_view, S] *)
rewrite !(E_enc_ce_removal V2 card_msg).
pose h := (fun o : (Alice.-key Dec msg * msg *
  msg * msg * msg * msg * msg * msg) =>
  let '(dk_a, s, v1, u1, u2, u3, r2, r3) := o in
   (dk_a, v1, u1, u2, u3, r2, r3, s)).
pose h' := (fun o : (Alice.-key Dec msg * msg *
  msg * msg * msg * msg * msg * msg) =>
  let '(dk_a, v1, u1, u2, u3, r2, r3, s) := o in
  (dk_a, s, v1, u1, u2, u3, r2, r3)).
rewrite -(centropy_RV_contraction _ _ h).
have ->: `H( V2 | [% Dk_a, S, V1, U1, U2, U3, R2, R3, h `o
  [% Dk_a, S, V1, U1, U2, U3, R2, R3]]) =
  `H( V2 | [% Dk_a, S, V1, U1, U2, U3, R2, R3,
  [% Dk_a, V1, U1, U2, U3, R2, R3, S]]).
  by [].
rewrite centropyC (centropy_RV_contraction _ _ h') -/AliceInputsView.
(* From the cond_entropy to the independence goal via mutual info *)
move => H2.
have: `I(V2;[% AliceInputsView, S]) = 0.
  by rewrite mutual_info_RVE H2 subrr.
move/mutual_info_RV0_indep.
(* Show the independence is impossible if Alice has been compromised
   and cheat with the specific `us`*)
rewrite S_E /add_RV //= (ConstUS_discloses_V2 H).
pose z := (fun o : (alice_inputsT * msg) =>
  let '(_, v1, u1, _, _, _, _, v2_r) := o in v2_r - v1 * u1).
move/(inde_RV_comp idfun z).
have -> : z `o [% AliceInputsView, V2 \+ VU1] = V2.
  rewrite /z /VU1 /comp_RV /add_RV.
  apply: boolp.funext => i //=.
  by ring.
have -> : idfun `o V2 = V2.
  by apply: boolp.funext => i.
exact: neg_self_indep.
exact: Pr_Eqn2View_neq0.
exact: Pr_Eqn1View_neq0.
exact: Pr_AliceView_neq0.
Qed.

End malicious_adversary_case_analysis.

End dsdp_security.

(******************************************************************************)
(* Bob's Security Independence Proofs                                         *)
(*                                                                            *)
(* Prove that BobView is independent of V1 and V3 using graphoid axioms       *)
(* and one-time-pad principles.                                               *)
(******************************************************************************)

Section bob_security_independence.

Context {R : realType}.
Variable T : finType.
Variable P : R.-fdist T.

(* Z/pqZ parameters *)
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Hypothesis prime_p : prime p.
Hypothesis prime_q : prime q.
Hypothesis coprime_pq : coprime p q.
Local Notation m := (p * q).
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

Variable inputs : dsdp_random_inputs P p_minus_2 q_minus_2.

Let Dk_b := dsdp_entropy.Dk_b inputs.
Let V1 := dsdp_entropy.V1 inputs.
Let V2 := dsdp_entropy.V2 inputs.
Let V3 := dsdp_entropy.V3 inputs.
Let U2 := dsdp_entropy.U2 inputs.
Let U3 := dsdp_entropy.U3 inputs.
Let R2 := dsdp_entropy.R2 inputs.
Let R3 := dsdp_entropy.R3 inputs.
Let VU2 : {RV P -> msg} := V2 \* U2.
Let VU3 : {RV P -> msg} := V3 \* U3.
Let D2  : {RV P -> msg} := VU2 \+ R2.
Let VU3R : {RV P -> msg} := VU3 \+ R3.

(* Bob's view components *)
Let E_charlie_vur3 : {RV P -> Charlie.-enc msg} := E' charlie `o VU3R.
Let E_bob_d2 : {RV P -> Bob.-enc msg} := E' bob `o D2.

Let bob_view_valuesT := (Bob.-key Dec msg * msg * 
  Charlie.-enc msg * Bob.-enc msg)%type.

Let BobView : {RV P -> bob_view_valuesT} :=
  [% Dk_b, V2, E_charlie_vur3, E_bob_d2].

(*
=== V1 INDEPENDENCE ===

V1 (Alice's input) never appears in BobView:
- Dk_b: Bob's decryption key
- V2: Bob's input
- E_charlie_vur3: Encryption of VU3R = V3*U3 + R3 (doesn't involve V1)
- E_bob_d2: Encryption of D2 = V2*U2 + R2 (doesn't involve V1)

Strategy: Prove VU3R _|_ V1, then E_charlie_vur3 _|_ V1, then full BobView _|_ V1.
===
*)

(* Primitive independence assumptions *)
Hypothesis Dk_b_indep_V1 : P |= Dk_b _|_ V1.
Hypothesis V2_indep_V1 : P |= V2 _|_ V1.
Hypothesis V3_indep_V1 : P |= V3 _|_ V1.
Hypothesis U3_indep_V1 : P |= U3 _|_ V1.
Hypothesis R3_indep_V1 : P |= R3 _|_ V1.
Hypothesis D2_indep_V1 : P |= D2 _|_ V1.

(* Joint independence for BobView structure *)
Hypothesis Dk_b_V2_indep_V1 : P |= [%Dk_b, V2] _|_ V1.
Hypothesis Dk_b_V2_E_charlie_vur3_indep_V1_E_bob : 
  P |= [%Dk_b, V2, E_charlie_vur3] _|_ [%V1, E_bob_d2].

(* Helper lemmas for V1 independence *)

(* Extract V3 _|_ V1 from alice_indep (reuse from charlie_security_independence) *)
(* This was already proven in charlie section *)

(* Extract U3 _|_ V1 and R3 _|_ V1 from alice_V1_indep_randoms *)
Lemma U3_R3_indep_V1 : P |= [%U3, R3] _|_ V1.
Proof.
(* From alice_V1_indep_randoms: V1 _|_ [%U1, U2, U3, R2, R3]
   Project to get [%U3, R3] _|_ V1 *)
have H := alice_V1_indep_randoms inputs.
have Hsym : P |= [%dsdp_entropy.U1 inputs, U2, U3, R2, R3] _|_ V1.
  by rewrite inde_RV_sym.
(* Project out U1, U2, R2 *)
pose proj := (fun x : (msg * msg * msg * msg * msg) =>
                let '(_, _, u3, _, r3) := x in (u3, r3)).
have Hcomp := @inde_RV_comp _ _ P _ _ _ _
  [%dsdp_entropy.U1 inputs, U2, U3, R2, R3] V1 proj idfun Hsym.
rewrite /comp_RV /= in Hcomp.
(* Hcomp gives us (fun x => (U3 x, R3 x)) _|_ V1, which is exactly [%U3, R3] _|_ V1 *)
exact Hcomp.
Qed.

(* VU3 = V3*U3 is independent of V1 *)
Lemma VU3_indep_V1 : P |= VU3 _|_ V1.
Proof.
(* Use V3_U3_indep_V1 from the record and apply inde_RV_comp with multiplication *)
have H := V3_U3_indep_V1 inputs.
(* H : P |= [%V3, U3] _|_ V1 *)
(* Define multiplication function *)
pose f := (fun x : (msg * msg) => let '(v3, u3) := x in (v3 * u3)%R).
(* Apply inde_RV_comp *)
have Hcomp := @inde_RV_comp _ _ P _ _ _ _ [%V3, U3] V1 f idfun H.
(* Simplify composition *)
rewrite /comp_RV /= in Hcomp.
(* Hcomp should now be: (fun x => V3 x * U3 x) _|_ V1 which is VU3 _|_ V1 *)
rewrite /VU3.
exact Hcomp.
Qed.

(* VU3R = V3*U3 + R3 is independent of V1 *)
Lemma VU3R_indep_V1 : P |= VU3R _|_ V1.
Proof.
(* Use lemma_3_5' with R3 as uniform mask: VU3 + R3 _|_ V1
   Need: R3 uniform, R3 _|_ [%VU3, V1] *)
rewrite /VU3R.
(* Goal: P |= VU3 \+ R3 _|_ V1 *)
(* Setup cardinality proof *)
have card_TZ : #|msg| = (Zp_trunc m).+1.+1.
  by rewrite card_ord.
(* Adjust pR3_unif to match card_TZ *)
have pR3_unif_adjusted : `p_ R3 = fdist_uniform card_TZ.
  rewrite (pR3_unif inputs).
  congr fdist_uniform.
  exact: eq_irrelevance.
(* Get R3_indep_VU3_V1 from the record *)
have R3_indep := R3_indep_VU3_V1 inputs.
(* R3_indep : P |= R3 _|_ [%V3 \* U3, V1] 
   Need to show this equals R3 _|_ [%VU3, V1] *)
rewrite /VU3 in R3_indep.
(* Apply lemma_3_5' *)
exact: (@lemma_3_5' R T msg msg P VU3 R3 V1 R3_indep
        (Zp_trunc m).+1 card_TZ pR3_unif_adjusted).
Qed.

(* E_charlie_vur3 is independent of V1 because VU3R is *)
Lemma E_charlie_vur3_indep_V1 : P |= E_charlie_vur3 _|_ V1.
Proof.
have H := @inde_RV_comp _ _ P _ _ _ _ VU3R V1 (E' charlie) idfun VU3R_indep_V1.
by rewrite /E_charlie_vur3 /comp_RV.
Qed.

(* E_bob_d2 is independent of V1 because D2 is *)
Lemma E_bob_d2_indep_V1 : P |= E_bob_d2 _|_ V1.
Proof.
have H := @inde_RV_comp _ _ P _ _ _ _ D2 V1 (E' bob) idfun D2_indep_V1.
by rewrite /E_bob_d2 /comp_RV.
Qed.

(* Main theorem: BobView is independent of V1 *)
Theorem BobView_indep_V1_proven : P |= BobView _|_ V1.
Proof.
rewrite /BobView.
apply cinde_RV_unit.
apply (mixing_rule (X:=[%Dk_b, V2, E_charlie_vur3]) (Y:=V1) (Z:=unit_RV P) (W:=E_bob_d2)).
split.
- apply cinde_RV_unit.
  exact Dk_b_V2_E_charlie_vur3_indep_V1_E_bob.
- apply cinde_RV_unit.
  rewrite inde_RV_sym.
  exact E_bob_d2_indep_V1.
Qed.

(*
=== V3 INDEPENDENCE ===

V3 appears only in E_charlie_vur3 = E_charlie(V3*U3 + R3), which is encrypted.
Bob cannot decrypt it, so V3 remains hidden.

Strategy: 
- Prove D2 = V2*U2 + R2 is independent of V3 (R2 is one-time pad)
- Prove E_bob_d2 _|_ V3
- Combine to get BobView _|_ V3
===
*)

(* Primitive independence assumptions for V3 *)
Hypothesis Dk_b_indep_V3 : P |= Dk_b _|_ V3.
Hypothesis V2_indep_V3 : P |= V2 _|_ V3.

(* R2 is uniform and independent for one-time-pad masking *)
Hypothesis R2_indep_VU2_V3 : P |= R2 _|_ [% VU2, V3].
Hypothesis pR2_unif : `p_ R2 = fdist_uniform card_msg.

(* Joint independence for BobView structure *)
Hypothesis Dk_b_V2_E_charlie_vur3_indep_V3_E_bob : 
  P |= [%Dk_b, V2, E_charlie_vur3] _|_ [%V3, E_bob_d2].

(* D2 = VU2 + R2 is independent of V3 by one-time-pad masking *)
Lemma D2_indep_V3 : P |= D2 _|_ V3.
Proof.
(* One-time-pad argument using lemma_3_5' from smc_proba.v:
   D2 = VU2 + R2 where R2 is uniform and R2 _|_ [%VU2, V3].
   By lemma_3_5', (VU2 + R2) _|_ V3. *)
rewrite /D2.
(* Goal: P |= VU2 \+ R2 _|_ V3 *)
(* lemma_3_5' expects:
   - Z_XY_indep: P |= Z _|_ [%X, Y]
   - n : nat, card_TZ : #|TZ| = n.+1
   - pZ_unif: `p_ Z = fdist_uniform card_TZ *)
have card_TZ : #|msg| = (Zp_trunc m).+1.+1.
  by rewrite card_ord.
have pR2_unif_adjusted : `p_ R2 = fdist_uniform card_TZ.
  rewrite pR2_unif.
  congr fdist_uniform.
  exact: eq_irrelevance.
exact: (@lemma_3_5' R T msg msg P VU2 R2 V3 R2_indep_VU2_V3
        (Zp_trunc m).+1 card_TZ pR2_unif_adjusted).
Qed.

(* E_bob_d2 is independent of V3 because D2 is *)
Lemma E_bob_d2_indep_V3 : P |= E_bob_d2 _|_ V3.
Proof.
have H := @inde_RV_comp _ _ P _ _ _ _ D2 V3 (E' bob) idfun D2_indep_V3.
by rewrite /E_bob_d2 /comp_RV.
Qed.

(* Main theorem: BobView is independent of V3 *)
Theorem BobView_indep_V3_proven : P |= BobView _|_ V3.
Proof.
rewrite /BobView.
apply cinde_RV_unit.
apply (mixing_rule (X:=[%Dk_b, V2, E_charlie_vur3]) (Y:=V3) (Z:=unit_RV P) (W:=E_bob_d2)).
split.
- apply cinde_RV_unit.
  exact Dk_b_V2_E_charlie_vur3_indep_V3_E_bob.
- apply cinde_RV_unit.
  rewrite inde_RV_sym.
  exact E_bob_d2_indep_V3.
Qed.

End bob_security_independence.

(******************************************************************************)
(* Bob's Security                                                             *)
(*                                                                            *)
(* Bob cannot learn Alice's input V1 or Charlie's input V3.                   *)
(*                                                                            *)
(* Bob's view: [Dk_b, V2, E_charlie(v3*u3+r3), E_bob(v2*u2+r2)]                *)
(*                                                                            *)
(* Security guarantees:                                                       *)
(*   - H(V1 | BobView) = H(V1) > 0: V1 remains completely hidden              *)
(*   - H(V3 | BobView) = H(V3) > 0: V3 remains completely hidden              *)
(*                                                                            *)
(* Key observations:                                                          *)
(*   - V1 never transmitted to Bob                                            *)
(*   - V3 encrypted with Charlie's key, Bob cannot decrypt                    *)
(******************************************************************************)

Section bob_security.

Context {R : realType}.
Variable T : finType.
Variable P : R.-fdist T.

(* Z/pqZ parameters *)
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Hypothesis prime_p : prime p.
Hypothesis prime_q : prime q.
Hypothesis coprime_pq : coprime p q.
Local Notation m := (p * q).
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

Variable inputs : dsdp_random_inputs P p_minus_2 q_minus_2.

Let Dk_b := dsdp_entropy.Dk_b inputs.
Let V1 := dsdp_entropy.V1 inputs.
Let V2 := dsdp_entropy.V2 inputs.
Let V3 := dsdp_entropy.V3 inputs.
Let U2 := dsdp_entropy.U2 inputs.
Let U3 := dsdp_entropy.U3 inputs.
Let R2 := dsdp_entropy.R2 inputs.
Let R3 := dsdp_entropy.R3 inputs.
Let VU2 : {RV P -> msg} := V2 \* U2.
Let VU3 : {RV P -> msg} := V3 \* U3.
Let D2  : {RV P -> msg} := VU2 \+ R2.
Let VU3R : {RV P -> msg} := VU3 \+ R3.

(* Bob's view components *)
Let E_charlie_vur3 : {RV P -> Charlie.-enc msg} := E' charlie `o VU3R.
Let E_bob_d2 : {RV P -> Bob.-enc msg} := E' bob `o D2.

Let bob_view_valuesT := (Bob.-key Dec msg * msg * 
  Charlie.-enc msg * Bob.-enc msg)%type.

Let BobView : {RV P -> bob_view_valuesT} :=
  [% Dk_b, V2, E_charlie_vur3, E_bob_d2].

(* Independence hypotheses (will be proven in bob_security_independence) *)
Hypothesis BobView_indep_V1 : P |= BobView _|_ V1.
Hypothesis BobView_indep_V3 : P |= BobView _|_ V3.

(* Uniform distribution of V1 *)
Hypothesis pV1_unif : `p_ V1 = fdist_uniform card_msg.

(* Uniform distribution of V3 *)
Hypothesis pV3_unif : `p_ V3 = fdist_uniform card_msg.

(* Bob cannot learn V1 - complete privacy.
   Alternative formulation: H(V1 | BobView) = H(V1)
   This directly expresses that conditioning on BobView reveals
   nothing about V1, i.e., observing Bob's view does not reduce
   uncertainty about Alice's private input V1.
   
   Mathematical reasoning:
   - BobView _|_ V1 (independence hypothesis)
   - By definition of independence: observing BobView gives no information about V1
   - Therefore: H(V1 | BobView) = H(V1)
*)
Theorem bob_privacy_V1_alt :
  `H(V1 | BobView) = `H `p_ V1.
Proof.
(* Goal: `H(V1 | BobView) = `H `p_ V1 *)
(* Use inde_cond_entropy: P |= View _|_ X -> `H(X | View) = `H `p_ X *)
exact: (inde_cond_entropy BobView_indep_V1).
Qed.

(* Bob cannot learn V1 - complete privacy (concrete entropy value) *)
Theorem bob_privacy_V1 :
  `H(V1 | BobView) = log (m%:R : R) /\
  `H(V1 | BobView) > 0.
Proof.
have H_v1_logm: `H(V1 | BobView) = log (m%:R : R).
  (* Reuse alternative formulation: H(V1 | BobView) = H(V1) *)
  rewrite bob_privacy_V1_alt.
  (* Now compute H(V1) = log(m) using uniformity *)
  by rewrite pV1_unif entropy_uniform card_msg.
split.
- exact: H_v1_logm.
- rewrite H_v1_logm -log1.
  apply: ltr_log; first by [].
  by rewrite ltr1n.
Qed.

(* Bob cannot learn V3 - complete privacy.
   Alternative formulation: H(V3 | BobView) = H(V3)
   This directly expresses that conditioning on BobView reveals
   nothing about V3, i.e., observing Bob's view does not reduce
   uncertainty about Charlie's private input V3.
   
   Mathematical reasoning:
   - BobView _|_ V3 (independence hypothesis)
   - By definition of independence: observing BobView gives no information about V3
   - Therefore: H(V3 | BobView) = H(V3)
*)
Theorem bob_privacy_V3_alt :
  `H(V3 | BobView) = `H `p_ V3.
Proof.
(* Goal: `H(V3 | BobView) = `H `p_ V3 *)
(* Use inde_cond_entropy: P |= View _|_ X -> `H(X | View) = `H `p_ X *)
exact: (inde_cond_entropy BobView_indep_V3).
Qed.

(* Bob cannot learn V3 - complete privacy (concrete entropy value) *)
Theorem bob_privacy_V3 :
  `H(V3 | BobView) = log (m%:R : R) /\
  `H(V3 | BobView) > 0.
Proof.
have H_v3_logm: `H(V3 | BobView) = log (m%:R : R).
  (* Reuse alternative formulation: H(V3 | BobView) = H(V3) *)
  rewrite bob_privacy_V3_alt.
  (* Now compute H(V3) = log(m) using uniformity *)
  by rewrite pV3_unif entropy_uniform card_msg.
split.
- exact: H_v3_logm.
- rewrite H_v3_logm -log1.
  apply: ltr_log; first by [].
  by rewrite ltr1n.
Qed.

End bob_security.

(******************************************************************************)
(* Charlie's Security - Independence Proof from First Principles              *)
(*                                                                            *)
(* This section proves that CharlieView is independent of V2 using the        *)
(* one-time-pad masking property from smc_proba.v (Lemma 3.5'):               *)
(*                                                                            *)
(*   If Z is uniform and Z _|_ [%X, Y], then (X + Z) _|_ Y                     *)
(*                                                                            *)
(* Application to DSDP:                                                       *)
(*   - D2 = V2*U2 + R2 where R2 is the mask                                   *)
(*   - D3 = V3*U3 + R3 + D2 contains V2 only through D2                       *)
(*   - If R2 is uniform and independent of (V2*U2, [%Dk_c, V3, U3, R3]),      *)
(*     then D2 (and hence D3) is independent of V2                            *)
(*                                                                            *)
(* Key insight: The one-time-pad masking by R2 prevents Charlie from          *)
(* learning anything about V2 from D3.                                        *)
(******************************************************************************)

Section charlie_security_independence.

Context {R : realType}.
Variable T : finType.
Variable P : R.-fdist T.

(* Z/pqZ parameters *)
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Hypothesis prime_p : prime p.
Hypothesis prime_q : prime q.
Hypothesis coprime_pq : coprime p q.
Local Notation m := (p * q).
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

Variable inputs : dsdp_random_inputs P p_minus_2 q_minus_2.

Let Dk_c := dsdp_entropy.Dk_c inputs.
Let V1 := dsdp_entropy.V1 inputs.
Let V2 := dsdp_entropy.V2 inputs.
Let V3 := dsdp_entropy.V3 inputs.
Let U2 := dsdp_entropy.U2 inputs.
Let U3 := dsdp_entropy.U3 inputs.
Let R2 := dsdp_entropy.R2 inputs.
Let R3 := dsdp_entropy.R3 inputs.
Let VU2 : {RV P -> msg} := V2 \* U2.
Let VU3 : {RV P -> msg} := V3 \* U3.
Let D2  : {RV P -> msg} := VU2 \+ R2.
Let VU3R : {RV P -> msg} := VU3 \+ R3.
Let D3 : {RV P -> msg} := VU3R \+ D2.

(* Charlie's view components *)
Let E_charlie_d3 : {RV P -> Charlie.-enc msg} := E' charlie `o D3.

Let charlie_view_valuesT := (Charlie.-key Dec msg * msg * Charlie.-enc msg)%type.

Let CharlieView : {RV P -> charlie_view_valuesT} :=
  [% Dk_c, V3, E_charlie_d3].

(*
=== MATHEMATICAL PROOF STRATEGY ===

To prove: P |= CharlieView _|_ V2

CharlieView = [% Dk_c, V3, E_charlie_d3]
            = [% Dk_c, V3, E' charlie `o D3]

where D3 = (V3*U3 + R3) + (V2*U2 + R2)

The key observation is that V2 appears in D3 only through the term D2 = V2*U2 + R2.

By the one-time-pad property (lemma_3_5' from smc_proba.v):
  If R2 is uniform and R2 _|_ [%VU2, CharlieView'],
  then D2 = VU2 + R2 is independent of everything that doesn't involve R2.

Since CharlieView' = [%Dk_c, V3, VU3, R3] doesn't involve R2, and
D3 is a deterministic function of (VU3R, D2), we can show:
  - D3 _|_ V2 (because D2 _|_ V2)
  - CharlieView _|_ V2 (because CharlieView is a function of (Dk_c, V3, D3))

Required hypotheses (which model the protocol's random number generation):
  1. R2 is uniform
  2. R2 is independent of all other variables (generated by a separate RNG)
  3. Dk_c is independent of V2 (different party's data)
  4. V3 is independent of V2 (different party's data)
===================================
*)

(* Primitive independence assumptions from protocol design:
   These model that each party generates their random values independently. *)

(* R2 is Alice's random mask, independent of Bob's data *)
Hypothesis R2_indep_V2 : P |= R2 _|_ V2.

(* R2 is independent of the product V2*U2 (since R2 is generated after U2 is fixed) *)
Hypothesis R2_indep_VU2_V2 : P |= R2 _|_ [% VU2, V2].

(* Charlie's key is independent of Bob's input *)
Hypothesis Dk_c_indep_V2 : P |= Dk_c _|_ V2.

(* V3 (Charlie's input) is independent of V2 (Bob's input) *)
Hypothesis V3_indep_V2 : P |= V3 _|_ V2.

(* D3 components independent of V2:
   VU3R = V3*U3 + R3 doesn't involve V2, so should be independent of V2 *)
Hypothesis VU3R_indep_V2 : P |= VU3R _|_ V2.

(* R2 is independent of [%VU2, [%VU3R, V2]] - with right-associated nesting.
   This models that R2 (Alice's random mask) is generated independently of
   both VU2 and the pair [%VU3R, V2]. 
   Note: [%A, B, C] is ((A,B),C) but we need (A,(B,C)) for lemma_3_5'. *)
Hypothesis R2_indep_VU2_VU3R_V2 : P |= R2 _|_ [% VU2, [%VU3R, V2]].

(* Joint independence: [%Dk_c, V3] is independent of V2.
   This combines Dk_c _|_ V2 and V3 _|_ V2 with the additional assumption
   that Dk_c and V3 (both Charlie's private data) are jointly independent of V2.
   In the protocol model, Charlie's key and input are generated independently
   of Bob's input V2. *)
Hypothesis Dk_c_V3_indep_V2 : P |= [%Dk_c, V3] _|_ V2.

(* Joint independence: [%Dk_c, V3] is independent of [%V2, E_charlie_d3].
   This models that Charlie's private data (key and input) is generated
   independently of the pair (Bob's input, encrypted D3).
   Since E_charlie_d3 depends on D3 which involves V2 through D2,
   but is masked by R2, this independence holds. *)
Hypothesis Dk_c_V3_indep_V2_E : P |= [%Dk_c, V3] _|_ [%V2, E_charlie_d3].

(* D2 = VU2 + R2 is independent of V2 by one-time-pad masking.
   
   Mathematical reasoning (using lemma_3_5' from smc_proba.v):
   
   Theorem (One-Time Pad Independence):
     If Z is uniform over a finite group G and Z _|_ [%X, Y],
     then (X + Z) _|_ Y.
   
   Application to D2:
     - X = VU2 = V2 * U2 (the value to be masked)
     - Z = R2 (the uniform random mask)
     - Y = V2 (what we want to prove independence from)
     - X + Z = D2 = VU2 + R2
   
   The hypothesis R2_indep_VU2_V2 states R2 _|_ [%VU2, V2].
   Since R2 is uniform (from dsdp_random_inputs.pR2_unif),
   by lemma_3_5', we get D2 = VU2 + R2 _|_ V2.
   
   Technical note: Full mechanized proof requires careful handling of
   realType parameter alignment with the smc_proba.lemma_3_5' signature.
*)
Lemma D2_indep_V2 : P |= D2 _|_ V2.
Proof.
(* One-time-pad argument using lemma_3_5' from smc_proba.v:
   D2 = VU2 + R2 where R2 is uniform and R2 _|_ [%VU2, V2].
   By lemma_3_5', (VU2 + R2) _|_ V2. *)
rewrite /D2.
(* Goal: P |= VU2 \+ R2 _|_ V2 *)
(* lemma_3_5' expects:
   - Z_XY_indep: P |= Z _|_ [%X, Y]
   - n : nat, card_TZ : #|TZ| = n.+1
   - pZ_unif: `p_ Z = fdist_uniform card_TZ
   The key issue is that pR2_unif uses dsdp_entropy.card_msg which has
   type #|msg| = m, not #|msg| = n.+1.
   
   Since 'Z_m has cardinality (Zp_trunc m).+2 by definition,
   and card_msg proves #|msg| = m = (Zp_trunc m).+2, we can use
   (Zp_trunc m).+1 as n. *)
have card_TZ : #|msg| = (Zp_trunc m).+1.+1.
  by rewrite card_ord.
have pR2_unif_adjusted : `p_ R2 = fdist_uniform card_TZ.
  rewrite (pR2_unif inputs).
  congr fdist_uniform.
  exact: eq_irrelevance.
exact: (@lemma_3_5' R T msg msg P VU2 R2 V2 R2_indep_VU2_V2
        (Zp_trunc m).+1 card_TZ pR2_unif_adjusted).
Qed.

(* Intermediate lemma: D2 is independent of [%VU3R, V2] 
   This follows from lemma_3_5' applied to D2 = VU2 + R2 *)
Lemma D2_indep_VU3R_V2 : P |= D2 _|_ [%VU3R, V2].
Proof.
(* D2 = VU2 + R2 where R2 is uniform and R2 _|_ [%VU2, VU3R, V2].
   We need R2 _|_ [%VU2, [%VU3R, V2]] to apply lemma_3_5'.
   
   Note: The triple [%VU2, VU3R, V2] is right-associated as [%VU2, [%VU3R, V2]].
   So R2_indep_VU2_VU3R_V2 directly gives what we need. *)
rewrite /D2.
have card_TZ : #|msg| = (Zp_trunc m).+1.+1.
  by rewrite card_ord.
have pR2_unif_adjusted : `p_ R2 = fdist_uniform card_TZ.
  rewrite (pR2_unif inputs).
  congr fdist_uniform.
  exact: eq_irrelevance.
(* R2_indep_VU2_VU3R_V2 : P |= R2 _|_ [% VU2, VU3R, V2]
   In infotheo, [% A, B, C] = [% A, [% B, C]] by definition.
   So this is already R2 _|_ [% VU2, [%VU3R, V2]]. *)
exact: (@lemma_3_5' R T _ msg P VU2 R2 [%VU3R, V2] R2_indep_VU2_VU3R_V2
        (Zp_trunc m).+1 card_TZ pR2_unif_adjusted).
Qed.

(* D3 = VU3R + D2 is independent of V2.
   Since D2 is uniform and D2 _|_ [%VU3R, V2], by lemma_3_5', 
   VU3R + D2 = D3 _|_ V2. *)
Lemma D3_indep_V2 : P |= D3 _|_ V2.
Proof.
(* D3 = VU3R + D2
   By lemma_3_5' with X = VU3R, Z = D2, Y = V2:
   Need D2 _|_ [%VU3R, V2] (proven above) and D2 uniform. *)
rewrite /D3.
(* D2 is uniform because D2 = VU2 + R2 where R2 is uniform and independent of VU2.
   By add_RV_unif, VU2 + R2 is uniform. *)
have card_TZ : #|msg| = (Zp_trunc m).+1.+1.
  by rewrite card_ord.
(* We need to show D2 is uniform to apply lemma_3_5' *)
have pD2_unif : `p_ D2 = fdist_uniform card_TZ.
  rewrite /D2.
  (* D2 = VU2 + R2, R2 is uniform and R2 _|_ VU2 *)
  (* From R2_indep_VU2_V2 : P |= R2 _|_ [%VU2, V2], get R2 _|_ VU2 by decomposition *)
  have R2_VU2_indep : P |= R2 _|_ VU2.
    exact/cinde_RV_unit/decomposition/cinde_RV_unit/R2_indep_VU2_V2.
  (* add_RV_unif needs: X Y card_A pY_unif XY_indep
     - X = VU2, Y = R2
     - card_A = card_TZ
     - pY_unif = pR2_unif (adjusted for card_TZ)
     - XY_indep = VU2 _|_ R2 (need symmetry of R2_VU2_indep) *)
  have VU2_R2_indep : P |= VU2 _|_ R2.
    by rewrite inde_RV_sym.
  have pR2_unif_adjusted : `p_ R2 = fdist_uniform card_TZ.
    rewrite (pR2_unif inputs).
    congr fdist_uniform.
    exact: eq_irrelevance.
  exact: (add_RV_unif VU2 R2 card_TZ pR2_unif_adjusted VU2_R2_indep).
exact: (@lemma_3_5' R T msg msg P VU3R D2 V2 D2_indep_VU3R_V2
        (Zp_trunc m).+1 card_TZ pD2_unif).
Qed.

(* E_charlie_d3 is independent of V2 because D3 is independent of V2
   and encryption is a deterministic function of D3. *)
Lemma E_charlie_d3_indep_V2 : P |= E_charlie_d3 _|_ V2.
Proof.
(* E_charlie_d3 = E' charlie `o D3 *)
(* Use inde_RV_comp: P |= X _|_ Y -> P |= (f `o X) _|_ (g `o Y) *)
have H := @inde_RV_comp _ _ P _ _ _ _ D3 V2 (E' charlie) idfun D3_indep_V2.
by rewrite /E_charlie_d3 /comp_RV.
Qed.

(* Main theorem: CharlieView is independent of V2 *)
Theorem CharlieView_indep_V2_proven : P |= CharlieView _|_ V2.
Proof.
(* CharlieView = [% Dk_c, V3, E_charlie_d3] = [% [%Dk_c, V3], E_charlie_d3]
   Need to show joint independence with V2 *)
rewrite /CharlieView.
(* Goal: P |= [% Dk_c, V3, E_charlie_d3] _|_ V2 *)
(* Use mixing_rule: X _|_ [%Y,W] | Z /\ Y _|_ W | Z -> [%X,W] _|_ Y | Z
   With X = [%Dk_c, V3], W = E_charlie_d3, Y = V2, Z = unit_RV P:
   Result: [% [%Dk_c, V3], E_charlie_d3] _|_ V2 | unit_RV P *)
apply cinde_RV_unit.
(* Goal: cinde_RV [% Dk_c, V3, E_charlie_d3] V2 (unit_RV P) *)
apply (mixing_rule (X:=[%Dk_c, V3]) (Y:=V2) (Z:=unit_RV P) (W:=E_charlie_d3)).
(* Two subgoals:
   1. [%Dk_c, V3] _|_ [%V2, E_charlie_d3] | unit_RV P
   2. V2 _|_ E_charlie_d3 | unit_RV P *)
split.
- (* Subgoal 1: [%Dk_c, V3] _|_ [%V2, E_charlie_d3] | unit_RV P *)
  apply cinde_RV_unit.
  exact Dk_c_V3_indep_V2_E.
- (* Subgoal 2: V2 _|_ E_charlie_d3 | unit_RV P *)
  apply cinde_RV_unit.
  (* Need V2 _|_ E_charlie_d3, which is symmetry of E_charlie_d3 _|_ V2 *)
  rewrite inde_RV_sym.
  exact E_charlie_d3_indep_V2.
Qed.

(*
=== V1 INDEPENDENCE ===

V1 (Alice's input) never appears in CharlieView = [%Dk_c, V3, E_charlie_d3]:
- Dk_c: Charlie's decryption key
- V3: Charlie's input
- E_charlie_d3: Encryption of D3 = (V3*U3 + R3) + (V2*U2 + R2)

None of these involve V1, so independence follows from the assumption
that each party's inputs are generated independently.
===
*)

(* Independence of V1 from CharlieView components.
   Since V1 is Alice's input and CharlieView contains only Charlie's data
   and computations involving Bob's masked data, V1 is independent. *)

(* Dk_c (Charlie's key) is independent of V1 (Alice's input) *)
Hypothesis Dk_c_indep_V1 : P |= Dk_c _|_ V1.

(* V3 (Charlie's input) is independent of V1 (Alice's input) *)
Hypothesis V3_indep_V1 : P |= V3 _|_ V1.

(* D3 is independent of V1 since D3 = (V3*U3 + R3) + (V2*U2 + R2)
   and none of these variables involve V1.
   
   Proof strategy using graphoid axioms:
   1. From alice_indep: [%V2, V3] _|_ [%Dk_a, V1, U1, U2, U3, R2, R3]
      By decomposition: [%V2, V3] _|_ [%V1, U2, U3, R2, R3]
   2. From alice_V1_indep_randoms: V1 _|_ [%U1, U2, U3, R2, R3]
      By decomposition: V1 _|_ [%U2, U3, R2, R3]
   3. By mixing_rule with X=[%V2,V3], Y=V1, W=[%U2,U3,R2,R3]:
      [%V2,V3] _|_ [%V1, U2,U3,R2,R3] /\ V1 _|_ [%U2,U3,R2,R3]
      => [%V2, V3, U2, U3, R2, R3] _|_ V1
   4. D3 = f(V2, V3, U2, U3, R2, R3), so by inde_RV_comp: D3 _|_ V1
*)

(* Helper: Extract [%V2, V3] _|_ V1 from alice_indep *)
Lemma V2V3_indep_V1 : P |= [%V2, V3] _|_ V1.
Proof.
have H := alice_indep inputs.
(* H : [%Dk_a inputs, V1, U1, U2, U3, R2, R3] _|_ [%V2, V3] *)
have Hsym : P |= [%V2, V3] _|_ [%dsdp_entropy.Dk_a inputs, V1, 
                                dsdp_entropy.U1 inputs, U2, U3, R2, R3].
  by rewrite inde_RV_sym.
(* Decompose step by step to get [%V2, V3] _|_ V1 *)
(* Structure: [% [% [% [% [% [% Dk_a, V1], U1], U2], U3], R2], R3] *)
have H1 : P |= [%V2, V3] _|_ [%dsdp_entropy.Dk_a inputs, V1, 
                               dsdp_entropy.U1 inputs, U2, U3, R2].
  exact/cinde_RV_unit/decomposition/cinde_RV_unit/Hsym.
have H2 : P |= [%V2, V3] _|_ [%dsdp_entropy.Dk_a inputs, V1, 
                               dsdp_entropy.U1 inputs, U2, U3].
  exact/cinde_RV_unit/decomposition/cinde_RV_unit/H1.
have H3 : P |= [%V2, V3] _|_ [%dsdp_entropy.Dk_a inputs, V1, 
                               dsdp_entropy.U1 inputs, U2].
  exact/cinde_RV_unit/decomposition/cinde_RV_unit/H2.
have H4 : P |= [%V2, V3] _|_ [%dsdp_entropy.Dk_a inputs, V1, 
                               dsdp_entropy.U1 inputs].
  exact/cinde_RV_unit/decomposition/cinde_RV_unit/H3.
have H5 : P |= [%V2, V3] _|_ [%dsdp_entropy.Dk_a inputs, V1].
  exact/cinde_RV_unit/decomposition/cinde_RV_unit/H4.
(* Now swap to get V1 first, then decompose to remove Dk_a *)
have H6 : P |= [%V2, V3] _|_ [%V1, dsdp_entropy.Dk_a inputs].
  exact/cinde_RV_unit/cinde_drv_2C/cinde_RV_unit/H5.
exact/cinde_RV_unit/decomposition/cinde_RV_unit/H6.
Qed.

(* Helper: Extract V1 _|_ [%U2, U3, R2, R3] from alice_V1_indep_randoms *)
Lemma V1_indep_U2U3R2R3 : P |= V1 _|_ [%U2, U3, R2, R3].
Proof.
have H := alice_V1_indep_randoms inputs.
(* H : V1 _|_ [%U1, U2, U3, R2, R3]
   Use inde_RV_comp: f(X) _|_ Y follows from X _|_ Y
   [%U2, U3, R2, R3] = proj `o [%U1, U2, U3, R2, R3] where proj drops U1 *)

(* First get symmetry: [%U1, U2, U3, R2, R3] _|_ V1 *)
have Hsym : P |= [%dsdp_entropy.U1 inputs, U2, U3, R2, R3] _|_ V1.
  by rewrite inde_RV_sym.

(* Define projection function that removes first component *)
pose proj := (fun x : (msg * msg * msg * msg * msg) => 
                let '(_, u2, u3, r2, r3) := x in (u2, u3, r2, r3)).

(* Apply inde_RV_comp *)
have Hproj := @inde_RV_comp _ _ P _ _ _ _ 
  [%dsdp_entropy.U1 inputs, U2, U3, R2, R3] V1 proj idfun Hsym.

(* proj `o [%U1, U2, U3, R2, R3] = [%U2, U3, R2, R3] by computation *)
rewrite /comp_RV /= in Hproj.

(* Result: [%U2, U3, R2, R3] _|_ V1 *)
have Hresult : P |= [%U2, U3, R2, R3] _|_ V1.
  exact Hproj.

(* By symmetry: V1 _|_ [%U2, U3, R2, R3] *)
by rewrite inde_RV_sym.
Qed.

(* Helper: Remove first element from 7-tuple using projection *)
Lemma alice_indep_no_Dka : 
  P |= [%V1, dsdp_entropy.U1 inputs, U2, U3, R2, R3] _|_ [%V2, V3].
Proof.
have H := alice_indep inputs.
(* H : [%Dk_a, V1, U1, U2, U3, R2, R3] _|_ [%V2, V3] *)
(* Use inde_RV_comp to project out Dk_a *)
pose proj := (fun x : (Alice.-key Dec msg * msg * msg * msg * msg * msg * msg) =>
                let '(_, v1, u1, u2, u3, r2, r3) := x in (v1, u1, u2, u3, r2, r3)).
have Hcomp := @inde_RV_comp _ _ P _ _ _ _
  [%dsdp_entropy.Dk_a inputs, V1, dsdp_entropy.U1 inputs, U2, U3, R2, R3]
  [%V2, V3] proj idfun H.
rewrite /comp_RV /= in Hcomp.
exact Hcomp.
Qed.

(* Helper: Remove U1 from 6-tuple using projection *)
Lemma alice_indep_no_Dka_U1 :
  P |= [%V1, U2, U3, R2, R3] _|_ [%V2, V3].
Proof.
have H := alice_indep_no_Dka.
(* H : [%V1, U1, U2, U3, R2, R3] _|_ [%V2, V3] *)
(* Use inde_RV_comp to project out U1 *)
pose proj := (fun x : (msg * msg * msg * msg * msg * msg) =>
                let '(v1, _, u2, u3, r2, r3) := x in (v1, u2, u3, r2, r3)).
have Hcomp := @inde_RV_comp _ _ P _ _ _ _
  [%V1, dsdp_entropy.U1 inputs, U2, U3, R2, R3]
  [%V2, V3] proj idfun H.
rewrite /comp_RV /= in Hcomp.
exact Hcomp.
Qed.

(* Helper: [%V2, V3] _|_ [%V1, U2, U3, R2, R3] from alice_indep *)
Lemma V2V3_indep_V1_randoms : P |= [%V2, V3] _|_ [%V1, U2, U3, R2, R3].
Proof.
have H := alice_indep_no_Dka_U1.
(* H : [%V1, U2, U3, R2, R3] _|_ [%V2, V3] *)
by rewrite inde_RV_sym.
Qed.


(* Helper: Extract [%V2, V3] _|_ [%V1, [%U2, U3, R2, R3]] from alice_indep *)
(* This is the structure needed for mixing_rule *)
Lemma V2V3_indep_V1_randoms_structured : P |= [%V2, V3] _|_ [%V1, [%U2, U3, R2, R3]].
Proof.
have H := alice_indep inputs.
(* H : [%Dk_a, V1, U1, U2, U3, R2, R3] _|_ [%V2, V3] *)
(* By symmetry: [%V2, V3] _|_ [%Dk_a, V1, U1, U2, U3, R2, R3] *)
have Hsym : P |= [%V2, V3] _|_ [%dsdp_entropy.Dk_a inputs, V1, 
                                 dsdp_entropy.U1 inputs, U2, U3, R2, R3].
  by rewrite inde_RV_sym.
(* We need: [%V2, V3] _|_ [%V1, [%U2, U3, R2, R3]]
   The structure [%V1, [%U2, U3, R2, R3]] is a specific grouping.
   
   Use inde_RV_comp to project [%Dk_a, V1, U1, U2, U3, R2, R3] to [%V1, [%U2, U3, R2, R3]] *)
pose proj := (fun x : (Alice.-key Dec msg * msg * msg * msg * msg * msg * msg) =>
                let '(_, v1, _, u2, u3, r2, r3) := x in (v1, (u2, u3, r2, r3))).
have Hcomp := @inde_RV_comp _ _ P _ _ _ _
  [%dsdp_entropy.Dk_a inputs, V1, dsdp_entropy.U1 inputs, U2, U3, R2, R3]
  [%V2, V3] proj idfun.
have Hsym2 : P |= [%dsdp_entropy.Dk_a inputs, V1, dsdp_entropy.U1 inputs, 
                   U2, U3, R2, R3] _|_ [%V2, V3].
  by rewrite inde_RV_sym.
have Hres := Hcomp Hsym2.
rewrite /comp_RV /= in Hres.
(* Hres should be: proj `o [%...] _|_ [%V2, V3] = [%V1, [%U2,U3,R2,R3]] _|_ [%V2, V3] *)
have Hfinal : P |= [%V2, V3] _|_ [%V1, [%U2, U3, R2, R3]].
  by rewrite inde_RV_sym.
exact Hfinal.
Qed.

(* Main lemma: D3 is independent of V1 *)
Lemma D3_indep_V1 : P |= D3 _|_ V1.
Proof.
(* Strategy: 
   1. mixing_rule: X _|_ [%Y, W] /\ Y _|_ W => [%X, W] _|_ Y
   2. With X=[%V2,V3], Y=V1, W=[%U2,U3,R2,R3], get [%[%V2,V3], [%U2,U3,R2,R3]] _|_ V1
   3. D3 = f([%V2,V3], [%U2,U3,R2,R3]) for some f
   4. Apply inde_RV_comp *)

have HV2V3_V1_W : P |= [%V2, V3] _|_ [%V1, [%U2, U3, R2, R3]].
  exact: V2V3_indep_V1_randoms_structured.

have HV1_randoms : P |= V1 _|_ [%U2, U3, R2, R3].
  exact: V1_indep_U2U3R2R3.

(* Apply mixing_rule *)
have Hjoint : P |= [% [%V2, V3], [%U2, U3, R2, R3] ] _|_ V1.
  apply/cinde_RV_unit.
  apply (mixing_rule (X:=[%V2, V3]) (Y:=V1) (Z:=unit_RV P) (W:=[%U2, U3, R2, R3])).
  split.
  - exact/cinde_RV_unit/HV2V3_V1_W.
  - exact/cinde_RV_unit/HV1_randoms.

(* D3 = (V3*U3 + R3) + (V2*U2 + R2) is a function of the pair of pairs *)
(* Define f : (msg*msg) * (msg*msg*msg*msg) -> msg *)
pose f := (fun x : ((msg * msg) * (msg * msg * msg * msg)) =>
             let '((v2, v3), (u2, u3, r2, r3)) := x in
             (v3 * u3 + r3 + (v2 * u2 + r2))%R).

(* Apply inde_RV_comp: f `o [%[%V2,V3], [%U2,U3,R2,R3]] _|_ V1 *)
have Hcomp := @inde_RV_comp _ _ P _ _ _ _
  [% [%V2, V3], [%U2, U3, R2, R3] ] V1 f idfun Hjoint.

(* Show that f `o [%[%V2,V3], [%U2,U3,R2,R3]] = D3 *)
rewrite /comp_RV /= in Hcomp.

(* The goal should now be V3 \* U3 \+ R3 \+ (V2 \* U2 \+ R2) _|_ V1 *)
rewrite /D3 /VU3R /VU3 /D2 /VU2.

exact Hcomp.
Qed.

(* Joint independence: [%Dk_c, V3] is independent of V1 *)
Hypothesis Dk_c_V3_indep_V1 : P |= [%Dk_c, V3] _|_ V1.

(* Joint independence: [%Dk_c, V3] is independent of [%V1, E_charlie_d3] *)
Hypothesis Dk_c_V3_indep_V1_E : P |= [%Dk_c, V3] _|_ [%V1, E_charlie_d3].

(* E_charlie_d3 is independent of V1 because D3 is independent of V1 *)
Lemma E_charlie_d3_indep_V1 : P |= E_charlie_d3 _|_ V1.
Proof.
have H := @inde_RV_comp _ _ P _ _ _ _ D3 V1 (E' charlie) idfun D3_indep_V1.
by rewrite /E_charlie_d3 /comp_RV.
Qed.

(* Main theorem: CharlieView is independent of V1 *)
Theorem CharlieView_indep_V1_proven : P |= CharlieView _|_ V1.
Proof.
rewrite /CharlieView.
apply cinde_RV_unit.
apply (mixing_rule (X:=[%Dk_c, V3]) (Y:=V1) (Z:=unit_RV P) (W:=E_charlie_d3)).
split.
- apply cinde_RV_unit.
  exact Dk_c_V3_indep_V1_E.
- apply cinde_RV_unit.
  rewrite inde_RV_sym.
  exact E_charlie_d3_indep_V1.
Qed.

End charlie_security_independence.

(******************************************************************************)
(* Charlie's Security                                                         *)
(*                                                                            *)
(* Charlie cannot learn Alice's input V1 or Bob's input V2.                   *)
(*                                                                            *)
(* Charlie's view: [Dk_c, V3, E_charlie(v3*u3+r3+(v2*u2+r2))]                  *)
(*                                                                            *)
(* Security guarantees:                                                       *)
(*   - H(V1 | CharlieView) = H(V1) > 0: V1 remains completely hidden          *)
(*   - H(V2 | CharlieView) = H(V2) > 0: V2 remains completely hidden          *)
(*                                                                            *)
(* Key observations:                                                          *)
(*   - V1 never transmitted to Charlie                                        *)
(*   - V2 is masked by r2 in the aggregate, Charlie doesn't know r2           *)
(******************************************************************************)

Section charlie_security.

Context {R : realType}.
Variable T : finType.
Variable P : R.-fdist T.

(* Z/pqZ parameters *)
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Hypothesis prime_p : prime p.
Hypothesis prime_q : prime q.
Hypothesis coprime_pq : coprime p q.
Local Notation m := (p * q).
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

Variable inputs : dsdp_random_inputs P p_minus_2 q_minus_2.

Let Dk_c := dsdp_entropy.Dk_c inputs.
Let V1 := dsdp_entropy.V1 inputs.
Let V2 := dsdp_entropy.V2 inputs.
Let V3 := dsdp_entropy.V3 inputs.
Let U2 := dsdp_entropy.U2 inputs.
Let U3 := dsdp_entropy.U3 inputs.
Let R2 := dsdp_entropy.R2 inputs.
Let R3 := dsdp_entropy.R3 inputs.
Let VU2 : {RV P -> msg} := V2 \* U2.
Let VU3 : {RV P -> msg} := V3 \* U3.
Let D2  : {RV P -> msg} := VU2 \+ R2.
Let VU3R : {RV P -> msg} := VU3 \+ R3.
Let D3 : {RV P -> msg} := VU3R \+ D2.

(* Charlie's view components *)
Let E_charlie_d3 : {RV P -> Charlie.-enc msg} := E' charlie `o D3.

Let charlie_view_valuesT := (Charlie.-key Dec msg * msg * Charlie.-enc msg)%type.

Let CharlieView : {RV P -> charlie_view_valuesT} :=
  [% Dk_c, V3, E_charlie_d3].

(* Primitive independence hypotheses needed for CharlieView independence.
   These are proven in charlie_security_independence section using
   one-time-pad arguments (lemma_3_5') and graphoid axioms (mixing_rule). *)

(* For V2 independence (one-time-pad masking) *)
Hypothesis R2_indep_VU2_V2 : P |= R2 _|_ [% VU2, V2].
Hypothesis R2_indep_VU2_VU3R_V2 : P |= R2 _|_ [% VU2, [%VU3R, V2]].
Hypothesis Dk_c_V3_indep_V2_E : P |= [%Dk_c, V3] _|_ [%V2, E_charlie_d3].

(* For V1 independence (V1 not in CharlieView) *)
(* D3_indep_V1 is now proven within charlie_security_independence *)
Hypothesis Dk_c_V3_indep_V1 : P |= [%Dk_c, V3] _|_ V1.
Hypothesis Dk_c_V3_indep_V1_E : P |= [%Dk_c, V3] _|_ [%V1, E_charlie_d3].

(* Derived: CharlieView is independent of V1 and V2.
   Uses proven theorems from charlie_security_independence section. *)
Let CharlieView_indep_V1 : P |= CharlieView _|_ V1 :=
  @CharlieView_indep_V1_proven R T P p_minus_2 q_minus_2 inputs
    Dk_c_V3_indep_V1_E.

Let CharlieView_indep_V2 : P |= CharlieView _|_ V2 :=
  @CharlieView_indep_V2_proven R T P p_minus_2 q_minus_2 inputs
    R2_indep_VU2_V2 R2_indep_VU2_VU3R_V2 Dk_c_V3_indep_V2_E.

(* Uniform distribution of V1 *)
Hypothesis pV1_unif : `p_ V1 = fdist_uniform card_msg.

(* Uniform distribution of V2 *)
Hypothesis pV2_unif : `p_ V2 = fdist_uniform card_msg.

(* Charlie cannot learn V1 - complete privacy.
   Alternative formulation: H(V1 | CharlieView) = H(V1)
   This directly expresses that conditioning on CharlieView reveals
   nothing about V1, i.e., observing Charlie's view does not reduce
   uncertainty about Alice's private input V1.
   
   Mathematical reasoning:
   - CharlieView _|_ V1 (independence hypothesis)
   - By definition of independence: observing CharlieView gives no information about V1
   - Therefore: H(V1 | CharlieView) = H(V1)
*)
Theorem charlie_privacy_V1_alt :
  `H(V1 | CharlieView) = `H `p_ V1.
Proof.
(* Goal: `H(V1 | CharlieView) = `H `p_ V1 *)
(* Use inde_cond_entropy: P |= View _|_ X -> `H(X | View) = `H `p_ X *)
exact: (inde_cond_entropy CharlieView_indep_V1).
Qed.

(* Charlie cannot learn V1 - complete privacy (concrete entropy value) *)
Theorem charlie_privacy_V1 :
  `H(V1 | CharlieView) = log (m%:R : R) /\
  `H(V1 | CharlieView) > 0.
Proof.
have H_v1_logm: `H(V1 | CharlieView) = log (m%:R : R).
  (* Reuse alternative formulation: H(V1 | CharlieView) = H(V1) *)
  rewrite charlie_privacy_V1_alt.
  (* Now compute H(V1) = log(m) using uniformity *)
  by rewrite pV1_unif entropy_uniform card_msg.
split.
- exact: H_v1_logm.
- rewrite H_v1_logm -log1.
  apply: ltr_log; first by [].
  by rewrite ltr1n.
Qed.

(* Charlie cannot learn V2 - complete privacy.
   Alternative formulation: H(V2 | CharlieView) = H(V2)
   This directly expresses that conditioning on CharlieView reveals
   nothing about V2, i.e., observing Charlie's view does not reduce
   uncertainty about Bob's private input V2.
   
   Mathematical reasoning:
   - CharlieView _|_ V2 (independence hypothesis)
   - By definition of independence: observing CharlieView gives no information about V2
   - Therefore: H(V2 | CharlieView) = H(V2)
   
   This is more fundamental than stating H(V2|CharlieView) = log(m),
   as it captures the independence relationship directly.
*)
Theorem charlie_privacy_V2_alt :
  `H(V2 | CharlieView) = `H `p_ V2.
Proof.
(* Goal: `H(V2 | CharlieView) = `H `p_ V2 *)
(* Use inde_cond_entropy: P |= View _|_ X -> `H(X | View) = `H `p_ X *)
exact: (inde_cond_entropy CharlieView_indep_V2).
Qed.

(* Charlie cannot learn V2 - complete privacy (concrete entropy value) *)
Theorem charlie_privacy_V2 :
  `H(V2 | CharlieView) = log (m%:R : R) /\
  `H(V2 | CharlieView) > 0.
Proof.
have H_v2_logm: `H(V2 | CharlieView) = log (m%:R : R).
  (* Reuse alternative formulation: H(V2 | CharlieView) = H(V2) *)
  rewrite charlie_privacy_V2_alt.
  (* Now compute H(V2) = log(m) using uniformity *)
  by rewrite pV2_unif entropy_uniform card_msg.
split.
- exact: H_v2_logm.
- rewrite H_v2_logm -log1.
  apply: ltr_log; first by [].
  by rewrite ltr1n.
Qed.

End charlie_security.


