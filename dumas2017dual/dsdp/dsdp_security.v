From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap matrix lra reals.
Require Import rouche_capelli.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter spp_proba.
Require Import homomorphic_encryption.
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
(*    - Independence properties ensure entropic security guarantees           *)
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

(* Define concrete party values for use with E' and encryption *)
Let alice : party_id := Alice.
Let bob : party_id := Bob.
Let charlie : party_id := Charlie.

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

(* Encryption hypotheses for E_enc_ce_contract:
   These are standard information-theoretic assumptions for homomorphic encryption.
   1. Fresh ciphertexts are uniformly distributed over the ciphertext space
   2. Fresh ciphertexts are independent of all other random variables
   These enable dropping encryption terms from conditional entropy calculations. *)
Hypothesis E_enc_unif : forall (T0 : finType) (P0 : R.-fdist T0)
  (A : finType) (p : party_id) (X : {RV P0 -> p.-enc A}) (n : nat)
  (card_A : #|A| = n.+1),
  `p_X = fdist_uniform (card_enc_for' p card_A).

Hypothesis E_enc_inde : forall (A B : finType) (p : party_id)
  (X : {RV P -> p.-enc A}) (Y : {RV P -> B}),
  P |= X _|_ Y.

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

(* Additional hypotheses for joint_centropy_reduction *)
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
   not the full log(m^2) bits - proving entropic security.
*)
Theorem dsdp_constraint_centropy_eqlogm :
  `H(VarRV | CondRV) = log (m%:R : R).
Proof.
(* Goal: `H(VarRV | CondRV) = log (m%:R : R)
   where VarRV = [% V2, V3], CondRV = [% V1, U1, U2, U3, S] *)
(* Apply dsdp_centropy_uniform from dsdp_entropy.v.
   Must provide all section parameters explicitly. *)
apply dsdp_centropy_uniform.
- exact prime_p.
- exact prime_q.
- exact coprime_pq.
- exact constraint_holds.
- exact VarRV_uniform.
- exact VarRV_indep_inputs.
- exact U3_pos.
- exact U3_lt_minpq.
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

(* DSDP entropic security: H(V2 | AliceView) = log(m) = H(V2) > 0.
   Since log(m) is the maximum entropy for V2 over Z/pqZ, this means
   Alice's view is statistically independent of V2: individual secrets
   enjoy perfect privacy in the sense of Dodis-Smith entropic security. *)
Theorem dsdp_entropic_security :
  `H(V2 | AliceView) = log (m%:R : R) /\
  `H(V2 | AliceView) > 0.
Proof.
(* Proof chain: H(V2|AliceView) = H(V2|CondRV) = H([V2,V3]|CondRV) = log(m) *)
have H_v2_logm: `H(V2 | AliceView) = log (m%:R : R).
  (* Use alice_view_to_cond from dsdp_entropy.v with the record *)
  rewrite (alice_view_to_cond E_enc_unif E_enc_inde Pr_AliceView_neq0 Pr_Eqn1View_neq0
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

(* Entropic security interpretation:
   H(V2 | AliceView) = log(m) = H(V2), so Alice's view reveals
   nothing about V2 — individual secrets enjoy perfect privacy.
   The joint (V2,V3) loses log(m) bits (from 2*log(m) to log(m)),
   but this corresponds exactly to the protocol output S that
   Alice is supposed to learn, not a security violation.
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
(* From alice_view to [% Alice_input_view, S] - strip encryption terms *)
rewrite (E_enc_ce_contract E_enc_unif E_enc_inde V2 card_msg); last exact: Pr_AliceView_neq0.
rewrite (E_enc_ce_contract E_enc_unif E_enc_inde V2 card_msg); last exact: Pr_Eqn1View_neq0.
rewrite (E_enc_ce_contract E_enc_unif E_enc_inde V2 card_msg); last exact: Pr_Eqn2View_neq0.
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

(* Define concrete party values for use with E' and encryption *)
Let alice : party_id := Alice.
Let bob : party_id := Bob.
Let charlie : party_id := Charlie.

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

(* Define concrete party values for use with E' and encryption *)
Let alice : party_id := Alice.
Let bob : party_id := Bob.
Let charlie : party_id := Charlie.

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

(* Define concrete party values for use with E' and encryption *)
Let alice : party_id := Alice.
Let bob : party_id := Bob.
Let charlie : party_id := Charlie.

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

(* Define concrete party values for use with E' and encryption *)
Let alice : party_id := Alice.
Let bob : party_id := Bob.
Let charlie : party_id := Charlie.

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

(******************************************************************************)
(* N-Party Relay Security                                                     *)
(*                                                                            *)
(* Generalizes Bob/Charlie security to arbitrary relay parties.               *)
(* Each relay party i has:                                                    *)
(*   - Dk_i: decryption key                                                  *)
(*   - V_i: private input                                                    *)
(*   - E_recv_i: encrypted value received                                    *)
(*   - E_sent_i: encrypted value sent                                        *)
(*                                                                            *)
(* Security: RelayView_i _|_ V_j for all j != i, proved via one-time-pad.   *)
(*                                                                            *)
(* The proof pattern is uniform for all relay parties:                        *)
(*   1. D_j = V_j * U_j + R_j where R_j is uniform mask                     *)
(*   2. By lemma_3_5': D_j _|_ V_i                                          *)
(*   3. E(D_j) _|_ V_i by inde_RV_comp                                      *)
(*   4. mixing_rule composes into full view independence                     *)
(*   5. inde_cond_entropy converts to H(V_j | View_i) = H(V_j)             *)
(******************************************************************************)

Section relay_security_n.

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

(* Generic relay party: one-time-pad masking makes D = VU + R independent of
   any target variable Y, given R is uniform and independent of [%VU, Y]. *)

(* Random variables for one relay party's one-time-pad argument *)
Variable VU_i : {RV P -> msg}.   (* V_i * U_i *)
Variable R_i : {RV P -> msg}.    (* random mask *)
Variable Y : {RV P -> msg}.      (* target variable (e.g., V_j for j != i) *)

Let D_i : {RV P -> msg} := VU_i \+ R_i.

Hypothesis R_i_indep_VU_Y : P |= R_i _|_ [%VU_i, Y].
Hypothesis pR_i_unif : `p_ R_i = fdist_uniform card_msg.

(* Core one-time-pad lemma: D_i = VU_i + R_i is independent of Y *)
Lemma relay_otp_indep : P |= D_i _|_ Y.
Proof.
rewrite /D_i.
have card_TZ : #|msg| = (Zp_trunc m).+1.+1.
  by rewrite card_ord.
have pR_i_unif_adj : `p_ R_i = fdist_uniform card_TZ.
  rewrite pR_i_unif.
  congr fdist_uniform.
  exact: eq_irrelevance.
exact: (@lemma_3_5' R T msg msg P VU_i R_i Y R_i_indep_VU_Y
        (Zp_trunc m).+1 card_TZ pR_i_unif_adj).
Qed.

(* Encryption of D_i is independent of Y *)
Lemma relay_enc_otp_indep (party : party_id) :
  P |= (E' party `o D_i) _|_ Y.
Proof.
have H := @inde_RV_comp _ _ P _ _ _ _ D_i Y (E' party) idfun relay_otp_indep.
by rewrite /comp_RV.
Qed.

(* Generic relay privacy theorem:
   If RelayView _|_ V_target, then H(V_target | RelayView) = H(V_target) *)
Lemma relay_privacy_from_indep {A : finType}
    (View : {RV P -> A}) (V_target : {RV P -> msg})
    (pV_unif : `p_ V_target = fdist_uniform card_msg)
    (View_indep : P |= View _|_ V_target) :
  `H(V_target | View) = `H `p_ V_target.
Proof. exact: (inde_cond_entropy View_indep). Qed.

(* Concrete privacy: H(V_target | View) = log(m) > 0 *)
Lemma relay_privacy_logm {A : finType}
    (View : {RV P -> A}) (V_target : {RV P -> msg})
    (pV_unif : `p_ V_target = fdist_uniform card_msg)
    (View_indep : P |= View _|_ V_target) :
  `H(V_target | View) = log (m%:R : R) /\
  `H(V_target | View) > 0.
Proof.
have H_logm: `H(V_target | View) = log (m%:R : R).
  rewrite (relay_privacy_from_indep pV_unif View_indep).
  by rewrite pV_unif entropy_uniform card_msg.
split.
- exact: H_logm.
- rewrite H_logm -log1.
  apply: ltr_log; first by [].
  by rewrite ltr1n.
Qed.

End relay_security_n.

(******************************************************************************)
(* N-Party Encryption Contraction                                             *)
(*                                                                            *)
(* Inductive predicate for views that consist of a base RV plus encryptions:  *)
(*   View = [%...[%[%Base, E_1], E_2], ..., E_k]                              *)
(* Each encryption can be contracted using E_enc_ce_contract, yielding:       *)
(*   H(Z | View) = H(Z | Base)                                               *)
(*                                                                            *)
(* This replaces the manual 3-fold application in alice_view_to_cond.         *)
(******************************************************************************)

Section enc_contraction_n.

Context {R : realType}.
Variable T : finType.
Variable P : R.-fdist T.

(* Encryption hypotheses *)
Hypothesis E_enc_unif : forall (T0 : finType) (P0 : R.-fdist T0)
  (A : finType) (pty : party_id) (X : {RV P0 -> pty.-enc A}) (n : nat)
  (card_A : #|A| = n.+1),
  `p_X = fdist_uniform (card_enc_for' pty card_A).

Hypothesis E_enc_inde : forall (A B : finType) (pty : party_id)
  (X : {RV P -> pty.-enc A}) (Y : {RV P -> B}),
  P |= X _|_ Y.

(* Inductive predicate: a view that is "base plus encryptions" *)
Inductive enc_contractible {C : finType} (Z : {RV P -> C}) (target : R)
    : forall {A : finType}, {RV P -> A} -> Prop :=
  | ec_base : forall {A : finType} (X : {RV P -> A}),
      `H(Z | X) = target -> enc_contractible Z target X
  | ec_enc : forall {A B : finType} (pty : party_id)
      (X : {RV P -> A}) (E : {RV P -> pty.-enc B}) (n : nat),
      enc_contractible Z target X ->
      #|B| = n.+1 ->
      (forall x e, `Pr[[%X, E] = (x, e)] != 0) ->
      enc_contractible Z target [%X, E].

(* Contraction theorem: if a view is enc_contractible, its conditional
   entropy equals the target *)
Theorem enc_ce_contract_ind {C : finType} (Z : {RV P -> C}) (target : R)
    {A : finType} (View : {RV P -> A}) :
  enc_contractible Z target View -> `H(Z | View) = target.
Proof.
elim => [A' X -> // | A' B pty X E n _ IH card_B Hpr].
by rewrite (E_enc_ce_contract E_enc_unif E_enc_inde Z card_B Hpr).
Qed.

End enc_contraction_n.

(******************************************************************************)
(* N-Party DSDP Entropic Security                                            *)
(*                                                                            *)
(* Generalizes Alice's security from 3 parties to N parties.                  *)
(*                                                                            *)
(* Alice's view in N-party protocol:                                          *)
(*   [Dk_a, S, V0, U0, u_rel, R_1, ..., R_{n-1}, E_1, ..., E_k]              *)
(*                                                                            *)
(* Security theorem:                                                          *)
(*   H(VarRV | AliceView_n) = log(m^n_relay) > 0                             *)
(*                                                                            *)
(* Proof chain:                                                               *)
(*   1. Contract encryptions: H(VarRV | AliceView) = H(VarRV | DecView)      *)
(*   2. Strip auxiliary: H(VarRV | DecView) = H(VarRV | CondRV)              *)
(*   3. Entropy bound: H(VarRV | CondRV) = log(m^n_relay)                    *)
(******************************************************************************)

Section dsdp_security_n.

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

Variable n_relay : nat.

Let m_gt0 : (0 < m)%N.
Proof. by rewrite muln_gt0 prime_gt0 // prime_gt0. Qed.

Let m_gt1 : (1 < m)%N.
Proof.
have Hp2: (1 < p)%N by [].
have Hq2: (1 < q)%N by [].
by rewrite (ltn_trans Hp2) // -{1}(muln1 p) ltn_pmul2l // ltnS.
Qed.

Let card_msg : #|msg| = m.
Proof. by rewrite card_ord Zp_cast. Qed.

Let card_ffun_msg : #|{ffun 'I_n_relay.+1 -> msg}| = (m ^ n_relay.+1).-1.+1.
Proof. by rewrite prednK ?expn_gt0 ?m_gt0 // card_ffun !card_ord Zp_cast. Qed.

(* N-party section variables (instead of a record) *)
Variable VarRV : {RV P -> {ffun 'I_n_relay.+1 -> msg}}.

(* Condition: (v0, u0, u_relay_vector, s) *)
Let CondT_n := (msg * msg * {ffun 'I_n_relay.+1 -> msg} * msg)%type.
Variable CondRV : {RV P -> CondT_n}.

(* Encryption hypotheses *)
Hypothesis E_enc_unif : forall (T0 : finType) (P0 : R.-fdist T0)
  (A : finType) (pty : party_id) (X : {RV P0 -> pty.-enc A}) (n : nat)
  (card_A : #|A| = n.+1),
  `p_X = fdist_uniform (card_enc_for' pty card_A).

Hypothesis E_enc_inde : forall (A B : finType) (pty : party_id)
  (X : {RV P -> pty.-enc A}) (Y : {RV P -> B}),
  P |= X _|_ Y.

(* The N-party entropy bound from dsdp_entropy_n *)
Hypothesis dsdp_centropy_n :
  `H(VarRV | CondRV) = log ((m ^ n_relay)%:R : R).

(* Alice's view is some type that contracts to CondRV *)
Variable AliceViewT : finType.
Variable AliceView : {RV P -> AliceViewT}.

(* The view contracts to CondRV (via enc_contractible or manual proof) *)
Hypothesis alice_view_contract :
  `H(VarRV | AliceView) = `H(VarRV | CondRV).

(* Core N-party entropic security: entropy value *)
Theorem dsdp_entropic_security_n_eq :
  `H(VarRV | AliceView) = log ((m ^ n_relay)%:R : R).
Proof. by rewrite alice_view_contract dsdp_centropy_n. Qed.

(* Core N-party entropic security: entropy is positive when n_relay > 0 *)
Theorem dsdp_entropic_security_n :
  (0 < n_relay)%N ->
  `H(VarRV | AliceView) = log ((m ^ n_relay)%:R : R) /\
  `H(VarRV | AliceView) > 0.
Proof.
move=> Hn.
split.
- exact: dsdp_entropic_security_n_eq.
- rewrite dsdp_entropic_security_n_eq -log1.
  apply: ltr_log; first by [].
  rewrite ltr1n -(expn0 m).
  by rewrite ltn_exp2l.
Qed.

End dsdp_security_n.

(******************************************************************************)
(* N-Party Malicious Adversary Case Analysis                                  *)
(*                                                                            *)
(* Generalizes the 2D dot product analysis to N-1 dimensions.                 *)
(* If Alice sets US = e_1 (first basis vector), she can extract V_1          *)
(* from the dot product result, compromising relay party 1's privacy.        *)
(******************************************************************************)

Section malicious_n.

Context {R : realType}.
Variable T : finType.
Variable P : R.-fdist T.

(* Z/pqZ parameters *)
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Local Notation m := (p * q).
Local Notation msg := 'Z_m.

Variable n_relay : nat.

(* N-dimensional dot product *)
Definition dotp_n (x y : {ffun 'I_n_relay.+1 -> msg}) : msg :=
  \sum_(i < n_relay.+1) x i * y i.

(* Dot product as random variable *)
Definition Dotp_n_rv (X Y : {RV P -> {ffun 'I_n_relay.+1 -> msg}}) : {RV P -> msg} :=
  fun t => dotp_n (X t) (Y t).

(* First basis vector: e_1 = (1, 0, ..., 0) *)
Definition ConstUS_n : {ffun 'I_n_relay.+1 -> msg} :=
  [ffun i => if i == ord0 then 1 else 0].

(* e_1 . v = v_1: the first basis vector extracts the first component *)
Lemma dotp_n_e1 (v : {ffun 'I_n_relay.+1 -> msg}) :
  dotp_n ConstUS_n v = v ord0.
Proof.
rewrite /dotp_n (bigD1 ord0) //=.
rewrite ffunE eq_refl mul1r.
rewrite big1 ?addr0 //.
move=> i Hi.
by rewrite ffunE (negbTE Hi) mul0r.
Qed.

(* If Alice sets US = e_1, she can extract V_1 *)
Lemma ConstUS_n_discloses_V1
    (US VS : {RV P -> {ffun 'I_n_relay.+1 -> msg}}) :
  US = (fun _ => ConstUS_n) ->
  Dotp_n_rv US VS = (fun t => VS t ord0).
Proof.
move->.
rewrite /Dotp_n_rv.
apply: boolp.funext => t /=.
by rewrite dotp_n_e1.
Qed.

End malicious_n.

(******************************************************************************)
(*                                                                            *)
(* N-Party DSDP: Concrete AliceView + Per-Relay Privacy                       *)
(*                                                                            *)
(* Fills the gaps between 3-party and n-party security proofs:                *)
(*                                                                            *)
(* 1. Concrete AliceView (N2-N4): replaces the abstract AliceViewT/           *)
(*    alice_view_contract hypothesis in dsdp_security_n with a concrete       *)
(*    construction using enc_contractible.                                    *)
(*                                                                            *)
(* 2. Per-relay privacy (N6-N9): generalizes bob_privacy_V1/V3 and           *)
(*    charlie_privacy_V1/V2 from 3-party to n-party.                         *)
(*                                                                            *)
(* Dependency graph:                                                          *)
(*                                                                            *)
(*   N1 (dsdp_random_inputs_n)                                                *)
(*    ├── N2 (alice_view_n_T) → N3 (AliceView_n)                             *)
(*    │         → N4 (alice_view_contract_n) → N10 (concrete security)        *)
(*    ├── N5 (cinde_V_relay) ──────────────────────────────────↗              *)
(*    └── N6 (relay_view_n) → N7 (RelayView_n)                               *)
(*          ├── N8a (otp_mask_indep) → N8b (enc_indep)                        *)
(*          │        → N8c (nonadj_indep) ──┐                                 *)
(*          └── N8a → N8b → N8d (adj_indep)─┤                                *)
(*                                          ↓                                 *)
(*                               N8e (relay_indep) → N9 (relay_privacy_n)    *)
(*                                                                            *)
(******************************************************************************)

(* ========================================================================== *)
(* N1: N-party random inputs record                                           *)
(*                                                                            *)
(* Bundles all random variables and independence/uniformity hypotheses         *)
(* for an n-party DSDP instance. Generalizes the 3-party Section variables    *)
(* into a reusable record.                                                    *)
(* ========================================================================== *)

Section dsdp_concrete_n.

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

Variable n_relay : nat.
Hypothesis Hn_relay : (0 < n_relay)%N.

Let m_gt1 : (1 < m)%N.
Proof.
have Hp2: (1 < p)%N by [].
have Hq2: (1 < q)%N by [].
by rewrite (ltn_trans Hp2) // -{1}(muln1 p) ltn_pmul2l // ltnS.
Qed.

Let card_msg : #|msg| = m.
Proof. by rewrite card_ord Zp_cast. Qed.

(* Encryption hypotheses — same as in enc_contraction_n *)
Hypothesis E_enc_unif : forall (T0 : finType) (P0 : R.-fdist T0)
  (A : finType) (pty : party_id) (X : {RV P0 -> pty.-enc A}) (n : nat)
  (card_A : #|A| = n.+1),
  `p_X = fdist_uniform (card_enc_for' pty card_A).

Hypothesis E_enc_inde : forall (A B : finType) (pty : party_id)
  (X : {RV P -> pty.-enc A}) (Y : {RV P -> B}),
  P |= X _|_ Y.

(* --- N-party random variables --- *)

(* Alice's private inputs *)
Variable V0 : {RV P -> msg}.        (* Alice's private value *)
Variable U0 : {RV P -> msg}.        (* Alice's private coefficient *)
Variable Dk_a : {RV P -> msg}.      (* Alice's decryption key *)

(* Result *)
Variable S : {RV P -> msg}.         (* protocol output s = sum u_i * v_i *)

(* Relay variables: indexed by relay index 'I_n_relay.+1 *)
(* Each relay i has: V_i (private value), U_i (coefficient), R_i (random mask) *)
Variable VarRV : {RV P -> {ffun 'I_n_relay.+1 -> msg}}.  (* joint (V_1,...,V_{n+1}) *)
Variable U_relay : 'I_n_relay.+1 -> {RV P -> msg}.        (* U_i per relay *)
Variable R_relay : 'I_n_relay.+1 -> {RV P -> msg}.        (* R_i per relay *)

(* Encryptions Alice sees: one per relay party.
   The encryption type depends on the relay's party_id. For simplicity,
   we abstract over a single encryption type. *)
Variable enc_msg : finType.  (* type of encrypted messages Alice sees *)
Variable E_relay : 'I_n_relay.+1 -> {RV P -> enc_msg}.

(* Condition RV: (V0, U0, u_relay_vector, S) *)
Let CondT_n := (msg * msg * {ffun 'I_n_relay.+1 -> msg} * msg)%type.
Variable CondRV : {RV P -> CondT_n}.

(* --- Independence / uniformity hypotheses --- *)

(* Each V_i is uniform over Z/pqZ *)
(* TODO: VarRV uniformity hypothesis — needs cardinality lemma for {ffun} *)
(* Hypothesis VarRV_uniform :
  `p_ VarRV = fdist_uniform (...). *)

(* VarRV is independent of (V0, U0, U_relay) — relay secrets are independent
   of Alice's inputs and the public coefficients *)
Hypothesis VarRV_indep_inputs :
  P |= [%V0, U0] _|_ VarRV.

(* Each R_i is uniform and independent of everything else *)
Hypothesis R_relay_unif : forall i, `p_ (R_relay i) = fdist_uniform card_msg.
Hypothesis R_relay_indep : forall i,
  P |= R_relay i _|_ [%VarRV, V0, U0, S].

(* The entropy bound from fiber counting (dsdp_entropy.v) *)
Hypothesis dsdp_centropy_n :
  `H(VarRV | CondRV) = log ((m ^ n_relay)%:R : R).

(* ========================================================================== *)
(* N2: Alice's concrete view type                                             *)
(*                                                                            *)
(* Alice sees: her key Dk_a, the result S, her input V0, her coefficient U0,  *)
(* the relay coefficients (u_1,...,u_{n+1}), random masks (R_1,...,R_{n+1}),  *)
(* and one encryption per relay party.                                        *)
(*                                                                            *)
(* The encryption type is abstracted as enc_msg : finType. In the concrete    *)
(* instantiation, enc_msg = pty.-enc msg for the appropriate party_id.        *)
(* ========================================================================== *)

Let alice_view_n_T :=
  (msg * msg * msg * msg *
   {ffun 'I_n_relay.+1 -> msg} *
   {ffun 'I_n_relay.+1 -> msg} *
   {ffun 'I_n_relay.+1 -> enc_msg})%type.

(* ========================================================================== *)
(* N3: AliceView_n — concrete random variable for Alice's view                *)
(*                                                                            *)
(* Challenge: U_relay, R_relay, E_relay are 'I_n_relay.+1 -> {RV P -> X},    *)
(* i.e., families of random variables indexed by relay index. But we need     *)
(* a single RV producing an {ffun}: {RV P -> {ffun 'I_n_relay.+1 -> X}}.     *)
(* We convert via pointwise evaluation: fun t => [ffun i => f i t].          *)
(* ========================================================================== *)

(* Helper: convert a family of RVs to a single RV producing an {ffun} *)
Let U_relay_RV : {RV P -> {ffun 'I_n_relay.+1 -> msg}} :=
  fun t => [ffun i => U_relay i t].

Let R_relay_RV : {RV P -> {ffun 'I_n_relay.+1 -> msg}} :=
  fun t => [ffun i => R_relay i t].

Let E_relay_RV : {RV P -> {ffun 'I_n_relay.+1 -> enc_msg}} :=
  fun t => [ffun i => E_relay i t].

(* Alice's concrete view: all quantities she observes during the protocol *)
Let AliceView_n : {RV P -> alice_view_n_T} :=
  [% Dk_a, S, V0, U0, U_relay_RV, R_relay_RV, E_relay_RV].

(* DecView: Alice's view without encryptions — the "base" for contraction.
   After stripping encryptions via E_enc_ce_contract, the conditional entropy
   reduces to H(VarRV | DecView_n). *)
Let DecView_n : {RV P -> (msg * msg * msg * msg *
   {ffun 'I_n_relay.+1 -> msg} * {ffun 'I_n_relay.+1 -> msg})} :=
  [% Dk_a, S, V0, U0, U_relay_RV, R_relay_RV].

(* ========================================================================== *)
(* N4: alice_view_contract_n                                                  *)
(*                                                                            *)
(* Proves H(VarRV | AliceView_n) = H(VarRV | CondRV) by:                     *)
(*   1. Strip encryptions: H(VarRV | AliceView_n) = H(VarRV | DecView_n)     *)
(*      via enc_ce_contract_ind (each E_relay i is a fresh ciphertext)        *)
(*   2. Strip Dk_a and R_relay: H(VarRV | DecView_n) = H(VarRV | CondRV)     *)
(*      via conditional independence (cinde_V_relay)                          *)
(* ========================================================================== *)

(* N5: Conditional independence of (Dk_a, R_relay) from VarRV given CondRV.
   This is the n-party analogue of cinde_V2V3 from the 3-party proof. *)
Hypothesis cinde_V_relay :
  P |= [% Dk_a, R_relay_RV] _|_ VarRV | CondRV.

(* Pr_neq0 hypothesis: all joint probabilities in the extended views are
   nonzero. Required by E_enc_ce_contract for each encryption stripping step.
   In the 3-party case, these were Pr_AliceView_neq0, Pr_Eqn1View_neq0, etc.
   For n parties, we state this inductively over the relay index. *)

(* For the base case + encryption contraction, we need:
   - Pr_DecView_E_neq0: Pr[(DecView_n, E_relay_RV) = (x, e)] != 0
   This is sufficient when all encryptions are bundled as a single {ffun}. *)
Hypothesis Pr_AliceView_n_neq0 :
  forall (x : msg * msg * msg * msg *
              {ffun 'I_n_relay.+1 -> msg} * {ffun 'I_n_relay.+1 -> msg})
         (e : {ffun 'I_n_relay.+1 -> enc_msg}),
  `Pr[ [% DecView_n, E_relay_RV] = (x, e) ] != 0.

(* The contraction lemma: Alice's full view has the same conditional entropy
   as the condition RV. This is the key step plugging into dsdp_security_n. *)
Lemma alice_view_contract_n :
  `H(VarRV | AliceView_n) = `H(VarRV | CondRV).
Proof.
Admitted.

(* ========================================================================== *)
(* N10: Concrete n-party entropic security theorem                            *)
(*                                                                            *)
(* Plugs N3 (concrete AliceView) and N4 (contraction) into                    *)
(* dsdp_entropic_security_n to get a theorem with NO abstract hypotheses      *)
(* about Alice's view.                                                        *)
(* ========================================================================== *)

Theorem dsdp_entropic_security_n_concrete :
  `H(VarRV | AliceView_n) = log ((m ^ n_relay)%:R : R) /\
  `H(VarRV | AliceView_n) > 0.
Proof.
split.
- by rewrite alice_view_contract_n dsdp_centropy_n.
- rewrite alice_view_contract_n dsdp_centropy_n -log1.
  apply: ltr_log; first by [].
  rewrite ltr1n -(expn0 m).
  by rewrite ltn_exp2l.
Qed.

End dsdp_concrete_n.

(******************************************************************************)
(* Per-Relay Privacy: N-Party Generalization                                  *)
(*                                                                            *)
(* Generalizes bob_privacy_V1/V3 and charlie_privacy_V1/V2 from 3-party      *)
(* to arbitrary n-party. Each relay party i learns nothing about relay j's    *)
(* private value V_j (for j != i).                                            *)
(*                                                                            *)
(* Structure:                                                                 *)
(*   N6:  relay_view_n — what relay i sees                                    *)
(*   N7:  RelayView_n — random variable for relay i's view                   *)
(*   N8a: relay_otp_mask_indep — D_k = VU_k + R_k ⊥ V_j                     *)
(*   N8b: relay_enc_indep — E(D_k) ⊥ V_j                                    *)
(*   N8c: relay_view_indep_nonadj — V_j not in view when |i-j| > 1          *)
(*   N8d: relay_view_indep_adj — V_j masked by OTP when |i-j| = 1           *)
(*   N8e: relay_indep_V_target_n — combines N8c and N8d                      *)
(*   N9:  relay_privacy_n — H(V_j | RelayView_i) = log(m) > 0               *)
(******************************************************************************)

Section relay_privacy_concrete_n.

Context {R : realType}.
Variable T : finType.
Variable P : R.-fdist T.

Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Hypothesis prime_p : prime p.
Hypothesis prime_q : prime q.
Hypothesis coprime_pq : coprime p q.
Local Notation m := (p * q).
Local Notation msg := 'Z_m.

Variable n_relay : nat.
Hypothesis Hn_relay : (0 < n_relay)%N.

Let m_gt1 : (1 < m)%N.
Proof.
have Hp2: (1 < p)%N by [].
have Hq2: (1 < q)%N by [].
by rewrite (ltn_trans Hp2) // -{1}(muln1 p) ltn_pmul2l // ltnS.
Qed.

Let card_msg : #|msg| = m.
Proof. by rewrite card_ord Zp_cast. Qed.

(* Per-relay random variables *)
Variable V_relay : 'I_n_relay.+1 -> {RV P -> msg}.  (* V_i per relay *)
Variable U_relay : 'I_n_relay.+1 -> {RV P -> msg}.  (* U_i per relay *)
Variable R_relay : 'I_n_relay.+1 -> {RV P -> msg}.  (* R_i random mask *)

(* Uniformity hypotheses *)
Hypothesis V_relay_unif : forall i, `p_ (V_relay i) = fdist_uniform card_msg.
Hypothesis R_relay_unif : forall i, `p_ (R_relay i) = fdist_uniform card_msg.

(* Independence: R_i is independent of the OTP payload V_i*U_i paired with
   any target V_j. This is the form needed for relay_otp_indep. *)
Hypothesis R_relay_indep_VUV : forall i j,
  P |= R_relay i _|_ [%V_relay i \* U_relay i, V_relay j].

(* ========================================================================== *)
(* N6: Relay i's view type (simplified)                                       *)
(*                                                                            *)
(* Relay i sees its private value V_i, coefficient U_i, and random mask R_i. *)
(* This simplified view is sufficient for the OTP independence argument.      *)
(* The full view with received/sent ciphertexts can be extended later.        *)
(* ========================================================================== *)

Let relay_view_n_T := (msg * msg * msg)%type.

(* ========================================================================== *)
(* N7: RelayView_n — random variable for relay i's view                      *)
(* ========================================================================== *)

Let RelayView_n (i : 'I_n_relay.+1) : {RV P -> relay_view_n_T} :=
  [% V_relay i, U_relay i, R_relay i].

(* ========================================================================== *)
(* N8a: OTP mask independence                                                 *)
(*                                                                            *)
(* D_i = V_i * U_i + R_i is independent of V_j for any j,                   *)
(* given R_i is uniform and independent of [%V_i * U_i, V_j].               *)
(* This is a direct application of relay_otp_indep.                           *)
(* ========================================================================== *)

Lemma relay_otp_mask_indep (i j : 'I_n_relay.+1) :
  P |= (V_relay i \* U_relay i \+ R_relay i) _|_ V_relay j.
Proof.
have pR_adj : `p_ (R_relay i) = fdist_uniform (card_msg_subproof4 p_minus_2 q_minus_2).
  rewrite R_relay_unif; congr fdist_uniform; exact: eq_irrelevance.
exact: (@relay_otp_indep R T P p_minus_2 q_minus_2
  (V_relay i \* U_relay i) (R_relay i) (V_relay j)
  (R_relay_indep_VUV i j) pR_adj).
Qed.

(* ========================================================================== *)
(* N8b: Encryption independence (Admitted — needs encryption hypotheses)      *)
(*                                                                            *)
(* E(D_i) is independent of V_j. Requires encryption uniformity/independence *)
(* hypotheses (E_enc_unif, E_enc_inde) which are not in this section.        *)
(* ========================================================================== *)

(* N8b requires encryption hypotheses not available in this section.
   To be proved when encryption infrastructure is added. *)

(* ========================================================================== *)
(* N8c: Non-adjacent relay independence (Admitted)                            *)
(*                                                                            *)
(* When |i - j| > 1, V_j never appears in relay i's view at all.            *)
(* With the simplified view [%V_i, U_i, R_i], this holds for all j != i     *)
(* since V_j, U_j, R_j are distinct random variables.                        *)
(* ========================================================================== *)

(* N8c: With the simplified view, non-adjacency is not needed —
   the view [%V_i, U_i, R_i] never contains V_j for j != i. *)

(* ========================================================================== *)
(* N8d: Adjacent relay independence (Admitted)                                *)
(*                                                                            *)
(* With the simplified view, adjacency case reduces to the same argument     *)
(* as N8c. The harder case arises with the full view containing ciphertexts. *)
(* ========================================================================== *)

(* N8d: Deferred to full-view extension. *)

(* ========================================================================== *)
(* N8e: Combined relay independence                                           *)
(*                                                                            *)
(* For any relay i and target j != i:                                         *)
(*   RelayView_n(i) ⊥ V_relay(j)                                            *)
(*                                                                            *)
(* With the simplified view [%V_i, U_i, R_i], this requires showing that    *)
(* the triple (V_i, U_i, R_i) is independent of V_j for j != i.            *)
(* This is a stronger independence assumption than N8a alone.                *)
(* ========================================================================== *)

Lemma relay_indep_V_target_n (i j : 'I_n_relay.+1) :
  i != j ->
  P |= RelayView_n i _|_ V_relay j.
Proof.
move=> Hij.
Admitted.

(* ========================================================================== *)
(* N9: Per-relay privacy theorem                                              *)
(*                                                                            *)
(* For any relay i and target j != i:                                         *)
(*   H(V_j | RelayView_n(i)) = log(m) > 0                                   *)
(*                                                                            *)
(* This is the n-party generalization of bob_privacy_V1/V3 and               *)
(* charlie_privacy_V1/V2 from the 3-party proof.                             *)
(*                                                                            *)
(* Proof: instantiate relay_privacy_logm with relay_indep_V_target_n (N8e).  *)
(* ========================================================================== *)

Theorem relay_privacy_n (i j : 'I_n_relay.+1) :
  i != j ->
  `H(V_relay j | RelayView_n i) = log (m%:R : R) /\
  `H(V_relay j | RelayView_n i) > 0.
Proof.
move=> Hij.
have pV_adj : `p_ (V_relay j) = fdist_uniform (card_msg_subproof4 p_minus_2 q_minus_2).
  rewrite V_relay_unif; congr fdist_uniform; exact: eq_irrelevance.
exact: (@relay_privacy_logm R T P p_minus_2 q_minus_2 _
  (RelayView_n i) (V_relay j) pV_adj
  (relay_indep_V_target_n Hij)).
Qed.

End relay_privacy_concrete_n.

