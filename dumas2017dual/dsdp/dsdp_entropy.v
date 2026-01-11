From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap matrix lra reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter smc_tactics.
Require Import smc_proba homomorphic_encryption entropy_fiber.
Require Import dsdp_program dsdp_extra dsdp_algebra.
Require Import fiber_zpq.

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

(*
  CRT Reconstruction Section
  ==========================
  
  This section formalizes the DSDP protocol over composite modulus Z/pqZ
  instead of prime field F_m. The key insight from CRT is:
  
    Z/pqZ ≅ Z/pZ × Z/qZ  (when gcd(p,q) = 1)
  
  For the constraint u2*v2 + u3*v3 = target:
    - 1 equation, 2 unknowns → 1 degree of freedom
    - Over Z/p: p solutions
    - Over Z/q: q solutions  
    - Over Z/pq: p × q = pq solutions (via CRT product rule)
  
  Security condition: U3 < min(p,q) ensures U3 is invertible in both
  Z/p and Z/q (since it can't be divisible by either prime).
*)
Section dsdp_entropy_zpq.

Context {R : realType}.
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Hypothesis prime_p : prime p.
Hypothesis prime_q : prime q.
Hypothesis coprime_pq : coprime p q.
Local Notation m := (p * q).
(* Use Zp ring structure for composite modulus arithmetic *)
Local Notation msg := 'Z_m.

(* Fiber over composite modulus: solutions to u2*v2 + u3*v3 = target in Z/pqZ *)
(* Note: This is the same as fiber_zpq_pair in fiber_zpq.v,
   kept local for clarity *)
Let dsdp_fiber_zpq (u2 u3 target : msg) : {set msg * msg} :=
  [set vv : msg * msg | (u2 * vv.1 + u3 * vv.2 == target)%R].

(* Fiber from full constraint: s - u1*v1 = u2*v2 + u3*v3 *)
Definition dsdp_fiber_full_zpq (u1 u2 u3 v1 s : msg) : {set msg * msg} :=
  dsdp_fiber_zpq u2 u3 (s - u1 * v1)%R.

Variable T : finType.
Variable P : R.-fdist T.
Variables (V1 V2 V3 U1 U2 U3 S : {RV P -> msg}).
Let CondRV : {RV P -> (msg * msg * msg * msg * msg)} :=
  [% V1, U1, U2, U3, S].
Let VarRV : {RV P -> (msg * msg)} := [%V2, V3].

Let card_msg : #|msg| = m.
Proof. by rewrite card_ord Zp_cast. Qed.

Let card_msg_pair : #|((msg * msg)%type : finType)| = (m ^ 2)%N.
Proof. by rewrite card_prod !card_msg expnS expn1. Qed.

Definition satisfies_constraint_zpq (cond : msg * msg * msg * msg * msg)
  (var : msg * msg) : Prop :=
  let '(v1, u1, u2, u3, s) := cond in
  let '(v2, v3) := var in
  (s - u1 * v1 = u2 * v2 + u3 * v3)%R.

Hypothesis constraint_holds :
  forall t, satisfies_constraint_zpq (CondRV t) (VarRV t).

(* 
   Security condition for fiber_zpq_pair_card:
   - (0 < u3)%N: u3 is positive
   - (u3 < minn p q)%N: u3 < min(p,q)
   
   These conditions ensure u3 is coprime to both p and q, hence invertible
   in Z/p and Z/q. This is sufficient for CRT decomposition.
   
   The conditions are passed as explicit parameters to lemmas rather than
   section hypotheses to make dependencies clear.
*)

(* Fiber cardinality follows from fiber_zpq_pair_card in fiber_zpq.v *)

(* Cryptographic assumptions for DSDP security:
   1. VarRV = (V2, V3) is uniformly distributed over msg × msg
   2. VarRV is independent of the inputs (V1, U1, U2, U3)
   These are standard assumptions in secure multi-party computation. *)
Hypothesis VarRV_uniform : `p_ VarRV = fdist_uniform card_msg_pair.
Hypothesis VarRV_indep_inputs : P |= [%V1, U1, U2, U3] _|_ VarRV.

(* ========================================================================= *)
(*         Section: Uniform over solutions from joint uniform prior          *)
(* ========================================================================= *)

Section uniform_from_joint_uniform.

(*
=== MATHEMATICAL PROOF STRATEGY ===

Statement: 
  Given VarRV is uniform over msg×msg with 1/m² and independent of [V1,U1,U2,U3],
  for any (v2,v3) in the fiber, the conditional probability equals 1/|fiber|.

Why it's true:
  1. Conditional probability = Pr[joint] / Pr[condition]
  2. Numerator: Pr[VarRV=(v2,v3), CondRV=cond] 
     Since constraint determines S from (v1,u1,u2,u3,v2,v3), this equals:
     Pr[VarRV=(v2,v3), [%V1,U1,U2,U3]=(v1,u1,u2,u3)]
     By independence: = Pr[VarRV=(v2,v3)] × Pr[[%V1,U1,U2,U3]=(v1,u1,u2,u3)]
     By uniform: = (m²)^-1 × Pr[[%V1,U1,U2,U3]=(v1,u1,u2,u3)]
  3. Denominator: Pr[CondRV=cond] = sum over fiber of numerator-type terms
     = |fiber| × (m²)^-1 × Pr[[%V1,U1,U2,U3]=(v1,u1,u2,u3)]
  4. Result: Numerator / Denominator = 1 / |fiber|

Required lemmas:
  - cpr_eqE: conditional probability as quotient
  - inde_RV_sym: independence symmetry  
  - pfwd1E, pfwd1_pairA, etc.: joint probability manipulation
  - fdist_uniformE: uniform distribution gives 1/card

===================================
*)

(* Abbreviation for [%V1, U1, U2, U3] - the inputs independent of VarRV *)
Let InputRV : {RV P -> (msg * msg * msg * msg)} := [%V1, U1, U2, U3].

(* Helper 1: Joint probability [%VarRV, InputRV] factors by independence *)
Lemma joint_factors_by_inde :
  P |= InputRV _|_ VarRV ->
  forall v1 u1 u2 u3 v2 v3,
    `Pr[[%VarRV, InputRV] = ((v2, v3), (v1, u1, u2, u3))] =
    `Pr[VarRV = (v2, v3)] * `Pr[InputRV = (v1, u1, u2, u3)].
Proof.
(* Goal: joint factors using independence *)
move=> Hinde v1 u1 u2 u3 v2 v3.
(* Use independence symmetry: InputRV _|_ VarRV -> VarRV _|_ InputRV *)
have Hinde_sym: P |= VarRV _|_ InputRV.
  by apply/inde_RV_sym.
(* Apply independence definition *)
move: Hinde_sym.
rewrite /inde_RV.
move=> /(_ (v2, v3) (v1, u1, u2, u3)).
by [].
Qed.

(* Helper 2: Uniform VarRV gives probability (m²)^-1 *)
Lemma uniform_VarRV_prob :
  `p_ VarRV = fdist_uniform card_msg_pair ->
  forall v2 v3, `Pr[VarRV = (v2, v3)] = (m ^ 2)%:R^-1 :> R.
Proof.
(* Goal: uniform distribution gives 1/m² *)
move=> Hunif v2 v3.
rewrite -dist_of_RVE Hunif fdist_uniformE.
by rewrite card_msg_pair.
Qed.

(* Helper 3: The joint [%VarRV, CondRV] probability equals [%VarRV, InputRV]
   when (v2,v3) is in the fiber (constraint is satisfied) *)
Lemma joint_VarRV_CondRV_eq_InputRV (v1 u1 u2 u3 s v2 v3 : msg) :
  (v2, v3) \in dsdp_fiber_full_zpq u1 u2 u3 v1 s ->
  `Pr[[%VarRV, CondRV] = ((v2, v3), (v1, u1, u2, u3, s))] =
  `Pr[[%VarRV, InputRV] = ((v2, v3), (v1, u1, u2, u3))].
Proof.
(* Goal: joint probabilities are equal when constraint holds *)
move=> Hin_fiber.
(* Both sides count the same events because S is determined by the constraint *)
rewrite !pfwd1E.
congr Pr.
apply/setP => t0.
rewrite !inE /= !xpair_eqE.
(* LHS: [&& VarRV_eq, InputRV_eq & S_eq] 
   RHS: [&& VarRV_eq, (V1&U1&U2)_eq & U3_eq]
   The constraint determines S, so LHS <-> RHS *)
apply/idP/idP => H.
- (* LHS -> RHS: drop S and rearrange *)
  move/and3P: H => [Hvar Hinput Hs].
  (* Hinput is ((V1 == v1) && (U1 == u1) && (U2 == u2)) && (U3 == u3) *)
  move/andP: Hinput => [Hinput3 Hu3].
  (* Hinput3 is ((V1 == v1) && (U1 == u1)) && (U2 == u2) *)
  move/andP: Hinput3 => [Hinput2 Hu2].
  (* Hinput2 is (V1 == v1) && (U1 == u1) *)
  move/andP: Hinput2 => [Hv1 Hu1].
  apply/and3P.
  split => //.
  (* Rebuild V1&U1&U2 *)
  by rewrite Hv1 Hu1 Hu2.
- (* RHS -> LHS: derive S=s from constraint *)
  move/and3P: H => [Hvar Hinput3 Hu3].
  (* Hinput3 is ((V1 == v1) && (U1 == u1)) && (U2 == u2) *)
  move/andP: Hinput3 => [Hinput2 Hu2].
  move/andP: Hinput2 => [Hv1 Hu1].
  apply/and3P.
  split => //.
  + (* Reconstruct V1&U1&U2&U3 *)
    by rewrite Hv1 Hu1 Hu2 Hu3.
  + (* S t0 = s follows from the constraint *)
    move/andP: Hvar => [/eqP Hv2_eq /eqP Hv3_eq].
    move/eqP: Hv1 => Hv1_eq.
    move/eqP: Hu1 => Hu1_eq.
    move/eqP: Hu2 => Hu2_eq.
    move/eqP: Hu3 => Hu3_eq.
    (* From constraint_holds: S t0 - U1 t0 * V1 t0 = U2 t0 * V2 t0 + U3 t0 * V3 t0 *)
    move: (constraint_holds t0).
    rewrite /satisfies_constraint_zpq /CondRV /VarRV /=.
    rewrite Hv1_eq Hu1_eq Hu2_eq Hu3_eq Hv2_eq Hv3_eq.
    move=> Hconstr.
    (* Hin_fiber: u2*v2 + u3*v3 = s - u1*v1 *)
    move: Hin_fiber.
    rewrite /dsdp_fiber_full_zpq /dsdp_fiber_zpq inE /=.
    move=> /eqP Hfiber_eq.
    apply/eqP.
    (* S t0 = s: from S t0 - u1*v1 = u2*v2 + u3*v3 = s - u1*v1 *)
    have Heq: S t0 - u1 * v1 = s - u1 * v1.
      by rewrite Hconstr Hfiber_eq.
    (* Add u1*v1 to both sides: S t0 - u1*v1 + u1*v1 = s - u1*v1 + u1*v1 *)
    (* i.e., S t0 = s *)
    by move: Heq => /(f_equal (fun x => x + u1 * v1)); rewrite !subrK.
Qed.

(* Helper 4: Denominator computation - sum over fiber *)
Lemma cond_prob_denom (v1 u1 u2 u3 s : msg) :
  P |= InputRV _|_ VarRV ->
  `p_ VarRV = fdist_uniform card_msg_pair ->
  `Pr[InputRV = (v1, u1, u2, u3)] != 0 ->
  `Pr[CondRV = (v1, u1, u2, u3, s)] =
  #|dsdp_fiber_full_zpq u1 u2 u3 v1 s|%:R * (m ^ 2)%:R^-1 *
  `Pr[InputRV = (v1, u1, u2, u3)].
Proof.
(* Goal: Pr[CondRV=cond] = |fiber| × (m²)^-1 × Pr[InputRV=...] *)
move=> Hinde Hunif HInputRV_neq0.

(* Step 1: Marginalize Pr[CondRV] = Σ_vv Pr[VarRV=vv, CondRV=...] *)
(* Use the standard marginalization: Pr[Y = y] = Σ_x Pr[X=x, Y=y] *)
have Hmargin: `Pr[CondRV = (v1, u1, u2, u3, s)] =
  \sum_(vv : msg * msg) `Pr[[%VarRV, CondRV] = (vv, (v1, u1, u2, u3, s))].
  (* Rewrite RHS using pfwd1_pairC to match standard form *)
  have ->: \sum_(vv : msg * msg) `Pr[[%VarRV, CondRV] = (vv, (v1, u1, u2, u3, s))] =
           \sum_(vv : msg * msg) `Pr[[%CondRV, VarRV] = ((v1, u1, u2, u3, s), vv)].
    apply: eq_bigr => vv _.
    by rewrite pfwd1_pairC.
  (* Now use PrX_fstRV with CondRV as first component *)
  by rewrite -(@PrX_fstRV _ _ _ _ P CondRV VarRV).

rewrite Hmargin.

(* Step 2: Split sum - only fiber elements contribute *)
rewrite (bigID (fun vv => vv \in dsdp_fiber_full_zpq u1 u2 u3 v1 s)) /=.

(* Terms outside fiber are 0 *)
have Hzero: \sum_(vv | vv \notin dsdp_fiber_full_zpq u1 u2 u3 v1 s)
            `Pr[[%VarRV, CondRV] = (vv, (v1, u1, u2, u3, s))] = 0.
  apply: big1 => [[v2' v3']] Hnotin.
  (* Use pfwd1_eq0 with proof that value is not in image *)
  rewrite pfwd1_eq0 //.
  (* Goal: (v2', v3', cond) \notin fin_img [%VarRV, CondRV] *)
  rewrite mem_undup.
  apply/mapP.
  (* Assume there exists t0 with [%VarRV,CondRV] t0 = (v2',v3',cond), derive contradiction *)
  move=> [t0 _ Heq].
  move: Heq => [Hv2' Hv3' Hv1' Hu1' Hu2' Hu3' Hs'].
  (* From constraint: S t0 - U1*V1 = U2*V2 + U3*V3 *)
  move: (constraint_holds t0).
  rewrite /satisfies_constraint_zpq /CondRV /VarRV /=.
  (* Substitute: v2' = V2 t0, etc. using -Hx' *)
  rewrite -Hv1' -Hu1' -Hu2' -Hu3' -Hv2' -Hv3' -Hs'.
  move=> Hconstr.
  (* Hconstr: s - u1*v1 = u2*v2' + u3*v3' means (v2',v3') is in fiber *)
  move/negP: Hnotin; apply.
  rewrite /dsdp_fiber_full_zpq /dsdp_fiber_zpq inE /=.
  by apply/eqP; rewrite -Hconstr.
rewrite Hzero addr0.

(* Step 3: Each fiber term = (m²)^-1 × Pr[InputRV] *)
transitivity (\sum_(vv in dsdp_fiber_full_zpq u1 u2 u3 v1 s)
              (m ^ 2)%:R^-1 * `Pr[InputRV = (v1, u1, u2, u3)]).
  apply: eq_bigr => [[v2' v3']] Hin.
  rewrite (joint_VarRV_CondRV_eq_InputRV Hin).
  rewrite (joint_factors_by_inde Hinde).
  rewrite (uniform_VarRV_prob Hunif).
  by [].

(* Step 4: Factor out constants *)
rewrite big_const iter_addr addr0.
by ring.
Qed.

(** Main bridge lemma: derive uniform-over-solutions from joint-uniform prior
    and independence.
    
    Mathematical reasoning:
    - Assumption: (V2,V3) is uniform over msg×msg with distribution 1/m²
    - Assumption: (V2,V3) is independent of (V1,U1,U2,U3)
    - The constraint S = u1*v1 + u2*v2 + u3*v3 determines S given the others
    
    For (v2,v3) in the fiber {(v2',v3') | u2*v2' + u3*v3' = s - u1*v1}:
    
    Numerator: Pr[(V2,V3)=(v2,v3) ∧ (V1,U1,U2,U3)=(v1,u1,u2,u3)]
             = Pr[(V2,V3)=(v2,v3)] × Pr[(V1,U1,U2,U3)=(v1,u1,u2,u3)]  (indep)
             = (1/m²) × Pr[(V1,U1,U2,U3)=(v1,u1,u2,u3)]
    
    Denominator: Pr[CondRV=(v1,u1,u2,u3,s)]
               = Σ_{(v2',v3') ∈ fiber} (1/m²) × Pr[(V1,U1,U2,U3)=...]
               = |fiber|/m² × Pr[(V1,U1,U2,U3)=(v1,u1,u2,u3)]
    
    Result: Numerator/Denominator = 1/|fiber|
*)
Lemma dsdp_uniform_over_solutions_from_joint_uniform :
  `p_ VarRV = fdist_uniform card_msg_pair ->
  P |= [%V1, U1, U2, U3] _|_ VarRV ->
  forall t v1 u1 u2 u3 s,
    U1 t = u1 -> U2 t = u2 -> U3 t = u3 ->
    V1 t = v1 -> S t = s ->
    (* The conditioning event must have positive probability for 
       the conditional probability to be well-defined *)
    `Pr[CondRV = (v1, u1, u2, u3, s)] != 0 ->
    forall v2 v3,
      (v2, v3) \in dsdp_fiber_full_zpq u1 u2 u3 v1 s ->
      `Pr[ VarRV = (v2, v3) | CondRV = (v1, u1, u2, u3, s) ] =
      (#|dsdp_fiber_full_zpq u1 u2 u3 v1 s|)%:R^-1.
Proof.
(* Goal: Pr[VarRV=(v2,v3) | CondRV=cond] = |fiber|^-1 *)
move=> Hunif Hinde t v1 u1 u2 u3 s HU1 HU2 HU3 HV1 HS HCond_neq0 v2 v3 Hin_fiber.
(* Step 1: Expand conditional probability as quotient *)
rewrite cpr_eqE.
(* Goal: Pr[[%VarRV, CondRV] = ...] / Pr[CondRV = ...] = |fiber|^-1 *)

(* Step 2: Check fiber is non-empty (t witnesses this) *)
have Hfiber_nempty: (0 < #|dsdp_fiber_full_zpq u1 u2 u3 v1 s|)%N.
  apply/card_gt0P.
  exists (v2, v3).
  exact: Hin_fiber.

(* Step 3: Compute InputRV probability - need non-zero *)
(* From HCond_neq0: Pr[CondRV = (v1,u1,u2,u3,s)] != 0, 
   we derive Pr[InputRV = (v1,u1,u2,u3)] != 0 since the InputRV event
   is a marginalization over S values. *)
have HInputRV_neq0: `Pr[InputRV = (v1, u1, u2, u3)] != 0.
  (* From HCond_neq0, there exists t' with CondRV t' = cond and P t' > 0 *)
  move/pfwd1_neq0: HCond_neq0 => [t' [Ht'_cond Ht'_pos]].
  (* Ht'_cond: t' \in CondRV @^-1 (v1,u1,u2,u3,s), i.e., CondRV t' = (v1,u1,u2,u3,s) *)
  (* This means InputRV t' = (v1,u1,u2,u3) *)
  apply/pfwd1_neq0.
  exists t'.
  split => //.
  (* t' \in InputRV @^-1 (v1, u1, u2, u3) *)
  move: Ht'_cond.
  rewrite !inE.
  (* Goal: CondRV t' == (v1,u1,u2,u3,s) -> InputRV t' == (v1,u1,u2,u3) *)
  move/eqP => [Hv1' Hu1' Hu2' Hu3' _].
  by apply/eqP; rewrite /= -Hv1' -Hu1' -Hu2' -Hu3'.

(* Step 4: Compute numerator using helpers *)
have Hnum: `Pr[[%VarRV, CondRV] = ((v2, v3), (v1, u1, u2, u3, s))] =
           (m ^ 2)%:R^-1 * `Pr[InputRV = (v1, u1, u2, u3)].
  rewrite (joint_VarRV_CondRV_eq_InputRV Hin_fiber).
  rewrite (joint_factors_by_inde Hinde).
  rewrite (uniform_VarRV_prob Hunif).
  by [].

(* Step 5: Compute denominator using helper *)
have Hdenom: `Pr[CondRV = (v1, u1, u2, u3, s)] =
             #|dsdp_fiber_full_zpq u1 u2 u3 v1 s|%:R * (m ^ 2)%:R^-1 *
             `Pr[InputRV = (v1, u1, u2, u3)].
  by apply: cond_prob_denom.

(* Step 6: Substitute and simplify *)
rewrite Hnum Hdenom.
(* Goal: (m²)^-1 * Pr[InputRV] / (|fiber| * (m²)^-1 * Pr[InputRV]) = |fiber|^-1 *)
field.
(* Need to show denominators are non-zero:
   [&& fiber_card != 0, q != 0, p != 0 & Pr[InputRV] != 0] *)
apply/and4P.
split.
- (* |fiber| != 0 *)
  by rewrite pnatr_eq0 -lt0n.
- (* 2 + q_minus_2%:R = q%:R != 0 since q >= 2 *)
  rewrite -natrD.
  by rewrite pnatr_eq0.
- (* 2 + p_minus_2%:R = p%:R != 0 since p >= 2 *)
  rewrite -natrD.
  by rewrite pnatr_eq0.
- (* Pr[InputRV] != 0 *)
  exact: HInputRV_neq0.
Qed.

End uniform_from_joint_uniform.

(* Fiber cardinality for full constraint *)
Lemma dsdp_fiber_full_zpq_card (u1 u2 u3 v1 s : msg) :
  (0 < u3)%N -> (u3 < minn p q)%N ->
  #|dsdp_fiber_full_zpq u1 u2 u3 v1 s| = m.
Proof.
move=> Hu3_pos Hu3_lt.
rewrite /dsdp_fiber_full_zpq /dsdp_fiber_zpq.
exact: (fiber_zpq_pair_card prime_p prime_q).
Qed.

(* Non-solutions have zero probability *)
Lemma dsdp_non_solution_zero_prob_zpq (u1 u2 u3 v1 s : msg) (v2 v3 : msg) :
  `Pr[CondRV = (v1, u1, u2, u3, s)] != 0 ->
  (v2, v3) \notin dsdp_fiber_full_zpq u1 u2 u3 v1 s ->
  `Pr[ VarRV = (v2, v3) | CondRV = (v1, u1, u2, u3, s) ] = 0.
Proof.
move=> Hcond_pos Hnot_solution.
(* Define constraint as fiber membership *)
set constraint := fun (conds : msg * msg * msg * msg * msg)
  (vals : msg * msg) =>
  let '(v1, u1, u2, u3, s) := conds in
  let '(v2, v3) := vals in
  (v2, v3) \in dsdp_fiber_full_zpq u1 u2 u3 v1 s.
have Hconstraint: forall t, constraint (CondRV t) (VarRV t).
  move=> t.
  rewrite /constraint /=.
  rewrite /dsdp_fiber_full_zpq /dsdp_fiber_zpq inE /=.
  apply/eqP.
  (* constraint_holds gives: s - u1*v1 = u2*v2 + u3*v3 *)
  (* We need: u2*v2 + u3*v3 = s - u1*v1 *)
  move: (constraint_holds t).
  rewrite /satisfies_constraint_zpq /CondRV /VarRV /=.
  by move=> ->.
by rewrite (cond_prob_zero_outside_constraint Hconstraint Hcond_pos).
Qed.

(* Solutions have uniform probability *)
Lemma dsdp_solution_uniform_prob_zpq (u1 u2 u3 v1 s : msg) (v2 v3 : msg) :
  (0 < u3)%N -> (u3 < minn p q)%N ->
  `Pr[CondRV = (v1, u1, u2, u3, s)] != 0 ->
  (v2, v3) \in dsdp_fiber_full_zpq u1 u2 u3 v1 s ->
  `Pr[ VarRV = (v2, v3) | CondRV = (v1, u1, u2, u3, s) ] = m%:R^-1.
Proof.
move=> Hu3_pos Hu3_lt Hcond_pos Hin.
(* From dsdp_uniform_over_solutions_from_joint_uniform and fiber cardinality *)
have Hcard: #|dsdp_fiber_full_zpq u1 u2 u3 v1 s| = m.
  by apply: dsdp_fiber_full_zpq_card.
(* Get witness from conditioning event being non-zero *)
move/pfwd1_neq0: (Hcond_pos) => [t [Ht _]].
move: Ht; rewrite inE => /eqP [HV1 HU1 HU2 HU3 HS].
rewrite (dsdp_uniform_over_solutions_from_joint_uniform 
           VarRV_uniform VarRV_indep_inputs HU1 HU2 HU3 HV1 HS Hcond_pos Hin).
by rewrite Hcard.
Qed.

(* Single-point conditional entropy: H[VarRV | CondRV = (v1,u1,u2,u3,s)]
   = log(m).
   Shows that for each fixed conditioning value, the conditional entropy
   equals log(m). This applies the general fiber entropy framework to DSDP:
   - Fiber = {(v2,v3) | u2*v2 + u3*v3 = s - u1*v1} has cardinality m
   - Uniform distribution over fiber implies entropy = log(m) *)
Lemma dsdp_entropy_uniform_subset_zpq (u1 u2 u3 v1 s : msg) :
  `Pr[ CondRV = (v1, u1, u2, u3, s)] != 0 ->
  (0 < u3)%N -> (u3 < minn p q)%N ->
  (forall pair : msg * msg,
    pair \in dsdp_fiber_full_zpq u1 u2 u3 v1 s ->
    `Pr[ VarRV = pair | CondRV = (v1, u1, u2, u3, s) ] = m%:R^-1) ->
  (forall pair : msg * msg,
    pair \notin dsdp_fiber_full_zpq u1 u2 u3 v1 s ->
    `Pr[ VarRV = pair | CondRV = (v1, u1, u2, u3, s) ] = 0) ->
  `H[ VarRV | CondRV = (v1, u1, u2, u3, s) ] = log (m%:R : R).
Proof.
move=> Hcond_pos Hu3_pos Hu3_lt Hsol_unif Hnonsol_zero.
(* Express conditional entropy as sum *)
have ->: `H[VarRV | CondRV = (v1, u1, u2, u3, s)] =
    - \sum_(pair : msg * msg)
     `Pr[VarRV = pair | CondRV = (v1, u1, u2, u3, s)] *
     log (`Pr[VarRV = pair | CondRV = (v1, u1, u2, u3, s)]).
  rewrite centropy1_RVE // /entropy.
  congr (- _); apply: eq_bigr => [[v2 v3]] _.
    by rewrite jfdist_cond_cPr_eq.
  by rewrite fst_RV2 dist_of_RVE.
(* Get cardinality *)
have card_m : #|dsdp_fiber_full_zpq u1 u2 u3 v1 s| = m.
  by apply: dsdp_fiber_full_zpq_card.
(* Adjust uniform hypothesis to match expected form *)
have Hsol_unif': forall pair : msg * msg,
    pair \in dsdp_fiber_full_zpq u1 u2 u3 v1 s ->
    `Pr[VarRV = pair | CondRV = (v1, u1, u2, u3, s)] = 
    #|dsdp_fiber_full_zpq u1 u2 u3 v1 s|%:R^-1.
  move=> pair Hin.
  rewrite (Hsol_unif pair Hin).
  by rewrite card_m.
rewrite (entropy_sum_split Hsol_unif' Hnonsol_zero).
rewrite card_m.
exact: entropy_uniform_set.
Qed.

(* Helper: Each conditioning value gives entropy log(m) *)
Lemma dsdp_centropy1_uniform_zpq (v1 u1 u2 u3 s : msg) :
  (0 < u3)%N -> (u3 < minn p q)%N ->
  `Pr[CondRV = (v1, u1, u2, u3, s)] != 0 ->
  `H[ VarRV | CondRV = (v1, u1, u2, u3, s) ] = log (m%:R : R).
Proof.
move=> Hu3_pos Hu3_lt Hcond_pos.
apply: dsdp_entropy_uniform_subset_zpq => //.
  move=> [v2 v3] Hpair.
  exact: dsdp_solution_uniform_prob_zpq.
move=> [v2 v3] Hpair.
exact: dsdp_non_solution_zero_prob_zpq.
Qed.

(* Main entropy result: H(V2, V3 | Alice's view) = log(pq) *)
(* This establishes that Alice learns nothing beyond the constraint. *)
Theorem dsdp_centropy_uniform_zpq :
  (forall t, (0 < U3 t)%N) ->
  (forall t, (U3 t < minn p q)%N) ->
  `H(VarRV | CondRV) = log (m%:R : R).
Proof.
move=> HU3_pos HU3_lt.
(* Expand conditional entropy as weighted sum *)
rewrite centropy_RVE' /=.
(* Transform each term in the sum *)
transitivity (\sum_(a : msg * msg * msg * msg * msg) 
               `Pr[ CondRV = a ] * log (m%:R : R)).
  (* Show each term equals Pr[...] * log(m) *)
  apply: eq_bigr => [] [] [] [] [] v1 u1 u2 u3 s H.
  have [->|Hcond_pos] := eqVneq (`Pr[CondRV = (v1, u1, u2, u3, s)]) 0.
    by rewrite !mul0r.
  (* Get u3 positivity from HU3_pos *)
  have Hu3_pos: (0 < u3)%N.
    move/pfwd1_neq0: Hcond_pos => [t [Ht _]].
    move: Ht; rewrite inE => /eqP Ht.
    have HU3t : U3 t = u3 by case: Ht => _ _ _ ->.
    by rewrite -HU3t; apply: HU3_pos.
  (* Get u3 < min(p,q) from HU3_lt *)
  have Hu3_lt: (u3 < minn p q)%N.
    move/pfwd1_neq0: Hcond_pos => [t [Ht _]].
    move: Ht; rewrite inE => /eqP Ht.
    have HU3t : U3 t = u3 by case: Ht => _ _ _ ->.
    by rewrite -HU3t; apply: HU3_lt.
  by rewrite (dsdp_centropy1_uniform_zpq Hu3_pos Hu3_lt Hcond_pos).
under eq_bigr do rewrite mulrC.
by rewrite -big_distrr /= sum_pfwd1 mulr1.
Qed.

Section dsdp_var_entropy_zpq.

(* m = p * q > 1 since p, q >= 2 *)
Let m_gt1 : (1 < m)%N.
Proof.
(* p >= 2, q >= 2, so p * q >= 4 > 1 *)
have Hp2: (1 < p)%N by [].
have Hq2: (1 < q)%N by [].
by rewrite (ltn_trans Hp2) // -{1}(muln1 p) ltn_pmul2l // ltnS.
Qed.

(* card_msg and card_msg_pair are inherited from outer section *)

(* Unconditional entropy of private inputs (V2, V3) when uniformly distributed.
   
   Since V2, V3 are private inputs from Bob and Charlie respectively,
   assuming uniform distribution gives H(V2,V3) = log(m²) = 2*log(m).
   
   Combined with the conditional entropy result H(V2,V3 | view) = log(m),
   this shows DSDP leaks log(m) bits but preserves log(m) bits of entropy.
   
   The security argument (privacy_by_bonded_leakage at end of file) shows
   that H(V2,V3 | AliceView) = H(V2 | AliceView), i.e., knowing V3 given
   the constraint adds no information beyond knowing V2. *)
Lemma dsdp_var_entropy_zpq :
  `p_VarRV = fdist_uniform card_msg_pair ->
  `H `p_VarRV = log (m%:R * m%:R : R).
Proof.
move->.
rewrite entropy_uniform card_prod !card_msg.
by rewrite natrM.
Qed.

End dsdp_var_entropy_zpq.

End dsdp_entropy_zpq.


(* For finite field (F_m) approach, see dsdp_entropy_field.v *)

Section dsdp_privacy_analysis.

Context {R : realType}.
Variable T : finType.
Variable P : R.-fdist T.

(* If A is const-RV actually P |= A _|_ A.
   But in the DSDP setting, we don't have such RVs.
*)
Hypothesis neg_self_indep : forall (TA : finType)
  (A : {RV P -> TA}), ~ P |= A _|_ A.

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

Let card_msg_pair : #|((msg * msg)%type : finType)| = (m ^ 2)%N.
Proof. by rewrite card_prod !card_msg expnS expn1. Qed.

Let enc := enc party msg.
Let pkey := pkey party msg.

Let data := (msg + enc + pkey)%type.
Let d x : data := inl (inl x).
Let e x : data := inl (inr x).
Let k x : data := inr x.

Notation "u *h w" := (Emul u w).
Notation "u ^h w" := (Epow u w).

(* Note: Trace-related entropy lemmas (DSDP_RV_zpq, AliceTraces,
   centropy_AliceTraces_AliceView) are defined in dsdp_entropy_trace.v
   for Z/pqZ analysis. For F_m based trace analysis, see
   dsdp_entropy_field.v. *)

Record dsdp_random_inputs :=
  DSDPRandomInputs {
    Dk_a : {RV P -> Alice.-key Dec msg};
    Dk_b : {RV P -> Bob.-key Dec msg};
    Dk_c : {RV P -> Charlie.-key Dec msg};

    V1 : {RV P -> msg};
    V2 : {RV P -> msg};
    V3 : {RV P -> msg};
    U1 : {RV P -> msg};
    U2 : {RV P -> msg};
    U3 : {RV P -> msg};
    R2 : {RV P -> msg};
    R3 : {RV P -> msg};

    alice_indep : P |= [% Dk_a, V1, U1, U2, U3, R2, R3] _|_ [%V2, V3];

    (* Alice's private input V1 is independent of her random protocol values.
       This models that V1 is Alice's pre-existing secret, while U1, U2, U3, R2, R3
       are freshly generated random values for the protocol. *)
    alice_V1_indep_randoms : P |= V1 _|_ [%U1, U2, U3, R2, R3];

    pV1_unif : `p_ V1 = fdist_uniform card_msg;
    pV2_unif : `p_ V2 = fdist_uniform card_msg;
    pV3_unif : `p_ V3 = fdist_uniform card_msg;
    pV2V3_unif : `p_ [% V2, V3] = fdist_uniform card_msg_pair;
    pU2_unif : `p_ U2 = fdist_uniform card_msg;
    pU3_unif : `p_ U3 = fdist_uniform card_msg;
    pR2_unif : `p_ R2 = fdist_uniform card_msg;
    pR3_unif : `p_ R3 = fdist_uniform card_msg;
}.

Variable inputs : dsdp_random_inputs.

Let Dk_a := Dk_a inputs.
Let Dk_b := Dk_b inputs.
Let Dk_c := Dk_c inputs.
Let V1 := V1 inputs.
Let V2 := V2 inputs.
Let V3 := V3 inputs.
Let U1 := U1 inputs.
Let U2 := U2 inputs.
Let U3 := U3 inputs.
Let R2 := R2 inputs.
Let R3 := R3 inputs.
Let VU2 : {RV P -> msg} := V2 \* U2.
Let VU3 : {RV P -> msg} := V3 \* U3.
Let D2  : {RV P -> msg} := VU2 \+ R2.
Let VU3R : {RV P -> msg} := VU3 \+ R3.
Let D3 : {RV P -> msg} := VU3R \+ D2.
Let S : {RV P -> msg} := D3 \- R2 \- R3 \+ U1 \* V1.

Let E_alice_d3 : {RV P -> Alice.-enc msg} := E' alice `o D3.
Let E_charlie_v3 : {RV P -> Charlie.-enc msg} := E' charlie `o V3.
Let E_bob_v2 : {RV P -> Bob.-enc msg} := E' bob `o V2.

(* Use these two and apply_inde_RV_comp to prove trivial indeps*)
Let alice_inputsT := (Alice.-key Dec msg * msg * msg * msg *
  msg * msg * msg)%type.
Let AliceInputsView : {RV P -> alice_inputsT} :=
  [% Dk_a, V1, U1, U2, U3, R2, R3].

(* Since `AliceInputView` are generated by Alice,
   while `v2` is generated by Bob *)
Hypothesis AliceInputsView_indep_V2 :
  P |= AliceInputsView _|_ V2.

Section alice_privacy_analysis.

(* E_charlie_v3 means it is encrypted (so generated) by the key of charlie.
   Therefore, encrypted RVs should be independent of other parties.
   Even other parties can add messages by HE properties, but addition to a RV
   means the independence keeps after the addition.
*)
Hypothesis inde_Echarlie : P |= AliceInputsView _|_ E_charlie_v3.
Hypothesis inde_Ebob : P |= AliceInputsView _|_ E_bob_v2.

Let alice_view_valuesT := (Alice.-key Dec msg * msg * msg * msg * msg * msg *
  msg * msg * Alice.-enc msg * Charlie.-enc msg * Bob.-enc msg)%type.

Let AliceView : {RV P -> alice_view_valuesT} :=
  [% Dk_a, S, V1, U1, U2, U3, R2, R3, E_alice_d3, E_charlie_v3, E_bob_v2].

(* Note: Trace-based lemmas (AliceTraces_from_viewP,
   AliceView_values_from_traceP, centropy_AliceTraces_AliceView) are not
   needed for Z/pqZ security analysis.
   They require dsdp_traces from dsdp_program.v which uses 'F_m.
   For trace-based analysis, see dsdp_entropy_field.v. *)

Local Definition Dec_view : {RV P -> (alice_inputsT * msg)} :=
  [% Dk_a, S, V1, U1, U2, U3, R2, R3].
Local Definition Eqn1_view :
  {RV P -> (alice_inputsT * msg * Alice.-enc msg * Charlie.-enc msg)}
  := [% Dec_view, E_alice_d3, E_charlie_v3].
Local Definition Eqn2_view :
  {RV P -> (alice_inputsT * msg * Alice.-enc msg)} :=
  [% Dec_view, E_alice_d3].
 
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

(* Since `AliceInputView` are generated by Alice,
   while `v2` is generated by Bob *)
Hypothesis AliceInputView_indep_V2 :
  P |= AliceInputsView _|_ V2.

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

(* S as function composition:
       S = f ∘ (U2,U3,V2,V3,V1,U1) where f computes the sum.
   Used for applying composition lemmas in entropy analysis. *)
Lemma S_compE :
  let f := (fun o => let '(u2, u3, v2, v3, v1, u1) := o
              in u2 * v2 + u3 * v3 + v1 * u1) in
  S = f `o [% U2, U3, V2, V3, V1, U1].
Proof.
rewrite /comp_RV /S /VS /US /D3 /VU3R /D2 /VU3 /VU2
  /VU1 /Dotp2_rv /dotp2 /add_RV.
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

Section semi_honest_case_analysis.

Section bonded_leakage_privacy.

(* Functional Determination of V3:
   
   The constraint s = u1*v1 + u2*v2 + u3*v3 creates a functional relationship:
   given all values except v3 (and assuming u3 is invertible), v3 is determined.
   
   For Z/pqZ (composite modulus m = p*q):
   - Invertibility condition: 0 < u3 < min(p,q) ensures u3 is coprime to m
   - Fiber cardinality: |{(v2,v3) | u2*v2 + u3*v3 = target}| = m
   - Proved directly in fiber_zpq.v using bijection argument
   
   Key insight: The entropy relationship

     H(V2, V3 | constraints) = H(V2 | constraints)

   holds because V3 adds no additional entropy once V2 and the constraint
   are known. This is a consequence of the constraint structure itself.
   
   See dsdp_entropy_zpq section for Z/pqZ entropy analysis.
   See dsdp_entropy_field.v for comparison with prime field F_m approach.
*)

Definition compute_v3 (o : (msg * msg * msg * msg * msg * msg)) : msg :=
  let '(v1_val, u1_val, u2_val, u3_val, s_val, v2_val) := o in
    (s_val - u2_val * v2_val - u1_val * v1_val) / u3_val.


Hypothesis U3_coprime_m :
  forall t, coprime (val (U3 t)) m.

(* If U3 gives zero, the adversary is not semi-honest,
   there fore this constraint fits the security model assumption.
*)
Lemma U3_nonzero : forall t, U3 t != 0.
Proof.
move=> t.
have Hcoprime := U3_coprime_m t.
case Hval: (val (U3 t)) => [|n] //.
(* If val = 0, derive contradiction from coprime 0 m *)
exfalso.
move: Hcoprime; rewrite Hval /coprime gcd0n => /eqP Hm1.
(* m = 1 but m = m_minus_2.+2 >= 2, contradiction *)
  by [].
apply/eqP => H.
move: Hval; rewrite H.
by [].
Qed.

(* V3 is functionally determined by the other variables via the constraint.
   Given V1, U1, U2, U3, S, V2, we can compute: V3 = (S - U2*V2 - U1*V1) / U3.
   This is key for showing H(V2,V3|constraint) = H(V2|constraint). 
   
   For Z/pqZ (ring, not field), we use:
   - U3 is a unit because coprime (val U3) m
   - Division by unit: x / y = x * y^-1
   - Inverse property: y^-1 * y = 1 when y is unit
*)
Lemma V3_determined : V3 = compute_v3 `o [% V1, U1, U2, U3, S, V2].
Proof.
(* Goal: V3 = compute_v3 `o [% V1, U1, U2, U3, S, V2] *)
rewrite S_compE /compute_v3 /comp_RV /=.
(* Goal: V3 = fun i => (S i - U2 i * V2 i - U1 i * V1 i) / U3 i *)
apply/boolp.funext => i /=.
(* Goal: V3 i = (U2*V2 + U3*V3 + V1*U1 - U2*V2 - U1*V1) / U3 i 
   Note: S i expanded to U2*V2 + U3*V3 + V1*U1 from S_compE *)

(* === Step 1: Show U3 i is a unit in 'Z_m === *)
have HU3_unit: (U3 i) \is a GRing.unit.
  (* U3 i : 'Z_m, need to show it's a unit *)
  (* Use: x \is unit in 'Z_m iff coprime m (val x) *)
  rewrite -[U3 i]natr_Zp unitZpE //.
  (* Goal: coprime m (val (U3 i)) *)
  by rewrite coprime_sym (U3_coprime_m i).

(* === Step 2: Simplify numerator to U3*V3 === *)
(* The numerator: U2*V2 + U3*V3 + V1*U1 - U2*V2 - U1*V1 = U3*V3 *)
have Hnum :
  U2 i * V2 i + U3 i * V3 i + V1 i * U1 i -
  U2 i * V2 i - U1 i * V1 i =
  U3 i * V3 i by ring.
rewrite Hnum.

(* === Step 3: Show V3 = U3*V3 / U3 using unit inverse property === *)
(* Goal: V3 i = U3 i * V3 i / U3 i *)
(* In comRing: U3 * V3 = V3 * U3, then V3 * U3 / U3 =
   V3 * (U3 / U3) = V3 * 1 = V3 *)
rewrite [U3 i * _]mulrC.
(* Goal: V3 i = V3 i * U3 i / U3 i *)
(* x * y / y = x * (y / y) = x * 1 = x *)
rewrite -mulrA.
(* Goal: V3 i = V3 i * (U3 i / U3 i) *)
rewrite divrr //.
(* Goal: V3 i = V3 i * 1 *)
by rewrite mulr1.
Qed.

(* TODO: put an assumption so the lemma
   V3_determined_centropy_v2 can be applied
   when the assumption is true.
*)

(** * Fundamental Principle of Constraint-Based Security
    
    When an auxiliary variable is functionally determined by a secret
    and a constraint, the joint entropy equals the secret's entropy alone.
    This formalizes the principle that "knowing possible solution pairs
    gives exactly the same information as knowing the constraint on the secret."
    
    This principle underlies many MPC protocols where:
    - [V2] is the secret to protect
    - [V3] is an auxiliary/helper variable
    - [S, U2, U3] form a constraint linking them
    - Given constraint, [v3] is determined by [V2] (or vice versa)
*)
Lemma V3_determined_centropy_v2 :
  `H([% V2, V3] | [% V1, U1, U2, U3, S]) = `H(V2 | [% V1, U1, U2, U3, S]).
Proof.
have ->: `H([% V2, V3] | [% V1, U1, U2, U3, S]) =
  `H([% V1, U1, U2, U3, S], [% V2, V3]) - `H `p_ [% V1, U1, U2, U3, S].
  by rewrite chain_rule_RV addrAC subrr add0r.
rewrite V3_determined.
have ->: `H([% V1, U1, U2, U3, S],
    [% V2, compute_v3 `o [% V1, U1, U2, U3, S, V2]]) =
  `H `p_[% V1, U1, U2, U3, S, V2].
  by rewrite joint_entropy_RVA joint_entropy_RV_comp.
have ->: `H( V2 | [% V1, U1, U2, U3, S]) =
  `H([% V1, U1, U2, U3, S], V2) - `H `p_ [% V1, U1, U2, U3, S].
  by rewrite chain_rule_RV addrAC subrr add0r.
by [].
Qed.

End bonded_leakage_privacy.

Hypothesis U3_coprime_m :
  forall t, coprime (val (U3 t)) m.

Let f := fun o :
  (Alice.-key Dec msg * msg * msg * msg * msg * msg * msg * msg) =>
    let '(dk_a, v1, u1, u2, u3, r2, r3, s) := o in
         ((dk_a, v1, u1, u2, u3, r2, r3), s). 

Let comp_aiv_dotp2:
  f `o [% Dk_a, V1, U1, U2, U3, R2, R3, Dotp2_rv VS US `+ VU1] =
    [% AliceInputsView, Dotp2_rv VS US `+ VU1].
Proof. rewrite /comp_RV. apply: boolp.funext => _ //=. Qed.

Hypothesis cinde_V2V3 :
  P |= [% Dk_a, R2, R3] _|_ [% V2, V3] | [% V1, U1, U2, U3, S].

Hypothesis cinde_V2 :
  P |= [% Dk_a, R2, R3] _|_ V2 | [% V1, U1, U2, U3, S].

Hypothesis V3_determined : 
  V3 = compute_v3 `o [% V1, U1, U2, U3, S, V2].

(* Generic helper: Strip encryptions from AliceView and apply conditional
   independence.
   Given: X is conditionally independent of [Dk_a, R2, R3] given CondRV
   Proves: H(X | AliceView) = H(X | CondRV)
   This is reused in dsdp_security.v for the bounded leakage proof. *)
Lemma alice_view_to_cond (A : finType) (Xvar : {RV P -> A}) :
  (P |= [% Dk_a, R2, R3] _|_ Xvar | [% V1, U1, U2, U3, S]) ->
  `H(Xvar | AliceView) = `H(Xvar | [% V1, U1, U2, U3, S]).
Proof.
move=> cinde_X.
rewrite /AliceView.
rewrite (E_enc_ce_removal Xvar card_msg); last exact: Pr_AliceView_neq0.
rewrite (E_enc_ce_removal Xvar card_msg); last exact: Pr_Eqn1View_neq0.
rewrite (E_enc_ce_removal Xvar card_msg); last exact: Pr_Eqn2View_neq0.
have H_reorder: `H(Xvar | [% Dk_a, S, V1, U1, U2, U3, R2, R3]) =
  `H(Xvar | [% Dk_a, R2, R3, V1, U1, U2, U3, S]).
  rewrite /centropy_RV /centropy /= !snd_RV2.
  rewrite (reindex (fun '(dk_a', r2', r3', v1', u1', u2', u3', s') => 
                    (dk_a', s', v1', u1', u2', u3', r2', r3')))/=.
    apply: eq_bigr => [] [] [] [] [] [] [] []
      dk_a' s' v1' u1' u2' u3' r2' r3' _.
    congr (_ * _).
         rewrite !dist_of_RVE !pfwd1E; congr Pr; apply/setP => u;
         rewrite !inE /= !xpair_eqE;
         rewrite -[andb]/GRing.mul; ring.
    rewrite /centropy1; congr (- _).
    rewrite /jcPr !snd_RV2.
    apply: eq_bigr => a _.
    rewrite /jcPr !setX1 !Pr_set1 !dist_of_RVE !pfwd1E.
    congr (_ * _).
      f_equal.
        by congr Pr; apply/setP => u; rewrite !inE /= !xpair_eqE;
           rewrite -[andb]/GRing.mul; ring.
      by f_equal; congr Pr; apply/setP => u;
         rewrite !inE /= !xpair_eqE; rewrite -[andb]/GRing.mul; ring.
    congr log.
      f_equal.
        by congr Pr; apply/setP => u; rewrite !inE /= !xpair_eqE;
           rewrite -[andb]/GRing.mul; ring.
      f_equal.
      by congr Pr; apply/setP => u; rewrite !inE /= !xpair_eqE;
         rewrite -[andb]/GRing.mul; ring.
    by exists (fun '(dk_a', s', v1', u1', u2', u3', r2', r3') =>
           (dk_a', r2', r3', v1', u1', u2', u3', s')) 
           => [] [] [] []  [] [] [] [] dk_a' v1' u1' r2' r3' u2' u3' s'.
rewrite H_reorder.
have H_assoc: `H(Xvar | [% Dk_a, R2, R3, V1, U1, U2, U3, S] ) =
    `H(Xvar | [% [% Dk_a, R2, R3], [% V1, U1, U2, U3, S]] ).
  rewrite /centropy_RV /centropy /= !snd_RV2.
  rewrite (reindex (fun '(o, (v1, u1, u2, u3, s)) =>
                    (o, v1, u1, u2, u3, s))) /=.
    apply: eq_bigr =>
      [] [] [] [] dk_a' r2' r3' [] [] [] [] v1' u1' u2' u3' s' _.
    congr (_ * _).
      rewrite !dist_of_RVE !pfwd1E.
      by congr Pr; apply/setP => u; rewrite !inE /= !xpair_eqE;
         rewrite -[andb]/GRing.mul; ring.
    rewrite /centropy1; congr (- _).
    rewrite /jcPr !snd_RV2.
    apply: eq_bigr => a _.
    rewrite /jcPr !setX1 !Pr_set1 !dist_of_RVE !pfwd1E.
    congr (_ * _).
      f_equal.
        by congr Pr; apply/setP => u; rewrite !inE /= !xpair_eqE;
           rewrite -[andb]/GRing.mul; ring.
      f_equal.
      by congr Pr; apply/setP => u; rewrite !inE /= !xpair_eqE;
         rewrite -[andb]/GRing.mul; ring.
    congr log.
    f_equal.
      by congr Pr; apply/setP => u; rewrite !inE /= !xpair_eqE;
         rewrite -[andb]/GRing.mul; ring.
    f_equal.
    by congr Pr; apply/setP => u; rewrite !inE /= !xpair_eqE;
       rewrite -[andb]/GRing.mul; ring.
  exists (fun '(o, v1, u1, u2, u3, s) =>
             (o, (v1, u1, u2, u3, s))).
  - by move=> [] o [] [] [] [] a1 a2 a3 a4 a5.
  - by move=> [] [] [] [] [] [] [] [] a1 a2 a3 a4 a5 o1 o2 o3.
rewrite H_assoc.
exact: (cinde_centropy_eq cinde_X).
Qed.

(* Privacy via bounded leakage: knowing (V2,V3) given Alice's view is
   equivalent to knowing just V2.
   V3 adds no additional information because it is determined by V2 and the
   constraint. This is the core privacy guarantee for Bob's input V2. *)
Lemma privacy_by_bonded_leakage :
  `H([% V2, V3] | AliceView ) = `H(V2 | AliceView).
Proof.
rewrite (alice_view_to_cond cinde_V2V3) (alice_view_to_cond cinde_V2).
apply: V3_determined_centropy_v2.
exact: U3_coprime_m.
Qed.

End semi_honest_case_analysis.

End alice_privacy_analysis.

End dsdp_privacy_analysis.


