From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap matrix lra reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import extra_proba entropy_fiber.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* Entropy Framework for Fibers over Composite Modulus Z/pqZ                  *)
(*                                                                            *)
(* This file provides general entropy lemmas for reasoning about conditional  *)
(* probabilities and entropy when random variables are constrained by linear  *)
(* equations over the ring Z/(pq)Z where p, q are distinct primes.            *)
(*                                                                            *)
(* Parallel to the abstract entropy_fiber.v but specialized for the ring      *)
(* structure of Z/pqZ. Key difference from field case: invertibility requires *)
(* coprimality condition rather than simple non-zero.                         *)
(*                                                                            *)
(* Main lemmas:                                                               *)
(*   Pr_cond_fiber_marginE:                                                   *)
(*     Pr[CondRV=c] = |fiber(c)| × (m²)^-1 × Pr[InputRV=proj(c)]              *)
(*     Marginal probability expressed in terms of fiber cardinality           *)
(*                                                                            *)
(*   cPr_uniform_fiber:                                                       *)
(*     Pr[VarRV=v | CondRV=c] = |fiber(c)|^-1                                 *)
(*     Uniform conditional probability over fiber from uniform prior          *)
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

Section fiber_entropy_zpq.

Context {R : realType}.
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Hypothesis prime_p : prime p.
Hypothesis prime_q : prime q.
Hypothesis coprime_pq : coprime p q.
Local Notation m := (p * q).
Local Notation msg := 'Z_m.

Variable T : finType.
Variable P : R.-fdist T.

(* Random variables *)
Variable VarRV : {RV P -> msg * msg}.
Variables (InputT : finType).
Variable InputRV : {RV P -> InputT}.
Variables (CondT : finType).
Variable CondRV : {RV P -> CondT}.

(* Fiber: the set of (v2,v3) satisfying the constraint for a given condition *)
Variable fiber : CondT -> {set msg * msg}.

(* Projection from CondT to InputT - extracts the input part of a condition *)
Variable proj_input : CondT -> InputT.

(* The constraint holds: VarRV t is always in the fiber of CondRV t *)
Hypothesis constraint_fiber : forall t, VarRV t \in fiber (CondRV t).

(* InputRV is the projection of CondRV *)
Hypothesis InputRV_proj : forall t, InputRV t = proj_input (CondRV t).

(* Cardinality constants *)
Let card_msg : #|msg| = m.
Proof. by rewrite card_ord Zp_cast. Qed.

Let card_msg_pair : #|((msg * msg)%type : finType)| = (m ^ 2)%N.
Proof. by rewrite card_prod !card_msg expnS expn1. Qed.

(* Assumptions: VarRV is uniform and independent of InputRV *)
Hypothesis VarRV_uniform : `p_ VarRV = fdist_uniform card_msg_pair.
Hypothesis VarRV_indep_inputs : P |= InputRV _|_ VarRV.

(* Joint probability factors by independence *)
Lemma joint_factors_by_indeE (input : InputT) (var : msg * msg) :
  `Pr[[%VarRV, InputRV] = (var, input)] =
  `Pr[VarRV = var] * `Pr[InputRV = input].
Proof.
have Hinde_sym: P |= VarRV _|_ InputRV.
  by rewrite inde_RV_sym.
move: Hinde_sym.
rewrite /inde_RV.
move=> /(_ var input).
by [].
Qed.

(* Uniform VarRV gives probability (m²)^-1 *)
Lemma uniform_VarRV_probE (var : msg * msg) :
  `Pr[VarRV = var] = (m ^ 2)%:R^-1 :> R.
Proof.
rewrite -dist_of_RVE VarRV_uniform fdist_uniformE.
by rewrite card_msg_pair.
Qed.

Section marginal_probability.

(* Hypothesis: joint probability equals when constrained *)
Hypothesis joint_eq_input :
  forall (cond : CondT) (var : msg * msg),
    var \in fiber cond ->
    `Pr[[%VarRV, CondRV] = (var, cond)] =
    `Pr[[%VarRV, InputRV] = (var, proj_input cond)].

(** Marginal probability over fiber.
    
    Pr[CondRV = cond] = |fiber(cond)| × (m²)^-1 × Pr[InputRV = proj_input(cond)]
    
    This expresses the marginal probability of the conditioning event
    as a product of:
    1. The fiber cardinality (number of solutions)
    2. The uniform probability (m²)^-1 for each solution
    3. The probability of the input values
*)
Lemma Pr_cond_fiber_marginE (cond : CondT) :
  `Pr[InputRV = proj_input cond] != 0 ->
  `Pr[CondRV = cond] =
  #|fiber cond|%:R * (m ^ 2)%:R^-1 * `Pr[InputRV = proj_input cond].
Proof.
(* Goal: Pr[CondRV=cond] = |fiber| × (m²)^-1 × Pr[InputRV=...] *)
move=> HInputRV_neq0.

(* Step 1: Marginalize Pr[CondRV] = Σ_vv Pr[VarRV=vv, CondRV=...] *)
have Hmargin: `Pr[CondRV = cond] =
  \sum_(vv : msg * msg) `Pr[[%VarRV, CondRV] = (vv, cond)].
  have ->: \sum_(vv : msg * msg) `Pr[[%VarRV, CondRV] = (vv, cond)] =
           \sum_(vv : msg * msg) `Pr[[%CondRV, VarRV] = (cond, vv)].
    apply eq_bigr => vv _.
    by rewrite pfwd1_pairC.
  by rewrite -(@PrX_fstRV _ _ _ _ P CondRV VarRV).

rewrite Hmargin.

(* Step 2: Split sum - only fiber elements contribute *)
rewrite (bigID (fun vv => vv \in fiber cond)) /=.

(* Terms outside fiber are 0 *)
have Hzero: \sum_(vv | vv \notin fiber cond)
            `Pr[[%VarRV, CondRV] = (vv, cond)] = 0.
  apply big1 => [[v2' v3']] Hnotin.
  rewrite pfwd1_eq0 //.
  rewrite mem_undup.
  apply/mapP.
  move=> [t0 _ /= Heq].
  (* Heq : (VarRV t0, CondRV t0) = ((v2', v3'), cond) *)
  case: Heq => Hvar Hcond.
  (* constraint_fiber: VarRV t0 \in fiber (CondRV t0) *)
  move: (constraint_fiber t0).
  rewrite -Hcond -Hvar.
  move=> Hin_fiber.
  by move/negP: Hnotin; apply.
rewrite Hzero addr0.

(* Step 3: Each fiber term = (m²)^-1 × Pr[InputRV] *)
transitivity (\sum_(vv in fiber cond)
              (m ^ 2)%:R^-1 * `Pr[InputRV = proj_input cond]).
  apply eq_bigr => [[v2' v3']] Hin.
  rewrite (joint_eq_input Hin).
  rewrite joint_factors_by_indeE.
  rewrite uniform_VarRV_probE.
  by [].

(* Step 4: Factor out constants *)
rewrite big_const iter_addr addr0.
by ring.
Qed.

End marginal_probability.

Section conditional_probability.

(* Hypothesis: joint probability equals when constrained *)
Hypothesis joint_eq_input :
  forall (cond : CondT) (var : msg * msg),
    var \in fiber cond ->
    `Pr[[%VarRV, CondRV] = (var, cond)] =
    `Pr[[%VarRV, InputRV] = (var, proj_input cond)].

(** Uniform conditional probability over fiber.
    
    Pr[VarRV = v | CondRV = cond] = |fiber(cond)|^-1
    
    When:
    1. VarRV is uniform over msg × msg
    2. VarRV is independent of InputRV
    3. The conditioning event has positive probability
    4. v is in the fiber of cond
    
    This is the key lemma for deriving entropy bounds in protocols
    where the constraint creates a fiber structure.
*)
Lemma cPr_uniform_fiber (cond : CondT) (v : msg * msg) :
  `Pr[CondRV = cond] != 0 ->
  v \in fiber cond ->
  `Pr[VarRV = v | CondRV = cond] = #|fiber cond|%:R^-1.
Proof.
(* Goal: Pr[VarRV=v | CondRV=cond] = |fiber|^-1 *)
move=> HCond_neq0 Hin_fiber.

(* Step 1: Expand conditional probability as quotient *)
rewrite cpr_eqE.

(* Step 2: Check fiber is non-empty *)
have Hfiber_nempty: (0 < #|fiber cond|)%N.
  apply/card_gt0P.
  exists v.
  exact Hin_fiber.

(* Step 3: Compute InputRV probability - need non-zero *)
have HInputRV_neq0: `Pr[InputRV = proj_input cond] != 0.
  move/pfwd1_neq0: HCond_neq0 => [t' [Ht'_cond Ht'_pos]].
  apply/pfwd1_neq0.
  exists t'.
  split => //.
  move: Ht'_cond.
  rewrite !inE.
  move/eqP => Hcond_eq.
  apply/eqP.
  (* InputRV t' = proj_input cond *)
  (* Use InputRV_proj: InputRV t' = proj_input (CondRV t') *)
  rewrite InputRV_proj.
  by rewrite Hcond_eq.

(* Step 4: Compute numerator *)
have Hnum: `Pr[[%VarRV, CondRV] = (v, cond)] =
           (m ^ 2)%:R^-1 * `Pr[InputRV = proj_input cond].
  rewrite (joint_eq_input Hin_fiber).
  rewrite joint_factors_by_indeE.
  rewrite uniform_VarRV_probE.
  by [].

(* Step 5: Compute denominator *)
have Hdenom: `Pr[CondRV = cond] =
             #|fiber cond|%:R * (m ^ 2)%:R^-1 *
             `Pr[InputRV = proj_input cond].
  by apply Pr_cond_fiber_marginE.

(* Step 6: Substitute and simplify *)
rewrite Hnum Hdenom.
field.
apply/and4P.
split.
- by rewrite pnatr_eq0 -lt0n.
- rewrite -natrD.
  by rewrite pnatr_eq0.
- rewrite -natrD.
  by rewrite pnatr_eq0.
- exact HInputRV_neq0.
Qed.

End conditional_probability.

End fiber_entropy_zpq.
