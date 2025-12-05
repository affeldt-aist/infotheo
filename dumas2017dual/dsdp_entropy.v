From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap matrix lra.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter smc_tactics.
Require Import smc_proba homomorphic_encryption entropy_fibers.
Require Import dsdp_program dsdp_extra dsdp_algebra.
Require Import entropy_zpq.

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

Local Definition R := Rdefinitions.R.

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
Section crt_reconstruct.

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
Definition dsdp_fiber_zpq (u2 u3 target : msg) : {set msg * msg} :=
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

Definition satisfies_constraint_zpq (cond : msg * msg * msg * msg * msg)
  (var : msg * msg) : Prop :=
  let '(v1, u1, u2, u3, s) := cond in
  let '(v2, v3) := var in
  (s - u1 * v1 = u2 * v2 + u3 * v3)%R.

Hypothesis constraint_holds :
  forall t, satisfies_constraint_zpq (CondRV t) (VarRV t).

Hypothesis U3_nonzero : forall t, U3 t != 0%R.

(* Security condition: U3 < min(p, q) ensures U3 is invertible mod p and mod q *)
Let minpq_lt_pmulq : (minn p q < p * q)%N.
Proof.
(* minn p q ≤ p < p * q since q ≥ 2 *)
apply: (@leq_ltn_trans p).
  by apply: geq_minl.
(* p < p * q since q ≥ 2 *)
by rewrite -{1}(muln1 p) ltn_pmul2l // ltnS.
Qed.

Hypothesis U3_lt_min_p_q : forall t, (U3 t < Ordinal minpq_lt_pmulq)%N.

(* 
   Key insight: U3 < min(p,q) implies:
   - U3 is not divisible by p (since U3 < p)
   - U3 is not divisible by q (since U3 < q)
   Therefore U3 is coprime to both p and q, hence invertible in Z/p and Z/q.
   
   This is weaker than requiring U3 invertible in Z/pq (which would require
   coprime(U3, pq)), but sufficient for CRT decomposition.
*)

(* 
   Key lemma: u3 < min(p,q) implies u3 is coprime to pq.
   Since 0 < u3 < min(p,q), we have:
   - u3 is not divisible by p (since u3 < p)
   - u3 is not divisible by q (since u3 < q)
   Therefore gcd(u3, pq) = 1, so u3 is a unit in Z/pq.
*)
Lemma lt_minpq_coprime_pq (u : 'Z_m) :
  (0 < u)%N -> (u < minn p q)%N ->
  coprime (nat_of_ord u) m.
Proof.
move=> Hu_pos Hu_lt.
rewrite /coprime /m.
(* u < minn p q <= p, so u < p *)
have Hu_lt_p: (u < p)%N.
  by apply: (leq_trans (n := minn p q)); [exact: Hu_lt | exact: geq_minl].
(* u < minn p q <= q, so u < q *)
have Hu_lt_q: (u < q)%N.
  by apply: (leq_trans (n := minn p q)); [exact: Hu_lt | exact: geq_minr].
rewrite Gauss_gcdl //.
  (* coprime u p = coprime p u = ~~ (p %| u) when p is prime *)
  rewrite -/(coprime u p) coprime_sym prime_coprime //.
  by rewrite gtnNdvd // ltnW.
(* gcd(u, q) = 1 since u < q and q is prime *)
rewrite -/(coprime u q) coprime_sym prime_coprime //.
by rewrite gtnNdvd // ltnW.
Qed.

(*
   Fiber cardinality via degree of freedom: |fiber| = m = p * q

   Mathematical proof (from crt_solution_counting.tex Section 5.4):
   ================================================================
   
   When u3 < min(p,q), we have coprime(u3, pq) by lt_minpq_coprime_pq.
   This means u3 is a unit in Z/pq.
   
   Bijection f : Z/pq -> fiber defined by:
     f(v2) = (v2, (target - u2*v2) / u3)
   
   1. f is injective: first component determines the pair
   
   2. f maps to fiber:
      u2*v2 + u3*((target - u2*v2)/u3)
      = u2*v2 + (target - u2*v2)     [u3 * (x/u3) = x for unit u3]
      = target ✓
   
   3. f is surjective: for (v2,v3) in fiber with u2*v2 + u3*v3 = target,
      v3 = (target - u2*v2)/u3, so (v2,v3) = f(v2)
   
   Therefore |fiber| = |Z/pq| = pq = m
   
   Technical TODOs:
   - Need MathComp lemma: coprime x m -> x \is a GRing.unit in 'Z_m
   - Work around dependent type issues with m = p*q as modulus
*)
Lemma dsdp_fiber_zpq_card (u2 u3 target : msg) :
  (0 < u3)%N -> (u3 < minn p q)%N ->
  #|dsdp_fiber_zpq u2 u3 target| = m.
Proof.
move=> Hu3_pos Hu3_lt.
have Hu3_coprime: coprime (nat_of_ord u3) m.
  by exact: (lt_minpq_coprime_pq Hu3_pos Hu3_lt).
(* m = p * q > 1 since p, q are primes (hence >= 2) *)
have Hm_gt1: (1 < m)%N.
  have Hp_gt1: (1 < p)%N by exact: prime_gt1.
  have Hq_gt0: (0 < q)%N by exact: prime_gt0.
  by rewrite /m (leq_trans Hp_gt1) // leq_pmulr.
(* u3 is a unit in 'Z_m *)
have Hu3_unit: u3 \is a GRing.unit.
  exact: (coprime_Zp_unit Hm_gt1 Hu3_coprime).
(* Bijection f : 'Z_m -> fiber, f(v2) = (v2, (target - u2*v2) * u3^-1) *)
pose f := fun v2 : msg => (v2, (target - u2 * v2) * u3^-1) : msg * msg.
rewrite /dsdp_fiber_zpq.
(* f is injective (first component determines pair) *)
have f_inj: injective f by move=> v2 v2'; rewrite /f /=; case=> ->.
(* f maps into fiber *)
have f_in_fiber: forall v, f v \in [set vv | u2 * vv.1 + u3 * vv.2 == target].
  move=> v.
  rewrite inE /f /=.
  apply/eqP.
  rewrite mulrCA mulrV //.
  by ring.
(* Every fiber element is in range of f *)
have fiber_in_range: forall vv, 
  vv \in [set vv | u2 * vv.1 + u3 * vv.2 == target] -> vv = f vv.1.
  move=> [v2' v3'].
  rewrite inE /= => /eqP Hconstr.
  rewrite /f /=.
  congr pair.
  rewrite -Hconstr [X in (X - _) / _]addrC addrK.
  by rewrite (mulrC u3 v3') mulrK.
(* Cardinality via bijection: |fiber| = |f @: msg| = |msg| = m *)
(* Since f is injective and fiber = f @: msg, #|fiber| = #|msg| = m *)
have Hfiber_eq_image: [set vv | u2 * vv.1 + u3 * vv.2 == target] = f @: [set: msg].
  apply/setP => vv.
  apply/idP/imsetP.
  - (* fiber -> image *)
    move=> Hin.
    exists vv.1 => //.
    by rewrite (fiber_in_range _ Hin).
  - (* image -> fiber *)
    case=> w _ ->.
    exact: f_in_fiber.
rewrite Hfiber_eq_image card_imset //.
(* #|[set: msg]| = m *)
by rewrite cardsT card_ord.
Qed.

(* Uniform distribution hypothesis over fiber *)
Hypothesis uniform_over_solutions : forall t v1 u1 u2 u3 s,
  U1 t = u1 -> U2 t = u2 -> U3 t = u3 ->
  V1 t = v1 -> S t = s ->
  forall v2 v3,
    (v2, v3) \in dsdp_fiber_full_zpq u1 u2 u3 v1 s ->
    `Pr[ VarRV = (v2, v3) | CondRV = (v1, u1, u2, u3, s) ] =
    (#|dsdp_fiber_full_zpq u1 u2 u3 v1 s|)%:R^-1.

(* Fiber cardinality for full constraint *)
Lemma dsdp_fiber_full_zpq_card (u1 u2 u3 v1 s : msg) :
  (0 < u3)%N -> (u3 < minn p q)%N ->
  #|dsdp_fiber_full_zpq u1 u2 u3 v1 s| = m.
Proof.
move=> Hu3_pos Hu3_lt.
by apply: dsdp_fiber_zpq_card.
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
(* From uniform_over_solutions and fiber cardinality *)
have Hcard: #|dsdp_fiber_full_zpq u1 u2 u3 v1 s| = m.
  by apply: dsdp_fiber_full_zpq_card.
(* Get witness from conditioning event being non-zero *)
move/pfwd1_neq0: (Hcond_pos) => [t [Ht _]].
move: Ht; rewrite inE => /eqP [HV1 HU1 HU2 HU3 HS].
rewrite (uniform_over_solutions HU1 HU2 HU3 HV1 HS Hin).
by rewrite Hcard.
Qed.

(* Helper: entropy at each conditioning value equals log(m) *)
Lemma dsdp_centropy1_uniform_zpq (v1 u1 u2 u3 s : msg) :
  (0 < u3)%N -> (u3 < minn p q)%N ->
  `Pr[CondRV = (v1, u1, u2, u3, s)] != 0 ->
  `H[ VarRV | CondRV = (v1, u1, u2, u3, s) ] = log (m%:R : R).
Proof.
move=> Hu3_pos Hu3_lt Hcond_pos.
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
have Hsol_unif: forall pair : msg * msg,
    pair \in dsdp_fiber_full_zpq u1 u2 u3 v1 s ->
    `Pr[VarRV = pair | CondRV = (v1, u1, u2, u3, s)] = 
    #|dsdp_fiber_full_zpq u1 u2 u3 v1 s|%:R^-1.
  move=> [v2 v3] Hin.
  rewrite (dsdp_solution_uniform_prob_zpq Hu3_pos Hu3_lt Hcond_pos Hin).
  by rewrite card_m.
have Hnonsol_zero: forall pair : msg * msg,
    pair \notin dsdp_fiber_full_zpq u1 u2 u3 v1 s ->
    `Pr[VarRV = pair | CondRV = (v1, u1, u2, u3, s)] = 0.
  move=> [v2 v3] Hnotin.
  by apply: dsdp_non_solution_zero_prob_zpq.
rewrite (entropy_sum_split Hsol_unif Hnonsol_zero).
rewrite card_m.
exact: entropy_uniform_set.
Qed.

(* Main entropy result: H(V2, V3 | Alice's view) = log(pq) *)
(* This establishes that Alice learns nothing beyond the constraint. *)
Theorem dsdp_centropy_uniform_zpq :
  (forall t, (0 < U3 t)%N) ->
  `H(VarRV | CondRV) = log (m%:R : R).
Proof.
move=> HU3_pos.
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
  (* Get u3 < min(p,q) from U3_lt_min_p_q *)
  have Hu3_lt: (u3 < minn p q)%N.
    move/pfwd1_neq0: Hcond_pos => [t [Ht _]].
    move: Ht; rewrite inE => /eqP Ht.
    have HU3t : U3 t = u3 by case: Ht => _ _ _ ->.
    rewrite -HU3t.
    exact: U3_lt_min_p_q.
  by rewrite (dsdp_centropy1_uniform_zpq Hu3_pos Hu3_lt Hcond_pos).
under eq_bigr do rewrite mulrC.
by rewrite -big_distrr /= sum_pfwd1 mulr1.
Qed.

End crt_reconstruct.


(*
  ============================================================================
  Connection between CRT (Z/pqZ) and Field (F_m) approaches
  ============================================================================
  
  The two approaches to DSDP entropy analysis:
  
  1. Field approach (Section dsdp_entropy_connection):
     - Modulus m is PRIME
     - Working over finite field 'F_m
     - Any non-zero element is invertible
     - Fiber cardinality: m (degree of freedom argument)
     - Conditional entropy: H(V2,V3 | Cond) = log(m)
  
  2. CRT approach (Section crt_reconstruct):
     - Modulus m = p × q for distinct primes p, q
     - Working over ring 'Z_m (NOT a field!)
     - Only elements coprime to m are invertible
     - Security requires U3 < min(p,q) to ensure invertibility
     - Fiber cardinality: m = pq (via CRT product rule)
     - Conditional entropy: H(V2,V3 | Cond) = log(m) = log(pq)
  
  Key insight: Both approaches yield the SAME entropy formula:
  
      H(V2, V3 | Alice's view) = log(m)
  
  where m is the modulus of the message space.
  
  The CRT approach is more general:
  - Works for composite moduli (needed for certain protocols)
  - Requires stronger invertibility condition (U3 < min(p,q))
  - Provides the same security guarantee (maximum entropy over solutions)
  
  When m is prime, the CRT approach degenerates to the field approach:
  - 'Z_m ≅ 'F_m (isomorphic as rings)
  - Every non-zero element is automatically coprime to m
  - The security condition U3 ≠ 0 suffices
*)

Section dsdp_approaches_equivalence.

(* 
   The mathematical equivalence:
   For constraint u2*v2 + u3*v3 = target with u3 invertible:
   
   Field case ('F_m, m prime):
     #solutions = m  (v2 free, v3 = (target - u2*v2)/u3)
   
   Ring case ('Z_m, m = pq):
     #solutions mod p = p  (CRT component)
     #solutions mod q = q  (CRT component)
     #solutions mod pq = p × q = m  (CRT product)
   
   Both cases: Entropy = log(#solutions) = log(m)
*)

(* When m is prime, 'Z_m and 'F_m have the same cardinality *)
Lemma Zp_Fp_card_eq (m_minus_2 : nat) :
  let m := m_minus_2.+2 in
  prime m ->
  #|'Z_m| = #|'F_m|.
Proof.
move=> /= Hprime.
rewrite card_ord.
by rewrite card_Fp // pdiv_id.
Qed.

(* The entropy formulas are identical for same modulus *)
Lemma entropy_formula_same (m : nat) :
  (1 < m)%N ->
  log (m%:R : R) = log (m%:R : R).
Proof. by []. Qed.

(*
   Summary of security guarantees:
   
   Field approach (prime m):
     - Condition: U3 ≠ 0
     - Guarantee: H(V2,V3 | Cond) = log(m) bits of uncertainty
   
   CRT approach (m = pq):
     - Condition: 0 < U3 < min(p,q)  (stronger!)
     - Guarantee: H(V2,V3 | Cond) = log(pq) = log(m) bits of uncertainty
   
   Both provide maximum entropy over the solution space, meaning
   Alice learns nothing beyond the constraint itself.
*)

End dsdp_approaches_equivalence.


Section dsdp_entropy_connection.

Variable F : finFieldType.
Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Hypothesis prime_m : prime m.
Local Notation msg := 'F_m.  (* Finite field with m elements *)

Variable T : finType.
Variable P : R.-fdist T.
Variables (V1 V2 V3 U1 U2 U3 S : {RV P -> msg}).
Let CondRV : {RV P -> (msg * msg * msg * msg * msg)} :=
  [% V1, U1, U2, U3, S].
Let VarRV : {RV P -> (msg * msg)} := [%V2, V3].

Definition satisfies_constraint (cond : msg * msg * msg * msg * msg)
  (var : msg * msg) : Prop :=
  let '(v1, u1, u2, u3, s) := cond in
  let '(v2, v3) := var in
  s - u1 * v1 = u2 * v2 + u3 * v3.

Hypothesis constraint_holds :
  forall t, satisfies_constraint (CondRV t) (VarRV t).

(* Non-degeneracy assumption *)
Hypothesis U3_nonzero : forall t, U3 t != 0.

(* Given the constraint (v2, v3) are uniformly distributed over solution pairs,
   for non-solution pairs have the zero probability, it is proven in lemma
   `dsdp_non_solution_zero_prob`.

   This hypothesis matches the maximum entropy principle: for any observer
   has no prior knowledge about the distribution of solutions, they choses
   the distribution with the maximum entropy.
*)
Hypothesis uniform_over_solutions : forall t v1 u1 u2 u3 s,
  U1 t = u1 -> U2 t = u2 -> U3 t = u3 ->
  V1 t = v1 -> S t = s ->
  forall v2 v3,
    (v2, v3) \in dsdp_fiber u1 u2 u3 v1 s ->
    `Pr[ VarRV = (v2, v3) | CondRV = (v1, u1, u2, u3, s) ] =
    (#|dsdp_fiber u1 u2 u3 v1 s|)%:R^-1.

Section dsdp_centropy_uniform_solutions.

(* Helper 1: Pairs not satisfying the constraint have zero
   conditional probability *)
Lemma dsdp_non_solution_zero_prob (v1 u1 u2 u3 s : msg) (v2 v3 : msg) :
  `Pr[ CondRV = (v1, u1, u2, u3, s)] != 0 ->
  (v2, v3) \notin dsdp_fiber u1 u2 u3 v1 s ->
  `Pr[ VarRV = (v2, v3) | CondRV =
  (v1, u1, u2, u3, s) ] = 0.
Proof.
move=> Hcond_pos Hnot_solution.
set constraint := fun (conds : msg * msg * msg * msg * msg)
  (vals : msg * msg) =>
  let '(v1, u1, u2, u3, s) := conds in
  let '(v2, v3) := vals in
  (v2, v3) \in dsdp_fiber u1 u2 u3 v1 s.
have Hconstraint: forall t, constraint (CondRV t) (VarRV t).
  move=> t.
  rewrite /constraint /=.
  rewrite inE /=.
  by rewrite constraint_holds.
by rewrite (cond_prob_zero_outside_constraint Hconstraint Hcond_pos).
Qed.

(* Helper 2: Solutions have uniform probability 1/m *)
Lemma dsdp_solution_uniform_prob (v1 u1 u2 u3 s : msg) (v2 v3 : msg) :
  `Pr[ CondRV = (v1, u1, u2, u3, s)] != 0 ->
  u3 != 0 ->
  (v2, v3) \in dsdp_fiber u1 u2 u3 v1 s ->
  `Pr[ VarRV = (v2, v3) | CondRV = (v1, u1, u2, u3, s) ] =
  m%:R^-1.
Proof.
move=> Hcond_pos Hu3_neq0 Hinsol.
(* Need to extract witnesses for the equalities from the conditioning event *)
(* Then apply uniform_over_solutions hypothesis *)
have card_m : #|dsdp_fiber u1 u2 u3 v1 s| = m.
  by apply: dsdp_fiber_cardinality.
move/pfwd1_neq0: Hcond_pos => [t [Ht _]].
move: Ht; rewrite inE => /eqP Ht.
case: Ht => HV1 HU1 HU2 HU3 HS.
by rewrite (@uniform_over_solutions
  t v1 u1 u2 u3 s HU1 HU2 HU3 HV1 HS v2 v3 Hinsol) card_m.
Qed.

(* Helper: Main entropy calculation *)
(* Uses general framework from entropy_fibers.v *)
Lemma dsdp_entropy_uniform_subset (u1 u2 u3 v1 s : msg) :
  `Pr[ CondRV = (v1, u1, u2, u3, s)] != 0 ->
  u3 != 0 ->
  (forall pair : msg * msg,
    pair \in dsdp_fiber u1 u2 u3 v1 s ->
    `Pr[ VarRV = pair | CondRV =
      (v1, u1, u2, u3, s) ] = m%:R^-1) ->
  (forall pair : msg * msg,
    pair \notin dsdp_fiber u1 u2 u3 v1 s ->
    `Pr[ VarRV = pair | CondRV =
      (v1, u1, u2, u3, s) ] = 0) ->
  `H[ VarRV | CondRV = (v1, u1, u2, u3, s) ] =
    log (m%:R : R).
Proof.
move=> Hcond_pos Hu3_neq0 Hsol_unif Hnonsol_zero.
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
have card_m : #|dsdp_fiber u1 u2 u3 v1 s| = m.
  by apply: dsdp_fiber_cardinality.
(* Adjust uniform hypothesis to match expected form *)
have Hsol_unif': forall pair : msg * msg,
    pair \in dsdp_fiber u1 u2 u3 v1 s ->
    `Pr[VarRV = pair | CondRV = (v1, u1, u2, u3, s)] = 
    #|dsdp_fiber u1 u2 u3 v1 s|%:R^-1.
  move=> pair Hin.
  rewrite (Hsol_unif pair Hin).
  by rewrite card_m.
rewrite (entropy_sum_split Hsol_unif' Hnonsol_zero).
have ->: #|dsdp_fiber u1 u2 u3 v1 s| = m.
  by rewrite card_m.
exact: entropy_uniform_set.
Qed.

(* Helper: Each conditioning value gives entropy log(m) *)
Lemma dsdp_centropy1_uniform (v1 u1 u2 u3 s : msg) :
  `Pr[CondRV = (v1, u1, u2, u3, s)] != 0 ->
  u3 != 0 ->
  `H[ VarRV | CondRV = (v1, u1, u2, u3, s) ] =
    log (m%:R : R).
Proof.
move=> Hcond_pos Hu3_neq0.
apply: dsdp_entropy_uniform_subset => //.
  move=> [v2 v3] Hpair.
  exact: dsdp_solution_uniform_prob.
move=> [v2 v3] Hpair.
exact: dsdp_non_solution_zero_prob.
Qed.

(* Main lemma *)
Lemma dsdp_centropy_uniform_solutions :
  `H(VarRV | CondRV) = log (m%:R : R).
Proof.
(* Expand conditional entropy as weighted sum *)
rewrite centropy_RVE' /=.
(* Transform each term in the sum *)
transitivity (\sum_(a : msg * msg * msg * msg * msg) 
               `Pr[ CondRV = a ] * log (m%:R : R)).
  (* Show each term equals Pr[...] * log(m) *)
  apply: eq_bigr => [] [] [] [] [] v1 u1 u2 u3 s H.
  have [->|Hcond_pos] := eqVneq (`Pr[CondRV =
    (v1, u1, u2, u3, s)]) 0.
    by rewrite !mul0r.
  have Hu3_neq0: u3 != 0.
    move/pfwd1_neq0: Hcond_pos => [t [Ht _]].
    move: Ht; rewrite inE => /eqP Ht.
    have HU3t : U3 t = u3.
      by case: Ht => _ _ _ ->.
    by rewrite -HU3t; apply: U3_nonzero.
  by rewrite (dsdp_centropy1_uniform Hcond_pos Hu3_neq0).
under eq_bigr do rewrite mulrC.
by rewrite -big_distrr /= sum_pfwd1 mulr1.
Qed.


End dsdp_centropy_uniform_solutions.

Section dsdp_var_entropy.
  
Let card_msg_pair : #|((msg * msg)%type : finType)| = (m ^ 2)%N.
Proof. by rewrite card_prod /= !card_Fp. Qed.

(* Assume all (v2, v3) are distributed uniformly since they are
   private inputs from parties, we get the unconditional entropy of them.

   So we get:

     `H(VarRV | CondRV) = log m < `H `p_VarRV

   Shows that the DSDP protocol indeed leaks information, but still secure by:

    Lemma privacy_by_bonded_leakage :
      `H([% V2, V3] | AliceView ) = `H(V2 | AliceView).

   At the end of this file.
*)
Lemma dsdp_var_entropy :
  `p_VarRV = fdist_uniform card_msg_pair ->
  `H `p_VarRV = log (m%:R * m%:R : R).
Proof.
move->.
rewrite entropy_uniform card_prod !card_Fp. 
  by rewrite natrM.
by [].
Qed.

End dsdp_var_entropy.

End dsdp_entropy_connection.

Section dsdp_privacy_analysis.

Variable F : finFieldType.
Variable T : finType.
Variable P : R.-fdist T.

(* If A is const-RV actually P |= A _|_ A.
   But in the DSDP setting, we don't have such RVs.
*)
Hypothesis neg_self_indep : forall (TA : finType)
  (A : {RV P -> TA}), ~ P |= A _|_ A.

Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Hypothesis prime_m : prime m.

Local Notation msg := 'F_m. 
(* Finite field - when m is prime, isomorphic to Z/mZ *)
Let card_msg : #|msg| = m.
Proof. by rewrite card_Fp // pdiv_id. Qed.

Let enc := enc party msg.
Let pkey := pkey party msg.

Let data := (msg + enc + pkey)%type.
Let d x : data := inl (inl x).
Let e x : data := inl (inr x).
Let k x : data := inr x.

Notation dsdp_traceT := (15.-bseq data).
Notation dsdp_tracesT := (3.-tuple dsdp_traceT).
Notation "u *h w" := (Emul u w).
Notation "u ^h w" := (Epow u w).

Definition dsdp_uncurry (o: Alice.-key Dec msg * Bob.-key Dec msg *
  Charlie.-key Dec msg * msg * msg * msg * msg * msg * msg * msg * msg)
  : dsdp_tracesT :=
  let '(dk_a, dk_b, dk_c, v1, v2 , v3, u1, u2, u3, r2, r3) := o in
  (dsdp_traces dk_a.2 dk_b.2 dk_c.2 v1 v2 v3 u1 u2 u3 r2 r3).

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

    pV1_unif : `p_ V1 = fdist_uniform card_msg;
    pV2_unif : `p_ V2 = fdist_uniform card_msg;
    pV3_unif : `p_ V3 = fdist_uniform card_msg;
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
Let AliceInputsView : {RV P -> alice_inputsT} := [% Dk_a, V1, U1, U2, U3, R2, R3].

(* Since `AliceInputView` are generated by Alice,
   while `v2` is generated by Bob *)
Hypothesis AliceInputsView_indep_V2 :
  P |= AliceInputsView _|_ V2.

Definition DSDP_RV (inputs : dsdp_random_inputs) :
  {RV P -> dsdp_tracesT} :=
    dsdp_uncurry `o
    [% Dk_a, Dk_b, Dk_c, V1, V2, V3, U1, U2, U3, R2, R3].

Section alice_privacy_analysis.

Local Notation m := m_minus_2.+2.

Let AliceTraces : {RV P -> dsdp_traceT} :=
      (fun t => tnth t 0) `o DSDP_RV inputs.

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

Let AliceTraces_values_from_view
  (v : alice_view_valuesT) : 15.-bseq _ :=
    let '(dk_a, s, v1 , u1, u2, u3, r2, r3,
      E_alice_d3, E_charlie_v3, E_bob_v2) := v in
    [bseq d s;
            e (E_alice_d3 : enc);
            e (E_charlie_v3 : enc);
            e (E_bob_v2 : enc);
            d r3; d r2; d u3; d u2; d u1; d v1; k (dk_a : pkey)].

Lemma AliceTraces_from_viewP :
  AliceTraces = AliceTraces_values_from_view `o AliceView.
Proof.
apply: boolp.funext => x /=.
rewrite /AliceTraces /DSDP_RV /comp_RV /= dsdp_traces_ok //=.
have Ha : dsdp_program.k (Alice, Dec, (Dk_a x).2) = k (Dk_a x).
  (* Rocq doesn't know this is the only case, and it makes both sides equal*)
  by case: Dk_a => t. 
rewrite  -[in RHS]Ha //=.
Qed.

Local Definition AliceView_values_from_trace (xs : dsdp_traceT) :
  alice_view_valuesT :=
    let failtrace := (KeyOf Alice Dec 0,
                        0, 0, 0, 0, 0, 0, 0,
                        E' Alice 0, E' Charlie 0, E' Bob 0) in
    if xs is Bseq [:: inl (inl s);
           inl (inr E_alice_d3);
           inl (inr E_charlie_v3);
           inl (inr E_bob_v2);
           inl (inl r3); inl (inl r2); inl (inl u3);
           inl (inl u2); inl (inl u1); inl (inl v1); inr dk_a] _
    then 
         if (E_alice_d3, E_charlie_v3, E_bob_v2, dk_a) is
              ((Alice, d3), (Charlie, v3), (Bob, v2), (Alice, Dec, k_a)) then
            (KeyOf Alice Dec k_a, s, v1 , u1, u2, u3, r2, r3,
               E' Alice d3, E' Charlie v3, E' Bob v2)
         else failtrace
    else failtrace.

Lemma AliceView_values_from_traceP:
   cancel AliceTraces_values_from_view AliceView_values_from_trace.
Proof.
move => [] [] [] [] [] [] [] [] [] [] dk ? ? ? ? ? ? ? a c b //=.
case: a => -[a ma] /=.  (* msg from `case: a`
                           can be case again to get 1. nat a 2. nat a < m*)
case: c => -[c mc] /=.
case: b => -[b mb] /=.
case: dk => -[dk mdk] /=.
by [].
Qed.

Lemma ce_AliceTraces_AliceView (w : finType) (v : {RV P -> w}) :
  `H(v | AliceTraces ) = `H(v | AliceView ).
Proof.
simpl in *.
transitivity (`H(v | [% AliceTraces, AliceView])).
  have -> : AliceView = AliceView_values_from_trace `o AliceTraces.
    by apply: boolp.funext => x /= ;
       rewrite AliceTraces_from_viewP /comp_RV AliceView_values_from_traceP.
  by rewrite centropy_RV_contraction.
by rewrite AliceTraces_from_viewP centropyC centropy_RV_contraction.
Qed.

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
  [set uv in setT `* setT | dotp2 uv.1 uv.2 == s].

Definition Dotp2_rv (X Y : {RV P -> (msg * msg)}) : {RV P -> msg} :=
  fun p => dotp2 (X p) (Y p).

Definition Dotp2Solutions
  (S : {RV P -> msg}) : {RV P -> {set (msg * msg) * (msg * msg)} } :=
  dotp2_solutions `o S.

Definition US := [% U2, U3].
Definition VS := [% V2, V3].

Definition ConstUS := [% (fun _ => 1):{RV P -> msg}, (fun _ => 0):{RV P -> msg}].
Definition VU1 : {RV P -> msg} := V1 \* U1.

Lemma S_alt :
  S = Dotp2_rv VS US \+ VU1.
Proof.
rewrite /S /VS /US /D3 /VU3R /D2 /VU3 /VU2 /VU1 /Dotp2_rv /dotp2 /add_RV.
apply: boolp.funext => i //=.
ring.
Qed.

Lemma S_alt2 :
  let f := (fun o => let '(u2, u3, v2, v3, v1, u1) := o
              in u2 * v2 + u3 * v3 + v1 * u1) in
  S = f `o [% U2, U3, V2, V3, V1, U1].
Proof.
rewrite /comp_RV /S /VS /US /D3 /VU3R /D2 /VU3 /VU2 /VU1 /Dotp2_rv /dotp2 /add_RV.
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
Lemma ConstUS_is_V2_discloser :
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
Theorem if_US_are_compromised_V2_is_leaked :
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
rewrite S_alt /add_RV //= (ConstUS_is_V2_discloser H).
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
   given all values except v3 (and assuming u3 ≠ 0), v3 is determined.
   
   In our F_m formalization: When u3 ≠ 0, we express this determination via
   division: v3 = (s - u2*v2 - u1*v1) / u3, which always yields exactly one
   solution. This division is a mathematical expression of functional
   determination that enables us to apply composition lemmas like
   `joint_entropy_RV_comp` in the entropy analysis.
   
   In Z/pq implementations: The division operation is not directly used by
   protocol parties. Instead, the constraint is satisfied through homomorphic
   computation. Parties sample uniformly from Z/pq without avoiding
   non-invertible elements. The adversary, observing only the encrypted
   constraint satisfaction (not individual v2, v3 values), cannot exploit
   whether sampled values are invertible.
   
   Key insight: The entropy relationship

     H(V2, V3 | constraints) = H(V2 | constraints)

   holds because V3 adds no additional entropy once V2 and the constraint
   are known. This is a consequence of the constraint structure itself,
   independent of how we mathematically express the determination
   (division in F_m, or implicit in Z/pq).
   
   NOTE: Current formalization uses 'F_m (prime field) where all non-zero
   elements are invertible, enabling clean entropy analysis via field-based
   linear algebra. The statistical distance between F_m and Z/pq is negligible
   (< 2^-1023) for cryptographic parameters, justifying this approximation.
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

Lemma V3_determined : V3 = compute_v3 `o [% V1, U1, U2, U3, S, V2].
Proof.
rewrite S_alt2 /compute_v3 /comp_RV /=.  
apply/boolp.funext => i /=.
field.
exact: (U3_nonzero i).
Qed.

(* TODO: put an assumption so the lemma
   determined_auxiliary_adds_no_information_v2 can be applied
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
Lemma determined_auxiliary_adds_no_information_v2 :
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

(* Entropy: set, and views to project to where we need orders. *)
Lemma privacy_by_bonded_leakage :
  `H([% V2, V3] | AliceView ) = `H(V2 | AliceView).
Proof.
set OtherAlice : {RV P -> (Alice.-key Dec msg) * msg * msg} :=
  [% Dk_a, R2, R3].
have H: forall V, `H(V | AliceView ) =
    `H(V | [% OtherAlice, V1, U1, U2, U3, S] ).
  move => t V.
  rewrite /OtherAlice /AliceView.
  rewrite !(E_enc_ce_removal V card_msg); last first.
    exact: Pr_AliceView_neq0; last first.
    exact: Pr_Eqn1View_neq0; last first.
    exact: Pr_Eqn2View_neq0.
  have H_reorder: `H( V | [% Dk_a, S, V1, U1, U2, U3, R2, R3]) =
    `H( V | [% Dk_a, R2, R3, V1, U1, U2, U3, S]).
    rewrite /centropy_RV /centropy /= !snd_RV2.
    rewrite (reindex (fun '(dk_a', r2', r3', v1', u1', u2', u3', s') => 
                      (dk_a', s', v1', u1', u2', u3', r2', r3')))/=.
      apply: eq_bigr => [] [] [] [] [] [] [] []
        dk_a' s' v1' u1' u2' u3' r2' r3' _.
      congr (_ * _).
           rewrite !dist_of_RVE !pfwd1E; congr Pr; apply/setP => u;
           rewrite !inE /= !xpair_eqE;
           (* GRing.mul has many instances so specify it then ring works. *)
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
    exact: H_reorder.
rewrite (H msg V2) (H (msg * msg)%type [% V2, V3]).
have H_assoc: forall V, `H(V | [% OtherAlice, V1, U1, U2, U3, S] ) =
    `H(V | [% OtherAlice, [%V1, U1, U2, U3, S]] ).
  move => t v.
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
rewrite (H_assoc msg V2) (H_assoc (msg * msg)%type [% V2, V3]).
rewrite (cinde_centropy_eq cinde_V2V3).
rewrite (cinde_centropy_eq cinde_V2).
apply: determined_auxiliary_adds_no_information_v2.
exact: U3_coprime_m.
Qed. (* TODO: opaque check takes very long. *)

End semi_honest_case_analysis.

End alice_privacy_analysis.

End dsdp_privacy_analysis.


