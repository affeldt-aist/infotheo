From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap matrix lra.
Require Import rouche_capelli.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter smc_tactics.
Require Import smc_proba homomorphic_encryption dsdp_program dsdp_extra.

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

Section dsdp_safety.
  
Variable F : finFieldType.
Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Hypothesis prime_m : prime m.
(* The following line won't work for \rank.
   And will make it report an unrelated
   'rV[_]_n vs. 'M[_]_(n, m) issue.

   Local Notation msg := 'I_m.
*)
Local Notation msg := 'F_m.  (* Finite field with m elements *)

Section linear_system.

(** ** 1. DSDP Linear System Definition *)

(* The DSDP constraint as a matrix equation

     s = u2 * v2 + u3 * v3 + u1 * v1

  As linear system:

  [u1  u2  u3] * [v1]   [s]
                 [v2] = [ ]
                 [v3]   [ ]
*)
Definition dsdp_matrix (u1 u2 u3 : msg) : 'M[msg]_(1, 3)  :=
  \matrix_(i < 1, j < 3) 
    match j with
    | Ordinal 0 _ => u1
    | Ordinal 1 _ => u2
    | Ordinal 2 _ => u3
    | _ => 0
    end.

(* Vector of secret values *)
Definition secret_vector (v1 v2 v3 : msg) : 'rV[msg]_3 :=
  \row_(j < 3)
    match j with
    | Ordinal 0 _ => v1
    | Ordinal 1 _ => v2
    | Ordinal 2 _ => v3
    | _ => 0
    end.

Definition dsdp_constraint (u1 u2 u3 v1 v2 v3 s : msg) : Prop :=
  (secret_vector v1 v2 v3) *m (dsdp_matrix u1 u2 u3)^T =
    \matrix_(i < 1, j < 1) s.

Lemma dsdp_matrix_rank1 u1 u2 u3 :
  (u1 != 0) || (u2 != 0) || (u3 != 0) ->
  \rank (dsdp_matrix u1 u2 u3) = 1.
Proof.
move=> Hneq0.
have rank_le1: (\rank (dsdp_matrix u1 u2 u3) <= 1)%N.
  by rewrite rank_leq_row.
have rank_ge1: (1 <= \rank (dsdp_matrix u1 u2 u3))%N.
  rewrite lt0n mxrank_eq0.
  move: Hneq0.
  rewrite -orbA.
  case/or3P => [Hu1 | Hu2 | Hu3].
  - apply/eqP => /matrixP H.
    move: (H ord0 ord0).
    rewrite !mxE /=.
    by move/eqP; rewrite (negbTE Hu1).
  - apply/eqP => /matrixP H.
    move: (H ord0 (lift ord0 ord0)).
    rewrite !mxE /=.
    by move/eqP; rewrite (negbTE Hu2).
  - apply/eqP => /matrixP H.
    move: (H ord0 (lift ord0 (lift ord0 ord0))).
    rewrite !mxE /=.
    by move/eqP; rewrite (negbTE Hu3).
by apply/eqP; rewrite eqn_leq rank_le1 rank_ge1.
Qed.

(* All solutions to the homogeneous system (kernel) *)
Definition dsdp_kernel (u1 u2 u3 : msg) : {set 'rV[msg]_3} :=
  [set v : 'rV[msg]_3 | v *m (dsdp_matrix u1 u2 u3)^T == 0].

(* All solutions to the inhomogeneous system *)
Definition dsdp_solution_set (u1 u2 u3 v1 s : msg) : {set 'rV[msg]_3} :=
  [set v : 'rV[msg]_3 | 
    v *m (dsdp_matrix u1 u2 u3)^T == \matrix_(i < 1, j < 1) (s - u1 * v1)].

Definition dsdp_solution_pairs (u1 u2 u3 v1 s : msg) : {set msg * msg} :=
  [set v2v3 : msg * msg | u1 * v1 + u2 * v2v3.1 + u3 * v2v3.2 == s].

Lemma dsdp_kernel_cardinality u1 u2 u3 :
  (u1 != 0) || (u2 != 0) || (u3 != 0) ->
  #|dsdp_kernel u1 u2 u3| = (m ^ (3 - 1))%N.
Proof.
move=> H.
rewrite /dsdp_kernel.
rewrite count_kernel_vectors.
rewrite mxrank_tr (dsdp_matrix_rank1 H).
(* Show #|{:msg}| = m *)
by rewrite card_Fp // pdiv_id.
Qed.

Lemma dsdp_solution_pairs_cardinality u1 u2 u3 v1 s :
  u3 != 0 ->
  #|dsdp_solution_pairs u1 u2 u3 v1 s| = m.
Proof.
move=> Hu3neg0.
rewrite /dsdp_solution_pairs.
(* Rewrite equation to separate constant term *)
have -> : [set v2v3 | u1 * v1 + u2 * v2v3.1 + u3 * v2v3.2 == s] =
          [set v2v3 | u2 * v2v3.1 + u3 * v2v3.2 == s - u1 * v1].
  apply/setP => [[v2 v3]]; rewrite !inE /=.
  by rewrite -subr_eq opprK addrAC addrC addrAC addrA.
rewrite (@count_affine_solutions_rank1 msg u2 u3 (s - u1 * v1) Hu3neg0).
(* Show #|msg| = m *)
by rewrite card_Fp // pdiv_id.
Qed.

Lemma dsdp_solution_set_card_full u1 u2 u3 v1 s :
  u3 != 0 ->
  #|dsdp_solution_set u1 u2 u3 v1 s| = (m ^ 2)%N.
Proof.
move=> Hu3neq0.
rewrite /dsdp_solution_set.
(* Step 1: Construct a particular solution x0 *)
pose x0 := \row_(j < 3) 
  (if j == ord0 then 0 
   else if j == lift ord0 ord0 then 0 
   else (s - u1 * v1) / u3).
(* Step 2: Prove x0 is indeed a solution *)
have Hx0 : x0 *m (dsdp_matrix u1 u2 u3)^T = 
           \matrix_(i < 1, j < 1) (s - u1 * v1).
  apply/matrixP => i j.
  rewrite !mxE.
  have -> : i = ord0 by apply: ord1.
  have -> : j = ord0 by apply: ord1.
  rewrite (bigD1 ord0) //= (bigD1 (lift ord0 ord0)) //=.
  rewrite (bigD1 (lift ord0 (lift ord0 ord0))) //= big1; last first.
    move=> k /andP [/andP [Hk1 Hk2] Hk3].
    case: k Hk1 Hk2 Hk3 => [[|[|[|?]]] ?] //=.
  by rewrite addr0 !mxE /= !mul0r !add0r divfK.
(* Step 3: Apply the affine solutions counting lemma *)
rewrite (@count_affine_solutions_explicit msg 3 1 
         (dsdp_matrix u1 u2 u3)^T 
         (\matrix_(i < 1, j < 1) (s - u1 * v1)) 
         x0 Hx0).
(* Step 4: Simplify using rank *)
rewrite mxrank_tr.
have -> : \rank (dsdp_matrix u1 u2 u3) = 1.
  apply: dsdp_matrix_rank1.
  by rewrite Hu3neq0 orbT.
by rewrite card_Fp // pdiv_id.
Qed.

End linear_system.

Section dsdp_entropy_connection.

Variable T : finType.
Variable P : R.-fdist T.
Variables (V1 V2 V3 U1 U2 U3 S : {RV P -> msg}).

(* The constraint holds with probability 1 *)
Hypothesis constraint_holds :
  forall t, S t = U1 t * V1 t + U2 t * V2 t + U3 t * V3 t.

(* Non-degeneracy assumption *)
Hypothesis U3_nonzero : forall t, U3 t != 0.

(* Given the constraint, (v2, v3) are uniformly distributed over solutions *)
(* By maximum entropy principle for any observer has no prior knowledge
   about the distribution of solutions.
*)
Hypothesis uniform_over_solutions : forall t v1 u1 u2 u3 s,
  U1 t = u1 -> U2 t = u2 -> U3 t = u3 ->
  V1 t = v1 -> S t = s ->
  forall v2 v3,
    (v2, v3) \in dsdp_solution_pairs u1 u2 u3 v1 s ->
    `Pr[ [% V2, V3] = (v2, v3) | [% V1, U1, U2, U3, S] = 
         (v1, u1, u2, u3, s) ] =
    1%:R / (#|dsdp_solution_pairs u1 u2 u3 v1 s|)%:R.

Section dsdp_centropy_uniform_solutions.

(* Helper 1: Pairs not satisfying the constraint have zero
   conditional probability *)
Lemma dsdp_non_solution_zero_prob (v1 u1 u2 u3 s : msg) (v2 v3 : msg) :
  `Pr[[% V1, U1, U2, U3, S] = (v1, u1, u2, u3, s)] != 0 ->
  (v2, v3) \notin dsdp_solution_pairs u1 u2 u3 v1 s ->
  `Pr[ [% V2, V3] = (v2, v3) | [% V1, U1, U2, U3, S] =
  (v1, u1, u2, u3, s) ] = 0.
Proof.
move=> Hcond_pos Hnot_solution.
set constraint := fun (conds : msg * msg * msg * msg * msg)
  (vals : msg * msg) =>
  let '(v1, u1, u2, u3, s) := conds in
  let '(v2, v3) := vals in
  (v2, v3) \in dsdp_solution_pairs u1 u2 u3 v1 s.
have Hconstraint: forall t, constraint ([%V1, U1, U2, U3, S] t) ([%V2, V3] t).
  move=> t.
  rewrite /constraint /=.
  rewrite inE /=.
  by rewrite constraint_holds.
by rewrite (cond_prob_zero_outside_constraint Hconstraint Hcond_pos).
Qed.

(* Helper 2: Solutions have uniform probability 1/m *)
Lemma dsdp_solution_uniform_prob (v1 u1 u2 u3 s : msg) (v2 v3 : msg) :
  `Pr[[% V1, U1, U2, U3, S] = (v1, u1, u2, u3, s)] != 0 ->
  u3 != 0 ->
  (v2, v3) \in dsdp_solution_pairs u1 u2 u3 v1 s ->
  `Pr[ [% V2, V3] = (v2, v3) | [% V1, U1, U2, U3, S] = (v1, u1, u2, u3, s) ] =
  1%:R / m%:R.
Proof.
move=> Hcond_pos Hu3_neq0 Hinsol.
(* Need to extract witnesses for the equalities from the conditioning event *)
(* Then apply uniform_over_solutions hypothesis *)
have card_m : #|dsdp_solution_pairs u1 u2 u3 v1 s| = m.
  by apply: dsdp_solution_pairs_cardinality.
move/pfwd1_neq0: Hcond_pos => [t [Ht _]].
move: Ht; rewrite inE => /eqP Ht.
case: Ht => HV1 HU1 HU2 HU3 HS.
by rewrite (@uniform_over_solutions
  t v1 u1 u2 u3 s HU1 HU2 HU3 HV1 HS v2 v3 Hinsol) card_m.
Qed.

(* Helper: Basic arithmetic - entropy of uniform distribution
   over n elements *)
Lemma entropy_uniform_count (n : nat) :
  (0 < n)%N ->
  (- \sum_(i < n) (1%:R / n%:R) * log ((1 / n%:R) : R)) = log (n%:R : R).
Proof.
move=> Hn_pos.
rewrite big_const iter_addr addr0 card_ord.
have Hn_gt0 : (0 < n%:R).
  move => t.
  by rewrite -[0]/(0%:R) ltr_nat.
rewrite mul1r (logV (Hn_gt0 R)).
field.
by rewrite pnatr_eq0 -lt0n Hn_pos.
Qed.

(* Helper 3c: Entropy formula in terms of conditional probability *)
Lemma dsdp_centropy1_as_sum (v1 u1 u2 u3 s : msg) :
  `Pr[[% V1, U1, U2, U3, S] = (v1, u1, u2, u3, s)] != 0 ->
  `H[ [% V2, V3] | [% V1, U1, U2, U3, S] = (v1, u1, u2, u3, s) ] =
  - \sum_(pair : msg * msg)
   `Pr[ [% V2, V3] = pair | [% V1, U1, U2, U3, S] = (v1, u1, u2, u3, s) ] *
   log (`Pr[ [% V2, V3] = pair | [% V1, U1, U2, U3, S] = (v1, u1, u2, u3, s) ]).
Proof.
move=> Hcond_pos.
rewrite centropy1_RVE // /entropy.
congr (- _); apply: eq_bigr => [[v2 v3]] _.
  by rewrite jfdist_cond_cPr_eq.
by rewrite fst_RV2 dist_of_RVE.
Qed.

(* Helper: Entropy over finite set with uniform probability *)
Lemma entropy_finite_set_uniform (SolSet : {set msg * msg}) (n : nat) :
  #|SolSet| = n ->
  (0 < n)%N ->
  (- \sum_(pair in SolSet) (1%:R / n%:R) *  log ((1 / n%:R) : R)) =
  log (n%:R : R).
Proof.
move=> Hcard Hn_pos.
rewrite big_const iter_addr addr0 Hcard -mulr_natr mul1r.
rewrite logV; last by rewrite ltr0n.
field.
by rewrite pnatr_eq0 -lt0n.
Qed.

(* Helper: Main entropy calculation *)
Lemma dsdp_entropy_uniform_subset (v1 u1 u2 u3 s : msg) :
  `Pr[[% V1, U1, U2, U3, S] = (v1, u1, u2, u3, s)] != 0 ->
  u3 != 0 ->
  (forall pair : msg * msg,
    pair \in dsdp_solution_pairs u1 u2 u3 v1 s ->
    `Pr[ [% V2, V3] = pair | [% V1, U1, U2, U3, S] =
      (v1, u1, u2, u3, s) ] = 1%:R / m%:R) ->
  (forall pair : msg * msg,
    pair \notin dsdp_solution_pairs u1 u2 u3 v1 s ->
    `Pr[ [% V2, V3] = pair | [% V1, U1, U2, U3, S] =
      (v1, u1, u2, u3, s) ] = 0) ->
  `H[ [% V2, V3] | [% V1, U1, U2, U3, S] = (v1, u1, u2, u3, s) ] =
    log (m%:R : R).
Proof.
move=> Hcond_pos Hu3_neq0 Hsol_unif Hnonsol_zero.
(* Express as sum using helper 3c *)
rewrite (dsdp_centropy1_as_sum Hcond_pos).
(* Split into solutions vs non-solutions using helper 3d *)
rewrite (entropy_sum_split Hsol_unif Hnonsol_zero).
have card_m : #|dsdp_solution_pairs u1 u2 u3 v1 s| = m.
  by apply: dsdp_solution_pairs_cardinality.
by apply: entropy_finite_set_uniform.
Qed.

(* Helper: Each conditioning value gives entropy log(m) *)
Lemma dsdp_centropy1_uniform (v1 u1 u2 u3 s : msg) :
  `Pr[[% V1, U1, U2, U3, S] = (v1, u1, u2, u3, s)] != 0 ->
  u3 != 0 ->
  `H[ [% V2, V3] | [% V1, U1, U2, U3, S] = (v1, u1, u2, u3, s) ] =
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
  `H([% V2, V3] | [% V1, U1, U2, U3, S]) = log (m%:R : R).
Proof.
(* Expand conditional entropy as weighted sum *)
rewrite centropy_RVE' /=.
(* Transform each term in the sum *)
transitivity (\sum_(a : msg * msg * msg * msg * msg) 
               `Pr[ [% V1, U1, U2, U3, S] = a ] * log (m%:R : R)).
  (* Show each term equals Pr[...] * log(m) *)
  apply: eq_bigr => [] [] [] [] [] v1 u1 u2 u3 s H.
  have [->|Hcond_pos] := eqVneq (`Pr[[% V1, U1, U2, U3, S] =
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

End dsdp_entropy_connection.

(** ** Main Security Theorem *)

(*
Theorem dsdp_security_bounded_leakage :
  `H(v2 | alice_view) = log (m%:R) /\
  `H(v2 | alice_view) > 0.
Proof.
split.
- (* Equality *)
  rewrite -pair_entropy_equals_component.
  rewrite pair_entropy_via_conditioning.
  exact: pair_entropy_from_uniformity.
- (* Positive bound *)
  rewrite -pair_entropy_equals_component.
  rewrite pair_entropy_via_conditioning.
  rewrite pair_entropy_from_uniformity.
  (* log(m) > 0 since m >= 2 *)
  apply: log_gt0.
  rewrite ltr1n.
  (* m = m_minus_2.+2 >= 2 *)
  by [].
Qed.
*)

(** ** Interpretation *)

(* The adversary learns log(m) bits about v2, not 0 bits (perfect secrecy)
   but also not log(m^2) bits (complete knowledge).
   
   This is because:
   - There are m possible values for v2
   - Each is equally likely given alice_view
   - Entropy = log(m) bits
   
   Security holds despite information leakage.
*)

End dsdp_safety.

