From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap matrix lra.
From rouche_capelli Require Import rouche_capelli.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter smc_tactics.
Require Import smc_proba homomorphic_encryption dsdp_program.

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

Section entropy_connection.

Variable T : finType.
Variable P : R.-fdist T.
Variables (V1 V2 V3 U1 U2 U3 S : {RV P -> msg}).

(* The constraint holds with probability 1 *)
Hypothesis constraint_holds :
  forall t, S t = U1 t * V1 t + U2 t * V2 t + U3 t * V3 t.

(* Non-degeneracy assumption *)
Hypothesis U3_nonzero : forall t, U3 t != 0.

(* Given the constraint, (v2, v3) are uniformly distributed over solutions *)
Hypothesis uniform_over_solutions : forall t v1 u1 u2 u3 s,
  U1 t = u1 -> U2 t = u2 -> U3 t = u3 ->
  V1 t = v1 -> S t = s ->
  forall v2 v3,
    (v2, v3) \in dsdp_solution_pairs u1 u2 u3 v1 s ->
    `Pr[ [% V2, V3] = (v2, v3) | [% V1, U1, U2, U3, S] = 
         (v1, u1, u2, u3, s) ] =
    1%:R / (#|dsdp_solution_pairs u1 u2 u3 v1 s|)%:R.

Lemma conditional_entropy_uniform_solutions :
  `H([% V2, V3] | [% V1, U1, U2, U3, S]) = log (m%:R : R).
Proof.
Admitted.

End entropy_connection.

(*
  MEMO: move linear algebra part ("safety" part) and its connection with the
  information theory to another file (dsdp_safety.v)
  DSDP constraint:

  s = u2 * v2 + u3 * v3 + u1 * v1

  As linear system:

  [u1  u2  u3] * [v1]   [s]
                 [v2] = [ ]
                 [v3]   [ ]


For the inhomogeneous system (with fixed s, u1, u2, u3):
Number of solutions = #|msg|^(3 - rank(A)) where A = [u1 u2 u3]
This is an affine space parallel to the kernel

*)
                                
(*

   Rank = 1 → Kernel dim = 2 → #|solutions| = m → 
   Uniform → H = log(m) → Security with bounded leakage

*)

(* The adversary learns log(m) bits about v2, not 0 bits (perfect secrecy)
   but also not log(m^2) bits (complete knowledge).
   
   This is because:
   - There are m possible values for v2
   - Each is equally likely given alice_view
   - Entropy = log(m) bits
   
   Security holds despite information leakage.
*)

(*

TODO:

Theorem dsdp_security :
  (* By Rouché-Capelli: multiple solutions exist *)
  #|solution_set| > 1 ->
  
  (* Pair entropy = component entropy *)
  `H([% V2, V3] | alice_view) = `H(v2 | alice_view) /\
  
  (* Bounded leakage *)
  `H(v2 | alice_view) = log #|solution_set| > 0.
Proof.
  move=> multi_solutions.
  split.
  - (* Apply pair_entropy_eq_component *)
    apply: pair_entropy_eq_component.
    (* Show v3 = f(v2, s, u2, u3) *)
    ...
  - (* Uniform distribution by max entropy *)
    rewrite uniform_over_solutions.
    (* log #|solution_set| > log 1 by multi_solutions *)
    ...
Qed.                         


*)


(*

(** * Linear Algebra Foundation for DSDP Security *)

Section DSDP_LinearAlgebra.

Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Local Notation msg := 'I_m.

(** ** 1. DSDP Linear System Definition *)

(* The DSDP constraint as a matrix equation *)
Definition dsdp_matrix (u1 u2 u3 : msg) : 'M[msg]_(1, 3) :=
  \matrix_(i < 1, j < 3) 
    match j with
    | Ordinal 0 _ => u1
    | Ordinal 1 _ => u2
    | Ordinal 2 _ => u3
    end.

(* Vector of secret values *)
Definition secret_vector (v1 v2 v3 : msg) : 'rV[msg]_3 :=
  \row_(j < 3)
    match j with
    | Ordinal 0 _ => v1
    | Ordinal 1 _ => v2
    | Ordinal 2 _ => v3
    end.

(* The constraint: s = u1*v1 + u2*v2 + u3*v3 *)
Definition dsdp_constraint (u1 u2 u3 v1 v2 v3 s : msg) : Prop :=
  (secret_vector v1 v2 v3) *m (dsdp_matrix u1 u2 u3)^T = \matrix_(i < 1, j < 1) s.

(** ** 2. Rank Properties *)

Lemma dsdp_matrix_rank1 u1 u2 u3 :
  (u1 != 0) || (u2 != 0) || (u3 != 0) ->
  \rank (dsdp_matrix u1 u2 u3) = 1.
Proof.
(* The matrix [u1 u2 u3] is 1×3, so rank is at most 1 *)
(* If any coefficient is nonzero, rank is exactly 1 *)
Admitted. (* TODO: prove using matrix rank properties *)

Lemma dsdp_matrix_rank0 :
  \rank (dsdp_matrix 0 0 0) = 0.
Proof.
(* Zero matrix has rank 0 *)
Admitted.

(** ** 3. Solution Set Definition *)

(* All solutions to the homogeneous system (kernel) *)
Definition dsdp_kernel (u1 u2 u3 : msg) : {set 'rV[msg]_3} :=
  [set v : 'rV[msg]_3 | v *m (dsdp_matrix u1 u2 u3)^T == 0].

(* All solutions to the inhomogeneous system *)
Definition dsdp_solution_set (u1 u2 u3 v1 s : msg) : {set 'rV[msg]_3} :=
  [set v : 'rV[msg]_3 | 
    v *m (dsdp_matrix u1 u2 u3)^T == \matrix_(i < 1, j < 1) (s - u1 * v1)].

(* Solutions as pairs (v2, v3) given v1 *)
Definition dsdp_solution_pairs (u1 u2 u3 v1 s : msg) : {set msg * msg} :=
  [set (v2, v3) | v2 : msg, v3 : msg & u1 * v1 + u2 * v2 + u3 * v3 == s].

(** ** 4. Kernel Cardinality *)

(* Using the result from your other repo *)
Lemma dsdp_kernel_cardinality u1 u2 u3 :
  (u1 != 0) || (u2 != 0) || (u3 != 0) ->
  #|dsdp_kernel u1 u2 u3| = (m ^ (3 - 1))%N.
Proof.
move=> nonzero.
rewrite (dsdp_matrix_rank1 nonzero).
(* Apply: count_kernel_vectors_gaussian_elimination *)
(* #| kernel | = #|msg|^(dim - rank) = m^(3-1) = m^2 *)
Admitted.

(** ** 5. Solution Set Cardinality *)

Lemma dsdp_solution_set_nonempty u1 u2 u3 v1 s :
  exists v2 v3, (v2, v3) \in dsdp_solution_pairs u1 u2 u3 v1 s.
Proof.
(* Over a field, inhomogeneous linear system always has solutions *)
(* Pick any v2, then v3 = (s - u1*v1 - u2*v2) / u3 if u3 ≠ 0 *)
Admitted.

Lemma dsdp_solution_pairs_cardinality u1 u2 u3 v1 s :
  u3 != 0 ->
  #|dsdp_solution_pairs u1 u2 u3 v1 s| = m.
Proof.
move=> u3_nonzero.
(* For each v2 in msg, there's exactly one v3 = (s - u1*v1 - u2*v2) / u3 *)
(* So bijection between msg and solution pairs *)
(* Therefore #|solutions| = #|msg| = m *)
Admitted.

Lemma dsdp_solution_set_card_full u1 u2 u3 v1 s :
  u3 != 0 ->
  #|dsdp_solution_set u1 u2 u3 v1 s| = (m ^ 2)%N.
Proof.
move=> u3_nonzero.
(* The solution set is an affine space of dimension 2 *)
(* Parallel to the kernel which has dimension 2 *)
(* Cardinality = m^2 *)
Admitted.

(** ** 6. Uniformity and Entropy Connection *)

Section DSDP_Entropy_Connection.

Variable T : finType.
Variable P : R.-fdist T.
Variables (v1 v2 v3 u1 u2 u3 s : {RV P -> msg}).

(* The constraint holds with probability 1 *)
Hypothesis constraint_holds :
  forall t, s t = u1 t * v1 t + u2 t * v2 t + u3 t * v3 t.

(* Non-degeneracy assumption *)
Hypothesis u3_nonzero : forall t, u3 t != 0.

(* Given the constraint, (v2, v3) are uniformly distributed over solutions *)
Hypothesis uniform_over_solutions : forall t v1_val u1_val u2_val u3_val s_val,
  u1 t = u1_val -> u2 t = u2_val -> u3 t = u3_val ->
  v1 t = v1_val -> s t = s_val ->
  forall v2_val v3_val,
    (v2_val, v3_val) \in dsdp_solution_pairs u1_val u2_val u3_val v1_val s_val ->
    `Pr[ [% V2, V3] = (v2_val, v3_val) | [% V1, U1, U2, U3, S] = 
         (v1_val, u1_val, u2_val, u3_val, s_val) ] =
    1%:R / (#|dsdp_solution_pairs u1_val u2_val u3_val v1_val s_val|)%:R.

Lemma entropy_uniform_finite (A : finType) (S : {set A}) :
  (0 < #|S|)%N ->
  `H (fdist_uniform #|S|) = log (#|S|%:R).
Proof.
(* Standard result: entropy of uniform distribution *)
Admitted.

Lemma conditional_entropy_uniform_solutions :
  `H([% V2, V3] | [% V1, U1, U2, U3, S]) = log (m%:R).
Proof.
move: (constraint_holds) (u3_nonzero) (uniform_over_solutions) => Hcons Hu3 Hunif.
(* By uniformity and solution set cardinality *)
rewrite /centropy_RV.
(* Each conditioning value gives uniform distribution over m solutions *)
(* H(v2,v3 | cond) = sum_cond P(cond) * log(m) = log(m) *)
(* Use dsdp_solution_pairs_cardinality *)
Admitted.

End DSDP_Entropy_Connection.

End DSDP_LinearAlgebra.

(** * Main Security Theorem *)

Section DSDP_Security_Theorem.

Variable T : finType.
Variable P : R.-fdist T.
Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Local Notation msg := 'I_m.

(* Protocol random variables *)
Variables (dk_a : {RV P -> Alice.-key Dec msg}).
Variables (v1 v2 v3 u1 u2 u3 : {RV P -> msg}).
Variables (r2 r3 : {RV P -> msg}).
Variables (s : {RV P -> msg}).

(* Alice's view *)
Definition alice_view := [% Dk_a, V1, U1, U2, U3, R2, R3, S].

(* Assumptions *)
Hypothesis constraint_holds :
  forall t, s t = u1 t * v1 t + u2 t * v2 t + u3 t * v3 t.

Hypothesis u3_nonzero : forall t, u3 t != 0.

Hypothesis uniform_over_solutions : (* as above *) True.

Hypothesis alice_independence_pair :
  P |= [% Dk_a, R2, R3] _|_ [% V2, V3] | [% V1, U1, U2, U3, S].

Hypothesis alice_independence_v2 :
  P |= [% Dk_a, R2, R3] _|_ v2 | [% V1, U1, U2, U3, S].

(* v3 is determined by other values *)
Definition compute_v3_from_constraint (v1_val u1_val u2_val u3_val s_val v2_val : msg) : msg :=
  (s_val - u1_val * v1_val - u2_val * v2_val) / u3_val.

Hypothesis v3_determined : 
  v3 = compute_v3_from_constraint `o [% V1, U1, U2, U3, S, V2].

(** ** Intermediate Results *)

Lemma pair_entropy_equals_component :
  `H([% V2, V3] | alice_view) = `H(v2 | alice_view).
Proof.
(* This is your safety_by_bonded_leakage lemma *)
exact: (safety_by_bonded_leakage alice_independence_pair alice_independence_v2).
Qed.

Lemma component_entropy_equals_solution_entropy :
  `H(v2 | alice_view) = log (m%:R) - log (m%:R) + log (m%:R).
Proof.
(* Simplification step *)
by rewrite subrr add0r.
Qed.

Lemma pair_entropy_via_conditioning :
  `H([% V2, V3] | alice_view) = `H([% V2, V3] | [% V1, U1, U2, U3, S]).
Proof.
(* By conditional independence from alice's randomness *)
(* Use alice_independence_pair and E_enc_ce_removal *)
Admitted.

Lemma pair_entropy_from_uniformity :
  `H([% V2, V3] | [% V1, U1, U2, U3, S]) = log (m%:R).
Proof.
exact: (@conditional_entropy_uniform_solutions T P v1 v2 v3 u1 u2 u3 s
         constraint_holds u3_nonzero uniform_over_solutions).
Qed.

(** ** Main Security Theorem *)

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

(** ** Interpretation *)

(* The adversary learns log(m) bits about v2, not 0 bits (perfect secrecy)
   but also not log(m^2) bits (complete knowledge).
   
   This is because:
   - There are m possible values for v2
   - Each is equally likely given alice_view
   - Entropy = log(m) bits
   
   Security holds despite information leakage.
*)

End DSDP_Security_Theorem.



*)

