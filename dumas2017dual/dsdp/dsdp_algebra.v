From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap matrix lra.
Require Import rouche_capelli.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter smc_tactics.
Require Import smc_proba homomorphic_encryption entropy_linear_fiber.
Require Import dsdp_program dsdp_extra.

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

Section fail_ring_rV_vs_M.

Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Local Notation msg := 'I_m.

Variable (mx : 'M[msg]_(1, 3)).
Fail Check \rank mx.
Locate "\rank".
About mxrank.body.

Variable F : finFieldType.
Local Notation msgF := 'F_m.
Variable (mxF : 'M[msgF]_(1, 3)).
Check \rank mxF.

End fail_ring_rV_vs_M.

Section dsdp_algebra.
  
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

(* The DSDP coefficient matrix has rank 1 when at least one coefficient is nonzero.
   This establishes the linear system has exactly 1 constraint, giving 2 degrees of freedom. *)
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

(* Fiber-ish definitions *)
Definition dsdp_fiber (u1 u2 u3 v1 s : msg) : {set msg * msg} :=
  constrained_pairs u2 u3 (s - u1 * v1).

(* Kernel cardinality: |ker(A)| = m^(n-r) = m^(3-1) = m^2 for rank-1 system.
   The kernel represents homogeneous solutions u1*v1 + u2*v2 + u3*v3 = 0. *)
Lemma dsdp_kernel_card u1 u2 u3 :
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

(* Fiber cardinality for pairs (v2, v3): |{(v2,v3) | u2*v2 + u3*v3 = s - u1*v1}| = m.
   With v1 fixed, the remaining 2-variable equation has m solutions (1 degree of freedom). *)
Lemma dsdp_fiber_card u1 u2 u3 v1 s :
  u3 != 0 ->
  #|dsdp_fiber u1 u2 u3 v1 s| = m.
Proof.
move=> Hu3neg0.
by apply: constrained_pairs_card.
Qed.

(* Full solution set cardinality: |{(v1,v2,v3) | u1*v1 + u2*v2 + u3*v3 = s}| = m^2.
   One constraint in 3 variables gives 2 degrees of freedom, hence m^2 solutions. *)
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

End dsdp_algebra.


