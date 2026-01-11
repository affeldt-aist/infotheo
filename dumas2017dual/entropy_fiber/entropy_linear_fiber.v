From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap matrix lra reals.
From mathcomp Require Import mathcomp_extra.
From robot Require Import euclidean.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import entropy_fiber.
Require Import rouche_capelli.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*  Entropy Theory for Linear Maps and Bilinear Forms                         *)
(*                                                                            *)
(*  This file specializes the abstract fiber entropy theory to linear algebra *)
(*  structures, providing an ergonomic API for information-theoretic          *)
(*  applications while leveraging general linear algebra theorems.            *)
(*                                                                            *)
(*  Relationship to Rouché-Capelli Theory:                                    *)
(*  -------------------------------------                                     *)
(*  Many results in this file are specialized versions of general theorems    *)
(*  from rouche_capelli.v (Rouché-Capelli theorem and affine solution sets):  *)
(*                                                                            *)
(*  1. linear_fiber_card_eq                                             *)
(*     = Special case of: all affine solution sets for Ax = b with fixed A    *)
(*       have the same cardinality (translates of the kernel)                 *)
(*     [General: affine_eq_translate_kernel + card_translate]                 *)
(*                                                                            *)
(*  2. linear_fiber_card                                                      *)
(*     = For a single linear equation (1 × n matrix u), the solution set has  *)
(*       cardinality |K|^(n-1) where K is the field                           *)
(*     [General: count_affine_solutions_explicit with rank(u) = 1]            *)
(*                                                                            *)
(*  3. constrained_pairs_card                                                 *)
(*     = For a rank-1 system in 2 variables over F_m, there are m solutions   *)
(*     [General: count_affine_solutions_rank1]                                *)
(*                                                                            *)
(*  Why Keep These Specialized Versions?                                      *)
(*  ------------------------------------                                      *)
(*  - Domain-appropriate types: linear_fiber u s vs. affine_solutions         *)
(*  - Self-documenting: names reflect entropy/information-theoretic concepts  *)
(*  - Simpler hypotheses: "u != 0" vs. "rank A = 1"                           *)
(*  - Better proof automation in entropy contexts                             *)
(*  - Pedagogical value: constructive proofs show why results hold            *)
(*                                                                            *)
(*  Implementation Strategy:                                                  *)
(*  -----------------------                                                   *)
(*  Lemmas are proven as thin wrappers that:                                  *)
(*  1. Translate between entropy-centric and matrix-centric formulations      *)
(*  2. Prove equivalence of problem statements                                *)
(*  3. Apply general Rouché-Capelli theorems                                  *)
(*  4. Translate results back to the entropy domain                           *)
(*                                                                            *)
(*  This approach provides an ergonomic API while avoiding duplicate proof    *)
(*  effort and automatically benefiting from improvements to general theory.  *)
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

Section linear_functional.

(* Work over a finite field *)
Variable F : finFieldType.
Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Hypothesis prime_m : prime m.
Local Notation msg := 'F_m.

(* Dimension of the vector space *)
Variable n : nat.

(* Linear functional: represented as dot product with a fixed vector *)
(* TODO: reuse the coq-robot package when it is published *)
Definition linear_functional (u : 'rV[msg]_n) (v : 'rV[msg]_n) : msg :=
  u *d v.

(* Fiber of the linear functional: generate the set of solutions *)
Definition linear_fiber (u : 'rV[msg]_n) (s : msg) : {set 'rV[msg]_n} :=
  @fiber 'rV[msg]_n msg (linear_functional u) s.

(* Helper: non-zero row vectors have at least one non-zero entry *)
(* This is a simple utility kept as-is for convenience *)
Lemma row_neq0_exists (u : 'rV[msg]_n) :
  u != 0 -> exists i, u ord0 i != 0.
Proof.
move => u_neq0.
case: (boolP [exists i, u 0 i != 0]).
  by move=> /existsP.
move => /existsPn Hall.
exfalso.
move: u_neq0; apply/negP.
rewrite negbK.
apply/eqP/matrixP => i j.
rewrite mxE.
move: (Hall j).
rewrite negbK.
move/eqP.
have ->: i = ord0.
  by rewrite (ord1 i).
by [].
Qed.

(* Non-zero vectors give well-defined fibers *)
(* Constructive proof: explicitly builds a solution by choosing one coordinate *)
Lemma linear_fiber_nonzero (u : 'rV[msg]_n) :
  u != 0 ->
  forall s, (0 < #|linear_fiber u s|)%N.
Proof.
move=> u_neq0 s.
apply/card_gt0P.
(* If u ≠ 0, there exists an index i where u_i ≠ 0 *)
have [i ui_neq0]: exists i, u 0 i != 0.
  by exact: row_neq0_exists.
(* Construct a solution v where v_i is chosen to satisfy the equation *)
exists (s / u 0 i *: 'e_i).  
by rewrite inE /linear_functional dotmulvZ dotmul_delta_mx divfK.
Qed.

(* Helper: fiber cardinality equals kernel cardinality *)
Lemma linear_fiber_kernel_card (u : 'rV[msg]_n) (s : msg) (x0 : 'rV[msg]_n) :
  u *d x0 = s ->
  #|linear_fiber u s| = #|[set v : 'rV[msg]_n | u *d v == 0]|.
Proof.
move=> Hx0.
pose kernel := [set v : 'rV[msg]_n | u *d v == 0].
rewrite -(card_translate kernel x0).
apply: eq_card => v.
rewrite !inE /linear_functional.
apply/eqP.
case: ifPn.
  case /imsetP => k + ->.
  rewrite inE => /eqP Hk.
  by rewrite dotmulDr Hk addr0.
apply: contraNnot.
move => uvs.
apply/imsetP.
rewrite /=.
exists (v - x0) => //.
  by rewrite inE dotmulBr uvs Hx0 subrr.
by rewrite subrKC.
Qed.

(* Key result: all fibers of a non-zero linear functional have the same size *)
(* All fibers of a linear functional have equal cardinality.
   
   WHY THIS WRAPPER: The general Rouché-Capelli theory works with matrices Ax=b,
   but entropy applications use dot products u·v = s. This wrapper:
   1. Hides matrix notation - takes row vector u directly
   2. Provides the natural "for all targets s1, s2" interface
   3. Enables direct application in entropy_fiber.v's constant-fiber framework
   
   Mathematical content: fiber(s) = x₀ + ker(u) for any solution x₀,
   so |fiber(s₁)| = |ker(u)| = |fiber(s₂)|.
*)
Lemma linear_fiber_card_eq (u : 'rV[msg]_n) :
  u != 0 ->
  forall s1 s2, #|linear_fiber u s1| = #|linear_fiber u s2|.
Proof.
move=> u_neq0 s1 s2.

(* Find particular solutions in each fiber *)
have [x1 Hx1]: exists x, x \in linear_fiber u s1.
  by apply/card_gt0P; exact: (linear_fiber_nonzero u_neq0 s1).
have [x2 Hx2]: exists x, x \in linear_fiber u s2.
  by apply/card_gt0P; exact: (linear_fiber_nonzero u_neq0 s2).
(* Extract the equations from fiber membership *)
move: Hx1 Hx2; rewrite !inE /linear_functional => /eqP Hx1 /eqP Hx2.
by rewrite (linear_fiber_kernel_card Hx1) (linear_fiber_kernel_card Hx2).
Qed.

(* Helper: row vector kernel equals column vector kernel (via transpose) *)
Local Lemma row_kernel_eq_col_kernel (u : 'rV[msg]_n) :
  #|[set v : 'rV[msg]_n | u *d v == 0]| = 
  #|[set w : 'cV[msg]_n | u *m w == 0]|.
Proof.
(* Goal: #|[set v | u *d v == 0]| = #|[set w | u *m w == 0]| *)
(* Bijection: v : 'rV_n <-> v^T : 'cV_n *)
rewrite -(card_in_imset (f := fun (v : 'rV[msg]_n) => v^T)); last first.
  by move=> v1 v2 _ _; exact: trmx_inj.
(* Goal: #|[set v^T | v in [set v | u *d v == 0]]| = #|[set w | u *m w == 0]| *)
apply: eq_card => w.
apply/imsetP/idP.
(* Forward: v in row kernel => v^T in col kernel *)
- case=> v; rewrite !inE => /eqP Hv ->.
  (* Goal: u *m v^T == 0 *)
  (* By dotmulP: u *m v^T = (u *d v)%:M, and Hv: u *d v = 0 *)
  rewrite dotmulP Hv.
  (* Goal: 0%:M == 0 *)
  by apply/eqP/matrixP => i j; rewrite !mxE mul0rn.
(* Backward: w in col kernel => w^T in row kernel *)
- rewrite inE => /eqP Hw.
  exists w^T; last by rewrite trmxK.
  rewrite inE; apply/eqP.
  (* Goal: u *d w^T = 0 *)
  (* From dotmulP: u *m w = (u *d w^T)%:M, Hw: u *m w = 0 *)
  have H: u *m w = (u *d w^T)%:M by rewrite -dotmulP trmxK.
  move: Hw; rewrite H => /matrixP /(_ ord0 ord0).
  by rewrite !mxE eqxx mulr1n.
Qed.

(* Cardinality of linear fiber: |K|^(n-1) *)
(* Fiber cardinality for linear functional: |{v | u·v = s}| = |F|^(n-1).
   
   WHY THIS WRAPPER: The general count_affine_solutions_explicit requires:
   - A matrix A and target b
   - A particular solution x₀ with Ax₀ = b
   - Explicit rank computation
   
   This wrapper provides the cleaner entropy-focused API:
   - Takes coefficient vector u and target s directly  
   - Handles the rank(u) = 1 case (single equation) automatically
   - Returns |field|^(n-1) directly for use in log calculations
   
   Example: For 2D with |F| = m, fiber has m^1 = m elements ⟹ entropy = log(m).
*)
Lemma linear_fiber_card (u : 'rV[msg]_n) (s : msg) :
  u != 0 ->
  (n > 0)%N ->
  #|linear_fiber u s| = (#|msg| ^ n.-1)%N.
Proof.
move=> u_neq0 n_pos.

(* Find a particular solution *)
have [x0 Hx0]: exists x, x \in linear_fiber u s.
  by apply/card_gt0P; exact: (linear_fiber_nonzero u_neq0 s).
move: Hx0; rewrite inE /linear_functional => /eqP Hx0.

(* Fiber cardinality equals kernel cardinality *)
rewrite (linear_fiber_kernel_card Hx0).

(* Apply row_kernel_eq_col_kernel *)
rewrite row_kernel_eq_col_kernel.

(* Now: #|[set w : 'cV_n | u *m w == 0]| = |msg|^(n-1) *)
(* This is count_kernel_vectors_col *)
rewrite count_kernel_vectors_col.

(* Show \rank u = 1 for non-zero row vector *)
have rank_u: \rank u = 1.
  apply/eqP; rewrite eqn_leq; apply/andP; split.
    (* rank ≤ 1: only one row *)
    by rewrite rank_leq_row.
  (* rank ≥ 1: u ≠ 0 *)
  rewrite lt0n mxrank_eq0.
  apply/matrix0Pn.
  (* u is a row vector (1 row), so row index is ord0 : 'I_1 *)
  (* Find column index where u is non-zero *)
  have [j uj_neq0]: exists j : 'I_n, u ord0 j != 0.
    by exact: row_neq0_exists.
  exists (ord0 : 'I_1), j.
  exact: uj_neq0.
by rewrite rank_u /= subn1.
Qed.

End linear_functional.

Section bilinear_form.

Variable F : finFieldType.
Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Hypothesis prime_m : prime m.
Local Notation msg := 'F_m.

(* dotp is a local alias for dotmul from coq-robot *)
Definition dotp (n : nat) (u v : 'rV[msg]_n) : msg := u *d v.

(* Alternative sum formulation (for reference) *)
Lemma dotpE (n : nat) (u v : 'rV[msg]_n) :
  dotp u v = \sum_(i < n) u 0 i * v 0 i.
Proof. by rewrite /dotp dotmulE. Qed.

(* Solution set for bilinear constraint *)
Definition bilinear_solutions (n : nat) (u : 'rV[msg]_n) (s : msg) :
  {set 'rV[msg]_n} :=
  [set v | dotp u v == s].

(* Connection to linear_fiber: dotp = linear_functional = dotmul *)
Lemma bilinear_solutions_fiberE (n : nat) (u : 'rV[msg]_n) (s : msg) :
  bilinear_solutions u s = linear_fiber u s.
Proof. by []. Qed.

(* Inherit cardinality result *)
(* For general n, the fiber has |msg|^(n-1) elements *)
Lemma bilinear_solutions_card (n : nat) (u : 'rV[msg]_n) (s : msg) :
  u != 0 ->
  (n > 0)%N ->
  #|bilinear_solutions u s| = (#|msg| ^ n.-1)%N.
Proof.
move=> u_neq0 n_pos.
rewrite bilinear_solutions_fiberE.
by rewrite linear_fiber_card.
Qed.

End bilinear_form.

Section tuple_bilinear_form.

(* Specialization to 2D and 3D cases using tuples *)

Variable F : finFieldType.
Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Hypothesis prime_m : prime m.
Local Notation msg := 'F_m.

(* 2D dot product using tuples *)
Definition dotp2 (x y : msg * msg) : msg :=
  x.1 * y.1 + x.2 * y.2.

(* Solution pairs for 2D constraint *)
Definition dotp2_solutions (u : msg * msg) (s : msg) : {set msg * msg} :=
  [set v | dotp2 u v == s].

(* Convert tuple to row vector *)
Definition tuple2_to_row (xy : msg * msg) : 'rV[msg]_2 :=
  \row_(i < 2) [:: xy.1; xy.2]`_i.

(* dotp2 matches dotmul of row vectors *)
Lemma dotp2_eq_matrix (x y : msg * msg) :
  dotp2 x y = tuple2_to_row x *d tuple2_to_row y.
Proof.
rewrite /dotp2 dotmulE (bigD1 ord0) //= (bigD1 (lift ord0 ord0)) //=.
rewrite big_pred0 ?addr0; last by case => [[|[|k]]] //=.
by rewrite !mxE.
Qed.

(* Cardinality for 2D case *)
(* Direct application of count_affine_solutions_rank1 *)
Lemma dotp2_solutions_card (u : msg * msg) (s : msg) :
  u != (0, 0) ->
  #|dotp2_solutions u s| = m.
Proof.
move=> u_neq0.
(* Use count_affine_solutions_rank1 directly *)
rewrite /dotp2_solutions.
(* This is exactly the form proven in rouche_capelli.v *)
case: (boolP (u.2 != 0)) => [u2_neq0 | /negbNE /eqP u2_eq0].
  (* Case u.2 ≠ 0: direct application *)
  have ->: [set v | dotp2 u v == s] = 
           [set v : msg * msg | u.1 * v.1 + u.2 * v.2 == s].
    apply/setP => v.
    by rewrite !inE /dotp2.
  rewrite (@count_affine_solutions_rank1 msg u.1 u.2 s u2_neq0).
  by rewrite card_Fp // pdiv_id.
(* Case u.2 = 0: then u.1 ≠ 0 since u ≠ (0,0) *)
have u1_neq0: u.1 != 0.
  case: u u_neq0 u2_eq0 => [u1' u2'] /= u_neq0 u2_eq0.
  apply/contra: u_neq0 => /eqP ->.
  by rewrite xpair_eqE u2_eq0 eqxx.
(* Swap roles and apply the theorem *)
have ->: [set vv | u.1 * vv.1 + u.2 * vv.2 == s] =
         [set (vv.2, vv.1) | vv in [set vv' | u.2 * vv'.1 + u.1 * vv'.2 == s]].
  apply/setP => vv; rewrite !inE.
  apply/idP/imsetP.
    move/eqP => Hvv.
    exists (vv.2, vv.1); last first.
      rewrite /=.
      exact: surjective_pairing.
    by rewrite inE /= addrC; apply/eqP.
  move=> [[v2' v1']] /=; rewrite inE => /eqP Hv' ->.
  by rewrite /= addrC; apply/eqP.
rewrite card_imset; last first.
  move=> [x1 x2] [y1 y2] /= [Heq2 Heq1].
  by congr pair.
rewrite count_affine_solutions_rank1; last by exact: u1_neq0.
by rewrite card_Fp.
Qed.

End tuple_bilinear_form.

Section bilinear_entropy_applications.

(* Apply fiber entropy theory to bilinear constraints *)

Context {R : realType}.
Variable T : finType.
Variable P : R.-fdist T.
Variable F : finFieldType.
Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Hypothesis prime_m : prime m.
Local Notation msg := 'F_m.
Variable n : nat.

Variable U V : {RV P -> 'rV[msg]_n}.

(* S is the dot product of U and V *)
Let S : {RV P -> msg} := (fun t => U t *d V t).

(* Non-degeneracy: U is not zero *)
Hypothesis U_nonzero : forall t, U t != 0.

(* Uniform distribution over solutions *)
Hypothesis uniform_over_solutions : forall t u s,
  U t = u -> S t = s ->
  forall v,
    v \in linear_fiber u s ->
    `Pr[V = v | [% U, S] = (u, s)] = #|linear_fiber u s|%:R ^-1.

(* Main result: conditional entropy equals log(m) *)
Theorem centropy_bilinear_uniform :
  (n > 0)%N ->
  `H(V | [% U, S]) = log ((m ^ n.-1)%:R : R).
Proof.
move=> n_pos.
have card_m : #|msg| = m.
  by rewrite card_Fp.
have fiber_size: forall (u : 'rV[msg]_n) (s : msg),
  u != 0 -> #|linear_fiber u s| = (m ^ n.-1)%N.
  move=> u_vec s_val u_vec_neq0.
  rewrite (@linear_fiber_card m_minus_2 n u_vec s_val u_vec_neq0 n_pos).
  by rewrite card_m.
apply: (@centropy_jcond_determined_fibers 
         R T P 'rV[msg]_n 'rV[msg]_n msg 
         V U S 
         (fun v u => u *d v)).
  - by [].
  - move=> u s v Hus_neq0 v_in_fiber.
    rewrite inE in v_in_fiber.
    have ->: #|[set x' | (fun (v0 : 'rV[msg]_n) (u0 : 'rV[msg]_n) => 
                         u0 *d v0) x' u == s]| = 
             #|linear_fiber u s|.
      by apply: eq_card => v0; rewrite !inE /linear_functional.
    have [t [Ut_eq Us_eq]]: exists t, U t = u /\ S t = s.
      move/pfwd1_neq0: Hus_neq0 => [t Ht].
      exists t.
      split.
        case: Ht => [/= /eqP].
        case => Ut _ _; exact: Ut.
        case: Ht => [/= /eqP].
        by case => _ St _; exact: St.
    have v_in: v \in linear_fiber u s by rewrite inE.
    by rewrite (uniform_over_solutions Ut_eq Us_eq v_in).
  - move=> u s Hus_neq0.
    rewrite /linear_fiber.
    have u_neq0: u != 0.
      move/pfwd1_neq0: Hus_neq0 => [t Ht].
      move: Ht => [/= /eqP].
      move => [Ut_eq_u _] _.
      rewrite -Ut_eq_u.
      exact: U_nonzero.
    rewrite /linear_fiber.
    exact: (fiber_size u s u_neq0).
by rewrite expn_gt0; apply/orP; left; apply: prime_gt0 prime_m.
Qed.

End bilinear_entropy_applications.

Section multi_dimensional_solutions.
  
(* Theory for joint solution sets (V2, V3) pairs *)

Variable F : finFieldType.
Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Hypothesis prime_m : prime m.
Local Notation msg := 'F_m.

(* For constraint: s = u1*v1 + u2*v2 + u3*v3 with v1 fixed *)
(* Solution set is pairs (v2, v3) satisfying u2*v2 + u3*v3 = s - u1*v1 *)

Definition constrained_pairs (u2 u3 : msg) (target : msg) : 
  {set msg * msg} :=
  [set vv | u2 * vv.1 + u3 * vv.2 == target].

(* When u3 ≠ 0, this is a line in F_m × F_m with m points *)
(*
   Thin wrapper around count_affine_solutions_rank1 from rouche_capelli.v:
   For the rank-1 linear system u2*x + u3*y = target with u3 ≠ 0,
   there are exactly #|K| solutions.
   
   This is the EXACT theorem proven at line 409-520 of rouche_capelli.v.
*)
Lemma constrained_pairs_card (u2 u3 target : msg) :
  u3 != 0 ->
  #|constrained_pairs u2 u3 target| = m.
Proof.
move=> u3_neq0.
have ->: #|constrained_pairs u2 u3 target| = #|msg|.
  exact: (count_affine_solutions_rank1 u2 target u3_neq0).
by rewrite card_Fp.
Qed.

(* 3D constraint: s = u1*v1 + u2*v2 + u3*v3 *)
Definition constrained_triples (u1 u2 u3 : msg) (target : msg) : 
  {set msg * msg * msg} :=
  [set vvv | u1 * vvv.1.1 + u2 * vvv.1.2 + u3 * vvv.2 == target].

(* Convert triple to row vector *)
Definition tuple3_to_row (xyz : msg * msg * msg) : 'rV[msg]_3 :=
  \row_(i < 3) [:: xyz.1.1; xyz.1.2; xyz.2]`_i.

Definition triple_coeff_matrix (u1 u2 u3 : msg) : 'M[msg]_(1, 3) :=
  \matrix_(i < 1, j < 3) 
    (if j == ord0 then u1 
     else if j == lift ord0 ord0 then u2 
     else u3).

(* 
   constrained_triples_card: |{(v1,v2,v3) : u1*v1 + u2*v2 + u3*v3 = s}| = m^2
   
   STATUS: Aborted - not needed for DSDP protocol analysis
   
   REASON: In DSDP, only Alice (result-computing party) knows the constraint
   result s. Alice's view already includes v1, reducing the problem from 3D to 2D:
   
     Alice knows: v1, u1, u2, u3, s
     Alice infers: (v2, v3) from u2*v2 + u3*v3 = s - u1*v1
     Use: constrained_pairs_card gives |{(v2,v3)}| = m
   
   WHEN NEEDED: This 3D lemma would be required for protocols where:
   - Adversary sees only (u1,u2,u3,s) but NO variable values
     Example: External eavesdropper on constraint announcement
   - Multi-round leakage analysis: H(V1,V2,V3|U,S) before revelation
     then H(V2,V3|V1,U,S) after, measuring Δ = log(m^2) - log(m) = log(m)
   - Protocol composition: Multiple DSDP instances before any vi revealed
   
   For DSDP-specific version, see dsdp_solution_set_card_full in dsdp_algebra.v
*)
Lemma constrained_triples_card (u1 u2 u3 target : msg) :
  (u1 != 0) || (u2 != 0) || (u3 != 0) ->
  #|constrained_triples u1 u2 u3 target| = (m ^ 2)%N.
Proof.
Abort.

End multi_dimensional_solutions.

