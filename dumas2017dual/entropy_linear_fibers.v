From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap matrix lra.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import entropy_fibers.
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
(*  1. linear_fiber_constant_size                                             *)
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

Local Definition R := Rdefinitions.R.

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
  (u *m v^T) 0 0.

(* Fiber of the linear functional *)
(* TODO: use the fiber definition *)
Definition linear_fiber (u : 'rV[msg]_n) (s : msg) : {set 'rV[msg]_n} :=
  [set v | linear_functional u v == s].

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
exists (\row_j if j == i then s / u 0 i else 0).
rewrite inE /linear_functional !mxE.
apply/eqP.
rewrite (bigD1 i) //= !mxE eqxx.
rewrite big1 ?addr0.
  field.
  exact: ui_neq0.
move=> j j_neq_i.
by rewrite mxE mxE (negbTE j_neq_i) mulr0.
Qed.

(* Helper: fiber cardinality equals kernel cardinality *)
Lemma linear_fiber_eq_kernel_card (u : 'rV[msg]_n) (s : msg) (x0 : 'rV[msg]_n) :
  (u *m x0^T) ord0 ord0 = s ->
  #|linear_fiber u s| = #|[set v : 'rV[msg]_n | (u *m v^T) ord0 ord0 == 0]|.
Proof.
move=> Hx0.
pose kernel := [set v : 'rV[msg]_n | (u *m v^T) ord0 ord0 == 0].
rewrite -(card_translate kernel x0).
apply: eq_card => v.
rewrite !inE /linear_functional.
apply/eqP.
case: (boolP (v \in [set x0 + s0 | s0 in kernel])) => [Hin | Hnotin].
  rewrite mxE.
  move: Hin => /imsetP [k Hk ->].
  move: Hk; rewrite inE => /eqP Hk.
  under eq_bigr do rewrite mxE.
  under eq_bigr do rewrite mxE mulrDr.
  rewrite big_split /=.
  (* First sum: \sum u 0 i * x0 0 i = (u *m x0^T) ord0 ord0 = s *)
  have ->: \sum_(i < n) u 0 i * x0 0 i = (u *m x0^T) ord0 ord0.
    rewrite !mxE.
    apply: eq_bigr => i _.
    by rewrite !mxE.
  rewrite Hx0.
  (* Second sum: \sum u 0 i * k 0 i = (u *m k^T) ord0 ord0 = 0 *)
  have ->: \sum_(i < n) u 0 i * k 0 i = (u *m k^T) ord0 ord0.
    rewrite !mxE.
    apply: eq_bigr => i _.
    by rewrite !mxE.
  by rewrite Hk addr0.
move=> Heq.
(* Assume (u *m v^T) 0 0 = s *)
(* Then v - x0 is in the kernel *)
have Hk: (v - x0) \in kernel.
  rewrite inE; apply/eqP.
  rewrite !mxE.
  under eq_bigr do rewrite mxE.
  under eq_bigr do rewrite mxE mulrDr.
  rewrite big_split /=.
  have ->: \sum_(i < n) u ord0 i * (- x0) ord0 i = 
           \sum_(i < n) u ord0 i * (- (x0 ord0 i)).
    apply: eq_bigr => i _.
    by congr (_ * _); rewrite mxE.  
  have ->: \sum_(i < n) u ord0 i * (- (x0 ord0 i)) = 
           - \sum_(i < n) u ord0 i * x0 ord0 i.
    rewrite -sumrN; apply: eq_bigr => i _.
    by rewrite mulrN.
  have ->: \sum_(i < n) u ord0 i * v ord0 i = (u *m v^T) ord0 ord0.
    rewrite mxE; apply: eq_bigr => i _.
    by rewrite !mxE.
  have ->: \sum_(i < n) u ord0 i * x0 ord0 i = (u *m x0^T) ord0 ord0.
    rewrite mxE; apply: eq_bigr => i _.
    by rewrite !mxE.
  by rewrite Heq Hx0 subrr.
have Hin: v \in [set x0 + s0 | s0 in kernel].
  apply/imsetP.
  exists (v - x0) => //.
  by rewrite addrC subrK.
by move: Hnotin; rewrite Hin.
Qed.

(* Key result: all fibers of a non-zero linear functional have the same size *)
(* 
   Thin wrapper around Rouché-Capelli Theory:
   ------------------------------------------
   This is a direct consequence of the general result that all affine solution 
   sets {x | Ax = b_i} for fixed A have equal cardinality (they are translates 
   of the kernel). See: affine_eq_translate_kernel + card_translate in 
   rouche_capelli.v. The usage of these two lemmas are in the major helper
   linear_fiber_eq_kernel_card.
*)
Lemma linear_fiber_constant_size (u : 'rV[msg]_n) :
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
by rewrite (linear_fiber_eq_kernel_card Hx1) (linear_fiber_eq_kernel_card Hx2).
Qed.

(* Helper: row vector kernel equals column vector kernel (via transpose) *)
Local Lemma row_kernel_eq_col_kernel (u : 'rV[msg]_n) :
  #|[set v : 'rV[msg]_n | (u *m v^T) ord0 ord0 == 0]| = 
  #|[set w : 'cV[msg]_n | u *m w == 0]|.
Proof.
(* Bijection: v : 'rV_n <-> v^T : 'cV_n *)
rewrite -(card_in_imset (f := fun (v : 'rV[msg]_n) => v^T)); last first.
  (* Injectivity of transpose *)
  by move=> v1 v2 _ _; exact: trmx_inj.

(* Show: [set v^T | v in row_kernel] = col_kernel *)
apply: eq_card => w.
apply/imsetP/idP.

(* Forward: if w = v^T and v in row kernel, then w in col kernel *)
- case=> v; rewrite !inE => /eqP Hv ->.
  (* Goal: u *m v^T == 0 *)
  apply/eqP.
  (* Use that (u *m v^T) ord0 ord0 = 0 implies u *m v^T = 0 *)
  apply/matrixP => i j.
  (* Both indices are ord0 since it's 1x1 matrix *)
  have ->: i = ord0 by apply: ord1.
  have ->: j = ord0 by apply: ord1.
  (* Now: (u *m v^T) ord0 ord0 = 0 ord0 ord0 *)
  by rewrite Hv mxE.

(* Backward: if w in col kernel, then w = (w^T)^T with w^T in row kernel *)
- rewrite inE => /eqP Hw.
  exists w^T; last by rewrite trmxK.
  rewrite inE; apply/eqP.
  (* Goal: (u *m (w^T)^T) ord0 ord0 = 0 *)
  rewrite trmxK.
  (* Now: (u *m w) ord0 ord0 = 0 *)
  move: Hw => /matrixP /(_ ord0 ord0) ->.
  by rewrite mxE.
Qed.

(* Cardinality of linear fiber: |K|^(n-1) *)
(*
   Thin wrapper around count_affine_solutions_explicit from rouche_capelli.v:
   --------------------------------------------------------------------------
   For a single linear equation u·x = s where u is a non-zero row vector,
   the solution set has cardinality |K|^(n-1) since rank(u) = 1.
   
   This follows directly from the general Rouché-Capelli formula:
   #|{x | Ax = b}| = |K|^(n - rank(A))
   
   In our case: A = u (1×n matrix), rank(u) = 1 (u ≠ 0), so we get |K|^(n-1).
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
rewrite (linear_fiber_eq_kernel_card Hx0).

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

Definition dotp (n : nat) (u v : 'rV[msg]_n) : msg :=
  \sum_(i < n) u 0 i * v 0 i.

(* Alternative matrix formulation *)
Lemma dotpE (n : nat) (u v : 'rV[msg]_n) :
  dotp u v = (u *m v^T) 0 0.
Proof.
rewrite /dotp !mxE.
by apply: eq_bigr => i _; rewrite !mxE.
Qed.

(* Solution set for bilinear constraint *)
Definition bilinear_solutions (n : nat) (u : 'rV[msg]_n) (s : msg) :
  {set 'rV[msg]_n} :=
  [set v | dotp u v == s].

(* Connection to linear_fiber *)
Lemma bilinear_solutions_eq_fiber (n : nat) (u : 'rV[msg]_n) (s : msg) :
  bilinear_solutions u s = linear_fiber u s.
Proof.
apply/setP => v.
by rewrite !inE /linear_functional dotpE.
Qed.

(* Inherit cardinality result *)
(* For general n, the fiber has |msg|^(n-1) elements *)
Lemma bilinear_solutions_card (n : nat) (u : 'rV[msg]_n) (s : msg) :
  u != 0 ->
  (n > 0)%N ->
  #|bilinear_solutions u s| = (#|msg| ^ n.-1)%N.
Proof.
move=> u_neq0 n_pos.
rewrite bilinear_solutions_eq_fiber.
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

(* dotp2 matches matrix dot product *)
Lemma dotp2_eq_matrix (x y : msg * msg) :
  dotp2 x y = (tuple2_to_row x *m (tuple2_to_row y)^T) 0 0.
Proof.
rewrite /dotp2 !mxE.
rewrite (bigD1 ord0) //=.
rewrite (bigD1 (lift ord0 ord0)) //=.
rewrite big_pred0 ?addr0; last first.
  move => i.
  rewrite andbC /=.
  by case: i => [[|[|k]]] //= Hn.
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
Let S : {RV P -> msg} := (fun t => (U t *m (V t)^T) 0 0).

(* Non-degeneracy: U is not zero *)
Hypothesis U_nonzero : forall t, U t != 0.

(* Uniform distribution over solutions *)
Hypothesis uniform_over_solutions : forall t u s,
  U t = u -> S t = s ->
  forall v,
    v \in linear_fiber u s ->
    `Pr[V = v | [% U, S] = (u, s)] = #|linear_fiber u s|%:R ^-1.

(* Main result: conditional entropy equals log(m) *)
Theorem bilinear_centropy_uniform :
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
apply: (@centropy_with_functional_constraint 
         T P 'rV[msg]_n 'rV[msg]_n msg 
         V U S 
         (fun v u => (u *m v^T) 0 0)).
  - by [].
  - move=> u s v Hus_neq0 v_in_fiber.
    rewrite inE in v_in_fiber.
    have ->: #|[set x' | (fun (v0 : 'rV[msg]_n) (u0 : 'rV[msg]_n) => 
                         (u0 *m v0^T) 0 0) x' u == s]| = 
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

End multi_dimensional_solutions.

