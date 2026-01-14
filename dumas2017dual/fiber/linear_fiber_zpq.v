From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap lra.
From mathcomp Require Import mathcomp_extra.
From robot Require Import euclidean.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import extra_algebra extra_proba extra_entropy entropy_fiber.
Require Import rouche_capelli.  (* For count_affine_solutions_rank1 *)

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* Linear fiber framework over composite modulus Z/pqZ                        *)
(*                                                                            *)
(* This file provides a general framework for computing fiber cardinalities   *)
(* over the ring Z/(pq)Z where p, q are distinct primes.                      *)
(*                                                                            *)
(* Key insight from CRT:                                                      *)
(*   Z/pqZ ≅ Z/pZ × Z/qZ  (when gcd(p,q) = 1)                                 *)
(*                                                                            *)
(* This file works over 'Z_m (ring, m = p*q composite).                       *)
(* For prime fields 'F_m, a simpler approach was previously in                *)
(* entropy_linear_fiber.v (now removed as out of scope).                      *)
(*                                                                            *)
(* For constraints of the form u · v = target (dot product):                  *)
(*   - 1 equation, n unknowns → n-1 degrees of freedom                        *)
(*   - Fiber cardinality: m^(n-1) when some u_i is invertible (unit)          *)
(*                                                                            *)
(* Security condition: u_i < min(p,q) ensures u_i is coprime to m,            *)
(* hence invertible in Z/m (since it can't be divisible by p or q).           *)
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

(* ========================================================================== *)
(*              Generalized linear fiber over Z/pqZ (dimension n)             *)
(* ========================================================================== *)

(*
=== MATHEMATICAL PROOF STRATEGY ===

Statement: For u ∈ (Z/m)^n with some u_i invertible,
           |{v ∈ (Z/m)^n | u · v = target}| = m^(n-1)

Why it's true:
  - One linear equation in n unknowns gives n-1 free variables
  - Fix pivot index i where u_i is a unit (invertible)
  - For any choice of v_j (j ≠ i), solve: v_i = (target - Σ_{j≠i} u_j*v_j) / u_i
  - This gives m^(n-1) solutions (m choices for each of n-1 free variables)

Proof approach:
  1. Construct bijection f : (Z/m)^(n-1) → fiber
  2. f assigns free variables to v_j (j ≠ i), computes v_i from constraint
  3. Show f is injective (free components determine the vector)
  4. Show f maps into fiber (constraint satisfied by construction)
  5. Show f is surjective (every fiber element arises from f)
  6. Conclude: |fiber| = |(Z/m)^(n-1)| = m^(n-1)

Required lemmas:
  - coprime_Zp_unit: coprime to m implies unit in Z/m
  - GRing.mulrV, GRing.mulrK: division properties for units
  - card_ord, card_mx: cardinality of ordinals and matrices

===================================
*)

Section linear_fiber.

Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Hypothesis prime_p : prime p.
Hypothesis prime_q : prime q.
Hypothesis coprime_pq : coprime p q.
Local Notation m := (p * q).
Local Notation msg := 'Z_m.

(* Dimension of vector space *)
Variable n : nat.
Hypothesis n_pos : (0 < n)%N.

(* m > 1 since p, q are primes (each ≥ 2) *)
Let m_gt1 : (1 < m)%N.
Proof.
have Hp_gt1: (1 < p)%N by exact: prime_gt1.
have Hq_gt0: (0 < q)%N by exact: prime_gt0.
by rewrite (leq_trans Hp_gt1) // leq_pmulr.
Qed.

(* Linear functional over Z/pqZ: dot product u · v *)
Definition linear_functional (u : 'rV[msg]_n) (v : 'rV[msg]_n) : msg :=
  u *d v.

(* Generalized fiber: solutions to u · v = target over Z/m *)
Definition linear_fiber (u : 'rV[msg]_n) (target : msg) :
  {set 'rV[msg]_n} :=
  [set v : 'rV[msg]_n | u *d v == target].

(*
  ==========================================================================
  Helper lemmas for linear_fiber_card
  ==========================================================================
  
  Strategy: Use bijection between 'rV[msg]_n and (msg * 'rV[msg]_n.-1)
  
  Key insight: For any fixed values of v_j (j ≠ i), there's exactly one v_i
  such that u · v = target. This v_i = (target - Σ_{j≠i} u_j*v_j) / u_i.
  
  We construct the bijection in two steps:
  1. fiber ≅ msg via projection to non-pivot coordinates + solving for pivot
  2. Actually, simpler: show |fiber| = m^(n-1) directly via injection/surjection
  
  Alternative approach (simpler for Coq):
  - Use that every fiber element is uniquely determined by n-1 free coordinates
  - Construct bijection f : 'rV[msg]_n -> msg where f(v) = v_i (pivot coord)
  - The fiber is exactly the preimage of the unique solution
*)

(* 
   For n=1, the fiber is either empty or singleton.
   We handle this case separately.
*)

(* Helper: dot product expansion isolating index i *)
Lemma dotmul_bigD1 (u v : 'rV[msg]_n) (i : 'I_n) :
  u *d v = u ord0 i * v ord0 i + \sum_(j < n | j != i) u ord0 j * v ord0 j.
Proof.
(* Expand dot product and isolate term at index i *)
by rewrite dotmulE (bigD1 i) //=;
   congr (_ + _);apply: eq_bigl => j; rewrite andbC.
Qed.

(* Helper: unit cancellation - x * y / x = y when x is a unit *)
Lemma unitrK (x y : msg) :
  x \is a GRing.unit -> x * y / x = y.
Proof.
move=> Hunit.
(* x * y / x = x * y * x^-1 *)
(* = x * (y * x^-1) = x * (x^-1 * y) = (x * x^-1) * y = 1 * y = y *)
rewrite -mulrA [y * x^-1]mulrC mulrA.
(* Goal: x / x * y = y, i.e., x * x^-1 * y = y *)
rewrite mulrV //.
by rewrite mul1r.
Qed.

(* For vectors u, v : 'I_n → Z_m with u·v = target and u(i) invertible,  *)
(* the pivot coordinate v(i) is determined by the free coordinates:      *)
(*   v(i) = (target - Σ_{j≠i} u(j)*v(j)) / u(i)                          *)
Lemma pivot_solveE (u v : 'rV[msg]_n) (target : msg) (i : 'I_n) :
  u ord0 i \is a GRing.unit ->
  u *d v = target ->
  v ord0 i = (target - \sum_(j < n | j != i) u ord0 j * v ord0 j) *
               (u ord0 i)^-1.
Proof.
move=> Hui_unit Hdot.
(* Expand dot product isolating index i *)
rewrite (dotmul_bigD1 u v i) in Hdot.
(* Hdot: u ord0 i * v ord0 i + sum = target *)
(* Goal: v ord0 i = (target - sum) * (u ord0 i)^-1 *)
have Heq: u ord0 i * v ord0 i = target - \sum_(j < n | j != i) u ord0 j *
                                           v ord0 j.
  by rewrite -Hdot addrK.
rewrite -Heq.
(* Goal: v ord0 i = u ord0 i * v ord0 i / u ord0 i *)
by rewrite unitrK.
Qed.

(* Helper: constructing a fiber element from free coordinates *)
(* Given "free" values for all j ≠ i, compute the unique v_i *)
Definition make_fiber_elem (u : 'rV[msg]_n) (target : msg) (i : 'I_n) 
  (free : 'I_n -> msg) : 'rV[msg]_n :=
  \row_(j < n) 
    if j == i then 
      (target - \sum_(k < n | k != i) u ord0 k * free k) * (u ord0 i)^-1
    else 
      free j.

(* Helper: make_fiber_elem is in the fiber when u_i is a unit *)
Lemma make_fiber_elemP (u : 'rV[msg]_n) (target : msg) (i : 'I_n)
  (free : 'I_n -> msg) :
  u ord0 i \is a GRing.unit ->
  make_fiber_elem u target i free \in linear_fiber u target.
Proof.
move=> Hui_unit.
rewrite inE /make_fiber_elem.
apply/eqP.
(* Expand dot product at index i *)
rewrite (dotmul_bigD1 _ _ i).
(* Goal: u ord0 i * (row...)_i + sum = target *)
(* Row access: (\row_j f j) ord0 k = f k *)
rewrite mxE /= eqxx.
(* Let S := \sum_(j != i) u_j * free_j *)
set S := \sum_(j < n | j != i) u ord0 j * free j.
set pivot := (target - S) / u ord0 i.
(* Simplify the sum: for j != i, row element is free j *)
have Hsum_eq: \sum_(j < n | j != i) u ord0 j *
                (\row_k (if k == i then pivot else free k)) ord0 j = S.
  rewrite /S; apply: eq_bigr => j Hji.
  by rewrite mxE /= (negbTE Hji).
rewrite Hsum_eq.
(* Now: u_i * pivot + S = target *)
rewrite /pivot mulrCA mulrV //.
(* Goal: (target - S) * 1 + S = target *)
rewrite mulr1.
(* Goal: target - S + S = target *)
by rewrite subrK.
Qed.

(* For vectors v1, v2 : 'I_n → Z_m in the fiber {v | u·v = target},    *)
(* if v1(j) = v2(j) for all j ≠ i (free coordinates),                  *)
(* then v1 = v2 (the pivot coordinate v(i) is uniquely determined).    *)
Lemma fiber_elem_inj (u : 'rV[msg]_n) (target : msg) (i : 'I_n)
  (v1 v2 : 'rV[msg]_n) :
  u ord0 i \is a GRing.unit ->
  v1 \in linear_fiber u target ->
  v2 \in linear_fiber u target ->
  (forall j, j != i -> v1 ord0 j = v2 ord0 j) ->
  v1 = v2.
Proof.
move=> Hui_unit Hv1 Hv2 Hsame_free.
apply/rowP => j.
case: (altP (j =P i)) => [->|Hji].
- (* j = i: pivot coordinate determined by constraint *)
  move: Hv1 Hv2; rewrite !inE => /eqP Hdot1 /eqP Hdot2.
  rewrite (pivot_solveE Hui_unit Hdot1).
  rewrite (pivot_solveE Hui_unit Hdot2).
  (* Goal: (target - sum1) / u_i = (target - sum2) / u_i *)
  (* Since sum1 = sum2 (by Hsame_free), they're equal *)
  congr (_ * _).
  congr (_ - _).
  apply: eq_bigr => k Hk.
  by rewrite Hsame_free.
- (* j ≠ i: free coordinate, same by hypothesis *)
  by apply: Hsame_free.
Qed.

(* Helper: cardinality of ffuns with one coordinate fixed to 0 *)
(* ========================================================================== *)
(*  Bijection between {f : 'I_n → Z_m | f(i) = 0} and {g : 'I_n.-1 → Z_m}     *)
(* ========================================================================== *)

(* restrict : ('I_n → Z_m) → ('I_n.-1 → Z_m), drops coordinate i *)
Definition ffun_restrict (i : 'I_n) (ff : {ffun 'I_n -> msg}) :
  {ffun 'I_n.-1 -> msg} :=
  [ffun j => ff (lift i j)].

(* extend : ('I_n.-1 → Z_m) → ('I_n → Z_m), inserts 0 at coordinate i *)
Definition ffun_extend (i : 'I_n) (g : {ffun 'I_n.-1 -> msg}) :
  {ffun 'I_n -> msg} :=
  [ffun j => if unlift i j is Some k then g k else 0].

(* extend maps into {f | f(i) = 0} *)
Lemma ffun_extendP (i : 'I_n) (g : {ffun 'I_n.-1 -> msg}) :
  ffun_extend i g \in [set ff : {ffun 'I_n -> msg} | ff i == 0].
Proof. by rewrite inE /ffun_extend ffunE unlift_none. Qed.

(* restrict ∘ extend = id *)
Lemma ffun_restrictK (i : 'I_n) : cancel (ffun_extend i) (ffun_restrict i).
Proof.
move=> g; apply/ffunP => j.
by rewrite /ffun_restrict /ffun_extend !ffunE liftK.
Qed.

(* extend ∘ restrict = id on {f | f(i) = 0} *)
Lemma ffun_extendK (i : 'I_n) (ff : {ffun 'I_n -> msg}) :
  ff i = 0 -> ffun_extend i (ffun_restrict i ff) = ff.
Proof.
move=> Hffi0; apply/ffunP => j.
rewrite /ffun_extend /ffun_restrict !ffunE.
case: (unliftP i j) => [k Hj|Hj].
- by rewrite ffunE Hj.
- by rewrite Hj Hffi0.
Qed.

(* extend is injective *)
Lemma ffun_extend_inj (i : 'I_n) : injective (ffun_extend i).
Proof.
move=> g1 g2 Heq.
by rewrite -(ffun_restrictK i g1) -(ffun_restrictK i g2) Heq.
Qed.

(*
    Counting: |{f : 'I_n → Z_m | f(i) = 0}| = m^(n-1)
    
    f(0) ∈ {0,1,...,m-1}     → m choices
    ...
    f(i) = 0                 → 1 choice (FIXED!)
    ...
    f(n-1) ∈ {0,1,...,m-1}   → m choices
    ─────────────────────────────────────
    Total: m^(n-1) functions (one less free coordinate)
*)
Lemma ffun_fix_coord_card (i : 'I_n) :
  #|[set ff : {ffun 'I_n -> msg} | ff i == 0]| = (m ^ n.-1)%N.
Proof.
have extend_inj: injective (ffun_extend i) by exact: ffun_extend_inj.
have Hcard_eq: #|[set ff : {ffun 'I_n -> msg} | ff i == 0]| =
  #|[set: {ffun 'I_n.-1 -> msg}]|.
  apply/eqP; rewrite eqn_leq; apply/andP; split.
  - (* <= : every element is extend of some g *)
    rewrite -(card_imset _ extend_inj).
    apply: subset_leq_card.
    apply/subsetP => ff; rewrite inE => /eqP Hff.
    apply/imsetP; exists (ffun_restrict i ff); first by rewrite inE.
    by rewrite ffun_extendK.
  - (* >= : extend maps into the target set *)
    rewrite -(card_imset _ extend_inj).
    apply: subset_leq_card.
    apply/subsetP => x /imsetP [g _ ->].
    exact: (ffun_extendP i).
rewrite Hcard_eq cardsT card_ffun !card_ord Zp_cast //.
Qed.

(* ========================================================================== *)
(*  Fiber as image of make_fiber_elem over representative set                 *)
(* ========================================================================== *)

(* Kernel of evaluation at coordinate i: ker(ev_i) = {f | f(i) = 0} *)
Let ker_eval (i : 'I_n) := [set f : {ffun 'I_n -> msg} | f i == 0].

(* mk: maps ffun to fiber element via make_fiber_elem *)
Let mk_fiber (u : 'rV[msg]_n) (target : msg) (i : 'I_n) 
  (f : {ffun 'I_n -> msg}) : 'rV[msg]_n :=
  make_fiber_elem u target i f.

(* The fiber {v | u·v = target} equals the image of mk_fiber over ker_eval *)
Let linear_fiber_imsetE (u : 'rV[msg]_n) (target : msg) (i : 'I_n) :
  u ord0 i \is a GRing.unit ->
  linear_fiber u target = mk_fiber u target i @: ker_eval i.
Proof.
move=> Hui_unit.
apply/setP => v.
rewrite inE.
apply/idP/imsetP.
- (* v in fiber -> exists f in ker_eval with v = mk_fiber f *)
  move=> Hv.
  pose f := [ffun j => if j == i then 0 else v ord0 j] : {ffun 'I_n -> msg}.
  exists f.
  + by rewrite inE ffunE eqxx.
  + have Hmk_in: mk_fiber u target i f \in linear_fiber u target.
      by apply: make_fiber_elemP.
    have Hv': v \in linear_fiber u target by rewrite inE.
    have Hsame: forall j, j != i -> v ord0 j = (mk_fiber u target i f) ord0 j.
      move=> j Hji.
      by rewrite /mk_fiber /make_fiber_elem mxE (negbTE Hji) ffunE (negbTE Hji).
    exact: (fiber_elem_inj Hui_unit Hv' Hmk_in Hsame).
- (* v = mk_fiber f for f in ker_eval -> v in fiber *)
  move=> [f Hf ->].
  have Hgoal: mk_fiber u target i f \in linear_fiber u target.
    by apply: make_fiber_elemP.
  by move: Hgoal; rewrite /linear_fiber !inE.
Qed.

(* mk_fiber is injective on ker_eval *)
Let mk_fiber_inj (u : 'rV[msg]_n) (target : msg) (i : 'I_n) :
  u ord0 i \is a GRing.unit ->
  {in ker_eval i &, injective (mk_fiber u target i)}.
Proof.
move=> Hui_unit f1 f2 Hf1 Hf2 Heq.
apply/ffunP => j.
case: (altP (j =P i)) => [->|Hji].
+ by move: Hf1 Hf2; rewrite !inE => /eqP -> /eqP ->.
+ have Hv1: mk_fiber u target i f1 \in linear_fiber u target
    by exact: make_fiber_elemP.
  have Hv2: mk_fiber u target i f2 \in linear_fiber u target
    by exact: make_fiber_elemP.
  have Hfree: forall k, k != i -> (mk_fiber u target i f1) ord0 k =
                                    (mk_fiber u target i f2) ord0 k.
    by move: Heq => ->.
  move: (Hfree j Hji).
  by rewrite /mk_fiber /make_fiber_elem !mxE (negbTE Hji).
Qed.

(*
  Main cardinality theorem for generalized linear fiber.
  
  When u has a unit component at index i:
    |linear_fiber u target| = m^(n-1)
*)
Lemma linear_fiber_card (u : 'rV[msg]_n) (target : msg) (i : 'I_n) :
  u ord0 i \is a GRing.unit ->
  #|linear_fiber u target| = (m ^ n.-1)%N.
Proof.
move=> Hui_unit.
rewrite (@linear_fiber_imsetE u target i Hui_unit).
rewrite (card_in_imset (@mk_fiber_inj u target i Hui_unit)).
exact: ffun_fix_coord_card.
Qed.

(*
   Key lemma: u < min(p,q) implies u is coprime to pq.
   Since 0 < u < min(p,q), we have:
   - u is not divisible by p (since u < p)
   - u is not divisible by q (since u < q)
   Therefore gcd(u, pq) = 1, so u is a unit in Z/pq.
*)
Lemma lt_minpq_coprime (u : msg) :
  (0 < u)%N -> (u < minn p q)%N ->
  coprime (nat_of_ord u) m.
Proof.
move=> Hu_pos Hu_lt.
rewrite /coprime.
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

End linear_fiber.


(* ========================================================================== *)
(*       2D specialization: fiber over pairs (v2, v3) : msg × msg             *)
(* ========================================================================== *)

(*
  This section provides the interface for dsdp_entropy.v which uses pairs
  (v2, v3) : msg × msg rather than row vectors 'rV[msg]_2.
  
  Main result: linear_fiber_2d_card proves |{(v2,v3) | u2*v2+u3*v3=s}| = m.
  
  CRT Projections (proj_Fp, proj_Fq) are provided for applying field-based
  theorems (rouche_capelli.v) to ring problems via CRT decomposition.
*)

Section fiber_2d.

Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Hypothesis prime_p : prime p.
Hypothesis prime_q : prime q.
Hypothesis coprime_pq : coprime p q.
Local Notation m := (p * q).
Local Notation msg := 'Z_m.

Let m_gt1 : (1 < m)%N.
Proof.
have Hp_gt1: (1 < p)%N by exact: prime_gt1.
have Hq_gt0: (0 < q)%N by exact: prime_gt0.
by rewrite (leq_trans Hp_gt1) // leq_pmulr.
Qed.

Let p_gt1 : (1 < p)%N := prime_gt1 prime_p.
Let q_gt1 : (1 < q)%N := prime_gt1 prime_q.

(* ========================================================================== *)
(*  CRT Projections: Z/(pq)Z → F_p and Z/(pq)Z → F_q                          *)
(* ========================================================================== *)

(* Project from 'Z_m to 'F_p by taking value mod p *)
Definition proj_Fp (x : msg) : 'F_p := inZp (val x).

(* Project from 'Z_m to 'F_q by taking value mod q *)
Definition proj_Fq (x : msg) : 'F_q := inZp (val x).

(* Projections are ring homomorphisms *)
Lemma proj_Fp_add (x y : msg) : proj_Fp (x + y)%R = (proj_Fp x + proj_Fp y)%R.
Proof.
rewrite /proj_Fp; apply/eqP; rewrite eqE /= !Fp_cast //.
by rewrite modn_dvdm ?modnDm // Zp_cast // dvdn_mulr.
Qed.

Lemma proj_Fp_mul (x y : msg) : proj_Fp (x * y)%R = (proj_Fp x * proj_Fp y)%R.
Proof.
rewrite /proj_Fp; apply/eqP; rewrite eqE /= !Fp_cast //.
by rewrite modn_dvdm ?modnMm // Zp_cast // dvdn_mulr.
Qed.

Lemma proj_Fq_add (x y : msg) : proj_Fq (x + y)%R = (proj_Fq x + proj_Fq y)%R.
Proof.
rewrite /proj_Fq; apply/eqP; rewrite eqE /= !Fp_cast //.
by rewrite modn_dvdm ?modnDm // Zp_cast // dvdn_mull.
Qed.

Lemma proj_Fq_mul (x y : msg) : proj_Fq (x * y)%R = (proj_Fq x * proj_Fq y)%R.
Proof.
rewrite /proj_Fq; apply/eqP; rewrite eqE /= !Fp_cast //.
by rewrite modn_dvdm ?modnMm // Zp_cast // dvdn_mull.
Qed.

(* Fiber over F_p: solutions to u2*v2 + u3*v3 = target *)
Definition fiber_Fp (u2 u3 target : 'F_p) : {set 'F_p * 'F_p} :=
  [set vv : 'F_p * 'F_p | u2 * vv.1 + u3 * vv.2 == target].

(* Fiber over F_q *)
Definition fiber_Fq (u2 u3 target : 'F_q) : {set 'F_q * 'F_q} :=
  [set vv : 'F_q * 'F_q | u2 * vv.1 + u3 * vv.2 == target].

(* Field fiber cardinality via count_affine_solutions_rank1 from rouche_capelli.v *)
Lemma fiber_Fp_card (u2 u3 target : 'F_p) :
  u3 != 0 -> #|fiber_Fp u2 u3 target| = p.
Proof.
move=> Hu3; rewrite /fiber_Fp.
by rewrite count_affine_solutions_rank1 // card_Fp.
Qed.

Lemma fiber_Fq_card (u2 u3 target : 'F_q) :
  u3 != 0 -> #|fiber_Fq u2 u3 target| = q.
Proof.
move=> Hu3; rewrite /fiber_Fq.
by rewrite count_affine_solutions_rank1 // card_Fp.
Qed.

(* ========================================================================== *)
(*  CRT Helper Lemmas for Dependent Type Handling                             *)
(* ========================================================================== *)

(*
  These helpers do rewrites involving Fp_cast/Zp_cast on pure nats,
  avoiding dependent type errors that occur when 'F_p or 'F_q variables
  are in scope.
*)

(* Modulus conversion: (Zp_trunc (pdiv p)).+2 = p *)
Let p_eq : (Zp_trunc (pdiv p)).+2 = p.
Proof. by rewrite Fp_cast // prime_gt1. Qed.

Let q_eq : (Zp_trunc (pdiv q)).+2 = q.
Proof. by rewrite Fp_cast // prime_gt1. Qed.

(* Pure nat helpers for modulus conversion *)
Let Zp_modn_p (n : nat) : (n %% (Zp_trunc (pdiv p)).+2 = n %% p)%N.
Proof. by rewrite p_eq. Qed.

Let Zp_modn_q (n : nat) : (n %% (Zp_trunc (pdiv q)).+2 = n %% q)%N.
Proof. by rewrite q_eq. Qed.

(* Pure nat helpers for bound conversion *)
Lemma Fp_bound_gen (n : nat) : (n < (Zp_trunc (pdiv p)).+2)%N -> (n < p)%N.
Proof. by rewrite p_eq. Qed.

Lemma Fq_bound_gen (n : nat) : (n < (Zp_trunc (pdiv q)).+2)%N -> (n < q)%N.
Proof. by rewrite q_eq. Qed.

(* Derived bounds for field elements *)
Lemma val_Fp_lt_p (x : 'F_p) : (val x < p)%N.
Proof. exact: Fp_bound_gen (ltn_ord x). Qed.

Lemma val_Fq_lt_q (x : 'F_q) : (val x < q)%N.
Proof. exact: Fq_bound_gen (ltn_ord x). Qed.

(* Helper for msg bound - avoids dependent type issues *)
Let Zm_bound_gen (n : nat) : (n < (Zp_trunc m).+2)%N -> (n < m)%N.
Proof. by rewrite Zp_cast. Qed.

Lemma val_msg_lt_m (x : msg) : (val x < m)%N.
Proof. exact: Zm_bound_gen (ltn_ord x). Qed.

(* ========================================================================== *)
(*  CRT Reconstruction: F_p × F_q → Z/(pq)Z                                   *)
(* ========================================================================== *)

(* Reconstruct element from field projections using chinese remainder *)
Definition crt_elem (xp : 'F_p) (xq : 'F_q) : msg :=
  inZp (chinese p q (val xp) (val xq)).

(* Reconstruct pair from field pairs *)
Definition crt_pair (pp : 'F_p * 'F_p) (qq : 'F_q * 'F_q) : msg * msg :=
  (crt_elem pp.1 qq.1, crt_elem pp.2 qq.2).

(* Pure nat helper for chinese projection *)
Lemma chinese_proj_p (vp vq : nat) :
  (vp < p)%N -> (chinese p q vp vq %% p = vp)%N.
Proof. by move=> Hvp; rewrite chinese_modl // modn_small. Qed.

Lemma chinese_proj_q (vp vq : nat) :
  (vq < q)%N -> (chinese p q vp vq %% q = vq)%N.
Proof. by move=> Hvq; rewrite chinese_modr // modn_small. Qed.

(* ========================================================================== *)
(*  Projection-Reconstruction Lemmas                                          *)
(* ========================================================================== *)

(* proj_Fp (crt_elem xp xq) = xp *)
Lemma proj_Fp_crt (xp : 'F_p) (xq : 'F_q) : proj_Fp (crt_elem xp xq) = xp.
Proof.
apply/val_inj.
rewrite /proj_Fp /crt_elem /=.
rewrite modn_dvdm; last by rewrite p_eq Zp_cast // dvdn_mulr.
rewrite Zp_modn_p.
rewrite chinese_proj_p //.
exact: val_Fp_lt_p.
Qed.

(* proj_Fq (crt_elem xp xq) = xq *)
Lemma proj_Fq_crt (xp : 'F_p) (xq : 'F_q) : proj_Fq (crt_elem xp xq) = xq.
Proof.
apply/val_inj.
rewrite /proj_Fq /crt_elem /=.
rewrite modn_dvdm; last by rewrite q_eq Zp_cast // dvdn_mull.
rewrite Zp_modn_q.
rewrite chinese_proj_q //.
exact: val_Fq_lt_q.
Qed.

(* Helper: inner Zp_trunc m = m *)
Let Zm_modn_m (n : nat) : (n %% (Zp_trunc m).+2 = n %% m)%N.
Proof. by rewrite Zp_cast. Qed.

(* crt_elem (proj_Fp x) (proj_Fq x) = x *)
Lemma crt_proj_id (x : msg) : crt_elem (proj_Fp x) (proj_Fq x) = x.
Proof.
apply/val_inj.
rewrite /crt_elem /proj_Fp /proj_Fq /=.
rewrite !Zp_modn_p !Zp_modn_q Zm_modn_m.
have Hx_lt := val_msg_lt_m x.
(* Goal: chinese p q (x %% p) (x %% q) %% m = x *)
(* Use chinese_mod: x = chinese p q (x %% p) (x %% q) %[mod m] *)
apply/eqP.
rewrite eq_sym -chinese_mod //.
by rewrite modn_small.
Qed.

(* Helper: from modular chinese equality over m, extract p-component equality *)
Lemma chinese_mod_inj_p (xp xp' : 'F_p) (xq xq' : 'F_q) :
  chinese p q (val xp) (val xq) = chinese p q (val xp') (val xq') %[mod m] ->
  xp = xp'.
Proof.
move=> /eqP Hmod.
apply/val_inj.
have Hl := chinese_modl coprime_pq (val xp) (val xq).
have Hr := chinese_modl coprime_pq (val xp') (val xq').
have Hp: (chinese p q (val xp) (val xq) %% p = chinese p q (val xp') (val xq') %% p)%N.
  have: (chinese p q (val xp) (val xq) %% m %% p = chinese p q (val xp') (val xq') %% m %% p)%N.
    by rewrite (eqP Hmod).
  by rewrite !modn_dvdm // dvdn_mulr.
move/eqP: Hl; move/eqP: Hr.
rewrite -{}Hp => /eqP Hr /eqP Hl.
have Heq: (val xp %% p = val xp' %% p)%N by rewrite -Hl -Hr.
have Hxp := val_Fp_lt_p xp.
have Hxp' := val_Fp_lt_p xp'.
by rewrite !modn_small in Heq.
Qed.

(* Helper: from modular chinese equality over m, extract q-component equality *)
Lemma chinese_mod_inj_q (xp xp' : 'F_p) (xq xq' : 'F_q) :
  chinese p q (val xp) (val xq) = chinese p q (val xp') (val xq') %[mod m] ->
  xq = xq'.
Proof.
move=> /eqP Hmod.
apply/val_inj.
have Hl := chinese_modr coprime_pq (val xp) (val xq).
have Hr := chinese_modr coprime_pq (val xp') (val xq').
have Hq: (chinese p q (val xp) (val xq) %% q = chinese p q (val xp') (val xq') %% q)%N.
  have: (chinese p q (val xp) (val xq) %% m %% q = chinese p q (val xp') (val xq') %% m %% q)%N.
    by rewrite (eqP Hmod).
  by rewrite !modn_dvdm // dvdn_mull.
move/eqP: Hl; move/eqP: Hr.
rewrite -{}Hq => /eqP Hr /eqP Hl.
have Heq: (val xq %% q = val xq' %% q)%N by rewrite -Hl -Hr.
have Hxq := val_Fq_lt_q xq.
have Hxq' := val_Fq_lt_q xq'.
by rewrite !modn_small in Heq.
Qed.

(* Helper: convert modular equality from (Zp_trunc m).+2 to m - no dependent types in signature *)
Let eqmod_Zp_m (a b : nat) :
  a = b %[mod (Zp_trunc m).+2] -> a = b %[mod m].
Proof. by rewrite Zp_cast. Qed.

(* crt_pair is injective *)
Lemma crt_pair_inj (pp pp' : 'F_p * 'F_p) (qq qq' : 'F_q * 'F_q) :
  crt_pair pp qq = crt_pair pp' qq' -> pp = pp' /\ qq = qq'.
Proof.
rewrite /crt_pair.
(* Pattern matching on pair equality gives modular equalities on chinese values *)
case => H1 H2.
(* H1: chinese p q pp.1 qq.1 = chinese p q pp'.1 qq'.1 %[mod (Zp_trunc m).+2] *)
(* H2: chinese p q pp.2 qq.2 = chinese p q pp'.2 qq'.2 %[mod (Zp_trunc m).+2] *)
(* Convert (Zp_trunc m).+2 to m using the helper *)
have H1' := eqmod_Zp_m H1.
have H2' := eqmod_Zp_m H2.
(* Extract component equalities *)
have Hp1 := chinese_mod_inj_p H1'.
have Hp2 := chinese_mod_inj_p H2'.
have Hq1 := chinese_mod_inj_q H1'.
have Hq2 := chinese_mod_inj_q H2'.
(* Reconstruct pair equalities *)
split.
- by rewrite (surjective_pairing pp) (surjective_pairing pp') Hp1 Hp2.
- by rewrite (surjective_pairing qq) (surjective_pairing qq') Hq1 Hq2.
Qed.

(* ========================================================================== *)
(*  Constraint Correspondence                                                 *)
(* ========================================================================== *)

(* Constraint in Z_m implies constraints in F_p and F_q *)
Lemma constraint_proj (u2 u3 target : msg) (vv : msg * msg) :
  u2 * vv.1 + u3 * vv.2 = target ->
  (proj_Fp u2 * proj_Fp vv.1 + proj_Fp u3 * proj_Fp vv.2 = proj_Fp target) /\
  (proj_Fq u2 * proj_Fq vv.1 + proj_Fq u3 * proj_Fq vv.2 = proj_Fq target).
Proof.
move=> Hconstr.
split.
- by rewrite -!proj_Fp_mul -proj_Fp_add Hconstr.
- by rewrite -!proj_Fq_mul -proj_Fq_add Hconstr.
Qed.

(* Constraints in F_p and F_q imply constraint in Z_m *)
Lemma constraint_crt (u2 u3 target : msg) (pp : 'F_p * 'F_p) (qq : 'F_q * 'F_q) :
  proj_Fp u2 * pp.1 + proj_Fp u3 * pp.2 = proj_Fp target ->
  proj_Fq u2 * qq.1 + proj_Fq u3 * qq.2 = proj_Fq target ->
  u2 * (crt_pair pp qq).1 + u3 * (crt_pair pp qq).2 = target.
Proof.
move=> Hp Hq.
(* Show projections are equal, then use CRT reconstruction *)
have HprojFp: proj_Fp (u2 * (crt_pair pp qq).1 + u3 * (crt_pair pp qq).2) = proj_Fp target.
  by rewrite proj_Fp_add !proj_Fp_mul /crt_pair /= !proj_Fp_crt.
have HprojFq: proj_Fq (u2 * (crt_pair pp qq).1 + u3 * (crt_pair pp qq).2) = proj_Fq target.
  by rewrite proj_Fq_add !proj_Fq_mul /crt_pair /= !proj_Fq_crt.
(* Both sides have same projections, so by CRT they're equal *)
rewrite -(crt_proj_id target).
rewrite -(crt_proj_id (u2 * (crt_pair pp qq).1 + u3 * (crt_pair pp qq).2)).
by rewrite HprojFp HprojFq.
Qed.

(* ========================================================================== *)
(*  Bijection between msg × msg and 'rV[msg]_2                                *)
(* ========================================================================== *)

(* Convert pair to row vector *)
Let pair_to_row (vv : msg * msg) : 'rV[msg]_2 :=
  \row_(j < 2) if j == ord0 then vv.1 else vv.2.

(* Convert row vector to pair *)
Let row_to_pair (v : 'rV[msg]_2) : msg * msg :=
  (v ord0 ord0, v ord0 ord_max).

(* pair_to_row ∘ row_to_pair = id *)
Let pair_to_rowK : cancel row_to_pair pair_to_row.
Proof.
move=> v; apply/rowP => j; rewrite mxE /row_to_pair.
case: (unliftP ord0 j) => [j'|] ->.
- have -> : lift ord0 j' = ord_max :> 'I_2 by apply/val_inj; case: j' => [] [].
  by [].
- by rewrite eqxx.
Qed.

(* row_to_pair ∘ pair_to_row = id *)
Let row_to_pairK : cancel pair_to_row row_to_pair.
Proof.
by move=> [v1 v2]; rewrite /row_to_pair /pair_to_row; congr pair; rewrite mxE.
Qed.

(* Injectivity for set cardinality *)
Let row_to_pair_inj : injective row_to_pair.
Proof. exact: (can_inj pair_to_rowK). Qed.

(* The dot product u *d v equals u2*v2 + u3*v3 *)
Let dotmul_pair_eq (u2 u3 : msg) (vv : msg * msg) :
  pair_to_row (u2, u3) *d pair_to_row vv = u2 * vv.1 + u3 * vv.2.
Proof.
rewrite dotmulE (bigD1 ord0) //= (bigD1 ord_max) //=.
rewrite big1 ?addr0; last first.
  move=> i /andP [Hi_neq0 Hi_neq_max].
  case: (unliftP ord0 i) Hi_neq0 Hi_neq_max => [j|] -> //.
  have -> : lift ord0 j = ord_max :> 'I_2 by apply/val_inj; case: j => [] [].
  by rewrite eqxx.
by rewrite /pair_to_row !mxE /= addrC.
Qed.

(* ========================================================================== *)
(*  Fiber correspondence via bijection                                        *)
(* ========================================================================== *)

(* Fiber over pairs: solutions to u2*v2 + u3*v3 = target *)
(* Exported Definition for use in dsdp_entropy.v *)
Definition linear_fiber_2d (u2 u3 target : msg) : {set msg * msg} :=
  [set vv : msg * msg | (u2 * vv.1 + u3 * vv.2 == target)%R].

(* linear_fiber_2d is the image of linear_fiber under row_to_pair *)
(* Local lemma - only used to derive linear_fiber_2d_card *)
Let linear_fiber_2d_eq (u2 u3 target : msg) :
  linear_fiber_2d u2 u3 target = 
    row_to_pair @: linear_fiber (pair_to_row (u2, u3)) target.
Proof.
apply/setP => vv.
rewrite inE.
apply/idP/imsetP.
- (* vv in linear_fiber_2d →
     exists v in linear_fiber with vv = row_to_pair v *)
  move=> /eqP Hconstr.
  exists (pair_to_row vv).
  + (* pair_to_row vv in linear_fiber *)
    rewrite inE.
    rewrite dotmul_pair_eq.
    by apply/eqP.
  + (* vv = row_to_pair (pair_to_row vv) *)
    by rewrite row_to_pairK.
- (* exists v in linear_fiber with vv = row_to_pair v →
     vv in linear_fiber_2d *)
  move=> [v Hv ->].
  move: Hv; rewrite inE => /eqP Hdot.
  apply/eqP.
  (* Goal: u2 * (row_to_pair v).1 + u3 * (row_to_pair v).2 = target *)
  rewrite -Hdot.
  rewrite -dotmul_pair_eq.
  by rewrite pair_to_rowK.
Qed.

(* ========================================================================== *)
(*  Main result: fiber cardinality (bijection approach)                       *)
(* ========================================================================== *)

(*
  Bijection approach: 2D fiber cardinality = m
  
  Derived from linear_fiber_card by:
  1. u3 < min(p,q) implies u3 is a unit (at index ord_max)
  2. linear_fiber_card gives |linear_fiber| = m^(2-1) = m
  3. Bijection preserves cardinality: |linear_fiber_2d| = |linear_fiber|
*)
Lemma linear_fiber_2d_card_bij (u2 u3 target : msg) :
  (0 < u3)%N -> (u3 < minn p q)%N ->
  #|linear_fiber_2d u2 u3 target| = m.
Proof.
move=> Hu3_pos Hu3_lt.
(* u3 is coprime to m, hence a unit *)
have Hu3_coprime: coprime (nat_of_ord u3) m.
  exact: (lt_minpq_coprime prime_p prime_q Hu3_pos Hu3_lt).
have Hu3_unit: u3 \is a GRing.unit.
  exact: (coprime_Zp_unit m_gt1 Hu3_coprime).
(* pair_to_row (u2, u3) has u3 at position ord_max *)
have Hcoef_ord_max: pair_to_row (u2, u3) ord0 ord_max = u3.
  by rewrite /pair_to_row mxE.
(* Apply linear_fiber_card with pivot index ord_max *)
have Hcoef_unit: pair_to_row (u2, u3) ord0 ord_max \is a GRing.unit.
  by rewrite Hcoef_ord_max.
have Hlinear_card: #|linear_fiber (pair_to_row (u2, u3)) target| = m.
  have := linear_fiber_card prime_p prime_q target Hcoef_unit.
  by rewrite /= expn1.
(* Use bijection to transfer cardinality *)
rewrite linear_fiber_2d_eq.
rewrite card_imset; last exact: row_to_pair_inj.
by rewrite Hlinear_card.
Qed.

(* ========================================================================== *)
(*  Main result: fiber cardinality (CRT approach via rouche_capelli.v)        *)
(* ========================================================================== *)

(*
  CRT approach: 2D fiber cardinality = m = p × q
  
  Uses Chinese Remainder Theorem to decompose:
    Z/(pq)Z ≅ Z/pZ × Z/qZ  (as rings)
  
  The constraint u2*v2 + u3*v3 = target over Z/pqZ decomposes into:
    - (u2 mod p)*(v2 mod p) + (u3 mod p)*(v3 mod p) = (target mod p)  over F_p
    - (u2 mod q)*(v2 mod q) + (u3 mod q)*(v3 mod q) = (target mod q)  over F_q
  
  By CRT bijection: |linear_fiber_2d| = |fiber_Fp| × |fiber_Fq|
  
  By rouche_capelli.v (count_affine_solutions_rank1):
    |fiber_Fp| = p  (when proj_Fp u3 ≠ 0)
    |fiber_Fq| = q  (when proj_Fq u3 ≠ 0)
  
  Since u3 < min(p,q), we have proj_Fp u3 ≠ 0 and proj_Fq u3 ≠ 0.
  Therefore: |linear_fiber_2d| = p × q = m
*)

(* Helper: u3 < p implies proj_Fp u3 ≠ 0 *)
Lemma proj_Fp_neq0 (u3 : msg) :
  (0 < u3)%N -> (val u3 < p)%N -> proj_Fp u3 != 0%R.
Proof.
move=> Hu3_pos Hu3_lt_p.
rewrite /proj_Fp.
apply/eqP => Heq.
have /val_eqP /= Hval := Heq.
move/eqP: Hval.
rewrite Fp_cast // modn_small // => Heq'.
by rewrite Heq' in Hu3_pos.
Qed.

(* Helper: u3 < q implies proj_Fq u3 ≠ 0 *)
Lemma proj_Fq_neq0 (u3 : msg) :
  (0 < u3)%N -> (val u3 < q)%N -> proj_Fq u3 != 0%R.
Proof.
move=> Hu3_pos Hu3_lt_q.
rewrite /proj_Fq.
apply/eqP => Heq.
have /val_eqP /= Hval := Heq.
move/eqP: Hval.
rewrite Fp_cast // modn_small // => Heq'.
by rewrite Heq' in Hu3_pos.
Qed.

(* CRT bijection: linear_fiber_2d bijects with fiber_Fp × fiber_Fq *)
Lemma linear_fiber_2d_crt_bij (u2 u3 target : msg) :
  (0 < u3)%N -> (u3 < minn p q)%N ->
  exists f : linear_fiber_2d u2 u3 target -> 
             fiber_Fp (proj_Fp u2) (proj_Fp u3) (proj_Fp target) *
             fiber_Fq (proj_Fq u2) (proj_Fq u3) (proj_Fq target),
    bijective f.
Proof.
move=> Hu3_pos Hu3_lt.
(* Define forward map: (v2, v3) ↦ ((proj_Fp v2, proj_Fp v3), (proj_Fq v2, proj_Fq v3)) *)
pose f := fun (vv : linear_fiber_2d u2 u3 target) =>
  let v := val vv in
  (@SetSub _ _ (proj_Fp v.1, proj_Fp v.2) (constraint_proj (valP vv)).1,
   @SetSub _ _ (proj_Fq v.1, proj_Fq v.2) (constraint_proj (valP vv)).2).
exists f.
split.
- (* Injective *)
  move=> [[v1 v2] Hv] [[v1' v2'] Hv'] /= [Hp Hq].
  apply/val_inj => /=.
  move: Hp Hq => /val_inj /= [Hp1 Hp2] /val_inj /= [Hq1 Hq2].
  (* v1 = v1' because proj_Fp v1 = proj_Fp v1' and proj_Fq v1 = proj_Fq v1' *)
  have Hv1: v1 = v1'.
    rewrite -(crt_proj_id v1) -(crt_proj_id v1').
    by rewrite Hp1 Hq1.
  have Hv2: v2 = v2'.
    rewrite -(crt_proj_id v2) -(crt_proj_id v2').
    by rewrite Hp2 Hq2.
  by rewrite Hv1 Hv2.
- (* Surjective *)
  move=> [[pp Hpp] [qq Hqq]].
  (* Reconstruct (v2, v3) from (pp, qq) via CRT *)
  pose vv := crt_pair pp qq.
  have Hvv: vv \in linear_fiber_2d u2 u3 target.
    rewrite inE /=.
    apply/eqP.
    apply: constraint_crt.
    + move: Hpp; rewrite inE => /eqP.
      by rewrite /vv /crt_pair /= !proj_Fp_crt.
    + move: Hqq; rewrite inE => /eqP.
      by rewrite /vv /crt_pair /= !proj_Fq_crt.
  exists (SetSub Hvv).
  apply/eqP.
  rewrite xpair_eqE.
  apply/andP; split; apply/eqP; apply/val_inj => /=.
  + by rewrite /vv /crt_pair /= !proj_Fp_crt.
  + by rewrite /vv /crt_pair /= !proj_Fq_crt.
Qed.

(* Main result: 2D fiber cardinality via CRT *)
Lemma linear_fiber_2d_card (u2 u3 target : msg) :
  (0 < u3)%N -> (u3 < minn p q)%N ->
  #|linear_fiber_2d u2 u3 target| = m.
Proof.
move=> Hu3_pos Hu3_lt.
(* u3 < p implies proj_Fp u3 ≠ 0 *)
have Hu3_lt_p: (val u3 < p)%N.
  by apply: leq_ltn_trans Hu3_lt (geq_minl _ _).
have Hu3_neq0_Fp := proj_Fp_neq0 Hu3_pos Hu3_lt_p.
(* u3 < q implies proj_Fq u3 ≠ 0 *)
have Hu3_lt_q: (val u3 < q)%N.
  by apply: leq_ltn_trans Hu3_lt (geq_minr _ _).
have Hu3_neq0_Fq := proj_Fq_neq0 Hu3_pos Hu3_lt_q.
(* Field fiber cardinalities via count_affine_solutions_rank1 from rouche_capelli.v *)
have Hcard_Fp := fiber_Fp_card Hu3_neq0_Fp.
have Hcard_Fq := fiber_Fq_card Hu3_neq0_Fq.
(* CRT bijection gives product of cardinalities *)
have [f Hf] := linear_fiber_2d_crt_bij Hu3_pos Hu3_lt.
rewrite (bij_eq_card Hf).
by rewrite card_prod Hcard_Fp Hcard_Fq.
Qed.

End fiber_2d.

(* ========================================================================== *)
(*            Connection between CRT (Z/pqZ) and Field (F_m) approaches       *)
(* ========================================================================== *)

(*
  The two approaches to entropy analysis:
  
  1. Field approach (for prime modulus m):
     - Working over finite field 'F_m
     - Any non-zero element is invertible
     - Fiber cardinality: m (degree of freedom argument)
     - Conditional entropy: H(V2,V3 | Cond) = log(m)
  
  2. CRT approach (for composite modulus m = p × q):
     - Working over ring 'Z_m (NOT a field!)
     - Only elements coprime to m are invertible
     - Security requires U3 < min(p,q) to ensure invertibility
     - Fiber cardinality: m = pq (via CRT product rule)
     - Conditional entropy: H(V2,V3 | Cond) = log(m) = log(pq)
  
  Key insight: Both approaches yield the SAME entropy formula:
  
      H(V2, V3 | constraint) = log(m)
  
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

(* See extra_algebra.v for Zp_Fp_card_eq and entropy_formula_same.
   
   Summary of security guarantees:
   
   Field approach (prime m):
     - Condition: U3 ≠ 0
     - Guarantee: H(V2,V3 | Cond) = log(m) bits of uncertainty
   
   CRT approach (m = pq):
     - Condition: 0 < U3 < min(p,q)  (stronger!)
     - Guarantee: H(V2,V3 | Cond) = log(pq) = log(m) bits of uncertainty
   
   Both provide maximum entropy over the solution space, meaning
   the observer learns nothing beyond the constraint itself.
*)

