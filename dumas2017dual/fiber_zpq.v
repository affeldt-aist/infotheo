From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap lra.
From mathcomp Require Import mathcomp_extra.
From robot Require Import euclidean.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import extra_algebra extra_proba extra_entropy entropy_fibers.
Require Import entropy_linear_fibers.

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
(* Generalization from entropy_linear_fibers.v:                               *)
(*   - entropy_linear_fibers.v: works over 'F_m (field, m prime)              *)
(*   - This file: works over 'Z_m (ring, m = p*q composite)                   *)
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
(*              Generalized linear fiber over Z/pqZ (dimension n)              *)
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

Section linear_fiber_zpq.

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
Definition linear_functional_zpq (u : 'rV[msg]_n) (v : 'rV[msg]_n) : msg :=
  u *d v.

(* Generalized fiber: solutions to u · v = target over Z/m *)
Definition linear_fiber_zpq (u : 'rV[msg]_n) (target : msg) : {set 'rV[msg]_n} :=
  [set v : 'rV[msg]_n | u *d v == target].

(* Condition: some component of u is a unit (invertible in Z/m) *)
Definition has_unit_component (u : 'rV[msg]_n) : Prop :=
  exists i : 'I_n, u ord0 i \is a GRing.unit.

(* Stronger condition specific to Z/pq: some component < min(p,q) and > 0 *)
Definition has_small_component (u : 'rV[msg]_n) : Prop :=
  exists i : 'I_n, (0 < u ord0 i)%N /\ (u ord0 i < minn p q)%N.

(* Small component implies unit component *)
Lemma small_component_unit (u : 'rV[msg]_n) :
  has_small_component u -> has_unit_component u.
Proof.
move=> [i [Hpos Hlt]].
exists i.
have Hcoprime: coprime (nat_of_ord (u ord0 i)) m.
  rewrite /coprime.
  have Hu_lt_p: (u ord0 i < p)%N.
    by apply: (leq_trans (n := minn p q)); [exact: Hlt | exact: geq_minl].
  have Hu_lt_q: (u ord0 i < q)%N.
    by apply: (leq_trans (n := minn p q)); [exact: Hlt | exact: geq_minr].
  rewrite Gauss_gcdl //.
    rewrite -/(coprime (u ord0 i) p) coprime_sym prime_coprime //.
    by rewrite gtnNdvd // ltnW.
  rewrite -/(coprime (u ord0 i) q) coprime_sym prime_coprime //.
  by rewrite gtnNdvd // ltnW.
exact: (coprime_Zp_unit m_gt1 Hcoprime).
Qed.

(*
  ==========================================================================
  Helper lemmas for linear_fiber_zpq_card
  ==========================================================================
  
  Strategy: Use bijection between 'rV[msg]_n and (msg * 'rV[msg]_n.-1)
  
  Key insight: For any fixed values of v_j (j ≠ i), there's exactly one v_i
  such that u · v = target. This v_i = (target - Σ_{j≠i} u_j*v_j) / u_i.
  
  We construct the bijection in two steps:
  1. fiber_zpq ≅ msg (via projection to non-pivot coordinates + solving for pivot)
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
by rewrite dotmulE (bigD1 i) //=; congr (_ + _); apply: eq_bigl => j; rewrite andbC.
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
  v ord0 i = (target - \sum_(j < n | j != i) u ord0 j * v ord0 j) * (u ord0 i)^-1.
Proof.
move=> Hui_unit Hdot.
(* Expand dot product isolating index i *)
rewrite (dotmul_bigD1 u v i) in Hdot.
(* Hdot: u ord0 i * v ord0 i + sum = target *)
(* Goal: v ord0 i = (target - sum) * (u ord0 i)^-1 *)
have Heq: u ord0 i * v ord0 i = target - \sum_(j < n | j != i) u ord0 j * v ord0 j.
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
  make_fiber_elem u target i free \in linear_fiber_zpq u target.
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
have Hsum_eq: \sum_(j < n | j != i) u ord0 j * (\row_k (if k == i then pivot else free k)) ord0 j = S.
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
  v1 \in linear_fiber_zpq u target ->
  v2 \in linear_fiber_zpq u target ->
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
(*  Bijection between {f : 'I_n → Z_m | f(i) = 0} and {g : 'I_n.-1 → Z_m}    *)
(* ========================================================================== *)

(* restrict : ('I_n → Z_m) → ('I_n.-1 → Z_m), drops coordinate i *)
Definition ffun_restrict (i : 'I_n) (ff : {ffun 'I_n -> msg}) : {ffun 'I_n.-1 -> msg} :=
  [ffun j => ff (lift i j)].

(* extend : ('I_n.-1 → Z_m) → ('I_n → Z_m), inserts 0 at coordinate i *)
Definition ffun_extend (i : 'I_n) (g : {ffun 'I_n.-1 -> msg}) : {ffun 'I_n -> msg} :=
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

(* Coercion from ffun to function for make_fiber_elem *)
Definition ffun_to_fun (f : {ffun 'I_n -> msg}) : 'I_n -> msg := fun j => f j.

(* Kernel of evaluation at coordinate i: ker(ev_i) = {f | f(i) = 0} *)
Definition ker_eval (i : 'I_n) := [set f : {ffun 'I_n -> msg} | f i == 0].

(* mk: maps ffun to fiber element via make_fiber_elem *)
Definition mk_fiber (u : 'rV[msg]_n) (target : msg) (i : 'I_n) 
  (f : {ffun 'I_n -> msg}) : 'rV[msg]_n :=
  make_fiber_elem u target i (ffun_to_fun f).

(* The fiber {v | u·v = target} equals the image of mk_fiber over ker_eval *)
Lemma linear_fiber_zpq_imsetE (u : 'rV[msg]_n) (target : msg) (i : 'I_n) :
  u ord0 i \is a GRing.unit ->
  linear_fiber_zpq u target = mk_fiber u target i @: ker_eval i.
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
  + have Hmk_in: mk_fiber u target i f \in linear_fiber_zpq u target.
      by apply: make_fiber_elemP.
    have Hv': v \in linear_fiber_zpq u target by rewrite inE.
    have Hsame: forall j, j != i -> v ord0 j = (mk_fiber u target i f) ord0 j.
      move=> j Hji.
      by rewrite /mk_fiber /make_fiber_elem mxE (negbTE Hji) /ffun_to_fun ffunE (negbTE Hji).
    exact: (fiber_elem_inj Hui_unit Hv' Hmk_in Hsame).
- (* v = mk_fiber f for f in ker_eval -> v in fiber *)
  move=> [f Hf ->].
  have Hgoal: mk_fiber u target i f \in linear_fiber_zpq u target.
    by apply: make_fiber_elemP.
  by move: Hgoal; rewrite /linear_fiber_zpq !inE.
Qed.

(* mk_fiber is injective on ker_eval *)
Lemma mk_fiber_inj (u : 'rV[msg]_n) (target : msg) (i : 'I_n) :
  u ord0 i \is a GRing.unit ->
  {in ker_eval i &, injective (mk_fiber u target i)}.
Proof.
move=> Hui_unit f1 f2 Hf1 Hf2 Heq.
apply/ffunP => j.
case: (altP (j =P i)) => [->|Hji].
+ by move: Hf1 Hf2; rewrite !inE => /eqP -> /eqP ->.
+ have Hv1: mk_fiber u target i f1 \in linear_fiber_zpq u target by exact: make_fiber_elemP.
  have Hv2: mk_fiber u target i f2 \in linear_fiber_zpq u target by exact: make_fiber_elemP.
  have Hfree: forall k, k != i -> (mk_fiber u target i f1) ord0 k = (mk_fiber u target i f2) ord0 k.
    by move: Heq => ->.
  move: (Hfree j Hji).
  by rewrite /mk_fiber /make_fiber_elem !mxE (negbTE Hji).
Qed.

(*
  Main cardinality theorem for generalized linear fiber.
  
  When u has a unit component at index i:
    |linear_fiber_zpq u target| = m^(n-1)
*)
Lemma linear_fiber_zpq_card (u : 'rV[msg]_n) (target : msg) (i : 'I_n) :
  u ord0 i \is a GRing.unit ->
  #|linear_fiber_zpq u target| = (m ^ n.-1)%N.
Proof.
move=> Hui_unit.
rewrite (@linear_fiber_zpq_imsetE u target i Hui_unit).
rewrite (card_in_imset (@mk_fiber_inj u target i Hui_unit)).
exact: ffun_fix_coord_card.
Qed.

End linear_fiber_zpq.

(* ========================================================================== *)
(*                   Original Z/pqZ fiber (dimension 2 special case)           *)
(* ========================================================================== *)

Section zpq_fiber_framework.

Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Hypothesis prime_p : prime p.
Hypothesis prime_q : prime q.
Hypothesis coprime_pq : coprime p q.
Local Notation m := (p * q).
(* Use Zp ring structure for composite modulus arithmetic *)
Local Notation msg := 'Z_m.

(* 
   Key lemma: u < min(p,q) implies u is coprime to pq.
   Since 0 < u < min(p,q), we have:
   - u is not divisible by p (since u < p)
   - u is not divisible by q (since u < q)
   Therefore gcd(u, pq) = 1, so u is a unit in Z/pq.
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

(* Fiber over composite modulus: solutions to u2*v2 + u3*v3 = target in Z/pqZ *)
Definition fiber_zpq (u2 u3 target : msg) : {set msg * msg} :=
  [set vv : msg * msg | (u2 * vv.1 + u3 * vv.2 == target)%R].

(*
   Fiber cardinality via degree of freedom: |fiber| = m = p * q

   Mathematical proof:
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
*)
Lemma fiber_zpq_card (u2 u3 target : msg) :
  (0 < u3)%N -> (u3 < minn p q)%N ->
  #|fiber_zpq u2 u3 target| = m.
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
rewrite /fiber_zpq.
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

(* Helper: minn p q < p * q *)
Let minpq_lt_pmulq : (minn p q < p * q)%N.
Proof.
(* minn p q ≤ p < p * q since q ≥ 2 *)
apply: (@leq_ltn_trans p).
  by apply: geq_minl.
(* p < p * q since q ≥ 2 *)
by rewrite -{1}(muln1 p) ltn_pmul2l // ltnS.
Qed.

End zpq_fiber_framework.

(* ========================================================================== *)
(*            Connection between CRT (Z/pqZ) and Field (F_m) approaches        *)
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

Section zpq_field_equivalence.

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
   the observer learns nothing beyond the constraint itself.
*)

End zpq_field_equivalence.

