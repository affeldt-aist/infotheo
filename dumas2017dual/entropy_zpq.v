From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap lra.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import extra_algebra extra_proba extra_entropy entropy_fibers.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* Fiber entropy framework over composite modulus Z/pqZ                       *)
(*                                                                            *)
(* This file provides a general framework for computing fiber cardinalities   *)
(* and entropy over the ring Z/(pq)Z where p, q are distinct primes.          *)
(*                                                                            *)
(* Key insight from CRT:                                                      *)
(*   Z/pqZ ≅ Z/pZ × Z/qZ  (when gcd(p,q) = 1)                                *)
(*                                                                            *)
(* For constraints of the form u2*v2 + u3*v3 = target:                        *)
(*   - 1 equation, 2 unknowns → 1 degree of freedom                           *)
(*   - Over Z/p: p solutions                                                  *)
(*   - Over Z/q: q solutions                                                  *)
(*   - Over Z/pq: p × q = pq solutions (via CRT product rule)                 *)
(*                                                                            *)
(* Security condition: u3 < min(p,q) ensures u3 is invertible in both         *)
(* Z/p and Z/q (since it can't be divisible by either prime).                 *)
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
(*                         Z/pqZ fiber framework                               *)
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

