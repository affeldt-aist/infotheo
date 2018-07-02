(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.
Require Import Reals Fourier FunctionalExtensionality.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop.
Require Import Nsatz.

(** * Formalization of discrete probabilities *)

(** OUTLINE
  1. Section distribution_definition.
     Distribution over sample space A
     (numerically-valued distribution function p : A -> R;
      for any a \in A, 0 <= p(a); \sum_{i \in A} p(i) = 1)
  2. Module Dist1.
  3. Module Uniform.
     Uniform distribution
  4. Module UniformSupport.
     Uniform distribution with a restricted support
  5. Module Binary.
     Binary distributions (distributions over sets with two elements)
  6. Section binary_distribution_prop.
  7. Module BinarySupport.
  8. Module D1Dist.
     construction of a distribution from another by removing one element from the support
  9. Module TupleDist.
  10. Module ProdDist.
  11. Module ConvexDist.
  12. Section tuple_prod_cast.
  13. Section wolfowitz_counting.
     Wolfowitz's counting principle
  14. Section probability.
      Probability of an event P with distribution p (Pr_p[P] = \sum_{i \in A, P\,i} \, p(i))
  15. Section Pr_tuple_prod.
  16. Section random_variable.
      Definition of a random variable (R-valued) with a distribution
      pr: Probability that a random variable evaluates to r \in R
  17. Section expected_value_definition.
      Expected value of a random variable
  18. Section expected_value_for_standard_random_variables.
      Properties of the expected value of standard random variables:
  19. Section probability_inclusion_exclusion.
      An algebraic proof of the formula of inclusion-exclusion (by Erik Martin-Dorel).
  20. Section markov_inequality.
  21. Section variance_definition.
  22. Section variance_properties.
  23. Section chebyshev.
      Chebyshev's Inequality
  24. Section joint_dist.
      Joint Distribution
  25. Section identically_distributed.
      Identically Distributed Random Variables
  26. Section independent_random_variables.
  27. Section sum_two_rand_var_def.
      The sum of two random variables
  28. Section sum_two_rand_var.
  29. Section sum_n_rand_var_def.
  30. Section sum_n_rand_var.
  31. Section sum_n_independent_rand_var_def.
  32. Section sum_n_independent_rand_var.
  33. Section weak_law_of_large_numbers.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "{ 'dist' T }" (at level 0, format "{ 'dist'  T }").
Reserved Notation "'`U' HC " (at level 10, HC at next level).
Reserved Notation "P `^ n" (at level 5).
Reserved Notation "P1 `x P2" (at level 6).
Reserved Notation "{ 'rvar' T }" (at level 0, format "{ 'rvar'  T }").
Reserved Notation "`p_ X" (at level 5).
Reserved Notation "'Pr[' X '=' r ']'"
  (at level 5, X at next level, r at next level).
Reserved Notation "k \cst* X" (at level 49).
Reserved Notation "X ''/' n" (at level 49, format "X  ''/'  n").
Reserved Notation "X \+_( H ) Y" (at level 50).
Reserved Notation "X \-_( H ) Y" (at level 50).
Reserved Notation "X '\+cst' m" (at level 50).
Reserved Notation "X '\-cst' m" (at level 50).
Reserved Notation "X '\^2' " (at level 49).
Reserved Notation "'`E'" (at level 5).
Reserved Notation "X '\=sum' Xs" (at level 50).
Reserved Notation "X '\=isum' Xs" (at level 50).
Reserved Notation "'Pr[' X '>=' r ']'" (at level 5,
  X at next level, r at next level, format "Pr[  X  >=  r  ]").
Reserved Notation "'`V'" (at level 5).
Reserved Notation "X _| P |_ Y" (at level 50).
Reserved Notation "Z \= X '@+' Y" (at level 50).

Local Open Scope reals_ext_scope.
Local Open Scope tuple_ext_scope.

Section distribution_definition.

Variable A : finType.

Record dist := mkDist {
  pmf :> A -> R+ ;
  pmf1 : \rsum_(a in A) pmf a = 1%R}.

Lemma dist_domain_not_empty (P : dist) : (0 < #| A |)%nat.
Proof.
apply/negPn/negP => abs; apply R1_neq_R0.
rewrite -(pmf1 P) (eq_bigl xpred0) ?big_pred0_eq // => a.
apply/negP => aA.
move/card_gt0P : abs; apply; by exists a.
Qed.

Definition dist_supp (d : dist) := [set a | d a != 0].

Lemma rsum_dist_supp (g : A -> R) (X : dist) (P : pred A):
  (\rsum_(a in A | P a) g a * X a = \rsum_(a | P a && (a \in dist_supp X)) g a * X a)%R.
Proof.
rewrite (bigID (mem (dist_supp X))) /= addRC (eq_bigr (fun=> 0)); last first.
  move=> i; rewrite inE negbK => /andP[_ /eqP] ->; by rewrite mulR0.
rewrite big_const iter_addR mulR0 add0R [in RHS]big_seq_cond.
apply eq_bigl => a; by rewrite !inE andbC /index_enum -enumT mem_enum inE.
Qed.

Definition makeDist (pmf : A -> R) (H0 : forall a, 0 <= pmf a)
  (H1 : \rsum_(a in A) pmf a = 1%R) := @mkDist (@mkPosFun _ pmf H0) H1.

Lemma dist_ge0 (P : dist) a : 0 <= P a.
Proof. exact: pos_f_ge0. Qed.

Lemma dist_max (P : dist) a : P a <= 1%R.
Proof.
rewrite -(pmf1 P) (_ : P a = \rsum_(a' in A | a' == a) P a').
  apply ler_rsum_l_support with (Q := xpredT) => // ?; exact/dist_ge0.
by rewrite big_pred1_eq.
Qed.

Lemma dist_eq d d' : pmf d = pmf d' -> d = d'.
Proof.
move: d d' => [d d1] [d' d'1] /= dd'.
move: d1 d'1; rewrite dd' => d1 d'1; congr mkDist; exact: eq_irrelevance.
Qed.

End distribution_definition.

Definition dist_of (A : finType) := fun phT : phant (Finite.sort A) => dist A.

Notation "{ 'dist' T }" := (dist_of (Phant T)) : proba_scope.

Module Dist1.
Section dist1.
Variables (A : finType) (a : A).

Definition f b := INR (b == a)%bool.

Lemma f0 b : 0 <= f b. Proof. exact: leR0n. Qed.

Lemma f1 : \rsum_(b in A) f b = 1%R.
Proof.
rewrite (bigD1 a) //= {1}/f eqxx /= (eq_bigr (fun=> 0)); last first.
  by move=> b ba; rewrite /f (negbTE ba).
by rewrite big1_eq // addR0.
Qed.

Definition d : dist A := makeDist f0 f1.

Lemma dxx : d a = 1%R.
Proof. by rewrite /d /= /f eqxx. Qed.

Lemma d_neq b : b != a -> d b = 0.
Proof. by move=> ba; rewrite /d /= /f (negbTE ba). Qed.

End dist1.
End Dist1.

Module DistBind.
Section distbind.
Variables (A B : finType) (p : dist A) (g : A -> dist B).

Definition f b := (\rsum_(a in A) p a * (g a) b)%R.

Lemma f0 b : 0 <= f b.
Proof. rewrite /f; apply rsumr_ge0 => a _; apply mulR_ge0; exact/dist_ge0. Qed.

Lemma f1 : \rsum_(b in B) f b = 1%R.
Proof.
rewrite /f exchange_big /= -[RHS](pmf1 p); apply eq_bigr => a _.
by rewrite -big_distrr /= pmf1 mulR1.
Qed.

Definition d : dist B := makeDist f0 f1.

End distbind.
End DistBind.

Lemma DistBind1f (A B : finType) (a : A) (f : A -> dist B) :
  DistBind.d (Dist1.d a) f = f a.
Proof.
apply/dist_eq/pos_fun_eq/functional_extensionality => b.
rewrite /DistBind.d /= /DistBind.f (bigD1 a) // Dist1.dxx mul1R [Dist1.d _]lock.
rewrite /= (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 ?addR0 // => c ca.
by rewrite -lock Dist1.d_neq // mul0R.
Qed.

Lemma DistBindp1 A (p : dist A) : DistBind.d p (@Dist1.d A) = p.
Proof.
apply/dist_eq/pos_fun_eq/functional_extensionality => /= a.
rewrite /DistBind.f (bigD1 a) // Dist1.dxx mulR1.
rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0.
by rewrite /= ?addR0.
by move=> b; rewrite inE andTb => ba; rewrite Dist1.d_neq ?mulR0 // eq_sym.
Qed.

Lemma DistBindA A B C (m : dist A) (f : A -> dist B) (g : B -> dist C) :
  DistBind.d (DistBind.d m f) g = DistBind.d m (fun x => DistBind.d (f x) g).
Proof.
apply/dist_eq/pos_fun_eq/functional_extensionality => c.
rewrite /DistBind.d /DistBind.f /=.
rewrite (eq_bigr (fun a => (\rsum_(a0 in A) m a0 * (f a0) a * (g a) c))); last first.
  move=> b _; by rewrite big_distrl.
rewrite exchange_big /=; apply eq_bigr => a _.
rewrite big_distrr /=; apply eq_bigr => b _; by rewrite mulRA.
Qed.

Module Uniform.
Section uniform.

Variables (A : finType) (n : nat).
Hypothesis domain_not_empty : #|A| = n.+1.

Definition f (a : A) := INR 1 / INR #|A|.

Lemma f0 a : 0 <= f a.
Proof. apply/divR_ge0 => //; apply/ltR0n; by rewrite domain_not_empty. Qed.

Lemma f1 : \rsum_(a in A) f a = 1%R.
Proof.
rewrite /f -big_distrr /= mul1R big_const iter_addR mulRV //.
by rewrite INR_eq0' domain_not_empty.
Qed.

Definition d : dist A := makeDist f0 f1.

End uniform.

Lemma d_neq0 (C : finType) (domain_non_empty : { m : nat | #| C | = m.+1 }) :
  forall x, d (projT2 domain_non_empty) x != 0.
Proof.
move=> x.
rewrite /d /= /f /=.
apply/negP; rewrite mulR_eq0 => /orP[|]; first by rewrite INR_eq0'.
apply/negP/invR_neq0; rewrite INR_eq0'; by case: domain_non_empty => x' ->.
Qed.

End Uniform.

Lemma dom_by_uniform A (P : dist A) n (HA : #|A| = n.+1) :
  P << (Uniform.d HA).
Proof.
move=> a; rewrite /Uniform.d /= /Uniform.f /= HA div1R => /esym abs.
exfalso.
move: abs; exact/ltR_eqF/invR_gt0/ltR0n.
Qed.

Module UniformSupport.
Section uniformsupport.

Variables (A : finType) (C : {set A}).
Hypothesis support_not_empty : (0 < #|C|)%nat.

Definition f a := if a \in C then 1 / INR #|C| else 0%R.

Lemma f0 a : 0 <= f a.
Proof.
rewrite /f.
case e : (a \in C); last exact/leRR.
apply divR_ge0; [by fourier|exact/ltR0n].
Qed.

Lemma f1 : \rsum_(a in A) f a = 1%R.
Proof.
rewrite /f.
have HC' : INR #|C| != 0%R by rewrite INR_eq0' -lt0n.
transitivity (\rsum_(a in A) (if a \in C then 1 else 0) / INR #|C|)%R.
apply eq_bigr => a _.
  case aC : (a \in C); by [ | move/eqP in HC'; field].
have HC'' : \rsum_(a in A) (if a \in C then 1 else 0)%R = INR #|C|.
  by rewrite -big_mkcondr /= big_const iter_addR mulR1.
by rewrite /Rdiv -big_distrl HC'' /= mulRV.
Qed.

Definition d : dist A := locked (makeDist f0 f1).

End uniformsupport.

Local Notation "'`U' HC " := (d HC).

Section UniformSupport_prop.

Variables (A : finType) (C : {set A}) (HC : (0 < #| C |)%nat).

Lemma E z : z \in C -> (`U HC) z = 1 / INR #|C|.
Proof. by rewrite /d; unlock; rewrite /= /f => ->. Qed.

Lemma E0 z : z \notin C -> (`U HC) z = 0.
Proof. by rewrite /d; unlock; move/negbTE; rewrite /= /f => ->. Qed.

Lemma restrict g : \rsum_(t in A) ((`U HC) t * g t)%R = \rsum_(t in C) ((`U HC) t * g t)%R.
Proof.
rewrite (bigID (fun x => x \in C)) /= addRC (eq_bigr (fun=> 0)).
by rewrite big_const // iter_addR mulR0 add0R.
move=> a aC; by rewrite E0 // mul0R.
Qed.

Lemma big_distrr g : \rsum_(t in C) ((`U HC) t * g t)%R = (/ INR #|C| * \rsum_(t in C) g t)%R.
Proof.
rewrite /= big_distrr /=; apply eq_bigr => /= i Hi; by rewrite E // div1R.
Qed.

Lemma neq0 z : ((`U HC) z != 0) = (z \in C).
Proof.
case/boolP : (z \in C) => [/E ->|/E0 ->//]; last by rewrite eqxx.
rewrite div1R; by apply/invR_neq0; rewrite INR_eq0' -lt0n.
Qed.

End UniformSupport_prop.

End UniformSupport.

Notation "'`U' HC " := (UniformSupport.d HC) : proba_scope.

Local Open Scope proba_scope.

Module Binary.
Section binary.

Variable A : finType.
Hypothesis HA : #|A| = 2%nat.
Variable p : R.
Hypothesis Hp : (0 <= p <= 1)%R.

Definition f (a : A) := fun a' => if a' == a then (1 - p)%R else p.

Lemma fxx a : f a a = (1 - p)%R.
Proof. by rewrite /f eqxx. Qed.

Lemma f0 (a a' : A) : 0 <= f a a'.
Proof. rewrite /f. case: ifP => _; case: Hp => ? ?; fourier. Qed.

Lemma f1 (a : A) : \rsum_(a' in A) f a a' = 1%R.
Proof.
rewrite Set2sumE /= /f.
case: ifPn => [/eqP <-|].
  by rewrite eq_sym (negbTE (Set2.a_neq_b HA)) subRK.
by rewrite eq_sym; move/Set2.neq_a_b/eqP => <-; rewrite eqxx subRKC.
Qed.

Lemma f_sum_swap a : \rsum_(a' in A) f a a' = \rsum_(a' in A) f a' a.
Proof. by rewrite 2!Set2sumE /f !(eq_sym a). Qed.

Definition d : dist A := makeDist (f0 (Set2.a HA)) (f1 (Set2.a HA)).

End binary.
End Binary.

Section binary_distribution_prop.

Variables (A : finType) (P Q : dist A).
Hypothesis card_A : #|A| = 2%nat.

Lemma charac_bdist : {r | {r01 : (0 <= r <= 1)%R & P = Binary.d card_A r01 }}.
Proof.
destruct P as [[pmf pmf0] pmf1].
exists (1 - pmf (Set2.a card_A))%R.
have r01 : 0 <= 1 - pmf (Set2.a card_A) <= 1%R.
  move: (dist_max (mkDist pmf1) (Set2.a card_A)) => /= H1.
  move: (pmf0 (Set2.a card_A)) => H0.
  split; first by fourier.
  suff : forall a, a <= 1 -> 0 <= a -> 1 - a <= 1 by apply.
  move=> *; fourier.
exists r01.
apply/dist_eq/pos_fun_eq => /=; apply functional_extensionality => a.
rewrite /Binary.f; case: ifPn => [/eqP ->|Ha]; first by field.
by rewrite -pmf1 /= Set2sumE /= addRC addRK; move/Set2.neq_a_b/eqP : Ha => ->.
Qed.

End binary_distribution_prop.

Module BinarySupport.
Section binary_support.

Variables (A : finType) (d : dist A).
Hypothesis Hd : #|dist_supp d| = 2%nat.

Definition a := enum_val (cast_ord (esym Hd) ord0).
Definition b := enum_val (cast_ord (esym Hd) (lift ord0 ord0)).

Lemma enumE : enum (dist_supp d) = a :: b :: [::].
Proof.
apply (@eq_from_nth _ a); first by rewrite -cardE Hd.
case=> [_ |]; first by rewrite [X in _ = X]/= {2}/a (enum_val_nth a).
case=> [_ |i]; last by rewrite -cardE Hd.
by rewrite [X in _ = X]/= {1}/b (enum_val_nth a).
Qed.

Lemma rsumE (f : A -> R) : \rsum_(i in dist_supp d) f i = f a + f b.
Proof.
transitivity (\rsum_(i <- enum (dist_supp d)) f i); last first.
  by rewrite enumE 2!big_cons big_nil addR0.
rewrite big_filter; apply eq_bigl => ?; by rewrite !inE.
Qed.

End binary_support.
End BinarySupport.

Module D1Dist.
Section d1dist.

Variables (B : finType) (X : dist B) (b : B).

Definition f : B -> R := fun a => if a == b then 0 else X a / (1 - X b).

Hypothesis Xb1 : X b != 1%R.

Lemma f0 : forall a, 0 <= f a.
Proof.
move=> a; rewrite /f.
case: ifPn => [_ |ab]; first exact/leRR.
apply mulR_ge0; first exact/dist_ge0.
apply/ltRW/invR_gt0/subR_gt0/ltRP; rewrite ltR_neqAle Xb1; exact/leRP/dist_max.
Qed.

Lemma f1 : \rsum_(a in B) f a = 1%R.
Proof.
rewrite (bigD1 b) //= {1}/f eqxx add0R.
rewrite (eq_bigr (fun c => X c / (1 - X b))); last first.
  by move=> ? cb; rewrite /f (negbTE cb).
rewrite -big_distrl /=.
move: (pmf1 X); rewrite (bigD1 b) //=.
move=> /eqP; rewrite eq_sym addRC -subR_eq => /eqP H.
have ? : 1 - X b != 0 by apply: contra Xb1; rewrite subR_eq0 eq_sym.
rewrite -(@eqR_mul2r (1 - X b)); last exact/eqP.
by rewrite mul1R -mulRA mulVR ?mulR1 // H.
Qed.

Definition d := makeDist f0 f1.

Lemma card_dist_supp (Xb0 : X b != 0) : #|dist_supp d| = #|dist_supp X|.-1.
Proof.
rewrite /dist_supp (cardsD1 b [set a | X a != 0]) !inE Xb0 add1n /=.
apply eq_card => i; rewrite !inE /f.
case: ifPn => //= ib; first by rewrite eqxx.
apply/idP/idP; first by apply: contra => /eqP ->; rewrite div0R.
apply: contra; rewrite /Rdiv mulR_eq0 => /orP[//|H].
exfalso.
move/negPn/negP : H; apply.
apply/invR_neq0; by apply: contra Xb1; rewrite subR_eq0 eq_sym.
Qed.

Lemma f_eq0 a (Xa0 : X a != 0) : ((f a == 0) = (b == a))%bool.
Proof.
rewrite /f; case: ifPn => [/eqP ->|ab]; first by rewrite !eqxx.
apply/idP/idP => [|]; last by rewrite eq_sym (negbTE ab).
rewrite mulR_eq0 => /orP[]; first by rewrite (negbTE Xa0).
by move/invR_eq0; rewrite subR_eq0 eq_sym (negbTE Xb1).
Qed.

Lemma f_0 a : X a = 0 -> f a = 0.
Proof. move=> Xa0; rewrite /f Xa0 div0R; by case: ifP. Qed.

End d1dist.
End D1Dist.

Lemma dist2tuple1 : forall A, dist A -> {dist 1.-tuple A}.
Proof.
move=> A d.
apply makeDist with (fun x => d (thead x)).
  move=> a; exact: dist_ge0.
rewrite -[RHS](pmf1 d); exact: big_1_tuple.
Defined.

Local Open Scope vec_ext_scope.

Lemma dist2rV1 : forall A, dist A -> {dist 'rV[A]_1}.
Proof.
move=> A d.
apply makeDist with (fun x : 'rV[A]_1 => d (x ``_ ord0)).
move=> a; exact: dist_ge0.
rewrite -[RHS](pmf1 d).
exact: big_rV_1.
Defined.

Local Close Scope vec_ext_scope.

Module TupleDist.

Section TupleDist_sect.

Variables (A : finType) (P : dist A) (n : nat).

Local Open Scope vec_ext_scope.

Definition f (t : 'rV[A]_n) := \rprod_(i < n) P t ``_ i.

Lemma f0 (t : 'rV[A]_n) : 0 <= f t.
Proof. apply rprodr_ge0 => ?; exact/dist_ge0. Qed.

(** Definition of the product distribution (over a row vector): *)

Lemma f1 : \rsum_(t in 'rV[A]_n) f t = 1%R.
Proof.
pose P' := fun (a : 'I_n) b => P b.
suff : \rsum_(g : {ffun 'I_n -> A }) \rprod_(i < n) P' i (g i) = 1%R.
Local Open Scope ring_scope.
  rewrite (reindex_onto (fun j : 'rV[A]_n => finfun (fun x => j ``_ x))
                        (fun i => \row_(j < n) i j)) /=.
Local Close Scope ring_scope.
  - move=> H; rewrite /f -H {H}.
    apply eq_big => t /=.
    + by apply/esym/eqP/rowP => i; rewrite mxE ffunE.
    + move=> _; apply eq_bigr => i _ /=; by rewrite ffunE.
  move=> g _; apply/ffunP => i; by rewrite ffunE mxE.
rewrite -bigA_distr_bigA /= /P'.
rewrite [RHS](_ : _ = \rprod_(i < n) 1)%R; last first.
  by rewrite big_const_ord iter_mulR pow1.
apply eq_bigr => i _; exact: pmf1.
Qed.

Definition d : {dist 'rV[A]_n} := locked (makeDist f0 f1).

Lemma dE t : d t = \rprod_(i < n) P t ``_ i.
Proof. rewrite /d; by unlock. Qed.

End TupleDist_sect.

End TupleDist.

Notation "P `^ n" := (TupleDist.d P n) : proba_scope.

Local Open Scope proba_scope.

Local Open Scope vec_ext_scope.

Lemma TupleDist0E (B : finType) (x : 'rV[B]_0) P : P `^ 0 x = 1%R.
Proof. by rewrite TupleDist.dE big_ord0. Qed.

Lemma TupleDist1E (A : finType) (a : 'rV[A]_1) P : (P `^ 1) a = P (a ``_ ord0).
Proof.
rewrite TupleDist.dE big_ord_recr /= big_ord0 mul1R; congr (P _ ``_ _).
by apply val_inj.
Qed.

Lemma TupleDistSE (B : finType) n (x : 'rV[B]_n.+1) P : P `^ n.+1 x = (P (x ``_ ord0) * P `^ n (rbehead x))%R.
Proof.
rewrite 2!TupleDist.dE big_ord_recl; congr (_ * _)%R.
apply eq_bigr => i _; by rewrite /rbehead mxE.
Qed.

Local Open Scope ring_scope.

Lemma rsum_rmul_rV_pmf_tnth A n k (P : dist A) :
  \rsum_(t : 'rV[ 'rV[A]_n]_k) \rprod_(m < k) (P `^ n) t ``_ m = 1%R.
Proof.
transitivity (\rsum_(j : {ffun 'I_k -> 'rV[A]_n}) \rprod_(m : 'I_k) P `^ _ (j m)).
  rewrite (reindex_onto (fun p : 'rV_k => [ffun i => p ``_ i])
    (fun x : {ffun 'I_k -> 'rV_n} => \row_(i < k) x i)) //=; last first.
    move=> f _; apply/ffunP => /= k0; by rewrite ffunE mxE.
  apply eq_big => //.
  - move=> v /=; by apply/esym/eqP/rowP => i; rewrite mxE ffunE.
  - move=> i _; apply eq_bigr => j _; by rewrite ffunE.
rewrite -(bigA_distr_bigA (fun m => P `^ _)) /= big_const.
by rewrite iter_mulR pmf1 pow1.
Qed.

Module ProdDist.

Section ProdDist_sect.

Variables (A B : finType) (P1 : dist A) (P2 : dist B).

Definition f (ab : A * B) := (P1 ab.1 * P2 ab.2)%R.

Lemma f0 (ab : A * B) : 0 <= f ab.
Proof. apply/mulR_ge0; exact/dist_ge0. Qed.

Lemma f1 : \rsum_(ab in {: A * B}) f ab = 1%R.
Proof.
rewrite -(pair_big xpredT xpredT (fun a b => P1 a * P2 b)%R) /= -(pmf1 P1).
apply eq_bigr => a _; by rewrite -big_distrr /= pmf1 mulR1.
Qed.

Definition d : {dist A * B} := makeDist f0 f1.

Definition proj1 (P : {dist A * B}) : dist A.
apply makeDist with (fun a => \rsum_(b in B) P (a, b)).
- move=> a; apply rsumr_ge0 => ? _; exact: dist_ge0.
- rewrite -[RHS](pmf1 P) pair_big /=; apply eq_bigr; by case.
Defined.

Definition proj2 (P : {dist A * B}) : dist B.
apply makeDist with (fun b => \rsum_(a in A) P (a, b)).
- move=> a; apply: rsumr_ge0 => ? _; exact: dist_ge0.
- rewrite exchange_big /= -[RHS](pmf1 P) pair_big /=; apply eq_big; by case.
Defined.

End ProdDist_sect.

End ProdDist.

Notation "P1 `x P2" := (ProdDist.d P1 P2) : proba_scope.

Module ConvexDist.
Section convexdist.
Variables (A : finType) (d1 d2 : dist A) (p : R).
Hypothesis p01 : (0 <= p <= 1)%R.

Definition f a := (p * d1 a + p.~ * d2 a)%R.

Lemma f0 a : 0 <= f a.
Proof.
apply addR_ge0; apply mulR_ge0;
 [by case: p01|exact: dist_ge0|exact: (onem_ge0 (proj2 p01))|exact: dist_ge0].
Qed.

Lemma f1 : \rsum_(a in A) f a = 1%R.
Proof. by rewrite big_split /= -2!big_distrr /= 2!pmf1 2!mulR1 onemKC. Qed.

Definition d : {dist A} := makeDist f0 f1.
End convexdist.
Section convexdist_prop.
Variables (A : finType).

Lemma d0 (d1 d2 : dist A) (H : 0 <= 0 <= 1) : ConvexDist.d d1 d2 H = d2.
Proof.
apply/dist_eq/pos_fun_eq/functional_extensionality => a /=.
by rewrite /f mulRDl !(mul0R,mulNR,oppR0,add0R,addR0,mulR1,mul1R).
Qed.

Lemma d1 (d1 d2 : dist A) (H : 0 <= 1 <= 1) : ConvexDist.d d1 d2 H = d1.
Proof.
apply/dist_eq/pos_fun_eq/functional_extensionality => a /=.
by rewrite /f mulRDl !(mul0R,mulNR,oppR0,add0R,addR0,mulR1,mul1R,addRN).
Qed.

Lemma commute (d1 d2 : dist A) p (Hp : 0 <= p <= 1) (Hp' : 0 <= p.~ <= 1) :
  d d1 d2 Hp = d d2 d1 Hp'.
Proof.
apply/dist_eq/pos_fun_eq/functional_extensionality => a /=.
by rewrite /f onemK addRC.
Qed.

Lemma idempotent (d0 : dist A) p (Hp : 0 <= p <= 1) : d d0 d0 Hp = d0.
Proof.
apply/dist_eq/pos_fun_eq/functional_extensionality => a /=.
by rewrite /f mulRBl mul1R addRCA addRN addR0.
Qed.

Lemma quasi_assoc (p q r s : R) (d0 d1 d2 : dist A)
  (Hp : 0 <= p <= 1) (Hq : 0 <= q <= 1) (Hr : 0 <= r <= 1) (Hs : 0 <= s <= 1) :
  p = (r * s)%R -> (s.~ = p.~ * q.~)%R ->
  d d0 (d d1 d2 Hq) Hp = d (d d0 d1 Hr) d2 Hs.
Proof.
move=> H1 H2.
apply/dist_eq/pos_fun_eq/functional_extensionality => a /=.
rewrite /d /f /=.
transitivity (p * d0 a + p.~ * q * d1 a + p.~ * q.~ * d2 a)%R; first nsatz.
transitivity (r * s * d0 a + r.~ * s * d1 a + s.~ * d2 a)%R; last nsatz.
rewrite H1; congr (_ + _ * _ + _ * _)%R.
rewrite -(onemK s) H2; nsatz.
rewrite H2 H1; nsatz.
Qed.

Lemma bind_left_distr (B : finType) (p : R) (Hp : 0 <= p <= 1)
  (d0 d1 : dist A) (f : A -> dist B) :
  DistBind.d (d d0 d1 Hp) f = d (DistBind.d d0 f) (DistBind.d d1 f) Hp.
Proof.
apply/dist_eq/pos_fun_eq/functional_extensionality => a /=.
rewrite /DistBind.d /DistBind.f /ConvexDist.d /ConvexDist.f /=.
rewrite 2!big_distrr /= -big_split /=; apply/eq_bigr => a0 _.
by rewrite mulRDl !mulRA.
Qed.

End convexdist_prop.
End ConvexDist.

Section tuple_prod_cast.

Variables A B : finType.
Variable n : nat.
Variable P : {dist 'rV[A * B]_n}.

(*
Definition dist_tuple_prod_cast : dist [finType of n.-tuple A * n.-tuple B].
apply makeDist with (fun xy => P (prod_tuple xy)).
move=> a; by apply Rle0f.
rewrite -(pmf1 P).
rewrite (reindex_onto (fun x => tuple_prod x) (fun y => prod_tuple y)); last first.
  move=> i _; by rewrite prod_tupleK.
rewrite /=.
apply eq_big => /= i.
- by rewrite inE tuple_prodK eqxx.
- move=> _; by rewrite tuple_prodK.
Defined.
*)

End tuple_prod_cast.

Section wolfowitz_counting.

Variables (C : finType) (P : dist C) (k : nat) (s : {set 'rV[C]_k}).

Lemma wolfowitz a b A B : 0 < A -> 0 < B ->
  a <= \rsum_(x in s) P `^ k x <= b ->
  (forall x : 'rV_k, x \in s -> A <= P `^ k x <= B) ->
  a / B <= INR #| s | <= b / A.
Proof.
move=> A0 B0 [Ha Hb] H.
have HB : \rsum_(x in s) P `^ _ x <= INR #|s| * B.
  have HB : \rsum_(x in s | predT s ) P `^ _ x <= INR #|s| * B.
    apply (@leR_trans (\rsum_(x in s | predT s) [fun _ => B] x)).
      apply ler_rsum_support => /= i iA _; by apply H.
    rewrite -big_filter /= big_const_seq /= iter_addR /=.
    apply leR_wpmul2r; first by fourier.
    apply Req_le.
    rewrite filter_index_enum count_predT cardE; congr (INR (size _)).
    apply eq_enum => i; by rewrite /in_mem /= andbC.
  apply/(leR_trans _ HB)/Req_le/eq_bigl => i; by rewrite andbC.
have HA : INR #|s| * A <= \rsum_(x in s) P `^ _ x.
  have HA : INR #|s| * A <= \rsum_(x in s | predT s) P `^ _ x.
    apply (@leR_trans (\rsum_(x in s | predT s) [fun _ => A] x)); last first.
      apply ler_rsum_support => i Hi _; by case: (H i Hi).
    rewrite -big_filter /= big_const_seq /= iter_addR /=.
    apply leR_wpmul2r; first by fourier.
    apply Req_le.
    rewrite filter_index_enum count_predT cardE; congr (INR (size _)).
    apply eq_enum => i; by rewrite /in_mem /= andbC.
  apply/(leR_trans HA)/Req_le/eq_bigl => i; by rewrite andbC.
split; apply/leRP.
- rewrite leR_pdivr_mulr //; apply/leRP; move/leR_trans : Ha; exact.
- rewrite leR_pdivl_mulr //; apply/leRP; exact: (leR_trans HA).
Qed.

End wolfowitz_counting.

Section probability.

Variables (A : finType) (P : dist A).

Definition Pr (E : {set A}) := \rsum_(a in E) P a.

Lemma le_0_Pr E : 0 <= Pr E.
Proof. apply rsumr_ge0 => *; exact: dist_ge0. Qed.

Lemma Pr_1 E : Pr E <= 1.
Proof.
rewrite -(pmf1 P); apply ler_rsum_l => // a _; [exact/leRR | exact/dist_ge0].
Qed.

Lemma Pr_ext E F : E :=: F -> Pr E = Pr F.
Proof. move=> H; apply eq_bigl => x; by rewrite H. Qed.

Local Open Scope R_scope.

Lemma Pr_0 : Pr set0 = 0.
Proof. rewrite /Pr big_pred0 // => a; by rewrite in_set0. Qed.

Lemma Pr_cplt E : Pr E + Pr (~: E) = 1.
Proof.
rewrite /Pr -bigU /=; last by rewrite -subsets_disjoint.
rewrite -(pmf1 P); apply eq_bigl => /= a.
by rewrite !inE /= orbN.
Qed.

Lemma Pr_to_cplt E : Pr E = 1 - Pr (~: E).
Proof. rewrite -(Pr_cplt E); field. Qed.

Lemma Pr_of_cplt E : Pr (~: E) = 1 - Pr E.
Proof. rewrite -(Pr_cplt E); field. Qed.

Lemma Pr_union E1 E2 : Pr (E1 :|: E2) <= Pr E1 + Pr E2.
Proof.
rewrite /Pr.
rewrite (_ : \rsum_(i in A | [pred x in E1 :|: E2] i) P i =
  \rsum_(i in A | [predU E1 & E2] i) P i); last first.
  apply eq_bigl => x /=; by rewrite inE.
rewrite (_ : \rsum_(i in A | [pred x in E1] i) P i =
  \rsum_(i in A | pred_of_set E1 i) P i); last first.
  apply eq_bigl => x /=; by rewrite unfold_in.
rewrite (_ : \rsum_(i in A | [pred x in E2] i) P i =
  \rsum_(i in A | pred_of_set E2 i) P i); last first.
  apply eq_bigl => x /=; by rewrite unfold_in.
exact/ler_rsum_predU/dist_ge0.
Qed.

Lemma Pr_union_disj E1 E2 :
  E1 :&: E2 = set0 (*NB: use disjoint?*) -> Pr (E1 :|: E2) = (Pr E1 + Pr E2)%R.
Proof.
move=> E1E2.
rewrite -bigU /=; last by rewrite -setI_eq0; apply/eqP.
apply eq_bigl => a /=; by rewrite !inE.
Qed.

Lemma Pr_incl (E E' : {set A}) : (E \subset E') -> Pr E <= Pr E'.
Proof.
move=> H; apply ler_rsum_l => a Ha;
  [exact/leRR | exact/dist_ge0 | move/subsetP : H; exact].
Qed.

Lemma Pr_bigcup (B : finType) (E : pred B) F :
  Pr (\bigcup_(i | E i) F i) <= \rsum_(i | E i) Pr (F i).
Proof.
rewrite /Pr.
elim: (index_enum _) => [| hd tl IH].
  rewrite big_nil; apply: rsumr_ge0 => i _; rewrite big_nil; exact/leRR.
rewrite big_cons.
case: ifP => H1.
  move: IH.
  set lhs := \rsum_(_ <- _ | _) _.
  move=> IH.
  apply: leR_trans.
    eapply leR_add2l; by apply IH.
  rewrite [X in _ <= X](exchange_big_dep (fun hd => (hd \in A) && [pred x in \bigcup_(i | E i) F i] hd)) /=; last first.
    move=> b j Pi Fj; apply/bigcupP; by exists b.
  rewrite big_cons /=.
  rewrite H1 big_const iter_addR -exchange_big_dep //; last first.
    move=> b j Pi Fj; apply/bigcupP; by exists b.
  apply/leR_add2r.
  set inr := INR _.
  suff H : 1 <= inr.
    rewrite -{1}(mul1R (P hd)).
    apply leR_wpmul2r => //; exact: dist_ge0.
  rewrite /inr {inr} (_ : 1 = INR 1) //.
  apply le_INR.
  apply/leP => /=.
  apply/card_gt0P.
  case/bigcupP : H1 => b E_b H1'.
  exists b.
  by rewrite -topredE /= E_b.
apply/(leR_trans IH)/ler_rsum => b Eb.
rewrite big_cons.
case: ifPn => hFb; last exact/leRR.
rewrite -[X in X <= _]add0R; exact/leR_add2r/dist_ge0.
Qed.

End probability.

Section Pr_tuple_prod.

Variables A B : finType.
Variable n : nat.
Variable P : dist [finType of n.-tuple (A * B)%type].
Variable Q : {set [finType of n.-tuple (A * B)%type]}.

(*
Lemma Pr_tuple_prod_cast : Pr (@dist_tuple_prod_cast A B n P) [set x | prod_tuple x \in Q] =
  Pr P Q.
Proof.
rewrite /Pr.
rewrite (reindex_onto (fun x => tuple_prod x) (fun y => prod_tuple y)) /=; last first.
  move=> i _; by rewrite prod_tupleK.
apply eq_big.
move=> tab /=.
  by rewrite !inE tuple_prodK eqxx andbC.
move=> i /= Hi; by rewrite tuple_prodK.
Qed.
*)

End Pr_tuple_prod.

Local Open Scope R_scope.

Section random_variable.

Record rvar A := mkRvar {rv_dist : dist A ; rv_fun :> A -> R }.

Definition rvar_of (A : finType) := fun phT : phant (Finite.sort A) => rvar A.

Local Notation "`p_ X" := (rv_dist X).

Section pr_def.

Variable A : finType.

Definition pr (X : rvar A) r := Pr `p_X [set x | X x == r].

End pr_def.

Definition scale_rv A k (X : rvar A) :=
  mkRvar `p_X (fun x => k * X x).
Definition add_rv A (X Y : rvar A) (H : `p_X = `p_Y) :=
  mkRvar `p_X (fun x => X x + Y x).
Definition sub_rv A (X Y : rvar A) (H : `p_X = `p_Y) :=
  mkRvar `p_X (fun x => X x - Y x).
Definition trans_add_rv A (X : rvar A) m :=
  mkRvar `p_X (fun x => X x + m).
Definition trans_min_rv A (X : rvar A) m :=
  mkRvar `p_X (fun x => X x - m).
Definition const_rv A cst (X : rvar A) :=
  mkRvar `p_X (fun _ => cst).
Definition comp_rv A (X : rvar A) f :=
  mkRvar `p_X (fun x => f (X x)).
Definition sq_rv A (X : rvar A) := comp_rv X (fun x => x ^ 2).

End random_variable.

Notation "{ 'rvar' T }" := (rvar_of (Phant T)) : proba_scope.
Notation "`p_ X" := (rv_dist X) : proba_scope.
Notation "'Pr[' X '=' r ']'" := (pr X r) : proba_scope.

Notation "k \cst* X" := (@scale_rv _ k X) : proba_scope.
Notation "X ''/' n" := (@scale_rv _ (1 / INR n) X) : proba_scope.
Notation "X \+_( H ) Y" := (@add_rv _ X Y H) : proba_scope.
Notation "X \-_( H ) Y" := (@sub_rv _ X Y H) : proba_scope.
Notation "X '\+cst' m" := (trans_add_rv X m) : proba_scope.
Notation "X '\-cst' m" := (trans_min_rv X m) : proba_scope.
Notation "X '\^2' " := (sq_rv X) : proba_scope.

(** The ``- log P'' random variable *)
Definition mlog_rv A (P : dist A) : rvar A := mkRvar P (fun x => - log (P x))%R.

Notation "'--log' P" := (mlog_rv P) (at level 5) : proba_scope.

(** Cast operation: *)

Lemma tuple1_of_rvar : forall A, rvar A -> {rvar 'rV[A]_1}.
Proof.
move=> A [d f]; apply mkRvar.
- exact (d `^ 1).
- exact (fun x => f (x ``_ ord0)).
Defined.

Definition cast_rv A : 'rV[rvar A]_1 -> {rvar 'rV[A]_1}.
move=> t.
exact (tuple1_of_rvar (t ``_ ord0)).
Defined.

Section expected_value_definition.

Variable A : finType.
Variable X : rvar A.

Definition Ex := \rsum_(r <- fin_img X) r * Pr[ X = r ].

(** Alternative (simpler) definition of the expected value: *)
Lemma ExE : Ex = \rsum_(a in A) X a * `p_X a.
Proof.
rewrite /Ex.
transitivity (\rsum_(r <- fin_img X) \rsum_(a in A | X a == r) (X a * `p_X a)).
  apply eq_bigr => r _.
  rewrite /pr big_distrr /=.
  apply congr_big => //= a.
    by rewrite inE.
  by rewrite inE => /eqP ->.
by rewrite -sum_parti_finType.
Qed.

Lemma Ex_nonneg : (forall a, 0 <= X a) -> 0 <= Ex.
Proof.
move=> H; rewrite ExE; apply: rsumr_ge0 => i _.
apply mulR_ge0; by [apply H | apply dist_ge0].
Qed.

End expected_value_definition.

Notation "'`E'" := (Ex) : proba_scope.

Section expected_value_for_standard_random_variables.

Variable A : finType.
Variables X Y : rvar A.

Lemma E_scale k : `E (k \cst* X) = k * `E X.
Proof.
rewrite /scale_rv 2!ExE /= big_distrr /=.
apply eq_bigr => i Hi; by rewrite -mulRA.
Qed.

Lemma E_num_int_add (H : `p_X = `p_Y) : `E (X \+_(H) Y) = `E X + `E Y.
Proof.
rewrite 2![in RHS]ExE -big_split /=.
rewrite ExE; apply eq_bigr => i i_A /=; by rewrite mulRDl H.
Qed.

Lemma E_num_int_sub (H : `p_X = `p_Y) : `E (X \-_(H) Y) = `E X - `E Y.
Proof.
rewrite (_ : `E X - `E Y = `E X + - 1 * `E Y)%R; last by field.
rewrite 2![in RHS]ExE big_distrr /= -big_split /=.
rewrite ExE; apply eq_bigr => i i_A /=; rewrite H; field.
Qed.

Lemma E_const k : `E (const_rv k X) = k.
Proof. by rewrite ExE /= -big_distrr /= pmf1 mulR1. Qed.

Lemma E_trans_add_rv m : `E (X \+cst m) = `E X + m.
Proof.
rewrite ExE /trans_add_rv /=.
transitivity (\rsum_(i in A) (X i * `p_X i + m * `p_X i)).
  apply eq_bigr => i Hi /=; field.
by rewrite big_split /= -big_distrr /= pmf1 -ExE mulR1.
Qed.

Lemma E_trans_id_rem m :
  `E ( (X \-cst m) \^2) = `E (X \^2 \-_( erefl ) (2 * m \cst* X) \+cst (m ^ 2)).
Proof. rewrite 2!ExE /=; apply eq_bigr => i Hi; field. Qed.

Lemma E_comp f k : (forall x y, f (x * y) = f x * f y) ->
  `E (comp_rv (k \cst* X) f) = `E (f k \cst* (comp_rv X f)).
Proof.
move=> H; rewrite /comp_rv /= 2!ExE /=.
apply eq_bigr => i i_in_A; rewrite H; field.
Qed.

Lemma E_comp_rv_ext f : `p_X = `p_Y -> rv_fun X = rv_fun Y ->
  `E (comp_rv X f) = `E (comp_rv Y f).
Proof. move=> H1 H2; by rewrite 2!ExE /comp_rv /= H1 H2. Qed.

End expected_value_for_standard_random_variables.

Lemma E_tuple1_of_rvar A : forall (X : rvar A), `E (tuple1_of_rvar X) = `E X.
Proof.
case=> d f.
rewrite 2!ExE /tuple1_of_rvar /=; apply big_rV_1 => // m.
by rewrite -TupleDist1E.
Qed.

(** ** An algebraic proof of the formula of inclusion-exclusion *)

Section probability_inclusion_exclusion.
(** This section gathers a proof of the formula of inclusion-exclusion
    contributed by Erik Martin-Dorel: the corresponding theorem is named
    [Pr_bigcup_incl_excl] and is more general than lemma [Pr_bigcup]. *)
Variable A : finType.
Variable P : dist A.

Lemma bigmul_eq0 (C : finType) (p : pred C) (F : C -> R) :
  (exists2 i : C, p i & F i = R0) <-> \rprod_(i : C | p i) F i = R0.
Proof.
split.
{ by case => [i Hi Hi0]; rewrite (bigD1 i) //= Hi0 mul0R. }
apply big_ind.
- by move=> K; exfalso; auto with real.
- move=> ? ? ? ? /eqP; rewrite mulR_eq0 => /orP[] /eqP; by auto.
- move=> i Hi Hi0; by exists i.
Qed.

Lemma setDUKl (T : finType) (a b : {set T}) : (a :|: b) :\: a = b :\: a.
Proof. by rewrite setDUl setDv set0U. Qed.

Lemma Pr_union_eq (E1 E2 : {set A}) :
  Pr P (E1 :|: E2) = (Pr P E1 + Pr P E2 - Pr P (E1 :&: E2))%R.
Proof.
rewrite -[E1 :|: E2](setID _ E1) Pr_union_disj; last first.
{ rewrite setDE -setIA [E1 :&: _]setIC -setIA [~: E1 :&: _]setIC setICr.
  by rewrite !setI0. }
rewrite setUK setDUKl -{1}[E2 in RHS](setID _ E1) Pr_union_disj; last first.
{ rewrite setDE -setIA [E1 :&: _]setIC -setIA [~: E1 :&: _]setIC setICr.
  by rewrite !setI0. }
by rewrite setIC; ring.
Qed.

(** *** A theory of indicator functions from [A : finType] to [R] *)

Definition Ind (s : {set A}) (x : A) : R := if x \in s then R1 else R0.

Lemma Ind_set0 (x : A) : Ind set0 x = R0.
Proof. by rewrite /Ind inE. Qed.

Lemma Ind_inP (s : {set A}) (x : A) : reflect (Ind s x = R1) (x \in s).
Proof.
apply: (iffP idP); rewrite /Ind; first by move->.
by case: ifP =>//; auto with real.
Qed.

Lemma Ind_notinP (s : {set A}) (x : A) : reflect (Ind s x = R0) (x \notin s).
Proof.
apply: (iffP idP); rewrite /Ind => Hmain.
  by rewrite ifF //; exact: negbTE.
by apply: negbT; case: ifP Hmain =>// _ H10; exfalso; auto with real.
Qed.

Lemma Ind_cap (S1 S2 : {set A}) (x : A) :
  Ind (S1 :&: S2) x = (Ind S1 x * Ind S2 x)%R.
Proof. by rewrite /Ind inE; case: in_mem; case: in_mem=>/=; ring. Qed.

Lemma Ind_bigcap I (e : I -> {set A}) (r : seq.seq I) (p : pred I) x :
  Ind (\bigcap_(j <- r | p j) e j) x = \rprod_(j <- r | p j) (Ind (e j) x).
Proof.
apply (big_ind2 (R1 := {set A}) (R2 := R)); last done.
- by rewrite /Ind inE.
- by move=> sa a sb b Ha Hb; rewrite -Ha -Hb; apply: Ind_cap.
Qed.

(** *** Extra support results for the expected value *)

(** Remark:

    Random variables [X : rvar A] are defined as a record
    gathering a distribution [P : dist A] and a function [f : A -> R].

    For convenience, we locally define the function [rv] for building
    such random variables, endowed with the ambient distribution [P]. *)

Let rv : (A -> R) -> rvar A := mkRvar P.

Lemma E_Ind s : `E (rv (Ind s)) = Pr P s.
Proof.
rewrite ExE /Ex /Ind /Pr (bigID (mem s)) /=.
rewrite [X in _ + X = _]big1; last by move=> i /negbTE ->; rewrite mul0R.
by rewrite addR0; apply: eq_bigr => i ->; rewrite mul1R.
Qed.

Lemma E_ext X2 X1 : X1 =1 X2 -> `E (rv X1) = `E (rv X2).
Proof. by move=> Heq; rewrite !ExE; apply: eq_bigr => i Hi /=; rewrite Heq. Qed.

Lemma E_add X1 X2 : `E (rv (fun w => X1 w + X2 w)) = `E (rv X1) + `E (rv X2).
Proof.
rewrite !ExE; erewrite eq_bigr. (* to replace later with under *)
  2: by move=> i Hi; rewrite mulRDl.
by rewrite big_split.
Qed.

Lemma E_rsum I r p (X : I -> A -> R) :
  `E (rv (fun x => \rsum_(i <- r | p i) X i x)) =
  \rsum_(i <- r | p i) (`E (rv (X i))).
Proof.
rewrite ExE /=; erewrite eq_bigr. (* to replace later with under *)
  2: by move=> a Ha; rewrite big_distrl.
by rewrite exchange_big /=; apply: eq_bigr => i Hi; rewrite ExE.
Qed.

Lemma E_scaler X1 r2 : `E (rv (fun w => X1 w * r2)) = `E (rv X1) * r2.
Proof.
by rewrite !ExE big_distrl /=; apply: eq_bigr => i Hi; rewrite mulRAC.
Qed.

Lemma E_scalel r1 X2 : `E (rv (fun w => r1 * X2 w)) = r1 * `E (rv X2).
Proof.
by rewrite !ExE big_distrr /=; apply: eq_bigr => i Hi; rewrite mulRA.
Qed.

(** [bigA_distr] is a specialization of [bigA_distr_bigA] and at the same
    time a generalized version of [GRing.exprDn] for iterated prod. *)
Lemma bigA_distr (R : Type) (zero one : R) (times : Monoid.mul_law zero)
    (plus : Monoid.add_law zero times)
    (I : finType)
    (F1 F2 : I -> R) :
  \big[times/one]_(i in I) plus (F1 i) (F2 i) =
  \big[plus/zero]_(0 <= k < #|I|.+1)
  \big[plus/zero]_(J in {set I} | #|J| == k)
  \big[times/one]_(j in I) (if j \notin J then F1 j else F2 j).
Proof.
pose F12 i (j : bool) := if ~~ j then F1 i else F2 i.
erewrite eq_bigr. (* to replace later with under *)
  2: move=> i _; rewrite (_: plus (F1 i) (F2 i) = \big[plus/zero]_(j : bool) F12 i j) //.
rewrite bigA_distr_bigA big_mkord (partition_big
  (fun i : {ffun I -> _} => inord #|[set x | i x]|)
  (fun j : [finType of 'I_#|I|.+1] => true)) //=.
{ eapply eq_big =>// i _.
  rewrite (reindex (fun s : {set I} => [ffun x => x \in s])); last first.
  { apply: onW_bij.
    exists (fun f : {ffun I -> bool} => [set x | f x]).
    by move=> s; apply/setP => v; rewrite inE ffunE.
    by move=> f; apply/ffunP => v; rewrite ffunE inE. }
  eapply eq_big.
  { move=> s; apply/eqP/eqP.
      move<-; rewrite -[#|s|](@inordK #|I|) ?ltnS ?max_card //.
      by congr inord; apply: eq_card => v; rewrite inE ffunE.
    move=> Hi; rewrite -[RHS]inord_val -{}Hi.
    by congr inord; apply: eq_card => v; rewrite inE ffunE. }
  by move=> j Hj; apply: eq_bigr => k Hk; rewrite /F12 ffunE. }
rewrite (reindex (fun x : 'I_2 => (x : nat) == 1%N)%bool); last first.
  { apply: onW_bij.
    exists (fun b : bool => inord (nat_of_bool b)).
    by move=> [x Hx]; rewrite -[RHS]inord_val; case: x Hx =>// x Hx; case: x Hx.
    by case; rewrite inordK. }
rewrite 2!big_ord_recl big_ord0 /F12 /=.
by rewrite Monoid.mulm1.
Qed.

Lemma bigID2 (R : Type) (I : finType) (J : {set I}) (F1 F2 : I -> R)
    (idx : R) (op : Monoid.com_law idx) :
  \big[op/idx]_(j in I) (if j \notin J then F1 j else F2 j) =
  op (\big[op/idx]_(j in ~: J) F1 j) (\big[op/idx]_(j in J) F2 j).
Proof.
rewrite (bigID (mem (setC J)) predT); apply: congr2.
by apply: eq_big =>// i /andP [H1 H2]; rewrite inE in_setC in H2; rewrite H2.
apply: eq_big => [i|i /andP [H1 H2]] /=; first by rewrite inE negbK.
by rewrite ifF //; apply: negbTE; rewrite inE in_setC in H2.
Qed.

Lemma bigcap_seq_const I (B : {set A}) (r : seq.seq I) :
  (0 < size r)%nat -> \bigcap_(i <- r) B = B.
Proof.
elim: r => [//|a r IHr] _; rewrite big_cons.
case: r IHr => [|b r] IHr; first by rewrite big_nil setIT.
by rewrite IHr // setIid.
Qed.

Lemma bigcap_ord_const n' (B : {set A}) :
  \bigcap_(i < n'.+1) B = B.
Proof. by rewrite bigcap_seq_const // /index_enum -enumT size_enum_ord. Qed.

Lemma bigcap_const (I : eqType) (B : {set A}) (r : seq.seq I) (p : pred I) :
  (exists2 i : I, i \in r & p i) ->
  \bigcap_(i <- r | p i) B = B.
Proof.
case=> i H1 H2; rewrite -big_filter bigcap_seq_const //.
rewrite size_filter- has_count.
by apply/hasP; exists i.
Qed.

Lemma m1powD k : k <> 0%nat -> (-1)^(k-1) = - (-1)^k.
Proof. by case: k => [//|k _]; rewrite subn1 /= mulN1R oppRK. Qed.

Lemma bigsum_card_constE (I : finType) (B : pred I) x0 :
  \rsum_(i in B) x0 = (INR #|B| * x0)%R.
Proof. by rewrite big_const iter_addR. Qed.

Lemma bigmul_constE (x0 : R) (k : nat) : \rprod_(i < k) x0 = (x0 ^ k)%R.
Proof. by rewrite big_const cardT size_enum_ord iter_mulR. Qed.

Lemma bigmul_card_constE (I : finType) (B : pred I) x0 : \rprod_(i in B) x0 = x0 ^ #|B|.
Proof. by rewrite big_const iter_mulR. Qed.

(** [bigmul_m1pow] is the Reals counterpart of lemma [GRing.prodrN] *)
Lemma bigmul_m1pow (I : finType) (p : pred I) (F : I -> R) :
  \rprod_(i in p) - F i = (-1) ^ #|p| * \rprod_(i in p) F i.
Proof.
rewrite -bigmul_card_constE.
apply: (big_rec3 (fun a b c => a = b * c)).
{ by rewrite mul1R. }
move=> i a b c Hi Habc; rewrite Habc; ring.
Qed.

Let SumIndCap (n : nat) (S : 'I_n -> {set A}) (k : nat) (x : A) :=
  \rsum_(J in {set 'I_n} | #|J| == k) (Ind (\bigcap_(j in J) S j) x).

Lemma Ind_bigcup_incl_excl (n : nat) (S : 'I_n -> {set A}) (x : A) :
  Ind (\bigcup_(i < n) S i) x =
  (\rsum_(1 <= k < n.+1) ((-1)^(k-1) * (SumIndCap S k x)))%R.
Proof.
case: n S => [|n] S; first by rewrite big_ord0 big_geq // Ind_set0.
set Efull := \bigcup_(i < n.+1) S i.
have Halg : \rprod_(i < n.+1) (Ind Efull x - Ind (S i) x) = 0.
  case Ex : (x \in Efull); last first.
  { have /Ind_notinP Ex0 := Ex.
    erewrite eq_bigr. (* to replace later with under *)
      2: by rewrite Ex0.
    have Ex00 : forall i : 'I_n.+1, Ind (S i) x = 0.
      move=> i; apply/Ind_notinP.
      by move/negbT: Ex; rewrite -!in_setC setC_bigcup; move/bigcapP; apply.
    erewrite eq_bigr. (* to replace later with under *)
      2: by move=> i _; rewrite Ex00.
    rewrite subR0.
    by apply/bigmul_eq0; exists ord0. }
  { rewrite /Efull in Ex.
    have /bigcupP [i Hi Hi0] := Ex.
    apply/bigmul_eq0; exists i =>//.
    by rewrite /Efull (Ind_inP _ _ Ex) (Ind_inP _ _ Hi0) subRR. }
rewrite bigA_distr in Halg.
do [erewrite eq_bigr; last by move=> k _; (* to replace later with under *)
    erewrite eq_bigr; last by move=> J _; rewrite bigID2] in Halg.
rewrite big_ltn //= in Halg.
move/eqP in Halg; rewrite -> addR_eq0 in Halg; move/eqP in Halg.
rewrite cardT size_enum_ord (big_pred1 set0) in Halg; last first.
  by move=> i; rewrite pred1E [RHS]eq_sym; apply: cards_eq0.
rewrite [in X in _ * X = _]big_pred0 in Halg; last by move=> i; rewrite inE.
do [erewrite eq_bigl; (* to replace later with under *)
  last by move=> j; rewrite !inE /negb /= ] in Halg.
rewrite mulR1 -Ind_bigcap bigcap_ord_const in Halg.
rewrite {}Halg.
rewrite (big_morph Ropp oppRD oppR0).
rewrite big_nat [RHS]big_nat.
apply: eq_bigr => i Hi; rewrite /SumIndCap /Efull.
rewrite m1powD; last first.
  by case/andP: Hi => Hi _ K0; rewrite K0 in Hi.
rewrite mulNR.
rewrite [in RHS](big_morph _ (morph_mulRDr _) (mulR0 _)).
congr Ropp; apply: eq_bigr => j Hj.
rewrite bigmul_m1pow (eqP Hj).
rewrite (_ : ?[a] * ((-1)^i * ?[b]) = (-1)^i * (?a * ?b)); last by ring.
congr Rmult.
have [Hlt|Hn1] := ltnP i n.+1; last first.
{ rewrite big1; last first.
  { move=> k Hk; rewrite inE in Hk.
    rewrite (_: j = [set: 'I_n.+1]) ?inE // in Hk.
    apply/setP/subset_cardP =>//.
    rewrite (eqP Hj) cardsT /= card_ord.
    by apply/anti_leq/andP; split; first by case/andP: Hi =>//. }
  by rewrite mul1R Ind_bigcap. }
rewrite -!Ind_bigcap bigcap_const; last first.
{ exists (odflt ord0 (pick [pred x | x \notin j])); first exact: mem_index_enum.
  case: pickP; first by move=> y Hy; rewrite !inE -in_setC in Hy.
  move=> /pred0P K; exfalso.
  rewrite /pred0b in K.
  have Hcard := cardsC j.
  rewrite cardsE (eqP K) (eqP Hj) cardT size_enum_ord addn0 in Hcard.
  by rewrite Hcard ltnn in Hlt. }
rewrite -Ind_cap -/Efull.
suff : \bigcap_(j0 in j) S j0 \subset Efull by move/setIidPr->.
rewrite /Efull.
pose i0 := odflt ord0 (pick (mem j)).
have Hi0 : i0 \in j.
{ rewrite /i0; case: pickP =>//.
  move=> /pred0P K; exfalso.
  rewrite /pred0b (eqP Hj) in K.
    by rewrite (eqP K) /= in Hi. }
apply: (subset_trans (bigcap_inf i0 Hi0)).
exact: (bigcup_sup i0).
Qed.

Let SumPrCap (n : nat) (S : 'I_n -> {set A}) (k : nat) :=
  \rsum_(J in {set 'I_n} | #|J| == k) Pr P (\bigcap_(j in J) S j).

Lemma E_SumIndCap n (S : 'I_n -> {set A}) k :
  `E (rv (SumIndCap S k)) = SumPrCap S k.
Proof.
rewrite /SumIndCap /SumPrCap E_rsum; apply: eq_bigr => i Hi.
by rewrite E_Ind.
Qed.

Theorem Pr_bigcup_incl_excl n (S : 'I_n -> {set A}) :
  Pr P (\bigcup_(i < n) S i) =
  \rsum_(1 <= k < n.+1) ((-1)^(k-1) * SumPrCap S k).
Proof.
rewrite -E_Ind ExE /=.
erewrite eq_bigr. (* to replace later with under *)
  2: by move=> ? _; rewrite /= Ind_bigcup_incl_excl.
simpl.
erewrite eq_bigr. (* to replace later with under *)
  2: by move=> a Ha; rewrite big_distrl.
rewrite exchange_big /=.
apply: eq_bigr => i _.
by rewrite -E_SumIndCap -E_scalel ExE.
Qed.

End probability_inclusion_exclusion.

Section markov_inequality.

Variable A : finType.
Variable X : rvar A.
Hypothesis X_nonneg : forall a, 0 <= X a.

Definition pr_geq (X : rvar A) r := Pr `p_X [set x | X x >b= r].

Local Notation "'Pr[' X '>=' r ']'" := (pr_geq X r).

Lemma Ex_lb (r : R) : r * Pr[ X >= r] <= `E X.
Proof.
rewrite ExE.
rewrite (bigID [pred a' | X a' >b= r]) /=.
rewrite -[a in a <= _]addR0.
apply leR_add; last first.
  apply rsumr_ge0 => a _.
  apply mulR_ge0; by [apply X_nonneg | apply dist_ge0].
apply (@leR_trans (\rsum_(i | X i >b= r) r * `p_ X i)).
  rewrite big_distrr /=;  apply/Req_le/eq_bigl => a; by rewrite inE.
apply ler_rsum => a Xar.
apply/leR_wpmul2r; [exact/dist_ge0 | exact/leRP].
Qed.

Lemma markov (r : R) : 0 < r -> Pr[X >= r] <= `E X / r.
Proof.
move=> ?; apply/leRP.
rewrite /Rdiv leR_pdivl_mulr // mulRC; exact/leRP/Ex_lb.
Qed.

End markov_inequality.

Notation "'Pr[' X '>=' r ']'" := (pr_geq X r) : proba_scope.

(** * Variance *)

Section variance_definition.

Variable A : finType.
Variable X : rvar A.

(** Variance of a random variable (\sigma^2(X) = V(X) = E (X^2) - (E X)^2): *)
Definition Var := let miu := `E X in `E ((X \-cst miu) \^2).

(** Alternative form for computing the variance
   (V(X) = E(X^2) - E(X)^2 \cite[Theorem 6.6]{probook}): *)
Lemma V_alt : Var = `E (X \^2)  - (`E X) ^ 2.
Proof.
rewrite /Var E_trans_id_rem E_trans_add_rv E_num_int_sub E_scale; field.
Qed.

End variance_definition.

Notation "'`V'" := (Var) : proba_scope.

Section variance_properties.

Variable A : finType.
Variable X : rvar A.

(** The variance is not linear V (k X) = k^2 V (X) \cite[Theorem 6.7]{probook}: *)
Lemma V_scale k : `V (k \cst* X) = k ^ 2 * `V X.
Proof.
rewrite {1}/`V [in X in X = _]/= E_scale.
rewrite (@E_comp_rv_ext _ ((k \cst* X) \-cst k * `E X) (k \cst* (X \+cst - `E X))) //; last first.
  apply functional_extensionality => /= x; field.
rewrite E_comp; last by move=> x y; field.
by rewrite E_scale.
Qed.

End variance_properties.

Lemma V_tuple1_of_rvar A : forall (X : rvar A), `V (tuple1_of_rvar X) = `V X.
Proof.
case=> d f.
rewrite /`V !E_tuple1_of_rvar !ExE; apply: big_rV_1 => // i.
by rewrite TupleDist1E.
Qed.

(** (Probabilistic statement.)
 In any data sample, "nearly all" the values are "close to" the mean value:
 Pr[ |X - E X| \geq \epsilon] \leq V(X) / \epsilon^2 *)
Section chebyshev.

Variable A : finType.
Variable X : rvar A.

Lemma chebyshev_inequality epsilon : 0 < epsilon ->
  Pr `p_X [set a | `| X a - `E X | >b= epsilon] <= `V X / epsilon ^ 2.
Proof.
move=> He; apply/leRP.
rewrite leR_pdivl_mulr; last exact/pow_gt0.
apply/leRP; rewrite mulRC /`V [in X in _ <= X]ExE.
rewrite (_ : `p_ ((X \-cst `E X) \^2) = `p_ X) //.
apply (@leR_trans (\rsum_(a in A | `| X a - `E X | >b= epsilon)
    (((X \-cst `E X) \^2) a  * `p_X a)%R)); last first.
  apply ler_rsum_l_support with (Q := xpredT) => // a .
  apply mulR_ge0; [exact: pow_even_ge0| exact: dist_ge0].
rewrite /Pr big_distrr [_ \^2]lock /= -!lock.
apply ler_rsum_l => i Hi; rewrite /= -!/(_ ^ 2).
- apply leR_wpmul2r; first exact: dist_ge0.
  move: Hi; rewrite inE -(sqR_norm (X i - _)) => H.
  apply/pow_incr; split => //; [exact/ltRW | exact/leRP].
- apply mulR_ge0; [exact: pow_even_ge0 | exact: dist_ge0].
- move: Hi; by rewrite inE.
Qed.

End chebyshev.

Section joint_dist.

Variable A : finType.
Variable P1 : dist A.
Variable n : nat.
Variable P2 : {dist 'rV[A]_n}.
Variable P : {dist 'rV[A]_n.+1}.

Definition joint :=
  (forall x, P1 x = \rsum_(t in 'rV[A]_n.+1 | t ``_ ord0 == x) P t) /\
  (forall x, P2 x = \rsum_(t in 'rV[A]_n.+1 | rbehead t == x) P t).

End joint_dist.

Lemma joint_prod_n_base_case A (P : dist A) : joint P (P `^ O) (P `^ 1).
Proof.
rewrite /joint; split => x.
- rewrite (big_pred1 (\row_(j < 1) x)); first by rewrite TupleDist1E mxE.
  move=> /= m.
  apply/eqP/eqP => [<- | ->].
    by apply/matrixP => a b; rewrite {a}(ord1 a) {b}(ord1 b) mxE.
  by rewrite mxE.
- rewrite TupleDist0E -(pmf1 (P `^ 1)).
  apply eq_bigl => /= m.
  rewrite inE.
  apply/esym/eqP.
  rewrite /rbehead.
  by apply/matrixP => a [].
Qed.

(** The tuple distribution is a joint distribution: *)
Lemma joint_prod_n : forall n A (P : dist A), joint P (P `^ n) (P `^ n.+1).
Proof.
case; first by apply joint_prod_n_base_case.
move=> n B d; split => x.
- transitivity (\rsum_(i in 'rV[B]_n.+1) (d `^ n.+1) i * d x)%R.
    by rewrite -big_distrl /= (pmf1 (d `^ n.+1)) mul1R.
  rewrite -big_rV_cons; apply eq_bigr => i Hi.
  by rewrite [in X in _ = X]TupleDistSE mulRC row_mx_row_ord0 rbehead_row_mx.
- rewrite -big_rV_behead.
  transitivity (\rsum_(i in B) d i * (d `^ n.+1 x))%R.
    by rewrite -big_distrl /= (pmf1 d) mul1R.
  apply eq_bigr => i _.
  by rewrite [in X in _ = X]TupleDistSE row_mx_row_ord0 rbehead_row_mx.
Qed.

Section identically_distributed.

Variable A : finType.
Variable P : dist A.
Variable n : nat.

(** The random variables Xs are identically distributed with distribution P: *)
(*Definition id_dist (Xs : n.-tuple (rvar A)) := forall i, `p_(Xs \_ i) = P.*)
Definition id_dist (Xs : 'rV[rvar A]_n) := forall i, `p_(Xs ``_ i) = P.

End identically_distributed.

Section independent_random_variables.

Variables (A : finType) (X : rvar A).
Variable n : nat.
Variable Y : {rvar 'rV[A]_n}.
Variable P : {dist 'rV[A]_n.+1}.

Definition inde_rv := forall x y,
  Pr P [set xy : 'rV_n.+1 | (X (xy ``_ ord0) == x) && (Y (rbehead xy) == y)] =
  (Pr[X = x] * Pr[Y = y])%R.

End independent_random_variables.

Notation "X _| P |_ Y" := (inde_rv X Y P) : proba_scope.

(** Independent random variables over the tuple distribution: *)
Lemma inde_rv_tuple_pmf_dist A (P : dist A) n (x y : R) (Xs : 'rV[rvar A]_n.+2) :
  id_dist P Xs ->
    Pr (P `^ n.+2) [set xy : 'rV__ | (- log (P (xy ``_ ord0)) == x)%R &&
      (\rsum_(i : 'I_n.+1)
       - log (`p_ ((rbehead Xs) ``_ i) (rbehead xy) ``_ i) == y)%R] =
    (Pr P [set a | - log (P a) == x] *
    Pr (P `^ n.+1) [set ta : 'rV__ |
      \rsum_(i : 'I_n.+1) - log (`p_ ((rbehead Xs) ``_ i) ta ``_ i) == y])%R.
Proof.
move=> Hid_dist.
rewrite /Pr.
move: (big_rV_cons_behead_support addR_comoid
  (fun i : 'rV[A]_n.+2 => P `^ _ i)
  [set a | (- log (P a) == x)%R]
  [set t : 'rV__ | \rsum_(i < n.+1) - log (`p_ ((rbehead Xs) ``_ i) t ``_ i) == y])%R => H.
eapply trans_eq.
  eapply trans_eq; last by symmetry; apply H.
  apply eq_bigl => ta /=; by rewrite !inE.
transitivity (\rsum_(a in [set a | (- log (P a) == x)%R])
  \rsum_(a' in [set ta : 'rV__ | \rsum_(i < n.+1) - log (`p_ ((rbehead Xs) ``_ i) ta ``_ i) == y])
  P a * P `^ _ a')%R.
  apply eq_bigr => a _.
  apply eq_bigr => ta _.
  by rewrite TupleDistSE row_mx_row_ord0 rbehead_row_mx.
rewrite big_distrl /=.
apply eq_bigr => a _; by rewrite -big_distrr.
Qed.

Section sum_two_rand_var_def.

Variable A : finType.
Variable X1 : rvar A.
Variable n : nat.
Variable X2 : {rvar 'rV[A]_n.+1}.
Variable X : {rvar 'rV[A]_n.+2}.

Definition sum := joint `p_X1 `p_X2 `p_X /\
  X =1 fun x => (X1 (x ``_ ord0) + X2 (rbehead x))%R.

End sum_two_rand_var_def.

Notation "Z \= X '@+' Y" := (sum X Y Z) : proba_scope.

Section sum_two_rand_var.

Variable A : finType.
Variable X1 : rvar A.
Variable n : nat.
Variable X2 : {rvar 'rV[A]_n.+1}.
Variable X : {rvar 'rV[A]_n.+2}.

(** The expected value of a sum is the sum of expected values,
   whether or not the summands are mutually independent
   (the ``First Fundamental Mystery of Probability'' \cite[Theorem 6.2]{probook}): *)
Lemma E_linear_2 : X \= X1 @+ X2 -> `E X = (`E X1 + `E X2)%R.
Proof.
case=> Hjoint Hsum.
rewrite !ExE /=.
transitivity (\rsum_(ta in 'rV[A]_n.+2)
  (X1 (ta ``_ ord0) * `p_X ta + X2 (rbehead ta) * `p_X ta)%R).
- apply eq_bigr => ta _; by rewrite Hsum mulRDl.
- rewrite big_split => //=; f_equal.
  + transitivity (\rsum_(a in A) (X1 a * \rsum_(ta in 'rV[A]_n.+1) `p_X (row_mx (\row_(k < 1) a) ta)))%R.
    * rewrite -(big_rV_cons_behead _ _ xpredT xpredT).
      apply eq_bigr => a _.
      rewrite big_distrr /=.
      apply eq_bigr => i _.
      by rewrite row_mx_row_ord0.
    * apply eq_bigr => a _.
      case: Hjoint.
      move/(_ a) => /= -> _.
      by rewrite big_rV_cons.
  + transitivity (\rsum_(ta in 'rV[A]_n.+1) (X2 ta * \rsum_(a in A) `p_X (row_mx (\row_(k < 1) a) ta))%R).
    * rewrite -(big_rV_cons_behead _ _ xpredT xpredT) exchange_big /=.
      apply eq_bigr => ta _; rewrite big_distrr /=.
      apply eq_bigr => a _.
      by rewrite rbehead_row_mx.
    * apply eq_bigr => ta _.
      case: Hjoint => _.
      move/(_ ta) => /= ->.
      by rewrite -big_rV_behead.
Qed.

(* TODO: relation with theorem 6.4 of probook (E(XY)=E(X)E(Y))? *)

Lemma E_id_rem_helper : X \= X1 @+ X2 -> X1 _| `p_X |_ X2 ->
  \rsum_(i in 'rV[A]_n.+2)(X1 (i ``_ ord0) * X2 (rbehead i) * `p_X i)%R =
    (`E X1 * `E X2)%R.
Proof.
case=> Hjoint Hsum Hinde.
apply trans_eq with (\rsum_(r <- undup (map X1 (enum A)))
   \rsum_(r' <- undup (map X2 (enum ('rV[A]_n.+1))))
   ( r * r' * Pr[ X1 = r] * Pr[ X2 = r' ]))%R; last first.
  symmetry.
  rewrite big_distrl /=.
  apply eq_bigr => i _.
  rewrite big_distrr /=.
  apply eq_bigr => j _.
  rewrite mulRA. f_equal. rewrite -!mulRA. f_equal. by rewrite mulRC.
rewrite -(big_rV_cons_behead _ _ xpredT xpredT).
apply trans_eq with (\rsum_(a in A) \rsum_(j in 'rV[A]_n.+1)
  (X1 a * X2 j * `p_X (row_mx (\row_(k < 1) a) j)))%R.
  apply eq_bigr => a _.
  apply eq_bigr => ta _.
  by rewrite row_mx_row_ord0 rbehead_row_mx.
rewrite (sum_parti _ X1); last by rewrite /index_enum -enumT; apply enum_uniq.
rewrite /index_enum -enumT.
apply eq_bigr => r _.
rewrite {1}enumT exchange_big /= (sum_parti _ X2); last first.
  rewrite /index_enum -enumT; by apply enum_uniq.
rewrite /index_enum -enumT.
apply eq_bigr => r' _.
apply trans_eq with (r * r' * \rsum_(i0 | X2 i0 == r') \rsum_(i1 | X1 i1 == r)
    (`p_X (row_mx (\row_(k < 1) i1) i0)))%R.
  rewrite big_distrr /= /index_enum -!enumT.
  apply eq_bigr => ta ta_r'.
  rewrite big_distrr /=.
  apply eq_bigr => a a_l.
  move/eqP : ta_r' => <-.
  by move/eqP : a_l => <-.
rewrite -!mulRA.
congr (_ * (_ * _))%R.
rewrite exchange_big /=.
move: {Hinde}(Hinde r r') => <-.
rewrite /Pr.
move: (big_rV_cons_behead_support addR_comoid (fun a => `p_ X a) [set j0 | X1 j0 == r]
  [set i0 | X2 i0 == r']) => H'.
eapply trans_eq.
  eapply trans_eq; last by apply H'.
  apply eq_big.
    move=> a /=; by rewrite inE.
  move=> a /eqP Ha.
  apply eq_bigl => ta /=; by rewrite inE.
apply eq_bigl => ta /=; by rewrite !inE.
Qed.

(** Expected Value of the Square (requires mutual independence): *)
Lemma E_id_rem : X \= X1 @+ X2 -> X1 _| `p_X |_ X2 ->
  `E (X \^2) = (`E (X1 \^2) + 2 * `E X1 * `E X2 + `E (X2 \^2))%R.
Proof.
case=> Hsum1 Hsum2 Hinde.
rewrite [in LHS]ExE.
apply trans_eq with (\rsum_(i in 'rV[A]_n.+2)
      ((X1 (i ``_ ord0) + X2 (rbehead i)) ^ 2%N * `p_X i))%R.
  apply eq_bigr => i _; by rewrite /sq_rv /= Hsum2.
apply trans_eq with (\rsum_(i in 'rV[A]_n.+2)
  ((X1 (i ``_ ord0)) ^ 2 + 2 * X1 (i ``_ ord0) * X2 (rbehead i) + (X2 (rbehead i)) ^ 2) *
    `p_X i)%R.
  apply eq_bigr => ? _; by rewrite sqrRD.
apply trans_eq with (\rsum_(i in 'rV[A]_n.+2)
  ((X1 (i ``_ ord0)) ^ 2 * `p_X i +  2 * X1 (i ``_ ord0) * X2 (rbehead i) * `p_X i +
   (X2 (rbehead i)) ^ 2 * `p_X i))%R.
  apply eq_bigr => ? ?; by field.
rewrite !big_split /=.
f_equal.
- f_equal.
  + rewrite ExE -(big_rV_cons_behead _ _ xpredT xpredT) /=.
    apply eq_bigr => i _.
    apply trans_eq with (X1 i ^ 2 * \rsum_(j in 'rV[A]_n.+1) `p_X (row_mx (\row_(k < 1) i) j))%R.
    * rewrite big_distrr /=.
      apply eq_bigr => i0 _.
      by rewrite row_mx_row_ord0.
    * congr (_ * _)%R.
      case: Hsum1 => -> _.
      exact: big_rV_cons.
  + rewrite -mulRA -(E_id_rem_helper (conj Hsum1 Hsum2)) // big_distrr /=.
    apply eq_bigr => i _; field.
- rewrite ExE -(big_rV_cons_behead _ _ xpredT xpredT).
  rewrite exchange_big /=.
  apply eq_bigr => t _.
  apply trans_eq with (X2 t ^ 2 * \rsum_(i0 in A) (`p_X (row_mx (\row_(k < 1) i0) t)))%R.
  + rewrite big_distrr /=; apply eq_bigr => i0 Hi0.
    by rewrite rbehead_row_mx.
  + congr (_ * _)%R.
    case: Hsum1 => _ ->.
    exact: big_rV_behead.
Qed.

(** The variance of the sum is the sum of variances for any two
  independent random variables %(\cite[Theorem 6.8]{probook})%: *)
Lemma V_linear_2 : X \= X1 @+ X2 -> X1 _| `p_X |_ X2  -> `V X = (`V X1 + `V X2)%R.
Proof.
move=> H ?; rewrite !V_alt E_id_rem // (E_linear_2 H) sqrRD; by field.
Qed.

End sum_two_rand_var.

Section sum_n_rand_var_def.

Variable A : finType.

(** The sum of n >= 1 random variable(s): *)
Inductive sum_n : forall n,
  {rvar 'rV[A]_n} -> 'rV[rvar A]_n -> Prop :=
| sum_n_1 : forall X, cast_rv X \=sum X
| sum_n_cons : forall n (Xs : 'rV_n.+1) Y X Z,
  Y \=sum Xs -> Z \= X @+ Y -> Z \=sum (row_mx (\row_(k < 1) X) Xs)
where "X '\=sum' Xs" := (sum_n X Xs) : proba_scope.

End sum_n_rand_var_def.

Notation "X '\=sum' Xs" := (sum_n X Xs) : proba_scope.

Section sum_n_rand_var.

Variable A : finType.

Lemma E_linear_n : forall n (Xs : 'rV[rvar A]_n) X,
  X \=sum Xs -> `E X = \rsum_(i < n) `E Xs ``_ i.
Proof.
elim => [Xs Xbar | [_ Xs Xbar | n IHn Xs Xbar] ].
- by inversion 1.
- inversion 1; subst.
  apply Eqdep_dec.inj_pair2_eq_dec in H0; last by exact eq_nat_dec.
  apply Eqdep_dec.inj_pair2_eq_dec in H1; last by exact eq_nat_dec.
  subst Xs Xbar.
  rewrite big_ord_recl big_ord0 addR0 /cast_rv.
  by rewrite E_tuple1_of_rvar.
- inversion 1; subst.
  apply Eqdep_dec.inj_pair2_eq_dec in H1; last by exact eq_nat_dec.
  apply Eqdep_dec.inj_pair2_eq_dec in H2; last by exact eq_nat_dec.
  subst Z Xs.
  move: {IHn}(IHn _ _ H3) => IHn'.
  rewrite big_ord_recl.
  have -> : \rsum_(i : 'I_n.+1) `E ((row_mx (\row_(k < 1) X) Xs0) ``_ (lift ord0 i)) =
       \rsum_(i : 'I_n.+1) `E (Xs0 ``_ i).
    apply eq_bigr => i _ /=.
    rewrite !ExE.
    apply eq_bigr => a _ /=.
    set tmp := row_mx _ _ _ _.
    suff : tmp = Xs0 ``_ i by move=> ->.
    rewrite /tmp.
    rewrite mxE.
    case: splitP => //.
      by move=> j; rewrite {j}(ord1 j).
    move=> k.
    by rewrite lift0 add1n => [] [] /ord_inj ->.
  rewrite -IHn' (E_linear_2 H4).
  by rewrite row_mx_row_ord0.
Qed.

End sum_n_rand_var.

Section sum_n_independent_rand_var_def.

Variable A : finType.

(** The sum of n >= 1 independent random variables: *)

Inductive isum_n : forall n,
  {rvar 'rV[A]_n} -> 'rV[rvar A]_n -> Prop :=
| isum_n_1 : forall X, cast_rv X \=isum X
| isum_n_cons : forall n (Ys : 'rV_n.+1) Y X Z,
  Y \=isum Ys -> Z \= X @+ Y -> X _| `p_Z |_ Y ->
  Z \=isum (row_mx (\row_(k < 1) X) Ys)
where "X '\=isum' Xs" := (isum_n X Xs) : proba_scope.

End sum_n_independent_rand_var_def.

Notation "X '\=isum' Xs" := (isum_n X Xs) : proba_scope.

Section sum_n_independent_rand_var.

Variable A : finType.

Lemma sum_n_i_sum_n : forall n (Xs : 'rV[rvar A]_n) X,
  X \=isum Xs -> X \=sum Xs.
Proof.
move=> n Xs Xsum.
elim.
- move=> X; by constructor 1.
- move=> n0 lst Z W Z' H1 H2 H3 H4.
  by econstructor 2; eauto.
Qed.

Lemma V_linearity_isum : forall n
  (X : {rvar 'rV[A]_n}) (Xs : 'rV[rvar A]_n),
  X \=isum Xs ->
  forall sigma2, (forall i, `V (Xs ``_ i) = sigma2) ->
  `V X = (INR n * sigma2)%R.
Proof.
elim.
  move=> X Xs X_Xs sigma2 Hsigma2.
  by inversion X_Xs.
case=> [_ | n IH] Xsum Xs Hsum s Hs.
  inversion Hsum.
  apply Eqdep_dec.inj_pair2_eq_dec in H; last by exact eq_nat_dec.
  apply Eqdep_dec.inj_pair2_eq_dec in H0; last by exact eq_nat_dec.
  subst Xs Xsum.
  rewrite /cast_rv V_tuple1_of_rvar /= mul1R.
  exact: Hs.
have {IH}IH : forall Xsum (Xs : 'rV[rvar A]_n.+1),
  Xsum \=isum Xs ->
  forall sigma2, (forall i, `V (Xs ``_ i) = sigma2) ->
    `V Xsum = (INR n.+1 * sigma2)%R by apply IH.
move: Hsum; inversion 1.
apply Eqdep_dec.inj_pair2_eq_dec in H0; last by exact eq_nat_dec.
apply Eqdep_dec.inj_pair2_eq_dec in H1; last by exact eq_nat_dec.
subst Z n0 Xs.
move: {IH}(IH Y Ys H2) => IH.
rewrite S_INR mulRDl -IH.
+ by rewrite mul1R addRC (@V_linear_2 _ _ _ _ _ H3) // -(Hs ord0) /= row_mx_row_ord0.
+ move=> i; rewrite -(Hs (lift ord0 i)).
  congr (`V _).
  rewrite mxE.
  case: splitP.
    move=> j; by rewrite {j}(ord1 j) lift0.
  move=> k.
  rewrite lift0 add1n.
  by case => /ord_inj ->.
Qed.

(** The variance of the average for independent random variables: *)

Lemma V_average_isum n (X : {rvar 'rV[A]_n}) Xs (sum_Xs : X \=isum Xs) :
  forall sigma2, (forall i, `V (Xs ``_ i) = sigma2) ->
  (INR n * `V (X '/ n))%R = sigma2.
Proof.
move=> s Hs.
destruct n.
  by inversion sum_Xs.
rewrite (V_scale X) // (V_linearity_isum sum_Xs Hs) //; field; exact/INR_eq0.
Qed.

End sum_n_independent_rand_var.

Section weak_law_of_large_numbers.

Variable A : finType.
Variable P : dist A.
Variable n : nat.
Variable Xs : 'rV[rvar A]_n.+1.     Hypothesis Xs_id : id_dist P Xs.
Variable miu : R.                   Hypothesis E_Xs : forall i, `E Xs ``_ i = miu.
Variable sigma2 : R.                Hypothesis V_Xs : forall i, `V Xs ``_ i = sigma2.
Variable X : {rvar 'rV[A]_n.+1}.
Variable X_Xs : X \=isum Xs.

Lemma wlln epsilon : 0 < epsilon ->
  Pr `p_X [set t | `| (X '/ n.+1) t - miu | >b= epsilon] <= sigma2 / ((INR n.+1) * epsilon ^ 2).
Proof.
move=> He.
have HV : `V (X '/ n.+1) = sigma2 / INR n.+1.
  rewrite -(V_average_isum X_Xs V_Xs) V_scale //; by field; exact/INR_eq0.
rewrite /Rdiv invRM; last 2 first.
  by rewrite INR_eq0.
  exact/gtR_eqF/pow_gt0.
rewrite mulRA (_ : sigma2 * / INR n.+1 = sigma2 / INR n.+1)%R // -{}HV.
have HE : `E (X '/ n.+1) = miu.
  rewrite E_scale (E_linear_n (sum_n_i_sum_n X_Xs)).
  set su := \rsum_(_<-_) _.
  have -> : su = (INR n.+1 * miu)%R.
    rewrite /su.
    transitivity (\rsum_(i < n.+1) miu); first exact/eq_bigr.
    by rewrite big_const /= iter_addR cardE /= size_enum_ord.
  by field; exact/INR_eq0.
rewrite -{}HE.
have cheby : Pr `p_(X '/ n.+1)
  [set t | `| X t / INR n.+1 - `E (X '/ n.+1) | >b= epsilon] <= `V (X '/ n.+1) / epsilon ^ 2.
  move: (chebyshev_inequality (X '/ n.+1) He) => cheby.
  set g := [set _ | _] in cheby; rewrite (@Pr_ext _ _ _ g) //.
  apply/setP => ta /=.
  by rewrite !inE /= mulRC mulRA mulR1.
set p1 := Pr _ _ in cheby. set p2 := Pr _ _. suff : p2 = p1 by move=> ->.
rewrite /p1 /p2 /=.
apply Pr_ext; apply/setP => ta /=; by rewrite !inE mul1R mulRC.
Qed.

End weak_law_of_large_numbers.
