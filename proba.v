(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.
Require Import Reals Lra Nsatz FunctionalExtensionality.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop.

(** * Formalization of discrete probabilities *)

(** OUTLINE
  1. Section distribution_definition.
       Distribution over sample space A
       (numerically-valued distribution function p : A -> R;
        for any a \in A, 0 <= p(a); \sum_{i \in A} p(i) = 1)
  2. Module Dist1.
  3. Module DistBind.
  4. Module Uniform.
       Uniform distribution
  5. Module UniformSupport.
       Uniform distribution with a restricted support
  6. Module Binary.
       Binary distributions (distributions over sets with two elements)
     Section binary_distribution_prop.
  7. Module BinarySupport.
  8. Module D1Dist.
       construction of a distribution from another
       by removing one element from the support
  9. Module ConvexDist.
  10. Module FamilyDist.
  11. Module Bivar.
       Joint (Bivariate) Distribution
  12. Module Multivar
        multivariate distribution
      Section joint_dist_rV.
      Section joint_rV_dist.
      Section joint_tuple_dist.
  13. Module ProdDist.
  14. Module TupleDist.
  15. Section wolfowitz_counting.
        Wolfowitz's counting principle
  16. Section probability.
        Probability of an event P with distribution p (Pr_p[P] = \sum_{i \in A, P\,i} \, p(i))
  17. Section random_variable.
        Definition of a random variable (R-valued) with a distribution
        pr: Probability that a random variable evaluates to r \in R
  18. Section expected_value_definition.
        Expected value of a random variable
      Section expected_value_for_standard_random_variables.
        Properties of the expected value of standard random variables
  19. Section probability_inclusion_exclusion.
        An algebraic proof of the formula of inclusion-exclusion (by Erik Martin-Dorel)
  20. Section markov_inequality.
  21. Section variance_definition.
      Section variance_properties.
  22. Section chebyshev.
        Chebyshev's Inequality
  23. Section identically_distributed.
        Identically Distributed Random Variables
  24. Section independent_random_variables.
      Section sum_two_rand_var_def.
        The sum of two random variables
      Section sum_two_rand_var.
      Section sum_n_rand_var_def.
      Section sum_n_rand_var.
      Section sum_n_independent_rand_var_def.
      Section sum_n_independent_rand_var.
  25. Section weak_law_of_large_numbers.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "{ 'dist' T }" (at level 0, format "{ 'dist'  T }").
Reserved Notation "'`U' HC " (at level 10, HC at next level).
Reserved Notation "P `^ n" (at level 5).
Reserved Notation "P1 `x P2" (at level 6).
Reserved Notation "P1 `, P2" (at level 6).
Reserved Notation "{ 'rvar' T }" (at level 0, format "{ 'rvar'  T }").
Reserved Notation "`p_ X" (at level 5).
Reserved Notation "'Pr[' X '=' r ']'" (at level 5, X at next level,
  r at next level, format "Pr[ X  =  r ]").
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
Reserved Notation "P |= X _|_ Y" (at level 50, X, Y at next level,
  format "P  |=  X  _|_  Y").
Reserved Notation "Z \= X '@+' Y" (at level 50).

Local Open Scope R_scope.
Local Open Scope reals_ext_scope.
Local Open Scope tuple_ext_scope.

Section distribution_definition.

Variable A : finType.

Record dist := mkDist {
  pmf :> A -> R+ ;
  pmf1 : \rsum_(a in A) pmf a = 1}.

Definition is_dist (f : A -> R) : Prop :=
  (forall a, 0 <= f a) /\ (\rsum_(a in A) f a = 1).

Lemma dist_is_dist (d : dist) : is_dist d.
Proof. by case: d; case => /= f pmf0 pmf1. Qed.

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

Lemma dist_ind (P : dist -> Prop) :
  (forall n : nat, (forall X, #|dist_supp X| = n -> P X) ->
    forall X b, #|dist_supp X| = n.+1 -> X b != 0 -> P X) ->
  forall X, P X.
Proof.
move=> H1 d.
move: {-2}(#|dist_supp d|) (erefl (#|dist_supp d|)) => n; move: n d.
elim=> [d /esym /card0_eq Hd0|].
  move: (pmf1 d).
  rewrite -[X in X = _]mul1R big_distrr rsum_dist_supp.
  rewrite big1 => [H01|a].
    by elim: (gtR_eqF _ _ Rlt_0_1).
  by rewrite Hd0.
move=> n IH d n13.
have [b Hb] : exists b : A, d b != 0.
  suff : {x | x \in dist_supp d} by case => a; rewrite inE => ?; exists a.
  apply/sigW/set0Pn; by rewrite -cards_eq0 -n13.
by refine (H1 n _ _ _ _ Hb) => // d' A2; apply IH.
Qed.

Definition makeDist (pmf : A -> R) (H0 : forall a, 0 <= pmf a)
  (H1 : \rsum_(a in A) pmf a = 1%R) := @mkDist (@mkPosFun _ pmf H0) H1.

Lemma dist_ge0 (P : dist) a : 0 <= P a.
Proof. exact: pos_f_ge0. Qed.

Lemma dist_neq0 (P : dist) a : (P a != 0) <-> (0 < P a).
Proof.
split => H; [|by move/gtR_eqF : H => /eqP].
rewrite ltR_neqAle; split; [exact/nesym/eqP|exact/dist_ge0].
Qed.

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

Lemma dist_ext d d' : (forall x, pos_f (pmf d) x = pos_f (pmf d') x) -> d = d'.
Proof. move=> ?; exact/dist_eq/pos_fun_eq/functional_extensionality. Qed.

Lemma dist_supp_singleP (d : dist) a :
  reflect (d a = 1) (dist_supp d == [set a]).
Proof.
apply: (iffP idP) => [/eqP Ha | Xa1].
  rewrite -(pmf1 d) (eq_bigr (fun i => 1 * d i)) => *; last by rewrite mul1R.
  by rewrite rsum_dist_supp Ha big_set1 mul1R.
have H : forall a0, a0 != a -> d a0 = 0.
  apply/(@prsumr_eq0P _ [pred x | x != a] d).
    move=> ? _; exact/dist_ge0.
  move/eqP : (pmf1 d).
  by rewrite (bigD1 a) //= Xa1 eq_sym addRC -subR_eq subRR => /eqP.
apply/eqP/setP => a0; rewrite !inE.
case/boolP : (_ == _ :> A) => /= [/eqP ->|/H ->]; last by rewrite eqxx.
rewrite Xa1; exact/eqP.
Qed.

Definition eqdist (d d' : dist) := [forall a, d a == d' a].

Lemma eqdistP : Equality.axiom eqdist.
Proof.
move=> d d'; apply: (iffP idP) => [/forallP H|->].
- by apply/dist_ext => a; rewrite (eqP (H a)).
- by apply/forallP => ?; rewrite eqxx.
Qed.

Canonical dist_eqMixin := EqMixin eqdistP.
Canonical dist_eqType := Eval hnf in EqType _ dist_eqMixin.

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

Definition d : dist A := locked (makeDist f0 f1).

Lemma dE a0 : d a0 = INR (a0 == a)%bool.
Proof. by rewrite /d; unlock. Qed.

End dist1.
End Dist1.

Module DistMap.
Section distmap.
Variables (A B : finType) (g : A -> B) (p : dist A).

Definition f b := \rsum_(a in A | g a == b) p a.

Lemma f0 b : 0 <= f b. Proof. apply: rsumr_ge0 => a _; exact/dist_ge0. Qed.

Lemma f1 : \rsum_(b in B) f b = 1%R.
Proof. by rewrite -(pmf1 p) (@partition_big _ _ _ _ _ _ g xpredT). Qed.

Definition d : dist B := locked (makeDist f0 f1).

Definition dE x : d x = f x. Proof. by rewrite /d; unlock. Qed.

End distmap.
End DistMap.

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

(* TODO: lock? *)
Definition d : dist B := makeDist f0 f1.

Lemma dE x : d x = f x.
Proof. by []. Qed.

End distbind.
End DistBind.

Lemma DistBind1f (A B : finType) (a : A) (f : A -> dist B) :
  DistBind.d (Dist1.d a) f = f a.
Proof.
apply/dist_ext => b.
rewrite /DistBind.d /= /DistBind.f (bigD1 a) //= Dist1.dE eqxx mul1R.
rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 ?addR0 // => c ca.
by rewrite Dist1.dE (negbTE ca) mul0R.
Qed.

Lemma DistBindp1 A (p : dist A) : DistBind.d p (@Dist1.d A) = p.
Proof.
apply/dist_ext => /= a; rewrite /DistBind.f (bigD1 a) //= Dist1.dE eqxx mulR1.
rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 /= ?addR0 //.
by move=> b ba; rewrite Dist1.dE eq_sym (negbTE ba) mulR0.
Qed.

Lemma DistBindA A B C (m : dist A) (f : A -> dist B) (g : B -> dist C) :
  DistBind.d (DistBind.d m f) g = DistBind.d m (fun x => DistBind.d (f x) g).
Proof.
apply/dist_ext => c.
rewrite /DistBind.d /DistBind.f /=.
rewrite (eq_bigr (fun a => (\rsum_(a0 in A) m a0 * (f a0) a * (g a) c))); last first.
  move=> b _; by rewrite big_distrl.
rewrite exchange_big /=; apply eq_bigr => a _.
rewrite big_distrr /=; apply eq_bigr => b _; by rewrite mulRA.
Qed.

Section map_bind_dist.
Variables (A B : finType) (g : A -> B).

Definition fmap_dist (p : dist A) : dist B :=
  DistBind.d p (fun a => Dist1.d (g a)).

Lemma fmap_distE (p : dist A) : DistMap.d g p = fmap_dist p.
Proof.
apply/dist_ext => b; rewrite DistMap.dE /DistMap.f /fmap_dist DistBind.dE.
rewrite /DistBind.f big_mkcond /=; apply eq_bigr => a _.
case: ifPn => [/eqP ->|]; rewrite Dist1.dE; [by rewrite eqxx mulR1|].
move/negbTE; rewrite eq_sym => ->; by rewrite mulR0.
Qed.

End map_bind_dist.

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

Definition d : dist A := locked (makeDist f0 f1).

Lemma dE a : d a = / INR #|A|.
Proof. by rewrite /d; unlock => /=; rewrite /f div1R. Qed.

End uniform.

Lemma d_neq0 (C : finType) (domain_non_empty : { m : nat | #| C | = m.+1 }) :
  forall x, d (projT2 domain_non_empty) x != 0.
Proof.
move=> c; rewrite dE invR_neq0 //; apply/eqP.
case: domain_non_empty => x' ->; by rewrite INR_eq0.
Qed.

End Uniform.

Lemma dom_by_uniform A (P : dist A) n (HA : #|A| = n.+1) :
  P << (Uniform.d HA).
Proof.
apply/dominatesP => a; rewrite Uniform.dE => /esym abs; exfalso.
move: abs; rewrite HA; exact/ltR_eqF/invR_gt0/ltR0n.
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
apply divR_ge0; [lra|exact/ltR0n].
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
Proof. rewrite /f. case: ifP => _; case: Hp => ? ?; lra. Qed.

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
  split; first lra.
  suff : forall a, a <= 1 -> 0 <= a -> 1 - a <= 1 by apply.
  move=> *; lra.
exists r01.
apply/dist_ext => a /=.
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
apply/ltRW/invR_gt0/subR_gt0/ltRP; rewrite ltR_neqAle' Xb1; exact/leRP/dist_max.
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

Definition d := locked (makeDist f0 f1).

Lemma dE a : d a = if a == b then 0 else X a / (1 - X b).
Proof. by rewrite /d; unlock. Qed.

Lemma card_dist_supp (Xb0 : X b != 0) : #|dist_supp d| = #|dist_supp X|.-1.
Proof.
rewrite /dist_supp (cardsD1 b [set a | X a != 0]) !inE Xb0 add1n /=.
apply eq_card => i; rewrite !inE dE.
case: ifPn => //= ib; first by rewrite eqxx.
apply/idP/idP; first by apply: contra => /eqP ->; rewrite div0R.
apply: contra; rewrite /Rdiv mulR_eq0' => /orP[//|H].
exfalso.
move/negPn/negP : H; apply.
apply/invR_neq0; by apply: contra Xb1; rewrite subR_eq0 eq_sym.
Qed.

Lemma d_eq0 a (Xa0 : X a != 0) : ((d a == 0) = (b == a))%bool.
Proof.
rewrite dE; case: ifPn => [/eqP ->|ab]; first by rewrite !eqxx.
apply/idP/idP => [|]; last by rewrite eq_sym (negbTE ab).
rewrite mulR_eq0' => /orP[]; first by rewrite (negbTE Xa0).
by move/invR_eq0; rewrite subR_eq0 eq_sym (negbTE Xb1).
Qed.

Lemma d_0 a : X a = 0 -> d a = 0.
Proof. move=> Xa0; rewrite dE Xa0 div0R; by case: ifP. Qed.

End d1dist.
End D1Dist.

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

Definition d : {dist A} := locked (makeDist f0 f1).

Lemma dE a : d a = (p * d1 a + p.~ * d2 a)%R.
Proof. by rewrite /d; unlock. Qed.

End convexdist.
Section convexdist_prop.
Variables (A : finType).

Local Notation "x <| p |> y" := (d x y p) (format "x  <| p |>  y", at level 50).

Lemma d0 (d1 d2 : dist A) (H : 0 <= 0 <= 1) : d1 <| H |> d2 = d2.
Proof.
apply/dist_ext => a /=.
by rewrite dE mulRDl !(mul0R,mulNR,oppR0,add0R,addR0,mulR1,mul1R).
Qed.

Lemma d1 (d1 d2 : dist A) (H : 0 <= 1 <= 1) : d1 <| H |> d2 = d1.
Proof.
apply/dist_ext => a /=.
by rewrite dE mulRDl !(mul0R,mulNR,oppR0,add0R,addR0,mulR1,mul1R,addRN).
Qed.

(* TODO: rename to skewed_commute *)
Lemma quasi_commute (d1 d2 : dist A) p (Hp : 0 <= p <= 1) (Hp' : 0 <= p.~ <= 1) :
  d1 <| Hp |> d2 = d2 <| Hp' |> d1.
Proof. apply/dist_ext => a /=; by rewrite 2!dE onemK addRC. Qed.

Lemma idempotent (d0 : dist A) p (p01 : 0 <= p <= 1) : d0 <|p01|> d0 = d0.
Proof.
apply/dist_ext => a; by rewrite dE mulRBl mul1R addRCA addRN addR0.
Qed.

Lemma quasi_assoc (p q r s : R) (d0 d1 d2 : dist A)
  (Hp : 0 <= p <= 1) (Hq : 0 <= q <= 1) (Hr : 0 <= r <= 1) (Hs : 0 <= s <= 1) :
  p = (r * s)%R -> (s.~ = p.~ * q.~)%R ->
  d0 <|Hp|> (d1 <|Hq|> d2) = (d0 <|Hr|> d1) <|Hs|> d2.
Proof.
move=> H1 H2; apply/dist_ext => a /=; rewrite 4!dE /=.
transitivity (p * d0 a + p.~ * q * d1 a + p.~ * q.~ * d2 a)%R; first lra.
transitivity (r * s * d0 a + r.~ * s * d1 a + s.~ * d2 a)%R; last lra.
rewrite H1; congr (_ + _ * _ + _ * _)%R.
rewrite -(onemK s) H2; nsatz.
rewrite H2 H1; lra.
Qed.

Lemma commute (x1 y1 x2 y2 : dist A) p q (Hp : 0 <= p <= 1) (Hq : 0 <= q <= 1) :
  (x1 <|Hq|> y1) <|Hp|> (x2 <|Hq|> y2) = (x1 <|Hp|> x2) <|Hq|> (y1 <|Hp|> y2).
Proof.
case/boolP : (p == 0 :> R) => [|]/eqP p0; first by subst p; rewrite !d0.
case/boolP : (q == 0 :> R) => [|]/eqP q0; first by subst q; rewrite !d0.
case/boolP : (p == 1 :> R) => [|]/eqP p1; first by subst p; rewrite !d1.
case/boolP : (q == 1 :> R) => [|]/eqP q1; first by subst q; rewrite !d1.
set r := p * q.
have pq1 : p * q != 1.
  apply/eqP => pq1; have {p1} : p < 1 by lra.
  rewrite -pq1 mulRC -ltR_pdivr_mulr; last lra.
  rewrite divRR; [lra | exact/eqP].
have r1 : r < 1.
  rewrite ltR_neqAle; split; [exact/eqP|rewrite -(mulR1 1); apply/leR_pmul; tauto].
set s := (p - r) / (1 - r).
rewrite -(@quasi_assoc r s _ _ x1); last 2 first.
  by rewrite mulRC.
  rewrite /onem {}/s; field; by apply/eqP; rewrite subR_eq0 eq_sym.
  split.
  - apply divR_ge0; last by rewrite subR_gt0.
    rewrite subR_ge0 /r -{2}(mulR1 p); apply/leR_wpmul2l; tauto.
  - rewrite /s leR_pdivr_mulr ?subR_gt0 // mul1R leR_add2r; tauto.
  split; by [apply/mulR_ge0; tauto | rewrite leR_eqVlt; right].
move=> Hs Hr.
rewrite (quasi_commute y1).
  split; [apply onem_ge0; tauto | apply onem_le1; tauto].
move=> Hs'.
set t := s.~ * q.
have t01 : 0 <= t <= 1.
  split; first by apply/mulR_ge0; [apply onem_ge0; tauto|tauto].
  rewrite /t -(mulR1 1); apply leR_pmul;
    [apply onem_ge0; tauto | tauto | apply onem_le1; tauto | tauto].
have t1 : t < 1.
  rewrite ltR_neqAle; split; last tauto.
  move=> t1; subst t.
  have {q1} : q < 1 by lra.
    rewrite -t1 -ltR_pdivr_mulr; last by lra.
    rewrite divRR; [lra | exact/eqP].
rewrite -(@quasi_assoc t p.~ _ _ x2) => //; last 2 first.
  by rewrite mulRC.
  rewrite 2!onemK /t /onem /s /r; field.
  by apply/eqP; rewrite subR_eq0 eq_sym.
  split; [apply onem_ge0; tauto | apply onem_le1; tauto].
move=> Hp'.
rewrite (@quasi_assoc _ _ p.~.~ q x1); last 2 first.
  by rewrite onemK.
  rewrite /t /onem /s /r; field; by apply/eqP; rewrite subR_eq0 eq_sym.
  by rewrite onemK.
move=> Hp''.
rewrite (quasi_commute y2 y1).
move: Hp''; rewrite onemK => Hp''.
by rewrite (ProofIrrelevance.proof_irrelevance _ Hp'' Hp).
Qed.

Lemma bind_left_distr (B : finType) (p : R) (Hp : 0 <= p <= 1)
  (d0 d1 : dist A) (f : A -> dist B) :
  DistBind.d (d0 <| Hp |> d1) f = DistBind.d d0 f <| Hp |> DistBind.d d1 f.
Proof.
apply/dist_ext => a /=.
rewrite /DistBind.d /DistBind.f dE /=.
rewrite 2!big_distrr /= -big_split /=; apply/eq_bigr => a0 _.
by rewrite dE mulRDl !mulRA.
Qed.

End convexdist_prop.
End ConvexDist.

Module FamilyDist.
Section familydist.
Variables (A : finType) (n : nat) (g : 'I_n -> dist A) (e : {dist 'I_n}).

Definition f a := \rsum_(i < n) e i * g i a.

Lemma f0 a : 0 <= f a.
Proof. apply: rsumr_ge0 => /= i _; apply mulR_ge0; exact: dist_ge0. Qed.

Lemma f1 : \rsum_(a in A) f a = 1.
Proof.
rewrite /f exchange_big /= -(pmf1 e) /=; apply eq_bigr => i _.
by rewrite -big_distrr /= pmf1 mulR1.
Qed.

Definition d : {dist A} := locked (makeDist f0 f1).

Lemma dE a : d a = \rsum_(i < n) e i * g i a.
Proof. by rewrite /d; unlock. Qed.

End familydist.
End FamilyDist.

(* bivariate (joint) distribution *)
Module Bivar.
Section bivar.
Variables (A B : finType) (P : {dist A * B}).

(* marginal left *)
Definition ml a := \rsum_(x in {: A * B} | x.1 == a) P x.

Lemma ml0 a : 0 <= ml a. Proof. apply rsumr_ge0 => x xa; exact: dist_ge0. Qed.

Lemma ml1 : \rsum_(a in A) ml a = 1%R.
Proof.
rewrite -(pmf1 P) (eq_bigr (fun a => P (a.1, a.2))); last by case.
rewrite -(pair_big xpredT xpredT (fun a b => P (a, b))) /=; apply eq_bigr => a _.
rewrite /ml -(pair_big_fst _ _ (pred1 a)) //= exchange_big /=.
apply eq_bigr => b _; by rewrite big_pred1_eq.
Qed.

Definition fst := locked (makeDist ml0 ml1).

Lemma fstE a : fst a = \rsum_(i in B) P (a, i).
Proof.
rewrite /fst; unlock => /=; rewrite /ml.
by rewrite -(pair_big_fst _ _ (pred1 a)) //= big_pred1_eq.
Qed.

Lemma dom_by_fst a b : fst a = 0 -> P (a, b) = 0.
Proof. rewrite fstE => /prsumr_eq0P -> // ? _; exact: dist_ge0. Qed.

Lemma dom_by_fstN a b : P (a, b) != 0 -> fst a != 0.
Proof. by apply: contra => /eqP /dom_by_fst ->. Qed.

(* marginal right *)
Definition mr b := \rsum_(x in {: A * B} | x.2 == b) P x.

Lemma mr0 b : 0 <= mr b. Proof. apply rsumr_ge0 => x xb; exact: dist_ge0. Qed.

Lemma mr1 : \rsum_(b in B) mr b = 1%R.
Proof.
rewrite -(pmf1 P) (eq_bigr (fun a => P (a.1, a.2))); last by case.
rewrite -(pair_big xpredT xpredT (fun a b => P (a, b))) /=.
rewrite exchange_big; apply eq_bigr => b _.
rewrite /mr -(pair_big_snd _ _ (pred1 b)) //=.
apply eq_bigr => a _; by rewrite big_pred1_eq.
Qed.

Definition snd : dist B := locked (makeDist mr0 mr1).

Lemma sndE b : snd b = \rsum_(i in A) P (i, b).
Proof.
rewrite /snd; unlock => /=; rewrite /mr -(pair_big_snd _ _ (pred1 b)) //=.
apply eq_bigr => a ?; by rewrite big_pred1_eq.
Qed.

Lemma dom_by_snd a b : snd b = 0 -> P (a, b) = 0.
Proof. rewrite sndE => /prsumr_eq0P -> // ? _; exact: dist_ge0. Qed.

Lemma dom_by_sndN a b : P (a, b) != 0 -> snd b != 0.
Proof. by apply: contra => /eqP /dom_by_snd ->. Qed.

End bivar.
End Bivar.

(* multivariate (joint) distribution *)
Module Multivar.
Section prod_of_rV.
Variables (A : finType) (n : nat) (P : {dist 'rV[A]_n.+1}).

Definition tobi (a : A * 'rV[A]_n) := P (row_mx (\row_(i < 1) a.1) a.2).

Lemma tobi0 a : 0 <= tobi a.
Proof. exact: dist_ge0. Qed.

Lemma tobi1 : \rsum_(a in {: A * 'rV[A]_n}) tobi a = 1%R.
Proof.
rewrite -(pmf1 P) /= -(big_rV_cons_behead _ xpredT xpredT) /=.
by rewrite pair_big /=; apply eq_bigr; case.
Qed.

Definition to_bivar : {dist A * 'rV[A]_n} := locked (makeDist tobi0 tobi1).

Lemma to_bivarE a : to_bivar a = P (row_mx (\row_(i < 1) a.1) a.2).
Proof. rewrite /to_bivar; unlock => /=; by []. Qed.

Definition head_of := Bivar.fst to_bivar.
Definition tail_of := Bivar.snd to_bivar.

Definition tolast (a : 'rV[A]_n * A) :=
  P (castmx (erefl, addn1 n) (row_mx a.1 (\row_(i < 1) a.2))).
Lemma tolast0 a : 0 <= tolast a. Proof. exact: dist_ge0. Qed.
Lemma tolast1 : \rsum_(a in {: 'rV[A]_n * A}) tolast a = 1%R.
Proof.
rewrite -(pmf1 P) /= -(big_rV_belast_last _ xpredT xpredT) /=.
by rewrite pair_big /=; apply eq_bigr; case.
Qed.
Definition to_bivar_last : {dist 'rV[A]_n * A} := locked (makeDist tolast0 tolast1).
Lemma to_bivar_lastE a : to_bivar_last a =
  P (castmx (erefl, addn1 n) (row_mx a.1 (\row_(i < 1) a.2))).
Proof. rewrite /to_bivar_last; unlock => /=; by []. Qed.

End prod_of_rV.

Section rV_of_prod.

Local Open Scope vec_ext_scope.

Variables (A : finType) (n : nat) (P : {dist A * 'rV[A]_n}).

Definition frombi (a : 'rV[A]_n.+1) := P (a ``_ ord0, rbehead a).

Lemma frombi0 a : 0 <= frombi a.
Proof. exact: dist_ge0. Qed.

Lemma frombi1 : \rsum_(a in {: 'rV[A]_n.+1}) frombi a = 1%R.
Proof.
rewrite -(pmf1 P) /= -(big_rV_cons_behead _ xpredT xpredT) /=.
rewrite pair_big /=; apply eq_bigr; case => a b _ /=.
by rewrite /frombi row_mx_row_ord0 rbehead_row_mx.
Qed.

Definition from_bivar : {dist 'rV[A]_n.+1} := locked (makeDist frombi0 frombi1).

Lemma from_bivarE a : from_bivar a = P (a ``_ ord0, rbehead a).
Proof. rewrite /from_bivar; unlock => /=; by []. Qed.

End rV_of_prod.

Lemma from_bivarK (A : finType) n (P : {dist A * 'rV[A]_n}) :
  to_bivar (from_bivar P) = P.
Proof.
apply/dist_ext => /= -[a b].
by rewrite to_bivarE /= from_bivarE /= row_mx_row_ord0 rbehead_row_mx.
Qed.

End Multivar.

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

Definition d : {dist A * B} := locked (makeDist f0 f1).

Lemma dE x : d x = (P1 x.1 * P2 x.2)%R. Proof. by rewrite /d; unlock. Qed.

End ProdDist_sect.
End ProdDist.

Notation "P1 `x P2" := (ProdDist.d P1 P2) : proba_scope.

Module TupleDist.
Section tupledist.
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
rewrite [RHS](_ : _ = \rprod_(i < n) 1)%R; last by rewrite big1.
apply eq_bigr => i _; exact: pmf1.
Qed.

Definition d : {dist 'rV[A]_n} := locked (makeDist f0 f1).

Lemma dE t : d t = \rprod_(i < n) P t ``_ i.
Proof. rewrite /d; by unlock. Qed.

End tupledist.

Local Notation "P `^ n" := (d P n).

Section tupledist_prop.
Variable B : finType.

Local Open Scope vec_ext_scope.

Lemma zero (x : 'rV[B]_0) P : P `^ 0 x = 1%R.
Proof. by rewrite dE big_ord0. Qed.

Lemma S n (x : 'rV[B]_n.+1) P : P `^ n.+1 x = P (x ``_ ord0) * P `^ n (rbehead x).
Proof.
rewrite 2!TupleDist.dE big_ord_recl; congr (_ * _)%R.
apply eq_bigr => i _; by rewrite /rbehead mxE.
Qed.

Lemma one (a : 'rV[B]_1) P : (P `^ 1) a = P (a ``_ ord0).
Proof. by rewrite S zero mulR1. Qed.

End tupledist_prop.

(* The tuple distribution as a joint distribution *)
Section joint_tuple_dist.

Variables (A : finType) (P : dist A) (n : nat).

Lemma head_of : P = Multivar.head_of (P `^ n.+1).
Proof.
apply/dist_ext => a; rewrite /Multivar.head_of Bivar.fstE /=.
evar (f : 'rV[A]_n -> R); rewrite (eq_bigr f); last first.
  move=> v _; rewrite Multivar.to_bivarE /= TupleDist.S.
  rewrite row_mx_row_ord0 rbehead_row_mx /f; reflexivity.
by rewrite {}/f -big_distrr /= pmf1 mulR1.
Qed.

Lemma tail_of : P `^ n = Multivar.tail_of (P `^ n.+1).
Proof.
apply/dist_ext => a; rewrite /Multivar.tail_of Bivar.sndE /=.
evar (f : A -> R); rewrite (eq_bigr f); last first.
  move=> v _; rewrite Multivar.to_bivarE /= TupleDist.S.
  rewrite row_mx_row_ord0 rbehead_row_mx /f; reflexivity.
by rewrite {}/f -big_distrl /= pmf1 mul1R.
Qed.

End joint_tuple_dist.
End TupleDist.

Notation "P `^ n" := (TupleDist.d P n) : proba_scope.

Local Open Scope ring_scope.
Local Open Scope vec_ext_scope.

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
by rewrite iter_mulR pmf1 exp1R.
Qed.

Local Close Scope vec_ext_scope.

(*Section tuple_prod_cast.

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

End tuple_prod_cast.*)

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
    apply leR_wpmul2r; first lra.
    apply Req_le.
    rewrite filter_index_enum count_predT cardE; congr (INR (size _)).
    apply eq_enum => i; by rewrite /in_mem /= andbC.
  apply/(leR_trans _ HB)/Req_le/eq_bigl => i; by rewrite andbC.
have HA : INR #|s| * A <= \rsum_(x in s) P `^ _ x.
  have HA : INR #|s| * A <= \rsum_(x in s | predT s) P `^ _ x.
    apply (@leR_trans (\rsum_(x in s | predT s) [fun _ => A] x)); last first.
      apply ler_rsum_support => i Hi _; by case: (H i Hi).
    rewrite -big_filter /= big_const_seq /= iter_addR /=.
    apply leR_wpmul2r; first lra.
    apply Req_le.
    rewrite filter_index_enum count_predT cardE; congr (INR (size _)).
    apply eq_enum => i; by rewrite /in_mem /= andbC.
  apply/(leR_trans HA)/Req_le/eq_bigl => i; by rewrite andbC.
split.
- rewrite leR_pdivr_mulr //; move/leR_trans : Ha; exact.
- rewrite leR_pdivl_mulr //; exact: (leR_trans HA).
Qed.

End wolfowitz_counting.

Section probability.
Variables (A : finType) (P : dist A).

Definition Pr (E : {set A}) := \rsum_(a in E) P a.

Lemma Pr_ge0 E : 0 <= Pr E.
Proof. apply rsumr_ge0 => *; exact: dist_ge0. Qed.

Lemma Pr_gt0 E : 0 < Pr E <-> Pr E != R0.
Proof.
split => H; first by move/gtR_eqF : H => /eqP.
rewrite ltR_neqAle; split; [exact/nesym/eqP|exact/Pr_ge0].
Qed.

Lemma Pr_1 E : Pr E <= 1.
Proof.
rewrite -(pmf1 P); apply ler_rsum_l => // a _; [exact/leRR | exact/dist_ge0].
Qed.

(*Lemma Pr_ext E F : E :=: F -> Pr E = Pr F.
Proof. by move=> ->. Qed.*)

Local Open Scope R_scope.

Lemma Pr_set0 : Pr set0 = 0.
Proof. rewrite /Pr big_pred0 // => a; by rewrite in_set0. Qed.

Lemma Pr_set0P S : Pr S = 0 <-> (forall s, s \in S -> P s = 0).
Proof.
rewrite /Pr (eq_bigl (fun x => x \in S)); last by [].
apply: (@prsumr_eq0P _ (mem S) P) => a Sa; exact: dist_ge0.
Qed.

Lemma Pr_setT : Pr setT = 1.
Proof. rewrite /Pr (eq_bigl xpredT) ?pmf1 // => a; by rewrite in_setT. Qed.

Lemma Pr_set1 a : Pr [set a] = P a.
Proof. by rewrite /Pr big_set1. Qed.

Lemma Pr_cplt E : Pr E + Pr (~: E) = 1.
Proof.
rewrite /Pr -bigU /=; last by rewrite -subsets_disjoint.
rewrite -(pmf1 P); apply eq_bigl => /= a; by rewrite !inE /= orbN.
Qed.

Lemma Pr_to_cplt E : Pr E = 1 - Pr (~: E).
Proof. rewrite -(Pr_cplt E); field. Qed.

Lemma Pr_of_cplt E : Pr (~: E) = 1 - Pr E.
Proof. rewrite -(Pr_cplt E); field. Qed.

Lemma Pr_incl (E E' : {set A}) : E \subset E' -> Pr E <= Pr E'.
Proof.
move=> H; apply ler_rsum_l => a Ha;
  [exact/leRR | exact/dist_ge0 | move/subsetP : H; exact].
Qed.

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

Lemma Pr_bigcup (B : finType) (E : pred B) F :
  Pr (\bigcup_(i | E i) F i) <= \rsum_(i | E i) Pr (F i).
Proof.
rewrite /Pr.
elim: (index_enum _) => [| h t IH].
  rewrite big_nil; apply: rsumr_ge0 => b _; rewrite big_nil; exact/leRR.
rewrite big_cons.
case: ifP => H1.
  apply: leR_trans; first by eapply leR_add2l; exact: IH.
  rewrite [X in _ <= X](exchange_big_dep
    (fun h => (h \in A) && [pred x in \bigcup_(i | E i) F i] h)) /=; last first.
    move=> b a Ea jFi; apply/bigcupP; by exists b.
  rewrite big_cons /= H1 big_const iter_addR -exchange_big_dep /=; last first.
    move=> b a Ea iFj; apply/bigcupP; by exists b.
  apply/leR_add2r.
  rewrite -{1}(mul1R (P h)); apply: (@leR_wpmul2r (P h)); [exact: dist_ge0|].
  rewrite (_ : 1 = INR 1) //; apply/le_INR/leP/card_gt0P.
  case/bigcupP : H1 => b Eb hFb; exists b; by rewrite -topredE /= Eb.
apply/(leR_trans IH)/ler_rsum => b Eb.
rewrite big_cons.
case: ifPn => hFb; last exact/leRR.
rewrite -[X in X <= _]add0R; exact/leR_add2r/dist_ge0.
Qed.

Lemma Pr_union_disj (E1 E2 : {set A}) :
  [disjoint E1 & E2] -> Pr (E1 :|: E2) = Pr E1 + Pr E2.
Proof. move=> ?; rewrite -bigU //=; apply eq_bigl => a; by rewrite inE. Qed.

Lemma Pr_big_union_disj n (E : 'I_n -> {set A}):
  (forall i j, i != j -> [disjoint E i & E j]) ->
  Pr (\bigcup_(i < n) E i) = \rsum_(i < n) Pr (E i).
Proof.
elim: n E => [E H|n IH E H]; first by rewrite !big_ord0 Pr_set0.
rewrite big_ord_recl /= Pr_union_disj; last first.
  rewrite -setI_eq0 big_distrr /=; apply/eqP/big1 => i _; apply/eqP.
  rewrite setI_eq0; exact: H.
rewrite big_ord_recl IH // => i j ij; by rewrite H.
Qed.

Lemma Pr_union_eq (E1 E2 : {set A}) :
  Pr (E1 :|: E2) = Pr E1 + Pr E2 - Pr (E1 :&: E2).
Proof.
rewrite -[E1 :|: E2](setID _ E1) Pr_union_disj; last first.
  rewrite -setI_eq0 setDE -setIA [E1 :&: _]setIC -setIA [~: E1 :&: _]setIC.
  by rewrite setICr !setI0.
rewrite setUK setDUKl -{1}[E2 in RHS](setID _ E1) Pr_union_disj; last first.
  rewrite -setI_eq0 setDE -setIA [E1 :&: _]setIC -setIA [~: E1 :&: _]setIC.
  by rewrite setICr !setI0.
rewrite setIC; ring.
Qed.

Lemma Pr_inter_eq (E1 E2 : {set A}) :
  Pr (E1 :&: E2) = (Pr E1 + Pr E2 - Pr (E1 :|: E2))%R.
Proof. by rewrite Pr_union_eq subRBA addRC addRK. Qed.

End probability.

Lemma Pr_fst_eq0 (A B : finType) (P : {dist (A * B)}) a b :
  Pr (Bivar.fst P) a = 0%R -> Pr P (setX a b) = 0%R.
Proof.
move/Pr_set0P => H; apply/Pr_set0P => -[? ?].
by rewrite inE /= => /andP[/H /Bivar.dom_by_fst ->].
Qed.

Lemma Pr_snd_eq0 (A B : finType) (P : {dist (A * B)}) a b :
  Pr (Bivar.snd P) b = 0%R -> Pr P (setX a b) = 0%R.
Proof.
move/Pr_set0P => H; apply/Pr_set0P => -[? ?].
by rewrite inE /= => /andP[_ /H /Bivar.dom_by_snd ->].
Qed.

Lemma Pr_setX1 (A B : finType) (PQ : {dist (A * B)}) a b :
  Pr PQ (setX [set a] [set b]) = Pr PQ [set (a, b)].
Proof.
rewrite (_ : setX [set a] _ = [set (a, b)]) //.
apply/setP => -[x1 x2]; by rewrite !inE /= xpair_eqE.
Qed.

(*Section Pr_tuple_prod.

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

End Pr_tuple_prod.*)

Local Open Scope R_scope.

Section random_variable.

Record rvar (A : finType) (T : eqType) := mkRvar {rv_dist : dist A ; rv_fun :> A -> T}.

Definition rvar_of (A : finType) (T : eqType) :=
  fun (phA : phant (Finite.sort A)) (phT : phant (Equality.sort T)) => rvar A T.

Local Notation "`p_ X" := (rv_dist X).

Section pr_def.

Variables (A : finType) (T : eqType).

Definition pr (X : rvar A T) r := Pr `p_X [set x | X x == r].

End pr_def.

Definition scale_rv A k (X : rvar A R_eqType) :=
  mkRvar `p_X (fun x => k * X x).
Definition add_rv A (X Y : rvar A R_eqType) (H : `p_X = `p_Y) :=
  mkRvar `p_X (fun x => X x + Y x).
Definition sub_rv A (X Y : rvar A R_eqType) (H : `p_X = `p_Y) :=
  mkRvar `p_X (fun x => X x - Y x).
Definition trans_add_rv A (X : rvar A R_eqType) m :=
  mkRvar `p_X (fun x => X x + m).
Definition trans_min_rv A (X : rvar A R_eqType) m :=
  mkRvar `p_X (fun x => X x - m).
Definition const_rv A T cst (X : rvar A T) :=
  @mkRvar _ T `p_X (fun _ => cst).
Definition comp_rv A T (B : eqType) (X : rvar A T) (f : T -> B) :=
  mkRvar `p_X (fun x => f (X x)).
Definition sq_rv A (X : rvar A R_eqType) := comp_rv X (fun x => x ^ 2).

End random_variable.

Notation "{ 'rvar' A , T }" := (rvar_of (Phant A) (Phant T)) : proba_scope.

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
Definition mlog_rv A (P : dist A) : rvar A R_eqType := mkRvar P (fun x => - log (P x))%R.

Notation "'--log' P" := (mlog_rv P) (at level 5) : proba_scope.

(** Cast operation: *)

Local Open Scope vec_ext_scope.

Definition rvar_rV1_of_rvar A T (X : rvar A T) : {rvar 'rV[A]_1, T} :=
  mkRvar (`p_X `^ 1) (fun x => X (x ``_ ord0)).

Definition cast_rV1 A T (v : 'rV[rvar A T]_1) : {rvar 'rV[A]_1, T} :=
  rvar_rV1_of_rvar (v ``_ ord0).

Local Close Scope vec_ext_scope.

Section expected_value_definition.

Variables (A : finType) (X : {rvar A, R}).

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

Lemma Ex_ge0 : (forall a, 0 <= X a) -> 0 <= Ex.
Proof.
move=> H; rewrite ExE; apply: rsumr_ge0 => i _.
apply mulR_ge0; by [apply H | apply dist_ge0].
Qed.

End expected_value_definition.

Notation "'`E'" := (Ex) : proba_scope.

Section expected_value_for_standard_random_variables.

Variables (A : finType) (X Y : {rvar A, R}).

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

Lemma E_rvar_rV1_of_rvar A : forall (X : rvar A R_eqType), `E (rvar_rV1_of_rvar X) = `E X.
Proof.
case=> d f.
rewrite 2!ExE /rvar_rV1_of_rvar /=; apply big_rV_1 => // m.
by rewrite -TupleDist.one.
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
- move=> ? ? ? ?; rewrite mulR_eq0 => -[]; by tauto.
- move=> i Hi Hi0; by exists i.
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
apply (big_ind2 (R1 := {set A}) (R2 := R)); last by [].
- by rewrite /Ind inE.
- by move=> sa a sb b Ha Hb; rewrite -Ha -Hb; apply: Ind_cap.
Qed.

(** *** Extra support results for the expected value *)

(** Remark:

    Random variables [X : rvar A] are defined as a record
    gathering a distribution [P : dist A] and a function [f : A -> R].

    For convenience, we locally define the function [rv] for building
    such random variables, endowed with the ambient distribution [P]. *)

Let rv : (A -> R) -> {rvar A, R} := mkRvar P.

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

Variables (A : finType) (X : {rvar A, R}).
Hypothesis X_ge0 : forall a, 0 <= X a.

Definition pr_geq (X : {rvar A, R}) r := Pr `p_X [set x | X x >b= r].

Local Notation "'Pr[' X '>=' r ']'" := (pr_geq X r).

Lemma Ex_lb (r : R) : r * Pr[ X >= r] <= `E X.
Proof.
rewrite ExE.
rewrite (bigID [pred a' | X a' >b= r]) /=.
rewrite -[a in a <= _]addR0.
apply leR_add; last first.
  apply rsumr_ge0 => a _.
  apply mulR_ge0; [exact/X_ge0 | apply dist_ge0].
apply (@leR_trans (\rsum_(i | X i >b= r) r * `p_ X i)).
  rewrite big_distrr /=;  apply/Req_le/eq_bigl => a; by rewrite inE.
apply ler_rsum => a Xar.
apply/leR_wpmul2r; [exact/dist_ge0 | exact/leRP].
Qed.

Lemma markov (r : R) : 0 < r -> Pr[X >= r] <= `E X / r.
Proof. move=> ?; rewrite /Rdiv leR_pdivl_mulr // mulRC; exact/Ex_lb. Qed.

End markov_inequality.

Notation "'Pr[' X '>=' r ']'" := (pr_geq X r) : proba_scope.

(** * Variance *)

Section variance_definition.

Variables (A : finType) (X : {rvar A, R}).

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

Variables (A : finType) (X : {rvar A, R}).

(** The variance is not linear V (k X) = k^2 V (X) \cite[Theorem 6.7]{probook}: *)
Lemma V_scale k : `V (k \cst* X) = k ^ 2 * `V X.
Proof.
rewrite {1}/`V [in X in X = _]/= E_scale.
rewrite (@E_comp_rv_ext _ ((k \cst* X) \-cst k * `E X) (k \cst* (X \+cst - `E X))) //; last first.
  apply functional_extensionality => /= x; field.
rewrite E_comp ?E_scale // => x y; field.
Qed.

End variance_properties.

Lemma V_rvar_rV1_of_rvar (A : finType) (X : {rvar A, R}) : `V (rvar_rV1_of_rvar X) = `V X.
Proof.
case: X => d f.
rewrite /`V !E_rvar_rV1_of_rvar !ExE; apply: big_rV_1 => // i.
by rewrite TupleDist.one.
Qed.

(** (Probabilistic statement.)
 In any data sample, "nearly all" the values are "close to" the mean value:
 Pr[ |X - E X| \geq \epsilon] \leq V(X) / \epsilon^2 *)
Section chebyshev.

Variables (A : finType) (X : {rvar A, R}).

Lemma chebyshev_inequality epsilon : 0 < epsilon ->
  Pr `p_X [set a | `| X a - `E X | >b= epsilon] <= `V X / epsilon ^ 2.
Proof.
move=> He; rewrite leR_pdivl_mulr; last exact/expR_gt0.
rewrite mulRC /`V [in X in _ <= X]ExE.
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

Section identically_distributed.

Variables (A : finType) (T : eqType) (P : dist A) (n : nat).

Local Open Scope vec_ext_scope.

(** The random variables Xs are identically distributed with distribution P: *)
Definition id_dist (Xs : 'rV[rvar A T]_n) := forall i, `p_(Xs ``_ i) = P.

End identically_distributed.

Section independent_events.

Variables (A : finType) (d : dist A) (E F : {set A}).

Definition inde_events := Pr d (E :&: F) = Pr d E * Pr d F.

End independent_events.

Section independent_discrete_random_variables.

Variables (A B : finType) (TA TB : eqType) (f : A -> TA) (g : B -> TB).
Variable P : {dist A * B}.
Let X := mkRvar (Bivar.fst P) f.
Let Y := mkRvar (Bivar.snd P) g.

Local Open Scope vec_ext_scope.

Definition inde_drv := forall (x : TA) (y : TB),
  Pr P [set xy | (X xy.1 == x) && (Y xy.2 == y)] = Pr[X = x] * Pr[Y = y].

Lemma inde_events_drv : inde_drv <-> (forall x y,
  inde_events P [set xy | X xy.1 == x] [set xy | Y xy.2 == y]).
Proof.
have H1 : forall x, Pr[X = x] = Pr P [set xy | f xy.1 == x].
  move=> /= x; rewrite /pr /Pr /= (eq_bigr (fun a => P (a.1, a.2))); last by case.
  rewrite (eq_bigl (fun ab => (ab.1 \in [set z | f z == x]) && (xpredT ab.2))); last first.
    move=> -[a b]; by rewrite !inE andbT.
  rewrite -[in RHS](pair_big (fun z => z \in [set z | f z == x]) xpredT (fun a b => P (a, b))) /=.
  apply eq_bigr => a _; by rewrite Bivar.fstE.
have H2 : forall y, Pr[Y = y] = Pr P [set xy | g xy.2 == y].
  move=> /= y; rewrite /pr /Pr /= (eq_bigr (fun a => P (a.1, a.2))); last by case.
  rewrite (eq_bigl (fun ab => (xpredT ab.1) && (ab.2 \in [set z | g z == y]))); last first.
    by move=> -[a b]; rewrite !inE.
  rewrite -[in RHS](pair_big xpredT (fun z => z \in [set z | g z == y]) (fun a b => P (a, b))) /=.
  rewrite exchange_big; apply eq_bigr => b _; by rewrite Bivar.sndE.
split=> [H /= x y|/= H x y].
  rewrite /inde_events.
  move: (H x y) => {H}H.
  rewrite -H1 -H2 -{}H; congr Pr; by apply/setP => /= ab; rewrite !inE.
rewrite /inde_events in H.
rewrite H1 H2 -{}H; congr Pr; by apply/setP => /= ab; rewrite !inE.
Qed.

Lemma prod_dist_inde_drv : P = (Bivar.fst P) `x (Bivar.snd P) -> inde_drv.
Proof.
move=> H x y.
rewrite /Pr /= (eq_bigr (fun a => P (a.1, a.2))); last by case.
rewrite (eq_bigl (fun a => (f a.1 == x) && (g a.2 == y))); last first.
  by case => a b; rewrite !inE.
rewrite -(pair_big [pred a | f a == x] [pred b | g b == y]
  (fun a1 a2 => P (a1, a2))) /=.
rewrite {1}/pr /Pr big_distrl /=; apply eq_big.
- move=> a; by rewrite inE.
- move=> a fax.
  rewrite /pr /Pr big_distrr /=; apply eq_big.
  + move=> b; by rewrite inE.
  + by move=> b gby; rewrite {1}H /= ProdDist.dE.
Qed.

End independent_discrete_random_variables.

Notation "P |= X _|_ Y" := (inde_drv X Y P) : proba_scope.

Local Open Scope vec_ext_scope.

(** Independent random variables over the tuple distribution: *)
Lemma inde_drv_tuple_dist A (P : dist A) n (x y : R) (f : A -> R) :
  Pr P `^ n.+1 [set xy : 'rV__ |
    (f (xy ``_ ord0) == x) && (\rsum_(i < n) f ((rbehead xy) ``_ i) == y)] =
  Pr P [set a | f a == x] *
  Pr P `^ n [set b : 'rV__ | \rsum_(i < n) f (b ``_ i) == y].
Proof.
rewrite /Pr.
move: (big_rV_cons_behead_support addR_comoid
  (fun i : 'rV__ => P `^ _ i)
  [set a | f a == x]
  [set t : 'rV__ | \rsum_(i < n) f ( t ``_ i) == y]) => H.
eapply trans_eq.
  eapply trans_eq; last by symmetry; apply H.
  apply eq_bigl => ta /=; by rewrite !inE.
transitivity (\rsum_(a in [set a | f a == x])
  \rsum_(a' in [set ta : 'rV__ | \rsum_(i < n) f (ta ``_ i) == y])
  P a * P `^ _ a').
  apply eq_bigr => a _.
  apply eq_bigr => ta _.
  by rewrite TupleDist.S row_mx_row_ord0 rbehead_row_mx.
rewrite big_distrl /=.
apply eq_bigr => a _; by rewrite -big_distrr.
Qed.

Local Close Scope vec_ext_scope.

Section sum_two_rand_var_def.

Variables (A : finType) (X1 : {rvar A, R}).
Variables (n : nat) (X2 : {rvar 'rV[A]_n.+1, R}).
Variable X : {rvar 'rV[A]_n.+2, R}.

Local Open Scope vec_ext_scope.

Definition sum :=
  (`p_X1 = Multivar.head_of `p_X /\ `p_X2 = Multivar.tail_of `p_X) /\
  X =1 fun x => X1 (x ``_ ord0) + X2 (rbehead x).

End sum_two_rand_var_def.

Notation "Z \= X '@+' Y" := (sum X Y Z) : proba_scope.

Section sum_two_rand_var.

Variables (A : finType) (X1 : {rvar A, R}).
Variables (n : nat) (X2 : {rvar 'rV[A]_n.+1, R}).
Variable X : {rvar 'rV[A]_n.+2, R}.

Local Open Scope vec_ext_scope.

(** The expected value of a sum is the sum of expected values,
   whether or not the summands are mutually independent
   (the ``First Fundamental Mystery of Probability'' \cite[Theorem 6.2]{probook}): *)
Lemma E_linear_2 : X \= X1 @+ X2 -> `E X = `E X1 + `E X2.
Proof.
move=> [[Hjoint1 Hjoint2] Hsum]; rewrite !ExE /=.
transitivity (\rsum_(ta in 'rV[A]_n.+2)
  (X1 (ta ``_ ord0) * `p_X ta + X2 (rbehead ta) * `p_X ta)).
- apply eq_bigr => ta _; by rewrite Hsum mulRDl.
- rewrite big_split => //=; f_equal.
  + transitivity (\rsum_(a in A)
      (X1 a * \rsum_(ta in 'rV_n.+1) ((Multivar.to_bivar `p_X) (a, ta)))).
    * rewrite -(big_rV_cons_behead _ xpredT xpredT); apply eq_bigr => a _.
      rewrite big_distrr /=; apply eq_bigr => i _.
      by rewrite row_mx_row_ord0 Multivar.to_bivarE.
    * apply eq_bigr => a _; by rewrite Hjoint1 /Multivar.head_of Bivar.fstE.
  + transitivity (\rsum_(ta in 'rV_n.+1)
      (X2 ta * \rsum_(a in A) ((Multivar.to_bivar `p_X) (a, ta)))).
    * rewrite -(big_rV_cons_behead _ xpredT xpredT) exchange_big /=.
      apply eq_bigr => ta _; rewrite big_distrr /=.
      apply eq_bigr => a _; by rewrite rbehead_row_mx Multivar.to_bivarE.
    * apply eq_bigr => ta _; by rewrite Hjoint2 /Multivar.tail_of Bivar.sndE.
Qed.

(* TODO: relation with theorem 6.4 of probook (E(XY)=E(X)E(Y))? *)

Lemma E_id_rem_helper : X \= X1 @+ X2 -> (Multivar.to_bivar `p_X) |= X1 _|_ X2 ->
  \rsum_(i in 'rV[A]_n.+2) (X1 (i ``_ ord0) * X2 (rbehead i) * `p_X i) =
    `E X1 * `E X2.
Proof.
case=> Hjoint Hsum Hinde.
apply trans_eq with (\rsum_(r <- undup (map X1 (enum A)))
   \rsum_(r' <- undup (map X2 (enum ('rV[A]_n.+1))))
   ( r * r' * Pr[ X1 = r] * Pr[ X2 = r' ]))%R; last first.
  rewrite [in RHS]big_distrl /=.
  apply eq_bigr => i _.
  rewrite big_distrr /=.
  apply eq_bigr => j _.
  by rewrite -!mulRA [in RHS](mulRCA _ j).
rewrite -(big_rV_cons_behead _ xpredT xpredT).
apply trans_eq with (\rsum_(a in A) \rsum_(j in 'rV[A]_n.+1)
  (X1 a * X2 j * `p_X (row_mx (\row_(k < 1) a) j)))%R.
  apply eq_bigr => a _.
  apply eq_bigr => ta _.
  by rewrite row_mx_row_ord0 rbehead_row_mx.
rewrite (sum_parti _ X1); last by rewrite /index_enum -enumT; apply enum_uniq.
rewrite /index_enum -enumT.
apply eq_bigr => /= r _.
rewrite {1}enumT exchange_big /= (sum_parti _ X2); last first.
  rewrite /index_enum -enumT; by apply enum_uniq.
rewrite /index_enum -enumT.
apply eq_bigr => /= r' _.
apply trans_eq with (r * r' * \rsum_(i0 | X2 i0 == r') \rsum_(i1 | X1 i1 == r)
    (`p_X (row_mx (\row_(k < 1) i1) i0))).
  rewrite big_distrr /= /index_enum -!enumT.
  apply eq_bigr => ta ta_r'.
  rewrite big_distrr /=.
  apply eq_bigr => a a_l.
  move/eqP : ta_r' => <-.
  by move/eqP : a_l => <-.
rewrite -[RHS]mulRA; congr (_ * _)%R.
rewrite exchange_big /=.
move: {Hinde}(Hinde r r') => /=.
rewrite -/(Multivar.head_of _) -/(Multivar.tail_of _).
rewrite -(proj1 Hjoint) -(proj2 Hjoint) => <-.
rewrite /Pr pair_big /=.
apply eq_big.
- by move=> -[a b] /=; rewrite inE.
- move=> -[a b] /= /andP[ar br']; by rewrite Multivar.to_bivarE.
Qed.

(** Expected Value of the Square (requires mutual independence): *)
Lemma E_id_rem : X \= X1 @+ X2 -> (Multivar.to_bivar `p_X) |= X1 _|_ X2 ->
  `E (X \^2) = `E (X1 \^2) + 2 * `E X1 * `E X2 + `E (X2 \^2).
Proof.
move=> [[Hjoint1 Hjoint2] Hsum] Hinde.
rewrite [in LHS]ExE.
transitivity (\rsum_(i in 'rV_n.+2)
  ((X1 (i ``_ ord0) + X2 (rbehead i)) ^ 2%N * `p_X i)).
  apply eq_bigr => i _; by rewrite /sq_rv /= Hsum.
transitivity (\rsum_(i in 'rV_n.+2) ((X1 (i ``_ ord0)) ^ 2 +
    2 * X1 (i ``_ ord0) * X2 (rbehead i) + (X2 (rbehead i)) ^ 2) * `p_X i).
  apply eq_bigr => ? _; by rewrite sqrRD.
transitivity (\rsum_(i in 'rV_n.+2) ((X1 (i ``_ ord0)) ^ 2 * `p_X i + 2 *
  X1 (i ``_ ord0) * X2 (rbehead i) * `p_X i + (X2 (rbehead i)) ^ 2 * `p_X i)).
  apply eq_bigr => ? ?; by field.
rewrite !big_split /=; congr (_ + _ + _).
- rewrite ExE -(big_rV_cons_behead _ xpredT xpredT) /=.
  apply eq_bigr => i _.
  transitivity (X1 i ^ 2 * \rsum_(j in 'rV_n.+1) (Multivar.to_bivar `p_ X) (i, j)).
  + rewrite big_distrr /=; apply eq_bigr => i0 _.
    by rewrite row_mx_row_ord0 Multivar.to_bivarE.
  + congr (_ * _)%R; by rewrite Hjoint1 /Multivar.head_of Bivar.fstE.
- rewrite -mulRA -E_id_rem_helper // big_distrr /=.
  apply eq_bigr => i _; field.
- rewrite ExE -(big_rV_cons_behead _ xpredT xpredT) exchange_big /=.
  apply eq_bigr => t _.
  transitivity (X2 t ^ 2 * \rsum_(i in A) (Multivar.to_bivar `p_ X) (i, t)).
  + rewrite big_distrr /=; apply eq_bigr => i _.
    by rewrite rbehead_row_mx Multivar.to_bivarE.
  + congr (_ * _); by rewrite Hjoint2 /Multivar.tail_of Bivar.sndE.
Qed.

(** The variance of the sum is the sum of variances for any two
  independent random variables %(\cite[Theorem 6.8]{probook})%: *)
Lemma V_linear_2 : X \= X1 @+ X2 -> (Multivar.to_bivar `p_X) |= X1 _|_ X2  ->
  `V X = `V X1 + `V X2.
Proof.
move=> H ?; rewrite !V_alt E_id_rem // (E_linear_2 H) sqrRD; by field.
Qed.

End sum_two_rand_var.

Section sum_n_rand_var_def.

Variable A : finType.

(** The sum of n >= 1 random variable(s): *)
Inductive sum_n : forall n, {rvar 'rV[A]_n, R} -> 'rV[{rvar A, R}]_n -> Prop :=
| sum_n_1 : forall X, cast_rV1 X \=sum X
| sum_n_cons : forall n (Xs : 'rV_n.+1) Y X Z,
  Y \=sum Xs -> Z \= X @+ Y -> Z \=sum (row_mx (\row_(k < 1) X) Xs)
where "X '\=sum' Xs" := (sum_n X Xs) : proba_scope.

End sum_n_rand_var_def.

Notation "X '\=sum' Xs" := (sum_n X Xs) : proba_scope.

Section sum_n_rand_var.

Variable A : finType.

Local Open Scope vec_ext_scope.

Lemma E_linear_n : forall n (Xs : 'rV[{rvar A, R}]_n) X,
  X \=sum Xs -> `E X = \rsum_(i < n) `E Xs ``_ i.
Proof.
elim => [Xs Xbar | [_ Xs Xbar | n IHn Xs Xbar] ].
- by inversion 1.
- inversion 1; subst.
  apply Eqdep_dec.inj_pair2_eq_dec in H0; last exact eq_nat_dec.
  apply Eqdep_dec.inj_pair2_eq_dec in H1; last exact eq_nat_dec.
  subst Xs Xbar.
  by rewrite big_ord_recl big_ord0 addR0 /cast_rV1 E_rvar_rV1_of_rvar.
- inversion 1; subst.
  apply Eqdep_dec.inj_pair2_eq_dec in H1; last exact eq_nat_dec.
  apply Eqdep_dec.inj_pair2_eq_dec in H2; last exact eq_nat_dec.
  subst Z Xs.
  move: {IHn}(IHn _ _ H3) => IHn.
  rewrite big_ord_recl.
  have -> : \rsum_(i < n.+1) `E ((row_mx (\row_(k < 1) X) Xs0) ``_ (lift ord0 i)) =
           \rsum_(i < n.+1) `E (Xs0 ``_ i).
    apply eq_bigr => i _ /=.
    rewrite !ExE.
    apply eq_bigr => a _ /=.
    rewrite (_ : lift _ _ = rshift 1 i); last exact: val_inj.
    by rewrite (@row_mxEr _ _ 1).
  by rewrite -IHn (E_linear_2 H4) row_mx_row_ord0.
Qed.

End sum_n_rand_var.

Section sum_n_independent_rand_var_def.

Variable A : finType.

(** The sum of n >= 1 independent random variables: *)

Inductive isum_n : forall n,
  {rvar 'rV[A]_n, R} -> 'rV[{rvar A, R}]_n -> Prop :=
| isum_n_1 : forall X, cast_rV1 X \=isum X
| isum_n_cons : forall n (Ys : 'rV_n.+1) Y X Z,
  Y \=isum Ys -> Z \= X @+ Y -> (Multivar.to_bivar `p_Z) |= X _|_ Y ->
  Z \=isum (row_mx (\row_(k < 1) X) Ys)
where "X '\=isum' Xs" := (isum_n X Xs) : proba_scope.

End sum_n_independent_rand_var_def.

Notation "X '\=isum' Xs" := (isum_n X Xs) : proba_scope.

Section sum_n_independent_rand_var.

Variable A : finType.

Lemma sum_n_i_sum_n n (Xs : 'rV[{rvar A, R}]_n) X : X \=isum Xs -> X \=sum Xs.
Proof.
elim.
- move=> X0; by constructor 1.
- move=> {Xs X n} n Ys Y X Z H1 H2 H3 H4.
  by econstructor 2; eauto.
Qed.

Local Open Scope vec_ext_scope.

Lemma V_linearity_isum : forall n (X : {rvar 'rV[A]_n, R}) (Xs : 'rV[{rvar A, R}]_n),
  X \=isum Xs ->
  forall sigma2, (forall i, `V (Xs ``_ i) = sigma2) ->
  `V X = INR n * sigma2.
Proof.
elim.
  move=> X Xs X_Xs sigma2 Hsigma2.
  by inversion X_Xs.
case=> [_ | n IH] Xsum Xs Hsum s Hs.
- inversion Hsum.
  apply Eqdep_dec.inj_pair2_eq_dec in H; last exact eq_nat_dec.
  apply Eqdep_dec.inj_pair2_eq_dec in H0; last exact eq_nat_dec.
  subst Xs Xsum.
  by rewrite /cast_rV1 V_rvar_rV1_of_rvar /= mul1R.
- move: Hsum; inversion 1.
  apply Eqdep_dec.inj_pair2_eq_dec in H0; last exact eq_nat_dec.
  apply Eqdep_dec.inj_pair2_eq_dec in H1; last exact eq_nat_dec.
  subst Z n0 Xs.
  move: {IH}(IH Y Ys H2) => IH.
  rewrite S_INR mulRDl -IH.
  + by rewrite mul1R addRC (V_linear_2 H3) // -(Hs ord0) /= row_mx_row_ord0.
  + move=> i; rewrite -(Hs (lift ord0 i)).
    congr (`V _).
    rewrite (_ : lift _ _ = rshift 1 i); last exact: val_inj.
    by rewrite (@row_mxEr _ _ 1).
Qed.

(** The variance of the average for independent random variables: *)

Lemma V_average_isum n (X : {rvar 'rV[A]_n, R}) Xs (sum_Xs : X \=isum Xs) :
  forall sigma2, (forall i, `V (Xs ``_ i) = sigma2) ->
  INR n * `V (X '/ n) = sigma2.
Proof.
move=> s Hs.
destruct n.
  by inversion sum_Xs.
rewrite (V_scale X) // (V_linearity_isum sum_Xs Hs) //; field; exact/INR_eq0.
Qed.

End sum_n_independent_rand_var.

Section weak_law_of_large_numbers.

Local Open Scope vec_ext_scope.

Variable A : finType.
Variable P : dist A.
Variable n : nat.
Variable Xs : 'rV[{rvar A, R}]_n.+1.     (*Hypothesis Xs_id : id_dist P Xs.*)
Variable miu : R.                   Hypothesis E_Xs : forall i, `E Xs ``_ i = miu.
Variable sigma2 : R.                Hypothesis V_Xs : forall i, `V Xs ``_ i = sigma2.
Variable X : {rvar 'rV[A]_n.+1, R}.
Variable X_Xs : X \=isum Xs.

Lemma wlln epsilon : 0 < epsilon ->
  Pr `p_X [set t | `| (X '/ n.+1) t - miu | >b= epsilon] <=
    sigma2 / (n.+1%:R * epsilon ^ 2).
Proof.
move=> He.
rewrite divRM; last 2 first.
  by rewrite INR_eq0.
  exact/gtR_eqF/expR_gt0.
have <- : `V (X '/ n.+1) = sigma2 / INR n.+1.
  rewrite -(V_average_isum X_Xs V_Xs) V_scale //; by field; exact/INR_eq0.
have <- : `E (X '/ n.+1) = miu.
  rewrite E_scale (E_linear_n (sum_n_i_sum_n X_Xs)).
  set su := \rsum_(_ <- _) _.
  have -> : su = INR n.+1 * miu.
    rewrite /su.
    transitivity (\rsum_(i < n.+1) miu); first exact/eq_bigr.
    by rewrite big_const /= iter_addR cardE /= size_enum_ord.
  by rewrite div1R mulRA mulVR ?mul1R // INR_eq0'.
move/leR_trans: (chebyshev_inequality (X '/ n.+1) He); apply; exact/leRR.
Qed.

End weak_law_of_large_numbers.
