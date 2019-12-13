(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import all_ssreflect ssralg fingroup perm finalg matrix.
From mathcomp Require boolp.
Require Import Reals Lra Nsatz.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop.

(******************************************************************************)
(*               Probabilities over finite distributions                      *)
(*                                                                            *)
(* This file provides a formalization of finite probabilities using           *)
(* distributions over a finite type (see fsdist.v for finitely-supported      *)
(* distributions) that ends with a proof of the weak law of large numbers.    *)
(*                                                                            *)
(*  {fdist A}       == the type of distributions over a finType A             *)
(*  Pr d E          == probability of event E over the distribution d         *)
(*  {RV P -> T}     == the type of random variables over an ambient           *)
(*                     distribution P                                         *)
(*  \Pr[ X = a ]    == the probability that the random variable X is a        *)
(* `Pr_ P [ A | B ] == conditional probability                                *)
(*  P |= X _|_ Y    == the random variables X and Y over the ambient          *)
(*                     distribution P are independent                         *)
(* `E X             == expected value of the random variable X                *)
(* `V X             == the variance of the random variable X                  *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*  E_sum_2              == the expected value of a sum is the sum of         *)
(*                          expected values, whether or not the  summands     *)
(*                           are mutually independent (the ``First            *)
(*                           Fundamental Mystery of Probability'')            *)
(*  V_sum_2              == the variance of the sum is the sum of variances   *)
(*                           for any two independent random variables         *)
(*  Var_average          == The variance of the average for independent       *)
(*                            random variables                                *)
(*  Pr_bigcup            == union bound/Boole's inequality                    *)
(*  Boole_eq             == Boole's equality                                  *)
(*  law_of_total_probability, law_of_total_probability_cond ==                *)
(*                          laws of total probability                        *)
(*  bayes_theorem        == Bayes' theorem                                    *)
(*  Pr_bigcup_incl_excl  == an algebraic proof (by Erik Martin-Dorel) of the  *)
(*                          formula of inclusion-exclusion                   *)
(*  markov               == Markov inequality                                 *)
(*  chebyshev_inequality == Chebyshev's inequality                            *)
(*  wlln                 == weak law of large numbers                         *)
(******************************************************************************)

(* OUTLINE
  1. Module FDist.
  2. Module FDist1.
  3. Module FDistBind.
  4. Module FDistMap.
  5. Module Uniform.
  6. Module UniformSupport.
       Uniform distribution with a restricted support
  7. Module Binary.
      Distributions over sets with two elements
  8. Module BinarySupport.
  9. Module D1Dist.
       construction of a distribution from another
       by removing one element from the support
  10. Module ConvnFDist.
  11. Module ConvFDist.
  12. Module Bivar.
       Joint (Bivariate) Distribution
  13. Module Multivar
       Joint (Multivariate) distribution
      Section joint_tuple_dist.
  14. Module ProdFDist.
  15. Module TupleFDist.
  16. Section wolfowitz_counting.
  17. Section probability.
  18. Section random_variable.
  19. Section expected_value_def.
      Section expected_value_prop.
        Properties of the expected value of standard random variables
  20. Section probability_inclusion_exclusion.
  21. Section markov_inequality.
  22. Section variance_def.
      Section variance_prop.
  23. Section chebyshev.
        Chebyshev's Inequality
  24. independence
      Section sum_two_rand_var_def.
        The sum of two random variables
      Section sum_two_rand_var.
      Section sum_n_rand_var_def.
        The sum of n >= 1 independent random variable(s)
      Section sum_n_rand_var.
  25. Section weak_law_of_large_numbers.
*)

Reserved Notation "{ 'fdist' T }" (at level 0, format "{ 'fdist'  T }").
Reserved Notation "'`U' HC " (at level 10, HC at next level).
Reserved Notation "P `^ n" (at level 5).
Reserved Notation "P1 `x P2" (at level 6).
Reserved Notation "P1 `, P2" (at level 6).
Reserved Notation "{ 'RV' d -> T }" (at level 0, d, T at next level,
  format "{ 'RV'  d  ->  T }").
Reserved Notation "`p_ X" (at level 5).
Reserved Notation "\Pr[ X = a ]" (at level 6, X, a at next level,
  format "\Pr[  X  =  a  ]").
Reserved Notation "\Pr[ X '\in' E ]" (at level 6, X, E at next level,
  format "\Pr[  X  '\in'  E  ]").
Reserved Notation "\Pr[ X >= r ]" (at level 6, X, r at next level,
  format "\Pr[  X  >=  r  ]").
Reserved Notation "k `cst* X" (at level 49).
Reserved Notation "X '`/' n" (at level 49, format "X  '`/'  n").
Reserved Notation "X `+ Y" (at level 50).
Reserved Notation "X `- Y" (at level 50).
Reserved Notation "X '`+cst' m" (at level 50).
Reserved Notation "X '`-cst' m" (at level 50).
Reserved Notation "X '`^2' " (at level 49).
Reserved Notation "'--log' P" (at level 5).
Reserved Notation "'`E'" (at level 5).
Reserved Notation "'`E_'" (at level 5, format "'`E_'").
Reserved Notation "X '\=sum' Xs" (at level 50).
Reserved Notation "'`V'" (at level 5).
Reserved Notation "'`V_' x" (at level 5, format "'`V_' x").
Reserved Notation "`Pr_ P [ A | B ]" (at level 6, P, A, B at next level,
  format "`Pr_ P [ A  |  B ]").
Reserved Notation "`Pr_[ A | B ]" (at level 6, A, B at next level,
  format "`Pr_[ A  |  B ]").
Reserved Notation "P |= X _|_ Y" (at level 50, X, Y at next level,
  format "P  |=  X  _|_  Y").
Reserved Notation "Z \= X '@+' Y" (at level 50).
Reserved Notation "X @^-1 x" (at level 10).
Reserved Notation "x <| p |> y" (format "x  <| p |>  y", at level 50).

Declare Scope proba_scope.

Notation "X @^-1 x" := ([set h | X h == x]) : proba_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.
Local Open Scope reals_ext_scope.
Local Open Scope tuple_ext_scope.

Module FDist.
Section fdist.
Variable A : finType.
Record t := mk {
  f :> A ->R+ ;
  _ : \sum_(a in A) f a == 1 :> R }.
Lemma ge0 (d : t) a : 0 <= d a.
Proof. by case: d => /= f _; apply/pos_ff_ge0. Qed.
Lemma f1 (d : t) : \sum_(a in A) d a = 1 :> R.
Proof. by case: d => f /= /eqP. Qed.
Lemma le1 (d : t) a : d a <= 1.
Proof.
rewrite -(f1 d) (_ : d a = \sum_(a' in A | a' == a) d a').
  apply (@ler_rsum_l_support _ _ _ xpredT) => // ?; exact/ge0.
by rewrite big_pred1_eq.
Qed.
Definition make (f : {ffun A -> R}) (H0 : forall a, 0 <= f a)
  (H1 : \sum_(a in A) f a = 1) := @mk (@mkPosFfun _ f
  (proj1 (@reflect_iff _ _ (forallP_leRP _)) H0)) (introT eqP H1).
End fdist.
Module Exports.
Notation fdist := t.
End Exports.
End FDist.
Export FDist.Exports.
Coercion FDist.f : fdist >-> pos_ffun.
Canonical fdist_subType A := Eval hnf in [subType for @FDist.f A].
Definition fdist_eqMixin A := [eqMixin of fdist A by <:].
Canonical dist_eqType A := Eval hnf in EqType _ (fdist_eqMixin A).

Hint Resolve FDist.ge0 : core.
Hint Resolve FDist.le1 : core.

Definition fdist_of (A : finType) := fun phT : phant (Finite.sort A) => fdist A.

Notation "{ 'fdist' T }" := (fdist_of (Phant T)) : proba_scope.

Lemma fdist_ge0_le1 (A : finType) (d : fdist A) a : 0 <= d a <= 1.
Proof. by []. Qed.

Definition probfdist (A : finType) (d : fdist A) a := Prob.mk (fdist_ge0_le1 d a).

Section FDist_lemmas.

Variable A : finType.
Implicit Types d : fdist A.

Definition is_fdist (f : A -> R) : Prop :=
  (forall a, 0 <= f a) /\ (\sum_(a in A) f a = 1).

Lemma fdist_is_fdist d : is_fdist d.
Proof. by case: d; case => f /= /forallP_leRP H0 /eqP H1. Qed.

Lemma fdist_card_neq0 d : (0 < #| A |)%nat.
Proof.
apply/negPn/negP => abs; apply R1_neq_R0.
rewrite -(FDist.f1 d) (eq_bigl xpred0) ?big_pred0_eq // => a.
apply/negP => aA.
move/card_gt0P : abs; apply; by exists a.
Qed.

Definition fdist_supp d := [set a | d a != 0].

Lemma rsum_fdist_supp (f : A -> R) d (P : pred A):
  \sum_(a in A | P a) d a * f a = \sum_(a | P a && (a \in fdist_supp d)) d a * f a.
Proof.
rewrite (bigID (mem (fdist_supp d))) /= addRC (eq_bigr (fun=> 0)); last first.
  move=> i; rewrite inE negbK => /andP[_ /eqP] ->; by rewrite mul0R.
rewrite big_const iter_addR mulR0 add0R [in RHS]big_seq_cond.
apply eq_bigl => a; by rewrite !inE andbC /index_enum -enumT mem_enum inE.
Qed.

Lemma fdist_ind (P : fdist A -> Type) :
  (forall n : nat, (forall X, #|fdist_supp X| = n -> P X) ->
    forall X b, #|fdist_supp X| = n.+1 -> X b != 0 -> P X) ->
  forall X, P X.
Proof.
move=> H1 d.
move: {-2}(#|fdist_supp d|) (erefl (#|fdist_supp d|)) => n; move: n d.
elim=> [d /esym /card0_eq Hd0|].
  move: (FDist.f1 d).
  rewrite -[X in X = _]mulR1 big_distrl rsum_fdist_supp big1 => [H01|a].
    by elim: (gtR_eqF _ _ Rlt_0_1).
  by rewrite Hd0.
move=> n IH d n13.
have [b Hb] : {b : A | d b != 0}.
  suff : {x | x \in fdist_supp d} by case => a; rewrite inE => ?; exists a.
  apply/sigW/set0Pn; by rewrite -cards_eq0 -n13.
by refine (H1 n _ _ _ _ Hb) => // d' A2; apply IH.
Qed.

Lemma fdist_gt0 d a : (d a != 0) <-> (0 < d a).
Proof.
split => H; [|by move/gtR_eqF : H => /eqP].
rewrite ltR_neqAle; split => //; exact/nesym/eqP.
Qed.

Lemma fdist_lt1 d a : (d a != 1) <-> (d a < 1).
Proof.
split=> H; first by rewrite ltR_neqAle; split => //; exact/eqP.
exact/eqP/ltR_eqF.
Qed.

Lemma fdist_ext d d' : (forall x, pos_ff d x = pos_ff d' x) -> d = d'.
Proof. move=> ?; exact/val_inj/val_inj/ffunP. Qed.

End FDist_lemmas.

Local Open Scope proba_scope.

Module FDist1.
Section fdist1.
Variables (A : finType) (a : A).
Definition f := [ffun b => INR (b == a)%bool].
Lemma f0 b : 0 <= f b. Proof. rewrite ffunE; exact: leR0n. Qed.
Lemma f1 : \sum_(b in A) f b = 1.
Proof.
rewrite (bigD1 a) //= {1}/f ffunE eqxx /= (eq_bigr (fun=> 0)); last first.
  by move=> b ba; rewrite /f ffunE (negbTE ba).
by rewrite big1_eq // addR0.
Qed.
Definition d : fdist A := locked (FDist.make f0 f1).
Lemma dE a0 : d a0 = INR (a0 == a)%bool.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
End fdist1.
Section prop.
Variable A : finType.
Lemma P (d : {fdist A}) a : reflect (forall i, i != a -> d i = 0) (d a == 1).
Proof.
apply: (iffP idP) => [/eqP H b ?|H].
- move : (FDist.f1 d); rewrite (bigD1 a) //= H => /esym/eqP.
  rewrite addRC -subR_eq' subRR.
  move/eqP/esym/prsumr_eq0P => -> // c ca; exact/fdist_ge0.
- move: (FDist.f1 d); rewrite (bigD1 a) //= => /esym.
  by rewrite -subR_eq => <-; rewrite big1 // subR0.
Qed.
Lemma dE1 (d' : fdist A) a : (d' a == 1 :> R) = (d' == d a :> {fdist A}).
Proof.
apply/idP/idP => [Pa1|/eqP ->]; last by rewrite dE eqxx.
apply/eqP/fdist_ext => a0; rewrite dE.
case/boolP : (a0 == a :> A) => Ha.
by rewrite (eqP Ha); exact/eqP.
by move/P : Pa1 => ->.
Qed.
Lemma supp a : fdist_supp (d a) = [set a] :> {set A}.
Proof.
apply/setP => a0; rewrite !inE; case/boolP : (_ == _ :> A) => [/eqP ->|a0a].
by rewrite dE eqxx; apply/negbT => /=; apply/eqP; rewrite INR_eq0.
by apply/negbTE; rewrite negbK dE (negbTE a0a).
Qed.
Lemma I1 (d : {fdist 'I_1}) : d = FDist1.d ord0.
Proof.
apply/fdist_ext => /= i; rewrite dE (ord1 i) eqxx.
by move: (FDist.f1 d); rewrite big_ord_recl big_ord0 addR0.
Qed.
End prop.
End FDist1.

Module FDistBind.
Section def.
Variables (A B : finType) (p : fdist A) (g : A -> fdist B).
Definition f := [ffun b => \sum_(a in A) p a * (g a) b].
Lemma f0 b : 0 <= f b.
Proof. rewrite /f ffunE; apply rsumr_ge0 => a _; exact: mulR_ge0. Qed.
Lemma f1 : \sum_(b in B) f b = 1.
Proof.
rewrite /f; evar (h : B -> R); rewrite (eq_bigr h); last first.
  move=> b _; rewrite ffunE /h; reflexivity.
rewrite {}/h exchange_big /= -[RHS](FDist.f1 p); apply eq_bigr => a _.
by rewrite -big_distrr /= FDist.f1 mulR1.
Qed.
Definition d : fdist B := locked (FDist.make f0 f1).
Lemma dE x : d x = \sum_(a in A) p a * (g a) x.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
End def.
End FDistBind.

Lemma FDistBind1f (A B : finType) (a : A) (f : A -> fdist B) :
  FDistBind.d (FDist1.d a) f = f a.
Proof.
apply/fdist_ext => b; rewrite FDistBind.dE /= (bigD1 a) //= FDist1.dE eqxx mul1R.
rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 ?addR0 // => c ca.
by rewrite FDist1.dE (negbTE ca) mul0R.
Qed.

Lemma FDistBindp1 A (p : fdist A) : FDistBind.d p (@FDist1.d A) = p.
Proof.
apply/fdist_ext => /= a; rewrite FDistBind.dE /= (bigD1 a) // FDist1.dE eqxx mulR1.
rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 /= ?addR0 //.
by move=> b ba; rewrite FDist1.dE eq_sym (negbTE ba) mulR0.
Qed.

Lemma FDistBindA A B C (m : fdist A) (f : A -> fdist B) (g : B -> fdist C) :
  FDistBind.d (FDistBind.d m f) g = FDistBind.d m (fun x => FDistBind.d (f x) g).
Proof.
apply/fdist_ext => c; rewrite !FDistBind.dE /=.
rewrite (eq_bigr (fun a => \sum_(a0 in A) m a0 * f a0 a * g a c)); last first.
  move=> b _; by rewrite FDistBind.dE big_distrl.
rewrite exchange_big /=; apply eq_bigr => a _.
rewrite FDistBind.dE big_distrr /=; apply eq_bigr => b _; by rewrite mulRA.
Qed.

Module FDistMap.
Section def.
Variables (A B : finType) (g : A -> B) (p : fdist A).
Definition d : {fdist B} := FDistBind.d p (fun a => FDist1.d (g a)).
Lemma dE (b : B) : d b = \sum_(a in A | g a == b) p a.
Proof.
rewrite /d FDistBind.dE [in RHS]big_mkcond /=; apply eq_bigr => a _.
case: ifPn => [/eqP ->|]; rewrite FDist1.dE; [by rewrite eqxx mulR1|].
move/negbTE; rewrite eq_sym => ->; by rewrite mulR0.
Qed.
End def.
Section prop.
Variables (A B C : finType).
Lemma id P : d (@id A) P = P. Proof. by rewrite /d FDistBindp1. Qed.
Lemma comp (g : A -> B) (h : C -> A) P : d g (d h P) = d (g \o h) P.
Proof.
rewrite /d FDistBindA; congr (FDistBind.d _ _).
by rewrite boolp.funeqE => x; rewrite FDistBind1f.
Qed.
End prop.
End FDistMap.

Module Uniform.
Section def.
Variables (A : finType) (n : nat).
Hypothesis domain_not_empty : #|A| = n.+1.
Definition f := [ffun a : A => INR 1 / INR #|A|].
Lemma f0 a : 0 <= f a.
Proof. rewrite ffunE; apply/divR_ge0 => //; apply/ltR0n; by rewrite domain_not_empty. Qed.
Lemma f1 : \sum_(a in A) f a = 1.
Proof.
rewrite /f; evar (h : A -> R); rewrite (eq_bigr h); last first.
  move=> b _; rewrite ffunE /h; reflexivity.
rewrite {}/h -big_distrr /= mul1R big_const iter_addR mulRV //.
by rewrite INR_eq0' domain_not_empty.
Qed.
Definition d : fdist A := locked (FDist.make f0 f1).
Lemma dE a : d a = / INR #|A|.
Proof. by rewrite /d; unlock => /=; rewrite /f div1R ffunE. Qed.
End def.
Lemma d_neq0 (C : finType) (domain_non_empty : { m : nat | #| C | = m.+1 }) :
  forall x, d (projT2 domain_non_empty) x != 0.
Proof.
move=> c; rewrite dE invR_neq0' //; apply/eqP.
case: domain_non_empty => x' ->; by rewrite INR_eq0.
Qed.
End Uniform.

Lemma dom_by_uniform A (P : fdist A) n (HA : #|A| = n.+1) :
  P << (Uniform.d HA).
Proof.
apply/dominatesP => a; rewrite Uniform.dE => /esym abs; exfalso.
move: abs; rewrite HA; exact/ltR_eqF/invR_gt0/ltR0n.
Qed.

Module UniformSupport.
Section def.
Variables (A : finType) (C : {set A}).
Hypothesis support_not_empty : (0 < #|C|)%nat.
Definition f := [ffun a : A => if a \in C then 1 / INR #|C| else 0].
Lemma f0 a : 0 <= f a.
Proof.
rewrite /f ffunE.
case e : (a \in C); last exact/leRR.
apply divR_ge0; [lra|exact/ltR0n].
Qed.
Lemma f1 : \sum_(a in A) f a = 1.
Proof.
rewrite /f.
have HC' : #|C|%:R != 0 by rewrite INR_eq0' -lt0n.
transitivity (\sum_(a in A) (if a \in C then 1 else 0) / INR #|C|).
apply eq_bigr => a _.
  rewrite ffunE; case aC : (a \in C); by [ | move/eqP in HC'; field].
have HC'' : \sum_(a in A) (if a \in C then 1 else 0) = #|C|%:R.
  by rewrite -big_mkcondr /= big_const iter_addR mulR1.
by rewrite /Rdiv -big_distrl HC'' /= mulRV.
Qed.
Definition d : fdist A := locked (FDist.make f0 f1).
End def.
Local Notation "'`U' HC " := (d HC).
Section prop.
Variables (A : finType) (C : {set A}) (HC : (0 < #| C |)%nat).

Lemma dET z : z \in C -> (`U HC) z = 1 / INR #|C|.
Proof. by rewrite /d; unlock; rewrite /= /f ffunE => ->. Qed.

Lemma dEN z : z \notin C -> (`U HC) z = 0.
Proof. by rewrite /d; unlock; move/negbTE; rewrite /= /f ffunE => ->. Qed.

Lemma restrict g : \sum_(t in A) ((`U HC) t * g t) = \sum_(t in C) ((`U HC) t * g t).
Proof.
rewrite (bigID (fun x => x \in C)) /= addRC (eq_bigr (fun=> 0)).
by rewrite big_const // iter_addR mulR0 add0R.
move=> a aC; by rewrite dEN // mul0R.
Qed.

Lemma big_distrr g : \sum_(t in C) ((`U HC) t * g t) = (/ INR #|C| * \sum_(t in C) g t).
Proof.
rewrite /= big_distrr /=; apply eq_bigr => /= i Hi; by rewrite dET // div1R.
Qed.

Lemma neq0 z : ((`U HC) z != 0) = (z \in C).
Proof.
case/boolP : (z \in C) => [/dET ->|/dEN ->//]; last by rewrite eqxx.
rewrite div1R; by apply/invR_neq0'; rewrite INR_eq0' -lt0n.
Qed.
End prop.
End UniformSupport.

Notation "'`U' HC " := (UniformSupport.d HC) : proba_scope.

Module Binary.
Section def.
Variable A : finType.
Hypothesis HA : #|A| = 2%nat.
Variable p : prob.
Definition f (a : A) := [ffun a' => if a' == a then p.~ else p].
Lemma f0 (a a' : A) : 0 <= f a a'.
Proof. by rewrite /f ffunE; case: ifP. Qed.
Lemma f1 (a : A) : \sum_(a' in A) f a a' = 1.
Proof.
rewrite Set2sumE /= /f !ffunE; case: ifPn => [/eqP <-|].
  by rewrite eq_sym (negbTE (Set2.a_neq_b HA)) subRK.
by rewrite eq_sym; move/Set2.neq_a_b/eqP => <-; rewrite eqxx subRKC.
Qed.
Definition d : A -> fdist A := fun a => locked (FDist.make (f0 a) (f1 a)).
Lemma dE a a' : d a a' = if a' == a then 1 - p else p.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
Lemma d_sum_swap a : \sum_(a' in A) d a a' = \sum_(a' in A) d a' a.
Proof. by rewrite 2!Set2sumE /= !dE !(eq_sym a). Qed.
Lemma dxx a : d a a = 1 - p.
Proof. by rewrite dE eqxx. Qed.
End def.
End Binary.

Section binary_distribution_prop.

Variables (A : finType) (P Q : fdist A).
Hypothesis card_A : #|A| = 2%nat.

Lemma charac_bdist : {r : prob | P = Binary.d card_A r (Set2.a card_A)}.
Proof.
destruct P as [[pf pf0] pf1].
have r01 : 0 <= 1 - pf (Set2.a card_A) <= 1.
  move: (FDist.le1 (FDist.mk pf1) (Set2.a card_A)) => /= H1.
  have {}pf1 : \sum_(a in A) pf a = 1 by rewrite -(eqP pf1); apply eq_bigr.
  move/forallP_leRP : pf0 => /(_ (Set2.a card_A)) => H0.
  split; first lra.
  suff : forall a, a <= 1 -> 0 <= a -> 1 - a <= 1 by apply.
  move=> *; lra.
exists (Prob.mk r01).
apply/fdist_ext => a /=.
rewrite Binary.dE; case: ifPn => [/eqP -> /=|Ha/=]; first by rewrite subRB subRR add0R.
by rewrite -(eqP pf1) /= Set2sumE /= addRC addRK; move/Set2.neq_a_b/eqP : Ha => ->.
Qed.

End binary_distribution_prop.

Module BinarySupport.
Section prop.
Variables (A : finType) (d : fdist A).
Hypothesis Hd : #|fdist_supp d| = 2%nat.
Definition a := enum_val (cast_ord (esym Hd) ord0).
Definition b := enum_val (cast_ord (esym Hd) (lift ord0 ord0)).
Lemma enumE : enum (fdist_supp d) = a :: b :: [::].
Proof.
apply (@eq_from_nth _ a); first by rewrite -cardE Hd.
case=> [_ |]; first by rewrite [X in _ = X]/= {2}/a (enum_val_nth a).
case=> [_ |i]; last by rewrite -cardE Hd.
by rewrite [X in _ = X]/= {1}/b (enum_val_nth a).
Qed.
Lemma rsumE (f : A -> R) : \sum_(i in fdist_supp d) f i = f a + f b.
Proof.
transitivity (\sum_(i <- enum (fdist_supp d)) f i); last first.
  by rewrite enumE 2!big_cons big_nil addR0.
rewrite big_filter; apply eq_bigl => ?; by rewrite !inE.
Qed.
End prop.
End BinarySupport.

Module D1FDist.
Section def.
Variables (B : finType) (X : fdist B) (b : B).
Definition f : B -> R := [ffun a => if a == b then 0 else X a / (1 - X b)].
Hypothesis Xb1 : X b != 1.
Lemma f0 : forall a, 0 <= f a.
Proof.
move=> a; rewrite /f ffunE.
case: ifPn => [_ |ab]; first exact/leRR.
apply mulR_ge0 => //; exact/ltRW/invR_gt0/subR_gt0/fdist_lt1.
Qed.
Lemma f1 : \sum_(a in B) f a = 1.
Proof.
rewrite (bigD1 b) //= {1}/f ffunE eqxx add0R.
rewrite (eq_bigr (fun c => X c / (1 - X b))); last first.
  by move=> ? cb; rewrite /f ffunE (negbTE cb).
rewrite -big_distrl /=.
move: (FDist.f1 X); rewrite (bigD1 b) //=.
move=> /esym; rewrite addRC -subR_eq => H.
have ?: 1 - X b != 0 by rewrite subR_eq0' eq_sym.
rewrite -(@eqR_mul2r (1 - X b)); last exact/eqP.
by rewrite mul1R -mulRA mulVR ?mulR1 // H.
Qed.
Definition d := locked (FDist.make f0 f1).
Lemma dE a : d a = if a == b then 0 else X a / (1 - X b).
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
End def.
Section prop.
Variables (B : finType) (X : fdist B) (b : B).
Hypothesis Xb1 : X b != 1.
Lemma card_fdist_supp (Xb0 : X b != 0) : #|fdist_supp (d Xb1)| = #|fdist_supp X|.-1.
Proof.
rewrite /fdist_supp (cardsD1 b [set a | X a != 0]) !inE Xb0 add1n /=.
apply eq_card => i; rewrite !inE dE.
case: ifPn => //= ib; first by rewrite eqxx.
apply/idP/idP; first by apply: contra => /eqP ->; rewrite div0R.
apply: contra; rewrite /Rdiv mulR_eq0' => /orP[//|H].
exfalso.
move/negPn/negP : H; apply.
by apply/invR_neq0'; rewrite subR_eq0' eq_sym.
Qed.

Lemma d_eq0 a (Xa0 : X a != 0) : ((d Xb1 a == 0) = (b == a))%bool.
Proof.
rewrite dE; case: ifPn => [/eqP ->|ab]; first by rewrite !eqxx.
apply/idP/idP => [|]; last by rewrite eq_sym (negbTE ab).
rewrite mulR_eq0' => /orP[]; first by rewrite (negbTE Xa0).
by move/invR_eq0'; rewrite subR_eq0' eq_sym (negbTE Xb1).
Qed.

Lemma d_0 a : X a = 0 -> d Xb1 a = 0.
Proof. move=> Xa0; rewrite dE Xa0 div0R; by case: ifP. Qed.

End prop.
End D1FDist.

(* TODO: move? *)
(* about_distributions_of_ordinals.*)

Lemma fdistI0_False (d : {fdist 'I_O}) : False.
Proof. move: (fdist_card_neq0 d); by rewrite card_ord. Qed.

Module I2FDist.
Section def.
Variable (p : prob).
Definition d : {fdist 'I_2} := Binary.d (card_ord 2) p (lift ord0 ord0).
Lemma dE a : d a = if a == ord0 then Prob.p p else p.~.
Proof.
rewrite /d Binary.dE; case: ifPn => [/eqP ->|].
by rewrite eq_sym (negbTE (neq_lift _ _)).
by case: ifPn => //; move: a => -[[//|[|]//]].
Qed.
End def.
Section prop.
Lemma p1 : d (`Pr 1) = FDist1.d ord0.
Proof.
apply/fdist_ext => /= i; rewrite dE FDist1.dE; case: ifPn => //= _; exact: onem1.
Qed.
Lemma p0 : d (`Pr 0) = FDist1.d (Ordinal (erefl (1 < 2)%nat)).
Proof.
apply/fdist_ext => /= i; rewrite dE FDist1.dE; case: ifPn => [/eqP ->//|].
case: i => -[//|] [|//] i12 _ /=; by rewrite onem0.
Qed.
End prop.
End I2FDist.

Module AddFDist.
Section def.
Variables (n m : nat) (d1 : {fdist 'I_n}) (d2 : {fdist 'I_m}) (p : prob).
Definition f := [ffun i : 'I_(n + m) =>
  let si := fintype.split i in
  match si with inl a => (p * d1 a) | inr a => p.~ * d2 a end].
Lemma f0 i : 0 <= f i.
Proof. rewrite /f ffunE; case: splitP => a _; exact: mulR_ge0. Qed.
Lemma f1 : \sum_(i < n + m) f i = 1.
Proof.
rewrite -(onemKC p) -{1}(mulR1 p) -(mulR1 p.~).
rewrite -{1}(FDist.f1 d1) -(FDist.f1 d2) big_split_ord /=; congr (_ + _).
- rewrite big_distrr /f /=; apply eq_bigr => i _; rewrite ffunE; case: splitP => [j Hj|k /= Hi].
  + congr (_ * d1 _); apply/val_inj => /=; by rewrite -Hj.
  + move: (ltn_ord i); by rewrite Hi -ltn_subRL subnn ltn0.
- rewrite big_distrr /f /=; apply eq_bigr => i _; rewrite ffunE; case: splitP => [j /= Hi|k /= /eqP].
  + move: (ltn_ord j); by rewrite -Hi -ltn_subRL subnn ltn0.
  + rewrite eqn_add2l => /eqP ik; congr (_ * d2 _); exact/val_inj.
Qed.
Definition d : {fdist 'I_(n + m)} := locked (FDist.make f0 f1).
Lemma dE i : d i =
  match fintype.split i with inl a => p * d1 a | inr a => p.~ * d2 a end.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
End def.
End AddFDist.

Module DelFDist.
Section def.
Variables (n : nat) (P : {fdist 'I_n.+1}) (j : 'I_n.+1) (Pj_neq1 : P j != 1).
Let D : {fdist 'I_n.+1} := D1FDist.d Pj_neq1.
Let h (i : 'I_n) := if (i < j)%nat then widen_ord (leqnSn _) i else lift ord0 i.
Lemma f0 i : 0 <= [ffun x => (D \o h) x] i.
Proof. by rewrite /h ffunE /=; case: ifPn. Qed.
Lemma f1 : \sum_(i < n) [ffun x => (D \o h) x] i = 1.
Proof.
rewrite -(FDist.f1 D) /= (bigID (fun i : 'I_n.+1 => (i < j)%nat)) /=.
rewrite (bigID (fun i : 'I_n => (i < j)%nat)) /=; congr (_ + _).
  rewrite (@big_ord_narrow_cond _ _ _ j n.+1 xpredT); first by rewrite ltnW.
  move=> jn; rewrite (@big_ord_narrow_cond _ _ _ j n xpredT); first by rewrite -ltnS.
  move=> jn'; apply eq_bigr => i _; rewrite ffunE; congr (D _).
  rewrite /h /= ltn_ord; exact/val_inj.
rewrite (bigID (pred1 j)) /= [X in _ = X + _](_ : _ = 0) ?add0R; last first.
  rewrite (big_pred1 j).
  by rewrite /D D1FDist.dE eqxx.
  by move=> /= i; rewrite -leqNgt andbC andb_idr // => /eqP ->.
rewrite [in RHS]big_mkcond big_ord_recl.
set X := (X in _ = addR_monoid _ X).
rewrite /= -leqNgt leqn0 eq_sym andbN add0R.
rewrite big_mkcond; apply eq_bigr => i _.
rewrite -2!leqNgt andbC eq_sym -ltn_neqAle ltnS.
case: ifPn => // ji; by rewrite /h ffunE ltnNge ji.
Qed.
Definition d : {fdist 'I_n} := locked (FDist.make f0 f1).
Lemma dE i : d i = D (h i). Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
Definition f (i : 'I_n) := h i.
End def.
End DelFDist.

Module BelastFDist.
Local Open Scope proba_scope.
Section def.
Variables (n : nat) (P : {fdist 'I_n.+1}) (Pmax_neq1 : P ord_max != 1).
Let D : {fdist 'I_n.+1} := D1FDist.d Pmax_neq1.
Definition d : {fdist 'I_n} := locked (DelFDist.d Pmax_neq1).
Lemma dE i : d i = D (widen_ord (leqnSn _) i).
Proof. by rewrite /d; unlock; rewrite DelFDist.dE ltn_ord. Qed.
End def.
End BelastFDist.

Module ConvnFDist.
Section def.
Variables (A : finType) (n : nat) (e : {fdist 'I_n}) (g : 'I_n -> fdist A).
Definition f := [ffun a => \sum_(i < n) e i * g i a].
Lemma f0 a : 0 <= f a.
Proof. by rewrite ffunE; apply: rsumr_ge0 => /= i _; apply mulR_ge0. Qed.
Lemma f1 : \sum_(a in A) f a = 1.
Proof.
rewrite /f; evar (h : A -> R); rewrite (eq_bigr h); last first.
  move=> b _; rewrite ffunE /h; reflexivity.
rewrite {}/h exchange_big /= -(FDist.f1 e) /=; apply eq_bigr => i _.
by rewrite -big_distrr /= FDist.f1 mulR1.
Qed.
Definition d : fdist A := locked (FDist.make f0 f1).
Lemma dE a : d a = \sum_(i < n) e i * g i a.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
End def.
Section prop.
Variables (A : finType) (n : nat).
Lemma fdist1 (g : 'I_n -> fdist A) a : d (FDist1.d a) g = g a.
Proof.
apply/fdist_ext => a0; rewrite dE (bigD1 a) //= FDist1.dE eqxx mul1R.
by rewrite big1 ?addR0 // => i ia; rewrite FDist1.dE (negbTE ia) mul0R.
Qed.
Lemma cst (e : {fdist 'I_n}) (a : {fdist A}) : d e (fun=> a) = a.
Proof. by apply/fdist_ext => ?; rewrite dE -big_distrl /= FDist.f1 mul1R. Qed.
End prop.
End ConvnFDist.

Lemma s_of_pq_prob (p q : prob) : 0 <= (p.~ * q.~).~ <= 1.
Proof.
move: p q => -[p [p0 p1]] [q [q0 q1]] /=; split; last first.
  apply/onem_le1/mulR_ge0; exact/onem_ge0.
apply/onem_ge0; rewrite -(mulR1 1); apply leR_pmul;
  [exact/onem_ge0 | exact/onem_ge0 | exact/onem_le1 | exact/onem_le1].
Qed.

Definition s_of_pq (p q : prob) : prob := locked (`Pr (p.~ * q.~).~).

Notation "[ 's_of' p , q ]" := (s_of_pq p q) (format "[ 's_of'  p ,  q ]") : proba_scope.

Lemma s_of_pqE (p q : prob) : [s_of p, q] = (p.~ * q.~).~ :> R.
Proof. by rewrite /s_of_pq; unlock. Qed.

Lemma s_of_p0 (p : prob) : [s_of p, `Pr 0] = p.
Proof. by apply/prob_ext; rewrite s_of_pqE onem0 mulR1 onemK. Qed.

Lemma s_of_0q (q : prob) : [s_of `Pr 0, q] = q.
Proof. by apply/prob_ext; rewrite s_of_pqE onem0 mul1R onemK. Qed.

Lemma s_of_pqE' (p q : prob) : [s_of p, q] = p + p.~ * q :> R.
Proof. rewrite s_of_pqE /= /onem; field. Qed.

Lemma s_of_gt0 p q : p != `Pr 0 -> 0 < [s_of p, q].
Proof.
move=> ?; rewrite s_of_pqE';
  apply addR_gt0wl; [exact/prob_gt0 | exact: mulR_ge0].
Qed.

Lemma ge_s_of (p q : prob) : p <= [s_of p, q].
Proof. rewrite s_of_pqE' addRC -leR_subl_addr subRR; exact/mulR_ge0. Qed.

Lemma r_of_pq_prob (p q : prob) : 0 <= p / [s_of p, q] <= 1.
Proof.
case/boolP : (p == `Pr 0 :> prob) => p0.
  rewrite (eqP p0) div0R; split => //; exact/leRR.
case/boolP : (q == `Pr 0 :> prob) => q0.
  rewrite (eqP q0) (s_of_p0 p) divRR //; split => //; exact/leRR.
split.
- apply divR_ge0 => //; exact/s_of_gt0.
- rewrite leR_pdivr_mulr ?mul1R; [exact: ge_s_of | exact: s_of_gt0].
Qed.

Definition r_of_pq (p q : prob) : prob := locked (Prob.mk (r_of_pq_prob p q)).

Notation "[ 'r_of' p , q ]" := (r_of_pq p q) (format "[ 'r_of'  p ,  q ]") : proba_scope.

Lemma r_of_pqE (p q : prob) : [r_of p, q] = p / [s_of p, q] :> R.
Proof. by rewrite /r_of_pq; unlock. Qed.

Lemma r_of_p0 (p : prob) : p != `Pr 0 -> [r_of p, `Pr 0] = `Pr 1.
Proof. by move=> p0; apply prob_ext; rewrite r_of_pqE s_of_p0 divRR. Qed.

Lemma r_of_0q (q : prob) : [r_of `Pr 0, q] = `Pr 0.
Proof. by apply/prob_ext; rewrite r_of_pqE div0R. Qed.

Lemma p_is_rs (p q : prob) : p = [r_of p, q] * [s_of p, q] :> R.
Proof.
case/boolP : (p == `Pr 0 :> prob) => p0; first by rewrite (eqP p0) r_of_0q mul0R.
case/boolP : (q == `Pr 0 :> prob) => q0.
  by rewrite (eqP q0) s_of_p0 r_of_p0 // mul1R.
rewrite r_of_pqE /Rdiv -mulRA mulVR ?mulR1 //.
suff : [s_of p, q] != 0 :> R by [].
by rewrite prob_gt0; apply s_of_gt0.
Qed.

Lemma r_of_pq_is_r (p q r s : prob) : r != `Pr 0 -> s != `Pr 0 ->
  p = r * s :> R -> s.~ = p.~ * q.~ -> [r_of p, q] = r.
Proof.
move=> r0 s0 H1 H2; apply prob_ext => /=.
rewrite r_of_pqE eqR_divr_mulr; last by rewrite s_of_pqE -H2 onemK.
rewrite (p_is_rs _ q) /= {1}s_of_pqE -H2 onemK r_of_pqE s_of_pqE.
by rewrite -H2 onemK /Rdiv -mulRA mulVR ?mulR1.
Qed.

Lemma p_of_rs_prob (r s : prob) : 0 <= r * s <= 1.
Proof.
move: r s => -[r [r0 r1]] [s [s0 s1]] /=.
split; [exact/mulR_ge0 | rewrite -(mulR1 1); exact: leR_pmul].
Qed.

Definition p_of_rs (r s : prob) : prob := locked (Prob.mk (p_of_rs_prob r s)).

Notation "[ 'p_of' r , s ]" := (p_of_rs r s) (format "[ 'p_of'  r ,  s ]") : proba_scope.

Lemma p_of_rsE (r s : prob) : [p_of r, s] = r * s :> R.
Proof. by rewrite /p_of_rs; unlock. Qed.

Lemma p_of_r1 (r : prob) : [p_of r, `Pr 1] = r.
Proof. by apply prob_ext; rewrite p_of_rsE mulR1. Qed.

Lemma p_of_1s (s : prob) : [p_of `Pr 1, s] = s.
Proof. by apply prob_ext; rewrite p_of_rsE mul1R. Qed.

Lemma p_of_r0 (r : prob) : [p_of r, `Pr 0] = `Pr 0.
Proof. by apply/prob_ext; rewrite p_of_rsE mulR0. Qed.

Lemma p_of_0s (s : prob) : [p_of `Pr 0, s] = `Pr 0.
Proof. by apply/prob_ext => /=; rewrite p_of_rsE mul0R. Qed.

Lemma p_of_rsC (r s : prob) : [p_of r, s] = [p_of s, r].
Proof. by apply/prob_ext; rewrite !p_of_rsE mulRC. Qed.

Lemma p_of_neq1 (p q : prob) : 0 < p < 1 -> [p_of q, p] != `Pr 1.
Proof.
case=> p0 p1; apply/eqP => pq1; move: (p1).
rewrite [X in _ < X -> _](_ : _ = Prob.p (`Pr 1)) //.
rewrite -pq1 p_of_rsE -ltR_pdivr_mulr // divRR ?prob_gt0 //.
rewrite ltRNge; apply; exact/prob_le1.
Qed.

Lemma p_of_rs1 (r s : prob) :
  ([p_of r, s] == `Pr 1 :> prob) = ((r == `Pr 1) && (s == `Pr 1)).
Proof.
apply/idP/idP; last by case/andP => /eqP -> /eqP ->; rewrite p_of_r1.
move/eqP/(congr1 Prob.p); rewrite /= p_of_rsE => /eqP.
apply contraLR => /nandP H.
wlog: r s H / r != `Pr 1;
  first by case: H;
  [ move => H /(_ r s); rewrite H; apply => //; by left
  | move => H /(_ s r); rewrite H mulRC; apply => //; by left ].
move=> Hr.
case/boolP: (r == `Pr 0 :> prob);
  first by move/eqP ->; rewrite mul0R eq_sym; apply/eqP/R1_neq_R0.
case/prob_gt0/ltR_neqAle => /eqP; rewrite [in X in X -> _]eq_sym => /eqP Hr' _.
apply/eqP => /(@eqR_mul2r (/ r)).
move/(_ (invR_neq0 _ Hr')).
rewrite mulRAC mulRV ?mul1R; last exact/eqP.
move=> srV.
move: (prob_le1 s); rewrite srV.
move/eqP : Hr' => /prob_gt0 Hr'.
rewrite invR_le1 // => Hr''.
move: (prob_le1 r) => Hr'''.
suff: r = 1 :> R by apply/eqP; rewrite Hr.
by apply eqR_le.
Qed.

Lemma p_of_rs1P r s : reflect (r = `Pr 1 /\ s  = `Pr 1) ([p_of r, s] == `Pr 1).
Proof.
move: (p_of_rs1 r s) ->.
apply: (iffP idP);
  [by case/andP => /eqP -> /eqP -> | by case => -> ->; rewrite eqxx].
Qed.

Lemma q_of_rs_prob (r s : prob) : 0 <= (r.~ * s) / [p_of r, s].~ <= 1.
Proof.
case/boolP : (r == `Pr 1 :> prob) => r1.
  rewrite (eqP r1) onem1 mul0R div0R; split => //; exact/leRR.
case/boolP : (s == `Pr 1 :> prob) => s1.
  rewrite (eqP s1) mulR1 p_of_r1 divRR ?onem_neq0 //; split=> //; exact/leRR.
split.
  apply/divR_ge0; first exact/mulR_ge0.
    apply/onem_gt0; rewrite p_of_rsE -(mulR1 1); apply/ltR_pmul => //;
      by [rewrite -prob_lt1 | rewrite -prob_lt1].
rewrite leR_pdivr_mulr ?mul1R.
  rewrite p_of_rsE {2}/onem leR_subr_addr -mulRDl addRC onemKC mul1R; exact/prob_le1.
apply onem_gt0; rewrite p_of_rsE -(mulR1 1); apply/ltR_pmul => //;
  by [rewrite -prob_lt1 | rewrite -prob_lt1].
Qed.

Definition q_of_rs (r s : prob) : prob := locked (Prob.mk (q_of_rs_prob r s)).

Notation "[ 'q_of' r , s ]" := (q_of_rs r s) (format "[ 'q_of'  r ,  s ]") : proba_scope.

Lemma q_of_rsE (r s : prob) : [q_of r, s] = (r.~ * s) / [p_of r, s].~ :> R.
Proof. by rewrite /q_of_rs; unlock. Qed.

Lemma q_of_r0 (r : prob) : [q_of r, `Pr 0] = `Pr 0.
Proof. by apply/prob_ext => /=; rewrite q_of_rsE mulR0 div0R. Qed.

Lemma q_of_r1 (r : prob) : r != `Pr 1 -> [q_of r, `Pr 1] = `Pr 1.
Proof.
move=> r1.
by apply/prob_ext => /=; rewrite q_of_rsE /= mulR1 p_of_r1 divRR // onem_neq0.
Qed.

Lemma q_of_1s (s : prob) : [q_of `Pr 1, s] = `Pr 0.
Proof. by apply/prob_ext => /=; rewrite q_of_rsE onem1 mul0R div0R. Qed.

Lemma pq_is_rs (p q : prob) : p.~ * q = [r_of p, q].~ * [s_of p, q].
Proof.
case/boolP : (p == `Pr 0 :> prob) => p0.
  by rewrite (eqP p0) onem0 mul1R r_of_0q onem0 mul1R s_of_0q.
rewrite r_of_pqE [in RHS]mulRBl mul1R.
rewrite /Rdiv -mulRA mulVR ?mulR1; last first.
  rewrite prob_gt0; exact/s_of_gt0.
by rewrite s_of_pqE' addRC addRK.
Qed.

Lemma s_of_pqK r s : [p_of r, s] != `Pr 1 ->
  [s_of [p_of r, s], [q_of r, s]] = s.
Proof.
move=> H.
apply/prob_ext; rewrite s_of_pqE /= p_of_rsE /= q_of_rsE /= p_of_rsE /=.
rewrite /onem; field.
rewrite subR_eq0; apply/eqP; apply: contra H => /eqP rs1.
by apply/eqP/prob_ext => /=; rewrite p_of_rsE.
Qed.

Lemma r_of_pqK (r s : prob) : [p_of r, s] != `Pr 1 -> s != `Pr 0 ->
  [r_of [p_of r, s], [q_of r, s]] = r.
Proof.
move=> H1 s0; apply/prob_ext => /=.
rewrite !(r_of_pqE,s_of_pqE,q_of_rsE,p_of_rsE) /onem; field.
split.
  rewrite subR_eq0 => /esym.
  apply/eqP; apply: contra H1 => /eqP H1.
  apply/eqP/prob_ext; by rewrite p_of_rsE.
rewrite 2!subRB subRR add0R mulRBl mul1R addRC subRK; exact/eqP.
Qed.

Module ConvFDist.
Section def.
Variables (A : finType) (p : prob) (d1 d2 : fdist A).
Definition d : {fdist A} := locked
  (ConvnFDist.d (I2FDist.d p) (fun i => if i == ord0 then d1 else d2)).
Lemma dE a : d a = p * d1 a + p.~ * d2 a.
Proof.
rewrite /d; unlock => /=.
by rewrite ConvnFDist.dE !big_ord_recl big_ord0 /= addR0 !I2FDist.dE.
Qed.
End def.
Section prop.
Variables (A : finType).
Implicit Types a b c : fdist A.

Local Notation "x <| p |> y" := (d p x y).

Lemma d1 a b : a <| `Pr 1 |> b = a.
Proof. apply/fdist_ext => a0; by rewrite dE /= onem1 mul1R mul0R addR0. Qed.

Lemma skewed_commute p a b : a <| p |> b = b <| `Pr p.~ |> a.
Proof. apply/fdist_ext => a0 /=; by rewrite 2!dE onemK addRC. Qed.

Lemma idempotent p a : a <| p |> a = a.
Proof. apply/fdist_ext => a0; by rewrite dE mulRBl mul1R addRCA addRN addR0. Qed.

Lemma quasi_assoc p q a b c :
  a <| p |> (b <| q |> c) = (a <| [r_of p, q] |> b) <| [s_of p, q] |> c.
Proof.
apply/fdist_ext => a0 /=; rewrite 4!dE /=.
set r := r_of_pq p q.  set s := s_of_pq p q.
transitivity (p * a a0 + p.~ * q * b a0 + p.~ * q.~ * c a0); first lra.
transitivity (r * s * a a0 + r.~ * s * b a0 + s.~ * c a0); last first.
  by rewrite 2!(mulRC _ s) -2!mulRA -mulRDr.
rewrite s_of_pqE onemK; congr (_ + _).
rewrite (_ : (p.~ * q.~).~ = [s_of p, q]); last by rewrite s_of_pqE.
by rewrite -pq_is_rs -p_is_rs.
Qed.

Lemma bind_left_distr (B : finType) p a b (f : A -> fdist B) :
  FDistBind.d (a <| p |> b) f = FDistBind.d a f <| p |> FDistBind.d b f.
Proof.
apply/fdist_ext => a0 /=; rewrite !(FDistBind.dE,dE) /=.
rewrite 2!big_distrr /= -big_split /=; apply/eq_bigr => a1 _.
by rewrite dE mulRDl !mulRA.
Qed.

End prop.
End ConvFDist.

Local Notation "x <| p |> y" := (ConvFDist.d p x y) : proba_scope.

Module PermFDist.
Section def.
Variables (n : nat) (P : {fdist 'I_n}) (s : 'S_n).
Definition f := [ffun i : 'I_n => P (s i)].
Lemma f0 (i : 'I_n) : 0 <= f i. Proof. by rewrite ffunE. Qed.
Lemma f1 : \sum_(i < n) f i = 1.
Proof.
transitivity (\sum_(i <- [tuple (s^-1)%g i | i < n]) f i).
  apply/perm_big/tuple_permP; exists s.
  destruct n; first by move: (fdistI0_False P).
  rewrite /index_enum -enumT; apply/(@eq_from_nth _ ord0).
    by rewrite size_map size_tuple -enumT size_enum_ord.
  move=> i; rewrite size_enum_ord => ni /=.
  rewrite (nth_map ord0) ?size_enum_ord //= tnth_map /=.
  apply (@perm_inj _ s); by rewrite permKV /= tnth_ord_tuple.
rewrite -(FDist.f1 P) /= big_map; apply congr_big => //.
  by rewrite /index_enum -enumT.
move=> i _; by rewrite /f ffunE permKV.
Qed.
Definition d : {fdist 'I_n} := locked (FDist.make f0 f1).
Lemma dE i : d i = P (s i).
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
End def.
Section prop.
Lemma dE1 (n : nat) (P : {fdist 'I_n}) : d P 1%g = P.
Proof. apply/fdist_ext => /= i; by rewrite dE perm1. Qed.
Lemma mul (n : nat) (P : {fdist 'I_n}) (s s' : 'S_n) : d (d P s) s' = d P (s' * s).
Proof. by apply/fdist_ext => /= i; rewrite !dE permM. Qed.
Lemma tperm (n : nat) (a b : 'I_n) : d (FDist1.d a) (tperm a b) = FDist1.d b.
Proof.
apply/fdist_ext => /= x; rewrite dE !FDist1.dE permE /=.
case: ifPn => [/eqP ->|xa]; first by rewrite eq_sym.
case: ifPn; by [rewrite eqxx | move=> _; rewrite (negbTE xa)].
Qed.
Lemma d1 (n : nat) (a : 'I_n) (s : 'S_n) : d (FDist1.d a) s = FDist1.d (s^-1 a)%g.
Proof.
apply/fdist_ext => /= i; rewrite dE !FDist1.dE; congr (INR (nat_of_bool _)).
by apply/eqP/eqP => [<-|->]; rewrite ?permK // ?permKV.
Qed.
End prop.
End PermFDist.

(* bivariate (joint) distribution *)
Module Bivar.
Section def.
Variables (A B : finType) (P : {fdist A * B}).

(* marginal left *)
Definition fst : fdist A := FDistMap.d fst P.

Lemma fstE a : fst a = \sum_(i in B) P (a, i).
Proof.
by rewrite /fst FDistMap.dE -(pair_big_fst _ _ (pred1 a)) //= big_pred1_eq.
Qed.

Lemma dom_by_fst a b : fst a = 0 -> P (a, b) = 0.
Proof. rewrite fstE => /prsumr_eq0P -> // ? _; exact: fdist_ge0. Qed.

Lemma dom_by_fstN a b : P (a, b) != 0 -> fst a != 0.
Proof. by apply: contra => /eqP /dom_by_fst ->. Qed.

(* marginal right *)
Definition snd : fdist B := FDistMap.d snd P.

Lemma sndE b : snd b = \sum_(i in A) P (i, b).
Proof.
rewrite /snd FDistMap.dE -(pair_big_snd _ _ (pred1 b)) //=.
apply eq_bigr => a ?; by rewrite big_pred1_eq.
Qed.

Lemma dom_by_snd a b : snd b = 0 -> P (a, b) = 0.
Proof. rewrite sndE => /prsumr_eq0P -> // ? _; exact: fdist_ge0. Qed.

Lemma dom_by_sndN a b : P (a, b) != 0 -> snd b != 0.
Proof. by apply: contra => /eqP /dom_by_snd ->. Qed.

End def.
End Bivar.

(* multivariate (joint) distribution *)
Module Multivar.
Section prod_of_rV.
Variables (A : finType) (n : nat) (P : {fdist 'rV[A]_n.+1}).

Let f (v : 'rV[A]_n.+1) : A * 'rV[A]_n := (v ord0 ord0, rbehead v).
Let inj_f : injective f.
Proof.
move=> a b -[H1 H2]; rewrite -(row_mx_rbehead a) -(row_mx_rbehead b).
by rewrite {}H2; congr (@row_mx _ 1 1 n _ _); apply/rowP => i; rewrite !mxE.
Qed.
Definition to_bivar : {fdist A * 'rV[A]_n} := FDistMap.d f P.
Lemma to_bivarE a : to_bivar a = P (row_mx (\row_(i < 1) a.1) a.2).
Proof.
case: a => x y; rewrite /to_bivar FDistMap.dE /=.
rewrite (_ : (x, y) = f (row_mx (\row_(i < 1) x) y)); last first.
  by rewrite /f row_mx_row_ord0 rbehead_row_mx.
by rewrite (big_pred1_inj inj_f).
Qed.

Definition head_of := Bivar.fst to_bivar.
Definition tail_of := Bivar.snd to_bivar.

Let g (v : 'rV[A]_n.+1) : 'rV[A]_n * A := (rbelast v, rlast v).
Let inj_g : injective g.
Proof.
by move=> a b -[H1 H2]; rewrite -(row_mx_rbelast a) -(row_mx_rbelast b) H1 H2.
Qed.
Definition belast_last : {fdist 'rV[A]_n * A} := FDistMap.d g P.
Lemma belast_lastE a : belast_last a =
  P (castmx (erefl, addn1 n) (row_mx a.1 (\row_(i < 1) a.2))).
Proof.
case: a => x y; rewrite /belast_last FDistMap.dE /=.
rewrite (_ : (x, y) = g (castmx (erefl 1%nat, addn1 n) (row_mx x (\row__ y)))); last first.
  by rewrite /g rbelast_row_mx row_mx_row_ord_max.
by rewrite (big_pred1_inj inj_g).
Qed.

End prod_of_rV.

Section rV_of_prod.

Local Open Scope vec_ext_scope.

Variables (A : finType) (n : nat) (P : {fdist A * 'rV[A]_n}).

Let f (x : A * 'rV[A]_n) : 'rV[A]_n.+1 := row_mx (\row_(_ < 1) x.1) x.2.
Lemma inj_f : injective f.
Proof.
move=> -[x1 x2] -[y1 y2]; rewrite /f /= => H.
move: (H) => /(congr1 (@lsubmx A 1 1 n)); rewrite 2!row_mxKl => /rowP/(_ ord0).
rewrite !mxE => ->; congr (_, _).
by move: H => /(congr1 (@rsubmx A 1 1 n)); rewrite 2!row_mxKr.
Qed.
Definition from_bivar : {fdist 'rV[A]_n.+1} := FDistMap.d f P.

Lemma from_bivarE a : from_bivar a = P (a ``_ ord0, rbehead a).
Proof.
rewrite /from_bivar FDistMap.dE /=.
rewrite {1}(_ : a = f (a ``_ ord0, rbehead a)); last first.
  by rewrite /f /= row_mx_rbehead.
by rewrite (big_pred1_inj inj_f).
Qed.

End rV_of_prod.

Lemma from_bivarK (A : finType) n : cancel (@from_bivar A n) (@to_bivar A n).
Proof.
move=> P; apply/fdist_ext => /= -[a b].
by rewrite to_bivarE /= from_bivarE /= row_mx_row_ord0 rbehead_row_mx.
Qed.

Lemma to_bivarK (A : finType) n : cancel (@to_bivar A n) (@from_bivar A n).
Proof.
move=> P; by apply/fdist_ext => v; rewrite from_bivarE to_bivarE row_mx_rbehead.
Qed.

End Multivar.

Module ProdFDist.
Section def.
Variables (A B : finType) (P : fdist A) (Q : A -> fdist B) (*TODO: sto mat?*).
Definition f := [ffun ab => P ab.1 * Q ab.1 ab.2].
Lemma f0 ab : 0 <= f ab. Proof. by rewrite ffunE; apply/mulR_ge0. Qed.
Lemma f1 : \sum_(ab in {: A * B}) f ab = 1.
Proof.
rewrite /f; evar (h : A * B -> R); rewrite (eq_bigr h); last first.
  move=> b _; rewrite ffunE /h; reflexivity.
rewrite {}/h -(pair_bigA _ (fun i j => P i * Q i j)) /= -(FDist.f1 P).
apply eq_bigr => a _; by rewrite -big_distrr FDist.f1 /= mulR1.
Qed.
Definition d := locked (FDist.make f0 f1).
Lemma dE ab : d ab = P ab.1 * Q ab.1 ab.2.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
Lemma fst : Bivar.fst d = P.
Proof.
apply/fdist_ext=> a; rewrite Bivar.fstE (eq_bigr _ (fun b _ => dE (a,b))) /=.
by rewrite -big_distrr FDist.f1 /= mulR1.
Qed.
End def.
Section prop.
Variables (A B : finType) (Q : A -> fdist B).
Lemma fst_convex p (a b : fdist A) : Bivar.fst (d (ConvFDist.d p a b) Q) =
  ConvFDist.d p (Bivar.fst (d a Q)) (Bivar.fst (d b Q)).
Proof. by rewrite !fst. Qed.
Lemma snd_convex p (a b : fdist A) : Bivar.snd (d (ConvFDist.d p a b) Q) =
  ConvFDist.d p (Bivar.snd (d a Q)) (Bivar.snd (d b Q)).
Proof.
apply/fdist_ext => b0.
rewrite Bivar.sndE ConvFDist.dE !Bivar.sndE 2!big_distrr /=.
rewrite -big_split; apply eq_bigr => a0 _; rewrite !dE ConvFDist.dE /=; field.
Qed.
End prop.
End ProdFDist.

(* notation for product distribution *)
Notation "P1 `x P2" := (ProdFDist.d P1 (fun _ => P2)) : proba_scope.

Section prod_dominates_joint.
Variables (A B : finType) (P : {fdist A * B}).
Let P1 := Bivar.fst P. Let P2 := Bivar.snd P.

Local Open Scope reals_ext_scope.
Lemma Prod_dominates_Joint : P << P1 `x P2.
Proof.
apply/dominatesP => -[a b].
rewrite ProdFDist.dE /= mulR_eq0 => -[P1a|P2b];
  by [rewrite Bivar.dom_by_fst | rewrite Bivar.dom_by_snd].
Qed.
End prod_dominates_joint.

Lemma ProdFDistsnd (A B : finType) (P1 : fdist A) (P2 : fdist B) : Bivar.snd (P1 `x P2) = P2.
Proof.
apply/fdist_ext => b.
rewrite Bivar.sndE.
erewrite eq_bigr => /=; last first.
  move=> a Ha; rewrite ProdFDist.dE /=; reflexivity.
by rewrite -big_distrl /= FDist.f1 mul1R.
Qed.

(* product distribution over a row vector *)
Module TupleFDist.
Local Open Scope vec_ext_scope.
Section def.
Variables (A : finType) (P : fdist A) (n : nat).

Definition f := [ffun t : 'rV[A]_n => \prod_(i < n) P t ``_ i].

Lemma f0 t : 0 <= f t.
Proof. by rewrite ffunE; apply rprodr_ge0. Qed.

Lemma f1 : \sum_(t in 'rV_n) f t = 1.
Proof.
pose P' := fun (a : 'I_n) b => P b.
suff : \sum_(g : {ffun 'I_n -> A }) \prod_(i < n) P' i (g i) = 1.
Local Open Scope ring_scope.
  rewrite (reindex_onto (fun j : 'rV[A]_n => finfun (fun x => j ``_ x))
                        (fun i => \row_(j < n) i j)) /=.
Local Close Scope ring_scope.
  - move=> H; rewrite /f -H {H}.
    apply eq_big => t /=.
    + by apply/esym/eqP/rowP => i; rewrite mxE ffunE.
    + move=> _; rewrite ffunE; apply eq_bigr => i _ /=; by rewrite ffunE.
  move=> g _; apply/ffunP => i; by rewrite ffunE mxE.
rewrite -bigA_distr_bigA /= /P'.
rewrite [RHS](_ : _ = \prod_(i < n) 1); last by rewrite big1.
apply eq_bigr => i _; exact: FDist.f1.
Qed.

Definition d : {fdist 'rV[A]_n} := locked (FDist.make f0 f1).

Lemma dE t : d t = \prod_(i < n) P t ``_ i.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.

End def.
Local Notation "P `^ n" := (d P n).
Section prop.
Variable A : finType.

Lemma zero (x : 'rV[A]_0) P : P `^ 0 x = 1.
Proof. by rewrite dE big_ord0. Qed.

Lemma S n (x : 'rV[A]_n.+1) P : P `^ n.+1 x = P (x ``_ ord0) * P `^ n (rbehead x).
Proof.
rewrite 2!TupleFDist.dE big_ord_recl; congr (_ * _).
apply eq_bigr => i _; by rewrite /rbehead mxE.
Qed.

Lemma one (a : 'rV[A]_1) P : (P `^ 1) a = P (a ``_ ord0).
Proof. by rewrite S zero mulR1. Qed.

Lemma to_bivar n (P : fdist A) : Multivar.to_bivar P `^ n.+1 = P `x P `^ n.
Proof.
apply/fdist_ext => /= -[a b].
rewrite Multivar.to_bivarE /= S ProdFDist.dE; congr (P _ * P `^ n _) => /=.
by rewrite row_mx_row_ord0.
by rewrite rbehead_row_mx.
Qed.

End prop.

(* The tuple distribution as a joint distribution *)
Section joint_tuple_fdist.

Variables (A : finType) (P : fdist A) (n : nat).

Lemma head_of : Multivar.head_of (P `^ n.+1) = P.
Proof.
apply/fdist_ext => a; rewrite /Multivar.head_of Bivar.fstE /=.
evar (f : 'rV[A]_n -> R); rewrite (eq_bigr f); last first.
  move=> v _; rewrite Multivar.to_bivarE /= TupleFDist.S.
  rewrite row_mx_row_ord0 rbehead_row_mx /f; reflexivity.
by rewrite {}/f -big_distrr /= FDist.f1 mulR1.
Qed.

Lemma tail_of : Multivar.tail_of (P `^ n.+1) = P `^ n.
Proof.
apply/fdist_ext => a; rewrite /Multivar.tail_of Bivar.sndE /=.
evar (f : A -> R); rewrite (eq_bigr f); last first.
  move=> v _; rewrite Multivar.to_bivarE /= TupleFDist.S.
  rewrite row_mx_row_ord0 rbehead_row_mx /f; reflexivity.
by rewrite {}/f -big_distrl /= FDist.f1 mul1R.
Qed.

End joint_tuple_fdist.
End TupleFDist.

Notation "P `^ n" := (TupleFDist.d P n) : proba_scope.

Local Open Scope ring_scope.
Local Open Scope vec_ext_scope.

Lemma rsum_rmul_rV_pmf_tnth A n k (P : fdist A) :
  (\sum_(t : 'rV[ 'rV[A]_n]_k) \prod_(m < k) (P `^ n) t ``_ m = 1)%R.
Proof.
transitivity (\sum_(j : {ffun 'I_k -> 'rV[A]_n}) \prod_(m : 'I_k) P `^ _ (j m))%R.
  rewrite (reindex_onto (fun p : 'rV_k => [ffun i => p ``_ i])
    (fun x : {ffun 'I_k -> 'rV_n} => \row_(i < k) x i)) //=; last first.
    move=> f _; apply/ffunP => /= k0; by rewrite ffunE mxE.
  apply eq_big => //.
  - move=> v /=; by apply/esym/eqP/rowP => i; rewrite mxE ffunE.
  - move=> i _; apply eq_bigr => j _; by rewrite ffunE.
rewrite -(bigA_distr_bigA (fun m => P `^ _)) /= big_const.
by rewrite iter_mulR FDist.f1 exp1R.
Qed.

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

(* Wolfowitz's counting principle *)
Section wolfowitz_counting.

Variables (C : finType) (P : fdist C) (k : nat) (s : {set 'rV[C]_k}).

Lemma wolfowitz a b A B : 0 < A -> 0 < B ->
  a <= \sum_(x in s) P `^ k x <= b ->
  (forall x : 'rV_k, x \in s -> A <= P `^ k x <= B) ->
  a / B <= INR #| s | <= b / A.
Proof.
move=> A0 B0 [Ha Hb] H.
have HB : \sum_(x in s) P `^ _ x <= INR #|s| * B.
  have HB : \sum_(x in s | predT s ) P `^ _ x <= INR #|s| * B.
    apply (@leR_trans (\sum_(x in s | predT s) [fun _ => B] x)).
      apply ler_rsum_support => /= i iA _; by apply H.
    rewrite -big_filter /= big_const_seq /= iter_addR /=.
    apply leR_wpmul2r; first lra.
    apply Req_le.
    rewrite filter_index_enum count_predT cardE; congr (INR (size _)).
    apply eq_enum => i; by rewrite /in_mem /= andbC.
  apply/(leR_trans _ HB)/Req_le/eq_bigl => i; by rewrite andbC.
have HA : INR #|s| * A <= \sum_(x in s) P `^ _ x.
  have HA : INR #|s| * A <= \sum_(x in s | predT s) P `^ _ x.
    apply (@leR_trans (\sum_(x in s | predT s) [fun _ => A] x)); last first.
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

Local Close Scope ring_scope.

Section probability.
Variables (A : finType) (P : fdist A).
Implicit Types E : {set A}.

Definition Pr E := \sum_(a in E) P a.

Lemma Pr_ge0 E : 0 <= Pr E. Proof. exact: rsumr_ge0. Qed.

Lemma Pr_gt0 E : 0 < Pr E <-> Pr E != R0.
Proof.
split => H; first by move/gtR_eqF : H => /eqP.
rewrite ltR_neqAle; split; [exact/nesym/eqP|exact/Pr_ge0].
Qed.

Lemma Pr_1 E : Pr E <= 1.
Proof. rewrite -(FDist.f1 P); apply ler_rsum_l => // a _; exact/leRR. Qed.

Lemma Pr_set0 : Pr set0 = 0.
Proof. rewrite /Pr big_pred0 // => a; by rewrite in_set0. Qed.

Lemma Pr_set0P E : Pr E = 0 <-> (forall a, a \in E -> P a = 0).
Proof.
rewrite /Pr (eq_bigl (fun x => x \in E)) //; exact: (@prsumr_eq0P _ (mem E) P).
Qed.

Lemma Pr_setT : Pr setT = 1.
Proof. rewrite /Pr (eq_bigl xpredT) ?FDist.f1 // => a; by rewrite in_setT. Qed.

Lemma Pr_set1 a : Pr [set a] = P a.
Proof. by rewrite /Pr big_set1. Qed.

Lemma Pr_cplt E : Pr E + Pr (~: E) = 1.
Proof.
rewrite /Pr -bigU /=; last by rewrite -subsets_disjoint.
rewrite -(FDist.f1 P); apply eq_bigl => /= a; by rewrite !inE /= orbN.
Qed.

Lemma Pr_to_cplt E : Pr E = 1 - Pr (~: E).
Proof. rewrite -(Pr_cplt E); field. Qed.

Lemma Pr_of_cplt E : Pr (~: E) = 1 - Pr E.
Proof. rewrite -(Pr_cplt E); field. Qed.

Lemma Pr_incl E E' : E \subset E' -> Pr E <= Pr E'.
Proof.
move=> H; apply ler_rsum_l => a Ha //; [exact/leRR | move/subsetP : H; exact].
Qed.

Lemma Pr_union E1 E2 : Pr (E1 :|: E2) <= Pr E1 + Pr E2.
Proof.
rewrite /Pr.
rewrite (_ : \sum_(i in A | [pred x in E1 :|: E2] i) P i =
  \sum_(i in A | [predU E1 & E2] i) P i); last first.
  apply eq_bigl => x /=; by rewrite inE.
rewrite (_ : \sum_(i in A | [pred x in E1] i) P i =
  \sum_(i in A | pred_of_set E1 i) P i); last first.
  apply eq_bigl => x /=; by rewrite unfold_in.
rewrite (_ : \sum_(i in A | [pred x in E2] i) P i =
  \sum_(i in A | pred_of_set E2 i) P i); last first.
  apply eq_bigl => x /=; by rewrite unfold_in.
exact/ler_rsum_predU.
Qed.

Lemma Pr_bigcup (B : finType) (p : pred B) F :
  Pr (\bigcup_(i | p i) F i) <= \sum_(i | p i) Pr (F i).
Proof.
rewrite /Pr.
elim: (index_enum _) => [| h t IH].
  rewrite big_nil; apply: rsumr_ge0 => b _; rewrite big_nil; exact/leRR.
rewrite big_cons.
case: ifP => H1.
  apply: leR_trans; first by eapply leR_add2l; exact: IH.
  rewrite [X in _ <= X](exchange_big_dep
    (fun h => (h \in A) && [pred x in \bigcup_(i | p i) F i] h)) /=; last first.
    move=> b a Ea jFi; apply/bigcupP; by exists b.
  rewrite big_cons /= H1 big_const iter_addR -exchange_big_dep /=; last first.
    move=> b a Ea iFj; apply/bigcupP; by exists b.
  apply/leR_add2r.
  rewrite -{1}(mul1R (P h)); apply: (@leR_wpmul2r (P h)) => //.
  rewrite (_ : 1 = 1%:R) //; apply/le_INR/leP/card_gt0P.
  case/bigcupP : H1 => b Eb hFb; exists b; by rewrite -topredE /= Eb.
apply/(leR_trans IH)/ler_rsum => b Eb.
rewrite big_cons.
case: ifPn => hFb; last exact/leRR.
rewrite -[X in X <= _]add0R; exact/leR_add2r.
Qed.

Lemma Pr_union_disj E1 E2 : [disjoint E1 & E2] -> Pr (E1 :|: E2) = Pr E1 + Pr E2.
Proof. move=> ?; rewrite -bigU //=; apply eq_bigl => a; by rewrite inE. Qed.

Let Pr_big_union_disj n (F : 'I_n -> {set A}) :
  (forall i j, i != j -> [disjoint F i & F j]) ->
  Pr (\bigcup_(i < n) F i) = \sum_(i < n) Pr (F i).
Proof.
elim: n F => [F H|n IH F H]; first by rewrite !big_ord0 Pr_set0.
rewrite big_ord_recl /= Pr_union_disj; last first.
  rewrite -setI_eq0 big_distrr /=; apply/eqP/big1 => i _; apply/eqP.
  rewrite setI_eq0; exact: H.
rewrite big_ord_recl IH // => i j ij; by rewrite H.
Qed.

Lemma Boole_eq (I : finType) (F : I -> {set A}) :
  (forall i j, i != j -> [disjoint F i & F j]) ->
  Pr (\bigcup_(i in I) F i) = \sum_(i in I) Pr (F i).
Proof.
move=> H.
rewrite (@reindex_onto _ _ _ _ _ enum_val enum_rank _ F) /=; last first.
  by move=> *; exact: enum_rankK.
rewrite [in RHS](@reindex_onto _ _ _ _ _ enum_val enum_rank) /=; last first.
  by move=> *; exact: enum_rankK.
rewrite (eq_bigl xpredT); last by move=> i; rewrite enum_valK eqxx.
rewrite Pr_big_union_disj; last first.
  move=> i j ij.
  suff : enum_val i != enum_val j by move/H.
  by apply: contra ij => /eqP/enum_val_inj ->.
by rewrite [in RHS](eq_bigl xpredT) // => i; rewrite enum_valK eqxx.
Qed.

Lemma law_of_total_probability (I : finType) (E : {set A}) (F : I -> {set A}) :
  (forall i j, i != j -> [disjoint F i & F j]) ->
  cover [set F i | i in I] = [set: A] ->
  Pr E = \sum_(i in I) Pr (E :&: F i).
Proof.
move=> dis cov; have {1}-> : E = \bigcup_(i in I) (E :&: F i).
  by rewrite cover_imset in cov; rewrite -big_distrr /= cov setIT.
rewrite Boole_eq // => i j /dis; rewrite -2!setI_eq0 -setIIr => /eqP ->.
by rewrite setI0.
Qed.

Lemma Pr_diff E1 E2 : Pr (E1 :\: E2) = Pr E1 - Pr (E1 :&: E2).
Proof. by rewrite /Pr [in RHS](big_setID E2) /= addRC addRK. Qed.

Lemma Pr_union_eq E1 E2 : Pr (E1 :|: E2) = Pr E1 + Pr E2 - Pr (E1 :&: E2).
Proof.
rewrite addRC -addR_opp -addRA addR_opp -Pr_diff -Pr_union_disj -?setU_setUD //.
by rewrite -setI_eq0 setIDA setDIl setDv set0I.
Qed.

Lemma Pr_inter_eq E1 E2 : Pr (E1 :&: E2) = Pr E1 + Pr E2 - Pr (E1 :|: E2).
Proof. by rewrite Pr_union_eq subRBA addRC addRK. Qed.

End probability.
Arguments law_of_total_probability {_} _ {_} _ _.

Lemma Pr_FDistMap (A B : finType) (f : A -> B) (d : fdist A) (E : {set A}) : injective f ->
  Pr d E = Pr (FDistMap.d f d) (f @: E).
Proof.
move=> bf; rewrite /Pr; evar (h : B -> R); rewrite [in RHS](eq_bigr h); last first.
  move=> b bfE; rewrite FDistMap.dE /h; reflexivity.
rewrite {}/h (exchange_big_dep (mem E)) /=; last first.
   by move=> b a /imsetP[a' a'E ->{b} /eqP] /bf ->.
apply eq_bigr => a aE; rewrite (big_pred1 (f a)) // => b /=.
rewrite andb_idl // => /eqP <-{b}; apply/imsetP; by exists a.
Qed.
Arguments Pr_FDistMap [A] [B] [f] [d] [E].

Lemma Pr_domin_fst (A B : finType) (P : {fdist A * B}) a b :
  Pr (Bivar.fst P) a = 0 -> Pr P (setX a b) = 0.
Proof.
move/Pr_set0P => H; apply/Pr_set0P => -[? ?].
by rewrite inE /= => /andP[/H /Bivar.dom_by_fst ->].
Qed.

Lemma Pr_domin_fstN (A B : finType) (P : {fdist A * B}) a b :
  Pr P (setX a b) != 0 -> Pr (Bivar.fst P) a != 0.
Proof. apply/contra => /eqP/Pr_domin_fst => ?; exact/eqP. Qed.

Lemma Pr_domin_snd (A B : finType) (P : {fdist A * B}) a b :
  Pr (Bivar.snd P) b = 0 -> Pr P (setX a b) = 0.
Proof.
move/Pr_set0P => H; apply/Pr_set0P => -[? ?].
by rewrite inE /= => /andP[_ /H /Bivar.dom_by_snd ->].
Qed.

Lemma Pr_domin_sndN (A B : finType) (P : {fdist A * B}) a b :
  Pr P (setX a b) != 0 -> Pr (Bivar.snd P) b != 0.
Proof. apply/contra => /eqP/Pr_domin_snd => ?; exact/eqP. Qed.

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

Section random_variable.

Definition RV {U : finType} (P : fdist U) (A : eqType) := U -> A.

Definition RV_of U (P : fdist U) (A : eqType) :=
  fun (phA : phant (Equality.sort U)) (phT : phant (Equality.sort A)) => RV P A.

Local Notation "{ 'RV' P -> T }" := (RV_of P (Phant _) (Phant T)).

Definition p_of U (P : fdist U) (T : eqType) (X : {RV P -> T}) : fdist U :=
  P.

End random_variable.

Notation "{ 'RV' P -> T }" := (RV_of P (Phant _) (Phant T)) : proba_scope.
Notation "`p_ X" := (p_of X) : proba_scope.

Definition pr_eq (U : finType) (A : eqType) (P : fdist U) (X : {RV P -> A}) (a : A) :=
  Pr `p_X (X @^-1 a).
Notation "\Pr[ X = a ]" := (pr_eq X a) : proba_scope.

Definition pr_eq_set (U A : finType) (P : fdist U) (X : {RV P -> A}) (E : {set A}) :=
  Pr `p_X (X @^-1: E).
Notation "\Pr[ X '\in' E ]" := (pr_eq_set X E) : proba_scope.

Lemma pr_eq0 (U : finType) (A : eqType) (P : fdist U) (X : {RV (P) -> (A)}) (a : A) :
  a \notin fin_img X -> \Pr[ X = a ] = 0.
Proof.
move=> Xa; rewrite /pr_eq /Pr big1 // => u; rewrite inE => /eqP Xua.
move: Xa; rewrite /fin_img mem_undup.
case/mapP; exists u => //; by rewrite mem_enum.
Qed.

Lemma pr_eq_set1 (U A : finType) (P : fdist U) (X : {RV P -> A}) x :
  \Pr[ X \in [set x] ] = \Pr[ X = x ].
Proof. by apply eq_bigl => i; rewrite !inE. Qed.

(* TODO: move to bigop? *)
Lemma imset_preimset (I J : finType) (h : I -> J) (B : {set J}) :
  B \subset h @: I -> h @: (h @^-1: B) = B.
Proof.
move/subsetP=> B_covered.
apply/setP/subset_eqP/andP. (* or, apply/eqP; rewrite eqEsubset; apply/andP. *)
split; apply/subsetP => x; first by case/imsetP => i; rewrite inE => H ->.
move=> xB; case/(B_covered x)/imsetP: (xB) => y yI xhy.
by apply/imsetP; exists y => //; rewrite inE -xhy.
Qed.
Section BigOps.
Variables (R : Type) (idx : R).
Variables (op : Monoid.law idx) (aop : Monoid.com_law idx).
Variables I J : finType.
Implicit Type A B : {set I}.
Implicit Type h : I -> J.
Implicit Type P : pred I.
Implicit Type F : I -> R.
Lemma partition_big_preimset h (B : {set J}) F :
  \big[aop/idx]_(i in h @^-1: B) F i =
     \big[aop/idx]_(j in B) \big[aop/idx]_(i in I | h i == j) F i.
Proof.
have HA : [disjoint B :&: [set h x | x in I] & B :\: [set h x | x in I]]
    by rewrite -setI_eq0 -setIA setIDA [in _ :&: B]setIC -setIDA setDv !setI0.
have Hha : [disjoint h @^-1: (B :&: [set h x | x in I])
                             & h @^-1: (B :\: [set h x | x in I])].
  rewrite -setI_eq0 -preimsetI.
  suff // : [disjoint B :&: [set h x | x in I] & B :\: [set h x | x in I]]
    by rewrite -setI_eq0; move/eqP => ->; rewrite preimset0.
rewrite -(setID B (h @: I)) /= preimsetU.
evar (p : pred I); rewrite (eq_bigl p); last first.
  move=> i; rewrite in_setU /p; reflexivity.
rewrite {}/p bigU //.
evar (p : pred J); rewrite (eq_bigl p); last first.
  move=> j; rewrite in_setU /p; reflexivity.
rewrite {}/p bigU //.
have -> : h @^-1: (B :\: [set h x | x in I]) = set0.
  apply/setP/subset_eqP/andP; rewrite sub0set; split => //.
  apply/subsetP=> i; rewrite !inE; case/andP.
  move/imsetP=> H _; elimtype False; apply H.
    by exists i; rewrite ?inE.
rewrite big_set0 Monoid.mulm1.
have -> : \big[aop/idx]_(x in B :\: [set h x | x in I])
           \big[aop/idx]_(i | h i == x) F i
          = \big[aop/idx]_(x in B :\: [set h x | x in I])
             idx.
  apply eq_bigr => j.
  rewrite inE; case/andP => Hj Hj'.
  apply big_pred0 => i.
  apply/negP => /eqP hij.
  move: Hj; rewrite -hij.
  move/imsetP; apply.
  by exists i.
rewrite big1_eq Monoid.mulm1.
 set B' := B :&: [set h x | x in I].
set A := h @^-1: B'.
have -> : B' = h @: A by rewrite imset_preimset //; apply subsetIr.
have Hright : forall j, j \in h @: A -> \big[aop/idx]_(i in I | h i == j) F i = \big[aop/idx]_(i in A | h i == j) F i.
  move=> j Hj; apply eq_bigl => i; apply andb_id2r; move/eqP => hij.
  move: Hj; rewrite -hij !inE.
  case/imsetP => x; rewrite /A /B' !inE => /andP [H H0] ->.
  by rewrite H H0.
rewrite [in RHS](eq_bigr _ Hright).
by apply: partition_big_imset.
Qed.
End BigOps.

(* special case where the codomain is a fintype *)
Module RVar.
Section def.
Variables (U A : finType) (P : fdist U) (X : {RV P -> A}).
Definition d : {fdist A} := FDistMap.d X P.
Lemma dE a : d a = \Pr[ X = a ].
Proof.
rewrite /d FDistMap.dE /pr_eq /Pr; apply eq_bigl => i; apply/andP/idP.
by case=> _ /eqP Xia; rewrite inE Xia.
by rewrite inE => /eqP ->.
Qed.
Lemma Pr_set (E : {set A}) : Pr d E = \Pr[ X \in E ].
Proof.
rewrite /pr_eq_set /Pr partition_big_preimset /=.
have -> : \sum_(a in E) d a = \sum_(a in E) \Pr[ X = a ]
  by apply eq_bigr => *; exact: dE.
apply eq_bigr => j jE.
rewrite /pr_eq /Pr.
apply eq_bigl => i.
by rewrite inE.
Qed.
Lemma Pr a : Pr d [set a] = \Pr[ X = a ].
Proof. by rewrite -dE Pr_set1. Qed.
End def.
End RVar.

Section random_variables.

Variables (U : finType) (P : fdist U).

Definition const_RV (T : eqType) cst : {RV P -> T} := fun=> cst.
Definition comp_RV (TA TB : eqType) (X : {RV P -> TA}) (f : TA -> TB) : {RV P -> TB} :=
  fun x => f (X x).
Definition scale_RV k (X : {RV P -> R}) : {RV P -> R} := fun x => k * X x.
Definition add_RV (X Y : {RV P -> R}) : {RV P -> R} := fun x => X x + Y x.
Definition sub_RV (X Y : {RV P -> R}) : {RV P -> R} := fun x => X x - Y x.
Definition trans_add_RV (X : {RV P -> R}) m : {RV P -> R} := fun x => X x + m.
Definition trans_min_RV (X : {RV P -> R}) m : {RV P -> R} := fun x => X x - m.
Definition sq_RV (X : {RV P -> R}) : {RV P -> R} := comp_RV X (fun x => x ^ 2).
Definition mlog_RV : {RV P -> R} := fun x => - log (P x).

End random_variables.

Notation "k `cst* X" := (scale_RV k X) : proba_scope.
Notation "X '`/' n" := (scale_RV (1 / INR n) X) : proba_scope.
Notation "X `+ Y" := (add_RV X Y) : proba_scope.
Notation "X `- Y" := (sub_RV X Y) : proba_scope.
Notation "X '`+cst' m" := (trans_add_RV X m) : proba_scope.
Notation "X '`-cst' m" := (trans_min_RV X m) : proba_scope.
Notation "X '`^2' " := (sq_RV X) : proba_scope.
Notation "'--log' P" := (mlog_RV P) : proba_scope.

Local Open Scope vec_ext_scope.

Definition cast_RV_tupledist1 U (P : fdist U) (T : eqType) (X : {RV P -> T}) : {RV (P `^ 1) -> T} :=
  fun x => X (x ``_ ord0).

Definition cast_rV1_RV_tupledist1 U (P : fdist U) (T : eqType) (Xs : 'rV[{RV P -> T}]_1) : {RV (P `^ 1) -> T} :=
  cast_RV_tupledist1 (Xs ``_ ord0).

Definition cast_fun_rV1 U (T : eqType) (X : U -> T) : 'rV[U]_1 -> T :=
  fun x => X (x ``_ ord0).

Definition cast_rV1_fun_rV1 U (T : eqType) (Xs : 'rV[U -> T]_1) : 'rV[U]_1 -> T :=
  cast_fun_rV1 (Xs ``_ ord0).

Local Close Scope vec_ext_scope.

Section expected_value_def.
Variables (U : finType) (P : fdist U) (X : {RV P -> R}).

Definition Ex := \sum_(u in U) X u * `p_X u.

Lemma Ex_ge0 : (forall u, 0 <= X u) -> 0 <= Ex.
Proof. move=> H; apply: rsumr_ge0 => u _; apply mulR_ge0 => //; exact/H. Qed.

End expected_value_def.
Arguments Ex {U} _ _.

Notation "'`E_'" := (@Ex _) : proba_scope.
Notation "'`E'" := (@Ex _ _) : proba_scope.

(* Alternative definition of the expected value: *)
Section Ex_alt.
Variables (U : finType) (P : fdist U) (X : {RV P -> R}).

Definition Ex_alt := \sum_(r <- fin_img X) r * \Pr[ X = r ].

Lemma Ex_altE : Ex_alt = `E X.
Proof.
rewrite /Ex.
transitivity (\sum_(r <- fin_img X) \sum_(u in U | X u == r) (X u * `p_X u)).
  apply eq_bigr => /= r _.
  rewrite /Pr big_distrr /=; apply congr_big => //= a.
  by rewrite inE.
  by rewrite inE => /eqP ->.
by rewrite -sum_parti_finType.
Qed.

End Ex_alt.

Section expected_value_prop.

Variables (U : finType) (P : fdist U) (X Y : {RV P -> R}).

Lemma E_scale_RV k : `E (k `cst* X) = k * `E X.
Proof.
rewrite /scale_RV {2}/Ex big_distrr /=; apply eq_bigr => a _; by rewrite mulRA.
Qed.

Lemma E_add_RV : `E (X `+ Y) = `E X + `E Y.
Proof. rewrite -big_split; apply eq_bigr => a _ /=; by rewrite -mulRDl. Qed.

Lemma E_sub_RV : `E (X `- Y) = `E X - `E Y.
Proof.
rewrite {3}/Ex -addR_opp (big_morph Ropp oppRD oppR0) -big_split /=.
apply eq_bigr => u _; by rewrite -mulNR -mulRDl.
Qed.

Lemma E_const_RV k : `E (const_RV P k) = k.
Proof. by rewrite /Ex /const_RV /= -big_distrr /= FDist.f1 mulR1. Qed.

Lemma E_trans_add_RV m : `E (X `+cst m) = `E X + m.
Proof.
rewrite /trans_add_RV /=.
transitivity (\sum_(u in U) (X u * `p_X u + m * `p_X u)).
  by apply eq_bigr => u _ /=; rewrite mulRDl.
by rewrite big_split /= -big_distrr /= FDist.f1 mulR1.
Qed.

Lemma E_trans_RV_id_rem m :
  `E ((X `-cst m) `^2) = `E ((X `^2 `- (2 * m `cst* X)) `+cst m ^ 2).
Proof.
apply eq_bigr => a _.
rewrite /sub_RV /trans_add_RV /trans_min_RV /sq_RV /= /comp_RV /scale_RV /= /p_of; field.
Qed.

Lemma E_comp_RV f k : (forall x y, f (x * y) = f x * f y) ->
  `E (comp_RV (k `cst* X) f) = `E ((f k) `cst* (comp_RV X f)).
Proof. move=> H; rewrite /comp_RV /=; apply eq_bigr => u _; by rewrite H. Qed.

Lemma E_comp_RV_ext f : X = Y -> `E (comp_RV X f) = `E (comp_RV Y f).
Proof. move=> H; by rewrite /comp_RV /= H. Qed.

End expected_value_prop.

Lemma E_cast_RV_tuplefdist1 A (P : fdist A) :
  forall (X : {RV P -> R}), `E (cast_RV_tupledist1 X) = `E X.
Proof.
move=> f.
rewrite /cast_RV_tupledist1 /=; apply big_rV_1 => // m; by rewrite -TupleFDist.one.
Qed.

Section probability_inclusion_exclusion.
(** This section gathers a proof of the formula of inclusion-exclusion
    contributed by Erik Martin-Dorel: the corresponding theorem is named
    [Pr_bigcup_incl_excl] and is more general than lemma [Pr_bigcup]. *)
Variable A : finType.
Variable P : fdist A.

Lemma bigmul_eq0 (C : finType) (p : pred C) (F : C -> R) :
  (exists2 i : C, p i & F i = R0) <-> \prod_(i : C | p i) F i = R0.
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
  Ind (S1 :&: S2) x = Ind S1 x * Ind S2 x.
Proof. by rewrite /Ind inE; case: in_mem; case: in_mem=>/=; ring. Qed.

Lemma Ind_bigcap I (e : I -> {set A}) (r : seq.seq I) (p : pred I) x :
  Ind (\bigcap_(j <- r | p j) e j) x = \prod_(j <- r | p j) (Ind (e j) x).
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

Notation "'rv' X" := (X : {RV P -> R}) (at level 4).

Lemma E_Ind s : `E (rv (Ind s)) = Pr P s.
Proof.
rewrite /Ex /Ind /Pr (bigID (mem s)) /=.
rewrite [X in _ + X = _]big1; last by move=> i /negbTE ->; rewrite mul0R.
by rewrite addR0; apply: eq_bigr => i ->; rewrite mul1R.
Qed.

Lemma E_ext X2 X1 : X1 =1 X2 -> `E (rv X1) = `E (rv X2).
Proof. by move=> Heq; apply: eq_bigr => i Hi /=; rewrite Heq. Qed.

Lemma E_add X1 X2 : `E (rv (fun w => X1 w + X2 w)) = `E (rv X1) + `E (rv X2).
Proof.
rewrite /Ex.
erewrite eq_bigr. (* to replace later with under *)
  2: by move=> i Hi; rewrite mulRDl.
by rewrite big_split.
Qed.

Lemma E_rsum I r p (X : I -> A -> R) :
  `E (rv (fun x => \sum_(i <- r | p i) X i x)) =
  \sum_(i <- r | p i) (`E (rv (X i))).
Proof.
rewrite /Ex.
erewrite eq_bigr. (* to replace later with under *)
  2: by move=> a Ha; rewrite big_distrl.
by rewrite exchange_big /=; apply: eq_bigr => i Hi.
Qed.

Lemma E_scaler X1 r2 : `E (rv (fun w => X1 w * r2)) = `E (rv X1) * r2.
Proof.
by rewrite big_distrl /=; apply: eq_bigr => i Hi; rewrite mulRAC.
Qed.

Lemma E_scalel r1 X2 : `E (rv (fun w => r1 * X2 w)) = r1 * `E (rv X2).
Proof.
by rewrite big_distrr /=; apply: eq_bigr => i Hi; rewrite mulRA.
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
  (fun i : {ffun I -> bool} => inord #|[set x | i x]|)
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
  \sum_(i in B) x0 = #|B|%:R * x0.
Proof. by rewrite big_const iter_addR. Qed.

Lemma bigmul_constE (x0 : R) (k : nat) : \prod_(i < k) x0 = x0 ^ k.
Proof. by rewrite big_const cardT size_enum_ord iter_mulR. Qed.

Lemma bigmul_card_constE (I : finType) (B : pred I) x0 : \prod_(i in B) x0 = x0 ^ #|B|.
Proof. by rewrite big_const iter_mulR. Qed.

(** [bigmul_m1pow] is the Reals counterpart of lemma [GRing.prodrN] *)
Lemma bigmul_m1pow (I : finType) (p : pred I) (F : I -> R) :
  \prod_(i in p) - F i = (-1) ^ #|p| * \prod_(i in p) F i.
Proof.
rewrite -bigmul_card_constE.
apply: (big_rec3 (fun a b c => a = b * c)).
{ by rewrite mul1R. }
move=> i a b c Hi Habc; rewrite Habc; ring.
Qed.

Let SumIndCap (n : nat) (S : 'I_n -> {set A}) (k : nat) (x : A) :=
  \sum_(J in {set 'I_n} | #|J| == k) (Ind (\bigcap_(j in J) S j) x).

Lemma Ind_bigcup_incl_excl (n : nat) (S : 'I_n -> {set A}) (x : A) :
  Ind (\bigcup_(i < n) S i) x =
  (\sum_(1 <= k < n.+1) (-1) ^ (k - 1) * SumIndCap S k x).
Proof.
case: n S => [|n] S; first by rewrite big_ord0 big_geq // Ind_set0.
set Efull := \bigcup_(i < n.+1) S i.
have Halg : \prod_(i < n.+1) (Ind Efull x - Ind (S i) x) = 0.
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
rewrite -> addR_eq0 in Halg.
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
  \sum_(J in {set 'I_n} | #|J| == k) Pr P (\bigcap_(j in J) S j).

Lemma E_SumIndCap n (S : 'I_n -> {set A}) k :
  `E (rv (SumIndCap S k)) = SumPrCap S k.
Proof.
rewrite /SumIndCap /SumPrCap E_rsum; apply: eq_bigr => i Hi.
by rewrite E_Ind.
Qed.

Theorem Pr_bigcup_incl_excl n (S : 'I_n -> {set A}) :
  Pr P (\bigcup_(i < n) S i) =
  \sum_(1 <= k < n.+1) ((-1)^(k-1) * SumPrCap S k).
Proof.
rewrite -E_Ind /=.
rewrite /Ex.
erewrite eq_bigr. (* to replace later with under *)
  2: by move=> ? _; rewrite /= Ind_bigcup_incl_excl.
simpl.
erewrite eq_bigr. (* to replace later with under *)
  2: by move=> a Ha; rewrite big_distrl.
rewrite exchange_big /=.
apply: eq_bigr => i _.
by rewrite -E_SumIndCap -E_scalel.
Qed.

End probability_inclusion_exclusion.

Section markov_inequality.

Variables (U : finType) (P : {fdist U}) (X : {RV P -> R}).
Hypothesis X_ge0 : forall u, 0 <= X u.

Definition pr_geq (X : {RV P -> R}) r := Pr `p_X [set x | X x >b= r].

Local Notation "'\Pr[' X '>=' r ']'" := (pr_geq X r).

Lemma Ex_lb (r : R) : r * \Pr[ X >= r] <= `E X.
Proof.
rewrite /Ex (bigID [pred a' | X a' >b= r]) /= -[a in a <= _]addR0.
apply leR_add; last first.
  apply rsumr_ge0 => a _; apply mulR_ge0 => //; exact/X_ge0.
apply (@leR_trans (\sum_(i | X i >b= r) r * `p_X i)).
  rewrite big_distrr /=;  apply/Req_le/eq_bigl => a; by rewrite inE.
apply ler_rsum => u Xur; apply/leR_wpmul2r => //; exact/leRP.
Qed.

Lemma markov (r : R) : 0 < r -> \Pr[ X >= r ] <= `E X / r.
Proof. move=> ?; rewrite /Rdiv leR_pdivl_mulr // mulRC; exact/Ex_lb. Qed.

End markov_inequality.

Notation "'Pr[' X '>=' r ']'" := (pr_geq X r) : proba_scope.

Section thm61.
Variables (U : finType) (P : fdist U) (X : {RV P -> R}) (phi : R -> R).
Lemma thm61 : `E (comp_RV X phi) = \sum_(r <- fin_img X) phi r * \Pr[ X = r ].
Proof.
rewrite /Ex.
rewrite (sum_parti_finType _ X (fun u => comp_RV X phi u * `p_ (comp_RV X phi) u)) /=.
apply eq_bigr => a _; rewrite /Pr big_distrr /=; apply eq_big.
by move=> u; rewrite inE.
by move=> u /eqP Xua; rewrite /comp_RV -Xua.
Qed.
End thm61.

Section variance_def.

Variables (U : finType) (P : fdist U) (X : {RV P -> R}).

(* Variance of a random variable (\sigma^2(X) = V(X) = E (X^2) - (E X)^2): *)
Definition Var := let miu := `E X in `E ((X `-cst miu) `^2).

(* Alternative form for computing the variance
   (V(X) = E(X^2) - E(X)^2 \cite[Theorem 6.6]{probook}): *)
Lemma VarE : Var = `E (X `^2)  - (`E X) ^ 2.
Proof.
rewrite /Var E_trans_RV_id_rem E_trans_add_RV E_sub_RV E_scale_RV; field.
Qed.

End variance_def.

Arguments Var {U} _ _.

Notation "'`V'" := (@Var _ _) : proba_scope.
Notation "'`V_' x" := (@Var _ x) : proba_scope.

Section variance_prop.

Variables (U : finType) (P : fdist U) (X : {RV P -> R}).

(* The variance is not linear V (k X) = k^2 V (X) \cite[Theorem 6.7]{probook}: *)
Lemma Var_scale k : `V (k `cst* X) = k ^ 2 * `V X.
Proof.
rewrite {1}/`V [in X in X = _]/= E_scale_RV.
pose Y : {RV P -> R} := k `cst* (X `+cst - `E X).
rewrite (@E_comp_RV_ext _ P ((k `cst* X) `-cst k * `E X) Y) //; last first.
  rewrite boolp.funeqE => /= x.
  rewrite /Y /scale_RV /= /trans_min_RV /trans_add_RV; field.
rewrite E_comp_RV ?E_scale_RV // => *; field.
Qed.

Lemma Var_trans m : `V (X `+cst m) = `V X.
Proof.
rewrite /Var E_trans_add_RV; congr (`E (_ `^2)).
rewrite boolp.funeqE => /= u; rewrite /trans_add_RV /trans_min_RV /=; field.
Qed.

End variance_prop.

Lemma Var_cast_RV_tuplefdist1 (A : finType) (P : fdist A) (X : {RV P -> R}) :
  `V (@cast_RV_tupledist1 _ P _ X) = `V X.
Proof.
rewrite !VarE !E_cast_RV_tuplefdist1; congr (_ - _).
apply: big_rV_1 => // v; by rewrite TupleFDist.one.
Qed.

(* (Probabilistic statement.)
 In any data sample, "nearly all" the values are "close to" the mean value:
 Pr[ |X - E X| \geq \epsilon] \leq V(X) / \epsilon^2 *)
Section chebyshev.

Variables (U : finType) (P : fdist U) (X : {RV P -> R}).

Lemma chebyshev_inequality epsilon : 0 < epsilon ->
  Pr `p_X [set u | `| X u - `E X | >b= epsilon] <= `V X / epsilon ^ 2.
Proof.
move=> He; rewrite leR_pdivl_mulr; last exact/expR_gt0.
rewrite mulRC /Var.
apply (@leR_trans (\sum_(a in U | `| X a - `E X | >b= epsilon)
    (((X `-cst `E X) `^2) a  * `p_X a))); last first.
  apply ler_rsum_l_support with (Q := xpredT) => // a .
  apply mulR_ge0 => //; exact: pow_even_ge0.
rewrite /Pr big_distrr.
rewrite  [_ ^2]lock /= -!lock.
apply ler_rsum_l => u; rewrite ?inE => Hu //=.
- rewrite  -!/(_ ^ 2).
  apply leR_wpmul2r => //.
  apply (@leR_trans ((X u - `E X) ^ 2)); last exact/leRR.
  rewrite -(sqR_norm (X u - `E X)).
  apply/pow_incr; split => //; [exact/ltRW | exact/leRP].
- apply mulR_ge0 => //; exact: pow_even_ge0.
Qed.

End chebyshev.

Section independent_events.

Variables (A : finType) (d : fdist A).

Definition inde_events (E F : {set A}) := Pr d (E :&: F) = Pr d E * Pr d F.

Lemma inde_events_cplt (E F : {set A}) :
  inde_events E F -> inde_events E (~: F).
Proof.
rewrite /inde_events => EF; have : Pr d E = Pr d (E :&: F) + Pr d (E :&: ~:F).
  rewrite (law_of_total_probability d E (fun b => if b then F else ~:F)) /=; last 2 first.
    move=> i j ij; rewrite -setI_eq0.
    by case: ifPn ij => Hi; case: ifPn => //= Hj _; rewrite ?setICr // setIC setICr.
    by rewrite cover_imset big_bool /= setUC setUCr.
  by rewrite big_bool addRC.
by rewrite addRC -subR_eq EF -{1}(mulR1 (Pr d E)) -mulRBr -Pr_of_cplt.
Qed.

End independent_events.

Section conditional_probablity.
Variables (A : finType) (d : {fdist A}).

Definition cPr0 (E F : {set A}) := Pr d (E :&: F) / Pr d F.
Local Notation "`Pr_[ E | F ]" := (cPr0 E F).

Lemma cPr0_ge0 (E F : {set A}) : Pr d F != 0 -> 0 <= `Pr_[E|F].
Proof. move=> F0; apply divR_ge0; [exact: Pr_ge0|by rewrite Pr_gt0]. Qed.

Lemma inde_events_cPr0 (E F : {set A}) : Pr d F != 0 -> inde_events d E F ->
  `Pr_[E | F] = Pr d E.
Proof. by move=> F0 EF; rewrite /cPr0 EF /Rdiv -mulRA mulRV ?mulR1. Qed.

Section bayes.
Variables (I : finType) (E : {set A}) (F : I -> {set A}).
Hypothesis dis : forall i j, i != j -> [disjoint F i & F j].
Hypothesis Fi0 : forall i, Pr d (F i) != 0.
Hypothesis cov : cover [set F i | i in I] = [set: A].

Lemma law_of_total_probability_cond  :
  Pr d E = \sum_(i in I) `Pr_[E | F i] * Pr d (F i).
Proof.
rewrite (law_of_total_probability _ _ _ dis cov); apply eq_bigr; move=> i _.
by rewrite /cPr0 /Rdiv -mulRA ?mulVR // mulR1.
Qed.

Lemma Bayes_theorem : Pr d E != 0 -> forall j,
  `Pr_[F j | E] = `Pr_[E | F j] * Pr d (F j) / \sum_(i in I) `Pr_[E | F i] * Pr d (F i).
Proof.
move=> E0 j.
rewrite /cPr0 {1}setIC {2 3}/Rdiv -!mulRA; congr (_ * _).
by rewrite mulRA mulVR ?mul1R // law_of_total_probability_cond.
Qed.

End bayes.

End conditional_probablity.

Notation "`Pr_ P [ E | F ]" := (cPr0 P E F) : proba_scope.

Module CondFDist.
Section def.
Variables (A : finType) (P : {fdist A}) (B : {set A}).
Hypothesis HB : Pr P B != 0.
Definition f := [ffun a => `Pr_P [[set a] | B]].
Lemma f0 a : 0 <= f a. Proof. by rewrite ffunE; apply cPr0_ge0. Qed.
Lemma f1 : \sum_(a in A) f a = 1.
Proof.
rewrite /f.
under eq_bigr do rewrite ffunE.
rewrite /cPr0 -big_distrl /= -divRE eqR_divr_mulr // mul1R.
rewrite (law_of_total_probability P B (fun i => [set i])); last 2 first.
  move=> i j ij; rewrite -setI_eq0; apply/eqP/setP => // a.
  by rewrite !inE; apply/negbTE; apply: contra ij => /andP[/eqP ->].
  apply/setP => // a; rewrite !inE; apply/bigcupP.
  by exists [set a]; rewrite ?inE //; apply/imsetP; exists a.
by apply eq_bigr => a _; rewrite setIC.
Qed.
Definition d : {fdist A} := locked (FDist.make f0 f1).
End def.
Section prop.
Variables (A : finType) (P : {fdist A}) (B : {set A}).
Hypothesis HB : Pr P B != 0.
Lemma dE a : d HB a = `Pr_P [[set a] | B].
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
End prop.
End CondFDist.

Section k_wise_independence.

Variables (A I : finType) (k : nat) (d : fdist A) (E : I -> {set A}).

Definition kwide_inde := forall (J : {set I}), (#|J| <= k)%nat ->
  Pr d (\bigcap_(i in J) E i) = \prod_(i in J) Pr d (E i).

End k_wise_independence.

Section pairwise_independence.

Variables (A I : finType) (d : fdist A) (E : I -> {set A}).

Definition pairwise_inde := @kwide_inde A I 2%nat d E.

Lemma pairwise_indeE :
  pairwise_inde <-> (forall (i j : I), i != j -> inde_events d (E i) (E j)).
Proof.
split => [pi i j ij|].
  red in pi.
  red in pi.
  have /pi : (#|[set i; j]| <= 2)%nat by rewrite cards2 ij.
  rewrite bigcap_setU !big_set1 => H.
  by rewrite /inde_events H (big_setD1 i) ?inE ?eqxx ?orTb //= setU1K ?inE // big_set1.
move=> H s.
move sn : (#| s |) => n.
case: n sn => [|[|[|//]]].
  by move/eqP; rewrite cards_eq0 => /eqP ->{s} _; rewrite !big_set0 Pr_setT.
  by move/eqP/cards1P => [i ->{s}] _; rewrite !big_set1.
move/eqP; rewrite cards2P => /existsP[a /existsP[b /andP[/eqP ->{s} ab]]] _.
rewrite !bigcap_setU !big_set1 (big_setD1 a) ?inE ?eqxx ?orTb //=.
by rewrite setU1K ?inE // big_set1 H.
Qed.

End pairwise_independence.

Section mutual_independence.

Variables (A I : finType) (d : fdist A) (E : I -> {set A}).

Definition mutual_inde := (forall k, @kwide_inde A I k.+1 d E).

Lemma mutual_indeE :
  mutual_inde <-> (forall J : {set I}, J \subset I ->
    Pr d (\bigcap_(i in J) E i) = \prod_(i in J) Pr d (E i)).
Proof.
rewrite /mutual_inde; split => [H J JI|H k J JI].
  have [/eqP->{J JI}|J0] := boolP (J == set0).
  by rewrite !big_set0 Pr_setT.
  by rewrite (H #|J|.-1) ?prednK // card_gt0.
by rewrite H //; apply/subsetP => i ij; rewrite inE.
Qed.

Lemma mutual_indeE' : #|I| != O -> mutual_inde <-> kwide_inde #|I| d E.
Proof.
move=> I0.
rewrite /mutual_inde; split => [H J JI|].
  have [/eqP->{J JI}|J0] := boolP (J == set0).
  by rewrite !big_set0 Pr_setT.
  by rewrite (H #|J|.-1) ?prednK // card_gt0.
by move=> H k J Jk; rewrite H // max_card.
Qed.

End mutual_independence.

Section independent_random_variables.

Variables (A B : finType) (P : {fdist A * B}).
Variables (TA TB : eqType).
Variables X : A -> TA.
Variables Y : B -> TB.

Local Open Scope vec_ext_scope.

Definition inde_drv := forall (x : TA) (y : TB),
  Pr P [set xy | (X xy.1 == x) && (Y xy.2 == y)] =
  Pr (Bivar.fst P) (X @^-1 x) * Pr (Bivar.snd P) (Y @^-1 y). (* TODO: notations *)

Lemma inde_events_drv : inde_drv <-> (forall x y,
  inde_events P [set xy | X xy.1 == x] [set xy | Y xy.2 == y]).
Proof.
have H1 : forall x, Pr (Bivar.fst P) (X @^-1 x) = Pr P [set xy | X xy.1 == x].
  move=> /= x; rewrite /Pr /=.
  rewrite (eq_bigr (fun a => P (a.1, a.2))); last by case.
  rewrite (eq_bigl (fun ab => (ab.1 \in X @^-1 x) && (xpredT ab.2))); last first.
    by case=> a b; rewrite !inE andbT.
  rewrite -[in RHS](pair_big (mem (X @^-1 x)) xpredT (fun a b => P (a, b))) /=.
  apply eq_bigr => a _; by rewrite Bivar.fstE.
have H2 : forall y, Pr (Bivar.snd P) (Y @^-1 y) = Pr P [set xy | Y xy.2 == y].
  move=> /= y; rewrite /Pr /= (eq_bigr (fun a => P (a.1, a.2))); last by case.
  rewrite (eq_bigl (fun ab => (xpredT ab.1) && (ab.2 \in [set z | Y z == y]))); last first.
    by case=> a b; rewrite !inE.
  rewrite -[in RHS](pair_big xpredT (mem (Y @^-1 y)) (fun a b => P (a, b))) /=.
  by rewrite exchange_big; apply eq_bigr => b _; rewrite Bivar.sndE.
split=> [H /= x y|/= H x y].
- rewrite /inde_events.
  move: (H x y) => {}H.
  rewrite -H1 -H2 -{}H; congr Pr; by apply/setP => /= ab; rewrite !inE.
- rewrite /inde_events in H.
  rewrite (H1 x) (H2 y) -{}H; congr Pr; by apply/setP => /= ab; rewrite !inE.
Qed.

Lemma prod_dist_inde_drv : P = (Bivar.fst P) `x (Bivar.snd P) -> inde_drv.
Proof.
move=> H x y.
rewrite /Pr /= (eq_bigr (fun a => P (a.1, a.2))); last by case.
rewrite (eq_bigl (fun a => (X a.1 == x) && (Y a.2 == y))); last first.
  by case => a b; rewrite !inE.
rewrite -(pair_big [pred a | X a == x] [pred b | Y b == y] (fun a1 a2 => P (a1, a2))) /=.
rewrite big_distrl /=; apply eq_big.
- move=> a; by rewrite inE.
- move=> a fax.
  rewrite big_distrr /=; apply eq_big.
  + by move=> b; rewrite inE.
  + by move=> b _; rewrite {1}H /= ProdFDist.dE.
Qed.

End independent_random_variables.

Notation "P |= X _|_ Y" := (@inde_drv _ _ P _ _ X Y) : proba_scope.

Section sum_two_rand_var_def.

Variables (A : finType) (n : nat).
Variables (X : 'rV[A]_n.+2 -> R) (X1 : A -> R) (X2 : 'rV[A]_n.+1 -> R).

Local Open Scope vec_ext_scope.

Definition sum_2 := X =1 fun x => X1 (x ``_ ord0) + X2 (rbehead x).

End sum_two_rand_var_def.

Notation "Z \= X '@+' Y" := (sum_2 Z X Y) : proba_scope.

Section sum_two_rand_var.

Variables (A : finType) (n : nat) (P : {fdist 'rV[A]_n.+2}) (X : {RV P -> R}).
Variables (X1 : A -> R) (X2 : 'rV[A]_n.+1 -> R).
Let P1 := Multivar.head_of P.
Let P2 := Multivar.tail_of P.

Local Open Scope vec_ext_scope.

Lemma E_sum_2 : X \= X1 @+ X2 -> `E X = `E_P1 X1 + `E_P2 X2.
Proof.
move=> Hsum.
transitivity (\sum_(ta in 'rV[A]_n.+2)
  (X1 (ta ``_ ord0) * `p_X ta + X2 (rbehead ta) * `p_X ta)).
- apply eq_bigr => ta _; by rewrite Hsum mulRDl.
- rewrite big_split => //=; congr (_ + _).
  + transitivity (\sum_(a in A)
      (X1 a * \sum_(ta in 'rV_n.+1) ((Multivar.to_bivar `p_X) (a, ta)))).
    * rewrite -(big_rV_cons_behead _ xpredT xpredT); apply eq_bigr => a _.
      rewrite big_distrr /=; apply eq_bigr => i _.
      by rewrite row_mx_row_ord0 Multivar.to_bivarE.
    * apply eq_bigr => a _; by rewrite Bivar.fstE.
  + transitivity (\sum_(ta in 'rV_n.+1)
      (X2 ta * \sum_(a in A) ((Multivar.to_bivar `p_X) (a, ta)))).
    * rewrite -(big_rV_cons_behead _ xpredT xpredT) exchange_big /=.
      apply eq_bigr => ta _; rewrite big_distrr /=.
      apply eq_bigr => a _; by rewrite rbehead_row_mx Multivar.to_bivarE.
    * apply eq_bigr => ta _; by rewrite Bivar.sndE.
Qed.

Lemma E_id_rem_helper : X \= X1 @+ X2 ->
  Multivar.to_bivar `p_X |= X1 _|_ X2 ->
  \sum_(i in 'rV[A]_n.+2) (X1 (i ``_ ord0) * X2 (rbehead i) * `p_X i) =
    `E_P1 X1 * `E_P2 X2.
Proof.
move=> Hsum Hinde.
rewrite -!Ex_altE.
apply trans_eq with (\sum_(r <- undup (map X1 (enum A)))
   \sum_(r' <- undup (map X2 (enum ('rV[A]_n.+1))))
   ( r * r' * @pr_eq _ _ P1 X1 r * @pr_eq _ _ P2 X2 r')); last first.
  rewrite [in RHS]big_distrl /=.
  apply eq_bigr => i _.
  rewrite big_distrr /=.
  apply eq_bigr => j _.
  by rewrite -!mulRA [in RHS](mulRCA _ j).
rewrite -(big_rV_cons_behead _ xpredT xpredT).
apply trans_eq with (\sum_(a in A) \sum_(j in 'rV[A]_n.+1)
  (X1 a * X2 j * `p_X (row_mx (\row_(k < 1) a) j))).
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
apply trans_eq with (r * r' * \sum_(i0 | X2 i0 == r') \sum_(i1 | X1 i1 == r)
    (`p_X (row_mx (\row_(k < 1) i1) i0))).
  rewrite big_distrr /= /index_enum -!enumT.
  apply eq_bigr => ta ta_r'.
  rewrite big_distrr /=.
  apply eq_bigr => a a_l.
  move/eqP : ta_r' => <-.
  by move/eqP : a_l => <-.
rewrite -[RHS]mulRA; congr (_ * _).
rewrite exchange_big /=.
move: {Hinde}(Hinde r r') => /=.
rewrite -/(Multivar.head_of _) -/(Multivar.tail_of _) -/P1 -/P2 => <-.
rewrite /Pr pair_big /=.
apply eq_big.
- by move=> -[a b] /=; rewrite inE.
- move=> -[a b] /= /andP[ar br']; by rewrite Multivar.to_bivarE.
Qed.

(* Expected Value of the Square (requires mutual independence): *)
Lemma E_id_rem : X \= X1 @+ X2 -> (Multivar.to_bivar `p_X) |= X1 _|_ X2 ->
  `E (X `^2) = `E_P1 (X1 `^2) + 2 * `E_P1 X1 * `E_P2 X2 + `E_P2 (X2 `^2).
Proof.
move=> Hsum Hinde.
rewrite -![in RHS]Ex_altE.
transitivity (\sum_(i in 'rV_n.+2)
  ((X1 (i ``_ ord0) + X2 (rbehead i)) ^ 2%N * `p_X i)).
  apply eq_bigr => i _; rewrite /sq_RV /=.
  by rewrite /comp_RV Hsum.
transitivity (\sum_(i in 'rV_n.+2) ((X1 (i ``_ ord0)) ^ 2 +
    2 * X1 (i ``_ ord0) * X2 (rbehead i) + (X2 (rbehead i)) ^ 2) * `p_X i).
  apply eq_bigr => ? _; by rewrite sqrRD.
transitivity (\sum_(i in 'rV_n.+2) ((X1 (i ``_ ord0)) ^ 2 * `p_X i + 2 *
  X1 (i ``_ ord0) * X2 (rbehead i) * `p_X i + (X2 (rbehead i)) ^ 2 * `p_X i)).
  apply eq_bigr => ? ?; by field.
rewrite !big_split /=; congr (_ + _ + _).
- rewrite Ex_altE -(big_rV_cons_behead _ xpredT xpredT) /=.
  apply eq_bigr => i _.
  transitivity (X1 i ^ 2 * \sum_(j in 'rV_n.+1) (Multivar.to_bivar `p_ X) (i, j)).
  + rewrite big_distrr /=; apply eq_bigr => i0 _.
    by rewrite row_mx_row_ord0 Multivar.to_bivarE.
  + congr (_ * _); by rewrite Bivar.fstE.
- rewrite -mulRA.
  rewrite !Ex_altE.
  rewrite -E_id_rem_helper // big_distrr /=.
  apply eq_bigr => i _; field.
- rewrite Ex_altE -(big_rV_cons_behead _ xpredT xpredT) exchange_big /=.
  apply eq_bigr => t _.
  transitivity (X2 t ^ 2 * \sum_(i in A) (Multivar.to_bivar `p_ X) (i, t)).
  + rewrite big_distrr /=; apply eq_bigr => i _.
    by rewrite rbehead_row_mx Multivar.to_bivarE.
  + congr (_ * _); by rewrite Bivar.sndE.
Qed.

Lemma V_sum_2 : X \= X1 @+ X2 -> (Multivar.to_bivar `p_X) |= X1 _|_ X2  ->
  `V X = `V_P1 X1 + `V_P2 X2.
Proof.
move=> H ?; rewrite !VarE E_id_rem // (E_sum_2 H) sqrRD.
rewrite /Ex /= /p_of /= -/P1 -/P2; field.
Qed.

End sum_two_rand_var.

Section expected_value_of_the_product.

Section thm64.
Variables (A B : finType) (X : A -> R) (Y : B -> R).
Variables (P : {fdist A * B}).
Let P1 := Bivar.fst P.
Let P2 := Bivar.snd P.

Lemma E_prod_2 : P |= X _|_ Y -> `E_P (fun ab => X ab.1 * Y ab.2) = `E_P1 X * `E_P2 Y.
Proof.
move=> Hinde.
transitivity (\sum_(x <- fin_img X)
                \sum_(y <- fin_img Y)
                   x * y * Pr P [set ab | (X ab.1 == x) && (Y ab.2 == y)]).
  rewrite /Ex /= (eq_bigr (fun u => X u.1 * Y u.2 * P (u.1, u.2))); last by case.
  rewrite -(pair_bigA _ (fun u1 u2 => X u1 * Y u2 * `p_ (fun ab : A * B => X ab.1 * Y ab.2) (u1, u2))) /=.
  rewrite (sum_parti_finType _ X) /=; apply eq_bigr => x _.
  rewrite exchange_big /= (sum_parti_finType _ Y) /=; apply eq_bigr => y _.
  rewrite /Pr big_distrr /= exchange_big pair_big /=.
  apply eq_big.
  by move=> -[a b] /=; rewrite inE.
  by case=> a b /= /andP[/eqP -> /eqP ->].
transitivity (\sum_(x <- fin_img X) \sum_(y <- fin_img Y) x * y * Pr P1 (X @^-1 x) * Pr P2 (Y @^-1 y)).
  apply eq_bigr => x _; apply eq_bigr => y _; by rewrite Hinde !mulRA.
rewrite -!Ex_altE.
rewrite /Ex_alt big_distrl; apply eq_bigr => x _ /=; rewrite big_distrr /=.
apply eq_bigr=> y _; rewrite -!mulRA; congr (_ * _); by rewrite mulRCA.
Qed.

End thm64.

End expected_value_of_the_product.

Section sum_n_rand_var_def.

Variable A : finType.

Inductive sum_n : forall n, ('rV[A]_n -> R) -> 'rV[A -> R]_n -> Prop :=
| sum_n_1 : forall X, sum_n (cast_rV1_fun_rV1 X) X
| sum_n_cons : forall n (Xs : 'rV_n.+1) Y X Z,
  Y \=sum Xs -> Z \= X @+ Y -> Z \=sum (row_mx (\row_(k < 1) X) Xs)
where "X '\=sum' Xs" := (sum_n X Xs) : proba_scope.

End sum_n_rand_var_def.

Notation "X '\=sum' Xs" := (sum_n X Xs) : proba_scope.

Section sum_n_rand_var.

Variable A : finType.

Local Open Scope vec_ext_scope.

Lemma E_sum_n (P : fdist A) : forall n (Xs : 'rV[A -> R]_n) X,
  X \=sum Xs -> `E_(P `^ n) X = \sum_(i < n) `E_P (Xs ``_ i).
Proof.
elim => [Xs Xbar | [_ Xs Xbar | n IHn Xs Xbar] ].
- by inversion 1.
- inversion 1; subst.
  apply Eqdep_dec.inj_pair2_eq_dec in H0; last exact eq_nat_dec.
  apply Eqdep_dec.inj_pair2_eq_dec in H1; last exact eq_nat_dec.
  subst Xs Xbar.
  by rewrite big_ord_recl big_ord0 addR0 E_cast_RV_tuplefdist1.
- inversion 1; subst.
  apply Eqdep_dec.inj_pair2_eq_dec in H1; last exact eq_nat_dec.
  apply Eqdep_dec.inj_pair2_eq_dec in H2; last exact eq_nat_dec.
  subst Z Xs.
  rewrite big_ord_recl.
  rewrite [X in _ = _ + X](_ : _ = \sum_(i < n.+1) `E_P (Xs0 ``_ i)); last first.
    apply eq_bigr => i _ /=.
    apply eq_bigr => a _ /=.
    rewrite (_ : lift _ _ = rshift 1 i); last exact: val_inj.
    by rewrite (@row_mxEr _ _ 1).
  rewrite -(IHn _ _ H3) (E_sum_2 H4) row_mx_row_ord0.
  by rewrite /Ex /p_of TupleFDist.head_of TupleFDist.tail_of.
Qed.

Lemma V_sum_n (P : fdist A) : forall n (X : 'rV[A]_n -> R) (Xs : 'rV[A -> R]_n),
  X \=sum Xs ->
  forall sigma2, (forall i, `V_P (Xs ``_ i) = sigma2) ->
  `V_(P `^ n) X = INR n * sigma2.
Proof.
elim.
  move=> X Xs X_Xs sigma2 Hsigma2.
  by inversion X_Xs.
case=> [_ | n IH] Xsum Xs Hsum s Hs.
- inversion Hsum.
  apply Eqdep_dec.inj_pair2_eq_dec in H; last exact eq_nat_dec.
  apply Eqdep_dec.inj_pair2_eq_dec in H0; last exact eq_nat_dec.
  subst Xs Xsum.
  by rewrite Var_cast_RV_tuplefdist1 mul1R.
- move: Hsum; inversion 1.
  apply Eqdep_dec.inj_pair2_eq_dec in H0; last exact eq_nat_dec.
  apply Eqdep_dec.inj_pair2_eq_dec in H1; last exact eq_nat_dec.
  subst Z n0 Xs.
  move: {IH}(IH Y _ H2) => IH.
  rewrite S_INR mulRDl -IH.
  + rewrite mul1R addRC (V_sum_2 H3) //; last first.
      by apply prod_dist_inde_drv; rewrite TupleFDist.to_bivar ProdFDist.fst ProdFDistsnd.
    by rewrite -(Hs ord0) /= row_mx_row_ord0 // TupleFDist.head_of TupleFDist.tail_of.
  + move=> i; rewrite -(Hs (lift ord0 i)).
    congr (`V _).
    rewrite (_ : lift _ _ = rshift 1 i); last exact: val_inj.
    by rewrite (@row_mxEr _ _ 1).
Qed.

Lemma Var_average n (P : fdist A) (X : 'rV[A]_n -> R) Xs (sum_Xs : X \=sum Xs) :
  forall sigma2, (forall i, `V_P (Xs ``_ i) = sigma2) ->
  INR n * `V_(P `^ n) (X `/ n) = sigma2.
Proof.
move=> s Hs.
destruct n.
  by inversion sum_Xs.
rewrite (Var_scale X) // (V_sum_n sum_Xs Hs) //; field; exact/INR_eq0.
Qed.

End sum_n_rand_var.

Section weak_law_of_large_numbers.

Local Open Scope vec_ext_scope.

Variables (A : finType) (P : fdist A) (n : nat).
Variable Xs : 'rV[A -> R]_n.+1.
Variable miu : R.
Hypothesis E_Xs : forall i, `E_P (Xs ``_ i) = miu.
Variable sigma2 : R.
Hypothesis V_Xs : forall i, `V_P (Xs ``_ i) = sigma2.
Variable X : {RV (P `^ n.+1) -> R}.
Variable X_Xs : X \=sum Xs.

Lemma wlln epsilon : 0 < epsilon ->
  Pr `p_X [set t | `| (X `/ n.+1) t - miu | >b= epsilon] <=
    sigma2 / (n.+1%:R * epsilon ^ 2).
Proof.
move=> e0.
rewrite divRM ?INR_eq0 //; last exact/gtR_eqF/expR_gt0.
have <- : `V (X `/ n.+1) = sigma2 / INR n.+1.
  rewrite -(Var_average X_Xs V_Xs) Var_scale //; field; exact/INR_eq0.
have <- : `E (X `/ n.+1) = miu.
  rewrite E_scale_RV (E_sum_n P X_Xs).
  rewrite div1R mulRC eqR_divr_mulr ?INR_eq0' // (eq_bigr (fun=> miu)) //.
  by rewrite big_const /= iter_addR cardE /= size_enum_ord mulRC.
move/leR_trans: (chebyshev_inequality (X `/ n.+1) e0); apply; exact/leRR.
Qed.

End weak_law_of_large_numbers.
