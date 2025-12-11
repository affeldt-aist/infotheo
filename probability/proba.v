(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
Require realType_ext.  (* Remove this line when requiring Rocq >= 9.2 *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup lra.
From mathcomp Require boolp.
From mathcomp Require Import unstable mathcomp_extra functions reals exp.
Require Import ssr_ext ssralg_ext bigop_ext realType_ext realType_ln fdist.

(**md**************************************************************************)
(* # Probabilities over finite distributions                                  *)
(*                                                                            *)
(* This file provides a formalization of finite probabilities using           *)
(* distributions over a finite type (see fsdist.v for finitely-supported      *)
(* distributions).                                                            *)
(*                                                                            *)
(* Selected lemmas:                                                           *)
(* - expected value of a sum of RVs (`E_sum_2`), a.k.a., the ``First          *)
(*   Fundamental Mystery of Probability''                                     *)
(* - variance of a sum (`V_sum_2`)                                            *)
(* - variance of the average for independent RVs (`Var_average`)              *)
(* - union bound/Boole's inequality (`Pr_bigcup`)                             *)
(* - Boole's equality (`Boole_eq`)                                            *)
(* - laws of total probability (`total_prob`, `total_prob_cond`)              *)
(* - Bayes' theorems (`Bayes`, `Bayes_extended`)                              *)
(* - an algebraic proof (by Erik Martin-Dorel) of the formula of              *)
(*   inclusion-exclusion (`Pr_bigcup_incl_excl`)                              *)
(* - reasoning by cases (`reasoning_by_cases`, `creasoning_by_cases`)         *)
(* - Markov' inequality (`markov`)                                            *)
(* - Chebyshev's inequality (`chebyshev_inequality`)                          *)
(* - weak law of large numbers (`wlln`)                                       *)
(*                                                                            *)
(* ```                                                                        *)
(*                E `*T == the set of pairs (x, y) with x in E                *)
(*                T`* F == the set of pairs (x, y) with y in F                *)
(*               Pr d E == probability of event E over the distribution d     *)
(*          {RV P -> T} == the type of random variables over an ambient       *)
(*                         distribution P where T is an eqType;               *)
(*                         carries pointwise algebraic structures             *)
(*       ambient_dist X == the P in X : {RV P -> T}                           *)
(*         `Pr[ X = a ] == the probability that the random variable X is a    *)
(*                         with a : A : eqType                                *)
(*        `Pr[ X >= r ] == the probability that the random variable X is      *)
(*                         greater or equal to r                              *)
(*        `Pr[ X <= r ] == the probability that the random variable X is less *)
(*                         or equal to r                                      *)
(*       `Pr[ X \in E ] == the probability that the random variable X is in E *)
(*                         (expect finTypes)                                  *)
(*                 `p_X := fdistmap X P with X : {RV P -> A}                  *)
(*           const_RV k == constant RV                                        *)
(*               f `o X == composition of a function and a RV                 *)
(* k `cst* X, X `*cst k == scaling of a RV                                    *)
(* X `+cst m, X `-cst m == translation of a RV                                *)
(*               X `/ n := n%:R^-1 `cst* X                                    *)
(*   `+,`-,`^2,`--,`log == operations on RVs                                  *)
(*     [% X, Y, ..., Z] == successive pairings of RVs                         *)
(* ```                                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(*                 `E X == expected value of the random variable X            *)
(*             Ex_alt X == expected value of an RV (sum in fin_img X)         *)
(*         `E_[ X | F ] == conditional expectation of X given an event F      *)
(*              Ind s a == indicator function (s : {set A}, a : A)            *)
(*                 `V X == the variance of the random variable X              *)
(*      inde_events E F == E and F are independent events                     *)
(*         kwise_inde E == k-wise independence of the family of events E      *)
(*      pairwise_inde E == pairwise independence of the family of events E    *)
(*        mutual_inde E == mutual independence of the family of events E      *)
(*      `Pr_P [ A | B ] == conditional probability for events                 *)
(*        fdist_cond E0 == distribution P conditioned by E with               *)
(*                         E : Pr P E != 0                                    *)
(*   cinde_events E F G == E and F are conditionally independent events       *)
(*                         given an event G                                   *)
(*         P |= X _|_ Y == X and Y are independent                            *)
(*                         The corresponding identifier is inde_RV            *)
(*          X _|_ Y | Z == X and Y are conditionally independent given Z      *)
(*                         The corresponding identifier is cinde_RV           *)
(* `Pr[ X = a | Y = b ] == conditional probability for random variables       *)
(* `Pr[ X \in E | Y \in F ] == conditional probability for random variables   *)
(*  P |= X _|_ Y | Z, X _|_  Y | Z == the RVs X and Y  are conditionally      *)
(*                         independent given a RV Z (in a distribution P)     *)
(*         P |= X _|_ Y == unconditional independence                         *)
(*          Z \= X @+ Y == Z is the sum of two random variables               *)
(*           X \=sum Xs == X is the sum of the n>=1 independent and           *)
(*                         identically distributed random variables Xs        *)
(* ```                                                                        *)
(******************************************************************************)

Reserved Notation "E `*T" (at level 40).
Reserved Notation "T`* F" (at level 40).
Reserved Notation "{ 'RV' d -> T }" (at level 0, d, T at level 1,
  format "{ 'RV'  d  ->  T }").
Reserved Notation "`p_ X" (at level 5).
Reserved Notation "`Pr[ X = a ]" (at level 0, X, a at next level,
  format "`Pr[  X  =  a  ]").
Reserved Notation "`Pr[ X '\in' E ]" (at level 0, X, E at next level,
  format "`Pr[  X  '\in'  E  ]").
Reserved Notation "`Pr[ X >= r ]" (at level 0, X, r at next level,
  format "`Pr[  X  >=  r  ]").
Reserved Notation "`Pr[ X <= r ]" (at level 0, X, r at next level,
  format "`Pr[  X  <=  r  ]").
Reserved Notation "k `cst* X" (at level 49).
Reserved Notation "X `*cst k" (at level 49).
Reserved Notation "k `*: X" (at level 49).
Reserved Notation "f `o X" (at level 50, format "f  `o '/ '  X").
Reserved Notation "X '`/' n" (at level 49, format "X  '`/'  n").
Reserved Notation "X `+ Y" (at level 50).
Reserved Notation "X `- Y" (at level 50).
Reserved Notation "X '`+cst' m" (at level 50).
Reserved Notation "X '`-cst' m" (at level 50).
Reserved Notation "X '`^2' " (at level 49).
Reserved Notation "'`--' P" (at level 5).
Reserved Notation "'`log' P" (at level 5).
Reserved Notation "'[%' x , y , .. , z ']'" (at level 0,
  format "[%  x ,  y ,  .. ,  z ]").
Reserved Notation "X '\=sum' Xs" (at level 50).
Reserved Notation "'`E'" (at level 0).
Reserved Notation "'`V'" (at level 0).
Reserved Notation "`Pr_ P [ A | B ]" (at level 6, P, A, B at next level,
  format "`Pr_ P [ A  |  B ]").
Reserved Notation "`Pr_[ A | B ]" (at level 6, A, B at next level,
  format "`Pr_[ A  |  B ]").
Reserved Notation "`E_[ X | B ]" (at level 6, X, B at next level,
  format "`E_[ X  |  B ]").
Reserved Notation "`Pr[ X = a | Y = b ]" (at level 0, X, Y, a, b at next level,
  format "`Pr[  X  =  a  |  Y  =  b  ]").
Reserved Notation "`Pr[ X '\in' E | Y '\in' F ]" (at level 0, X, Y, E, F at next level,
  format "`Pr[  X  '\in'  E  |  Y  '\in'  F  ]").
Reserved Notation "`Pr[ X '\in' E | Y = F ]" (at level 0, X, Y, E, F at next level,
  format "`Pr[  X  '\in'  E  |  Y  =  F  ]").
Reserved Notation "`Pr[ X = E | Y '\in' F ]" (at level 0, X, Y, E, F at next level,
  format "`Pr[  X  =  E  |  Y  '\in'  F  ]").
Reserved Notation "X _|_  Y | Z" (at level 50, Y, Z at next level).
Reserved Notation "P |= X _|_  Y | Z" (at level 50, X, Y, Z at next level).
Reserved Notation "P |= X _|_ Y" (at level 50, X, Y at next level,
  format "P  |=  X  _|_  Y").
Reserved Notation "Z \= X '@+' Y" (at level 50).

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Delimit Scope set_scope with set.
Delimit Scope proba_scope with proba.

Import Order.POrderTheory GRing.Theory Num.Theory.

(* NB: to get rid of ^o in R^o *)
From mathcomp Require Import normedtype.
Import numFieldNormedType.Exports.

(* TODO: mv *)
Lemma m1powD {R : pzRingType} k :
  k <> 0%nat -> (-1) ^+ (k-1) = - (-1) ^+ k :> R.
Proof. by case: k => [//|k _]; rewrite subn1 /= exprS mulN1r opprK. Qed.

Notation "E `*T" := ([set x | x.1 \in E]) : proba_scope.
Notation "T`* F" := ([set x | x.2 \in F]) : proba_scope.

Section TsetT.
Context {R : realType}.

Variables (A B : finType) (P : R.-fdist (A * B)).
Implicit Types (E : {set A}) (F : {set B}).

Lemma TsetT : T`* setT = setT :> {set A * B}.
Proof. by apply/setP => -[a b]; rewrite !inE. Qed.

Lemma setTT : setT `*T = setT :> {set A * B}.
Proof. by apply/setP => -[a b]; rewrite !inE. Qed.

Lemma EsetT E : E `*T = E `* setT :> {set A * B}.
Proof. by apply/setP => -[a b]; rewrite !inE andbT. Qed.

Lemma setTE F : T`* F = setT `* F :> {set A * B}.
Proof. by apply/setP => -[a b]; rewrite !inE. Qed.

Lemma Tset0 : T`* set0 = set0 :> {set A * B}.
Proof. by apply/setP => -[a b]; rewrite !inE. Qed.

Lemma set0T : set0 `*T = set0 :> {set A * B}.
Proof. by apply/setP => -[a b]; rewrite !inE. Qed.

Lemma DsetT E1 E2 : (E1 :\: E2) `*T = (E1 `*T) :\: (E2 `*T) :> {set A * B}.
Proof. by apply/setP => -[a b]; rewrite !inE. Qed.

Lemma UsetT E1 E2 : (E1 :|: E2) `*T = (E1 `*T) :|: (E2 `*T) :> {set A * B}.
Proof. by apply/setP => -[a b]; rewrite !inE. Qed.

Lemma IsetT E1 E2 : (E1 :&: E2) `*T = (E1 `*T) :&: (E2 `*T) :> {set A * B}.
Proof. by apply/setP => -[a b]; rewrite !inE. Qed.

End TsetT.

Section probability.
Context {R : realType}.

Variables (A : finType) (P : R.-fdist A).
Implicit Types E : {set A}.

Definition Pr E := \sum_(a in E) P a.

Lemma Pr_ge0 E : 0 <= Pr E. Proof. exact/sumr_ge0. Qed.
Local Hint Resolve Pr_ge0 : core.

Lemma lt0Pr E : (0 < Pr E) = (Pr E != 0).
Proof. by rewrite lt_neqAle Pr_ge0 andbT eq_sym. Qed.

Lemma Pr_le1 E : Pr E <= 1.
Proof. by rewrite -(FDist.f1 P) /Pr; exact/ler_suml. Qed.

Lemma ltPr1 E : (Pr E < 1) = (Pr E != 1).
Proof. by rewrite lt_neqAle Pr_le1 andbT. Qed.

Lemma Pr_set0 : Pr set0 = 0.
Proof. by rewrite /Pr big_pred0 // => a; rewrite in_set0. Qed.

Lemma Pr_set0P E : Pr E = 0 <-> (forall a, a \in E -> P a = 0).
Proof.
rewrite /Pr (eq_bigl (fun x => x \in E)) //; split => [|h].
  move/eqP; rewrite psumr_eq0// => /allP + a aE.
  by move/(_ a); rewrite mem_index_enum aE implyTb => /(_ isT)/eqP.
apply/eqP; rewrite psumr_eq0 //; apply/allP => a _.
by apply/implyP => /h/eqP.
Qed.

Lemma Pr_setT : Pr setT = 1.
Proof. by rewrite /Pr (eq_bigl xpredT) ?FDist.f1 // => a; rewrite in_setT. Qed.

Lemma Pr_set1 a : Pr [set a] = P a.
Proof. by rewrite /Pr big_set1. Qed.

Lemma Pr_cplt E : Pr E + Pr (~: E) = 1.
Proof.
rewrite /Pr -bigU /=; last by rewrite -subsets_disjoint.
by rewrite -(FDist.f1 P); apply: eq_bigl => /= a; rewrite !inE /= orbN.
Qed.

Lemma Pr_to_cplt E : Pr E = 1 - Pr (~: E).
Proof. by rewrite -(Pr_cplt E) addrK. Qed.

Lemma Pr_setC E : Pr (~: E) = 1 - Pr E.
Proof. by rewrite -(Pr_cplt E) addrAC subrr add0r. Qed.

Lemma subset_Pr E E' : E \subset E' -> Pr E <= Pr E'.
Proof.
by move=> H; apply: ler_suml => a aE //; move/subsetP : H; exact.
Qed.

Lemma le_Pr_setU E1 E2 : Pr (E1 :|: E2) <= Pr E1 + Pr E2.
Proof.
rewrite /Pr.
rewrite [X in X <= _](_ : _ = \sum_(i in A | [predU E1 & E2] i) P i); last first.
  by apply: eq_bigl => x /=; rewrite inE.
rewrite [X in _ <= X + _](_ : _ = \sum_(i in A | pred_of_set E1 i) P i); last first.
  by apply: eq_bigl => x /=; rewrite unfold_in.
rewrite [X in _ <= _ + X](_ : _ = \sum_(i in A | pred_of_set E2 i) P i); last first.
  by apply: eq_bigl => x /=; rewrite unfold_in.
exact: ler_sum_predU.
Qed.

Lemma Pr_bigcup (B : finType) (p : pred B) F :
  Pr (\bigcup_(i | p i) F i) <= \sum_(i | p i) Pr (F i).
Proof.
rewrite /Pr; elim: (index_enum _) => [| h t IH].
  by rewrite big_nil; apply/sumr_ge0 => b _; rewrite big_nil.
rewrite big_cons; case: ifP => H1.
  apply: (@le_trans _ _ (P h + \sum_(i | p i) \sum_(a <- t | a \in F i) P a)).
    by rewrite lerD2l.
  rewrite [X in _ <= X](exchange_big_dep
    (fun h => (h \in A) && [pred x in \bigcup_(i | p i) F i] h)) /=; last first.
    by move=> b a Ea jFi; apply/bigcupP; exists b.
  rewrite big_cons /= H1 big_const iter_addr -exchange_big_dep /=; last first.
    by move=> b a Ea iFj; apply/bigcupP; exists b.
  rewrite lerD2r// addr0 -mulr_natl -{1}(mul1r (P h)) ler_wpM2r//.
  rewrite [leLHS](_ : 1 = 1%:R)// ler_nat; apply/card_gt0P.
  by case/bigcupP : H1 => b Eb hFb; exists b; rewrite -topredE /= Eb.
apply/(le_trans IH)/ler_sum => b Eb; rewrite big_cons.
case: ifPn => hFb; last by rewrite lexx.
by rewrite -[X in X <= _]add0r lerD2r.
Qed.

Lemma disjoint_Pr_setU E1 E2 : [disjoint E1 & E2] -> Pr (E1 :|: E2) = Pr E1 + Pr E2.
Proof. by move=> ?; rewrite -bigU //=; apply: eq_bigl => a; rewrite inE. Qed.

Let Pr_big_union_disj n (F : 'I_n -> {set A}) :
  (forall i j, i != j -> [disjoint F i & F j]) ->
  Pr (\bigcup_(i < n) F i) = \sum_(i < n) Pr (F i).
Proof.
elim: n F => [|n IH] F H; first by rewrite !big_ord0 Pr_set0.
rewrite big_ord_recl /= disjoint_Pr_setU; last first.
  rewrite -setI_eq0 big_distrr /=; apply/eqP/big1 => i _; apply/eqP.
  by rewrite setI_eq0; exact: H.
by rewrite big_ord_recl IH // => i j ij; rewrite H.
Qed.

Lemma Pr_setD E1 E2 : Pr (E1 :\: E2) = Pr E1 - Pr (E1 :&: E2).
Proof. by rewrite /Pr [in RHS](big_setID E2) //= addrAC subrr add0r. Qed.

Lemma Pr_setU E1 E2 : Pr (E1 :|: E2) = Pr E1 + Pr E2 - Pr (E1 :&: E2).
Proof.
rewrite addrAC -Pr_setD addrC -disjoint_Pr_setU -?setU_setUD//.
by rewrite -setI_eq0 setIDA setDIl setDv set0I.
Qed.

Lemma Pr_setI E1 E2 : Pr (E1 :&: E2) = Pr E1 + Pr E2 - Pr (E1 :|: E2).
Proof. by rewrite Pr_setU opprB addrCA subrr addr0. Qed.

Lemma Boole_eq (I : finType) (F : I -> {set A}) :
  (forall i j, i != j -> [disjoint F i & F j]) ->
  Pr (\bigcup_(i in I) F i) = \sum_(i in I) Pr (F i).
Proof.
move=> H.
rewrite (reindex_onto enum_val enum_rank) /=; last first.
  by move=> *; exact: enum_rankK.
rewrite [in RHS](reindex_onto  enum_val enum_rank) /=; last first.
  by move=> *; exact: enum_rankK.
rewrite (eq_bigl xpredT); last by move=> i; rewrite enum_valK eqxx.
rewrite Pr_big_union_disj; last first.
  move=> i j ij.
  suff : enum_val i != enum_val j by move/H.
  by apply: contra ij => /eqP/enum_val_inj ->.
by rewrite [in RHS](eq_bigl xpredT) // => i; rewrite enum_valK eqxx.
Qed.

Lemma total_prob (I : finType) (E : {set A}) (F : I -> {set A}) :
  (forall i j, i != j -> [disjoint F i & F j]) ->
  cover (F @: I) = [set: A] ->
  Pr E = \sum_(i in I) Pr (E :&: F i).
Proof.
move=> dis cov; have {1}-> : E = \bigcup_(i in I) (E :&: F i).
  by rewrite cover_imset in cov; rewrite -big_distrr /= cov setIT.
rewrite Boole_eq // => i j /dis; rewrite -2!setI_eq0 -setIIr => /eqP ->.
by rewrite setI0.
Qed.

End probability.
Arguments total_prob {_} _ {_} _ _.
Global Hint Resolve Pr_ge0 : core.
#[deprecated(since="infotheo 0.7.2", note="renamed to `Pr_setC`")]
Notation Pr_of_cplt := Pr_setC(only parsing).
#[deprecated(since="infotheo 0.7.2", note="renamed to `le_Pr_setU`")]
Notation Pr_union := le_Pr_setU (only parsing).
#[deprecated(since="infotheo 0.7.2", note="renamed to `disjoint_Pr_setU`")]
Notation Pr_union_disj := disjoint_Pr_setU (only parsing).
#[deprecated(since="infotheo 0.7.2", note="renamed to `Pr_setD`")]
Notation Pr_diff := Pr_setD (only parsing).
#[deprecated(since="infotheo 0.7.2", note="renamed to `Pr_setU`")]
Notation Pr_union_eq := Pr_setU (only parsing).
#[deprecated(since="infotheo 0.7.2", note="renamed to `Pr_setI`")]
Notation Pr_inter_eq := Pr_setI (only parsing).
#[deprecated(since="infotheo 0.7.2", note="renamed to `subset_Pr`")]
Notation Pr_incl := subset_Pr (only parsing).
#[deprecated(since="infotheo 0.7.2", note="renamed to `Pr_le1`")]
Notation Pr_1 := Pr_le1 (only parsing).
#[deprecated(since="infotheo 0.9.2", note="renamed to `lt0Pr`")]
Notation Pr_gt0P := lt0Pr (only parsing).
#[deprecated(since="infotheo 0.9.2", note="renamed to `ltPr1`")]
Notation Pr_lt1P := ltPr1 (only parsing).

Lemma Pr_domin_setI {R : realType} (A : finType) (d : R.-fdist A) (E F : {set A}) :
  Pr d E = 0 -> Pr d (E :&: F) = 0.
Proof.
move=> PE0; apply/eqP; rewrite psumr_eq0//; apply/allP => a _.
apply/implyP; rewrite inE => /andP[aE aF].
move/eqP : PE0; rewrite psumr_eq0// => /allP.
by move=> /(_ a); rewrite mem_index_enum => /(_ isT); rewrite aE implyTb.
Qed.

Section Pr_extra.
Context {R : realType}.

Variables (A B : finType) (P : R.-fdist (A * B)).
Implicit Types (E : {set A}) (F : {set B}).

Lemma Pr_XsetT E : Pr P (E `* [set: B]) = Pr (P`1) E.
Proof.
rewrite [in RHS]/Pr; under [in RHS]eq_bigr do rewrite fdist_fstE.
rewrite /Pr big_setX /=; apply: eq_bigr => a aE.
by apply: eq_bigl => b; rewrite !inE.
Qed.

Lemma Pr_setTX F : Pr P ([set: A] `* F) = Pr (P`2) F.
Proof.
rewrite /Pr big_setX /= exchange_big; apply: eq_bigr => a aE.
by rewrite fdist_sndE /=; apply: eq_bigl => b; rewrite inE.
Qed.

Lemma PrX_snd F : \sum_(a in A) Pr P ([set a] `* F) = Pr (P`2) F.
Proof.
rewrite -Pr_setTX /Pr big_setX; apply: eq_big => a; first by rewrite !inE.
by rewrite big_setX /= big_set1.
Qed.

Lemma PrX_fst E : \sum_(b in B) Pr P (E `* [set b]) = Pr (P`1) E.
Proof.
rewrite -Pr_XsetT /Pr big_setX /= [in RHS]exchange_big /=; apply: eq_big => b.
  by rewrite !inE.
by move=> _; rewrite big_setX /= exchange_big big_set1.
Qed.

End Pr_extra.

Lemma fst_Pr_domin_setX {R : realType} (A B : finType) (P : R.-fdist (A * B)) E F :
  Pr P`1 E = 0 -> Pr P (E `* F) = 0.
Proof.
move/Pr_set0P => H; apply/Pr_set0P => -[? ?].
by rewrite inE /= => /andP[/H /dom_by_fdist_fst ->].
Qed.
#[deprecated(since="infotheo 0.9.2", note="renamed to `fst_Pr_domin_setX`")]
Notation Pr_domin_setX := fst_Pr_domin_setX (only parsing).

Lemma snd_Pr_domin_setX {R : realType} (A B : finType) (P : R.-fdist (A * B)) E F :
  Pr P`2 F = 0 -> Pr P (E `* F) = 0.
Proof.
move/Pr_set0P => H; apply/Pr_set0P => -[? ?].
by rewrite inE /= => /andP[/[swap] /H /dom_by_fdist_snd].
Qed.

Lemma Pr_domin_setXN {R : realType} (A B : finType) (P : R.-fdist (A * B)) E F :
  Pr P (E `* F) != 0 -> Pr P`1 E != 0.
Proof. by apply/contra => /eqP/fst_Pr_domin_setX => ?; exact/eqP. Qed.

Lemma Pr_fdistmap {R : realType} (A B : finType) (f : A -> B) (d : R.-fdist A)
    (E : {set A}) : injective f ->
  Pr d E = Pr (fdistmap f d) (f @: E).
Proof.
move=> bf; rewrite /Pr.
under [in RHS]eq_bigr do rewrite fdistmapE.
rewrite (exchange_big_dep (mem E)) /=; last first.
  by move=> _ a /imsetP[a' a'E ->]; rewrite 2!inE => /eqP /bf ->.
apply: eq_bigr => a aE; rewrite (big_pred1 (f a)) // => b /=.
by rewrite !inE andb_idl //= => /eqP <-{b}; apply/imsetP; exists a.
Qed.
Arguments Pr_fdistmap {R} [A] [B] [f] [d] [E].

Lemma Pr_fdist_prod {R : realType} (A B : finType) (P1 : R.-fdist A) (P2 : R.-fdist B)
  (E1 : {set A}) (E2 : {set B}) :
  Pr (P1 `x P2) ((E1 `*T) :&: (T`* E2)) = Pr (P1 `x P2) (E1 `*T) * Pr (P1 `x P2) (T`* E2).
Proof.
rewrite {1}/Pr /=.
set P := P1 `x P2.
rewrite (eq_bigr (fun x => P (x.1, x.2))); last by case.
rewrite [in LHS](eq_bigl (fun x => (x.1 \in E1) && (x.2 \in E2))); last first.
  by case=> a b; rewrite !inE.
rewrite -[in LHS](pair_big _ _ (fun x1 x2 => P (x1, x2))) /=.
rewrite {1}/Pr /=.
rewrite (eq_bigr (fun x => P (x.1, x.2))); last by case.
rewrite [in X in _ = X * _](eq_bigl (fun a => a.1 \in E1)); last first.
  by case=> a b; rewrite !inE.
rewrite [in RHS](eq_bigl (fun x => (x.1 \in E1) && true)); last first.
  by case=> a b; rewrite !andbT.
rewrite -[in RHS](pair_big (fun x => x \in E1) xpredT (fun x1 x2 => P (x1, x2))) /=.
rewrite big_distrl /=; apply: eq_big => // a /eqP E1a /=.
rewrite {1}/Pr /=.
rewrite (eq_bigr (fun x => P (x.1, x.2))); last by case.
rewrite [in X in _ = _ * X](eq_bigl (fun a => a.2 \in E2)); last first.
  by move=> b; rewrite !inE.
rewrite [in RHS](eq_bigl (fun x => true && (x.2 \in E2))) //.
rewrite -[in RHS](pair_big xpredT (fun x => x \in E2) (fun x1 x2 => P (x1, x2))) /=.
rewrite exchange_big /= big_distrr /=; apply: eq_big => // b E2b.
rewrite fdist_prodE /=; congr (_ * _); under eq_bigr do rewrite fdist_prodE /=.
  by rewrite -big_distrr /= FDist.f1 mulr1.
by rewrite -big_distrl /= FDist.f1 mul1r.
Qed.

Lemma Pr_fdist_fst {R : realType} (A B : finType) (P : R.-fdist (A * B)) (E : {set A}) :
  Pr P`1 E = Pr P (E `*T).
Proof.
rewrite /Pr (eq_bigr (fun x => P (x.1, x.2))); last by case.
rewrite [in RHS](eq_bigl (fun x => (x.1 \in E) && true)); last first.
  by move=> [a b]; rewrite !inE andbT.
rewrite -[in RHS](pair_big (mem E) xpredT (fun x1 x2 => P (x1, x2))) /=.
by under eq_bigr do rewrite fdist_fstE.
Qed.

Lemma Pr_fdist_snd {R : realType} (A B : finType) (P : R.-fdist (A * B)) (E : {set B}) :
  Pr P`2 E = Pr P (T`* E).
Proof.
rewrite /Pr (eq_bigr (fun x => P (x.1, x.2))); last by case.
rewrite [in RHS](eq_bigl (fun x => true && (x.2 \in E))); last first.
  by move=> [a b]; rewrite !inE.
rewrite -[in RHS](pair_big xpredT (mem E) (fun x1 x2 => P (x1, x2))) /=.
under eq_bigr do rewrite fdist_sndE.
by rewrite exchange_big.
Qed.

Local Open Scope vec_ext_scope.
Lemma Pr_fdist_prod_of_rV {R : realType} (A : finType) n (P : R.-fdist 'rV[A]_n.+1)
    (E : {set A}) (F : {set 'rV[A]_n}) :
  Pr (fdist_prod_of_rV P) (E `* F) =
  Pr P [set x : 'rV[A]_n.+1 | ((x ``_ ord0) \in E) && ((rbehead x) \in F)].
Proof.
rewrite /Pr (eq_bigr (fun x => fdist_prod_of_rV P (x.1, x.2))); last by case.
rewrite [in LHS](eq_bigl (fun a => (a.1 \in E) && (a.2 \in F))); last first.
  by move=> [a b]; rewrite !inE.
rewrite -[in LHS](pair_big (mem E) (mem F) (fun x1 x2 => fdist_prod_of_rV P (x1, x2))) /=.
rewrite [in RHS](eq_bigl (fun x : 'rV_n.+1 => (x ``_ ord0 \in E) && (rbehead x \in F))); last first.
  by move=> v; rewrite !inE.
rewrite -(big_rV_cons_behead _ (mem E) (mem F)) /=.
by apply: eq_bigr => a aE; apply: eq_bigr => v _; rewrite fdist_prod_of_rVE.
Qed.

Lemma Pr_fdist_prod_of_rV1 {R : realType} (A : finType) n (P : R.-fdist 'rV[A]_n.+1) (E : {set A}) :
  Pr (fdist_prod_of_rV P) (E `*T) = Pr P [set x : 'rV[A]_n.+1 | (x ``_ ord0) \in E].
Proof.
by rewrite EsetT Pr_fdist_prod_of_rV; congr Pr; apply/setP => v; rewrite !inE andbT.
Qed.

Lemma Pr_fdist_prod_of_rV2 {R : realType} (A : finType) n (P : R.-fdist 'rV[A]_n.+1) (E : {set 'rV[A]_n}) :
  Pr (fdist_prod_of_rV P) (T`* E) = Pr P [set x : 'rV[A]_n.+1 | (rbehead x) \in E].
Proof.
by rewrite setTE Pr_fdist_prod_of_rV; congr Pr; apply/setP => v; rewrite !inE.
Qed.

Local Close Scope vec_ext_scope.

Section random_variable.
Context {R : realType}.
Variables (U : finType) (T : eqType).

Definition RV (P : R.-fdist U) := U -> T.

Definition RV_of (P : R.-fdist U) :=
  fun (phA : phant (Equality.sort U)) (phT : phant (Equality.sort T)) => RV P.

Local Notation "{ 'RV' P -> V }" := (RV_of P%fdist (Phant _) (Phant V)).

Definition ambient_dist (P : R.-fdist U) (X : {RV P -> T}) : R.-fdist U := P.

HB.instance Definition _ (P : R.-fdist U) := boolp.gen_eqMixin {RV P -> T}.

End random_variable.
Notation "{ 'RV' P -> T }" := (RV_of P%fdist (Phant _) (Phant T)) : proba_scope.

Section random_variable_eqType.
Context {R : realType}.
Variables (U : finType) (A : eqType) (P : R.-fdist U).

Definition pfwd1 (X : {RV P -> A}) (a : A) := locked (Pr P (finset (X @^-1 a))).
Local Notation "`Pr[ X = a ]" := (pfwd1 X a).

Lemma pfwd1E (X : {RV P -> A}) a : `Pr[ X = a ] = Pr P (finset (X @^-1 a)).
Proof. by rewrite /pfwd1; unlock. Qed.

Lemma pfwd1_ge0 (X : {RV P -> A}) (a : A) : 0 <= `Pr[ X = a].
Proof. by rewrite pfwd1E. Qed.

Lemma pfwd1_neq0 (X : {RV P -> A}) (a : A) :
  `Pr[ X = a ] != 0 <-> exists i, i \in X @^-1 a /\ 0 < P i.
Proof.
split; rewrite pfwd1E /Pr => PXa0.
  have H i : 0 <= P i by apply/FDist.ge0.
  have := @psumr_neq0 R U (enum (finset (X @^-1 a))) xpredT _ (fun i _ => H i).
  rewrite big_enum PXa0 => /esym/hasP[i/=].
  by rewrite mem_enum inE/= => Xia Pi_gt0; exists i.
case: PXa0 => i; rewrite inE => ?.
rewrite psumr_neq0//; apply/hasP; exists i => //.
by rewrite inE; exact/andP.
Qed.

Lemma pfwd1_eq0 (X : {RV P -> A}) (a : A) : a \notin fin_img X -> `Pr[ X = a ] = 0.
Proof.
move=> aX; apply/eqP/negPn; apply: contra aX => /pfwd1_neq0 [i [iXa Pi0]].
rewrite mem_undup; apply/mapP; exists i; rewrite ?mem_enum //.
by move: iXa; rewrite inE => /eqP.
Qed.

End random_variable_eqType.
Notation "`Pr[ X = a ]" := (pfwd1 X a) : proba_scope.
#[global] Hint Extern 0 (is_true (0 <= `Pr[ _ = _ ])) =>
  solve [apply: pfwd1_ge0] : core.

Section random_variable_choiceType.
Context {R : realType} {U : finType} {T : choiceType} {P : R.-fdist U}.

HB.instance Definition _ := boolp.gen_choiceMixin {RV P -> T}.

End random_variable_choiceType.

Section random_variable_order.
Context {R : realType}.
Context (U : finType) d (T : porderType d) (P : R.-fdist U).
Variables (X : {RV P -> T}).

Definition pr_geq (X : {RV P -> T}) r := Pr P [set x | (X x >= r)%O ].

Definition pr_leq (X : {RV P -> T}) r := Pr P [set x | (X x <= r)%O ].

End random_variable_order.
Notation "'`Pr[' X '>=' r ']'" := (pr_geq X r) : proba_scope.
Notation "'`Pr[' X '<=' r ']'" := (pr_leq X r) : proba_scope.

(* TODO: move *)
Lemma preimg_set1 {R : realType} (U : finType) (P : R.-fdist U) (A : finType)
    (X : {RV P -> A}) (a : A) :
  X @^-1: [set a] = finset (preim X (pred1 a)).
Proof. by apply/setP => x; rewrite !inE. Qed.

Section random_variable_finType.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (A : finType).

Definition pr_in (X : {RV P -> A}) (E : {set A}) := locked (Pr P (X @^-1: E)).
Local Notation "`Pr[ X '\in' E ]" := (pr_in X E).

Lemma pr_inE (X : {RV P -> A}) (E : {set A}) :
  `Pr[ X \in E ] = Pr P (X @^-1: E).
Proof. by rewrite /pr_in; unlock. Qed.

Definition dist_of_RV (X : {RV P -> A}) : R.-fdist A := fdistmap X P.
Local Notation "`p_ X" := (dist_of_RV X).

Lemma pfwd1EfinType (X : {RV P -> A}) (a : A) :
  `Pr[ X = a ] = Pr P (X @^-1: [set a]).
Proof. by rewrite pfwd1E -preimg_set1. Qed.

Lemma dist_of_RVE (X : {RV P -> A}) (a : A) : `p_X a = `Pr[ X = a ].
Proof.
by rewrite pfwd1EfinType /Pr fdistmapE//; apply: eq_bigl => i; rewrite !inE.
Qed.

Lemma sum_pfwd1 (X : {RV P -> A}) : \sum_a `Pr[ X = a ] = 1.
Proof.
under eq_bigr do rewrite -dist_of_RVE.
by rewrite FDist.f1.
Qed.

Lemma pr_inE' (X : {RV P -> A}) (E : {set A}) : `Pr[ X \in E ] = Pr `p_X E.
Proof.
rewrite pr_inE /Pr partition_big_preimset /=.
by apply: eq_bigr => a aE; rewrite /dist_of_RV fdistmapE.
Qed.

Lemma pr_in1 (X : {RV P -> A}) x : `Pr[ X \in [set x] ] = `Pr[ X = x ].
Proof. by rewrite pr_inE' Pr_set1 -dist_of_RVE. Qed.

End random_variable_finType.
Notation "`Pr[ X '\in' E ]" := (pr_in X E) : proba_scope.
Notation "`p_ X" := (dist_of_RV X) : proba_scope.
#[deprecated(since="infotheo 0.9.2", note="renamed to `pr_in`")]
Notation pr_eq_set := pr_in (only parsing).
#[deprecated(since="infotheo 0.9.2", note="renamed to `pr_inE`")]
Notation pr_eq_setE := pr_inE (only parsing).
#[deprecated(since="infotheo 0.9.2", note="renamed to `pr_in1`")]
Notation pr_eq_set1 := pr_in1 (only parsing).

Section random_variable_basic_constructions.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).

Definition unit_RV : {RV P -> unit} := fun=> tt.
Definition const_RV (T : eqType) : T -> {RV P -> T} := cst.
Definition comp_RV (TA TB : eqType) (f : TA -> TB) (X : {RV P -> TA}) : {RV P -> TB} :=
  fun x => f (X x).

End random_variable_basic_constructions.

Notation "f `o X" := (comp_RV f X).

Section nmod_random_variables.
Context {R : realType} {U : finType} {P : R.-fdist U} {V : nmodType}.
Implicit Types f g h : {RV P -> V}.
Local Open Scope ring_scope.

HB.instance Definition _ :=
  @GRing.isNmodule.Build
    {RV P -> V} 0 +%R (@addrA (U -> V)) (@addrC (U -> V)) (@add0r (U -> V)).

Definition trans_add_RV (X : {RV P -> V}) m : {RV P -> V} := X + const_RV P m.

End nmod_random_variables.

Notation "X `+ Y" := (X + Y) (only parsing) : proba_scope.
Notation "X '`+cst' m" := (trans_add_RV X m) (only parsing) : proba_scope.

Section zmod_random_variables.
Context {R : realType} {U : finType} {P : R.-fdist U} {V : zmodType}.
Local Open Scope ring_scope.

HB.instance Definition _ :=
  @GRing.Nmodule_isZmodule.Build {RV P -> V} -%R (@addNr (U -> V)).

Definition trans_sub_RV (X : {RV P -> V}) m : {RV P -> V} := X - const_RV P m.

Local Notation "X `- Y" := (X - Y) (only parsing) : proba_scope.

Lemma sub_RV_neg (X Y : {RV P -> V}) :
  X `- Y = X `+ - Y.
Proof. by []. Qed.

End zmod_random_variables.

Notation "X `- Y" := (X - Y) (only parsing) : proba_scope.
Notation "X '`-cst' m" := (trans_sub_RV X m) (only parsing) : proba_scope.
Notation "'`--' P" := (- P) (only parsing) : proba_scope.

(* copied from mca master *)
Section pzRing_random_variables.
Context {R : realType} {U : finType} {P : R.-fdist U} {V : pzRingType}.
Implicit Types f g h : {RV P -> V}.
Local Open Scope ring_scope.

Let mulrA : associative (fun f g => f \* g).
Proof. by move=> f g h; rewrite boolp.funeqE=> x /=; rewrite mulrA. Qed.

Let mul1r : left_id (cst 1) (fun f g => f \* g).
Proof. by move=> f; rewrite boolp.funeqE=> x /=; rewrite mul1r. Qed.

Let mulr1 : right_id (cst 1) (fun f g => f \* g).
Proof. by move=> f; rewrite boolp.funeqE=> x /=; rewrite mulr1. Qed.

Let mulrDl : left_distributive (fun f g => f \* g) +%R.
Proof. by move=> f g h; rewrite boolp.funeqE=> x/=; rewrite mulrDl. Qed.

Let mulrDr : right_distributive (fun f g => f \* g) +%R.
Proof. by move=> f g h; rewrite boolp.funeqE=> x/=; rewrite mulrDr. Qed.

HB.instance Definition _ := @GRing.Zmodule_isPzRing.Build {RV P -> V} (cst 1)
  (fun f g => f \* g) mulrA mul1r mulr1 mulrDl mulrDr.

End pzRing_random_variables.

Notation "X `* Y" := (X * Y) (only parsing) : proba_scope.

(* copied from mca master *)
Section comPzRing_random_variables.
Context {R : realType} {U : finType} {P : R.-fdist U} {V : comPzRingType}.
Local Open Scope ring_scope.

Let mulrC : commutative (@GRing.mul {RV P -> V}).
Proof. by move=> f g; rewrite boolp.funeqE => x; rewrite /GRing.mul/= mulrC. Qed.

HB.instance Definition _ :=
  GRing.PzRing_hasCommutativeMul.Build {RV P -> V} mulrC.

End comPzRing_random_variables.

(* copied from mca master *)
Section lmodule_random_variables.
Context {R : realType} {U : finType} {P : R.-fdist U} {K : pzRingType} {V : lmodType K}.

Program Definition RV_lmodMixin := @GRing.Zmodule_isLmodule.Build K {RV P -> V}
  (fun k f => k \*: f) _ _ _ _.
Next Obligation. by move=> k f v; rewrite boolp.funeqE=> x; exact: scalerA. Qed.
Next Obligation. by move=> f; rewrite boolp.funeqE=> x /=; rewrite scale1r. Qed.
Next Obligation.
by move=> f g h; rewrite boolp.funeqE => x /=; rewrite scalerDr.
Qed.
Next Obligation.
by move=> f g h; rewrite boolp.funeqE => x /=; rewrite scalerDl.
Qed.

HB.instance Definition _ := RV_lmodMixin.

End lmodule_random_variables.

(* waiting for a newer version of mathcomp, where pzLalgType will be available*)
(*
Section lalgebra_random_variables.
Context {R : realType} {U : finType} {P : R.-fdist U} {K : pzRingType} {V : pzLalgType K}.
Local Open Scope ring_scope.

Let scalerAl (a : K) (X Y : {RV P -> V}) : a *: (X * Y) = (a *: X) * Y.
Proof. by rewrite boolp.funeqE => x /=; exact: scalerAl. Qed.

Fail Program Definition RV_lalgMixin :=
  GRing.Lmodule_isLalgebra.Build  _ _  scalerAl.

End lalgebra_random_variables.
*)

Section algebraic_constructions_on_random_variables.
Local Open Scope ring_scope.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).

(* this is not a normal scaling, should be renamed like dependent_scale_RV *)
Definition scale_RV (V : lmodType R) (f : U -> R) (X : {RV P -> V}) : {RV P -> V}
  := fun x => f x *: X x.
(* fix scaler_RV / Definition scaler_RV (X : {RV P -> V}) k : {RV P -> V} := fun x => X x * k. *)

End algebraic_constructions_on_random_variables.

Notation "k `cst* X" := (k *: X) (only parsing) : proba_scope.
Notation "X `*cst k" := (k *: X) (only parsing) : proba_scope.
Notation "f `*: X" := (scale_RV f X) : proba_scope.
Notation "X '`/' n" := (n%:R^-1 *: X) (only parsing) : proba_scope.
Notation "X '`^2' " := (X ^+ 2) (only parsing) : proba_scope.

Section RV_simplification_lemmas.
Context {R : realType} {U : finType} {P : R.-fdist U}.
Implicit Types (K : pzRingType).
Local Open Scope ring_scope.

Lemma sumrRVE {V : nmodType} I (r : seq I) (p : pred I) (X : I -> {RV P -> V}) :
  \sum_(i <- r | p i) X i = fun x => \sum_(i <- r | p i) X i x.
Proof. by apply/boolp.funext => ?; elim/big_rec2: _ => //= i y ? Pi <-. Qed.
(* NB: should be `exact: sumrfctE.`, but this does not work for now *)

Lemma prodrRVE {V : pzRingType} I (r : seq I) (p : pred I) (X : I -> {RV P -> V}) :
  \prod_(i <- r | p i) X i = fun x => \prod_(i <- r | p i) X i x.
Proof. by apply/boolp.funext => ?; elim/big_rec2: _ => //= i y ? Pi <-. Qed.
(* FIXTHEM: analysis.functions.prodrfctE is not generic enough *)

Lemma addrRVE {V : nmodType} (X Y : {RV P -> V}) :
  X + Y = fun x => X x + Y x.
Proof. by []. Qed.

Lemma natmulRVE {V : nmodType} (X : {RV P -> V}) n :
  X *+ n = fun x => X x *+ n.
Proof. exact: natmulfctE. Qed.

Lemma opprRVE (V : zmodType) (X : {RV P -> V}) : - X = (fun x => - X x).
Proof. by []. Qed.

Lemma mulrRVE (V : pzRingType) (X Y : {RV P -> V}) :
  X * Y = (fun x => X x * Y x).
Proof. by []. Qed.

Lemma scalerRVE K (V : lmodType K) k (X : {RV P -> V}) :
  k *: X = (fun x => k *: X x).
Proof. by []. Qed.
(* FIXTHEM: analysis.functions.scalrfctE looks like a typo (of scalerfctE) *)

Lemma trans_add_RVE (V : nmodType) (X : {RV P -> V}) m :
  X `+cst m = (fun x => X x + m).
Proof. by []. Qed.

Lemma trans_sub_RVE (V : zmodType) (X : {RV P -> V}) m :
  X `-cst m = (fun x => X x - m).
Proof. by []. Qed.

Lemma const_RVE (T : eqType) (x : T) :
  const_RV P x = fun _ => x.
Proof. by []. Qed.

Lemma exprRVE (V : pzRingType) (X : {RV P -> V}) n:
  X ^+ n = (fun x => X x ^+ n).
Proof. by elim: n => [|n h]; rewrite boolp.funeqE=> ?; rewrite ?expr0 ?exprS ?h. Qed.
(* FIXTHEM: analysis.functions.exprfctE is not generic enough *)

Lemma comp_RVE (T1 T2 : eqType) (f : T1 -> T2) (X : {RV P -> T1}) :
  f \o X = fun x => f (X x).
Proof. by []. Qed.

Definition RV_fctE :=
  (@const_RVE, @comp_RVE, @opprRVE, @addrRVE, @mulrRVE, @scalerRVE, @exprRVE,
    @natmulRVE, @trans_add_RVE, @trans_sub_RVE, fctE).

Lemma addr_const_RV (V : nmodType) (x y : V) :
  const_RV P x + const_RV P y = const_RV P (x + y).
Proof. by []. Qed.

Lemma natmul_const_RV (V : nmodType) (x : V) n :
  const_RV P x *+ n = const_RV P (x *+ n).
Proof. by rewrite natmulRVE. Qed.

Lemma oppr_const_RV (V : zmodType) (x : V) :
  - const_RV P x = const_RV P (- x).
Proof. by []. Qed.

Lemma mulr_const_RV (V : pzRingType) (x y : V) :
  const_RV P x * const_RV P y = const_RV P (x * y).
Proof. by []. Qed.

Lemma scaler_const_RV K (V : lmodType K) k (x : V) :
  k *: const_RV P x = const_RV P (k *: x).
Proof. by []. Qed.

Lemma expr_const_RV (V : pzRingType) (x : V) n :
  const_RV P x ^+ n = const_RV P (x ^+ n).
Proof. by rewrite exprRVE. Qed.

End RV_simplification_lemmas.

Arguments sumrRVE {R U}.
Arguments prodrRVE {R U}.

Section real_random_variables.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).

Definition log_RV : {RV P -> R} := fun x => log (P x).

End real_random_variables.
Notation "'`log' P" := (log_RV P) : proba_scope.

Section RV_lemmas.
Context {R : realType} {V : lmodType R}.
Variables (U : finType) (P : R.-fdist U).

Lemma scale_RVA f g (X : {RV P -> V}) :
  scale_RV (f \* g) X = scale_RV f (scale_RV g X).
Proof. by rewrite /scale_RV boolp.funeqE => u; rewrite scalerA. Qed.

Lemma sq_RV_ge0 (X : {RV P -> R}) x : 0 <= (X ^+ 2) x.
Proof. by rewrite sqr_ge0. Qed.

End RV_lemmas.

Section pair_of_RVs.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).
Variables (A : eqType) (X : {RV P -> A}) (B : eqType) (Y : {RV P -> B}).
Definition RV2 : {RV P -> A * B} := fun x => (X x, Y x).
End pair_of_RVs.

Notation "'[%' x , y , .. , z ']'" := (RV2 .. (RV2 x y) .. z).

Section RV2_prop.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).
Variables (A B : finType) (X : {RV P -> A}) (Y : {RV P -> B}).

Lemma fst_RV2 : (`p_[% X, Y])`1 = `p_X.
Proof. by rewrite /fdist_fst /dist_of_RV fdistmap_comp. Qed.

Lemma snd_RV2 : (`p_[% X, Y])`2 = `p_Y.
Proof. by rewrite /fdist_snd /dist_of_RV fdistmap_comp. Qed.

Lemma fdistX_RV2 : fdistX `p_[% X, Y] = `p_[% Y, X].
Proof. by rewrite /fdistX /dist_of_RV fdistmap_comp. Qed.

Lemma RV20 : fst \o [% X, unit_RV P] =1 X.
Proof. by []. Qed.

Lemma RV02 : snd \o [% unit_RV P, X] =1 X.
Proof. by []. Qed.

End RV2_prop.

Section RV3_prop.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).
Variables (A B C D : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).

Lemma fdist_proj13_RV3 : fdist_proj13 `p_[% X, Y, Z] = `p_[% X, Z].
Proof.
by rewrite /fdist_proj13 /fdist_snd /fdistA /dist_of_RV /fdistC12 !fdistmap_comp.
Qed.

Lemma snd_RV3 : (`p_[% X, Y, Z])`2 = (`p_[% X, Z])`2.
Proof. by rewrite -fdist_proj13_snd fdist_proj13_RV3. Qed.

Lemma fdistC12_RV3 : fdistC12 `p_[% X, Y, Z] = `p_[% Y, X, Z].
Proof. by rewrite /fdistC12 /dist_of_RV fdistmap_comp. Qed.

Lemma fdistA_RV3 : fdistA `p_[% X, Y, Z] = `p_[% X, [% Y, Z]].
Proof. by rewrite /fdistC12 /dist_of_RV /fdistA fdistmap_comp. Qed.

End RV3_prop.

Lemma pr_eq_unit {R : realType} (U : finType) (P : R.-fdist U) :
  `Pr[ (unit_RV P) = tt ] = 1.
Proof. by rewrite -dist_of_RVE; apply/eqP/fdist1P => -[]. Qed.

Lemma Pr_fdistmap_RV2 {R : realType} (U : finType) (P : R.-fdist U) (A B : finType)
  (E : {set A}) (F : {set B}) (X : {RV P -> A}) (Z : {RV P -> B}) :
  Pr `p_[% X, Z] (E `* F) =
  Pr P ([set x | preim X (mem E) x] :&: [set x | preim Z (mem F) x]).
Proof.
rewrite /Pr.
transitivity (\sum_(a in ([% X, Z] @^-1: (E `* F)%set)) P a); last first.
  by apply: eq_bigl => u; rewrite !inE.
rewrite [in RHS]partition_big_preimset /=.
apply: eq_big => // -[a c]; rewrite inE => /andP[/= aE cF].
by rewrite fdistmapE.
Qed.

Lemma pfwd1_diag {R : realType} (T : finType) (U : eqType) (P : R.-fdist T)
  (X : {RV P -> U}) (x : U) : `Pr[ [% X, X] = (x, x) ] = `Pr[ X = x ].
Proof.
by rewrite !pfwd1E /Pr; apply: eq_bigl=> a; rewrite !inE xpair_eqE andbb.
Qed.

Section pr_pair.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).
Variables (A B C : finType) (TA TB TC : eqType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).
Variables (TX : {RV P -> TA}) (TY : {RV P -> TB}) (TZ : {RV P -> TC}).

Lemma pr_in_pairC E F : `Pr[ [% Y, X] \in F `* E ] = `Pr[ [% X, Y] \in E `* F].
Proof. by rewrite 2!pr_inE; apply: eq_bigl => u; rewrite !inE /= andbC. Qed.

Lemma pfwd1_pairC x : `Pr[ [% TY, TX] = x ] = `Pr[ [% TX, TY] = swap x].
Proof.
by rewrite !pfwd1E; congr Pr; apply/setP => u; rewrite !inE /= !xpair_eqE andbC.
Qed.

Lemma pr_in_pairA E F G :
  `Pr[ [% X, [% Y, Z]] \in E `* (F `* G) ] =
  `Pr[ [% [% X, Y], Z] \in (E `* F) `* G].
Proof. by rewrite !pr_inE; apply: eq_bigl => u; rewrite !inE /= andbA. Qed.

Lemma pfwd1_pairA a b c :
  `Pr[ [% TX, [% TY, TZ]] = (a, (b, c))] = `Pr[ [% TX, TY, TZ] = (a, b, c) ].
Proof.
by rewrite !pfwd1E; apply: eq_bigl => u; rewrite !inE /= !xpair_eqE andbA.
Qed.

Lemma pr_in_pairAC E F G :
`Pr[ [% X, Y, Z] \in (E `* F) `* G] = `Pr[ [% X, Z, Y] \in (E `* G) `* F].
Proof. by rewrite !pr_inE; apply: eq_bigl => u; rewrite !inE /= andbAC. Qed.

Lemma pfwd1_pairAC a b c :
`Pr[ [% TX, TY, TZ] = (a, b, c) ] = `Pr[ [% TX, TZ, TY] = (a, c, b)].
Proof.
by rewrite !pfwd1E; apply: eq_bigl => u; rewrite !inE /= !xpair_eqE andbAC.
Qed.

Lemma pr_in_pairCA E F G :
`Pr[ [% X, [%Y, Z]] \in E `* (F `* G) ] = `Pr[ [% Y, [%X, Z]] \in F `* (E `* G)].
Proof. by rewrite !pr_inE; apply: eq_bigl => u; rewrite !inE /= andbCA. Qed.

Lemma pfwd1_pairCA  a b c :
`Pr[ [% TX, [%TY, TZ]] = (a, (b, c)) ] = `Pr[ [% TY, [% TX, TZ]] = (b, (a, c))].
Proof.
by rewrite !pfwd1E; apply: eq_bigl => u; rewrite !inE /= !xpair_eqE andbCA.
Qed.

Lemma pr_in_comp_image (f : A -> B) E : injective f ->
  `Pr[ X \in E ] = `Pr[ (f `o X) \in f @: E ].
Proof.
by move=> inj_f; rewrite 2!pr_inE' (Pr_fdistmap inj_f) fdistmap_comp.
Qed.

Lemma pfwd1_comp (f : A -> B) a : injective f ->
  `Pr[ (f `o X) = f a ] = `Pr[ X = a ].
Proof.
move=> inj_f.
by rewrite -!pr_in1 !pr_inE' (Pr_fdistmap inj_f) fdistmap_comp imset_set1.
Qed.

End pr_pair.
#[deprecated(since="infotheo 0.9.6", note="renamed to `pr_in_comp_image`")]
Notation pr_in_comp := pr_in_comp_image (only parsing).

Section pr_in_comp'.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).
Variables (TA UA : finType) (f : TA -> UA) (X : {RV P -> TA}).

(* TODO: rename to pr_in_comp after releasing 0.9.7 *)
Lemma pr_in_comp' E : `Pr[ (f `o X) \in E ]  = `Pr[ X \in f @^-1: E ].
Proof.
rewrite !pr_inE' /Pr.
rewrite partition_big_preimset /=.
apply: eq_bigr=> i iE.
under [RHS]eq_bigr=> j ?.
  rewrite fdistmapE.
  under eq_bigl do rewrite /= inE /=.
  over.
under eq_bigl do rewrite -in_preimset1.
rewrite -partition_big_preimset /= fdistmapE.
apply: eq_bigl=> j.
by rewrite !inE.
Qed.

End pr_in_comp'.

Section pfwd1_RV2_comp.
Context {R : realType} (T A B : finType) (P : R.-fdist T).
Variables (X : {RV P -> A}) (f : A -> B).
Variables (a : A).

Lemma pfwd1_RV2_compl : `Pr[ [% f `o X, X] = (f a, a) ] = `Pr[ X = a ].
Proof.
rewrite 2!pfwd1E; congr Pr; apply/setP => t.
by rewrite !inE xpair_eqE andb_idl// => /eqP <-.
Qed.

End pfwd1_RV2_comp.

Lemma pr_in_pair_setT {R : realType} (U : finType) (P : R.-fdist U)
    (A B : finType) (E : {set A}) (X : {RV P -> A}) (Y : {RV P -> B}) :
  `Pr[ [% X, Y] \in E `*T ] = `Pr[ X \in E ].
Proof.
apply/esym.
rewrite (@pr_in_comp_image _ _ _ _ _ _ (fun a => (a, tt))); last by move=> u1 u2 -[].
rewrite 2!pr_inE; congr Pr; apply/setP => u; rewrite !inE /=.
by apply/imsetP/idP => [[a aE [] ->//]|XuE]; exists (X u).
Qed.

Section RV_domin_finType.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (A B : finType) (TA TB : eqType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}).
Variables (TX : {RV P -> A}) (TY : {RV P -> B}).

Lemma pr_in_domin_RV2 E F : `Pr[ X \in E] = 0 -> `Pr[ [% X, Y] \in E `* F] = 0.
Proof. by move=> H; rewrite pr_inE' fst_Pr_domin_setX // fst_RV2 -pr_inE'. Qed.

End RV_domin_finType.

Section RV_domin_eqType.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (TA TB : eqType).
Variables (TX : {RV P -> TA}) (TY : {RV P -> TB}).

Lemma pfwd1_domin_RV2 a b : `Pr[ TX = a] = 0 -> `Pr[ [% TX, TY] = (a, b) ] = 0.
Proof.
rewrite !pfwd1E /Pr => /psumr_eq0P => a0.
rewrite big1// => i.
rewrite inE/= xpair_eqE => /andP [] ? ?.
by apply: a0 => //; rewrite inE.
Qed.

Lemma pfwd1_domin_RV1 a b : `Pr[ TY = b] = 0 -> `Pr[ [% TX, TY] = (a, b) ] = 0.
Proof.
rewrite !pfwd1E /Pr => /psumr_eq0P => a0.
rewrite big1// => i.
rewrite inE/= xpair_eqE => /andP [] ? ?.
by apply: a0 => //; rewrite inE.
Qed.

End RV_domin_eqType.

Local Open Scope vec_ext_scope.

(* TODO: really necessary? *)
Definition cast_RV_fdist_rV1 {R : realType} (U : finType) (P : R.-fdist U) (T : eqType)
    (X : {RV P -> T}) : {RV (P `^ 1) -> T} :=
  fun x => X (x ``_ ord0).

(* TODO: really necessary? *)
Definition cast_RV_fdist_rV10 {R : realType} (U : finType) (P : R.-fdist U) (T : eqType)
    (Xs : 'rV[{RV P -> T}]_1) : {RV (P `^ 1) -> T} :=
  cast_RV_fdist_rV1 (Xs ``_ ord0).

(* TODO: really necessary? *)
Definition cast_fun_rV1 U (T : eqType) (X : U -> T) : 'rV[U]_1 -> T :=
  fun x => X (x ``_ ord0).

(* TODO: really necessary? *)
Definition cast_fun_rV10 U (T : eqType) (Xs : 'rV[U -> T]_1) : 'rV[U]_1 -> T :=
  cast_fun_rV1 (Xs ``_ ord0).

Local Close Scope vec_ext_scope.

Section expected_value_def.
Context {R : realType} {V : lmodType R}.
Variables (U : finType) (P : R.-fdist U) (X : {RV P -> V}).

Definition Ex := \sum_(u in U) P u *: X u.

End expected_value_def.
Arguments Ex {R V U} _ _.

Notation "'`E'" := (@Ex _ _ _ _) : proba_scope.

(* Alternative definition of the expected value: *)
Section Ex_alt.
Context {R : realType} {V : lmodType R}.
Variables (U : finType) (P : R.-fdist U) (X : {RV P -> V}).

Definition Ex_alt := \sum_(r <- fin_img X) `Pr[ X = r ] *: r.

Lemma Ex_altE : Ex_alt = `E X.
Proof.
rewrite /Ex.
transitivity (\sum_(r <- fin_img X) \sum_(u in U | X u == r) (P u *: X u)).
  apply: eq_bigr => /= r _; rewrite pfwd1E scaler_suml /=.
  by apply: eq_big => //= a; rewrite !inE // => /eqP ->.
by rewrite -partition_big_fin_img.
Qed.

End Ex_alt.

Section expected_value_prop.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).

Lemma E_add_RV {V : lmodType R} (X Y : {RV P -> V}) :
  `E (X `+ Y) = `E X + `E Y.
Proof. by rewrite -big_split; apply: eq_bigr => a _ /=; rewrite scalerDr. Qed.

Lemma E_sub_RV {V : lmodType R} (X Y : {RV P -> V}) :
  `E (X `- Y) = `E X - `E Y.
Proof.
rewrite {3}/Ex big_morph_oppr -big_split /=.
by apply: eq_bigr => u _; rewrite scalerDr scalerN.
Qed.

Lemma E_opp_RV {V : lmodType R} (X : {RV P -> V}) :
  `E (`-- X) = - `E X.
Proof.
rewrite /Ex/=; under eq_bigr do rewrite scalerN.
exact/esym/big_morph_oppr.
Qed.

Lemma E_scale_RV {V : lmodType R} (X : {RV P -> V}) k :
  `E (k `cst* X) = k *: `E X.
Proof.
rewrite /scale_RV {2}/Ex scaler_sumr /=; apply: eq_bigr => a _.
by rewrite !scalerA mulrC.
Qed.

Lemma Ex_ge0 (X : {RV P -> R}) : (forall u, 0 <= X u) -> 0 <= `E X.
Proof. by move=> H; apply/sumr_ge0 => u _; rewrite mulr_ge0. Qed.

Lemma E_sumR {V : lmodType R} I r p (Z : I -> {RV P -> V}) :
  `E (\sum_(i <- r | p i) Z i) = \sum_(i <- r | p i) (`E (Z i)).
Proof.
by rewrite exchange_big/=; apply: eq_bigr=> u _; rewrite sumrRVE scaler_sumr.
Qed.

Lemma E_const_RV {V : lmodType R} (k : V) : `E (@const_RV _ U P V k) = k.
Proof. by rewrite /Ex /const_RV /= -scaler_suml /= FDist.f1 scale1r. Qed.

Lemma E_trans_add_RV {V : lmodType R} (X : {RV P -> V}) m :
  `E (X `+cst m) = `E X + m.
Proof.
rewrite /trans_add_RV /=.
transitivity (\sum_(u in U) (P u *: X u + P u *: m)).
  by apply: eq_bigr => u _ /=; rewrite scalerDr.
by rewrite big_split /= -scaler_suml /= FDist.f1 scale1r.
Qed.

Lemma E_trans_sub_RV {V : lmodType R} (X : {RV P -> V}) m :
  `E (X `-cst m) = `E X - m.
Proof.
rewrite /trans_sub_RV /=.
transitivity (\sum_(u in U) (P u *: X u + P u *: - m)).
  by apply: eq_bigr => u _ /=; rewrite scalerDr.
by rewrite big_split /= -scaler_suml /= FDist.f1 scale1r.
Qed.

Lemma E_trans_RV_id_rem (X : {RV P -> R}) m :
  `E ((X `-cst m) `^2) = `E ((X `^2 `- ((2 * m) `cst* X)) `+cst m ^+ 2).
Proof.
congr `E; rewrite sqrrB; congr (_ - _ + _).
by rewrite -mulr_natr -mulrA mulr_regr mulrC.
Qed.

Lemma E_comp_RV (f : R -> R) k (X : {RV P -> R}) :
    (forall x y, f (x * y) = f x * f y) ->
  `E (f `o (k `cst* X)) = `E (f k `cst* (f `o X)).
Proof. by move=> H; rewrite /comp_RV /=; apply: eq_bigr => u _; rewrite H. Qed.

End expected_value_prop.

Lemma E_cast_RV_fdist_rV1 {R : realType} {V : lmodType R} (A : finType)
    (P : R.-fdist A) :
  forall (X : {RV P -> V}), `E (cast_RV_fdist_rV1 X) = `E X.
Proof.
move=> f; rewrite /cast_RV_fdist_rV1 /=; apply: big_rV_1 => // m.
by rewrite -fdist_rV1.
Qed.

Section conditional_expectation_def.
Context {R : realType} {V : lmodType R}.
Variable (U : finType) (P : R.-fdist U) (X : {RV P -> V}) (F : {set U}).

Definition cEx :=
  \sum_(r <- fin_img X) Pr P (finset (X @^-1 r) :&: F) / Pr P F *: r.

End conditional_expectation_def.
Notation "`E_[ X | F ]" := (cEx X F).

Section conditional_expectation_prop.
Context {R : realType} {V : lmodType R}.
Variable (U I : finType) (P : R.-fdist U) (X : {RV P -> V}) (F : I -> {set U}).
Hypothesis dis : forall i j, i != j -> [disjoint F i & F j].
Hypothesis cov : cover [set F i | i in I] = [set: U].

Lemma Ex_cEx : `E X = \sum_(i in I) Pr P (F i) *: `E_[X | F i].
Proof.
apply/esym; rewrite /cEx.
evar (f : I -> V); rewrite (eq_bigr f); last first.
  by move=> i _; rewrite scaler_suml /f; reflexivity.
rewrite {}/f /= (bigID (fun i => Pr P (F i) != 0)) /=.
rewrite [in X in _ + X = _]big1 ?addr0; last first.
  move=> i; rewrite negbK => /eqP ->; rewrite big1 // => r _.
  under eq_bigr => j _ do rewrite invr0 mulr0.
  by rewrite -scaler_sumr scale0r scaler0.
transitivity (\sum_(i in I | Pr P (F i) != 0)
  \sum_(j <- fin_img X) (Pr P (finset (X @^-1 j) :&: F i)) *: j).
  apply: eq_bigr => i Fi0.
  rewrite -scaler_suml scaler_sumr.
  apply: eq_bigr => r _.
  by rewrite scalerA mulrCA mulfV// mulr1.
rewrite -Ex_altE /Ex_alt exchange_big /=; apply: eq_bigr => r _.
rewrite -scaler_suml /=; congr (_ *: _).
transitivity (\sum_(i in I) Pr P (finset (X @^-1 r) :&: F i)).
  rewrite big_mkcond /=; apply: eq_bigr => i _.
  case: ifPn => //; rewrite negbK => /eqP PFi0.
  rewrite /Pr big1 // => u; rewrite inE => /andP[uXr uFi].
  move/eqP : PFi0; rewrite psumr_eq0// => /allP/(_ u).
  by rewrite mem_index_enum uFi implyTb => /(_ isT)/eqP.
rewrite -Boole_eq; last first.
  move=> i j ij; rewrite -setI_eq0; apply/eqP/setP => u; rewrite !inE.
  apply/negbTE; rewrite !negb_and.
  have [/= Xur|//] := eqVneq (X u) r.
  move: (dis ij); rewrite -setI_eq0 => /eqP/setP/(_ u).
  by rewrite !inE => /negbT; rewrite negb_and.
rewrite pfwd1E; congr Pr.
move: cov; rewrite cover_imset => cov'.
by rewrite -big_distrr /= cov' setIT.
Qed.

End conditional_expectation_prop.

(** A theory of indicator functions from [A : finType] to [R] *)
Section Ind.
Context {R : realType} {A : finType}.
Implicit Types (x : A) (X Y : {set A}).

Definition Ind X x : R := if x \in X then 1 else 0.

Lemma Ind_ge0 X x : 0 <= Ind X x :> R.
Proof. by rewrite /Ind; case: ifPn. Qed.

Lemma Ind_le1 X x : Ind X x <= 1 :> R.
Proof. by rewrite /Ind; case: ifPn. Qed.

Lemma Ind_set0 x : Ind set0 x = 0.
Proof. by rewrite /Ind inE. Qed.

Lemma Ind_setT x : Ind [set: A] x = 1.
Proof. by rewrite /Ind inE. Qed.

Lemma Ind_inP X x : reflect (Ind X x = 1) (x \in X).
Proof.
apply: (iffP idP); rewrite /Ind; first by move->.
by case: ifPn => // _ /eqP; rewrite eq_sym oner_eq0.
Qed.

Lemma Ind_notinP X x : reflect (Ind X x = 0) (x \notin X).
Proof.
apply: (iffP idP); rewrite /Ind => Hmain.
  by rewrite ifF //; exact: negbTE.
by apply: negbT; case: ifP Hmain =>// _ /eqP; rewrite oner_eq0.
Qed.

Lemma Ind_subset X Y : X \subset Y <-> forall a, Ind X a <= Ind Y a :> R.
Proof.
rewrite /Ind; split => H.
  move=> a; case: ifPn.
  - by move/subsetP ->.
  - by case: (a \in Y).
apply/subsetP => a aX.
by move: (H a); rewrite aX; case: (a \in Y) => //; rewrite ler10.
Qed.

Lemma Ind_setI X Y x : Ind (X :&: Y) x = Ind X x * Ind Y x.
Proof. by rewrite /Ind inE; case: in_mem; case: in_mem=>/=; lra. Qed.

Lemma Ind_setU X Y x :
  Ind (X :|: Y) x = Num.max (Ind X x) (Ind Y x).
Proof.
rewrite /Ind inE; case: ifPn; last first.
  by rewrite negb_or => /andP [] /negPf -> /negPf -> /=; rewrite maxxx.
by case/orP => ->; rewrite -/(Ind _ _) ?(@max_l _ _ 1) ?max_r// Ind_le1.
Qed.

Lemma Ind_bigcap I (e : I -> {set A}) (r : seq I) (p : pred I) x :
  Ind (\bigcap_(j <- r | p j) e j) x = \prod_(j <- r | p j) (Ind (e j) x).
Proof.
apply: (big_ind2 (fun a b => Ind a x = b)) => //.
- exact: Ind_setT.
by move=> ???? <- <-; exact: Ind_setI.
Qed.

Lemma Ind_bigcup I (e : I -> {set A}) (r : seq I) (p : pred I) x :
  Ind (\bigcup_(j <- r | p j) e j) x =
  \big[Order.max/0]_(j <- r | p j) (Ind (e j) x).
Proof.
apply: (big_ind2 (fun a b => Ind a x = b)) => //.
- exact: Ind_set0.
by move=> ???? <- <-; exact: Ind_setU.
Qed.

Lemma E_Ind (P : R.-fdist A) s : `E (Ind s : {RV P -> R}) = Pr P s.
Proof.
rewrite /Ex /Ind /Pr (bigID (mem s)) /=.
rewrite [X in _ + X = _]big1; last by move=> i /negbTE ->; rewrite scaler0.
by rewrite addr0; apply: eq_bigr => i ->; rewrite -[RHS]mulr1 mulr_regl.
Qed.

End Ind.
#[deprecated(since="infotheo 0.9.7", note="renamed to `Ind_setI`")]
Notation Ind_cap := Ind_setI (only parsing).

Section Ind_RV.
Context {R : realType} {V : lmodType R}.
Variables (U : finType) (P : R.-fdist U).

Lemma Ind_setD (X Y : {set U}) :
  Y \subset X -> Ind (X :\: Y) = Ind X `- Ind Y :> {RV P -> R}.
Proof.
move/subsetP=> YsubX; rewrite /Ind !RV_fctE; apply: boolp.funext => u /=.
case: ifPn; rewrite inE ?negb_and;
  first by case/andP => /negbTE -> ->; rewrite subr0.
case/orP; first by move => /negbNE /[dup] /YsubX -> ->; rewrite subrr.
move/contraNN: (YsubX u) => YsubX'.
move=> /[dup] /YsubX' /negbTE -> /negbTE ->.
by rewrite subrr.
Qed.

Lemma sq_RVE (X : {RV P -> R}) : X `^2 = X `* X.
Proof. by []. Qed.

Lemma Ind_sqr F : Ind F = ((Ind F : {RV P -> R}) `^2).
Proof.
rewrite sq_RVE boolp.funeqE /Ind !RV_fctE => x.
by case: ifPn; rewrite ?mulr0 ?mulr1.
Qed.

End Ind_RV.

(** This section gathers a proof of the formula of inclusion-exclusion
    contributed by Erik Martin-Dorel: the corresponding theorem is named
    [Pr_bigcup_incl_excl] and is more general than lemma [Pr_bigcup]. *)
Section probability_inclusion_exclusion.
Context {R : realType}.
Variables (A : finType) (P : R.-fdist A).

Let SumIndCap (n : nat) (S : 'I_n -> {set A}) (k : nat) : {RV P -> R} :=
  \sum_(J in {set 'I_n} | #|J| == k) (Ind (\bigcap_(j in J) S j)).

Lemma Ind_bigcup_incl_excl (n : nat) (S : 'I_n -> {set A}) (x : A) :
  Ind (\bigcup_(i < n) S i) x =
  (\sum_(1 <= k < n.+1) (-1) ^+ (k - 1) * SumIndCap S k x).
Proof.
case: n S => [|n] S; first by rewrite big_ord0 big_geq // Ind_set0.
set Efull := \bigcup_(i < n.+1) S i.
have Halg : \prod_(i < n.+1) (Ind Efull x - Ind (S i) x) = 0 :> R.
  case Ex : (x \in Efull); last first.
  { have /Ind_notinP Ex0 := Ex.
    under eq_bigr do rewrite Ex0.
    have Ex00 : forall i : 'I_n.+1, Ind (S i) x = 0 :> R.
      move=> i; apply/Ind_notinP.
      by move/negbT: Ex; rewrite -!in_setC setC_bigcup; move/bigcapP; apply.
    under eq_bigr do rewrite Ex00.
    by rewrite subr0 big_ord_recl mul0r. }
  { rewrite /Efull in Ex.
    have /bigcupP [i Hi Hi0] := Ex.
    rewrite (bigD1 i)//= /Efull (Ind_inP _ _ Ex) (Ind_inP _ _ Hi0) subrr.
    by rewrite mul0r. }
rewrite bigA_distr/= in Halg.
do [erewrite eq_bigr; last by move=> k _; (* TODO: replace with under *)
    erewrite eq_bigr; last by move=> J _; rewrite bigID2] in Halg.
rewrite big_ltn //= in Halg.
move/eqP in Halg.
rewrite addr_eq0 in Halg.
rewrite cardT size_enum_ord (big_pred1 set0) in Halg; last first.
  by move=> i; rewrite pred1E [RHS]eq_sym; apply: cards_eq0.
move/eqP in Halg.
rewrite [in X in _ * X = _]big_pred0 in Halg; last by move=> i; rewrite inE.
do [erewrite eq_bigl; (* TODO: replace with under *)
  last by move=> j; rewrite !inE /negb /= ] in Halg.
rewrite mulr1 -Ind_bigcap big_const_ord iterSr iter_fix setIT ?setIid // in Halg.
rewrite {}Halg big_morph_oppr big_nat [RHS]big_nat.
apply: eq_bigr => i Hi; rewrite /SumIndCap /Efull.
rewrite m1powD; last first.
  by case/andP: Hi => Hi _ K0; rewrite K0 in Hi.
rewrite mulNr.
rewrite (sumrRVE P) big_distrr/=.
congr -%R; apply: eq_bigr => j Hj.
rewrite prodrN (eqP Hj).
rewrite (_ : ?[a] * ((-1)^+i * ?[b]) = (-1)^+i * (?a * ?b)); last by lra.
congr *%R.
have [Hlt|Hn1] := ltnP i n.+1; last first.
{ rewrite big1; last first.
  { move=> k Hk; rewrite inE in Hk.
    rewrite (_: j = [set: 'I_n.+1]) ?inE // in Hk.
    apply/setP/subset_cardP =>//.
    rewrite (eqP Hj) cardsT /= card_ord.
    by apply/anti_leq/andP; split; first by case/andP: Hi =>//. }
  by rewrite mul1r Ind_bigcap. }
rewrite -!Ind_bigcap big_const.
  rewrite cardsCs card_ord setCK (eqP Hj).
  have [m ->] : exists m, (n.+1 - i)%nat = m.+1.
    by exists (n.+1 - i).-1; rewrite prednK // subn_gt0.
  rewrite iterSr iter_fix ?setIT ?setIid //.
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
  `E (SumIndCap S k : {RV P -> R}) = SumPrCap S k.
Proof.
rewrite /SumIndCap /SumPrCap E_sumR; apply: eq_bigr => i Hi.
by rewrite E_Ind.
Qed.

Theorem Pr_bigcup_incl_excl n (S : 'I_n -> {set A}) :
  Pr P (\bigcup_(i < n) S i) =
  \sum_(1 <= k < n.+1) ((-1)^+(k-1) * SumPrCap S k).
Proof.
rewrite -E_Ind /=.
rewrite /Ex.
under [LHS]eq_bigr => i _.
  rewrite Ind_bigcup_incl_excl scaler_sumr.
  under eq_bigr => j _ do rewrite scalerAr.
  over.
rewrite exchange_big /=.
apply: eq_bigr => i _.
rewrite -E_SumIndCap mulr_regl -E_scale_RV.
by under [LHS]eq_bigr => j _ do rewrite -scalerAr.
Qed.

End probability_inclusion_exclusion.

Section markov_inequality.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (X : {RV P -> R}).
Hypothesis X_ge0 : forall u, 0 <= X u.

Lemma Ex_lb (r : R) : `Pr[ X >= r] *: r <= `E X.
Proof.
rewrite /Ex (bigID [pred a' | X a' >= r]) /= -[a in a <= _]addr0.
rewrite lerD//; last by apply/sumr_ge0 => a _; rewrite mulr_ge0.
apply: (@le_trans _ _ (\sum_(i | X i >= r) P i *: r)).
  rewrite scaler_suml /= le_eqVlt; apply/orP; left; apply/eqP.
  by apply/eq_bigl => a; rewrite inE.
by apply: ler_sum => u Xur; rewrite -!mulr_regl; exact/ler_wpM2l.
Qed.

Lemma markov (r : R) : 0 < r -> `Pr[ X >= r ] <= `E X / r.
Proof. by move=> r0; rewrite ler_pdivlMr //; exact/Ex_lb. Qed.

End markov_inequality.

Section thm61.
Context {R : realType} {V : lmodType R}.
Variables (A : eqType) (U : finType) (P : R.-fdist U) (X : {RV P -> A}) (phi : A -> V).

Lemma Ex_comp_RV : `E (phi `o X) = \sum_(r <- fin_img X) `Pr[ X = r ] *: phi r.
Proof.
rewrite /Ex.
rewrite (partition_big_fin_img _ X (fun u => P u *: (phi `o X) u))/=.
apply: eq_bigr => a _.
rewrite pfwd1E /Pr scaler_suml /=; apply: eq_big.
  by move=> u; rewrite inE.
by move=> u /eqP Xua; rewrite /comp_RV -Xua.
Qed.

End thm61.

Section variance_def.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (X : {RV P -> R}).

Definition Var := let miu := `E X in `E ((X `-cst miu) `^2).

Lemma VarE : Var = `E (X `^2) - (`E X) ^+ 2.
Proof.
by rewrite /Var E_trans_RV_id_rem E_trans_add_RV E_sub_RV E_scale_RV -mulr_regl; lra.
Qed.

End variance_def.

Arguments Var {R U} _ _.

Notation "'`V'" := (@Var _ _ _) : proba_scope.

Section variance_prop.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (X : {RV P -> R}).

(** The variance is not linear: *)
Lemma Var_scale k : `V (k `cst* X) = k ^+ 2 *: `V X.
Proof.
rewrite /Var -E_scale_RV /trans_sub_RV; congr Ex.
rewrite E_scale_RV -scaler_const_RV -scalerBr.
(* the next line would become unnecessary once pzLalgType is instantiated for RVs *)
apply/boolp.funext=> ?; rewrite !RV_fctE/=.
by rewrite exprZn.
Qed.

Lemma Var_trans m : `V (X `+cst m) = `V X.
Proof.
rewrite /Var E_trans_add_RV; congr (`E (_ `^2)).
rewrite /trans_sub_RV /trans_add_RV -addr_const_RV.
by rewrite [X in _ + _ - X]addrC addrKA.
Qed.

End variance_prop.

Lemma Var_cast_RV_fdist_rV1 {R : realType} (A : finType) (P : R.-fdist A)
    (X : {RV P -> R}) :
  `V (@cast_RV_fdist_rV1 _ _ P _ X) = `V X.
Proof.
rewrite !VarE !E_cast_RV_fdist_rV1; congr (_ - _).
by apply: big_rV_1 => // v; rewrite fdist_rV1.
Qed.

Section chebyshev.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (X : {RV P -> R}).

Import Num.Def.

(** In any data sample, "nearly all" the values are "close to" the mean value: *)
Lemma chebyshev_inequality epsilon : 0 < epsilon ->
  `Pr[ (normr `o (X `-cst `E X)) >= epsilon] <= `V X / epsilon ^+ 2.
Proof.
move=> He; rewrite ler_pdivlMr ?exprn_gt0//.
rewrite mulrC /Var.
apply: (@le_trans _ _ (\sum_(a in U | `| X a - `E X | >= epsilon)
    P a *: (((X `-cst `E X) `^2) a))); last first.
  rewrite /Ex big_mkcondr/=; apply: ler_sum => a _; case: ifPn => // _.
  by apply: mulr_ge0 => //; exact: sq_RV_ge0.
rewrite /Pr big_distrr/= [_ ^+ 2]lock /= -!lock big_mkcond/= [leRHS]big_mkcond/=.
apply: ler_sum => u _; rewrite inE/=; case: ifPn => //.
rewrite -!/(_ ^+ 2) => H.
rewrite mulrC ler_wpM2l => //=.
apply: (@le_trans _ _ ((X u - `E X) ^+ 2)); last by rewrite lexx.
by rewrite -real_normK ?num_real// -[leRHS]real_normK ?num_real// ler_sqr// gtr0_norm.
Qed.

End chebyshev.

Section independent_events.
Context {R : realType}.
Variables (A : finType) (d : R.-fdist A).

Definition inde_events (E F : {set A}) := Pr d (E :&: F) = Pr d E * Pr d F.

Lemma inde_events_cplt (E F : {set A}) :
  inde_events E F -> inde_events E (~: F).
Proof.
rewrite /inde_events => EF; have : Pr d E = Pr d (E :&: F) + Pr d (E :&: ~:F).
  rewrite (@total_prob _ _ d _ E (fun b => if b then F else ~:F)) /=; last 2 first.
    move=> i j ij; rewrite -setI_eq0.
    by case: ifPn ij => Hi; case: ifPn => //= Hj _;
      rewrite ?setICr // setIC setICr.
    by rewrite cover_imset big_bool /= setUC setUCr.
  by rewrite big_bool addrC.
move=> /eqP.
by rewrite addrC -subr_eq EF -{1}(mulr1 (Pr d E)) -mulrBr -Pr_setC => /eqP.
Qed.

End independent_events.

Section k_wise_independence.
Context {R : realType}.
Variables (A I : finType) (k : nat) (d : R.-fdist A) (E : I -> {set A}).

Definition kwise_inde := forall J : {set I}, (#|J| <= k)%N ->
  Pr d (\bigcap_(i in J) E i) = \prod_(i in J) Pr d (E i).

End k_wise_independence.

Section pairwise_independence.
Context {R : realType}.
Variables (A I : finType) (d : R.-fdist A) (E : I -> {set A}).

Definition pairwise_inde := @kwise_inde R A I 2%nat d E.

Lemma pairwise_indeE :
  pairwise_inde <-> forall i j, i != j -> inde_events d (E i) (E j).
Proof.
split => [pi i j ij|].
  rewrite /pairwise_inde in pi.
  have /pi : (#|[set i; j]| <= 2)%N by rewrite cards2 ij.
  rewrite bigcap_setU !big_set1 => H.
  rewrite /inde_events.
  by rewrite H (big_setD1 i) ?inE ?eqxx ?orTb//= setU1K ?inE// big_set1.
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
Context {R : realType}.
Variables (A I : finType) (d : R.-fdist A) (E : I -> {set A}).

Definition mutual_inde := forall k, @kwise_inde R A I k.+1 d E.

Lemma mutual_indeE :
  mutual_inde <-> (forall J : {set I}, J \subset I ->
    Pr d (\bigcap_(i in J) E i) = \prod_(i in J) Pr d (E i)).
Proof.
rewrite /mutual_inde; split => [H J JI|H k J JI].
  have [->{J JI}|J0] := eqVneq J set0.
    by rewrite !big_set0 Pr_setT.
  by rewrite (H #|J|.-1) ?prednK // card_gt0.
by rewrite H //; apply/subsetP => i ij; rewrite inE.
Qed.

Lemma mutual_indeE' : #|I| != O -> mutual_inde <-> kwise_inde #|I| d E.
Proof.
move=> I0.
rewrite /mutual_inde; split => [H J JI|].
  have [->{J JI}|J0] := eqVneq J set0.
    by rewrite !big_set0 Pr_setT.
  by rewrite (H #|J|.-1) ?prednK // card_gt0.
by move=> H k J Jk; rewrite H // max_card.
Qed.

End mutual_independence.

Section uniform_finType_RV_lemmas.
Local Open Scope proba_scope.
Context {R : realType}.
Variables (T : finType) (n : nat) (P : R.-fdist T) (A : finType).
Variable X : {RV P -> A}.

Hypothesis card_A : #|A| = n.+1.
Hypothesis Xunif : `p_X = fdist_uniform card_A.

Lemma bij_comp_RV (f g : A -> A) :
  cancel f g -> cancel g f -> `p_(f `o X) =1 `p_X \o g.
Proof.
move=> fg gf x /=; rewrite !fdistbindE.
apply: eq_bigr=> a _.
by rewrite !fdist1E -(can_eq gf) fg.
Qed.

Lemma bij_RV_unif (f g : A -> A) :
  cancel f g -> cancel g f -> `p_(f `o X) = fdist_uniform card_A.
Proof.
move => fg gf.
apply/val_inj/ffunP => x /=.
by rewrite (bij_comp_RV fg gf) Xunif /= !fdist_uniformE.
Qed.

End uniform_finType_RV_lemmas.

Section uniform_finZmod_RV_lemmas.
Local Open Scope proba_scope.
Context {R : realType}.
Variables (T : finType) (P : R.-fdist T) (A : finZmodType).
Variable X : {RV P -> A}.

Let n := #|A|.-1.
Let card_A : #|A| = n.+1.
Proof. by apply/esym/prednK/card_gt0P; exists 0. Qed.

Hypothesis Xunif : `p_X = fdist_uniform card_A.

Lemma trans_RV_unif (m : A) : `p_(X `+cst m) = fdist_uniform card_A.
Proof. exact: (bij_RV_unif Xunif (addrK m) (subrK m)). Qed.

Lemma opp_RV_unif : `p_(`-- X) = fdist_uniform card_A.
Proof. exact: (bij_RV_unif Xunif opprK opprK). Qed.

End uniform_finZmod_RV_lemmas.

Section conditional_probablity.
Context {R : realType}.
Variables (A : finType) (d : R.-fdist A).
Implicit Types E F : {set A}.

Definition cPr E F := Pr d (E :&: F) / Pr d F.
Local Notation "`Pr_[ E | F ]" := (cPr E F).

Lemma cPr_ge0 E F : 0 <= `Pr_[E | F].
Proof.
rewrite /cPr; have [PF0|PF0] := eqVneq (Pr d F) 0.
  by rewrite setIC (Pr_domin_setI _ PF0) mul0r.
by rewrite divr_ge0.
Qed.
Local Hint Resolve cPr_ge0 : core.

Lemma cPr_eq0P E F : `Pr_[E | F] = 0 <-> Pr d (E :&: F) = 0.
Proof.
split; rewrite /cPr; last by move=> ->; rewrite mul0r.
move=> /eqP.
rewrite /cPr mulf_eq0 => -/predU1P[//|].
rewrite invr_eq0 => /eqP.
by rewrite setIC; exact: Pr_domin_setI.
Qed.

Lemma cPr_le1 E F : `Pr_[E | F] <= 1.
Proof.
rewrite /cPr.
have [PF0|PF0] := eqVneq (Pr d F) 0.
  by rewrite setIC (Pr_domin_setI E PF0) mul0r.
rewrite ler_pdivrMr ?lt0Pr//.
rewrite mul1r /Pr big_mkcond/= [leRHS]big_mkcond/=.
apply: ler_sum => // a _; rewrite inE.
have [aF|aF] := boolP (a \in F).
  rewrite andbT.
  by case: ifPn.
by rewrite andbF.
Qed.

Lemma cPrET E : `Pr_[E | setT] = Pr d E.
Proof. by rewrite /cPr setIT Pr_setT divr1. Qed.

Lemma cPrE0 E : `Pr_[E | set0] = 0.
Proof. by rewrite /cPr setI0 Pr_set0 mul0r. Qed.

Lemma lt0cPr E F : (0 < `Pr_[E | F]) = (`Pr_[E | F] != 0).
Proof. by rewrite lt_neqAle cPr_ge0 andbT eq_sym. Qed.

Lemma Pr_cPr_gt0 E F : 0 < Pr d (E :&: F) <-> 0 < `Pr_[E | F].
Proof.
rewrite lt0Pr; split => H; last first.
  move: H; rewrite lt0cPr; apply: contra => /eqP.
  by rewrite /cPr => ->; rewrite mul0r.
rewrite divr_gt0 ?lt0Pr//.
by apply: contra H; rewrite setIC => /eqP F0; apply/eqP/Pr_domin_setI.
Qed.

Lemma cPr_setD F1 F2 E :
  `Pr_[F1 :\: F2 | E] = `Pr_[F1 | E] - `Pr_[F1 :&: F2 | E].
Proof. by rewrite /cPr -mulrBl setIDAC Pr_setD setIAC. Qed.

Lemma cPr_setU F1 F2 E :
  `Pr_[F1 :|: F2 | E] = `Pr_[F1 | E] + `Pr_[F2 | E] - `Pr_[F1 :&: F2 | E].
Proof. by rewrite /cPr -mulrDl -mulrBl setIUl Pr_setU setIACA setIid. Qed.

Lemma Bayes E F : `Pr_[E | F] = `Pr_[F | E] * Pr d E / Pr d F.
Proof.
have [PE0|PE0] := eqVneq (Pr d E) 0.
  by rewrite /cPr [in RHS]setIC !(Pr_domin_setI F PE0) !mul0r.
by rewrite /cPr setIC -(mulrA _ _ (Pr d E)) mulVf// mulr1.
Qed.

Lemma product_rule E F : Pr d (E :&: F) = `Pr_[E | F] * Pr d F.
Proof.
rewrite /cPr; have [PF0|PF0] := eqVneq (Pr d F) 0.
  by rewrite setIC (Pr_domin_setI E PF0) 2!mul0r.
by rewrite -mulrA mulVf ?mulr1.
Qed.

Lemma product_rule_cond E F G :
  `Pr_[E :&: F | G] = `Pr_[E | F :&: G] * `Pr_[F | G].
Proof. by rewrite /cPr mulrA -setIA {1}product_rule. Qed.

Lemma cPr_cplt E F : Pr d E != 0 -> `Pr_[ ~: F | E] = 1 - `Pr_[F | E].
Proof.
move=> PE0; rewrite /cPr -(@divff _ (Pr d E))// -mulrBl; congr (_ / _).
apply/eqP; rewrite -subr_eq opprK addrC eq_sym.
rewrite -{1}(@setIT _ E) -(setUCr F) setIC setIUl disjoint_Pr_setU //.
by rewrite -setI_eq0 setIACA setICr set0I.
Qed.

Lemma inde_events_cPr E F : Pr d F != 0 -> inde_events d E F ->
  `Pr_[E | F] = Pr d E.
Proof. by move=> F0 EF; rewrite /cPr EF -mulrA mulfV ?mulr1. Qed.

Section bayes_extended.
Variables (I : finType) (E : {set A}) (F : I -> {set A}).
Hypothesis dis : forall i j, i != j -> [disjoint F i & F j].
Hypothesis cov : cover (F @: I) = [set: A].

Lemma total_prob_cond :
  Pr d E = \sum_(i in I) `Pr_[E | F i] * Pr d (F i).
Proof.
rewrite (@total_prob _ _ _ _ _ _ dis cov); apply: eq_bigr; move=> i _.
by rewrite product_rule.
Qed.

Lemma Bayes_extended j : `Pr_[F j | E] =
  `Pr_[E | F j] * Pr d (F j) / \sum_(i in I) `Pr_[E | F i] * Pr d (F i).
Proof.
have [PE0|PE0] := eqVneq (Pr d E) 0.
  by rewrite {1 2}/cPr setIC (Pr_domin_setI (F j) PE0) !mul0r.
rewrite -total_prob_cond /cPr -(mulrA _ _ (Pr _ (F j))); congr (_ / _).
have [Fj0|Fj0] := eqVneq (Pr d (F j)) 0.
  by rewrite Fj0 !mulr0 (Pr_domin_setI E Fj0).
by rewrite setIC mulVf ?mulr1.
Qed.

End bayes_extended.

End conditional_probablity.
Notation "`Pr_ P [ E | F ]" := (cPr P E F) : proba_scope.
Global Hint Resolve cPr_ge0 : core.

#[deprecated(since="infotheo 0.7.2", note="renamed to `cPr_eq0P`")]
Notation cPr_eq0 := cPr_eq0P (only parsing).
#[deprecated(since="infotheo 0.7.2", note="renamed to `cPr_le1`")]
Notation cPr_max := cPr_le1 (only parsing).
#[deprecated(since="infotheo 0.9.2", note="renamed to `lt0cPr`")]
Notation cPr_gt0P := lt0cPr (only parsing).
#[deprecated(since="infotheo 0.7.3", note="renamed to `cPr_setD`")]
Notation cPr_diff := cPr_setD (only parsing).
#[deprecated(since="infotheo 0.7.3", note="renamed to `cPr_setU`")]
Notation cPr_union_eq := cPr_setU (only parsing).

Section fdist_cond.
Context {R : realType}.
Variables (A : finType) (P : R.-fdist A) (E : {set A}).
Hypothesis E0 : Pr P E != 0.

Let f := [ffun a => `Pr_P [[set a] | E]].

Let f0 a : (0 <= f a)%O. Proof. by rewrite ffunE. Qed.

Let f1 : \sum_(a in A) f a = 1.
Proof.
rewrite /f.
under eq_bigr do rewrite ffunE.
rewrite /cPr -big_distrl /= eqr_divrMr // mul1r.
rewrite (@total_prob _ _ P _ E (fun i => [set i])); last 2 first.
  move=> i j ij; rewrite -setI_eq0; apply/eqP/setP => // a.
  by rewrite !inE; apply/negbTE; apply: contra ij => /andP[/eqP ->].
  apply/setP => // a; rewrite !inE; apply/bigcupP.
  by exists [set a]; rewrite ?inE //; apply/imsetP; exists a.
by apply: eq_bigr => a _; rewrite setIC.
Qed.

Definition fdist_cond : R.-fdist A := locked (FDist.make f0 f1).

End fdist_cond.

Section fdist_cond_prop.
Context {R : realType}.
Variables (A : finType) (P : R.-fdist A) (E : {set A}).

Hypothesis E0 : Pr P E != 0.

Lemma fdist_condE a : fdist_cond E0 a = `Pr_P [[set a] | E].
Proof. by rewrite /fdist_cond; unlock; rewrite ffunE. Qed.

Lemma Pr_fdist_cond G : Pr (fdist_cond E0) G = `Pr_P [ G | E ].
Proof.
rewrite /Pr; under eq_bigr do rewrite fdist_condE.
rewrite -big_distrl /=; congr (_ / _).
rewrite (_ : _ :&: _ = \bigcup_(i in G) ([set i] :&: E)); last first.
  by rewrite -big_distrl /= -bigcup_set1.
rewrite [in RHS]/Pr big_bigcup_partition // => i j ij.
rewrite -setI_eq0; apply/eqP/setP => a; rewrite !inE.
apply/negbTE; rewrite !negb_and.
have [->/=|//] := eqVneq a i.
by rewrite ij /= orbT.
Qed.

End fdist_cond_prop.

Lemma Pr_fdistX {R : realType} (A B : finType) (P : R.-fdist (A * B))
    (E : {set A}) (F : {set B}) :
  Pr (fdistX P) (F `* E) = Pr P (E `* F).
Proof.
rewrite /Pr !big_setX exchange_big /=; apply: eq_bigr => b _.
by apply: eq_bigr => a _; rewrite fdistXE.
Qed.

Lemma Pr_fdistA {R : realType} (A B C : finType) (P : R.-fdist (A * B * C)) E F G :
  Pr (fdistA P) (E `* (F `* G)) = Pr P (E `* F `* G).
Proof.
rewrite /fdistA (@Pr_fdistmap _ _ _ (@prodA A B C))// ?imsetA//.
exact: inj_prodA.
Qed.

Lemma Pr_fdistC12 {R : realType} (A B C : finType) (P : R.-fdist (A * B * C)) E F G :
  Pr (fdistC12 P) (E `* F `* G) = Pr P (F `* E `* G).
Proof.
rewrite /Pr !big_setX /= exchange_big; apply: eq_bigr => a aF.
by apply: eq_bigr => b bE; apply: eq_bigr => c cG; rewrite fdistC12E.
Qed.

Lemma Pr_fdistAC {R : realType} (A B C : finType) (P : R.-fdist (A * B * C)) E F G :
  Pr (fdistAC P) (E `* G `* F) = Pr P (E `* F `* G).
Proof. by rewrite /fdistAC Pr_fdistX Pr_fdistA Pr_fdistC12. Qed.

Lemma Pr_fdist_proj23_domin {R : realType} (A B C : finType)
    (P : R.-fdist (A * B * C)) E F G :
  Pr (fdist_proj23 P) (F `* G) = 0 -> Pr P (E `* F `* G) = 0.
Proof.
move/Pr_set0P => H; apply/Pr_set0P => -[[? ?] ?].
rewrite !inE /= -andbA => /and3P[aE bF cG].
by apply/fdist_proj23_domin/H; rewrite inE /= bF cG.
Qed.

Section conditionally_independent_events.
Context {R : realType}.
Variables (A : finType) (d : R.-fdist A).

Definition cinde_events (E F G : {set A}) :=
  `Pr_d[ E :&: F | G] = `Pr_d[E | G] * `Pr_d[F | G].

Lemma cinde_events_alt (E F G : {set A}) : cinde_events E F G <->
  `Pr_d[ E | F :&: G] = `Pr_d[E | G] \/ Pr d (F :&: G) = 0.
Proof.
split=> [|[|FG0]]; rewrite /cinde_events.
- rewrite product_rule_cond => H.
  have [/cPr_eq0P EG0|EG0] := eqVneq (`Pr_d[F | G]) 0.
    by rewrite /cPr EG0; right.
  by left; move: H => /mulIf; apply.
- by rewrite product_rule_cond => ->.
- by rewrite /cPr -setIA setIC Pr_domin_setI // !mul0r FG0 mul0r mulr0.
Qed.

Lemma cinde_events_unit (E F : {set A}) : inde_events d E F <->
  cinde_events E F setT.
Proof. by split; rewrite /cinde_events /inde_events !cPrET. Qed.

End conditionally_independent_events.

Section crandom_variable_eqType.
Context {R : realType}.
Variables (U : finType) (A B : eqType) (P : R.-fdist U).

Definition cPr_eq (X : {RV P -> A}) (a : A) (Y : {RV P -> B}) (b : B) :=
  locked (`Pr_P[ finset (X @^-1 a) | finset (Y @^-1 b)]).
Local Notation "`Pr[ X = a | Y = b ]" := (cPr_eq X a Y b).

Lemma cPr_eq_def (X : {RV P -> A}) (a : A) (Y : {RV P -> B}) (b : B) :
  `Pr[ X = a | Y = b ] = `Pr_P [ finset (X @^-1 a) | finset (Y @^-1 b) ].
Proof. by rewrite /cPr_eq; unlock. Qed.

End crandom_variable_eqType.
Notation "`Pr[ X = a | Y = b ]" := (cPr_eq X a Y b) : proba_scope.

Section cPr_eq_finType.
Context {R : realType}.
Variables (U : finType) (A B : finType) (P : R.-fdist U).

Lemma cPr_eq_finType (X : {RV P -> A}) (a : A) (Y : {RV P -> B}) (b : B) :
  `Pr[ X = a | Y = b ] = `Pr_P [ X @^-1: [set a] | Y @^-1: [set b] ].
Proof. by rewrite cPr_eq_def !preimg_set1. Qed.

End cPr_eq_finType.

#[deprecated(since="infotheo 0.7.2", note="renamed to `cPr_eq`")]
Notation cpr_eq0 := cPr_eq (only parsing).
#[deprecated(since="infotheo 0.7.2", note="renamed to `cPr_eq_def`")]
Notation cpr_eqE' := cPr_eq_def (only parsing).

(* TODO: sect *)
Lemma cpr_eq_unit_RV {R : realType} (U : finType) (A : eqType) (P : R.-fdist U)
    (X : {RV P -> A}) (a : A) :
  `Pr[ X = a | (unit_RV P) = tt ] = `Pr[ X = a ].
Proof. by rewrite cPr_eq_def cPrET pfwd1E. Qed.

Lemma cpr_eqE {R : realType} (U : finType) (P : R.-fdist U) (TA TB : eqType)
  (X : {RV P -> TA}) (Y : {RV P -> TB}) a b :
  `Pr[ X = a | Y = b ] = `Pr[ [% X, Y] = (a, b) ] / `Pr[Y = b].
Proof.
rewrite cPr_eq_def /cPr /dist_of_RV 2!pfwd1E; congr (Pr _ _ / _).
by apply/setP => u; rewrite !inE xpair_eqE.
Qed.

Lemma cPr_eq_id {R : realType} (T : finType) (U : eqType) (P : R.-fdist T)
(X : {RV P -> U}) (x : U) : `Pr[ X = x ] != 0 -> `Pr[ X = x | X = x ] = 1.
Proof. by move=> ?; rewrite cpr_eqE pfwd1_diag divff. Qed.

Section crandom_variable_finType.
Context {R : realType}.
Variables (U A B : finType) (P : R.-fdist U).
Implicit Types X : {RV P -> A}.

Definition cpr_in X (E : {set A}) (Y : {RV P -> B}) (F : {set B}) :=
  locked (`Pr_P [ X @^-1: E | Y @^-1: F ]).
Local Notation "`Pr[ X \in E | Y \in F ]" := (cpr_in X E Y F).

Lemma cpr_inE X (E : {set A}) (Y : {RV P -> B}) (F : {set B}) :
  `Pr[ X \in E | Y \in F ] = `Pr_P [ X @^-1: E | Y @^-1: F ].
Proof. by rewrite /cpr_in; unlock. Qed.

Lemma cpr_in1 X x (Y : {RV P -> B}) y :
  `Pr[ X \in [set x] | Y \in [set y] ] = `Pr[ X = x | Y = y ].
Proof.
by rewrite cpr_inE cPr_eq_def; congr cPr; apply/setP => u; rewrite !inE.
Qed.

End crandom_variable_finType.
Notation "`Pr[ X '\in' E | Y '\in' F ]" := (cpr_in X E Y F) : proba_scope.
Notation "`Pr[ X '\in' E | Y = b ]" :=
  (`Pr[ X \in E | Y \in [set b]]) : proba_scope.
Notation "`Pr[ X = a | Y '\in' F ]" :=
  (`Pr[ X \in [set a] | Y \in F]) : proba_scope.

#[deprecated(since="infotheo 0.9.2", note="renamed to `cpr_in`")]
Notation cpr_eq_set := cpr_in (only parsing).
#[deprecated(since="infotheo 0.9.2", note="renamed to `cpr_inE`")]
Notation cpr_eq_setE := cpr_inE (only parsing).
#[deprecated(since="infotheo 0.9.2", note="renamed to `cpr_in1`")]
Notation cpr_eq_set1 := cpr_in1 (only parsing).

Lemma cpr_in_unit_RV {R : realType} (U A : finType) (P : R.-fdist U) (X : {RV P -> A})
    (E : {set A}) :
  `Pr[ X \in E | (unit_RV P) = tt ] = `Pr[ X \in E ].
Proof.
rewrite cpr_inE (_ : _ @^-1: [set tt] = setT); last first.
  by apply/setP => u; rewrite !inE.
by rewrite cPrET pr_inE.
Qed.

Lemma cpr_inEdiv {R : realType} (U : finType) (P : R.-fdist U) (A B : finType)
    (X : {RV P -> A}) (Z : {RV P -> B}) E F :
  `Pr[X \in E | Z \in F] = `Pr[ [%X, Z] \in E `* F] / `Pr[Z \in F].
Proof.
rewrite /cpr_in; unlock.
rewrite !pr_inE /cPr; congr (Pr _ _ * _).
by apply/setP => u; rewrite !inE.
Qed.

Lemma cpr_inE' {R : realType} (U : finType) (P : R.-fdist U) (A B : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (E : {set A}) (F : {set B}) :
  `Pr[ X \in E | Y \in F ] = `Pr_(`p_ [% X, Y]) [E `*T | T`* F].
Proof.
rewrite cpr_inE /cPr /dist_of_RV; congr (_ / _).
  rewrite setTE EsetT setIX setIT setTI.
  by rewrite Pr_fdistmap_RV2.
by rewrite setTE Pr_fdistmap_RV2; congr Pr; apply/setP => u; rewrite !inE.
Qed.

Section cpr_pair.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (A B C D : finType) (TA TB TC TD : eqType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) (W : {RV P -> D}).
Variables (TX : {RV P -> TA}) (TY : {RV P -> TB}) (TZ : {RV P -> TC}) (TW : {RV P -> TD}).

Lemma cpr_eq_pairC a b c :
  `Pr[ [% TY, TX] = (b, a) | Z = c ] = `Pr[ [% TX, TY] = (a, b) | Z = c ].
Proof.
rewrite cpr_eqE.
rewrite pfwd1_pairC pfwd1_pairA pfwd1_pairAC -pfwd1_pairA pfwd1_pairC.
by rewrite -cpr_eqE.
Qed.

Lemma cpr_in_pairC E F G :
  `Pr[ [% Y, X] \in E `* F | Z \in G ] = `Pr[ [% X, Y] \in F `* E | Z \in G ].
Proof.
rewrite cpr_inEdiv.
rewrite pr_in_pairC pr_in_pairA pr_in_pairAC -pr_in_pairA pr_in_pairC.
by rewrite -cpr_inEdiv.
Qed.

Lemma cpr_eq_pairA a b c d :
  `Pr[ [% TX, [% TY, TZ]] = (a, (b, c)) | TW = d ] =
  `Pr[ [% TX, TY, TZ] = (a, b, c) | TW = d].
Proof.
rewrite 2!cPr_eq_def; congr (Pr _ _ / _).
by apply/setP => u; rewrite !inE /= !xpair_eqE andbA.
Qed.

Lemma cpr_in_pairA E F G H :
  `Pr[ [% X, [% Y, Z]] \in E `* (F `* G) | W \in H] =
  `Pr[ [% X, Y, Z] \in E `* F `* G | W \in H].
Proof.
rewrite 2!cpr_inEdiv; congr (_ / _).
rewrite !pr_inE' !Pr_fdistmap_RV2; congr Pr.
by apply/setP => u; rewrite !inE /= !andbA.
Qed.

Lemma cpr_eq_pairAr a b c d :
  `Pr[ TX = a | [% TY, [% TZ, TW]] = (b, (c, d)) ] =
  `Pr[ TX = a | [% TY, TZ, TW] = (b, c, d) ].
Proof.
rewrite 2!cpr_eqE; congr (_ / _).
rewrite !pfwd1E; congr Pr.
by apply/setP => u; rewrite !inE /= !xpair_eqE !andbA.
by rewrite pfwd1_pairA.
Qed.

Lemma cpr_in_pairAr E F G H :
  `Pr[ X \in E | [% Y, [% Z, W]] \in F `* (G `* H) ] =
  `Pr[ X \in E | [% Y, Z, W] \in F `* G `* H ].
Proof.
rewrite 2!cpr_inEdiv; congr (_ / _).
rewrite !pr_inE' !Pr_fdistmap_RV2; congr Pr.
by apply/setP => u; rewrite !inE /= !andbA.
by rewrite -pr_in_pairA.
Qed.

Lemma cpr_eq_pairAC a b c d :
  `Pr[ [% TX, TY, TZ] = (a, b, c) | TW = d ] =
  `Pr[ [% TX, TZ, TY] = (a, c, b) | TW = d ].
Proof.
rewrite 2!cpr_eqE; congr (_ / _).
rewrite !pfwd1E; congr Pr.
apply/setP => u; rewrite !inE /= !xpair_eqE /=; congr (_ && _).
by rewrite andbAC.
Qed.

Lemma cpr_in_pairAC E F G H :
  `Pr[ [% X, Y, Z] \in (E `* F `* G) | W \in H] =
  `Pr[ [% X, Z, Y] \in (E `* G `* F) | W \in H].
Proof.
rewrite 2!cpr_inEdiv; congr (_ / _).
rewrite !pr_inE' !Pr_fdistmap_RV2; congr Pr.
apply/setP => u; rewrite !inE /=; congr (_ && _).
by rewrite andbAC.
Qed.

Lemma cpr_eq_pairACr a b c d :
  `Pr[ TX = a | [% TY, TZ, TW] = (b, c, d) ] =
  `Pr[ TX = a | [% TY, TW, TZ] = (b, d, c) ].
Proof.
rewrite 2!cpr_eqE; congr (_ / _).
  rewrite !pfwd1E; congr Pr.
  apply/setP => u; rewrite !inE !xpair_eqE -!andbA; congr (_ && _).
  by rewrite !andbA andbAC.
by rewrite pfwd1_pairAC.
Qed.

Lemma cpr_in_pairACr E F G H :
  `Pr[ X \in E | [% Y, Z, W] \in F `* G `* H ] =
  `Pr[ X \in E | [% Y, W, Z] \in F `* H `* G ].
Proof.
rewrite 2!cpr_inEdiv; congr (_ / _).
rewrite !pr_inE' !Pr_fdistmap_RV2; congr Pr.
by apply/setP => u; rewrite !inE /= !andbA /= andbAC.
by rewrite pr_in_pairAC.
Qed.

Lemma cpr_eq_pairCr a b c :
  `Pr[ TX = a | [% TY, TZ] = (b, c) ] = `Pr[ TX = a | [% TZ, TY] = (c, b) ].
Proof.
rewrite 2!cpr_eqE; congr (_ / _).
  by rewrite pfwd1_pairA pfwd1_pairAC -pfwd1_pairA.
by rewrite pfwd1_pairC.
Qed.

Lemma cpr_in_pairCr E F G :
  `Pr[ X \in E | [% Y, Z] \in F `* G ] = `Pr[ X \in E | [% Z, Y] \in G `* F ].
Proof.
rewrite 2!cpr_inEdiv.
rewrite pr_in_pairA pr_in_pairAC -pr_in_pairA; congr (_ / _).
by rewrite pr_in_pairC.
Qed.

End cpr_pair.

Lemma cpr_eq_product_rule {R : realType} (U : finType) (P : R.-fdist U) (A B C : eqType)
  (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) a b c :
  `Pr[ [% X, Y] = (a, b) | Z = c ] =
  `Pr[ X = a | [% Y, Z] = (b, c) ] * `Pr[ Y = b | Z = c ].
Proof.
rewrite cPr_eq_def.
rewrite (_ : [set x | preim [% X, Y] (pred1 (a, b)) x] =
             finset (X @^-1 a) :&: finset (Y @^-1 b)); last first.
  by apply/setP => u; rewrite !inE xpair_eqE.
rewrite product_rule_cond cPr_eq_def; congr (cPr _ _ _ * _).
- by apply/setP=> u; rewrite !inE xpair_eqE.
- by rewrite cPr_eq_def.
Qed.

Lemma reasoning_by_cases {R : realType} (U : finType) (P : R.-fdist U)
  (A B : finType) (X : {RV P -> A}) (Y : {RV P -> B}) E :
  `Pr[ X \in E ] = \sum_(b <- fin_img Y) `Pr[ [% X, Y] \in (E `* [set b])].
Proof.
rewrite pr_inE.
have -> : X @^-1: E = \bigcup_d [% X, Y] @^-1: ((E `* [set d])).
  rewrite bigcup_preimset; apply/setP => u; rewrite !inE; apply/idP/bigcupP.
  by move=> XuE; exists (Y u) => //; rewrite !inE /= XuE /=.
  by case=> b _; rewrite !inE => /andP[] ->.
rewrite bigcup_preimset /Pr partition_big_preimset /=.
rewrite partition_disjoint_bigcup /=; last first.
  move=> i j ij; rewrite -setI_eq0; apply/eqP/setP => u; rewrite !inE.
  by apply/negbTE/negP=> /andP[] /andP[] -> /eqP -> /=; move/negP: ij; exact.
apply/esym; set F := BIG_F.
transitivity (\sum_(b in B) F b).
  rewrite [in RHS](bigID (mem (fin_img Y))) /=.
  rewrite [X in _ = _ + X]big1 ?addr0 //.
    by rewrite big_uniq // undup_uniq.
  by move=> b bY; rewrite {}/F pr_in_pairC pr_in_domin_RV2 // pr_in1 pfwd1_eq0.
by apply: eq_bigr => b _; rewrite /F pr_inE /Pr partition_big_preimset.
Qed.

Lemma creasoning_by_cases {R : realType} (U : finType) (P : R.-fdist U)
  (A B C : finType) (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}) E F :
  `Pr[ X \in E | Z \in F ] = \sum_(b <- fin_img Y) `Pr[ [% X, Y] \in (E `* [set b]) | Z \in F].
Proof.
rewrite cpr_inEdiv; under eq_bigr do rewrite cpr_inEdiv.
rewrite -big_distrl /= (reasoning_by_cases _ Y); congr (_ / _).
by apply: eq_bigr => b _; rewrite pr_in_pairAC.
Qed.

Section conditionnally_independent_discrete_RVs.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (A B C : eqType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).

Definition cinde_RV := forall a b c,
  `Pr[ [% X, Y] = (a, b) | Z = c ] = `Pr[ X = a | Z = c ] * `Pr[ Y = b | Z = c].

Lemma cinde_RV_events : cinde_RV <-> (forall x y z,
  cinde_events P (finset (X @^-1 x)) (finset (Y @^-1 y)) (finset (Z @^-1 z))).
Proof.
split=> [H /= x y z|/= H x y z].
- rewrite /cinde_events -2!cPr_eq_def -H cPr_eq_def; congr cPr.
  by apply/setP => /= ab; rewrite !inE.
- rewrite (cPr_eq_def _ x) (cPr_eq_def _ y) -H cPr_eq_def; congr cPr.
  by apply/setP => /= ab; rewrite !inE.
Qed.

End conditionnally_independent_discrete_RVs.
Notation "P |= X _|_  Y | Z" := (@cinde_RV _ _ P _ _ _ X Y Z) : proba_scope.
Notation "X _|_  Y | Z" := (cinde_RV X Y Z) : proba_scope.
#[deprecated(since="infotheo 0.9.2", note="renamed to `cinde_RV`")]
Notation cinde_rv := cinde_RV (only parsing).
#[deprecated(since="infotheo 0.9.2", note="renamed to `cinde_RV_events`")]
Notation cinde_rv_events := cinde_RV_events (only parsing).

Section cinde_RV_sym.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (A B C : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).

Lemma cinde_RV_sym : X _|_ Y | Z -> Y _|_  X | Z.
Proof. by move=> H a b c; rewrite mulrC cpr_eq_pairC. Qed.

End cinde_RV_sym.
#[deprecated(since="infotheo 0.9.2", note="renamed to `cinde_RV_sym`")]
Notation cinde_rv_sym := cinde_RV_sym (only parsing).

Section independent_rv.
Context {R : realType}.
Variables (A : finType) (P : R.-fdist A) (TA TB : eqType).
Variables (X : {RV P -> TA}) (Y : {RV P -> TB}).

Definition inde_RV := forall x y,
  `Pr[ [% X, Y] = (x, y)] = `Pr[ X = x ] * `Pr[ Y = y ].

Lemma cinde_RV_unit : inde_RV <-> cinde_RV X Y (unit_RV P).
Proof.
split => [H a b []|H a b]; first by rewrite !cpr_eq_unit_RV H.
by have := H a b tt; rewrite !cpr_eq_unit_RV.
Qed.

Lemma inde_RV_events : inde_RV <->
  (forall x y, inde_events P (finset (X @^-1 x)) (finset (Y @^-1 y))).
Proof.
split => [/cinde_RV_unit/cinde_RV_events H a b|H].
  exact/cinde_events_unit/(H _ _ tt).
by apply/cinde_RV_unit/cinde_RV_events => a b []; exact/cinde_events_unit/H.
Qed.

End independent_rv.
Notation "P |= X _|_ Y" := (@inde_RV _ _ P _ _ X Y) : proba_scope.
#[deprecated(since="infotheo 0.9.2", note="renamed to `inde_RV`")]
Notation inde_rv := inde_RV (only parsing).
#[deprecated(since="infotheo 0.9.2", note="renamed to `cinde_RV_unit`")]
Notation cinde_rv_unit := cinde_RV_unit (only parsing).
#[deprecated(since="infotheo 0.9.2", note="renamed to `inde_RV_events`")]
Notation inde_rv_events := inde_RV_events (only parsing).

Section inde_RVP.
Context {R : realType}.
Variables (A : finType) (P : R.-fdist A) (TA TB : finType).
Variables (X : {RV P -> TA}) (Y : {RV P -> TB}).

Lemma inde_RVP : P |= X _|_ Y <-> forall E F,
  `Pr[ [% X, Y] \in E `* F] = `Pr[ X \in E ] * `Pr[ Y \in F ].
Proof.
split=> [PXY|H]; last by move=> *; rewrite -!pr_in1 -H setX1.
move=> E F; rewrite !pr_inE'.
rewrite [LHS]/Pr; under eq_bigr=> *.
  rewrite fdistmapE.
  under eq_bigl do rewrite !inE /=.
  over.
rewrite [in RHS]/Pr big_distrl /=.
under [RHS]eq_bigr=> i ?.
  rewrite big_distrr /=.
  under eq_bigr do rewrite !dist_of_RVE -PXY -dist_of_RVE.
  over.
by rewrite -big_setX; apply: eq_bigr=> *; rewrite fdistmapE.
Qed.

End inde_RVP.

Section inde_RV_comp.
Context {R : realType}.
Variables (A : finType) (P : R.-fdist A).

(* Origin: Lemma 3.1 in
  "Information-Theoretically Secure Number-Product Protocol."
  by Shen et al., 2007.
  https://doi.org/10.1109/ICMLC.2007.4370663.
*)
Lemma inde_RV_comp (TA TB UA UB : finType) (X : {RV P -> TA}) (Y : {RV P -> TB})
    (f : TA -> UA) (g : TB -> UB) :
  P |= X _|_ Y -> P|= (f `o X) _|_ (g `o Y).
Proof.
move=> /inde_RVP inde_XY; apply/inde_RVP => E F.
by rewrite (pr_in_comp' f) (pr_in_comp' g) -inde_XY -preimsetX -pr_in_comp'.
Qed.

End inde_RV_comp.

Section inde_RV_sym.
Context {R : realType}.
Variables (A : finType) (P : R.-fdist A) (TA TB: finType).
Variables (X : {RV P -> TA}) (Y : {RV P -> TB}).

Lemma inde_RV_sym : P |= X _|_ Y <-> P |= Y _|_ X.
Proof. by split => /cinde_RV_unit/cinde_RV_sym/cinde_RV_unit. Qed.

End inde_RV_sym.

(* We put the following section here because it uses reasoning_by_cases and
   the independence notation. *)
Section pfwd1_RV_op.
Context {R : realType}.
Variables (A : finType) (P : R.-fdist A) (TX1 TX2 TY : finType).
Variables (X1 : {RV P -> TX1}) (X2 : {RV P -> TX2}) (Y: {RV P -> TY}).
Variable op : TX1 -> TX2 -> TY.

Definition RV_op (A : {RV P -> TX1}) (B : {RV P -> TX2}) : {RV P -> TY} :=
  uncurry op `o [% A, B].

Hypothesis X1_X2_inde : P|= X1 _|_ X2.
Hypothesis X1X2_Y_inde : P|= [%X1, X2] _|_ Y.

Lemma pfwd1_RV_op y : `Pr[ (RV_op X1 X2) = y ] =
  \sum_(x1 <- fin_img X1)
    (\sum_(x2 <- fin_img X2 | op x1 x2 == y) `Pr[ X1 = x1 ] * `Pr[ X2 = x2]).
Proof.
rewrite -[LHS]pr_in1 (reasoning_by_cases _ X1).
apply: eq_bigr => x1 _.
rewrite (reasoning_by_cases _ X2) [RHS]big_mkcond /=.
apply: eq_bigr => x2 _.
case: ifPn => [/eqP <-|x1x2y].
  rewrite -X1_X2_inde 2!setX1 pr_in1.
  pose f (p : TX1 * TX2) := (op p.1 p.2, p.1, p.2).
  by have /pfwd1_comp <-: injective f by move => [a b] [? ?] [] _ -> ->.
rewrite 2!setX1 pr_in1 pfwd1_eq0//.
apply: contra x1x2y.
by rewrite fin_img_imset => /imsetP[a0 _ [] -> -> ->].
Qed.

Lemma pfwd1_RV2_op y1 y2 : `Pr[ [%(RV_op X1 X2), Y] = (y1, y2) ] =
  \sum_(x1 <- fin_img X1)
    (\sum_(x2 <- fin_img X2 | op x1 x2 == y1)
      `Pr[ X1 = x1 ] * `Pr[ X2 = x2 ] * `Pr[ Y = y2 ]).
Proof.
rewrite (inde_RV_comp _ idfun)//.
under eq_bigr do rewrite -big_distrl /=.
by rewrite -big_distrl /= -pfwd1_RV_op.
Qed.

End pfwd1_RV_op.

Lemma cinde_alt {R : realType} (U : finType) (P : R.-fdist U) (A B C : finType)
    (X : {RV P -> A}) (Y : {RV P -> B}) {Z : {RV P -> C}} a b c :
  P |= X _|_ Y | Z ->
  `Pr[ [% Y, Z] = (b, c)] != 0 ->
  `Pr[ X = a | [% Y, Z] = (b, c)] = `Pr[X = a | Z = c].
Proof.
move=> K H0.
rewrite [in LHS]cpr_eqE; apply: (@mulIf _ _ H0).
rewrite -mulrA mulVf ?mulr1//.
have H1 : (`Pr[ Z = c ])^-1 != 0.
  apply: invr_neq0; rewrite pfwd1_pairC in H0.
  by apply: contra H0 => /eqP/(pfwd1_domin_RV2 Y b)/eqP.
rewrite pfwd1_pairA; apply: (@mulIf _ _ H1).
by rewrite -mulrA -!cpr_eqE K.
Qed.

Section sum_two_rand_var_def.
Context {R : realType} {V : lmodType R}.
Variables (A : finType) (n : nat).
Variables (X : 'rV[A]_n.+2 -> V) (X1 : A -> V) (X2 : 'rV[A]_n.+1 -> V).

Local Open Scope vec_ext_scope.

Definition sum_2 := X =1 fun x => X1 (x ``_ ord0) + X2 (rbehead x).

End sum_two_rand_var_def.

Notation "Z \= X '@+' Y" := (sum_2 Z X Y) : proba_scope.

Section sum_two_rand_var.
Context {R : realType}.
Local Open Scope vec_ext_scope.

Variables (A : finType) (n : nat) (P : R.-fdist 'rV[A]_n.+2) (X : {RV P -> R}).
Let P1 := head_of_fdist_rV P.
Let P2 := tail_of_fdist_rV P.
Variables (X1 : {RV P1 -> R}) (X2 : {RV P2 -> R}).

Let X1' : {RV P -> R} := fun x => X1 (x ``_ ord0).
Let X2' : {RV P -> R} := fun x => X2 (rbehead x).

Lemma E_sum_2 : X \= X1 @+ X2 -> `E X = `E X1 + `E X2.
Proof.
move=> Hsum; transitivity (\sum_(ta in 'rV[A]_n.+2)
  (P ta *: X1 (ta ``_ ord0) + P ta *: X2 (rbehead ta))).
  by apply: eq_bigr => ta _; rewrite Hsum scalerDr.
rewrite big_split => //=; congr (_ + _).
- transitivity (\sum_(a in A)
    (\sum_(ta in 'rV_n.+1) (fdist_prod_of_rV P (a, ta))) *: X1 a).
  + rewrite -(big_rV_cons_behead _ xpredT xpredT); apply: eq_bigr => a _.
    rewrite scaler_suml /=; apply: eq_bigr => i _.
    by rewrite row_mx_row_ord0 fdist_prod_of_rVE.
  + by apply: eq_bigr => a _; rewrite fdist_fstE.
- transitivity (\sum_(ta in 'rV_n.+1)
    (\sum_(a in A) (fdist_prod_of_rV P (a, ta))) *: X2 ta).
  + rewrite -(big_rV_cons_behead _ xpredT xpredT) exchange_big /=.
    apply: eq_bigr => ta _; rewrite scaler_suml /=.
    by apply: eq_bigr => a _; rewrite rbehead_row_mx fdist_prod_of_rVE.
  + by apply: eq_bigr => ta _; rewrite fdist_sndE.
Qed.

End sum_two_rand_var.

Section prod_two_rand_var.
Local Open Scope vec_ext_scope.
Context {R : realType}.
Variables (A : finType) (n : nat) (P : R.-fdist 'rV[A]_n.+2) (X : {RV P -> R}).
Let P1 := head_of_fdist_rV P.
Let P2 := tail_of_fdist_rV P.
Variables (X1 : {RV P1 -> R}) (X2 : {RV P2 -> R}).

Let X1' : {RV P -> R} := fun x => X1 (x ``_ ord0).
Let X2' : {RV P -> R} := fun x => X2 (rbehead x).

Lemma E_id_rem_helper : X \= X1 @+ X2 ->
  P |= X1' _|_ X2' ->
  \sum_(i in 'rV[A]_n.+2) (X1 (i ``_ ord0) * X2 (rbehead i) * P i) =
    `E X1 * `E X2.
Proof.
move=> Hsum Hinde.
rewrite -!Ex_altE.
transitivity (\sum_(r <- undup (map X1 (enum A)))
   \sum_(r' <- undup (map X2 (enum ('rV[A]_n.+1))))
   ( r * r' * `Pr[X1 = r] * `Pr[X2 = r'])); last first.
  rewrite [in RHS]big_distrl /=; apply: eq_bigr => i _.
  rewrite big_distrr /=; apply: eq_bigr => j _.
  rewrite -!mulr_regl; apply: esym.
  by rewrite mulrAC mulrA -mulrA (mulrC i) [LHS]mulrC mulrA.
rewrite -(big_rV_cons_behead _ xpredT xpredT) /=.
transitivity (\sum_(a in A) \sum_(j in 'rV[A]_n.+1)
  (X1 a * X2 j * P (row_mx (\row_(k < 1) a) j))).
  apply: eq_bigr => a _; apply: eq_bigr => ta _.
  by rewrite row_mx_row_ord0 rbehead_row_mx.
rewrite (partition_big_undup_map _ X1); last first.
  by rewrite /index_enum -enumT; apply: enum_uniq.
rewrite /index_enum -enumT.
apply: eq_bigr => /= r _.
rewrite {1}enumT exchange_big /= (partition_big_undup_map _ X2); last first.
  by rewrite /index_enum -enumT; apply: enum_uniq.
rewrite /index_enum -enumT.
apply: eq_bigr => /= r' _.
transitivity (r * r' * \sum_(i0 | X2 i0 == r') \sum_(i1 | X1 i1 == r)
    (P (row_mx (\row_(k < 1) i1) i0))).
  rewrite big_distrr /= /index_enum -!enumT; apply: eq_bigr => ta ta_r'.
  rewrite big_distrr /=; apply: eq_bigr => a a_l.
  move/eqP : ta_r' => <-.
  by move/eqP : a_l => <-.
rewrite -[RHS]mulrA; congr (_ * _).
rewrite exchange_big /=.
have {}Hinde := Hinde r r'.
have -> : `Pr[ X1 = r ] = `Pr[ X1' = r ].
  rewrite 2!pfwd1E /P1 /head_of_fdist_rV Pr_fdist_fst Pr_fdist_prod_of_rV1; congr Pr.
  by apply/setP => /= v; rewrite !inE /X1'.
have -> : `Pr[ X2 = r' ] = `Pr[ X2' = r' ].
  rewrite 2!pfwd1E /P1 /tail_of_fdist_rV Pr_fdist_snd Pr_fdist_prod_of_rV2; congr Pr.
  by apply/setP => /= v; rewrite !inE /X2'.
rewrite -Hinde.
rewrite pfwd1E /ambient_dist /Pr.
transitivity (\sum_(a : 'rV_n.+2 | (X1 (a ``_ ord0) == r) && (X2 (rbehead a) == r')) P a).
  by rewrite -(big_rV_cons_behead _ [pred x | X1 x == r] [pred x | X2 x == r']) /=.
apply: eq_bigl => /= v.
by rewrite /X1' /X2' !inE /RV2 xpair_eqE.
Qed.

Lemma E_id_rem : X \= X1 @+ X2 -> P |= X1' _|_ X2' ->
  `E (X `^2) = `E (X1 `^2) + 2 * `E X1 * `E X2 + `E (X2 `^2).
Proof.
move=> Hsum Hinde.
rewrite -![in RHS]Ex_altE.
transitivity (\sum_(i in 'rV_n.+2)
  P i *: ((X1 (i ``_ ord0) + X2 (rbehead i)) ^+ 2%N)).
  apply: eq_bigr => i _; rewrite !RV_fctE/=.
  by rewrite /comp_RV Hsum.
transitivity (\sum_(i in 'rV_n.+2) P i * ((X1 (i ``_ ord0)) ^+ 2 +
    2 * X1 (i ``_ ord0) * X2 (rbehead i) + (X2 (rbehead i)) ^+ 2)).
  by apply: eq_bigr => ? _; rewrite sqrrD -mulrA mulr_natl -!mulr_regl.
transitivity (\sum_(i in 'rV_n.+2) ((X1 (i ``_ ord0)) ^+ 2 * P i + 2 *
  X1 (i ``_ ord0) * X2 (rbehead i) * P i + (X2 (rbehead i)) ^+ 2 * P i)).
  by apply: eq_bigr => ? ?; lra.
rewrite !big_split /=; congr (_ + _ + _).
- rewrite Ex_altE -(big_rV_cons_behead _ xpredT xpredT) /=.
  apply: eq_bigr => i _.
  transitivity (X1 i ^+ 2 * \sum_(j in 'rV_n.+1) (fdist_prod_of_rV P) (i, j)).
  + rewrite big_distrr /=; apply: eq_bigr => i0 _.
    by rewrite row_mx_row_ord0 fdist_prod_of_rVE.
  + by rewrite fdist_fstE/= -mulr_regl mulrC.
- rewrite -mulrA.
  rewrite !Ex_altE.
  rewrite -E_id_rem_helper // big_distrr /=.
  by apply: eq_bigr => i _; lra.
- rewrite Ex_altE -(big_rV_cons_behead _ xpredT xpredT) exchange_big /=.
  apply: eq_bigr => t _.
  transitivity (X2 t ^+ 2 * \sum_(i in A) (fdist_prod_of_rV P) (i, t)).
  + rewrite big_distrr /=; apply: eq_bigr => i _.
    by rewrite rbehead_row_mx fdist_prod_of_rVE.
  + by rewrite mulrC; congr (_ * _); rewrite fdist_sndE.
Qed.

Lemma V_sum_2 : X \= X1 @+ X2 -> P |= X1' _|_ X2'  ->
  `V X = `V X1 + `V X2.
Proof.
move=> H ?; rewrite !VarE E_id_rem // (E_sum_2 H) sqrrD.
by rewrite /Ex /= -/P1 -/P2; lra.
Qed.

End prod_two_rand_var.

Section expected_value_of_the_product.

Section thm64.
Context {R : realType}.
Variables (A B : finType) (P : R.-fdist (A * B)).
Variables (X : {RV (P`1) -> R}) (Y : {RV (P`2) -> R}).

Let XY : {RV P -> (R * R)%type} := (fun x => (X x.1, Y x.2)).
Let XmY : {RV P -> R} := (fun x => X x.1 * Y x.2).

Let X' : {RV P -> R} := fun x => X x.1.
Let Y' : {RV P -> R} := fun x => Y x.2.

Lemma E_prod_2 : P |= X' _|_ Y' -> `E XmY = `E X * `E Y.
Proof.
move=> Hinde.
transitivity (\sum_(x <- fin_img X) \sum_(y <- fin_img Y)
    `Pr[ XY = (x, y) ] *: (x * y)).
  rewrite /Ex /= (eq_bigr (fun u => P (u.1, u.2) *: (X u.1 * Y u.2))); last by case.
  rewrite -(pair_bigA _ (fun u1 u2 => P (u1, u2) *: (X u1 * Y u2))) /=.
  rewrite (partition_big_fin_img _ X) /=; apply: eq_bigr => x _.
  rewrite exchange_big /= (partition_big_fin_img _ Y) /=; apply: eq_bigr => y _.
  rewrite pfwd1E /Pr scaler_suml /= exchange_big pair_big /=.
  apply: eq_big.
    by move=> -[a b] /=; rewrite inE.
  by case=> a b /= /andP[/eqP -> /eqP ->].
transitivity (\sum_(x <- fin_img X) \sum_(y <- fin_img Y)
    `Pr[ X = x ] * `Pr[ Y = y ] *: (x * y)).
  apply: eq_bigr => x _; apply: eq_bigr => y _.
  rewrite -!mulr_regl.
  have {}Hinde := Hinde x y.
  congr (_ * (_ * _)).
  transitivity (`Pr[ X' = x ] * `Pr[ Y' = y ]); last first.
    congr (_ * _).
      rewrite !pfwd1E Pr_fdist_fst; congr Pr.
      by apply/setP => -[a b]; rewrite !inE.
    rewrite !pfwd1E Pr_fdist_snd; congr Pr.
    by apply/setP => -[a b]; rewrite !inE.
  by rewrite -Hinde !pfwd1E.
rewrite -!Ex_altE.
rewrite /Ex_alt big_distrl; apply: eq_bigr => x _ /=; rewrite big_distrr /=.
apply: eq_bigr=> y _.
by rewrite -mulrA (mulrCA x) -mulr_regl !mulrA.
Qed.

End thm64.

End expected_value_of_the_product.

Section sum_n_rand_var_def.
Context {R : realType}.
Variables (A : finType) (P : R.-fdist A).

Inductive sum_n : forall n, {RV (P `^ n) -> R} -> 'rV[{RV P -> R}]_n -> Prop :=
| sum_n_1 : forall X, sum_n (cast_fun_rV10 X) X
| sum_n_cons : forall n (Xs : 'rV_n.+1) Y X Z,
  Y \=sum Xs -> Z \= X @+ Y -> Z \=sum (row_mx (\row_(k < 1) X) Xs)
where "X '\=sum' Xs" := (sum_n X Xs) : proba_scope.

End sum_n_rand_var_def.

Notation "X '\=sum' Xs" := (sum_n X Xs) : proba_scope.

Section inde_RV_lemma.
Context {R : realType}.

Section prod_dist_inde_RV.
Variables (A B : finType) (P1 : R.-fdist A) (P2 : R.-fdist B) (TA TB : eqType).
Variable (X : {RV P1 -> TA}) (Y : {RV P2 -> TB}).
Let P := P1 `x P2.
Let X' : {RV P -> TA} := fun x => X x.1.
Let Y' : {RV P -> TB} := fun x => Y x.2.
Let XY : {RV P -> (TA * TB)%type} := fun x => (X' x, Y' x).

Lemma prod_dist_inde_RV : P |= X' _|_ Y'.
Proof.
apply/inde_RV_events => x y.
rewrite (_ : [set _ | _ ] = finset (X @^-1 x) `*T); last first.
  by apply/setP => -[a b]; rewrite !inE.
rewrite (_ : [set x | preim Y' (pred1 y) x] = T`* finset (Y @^-1 y)); last first.
  by apply/setP => -[a b]; rewrite !inE.
by rewrite /P /inde_events -Pr_fdist_prod.
Qed.

End prod_dist_inde_RV.

Lemma inde_dist_of_RV2 (A B C : finType) (P : R.-fdist A)
  (X : {RV P -> B}) (Y : {RV P -> C}) :
  P |= X _|_ Y -> `p_[% X, Y] = `p_ X `x `p_ Y.
Proof.
move=> PXY; apply: fdist_ext => -[x y] /=.
by rewrite fdist_prodE/= !dist_of_RVE PXY.
Qed.

End inde_RV_lemma.
#[deprecated(since="infotheo 0.9.2", note="renamed to `prod_dist_inde_RV`")]
Notation prod_dist_inde_rv := prod_dist_inde_RV (only parsing).

Local Open Scope vec_ext_scope.
Lemma prod_dist_inde_RV_rV {R : realType} (A : finType) (P : R.-fdist A)
    n (X : A -> R) (Y : {RV (P `^ n) -> R}) x y :
  `Pr[ ([% (fun v => X v ``_ ord0) : {RV (P`^n.+1) -> _},
           (fun v => Y (rbehead v) : _ )]) = (x, y) ] =
  `Pr[ ((fun v => X v ``_ ord0) : {RV (P`^n.+1) -> _}) = x ] *
  `Pr[ ((fun v => Y (rbehead v)) : {RV (P`^n.+1) -> _}) = y ].
Proof.
have /= := @prod_dist_inde_RV _ _ _ P (P `^ n) _ _ X Y x y.
rewrite !pfwd1E -!fdist_prod_of_fdist_rV.
rewrite (_ : [set x0 | _] =
    finset (X @^-1 x) `* finset (Y @^-1 y))%set; last first.
  by apply/setP => -[a b]; rewrite !inE /= xpair_eqE.
rewrite Pr_fdist_prod_of_rV
    (_ : [set x0 | _] = finset (X @^-1 x) `*T); last first.
  by apply/setP => a; rewrite !inE.
rewrite Pr_fdist_prod_of_rV1.
rewrite (_ : [set x0 | _] = T`* finset (Y @^-1 y)); last first.
  by apply/setP => a; rewrite !inE.
move=> Hinde.
apply: eq_trans.
  apply: eq_trans; last exact: Hinde.
  by congr Pr; apply/setP => v; rewrite !inE xpair_eqE.
by rewrite Pr_fdist_prod_of_rV2; congr (Pr _ _ * Pr (P `^ n.+1) _);
  apply/setP => v; rewrite !inE.
Qed.
Local Close Scope vec_ext_scope.
#[deprecated(since="infotheo 0.9.2", note="renamed to `prod_dist_inde_RV_rV`")]
Notation prod_dist_inde_rv_vec := prod_dist_inde_RV_rV (only parsing).

Section sum_n_rand_var.
Context {R : realType}.
Variable (A : finType) (P : R.-fdist A).

Local Open Scope vec_ext_scope.

Lemma E_sum_n : forall n (Xs : 'rV[{RV P -> R}]_n) (X : {RV (P `^ n) -> R}),
  X \=sum Xs -> `E X = \sum_(i < n) `E (Xs ``_ i).
Proof.
have inj_pair2_nat := Eqdep_dec.inj_pair2_eq_dec _ Peano_dec.eq_nat_dec.
elim => [Xs Xbar | [_ Xs Xbar | n IHn Xs Xbar] ].
- by inversion 1.
- inversion 1; subst.
  have XbarE := inj_pair2_nat _ _ _ _ H0.
  have XsE := inj_pair2_nat _ _ _ _ H1.
  subst Xs Xbar.
  by rewrite big_ord_recl big_ord0 addr0 E_cast_RV_fdist_rV1.
- inversion 1; subst.
  have XbarE := inj_pair2_nat _ _ _ _ H1.
  have XsE := inj_pair2_nat _ _ _ _ H2.
  subst Z Xs.
  rewrite big_ord_recl.
  rewrite [X in _ = _ + X](_ : _ = \sum_(i < n.+1) `E (Xs0 ``_ i : {RV P -> R})); last first.
    apply: eq_bigr => i _ /=.
    apply: eq_bigr => a _ /=.
    rewrite (_ : lift _ _ = rshift 1 i); last exact: val_inj.
    by rewrite (@row_mxEr _ _ 1).
  rewrite -(IHn _ _ H3) (E_sum_2 H4) row_mx_row_ord0.
  by rewrite /Ex head_of_fdist_rV_fdist_rV tail_of_fdist_rV_fdist_rV.
Qed.

Lemma V_sum_n : forall n (X : {RV (P `^ n) -> R}) (Xs : 'rV[{RV P -> R}]_n),
  X \=sum Xs ->
  forall sigma2, (forall i, `V (Xs ``_ i) = sigma2) ->
  `V X = n%:R * sigma2.
Proof.
have inj_pair2_nat := Eqdep_dec.inj_pair2_eq_dec _ Peano_dec.eq_nat_dec.
elim=> [X Xs X_Xs sigma2 Hsigma2|].
  by inversion X_Xs.
case=> [_ | n IH] Xsum Xs Hsum s Hs.
- inversion Hsum.
  have XsumE := inj_pair2_nat _ _ _ _ H.
  have XsE := inj_pair2_nat _ _ _ _ H0.
  subst Xs Xsum.
  by rewrite Var_cast_RV_fdist_rV1 mul1r.
- move: Hsum; inversion 1.
  have XsumE := inj_pair2_nat _ _ _ _ H0.
  have XsE := inj_pair2_nat _ _ _ _ H1.
  subst Z n0 Xs.
  move: {IH}(IH Y _ H2) => IH.
  rewrite -[in RHS](add2n n) mulrDl -IH.
  + rewrite mul1r (V_sum_2 H3) //; last exact: prod_dist_inde_RV_rV.
    rewrite -(Hs ord0) /= row_mx_row_ord0 // head_of_fdist_rV_fdist_rV.
    by rewrite tail_of_fdist_rV_fdist_rV.
  + move=> i; rewrite -(Hs (lift ord0 i)).
    congr (`V _).
    rewrite (_ : lift _ _ = rshift 1 i); last exact: val_inj.
    by rewrite (@row_mxEr _ _ 1).
Qed.

Lemma Var_average n (X : {RV (P `^ n) -> R}) Xs (sum_Xs : X \=sum Xs) :
  forall sigma2, (forall i, `V (Xs ``_ i) = sigma2) ->
  n%:R * `V (X `/ n) = sigma2.
Proof.
move=> s Hs; destruct n; first by inversion sum_Xs.
rewrite (Var_scale X) // (V_sum_n sum_Xs Hs) //.
rewrite mulrCA (mulrA _ _ s) -expr2.
by rewrite exprVn mulrA mulVf ?mul1r// sqrf_eq0 pnatr_eq0.
Qed.

End sum_n_rand_var.

Section weak_law_of_large_numbers.
Context {R : realType}.
Local Open Scope vec_ext_scope.

Variables (A : finType) (P : R.-fdist A) (n : nat).
Variable Xs : 'rV[{RV P -> R}]_n.+1.
Variable miu : R.
Hypothesis E_Xs : forall i, `E (Xs ``_ i) = miu.
Variable sigma2 : R.
Hypothesis V_Xs : forall i, `V (Xs ``_ i) = sigma2.
Variable X : {RV (P `^ n.+1) -> R}.
Variable X_Xs : X \=sum Xs.

Import Num.Def.

Lemma wlln epsilon : 0 < epsilon ->
  `Pr[ (normr `o ((X `/ n.+1) `-cst miu)) >= epsilon ] <=
    sigma2 / (n.+1%:R * epsilon ^+ 2).
Proof.
move=> e0.
rewrite invfM//.
rewrite mulrA.
have <- : `V (X `/ n.+1) = sigma2 / n.+1%:R.
  rewrite -(Var_average X_Xs V_Xs) Var_scale //.
  by rewrite [RHS]mulrC (mulrA _ n.+1%:R) mulVf ?pnatr_eq0// !mul1r.
have <- : `E (X `/ n.+1) = miu.
  rewrite E_scale_RV (E_sum_n X_Xs) -mulr_regl.
  rewrite mulrC eqr_divrMr ?pnatr_eq0// (eq_bigr (fun=> miu)) //.
  by rewrite big_const /= iter_addr cardE /= size_enum_ord addr0 mulr_natr.
move/le_trans: (chebyshev_inequality (X `/ n.+1) e0); apply.
by rewrite lexx.
Qed.

End weak_law_of_large_numbers.

(** wip: *)
Section vector_of_RVs.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).
Variables (A : finType) (n : nat) (X : 'rV[{RV P -> A}]_n).
Local Open Scope ring_scope.
Local Open Scope vec_ext_scope.
Definition RVn : {RV P -> 'rV[A]_n} := fun x => \row_(i < n) (X ``_ i) x.
End vector_of_RVs.

Section prob_chain_rule.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (A : finType).
Local Open Scope vec_ext_scope.

Lemma prob_chain_rule : forall (n : nat) (X : 'rV[{RV P -> A}]_n.+1) x,
  `Pr[ (RVn X) = x ] =
  \prod_(i < n.+1)
    if i == ord0 then
      `Pr[ (X ``_ ord0) = (x ``_ ord0)   ]
    else
      `Pr[ (X ``_ i) = (x ``_ i) |
        (RVn (row_drop (inord (n - i.+1)) X)) = (row_drop (inord (n - i.+1)) x) ].
Proof.
elim => [X /= x|n ih X /= x].
  rewrite big_ord_recl big_ord0 mulr1.
  (* TODO: lemma *)
  rewrite /pfwd1; unlock.
  apply: eq_bigl => u.
  rewrite !inE /RVn.
  apply/eqP/eqP => [<-|H]; first by rewrite mxE.
  by apply/rowP => i; rewrite {}(ord1 i) !mxE.
rewrite big_ord_recr /=.
Abort.

End prob_chain_rule.
