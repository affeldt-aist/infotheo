(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect all_algebra fingroup lra.
From mathcomp Require boolp.
From mathcomp Require Import unstable mathcomp_extra reals exp.
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
(*                         distribution P where T is an eqType                *)
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
Reserved Notation "{ 'RV' d -> T }" (at level 0, d, T at next level,
  format "{ 'RV'  d  ->  T }").
Reserved Notation "`p_ X" (at level 5).
Reserved Notation "`Pr[ X = a ]" (at level 6, X, a at next level,
  format "`Pr[  X  =  a  ]").
Reserved Notation "`Pr[ X '\in' E ]" (at level 6, X, E at next level,
  format "`Pr[  X  '\in'  E  ]").
Reserved Notation "`Pr[ X >= r ]" (at level 6, X, r at next level,
  format "`Pr[  X  >=  r  ]").
Reserved Notation "`Pr[ X <= r ]" (at level 6, X, r at next level,
  format "`Pr[  X  <=  r  ]").
Reserved Notation "k `cst* X" (at level 49).
Reserved Notation "X `*cst k" (at level 49).
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
Reserved Notation "`Pr[ X = a | Y = b ]" (at level 6, X, Y, a, b at next level,
  format "`Pr[  X  =  a  |  Y  =  b  ]").
Reserved Notation "`Pr[ X '\in' E | Y '\in' F ]" (at level 6, X, Y, E, F at next level,
  format "`Pr[  X  '\in'  E  |  Y  '\in'  F  ]").
Reserved Notation "`Pr[ X '\in' E | Y = F ]" (at level 6, X, Y, E, F at next level,
  format "`Pr[  X  '\in'  E  |  Y  =  F  ]").
Reserved Notation "`Pr[ X = E | Y '\in' F ]" (at level 6, X, Y, E, F at next level,
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

Import Order.POrderTheory GRing.Theory Num.Theory.

(* TODO: mv *)
Lemma m1powD {R : ringType} k : k <> 0%nat -> (-1) ^+ (k-1) = - (-1) ^+ k :> R.
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
by rewrite -(FDist.f1 P); apply eq_bigl => /= a; rewrite !inE /= orbN.
Qed.

Lemma Pr_to_cplt E : Pr E = 1 - Pr (~: E).
Proof. by rewrite -(Pr_cplt E) addrK. Qed.

Lemma Pr_setC E : Pr (~: E) = 1 - Pr E.
Proof. by rewrite -(Pr_cplt E) addrAC subrr add0r. Qed.

Lemma subset_Pr E E' : E \subset E' -> Pr E <= Pr E'.
Proof.
by move=> H; apply ler_suml => a aE //; move/subsetP : H; exact.
Qed.

Lemma le_Pr_setU E1 E2 : Pr (E1 :|: E2) <= Pr E1 + Pr E2.
Proof.
rewrite /Pr.
rewrite [X in X <= _](_ : _ = \sum_(i in A | [predU E1 & E2] i) P i); last first.
  by apply eq_bigl => x /=; rewrite inE.
rewrite [X in _ <= X + _](_ : _ = \sum_(i in A | pred_of_set E1 i) P i); last first.
  by apply eq_bigl => x /=; rewrite unfold_in.
rewrite [X in _ <= _ + X](_ : _ = \sum_(i in A | pred_of_set E2 i) P i); last first.
  by apply eq_bigl => x /=; rewrite unfold_in.
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
Proof. by move=> ?; rewrite -bigU //=; apply eq_bigl => a; rewrite inE. Qed.

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
rewrite /Pr big_setX /= exchange_big; apply eq_bigr => a aE.
by rewrite fdist_sndE /=; apply eq_bigl => b; rewrite inE.
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
apply eq_bigr => a aE; rewrite (big_pred1 (f a)) // => b /=.
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
rewrite big_distrl /=; apply eq_big => // a /eqP E1a /=.
rewrite {1}/Pr /=.
rewrite (eq_bigr (fun x => P (x.1, x.2))); last by case.
rewrite [in X in _ = _ * X](eq_bigl (fun a => a.2 \in E2)); last first.
  by move=> b; rewrite !inE.
rewrite [in RHS](eq_bigl (fun x => true && (x.2 \in E2))) //.
rewrite -[in RHS](pair_big xpredT (fun x => x \in E2) (fun x1 x2 => P (x1, x2))) /=.
rewrite exchange_big /= big_distrr /=; apply eq_big => // b E2b.
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
by apply eq_bigr => a aE; apply eq_bigr => v _; rewrite fdist_prod_of_rVE.
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

Local Notation "{ 'RV' P -> V }" := (RV_of P (Phant _) (Phant V)).

Definition ambient_dist (P : R.-fdist U) (X : {RV P -> T}) : R.-fdist U := P.

End random_variable.
Notation "{ 'RV' P -> T }" := (RV_of P (Phant _) (Phant T)) : proba_scope.

Section random_variable_eqType.
Context {R : realType}.
Variables (U : finType) (A : eqType) (P : R.-fdist U).

Definition pr_eq (X : {RV P -> A}) (a : A) := locked (Pr P ((finset (X @^-1 a)))).
Local Notation "`Pr[ X = a ]" := (pr_eq X a).

Lemma pr_eqE (X : {RV P -> A}) (a : A) : `Pr[ X = a ] = Pr P (finset (X @^-1 a)).
Proof. by rewrite /pr_eq; unlock. Qed.

Lemma pr_eq_ge0 (X : {RV P -> A}) (a : A) : 0 <= `Pr[ X = a].
Proof. by rewrite pr_eqE. Qed.

Lemma pr_eq_neq0 (X : {RV P -> A}) (a : A) :
  `Pr[ X = a ] != 0 <-> exists i, i \in X @^-1 a /\ 0 < P i.
Proof.
split; rewrite pr_eqE /Pr => PXa0.
  have H : forall i : U, 0 <= P i by move=> ?; apply/FDist.ge0.
  have := @psumr_neq0 R U (enum (finset (X @^-1 a))) xpredT _ (fun i _ => H i).
  rewrite big_enum PXa0 => /esym/hasP[i/=].
  by rewrite mem_enum inE/= => Xia Pi_gt0; exists i.
case: PXa0 => i; rewrite inE => ?.
rewrite psumr_neq0//; apply/hasP; exists i => //.
by rewrite inE; exact/andP.
Qed.

Lemma pr_eq0 (X : {RV P -> A}) (a : A) : a \notin fin_img X -> `Pr[ X = a ] = 0.
Proof.
move=> aX; apply/eqP/negPn; apply: contra aX => /pr_eq_neq0 [i [iXa Pi0]].
rewrite mem_undup; apply/mapP; exists i; rewrite ?mem_enum //.
by move: iXa; rewrite inE => /eqP.
Qed.

End random_variable_eqType.
Notation "`Pr[ X = a ]" := (pr_eq X a) : proba_scope.
Global Hint Resolve pr_eq_ge0 : core.

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

Definition pr_in (X : {RV P -> A}) (E : {set A}) :=
  locked (Pr P (X @^-1: E)).
Local Notation "`Pr[ X '\in' E ]" := (pr_in X E).

Lemma pr_inE (X : {RV P -> A}) (E : {set A}) :
  `Pr[ X \in E ] = Pr P (X @^-1: E).
Proof. by rewrite /pr_in; unlock. Qed.

Definition dist_of_RV (X : {RV P -> A}) : R.-fdist A := fdistmap X P.
Local Notation "`p_ X" := (dist_of_RV X).

(* TODO: rename *)
Lemma pr_eqE_finType (X : {RV P -> A}) (a : A) :
  `Pr[ X = a ] = Pr P (X @^-1: [set a]).
Proof. by rewrite pr_eqE -preimg_set1. Qed.

Lemma pr_eqE' (X : {RV P -> A}) (a : A) : `Pr[ X = a ] = `p_X a.
Proof.
by rewrite pr_eqE_finType /Pr fdistmapE//; apply eq_bigl => i; rewrite !inE.
Qed.

Lemma pr_eq1 (X : {RV P -> A}) : \sum_a `Pr[ X = a ] = 1.
Proof.
under eq_bigr do rewrite pr_eqE'.
by rewrite FDist.f1.
Qed.

Lemma pr_inE' (X : {RV P -> A}) (E : {set A}) : `Pr[ X \in E ] = Pr `p_X E.
Proof.
rewrite pr_inE /Pr partition_big_preimset /=.
by apply eq_bigr => a aE; rewrite /dist_of_RV fdistmapE.
Qed.

Lemma pr_in1 (X : {RV P -> A}) x : `Pr[ X \in [set x] ] = `Pr[ X = x ].
Proof. by rewrite pr_inE' Pr_set1 pr_eqE'. Qed.

End random_variable_finType.
Notation "`Pr[ X '\in' E ]" := (pr_in X E) : proba_scope.
Notation "`p_ X" := (dist_of_RV X) : proba_scope.
#[deprecated(since="infotheo 0.9.2", note="renamed to `pr_in`")]
Notation pr_eq_set := pr_in (only parsing).
#[deprecated(since="infotheo 0.9.2", note="renamed to `pr_inE`")]
Notation pr_eq_setE := pr_inE (only parsing).
#[deprecated(since="infotheo 0.9.2", note="renamed to `pr_in1`")]
Notation pr_eq_set1 := pr_in1 (only parsing).

Section random_variables.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).

Definition unit_RV : {RV P -> unit} := fun=> tt.
Definition const_RV (T : eqType) cst : {RV P -> T} := fun=> cst.
Definition comp_RV (TA TB : eqType) (f : TA -> TB) (X : {RV P -> TA}) : {RV P -> TB} :=
  fun x => f (X x).

End random_variables.

Notation "f `o X" := (comp_RV f X).

Section zmod_random_variables.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (V : zmodType).
Local Open Scope ring_scope.

Definition add_RV (X Y : {RV P -> V}) : {RV P -> V} := fun x => X x + Y x.
Definition sub_RV (X Y : {RV P -> V}) : {RV P -> V} := fun x => X x - Y x.

Definition opp_RV (X : {RV P -> V}) : {RV P -> V} := fun x => - X x.
Definition trans_add_RV (X : {RV P -> V}) m : {RV P -> V} := fun x => X x + m.
Definition trans_sub_RV (X : {RV P -> V}) m : {RV P -> V} := fun x => X x - m.
Definition sumR_RV I (r : seq I) (p : pred I) (X : I -> {RV P -> V}) : {RV P -> V} :=
  fun x => \sum_(i <- r | p i) X i x.

Local Notation "X `+ Y" := (add_RV X Y) : proba_scope.
Local Notation "X `- Y" := (sub_RV X Y) : proba_scope.

Lemma sub_RV_neg (X Y : {RV P -> V}) :
  X `- Y = X `+ opp_RV Y.
Proof. by []. Qed.

End zmod_random_variables.

Notation "X `+ Y" := (add_RV X Y) : proba_scope.
Notation "X `- Y" := (sub_RV X Y) : proba_scope.
Notation "X '`+cst' m" := (trans_add_RV X m) : proba_scope.
Notation "X '`-cst' m" := (trans_sub_RV X m) : proba_scope.
Notation "'`--' P" := (opp_RV P) : proba_scope.

Section ring_random_variables.
Local Open Scope ring_scope.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (V : ringType).

Definition scalel_RV k (X : {RV P -> V}) : {RV P -> V} := fun x => k * X x.
Definition scaler_RV (X : {RV P -> V}) k : {RV P -> V} := fun x => X x * k.
Definition sq_RV (X : {RV P -> V}) : {RV P -> V} := (fun x => x ^+ 2) `o X.

End ring_random_variables.

Notation "k `cst* X" := (scalel_RV k X) : proba_scope.
Notation "X `*cst k" := (scaler_RV X k) : proba_scope.
Notation "X '`/' n" := (scalel_RV n%:R^-1 X) : proba_scope.
Notation "X '`^2' " := (sq_RV X) : proba_scope.

Section real_random_variables.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).

Definition log_RV : {RV P -> R} := fun x => log (P x).

End real_random_variables.

Notation "'`log' P" := (log_RV P) : proba_scope.

Section RV_lemmas.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).
Implicit Types X : {RV P -> R}.

Lemma scalel_RVA k l X : scalel_RV (k * l) X = scalel_RV k (scalel_RV l X).
Proof. by rewrite /scalel_RV boolp.funeqE => u; rewrite mulrA. Qed.

Lemma scaler_RVA X k l : scaler_RV X (k * l) = scaler_RV (scaler_RV X k) l.
Proof. by rewrite /scaler_RV boolp.funeqE => u; rewrite mulrA. Qed.

Lemma sq_RV_pow2 X x : sq_RV X x = (X x) ^+ 2.
Proof. reflexivity. Qed.

Lemma sq_RV_ge0 X x : 0 <= sq_RV X x.
Proof. by rewrite sq_RV_pow2 sqr_ge0. Qed.

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

Lemma pr_eq_unit {R : realType} (U : finType) (P : R.-fdist U) : `Pr[ (unit_RV P) = tt ] = 1.
Proof. by rewrite pr_eqE'; apply/eqP/fdist1P; case. Qed.

Lemma Pr_fdistmap_RV2 {R : realType} (U : finType) (P : R.-fdist U) (A B : finType)
  (E : {set A}) (F : {set B}) (X : {RV P -> A}) (Z : {RV P -> B}) :
  Pr `p_[% X, Z] (E `* F) =
  Pr P ([set x | preim X (mem E) x] :&: [set x | preim Z (mem F) x]).
Proof.
rewrite /Pr.
transitivity (\sum_(a in ([% X, Z] @^-1: (E `* F))) P a); last first.
  by apply eq_bigl => u; rewrite !inE.
rewrite [in RHS]partition_big_preimset /=.
apply eq_big => // -[a c]; rewrite inE => /andP[/= aE cF].
by rewrite fdistmapE.
Qed.

Lemma pr_eq_diag {R : realType} (T : finType) (U : eqType) (P : R.-fdist T)
(X : {RV P -> U}) (x : U) : `Pr[ [% X, X] = (x, x) ] = `Pr[ X = x ].
Proof. by rewrite !pr_eqE /Pr; apply: eq_bigl=> a; rewrite !inE xpair_eqE andbb.
Qed.

Section pr_pair.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).
Variables (A B C : finType) (TA TB TC : eqType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).
Variables (TX : {RV P -> TA}) (TY : {RV P -> TB}) (TZ : {RV P -> TC}).

Lemma pr_in_pairC E F : `Pr[ [% Y, X] \in F `* E ] = `Pr[ [% X, Y] \in E `* F].
Proof. by rewrite 2!pr_inE; apply eq_bigl => u; rewrite !inE /= andbC. Qed.

Lemma pr_eq_pairC x : `Pr[ [% TY, TX] = x ] = `Pr[ [% TX, TY] = swap x].
Proof.
by rewrite !pr_eqE; congr Pr; apply/setP => u; rewrite !inE /= !xpair_eqE andbC.
Qed.

Lemma pr_in_pairA E F G :
  `Pr[ [% X, [% Y, Z]] \in E `* (F `* G) ] =
  `Pr[ [% [% X, Y], Z] \in (E `* F) `* G].
Proof. by rewrite !pr_inE; apply eq_bigl => u; rewrite !inE /= andbA. Qed.

Lemma pr_eq_pairA a b c :
  `Pr[ [% TX, [% TY, TZ]] = (a, (b, c))] = `Pr[ [% TX, TY, TZ] = (a, b, c) ].
Proof.
by rewrite !pr_eqE; apply eq_bigl => u; rewrite !inE /= !xpair_eqE andbA.
Qed.

Lemma pr_in_pairAC E F G :
`Pr[ [% X, Y, Z] \in (E `* F) `* G] = `Pr[ [% X, Z, Y] \in (E `* G) `* F].
Proof. by rewrite !pr_inE; apply eq_bigl => u; rewrite !inE /= andbAC. Qed.

Lemma pr_eq_pairAC a b c :
`Pr[ [% TX, TY, TZ] = (a, b, c) ] = `Pr[ [% TX, TZ, TY] = (a, c, b)].
Proof.
by rewrite !pr_eqE; apply eq_bigl => u; rewrite !inE /= !xpair_eqE andbAC.
Qed.

Lemma pr_in_pairCA E F G :
`Pr[ [% X, [%Y, Z]] \in E `* (F `* G) ] = `Pr[ [% Y, [%X, Z]] \in F `* (E `* G)].
Proof. by rewrite !pr_inE; apply eq_bigl => u; rewrite !inE /= andbCA. Qed.

Lemma pr_eq_pairCA  a b c :
`Pr[ [% TX, [%TY, TZ]] = (a, (b, c)) ] = `Pr[ [% TY, [% TX, TZ]] = (b, (a, c))].
Proof.
by rewrite !pr_eqE; apply eq_bigl => u; rewrite !inE /= !xpair_eqE andbCA.
Qed.

Lemma pr_in_comp (f : A -> B) E : injective f ->
  `Pr[ X \in E ] = `Pr[ (f `o X) \in f @: E ].
Proof.
by move=> inj_f; rewrite 2!pr_inE' (Pr_fdistmap inj_f) fdistmap_comp.
Qed.

Lemma pr_eq_comp (f : A -> B) a : injective f ->
  `Pr[ X = a ] = `Pr[ (f `o X) = f a ].
Proof.
move=> inj_f.
by rewrite -!pr_in1 !pr_inE' (Pr_fdistmap inj_f) fdistmap_comp imset_set1.
Qed.

End pr_pair.

Section more_pr_lemmas.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).
Variables (TA UA : finType) (f : TA -> UA) (X : {RV P -> TA}).

(* TODO: rename *)
Lemma pr_in_comp' E :
  `Pr[ (f `o X) \in E ]  = `Pr[ X \in f @^-1: E ].
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

End more_pr_lemmas.

Lemma pr_eq_pair_setT {R : realType} (U : finType) (P : R.-fdist U)
    (A B : finType) (E : {set A}) (X : {RV P -> A}) (Y : {RV P -> B}) :
  `Pr[ [% X, Y] \in E `*T ] = `Pr[ X \in E ].
Proof.
apply/esym.
rewrite (@pr_in_comp _ _ _ _ _ _ (fun a => (a, tt))); last by move=> u1 u2 -[].
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

Lemma pr_eq_domin_RV2 a b : `Pr[ TX = a] = 0 -> `Pr[ [% TX, TY] = (a, b) ] = 0.
Proof.
rewrite !pr_eqE /Pr => /psumr_eq0P => a0.
rewrite big1// => i.
rewrite inE/= xpair_eqE => /andP [] ? ?.
by apply: a0 => //; rewrite inE.
Qed.

Lemma pr_eq_domin_RV1 a b : `Pr[ TY = b] = 0 -> `Pr[ [% TX, TY] = (a, b) ] = 0.
Proof.
rewrite !pr_eqE /Pr => /psumr_eq0P => a0.
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
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (X : {RV P -> R}).

Definition Ex := \sum_(u in U) X u * P u.

Lemma Ex_ge0 : (forall u, 0 <= X u) -> 0 <= Ex.
Proof. move=> H; apply/sumr_ge0 => u _; rewrite mulr_ge0//; exact/RleP. Qed.

End expected_value_def.
Arguments Ex {R U} _ _.

Notation "'`E'" := (@Ex _ _ _) : proba_scope.

(* Alternative definition of the expected value: *)
Section Ex_alt.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (X : {RV P -> R}).

Definition Ex_alt := \sum_(r <- fin_img X) r * `Pr[ X = r ].

Lemma Ex_altE : Ex_alt = `E X.
Proof.
rewrite /Ex.
transitivity (\sum_(r <- fin_img X) \sum_(u in U | X u == r) (X u * P u)).
  apply eq_bigr => /= r _; rewrite pr_eqE big_distrr /=.
  by apply eq_big => //= a; rewrite !inE // => /eqP ->.
by rewrite -partition_big_fin_img.
Qed.

End Ex_alt.

Section expected_value_prop.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (X Y : {RV P -> R}).

Lemma E_opp_RV : `E (`-- X) = - `E X.
Proof.
by rewrite /Ex/= big_morph_oppr/=; apply: eq_bigr => u _; rewrite mulNr.
Qed.

Lemma E_scalel_RV k : `E (k `cst* X) = k * `E X.
Proof.
by rewrite /scalel_RV {2}/Ex big_distrr /=; apply eq_bigr => a _; rewrite mulrA.
Qed.

Lemma E_scaler_RV k : `E (X `*cst k) = `E X * k.
Proof.
by rewrite big_distrl /=; apply: eq_bigr => i Hi; rewrite mulrAC.
Qed.

Lemma E_add_RV : `E (X `+ Y) = `E X + `E Y.
Proof. rewrite -big_split; apply eq_bigr => a _ /=; by rewrite -mulrDl. Qed.

Lemma E_sumR I r p (Z : I -> {RV P -> R}) :
  `E (sumR_RV r p Z) = \sum_(i <- r | p i) (`E (Z i)).
Proof.
rewrite /Ex.
under eq_bigr do rewrite big_distrl.
rewrite /=.
by rewrite exchange_big /=; apply: eq_bigr => i Hi.
Qed.

Lemma E_sub_RV : `E (X `- Y) = `E X - `E Y.
Proof.
rewrite {3}/Ex big_morph_oppr -big_split /=.
by apply eq_bigr => u _; by rewrite -mulNr -mulrDl.
Qed.

Lemma E_const_RV k : `E (const_RV P k) = k.
Proof. by rewrite /Ex /const_RV /= -big_distrr /= FDist.f1 mulr1. Qed.

Lemma E_trans_add_RV m : `E (X `+cst m) = `E X + m.
Proof.
rewrite /trans_add_RV /=.
transitivity (\sum_(u in U) (X u * P u + m * P u)).
  by apply eq_bigr => u _ /=; rewrite mulrDl.
by rewrite big_split /= -big_distrr /= FDist.f1 mulr1.
Qed.

Lemma E_trans_sub_RV m : `E (X `-cst m) = `E X - m.
Proof.
rewrite /trans_sub_RV /=.
transitivity (\sum_(u in U) (X u * P u + - m * P u)).
  by apply eq_bigr => u _ /=; rewrite mulrDl.
by rewrite big_split /= -big_distrr /= FDist.f1 mulr1.
Qed.

Lemma E_trans_RV_id_rem m :
  `E ((X `-cst m) `^2) = `E ((X `^2 `- (2 * m `cst* X)) `+cst m ^+ 2).
Proof.
apply eq_bigr => a _.
rewrite /sub_RV /trans_add_RV /trans_sub_RV /sq_RV /= /comp_RV /scalel_RV /=.
by rewrite /ambient_dist; lra.
Qed.

Lemma E_comp_RV f k : (forall x y, f (x * y) = f x * f y) ->
  `E (f `o (k `cst* X)) = `E ((f k) `cst* (f `o X)).
Proof. by move=> H; rewrite /comp_RV /=; apply eq_bigr => u _; rewrite H. Qed.

Lemma E_comp_RV_ext f : X = Y -> `E (f `o X) = `E (f `o Y).
Proof. move=> H; by rewrite /comp_RV /= H. Qed.

End expected_value_prop.

Lemma E_cast_RV_fdist_rV1 {R : realType} (A : finType) (P : R.-fdist A) :
  forall (X : {RV P -> R}), `E (cast_RV_fdist_rV1 X) = `E X.
Proof.
move=> f; rewrite /cast_RV_fdist_rV1 /=; apply big_rV_1 => // m.
by rewrite -fdist_rV1.
Qed.

Section conditional_expectation_def.
Context {R : realType}.
Variable (U : finType) (P : R.-fdist U) (X : {RV P -> R}) (F : {set U}).

Definition cEx :=
  \sum_(r <- fin_img X) r * Pr P (finset (X @^-1 r) :&: F) / Pr P F.

End conditional_expectation_def.
Notation "`E_[ X | F ]" := (cEx X F).

Section conditional_expectation_prop.
Context {R : realType}.
Variable (U I : finType) (P : R.-fdist U) (X : {RV P -> R}) (F : I -> {set U}).
Hypothesis dis : forall i j, i != j -> [disjoint F i & F j].
Hypothesis cov : cover [set F i | i in I] = [set: U].

Lemma Ex_cEx : `E X = \sum_(i in I) `E_[X | F i] * Pr P (F i).
Proof.
apply/esym; rewrite /cEx.
evar (f : I -> R); rewrite (eq_bigr f); last first.
  move=> i _; rewrite big_distrl /f; reflexivity.
rewrite {}/f /= (bigID (fun i => Pr P (F i) != 0)) /=.
rewrite [in X in _ + X = _]big1 ?addr0; last first.
  by move=> i; rewrite negbK => /eqP ->; rewrite big1 // => r _; rewrite mulr0.
transitivity (\sum_(i in I | Pr P (F i) != 0)
  \sum_(j <- fin_img X) (j * Pr P (finset (X @^-1 j) :&: F i))).
  apply: eq_bigr => i Fi0; apply eq_bigr => r _.
  by rewrite -mulrA mulVf ?mulr1.
rewrite -Ex_altE /Ex_alt exchange_big /=; apply: eq_bigr => r _.
rewrite -big_distrr /=; congr (_ * _).
transitivity (\sum_(i in I) Pr P (finset (X @^-1 r) :&: F i)).
  rewrite big_mkcond /=; apply eq_bigr => i _.
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
rewrite pr_eqE; congr Pr.
move: cov; rewrite cover_imset => cov'.
by rewrite -big_distrr /= cov' setIT.
Qed.

End conditional_expectation_prop.

(** A theory of indicator functions from [A : finType] to [R] *)
Section Ind.
Context {R : realType}.
Variable A : finType.

Definition Ind (s : {set A}) (x : A) : R := if x \in s then 1 else 0.

Lemma Ind_set0 (x : A) : Ind set0 x = 0.
Proof. by rewrite /Ind inE. Qed.

Lemma Ind_inP (s : {set A}) (x : A) : reflect (Ind s x = 1) (x \in s).
Proof.
apply: (iffP idP); rewrite /Ind; first by move->.
by case: ifPn => // _ /eqP; rewrite eq_sym oner_eq0.
Qed.

Lemma Ind_notinP (s : {set A}) (x : A) : reflect (Ind s x = 0) (x \notin s).
Proof.
apply: (iffP idP); rewrite /Ind => Hmain.
  by rewrite ifF //; exact: negbTE.
by apply: negbT; case: ifP Hmain =>// _ /eqP; rewrite oner_eq0.
Qed.

Lemma Ind_cap (S1 S2 : {set A}) (x : A) :
  Ind (S1 :&: S2) x = Ind S1 x * Ind S2 x.
Proof. by rewrite /Ind inE; case: in_mem; case: in_mem=>/=; lra. Qed.


Lemma Ind_bigcap I (e : I -> {set A}) (r : seq I) (p : pred I) x :
  Ind (\bigcap_(j <- r | p j) e j) x = \prod_(j <- r | p j) (Ind (e j) x).
Proof.
apply (big_ind2 (R1 := {set A}) (R2 := R)); last by [].
- by rewrite /Ind inE.
- by move=> sa a sb b Ha Hb; rewrite -Ha -Hb; apply: Ind_cap.
Qed.

Lemma E_Ind (P : R.-fdist A) s : `E (Ind s : {RV P -> R}) = Pr P s.
Proof.
rewrite /Ex /Ind /Pr (bigID (mem s)) /=.
rewrite [X in _ + X = _]big1; last by move=> i /negbTE ->; rewrite mul0r.
by rewrite addr0; apply: eq_bigr => i ->; rewrite mul1r.
Qed.

End Ind.

(** This section gathers a proof of the formula of inclusion-exclusion
    contributed by Erik Martin-Dorel: the corresponding theorem is named
    [Pr_bigcup_incl_excl] and is more general than lemma [Pr_bigcup]. *)
Section probability_inclusion_exclusion.
Context {R : realType}.
Variables (A : finType) (P : R.-fdist A).

Let SumIndCap (n : nat) (S : 'I_n -> {set A}) (k : nat) (x : A) : R :=
  \sum_(J in {set 'I_n} | #|J| == k) (Ind (\bigcap_(j in J) S j) x).

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
rewrite big_distrr/=.
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
under eq_bigr do rewrite Ind_bigcup_incl_excl.
under eq_bigr do rewrite big_distrl.
rewrite /=.
rewrite exchange_big /=.
apply: eq_bigr => i _.
by rewrite -E_SumIndCap -E_scalel_RV.
Qed.

End probability_inclusion_exclusion.

Section markov_inequality.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (X : {RV P -> R}).
Hypothesis X_ge0 : forall u, 0 <= X u.

Lemma Ex_lb (r : R) : r * `Pr[ X >= r] <= `E X.
Proof.
rewrite /Ex (bigID [pred a' | X a' >= r]) /= -[a in a <= _]addr0.
rewrite lerD//; last first.
  by apply/sumr_ge0 => a _; rewrite mulr_ge0//; exact/RleP/X_ge0.
apply (@le_trans _ _ (\sum_(i | X i >= r) r * P i)).
  rewrite big_distrr /= le_eqVlt; apply/orP; left; apply/eqP.
  by apply/eq_bigl => a; rewrite inE.
by apply: ler_sum => u Xur; exact/ler_wpM2r.
Qed.

Lemma markov (r : R) : 0 < r -> `Pr[ X >= r ] <= `E X / r.
Proof. by move=> r0; rewrite ler_pdivlMr // mulrC; exact/Ex_lb. Qed.

End markov_inequality.

Section thm61.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (X : {RV P -> R}) (phi : R -> R).

Lemma Ex_comp_RV : `E (phi `o X) = \sum_(r <- fin_img X) phi r * `Pr[ X = r ].
Proof.
rewrite /Ex.
rewrite (partition_big_fin_img _ X (fun u => (phi `o X) u * P u)) /=.
apply: eq_bigr => a _.
rewrite pr_eqE /Pr big_distrr /=; apply eq_big.
  by move=> u; rewrite inE.
by move=> u /eqP Xua; rewrite /comp_RV -Xua.
Qed.

End thm61.

Section variance_def.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (X : {RV P -> R}).

Definition Var := let miu := `E X in `E ((X `-cst miu) `^2).

Lemma VarE : Var = `E (X `^2)  - (`E X) ^+ 2.
Proof.
by rewrite /Var E_trans_RV_id_rem E_trans_add_RV E_sub_RV E_scalel_RV; lra.
Qed.

End variance_def.

Arguments Var {R U} _ _.

Notation "'`V'" := (@Var _ _ _) : proba_scope.

Section variance_prop.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U) (X : {RV P -> R}).

(** The variance is not linear: *)
Lemma Var_scale k : `V (k `cst* X) = k ^+ 2 * `V X.
Proof.
rewrite {1}/`V [in X in X = _]/= E_scalel_RV.
pose Y : {RV P -> R} := k `cst* (X `+cst - `E X).
rewrite (@E_comp_RV_ext _ _ P ((k `cst* X) `-cst k * `E X) Y) //; last first.
  rewrite boolp.funeqE => /= x.
  by rewrite /Y /scalel_RV /= /trans_sub_RV /trans_add_RV; lra.
by rewrite E_comp_RV ?E_scalel_RV // => *; lra.
Qed.

Lemma Var_trans m : `V (X `+cst m) = `V X.
Proof.
rewrite /Var E_trans_add_RV; congr (`E (_ `^2)).
by rewrite boolp.funeqE => /= u; rewrite /trans_add_RV /trans_sub_RV /=; lra.
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
apply (@le_trans _ _ (\sum_(a in U | `| X a - `E X | >= epsilon)
    (((X `-cst `E X) `^2) a  * P a))); last first.
  rewrite /Ex big_mkcondr/=; apply: ler_sum => a _; case: ifPn => // _.
  by apply mulr_ge0 => //; exact: sq_RV_ge0.
rewrite /Pr big_distrr/= [_ ^+ 2]lock /= -!lock big_mkcond/= [leRHS]big_mkcond/=.
apply: ler_sum => u _; rewrite inE/=; case: ifPn => //.
rewrite -!/(_ ^+ 2) => H.
apply: ler_wpM2r => //=.
apply (@le_trans _ _ ((X u - `E X) ^+ 2)); last by rewrite lexx.
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
rewrite (@total_prob _ _ _ _ _ _ dis cov); apply eq_bigr; move=> i _.
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
rewrite /Pr !big_setX exchange_big /=; apply eq_bigr => b _.
by apply eq_bigr => a _; rewrite fdistXE.
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
rewrite /Pr !big_setX /= exchange_big; apply eq_bigr => a aF.
by apply eq_bigr => b bE; apply eq_bigr => c cG; rewrite fdistC12E.
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
Proof. by rewrite cPr_eq_def cPrET pr_eqE. Qed.

Lemma cpr_eqE {R : realType} (U : finType) (P : R.-fdist U) (TA TB : eqType)
  (X : {RV P -> TA}) (Y : {RV P -> TB}) a b :
  `Pr[ X = a | Y = b ] = `Pr[ [% X, Y] = (a, b) ] / `Pr[Y = b].
Proof.
rewrite cPr_eq_def /cPr /dist_of_RV 2!pr_eqE; congr (Pr _ _ / _).
by apply/setP => u; rewrite !inE xpair_eqE.
Qed.

Lemma cPr_eq_id {R : realType} (T : finType) (U : eqType) (P : R.-fdist T)
(X : {RV P -> U}) (x : U) : `Pr[ X = x ] != 0 -> `Pr[ X = x | X = x ] = 1.
Proof. by move=> ?; rewrite cpr_eqE pr_eq_diag divff. Qed.

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
rewrite pr_eq_pairC pr_eq_pairA pr_eq_pairAC -pr_eq_pairA pr_eq_pairC.
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
rewrite !pr_eqE; congr Pr.
by apply/setP => u; rewrite !inE /= !xpair_eqE !andbA.
by rewrite pr_eq_pairA.
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
rewrite !pr_eqE; congr Pr.
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
  rewrite !pr_eqE; congr Pr.
  apply/setP => u; rewrite !inE !xpair_eqE -!andbA; congr (_ && _).
  by rewrite !andbA andbAC.
by rewrite pr_eq_pairAC.
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
by rewrite pr_eq_pairA pr_eq_pairAC -pr_eq_pairA.
by rewrite pr_eq_pairC.
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
  by move=> b bY; rewrite {}/F pr_in_pairC pr_in_domin_RV2 // pr_in1 pr_eq0.
by apply eq_bigr => b _; rewrite /F pr_inE /Pr partition_big_preimset.
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

Section inde_RV_sym.
Context {R : realType}.
Variables (A : finType) (P : R.-fdist A) (TA TB: finType).
Variables (X : {RV P -> TA}) (Y : {RV P -> TB}).

Lemma inde_RV_sym : P |= X _|_ Y <-> P |= Y _|_ X.
Proof. by split => /cinde_RV_unit/cinde_RV_sym/cinde_RV_unit. Qed.

End inde_RV_sym.

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
  apply invr_neq0; rewrite pr_eq_pairC in H0.
  by apply: contra H0 => /eqP/(pr_eq_domin_RV2 Y b)/eqP.
rewrite pr_eq_pairA; apply: (@mulIf _ _ H1).
by rewrite -mulrA -!cpr_eqE K.
Qed.

Section sum_two_rand_var_def.
Context {R : realType}.
Variables (A : finType) (n : nat).
Variables (X : 'rV[A]_n.+2 -> R) (X1 : A -> R) (X2 : 'rV[A]_n.+1 -> R).

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
  (X1 (ta ``_ ord0) * P ta + X2 (rbehead ta) * P ta)).
  by apply eq_bigr => ta _; rewrite Hsum mulrDl.
rewrite big_split => //=; congr (_ + _).
- transitivity (\sum_(a in A)
    (X1 a * \sum_(ta in 'rV_n.+1) (fdist_prod_of_rV P (a, ta)))).
  + rewrite -(big_rV_cons_behead _ xpredT xpredT); apply eq_bigr => a _.
    rewrite big_distrr /=; apply eq_bigr => i _.
    by rewrite row_mx_row_ord0 fdist_prod_of_rVE.
  + by apply eq_bigr => a _; rewrite fdist_fstE.
- transitivity (\sum_(ta in 'rV_n.+1)
    (X2 ta * \sum_(a in A) (fdist_prod_of_rV P (a, ta)))).
  + rewrite -(big_rV_cons_behead _ xpredT xpredT) exchange_big /=.
    apply eq_bigr => ta _; rewrite big_distrr /=.
    by apply eq_bigr => a _; rewrite rbehead_row_mx fdist_prod_of_rVE.
  + by apply eq_bigr => ta _; rewrite fdist_sndE.
Qed.

Lemma E_id_rem_helper : X \= X1 @+ X2 ->
  P |= X1' _|_ X2' ->
  \sum_(i in 'rV[A]_n.+2) (X1 (i ``_ ord0) * X2 (rbehead i) * P i) =
    `E X1 * `E X2.
Proof.
move=> Hsum Hinde.
rewrite -!Ex_altE.
apply trans_eq with (\sum_(r <- undup (map X1 (enum A)))
   \sum_(r' <- undup (map X2 (enum ('rV[A]_n.+1))))
   ( r * r' * @pr_eq _ _ _ P1 X1 r * @pr_eq _ _ _ P2 X2 r')); last first.
  rewrite [in RHS]big_distrl /=; apply eq_bigr => i _.
  rewrite big_distrr /=; apply eq_bigr => j _.
  by rewrite -!mulrA [in RHS](mulrCA _ j).
rewrite -(big_rV_cons_behead _ xpredT xpredT) /=.
apply trans_eq with (\sum_(a in A) \sum_(j in 'rV[A]_n.+1)
  (X1 a * X2 j * P (row_mx (\row_(k < 1) a) j))).
  apply eq_bigr => a _; apply eq_bigr => ta _.
  by rewrite row_mx_row_ord0 rbehead_row_mx.
rewrite (partition_big_undup_map _ X1); last first.
  by rewrite /index_enum -enumT; apply enum_uniq.
rewrite /index_enum -enumT.
apply eq_bigr => /= r _.
rewrite {1}enumT exchange_big /= (partition_big_undup_map _ X2); last first.
  by rewrite /index_enum -enumT; apply enum_uniq.
rewrite /index_enum -enumT.
apply eq_bigr => /= r' _.
apply trans_eq with (r * r' * \sum_(i0 | X2 i0 == r') \sum_(i1 | X1 i1 == r)
    (P (row_mx (\row_(k < 1) i1) i0))).
  rewrite big_distrr /= /index_enum -!enumT; apply eq_bigr => ta ta_r'.
  rewrite big_distrr /=; apply eq_bigr => a a_l.
  move/eqP : ta_r' => <-.
  by move/eqP : a_l => <-.
rewrite -[RHS]mulrA; congr (_ * _).
rewrite exchange_big /=.
have {}Hinde := Hinde r r'.
have -> : `Pr[ X1 = r ] = `Pr[ X1' = r ].
  rewrite 2!pr_eqE /P1 /head_of_fdist_rV Pr_fdist_fst Pr_fdist_prod_of_rV1; congr Pr.
  by apply/setP => /= v; rewrite !inE /X1'.
have -> : `Pr[ X2 = r' ] = `Pr[ X2' = r' ].
  rewrite 2!pr_eqE /P1 /tail_of_fdist_rV Pr_fdist_snd Pr_fdist_prod_of_rV2; congr Pr.
  by apply/setP => /= v; rewrite !inE /X2'.
rewrite -Hinde.
rewrite pr_eqE /ambient_dist /Pr.
transitivity (\sum_(a : 'rV_n.+2 | (X1 (a ``_ ord0) == r) && (X2 (rbehead a) == r')) P a).
  by rewrite -(big_rV_cons_behead _ [pred x | X1 x == r] [pred x | X2 x == r']) /=.
apply eq_bigl => /= v.
by rewrite /X1' /X2' !inE /RV2 xpair_eqE.
Qed.

Lemma E_id_rem : X \= X1 @+ X2 -> P |= X1' _|_ X2' ->
  `E (X `^2) = `E (X1 `^2) + 2 * `E X1 * `E X2 + `E (X2 `^2).
Proof.
move=> Hsum Hinde.
rewrite -![in RHS]Ex_altE.
transitivity (\sum_(i in 'rV_n.+2)
  ((X1 (i ``_ ord0) + X2 (rbehead i)) ^+ 2%N * P i)).
  apply eq_bigr => i _; rewrite /sq_RV /=.
  by rewrite /comp_RV Hsum.
transitivity (\sum_(i in 'rV_n.+2) ((X1 (i ``_ ord0)) ^+ 2 +
    2 * X1 (i ``_ ord0) * X2 (rbehead i) + (X2 (rbehead i)) ^+ 2) * P i).
  by apply eq_bigr => ? _; rewrite sqrrD -mulrA mulr_natl.
transitivity (\sum_(i in 'rV_n.+2) ((X1 (i ``_ ord0)) ^+ 2 * P i + 2 *
  X1 (i ``_ ord0) * X2 (rbehead i) * P i + (X2 (rbehead i)) ^+ 2 * P i)).
  by apply eq_bigr => ? ?; lra.
rewrite !big_split /=; congr (_ + _ + _).
- rewrite Ex_altE -(big_rV_cons_behead _ xpredT xpredT) /=.
  apply eq_bigr => i _.
  transitivity (X1 i ^+ 2 * \sum_(j in 'rV_n.+1) (fdist_prod_of_rV P) (i, j)).
  + rewrite big_distrr /=; apply eq_bigr => i0 _.
    by rewrite row_mx_row_ord0 fdist_prod_of_rVE.
  + by rewrite fdist_fstE.
- rewrite -mulrA.
  rewrite !Ex_altE.
  rewrite -E_id_rem_helper // big_distrr /=.
  by apply eq_bigr => i _; lra.
- rewrite Ex_altE -(big_rV_cons_behead _ xpredT xpredT) exchange_big /=.
  apply eq_bigr => t _.
  transitivity (X2 t ^+ 2 * \sum_(i in A) (fdist_prod_of_rV P) (i, t)).
  + rewrite big_distrr /=; apply eq_bigr => i _.
    by rewrite rbehead_row_mx fdist_prod_of_rVE.
  + by congr (_ * _); rewrite fdist_sndE.
Qed.

Lemma V_sum_2 : X \= X1 @+ X2 -> P |= X1' _|_ X2'  ->
  `V X = `V X1 + `V X2.
Proof.
move=> H ?; rewrite !VarE E_id_rem // (E_sum_2 H) sqrrD.
by rewrite /Ex /= -/P1 -/P2; lra.
Qed.

End sum_two_rand_var.

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
    x * y * `Pr[ XY = (x, y) ]).
  rewrite /Ex /= (eq_bigr (fun u => X u.1 * Y u.2 * P (u.1, u.2))); last by case.
  rewrite -(pair_bigA _ (fun u1 u2 => X u1 * Y u2 * P (u1, u2))) /=.
  rewrite (partition_big_fin_img _ X) /=; apply eq_bigr => x _.
  rewrite exchange_big /= (partition_big_fin_img _ Y) /=; apply eq_bigr => y _.
  rewrite pr_eqE /Pr big_distrr /= exchange_big pair_big /=.
  apply eq_big.
    by move=> -[a b] /=; rewrite inE.
  by case=> a b /= /andP[/eqP -> /eqP ->].
transitivity (\sum_(x <- fin_img X) \sum_(y <- fin_img Y)
    x * y * `Pr[ X = x ] * `Pr[ Y = y ]).
  apply eq_bigr => x _; apply eq_bigr => y _.
  rewrite -!mulrA.
  have {}Hinde := Hinde x y.
  congr (_ * (_ * _)).
  transitivity (`Pr[ X' = x ] * `Pr[ Y' = y ]); last first.
    congr (_ * _).
      rewrite !pr_eqE Pr_fdist_fst; congr Pr.
      by apply/setP => -[a b]; rewrite !inE.
    rewrite !pr_eqE Pr_fdist_snd; congr Pr.
    by apply/setP => -[a b]; rewrite !inE.
  by rewrite -Hinde !pr_eqE.
rewrite -!Ex_altE.
rewrite /Ex_alt big_distrl; apply eq_bigr => x _ /=; rewrite big_distrr /=.
apply eq_bigr=> y _.
by rewrite -!mulrA; congr (_ * _); rewrite mulrCA.
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
rewrite !pr_eqE -!fdist_prod_of_fdist_rV.
rewrite (_ : [set x0 | _] = (finset (X @^-1 x)) `* (finset (Y @^-1 y))); last first.
  by apply/setP => -[a b]; rewrite !inE /= xpair_eqE.
rewrite Pr_fdist_prod_of_rV (_ : [set x0 | _] = (finset (X @^-1 x)) `*T); last first.
  by apply/setP => a; rewrite !inE.
rewrite Pr_fdist_prod_of_rV1 (_ : [set x0 | _] = T`* (finset (Y @^-1 y))); last first.
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
elim => [Xs Xbar | [_ Xs Xbar | n IHn Xs Xbar] ].
- by inversion 1.
- inversion 1; subst.
  apply Eqdep_dec.inj_pair2_eq_dec in H0; last exact Peano_dec.eq_nat_dec.
  apply Eqdep_dec.inj_pair2_eq_dec in H1; last exact Peano_dec.eq_nat_dec.
  subst Xs Xbar.
  by rewrite big_ord_recl big_ord0 addr0 E_cast_RV_fdist_rV1.
- inversion 1; subst.
  apply Eqdep_dec.inj_pair2_eq_dec in H1; last exact Peano_dec.eq_nat_dec.
  apply Eqdep_dec.inj_pair2_eq_dec in H2; last exact Peano_dec.eq_nat_dec.
  subst Z Xs.
  rewrite big_ord_recl.
  rewrite [X in _ = _ + X](_ : _ = \sum_(i < n.+1) `E (Xs0 ``_ i)); last first.
    apply eq_bigr => i _ /=.
    apply eq_bigr => a _ /=.
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
elim=> [X Xs X_Xs sigma2 Hsigma2|].
  by inversion X_Xs.
case=> [_ | n IH] Xsum Xs Hsum s Hs.
- inversion Hsum.
  apply Eqdep_dec.inj_pair2_eq_dec in H; last exact Peano_dec.eq_nat_dec.
  apply Eqdep_dec.inj_pair2_eq_dec in H0; last exact Peano_dec.eq_nat_dec.
  subst Xs Xsum.
  by rewrite Var_cast_RV_fdist_rV1 mul1r.
- move: Hsum; inversion 1.
  apply Eqdep_dec.inj_pair2_eq_dec in H0; last exact Peano_dec.eq_nat_dec.
  apply Eqdep_dec.inj_pair2_eq_dec in H1; last exact Peano_dec.eq_nat_dec.
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
  rewrite E_scalel_RV (E_sum_n X_Xs).
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
  rewrite /pr_eq; unlock.
  apply eq_bigl => u.
  rewrite !inE /RVn.
  apply/eqP/eqP => [<-|H]; first by rewrite mxE.
  by apply/rowP => i; rewrite {}(ord1 i) !mxE.
rewrite big_ord_recr /=.
Abort.

End prob_chain_rule.
