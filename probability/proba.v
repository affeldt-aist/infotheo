(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import all_ssreflect ssralg fingroup perm finalg matrix.
From mathcomp Require boolp.
Require Import Reals Lra Nsatz.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop.
Require Import fdist.

(******************************************************************************)
(*               Probabilities over finite distributions                      *)
(*                                                                            *)
(* This file provides a formalization of finite probabilities using           *)
(* distributions over a finite type (see fsdist.v for finitely-supported      *)
(* distributions) that ends with a proof of the weak law of large numbers.    *)
(*                                                                            *)
(*  Pr d E          == probability of event E over the distribution d         *)
(*  {RV P -> T}     == the type of random variables over an ambient           *)
(*                     distribution P                                         *)
(*  \Pr[ X = a ]    == the probability that the random variable X is a        *)
(*  \Pr[ X >= r ]    == the probability that the random variable X is greater  *)
(*                     or equal to a                                          *)
(*  `Pr_P [ A | B ] == conditional probability                                *)
(*  P |= X _|_ Y    == the random variables X and Y over the ambient          *)
(*                     distribution P are independent                         *)
(*  Z \= X @+ Y     == Z is the sum of two random variables                   *)
(*  X \=sum Xs      == X is the sum of the n>=1 random variables Xs           *)
(*  `E X            == expected value of the random variable X                *)
(*  `V X            == the variance of the random variable X                  *)
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
(*                          laws of total probability                         *)
(*  bayes_theorem        == Bayes' theorem                                    *)
(*  Pr_bigcup_incl_excl  == an algebraic proof (by Erik Martin-Dorel) of the  *)
(*                          formula of inclusion-exclusion                    *)
(*  markov               == Markov inequality                                 *)
(*  chebyshev_inequality == Chebyshev's inequality                            *)
(*  inde_events          == independent events                                *)
(*  wlln                 == weak law of large numbers                         *)
(******************************************************************************)

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

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Notation "X @^-1 x" := ([set h | X h == x]) : proba_scope.

Local Open Scope R_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.

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

Notation "'\Pr[' X '>=' r ']'" := (pr_geq X r) : proba_scope.

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
