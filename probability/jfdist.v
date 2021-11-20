(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg fingroup perm finalg matrix.
From mathcomp Require boolp.
From mathcomp Require Import Rstruct.
Require Import Reals.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop fdist.
Require Import proba.

(******************************************************************************)
(*        Conditional probabilities over joint finite distributions           *)
(*                                                                            *)
(*       \Pr_P [ A | B ] == conditional probability of A given B where P is a *)
(*                          joint distribution                                *)
(* CondJFDist0.d PQ a a0 == The conditional distribution derived from PQ      *)
(*                          given a, PQ is a joint distribution               *)
(*                          {fdist A * B}, a0 is a proof that                 *)
(*                          Bivar.fst PQ a != 0, the result is a              *)
(*                          distribution {fdist B}                            *)
(*     CondJFDist.d PQ a == The conditional distribution derived from PQ      *)
(*                          given a Same as CondJFDist0.d when                *)
(*                          Bivar.fst PQ a != 0.                              *)
(*           PQ `(| a |) == notation CondJFDist.d PQ a                        *)
(*                                                                            *)
(******************************************************************************)

(* TODO: complete documentation using the following (outdated?) information:
- Various distributions (Swap.d, Self.d, TripA.d, TripA'.d, TripC12.d, TripC23.d,
  TripC13.d, Proj13.d, Proj23.d)
- Section conditional_probability_def.
- Module CondJFDist.
- Module CondJFDistT.
- Module CJFDist.
- Section conditional_probability_prop.
- Section total_probability.
- Section bayes.
- Section conditional_probability_prop3.
- Section product_rule.
- Section conditional_expectation_def.
- Section conditional_expectation_prop.
- Various distributions (Take.d, Nth.d, PairNth.d, PairTake.d, MargDist.d,
  MultivarPerm.d, TakeDrop.d)
*)

Reserved Notation "\Pr_ P [ A | B ]" (at level 6, P, A, B at next level,
  format "\Pr_ P [ A  |  B ]").
Reserved Notation "\Pr_[ A | B ]" (at level 6, A, B at next level,
  format "\Pr_[ A  |  B ]").
Reserved Notation "P `(| a ')'" (at level 6, a at next level, format "P `(| a )").

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.
Local Open Scope proba_scope.

Lemma bij_swap A B : bijective (@swap A B).
Proof. apply Bijective with swap; by case. Qed.
Arguments bij_swap {A B}.

Lemma swapK A B : (@swap A B) \o swap = @id (B * A).
Proof. by rewrite boolp.funeqE => -[]. Qed.

Module Swap.
Section def.
Variables (A B : finType) (P : {fdist A * B}).
Definition d : {fdist B * A} := FDistMap.d swap P.
Lemma dE a b : d (b, a) = P (a, b).
Proof.
by rewrite FDistMap.dE /= -/(swap (a, b)) (big_pred1_inj (bij_inj bij_swap)).
Qed.
End def.
Section prop.
Variables (A B : finType) (P : {fdist A * B}).
Lemma fst : Bivar.fst (d P) = Bivar.snd P.
Proof. by rewrite /Bivar.fst /d FDistMap.comp. Qed.
Lemma snd : Bivar.snd (d P) = Bivar.fst P.
Proof. by rewrite /Bivar.snd /d FDistMap.comp. Qed.
Lemma dI : d (d P) = P.
Proof. by rewrite /d FDistMap.comp swapK FDistMap.id. Qed.
Lemma Pr (E : {set A}) (F : {set B}) : Pr P (E `* F) = Pr (Swap.d P) (F `* E).
Proof.
rewrite /Pr !big_setX exchange_big /=; apply eq_bigr => b _.
apply eq_bigr => a _; by rewrite Swap.dE.
Qed.
End prop.
Section prop2.
Variables (A B : finType) (P : fdist A) (Q : fdist B).
Lemma ProdFDist : Swap.d (Q `x P) = P `x Q.
Proof. apply/fdist_ext => -[a b]; by rewrite dE !ProdFDist.dE mulRC. Qed.
End prop2.
Section prop3.
Variables (A B : finType) (P : {fdist A * B}) (Q : {fdist A * B}).
Local Open Scope reals_ext_scope.
Lemma dom_by : dominates P Q -> dominates (Swap.d P) (Swap.d Q).
Proof.
by move/dominatesP => H; apply/dominatesP => -[b a]; rewrite !dE => /H.
Qed.
End prop3.
End Swap.

Lemma Swap_RV2 (U : finType) (P : fdist U) (A B : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) : Swap.d `d_[% X, Y] = `d_[% Y, X].
Proof. by rewrite /Swap.d /dist_of_RV FDistMap.comp. Qed.

Module Self.
Section def.
Variable (A : finType) (P : {fdist A}).
Definition f := [ffun a : A * A => if a.1 == a.2 then P a.1 else 0].
Lemma f0 x : 0 <= f x.
Proof. rewrite /f ffunE; case: ifPn => [/eqP -> //| _]; exact: leRR. Qed.
Lemma f1 : \sum_(x in {: A * A}) f x = 1.
Proof.
rewrite (eq_bigr (fun a => f (a.1, a.2))); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => f (a1, a2))) /=.
rewrite -(FDist.f1 P); apply/eq_bigr => a _.
under eq_bigr do rewrite ffunE.
rewrite /= (bigD1 a) //= eqxx.
by rewrite big1 ?addR0 // => a' /negbTE; rewrite eq_sym => ->.
Qed.
Definition d : {fdist A * A} := locked (FDist.make f0 f1).
Lemma dE a : d a = if a.1 == a.2 then P a.1 else 0.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
End def.
Section prop.
Variables (A : finType) (P : {fdist A}).
Lemma fst : Bivar.fst (d P) = P.
Proof.
apply/fdist_ext => a /=; rewrite Bivar.fstE (bigD1 a) //= dE eqxx /=.
by rewrite big1 ?addR0 // => a' /negbTE; rewrite dE /= eq_sym => ->.
Qed.
Lemma swap : Swap.d (d P) = d P.
Proof.
apply/fdist_ext => -[a1 a2].
by rewrite Swap.dE !dE /= eq_sym; case: ifPn => // /eqP ->.
Qed.
End prop.
End Self.

Definition ex2C (T : Type) (P Q : T -> Prop) : @ex2 T P Q <-> @ex2 T Q P.
Proof. by split; case=> x H0 H1; exists x. Qed.

Module TripA.
Section def.
Variables (A B C : finType) (P : {fdist A * B * C}).
Definition f (x : A * B * C) := (x.1.1, (x.1.2, x.2)).
Lemma inj_f : injective f.
Proof. by rewrite /f => -[[? ?] ?] [[? ?] ?] /= [-> -> ->]. Qed.
Definition d : {fdist A * (B * C)} := FDistMap.d f P.
Lemma dE x : d x = P (x.1, x.2.1, x.2.2).
Proof.
case: x => a [b c]; rewrite /d FDistMap.dE /= -/(f (a, b, c)) big_pred1_inj //.
exact/inj_f.
Qed.

Lemma domin a b c : d (a, (b, c)) = 0 -> P (a, b, c) = 0.
Proof. by rewrite dE. Qed.

Lemma dominN a b c : P (a, b, c) != 0 -> d (a, (b, c)) != 0.
Proof. by apply: contra => /eqP H; apply/eqP; apply: domin H. Qed.
End def.
Section prop.
Variables (A B C : finType) (P : {fdist A * B * C}).
Implicit Types (E : {set A}) (F : {set B}) (G : {set C}).

Lemma fst : Bivar.fst (d P) = Bivar.fst (Bivar.fst P).
Proof. by rewrite /Bivar.fst /d 2!FDistMap.comp. Qed.

Lemma fst_snd : Bivar.fst (Bivar.snd (d P)) = Bivar.snd (Bivar.fst P).
Proof. by rewrite /d /Bivar.snd /Bivar.fst /= !FDistMap.comp. Qed.

Lemma snd_snd : Bivar.snd (Bivar.snd (d P)) = Bivar.snd P.
Proof. by rewrite /d /Bivar.snd !FDistMap.comp. Qed.

Lemma snd_swap : Bivar.snd (Swap.d (d P)) = Bivar.fst (Bivar.fst P).
Proof. by rewrite /d /Bivar.snd /Swap.d /Bivar.fst /= 3!FDistMap.comp. Qed.

Lemma snd_fst_swap : Bivar.snd (Bivar.fst (Swap.d (d P))) = Bivar.snd P.
Proof. by rewrite /Bivar.snd /Bivar.fst /Swap.d !FDistMap.comp. Qed.

Lemma imset E F G : [set f x | x in (E `* F) `* G] = E `* (F `* G).
Proof.
apply/setP=> -[a [b c]]; apply/imsetP/idP.
- rewrite ex2C; move=> [[[a' b'] c']] /eqP.
  by rewrite /f !inE !xpair_eqE /= => /andP [] /eqP -> /andP [] /eqP -> /eqP -> /andP [] /andP [] -> -> ->.
- by rewrite !inE /= => /andP [aE /andP [bF cG]]; exists ((a, b), c); rewrite // !inE /= aE bF cG.
Qed.

Lemma Pr E F G : Pr (d P) (E `* (F `* G)) = Pr P (E `* F `* G).
Proof. by rewrite /d (Pr_FDistMap (@inj_f A B C)) imset. Qed.

End prop.
End TripA.
Arguments TripA.inj_f {A B C}.

Module TripA'.
Section def.
Variables (A B C : finType) (P : {fdist A * (B * C)}).
Definition f (x : A * (B * C)) := (x.1, x.2.1, x.2.2).
Lemma inj_f : injective f.
Proof. by rewrite /f => -[? [? ?]] [? [? ?]] /= [-> -> ->]. Qed.
Definition d : {fdist A * B * C} := FDistMap.d f P.
Lemma dE x : d x = P (x.1.1, (x.1.2, x.2)).
Proof.
case: x => -[a b] c; rewrite /d FDistMap.dE /= -/(f (a, (b, c))).
by rewrite (big_pred1_inj inj_f).
Qed.
End def.
Section prop.
Variables (A B C : finType) (P : {fdist A * (B * C)}).
Lemma Pr a b c : Pr P (a `* (b `* c)) = Pr (d P) ((a `* b) `* c).
Proof.
rewrite /Pr !big_setX /=; apply eq_bigr => a0 _.
rewrite !big_setX; apply eq_bigr => b0 _; apply eq_bigr => c0 _; by rewrite dE.
Qed.
End prop.
End TripA'.
Arguments TripA'.inj_f {A B C}.

Module TripC12.
Section def.
Variables (A B C : finType) (P : {fdist A * B * C}).
Let f (x : A * B * C) := (x.1.2, x.1.1, x.2).
Lemma inj_f : injective f.
Proof. by rewrite /f => -[[? ?] ?] [[? ?] ?] /= [-> -> ->]. Qed.
Definition d : {fdist B * A * C} := FDistMap.d f P.
Lemma dE x : d x = P (x.1.2, x.1.1, x.2).
Proof.
case: x => -[b a] c; rewrite /d FDistMap.dE /= -/(f (a, b, c)).
by rewrite (big_pred1_inj inj_f).
Qed.

Lemma snd : Bivar.snd d = Bivar.snd P.
Proof. by rewrite /Bivar.snd /d FDistMap.comp. Qed.

Lemma fst : Bivar.fst d = Swap.d (Bivar.fst P).
Proof. by rewrite /Bivar.fst /d /Swap.d 2!FDistMap.comp. Qed.

Lemma fstA : Bivar.fst (TripA.d d) = Bivar.snd (Bivar.fst P).
Proof. by rewrite /Bivar.fst /TripA.d /Bivar.snd !FDistMap.comp. Qed.
End def.
Section prop.
Variables (A B C : finType) (P : {fdist A * B * C}).
Lemma dI : d (d P) = P.
Proof.
rewrite /d FDistMap.comp (_ : _ \o _ = ssrfun.id) ?FDistMap.id //.
by rewrite boolp.funeqE => -[[]].
Qed.
Lemma Pr E F G : Pr (d P) (E `* F `* G) = Pr P (F `* E `* G).
Proof.
rewrite /Pr !big_setX /= exchange_big; apply eq_bigr => a aF.
by apply eq_bigr => b bE; apply eq_bigr => c cG; rewrite dE.
Qed.
End prop.
End TripC12.

Module TripAC.
Section def.
Variables (A B C : finType) (P : {fdist A * B * C}).
Definition f := fun x : A * B * C => (x.1.1, x.2, x.1.2).
Lemma inj_f : injective f. Proof. by move=> -[[? ?] ?] [[? ?] ?] [-> -> ->]. Qed.
Definition d : {fdist A * C * B} := Swap.d (TripA.d (TripC12.d P)).
Lemma dE x : d x = P (x.1.1, x.2, x.1.2).
Proof. by case: x => x1 x2; rewrite /d Swap.dE TripA.dE TripC12.dE. Qed.
End def.
Section prop.
Variables (A B C : finType) (P : {fdist A * B * C}).
Implicit Types (E : {set A}) (F : {set B}) (G : {set C}).

Lemma snd : Bivar.snd (d P) = Bivar.snd (Bivar.fst P).
Proof. by rewrite /d Swap.snd TripC12.fstA. Qed.

Lemma fstA : Bivar.fst (TripA.d (d P)) = Bivar.fst (TripA.d P).
Proof. by rewrite /Bivar.fst !FDistMap.comp. Qed.

Lemma fst_fst : Bivar.fst (Bivar.fst (d P)) = Bivar.fst (Bivar.fst P).
Proof. by rewrite /Bivar.fst !FDistMap.comp. Qed.

Lemma sndA : Bivar.snd (TripA.d (d P)) = Swap.d (Bivar.snd (TripA.d P)).
Proof. by rewrite /Bivar.snd /Swap.d !FDistMap.comp. Qed.

Lemma imset E F G : [set f x | x in E `* F `* G] = E `* G `* F.
Proof.
apply/setP => -[[a c] b]; apply/imsetP/idP.
- rewrite ex2C; move=> [[[a' b'] c']] /eqP.
  by rewrite /f !inE !xpair_eqE /= => /andP [] /andP [] /eqP -> /eqP -> /eqP -> /andP [] /andP [] -> -> ->.
- by rewrite !inE /= => /andP [] /andP [] aE cG bF; exists ((a, b), c); rewrite // !inE  /= aE cG bF.
Qed.

Lemma Pr E F G : Pr (d P) (E `* G `* F) = Pr P (E `* F `* G).
Proof. by rewrite /d -Swap.Pr TripA.Pr TripC12.Pr. Qed.
End prop.
End TripAC.
Arguments TripAC.inj_f {A B C}.

Module TripC13.
Section def.
Variables (A B C : finType) (P : {fdist A * B * C}).
Definition d : {fdist C * B * A} := TripC12.d (Swap.d (TripA.d P)).
Lemma dE x : d x = P (x.2, x.1.2, x.1.1).
Proof. by rewrite /d TripC12.dE Swap.dE TripA.dE. Qed.

Lemma fst : Bivar.fst d = Swap.d (Bivar.snd (TripA.d P)).
Proof. by rewrite /d /Bivar.fst /Swap.d !FDistMap.comp. Qed.

Lemma snd : Bivar.snd d = Bivar.fst (Bivar.fst P).
Proof. by rewrite /d TripC12.snd TripA.snd_swap. Qed.

Lemma fst_fst : Bivar.fst (Bivar.fst d) = Bivar.snd P.
Proof. by rewrite /Bivar.fst /Bivar.snd !FDistMap.comp. Qed.

Lemma sndA : Bivar.snd (TripA.d d) = Swap.d (Bivar.fst P).
Proof. by rewrite /Bivar.snd /Swap.d !FDistMap.comp. Qed.
End def.
End TripC13.

Module Proj13.
Section def.
Variables (A B C : finType) (P : {fdist A * B * C}).
Definition d : {fdist A * C} := Bivar.snd (TripA.d (TripC12.d P)).
Lemma dE x : d x = \sum_(b in B) P (x.1, b, x.2).
Proof.
rewrite /d Bivar.sndE; apply eq_bigr => b _; by rewrite TripA.dE TripC12.dE.
Qed.

Lemma domin a b c : d (a, c) = 0 -> P (a, b, c) = 0.
Proof. by rewrite dE /= => /psumR_eq0P ->. Qed.

Lemma dominN a b c : P (a, b, c) != 0 -> d (a, c) != 0.
Proof. by apply: contra => /eqP H; apply/eqP/domin. Qed.

Lemma snd : Bivar.snd d = Bivar.snd P.
Proof. by rewrite /d TripA.snd_snd TripC12.snd. Qed.

Lemma fst : Bivar.fst d = Bivar.fst (TripA.d P).
Proof. by rewrite /d TripA.fst_snd TripC12.fst Swap.snd TripA.fst. Qed.

End def.
End Proj13.

Module Proj23.
Section def.
Variables (A B C : finType) (P : {fdist A * B * C}).
Definition d : {fdist B * C} := Bivar.snd (TripA.d P).
Lemma dE x : d x = \sum_(a in A) P (a, x.1, x.2).
Proof. by rewrite /d Bivar.sndE; apply eq_bigr => a _; rewrite TripA.dE. Qed.

Lemma domin a b c : d (b, c) = 0 -> P (a, b, c) = 0.
Proof. by rewrite dE /= => /psumR_eq0P ->. Qed.

Lemma dominN a b c : P (a, b, c) != 0 -> d (b, c) != 0.
Proof. by apply: contra => /eqP H; apply/eqP; apply: domin. Qed.

Lemma fst : Bivar.fst d = Bivar.snd (Bivar.fst P).
Proof. by rewrite /d TripA.fst_snd. Qed.
Lemma snd : Bivar.snd d = Bivar.snd P.
Proof. by rewrite /d TripA.snd_snd. Qed.
End def.
Section prop.
Variables (A B C : finType) (P : {fdist A * B * C}).
Implicit Types (E : {set A}) (F : {set B}) (G : {set C}).
Lemma Pr_domin E F G :
  Pr (d P) (F `* G) = 0 -> Pr P (E `* F `* G) = 0.
Proof.
move/Pr_set0P => H; apply/Pr_set0P => -[[? ?] ?].
rewrite !inE /= -andbA => /and3P[aE bF cG].
by apply/domin/H; rewrite inE /= bF cG.
Qed.
End prop.
End Proj23.

Section Proj_prop.
Variables (A B C : finType) (P : {fdist A * B * C}).
Lemma Proj13_TripAC : Proj13.d (TripAC.d P) = Bivar.fst P.
Proof.
rewrite /Proj13.d /Bivar.snd /TripA.d /TripC12.d /TripAC.d /Bivar.fst.
rewrite !FDistMap.comp /=; congr (FDistMap.d _ _).
by rewrite boolp.funeqE => -[[]].
Qed.
End Proj_prop.

(* TODO: move to proba.v? *)
Section Pr_extra.

Variables (A B : finType) (P : {fdist A * B}).
Implicit Types (E : {set A}) (F : {set B}).

Lemma Pr_XsetT E : Pr P (E `* [set: B]) = Pr (Bivar.fst P) E.
Proof.
rewrite [in RHS]/Pr; under [in RHS]eq_bigr do rewrite Bivar.fstE.
rewrite /Pr big_setX /=; apply eq_bigr => a aE.
by rewrite [in RHS]sumR_setT; apply eq_bigl => b; rewrite andbT.
Qed.

Lemma Pr_setTX F : Pr P ([set: A] `* F) = Pr (Bivar.snd P) F.
Proof.
rewrite /Pr big_setX /= exchange_big; apply eq_bigr => a aE.
by rewrite Bivar.sndE /=; apply eq_bigl => b; rewrite inE.
Qed.

Lemma PrX_snd F : \sum_(a in A) Pr P ([set a] `* F) = Pr (Bivar.snd P) F.
Proof.
rewrite -Pr_setTX /Pr sumR_setT big_setX /=.
by apply eq_big => a; rewrite andbT // => _; rewrite big_setX /= big_set1.
Qed.

Lemma PrX_fst E : \sum_(b in B) Pr P (E `* [set b]) = Pr (Bivar.fst P) E.
Proof.
rewrite -Pr_XsetT /Pr sumR_setT big_setX /= [in RHS]exchange_big /=.
apply eq_big => b /=; rewrite andbT // => _.
by rewrite big_setX /= exchange_big big_set1.
Qed.

End Pr_extra.

Section conditional_probability.

Variables (A B : finType) (P : {fdist A * B}).
Implicit Types (E : {set A}) (F : {set B}).

Definition jcPr E F := Pr P (E `* F) / Pr (Bivar.snd P) F.

Local Notation "\Pr_[ E | F ]" := (jcPr E F).

Lemma jcPrE E F : \Pr_[E | F] = `Pr_P [E `*T | T`* F].
Proof. by rewrite /jcPr -Pr_setTX setTE /cPr EsetT setIX !(setIT,setTI). Qed.

Lemma jcPrET E : \Pr_[E | setT] = Pr (Bivar.fst P) E.
Proof. by rewrite jcPrE TsetT cPrET -Pr_XsetT EsetT. Qed.

Lemma jcPrE0 E : \Pr_[E | set0] = 0.
Proof. by rewrite jcPrE Tset0 cPrE0. Qed.

Lemma jcPr_ge0 E F : 0 <= \Pr_[E | F].
Proof. by rewrite jcPrE. Qed.

Lemma jcPr_max E F : \Pr_[E | F] <= 1.
Proof. by rewrite jcPrE; apply cPr_max. Qed.

Lemma jcPr_gt0 E F : 0 < \Pr_[E | F] <-> \Pr_[E | F] != 0.
Proof. by rewrite !jcPrE; apply cPr_gt0. Qed.

Lemma Pr_jcPr_gt0 E F : 0 < Pr P (E `* F) <-> 0 < \Pr_[E | F].
Proof.
split.
- rewrite -{1}(setIT E) -{1}(setIT F) (setIC F) -setIX jcPrE.
  by move/Pr_cPr_gt0; rewrite -setTE -EsetT.
- move=> H; rewrite -{1}(setIT E) -{1}(setIT F) (setIC F) -setIX.
  by apply/Pr_cPr_gt0; move: H; rewrite jcPrE -setTE -EsetT.
Qed.

Lemma jcPr_cplt E F : Pr (Bivar.snd P) F != 0 ->
  \Pr_[ ~: E | F] = 1 - \Pr_[E | F].
Proof.
by move=> PF0; rewrite 2!jcPrE EsetT setCX cPr_cplt ?EsetT // setTE Pr_setTX.
Qed.

Lemma jcPr_diff E1 E2 F : \Pr_[E1 :\: E2 | F] = \Pr_[E1 | F] - \Pr_[E1 :&: E2 | F].
Proof.
rewrite jcPrE DsetT cPr_diff jcPrE; congr (_ - _).
by rewrite 2!EsetT setIX setTI -EsetT jcPrE.
Qed.

Lemma jcPr_union_eq E1 E2 F :
  \Pr_[E1 :|: E2 | F] = \Pr_[E1 | F] + \Pr_[E2 | F] - \Pr_[E1 :&: E2 | F].
Proof. by rewrite jcPrE UsetT cPr_union_eq !jcPrE IsetT. Qed.

Section total_probability.

Variables (I : finType) (E : {set A}) (F : I -> {set B}).
Let P1 := Bivar.fst P.  Let P2 := Bivar.snd P. Let P' := Swap.d P.
Hypothesis dis : forall i j, i != j -> [disjoint F i & F j].
Hypothesis cov : cover (F @: I) = [set: B].

Lemma jtotal_prob_cond :
  Pr P1 E = \sum_(i in I) \Pr_[E | F i] * Pr P2 (F i).
Proof.
rewrite -Pr_XsetT -EsetT.
rewrite (@total_prob_cond _ _ _ _ (fun i => T`* F i)); last 2 first.
  move=> i j ij; rewrite -setI_eq0 !setTE setIX setTI.
  by move: (dis ij); rewrite -setI_eq0 => /eqP ->; rewrite setX0.
  (* TODO: lemma? *)
  apply/setP => -[a b]; rewrite inE /cover.
  apply/bigcupP => /=.
  move: cov; rewrite /cover => /setP /(_ b).
  rewrite !inE => /bigcupP[b'].
  move/imsetP => [i _ ->{b'} bFi].
  exists (T`* F i).
  by apply/imsetP; exists i.
  by rewrite inE.
apply eq_bigr => i _.
rewrite -Pr_setTX -setTE; congr (_ * _).
by rewrite jcPrE.
Qed.

End total_probability.

End conditional_probability.

Notation "\Pr_ P [ E | F ]" := (jcPr P E F) : proba_scope.

Section bayes.
Variables (A B : finType) (PQ : {fdist A * B}).
Let P := Bivar.fst PQ. Let Q := Bivar.snd PQ. Let QP := Swap.d PQ.
Implicit Types (E : {set A}) (F : {set B}).

Lemma jBayes E F : \Pr_PQ[E | F] = \Pr_QP [F | E] * Pr P E / Pr Q F.
Proof.
rewrite 2!jcPrE Bayes /Rdiv -2!mulRA.
rewrite EsetT Pr_XsetT setTE Pr_setTX /cPr; congr ((_ / _) * (_ / _)).
by rewrite /QP setIX Swap.Pr -setIX -EsetT -setTE.
by rewrite Swap.Pr -setTE.
Qed.

Lemma jBayes_extended (I : finType) (E : I -> {set A}) (F : {set B}) :
  (forall i j, i != j -> [disjoint E i & E j]) ->
  cover [set E i | i in I] = [set: A] ->
  forall i,
  \Pr_PQ [E i | F] = (\Pr_QP [F | E i] * Pr P (E i)) /
                     \sum_(j in I) \Pr_ QP [F | E j] * Pr P (E j).
Proof.
move=> dis cov i; rewrite jBayes; congr (_ / _).
move: (@jtotal_prob_cond _ _ QP I F E dis cov).
rewrite {1}/QP Swap.fst => ->.
by apply eq_bigr => j _; rewrite -/QP {2}/QP Swap.snd.
Qed.

End bayes.

Section conditional_probability_prop3.
Variables (A B C : finType) (P : {fdist A * B * C}).

Lemma jcPr_TripC12 (E : {set A}) (F : {set B }) (G : {set C}) :
  \Pr_(TripC12.d P)[F `* E | G] = \Pr_P[E `* F | G].
Proof. by rewrite /jcPr TripC12.Pr TripC12.snd. Qed.

Lemma jcPr_TripA_TripAC (E : {set A}) (F : {set B}) (G : {set C}) :
  \Pr_(TripA.d (TripAC.d P))[E | G `* F] = \Pr_(TripA.d P)[E | F `* G].
Proof.
rewrite /jcPr 2!TripA.Pr TripAC.Pr; congr (_ / _).
by rewrite TripAC.sndA Swap.Pr Swap.dI.
Qed.

Lemma jcPr_TripA_TripC12 (E : {set A}) (F : {set B}) (G : {set C}) :
  \Pr_(TripA.d (TripC12.d P))[F | E `* G] = \Pr_(TripA.d (Swap.d (TripA.d P)))[F | G `* E].
Proof.
rewrite /jcPr; congr (_ / _).
by rewrite TripA.Pr TripC12.Pr TripA.Pr [in RHS]Swap.Pr Swap.dI TripA.Pr.
rewrite -/(Proj13.d _) -(Swap.dI (Proj13.d P)) Swap.Pr Swap.dI; congr Pr.
(* TODO: lemma? *)
by rewrite /Proj13.d /Swap.d /Bivar.snd /TripA.d !FDistMap.comp.
Qed.

End conditional_probability_prop3.

Section product_rule.

Section main.
Variables (A B C : finType) (P : {fdist A * B * C}).
Implicit Types (E : {set A}) (F : {set B}) (G : {set C}).
Lemma jproduct_rule_cond E F G :
  \Pr_P [E `* F | G] = \Pr_(TripA.d P) [E | F `* G] * \Pr_(Proj23.d P) [F | G].
Proof.
rewrite /jcPr; rewrite !mulRA; congr (_ * _); last by rewrite Proj23.snd.
rewrite -mulRA -/(Proj23.d _) -TripA.Pr.
case/boolP : (Pr (Proj23.d P) (F `* G) == 0) => H; last by rewrite mulVR ?mulR1.
suff -> : Pr (TripA.d P) (E `* (F `* G)) = 0 by rewrite mul0R.
rewrite TripA.Pr; exact/Proj23.Pr_domin/eqP.
Qed.
End main.

Section variant.
Variables (A B C : finType) (P : {fdist A * B * C}).
Implicit Types (E : {set A}) (F : {set B}) (G : {set C}).
Lemma product_ruleC E F G :
  \Pr_P [ E `* F | G] = \Pr_(TripA.d (TripC12.d P)) [F | E `* G] * \Pr_(Proj13.d P) [E | G].
Proof. by rewrite -jcPr_TripC12 jproduct_rule_cond. Qed.
End variant.

Section prod.
Variables (A B : finType) (P : {fdist A * B}).
Implicit Types (E : {set A}) (F : {set B}).
Lemma jproduct_rule E F : Pr P (E `* F) = \Pr_P[E | F] * Pr (Bivar.snd P) F.
Proof.
have [/eqP PF0|PF0] := boolP (Pr (Bivar.snd P) F == 0).
  rewrite jcPrE /cPr -{1}(setIT E) -{1}(setIT F) -setIX.
  rewrite Pr_domin_setI; last by rewrite Swap.Pr Pr_domin_setX // Swap.fst.
  by rewrite setIC Pr_domin_setI ?(div0R,mul0R) // setTE Pr_setTX.
rewrite -{1}(setIT E) -{1}(setIT F) -setIX product_rule.
rewrite -EsetT setTT cPrET Pr_setT mulR1 jcPrE.
rewrite /cPr {1}setTE {1}EsetT.
by rewrite setIX setTI setIT setTE Pr_setTX -mulRA mulVR ?mulR1.
Qed.
End prod.

End product_rule.

Lemma Pr_FDistMap_r (A B B' : finType) (f : B -> B') (d : {fdist A * B}) (E : {set A}) (F : {set B}):
  injective f ->
  \Pr_d [E | F] = \Pr_(FDistMap.d (fun x => (x.1, f x.2)) d) [E | f @: F].
Proof.
move=> injf; rewrite /jcPr; congr (_ / _).
- rewrite (@Pr_FDistMap _ _ (fun x => (x.1, f x.2))) /=; last by move=> [? ?] [? ?] /= [-> /injf ->].
  congr (Pr _ _); apply/setP => -[a b]; rewrite !inE /=.
  apply/imsetP/andP.
  - case=> -[a' b']; rewrite inE /= => /andP[a'E b'F] [->{a} ->{b}]; split => //.
    apply/imsetP; by exists b'.
  - case=> aE /imsetP[b' b'F] ->{b}; by exists (a, b') => //; rewrite inE /= aE.
by rewrite /Bivar.snd FDistMap.comp (@Pr_FDistMap _ _ f) // FDistMap.comp.
Qed.
Arguments Pr_FDistMap_r [A] [B] [B'] [f] [d] [E] [F] _.

Lemma Pr_FDistMap_l (A A' B : finType) (f : A -> A') (d : {fdist A * B}) (E : {set A}) (F : {set B}):
  injective f ->
  \Pr_d [E | F] = \Pr_(FDistMap.d (fun x => (f x.1, x.2)) d) [f @: E | F].
Proof.
move=> injf; rewrite /jcPr; congr (_ / _).
- rewrite (@Pr_FDistMap _ _ (fun x => (f x.1, x.2))) /=; last by move=> [? ?] [? ?] /= [/injf -> ->].
  congr (Pr _ _); apply/setP => -[a b]; rewrite !inE /=.
  apply/imsetP/andP.
  - case=> -[a' b']; rewrite inE /= => /andP[a'E b'F] [->{a} ->{b}]; split => //.
    apply/imsetP; by exists a'.
  - by case=> /imsetP[a' a'E] ->{a} bF; exists (a', b) => //; rewrite inE /= a'E.
by rewrite /Bivar.snd !FDistMap.comp.
Qed.
Arguments Pr_FDistMap_l [A] [A'] [B] [f] [d] [E] [F] _.

(* TODO: move? *)
Lemma Pr_jcPr_unit (A : finType) (E : {set A}) (P : {fdist A}) :
  Pr P E = \Pr_(FDistMap.d (fun a => (a, tt)) P) [E | setT].
Proof.
rewrite /jcPr (Pr_set1 _ tt).
rewrite (_ : Bivar.snd _ = FDist1.d tt) ?FDist1.dE ?eqxx ?divR1; last first.
  rewrite /Bivar.snd FDistMap.comp; apply/fdist_ext; case.
  by rewrite FDistMap.dE FDist1.dE /= (eq_bigl xpredT) // FDist.f1.
rewrite /Pr big_setX /=; apply eq_bigr => a _; rewrite (big_set1 _ tt) /=.
rewrite FDistMap.dE (big_pred1 a) // => a0; rewrite inE /=.
by apply/eqP/eqP => [[] -> | ->].
Qed.

Module CondJFDist0.
Section def.
Variables (A B : finType) (PQ : {fdist A * B}) (a : A).
Hypothesis Ha : Bivar.fst PQ a != 0.
Definition f := [ffun b => \Pr_(Swap.d PQ) [[set b] | [set a]]].
Lemma f0 b : 0 <= f b. Proof. rewrite ffunE; exact: jcPr_ge0. Qed.
Lemma f1 : \sum_(b in B) f b = 1.
Proof.
under eq_bigr do rewrite ffunE.
by rewrite /jcPr -big_distrl /= PrX_snd mulRV // Pr_set1 Swap.snd.
Qed.
Definition d : {fdist B} := locked (FDist.make f0 f1).
Lemma dE b : d b = \Pr_(Swap.d PQ) [[set b] | [set a]].
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
End def.
End CondJFDist0.
Arguments CondJFDist0.d {A} {B} _ _ _.

Module CondJFDist.
Section def.
Variables (A B : finType) (PQ : {fdist A * B}) (a : A).
Let Ha := Bivar.fst PQ a != 0.
Lemma sizeB : #|B| = #|B|.-1.+1.
Proof.
case HB: #|B| => //.
move: (fdist_card_neq0 PQ); by rewrite card_prod HB muln0 ltnn.
Qed.
Definition d :=
  match boolP Ha with
  | AltTrue H => CondJFDist0.d PQ _ H
  | AltFalse _ => Uniform.d sizeB
  end.
Lemma dE (H : Ha) b : d b = \Pr_(Swap.d PQ) [[set b] | [set a]].
Proof.
rewrite /d; destruct boolP.
  by rewrite CondJFDist0.dE.
by rewrite H in i.
Qed.
Lemma dNE (H : ~~ Ha) : d = Uniform.d sizeB.
Proof.
rewrite /d; destruct boolP => //.
by rewrite i in H.
Qed.
End def.
End CondJFDist.
Notation "P `(| a ')'" := (CondJFDist.d P a).

Lemma cPr_1 (U : finType) (P : fdist U) (A B : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) a : `Pr[X = a] != 0 ->
  \sum_(b <- fin_img Y) `Pr[ Y = b | X = a ] = 1.
Proof.
rewrite -pr_eq_set1 pr_inE' Pr_set1 -{1}(fst_RV2 _ Y) => Xa0.
set Q := `d_[% X, Y] `(| a ).
rewrite -(FDist.f1 Q) [in RHS](bigID (mem (fin_img Y))) /=.
rewrite [X in _ = _ + X](eq_bigr (fun=> 0)); last first.
  move=> b bY.
  rewrite /Q CondJFDist.dE // /jcPr /Pr !(big_setX,big_set1) /= Swap.dE Swap.snd fst_RV2.
  rewrite -!pr_eqE' !pr_eqE.
  rewrite /Pr big1 ?div0R // => u.
  rewrite inE => /eqP[Yub ?].
  exfalso.
  move/negP : bY; apply.
  rewrite mem_undup; apply/mapP; exists u => //; by rewrite mem_enum.
rewrite big_const iter_addR mulR0 addR0.
rewrite big_uniq; last by rewrite /fin_img undup_uniq.
apply eq_bigr => b; rewrite mem_undup => /mapP[u _ bWu].
rewrite /Q CondJFDist.dE // Swap_RV2.
rewrite jcPrE -cpr_inE'.
by rewrite cpr_eq_set1.
Qed.

Section condjfdist_prop.

Variables (A B : finType) (P : {fdist A * B}).

Lemma jcPr_1 a : Bivar.fst P a != 0 ->
  \sum_(b in B) \Pr_(Swap.d P)[ [set b] | [set a] ] = 1.
Proof.
move=> Xa0; rewrite -(FDist.f1 (P `(| a ))).
apply eq_bigr => b _; by rewrite CondJFDist.dE.
Qed.

End condjfdist_prop.

Module CJFDist.
Section def.
Variables (A B : finType).
Record t := mkt {P : fdist A ; W :> A -> fdist B}.
Definition joint_of (x : t) : {fdist A * B} := ProdFDist.d (P x) (W x).
Definition make_joint (P : fdist A) (W : A -> fdist B) : {fdist A * B} :=
  joint_of (mkt P W).
Lemma CondJFDistE (x : t) : forall a (a0 : Bivar.fst (joint_of x) a != 0),
  x a = (joint_of x) `(| a ).
Proof.
move=> a a0; apply/fdist_ext => b.
rewrite CondJFDist.dE // /jcPr setX1 !Pr_set1 /P Swap.dE Swap.snd ProdFDist.fst.
rewrite ProdFDist.dE /= /Rdiv mulRAC mulRV ?mul1R //.
by move: a0; rewrite ProdFDist.fst.
Qed.
Lemma E (x : t) a b : (P x) a <> 0 ->
  x a b = \Pr_(Swap.d (joint_of x))[[set b]|[set a]].
Proof.
move=> Pxa.
rewrite /jcPr setX1 Swap.snd 2!Pr_set1 /joint_of Swap.dE ProdFDist.fst.
rewrite ProdFDist.dE /= /Rdiv mulRAC mulRV ?mul1R //; exact/eqP.
Qed.
Definition split (PQ : {fdist A * B}) := mkt (Bivar.fst PQ) (fun x => PQ `(| x )).
Lemma splitK : cancel split joint_of.
Proof.
move=> PQ.
rewrite /joint_of /split /=.
apply/fdist_ext => ab.
rewrite ProdFDist.dE.
case /boolP: (Bivar.fst PQ ab.1 == 0) => Ha.
  rewrite (eqP Ha) mul0R.
  symmetry.
  apply (dominatesE (Prod_dominates_Joint PQ)).
  by rewrite ProdFDist.dE (eqP Ha) mul0R.
rewrite CondJFDist.dE // -Swap.snd mulRC.
rewrite -(Pr_set1 _ ab.1) -jproduct_rule setX1 Pr_set1 Swap.dE.
by destruct ab.
Qed.
End def.
End CJFDist.
Definition cjfdistw (A B : finType) (x : CJFDist.t A B) := CJFDist.W x.
Coercion cjfdistw : CJFDist.t >-> Funclass.

Local Open Scope vec_ext_scope.

(* TODO: move? *)
Section row_mxA'.
Variables (A : finType) (n : nat) (i : 'I_n.+1).
Lemma row_mxA' (w1 : 'rV_(n - i)) (a : A) (w : 'rV_i) (H1 : (n.+1 - i)%nat = (n - i)%nat.+1)
  (H2 : _) (H3 : (i + 1%nat + (n - i))%nat = n.+1) :
  castmx (erefl 1%nat, H3) (row_mx (row_mx w (\row__ a)) w1) =
  castmx (erefl 1%nat, H2) (row_mx w (castmx (erefl 1%nat, esym H1) (row_mx (\row_(_ < 1) a) w1))).
Proof.
apply/rowP => j.
rewrite !castmxE /= !cast_ord_id /=.
case: (ltnP j i) => [ji|].
  move=> [:Hj0].
  have @j0 : 'I_(i + 1) by apply: (@Ordinal _ j); abstract: Hj0; rewrite addn1 ltnS ltnW.
  rewrite (_ : cast_ord _ _ = lshift (n - i) j0); last exact/val_inj.
  rewrite row_mxEl.
  rewrite (_ : cast_ord _ _ = lshift (n.+1 - i) (Ordinal ji)); last exact/val_inj.
  rewrite row_mxEl.
  rewrite (_ : j0 = lshift 1 (Ordinal ji)); last exact/val_inj.
  by rewrite row_mxEl.
rewrite leq_eqVlt => /orP[/eqP|]ij.
  move=> [:Hj0].
  have @j0 : 'I_(i + 1) by apply: (@Ordinal _ j); abstract: Hj0; by rewrite addn1 ij ltnS.
  rewrite (_ : cast_ord _ _ = lshift (n - i) j0); last exact/val_inj.
  rewrite row_mxEl.
  rewrite (_ : j0 = rshift i ord0); last first.
    by apply val_inj => /=; rewrite ij addn0.
  rewrite row_mxEr mxE.
  move=> [:Hj1].
  have @j1 : 'I_(n.+1 - i).
    by apply: (@Ordinal _ 0); abstract: Hj1; rewrite subn_gt0.
  rewrite (_ : cast_ord _ _ = rshift i j1); last first.
    by apply/val_inj => /=; rewrite ij addn0.
  rewrite row_mxEr castmxE /= cast_ord_id esymK.
  have @j2 : 'I_1 := ord0.
  rewrite (_ : cast_ord _ _ = lshift (n - i) j2); last exact/val_inj.
  by rewrite (@row_mxEl _ _ 1%nat) mxE.
move=> [:Hj0].
have @j0 : 'I_(n - i).
  apply: (@Ordinal _ (j - i.+1)); abstract: Hj0.
  by rewrite subnS prednK ?subn_gt0 // leq_sub2r // -ltnS.
rewrite (_ : cast_ord _ _ = rshift (i + 1) j0); last first.
  apply/val_inj => /=; by rewrite addn1 subnKC.
rewrite row_mxEr.
have @j1 : 'I_(n.+1 - i) by apply: (@Ordinal _ (j - i)); rewrite ltn_sub2r.
rewrite (_ : cast_ord _ _ = rshift i j1); last first.
  by apply val_inj => /=; rewrite subnKC // ltnW.
rewrite row_mxEr castmxE /= cast_ord_id.
have @j2 : 'I_(n - i).
  apply: (@Ordinal _ (j1 - 1)).
  by rewrite /= subn1 prednK ?subn_gt0 // leq_sub2r // -ltnS.
rewrite (_ : cast_ord _ _ = rshift 1 j2); last first.
  apply/val_inj => /=; by rewrite subnKC // subn_gt0.
rewrite (@row_mxEr _ _ 1%nat); congr (_ _ _); apply val_inj => /=; by rewrite subnS subn1.
Qed.
End row_mxA'.

(* TODO: move? *)
Lemma head_of_fst_belast_last (A : finType) (n : nat) (P : {fdist 'rV[A]_n.+2}) :
  Multivar.head_of (Bivar.fst (Multivar.belast_last P)) = Multivar.head_of P.
Proof.
rewrite /Multivar.head_of /Bivar.fst /Multivar.to_bivar /Multivar.belast_last.
rewrite !FDistMap.comp; congr (FDistMap.d _ P).
rewrite boolp.funeqE => /= v /=.
rewrite /rbelast mxE; congr (v ord0 _); exact: val_inj.
Qed.

(* wip *)
Module Subvec.
Section def.
Variables (A : finType) (n : nat) (P : {fdist 'rV[A]_n}) (s : {set 'I_n}).
Definition d : {fdist 'rV[A]_#|s| } := FDistMap.d (fun x => sub_vec x s) P.
End def.
End Subvec.
Section subvec_prop.
Variables (A : finType) (n : nat) (P : {fdist 'rV[A]_n.+1}).
Definition marginal1_cast (i : 'I_n.+1) (v : 'rV[A]_#|[set i]|) : A :=
  (castmx (erefl, cards1 i) v) ``_ ord0.
Lemma head_ofE :
  Multivar.head_of P = FDistMap.d (@marginal1_cast ord0) (@Subvec.d A n.+1 P [set ord0]).
Proof.
apply fdist_ext => a.
rewrite FDistMap.dE /= /Multivar.head_of Bivar.fstE /= /Multivar.to_bivar.
under eq_bigr do rewrite FDistMap.dE /=.
rewrite /Subvec.d.
under [in RHS] eq_bigr do rewrite FDistMap.dE /=.
Abort.
End subvec_prop.

Module Nth.
Section def.
Variables (A : finType) (n : nat) (P : {fdist 'rV[A]_n}) (i : 'I_n).
Definition d : {fdist A} := FDistMap.d (fun v : 'rV[A]_n => v ``_ i) P.
Lemma dE a : d a = \sum_(x : 'rV[A]_n | x ``_ i == a) P x.
Proof. by rewrite FDistMap.dE. Qed.
End def.
Section prop.
Lemma head_ofE (A : finType) (n : nat) (P : {fdist 'rV[A]_n.+1}) :
  Multivar.head_of P = d P ord0.
Proof.
by rewrite /Multivar.head_of /d /Bivar.fst /Multivar.to_bivar FDistMap.comp.
Qed.
End prop.
End Nth.

Module PairNth.
Section def.
Variables (A B : finType) (n : nat) (P : {fdist 'rV[A]_n * B}) (i : 'I_n).
Definition d : {fdist A * B} :=
  FDistMap.d (fun x : 'rV[A]_n * B => (x.1 ord0 i, x.2)) P.
Lemma dE ab :
  d ab = \sum_(x : 'rV[A]_n * B | (x.1 ``_ i == ab.1) && (x.2 == ab.2)) P x.
Proof. by rewrite FDistMap.dE. Qed.
End def.
End PairNth.

Module MargFDist.
Section def.
Variables (A : finType) (n : nat) (P : {fdist 'rV[A]_n.+1}) (i : 'I_n.+1).
Definition d : {fdist 'rV[A]_n} := FDistMap.d (col' i) P.
Lemma dE v : d v = \sum_(x : 'rV[A]_n.+1 | col' i x == v) P x.
Proof. by rewrite FDistMap.dE. Qed.
End def.
Section prop.
Variables (A : finType) (n : nat) (P : {fdist 'rV[A]_n.+1}).
Lemma tail_ofE : Multivar.tail_of P = d P ord0.
Proof.
by rewrite /d /Multivar.tail_of /Bivar.snd /Multivar.to_bivar FDistMap.comp.
Qed.
End prop.
End MargFDist.

Module Take.
Section def.
Variable (A : finType) (n : nat) (P : {fdist 'rV[A]_n}).
Definition d (i : 'I_n.+1) : {fdist 'rV[A]_i} := FDistMap.d (row_take i) P.
Lemma dE i v : d i v = \sum_(w in 'rV[A]_(n - i))
  P (castmx (erefl, subnKC (ltnS' (ltn_ord i))) (row_mx v w)).
Proof.
rewrite FDistMap.dE /=.
rewrite (@reindex_onto _ _ _ [finType of 'rV[A]_n] [finType of 'rV[A]_(n - i)]
  (fun w => castmx (erefl 1%nat, subnKC (ltnS' (ltn_ord i))) (row_mx v w))
  (@row_drop A n i)) /=; last first.
  move=> w wv; apply/rowP => j.
  rewrite castmxE /= cast_ord_id /row_drop mxE; case: splitP => [j0 /= jj0|k /= jik].
  - rewrite -(eqP wv) mxE castmxE /= cast_ord_id; congr (w _ _); exact: val_inj.
  - rewrite mxE /= castmxE /= cast_ord_id; congr (w _ _); exact: val_inj.
apply eq_bigl => w; rewrite inE; apply/andP; split; apply/eqP/rowP => j.
- by rewrite !mxE !castmxE /= !cast_ord_id esymK cast_ordK row_mxEl.
- by rewrite !mxE !castmxE /= cast_ord_id esymK cast_ordK cast_ord_id row_mxEr.
Qed.
End def.
Section prop.
Lemma all (A : finType) (n : nat) (P : {fdist 'rV[A]_n.+2}) :
  d P (lift ord0 ord_max) = P.
Proof.
rewrite /d (_ : row_take (lift ord0 ord_max) = ssrfun.id) ?FDistMap.id //.
rewrite boolp.funeqE => v; apply/rowP => i.
rewrite /row_take mxE castmxE /= cast_ord_id; congr (v _ _); exact: val_inj.
Qed.
End prop.
End Take.
Arguments Take.dE {A} {n} _ _ _.

Lemma take_nth (A : finType) (n : nat) (P : {fdist 'rV[A]_n.+1}) (i : 'I_n.+1) :
  Bivar.snd (Multivar.belast_last (Take.d P (lift ord0 i))) = Nth.d P i.
Proof.
rewrite /Bivar.snd /Multivar.belast_last /Take.d /Nth.d !FDistMap.comp.
congr (FDistMap.d _ _); rewrite boolp.funeqE => /= v /=.
rewrite /rlast mxE castmxE /= cast_ord_id /=; congr (v ``_ _); exact: val_inj.
Qed.

Module PairTake.
Section def.
Variables (A B : finType) (n : nat) (P : {fdist 'rV[A]_n.+1 * B}) (i : 'I_n.+1).
Definition d : {fdist 'rV_i * A * B} :=
  FDistMap.d (fun x : 'rV[A]_n.+1 * B => (row_take (widen_ord (leqnSn _) i) x.1, x.1 ord0 i, x.2)) P.
End def.
End PairTake.

Section to_bivar_last_take.

Variables (A B : finType).
Variables (n : nat) (PY : {fdist 'rV[A]_n.+1 * B}).
Let P : {fdist 'rV[A]_n.+1} := Bivar.fst PY.

Lemma belast_last_take (j : 'I_n.+1) :
  Multivar.belast_last (Take.d P (lift ord0 j)) = Bivar.fst (PairTake.d PY j).
Proof.
rewrite /Multivar.belast_last /Take.d /Bivar.fst /PairTake.d !FDistMap.comp.
congr (FDistMap.d _ PY); rewrite boolp.funeqE => /= -[v b] /=; congr (_, _).
- apply/rowP => i.
  rewrite /rbelast !mxE !castmxE /=; congr (v _ _); exact: val_inj.
- rewrite /rlast mxE castmxE /=; congr (v _ _); exact: val_inj.
Qed.

End to_bivar_last_take.

(*TODO: move*)
Lemma col_perm_inj n (s : 'S_n) T m : injective (@col_perm T m n s).
Proof.
move=> x y; rewrite /col_perm => /matrixP xy; apply/matrixP => i j.
by move: (xy i (s^-1%g j)); rewrite !mxE permKV.
Qed.

Module MultivarPerm.
Section def.
Variables (A : finType) (n : nat) (P : {fdist 'rV[A]_n}) (s : 'S_n).
Definition d : {fdist 'rV[A]_n} := FDistMap.d (col_perm s^-1) P.
Lemma dE v : d v = P (col_perm s v).
Proof.
rewrite FDistMap.dE /= {1}(_ : v = col_perm s^-1 (col_perm s v)); last first.
  by rewrite -col_permM mulVg col_perm1.
rewrite big_pred1_inj //; exact: col_perm_inj.
Qed.
End def.
End MultivarPerm.

Module TakeDrop.
Section def.
Variables (A : finType) (n : nat) (P : {fdist 'rV[A]_n.+1}) (i : 'I_n.+1).
Definition d : {fdist A * 'rV[A]_i * 'rV[A]_(n - i)} :=
  FDistMap.d (fun x : 'rV[A]_n.+1 => (x ord0 ord0, row_take i (rbehead x), row_drop i (rbehead x))) P.
Let g (x : 'rV[A]_n.+1) : A * 'rV[A]_i * 'rV[A]_(n - i) :=
  (x ``_ ord0,
   row_take i (rbehead x),
   row_drop i (rbehead x)).
Lemma inj_g : injective g.
Proof.
move=> a b; rewrite /g => -[H1 H2 H3].
rewrite -(row_mx_rbehead a) -(row_mx_rbehead b) H1; congr (@row_mx _ 1%nat 1%nat _ _ _).
rewrite (row_mx_take_drop i (rbehead a)) (row_mx_take_drop i (rbehead b)).
by rewrite H2 H3.
Qed.
Lemma dE x : d x = P (row_mx (\row_(_ < 1) x.1.1) (castmx (erefl 1%nat, @subnKC i n (ltnS' (ltn_ord i))) (row_mx x.1.2 x.2))).
Proof.
rewrite /d FDistMap.dE /=.
rewrite (eq_bigl (fun a => g a == x)) //.
rewrite {1}(_ : x = g (row_mx (\row_(k<1) x.1.1) (castmx (erefl 1%nat, subnKC (ltnS' (ltn_ord i))) (row_mx x.1.2 x.2)))); last first.
  move: x => /= -[[x11 x12] x2].
  rewrite /g row_mx_row_ord0 /=; congr (_, _, _).
  apply/rowP => j; rewrite !mxE !castmxE /= cast_ord_id mxE esymK.
  have @k : 'I_n.
    by apply: (@Ordinal _ j); rewrite (leq_trans (ltn_ord j)) // -ltnS.
  rewrite (_ : lift _ _ = rshift 1%nat k); last first.
    by apply val_inj => /=; rewrite /bump leq0n.
  rewrite (@row_mxEr _ 1%nat 1%nat) // castmxE /= cast_ord_id.
  rewrite (_ : cast_ord _ k = lshift (n - i) j).
  by rewrite row_mxEl.
  exact: val_inj.
  apply/rowP => j; rewrite mxE castmxE /= cast_ord_id mxE esymK.
  have @k0 : 'I_n by apply: (@Ordinal _ (i + j)); rewrite -ltn_subRL.
  rewrite (_ : lift _ _ = rshift 1%nat k0); last first.
    apply val_inj => /=; by rewrite /bump leq0n.
  rewrite (@row_mxEr _ 1%nat 1%nat) castmxE /=.
  rewrite (_ : cast_ord _ _ = rshift i j); last exact: val_inj.
  by rewrite row_mxEr cast_ord_id.
by rewrite (big_pred1_inj inj_g).
Qed.
End def.
End TakeDrop.
