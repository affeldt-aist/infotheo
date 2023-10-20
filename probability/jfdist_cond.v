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
(*  jfdist_cond0 PQ a a0 == The conditional distribution derived from PQ      *)
(*                          given a; PQ is a joint distribution               *)
(*                          {fdist A * B}, a0 is a proof that                 *)
(*                          fdist_fst PQ a != 0, the result is a              *)
(*                          distribution {fdist B}                            *)
(*      jfdist_cond PQ a == The conditional distribution derived from PQ      *)
(*                          given a; same as fdist_cond0 when                 *)
(*                          fdist_fst PQ a != 0.                              *)
(*           PQ `(| a |) == notation jfdist_cond PQ a                         *)
(*                                                                            *)
(******************************************************************************)

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
Local Open Scope fdist_scope.

Section conditional_probability.
Variables (A B : finType) (P : {fdist A * B}).
Implicit Types (E : {set A}) (F : {set B}).

Definition jcPr E F := Pr P (E `* F) / Pr (P`2) F.

Local Notation "\Pr_[ E | F ]" := (jcPr E F).

Lemma jcPrE E F : \Pr_[E | F] = `Pr_P [E `*T | T`* F].
Proof. by rewrite /jcPr -Pr_setTX setTE /cPr EsetT setIX !(setIT,setTI). Qed.

Lemma jcPrET E : \Pr_[E | setT] = Pr P`1 E.
Proof. by rewrite jcPrE TsetT cPrET -Pr_XsetT EsetT. Qed.

Lemma jcPrE0 E : \Pr_[E | set0] = 0.
Proof. by rewrite jcPrE Tset0 cPrE0. Qed.

Lemma jcPr_ge0 E F : 0 <= \Pr_[E | F].
Proof. by rewrite jcPrE. Qed.

Lemma jcPr_le1 E F : \Pr_[E | F] <= 1.
Proof. by rewrite jcPrE; exact: cPr_max. Qed.

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

Lemma jcPr_cplt E F : Pr (P`2) F != 0 -> \Pr_[ ~: E | F] = 1 - \Pr_[E | F].
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
Let P' := fdistX P.
Hypothesis dis : forall i j, i != j -> [disjoint F i & F j].
Hypothesis cov : cover (F @: I) = [set: B].

Lemma jtotal_prob_cond : Pr P`1 E = \sum_(i in I) \Pr_[E | F i] * Pr P`2 (F i).
Proof.
rewrite -Pr_XsetT -EsetT.
rewrite (@total_prob_cond _ _ _ _ (fun i => T`* F i)); last 2 first.
  - move=> i j ij; rewrite -setI_eq0 !setTE setIX setTI.
    by move: (dis ij); rewrite -setI_eq0 => /eqP ->; rewrite setX0.
  - (* TODO: lemma? *) apply/setP => -[a b]; rewrite inE /cover.
    apply/bigcupP => /=.
    move: cov; rewrite /cover => /setP /(_ b).
    rewrite !inE => /bigcupP[b'].
    move/imsetP => [i _ ->{b'} bFi].
    exists (T`* F i).
      by apply/imsetP; exists i.
    by rewrite inE.
by apply eq_bigr => i _; rewrite -Pr_setTX -setTE; congr (_ * _); rewrite jcPrE.
Qed.

End total_probability.

End conditional_probability.
Notation "\Pr_ P [ E | F ]" := (jcPr P E F) : proba_scope.

Section jPr_Pr.
Variables (U : finType) (P : {fdist U}) (A B : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (E : {set A}) (F : {set B}).

Lemma jPr_Pr : \Pr_(`p_[% X, Y]) [E | F] = `Pr[X \in E |Y \in F].
Proof.
rewrite /jcPr Pr_fdistmap_RV2/= cpr_eq_setE /cPr; congr (_ / _).
rewrite Pr_fdist_snd setTE Pr_fdistmap_RV2/=.
rewrite (_ : [set x | X x \in [set: A]] = setT) ?setTI//.
by apply/setP => x; rewrite !inE.
Qed.

End jPr_Pr.

Section bayes.
Variables (A B : finType) (PQ : {fdist A * B}).
Let P := PQ`1. Let Q := PQ`2. Let QP := fdistX PQ.
Implicit Types (E : {set A}) (F : {set B}).

Lemma jBayes E F : \Pr_PQ[E | F] = \Pr_QP [F | E] * Pr P E / Pr Q F.
Proof.
rewrite 2!jcPrE Bayes /Rdiv -2!mulRA.
rewrite EsetT Pr_XsetT setTE Pr_setTX /cPr; congr ((_ / _) * (_ / _)).
  by rewrite EsetT setTE [in RHS]setIX Pr_fdistX setIX.
by rewrite setTE Pr_fdistX.
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
rewrite {1}/QP fdistX1 => ->.
by apply eq_bigr => j _; rewrite -/QP {2}/QP fdistX2.
Qed.

End bayes.

Section conditional_probability_prop3.
Variables (A B C : finType) (P : {fdist A * B * C}).

Lemma jcPr_TripC12 (E : {set A}) (F : {set B }) (G : {set C}) :
  \Pr_(fdistC12 P)[F `* E | G] = \Pr_P[E `* F | G].
Proof. by rewrite /jcPr Pr_fdistC12 fdistC12_snd. Qed.

Lemma jcPr_fdistA_AC (E : {set A}) (F : {set B}) (G : {set C}) :
  \Pr_(fdistA (fdistAC P))[E | G `* F] = \Pr_(fdistA P)[E | F `* G].
Proof.
rewrite /jcPr 2!Pr_fdistA Pr_fdistAC; congr (_ / _).
by rewrite fdistA_AC_snd -Pr_fdistX fdistXI.
Qed.

Lemma jcPr_fdistA_C12 (E : {set A}) (F : {set B}) (G : {set C}) :
  \Pr_(fdistA (fdistC12 P))[F | E `* G] = \Pr_(fdistA (fdistX (fdistA P)))[F | G `* E].
Proof.
rewrite /jcPr; congr (_ / _).
  by rewrite Pr_fdistA Pr_fdistC12 Pr_fdistA -[in RHS]Pr_fdistX fdistXI Pr_fdistA.
rewrite -/(fdist_proj13 _) -(fdistXI (fdist_proj13 P)) -Pr_fdistX fdistXI; congr Pr.
(* TODO: lemma? *)
by rewrite /fdist_proj13 /fdistX /fdist_snd /fdistA !fdistmap_comp.
Qed.

End conditional_probability_prop3.

Section product_rule.

Section main.
Variables (A B C : finType) (P : {fdist A * B * C}).
Implicit Types (E : {set A}) (F : {set B}) (G : {set C}).

Lemma jproduct_rule_cond E F G :
  \Pr_P [E `* F | G] = \Pr_(fdistA P) [E | F `* G] * \Pr_(fdist_proj23 P) [F | G].
Proof.
rewrite /jcPr; rewrite !mulRA; congr (_ * _); last by rewrite fdist_proj23_snd.
rewrite -mulRA -/(fdist_proj23 _) -Pr_fdistA.
case/boolP : (Pr (fdist_proj23 P) (F `* G) == 0) => H; last by rewrite mulVR ?mulR1.
suff -> : Pr (fdistA P) (E `* (F `* G)) = 0 by rewrite mul0R.
by rewrite Pr_fdistA; exact/Pr_fdist_proj23_domin/eqP.
Qed.

End main.

Section variant.
Variables (A B C : finType) (P : {fdist A * B * C}).
Implicit Types (E : {set A}) (F : {set B}) (G : {set C}).

Lemma product_ruleC E F G :
  \Pr_P [ E `* F | G] = \Pr_(fdistA (fdistC12 P)) [F | E `* G] * \Pr_(fdist_proj13 P) [E | G].
Proof. by rewrite -jcPr_TripC12 jproduct_rule_cond. Qed.

End variant.

Section prod.
Variables (A B : finType) (P : {fdist A * B}).
Implicit Types (E : {set A}) (F : {set B}).

Lemma jproduct_rule E F : Pr P (E `* F) = \Pr_P[E | F] * Pr (P`2) F.
Proof.
have [/eqP PF0|PF0] := boolP (Pr (P`2) F == 0).
  rewrite jcPrE /cPr -{1}(setIT E) -{1}(setIT F) -setIX.
  rewrite Pr_domin_setI; last by rewrite -Pr_fdistX Pr_domin_setX // fdistX1.
  by rewrite setIC Pr_domin_setI ?(div0R,mul0R) // setTE Pr_setTX.
rewrite -{1}(setIT E) -{1}(setIT F) -setIX product_rule.
rewrite -EsetT setTT cPrET Pr_setT mulR1 jcPrE.
rewrite /cPr {1}setTE {1}EsetT.
by rewrite setIX setTI setIT setTE Pr_setTX -mulRA mulVR ?mulR1.
Qed.

End prod.

End product_rule.

Lemma jcPr_fdistmap_r (A B B' : finType) (f : B -> B') (d : {fdist A * B})
    (E : {set A}) (F : {set B}): injective f ->
  \Pr_d [E | F] = \Pr_(fdistmap (fun x => (x.1, f x.2)) d) [E | f @: F].
Proof.
move=> injf; rewrite /jcPr; congr (_ / _).
- rewrite (@Pr_fdistmap _ _ (fun x => (x.1, f x.2))) /=; last first.
    by move=> [? ?] [? ?] /= [-> /injf ->].
  congr (Pr _ _); apply/setP => -[a b]; rewrite !inE /=.
  apply/imsetP/andP.
  - case=> -[a' b']; rewrite inE /= => /andP[a'E b'F] [->{a} ->{b}]; split => //.
    apply/imsetP; by exists b'.
  - case=> aE /imsetP[b' b'F] ->{b}; by exists (a, b') => //; rewrite inE /= aE.
by rewrite /fdist_snd fdistmap_comp (@Pr_fdistmap _ _ f) // fdistmap_comp.
Qed.
Arguments jcPr_fdistmap_r [A] [B] [B'] [f] [d] [E] [F] _.

Lemma jcPr_fdistmap_l (A A' B : finType) (f : A -> A') (d : {fdist A * B})
    (E : {set A}) (F : {set B}): injective f ->
  \Pr_d [E | F] = \Pr_(fdistmap (fun x => (f x.1, x.2)) d) [f @: E | F].
Proof.
move=> injf; rewrite /jcPr; congr (_ / _).
- rewrite (@Pr_fdistmap _ _ (fun x => (f x.1, x.2))) /=; last first.
    by move=> [? ?] [? ?] /= [/injf -> ->].
  congr (Pr _ _); apply/setP => -[a b]; rewrite !inE /=.
  apply/imsetP/andP.
  - case=> -[a' b']; rewrite inE /= => /andP[a'E b'F] [->{a} ->{b}]; split => //.
    apply/imsetP; by exists a'.
  - by case=> /imsetP[a' a'E] ->{a} bF; exists (a', b) => //; rewrite inE /= a'E.
by rewrite /fdist_snd !fdistmap_comp.
Qed.
Arguments jcPr_fdistmap_l [A] [A'] [B] [f] [d] [E] [F] _.

Lemma Pr_jcPr_unit (A : finType) (E : {set A}) (P : {fdist A}) :
  Pr P E = \Pr_(fdistmap (fun a => (a, tt)) P) [E | setT].
Proof.
rewrite /jcPr (Pr_set1 _ tt).
rewrite (_ : _`2 = fdist1 tt) ?fdist1xx ?divR1; last first.
  rewrite /fdist_snd fdistmap_comp; apply/fdist_ext; case.
  by rewrite fdistmapE fdist1xx (eq_bigl xpredT) // FDist.f1.
rewrite /Pr big_setX /=; apply eq_bigr => a _; rewrite (big_set1 _ tt) /=.
rewrite fdistmapE (big_pred1 a) // => a0; rewrite inE /=.
by apply/eqP/eqP => [[] -> | ->].
Qed.

Section jfdist_cond0.
Variables (A B : finType) (PQ : {fdist (A * B)}) (a : A).
Hypothesis Ha : PQ`1 a != 0.

Let f := [ffun b => \Pr_(fdistX PQ) [[set b] | [set a]]].

Let f0 b : 0 <= f b. Proof. rewrite ffunE; exact: jcPr_ge0. Qed.

Let f0' b : (0 <= f b)%O. Proof. by apply/RleP. Qed.

Let f1 : \sum_(b in B) f b = 1.
Proof.
under eq_bigr do rewrite ffunE.
by rewrite /jcPr -big_distrl /= PrX_snd mulRV // Pr_set1 fdistX2.
Qed.

Definition jfdist_cond0 : {fdist B} := locked (@FDist.make _ _ _ f0' f1).

Lemma jfdist_cond0E b : jfdist_cond0 b = \Pr_(fdistX PQ) [[set b] | [set a]].
Proof. by rewrite /jfdist_cond0; unlock; rewrite ffunE. Qed.

End jfdist_cond0.
Arguments jfdist_cond0 {A} {B} _ _ _.

Section jfdist_cond.
Variables (A B : finType) (PQ : {fdist A * B}) (a : A).
Let Ha := PQ`1 a != 0.

Let sizeB : #|B| = #|B|.-1.+1.
Proof.
case HB: #|B| => //.
by move: (fdist_card_neq0 PQ); rewrite card_prod HB muln0 ltnn.
Qed.

Definition jfdist_cond :=
  match boolP Ha with
  | AltTrue H => jfdist_cond0 PQ _ H
  | AltFalse _ => fdist_uniform sizeB
  end.

Lemma jfdist_condE (H : Ha) b : jfdist_cond b = \Pr_(fdistX PQ) [[set b] | [set a]].
Proof.
by rewrite /jfdist_cond; destruct boolP; [rewrite jfdist_cond0E|rewrite H in i].
Qed.

Lemma jfdist_cond_dflt (H : ~~ Ha) : jfdist_cond = fdist_uniform sizeB.
Proof.
by rewrite /jfdist_cond; destruct boolP => //; rewrite i in H.
Qed.

End jfdist_cond.
Notation "P `(| a ')'" := (jfdist_cond P a).

Lemma cPr_1 (U : finType) (P : fdist U) (A B : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) a : `Pr[X = a] != 0 ->
  \sum_(b <- fin_img Y) `Pr[ Y = b | X = a ] = 1.
Proof.
rewrite -pr_eq_set1 pr_inE' Pr_set1 -{1}(fst_RV2 _ Y) => Xa0.
set Q := `p_[% X, Y] `(| a ).
rewrite -(FDist.f1 Q) [in RHS](bigID (mem (fin_img Y))) /=.
rewrite [X in _ = _ + X](eq_bigr (fun=> 0)); last first.
  move=> b bY.
  rewrite /Q jfdist_condE // /jcPr /Pr !(big_setX,big_set1) /= fdistXE fdistX2 fst_RV2.
  rewrite -!pr_eqE' !pr_eqE.
  rewrite /Pr big1 ?div0R // => u.
  rewrite inE => /eqP[Yub ?].
  exfalso.
  move/negP : bY; apply.
  by rewrite mem_undup; apply/mapP; exists u => //; rewrite mem_enum.
rewrite big_const iter_addR mulR0 addR0.
rewrite big_uniq; last by rewrite /fin_img undup_uniq.
apply eq_bigr => b; rewrite mem_undup => /mapP[u _ bWu].
rewrite /Q jfdist_condE // fdistX_RV2.
by rewrite jcPrE -cpr_inE' cpr_eq_set1.
Qed.

Lemma jcPr_1 (A B : finType) (P : {fdist A * B}) a : P`1 a != 0 ->
  \sum_(b in B) \Pr_(fdistX P)[ [set b] | [set a] ] = 1.
Proof.
move=> Xa0; rewrite -(FDist.f1 (P `(| a ))); apply eq_bigr => b _.
by rewrite jfdist_condE.
Qed.

Lemma jfdist_cond_prod (A B : finType) (P : fdist A) (W : A -> fdist B) (a : A) :
  (P `X W)`1 a != 0 -> W a = (P `X W) `(| a ).
Proof.
move=> a0; apply/fdist_ext => b.
rewrite jfdist_condE // /jcPr setX1 !Pr_set1 fdistXE fdistX2 fdist_prod1.
rewrite fdist_prodE /= /Rdiv mulRAC mulRV ?mul1R //.
by move: a0; rewrite fdist_prod1.
Qed.

Lemma jcPr_fdistX_prod (A B : finType) (P : fdist A) (W : A -> fdist B) a b :
  P a <> 0 -> \Pr_(fdistX (P `X W))[ [set b] | [set a] ] = W a b.
Proof.
move=> Pxa.
rewrite /jcPr setX1 fdistX2 2!Pr_set1 fdistXE fdist_prod1.
by rewrite fdist_prodE /= /Rdiv mulRAC mulRV ?mul1R //; exact/eqP.
Qed.

Section fdist_split.
Variables (A B : finType).

Definition fdist_split (PQ : {fdist A * B}) := (PQ`1, fun x => PQ `(| x )).

Lemma fdist_prodK : cancel fdist_split (uncurry (@fdist_prod A B)).
Proof.
move=> PQ; apply/fdist_ext => ab; rewrite fdist_prodE.
have [Ha|Ha] := eqVneq (PQ`1 ab.1) 0.
  rewrite Ha mul0R; apply/esym/(dominatesE (Prod_dominates_Joint PQ)).
  by rewrite fdist_prodE Ha mul0R.
rewrite jfdist_condE // -fdistX2 mulRC.
rewrite -(Pr_set1 _ ab.1) -jproduct_rule setX1 Pr_set1 fdistXE.
by case ab.
Qed.

End fdist_split.
