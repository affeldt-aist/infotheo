(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import Reals Lra.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.

(* tentative definition of conditional probability
OUTLINE:
- Various distributions (Swap.d, Self.d, TripA.d, TripA'.d, TripC12.d, TripC23.d,
  TripC13.d, Proj13.d, Proj23.d)
- Section conditional_probability_def.
- Module CondDist.
- Module CondDistT.
- Module CDist.
- Section conditional_probability_prop.
- Section total_probability.
- Section bayes.
- Section conditional_probability_prop3.
- Section product_rule.
- Section conditional_expectation_def.
- Section conditional_expectation_prop.
*)

Reserved Notation "\Pr_ P [ A | B ]" (at level 6, P, A, B at next level,
  format "\Pr_ P [ A  |  B ]").
Reserved Notation "\Pr_[ A | B ]" (at level 6, A, B at next level,
  format "\Pr_[ A  |  B ]").

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.
Local Open Scope proba_scope.

Lemma inj_swap A B : injective (@swap A B).
Proof. by move=> [? ?] [? ?] [-> ->]. Qed.

Lemma bij_swap A B : bijective (@swap A B).
Proof. apply Bijective with swap; by case. Qed.

Lemma ide_swap A B : (@swap A B) \o swap = @id (B * A).
Proof. by apply/FunctionalExtensionality.functional_extensionality => -[]. Qed.

Module Swap.
Section def.
Variables (A B : finType) (P : {dist A * B}).
Definition d : {dist B * A} := DistMap.d swap P.
Lemma dE a b : d (b, a) = P (a, b).
Proof.
rewrite DistMap.dE /= (_ : (b, a) = swap (a ,b)) //.
by rewrite (big_pred1_inj _ _ _ (@inj_swap _ _)).
Qed.
End def.
Section prop.
Variables (A B : finType) (P : {dist A * B}).
Lemma fst : Bivar.fst (d P) = Bivar.snd P.
Proof. by rewrite /Bivar.fst /d DistMap.comp. Qed.
Lemma snd : Bivar.snd (d P) = Bivar.fst P.
Proof. by rewrite /Bivar.snd /d DistMap.comp. Qed.
Lemma dI : d (d P) = P.
Proof. by rewrite /d DistMap.comp ide_swap DistMap.id. Qed.
Lemma Pr (E : {set A}) (F : {set B}) :
  Pr P (setX E F) = Pr (Swap.d P) (setX F E).
Proof.
rewrite /Pr !big_setX exchange_big /=; apply eq_bigr => b _.
apply eq_bigr => a _; by rewrite Swap.dE.
Qed.
End prop.
Section prop2.
Variables (A B : finType) (P : dist A) (Q : dist B).
Lemma ProdDist : Swap.d (Q `x P) = P `x Q.
Proof. apply/dist_ext => -[a b]; by rewrite dE !ProdDist.dE mulRC. Qed.
End prop2.
Section prop3.
Variables (A B : finType) (P : {dist A * B}) (Q : {dist A * B}).
Local Open Scope reals_ext_scope.
Lemma dom_by : dominates P Q -> dominates (Swap.d P) (Swap.d Q).
Proof.
by move/dominatesP => H; apply/dominatesP => -[b a]; rewrite !dE => /H.
Qed.
End prop3.
End Swap.

Module Self.
Section def.
Variable (A : finType) (P : {dist A}).
Definition f := [ffun a : A * A => if a.1 == a.2 then P a.1 else 0].
Lemma f0 x : 0 <= f x.
Proof.
rewrite /f ffunE; case: ifPn => [/eqP ->| _]; [exact: dist_ge0|exact: leRR].
Qed.
Lemma f1 : \rsum_(x in {: A * A}) f x = 1.
Proof.
rewrite (eq_bigr (fun a => f (a.1, a.2))); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => f (a1, a2))) /=.
rewrite -(epmf1 P); apply/eq_bigr => a _.
rewrite /f; evar (h : A -> R); rewrite (eq_bigr h); last first.
  move=> b _; rewrite ffunE /h; reflexivity.
rewrite {}/h /= (bigD1 a) //= eqxx.
rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 ?addR0 //.
by move=> a' /negbTE; rewrite eq_sym => ->.
Qed.
Definition d : {dist A * A} := locked (makeDist f0 f1).
Lemma dE a : d a = if a.1 == a.2 then P a.1 else 0.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
End def.
Section prop.
Variables (A : finType) (P : {dist A}).
Lemma fst : Bivar.fst (d P) = P.
Proof.
apply/dist_ext => a /=; rewrite Bivar.fstE (bigD1 a) //= dE eqxx /=.
rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 ?addR0 //.
by move=> a' /negbTE; rewrite dE /= eq_sym => ->.
Qed.
Lemma swap : Swap.d (d P) = d P.
Proof.
apply/dist_ext => -[a1 a2].
by rewrite Swap.dE !dE /= eq_sym; case: ifPn => // /eqP ->.
Qed.
End prop.
End Self.

Module TripA.
Section def.
Variables (A B C : finType) (P : {dist A * B * C}).
Let f (x : A * B * C) := (x.1.1, (x.1.2, x.2)).
Lemma inj_f : injective f.
Proof. by rewrite /f => -[[? ?] ?] [[? ?] ?] /= [-> -> ->]. Qed.
Definition d : {dist A * (B * C)} := DistMap.d f P.
Lemma dE x : d x = P (x.1, x.2.1, x.2.2).
Proof.
case: x => a [b c]; rewrite /d DistMap.dE /= -/(f (a, b, c)) big_pred1_inj //.
exact/inj_f.
Qed.

Lemma domin a b c : d (a, (b, c)) = 0 -> P (a, b, c) = 0.
Proof. by rewrite dE. Qed.

Lemma dominN a b c : P (a, b, c) != 0 -> d (a, (b, c)) != 0.
Proof. by apply: contra => /eqP H; apply/eqP; apply: domin H. Qed.
End def.
Section prop.
Variables (A B C : finType) (P : {dist A * B * C}).
Implicit Types (E : {set A}) (F : {set B}) (G : {set C}).

Lemma fst : Bivar.fst (d P) = Bivar.fst (Bivar.fst P).
Proof. by rewrite /Bivar.fst /d 2!DistMap.comp. Qed.

Lemma fst_snd : Bivar.fst (Bivar.snd (d P)) = Bivar.snd (Bivar.fst P).
Proof. by rewrite /d /Bivar.snd /Bivar.fst /= !DistMap.comp. Qed.

Lemma snd_snd : Bivar.snd (Bivar.snd (d P)) = Bivar.snd P.
Proof. by rewrite /d /Bivar.snd !DistMap.comp. Qed.

Lemma snd_swap : Bivar.snd (Swap.d (d P)) = Bivar.fst (Bivar.fst P).
Proof. by rewrite /d /Bivar.snd /Swap.d /Bivar.fst /= 3!DistMap.comp. Qed.

Lemma snd_fst_swap : Bivar.snd (Bivar.fst (Swap.d (d P))) = Bivar.snd P.
Proof. by rewrite /Bivar.snd /Bivar.fst /Swap.d !DistMap.comp. Qed.

Lemma Pr E F G : Pr (TripA.d P) (setX E (setX F G)) = Pr P (setX (setX E F) G).
Proof.
rewrite /Pr !big_setX /=; apply eq_bigr => a aE; rewrite big_setX /=.
by apply eq_bigr => b bF; apply eq_bigr => c cG; rewrite TripA.dE.
Qed.

End prop.
End TripA.

Module TripA'.
Section def.
Variables (A B C : finType) (P : {dist A * (B * C)}).
Definition f (x : A * (B * C)) := ((x.1, x.2.1), x.2.2).
Lemma inj_f : injective f.
Proof. by rewrite /f => -[? [? ?]] [? [? ?]] /= [-> -> ->]. Qed.
Definition d : {dist A * B * C} := DistMap.d f P.
Lemma dE x : d x = P (x.1.1, (x.1.2, x.2)).
Proof.
case: x => -[a b] c; rewrite /d DistMap.dE /= -/(f (a, (b, c))).
by rewrite (big_pred1_inj _ _ _ inj_f).
Qed.
End def.
End TripA'.

Module TripC12.
Section def.
Variables (A B C : finType) (P : {dist A * B * C}).
Let f (x : A * B * C) := (x.1.2, x.1.1, x.2).
Lemma inj_f : injective f.
Proof. by rewrite /f => -[[? ?] ?] [[? ?] ?] /= [-> -> ->]. Qed.
Definition d : {dist B * A * C} := DistMap.d f P.
Lemma dE x : d x = P (x.1.2, x.1.1, x.2).
Proof.
case: x => -[b a] c; rewrite /d DistMap.dE /= -/(f (a, b, c)).
by rewrite (big_pred1_inj _ _ _ inj_f).
Qed.

Lemma snd : Bivar.snd d = Bivar.snd P.
Proof. by rewrite /Bivar.snd /d DistMap.comp. Qed.

Lemma fst : Bivar.fst d = Swap.d (Bivar.fst P).
Proof. by rewrite /Bivar.fst /d /Swap.d 2!DistMap.comp. Qed.

Lemma fstA : Bivar.fst (TripA.d d) = Bivar.snd (Bivar.fst P).
Proof. by rewrite /Bivar.fst /TripA.d /Bivar.snd !DistMap.comp. Qed.
End def.
Section prop.
Variables (A B C : finType) (P : {dist A * B * C}).
Lemma dI : d (d P) = P.
Proof.
rewrite /d DistMap.comp (_ : _ \o _ = ssrfun.id) ?DistMap.id //.
by apply FunctionalExtensionality.functional_extensionality => -[[]].
Qed.
Lemma Pr E F G : Pr (d P) (setX (setX E F) G) = Pr P (setX (setX F E) G).
Proof.
rewrite /Pr !big_setX /= exchange_big; apply eq_bigr => a aF.
by apply eq_bigr => b bE; apply eq_bigr => c cG; rewrite dE.
Qed.
End prop.
End TripC12.

Module TripC23.
Section def.
Variables (A B C : finType) (P : {dist A * B * C}).
Definition d : {dist A * C * B} := Swap.d (TripA.d (TripC12.d P)).
Lemma dE x : d x = P (x.1.1, x.2, x.1.2).
Proof. by case: x => x1 x2; rewrite /d Swap.dE TripA.dE TripC12.dE. Qed.
End def.
Section prop.
Variables (A B C : finType) (P : {dist A * B * C}).
Implicit Types (E : {set A}) (F : {set B}) (G : {set C}).

Lemma snd : Bivar.snd (d P) = Bivar.snd (Bivar.fst P).
Proof. by rewrite /d Swap.snd TripC12.fstA. Qed.

Lemma fstA : Bivar.fst (TripA.d (d P)) = Bivar.fst (TripA.d P).
Proof. by rewrite /Bivar.fst !DistMap.comp. Qed.

Lemma fst_fst : Bivar.fst (Bivar.fst (d P)) = Bivar.fst (Bivar.fst P).
Proof. by rewrite /Bivar.fst !DistMap.comp. Qed.

Lemma sndA : Bivar.snd (TripA.d (d P)) = Swap.d (Bivar.snd (TripA.d P)).
Proof. by rewrite /Bivar.snd /Swap.d !DistMap.comp. Qed.

Lemma Pr E F G : Pr (TripC23.d P) (setX (setX E G) F) = Pr P (setX (setX E F) G).
Proof.
rewrite /Pr !big_setX /=; apply eq_bigr => a aE.
rewrite exchange_big /=; apply eq_bigr => c cF.
by apply eq_bigr => b bG; rewrite TripC23.dE.
Qed.
End prop.
End TripC23.

Module TripC13.
Section def.
Variables (A B C : finType) (P : {dist A * B * C}).
Definition d : {dist C * B * A} := TripC12.d (Swap.d (TripA.d P)).
Lemma dE x : d x = P (x.2, x.1.2, x.1.1).
Proof. by rewrite /d TripC12.dE Swap.dE TripA.dE. Qed.

Lemma fst : Bivar.fst d = Swap.d (Bivar.snd (TripA.d P)).
Proof. by rewrite /d /Bivar.fst /Swap.d !DistMap.comp. Qed.

Lemma snd : Bivar.snd d = Bivar.fst (Bivar.fst P).
Proof. by rewrite /d TripC12.snd TripA.snd_swap. Qed.

Lemma fst_fst : Bivar.fst (Bivar.fst d) = Bivar.snd P.
Proof. by rewrite /Bivar.fst /Bivar.snd !DistMap.comp. Qed.

Lemma sndA : Bivar.snd (TripA.d d) = Swap.d (Bivar.fst P).
Proof. by rewrite /Bivar.snd /Swap.d !DistMap.comp. Qed.
End def.
End TripC13.

Module Proj13.
Section def.
Variables (A B C : finType) (P : {dist A * B * C}).
Definition d : {dist A * C} := Bivar.snd (TripA.d (TripC12.d P)).
Lemma dE x : d x = \rsum_(b in B) P (x.1, b, x.2).
Proof.
rewrite /d Bivar.sndE; apply eq_bigr => b _; by rewrite TripA.dE TripC12.dE.
Qed.

Lemma domin a b c : d (a, c) = 0 -> P (a, b, c) = 0.
Proof. rewrite dE /= => /prsumr_eq0P -> // b' _; exact: dist_ge0. Qed.

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
Variables (A B C : finType) (P : {dist A * B * C}).
Definition d : {dist B * C} := Bivar.snd (TripA.d P).
Lemma dE x : d x = \rsum_(a in A) P (a, x.1, x.2).
Proof. by rewrite /d Bivar.sndE; apply eq_bigr => a _; rewrite TripA.dE. Qed.

Lemma domin a b c : d (b, c) = 0 -> P (a, b, c) = 0.
Proof. rewrite dE /= => /prsumr_eq0P -> // a' _; exact: dist_ge0. Qed.

Lemma dominN a b c : P (a, b, c) != 0 -> d (b, c) != 0.
Proof. by apply: contra => /eqP H; apply/eqP; apply: domin. Qed.

Lemma fst : Bivar.fst d = Bivar.snd (Bivar.fst P).
Proof. by rewrite /d TripA.fst_snd. Qed.
Lemma snd : Bivar.snd d = Bivar.snd P.
Proof. by rewrite /d TripA.snd_snd. Qed.
End def.
Section prop.
Variables (A B C : finType) (P : {dist A * B * C}).
Implicit Types (E : {set A}) (F : {set B}) (G : {set C}).
Lemma Pr_domin E F G :
  Pr (d P) (setX F G) = 0 -> Pr P (setX (setX E F) G) = 0.
Proof.
move/Pr_set0P => H; apply/Pr_set0P => -[[? ?] ?].
rewrite !inE /= -andbA => /and3P[aE bF cG].
by apply/domin/H; rewrite inE /= bF cG.
Qed.
End prop.
End Proj23.

Section Proj_prop.
Variables (A B C : finType) (P : {dist A * B * C}).
Lemma Proj13_TripC23 : Proj13.d (TripC23.d P) = Bivar.fst P.
Proof.
rewrite /Proj13.d /Bivar.snd /TripA.d /TripC12.d /TripC23.d /Bivar.fst.
rewrite !DistMap.comp /=; congr (DistMap.d _ _).
by apply FunctionalExtensionality.functional_extensionality => -[[]].
Qed.
End Proj_prop.

(* TODO: move to proba.v? *)
Section Pr_extra.

Variables (A B : finType) (P : {dist A * B}).
Implicit Types (E : {set A}) (F : {set B}).

Lemma PrX_setT E : Pr P (setX E [set: B]) = Pr (Bivar.fst P) E.
Proof.
rewrite /Pr big_setX /=; apply eq_bigr => a aE.
by rewrite Bivar.fstE /=; apply eq_bigl => b; rewrite inE.
Qed.

Lemma PrX_snd F : \rsum_(a in A) Pr P (setX [set a] F) = Pr (Bivar.snd P) F.
Proof.
rewrite /Pr (eq_bigr (fun i =>
    \rsum_(a in [set i]) \rsum_(j in F) P (a, j))); last first.
  by move=> a _; rewrite big_setX.
rewrite pair_big_dep /= exchange_big /=; apply eq_bigr => b _.
rewrite Bivar.sndE (reindex_onto (fun x => (x, x)) fst); last first.
  by case => /= a b0; rewrite in_set1 => /eqP ->.
by rewrite /= (eq_bigl predT) // => a; rewrite !inE !eqxx.
Qed.

Lemma PrX_fst E : \rsum_(b in B) Pr P (setX E [set b]) = Pr (Bivar.fst P) E.
Proof.
rewrite /Pr (eq_bigr (fun i =>
    \rsum_(b in [set i]) \rsum_(i in E) P (i, b))); last first.
  by move=> b _; rewrite big_setX /= exchange_big.
rewrite pair_big_dep /= exchange_big /=; apply eq_bigr => a _.
rewrite Bivar.fstE (reindex_onto (fun x => (x, x)) snd); last first.
  by case => /= a1 b; rewrite in_set1 => /eqP ->.
by rewrite /= (eq_bigl predT) // => b; rewrite !inE !eqxx.
Qed.

Lemma PrX_diff E1 E2 F :
  Pr P (setX (E1 :\: E2) F) = Pr P (setX E1 F) - Pr P (setX (E1 :&: E2) F).
Proof.
rewrite /Pr !big_setX /= exchange_big [in X in _ = X - _]exchange_big /=.
rewrite [in X in _ = _ - X]exchange_big -addR_opp big_morph_oppR.
rewrite -big_split /=; apply eq_bigr => a aE.
by rewrite [in X in _ = X + _](big_setID E2) /= -addRA addRCA addR_opp subRR addR0.
Qed.

Lemma PrX_union E1 E2 F :
  Pr P (setX (E1 :|: E2) F) = Pr P (setX E2 F) + Pr P (setX (E1 :\: E2) F).
Proof.
rewrite /Pr !big_setX /= exchange_big /= [in X in _ = X + _]exchange_big /=.
rewrite [in X in _ = _ + X]exchange_big /= -big_split /=; apply eq_bigr => b bF.
apply/esym.
rewrite big_mkcond [in X in _ + X]big_mkcond -big_split /= [in RHS]big_mkcond.
apply eq_bigr => a _.
case: ifPn => aF2; first by rewrite in_setD aF2 /= in_setU aF2 orbT addR0.
by rewrite in_setD aF2 /= in_setU (negbTE aF2) orbF; case: ifPn; rewrite add0R.
Qed.

End Pr_extra.

Section conditional_probability_def.

Variables (A B : finType) (P : {dist A * B}).
Implicit Types (E : {set A}) (F : {set B}).

(* Pr(a | b) *)
Definition cPr E F := Pr P (setX E F) / Pr (Bivar.snd P) F.

Local Notation "\Pr_[ E | F ]" := (cPr E F).

Lemma cPr_setT E : \Pr_[E | setT] = Pr (Bivar.fst P) E.
Proof. by rewrite /cPr Pr_setT divR1 PrX_setT. Qed.

Lemma cPr_set0 E : \Pr_[E | set0] = 0.
Proof. by rewrite /cPr Pr_domin_snd ?div0R // Pr_set0. Qed.

Lemma cPr_ge0 E F : 0 <= \Pr_[E | F].
Proof.
rewrite /cPr; case/boolP : (Pr (Bivar.snd P) F == 0) => [/eqP|] H0.
  suff -> : Pr P (setX E F) = 0 by rewrite div0R; exact: leRR.
  by rewrite Pr_domin_snd.
apply divR_ge0; [exact: Pr_ge0 | by rewrite Pr_gt0].
Qed.

Lemma cPr_max E F : \Pr_[E | F] <= 1.
Proof.
rewrite /cPr; case/boolP : (Pr (Bivar.snd P) F == 0) => [/eqP|] H0.
  by rewrite Pr_domin_snd // div0R.
rewrite leR_pdivr_mulr ?Pr_gt0 // mul1R /Pr big_setX /= exchange_big /=.
apply ler_rsum => b _.
rewrite Bivar.sndE; apply ler_rsum_l => // a _; [exact: leRR | exact: dist_ge0].
Qed.

Lemma Pr_cPr E F : Pr P (setX E F) = \Pr_[E | F] * Pr (Bivar.snd P) F.
Proof.
case/boolP : (Pr (Bivar.snd P) F == 0) => [/eqP H0|H0].
- by rewrite H0 mulR0 Pr_domin_snd.
- by rewrite /cPr -mulRA mulVR // mulR1.
Qed.

Lemma cPr_gt0 E F : 0 < \Pr_[E | F] <-> \Pr_[E | F] != 0.
Proof.
split; rewrite /cPr; first by rewrite ltR_neqAle => -[/eqP H1 _]; rewrite eq_sym.
rewrite ltR_neqAle eq_sym => /eqP H; split => //; exact: cPr_ge0.
Qed.

Lemma cPr_Pr_setX_gt0 E F : 0 < Pr P (setX E F) <-> 0 < \Pr_[E | F].
Proof.
rewrite Pr_gt0; split => H; last first.
  move/cPr_gt0 : H; apply: contra => /eqP; rewrite /cPr => ->; by rewrite div0R.
rewrite /cPr; apply/divR_gt0; rewrite Pr_gt0 //; exact: Pr_domin_sndN H.
Qed.

End conditional_probability_def.

Notation "\Pr_ P [ E | F ]" := (cPr P E F) : proba_scope.

Module CondDist.
Section def.
Variables (A B : finType) (PQ : {dist A * B}) (a : A).
Hypothesis Ha : Bivar.fst PQ a != 0.
Definition f := [ffun b => \Pr_(Swap.d PQ) [[set b] | [set a]]].
Lemma f0 b : 0 <= f b. Proof. rewrite ffunE; exact: cPr_ge0. Qed.
Lemma f1 : \rsum_(b in B) f b = 1.
Proof.
rewrite /f; evar (h : B -> R); rewrite (eq_bigr h); last first.
  move=> b _; rewrite ffunE /h; reflexivity.
by rewrite {}/h /cPr -big_distrl /= PrX_snd mulRV // Pr_set1 Swap.snd.
Qed.
Definition d : {dist B} := locked (makeDist f0 f1).
Lemma dE b : d b = \Pr_(Swap.d PQ) [[set b] | [set a]].
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
End def.
End CondDist.

Arguments CondDist.d {A} {B} _ _ _.

Module CondDistT.
Section def.
Variables (A B : finType) (PQ : {dist A * B}) (a : A).
Let Ha := Bivar.fst PQ a != 0.
Lemma sizeB : #|B| = #|B|.-1.+1.
Proof.
case HB: #|B| => //.
move: (dist_domain_not_empty PQ).
by rewrite card_prod HB muln0 ltnn.
Qed.
Definition d :=
  match boolP Ha with
  | AltTrue H => CondDist.d PQ a H
  | AltFalse _ => Uniform.d sizeB
  end.
Lemma dE (H : Ha) : d = CondDist.d PQ a H.
Proof.
rewrite /d; destruct boolP.
  by rewrite (eq_irrelevance i H).
by rewrite H in i.
Qed.
Lemma dNE (H : ~~Ha) : d = Uniform.d sizeB.
Proof.
rewrite /d; destruct boolP => //.
by rewrite i in H.
Qed.
End def.
End CondDistT.

Module CDist.
Section def.
Variables (A B : finType).
Record t := mkt {P : dist A ; W :> A -> dist B}.
Definition joint_of (x : t) : {dist A * B} := ProdDist.d (P x) (W x).
Definition make_joint (P : dist A) (W : A -> dist B) : {dist A * B} :=
  joint_of (mkt P W).
Lemma CondDistE (x : t) : forall a (a0 : Bivar.fst (joint_of x) a != 0),
  x a = CondDist.d (joint_of x) _ a0.
Proof.
move=> a a0; apply/dist_ext => b.
rewrite CondDist.dE /cPr setX1 !Pr_set1 /P Swap.dE Swap.snd ProdDist.fst.
rewrite ProdDist.dE /= /Rdiv mulRAC mulRV ?mul1R //.
by move: a0; rewrite ProdDist.fst.
Qed.
Lemma E (x : t) a b : (P x) a <> 0 ->
  x a b = \Pr_(Swap.d (joint_of x))[[set b]|[set a]].
Proof.
move=> Pxa.
rewrite /cPr setX1 Swap.snd 2!Pr_set1 /joint_of Swap.dE ProdDist.fst.
rewrite ProdDist.dE /= /Rdiv mulRAC mulRV ?mul1R //; exact/eqP.
Qed.
Definition split (PQ : {dist A * B}) :=
  mkt (Bivar.fst PQ) (CondDistT.d PQ).
Lemma splitK : cancel split joint_of.
Proof.
move=> PQ.
rewrite /joint_of /split /=.
apply/dist_ext => ab.
rewrite ProdDist.dE.
case /boolP: (Bivar.fst PQ ab.1 == 0) => Ha.
  rewrite (eqP Ha) mul0R.
  symmetry.
  apply (dominatesE (Prod_dominates_Joint PQ)).
  by rewrite ProdDist.dE (eqP Ha) mul0R.
rewrite CondDistT.dE CondDist.dE -Swap.snd mulRC.
rewrite -(Pr_set1 _ ab.1) -Pr_cPr setX1 Pr_set1 Swap.dE.
by destruct ab.
Qed.
End def.
End CDist.
Definition cdistw (A B : finType) (x : CDist.t A B) := CDist.W x.
Coercion cdistw : CDist.t >-> Funclass.

Section conditional_probability_prop.

Variables (A B : finType) (P : {dist A * B}).

Lemma cPr_1 a : Bivar.fst P a != 0 ->
  \rsum_(b in B) \Pr_(Swap.d P)[ [set b] | [set a] ] = 1.
Proof.
move=> Xa0; rewrite -(epmf1 (CondDist.d P _ Xa0)).
apply eq_bigr => b _; by rewrite CondDist.dE.
Qed.

Lemma cPr_cplt E F : Pr (Bivar.snd P) E != 0 ->
  \Pr_P[~: F | E] = 1 - \Pr_P[F | E].
Proof.
move=> H.
rewrite -subR_eq -addR_opp oppRK /cPr -mulRDl /Pr.
rewrite !big_setX /= exchange_big /= [in X in (_ + X) * / _]exchange_big /=.
rewrite -big_split /= (eq_bigr (fun i => \rsum_(i0 in A) P (i0, i))); last first.
  move=> a aE; apply/esym; rewrite (bigID (fun x => x \in F)) /= addRC; congr (_ + _).
  by apply eq_bigl => b; rewrite !inE.
by rewrite eqR_divr_mulr // mul1R; apply eq_bigr => a aE; rewrite Bivar.sndE.
Qed.

Lemma cPr_diff F1 F2 E : \Pr_P[F1 :\: F2 | E] = \Pr_P[F1 | E] - \Pr_P[F1 :&: F2 | E].
Proof. by rewrite /cPr -mulRBl PrX_diff. Qed.

Lemma cPr_union_eq F1 F2 E :
  \Pr_P[F1 :|: F2 | E] = \Pr_P[F1 | E] + \Pr_P[F2 | E] - \Pr_P[F1 :&: F2 | E].
Proof.
transitivity (\Pr_P[F2 | E] + \Pr_P[F1 :\: F2 | E]); last first.
  by rewrite cPr_diff addRA addR_opp addRC.
by rewrite /cPr -mulRDl PrX_union.
Qed.

End conditional_probability_prop.

Section total_probability.

Variables (A B : finType) (PQ : {dist A * B}).
Variables (n : nat) (E : 'I_n -> {set A}) (F : {set B}).
Let P := Bivar.fst PQ.  Let Q := Bivar.snd PQ. Let QP := Swap.d PQ.

Lemma total_prob : (forall i j, i != j -> [disjoint E i & E j]) ->
  cover [set E i | i in 'I_n] = [set: A] ->
  Pr Q F = \rsum_(i < n) Pr P (E i) * \Pr_QP [F | E i].
Proof.
move=> disE covE.
rewrite (eq_bigr (fun i => Pr QP (setX F (E i)))); last first.
  by move=> i _; rewrite Pr_cPr mulRC Swap.snd.
rewrite -Pr_big_union_disj; last first.
  move=> i j ij; rewrite -setI_eq0; apply/eqP/setP => -[b a]; rewrite inE.
  move: (disE _ _ ij); rewrite -setI_eq0 => /eqP/setP/(_ a).
  by rewrite !inE /= andbACA andbb => ->; rewrite andbF.
rewrite bigcup_setX Pr_cPr Swap.snd.
move: covE; rewrite cover_imset => ->.
by rewrite cPr_setT Pr_setT mulR1 Swap.fst.
Qed.

End total_probability.

Section bayes.
Variables (A B : finType) (PQ : {dist A * B}).
Let P := Bivar.fst PQ. Let Q := Bivar.snd PQ. Let QP := Swap.d PQ.
Implicit Types (E : {set A}) (F : {set B}).

Lemma bayes E F : \Pr_PQ[E | F] = \Pr_QP [F | E] * Pr P E / Pr Q F.
Proof.
rewrite /cPr -Swap.Pr Swap.snd -/Q -/P.
case/boolP : (Pr P E == 0) => [/eqP|] H0.
  by rewrite Pr_domin_fst // !(mul0R,div0R).
- rewrite /Rdiv -!mulRA; congr (_ * _).
  by rewrite mulRCA mulRA mulRV // mul1R.
Qed.

Lemma bayes_family n (E : 'I_n -> {set A}) (F : {set B}) :
  (forall i j, i != j -> [disjoint E i & E j]) ->
  cover [set E i | i in 'I_n] = [set: A] ->
  forall i,
  \Pr_PQ [E i | F] = (\Pr_QP [F | E i] * Pr P (E i)) /
                     \rsum_(j < n) \Pr_ QP [F | E j] * Pr P (E j).
Proof.
move=> H1 H2 i.
rewrite bayes (total_prob _ _ H1) //; congr (_ / _).
apply eq_bigr => j _; by rewrite mulRC.
Qed.

End bayes.

Section todo.
Variables (A B : finType) (PQ : {dist A * B}).
Let P := Bivar.fst PQ. Let Q := Bivar.snd PQ. Let QP := Swap.d PQ.
Implicit Types (E : {set A}) (F : {set B}).

Lemma Pr_cPr' E F : Pr PQ (setX E F) = Pr P E * \Pr_QP[F | E].
Proof.
case/boolP : (Pr (Bivar.fst PQ) E == 0) => [/eqP H0|H0].
- by rewrite H0 mul0R Pr_domin_fst.
- by rewrite /cPr -mulRCA Swap.snd mulRV // mulR1 [in RHS]Swap.Pr Swap.dI.
Qed.
End todo.

Section conditional_probability_prop3.
Variables (A B C : finType) (P : {dist A * B * C}).

Lemma cPr_TripC12 (E : {set A}) (F : {set B }) (G : {set C}) :
  \Pr_(TripC12.d P)[setX F E | G] = \Pr_P[setX E F | G].
Proof. by rewrite /cPr TripC12.Pr TripC12.snd. Qed.

Lemma cPr_TripA_TripC23 (E : {set A}) (F : {set B}) (G : {set C}) :
  \Pr_(TripA.d (TripC23.d P))[E | setX G F] = \Pr_(TripA.d P)[E | setX F G].
Proof.
rewrite /cPr 2!TripA.Pr TripC23.Pr; congr (_ / _).
by rewrite TripC23.sndA Swap.Pr Swap.dI.
Qed.

Lemma cPr_TripA_TripC12 (E : {set A}) (F : {set B}) (G : {set C}) :
  \Pr_(TripA.d (TripC12.d P))[F | setX E G] = \Pr_(TripA.d (Swap.d (TripA.d P)))[F| setX G E].
Proof.
rewrite /cPr; congr (_ / _).
by rewrite TripA.Pr TripC12.Pr TripA.Pr [in RHS]Swap.Pr Swap.dI TripA.Pr.
rewrite -/(Proj13.d _) -(Swap.dI (Proj13.d P)) Swap.Pr Swap.dI; congr Pr.
(* TODO: lemma? *)
by rewrite /Proj13.d /Swap.d /Bivar.snd /TripA.d !DistMap.comp.
Qed.

End conditional_probability_prop3.

Section product_rule.
Section main.
Variables (A B C : finType) (P : {dist A * B * C}).
Implicit Types (E : {set A}) (F : {set B}) (G : {set C}).

Lemma product_rule E F G :
  \Pr_P [setX E F | G] = \Pr_(TripA.d P) [E | setX F G] * \Pr_(Proj23.d P) [F | G].
Proof.
rewrite /cPr; rewrite !mulRA; congr (_ * _); last by rewrite Proj23.snd.
rewrite -mulRA -/(Proj23.d _) -TripA.Pr.
case/boolP : (Pr (Proj23.d P) (setX F G) == 0) => H; last by rewrite mulVR ?mulR1.
suff -> : Pr (TripA.d P) (setX E (setX F G)) = 0 by rewrite mul0R.
rewrite TripA.Pr; exact/Proj23.Pr_domin/eqP.
Qed.
End main.
Section variant.
Variables (A B C : finType) (P : {dist A * B * C}).
Implicit Types (E : {set A}) (F : {set B}) (G : {set C}).

Lemma product_ruleC E F G :
  \Pr_P [ setX E F | G] = \Pr_(TripA.d (TripC12.d P)) [F | setX E G] * \Pr_(Proj13.d P) [E | G].
Proof. by rewrite -cPr_TripC12 product_rule. Qed.
End variant.
End product_rule.

Section conditional_expectation_def.

Variable (U : finType) (P : dist U) (X : {RV P -> R}) (F : {set U}).

Definition cEx := \rsum_(r <- fin_img X) r * Pr P ((X @^-1 r) :&: F) / Pr P F.

End conditional_expectation_def.

Section conditional_expectation_prop.

Variable (U : finType) (P : dist U) (X : {RV P -> R}).
Variables (n : nat) (F : 'I_n -> {set U}).

Lemma thm65 : (forall i j, i != j -> [disjoint F i & F j]) ->
  cover [set F i | i in 'I_n] = [set: U] ->
  `E X = \rsum_(i < n) cEx X (F i) * Pr P (F i).
Proof.
move=> H1 H2; apply/esym; rewrite /cEx.
evar (f : 'I_n -> R); rewrite (eq_bigr f); last first.
  move=> i _; rewrite big_distrl /f; reflexivity.
rewrite {}/f /= (bigID (fun i => Pr P (F i) != 0)) /=.
rewrite [in X in _ + X = _]big1 ?addR0; last first.
  move=> i; rewrite negbK => /eqP ->; rewrite big1 // => r _; by rewrite mulR0.
transitivity (\rsum_(i < n | Pr P (F i) != 0)
  \rsum_(i0 <- fin_img X) (i0 * Pr P ((X @^-1 i0) :&: F i))).
  apply eq_bigr => i Fi0; apply eq_bigr => r _.
  by rewrite -!mulRA mulVR // mulR1.
rewrite -Ex_altE /Ex_alt exchange_big /=; apply eq_bigr => r _.
rewrite -big_distrr /=; congr (_ * _).
transitivity (\rsum_(i < n) Pr P (X @^-1 r :&: F i)).
  rewrite big_mkcond /=; apply eq_bigr => i _.
  case: ifPn => //; rewrite negbK => /eqP PFi0.
  rewrite /Pr big1 // => u; rewrite inE => /andP[uXr uFi].
  move/prsumr_eq0P : PFi0 => -> // u' _; exact/dist_ge0.
rewrite -Pr_big_union_disj; last first.
  move=> i j ij; rewrite -setI_eq0; apply/eqP/setP => u; rewrite !inE.
  apply/negbTE; rewrite !negb_and.
  case/boolP : (X u == r) => Xur //=.
  move: (H1 _ _ ij); rewrite -setI_eq0 => /eqP/setP/(_ u).
  by rewrite !inE => /negbT; rewrite negb_and.
congr Pr.
rewrite cover_imset in H2.
by rewrite -big_distrr /= H2 setIT.
Qed.

End conditional_expectation_prop.
