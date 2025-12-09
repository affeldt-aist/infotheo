From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg.
From mathcomp Require Import Rstruct ring boolp finmap lra.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import extra_algebra.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* General probability lemmas used in dumas2017dual formalization             *)
(*                                                                            *)
(* This file contains probability lemmas that are more general than           *)
(* DSDP-specific:                                                             *)
(*   - Conditional probability lemmas                                          *)
(*   - Random variable permutation lemmas                                      *)
(*   - Joint distribution lemmas                                               *)
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
(*                    Conditional probability lemmas                           *)
(* ========================================================================== *)

Section proba_extra.

(* If a is not in the image of X, then (a, b) cannot be in the joint image.
   This is used to show that pairs outside the support have zero probability. *)
Lemma pair_notin_fin_img_fst (T A B : finType) (P : R.-fdist T)
  (X : {RV P -> A}) (Y : {RV P -> B}) (a : A) (b : B) :
  a \notin fin_img X -> (a, b) \notin fin_img [% X, Y].
Proof.
move=> a_notin_img.
apply/memPn => p Hp.
move: Hp.
rewrite /fin_img mem_undup.
move/mapP => [] t Ht ->.
rewrite xpair_eqE.
apply/nandP; left.
apply/eqP => Xt_eq_a.
move: a_notin_img.
rewrite mem_undup => /negP.
apply;apply/mapP.
exists t.
  exact: Ht.
symmetry.
exact: Xt_eq_a.
Qed.

(* Conditional probabilities sum to 1: Σ_a Pr[X = a | Y = y] = 1.
   This is the law of total probability for conditional distributions,
   essential for showing that conditional distributions are valid fdists. *)
Lemma sum_cPr_eq 
  (T A B : finType) (P : R.-fdist T)
  (X : {RV P -> A}) (Y : {RV P -> B}) (y : B) :
  `Pr[Y = y] != 0 ->
  \sum_(a in A) `Pr[X = a | Y = y] = 1.
Proof.
move=> Hy_neq0.
rewrite (bigID (mem (fin_img X))) /=.
rewrite [X in _ + X = _](eq_bigr (fun=> 0)); last first.
  move=> a a_notin_img.
  rewrite cpr_eqE.
  have ->: `Pr[[% X, Y] = (a, y)] = 0.
    apply/eqP; rewrite pfwd1_eq0; apply/eqP.
      by [].
    apply/eqP.
    apply: pair_notin_fin_img_fst.
    exact: a_notin_img.
  by rewrite mul0r.
rewrite [X in _ + X]big1 ?addr0; last by move=> i _.  
rewrite -big_uniq /=.
  apply: cPr_1.
  exact: Hy_neq0.
apply: undup_uniq.
Qed.

(* Helper lemma: if z is not in the image of Z, then conditional probability is 0 *)
Lemma cPr_eq_notin_fin_img (V W T : finType) (P : R.-fdist T)
  (Y : {RV P -> V}) (Z : {RV P -> W}) (y : V) (z : W) :
  z \notin fin_img Z -> `Pr[Z = z | Y = y] = 0.
Proof.
move=> z_notin.
rewrite cpr_eqE !pfwd1E /Pr big1 ?mul0r //.
move=> t; rewrite inE => /eqP Zt.
exfalso; move/negP: z_notin; apply.
rewrite mem_undup; apply/mapP; exists t => //.
  by rewrite mem_enum.
by move: Zt => [->].
Qed.

(* Helper: If two different values both have conditional probability 1, contradiction *)
Lemma cPr_eq_two_ones_absurd (V W T : finType) (P : R.-fdist T)
  (Y : {RV P -> V}) (Z : {RV P -> W}) (y : V) (z z' : W) :
  `Pr[Y = y] != 0 ->
  z != z' ->
  `Pr[Z = z | Y = y] = 1 ->
  `Pr[Z = z' | Y = y] = 1 ->
  False.
Proof.
move=> Hy_neq0 Hneq Hz Hz'.
(* All conditional probabilities sum to 1 *)
have H_sum: \sum_(w <- fin_img Z) `Pr[Z = w | Y = y] = 1
  by exact: (cPr_1 Z Hy_neq0).
(* Both z and z' must be in fin_img Z *)
have z_in: z \in fin_img Z by
  apply/negPn/negP => z_notin; move: (cPr_eq_notin_fin_img Y y z_notin); rewrite Hz; lra.
have z'_in: z' \in fin_img Z by
  apply/negPn/negP => z'_notin; move: (cPr_eq_notin_fin_img Y y z'_notin); rewrite Hz'; lra.
(* Extract z from sum: 1 = 1 + rest *)
move: H_sum; rewrite (bigD1_seq z) ?undup_uniq //= Hz => H_sum.
(* So rest = 0 *)
have H_rest: \sum_(w <- fin_img Z | w != z) `Pr[Z = w | Y = y] = 0 by lra.
(* But z' is in rest with value 1 *)
move: H_rest.
rewrite (@bigD1_seq_cond _ _ _ _ (fin_img Z) z' (fun w => w != z) (fun w => `Pr[Z = w | Y = y])) ?undup_uniq //=; last first.
  - by rewrite eq_sym.
rewrite Hz'.
have: 0 <= \sum_(i <- fin_img Z | (i != z) && (i != z')) `Pr[ Z = i | Y = y ].
  by apply: sumr_ge0 => w _; rewrite cPr_eq_def; exact: cPr_ge0.
by lra.
Qed.

(* Conditional fdist equals conditional probability *)
Lemma jfdist_cond_cPr_eq  {T TX TY : finType} (P : R.-fdist T)
  (X : {RV P -> TX}) (Y : {RV P -> TY}) (x : TX) (y : TY) :
  `Pr[X = x] != 0 ->
  `p_[% X, Y]`(|x) y = `Pr[Y = y | X = x].
Proof.
Proof.
move=> Hx_pos.
rewrite jfdist_condE; last first.
  by rewrite fst_RV2 dist_of_RVE.
rewrite cpr_eqE.
rewrite /jcPr.
congr (_ / _).
- rewrite Pr_fdistX.
  rewrite setX1.
  rewrite Pr_set1 dist_of_RVE.
  by rewrite pfwd1_pairC.
- rewrite fdistX2 fst_RV2.
  by rewrite Pr_set1 dist_of_RVE.
Qed.

(* If Y must satisfy a property determined by X,
   then conditional probability is zero outside that property *)
Lemma cond_prob_zero_outside_constraint 
  {T TX TY : finType} (P : R.-fdist T)
  (X : {RV P -> TX}) (Y : {RV P -> TY})
  (constraint : TX -> TY -> bool) :
  (* The constraint must hold almost surely *)
  (forall t, constraint (X t) (Y t)) ->
  (* Then conditional probability is zero outside the constraint *)
  forall x y,
    `Pr[X = x] != 0 ->
    ~~ constraint x y ->
    `Pr[Y = y | X = x] = 0.
Proof.
move=> Hconstraint x y Hx_pos Hnot_constraint.
rewrite cpr_eqE.
have Hempty: finset ([%Y, X] @^-1 (y, x)) = set0.
  apply/setP => t.
  rewrite in_set0 inE /preim /pred1 /= xpair_eqE.
  apply: contraTF Hnot_constraint => /andP[/eqP HY /eqP HX].
  by rewrite -HY -HX Hconstraint.
have ->: `Pr[[%Y, X] = (y, x)] = 0.
  by rewrite pfwd1E Hempty Pr_set0.
by rewrite mul0r.
Qed.

(* Marginalization: summing joint probabilities over Y yields marginal of X.
   Σ_y Pr[(X,Y) = (x,y)] = Pr[X = x]. Fundamental for deriving marginals. *)
Lemma PrX_fstRV  (A B T : finType) (P : R.-fdist T)
  (X : {RV P -> A}) (Y : {RV P -> B}) (x : A) :
  \sum_(y : B) `Pr[[% X, Y] = (x, y)] = `Pr[X = x].
Proof.
have ->: `Pr[X = x] = Pr (`p_X) [set x].
  by rewrite -pr_in1 Pr_set1 dist_of_RVE pr_in1.
have ->: Pr (`p_X) [set x] = Pr (`p_[% X, Y])`1 [set x].
  by rewrite fst_RV2.
have ->: Pr (`p_[% X, Y])`1 [set x] = 
         \sum_(y : B) Pr (`p_[% X, Y]) ([set x] `* [set y]).
  by rewrite -PrX_fst.
apply: eq_bigr => y _.
have ->: Pr (`p_[% X, Y]) ([set x] `* [set y]) = 
         Pr (`p_[% X, Y]) [set (x, y)].
  congr (Pr (`p_[% X, Y]) _).
  by apply/setP => -[a b]; rewrite !inE xpair_eqE.
have ->: Pr (`p_[% X, Y]) [set (x, y)] = (`p_[% X, Y]) (x, y).
   by rewrite Pr_set1.
by rewrite dist_of_RVE.
Qed.

(* Joint probability product rule: Pr[(X,Y) = (x,y)] = Pr[Y=y] * Pr[X=x|Y=y].
   This is Bayes' theorem in product form, fundamental for decomposing
   joint distributions into marginal × conditional. *)
Lemma jproduct_ruleRV (A B T : finType) (P : R.-fdist T)
  (X : {RV P -> A}) (Y : {RV P -> B}) (x : A) (y : B) :
  `Pr[[% X, Y] = (x, y)] = `Pr[Y = y] * `Pr[X = x | Y = y].
Proof.
have ->: `Pr[[% X, Y] = (x, y)] = Pr (`p_[% X, Y]) [set (x, y)].
  by rewrite -pr_in1 Pr_set1 dist_of_RVE pr_in1.
have ->: [set (x, y)] = [set x] `* [set y].
  by apply/setP => -[a b]; rewrite !inE xpair_eqE.
rewrite jproduct_rule.
rewrite mulrC; congr (_ * _).
  by rewrite snd_RV2 Pr_set1 dist_of_RVE.
by rewrite -cpr_in1 -jPr_Pr.
Qed.

End proba_extra.

(* ========================================================================== *)
(*                  Random variable permutation lemmas                         *)
(* ========================================================================== *)

Section perm_extra.

Variables (T : finType) (P : R.-fdist T).

(* Projection of triple (X,Y,Z) onto (Y,Z) gives the joint distribution of (Y,Z).
   This connects fdist_proj23 with the random variable notation. *)
Lemma fdist_proj23_RV3 (TA TB TC : finType) 
    (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z : {RV P -> TC})
 : fdist_proj23 `p_[% X, Y, Z] = `p_[% Y, Z].
Proof.
by rewrite /fdist_proj23 /fdist_snd /fdistA /dist_of_RV /fdistC12 !fdistmap_comp.
Qed.

(* Swap 3rd and 4th components in 4-tuple probability: 
   Pr[(X,Y,Z,W)=(a,b,c,d)] = Pr[(X,Y,W,Z)=(a,b,d,c)].
   Used for reordering conditioning variables. *)
Lemma pfwd1_pair4_swap34 (TA TB TC TD : finType) 
    (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z : {RV P -> TC}) (W : {RV P -> TD})
    a b c d :
  `Pr[ [% X, Y, Z, W] = (a, b, c, d) ] = 
  `Pr[ [% X, Y, W, Z] = (a, b, d, c) ].
Proof.
rewrite !pfwd1E; apply eq_bigl => u.
by rewrite !inE /= !xpair_eqE; do ! case: (_ == _) => //=.
Qed.

(* Swap components in nested triple: (a,(b,c,d)) ↔ (a,(b,d,c)).
   Relates different nestings of tuple probabilities. *)
Lemma pfwd1_nested3_AC (TA TB TC TD : finType)
    (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z : {RV P -> TC}) (W : {RV P -> TD})
    a b c d :
  `Pr[ [% X, [% Y, Z, W]] = (a, (b, c, d)) ] = 
  `Pr[ [% X, [% Y, W, Z]] = (a, (b, d, c)) ].
Proof.
rewrite !pfwd1_pairA !pfwd1E.
congr Pr.
apply/setP => u.
by rewrite !inE /= !xpair_eqE [in LHS]andbA [in RHS]andbA andbAC.
Qed.

(* Associativity for 4-tuple: (a,b,c,d) ↔ (a,(b,c),d).
   Shows that flat 4-tuples equal nested representations. *)
Lemma pfwd1_pair4_mid_A (TA TB TC TD : finType)
    (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z : {RV P -> TC}) (W : {RV P -> TD})
    a b c d :
  `Pr[ [% X, Y, Z, W] = (a, b, c, d) ] = 
  `Pr[ [% X, [% Y, Z], W] = (a, (b, c), d) ].
Proof.
rewrite !pfwd1E.
congr Pr; apply/setP => u.
by rewrite !inE /= !xpair_eqE andbA.
Qed.

(* Conditional entropy is invariant under swapping last two conditioning vars:
   H(X | Y,Z,W) = H(X | Y,W,Z). Commutativity for conditioning tuple tail. *)
Lemma centropyAC
    (A B C D : finType) (X : {RV P -> A}) (Y : {RV P -> B}) 
    (Z : {RV P -> C}) (W : {RV P -> D}) :
  `H(X | [% Y, Z, W]) = `H(X | [% Y, W, Z]).
Proof.
rewrite /centropy_RV /centropy /=.
rewrite (reindex (fun '(a, b, c) => (a, c, b)))/=.
  apply: eq_bigr => -[[b c] d] _ /=.
  rewrite !snd_RV2 !dist_of_RVE pfwd1_pairAC.
  congr *%R.
  rewrite /centropy1; congr (- _).
  rewrite /jcPr !snd_RV2.
  apply: eq_bigr => a _.
  by rewrite !setX1 !Pr_set1 !dist_of_RVE pfwd1_nested3_AC pfwd1_pairAC.
- exists (fun '(a, b, c) => (a, c, b)) => -[[? ?] ?] //=.
Qed.

(* Associativity for conditional entropy: H(X | (Y,(Z,W))) = H(X | Y,Z,W).
   Flattens nested conditioning tuples. *)
Lemma centropyA
    (A B C D : finType) (X : {RV P -> A}) (Y : {RV P -> B}) 
    (Z : {RV P -> C}) (W : {RV P -> D}) :
  `H(X | [% Y, [% Z, W]]) = `H(X | [% Y, Z, W]).
Proof.
rewrite /centropy_RV /centropy !snd_RV2.
rewrite (reindex (fun '(b, (c, d)) => ((b, c), d)))/=.
  apply: eq_bigr => [[b [c d]] H].
  rewrite !dist_of_RVE.
  rewrite pfwd1_pairA.
  congr (_ * _).
  rewrite /centropy1; congr (- _).
  rewrite /jcPr.
  apply: eq_bigr => a _.
  rewrite !snd_RV2.
  rewrite !setX1 !Pr_set1 !dist_of_RVE !pfwd1_pairA.
  congr (_ * _).
    congr (_ / _).
    by rewrite pfwd1_pair4_mid_A.
  congr (_ * _).
  congr exp.ln.
    by rewrite pfwd1_pair4_mid_A.
exists (fun '(b, c, d) => (b, (c, d))).
by move => [b [c d]].
by move => [[b c] d].
Qed.

(* Flatten nested pair in middle position: H(X | W,(V,Z),Y) = H(X | W,V,Z,Y).
   Associativity when the nested pair is in the middle of the conditioning. *)
Lemma centropyA_middle
    {A B C D E : finType} 
    (X : {RV P -> A}) (W : {RV P -> B}) 
    (V : {RV P -> C}) (Z : {RV P -> D}) (Y : {RV P -> E}) :
  `H(X | [% W, [% V, Z], Y]) = `H(X | [% W, V, Z, Y]).
Proof.
rewrite /centropy_RV /centropy //=.
rewrite (reindex (fun '((b, (c, e)), d) => ((b, c), e, d))) //=.
  apply: eq_bigr => [] [] [] b [] c d e _ //=.
  congr (_ * _).
  by rewrite !snd_RV2 !dist_of_RVE pfwd1_pair4_mid_A.
rewrite /centropy1; congr (- _).
rewrite /jcPr; apply: eq_bigr => a _.
rewrite !setX1 !Pr_set1 !snd_RV2 !dist_of_RVE !pfwd1_pairA.
congr (_ * _).
   congr (_ / _); last by rewrite -!pfwd1_pair4_mid_A.
   - rewrite -!pfwd1_pair4_mid_A !pfwd1E.
     congr Pr; apply/setP => u.
     by rewrite !inE /= !xpair_eqE [in RHS]andbA.
   congr (_ * _).
   congr exp.ln.
   congr (_ / _); last by rewrite -!pfwd1_pair4_mid_A.
     rewrite -!pfwd1_pair4_mid_A !pfwd1E.
     congr Pr; apply/setP => u.
     by rewrite !inE /= !xpair_eqE [in RHS]andbA.
exists (fun '(b, c, d, e) => (b, (c, d), e)).
by move => [[] b [] c d e].
by move => [[] [] b] c d e.
Qed.

(* Swap 2nd and 4th positions in 4-variable conditioning:
   H(X | W,Y,Z,V) = H(X | W,V,Z,Y). Used for reordering Alice's view components. *)
Lemma centropy4_swap_2_4
    (A B C D E : finType)
    (X : {RV P -> A}) (W : {RV P -> B}) (Y : {RV P -> C}) 
    (Z : {RV P -> D}) (V : {RV P -> E}) :
  `H(X | [% W, Y, Z, V]) = `H(X | [% W, V, Z, Y]).
Proof.
rewrite centropyAC.
rewrite centropyC.
rewrite centropyC.
rewrite centropyC.
rewrite centropyC.
rewrite -centropyA.
rewrite centropyAC.
rewrite -centropyA.
rewrite centropyA.
by rewrite centropyA_middle.
Qed.

(* Marginal equivalence under swap: the 2nd marginal of (Z,Y) equals
   the 1st marginal of (Y,Z). Both give the distribution of Y. *)
Lemma marginal_swap_YZ
  (V W : finType)
  (Y : {RV P -> V}) (Z : {RV P -> W}) :
  forall y : V, (`p_[% Z, Y])`2 y = (`p_[% Y, Z])`1 y.
Proof.
move=> y.
by rewrite -fdistX_RV2 fdistX2.
Qed.

End perm_extra.

