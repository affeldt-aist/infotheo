From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap matrix lra.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter smc_tactics.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* Necessary helpers for formalization of:                                    *)
(*                                                                            *)
(* Dumas, J. G., Lafourcade, P., Orfila, J. B., & Puys, M. (2017).            *)
(* Dual protocols for private multi-party matrix multiplication               *)
(* and trust computations.                                                    *)
(* Computers & security, 71, 51-70.                                           *)
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
Local Open Scope vec_ext_scope.

Local Definition R := Rdefinitions.R.

Reserved Notation "u *h w" (at level 40).
Reserved Notation "u ^h w" (at level 40).

Section log_extra.

Lemma logr_eq1 (x : R) : 0 < x -> (log x = 0) <-> (x = 1).
Proof.
move=> Hpos; split.
- (* log x = 0 -> x = 1 *)
  move=> Hlog.
  rewrite -[x]logK //.
  by rewrite Hlog exp.powRr0.
- (* x = 1 -> log x = 0 *)
  move=> ->.
  exact: log1.
Qed.

End log_extra.

Section bigop_extra.

Lemma bigD1_filter {R : Type} {op : SemiGroup.com_law R} {idx : R}
  {I : eqType} (r : seq I) (j : I) (P : pred I) (F : I -> R) :
  j \in r -> P j -> uniq r ->
  \big[op/idx]_(i <- [seq x <- r | P x]) F i = 
    op (F j) (\big[op/idx]_(i <- [seq x <- r | P x] | i != j) F i).
Proof.
Proof.
move=> j_in Pj uniq_r.
apply: bigD1_seq; last by apply: filter_uniq.
by rewrite mem_filter Pj j_in.
Qed.

Lemma bigD1_seq_cond {R : Type} {op : SemiGroup.com_law R} {idx : R}
  {I : eqType} (r : seq I) (j : I) (P : pred I) (F : I -> R) :
  j \in r -> P j -> uniq r ->
  \big[op/idx]_(i <- r | P i) F i = 
    op (F j) (\big[op/idx]_(i <- r | P i && (i != j)) F i).
Proof.
move=> j_in Pj uniq_r.
rewrite (big_rem_AC op idx P F j_in) Pj /=.
congr (op (F j) _).
rewrite (rem_filter _ uniq_r).
rewrite -(@big_filter _ _ _ _ r (predI P (predC1 j)) F).
rewrite -(@big_filter _ _ _ _ [seq x <- r | predC1 j x] P F).
congr (\big[op/idx]_(i <- _) F i).
by rewrite filter_predI.
Qed.

End bigop_extra.

Section proba_extra.

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

Section perm_extra.

Lemma fdist_proj23_RV3  (T : finType) (P : R.-fdist T) (TA TB TC : finType) 
    (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z : {RV P -> TC})
 : fdist_proj23 `p_[% X, Y, Z] = `p_[% Y, Z].
Proof.
by rewrite /fdist_proj23 /fdist_snd /fdistA /dist_of_RV /fdistC12 !fdistmap_comp.
Qed.

Lemma pfwd1_pair4_swap34 (T : finType) (P : R.-fdist T) (TA TB TC TD : finType) 
    (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z : {RV P -> TC}) (W : {RV P -> TD})
    a b c d :
  `Pr[ [% X, Y, Z, W] = (a, b, c, d) ] = 
  `Pr[ [% X, Y, W, Z] = (a, b, d, c) ].
Proof.
rewrite !pfwd1E; apply eq_bigl => u.
by rewrite !inE /= !xpair_eqE; do ! case: (_ == _) => //=.
Qed.

Lemma pfwd1_nested3_AC (T : finType) (P : R.-fdist T) (TA TB TC TD : finType)
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

Lemma pfwd1_pair4_mid_A (T : finType) (P : R.-fdist T) (TA TB TC TD : finType)
    (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z : {RV P -> TC}) (W : {RV P -> TD})
    a b c d :
  `Pr[ [% X, Y, Z, W] = (a, b, c, d) ] = 
  `Pr[ [% X, [% Y, Z], W] = (a, (b, c), d) ].
Proof.
rewrite !pfwd1E.
congr Pr; apply/setP => u.
by rewrite !inE /= !xpair_eqE andbA.
Qed.

Lemma centropyAC (T : finType) (P : R.-fdist T)
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

Lemma centropyA (T : finType) (P : R.-fdist T)
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

Lemma centropyA_middle {T : finType} {P : R.-fdist T}
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

Lemma centropy4_swap_2_4 (T : finType) (P : R.-fdist T)
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

Lemma marginal_swap_YZ
  (V W T : finType) (P : R.-fdist T)
  (Y : {RV P -> V}) (Z : {RV P -> W}) :
  forall y : V, (`p_[% Z, Y])`2 y = (`p_[% Y, Z])`1 y.
Proof.
move=> y.
by rewrite -fdistX_RV2 fdistX2.
Qed.

End perm_extra.

Section entropy_extra.
  
(* Entropy sum over a subset with uniform probability *)
Lemma entropy_sum_split (A : finType) 
  (S : pred A) (p : R) (prob : A -> R) :
  (forall a, S a -> prob a = p) ->
  (forall a, ~~ S a -> prob a = 0) ->
  (- \sum_(a : A) prob a * log (prob a)) = (- \sum_(a : A | S a) p * log p).
Proof.
move=> Hin Hout.
rewrite (bigID S) /=.
rewrite [X in _ + X]big1 ?addr0; last first.
  move => a /Hout ->.
  by rewrite mul0r.
congr (- _).
by apply: eq_bigr => a /Hin ->.
Qed.

Section cinde_cond_mutual_info0.

Variables (T TX TY TZ : finType).
Variable (P : R.-fdist T).
Variables (X : {RV P -> TX}) (Y : {RV P -> TY}) (Z : {RV P -> TZ}).

Lemma cinde_cond_mutual_info0 :
  P |= X _|_ Y | Z -> cond_mutual_info `p_[% X, Y, Z] = 0.
Proof.
move=> H_cinde.
rewrite cond_mutual_infoE.
apply/eqP.
rewrite big1 //.
case=> [[a b] c] _.
rewrite //=.
have [->|Habc_neq0] := eqVneq (`p_[% X, Y, Z] (a, b, c)) 0.
  by rewrite mul0r.
apply/eqP; rewrite mulf_eq0; apply/orP; right.
apply/eqP.
have H_pos: 0 < (\Pr_`p_ [% X, Y, Z][[set (a, b)] | [set c]] /
              (\Pr_(fdist_proj13 `p_ [% X, Y, Z])[[set a] | [set c]] *
               \Pr_(fdist_proj23 `p_ [% X, Y, Z])[[set b] | [set c]])).
  rewrite divr_gt0; last first.
  - apply: mulr_gt0.   
    + rewrite -Pr_jcPr_gt0 lt0Pr setX1 Pr_set1.
      by rewrite (fdist_proj13_dominN (b:=b)).
    + rewrite -Pr_jcPr_gt0 lt0Pr setX1 Pr_set1.
      by rewrite (fdist_proj23_dominN (a:=a)).
  - rewrite -Pr_jcPr_gt0 lt0Pr setX1 Pr_set1.
    exact: Habc_neq0.
  - by [].
rewrite (logr_eq1 H_pos).
move: (H_cinde a b c); rewrite /cinde_RV => H_eq.
have Hzne0: `Pr[Z = c] != 0.
  apply: contra_neq Habc_neq0 => Hz0.
  rewrite dist_of_RVE pfwd1_pairC.
  by rewrite (pfwd1_domin_RV2 [%X, Y] (a,b) Hz0).
rewrite cpr_eqE in H_eq.
rewrite /jcPr !setX1 !Pr_set1.
have ->: (fdist_proj13 `p_ [% X, Y, Z])`2 = `p_ Z.
  by rewrite fdist_proj13_snd; apply/fdist_ext => x; rewrite snd_RV3 snd_RV2.
have ->: (fdist_proj23 `p_ [% X, Y, Z])`2 = `p_ Z.
  by rewrite fdist_proj23_snd; apply/fdist_ext => y; rewrite snd_RV3 snd_RV2.
rewrite fdist_proj13_RV3 fdist_proj23_RV3.
rewrite snd_RV3 snd_RV2 !dist_of_RVE -!cpr_eqE -H_eq cpr_eqE //=.
rewrite dist_of_RVE in Habc_neq0.
by field; rewrite ?Hzne0 ?Habc_neq0.
Qed.

End cinde_cond_mutual_info0.

Section cinde_centropy_eq.

Variables (T TX TY TZ : finType).
Variable (P : R.-fdist T).
Variables (X : {RV P -> TX}) (Y : {RV P -> TY}) (Z : {RV P -> TZ}).

(* Main result: conditional independence implies conditional entropy equality *)
Lemma cinde_centropy_eq :
  P |= X _|_ Y | Z -> `H(Y | [% X, Z]) = `H(Y | Z).
Proof.
move=> H_cinde.
have H_cinde_sym: P |= Y _|_ X | Z by apply: symmetry.
have : cond_mutual_info `p_[% Y, X, Z] = 0.
  by rewrite (cinde_cond_mutual_info0 H_cinde_sym).
rewrite /cond_mutual_info.
move/eqP; rewrite subr_eq0; move/eqP.
rewrite /centropy_RV /centropy.
rewrite fdist_proj13_snd snd_RV3 snd_RV2 fdistA_RV3 snd_RV2 fdist_proj13_RV3.
move => H0.
symmetry.
exact: H0.
Qed.

End cinde_centropy_eq.

Section zero_entropy_eq_point_mass.

Variables (T : finType) (P : R.-fdist T).

Lemma zero_entropy_eq_point_mass1
  (V: finType)
  (Z : {RV P -> V}) :
  `H `p_Z = 0 <-> exists z, `Pr[Z = z] = 1.
Proof.
clear.
split; last first.
  case=> z Hz.
  apply/eqP; rewrite oppr_eq0.
  apply/eqP.
  apply: big1 => i _.
  case: (altP (i =P z)) => [-> | Hneq]; first by
    rewrite dist_of_RVE Hz mul1r log1. (* i = z *)
    (* i != z: show `Pr[Z = i] = 0 *)
    have Hi0: `Pr[ Z = i ] = 0.
      have: (1 : R) + \sum_(j | j != z) `Pr[ Z = j ] = 1.
        have Hsum: \sum_j `Pr[ Z = j ] = 1 by exact: sum_pfwd1.
        by rewrite (bigD1 z) //= Hz in Hsum.
    move=> /(f_equal (fun x => x - 1)).
    rewrite subrr addrAC subrr add0r.
    move=> /eqP.
    rewrite (psumr_eq0 _ _); last by move=> j _.
    move=> /allP /(_ i).
    rewrite mem_index_enum => /(_ erefl).
    by rewrite Hneq /= => /eqP.  
  by rewrite dist_of_RVE Hi0 mul0r.
rewrite /entropy -sumrN.
move/eqP.
rewrite psumr_eq0.
move/allP.
move => /= Hall.
have H_terms_zero: forall i : V , - (`p_ Z i * log (`p_ Z i)) = 0.
  move=> i.
  apply/eqP.
  have := Hall i.
  rewrite mem_index_enum.
  exact.
have H_01: forall i : V, `p_ Z i = 0 \/ `p_ Z i = 1.
  move=> i.
  move: (H_terms_zero i).
  move/eqP.
  rewrite oppr_eq0 dist_of_RVE mulf_eq0.
  case/boolP : (`Pr[ Z = i ] == 0) => [/eqP H0 | H_neq0 /=]; first by left.
  move/eqP.
  rewrite logr_eq1; first by right. 
  by rewrite lt0r H_neq0 pfwd1_ge0.
have Hsum: \sum_i `Pr[ Z = i ] = 1.
  exact: sum_pfwd1.
(* Assume that everything is zero. *)
case/boolP : [forall i : V, `p_ Z i == 0] => Hall0.
  move /eqP : Hsum.
  rewrite big1.
    by rewrite eq_sym oner_eq0.
  move/forallP in Hall0.
  move => i _.
  apply/eqP.
  by rewrite -dist_of_RVE.
move: Hall0.
rewrite negb_forall.
case/existsP => i.
case: (H_01 i).
  by move/eqP => ->.
rewrite dist_of_RVE.
move => H1 _.
by exists i.
move => i _.
case: (altP (`p_ Z i =P 0)) => [-> | Hneq0]; first by rewrite mul0r oppr0.
  have /andP [Hge0 Hle1] := fdist_ge0_le1 (`p_ Z) i.
  have Hpos: 0 < `p_ Z i by rewrite lt0r Hneq0 Hge0.
  have Hlog_neg: log (`p_ Z i) <= 0.
    rewrite -log1 ler_log.
      - exact: Hle1.
      - rewrite posrE //.
        by rewrite posrE //.
rewrite -mulrN.
rewrite pmulr_rge0; first by rewrite oppr_ge0.
exact: Hpos.
Qed.

Lemma zero_entropy_eq_point_mass
  (V: finType)
  (Z : {RV P -> V}) :
  `H `p_Z = 0 <-> exists! z, `Pr[Z = z] = 1.
Proof.
simpl in *.
split.
  move=> /zero_entropy_eq_point_mass1 [z Hz].
  exists z; split => [// | z' Hz'].
  (* Show z = z' using sum = 1 *)
  apply/eqP; apply/negPn/negP => Hneq.
 (* If z != z', both have prob 1, so sum >= 2 *)
  have: 2 <= \sum_i `Pr[ Z = i ].
    rewrite (bigD1 z) //= Hz (bigD1 z') /=; last by rewrite eq_sym.
    rewrite Hz'.
    have: 0 <= \sum_(i | (i != z) && (i != z')) `Pr[ Z = i ].
      by apply: sumr_ge0 => i _; exact: pfwd1_ge0.
    move=> Hge0.
    have ->: (2 : R) = 1 + 1 by rewrite -[2]/(1 + 1)%:R natrD.
    by lra.
  rewrite sum_pfwd1.
  by lra.
case=> z [Hz _].
apply/zero_entropy_eq_point_mass1.
by exists z.
Qed.

End zero_entropy_eq_point_mass.

(* The conditional entropy H(Z | Y) equals zero
   if and only if Z is completely determined by Y.

   In other words: for every possible value that Y can actually take
   (i.e., values with positive probability),
   there is exactly one corresponding value of Z that will
   occur with 100% certainty.
*)

Section zero_centropy_eq_point_mass.

(* Helper: if the conditional distribution Pr[Z | Y = y] is deterministic 
   (i.e., there exists z with Pr[Z = z | Y = y] = 1),
   then the corresponding term in the conditional entropy sum is zero. *)
Lemma centropy_term_deterministic
  (V W T : finType) (P : R.-fdist T)
  (Y : {RV P -> V}) (Z : {RV P -> W})
  (y : V) :
  `Pr[Y = y] != 0 ->
  (exists z, `Pr[Z = z | Y = y] = 1) ->
  `p_Y y * centropy1 `p_[% Z, Y] y = 0.
Proof.
move=> Hy_neq0 [z Hz].
rewrite /centropy1.
transitivity (`p_Y y * (- \sum_(w in W) (0 : R))).
  congr (_ * - _).
  apply: eq_bigr => w _.
  have [->|w_neq_z] := eqVneq w z; first by rewrite jPr_Pr cpr_in1 Hz mul1r log1.
  have Hw0: `Pr[Z = w | Y = y] = 0.
    (* Since Pr[Z = z | Y = y] = 1 and sum of probs = 1, 
       all other values must have prob 0 *)
    have Hsum := cPr_1 Y Hy_neq0.
    (* Convert from sum over fin_img to sum over W *)
    have Hsum': \sum_(w' in W) `Pr[Z = w' | Y = y] = 1.
      (* Proof of sum = 1 over W *)
      by rewrite sum_cPr_eq.
    have: 1 + \sum_(w' | w' != z) `Pr[Z = w' | Y = y] = 1.
      rewrite (bigD1 z) //= Hz in Hsum'.
      exact: Hsum'.
    move=> /(f_equal (fun x => x - 1)).
    rewrite subrr addrAC subrr add0r.
    move/eqP.
    rewrite psumr_eq0; last first.
      move => w2 _.
      rewrite -cpr_in1 -jPr_Pr.
      exact: jcPr_ge0.
    move=> /allP /(_ w).
    rewrite mem_index_enum => /(_ erefl).
    by rewrite w_neq_z /= => /eqP.
  by rewrite jPr_Pr cpr_in1 Hw0 mul0r.
by rewrite big1 ?oppr0 ?mulr0.
Qed.

(* Helper: Conditional distribution has zero entropy when centropy1 is zero *)
Lemma jfdist_cond_entropy_zero
  (V W T : finType) (P : R.-fdist T)
  (Y : {RV P -> V}) (Z : {RV P -> W})
  (y : V)
  (Hy_marginal : (`p_[% Y, Z])`1 y != 0)
  (Hy_centropy_zero : 
    - (\sum_(b in W) \Pr_`p_[% Z, Y][[set b] | [set y]] * 
      log \Pr_`p_[% Z, Y][[set b] | [set y]]) = 0) :
  let cond_dist := jfdist_cond0 `p_[% Y, Z] y Hy_marginal in
  `H cond_dist = 0.
Proof.
rewrite /entropy.
apply/eqP; rewrite oppr_eq0; apply/eqP.
transitivity (\sum_(b in W) \Pr_`p_[% Z, Y][[set b] | [set y]] * 
              log \Pr_`p_[% Z, Y][[set b] | [set y]]).
  apply: eq_bigr => b _.
  rewrite jfdist_cond0E.
  (* Now we need to show \Pr_(fdistX `p_[% Y, Z])[[set b] | [set y]] = 
     \Pr_`p_[% Z, Y][[set b] | [set y]] *)
  rewrite fdistX_RV2.
  by [].
move: Hy_centropy_zero.
move/eqP.
rewrite oppr_eq0 => /eqP.
exact.
Qed.

(* Helper: Point mass in conditional distribution implies
  conditional probability = 1 *)
Lemma point_mass_to_cond_prob
  (V W T : finType) (P : R.-fdist T)
  (Y : {RV P -> V}) (Z : {RV P -> W})
  (y : V) (z : W)
  (Hy_marginal : (`p_[% Y, Z])`1 y != 0)
  (Hz : (jfdist_cond0 `p_[% Y, Z] y Hy_marginal) z = 1) :
  `Pr[Z = z | Y = y] = 1.
Proof.
rewrite -cpr_in1 -jPr_Pr.
rewrite -fdistX_RV2.
rewrite -jfdist_cond0E.
exact: Hz.
Qed.

(* Helper: If the conditional entropy at y equals zero (as a Prop equality = 0)
   then there exists z with Pr[Z = z | Y = y] = 1. *)
Lemma zero_centropy1_point_mass
  (V W T : finType) (P : R.-fdist T)
  (Y : {RV P -> V}) (Z : {RV P -> W})
  (y : V)
  (HPrYeq0 : `Pr[Y = y] != 0)
  (Hy_centropy_zero : 
    - (\sum_(b in W) \Pr_`p_[% Z, Y][[set b] | [set y]] * 
      log \Pr_`p_[% Z, Y][[set b] | [set y]]) = 0) :
  exists z : W, `Pr[Z = z | Y = y] = 1.
Proof.
(* Step 1: Get marginal for Y in the swapped distribution *)
have Hy_marginal : (`p_[% Y, Z])`1 y != 0.
  rewrite -marginal_swap_YZ snd_RV2 dist_of_RVE.
  exact: HPrYeq0.

(* Step 2: Construct conditional distribution *)
set cond_dist := jfdist_cond0 `p_[% Y, Z] y Hy_marginal.

(* Step 3: Show its entropy is zero *)
have H_cond_zero : `H cond_dist = 0.
  exact: jfdist_cond_entropy_zero Y Z y Hy_marginal Hy_centropy_zero.

(* Step 4: Apply zero_entropy_eq_point_mass1 to get point mass *)
have [z Hz] : exists z, cond_dist z = 1.
  (* The identity function viewed as an RV on cond_dist (wrapper RV) *)
  pose idRV : {RV cond_dist -> W} := idfun.
  (* The distribution of idRV is cond_dist itself *)
  have H_dist: `p_idRV = cond_dist.
    apply/fdist_ext => w.
    rewrite dist_of_RVE pfwd1E /idRV /=.
    rewrite /Pr.
    rewrite (eq_bigl (pred1 w)); last by move=> x; rewrite inE.
    by rewrite big_pred1_eq.

  (* With the wrapper RV, apply zero_entropy_eq_point_mass1 *)
  have [z Hz_RV]: exists z, `Pr[idRV = z] = 1.
    have := @zero_entropy_eq_point_mass1 _ cond_dist W idRV.
    rewrite H_dist H_cond_zero.
    by move=> [H_fwd _]; apply: H_fwd.

  (* Convert back: Pr[idRV = z] equals cond_dist z *)
  exists z.
  rewrite -dist_of_RVE H_dist in Hz_RV.
  exact Hz_RV.

(* Step 5: Convert to conditional probability *)
exists z.
exact: point_mass_to_cond_prob Y Z y z Hy_marginal Hz.
Qed.

(* Main lemma 1: conditional entropy is zero iff Z is a function of Y *)
Lemma zero_centropy_eq_deterministic1
  (V W T : finType) (P : R.-fdist T)
  (Y : {RV P -> V}) (Z : {RV P -> W}) :
  `H(Z | Y) = 0 <-> 
    (forall y, `Pr[Y = y] != 0 -> exists z, `Pr[Z = z | Y = y] = 1).
Proof.
split; last first.
  move => H.
  rewrite /centropy_RV centropyE.
  apply/eqP; rewrite oppr_eq0.
  rewrite fdistX_RV2.
  apply/eqP.
  (* Step 1: Express joint probability in terms of conditional *)
  transitivity (\sum_(a in V) \sum_(b in W) 
                \Pr_`p_[% Z, Y][[set b] | [set a]] * `p_Y a * 
                log \Pr_`p_[% Z, Y][[set b] | [set a]]).
    apply: eq_bigr => a _.
    apply: eq_bigr => b _.
    have ->: `p_ [% Y, Z] (a, b) = \Pr_`p_[% Z, Y][[set b] | [set a]] * `p_Y a.
      have ->: `p_ [% Y, Z] (a, b) = `p_ [% Z, Y] (b, a).
        by rewrite !dist_of_RVE pfwd1_pairC.
      rewrite -!Pr_set1.
      rewrite (_ : [set (b, a)] = [set b] `* [set a]); last first.
        by apply/setP => -[c d]; rewrite !inE xpair_eqE.
      rewrite jproduct_rule.
      by rewrite -(snd_RV2 Z Y) Pr_set1 dist_of_RVE.
    by rewrite mulrCA.

  (* Step 2: Factor out `p_Y a from inner sum *)
  transitivity (\sum_(a in V) `p_Y a * 
                \sum_(b in W) \Pr_`p_[% Z, Y][[set b] | [set a]] * 
                log \Pr_`p_[% Z, Y][[set b] | [set a]]).
    apply: eq_bigr => a _.
    rewrite big_distrr /=.
    apply: eq_bigr => b _.
    by ring.
    
  (* Step 3: Recognize as weighted conditional entropy (with minus sign) *)
  transitivity (\sum_(a in V) `p_Y a * 
                (- (- \sum_(b in W) \Pr_`p_[% Z, Y][[set b] | [set a]] * 
                    log \Pr_`p_[% Z, Y][[set b] | [set a]]))).
    apply: eq_bigr => a _.
    by rewrite opprK.
    
  (* Step 4: This is centropy1 *)
  transitivity (\sum_(a in V) `p_Y a * (- centropy1 `p_[% Z, Y] a)).
    by [].

  (* Step 5: Factor out minus sign *)
  transitivity (- \sum_(a in V) `p_Y a * centropy1 `p_[% Z, Y] a).
    by rewrite -sumrN; apply: eq_bigr => a _; rewrite mulrN.
    
  rewrite big1 ?oppr0 //.
  move => y _.
  case/boolP: (`Pr[Y = y] == 0) => [/eqP Hy_eq0 | Hy_neq0].
    by rewrite dist_of_RVE Hy_eq0 mul0r.
  rewrite centropy_term_deterministic //.
  exact: H.
  
(* The opposite direction*)
move => H y Hyneq0.
move: H.
rewrite /centropy_RV.
rewrite /centropy.
rewrite snd_RV2.
move/eqP.
rewrite psumr_eq0 //; last first.
  move => i _.
  rewrite mulr_ge0 //.
  by rewrite centropy1_ge0.
move/allP.
move => Hall.
apply: zero_centropy1_point_mass => //.
rewrite -/(centropy1 _ _).
move: (Hall y (mem_index_enum _)).
move/implyP/(_ isT).
rewrite mulf_eq0.
rewrite dist_of_RVE.
rewrite (negbTE Hyneq0).
by move/eqP.
Qed.

(* Main lemma: conditional entropy zero means Z is a unique function of Y *)
Lemma zero_centropy_eq_deterministic
  (V W T: finType) (P : R.-fdist T)
  (Y : {RV P -> V}) (Z : {RV P -> W}) :
  `H(Z | Y) = 0 <-> 
    (forall y, `Pr[Y = y] != 0 -> exists! z, `Pr[Z = z | Y = y] = 1).
Proof.
split; last first.
  (* Backward: uniqueness implies existence *)
  move => H.
  apply/zero_centropy_eq_deterministic1.
  move => y Hy.
  case: (H y Hy).
  move => z [] Hz _.
  by exists z.
(* Forward: existence + uniqueness *)
move=> /zero_centropy_eq_deterministic1 H_ex y Hy_neq0.
have [z Hz] := H_ex y Hy_neq0.
exists z; split => // z' Hz'.
move: Hz.
rewrite cpr_eqE -dist_of_RVE -((snd_RV2 Z Y)).
move/divr1_eq.
rewrite/fdist_snd.
rewrite fdistmapE /=.
move=> H_joint_eq_marg.

(* Step 1: Show that the sum equals the marginal Pr[Y = y] *)
have H_marg: \sum_(a in preim snd (pred1 y)) `p_ [% Z, Y] a = `Pr[Y = y].
  rewrite -dist_of_RVE -(snd_RV2 Z Y) /fdist_snd fdistmapE /=.
  by apply: eq_bigl => [[w y']]; rewrite !inE.

(* Step 2: Derive Pr[Z = z | Y = y] = 1 *)
have Hz: `Pr[Z = z | Y = y] = 1.
  rewrite cpr_eqE -!dist_of_RVE.
  move: H_joint_eq_marg.
  rewrite H_marg.
  rewrite !dist_of_RVE => ->.
  by rewrite divff // Hy_neq0.
  
(* Step 3: Uniqueness - both z and z' have cond prob 1 *)
apply/eqP; apply/negPn/negP => Hneq.
apply: (cPr_eq_two_ones_absurd Hy_neq0 Hneq Hz Hz').
Qed.

End zero_centropy_eq_point_mass.

End entropy_extra.

Section Zp_unit_extra.

(* 
   Helper lemmas for unit characterization in Z/mZ rings.
   
   In 'Z_m (integers mod m), an element x is a unit (invertible)
   if and only if gcd(x, m) = 1, i.e., coprime x m.
   
   This is fundamental for CRT-based analysis where we work with
   composite moduli m = p*q and need to establish invertibility
   from coprimality conditions.
   
   Mathematical proof:
   - Forward (coprime -> unit): By Bezout's identity, coprime x m means
     exists s,t: s*x + t*m = 1. In Z/m, this gives s*x ≡ 1, so s is inverse.
   - Backward (unit -> coprime): If x*y = 1 in Z/m, then x*y ≡ 1 (mod m),
     so m | (x*y - 1). Any common divisor d of x and m must divide 1.
     
   Technical note: These proofs require careful handling of:
   - egcdn/egcdnP for Bezout coefficients
   - Modular arithmetic (modnMml, modnDml)
   - Conversion between 'Z_m and nat (nat_of_ord, inZp)
*)

(* coprime x m implies x is a unit in 'Z_m (when m > 1) *)
(* 
   Key lemma from MathComp: unitZpE
   (x%:R : 'Z_m) \is a GRing.unit = coprime m x  (when 1 < m)
   
   For x : 'Z_m, we have x = (nat_of_ord x)%:R, so we can apply unitZpE directly.
*)
Lemma coprime_Zp_unit (m : nat) (x : 'Z_m) :
  (1 < m)%N -> coprime x m -> x \is a GRing.unit.
Proof.
move=> Hm_gt1 Hcoprime.
set xn := nat_of_ord x.
have Hx_eq: x = xn%:R :> 'Z_m by rewrite Zp_nat valZpK.
by rewrite Hx_eq unitZpE // coprime_sym.
Qed.

(* The converse: unit in 'Z_m implies coprime (when m > 1) *)
(* 
   Uses unitZpE in reverse: (x%:R) \is a GRing.unit = coprime m x
*)
Lemma Zp_unit_coprime (m : nat) (x : 'Z_m) :
  (1 < m)%N -> x \is a GRing.unit -> coprime x m.
Proof.
move=> Hm_gt1 Hunit.
set xn := nat_of_ord x.
have Hx_eq: x = xn%:R :> 'Z_m by rewrite Zp_nat valZpK.
by move: Hunit; rewrite Hx_eq unitZpE // coprime_sym.
Qed.

(* Equivalence form: unit status iff coprime (when m > 1) *)
Lemma Zp_unitP (m : nat) (x : 'Z_m) :
  (1 < m)%N -> (x \is a GRing.unit) = coprime x m.
Proof.
move=> Hm_gt1.
apply/idP/idP; [exact: (Zp_unit_coprime Hm_gt1) | exact: (coprime_Zp_unit Hm_gt1)].
Qed.

End Zp_unit_extra.
