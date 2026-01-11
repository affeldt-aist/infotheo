From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg.
From mathcomp Require Import Rstruct ring boolp finmap lra reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import extra_algebra extra_proba.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* General entropy lemmas used in dumas2017dual formalization                 *)
(*                                                                            *)
(* This file contains entropy lemmas that are more general than               *)
(* DSDP-specific:                                                             *)
(*   - Entropy sum manipulation lemmas                                         *)
(*   - Conditional independence / mutual information lemmas                    *)
(*   - Zero entropy characterization lemmas                                    *)
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

(* ========================================================================== *)
(*                      Entropy sum manipulation                               *)
(* ========================================================================== *)

Section entropy_sum.

Context {R : realType}.

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

End entropy_sum.

(* ========================================================================== *)
(*            Conditional independence and mutual information                  *)
(* ========================================================================== *)

Section cinde_cond_mutual_info0.

Context {R : realType}.
Variables (T TX TY TZ : finType).
Variable (P : R.-fdist T).
Variables (X : {RV P -> TX}) (Y : {RV P -> TY}) (Z : {RV P -> TZ}).

(* Conditional independence implies zero conditional mutual information:
   If X ⊥ Y | Z, then I(X;Y|Z) = 0. This is the information-theoretic
   characterization of conditional independence. *)
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

Context {R : realType}.
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

(* ========================================================================== *)
(*                 Zero entropy characterization lemmas                        *)
(* ========================================================================== *)

Section zero_entropy_eq_point_mass.

Context {R : realType}.
Variables (T : finType) (P : R.-fdist T).

(* Zero entropy characterizes point mass distributions:
   H(Z) = 0 iff there exists z with Pr[Z = z] = 1.
   This is the deterministic case - no uncertainty means one certain outcome. *)
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

(* Unique point mass characterization: H(Z) = 0 iff there exists UNIQUE z
   with Pr[Z = z] = 1. Strengthens zero_entropy_eq_point_mass1 with uniqueness. *)
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

(* ========================================================================== *)
(*            Zero conditional entropy characterization                        *)
(* ========================================================================== *)

(* The conditional entropy H(Z | Y) equals zero
   if and only if Z is completely determined by Y.

   In other words: for every possible value that Y can actually take
   (i.e., values with positive probability),
   there is exactly one corresponding value of Z that will
   occur with 100% certainty.
*)

Section zero_centropy_eq_point_mass.

Context {R : realType}.

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
    have := @zero_entropy_eq_point_mass1 R W cond_dist W idRV.
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
      rewrite (_ : [set (b, a)] = setX [set b] [set a]); last first.
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

