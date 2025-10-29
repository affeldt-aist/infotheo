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

Section entropy_extra.

Section cinde_cond_mutual_info0.

Variables (T TX TY TZ : finType).
Variable (P : R.-fdist T).
Variables (X : {RV P -> TX}) (Y : {RV P -> TY}) (Z : {RV P -> TZ}).

Lemma fdist_proj23_RV3 : fdist_proj23 `p_[% X, Y, Z] = `p_[% Y, Z].
Proof.
by rewrite /fdist_proj23 /fdist_snd /fdistA /dist_of_RV /fdistC12 !fdistmap_comp.
Qed.

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
field.
rewrite dist_of_RVE in Habc_neq0.
by rewrite Hzne0 Habc_neq0.
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

(* TODO: the conditional version *)
End zero_entropy_eq_point_mass.

(* The conditional entropy H(Z | Y) equals zero
   if and only if Z is completely determined by Y.

   In other words: for every possible value that Y can actually take
   (i.e., values with positive probability),
   there is exactly one corresponding value of Z that will
   occur with 100% certainty.
*)

Section zero_centropy_eq_point_mass.

(* Helper lemma. *)
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

(* Helper lemma. *)
Lemma sum_cPr_eq 
  (T A B : finType) (P : R.-fdist T)
  (X : {RV P -> A}) (Y : {RV P -> B}) (y : B) :
  `Pr[Y = y] != 0 ->
  \sum_(a in A) `Pr[X = a | Y = y] = 1.
Proof.
move=> Hy_neq0.
(* Split sum over A into values in fin_img X and those not *)
rewrite (bigID (mem (fin_img X))) /=.
(* Values not in fin_img X have probability 0 *)
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

(* Helper: Convert centropyE form (with joint prob) to pure conditional form *)
Lemma centropy_joint_to_cond
  (V W  T : finType) (P : R.-fdist T)
  (Y : {RV P -> V}) (Z : {RV P -> W})
  (y : V)
  (Hy_neq0 : `Pr[Y = y] != 0)
  (H_joint : 
    - (\sum_(b in W) fdistX `p_[% Z, Y] (y, b) * 
      log \Pr_`p_[% Z, Y][[set b] | [set y]]) = 0) :
  - (\sum_(b in W) \Pr_`p_[% Z, Y][[set b] | [set y]] * 
    log \Pr_`p_[% Z, Y][[set b] | [set y]]) = 0.
Proof.
(* Factor: fdistX `p_[% Z, Y] (y, b) = \Pr_[Z=b|Y=y] * \Pr[Y=y] *)
have H_factor: forall b, 
  fdistX `p_[% Z, Y] (y, b) = \Pr_`p_[% Z, Y][[set b] | [set y]] * `Pr[Y = y].
  move=> b.
  rewrite fdistX_RV2.
  rewrite /jcPr.
  rewrite snd_RV2 dist_of_RVE.
  rewrite setX1 Pr_set1.
  have [Py_eq0|Py_neq0] := eqVneq (`Pr[Y = y]) 0.
    - by move: Hy_neq0; rewrite Py_eq0 eqxx.
    - Fail field.
      admit.
Admitted.

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

(* Helper *)
Lemma marginal_swap_YZ
  (V W T : finType) (P : R.-fdist T)
  (Y : {RV P -> V}) (Z : {RV P -> W}) :
  forall y : V, (`p_[% Z, Y])`2 y = (`p_[% Y, Z])`1 y.
Proof.
move=> y.
by rewrite -fdistX_RV2 fdistX2.
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

(* Main lemma 1: conditional entropy is zero iff there exists a function *)
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
    Fail rewrite -big_distrr /=.
    admit.
    
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
    

  (* Step 6: Transform sum to explicit form where each term is 0 *)
  transitivity (\sum_(y in V) 
                (if `Pr[Y = y] == 0 then 0 
                 else `p_Y y * centropy1 `p_[% Z, Y] y)).
    Fail apply: eq_bigr => y _.
    admit.

  (* Step 7: Show this equals a sum of all zeros *)
  transitivity (\sum_(y in V) (0 : R)).
    apply: eq_bigr => y _.
    case: ifP => [Hy_eq0 | Hy_neq0]; first by [].
    rewrite centropy_term_deterministic; first by [].
      by rewrite Hy_neq0.
    by apply: H; rewrite Hy_neq0.
  by rewrite big1.
  
(* The opposite direction*)
rewrite /centropy_RV centropyE => /eqP.
rewrite -sumrN.
rewrite psumr_eq0.
  move/allP.
  move => /= Hall y HPrYeq0.
  apply: zero_centropy1_point_mass.
    exact: HPrYeq0.
  have Hy_cond := centropy_joint_to_cond HPrYeq0.
  Fail exact (zero_centropy1_point_mass HPrYeq0 Hy_cond).
Admitted.

(* Main lemma: conditional entropy zero means Z is a unique function of Y *)
Lemma zero_centropy_eq_deterministic
  (V W : finType)
  (Y : {RV P -> V}) (Z : {RV P -> W}) :
  `H(Z | Y) = 0 <-> 
    (forall y, `Pr[Y = y] != 0 -> exists! z, `Pr[Z = z | Y = y] = 1).
Proof.
split.
  (* Forward: existence + uniqueness *)
  move=> /zero_centropy_eq_deterministic1 H_ex y Hy_neq0.
  have [z Hz] := H_ex y Hy_neq0.
  exists z; split => // z' Hz'.
  (* Show z = z' using sum = 1 *)
  apply/eqP; apply/negPn/negP => Hneq.
  (* If z != z', both have prob 1, so sum >= 2 *)
  have: 2 <= \sum_w `Pr[Z = w | Y = y].
    rewrite (bigD1 z) //= Hz (bigD1 z') /=; last by rewrite eq_sym.
    rewrite Hz'.
    have: 0 <= \sum_(w | (w != z) && (w != z')) `Pr[Z = w | Y = y].
    admit.
(* Backward: uniqueness implies existence *)
Abort.

End zero_entropy_eq_point_mass.

End entropy_extra.
