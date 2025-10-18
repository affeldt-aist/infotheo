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

End zero_entropy_eq_point_mass.

End entropy_extra.
