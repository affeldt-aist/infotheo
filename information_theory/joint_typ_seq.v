(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg matrix.
Require Import Reals Lra.
From mathcomp Require Import Rstruct.
Require Import ssrZ ssrR Reals_ext ssr_ext logb ssralg_ext bigop_ext Rbigop.
Require Import fdist proba entropy aep typ_seq channel.

(******************************************************************************)
(*                        Jointly typical sequences                           *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   JTS P W n epsilon == epsilon-jointly typical sequences of size n for an  *)
(*                        input distribution P and  a channel W               *)
(*                        JTS(n,e) is a subset of TS_{P,W}(n,e) such that     *)
(*                        (x,y) \in JTS(n,e) <->                              *)
(*                        x \in TS_P(n,e) /\ y \in TS_{PW}(n,e)               *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*  JTS_sup               == Upper-bound for the set of jointly typical       *)
(*                           sequences                                        *)
(*  JTS_1                 == when they are very long, the jointly typical     *)
(*                           sequences coincide with the typical sequences of *)
(*                           the joint distribution                           *)
(*  non_typical_sequences == the probability of the same event (joint         *)
(*                           typicality) taken over the product distribution  *)
(*                           of the inputs and the out-puts considered        *)
(*                           independently tends to 0 asngets large           *)
(*                                                                            *)
(* For details, see Reynald Affeldt, Manabu Hagiwara, and Jonas Sénizergues.  *)
(* Formalization of Shannon's theorems. Journal of Automated Reasoning,       *)
(* 53(1):63--103, 2014                                                        *)
(******************************************************************************)

Declare Scope jtyp_seq_scope.
Reserved Notation "'`JTS'".

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope typ_seq_scope.
Local Open Scope fdist_scope.
Local Open Scope channel_scope.
Local Open Scope entropy_scope.
Local Open Scope R_scope.

Section joint_typ_seq_definition.

Variables A B : finType.
Variable P : {fdist A}.
Variable W : `Ch(A, B).
Variable n : nat.
Variable epsilon : R.

Definition jtyp_seq (t : 'rV[A * B]_n) :=
  [&& typ_seq P epsilon (rV_prod t).1,
      typ_seq (`O(P , W)) epsilon (rV_prod t).2 &
      typ_seq ((P `X W)) epsilon t].

Definition set_jtyp_seq : {set 'rV[A * B]_n} := [set tab | jtyp_seq tab].

Local Notation "'`JTS'" := (set_jtyp_seq).

Lemma typical_sequence1_JTS x : prod_rV x \in `JTS ->
  exp2 (- INR n * (`H P + epsilon)) <= P `^ n x.1 <= exp2 (- INR n * (`H P - epsilon)).
Proof.
rewrite inE => /and3P[/andP[/RleP JTS11 /RleP JTS12] _ _].
by rewrite prod_rVK in JTS11, JTS12.
Qed.

Lemma typical_sequence1_JTS' x : prod_rV x \in `JTS ->
  exp2 (- INR n * (`H (`O( P , W)) + epsilon)) <= (`O( P , W)) `^ n x.2 <=
  exp2 (- INR n * (`H (`O( P , W)) - epsilon)).
Proof.
rewrite inE => /and3P[_ /andP[/RleP JTS11 /RleP JTS12] _].
by rewrite prod_rVK in JTS11, JTS12.
Qed.

End joint_typ_seq_definition.

Notation "'`JTS'" := (set_jtyp_seq) : jtyp_seq_scope.
Local Open Scope jtyp_seq_scope.

Section jtyp_seq_upper.

Variables (A B : finType) (P : {fdist A}) (W : `Ch(A, B)).
Variable n : nat.
Variable epsilon : R.

Lemma JTS_sup : INR #| `JTS P W n epsilon| <= exp2 (INR n * (`H(P , W) + epsilon)).
Proof.
have : INR #|`JTS P W n epsilon| <= INR #|`TS ((P `X W)) n epsilon|.
  suff : `JTS P W n epsilon \subset `TS ((P `X W)) n epsilon.
    by move/subset_leq_card/leP/le_INR.
  apply/subsetP => tab.
  by rewrite /set_jtyp_seq inE /jtyp_seq inE => /and3P[].
move/leR_trans; apply; exact: (@TS_sup _ ((P `X W)) epsilon n).
Qed.

End jtyp_seq_upper.

Section jtyp_seq_transmitted.
Variables (A B : finType) (P : {fdist A}) (W : `Ch(A, B)).
Variable epsilon : R.

Local Open Scope zarith_ext_scope.

Definition JTS_1_bound :=
  maxn '| up (aep_bound P (epsilon / 3)) |
 (maxn '| up (aep_bound (`O(P , W)) (epsilon / 3)) |
       '| up (aep_bound ((P `X W)) (epsilon / 3)) |).

Variable n : nat.
Hypothesis He : 0 < epsilon.

Lemma JTS_1 : (JTS_1_bound <= n)%nat ->
  1 - epsilon <= Pr ((P `X W) `^ n) (`JTS P W n epsilon).
Proof.
have : (JTS_1_bound <= n)%nat ->
  Pr ( (P `^ n `X (W ``^ n)) )
    [set x | x.1 \notin `TS P n epsilon] +
  Pr ( (P `^ n `X (W ``^ n)) )
    [set x | x.2 \notin `TS (`O(P , W)) n epsilon] +
  Pr ( (P `^ n `X  (W ``^ n)))
    [set x | prod_rV x \notin `TS ( (P `X W) ) n epsilon] <= epsilon.
  have H1 : forall n, Pr ((P `X W) `^ n) [set x | (rV_prod x).1 \notin `TS P n epsilon ] <=
    Pr (P `^ n) [set x | x \notin `TS P n (epsilon / 3)].
    move=> m.
    have : 1 <= 3 by lra.
    move/(set_typ_seq_incl P m (ltRW He)) => Hincl.
    rewrite (Pr_DMC_fst P W (fun x => x \notin `TS P m epsilon)).
    apply/Pr_incl/subsetP => i /=; rewrite !inE.
    apply contra.
    by move/subsetP : Hincl => /(_ i); rewrite !inE.
  have {H1}HnP : forall n, ('| up (aep_bound P (epsilon / 3)) | <= n)%nat ->
    Pr ((P `X W) `^ n) [set x | (rV_prod x).1 \notin `TS P n epsilon ] <= epsilon /3.
    move=> m Hm.
    apply: leR_trans; first exact: (H1 m).
    have m_prednK : m.-1.+1 = m.
      rewrite prednK // (leq_trans _ Hm) // (_ : O = '| 0 |) //.
      by apply/ltP/Zabs_nat_lt; split; [by [] | apply/up_pos/aep_bound_ge0; lra].
    have : 1 - (epsilon / 3) <= Pr (P `^ m) (`TS P m (epsilon/3)).
      rewrite -m_prednK.
      apply Pr_TS_1.
      - by apply divR_gt0 => //; lra.
      - rewrite m_prednK.
        move/leP/le_INR : Hm; apply leR_trans.
        rewrite INR_Zabs_nat; last first.
          apply/ltZW/up_pos/aep_bound_ge0 => //.
          apply divR_gt0 => //; lra.
        exact/ltRW/(proj1 (archimed _ )).
    rewrite leR_subl_addr addRC -leR_subl_addr; apply: leR_trans.
    rewrite Pr_to_cplt setCK.
    by apply/RleP; rewrite Order.POrderTheory.lexx.
  have H1 m :
    Pr ((P `X W) `^ m) [set x | (rV_prod x).2 \notin `TS ( `O(P , W) ) m epsilon ] <=
    Pr ( (`O( P , W) ) `^ m) (~: `TS ( `O( P , W) ) m (epsilon / 3)).
    have : 1 <= 3 by lra.
    move/(set_typ_seq_incl (`O(P , W)) m (ltRW He)) => Hincl.
    rewrite Pr_DMC_out.
    apply/Pr_incl/subsetP => i /=; rewrite !inE.
    apply contra.
    move/subsetP : Hincl => /(_ i).
    by rewrite !inE.
  have {H1}HnPW m : ('| up (aep_bound (`O(P , W)) (epsilon / 3)) | <= m)%nat ->
    Pr ((P `X W) `^ m) [set x | (rV_prod x).2 \notin `TS (`O(P , W)) m epsilon] <= epsilon /3.
    move=> Hm.
    apply: leR_trans; first exact: (H1 m).
    have m_prednK : m.-1.+1 = m.
      rewrite prednK // (leq_trans _ Hm) // (_ : O = '| 0 |) //.
      apply/ltP/Zabs_nat_lt (* TODO: ssrZ? *); split; [by []|apply/up_pos/aep_bound_ge0; lra].
    have : 1 - epsilon / 3 <= Pr ((`O(P , W)) `^ m) (`TS (`O(P , W)) m (epsilon / 3)).
      rewrite -m_prednK.
      apply Pr_TS_1.
      - apply divR_gt0 => //; lra.
      - move/leP/le_INR : Hm.
        rewrite m_prednK.
        apply leR_trans.
        rewrite INR_Zabs_nat; last first.
          apply/ltZW/up_pos/aep_bound_ge0; lra.
        exact/ltRW/(proj1 (archimed _ )).
    rewrite leR_subl_addr addRC -leR_subl_addr; apply: leR_trans.
    rewrite Pr_to_cplt setCK.
    by apply/RleP; rewrite Order.POrderTheory.lexx.
  have H1 m : Pr ((P `X W) `^ m) (~: `TS ((P `X W)) m epsilon) <=
    Pr (((P `X W) ) `^ m) (~: `TS ((P `X W)) m (epsilon / 3)).
    have : 1 <= 3 by lra.
    move/(set_typ_seq_incl ((P `X W)) m (ltRW He)) => Hincl.
    apply/Pr_incl/subsetP => /= v; rewrite !inE.
    apply contra.
    by move/subsetP : Hincl => /(_ v); by rewrite !inE.
  have {H1}HnP_W m : ('| up (aep_bound ((P `X W)) (epsilon / 3)) | <= m)%nat ->
    Pr ((P `X W) `^ m) (~: `TS ((P `X W)) m epsilon) <= epsilon /3.
    move=> Hm.
    apply: leR_trans; first exact: (H1 m).
    have m_prednK : m.-1.+1 = m.
      rewrite prednK // (leq_trans _ Hm) // (_ : O = '| 0 |) //.
      apply/ltP/Zabs_nat_lt; split; [by []|apply/up_pos/aep_bound_ge0; lra].
    have : 1 - epsilon / 3 <= Pr (((P `X W)) `^ m) (`TS ((P `X W)) m (epsilon / 3)).
      rewrite -m_prednK; apply Pr_TS_1.
      - apply divR_gt0 => //; lra.
      - rewrite m_prednK.
        move/leP/le_INR : Hm; apply leR_trans.
        rewrite INR_Zabs_nat; last first.
          apply/ltZW/up_pos/aep_bound_ge0; lra.
        exact/Rlt_le/(proj1 (archimed _ )).
    rewrite leR_subl_addr addRC -leR_subl_addr; apply: leR_trans.
    rewrite Pr_to_cplt setCK.
    by apply/RleP; rewrite Order.POrderTheory.lexx.
  move=> Hn.
  rewrite [in X in _ <= X](_ : epsilon = epsilon / 3 + epsilon / 3 + epsilon / 3)%R; last by field.
  move: Hn; rewrite 2!geq_max => /andP[Hn1 /andP[Hn2 Hn3]].
  rewrite !Pr_DMC_rV_prod.
  apply leR_add; first by apply leR_add; [exact: HnP | exact: HnPW].
  apply: leR_trans; last exact/HnP_W/Hn3.
  by apply/Req_le; congr Pr; apply/setP => /= tab; by rewrite !inE rV_prodK.
move=> Hn_Pr Hn.
suff H : Pr ((P `X W) `^ n ) (~: `JTS P W n epsilon) <= epsilon.
  rewrite -(Pr_cplt ((P `X W) `^ n) (`JTS P W n epsilon)).
  by rewrite leR_subl_addr leR_add2l.
apply (@leR_trans (Pr ((P `X W) `^ n)
                      ([set x | ((rV_prod x).1 \notin `TS P n epsilon)] :|:
                       ([set x | ((rV_prod x).2 \notin `TS (`O( P , W)) n epsilon)] :|:
                        (~: `TS ((P `X W)) n epsilon))))).
  by apply Req_le; congr Pr; apply/setP => xy;  rewrite !inE 2!negb_and orbA.
apply: leR_trans; last exact: Hn_Pr.
apply (@leR_trans (
 Pr ((P `X W) `^ n) [set x | (rV_prod x).1 \notin `TS P n epsilon] +
 Pr ((P `X W) `^ n) ([set x | ((rV_prod x).2 \notin `TS (`O( P , W)) n epsilon)] :|:
                      (~: `TS ((P `X W)) n epsilon)))).
  exact: Pr_union.
rewrite -addRA !Pr_DMC_rV_prod; apply/leR_add2l; apply: leR_trans (Pr_union _ _ _).
by apply/Req_le; congr Pr; apply/setP => t; rewrite !inE rV_prodK.
Qed.

End jtyp_seq_transmitted.

Section non_typicality.
Variables (A B : finType) (P : {fdist A}) (W : `Ch(A, B)) (n : nat) (epsilon : R).

Lemma non_typical_sequences : Pr ((P `^ n) `x ((`O(P , W)) `^ n))
  [set x | prod_rV x \in `JTS P W n epsilon] <= exp2 (- n%:R * (`I(P, W) - 3 * epsilon)).
Proof.
rewrite /Pr /=.
apply (@leR_trans (\sum_(i | i \in `JTS P W n epsilon)
    (exp2 (- INR n * (`H P - epsilon)) * exp2 (- n%:R * (`H( P `o W ) - epsilon))))) => /=.
  rewrite (reindex_onto (fun y => prod_rV y) (fun x => rV_prod x)) /=; last first.
    by move=> ? ?; rewrite rV_prodK.
  apply: leR_sumRl => i; rewrite inE => iJTS.
  - rewrite fdist_prodE; apply leR_pmul => //.
    exact: proj2 (typical_sequence1_JTS iJTS).
    exact: proj2 (typical_sequence1_JTS' iJTS).
  - exact/mulR_ge0.
  - by rewrite prod_rVK eqxx andbC.
rewrite (_ : \sum_(_ | _) _ =
  INR #| `JTS P W n epsilon| *
  exp2 (- n%:R * (`H P - epsilon)) * exp2 (- INR n * (`H( P `o W) - epsilon))); last first.
  by rewrite big_const iter_addR mulRA.
apply (@leR_trans (exp2 (INR n * (`H( P , W ) + epsilon)) *
  exp2 (- n%:R * (`H P - epsilon)) * exp2 (- INR n * (`H( P `o W ) - epsilon)))).
  do 2 apply leR_wpmul2r => //.
  exact/JTS_sup.
apply Req_le; rewrite -2!ExpD; congr (exp2 _).
rewrite /mutual_info_chan !mulRDr 2!Rmult_opp_opp.
by rewrite (_ : 3 * epsilon = epsilon + epsilon + epsilon); field.
Qed.

End non_typicality.
