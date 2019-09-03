(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg matrix.
Require Import Reals Lra.
Require Import ssrZ ssrR Reals_ext ssr_ext logb ssralg_ext bigop_ext Rbigop.
Require Import proba entropy aep typ_seq channel.

(** * Jointly typical sequences *)

Reserved Notation "'`JTS'".

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope typ_seq_scope.
Local Open Scope channel_scope.
Local Open Scope entropy_scope.
Local Open Scope proba_scope.
Local Open Scope R_scope.

(** Definition of jointly typical sequences: *)

Section joint_typ_seq_definition.

Variables A B : finType.
Variable P : fdist A.
Variable W : `Ch(A, B).
Variable n : nat.
Variable epsilon : R.

Definition jtyp_seq (t : 'rV[A * B]_n) :=
  [&& typ_seq P epsilon (rV_prod t).1,
      typ_seq (`O(P , W)) epsilon (rV_prod t).2 &
      typ_seq (`J(P , W)) epsilon t].

Definition set_jtyp_seq : {set 'rV[A * B]_n} := [set tab | jtyp_seq tab].

Local Notation "'`JTS'" := (set_jtyp_seq).

(** JTS(n,e) is a subset of TS_{P,W}(n,e) such that
   (x,y) \in JTS(n,e) <-> x \in TS_P(n,e) /\ y \in TS_{PW}(n,e) *)

Lemma typical_sequence1_JTS x : prod_rV x \in `JTS ->
  exp2 (- INR n * (`H P + epsilon)) <= P `^ n x.1 <= exp2 (- INR n * (`H P - epsilon)).
Proof.
rewrite inE => /and3P[/andP[/leRP JTS11 /leRP JTS12] _ _].
by rewrite prod_rVK in JTS11, JTS12.
Qed.

Lemma typical_sequence1_JTS' x : prod_rV x \in `JTS ->
  exp2 (- INR n * (`H (`O( P , W)) + epsilon)) <= (`O( P , W)) `^ n x.2 <=
  exp2 (- INR n * (`H (`O( P , W)) - epsilon)).
Proof.
rewrite inE => /and3P[_ /andP[/leRP JTS11 /leRP JTS12] _].
by rewrite prod_rVK in JTS11, JTS12.
Qed.

End joint_typ_seq_definition.

Notation "'`JTS'" := (set_jtyp_seq) : jtyp_seq_scope.
Local Open Scope jtyp_seq_scope.

(** Upper-bound for the set of jointly typical sequences: *)

Section jtyp_seq_upper.

Variables (A B : finType) (P : fdist A) (W : `Ch(A, B)).
Variable n : nat.
Variable epsilon : R.

Lemma JTS_sup : INR #| `JTS P W n epsilon| <= exp2 (INR n * (`H(P , W) + epsilon)).
Proof.
have : INR #|`JTS P W n epsilon| <= INR #|`TS (`J(P , W)) n epsilon|.
  suff : `JTS P W n epsilon \subset `TS (`J(P , W)) n epsilon.
    by move/subset_leq_card/leP/le_INR.
  apply/subsetP => tab.
  by rewrite /set_jtyp_seq inE /jtyp_seq inE => /and3P[].
move/leR_trans; apply; exact: (@TS_sup _ (`J(P , W)) epsilon n).
Qed.

End jtyp_seq_upper.

Section jtyp_seq_transmitted.

Variables (A B : finType) (P : fdist A) (W : `Ch(A, B)).
Variable epsilon : R.

Local Open Scope zarith_ext_scope.

Definition JTS_1_bound :=
  maxn '| up (aep_bound P (epsilon / 3)) |
 (maxn '| up (aep_bound (`O(P , W)) (epsilon / 3)) |
       '| up (aep_bound (`J(P , W)) (epsilon / 3)) |).

Variable n : nat.
Hypothesis He : 0 < epsilon.

(** #<img src="http://staff.aist.go.jp/reynald.affeldt/shannon/typ_seq1-10.png"># *)

Lemma JTS_1 : (JTS_1_bound <= n)%nat ->
  1 - epsilon <= Pr (`J(P , W) `^ n) (`JTS P W n epsilon).
Proof.
have : (JTS_1_bound <= n)%nat ->
  Pr ( `J( P `^ n , W ``^ n) )
    [set x | x.1 \notin `TS P n epsilon] +
  Pr ( `J( P `^ n , W ``^ n) )
    [set x | x.2 \notin `TS (`O(P , W)) n epsilon] +
  Pr ( `J( P `^ n , W ``^ n))
    [set x | prod_rV x \notin `TS ( `J( P , W) ) n epsilon] <= epsilon.
  have H1 : forall n, Pr (`J(P , W) `^ n) [set x | (rV_prod x).1 \notin `TS P n epsilon ] <=
    Pr (P `^ n) [set x | x \notin `TS P n (epsilon / 3)].
    move=> m.
    have : 1 <= 3 by lra.
    move/(set_typ_seq_incl P m (ltRW He)) => Hincl.
    rewrite (JointFDistChan.Pr_DMC_fst P W (fun x => x \notin `TS P m epsilon)).
    apply/Pr_incl/subsetP => i /=; rewrite !inE.
    apply contra.
    move/subsetP : Hincl => /(_ i).
    by rewrite !inE.
  have {H1}HnP : forall n, ('| up (aep_bound P (epsilon / 3)) | <= n)%nat ->
    Pr (`J(P , W) `^ n) [set x | (rV_prod x).1 \notin `TS P n epsilon ] <= epsilon /3.
    move=> m Hm.
    apply: leR_trans; first exact: (H1 m).
    have m_prednK : m.-1.+1 = m.
      rewrite prednK // (leq_trans _ Hm) // (_ : O = '| 0 |) //.
      apply/ltP/Zabs_nat_lt; split; [by [] | apply/up_pos/aep_bound_ge0; lra].
    have : 1 - (epsilon / 3) <= Pr (P `^ m) (`TS P m (epsilon/3)).
      rewrite -m_prednK.
      apply Pr_TS_1.
      - apply divR_gt0 => //; lra.
      - rewrite m_prednK.
        move/leP/le_INR : Hm; apply leR_trans.
        rewrite INR_Zabs_nat; last first.
          apply/ltZW/up_pos/aep_bound_ge0 => //.
          apply divR_gt0 => //; lra.
        exact/ltRW/(proj1 (archimed _ )).
    rewrite leR_subl_addr addRC -leR_subl_addr; apply: leR_trans.
    rewrite Pr_to_cplt setCK; exact/leRR.
  have H1 : forall n,
    Pr (`J(P , W) `^ n) [set x | (rV_prod x).2 \notin `TS ( `O(P , W) ) n epsilon ] <=
    Pr ( (`O( P , W) ) `^ n) (~: `TS ( `O( P , W) ) n (epsilon / 3)).
    move=> m.
    have : 1 <= 3 by lra.
    move/(set_typ_seq_incl (`O(P , W)) m (ltRW He)) => Hincl.
    rewrite JointFDistChan.Pr_DMC_out.
    apply/Pr_incl/subsetP => i /=; rewrite !inE.
    apply contra.
    move/subsetP : Hincl => /(_ i).
    by rewrite !inE.
  have {H1}HnPW : forall n, ('| up (aep_bound (`O(P , W)) (epsilon / 3)) | <= n)%nat ->
    Pr (`J(P , W) `^ n) [set x | (rV_prod x).2 \notin `TS (`O(P , W)) n epsilon] <= epsilon /3.
    move=> m Hm.
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
    rewrite Pr_to_cplt setCK; exact/leRR.
  have H1 : forall n, Pr (`J(P , W) `^ n) (~: `TS (`J(P , W)) n epsilon) <=
    Pr (( `J( P , W) ) `^ n) (~: `TS (`J( P , W)) n (epsilon / 3)).
    move=> m.
    have : 1 <= 3 by lra.
    move/(set_typ_seq_incl (`J( P , W)) m (ltRW He)) => Hincl.
    apply/Pr_incl/subsetP => /= v; rewrite !inE.
    apply contra.
    move/subsetP : Hincl => /(_ v); by rewrite !inE.
  have {H1}HnP_W : forall n, ('| up (aep_bound (`J(P , W)) (epsilon / 3)) | <= n)%nat ->
    Pr (`J(P , W) `^ n) (~: `TS (`J( P , W)) n epsilon) <= epsilon /3.
    move=> m Hm.
    apply: leR_trans; first exact: (H1 m).
    have m_prednK : m.-1.+1 = m.
      rewrite prednK // (leq_trans _ Hm) // (_ : O = '| 0 |) //.
      apply/ltP/Zabs_nat_lt; split; [by []|apply/up_pos/aep_bound_ge0; lra].
    have : 1 - epsilon / 3 <= Pr ((`J( P , W)) `^ m) (`TS (`J( P , W)) m (epsilon / 3)).
      rewrite -m_prednK; apply Pr_TS_1.
      - apply divR_gt0 => //; lra.
      - rewrite m_prednK.
        move/leP/le_INR : Hm; apply leR_trans.
        rewrite INR_Zabs_nat; last first.
          apply/ltZW/up_pos/aep_bound_ge0; lra.
        exact/Rlt_le/(proj1 (archimed _ )).
    rewrite leR_subl_addr addRC -leR_subl_addr; apply: leR_trans.
    rewrite Pr_to_cplt setCK; exact/leRR.
  move=> Hn.
  rewrite [in X in _ <= X](_ : epsilon = epsilon / 3 + epsilon / 3 + epsilon / 3)%R; last by field.
  move: Hn; rewrite 2!geq_max => /andP[Hn1 /andP[Hn2 Hn3]].
  rewrite !JointFDistChan.Pr_DMC_rV_prod.
  apply leR_add; first by apply leR_add; [exact: HnP | exact: HnPW].
  apply: leR_trans; last exact/HnP_W/Hn3.
  apply/Req_le; congr Pr; apply/setP => /= tab; by rewrite !inE rV_prodK.
move=> Hn_Pr Hn.
suff H : Pr (`J(P , W) `^ n ) (~: `JTS P W n epsilon) <= epsilon.
  rewrite -(Pr_cplt (`J(P , W) `^ n) (`JTS P W n epsilon)).
  by rewrite leR_subl_addr leR_add2l.
apply (@leR_trans (Pr (`J(P , W) `^ n)
                      ([set x | ((rV_prod x).1 \notin `TS P n epsilon)] :|:
                       ([set x | ((rV_prod x).2 \notin `TS (`O( P , W)) n epsilon)] :|:
                        (~: `TS (`J( P , W)) n epsilon))))).
  apply Req_le; congr Pr; apply/setP => xy; by rewrite !inE 2!negb_and orbA.
apply: leR_trans; last exact: Hn_Pr.
apply (@leR_trans (
 Pr (`J(P , W) `^ n) [set x | (rV_prod x).1 \notin `TS P n epsilon] +
 Pr (`J(P , W) `^ n) ([set x | ((rV_prod x).2 \notin `TS (`O( P , W)) n epsilon)] :|:
                      (~: `TS (`J( P , W)) n epsilon)))).
  exact: Pr_union.
rewrite -addRA !JointFDistChan.Pr_DMC_rV_prod.
apply/leR_add2l; apply: leR_trans; last exact: Pr_union.
apply/Req_le; congr Pr; apply/setP => t; by rewrite !inE rV_prodK.
Qed.

End jtyp_seq_transmitted.

Section non_typicality.

Variables (A B : finType) (P : fdist A) (W : `Ch(A, B)).
Variable n : nat.
Variable epsilon : R.

(** #<img src="http://staff.aist.go.jp/reynald.affeldt/shannon/typ_seq2-10.png"># *)

Lemma non_typical_sequences :
  Pr ((P `^ n) `x ((`O(P , W)) `^ n))
    [set x | prod_rV x \in `JTS P W n epsilon] <= exp2 (- INR n * (`I(P, W) - 3 * epsilon)).
Proof.
rewrite /Pr /=.
apply (@leR_trans (\sum_(i | i \in `JTS P W n epsilon)
    (exp2 (- INR n * (`H P - epsilon)) * exp2 (- INR n * (`H( P `o W ) - epsilon))))) => /=.
  rewrite (reindex_onto (fun y => prod_rV y) (fun x => rV_prod x)) /=; last first.
    move=> ? ?; by rewrite rV_prodK.
  apply: ler_rsum_l => i Hi.
  - rewrite inE in Hi.
    rewrite ProdFDist.dE.
    apply leR_pmul => //.
    exact: proj2 (typical_sequence1_JTS Hi).
    exact: proj2 (typical_sequence1_JTS' Hi).
  - exact/mulR_ge0.
  - rewrite inE in Hi.
    by rewrite prod_rVK eqxx andbC.
rewrite (_ : \sum_(_ | _) _ =
  INR #| `JTS P W n epsilon| *
  exp2 (- INR n * (`H P - epsilon)) * exp2 (- INR n * (`H( P `o W) - epsilon))); last first.
  rewrite big_const_seq /= (_ : count _ _ = #|`JTS P W n epsilon|); last first.
    by rewrite -size_filter filter_index_enum -cardE.
  by rewrite iter_addR -mulRA.
apply (@leR_trans (exp2 (INR n * (`H( P , W ) + epsilon)) *
  exp2 (- INR n * (`H P - epsilon)) * exp2 (- INR n * (`H( P `o W ) - epsilon)))).
  do 2 apply leR_wpmul2r => //.
  exact/JTS_sup.
apply Req_le.
rewrite -2!ExpD.
congr (exp2 _).
rewrite /MutualInfoChan.mut_info !mulRDr 2!Rmult_opp_opp (_ : 3 * epsilon = epsilon + epsilon + epsilon); by field.
Qed.

End non_typicality.
