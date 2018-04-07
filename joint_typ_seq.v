(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import Rssr Reals_ext ssr_ext log2 ssralg_ext bigop_ext Rbigop proba.
Require Import  entropy aep typ_seq channel.

(** * Jointly typical sequences *)

Reserved Notation "'`JTS'".

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope typ_seq_scope.
Local Open Scope channel_scope.
Local Open Scope entropy_scope.
Local Open Scope proba_scope.

(** Definition of jointly typical sequences: *)

Section joint_typ_seq_definition.

Variables A B : finType.
Variable P : dist A.
Variable W : `Ch_1(A, B).
Variable n : nat.
Variable epsilon : R.

Definition jtyp_seq (t : 'rV[A * B]_n) :=
  typ_seq P epsilon (rV_prod t).1 &&
  typ_seq (`O(P , W)) epsilon (rV_prod t).2 &&
  typ_seq (`J(P , W)) epsilon t.

Definition set_jtyp_seq : {set 'rV[A * B]_n} := [set tab | jtyp_seq tab].

Local Notation "'`JTS'" := (set_jtyp_seq).

(** JTS(n,e) is a subset of TS_{P,W}(n,e) such that
   (x,y) \in JTS(n,e) <-> x \in TS_P(n,e) /\ y \in TS_{PW}(n,e) *)

Lemma typical_sequence1_JTS x : prod_rV x \in `JTS ->
  exp2 (- INR n * (`H P + epsilon)) <= P `^ n x.1 <= exp2 (- INR n * (`H P - epsilon)).
Proof.
rewrite inE.
case/andP=> /andP [].
case/andP=> /RleP JTS11 /RleP JTS12.
move=> _ _.
by rewrite prod_rVK in JTS11, JTS12.
Qed.

Lemma typical_sequence1_JTS' x : prod_rV x \in `JTS ->
  exp2 (- INR n * (`H (`O( P , W)) + epsilon)) <= (`O( P , W)) `^ n x.2 <=
  exp2 (- INR n * (`H (`O( P , W)) - epsilon)).
Proof.
rewrite inE.
case/andP => /andP [].
move=> _.
case/andP=> /RleP JTS11 /RleP JTS12.
move=> _.
by rewrite prod_rVK in JTS11, JTS12.
Qed.

End joint_typ_seq_definition.

Notation "'`JTS'" := (set_jtyp_seq) : jtyp_seq_scope.
Local Open Scope jtyp_seq_scope.

(** Upper-bound for the set of jointly typical sequences: *)

Section jtyp_seq_upper.

Variables A B : finType.
Variable P : dist A.
Variable W : `Ch_1(A, B).
Variable n : nat.
Variable epsilon : R.

Lemma JTS_sup : INR #| `JTS P W n epsilon| <= exp2 (INR n * (`H(P , W) + epsilon)).
Proof.
have H : INR #|`JTS P W n epsilon| <= INR #|`TS (`J(P , W)) n epsilon|.
  have H : `JTS P W n epsilon \subset `TS (`J(P , W)) n epsilon.
    apply/subsetP => tab.
    rewrite /set_jtyp_seq inE /jtyp_seq.
    case/andP => /andP [] _ _.
    by rewrite inE.
  apply le_INR.
  apply/leP.
  by apply subset_leq_card.
eapply Rle_trans; first by apply H.
by apply (@TS_sup _ (`J(P , W)) epsilon n).
Qed.

End jtyp_seq_upper.

Section jtyp_seq_transmitted.

Variable A B : finType.
Variable P : dist A.
Variable W : `Ch_1(A, B).
Variable epsilon : R.

Definition JTS_1_bound :=
  maxn (Zabs_nat (up (aep_bound P (epsilon / 3))))
 (maxn (Zabs_nat (up (aep_bound (`O(P , W)) (epsilon / 3))))
       (Zabs_nat (up (aep_bound (`J(P , W)) (epsilon / 3))))).

Variable n : nat.
Hypothesis He : 0 < epsilon.

(** #<img src="http://staff.aist.go.jp/reynald.affeldt/shannon/typ_seq1-10.png"># *)

Lemma JTS_1 : (JTS_1_bound <= n)%nat ->
  Pr (`J(P , W) `^ n) (`JTS P W n epsilon) >= 1 - epsilon.
Proof.
have : (JTS_1_bound <= n)%nat ->
  Pr ( `J( P `^ n , W ``^ n) )
    [set x | x.1 \notin `TS P n epsilon] +
  Pr ( `J( P `^ n , W ``^ n) )
    [set x | x.2 \notin `TS (`O(P , W)) n epsilon] +
  Pr ( `J( P `^ n , W ``^ n))
    [set x | prod_rV x \notin `TS ( `J( P , W) ) n epsilon] <= epsilon.
  have H1 m :
    Pr (`J(P , W) `^ m) [set x | (rV_prod x).1 \notin `TS P m epsilon ] =
    Pr (P `^ m) [set x | x \notin `TS P m epsilon].
    rewrite {1}/Pr.
    rewrite big_rV_prod /=.
    rewrite -(@pair_big_fst _ _ _ _ _ _ _ [pred x | x \notin `TS P m epsilon]) //; last first.
      move=> t /=.
      rewrite SetDef.pred_of_setE /= SetDef.finsetE /= ffunE.
      do 2 f_equal.
      apply/matrixP => a b; by rewrite {a}(ord1 a) !mxE.
    rewrite /=.
    transitivity (\rsum_(i | i \notin `TS P m epsilon)
      (P `^ m i * (\rsum_(y in 'rV[B]_m) W ``(y | i)))).
      apply eq_bigr => ta Hta.
      rewrite mulRC big_distrl /=.
      apply eq_bigr => tb _ /=.
      rewrite DMCE.
      rewrite [in RHS]TupleDist.dE -[in RHS]big_split /=.
      rewrite TupleDist.dE.
      apply eq_bigr => j _.
      by rewrite JointDist.dE /= -fst_tnth_prod_rV -snd_tnth_prod_rV.
    transitivity (\rsum_(i | i \notin `TS P m epsilon) P `^ _ i).
      apply eq_bigr => i Hi.
      by rewrite (pmf1 (W ``(| i))) mulR1.
    rewrite /Pr.
    apply eq_bigl => t; by rewrite !inE.
  have {H1}H1 : forall n, Pr (`J(P , W) `^ n) [set x | (rV_prod x).1 \notin `TS P n epsilon ] <=
    Pr (P `^ n) [set x | x \notin `TS P n (epsilon / 3)].
    move=> m.
    have : 1 <= 3 by fourier.
    move/(set_typ_seq_incl P m (ltRW _ _ He)) => Hincl.
    apply Rle_trans with (Pr (P `^ m) [set x | x \notin `TS P m epsilon]); last first.
      apply Pr_incl.
      apply/subsetP => i /=; rewrite !inE.
      apply contra.
      move/subsetP in Hincl.
      move: (Hincl i).
      by rewrite !inE.
    rewrite H1.
    by apply Req_le.
  have {H1}HnP : forall n, (Zabs_nat (up (aep_bound P (epsilon / 3))) <= n)%nat ->
    Pr (`J(P , W) `^ n) [set x | (rV_prod x).1 \notin `TS P n epsilon ] <= epsilon /3.
    move=> n0 Hn0.
    eapply Rle_trans; first by apply (H1 n0).
    have n0_prednK : n0.-1.+1 = n0.
      rewrite prednK //.
      apply/ltP.
      apply lt_le_trans with (Zabs_nat (up (aep_bound P (epsilon / 3)))); last first.
        by apply/leP.
      rewrite (_ : O = Zabs_nat 0) //.
      apply Zabs_nat_lt.
      split; first by done.
      apply up_pos, aep_bound_pos.
      fourier.
    have Htmp : Pr (P `^ n0) (`TS P n0 (epsilon/3)) >= 1 - (epsilon / 3).
      rewrite -n0_prednK.
      apply Pr_TS_1 => //.
      - apply Rlt_mult_inv_pos => //; fourier.
      - rewrite n0_prednK.
        move/leP in Hn0.
        apply le_INR in Hn0.
        apply Rle_trans with (INR (Zabs_nat (up (aep_bound P (epsilon / 3))))) => //.
        rewrite INR_Zabs_nat; last first.
          apply Zlt_le_weak, up_pos, aep_bound_pos => //.
          apply Rlt_mult_inv_pos => //; fourier.
        exact/ltRW/(proj1 (archimed _ )).
    rewrite Pr_to_cplt.
    set p1 := Pr _ _ in Htmp.
    rewrite (_ : Pr _ _ = p1); last first.
      rewrite /p1; apply Pr_ext; apply/setP => i /=; by rewrite !inE negbK.
    fourier.
  have H1 m :
    Pr (`J(P , W) `^ m) [set x | (rV_prod x).2 \notin `TS ( `O(P , W) ) m epsilon] =
    Pr (( `O(P , W) ) `^ m) (~: `TS ( `O(P , W) ) m epsilon).
    rewrite {1}/Pr big_rV_prod /=.
    rewrite -(@pair_big_snd _ _ _ _ _ _ _ [pred x | x \notin `TS (`O(P , W)) m epsilon]) //; last first.
      move=> tab /=.
      rewrite SetDef.pred_of_setE /= SetDef.finsetE /= ffunE. (* NB: clean *)
      do 3 f_equal.
      apply/matrixP => a b; rewrite {a}(ord1 a).
      by rewrite !mxE.
    rewrite /= /Pr /= exchange_big /=.
    apply eq_big => tb.
      by rewrite !inE.
    move=> Htb.
    rewrite TupleDist.dE.
    etransitivity; last by apply eq_bigr => i _; rewrite OutDist.dE; reflexivity.
    rewrite bigA_distr_bigA /=.
  (* TODO: move *)
  Local Open Scope ring_scope.
  Local Open Scope vec_ext_scope.
    rewrite (reindex_onto (fun p : 'rV[A]_m => [ffun x => p ord0 x])
      (fun y : {ffun 'I_m -> A} => \row_(i < m) y i)) /=; last first.
      move=> j _.
      apply/ffunP => /= m0.
      by rewrite ffunE mxE.
    apply eq_big => ta.
      rewrite inE; apply/esym.
      by apply/eqP/matrixP => a b; rewrite {a}(ord1 a) mxE ffunE.
    move=> k.
    rewrite TupleDist.dE /=; apply eq_bigr => l _.
    by rewrite JointDist.dE -fst_tnth_prod_rV -snd_tnth_prod_rV ffunE.
  have {H1}H1 : forall n,
    Pr (`J(P , W) `^ n) [set x | (rV_prod x).2 \notin `TS ( `O(P , W) ) n epsilon ] <=
    Pr ( (`O( P , W) ) `^ n) (~: `TS ( `O( P , W) ) n (epsilon / 3)).
    move=> m.
    have : 1 <= 3 by fourier.
    move/(set_typ_seq_incl (`O(P , W)) m (ltRW _ _ He)) => Hincl.
    apply Rle_trans with (Pr ((`O(P , W)) `^ m) (~: `TS (`O(P , W)) m epsilon)); last first.
      apply Pr_incl.
      apply/subsetP => i /=; rewrite !inE.
      apply contra.
      move/subsetP : Hincl.
      move/(_ i).
      by rewrite !inE.
      rewrite H1; by apply Req_le.
  have {H1}HnPW : forall n, (Zabs_nat (up (aep_bound (`O(P , W)) (epsilon / 3))) <= n)%nat ->
    Pr (`J(P , W) `^ n) [set x | (rV_prod x).2 \notin `TS (`O(P , W)) n epsilon] <= epsilon /3.
    move=> n0 Hn0.
    eapply Rle_trans; first by apply (H1 n0).
    have n0_prednK : n0.-1.+1 = n0.
      rewrite prednK //.
      apply/ltP.
      apply lt_le_trans with (Zabs_nat (up (aep_bound (`O(P , W)) (epsilon / 3)))); last first.
        by apply/leP.
      rewrite (_ : O = Zabs_nat 0) //.
      apply Zabs_nat_lt.
      split; first by done.
      apply up_pos, aep_bound_pos; fourier.
    have Htmp : Pr ((`O(P , W)) `^ n0) (`TS (`O(P , W)) n0 (epsilon / 3)) >=
      1 - epsilon / 3.
      rewrite -n0_prednK.
      apply Pr_TS_1 => //.
      - apply Rlt_mult_inv_pos => //; fourier.
      - move/leP in Hn0.
        apply le_INR in Hn0.
        apply Rle_trans with (INR (Zabs_nat (up (aep_bound (`O(P , W)) (epsilon / 3))))) => //.
        + rewrite INR_Zabs_nat; last first.
            apply Zlt_le_weak.
            apply up_pos, aep_bound_pos; fourier.
          exact/ltRW/(proj1 (archimed _ )).
        + by rewrite n0_prednK.
    rewrite Pr_to_cplt.
    set p1 := Pr _ _ in Htmp.
    rewrite (_ : Pr _ _ = p1); last first.
      rewrite /p1; apply Pr_ext; apply/setP => i /=; by rewrite !inE negbK.
    fourier.
  have H1 : forall n,
    Pr (`J(P , W) `^ n) (~: `TS (`J(P , W)) n epsilon) <=
    Pr (( `J( P , W) ) `^ n) (~: `TS (`J( P , W)) n (epsilon / 3)).
    move=> m.
    have : 1 <= 3 by fourier.
    move/(set_typ_seq_incl (`J( P , W)) m (ltRW _ _ He)) => Hincl.
    apply Rle_trans with (Pr ((`J( P , W)) `^ m) (~: `TS (`J( P , W)) m epsilon)); last first.
      apply Pr_incl.
      apply/subsetP => i /=; rewrite !inE.
      apply contra.
      move/subsetP : Hincl.
      move/(_ i).
      by rewrite !inE.
    by apply Req_le.
  have {H1}HnP_W : forall n, (Zabs_nat (up (aep_bound (`J(P , W)) (epsilon / 3))) <= n)%nat ->
    Pr (`J(P , W) `^ n) (~: `TS (`J( P , W)) n epsilon) <= epsilon /3.
    move=> n0 Hn0.
    eapply Rle_trans; first by apply (H1 n0).
    have n0_prednK : n0.-1.+1 = n0.
      rewrite prednK //.
      apply/ltP.
      apply lt_le_trans with (Zabs_nat (up (aep_bound (`J(P , W)) (epsilon / 3)))); last first.
        by apply/leP.
      rewrite (_ : O = Zabs_nat 0) //.
      apply Zabs_nat_lt.
      split; first by done.
      apply up_pos, aep_bound_pos; fourier.
    have Htmp : Pr ((`J( P , W)) `^ n0) (`TS (`J( P , W)) n0 (epsilon / 3)) >= 1 - epsilon / 3.
      rewrite -n0_prednK.
      apply Pr_TS_1 => //.
      - apply Rlt_mult_inv_pos => //; fourier.
      - rewrite n0_prednK.
        move/leP in Hn0.
        apply le_INR in Hn0.
        apply Rle_trans with (INR (Zabs_nat (up (aep_bound (`J(P , W)) (epsilon / 3))))) => //.
        rewrite INR_Zabs_nat; last first.
          apply Zlt_le_weak, up_pos, aep_bound_pos; fourier.
        exact/Rlt_le/(proj1 (archimed _ )).
    rewrite Pr_to_cplt.
    set p1 := Pr _ _ in Htmp.
    rewrite (_ : Pr _ _ = p1); last first.
      rewrite /p1; apply Pr_ext; apply/setP => i /=; by rewrite !inE negbK.
    fourier.
  move=> Hn.
  rewrite [in X in _ <= X] (_ : epsilon = epsilon / 3 + epsilon / 3 + epsilon / 3)%R; last by field.
  rewrite 2!geq_max in Hn.
  case/andP : Hn => Hn1; case/andP => Hn2 Hn3.
  rewrite !Pr_rV_prod.
  apply Rplus_le_compat.
    apply Rplus_le_compat; [exact: HnP | exact: HnPW].
  apply: Rle_trans; last exact/HnP_W/Hn3.
  apply/Req_le/Pr_ext/setP => /= tab.
  by rewrite !inE rV_prodK.
move=> n0n Hn0n0.
suff H : Pr (`J(P , W) `^ n ) (~: `JTS P W n epsilon) <= epsilon.
  rewrite -(Pr_cplt (`J(P , W) `^ n) (`JTS P W n epsilon)).
  have : forall a b r : R, a <= r -> b >= b + a - r by move=> *; fourier.
  by apply.
rewrite (@Pr_ext _ (`J(P , W) `^ n) (~: _)
([set x | ((rV_prod x).1 \notin `TS P n epsilon)] :|:
([set x | ((rV_prod x).2 \notin `TS (`O( P , W)) n epsilon)] :|:
          (~: `TS (`J( P , W)) n epsilon)))); last first.
  apply/setP => xy.
  by rewrite !inE 2!negb_and orbA.
eapply Rle_trans; last by apply n0n.
apply Rle_trans with (
Pr (`J(P , W) `^ n) [set x | (rV_prod x).1 \notin `TS P n epsilon] +
Pr (`J(P , W) `^ n) ([set x | ((rV_prod x).2 \notin `TS (`O( P , W)) n epsilon)] :|:
               (~: `TS (`J( P , W)) n epsilon)))%R.
  by apply: Pr_union.
rewrite -addRA !Pr_rV_prod.
apply Rplus_le_compat_l.
eapply Rle_trans; last exact: Pr_union.
apply/Req_le/Pr_ext/setP => t.
by rewrite !inE rV_prodK.
Qed.

End jtyp_seq_transmitted.

Section non_typicality.

Variables A B : finType.
Variable P : dist A.
Variable W : `Ch_1(A, B).
Variable n : nat.
Variable epsilon : R.

(** #<img src="http://staff.aist.go.jp/reynald.affeldt/shannon/typ_seq2-10.png"># *)

Lemma non_typical_sequences :
  Pr ((P `^ n) `x ((`O(P , W)) `^ n))
    [set x | prod_rV x \in `JTS P W n epsilon] <= exp2 (- INR n * (`I( P ; W) - 3 * epsilon)).
Proof.
rewrite /Pr /=.
apply Rle_trans with
  (\rsum_(i | i \in `JTS P W n epsilon)
    (exp2 (- INR n * (`H P - epsilon)) * exp2 (- INR n * (`H( P `o W ) - epsilon)))) => /=.
  rewrite (reindex_onto (fun y => prod_rV y) (fun x => rV_prod x)) /=; last first.
    move=> ? ?; by rewrite rV_prodK.
  apply: ler_rsum_l => i Hi.
  - rewrite inE in Hi.
    apply Rmult_le_compat.
    exact: dist_nonneg.
    exact: dist_nonneg.
    exact: (proj2 (typical_sequence1_JTS Hi)).
    by apply (typical_sequence1_JTS' Hi).
  - exact/mulR_ge0.
  - rewrite inE in Hi.
    by rewrite prod_rVK eqxx andbC.
rewrite (_ : \rsum_(_ | _) _ =
  INR #| `JTS P W n epsilon| *
  exp2 (- INR n * (`H P - epsilon)) * exp2 (- INR n * (`H( P `o W) - epsilon))); last first.
  rewrite big_const_seq /= (_ : count _ _ = #|`JTS P W n epsilon|); last first.
    by rewrite -size_filter filter_index_enum -cardE.
  by rewrite iter_Rplus -mulRA.
apply Rle_trans with (exp2 (INR n * (`H( P , W ) + epsilon)) *
  exp2 (- INR n * (`H P - epsilon)) * exp2 (- INR n * (`H( P `o W ) - epsilon))).
  apply: Rmult_le_compat _ (Rle_refl _) => //.
  - exact: mulR_ge0 (pos_INR _) _.
  - apply: Rmult_le_compat _ (pos_INR _) _ _ (Rle_refl _) => //.
    exact/JTS_sup.
apply Req_le.
rewrite -2!ExpD.
congr (exp2 _).
rewrite /mut_info !mulRDr 2!Rmult_opp_opp (_ : 3 * epsilon = epsilon + epsilon + epsilon); by field.
Qed.

End non_typicality.
