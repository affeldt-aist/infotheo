(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup perm finalg matrix.
From mathcomp Require Import boolp classical_sets.
Require Import Reals Lra ProofIrrelevance FunctionalExtensionality.
Require Import ssrR Reals_ext Ranalysis_ext ssr_ext ssralg_ext logb Rbigop.
Require Import proba convex.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.

Module ScaledConvexSpace.

Local Open Scope R_scope.

Section scaled_convex.
Variables A : convType.

Local Open Scope convex_scope.

Inductive scaled_pt := Scaled of Rpos & A | Zero.

Definition S1 := Scaled Rpos1.

Lemma Scaled_inj p : injective (Scaled p).
Proof. by move=> x y []. Qed.

Definition raw_weight pt : R :=
  if pt is Scaled r _ then r else 0.

Lemma weight_ge0 pt : 0 <= raw_weight pt.
Proof. case: pt => /= [[x] /= /ltRP/ltRW //|]; by apply leRR. Qed.

Definition weight := mkPosFun weight_ge0.

Definition point pt : weight pt > 0 -> A.
destruct pt.
+ move=> _; exact c.
+ case/ltRR.
Defined.

Lemma Rpos_prob_Op1 (r q : Rpos) : 0 <= r / addRpos r q <= 1.
Proof.
split.
+ apply /ltRW /divR_gt0; by apply /Rpos_gt0.
+ apply leR_pdivr_mulr.
    by apply /Rpos_gt0.
  rewrite mul1R.
  by apply /leR_addl /ltRW /Rpos_gt0.
Qed.
Definition Rpos_prob r q := Prob.mk (Rpos_prob_Op1 r q).

Lemma onem_div p q : q != 0 -> (p/q).~ = (q-p)/q.
Proof.
move=> Hq.
by rewrite /onem -(divRR q) // /Rdiv /Rminus -mulNR -mulRDl.
Qed.

Lemma Rpos_probC r q : Rpos_prob q r = `Pr(Rpos_prob r q).~.
Proof.
apply prob_ext => /=.
rewrite [in RHS]addRC onem_div.
  by rewrite /= addRK.
by apply Rpos_neq0.
Qed.

Definition addpt a b :=
  match a, b with
  | Scaled r x, Scaled q y => Scaled (addRpos r q) (x <| Rpos_prob r q |> y)
  | Zero, _ => b
  | _, _ => a
  end.

(* Note: we need the argument to be an Rpos, because otherwise addpt cannot
   make a commutative monoid:
   1) if addpt (Scaled 0 x) (Scaled 0 y) = Scaled 0 x commutativity fails
      so at least we need addpt (Scaled 0 x) (Scaled 0 y) = Zero
   2) if addpt (Scaled 0 x) Zero = Zero then left/right identity fail
   2) if addpt (Scaled 0 x) Zero = Scaled 0 x then associativity fails
      addpt (Scaled 0 x) (addpt (Scaled 0 y) (Scaled 0 z)) = Scaled 0 x
      addpt (addpt (Scaled 0 x) (Scaled 0 y)) (Scaled 0 z) = Scaled 0 z
   So we cannot allow 0 as argument to Scaled.                             *)

Lemma addptC : commutative addpt.
Proof.
move=> [r x|] [q y|] //=.
congr Scaled. by apply val_inj; rewrite /= addRC.
rewrite convC; congr Conv.
by rewrite [RHS]Rpos_probC.
Qed.

Lemma addptA : associative addpt.
Proof.
move=> [p x|] [q y|] [r z|] //=.
congr Scaled. by apply val_inj; rewrite /= addRA.
rewrite convA; congr Conv; last first.
  apply prob_ext => /=.
  rewrite s_of_pqE -addRA.
  rewrite Rpos_probC (@Rpos_probC r) /= !onemK.
  rewrite -(addRC p) -(addRC q) /Rdiv.
  rewrite mulRA mulRC !mulRA.
  rewrite mulVR; last by apply Rpos_neq0.
  rewrite mul1R mulRC onem_div; last by apply Rpos_neq0.
  by rewrite /= !addRA addRK.
congr Conv.
apply prob_ext => /=.
rewrite r_of_pqE /=.
rewrite s_of_pqE Rpos_probC (Rpos_probC r) /= !onemK.
rewrite {3 4}/Rdiv !mulRA -(mulRC (/ (r + q))) !mulRA.
have Hpqr : p + q + r != 0 by apply Rpos_neq0.
have Hqrp : q + r + p != 0 by apply Rpos_neq0.
rewrite (addRC r) mulVR; last by apply Rpos_neq0.
rewrite mul1R -(mulRC r) -/(Rdiv r _) onem_div //.
rewrite {3}/Rdiv divRM /=; last by apply /invR_neq0/eqP.
  rewrite -(addRC p) addRA addRK invRK; last by apply /eqP.
  by rewrite /Rdiv mulRC (mulRC p) !mulRA mulRV // mul1R.
rewrite -addRA (addRC r) addRA /= addRK.
by apply /eqP /Rpos_neq0.
Qed.

Lemma addpt0 x : addpt x Zero = x.
Proof. by case: x. Qed.

Lemma add0pt x : addpt Zero x = x.
Proof. by []. Qed.

Canonical addpt_monoid := Monoid.Law addptA add0pt addpt0.
Canonical addpt_comoid := Monoid.ComLaw addptC.

Definition barycenter (pts : seq scaled_pt) :=
  \big[addpt/Zero]_(x <- pts) x.

Lemma weight_addpt : {morph weight : x y / addpt x y >-> x + y}.
Proof. move=> [p x|] [q y|] //=; by rewrite (add0R, addR0). Qed.

Lemma weight0 : weight Zero = 0.
Proof. by []. Qed.

Lemma weight_bary pts : weight (barycenter pts) = \rsum_(x <- pts) weight x.
Proof. by rewrite (big_morph weight weight_addpt weight0). Qed.

Definition mkscaled r q (x : A) :=
  match Rlt_dec 0 r with
  | left Hr => Scaled (mulRpos (mkRpos Hr) q) x
  | right _ => Zero
  end.

Definition scalept p (x : scaled_pt) :=
  if x is Scaled q y then mkscaled p q y else Zero.

(*Definition scalept := locked scalept_def.*)

Lemma scaleptR0 p : scalept p Zero = Zero.
Proof. by []. Qed.

Lemma scalept_weight p x : 0 <= p -> weight (scalept p x) = p * weight x.
Proof.
case: x => [q y|] Hp.
  rewrite /= /mkscaled.
  case: Rlt_dec => //= Hp'.
  by rewrite (eqR_le_Ngt Hp Hp') mul0R.
by rewrite scaleptR0 mulR0.
Qed.

Lemma mkscaled_gt0 r p (x : A) (H : r > 0) :
  mkscaled r p x = Scaled (mulRpos (mkRpos H) p) x.
Proof.
rewrite /mkscaled.
case: Rlt_dec => // Hr.
congr Scaled. by apply val_inj.
Qed.

Lemma scalept_addpt r :
  0 <= r -> {morph scalept r : x y / addpt x y >-> addpt x y}.
Proof.
rewrite /scalept.
move=> Hr [p x|] [q y|] //=; last first.
  by rewrite addpt0.
rewrite /mkscaled.
case: Rlt_dec => Hpq //=.
congr Scaled.
+ apply val_inj. by rewrite /= mulRDr.
+ congr Conv. apply prob_ext => /=.
  have Hr0 : r <> 0 by apply gtR_eqF.
  rewrite /= -mulRDr -(mulRC (p+q)) divRM //.
    by rewrite -(mulRC (/r)) !mulRA mulVR ?mul1R //; apply /eqP.
  by apply/eqP/Rpos_neq0.
Qed.

Lemma scalept_bary p (H : 0 <= p) pts :
  scalept p (barycenter pts) = barycenter (map (scalept p) pts).
Proof.
rewrite (big_morph (scalept p) (scalept_addpt H) (scaleptR0 _)).
by rewrite /barycenter big_map.
Qed.

Lemma scalept_comp p q x :
  0 <= p -> 0 <= q -> scalept p (scalept q x) = scalept (p * q) x.
Proof.
move=> Hp Hq.
rewrite /scalept /mkscaled.
case: x => [r x|] //=.
case: Rlt_dec => Hqr.
  case: Rlt_dec => /= Hpr.
    case: Rlt_dec => [Hpq|].
      congr Scaled.
      by apply val_inj; rewrite /= mulRA.
    by elim; apply mulR_gt0.
  case: Rlt_dec => // Hpq'.
  elim Hpr; by apply (proj1 (pmulR_lgt0 Hqr)).
case: Rlt_dec => // Hpq.
elim Hqr.
case/leR_eqVlt: Hq => // Hq.
move: Hpq.
by rewrite -Hq mulR0 => /ltRR.
Qed.

Lemma scalept_addR p q x :
  0 <= p -> 0 <= q ->
  scalept (p + q) x = addpt (scalept p x) (scalept q x).
Proof.
move=> Hp Hq.
rewrite /scalept /mkscaled.
case: x => // r c.
case: Rlt_dec => Hpq.
  case: Rlt_dec => Hpr.
    case: Rlt_dec => Hqr.
      congr Scaled.
        by apply val_inj; rewrite /= mulRDl.
      by rewrite convmm.
    congr Scaled; apply val_inj => /=.
    by rewrite /= (eqR_le_Ngt Hq Hqr) addR0.
  case: Rlt_dec => Hqr.
    congr Scaled; apply val_inj => /=.
    by rewrite /= (eqR_le_Ngt Hp Hpr) add0R.
  elimtype False; move: Hpq.
  by rewrite (eqR_le_Ngt Hp Hpr) (eqR_le_Ngt Hq Hqr) addR0 => /ltRR.
case: Rlt_dec => Hpr.
  elim Hpq.
  by apply/addR_gt0wl.
case: Rlt_dec => Hqr.
  elim Hpq.
  by apply/addR_gt0wr.
by [].
Qed.

Lemma scalept0 x : scalept 0 x = Zero.
Proof.
case: x; rewrite /scalept /mkscaled //.
move=> r c; case: Rlt_dec => // Hr.
by elim (ltRR 0).
Qed.

Lemma scalept1 x : scalept 1 x = x.
Proof.
case: x; rewrite /scalept /mkscaled //.
move=> r c; case: Rlt_dec => // Hr.
by congr Scaled; apply val_inj; rewrite /= mul1R.
Qed.

Lemma big_scalept (B : finType) (F : B -> R+) x :
  \big[addpt/Zero]_(i : B) scalept (F i) x = scalept (\rsum_(i : B) (F i)) x.
Proof.
apply (@proj1 _ (0 <= \rsum_(i : B) F i)).
apply (big_ind2 (fun y q => y = scalept q x /\ 0 <= q)).
+ rewrite scalept0; split => //. apply leRR.
+ move=> x1 x2 y1 y2 [Hx1 Hx2] [Hy1 Hy2].
  split. by rewrite Hx1 Hy1 scalept_addR.
  by apply addR_ge0.
+ move=> i _; split => //.
  by apply pos_f_ge0.
Qed.

Section reordering.
Variables n : nat.
Variable p : {dist 'I_n}.
Variable h : 'I_n -> scaled_pt.

Lemma perm_eq_perm (pe : 'S_n) :
  perm_eq (enum 'I_n) [seq pe i | i <- enum 'I_n].
Proof.
apply uniq_perm_eq.
+ by rewrite enum_uniq.
+ rewrite map_inj_in_uniq ?enum_uniq //.
  by move=> x1 x2 _ _; apply perm_inj.
move=> i.
rewrite mem_enum inE.
symmetry.
apply/mapP.
exists (perm_inv pe i).
  by rewrite mem_enum inE.
by rewrite permKV.
Qed.

Lemma barycenter_reorder (pe : 'S_n) :
  \big[addpt/Zero]_(i < n) scalept (p i) (h i) =
  \big[addpt/Zero]_(i < n) scalept (p (pe i)) (h (pe i)).
Proof.
rewrite -[RHS](big_map pe xpredT (fun i => scalept (p i) (h i))).
apply eq_big_perm.
by rewrite /index_enum -enumT perm_eq_perm.
Qed.
End reordering.

Section convdist.
Variables n m : nat.
Variable p : {dist 'I_n}.
Variable q : 'I_n -> {dist 'I_m}.
Variable h : 'I_m -> scaled_pt.

Lemma barycenter_convdist :
  \big[addpt/Zero]_(i < n) scalept (p i)
     (\big[addpt/Zero]_(j < m) scalept (q i j) (h j))
  = \big[addpt/Zero]_(j < m) scalept (ConvDist.d p q j) (h j).
Proof.
rewrite (eq_bigr _
          (fun i _ => big_morph (scalept (p i)) (scalept_addpt (pos_f_ge0 p i))
                                (scaleptR0 _) _ _ _)).
rewrite exchange_big /=.
apply eq_bigr => j _.
rewrite (eq_bigr _
          (fun i _ => scalept_comp _ (pos_f_ge0 p i) (pos_f_ge0 (q i) j))).
rewrite ConvDist.dE.
have HF : forall i, 0 <= p i * q i j.
  by move=> i; apply mulR_ge0; apply pos_f_ge0.
rewrite (eq_bigr (mkPosFun HF)) //.
by rewrite -big_scalept; apply eq_bigr.
Qed.
End convdist.

Section binary.
Variables x y : A.
Variable p : prob.

Lemma adjunction_1 a b :
  addpt (scalept 1 (S1 a)) (scalept 0 (S1 b)) =
  S1 (a <|`Pr 1|> b).
Proof. by rewrite scalept0 scalept1 addpt0 conv1. Qed.

Lemma adjunction_2 :
  addpt (scalept p (S1 x)) (scalept p.~ (S1 y)) = S1 (x <| p |> y).
Proof.
case Hp0: (0 <b p); last first.
  move/prob_ge0/leR_eqVlt: p => [Hp | /ltRP]; last by rewrite Hp0.
  rewrite -Hp /= convC addptC {1}onem0 adjunction_1.
  by congr Scaled; congr Conv; apply prob_ext; rewrite /= -Hp onem0.
case Hp1: (0 <b p.~); last first.
  move/prob_ge0/leR_eqVlt: `Pr p.~ => [Hp | /ltRP]; last by rewrite Hp1.
  rewrite {1}(probK p) /= -Hp /= onem0 adjunction_1.
  by congr Scaled; congr Conv; apply prob_ext; rewrite (probK p) /= -Hp onem0.
move/ltRP/mkscaled_gt0: (Hp0) => /= ->.
move/ltRP/mkscaled_gt0: (Hp1) => ->.
congr Scaled.
  apply val_inj; by rewrite /= !mulR1 onemKC.
congr Conv; apply prob_ext => /=.
by rewrite !mulR1 /= addRC subRK divR1.
Qed.
End binary.

Section adjunction.
Variables (n : nat) (points : 'I_n -> A).

Definition points_of_dist (d : {dist 'I_n}) :=
  [seq scalept (d i) (S1 (points i)) | i <- enum 'I_n].

Lemma weight_gt0 d : weight (barycenter (points_of_dist d)) > 0.
rewrite weight_bary.
rewrite (_ : \rsum_(x <- _)  _ = 1).
  apply /Rlt_gt /Rlt_0_1.
rewrite big_map -(pmf1 d) big_filter.
apply eq_bigr => i _.
rewrite scalept_weight ?mulR1 //.
by apply pos_f_ge0.
Qed.

Lemma perm_eq_filter0 :
  perm_eq [seq i <- enum 'I_n.+1 | i != ord0]
          [seq lift ord0 i | i <- enum 'I_n].
Proof.
apply uniq_perm_eq.
+ by rewrite filter_uniq // enum_uniq.
+ rewrite map_inj_in_uniq ?enum_uniq //.
  by move=> x1 x2 _ _; apply lift_inj.
move=> j.
rewrite mem_filter mem_enum andbT.
symmetry.
case: (unliftP ord0 j) => /= [a|] ->.
  rewrite eq_sym neq_lift.
  rewrite mem_map. by rewrite mem_enum inE.
  by apply: lift_inj.
rewrite eqxx.
apply/mapP => /= -[x Hx].
move/(f_equal (@nat_of_ord _)).
by rewrite lift0.
Qed.
End adjunction.

Lemma adjunction_n n (points : 'I_n -> A) d :
  barycenter (points_of_dist points d) = S1 (Convn d points).
Proof.
elim: n points d => [|n IH] points d.
  move: (pmf1 d).
  rewrite big_ord0 => /Rlt_not_eq; elim.
  by apply Rlt_0_1.
rewrite /=.
case: eqVneq => Hd.
  rewrite /barycenter big_map (bigD1_seq ord0); first last.
    apply enum_uniq.
    apply mem_enum.
  rewrite Hd big1 /=.
    rewrite addpt0 (mkscaled_gt0 _ _ Rlt_0_1).
    by congr Scaled; apply val_inj; rewrite /= mulR1.
  move=> i Hi; have := pmf1 d.
  rewrite (bigD1 ord0) ?mem_enum // Hd /= addRC => /(f_equal (Rminus^~ 1)).
  rewrite addRK subRR => /prsumr_eq0P -> //.
    by rewrite -(scalept0 (S1 (points i))).
  by move=> a _; apply pos_f_ge0.
set d' := DelDist.d Hd.
set points' := fun i => points (DelDist.h ord0 i).
rewrite /barycenter big_map (bigD1_seq ord0) ?enum_uniq ?mem_enum //=.
rewrite -big_filter.
rewrite (eq_big_perm (map (lift ord0) (enum 'I_n)));
  last by apply perm_eq_filter0.
rewrite big_map.
have Hd0' : 1 - d ord0 > 0.
  by apply ltR_subRL; rewrite addR0; apply dist_lt1.
rewrite (eq_bigr
           (fun j => scalept (1 - d ord0) (mkscaled (d' j) Rpos1 (points' j))));
  last first.
  move=> i _.
  transitivity (scalept (1 - d ord0) (scalept (d' i) (S1 (points' i)))) => //.
  rewrite scalept_comp; [|by apply ltRW|by apply pos_f_ge0].
  rewrite DelDist.dE D1Dist.dE /=.
  rewrite /Rdiv (mulRC (d _)) mulRA mulRV.
    by rewrite mul1R.
  apply/eqP => H1d0.
  move: Hd0'.
  by rewrite H1d0 => /ltRR.
rewrite -(big_morph (scalept (1 - d ord0)) (scalept_addpt (ltRW Hd0'))
                    (scaleptR0 _)).
have:= IH points' d'.
rewrite /barycenter big_map => -> /=.
by rewrite -adjunction_2.
Qed.

End scaled_convex.

End ScaledConvexSpace.
