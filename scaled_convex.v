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

Section Rpos.
Inductive Rpos : predArgType := mkRpos x of x >b 0.
Definition Rpos_val (x : Rpos) := let: mkRpos y _ := x in y.
Coercion Rpos_val : Rpos >-> R.

Canonical Rpos_subType := [subType for Rpos_val].
Definition Rpos_eqMixin := Eval hnf in [eqMixin of Rpos by <:].
Canonical Rpos_eqType := Eval hnf in EqType Rpos Rpos_eqMixin.

Lemma Rpos_neq0 (x : Rpos) : val x != 0.
Proof. case: x => p /=. by rewrite /gtRb lt0R => /andP []. Qed.

Definition addRpos_def : Rpos -> Rpos -> Rpos.
intros [x Hx] [y Hy].
apply (@mkRpos (x+y)).
apply /ltRP/addR_gt0/ltRP => //.
by apply/ltRP.
Defined.

Definition addRpos := locked addRpos_def.

Lemma addRposE x y : val (addRpos x y) = val x + val y.
Proof. by rewrite /addRpos -lock; destruct x, y. Qed.

Lemma addRposC : commutative addRpos.
Proof. by move=> x y; apply val_inj; rewrite !addRposE addRC. Qed.

Lemma addRposA : associative addRpos.
Proof. by move=> x y z; apply val_inj; rewrite !addRposE addRA. Qed.

Definition mulRpos_def : Rpos -> Rpos -> Rpos.
intros [x Hx] [y Hy].
apply (@mkRpos (x*y)).
apply /ltRP/mulR_gt0/ltRP => //.
by apply/ltRP.
Defined.

Definition mulRpos := locked mulRpos_def.

Lemma mulRposE x y : val (mulRpos x y) = val x * val y.
Proof. by rewrite /mulRpos -lock; destruct x, y. Qed.

Lemma mulRposC : commutative mulRpos.
Proof. by move=> x y; apply val_inj; rewrite !mulRposE mulRC. Qed.

Lemma mulRposA : associative mulRpos.
Proof. by move=> x y z; apply val_inj; rewrite !mulRposE mulRA. Qed.

End Rpos.

Section scaled_convex.
Variables A : convType.

Local Open Scope convex_scope.

Inductive scaled_pt := Scaled of Rpos & A | Zero.

Definition raw_weight pt : R :=
  if pt is Scaled r _ then r else 0.

Lemma weight_ge0 pt : 0 <= raw_weight pt.
Proof. case: pt => /= [[x] /= /ltRP/ltRW] //; by apply leRR. Qed.

Definition weight := mkPosFun weight_ge0.

Definition point pt : weight pt > 0 -> A.
destruct pt.
+ move=> _; exact c.
+ case/ltRR.
Defined.

Definition mkscaled r (x : A) :=
  match boolP (r >b 0) with
  | AltTrue Hr => Scaled (mkRpos Hr) x
  | AltFalse _ => Zero
  end.

Lemma weight_mkscaled r x : (0 <= r) -> weight (mkscaled r x) = r.
Proof.
move=> H.
rewrite /mkscaled. destruct boolP => //=.
case Hr: (r == 0).
  by rewrite (eqP Hr).
move/leRP: H.
rewrite /gtRb in i.
by rewrite le0R (negbTE i) orbF => /eqP ->.
Qed.

Lemma point_mkscaled r x H : @point (mkscaled r x) H = x.
Proof.
move: H; rewrite /point.
rewrite /mkscaled.
destruct boolP => //=.
by move/ltRR.
Qed.

Lemma Rpos_prob_Op1 (r q : Rpos) : 0 <= r / addRpos r q <= 1.
Proof.
split.
+ apply /ltRW /divR_gt0. by case: r => /= r /ltRP.
  by case: addRpos => /= x /ltRP.
+ apply leR_pdivr_mulr.
    by case: addRpos => /= x /ltRP.
  rewrite addRposE mul1R.
  apply /leR_addl /ltRW /ltRP.
  by case: q.
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
rewrite [in RHS]addRposC onem_div.
  by rewrite addRposE /= addRK.
by apply Rpos_neq0.
Qed.

Definition addpt a b :=
  match a, b with
  | Scaled r x, Scaled q y => Scaled (addRpos r q) (x <| Rpos_prob r q |> y)
  | Zero, _ => b
  | _, _ => a
  end.

Lemma addptC : commutative addpt.
Proof.
move=> [r x|] [q y|] //=.
rewrite addRposC; congr Scaled.
rewrite convC; congr Conv.
by rewrite [RHS]Rpos_probC.
Qed.

Lemma addptA : associative addpt.
Proof.
move=> [p x|] [q y|] [r z|] //=.
rewrite -addRposA; congr Scaled.
rewrite convA; congr Conv; last first.
  apply prob_ext => /=.
  rewrite s_of_pqE.
  rewrite -addRposA.
  rewrite Rpos_probC (@Rpos_probC r) /= !onemK.
  rewrite -(addRposC p) -(addRposC q).
  rewrite /Rdiv.
  rewrite mulRA mulRC !mulRA.
  rewrite mulVR; last by apply Rpos_neq0.
  rewrite mul1R mulRC onem_div; last by apply Rpos_neq0.
  by rewrite !addRposE /= !addRA addRK.
congr Conv.
apply prob_ext => /=.
rewrite r_of_pqE /=.
rewrite s_of_pqE Rpos_probC (Rpos_probC r) /= !onemK.
rewrite {3 4}/Rdiv !mulRA -(mulRC (/ addRpos r q)) !mulRA.
have Hpqr := Rpos_neq0 (addRpos (addRpos p q) r).
rewrite !addRposE /= in Hpqr.
rewrite (addRposC r) mulVR; last by apply Rpos_neq0.
rewrite mul1R -(mulRC r) -/(Rdiv r _) onem_div ?Rpos_neq0 //.
rewrite {3}/Rdiv divRM; last by apply /invR_neq0/eqP/Rpos_neq0.
  rewrite !addRposE /=.
  rewrite -(addRC p) addRA addRK invRK; last by apply /eqP.
  by rewrite /Rdiv mulRC (mulRC p) !mulRA mulRV // mul1R.
rewrite -addRposA (addRposC r) addRposA addRposE /= addRK.
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
Proof. move=> [p x|] [q y|] /=; by rewrite (add0R, addR0, addRposE). Qed.

Lemma weight0 : weight Zero = 0.
Proof. by []. Qed.

Lemma weight_bary pts : weight (barycenter pts) = \rsum_(x <- pts) weight x.
Proof. by rewrite (big_morph weight weight_addpt weight0). Qed.

Definition scalept_def p (x : scaled_pt) :=
  if x is Scaled q y then
    match boolP (p >b 0) with
    | AltTrue Hp => Scaled (mulRpos (mkRpos Hp) q) y
    | AltFalse _ => Zero
    end
  else Zero.

Definition scalept := locked scalept_def.

Lemma scalept_weight p x : 0 <= p -> weight (scalept p x) = p * weight x.
Proof.
case: x => [q y|] Hp.
  rewrite /scalept -lock /=.
  destruct boolP.
    rewrite /weight /=.
    rewrite /mulRpos -lock.
    by destruct q.
  move/leRP: Hp.
  rewrite /gtRb in i.
  rewrite le0R (negbTE i) orbF => /eqP ->.
  by rewrite mul0R.
by rewrite /= /scalept -lock mulR0.
Qed.

Lemma scalept_addpt r :
  0 <= r -> {morph scalept r : x y / addpt x y >-> addpt x y}.
Proof.
rewrite /scalept -lock.
move=> Hr [p x|] [q y|] //=.
destruct boolP => //=.
congr Scaled.
+ apply val_inj. rewrite !(mulRposE,addRposE) /=. by rewrite mulRDr.
+ congr Conv. apply prob_ext => /=.
  have Hr0 : r <> 0.
    move=> Hr0; move: i.
    by rewrite Hr0 => /ltRP /ltRR.
  rewrite !(mulRposE,addRposE) /= -mulRDr divRM //.
    by rewrite {2}/Rdiv -(mulRC (/r)) mulRA mulVR ?mul1R //; apply /eqP.
  have /= /eqP := (Rpos_neq0 (addRpos p q)).
  by rewrite addRposE.
by rewrite addpt0.
Qed.

Lemma scalept0 p : scalept p Zero = Zero.
Proof. by rewrite /scalept -lock. Qed.

Lemma scalept_bary p (H : 0 <= p) pts :
  scalept p (barycenter pts) = barycenter (map (scalept p) pts).
Proof.
rewrite (big_morph (scalept p) (scalept_addpt H) (scalept0 _)).
by rewrite /barycenter big_map.
Qed.

Lemma scalept_comp p q x :
  0 <= p -> 0 <= q -> scalept p (scalept q x) = scalept (p * q) x.
Proof.
move=> Hp Hq.
rewrite /scalept -lock.
case: x => [r x|] //=.
destruct boolP.
  destruct boolP => /=.
    destruct boolP.
      congr Scaled.
      by apply val_inj; rewrite !mulRposE /= mulRA.
    elimtype False.
    move/ltRP /pmulR_lgt0 in i0.
    rewrite /gtRb (introT (ltRP _ _) (i0 _)) // in i1.
    by apply /ltRP.
  destruct boolP => //.
  elimtype False.
  elim (negP i0).
  apply/ltRP/mulR_gt0/ltRP => //.
  by apply/ltRP.
destruct boolP => //.
elimtype False.
case/leR_eqVlt: Hq => Hq.
  rewrite -Hq mulR0 in i0.
  by move/ltRP/ltRR in i0.
by rewrite /gtRb (introT (ltRP _ _) Hq) in i.
Qed.

Lemma scalept_addR x : {morph scalept^~ x : p q / p + q >-> addpt p q}.
Proof.
move=> p q.
Abort.

Definition Rpos1 := @mkRpos 1 (introT (ltRP _ _) Rlt_0_1).

Lemma nonneg_nonpos_0 p : 0 <= p -> ~~ (p >b 0) -> p = 0.
Proof. by move/leRP; rewrite le0R /gtRb; case: eqP => //= _ ->. Qed.

Lemma scalept_addR p q x :
  0 <= p -> 0 <= q ->
  scalept (p + q) x = addpt (scalept p x) (scalept q x).
Proof.
move=> Hp Hq.
rewrite /scalept -lock /scalept_def.
destruct boolP.
  destruct boolP.
    destruct boolP.
      case: x => [r x|] //=.
      rewrite convmm; congr Scaled.
      apply val_inj; rewrite addRposE !mulRposE /=.
      by rewrite mulRDl.
    case: x => [r x|] //=.
    congr Scaled; apply val_inj; rewrite !mulRposE /=.
    by rewrite (nonneg_nonpos_0 Hq i1) addR0.
  destruct boolP.
    case: x => [r x|] //=.
    congr Scaled; apply val_inj; rewrite !mulRposE /=.
    by rewrite (nonneg_nonpos_0 Hp i0) add0R.
  elimtype False.
  rewrite (nonneg_nonpos_0 Hp i0) (nonneg_nonpos_0 Hq i1) addR0 in i.
  by move/ltRP/ltRR: i.
destruct boolP.
  elimtype False.
  move: i => /negP; elim.
  apply/ltRP/addR_gt0wl => //.
  by apply/ltRP.
destruct boolP.
  elimtype False.
  move: i => /negP; elim.
  by apply/ltRP/addR_gt0wr/ltRP.
by case: x.
Qed.

Lemma scalept_R0 x : scalept 0 x = Zero.
Proof.
case: x; rewrite /scalept -lock //=.
move=> r c; destruct boolP => //.
by elim (ltRR 0); apply /ltRP.
Qed.

Lemma big_scalept (B : finType) (F : B -> R+) x :
  \big[addpt/Zero]_(i : B) scalept (F i) x = scalept (\rsum_(i : B) (F i)) x.
Proof.
apply (@proj1 _ (0 <= \rsum_(i : B) F i)).
apply (big_ind2 (fun y q => y = scalept q x /\ 0 <= q)).
+ rewrite scalept_R0; split => //. apply leRR.
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

Lemma barycenter_reorder (pe : 'S_n) :
  \big[addpt/Zero]_(i < n) scalept (p i) (h i) =
  \big[addpt/Zero]_(i < n) scalept (p (pe i)) (h (pe i)).
Proof.
transitivity (barycenter [tuple scalept (p i) (h i) | i < n]).
  by rewrite /barycenter big_map big_filter.
transitivity
  (barycenter (map_tuple (fun i => scalept (p i) (h i)) (mktuple pe))).
  rewrite /barycenter.
  rewrite 3!big_map /=.
  apply eq_big_perm, uniq_perm_eq.
  + by rewrite -enumT enum_uniq.
    rewrite map_inj_in_uniq ?enum_uniq //.
  + by move=> x1 x2 _ _; apply perm_inj.
  rewrite -enumT.
  move=> i.
  rewrite mem_enum inE.
  symmetry.
  apply/mapP.
  exists (perm_inv pe i).
    by rewrite mem_enum inE.
  by rewrite permKV.
by rewrite /barycenter big_map big_map big_filter.
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
rewrite (eq_bigr _ (fun i _ => big_morph (scalept (p i)) (scalept_addpt (pos_f_ge0 p i)) (scalept0 _) _ _ _)).
rewrite exchange_big /=.
apply eq_bigr => j _.
rewrite (eq_bigr _ (fun i _ => scalept_comp _ (pos_f_ge0 p i) (pos_f_ge0 (q i) j))).
rewrite ConvDist.dE.
have HF : forall i, 0 <= p i * q i j.
  by move=> i; apply mulR_ge0; apply pos_f_ge0.
rewrite (eq_bigr (mkPosFun HF)) //.
by rewrite -big_scalept; apply eq_bigr.
Qed.
End convdist.

Section binary.
Variable B : finType.
Hypothesis HB : #|B| = 2%nat.
Variable points : B -> A.
Variable p : prob.
Variable b : B.
Let d := Binary.d HB p b.

Definition scaled_points :=
  [seq mkscaled (d i) (points i) | i <- enum B].
End binary.

Section adjunction.
Variables (n : nat) (points : 'I_n -> A).

Definition points_of_dist (d : {dist 'I_n}) :=
  [seq mkscaled (d i) (points i) | i <- enum 'I_n].

Lemma weight_gt0 d : weight (barycenter (points_of_dist d)) > 0.
rewrite weight_bary.
rewrite (_ : \rsum_(x <- _)  _ = 1).
  apply /Rlt_gt /Rlt_0_1.
rewrite big_map -(pmf1 d) big_filter.
apply eq_bigr => i _.
rewrite weight_mkscaled //.
by apply pos_f_ge0.
Qed.
End adjunction.

Lemma adjunction_n n (points : 'I_n -> A) d :
  barycenter (points_of_dist points d) = Scaled Rpos1 (Convn d points).
Proof.
elim: n points d => [|n IH] points d.
+ move: (pmf1 d).
  rewrite big_ord0 => /Rlt_not_eq; elim. apply Rlt_0_1.
+ rewrite /=.
  case: eqVneq => Hd.
    rewrite /barycenter.
    rewrite big_map (bigD1_seq ord0); first last.
      apply enum_uniq.
      apply mem_enum.
    rewrite Hd big1 /=.
      rewrite addptC /= /mkscaled.
      destruct boolP.
        congr Scaled.
        by apply val_inj.
      elim: (negP i).
      apply/ltRP/Rlt_0_1.
    move=> i Hi.
    have := pmf1 d.
    rewrite (bigD1 ord0) ?mem_enum // Hd /= addRC.
    move/(f_equal (fun x => x - 1)).
    rewrite addRK subRR /mkscaled => /prsumr_eq0P -> //.
      destruct boolP => //.
      by move/ltRP/ltRR: (i0).
    move=> a _; apply pos_f_ge0.
  set d' := DelDist.d Hd.
  set points' := fun i => points (DelDist.h ord0 i).
  rewrite /barycenter big_map (bigD1_seq ord0) ?enum_uniq ?mem_enum //=.
  case/boolP: (d ord0 == 0) => Hd0.
    rewrite (eqP Hd0) {1}/mkscaled.
    destruct boolP => /=. by move/ltRP/ltRR: (i).
    have -> : probdist d ord0 = `Pr 0.
      apply prob_ext => /=. by apply/eqP.
    rewrite conv0 -IH.
    rewrite -big_filter.
Abort.

End scaled_convex.

End ScaledConvexSpace.
