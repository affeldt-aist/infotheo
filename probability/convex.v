(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup perm finalg matrix.
From mathcomp Require Import boolp classical_sets.
Require Import Reals Lra ProofIrrelevance FunctionalExtensionality.
Require Import ssrR Reals_ext Ranalysis_ext ssr_ext ssralg_ext logb Rbigop.
Require Import proba.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "x <| p |> y" (format "x  <| p |>  y", at level 50).
Reserved Notation "{ 'convex_set' T }" (format "{ 'convex_set'  T }").
Reserved Notation "'\Conv_' d f" (at level 36, f at level 36, d at level 0,
  format "\Conv_ d  f").

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.

Section PR_to_classical_sets.

Variable T : Type.
Implicit Types A B C : set T.

Local Open Scope classical_set_scope.

Lemma set0U A : set0 `|` A = A.
Proof. rewrite funeqE => t; rewrite propeqE; split; by [case|right]. Qed.

Lemma setU0 A : A `|` set0 = A.
Proof. rewrite funeqE => t; rewrite propeqE; split; by [case|left]. Qed.

Lemma sub0set A : set0 `<=` A.
Proof. by []. Qed.

Lemma subset0 A : (A `<=` set0) = (A = set0).
Proof. rewrite propeqE; split => [?|-> //]; exact/eqEsubset. Qed.

Lemma subUset A B C : (B `|` C `<=` A) = ((B `<=` A) /\ (C `<=` A)).
Proof.
rewrite propeqE; split => [H|H]; first by split => x Hx; apply H; [left|right].
move=> x [] Hx; [exact: (proj1 H)|exact: (proj2 H)].
Qed.

Lemma setU_eq0 A B : (A `|` B = set0) = ((A = set0) /\ (B = set0)).
Proof. by rewrite -!subset0 subUset. Qed.

Lemma set0P A : (A != set0) <-> (A !=set0).
Proof.
split; [move=> A_neq0|by case=> t tA; apply/negP => /eqP A0; rewrite A0 in tA].
apply/existsp_asboolP; rewrite -(negbK `[exists _, _]); apply/negP.
rewrite existsbE => /forallp_asboolPn H.
move/negP : A_neq0; apply; apply/eqP; rewrite funeqE => t; rewrite propeqE.
move: (H t); by rewrite asboolE.
Qed.

End PR_to_classical_sets.

Section tmp.
Local Open Scope proba_scope.
Variables (n m : nat) (d1 : {dist 'I_n}) (d2 : {dist 'I_m}) (p : prob).
Lemma ConvDist_Add (A : finType) (g : 'I_n -> dist A) (h : 'I_m -> dist A) :
  ConvDist.d
    (AddDist.d d1 d2 p)
    [ffun i => match fintype.split i with inl a => g a | inr a => h a end] =
  Conv2Dist.d (ConvDist.d d1 g) (ConvDist.d d2 h) p.
Proof.
apply/dist_ext => a.
rewrite !Conv2Dist.dE !ConvDist.dE.
rewrite 2!big_distrr /= big_split_ord /=; congr (_ + _)%R;
  apply eq_bigr => i _; rewrite AddDist.dE ffunE.
case: splitP => /= j ij.
rewrite mulRA; congr (_ * d1 _ * (g _) a)%R; exact/val_inj.
move: (ltn_ord i); by rewrite ij -ltn_subRL subnn ltn0.
case: splitP => /= j ij.
move: (ltn_ord j); by rewrite -ij -ltn_subRL subnn ltn0.
move/eqP : ij; rewrite eqn_add2l => /eqP ij.
rewrite mulRA; congr (_ * d2 _ * (h _) a)%R; exact/val_inj.
Qed.
End tmp.

Section tmp2.
Variables (A : finType) (n : nat) (g : 'I_n.+1 -> dist A) (P : {dist 'I_n.+1}).
Lemma DelDistConvex (j : 'I_n.+1) (H : (0 <= P j <= 1)%R) (Pj1 : P j != 1%R) :
  let g' := fun i : 'I_n => g (DelDist.h j i) in
  ConvDist.d P g = Conv2Dist.d (g j) (ConvDist.d (DelDist.d Pj1) g') (Prob.mk H).
Proof.
move=> g' /=; apply/dist_ext => a.
rewrite Conv2Dist.dE /= ConvDist.dE (bigD1 j) //=; congr (_ + _)%R.
rewrite ConvDist.dE big_distrr /=.
rewrite (bigID (fun i : 'I_n.+1 => (i < j)%nat)) //= (bigID (fun i : 'I_n => (i < j)%nat)) //=; congr (_ + _)%R.
  rewrite (@big_ord_narrow_cond _ _ _ j n.+1); first by rewrite ltnW.
  move=> jn; rewrite (@big_ord_narrow_cond _ _ _ j n xpredT); first by rewrite -ltnS.
  move=> jn'.
  apply/eq_big.
  by move=> /= i; apply/negP => /eqP/(congr1 val) /=; apply/eqP; rewrite ltn_eqF.
  move=> /= i _.
  rewrite DelDist.dE /= /DelDist.h /= ltn_ord D1Dist.dE /= ifF /=; last first.
    by apply/negP => /eqP/(congr1 val) /=; apply/eqP; rewrite ltn_eqF.
  rewrite mulRA mulRCA mulRV ?mulR1 ?onem_neq0 //.
  congr (P _ * _)%R; first exact/val_inj.
  rewrite /g' /DelDist.h /= ltn_ord; congr (g _ a).
  exact/val_inj.
rewrite (eq_bigl (fun i : 'I_n.+1 => (j < i)%nat)); last first.
  move=> i; by rewrite -leqNgt eq_sym -ltn_neqAle.
rewrite (eq_bigl (fun i : 'I_n => (j <= i)%nat)); last first.
  move=> i; by rewrite -leqNgt.
rewrite big_mkcond.
rewrite big_ord_recl ltn0 /= add0R.
rewrite [in RHS]big_mkcond.
apply eq_bigr => i _.
rewrite /bump add1n ltnS; case: ifPn => // ji.
rewrite DelDist.dE D1Dist.dE /DelDist.h /= ltnNge ji /= ifF; last first.
  apply/eqP => /(congr1 val) => /=.
  rewrite /bump add1n => ij.
  move: ji; apply/negP; by rewrite -ij ltnn.
rewrite /Rdiv mulRAC [in RHS] mulRC -mulRA mulVR // ?mulR1 ?onem_neq0 //.
by rewrite /g' /DelDist.h ltnNge ji.
Qed.
End tmp2.

(* technical device *)
Module CodomDDist.
Section def.
Local Open Scope classical_set_scope.
Variables (A : Type) (n : nat) (g : 'I_n -> A) (e : {dist 'I_n}) (y : set A).
Definition f := [ffun i : 'I_n => if g i \in y then e i else 0%R].
Lemma f0 i : (0 <= f i)%R.
Proof. rewrite /f ffunE; case: ifPn => _; [exact/dist_ge0|exact/leRR]. Qed.
Lemma f1 (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, x (g i) -> e i = 0%R) :
  (\rsum_(i < n) f i = 1)%R.
Proof.
rewrite /f -(epmf1 e) /=.
apply eq_bigr => i _; rewrite ffunE.
case: ifPn => // /negP; rewrite in_setE => ygi.
rewrite ge //.
have : (x `|` y) (g i) by apply/gX; by exists i.
by case.
Qed.
Definition d (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, x (g i) -> e i = 0%R) : {dist 'I_n} :=
  locked (makeDist f0 (f1 gX ge)).
Lemma dE (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, x (g i) -> e i = 0%R) i :
  d gX ge i = if g i \in y then e i else 0%R.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
Lemma f1' (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, (x (g i)) /\ (~ y (g i)) -> e i = 0%R) :
  (\rsum_(i < n) f i = 1)%R.
Proof.
rewrite /f -(epmf1 e) /=.
apply eq_bigr => i _; rewrite ffunE.
case: ifPn => // /negP; rewrite in_setE => giy.
rewrite ge //.
have : (x `|` y) (g i) by apply/gX; by exists i.
by case.
Qed.
Definition d' (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, (x (g i)) /\ (~ y (g i)) -> e i = 0%R) :=
  locked (makeDist f0 (f1' gX ge)).
Lemma dE' (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, (x (g i)) /\ (~ y (g i)) -> e i = 0%R) i :
  d' gX ge i = if g i \in y then e i else 0%R.
Proof. by rewrite /d'; unlock; rewrite ffunE. Qed.
End def.
End CodomDDist.

Lemma r_of_pq_is_r (p q r s : prob) : r != `Pr 0 -> s != `Pr 0 ->
  p = (r * s)%R :> R -> s.~ = (p.~ * q.~)%R ->
  [r_of p, q] = r.
Proof.
move=> r0 s0 H1 H2.
apply prob_ext => /=.
rewrite r_of_pqE eqR_divr_mulr; last first.
  by rewrite s_of_pqE -H2 onemK.
rewrite (p_is_rs _ q) /=.
rewrite {1}s_of_pqE -H2 onemK.
rewrite r_of_pqE s_of_pqE.
rewrite -H2 onemK.
by rewrite /Rdiv -mulRA mulVR ?mulR1.
Qed.

Module ConvexSpace.
Record class_of (T : Type) : Type := Class {
  conv : T -> T -> prob -> T where "a <| p |> b" := (conv a b p);
  _ : forall a b, a <| `Pr 1 |> b = a ;
  _ : forall a p, a <| p |> a = a ;
  _ : forall a b p, a <| p |> b = b <| `Pr p.~ |> a;
  _ : forall (p q : prob) (a b c : T),
      a <| p |> (b <| q |> c) = (a <| [r_of p, q] |> b) <| [s_of p, q] |> c
}.
Structure t : Type := Pack { car : Type ; class : class_of car }.
Module Exports.
Definition Conv (T : t) : car T -> car T -> prob -> car T :=
  let: Pack _ (Class x _ _ _ _) := T in x.
Arguments Conv {T} : simpl never.
Notation "x <| p |> y" := (Conv x y p) : convex_scope.
Notation convType := t.
Coercion car : convType >-> Sortclass.
End Exports.
End ConvexSpace.
Export ConvexSpace.Exports.

Local Open Scope convex_scope.

Section convex_space_interface.
Variables A : convType.
Implicit Types a b c : A.
Implicit Types p q r s : prob.
Lemma conv1 a b : a <| `Pr 1 |> b = a.
Proof. by case: A a b => ? []. Qed.
Lemma convmm a p : a <| p |> a = a.
Proof. by case: A a => ? []. Qed.
Lemma convC a b p : a <| p |> b = b <| `Pr p.~ |> a.
Proof. by case: A a b => ? []. Qed.
Lemma convA p q a b c :
  a <| p |> (b <| q |> c) = (a <| [r_of p, q] |> b) <| [s_of p, q] |> c.
Proof.
case: A a b c p q => ? [] f H0 H1 H2 H3 d0 d1 d2 p q; by rewrite /Conv H3.
Qed.
End convex_space_interface.

Lemma prob_dist (A : finType) (d : dist A) (a : A) : (0 <= d a <= 1)%R.
Proof. split; [exact/dist_ge0 | exact/dist_max]. Qed.

Definition probdist (A : finType) (d : dist A) (a : A) := @Prob.mk (d a) (prob_dist d a).

Module ScaledConvex.
Section scaled_convex.
Variable A : convType.
Local Open Scope R_scope.
Local Open Scope convex_scope.

(* Note: we need the argument of Scaled to be an Rpos, because otherwise
   addpt cannot make a commutative monoid:
   1) if addpt (Scaled 0 x) (Scaled 0 y) = Scaled 0 x commutativity fails
      so at least we need addpt (Scaled 0 x) (Scaled 0 y) = Zero
   2) if addpt (Scaled 0 x) Zero = Zero then left/right identity fail
   2) if addpt (Scaled 0 x) Zero = Scaled 0 x then associativity fails
      addpt (Scaled 0 x) (addpt (Scaled 0 y) (Scaled 0 z)) = Scaled 0 x
      addpt (addpt (Scaled 0 x) (Scaled 0 y)) (Scaled 0 z) = Scaled 0 z
   So we cannot allow 0 as argument to Scaled.                             *)

Inductive scaled_pt := Scaled of Rpos & A | Zero.

Local Notation "a *: v" := (Scaled a v).

Definition S1 x := `Pos 1 *: x.

Lemma Scaled_inj p : injective (Scaled p).
Proof. by move=> x y []. Qed.

Definition S1_inj : injective S1 := @Scaled_inj Rpos1.

Definition raw_weight pt : R :=
  if pt is r *: _ then r else 0.

Lemma weight_ge0 pt : 0 <= raw_weight pt.
Proof. case: pt => /= [[x] /= /ltRP/ltRW //|]; by apply leRR. Qed.

Definition weight := mkPosFun weight_ge0.

Definition point pt : weight pt > 0 -> A.
destruct pt.
+ move=> _; exact c.
+ case/ltRR.
Defined.

Lemma point_Scaled p x H : @point (p *: x) H = x.
Proof. by []. Qed.

Lemma Scaled_point x H : mkRpos H *: @point x H = x.
Proof.
case: x H => [p x|] H; by [congr Scaled; apply val_inj | elim: (ltRR 0)].
Qed.

Lemma weight0_Zero x : weight x = 0 -> x = Zero.
Proof. case: x => //= r c /esym Hr; by move/ltR_eqF: (Rpos_gt0 r). Qed.

Lemma Rpos_prob_Op1 (r q : Rpos) : 0 <= r / `Pos (r + q) <= 1.
Proof.
split.
+ apply /ltRW /divR_gt0; by apply /Rpos_gt0.
+ apply leR_pdivr_mulr.
    by apply /Rpos_gt0.
  rewrite mul1R.
  by apply /leR_addl /ltRW /Rpos_gt0.
Qed.
Definition Rpos_prob (r q : Rpos) :=
  @Prob.mk (r / `Pos (r + q)) (Rpos_prob_Op1 _ _).

Lemma onem_div p q : q != 0 -> (p/q).~ = (q-p)/q.
Proof.
move=> Hq.
by rewrite /onem -(divRR q) // /Rdiv /Rminus -mulNR -mulRDl.
Qed.

Lemma Rpos_probC r q : Rpos_prob q r = `Pr (Rpos_prob r q).~.
Proof.
apply prob_ext => /=.
rewrite [in RHS]addRC onem_div.
  by rewrite /= addRK.
by apply Rpos_neq0.
Qed.

(* scaled_pt associated with the following operations define
   a real cone [Varacca & Winskell, MSCS, 2006]
   In the following we annotate the lemmas with the corresponding
   axiom in definition 2.1 [VW] (the numbers are 1-7 and 13)  *)

Definition addpt a b :=
  match a, b with
  | r *: x, q *: y => `Pos (r + q) *: (x <| `Pr (`Pos (r / (r + q))) |> y)
  | _, Zero => a
  | Zero, _ => b
  end.

Definition scalept p (x : scaled_pt) :=
  match Rlt_dec 0 p, x with
  | left Hr, q *: y => `Pos (mkRpos Hr * q) *: y
  | _, _ => Zero
  end.

Lemma onem_divRxxy (r q : Rpos) : (r / (r + q)).~ = q / (q + r).
Proof.
rewrite /onem subR_eq (addRC r) -mulRDl mulRV //.
exact/eqP/gtR_eqF/ltRP/addRpos_gt0.
Qed.

(* 1 *)
Lemma addptC : commutative addpt.
Proof.
move=> [r x|] [q y|] //=.
congr Scaled. by apply val_inj; rewrite /= addRC.
rewrite convC; congr Conv; exact/prob_ext/onem_divRxxy.
Qed.

Lemma s_of_Rpos_probA (p q r : Rpos) :
  [s_of `Pr `Pos (p / (p + (q + r))), `Pr `Pos (q / (q + r))] = `Pr `Pos ((p + q) / (p + q + r)).
(*  [s_of Rpos_prob p (`Pos (q + r)), Rpos_prob q r] = Rpos_prob (`Pos (p + q)) r.*)
Proof.
apply prob_ext => /=; rewrite s_of_pqE /onem /=; field.
split; exact/eqP/Rpos_neq0.
Qed.

Lemma r_of_Rpos_probA (p q r : Rpos) :
  [r_of `Pr `Pos (p / (p + (q + r))), `Pr `Pos (q / (q + r))] = `Pr `Pos (p / (p + q)).
(*  [r_of Rpos_prob p (`Pos (q + r)), Rpos_prob q r] = Rpos_prob p q.*)
Proof.
apply/prob_ext => /=; rewrite r_of_pqE s_of_pqE /onem /=; field.
do 3 (split; first exact/eqP/Rpos_neq0).
rewrite (addRC p (q + r)) addRK {4}[in q + r]addRC addRK.
rewrite mulRC -mulRBr (addRC _ p) addRA addRK mulR_neq0.
split; exact/eqP/Rpos_neq0.
Qed.

(* 2 *)
Lemma addptA : associative addpt.
Proof.
move=> [p x|] [q y|] [r z|] //=.
congr Scaled. by apply val_inj; rewrite /= addRA.
rewrite convA; congr Conv; last exact: s_of_Rpos_probA.
congr Conv; exact: r_of_Rpos_probA.
Qed.

(* 3 *)
Lemma addpt0 x : addpt x Zero = x.
Proof. by case: x. Qed.

(* 3' *)
Lemma add0pt x : addpt Zero x = x.
Proof. by case: x. Qed.

Canonical addpt_monoid := Monoid.Law addptA add0pt addpt0.
Canonical addpt_comoid := Monoid.ComLaw addptC.

Lemma weight_addpt : {morph weight : x y / addpt x y >-> x + y}.
Proof. move=> [p x|] [q y|] //=; by rewrite (add0R, addR0). Qed.

Lemma weight0 : weight Zero = 0.
Proof. by []. Qed.

Lemma scaleptR0 p : scalept p Zero = Zero.
Proof. by rewrite /scalept; case: Rlt_dec. Qed.

Lemma scalept_gt0 p (q : Rpos) x (H : 0 < p) :
  scalept p (q *: x) = `Pos (mkRpos H * q) *: x.
Proof.
rewrite /scalept; case: Rlt_dec => // Hr.
congr Scaled; by apply val_inj.
Qed.

(* 4 *)
Lemma scalept0 x : scalept 0 x = Zero.
Proof. rewrite /scalept; case: Rlt_dec => // Hr; by elim (ltRR 0). Qed.

(* 5 *)
Lemma scalept1 x : scalept 1 x = x.
Proof.
case: x => [r c|]; rewrite ?scaleptR0 // scalept_gt0.
congr Scaled; apply val_inj; by rewrite /= mul1R.
Qed.

Lemma scalept_Scaled p q x : scalept p (q *: x) = scalept (p*q) (S1 x).
Proof.
rewrite /scalept.
case: Rlt_dec => Hp; case: Rlt_dec => Hpq //.
- congr Scaled; apply val_inj; by rewrite /= mulR1.
- elim Hpq; by apply /mulR_gt0 /Rpos_gt0.
- elim Hp; move/pmulR_lgt0: Hpq; apply; apply Rpos_gt0.
Qed.

Lemma scalept_weight p x : 0 <= p -> weight (scalept p x) = p * weight x.
Proof.
case=> Hp; last by rewrite -Hp scalept0 mul0R.
case: x => [r y|]; by [rewrite scalept_gt0 | rewrite scaleptR0 mulR0].
Qed.

(* 6 *)
Lemma scalept_addpt r : {morph scalept r : x y / addpt x y >-> addpt x y}.
Proof.
rewrite /scalept; case: Rlt_dec => // Hr x y.
case: x => [p x|]; last by rewrite !add0pt.
case: y => [q y|]; last by rewrite !addpt0.
congr Scaled. by apply val_inj => /=; rewrite mulRDr.
have Hr0 : r <> 0 by apply gtR_eqF.
congr Conv; apply prob_ext; rewrite /= -mulRDr divRM //.
  rewrite /Rdiv -(mulRAC r) mulRV ?mul1R //; by apply /eqP.
by apply/eqP/Rpos_neq0.
Qed.

Definition big_scalept q :=
  big_morph (scalept q) (scalept_addpt q) (scaleptR0 _).

(* 7 *)
Lemma scalept_comp p q x :
  0 <= p -> 0 <= q -> scalept p (scalept q x) = scalept (p * q) x.
Proof.
case=> Hp; last by rewrite -Hp mul0R !scalept0.
case=> Hq; last by rewrite -Hq mulR0 scalept0 scaleptR0.
case: x => [r x|]; rewrite ?scaleptR0 // !scalept_gt0; first by apply mulR_gt0.
move=> Hpq; congr Scaled; apply val_inj => /=; by rewrite mulRA.
Qed.

(* 13 *)
Lemma scalept_addR p q x :
  0 <= p -> 0 <= q ->
  scalept (p + q) x = addpt (scalept p x) (scalept q x).
Proof.
case=> Hp; last by rewrite -Hp scalept0 add0R add0pt.
case=> Hq; last by rewrite -Hq scalept0 addR0 addpt0.
case: x => [r c|]; last by rewrite !scaleptR0.
rewrite !scalept_gt0 => [|Hpq /=]; first by apply addR_gt0.
rewrite convmm; congr Scaled; apply val_inj; by rewrite /= mulRDl.
Qed.

Lemma scalept_rsum (B : finType) (F : B -> R+) x :
  scalept (\rsum_(i : B) (F i)) x = \big[addpt/Zero]_(i : B) scalept (F i) x.
Proof.
apply (@proj1 _ (0 <= \rsum_(i : B) F i)).
apply (big_ind2 (fun y q => scalept q x = y /\ 0 <= q)).
+ rewrite scalept0; split => //. apply leRR.
+ move=> x1 x2 y1 y2 [Hx1 Hx2] [Hy1 Hy2].
  split. by rewrite -Hx1 -Hy1 scalept_addR.
  by apply addR_ge0.
+ move=> i _; split => //.
  by apply pos_f_ge0.
Qed.

Definition scaled_conv x y (p : prob) := addpt (scalept p x) (scalept p.~ y).
Definition Scaled_convMixin : ConvexSpace.class_of scaled_pt.
apply (@ConvexSpace.Class _ scaled_conv); rewrite /scaled_conv /=.
+ by move=> a b; rewrite onem1 scalept1 scalept0 addpt0.
+ move=> a p; rewrite -scalept_addR; try apply prob_ge0.
  by rewrite onemKC scalept1.
+ move=> a b p; by rewrite [RHS]addptC onemK.
+ move=> p q a b c.
  rewrite !scalept_addpt ?scalept_comp; try apply prob_ge0.
  rewrite -[RHS]addptA; congr addpt.
    by rewrite (p_is_rs p q) mulRC.
  by rewrite pq_is_rs mulRC s_of_pqE onemK.
Defined.
Canonical Scaled_convType := ConvexSpace.Pack Scaled_convMixin.

Definition barycenter (pts : seq scaled_pt) :=
  \big[addpt/Zero]_(x <- pts) x.

Lemma barycenter_big_fin (T : finType) (F : T -> scaled_pt) :
  barycenter [seq F i | i <- enum T] = \big[addpt/Zero]_i F i.
Proof. by rewrite /barycenter big_map big_filter. Qed.

Lemma weight_bary pts : weight (barycenter pts) = \rsum_(x <- pts) weight x.
Proof. by rewrite (big_morph weight weight_addpt weight0). Qed.

Lemma scalept_bary p (H : 0 <= p) pts :
  scalept p (barycenter pts) = barycenter (map (scalept p) pts).
Proof. by rewrite big_scalept /barycenter big_map. Qed.

Lemma barycenter_perm n (F : 'I_n -> scaled_pt) (pe : 'S_n) :
  \big[addpt/Zero]_(i < n) F i = \big[addpt/Zero]_(i < n) F (pe i).
Proof.
rewrite -!barycenter_big_fin /barycenter big_map map_comp big_map.
exact/perm_big/perm_eq_perm.
Qed.

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
rewrite (eq_bigr _ (fun i _ => big_scalept (p i) _ _ _)).
rewrite exchange_big /=; apply eq_bigr => j _.
rewrite ConvDist.dE.
have HF : forall i, 0 <= p i * q i j by move=> i; apply/mulR_ge0; apply/dist_ge0.
rewrite (scalept_rsum (mkPosFun HF)) /=; apply eq_bigr => i _.
rewrite scalept_comp //; exact/dist_ge0.
Qed.
End convdist.

Section adjunction.
Variable p : prob.

Lemma adjunction_1 a b :
  addpt (scalept 1 (S1 a)) (scalept 0 (S1 b)) = S1 (a <|`Pr 1|> b).
Proof. by rewrite scalept0 scalept1 addpt0 conv1. Qed.

Lemma adjunction_2 x y :
  addpt (scalept p (S1 x)) (scalept p.~ (S1 y)) = S1 (x <| p |> y).
Proof.
case/prob_ge0: p => Hp; last first.
  rewrite -Hp /= convC addptC onem0 adjunction_1.
  by congr (_ (_ <|_|> _)); apply prob_ext; rewrite /= -Hp onem0.
case/prob_le1: p => Hp1; last first.
  rewrite Hp1 /= onem1 adjunction_1.
  by congr (_ (_ <|_|> _)); apply prob_ext; rewrite /= Hp1.
rewrite (scalept_gt0 _ _ Hp) (@scalept_gt0 p.~) => [|H].
   by rewrite ltR_subRL addR0.
congr Scaled.
  apply val_inj; by rewrite /= !mulR1 onemKC.
congr Conv; apply prob_ext => /=.
by rewrite !mulR1 /= addRC subRK divR1.
Qed.

Lemma S1_conv : {morph S1 : a b / a <|p|> b >-> a <|p|> b}.
Proof. move=> a b. by rewrite -adjunction_2. Qed.
End adjunction.

End scaled_convex.
End ScaledConvex.
Local Notation "a *: v" := (@ScaledConvex.Scaled _ a v).

Section convex_space_prop.
Variables A : convType.
Implicit Types a b : A.
Lemma conv0 a b : a <| `Pr 0 |> b = b.
Proof.
rewrite convC (_ : `Pr _ = `Pr 1) ?conv1 //=; apply prob_ext; exact: onem0.
Qed.

Lemma convA0 (p q r s : prob) a b c :
  p = (r * s)%R :> R -> (s.~ = p.~ * q.~)%R ->
  a <| p |> (b <| q |> c) = (a <| r |> b) <| s |> c.
Proof.
move=> H1 H2.
case/boolP : (r == `Pr 0) => r0.
  rewrite (eqP r0) conv0 (_ : p = `Pr 0) ?conv0; last first.
    by apply/prob_ext; rewrite H1 (eqP r0) mul0R.
  congr (_ <| _ |> _); move: H2; rewrite H1 (eqP r0) mul0R onem0 mul1R.
  move/(congr1 onem); rewrite !onemK => ?; exact/prob_ext.
case/boolP : (s == `Pr 0) => s0.
  have p0 : p = `Pr 0 by apply/prob_ext; rewrite H1 (eqP s0) mulR0.
  rewrite (eqP s0) conv0 p0 // ?conv0.
  rewrite (_ : q = `Pr 0) ?conv0 //.
  move: H2; rewrite p0 onem0 mul1R => /(congr1 onem); rewrite !onemK => sq.
  rewrite -(eqP s0); exact/prob_ext.
rewrite convA; congr ((_ <| _ |> _) <| _ |> _).
  by rewrite (@r_of_pq_is_r  _ _ r s).
apply prob_ext => /=; by rewrite s_of_pqE -H2 onemK.
Qed.

Lemma convA' (r s : prob) a b c : [p_of r, s] != `Pr 1 ->
  a <| [p_of r, s] |> (b <| [q_of r, s] |> c) = (a <| r |> b) <| s |> c.
Proof.
move=> H; case/boolP : (s == `Pr 0) => s0.
- by rewrite (eqP s0) p_of_r0 conv0 q_of_r0 conv0 conv0.
- by rewrite convA s_of_pqK // r_of_pqK.
Qed.

Import ScaledConvex.

Lemma commute (x1 y1 x2 y2 : A) p q :
  (x1 <|q|> y1) <|p|> (x2 <|q|> y2) = (x1 <|p|> x2) <|q|> (y1 <|p|> y2).
Proof.
apply S1_inj; rewrite ![in LHS]S1_conv [LHS]/Conv /= /scaled_conv.
rewrite !scalept_addpt ?scalept_comp; try apply prob_ge0.
rewrite !(mulRC p) !(mulRC p.~) addptA addptC (addptC (scalept (q*p) _)).
rewrite !addptA -addptA -!scalept_comp -?scalept_addpt; try apply prob_ge0.
by rewrite !(addptC (scalept _.~ _)) !S1_conv.
Qed.

Lemma distribute (x y z : A) (p q : prob) :
  x <| p |> (y <| q |> z) = (x <| p |> y) <| q |> (x <| p |> z).
Proof. by rewrite -{1}(convmm x q) commute. Qed.

Local Open Scope vec_ext_scope.

Fixpoint Convn n : {dist 'I_n} -> ('I_n -> A) -> A :=
  match n return forall (e : {dist 'I_n}) (g : 'I_n -> A), A with
  | O => fun e g => False_rect A (distI0_False e)
  | m.+1 => fun e g =>
    match eqVneq (e ord0) 1%R with
    | left _ => g ord0
    | right H => let G := fun i => g (DelDist.h ord0 i) in
      g ord0 <| probdist e ord0 |> Convn (DelDist.d H) G
    end
  end.

Local Notation "'\Conv_' d f" := (Convn d f).

Section with_affine_projection.
Variable B : convType.
Variable prj : A -> B.
Hypothesis prj_affine : forall p, {morph prj : x y / x <|p|> y >-> x <|p|> y}.

Definition map_scaled (x : scaled_pt A) :=
  if x is p *: a then p *: prj a else @Zero B.

Lemma map_scaled_affine p :
  {morph map_scaled : x y / x <|p|> y >-> x <|p|> y}.
Proof.
move=> [q x|] [r y|] /=; rewrite /Conv /= /scaled_conv ?scaleptR0 //.
+ rewrite !(scalept_Scaled p) !(scalept_Scaled p.~) /= /scalept.
  case: Rlt_dec => Hpq; case: Rlt_dec => Hpr //=; congr Scaled.
  by rewrite prj_affine.
+ rewrite !addpt0 !(scalept_Scaled p) /= /scalept; by case: Rlt_dec.
+ rewrite !add0pt !(scalept_Scaled p.~) /= /scalept; by case: Rlt_dec.
Qed.

Lemma S1_convn_proj n (points : 'I_n -> A) d :
  S1 (prj (\Conv_d points)) =
  \big[@addpt B/Zero B]_(i < n) scalept (d i) (S1 (prj (points i))).
Proof.
elim: n points d => [|n IH] points d.
  move: (epmf1 d).
  rewrite /= big_ord0 => /Rlt_not_eq; elim.
  exact: Rlt_0_1.
rewrite /=.
case: eqVneq => Hd.
  rewrite (bigD1 ord0) ?inE // Hd big1 /=.
    rewrite addpt0 (scalept_gt0 _ _ Rlt_0_1).
    by congr Scaled; apply val_inj; rewrite /= mulR1.
  move=> i Hi; have := epmf1 d.
  rewrite (bigD1 ord0) ?inE // Hd /= addRC => /(f_equal (Rminus^~ R1)).
  rewrite addRK subRR => /prsumr_eq0P -> //.
    by rewrite scalept0.
  by move=> a _; exact/dist_ge0.
set d' := DelDist.d Hd.
set points' := fun i => points (DelDist.h ord0 i).
rewrite /index_enum -enumT (bigD1_seq ord0) ?enum_uniq ?mem_enum //=.
rewrite -big_filter (perm_big (map (lift ord0) (enum 'I_n)));
  last by apply perm_filter_enum_ord.
rewrite prj_affine S1_conv; congr addpt.
rewrite IH -barycenter_big_fin scalept_bary; last by apply prob_ge0.
rewrite /barycenter 2!big_map [in RHS]big_map.
apply eq_bigr => i _.
rewrite scalept_comp; [|by apply prob_ge0|exact/dist_ge0].
rewrite DelDist.dE D1Dist.dE /=.
rewrite /Rdiv (mulRC (d _)) mulRA mulRV ?mul1R //.
by move: (Hd); apply contra => /eqP Hd'; rewrite -onem0 -Hd' onemK.
Qed.
End with_affine_projection.

Lemma S1_convn n (points : 'I_n -> A) d :
  S1 (\Conv_d points) =
  \big[@addpt A/Zero A]_(i < n) scalept (d i) (S1 (points i)).
Proof. by rewrite (@S1_convn_proj _ (@id A)). Qed.

Lemma eq_convn n g1 g2 (d1 d2 : {dist 'I_n}) :
  g1 =1 g2 -> d1 =1 d2 -> \Conv_d1 g1 = \Conv_d2 g2.
Proof.
move=> Hg Hd; apply S1_inj; rewrite !S1_convn.
apply congr_big => // i _; by rewrite Hg Hd.
Qed.

Lemma convn_proj n g (d : {dist 'I_n}) i : d i = R1 -> \Conv_d g = g i.
Proof.
move=> Hd; apply S1_inj.
rewrite S1_convn (bigD1 i) ?inE //=.
rewrite big1; first by rewrite addpt0 Hd scalept1.
move=> j Hj.
move/eqP/Dist1.dist1P: Hd => -> //; by rewrite scalept0.
Qed.

Lemma ConvnDist1 (n : nat) (j : 'I_n) (g : 'I_n -> A): \Conv_(Dist1.d j) g = g j.
Proof. by apply convn_proj; rewrite Dist1.dE eqxx. Qed.

Lemma convn1E g (e : {dist 'I_1}) : \Conv_ e g = g ord0.
Proof.
rewrite /=; case: eqVneq => [//|H]; exfalso; move/eqP: H; apply.
by apply/eqP; rewrite Dist1.one (Dist1.I1 e).
Qed.

Lemma convnE n g (d : {dist 'I_n.+1}) (i1 : d ord0 != 1%R) :
  \Conv_d g = g ord0 <| probdist d ord0 |> \Conv_(DelDist.d i1) (fun x => g (DelDist.h ord0 x)).
Proof.
rewrite /=; case: eqVneq => /= H.
exfalso; by rewrite H eqxx in i1.
by rewrite (eq_irrelevance H i1).
Qed.

Lemma convn2E g (d : {dist 'I_2}) :
  \Conv_d g = g ord0 <| probdist d ord0 |> g (lift ord0 ord0).
Proof.
case/boolP : (d ord0 == 1%R) => [|i1].
  rewrite Dist1.one => /eqP ->; rewrite ConvnDist1.
  rewrite (_ : probdist _ _ = `Pr 1) ?conv1 //.
  by apply prob_ext => /=; rewrite Dist1.dE eqxx.
rewrite convnE; congr (_ <| _ |> _).
by rewrite convn1E /DelDist.h ltnn.
Qed.

(* ref: M.H.Stone, postulates for the barycentric calculus, lemma 2 *)
Lemma Convn_perm (n : nat) (d : {dist 'I_n}) (g : 'I_n -> A) (s : 'S_n) :
  \Conv_d g = \Conv_(PermDist.d d s) (g \o s).
Proof.
apply S1_inj; rewrite !S1_convn (barycenter_perm _ s).
apply eq_bigr => i _; by rewrite PermDist.dE.
Qed.

(* ref: M.H.Stone, postulates for the barycentric calculus, lemma 4 *)
Theorem Convn_convdist (n m : nat) (d : {dist 'I_n})
        (e : 'I_n -> {dist 'I_m}) (x : 'I_m -> A) :
  \Conv_d (fun i => \Conv_(e i) x) = \Conv_(ConvDist.d d e) x.
Proof.
apply S1_inj; rewrite !S1_convn -barycenter_convdist.
apply eq_bigr => i _; by rewrite S1_convn.
Qed.
End convex_space_prop.

Notation "'\Conv_' d f" := (Convn d f) : convex_scope.

Section is_convex_set.
Local Open Scope classical_set_scope.
Variable A : convType.

Definition is_convex_set (D : set A) : bool :=
  `[<forall x y t, x \in D -> y \in D -> x <| t |> y \in D>].

Lemma is_convex_set0 : is_convex_set set0.
Proof. apply/asboolP => x y p; by rewrite in_setE. Qed.

Lemma is_convex_set1 a : is_convex_set [set a].
Proof.
apply/asboolP => x y p; rewrite 2!in_setE /= => -> ->.
by rewrite convmm in_setE.
Qed.

Lemma is_convex_setT : is_convex_set setT.
Proof. apply/asboolP => ? ? ? _ _; by rewrite in_setE. Qed.

Definition is_convex_set_n (X : set A) : bool :=
  `[< forall n (g : 'I_n -> A) (d : {dist 'I_n}), g @` setT `<=` X -> \Conv_d g \in X >].

Lemma is_convex_setP (X : set A) : is_convex_set X = is_convex_set_n X.
Proof.
apply/idP/idP => H; apply/asboolP; last first.
  move=> x y p xX yX.
  case/boolP : (p == `Pr 1) => [/eqP ->|p1]; first by rewrite conv1.
  set g : 'I_2 -> A := fun i => if i == ord0 then x else y.
  have gX : g @` setT `<=` X by move=> a -[i _ <-]; rewrite -in_setE /g; case: ifPn.
  move/asboolP : H => /(_ _ g (I2Dist.d p) gX).
  rewrite convnE; first by rewrite I2Dist.dE eqxx.
  move=> p1'.
  rewrite {1}/g eqxx (_ : probdist _ _ = p); last first.
    by apply prob_ext => /=; rewrite I2Dist.dE eqxx.
  by rewrite (_ : \Conv_ _ _ = y) // (_ : (fun _ => _) = (fun=> y)) ?convn1E.
elim => [g d|n IH g d]; first by move: (distI0_False d).
destruct n as [|n] => gX.
  rewrite {IH} (@convn_proj _ _ _ _ ord0) //.
  rewrite in_setE; exact/gX/classical_sets.imageP.
  by apply/eqP; rewrite Dist1.one (Dist1.I1 d).
case/boolP : (d ord0 == 1%R) => [/eqP|]d01.
  suff -> : \Conv_d g = g ord0 by rewrite in_setE; apply gX; exists ord0.
  by rewrite (@convn_proj _ _ _ _ ord0).
set D : {dist 'I_n.+1} := DelDist.d d01.
pose G (i : 'I_n.+1) : A := g (DelDist.h (@ord0 _) i).
have : G @` setT `<=` X.
  by move=> x -[i _ <-{x}]; rewrite /G /DelDist.h ltn0; apply gX; exists ((lift ord0 i)).
move/(IH _ D) => {IH}IH.
rewrite convnE //.
move/asboolP : H; apply => //.
rewrite in_setE; exact/gX/classical_sets.imageP.
Qed.
End is_convex_set.

Section hull_def.
Local Open Scope classical_set_scope.
Definition hull (T : convType) (X : set T) : set T :=
  [set p : T | exists n (g : 'I_n -> T) d, g @` setT `<=` X /\ p = \Conv_d g].
End hull_def.

Section hull_prop.
Variable A : convType.
Lemma hull_mem (X : set A) x : x \in X -> x \in hull X.
Proof.
move=> xX.
rewrite in_setE /hull.
exists 1, (fun=> x), (Dist1.d ord0); split; last by rewrite convn1E.
move=> d -[i _ <-]; by rewrite -in_setE.
Qed.
Lemma hull0 : hull set0 = set0 :> set A.
Proof.
rewrite funeqE => d; rewrite propeqE; split => //.
case=> n [g [e [gX ->{d}]]].
destruct n as [|n].
  by move: (distI0_False e).
exfalso; apply: (gX (g ord0)); exact/imageP.
Qed.
Lemma hull_eq0 (X : set A) : (hull X == set0) = (X == set0).
Proof.
apply/idP/idP=> [/eqP abs|]; last by move=> /eqP ->; rewrite hull0.
apply/negPn/negP => /set0P[/= d]; rewrite -in_setE => dX.
move: abs; rewrite funeqE => /(_ d); rewrite propeqE /set0 => -[H _]; apply H.
by rewrite -in_setE; apply: hull_mem.
Qed.
Lemma mem_hull_setU (x y : set A) (a0 a1 : A) p :
  a0 \in x -> a1 \in y -> a0 <| p |> a1 \in hull (x `|` y).
Proof.
rewrite 3!in_setE => a0x a1y.
exists 2, (fun i => if i == ord0 then a0 else a1), (I2Dist.d p); split => /=.
  move=> a2.
  case => i _ <-{a2} /=.
  case: ifPn => _; [by left | by right].
case: eqVneq => [|H].
  rewrite I2Dist.dE eqxx /= => p1.
  suff -> : p = `Pr 1 by rewrite conv1.
  exact/prob_ext.
congr (_ <| _ |> _); last by apply prob_ext => /=; rewrite I2Dist.dE eqxx.
case: eqVneq => H' //.
exfalso.
move: H'; rewrite DelDist.dE D1Dist.dE /DelDist.h ltnn.
have lift0' : lift ord0 ord0 != ord0 :> 'I_2.
  by apply/eqP => /(congr1 val) /=; rewrite /bump leq0n.
rewrite (negbTE lift0') I2Dist.dE (negbTE lift0') I2Dist.dE eqxx divRR ?eqxx //.
by move: H; rewrite I2Dist.dE eqxx onem_neq0.
Qed.
Lemma mem_hull_setU_left (x y : set A) (a : A) : a \in x -> a \in hull (x `|` y).
Proof. by rewrite in_setE=> ax; apply: hull_mem; rewrite in_setE; left. Qed.

End hull_prop.

Module CSet.
Section def.
Local Open Scope classical_set_scope.
Variable A : convType.
Record t : Type := mk {
  car :> set A ;
  H : is_convex_set car }.
End def.
End CSet.
Notation convex_set := CSet.t.
Coercion CSet.car : convex_set >-> set.

Definition convex_set_of (A : convType) :=
  fun phT : phant (ConvexSpace.car A) => convex_set A.
Notation "{ 'convex_set' T }" := (convex_set_of (Phant T)) : convex_scope.

Section cset_canonical.
Variable (A : convType).
Canonical cset_subType := [subType for @CSet.car A].
Canonical cset_predType :=
  Eval hnf in PredType (fun t : convex_set A => (fun x => x \in CSet.car t)).
Definition cset_eqMixin := Eval hnf in [eqMixin of convex_set A by <:].
Canonical cset_eqType := Eval hnf in EqType (convex_set A) cset_eqMixin.
End cset_canonical.

Section CSet_prop.
Local Open Scope classical_set_scope.
Variable A : convType.

Lemma mem_convex_set (x y : A) (p : prob) (X : {convex_set A}) :
  x \in X -> y \in X -> x <|p|> y \in X.
Proof.
case: X => X convX; move: (convX) => convX_save.
move/asboolP : convX => convX Hx Hy; exact: convX.
Qed.

Definition cset0 : {convex_set A} := CSet.mk (is_convex_set0 A).

Lemma cset0P (x : {convex_set A}) : (x == cset0) = (x == set0 :> set _).
Proof. by case: x. Qed.

Lemma cset0PN (x : {convex_set A}) : (x != cset0) <-> (x !=set0).
Proof.
rewrite cset0P; case: x => //= x Hx; split; last first.
  case=> a xa; apply/eqP => x0; move: xa; by rewrite x0.
by case/set0P => /= d dx; exists d.
Qed.

Definition cset1 (x : A) : {convex_set A} := CSet.mk (is_convex_set1 x).

Lemma cset1_neq0 (x : A) : cset1 x != cset0.
Proof. apply/cset0PN; by exists x. Qed.

Lemma hull_cset (x : {convex_set A}) : hull x = x.
Proof.
rewrite predeqE => d; split.
- move=> -[n [g [e [gX ->{d}]]]].
  move: (CSet.H x); rewrite is_convex_setP /is_convex_set_n => /asboolP/(_ _ g e gX).
  by rewrite in_setE.
- by rewrite -in_setE => /hull_mem; rewrite in_setE.
Qed.

Import ScaledConvex.
Definition scaled_set (D : set A) :=
  [set x | if x is p *: a then a \in D else True].

Lemma addpt_scaled_set (D : {convex_set A}) x y :
  x \in scaled_set D -> y \in scaled_set D -> addpt x y \in scaled_set D.
Proof.
case: x => [p x|]; case: y => [q y|] //=; rewrite !in_setE /scaled_set.
move/CSet.H/asboolP: (D); apply.
Qed.

Lemma scalept_scaled_set (D : {convex_set A}) r x :
  x \in scaled_set D -> scalept r x \in scaled_set D.
Proof.
rewrite /scalept; case: Rlt_dec => //= Hr; by [case: x | rewrite !in_setE].
Qed.

Lemma scaled_set_extract (D : {convex_set A}) x (H : (0 < weight _ x)%R) :
  x \in scaled_set D -> point H \in CSet.car D.
Proof. case: x H => [p x|/ltRR] //=; by rewrite in_setE. Qed.

Lemma split_lshift n m (i : 'I_n) : fintype.split (lshift m i) = inl i.
Proof. by rewrite -/(unsplit (inl i)) unsplitK. Qed.
Lemma split_rshift n m (i : 'I_m) : fintype.split (rshift n i) = inr i.
Proof. by rewrite -/(unsplit (inr i)) unsplitK. Qed.

Lemma AddDist_conv n m p (g : 'I_(n+m) -> A)(d : {dist 'I_n})(e : {dist 'I_m}) :
  \Conv_(AddDist.d d e p) g =
  \Conv_d (g \o @lshift n m) <|p|> \Conv_e (g \o @rshift n m).
Proof.
apply S1_inj; rewrite S1_conv !S1_convn.
rewrite /Conv /= /scaled_conv big_split_ord !big_scalept /=.
congr addpt; apply eq_bigr => i _;
  rewrite (scalept_comp (S1 _) (prob_ge0 _) (dist_ge0 _ _));
  by rewrite AddDist.dE (split_lshift,split_rshift).
Qed.
Lemma convex_hull (X : set A) : is_convex_set (hull X).
Proof.
apply/asboolP => x y p; rewrite 2!in_setE.
move=> -[n [g [d [gX ->{x}]]]].
move=> -[m [h [e [hX ->{y}]]]].
rewrite in_setE.
exists (n + m).
exists [ffun i => match fintype.split i with inl a => g a | inr a => h a end].
exists (AddDist.d d e p).
split.
  move=> a -[i _]; rewrite ffunE.
  case: splitP => j _ <-; by [apply gX; exists j | apply hX; exists j].
rewrite AddDist_conv; congr Conv; apply eq_convn => i //=;
  by rewrite ffunE (split_lshift,split_rshift).
Qed.

Lemma hullI (X : set A) : hull (hull X) = hull X.
Proof.
rewrite predeqE => d; split.
- move=> -[n [g [e [gX ->{d}]]]].
  move: (convex_hull X).
  rewrite is_convex_setP /is_convex_set_n => /asboolP/(_ _ g e gX).
  by rewrite in_setE.
- by rewrite -in_setE => /hull_mem; rewrite in_setE.
Qed.

Lemma hull_setU (a : A) (x y : {convex_set A}) :
  x !=set0 -> y !=set0 -> a \in hull (x `|` y) ->
  exists a1, a1 \in x /\ exists a2, a2 \in y /\ exists p : prob, a = a1 <| p |> a2.
Proof.
move=> x0 y0.
rewrite in_setE.
case=> n -[g [e [gX Ha]]].
case: x0 => dx dx_x.
case: y0 => dy dy_y.
suff : exists a1, a1 \in scaled_set x /\ exists a2, a2 \in scaled_set y
         /\ S1 a = addpt a1 a2.
  case => -[p a1|] [Ha1] [] [q a2|] /= [Ha2] // [Hpq ->];
    (exists a1; split;
      first by rewrite -(@point_Scaled _ p a1 (Rpos_gt0 _));
      apply scaled_set_extract)
     || (exists dx; split; first by rewrite in_setE);
    (exists a2; split;
      first by rewrite -(@point_Scaled _ q a2 (Rpos_gt0 _));
      apply scaled_set_extract)
     || (exists dy; split; first by rewrite in_setE).
  + esplit; congr Conv.
  + exists `Pr 1; by rewrite conv1.
  + exists `Pr 0; by rewrite conv0.
move/(f_equal (@S1 _)): Ha; rewrite S1_convn.
rewrite (bigID (fun i => g i \in x)).
set sa1 := \big[_/_]_(i < n | _) _.
set sa2 := \big[_/_]_(i < n | _) _.
move=> Hsa.
exists sa1; split.
  rewrite /sa1; apply big_ind.
  + by rewrite in_setE.
  + apply addpt_scaled_set.
  + move=> i Hi; apply scalept_scaled_set.
    by rewrite in_setE.
exists sa2; split.
  rewrite /sa2; apply big_ind.
  + by rewrite in_setE.
  + apply addpt_scaled_set.
  + move=> i Hi; apply scalept_scaled_set.
    rewrite in_setE /= -[_ \in _]orFb -(negbTE Hi).
    apply/orP; rewrite 2!in_setE; exact/gX/imageP.
by [].
Qed.
End CSet_prop.

Section R_convex_space.
Definition avg a b (t : prob) := (t * a + t.~ * b)%R.
Lemma avg1 a b : avg a b (`Pr 1) = a.
Proof. by rewrite /avg /= mul1R onem1 mul0R addR0. Qed.
Lemma avgI x (p : prob) : avg x x p = x.
Proof. by rewrite /avg -mulRDl onemKC mul1R. Qed.
Lemma avgC x y (p : prob) : avg x y p = avg y x `Pr p.~.
Proof. by rewrite /avg onemK addRC. Qed.
Lemma avgA (p q : prob) (d0 d1 d2 : R) :
  avg d0 (avg d1 d2 q) p = avg (avg d0 d1 [r_of p, q]) d2 [s_of p, q].
Proof.
rewrite /avg /onem.
set s := [s_of p, q].
set r := [r_of p, q].
rewrite (mulRDr s) -addRA (mulRA s) (mulRC s); congr (_ + _)%R.
  by rewrite (p_is_rs p q) -/s.
rewrite mulRDr (mulRA _ _ d2).
rewrite -/p.~ -/q.~ -/r.~ -/s.~.
rewrite {2}(s_of_pqE p q) onemK; congr (_ + _)%R.
rewrite 2!mulRA; congr (_ * _)%R.
by rewrite pq_is_rs -/r -/s mulRC.
Qed.
Definition R_convMixin := ConvexSpace.Class avg1 avgI avgC avgA.
Canonical R_convType := ConvexSpace.Pack R_convMixin.
Lemma avg_oppD x y t : (- x <|t|> - y = - (x <|t|> y))%R.
Proof. rewrite /Conv /= /avg; lra. Qed.
Lemma avg_mulDr t : right_distributive Rmult (fun x y => x <|t|> y).
Proof. move => x y z. rewrite /Conv /= /avg. lra. Qed.
Lemma avg_mulDl t : left_distributive Rmult (fun x y => x <|t|> y).
Proof. move => x y z. rewrite /Conv /= /avg. lra. Qed.
(* Introduce morphisms to prove avgnE *)
Import ScaledConvex.
Definition scaleR x : R := if x is p *: y then p * y else 0.
Lemma Scaled1RK : cancel (@S1 R_convType) scaleR.
Proof. by move=> x /=; rewrite mul1R. Qed.
Lemma scaleR_addpt : {morph scaleR : x y / addpt x y >-> (x + y)%R}.
Proof.
move=> [p x|] [q y|] /=; rewrite ?(add0R,addR0) //.
rewrite /Conv /= /avg /Rpos_prob /= onem_div /Rdiv; last by apply Rpos_neq0.
rewrite -!(mulRC (/ _)%R) mulRDr !mulRA mulRV; last by apply Rpos_neq0.
by rewrite !mul1R (addRC p) addRK.
Qed.
Lemma scaleR0 : scaleR (@Zero _) = R0. by []. Qed.
Lemma scaleR_scalept p x : (0 <= p -> scaleR (scalept p x) = p * scaleR x)%R.
Proof.
case: x => [q y|]; last by rewrite scaleptR0 mulR0.
case=> Hp. by rewrite scalept_gt0 /= mulRA.
by rewrite -Hp scalept0 mul0R.
Qed.
Definition big_scaleR := big_morph scaleR scaleR_addpt scaleR0.
Definition avgn n (g : 'I_n -> R) (e : {dist 'I_n}) := \rsum_(i < n) (e i * g i)%R.
Lemma avgnE n (g : 'I_n -> R) e : \Conv_e g = avgn g e.
Proof.
rewrite -[LHS]Scaled1RK S1_convn big_scaleR.
apply eq_bigr => i _.
rewrite scaleR_scalept ?Scaled1RK //; exact/dist_ge0.
Qed.
End R_convex_space.

Module Funavg.
Section funavg.
Variables (A : Type) (B : convType).
Let T := A -> B.
Definition avg (x y : T) (t : prob) := fun a : A => (x a <| t |> y a).
Lemma avg1 (x y : T) : avg x y (`Pr 1) = x.
Proof.
apply FunctionalExtensionality.functional_extensionality => a.
by apply conv1.
Qed.
Lemma avgI (x : T) (p : prob) : avg x x p = x.
Proof.
apply FunctionalExtensionality.functional_extensionality => a.
by apply convmm.
Qed.
Lemma avgC (x y : T) (p : prob) : avg x y p = avg y x `Pr p.~.
Proof.
apply FunctionalExtensionality.functional_extensionality => a.
by apply convC.
Qed.
Lemma avgA (p q (*r s*) : prob) (d0 d1 d2 : T) :
  avg d0 (avg d1 d2 q) p = avg (avg d0 d1 [r_of p, q]) d2 [s_of p, q].
Proof.
move=> *.
apply FunctionalExtensionality.functional_extensionality => a.
by apply convA.
Qed.
End funavg.
End Funavg.

Section fun_convex_space.
Variables (A : Type) (B : convType).

Definition funConvMixin := ConvexSpace.Class
  (@Funavg.avg1 A B) (@Funavg.avgI A B) (@Funavg.avgC A B) (@Funavg.avgA A B).
Canonical funConvType := ConvexSpace.Pack funConvMixin.

End fun_convex_space.

Module Depfunavg.
Section depfunavg.
Variables (A : Type) (B : A -> convType).
Let T := forall a : A , B a.
Definition avg (x y : T) (t : prob) := fun a : A => (x a <| t |> y a).
Lemma avg1 (x y : T) : avg x y (`Pr 1) = x.
Proof.
apply FunctionalExtensionality.functional_extensionality_dep => a.
by apply conv1.
Qed.
Lemma avgI (x : T) (p : prob) : avg x x p = x.
Proof.
apply FunctionalExtensionality.functional_extensionality_dep => a.
by apply convmm.
Qed.
Lemma avgC (x y : T) (p : prob) : avg x y p = avg y x `Pr p.~.
Proof.
apply FunctionalExtensionality.functional_extensionality_dep => a.
by apply convC.
Qed.
Lemma avgA (p q (*r s*) : prob) (d0 d1 d2 : T) :
  avg d0 (avg d1 d2 q) p = avg (avg d0 d1 [r_of p, q]) d2 [s_of p, q].
Proof.
move => *.
apply FunctionalExtensionality.functional_extensionality_dep => a.
by apply convA.
Qed.
End depfunavg.
End Depfunavg.

Section depfun_convex_space.
Variables (A : Type) (B : A -> convType).

Definition depfunConvMixin := ConvexSpace.Class
  (@Depfunavg.avg1 A B) (@Depfunavg.avgI A B) (@Depfunavg.avgC A B) (@Depfunavg.avgA A B).
Canonical depfunConvType := ConvexSpace.Pack depfunConvMixin.

End depfun_convex_space.

Module Pairavg.
Section pairavg.
Variables (A B : convType).
Let T := prod A B.
Definition avg (x y : T) (t : prob) := (fst x <| t |> fst y , snd x <| t |> snd y).
Lemma avg1 (x y : T) : avg x y (`Pr 1) = x.
Proof.
  rewrite /avg (conv1 (fst x)) (conv1 (snd x)).
    by case x.
Qed.
Lemma avgI (x : T) (p : prob) : avg x x p = x.
Proof.
  rewrite /avg (convmm (fst x)) (convmm (snd x)).
    by case x.
Qed.
Lemma avgC (x y : T) (p : prob) : avg x y p = avg y x `Pr p.~.
Proof.
by congr (pair _ _); apply convC.
Qed.
Lemma avgA (p q : prob) (d0 d1 d2 : T) :
  avg d0 (avg d1 d2 q) p = avg (avg d0 d1 [r_of p, q]) d2 [s_of p, q].
Proof.
move => *.
congr (pair _ _); by apply convA.
Qed.
End pairavg.
End Pairavg.

Section pair_convex_space.
Variables (A B : convType).

Definition pairConvMixin := ConvexSpace.Class
  (@Pairavg.avg1 A B) (@Pairavg.avgI A B) (@Pairavg.avgC A B) (@Pairavg.avgA A B).
Canonical pairConvType := ConvexSpace.Pack pairConvMixin.

End pair_convex_space.

Module OrderedConvexSpace.
Record mixin_of (T : convType) : Type := Mixin {
  leconv : T -> T -> Prop where "a <= b" := (leconv a b);
  _ : forall a, a <= a;
  _ : forall b a c, a <= b -> b <= c -> a <= c;
  _ : forall a b, a = b <-> a <= b /\ b <= a }.
Record class_of (car : Type) := Class {
  base : ConvexSpace.class_of car;
  mixin : mixin_of (ConvexSpace.Pack base);
}.
Structure t : Type := Pack {car : Type; class : class_of car}.
Definition baseType (T : t) := ConvexSpace.Pack (base (class T)).
Module Exports.
Definition Leconv (T : t) : car T -> car T -> Prop :=
  let: Pack _ (Class _ (Mixin leconv _ _ _)) := T in leconv.
Arguments Leconv {T} : simpl never.
Notation "x <= y" := (Leconv x y) : ordered_convex_scope.
Notation "x <= y <= z" := (Leconv x y /\ Leconv y z) : ordered_convex_scope.
Notation orderedConvType := t.
Coercion baseType : orderedConvType >-> convType.
Canonical baseType.
End Exports.
End OrderedConvexSpace.
Export OrderedConvexSpace.Exports.

Section ordered_convex_space_interface.
Local Open Scope ordered_convex_scope.
Variable A : orderedConvType.
Implicit Types a b c : A.
Lemma leconvR a : a <= a.
Proof. by case: A a => ? [? []]. Qed.
Lemma leconv_trans b a c : a <= b -> b <= c -> a <= c.
Proof. by case: A b a c => ? [? []]. Qed.
Lemma eqconv_le a b : (a = b) <-> (a <= b <= a).
Proof. by case: A a b => ? [? []]. Qed.
End ordered_convex_space_interface.

Definition R_orderedConvMixin := OrderedConvexSpace.Mixin leRR leR_trans eqR_le.
Canonical R_orderedConvType := OrderedConvexSpace.Pack (OrderedConvexSpace.Class R_orderedConvMixin).

Module FunLe.
Section lefun.
Local Open Scope ordered_convex_scope.
Variables (A : convType) (B : orderedConvType).
Definition T := A -> B.
Definition lefun (f g : T) := forall a, f a <= g a.
Lemma lefunR f : lefun f f.
Proof. move => *; exact: leconvR. Qed.
Lemma lefun_trans g f h : lefun f g -> lefun g h -> lefun f h.
Proof. move => Hfg Hgh a; move : (Hfg a) (Hgh a); exact: leconv_trans. Qed.
Lemma eqfun_le f g : f = g <-> lefun f g /\ lefun g f.
Proof. split; [move ->; move: lefunR; done |].
case => Hfg Hgh; apply FunctionalExtensionality.functional_extensionality => a.
move : (Hfg a) (Hgh a) => Hfg' Hgh'.
by apply eqconv_le.
Qed.
End lefun.
End FunLe.

Section fun_ordered_convex_space.
Variables (A : convType) (B : orderedConvType).
Import FunLe.
Definition fun_orderedConvMixin := OrderedConvexSpace.Mixin (@lefunR A B) (@lefun_trans A B) (@eqfun_le A B).
Canonical fun_orderedConvType := OrderedConvexSpace.Pack (OrderedConvexSpace.Class fun_orderedConvMixin).
End fun_ordered_convex_space.

Module OppositeOrderedConvexSpace.
Section def.
Variable A : orderedConvType.
CoInductive T := mkOpp : A -> T.
End def.
Section leopp.
Local Open Scope ordered_convex_scope.
Variable A : orderedConvType.
Notation T := (T A).
Definition leopp (x y : T) := match (x,y) with (mkOpp x',mkOpp y') => y' <= x' end.
Lemma leoppR x : leopp x x.
Proof. case x; exact: leconvR. Qed.
Lemma leopp_trans y x z : leopp x y -> leopp y z -> leopp x z.
Proof. case x;case y;case z=>z' y' x' yx zy; apply:(leconv_trans zy); exact yx. Qed.
Lemma eqopp_le x y : x = y <-> leopp x y /\ leopp y x.
Proof. split; [move ->; move: leoppR; done |].
case x;case y=>y' x'; rewrite /leopp/=.
by move/eqconv_le->.
Qed.
End leopp.
Section convtype.
Local Open Scope convex_scope.
Variable A : orderedConvType.
Notation T := (T A).
Definition unbox (x : T) := match x with mkOpp x' => x' end.
Definition avg a b (t : prob) := mkOpp (unbox a <|t|> unbox b).
Lemma avg1 a b : avg a b (`Pr 1) = a.
Proof. by case a;case b=>b' a';rewrite/avg/unbox/=conv1. Qed.
Lemma avgI x (p : prob) : avg x x p = x.
Proof. by case x=>x';rewrite/avg/unbox/=convmm. Qed.
Lemma avgC x y (p : prob) : avg x y p = avg y x `Pr p.~.
Proof. by case x;case y=>y' x'; rewrite/avg/unbox/=convC. Qed.
Lemma avgA (p q : prob) d0 d1 d2 :
  avg d0 (avg d1 d2 q) p = avg (avg d0 d1 [r_of p, q]) d2 [s_of p, q].
Proof. by case d0;case d1;case d2=>d2' d1' d0';rewrite/avg/unbox/=convA. Qed.
Definition oppConvMixin := ConvexSpace.Class avg1 avgI avgC avgA.
End convtype.
End OppositeOrderedConvexSpace.

Section opposite_ordered_convex_space.
Import OppositeOrderedConvexSpace.
Variable A : orderedConvType.
Canonical oppConvType := ConvexSpace.Pack (oppConvMixin A).
Definition opposite_orderedConvMixin := @OrderedConvexSpace.Mixin oppConvType (@leopp A) (@leoppR A) (@leopp_trans A) (@eqopp_le A).
Canonical opposite_orderedConvType := OrderedConvexSpace.Pack (OrderedConvexSpace.Class opposite_orderedConvMixin).
End opposite_ordered_convex_space.
Notation "a '.逆'" := (OppositeOrderedConvexSpace.mkOpp a) (at level 10, format "a .逆") : ordered_convex_scope.

Section opposite_ordered_convex_space_prop.
Local Open Scope ordered_convex_scope.
Import OppositeOrderedConvexSpace.
Variable A : orderedConvType.
Lemma conv_leoppD (a b : A) t : a.逆 <|t|> b.逆 = (a <|t|> b).逆.
Proof. by rewrite/Conv/=/avg/unbox. Qed.
Lemma unboxK (a : A) : unbox (a.逆) = a.
Proof. reflexivity. Qed.
Lemma leoppP (a b : T A) : a <= b <-> unbox b <= unbox a.
Proof. by case a;case b=>*;rewrite !unboxK. Qed.
End opposite_ordered_convex_space_prop.

Section convex_function_def.
Local Open Scope ordered_convex_scope.
Variables (A : convType) (B : orderedConvType).

Definition convex_function_at (f : A -> B) a b p :=
  f (a <| p |> b) <= f a <| p |> f b.

(* NB(rei): move from 'I_n -> A to 'rV[A]_n? *)
Definition convex_function_at_Convn (f : A -> B) n (a : 'I_n -> A) (t : {dist 'I_n}) :=
  f (\Conv_t a) <= \Conv_t (f \o a).

Definition strictly_convexf_at (f : A -> B) := forall a b (t : prob),
  a <> b -> (0 < t < 1)%R -> convex_function_at f a b t.

Lemma convex_function_atxx (f : A -> B) a t : convex_function_at f a a t.
Proof. rewrite /convex_function_at !convmm; exact/leconvR. Qed.

End convex_function_def.

Module ConvexFunction. (* see Additive in ssralg *)
Section ClassDef.
Local Open Scope ordered_convex_scope.
Variables (U : convType) (V : orderedConvType).
Definition axiom (f : U -> V) := forall a b (t : prob), convex_function_at f a b t.
Structure map (phUV : phant (U -> V)) := Pack {apply; _ : axiom apply}.
Local Coercion apply : map >-> Funclass.
Variables (phUV : phant (U -> V)) (f g : U -> V) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.
End ClassDef.
Module Exports.
Notation convex_function f := (axiom f).
Coercion apply : map >-> Funclass.
Notation ConvexFunction fA := (Pack (Phant _) fA).
Notation "{ 'convex' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'convex'  fUV }") : convex_scope.
Notation "[ 'convex' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'convex'  'of'  f  'as'  g ]") : convex_scope.
Notation "[ 'convex' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'convex'  'of'  f ]") : convex_scope.
End Exports.
End ConvexFunction.
Include ConvexFunction.Exports.

Section convex_function_prop.
Variables (U : convType) (V : orderedConvType) (f : {convex U -> V}).
Lemma convex_functionP a b t : convex_function_at f a b t.
Proof. by case: f => f0; apply. Qed.
End convex_function_prop.

Section convex_function_prop'.
Local Open Scope ordered_convex_scope.
Variable (A : convType) (B C : orderedConvType).

Lemma convex_function_sym (f : A -> B) a b : (forall t, convex_function_at f a b t) ->
  forall t, convex_function_at f b a t.
Proof.
move => H t; move: (H (`Pr t.~)).
by rewrite /convex_function_at /= convC -probK (convC (f a)) -probK.
Qed.

Lemma convex_function_comp (f : {convex A -> B}) (g : {convex B -> C})
      (g_monotone_on_hull_Im_f : forall a b t, (f (a <|t|> b) <= f a <|t|> f b) -> (g (f (a <|t|> b)) <= g (f a <|t|> f b)))
      : convex_function (fun a => g (f a)).
Proof.
  move=> a b t.
  move : (convex_functionP g (f a) (f b) t).
  rewrite /convex_function_at => Hg.
  eapply leconv_trans; [| exact Hg] => {Hg}.
  apply g_monotone_on_hull_Im_f.
  exact: (convex_functionP f).
Qed.

Lemma convex_function_comp' (f : {convex A -> B}) (g : {convex B -> C})
      (g_monotone : forall x y, (x <= y) -> (g x <= g y))
      : convex_function (fun a => g (f a)).
Proof.
  apply convex_function_comp => // *.
  by apply g_monotone.
Qed.

End convex_function_prop'.

Section convex_in_both.
Local Open Scope ordered_convex_scope.
Variables (A B : convType) (C : orderedConvType) (f : A -> B -> C).
Definition convex_in_both := convex_function (prod_curry f).
Lemma convex_in_bothP :
  convex_in_both
  <->
  forall a0 a1 b0 b1 t,
    f (a0 <| t |> a1) (b0 <| t |> b1) <= f a0 b0 <| t |> f a1 b1.
Proof.
split => [H a0 a1 b0 b1 t | H];
  first by move: (H (a0,b0) (a1,b1) t); rewrite /convex_function_at /prod_curry.
by case => a0 b0 [a1 b1] t; move:(H a0 a1 b0 b1 t); rewrite /convex_function_at /prod_curry.
Qed.
End convex_in_both.

Section biconvex_function.
Local Open Scope ordered_convex_scope.
Section definition.
Variables (A B : convType) (C : orderedConvType) (f : A -> B -> C).
Definition biconvex_function := (forall a, convex_function (f a)) /\ (forall b, convex_function (f^~ b)).
(*
Lemma biconvex_functionP : biconvex_function <-> convex_function f /\ @convex_function B (fun_orderedConvType A C) (fun b a => f a b).
Proof.
change ((forall (a : A) (a0 b : B) (t : prob),
   f a (a0 <|t|> b) <= f a a0 <|t|> f a b) /\
  (forall (b : B) (a b0 : A) (t : prob),
   f (a <|t|> b0) b <= f a b <|t|> f b0 b) <->
  (forall (a b : A) (t : prob) (a0 : B),
   f (a <|t|> b) a0 <= f a a0 <|t|> f b a0) /\
  (forall (a b : B) (t : prob) (a0 : A),
   f a0 (a <|t|> b) <= f a0 a <|t|> f a0 b)).
by split; case => [H0 H1]; split => *; try apply H0; try apply H1.
Qed.
 *)
End definition.
Section counterexample.
Local Open Scope R_scope.
Example biconvex_is_not_convex_in_both : exists f : R -> R -> R, biconvex_function f /\ ~ convex_in_both f.
Proof.
exists Rmult; split.
split => [a b0 b1 t | b a0 a1 t] /=; rewrite /Conv /= ; [rewrite avg_mulDr /Conv /=|rewrite avg_mulDl /Conv /=]; exact: leRR.
move /convex_in_bothP /(_ (-1)%R 1%R 1%R (-1)%R (probinvn 1)).
rewrite /Leconv /probinvn /Conv /= /avg /=.
rewrite mul1R !mulR1 !mulRN1.
rewrite /onem.
rewrite (_ : (- / (1 + 1) + (1 - / (1 + 1))) = 0); last by lra.
rewrite mul0R.
rewrite (_ : - / (1 + 1) + - (1 - / (1 + 1)) = - 1); last by lra.
by move /leRNlt; apply; lra.
Qed.
End counterexample.
End biconvex_function.

Section concave_function_def.
Local Open Scope ordered_convex_scope.
Variables (A : convType) (B : orderedConvType).
Definition concave_function_at (f : A -> B) a b t := convex_function_at (fun a => (f a).逆) a b t. 
Definition concave_function_at' (f : A -> B) a b t := (f a <| t |> f b <= f (a <| t |> b)).
Definition strictly_concavef_at (f : A -> B) := forall a b (t : prob),
  a <> b -> (0 < t < 1)%R -> concave_function_at f a b t.
Lemma concave_function_at'P f a b t : concave_function_at' f a b t <-> concave_function_at f a b t.
Proof. by rewrite /concave_function_at'/concave_function_at/convex_function_at conv_leoppD leoppP. Qed.
End concave_function_def.

Module ConcaveFunction.
Section ClassDef.
Local Open Scope ordered_convex_scope.
Variables (U : convType) (V : orderedConvType).
Definition axiom (f : U -> V) := forall a b (t : prob), concave_function_at f a b t.
Structure map (phUV : phant (U -> V)) := Pack {apply; _ : axiom apply}.
Local Coercion apply : map >-> Funclass.
Variables (phUV : phant (U -> V)) (f g : U -> V) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.
End ClassDef.
Module Exports.
Notation concave_function f := (axiom f).
Coercion apply : map >-> Funclass.
Notation ConcaveFunction fA := (Pack (Phant _) fA).
Notation "{ 'concave' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'concave'  fUV }") : convex_scope.
Notation "[ 'concave' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'concave'  'of'  f  'as'  g ]") : convex_scope.
Notation "[ 'concave' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'concave'  'of'  f ]") : convex_scope.
End Exports.
End ConcaveFunction.
Include ConcaveFunction.Exports.

(* NB: see leR_oppl *)
Lemma leR_opp2 x y : (-x <= - y)%R <-> (y <= x)%R.
Proof. split;[exact: Ropp_le_cancel|exact:Ropp_le_contravar]. Qed.

Section concave_function_prop.
Local Open Scope ordered_convex_scope.
Variable (A : convType) (B : orderedConvType).
Section prop.
Variable (f : A -> B).
Lemma concave_function_atxx a t : concave_function_at f a a t.
Proof. exact: convex_function_atxx. Qed.
End prop.
Section Rprop.
(*Variable (f : A -> R).*)
Lemma R_convex_function_atN (f : A -> R) a b t : concave_function_at f a b t -> convex_function_at (fun x => - f x)%R a b t.
Proof. by rewrite /convex_function_at /Leconv /= avg_oppD leR_opp2. Qed.
Lemma R_concave_function_atN (f : A -> R) a b t : convex_function_at f a b t -> concave_function_at (fun x => - f x)%R a b t.
Proof. by rewrite /concave_function_at /Leconv /= /OppositeOrderedConvexSpace.leopp /Leconv /= avg_oppD leR_opp2. Qed.
Lemma R_convex_functionN (f : A -> R) : concave_function f -> convex_function (fun x => - f x)%R.
Proof. move=> H a b t; exact/R_convex_function_atN/H. Qed.
Lemma R_concave_functionN (f : A -> R) : convex_function f -> concave_function (fun x => - f x)%R.
Proof. move=> H a b t; exact/R_concave_function_atN/H. Qed.
Lemma R_convex_function_atN' (f : A -> R) a b t : concave_function_at (fun x => - f x)%R a b t -> convex_function_at f a b t.
Proof. by move/(R_convex_function_atN);rewrite/convex_function_at !oppRK. Qed.
Lemma R_concave_function_atN' (f : A -> R) a b t : convex_function_at (fun x => - f x)%R a b t -> concave_function_at f a b t.
Proof. by move/(R_concave_function_atN);rewrite/concave_function_at/convex_function_at !oppRK. Qed.
Lemma R_convex_functionN' (f : A -> R) : concave_function (fun x => - f x)%R -> convex_function f.
Proof. move=> H a b t; exact/R_convex_function_atN'/H. Qed.
Lemma R_concave_functionN' (f : A -> R) : convex_function (fun x => - f x)%R -> concave_function f.
Proof. move=> H a b t; exact/R_concave_function_atN'/H. Qed.
End Rprop.
Section Rprop2.
Lemma R_convex_functionB (f g : A -> R) :
  convex_function f -> concave_function g -> convex_function (fun x => f x - g x)%R.
Proof.
move=> H1 H2 p q t.
rewrite /convex_function_at /=.
rewrite {3}/Conv /= /avg /= (* TODO *) 2!mulRBr addRAC addRA.
move: (H1 p q t) => {H1}H1.
rewrite -addR_opp -addRA; apply leR_add => //.
rewrite -2!mulRN addRC; exact: (R_convex_functionN H2).
Qed.
Lemma R_concave_functionB (f g : A -> R) :
  concave_function f -> convex_function g -> concave_function (fun x => f x - g x)%R.
Proof.
move=> H1 H2.
rewrite (_ : (fun _ => _) = (fun x => - (g x - f x)))%R; last first.
  apply FunctionalExtensionality.functional_extensionality => x; by rewrite oppRB.
exact/R_concave_functionN/R_convex_functionB.
Qed.
End Rprop2.
End concave_function_prop.

Section affine_function_def.
Local Open Scope ordered_convex_scope.
Variables (A : convType) (B : convType).
Definition affine_function_at (f : A -> B) a b t := (f (a <| t |> b) = f a <| t |> f b).
End affine_function_def.

Module AffineFunction.
Section ClassDef.
Local Open Scope ordered_convex_scope.
Variables (U : convType) (V : convType).
Definition axiom (f : U -> V) := forall a b (t : prob), affine_function_at f a b t.
Structure map (phUV : phant (U -> V)) := Pack {apply; _ : axiom apply}.
Local Coercion apply : map >-> Funclass.
Variables (phUV : phant (U -> V)) (f g : U -> V) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.
End ClassDef.
Module Exports.
Notation affine_function f := (axiom f).
Coercion apply : map >-> Funclass.
Notation AffineFunction fA := (Pack (Phant _) fA).
Notation "{ 'affine' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'affine'  fUV }") : convex_scope.
Notation "[ 'affine' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'affine'  'of'  f  'as'  g ]") : convex_scope.
Notation "[ 'affine' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'affine'  'of'  f ]") : convex_scope.
End Exports.
End AffineFunction.
Include AffineFunction.Exports.

Section affine_function_prop0.
Lemma affine_functionP' (A B : convType) (f : {affine A -> B}) a b t :
  affine_function_at f a b t.
Proof. by case: f => f0; apply. Qed.
Lemma affine_function_id_proof (A : convType) :
  affine_function (ssrfun.id : A -> A).
Proof. by []. Qed.
Definition affine_function_id (A : convType) : {affine A -> A} :=
  AffineFunction (@affine_function_id_proof A).
Lemma affine_function_comp_proof (A B C : convType) (f : {affine A -> B})
  (g : {affine B -> C}) : affine_function (g \o f).
Proof.
move=> a b t; rewrite /affine_function_at /=.
by rewrite (affine_functionP' f) (affine_functionP' g).
Qed.
Definition affine_function_comp (A B C : convType) (f : {affine A -> B}) (g : {affine B -> C}) :
  {affine A -> C} := AffineFunction (affine_function_comp_proof f g).
Lemma affine_function_Sum (A B : convType) (f : {affine A -> B}) (n : nat)
                          (g : 'I_n -> A) (e : {dist 'I_n}) :
  f (\Conv_e g) = \Conv_e (f \o g).
Proof.
Import ScaledConvex.
apply S1_inj; rewrite S1_convn S1_convn_proj //.
by move=> p x y; rewrite affine_functionP'.
Qed.
End affine_function_prop0.

Section affine_function_prop.
Variables (A : convType) (B : orderedConvType).

Lemma affine_functionP (f : A -> B) : affine_function f <-> convex_function f /\ concave_function f.
Proof.
split => [H | [H1 H2] p q t].
  split.
  - move=> p q t; rewrite /convex_function_at /= H //; exact/leconvR.
  - move=> p q t; rewrite /concave_function_at /= H //; exact/leconvR.
rewrite /affine_function_at eqconv_le; split; [exact/H1|exact/H2].
Qed.

End affine_function_prop.

Section R_affine_function_prop.
Variables (A : convType) (f : A -> R).
Lemma R_affine_functionN : affine_function f -> affine_function (fun x => - f x)%R.
Proof. move /affine_functionP => [H1 H2]; rewrite affine_functionP; split => //; [exact/R_convex_functionN|exact/R_concave_functionN]. Qed.
End R_affine_function_prop.

Section convex_function_in_def.
Variables (A : convType) (D : convex_set A) (f : A -> R).
Definition convex_function_in :=
  forall a b p, a \in D -> b \in D -> convex_function_at f a b p.
Definition concave_function_in :=
  forall a b p, a \in D -> b \in D -> concave_function_at f a b p.
End convex_function_in_def.

Section dist_convex_space.
Variable A : finType.
Definition dist_convMixin :=
  @ConvexSpace.Class (dist A) (@Conv2Dist.d A)
  (@Conv2Dist.d1 A)
  (@Conv2Dist.idempotent A)
  (@Conv2Dist.skewed_commute A)
  (@Conv2Dist.quasi_assoc A).
Canonical dist_convType := ConvexSpace.Pack dist_convMixin.

(* Reuse the morphisms from R_convex_space. *)
Import ScaledConvex.
Lemma convn_convdist (n : nat) (g : 'I_n -> dist A) (d : {dist 'I_n}) :
  \Conv_d g = ConvDist.d d g.
Proof.
apply dist_ext=> a; rewrite -[LHS]Scaled1RK.
rewrite (@S1_convn_proj _ _ (@^~ a \o @pos_ff _ \o @pmf _)); last first.
  move=> p x y /=; by rewrite /Conv /= Conv2Dist.dE.
rewrite big_scaleR ConvDist.dE; apply eq_bigr => i _.
rewrite scaleR_scalept ?Scaled1RK //; exact/dist_ge0.
Qed.
End dist_convex_space.

(* TODO *)
Section dist_ordered_convex_space.
Variable A : finType.
Definition dist_orderedConvMixin := (@OrderedConvexSpace.Mixin (dist_convType A)).
End dist_ordered_convex_space.

Lemma Conv2DistdE (A : finType) (a b : dist A) (p : prob) (x : A) :
  (a <| p |> b) x = a x <| p |> b x.
Proof. by rewrite Conv2Dist.dE. Qed.

Lemma DistBindConv (A : finType) (B : finType)(p : prob) (dx dy : dist A) (f : A -> dist B) :
  DistBind.d dx f <|p|> DistBind.d dy f = DistBind.d (dx <|p|> dy) f.
Proof.
apply/dist_ext => b0.
rewrite !(Conv2Dist.dE,DistBind.dE) !big_distrr -big_split; apply eq_bigr => a0 _ /=.
by rewrite Conv2Dist.dE mulRDl 2!mulRA.
Qed.

Lemma rsum_Conv (A : finType) (p : prob) (dx dy : dist A):
  \rsum_(a in A) (dx a <|p|> dy a) =
  \rsum_(a in A) dx a <|p|> \rsum_(a in A) dy a.
Proof. by rewrite /Conv /= /avg big_split /= -2!big_distrr. Qed.

Section convex_set_R.

Lemma Rpos_convex : is_convex_set (fun x => 0 < x)%R.
Proof.
apply/asboolP => x y t; rewrite !in_setE => Hx Hy.
case/boolP : (t == `Pr 0) => [/eqP ->| Ht0]; first by rewrite conv0.
apply addR_gt0wl; first by apply mulR_gt0 => //; exact/prob_gt0.
apply mulR_ge0; [exact/onem_ge0/prob_le1 | exact: ltRW].
Qed.

Definition Rpos_interval := CSet.mk Rpos_convex.

Lemma Rnonneg_convex : is_convex_set (fun x => 0 <= x)%R.
Proof.
apply/asboolP => x y t; rewrite !in_setE => Hx Hy.
apply addR_ge0; apply/mulR_ge0 => //; [exact/prob_ge0 | apply/onem_ge0; exact/prob_le1].
Qed.

Definition Rnonneg_interval := CSet.mk Rnonneg_convex.

Lemma open_interval_convex a b (Hab : (a < b)%R) : is_convex_set (fun x => a < x < b)%R.
Proof.
apply/asboolP => x y t; rewrite !in_setE => -[xa xb] [ya yb].
case/boolP : (t == `Pr 0) => [/eqP|]t0; first by rewrite t0 conv0.
case/boolP : (t == `Pr 1) => [/eqP|]t1; first by rewrite t1 conv1.
apply conj.
- rewrite -[X in (X < t * x + t.~ * y)%R]mul1R -(onemKC t) mulRDl.
  apply ltR_add; rewrite ltR_pmul2l //; [exact/prob_gt0 | exact/onem_gt0/prob_lt1].
- rewrite -[X in (_ + _ < X)%R]mul1R -(onemKC t) mulRDl.
  apply ltR_add; rewrite ltR_pmul2l //; [exact/prob_gt0 | exact/onem_gt0/prob_lt1].
Qed.

Lemma open_unit_interval_convex : is_convex_set (fun x => 0 < x < 1)%R.
Proof. apply /open_interval_convex /Rlt_0_1. Qed.

Definition open_unit_interval := CSet.mk open_unit_interval_convex.

End convex_set_R.

Section convex_function_R.

Implicit Types f : R_convType -> R.

Lemma concave_function_atN f x y t : concave_function_at f x y t ->
  forall k, (0 <= k)%R -> concave_function_at (fun x => f x * k)%R x y t.
Proof.
move=> H k k0; rewrite /concave_function_at /convex_function_at.
rewrite conv_leoppD leoppP.
rewrite {2}/Conv /= /avg /= (* TODO *).
rewrite /Leconv /= -avg_mulDl.
exact: leR_wpmul2r.
Qed.

Lemma convexf_at_onem x y (t : prob) f : (0 < x -> 0 < y -> x < y ->
  convex_function_at f x y t -> convex_function_at f y x (`Pr t.~))%R.
Proof.
move=> x0 y0 xy H; rewrite /convex_function_at.
rewrite {2}/Conv /= /avg /= onemK addRC.
rewrite /convex_function_at /Conv /= /avg /= in H.
rewrite /Conv /= /avg /= onemK addRC.
apply: (leR_trans H); rewrite addRC; exact/leRR.
Qed.

Lemma concavef_at_onem x y (t : prob) f : (0 < x -> 0 < y -> x < y ->
  concave_function_at f x y t -> concave_function_at f y x (`Pr t.~))%R.
Proof.
move=>x0 y0 xy; rewrite/concave_function_at/convex_function_at.
rewrite !conv_leoppD !leoppP/=.
rewrite /Conv /= /avg /= onemK.
by rewrite addRC [in X in Leconv _ X -> _]addRC.
Qed.
End convex_function_R.

(* NB(saikawa):
Assume f is twice differentiable on an open interval I.
Let Df and DDf be the first and second derivatives of f.
Further assume DDf is always positive.  By applying MVT, we have :
forall a x \in I, exists c1 \in [a,x], f(x) = f(a) + (x-a) * Df(c1).
Fix a and x.  Applying MVT again, we further get :
exists c2 \in (a,c1), Df(c1) = Df(a) + (c1-a) * DDf(c2).
The two equations combined is :
f(x) = f(a) + (x-a) * Df(a) + (x-a)(c1-a) * DDf(c2).
The last term is then positive thanks to the assumption on DDf.
Now this is an equivalent condition to the convexity of f.
 *)

(* ref: http://www.math.wisc.edu/~nagel/convexity.pdf *)
Section twice_derivable_convex.

Variables (f : R -> R) (a b : R).
Let I := fun x0 => (a <= x0 <= b)%R.
Hypothesis HDf : pderivable f I.
Variable Df : R -> R.
Hypothesis DfE : forall x (Hx : I x), Df x = derive_pt f x (HDf Hx).
Hypothesis HDDf : pderivable Df I.
Variable DDf : R -> R.
Hypothesis DDfE : forall x (Hx : I x), DDf x = derive_pt Df x (HDDf Hx).
Hypothesis DDf_ge0 : forall x, I x -> (0 <= DDf x)%R.

Definition L (x : R) := (f a + (x - a) / (b - a) * (f b - f a))%R.

Hypothesis ab : (a < b)%R.

Lemma LE x : L x = ((b - x) / (b - a) * f a + (x - a) / (b - a) * f b)%R.
Proof.
rewrite /L mulRBr [in LHS]addRA addRAC; congr (_ + _)%R.
rewrite addR_opp -{1}(mul1R (f a)) -mulRBl; congr (_ * _)%R.
rewrite -(mulRV (b - a)); last by rewrite subR_eq0'; exact/eqP/gtR_eqF.
by rewrite -mulRBl -addR_opp oppRB addRA subRK addR_opp.
Qed.

Lemma convexf_ptP : (forall x, a <= x <= b -> 0 <= L x - f x)%R ->
  forall t : prob, convex_function_at f a b t.
Proof.
move=> H t; rewrite /convex_function_at.
set x := (t * a + t.~ * b)%R.
have : (a <= x <= b)%R.
  rewrite /x; split.
  - apply (@leR_trans (t * a + t.~ * a)).
      rewrite -mulRDl addRCA addR_opp subRR addR0 mul1R; exact/leRR.
    case/boolP : (t == `Pr 1) => [/eqP ->|t1].
      rewrite /onem subRR !mul0R !addR0; exact/leRR.
    rewrite leR_add2l; apply leR_wpmul2l; last exact/ltRW.
    exact/onem_ge0/prob_le1.
  - apply (@leR_trans (t * b + t.~ * b)); last first.
      rewrite -mulRDl addRCA addR_opp subRR addR0 mul1R; exact/leRR.
    rewrite leR_add2r; apply leR_wpmul2l; [exact/prob_ge0 | exact/ltRW].
move/H; rewrite subR_ge0 => /leR_trans; apply.
rewrite LE //.
have -> : ((b - x) / (b - a) = t)%R.
  rewrite /x -addR_opp oppRD addRCA mulRBl mul1R oppRB (addRCA b).
  rewrite addR_opp subRR addR0 -mulRN addRC -mulRDr addR_opp.
  rewrite /Rdiv -mulRA mulRV ?mulR1 // subR_eq0'; exact/eqP/gtR_eqF.
have -> : ((x - a) / (b - a) = t.~)%R.
  rewrite /x -addR_opp addRAC -{1}(oppRK a) mulRN -mulNR -{2}(mul1R (- a)%R).
  rewrite -mulRDl (addRC _ R1) addR_opp -mulRDr addRC addR_opp.
  rewrite /Rdiv -mulRA mulRV ?mulR1 // subR_eq0'; exact/eqP/gtR_eqF.
exact/leRR.
Qed.

Lemma second_derivative_convexf_pt : forall t : prob, convex_function_at f a b t.
Proof.
have note1 : forall x, R1 = ((x - a) / (b - a) + (b - x) / (b - a))%R.
  move=> x; rewrite -mulRDl addRC addRA subRK addR_opp mulRV // subR_eq0'.
  exact/eqP/gtR_eqF.
have step1 : forall x, f x = ((x - a) / (b - a) * f x + (b - x) / (b - a) * f x)%R.
  by move=> x; rewrite -mulRDl -note1 mul1R.
apply convexf_ptP => // x axb.
rewrite /L.
case: axb.
  rewrite leR_eqVlt => -[-> _|].
  rewrite /L subRR div0R mul0R addR0 subRR; exact/leRR.
move=> ax.
rewrite leR_eqVlt => -[->|].
rewrite /L /Rdiv mulRV ?mul1R; last by rewrite subR_eq0'; exact/eqP/gtR_eqF.
rewrite addRC subRK subRR; exact/leRR.
move=> xb.
have {step1}step2 : (L x - f x =
  (x - a) * (b - x) / (b - a) * ((f b - f x) / (b - x)) -
  (b - x) * (x - a) / (b - a) * ((f x - f a) / (x - a)))%R.
  rewrite {1}step1 {step1}.
  rewrite -addR_opp oppRD addRA addRC addRA.
  rewrite LE //.
  rewrite {1}/Rdiv -(mulRN _ (f x)) -/(Rdiv _ _).
  rewrite addRA -mulRDr (addRC _ (f a)) (addR_opp (f a)).
  rewrite -mulRN -addRA -mulRDr (addR_opp (f b)).
  rewrite addRC.
  rewrite -(oppRK (f a - f x)) mulRN addR_opp oppRB.
  congr (_ + _)%R.
  - rewrite {1}/Rdiv -!mulRA; congr (_ * _)%R; rewrite mulRCA; congr (_ * _)%R.
    rewrite mulRCA mulRV ?mulR1 // subR_eq0'; exact/eqP/gtR_eqF.
  - rewrite -!mulNR -!mulRA; congr (_ * _)%R; rewrite mulRCA; congr (_ * _)%R.
    rewrite mulRCA mulRV ?mulR1 // subR_eq0'; exact/eqP/gtR_eqF.
have [c2 [Ic2 Hc2]] : exists c2, (x < c2 < b /\ (f b - f x) / (b - x) = Df c2)%R.
  have H : pderivable f (fun x0 => x <= x0 <= b)%R.
    move=> z [z1 z2]; apply HDf; split => //.
    apply (@leR_trans x) => //; exact: ltRW.
  case: (@MVT_cor1_pderivable x b f H xb) => c2 [Ic2 [H1 H2]].
  exists c2; split => //.
  rewrite H1 /Rdiv -mulRA mulRV ?mulR1; last first.
    by rewrite subR_eq0'; exact/eqP/gtR_eqF.
  rewrite DfE; last by move=> ?; exact: proof_derive_irrelevance.
  split.
    apply (@leR_trans x); [exact/ltRW | by case: Ic2 H1].
  by case: H2 => _ /ltRW.
have [c1 [Ic1 Hc1]] : exists c1, (a < c1 < x /\ (f x - f a) / (x - a) = Df c1)%R.
  have H : pderivable f (fun x0 => a <= x0 <= x)%R.
    move=> z [z1 z2]; apply HDf; split => //.
    apply (@leR_trans x) => //; exact: ltRW.
  case: (@MVT_cor1_pderivable a x f H ax) => c1 [Ic1 [H1 H2]].
  exists c1; split => //.
  rewrite H1 /Rdiv -mulRA mulRV ?mulR1; last first.
    by rewrite subR_eq0'; exact/eqP/gtR_eqF.
  rewrite DfE; last by move=> ?; exact: proof_derive_irrelevance.
  split.
  - by case: H2 => /ltRW.
  - apply (@leR_trans x).
    by case: H2 => _ /ltRW.
    apply (@leR_trans c2); apply/ltRW; by case: Ic2.
have c1c2 : (c1 < c2)%R by apply (@ltR_trans x); [case: Ic1 | case: Ic2].
have {step2 Hc1 Hc2}step3 : (L x - f x =
  (b - x) * (x - a) * (c2 - c1) / (b - a) * ((Df c2 - Df c1) / (c2 - c1)))%R.
  rewrite {}step2 Hc2 Hc1 (mulRC (x - a)%R) -mulRBr {1}/Rdiv -!mulRA.
  congr (_ * (_ * _))%R; rewrite mulRCA; congr (_ * _)%R.
  rewrite mulRCA mulRV ?mulR1 // subR_eq0'; by move/gtR_eqF/eqP : c1c2.
have [d [Id H]] : exists d, (c1 < d < c2 /\ (Df c2 - Df c1) / (c2 - c1) = DDf d)%R.
  have H : pderivable Df (fun x0 => c1 <= x0 <= c2)%R.
    move=> z [z1 z2]; apply HDDf; split => //.
    - apply (@leR_trans c1) => //; by case: Ic1 => /ltRW.
    - apply (@leR_trans c2) => //; by case: Ic2 => _ /ltRW.
  case: (@MVT_cor1_pderivable c1 c2 Df H c1c2) => d [Id [H1 H2]].
  exists d; split => //.
  rewrite H1 /Rdiv -mulRA mulRV ?mulR1; last first.
    by rewrite subR_eq0'; exact/eqP/gtR_eqF.
  rewrite DDfE; last by move=> ?; exact: proof_derive_irrelevance.
  split.
  - apply (@leR_trans c1); last by case: Id H1.
    apply/ltRW; by case: Ic1.
  - apply (@leR_trans c2); last by case: Ic2 => _ /ltRW.
    by case: H2 => _ /ltRW.
rewrite {}step3 {}H.
apply/mulR_ge0; last first.
  apply: DDf_ge0; split.
    apply (@leR_trans c1).
      apply/ltRW; by case: Ic1.
     by case: Id => /ltRW.
  apply (@leR_trans c2).
    by case: Id => _ /ltRW.
  apply/ltRW; by case: Ic2.
apply/mulR_ge0; last by apply/ltRW/invR_gt0; rewrite subR_gt0.
apply/mulR_ge0; last first.
  by rewrite subR_ge0; case: Id => Id1 Id2; apply (@leR_trans d); exact/ltRW.
apply/mulR_ge0; rewrite subR_ge0; exact/ltRW.
Qed.

End twice_derivable_convex.
