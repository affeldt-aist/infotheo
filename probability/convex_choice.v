(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import all_ssreflect ssralg fingroup perm finalg matrix.
From mathcomp Require Import boolp classical_sets.
Require Import Reals.
Require Import ssrR Reals_ext Ranalysis_ext ssr_ext ssralg_ext logb Rbigop.
Require Import proba.

(* convex spaces over a choiceType *)

Reserved Notation "x <| p |> y" (format "x  <| p |>  y", at level 50).
Reserved Notation "{ 'convex_set' T }" (format "{ 'convex_set'  T }").
Reserved Notation "'\Conv_' d f" (at level 36, f at level 36, d at level 0,
  format "\Conv_ d  f").
Reserved Notation "\ssum_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
  format "'[' \ssum_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\ssum_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
  format "'[' \ssum_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\ssum_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
  format "'[' \ssum_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\ssum_ i F"
  (at level 41, F at level 41, i at level 0, right associativity,
  format "'[' \ssum_ i '/  '  F ']'").
Reserved Notation "\ssum_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50, only parsing).
Reserved Notation "\ssum_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
  format "'[' \ssum_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\ssum_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
  format "'[' \ssum_ ( i  <  n ) '/  '  F ']'").

Declare Scope convex_scope.
Declare Scope ordered_convex_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.

Section tmp.
Local Open Scope proba_scope.
Variables (n m : nat) (d1 : {fdist 'I_n}) (d2 : {fdist 'I_m}) (p : prob).
Lemma ConvnFDist_Add (A : finType) (g : 'I_n -> fdist A) (h : 'I_m -> fdist A) :
  ConvnFDist.d (AddFDist.d d1 d2 p)
    [ffun i => match fintype.split i with inl a => g a | inr a => h a end] =
  ConvFDist.d p (ConvnFDist.d d1 g) (ConvnFDist.d d2 h).
Proof.
apply/fdist_ext => a; rewrite !ConvFDist.dE !ConvnFDist.dE.
rewrite 2!big_distrr /= big_split_ord /=; congr (_ + _)%R;
  apply eq_bigr => i _; rewrite AddFDist.dE ffunE.
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
Variables (A : finType) (n : nat) (g : 'I_n.+1 -> fdist A) (P : {fdist 'I_n.+1}).
Lemma DelDistConvex (j : 'I_n.+1) (H : (0 <= P j <= 1)%R) (Pj1 : P j != 1%R) :
  let g' := fun i : 'I_n => g (DelFDist.f j i) in
  ConvnFDist.d P g = ConvFDist.d (Prob.mk H) (g j) (ConvnFDist.d (DelFDist.d Pj1) g').
Proof.
move=> g' /=; apply/fdist_ext => a.
rewrite ConvFDist.dE /= ConvnFDist.dE (bigD1 j) //=; congr (_ + _)%R.
rewrite ConvnFDist.dE big_distrr /=.
rewrite (bigID (fun i : 'I_n.+1 => (i < j)%nat)) //= (bigID (fun i : 'I_n => (i < j)%nat)) //=; congr (_ + _)%R.
  rewrite (@big_ord_narrow_cond _ _ _ j n.+1); first by rewrite ltnW.
  move=> jn; rewrite (@big_ord_narrow_cond _ _ _ j n xpredT); first by rewrite -ltnS.
  move=> jn'.
  apply/eq_big.
  by move=> /= i; apply/negP => /eqP/(congr1 val) /=; apply/eqP; rewrite ltn_eqF.
  move=> /= i _.
  rewrite DelFDist.dE /= ltn_ord D1FDist.dE /= ifF /=; last first.
    by apply/negP => /eqP/(congr1 val) /=; apply/eqP; rewrite ltn_eqF.
  rewrite mulRA mulRCA mulRV ?mulR1 ?onem_neq0 //.
  congr (P _ * _)%R; first exact/val_inj.
  rewrite /g' /DelFDist.f /= ltn_ord; congr (g _ a); exact/val_inj.
rewrite (eq_bigl (fun i : 'I_n.+1 => (j < i)%nat)); last first.
  move=> i; by rewrite -leqNgt eq_sym -ltn_neqAle.
rewrite (eq_bigl (fun i : 'I_n => (j <= i)%nat)); last first.
  move=> i; by rewrite -leqNgt.
rewrite big_mkcond.
rewrite big_ord_recl ltn0 /= add0R.
rewrite [in RHS]big_mkcond.
apply eq_bigr => i _.
rewrite /bump add1n ltnS; case: ifPn => // ji.
rewrite DelFDist.dE D1FDist.dE ltnNge ji /= ifF; last first.
  apply/eqP => /(congr1 val) => /=.
  rewrite /bump add1n => ij.
  move: ji; apply/negP; by rewrite -ij ltnn.
rewrite /Rdiv mulRAC [in RHS] mulRC -mulRA mulVR // ?mulR1 ?onem_neq0 //.
by rewrite /g' /DelFDist.f ltnNge ji.
Qed.
End tmp2.

(* technical device *)
Module CodomDFDist.
Section def.
Local Open Scope classical_set_scope.
Variables (A : Type) (n : nat) (g : 'I_n -> A) (e : {fdist 'I_n}) (y : set A).
Definition f := [ffun i : 'I_n => if g i \in y then e i else 0%R].
Lemma f0 i : (0 <= f i)%R.
Proof. rewrite /f ffunE; case: ifPn => _ //; exact/leRR. Qed.
Lemma f1 (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, x (g i) -> e i = 0%R) :
  (\sum_(i < n) f i = 1)%R.
Proof.
rewrite /f -(FDist.f1 e) /=.
apply eq_bigr => i _; rewrite ffunE.
case: ifPn => // /negP; rewrite in_setE => ygi.
rewrite ge //.
have : (x `|` y) (g i) by apply/gX; by exists i.
by case.
Qed.
Definition d (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, x (g i) -> e i = 0%R) : {fdist 'I_n} :=
  locked (FDist.make f0 (f1 gX ge)).
Lemma dE (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, x (g i) -> e i = 0%R) i :
  d gX ge i = if g i \in y then e i else 0%R.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
Lemma f1' (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, (x (g i)) /\ (~ y (g i)) -> e i = 0%R) :
  (\sum_(i < n) f i = 1)%R.
Proof.
rewrite /f -(FDist.f1 e) /=; apply eq_bigr => i _; rewrite ffunE.
case: ifPn => // /negP; rewrite in_setE => giy.
rewrite ge //.
have : (x `|` y) (g i) by apply/gX; by exists i.
by case.
Qed.
Definition d' (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, (x (g i)) /\ (~ y (g i)) -> e i = 0%R) :=
  locked (FDist.make f0 (f1' gX ge)).
Lemma dE' (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, (x (g i)) /\ (~ y (g i)) -> e i = 0%R) i :
  d' gX ge i = if g i \in y then e i else 0%R.
Proof. by rewrite /d'; unlock; rewrite ffunE. Qed.
End def.
End CodomDFDist.

Module ConvexSpace.
Record class_of (T : choiceType) : Type := Class {
  conv : prob -> T -> T -> T where "a <| p |> b" := (conv p a b);
  _ : forall a b, a <| `Pr 1 |> b = a ;
  _ : forall p a, a <| p |> a = a ;
  _ : forall p a b, a <| p |> b = b <| `Pr p.~ |> a;
  _ : forall (p q : prob) (a b c : T),
      a <| p |> (b <| q |> c) = (a <| [r_of p, q] |> b) <| [s_of p, q] |> c
}.
Structure t : Type := Pack { car : choiceType ; class : class_of car }.
Module Exports.
Definition Conv (T : t) : prob -> car T -> car T -> car T :=
  match T return prob -> car T -> car T -> car T with Pack _ (Class x _ _ _ _) => x end.
Arguments Conv {T} : simpl never.
Notation "x <| p |> y" := (Conv p x y) : convex_scope.
Notation convType := t.
Coercion car : convType >-> choiceType (*Sortclass*).
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

Definition sum_of_scaled_pt (m : scaled_pt) : Rpos * A + unit :=
  match m with Scaled r a => inl _ (r, a) | Zero => inr _ tt end.

Definition scaled_pt_of_sum (m : (Rpos * A) + unit) :=
  match m with inl p => Scaled p.1 p.2 | inr n => Zero end.

Lemma sum_of_scaled_ptK : cancel sum_of_scaled_pt scaled_pt_of_sum.
Proof. by case. Qed.

Definition scaled_pt_eqMixin := CanEqMixin sum_of_scaled_ptK.
Canonical scaled_pt_eqType := Eval hnf in EqType scaled_pt scaled_pt_eqMixin.
Definition scaled_pt_choiceMixin := CanChoiceMixin sum_of_scaled_ptK.
Canonical scaled_pt_choiceType := Eval hnf in ChoiceType scaled_pt scaled_pt_choiceMixin.

Local Notation "a *: v" := (Scaled a v).

Definition S1 x : [choiceType of scaled_pt] := `Pos 1 *: x.

Lemma Scaled_inj p : injective (Scaled p).
Proof. by move=> x y []. Qed.

Definition S1_inj : injective S1 := @Scaled_inj Rpos1.

Definition raw_weight pt : R :=
  if pt is r *: _ then r else 0.

Lemma weight_ge0 pt : 0 <= raw_weight pt.
Proof. case: pt => /= [[x] /= /ltRP/ltRW //|]; by apply leRR. Qed.

Definition weight := mkPosFun weight_ge0.

Definition point pt : weight pt > 0 -> A.
destruct pt as [t c|].
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

Local Notation "\ssum_ ( i <- r ) F" := (\big[addpt/Zero]_(i <- r) F).
Local Notation "\ssum_ ( i : t ) F" := (\big[addpt/Zero]_(i : t) F).
Local Notation "\ssum_ i F" := (\big[addpt/Zero]_i F).
Local Notation "\ssum_ ( i < n | P ) F" := (\big[addpt/Zero]_(i < n | P%B) F).
Local Notation "\ssum_ ( i < n ) F" := (\big[addpt/Zero]_(i < n) F).

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
rewrite convA; congr Conv; first exact: s_of_Rpos_probA.
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

Lemma scalept_rsum (B : finType) (F : B ->R^+) x :
  scalept (\sum_(i : B) (F i)) x = \ssum_b scalept (F b) x.
Proof.
apply (@proj1 _ (0 <= \sum_(i : B) F i)).
apply (big_ind2 (fun y q => scalept q x = y /\ 0 <= q)).
+ by rewrite scalept0.
+ move=> x1 x2 y1 y2 [Hx1 Hx2] [Hy1 Hy2].
  rewrite -Hx1 -Hy1 scalept_addR //; split => //; exact: addR_ge0.
+ move=> i _; split => //; exact/pos_f_ge0.
Qed.

Definition scaled_conv p x y := addpt (scalept p x) (scalept p.~ y).
Definition Scaled_convMixin : ConvexSpace.class_of [choiceType of scaled_pt].
apply (@ConvexSpace.Class _ scaled_conv); rewrite /scaled_conv /=.
+ by move=> a b; rewrite onem1 scalept1 scalept0 addpt0.
+ by move=> a p; rewrite -scalept_addR // onemKC scalept1.
+ move=> a b p; by rewrite [RHS]addptC onemK.
+ move=> p q a b c.
  rewrite !scalept_addpt ?scalept_comp // -[RHS]addptA; congr addpt.
    by rewrite (p_is_rs p q) mulRC.
  by rewrite pq_is_rs mulRC s_of_pqE onemK.
Defined.
Canonical Scaled_convType := ConvexSpace.Pack Scaled_convMixin.

Definition barycenter (pts : seq scaled_pt) := \ssum_(x <- pts) x.

Lemma barycenter_big_fin (T : finType) (F : T -> scaled_pt) :
  barycenter [seq F i | i <- enum T] = \ssum_i F i.
Proof. by rewrite /barycenter big_map big_filter. Qed.

Lemma weight_bary pts : weight (barycenter pts) = \sum_(x <- pts) weight x.
Proof. by rewrite (big_morph weight weight_addpt weight0). Qed.

Lemma scalept_bary p (H : 0 <= p) pts :
  scalept p (barycenter pts) = barycenter (map (scalept p) pts).
Proof. by rewrite big_scalept /barycenter big_map. Qed.

Lemma barycenter_perm n (F : 'I_n -> scaled_pt) (pe : 'S_n) :
  \ssum_(i < n) F i = \ssum_(i < n) F (pe i).
Proof.
rewrite -!barycenter_big_fin /barycenter big_map map_comp big_map.
exact/perm_big/perm_eq_perm.
Qed.

Section convfdist.
Variables n m : nat.
Variable p : {fdist 'I_n}.
Variable q : 'I_n -> {fdist 'I_m}.
Variable h : 'I_m -> scaled_pt.

Lemma barycenter_convnfdist :
  \ssum_(i < n) scalept (p i) (\ssum_(j < m) scalept (q i j) (h j)) =
  \ssum_(j < m) scalept (ConvnFDist.d p q j) (h j).
Proof.
rewrite (eq_bigr _ (fun i _ => big_scalept (p i) _ _ _)).
rewrite exchange_big /=; apply eq_bigr => j _; rewrite ConvnFDist.dE.
have HF : forall i, 0 <= p i * q i j by move=> i; apply/mulR_ge0.
rewrite (scalept_rsum (mkPosFun HF)) /=; apply eq_bigr => i _.
by rewrite scalept_comp.
Qed.
End convfdist.

Section adjunction.
Variable p : prob.

Lemma adjunction_1 a b :
  addpt (scalept 1 (S1 a)) (scalept 0 (S1 b)) = S1 (a <|`Pr 1|> b).
Proof. by rewrite scalept0 scalept1 addpt0 conv1. Qed.

Lemma adjunction_2 x y :
  addpt (scalept p (S1 x)) (scalept p.~ (S1 y)) = S1 (x <| p |> y).
Proof.
case/Prob.ge0: p => Hp; last first.
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

Notation "\ssum_ ( i <- r | P ) F" :=
  (\big[(@ScaledConvex.addpt _)/(@ScaledConvex.Zero _)]_(i <- r | P%B) F) : convex_scope.
Notation "\ssum_ ( i <- r ) F" :=
  (\big[(@ScaledConvex.addpt _)/(@ScaledConvex.Zero _)]_(i <- r) F) : convex_scope.
Notation "\ssum_ ( i : t ) F" :=
  (\big[(@ScaledConvex.addpt _)/(@ScaledConvex.Zero _)]_(i : t) F) : convex_scope.
Notation "\ssum_ ( i | P ) F" :=
  (\big[(@ScaledConvex.addpt _)/(@ScaledConvex.Zero _)]_(i | P%B) F) : convex_scope.
Notation "\ssum_ i F" :=
  (\big[(@ScaledConvex.addpt _)/(@ScaledConvex.Zero _)]_i F) : convex_scope.
Notation "\ssum_ ( i < n | P ) F" :=
  (\big[ScaledConvex.addpt/ScaledConvex.Zero]_(i < n | P%B) F) : convex_scope.
Notation "\ssum_ ( i < n ) F" :=
  (\big[(@ScaledConvex.addpt _)/(@ScaledConvex.Zero _)]_(i < n) F) : convex_scope.

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
  apply prob_ext => /=; by rewrite s_of_pqE -H2 onemK.
by rewrite (@r_of_pq_is_r  _ _ r s).
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
rewrite !scalept_addpt ?scalept_comp //.
rewrite !(mulRC p) !(mulRC p.~) addptA addptC (addptC (scalept (q*p) _)).
rewrite !addptA -addptA -!scalept_comp -?scalept_addpt //.
by rewrite !(addptC (scalept _.~ _)) !S1_conv.
Qed.

Lemma convDr (x y z : A) (p q : prob) :
  x <| p |> (y <| q |> z) = (x <| p |> y) <| q |> (x <| p |> z).
Proof. by rewrite -{1}(convmm x q) commute. Qed.

Local Open Scope vec_ext_scope.

Fixpoint Convn n : {fdist 'I_n} -> ('I_n -> A) -> A :=
  match n return forall (e : {fdist 'I_n}) (g : 'I_n -> A), A with
  | O => fun e g => False_rect A (fdistI0_False e)
  | m.+1 => fun e g =>
    match eqVneq (e ord0) 1%R with
    | left _ => g ord0
    | right H => let G := fun i => g (DelFDist.f ord0 i) in
      g ord0 <| probfdist e ord0 |> Convn (DelFDist.d H) G
    end
  end.

Local Notation "'\Conv_' d f" := (Convn d f).

Section with_affine_projection.
Variable B : convType.
Variable prj : A -> B.
Hypothesis prj_affine : forall p, {morph prj : x y / x <|p|> y >-> x <|p|> y}.

Definition map_scaled (x : [choiceType of scaled_pt A]) : [choiceType of scaled_pt B] :=
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
  \ssum_(i < n) scalept (d i) (S1 (prj (points i))).
Proof.
elim: n points d => [|n IH] points d.
  move: (FDist.f1 d); rewrite /= big_ord0 => /Rlt_not_eq; elim.
  exact: Rlt_0_1.
rewrite /=.
case: eqVneq => Hd.
  rewrite (bigD1 ord0) ?inE // Hd big1 /=.
    rewrite addpt0 (scalept_gt0 _ _ Rlt_0_1).
    by congr Scaled; apply val_inj; rewrite /= mulR1.
  move=> i Hi; have := FDist.f1 d.
  rewrite (bigD1 ord0) ?inE // Hd /= addRC => /(f_equal (Rminus^~ R1)).
  rewrite addRK subRR => /prsumr_eq0P -> //.
  by rewrite scalept0.
set d' := DelFDist.d Hd.
set points' := fun i => points (DelFDist.f ord0 i).
rewrite /index_enum -enumT (bigD1_seq ord0) ?enum_uniq ?mem_enum //=.
rewrite -big_filter (perm_big (map (lift ord0) (enum 'I_n)));
  last by apply perm_filter_enum_ord.
rewrite prj_affine S1_conv; congr addpt.
rewrite IH -barycenter_big_fin scalept_bary //.
rewrite /barycenter 2!big_map [in RHS]big_map.
apply eq_bigr => i _.
rewrite scalept_comp // DelFDist.dE D1FDist.dE /=.
rewrite /Rdiv (mulRC (d _)) mulRA mulRV ?mul1R //.
by move: (Hd); apply contra => /eqP Hd'; rewrite -onem0 -Hd' onemK.
Qed.
End with_affine_projection.

Lemma S1_convn n (points : 'I_n -> A) d :
  S1 (\Conv_d points) = \ssum_(i < n) scalept (d i) (S1 (points i)).
Proof. by rewrite (@S1_convn_proj _ (@id A)). Qed.

Lemma eq_convn n g1 g2 (d1 d2 : {fdist 'I_n}) :
  g1 =1 g2 -> d1 =1 d2 -> \Conv_d1 g1 = \Conv_d2 g2.
Proof.
move=> Hg Hd; apply S1_inj; rewrite !S1_convn.
apply congr_big => // i _; by rewrite Hg Hd.
Qed.

Lemma convn_proj n g (d : {fdist 'I_n}) i : d i = R1 -> \Conv_d g = g i.
Proof.
move=> Hd; apply S1_inj.
rewrite S1_convn (bigD1 i) ?inE //=.
rewrite big1; first by rewrite addpt0 Hd scalept1.
move=> j Hj.
move/eqP/FDist1.P: Hd => -> //; by rewrite scalept0.
Qed.

Lemma ConvnFDist1 (n : nat) (j : 'I_n) (g : 'I_n -> A): \Conv_(FDist1.d j) g = g j.
Proof. by apply convn_proj; rewrite FDist1.dE eqxx. Qed.

Lemma convn1E g (e : {fdist 'I_1}) : \Conv_ e g = g ord0.
Proof.
rewrite /=; case: eqVneq => [//|H]; exfalso; move/eqP: H; apply.
by apply/eqP; rewrite FDist1.dE1 (FDist1.I1 e).
Qed.

Lemma convnE n g (d : {fdist 'I_n.+1}) (i1 : d ord0 != 1%R) :
  \Conv_d g = g ord0 <| probfdist d ord0 |> \Conv_(DelFDist.d i1) (fun x => g (DelFDist.f ord0 x)).
Proof.
rewrite /=; case: eqVneq => /= H.
exfalso; by rewrite H eqxx in i1.
by rewrite (eq_irrelevance H i1).
Qed.

Lemma convn2E g (d : {fdist 'I_2}) :
  \Conv_d g = g ord0 <| probfdist d ord0 |> g (lift ord0 ord0).
Proof.
case/boolP : (d ord0 == 1%R) => [|i1].
  rewrite FDist1.dE1 => /eqP ->; rewrite ConvnFDist1.
  rewrite (_ : probfdist _ _ = `Pr 1) ?conv1 //.
  by apply prob_ext => /=; rewrite FDist1.dE eqxx.
rewrite convnE; congr (_ <| _ |> _).
by rewrite convn1E /DelFDist.f ltnn.
Qed.

(* ref: M.H.Stone, postulates for the barycentric calculus, lemma 2 *)
Lemma Convn_perm (n : nat) (d : {fdist 'I_n}) (g : 'I_n -> A) (s : 'S_n) :
  \Conv_d g = \Conv_(PermFDist.d d s) (g \o s).
Proof.
apply S1_inj; rewrite !S1_convn (barycenter_perm _ s).
apply eq_bigr => i _; by rewrite PermFDist.dE.
Qed.

(* ref: M.H.Stone, postulates for the barycentric calculus, lemma 4 *)
Theorem Convn_convnfdist (n m : nat) (d : {fdist 'I_n})
        (e : 'I_n -> {fdist 'I_m}) (x : 'I_m -> A) :
  \Conv_d (fun i => \Conv_(e i) x) = \Conv_(ConvnFDist.d d e) x.
Proof.
apply S1_inj; rewrite !S1_convn -barycenter_convnfdist.
apply eq_bigr => i _; by rewrite S1_convn.
Qed.

Local Open Scope R_scope.

Lemma convn_const (a : A) :
  forall (n : nat) (d : {fdist 'I_n}), \Conv_d (fun _ => a) = a.
Proof.
elim; first by move=> d; move/fdistI0_False: (d).
move=> n IHn d.
case/boolP: (d ord0 == 1); first by move/eqP/(convn_proj (fun _ => a)).
by move=> d0n0; rewrite convnE IHn convmm.
Qed.

Lemma convnDr :
  forall (n : nat) (p : prob) (x : A) (g : 'I_n -> A) (d : {fdist 'I_n}),
    x <|p|> \Conv_d g = \Conv_d (fun i : 'I_n => x <|p|> g i).
Proof.
elim; first by move=> p x g d; move/fdistI0_False: (d).
move=> n IHn p x g d.
case/boolP: (d ord0 == 1); first by move/eqP=> d01; rewrite (convn_proj g d01) (convn_proj (fun i => x <|p|> g i) d01).
move=> d0n1.
rewrite !convnE !IHn.
congr Convn; apply funext=> i.
by rewrite convDr.
Qed.

End convex_space_prop.

Notation "'\Conv_' d f" := (Convn d f) : convex_scope.

Section is_convex_set.
Local Open Scope classical_set_scope.
Variable A : convType.

Definition is_convex_set (D : set A) : bool :=
  `[<forall x y t, D x -> D y -> D (x <| t |> y)>].

Lemma is_convex_set0 : is_convex_set set0.
Proof. exact/asboolP. Qed.

Lemma is_convex_set1 a : is_convex_set [set a].
Proof. by apply/asboolP => x y p /= => -> ->; rewrite convmm. Qed.

Lemma is_convex_setT : is_convex_set setT.
Proof. exact/asboolP. Qed.

Definition is_convex_set_n (X : set A) : bool :=
  `[< forall n (g : 'I_n -> A) (d : {fdist 'I_n}), g @` setT `<=` X -> X (\Conv_d g) >].

Lemma is_convex_setP (X : set A) : is_convex_set X = is_convex_set_n X.
Proof.
apply/idP/idP => H; apply/asboolP; last first.
  move=> x y p xX yX.
  case/boolP : (p == `Pr 1) => [/eqP ->|p1]; first by rewrite conv1.
  set g : 'I_2 -> A := fun i => if i == ord0 then x else y.
  have gX : g @` setT `<=` X by move=> a -[i _ <-]; rewrite /g; case: ifPn.
  move/asboolP : H => /(_ _ g (I2FDist.d p) gX).
  rewrite convnE; first by rewrite I2FDist.dE eqxx.
  move=> p1'.
  rewrite {1}/g eqxx (_ : probfdist _ _ = p); last first.
    by apply prob_ext => /=; rewrite I2FDist.dE eqxx.
  by rewrite (_ : \Conv_ _ _ = y) // (_ : (fun _ => _) = (fun=> y)) ?convn1E.
elim => [g d|n IH g d]; first by move: (fdistI0_False d).
destruct n as [|n] => gX.
  rewrite {IH} (@convn_proj _ _ _ _ ord0) //.
  exact/gX/classical_sets.imageP.
  by apply/eqP; rewrite FDist1.dE1 (FDist1.I1 d).
case/boolP : (d ord0 == 1%R) => [/eqP|]d01.
  suff -> : \Conv_d g = g ord0 by apply gX; exists ord0.
  by rewrite (@convn_proj _ _ _ _ ord0).
set D : {fdist 'I_n.+1} := DelFDist.d d01.
pose G (i : 'I_n.+1) : A := g (DelFDist.f (@ord0 _) i).
have : G @` setT `<=` X.
  by move=> x -[i _ <-{x}]; rewrite /G /DelFDist.f ltn0; apply gX; exists ((lift ord0 i)).
move/(IH _ D) => {}IH.
rewrite convnE //.
move/asboolP : H; apply => //; exact/gX/classical_sets.imageP.
Qed.
End is_convex_set.

Section hull_def.
Local Open Scope classical_set_scope.
Definition hull (T : convType) (X : set T) : set T :=
  [set p : T | exists n (g : 'I_n -> T) d, g @` setT `<=` X /\ p = \Conv_d g].
End hull_def.

Section hull_prop.
Variable A : convType.
Implicit Types X Y : set A.
Implicit Types a : A.
Lemma subset_hull X : (X `<=` hull X)%classic.
Proof.
move=> x xX; rewrite /hull; exists 1, (fun=> x), (FDist1.d ord0).
split => [d [i _ <-] //|]; by rewrite convn1E.
Qed.
Lemma hull0 : hull set0 = set0 :> set A.
Proof.
rewrite funeqE => d; rewrite propeqE; split => //.
move=> [n [g [e [gX ->{d}]]]].
destruct n as [|n]; first by move: (fdistI0_False e).
exfalso; apply: (gX (g ord0)); exact/imageP.
Qed.
Lemma hull_eq0 X : (hull X == set0) = (X == set0).
Proof.
apply/idP/idP=> [/eqP abs|]; last by move=> /eqP ->; rewrite hull0.
apply/negPn/negP => /set0P[/= d] => dX.
move: abs; rewrite funeqE => /(_ d); rewrite propeqE /set0 => -[H _]; apply H.
exact/subset_hull.
Qed.
Lemma mem_hull_setU X Y a0 a1 p : X a0 -> Y a1 -> (hull (X `|` Y)) (a0 <| p |> a1).
Proof.
move=> a0X a1y.
exists 2, (fun i => if i == ord0 then a0 else a1), (I2FDist.d p); split => /=.
  move=> a2.
  case => i _ <-{a2} /=.
  case: ifPn => _; [by left | by right].
case: eqVneq => [|H].
  rewrite I2FDist.dE eqxx /= => p1.
  suff -> : p = `Pr 1 by rewrite conv1.
  exact/prob_ext.
congr (_ <| _ |> _); first by apply prob_ext => /=; rewrite I2FDist.dE eqxx.
case: eqVneq => H' //.
exfalso.
move: H'; rewrite DelFDist.dE D1FDist.dE (eq_sym (lift _ _)) (negbTE (neq_lift _ _)).
rewrite I2FDist.dE (eq_sym (lift _ _)) (negbTE (neq_lift _ _)) I2FDist.dE eqxx divRR ?eqxx //.
by move: H; rewrite I2FDist.dE eqxx onem_neq0.
Qed.
End hull_prop.

(* NB: was duplicate in monae_lib.v before *)
Section choice_cast.

Definition equality_mixin_of_Type (T : Type) : Equality.mixin_of T :=
  EqMixin (fun x y : T => boolp.asboolP (x = y)).

Definition choice_of_Type (T : Type) : choiceType :=
  Choice.Pack (Choice.Class (equality_mixin_of_Type T) boolp.gen_choiceMixin).

Definition choice_of_Object {T} (t : T) : choice_of_Type T := t.

End choice_cast.

Module CSet.
Section cset.
Variable A : convType.
Record class_of (X : set A) : Type := Class { _ : is_convex_set X }.
Record t : Type := Pack { car : set A ; class : class_of car }.
End cset.
Module Exports.
Notation convex_set := t.
Coercion car : convex_set >-> set.
End Exports.
End CSet.
Export CSet.Exports.

Definition convex_set_of (A : convType) :=
  fun phT : phant (ConvexSpace.car A) => convex_set A.
Notation "{ 'convex_set' T }" := (convex_set_of (Phant T)) : convex_scope.

Section cset_canonical.
Variable (A : convType).
Canonical cset_predType := Eval hnf in
  PredType (fun t : convex_set A => (fun x => x \in CSet.car t)).
Canonical cset_eqType := Equality.Pack (equality_mixin_of_Type (convex_set A)).
Canonical cset_choiceType := choice_of_Type (convex_set A).
End cset_canonical.

Section CSet_interface.
Variable (A : convType).
Implicit Types X Y : {convex_set A}.
Lemma convex_setP X : is_convex_set X.
Proof. by case: X => X []. Qed.
Lemma cset_ext X Y : X = Y :> set _ -> X = Y.
Proof.
move: X Y => -[X HX] [Y HY] /= ?; subst Y.
congr (CSet.Pack _); exact/Prop_irrelevance.
Qed.
End CSet_interface.

Section CSet_prop.
Local Open Scope classical_set_scope.
Import ScaledConvex.
Variable A : convType.
Implicit Types X Y : {convex_set A}.
Implicit Types a : A.
Implicit Types x y : scaled_pt A.

Lemma mem_convex_set a1 a2 p X : a1 \in X -> a2 \in X -> a1 <|p|> a2 \in X.
Proof.
case: X => X [convX]; move: (convX) => convX_save.
move/asboolP : convX => convX Hx Hy.
by rewrite in_setE; apply: convX; rewrite -in_setE.
Qed.

Definition cset0 : {convex_set A} := CSet.Pack (CSet.Class (is_convex_set0 A)).

Lemma cset0P X : (X == cset0) = (X == set0 :> set _).
Proof.
case: X => x [Hx] /=; apply/eqP/eqP => [-[] //| ?]; subst x; exact: cset_ext.
Qed.

Lemma cset0PN X : X != cset0 <-> X !=set0.
Proof.
rewrite cset0P; case: X => //= x Hx; split; last first.
  case=> a xa; apply/eqP => x0; move: xa; by rewrite x0.
by case/set0P => /= d dx; exists d.
Qed.

Definition cset1 a : {convex_set A} := CSet.Pack (CSet.Class (is_convex_set1 a)).

Lemma cset1_neq0 a : cset1 a != cset0.
Proof. by apply/cset0PN; exists a. Qed.

Lemma hull_cset X : hull X = X.
Proof.
rewrite predeqE => d; split; last exact/subset_hull.
move=> -[n [g [e [gX ->{d}]]]].
move: (convex_setP X); rewrite is_convex_setP /is_convex_set_n.
by move=> /asboolP/(_ _ g e gX).
Qed.

Lemma split_lshift n m (i : 'I_n) : fintype.split (lshift m i) = inl i.
Proof. by rewrite -/(unsplit (inl i)) unsplitK. Qed.
Lemma split_rshift n m (i : 'I_m) : fintype.split (rshift n i) = inr i.
Proof. by rewrite -/(unsplit (inr i)) unsplitK. Qed.

Lemma AddFDist_conv n m p (g : 'I_(n+m) -> A)(d : {fdist 'I_n})(e : {fdist 'I_m}) :
  \Conv_(AddFDist.d d e p) g =
  \Conv_d (g \o @lshift n m) <|p|> \Conv_e (g \o @rshift n m).
Proof.
apply S1_inj; rewrite S1_conv !S1_convn.
rewrite /Conv /= /scaled_conv big_split_ord !big_scalept /=.
congr addpt; apply eq_bigr => i _;
  rewrite (scalept_comp (S1 _) (Prob.ge0 _) (FDist.ge0 _ _));
  by rewrite AddFDist.dE (split_lshift,split_rshift).
Qed.

Lemma hull_is_convex (Z : set A) : is_convex_set (hull Z).
Proof.
apply/asboolP => x y p [n [g [d [gX ->{x}]]]] [m [h [e [hX ->{y}]]]].
exists (n + m).
exists [ffun i => match fintype.split i with inl a => g a | inr a => h a end].
exists (AddFDist.d d e p).
split.
  move=> a -[i _]; rewrite ffunE.
  case: splitP => j _ <-; by [apply gX; exists j | apply hX; exists j].
rewrite AddFDist_conv; congr Conv; apply eq_convn => i //=;
  by rewrite ffunE (split_lshift,split_rshift).
Qed.
Canonical hull_is_convex_set (Z : set A) : convex_set A :=
  CSet.Pack (CSet.Class (hull_is_convex Z)).

Definition scaled_set (Z : set A) :=
  [set x | if x is p *: a then Z a else True].

Lemma addpt_scaled_set X x y :
  x \in scaled_set X -> y \in scaled_set X -> addpt x y \in scaled_set X.
Proof.
case: x => [p x|]; case: y => [q y|] //=; exact: mem_convex_set.
Qed.

Lemma scalept_scaled_set X r x :
  x \in scaled_set X -> scalept r x \in scaled_set X.
Proof.
rewrite /scalept; case: Rlt_dec => //= Hr; by [case: x | rewrite !in_setE].
Qed.

Lemma scaled_set_extract X x (H : (0 < weight _ x)%R) :
  x \in scaled_set X -> point H \in X.
Proof. case: x H => [p x|/ltRR] //=; by rewrite in_setE. Qed.

Lemma hull_setU (a : A) X Y : X !=set0 -> Y !=set0 -> (hull (X `|` Y)) a ->
  exists a1, a1 \in X /\ exists a2, a2 \in Y /\ exists p : prob, a = a1 <| p |> a2.
Proof.
move=> [dx dx_x] [dy dy_y].
case=> n -[g [e [gX Ha]]].
suff : exists x1, x1 \in scaled_set X /\ exists x2, x2 \in scaled_set Y /\
    S1 a = addpt x1 x2.
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
rewrite (bigID (fun i => g i \in X)) /=.
set sa1 := \big[_/_]_(i < n | _) _.
set sa2 := \big[_/_]_(i < n | _) _.
move=> Hsa.
exists sa1; split.
  rewrite /sa1; apply big_ind.
  + by rewrite in_setE.
  + apply addpt_scaled_set.
  + move=> i Hi; exact: scalept_scaled_set.
exists sa2; split.
  rewrite /sa2; apply big_ind.
  + by rewrite in_setE.
  + apply addpt_scaled_set.
  + move=> i Hi; apply scalept_scaled_set.
    rewrite -[_ \in _]orFb -(negbTE Hi).
    apply/orP; rewrite 2!in_setE; exact/gX/imageP.
by [].
Qed.
End CSet_prop.

Section R_convex_space.
Implicit Types p q : prob.
Definition avg p a b := (p * a + p.~ * b)%R.
Lemma avg1 a b : avg (`Pr 1) a b = a.
Proof. by rewrite /avg /= mul1R onem1 mul0R addR0. Qed.
Lemma avgI p x : avg p x x = x.
Proof. by rewrite /avg -mulRDl onemKC mul1R. Qed.
Lemma avgC p x y : avg p x y = avg (`Pr p.~) y x.
Proof. by rewrite /avg onemK addRC. Qed.
Lemma avgA p q (d0 d1 d2 : R) :
  avg p d0 (avg q d1 d2) = avg [s_of p, q] (avg [r_of p, q] d0 d1) d2.
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
Lemma avg_oppD p x y : (- x <| p |> - y = - (x <| p |> y))%R.
Proof. by rewrite /Conv /= /avg 2!mulRN -oppRD. Qed.
Lemma avg_mulDr p : right_distributive Rmult (fun x y => x <| p |> y).
Proof. by move=> x ? ?; rewrite /Conv /= /avg mulRDr mulRCA (mulRCA x). Qed.
Lemma avg_mulDl p : left_distributive Rmult (fun x y => x <| p |> y).
Proof. by move=> x ? ?; rewrite /Conv /= /avg mulRDl -mulRA -(mulRA p.~). Qed.
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
Lemma scaleR_scalept r x : (0 <= r -> scaleR (scalept r x) = r * scaleR x)%R.
Proof.
case: x => [q y|]; last by rewrite scaleptR0 mulR0.
case=> r0. by rewrite scalept_gt0 /= mulRA.
by rewrite -r0 scalept0 mul0R.
Qed.
Definition big_scaleR := big_morph scaleR scaleR_addpt scaleR0.
Definition avgn n (g : 'I_n -> R) (e : {fdist 'I_n}) := (\sum_(i < n) e i * g i)%R.
Lemma avgnE n (g : 'I_n -> R) e : \Conv_e g = avgn g e.
Proof.
rewrite -[LHS]Scaled1RK S1_convn big_scaleR.
by apply eq_bigr => i _; rewrite scaleR_scalept // Scaled1RK.
Qed.
End R_convex_space.

Module Funavg.
Section funavg.
Variables (A : choiceType) (B : convType).
Let T := A -> B.
Implicit Types p q : prob.
Definition avg p (x y : T) := fun a : A => (x a <| p |> y a).
Lemma avg1 (x y : T) : avg (`Pr 1) x y = x.
Proof. rewrite funeqE => a; exact/conv1. Qed.
Lemma avgI p (x : T) : avg p x x = x.
Proof. rewrite funeqE => a; exact/convmm. Qed.
Lemma avgC p (x y : T) : avg p x y = avg (`Pr p.~) y x.
Proof. rewrite funeqE => a; exact/convC. Qed.
Lemma avgA p q (d0 d1 d2 : T) :
  avg p d0 (avg q d1 d2) = avg [s_of p, q] (avg [r_of p, q] d0 d1) d2.
Proof. move=> *; rewrite funeqE => a; exact/convA. Qed.
End funavg.
End Funavg.

Section fun_convex_space.
Variables (A : choiceType) (B : convType).

Definition funConvMixin := ConvexSpace.Class
  (@Funavg.avg1 A B) (@Funavg.avgI A B) (@Funavg.avgC A B) (@Funavg.avgA A B).
Canonical funConvType := ConvexSpace.Pack funConvMixin.

End fun_convex_space.

From mathcomp Require Import topology.

(* TODO: move to topology? *)
Section depfun.
Variable (I : Type) (T : I -> choiceType).
Definition depfun_choiceClass :=
  Choice.Class (Equality.class (dep_arrow_eqType T)) gen_choiceMixin.
Definition depfun_choiceType := Choice.Pack depfun_choiceClass.
End depfun.

Module Depfunavg.
Section depfunavg.
Variables (A : choiceType) (B : A -> convType).
Let T := depfun_choiceType B.
Implicit Types p q : prob.
Definition avg p (x y : T) := fun a : A => (x a <| p |> y a).
Lemma avg1 (x y : T) : avg (`Pr 1) x y = x.
Proof.
apply FunctionalExtensionality.functional_extensionality_dep => a; exact/conv1.
Qed.
Lemma avgI p (x : T) : avg p x x = x.
Proof.
apply FunctionalExtensionality.functional_extensionality_dep => a; exact/convmm.
Qed.
Lemma avgC p (x y : T) : avg p x y = avg (`Pr p.~) y x.
Proof.
apply FunctionalExtensionality.functional_extensionality_dep => a; exact/convC.
Qed.
Lemma avgA p q (d0 d1 d2 : T) :
  avg p d0 (avg q d1 d2) = avg [s_of p, q] (avg [r_of p, q] d0 d1) d2.
Proof.
move => *.
apply FunctionalExtensionality.functional_extensionality_dep => a; exact/convA.
Qed.
End depfunavg.
End Depfunavg.

Section depfun_convex_space.
Variables (A : choiceType) (B : A -> convType).

Definition depfunConvMixin := ConvexSpace.Class
  (@Depfunavg.avg1 A B) (@Depfunavg.avgI A B) (@Depfunavg.avgC A B) (@Depfunavg.avgA A B).
Canonical depfunConvType := ConvexSpace.Pack depfunConvMixin.

End depfun_convex_space.

Module Pairavg.
Section pairavg.
Variables (A B : convType).
Let T := prod A B.
Implicit Types p q : prob.
Definition avg p (x y : T) := (fst x <| p |> fst y , snd x <| p |> snd y).
Lemma avg1 (x y : T) : avg (`Pr 1) x y = x.
Proof. rewrite /avg (conv1 (fst x)) (conv1 (snd x)); by case x. Qed.
Lemma avgI p (x : T) : avg p x x = x.
Proof. rewrite /avg (convmm (fst x)) (convmm (snd x)); by case x. Qed.
Lemma avgC p (x y : T) : avg p x y = avg (`Pr p.~) y x.
Proof. by congr (pair _ _); apply convC. Qed.
Lemma avgA p q (d0 d1 d2 : T) :
  avg p d0 (avg q d1 d2) = avg [s_of p, q] (avg [r_of p, q] d0 d1) d2.
Proof. move => *; congr (pair _ _); by apply convA. Qed.
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
Record class_of (car : choiceType) := Class {
  base : ConvexSpace.class_of car;
  mixin : mixin_of (ConvexSpace.Pack base);
}.
Structure t : Type := Pack {car : choiceType; class : class_of car}.
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
Proof.
split; [move ->; by move: lefunR |].
case=> Hfg Hgh; rewrite funeqE => a.
move : (Hfg a) (Hgh a) => Hfg' Hgh'; exact/eqconv_le.
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
Lemma A_of_TK : cancel (fun t => let: mkOpp a := t in a) mkOpp.
Proof. by case. Qed.
Definition A_of_T_eqMixin := CanEqMixin A_of_TK.
Canonical A_of_T_eqType := Eval hnf in EqType T A_of_T_eqMixin.
Definition A_of_T_choiceMixin := CanChoiceMixin A_of_TK.
Canonical A_of_T_choiceType := Eval hnf in ChoiceType T A_of_T_choiceMixin.
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
Implicit Types p q : prob.
Definition unbox (x : T) := match x with mkOpp x' => x' end.
Definition avg p a b := mkOpp (unbox a <| p |> unbox b).
Lemma avg1 a b : avg (`Pr 1) a b = a.
Proof. by case a;case b=>b' a';rewrite/avg/unbox/=conv1. Qed.
Lemma avgI p x : avg p x x = x.
Proof. by case x=>x';rewrite/avg/unbox/=convmm. Qed.
Lemma avgC p x y : avg p x y = avg (`Pr p.~) y x.
Proof. by case x;case y=>y' x'; rewrite/avg/unbox/=convC. Qed.
Lemma avgA p q d0 d1 d2 :
  avg p d0 (avg q d1 d2) = avg [s_of p, q] (avg [r_of p, q] d0 d1) d2.
Proof. by case d0;case d1;case d2=>d2' d1' d0';rewrite/avg/unbox/=convA. Qed.
Definition oppConvMixin := ConvexSpace.Class avg1 avgI avgC avgA.
End convtype.
End OppositeOrderedConvexSpace.

Section opposite_ordered_convex_space.
Import OppositeOrderedConvexSpace.
Variable A : orderedConvType.
Canonical oppConvType := ConvexSpace.Pack (oppConvMixin A).
Definition opposite_orderedConvMixin :=
  @OrderedConvexSpace.Mixin oppConvType (@leopp A) (@leoppR A) (@leopp_trans A) (@eqopp_le A).
Canonical opposite_orderedConvType :=
  OrderedConvexSpace.Pack (OrderedConvexSpace.Class opposite_orderedConvMixin).
End opposite_ordered_convex_space.
Notation "'\opp{' a '}'" := (OppositeOrderedConvexSpace.mkOpp a)
  (at level 10, format "\opp{ a }") : ordered_convex_scope.

Section opposite_ordered_convex_space_prop.
Local Open Scope ordered_convex_scope.
Import OppositeOrderedConvexSpace.
Variable A : orderedConvType.
Lemma conv_leoppD (a b : A) t : \opp{a} <|t|> \opp{b} = \opp{a <|t|> b}.
Proof. by rewrite /Conv /= /avg /unbox. Qed.
Lemma unboxK (a : A) : unbox (\opp{a}) = a.
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
Definition convex_function_at_Convn (f : A -> B) n (a : 'I_n -> A) (t : {fdist 'I_n}) :=
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
rewrite !(mul1R,mulR1,mulRN1) -oppRD onemKC.
rewrite (_ : - / (1 + 1) + (/ (1 + 1)).~ = 0); last first.
  by rewrite /onem addRCA -oppRD -div1R eps2 addRN.
rewrite mul0R leR_oppr oppR0 leRNgt; apply; exact/Rlt_0_1.
Qed.
End counterexample.
End biconvex_function.

Section concave_function_def.
Local Open Scope ordered_convex_scope.
Variables (A : convType) (B : orderedConvType).
Definition concave_function_at (f : A -> B) a b t :=
  @convex_function_at A _ (fun a => \opp{f a} : opposite_orderedConvType B) a b t.
Definition concave_function_at' (f : A -> B) a b t := (f a <| t |> f b <= f (a <| t |> b)).
Definition strictly_concavef_at (f : A -> B) := forall a b (t : prob),
  a <> b -> (0 < t < 1)%R -> concave_function_at f a b t.
Lemma concave_function_at'P f a b t : concave_function_at' f a b t <-> concave_function_at f a b t.
Proof.
by rewrite /concave_function_at'/concave_function_at/convex_function_at conv_leoppD leoppP.
Qed.
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
move: (H1 p q t) => {}H1.
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
                          (g : 'I_n -> A) (e : {fdist 'I_n}) :
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

Local Open Scope classical_set_scope.

Lemma is_convex_set_image (A B : convType) (f : {affine A -> B})
  (a : convex_set A) : is_convex_set (f @` a).
Proof.
rewrite /is_convex_set.
apply/asboolP => x y p [a0 Ha0 <-{x}] [a1 Ha1 <-{y}].
exists (a0 <|p|> a1) => //.
by rewrite -in_setE; apply/mem_convex_set; rewrite in_setE.
by rewrite (affine_functionP' f).
Qed.

Lemma is_convex_set_image' (A B : convType) (f : A -> B) (H : affine_function f)
  (a : convex_set A) : is_convex_set (f @` a).
Proof.
rewrite /is_convex_set.
apply/asboolP => x y p [a0 Ha0 <-{x}] [a1 Ha1 <-{y}]; exists (a0 <|p|> a1) => //.
by rewrite -in_setE; apply/mem_convex_set; rewrite in_setE.
by rewrite H.
Qed.

Local Close Scope classical_set_scope.

Section R_affine_function_prop.
Variables (A : convType) (f : A -> R).
Lemma R_affine_functionN : affine_function f -> affine_function (fun x => - f x)%R.
Proof.
move/affine_functionP => [H1 H2]; rewrite affine_functionP.
split => //; [exact/R_convex_functionN|exact/R_concave_functionN].
Qed.
End R_affine_function_prop.

Section convex_function_in_def.
Variables (A : convType) (D : convex_set A) (f : A -> R).
Definition convex_function_in :=
  forall a b p, a \in D -> b \in D -> convex_function_at f a b p.
Definition concave_function_in :=
  forall a b p, a \in D -> b \in D -> concave_function_at f a b p.
End convex_function_in_def.

Section fdist_convex_space.
Variable A : finType.
Definition fdist_convMixin :=
  @ConvexSpace.Class (choice_of_Type (fdist A)) (@ConvFDist.d A)
  (@ConvFDist.d1 A)
  (@ConvFDist.idempotent A)
  (@ConvFDist.skewed_commute A)
  (@ConvFDist.quasi_assoc A).
Canonical fdist_convType := ConvexSpace.Pack fdist_convMixin.
End fdist_convex_space.

(* TODO: move up? *)
Require Import fsdist.

Section FSDist_convex_space.
Variable A : choiceType.
Definition FSDist_convMixin :=
  @ConvexSpace.Class (FSDist_choiceType A) (@ConvFSDist.d A)
  (@ConvFSDist.conv1 A)
  (@ConvFSDist.convmm A)
  (@ConvFSDist.convC A)
  (@ConvFSDist.convA' A).
Canonical FSDist_convType := ConvexSpace.Pack FSDist_convMixin.

(* Reuse the morphisms from R_convex_space. *)
Import ScaledConvex finmap.
Lemma convn_convnfsdist (n : nat) (g : 'I_n -> {dist A}) (d : {fdist 'I_n}) :
  \Conv_d g = ConvnFSDist.d d g.
Proof.
apply FSDist_ext=> a; rewrite -[LHS]Scaled1RK.
rewrite (@S1_convn_proj _ _ (fun x : {dist A} => finmap.fun_of_fsfun x a));
  last first.
  move=> p x y /=; by rewrite /Conv /= ConvFSDist.dE.
rewrite big_scaleR ConvnFSDist.dE /= fsfunE.
case: ifPn => Ha.
  by apply eq_bigr => i _; rewrite scaleR_scalept // Scaled1RK.
(* TODO: extra lemmas ? *)
rewrite big1 // => i _.
move: Ha.
rewrite /ConvnFSDist.D.
move/bigfcupP => Hn.
case /boolP: (d i == R0) => Hdi.
  by rewrite (eqP Hdi) scalept0.
case /boolP: (g i a == R0) => Hgia.
  by rewrite (eqP Hgia) scaleR_scalept /= ?mulR0.
elim: Hn.
exists i.
  rewrite mem_index_enum /=.
  apply/ltRP.
  by rewrite -fdist_gt0.
by rewrite mem_finsupp.
Qed.
End FSDist_convex_space.

(* TODO *)
Section fsdist_ordered_convex_space.
Variable A : choiceType.
Definition fsdist_orderedConvMixin := @OrderedConvexSpace.Mixin (FSDist_convType A).
End fsdist_ordered_convex_space.

(*
Lemma Conv2DistdE (A : choiceType) (a b : Dist A) (p : prob) (x : A) :
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

TODO: see convex_type.v
*)

Section convex_set_R.

Lemma Rpos_convex : is_convex_set (fun x => 0 < x)%R.
Proof.
apply/asboolP => x y t Hx Hy.
case/boolP : (t == `Pr 0) => [/eqP ->| Ht0]; first by rewrite conv0.
apply addR_gt0wl; first by apply mulR_gt0 => //; exact/prob_gt0.
apply mulR_ge0 => //; exact: ltRW.
Qed.

Definition Rpos_interval := CSet.Pack (CSet.Class Rpos_convex).

Lemma Rnonneg_convex : is_convex_set (fun x => 0 <= x)%R.
Proof. apply/asboolP=> x y t Hx Hy; apply addR_ge0; exact/mulR_ge0. Qed.

Definition Rnonneg_interval := CSet.Pack (CSet.Class Rnonneg_convex).

Lemma open_interval_convex a b (Hab : (a < b)%R) : is_convex_set (fun x => a < x < b)%R.
Proof.
apply/asboolP => x y t [xa xb] [ya yb].
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

Definition open_unit_interval := CSet.Pack (CSet.Class open_unit_interval_convex).

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
    rewrite leR_add2l; apply leR_wpmul2l => //; exact/ltRW.
  - apply (@leR_trans (t * b + t.~ * b)); last first.
      rewrite -mulRDl addRCA addR_opp subRR addR0 mul1R; exact/leRR.
    rewrite leR_add2r; apply leR_wpmul2l => //; exact/ltRW.
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
