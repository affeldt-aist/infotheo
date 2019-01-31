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

Definition addRpos : Rpos -> Rpos -> Rpos.
intros [x Hx] [y Hy].
apply (@mkRpos (x+y)).
apply /ltRP/addR_gt0/ltRP => //.
by apply/ltRP.
Defined.

Lemma addRposE x y : val (addRpos x y) = val x + val y.
Proof. by destruct x, y. Qed.

Lemma addRpos_neq0 x y : val (addRpos x y) != 0.
Proof. case: addRpos => p /=. by rewrite /gtRb lt0R => /andP []. Qed.

Lemma addRposC : commutative addRpos.
Proof. by move=> x y; apply val_inj; rewrite !addRposE addRC. Qed.

Lemma addRposA : associative addRpos.
Proof. by move=> x y z; apply val_inj; rewrite !addRposE addRA. Qed.

Definition mulRpos : Rpos -> Rpos -> Rpos.
intros [x Hx] [y Hy].
apply (@mkRpos (x*y)).
apply /ltRP/mulR_gt0/ltRP => //.
by apply/ltRP.
Defined.

Lemma mulRposE x y : val (mulRpos x y) = val x * val y.
Proof. by destruct x, y. Qed.

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
by apply addRpos_neq0.
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
  rewrite mulVR; last by apply addRpos_neq0.
  rewrite mul1R mulRC onem_div; last by apply addRpos_neq0.
  by rewrite !addRposE /= !addRA addRK.
congr Conv.
apply prob_ext => /=.
rewrite r_of_pqE /=.
rewrite s_of_pqE Rpos_probC (Rpos_probC r) /= !onemK.
rewrite {3 4}/Rdiv !mulRA -(mulRC (/ addRpos r q)) !mulRA.
have Hpqr := addRpos_neq0 (addRpos p q) r.
rewrite !addRposE /= in Hpqr.
rewrite (addRposC r) mulVR; last by apply addRpos_neq0.
rewrite mul1R -(mulRC r) -/(Rdiv r _) onem_div ?addRpos_neq0 //.
rewrite {3}/Rdiv divRM; last by apply /invR_neq0/eqP/addRpos_neq0.
  rewrite !addRposE /=.
  rewrite -(addRC p) addRA addRK invRK; last by apply /eqP.
  by rewrite /Rdiv mulRC (mulRC p) !mulRA mulRV // mul1R.
rewrite -addRposA (addRposC r) addRposA addRposE /= addRK.
by apply /eqP /addRpos_neq0.
Qed.

Lemma addpt0 x : addpt x Zero = x.
Proof. by case: x. Qed.

Lemma add0pt x : addpt Zero x = x.
Proof. by []. Qed.

Canonical addpt_monoid := Monoid.Law addptA add0pt addpt0.
Canonical addpt_comoid := Monoid.ComLaw addptC.

Lemma addpt_weight a b : weight (addpt a b) = weight a + weight b.
Proof.
move: a b => [p x|] [q y|] /=; by rewrite (add0R, addR0, addRposE).
Qed.

Definition barycenter (pts : seq scaled_pt) :=
  \big[addpt/Zero]_(x <- pts) x.

End scaled_convex.

End ScaledConvexSpace.
