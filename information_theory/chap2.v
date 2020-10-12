(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import all_ssreflect ssralg fingroup perm finalg.
From mathcomp Require Import matrix.
From mathcomp Require boolp.
Require Import Reals Lra.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop fdist.
Require Import proba jfdist divergence entropy.

(******************************************************************************)
(*                Chapter 2 of Elements of Information Theory                 *)
(*                                                                            *)
(* Formalization of the chapter 2 of:                                         *)
(* Thomas M. Cover, Joy A. Thomas, Elements of Information Theory, Wiley,     *)
(* 2005                                                                       *)
(* See also entropy.v and convex_fdist.v                                      *)
(*                                                                            *)
(* chain_rule == (thm 2.1.1)                                                  *)
(* chain_rule_rV == chain rule for entropy (thm 2.5.1)                        *)
(* chain_rule_information == chain rule for information (thm 2.5.2)           *)
(* chain_rule_relative_entropy == chain rule for relative entropy (thm 2.5.3) *)
(* data_processing_inequality == (thm 2.8.1)                                  *)
(*                                                                            *)
(* Extra lemma:                                                               *)
(*  han == Han's inequality                                                   *)
(******************************************************************************)

(*
Contents:
- Module JointEntropy.
  Section joint_entropy_prop.
- Module CondEntropy.
  Section conditional_entropy_prop.
- Section chain_rule.
- Section chain_rule_generalization.
- Section entropy_chain_rule_corollary.
- Section conditional_entropy_prop2.
- Section conditional_entropy_prop3.
- Module MutualInfo.
- Section mutualinfo_prop.
- Section chain_rule_for_entropy.
- Section divergence_conditional_distributions.
- Section conditional_mutual_information.
- Section conditional_relative_entropy.
- Section chain_rule_for_information.
- Section conditioning_reduces_entropy.
- Section independence_bound_on_entropy.
- Section markov_chain.
- Section markov_chain_prop.
- Section Han_inequality.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

Module JointEntropy.
Section def.
Variables (A B : finType) (P : {fdist A * B}).

(* eqn 2.8 *)
Definition h := `H P.

(* eqn 2.9 *)
Lemma hE : h = `E (--log P).
Proof. by rewrite /h entropy_Ex. Qed.

Lemma hC : h = `H (Swap.d P).
Proof.
congr (- _) => /=.
rewrite (eq_bigr (fun a => P (a.1, a.2) * log (P (a.1, a.2)))); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => P (a1, a2) * log (P (a1, a2)))) /=.
rewrite exchange_big pair_big; apply eq_bigr => -[a b] _; by rewrite Swap.dE.
Qed.
End def.
Section rV.
Lemma entropyE (A : finType) n (P : {fdist 'rV[A]_n.+1}) :
  `H P = h (Multivar.belast_last P).
Proof.
rewrite /h /entropy; congr (- _) => /=.
rewrite -(big_rV_belast_last _ xpredT xpredT) /=.
rewrite pair_big /=; apply eq_bigr => -[a b] _ /=.
by rewrite Multivar.belast_lastE.
Qed.
End rV.
End JointEntropy.

Section notation_with_random_variables.
Section jointentropy_drv.
Variables (U A B : finType) (P : {fdist U}) (X : {RV P -> A}) (Y : {RV P -> B}).
Definition jointentropy_drv := JointEntropy.h (FDistMap.d [% X, Y] P).
End jointentropy_drv.
Local Notation "'`H2(' X ',' Y ')'" := (jointentropy_drv X Y)
  (format "'`H2(' X ','  Y ')'").
End notation_with_random_variables.

Section joint_entropy_prop.
Variable (A : finType) (P : {fdist A}).

Lemma joint_entropy_self : JointEntropy.h (Self.d P) = `H P.
Proof.
congr (- _).
rewrite (eq_bigr (fun a => Self.d P (a.1, a.2) * log (Self.d P (a.1, a.2)))); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => Self.d P (a1, a2) * log (Self.d P (a1, a2)))) /=.
apply/eq_bigr => a _.
rewrite (bigD1 a) //= !Self.dE /= eqxx big1 ?addR0 //.
by move=> a' /negbTE; rewrite Self.dE /= eq_sym => ->; rewrite mul0R.
Qed.

End joint_entropy_prop.

Module CondEntropy.
Section condentropy.
Variables (A B : finType) (QP : {fdist B * A}).

(* H(Y|X = x), see eqn 2.10 *)
Definition h1 a := - \sum_(b in B)
  \Pr_QP [ [set b] | [set a] ] * log (\Pr_QP [ [set b] | [set a] ]).

Let P := Bivar.snd QP.

(*eqn 2.11 *)
Definition h := \sum_(a in A) P a * h1 a.

Let PQ := Swap.d QP.

(* cover&thomas 2.12 *)
Lemma hE : h = - \sum_(a in A) \sum_(b in B)
  PQ (a, b) * log (\Pr_QP [ [set b] | [set a]]).
Proof.
rewrite /h big_morph_oppR /=; apply eq_bigr => a _.
rewrite /h1 mulRN big_distrr /=; congr (- _); apply eq_bigr => b _.
rewrite mulRA; congr (_ * _).
by rewrite mulRC -(Pr_set1 P a) -jproduct_rule setX1 Swap.dE Pr_set1.
Qed.

Lemma h1_ge0 a : 0 <= h1 a.
Proof.
rewrite /h1 big_morph_oppR; apply sumR_ge0 => b _; rewrite -mulRN.
case/boolP : (\Pr_QP[[set b]|[set a]] == 0) => [/eqP|] H0.
  rewrite H0 mul0R; exact/leRR.
apply mulR_ge0; [exact: jcPr_ge0|].
rewrite -oppR0 -(Log_1 2) /log leR_oppr oppRK.
by apply Log_increasing_le => //; [rewrite jcPr_gt0 | exact: jcPr_max].
Qed.

Lemma h_ge0 : 0 <= h.
Proof. by apply sumR_ge0 => a _; apply mulR_ge0 => //; exact: h1_ge0. Qed.

End condentropy.
End CondEntropy.

Section conditional_entropy_prop.

Variables (A B C : finType) (PQR : {fdist A * B * C}).

Lemma h1TripAC b c :
  CondEntropy.h1 (TripA.d PQR) (b, c) =
  CondEntropy.h1 (TripA.d (TripAC.d PQR)) (c, b).
Proof.
rewrite /CondEntropy.h1; congr (- _).
by apply eq_bigr => a _; rewrite -!setX1 jcPr_TripA_TripAC.
Qed.

Lemma hTripAC :
  CondEntropy.h (TripA.d PQR) =
  CondEntropy.h (TripA.d (TripAC.d PQR)).
Proof.
rewrite /CondEntropy.h /=.
rewrite (eq_bigr (fun a => (Bivar.snd (TripA.d PQR)) (a.1, a.2) * CondEntropy.h1 (TripA.d PQR) (a.1, a.2))); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => (Bivar.snd (TripA.d PQR)) (a1, a2) * CondEntropy.h1 (TripA.d PQR) (a1, a2))) /=.
rewrite exchange_big pair_big /=; apply eq_bigr => -[c b] _ /=; congr (_ * _).
  by rewrite TripAC.sndA Swap.dE.
by rewrite h1TripAC.
Qed.

End conditional_entropy_prop.

Section chain_rule.
Variables (A B : finType) (PQ : {fdist A * B}).
Let P := Bivar.fst PQ.
Let QP := Swap.d PQ.

Lemma chain_rule : JointEntropy.h PQ = `H P + CondEntropy.h QP. (* 2.14 *)
Proof.
rewrite /JointEntropy.h {1}/entropy.
transitivity (- (\sum_(a in A) \sum_(b in B)
    PQ (a, b) * log (P a * \Pr_QP [ [set b] | [set a] ]))). (* 2.16 *)
  congr (- _); rewrite pair_big /=; apply eq_bigr => -[a b] _ /=.
  congr (_ * log _); case/boolP : (P a == 0) => [/eqP|] H0.
  - by rewrite (Bivar.dom_by_fst _ H0) H0 mul0R.
  - by rewrite -(Pr_set1 P a) /P -(Swap.snd PQ) mulRC -jproduct_rule setX1 Pr_set1 Swap.dE.
transitivity (
  - (\sum_(a in A) \sum_(b in B) PQ (a, b) * log (P a))
  - (\sum_(a in A) \sum_(b in B) PQ (a, b) * log (\Pr_QP [ [set b] | [set a] ]))). (* 2.17 *)
  rewrite -oppRB; congr (- _); rewrite -addR_opp oppRK -big_split /=.
  apply eq_bigr => a _; rewrite -big_split /=; apply eq_bigr => b _.
  case/boolP : (PQ (a, b) == 0) => [/eqP H0|H0].
  - by rewrite H0 !mul0R addR0.
  - rewrite -mulRDr; congr (_ * _); rewrite mulRC logM //.
    by rewrite -Pr_jcPr_gt0 setX1 Pr_set1 Swap.dE -fdist_gt0.
    rewrite -fdist_gt0; exact: Bivar.dom_by_fstN H0.
rewrite [in X in _ + X = _]big_morph_oppR; congr (_ + _).
- rewrite /entropy; congr (- _); apply eq_bigr => a _.
  by rewrite -big_distrl /= -Bivar.fstE.
- rewrite CondEntropy.hE big_morph_oppR.
  apply eq_bigr => a _; congr (- _); apply eq_bigr => b _; by rewrite !Swap.dE.
Qed.

End chain_rule.

Section chain_rule_generalization.

Local Open Scope ring_scope.

(* TODO: move *)
Definition put_front (n : nat) (i : 'I_n.+1) : 'I_n.+1 -> 'I_n.+1 := fun j =>
  if j == i then ord0 else
    if (j < i)%nat then inord (j.+1) else
      j.

Definition put_back (n : nat) (i : 'I_n.+1) : 'I_n.+1 -> 'I_n.+1 := fun j =>
  if j == ord0 then i else
    if (j <= i)%nat then inord (j.-1) else
      j.

Lemma put_backK n (i : 'I_n.+1) : cancel (put_front i) (put_back i).
Proof.
move=> j; rewrite /put_back /put_front; case: (ifPn (j == i)) => [ji|].
  rewrite eqxx; exact/esym/eqP.
rewrite neq_ltn => /orP[|] ji.
  rewrite ji ifF; last first.
    apply/negbTE/eqP => /(congr1 val) => /=.
    by rewrite inordK // ltnS (leq_trans ji) // -ltnS.
  rewrite inordK; last by rewrite ltnS (leq_trans ji) // -ltnS.
  by rewrite ji /=; apply val_inj => /=; rewrite inordK.
rewrite ltnNge (ltnW ji) /= ifF; last first.
  by apply/negbTE; rewrite -lt0n (leq_trans _ ji).
by rewrite leqNgt ji.
Qed.

Lemma put_front_inj (n : nat) (i : 'I_n.+1) : injective (put_front i).
Proof. exact: (can_inj (put_backK i)). Qed.
Arguments put_front_inj {n} _.

Definition put_front_perm (n : nat) i : 'S_n.+1 := perm (put_front_inj i).

(* TODO: clean *)
Lemma MargFDistd_put_front n (A : finType) (P : {fdist 'rV[A]_n.+1}) (i : 'I_n.+1) :
  i != ord0 ->
  MargFDist.d P i = Bivar.snd (Multivar.to_bivar (MultivarPerm.d P (put_front_perm i))).
Proof.
move=> i0; apply/fdist_ext => /= v; rewrite MargFDist.dE Bivar.sndE.
destruct n as [|n']; first by rewrite (ord1 i) eqxx in i0.
transitivity (\sum_(x : A) P
  (\row_(k < n'.+2) (if k == i then x else v ``_ (inord (unbump i k)))))%R.
  rewrite (reindex_onto (fun a => \row_k (if k == i then a else v ``_ (inord (unbump i k))))
    (fun w => w ``_ i)); last first.
    move=> w wv.
    apply/rowP => j.
    rewrite !mxE; case: ifPn => [/eqP -> //|ji].
    rewrite -(eqP wv) mxE; congr (w _ _).
    move: ji; rewrite neq_ltn => /orP[|] ji.
      apply val_inj => /=.
      rewrite inordK; last first.
        by rewrite /unbump (ltnNge i j) (ltnW ji) subn0 (leq_trans ji) // -ltnS.
      by rewrite unbumpK //= inE ltn_eqF.
    apply val_inj => /=.
    rewrite inordK; last first.
      rewrite /unbump ji subn1 prednK //; by [rewrite -ltnS | rewrite (leq_ltn_trans _ ji)].
    by rewrite unbumpK //= inE gtn_eqF.
  apply eq_bigl => a /=.
  apply/andP; split.
    apply/eqP/rowP => k.
    rewrite !mxE eq_sym (negbTE (neq_lift _ _)).
    congr (v _ _).
    apply val_inj => /=.
    by rewrite bumpK inordK.
  by rewrite mxE eqxx.
under [RHS] eq_bigr do rewrite Multivar.to_bivarE MultivarPerm.dE.
apply/eq_bigr => a _; congr (P _); apply/rowP => k /=.
rewrite /col_perm /= 2!mxE /=.
rewrite /put_front_perm /= permE /put_front.
case: ifPn => [ki|]; first by rewrite row_mx_row_ord0.
rewrite neq_ltn => /orP[|] ki.
  rewrite ki.
  rewrite (_ : inord _ = rshift 1 (inord k)); last first.
    apply/val_inj => /=.
    rewrite add1n inordK /=.
      by rewrite inordK // (leq_trans ki) // -ltnS.
    by rewrite ltnS (leq_trans ki) // -ltnS.
  rewrite (@row_mxEr _ _ 1); congr (v ``_ _).
  apply val_inj => /=.
  rewrite /unbump ltnNge (ltnW ki) subn0 inordK //.
  by rewrite (leq_trans ki) // -ltnS.
rewrite ltnNge (ltnW ki) /=; move: ki.
have [/eqP -> //|k0] := boolP (k == ord0).
rewrite (_ : k = rshift 1 (inord k.-1)); last first.
  by apply val_inj => /=; rewrite add1n inordK ?prednK // ?lt0n // -ltnS.
rewrite (@row_mxEr _ 1 1) /=.
rewrite inordK ?prednK ?lt0n // -1?ltnS // ltnS add1n prednK ?lt0n // => ik.
by congr (v _ _); apply val_inj => /=; rewrite /unbump ik subn1.
Qed.

Lemma chain_rule_multivar (A : finType) (n : nat) (P : {fdist 'rV[A]_n.+1})
  (i : 'I_n.+1) : i != ord0 ->
  (`H P = `H (MargFDist.d P i) +
    CondEntropy.h (Multivar.to_bivar (MultivarPerm.d P (put_front_perm i))))%R.
Proof.
move=> i0; rewrite MargFDistd_put_front // -Swap.fst.
rewrite -{2}(Swap.dI (Multivar.to_bivar _)) -chain_rule JointEntropy.hC Swap.dI.
by rewrite entropy_to_bivar entropy_multivarperm.
Qed.

End chain_rule_generalization.

Section entropy_chain_rule_corollary.
Variables (A B C : finType) (PQR : {fdist A * B * C}).
Let PR : {fdist A * C} := Proj13.d PQR.
Let QPR : {fdist B * (A * C)} := TripA.d (TripC12.d PQR).

(* eqn 2.21, H(X,Y|Z) = H(X|Z) + H(Y|X,Z) *)
Lemma chain_rule_corollary :
  CondEntropy.h PQR = CondEntropy.h PR + CondEntropy.h QPR.
Proof.
rewrite !CondEntropy.hE -oppRD; congr (- _).
rewrite [in X in _ = _ + X](eq_bigr (fun j => \sum_(i in B) (Swap.d QPR) ((j.1, j.2), i) * log \Pr_QPR[[set i] | [set (j.1, j.2)]])); last by case.
rewrite -[in RHS](pair_bigA _ (fun j1 j2 => \sum_(i in B) (Swap.d QPR ((j1, j2), i) * log \Pr_QPR[[set i] | [set (j1, j2)]]))) /=.
rewrite [in X in _ = _ + X]exchange_big /= -big_split; apply eq_bigr => c _ /=.
rewrite [in LHS](eq_bigr (fun j => (Swap.d PQR) (c, (j.1, j.2)) * log \Pr_PQR[[set (j.1, j.2)] | [set c]])); last by case.
rewrite -[in LHS](pair_bigA _ (fun j1 j2 => (Swap.d PQR) (c, (j1, j2)) * log \Pr_PQR[[set (j1, j2)] | [set c]])) /=.
rewrite -big_split; apply eq_bigr => a _ /=.
rewrite Swap.dE Proj13.dE big_distrl /= -big_split; apply eq_bigr => b _ /=.
rewrite !(Swap.dE,TripA.dE,TripC12.dE) /= -mulRDr.
case/boolP : (PQR (a, b, c) == 0) => [/eqP H0|H0].
  by rewrite H0 !mul0R.
rewrite -logM; last 2 first.
  rewrite -Pr_jcPr_gt0 Pr_gt0 setX1 Pr_set1; exact: Proj13.dominN H0.
  by rewrite -Pr_jcPr_gt0 Pr_gt0 setX1 Pr_set1 TripA.dE /= TripC12.dE.
congr (_ * log _).
by rewrite -setX1 product_ruleC !setX1 mulRC.
Qed.

End entropy_chain_rule_corollary.

Section conditional_entropy_prop2. (* NB: here because use chain rule *)

Variables (A B : finType) (PQ : {fdist A * B}).
Let P := Bivar.fst PQ.
Let Q := Bivar.snd PQ.
Let QP := Swap.d PQ.

Lemma entropyB : `H P - CondEntropy.h PQ = `H Q - CondEntropy.h QP.
Proof.
rewrite subR_eq addRAC -subR_eq subR_opp -chain_rule JointEntropy.hC.
by rewrite -/(JointEntropy.h (Swap.d PQ)) chain_rule Swap.fst -/Q Swap.dI.
Qed.

End conditional_entropy_prop2.

Section conditional_entropy_prop3. (* NB: here because use chain rule *)

Variables (A : finType) (P : {fdist A}).

Lemma CondEntrop_self : CondEntropy.h (Self.d P) = 0.
Proof.
move: (@chain_rule _ _ (Self.d P)).
rewrite !Self.fst Self.swap addRC -subR_eq => <-.
by rewrite joint_entropy_self subRR.
Qed.

End conditional_entropy_prop3.

Module MutualInfo.
Local Open Scope divergence_scope.
Section def.
Variables (A B : finType) (PQ : {fdist A * B}).
Let P := Bivar.fst PQ.
Let Q := Bivar.snd PQ.
Let QP := Swap.d PQ.

(* I(X;Y) *)
Definition mi := D(PQ || P `x Q).
End def.
Section prop.
Variables (A B : finType) (PQ : {fdist A * B}).
Let P := Bivar.fst PQ.
Let Q := Bivar.snd PQ.
Let QP := Swap.d PQ.

(* 2.28 *)
Lemma miE0 : mi PQ =
  \sum_(a in A) \sum_(b in B) PQ (a, b) * log (PQ (a, b) / (P a * Q b)).
Proof.
rewrite /mi /div pair_big /=; apply eq_bigr; case => a b _ /=.
case/boolP : (PQ (a, b) == 0) => [/eqP H0|H0].
- by rewrite H0 !mul0R.
- by rewrite ProdFDist.dE.
Qed.

(* 2.39 *)
Lemma miE : mi PQ = `H P - CondEntropy.h PQ.
Proof.
rewrite miE0.
transitivity (\sum_(a in A) \sum_(b in B)
    PQ (a, b) * log (\Pr_PQ [ [set a] | [set b] ] / P a)).
  apply eq_bigr => a _; apply eq_bigr => b _.
  rewrite /jcPr setX1 2!Pr_set1 /= -/Q.
  case/boolP : (PQ (a, b) == 0) => [/eqP H0 | H0].
  - by rewrite H0 !mul0R.
  - congr (_ * log _).
    rewrite divRM; last 2 first.
      apply/eqP; exact: Bivar.dom_by_fstN H0.
      apply/eqP; exact: Bivar.dom_by_sndN H0.
    by rewrite mulRAC.
transitivity (- (\sum_(a in A) \sum_(b in B) PQ (a, b) * log (P a)) +
  \sum_(a in A) \sum_(b in B) PQ (a, b) * log (\Pr_PQ [ [set a] | [set b] ])). (* 2.37 *)
  rewrite big_morph_oppR -big_split; apply/eq_bigr => a _ /=.
  rewrite big_morph_oppR -big_split; apply/eq_bigr => b _ /=.
  rewrite addRC -mulRN -mulRDr addR_opp.
  case/boolP : (PQ (a, b) == 0) => [/eqP ->| H0].
  - by rewrite !mul0R.
  - congr (_ * _); rewrite logDiv //.
    + by rewrite -Pr_jcPr_gt0 Pr_gt0 setX1 Pr_set1.
    + rewrite -fdist_gt0; exact: Bivar.dom_by_fstN H0.
rewrite -subR_opp; congr (_ - _).
- rewrite /entropy; congr (- _); apply/eq_bigr => a _.
  by rewrite -big_distrl /= -Bivar.fstE.
- rewrite /CondEntropy.h exchange_big.
  rewrite big_morph_oppR; apply eq_bigr=> b _ /=.
  rewrite mulRN; congr (- _).
  rewrite big_distrr /=; apply eq_bigr=> a _ /=.
  rewrite mulRA; congr (_ * _); rewrite -/Q.
  by rewrite -[in LHS]Pr_set1 -setX1 jproduct_rule Pr_set1 -/Q mulRC.
Qed.

Lemma miE2 : mi PQ = `H Q - CondEntropy.h QP. (* 2.40 *)
Proof. by rewrite miE entropyB. Qed.

Lemma miE3 : mi PQ = `H P + `H Q - `H PQ. (* 2.41 *)
Proof.
rewrite miE; move: (chain_rule QP).
rewrite addRC -subR_eq -(Swap.dI PQ) -/QP => <-.
by rewrite -addR_opp oppRB Swap.fst -/Q addRA JointEntropy.hC.
Qed.

(* nonnegativity of mutual information 2.90 *)
Lemma mi_ge0 : 0 <= mi PQ.
Proof. exact/div_ge0/Prod_dominates_Joint. Qed.

Lemma mi0P : mi PQ = 0 <-> PQ = P `x Q.
Proof.
split; last by rewrite /mi => <-; rewrite div0P //; exact: dominatesxx.
rewrite /mi div0P //; exact: Prod_dominates_Joint.
Qed.
End prop.
End MutualInfo.

(* TODO: example 2.3.1 *)

Section mutualinfo_prop.

Local Open Scope divergence_scope.

(* eqn 2.46 *)
Lemma mi_sym (A B : finType) (PQ : {fdist A * B}) :
  let P := Bivar.fst PQ in
  let Q := Bivar.snd PQ in
  MutualInfo.mi PQ = MutualInfo.mi (Swap.d PQ).
Proof.
by move=> P Q; rewrite !MutualInfo.miE entropyB Swap.fst.
Qed.

(* eqn 2.47 *)
Lemma mutual_info_self (A : finType) (P : fdist A) :
  MutualInfo.mi (Self.d P) = `H P.
Proof.
by rewrite MutualInfo.miE CondEntrop_self subR0 Self.fst.
Qed.

End mutualinfo_prop.

Section chain_rule_for_entropy.

Local Open Scope vec_ext_scope.

Lemma entropy_head_of1 (A : finType) (P : {fdist 'M[A]_1}) :
  `H P = `H (Multivar.head_of P).
Proof.
rewrite /entropy; congr (- _); apply: big_rV_1 => // a.
rewrite /Multivar.head_of Bivar.fstE /= (big_rV_0 _ _ (a ``_ ord0)).
rewrite Multivar.to_bivarE /=; congr (P _ * log (P _)).
- apply/rowP => i.
  by rewrite (ord1 i) !mxE; case: splitP => // i0; rewrite (ord1 i0) mxE.
- apply/rowP => i.
  by rewrite (ord1 i) !mxE; case: splitP => // i0; rewrite (ord1 i0) mxE.
Qed.

Lemma chain_rule_rV (A : finType) (n : nat) (P : {fdist 'rV[A]_n.+1}) :
  `H P = \sum_(i < n.+1)
          if i == O :> nat then
            `H (Multivar.head_of P)
          else
            CondEntropy.h (Swap.d (Multivar.belast_last (Take.d P (lift ord0 i)))).
Proof.
elim: n P => [P|n IH P].
  by rewrite big_ord_recl /= big_ord0 addR0 -entropy_head_of1.
rewrite JointEntropy.entropyE chain_rule {}IH [in RHS]big_ord_recr /=.
rewrite Take.all; congr (_ + _); apply eq_bigr => i _.
case: ifP => i0; first by rewrite head_of_fst_belast_last.
congr (CondEntropy.h (Swap.d (Multivar.belast_last _))).
rewrite /Take.d /Bivar.fst /Multivar.belast_last !FDistMap.comp.
congr (FDistMap.d _ P); rewrite boolp.funeqE => /= v.
apply/rowP => j; rewrite !mxE !castmxE /= !mxE /= cast_ord_id; congr (v _ _).
exact: val_inj.
Qed.

End chain_rule_for_entropy.

Section divergence_conditional_distributions.

Variables (A B C : finType) (PQR : {fdist A * B * C}).

Definition cdiv1 z := \sum_(x in {: A * B})
  \Pr_PQR[[set x] | [set z]] * log (\Pr_PQR[[set x] | [set z]] /
    (\Pr_(Proj13.d PQR)[[set x.1] | [set z]] * \Pr_(Proj23.d PQR)[[set x.2] | [set z]])).

Local Open Scope divergence_scope.

Lemma cdiv1_is_div (c : C) (Hc  : Bivar.fst (Swap.d PQR) c != 0)
                           (Hc1 : Bivar.fst (Swap.d (Proj13.d PQR)) c != 0)
                           (Hc2 : Bivar.fst (Swap.d (Proj23.d PQR)) c != 0) :
  cdiv1 c = D((Swap.d PQR) `(| c ) ||
    ((Swap.d (Proj13.d PQR)) `(| c )) `x ((Swap.d (Proj23.d PQR)) `(| c ))).
Proof.
rewrite /cdiv1 /div; apply eq_bigr => -[a b] /= _; rewrite CondJFDist.dE //.
rewrite Swap.dI.
case/boolP : (\Pr_PQR[[set (a, b)]|[set c]] == 0) => [/eqP ->|H0].
  by rewrite !mul0R.
by rewrite ProdFDist.dE /= CondJFDist.dE // CondJFDist.dE // !Swap.dI.
Qed.

Lemma cdiv1_ge0 z : 0 <= cdiv1 z.
Proof.
case/boolP : (Bivar.snd PQR z == 0) => [/eqP|] z0.
  apply sumR_ge0 => -[a b] _.
  rewrite {1}/jcPr setX1 Pr_set1 (Bivar.dom_by_snd _ z0) div0R mul0R.
  exact: leRR.
have Hc : Bivar.fst (Swap.d PQR) z != 0.
  by rewrite Swap.fst.
have Hc1 : Bivar.fst (Swap.d (Proj13.d PQR)) z != 0.
  by rewrite Swap.fst Proj13.snd.
have Hc2 : Bivar.fst (Swap.d (Proj23.d PQR)) z != 0.
  by rewrite Swap.fst Proj23.snd.
rewrite cdiv1_is_div //; apply div_ge0.
(* TODO: lemma *)
apply/dominatesP => -[a b].
rewrite ProdFDist.dE !CondJFDist.dE //= mulR_eq0 => -[|].
- rewrite /jcPr !setX1 !Pr_set1 !mulR_eq0 => -[|].
  rewrite !Swap.dI.
  move/Proj13.domin => ->; by left.
  rewrite !Swap.dI.
  rewrite Proj13.snd /Rdiv => ->; by right.
- rewrite /jcPr !setX1 !Pr_set1 !mulR_eq0 => -[|].
  rewrite !Swap.dI.
  move/Proj23.domin => ->; by left.
  rewrite !Swap.dI.
  rewrite Proj23.snd => ->; by right.
Qed.

End divergence_conditional_distributions.

Section conditional_mutual_information.
Section def.
Variables (A B C : finType) (PQR : {fdist A * B * C}).

(* I(X;Y|Z) = H(X|Z) - H(X|Y,Z) 2.60 *)
Definition cmi := CondEntropy.h (Proj13.d PQR) - CondEntropy.h (TripA.d PQR).
End def.
Section prop.
Variables (A B C : finType) (PQR : {fdist A * B * C}).
Lemma cmiE : cmi PQR = \sum_(x in {: A * B * C}) PQR x *
  log (\Pr_PQR[[set x.1] | [set x.2]] /
       (\Pr_(Proj13.d PQR)[[set x.1.1] | [set x.2]] * \Pr_(Proj23.d PQR)[[set x.1.2] | [set x.2]])).
Proof.
rewrite /cmi 2!CondEntropy.hE /= subR_opp big_morph_oppR.
rewrite (eq_bigr (fun a => \sum_(b in A) (Swap.d (TripA.d PQR)) (a.1, a.2, b) * log \Pr_(TripA.d PQR)[[set b] | [set (a.1, a.2)]])); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => \sum_(b in A) (Swap.d (TripA.d PQR)) ((a1, a2), b) * log \Pr_(TripA.d PQR)[[set b] | [set (a1, a2)]])).
rewrite exchange_big -big_split /=.
rewrite (eq_bigr (fun x => PQR (x.1, x.2) * log
(\Pr_PQR[[set x.1] | [set x.2]] /
        (\Pr_(Proj13.d PQR)[[set x.1.1] | [set x.2]] * \Pr_(Proj23.d PQR)[[set x.1.2] | [set x.2]])))); last by case.
rewrite -(pair_bigA _ (fun x1 x2 => PQR (x1, x2) * log
(\Pr_PQR[[set x1] | [set x2]] /
        (\Pr_(Proj13.d PQR)[[set x1.1] | [set x2]] * \Pr_(Proj23.d PQR)[[set x1.2] | [set x2]])))).
rewrite /= exchange_big; apply eq_bigr => c _.
rewrite big_morph_oppR /= exchange_big -big_split /=.
rewrite (eq_bigr (fun i => PQR ((i.1, i.2), c) * log
       (\Pr_PQR[[set (i.1, i.2)] | [set c]] /
        (\Pr_(Proj13.d PQR)[[set i.1] | [set c]] * \Pr_(Proj23.d PQR)[[set i.2] | [set c]])))); last by case.
rewrite -(pair_bigA _ (fun i1 i2 => PQR (i1, i2, c) * log
  (\Pr_PQR[[set (i1, i2)] | [set c]] /
  (\Pr_(Proj13.d PQR)[[set i1] | [set c]] * \Pr_(Proj23.d PQR)[[set i2] | [set c]])))).
apply eq_bigr => a _ /=.
rewrite Swap.dE Proj13.dE big_distrl /= big_morph_oppR -big_split.
apply eq_bigr => b _ /=.
rewrite Swap.dE TripA.dE /= -mulRN -mulRDr.
case/boolP : (PQR (a, b, c) == 0) => [/eqP ->| H0]; first by rewrite !mul0R.
congr (_ * _).
rewrite addRC addR_opp -logDiv; last 2 first.
  rewrite -Pr_jcPr_gt0 Pr_gt0 setX1 Pr_set1; exact: TripA.dominN H0.
  rewrite -Pr_jcPr_gt0 Pr_gt0 setX1 Pr_set1; exact: Proj13.dominN H0.
congr (log _).
rewrite divRM; last 2 first.
  apply/eqP.
  rewrite -jcPr_gt0 -Pr_jcPr_gt0 Pr_gt0 setX1 Pr_set1; exact: Proj13.dominN H0.
  apply/eqP.
  rewrite -jcPr_gt0 -Pr_jcPr_gt0 Pr_gt0 setX1 Pr_set1; exact: Proj23.dominN H0.
rewrite {2}/Rdiv -mulRA mulRCA {1}/Rdiv [in LHS]mulRC; congr (_ * _).
rewrite -[in X in _ = X * _]setX1 jproduct_rule_cond setX1 -mulRA mulRV ?mulR1 //.
rewrite /jcPr divR_neq0' // ?setX1 !Pr_set1.
exact: Proj23.dominN H0.
rewrite Proj23.snd; exact: Bivar.dom_by_sndN H0.
Qed.

Let R := Bivar.snd PQR.

Lemma cmiE2 : cmi PQR = \sum_(z in C) R z * cdiv1 PQR z.
Proof.
rewrite cmiE.
rewrite (eq_bigr (fun x => PQR (x.1, x.2) * log
  (\Pr_PQR[[set x.1] | [set x.2]] /
    (\Pr_(Proj13.d PQR)[[set x.1.1] | [set x.2]] * \Pr_(Proj23.d PQR)[[set x.1.2] | [set x.2]])))); last by case.
rewrite -(pair_bigA _ (fun x1 x2 => PQR (x1, x2) * log
  (\Pr_PQR[[set x1] | [set x2]] /
    (\Pr_(Proj13.d PQR)[[set x1.1] | [set x2]] * \Pr_(Proj23.d PQR)[[set x1.2] | [set x2]])))).
rewrite exchange_big; apply eq_bigr => c _ /=.
rewrite big_distrr /=; apply eq_bigr => -[a b] _ /=; rewrite mulRA; congr (_ * _).
rewrite mulRC.
move: (jproduct_rule PQR [set (a, b)] [set c]); rewrite -/R Pr_set1 => <-.
by rewrite setX1 Pr_set1.
Qed.

(* 2.92 *)
Lemma cmi_ge0 : 0 <= cmi PQR.
Proof.
by rewrite cmiE2; apply sumR_ge0 => c _; apply mulR_ge0 => //; exact: cdiv1_ge0.
Qed.

Let P : fdist A := Bivar.fst (TripA.d PQR).
Let Q : fdist B := Bivar.snd (Bivar.fst PQR).

Lemma chain_rule_mi : MutualInfo.mi PQR = MutualInfo.mi (Proj13.d PQR) + cmi (Swap.d (TripA.d PQR)).
Proof.
rewrite MutualInfo.miE.
move: (chain_rule (Bivar.fst PQR)); rewrite /JointEntropy.h => ->.
have -> : CondEntropy.h PQR = CondEntropy.h (Proj13.d PQR) + CondEntropy.h (TripA.d (TripC12.d PQR)).
  by rewrite chain_rule_corollary.
rewrite -addR_opp oppRD addRCA 2!addRA -(addRA (- _ + _)) addR_opp; congr (_ + _).
  rewrite MutualInfo.miE addRC; congr (_ - _).
  by rewrite Proj13.fst TripA.fst.
rewrite /cmi; congr (CondEntropy.h _ - _).
  by rewrite /Proj13.d -/(TripC13.d _) TripC13.sndA.
(* TODO: lemma *)
rewrite /CondEntropy.h.
rewrite (eq_bigr (fun a => (Bivar.snd (TripA.d (TripC12.d PQR))) (a.1, a.2) * CondEntropy.h1 (TripA.d (TripC12.d PQR)) (a.1, a.2))); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => (Bivar.snd (TripA.d (TripC12.d PQR))) (a1, a2) * CondEntropy.h1 (TripA.d (TripC12.d PQR)) (a1, a2))).
rewrite exchange_big pair_big; apply eq_bigr => -[c a] _ /=; congr (_ * _).
  rewrite !Bivar.sndE; apply eq_bigr => b _.
  by rewrite !(Swap.dE,TripA.dE,TripC12.dE).
rewrite /CondEntropy.h1; congr (- _).
apply eq_bigr => b _.
by rewrite -setX1 jcPr_TripA_TripC12 setX1.
Qed.
End prop.
End conditional_mutual_information.

Section conditional_relative_entropy.
Section def.
Variables (A B : finType) (P Q : CJFDist.t A B).
Let Pj : {fdist B * A} := Swap.d (CJFDist.joint_of P).
Let Qj : {fdist B * A} := Swap.d (CJFDist.joint_of Q).
Let P1 : {fdist A} := CJFDist.P P.

(* eqn 2.65 *)
Definition cre := \sum_(x in A) P1 x * \sum_(y in B)
  \Pr_Pj[[set y]|[set x]] * log (\Pr_Pj[[set y]|[set x]] / \Pr_Qj[[set y]|[set x]]).
End def.

Section prop.
Local Open Scope divergence_scope.
Local Open Scope reals_ext_scope.
Variables (A B : finType) (P Q : CJFDist.t A B).
Let Pj : {fdist B * A} := Swap.d (CJFDist.joint_of P).
Let Qj : {fdist B * A} := Swap.d (CJFDist.joint_of Q).
Let P1 : {fdist A} := CJFDist.P P.
Let Q1 : {fdist A} := CJFDist.P Q.

Lemma chain_rule_relative_entropy :
  Pj `<< Qj -> D(Pj || Qj) = D(P1 || Q1) + cre P Q.
Proof.
move=> PQ.
rewrite {2}/div /cre -big_split /= {1}/div /=.
rewrite (eq_bigr (fun a => Pj (a.1, a.2) * (log (Pj (a.1, a.2) / (Qj (a.1, a.2)))))); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => Pj (a1, a2) * (log (Pj (a1, a2) / (Qj (a1, a2)))))) /=.
rewrite exchange_big; apply eq_bigr => a _ /=.
rewrite [in X in _ = X * _ + _](_ : P1 a = Bivar.snd Pj a); last first.
  by rewrite /P Swap.snd ProdFDist.fst.
rewrite Bivar.sndE big_distrl /= big_distrr /= -big_split /=; apply eq_bigr => b _.
rewrite mulRA (_ : P1 a * _ = Pj (b, a)); last first.
  rewrite /jcPr Pr_set1 -/P1 mulRCA setX1 Pr_set1 {1}/Pj Swap.snd ProdFDist.fst.
  case/boolP : (P1 a == 0) => [/eqP|] P2a0.
    have Pba0 : Pj (b, a) = 0 by rewrite /P Swap.dE ProdFDist.dE P2a0 mul0R.
    by rewrite Pba0 mul0R.
  by rewrite mulRV // ?mulR1.
rewrite -mulRDr.
case/boolP : (Pj (b, a) == 0) => [/eqP ->|H0]; first by rewrite !mul0R.
congr (_ * _).
have P1a0 : P1 a != 0.
  apply: contra H0 => /eqP.
  rewrite /P Swap.dE ProdFDist.dE => ->; by rewrite mul0R.
have Qba0 := dominatesEN PQ H0.
have Q2a0 : Q1 a != 0.
  apply: contra Qba0; rewrite /Q Swap.dE ProdFDist.dE => /eqP ->; by rewrite mul0R.
rewrite -logM; last 2 first.
  by apply/divR_gt0; rewrite -fdist_gt0.
  apply/divR_gt0; by rewrite -Pr_jcPr_gt0 setX1 Pr_set1 -fdist_gt0.
congr (log _).
rewrite /jcPr !setX1 !Pr_set1.
rewrite !Swap.dE !Swap.snd !ProdFDist.fst !ProdFDist.dE /=.
rewrite -/P1 -/Q1; field.
split; first exact/eqP.
split; first exact/eqP.
apply/eqP.
apply: contra Qba0; rewrite /Qj Swap.dE ProdFDist.dE /= => /eqP ->; by rewrite mulR0.
Qed.
End prop.
End conditional_relative_entropy.

Section chain_rule_for_information.

Variables (A : finType).
Let B := A. (* need in the do-not-delete-me step *)
Variables (n : nat) (PY : {fdist 'rV[A]_n.+1 * B}).
Let P : {fdist 'rV[A]_n.+1} := Bivar.fst PY.
Let Y : {fdist B} := Bivar.snd PY.

Let f (i : 'I_n.+1) : {fdist A * 'rV[A]_i * B} := TripC12.d (PairTake.d PY i).
Let fAC (i : 'I_n.+1) : {fdist A * B * 'rV[A]_i} := TripAC.d (f i).
Let fA (i : 'I_n.+1) : {fdist A * ('rV[A]_i * B)} := TripA.d (f i).

Local Open Scope vec_ext_scope.

Lemma chain_rule_information :
  (* 2.62 *) MutualInfo.mi PY = \sum_(i < n.+1)
    if i == O :> nat then
      MutualInfo.mi (PairNth.d PY ord0)
    else
      cmi (fAC i).
Proof.
rewrite MutualInfo.miE chain_rule_rV.
have -> : CondEntropy.h PY = \sum_(j < n.+1)
  if j == O :> nat then
    CondEntropy.h (PairNth.d PY ord0)
  else
    CondEntropy.h (fA j).
  move: (chain_rule (Swap.d PY)).
  rewrite Swap.dI addRC -subR_eq Swap.fst -/Y => <-.
  rewrite /JointEntropy.h.
  (* do-not-delete-me *)
  set YP : {fdist 'rV[A]_n.+2} := Multivar.from_bivar (Swap.d PY).
  transitivity (`H YP - `H Y); first by rewrite /YP entropy_from_bivar.
  rewrite (chain_rule_rV YP).
  rewrite [in LHS]big_ord_recl /=.
  rewrite (_ : `H (Multivar.head_of YP) = `H Y); last first.
    by rewrite /YP /Multivar.head_of (Multivar.from_bivarK (Swap.d PY)) Swap.fst.
  rewrite addRC addRK.
  apply eq_bigr => j _.
  case: ifPn => j0.
  - have {}j0 : j = ord0 by move: j0 => /eqP j0; exact/val_inj.
    subst j.
    rewrite /CondEntropy.h /=.
    apply big_rV_1 => // a1.
    have H1 : forall a,
     (Swap.d (Multivar.belast_last (Take.d YP (lift ord0 (lift ord0 ord0))))) (a, a1) =
     (PairNth.d PY ord0) (a, a1 ``_ ord0).
      move=> a.
      rewrite Swap.dE Multivar.belast_lastE (Take.dE _ (lift ord0 (lift ord0 ord0))) PairNth.dE /=.
      have H1 : (n.+2 - bump 0 (bump 0 0) = n)%nat by rewrite /bump !leq0n !add1n subn2.
      rewrite (big_cast_rV H1).
      rewrite (eq_bigr (fun x => PY (x.1, x.2))); last by case.
      rewrite -(pair_big (fun i : 'rV_n.+1 => i ``_ ord0 == a) (fun i => i == a1 ``_ ord0) (fun i1 i2 => PY (i1, i2))) /=.
      rewrite [in RHS](eq_bigl (fun i : 'rV_n.+1 => (xpred1 a (i ``_ ord0)) && (xpredT i))); last first.
        move=> i; by rewrite andbT.
      rewrite -(big_rV_cons_behead (fun i => \sum_(j | j == a1 ``_ ord0) PY (i, j)) (fun i => i == a) xpredT).
      rewrite exchange_big /=.
      apply eq_bigr => v _.
      rewrite big_pred1_eq.
      rewrite big_pred1_eq.
      rewrite /YP.
      rewrite Multivar.from_bivarE Swap.dE /=; congr (PY (_, _)).
        apply/rowP => i.
        rewrite mxE castmxE /=.
        move: (leq0n i); rewrite leq_eqVlt => /orP[/eqP|] i0.
          move=> [:Hi1].
          have @i1 : 'I_(bump 0 0).+1.
            apply: (@Ordinal _ i.+1); abstract: Hi1.
            by rewrite /bump leq0n add1n -i0.
          rewrite (_ : cast_ord _ _ = lshift (n.+2 - bump 0 (bump 0 0)) i1); last exact/val_inj.
          rewrite row_mxEl castmxE /= 2!cast_ord_id.
          rewrite (_ : cast_ord _ _ = rshift 1 (Ordinal (ltn_ord ord0))); last first.
            apply val_inj => /=; by rewrite add1n -i0.
          rewrite row_mxEr mxE.
          set i2 : 'I_1 := Ordinal (ltn_ord ord0).
          rewrite (_ : i = lshift n i2); last exact/val_inj.
          by rewrite (@row_mxEl _ _ 1) mxE.
        move=> [:Hi1].
        have @i1 : 'I_(n.+2 - bump 0 (bump 0 0)).
          apply: (@Ordinal _ i.-1); abstract: Hi1.
          by rewrite /bump !leq0n !add1n subn2 prednK //= -ltnS.
        rewrite (_ : cast_ord _ _ = rshift (bump 0 0).+1 i1); last first.
          by apply/val_inj => /=; rewrite /bump !leq0n !add1n add2n prednK.
        rewrite row_mxEr castmxE /= !cast_ord_id.
        have @i2 : 'I_n by apply: (@Ordinal _ i.-1); rewrite prednK // -ltnS.
        rewrite (_ : i = rshift 1 i2); last first.
          by apply/val_inj => /=; rewrite add1n prednK.
        rewrite (@row_mxEr _ _ 1) //; congr (v _ _); exact/val_inj.
      rewrite castmxE /=.
      rewrite (_ : cast_ord _ _ = lshift (n.+2 - bump 0 (bump 0 0)) (Ordinal (ltn_ord ord0))); last exact/val_inj.
      rewrite row_mxEl castmxE /= 2!cast_ord_id.
      rewrite (_ : cast_ord _ _ = lshift 1 (Ordinal (ltn_ord ord0))); last exact/val_inj.
      rewrite row_mxEl /=; congr (a1 ``_ _); exact/val_inj.
    congr (_ * _).
      rewrite 2!Bivar.sndE; apply eq_bigr => a _; by rewrite H1.
    rewrite /CondEntropy.h1; congr (- _).
    apply eq_bigr => a _; congr (_ * log _).
    + rewrite /jcPr /Pr !big_setX /= !big_set1.
      rewrite H1; congr (_ / _).
      rewrite !Bivar.sndE; apply eq_bigr => a0 _.
      by rewrite H1.
    + rewrite /jcPr /Pr !big_setX /= !big_set1.
      rewrite H1; congr (_ / _).
      rewrite !Bivar.sndE; apply eq_bigr => a0 _.
      by rewrite H1.
  - rewrite /fA /f.
    rewrite /CondEntropy.h /=.
    have H1 : bump 0 j = j.+1 by rewrite /bump leq0n.
    rewrite (big_cast_rV H1) /=.
    rewrite -(big_rV_cons_behead _ xpredT xpredT) /= exchange_big /= pair_bigA.
    have H2 : forall (v : 'rV_j) (b : B) (a : A) (H1' : (1 + j)%nat = lift ord0 j),
      (Swap.d (Multivar.belast_last (Take.d YP (lift ord0 (lift ord0 j)))))
      (a, (castmx (erefl 1%nat, H1') (row_mx (\row__ b) v))) =
      (TripA.d (TripC12.d (PairTake.d PY j))) (a, (v, b)).
      move=> v b a H1'.
      rewrite /YP /Swap.d /Multivar.belast_last /Take.d /Multivar.from_bivar.
      rewrite /TripA.d /TripC12.d /PairTake.d !FDistMap.comp !FDistMap.dE /=.
      apply eq_bigl => -[w b0]; rewrite /= /swap /= !inE /=.
      rewrite (_ : rlast _ = w ``_ j); last first.
        rewrite /rlast !mxE !castmxE /= cast_ord_id.
        rewrite (_ : cast_ord _ _ = rshift 1%nat j); last exact/val_inj.
        by rewrite (@row_mxEr _ 1%nat 1%nat n.+1).
      rewrite !xpair_eqE; congr (_ && _).
      rewrite (_ : rbelast _ =
        row_take (lift ord0 j) (rbelast (row_mx (\row_(k<1) b0) w))); last first.
        apply/rowP => i; rewrite !mxE !castmxE /= esymK !cast_ord_id.
        rewrite /rbelast mxE; congr (row_mx _ _ _ _); exact: val_inj.
      rewrite (_ : rbelast _ = row_mx (\row_(k<1) b0) (rbelast w)); last first.
        apply/rowP => i; rewrite mxE /rbelast.
        case/boolP : (i == O :> nat) => [/eqP | ] i0.
          rewrite (_ : widen_ord _ _ = ord0); last exact: val_inj.
          rewrite (_ : i = ord0); last exact: val_inj.
          by rewrite 2!row_mx_row_ord0.
        have @k : 'I_n.+1.
          apply: (@Ordinal _ i.-1).
          by rewrite prednK // ?lt0n // -ltnS (leq_trans (ltn_ord i)).
        rewrite (_ : widen_ord _ _ = rshift 1%nat k); last first.
          by apply val_inj => /=; rewrite -subn1 subnKC // lt0n.
        rewrite (@row_mxEr _ 1%nat 1%nat n.+1).
        have @k' : 'I_n.
          apply: (@Ordinal _ i.-1).
          by rewrite prednK // ?lt0n // -ltnS (leq_trans (ltn_ord i)).
        rewrite (_ : i = rshift 1%nat k'); last first.
          by apply val_inj => /=; rewrite -subn1 subnKC // lt0n.
        rewrite (@row_mxEr _ 1%nat 1%nat n) mxE; congr (w ord0 _); exact: val_inj.
      apply/idP/idP; last first.
        move/andP => /= [/eqP <- /eqP ->].
        apply/eqP/rowP => k.
        rewrite !mxE !castmxE /= esymK !cast_ord_id.
        case/boolP : (k == O :> nat) => [/eqP | ] k0.
          rewrite (_ : cast_ord _ _ = ord0); last exact: val_inj.
          rewrite (_ : k = ord0); last exact: val_inj.
          by rewrite 2!row_mx_row_ord0.
        have @l : 'I_n.
          apply: (@Ordinal _ k.-1).
          by rewrite prednK // ?lt0n // -ltnS (leq_trans (ltn_ord k)).
        rewrite (_ : cast_ord _ _ = rshift 1%nat l); last first.
          by apply val_inj => /=; rewrite add1n prednK // lt0n.
        rewrite (@row_mxEr _ 1%nat 1%nat n) //.
        have @l0 : 'I_(widen_ord (leqnSn n.+1) j).
          apply: (@Ordinal _ k.-1).
          by rewrite prednK // ?lt0n // -ltnS (leq_trans (ltn_ord k)).
        rewrite (_ : k = rshift 1%nat l0); last first.
          by apply val_inj => /=; rewrite add1n prednK // lt0n.
        rewrite (@row_mxEr _ 1%nat 1%nat) //.
        rewrite !mxE !castmxE /= cast_ord_id; congr (w _ _).
        exact: val_inj.
      move/eqP/rowP => H.
      move: (H ord0).
      rewrite !mxE !castmxE /= 2!cast_ord_id esymK.
      rewrite (_ : cast_ord _ _ = ord0); last exact: val_inj.
      rewrite 2!row_mx_row_ord0 => ->; rewrite eqxx andbT.
      apply/eqP/rowP => k.
      have @k1 : 'I_(bump 0 j).
        apply: (@Ordinal _ k.+1).
        by rewrite /bump leq0n add1n ltnS.
      move: (H k1).
      rewrite !mxE !castmxE /= esymK !cast_ord_id.
      have @k2 : 'I_n.
        apply: (@Ordinal _ k).
        by rewrite (leq_trans (ltn_ord k)) // -ltnS (leq_trans (ltn_ord j)).
      rewrite (_ : cast_ord _ _ = rshift 1%nat k2); last first.
        by apply val_inj => /=; rewrite add1n.
      rewrite (@row_mxEr _ 1%nat 1%nat) mxE.
      rewrite (_ : cast_ord _ _ = widen_ord (leqnSn n) k2); last exact: val_inj.
      move=> ->.
      rewrite (_ : k1 = rshift 1%nat k); last by apply val_inj => /=; rewrite add1n.
      by rewrite row_mxEr.
    apply eq_bigr => -[v b] _ /=.
    rewrite 2!Bivar.sndE; congr (_ * _).
      apply eq_bigr => a _.
      rewrite -H2.
      congr (Swap.d _ (a, castmx (_, _) _)).
      exact: eq_irrelevance.
    rewrite /CondEntropy.h1; congr (- _).
    apply eq_bigr => a _.
    rewrite /jcPr /Pr !big_setX /= !big_set1.
    rewrite !H2 //=.
    congr (_ / _ * log (_ / _)).
    + rewrite 2!Bivar.sndE; apply eq_bigr => a' _; by rewrite H2.
    + rewrite 2!Bivar.sndE; apply eq_bigr => a' _; by rewrite H2.
rewrite -addR_opp big_morph_oppR -big_split /=; apply eq_bigr => j _ /=.
case: ifPn => j0.
- rewrite MutualInfo.miE addR_opp; congr (`H _ - _).
  rewrite /Multivar.head_of /Bivar.fst.
  rewrite /Multivar.to_bivar.
  by rewrite /PairNth.d !FDistMap.comp.
- rewrite /cmi /fA -/P; congr (_ - _).
  + congr CondEntropy.h.
    by rewrite /fAC /f Proj13_TripAC TripC12.fst belast_last_take.
  + rewrite /fAC /f /TripAC.d TripC12.dI /CondEntropy.h /=.
    rewrite (eq_bigr (fun a => Bivar.snd (TripA.d (TripC12.d (PairTake.d PY j))) (a.1, a.2) *
       CondEntropy.h1 (TripA.d (TripC12.d (PairTake.d PY j))) (a.1, a.2))); last by case.
    rewrite -(pair_bigA _ (fun a1 a2 => (Bivar.snd (TripA.d (TripC12.d (PairTake.d PY j)))) (a1, a2) *
       CondEntropy.h1 (TripA.d (TripC12.d (PairTake.d PY j))) (a1, a2))) /=.
    rewrite exchange_big pair_bigA /=; apply eq_bigr => -[b v] _ /=.
    congr (_ * _).
    * rewrite !Bivar.sndE; apply eq_bigr=> a _.
      by rewrite !TripA.dE /= Swap.dE TripC12.dE /= TripA.dE.
    * (* TODO: lemma? *)
      rewrite /CondEntropy.h1; congr (- _); apply eq_bigr => a _.
      by rewrite -!setX1 -jcPr_TripA_TripAC /TripAC.d TripC12.dI.
Qed.

End chain_rule_for_information.

Section conditioning_reduces_entropy.
Section prop.
Variables (A B : finType) (PQ : {fdist A * B}).
Let P := Bivar.fst PQ.
Let Q := Bivar.snd PQ.
Let QP := Swap.d PQ.

(* 2.95 *)
Lemma information_cant_hurt : CondEntropy.h PQ <= `H P.
Proof. rewrite -subR_ge0 -MutualInfo.miE; exact: MutualInfo.mi_ge0. Qed.

Lemma condentropy_indep : PQ = P `x Q -> CondEntropy.h PQ = `H P.
Proof. move/MutualInfo.mi0P; by rewrite MutualInfo.miE subR_eq0 => <-. Qed.
End prop.
Section prop2.
Variables (A B C : finType) (PQR : {fdist A * B * C}).
Let P : fdist A := Bivar.fst (TripA.d PQR).
Let Q : fdist B := Bivar.snd (Bivar.fst PQR).
Let R := Bivar.snd PQR.
Lemma mi_bound : Bivar.fst PQR = P `x Q (* P and Q independent *) ->
  MutualInfo.mi (Proj13.d PQR) + MutualInfo.mi (Proj23.d PQR) <= MutualInfo.mi PQR.
Proof.
move=> PQ; rewrite chain_rule_mi leR_add2l /cmi.
rewrite [X in _ <= X - _](_ : _ = `H Q); last first.
  rewrite condentropy_indep; last first.
    rewrite Proj13.fst TripA.fst Swap.fst TripA.fst_snd -/Q.
    rewrite Proj13.snd Swap.snd -/P.
    rewrite -[RHS]Swap.dI Swap.ProdFDist -PQ.
    apply/fdist_ext => -[b a]. (* TODO: lemma? *)
    rewrite Proj13.dE Swap.dE Bivar.fstE; apply eq_bigr => c _.
    by rewrite Swap.dE TripA.dE.
  by rewrite /Proj13.d TripA.fst_snd TripC12.fst Swap.fst Swap.snd TripA.fst_snd -/Q.
rewrite MutualInfo.miE.
rewrite Proj23.fst -/Q.
rewrite -oppRB leR_oppl oppRB -!addR_opp leR_add2r.
(* conditioning cannot increase entropy *)
(* Q|R,P <= Q|R, lemma *)
rewrite -subR_ge0.
move: (cmi_ge0 (TripC12.d PQR)); rewrite /cmi.
rewrite /Proj13.d TripC12.dI -/(Proj23.d _).
by rewrite hTripAC /TripAC.d TripC12.dI.
Qed.
End prop2.
End conditioning_reduces_entropy.

(* TODO: example 2.6.1 *)

Section independence_bound_on_entropy.

Variables (A : finType) (n : nat) (P : {fdist 'rV[A]_n.+1}).

(* thm 2.6.6 TODO: with equality in case of independence *)
Lemma independence_bound_on_entropy : `H P <= \sum_(i < n.+1) `H (Nth.d P i).
Proof.
rewrite chain_rule_rV; apply leR_sumR => /= i _.
case: ifPn => [/eqP|] i0.
  rewrite (_ : i = ord0); last exact/val_inj.
  rewrite Nth.head_ofE; exact/leRR.
apply: leR_trans; first exact: information_cant_hurt.
by rewrite Swap.fst take_nth; exact/leRR.
Qed.

End independence_bound_on_entropy.

Section markov_chain.

Variables (A B C : finType) (PQR : {fdist A * B * C}).
Let P := Bivar.fst (Bivar.fst PQR).
Let Q := Bivar.snd (Bivar.fst PQR).
Let PQ := Bivar.fst PQR.
Let QP := Swap.d PQ.
Let RQ := Swap.d (Bivar.snd (TripA.d PQR)).

(* cond. distr. of Z depends only on Y and conditionally independent of X *)
Definition markov_chain := forall (x : A) (y : B) (z : C),
  PQR (x, y, z) = P x * \Pr_QP[ [set y] | [set x]] * \Pr_RQ[ [set z] | [set y]].

Let PRQ := TripAC.d PQR.

(* X and Z are conditionally independent given Y TODO: iff *)
Lemma markov_cmi : markov_chain -> cmi (PRQ : {fdist A * C * B}) = 0.
Proof.
rewrite /markov_chain => mc.
rewrite cmiE (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 //= => x _.
case/boolP : (PRQ x == 0) => [/eqP ->|H0]; first by rewrite mul0R.
rewrite (_ : _ / _ = 1); first by rewrite /log Log_1 mulR0.
rewrite eqR_divr_mulr ?mul1R; last first.
  rewrite mulR_neq0'; apply/andP; split.
    (* TODO: lemma? *)
    rewrite /jcPr divR_neq0' //.
      rewrite setX1 Pr_set1.
      case: x => [[x11 x12] x2] in H0 *.
      exact: Proj13.dominN H0.
    rewrite Pr_set1 Proj13.snd.
    case: x => [x1 x2] in H0 *.
    exact: Bivar.dom_by_sndN H0.
  (* TODO: lemma? *)
  rewrite /jcPr divR_neq0' //.
    rewrite setX1 Pr_set1.
    case: x => [[x11 x12] x2] in H0 *.
    exact: Proj23.dominN H0.
  rewrite Pr_set1 Proj23.snd.
  case: x => [x1 x2] in H0 *.
  exact: Bivar.dom_by_sndN H0.
(* TODO: lemma? *) (* 2.118 *)
transitivity (Pr PRQ [set x] / Pr Q [set x.2]).
  rewrite /jcPr setX1 {2}/PRQ TripAC.snd -/Q; by case: x H0.
transitivity (Pr PQ [set (x.1.1,x.2)] * \Pr_RQ[[set x.1.2]|[set x.2]] / Pr Q [set x.2]).
  congr (_ / _).
  case: x H0 => [[a c] b] H0 /=.
  rewrite /PRQ Pr_set1 TripAC.dE /= mc; congr (_ * _).
  rewrite /jcPr {2}/QP Swap.snd -/P Pr_set1 mulRCA mulRV ?mulR1; last first.
    apply Bivar.dom_by_fstN with b.
    apply Bivar.dom_by_fstN with c.
    by rewrite TripAC.dE in H0.
  by rewrite /QP -Swap.Pr setX1.
rewrite {1}/Rdiv -mulRA mulRCA mulRC; congr (_ * _).
  rewrite /jcPr Proj13.snd -/Q {2}/PRQ TripAC.snd -/Q -/(Rdiv _ _); congr (_ / _).
  by rewrite /PRQ /PQ setX1 Proj13_TripAC.
rewrite /jcPr Proj23.snd; congr (_ / _).
- by rewrite /RQ /PRQ /Proj23.d TripAC.sndA.
- by rewrite /RQ Swap.snd TripA.fst_snd /PRQ TripAC.snd.
Qed.

Let PR := Proj13.d PQR.

Lemma data_processing_inequality : markov_chain ->
  MutualInfo.mi PR <= MutualInfo.mi PQ.
Proof.
move=> H.
have H1 : MutualInfo.mi (TripA.d PQR) = MutualInfo.mi PR + cmi PQR.
  rewrite /cmi !MutualInfo.miE addRA; congr (_ - _).
  by rewrite -/PR subRK /PR Proj13.fst.
have H2 : MutualInfo.mi (TripA.d PQR) = MutualInfo.mi PQ + cmi PRQ.
  transitivity (MutualInfo.mi (TripA.d PRQ)).
    by rewrite !MutualInfo.miE TripAC.fstA hTripAC.
  rewrite /cmi !MutualInfo.miE addRA; congr (_ - _).
  by rewrite TripA.fst {1}/PRQ Proj13_TripAC -/PQ subRK /PQ TripAC.fst_fst.
have H3 : cmi PRQ = 0 by rewrite markov_cmi.
have H4 : 0 <= cmi PQR by exact: cmi_ge0.
move: H2; rewrite {}H3 addR0 => <-.
by rewrite {}H1 addRC -leR_subl_addr subRR.
Qed.

End markov_chain.

Section markov_chain_prop.

Variables (A B C : finType) (PQR : {fdist A * B * C}).

Lemma markov_chain_order : markov_chain PQR -> markov_chain (TripC13.d PQR).
Proof.
rewrite /markov_chain => H c b a.
rewrite TripC13.dE /=.
rewrite {}H.
rewrite TripC13.fst_fst.
rewrite (jBayes _ [set a] [set b]).
rewrite Swap.dI.
rewrite Swap.fst.
rewrite Swap.snd.
rewrite (mulRC (_ a)) -mulRA.
rewrite [in RHS]mulRCA -[in RHS]mulRA.
congr (_ * _).
  by rewrite TripC13.sndA.
rewrite (jBayes _ [set c] [set b]).
rewrite Swap.dI.
rewrite [in LHS]mulRCA -[in LHS]mulRA.
rewrite [in RHS](mulRC (_ c)) -[in RHS](mulRA _ (_ c)).
rewrite [in RHS]mulRCA.
congr (_ * _).
  congr (\Pr_ _ [_ | _]).
  by rewrite TripC13.fst Swap.dI.
rewrite !Pr_set1.
rewrite [in RHS]mulRCA.
congr (_ * _).
  by rewrite Swap.fst TripA.snd_snd.
congr (_ * / _).
  congr (_ a).
  by rewrite TripA.snd_snd TripC13.snd.
by rewrite Swap.snd TripA.fst_snd TripC13.sndA Swap.fst.
Qed.

End markov_chain_prop.

Section Han_inequality.

Local Open Scope ring_scope.

Lemma information_cant_hurt_cond (A : finType) (n' : nat) (n := n'.+1 : nat)
  (P : {fdist 'rV[A]_n}) (i : 'I_n) (i0 : i != O :> nat) :
  CondEntropy.h (Multivar.to_bivar P) <=
  CondEntropy.h (Multivar.to_bivar (Take.d P (lift ord0 i))).
Proof.
rewrite -subR_ge0.
set Q : {fdist A * 'rV[A]_i * 'rV[A]_(n' - i)} := TakeDrop.d P i.
have H1 : Proj13.d (TripAC.d Q) = Multivar.to_bivar (Take.d P (lift ord0 i)).
  rewrite /Proj13.d /TripAC.d /Multivar.to_bivar /Take.d /Bivar.snd /TripA.d.
  rewrite /TripC12.d /Swap.d /TakeDrop.d !FDistMap.comp; congr (FDistMap.d _ P).
  rewrite boolp.funeqE => /= v /=.
  congr (_, _).
  - rewrite mxE castmxE /= cast_ord_id; congr (v ord0 _); exact: val_inj.
  - apply/rowP => j.
    rewrite !mxE !castmxE /= !cast_ord_id !esymK mxE; congr (v ord0 _).
    exact: val_inj.
have H2 : CondEntropy.h (TripA.d (TripAC.d Q)) = CondEntropy.h (Multivar.to_bivar P).
  rewrite -hTripAC /CondEntropy.h /=.
  rewrite (@partition_big _ _ _ _ _ xpredT (@row_take A _ i) xpredT) //=.
  rewrite (eq_bigr (fun a => (Bivar.snd (TripA.d Q)) (a.1, a.2) *
           CondEntropy.h1 (TripA.d Q) (a.1, a.2))%R); last by case.
  rewrite -(pair_bigA _ (fun a1 a2 => (Bivar.snd (TripA.d Q)) (a1, a2) *
           CondEntropy.h1 (TripA.d Q) (a1, a2))%R) /=.
  apply eq_bigr => v _.
(* TODO: lemma yyy *)
  rewrite (@reindex_onto _ _ _ [finType of 'rV[A]_n'] [finType of 'rV[A]_(n' - i)]
    (fun w => (castmx (erefl 1%nat, subnKC (ltnS' (ltn_ord i))) (row_mx v w)))
    (@row_drop A _ i)) /=; last first.
    move=> w wv; apply/rowP => j.
    rewrite castmxE /= cast_ord_id /row_drop mxE; case: splitP => [j0 /= jj0|k /= jik].
    - rewrite -(eqP wv) mxE castmxE /= cast_ord_id; congr (w _ _); exact: val_inj.
    - rewrite mxE /= castmxE /= cast_ord_id; congr (w _ _); exact: val_inj.
  apply eq_big => /= w.
    apply/esym/andP; split; apply/eqP/rowP => j.
    by rewrite !mxE !castmxE /= !cast_ord_id esymK cast_ordK row_mxEl.
    by rewrite !mxE !castmxE /= cast_ord_id esymK cast_ordK cast_ord_id row_mxEr.
  move=> _; congr (_ * _)%R.
  - rewrite !Bivar.sndE; apply eq_bigr => a _.
    by rewrite TripA.dE /= Multivar.to_bivarE /= /Q TakeDrop.dE.
  - rewrite /CondEntropy.h1; congr (- _)%R; apply eq_bigr => a _.
    congr (_ * log _)%R.
    + rewrite /jcPr !(Pr_set1,setX1) TripA.dE /= /Q TakeDrop.dE /= Multivar.to_bivarE /=.
      congr (_ / _)%R.
      rewrite !Bivar.sndE; apply eq_bigr => a0 _.
      by rewrite TripA.dE TakeDrop.dE Multivar.to_bivarE.
    + rewrite /jcPr !(Pr_set1,setX1) TripA.dE /= /Q TakeDrop.dE /= Multivar.to_bivarE /=.
      congr (_ / _)%R.
      rewrite !Bivar.sndE; apply eq_bigr => a0 _.
      by rewrite TripA.dE TakeDrop.dE Multivar.to_bivarE.
rewrite (_ : _ - _ = cmi (TripAC.d Q))%R; last by rewrite /cmi H1 H2.
exact/cmi_ge0.
Qed.

Lemma han_helper (A : finType) (n' : nat) (n := n'.+1 : nat)
  (P : {fdist 'rV[A]_n}) (i : 'I_n) (i0 : i != O :> nat) :
  CondEntropy.h (Multivar.to_bivar (MultivarPerm.d P (put_front_perm i))) <=
  CondEntropy.h (Swap.d (Multivar.belast_last (Take.d P (lift ord0 i)))).
Proof.
rewrite (_ : Swap.d _ = Multivar.to_bivar (MultivarPerm.d
    (Take.d P (lift ord0 i)) (put_front_perm (inord i)))); last first.
  apply/fdist_ext => /= -[a v].
  rewrite Swap.dE Multivar.belast_lastE Multivar.to_bivarE /= MultivarPerm.dE.
  rewrite !(Take.dE _ (lift ord0 i)); apply eq_bigr => /= w _; congr (P _); apply/rowP => k.
  rewrite !castmxE /= cast_ord_id.
  case/boolP : (k < i.+1)%nat => ki.
    have @k1 : 'I_i.+1 := Ordinal ki.
    rewrite (_ : cast_ord _ k = lshift (n - bump 0 i) k1); last exact/val_inj.
    rewrite 2!row_mxEl castmxE /= cast_ord_id [in RHS]mxE.
    case/boolP : (k < i)%nat => [ki'|].
      rewrite (_ : cast_ord _ _ = lshift 1%nat (Ordinal ki')) /=; last exact/val_inj.
      rewrite row_mxEl /put_front_perm permE /put_front ifF; last first.
        apply/negbTE/eqP => /(congr1 val) /=.
        by rewrite inordK // => /eqP; rewrite ltn_eqF.
      rewrite inordK //= ki' (_ : inord k.+1 = rshift 1%nat (Ordinal ki')); last first.
        by apply/val_inj => /=; rewrite inordK.
      by rewrite (@row_mxEr _ 1%nat 1%nat).
    rewrite permE /put_front.
    rewrite -leqNgt leq_eqVlt => /orP[|] ik.
      rewrite ifT; last first.
        apply/eqP/val_inj => /=; rewrite inordK //; exact/esym/eqP.
      rewrite row_mx_row_ord0 (_ : cast_ord _ _ = rshift i ord0); last first.
        by apply val_inj => /=; rewrite addn0; apply/esym/eqP.
      by rewrite row_mxEr mxE.
    move: (leq_ltn_trans ik ki); by rewrite ltnn.
  rewrite -ltnNge ltnS in ki.
  move=> [:Hk1].
  have @k1 : 'I_(n - bump 0 i).
    apply: (@Ordinal _ (k - i.+1)).
    abstract: Hk1.
    by rewrite /bump leq0n add1n ltn_sub2r // (leq_ltn_trans _ (ltn_ord k)).
  rewrite (_ : cast_ord _ _ = rshift i.+1 k1); last by apply val_inj => /=; rewrite subnKC.
  by rewrite 2!row_mxEr.
rewrite (_ : MultivarPerm.d (Take.d _ _) _ =
  Take.d (MultivarPerm.d P (put_front_perm i)) (lift ord0 i)); last first.
  apply/fdist_ext => /= w.
  rewrite MultivarPerm.dE 2!(Take.dE _ (lift ord0 i)); apply eq_bigr => /= v _.
  rewrite MultivarPerm.dE; congr (P _); apply/rowP => /= k.
  rewrite /col_perm mxE !castmxE /= !cast_ord_id /=.
  case/boolP : (k < bump 0 i)%nat => ki.
    rewrite (_ : cast_ord _ _ = lshift (n - bump 0 i) (Ordinal ki)); last exact/val_inj.
    rewrite row_mxEl mxE /put_front_perm !permE /= /put_front /=.
    case/boolP : (k == i) => ik.
      rewrite ifT; last first.
        apply/eqP/val_inj => /=; rewrite inordK //; exact/eqP.
      rewrite (_ : cast_ord _ _ = lshift (n - bump 0 i) ord0); last exact/val_inj.
      by rewrite row_mxEl.
    rewrite ifF; last first.
      apply/negbTE/eqP => /(congr1 val) /=.
      apply/eqP; by rewrite inordK.
    case/boolP : (k < i)%nat => {}ik.
      rewrite inordK // ik.
      move=> [:Hk1].
      have @k1 : 'I_(bump 0 i).
        apply: (@Ordinal _ k.+1).
        abstract: Hk1.
        by rewrite /bump leq0n add1n.
      rewrite (_ : cast_ord _ _ = lshift (n - bump 0 i) k1); last first.
        apply/val_inj => /=; rewrite inordK // ltnS.
        by rewrite (leq_trans ik) // -ltnS.
      rewrite row_mxEl; congr (w _ _).
      by apply val_inj => /=; rewrite inordK.
    rewrite -ltnNge in ik.
    rewrite ifF; last first.
      apply/negbTE.
      by rewrite -leqNgt -ltnS inordK.
    rewrite (_ : cast_ord _ _ = lshift (n - bump 0 i) (Ordinal ki)); last exact/val_inj.
    by rewrite row_mxEl.
  rewrite -ltnNge /bump leq0n add1n ltnS in ki.
  move=> [:Hk1].
  have @k1 : 'I_(n - bump 0 i).
    apply: (@Ordinal _ (k - i.+1)).
    abstract: Hk1.
    by rewrite /bump leq0n add1n ltn_sub2r // (leq_trans _ (ltn_ord k)).
  rewrite (_ : cast_ord _ _ = rshift i.+1 k1); last by apply/val_inj => /=; rewrite subnKC.
  rewrite row_mxEr permE /put_front /= ifF; last first.
     by move: ki; rewrite ltnNge; apply: contraNF => /eqP ->.
  rewrite ltnNge (ltnW ki) /=.
  move=> [:Hk2].
  have @k2 : 'I_(n - bump 0 i).
    apply: (@Ordinal _ (k - i.+1)).
    abstract: Hk2.
    by rewrite /bump leq0n add1n ltn_sub2r // (leq_trans _ (ltn_ord k)).
  rewrite (_ : cast_ord _ _ = rshift (bump 0 i) k2); last first.
    by apply/val_inj => /=; rewrite /bump leq0n add1n subnKC.
  rewrite row_mxEr; congr (v _ _); exact/val_inj.
exact/information_cant_hurt_cond.
Qed.

Variables (A : finType) (n' : nat).
Let n := n'.+1.
Variable (P : {fdist 'rV[A]_n}).

Lemma han : n.-1%:R * `H P <= \sum_(i < n) `H (MargFDist.d P i).
Proof.
rewrite -subn1 natRB // mulRBl mul1R leR_subl_addr {2}(chain_rule_rV P).
rewrite -big_split /= -{1}(card_ord n) -sum1_card big_morph_natRD big_distrl /=.
apply leR_sumR => i _; rewrite mul1R.
case: ifPn => [/eqP|] i0.
  rewrite (_ : i = ord0); last exact/val_inj.
  rewrite -MargFDist.tail_ofE /Multivar.tail_of /Multivar.head_of.
  rewrite -{1}(Multivar.to_bivarK P) entropy_from_bivar.
  move: (chain_rule (Multivar.to_bivar P)); rewrite /JointEntropy.h => ->.
  by rewrite [in X in _ <= X]addRC leR_add2l -Swap.fst; exact: information_cant_hurt.
by rewrite (chain_rule_multivar _ i0) leR_add2l; exact/han_helper.
Qed.

End Han_inequality.
