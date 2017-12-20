(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import Reals_ext ssr_ext ssralg_ext log2 Rssr tuple_prod Rbigop.
Require Import proba entropy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Definition of channels and of the capacity *)

(*Local Open Scope tuple_ext_scope.*)

Module Channel1.

Section Channel1_sect.

Variables A B : finType.

(** Probability transition matrix: *)

(** Definition of a discrete channel of input alphabet A and output alphabet B.
    It is a collection of probability mass functions, one for each a in A: *)

Local Notation "'`Ch_1'" := (A -> dist B).

(** Channels with non-empty alphabet: *)

Record chan_star := mkChan {
  c :> `Ch_1 ;
  input_not_0 : (0 < #|A|)%nat }.

Local Notation "'`Ch_1*'" := (chan_star).

Lemma chan_star_eq (c1 c2 : `Ch_1*) : c c1 = c c2 -> c1 = c2.
Proof.
destruct c1 as [c1 Hc1].
destruct c2 as [c2 Hc2].
move=> /= ?; subst c2.
f_equal.
apply eq_irrelevance.
Qed.

End Channel1_sect.

End Channel1.

Definition chan_star_coercion := Channel1.c.
Coercion chan_star_coercion : Channel1.chan_star >-> Funclass.

Notation "'`Ch_1(' A ',' B ')'" := (A -> dist B) (at level 10, A, B at next level) : channel_scope.

Notation "'`Ch_1*(' A ',' B ')'" := (@Channel1.chan_star A B) (at level 10, A, B at next level) : channel_scope.

Local Open Scope channel_scope.

Notation "W '`(' b '|' a ')'" := (W a b)
  (at level 10, b, a at next level, only parsing) : channel_scope.

Module DMC.

Section DMC_sect.

Variables A B : finType.
Variable W : `Ch_1(A, B).
Variable n : nat.

(** nth extension of the discrete memoryless channel (DMC): *)

Local Open Scope proba_scope.
Local Open Scope ring_scope.

Definition channel_ext n := 'rV[A]_n -> {dist 'rV[B]_n}.

Local Notation "'`Ch_' n" := (channel_ext n) (at level 9, n at next level, format "'`Ch_'  n").

(** Definition of a discrete memoryless channel (DMC).
    W(y|x) = \Pi_i W_0(y_i|x_i) where W_0 is a probability
    transition matrix. *)

Local Open Scope vec_ext_scope.

Definition f (x y : 'rV_n) := \rmul_(i < n) W `(y ``_ i | x ``_ i).

Lemma f0 x y : 0 <= f x y.
Proof. apply Rle_0_big_mult => /= i; by apply dist_nonneg. Qed.

Lemma f1 x : \rsum_(y in 'rV_n) f x y = 1%R.
Proof.
set f' := fun i b => W (x ``_ i) b.
suff H : \rsum_(g : {ffun 'I_n -> B}) \rmul_(i < n) f' i (g i) = 1%R.
  rewrite -{}[RHS]H /f'.
  rewrite (reindex_onto (fun vb : 'rV_n => [ffun x => vb ``_ x])
    (fun g  => \row_(k < n) g k)) /=; last first.
    move=> g _; apply/ffunP => /= i; by rewrite ffunE mxE.
  apply eq_big => vb.
  - rewrite inE.
    apply/esym/eqP/matrixP => a b; by rewrite {a}(ord1 a) mxE ffunE.
  - move=> _; apply eq_bigr => i _; by rewrite ffunE.
rewrite -bigA_distr_bigA /= /f'.
transitivity (\rmul_(i < n) 1%R); first by apply eq_bigr => i _; rewrite pmf1.
by rewrite big_const_ord iter_Rmult pow1.
Qed.

Definition c : `Ch_n := locked (fun x => makeDist (f0 x) (f1 x)).

End DMC_sect.

End DMC.

Notation "'`Ch_' n '(' A ',' B ')'" := (@DMC.channel_ext A B n) (at level 10, A, B, n at next level, format "'`Ch_'  n  '(' A ','  B ')'") : channel_scope.

Notation "W '``^' n" := (@DMC.c _ _ W n) (at level 10) : channel_scope.

Notation "W '``(|' x ')'" := (@DMC.c _ _ W _ x) (at level 10, x at next level) : channel_scope.

Notation "W '``(' y '|' x ')'" := (@DMC.c _ _ W _ x y) (at level 10, y, x at next level) : channel_scope.

Local Open Scope proba_scope.

Lemma DMCE {A B : finType} n (W : `Ch_1(A, B)) b a :
  W ``(b | a) = \rmul_(i < n) W (a ord0 i) (b ord0 i).
Proof. rewrite /DMC.c; by unlock. Qed.

Lemma DMC_nonneg {A B : finType} n (W : `Ch_1(A, B)) b (a : 'rV_n) : 0 <= W ``(b | a).
Proof. by apply dist_nonneg. Qed.

Module OutDist.

Section OutDist_sect.

Variables A B : finType.
Variable P : dist A.
Variable W  : `Ch_1(A, B).

(** Output distribution for the discrete channel: *)

Definition f (b : B) := \rsum_(a in A) W a b * P a.

Lemma f0 (b : B) : 0 <= f b.
Proof. apply: Rle_big_0_P_g => a _; apply: Rmult_le_pos; by apply dist_nonneg. Qed.

Lemma f1 : \rsum_(b in B) f b = 1.
Proof.
rewrite exchange_big /= -(pmf1 P).
apply eq_bigr => a _; by rewrite -big_distrl /= (pmf1 (W a)) Rmult_1_l.
Qed.

Definition d : dist B := locked (makeDist f0 f1).

Lemma dE b : d b = \rsum_(a in A) W a b * P a.
Proof. rewrite /d; by unlock. Qed.

End OutDist_sect.

End OutDist.

Notation "'`O(' P , W )" := (OutDist.d P W) (at level 10, P, W at next level) : channel_scope.

Section OutDist_prop.

Variables A B : finType.

(** Equivalence between both definition when n = 1: *)

Local Open Scope reals_ext_scope.
Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.

Lemma tuple_pmf_out_dist (W : `Ch_1(A, B)) (P : dist A) n (b : 'rV_ _):
   \rsum_(j0 : 'rV[A]_n)
      ((\rmul_(i < n) W j0 ``_ i b ``_ i) * P `^ _ j0)%R =
   (`O(P , W)) `^ _ b.
Proof.
rewrite TupleDist.dE.
apply/esym.
etransitivity; first by apply eq_bigr => i _; rewrite OutDist.dE; reflexivity.
rewrite bigA_distr_big_dep /=.
rewrite (reindex_onto (fun p : 'rV_n => [ffun x => p ``_ x]) (fun y => \row_(k < n) y k)) //=; last first.
  move=> i _.
  apply/ffunP => /= n0; by rewrite ffunE mxE.
apply eq_big.
- move=> a /=.
  apply/andP; split; [by apply/finfun.familyP|].
  by apply/eqP/rowP => a'; rewrite mxE ffunE.
- move=> a Ha.
  rewrite big_split /=; congr (_ * _)%R.
  + apply eq_bigr => i /= _; by rewrite ffunE.
  + rewrite TupleDist.dE; by apply eq_bigr => i /= _; rewrite ffunE.
Qed.

End OutDist_prop.

(** Output entropy: *)

Local Open Scope entropy_scope.

Notation "'`H(' P '`o' W )" := (`H ( `O( P , W ))) (at level 10, P, W at next level) : channel_scope.

Module JointDist.

Section JointDist_sect.

Variables A B : finType.
Variable P : dist A.
Variable W : `Ch_1(A, B).

(** Joint distribution: *)

Definition f (ab : A * B) := W ab.1 ab.2 * P ab.1.

Lemma f0 (ab : A * B) : 0 <= f ab.
Proof. apply: Rmult_le_pos; by [apply ptm0 | apply dist_nonneg]. Qed.

Lemma f1 : \rsum_(ab | ab \in {: A * B}) (W ab.1) ab.2 * P ab.1 = 1.
Proof.
rewrite -(pair_big xpredT xpredT (fun a b => (W a) b * P a)) /= -(pmf1 P).
apply eq_bigr => /= t Ht; by rewrite -big_distrl /= pmf1 Rmult_1_l.
Qed.

Definition d : dist [finType of A * B] := locked (makeDist f0 f1).

Lemma dE ab : d ab = W ab.1 ab.2 * P ab.1.
Proof. rewrite /d; by unlock. Qed.

End JointDist_sect.

End JointDist.

Notation "'`J(' P , W )" := (JointDist.d P W) (at level 10, P, W at next level) : channel_scope.

Section Pr_tuple_prod_sect.

Variable A B : finType.
Variable P : dist A.
Variable W : `Ch_1(A, B).
Variable n : nat.

Lemma Pr_tuple_prod Q : Pr (`J(P `^ n, (W ``^ n))) [set x | Q x] =
  Pr (`J(P, W)) `^ n [set x | Q (tuple_prod x)].
Proof.
rewrite /Pr.
rewrite rsum_rV_prod /=.
apply eq_big.
  move=> tab /=.
  by rewrite !inE prod_tupleK.
move=> tab.
rewrite inE => Htab.
rewrite JointDist.dE DMCE TupleDist.dE -big_split /= TupleDist.dE.
apply eq_bigr => i /= _.
by rewrite JointDist.dE -snd_tnth_prod_tuple -fst_tnth_prod_tuple.
Qed.

End Pr_tuple_prod_sect.

(** Mutual entropy: *)

Notation "`H( P , W )" := (`H ( `J(P , W))) (at level 10, P, W at next level) : channel_scope.

Section conditional_entropy.

Variable A B : finType.
Variable W : `Ch_1(A, B).
Variable P : dist A.

(** Definition of conditional entropy *)

Definition cond_entropy := `H(P , W) - `H P.

End conditional_entropy.

Notation "`H( W | P )" := (cond_entropy W P) (at level 10, W, P at next level) : channel_scope.

Local Open Scope channel_scope.

Section conditional_entropy_prop.

Variables A B : finType.
Variable W : `Ch_1(A, B).
Variable P : dist A.
Local Open Scope channel_scope.
Local Open Scope Rb_scope.

(** Equivalent expression of the conditional entropy (cf. Lemma 6.23) *)

Lemma cond_entropy_single_sum : `H( W | P ) = \rsum_(a in A) P a * `H (W a).
Proof.
rewrite /cond_entropy /`H /=.
rewrite (eq_bigr (fun x => (`J( P, W)) (x.1, x.2) * log ((`J( P, W)) (x.1, x.2)))); last by case.
rewrite -(pair_big xpredT xpredT (fun a b => (`J( P, W)) (a, b) * log ((`J( P, W)) (a, b)))) /=.
rewrite /Rminus -Ropp_plus_distr /=; f_equal.
rewrite (big_morph _ morph_Ropp Ropp_0) -big_split /= (big_morph _ morph_Ropp Ropp_0).
apply eq_bigr => // a _.
case/boolP : (P a == 0); move=> Hcase.
- move/eqP in Hcase.
  rewrite Hcase !(mul0R, addR0, Ropp_0).
  transitivity (- \rsum_(b : B) 0).
    congr (- _).
    apply eq_bigr => // b _.
    by rewrite {1}JointDist.dE Hcase !(mul0R, mulR0).
  by rewrite big_const iter_Rplus mulR0 Ropp_0.
- rewrite Rmult_comm -(Rmult_1_r (-(log (P a) * P a))) -(pmf1 (W a)).
  rewrite (big_morph _ (morph_mulRDr _) (mulR0 _)) Ropp_mult_distr_r_reverse; f_equal.
  rewrite (big_morph _ (morph_mulRDr _) (mulR0 _)) -big_split /=.
  apply eq_bigr => // b _.
  case/boolP : (W a b == 0); move=> Hcase2.
  - move/eqP in Hcase2.
    by rewrite {1}JointDist.dE Hcase2 !(mul0R, mulR0, addR0).
  - rewrite {2}JointDist.dE log_mult; last 2 first.
    + apply Rlt_le_neq; first by apply dist_nonneg.
      move=> abs; by rewrite -abs eqxx in Hcase2.
    + apply Rlt_le_neq; first by apply dist_nonneg.
      move=> abs; by rewrite -abs eqxx in Hcase.
    + rewrite {1}JointDist.dE /=; by field.
Qed.

End conditional_entropy_prop.

Section mutual_information_section.

Variables A B : finType.

(** Mutual information of distributions *)

Definition mut_info_dist (P : dist [finType of A * B]) :=
  `H (ProdDist.proj1 P) + `H (ProdDist.proj2 P) - `H P.

(** Mutual information of input/output *)

Definition mut_info P (W : `Ch_1(A, B)) := `H P + `H(P `o W) - `H(P , W).

End mutual_information_section.

Notation "`I( P ; W )" := (mut_info P W) (at level 50) : channel_scope.

Section capacity_definition.

Variables A B : finType.

(** Relation defining the capacity of a channel: *)

Definition ubound {S : Type} (f : S -> R) (ub : R) := forall a, f a <= ub.

Definition lubound {S : Type} (f : S -> R) (lub : R) :=
  ubound f lub /\ forall ub, ubound f ub -> lub <= ub.

Definition capacity (W : `Ch_1(A, B)) cap := lubound (fun P => `I(P ; W)) cap.

Lemma capacity_uniq (W : `Ch_1(A, B)) r1 r2 :
  capacity W r1 -> capacity W r2 -> r1 = r2.
Proof. case=> H1 H2 [H3 H4]; apply Rle_antisym; by [apply H2 | apply H4]. Qed.

End capacity_definition.
