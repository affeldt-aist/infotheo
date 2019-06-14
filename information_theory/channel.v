(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import Reals.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.
Require Import entropy cproba chap2.

(** * Definition of channels and of the capacity *)

(** OUTLINE:
  1. Module Channel1.
     Probability transition matrix
  2. Module DMC.
     nth extension of the discrete memoryless channel
  3. Section DMC_sub_vec.
  4. Module OutDist.
     Output distribution for the discrete channel
  5. Section OutDist_prop.
     Output entropy
  6. Module JointDistChan.
     Joint distribution
  7. Section Pr_rV_prod_sect.
  8. Module CondEntropyChan.
  9. Module MutualInfoChan
  10. Section capacity_definition.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "'`Ch_1(' A ',' B ')'" (at level 10, A, B at next level,
  only parsing).
Reserved Notation "'`Ch_1*(' A ',' B ')'" (at level 10, A, B at next level).
Reserved Notation "W '`(' b '|' a ')'" (at level 10, b, a at next level,
  only parsing).
Reserved Notation "'`Ch_' n '(' A ',' B ')'" (at level 10,
  A, B, n at next level, format "'`Ch_'  n  '(' A ','  B ')'").
Reserved Notation "W '``^' n" (at level 10).
Reserved Notation "W '``(|' x ')'" (at level 10, x at next level).
Reserved Notation "W '``(' y '|' x ')'" (at level 10, y, x at next level).
Reserved Notation "'`O(' P , W )" (at level 10, P, W at next level,
  format "'`O(' P ,  W )").
Reserved Notation "'`J(' P , W )" (at level 10, P, W at next level,
  format "'`J(' P ,  W )").
Reserved Notation "'`H(' P '`o' W )" (at level 10, P, W at next level,
  format "'`H(' P  '`o'  W )").
Reserved Notation "`H( P , W )" (at level 10, P, W at next level,
  format "`H( P ,  W )").
Reserved Notation "`H( W | P )" (at level 10, W, P at next level).
Reserved Notation "`I( P , W )" (at level 50, format "`I( P ,  W )").

Local Open Scope R_scope.

Module Channel1.
Section channel1.
Variables A B : finType.

(* Definition of a discrete channel of input alphabet A and output alphabet B.
   It is a collection of probability mass functions, one for each a in A: *)
Local Notation "'`Ch_1'" := (A -> dist B).

(* Channels with non-empty alphabet: *)
Record chan_star := mkChan {
  c :> `Ch_1 ;
  input_not_0 : (0 < #|A|)%nat }.

Local Notation "'`Ch_1*'" := (chan_star).

Lemma chan_star_eq (c1 c2 : `Ch_1*) : c c1 = c c2 -> c1 = c2.
Proof.
move: c1 c2 => [c1 Hc1] [c2 Hc2] /= <-{c2}; congr mkChan; exact: eq_irrelevance.
Qed.

End channel1.
End Channel1.

Definition chan_star_coercion := Channel1.c.
Coercion chan_star_coercion : Channel1.chan_star >-> Funclass.

Notation "'`Ch_1(' A ',' B ')'" := (A -> dist B) : channel_scope.
Local Open Scope channel_scope.
Notation "'`Ch_1*(' A ',' B ')'" := (@Channel1.chan_star A B) : channel_scope.
Notation "W '`(' b '|' a ')'" := ((W : `Ch_1(_, _)) a b) : channel_scope.
Local Open Scope proba_scope.
Local Open Scope vec_ext_scope.
Local Open Scope entropy_scope.

Module DMC.
Section def.

Variables (A B : finType) (W : `Ch_1(A, B)) (n : nat).

Local Open Scope ring_scope.

Definition channel_ext n := 'rV[A]_n -> {dist 'rV[B]_n}.

(* Definition of a discrete memoryless channel (DMC).
   W(y|x) = \Pi_i W_0(y_i|x_i) where W_0 is a probability
   transition matrix. *)
Definition f (x : 'rV_n) := [ffun y : 'rV_n => \rprod_(i < n) W `(y ``_ i | x ``_ i)].

Lemma f0 x y : 0 <= f x y.
Proof. rewrite ffunE; apply rprodr_ge0 => ?; exact: dist_ge0. Qed.

Lemma f1 x : \rsum_(y in 'rV_n) f x y = 1%R.
Proof.
set f' := fun i b => W (x ``_ i) b.
suff H : \rsum_(g : {ffun 'I_n -> B}) \rprod_(i < n) f' i (g i) = 1%R.
  rewrite -{}[RHS]H /f'.
  rewrite (reindex_onto (fun vb : 'rV_n => [ffun x => vb ``_ x])
    (fun g  => \row_(k < n) g k)) /=; last first.
    move=> g _; apply/ffunP => /= i; by rewrite ffunE mxE.
  apply eq_big => vb.
  - rewrite inE.
    apply/esym/eqP/rowP => a; by rewrite mxE ffunE.
  - move=> _; rewrite ffunE; apply eq_bigr => i _; by rewrite ffunE.
rewrite -bigA_distr_bigA /= /f'.
transitivity (\rprod_(i < n) 1%R); first by apply eq_bigr => i _; rewrite epmf1.
by rewrite big1.
Qed.

Definition c : channel_ext n := locked (fun x => makeDist (f0 x) (f1 x)).

End def.
End DMC.

Arguments DMC.c {A} {B}.

Notation "'`Ch_' n '(' A ',' B ')'" := (@DMC.channel_ext A B n) : channel_scope.
Notation "W '``^' n" := (DMC.c W n) : channel_scope.
Notation "W '``(|' x ')'" := (DMC.c W _ x) : channel_scope.
Notation "W '``(' y '|' x ')'" := (DMC.c W _ x y) : channel_scope.

Lemma DMCE (A B : finType) n (W : `Ch_1(A, B)) b a :
  W ``(b | a) = \rprod_(i < n) W (a ``_ i) (b ``_ i).
Proof. by rewrite /DMC.c; unlock; rewrite ffunE. Qed.

Lemma DMC_ge0 (A B : finType) n (W : `Ch_1(A, B)) b (a : 'rV_n) : 0 <= W ``(b | a).
Proof. exact: dist_ge0. Qed.

Section DMC_sub_vec.

Variables (A B : finType) (W : `Ch_1(A, B)).
Variable n' : nat.
Let n := n'.+1.
Variable tb : 'rV[B]_n.

Lemma rprod_sub_vec (D : {set 'I_n}) (t : 'rV_n) :
  \rprod_(i < #|D|) W ((t # D) ``_ i) ((tb # D) ``_ i) =
  \rprod_(i in D) W (t ``_ i) (tb ``_ i).
Proof.
case/boolP : (D == set0) => [/eqP -> |].
  rewrite big_set0 big_hasC //.
  apply/hasPn => /=.
  rewrite cards0; by case.
case/set0Pn => /= i iD.
pose f : 'I_n -> 'I_#|D| :=
  fun i => match Bool.bool_dec (i \in D) true with
             | left H => enum_rank_in H i
             | _ => enum_rank_in iD i
           end.
rewrite (reindex_onto (fun i : 'I_#|D| => enum_val i) f) /=.
  apply eq_big => j.
    rewrite /f /=.
    case: Bool.bool_dec => [a|].
      by rewrite enum_valK_in a eqxx.
    by rewrite enum_valP.
  by rewrite /sub_vec 2!mxE.
move=> j jD.
rewrite /f /=.
case: Bool.bool_dec => [a| //].
by rewrite enum_rankK_in.
Qed.

Lemma DMC_sub_vecE (V : {set 'I_n}) (t : 'rV_n) :
  W ``(tb # V | t # V) = \rprod_(i in V) W (t ``_ i) (tb ``_ i).
Proof. by rewrite DMCE -rprod_sub_vec. Qed.

End DMC_sub_vec.

Module OutDist.
Section def.
Variables (A B : finType) (P : dist A) (W  : `Ch_1(A, B)).
Definition f := [ffun b : B => \rsum_(a in A) W a b * P a].
Lemma f0 (b : B) : 0 <= f b.
Proof. rewrite ffunE; apply: rsumr_ge0 => a _; apply: mulR_ge0; exact/dist_ge0. Qed.
Lemma f1 : \rsum_(b in B) f b = 1.
Proof.
rewrite /f; evar (h : B -> R); rewrite (eq_bigr h); last first.
  move=> a _; rewrite ffunE /h; reflexivity.
rewrite {}/h exchange_big /= -(epmf1 P).
apply eq_bigr => a _; by rewrite -big_distrl /= (epmf1 (W a)) mul1R.
Qed.
Definition d : dist B := locked (makeDist f0 f1).
Lemma dE b : d b = \rsum_(a in A) W a b * P a.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
End def.
End OutDist.

Notation "'`O(' P , W )" := (OutDist.d P W) : channel_scope.

Section OutDist_prop.
Variables A B : finType.

Local Open Scope ring_scope.

Lemma tuple_pmf_out_dist (W : `Ch_1(A, B)) (P : dist A) n (b : 'rV_ _):
   \rsum_(j : 'rV[A]_n)
      ((\rprod_(i < n) W j ``_ i b ``_ i) * P `^ _ j)%R =
   (`O(P, W)) `^ _ b.
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

Notation "'`H(' P '`o' W )" := (`H ( `O( P , W ) )) : channel_scope.

Module JointDistChan.
Section def.
Variables (A B : finType) (P : dist A) (W : `Ch_1(A, B)).
Definition d : {dist A * B} := locked (ProdDist.d P W).
Lemma dE ab : d ab = P ab.1 * W ab.1 ab.2.
Proof. by rewrite /d; unlock => /=; rewrite ProdDist.dE. Qed.
End def.
Local Notation "'`J(' P , W )" := (JointDistChan.d P W).
Section prop.
Variables (A B : finType) (P : dist A) (W : `Ch_1(A, B)) (n : nat).
Lemma Pr_DMC_rV_prod (Q : 'rV_n * 'rV_n -> bool) :
  Pr (`J(P `^ n, W ``^ n)) [set x | Q x] =
  Pr (`J(P, W)) `^ n       [set x | Q (rV_prod x)].
Proof.
rewrite /Pr [RHS]big_rV_prod /=.
apply eq_big => y; first by rewrite !inE prod_rVK.
rewrite inE => Qy.
rewrite JointDistChan.dE DMCE TupleDist.dE -big_split /= TupleDist.dE.
apply eq_bigr => i /= _.
by rewrite JointDistChan.dE -snd_tnth_prod_rV -fst_tnth_prod_rV.
Qed.
Lemma Pr_DMC_fst (Q : 'rV_n -> bool) :
  Pr (`J(P, W)) `^ n [set x | Q (rV_prod x).1 ] =
  Pr P `^ n [set x | Q x ].
Proof.
rewrite {1}/Pr big_rV_prod /= -(pair_big_fst _ _ [pred x | Q x]) //=; last first.
  move=> t /=.
  rewrite SetDef.pred_of_setE /= SetDef.finsetE /= ffunE. (* TODO: clean *)
  do 2 f_equal.
  apply/rowP => a; by rewrite !mxE.
transitivity (\rsum_(i | Q i) (P `^ n i * (\rsum_(y in 'rV[B]_n) W ``(y | i)))).
  apply eq_bigr => ta Sta.
  rewrite big_distrr; apply eq_bigr => tb _ /=.
  rewrite DMCE [in RHS]TupleDist.dE -[in RHS]big_split /= TupleDist.dE.
  apply eq_bigr => j _.
  by rewrite JointDistChan.dE /= -fst_tnth_prod_rV -snd_tnth_prod_rV.
transitivity (\rsum_(i | Q i) P `^ _ i).
  apply eq_bigr => i _; by rewrite (epmf1 (W ``(| i))) mulR1.
rewrite /Pr; apply eq_bigl => t; by rewrite !inE.
Qed.
Local Open Scope ring_scope.
Lemma Pr_DMC_out m (S : {set 'rV_m}) :
  Pr (`J(P , W) `^ m) [set x | (rV_prod x).2 \notin S] =
  Pr (`O(P , W) `^ m) (~: S).
Proof.
rewrite {1}/Pr big_rV_prod /= -(pair_big_snd _ _ [pred x | x \notin S]) //=; last first.
  move=> tab /=.
  rewrite SetDef.pred_of_setE /= SetDef.finsetE /= ffunE. (* TODO: clean *)
  do 3 f_equal.
  apply/rowP => a; by rewrite !mxE.
rewrite /= /Pr /= exchange_big /=.
apply eq_big => tb.
  by rewrite !inE.
move=> Htb.
rewrite TupleDist.dE.
etransitivity; last by apply eq_bigr => i _; rewrite OutDist.dE; reflexivity.
rewrite bigA_distr_bigA /=.
rewrite (reindex_onto (fun p : 'rV[A]_m => [ffun x => p ord0 x])
  (fun y : {ffun 'I_m -> A} => \row_(i < m) y i)) /=; last first.
  move=> f _.
  apply/ffunP => /= m0.
  by rewrite ffunE mxE.
apply eq_big => ta.
  rewrite inE; apply/esym.
  by apply/eqP/rowP => a; rewrite mxE ffunE.
move=> Hta.
rewrite TupleDist.dE /=; apply eq_bigr => l _.
by rewrite JointDistChan.dE -fst_tnth_prod_rV -snd_tnth_prod_rV ffunE mulRC.
Qed.
End prop.
End JointDistChan.

Notation "'`J(' P , W )" := (JointDistChan.d P W) : channel_scope.

Section relation_channel_cproba.

Variables (A B : finType) (W : `Ch_1(A, B)) (P : dist A).
Let QP := Swap.d (`J(P, W)).

Lemma channel_cPr : forall a b, P a != 0 -> W a b = \Pr_QP[[set b]|[set a]].
Proof.
move=> a b Pa0.
rewrite (@CDist.E _ _ (CDist.mkt P W)) //=; last exact/eqP.
congr cPr.
apply/dist_ext => -[b0 a0].
by rewrite !Swap.dE JointDistChan.dE /= /CDist.joint_of /= ProdDist.dE.
Qed.

End relation_channel_cproba.

(* Mutual entropy *)
Notation "`H( P , W )" := (`H (`J(P, W)) ) : channel_scope.

(* Definition of conditional entropy using an input distribution and a channel *)
Module CondEntropyChan.
Section def.
Variables (A B : finType) (W : `Ch_1(A, B)) (P : dist A).
Definition h := `H(P, W) - `H P.
End def.
End CondEntropyChan.

Notation "`H( W | P )" := (CondEntropyChan.h W P) : channel_scope.

Section condentropychan_prop.
Variables (A B : finType) (W : `Ch_1(A, B)) (P : dist A).

Lemma CondEntropyChanE : `H(W | P) = CondEntropy.h (Swap.d (`J(P, W))).
Proof.
rewrite /CondEntropyChan.h.
move: (chain_rule (`J(P, W))); rewrite /JointEntropy.h => ->.
rewrite /JointDistChan.d; unlock; rewrite ProdDist.fst addRC addRK.
by rewrite /JointDistChan.d; unlock.
Qed.

Lemma CondEntropyChanE2 : `H(W | P) = \rsum_(a in A) P a * `H (W a).
Proof.
rewrite CondEntropyChanE CondEntropy.hE big_morph_oppR; apply eq_bigr => a _.
rewrite big_morph_oppR /entropy mulRN -mulNR big_distrr; apply eq_bigr => b _.
rewrite /= Swap.dI JointDistChan.dE /= mulNR mulRA.
case/boolP: (P a == 0) => [/eqP ->|Pa0].
  by rewrite !(mulR0,mul0R).
by rewrite -channel_cPr.
Qed.
End condentropychan_prop.

Module MutualInfoChan.
Section def.
Variables A B : finType.

(* Mutual information of distributions *)
Definition mut_info_dist (P : {dist A * B}) :=
  `H (Bivar.fst P) + `H (Bivar.snd P) - `H P.

(* Mutual information of input/output *)
Definition mut_info P (W : `Ch_1(A, B)) := `H P + `H(P `o W) - `H(P , W).

End def.
End MutualInfoChan.

Notation "`I( P , W )" := (MutualInfoChan.mut_info P W) : channel_scope.

Section mutualinfo_prop.
Variables (A B : finType) (W : `Ch_1(A, B)) (P : dist A).

Lemma mut_info_chanE : `I(P, W) = MutualInfo.mi (Swap.d (`J(P, W))).
Proof.
rewrite /MutualInfoChan.mut_info MutualInfo.miE -CondEntropyChanE.
rewrite /CondEntropyChan.h -[in RHS]addR_opp oppRB addRCA addRA; congr (_ + _ + _).
congr `H.
rewrite Swap.fst.
apply/dist_ext => b.
rewrite OutDist.dE Bivar.sndE; apply/eq_bigr => a _.
by rewrite JointDistChan.dE mulRC.
Qed.
End mutualinfo_prop.

Section capacity_definition.

Variables A B : finType.

(** Relation defining the capacity of a channel: *)

Definition ubound {S : Type} (f : S -> R) (ub : R) := forall a, f a <= ub.

Definition lubound {S : Type} (f : S -> R) (lub : R) :=
  ubound f lub /\ forall ub, ubound f ub -> lub <= ub.

Definition capacity (W : `Ch_1(A, B)) cap := lubound (fun P => `I(P , W)) cap.

Lemma capacity_uniq (W : `Ch_1(A, B)) r1 r2 :
  capacity W r1 -> capacity W r2 -> r1 = r2.
Proof. move=> [? H1] [? H2]; rewrite eqR_le; split; [exact: H1| exact: H2]. Qed.

End capacity_definition.
