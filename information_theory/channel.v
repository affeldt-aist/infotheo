(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg matrix.
Require Import Reals.
From mathcomp Require Import Rstruct.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop fdist.
Require Import proba entropy jfdist chap2.

(******************************************************************************)
(*                 Definition of channels and of the capacity                 *)
(*                                                                            *)
(* `Ch(A, B)  == definition of a discrete channel of input alphabet A and     *)
(*               output alphabet B; it is a collection of probability mass    *)
(*               functions, one for each a in A (i.e., a probability          *)
(*               transition matrix                                            *)
(* `Ch*(A, B) == channels with non-empty alphabet                             *)
(* W `(b | a) == probability of receiving b knowing a was sent over the       *)
(*               channel W                                                    *)
(* W ``^ n, W ``(| x), W ``(y | x) == definition of a discrete memoryless     *)
(*               channel (DMC, or nth extension of the discrete memoryless    *)
(*               channel); W(y|x) = \Pi_i W_0(y_i|x_i) where W_0 is a         *)
(*               probability transition matrix                                *)
(* `O(P, W)   == output distribution for the discrete channel                 *)
(* `H(P `o W) == output entropy                                               *)
(* `J(P, W)   == joint distribution                                           *)
(* `H(P , W)  == mutual entropy                                               *)
(* `H(W | P)  == definition of conditional entropy using an input             *)
(*               distribution and a channel                                   *)
(* `I(P, W)   == mutual information of input/output                           *)
(* capacity   == capacity of a channel                                        *)
(*                                                                            *)
(******************************************************************************)

Declare Scope channel_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "'`Ch(' A ',' B ')'" (at level 10, A, B at next level).
Reserved Notation "'`Ch*(' A ',' B ')'" (at level 10, A, B at next level).
Reserved Notation "W '`(' b '|' a ')'" (at level 10, b, a at next level).
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

Local Notation "'`Ch'" := (A -> fdist B) (only parsing).

Record chan_star := mkChan {
  c :> `Ch ;
  input_not_0 : (0 < #|A|)%nat }.

Local Notation "'`Ch*'" := (chan_star).

Lemma chan_star_eq (c1 c2 : `Ch*) : c c1 = c c2 -> c1 = c2.
Proof.
move: c1 c2 => [c1 Hc1] [c2 Hc2] /= <-{c2}; congr mkChan; exact: eq_irrelevance.
Qed.

End channel1.
End Channel1.

Definition chan_star_coercion := Channel1.c.
Coercion chan_star_coercion : Channel1.chan_star >-> Funclass.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Notation "'`Ch(' A ',' B ')'" := (A -> {fdist B}) (only parsing) : channel_scope.
Local Open Scope channel_scope.
Notation "'`Ch*(' A ',' B ')'" := (@Channel1.chan_star A B) : channel_scope.
Notation "W '`(' b '|' a ')'" := ((W : `Ch(_, _)) a b) (only parsing) : channel_scope.
Local Open Scope proba_scope.
Local Open Scope vec_ext_scope.
Local Open Scope entropy_scope.

Module DMC.
Section def.

Variables (A B : finType) (W : `Ch(A, B)) (n : nat).

Local Open Scope ring_scope.

Definition f (x : 'rV[A]_n) := [ffun y : 'rV[B]_n => (\prod_(i < n) W `(y ``_ i | x ``_ i))%R].

Lemma f0 x y : 0 <= f x y. Proof. rewrite ffunE; exact: prodR_ge0. Qed.

Lemma f1 x : (\sum_(y in 'rV_n) f x y = 1)%R.
Proof.
set f' := fun i b => W (x ``_ i) b.
suff H : (\sum_(g : {ffun 'I_n -> B}) \prod_(i < n) f' i (g i) = 1)%R.
  rewrite -{}[RHS]H /f'.
  rewrite (reindex_onto (fun vb : 'rV_n => [ffun x => vb ``_ x])
    (fun g  => \row_(k < n) g k)) /=; last first.
    move=> g _; apply/ffunP => /= i; by rewrite ffunE mxE.
  apply eq_big => vb.
  - rewrite inE.
    apply/esym/eqP/rowP => a; by rewrite mxE ffunE.
  - move=> _; rewrite ffunE; apply eq_bigr => i _; by rewrite ffunE.
by rewrite -bigA_distr_bigA /= /f' big1 // => i _; rewrite FDist.f1.
Qed.

Definition c : `Ch('rV[A]_n, 'rV[B]_n) := locked (fun x => FDist.make (f0 x) (f1 x)).

End def.
End DMC.

Arguments DMC.c {A} {B}.

Notation "W '``^' n" := (DMC.c W n) : channel_scope.
Notation "W '``(|' x ')'" := (DMC.c W _ x) : channel_scope.
Notation "W '``(' y '|' x ')'" := (DMC.c W _ x y) : channel_scope.

Lemma DMCE (A B : finType) n (W : `Ch(A, B)) b a :
  W ``(b | a) = \prod_(i < n) W (a ``_ i) (b ``_ i).
Proof. by rewrite /DMC.c; unlock; rewrite ffunE. Qed.

(*Lemma DMC_ge0 (A B : finType) n (W : `Ch(A, B)) b (a : 'rV_n) : 0 <= W ``(b | a).
Proof. exact: fdist_ge0. Qed.*)

Section DMC_sub_vec.

Variables (A B : finType) (W : `Ch(A, B)).
Variable n' : nat.
Let n := n'.+1.
Variable tb : 'rV[B]_n.

Lemma rprod_sub_vec (D : {set 'I_n}) (t : 'rV_n) :
  \prod_(i < #|D|) W ((t # D) ``_ i) ((tb # D) ``_ i) =
  \prod_(i in D) W (t ``_ i) (tb ``_ i).
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
  W ``(tb # V | t # V) = \prod_(i in V) W (t ``_ i) (tb ``_ i).
Proof. by rewrite DMCE -rprod_sub_vec. Qed.

End DMC_sub_vec.

Module OutFDist.
Section def.
Variables (A B : finType) (P : fdist A) (W  : `Ch(A, B)).
Definition f := [ffun b : B => \sum_(a in A) W a b * P a].
Lemma f0 (b : B) : 0 <= f b.
Proof. by rewrite ffunE; apply: sumR_ge0 => a _; exact: mulR_ge0. Qed.
Lemma f1 : \sum_(b in B) f b = 1.
Proof.
under eq_bigr do rewrite ffunE /=.
rewrite exchange_big /= -(FDist.f1 P).
by apply eq_bigr => a _; rewrite -big_distrl /= (FDist.f1 (W a)) mul1R.
Qed.
Definition d : fdist B := locked (FDist.make f0 f1).
Lemma dE b : d b = \sum_(a in A) W a b * P a.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
End def.
End OutFDist.

Notation "'`O(' P , W )" := (OutFDist.d P W) : channel_scope.

Section OutFDist_prop.
Variables A B : finType.

Local Open Scope ring_scope.

Lemma tuple_pmf_out_fdist (W : `Ch(A, B)) (P : fdist A) n (b : 'rV_ _):
   (\sum_(j : 'rV[A]_n)
      (\prod_(i < n) W j ``_ i b ``_ i) * P `^ _ j)%R =
   (`O(P, W)) `^ _ b.
Proof.
rewrite fdist_rVE; apply/esym.
etransitivity; first by apply eq_bigr => i _; rewrite OutFDist.dE; reflexivity.
rewrite bigA_distr_big_dep /=.
rewrite (reindex_onto (fun p : 'rV_n => [ffun x => p ``_ x]) (fun y => \row_(k < n) y k)) //=; last first.
  by move=> i _; apply/ffunP => /= n0; rewrite ffunE mxE.
apply eq_big.
- move=> a /=.
  apply/andP; split; [by apply/finfun.familyP|].
  by apply/eqP/rowP => a'; rewrite mxE ffunE.
- move=> a Ha.
  rewrite big_split /=; congr (_ * _)%R.
  + by apply eq_bigr => i /= _; rewrite ffunE.
  + by rewrite fdist_rVE; apply eq_bigr => i /= _; rewrite ffunE.
Qed.

End OutFDist_prop.

Notation "'`H(' P '`o' W )" := (`H ( `O( P , W ) )) : channel_scope.

Module JointFDistChan.
Section def.
Variables (A B : finType) (P : fdist A) (W : `Ch(A, B)).
Definition d : {fdist A * B} := locked (fdist_prod P W).
Lemma dE ab : d ab = P ab.1 * W ab.1 ab.2.
Proof. by rewrite /d; unlock => /=; rewrite fdist_prodE. Qed.
End def.
Local Notation "'`J(' P , W )" := (d P W).
Section prop.
Variables (A B : finType) (P : fdist A) (W : `Ch(A, B)) (n : nat).
Lemma Pr_DMC_rV_prod (Q : 'rV_n * 'rV_n -> bool) :
  Pr (`J(P `^ n, W ``^ n)) [set x | Q x] =
  Pr (`J(P, W)) `^ n       [set x | Q (rV_prod x)].
Proof.
rewrite /Pr [RHS]big_rV_prod /=.
apply eq_big => y; first by rewrite !inE prod_rVK.
rewrite inE => Qy.
rewrite dE DMCE fdist_rVE -big_split /= fdist_rVE.
apply eq_bigr => i /= _.
by rewrite JointFDistChan.dE -snd_tnth_prod_rV -fst_tnth_prod_rV.
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
transitivity (\sum_(i | Q i) (P `^ n i * (\sum_(y in 'rV[B]_n) W ``(y | i)))).
  apply eq_bigr => ta Sta.
  rewrite big_distrr; apply eq_bigr => tb _ /=.
  rewrite DMCE [in RHS]fdist_rVE -[in RHS]big_split /= fdist_rVE.
  apply eq_bigr => j _.
  by rewrite dE /= -fst_tnth_prod_rV -snd_tnth_prod_rV.
transitivity (\sum_(i | Q i) P `^ _ i).
  apply eq_bigr => i _; by rewrite (FDist.f1 (W ``(| i))) mulR1.
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
rewrite fdist_rVE.
etransitivity; last by apply eq_bigr => i _; rewrite OutFDist.dE; reflexivity.
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
rewrite fdist_rVE /=; apply eq_bigr => l _.
by rewrite dE -fst_tnth_prod_rV -snd_tnth_prod_rV ffunE mulRC.
Qed.
End prop.
End JointFDistChan.

Notation "'`J(' P , W )" := (JointFDistChan.d P W) : channel_scope.

Section relation_channel_cproba.

Variables (A B : finType) (W : `Ch(A, B)) (P : fdist A).
Let QP := fdistX (`J(P, W)).

Lemma channel_cPr : forall a b, P a != 0 -> W a b = \Pr_QP[[set b]|[set a]].
Proof.
move=> a b Pa0.
rewrite (@jfdist_prodE _ _ (mkjfdist_prod_type P W)) //=; last exact/eqP.
congr (\Pr_ _ [_ | _ ]).
apply/fdist_ext => -[b0 a0].
by rewrite !fdistXE JointFDistChan.dE /= /jfdist_prod /= fdist_prodE.
Qed.

End relation_channel_cproba.

Notation "`H( P , W )" := (`H (`J(P, W)) ) : channel_scope.

Module CondEntropyChan.
Section def.
Variables (A B : finType) (W : `Ch(A, B)) (P : fdist A).
Definition h := `H(P, W) - `H P.
End def.
End CondEntropyChan.

Notation "`H( W | P )" := (CondEntropyChan.h W P) : channel_scope.

Section condentropychan_prop.
Variables (A B : finType) (W : `Ch(A, B)) (P : fdist A).

(* TODO: rename *)
Lemma CondEntropyChanE : `H(W | P) = cond_entropy (fdistX (`J(P, W))).
Proof.
rewrite /CondEntropyChan.h.
move: (chain_rule (`J(P, W))); rewrite /joint_entropy => ->.
by rewrite /JointFDistChan.d; unlock; rewrite fdist_prod1 addRC addRK.
Qed.

Lemma CondEntropyChanE2 : `H(W | P) = \sum_(a in A) P a * `H (W a).
Proof.
rewrite CondEntropyChanE cond_entropyE big_morph_oppR; apply eq_bigr => a _.
rewrite big_morph_oppR /entropy mulRN -mulNR big_distrr; apply eq_bigr => b _.
rewrite /= fdistXI JointFDistChan.dE /= mulNR mulRA.
have [->|Pa0] := eqVneq (P a) 0; first by rewrite !(mulR0,mul0R).
by rewrite -channel_cPr.
Qed.

End condentropychan_prop.

Module MutualInfoChan.
Section def.
Local Open Scope fdist_scope.
Variables A B : finType.

(* Mutual information of distributions *)
Definition mut_info_dist (P : {fdist A * B}) := `H (P`1) + `H (P`2) - `H P.

Definition mut_info P (W : `Ch(A, B)) := `H P + `H(P `o W) - `H(P , W).

End def.
End MutualInfoChan.

Notation "`I( P , W )" := (MutualInfoChan.mut_info P W) : channel_scope.

Section mutualinfo_prop.
Variables (A B : finType) (W : `Ch(A, B)) (P : fdist A).

Lemma mut_info_chanE : `I(P, W) = mutual_info (fdistX (`J(P, W))).
Proof.
rewrite /MutualInfoChan.mut_info mutual_infoE -CondEntropyChanE.
rewrite /CondEntropyChan.h -[in RHS]addR_opp oppRB addRCA addRA; congr (_ + _ + _).
congr `H.
rewrite fdistX1.
apply/fdist_ext => b.
rewrite OutFDist.dE fdist_sndE; apply/eq_bigr => a _.
by rewrite JointFDistChan.dE mulRC.
Qed.
End mutualinfo_prop.

From mathcomp Require Import classical_sets.
Local Open Scope classical_set_scope.

Definition capacity (A B : finType) (W : `Ch(A, B)) :=
  reals.sup [set `I(P, W) | P in @setT (fdist A)].
