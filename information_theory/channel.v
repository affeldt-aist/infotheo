(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import Rstruct reals classical_sets.
Require Import ssr_ext ssralg_ext bigop_ext realType_ext realType_ln fdist.
Require Import proba entropy jfdist_cond.

(**md**************************************************************************)
(* # Definition of channels and of the capacity                               *)
(*                                                                            *)
(* ```                                                                        *)
(*  `Ch(A, B) == discrete channel of input alphabet A and output alphabet B;  *)
(*               it is a collection of probability mass functions, one for    *)
(*               each a in A (i.e., a probability transition matrix           *)
(* `Ch*(A, B) == channels with non-empty alphabet                             *)
(* W `(b | a) == probability of receiving b knowing a was sent over the       *)
(*               channel W                                                    *)
(* W ``^ n, W ``(| x), W ``(y | x) == definition of a discrete memoryless     *)
(*               channel (DMC, or nth extension of the discrete memoryless    *)
(*               channel); W(y|x) = \Pi_i W_0(y_i|x_i) where W_0 is a         *)
(*               probability transition matrix                                *)
(*   `O(P, W) == output distribution for the channel                          *)
(* `H(P `o W) == output entropy for the channel                               *)
(* The input/output joint distribution for the channel is P `X W.             *)
(*  `H(P , W) == the input/output joint entropy for the channel               *)
(*  `H(W | P) == definition of conditional entropy using an input             *)
(*               distribution and a channel                                   *)
(*   `I(P, W) == the input/output mutual information for the channel          *)
(*   capacity == capacity of a channel                                        *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory Num.Theory.

Declare Scope channel_scope.
Delimit Scope channel_scope with channel.

Local Open Scope channel_scope.
Local Open Scope fdist_scope.
Local Open Scope ring_scope.

Reserved Notation "'`Ch(' A ',' B ')'" (at level 10, A, B at next level).
Reserved Notation "'`Ch*(' A ',' B ')'" (at level 10, A, B at next level).
Reserved Notation "W '`(' b '|' a ')'" (at level 10, b, a at next level).
Reserved Notation "W '``^' n" (at level 10).
Reserved Notation "W '``(|' x ')'" (at level 10, x at next level).
Reserved Notation "W '``(' y '|' x ')'" (at level 10, y, x at next level).
Reserved Notation "'`O(' P , W )" (at level 10, P, W at next level,
  format "'`O(' P ,  W )").
Reserved Notation "'`H(' P '`o' W )" (at level 10, P, W at next level,
  format "'`H(' P  '`o'  W )").
Reserved Notation "`H( P , W )" (at level 10, P, W at next level,
  format "`H( P ,  W )").
Reserved Notation "`H( W | P )" (at level 10, W, P at next level).
Reserved Notation "`I( P , W )" (at level 50, format "`I( P ,  W )").

Module Channel1.
Section channel1.
Variables A B : finType.

Local Notation "'`Ch'" := (A -> {fdist B}) (only parsing).

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

Local Open Scope proba_scope.

Notation "'`Ch(' A ',' B ')'" := (A -> {fdist B}) (only parsing) : channel_scope.
Notation "'`Ch*(' A ',' B ')'" := (@Channel1.chan_star A B) : channel_scope.
Notation "W '`(' b '|' a ')'" := ((W : `Ch(_, _)) a b) (only parsing) : channel_scope.

Local Open Scope proba_scope.
Local Open Scope vec_ext_scope.
Local Open Scope entropy_scope.

Module DMC.
Section def.
Local Open Scope ring_scope.
Variables (A B : finType) (W : `Ch(A, B)) (n : nat).

Definition f (x : 'rV[A]_n) :=
  [ffun y : 'rV[B]_n => (\prod_(i < n) W `(y ``_ i | x ``_ i))].

Lemma f0 x y : (0 <= f x y). Proof. rewrite ffunE; exact: prodr_ge0. Qed.

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

Definition c : `Ch('rV[A]_n, 'rV[B]_n) :=
  locked (fun x => FDist.make (f0 x) (f1 x)).

End def.
End DMC.

Arguments DMC.c {A} {B}.

Notation "W '``^' n" := (DMC.c W n) : channel_scope.
Notation "W '``(|' x ')'" := (DMC.c W _ x) : channel_scope.
Notation "W '``(' y '|' x ')'" := (DMC.c W _ x y) : channel_scope.

Lemma DMCE (A B : finType) n (W : `Ch(A, B)) b a :
  W ``(b | a) = \prod_(i < n) W (a ``_ i) (b ``_ i).
Proof. by rewrite /DMC.c; unlock; rewrite ffunE. Qed.

Section DMC_sub_vec.
Variables (A B : finType) (W : `Ch(A, B)) (n : nat) (tb : 'rV[B]_n).

Lemma rprod_sub_vec (D : {set 'I_n}) (t : 'rV_n) :
  \prod_(i < #|D|) W ((t \# D) ``_ i) ((tb \# D) ``_ i) =
  \prod_(i in D) W (t ``_ i) (tb ``_ i).
Proof.
have [->|/set0Pn[i iD]] := eqVneq D finset.set0.
  by rewrite big_set0 big_hasC //; apply/hasPn => /=; rewrite cards0; case.
pose f : 'I_n -> 'I_#|D| :=
  fun i => match Bool.bool_dec (i \in D) true with
             | left H => enum_rank_in H i
             | _ => enum_rank_in iD i
           end.
rewrite (reindex_onto (fun i : 'I_#|D| => enum_val i) f) /=.
  apply: eq_big => j; last by rewrite /sub_vec 2!mxE.
  rewrite /f /=; case: Bool.bool_dec => [a|].
    by rewrite enum_valK_in a eqxx.
  by rewrite enum_valP.
move=> j jD.
by rewrite /f /=; case: Bool.bool_dec => [a| //]; rewrite enum_rankK_in.
Qed.

Lemma DMC_sub_vecE (V : {set 'I_n}) (t : 'rV_n) :
  W ``(tb \# V | t \# V) = \prod_(i in V) W (t ``_ i) (tb ``_ i).
Proof. by rewrite DMCE -rprod_sub_vec. Qed.

End DMC_sub_vec.

Section fdist_out.
Variables (A B : finType) (P : {fdist A}) (W  : A -> {fdist B}).

Definition f := [ffun b : B => \sum_(a in A) W a b * P a].

Let f0 (b : B) : 0 <= f b.
Proof.
by rewrite ffunE; apply/RleP; apply/RleP/sumr_ge0 => a _; rewrite mulr_ge0.
Qed.

Let f1 : \sum_(b in B) f b = 1.
Proof.
under eq_bigr do rewrite ffunE /=.
rewrite exchange_big /= -[RHS](FDist.f1 P).
by apply eq_bigr => a _; rewrite -big_distrl /= (FDist.f1 (W a)) mul1r.
Qed.

Definition fdist_out : {fdist B} := locked (FDist.make f0 f1).

Lemma fdist_outE b : fdist_out b = \sum_(a in A) W a b * P a.
Proof. by rewrite /fdist_out; unlock; rewrite ffunE. Qed.

End fdist_out.

Notation "'`O(' P , W )" := (fdist_out P W) : channel_scope.

Notation "'`H(' P '`o' W )" := (`H ( `O( P , W ) )) : channel_scope.

Section fdist_out_prop.
Variables A B : finType.

Lemma fdist_rV_out (W : `Ch(A, B)) (P : {fdist A}) n (b : 'rV_n):
  (`O(P, W) `^ _) b =
  \sum_(j : 'rV[A]_n) ((\prod_(i < n) W j ``_ i b ``_ i) * (P `^ _) j).
Proof.
rewrite fdist_rVE.
under eq_bigr do rewrite fdist_outE.
rewrite bigA_distr_big_dep /=.
rewrite (reindex_onto (fun p : 'rV_n => [ffun x => p ``_ x])
                      (fun y => \row_(k < n) y k)) //=; last first.
  by move=> i _; apply/ffunP => /= n0; rewrite ffunE mxE.
apply: eq_big.
- move=> a /=; apply/andP; split; first exact/finfun.familyP.
  by apply/eqP/rowP => a'; rewrite mxE ffunE.
- move=> a Ha; rewrite big_split /=; congr (_ * _)%R.
  + by apply eq_bigr => i /= _; rewrite ffunE.
  + by rewrite fdist_rVE; apply eq_bigr => i /= _; rewrite ffunE.
Qed.
Local Close Scope ring_scope.

Lemma fdistX_prod_out (W : `Ch(A, B)) (P : {fdist A}) : (fdistX (P `X W))`1 = `O(P, W).
Proof.
rewrite fdistX1; apply/fdist_ext => b; rewrite fdist_outE fdist_sndE.
by under eq_bigr do rewrite fdist_prodE mulrC.
Qed.

End fdist_out_prop.

Section Pr_fdist_prod.
Variables (A B : finType) (P : {fdist A}) (W : `Ch(A, B)) (n : nat).

Lemma Pr_DMC_rV_prod (Q : 'rV_n * 'rV_n -> bool) :
  Pr (((P `^ n) `X (W ``^ n))) [set x | Q x] =
  Pr ((P `X W) `^ n)           [set x | Q (rV_prod x)].
Proof.
rewrite /Pr [RHS]big_rV_prod /=; apply: eq_big => y.
  by rewrite !inE prod_rVK.
rewrite inE => Qy; rewrite fdist_prodE DMCE fdist_rVE -big_split /= fdist_rVE.
apply: eq_bigr => i /= _.
by rewrite fdist_prodE -snd_tnth_prod_rV -fst_tnth_prod_rV.
Qed.

Lemma Pr_DMC_fst (Q : 'rV_n -> bool) :
  Pr ((P `X W) `^ n) [set x | Q (rV_prod x).1 ] =
  Pr (P `^ n)        [set x | Q x].
Proof.
rewrite {1}/Pr big_rV_prod /= -(pair_big_fst _ _ [pred x | Q x]) //=; last first.
  move=> t /=.
  set X := (X in X _ = _); transitivity (prod_rV t \in X) => //; rewrite inE/=.
  congr (Q _).
  by apply/rowP => a; rewrite !mxE.
transitivity (\sum_(i | Q i) (P `^ n) i * (\sum_(y in 'rV[B]_n) W ``(y | i))).
  apply: eq_bigr => ta Sta; rewrite big_distrr; apply: eq_bigr => tb _ /=.
  rewrite DMCE [in RHS]fdist_rVE -[in RHS]big_split /= fdist_rVE.
  by apply eq_bigr => j _; rewrite fdist_prodE /= -fst_tnth_prod_rV -snd_tnth_prod_rV.
transitivity (\sum_(i | Q i) (P `^ _) i).
  by apply eq_bigr => i _; rewrite (FDist.f1 (W ``(| i))) mulr1.
by rewrite /Pr; apply eq_bigl => t; rewrite !inE.
Qed.

Lemma Pr_DMC_out m (S : {set 'rV_m}) :
  Pr ((P `X W) `^ m) [set x | (rV_prod x).2 \notin S] =
  Pr (`O(P , W) `^ m) (~: S).
Proof.
rewrite {1}/Pr big_rV_prod /= -(pair_big_snd _ _ [pred x | x \notin S]) //=; last first.
  move=> tab /=.
  set X := (X in X _ = _); transitivity (prod_rV tab \in X) => //; rewrite inE/=.
  do 2 f_equal.
  by apply/rowP => a; rewrite !mxE.
rewrite /= /Pr /= exchange_big /=; apply: eq_big => tb; first by rewrite !inE.
move=> Htb.
rewrite fdist_rVE.
under [RHS]eq_bigr do rewrite fdist_outE.
rewrite bigA_distr_bigA /=.
rewrite (reindex_onto (fun p : 'rV[A]_m => [ffun x => p ord0 x])
    (fun y : {ffun 'I_m -> A} => \row_(i < m) y i)) /=; last first.
  by move=> f _; apply/ffunP => /= m0; rewrite ffunE mxE.
apply: eq_big => ta.
  by rewrite inE; apply/esym/eqP/rowP => a; rewrite mxE ffunE.
move=> Hta.
rewrite fdist_rVE /=; apply eq_bigr => l _.
by rewrite fdist_prodE -fst_tnth_prod_rV -snd_tnth_prod_rV ffunE mulrC.
Qed.

End Pr_fdist_prod.

Lemma channel_jcPr (A B : finType) (W : `Ch(A, B)) (P : {fdist A}) a b :
  P a != 0 ->
  W a b = \Pr_(fdistX (P `X W))[ [set b] | [set a] ].
Proof. by move=> Pa0; rewrite jcPr_fdistX_prod//; exact/eqP. Qed.

Notation "`H( P , W )" := (`H (P `X W)) : channel_scope.

Section conditional_entropy_chan.
Variables (A B : finType) (W : `Ch(A, B)) (P : {fdist A}).

Definition cond_entropy_chan := (`H(P, W) - `H P)%channel.
End conditional_entropy_chan.

Notation "`H( W | P )" := (cond_entropy_chan W P) : channel_scope.

Section condentropychan_prop.
Variables (A B : finType) (W : `Ch(A, B)) (P : {fdist A}).

Lemma cond_entropy_chanE : (`H(W | P) = centropy (fdistX (P `X W)))%channel.
Proof.
rewrite /cond_entropy_chan.
have := chain_rule (P `X W); rewrite /joint_entropy => ->.
by rewrite fdist_prod1 addrAC subrr add0r.
Qed.

Lemma cond_entropy_chanE2 : (`H(W | P) = \sum_(a in A) P a * `H (W a))%channel.
Proof.
rewrite cond_entropy_chanE centropyE big_morph_oppr; apply: eq_bigr => a _.
rewrite big_morph_oppr /entropy mulrN -mulNr big_distrr/=; apply: eq_bigr => b _.
rewrite fdistXI fdist_prodE /= mulNr (mulrA (P a)); congr (- _).
have [->|Pa0] := eqVneq (P a) 0; first by rewrite !(mulr0,mul0r).
by rewrite -channel_jcPr.
Qed.

End condentropychan_prop.

Section mutual_info_chan.
Local Open Scope fdist_scope.
Variables A B : finType.

Definition mutual_info_dist (P : {fdist A * B}) := `H P`1 + `H P`2 - `H P.

Definition mutual_info_chan P (W : `Ch(A, B)) :=
  `H P + `H(P `o W) - `H(P , W)%channel.

End mutual_info_chan.

Notation "`I( P , W )" := (mutual_info_chan P W) : channel_scope.

Section mutual_info_chan_prop.
Variables (A B : finType) (W : `Ch(A, B)) (P : {fdist A}).

Lemma mutual_info_chanE : `I(P, W) = mutual_info (fdistX (P `X W)).
Proof.
rewrite /mutual_info_chan mutual_infoE -cond_entropy_chanE.
by rewrite opprB addrCA addrA fdistX_prod_out.
Qed.

End mutual_info_chan_prop.

Definition capacity (A B : finType) (W : `Ch(A, B)) :=
  sup [set `I(P, W) | P in [set: {fdist A}]].
