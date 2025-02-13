(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg perm zmodp.
From mathcomp Require Import matrix.
Require Import f2 ssr_ext ssralg_ext max_subset.
Require Import num_occ hamming ldpc_erasure tanner linearcode.

(**md**************************************************************************)
(* # Combinatorial Result about the Performance of Iterative Decoding         *)
(*                                                                            *)
(* Formalization of Lemma 1.1 from Di, C., Proietti, D., Telatar, I.E.,       *)
(* Richardson, T.J., Urbanke, R.L.: Finite-length analysis of low-density     *)
(* parity-check codes on the binary erasure channel. IEEE Trans. Inf. Theory  *)
(* 48(6), 1570–1579 (2002)                                                    *)
(* Combinatorial Characterization of Iterative Decoder Performance:           *)
(* 'Let E denote the subset of the set of variables nodes which is erased by  *)
(* the channel. Then the set of erasures which remain when the decoder stops  *)
(* is equal to the unique maximal stopping set of E.'                         *)
(* see Section                                                                *)
(* combinatorial_characterization_of_iterative_decoder_performance            *)
(*                                                                            *)
(* For details, see Obata, N.: Formalization of theorems about stopping sets  *)
(* and the decoding performance of LDPC codes. Department of Communications   *)
(* and Computer Engineering, Graduate School of Science and Engineering,      *)
(* Tokyo Institute of Technology, Master’s thesis (2015). (in Japanese).      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.
Import GRing.Theory.
Local Open Scope ring_scope.

Local Open Scope vec_ext_scope.

Section PCM_instance.
Variables (m n : nat) (H : 'M['F_2]_(m, n)).

Local Notation "''F'" := (Fnext H).

Definition PCM_instance (y : 'rV[letter]_n) :=
  \matrix_(i < m, j < n) if i \in 'F j then y ``_ j else Blank.

Lemma PCM_instanceE n0 m0 y : m0 \in 'F n0 -> (PCM_instance y) m0 n0 = y ``_ n0.
Proof. move=> m0n0; by rewrite /mxSum !mxE m0n0. Qed.

Lemma mxProd_mxStar_PCM_instance (y : 'rV[letter]_n) :
  (forall n0, y ``_ n0 != Blank) -> mxProd H y (mxStar H) = PCM_instance y.
Proof.
move=> Hblank.
rewrite /mxProd.
apply/matrixP => i j; rewrite !mxE.
case: ifP => /= ij; last by rewrite ij.
rewrite /colFnextD1.
case/orP : (letter_split (y ``_ j)) => [/existsP[x /eqP Hx]|].
  rewrite Hx.
  apply Prod_colFnext_Bit => //; apply/allP => /= m1.
  by rewrite mem_enum in_setD1 !mxE => /andP[m1i ->].
move: (Hblank j).
case/letterP : (y ``_ j) => // _ _.
apply/Prod_starblank_is_Star/allP => /= y'.
rewrite !inE => /orP[/eqP -> //| /mapP[x]].
by rewrite mxE mem_enum in_setD1 mxE => /andP[xi ->] ->.
Qed.

(*Local Open Scope bec_scope.
Local Open Scope letter_scope.

Lemma PCM_instance_approx (c : 'rV_n) y (cy : c BEC( H ) y) :
  c <=M PCM_instance y.
Proof.
apply/forallP => /= m0; apply/forallP => x; rewrite {x}(ord1 x).
apply/forallP => n0; rewrite !mxE.
case: ifPn => // m0n0; rewrite /blank_to_star.
case: ifPn => // Hyn0.
case: cy => _ /forallP/(_ ord0)/forallP/(_ n0); by rewrite mxE.
Qed.

Variable y : 'rV[letter]_n.
Hypothesis BEC_y : exists c : 'rV['F_2]_n, c BEC( H ) y.

Lemma BEC_PCM_instance : BEC_approx H y (PCM_instance y).
Proof. case: BEC_y => c cy; exists c => //; exact: PCM_instance_approx. Qed.*)

End PCM_instance.

Section stopping_set.
Local Open Scope ring_scope.
Variables (m n : nat) (H : 'M['F_2]_(m, n)).

Local Notation "'`V'" := (Vnext H).
Local Notation "'`F'" := (Fnext H).

Definition stopset (s : {set 'I_n}) := [forall m0, #| s :&: `V m0 | != 1%N].

Lemma stopset0 : stopset set0.
Proof. apply/forallP => /= m0; by rewrite set0I cards0. Qed.

Lemma stopsetU s1 s2 : stopset s1 -> stopset s2 -> stopset (s1 :|: s2).
Proof.
move=> /forallP Hs1 /forallP Hs2; apply/forallP => /= m0.
have : forall p : nat, (p == O) || (2 <= p) -> p != 1%nat by case=> //; case.
apply.
have Hp : forall p, p != 1%nat -> (p == O) || (2 <= p) by case=> //; case.
case/orP: {Hs1}(Hp _ (Hs1 m0)) => [|{Hp}Hs1].
  case/orP: {Hs2 Hp}(Hp _ (Hs2 m0)).
    rewrite 2!cards_eq0 => /eqP Hs1 /eqP Hs2.
    by rewrite setIUl Hs1 Hs2 setU0 cards0 eqxx.
  move=> Hs1; rewrite cards_eq0 => /eqP Hs2; apply/orP; right.
  by rewrite setIUl Hs2 set0U.
apply/orP; right.
by rewrite setIUl cardsU -(addn0 2%N) -addnBA ?leq_add // subset_leq_card // subsetIr.
Qed.

Lemma stopsetE_help (s : {set 'I_n}) m0 n0 :
  n0 \in s ->
  m0 \in `F n0 ->
  #| s :&: `V m0 | != 1%nat ->
  exists n1, (m0 \in `F n1) /\ (n0 != n1) /\ (n1 \in s).
Proof.
move=> n0s m0n0 HwH.
have : s :&: `V m0 :\ n0 != set0.
  move: HwH.
  apply contra.
  move/eqP.
  move/(f_equal (fun x => n0 |: x)).
  rewrite setD1K; last by rewrite inE n0s -FnextE.
  move=> ->.
  by rewrite cardsU1 /= cards0 inE.
case/set0Pn => n1.
rewrite in_setD1 => /andP [] n1n0.
rewrite inE => /andP [] n1s1 m0n1.
exists n1.
rewrite FnextE m0n1; by rewrite eq_sym.
Qed.

Lemma stopsetE (s : {set 'I_n}) :
  stopset s =
  [forall m0, [forall n0, (n0 \in s) && (m0 \in `F n0) ==> ((`V m0 :&: s) :\ n0 != set0)]].
Proof.
apply/idP/idP.
  move=> /forallP Hs; apply/'forall_forallP => m0 n0; apply/implyP => /andP[n0s m0n0].
  case: (stopsetE_help n0s m0n0 (Hs m0)) => /= n1 [m0n1 [n0n1 n1s]].
  apply/set0Pn.
  exists n1; by rewrite 2!inE eq_sym n0n1 in_setI -FnextE m0n1.
move=> H0; apply/forallP => /= m0; apply/negP => abs.
case/boolP : [exists n0, (n0 \in s) && (m0 \in `F n0)]; last first.
  move/negP; apply.
  have : #|[set n0 in s | n0 \in `V m0]| != O by rewrite (eqP abs).
  rewrite cards_eq0.
  case/set0Pn => n1.
  rewrite inE.
  case/andP => H1 H2.
  by apply/existsP; exists n1; rewrite FnextE H1.
case/existsP => /= n0 /andP[n0W m0n0].
move/'forall_forallP : H0 => /(_ m0 n0); rewrite n0W m0n0 implyTb.
case/set0Pn => /= n1.
rewrite 3!inE.
case/and3P => [n1n0 m0n1 n1W].
suff : 1 < #|[set n0 in s | n0 \in `V m0]| by rewrite (eqP abs).
rewrite cardsltn1P.
apply/existsP; exists n0; apply/existsP; exists n1.
by rewrite eq_sym n1n0 andbT inE n0W /= andbC inE n1W /= m0n1 /= -FnextE.
Qed.

End stopping_set.

Section test_stopset.

(*

1 1 0
1 1 0
1 1 0

*)

Definition test_mat : 'M['F_2]_(4, 4) := \matrix_(i < 4, j < 4)
 if j == 0 then 1 else if j == 1 then 1 else 0.

Definition set1 : {set 'I_4} := 1 |: [set 0].

Lemma set1_is_stopset : stopset test_mat set1.
Proof.
rewrite /stopset.
apply/forallP => /= m0.
have : forall a : nat, 1 < a -> a != 1%nat by case=> //; case.
apply.
rewrite cardsltn1P.
case: m0 => -[ ? | ].
  apply/existsP; exists 1; apply/existsP; exists 0.
  by rewrite !inE eqxx /= /test_mat !VnextE !tanner_relE /= !mxE !eqxx.
case => [ ? | ].
  apply/existsP; exists 1; apply/existsP; exists 0.
  by rewrite !inE eqxx /= /test_mat !VnextE !tanner_relE /= !mxE !eqxx.
case => [ ? | ].
  apply/existsP; exists 1; apply/existsP; exists 0.
  by rewrite !inE eqxx /= /test_mat !VnextE !tanner_relE /= !mxE !eqxx.
case => [ ? | [] //].
apply/existsP; exists 1; apply/existsP; exists 0.
by rewrite !inE eqxx /= /test_mat !VnextE !tanner_relE /= !mxE !eqxx.
Qed.

Definition set2 : {set 'I_4} := 1 |: [set 1].

Lemma set2_is_not_stopset : ~~ stopset test_mat set2.
Proof.
rewrite /stopset.
rewrite negb_forall.
apply/existsP; exists 0.
rewrite negbK.
apply/cards1P.
exists 1.
apply/setP => /=  i.
rewrite !inE /test_mat /= !VnextE !tanner_relE /= mxE.
case: i.
case=> [? // | ].
case=> [? // | ].
case=> [? // | ].
by case.
Qed.

End test_stopset.

Section largest_subset_verifying_stopset.
Variables (m n : nat) (H : 'M['F_2]_(m, n)).
Variable E : {set 'I_n}.

Definition largest_stopset := maxset (stopset H) E.

Lemma largest_stopset_is_unique : is_unique largest_stopset
  (fun E' => E' \subset E /\ covered_by (stopset H) E E' /\ stopset H E').
Proof.
apply maxset_is_unique.
exact: stopset0.
exact: stopsetU.
Qed.

End largest_subset_verifying_stopset.

Section stopset_cols_starblank.
Variables (m n : nat) (H : 'M['F_2]_(m, n)).

Local Notation "''F'" := (Fnext H).
Local Notation "''V'" := (Vnext H).

Definition cols_starblank (M : 'M[letter]_(m, n)) (s : {set 'I_n}) :=
  forall n0, n0 \in s ->
  col n0 M = \col_m0 (if m0 \in 'F n0 then Star else Blank).

Variables s : {set 'I_n}.
Hypothesis s_stopset : stopset H s.

Lemma mxSum_Star n0 m0 M :
  cols_starblank M s -> n0 \in s -> m0 \in 'F n0 ->
  mxSum H M m0 n0 = Star.
Proof.
move=> HB n0s m0n0.
rewrite /mxSum mxE m0n0.
set ls := rowVnextD1 _ _ _ _.
rewrite /Sum.
suff -> : has starblank ls by [].
move/forallP : s_stopset => /(_ m0).
case/(stopsetE_help n0s m0n0) => n2 [m0n2 [n0n2 n2s1]].
apply/hasP => /=; exists Star => //.
apply/mapP; exists n2.
  by rewrite mem_enum in_setD1 eq_sym n0n2 -FnextE.
by move/colP: (HB _ n2s1) => /(_ m0); rewrite !mxE m0n2.
Qed.

End stopset_cols_starblank.

Section subset_erasures.
Variables (m n : nat) (H : 'M['F_2]_(m, n)).

Local Notation "''V'" := (Vnext H).
Local Notation "''F'" := (Fnext H).

Definition erasures (y : 'rV[letter]_n) : {set 'I_n} :=
  [set i | y ``_ i == Star].

Variables (s : {set 'I_n}) (y : 'rV[letter]_n).
Hypothesis (sy : s \subset erasures y).

Lemma cols_starblank_PCM_instance_erasures : cols_starblank H (PCM_instance H y) s.
Proof.
move=> n0 n0s; apply/colP => m1; rewrite !mxE; case: ifPn => // m1n0.
by move/subsetP : sy => /(_ _ n0s); rewrite inE => /eqP.
Qed.

Lemma cols_starblank_mxProd : cols_starblank H (mxProd H y (mxStar H)) s.
Proof.
rewrite /cols_starblank => n1 n1s; apply/colP => m1.
rewrite -[in RHS]cols_starblank_PCM_instance_erasures // 5!mxE.
case: ifP => [m1n1|->//].
have -> : y ``_ n1 = Star.
  by move/subsetP : sy => /(_ _ n1s); rewrite inE => /eqP.
rewrite Prod_cons_Star Prod_starblank_is_Star //.
apply/allP => /= l /mapP[/= m0].
by rewrite mem_enum in_setD1 2!mxE => /andP[_ ->] ->.
Qed.

Lemma all_starblank_colFNext_mxSum_stopset (stopset_s : stopset H s) M :
  cols_starblank H M s -> forall n0, n0 \in s ->
  all starblank (colFnext H (y ``_ n0) (col n0 (mxSum H M)) n0).
Proof.
move=> Hcols n0 n0s.
apply/allP => /= l.
rewrite in_cons.
case/orP => [ /eqP -> | ].
  move/subsetP : sy => /(_ _ n0s).
  by rewrite inE => /eqP ->.
case/imageP => m1 m1n0.
by rewrite mxE (mxSum_Star stopset_s Hcols n0s m1n0) => ->.
Qed.

Lemma Prod_colFNext_mxSum_stopset (stopset_s : stopset H s) M :
  cols_starblank H M s -> forall n0, n0 \in s ->
  Prod (colFnext H (y ``_ n0) (col n0 (mxSum H M)) n0) = Star.
Proof. move=> ? ? ?; by apply/Prod_starblank_is_Star/all_starblank_colFNext_mxSum_stopset. Qed.

Lemma all_starblank_colFNextD1_mxSum_stopset (stopset_s : stopset H s) M :
  cols_starblank H M s -> forall n0, n0 \in s ->
  forall m0, all starblank (colFnextD1 H (y ``_ n0) (col n0 (mxSum H M)) n0 m0).
Proof.
move=> Hcols n0 n0s m0.
move/allP: (all_starblank_colFNext_mxSum_stopset stopset_s Hcols n0s) => H0.
apply/allP => l; rewrite inE => /orP[|] H1.
  move: (H0 l); rewrite inE H1 orTb; by apply.
move: (H0 l); rewrite inE; apply; apply/orP; right.
case/mapP : H1 => x Hx Hl.
apply/mapP; exists x => //.
by move: Hx; rewrite !mem_enum in_setD1 => /andP[].
Qed.

Lemma Prod_colFNextD1_mxSum_stopset (stopset_s : stopset H s) m0 n0 M :
  cols_starblank H M s -> n0 \in s ->
  Prod (colFnextD1 H (y ``_ n0) (col n0 (mxSum H M)) n0 m0) = Star.
Proof. move=> ? ?; by apply/Prod_starblank_is_Star/all_starblank_colFNextD1_mxSum_stopset. Qed.

Lemma subset_erasures_Esti : s \subset erasures (Esti H y (mxStar H)).
Proof.
apply/subsetP => /= n0 Hn0; rewrite inE.
move/subsetP : sy => /(_ _ Hn0).
rewrite inE !mxE /colFnext => /eqP ->.
by rewrite Prod_cons_Star Prod_mxStar_col_Star.
Qed.

Local Open Scope bec_scope.

Hypothesis BEC_y : exists c : 'rV['F_2]_n, c BEC( H ) y.

Lemma stopset_subset_erasures_SP_BEC (stopset_s : stopset H s) :
  s \subset erasures (SP_BEC BEC_y).
Proof.
rewrite /SP_BEC.
case: (SP_BEC0_is_iter BEC_y) => x ->.
apply/subsetP => /= n0 n0_in_s.
rewrite /erasures inE /SP_BEC.
move Halpha : (mxStar H) => alpha.
move: (subset_erasures_Esti).
rewrite Halpha.
move/subsetP => /(_ _ n0_in_s) => Hn0.
rewrite !inE /SP_BEC /= in Hn0.
move: cols_starblank_mxProd.
rewrite /iSP_BEC0.
rewrite {}Halpha => Hbeta.
move: x alpha Hbeta Hn0.
elim => [ //= | lmax IHmax ] alpha Hbeta.
rewrite -(addn1 lmax) iterD => EstiStar(*NB: not used?*).
apply IHmax.
  rewrite /= /cols_starblank => n1 Hns1; apply/colP => m1.
  rewrite !mxE.
  case: ifPn => /= m1n1.
    by apply: Prod_colFNextD1_mxSum_stopset.
  rewrite (negbTE m1n1).
  by move: (Hbeta _ Hns1) => /colP/(_ m1); rewrite !mxE (negbTE m1n1).
rewrite mxE.
exact/eqP/Prod_colFNext_mxSum_stopset.
Qed.

End subset_erasures.

Local Open Scope letter_scope.

Section erase.
Variables n : nat.

Definition erase (y : 'rV['F_2]_n) (E : {set 'I_n}) :=
  \row_(n0 < n) if n0 \in E then Star else Bit (y ``_ n0).

Lemma erasures_erase y E : erasures (erase y E) = E.
Proof. apply/setP => /= n0; by rewrite !inE !mxE; case: ifPn. Qed.

Lemma lel_mat_erase (c : 'rV['F_2]_n) E : map_mx Bit c <=m erase c E.
Proof.
apply/'forall_forallP => /= m0 n0; rewrite (ord1 m0){m0}.
rewrite 2!mxE; case: ifPn => // n1E; by rewrite lell.
Qed.

Local Open Scope bec_scope.

Lemma BEC_IO_erase m (H : 'M['F_2]_(m, n)) c E :
  syndrome H c = 0 -> c BEC( H ) (erase c E).
Proof. move=> ?; rewrite /BEC_IO; split => //; exact: lel_mat_erase. Qed.

Variables m : nat.
Variable H : 'M['F_2]_(m, n).

Local Notation "'`F'" := (Fnext H).

Lemma starletter_mxProd_erase (c : 'rV['F_2]_n) (E : {set 'I_n}) (M : 'M_(m, n)) m0 n0 (m0n0 : m0 \in `F n0) :
  all [pred i | starletter ((col n0 M) i ord0) (c ``_ n0)] (enum (`F n0)) ->
  starletter ((mxProd H (erase c E) M) m0 n0) (c ``_ n0).
Proof.
move=> /= IH.
rewrite mxE m0n0 /colFnextD1 mxE.
case: ifP => n0E; last first.
  apply/orP; right.
  apply/eqP/Prod_cons_starletter/allP => i.
  rewrite mem_enum in_setD1 => /andP[_]; rewrite -mem_enum => iFn0.
  by move/allP : IH => /(_ _ iFn0) /=; rewrite mxE.
rewrite Prod_cons_Star.
set l := [seq _ | _ in _].
case/boolP : (Bit c ``_ n0 \in l) => Hl.
  apply/orP; right.
  rewrite (@Prod_starletter _ _ _ _ (c ``_ n0)) //.
    apply/allP => x; rewrite mem_enum in_setD1 => /andP[? x2].
    by move/allP : IH => /(_ x); rewrite mem_enum => /(_ x2) /=; rewrite mxE.
  case/mapP : Hl => m1 Hm1 xm1.
  exists m1 => //.
  by rewrite mem_enum in Hm1.
  by rewrite -xm1.
apply/orP; left.
apply/eqP/Prod_starblank_is_Star/allP => /= y.
case/mapP => /= m1; rewrite mem_enum in_setD1 => /andP[m1m0 Hm1] ->{y}.
move/allP : IH => /(_ m1); rewrite mem_enum => /(_ Hm1) /=.
rewrite mxE; case/orP => [/eqP -> //| /eqP abs].
rewrite abs.
exfalso.
move/negP : Hl; apply.
apply/mapP; exists m1 => //.
by rewrite mem_enum in_setD1 m1m0.
by rewrite mxE.
Qed.

Local Open Scope num_occ_scope.

Lemma Prod_erase_Star (c : 'rV['F_2]_n) (E : {set 'I_n}) m0 n0 (M : 'M[letter]_(m, n)):
  (forall j0, all [pred i | starletter ((col j0 M) i ord0) (c ``_ j0)] (enum (`F j0 :\ m0))) ->
  Prod (colFnextD1 H ((erase c E) ``_ n0) (col n0 M) n0 m0) = Star ->
  (forall i0, i0 \in `F n0 :\ m0 -> M i0 n0 = Star) /\ (erase c E) ``_ n0 = Star.
Proof.
move=> H1 H2.
split.
  move=> m1 m1j0.
  rewrite in_setD1 in m1j0.
  case/andP : m1j0 => m1m0 m1j0.
  move: (H1 n0) => /allP/(_ m1); rewrite mem_enum in_setD1 m1j0 andbT m1m0 => /(_ isT).
  rewrite inE mxE /starletter; case/orP; first by move/eqP.
  move=> abs.
  move/eqP: H2; rewrite Prod_StarE => /forallP/(_ (bool_of_F2 (c ``_ n0))).
  have : N(Bit (~~ bool_of_F2 c ``_ n0) | colFnextD1 H ((erase c E) ``_ n0) (col n0 M) n0 m0) = O.
    apply/eqP.
    rewrite -notin_num_occ_0 inE negb_or /=.
    apply/andP; split.
    rewrite mxE.
    case: ifP => // j0E.
      by case/F2P : (c ``_ n0).
    apply/mapP.
    case=> /= m2 Hm2 H3.
    move: (H1 n0) => /allP/(_ _ Hm2) /=.
    rewrite mxE in H3.
    rewrite mxE -H3 /= => /eqP [].
    by case/F2P : (c ``_ n0).
  move=> ->.
  rewrite -notin_num_occ_0 inE negb_or.
  case/andP => H3 H4.
  case/mapP : H4.
  exists m1.
  by rewrite mem_enum 2!inE m1j0 m1m0.
  by rewrite mxE (eqP abs) bool_of_F2K.
rewrite mxE.
case: ifPn => // n0E.
exfalso.
move: H2; by rewrite mxE (negbTE n0E) Prod_colFnext_Bit.
Qed.

Lemma all_stopsets_in_erasures_in_SP_BEC c E (Hc : syndrome H c = 0) :
  covered_by (stopset H) E (erasures (SP_BEC (ex_intro _ c (BEC_IO_erase E Hc)))).
Proof.
apply/forallP => /= s; apply/implyP.
rewrite inE => /andP[H0 H1].
apply stopset_subset_erasures_SP_BEC => //; by rewrite erasures_erase.
Qed.

End erase.

Section erasures_SP_BEC.
Variables (m n : nat) (H : 'M['F_2]_(m, n)).
Variable c : 'rV['F_2]_n.
Hypothesis Hc : syndrome H c = 0.
Variable E : {set 'I_n}.

Local Notation "''F'" := (Fnext H).
Local Notation "''V'" := (Vnext H).

Lemma all_starletter_iSP_BEC0S : forall l n0, all
  [pred i | starletter ((col n0 (iSP_BEC0 H (erase c E) l.+1)) i ord0) (c ``_ n0)]
  (enum ('F n0)).
Proof.
elim => [j|l IH j].
  apply/allP => /= i ij.
  rewrite /starletter /= !mxE -mem_enum ij /Sum.
  case: ifPn => [_| K ]; first by apply/orP; left.
  apply/orP; right; apply/eqP; congr Bit.
  rewrite (sum_rowVnextD1_nostars Hc) //; last by rewrite -mem_enum.
  move=> n1.
  rewrite in_setD1 => /andP[n1j ijn1].
  rewrite !mxE FnextE ijn1.
  case: ifPn => n1E; last first.
    rewrite Prod_colFnext_Bit //.
    apply/allP => m1.
    by rewrite mem_enum in_setD1 => /andP[xi xFn1] /=; rewrite !mxE xFn1.
  suff : false by [].
  move: K; rewrite -all_predC.
  move/allP => /= /(_ Star); apply.
  apply/mapP.
  exists n1 => //.
    by rewrite mem_enum in_setD1 n1j.
  by rewrite !mxE FnextE ijn1 n1E /colFnextD1 Prod_cons_Star Prod_mxStar_col_Star.
apply/allP => i ij.
rewrite /= mxE /starletter /= mxE -mem_enum ij.
set starset := [set n1 | (n1 \in 'V i :\ j) &&
  ((mxProd H (erase c E) (iSP_BEC0 H (erase c E) l.+1)) i n1 == Star) ].
have [/eqP H1|H1] : (#| starset | = O \/ 1 <= #| starset |)%nat.
  case: (#| starset| ); [tauto | move=> n0; by right].
- apply/orP; right.
  rewrite cards_eq0 in H1.
  have H0 : forall n0, n0 \in 'V i :\ j ->
    (mxProd H (erase c E) (iSP_BEC0 H (erase c E) l.+1)) i n0 = Bit c ``_ n0.
    move=> /= n0.
    rewrite in_setD1.
    case/andP => n0j n0i.
    have n0i' : i \in 'F n0 by rewrite FnextE.
    move: {n0i'}(starletter_mxProd_erase E n0i' (IH n0)).
    case/orP => [abs | /eqP //].
    move/eqP/setP : H1 => /(_ n0).
    by rewrite in_set0 inE abs andbT in_setD1 n0j n0i.
  rewrite (sum_rowVnextD1_Bit Hc) //; first by rewrite -mem_enum.
  move=> *; by rewrite mxE H0.
- move: H1.
  rewrite card_gt0 => /set0Pn[/= n1 Hn1].
  apply/orP; left.
  (* TODO: lemma? *)
  rewrite /Sum ifT //.
  apply/hasP => /=; exists Star => //.
  move: Hn1; rewrite inE => /andP[].
  rewrite in_setD1 => /andP[] n1j n1Vj /eqP <-.
  apply/mapP; exists n1 => //; rewrite ?mxE //.
  by rewrite mem_enum in_setD1 n1j.
Qed.

Lemma all_starletter_iSP_BEC0 : forall l n0, all
  [pred i | starletter ((col n0 (iSP_BEC0 H (erase c E) l)) i ord0) (c ``_ n0)]
  (enum ('F n0)).
Proof.
case => [n0 /=|].
  apply/allP => m1 m1n0 /=.
  move/allP: (all_mxStar H n0) => /(_ _ m1n0) /=.
  by rewrite /= 3!mxE => /eqP ->.
exact: all_starletter_iSP_BEC0S.
Qed.

Lemma not_erasure_SP_BEC n0 : n0 \notin E ->
  (SP_BEC (ex_intro _ c (BEC_IO_erase E Hc))) ``_ n0 = Bit (c ``_ n0).
Proof.
move=> n0E.
rewrite /SP_BEC.
case: (SP_BEC0_is_iter (ex_intro _ c (BEC_IO_erase E Hc))) => l ->.
rewrite /Esti mxE /colFnext mxE (negbTE n0E) Prod_cons_starletter //.
exact: all_starletter_iSP_BEC0.
Qed.

Lemma erasures_SP_BEC_subset :
  erasures (SP_BEC (ex_intro _ c (BEC_IO_erase E Hc))) \subset E.
Proof.
apply/subsetP => /= n0.
rewrite /erasures inE /SP_BEC.
case/boolP: (n0 \in E) => [//|n0E].
by rewrite not_erasure_SP_BEC.
Qed.

End erasures_SP_BEC.

Section starFnext_def.
Variables (m n : nat) (H : 'M['F_2]_(m, n)).

Local Notation "'`F'" := (Fnext H).

Definition starFnext (y : 'rV[letter]_n) M : {set 'I_n} :=
  [set n0 | (y ``_ n0 == Star) && [forall m0, (m0 \in `F n0) ==> (M m0 n0 == Star)]].

End starFnext_def.

Section starFnext_prop.
Variables (m n : nat) (H : 'M['F_2]_(m, n)).

Local Notation "'`V'" := (Vnext H).
Local Notation "'`F'" := (Fnext H).

Variable c : 'rV['F_2]_n.
Variable E : {set 'I_n}.
Let y : 'rV_n := erase c E.

Lemma starFnext_mxStar : starFnext H y (mxStar H) = erasures (Esti H y (mxStar H)).
Proof.
apply/setP => /= n0; rewrite !inE !mxE.
case: ifPn => n0E.
  rewrite /colFnext Prod_cons_Star Prod_mxStar_col_Star eqxx andTb.
  apply/forallP => m0.
  apply/implyP => m0n0; by rewrite mxE m0n0.
rewrite /= /colFnext Prod_cons_starletter //.
apply/allP => m0; by rewrite mem_enum inE 2!mxE => ->.
Qed.

Local Open Scope num_occ_scope.

Lemma starFnext_iter_mxSumProdS (Hc : syndrome H c = 0) l :
  starFnext H y (iSP_BEC0 H y l) = erasures (Esti H y (iSP_BEC0 H y l)).
Proof.
apply/setP => /= n0.
case/boolP : (n0 \in erasures (Esti H y (iSP_BEC0 H y l))) => H0.
  rewrite !inE mxE /Esti /colFnext in H0.
  rewrite inE.
  move: H0.
  rewrite /y mxE.
  case: ifPn => [n0E |n0E H0].
    rewrite Prod_cons_Star => H0.
    rewrite eqxx andTb.
    apply/forallP => /= m0.
    apply/implyP => Hm0.
    set tmp := [seq _ | _ in _] in H0.
    case/boolP : (Bit c ``_ n0 \in tmp) => [abs | Hn0].
      have {abs} : Bit (F2_of_bool (negb (bool_of_F2 (c ``_ n0)))) \in tmp.
        apply: contraLR abs => abs.
        rewrite notin_num_occ_0 -{1}(bool_of_F2K (c ``_ n0)).
        move: H0; rewrite Prod_StarE => /forallP/(_ (bool_of_F2 c ``_ n0))/eqP ->.
        by rewrite -notin_num_occ_0.
      case/mapP => m1 Hm1.
      rewrite mxE => m1n0.
      move: (all_starletter_iSP_BEC0 Hc E l n0) => /allP/(_ _ Hm1) /=.
      rewrite mxE -m1n0.
      by case: (F2P (c ``_ n0)).
    move: (all_starletter_iSP_BEC0 Hc E l n0) => /allP/(_ m0).
    rewrite mem_enum => /(_ Hm0); rewrite inE.
    rewrite /starletter => /orP[|].
      by rewrite mxE.
    rewrite mxE => /eqP abs.
    exfalso.
    move/negP : Hn0; apply.
    apply/mapP; exists m0.
      by rewrite mem_enum.
    by rewrite mxE abs.
  exfalso.
  move: H0; rewrite Prod_StarE => /forallP/(_ (bool_of_F2 (c ``_ n0)))/eqP.
  rewrite num_occ_cons /= bool_of_F2K eqxx /= (_ : _ == _ = false) /=; last by case/F2P : (c ``_ n0).
  rewrite add1n add0n.
  rewrite (_ : N(Bit (F2_of_bool (~~ bool_of_F2 c ``_ n0)) | _) = O) //.
  apply/eqP; rewrite -notin_num_occ_0.
  apply/mapP; case => m1 Hm1 abs.
  move: (all_starletter_iSP_BEC0 Hc E l n0) => /allP/(_ _ Hm1).
  rewrite /= -abs.
  by case/F2P : (c ``_ n0).
rewrite !inE mxE /Esti in H0.
rewrite inE.
apply/negbTE.
rewrite negb_and negb_forall.
case/boolP : (y ``_ n0 != Star) => //=.
rewrite negbK.
move: H0.
rewrite /y mxE.
case: ifP => // n0E.
rewrite /colFnext Prod_cons_Star.
case/Prod_map_not_Star => [b [m1 [H0 H1]]] _.
apply/existsP; exists m1.
rewrite mxE in H1.
by rewrite negb_imply H0 /= H1.
Qed.

Lemma starFnext_iter_mxSumProd (Hc : syndrome H c = 0) l :
  starFnext H y (iSP_BEC0 H y l) = erasures (Esti H y (iSP_BEC0 H y l)).
Proof.
case: l => [|l]; [exact starFnext_mxStar | exact: starFnext_iter_mxSumProdS].
Qed.

End starFnext_prop.

Section starFnext_syndrome_prop.
Variables (m n : nat) (H : 'M['F_2]_(m, n)).

Local Notation "'`V'" := (Vnext H).
Local Notation "'`F'" := (Fnext H).

Variable c : 'rV['F_2]_n.
Hypothesis Hc : syndrome H c = 0.

Variable E : {set 'I_n}.
Let y : 'rV_n := erase c E.

Local Open Scope num_occ_scope.

Lemma starletter_PiSP_BEC0 : forall l n0 m0, m0 \in `F n0 ->
  starletter ((PiSP_BEC0 H y l) m0 n0) (c ``_ n0).
Proof.
case => [ | l] n0 m0 n0m0.
  rewrite /PiSP_BEC0 mxProd_mxStar_PCM_instance; last first.
    move=> n1; rewrite mxE; by case: ifPn.
  rewrite PCM_instanceE // mxE.
  case: ifPn => // _; by rewrite /starletter eqxx orbC.
exact: (starletter_mxProd_erase E n0m0 (all_starletter_iSP_BEC0S Hc _ _ _)).
Qed.

Lemma iSP_BEC0_star_inv l m0 n0 : (iSP_BEC0 H y l.+1) m0 n0 = Star ->
  exists n1, n1 != n0 /\ m0 \in `F n1 /\ (PiSP_BEC0 H y l) m0 n1 = Star.
Proof.
rewrite mxE.
case: ifPn => m0n0.
  rewrite /Sum.
  case: ifP; last by [].
  case/hasP => /= ln1.
  case/mapP => n1 Hn1 Hln1 Kln1 _.
  exists n1 => //.
  move: Hn1.
  rewrite mem_enum in_setD1 => /andP[-> n1m0]; split => //.
  rewrite FnextE n1m0; split => //.
  move: (@starletter_PiSP_BEC0 l n1 m0).
  rewrite FnextE => /(_ n1m0).
  rewrite /starletter => /orP[/eqP //| /eqP abs].
  exfalso.
  move: Kln1.
  by rewrite Hln1 mxE abs.
case: l => [|l].
  by rewrite /= !mxE (negbTE m0n0).
move: (iSP_BEC0_Blank y l m0n0).
by rewrite !mxE (negbTE m0n0) /= => ->.
Qed.

Lemma all_starletter_iSP_BEC0D1 l n0 m0 :
  all [pred i | starletter ((col n0 (iSP_BEC0 H y l)) i ord0) (c ``_ n0)] (enum (`F n0 :\ m0)).
Proof.
apply/allP => /= m1.
rewrite mem_enum in_setD1 => /andP[m1m0 m1Fn0].
by move/allP: (all_starletter_iSP_BEC0 Hc E l n0) => /(_ m1); rewrite mem_enum => /(_ m1Fn0).
Qed.

Lemma PiSP_BEC0_Star_inv l n0 m0 : n0 \in `V m0 -> (PiSP_BEC0 H y l) m0 n0 = Star ->
  y ``_ n0 = Star.
Proof.
case: l n0 m0 => [n0 m0 n0m0|].
  rewrite /PiSP_BEC0 /= mxProd_mxStar_PCM_instance; last first.
    move=> n1; rewrite mxE; by case: ifPn.
  by rewrite PCM_instanceE // FnextE.
move=> l n1 m0 n1m0.
rewrite mxE FnextE n1m0.
apply (@Prod_erase_Star _ _ H c E m0 n1 (iSP_BEC0 H y l.+1)).
move=> j0; exact: (all_starletter_iSP_BEC0D1 l.+1 j0 m0).
Qed.

Lemma PiSP_BEC0_Star_inv_stable l n0 m0 : n0 \in `V m0 -> (PiSP_BEC0 H y l) m0 n0 = Star ->
  iSP_BEC0 H y l = iSP_BEC0 H y l.+1 ->
  forall n1, n1 \in `V m0 -> n1 != n0 -> (iSP_BEC0 H y l) m0 n1 = Star.
Proof.
move=> m0n0 H1 Hstable n1 n1m0 n1n0.
rewrite Hstable mxE FnextE n1m0.
rewrite /Sum ifT //.
apply/hasP => //=; exists Star => //.
apply/mapP; exists n0 => //.
by rewrite mem_enum in_setD1 eq_sym n1n0.
by rewrite mxE.
Qed.

Lemma PiSP_BEC0S_Star_inv l n0 m0 : n0 \in `V m0 -> (PiSP_BEC0 H y l.+1) m0 n0 = Star ->
  forall m1, m1 \in `F n0 :\ m0 -> (iSP_BEC0 H y l.+1) m1 n0 = Star.
Proof.
move=> n0m0 H1 m1 m1n.
rewrite mxE FnextE n0m0 in H1.
have : (forall n1, all
    [pred i | starletter ((col n1 (mxSum H (PiSP_BEC0 H y l))) i ord0) (c ``_ n1)]
    (enum (`F n1 :\ m0))).
  move=> n2; apply/allP => m2 m2n2.
  move: (all_starletter_iSP_BEC0 Hc E l.+1).
  move/(_ n2) => /allP/(_ m2).
  by move: m2n2; rewrite 2!mem_enum in_setD1 => /andP[m2m0 m2Fn2] /(_ m2Fn2).
move/(@Prod_erase_Star _ _ H c E m0 n0 (mxSum H (PiSP_BEC0 H y l))).
move/(_ H1) => [H2 H3].
by apply H2.
Qed.

Lemma fixed_point_stopset_starFnext l :
  iSP_BEC0 H y l.+1 = iSP_BEC0 H y l ->
  stopset H (starFnext H y (iSP_BEC0 H y l.+1)).
Proof.
move=> Hstable.
rewrite stopsetE; apply/'forall_forallP => m0 n0; apply/implyP => /andP[Hn0 Hm0].
move: Hn0.
rewrite /starFnext inE => /andP[yn0 /forallP Hn0].
move: (Hn0 m0) => /implyP /(_ Hm0)/eqP.
case/iSP_BEC0_star_inv => n1 [] n1n0 [] m0n1 bm0n1.
apply/set0Pn; exists n1.
rewrite FnextE in m0n1.
rewrite in_setD1 in_setI n1n0 /= m0n1 /= /starFnext /=.
have [H1 H2] : (forall m1, m1 \in `F n1 :\ m0 -> iSP_BEC0 H y l m1 n1 = Star) /\ y ``_ n1 = Star.
  apply Prod_erase_Star.
  - move=> ?; by apply all_starletter_iSP_BEC0D1.
  - rewrite /colFnextD1 (@PiSP_BEC0_Star_inv l _ _ m0n1) // Prod_cons_Star.
    apply/eqP.
    rewrite Prod_starblank_is_Star //.
    apply/allP => /= x.
    case/mapP => /= m1 Hm1 ->.
    rewrite mxE -Hstable (@PiSP_BEC0S_Star_inv _ _ m0) // /PiSP_BEC0 ?Hstable //; by rewrite mem_enum in Hm1.
rewrite inE H2 eqxx /=.
apply/forallP => m2.
apply/implyP => Hm2.
have [?|m2m0] := eqVneq m2 m0.
  subst m2.
  suff : (iSP_BEC0 H y l) m0 n1 = Star.
    by rewrite -{1}Hstable /= => ->.
  case: l => [|l] in Hstable Hn0 bm0n1 H1 *.
  - by rewrite !mxE Hm2.
  - apply: (@PiSP_BEC0_Star_inv_stable _ n0 m0 _ _ _ n1 m0n1 n1n0) => //.
    + by rewrite FnextE in Hm0.
    + rewrite FnextE in Hm0.
      rewrite /= /mxProd /colFnextD1 mxE FnextE Hm0 (eqP yn0) Prod_cons_Star.
      apply/Prod_starblank_is_Star/allP => y0.
      case/mapP => m1 Hm1 ->.
      apply/starblankP; apply/orP; left.
      suff <- : (iSP_BEC0 H y l.+2) m1 n0 = Star by rewrite mxE Hstable.
      apply/eqP.
      move: Hm1 (Hn0 m1).
      by rewrite mem_enum 2!inE => /andP[m1m0 ->].
move: (H1 m2).
rewrite 2!inE m2m0 Hm2 => /(_ erefl) <-.
by rewrite -{2}Hstable.
Qed.

End starFnext_syndrome_prop.

Section combinatorial_characterization_of_iterative_decoder_performance.
Variables (m n : nat) (H : 'M['F_2]_(m, n)).

Local Notation "'`F'" := (Fnext H).

Variable c : 'rV['F_2]_n.
Hypothesis Hc : syndrome H c = 0.

Local Open Scope bec_scope.

Variable E : {set 'I_n}.
Let y : 'rV[letter]_n := erase c E.
Let BEC_y : exists c : 'rV_n, c BEC( H) y := ex_intro _ c (BEC_IO_erase E Hc).

Lemma stopset_erasures_SP_BEC_stable p :
  SP_BEC0 BEC_y = iSP_BEC0 H y p ->
  stopset H (erasures (SP_BEC BEC_y)).
Proof.
move=> Hstable.
have -> : erasures (SP_BEC BEC_y) = starFnext H y (iSP_BEC0 H y p.+1).
  rewrite (starFnext_iter_mxSumProd E Hc p.+1); congr erasures.
  rewrite /SP_BEC; congr (Esti H y _).
  by rewrite (SP_BEC0_is_a_fixpoint BEC_y) Hstable.
apply: (fixed_point_stopset_starFnext Hc).
by rewrite -Hstable SP_BEC0_is_a_fixpoint Hstable.
Qed.

Lemma stopset_erasures_SP_BEC : stopset H (erasures (SP_BEC BEC_y)).
Proof.
case: (SP_BEC0_is_iter BEC_y) => l Hstable.
exact: (stopset_erasures_SP_BEC_stable Hstable).
Qed.

Lemma largest_stopset_erasures_SP_BEC :
  largest_stopset H E = erasures (SP_BEC BEC_y).
Proof.
rewrite -(@largest_stopset_is_unique _ _ H _ (erasures (SP_BEC BEC_y))) //.
split; first by apply erasures_SP_BEC_subset.
split; first by apply all_stopsets_in_erasures_in_SP_BEC.
exact: stopset_erasures_SP_BEC.
Qed.

End combinatorial_characterization_of_iterative_decoder_performance.
