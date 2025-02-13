(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum fingroup finalg perm.
From mathcomp Require Import zmodp matrix mxalgebra vector ring.
From mathcomp Require Import Rstruct reals.
Require Import ssr_ext ssralg_ext bigop_ext realType_ext f2 linearcode natbin.
Require Import hamming fdist proba channel channel_code decoding.
Require Import binary_symmetric_channel.

(**md**************************************************************************)
(* # Hamming Codes                                                            *)
(*                                                                            *)
(* Main lemmas:                                                               *)
(* - the minimum distance of Hamming codes is 3 (`hamming_min_dist`)          *)
(* - the function hamming_repair implements minimum distance decoding         *)
(*   (`hamming_MD_decoding`)                                                  *)
(* - closed formula for the error rate of Hamming codes (`hamming_error_rat`) *)
(*                                                                            *)
(* ```                                                                        *)
(*       Hamming.PCM == definition of Hamming codes parameterized by the      *)
(*                      height r of the parity check matrix. See              *)
(*                      [F.J. MacWilliams and N.J.A. Sloane, The Theory of    *)
(*                      Error-Correcting Codes, 1977] (p.25). r > 1 because   *)
(*                      with r = 1, the parity check matrix would be the      *)
(*                      identity matrix of dimension 1 x 1, therefore the     *)
(*                      only codeword is 0, and the minimum distance is       *)
(*                      undefined.                                            *)
(*    hamming_repair == repair (decoding w.o. discarding) function for        *)
(*                      Hamming codes                                         *)
(* Module SysHamming == Hamming codes in systematic form                      *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory Order.POrderTheory.
Local Open Scope ring_scope.

Module Hamming.
Section hamming_code_definition.
Variables (m : nat).
Let n := (2 ^ m.-1).-1.*2.+1.

Definition PCM := \matrix_(i < m, j < n) (cV_of_nat m j.+1 i 0).

Definition code : Lcode0.t 'F_2 n := kernel PCM.

End hamming_code_definition.

Section helper_lemmas.
Variable m' : nat.
Let m := m'.+2.

Definition len := (2 ^ m'.+1).-1.*2.+1.
Let n := len.

Lemma len_dim : n = (2 ^ m).-1.
Proof.
rewrite /n /len !expnS -subn1 doubleB -muln2 -subSn; last first.
  by rewrite -muln2 mulnC -mulnA leq_mul2l /= -expnSr expn_gt0.
by rewrite -muln2 mul1n subn2 /= mulnC.
Qed.

Lemma two_len : (2 < n)%N.
Proof. by rewrite len_dim -subn1 ltn_subRL (@leq_exp2l 2 2). Qed.

Lemma dim_len : (m <= n)%N.
Proof. by rewrite len_dim -ltnS prednK ?expn_gt0 // ltn_expl. Qed.

Lemma len_two_m (i : 'I_n) : (i.+1 < 2 ^ m)%N.
Proof.
by rewrite (leq_ltn_trans (ltn_ord i)) // len_dim -ltnS prednK // expn_gt0.
Qed.

End helper_lemmas.

End Hamming.

(** We show that there is no codeword of Hamming weight 1 and 2 but
   since there is one codeword of weight 3, we can conclude that the
   minimum distance of Hamming codes is 3. *)
Section hamming_code_minimun_distance.
Variable m' : nat.
Let m := m'.+2.
Let n := Hamming.len m'.
Let H := Hamming.PCM m.

Lemma no_weight_1_cw x : wH x = 1%N -> syndrome H x <> 0.
Proof.
move=> /wH_1[i [Hi Hi']].
rewrite /syndrome mulmx_sum_col (bigID (pred1 i)) /= big_pred1_eq /=.
rewrite  (eq_bigr (fun=> 0)) /=; last first.
  move=> j; rewrite eq_sym => /eqP/Hi'; rewrite mxE => ->; by rewrite scale0r.
rewrite big_const_seq /= iter_addr0_cV mxE Hi scale1r addr0 col_matrix trmxK.
apply rV_of_nat_neq0 => //.
by rewrite -(addn1 i) addnC -ltn_subRL subn1 -Hamming.len_dim.
Qed.

Lemma no_weight_2_cw x : wH x = 2%N -> syndrome H x <> 0.
Proof.
move=> /wH_2[i [j [Hij [Hi [Hj Hk]]]]].
rewrite /syndrome mulmx_sum_col (bigID (pred1 i)) /= big_pred1_eq /=.
rewrite (bigID (pred1 j)) /= (eq_bigl (pred1 j)) /=; last first.
  move=> a /=; have [aj|aj] := eqVneq a j; last by rewrite andbC.
  rewrite andbC /= aj eq_sym; by apply/eqP.
rewrite big_pred1_eq /= (eq_bigr (fun=> 0)) /=; last first.
  move=> a /andP[X1 X2].
  rewrite mxE Hk ?scale0r //; (apply/eqP; by rewrite eq_sym).
rewrite big_const_seq /= iter_addr0_cV /= 2!mxE Hi Hj 2!scale1r addr0.
rewrite linearD /= 2!col_matrix 2!trmxK.
apply rV_of_natD_neq0 => //.
- by apply/eqP; move/eqP : Hij; apply contra => /eqP[]/eqP.
- by rewrite -(addn1 i) addnC -ltn_subRL subn1 -Hamming.len_dim.
- by rewrite -(addn1 j) addnC -ltn_subRL subn1 -Hamming.len_dim.
Qed.

(** The row-vector 1110...0 (len-1 0's) is a codeword: *)

Lemma weight_3_cw : syndrome H (rV_of_nat n (7 * 2 ^ (n - 3))) = 0.
Proof.
have two_m := Hamming.two_len m'.
apply/rowP => x; rewrite !mxE.
have Hn' : size (bitseq_of_N (bin_of_nat (7 * 2 ^ (n - 3)))) = n.
  apply/eqP.
  rewrite eqn_leq size_bitseq_of_N_ub /=; last 2 first.
    exact/rev7_neq0.
    exact/rev7_ub.
  move: (@size_bitseq_of_N_lb (7 * 2 ^ (n - 3)) n.-1 (rev7_lb two_m)).
  by rewrite -ltnS prednK.
(* the first term of the sum *)
rewrite (bigD1 0) //= !mxE.
set i := nth _ _ 0.
have {i} -> : i = true.
  rewrite /i /bitseq_of_nat /pad_seqL size_rev Hn'.
  by rewrite leqnn subnn cat0s bin_of_nat_rev7 // rev7_bin.
rewrite mulr1.
(* the second term of the sum *)
pose i1 := Ordinal (ltnW two_m); pose i2 := Ordinal two_m.
rewrite (bigD1 i1) // (bigD1 i2) //= !mxE.
set i := nth _ _ i1.
have {i} -> : i = true.
  rewrite /i /bitseq_of_nat /pad_seqL size_rev Hn'.
  by rewrite leqnn subnn cat0s bin_of_nat_rev7 // rev7_bin.
rewrite mulr1.
(* the third term of the sum *)
set i := nth _ _ i2.
have {i} -> : i = true.
  rewrite /i /bitseq_of_nat /pad_seqL size_rev Hn'.
  by rewrite  leqnn subnn cat0s bin_of_nat_rev7 // rev7_bin.
rewrite mulr1 big1 ?addr0 => [|i i_gt2]; last first.
  rewrite /rV_of_nat /bitseq_of_nat.
  rewrite !mxE /= /pad_seqL size_rev Hn' leqnn subnn /=.
  rewrite bin_of_nat_rev7 //= rev7_bin //=.
  set j := nth _ _ i.
  suff -> : j = false by rewrite mulr0.
  rewrite /j.
  clear -i_gt2.
  case: i i_gt2 => -[//|[//|[//|m0]]] /=.
  by rewrite nth_nseq ltn_subRL addnC addn3 => ->.
rewrite /bitseq_of_nat.
destruct x as [x Hx] => /=.
set p0 := pad_seqL _ _ _.
set p1 := pad_seqL _ _ _.
set p2 := pad_seqL _ _ _.
have [X|[X|X]] : (x = m.-1 \/ x = m.-2 \/ x < m.-2)%N.
  move: Hx; rewrite ltnS leq_eqVlt => /orP[/eqP ->|]; first by auto.
  by rewrite ltnS leq_eqVlt => /orP[/eqP|]; auto.
- (* true false true *)
  rewrite X.
  rewrite {1}(_ : m = size p0); last by rewrite /p0 size_pad_seqL.
  rewrite {1}(_ : m = size p1); last by rewrite /p0 size_pad_seqL.
  rewrite {1}(_ : m = size p2); last by rewrite /p0 size_pad_seqL.
  by rewrite 3!nth_last last_cat /= /p1 /p2 /= 2!last_cat /= add0r addrr_char2.
- (* false true true *)
  rewrite X /= /p0 /pad_seqL /=.
  rewrite -cat1s catA nth_cat /= size_nseq /= ltnS leqnn.
  rewrite (_ : false :: _ = nseq m'.+1 false) // nth_nseq ltnS leqnn /=.
  rewrite /p1 /pad_seqL /= nth_cat size_nseq subn2 ltnn subnn /=.
  rewrite /p2 /pad_seqL /= nth_cat size_nseq subn2 ltnn subnn /=.
  by rewrite addrr_char2 // addr0.
- (* false false false *)
  rewrite /p0 /p1 /p2 /= /pad_seqL /=.
  rewrite -cat_cons -[_::_]/(nseq _.+1 _) cats1 nth_rcons size_nseq ltnW // nth_nseq ltnW //.
  rewrite nth_cat size_nseq subn2 X /= nth_nseq X /=.
  by rewrite nth_cat size_nseq X /= nth_nseq X /= !addr0.
Qed.

Lemma hamming_not_trivial : not_trivial (Hamming.code m).
Proof.
exists (rV_of_nat n (7 * 2 ^ (n - 3))).
rewrite memv_ker lfunE /= weight_3_cw eqxx /=.
apply/eqP/rV_of_nat_neq0 => //; [exact: rev7_neq0 | exact: rev7_ub (Hamming.two_len _)].
Qed.

Lemma hamming_min_dist : min_dist hamming_not_trivial = 3%N.
Proof.
move: (min_dist_is_min hamming_not_trivial) => Hforall.
move: (min_dist_achieved hamming_not_trivial) => Hexists.
move: (min_dist_neq0) => H3.
suff : (min_dist hamming_not_trivial <> 1 /\
       min_dist hamming_not_trivial <> 2 /\
       min_dist hamming_not_trivial <= 3)%N.
  move : H3.
  move/(_ _ _ _ hamming_not_trivial).
  destruct (min_dist hamming_not_trivial) as [|p]=> //.
  case: p Hforall Hexists => //; first by intuition.
  case; first by intuition.
  case; first by intuition.
  move=> p _ _ _ [_ [_ ]]; by case: p.
split => [min1 | ].
  case: Hexists => c [] Hc [] c0.
  rewrite min1 => /no_weight_1_cw; apply.
  move: Hc; by rewrite memv_ker lfunE /= => /eqP.
split => [min2 | ].
  case: Hexists => c [] Hc [] c0.
  rewrite min2 => /no_weight_2_cw; apply.
  move: Hc; by rewrite memv_ker lfunE /= => /eqP.
move: (Hforall (rV_of_nat n (7 * 2 ^ (n - 3)))).
have -> : wH (rV_of_nat n (7 * 2 ^ (n - 3))) = 3%N.
  by rewrite -wH_7_rev7 ?Hamming.two_len // wH_7 // Hamming.two_len.
apply; first by rewrite memv_ker lfun_simp /= weight_3_cw.
apply/eqP/rV_of_nat_neq0; [exact: rev7_neq0 | exact: rev7_ub (Hamming.two_len _)].
Qed.

End hamming_code_minimun_distance.

Section hamming_code_minimum_distance_decoding.
Variable m' : nat.
Let m := m'.+2.
Let n := Hamming.len m'.

Definition hamming_err y :=
  let i := nat_of_rV (syndrome (Hamming.PCM m) y) in
  if i is O then 0 else rV_of_nat n (2 ^ (n - i)).

Lemma wH_hamming_err_ub y : (wH (hamming_err y) <= 1)%N.
Proof.
rewrite /hamming_err.
move Hy : (nat_of_rV _) => [|p /=].
  by rewrite (@leq_trans O) // eq_leq // wH0.
by rewrite eq_leq // wH_two_pow // /n subSS sub_ord_proof.
Qed.

Definition alt_hamming_err (y : 'rV_n) : 'rV['F_2]_n :=
  let s : 'rV_m := syndrome (Hamming.PCM m) y in
  let n0 := nat_of_rV s in
  if n0 is O then 0 else (\row_(j < n) if n0.-1 == j then 1 else 0).

Lemma alt_hamming_err_ub y : (wH (alt_hamming_err y) <= 1)%N.
Proof.
rewrite /alt_hamming_err.
destruct (nat_of_rV _); first by rewrite wH0.
clearbody n; clear.
rewrite wH_sum.
have [n0n|n0n] := ltnP n0 n.
  rewrite (bigD1 (Ordinal n0n))//= mxE eqxx (eq_bigr (fun x => O)); last first.
    move=> i Hi; rewrite mxE ifF //.
    apply: contraNF Hi => /eqP Hi; by apply/eqP/val_inj.
  by rewrite big_const iter_addn mul0n.
rewrite (eq_bigr (fun x => O)); first by rewrite big_const iter_addn.
move=> i _; rewrite mxE ifF //=.
by apply/negbTE; rewrite gtn_eqF// (leq_trans (ltn_ord i)).
Qed.

Lemma syndrome_hamming_err y :
  syndrome (Hamming.PCM m) (hamming_err y) = syndrome (Hamming.PCM m) y.
Proof.
rewrite /hamming_err.
move Hs : (syndrome (Hamming.PCM m) y) => s.
have [->|s0] := eqVneq s 0.
  by rewrite nat_of_rV_0 syndrome0.
have [k ks] : exists k : 'I_n, nat_of_rV s = k.+1.
  move: s0; rewrite -nat_of_rV_eq0 -lt0n => s0.
  move: (nat_of_rV_up s) => sup.
  have sn1up : ((nat_of_rV s).-1 < n)%N.
    by rewrite /n Hamming.len_dim -ltnS prednK // prednK // expn_gt0.
  exists (Ordinal sn1up); by rewrite /= prednK.
rewrite ks /= /syndrome.
transitivity
  (col (Ordinal (rev_ord_proof (Ordinal (rev_ord_proof k)))) (Hamming.PCM m))^T.
  rewrite trmx_mul trmxK.
  rewrite (mulmx_rV_of_nat_row (Hamming.PCM m)^T (Ordinal (rev_ord_proof k))).
  by rewrite tr_col.
rewrite col_matrix /= subnS prednK; last by rewrite subnBA // addnC addnK.
by rewrite subnBA // addnC addnK -ks trmxK nat_of_rVK.
Qed.

Definition hamming_repair : repairT _ _ n :=
  [ffun y => Some (y + hamming_err y)].

Lemma C_not_empty : {c0 | c0 \in [set cw in Hamming.code m]}.
Proof. exists 0; by rewrite inE mem0v. Qed.

Lemma hamming_MD_alt : MD_decoding_alt hamming_repair C_not_empty.
Proof.
rewrite /MD_decoding => /= y c.
rewrite /= /hamming_repair ffunE => -[] yc.
have : dH y c = O \/ dH y c = 1%nat.
  rewrite -yc dH_wH.
  move: (wH_hamming_err_ub y).
  rewrite leq_eqVlt ltnS leqn0 => /orP[] /eqP; by auto.
have c_is_cw : c \in [set cw in Hamming.code m].
  by rewrite inE -yc mem_kernel_syndrome0 syndromeD syndrome_hamming_err F2_addmx.
case=> [dH0 | dH1].
  move: (@leq_bigmin _ _ C_not_empty c c_is_cw (dH y)).
  by rewrite dH0 leqn0 => /eqP.
move: (@leq_bigmin _ _ C_not_empty c c_is_cw (dH y)).
rewrite dH1.
set x := arg_min _ _ _.
rewrite -yc /hamming_repair in dH1.
have syndrome_not_0 : syndrome (Hamming.PCM m) y != 0.
  apply/eqP => syndrome_is_0.
  move: dH1.
  by rewrite /hamming_err syndrome_is_0 nat_of_rV_0 addr0 dHE subrr wH0.
move=> dHy.
suff : dH y x != O.
  by move: dHy; rewrite leq_eqVlt => /orP[/eqP //|]; rewrite ltnS leqn0 => ->.
apply/negP => abs.
have : y = x by move: abs; rewrite dHE wH_eq0 subr_eq0 => /eqP.
rewrite /x; case: arg_minnP => [|/=]; first by case: C_not_empty.
move=> y' Hy' _ yy'; rewrite -{}yy' in Hy'.
move/negP : syndrome_not_0; apply.
by rewrite -mem_kernel_syndrome0; rewrite inE in Hy'.
Qed.

Lemma hamming_repair_img : oimg hamming_repair \subset Hamming.code m.
Proof.
apply/subsetP => y /=.
rewrite inE => /existsP[/= x].
rewrite /hamming_repair ffunE => /eqP [<-].
by rewrite mem_kernel_syndrome0 syndromeD syndrome_hamming_err F2_addmx.
Qed.

Lemma hamming_MD_decoding :
  MD_decoding [set cw in Hamming.code m] hamming_repair.
Proof.
apply (@MD_decoding_equiv _ _ _ hamming_repair C_not_empty).
  apply/subsetP => x Hx; rewrite inE.
  by move/subsetP : hamming_repair_img => /(_ _ Hx).
by apply hamming_MD_alt.
Qed.

End hamming_code_minimum_distance_decoding.

Module SysHamming.
Section hamming_code_systematic.
Variable m' : nat.
Let m := m'.+2.
Let n := Hamming.len m'.

Lemma cols_PCM : [set c | (wH c^T >= 1)%N] = [set col i (Hamming.PCM m) | i : 'I_n].
Proof.
apply/setP => i.
rewrite in_set.
case Hi : (0 < wH i^T)%N.
  apply/esym/imsetP.
  have H0 : (nat_of_rV i^T - 1 < n)%N.
    have iup := nat_of_rV_up i^T.
    rewrite /n Hamming.len_dim -subn1 ltn_sub2r //.
    by rewrite -{1}(expn0 2) ltn_exp2l // ltnW.
  exists (Ordinal H0) => //.
  apply/trmx_inj.
  rewrite col_matrix /= trmxK -{1}(nat_of_rVK i^T) subn1 prednK // lt0n nat_of_rV_eq0.
  by apply/eqP => abs; rewrite abs lt0n wH0 eqxx in Hi.
apply/esym/negbTE; move/negbT : Hi; apply contra.
case/imsetP => j Hj ->.
case HwH : (wH (col j (Hamming.PCM m))^T); last by [].
exfalso.
move/eqP: HwH.
rewrite col_matrix wH_eq0 trmxK => /eqP.
by apply rV_of_nat_neq0 => //; apply Hamming.len_two_m.
Qed.

Lemma col_PCM_inj : injective (fun i => col i (Hamming.PCM m)).
Proof.
move=> i j Hij.
rewrite 2!col_matrix in Hij.
have Hi := Hamming.len_two_m i.
have Hj := Hamming.len_two_m j.
rewrite -(Pnat.Nat2Pos.id i.+1) // in Hij Hi.
rewrite -(Pnat.Nat2Pos.id j.+1) // in Hij Hj.
rewrite !BinPos_nat_of_P_nat_of_pos in Hij Hi Hj.
move/trmx_inj in Hij.
have Hpos := nat_of_pos_inj (rV_of_nat_inj Hi Hj Hij).
have Hij' : i.+1 = j.+1 by apply Pnat.Nat2Pos.inj.
apply/eqP.
rewrite -(addn1 i) -(addn1 j) in Hij'.
move/eqP: Hij'.
by rewrite eqn_add2r.
Qed.

Lemma cols_1 : [set c : 'cV['F_2]_m | wH c^T == 1%nat] = [set col i 1 | i : 'I_m].
Proof.
apply/setP => /= i.
rewrite in_set; apply/esym.
case HwH : (wH i^T == _).
  apply/imsetP.
  move: HwH.
  rewrite wH_num_occ num_occ.num_occ_alt => /cards1P[x Hx].
  exists x => //.
  apply/colP => j.
  rewrite !mxE /=.
  move/setP/(_ j): Hx.
  rewrite in_set1 in_set tnth_mktuple mxE => <-.
  by rewrite F2_eq1; case: F2P.
apply/negbTE; move/negbT: HwH; apply contra.
case/imsetP => x Hx ->.
by apply/eqP/wH_col_1.
Qed.

Lemma cols_1_inj : injective (fun i => col i 1 : 'cV['F_2]_m).
Proof.
move=> i j /= /matrixP/(_ j 0).
rewrite !mxE eqxx /=.
by case Hji : (j == i) => // _; apply/esym/eqP.
Qed.

Definition non_unit_cols := [set c : 'cV['F_2]_m | wH c^T > 1]%N.

Definition unit_cols := [set c : 'cV['F_2]_m | wH c^T == 1%nat].

Lemma card_all_cols : #|non_unit_cols :|: unit_cols| = n.
Proof.
rewrite /non_unit_cols /unit_cols.
transitivity #|[set c : 'cV['F_2]_m | wH c^T >= 1]%N|.
  apply eq_card=> c; by rewrite !in_set orbC eq_sym -leq_eqVlt.
by rewrite cols_PCM card_imset ?card_ord //; exact: col_PCM_inj.
Qed.

Lemma card_unit_cols : #|unit_cols| = m.
Proof.
by rewrite /unit_cols cols_1 card_imset; [apply card_ord | apply cols_1_inj].
Qed.

Lemma card_non_unit : #|non_unit_cols| = (n - m)%nat.
Proof.
apply/eqP.
rewrite -(eqn_add2r #|unit_cols|).
apply/eqP.
have: #|non_unit_cols :&: unit_cols| = #|(set0 : {set 'cV['F_2]_m})|.
  apply eq_card=> c.
  rewrite !in_set andbC.
  apply/negP.
  by case/andP => /eqP ->.
rewrite cards0 => Hint.
rewrite -(subn0 (_ + _)%nat) -[X in (_ + _ - X)%nat]Hint.
by rewrite -cardsU card_unit_cols (subnK (Hamming.dim_len m')) card_all_cols.
Qed.

Definition idsA := [seq i <- enum 'I_n | col i (Hamming.PCM m) \in non_unit_cols].

Definition ids1 (i : 'I_m) : {j : 'I_n | col j (Hamming.PCM m) = col i 1}.
have Hin : col i 1 \in image (fun j => col j (Hamming.PCM m)) 'I_n.
  apply/mapP.
  have Hi : col i 1 \in [set col i (Hamming.PCM m) | i : 'I_n].
    rewrite -cols_PCM inE.
    have : col i 1 \in [set c : 'cV['F_2]_m | wH c^T == 1%nat].
      rewrite cols_1.
      by apply/imsetP; exists i.
    by rewrite inE => /eqP ->.
  case/imsetP : Hi => j Hj Hj'.
  by exists j => //; rewrite mem_enum.
by exists (iinv Hin); apply (f_iinv Hin).
Defined.

Definition ord_split (i : 'I_n) : 'I_(n - m + m) :=
  cast_ord (esym (subnK (Hamming.dim_len m'))) i.

Definition perm_ids (i : 'I_n) :=
  match fintype.split (ord_split i) with
  | inl j => nth 0 idsA j
  | inr j => proj1_sig (ids1 j)
  end.

Lemma uniq_idsA : uniq idsA.
Proof. apply filter_uniq, enum_uniq. Qed.

Lemma size_idsA : size idsA = (n - m)%nat.
Proof.
move/card_uniqP: uniq_idsA <-.
rewrite /idsA.
suff: #|[set i : 'I_n | col i (Hamming.PCM m) \in non_unit_cols]| = (n - m)%nat.
  move <-.
  apply eq_card => i.
  by rewrite inE mem_filter mem_enum inE andbT.
rewrite -card_non_unit -(card_imset _ col_PCM_inj).
apply eq_card => c.
have Hcols x : x \in non_unit_cols -> x \in [set col i (Hamming.PCM m) | i : 'I_n].
  rewrite /non_unit_cols -cols_PCM !inE => ?; exact: ltnW.
case Hc : (c \in non_unit_cols).
  apply/imsetP.
  case/imsetP: (Hcols _ Hc) => x Hx Hx'.
  by exists x => //; rewrite inE -Hx'.
apply/negbTE.
move/negbT: Hc; apply contra.
case/imsetP => x Hx Hx'.
by rewrite inE -Hx' in Hx.
Qed.

Lemma idsA_ids1 (i : 'I_(n - m)) (j : 'I_m) : idsA `_ i <> sval (ids1 j).
Proof.
destruct (ids1 j) => /= Hij.
have Hlti : (i < size idsA)%N by rewrite size_idsA.
move: (mem_nth 0 Hlti).
rewrite Hij => Hi.
move: (imset_f (fun i => col i (Hamming.PCM m)) Hi).
rewrite /idsA e.
case/imsetP => y Hy Hy'.
rewrite mem_filter -Hy' in Hy.
move: (f_equal (fun c => wH c^T) Hy').
case Hj : (col j 1 \in non_unit_cols).
  by rewrite /non_unit_cols inE wH_col_1 in Hj.
by rewrite Hj in Hy.
Qed.

Lemma perm_ids_inj : injective perm_ids.
Proof.
rewrite /perm_ids => i j.
move: (splitP (ord_split i)) => [i' Hi'|i' Hi'].
  move: (splitP (ord_split j)) => [j' Hj'|j' Hj'].
    move/eqP.
    rewrite nth_uniq.
    - rewrite -Hi' -Hj' => /eqP ij.
      by apply val_inj.
    - by rewrite size_idsA.
    - by rewrite size_idsA.
    - by apply uniq_idsA.
  move=> Hij.
  by move: (idsA_ids1 Hij).
move: (splitP (ord_split j)) => [j' Hj'|j' Hj'].
  move/eqP.
  rewrite eq_sym.
  by move/eqP/idsA_ids1.
move=> Htmp.
have Hij : i' = j'.
  apply cols_1_inj.
  by rewrite -(proj2_sig (ids1 i')) -(proj2_sig (ids1 j')) Htmp.
rewrite Hij -Hj' /= in Hi'.
exact: val_inj.
Qed.

Definition systematic : 'S_n := perm perm_ids_inj.

Definition PCM := col_perm systematic (Hamming.PCM m).

Definition CSM : 'M_(m, n - m):=
  lsubmx (castmx (erefl m, esym (subnK (Hamming.dim_len m'))) PCM).

Lemma PCM_A_1 : PCM = castmx (erefl, subnK (Hamming.dim_len m')) (row_mx CSM 1).
Proof.
apply/matrixP => i j.
rewrite mxE castmxE /=.
have [Hcond|Hcond] := ltnP j (n - m)%N.
  have -> : cast_ord (esym (subnK (Hamming.dim_len m'))) j =
           lshift m (Ordinal Hcond) by apply val_inj.
  rewrite row_mxEl [in X in _  = X]mxE.
  rewrite castmxE /=.
  rewrite /PCM 2!cast_ord_id.
  rewrite esymK [in X in _ = X]mxE.
  by congr (Hamming.PCM m _ (systematic _)); exact: val_inj.
rewrite [in X in _ = X]mxE.
move: (splitP (cast_ord (esym (subnK (Hamming.dim_len m'))) j)) => [k Hk|k Hk].
  have jk : j = k :> nat by [].
  by rewrite leqNgt jk (ltn_ord k) in Hcond.
rewrite permE /perm_ids.
move Hj : (ord_split j) => l.
move: (splitP l) => [p Hp|p Hlp].
  exfalso.
  move/negP : Hcond; apply.
  suff -> : nat_of_ord j = nat_of_ord p by apply/negP; rewrite -ltnNge ltn_ord.
  by rewrite -Hp -Hj.
destruct ids1 as [x e] => /=.
move/matrixP/(_ i 0) : e.
rewrite !mxE => -> /=.
rewrite cast_ord_id; congr (_ == _)%:R.
apply/val_inj/eqP => /=.
by rewrite -(eqn_add2l (n - m)) -Hlp -Hj Hk.
Qed.

Definition GEN' : 'M_(n - m, n) :=
  castmx (erefl, subnK (Hamming.dim_len m')) (row_mx 1%:M (- CSM)^T).

Program Definition GEN'' : 'M_(n - m, n) :=
  @Syslcode.GEN 'F_2 _ _ _ (castmx (_, erefl (n - m)%nat) CSM).
Next Obligation. exact: leq_subr. Qed.
Next Obligation. by rewrite (subnBA _ (Hamming.dim_len m')) addnC addnK. Qed.

Lemma GEN'E : GEN' = GEN''.
Proof.
rewrite /GEN' /GEN'' /Syslcode.GEN !F2_mx_opp.
Abort.

Lemma PCM_GEN' : PCM *m GEN'^T = 0.
Proof.
rewrite PCM_A_1 /GEN' /= trmx_cast (castmx_cols_mulmx subnK).
by rewrite tr_row_mx trmxK mul_row_col tr_scalar_mx mulmx1 mulmxN mul1mx addrN.
Qed.

(* NB: proof derived from the module SysLCode_m but longish because of casts *)
Lemma PCM_GEN'_alt : PCM *m GEN'^T = 0.
Proof.
have H1 : (n - m <= n)%nat by apply leq_subr.
have H2 : (m = n - (n - m))%nat by rewrite (subnBA _ (Hamming.dim_len m')) addnC addnK.
move: (Syslcode.H_G_T H1 (castmx (H2, erefl (n - m)%nat) CSM)) => /=.
rewrite /Syslcode.PCM /= /Syslcode.GEN /= => H0.
rewrite PCM_A_1 /GEN' !F2_mx_opp.
apply/matrixP => a b.
rewrite [in X in _ = X]mxE.
move/matrixP : H0.
move/(_ (cast_ord H2 a) b).
rewrite [in X in _ = X -> _]mxE => <-.
rewrite !mxE.
apply eq_bigr; case=> i Hi _ /=.
congr (_ * _).
  rewrite !castmxE /= !cast_ord_id !mxE.
  case: splitP.
  - case=> j Hj /= ?; subst j.
    case: splitP.
    + case=> j Hj_ /= ?; subst j.
      rewrite castmxE /= cast_ord_id.
      f_equal; by apply val_inj.
    + case=> k Hk /= ?; subst i.
      exfalso.
      by rewrite ltnNge leq_addr in Hj.
  - case=> k Hk /= ?; subst i.
    case: splitP.
    + case=> j Hj /= ?; subst j.
      exfalso.
      by rewrite ltnNge leq_addr in Hj.
    + case=> j Hj /= /eqP.
      rewrite eqn_add2l => /eqP ?; subst j.
      by rewrite !mxE.
rewrite 2!mxE !castmxE /= F2_mx_opp !cast_ord_id !mxE.
case: splitP.
- case=> j Hj /= ?; subst j.
  case: splitP.
  + case=> j Hj_ /= ?; subst j.
    by rewrite !mxE.
  + case=> k Hk /= ?; subst i.
    exfalso.
    by rewrite ltnNge leq_addr in Hj.
- case=> k Hk /= ?; subst i.
  case: splitP.
  + case=> j Hj /= ?; subst j.
    exfalso.
    by rewrite ltnNge leq_addr in Hj.
  + case=> j Hj /= /eqP.
    rewrite eqn_add2l => /eqP ?; subst j.
    rewrite mxE [in X in _ = X]mxE castmxE /= cast_ord_id.
    congr (CSM _ _); exact: val_inj.
Qed.

Definition mx_discard : 'M['F_2]_(n - m, n) :=
  castmx (erefl, subnK (Hamming.dim_len m')) (row_mx 1%:M 0).
(*   castmx _ (@Syslcode.DIS _ _ _ _).*)

Definition mx_discard' : 'M_(n - m, n) :=
  @Syslcode.DIS 'F_2 _ _ (leq_subr _ _).

Lemma mx_discardE : mx_discard = mx_discard'.
Proof.
apply/matrixP => a b.
rewrite /mx_discard /mx_discard' /Syslcode.DIS !castmxE /= cast_ord_id.
Abort.

Lemma mx_discard_GEN' : mx_discard *m GEN'^T = 1%:M.
Proof.
rewrite /GEN' /mx_discard /= trmx_cast (castmx_cols_mulmx subnK).
rewrite tr_row_mx trmxK mul_row_col.
by rewrite tr_scalar_mx mulmx1 mul0mx addr0.
Qed.

End hamming_code_systematic.

End SysHamming.

(** we derive an encoding and a discard functions from the systematic ones *)
Module Hamming'.
Section from_hamming_code_systematic.
Variable m' : nat.
Let m := m'.+2.
Let n := Hamming.len m'.

Local Notation systematic := (SysHamming.systematic m').

Definition mx_discard :=
  col_perm systematic^-1 (SysHamming.mx_discard m').

Definition GEN := col_perm systematic^-1 (SysHamming.GEN' m').

Lemma PCM_GEN : Hamming.PCM m *m GEN ^T = 0.
Proof. by rewrite /GEN tr_col_perm -mul_col_perm SysHamming.PCM_GEN'. Qed.

Lemma mx_discard_GEN : mx_discard *m GEN ^T = 1%:M.
Proof.
rewrite /GEN /mx_discard tr_col_perm -mul_col_perm.
rewrite -col_permM.
have -> : (systematic * systematic^-1 = 1)%g.
  apply/permP=> i.
  by rewrite permM permK perm1.
by rewrite col_perm1 SysHamming.mx_discard_GEN'.
Qed.

Definition discard : discardT _ n _ := fun y => y *m mx_discard^T.

Definition channel_code := mkCode
  [ffun t => t *m GEN] [ffun x => omap discard (@hamming_repair _ x)].

Lemma encode_inj : injective (enc channel_code).
Proof.
move=> /= i j; rewrite !ffunE => /(congr1 (fun t => mx_discard *m t^T)).
by rewrite !trmx_mul !mulmxA mx_discard_GEN !mul1mx => /trmx_inj.
Qed.

Lemma enc_discard_is_id :
  cancel_on (Hamming.code m) (enc channel_code) discard.
Proof.
move=> y Hy.
rewrite /discard /= ffunE.
rewrite /syndrome in Hy.
have {}Hy : SysHamming.PCM m' *m row_perm systematic y^T = 0.
  rewrite /SysHamming.PCM.
  rewrite mul_col_perm.
  rewrite 2!row_permE.
  rewrite !(mulmxA (perm_mx systematic^-1)).
  rewrite -perm_mxM.
  rewrite mulVg.
  rewrite perm_mx1.
  rewrite mul1mx.
  apply/trmx_inj/eqP.
  by rewrite trmx0 -mem_kernel_syndrome0.
rewrite /discard /GEN.
rewrite /mx_discard /SysHamming.GEN'.
rewrite SysHamming.PCM_A_1 in Hy.
rewrite tr_col_perm.
rewrite mul_row_perm.
rewrite invgK.
rewrite trmx_cast /=.
rewrite tr_row_mx.
rewrite trmx0 trmx1.
rewrite [in X in _ *m _ *m X = _ ]col_permE.
rewrite invgK.
set tmp := castmx _ (col_mx _ _).
rewrite -mulmxA.
rewrite (mulmxA tmp).
rewrite {}/tmp.
rewrite (_ : castmx _ _ *m castmx _ _ =
  castmx (subnK (Hamming.dim_len m'), subnK (Hamming.dim_len m'))
    ((col_mx 1%:M 0) *m (row_mx 1%:M (- SysHamming.CSM m')^T))); last first.
  apply/matrixP => a b.
  rewrite !mxE.
  rewrite castmxE.
  rewrite !mxE.
  apply eq_bigr => /= i _.
  congr (_ * _); by rewrite castmxE /= cast_ord_id.
rewrite mul_col_row.
rewrite 2!mul1mx 2!mul0mx.
rewrite block_mxEv row_mx0.
apply trmx_inj.
rewrite trmx_mul.
rewrite tr_col_perm.
rewrite trmx_mul.
rewrite trmx_cast.
rewrite tr_col_mx.
rewrite trmx0 tr_row_mx.
rewrite trmx1 trmxK /=.
rewrite tr_perm_mx.
rewrite -mulmxA.
have [Y1 [Y2 HY]] : exists (Y1 : 'cV_ _) Y2, (row_perm systematic y^T) =
  castmx (subnK (Hamming.dim_len m'), erefl 1%nat) (col_mx Y1 Y2).
  exists (\matrix_(j < 1, i < n - m) (y j (systematic (widen_ord (leq_subr m n) i))))^T.
  have dim_len_new i (Hi : (i < m)%N) : (n - m + i < n)%N.
    by rewrite -ltn_subRL subnBA ?Hamming.dim_len // addnC addnK.
  exists (\matrix_(j < 1, i < m) (y j (systematic (Ordinal (dim_len_new _ (ltn_ord i))))))^T.
  apply/colP => a /=.
  rewrite !mxE castmxE /=.
  rewrite !mxE.
  case: splitP.
    move=> j aj.
    rewrite !mxE /=.
    congr (y _ (systematic _)); by apply val_inj.
  move=> k ak.
    rewrite mxE /= mxE /=.
    congr (y _ (systematic _)); by apply val_inj.
rewrite HY in Hy.
rewrite (castmx_cols_mulmx subnK) in Hy.
rewrite mul_row_col in Hy.
rewrite mul1mx in Hy.
rewrite HY.
transitivity (perm_mx systematic^-1 *m (castmx (subnK (Hamming.dim_len m'), erefl (n - m)%nat)
                              (col_mx 1%:M (- SysHamming.CSM m')) *m Y1)).
  congr (_ *m _).
  rewrite (castmx_cols_mulmx2 subnK).
  rewrite mul_row_col.
  rewrite mul0mx addr0.
  by rewrite (mulmx_castmx_cols_comm2 subnK).
transitivity (perm_mx systematic^-1 *m (castmx (subnK (Hamming.dim_len m'), erefl 1%nat)
                              (col_mx Y1 ((- SysHamming.CSM m') *m Y1)))).
  congr (_ *m _).
  transitivity (castmx (subnK (Hamming.dim_len m'), erefl 1%nat) (col_mx 1%:M (- SysHamming.CSM m') *m Y1)).
    by rewrite (mulmx_castmx_cols_comm2 subnK).
  congr castmx.
  by rewrite mul_col_mx mul1mx.
have {}HY : y^T = row_perm (systematic^-1) (castmx (subnK (Hamming.dim_len m'), erefl 1%nat) (col_mx Y1 Y2)).
  rewrite -HY.
  rewrite 2!row_permE.
  rewrite mulmxA.
  rewrite -perm_mxM.
  rewrite mulVg.
  rewrite perm_mx1.
  by rewrite mul1mx.
rewrite HY row_permE; congr (_ *m castmx _ (col_mx _ _)).
apply/eqP; by rewrite eq_sym -subr_eq0 mulNmx opprK addrC Hy.
Qed.

Lemma syndrome_enc msg : syndrome (Hamming.PCM m) ((enc channel_code) msg) = 0.
Proof.
apply/eqP => /=; rewrite ffunE /syndrome.
by rewrite trmx_mul trmxK -mulmxA -(trmxK GEN) -trmx_mul PCM_GEN trmx0 mulmx0.
Qed.

Lemma enc_img_is_code : (enc channel_code) @: 'rV_(n - m) \subset Hamming.code m.
Proof.
apply/subsetP => /= t /imsetP[/= x _] ->.
by rewrite mem_kernel_syndrome0 (syndrome_enc x).
Qed.

Lemma hamming_repair_img : (oimg (@hamming_repair m')) \subset Hamming.code m.
Proof.
apply/subsetP => y /=.
rewrite inE => /existsP[/= x].
rewrite /hamming_repair ffunE => /eqP [<-].
by rewrite mem_kernel_syndrome0 syndromeD syndrome_hamming_err F2_addmx.
Qed.

End from_hamming_code_systematic.

End Hamming'.

Section hamming_code_error_distance.
Variable r' : nat.
Let r := r'.+2.
Let n := Hamming.len r'.

Definition lcode : Lcode.t 'F_2 'F_2 n _ :=
  @Lcode.mk _ _ _ _ _
    (Encoder.mk (@Hamming'.encode_inj r') (@Hamming'.enc_img_is_code r'))
    (Decoder.mk (@hamming_repair_img r') (@Hamming'.discard r')) (@Hamming'.enc_discard_is_id r').

Let f := Encoder.enc (Lcode.enc lcode).
Let phi := Decoder.dec (Lcode.dec lcode).
Let repair := Decoder.repair (Lcode.dec lcode).

Lemma hamming_err_enc m : hamming_err (f m) = 0.
Proof. by rewrite /hamming_err Hamming'.syndrome_enc nat_of_rV_0. Qed.

Lemma dec_enc m : phi (f m) = Some m.
Proof.
rewrite /= !ffunE /= /hamming_repair.
move: (hamming_err_enc m); rewrite !ffunE /= => ->.
rewrite addr0 /Hamming'.discard -mulmxA.
suff -> : Hamming'.GEN r' *m (Hamming'.mx_discard r')^T = 1%:M by rewrite mulmx1.
apply trmx_inj; by rewrite trmx1 trmx_mul trmxK Hamming'.mx_discard_GEN.
Qed.

Lemma err_codeword c : c \in lcode -> hamming_err c = 0.
Proof.
rewrite /hamming_err mem_kernel_syndrome0 => /eqP ->; by rewrite nat_of_rV_0.
Qed.

Lemma repair_codeword c : c \in lcode -> repair c = Some c.
Proof.
rewrite /= /repair /= /hamming_repair ffunE => Hc; congr Some.
apply/eqP; by rewrite eq_sym addrC -subr_eq subrr eq_sym err_codeword.
Qed.

Definition decoder : MD_decoding [set cw in lcode] (Decoder.repair (Lcode.dec lcode)).
move=> /= y c Hy c'.
rewrite !(dH_sym _ y).
move: (@hamming_MD_alt r' y c).
move=> ->.
- case: arg_minnP.
    by destruct C_not_empty.
  by move => /= i Hi; apply.
- by rewrite -Hy /Decoder.repair /= /hamming_repair ffunE.
Defined.

Lemma encode_decode c y : c \in lcode ->
  repair y != None -> (dH c y <= 1)%N -> repair y = Some c.
Proof.
move=> Hc Hy cy.
apply: (@mddP _ _ lcode _ decoder (hamming_not_trivial r')) => //.
by apply hamming_repair_img.
by rewrite /mdd_err_cor hamming_min_dist.
Qed.

Lemma repair_failure2 e c : c \in lcode ->
  ~~ (if repair e is Some y0 then y0 != c else true) -> (wH (c + e) <= 1)%N.
Proof.
move=> Hc H.
suff : dH e c = O \/ dH e c = 1%N by rewrite dHE F2_mx_opp addrC; case=> ->.
move: H.
move x : (repair e) => [|] // ex.
rewrite negbK => /eqP xc.
move: ex; rewrite {}xc {x}.
rewrite /repair /Decoder.repair /= /hamming_repair ffunE; case => <-.
move: (wH_hamming_err_ub e).
rewrite dH_wH leq_eqVlt ?ltnS ?leqn0 => /orP[|] /eqP ->; by auto.
Qed.

Lemma repair_failure1 e c : c \in lcode ->
  (if repair e is Some x then x != c else true) -> (1 < wH (c + e))%N.
Proof.
move=> Hc.
move xc : (repair e) => [x ex |]; last first.
  by move=> _; move: xc; rewrite /repair /= /hamming_repair ffunE.
rewrite ltnNge; apply: contra xc.
rewrite leq_eqVlt ltnS leqn0 orbC => /orP[|/eqP cy1].
- rewrite wH_eq0 => /eqP/F2_addmx0 cy.
  by move: ex; rewrite -cy repair_codeword // => -[->].
- move: (ex); rewrite (@encode_decode _ e Hc) ?ex // ?dHE // ?F2_mx_opp ?cy1 //.
  by case => ->.
Qed.

Lemma repair_failure e c : c \in lcode ->
  (if repair e is Some x then x != c else true) = (1 < wH (c + e))%N.
Proof.
move=> Hc.
apply/idP/idP; first by move/repair_failure1; apply.
apply: contraTT; move/repair_failure2; rewrite -leqNgt; by apply.
Qed.

End hamming_code_error_distance.

Local Open Scope channel_code_scope. (* to get e(W,c), echa(W,c) notations *)

Section hamming_code_error_rate.
Let R := Rdefinitions.R.
Variable M : finType.
Hypothesis M_not_0 : (0 < #|M|)%nat.
Variable p : {prob R}.
Let card_F2 : #| 'F_2 | = 2%N. by rewrite card_Fp. Qed.
Let W := BSC.c card_F2 p.

Variable m' : nat.
Let m := m'.+2.
Let n := Hamming.len m'.
Let hamming_channel_code : code _ _ _ n := Hamming'.channel_code m'.

Lemma e_hamming m0 :
  e(W, hamming_channel_code) m0 =
  \sum_(e0 in [set e0 : 'rV['F_2]_n | (2 <= wH e0)%nat])
    (1 - Prob.p p) ^+ (n - wH e0) * (Prob.p p) ^+ wH e0 :> R.
Proof.
rewrite /ErrRateCond /Pr /=.
transitivity (
  \sum_(a | a \in preimC (dec hamming_channel_code) m0)
    let d := dH ((enc hamming_channel_code) m0) a in
    (1 - Prob.p p) ^+ (n - d) * (Prob.p p) ^+ d).
  apply eq_bigr => t Ht.
  rewrite dH_sym.
  rewrite -(DMC_BSC_prop p (enc hamming_channel_code) m0 t).
  by rewrite [X in BSC.c X _](_ : _ = card_F2).
transitivity (
\sum_(a|a \in [set tb | if dec hamming_channel_code tb is Some m1 then
                           m1 != m0 else
                           true])
      (let d := dH ((enc hamming_channel_code) m0) a in
       (1 - Prob.p p) ^+ (n - d) * (Prob.p p) ^+ d)).
  apply eq_bigl => t /=.
  rewrite !inE.
  case_eq (dec hamming_channel_code t) => [m1 Hm1|]; last first.
    by move=> ->.
  by case: ((dec hamming_channel_code) t).
set y0 := (enc hamming_channel_code) m0.
set f : 'rV__ -> 'rV__ := fun y => (y0 + y).
transitivity (
  \sum_(y | f y \in [set e1 | (1 < wH e1)%nat])
    (1 - Prob.p p) ^+ (n - wH (f y)) * (Prob.p p) ^+ wH (f y)).
  apply eq_big.
    move=> y.
    simpl in y, f, m0.
    rewrite !inE.
    have H : y0 \in lcode m'.
      move/subsetP : (Encoder.enc_img (Lcode.enc (lcode m'))); apply.
      apply/imsetP; by exists m0.
    move/(@repair_failure _ y y0) : H => /= H.
    rewrite /f /= ffunE.
    move: H.
    move H : ((@hamming_repair m') y) => [h|//].
    rewrite /= in h H * => <-.
    rewrite /y0 /=.
    apply/idP/idP.
      apply: contra => /eqP ->.
      rewrite ffunE /Hamming'.discard.
      rewrite -mulmxA.
      move: (Hamming'.mx_discard_GEN m').
      move/(congr1 trmx).
      rewrite trmx_mul trmxK => ->.
      by rewrite trmx1 mulmx1.
    rewrite ffunE; apply: contra => /= /eqP <-.
    have : h \in Hamming.code m.
      rewrite mem_kernel_syndrome0.
      move: H.
      rewrite /hamming_repair ffunE => -[<-].
      by rewrite syndromeD syndrome_hamming_err F2_addmx.
    move/(@Lcode.compatible _ _ _ _ (lcode m') h).
    by rewrite /= ffunE => ->.
  move=> /= y; rewrite inE => Hy.
  by rewrite /dH !F2_mx_opp.
apply/esym/reindex.
exists f; move=> /= x _; by rewrite /f addrA F2_addmx add0r.
Qed.

Lemma hamming_error_rate : Prob.p p < 1/2 ->
  echa(W, hamming_channel_code) =
    1 - ((1 - Prob.p p) ^+ n) - n%:R * (Prob.p p) * ((1 - Prob.p p) ^+ (n - 1)).
Proof.
move=> p05.
rewrite /CodeErrRate.
eapply eq_trans.
  apply f_equal.
  apply eq_bigr => i _; exact: e_hamming.
eapply eq_trans.
  apply f_equal.
  by rewrite big_const /= iter_addr addr0.
rewrite /=.
rewrite -[in X in _ * X = _]mulr_natl.
rewrite mulrA /=.
set den := _%:R.
rewrite mulVf; last first.
  rewrite /den card_mx/= mul1n.
  rewrite Num.Theory.pnatr_eq0.
  rewrite expn_eq0.
  by rewrite negb_and card_F2.
rewrite mul1r.
have toleft (A B C D : R) : A + C + D = B -> A = B - C - D.
 move => <-.
 by rewrite addrAC addrK addrK.
apply toleft.
rewrite -addrA.
rewrite -(hamming_01 n (Prob.p p)).
rewrite -big_union //=.
  rewrite (_ : _ :|: _ = [set: 'rV_n]).
    by rewrite binomial_theorem//.
  by apply/setP => /= x; by rewrite !inE leqNgt orNb.
rewrite -setI_eq0.
apply/eqP/setP => /= x; by rewrite !inE leqNgt andNb.
Qed.

End hamming_code_error_rate.
