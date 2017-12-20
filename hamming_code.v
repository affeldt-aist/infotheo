(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg perm zmodp matrix.
From mathcomp Require Import mxalgebra vector.
Require Import ssr_ext ssralg_ext Rssr f2 linearcode natbin hamming Rbigop.
Require Import Rbigop_max proba channel channel_code decoding.
Require Import binary_symmetric_channel.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Hamming Codes *)

(** OUTLINE:
- Module Hamming.
  - Section hamming_code_definition.
  - Section helper_lemmas.
- Section hamming_code_minimun_distance
- section hamming_code_minimum_distance_decoding
- Module SysHamming.
  - Section hamming_code_systematic.
- Module Hamming'.
  - Section hamming_discard_from_hamming_code_systematic
  - Section hamming_code_error_distance
- Section hamming_code_error_rate
*)

(* TODO: move *)
Lemma col_matrix (R : ringType) m n (A : 'I_m -> 'cV[R]_(n.+1)) (i : 'I_m) :
  col i (\matrix_(a < n.+1, b < m) (A b) a ord0) = A i.
Proof. apply/matrixP => a b; by rewrite !mxE (ord1 b). Qed.

Import GRing.Theory.
Local Open Scope ring_scope.

Module Hamming.

(** Definition of Hamming codes parameterized by the height r of the
  parity check matrix. See [F.J. MacWilliams and N.J.A. Sloane, The
  Theory of Error-Correcting Codes, 1977] (p.25). r > 1 because with
  r = 1, the parity check matrix would be the identity matrix of
  dimension 1 x 1, therefore the only codeword is 0, and the minimum
  distance is undefined. *)

Section hamming_code_definition.

Variables (m : nat).
Let n := (expn 2 m.-1).-1.*2.+1. (* TODO: use the ^ notation x*)

Definition PCM := \matrix_(i < m, j < n) (cV_of_nat m j.+1 i 0).

Definition code : Lcode0.t [finFieldType of 'F_2] n := kernel PCM.

End hamming_code_definition.

Section helper_lemmas.

Variable m' : nat.
Let m := m'.+2.

Definition len := (expn 2 m'.+1).-1.*2.+1.
Let n := len.

Lemma len_dim : n = (expn 2 m).-1.
Proof.
rewrite /n /len !expnS -subn1 doubleB -muln2 -subSn; last first.
  by rewrite -muln2 mulnC -mulnA leq_mul2l /= -expnSr expn_gt0.
by rewrite -muln2 mul1n subn2 /= mulnC.
Qed.

Lemma two_len : 2 < n.
Proof. by rewrite len_dim -subn1 ltn_subRL (@leq_exp2l 2 2). Qed.

Lemma m_len : m <= n.
Proof. rewrite len_dim -ltnS prednK; by [rewrite ltn_expl | rewrite expn_gt0]. Qed.

Lemma len_two_m (i : 'I_n) : i.+1 < expn 2 m.
Proof.
apply (leq_ltn_trans (ltn_ord i)); by rewrite len_dim -ltnS prednK // expn_gt0.
Qed.

Lemma dim_len i (Hi : i < m) : n - m + i < n.
Proof.
rewrite -ltn_subRL subnBA; last by apply m_len.
by rewrite addnC addnK.
Qed.

End helper_lemmas.

End Hamming.

Section hamming_code_minimun_distance.

(** We show that there is no codeword of Hamming weight 1 and 2 but
   since there is one codeword of weight 3, we can conclude that the
   minimum distance of Hamming codes is 3. *)

Variable m' : nat.
Let n := Hamming.len m'.
Let H := Hamming.PCM m'.+2.

Lemma no_weight_1_cw x : wH x = 1%nat -> syndrome H x <> 0.
Proof.
move=> /wH_1[i [Hi Hi']].
rewrite /syndrome mulmx_sum_col (bigID (pred1 i)) /= big_pred1_eq /=.
rewrite  (eq_bigr (fun=> 0)) /=; last first.
  move=> j; rewrite eq_sym => /eqP/Hi'; rewrite mxE => ->; by rewrite scale0r.
rewrite big_const_seq /= iter_addr0_cV mxE Hi scale1r addr0 col_matrix trmxK.
apply rV_of_nat_neq0 => //.
by rewrite -(addn1 i) addnC -ltn_subRL subn1 -Hamming.len_dim.
Qed.

Lemma no_weight_2_cw x : wH x = 2 -> syndrome H x <> 0.
Proof.
move=> /wH_2[i [j [Hij [Hi [Hj Hk]]]]].
rewrite /syndrome mulmx_sum_col (bigID (pred1 i)) /= big_pred1_eq /=.
rewrite (bigID (pred1 j)) /= (eq_bigl (pred1 j)) /=; last first.
  move=> a /=; case/boolP : (a == j) => aj; last by rewrite andbC.
  rewrite andbC /= (eqP aj) eq_sym; by apply/eqP.
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

Let two_m := Hamming.two_len m'.
Let m := m'.+2.

Lemma weight_3_cw : syndrome H (rV_of_nat n (7 * expn 2 (n - 3))) = 0.
Proof.
apply/matrixP => y x; rewrite {y}(ord1 y) !mxE.
have Hn' : size (N2bitseq (bin_of_nat (7 * expn 2 (n - 3)))) = n.
  apply/eqP.
  rewrite eqn_leq size_N2bitseq_ub /=; last 2 first.
    by apply rev7_neq0.
    by apply (rev7_ub _ two_m) .
  move: (@size_N2bitseq_lb (7 * expn 2 (n - 3))%nat n.-1 (rev7_lb _ two_m)).
  by rewrite -ltnS prednK.
(* the first term of the sum *)
rewrite (bigD1 0) //= !mxE.
set nth1 := nth _ _ 0.
have -> : nth1 = true.
  rewrite /nth1 /nat2bin /pad_seqL size_rev Hn'.
  by rewrite leqnn subnn cat0s (bin_of_nat_rev7 _ two_m) // (rev7_bin two_m).
rewrite mulr1.
(* the second term of the sum *)
pose i1 := Ordinal (ltnW two_m); pose i2 := Ordinal two_m.
rewrite (bigD1 i1) // (bigD1 i2) //= !mxE.
set nth2 := nth _ _ i1.
have -> : nth2 = true.
  rewrite /nth2 /nat2bin /pad_seqL size_rev Hn'.
  by rewrite leqnn subnn cat0s (bin_of_nat_rev7 _ two_m) // (rev7_bin two_m).
rewrite mulr1.
(* the third term of the sum *)
set nth3 := nth _ _ i2.
have -> : nth3 = true.
  rewrite /nth3 /nat2bin /pad_seqL size_rev Hn'.
  by rewrite  leqnn subnn cat0s (bin_of_nat_rev7 _ two_m) // (rev7_bin two_m).
rewrite mulr1 big1 ?addr0 => [|i i_gt2]; last first.
  rewrite /rV_of_nat /bitseq_F2row /bitseq_to_row /nat2bin.
  rewrite !mxE /= /pad_seqL size_rev Hn' leqnn subnn /=.
  rewrite (bin_of_nat_rev7 _ two_m) /= (rev7_bin two_m) /=.
  set nth4 := nth _ _ i.
  suff -> : nth4 = false by rewrite mulr0.
  rewrite /nth4.
  clear -i_gt2.
  destruct i as [m0] => /=.
  destruct m0 => //.
  destruct m0 => //.
  destruct m0 => //=.
  rewrite nth_nseq.
  by rewrite ltn_subRL addnC addn3 i.
rewrite /nat2bin.
destruct x as [x Hx] => /=.
set p0 := pad_seqL _ _ _.
set p1 := pad_seqL _ _ _.
set p2 := pad_seqL _ _ _.
have [X|[X|X]] : (x = m.-1 \/ x = m.-2 \/ x < m.-2)%nat.
  rewrite ltnS leq_eqVlt in Hx.
  case/orP : Hx.
  - by move/eqP; auto.
  - rewrite ltnS leq_eqVlt => /orP[].
    + by move/eqP; auto.
    + by auto.
- (* true false true *)
  rewrite X.
  rewrite {1}(_ : m = size p0); last by rewrite /p0 size_pad_seqL.
  rewrite {1}(_ : m = size p1); last by rewrite /p0 size_pad_seqL.
  rewrite {1}(_ : m = size p2); last by rewrite /p0 size_pad_seqL.
  by rewrite 3!nth_last /p0 /= last_cat /= /p1 /p2 /= 2!last_cat /= add0r addrr_char2.
- (* false true true *)
  rewrite X /= /p0 /pad_seqL /=.
  rewrite -cat1s catA nth_cat /= size_nseq /= ltnS leqnn.
  rewrite (_ : false :: nseq m' false = nseq m'.+1 false) // nth_nseq ltnS leqnn /=.
  rewrite /p1 /pad_seqL /= nth_cat size_nseq subn2 ltnn subnn /=.
  rewrite /p2 /pad_seqL /= nth_cat size_nseq subn2 ltnn subnn /=.
  by rewrite addrr_char2 // addr0.
(* false false false *)
rewrite /p0 /p1 /p2 /= /pad_seqL /=.
rewrite -!cat_cons -[_::_]/(nseq _.+1 _) nseq_S -catA nth_cat size_nseq X nth_nseq X /=.
rewrite nth_cat size_nseq subn2 X /= nth_nseq X /=.
by rewrite nth_cat size_nseq X /= nth_nseq X /= !addr0.
Qed.

Lemma hamming_not_trivial : not_trivial (Hamming.code m).
Proof.
exists (rV_of_nat n (7 * expn 2 (n - 3))).
rewrite memv_ker lfunE /= weight_3_cw eqxx /=.
apply/eqP/rV_of_nat_neq0 => //.
by apply rev7_neq0.
by apply (rev7_ub _ two_m).
Qed.

Lemma hamming_min_dist : min_dist hamming_not_trivial = 3.
Proof.
move: (min_dist_is_min hamming_not_trivial) => H1.
move: (min_dist_achieved hamming_not_trivial) => H2.
move: (min_dist_neq0) => H3.
suff : min_dist hamming_not_trivial <> 1%nat /\
       min_dist hamming_not_trivial <> 2 /\
       min_dist hamming_not_trivial <= 3.
  move : H3.
  move/(_ _ _ _ hamming_not_trivial).
  destruct (min_dist hamming_not_trivial) as [|n_]=> //.
  destruct n_ as [|n_]; first by intuition.
  destruct n_ as [|n_]; first by intuition.
  destruct n_ as [|n_]; first by intuition.
  move=> _ [] _ [] _.
  by destruct n_.
split => [H0 | ].
  case: H2 => c [] K1 [] K2.
  rewrite H0 => /no_weight_1_cw; apply.
  move: K1; by rewrite memv_ker lfunE /= => /eqP.
split => [H0 | ].
  case: H2 => c [] K1 [] K2.
  rewrite H0 => /no_weight_2_cw; apply.
  move: K1; by rewrite memv_ker lfunE /= => /eqP.
move: (H1 (rV_of_nat n (7 * expn 2 (n - 3)))).
have -> : wH (rV_of_nat n (7 * expn 2 (n - 3))) = 3.
  by rewrite -(wH_7_rev7 two_m) (wH_7 two_m).
apply.
  by rewrite memv_ker lfun_simp /= weight_3_cw.
apply/eqP/rV_of_nat_neq0.
by apply rev7_neq0.
exact (rev7_ub _ two_m).
Qed.

End hamming_code_minimun_distance.

Section hamming_code_minimum_distance_decoding.

Variable m' : nat.
Let m := m'.+2.
Let n := Hamming.len m'.

Definition hamming_err y :=
  let i := nat_of_rV (syndrome (Hamming.PCM m) y) in
  if i is O then 0 else rV_of_nat n (expn 2 (n - i)).

Lemma wH_hamming_err_ub y : wH (hamming_err y) <= 1.
Proof.
rewrite /hamming_err.
move Hp : (nat_of_rV _) => [|p /=].
  rewrite (@leq_trans O) // eq_leq //.
  by apply/eqP; rewrite wH0.
apply eq_leq.
have {Hp}Hp : p < n.
  rewrite -ltnS -Hp /n [in X in _ < X]Hamming.len_dim prednK; last by rewrite expn_gt0.
  by rewrite bitseq2N_up // size_map size_tuple.
by rewrite wH_two_pow // /n subSS sub_ord_proof.
Qed.

Definition alt_hamming_err (y : 'rV['F_2]_n) : 'rV['F_2]_n :=
  let s : 'rV['F_2]_m := syndrome (Hamming.PCM m) y in
  let n0 := nat_of_rV s in
  if n0 is O then 0 else (\row_(j < n) if n0.-1 == j then 1 else 0).

Lemma alt_hamming_err_ub y : wH (alt_hamming_err y) <= 1.
Proof.
rewrite /alt_hamming_err.
destruct (nat_of_rV _).
  suff -> : @wH [fieldType of 'F_2] n 0 = O by done.
  apply/eqP; by rewrite wH0.
clearbody n; clear.
rewrite wH_sum.
case/boolP : (n0 < n) => n0n.
  rewrite (bigD1 (Ordinal n0n)) //= mxE eqxx.
  rewrite (eq_bigr (fun x => 0%nat)); last first.
    move=> i Hi; rewrite mxE.
    case: ifP => // /eqP ?; subst n0.
    suff : False by done.
  move/negP : Hi; apply; by apply/eqP/val_inj.
  by rewrite big_const iter_addn mul0n.
rewrite (eq_bigr (fun x => O)); first by rewrite big_const iter_addn.
move=> i _; rewrite mxE.
case: ifP => // /eqP Hi.
move: (ltn_ord i); by rewrite -Hi /= (negbTE n0n).
Qed.

Lemma syndrome_hamming_err y : syndrome (Hamming.PCM m) (hamming_err y) = syndrome (Hamming.PCM m) y.
Proof.
rewrite /hamming_err.
move Hs : (syndrome (Hamming.PCM m) y) => s.
case/boolP : (s == 0) => [/eqP ->|s0].
  by rewrite nat_of_rV_0 syndrome0.
have [k ks] : exists k : 'I_n, nat_of_rV s = k.+1.
  move: s0; rewrite -nat_of_rV_eq0 -lt0n => s0.
  move: (nat_of_rV_up s) => sup.
  have sn1up : (nat_of_rV s).-1 < n.
    by rewrite /n Hamming.len_dim -ltnS prednK // prednK // expn_gt0.
  exists (Ordinal sn1up); by rewrite /= prednK.
rewrite ks /= /syndrome.
transitivity (col (Ordinal (rev_ord_proof (Ordinal (rev_ord_proof k)))) (Hamming.PCM m))^T.
  rewrite trmx_mul trmxK (mulmx_rV_of_nat_row (Hamming.PCM m)^T (Ordinal (rev_ord_proof k))).
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
rewrite /MD_decoding => /= y y0 Hy0.
move: Hy0.
rewrite /= /hamming_repair ffunE.
case => Hy0.
have : dH y y0 = O \/ dH y y0 = 1%nat.
  rewrite -Hy0 dH_wH.
  move: (wH_hamming_err_ub y).
  rewrite leq_eqVlt.
  case/orP.
  - move/eqP; by right.
  - rewrite ltnS leqn0; move/eqP; by left.
have y0_in_code : y0 \in [set cw in Hamming.code m].
  by rewrite inE -Hy0 mem_kernel_syndrome0 syndromeD syndrome_hamming_err F2_addmx.
case=> [dH0 | dH1].
  rewrite dH0.
  move: (@bigminn_min _ _ C_not_empty y0 y0_in_code (dH y)).
  rewrite dH0 leqn0.
  by move/eqP.
rewrite dH1.
move: (@bigminn_min _ _ C_not_empty y0 y0_in_code (dH y)).
set myarg_min := arg_min _ _ _.
rewrite dH1.
rewrite -Hy0 /hamming_repair in dH1.
have syndrome_not_0 : syndrome (Hamming.PCM m) y != 0.
  rewrite /hamming_err in dH1.
  apply/eqP => syndrome_is_0.
  move: dH1; rewrite syndrome_is_0 nat_of_rV_0 addr0 /dH F2_mx_opp F2_addmx.
  by rewrite wH0.
move=> dHy.
suff : dH y myarg_min != O.
  move: dHy; rewrite leq_eqVlt => /orP[/eqP //|]; by rewrite ltnS leqn0 => ->.
apply/negP => abs.
have : y = myarg_min by move: abs; rewrite dHE wH_eq0 subr_eq0 => /eqP.
rewrite /myarg_min.
case: arg_minP => [|/=]; first by case: C_not_empty.
move=> y' Hy' _ yy'; subst y'.
move/negP : syndrome_not_0; apply.
rewrite -mem_kernel_syndrome0; by rewrite inE in Hy'.
Qed.

Lemma hamming_repair_img : oimg hamming_repair \subset Hamming.code m.
Proof.
apply/subsetP => y /=.
rewrite inE => /existsP[/= x].
rewrite /hamming_repair ffunE.
move/eqP => [<-].
by rewrite mem_kernel_syndrome0 syndromeD syndrome_hamming_err F2_addmx.
Qed.

Lemma hamming_MD_decoding :
  MD_decoding [set cw in Hamming.code m] hamming_repair.
Proof.
apply (@MD_decoding_equiv _ _ _ hamming_repair C_not_empty).
  apply/subsetP => x Hx.
  rewrite inE.
  by move/subsetP : hamming_repair_img => /(_ _ Hx).
by apply hamming_MD_alt.
Qed.

End hamming_code_minimum_distance_decoding.

Module SysHamming.

Section hamming_code_systematic.

Variable m' : nat.
Let m := m'.+2.
Let n := Hamming.len m'.

Lemma cols_hamH : [set c : 'cV['F_2]_m | wH c^T >= 1] = [set col i (Hamming.PCM m) | i : 'I_n].
Proof.
apply/setP => i.
rewrite in_set.
case Hi : (0 < wH i^T).
  apply/esym/imsetP.
  have H0 : nat_of_rV i^T - 1 < n.
    have iup := nat_of_rV_up i^T.
    rewrite /n Hamming.len_dim -subn1.
    apply ltn_sub2r => //.
    by rewrite -{1}(expn0 2) ltn_exp2l // ltnW.
  exists (Ordinal H0) => //.
  apply/trmx_inj.
  rewrite col_matrix /= trmxK -{1}(nat_of_rVK i^T) subn1 prednK // lt0n nat_of_rV_eq0.
  apply/eqP => abs; by rewrite abs lt0n wH0 eqxx in Hi.
apply/esym/negbTE; move/negbT : Hi; apply contra.
case/imsetP => j Hj ->.
case HwH : (wH (col j (Hamming.PCM m))^T); last done.
exfalso.
move/eqP: HwH.
rewrite col_matrix wH_eq0 trmxK => /eqP.
apply rV_of_nat_neq0 => //; by apply Hamming.len_two_m.
Qed.

Lemma col_hamH_inj : injective (fun i => col i (Hamming.PCM m)).
Proof.
move=> i j Hij.
rewrite 2!col_matrix in Hij.
have Hi := Hamming.len_two_m i.
have Hj := Hamming.len_two_m j.
rewrite -(Pnat.Nat2Pos.id i.+1) // in Hij Hi.
rewrite -(Pnat.Nat2Pos.id j.+1) // in Hij Hj.
rewrite !BinPos_nat_of_P_nat_of_pos in Hij Hi Hj.
move/trmx_inj in Hij.
have Hpos := rV_of_nat_inj Hi Hj Hij.
have Hij' : i.+1 = j.+1 by apply Pnat.Nat2Pos.inj.
apply/eqP.
rewrite -(addn1 i) -(addn1 j) in Hij'.
move/eqP: Hij'.
by rewrite eqn_add2r.
Qed.

Lemma cols_1 : [set c : 'cV['F_2]_m | wH c^T == 1%nat] = [set col i 1%:M | i : 'I_m].
Proof.
apply/setP => i.
rewrite in_set.
symmetry.
case HwH : (wH i^T == _).
  apply/imsetP.
  (* TODO: shouldn't do that *)
  rewrite wH_oldE /wH_old num_occ.num_occ_alt in HwH.
  move/cards1P: HwH => [x Hx].
  exists x => //.
  apply/colP => j.
  rewrite !mxE /=.
  move/setP/(_ j): Hx.
  rewrite in_set1 in_set tnth_mktuple mxE => <-.
  rewrite F2_eq1; by case: F2P.
apply/negbTE; move/negbT: HwH; apply contra.
case/imsetP => x Hx ->.
by apply/eqP/wH_col_1.
Qed.

Lemma cols_1_inj : injective (fun i => col i 1%:M : 'cV['F_2]_m).
Proof.
move=> i j /= /matrixP/(_ j 0).
rewrite !mxE eqxx /=.
case Hji : (j == i) => // _. by symmetry; apply/eqP.
Qed.

Definition non_unit_cols := [set c : 'cV['F_2]_m | wH c^T > 1].

Definition unit_cols := [set c : 'cV['F_2]_m | wH c^T == 1%nat].

Lemma card_all_cols : #|non_unit_cols :|: unit_cols| = n.
Proof.
rewrite /non_unit_cols /unit_cols.
transitivity #|[set c : 'cV['F_2]_m | wH c^T >= 1%nat]|.
  apply eq_card=> c.
  by rewrite !in_set orbC eq_sym -leq_eqVlt.
rewrite cols_hamH card_imset ?card_ord //.
by apply col_hamH_inj.
Qed.

Lemma card_unit_cols : #|unit_cols| = m.
Proof. rewrite /unit_cols cols_1 card_imset; by [apply card_ord | apply cols_1_inj]. Qed.

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
by rewrite -cardsU card_unit_cols (subnK (Hamming.m_len m')) card_all_cols.
Qed.

Definition idsA := [seq i <- enum 'I_n | col i (Hamming.PCM m) \in non_unit_cols].

Definition ids1 (i : 'I_m) : {j : 'I_n | col j (Hamming.PCM m) = col i 1%:M}.
have Hin : col i 1%:M \in image (fun j => col j (Hamming.PCM m)) 'I_n.
  apply/mapP.
  have Hi : col i 1%:M \in [set col i (Hamming.PCM m) | i : 'I_n].
    rewrite -cols_hamH inE.
    have : col i 1%:M \in [set c : 'cV['F_2]_m | wH c^T == 1%nat].
      rewrite cols_1.
      apply/imsetP; by exists i.
    by rewrite inE => /eqP ->.
  case/imsetP : Hi => j Hj Hj'.
  exists j => //.
  by rewrite mem_enum.
exists (iinv Hin).
by apply (f_iinv Hin).
Defined.

Definition ord_split (i : 'I_n) : 'I_(n - m + m) := cast_ord (esym (subnK (Hamming.m_len m'))) i.

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
  rewrite inE mem_filter mem_enum.
  have -> : i \in 'I_n by [].
  by rewrite andbT.
rewrite -card_non_unit.
rewrite -(card_imset _ col_hamH_inj).
apply eq_card.
move=> c.
have Hcols x: x \in non_unit_cols -> x \in [set col i (Hamming.PCM m) | i : 'I_n].
  rewrite /non_unit_cols -cols_hamH !inE => Hx.
  by apply ltnW.
case Hc: (c \in non_unit_cols).
  apply/imsetP.
  case/imsetP: (Hcols _ Hc) => x Hx Hx'.
  exists x => //.
  by rewrite inE -Hx'.
apply/negbTE.
move/negbT: Hc.
apply contra.
case/imsetP => x Hx Hx'.
by rewrite inE -Hx' in Hx.
Qed.

Lemma idsA_ids1 (i' : 'I_(n - m)) (j' : 'I_m) : idsA`_i' <> sval (ids1 j').
Proof.
destruct (ids1 j') => /= Hij.
have Hlti' : i' < size idsA by rewrite size_idsA.
move: (mem_nth 0 Hlti').
rewrite Hij => Hi.
move: (mem_imset (fun i => col i (Hamming.PCM m)) Hi).
rewrite /idsA e.
case/imsetP => y Hy Hy'.
rewrite mem_filter -Hy' in Hy.
move: (f_equal (fun c => wH c^T) Hy').
case Hj : (col j' 1%:M \in non_unit_cols).
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
by apply val_inj.
Qed.

Definition systematic : 'S_n := perm perm_ids_inj.

(*Definition PCM_cast : 'M['F_2]_(m, (n - m) + m) :=
  castmx (erefl, esym (subnK (Ham.m_len m'))) PCM.*)

Definition PCM := col_perm systematic (Hamming.PCM m).

Definition CSM :=
  lsubmx (castmx (erefl m, esym (subnK (Hamming.m_len m'))) PCM).

Lemma PCM_A_1 : PCM = castmx (erefl, subnK (Hamming.m_len m')) (row_mx CSM 1%:M).
Proof.
apply/matrixP => i j.
rewrite mxE castmxE /=.
case/boolP : (j < n - m) => Hcond.
  have -> : cast_ord (esym (subnK (Hamming.m_len m'))) j = lshift m (Ordinal Hcond) by apply val_inj.
  rewrite row_mxEl [in X in _  = X]mxE.
  rewrite castmxE /=.
  rewrite /PCM 2!cast_ord_id.
  rewrite esymK [in X in _ = X]mxE.
  congr (Hamming.PCM m _ (systematic _)); by apply val_inj.
rewrite [in X in _ = X]mxE.
move: (splitP (cast_ord (esym (subnK (Hamming.m_len m'))) j)) => [j' Hj'|j' Hj'].
  have Hj: (j:nat) = j' by [].
  by rewrite Hj (ltn_ord j') in Hcond.
rewrite permE /perm_ids.
move Hj : (ord_split j) => j_.
move: (splitP j_) => [k Hk|k Hk].
  suff : False by done.
  move/negP : Hcond; apply.
  suff -> : nat_of_ord j = nat_of_ord k by apply ltn_ord.
  by rewrite -Hk -Hj.
destruct ids1 as [x e] => /=.
move/matrixP/(_ i 0) : e.
rewrite !mxE => -> /=.
rewrite cast_ord_id.
congr (_ == _)%:R.
apply/val_inj => /=.
apply/eqP.
by rewrite -(eqn_add2l (n - m)) -Hk -Hj Hj'.
Qed.

(*Definition G_cast := castmx (erefl, subnK (Ham.m_len m')) (row_mx 1%:M (- A)^T).
Check G_cast.
*)

Definition GEN' :=
  castmx (erefl, subnK (Hamming.m_len m')) (row_mx 1%:M (- CSM)^T).

Lemma PCM_GEN' : PCM *m GEN'^T = 0.
Proof.
rewrite PCM_A_1 /GEN' /= trmx_cast (castmx_cols_mulmx subnK).
rewrite tr_row_mx trmxK mul_row_col tr_scalar_mx mulmx1.
by rewrite mulmxN mul1mx addrN.
Qed.

(* NB: proof derived from the module SysLCode_m but longish because of casts *)
Lemma PCM_GEN'_alt : PCM *m GEN'^T = 0.
Proof.
have H1 : (n - m <= n)%nat by apply leq_subr.
have H2 : (m = n - (n - m))%nat by rewrite (subnBA _ (Hamming.m_len m')) addnC addnK.
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
      suff : False by done.
      by rewrite ltnNge leq_addr in Hj.
  - case=> k Hk /= ?; subst i.
    case: splitP.
    + case=> j Hj /= ?; subst j.
      suff : False by done.
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
    suff : False by done.
    by rewrite ltnNge leq_addr in Hj.
- case=> k Hk /= ?; subst i.
  case: splitP.
  + case=> j Hj /= ?; subst j.
    suff : False by done.
    by rewrite ltnNge leq_addr in Hj.
  + case=> j Hj /= /eqP.
    rewrite eqn_add2l => /eqP ?; subst j.
    rewrite mxE [in X in _ = X]mxE castmxE /= cast_ord_id.
    f_equal; by apply val_inj.
Qed.

Definition mx_discard : 'M['F_2]_(n - m, n) :=
  castmx (erefl, subnK (Hamming.m_len m')) (row_mx 1%:M 0).

Lemma mx_discard_GEN' : mx_discard *m GEN'^T = 1%:M.
Proof.
rewrite /GEN' /mx_discard /= trmx_cast (castmx_cols_mulmx subnK).
rewrite tr_row_mx trmxK mul_row_col.
by rewrite tr_scalar_mx mulmx1 mul0mx addr0.
Qed.

End hamming_code_systematic.

End SysHamming.

Module Hamming'.

Section hamming_discard_from_hamming_code_systematic.

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
move=> /= i j Hij.
rewrite !ffunE in Hij.
move: (congr1 (fun t => mx_discard *m t^T) Hij).
rewrite !trmx_mul !mulmxA mx_discard_GEN !mul1mx => Hij'.
move: (congr1 (fun t => t ^T) Hij').
by rewrite !trmxK.
Qed.

Lemma enc_discard_is_id :
  cancel_on (Hamming.code m) (enc channel_code) discard.
Proof.
move=> y Hy.
rewrite /discard /= ffunE.
rewrite /syndrome in Hy.
have {Hy}Hy : SysHamming.PCM m' *m row_perm systematic y^T = 0.
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
  castmx (subnK (Hamming.m_len m'), subnK (Hamming.m_len m')) ((col_mx 1%:M 0) *m (row_mx 1%:M (- SysHamming.CSM m')^T))); last first.
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
  castmx (subnK (Hamming.m_len m'), erefl 1%nat) (col_mx Y1 Y2).
  exists (\matrix_(j < 1, i < n - m) (y j (systematic (widen_ord (leq_subr m n) i))))^T.
  exists (\matrix_(j < 1, i < m) (y j (systematic (Ordinal (Hamming.dim_len (ltn_ord i))))))^T.
  apply/matrixP => a b /=.
  rewrite (ord1 b) {b} /=.
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
transitivity (perm_mx systematic^-1 *m (castmx (subnK (Hamming.m_len m'), erefl (n - m)%nat)
                              (col_mx 1%:M (- SysHamming.CSM m')) *m Y1)).
  congr (_ *m _).
  rewrite (castmx_cols_mulmx2 subnK).
  rewrite mul_row_col.
  rewrite mul0mx addr0.
  by rewrite (mulmx_castmx_cols_comm2 subnK).
transitivity (perm_mx systematic^-1 *m (castmx (subnK (Hamming.m_len m'), erefl 1%nat)
                              (col_mx Y1 ((- SysHamming.CSM m') *m Y1)))).
  congr (_ *m _).
  transitivity (castmx (subnK (Hamming.m_len m'), erefl 1%nat) (col_mx 1%:M (- SysHamming.CSM m') *m Y1)).
    by rewrite (mulmx_castmx_cols_comm2 subnK).
  congr castmx.
  by rewrite mul_col_mx mul1mx.
have {HY}HY : y^T = row_perm (systematic^-1) (castmx (subnK (Hamming.m_len m'), erefl 1%nat) (col_mx Y1 Y2)).
  rewrite -HY.
  rewrite 2!row_permE.
  rewrite mulmxA.
  rewrite -perm_mxM.
  rewrite mulVg.
  rewrite perm_mx1.
  by rewrite mul1mx.
rewrite HY row_permE.
congr (_ *m castmx _ (col_mx _ _)).
apply F2_addmx0.
by rewrite F2_mx_opp.
Qed.

Lemma syndrome_enc msg : syndrome (Hamming.PCM m) ((enc channel_code) msg) = 0.
Proof.
apply/eqP.
by rewrite /= ffunE /syndrome trmx_mul trmxK -mulmxA -(trmxK GEN) -trmx_mul PCM_GEN trmx0 mulmx0.
Qed.

Lemma enc_img_is_code : (enc channel_code) @: [finType of 'rV_(n - m)] \subset Hamming.code m.
Proof.
apply/subsetP => /= t /imsetP[/= x _].
rewrite ffunE => ->.
rewrite mem_kernel_syndrome0.
move: (syndrome_enc x) => /=.
by rewrite ffunE => ->.
Qed.

Lemma hamming_repair_img : (oimg (@hamming_repair m')) \subset Hamming.code m.
Proof.
apply/subsetP => y /=.
rewrite inE => /existsP[/= x].
rewrite /hamming_repair ffunE.
move/eqP => [<-].
by rewrite mem_kernel_syndrome0 syndromeD syndrome_hamming_err F2_addmx.
Qed.

End hamming_discard_from_hamming_code_systematic.

Section hamming_code_error_distance.

Variable r' : nat.
Let r := r'.+2.
Let n := Hamming.len r'.

Definition lcode := @Lcode.mk _ _ _ _ _ (Encoder.mk (@encode_inj r') (@enc_img_is_code r')) (Decoder.mk (@hamming_repair_img r') (@discard r')) (@enc_discard_is_id r').

Let f := Encoder.enc (Lcode.enc lcode).
Let phi := Decoder.dec (Lcode.dec lcode).
Let repair := Decoder.repair (Lcode.dec lcode).

Lemma hamming_err_enc msg : hamming_err (f msg) = 0.
Proof. by rewrite /hamming_err syndrome_enc nat_of_rV_0. Qed.

Lemma dec_enc m0 : phi (f m0) = Some m0.
Proof.
rewrite /= !ffunE /= /hamming_repair.
move: (hamming_err_enc m0).
rewrite !ffunE /= => ->.
rewrite addr0; congr Some.
rewrite /discard.
rewrite -mulmxA.
suff -> : GEN r' *m (mx_discard r')^T = 1%:M by rewrite mulmx1.
apply trmx_inj.
by rewrite trmx1 trmx_mul trmxK mx_discard_GEN.
Qed.

(* TODO: move *)
Lemma repair_err_is_0 m0 : m0 \in lcode -> hamming_err m0 = 0.
Proof.
rewrite /hamming_err mem_kernel_syndrome0 => /eqP ->; by rewrite nat_of_rV_0.
Qed.

Lemma repair_enc m0 : m0 \in lcode -> repair m0 = Some m0.
Proof.
rewrite /= /repair /= /hamming_repair ffunE => Hm0; congr Some.
apply/eqP.
by rewrite eq_sym addrC -subr_eq subrr eq_sym repair_err_is_0.
Qed.

Definition decoder : MD_decoding [set cw in lcode] (Decoder.repair (Lcode.dec lcode)).
move=> v /= y Hy y'.
rewrite !(dH_sym _ v).
move: (@hamming_MD_alt r' v y).
move=> ->.
- case: arg_minP.
    by destruct C_not_empty.
  move => i Hi Htmp y'C. 
  by apply Htmp => //.
- move: Hy.
  case=> <-.
  by rewrite /Decoder.repair /= /hamming_repair ffunE.
Defined.

Lemma encode_decode x y : x \in lcode ->
  repair y != None ->
  dH x y <= 1 ->
  repair y = Some x.
Proof.
move=> Hx Hy He.
apply: (@mddP _ _ lcode _ decoder (hamming_not_trivial r')) => //.
by apply hamming_repair_img.
by rewrite /mdd_err_cor hamming_min_dist.
Qed.

Lemma error_distance1 y m0 : m0 \in lcode ->
  match repair y with
       | Some y0 => y0 != m0
       | None => true
       end = false ->
  wH (m0 + y) <= 1.
Proof.
move=> Hm0.
move/negbT => Hlhs.
suff : dH y m0 = O \/ dH y m0 = 1%nat.
  rewrite /dH F2_mx_opp addrC.
  by case=> ->.
move: Hlhs.
move y0 : (repair y) => [|] // yy0.
rewrite negbK => /eqP y0m0; subst y0.
move: yy0.
rewrite /repair /Decoder.repair /=.
move Htmp : (@hamming_repair r' y) => [tmp|] // [] <-.
rewrite /hamming_repair ffunE in Htmp.
case: (Htmp) => <-.
rewrite dH_wH.
move: (wH_hamming_err_ub y).
rewrite leq_eqVlt.
case/orP; [move/eqP; by right | rewrite ltnS leqn0; move/eqP; by left].
Qed.

Lemma error_distance2 y m0 : m0 \in lcode ->
   match repair y with
         | Some y0 => y0 != m0
         | None => true
         end ->
   1 < wH (m0 + y).
Proof.
move=> Hm0.
move Hdecr : (repair y) => [y0 Hy0|y0].
  rewrite ltnNge.
  move: Hdecr; apply: contra => Hdecr.
  have {Hdecr} : wH (m0 + y) = O \/ wH (m0 + y) = 1%nat.
    destruct (wH _ ); auto.
    destruct n0; auto.
    by destruct n0.
  case.
    move/eqP; rewrite wH_eq0.
    move/eqP/F2_addmx0 => H1.
    rewrite -H1 in Hy0.
    move: Hy0.
    by rewrite repair_enc // => -[->].
  move=> HwH1.
  move: (Hy0).
  rewrite (@encode_decode m0 y).
      by case => ->.
    done.
  by rewrite Hy0.
  by rewrite /dH F2_mx_opp HwH1.
move: y0.
rewrite /repair /Decoder.repair /=.
move Hcor : (@hamming_repair _ _) => [//|] _.
move: Hcor.
by rewrite /hamming_repair ffunE.
Qed.

Lemma error_distance y m0 : m0 \in lcode ->
  match repair y with
  | Some m1 => m1 != m0
  | None => true
  end =
  (1 < wH (m0 + y)).
Proof.
move=> Hm0.
move Hlhs : (match _ with Some _ => _ | _ => _ end) => [].
  by apply/esym/error_distance2.
apply/esym/negbTE.
rewrite -leqNgt.
by apply error_distance1.
Qed.

End hamming_code_error_distance.

End Hamming'.

Local Open Scope channel_code_scope. (* to get e(W,c), echa(W,c) notations *)

Require Import Reals Reals_ext.

Section hamming_code_error_rate.

Variable M : finType.
Hypothesis M_not_0 : 0 < #|M|.
Variable p : R.
Hypothesis p_01 : (0 <= p <= 1)%R.
Let card_F2 : #| 'F_2 | = 2. by rewrite card_Fp. Qed.
Let W := BSC.c card_F2 p_01.

Variable m' : nat.
Let m := m'.+2.
Let n := Hamming.len m'.
Let ham_lcode := Hamming'.lcode m'.
Let hamming_channel_code : code _ _ _ n := Hamming'.channel_code m'.

Local Open Scope R_scope.

Lemma e_hamming m0 :
  e(W, hamming_channel_code) m0 =
  \rsum_(e0 in [set e0 : 'rV['F_2]_n | (2 <= wH e0)%nat])
    (1 - p) ^ (n - wH e0) * p ^ wH e0.
Proof.
rewrite /ErrRateCond /Pr /=.
transitivity (
  \rsum_(a | a \in preimC (dec hamming_channel_code) m0)
    let d := dH ((enc hamming_channel_code) m0) a in
    (1 - p) ^ (n - d) * p ^ d).
  apply eq_bigr => t Ht.
  rewrite dH_sym.
  rewrite -(DMC_BSC_prop p_01 (enc hamming_channel_code) m0 t).
  set tmp := eq_ind_r _ _ _.
  by rewrite (_ : tmp = card_F2); last by apply eq_irrelevance.
transitivity (
\rsum_(a|a \in [set tb | if dec hamming_channel_code tb is Some m1 then
                           m1 != m0 else
                           true])
      (let d :=
         dH ((enc hamming_channel_code) m0) a in
       (1 - p) ^ (n - d) * p ^ d)).
  apply eq_bigl => t /=.
  rewrite !inE.
  case_eq (dec hamming_channel_code t) => [m1 Hm1|]; last first.
    move=> ->.
    by apply/eqP.
  case: ((dec hamming_channel_code) t).
    move=> m3.
    by case: (m3 != m0).
  by apply/eqP.
set y0 := (enc hamming_channel_code) m0.
Local Close Scope R_scope.
set f := fun y => y0 + y.
Local Open Scope R_scope.
transitivity (
  \rsum_(y | f y \in [set e1 | (1 < wH e1)%nat])
    (1 - p) ^ (n - wH (f y)) * p ^ wH (f y)).
  apply eq_big.
    move=> y.
    simpl in y, f, m0.
    rewrite !inE.
    have H : y0 \in Hamming'.lcode m'.
      move/subsetP : (Encoder.enc_img (Lcode.enc ham_lcode)); apply.
      apply/imsetP.
      by exists m0.
    move: (@Hamming'.error_distance _ y y0 H) => {H}H.
    rewrite /= in H.
    rewrite /f /dec /= ffunE.
    move: H.
    move H : ((@hamming_repair m') y) => [h|//].
    rewrite /= in h H * => <-.
    rewrite /y0.
    rewrite /=.
    apply/idP/idP.
      apply: contra.
      move/eqP => ->.
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
    move/(@Lcode.compatible _ _ _ _ (Hamming'.lcode m') h).
    by rewrite /= ffunE => ->.
  move=> /= y Hy.
  rewrite inE in Hy.
  by rewrite /dH !F2_mx_opp.
apply/esym/reindex.
exists f.
  move=> /= x _.
  by rewrite /f addrA F2_addmx add0r.
move=> /= x _.
by rewrite /f addrA F2_addmx add0r.
Qed.

Lemma hamming_error_rate : p < 1/2 ->
  echa(W, hamming_channel_code) =
    1 - ((1 - p) ^ n) - INR n * p * ((1 - p) ^ (n - 1)).
Proof.
move => p05.
rewrite /CodeErrRate.
eapply eq_trans.
  apply f_equal.
  apply eq_bigr => i _.
  by apply e_hamming.
eapply eq_trans.
  apply f_equal.
  by rewrite big_const /= iter_Rplus.
rewrite mulRA /=.
set tmp := INR _.
have -> : 1 /tmp * tmp = 1.
  field.
  rewrite /tmp card_matrix /= -INR_pow_expn.
  apply/pow_nonzero/not_0_INR.
  by rewrite card_F2.
rewrite mul1R.
have toleft A B C D : A + C + D = B -> A = B - C - D.
  move => <-; ring.
apply toleft.
rewrite -addRA -(hamming_01 n p) //.
rewrite -(@rsum_union _ _ _ [set: 'rV_n]).
    by apply binomial_theorem.
  rewrite -setI_eq0.
  apply/eqP/setP => /= x.
  by rewrite !inE leqNgt andNb.
apply/setP => /= x.
by rewrite !inE leqNgt orNb.
Qed.

End hamming_code_error_rate.
