(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
Require Import Reals.
From mathcomp Require Import all_ssreflect fingroup zmodp ssralg ssrnum finalg.
From mathcomp Require Import perm matrix poly mxalgebra mxpoly.
From mathcomp Require Import Rstruct reals.
Require Import ssr_ext ssralg_ext f2 num_occ natbin bigop_ext.

(**md**************************************************************************)
(* # Hamming weight and Hamming distance                                      *)
(*                                                                            *)
(* This file provides lemmas about Hamming weight and distance, e.g.:         *)
(* - triangular inequality (`dH_tri_ine`)                                     *)
(* - weight of $0...011$ (`wH_3`)                                             *)
(* - weight of $0..0111$ (`wH_7`)                                             *)
(* - the number of points (`'rV['F_q]_n`) at distance `k` from `x` is         *)
(*   `'C(n, k) * q.-1 ^ k` (`card_sphere q n k x`)                            *)
(* - binomial theorem (`binomial_theorem`)                                    *)
(*                                                                            *)
(* ```                                                                        *)
(*    HammingBitstring.wH a == Hamming weight of a : bitseq                   *)
(*  HammingBitstring.dH a b := wH (a (+) b)                                   *)
(*                     wH v == Hamming weight of v : 'rV[F]_n (F : ringType)  *)
(*                   dH u v := wH (u - v)                                     *)
(*                wH_supp x := [set i | x ``_ i != 0]                         *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

Local Open Scope vec_ext_scope.
Local Open Scope num_occ_scope.

Module HammingBitstring.

Definition wH (a : bitseq) := N(true | a).

Definition dH (a b : bitseq) : nat := wH (addb_seq a b).

Lemma dH_count : forall n a b, size a = n ->
  dH (nseq n b) a = count (pred1 (negb b)) a.
Proof.
elim; first by case.
move=> n IH [|[|] ta] [] // [H]; rewrite /dH in IH;
  by rewrite /= /dH /= IH.
Qed.

Lemma dH_sym n a b : size a = n -> size b = n -> dH a b = dH b a.
Proof. move=> Ha Hb. by rewrite /dH (@addb_seq_com n). Qed.

Lemma dH_tri_ine : forall n a b c, size a = n -> size b = n -> size c = n ->
  (dH a b <= dH a c + dH c b)%N.
Proof.
elim => [ [] // [] // [] // |].
move=> n IH [|ha ta] // [|hb tb] // [|hc tc] // [Ha] [Hb] [Hc].
rewrite /dH /= -/(dH ta tb) -/(dH ta tc) -/(dH tc tb).
move: {IH}(IH _ _ _ Ha Hb Hc) => IH.
apply: leq_trans.
- apply leq_add; [by apply leqnn | by apply IH].
- rewrite !eqb_id !addnA -(addnC (hc (+) hb)) addnA -2!addnA; apply leq_add.
  + rewrite addnC; by apply addb_tri_ine.
  + by apply leqnn.
Qed.

Lemma dH_cat a b c d : size a = size c -> size b = size d ->
  dH (a ++ b) (c ++ d) = (dH a c + dH b d)%nat.
Proof.
move=> ac bd; by rewrite /dH /wH addb_seq_cat // /num_occ count_cat.
Qed.

End HammingBitstring.

Section hamming_weight_distance.
Variables (F : ringType) (n : nat).
Implicit Types u v : 'rV[F]_n.

Definition wH v := count (fun x => x != 0) (tuple_of_row v).

Lemma max_wH u : (wH u <= n)%N.
Proof. by rewrite /wH (leq_trans (count_size _ _)) // size_tuple. Qed.

Lemma max_wH' u : (wH u < n.+1)%N. Proof. by rewrite ltnS max_wH. Qed.

Lemma wH_sum v : wH v = (\sum_(n0 < n) (v ``_ n0 != 0%R))%nat.
Proof.
rewrite /wH 1!count_map -sum1_count /= big_mkcond /=.
apply congr_big => //=; by rewrite /index_enum -enumT.
Qed.

Lemma wH_const_mx b : b != 0 -> wH (const_mx b) = n.
Proof.
move=> b0; rewrite wH_sum (eq_bigr (fun=> 1%nat)) //.
- by rewrite sum_nat_const card_ord muln1.
- by move=> ? _; rewrite mxE b0.
Qed.

Lemma wH0 : wH 0 = O.
Proof. by rewrite wH_sum big1 // => i _; rewrite mxE eqxx. Qed.

Lemma wH0_inv v : wH v = O -> v = 0.
Proof.
move=> v0.
apply/rowP => i; rewrite mxE; apply/eqP; move/eqP : v0; apply: contraTT => vi0.
rewrite -lt0n -has_count; apply/hasP.
exists (v ``_ i) => //; apply/mapP; exists i => //.
by rewrite val_ord_tuple mem_enum.
Qed.

Lemma wH_eq0 u : (wH u == O) = (u == 0).
Proof. apply/idP/idP => [/eqP/wH0_inv/eqP //|/eqP ->]; by rewrite wH0. Qed.

Lemma wH_opp v : wH (- v) = wH v.
Proof.
rewrite {1}/wH [X in tval X](_ : _ = [tuple of map (fun x => - x) (tuple_of_row v)]); last first.
  apply: eq_from_tnth => i /=; by rewrite !tnth_map mxE.
rewrite count_map; apply eq_count => i /=; by rewrite oppr_eq0.
Qed.

Lemma wH_rVpoly u : wH u = count (fun i : 'I_n => (rVpoly u)`_i != 0) (enum 'I_n).
Proof.
rewrite /wH count_map; apply eq_in_count => /= i _.
rewrite coef_poly insubT // => ni.
rewrite ltn_ord; congr (u _ _ != _); by apply val_inj.
Qed.

Lemma wH_poly_rV (p : {poly F}) : (wH (poly_rV p) <= size p)%N.
Proof.
rewrite /wH /=.
case/boolP : (size p < n)%N => pn; last first.
  rewrite -leqNgt in pn; rewrite (leq_trans _ pn) //.
  by rewrite (leq_trans (count_size _ _)) // size_map size_enum_ord.
have -> : [seq (poly_rV p) ``_ i | i <- enum 'I_n] =
  [seq (poly_rV p) ``_ i | i <- enum ('I_(size p))] ++ nseq (n - size p) 0.
  apply (@eq_from_nth _ 0) => [|i].
    by rewrite size_cat 2!size_map !size_enum_ord size_nseq subnKC // ltnW.
  rewrite size_map size_enum_ord => ni.
  rewrite (nth_map (Ordinal ni)) ?size_enum_ord // mxE nth_enum_ord //.
  rewrite nth_cat size_map size_enum_ord; case: ifPn => [pi|].
    by rewrite (nth_map (Ordinal pi)) ?size_enum_ord // mxE nth_enum_ord.
  rewrite -leqNgt => /leq_sizeP/(_ _ (leqnn i)) ->; by rewrite nth_nseq ltn_sub2r.
rewrite count_cat [X in (_ + X <= _)%N](_ : count _ _ = O) ?addn0; last first.
  rewrite (@eq_in_count _ _ pred0) ?count_pred0 //.
  move=> i; case/nseqP => -> /= _; by rewrite eqxx.
by rewrite count_map (leq_trans (count_size _ _)) // size_enum_ord.
Qed.

Lemma wH_card_supp u : wH u = #|supp u|%N.
Proof.
rewrite wH_sum /supp -sum1dep_card [in RHS]big_mkcond; by apply/eq_bigr.
Qed.

Definition dH u v := wH (u - v).

Lemma dHE u v : dH u v = wH (u - v). Proof. by []. Qed.

Lemma dH_wH u v : dH u (u + v) = wH v.
Proof. by rewrite /dH opprD addrA subrr add0r wH_opp. Qed.

Lemma dH0x x : dH 0 x = wH x.
Proof. by rewrite /dH add0r wH_opp. Qed.

Lemma max_dH u v : (dH u v <= n)%N.
Proof. rewrite /dH. apply max_wH. Qed.

Lemma dH_sym u v : dH u v = dH v u.
Proof. by rewrite {1}/dH -wH_opp opprB. Qed.

End hamming_weight_distance.

Lemma wH_count n (x : 'rV['F_2]_n) : wH x = count (fun i => x ``_ i == 1) (enum 'I_n).
Proof.
rewrite wH_sum -sum1_count [in RHS]big_mkcond /=.
apply congr_big => //.
- by rewrite /index_enum -enumT.
- move=> i _; case: ifPn => [/eqP -> //|].
  by rewrite -F2_eq0 => /eqP ->.
Qed.

Lemma sum_wH_row (F : ringType) n m (H : 'M[F]_(m, n)) :
  (\sum_(m0 : 'I_m) wH (row m0 H) = \sum_(n0 : 'I_n) wH (col n0 H)^T)%nat.
Proof.
transitivity (\sum_(m0 < m) \sum_(n0 < n) (H m0 n0 != 0%R))%nat.
  apply eq_bigr => m0 _.
  rewrite wH_sum; apply eq_bigr => n0 _; by rewrite mxE.
rewrite exchange_big /=.
apply eq_bigr => n0 _.
rewrite wH_sum; apply eq_bigr => m0 _; by rewrite 2!mxE.
Qed.

Section wH_num_occ_bitstring.

Lemma wH_col_1 n (i : 'I_n) : @wH 'F_2 _ (col i 1%:M)^T = 1%N.
Proof.
rewrite wH_sum (bigD1 i) //= !mxE eqxx /= add1n (eq_bigr (fun=> O)).
by rewrite big_const iter_addn mul0n.
move=> j ji; by rewrite !mxE (negbTE ji).
Qed.

Lemma wH_num_occ n (v : 'rV['F_2]_n) : wH v = N(1 | tuple_of_row v).
Proof. rewrite /wH /num_occ; apply eq_count => i; by rewrite -F2_eq1. Qed.

Lemma wH_bitstring n (x : 'rV_n) :
  wH x = HammingBitstring.wH (tval (rowF2_tuplebool x)).
Proof.
rewrite wH_num_occ /HammingBitstring.wH /= /num_occ /= [in RHS]count_map.
apply eq_in_count => /= b Hb; by rewrite -(F2_eq1 b) eqb_id.
Qed.

End wH_num_occ_bitstring.

Lemma wH_castmx n (F : ringType) (x : 'rV[F]_n) n' (H : (1 = 1)%N * (n = n')) :
  wH (castmx H x) = wH x.
Proof.
case: H => H1 H2; subst n'.
rewrite /wH !count_map /=; apply eq_in_count => /= i _.
by rewrite castmxE /= !cast_ord_id.
Qed.

Lemma wH_row_mx n (F : ringType) r (rn : (r <= n)%N) :
  wH (row_mx (const_mx 1) 0 : 'rV[F]_(r + (n - r))) = r.
Proof.
rewrite wH_sum (bigID (fun x : 'I__ => (x < r)%N)) /=.
rewrite (eq_bigr (fun=> 1%N)); last first.
  move=> i ir.
  rewrite (_ : i = lshift _ (Ordinal ir)) ?row_mxEl ?mxE ?oner_neq0 //.
  by apply val_inj.
rewrite sum1dep_card (eq_bigr (fun=> O)) //; last first.
  move=> i ir.
  have ir' : (i - r < n - r)%N.
    destruct r as [|r].
      rewrite subn0.
      move/leq_trans: (ltn_ord i); apply; by rewrite subn0 add0n.
    rewrite subnS prednK // ?subn_gt0 // ?ltnNge; last by rewrite ltnS in ir.
    rewrite /= [in X in (_ <= X)%N]subnS.
    destruct n as [|n'] => //.
    rewrite subSKn leq_sub2r //.
    move: (ltn_ord i); by rewrite [in X in (_ < X)%N -> _]subnKC ltnS.
  rewrite (_ : i = rshift _ (Ordinal ir')); last first.
    apply val_inj => /=; by rewrite [in RHS]subnKC // leqNgt.
  by rewrite row_mxEr mxE eqxx.
rewrite big_const iter_addn_0 mul0n addn0 -sum1dep_card.
by rewrite big_ord_narrow ?subnKC // sum1_card card_ord.
Qed.

Section hamming_triangular_inequality.
Variables (F : ringType).

Lemma tri_ine (a b c : F) : ((a != b) <= (c != b) + (a != c))%nat.
Proof.
case/boolP : (a == b) => ab //=.
by case/boolP : (c == b) => cb //=; rewrite add0n (eqP cb) {cb} ab.
Qed.

Lemma dH_tri_ine n (c a b : 'rV[F]_n) : (@dH _ n a b <= dH a c + dH c b)%nat.
Proof.
elim: n a b c => [a b c|n IH a b c].
  by rewrite (empty_rV a) (empty_rV b) (empty_rV c) /dH subrr wH0.
rewrite /dH /wH.
have H : forall v w : 'rV[F]_n.+1,
  count (fun x : F => x != 0) (tuple_of_row (v - w)) =
  addn (v ``_ 0 - w ``_ 0 != 0) (count (fun x => x != 0) (behead (tuple_of_row (v - w)))).
  move=> v w.
  rewrite (tuple_eta (tuple_of_row (v - w))) /=.
  by rewrite /tuple_of_row /thead tnth_map !mxE tnth_ord_tuple.
rewrite !H {H} addnCA !addnA -addnA leq_add //; last first.
move: {IH}(IH (row_of_tuple [tuple of (behead (tuple_of_row a))])
              (row_of_tuple [tuple of (behead (tuple_of_row b))])
              (row_of_tuple [tuple of (behead (tuple_of_row c))])).
  rewrite /dH /wH.
  set lhs := (X in (X <= _)%nat -> _).
  set rhs := (X in (_ <= X)%nat -> _) => IH.
  apply (@leq_trans lhs).
    rewrite /lhs.
    apply eq_leq.
    rewrite (_ : tuple_of_row _ = [tuple of (behead (tuple_of_row (a - b)))]) //.
    apply eq_from_tnth.
    rewrite /tuple_of_row => i; by rewrite !(tnth_behead,tnth_mktuple,mxE).
  apply (leq_trans IH) => {IH}.
  rewrite leq_add //.
  - apply eq_leq.
    rewrite (_ : tuple_of_row _ = [tuple of (behead (tuple_of_row (a - c)))]) //.
    apply eq_from_tnth.
    rewrite /tuple_of_row => i; by rewrite !(tnth_behead,tnth_mktuple,mxE).
  - apply eq_leq.
    rewrite (_ : tuple_of_row _ = [tuple of (behead (tuple_of_row (c - b)))]) //.
    apply eq_from_tnth.
    rewrite /tuple_of_row => i; by rewrite !(tnth_behead,tnth_mktuple,mxE).
by rewrite !subr_eq0 tri_ine.
Qed.

End hamming_triangular_inequality.

Section wH_supp.
Variables (n : nat) (F : ringType).
Implicit Types x : 'rV[F]_n.

Definition wH_supp x := [set i | x ``_ i != 0].

Lemma card_wH_supp x : #| wH_supp x |%N = wH x.
Proof.
rewrite cardE size_filter /wH count_map -enumT /=.
apply eq_in_count => /= i _; by rewrite inE.
Qed.

Lemma mem_wH_supp x (i : 'I_n) : (x ``_ i != 0) = (i \in wH_supp x).
Proof. by rewrite inE. Qed.

End wH_supp.

Lemma nth_wH_supp k n (F : ringType) (y : 'rV[F]_n.+1) : (k <= n.+1)%N ->
  wH y = k -> forall j : nat, (j < k)%N -> y ``_ (nth ord0 (enum (wH_supp y)) j) != 0.
Proof.
move=> kn yD j jk; rewrite mem_wH_supp -mem_enum; apply/mem_nth.
by rewrite -cardE card_wH_supp yD.
Qed.

Section wH_permutation.
Variable n : nat.

Lemma wH_perm_mx (s : 'S_n) (z : 'rV['F_2]_n) : wH (z *m perm_mx s) = wH z.
Proof.
rewrite !wH_num_occ.
suff -> : tuple_of_row (z *m perm_mx s) = perm_tuple (s^-1)%g (tuple_of_row z).
  by apply: num_occ_perm.
apply eq_from_tnth => n0; by rewrite 3!tnth_mktuple vec_perm_mx !mxE.
Qed.

End wH_permutation.

Section wH_binomial.

Local Open Scope ring_scope.
Lemma wH_m_card n k : #|[set a in 'rV['F_2]_n | wH a == k]| = 'C(n, k).
Proof.
rewrite -[in X in _ = X](card_ord n) -card_draws -2!sum1dep_card.
pose h' := fun s : {set 'I_n} => \row_(j < n) (if j \in s then (1 : 'F_2) else 0).
have h'h (i : 'rV_n) : h' [set i0 | i ``_ i0 == 1] == i.
  apply/eqP/rowP => y; rewrite !mxE inE.
  case: ifP => [/eqP -> // | /negbT]; by rewrite -F2_eq0 => /eqP.
rewrite (reindex_onto (fun x : 'rV_n => [set i | x ``_ i == 1]) h') /=.
- apply eq_bigl => i.
  rewrite wH_num_occ num_occ_alt h'h andbC /=; congr (_ == _).
  apply eq_card => t; by rewrite !inE tnth_mktuple.
- move=> s Hs.
  apply/setP => /= i; rewrite !inE /h' mxE; by case: ifP.
Qed.
Local Close Scope ring_scope.

Lemma card_Fp_F2 p n' k : let n := n'.+1 in prime p -> k <= n ->
  (\sum_(x : 'rV['F_p]_n | [forall j : 'I_n, (k <= j) ==> (x ``_ j == 0%R)] &&
    [forall j : 'I_n, (j < k) ==> (x ``_ j != 0%R)]) 1) =
  (\sum_(x : 'rV['F_2]_n | [forall j : 'I_n, (k <= j) ==> (x ``_ j == 0%R)] &&
    [forall j : 'I_n, (j < k) ==> (x ``_ j != 0%R)]) 1 * p.-1 ^ k).
Proof.
move=> n primep kn.
destruct p as [|p'] => //; destruct p' as [|p'] => //.
set p := p'.+2.
transitivity (\sum_(x : 'rV['F_p]_k | [forall j : 'I_k, x ``_ j != 0%R]) 1).
  rewrite !sum1dep_card.
  pose f : 'rV_n -> 'rV_k :=
    fun x => (@ulsubmx 'F_p 1 0 k (n - k) (castmx (erefl, esym (subnKC kn)) x)).
  set D := [set _ | _].
  transitivity (#|f @: D|).
    apply/esym/card_in_imset => /= x y.
    rewrite !inE => /andP[/forallP xD1 /forallP xD2] /andP[/forallP yD1 /forallP yD2] Hf.
    apply/rowP => i.
    case: (leqP k i) => n0i.
      move: (xD1 i); rewrite n0i implyTb => /eqP /= ->.
      move: (yD1 i); by rewrite n0i implyTb => /eqP /= ->.
    move: Hf => /rowP /(_ (Ordinal n0i)).
    rewrite !mxE !castmxE /= !cast_ord_id !esymK /= !lshift0.
    set i' := cast_ord _ _.
    suff -> : i = i' by [].
    by apply val_inj.
  apply eq_card => /= x.
  rewrite !inE; apply/imsetP/forallP => [[y yD -> {x} i]|].
    rewrite !mxE !castmxE /=.
    move: yD.
    rewrite inE => /andP[/forallP H1 /forallP /(_ (widen_ord kn i))] /=.
    rewrite (ltn_ord i) implyTb; apply: contra => /eqP H.
    by rewrite -[X in _ == X]H; apply/eqP; congr (y _ _); apply val_inj.
  move=> Hx0.
  exists (castmx (erefl, subnKC kn) (row_mx x (0%R : 'rV_(n - k)))).
  - rewrite !inE; apply/andP; split; apply/forallP => /= i; apply/implyP => n0i.
    rewrite castmxE /= cast_ord_id /=.
    set i' := cast_ord _ _.
    have @i'' : 'I_(n - k).
      exists (i - k); destruct k as [|k]; first by rewrite ltn_sub2r.
      by rewrite subnS prednK // ?subn_gt0 // subnS -subSKn -2!subn1 leq_sub2r // leq_sub2r.
    rewrite (_ : i' = rshift k i''); last by apply val_inj => /=; rewrite subnKC.
    by rewrite row_mxEr // mxE.
  - have := Hx0 (Ordinal n0i).
    apply: contra.
    rewrite castmxE /= cast_ord_id.
    set i' := cast_ord _ _.
    rewrite (_ : i' = lshift (n - k) (Ordinal n0i)); last by apply val_inj.
    by rewrite row_mxEl.
  apply/rowP => i; rewrite !mxE !castmxE /= !cast_ord_id lshift0.
  rewrite (_ : cast_ord _ _ = (lshift (n - k) i)) ?row_mxEl //; by apply val_inj.
transitivity (p.-1 ^ k); last first.
  rewrite -big_distrl /= sum1dep_card.
  set s := [set _ | _].
  rewrite (_ : s = set1 (\row_(i < n) if (k <= i)%N then 0 else 1)%R) ?cards1 ?mul1n //.
  apply/setP => /= x; rewrite !inE {s}.
  apply/idP/idP => [/andP[/forallP H1 /forallP H2]|/eqP H].
  apply/eqP/rowP => /= j; rewrite !mxE; case: ifPn => n0j.
    by move: (H1 j); rewrite n0j implyTb => /eqP.
    rewrite -ltnNge in n0j; move: (H2 j); rewrite n0j implyTb => /eqP xj0.
    apply/eqP. rewrite f2.F2_eq1. by apply/eqP.
  apply/andP; split; apply/forallP => /= j; apply/implyP => n0j;
    rewrite H mxE; by [rewrite n0j | rewrite leqNgt n0j].
by apply: card_rV_wo_zeros.
Qed.

Local Open Scope ring_scope.
Lemma wH_m_card_gen p n k : prime p -> (k <= n)%N ->
  #|[set a in 'rV['F_p]_n | wH a == k]| = ('C(n, k) * p.-1 ^ k)%N.
Proof.
move=> primep n0n.
destruct p as [|p'] => //; destruct p' as [|p'] => //.
set p := p'.+2.
destruct k as [|k'] => //.
  rewrite bin0 expn0 mul1n.
  set s := [set _ in _ | _].
  rewrite (_ : s = set1 0%R) ?cards1 //.
  apply/setP => /= x.
  by apply/idP/idP; rewrite !inE /= ?wH_eq0.
set k := k'.+1.
destruct n as [|n'] => //.
set n := n'.+1.
transitivity (#|[set a in 'rV['F_2]_n | wH a == k]| * p.-1 ^ k)%N; last first.
  by rewrite wH_m_card.
rewrite -!sum1dep_card big_distrl /=.
transitivity (\sum_(i : 'rV['F_2]_n | wH i == k)
  (\sum_(x : 'rV['F_p]_k | [forall j, x ``_ j != 0%R]) 1))%nat; last first.
  apply eq_bigr => x Hx.
  by rewrite card_rV_wo_zeros ?mul1n.
rewrite exchange_big /=.
set P := fun x : 'rV['F_p]_n => wH x == k.
set Q := fun x : 'rV['F_p]_k => [forall j, x ``_ j != 0%R].
set f := fun x : 'rV['F_p]_n => (\row_i x ``_ (nth ord0 (enum (wH_supp x)) i) : 'rV['F_p]_k).
rewrite (partition_big f Q) /=; last first.
  move=> /= x /eqP Hx.
  apply/forallP => /= i; by rewrite !mxE (@nth_wH_supp k).
apply eq_bigr => x Hx.
rewrite !sum1dep_card.
set h : 'rV['F_p]_n -> 'rV['F_2]_n := fun y => \row_i (if y ``_ i != 0 then 1 else 0)%R.
set h' : 'rV['F_2]_n -> 'rV['F_p]_n := fun y => \row_i
  if y ``_ i == 0%R then 0%R else x ``_ (inord (index i (enum (wH_supp y)))).
apply esym.
have Hh' : {in [set x0 | wH x0 == k] &, injective h'}.
  move=> u v Hu Hv.
  rewrite /h' => uv.
  apply/rowP => i.
  move/rowP: uv => /(_ i).
  rewrite !mxE.
  case: ifPn => u0i.
    case: ifPn => v0i; first by rewrite (eqP u0i) (eqP v0i).
    move/esym/eqP.
    set j := inord _.
    move/forallP in Hx.
    by move: (Hx j) => /negbTE ->.
  case: ifPn => v0i.
    set j := inord _.
    move/eqP.
    move/forallP in Hx.
    move: (Hx j); by move/negbTE ->.
  rewrite -2!f2.F2_eq1 in u0i, v0i.
  by rewrite (eqP u0i) (eqP v0i).
rewrite -[in LHS](card_in_imset Hh').
apply eq_card => /= y.
rewrite !inE.
apply/imsetP/andP => /=.
  case=> z.
  have wH_h' : wH z = wH (h' z).
    rewrite /wH !count_map; apply eq_in_count => /= i _.
    rewrite !mxE.
    case: ifPn => //= zi0; apply/esym.
    set j := inord _.
    by move/forallP : Hx => /(_ j).
  rewrite inE => Hz ->; split; first by rewrite -wH_h'.
  apply/eqP/rowP => i.
  rewrite !mxE.
  move/eqP in Hz.
  have wH_supp_h' : wH_supp (h' z) = (wH_supp z).
    apply/setP => j.
    rewrite !inE !mxE; case: ifPn => // zj0 /=.
    move/forallP : Hx; by apply.
  case: ifPn => Kz.
    move: (@nth_wH_supp _ _ _ z n0n Hz).
    rewrite -wH_supp_h'.
    move/(_ i (ltn_ord i)); by rewrite Kz.
  rewrite wH_supp_h' index_uniq ?enum_uniq //.
  by rewrite inord_val.
  by rewrite -cardE card_wH_supp Hz.
have wH_supp_h : wH_supp y = wH_supp (h y).
  apply/setP => j; rewrite !inE !mxE; by case: ifPn.
case=> Hyn0 hyx.
exists (h y); first by rewrite inE -card_wH_supp -wH_supp_h card_wH_supp.
apply/rowP => i.
rewrite !mxE.
case: ifPn; first by case: ifPn => //; rewrite negbK => /eqP.
case: ifPn => // yi0 _.
rewrite -(eqP hyx) !mxE.
have Hk : k = size (enum (wH_supp y)).
  rewrite -cardE; apply/esym; rewrite card_wH_supp; by apply/eqP.
rewrite inordK; last by rewrite -wH_supp_h -/k Hk index_mem mem_enum inE.
by rewrite wH_supp_h nth_index // mem_enum -wH_supp_h inE.
Qed.
Local Close Scope ring_scope.

Lemma card_sphere q n k x : k <= n -> prime q ->
  #|[set a in 'rV['F_q]_n | dH x a == k]| = ('C(n, k) * q.-1 ^ k)%nat.
Proof.
move=> n0m0 primeq.
rewrite /dH.
transitivity (#|[set a in 'rV['F_q]_n | wH a == k]|).
  rewrite -!sum1dep_card (reindex_onto (fun y => x - y)%R (fun y => x - y)%R) /=; last first.
    by move=> y _; rewrite opprB addrCA subrr addr0.
  apply eq_bigl => y; by rewrite !opprB addrCA subrr addr0 eqxx andbT.
destruct k as [|k]; last by apply: wH_m_card_gen.
rewrite bin0 expn0 muln1.
apply/eqP/cards1P; exists 0%R.
apply/setP => i; by rewrite !inE wH_eq0.
Qed.

Lemma sphere_not_empty n (F : finRingType) r (rn : r <= n) (x : 'rV[F]_n) :
  [set y | dH x y == r] != set0.
Proof.
destruct r as [|r'].
  rewrite /dH.
  apply/negP => /eqP/setP/(_ x).
  by rewrite inE subrr wH0 eqxx !inE.
set r := r'.+1.
apply/set0Pn.
set y : 'rV[F]_n:= (\row_i if (i < r)%N then 1 else 0)%R.
exists (x + y)%R.
rewrite inE dH_wH.
rewrite (_ : y = castmx (erefl, subnKC rn) (@row_mx _ 1 r (n -r) (const_mx 1%R) 0)).
  by rewrite wH_castmx wH_row_mx.
apply/rowP => i.
rewrite !castmxE /= cast_ord_id /= mxE.
case: ifPn => ir; set j := cast_ord _ _.
  rewrite (_ : j = lshift _ (Ordinal ir)); last by apply val_inj.
  by rewrite row_mxEl mxE.
have ir' : i - r < n - r.
  rewrite subnS prednK //; last first.
    rewrite subn_gt0; move: ir; by rewrite -leqNgt.
  destruct n as [|n'] => //.
  rewrite subSS leq_sub2r //; by move: (ltn_ord i).
rewrite (_ : j = rshift _ (Ordinal ir')); last first.
  apply val_inj => /=; by rewrite subnKC // leqNgt.
by rewrite row_mxEr mxE.
Qed.

End wH_binomial.

Section card_dH.
Variable n : nat.

Local Open Scope tuple_ext_scope.
Lemma card_dH (x y : n.-tuple 'F_2) :
  (#| [pred i | y !_ i != x !_ i ] |)%N = dH (row_of_tuple x) (row_of_tuple y).
Proof.
rewrite /dH wH_num_occ num_occ_alt /=.
apply eq_card => /= i.
rewrite inE.
move H : (_ \in _) => [|].
  symmetry.
  rewrite F2_eq1.
  move: H; apply contra.
  by rewrite tnth_mktuple !mxE subr_eq0 eq_sym.
move/negbT in H.
rewrite negbK in H.
apply/esym/negbTE.
rewrite -F2_eq0 tnth_mktuple !mxE.
move/eqP : H => ->.
by rewrite subr_eq0.
Qed.
Local Close Scope tuple_ext_scope.

(* TODO: rename? move? *)
Lemma card_dH_vec (x y : 'rV['F_2]_n) :
  (#| [pred i | y ``_ i != x ``_ i ] |)%N = dH x y.
Proof.
rewrite /dH wH_num_occ num_occ_alt /=.
apply eq_card => /= i.
rewrite inE.
move H : (_ \in _) => [|].
  symmetry.
  rewrite F2_eq1.
  apply: contra H.
  by rewrite tnth_mktuple !mxE subr_eq0 eq_sym.
move/negbT in H.
rewrite negbK in H.
apply/esym/negbTE.
rewrite -F2_eq0 tnth_mktuple !mxE.
move/eqP : H => ->.
by rewrite subr_eq0.
Qed.

Lemma card_dHC (x y : 'rV['F_2]_n) :
  (#| [pred i | y ``_ i == x ``_ i ] |)%N = (n - dH x y)%nat.
Proof.
move: (cardC [pred i | y ``_i == x ``_i ]).
rewrite card_ord => H.
by rewrite -[in X in _ = (X - _)%nat]H -card_dH_vec -addnBA // subnn addn0.
Qed.

End card_dH.

Local Open Scope ring_scope.
Lemma wH_two_pow n p : (p < n)%N -> wH (rV_of_nat n (expn 2 p)) = 1%nat.
Proof.
move=> pn.
rewrite wH_bitstring /rV_of_nat /row_of_bitseq /row_of_seq /rowF2_tuplebool /=.
rewrite /HammingBitstring.wH /num_occ count_map.
rewrite (eq_count (a2 := pred1 1)); last by move=> ? /=; rewrite eqb_id F2_eq1.
rewrite -sum1_count big_map /=.
rewrite (eq_bigl (pred1 (Ordinal (rev_ord_proof (Ordinal pn))))); last first.
  move=> i /=; symmetry; rewrite -[in X in X = _]val_eqE /=.
  rewrite mxE bitseq_of_nat_expn2 // nth_cat size_nseq.
  case: ifP => [ i_m | /negbT ].
    rewrite nth_nseq i_m /=.
    apply/negbTE; by rewrite neq_ltn i_m.
  rewrite -leqNgt leq_eqVlt; case/orP => [/eqP Heq | npi].
    by rewrite -Heq subnn /= !eqxx.
  rewrite -[in X in _ = X]subnSK //= nth_nseq.
  transitivity false; last by case: ifP.
  apply/negbTE; by rewrite neq_ltn npi orbC.
by rewrite /= big_filter_cond /= big_pred1_eq.
Qed.
Local Close Scope ring_scope.

(* TODO: clean *)
Section AboutwH123.
Local Open Scope tuple_ext_scope.

Local Notation "l `b_ i" := (@nth _ false l i) (at level 3, i at level 2).

Lemma wHb_1 : forall n l, size l = n ->
  HammingBitstring.wH l = 1%nat ->
  exists i, (i < n /\ l `b_ i = true)%nat /\
    forall j, (j < n -> j <> i -> l `b_ j = false)%nat.
Proof.
elim.
- by case.
- move=> n IH [|[] t] // [Hsz] /=.
  + case=> H.
    exists O.
    split; first by [].
    move=> j Hj Hj'.
    destruct j => //=.
    move: (has_count (pred1 true) t).
    rewrite /HammingBitstring.wH /num_occ in H.
    rewrite H ltnn.
    move/negbT/hasPn => K.
    move: (@mem_nth _ false t j).
    rewrite ltnS in Hj.
    rewrite Hsz.
    move/(_ Hj).
    move/K => /= {}K.
    apply Bool.not_true_is_false.
    by apply/eqP.
  + rewrite add0n.
    case/(IH _ Hsz) => i [[H11 H12] H2].
    exists i.+1%N.
    split; first by [].
    move=> j Hj Hj'.
    destruct j => //=.
    apply H2 => //.
    contradict Hj'; by subst j.
Qed.

Lemma wH_1 n (x : 'rV['F_2]_n) : wH x = 1%nat ->
  exists i : 'I_n, x ``_ i = 1%R /\ (forall j : 'I_n, i <> j -> x ``_ j = 0%R).
Proof.
rewrite wH_bitstring.
move/wHb_1.
move/(_ n).
rewrite size_tuple.
case/(_ erefl) => i [] [] H1 H2 H3.
exists (Ordinal H1); split.
  transitivity (F2_of_bool true) => //.
  rewrite -H2 /rowF2_tuplebool (nth_map ord0); last by rewrite size_tuple.
  rewrite (_ : _ _ _ i = (tuple_of_row x) !_ (Ordinal H1)); last first.
    apply set_nth_default; by rewrite size_tuple.
  rewrite tnth_mktuple {1}(F2_0_1 (x ``_ (Ordinal H1))); by case: (x ``_ _ != 0%R).
move=> j Hj.
transitivity (F2_of_bool false) => //.
rewrite -(H3 j) //; last first.
  move=> ?; subst i.
  by apply/Hj/val_inj.
rewrite /rowF2_tuplebool (nth_map ord0); last by rewrite size_tuple.
suff -> : x ``_ j = nth ord0 (tuple_of_row x) j by apply: F2_0_1.
rewrite (_ : _ _ _ j = (tuple_of_row x) !_ j); last by rewrite tnth_mktuple.
exact: tnth_nth.
Qed.

Lemma wHb_2 : forall n l, size l = n ->
  HammingBitstring.wH l = 2%nat ->
  (exists i, exists k, (i < n /\ l `b_ i = true) /\
    (k < n /\ l `b_ k = true) /\ i <> k /\
    forall j, j < n -> j <> i -> j <> k -> l `b_ j = false)%nat.
Proof.
elim.
- by case.
- case.
  move=> IH l Hsz Hcount.
  rewrite /HammingBitstring.wH /num_occ in Hcount.
  move: (count_size (pred1 true) l).
  by rewrite Hcount Hsz ltnn.
- move=> n IH [|[] t] // [Hsz] /=.
  + rewrite add1n.
    case=> X.
    exists O.
    case: (@wHb_1 _ _ Hsz X) => k [[Hk1 Hk11] Hk2].
    exists k.+1%N.
    split; first by [].
    split; first by split => //; exact: (@leq_ltn_trans n.+1%N).
    split; first by [].
    move=> j Hj Hj' Hjk.
    destruct j => //=.
    apply Hk2 => //.
    contradict Hjk; by rewrite Hjk.
  + rewrite add0n.
    case/(IH _ Hsz) => i [k [[H11 H12] [H21 [H221 H222]]]].
    exists i.+1%N, k.+1%N.
    split; first by [].
    split; first by [].
    split.
    contradict H221; by case: H221.
    move=> j Hj Hj' Hjk.
    destruct j => //=.
    apply H222 => //.
    contradict Hj'; by subst j.
    contradict Hjk; by subst j.
Qed.

Lemma wH_2 n (x : 'rV['F_2]_n) : wH x = 2%nat ->
  exists i j : 'I_n, i <> j /\ x ``_ i = 1%R /\ x ``_ j = 1%R /\
  (forall k : 'I_n, i <> k -> j <> k -> x ``_ k = 0%R).
Proof.
rewrite wH_bitstring.
move/wHb_2.
move/(_ n).
rewrite size_tuple.
case/(_ erefl) => i [] k [] [] H1 H2 [] [] H3 H4 [] H5 H6.
exists (Ordinal H1), (Ordinal H3); split.
  by case.
split.
  transitivity (F2_of_bool true) => //.
  rewrite -H2 /rowF2_tuplebool (nth_map ord0); last by rewrite size_tuple.
  rewrite (_ : _ _ _ i = (tuple_of_row x) !_ (Ordinal H1)); last first.
    apply set_nth_default; by rewrite size_tuple.
  rewrite tnth_mktuple {1}(F2_0_1 (x ``_ (Ordinal H1))); by case: (x ``_ _ != 0%R).
split.
  transitivity (F2_of_bool true) => //.
  rewrite -H4 /rowF2_tuplebool (nth_map ord0); last by rewrite size_tuple.
  rewrite (_ : _ _ _ k = (tuple_of_row x) !_ (Ordinal H3)); last first.
    apply set_nth_default; by rewrite size_tuple.
  rewrite tnth_mktuple {1}(F2_0_1 (x ``_ (Ordinal H3))); by case: (x ``_ _ != 0%R).
move=> j ij kj.
transitivity (F2_of_bool false) => //.
rewrite -(H6 j) //; last first.
- move=> ?; subst k.
  by apply/kj/val_inj.
- move=> ?; subst i.
  by apply/ij/val_inj.
rewrite /rowF2_tuplebool (nth_map ord0); last by rewrite size_tuple.
suff -> : x ``_ j = nth ord0 (tuple_of_row x) j by apply: F2_0_1.
rewrite (_ : _ _ _ j = (tuple_of_row x) !_ j); last by rewrite tnth_mktuple.
exact: tnth_nth.
Qed.

Lemma wH_3 : forall n, (3 <= n)%N -> wH (rV_of_nat n 3) = 2%N.
Proof.
case => // [] // [] // [] // n _.
rewrite /wH /num_occ /rV_of_nat.
set tmp := tuple_of_row _.
have -> : tmp = [tuple of rev (1 :: 1 :: nseq n.+1 0)]%R.
  apply eq_from_tnth => i.
  rewrite tnth_mktuple mxE.
  rewrite -(nth_map _ 0%R); last by rewrite size_cat size_nseq /= addn2.
  rewrite (tnth_nth 0%R); congr ( _ `_ i)%R.
  rewrite /= (_ : 0 :: nseq n 0 = nseq n.+1 0)%R //.
  rewrite nseq_S -[in RHS]cat1s -[in RHS](cat1s _ (rcons _ _)) catA rev_cat.
  rewrite [in RHS]rev_rcons /=; congr (_ :: _).
  by rewrite rev_nseq map_cat map_nseq.
rewrite /=.
set y := _ :: _.
rewrite (_ : y = [:: 1; 1; 0] ++ nseq n 0)%R // rev_cat count_cat /= -(@eq_in_count _ pred0).
  by rewrite count_pred0.
move=> /= b; by rewrite rev_nseq => /nseqP[->].
Qed.

Lemma wH_7 : forall n, (3 <= n)%N -> wH (rV_of_nat n 7) = 3%N.
Proof.
case => // [] // [] // [] // n _.
rewrite /wH /num_occ /rV_of_nat.
set x := tuple_of_row _.
have -> : x =[tuple of rev (1 :: 1 :: 1 :: nseq n 0)]%R.
  rewrite /x {x}.
  apply eq_from_tnth => i.
  rewrite tnth_mktuple mxE (tnth_nth 0%R).
  rewrite -(nth_map _ ord0); last first.
    rewrite /pad_seqL /=.
    destruct n => //=.
    by rewrite size_cat size_nseq /= addn3.
  congr (_ `_ i)%R.
  rewrite /bitseq_of_nat /= !rev_cons /= /pad_seqL /= -addn3 addnK map_cat /= map_nseq /=.
  by rewrite rev_nseq -!cats1 /= -!catA.
rewrite /=.
set y := _ :: _.
rewrite (_ : y = [:: 1; 1; 1] ++ nseq n 0)%R // rev_cat count_cat /=.
rewrite -(@eq_in_count _ pred0) ?count_pred0 //.
by move=> /= b; rewrite rev_nseq => /nseqP[->].
Qed.

Lemma wH_7_rev7 n : (2 < n)%N ->
  wH (rV_of_nat n 7) = wH (rV_of_nat n (7 * expn 2 (n - 3))).
Proof.
move=> Hn.
rewrite 2!wH_num_occ /rV_of_nat.
set lhs := tuple_of_row _.
set rhs := tuple_of_row _.
suff <- : rev lhs = rhs by apply num_occ_rev.
rewrite /lhs /rhs.
rewrite /row_of_bitseq.
rewrite -!row_of_seqK.
rewrite -map_rev.
by rewrite rev_bitseq_of_nat_7.
Qed.

End AboutwH123.

Local Open Scope ring_scope.

Lemma hamming_01 (R : realType) m p :
  \sum_(u in 'rV['F_2]_m| u \in [set v |(1 >= wH v)%nat])
    (1 - p) ^+ (m - wH u) * p ^+ wH u =
  (1 - p) ^+ m + m%:R * p * (1 - p) ^+ (m - 1) :> R.
Proof.
rewrite (bigID [pred i | wH i == O]) /=.
rewrite (big_pred1 (@GRing.zero _)) /=; last first.
  by move=> i /=; rewrite !inE -wH_eq0 andb_idl // => /eqP ->.
rewrite wH0 expr0 subn0 mulr1; congr (_ + _).
transitivity (\sum_(i | wH (i : 'rV['F_2]_m) == 1%nat) ((1 - p) ^+ (m - 1) * p ^+ 1)).
  transitivity (\sum_(i|(wH (i : 'rV['F_2]_m) == 1)%nat)
      ((1 - p) ^+ (m - wH i) * p ^+ wH i)).
    apply eq_bigl => /= i.
    rewrite !inE.
    case/boolP : (wH i == 1)%nat => [/eqP -> //|wH_1].
    case wH_0 : (wH i) => [|n1]; first by rewrite eqxx.
    rewrite /= andbT.
    case n1_0 : n1 => [|? //].
    by rewrite wH_0 n1_0 in wH_1.
  by apply/eq_bigr => /= v /eqP ->.
rewrite big_const iter_addr addr0 expr1 /=.
rewrite -cardsE wH_m_card bin1 mulrC.
rewrite -mulrA.
by rewrite mulr_natl.
Qed.

Lemma binomial_theorem {R : realType} m p :
  \sum_(b in [set: 'rV['F_2]_m]) (1 - p) ^+ (m - wH b) * p ^+ wH b = 1 :> R.
Proof.
transitivity (((1 - p) + p) ^+ m); last first.
  by rewrite subrK expr1n.
rewrite exprDn.
transitivity (\sum_(b : 'rV['F_2]_m) (1 - p) ^+ (m - wH b) * p ^+ wH b).
  by apply eq_bigl => /= i; rewrite inE.
rewrite (classify_big (fun s => Ordinal (max_wH' s))
                 (fun x => (1 - p) ^+ (m - x) * p ^+ x)) /=.
apply: eq_bigr=> i _.
rewrite -wH_m_card.
rewrite mulr_natl.
congr (_*+ _).
by apply eq_card => /= x; rewrite !inE.
Qed.
