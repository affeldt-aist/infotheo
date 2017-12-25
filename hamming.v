(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import fintype finfun finset bigop prime fingroup zmodp.
From mathcomp Require Import ssralg perm matrix tuple poly finalg mxalgebra.
From mathcomp Require Import mxpoly mxrepresentation binomial.
Require Import ssr_ext ssralg_ext f2 num_occ natbin.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma num_occ_sum : forall (t : seq 'F_2), num_occ 1%R t = \sum_(i <- t) i.
Proof.
elim => [ /= | /= h t ->]; first by rewrite big_nil.
rewrite big_cons; by case/F2P: h.
Qed.

Lemma addb_nseq b : forall r v, size v = r ->
  [seq x.1 (+) x.2 | x <- zip (nseq r b) v] = map (pred1 (negb b)) v.
Proof.
elim=> [ [] // | r IH [|h t] //= [] r_t].
rewrite {}IH //; move: b h; by case; case.
Qed.

Definition addb_seq a b := [seq x.1 (+) x.2 | x <- zip a b].

Lemma addb_seq_com : forall n a b, size a = n -> size b = n ->
  addb_seq a b = addb_seq b a.
Proof.
elim => [ [] // [] // | n IH [|ha ta] // [|hb tb] // ] [Ha] [Hb].
by rewrite /addb_seq /= -!/(addb_seq _ _) IH // addbC.
Qed.

Lemma addb_tri_ine a b c : a (+) b <= (a (+) c) + (c (+) b).
Proof. move: a b c; by case; case; case. Qed.

Lemma addb_seq_cat a b c d : size a = size c ->
  addb_seq (a ++ b) (c ++ d) = addb_seq a c ++ addb_seq b d.
Proof. move=> a_c; by rewrite /addb_seq /= -map_cat zip_cat. Qed.

Lemma addb_seq_map {A : Type} : forall n (a b : seq A) f,
  size a = n -> size b = n ->
  addb_seq (map f a) (map f b) = map (fun x => f x.1 (+) f x.2) (zip a b).
Proof.
elim => [[] // [] //| n IH [|ha ta] // [|hb tb] //= f [Ha] [Hb]].
by rewrite /addb_seq /= -IH.
Qed.

Module HammingBitstring.

Local Open Scope num_occ_scope.

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
  dH a b <= dH a c + dH c b.
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
  dH (a ++ b) (c ++ d) = dH a c + dH b d.
Proof.
move=> ac bd; by rewrite /dH /wH addb_seq_cat // /num_occ count_cat.
Qed.

End HammingBitstring.

(* TODO: move *)
Lemma enum_inord (m : nat) : enum 'I_m.+1 = [seq inord i | i <- iota 0 m.+1].
Proof.
rewrite -val_enum_ord -map_comp.
transitivity ([seq i | i <- enum 'I_m.+1]); first by rewrite map_id.
apply eq_map => i /=; by rewrite inord_val.
Qed.

Open Scope vec_ext_scope.

Local Open Scope ring_scope.

(* TODO: move *)
Lemma seq_of_poly_rV (F : ringType) m (p : {poly F}) (_ : size p < m) :
  [seq (poly_rV p) ``_ i | i <- enum 'I_m] =
  [seq (poly_rV p) ``_ i | i <- enum ('I_(size p))] ++ nseq (m - size p) 0.
Proof.
case: m H => // m pm.
rewrite (_ : enum _ = map inord (iota 0 (size p) ++ iota (size p) (m.+1 - size p))); last first.
  by rewrite -iota_add subnKC ?enum_inord // ltnW.
rewrite 2!map_cat; congr (_ ++ _).
  rewrite -val_enum_ord -!map_comp; apply eq_map => i /=.
  by rewrite !mxE inordK // (ltn_trans (ltn_ord i)).
rewrite -map_comp.
apply (@eq_from_nth _ 0); first by rewrite size_map size_iota size_nseq.
move=> i.
rewrite size_map size_iota => Hi.
rewrite (nth_map O) ?size_iota //= mxE nth_nseq Hi nth_iota //.
move/leq_sizeP: (leq_addr i (size p)); apply.
by rewrite inordK // -ltn_subRL.
Qed.

Local Close Scope ring_scope.

Section hamming_weight_distance.

Variables (F : ringType) (n : nat).
Implicit Types u v : 'rV[F]_n.

Local Open Scope ring_scope.

Definition wH v := count (fun x => x != 0) (tuple_of_row v).

Lemma wH_rVpoly u : wH u = count (fun i : 'I_n => (rVpoly u)`_i != 0) (enum 'I_n).
Proof.
rewrite /wH count_map; apply eq_in_count => /= i _.
rewrite coef_poly insubT // => ni.
rewrite ltn_ord; congr (u _ _ != _); by apply val_inj.
Qed.

Lemma wH_poly_rV (p : {poly F}) : wH (poly_rV p) <= size p.
Proof.
rewrite /wH /=.
case/boolP : (size p < n) => pn; last first.
  rewrite -leqNgt in pn; rewrite (leq_trans _ pn) //.
  by rewrite (leq_trans (count_size _ _)) // size_map size_enum_ord.
have -> : [seq (poly_rV p) ``_ i | i <- enum 'I_n] =
  [seq (poly_rV p) ``_ i | i <- enum ('I_(size p))] ++ nseq (n - size p) 0.
  by rewrite seq_of_poly_rV.
rewrite count_cat [X in _ + X <= _](_ : count _ _ = O) ?addn0; last first.
  rewrite (@eq_in_count _ _ pred0) ?count_pred0 //.
  move=> i; case/nseqP => -> /= _; by rewrite eqxx.
by rewrite count_map (leq_trans (count_size _ _)) // size_enum_ord.
Qed.

Lemma max_wH u : wH u <= n.
Proof. by rewrite /wH (leq_trans (count_size _ _)) // size_tuple. Qed.

Lemma max_wH' u : wH u < n.+1.
Proof. rewrite ltnS. by apply max_wH. Qed.

Lemma wH0 : wH 0 = O.
Proof.
rewrite /wH (@eq_in_count _ _ pred0) ?count_pred0 // => i /mapP[/= j _].
by rewrite mxE => ->; rewrite eqxx.
Qed.

Lemma wH0_inv v : wH v = O -> v = 0.
Proof.
move=> H.
apply/rowP => i; rewrite mxE; apply/eqP; move/eqP : H; apply: contraTT => H.
rewrite -lt0n -has_count; apply/hasP.
exists (v 0 i) => //; apply/mapP; exists i => //.
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

Definition dH u v := wH (u - v).

Lemma dHE u v : dH u v = wH (u - v). Proof. by []. Qed.

Lemma dH_wH u v : dH u (u + v) = wH v.
Proof. by rewrite /dH opprD addrA subrr add0r wH_opp. Qed.

Lemma dH0x x : dH 0 x = wH x.
Proof. by rewrite /dH add0r wH_opp. Qed.

Lemma max_dH u v : dH u v <= n.
Proof. rewrite /dH. apply max_wH. Qed.

Lemma dH_sym u v : dH u v = dH v u.
Proof. by rewrite {1}/dH -wH_opp opprB. Qed.

Local Open Scope nat_scope.

Lemma wH_sum v : wH v = \sum_(n0 < n) (v ``_ n0 != 0)%R.
Proof.
rewrite /wH 1!count_map -sum1_count /= big_mkcond /=.
apply congr_big => //=; by rewrite /index_enum -enumT.
Qed.

Local Close Scope nat_scope.

Lemma wH_card_supp u : wH u = #|supp u|%N.
Proof.
rewrite wH_sum /supp -sum1dep_card [in RHS]big_mkcond; by apply/eq_bigr.
Qed.

End hamming_weight_distance.

Lemma wH_count n (x : 'rV['F_2]_n) : wH x = count (fun i => x ``_ i == 1%R) (enum 'I_n).
Proof.
rewrite wH_sum -sum1_count [in RHS]big_mkcond /=.
apply congr_big => //.
- by rewrite /index_enum -enumT.
- move=> i _; case: ifPn => [/eqP -> //|].
  by rewrite -F2_eq0 => /eqP ->.
Qed.

Lemma sum_wH_row (F : ringType) n m (H : 'M[F]_(m, n)) :
  \sum_(m0 : 'I_m) wH (row m0 H) = \sum_(n0 : 'I_n) wH (col n0 H)^T.
Proof.
transitivity (\sum_(m0 < m) \sum_(n0 < n) (H m0 n0 != 0)%R).
  apply eq_bigr => m0 _.
  rewrite wH_sum; apply eq_bigr => n0 _; by rewrite mxE.
rewrite exchange_big /=.
apply eq_bigr => n0 _.
rewrite wH_sum; apply eq_bigr => m0 _; by rewrite 2!mxE.
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
  count (fun x : F => x != 0%R) (tuple_of_row (v - w)) =
  addn (v ``_ 0 - w ``_ 0 != 0)%R (count (fun x : F => x != 0)%R (behead (tuple_of_row (v - w)))).
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

Definition wH_supp x := [set i | x ``_ i != 0%R].

Lemma card_wH_supp x : #| wH_supp x |%N = wH x.
Proof.
rewrite cardE size_filter /wH count_map -enumT /=.
apply eq_in_count => /= i _; by rewrite inE.
Qed.

Lemma mem_wH_supp x (i : 'I_n) : (x ``_ i != 0%R) = (i \in wH_supp x).
Proof. by rewrite inE. Qed.

End wH_supp.

Lemma nth_wH_supp k n (F : ringType) (y : 'rV[F]_n.+1) : (k <= n.+1)%N ->
  wH y = k -> forall j : nat, (j < k)%N -> y ``_ (nth ord0 (enum (wH_supp y)) j) != 0%R.
Proof.
move=> kn yD j jk; rewrite mem_wH_supp -mem_enum; apply/mem_nth.
by rewrite -cardE card_wH_supp yD.
Qed.

Section wH_old.

Local Open Scope num_occ_scope.
Local Open Scope ring_scope.

Definition wH_old n (v : 'rV['F_2]_n) := N(1 | tuple_of_row v).

Lemma wH_oldE n (v : 'rV['F_2]_n) : wH v = wH_old v.
Proof.
rewrite /wH /wH_old /num_occ; apply eq_count => i; by rewrite -F2_eq1.
Qed.

Lemma wH_old_wH_b n (x : 'rV_n) :
  wH_old x = HammingBitstring.wH (tval (rowF2_tuplebool x)).
Proof.
rewrite /wH_old /HammingBitstring.wH /= /num_occ /= [in RHS]count_map.
apply eq_in_count => /= b Hb; by rewrite -(F2_eq1 b) eqb_id.
Qed.

Lemma wH_col_1 n (i : 'I_n) : @wH [fieldType of 'F_2] _ (col i 1%:M)^T = 1%N.
Proof.
rewrite wH_oldE /wH_old.
rewrite num_occ_alt.
apply/eqP/cards1P.
exists i.
apply/setP => n0.
rewrite in_set1 in_set tnth_mktuple 3!mxE.
by case (_ == i).
Qed.

Local Open Scope tuple_ext_scope.

Lemma dH_dH_bitseq n (a b : 'rV_n) :
  dH a b = HammingBitstring.dH (tval (rowF2_tuplebool a)) (tval (rowF2_tuplebool b)).
Proof.
rewrite /dH wH_oldE /wH_old.
rewrite /HammingBitstring.dH /HammingBitstring.wH.
transitivity (N(true | map bool_of_F2 (tuple_of_row (a - b)))).
  rewrite num_occ_sum_bool big_map num_occ_sum.
  apply eq_bigr; by case/F2P.
congr (N(true | _)).
apply/(@eq_from_nth _ true) => [|i Hi].
  by rewrite size_map /addb_seq size_map size_zip !size_tuple minnn.
rewrite size_map size_tuple in Hi.
rewrite (nth_map (0 : 'F_2)); last by rewrite size_tuple.
rewrite /addb_seq.
rewrite (nth_map (true, true)); last by rewrite size_zip 2!size_tuple minnn.
rewrite nth_zip /=; last by rewrite 2!size_map 2!size_tuple.
rewrite /bool_of_F2.
rewrite (_ : _ `_ i = [tuple (a - b) ``_ x | x < n] \_ (Ordinal Hi)); last first.
  rewrite tnth_mktuple.
  rewrite (nth_map (Ordinal Hi)) //; last by rewrite size_enum_ord.
  congr (_ ord0 _).
  by rewrite -[RHS](@nth_ord_enum n (Ordinal Hi)).
rewrite tnth_mktuple !mxE.
rewrite (nth_map (0 : 'F_2)); last by rewrite size_map size_enum_ord.
rewrite (nth_map (0 : 'F_2)); last by rewrite size_map size_enum_ord.
rewrite (_ : _ `_ i = (tuple_of_row a) \_ (Ordinal Hi)); last first.
  rewrite tnth_mktuple (nth_map (Ordinal Hi)); last by rewrite size_enum_ord.
  congr (_ ord0 _).
  apply val_inj => /=.
  by rewrite nth_enum_ord.
rewrite (_ : _ `_ i = (tuple_of_row b) \_ (Ordinal Hi)); last first.
  rewrite tnth_mktuple (nth_map (Ordinal Hi)); last by rewrite size_enum_ord.
  congr (_ ord0 _).
  apply val_inj => /=.
  by rewrite nth_enum_ord.
by rewrite 2!tnth_mktuple oppr_char2 // -bool_of_F2_add_xor.
Qed.

End wH_old.

Lemma wH_castmx n (F : ringType) (x : 'rV[F]_n) n' (H : (1 = 1)%N * (n = n')) :
  wH (castmx H x) = wH x.
Proof.
case: H => H1 H2; subst n'.
rewrite /wH !count_map /=; apply eq_in_count => /= i _.
by rewrite castmxE /= !cast_ord_id.
Qed.

Local Open Scope ring_scope.

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

Local Close Scope ring_scope.

Section wH_permutation.

Variable n : nat.

Lemma perm_on_Sn (s : 'S_n) : perm_on [set x | x \in enum 'I_n] s.
Proof. apply/subsetP=> /= x _; by rewrite !in_set mem_enum. Qed.

Lemma perm_eq_enum (s : 'S_n) : perm_eq (enum 'I_n) (map (s^-1)%g (enum 'I_n)).
Proof.
apply uniq_perm_eq.
- by apply enum_uniq.
- rewrite map_inj_uniq; by [apply enum_uniq | apply: perm_inj].
- move=> /= xi.
  case Hi : (xi \in enum 'I_n).
  + symmetry; apply/mapP; exists (s xi).
    * move: (perm_closed xi (perm_on_Sn s)).
      by rewrite !in_set => ->.
    * by rewrite permK.
  + symmetry; apply/mapP; case=> x Hx Hxxi.
    move: (perm_closed x (perm_on_Sn (s^-1)%g)).
    by rewrite !in_set -Hxxi Hx Hi.
Qed.

Lemma wH_perm_mx (s : 'S_n) (z : 'rV['F_2]_n) : wH (z *m perm_mx s) = wH z.
Proof.
rewrite !wH_oldE /wH_old.
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
pose h' := fun s : {set 'I_n} => \row_(j < n) (if j \in s then (1 : 'F_2) else 0)%R.
have h'h (i : 'rV_n) : h' [set i0 | i ``_ i0 == 1%R] == i.
  apply/eqP/rowP => y; rewrite !mxE inE.
  case: ifP => [/eqP -> // | /negbT]; by rewrite -F2_eq0 => /eqP.
rewrite (reindex_onto (fun x : 'rV_n => [set i | x ``_ i == 1%R]) h') /=.
- apply eq_bigl => i.
  rewrite wH_oldE /wH_old num_occ_alt h'h andbC /=; congr (_ == _).
  apply eq_card => t; by rewrite !inE tnth_mktuple.
- move=> s Hs.
  apply/setP => /= i; rewrite !inE /h' mxE; by case: ifP.
Qed.

Local Close Scope ring_scope.

Local Open Scope nat_scope.

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
  rewrite (_ : s = set1 (\row_(i < n) if k <= i then 0 else 1)%R) ?cards1 ?mul1n //.
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

Local Close Scope nat_scope.

Local Open Scope ring_scope.
Local Open Scope nat_scope.

Lemma wH_m_card_gen p n k : prime p -> k <= n ->
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
  (\sum_(x : 'rV['F_p]_k | [forall j, x ``_ j != 0%R]) 1)); last first.
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

Lemma card_sphere q n k x : k <= n -> prime q ->
  #|[set a in 'rV['F_q]_n | dH x a == k]| = 'C(n, k) * q.-1 ^ k.
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
set y : 'rV[F]_n:= (\row_i if i < r then 1 else 0)%R.
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
  (#| [pred i | y \_ i != x \_ i ] |)%N = dH (row_of_tuple x) (row_of_tuple y).
Proof.
rewrite /dH wH_oldE /wH_old num_occ_alt /=.
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

(* TODO: rename? move? *)
Lemma card_dH_vec (x y : 'rV['F_2]_n) :
  (#| [pred i | y ``_ i != x ``_ i ] |)%N = dH x y.
Proof.
rewrite /dH wH_oldE /wH_old num_occ_alt /=.
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

(** Encoding of Naturals as Vectors *)

(** Function that transforms natural numbers into their binary encodings, e.g.:
  nat2bin 3 1 = [ 0 0 1 ],
  nat2bin 3 2 = [ 0 1 0 ],
  nat2bin 3 3 = [ 0 1 1 ]. *)

Section rV_and_nat_def.

Variable n : nat.

Definition rV_of_nat (i : nat) : 'rV['F_2]_n := bitseq_F2row (size_nat2bin i n).

Definition nat_of_rV (y : 'rV['F_2]_n) : nat :=
  BinNat.N.to_nat (bitseq2N (map bool_of_F2 (tuple_of_row y))).

End rV_and_nat_def.

(* TODO: clean *)
Section rV_and_nat_prop.

Variable n : nat.

Local Open Scope ring_scope.

Lemma rV_of_nat_neq0 i : i <> O -> (i < expn 2 n)%N -> rV_of_nat n i <> 0%R.
Proof.
move=> Hi W.
rewrite /rV_of_nat /bitseq_F2row /bitseq_to_row.
move: (nat2bin_nseq_false i n Hi W) => H.
contradict H.
apply eq_from_nth with false.
- by rewrite /= size_pad_seqL size_nseq.
- move=> j Hj.
  rewrite (_ : size _ = n) in Hj; last first.
    (* TODO: lemma? *)
    apply/eqP. by apply size_nat2bin.
  move/rowP : H => /(_ (Ordinal Hj)).
  rewrite !mxE /= => Hj'.
  rewrite nth_nseq Hj.
  by apply F2_of_bool_0_inv.
Qed.

(* TODO: move? *)
Lemma row_nth (i j : bitseq) : (size i <= n)%nat -> size j = size i ->
  \row_(i0 < n) F2_of_bool (nth false i i0) =
  \row_(i0 < n) F2_of_bool (nth false j i0) -> i = j.
Proof.
move=> Hi Hj /matrixP Heq.
apply/esym.
apply (@eq_from_nth _ false _ _ Hj) => i0 Hi0.
rewrite Hj in Hi0.
have {Hi0}Hi0 : (i0 < n)%nat.
  apply leq_ltn_trans with ((size i).-1)%nat;
    rewrite -ltnS prednK //; by apply leq_ltn_trans with i0.
move: (Heq 0 (Ordinal Hi0)).
rewrite !mxE /=; by do 2 case: nth.
Qed.

Lemma rV_of_nat_inj i j : (nat_of_pos i < expn 2 n)%N -> (nat_of_pos j < expn 2 n)%N ->
  rV_of_nat n (nat_of_pos i) = rV_of_nat n (nat_of_pos j) -> i = j.
Proof.
move=> Hi Hj.
rewrite /rV_of_nat /bitseq_F2row /bitseq_to_row.
move/row_nth => X.
have Htmp : (size (nat2bin (nat_of_pos i) n) <= n)%N.
  move: (size_nat2bin (nat_of_pos i) n).
  by move/eqP => ->.
apply X in Htmp => //; last first.
  apply (@trans_eq _ _ n).
  - by apply/eqP/size_nat2bin.
  - by apply/esym/eqP/size_nat2bin.
rewrite /nat2bin in Htmp.
move: (N2bitseq_leading_bit (bin_of_nat (nat_of_pos i))) => U.
lapply U; last by apply bin_of_nat_nat_of_pos_not_0.
case=> ik Hik.
rewrite Hik in Htmp.
move: (N2bitseq_leading_bit (bin_of_nat (nat_of_pos j))) => V.
lapply V; last by apply bin_of_nat_nat_of_pos_not_0.
case=> jk Hjk.
rewrite Hjk in Htmp.
destruct n as [|n0].
- rewrite expn0 in Hi.
  move: (@nat_of_pos_not_0 i) => W.
  by destruct (nat_of_pos i).
- apply pad_seqL_leading_true_inj in Htmp; last 2 first.
    have H : (size (true :: ik) <= n0.+1)%N.
      rewrite -Hik size_rev.
      apply size_N2bitseq_ub => //.
      by apply nat_of_pos_not_0.
    by rewrite /= ltnS in H.
  have H : (size (true :: jk) <= n0.+1)%N.
    rewrite -Hjk size_rev.
    apply size_N2bitseq_ub => //.
    by apply nat_of_pos_not_0.
    by rewrite /= ltnS in H.
  subst ik.
  rewrite -Hjk in Hik.
  move/rev_inj : Hik.
  by move/N2bitseq_inj/bin_of_nat_inj/nat_of_pos_inj.
Qed.

Local Open Scope nat_scope.
Local Open Scope ring_scope.

Lemma rV_of_natD_neq0 i j : i <> j -> i <> O -> j <> O ->
  (i < expn 2 n)%N -> (j < expn 2 n)%N -> rV_of_nat n i + rV_of_nat n j <> 0.
Proof.
move=> Hij Hi Hj Hin Hjn.
destruct i => //.
destruct j => //.
contradict Hij.
apply F2_addmx0 in Hij.
have [ii Hii] : exists ii, i.+1 = nat_of_pos ii.
  exists (BinPos.P_of_succ_nat i).
  rewrite -Pnat.nat_of_P_o_P_of_succ_nat_eq_succ.
  by rewrite BinPos_nat_of_P_nat_of_pos.
have [jj Hjj] : exists jj, j.+1 = nat_of_pos jj.
  exists (BinPos.P_of_succ_nat j).
  rewrite -Pnat.nat_of_P_o_P_of_succ_nat_eq_succ.
  by rewrite BinPos_nat_of_P_nat_of_pos.
rewrite Hii Hjj in Hij.
apply rV_of_nat_inj in Hij; last 2 first.
  by rewrite -Hii.
  by rewrite -Hjj.
rewrite Hjj; by subst ii.
Qed.

Lemma mulmx_rV_of_nat_row n' (M : 'M_(n, n')) (k : 'I_n) :
  rV_of_nat n (expn 2 k) *m M = row (Ordinal (rev_ord_proof k)) M.
Proof.
rewrite /rV_of_nat.
apply/rowP => i.
rewrite !mxE /=.
transitivity (\sum_(j < n) (F2_of_bool (nth false (nat2bin (expn 2 k) n) j) * M j i)).
  apply eq_bigr => l _; by rewrite mxE.
rewrite nat2bin_two_pow //.
pose mk := Ordinal (rev_ord_proof k).
rewrite -/mk (bigID (pred1 mk)) /= big_pred1_eq.
set x := nth _ _ _.
have -> : x = true.
  by rewrite {}/x nth_cat size_nseq {1}/mk ltnn subnn.
rewrite mul1r.
set lhs := \sum_ (_ | _) _.
suff -> : lhs = 0 by rewrite addr0.
transitivity (\sum_(i | i != mk) (0 : 'F_2)).
  apply eq_bigr => l lmk.
  set rhs := nth _ _ _.
  suff -> : rhs = false by rewrite mul0r.
  rewrite /rhs nth_cat size_nseq.
  case: ifP => Hcase; first by rewrite nth_nseq Hcase.
  rewrite (_ : true :: _ = [:: true] ++ nseq k false) // nth_cat /=.
  case: ifP => lnk.
    suff : False by done.
    clear -lnk lmk Hcase.
    have {lnk} : l <= n - k.+1 by rewrite ltnS leqn0 in lnk.
    rewrite leq_eqVlt Hcase orbC /=; by apply/negP.
  rewrite nth_nseq; by case: ifP.
by rewrite big_const iter_addr0.
Qed.

Lemma rV_of_nat_0 : rV_of_nat n 0 = 0.
Proof.
rewrite /rV_of_nat /bitseq_F2row /bitseq_to_row nat2bin_0_n.
apply/rowP => b /=.
rewrite 2!mxE nth_nseq; by case: ifP.
Qed.

Lemma nat_of_rV_up (y : 'rV_n) : nat_of_rV y < expn 2 n.
Proof. by rewrite /nat_of_rV bitseq2N_up // size_map size_tuple. Qed.

Lemma nat_of_rV_0 : nat_of_rV (0 : 'rV_n) = O.
Proof.
rewrite /nat_of_rV.
set tmp := map _ _.
have -> : tmp = nseq n false.
  rewrite {}/tmp  /= (_ : false = bool_of_F2 0) // -map_nseq.
  congr ([seq _ | i <- _]).
  apply eq_from_nth with 0.
  - by rewrite size_map size_enum_ord size_nseq.
  - move=> i Hi.
    rewrite size_map size_enum_ord in Hi.
    rewrite nth_nseq Hi (nth_map (Ordinal Hi)); last by rewrite size_enum_ord.
    by rewrite mxE.
by rewrite bitseq2N_nseq_false.
Qed.

Lemma tuple_of_row_ord0 (F : Type) (y : 'rV[F]_0) : tuple_of_row y = [tuple of [::]].
Proof. apply eq_from_tnth; by case. Qed.

Lemma nat_of_rV_ord0 (y : 'rV_0) : nat_of_rV y = O.
Proof. by rewrite /nat_of_rV N_bin_to_nat tuple_of_row_ord0. Qed.

Lemma nat_of_rV_eq0 (y : 'rV_n) : (nat_of_rV y == O) = (y == 0).
Proof.
case Hlhs : (nat_of_rV _ == O); last first.
  symmetry; apply/negP => /eqP abs; subst y.
  by rewrite nat_of_rV_0 eqxx in Hlhs.
symmetry; apply/eqP.
move/eqP : Hlhs.
rewrite /nat_of_rV [X in _ = X -> _](_ : O = BinNat.N.to_nat 0) //.
move/Nnat.N2Nat.inj/bitseq2N_0.
rewrite size_map size_tuple.
move/(_ _ erefl) => Htmp.
apply tuple_of_row_inj, val_inj.
rewrite -(map_id (val (tuple_of_row y))).
transitivity (map (F2_of_bool \o bool_of_F2) (val (tuple_of_row y))).
  apply eq_in_map => i /= _; by rewrite bool_of_F2K.
by rewrite map_comp Htmp row_to_seq_0 (_ : 0 = F2_of_bool false) // map_nseq.
Qed.

Lemma nat_of_rVK (y : 'rV_n) : rV_of_nat n (nat_of_rV y) = y.
Proof.
destruct n as [|n0].
  apply/rowP; by case.
apply/rowP => i.
rewrite mxE /nat_of_rV.
set tmp := [seq bool_of_F2 i | i <- _].
rewrite [X in nat2bin _ X](_ : _ = size tmp); last by rewrite size_map size_tuple.
rewrite bitseq2NK; last by rewrite size_tuple.
rewrite /tmp (nth_map (0 : 'F_2)); last by rewrite size_tuple.
rewrite bool_of_F2K (_ : _ `_ _ = tnth (tuple_of_row y) i); last first.
  apply set_nth_default; by rewrite size_tuple.
by rewrite tnth_mktuple.
Qed.

Lemma wH_two_pow p  : p < n -> wH (rV_of_nat n (expn 2 p)) = 1%nat.
Proof.
move=> pn.
rewrite wH_oldE wH_old_wH_b /rV_of_nat /bitseq_F2row /bitseq_to_row /rowF2_tuplebool /=.
rewrite /HammingBitstring.wH /num_occ count_map.
rewrite (eq_count (a2 := pred1 1)); last by move=> ? /=; rewrite eqb_id F2_eq1.
rewrite -sum1_count big_map /=.
rewrite (eq_bigl (pred1 (Ordinal (rev_ord_proof (Ordinal pn))))); last first.
  move=> i /=; symmetry; rewrite -[in X in X = _]val_eqE /=.
  rewrite mxE nat2bin_two_pow // nth_cat size_nseq.
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

End rV_and_nat_prop.

Section cV_and_nat.

Local Open Scope ring_scope.

Definition cV_of_nat (n i : nat) : 'cV['F_2]_n := (rV_of_nat n i)^T.

Definition nat_of_cV n (y : 'cV['F_2]_n) : nat := nat_of_rV y^T.

Lemma nat_of_cV_0 k : nat_of_cV (0 : 'cV_k) = O.
Proof. by rewrite /nat_of_cV trmx0 nat_of_rV_0. Qed.

Lemma nat_of_rV_tr n (y : 'rV_n) : nat_of_rV y = nat_of_cV (y^T).
Proof. by rewrite /nat_of_cV trmxK. Qed.

End cV_and_nat.

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
    split; first by done.
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
    move/K => /= {K}K.
    apply Bool.not_true_is_false.
    by apply/eqP.
  + rewrite add0n.
    case/(IH _ Hsz) => i [[H11 H12] H2].
    exists i.+1%N.
    split; first by done.
    move=> j Hj Hj'.
    destruct j => //=.
    apply H2 => //.
    contradict Hj'; by subst j.
Qed.

Lemma wH_1 n (x : 'rV['F_2]_n) : wH x = 1%nat ->
  exists i : 'I_n, x ``_ i = 1%R /\ (forall j : 'I_n, i <> j -> x ``_ j = 0%R).
Proof.
rewrite wH_oldE wH_old_wH_b.
move/wHb_1.
move/(_ n).
rewrite size_tuple.
case/(_ erefl) => i [] [] H1 H2 H3.
exists (Ordinal H1); split.
  transitivity (F2_of_bool true) => //.
  rewrite -H2 /rowF2_tuplebool (nth_map ord0); last by rewrite size_tuple.
  rewrite (_ : _ _ _ i = (tuple_of_row x) \_ (Ordinal H1)); last first.
    apply set_nth_default; by rewrite size_tuple.
  rewrite tnth_mktuple {1}(F2_0_1 (x ``_ (Ordinal H1))); by case: (x ``_ _ != 0%R).
move=> j Hj.
transitivity (F2_of_bool false) => //.
rewrite -(H3 j) //; last first.
  move=> ?; subst i.
  by apply/Hj/val_inj.
rewrite /rowF2_tuplebool (nth_map ord0); last by rewrite size_tuple.
suff -> : x ``_ j = nth ord0 (tuple_of_row x) j by apply: F2_0_1.
rewrite (_ : _ _ _ j = (tuple_of_row x) \_ j); last by rewrite tnth_mktuple.
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
    split; first by done.
    split.
      split; last by done.
      by apply leq_ltn_trans with n.+1%N.
    split; first by done.
    move=> j Hj Hj' Hjk.
    destruct j => //=.
    apply Hk2 => //.
    contradict Hjk; by rewrite Hjk.
  + rewrite add0n.
    case/(IH _ Hsz) => i [k [[H11 H12] [H21 [H221 H222]]]].
    exists i.+1%N, k.+1%N.
    split; first by done.
    split; first by done.
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
rewrite wH_oldE wH_old_wH_b.
move/wHb_2.
move/(_ n).
rewrite size_tuple.
case/(_ erefl) => i [] k [] [] H1 [] H2 [] [] H3 [] H4 [] H5 H6.
exists (Ordinal H1), (Ordinal H3); split.
  by case.
split.
  transitivity (F2_of_bool true) => //.
  rewrite -H2 /rowF2_tuplebool (nth_map ord0); last by rewrite size_tuple.
  rewrite (_ : _ _ _ i = (tuple_of_row x) \_ (Ordinal H1)); last first.
    apply set_nth_default; by rewrite size_tuple.
  rewrite tnth_mktuple {1}(F2_0_1 (x ``_ (Ordinal H1))); by case: (x ``_ _ != 0%R).
split.
  transitivity (F2_of_bool true) => //.
  rewrite -H4 /rowF2_tuplebool (nth_map ord0); last by rewrite size_tuple.
  rewrite (_ : _ _ _ k = (tuple_of_row x) \_ (Ordinal H3)); last first.
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
rewrite (_ : _ _ _ j = (tuple_of_row x) \_ j); last by rewrite tnth_mktuple.
exact: tnth_nth.
Qed.

Lemma wH_3 : forall n, (3 <= n)%N -> wH (rV_of_nat n 3) = 2%N.
Proof.
case => // [] // [] // [] // n _.
rewrite /wH /num_occ /rV_of_nat.
set tmp := tuple_of_row _.
have -> : tmp = [tuple of rev (1 :: 1 :: nseq n.+1 0)]%R.
  apply eq_from_tnth => i.
  rewrite tnth_mktuple /bitseq_F2row /bitseq_to_row /nat2bin mxE.
  rewrite (tnth_nth 0%R).
  rewrite -(nth_map _ 0%R); last by rewrite size_cat size_nseq /= addn2.
  congr (_ `_ i)%R.
  rewrite /= map_cat /= -!cat_rcons cats0 (_ : 0 :: nseq n 0 = nseq n.+1 0)%R //.
  by rewrite 2!rev_cons nseq_S -cat_rcons cats0 rev_rcons /= rev_nseq map_nseq.
rewrite /=.
set y := _ :: _.
rewrite (_ : y = [:: 1; 1; 0] ++ nseq n 0)%R // rev_cat count_cat /= -(@eq_in_count _ pred0).
  by rewrite count_pred0.
move=> a /=.
rewrite rev_nseq.
by move/mem_nseq/eqP => ->.
Qed.

Lemma wH_7 : forall n, (3 <= n)%N -> wH (rV_of_nat n 7) = 3%N.
Proof.
case => // [] // [] // [] // n _.
rewrite /wH /num_occ /rV_of_nat.
set x := tuple_of_row _.
have -> : x =[tuple of rev (1 :: 1 :: 1 :: nseq n 0)]%R.
  rewrite /x {x}.
  apply eq_from_tnth => i.
  rewrite tnth_mktuple /bitseq_F2row /bitseq_to_row /nat2bin mxE (tnth_nth 0%R).
  rewrite -(nth_map _ ord0); last first.
    rewrite /pad_seqL /=.
    destruct n => //=.
    by rewrite size_cat size_nseq /= addn3.
  congr (_ `_ i)%R.
  rewrite /= !rev_cons /= /pad_seqL /= -addn3 addnK map_cat /= map_nseq /=.
  by rewrite rev_nseq -!cats1 /= -!catA.
rewrite /=.
set y := _ :: _.
rewrite (_ : y = [:: 1; 1; 1] ++ nseq n 0)%R // rev_cat count_cat /=.
rewrite -(@eq_in_count _ pred0) ?count_pred0 //.
move=> a /=.
rewrite rev_nseq.
by move/mem_nseq/eqP => ->.
Qed.

(* TODO: move? *)
Lemma rev7_bin : forall m, (2 < m)%N ->
  rev (N2bitseq (BinNums.Npos (xOs (m - 3) (BinNums.xI 3)))) =
  true :: true :: true :: nseq (m - 3) false.
Proof.
elim=> //.
case=> //.
case=> //.
case=> // m /(_ isT).
rewrite -{1}addn3 -addnBA // subnn addn0 => IH _.
rewrite -{1}addn4 -addnBA //= (_ : 4 - 3 = 1)%nat // addn1 /=.
rewrite rev_cons IH /=.
rewrite -{1}addn3 -addnBA // subnn addn0.
rewrite -cats1.
by rewrite -nseq_S.
Qed.

(* TODO: move? *)
Lemma rev_nat2bin_7 n : (2 < n)%N ->
  rev (nat2bin 7 n) = nat2bin (7 * expn 2 (n - 3)) n.
Proof.
move=>Hn.
rewrite /nat2bin.
rewrite (bin_of_nat_rev7 _ Hn).
rewrite (@bin_of_nat_7 n) //=.
rewrite (rev7_bin Hn) /=.
rewrite {1}/pad_seqL /=.
rewrite Hn.
rewrite rev_cat /=.
rewrite /pad_seqL /=.
rewrite size_nseq.
case: ifP => H //.
  rewrite (_ : n - (n - 3).+3 = 0)%nat //; last first.
  destruct n => //.
  destruct n => //.
  destruct n => //.
  rewrite -addn3.
  by rewrite -(@addnBA n 3 3) // subnn addn0 addn3 subnn.
by rewrite rev_nseq.
exfalso.
move/negbT in H.
rewrite -leqNgt in H.
destruct n => //.
destruct n => //.
destruct n => //.
by rewrite -{2}addn3 -addnBA // subnn addn0 ltnn in H.
Qed.

Lemma wH_7_rev7 n : (2 < n)%N ->
  wH (rV_of_nat n 7) = wH (rV_of_nat n (7 * expn 2 (n - 3))).
Proof.
move=> Hn.
rewrite 2!wH_oldE /wH_old /rV_of_nat.
set lhs := tuple_of_row _.
set rhs := tuple_of_row _.
suff <- : rev lhs = rhs by apply num_occ_rev.
rewrite /lhs /rhs.
rewrite /bitseq_F2row.
rewrite -!bitseq_to_rowK.
rewrite -map_rev.
by rewrite rev_nat2bin_7.
Qed.

End AboutwH123.

(* TODO: move? *)
Require Import Reals Reals_ext Rbigop Rssr.

Local Open Scope R_scope.
Local Open Scope ring_scope.

Lemma hamming_01 m p :
  \rsum_(u in 'rV['F_2]_m| u \in [set v |(1 >= wH v)%nat])
           ((1 - p) ^ (m - wH u) * p ^ wH u)%R =
  ((1 - p) ^ m + INR m * p * (1 - p) ^ (m - 1))%R.
Proof.
rewrite (bigID [pred i | wH i == O]) /=.
rewrite (big_pred1 (0 : 'rV_m)) /=; last first.
  move=> i /=.
  by rewrite !inE -wH_eq0 andb_idl // => /eqP ->.
rewrite wH0 pow_O subn0 mulR1; f_equal.
transitivity (\rsum_(i | wH (i : 'rV['F_2]_m) == 1%nat) ((1 - p) ^ (m - 1) * p ^ 1)%R).
  transitivity (\rsum_(i|(wH (i : 'rV['F_2]_m) == 1)%nat)
      ((1 - p) ^ (m - wH i) * p ^ wH i)%R).
    apply eq_bigl => /= i.
    rewrite !inE.
    case wH_1 : (wH i == 1)%nat.
      move/eqP in wH_1.
      by rewrite wH_1.
    case wH_0 : (wH i) => [|n1].
      by rewrite eqxx.
    rewrite /= andbT.
    case n1_0 : n1 => [|n2].
      by rewrite wH_0 n1_0 in wH_1.
    by [].
  transitivity (\rsum_(i|wH (i : 'rV['F_2]_m) == 1%N) ((1 - p) ^ (m - 1) * p ^ 1)%R).
    by apply eq_bigr => i /= /eqP ->.
  done.
by rewrite big_const iter_Rplus pow_1 /= -(mulRC p) mulRA -cardsE wH_m_card bin1.
Qed.

Lemma binomial_theorem m p :
  (\rsum_(b|b \in [set: 'rV['F_2]_m]) (1 - p) ^ (m - wH b) * p ^ wH b = 1)%R.
Proof.
transitivity (((1 - p) + p) ^ m); last first.
  rewrite addRC (_ : (p + (1 - p) = 1)%R); last by field.
  by rewrite pow1.
rewrite RPascal.
transitivity (\rsum_(b : 'rV['F_2]_m) ((1 - p) ^ (m - wH b) * p ^ wH b)%R).
  apply eq_bigl => /= i; by rewrite inE.
rewrite (classify_big (fun s : 'rV_m => Ordinal (max_wH' s)) (fun x => ((1 - p) ^ (m - x) * p ^ x))%R) /=.
apply eq_bigr => i _.
do 2 f_equal.
rewrite -wH_m_card.
apply eq_card => /= x; by rewrite !inE.
Qed.