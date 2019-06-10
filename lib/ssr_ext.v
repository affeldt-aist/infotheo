(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype finfun fingraph tuple div path bigop prime.
From mathcomp Require Import finset fingroup perm.
Import Coq.NArith.BinNatDef.

(** * Additional lemmas about ssrnat, seq, eqType, finType, finset, tuple, perm *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Notation "t '\_' i" := (tnth t i) (at level 9) : tuple_ext_scope.
Reserved Notation "n .-bseq" (at level 2, format "n .-bseq").

Lemma addb_tri_ine a b c : a (+) b <= (a (+) c) + (c (+) b).
Proof. move: a b c; by case; case; case. Qed.

Section ssrnat_ext.

Lemma nat_of_pos_not_0 : forall p, nat_of_pos p <> O.
Proof.
elim => // p H.
contradict H.
rewrite /= NatTrec.doubleE in H.
apply/eqP; rewrite -double_eq0; by apply/eqP.
Qed.

Lemma nat_of_pos_inj : forall i j, nat_of_pos i = nat_of_pos j -> i = j.
Proof.
elim=> [i Hi [] | i Hi [] | j /=].
- move=> j /= [] /eqP.
  by rewrite !NatTrec.doubleE -!muln2 eqn_mul2r /= => /eqP/Hi ->.
- move=> j /=.
  rewrite !NatTrec.doubleE => Hj.
  have absurd : odd ((nat_of_pos j).*2) by rewrite -Hj /= odd_double.
  by rewrite odd_double in absurd.
- rewrite /= NatTrec.doubleE.
  case => Habsurd.
  exfalso.
  move: (@nat_of_pos_not_0 i).
  by destruct (nat_of_pos i).
- move=> j /=.
  rewrite !NatTrec.doubleE => Hj.
  have absurd : odd ((nat_of_pos i).*2) by rewrite Hj /= odd_double.
  by rewrite odd_double in absurd.
- move=> j /= /eqP.
  by rewrite !NatTrec.doubleE -!muln2 eqn_mul2r /= => /eqP/Hi ->.
- rewrite /= NatTrec.doubleE => absurd.
  exfalso.
  move: (@nat_of_pos_not_0 i).
  by destruct (nat_of_pos i).
  destruct j => //=;
    rewrite NatTrec.doubleE => absurd ;
      exfalso ;
        move: (@nat_of_pos_not_0 j) => H' ;
          by destruct (nat_of_pos j).
Qed.

Lemma bin_of_nat_inj : forall a b, bin_of_nat a = bin_of_nat b -> a = b.
Proof.
move=> a b X.
have : nat_of_bin (bin_of_nat a) = nat_of_bin (bin_of_nat b) by rewrite X.
by rewrite 2!bin_of_natK.
Qed.

Lemma bin_of_nat_nat_of_pos_not_0 : forall i, bin_of_nat (nat_of_pos i) <> 0%num.
Proof.
elim=> // a Ha /=.
rewrite NatTrec.doubleE.
contradict Ha.
by destruct (nat_of_pos a).
Qed.

Lemma bin_of_nat_expn2 m : bin_of_nat (expn 2 m.+1) = BinNat.N.mul 2%num (bin_of_nat (expn 2 m)).
Proof.
set x := BinNat.N.mul _ _.
by rewrite -(nat_of_binK x) {}/x nat_of_mul_bin bin_of_natK expnS.
Qed.

Lemma Nto_natE x : BinNat.N.to_nat x = nat_of_bin x.
Proof.
case x => //=.
elim => [ | | //] p Hp /=.
by rewrite Pnat.Pos2Nat.inj_xI NatTrec.trecE Hp -mul2n.
by rewrite Pnat.Pos2Nat.inj_xO NatTrec.trecE Hp -mul2n.
Qed.

Lemma BinPos_nat_of_P_nat_of_pos : forall i, BinPos.nat_of_P i = nat_of_pos i.
Proof.
elim=> // i /= Hi.
- by rewrite Pnat.nat_of_P_xI NatTrec.doubleE Hi multE mul2n.
- by rewrite Pnat.nat_of_P_xO NatTrec.doubleE Hi multE mul2n.
Qed.

Lemma nat_of_posK k : bin_of_nat (nat_of_pos k) = BinNat.Npos k.
Proof. by rewrite -(nat_of_binK (BinNat.Npos k)). Qed.

End ssrnat_ext.

Definition swap {A B : Type} (ab : A * B) := (ab.2, ab.1).

Lemma injective_swap (A B : finType) (E : {set A * B}) : {in E &, injective swap}.
Proof. by case=> a b [a0 b0] /= _ _ [-> ->]. Qed.

Lemma set_swap (A B : finType) (P : B -> A -> bool) :
  [set h : {: B * A} | P h.1 h.2 ] = swap @: [set h | P h.2 h.1].
Proof.
apply/setP => /= -[b a]; rewrite !inE /=; apply/idP/imsetP => [H|].
- by exists (a, b) => //=; rewrite inE.
- by case=> -[a0 b0]; rewrite inE /= => ? [-> ->].
Qed.

Section seq_ext.

Variables A B : Type.
Implicit Types l : seq A.

Lemma zip_swap : forall l (k : seq B),
  zip l k = map (fun x => (x.2, x.1)) (zip k l).
Proof. elim => [ [] // | h t IH [|hd tl] //=]; by rewrite IH. Qed.

Lemma sumn_big_addn s : sumn s = \sum_ ( i <- s ) i.
Proof.
elim s => [|a l HR] /= ; first by rewrite big_nil.
by rewrite -cat1s big_cat /= big_seq1 HR.
Qed.

Lemma filter_flatten T u (s : seq (seq T)) : filter u (flatten s) = flatten (map (filter u) s).
Proof.
elim s => // hd tl HR.
rewrite -cat1s map_cat !flatten_cat filter_cat -HR.
f_equal ; by rewrite /flatten /= 2!cats0.
Qed.

Lemma drop_take_iota a b c : a <= b <= c ->
  drop a (take b (iota 0 c)) = filter (fun n => a <= n < b) (iota 0 c).
Proof.
move=> /andP [Hab Hbc].
set f := fun n => a <= n < b.
rewrite -(subnKC Hbc) iota_add take_cat size_iota subnn take0 add0n (ltnn b) cats0 filter_cat.
rewrite (_ : filter f (iota b (c-b)) = [::]) ; last first.
  apply/eqP/negPn ; rewrite -has_filter ; apply/hasPn => l.
  rewrite mem_iota (subnKC Hbc) /f negb_and => /andP [H _].
  by rewrite -leqNgt H orbT.
rewrite cats0 -(subnKC Hab) iota_add drop_cat size_iota subnn drop0 add0n (ltnn a) filter_cat.
rewrite (_ : filter f (iota 0 a) = [::]) ; last first.
  apply/eqP/negPn ; rewrite -has_filter ; apply/hasPn => l.
  rewrite mem_iota /f negb_and add0n => /andP [_ H].
  by rewrite -ltnNge H orTb.
rewrite cat0s.
symmetry ; apply/all_filterP/allP.
move=> l.
by rewrite mem_iota /f (subnKC Hab).
Qed.

Lemma take_take : forall (n m :nat) l, take n (take (n + m) l) = take n l.
Proof.
elim=> [* | n0 IH m0 z0].
- by rewrite !take0.
- destruct z0 => //=; by rewrite IH.
Qed.

Lemma take_drop_take : forall m n l,
  m + n <= size l -> take n (drop m (take (m + n) l)) = (drop m (take (m + n) l)).
Proof.
elim=> [n0 z Hsz | m IH n1 [|hd tl] //=].
- rewrite drop0 add0n take_oversize // size_take.
  case: ifP => // {Hsz}.
  move/negbT; by rewrite -leqNgt.
rewrite addnC addnS => ?; by rewrite IH // addnC.
Qed.

Lemma zip_mask : forall bs l (k : seq B),
  zip (mask bs l) (mask bs k) = mask bs (zip l k).
Proof.
elim=> // h t IH [|a1 a2] [|b1 b2] //=.
- destruct h => //=; by case: mask.
- destruct h => //=; by case: mask.
- destruct h => /=; by rewrite IH.
Qed.

Lemma nseq_add n (a : A) m : nseq (n + m) a = nseq n a ++ nseq m a.
Proof. rewrite cat_nseq; elim: n => // n ih; by rewrite addSn /= ih. Qed.

Variable a : A.

Lemma map_nth_iota_id l : map (nth a l) (iota 0 (size l)) = l.
Proof.
apply: (@eq_from_nth _ a); first by rewrite size_map size_iota.
rewrite size_map; move=> i; rewrite size_iota => Hi.
by rewrite (@nth_map _ 0 _ _ _ _ _) // ?size_iota // nth_iota.
Qed.

Lemma nseq_S : forall n, nseq n.+1 a = rcons (nseq n a) a.
Proof. by elim=> //= n <-. Qed.

Lemma rev_nseq : forall n, rev (nseq n a) = nseq n a.
Proof. elim => // n ih; by rewrite /= rev_cons ih -nseq_S. Qed.

Lemma nseq_cat l l' n : l ++ l' = nseq n a -> l' = nseq (n - size l) a.
Proof.
move=> H2; move/(congr1 (drop (size l))) : (H2).
rewrite drop_cat ltnn subnn drop0 => ->.
move: (nseq_add (size l) a (n - size l)).
rewrite subnKC; last by rewrite -(size_nseq n a) -H2 size_cat leq_addr.
move=> ->; by rewrite drop_cat size_nseq ltnn subnn drop0.
Qed.

End seq_ext.

Section Pad.

Variables (A : Type) (a : A).
Implicit Types s t : seq A.

Definition pad_seqR s n :=
  if size s <= n then s ++ nseq (n - size s) a else take n s.

Lemma size_pad_seqR s n : size (pad_seqR s n) = n.
Proof.
rewrite /pad_seqR; case: ifPn; last by rewrite -ltnNge size_take => ->.
by rewrite size_cat size_nseq => /subnKC.
Qed.

Lemma pad_seqR_size s n : size s = n -> pad_seqR s n = s.
Proof. by rewrite /pad_seqR => ->; rewrite leqnn subnn cats0. Qed.

Definition pad_seqL s n :=
  if size s <= n then nseq (n - size s) a ++ s else take n s.

Lemma pad_seqL_inj n s t : size s = n -> size t = n ->
  pad_seqL s n = pad_seqL t n -> s = t.
Proof.
elim: n s t => [[] // [] // | ] n IH [|a' ta] // [|b tb] // [Ha] [Hb].
by rewrite /pad_seqL /= Ha Hb ltnS leqnn subnn.
Qed.

Lemma size_pad_seqL n s : size (pad_seqL s n) = n.
Proof.
rewrite /pad_seqL; case: ifPn; last by rewrite -ltnNge size_take => ->.
by rewrite size_cat size_nseq => /subnK.
Qed.

End Pad.

Section seq_eqType_ext.

Variables A B : eqType.

Lemma take_index (a : A) s : a \notin take (index a s) s.
Proof.
elim: s => // h t IH /=; case: ifPn => //.
by rewrite inE negb_or eq_sym IH andbT.
Qed.

Lemma uniq_take i (s : seq A) :  i < size s -> uniq s -> uniq (take i s).
Proof.
elim: i s => [l _ _ |i IH [| h t] //=]; first by rewrite take0.
rewrite ltnS => nt /andP[ht ut].
rewrite (IH _ nt ut) andbT; apply: contra ht; exact: mem_take.
Qed.

Lemma sorted_of_nth (r : rel A) s (r_trans : transitive r) (r_sorted : sorted r s) :
  forall x0 a b, a < b < size s -> r (nth x0 s a) (nth x0 s b).
Proof.
move=> a0 a b /= /andP [Hab Hbs].
set f := nth a0 s.
have Has : a < size s by exact/(leq_ltn_trans _ Hbs)/ltnW.
have H : subseq [:: f a ; f b] s.
  rewrite -(map_nth_iota_id a0 s) (_ : [:: f a; f b] = map f [:: a ; b]) //.
  apply: map_subseq.
  rewrite -(subnK Has) addnC iota_add add0n (_ : [:: a; b] = [::a] ++ [::b]) //.
  apply cat_subseq; rewrite sub1seq mem_iota.
  - by rewrite add0n leq0n ltnSn.
  - by rewrite Hab subnKC.
by case/andP : (subseq_sorted r_trans H r_sorted).
Qed.

Lemma sorted_cat (l k : seq A) (r : @rel A) :
  sorted r l -> sorted r k ->
  (forall a, a \in l -> forall b, b \in k -> r a b) ->
  sorted r (l ++ k).
Proof.
move=> Hl Hk H.
destruct l => //.
rewrite /sorted /= cat_path.
rewrite /sorted in Hl.
apply/andP; split => //.
destruct k => //.
rewrite /sorted in Hk.
rewrite /= Hk andbC /=.
apply H.
by rewrite mem_last.
by rewrite in_cons eqxx.
Qed.

Lemma sorted_is_flattened leT (Htrans : transitive leT)
  (Hanti : antisymmetric leT) (Hrefl : reflexive leT) :
  forall n (l k : seq A), n = size l -> uniq l -> sorted leT l ->
  sorted leT k -> {subset k <= l} ->
  k = flatten (map (fun elt => filter (pred1 elt) k) l).
Proof.
elim=> [[]// k _ _ _ Hk H|] /=.
  destruct k => //.
  exfalso.
  move: (H s).
  by rewrite !inE eqxx orTb in_nil => /(_ isT).
move=> n0 IH [|hd tl] // v [lst_sz] lst_uniq lst_sorted v_sorted Hincl.
have X1 : v = filter (pred1 hd) v ++ filter (predC (pred1 hd)) v.
  apply eq_sorted with leT => //.
  - apply: sorted_cat.
    + by apply sorted_filter.
    + by apply sorted_filter.
    + move=> a.
      rewrite mem_filter => /andP[/= /eqP ?]; subst hd => av b.
      rewrite mem_filter => /andP[/= ba /Hincl].
      rewrite inE => /orP[|].
      * move/eqP => ?; by subst b.
      * move=> btl.
        rewrite /sorted in lst_sorted.
        move: (@subseq_order_path _ _ (Htrans) a [:: b] tl).
        rewrite /= andbC /=.
        apply => //; by rewrite sub1seq.
  - rewrite perm_sym; by apply permEl, perm_filterC.
rewrite {1}X1 {X1} /=.
congr (_ ++ _).
move: lst_uniq => /= /andP[hdtl tl_uniq].
rewrite (IH tl (filter (predC (pred1 hd)) v) lst_sz tl_uniq).
- congr flatten.
  apply eq_in_map => i i_tl.
  rewrite -filter_predI.
  apply eq_in_filter => j j_v /=.
  case/boolP: (j == i) => ij //=.
  apply/negP => /eqP ?; subst j.
  move/eqP : ij => ?; subst i.
  by rewrite i_tl in hdtl.
- destruct tl => //=.
  by case/andP : lst_sorted.
- exact: sorted_filter.
- move=> i.
  rewrite mem_filter /= => /andP[ihd] /Hincl.
  rewrite inE => /orP[|//]; by rewrite (negbTE ihd).
Qed.

Lemma filter_zip_L m (l : seq A) (k : seq B) a :
  size l = m -> size k = m ->
  filter (fun x => x.1 == a) (zip l k) =
  zip (filter (pred1 a) l) (mask (map (pred1 a) l) k).
Proof.
move=> Hl Hk.
rewrite filter_mask [in RHS]filter_mask zip_mask; congr mask.
elim: m l k Hl Hk a => [[] // [] //|n ih].
move=> [|a1 a2] // [|b1 b2] // [sza2] [szb2] a /=; by rewrite ih.
Qed.

Lemma filter_zip_R m (l : seq A) (k : seq B) b :
  size l = m -> size k = m ->
  filter (fun x => x.2 == b) (zip l k) =
  zip (mask (map (pred1 b) k) l) (filter (pred1 b) k).
Proof.
move=> Hl Hk.
rewrite filter_mask [in RHS]filter_mask zip_mask; congr mask.
elim: m l k Hl Hk b => [[] // [] // | n ih].
move=> [|a1 a2] // [|b1 b2] // [sza2] [szb2] b /=; by rewrite ih.
Qed.

Lemma undup_filter (P : pred B) l : undup (filter P l) = filter P (undup l).
Proof.
elim: l => // h t IH /=; case/boolP : (P h) => /= Ph.
- case/boolP: (h \in t) => ht.
  + by rewrite mem_filter Ph ht.
  + by rewrite mem_filter (negbTE ht) andbF /= Ph IH.
- rewrite IH; case: ifPn => //= ?; by rewrite (negbTE Ph).
Qed.

Lemma undup_perm (f : A -> B) p h t : undup (map f p) = h :: t ->
  exists p1 : seq A, exists p2 : seq A,
    perm_eq p (p1 ++ p2) /\ undup (map f p1) = [:: h] /\ undup (map f p2) = t.
Proof.
move=> p_t; exists (filter (preim f (pred1 h)) p), (filter (preim f (mem t)) p).
split.
- apply/permPl => x; rewrite -(perm_filterC (preim f (pred1 h)) p).
  apply/permPl : x.
  rewrite perm_cat2l (@eq_in_filter _ _ [pred x | f x \in t]) //= => x X.
  case/boolP: (f x == h) => [/eqP ->|/negbTE fxh] /=; apply/esym.
  + by have /andP[/negbTE] : uniq (h :: t) by rewrite -p_t; apply undup_uniq.
  + have : f x \in h :: t by rewrite -p_t mem_undup; apply/mapP; exists x.
    rewrite in_cons => /orP[|->//]; by rewrite fxh.
- split.
  + rewrite -filter_map undup_filter p_t /= eqxx; congr cons.
    rewrite -(filter_pred0 t); apply eq_in_filter => i it /=.
    apply/negP => /eqP X; subst h.
    have : uniq (i :: t) by rewrite -p_t; exact: undup_uniq.
    rewrite /= => /andP[]; by rewrite it.
  + rewrite -filter_map undup_filter p_t /= ifF; last first.
      apply/negP => X.
      have : uniq (h :: t) by rewrite -p_t undup_uniq.
      by rewrite /= X.
    rewrite -[RHS](filter_predT t); exact: eq_in_filter.
Qed.

End seq_eqType_ext.

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

Lemma addb_seq_cat a b c d : size a = size c ->
  addb_seq (a ++ b) (c ++ d) = addb_seq a c ++ addb_seq b d.
Proof. move=> a_c; by rewrite /addb_seq /= -map_cat zip_cat. Qed.

Lemma addb_seq_map A : forall n (a b : seq A) f,
  size a = n -> size b = n ->
  addb_seq (map f a) (map f b) = map (fun x => f x.1 (+) f x.2) (zip a b).
Proof.
elim => [[] // [] //| n IH [|ha ta] // [|hb tb] //= f [Ha] [Hb]].
by rewrite /addb_seq /= -IH.
Qed.

Lemma ord1 (i : 'I_1) : i = ord0. Proof. case: i => [[]] // ?; exact/eqP. Qed.

Lemma ord2 (i : 'I_2) : (i == ord0) || (i == Ordinal (erefl (1 < 2))).
Proof. by case: i => -[|[|]]. Qed.

Lemma ord3 (i : 'I_3) :
  [|| i == ord0, i == Ordinal (erefl (1 < 3)) | i == Ordinal (erefl (2 < 3))].
Proof. by case: i => -[|[|[|]]]. Qed.

Lemma enum_inord (m : nat) : enum 'I_m.+1 = [seq inord i | i <- iota 0 m.+1].
Proof.
rewrite -val_enum_ord -map_comp.
transitivity ([seq i | i <- enum 'I_m.+1]); first by rewrite map_id.
apply eq_map => i /=; by rewrite inord_val.
Qed.

Lemma inj_card (A B : finType) (f : {ffun A -> B}) :
  injective f -> #| A | <= #| B |.
Proof. move=> Hf; by rewrite -(@card_imset _ _ f) // max_card. Qed.

Section finset_ext.
Implicit Types A B : finType.

Lemma setDUKl A (E F : {set A}) : (E :|: F) :\: E = F :\: E.
Proof. by rewrite setDUl setDv set0U. Qed.

Lemma setU_setUD A (E F : {set A}) : E :|: F = F :|: E :\: F.
Proof.
apply/setP => a; rewrite !inE; apply/orP/orP => -[->|H] ; [
  by rewrite andbT; apply/orP; rewrite orbN | by left |
  by right | case/andP : H => _ ->; by left ].
Qed.

Lemma seq_index_enum_card A : forall s (E : {set A}) a,
  s =i enum E -> uniq s -> a \in E -> index a s < #| E |.
Proof.
elim => [E a _ _ aE| h t IH E a htE uniqht aE /=].
  exact: enum_rank_subproof aE.
case: ifPn => [_|hi]; first by rewrite card_gt0; apply/set0Pn; exists a.
apply (@leq_ltn_trans #|E :\ h|); last first.
  by rewrite (cardsD1 h E) -mem_enum -htE mem_head add1n.
apply IH.
- move=> j; case/boolP : (j \in enum (E :\ h)).
  + rewrite mem_enum in_setD1 => /andP[/negbTE H].
    by rewrite -mem_enum -htE in_cons H.
  + rewrite mem_enum in_setD1 negb_and negbK => /orP[/eqP ->{j}|].
    - by move: uniqht => /= /andP[/negbTE].
    - by rewrite -mem_enum -htE inE negb_or => /andP[_ /negbTE].
- move: uniqht; by case/andP.
- apply/setD1P; by rewrite eq_sym.
Qed.

Lemma setX1 A B (a : A) (b : B) : setX [set a] [set b] = [set (a, b)].
Proof. by apply/setP => -[a0 b0]; rewrite !inE /= xpair_eqE. Qed.

Lemma bigcup_setX A B n (E : 'I_n -> {set A}) (F : {set B}) :
  \bigcup_(i < n) setX F (E i) = setX F (\bigcup_(i < n) (E i)).
Proof.
apply/setP => -[b a] /=; rewrite !inE /=.
apply/bigcupP/andP => [[/= i _]|[K1] /bigcupP[/= i _ aEi]].
  rewrite !inE /= => /andP[xb yai]; rewrite xb; split => //.
  by apply/bigcupP; exists i.
by exists i => //; rewrite !inE /= K1.
Qed.

Lemma cardsltn1P A (E : {set A}) :
  (1 < #| E |) = [exists a, exists b, (a \in E) && (b \in E) && (a != b)].
Proof.
case/boolP : (E == set0) => [/eqP -> | /set0Pn [] /= a Ha].
  rewrite cards0; apply/esym/negbTE.
  rewrite negb_exists; apply/forallP => a.
  rewrite negb_exists; apply/forallP => b; by rewrite !inE.
case/boolP : (E :\ a == set0) => [/eqP Ea0 | ].
  have -> : E = [set a] by apply/eqP; rewrite -(setD1K Ha) Ea0 setU0.
  rewrite cards1; apply/esym/negbTE.
  rewrite negb_exists; apply/forallP => b.
  rewrite negb_exists; apply/forallP => c.
  rewrite 2!in_set1 2!negb_and negbK.
  case/boolP : (b == c) => [_|bc]; first by rewrite orbT.
  rewrite orbF.
  case/boolP : (b == a) => //= /eqP <-; by rewrite eq_sym.
case/set0Pn => b Hb.
have -> : 1 < #| E | by rewrite (cardsD1 a E) Ha /= (cardsD1 b (E :\ a)) Hb.
apply/esym; apply/existsP; exists a; apply/existsP; exists b.
rewrite !inE eq_sym andbC in Hb.
by rewrite -andbA Hb andbT.
Qed.

Lemma set1_set2 A (E : {set A}) a :
  a \in E -> E != set1 a -> exists i, (i \in E) && (i != a).
Proof.
move/setD1K => aC Ca.
have /set0Pn[b] : E :\ a != set0.
  apply: contra Ca; rewrite setD_eq0 subset1 => /orP[//|].
  by rewrite -aC => /eqP/setP/(_ a); rewrite !inE eqxx.
rewrite !inE => /andP[ba bC]; exists b; by rewrite bC.
Qed.

Lemma set2_set1 A (E : {set A}) a :
  (exists i, (i \in E) && (i != a)) -> E != set1 a.
Proof.
case=> b /andP[bC]; apply: contra => /eqP Ca; move: bC; by rewrite Ca !inE.
Qed.

End finset_ext.

Module Set2.
Section set2.

Variable X : finType.
Hypothesis HX : #|X| = 2%nat.

Definition a := enum_val (cast_ord (esym HX) ord0).
Definition b := enum_val (cast_ord (esym HX) (lift ord0 ord0)).

Lemma enumE : enum X = a :: b :: [::].
Proof.
apply (@eq_from_nth _ a); first by rewrite -cardE HX.
case=> [_|]; first by rewrite [X in _ = X]/= {2}/a (enum_val_nth a).
case=> [_ |i]; last by rewrite -cardE HX.
by rewrite [X in _ = X]/= {1}/b (enum_val_nth a).
Qed.

Lemma a_neq_b : a != b.
Proof. rewrite /a /b. apply/eqP. by move/enum_val_inj. Qed.

Lemma neq_a_b x : x != a -> x == b.
Proof. have : x \in X by []. by rewrite -mem_enum enumE !inE => /orP[->|]. Qed.

Lemma ind (C : X -> Type) : C a -> C b -> forall a, C a.
Proof.
move=> H1 H2 c; by case/boolP : (c == a) => [/eqP -> //|/neq_a_b/eqP ->].
Qed.

End set2.
End Set2.

Section tuple_ext.

Variable A : Type.

Local Open Scope tuple_ext_scope.

Lemma tcast2tval m n (H : m = n) :
  forall (v : m.-tuple A) (w : n.-tuple A), tcast H v = w -> tval v = tval w.
Proof. subst n. by move=> [v Hv] [w Hw] <- /=. Qed.

Lemma tcast_take_inj n m k (H : minn n k = m) (nk : n = k) (t v : k.-tuple A) :
  tcast H [tuple of take n t] = tcast H [tuple of take n v] -> t = v.
Proof.
subst m n => /=.
case => /= tv.
apply eq_from_tnth => i.
rewrite (tnth_nth t\_i) [in X in _ = X](tnth_nth t\_i).
by rewrite -(@nth_take k) // -[in X in _ = X](@nth_take k) // tv.
Qed.

Lemma eq_tcast n (t : n.-tuple A) m (v : m.-tuple A) (H : m = n) :
  tval t = tval v -> t = tcast H v.
Proof. subst m; rewrite tcast_id => tt'; exact: val_inj. Qed.

Lemma eq_tcast2 n (t : seq A) m (v : m.-tuple A) (H : m = n) :
  t = tval v -> t = tval (tcast H v).
Proof. subst m. by rewrite tcast_id. Qed.

Lemma tnth_zip_1 (B : finType) n (x1 : n.-tuple A) (x2 : n.-tuple B) i:
  (tnth [tuple of zip x1 x2] i).1 = tnth x1 i.
Proof.
rewrite /tnth; set def := tnth_default _ _; case: def => ? ?.
rewrite nth_zip /=; last by rewrite !size_tuple.
apply set_nth_default; by rewrite size_tuple.
Qed.

Lemma tnth_zip_2 (B : finType) n (x1 : n.-tuple A) (x2 : n.-tuple B) i:
  (tnth [tuple of zip x1 x2] i).2 = tnth x2 i.
Proof.
rewrite /tnth; set def := tnth_default _ _; case: def => ? ?.
rewrite nth_zip /=; last by rewrite !size_tuple.
apply set_nth_default; by rewrite size_tuple.
Qed.

Lemma thead_tuple1 : forall (i : 1.-tuple A), [tuple thead i] = i.
Proof. move=> [ [|h []] H] //. by apply val_inj. Qed.

Definition tbehead n (t : n.+1.-tuple A) : n.-tuple A := [tuple of behead t].

Lemma sorted_of_tnth {C : eqType} (r : rel C) k (t : k.-tuple C) :
  transitive r -> sorted r t -> forall a b : 'I_k, a < b -> r (t \_ a) (t \_ b).
Proof.
move=> r_trans r_sorted a b ab.
rewrite (tnth_nth t\_b) {2}(tnth_nth t\_b).
apply sorted_of_nth => //; by rewrite ab size_tuple /=.
Qed.

Lemma sorted_of_tnth_leq (X : finType) (n : nat) (r : rel X) (t : n.-tuple X)
  (r_trans : transitive r) (r_refl : reflexive r) (Hx : sorted r t) :
  forall (l p : 'I_n), l <= p -> r t\_l t\_p.
Proof.
move=> l p leqlp.
case/boolP : (l == p) => Hcase.
- move/eqP in Hcase; rewrite Hcase; apply r_refl.
- apply sorted_of_tnth => //; by rewrite ltn_neqAle leqlp Hcase.
Qed.

Definition sort_tuple (X : eqType) n (r : rel X) (t : n.-tuple X) : n.-tuple X.
apply Tuple with (sort r t).
by rewrite size_sort size_tuple.
Defined.

End tuple_ext.

Section bseq_def.

Variables (n : nat) (T : Type).

Structure bseq_of : Type := Bseq {bseqval :> seq T; _ : size bseqval <= n}.

Lemma bseqval_inj : injective bseqval.
Proof.
move=> [a Ha] [b Hb] /= H.
move: Ha Hb; rewrite H => Ha Hb.
congr Bseq; exact: eq_irrelevance.
Qed.

Canonical bseq_subType := Eval hnf in [subType for bseqval].

End bseq_def.

Notation "n .-bseq" := (bseq_of n) : type_scope.

Program Definition bseq0 n T : n.-bseq T := @Bseq n T [::] _.

Definition bseq_of_tuple n T (t : seq T) : n.-bseq T :=
  match Bool.bool_dec (size t <= n) true with
    left H => Bseq H | right _ => @bseq0 n T
  end.

Lemma size_bseq n T (bs : n.-bseq T) : size bs <= n.
Proof. by case: bs. Qed.

Lemma rcons_bseqP n T (t : n.-bseq T) x : size (rcons t x) <= n.+1.
Proof. by rewrite size_rcons ltnS size_bseq. Qed.
Canonical rcons_bseq n T (t : n.-bseq T) x := Bseq (rcons_bseqP t x).

Definition bseq n T (t : n.-bseq T) mkT : bseq_of n T :=
  mkT (let: Bseq _ tP := t return size t <= n in tP).

Notation "[ 'bseq' 'of' s ]" := (@bseq _ _ _ (fun sP => @Bseq _ _ s sP))
  (at level 0, format "[ 'bseq'  'of'  s ]") : type_scope.

Section bseq_structures.

Variable n : nat.

Definition bseq_eqMixin (T : eqType) := Eval hnf in [eqMixin of n.-bseq T by <:].
Canonical bseq_eqType (T : eqType) := Eval hnf in EqType (n.-bseq T) (bseq_eqMixin T).
Canonical bseq_predType (T : eqType) :=
  Eval hnf in PredType (fun t : n.-bseq T => mem_seq t). (* TODO: warning *)
Definition bseq_choiceMixin (T : choiceType) := [choiceMixin of n.-bseq T by <:].
Canonical bseq_choiceType (T : choiceType) :=
  Eval hnf in ChoiceType (n.-bseq T) (bseq_choiceMixin T).
Definition bseq_countMixin (T : countType) := [countMixin of n.-bseq T by <:].
Canonical bseq_countType (T : countType) :=
  Eval hnf in CountType (n.-bseq T) (bseq_countMixin T).
Canonical bseq_subCountType (T : countType) := Eval hnf in [subCountType of n.-bseq T].

Definition bseq_enum (T : finType) : seq (n.-bseq T) :=
  flatten (map (fun m => map (@bseq_of_tuple n _) (map (@tval _ _) (enum {: m.-tuple T})))
               (iota 0 n.+1)).

Lemma bseq_of_tuple_inj T m (mn : m <= n) :
  injective (bseq_of_tuple n (T:=T) \o @tval m T).
Proof.
move=> /= [a Ha] [b Hb] /=.
rewrite /bseq_of_tuple.
case: Bool.bool_dec; last by rewrite (eqP Ha) mn.
move=> Ha'.
case: Bool.bool_dec => [Hb'|]; last by rewrite (eqP Hb) mn.
case => ?; subst a.
congr Tuple; exact: eq_irrelevance.
Qed.

Lemma bseq_enumP T : Finite.axiom (bseq_enum T).
Proof.
case=> s sn.
rewrite count_flatten -[in iota _ _](subnKC sn) -addnS iota_add !map_cat.
rewrite sumn_cat add0n /= addnCA -sumn_cat -!map_cat count_uniq_mem; last first.
  rewrite -map_comp map_inj_uniq //; by [rewrite enum_uniq | exact: bseq_of_tuple_inj].
rewrite -map_comp (_ : _ \in _); last first.
  apply/mapP => /=.
  exists (in_tuple s); first by rewrite mem_enum inE.
  rewrite /bseq_of_tuple.
  case: Bool.bool_dec; last by rewrite size_tuple sn.
  move=> sn'; congr Bseq; exact: eq_irrelevance.
rewrite add1n; congr S; apply/eqP/natnseq0P/all_pred1P/allP => /= m.
rewrite -map_comp; case/mapP => /= l Hl ->.
move: Hl; rewrite mem_cat => /orP[|].
  rewrite mem_iota add0n leq0n /= => ls.
  apply/eqP/count_memPn/mapP => /= -[s' /mapP[t' _ ->]].
  rewrite /bseq_of_tuple.
  case: Bool.bool_dec => ln; case => ?; subst s.
  by rewrite size_tuple ltnn in ls.
  by rewrite ltn0 in ls.
rewrite mem_iota => /andP[sl].
rewrite addSn subnKC // ltnS => ln.
apply/eqP/count_memPn/mapP => /= -[s' /mapP[t' _ ->]].
rewrite /bseq_of_tuple.
case: Bool.bool_dec; last by rewrite size_tuple ln.
move=> _ln'; case => ?; subst s.
by rewrite size_tuple ltnn in sl.
Qed.

Canonical bseq_finMixin (T : finType) := Eval hnf in FinMixin (@bseq_enumP T).
Canonical bseq_finType (T : finType) := Eval hnf in FinType (n.-bseq T) (bseq_finMixin T).
Canonical bseq_subFinType (T: finType) := Eval hnf in [subFinType of n.-bseq T].

End bseq_structures.

Section bseq_lemmas.

Variables (n : nat) (T : Type).

Lemma leq_take (s : seq T) k : size s <= n -> size (take k s) <= n.
Proof.
by move=> sn; rewrite size_take; case: ifPn => // ks; rewrite (leq_trans _ sn) // ltnW.
Qed.

Definition bseq_take (t : n.-bseq T) k : n.-bseq T := Bseq (leq_take k (size_bseq t)).

End bseq_lemmas.

Section ordered_ranks.

Variable X : finType.

Definition le_rank (x y : X) := enum_rank x <= enum_rank y.

Definition lt_rank x y := le_rank x y && (x != y).

Lemma lt_rank_alt x y : lt_rank x y = (enum_rank x < enum_rank y).
Proof.
rewrite /lt_rank /le_rank ltn_neqAle andbC; apply andb_id2r => _.
case/boolP : (x == y) => [/eqP ->|xy]; first by rewrite eqxx.
apply/esym => /=; apply: contra xy => /eqP H.
by apply/eqP/enum_rank_inj/ord_inj.
Qed.

Lemma le_rank_trans : transitive le_rank.
Proof. rewrite /le_rank /transitive => a b c /leq_trans; by apply. Qed.

Lemma le_rank_refl : reflexive le_rank.
Proof. by rewrite /le_rank /reflexive => a. Qed.

Lemma le_rank_asym : antisymmetric le_rank.
Proof. move=> a b H; apply enum_rank_inj; rewrite -eqn_leq in H; exact/eqP. Qed.

Lemma le_rank_total : total le_rank.
Proof. by rewrite /total => a b; rewrite /le_rank leq_total. Qed.

Lemma lt_le_rank_trans u v w : lt_rank u v -> le_rank v w -> lt_rank u w.
Proof.
rewrite /lt_rank => /andP [uv H] vw.
rewrite (le_rank_trans uv vw) /=; apply: contra H => /eqP ?.
subst w; by rewrite (@le_rank_asym u v) // uv.
Qed.

Lemma le_lt_rank_trans u v w : le_rank u v -> lt_rank v w -> lt_rank u w.
Proof.
rewrite /lt_rank => uv /andP[vw H].
rewrite (le_rank_trans uv vw) /=; apply: contra H => /eqP ?.
subst w. by rewrite (@le_rank_asym u v) // uv.
Qed.

Lemma lt_le_rank_weak u v : lt_rank u v -> le_rank u v.
Proof. by rewrite /lt_rank => /andP [H _]. Qed.

Lemma lt_neq_rank u v : lt_rank u v -> u != v.
Proof. by rewrite /lt_rank => /andP [_ H]. Qed.

Lemma sorted_enum : sorted le_rank (enum X).
Proof.
rewrite /sorted.
move HX : (enum X) => Alst.
destruct Alst => //.
apply/(pathP s) => i Hi.
rewrite /le_rank -HX.
destruct Alst => //.
have iA : i < #|X| by rewrite cardE HX (ltn_trans Hi).
rewrite -(@enum_val_nth X (xpredT) s (Ordinal iA)).
have i1A : i.+1 < #|X| by rewrite cardE HX (leq_ltn_trans Hi).
have -> : (nth s (s0 :: Alst) i) = (nth s (enum X) i.+1) by rewrite /= HX.
by rewrite -(@enum_val_nth X (xpredT) s (Ordinal i1A)) 2!enum_valK leqnSn.
Qed.

End ordered_ranks.

Section perm_tuples.

Local Open Scope tuple_ext_scope.

Variables (A : eqType) (n : nat) (s : 'S_n).

Definition perm_tuple (t : n.-tuple A) := [tuple (t \_ (s i)) | i < n].

End perm_tuples.

Section perm_tuples_prop.

Lemma tuple_exist_perm_sort (T : eqType) n (r : rel T) (t : n.-tuple T) :
  exists s : 'S_n, t = perm_tuple s (sort_tuple r t).
Proof.
rewrite /perm_tuple.
have : perm_eq t (sort_tuple r t) by rewrite perm_sym perm_sort perm_refl.
case/tuple_permP => u Hu; exists u.
case: t Hu => t /= Ht Hu.
apply eq_from_tnth => i /=.
rewrite /tnth /= -Hu.
apply: set_nth_default.
move/eqP : {Hu}Ht => ->; by case: i.
Qed.

Variable A : finType.

Lemma perm_tuple_id n (t : n.-tuple A) : perm_tuple 1 t = t.
Proof.
apply eq_from_tnth => i.
by rewrite /perm_tuple /= tnth_map /= perm1 tnth_ord_tuple.
Qed.

Definition perm_tuple_set n (s : 'S_n) (E : {set n.-tuple A}) :=
  perm_tuple s @: E.

Lemma perm_tuple_comp n (s1 s2 : 'S_n) (t : n.-tuple A) :
  perm_tuple s1 (perm_tuple s2 t) = perm_tuple (s1 * s2) t.
Proof.
apply eq_from_tnth => i.
by rewrite /perm_tuple !tnth_map /= tnth_ord_tuple permM.
Qed.

Lemma perm_tuple_inj n (s : 'S_n) : injective (@perm_tuple A n s).
Proof.
move=> a b H.
have : perm_tuple 1 a = perm_tuple 1 b by rewrite -(mulVg s) -!perm_tuple_comp H.
rewrite !perm_tuple_id; apply.
Qed.

Lemma perm_tuple0 (u : 'S_0) (t : 0.-tuple A) : perm_tuple u t = t.
Proof.
rewrite (tuple0 t) (_ : u = 1%g) ?perm_tuple_id //; by apply/permP => /=; case.
Qed.

Lemma zip_perm_tuple (B : finType) n (a : n.-tuple A) (b : n.-tuple B) (s : 'S_n) :
  zip_tuple (perm_tuple s a) (perm_tuple s b) = perm_tuple s (zip_tuple a b).
Proof.
apply eq_from_tnth; case.
destruct n as [|n] => //.
case=> [Hi | i Hi].
  rewrite (tnth_nth (thead a, thead b)) (tnth_nth (thead (zip_tuple a b))).
  rewrite /= enum_ordS /= (tnth_nth (thead a, thead b)) /= nth_zip; last first.
    by rewrite (size_tuple a) (size_tuple b).
  by rewrite (tnth_nth (thead a)) /= (tnth_nth (thead b)).
rewrite (tnth_nth (thead a, thead b)) (tnth_nth (thead (zip_tuple a b))) /=.
rewrite enum_ordS /= nth_zip; last by rewrite 4!size_map size_enum_ord.
rewrite [in RHS](nth_map ord0); last by rewrite size_map size_enum_ord.
rewrite [in RHS](tnth_nth (thead a, thead b)) [in RHS]/zip_tuple /=.
rewrite [in RHS]nth_zip; last by rewrite (size_tuple a) (size_tuple b).
rewrite (nth_map ord0); last by rewrite size_map size_enum_ord.
rewrite (nth_map ord0); last by rewrite size_map size_enum_ord.
by rewrite (tnth_nth (thead a)) (tnth_nth (thead b)).
Qed.

End perm_tuples_prop.

Section perm_enum.
Variable n : nat.

Lemma perm_eq_perm (pe : 'S_n) :
  perm_eq (enum 'I_n) [seq pe i | i <- enum 'I_n].
Proof.
apply uniq_perm.
+ by rewrite enum_uniq.
+ rewrite map_inj_in_uniq ?enum_uniq //.
  by move=> x1 x2 _ _; apply perm_inj.
move=> i.
rewrite mem_enum inE.
symmetry.
apply/mapP.
exists (perm_inv pe i).
  by rewrite mem_enum inE.
by rewrite permKV.
Qed.

Lemma perm_filter_enum_ord j :
  perm_eq [seq i <- enum 'I_n.+1 | i != j]
          [seq lift j i | i <- enum 'I_n].
Proof.
apply uniq_perm.
+ by rewrite filter_uniq // enum_uniq.
+ rewrite map_inj_in_uniq ?enum_uniq //.
  by move=> x1 x2 _ _; apply lift_inj.
move=> k.
rewrite mem_filter mem_enum andbT.
symmetry.
case: (unliftP j k) => /= [a|] ->.
  rewrite eq_sym neq_lift.
  rewrite mem_map. by rewrite mem_enum inE.
  by apply: lift_inj.
rewrite eqxx.
apply/mapP => /= -[x Hx].
move/(f_equal (@nat_of_ord _)).
by apply/eqP/neq_lift.
Qed.
End perm_enum.

Lemma connect_sym1 (D : finType) (r : rel D) : symmetric r ->
  forall x y, connect r x y -> connect r y x.
Proof.
move=> rs x y; case/boolP : (x == y) => [/eqP ->//|xy].
case/connectP => s H1 H2; apply/connectP.
elim/last_ind : s H1 H2 => [|h t _ H1 H2].
  rewrite /= => _ ?; subst y; by rewrite eqxx in xy.
rewrite last_rcons in H2; subst t.
move: H1; rewrite rcons_path => /andP[H1 H2].
exists (rcons (rev h) x); last by rewrite last_rcons.
apply/(pathP x) => i.
rewrite size_rcons ltnS leq_eqVlt size_rev.
case/orP => [/eqP|] Hi.
  case: h => [|h t] in H1 H2 Hi *.
    rewrite /= in H2; by rewrite Hi /= rs.
  rewrite Hi nth_rcons size_rev ltnn eqxx /= nth_rcons size_rev /= ltnS leqnn.
  rewrite nth_rev // subnn rs /=; by case/andP : H1.
rewrite nth_rcons size_rev Hi -cat1s -cats1 catA cats1.
rewrite nth_rcons /= size_rev ltnS (ltnW Hi) nth_rev // -cat1s nth_cat /=.
case: ifPn.
  rewrite ltnS leqn0 => /eqP -> /=; by rewrite subn1 nth_last rs.
rewrite -leqNgt => i0.
rewrite subn1 /= rs nth_rev ?(leq_ltn_trans _ Hi) // ?leq_pred // prednK //.
move/pathP : H1 => /(_ x (size h - i)).
rewrite -cat1s nth_cat /= ifF; last first.
  apply/negbTE; by rewrite -leqNgt subn_gt0 (leq_trans _ Hi).
rewrite -subnDA addn1; apply.
by rewrite -{2}(subn0 (size h)) ltn_sub2l // (leq_trans _ Hi).
Qed.

Lemma connect_sym (D : finType) (r : rel D) : symmetric r -> connect_sym r.
Proof.
move=> ?; rewrite /connect_sym => ? ?; apply/idP/idP => /connect_sym1; exact.
Qed.
