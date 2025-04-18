(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp Require Import mathcomp_extra.
Import Coq.NArith.BinNatDef.

(**md**************************************************************************)
(* # Additional lemmas about ssrnat, seq, eqType, finType, finset, tuple, etc.*)
(******************************************************************************)

Declare Scope tuple_ext_scope.
Declare Scope vec_ext_scope.

Notation "t '!_' i" := (tnth t i) (at level 9) : tuple_ext_scope.
Reserved Notation "A `* B"  (at level 46, left associativity).
Reserved Notation "A :+: B" (at level 52, left associativity).

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma compfid A B (f : A -> B) : f \o idfun = f. Proof. by []. Qed.

Section ssrbool_ext.

Lemma addb_tri_ine (a b c : bool) : a (+) b <= (a (+) c) + (c (+) b).
Proof. move: a b c; by case; case; case. Qed.

End ssrbool_ext.

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

Section Flatten.
Variables (A B : eqType) (f : A -> seq B).

Lemma flatten_single x l :
  uniq l -> x \in l -> (forall y, y \in l -> y != x -> f y = [::]) ->
  flatten (map f l) = f x.
Proof.
elim: l => [|a l IH] //= /andP [Hal Hun] Hx Hy.
move: Hx.
rewrite in_cons => /orP [/eqP|] Hx.
  suff ->: flatten (map f l) = [::].
    by rewrite cats0 Hx.
  apply/nilP; rewrite /nilp size_flatten sumnE !big_map big_seq big1 //.
  move=> i Hi; apply/eqP/nilP/Hy.
  - by rewrite in_cons Hi orbT.
  - by subst x; apply: contra Hal => /eqP <-.
rewrite Hy //=.
- apply IH => // y Hyl; apply Hy.
  by rewrite in_cons Hyl orbT.
- by apply mem_head.
- by apply: contra Hal => /eqP ->.
Qed.

Lemma uniq_flatten_map x y l :
  has (mem (f x)) (f y) ->
  uniq (flatten (map f l)) -> x \in l -> y \in l -> x = y.
Proof.
move/hasP => [b Hby Hbx].
elim: l => // a l IH.
rewrite !in_cons /= cat_uniq => /andP/proj2/andP[Hun1 Hun2] /orP[] Hx /orP[] Hy.
- by rewrite (eqP Hx) (eqP Hy).
- move/hasP: Hun1; elim.
  exists b.
    apply/flattenP.
    by exists (f y) => //; exact/map_f.
  by rewrite -(eqP Hx).
- move/hasP: Hun1; elim.
  exists b.
    apply/flattenP.
    by exists (f x) => //; exact/map_f.
  by rewrite -(eqP Hy).
- by apply IH.
Qed.

Lemma subseq_flatten (f' : A -> seq B) l :
  (forall x, x \in l -> subseq (f x) (f' x)) ->
  subseq (flatten (map f l)) (flatten (map f' l)).
Proof.
elim: l => [|a l IH] //= Hl.
rewrite cat_subseq //.
  by apply Hl; rewrite in_cons eqxx.
by apply IH => x Hx; apply Hl; rewrite in_cons Hx orbT.
Qed.

End Flatten.

Section seq_ext.
Variables A B : Type.
Implicit Types l : seq A.

Lemma zip_swap : forall l (k : seq B),
  zip l k = map swap (zip k l).
Proof. elim => [ [] // | h t IH [|hd tl] //=]; by rewrite IH. Qed.

Lemma sumn_big_addn s : sumn s = \sum_ ( i <- s ) i.
Proof.
elim s => [|a l HR] /= ; first by rewrite big_nil.
by rewrite -cat1s big_cat /= big_seq1 HR.
Qed.

Lemma count_sumn (p : B -> bool) (l : seq B) :
  sumn (map (nat_of_bool \o p) l) = count p l.
Proof.
elim: l => [|a l IH] //=.
by rewrite IH.
Qed.

Lemma drop_take_iota a b c : a <= b <= c ->
  drop a (take b (iota 0 c)) = [seq n <- iota 0 c | a <= n < b].
Proof.
move=> /andP[ab bc].
set f := fun n => a <= n < b.
rewrite -(subnKC bc) iotaD take_cat size_iota subnn take0 add0n (ltnn b) cats0 filter_cat.
rewrite (_ : filter f (iota b (c-b)) = [::]) ; last first.
  apply/eqP/negPn ; rewrite -has_filter ; apply/hasPn => l.
  rewrite mem_iota (subnKC bc) /f negb_and => /andP [bl _].
  by rewrite -leqNgt bl orbT.
rewrite cats0 -(subnKC ab) iotaD drop_cat size_iota subnn drop0 add0n (ltnn a) filter_cat.
rewrite (_ : filter f (iota 0 a) = [::]) ; last first.
  apply/eqP/negPn ; rewrite -has_filter ; apply/hasPn => l.
  rewrite mem_iota /f negb_and add0n => /andP [_ H].
  by rewrite -ltnNge H orTb.
rewrite cat0s.
apply/esym/all_filterP/allP => l.
by rewrite mem_iota /f (subnKC ab).
Qed.

Lemma zip_mask : forall bs l (k : seq B),
  zip (mask bs l) (mask bs k) = mask bs (zip l k).
Proof.
elim=> // h t IH [|a1 a2] [|b1 b2] //=.
- destruct h => //=; by case: mask.
- destruct h => //=; by case: mask.
- destruct h => /=; by rewrite IH.
Qed.

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
move=> ll'na; move/(congr1 (drop (size l))) : (ll'na).
rewrite drop_cat ltnn subnn drop0 => ->.
have := nseqD (size l) (n - size l) a.
rewrite subnKC; last by rewrite -(size_nseq n a) -ll'na size_cat leq_addr.
by move=> ->; rewrite drop_cat size_nseq ltnn subnn drop0.
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

Lemma eq_in_map_seqs {A B : eqType} (f1 f2 : A -> B) l1 l2 :
  l1 = l2 -> {in l1, f1 =1 f2} -> map f1 l1 = map f2 l2.
Proof. by move=> <-; apply eq_in_map. Qed.

Variables A B : eqType.

Lemma take_index (a : A) s : a \notin take (index a s) s.
Proof.
elim: s => // h t IH /=; case: ifPn => //.
by rewrite inE negb_or eq_sym IH andbT.
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
  rewrite -(subnK Has) addnC iotaD add0n (_ : [:: a; b] = [::a] ++ [::b]) //.
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
  apply: (@sorted_eq _ leT) => //.
  - apply: sorted_cat.
    + exact: sorted_filter.
    + exact: sorted_filter.
    + move=> a.
      rewrite mem_filter => /andP[/= /eqP ?]; subst hd => av b.
      rewrite mem_filter => /andP[/= ba /Hincl].
      rewrite inE => /orP[|].
      * move/eqP => ?; by subst b.
      * move=> btl.
        rewrite /sorted in lst_sorted.
        have /= := @subseq_path _ _ Htrans a [:: b] tl.
        rewrite andbT.
        by apply => //; rewrite sub1seq.
  - by rewrite perm_sym; apply permEl, perm_filterC.
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
  by rewrite inE => /orP[|//]; rewrite (negbTE ihd).
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

Section seq_bool.

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

End seq_bool.

Section finfun_ext.

Lemma inj_card (A B : finType) (f : {ffun A -> B}) :
  injective f -> #| A | <= #| B |.
Proof. move=> Hf; by rewrite -(@card_imset _ _ f) // max_card. Qed.

End finfun_ext.

Lemma bij_swap A B : bijective (@swap A B).
Proof. apply Bijective with swap; by case. Qed.
Arguments bij_swap {A B}.

Section finset_ext.
Implicit Types A B : finType.

Lemma injective_swap (A B : finType) (E : {set A * B}) : {in E &, injective swap}.
Proof. by case=> a b [a0 b0] /= _ _ [-> ->]. Qed.

Lemma set_swap (A B : finType) (P : B -> A -> bool) :
  [set h : {: B * A} | P h.1 h.2 ] = swap @: [set h | P h.2 h.1].
Proof.
apply/setP => /= -[b a]; rewrite !inE /=; apply/idP/imsetP => [H|].
- by exists (a, b) => //=; rewrite inE.
- by case=> -[a0 b0]; rewrite inE /= => ? [-> ->].
Qed.

Lemma setT_bool : [set: bool] = [set true; false].
Proof.
apply/eqP; rewrite eqEsubset; apply/andP; split => //.
by apply/subsetP => x; rewrite !inE; case: x.
Qed.

Lemma setDUKl A (E F : {set A}) : (E :|: F) :\: E = F :\: E.
Proof. by rewrite setDUl setDv set0U. Qed.

Lemma setDIlW (T : finType) (A B C : {set T}) :
  A :&: B :\: C = A :&: B :\: C :&: B.
Proof.
apply/setP=> x; rewrite !inE.
by case: (x \in A); case: (x \in B); case: (x \in C).
Qed.

Lemma setIDACW (T : finType) (A B C : {set T}) :
  (A :\: B) :&: C = A :&: C :\: B :&: C.
Proof. by rewrite setIDAC setDIlW. Qed.

Lemma setDAC (T : finType) (A B C : {set T}) :
  A :\: B :\: C = A :\: C :\: B.
Proof. by rewrite setDDl setUC -setDDl. Qed.

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

Local Notation "A `* B" := (setX A B).

Lemma setX1 A B (a : A) (b : B) : [set a] `* [set b] = [set (a, b)].
Proof. by apply/setP => -[a0 b0]; rewrite !inE /= xpair_eqE. Qed.

Lemma setX1r (A B : finType) (E : {set A}) (b : B) :
  E `* [set b] = [set (a, b) | a in E].
Proof. by rewrite -imset2_pair imset2_set1r. Qed.

Lemma setX0 (A B : finType) (E : {set A}) : E `* set0 = set0 :> {set A * B}.
Proof.
apply/setP/subset_eqP/andP; split; apply/subsetP => -[a b]; rewrite !inE //.
by move/andP => [].
Qed.

Lemma set0X (A B : finType) (F : {set B}) : set0 `* F = set0 :> {set A * B}.
Proof.
by apply/setP/subset_eqP/andP; split; apply/subsetP => -[a b]; rewrite !inE.
Qed.

Lemma setIX (A B : finType) (E E' : {set A}) (F F' : {set B}) :
  E `* F :&: E' `* F' = (E :&: E') `* (F :&: F').
Proof.
apply/setP => -[a b]; rewrite !inE /= !andbA; congr (_ && _).
by rewrite -!andbA; congr (_ && _); rewrite andbC.
Qed.

Lemma setCX (A B : finType) (E : {set A}) :
  ~: E `* setT = ~: (E `* setT) :> {set A * B}.
Proof. by apply/setP => -[a b]; rewrite !inE !andbT. Qed.

Lemma setTX (A B : finType) : setT `* setT = setT :> {set A * B}.
Proof. by apply/setP => -[/= a b]; rewrite !inE. Qed.

Lemma cardsltn1P A (E : {set A}) :
  (1 < #| E |) = [exists a, exists b, [&& (a \in E), (b \in E) & (a != b)]].
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
  case/boolP : (b == c) => [_|bc]; first by rewrite !orbT.
  rewrite orbF.
  case/boolP : (b == a) => //= /eqP <-; by rewrite eq_sym.
case/set0Pn => b Hb.
have -> : 1 < #| E | by rewrite (cardsD1 a E) Ha /= (cardsD1 b (E :\ a)) Hb.
apply/esym; apply/existsP; exists a; apply/existsP; exists b.
by rewrite !inE eq_sym andbC in Hb; rewrite Hb Ha.
Qed.

Lemma cards2P (A : finType) (E : {set A}) :
  (#| E | == 2) = [exists a, exists b, (E == [set a; b]) && (a != b)].
Proof.
apply/idP/idP => [s2|]; last first.
  by move/existsP => -[a /existsP[b /andP[/eqP -> ab]]]; rewrite cards2 ab.
move: (s2) => /eqP/esym/eq_leq.
rewrite cardsltn1P => /existsP[a /existsP[b /and3P[aE bE ab]]].
apply/existsP; exists a; apply/existsP; exists b; rewrite ab andbT; apply/eqP.
rewrite -(setD1K aE) -(setD1K bE); apply/setP => i; rewrite !inE.
have [/eqP->{i} //|/= ia] := boolP (i == a).
have [/eqP->{i} //|/= ib] := boolP (i == b).
apply/negbTE/negP => iE.
move/eqP : s2; rewrite (cardsD1 a) aE add1n => -[].
rewrite (cardD1 b) !inE eq_sym ab bE add1n => -[].
by rewrite (cardD1 i) !inE ib ia iE add1n.
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

Definition fin_img (A : finType) (B : eqType) (f : A -> B) : seq B := undup (map f (enum A)).

Lemma fin_img_imset (A B : finType) (f : A -> B) : fin_img f =i f @: A.
Proof.
apply/subset_eqP/andP; split; apply/subsetP => b; rewrite mem_undup; case/boolP : [exists a, b  == f a].
- by case/existsP => a /eqP ->; rewrite imset_f.
- rewrite negb_exists; move/forallP=> bfx.
  case/mapP => a _ bfa.
    by move: (bfx a); rewrite bfa => /eqP.
- by case/existsP => a /eqP -> _; apply/mapP; exists a; rewrite // mem_enum.
- rewrite negb_exists; move/forallP=> bfx.
  case/imsetP => a _ bfa.
    by move: (bfx a); rewrite bfa => /eqP.
Qed.

Lemma imset_preimset (I J : finType) (h : I -> J) (B : {set J}) :
  B \subset h @: I -> h @: (h @^-1: B) = B.
Proof.
move/subsetP=> B_covered.
apply/setP/subset_eqP/andP. (* or, apply/eqP; rewrite eqEsubset; apply/andP. *)
split; apply/subsetP => x; first by case/imsetP => i; rewrite inE => H ->.
move=> xB; case/(B_covered x)/imsetP: (xB) => y yI xhy.
by apply/imsetP; exists y => //; rewrite inE -xhy.
Qed.

Section more_preimset.
Context {R : Type}.
Variables (aT1 aT2 aT3 rT1 rT2 rT3 : finType).
Variables (f : aT1 -> rT1)  (g : aT2 -> rT2) (h : aT3 -> rT3).
Variables (A : {set rT1}) (B : {set rT2}) (C : {set rT3}).

Local Notation "f × g" :=
  (fun xy => (f xy.1, g xy.2)) (at level 10).

Lemma preimsetX : f × g @^-1: (A `* B) = f @^-1: A `* g @^-1: B.
Proof. by apply/setP=> -[] a b /=; rewrite !inE. Qed.

Lemma preimsetX2 :
  h × (f × g) @^-1: (C `* (A `* B)) = h @^-1: C `* (f @^-1: A `* g @^-1: B).
Proof. by apply/setP=> -[] a b /=; rewrite !inE. Qed.

Lemma in_preimset x (Y : {set rT1}) : (x \in f @^-1: Y) = (f x \in Y).
Proof. by rewrite !inE. Qed.

Lemma in_preimset1 x y : (x \in f @^-1: [set y]) = (f x == y).
Proof. by rewrite !inE. Qed.

End more_preimset.

Lemma imsetPn {aT rT : finType} {f : aT -> rT} {D : mem_pred aT} {y : rT} :
  reflect (forall x : aT, in_mem x D -> y != f x) (y \notin imset f D).
Proof.
apply: (iffP idP).
  move/imsetP=> H x xD; apply/eqP=> yfx; apply: H.
  by exists x.
move=> H; apply/imsetP=> -[] x xD yfx.
by have:= H x xD; rewrite yfx eqxx.
Qed.

Lemma big_set2 (R : Type) (idx : R) (op : Monoid.com_law idx) (I : finType)
  (a b : I) (F : I -> R) :
  a != b -> \big[op/idx]_(i in [set a; b]) F i = op (F a) (F b).
Proof. by move=> ab; rewrite big_setU1 ?inE // big_set1. Qed.

Definition setY (T : finType) (A B : {set T}) := (A :\: B :|: B :\: A).
Notation "A :+: B" := (setY A B).

Section setY_lemmas.
Variable (T : finType).
Local Notation "+%S" := (@setY T).
Local Notation "-%S" := idfun.
Local Notation "0" := (@set0 T).

Lemma setYA : associative +%S.
Proof.
move=> x y z; apply/setP=> i; rewrite !inE.
by case: (i \in x); case: (i \in y); case: (i \in z).
Qed.
Lemma setYC : commutative +%S.
Proof. by move=> *; rewrite /setY setUC. Qed.
Lemma set0Y : left_id 0 +%S.
Proof. by move=> ?; rewrite /setY set0D setD0 set0U. Qed.
Lemma setNY : left_inverse 0 -%S +%S.
Proof. by move=> *; rewrite /setY /= setDv setU0. Qed.
Lemma setIYl : left_distributive (@setI T) +%S.
Proof. by move=> *; rewrite [in LHS]/setY setIUl !setIDACW. Qed.

Lemma setIUY (A B : {set T}) :
  (A :+: B) :|: (A :&: B) = A :|: B.
Proof. by apply/setP=> x; rewrite !inE; case: (x \in A); case: (x \in B). Qed.

Lemma setIYI_disj (A B : {set T}) :
  [disjoint (A :+: B) & (A :&: B)].
Proof.
rewrite -setI_eq0; apply/eqP/setP=> x; rewrite !inE.
by case: (x \in A); case: (x \in B).
Qed.

End setY_lemmas.

End finset_ext.
Notation "A `* B" := (setX A B) : set_scope.
Notation "A :+: B" := (setY A B).

Module Set2.
Section set2.
Variable A : finType.
Hypothesis A2 : #|A| = 2%nat.

Definition a := enum_val (cast_ord (esym A2) ord0).
Definition b := enum_val (cast_ord (esym A2) (lift ord0 ord0)).

Lemma enumE : enum A = a :: b :: [::].
Proof.
apply (@eq_from_nth _ a); first by rewrite -cardE A2.
case=> [_|]; first by rewrite [X in _ = X]/= {2}/a (enum_val_nth a).
case=> [_ |i]; last by rewrite -cardE A2.
by rewrite [X in _ = X]/= {1}/b (enum_val_nth a).
Qed.

Lemma a_neq_b : a != b.
Proof. rewrite /a /b. apply/eqP. by move/enum_val_inj. Qed.

Lemma neq_a_b x : x != a -> x == b.
Proof. have : x \in A by []. by rewrite -mem_enum enumE !inE => /orP[->|]. Qed.

Lemma ind (P : A -> Type) : P a -> P b -> forall a, P a.
Proof. by move=> ?? c; have [/eqP->//|/neq_a_b/eqP ->] := boolP (c == a). Qed.

Lemma E : setT = [set a; b].
Proof.
apply/setP => x; rewrite !inE; apply/esym; move: x.
by apply: (@ind (fun x => (x == a) || (x == b))); rewrite eqxx ?orbT ?orTb.
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
rewrite (tnth_nth t!_i) [in X in _ = X](tnth_nth t!_i).
by rewrite -(@nth_take k) // -[in X in _ = X](@nth_take k) // tv.
Qed.

Lemma eq_tcast n m (v : m.-tuple A) (H : m = n) : tval (tcast H v) = v.
Proof. by subst m; rewrite tcast_id. Qed.

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
  transitive r -> sorted r t -> forall a b : 'I_k, a < b -> r (t !_ a) (t !_ b).
Proof.
move=> r_trans r_sorted a b ab.
rewrite (tnth_nth t!_b) {2}(tnth_nth t!_b).
apply sorted_of_nth => //; by rewrite ab size_tuple /=.
Qed.

Lemma sorted_of_tnth_leq (X : finType) (n : nat) (r : rel X) (t : n.-tuple X)
  (r_trans : transitive r) (r_refl : reflexive r) (Hx : sorted r t) :
  forall (l p : 'I_n), l <= p -> r t!_l t!_p.
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

Lemma tnth_uniq (T : eqType) n (t : n.-tuple T) (i j : 'I_n) :
  uniq t -> (t !_ i == t !_ j) = (i == j).
Proof.
pose a := t !_ i; rewrite 2!(tnth_nth a) => *.
by rewrite nth_uniq // size_tuple.
Qed.

End tuple_ext.

Section bseq_lemmas.

Variables (n : nat) (T : Type).

Lemma bseqval_inj : injective (@bseqval n T).
Proof.
move=> [a Ha] [b Hb] /= H.
move: Ha Hb; rewrite H => Ha Hb.
by congr Bseq; exact: eq_irrelevance.
Qed.

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

Definition perm_tuple (t : n.-tuple A) := [tuple (t !_ (s i)) | i < n].

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
  rewrite /= enum_ordSl /= (tnth_nth (thead a, thead b)) /= nth_zip; last first.
    by rewrite (size_tuple a) (size_tuple b).
  by rewrite (tnth_nth (thead a)) /= (tnth_nth (thead b)).
rewrite (tnth_nth (thead a, thead b)) (tnth_nth (thead (zip_tuple a b))) /=.
rewrite enum_ordSl /= nth_zip; last by rewrite 4!size_map size_enum_ord.
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

Lemma perm_on_Sn (s : 'S_n) : perm_on [set x | x \in enum 'I_n] s.
Proof. apply/subsetP=> /= x _; by rewrite !in_set mem_enum. Qed.

(*Lemma perm_eq_enum (s : 'S_n) : perm_eq (enum 'I_n) (map (s^-1)%g (enum 'I_n)).
Proof.
apply uniq_perm.
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
Qed.*)

End perm_enum.

Section fingraph_ext.

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

End fingraph_ext.

Section uniq_path.

Variable A : eqType.
Variable g : rel A.

Definition uniq_path a p := path g a p && uniq (a :: p).

Lemma cons_uniq_path a b s :
  g a b -> a \notin b :: s -> uniq_path b s -> uniq_path a (b :: s).
Proof.
move=> Hab Has /andP /= [Hpi Hun].
rewrite /uniq_path /=.
by rewrite Hun Hpi Hab Has.
Qed.

Lemma rev_path_rcons a b p :
  symmetric g ->
  path g a (rcons p b) = path g b (rcons (rev p) a).
Proof.
move=> HR.
elim: p a b => [|c p Hp] a b /=.
  by rewrite HR.
rewrite rev_cons -(cats1 _ a) cat_path -Hp /= last_rcons /=.
by rewrite (HR a) andbC andbT.
Qed.

End uniq_path.

Section boolP.
Variables (p : bool) (R : Type) (T : is_true p -> R) (F : is_true (~~ p) -> R).
Lemma boolPT  (H : is_true p) :
  match boolP p with
  | AltTrue HT => T HT
  | AltFalse HF => F HF
  end = T H.
Proof.
destruct boolP.
- congr T.
  rewrite (Eqdep_dec.eq_proofs_unicity _ i H) //.
  by move=> x y; have:= Bool.bool_dec x y => -[]; [left | right].
- by elim: (negP i).
Qed.

Lemma boolPF  (H : is_true (~~ p)) :
  match boolP p with
  | AltTrue HT => T HT
  | AltFalse HF => F HF
  end = F H.
Proof.
destruct boolP.
- by elim: (negP H).
- congr F.
  rewrite (Eqdep_dec.eq_proofs_unicity _ i H) //.
  by move=> x y; have:= Bool.bool_dec x y => -[]; [left | right].
Qed.
End boolP.

Section fintype_extra.

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

Lemma split_lshift n m (i : 'I_n) : fintype.split (lshift m i) = inl i.
Proof. by rewrite -/(unsplit (inl i)) unsplitK. Qed.

Lemma split_rshift n m (i : 'I_m) : fintype.split (rshift n i) = inr i.
Proof. by rewrite -/(unsplit (inr i)) unsplitK. Qed.

Lemma size_index_enum (T : finType) : size (index_enum T) = #|T|.
Proof. by rewrite cardT enumT. Qed.

Lemma index_enum_cast_ord n m (e : n = m) :
  index_enum 'I_m = [seq cast_ord e i | i <- index_enum 'I_n].
Proof.
subst m; rewrite -{1}(map_id (index_enum 'I_n)).
apply eq_map=> [[x xlt]].
by rewrite /cast_ord; congr Ordinal; exact: bool_irrelevance.
Qed.

Lemma perm_map_bij [T : finType] [f : T -> T] (s : seq T) : bijective f ->
  perm_eq (index_enum T) [seq f i | i <- index_enum T].
Proof.
rewrite /index_enum; case: index_enum_key => /= fbij.
rewrite /perm_eq -enumT -forallb_tnth; apply /forallP=>i /=.
case: fbij => g fg gf.
rewrite enumT enumP count_map -size_filter (@eq_in_filter _ _
    (pred1 (g (tnth (cat_tuple (enum_tuple T) (map_tuple [eta f] (enum_tuple T))) i)))).
  by rewrite size_filter enumP.
by move=> x _ /=; apply/eqP/eqP => [/(congr1 g) <-|->//].
Qed.

End fintype_extra.

Section order_extra.
(* eq_le would be a better name but it is already occupied:
   eq_le : (x == y) = (x <= y <= x)%O *)
Lemma eqW {disp : order.Order.disp_t} {T : porderType disp} (x y : T) :
  x = y -> (x <= y)%O.
Proof. by move->; exact: Order.POrderTheory.lexx. Qed.
End order_extra.
