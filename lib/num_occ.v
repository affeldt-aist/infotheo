(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect fingroup perm zmodp ssralg.
Require Import ssr_ext f2.

(**md**************************************************************************)
(* # Number of occurrences in a tuple                                         *)
(*                                                                            *)
(* ```                                                                        *)
(*             N(a | t) == number of occurrences of a in t                    *)
(*   N((a,b) | (ta,tb)) == number of occurrences of (a,b) in zip ta tb        *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "'N(' a '|' t ')'" (format "N( a  |  t )").
Reserved Notation "'N(' a ',' b '|' ta ',' tb ')'".

Declare Scope num_occ_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope tuple_ext_scope.
Local Open Scope nat_scope.

Section num_occ_def.
Variables (A : eqType) (a : A) (t : seq A).

Definition num_occ := count_mem a t.

End num_occ_def.

Notation "'N(' a '|' t ')'" := (num_occ a t) : num_occ_scope.
Local Open Scope num_occ_scope.

Section num_occ_prop.
Variables (A : eqType) (a : A).

Lemma num_occ0 : N(a | [::]) = 0. Proof. by []. Qed.

Lemma num_occ_cons x y (t : seq A) : N(x | y :: t) = (x == y) + N(x | t).
Proof. by rewrite eq_sym. Qed.

Lemma filter_pred1_num_occ (t : seq A) : filter (pred1 a) t = nseq N(a | t) a.
Proof.
set lhs := (X in X = _).
rewrite (_ : N(a | t) = size lhs); last by rewrite size_filter.
apply/all_pred1P/all_filterP; by rewrite filter_id.
Qed.

Lemma num_occ_map_filter (B : finType) (f : B -> A) (s : {set B}) (p : pred A) (pa : p a) :
  N(a | [seq f i | i <- enum s & p (f i)]) = N(a | [seq f i | i in s]).
Proof.
rewrite /num_occ count_map count_filter /= count_map.
apply eq_count => /= m0 /=; by rewrite andb_idr // => /eqP ->.
Qed.

Lemma notin_num_occ_0 (t : seq A) : (a \notin t) = (N(a | t) == O).
Proof.
apply/esym.
case/boolP : (a \notin t) => [/count_memPn | ].
  rewrite /num_occ; by move=> ->.
apply: contraNF; by move/eqP/count_memPn.
Qed.

Lemma mem_num_occ_gt0 (t : seq A) : (a \in t) = (0 < N(a | t)).
Proof. by rewrite ltnNge leqn0 -notin_num_occ_0 negbK. Qed.

Lemma num_occ_rev (t : seq A) : N(a | t) = N(a | rev t).
Proof.
elim : t => // hd tl IH /=.
by rewrite IH rev_cons /= {2}/num_occ -cats1 count_cat /= addn0 addnC.
Qed.

End num_occ_prop.
Arguments num_occ_map_filter [A] [a] [B] [f] [s] _ _.

Lemma num_occ_sum : forall (t : seq 'F_2), num_occ 1%R t = \sum_(i <- t) i.
Proof.
elim => [ /= | /= h t ->]; first by rewrite big_nil.
rewrite big_cons; by case/F2P: h.
Qed.

Lemma num_occ_sum_bool : forall t : seq bool, N(true | t) = \sum_(i <- t) i.
Proof.
elim => [|hd tl IH]; first by rewrite big_nil num_occ0.
rewrite /num_occ /= -/(N(true | tl)) IH big_cons; by case: hd.
Qed.

Lemma sum_num_occ_size (A : finType) s : (\sum_(a in A) N(a|s))%nat = size s.
Proof.
elim: s => [|a s IH] /=.
+ by apply big1_eq.
+ by rewrite big_split /= IH -big_mkcond /= (big_pred1 a) // => x; rewrite eq_sym.
Qed.

Lemma num_occ_flatten (A : finType) (a : A) ss :
  N(a|flatten ss) = (\sum_(s <- ss) N(a|s))%nat.
Proof.
rewrite /num_occ.
elim: ss => [|s ss IH] /=; first by rewrite big_nil.
by rewrite big_cons /= count_cat IH.
Qed.

Section num_occ_tuple.

Lemma num_occ_leq_n {A : eqType} n a (t : n.-tuple A) : N(a | t) <= n.
Proof. by rewrite /num_occ -[X in _ <= X](size_tuple t) count_size. Qed.

Variables (A : finType) (n : nat) (a : A) (t : n.-tuple A).

Definition set_occ := [set i | t !_ i == a].

Lemma num_occ_alt : N(a | t) = #| set_occ |.
Proof.
rewrite cardE -sum1_size big_filter /= /num_occ -sum1_count big_tuple.
apply/eq_bigl => i; by rewrite !inE.
Qed.

Lemma num_occ_thead (ta : n.+1.-tuple A) :
  N(a | ta) = N(a | [tuple of [:: thead ta]]) + N(a | tbehead ta).
Proof.  by rewrite {1}(tuple_eta ta) /num_occ /= addn0. Qed.

Lemma sum_num_occ_seq1 : \sum_(i in A) N(i | [:: a]) = 1.
Proof.
rewrite (bigID (pred1 a)) /= big_pred1_eq /= eqxx /= addn0.
rewrite (_ : \sum_(_ | _) _ = \sum_(a' : A | a' != a) 0).
by rewrite sum_nat_const muln0.
apply eq_bigr => a'' /negbTE Ha''; by rewrite eq_sym Ha''.
Qed.

End num_occ_tuple.

Section num_occ_tuple_prop.
Variable (A : finType) (n : nat) (t : n.-tuple A).

Lemma sum_num_occ_alt : \sum_(a in A) N(a | t) = n.
Proof.
elim : n t => [[] [] // Hi|m IH y].
  by rewrite (eq_bigr (fun=> 0)) // big_const iter_addn.
rewrite (eq_bigr (fun a => N(a | [tuple of [:: thead y]]) + N(a | tbehead y))).
  by rewrite big_split /= (IH (tbehead y)) sum_num_occ_seq1 add1n.
move=> a _; by apply num_occ_thead.
Qed.

Lemma sum_num_occ_all : \sum_(i < #|A|) N(enum_val i | t) = n.
Proof.
symmetry.
rewrite -{1}sum_num_occ_alt.
rewrite (reindex_onto enum_rank enum_val) /= => [|i _]; last by rewrite enum_valK.
apply eq_big => x0 ; by rewrite enum_rankK // eqxx.
Qed.

Local Open Scope group_scope.

Lemma num_occ_perm (a : A) (s : 'S_n) : N(a | perm_tuple s t) = N(a | t).
Proof.
rewrite 2!num_occ_alt.
rewrite (_ : set_occ a (perm_tuple s t) = s^-1 @: set_occ a t).
apply/card_imset/perm_inj.
apply/eqP.
rewrite eqEsubset.
apply/andP; split; apply/subsetP => i.
- rewrite in_set => H.
  apply/imsetP.
  exists (s i); last by rewrite -permM mulgV perm1.
  rewrite in_set.
  move/eqP : H => <-; by rewrite /perm_tuple tnth_map tnth_ord_tuple.
- rewrite in_set.
  case/imsetP => j.
  rewrite in_set.
  move/eqP => <- ->.
  by rewrite tnth_map tnth_ord_tuple permKV.
Qed.

Local Close Scope group_scope.

End num_occ_tuple_prop.

Section num_co_occ_def.
Variables (A B : eqType) (a : A) (b : B) (ta : seq A) (tb : seq B).

Local Open Scope nat_scope.

Definition num_co_occ := N( (a, b) | zip ta tb ).

End num_co_occ_def.

Notation "'N(' a ',' b '|' ta ',' tb ')'" := (num_co_occ a b ta tb) : num_occ_scope.

Section num_co_occ_prop.
Variables (A B : eqType) (a : A) (b : B) (ta : seq A) (tb : seq B).

Lemma num_co_occ1 (a' : A) : N(a, b | [:: a'], [:: b]) = N(a | [:: a']).
Proof. by rewrite /num_co_occ /num_occ /= !addn0 xpair_eqE eqxx andbC. Qed.

Lemma num_co_occ_sym : N(a, b | ta, tb) = N(b, a | tb, ta).
Proof.
rewrite /num_co_occ /num_occ.
rewrite (_ : zip tb ta = map (fun x => (x.2, x.1)) (zip ta tb)); last by apply zip_swap.
rewrite -2!size_filter filter_map size_map.
congr (size _).
apply eq_filter; case=> a' b' /=.
by rewrite 2!xpair_eqE andbC.
Qed.

End num_co_occ_prop.

Section num_co_occ_tuple.
Variables (A B : finType) (n : nat) (a : A) (b : B) (ta : n.-tuple A) (tb : n.-tuple B).

Definition set_co_occ := [set i | (ta !_ i == a) && (tb !_ i == b)].

Lemma num_co_occ_leq_n : N(a, b | ta, tb) <= n.
Proof. rewrite /num_co_occ ; by apply num_occ_leq_n. Qed.

Lemma num_co_occ_ub : N(a, b | ta, tb) < n.+1.
Proof. rewrite ltnS ; apply num_co_occ_leq_n. Qed.

Lemma num_co_occ_alt : N(a, b | ta, tb) = #| set_co_occ |.
Proof.
rewrite /num_co_occ num_occ_alt /set_occ.
apply eq_card => i.
rewrite !in_set /zip_tuple (tnth_nth (a, b)) nth_zip ?size_tuple //.
by rewrite -2!tnth_nth xpair_eqE.
Qed.

End num_co_occ_tuple.

Section num_co_occ_tuple_prop.
Variables (A B : finType) (n : nat) (ta : n.-tuple A) (tb : n.-tuple B).

Lemma num_co_occ_sum : \sum_(a : A) \sum_ (b : B) N( a , b | ta , tb) = n.
Proof.
rewrite pair_big /=.
rewrite (_ : \sum_p N(p.1, p.2 | ta, tb) = \sum_p N(p | zip_tuple ta tb)).
  by rewrite sum_num_occ_alt.
f_equal.
Qed.

Definition set_set_co_occ a :=
  [set set_co_occ a b ta tb | b in B & [exists i, i \in set_co_occ a b ta tb]].

Lemma cover_set_set_co_occ a : cover (set_set_co_occ a) = set_occ a ta.
Proof.
apply/setP => i.
rewrite cover_imset.
apply/bigcupP.
case : ifP; last by move=> /negP H1 H ; move: H1; apply/negP; case H => {H} y0 ; rewrite 3!in_set => _ /andP [].
rewrite in_set => /eqP Hi.
exists (tb!_i) ; last by rewrite in_set Hi eqxx andTb.
rewrite in_set; apply/andP; split => //.
apply/existsP; exists i; by rewrite in_set Hi eqxx andTb.
Qed.

Lemma trivIset_set_set_co_occ a : trivIset (set_set_co_occ a).
Proof.
apply/trivIsetP => S1 S2; case/imsetP => P1 _ HP1; case/imsetP => P2 _ HP2 HP12.
subst S1 S2.
rewrite /disjoint.
apply/pred0P => m /=.
apply/negP/negP.
rewrite 2!in_set.
move: m.
apply/forallP; rewrite -negb_exists; apply/negP; case/existsP => i /andP [/andP [_ /eqP H1] /andP [_ /eqP H2]]; contradict HP12.
apply/negP/negPn/eqP; by rewrite -H1 -H2.
Qed.

Lemma num_co_occ_partial_sum_alt a : \sum_(b : B) N(a , b | ta , tb) = N(a | ta).
Proof.
elim: n ta tb => [x' y' | m IHm x1 y1].
  rewrite (tuple0 x') (tuple0 y') num_occ0.
  transitivity (\sum_(y0 : B) 0).
    by apply eq_bigr => b _.
  by rewrite big_const iter_addn mul0n addn0.
rewrite num_occ_thead.
transitivity (\sum_y0 (N(a, y0 | [tuple thead x1], [tuple thead y1]) +
                       N(a, y0 | tbehead x1, tbehead y1))).
  apply eq_bigr => i _.
  by rewrite {1}/num_co_occ {1}(tuple_eta x1) {1}(tuple_eta y1) /num_co_occ /num_occ /= addn0.
rewrite big_split /=.
move: {IHm}(IHm (tbehead x1) (tbehead y1)) => ->.
congr (_ + _).
rewrite (bigD1 (thead y1)) //= num_co_occ1.
set tmp := \sum_(_ | _) _.
suff : tmp = 0 by move=> ->; rewrite addn0.
rewrite {}/tmp.
transitivity (\sum_(H | H != thead y1) 0).
  apply eq_bigr => b Hb.
  apply/eqP.
  rewrite /num_co_occ -notin_num_occ_0.
  move: Hb; apply contra => Hb.
  case/tnthP : Hb => i.
  rewrite (tnth_nth (a, b)) /= (ord1 i) /=.
  by case => _ ->.
by rewrite big_const iter_addn mul0n addn0.
Qed.

Lemma num_co_occ_perm (a : A) (b : B) (s : 'S_n) :
  N( a , b | perm_tuple s ta , perm_tuple s tb ) = N( a , b | ta , tb ).
Proof.
by rewrite /num_co_occ -(@num_occ_perm _ n (zip_tuple ta tb) (a, b) s) -zip_perm_tuple.
Qed.

End num_co_occ_tuple_prop.

Lemma num_co_occ_num_occ1 {A B : finType} a' b' (a : A) :
  \sum_(i in B) N(a, i | [tuple of [:: a']], [tuple of [:: b']]) = (a' == a).
Proof.
case/boolP : (a' == a) => [/eqP ->{a'} | a'a].
- rewrite /num_co_occ /num_occ /= (bigD1 b') //= eqxx /= addn0 add1n; congr S.
  rewrite (eq_bigr (fun=> 0)).
  by rewrite big_const iter_addn.
  move=> b bb'; by rewrite xpair_eqE eqxx /= addn0 eq_sym (negbTE bb').
- rewrite (eq_bigr (fun=> 0)).
  by rewrite big_const iter_addn.
  move=> b _; by rewrite /num_co_occ /num_occ /= xpair_eqE (negbTE a'a).
Qed.

Lemma num_co_occ_num_occ {A B : finType} : forall n (ta : n.-tuple A) (tb : n.-tuple B) a,
   \sum_(b in B) N(a, b | ta, tb) = N(a | ta).
Proof.
elim => [ta tb a | n IH ta tb a].
  rewrite (tuple0 ta) (tuple0 tb) /= (eq_bigr (fun=> 0)) //.
  by rewrite big_const iter_addn !Monoid.simpm.
move: {IH}(IH (tbehead ta) (tbehead tb) a) => IH.
rewrite [in X in _ = X]/num_occ /= in IH.
rewrite (tuple_eta ta) (tuple_eta tb) /= [in RHS]/num_occ.
rewrite (eq_bigr (fun b =>
  N(a, b | [:: thead ta], [:: thead tb]) + N(a, b | tbehead ta, tbehead tb))).
  by rewrite big_split /= IH num_co_occ_num_occ1.
move=> b' _; by rewrite /num_co_occ num_occ_thead.
Qed.

Section cansort.
Variable A : finType.
Variable n : nat.
Variable ta : n.-tuple A.

Definition sum_num_occ (k : nat) := \sum_(i < #|A| | i < k) N(enum_val i | ta).

Lemma sum_num_occ_0 : sum_num_occ 0 = 0.
Proof. rewrite /sum_num_occ; apply big_pred0 => i /=; by rewrite ltn0. Qed.

Lemma sum_num_occ_rec (k : 'I_#|A|) : sum_num_occ k.+1 = sum_num_occ k + N(enum_val k | ta).
Proof.
rewrite /sum_num_occ (bigD1 k) /=; last by exact (leqnn k).
rewrite addnC.
apply/eqP; rewrite eqn_add2r; apply/eqP.
apply eq_bigl => i; by rewrite andbC -ltn_neqAle.
Qed.

Lemma sum_num_occ_sub (k : 'I_#|A|) : sum_num_occ k.+1 - sum_num_occ k = N(enum_val k | ta).
Proof.
rewrite sum_num_occ_rec addnC; symmetry.
by rewrite -{1}(addn0 N(enum_val k | ta)) -(subnn (sum_num_occ k)) addnBA.
Qed.

Lemma full_sum_num_occ (k : nat) : #|A| <= k ->
  sum_num_occ k = \sum_(i < #|A|) N(enum_val i | ta).
Proof. move=> Hk; apply eq_bigl => i; by rewrite (leq_trans (ltn_ord i) Hk). Qed.

Lemma full_sum_num_occ_n (k : nat) : #|A| <= k -> sum_num_occ k = n.
Proof. move=> Hk; by rewrite full_sum_num_occ // sum_num_occ_all. Qed.

Lemma sum_num_occ_inc_loc (k : nat) : sum_num_occ k <= sum_num_occ k.+1.
Proof.
case/boolP : (k < #|A|) => Hcase.
- move: (sum_num_occ_rec (Ordinal Hcase)) => /= ->; by apply leq_addr.
- rewrite -leqNgt in Hcase.
  rewrite !full_sum_num_occ //; by apply (leq_trans Hcase).
Qed.

Lemma sum_num_occ_inc (k l : nat) : k <= l -> sum_num_occ k <= sum_num_occ l.
Proof.
move=> kl.
have -> : l = k + (l - k) by rewrite subnKC.
set m := l - k.
elim: m => [|n' IH].
- by rewrite addn0 leqnn.
- by rewrite (leq_trans IH _) // addnS sum_num_occ_inc_loc.
Qed.

Lemma sum_num_occ_leq_n (k : nat) : sum_num_occ k <= n.
Proof.
case/boolP : (k < #|A|) => Hcase.
- rewrite -(@full_sum_num_occ_n #|A| _); last by apply leqnn.
  apply ltnW in Hcase.
  by apply sum_num_occ_inc.
- rewrite -leqNgt in Hcase.
  by rewrite full_sum_num_occ_n.
Qed.

Lemma minn_sum_num_occ_n (k : nat) : minn (sum_num_occ k) n = sum_num_occ k.
Proof. apply/minn_idPl ; apply sum_num_occ_leq_n. Qed.

Lemma min_sum_num_occ (k : nat) : minn (sum_num_occ k) (sum_num_occ k.+1) = sum_num_occ k.
Proof. apply/minn_idPl; by apply sum_num_occ_inc. Qed.

Section order_surgery.
Hypothesis ta_cansorted : sorted (@le_rank A) ta.

(* TODO: move? *)
Lemma set_predleq_size r k l : k + l <= r -> #|[set i : 'I_r | nat_of_ord i \in iota k l]| = l.
Proof.
elim: l => [kr | l IH HSl].
- apply/eqP; rewrite cards_eq0; apply/eqP.
  apply/setP => i; by rewrite !inE.
- rewrite addnS in HSl.
  have : k + l <= r by apply: (leq_trans _ HSl); apply leqnSn.
  move/IH => Hl.
  rewrite -sum1_card (bigD1 (Ordinal HSl)) /=.
  rewrite (_ : \sum_(i in [set i0 : 'I_r | nat_of_ord i0 \in iota k l.+1] | _) 1 =
               \sum_(i in [set i0 : 'I_r | nat_of_ord i0 \in iota k l]) 1); last first.
    apply eq_bigl => i; rewrite !in_set.
    case/boolP : (i != Ordinal HSl) => Hcase.
    - rewrite andbT -addn1 iotaD /= mem_cat !inE.
      set tmp := _ == _ + _.
      suff -> : tmp = false by rewrite orbC.
      apply/eqP/eqP.
      move: Hcase; apply: contra => /eqP Hcase.
      by apply/eqP; apply val_inj.
    - rewrite negbK in Hcase.
      move/eqP : Hcase => ->.
      by rewrite andbC /= mem_iota /= ltnn andbC.
  by rewrite sum1_card Hl add1n.
rewrite in_set in_cons mem_iota /=.
destruct l; first by rewrite addn0; apply/orP; left.
apply/orP; right.
apply/andP; split; by [rewrite addnS ltnS leq_addr | rewrite ltn_add2r].
Qed.

Lemma sum_num_occ_enum_val (k : 'I_#|A|) (l : 'I_n) :
  sum_num_occ k <= l < sum_num_occ k.+1 -> ta!_l = enum_val k.
Proof.
move: (ltnSn k).
set k':= {2}k.+1.
move: k' => k'.
elim: k' l k => [l k /= | m IH l k km]; first by rewrite ltn0.
case/boolP : (k < m) => Hcase; first by apply IH.
rewrite -leqNgt in Hcase.
have : m = k by apply/eqP; rewrite eqn_leq; apply/andP.
rewrite {Hcase} => ?; subst m.
case/andP => [Hlm1 Hlm2].
apply/eqP/negPn/negP; move=> abs.
case/boolP : (lt_rank ta!_l (enum_val k)) => Hcase.
- have Hrank : enum_rank ta!_l < k by rewrite lt_rank_alt enum_valK in Hcase.
  have Hcontr : #|[set i | (i==l) || (sum_num_occ (enum_rank ta!_l)<= i < sum_num_occ (enum_rank ta!_l).+1)]| <= N(ta!_l|ta).
    rewrite num_occ_alt subset_leq_card // subsetE; apply/pred0P => i /=.
    rewrite !in_set /=.
    apply/negbTE; rewrite negb_and.
    case/boolP : (ta!_i == ta!_l) => ta_il //.
    rewrite negb_or; apply/andP; split.
    - move: ta_il; apply contra => /eqP ->; by rewrite eqxx.
    - move: ta_il; apply contra => ta_il.
      apply/eqP; rewrite -(enum_rankK (ta!_l)); by apply IH.
  rewrite (_ : #|[set i | (i == l) || (sum_num_occ (enum_rank ta!_l) <= i < sum_num_occ (enum_rank ta!_l).+1)]| = N(ta!_l | ta).+1) in Hcontr; first by rewrite ltnn in Hcontr.
  symmetry; rewrite -addn1 sum_num_occ_rec -sum1_card.
  rewrite (bigD1 l) /=; last by rewrite in_set; apply/orP; apply or_introl.
  rewrite addnC; apply/eqP; rewrite eqn_add2l; apply/eqP.
  transitivity (\sum_(i in [set i0 : 'I_n | nat_of_ord i0 \in iota (sum_num_occ (enum_rank ta!_l)) N(enum_val (enum_rank ta!_l) | ta)]) 1); last first.
    apply eq_bigl => i; rewrite !in_set.
    case/boolP : (i != l) => Hcase2.
    - rewrite mem_iota.
      move/negPf in Hcase2; by rewrite andbT Hcase2 orFb.
    - rewrite negbK in Hcase2; move/eqP in Hcase2; subst i.
      rewrite andbF mem_iota.
      apply/negP; case/andP => H1.
      rewrite -sum_num_occ_rec; apply/negP; rewrite -leqNgt.
      by rewrite (leq_trans _ Hlm1) // sum_num_occ_inc.
  by rewrite sum1_card set_predleq_size enum_rankK // -{2}(enum_rankK ta!_l) -sum_num_occ_rec sum_num_occ_leq_n.
- have {abs} {}Hcase : lt_rank (enum_val k) ta!_l.
    rewrite lt_rank_alt; rewrite lt_rank_alt -leqNgt in Hcase.
    rewrite ltn_neqAle; apply/andP; split => //.
    rewrite enum_valK.
    suff : k != enum_rank ta!_l by move=> ->.
    apply/negP ; move/eqP.
    move=> abs2; symmetry in abs2; rewrite -abs2 enum_rankK {abs2} in abs.
    contradict abs ; by apply/negP/negPn/eqP.
  move/negP : (ltnn N(enum_val k | ta)) => abs; contradict abs.
  rewrite {1}num_occ_alt.
  have H : #|[set i | ta!_i == enum_val k]| <= #|[set i : 'I_n | (sum_num_occ k <= i < l)]|.
    apply subset_leq_card.
    rewrite subsetE; apply/pred0P => i /=.
    rewrite !in_set /=.
    apply/negP/negP.
    rewrite negb_and negbK.
    case/boolP : (sum_num_occ k <= i < l) => Hcase2; first by apply/orP; apply or_introl.
    case/boolP : (l <= i) => Hcase3.
    + rewrite eq_sym; apply lt_neq_rank.
      eapply lt_le_rank_trans; first by apply Hcase.
      apply sorted_of_tnth_leq => //; [exact/le_rank_trans | exact/le_rank_refl].
    + rewrite -ltnNge in Hcase3.
      rewrite Hcase3 andbT -ltnNge {Hcase3} in Hcase2.
      apply lt_neq_rank.
      have lt0m : 0 < k.
        rewrite ltnNge leqn0 ; apply/eqP => abs2.
        contradict Hcase2 ; by rewrite abs2 sum_num_occ_0 ltn0.
      have H2 : forall (k' : 'I_#|A|) (l : 'I_n), k'.-1 < k -> l < sum_num_occ k' -> lt_rank ta!_l (enum_val k'). (* nested induction *)
      case; elim.
      - move=> H0 l0 /= _ abs2 ; contradict abs2 ; by rewrite sum_num_occ_0 ltn0.
      - move=> k' HR' HSk l0 /= k'k Hl0.
        have Hk' : k' < #|A| by apply: (leq_trans k'k _); apply ltnW.
        apply: (@le_lt_rank_trans _ _ (enum_val (Ordinal Hk'))).
        - case/boolP : (l0 < sum_num_occ k') => Hcase3; rewrite /le_rank leq_eqVlt; apply/orP; [apply or_intror | apply or_introl].
          - rewrite -lt_rank_alt; apply HR'; by [apply: (leq_ltn_trans (leq_pred _) k'k) | apply Hcase3].
          - rewrite -leqNgt in Hcase3; rewrite (IH _ (Ordinal Hk')) //; by apply/andP.
        - rewrite lt_rank_alt !enum_valK; by apply ltnSn.
      apply H2 ; by [rewrite -{2}(prednK lt0m) ; apply ltnSn | apply Hcase2].
  rewrite -(subnKC Hlm1) in H.
  set lhs := #| _ | in H.
  have {}H : lhs <= #|[set i : 'I_n | nat_of_ord i \in iota (sum_num_occ k) (l - sum_num_occ k)]|.
    apply (leq_trans H), eq_leq.
    by apply eq_card => /= i; rewrite !inE mem_iota.
  rewrite set_predleq_size in H; last by rewrite (subnKC Hlm1) ltnW.
  apply: (leq_ltn_trans H _).
  by rewrite -sum_num_occ_sub /= ltn_sub2r // (leq_ltn_trans Hlm1 Hlm2).
Qed.

Lemma enum_val_sum_num_occ (k : 'I_#|A|) (l : 'I_n) :
  ta!_l = enum_val k -> sum_num_occ k <= l < sum_num_occ k.+1.
Proof.
move=> Hkl; apply/negP => /negP abs.
have : #|[set i | (i == l) || (sum_num_occ k <= i < sum_num_occ k.+1)]| <= N(ta!_l | ta).
  rewrite num_occ_alt subset_leq_card // subsetE.
  apply/pred0P => /= i /=; rewrite !in_set /=.
  case/boolP : (ta!_i == ta!_l) => ta_il //=.
  apply/negbTE; rewrite negb_or; apply/andP; split.
  - move: ta_il; apply: contra => /eqP ?; subst l; by rewrite eqxx.
  - move: ta_il; apply: contra => Hsum_num_occ.
    apply/eqP; rewrite Hkl; by apply sum_num_occ_enum_val.
suff -> : #|[set i | (i == l) || (sum_num_occ k <= i < sum_num_occ k.+1)]| = N(ta!_l | ta).+1.
  by rewrite ltnn.
symmetry; rewrite -addn1 sum_num_occ_rec -sum1_card.
rewrite (bigD1 l) /=; last by rewrite in_set; apply/orP; apply or_introl.
rewrite addnC; apply/eqP; rewrite eqn_add2l; apply/eqP.
transitivity ( \sum_(i in [set i0 : 'I_n | nat_of_ord i0 \in iota (sum_num_occ k) N(enum_val k | ta)]) 1 ).
  rewrite sum1_card set_predleq_size; by [rewrite Hkl | rewrite -sum_num_occ_rec; apply sum_num_occ_leq_n].
apply eq_bigl => i; rewrite !in_set.
case/boolP : (i != l) => [/negPf |] il.
- by rewrite andbT il orFb mem_iota.
- rewrite negbK in il; move/eqP in il; subst i.
  rewrite andbF mem_iota.
  apply/negbTE; move: abs; apply contra.
  by rewrite -sum_num_occ_rec.
Qed.

Lemma sum_num_occ_is_enum_val (k : 'I_#|A|) (l : 'I_n) :
  sum_num_occ k <= l < sum_num_occ k.+1 = (ta!_l == enum_val k).
Proof.
case/boolP : (sum_num_occ k <= l < sum_num_occ k.+1) => Hcase.
- exact/esym/eqP/sum_num_occ_enum_val.
- apply/esym/negbTE;apply: contra Hcase => /eqP; exact: enum_val_sum_num_occ.
Qed.

End order_surgery.

End cansort.
