(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import Rssr Reals_ext log2 ssr_ext ssralg_ext.

(** * Additional lemmas about bigops *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section bigop_no_law.

Variables (R : Type) (idx : R) (op : R -> R -> R).

Lemma big_tcast n m (n_m : m = n) (A : finType) F (P : pred {: n.-tuple A}) :
  \big[op/idx]_(p in {: n.-tuple A} | P p) (F p) =
  \big[op/idx]_(p in {: m.-tuple A} | P (tcast n_m p)) (F (tcast n_m p)).
Proof. subst m; apply eq_bigr => ta => /andP[_ H]; by rewrite tcast_id. Qed.

End bigop_no_law.

Section bigop_law.

Variables (R : eqType) (idx : R) (op : Monoid.law idx) .
Variable (A : finType).

Lemma big_neq0 (X : {set A}) (f : A -> R) :
  \big[op/idx]_(t | t \in X) f t != idx -> [exists t, (t \in X) && (f t != idx)].
Proof.
move=> H.
apply negbNE.
rewrite negb_exists.
apply/negP => /forallP abs.
move/negP : H; apply.
rewrite big_mkcond /=.
apply/eqP.
transitivity (\big[op/idx]_(a : A) idx); last by rewrite big1_eq.
apply eq_bigr => a _.
case: ifP => // Hcond.
move: (abs a); by rewrite Hcond /= negbK => /eqP.
Qed.

End bigop_law.

Section removeme.

Variable op : Monoid.com_law 1.

Local Notation "'*%M'" := op (at level 0).
Local Notation "x * y" := (op x y).

Lemma mybig_index_uniq (I : eqType) (i : R) (r : seq I) (E : 'I_(size r) -> R) :
  uniq r ->
  \big[*%M/1]_i E i = \big[*%M/1]_(x <- r) oapp E i (insub (seq.index x r)).
Proof.
move=> Ur.
apply/esym.
rewrite big_tnth.
apply: eq_bigr => j _.
by rewrite index_uniq // valK.
Qed.

End removeme.

Section bigop_add_law.

Variables (R : Type) (idx : R) (op : R -> R -> R) (M : Monoid.add_law idx op).
Variable A : finType.

Lemma Set2sumE (f : A -> R) (card_A : #|A| = 2%nat) :
 \big[M/idx]_(i in A) (f i) = M (f (Set2.a card_A)) (f (Set2.b card_A)).
Proof.
by rewrite /index_enum -enumT Set2.enumE !big_cons big_nil (Monoid.addm0 M) !enum_valP.
Qed.

Lemma big_rV_0 f (P : pred _) : \big[M/idx]_(v in 'rV[A]_0 | P v) f v =
  if P (row_of_tuple [tuple]) then f (row_of_tuple [tuple]) else idx.
Proof.
rewrite -big_map /= /index_enum -enumT /=.
set e := enum _.
rewrite (_ : e = [:: row_of_tuple [tuple]]).
  by rewrite /= big_cons big_nil Monoid.addm0.
rewrite /e.
apply (@eq_from_nth _ (row_of_tuple [tuple])).
  by rewrite -cardE card_matrix muln0 expn0.
move=> i.
rewrite -cardE card_matrix muln0 expn0 ltnS leqn0 => /eqP ->{i}.
rewrite -/e.
destruct e => //.
apply val_inj => /=.
by apply/ffunP => /= -[? []].
Qed.

End bigop_add_law.

Section bigop_add_law_eqtype.

Variable A : finType.

(** Switching from a sum on the domain to a sum on the image of function *)

Definition fin_img (B : eqType) (f : A -> B) : seq B :=
  undup (map f (enum A)).

Variables (R : eqType) (idx : R) (op : R -> R -> R) (M : Monoid.add_law idx op).

Lemma sum_parti (p : seq A) (f : A -> R) : forall g, uniq p ->
  \big[M/idx]_(i <- p) (g i) =
  \big[M/idx]_(r <- undup (map f p)) \big[M/idx]_(i <- p | f i == r) (g i).
Proof.
move Hn : (undup (map f (p))) => n.
move: n p f Hn.
elim => [p f HA F Hp | h t IH p f H F Hp].
- rewrite big_nil.
  suff : p = [::] by move=> ->; rewrite big_nil.
  move/undup_nil : HA => /(congr1 size) /=; rewrite size_map.
  by move/eqP; rewrite size_eq0 => /eqP.
- rewrite big_cons.
  have [preh [pret [H1 [H2 H3]]]] : exists preh pret,
    perm_eq p (preh ++ pret) /\ undup (map f preh) = [:: h] /\ undup (map f pret) = t.
    by apply undup_perm.
  apply (@trans_eq _ _ (\big[M/idx]_(i <- preh ++ pret) F i)); first exact: eq_big_perm.
  apply trans_eq with
   (M (\big[M/idx]_(i <- preh ++ pret | f i == h) F i)
   (\big[M/idx]_(j <- t) \big[M/idx]_(i <- preh ++ pret | f i == j) F i)); last first.
    congr (M _ _).
      apply: eq_big_perm; by rewrite perm_eq_sym.
    apply eq_bigr => i _ /=; apply: eq_big_perm; by rewrite perm_eq_sym.
  have -> :
    \big[M/idx]_(j <- t) \big[M/idx]_(i <- (preh ++ pret) | f i == j) F i =
    \big[M/idx]_(j <- t) \big[M/idx]_(i <- pret | f i == j) F i.
    rewrite [in LHS]big_seq_cond [in RHS]big_seq_cond /=.
    apply/esym/eq_bigr => i Hi.
    rewrite big_cat /=.
    rewrite (_ : \big[M/idx]_(i0 <- preh | f i0 == i) F i0 = idx) ?Monoid.add0m //.
    transitivity (\big[M/idx]_(i0 <- preh | false) F i0); last by rewrite big_pred0.
    rewrite big_seq_cond.
    apply eq_bigl => /= j.
    apply/negP.
    case/andP; move=> Xj_i; move/eqP=> j_preh.
    subst i.
    have Xj_h : f j \in [:: h].
      have H4 : f j \in map f preh by apply/mapP; exists j.
      have : f j \in undup (map f preh) by rewrite mem_undup.
      by rewrite H2.
    have : uniq (h :: t).
      rewrite -H.
      by apply undup_uniq.
    rewrite /= in_cons in_nil orbC /= in Xj_h.
    move/eqP : Xj_h => Xj_h.
    subst h.
    rewrite andbC /= in Hi.
    by rewrite /= Hi.
  rewrite -IH //; last first.
    have : uniq (preh ++ pret) by rewrite -(@perm_eq_uniq _ _ _ H1).
    rewrite cat_uniq.
    case/andP => _; by case/andP.
  have -> : \big[M/idx]_(i <- (preh ++ pret) | f i == h) F i =
    \big[M/idx]_(i <- preh) F i.
    rewrite big_cat /=.
    have -> : \big[M/idx]_(i <- pret | f i == h) F i = idx.
      transitivity (\big[M/idx]_(i0 <- pret | false) F i0); last by rewrite big_pred0.
      rewrite big_seq_cond.
      apply eq_bigl => /= j.
      apply/negP.
      case/andP; move => j_pret; move/eqP => Xj_h.
      subst h.
      have Xj_t : f j \in t.
        have H4 : f j \in map f pret.
        apply/mapP; by exists j.
        have H5 : f j \in undup (map f pret).
        by rewrite mem_undup.
        by rewrite H3 in H5.
      have : uniq (f j :: t) by rewrite -H undup_uniq.
      by rewrite /= Xj_t.
    rewrite Monoid.addm0 big_seq_cond /=.
    symmetry.
    rewrite big_seq_cond /=.
    apply congr_big => //= x.
    case/boolP : (x \in preh) => Y //=.
    symmetry.
    have : f x \in [:: h].
      rewrite -H2 mem_undup.
      apply/mapP; by exists x.
    by rewrite in_cons /= in_nil orbC.
  by rewrite big_cat.
Qed.

(* NB: use finset.partition_big_imset? *)
Lemma sum_parti_finType (f : A -> R) g :
   \big[M/idx]_(i in A) (g i) =
   \big[M/idx]_(r <- fin_img f) \big[M/idx]_(i in A | f i == r) (g i).
Proof.
move: (@sum_parti (enum A) f g) => /=.
rewrite enum_uniq.
move/(_ (refl_equal _)) => IH.
transitivity (\big[M/idx]_(i <- enum A) g i).
  apply congr_big => //.
  by rewrite enumT.
rewrite IH.
apply eq_bigr => i _.
apply congr_big => //; by rewrite enumT.
Qed.

End bigop_add_law_eqtype.

Section bigop_com_law.

Variables (R : Type) (idx : R) (M : Monoid.com_law idx).
Variable A : finType.

Lemma big_union (X1 X2 : {set A}) f :
  [disjoint X2 & X1] ->
  \big[M/idx]_(a | a \in X1 :|: X2) f a =
  M (\big[M/idx]_(a | a \in X1) f a) (\big[M/idx]_(a | a \in X2) f a).
Proof.
move=> Hdisj.
rewrite (@big_setID _ _ _ _ _ X1) /= setUK setDUl setDv set0U.
suff : X2 :\: X1 = X2 by move=> ->.
by apply/setDidPl.
Qed.

Variable B : finType.

(** Big sums lemmas for cartesian products *)

Lemma pair_big_fst (F : {: A * B} -> R) P Q :
  P =1 Q \o fst ->
  \big[M/idx]_(i in A | Q i) \big[M/idx]_(j in B) F (i, j) =
  \big[M/idx]_(i in {: A * B} | P i) F i.
Proof.
move=> /= PQ; rewrite pair_big /=.
apply eq_big.
- case=> /= i1 i2; by rewrite inE andbC PQ.
- by case.
Qed.

Lemma pair_big_snd (F : {: A * B} -> R) P Q :
  P =1 Q \o snd ->
  \big[M/idx]_(i in A) \big[M/idx]_(j in B | Q j) F (i, j) =
  \big[M/idx]_(i in {: A * B} | P i) F i.
Proof.
move=> /= PQ; rewrite pair_big /=.
apply eq_big.
- case=> /= i1 i2; by rewrite PQ.
- by case.
Qed.

Lemma big_rV_prod n f (X : {set 'rV[A * B]_n}) :
  \big[M/idx]_(a in 'rV[A * B]_n | a \in X) f a =
  \big[M/idx]_(a in {: 'rV[A]_n * 'rV[B]_n} | (prod_rV a) \in X) f (prod_rV a).
Proof.
rewrite (reindex_onto (@rV_prod _ _ _) (@prod_rV _ _ _)) //=; last first.
  move=> ? _; by rewrite prod_rVK.
apply eq_big => [?|? _]; by rewrite rV_prodK // eqxx andbC.
Qed.

Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.

Lemma big_rV_1 f g (P : pred _) (Q : pred _):
  (forall i : 'rV[A]_1, f i = g (i ``_ ord0)) ->
  (forall i : 'rV[A]_1, P i = Q (i ``_ ord0)) ->
  \big[M/idx]_(i in 'rV[A]_1 | P i) f i = \big[M/idx]_(i in A | Q i) g i.
Proof.
move=> FG PQ.
rewrite (reindex_onto (fun i => \row_(j < 1) i) (fun p => p ``_ ord0)) /=; last first.
  move=> m Pm.
  apply/matrixP => a b; rewrite {a}(ord1 a) {b}(ord1 b); by rewrite mxE.
apply eq_big => a.
  by rewrite PQ mxE eqxx andbT.
by rewrite FG !mxE.
Qed.

Lemma big_singl_rV (f : A -> R) k :
  \big[M/idx]_(i in A) f i = k -> \big[M/idx]_(i in 'rV[A]_1) f (i ``_ ord0) = k.
Proof.
move=> <-.
rewrite (reindex_onto (fun j => \row_(i < 1) j) (fun p => p ``_ ord0)) /=.
- apply eq_big => a; first by rewrite mxE eqxx inE.
  move=> _; by rewrite mxE.
- move=> t _; apply/matrixP => a b; by rewrite (ord1 a) (ord1 b) mxE.
Qed.

Lemma big_1_tuple F G P Q :
  (forall i : 1.-tuple A, F i = G (thead i)) ->
  (forall i : 1.-tuple A, P i = Q (thead i)) ->
  \big[M/idx]_(i in {: 1.-tuple A} | P i) F i = \big[M/idx]_(i in A | Q i) G i.
Proof.
move=> FG PQ.
rewrite (reindex_onto (fun i => [tuple of [:: i]]) (fun p => thead p)) /=; last first.
  case/tupleP => h t X; by rewrite theadE (tuple0 t).
apply eq_big => x //.
by rewrite (PQ [tuple x]) /= theadE eqxx andbC.
move=> X; by rewrite FG.
Qed.

Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.

Lemma big_rV_cons n (F : 'rV[A]_n.+1 -> R) (a : A) :
  \big[M/idx]_(v in 'rV[A]_n) (F (row_mx (\row_(k < 1) a) v)) =
  \big[M/idx]_(v in 'rV[A]_n.+1 | v ``_ ord0 == a) (F v).
Proof.
symmetry.
rewrite (reindex_onto (fun j : 'rV[A]_n => row_mx (\row_(k < 1) a) j)
  (fun p : 'rV[A]_n.+1 => rbehead p)) /=; last first.
  move=> m Hm.
  apply/matrixP => i j; rewrite {i}(ord1 i).
  rewrite row_mx_rbehead //.
  by apply/eqP.
apply eq_bigl => /= x.
by rewrite rbehead_row_mx eqxx andbT row_mx_row_ord0 eqxx.
Qed.

Lemma big_rV_behead n (F : 'rV[A]_n.+1 -> R) (w : 'rV[A]_n) :
  \big[M/idx]_(a in A) (F (row_mx (\row_(k < 1) a) w)) =
  \big[M/idx]_(v in 'rV[A]_n.+1 | rbehead v == w) (F v).
Proof.
apply/esym.
rewrite (reindex_onto (fun p => row_mx (\row_(k < 1) p) w) (fun p => p ``_ ord0) ) /=; last first.
  move=> i /eqP <-.
  apply/matrixP => a b; rewrite {a}(ord1 a).
  by rewrite row_mx_rbehead.
apply eq_bigl => /= a.
by rewrite rbehead_row_mx eqxx /= row_mx_row_ord0 eqxx.
Qed.

Lemma big_rV_cons_behead_support n (F : 'rV[A]_n.+1 -> R) (X1 : {set A}) (X2 : {set {: 'rV[A]_n}}) :
  \big[M/idx]_(a in X1) \big[M/idx]_(v in X2) (F (row_mx (\row_(k < 1) a) v))
  =
  \big[M/idx]_(w in 'rV[A]_n.+1 | (w ``_ ord0 \in X1) && (rbehead w \in X2)) (F w).
Proof.
apply/esym.
rewrite (@partition_big _ _ _ _ _ _ (fun x : 'rV[A]_n.+1 => x ``_ ord0) (mem X1)) //=.
- apply eq_bigr => i Hi.
  rewrite (reindex_onto (fun j : 'rV[A]_n => row_mx (\row_(k < 1) i) j) rbehead) /=; last first.
    move=> j Hj.
    case/andP : Hj => Hj1 /eqP => <-.
    apply/matrixP => a b; rewrite {a}(ord1 a).
    by rewrite row_mx_rbehead.
  apply congr_big => // x /=.
  by rewrite rbehead_row_mx eqxx andbT row_mx_row_ord0 eqxx Hi andbT.
move=> i; by case/andP.
Qed.

Lemma big_rV_cons_behead n (F : 'rV[A]_n.+1 -> R) (P1 : pred A) (P2 : pred 'rV[A]_n) :
  \big[M/idx]_(i in A | P1 i) \big[M/idx]_(j in 'rV[A]_n | P2 j) (F (row_mx (\row_(k < 1) i) j))
  =
  \big[M/idx]_(p in 'rV[A]_n.+1 | (P1 (p ``_ ord0)) && (P2 (rbehead p)) ) (F p).
Proof.
symmetry.
rewrite (@partition_big _ _ _ _ _ _ (fun x : 'rV[A]_n.+1 => x ``_ ord0)
  (fun x : A => P1 x)) //=.
- apply eq_bigr => i Hi.
  rewrite (reindex_onto (fun j : 'rV[A]_n => row_mx (\row_(k < 1) i) j) rbehead) /=; last first.
    move=> j Hj.
    case/andP : Hj => Hj1 /eqP => <-.
    apply/matrixP => a b; rewrite {a}(ord1 a).
    by rewrite row_mx_rbehead.
  apply congr_big => // x /=.
  by rewrite row_mx_row_ord0 rbehead_row_mx 2!eqxx Hi !andbT.
move=> i; by case/andP.
Qed.

End bigop_com_law.

Section MyPartitions.

Variables (R : Type) (idx : R) (op : Monoid.com_law idx).

Variables T I : finType.

Lemma big_bigcup_partition (F : I -> {set T}) E (V : {set I}):
  (forall i j, i != j -> [disjoint F i & F j]) ->
  \big[op/idx]_(x in \bigcup_(i in V) F i) E x =
    \big[op/idx]_(i in V) \big[op/idx]_(x in F i) E x.
Proof.
move=> disjF; pose Q := [set F i | i in V & F i != set0].
have trivP: trivIset Q.
  apply/trivIsetP=> _ _ /imsetP[i _ ->] /imsetP[j _ ->] neqFij.
  by apply: disjF; apply: contraNneq neqFij => ->.
have ->: \bigcup_(i in V) F i = cover Q.
  apply/esym.
  rewrite cover_imset big_mkcond /=.
  apply/esym.
  rewrite big_mkcond /=.
  apply: eq_bigr => i _.
  case: ifP.
    rewrite inE => -> /=.
    by case: ifP => // /eqP.
  by rewrite inE => ->.
rewrite big_trivIset // big_imset => [|i j _ /setIdP[_ notFj0] eqFij].
  rewrite big_mkcond [in X in _ = X]big_mkcond.
  apply: eq_bigr => i _.
  rewrite inE.
  case: ifP.
    by case/andP=> ->.
  move/negbT.
  rewrite negb_and.
  case/orP.
    by move/negbTE => ->.
  rewrite negbK => /eqP Fi.
  case: ifP => //.
  by rewrite Fi big_set0.
by apply: contraNeq (disjF _ _) _; rewrite -setI_eq0 eqFij setIid.
Qed.

End MyPartitions.

Section big_tuple_ffun.

Import Monoid.Theory.

Variable R : Type.
Variable times : Monoid.mul_law 0.
Local Notation "*%M" := times (at level 0).
Variable plus : Monoid.add_law 0 *%M.
Local Notation "+%M" := plus (at level 0).

Lemma big_tuple_ffun (I J : finType) (F : {ffun I -> J} -> R)
  (G : _ -> _ -> _) (jdef : J) (idef : I) :
  \big[+%M/0]_(j : #|I|.-tuple J) G (F [ffun x => tnth j (enum_rank x)]) (nth jdef j 0)
    = \big[+%M/0]_(f : {ffun I -> J}) G (F f) (f (nth idef (enum I) 0)).
Proof.
rewrite (reindex_onto (fun y => fgraph y) (fun p => [ffun x => tnth p (enum_rank x)])); last first.
  move=> t _; by apply/eq_from_tnth => i; rewrite tnth_fgraph ffunE enum_valK.
apply eq_big.
  move=> f /=; apply/eqP/ffunP => i; by rewrite ffunE tnth_fgraph enum_rankK.
move=> f _.
congr (G (F _) _).
  apply/ffunP => i; by rewrite ffunE tnth_fgraph enum_rankK.
have @zero : 'I_#|I| by exists O; apply/card_gt0P; exists idef.
transitivity (tnth (fgraph f) zero).
  apply set_nth_default; by rewrite size_tuple ltn_ord.
rewrite tnth_fgraph; congr (f _).
by apply enum_val_nth.
Qed.

End big_tuple_ffun.

Lemma bigcup_set0 n i (T T' : finType) (D : 'I_n -> {set T'}) (A : T' -> 'I_n -> {set T}) :
  (exists t', (t' \in D i) && (A t' i != set0)) ->
  \bigcup_(t' in D i) A t' i == set0 -> D i == set0.
Proof.
move=> abs.
move/set0Pn => Hset0.
apply/set0Pn.
move=> abs'; apply Hset0 => {Hset0}.
case: abs' => t' t'i.
case: abs => t'' /andP[t''i].
case/set0Pn => t tA.
exists t; apply/bigcupP; by exists t''.
Qed.
