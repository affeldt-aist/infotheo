(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext.

(** * Additional lemmas about bigops *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section bigop_no_law.

Variables (R : Type) (idx : R) (op : R -> R -> R).

Lemma big_tcast n m (n_m : n = m) (A : finType) F (P : pred {: n.-tuple A}) :
  \big[op/idx]_(p in {: n.-tuple A} | P p) F p =
  \big[op/idx]_(p in {: m.-tuple A} | P (tcast (esym n_m) p)) F (tcast (esym n_m) p).
Proof. subst m; apply eq_bigr => ta => /andP[_ H]; by rewrite tcast_id. Qed.

Lemma big_cast_rV n m (n_m : n = m) (A : finType) F (P : pred {: 'rV[A]_n}) :
  \big[op/idx]_(p in {: 'rV_n} | P p) F p =
  \big[op/idx]_(p in {: 'rV_m} | P (castmx (erefl, esym n_m) p)) F (castmx (erefl, esym n_m) p).
Proof. by subst m; apply eq_bigr => ta => /andP[_ H]. Qed.

End bigop_no_law.
Arguments big_tcast {R} {idx} {op} {n} {m} _ {A} _ _.
Arguments big_cast_rV {R} {idx} {op} {n} {m} _ {A} _ _.

Section bigop_add_law.

Variables (R : Type) (idx : R) (op : R -> R -> R) (M : Monoid.add_law idx op).
Variable A : finType.

Lemma Set2sumE (f : A -> R) (card_A : #|A| = 2%nat) :
 \big[M/idx]_(i in A) (f i) = M (f (Set2.a card_A)) (f (Set2.b card_A)).
Proof.
by rewrite /index_enum -enumT Set2.enumE !big_cons big_nil (Monoid.addm0 M) !enum_valP.
Qed.

Local Open Scope ring_scope.
Lemma big_rV_0 f (P : pred 'rV[A]_0) (a : A) : \big[M/idx]_(v in 'rV[A]_0 | P v) f v =
  if P (\row_(i < 0) a) then f (\row_(i < 0) a) else idx.
Proof.
rewrite -big_map /= /index_enum -enumT /=.
set e := enum _.
rewrite (_ : e = [:: \row_(i < 0) a]).
  by rewrite /= big_cons big_nil Monoid.addm0.
rewrite /e.
apply (@eq_from_nth _ (\row_(i < 0) a)).
  by rewrite -cardE card_matrix muln0 expn0.
move=> i.
rewrite -cardE card_matrix muln0 expn0 ltnS leqn0 => /eqP ->{i}.
rewrite -/e.
destruct e => //.
apply val_inj => /=.
by apply/ffunP => /= -[? []].
Qed.

Lemma big_tuple_0 f (P : pred _) : \big[M/idx]_(v in 'rV[A]_0 | P v) f v =
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

Arguments big_rV_0 {R} {idx} {op} {M} {A} _ _ _.

Section bigop_add_law_eqtype.

Variables (A : finType) (B : eqType).

(** Switching from a sum on the domain to a sum on the image of function *)

Definition fin_img (f : A -> B) : seq B := undup (map f (enum A)).

Variables (R : eqType) (idx : R) (op : R -> R -> R) (M : Monoid.add_law idx op).

Lemma sum_parti (p : seq A) (f : A -> B) : forall g, uniq p ->
  \big[M/idx]_(i <- p) (g i) =
  \big[M/idx]_(r <- undup (map f p)) \big[M/idx]_(i <- p | f i == r) (g i).
Proof.
move Hn : (undup (map f (p))) => n.
elim: n p f Hn => [p f H F ? | b bs IH p f H F ?].
  rewrite big_nil.
  suff -> : p = [::] by rewrite big_nil.
  move/undup_nil : H => /(congr1 size) /=; rewrite size_map.
  by move/eqP; rewrite size_eq0 => /eqP.
rewrite big_cons.
have [h [t [H1 [H2 H3]]]] : exists h t,
  perm_eq p (h ++ t) /\ undup (map f h) = [:: b] /\ undup (map f t) = bs.
  exact: undup_perm.
transitivity (\big[M/idx]_(i <- h ++ t) F i); first exact: perm_big.
transitivity (M
    (\big[M/idx]_(i <- h ++ t | f i == b) F i)
    (\big[M/idx]_(j <- bs) \big[M/idx]_(i <- h ++ t | f i == j) F i)); last first.
  congr (M _ _).
  by apply: perm_big; rewrite perm_sym.
  by apply eq_bigr => b0 _ /=; apply: perm_big; rewrite perm_sym.
have -> : \big[M/idx]_(j <- bs) \big[M/idx]_(i <- h ++ t | f i == j) F i =
  \big[M/idx]_(j <- bs) \big[M/idx]_(i <- t | f i == j) F i.
  rewrite [in LHS]big_seq_cond [in RHS]big_seq_cond /=.
  apply/esym/eq_bigr => b0; rewrite andbT => b0bs.
  rewrite big_cat /=.
  rewrite (_ : \big[M/idx]_(i0 <- h | f i0 == b0) F i0 = idx); first by rewrite Monoid.add0m.
  transitivity (\big[M/idx]_(i0 <- h | false) F i0); last by rewrite big_pred0.
  rewrite big_seq_cond; apply eq_bigl => /= a.
  apply/negP => /andP[ah /eqP fai]; subst b0.
  have fab : f a \in [:: b].
    have H' : f a \in map f h by apply/mapP; exists a.
    have : f a \in undup (map f h) by rewrite mem_undup.
    by rewrite H2.
  have : uniq (b :: bs) by rewrite -H undup_uniq.
  move: fab; rewrite /= in_cons in_nil orbC /= => /eqP ?; subst b.
  by rewrite b0bs.
rewrite -IH //; last first.
  have : uniq (h ++ t) by rewrite -(perm_uniq H1).
  by rewrite cat_uniq => /and3P[].
suff -> : \big[M/idx]_(i <- h ++ t | f i == b) F i = \big[M/idx]_(i <- h) F i.
  by rewrite big_cat.
rewrite big_cat /=.
have -> : \big[M/idx]_(i <- t | f i == b) F i = idx.
  transitivity (\big[M/idx]_(i0 <- t | false) F i0); last by rewrite big_pred0.
  rewrite big_seq_cond; apply eq_bigl => /= a.
  apply/negP => /andP[ta /eqP fab]; subst b.
  have fabs : f a \in bs.
    have : f a \in undup (map f t) by rewrite mem_undup; apply/mapP; exists a.
    by rewrite H3.
  have : uniq (f a :: bs) by rewrite -H undup_uniq.
  by rewrite /= fabs.
rewrite Monoid.addm0 big_seq_cond /=.
apply/esym.
rewrite big_seq_cond /=; apply congr_big => //= a.
rewrite andbT.
case/boolP : (a \in h) => ah //=; apply/esym.
have : f a \in [:: b] by rewrite -H2 mem_undup; apply/mapP; exists a.
by rewrite in_cons /= in_nil orbC.
Qed.

(* NB: use finset.partition_big_imset? *)
Lemma sum_parti_finType (f : A -> B) g :
   \big[M/idx]_(i in A) (g i) =
   \big[M/idx]_(r <- fin_img f) \big[M/idx]_(i in A | f i == r) (g i).
Proof.
move: (@sum_parti (enum A) f g) => /=.
rewrite enum_uniq.
move/(_ isT) => IH.
transitivity (\big[M/idx]_(i <- enum A) g i); first by rewrite enumT.
rewrite IH.
apply eq_bigr => i _.
apply congr_big => //; by rewrite enumT.
Qed.

End bigop_add_law_eqtype.

Section big_pred1_inj.
Variables (R : Type) (idx : R) (op : Monoid.law idx).
Lemma big_pred1_inj (A C : finType) h i (k : A -> C) : injective k ->
  \big[op/idx]_(a | k a == k i) h a = h i.
Proof. by move=> ?; rewrite (big_pred1 i) // => ?; rewrite eqtype.inj_eq. Qed.
End big_pred1_inj.

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
move=> /= PQ; rewrite pair_big /=; apply eq_big; last by case.
case=> /= ? ?; by rewrite inE andbC PQ.
Qed.

Lemma pair_big_snd (F : {: A * B} -> R) P Q :
  P =1 Q \o snd ->
  \big[M/idx]_(i in A) \big[M/idx]_(j in B | Q j) F (i, j) =
  \big[M/idx]_(i in {: A * B} | P i) F i.
Proof.
move=> /= PQ; rewrite pair_big /=; apply eq_big; last by case.
case=> /= ? ?; by rewrite PQ.
Qed.

Lemma big_setX (a : {set A}) (b : {set B}) f :
  \big[M/idx]_(x in setX a b) f x = \big[M/idx]_(x in a) \big[M/idx]_(y in b) f (x, y).
Proof.
rewrite (eq_bigl (fun x => (x.1 \in a) && (x.2 \in b))); last first.
  by case=> x y; rewrite in_setX.
rewrite (eq_bigr (fun x => f (x.1, x.2))); last by case.
by rewrite -(pair_big _ _ (fun a b => f (a, b))).
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
  apply/rowP => a; by rewrite {a}(ord1 a) mxE.
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
- move=> t _; apply/rowP => a; by rewrite (ord1 a) mxE.
Qed.

(*Lemma big_1_tuple F G P Q :
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
Qed.*)

Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.

Lemma big_rV_cons n (F : 'rV[A]_n.+1 -> R) (a : A) (i0 : 'I_n.+1) : i0 = ord0 ->
  \big[M/idx]_(v in 'rV[A]_n) (F (row_mx (\row_(k < 1) a) v)) =
  \big[M/idx]_(v in 'rV[A]_n.+1 | v ``_ i0 == a) (F v).
Proof.
move=> i00.
rewrite [in RHS](reindex_onto (row_mx (\row_(k < 1) a)) rbehead) /=; last first.
  move=> m /eqP <-; by rewrite i00 row_mx_rbehead.
apply eq_bigl => ?; by rewrite i00 rbehead_row_mx eqxx andbT row_mx_row_ord0 eqxx.
Qed.

Lemma big_rV_behead n (F : 'rV[A]_n.+1 -> R) (w : 'rV[A]_n) :
  \big[M/idx]_(a in A) (F (row_mx (\row_(k < 1) a) w)) =
  \big[M/idx]_(v in 'rV[A]_n.+1 | rbehead v == w) (F v).
Proof.
rewrite [in RHS](reindex_onto
  (fun p => row_mx (\row_(k < 1) p) w) (fun p => p ``_ ord0) ) /=; last first.
  move=> i /eqP <-; by rewrite row_mx_rbehead.
apply eq_bigl => ?; by rewrite rbehead_row_mx eqxx /= row_mx_row_ord0 eqxx.
Qed.

Lemma big_rV_cons_behead_support n (F : 'rV[A]_n.+1 -> R)
  (X1 : {set A}) (X2 : {set {: 'rV[A]_n}}) :
  \big[M/idx]_(a in X1) \big[M/idx]_(v in X2) (F (row_mx (\row_(k < 1) a) v)) =
  \big[M/idx]_(w in 'rV[A]_n.+1 | (w ``_ ord0 \in X1) && (rbehead w \in X2)) (F w).
Proof.
rewrite [in RHS](partition_big (fun x : 'rV_n.+1 => x ``_ ord0) (mem X1)) /=; last first.
  by move=> i /andP[].
apply eq_bigr => i Hi.
rewrite (reindex_onto (fun j => row_mx (\row_(k < 1) i) j) rbehead) /=; last first.
  move=> j /andP[] => _ /eqP => <-; by rewrite row_mx_rbehead.
apply eq_big => //= x; by rewrite row_mx_row_ord0 rbehead_row_mx !eqxx Hi !andbT.
Qed.

Lemma big_rV_cons_behead n (F : 'rV[A]_n.+1 -> R)
  (P1 : pred A) (P2 : pred 'rV[A]_n) :
  \big[M/idx]_(i in A | P1 i)
    \big[M/idx]_(j in 'rV[A]_n | P2 j) (F (row_mx (\row_(k < 1) i) j)) =
  \big[M/idx]_(p in 'rV[A]_n.+1 | (P1 (p ``_ ord0)) && (P2 (rbehead p)) ) (F p).
Proof.
rewrite [in RHS](partition_big (fun x : 'rV_n.+1 => x ``_ ord0) P1) /=; last first.
  by move=> i /andP[].
apply eq_bigr => i Hi.
rewrite (reindex_onto (fun j => row_mx (\row_(k < 1) i) j) rbehead) /=; last first.
    move=> j /andP[] Hj1 /eqP => <-; by rewrite row_mx_rbehead.
apply eq_big => //= x; by rewrite row_mx_row_ord0 rbehead_row_mx 2!eqxx Hi !andbT.
Qed.

Lemma big_rV_belast_last n (F : 'rV[A]_n.+1 -> R)
  (P1 : pred 'rV[A]_n) (P2 : pred A) :
  \big[M/idx]_(i in 'rV[A]_n | P1 i)
    \big[M/idx]_(j in A | P2 j) (F (castmx (erefl, addn1 n) (row_mx i (\row_(k < 1) j)))) =
  \big[M/idx]_(p in 'rV[A]_n.+1 | (P1 (rbelast p)) && (P2 (rlast p)) ) (F p).
Proof.
rewrite [in RHS](partition_big (fun x : 'rV_n.+1 => rlast x) P2) /=; last first.
  by move=> i /andP[].
rewrite exchange_big.
apply eq_bigr => i Hi.
rewrite (reindex_onto (fun j => (castmx (erefl 1%nat, addn1 n) (row_mx j (\row_(k < 1) i)))) rbelast) /=; last first.
    move=> j /andP[] Hj1 /eqP => <-; by rewrite row_mx_rbelast.
apply eq_big => //= x.
by rewrite row_mx_row_ord_max rbelast_row_mx 2!eqxx !andbT Hi andbT.
Qed.

End bigop_com_law.
Arguments pair_big_fst {R} {idx} {M} {A} {B} _.
Arguments pair_big_snd {R} {idx} {M} {A} {B} _.
Arguments big_rV_belast_last {R} {idx} {M} {A} {n} _ _ _.
Arguments big_rV_cons_behead {R} {idx} {M} {A} {n} _ _ _.

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
