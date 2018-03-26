(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import Rssr Reals_ext log2 ssr_ext ssralg_ext tuple_prod.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** Additional lemmas about bigop (in particular, instantiation to Coq reals) *)

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
  move/undup_nil_inv : HA.
  move/map_nil_inv => ->.
  by rewrite big_nil.
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
  \big[M/idx]_(a in {: 'rV[A]_n * 'rV[B]_n} | (prod_tuple a) \in X) f (prod_tuple a).
Proof.
rewrite (reindex_onto (@tuple_prod _ _ _) (@prod_tuple _ _ _)) //=; last first.
  move=> ? _; by rewrite prod_tupleK.
apply eq_big => [?|? _].
  by rewrite tuple_prodK eqxx andbC.
by rewrite tuple_prodK.
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

Section big_tuple_ffun.

Import Monoid.Theory.

Variable R : Type.
Variable times : Monoid.mul_law 0.
Local Notation "*%M" := times (at level 0).
Variable plus : Monoid.add_law 0 *%M.
Local Notation "+%M" := plus (at level 0).

Lemma big_tuple_ffun (I J : finType) (F : {ffun I -> J} -> R)
  (G : _ -> _ -> _) (jdef : J) (idef : I) :
  \big[+%M/0]_(j : #|I|.-tuple J) G (F (Finfun j)) (nth jdef j 0)
    = \big[+%M/0]_(f : {ffun I -> J}) G (F f) (f (nth idef (enum I) 0)).
Proof.
rewrite (reindex_onto (fun y => fgraph y) (fun p => Finfun p)) //.
apply eq_big; first by case => t /=; by rewrite eqxx.
move=> i _.
congr (G _ _).
  by case: i.
case: i => [ [tval Htval] ].
rewrite [fgraph _]/= -(nth_map idef jdef); last first.
  rewrite -cardE; apply/card_gt0P; by exists idef.
by rewrite -codomE codom_ffun.
Qed.

End big_tuple_ffun.

Local Open Scope reals_ext_scope.

(** * Instantiation of canonical big operators with Coq reals *)

Notation "\rsum_ ( i <- r | P ) F" := (\big[Rplus/R0]_(i <- r | P%B) F)
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \rsum_ ( i  <-  r  |  P ) '/  '  F ']'").
Notation "\rsum_ ( i <- r ) F" :=  (\big[Rplus/R0]_(i <- r) F)
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \rsum_ ( i  <-  r ) '/  '  F ']'").
Notation "\rsum_ ( m <= i < n | P ) F" := (\big[Rplus/R0]_(m <= i < n | P%B) F)
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \rsum_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Notation "\rsum_ ( m <= i < n ) F" := (\big[Rplus/R0]_(m <= i < n) F)
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \rsum_ ( m  <=  i  <  n ) '/  '  F ']'").
Notation "\rsum_ ( i | P ) F" := (\big[Rplus/R0]_(i | P%B) F)
  (at level 41, F at level 41, i at level 50,
           format "'[' \rsum_ ( i  |  P ) '/  '  F ']'").
Notation "\rsum_ ( i : t | P ) F" := (\big[Rplus/R0]_(i : t | P%B) F)
  (at level 41, F at level 41, i at level 50,
           only parsing).
Notation "\rsum_ ( i : t ) F" := (\big[Rplus/R0]_(i : t) F)
  (at level 41, F at level 41, i at level 50,
           only parsing).
Notation "\rsum_ ( i < n | P ) F" := (\big[Rplus/R0]_(i < n | P%B) F)
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \rsum_ ( i  <  n  |  P ) '/  '  F ']'").
Notation "\rsum_ ( i < n ) F" := (\big[Rplus/R0]_(i < n) F)
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \rsum_ ( i  <  n ) '/  '  F ']'").
Notation "\rsum_ ( i 'in' A | P ) F" := (\big[Rplus/R0]_(i in A | P%B) F)
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \rsum_ ( i  'in'  A  |  P ) '/  '  F ']'").
Notation "\rsum_ ( i 'in' A ) F" := (\big[Rplus/R0]_(i in A) F)
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \rsum_ ( i  'in'  A ) '/  '  F ']'").

Notation "\rprod_ ( i <- r | P ) F" := (\big[Rmult/R1]_(i <- r | P%B) F)
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \rprod_ ( i  <-  r  |  P ) '/  '  F ']'").
Notation "\rprod_ ( i <- r ) F" :=  (\big[Rmult/R1]_(i <- r) F)
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \rprod_ ( i  <-  r ) '/  '  F ']'").
Notation "\rprod_ ( m <= i < n | P ) F" := (\big[Rmult/R1]_(m <= i < n | P%B) F)
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \rprod_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Notation "\rprod_ ( m <= i < n ) F" := (\big[Rmult/R1]_(m <= i < n) F)
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \rprod_ ( m  <=  i  <  n ) '/  '  F ']'").
Notation "\rprod_ ( i | P ) F" := (\big[Rmult/R1]_(i | P%B) F)
  (at level 41, F at level 41, i at level 50,
           format "'[' \rprod_ ( i  |  P ) '/  '  F ']'").
Notation "\rprod_ ( i : t | P ) F" := (\big[Rmult/R1]_(i : t | P%B) F)
  (at level 41, F at level 41, i at level 50,
           only parsing).
Notation "\rprod_ ( i : t ) F" := (\big[Rmult/R1]_(i : t) F)
  (at level 41, F at level 41, i at level 50,
           only parsing).
Notation "\rprod_ ( i < n | P ) F" := (\big[Rmult/R1]_(i < n | P%B) F)
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \rprod_ ( i  <  n  |  P ) '/  '  F ']'").
Notation "\rprod_ ( i < n ) F" := (\big[Rmult/R1]_(i < n) F)
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \rprod_ ( i  <  n ) '/  '  F ']'").
Notation "\rprod_ ( i 'in' A | P ) F" := (\big[Rmult/R1]_(i in A | P%B) F)
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \rprod_ ( i  'in'  A  |  P ) '/  '  F ']'").
Notation "\rprod_ ( i 'in' A ) F" := (\big[Rmult/R1]_(i in A) F)
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \rprod_ ( i  'in'  A ) '/  '  F ']'").

Canonical addR_monoid := Monoid.Law addRA add0R addR0.
Canonical addR_comoid := Monoid.ComLaw addRC.
Canonical mulR_monoid := Monoid.Law mulRA mul1R mulR1.
Canonical mulR_muloid := Monoid.MulLaw mul0R mulR0.
Canonical mulR_comoid := Monoid.ComLaw mulRC.
Canonical addR_addoid := Monoid.AddLaw mulRDl mulRDr.

Lemma iter_Rplus n r : ssrnat.iter n (Rplus r) 0 = INR n * r.
Proof.
elim : n r => [r /= | m IHm r]; first by rewrite mul0R.
rewrite iterS IHm S_INR; field.
Qed.

Lemma iter_Rmult n p : ssrnat.iter n (Rmult p) 1 = p ^ n.
Proof. elim : n p => // n0 IH p0 /=; by rewrite IH. Qed.

Lemma morph_Ropp : {morph [eta Ropp] : x y / x + y}.
Proof. by move=> x y /=; field. Qed.

Lemma morph_plus_INR : {morph INR : x y / (x + y)%nat >-> x + y}.
Proof. move=> x y /=; by rewrite plus_INR. Qed.

Lemma morph_mult_INR : {morph INR : x y / (x * y)%nat >-> x * y}.
Proof. move=> x y /=; by rewrite mult_INR. Qed.

Lemma morph_mulRDr a : {morph [eta Rmult a] : x y / x + y}.
Proof. move=> * /=; by rewrite mulRDr. Qed.

Lemma morph_mulRDl a : {morph Rmult^~ a : x y / x + y}.
Proof. move=> x y /=; by rewrite mulRDl. Qed.

Lemma morph_exp2_plus : {morph [eta exp2] : x y / x + y >-> x * y}.
Proof. move=> ? ? /=; by rewrite -exp2_plus. Qed.

(** Rle, Rlt lemmas for big sums of reals *)

Section ler_ltr_rsum.

Variables (A : finType) (f g : A -> R) (P Q : pred A).

Lemma ler_rsum : (forall i, P i -> f i <= g i) ->
  \rsum_(i | P i) f i <= \rsum_(i | P i) g i.
Proof.
move=> H; elim: (index_enum _) => [|h t IH].
- rewrite !big_nil; exact/Rle_refl.
- rewrite !big_cons; case: ifP => // Ph; apply Rplus_le_compat => //; exact/H.
Qed.

Lemma ler_rsum_support (X : {set A}) :
  (forall i, i \in X -> P i -> f i <= g i) ->
  \rsum_(i in X | P i) f i <= \rsum_(i in X | P i) g i.
Proof.
move=> H.
elim: (index_enum _) => [| hd tl IH].
- rewrite !big_nil; exact/Rle_refl.
- rewrite !big_cons.
  set cond := _ && _; move Hcond : cond => []; subst cond => //.
  apply Rplus_le_compat => //.
  case/andP : Hcond; exact: H.
Qed.

Lemma ler_rsum_l : (forall i, P i -> f i <= g i) ->
  (forall i, Q i -> 0 <= g i) ->
  (forall i, P i -> Q i) ->
  \rsum_(i | P i) f i <= \rsum_(i | Q i) g i.
Proof.
move=> f_g Qg H.
elim: (index_enum _) => [| h t IH].
- rewrite !big_nil; by apply Rle_refl.
- rewrite !big_cons /=; case: ifP => [Ph|Ph].
    rewrite (H _ Ph); apply Rplus_le_compat => //; exact: f_g.
  case: ifP => // Qh; apply: Rle_trans; [apply IH|].
  rewrite -{1}[X in X <= _](add0R _); exact/Rplus_le_compat_r/Qg.
Qed.

Lemma ler_rsum_l_support (R : pred A) :
  (forall a, 0 <= f a) -> (forall i, P i -> Q i) ->
  \rsum_(i in R | P i) f i <= \rsum_(i in R | Q i) f i.
Proof.
move=> Hf P_Q.
elim: (index_enum _) => [|h t IH].
- rewrite !big_nil; exact/Rle_refl.
- rewrite !big_cons.
  set cond := _ \in _; move Hcond : cond => []; subst cond => //=.
  case: ifP => // HP.
  + case: ifP => [HQ|].
    * exact: Rplus_le_compat_l.
    * by rewrite (P_Q _ HP).
  + case: ifP => // HQ.
    rewrite -[X in X <= _]add0R; exact/Rplus_le_compat.
Qed.

Lemma ltr_rsum_support (X : {set A}) : (0 < #|X|)%nat ->
  (forall i, i \in X -> f i < g i) ->
  \rsum_(i in X) f i < \rsum_(i in X) g i.
Proof.
move Hn : #|X| => n.
elim: n X Hn => // n IH X Hn _ H.
move: (ltn0Sn n); rewrite -Hn card_gt0; case/set0Pn => a0 Ha0.
rewrite (@big_setD1 _ _ _ _ a0 _ f) //= (@big_setD1 _ _ _ _ a0 _ g) //=.
case: n => [|n] in IH Hn.
  rewrite (_ : X :\ a0 = set0); last first.
    move: Hn.
    by rewrite (cardsD1 a0) Ha0 /= add1n => -[] /eqP; rewrite cards_eq0 => /eqP.
  rewrite !big_set0 2!addR0; exact: H.
apply Rplus_lt_compat; first exact/H.
apply IH => //.
- move: Hn; rewrite (cardsD1 a0) Ha0 /= add1n; by case.
- move=> a; rewrite in_setD inE => /andP[_ ?]; exact: H.
Qed.

End ler_ltr_rsum.

Lemma ler_rsum_Rabs (A : finType) f : Rabs (\rsum_(a : A) f a) <= \rsum_(a : A) Rabs (f a).
Proof.
elim: (index_enum _) => [|h t IH].
  rewrite 2!big_nil Rabs_R0; by apply Rle_refl.
rewrite 2!big_cons.
apply (Rle_trans _ (Rabs (f h) + Rabs (\rsum_(j <- t) f j)));
  [exact/Rabs_triang |exact/Rplus_le_compat_l].
Qed.

Lemma ler_rsum_predU (A : finType) (f : A -> R) (P Q : pred A) :
  (forall a, 0 <= f a) -> \rsum_(i in A | [predU P & Q] i) f i <=
  \rsum_(i in A | P i) f i + \rsum_(i in A | Q i) f i.
Proof.
move=> Hf.
elim: (index_enum _) => [|h t IH /=]; first by rewrite !big_nil /=; fourier.
rewrite !big_cons /=.
case: ifPn => /=.
- case/orP => [hP | hQ].
  + move: hP; rewrite unfold_in => ->.
    case: ifP => // Qh.
    * rewrite -addRA; apply Rplus_le_compat_l.
      eapply Rle_trans; first exact/IH.
      have : forall a b c, 0 <= c -> a + b <= a + (c + b) by move=> *; fourier.
      apply; by apply Hf.
    * rewrite -addRA; apply Rplus_le_compat_l.
      eapply Rle_trans; first exact/IH.
      by apply Req_le.
  + move: hQ; rewrite unfold_in => ->.
    case: ifP => // Ph.
    * rewrite -addRA; apply Rplus_le_compat_l.
      eapply Rle_trans; first exact/IH.
      have : forall a b c, 0 <= c -> a + b <= a + (c + b) by move=> *; fourier.
      apply; by apply Hf.
    * rewrite -(Rplus_comm (f h + _)) -addRA; apply Rplus_le_compat_l.
      eapply Rle_trans; first exact/IH.
      by rewrite Rplus_comm; apply Req_le.
- rewrite negb_or.
  case/andP.
  rewrite !unfold_in; move/negbTE => -> /negbTE ->.
  exact/IH.
Qed.

Lemma rsumr_ge0 (A : finType) (P : pred A) f (H : forall i, P i -> 0 <= f i) :
  0 <= \rsum_(i in A | P i) f i.
Proof.
apply Rle_trans with (\rsum_(i | (i \in A) && P i) (fun=> 0) i).
rewrite big_const iter_Rplus mulR0 /=; exact/Rle_refl.
exact/ler_rsum.
Qed.

Lemma rsumr_gt0 (A : finType) (f : A -> R) (HA : (0 < #|A|)%nat) :
  (forall i, 0 < f i) -> 0 < \rsum_(i in A) f i.
Proof.
move=> H.
rewrite (_ : \rsum_(i in A) f i = \rsum_(i in [set: A]) f i); last first.
  apply eq_bigl => x /=; by rewrite !inE.
eapply Rle_lt_trans; last first.
  apply ltr_rsum_support with (f := fun=> 0) => //.
  by rewrite cardsT.
rewrite big_const_seq iter_Rplus mulR0; exact/Rle_refl.
Qed.

Lemma prsumr_eq0P (A : finType) (P : pred A) f :
  (forall a, P a -> 0 <= f a) ->
  \rsum_(a | P a) f a = 0 <-> (forall a, P a -> f a = 0).
Proof.
move=> Hf; split=> [H a Ha|h]; last first.
  by rewrite (eq_bigr (fun=> 0)) // big_const iter_Rplus mulR0.
suff : f a = 0 /\ \rsum_(i | P i && (i != a)) f i = 0 by case.
apply: Rplus_eq_R0.
- exact/Hf/Ha.
- apply: rsumr_ge0 => ? /andP[? ?]; by apply Hf.
- rewrite -bigD1 /=; [exact H | exact Ha].
Qed.

(* TODO: factorize? *)
Lemma Rle_big_eq (A : finType) (f g : A -> R) (P : pred A) :
   (forall i : A, P i -> f i <= g i) ->
   \rsum_(i | P i) g i = \rsum_(i | P i) f i ->
   (forall i : A, P i -> g i = f i).
Proof.
move=> H1 H2 i Hi.
apply/eqP; rewrite -subR_eq0; apply/eqP.
move: i Hi.
apply prsumr_eq0P.
- move=> i Hi.
  apply (Rplus_le_reg_l (f i)).
  rewrite addR0 subRKC; by apply H1.
- rewrite big_split /= -(big_morph _ morph_Ropp oppR0).
  by apply/eqP; rewrite subR_eq0 H2.
Qed.

(** Rle, Rlt lemmas for big-mult of reals *)

Section ler_ltr_rprod.

Lemma rprodr_gt0 {A : finType} F : (forall i, 0 < F i) ->
  0 < \rprod_(i : A) F i.
Proof.
move=> H.
elim: (index_enum _) => [| hd tl IH].
rewrite big_nil; fourier.
rewrite big_cons; apply mulR_gt0 => //; by apply H.
Qed.

Lemma rprodr_ge0 {A : finType} F : (forall i, 0 <= F i) ->
  0 <= \rprod_(i : A) F i.
Proof.
move=> H.
elim: (index_enum _) => [| hd tl IH].
  rewrite big_nil; fourier.
rewrite big_cons; apply mulR_ge0 => //; exact H.
Qed.

Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.

Lemma rprodr_gt0_inv {B : finType} F (HF: forall a, 0 <= F a) :
  forall n (x : 'rV[B]_n.+1),
  0 < \rprod_(i < n.+1) F (x ``_ i) -> forall i, 0 < F (x ``_ i).
Proof.
elim => [x | n IH].
  rewrite big_ord_recr /= big_ord0 mul1R => Hi i.
  suff : i = ord_max by move=> ->.
  rewrite (ord1 i).
  by apply/val_inj.
move=> x.
set t := \row_(i < n.+1) (x ``_ (lift ord0 i)).
rewrite big_ord_recl /= => H.
apply Rlt_0_Rmult_inv in H; last 2 first.
  exact/HF.
  apply rprodr_ge0 => ?; exact/HF.
case.
case=> [Hi | i Hi].
  rewrite (_ : Ordinal _ = ord0); last exact/val_inj.
  by case: H.
case: H => _ H.
have : 0 < \rprod_(i0 < n.+1) F (t ``_ i0).
  suff : \rprod_(i < n.+1) F (x ``_ (lift ord0 i)) =
         \rprod_(i < n.+1) F (t ``_ i) by move=> <-.
  apply eq_bigr => ? _; by rewrite mxE.
have Hi' : (i < n.+1)%nat by rewrite ltnS in Hi.
move/IH.
move/(_ (Ordinal Hi')).
set o1 := Ordinal _.
set o2 := Ordinal _.
suff : lift ord0 o1 = o2 by move=> <-; rewrite mxE.
by apply val_inj.
Qed.

Lemma rprodr_ge1 {A : finType}  f : (forall i, 1 <= f i) ->
  1 <= \rprod_(i : A) f i.
Proof.
move=> Hf.
elim: (index_enum _) => [| hd tl IH].
- rewrite big_nil; by apply Rle_refl.
- rewrite big_cons -{1}(mulR1 1%R); apply Rmult_le_compat => // ; fourier.
Qed.

Local Open Scope R_scope.

Lemma ler_rprod {A : finType} f g : (forall i, 0 <= f i <= g i) ->
  \rprod_(i : A) f i <= \rprod_(i : A) g i.
Proof.
move=> Hfg.
case/orP : (orbN [forall i, f i != 0%R]) ; last first.
- rewrite negb_forall => /existsP Hf.
  case: Hf => i0 /negPn/eqP Hi0.
  rewrite (bigD1 i0) //= Hi0 mul0R; apply rprodr_ge0.
  move=> i ; move: (Hfg i) => [Hi1 Hi2] ; by apply (Rle_trans _ _ _ Hi1 Hi2).
- move=> /forallP Hf.
  have Hprodf : 0 < \rprod_(i : A) f i.
    apply rprodr_gt0 => a.
    move: (Hf a) (Hfg a) => {Hf}Hf {Hfg}[Hf2 _].
    apply/RltP; rewrite Rlt_neqAle eq_sym Hf /=; by apply/RleP.
  apply (Rmult_le_reg_r (1 * / \rprod_(i : A) f i) _ _).
    apply Rlt_mult_inv_pos => //; fourier.
  rewrite mul1R mulRV; last exact/not_eq_sym/Rlt_not_eq.
  set inv_spec := fun r => if r == 0 then 0 else / r.
  rewrite (_ : / (\rprod_(a : A) f a) = inv_spec (\rprod_(a : A) f a)) ; last first.
    rewrite /inv_spec (_ : \rprod_(a : A) f a == 0 = false) //.
    apply/eqP ; by apply not_eq_sym, Rlt_not_eq.
  rewrite (@big_morph _ _ (inv_spec) R1 Rmult R1 Rmult _); last 2 first.
  - move=> a b /=.
    case/boolP : ((a != 0) && (b != 0)).
    - move=> /andP [/negbTE Ha /negbTE Hb] ; rewrite /inv_spec Ha Hb.
      move/negbT in Ha ; move/negbT in Hb.
      have : (a * b)%R == 0 = false ; last move=> ->.
      apply/negP => /eqP Habs.
        apply (Rmult_eq_compat_r (/ b)) in Habs ; move: Habs.
        rewrite -mulRA mul0R mulRV ?mulR1; move/eqP; exact/negP.
      apply Rinv_mult_distr; move/eqP; exact/negP.
    - rewrite negb_and => Hab.
      case/orP : (orbN (a != 0)) => Ha.
      - rewrite Ha /= in Hab; move/negPn/eqP in Hab; rewrite Hab mulR0 /inv_spec.
        by rewrite (_ : 0 == 0 ) // mulR0.
      - move/negPn/eqP in Ha ; rewrite Ha mul0R /inv_spec.
        by rewrite (_ : 0 == 0 ) // mul0R.
  - rewrite /inv_spec.
    have : ~~ (1 == 0).
      apply/eqP => H01; symmetry in H01; move: H01; apply Rlt_not_eq; fourier.
    move/negbTE => -> ; by rewrite Rinv_1.
  rewrite -big_split /=.
  apply rprodr_ge1 => a.
  move/(_ a) in Hf.
  move: Hfg => /(_ a) [Hf2 Hfg].
  rewrite /inv_spec.
  move/negbTE in Hf; rewrite Hf; move/negbT in Hf.
  rewrite -(mulRV (f a)); last by move/eqP; apply/negP.
  apply Rmult_le_compat_r => //.
  rewrite -(mul1R (/ f a)).
  apply Rle_mult_inv_pos; first fourier.
  apply/RltP; rewrite Rlt_neqAle eq_sym Hf /=; exact/RleP.
Qed.

End ler_ltr_rprod.

Lemma classify_big (A : finType) n (f : A -> 'I_n) (F : 'I_n -> R) :
  \rsum_(s : A) F (f s) = \rsum_(i < n) INR #|f @^-1: [set i]| * F i.
Proof.
transitivity (\rsum_(i < n) \rsum_(s | true && (f s == i)) F (f s)).
  by apply partition_big.
apply eq_bigr => i _ /=.
transitivity (\rsum_(s | f s == i) F i); first by apply eq_bigr => s /eqP ->.
rewrite big_const iter_Rplus.
congr (INR _ * _).
apply eq_card => j /=; by rewrite !inE.
Qed.

Section pascal.

Lemma sum_f_R0_rsum : forall n (f : nat -> R),
  sum_f_R0 f n = \rsum_(i < n.+1) f i.
Proof.
elim => [f|n IH f] /=; first by rewrite big_ord_recl /= big_ord0 addR0.
by rewrite big_ord_recr /= IH.
Qed.

Theorem RPascal k (a b : R) :
  (a + b) ^ k = \rsum_(i < k.+1) INR ('C(k, i))* (a ^ (k - i) * b ^ i).
Proof.
rewrite addRC Binomial.binomial sum_f_R0_rsum.
apply eq_bigr => i _.
rewrite combinaison_Coq_SSR; last by rewrite -ltnS.
rewrite -minusE; field.
Qed.

End pascal.

Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.

Lemma log_rmul_rsum_mlog {A : finType} (f : A -> R+) : forall n (ta : 'rV[A]_n.+1),
  (forall i, 0 < f ta ``_ i) ->
  (- log (\rprod_(i < n.+1) f ta ``_ i) = \rsum_(i < n.+1) - log (f ta ``_ i))%R.
Proof.
elim => [i Hi | n IH].
  by rewrite big_ord_recl big_ord0 mulR1 big_ord_recl big_ord0 addR0.
move=> ta Hi.
rewrite big_ord_recl /= log_mult; last 2 first.
  by apply Hi.
  apply rprodr_gt0 => i; by apply Hi.
set tl := \row_(i < n.+1) ta ``_ (lift ord0 i).
have : forall i0 : 'I_n.+1, 0 < f tl ``_ i0.
  move=> i; rewrite mxE; exact/Hi.
move/IH => {IH}IH.
have -> : \rprod_(i < n.+1) f ta ``_ (lift ord0 i) = \rprod_(i < n.+1) f tl ``_ i.
  apply eq_bigr => i _; by rewrite mxE.
rewrite oppRD [X in _ = X]big_ord_recl IH.
congr (_ + _)%R.
apply eq_bigr => i _; by rewrite mxE.
Qed.
