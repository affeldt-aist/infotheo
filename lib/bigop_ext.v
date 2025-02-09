(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix lra.
From mathcomp Require boolp.
Require Import ssr_ext ssralg_ext.

(******************************************************************************)
(*                     Additional lemmas about bigops                         *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma morph_oppr {R : ringType} : {morph @GRing.opp R : x y / (x + y)%R : R}.
Proof. by move=> x y /=; rewrite GRing.opprD. Qed.

#[deprecated(since="infotheo 0.9", note="use `big_distrr` instead of `big_morph` + `morph_mulRdr`")]
Lemma morph_mulRDr {R : ringType} a : {morph (GRing.mul a) : x y / (x + y)%R : R}.
Proof. by move=> * /=; rewrite GRing.mulrDr. Qed.

Definition big_morph_oppr {R : ringType} := big_morph _ morph_oppr (@GRing.oppr0 R).

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

Lemma Set2sumE (A : finType) (f : A -> R) (card_A : #|A| = 2%nat) :
 \big[M/idx]_(i in A) (f i) = M (f (Set2.a card_A)) (f (Set2.b card_A)).
Proof.
by rewrite /index_enum -enumT Set2.enumE !big_cons big_nil (Monoid.addm0 M) !enum_valP.
Qed.

Lemma big_bool (f : bool -> R) : \big[M/idx]_(i in {:bool}) f i = M (f false) (f true).
Proof.
set h : 'I_2 -> bool := [eta (fun=>false) with ord0 |-> false, lift ord0 ord0 |-> true].
set h' : bool -> 'I_2 := fun x => match x with false => ord0 | true => lift ord0 ord0 end.
rewrite (reindex_onto h h') /=; last by move=> i _; rewrite /h /h'; case: ifP.
rewrite (eq_bigl xpredT); last first.
  move=> i; move: (ord2 i) => /orP[|] /eqP -> /=; first by rewrite eqxx.
  exact/eqP/val_inj.
by rewrite big_ord_recl /= big_ord_recl big_ord0 Monoid.addm0.
Qed.

Variable (A : finType).
Local Open Scope ring_scope.

Lemma big_rV0_row_of_tuple f (P : pred _) :
  \big[M/idx]_(v in 'rV[A]_0 | P v) f v =
  if P (row_of_tuple [tuple]) then f (row_of_tuple [tuple]) else idx.
Proof.
rewrite -big_map /= /index_enum -enumT /=.
set e := enum _.
rewrite (_ : e = [:: row_of_tuple [tuple]]).
  by rewrite /= big_cons big_nil Monoid.addm0.
rewrite /e.
apply (@eq_from_nth _ (row_of_tuple [tuple])).
  by rewrite -cardE card_mx muln0 expn0.
move=> i.
rewrite -cardE card_mx muln0 expn0 ltnS leqn0 => /eqP ->{i}.
rewrite -/e.
destruct e => //.
apply val_inj => /=.
by apply/ffunP => /= -[? []].
Qed.

End bigop_add_law.

Section bigop_algebraic_misc.
(** [bigA_distr] is a specialization of [bigA_distr_bigA] and at the same
    time a generalized version of [GRing.exprDn] for iterated prod. *)
Lemma bigA_distr (R : Type) (zero one : R) (times : Monoid.mul_law zero)
    (plus : Monoid.add_law zero times)
    (I : finType)
    (F1 F2 : I -> R) :
  \big[times/one]_(i in I) plus (F1 i) (F2 i) =
  \big[plus/zero]_(0 <= k < #|I|.+1)
  \big[plus/zero]_(J in {set I} | #|J| == k)
  \big[times/one]_(j in I) (if j \notin J then F1 j else F2 j).
Proof.
pose F12 i (j : bool) := if ~~ j then F1 i else F2 i.
under eq_bigr=> i.
  rewrite (_: plus (F1 i) (F2 i) = \big[plus/zero]_j F12 i j); last first.
    rewrite (bigID (fun i => i == false)) big_pred1_eq (big_pred1 true) //.
    by case.
  over.
rewrite bigA_distr_bigA big_mkord (partition_big
  (fun i : {ffun I -> bool} => inord #|[set x | i x]|)
  (fun j : 'I_#|I|.+1 => true)) //=.
{ eapply eq_big =>// i _.
  rewrite (reindex (fun s : {set I} => [ffun x => x \in s])); last first.
  { apply: onW_bij.
    exists (fun f : {ffun I -> bool} => [set x | f x]).
    by move=> s; apply/setP => v; rewrite inE ffunE.
    by move=> f; apply/ffunP => v; rewrite ffunE inE. }
  eapply eq_big.
  { move=> s; apply/eqP/eqP.
      move<-; rewrite -[#|s|](@inordK #|I|) ?ltnS ?max_card //.
      by congr inord; apply: eq_card => v; rewrite inE ffunE.
    move=> Hi; rewrite -[RHS]inord_val -{}Hi.
    by congr inord; apply: eq_card => v; rewrite inE ffunE. }
  by move=> j Hj; apply: eq_bigr => k Hk; rewrite /F12 ffunE. }
Qed.

Lemma bigID2 (R : Type) (I : finType) (J : {set I}) (F1 F2 : I -> R)
    (idx : R) (op : Monoid.com_law idx) :
  \big[op/idx]_(j in I) (if j \notin J then F1 j else F2 j) =
  op (\big[op/idx]_(j in ~: J) F1 j) (\big[op/idx]_(j in J) F2 j).
Proof.
rewrite (bigID (mem (setC J)) predT); apply: congr2.
by apply: eq_big =>// i /andP [H1 H2]; rewrite inE in_setC in H2; rewrite H2.
apply: eq_big => [i|i /andP [H1 H2]] /=; first by rewrite inE negbK.
by rewrite ifF //; apply: negbTE; rewrite inE in_setC in H2.
Qed.
End bigop_algebraic_misc.

(** Switching from a sum on the domain to a sum on the image of function *)
Section partition_big_finType_eqType.
Variables (A : finType) (B : eqType).
Variables (R : Type) (idx : R) (op : R -> R -> R) (M : Monoid.add_law idx op).

Lemma partition_big_undup_map (p : seq A) (f : A -> B) : forall g, uniq p ->
  \big[M/idx]_(i <- p) g i =
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
  rewrite [in LHS]big_seq [in RHS]big_seq /=.
  apply/esym/eq_bigr => b0 b0bs.
  rewrite big_cat /=.
  rewrite (_ : \big[M/idx]_(i0 <- h | f i0 == b0) F i0 = idx) ?Monoid.add0m//.
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
rewrite big_seq /=; apply congr_big => //= a.
case/boolP : (a \in h) => ah //=; apply/esym.
have : f a \in [:: b] by rewrite -H2 mem_undup; apply/mapP; exists a.
by rewrite in_cons /= in_nil orbC.
Qed.

(* NB: compare with finset.partition_big_imset *)
Lemma partition_big_fin_img (f : A -> B) g :
  \big[M/idx]_(i in A) (g i) =
  \big[M/idx]_(r <- fin_img f) \big[M/idx]_(i in A | f i == r) (g i).
Proof.
have /= := @partition_big_undup_map (enum A) f g.
rewrite enum_uniq => /(_ isT) H.
transitivity (\big[M/idx]_(i <- enum A) g i); first by rewrite enumT.
by rewrite H; apply eq_bigr => i _; apply congr_big => //; rewrite enumT.
Qed.

End partition_big_finType_eqType.

Section BigOps.
Variables (R : Type) (idx : R).
Variables (op : Monoid.law idx) (aop : Monoid.com_law idx).
Variables I J : finType.
Implicit Type A B : {set I}.
Implicit Type h : I -> J.
Implicit Type P : pred I.
Implicit Type F : I -> R.

Lemma partition_big_preimset h (B : {set J}) F :
  \big[aop/idx]_(i in h @^-1: B) F i =
     \big[aop/idx]_(j in B) \big[aop/idx]_(i in I | h i == j) F i.
Proof.
have HA : [disjoint B :&: [set h x | x in I] & B :\: [set h x | x in I]]
    by rewrite -setI_eq0 -setIA setIDA [in _ :&: B]setIC -setIDA setDv !setI0.
have Hha : [disjoint h @^-1: (B :&: [set h x | x in I])
                             & h @^-1: (B :\: [set h x | x in I])].
  rewrite -setI_eq0 -preimsetI.
  suff : [disjoint B :&: [set h x | x in I] & B :\: [set h x | x in I]].
    by rewrite -setI_eq0; move/eqP => ->; rewrite preimset0.
  by [].
rewrite -(setID B (h @: I)) /= preimsetU.
under eq_bigl do rewrite in_setU.
rewrite bigU //.
under [in RHS]eq_bigl do rewrite in_setU.
rewrite bigU //.
have -> : h @^-1: (B :\: [set h x | x in I]) = set0.
  apply/setP/subset_eqP/andP; rewrite sub0set; split => //.
  apply/subsetP=> i; rewrite !inE; case/andP.
  move/imsetP=> H _; rewrite boolp.falseE; apply: H.
  by exists i; rewrite ?inE.
rewrite big_set0 Monoid.mulm1.
have -> : \big[aop/idx]_(x in B :\: [set h x | x in I]) \big[aop/idx]_(i | h i == x) F i =
          \big[aop/idx]_(x in B :\: [set h x | x in I]) idx.
  apply eq_bigr => j.
  rewrite inE; case/andP => Hj Hj'.
  apply big_pred0 => i.
  apply/negP => /eqP hij.
  move: Hj; rewrite -hij.
  move/imsetP; apply.
  by exists i.
rewrite big1_eq Monoid.mulm1.
set B' := B :&: [set h x | x in I].
set A := h @^-1: B'.
have -> : B' = h @: A by rewrite imset_preimset //; apply subsetIr.
have Hright j : j \in h @: A -> \big[aop/idx]_(i in I | h i == j) F i =
                               \big[aop/idx]_(i in A | h i == j) F i.
  move=> Hj; apply eq_bigl => i; apply andb_id2r; move/eqP => hij.
  move: Hj; rewrite -hij !inE.
  case/imsetP => x; rewrite /A /B' !inE => /andP [H H0] ->.
  by rewrite H H0.
rewrite [in RHS](eq_bigr _ Hright).
exact: partition_big_imset.
Qed.

End BigOps.

Section big_pred1_inj.
Variables (R : Type) (idx : R) (op : Monoid.law idx).

Lemma big_pred1_inj (A C : finType) h i (k : A -> C) : injective k ->
  \big[op/idx]_(a | k a == k i) h a = h i.
Proof. by move=> ?; rewrite (big_pred1 i) // => ?; rewrite eqtype.inj_eq. Qed.

End big_pred1_inj.
Arguments big_pred1_inj [R] [idx] [op] [A] [C] [h] [i] [k] _.

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
  \big[M/idx]_(x in a `* b) f x = \big[M/idx]_(x in a) \big[M/idx]_(y in b) f (x, y).
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

Lemma big_rV1_ord0 (f : A -> R) k :
  \big[M/idx]_(i in A) f i = k -> \big[M/idx]_(i in 'rV[A]_1) f (i ``_ ord0) = k.
Proof.
move=> <-.
rewrite (reindex_onto (fun j => \row_(i < 1) j) (fun p => p ``_ ord0)) /=.
- apply eq_big => a; first by rewrite mxE eqxx inE.
  move=> _; by rewrite mxE.
- move=> t _; apply/rowP => a; by rewrite (ord1 a) mxE.
Qed.

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

Section bigcup_ext.
Variables I A B : finType.

Lemma bigcup_set0 i (D : I -> {set B}) (F : B -> I -> {set A}) b :
  b \in D i -> F b i != set0 ->
  \bigcup_(b' in D i) F b' i == set0 -> D i == set0.
Proof.
move=> bDi Fbi0 /set0Pn F0; apply/set0Pn => -[b' b'i]; apply F0 => {F0}.
by case/set0Pn : Fbi0 => a tA; exists a; apply/bigcupP; exists b.
Qed.

Lemma bigcup_setX (E : I -> {set A}) (F : {set B}) :
  \bigcup_(i in I) (F `* E i) = F `* (\bigcup_(i in I) (E i)).
Proof.
apply/setP => -[b a] /=; rewrite !inE /=.
apply/bigcupP/andP => [[/= i _]|[K1] /bigcupP[/= i _ aEi]].
  rewrite !inE /= => /andP[xb yai]; rewrite xb; split => //.
  by apply/bigcupP; exists i.
by exists i => //; rewrite !inE /= K1.
Qed.

Lemma bigcup_preimset (P : pred I) (F : A -> B) (E : I -> {set B}) :
  \bigcup_(i | P i) F @^-1: E i = F @^-1: \bigcup_(i | P i) E i.
Proof.
rewrite/preimset.
apply/setP=> x; rewrite inE; apply/bigcupP/bigcupP => -[] i HPi; rewrite ?inE => HFxEi; exists i => //=; by rewrite inE.
Qed.

Lemma bigcup_set1 (E : {set A}) : E = \bigcup_(a in E) [set a].
Proof.
apply/setP => a; apply/idP/bigcupP => [aE|[a' a'E]].
by exists a => //; rewrite inE.
by rewrite inE => /eqP ->.
Qed.

End bigcup_ext.

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
Variable V : zmodType.
Variable times : Monoid.mul_law (@GRing.zero V).
Local Notation "*%M" := times (at level 0).
Variable plus : Monoid.add_law (@GRing.zero V) *%M.
Local Notation "+%M" := plus (at level 0).

Lemma big_tuple_ffun (I J : finType) (F : {ffun I -> J} -> R)
  (G : R -> J -> V) (jdef : J) (idef : I) :
  \big[+%M/@GRing.zero V]_(j : #|I|.-tuple J) G (F [ffun x => tnth j (enum_rank x)]) (nth jdef j 0)
    = \big[+%M/@GRing.zero V]_(f : {ffun I -> J}) G (F f) (f (nth idef (enum I) 0)).
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

Import Order.POrderTheory Order.TotalTheory GRing.Theory Num.Theory.

Section prod_gt0_inv.
Local Open Scope ring_scope.
Lemma prod_gt0_inv (R : realFieldType) n (F : _ -> R)
  (HF: forall a, (0 <= F a)) :
  (0 < \prod_(i < n.+1) F i -> forall i, 0 < F i).
Proof.
move=> h i.
rewrite lt_neqAle HF andbT; apply/eqP => /esym F0.
move: h; rewrite ltNge => /negP; apply.
rewrite le_eqVlt; apply/orP; left.
rewrite prodf_seq_eq0/=.
apply/hasP; exists i; last exact/eqP.
by rewrite mem_index_enum.
Qed.
End prod_gt0_inv.

Section classify_big.
Local Open Scope ring_scope.
Variable R : ringType.

Lemma classify_big (A : finType) n (f : A -> 'I_n) (F : 'I_n -> R) :
  \sum_a F (f a) =
    \sum_(i < n) (#|f @^-1: [set i]|%:R * F i).
Proof.
transitivity (\sum_(i < n) \sum_(a | true && (f a == i)) F (f a)).
  by apply partition_big.
apply eq_bigr => i _ /=.
transitivity (\sum_(a | f a == i) F i); first by apply eq_bigr => s /eqP ->.
rewrite big_const iter_addr addr0 mulr_natl; congr GRing.natmul.
apply eq_card => j /=; by rewrite !inE.
Qed.
End classify_big.

Section num.
Local Open Scope ring_scope.
Variables (R : numDomainType) (I : Type) (r : seq I).

(* generalizes leR_sumRl *)
Lemma ler_suml [P Q : pred I] [F G : I -> R] :
  (forall i : I, P i -> F i <= G i) ->
  (forall i : I, Q i -> ~~ P i -> 0 <= G i) ->
  (forall i : I, P i -> Q i) ->
  \sum_(i <- r | P i) F i <= \sum_(i <- r | Q i) G i.
Proof.
move=> PFG QG0 PQ.
move: PFG => /ler_sum /le_trans; apply.
rewrite [leRHS](bigID P) /=.
move: PQ => /(_ _) /andb_idl => /(eq_bigl _ G) ->.
rewrite lerDl; apply: sumr_ge0=> i.
by case/andP; exact: QG0.
Qed.

(* generalizes leR_sumR_predU
   NB: here we use (predU P Q) instead of [predU P & Q] for the union.
   The former is suitable for applicative predicates as in this lemma
   while the latter infix notation should be used only for collective predicates.
   ([predU P & Q] i gets simplified to i \in P || i \in Q
    while (predU P Q) i to P i || Q i) *)
Lemma ler_sum_predU [P Q : pred I] (F : I -> R) :
  (forall i : I, P i -> Q i -> 0 <= F i) ->
  \sum_(i <- r | (predU P Q) i) F i <=
    \sum_(i <- r | P i) F i + \sum_(i <- r | Q i) F i.
Proof.
move=> F0.
under eq_bigr => i _.
  rewrite (_ : F i = if Q i then F i else F i); last by case: ifP.
  over.
rewrite big_if /=.
under eq_bigl do rewrite orbC orbK.
rewrite addrC; apply: lerD => //.
apply: ler_suml=> // i; rewrite andb_orl andbN orbF; last by case/andP.
by move=> /[dup] /F0 /[swap] -> /[!andTb] /[!negbK].
Qed.
End num.

Section real.
Local Open Scope ring_scope.
Variables (R : realDomainType) (I : Type) (r : seq I).

Lemma fsumr_gt0 (U : eqType) (F : U -> R) (s : seq U) :
  0 < \sum_(i <- s) F i -> exists2 i, i \in s & 0 < F i.
Proof.
elim: s => [|h t ih]; first by rewrite big_nil ltxx.
rewrite big_cons.
have H : forall x y : R, 0 < x + y -> 0 < x \/ 0 < y by move=> x y; lra.
move/H => [Fh0|]; first by exists h => //; rewrite mem_head.
by move/ih => [u ut Fu0]; exists u => //; rewrite inE ut orbT.
Qed.

End real.

Declare Scope min_scope.

Reserved Notation "\min^ b '_(' a 'in' A ) F" (at level 41,
  F at level 41, a, A at level 50,
   format "'[' \min^ b '_(' a  'in'  A ) '/  '  F ']'").

Notation "\min^ b '_(' a 'in' A ) F" :=
  ((fun a => F) (arg_min b (fun x => x \in A) (fun a => F))) : min_scope.

Notation "\rmax_ ( i 'in' A ) F" := (\big[Order.max/GRing.zero]_(i in A) F)
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \rmax_ ( i  'in'  A ) '/  '  F ']'").

Notation "\rmax_ ( i <- r ) F" :=  (\big[Order.max/GRing.zero]_(i <- r) F)
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \rmax_ ( i  <-  r ) '/  '  F ']'").

Section order.
Import classical.mathcomp_extra Order.Theory.
Local Open Scope ring_scope.
Local Open Scope order_scope.

Lemma bigmax_le_seq disp (T : porderType disp) (I : eqType) (r : seq I) (f : I -> T)
    (x0 x : T) (PP : pred I) :
  (x0 <= x)%O ->
  (forall i : I, i \in r -> PP i -> (f i <= x)%O) ->
  (\big[Order.max/x0]_(i <- r | PP i) f i <= x)%O.
Proof.
move=> x0x cond; rewrite big_seq_cond bigmax_le // => ? /andP [? ?]; exact: cond.
Qed.

(* seq version of order.bigmax_leP *)
Lemma bigmax_leP_seq disp (T : orderType disp) (I : eqType) (r : seq I) (F : I -> T)
    (x m : T) (PP : pred I) :
reflect ((x <= m)%O /\ (forall i : I, i \in r -> PP i -> (F i <= m)%O))
  (\big[Order.max/x]_(i <- r | PP i) F i <= m)%O.
Proof.
apply:(iffP idP); last by case; exact:bigmax_le_seq.
move=> bm; split; first by exact/(le_trans _ bm)/bigmax_ge_id.
by move=> *; exact/(le_trans _ bm)/le_bigmax_seq.
Qed.

Section classical.
Import boolp.
Lemma bigmax_gt0P_seq (T : realDomainType) (A : eqType) (F : A -> T)
  (s : seq A) (PP : pred A) :
reflect (exists i : A, [/\ i \in s, PP i & (0 < F i)%O]) (0 < \big[Num.max/0]_(m <- s | PP m) F m).
Proof.
rewrite ltNge.
apply:(iffP idP).
  move=> /bigmax_leP_seq /not_andP []; first by rewrite lexx.
  move=> /existsNP [] x /not_implyP [] xs /not_implyP [] PPx /negP.
  rewrite -ltNge=> Fx0.
  by exists x; repeat (split=> //).
case=> x [] ? ? ?; apply/bigmax_leP_seq/not_andP; right.
apply/existsNP; exists x; do 2 (apply/not_implyP; split=> //).
by apply/negP; rewrite -ltNge.
Qed.
End classical.

End order.

Section big_union.

Definition big_union_disj := big_union.

(* TODO: this is more generic and should be called big_union *)
Lemma big_union_nondisj (R : Type) (idx : R) (M : Monoid.com_law idx)
  (A : finType) (X1 X2 : {set A}) (f : A -> R) :
  \big[M/idx]_(a in (X1 :&: X2)) f a = idx ->
  \big[M/idx]_(a in (X1 :|: X2)) f a =
    M (\big[M/idx]_(a in X1) f a) (\big[M/idx]_(a in X2) f a).
Proof.
move=> I0.
rewrite -setIUY big_union_disj 1?disjoint_sym ?setIYI_disj //.
rewrite I0 Monoid.opm1 big_union_disj; last first.
  by rewrite -setI_eq0 setIDA setIC Order.SetSubsetOrder.setIDv // set0D.
  (* Order.SetSubsetOrder.setIDv is B :&: (A :\: B) = set0 *)
set lhs := LHS.
rewrite -(setID X1 X2) big_union_disj; last first.
  by rewrite -setI_eq0 setIC -setIA Order.SetSubsetOrder.setIDv // setI0.
rewrite I0 Monoid.op1m.
rewrite -[in X in M _ X](setID X2 X1) big_union_disj; last first.
  by rewrite -setI_eq0 setIC -setIA Order.SetSubsetOrder.setIDv // setI0.
by rewrite setIC I0 Monoid.op1m.
Qed.

End big_union.
