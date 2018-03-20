(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import Rssr Reals_ext log2 ssr_ext ssralg_ext tuple_prod.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope reals_ext_scope.

(** * Instantiation of canonical big operators with Coq reals *)

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

Section Abelian.

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

End Abelian.

Canonical addR_monoid := Monoid.Law addRA add0R addR0.
Canonical addR_comoid := Monoid.ComLaw addRC.
Canonical mulR_monoid := Monoid.Law mulRA mul1R mulR1.
Canonical mulR_muloid := Monoid.MulLaw mul0R mulR0.
Canonical mulR_comoid := Monoid.ComLaw mulRC.
Canonical addR_addoid := Monoid.AddLaw mulRDl mulRDr.

Notation "\rsum_ ( i <- t ) F" := (\big[Rplus/0%R]_( i <- t) F)
  (at level 41, F at level 41, i at level 50,
    format "'[' \rsum_ ( i <- t ) '/  '  F ']'") : R_scope.
Notation "\rsum_ ( m <= i < n ) F" := (\big[Rplus/0%R]_( m <= i < n ) F)
  (at level 41, F at level 41, i, m, n at level 50,
    format "'[' \rsum_ ( m  <=  i  <  n ) '/  '  F ']'") : R_scope.
Notation "\rsum_ ( i | P ) F" := (\big[Rplus/0%R]_( i | P) F)
  (at level 41, F at level 41, i at level 50,
    format "'[' \rsum_ ( i  |  P ) '/  '  F ']'") : R_scope.
Notation "\rsum_ ( i ':' A | P ) F" := (\big[Rplus/0%R]_( i : A | P ) F)
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \rsum_ ( i  ':'  A  |  P ) '/  '  F ']'") : R_scope.
Notation "\rsum_ ( i : t ) F" := (\big[Rplus/0%R]_( i : t) F)
  (at level 41, F at level 41, i at level 50,
    format "'[' \rsum_ ( i : t ) '/  '  F ']'") : R_scope.
Notation "\rsum_ ( i < n ) F" := (\big[Rplus/0%R]_( i < n ) F)
  (at level 41, F at level 41, i at level 50,
    format "'[' \rsum_ ( i < n ) '/  '  F ']'") : R_scope.
Notation "\rsum_ ( i 'in' A | P ) F" := (\big[Rplus/0%R]_( i in A | P ) F)
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \rsum_ ( i  'in'  A  |  P ) '/  '  F ']'") : R_scope.
Notation "\rsum_ ( a 'in' A ) F" := (\big[Rplus/0%R]_( a in A ) F)
  (at level 41, F at level 41, a, A at level 50,
    format "'[' \rsum_ ( a  'in'  A ) '/  '  F ']'") : R_scope.

Lemma big_Rabs {A : finType} F : Rabs (\rsum_ (a : A) F a) <= \rsum_ (a : A) Rabs (F a).
Proof.
elim: (index_enum _) => [| hd tl IH].
  rewrite 2!big_nil Rabs_R0; by apply Rle_refl.
rewrite 2!big_cons.
apply (Rle_trans _ (Rabs (F hd) + Rabs (\rsum_(j <- tl) F j))); first by apply Rabs_triang.
by apply Rplus_le_compat_l.
Qed.

Lemma classify_big {T : finType} k (f : T -> 'I_k) (F : 'I_k -> R) :
  \rsum_(s : T) F (f s) = \rsum_(n : 'I_k) INR #|f @^-1: [set n]| * F n.
Proof.
transitivity (\rsum_(n<k) \rsum_(s | true && (f s == n)) F (f s)).
  by apply partition_big.
apply eq_bigr => i _ /=.
transitivity (\rsum_(s|f s == i) F i).
  by apply eq_bigr => s /eqP ->.
rewrite big_const iter_Rplus.
do 2 f_equal.
apply eq_card => j /=.
by rewrite !inE.
Qed.

Lemma Set2rsumE {A : finType} (f : A -> R) (card_A : #|A| = 2%nat) :
 \rsum_(i in A) (f i) = f (Set2.a card_A) + f (Set2.b card_A).
Proof.
by rewrite /index_enum -enumT Set2.enumE !big_cons big_nil addR0 !enum_valP.
Qed.

(** Rle, Rlt lemmas for big sums of reals *)

Section Rcomparison_rsum.

Variable A : finType.
Variables f g : A -> R.
Variable P Q : pred A.

Lemma Rle_big_P_f_g_X (X : {set A}) : (forall i, i \in X -> P i -> f i <= g i) ->
  \rsum_(i in X | P i) f i <= \rsum_(i in X | P i) g i.
Proof.
move=> H.
elim: (index_enum _) => [| hd tl IH].
- rewrite !big_nil; by apply Rle_refl.
- rewrite !big_cons.
  set cond := _ && _; move Hcond : cond => []; subst cond => //.
  apply Rplus_le_compat => //.
  case/andP : Hcond.
  by apply H.
Qed.

Lemma Rle_big_P_f_g : (forall i, P i -> f i <= g i) ->
  \rsum_(i | P i) f i <= \rsum_(i | P i) g i.
Proof.
move=> H.
elim: (index_enum _) => [| hd tl IH].
- rewrite !big_nil; by apply Rle_refl.
- rewrite !big_cons.
  case: ifP => Hcase //.
  apply Rplus_le_compat => //.
  by apply H.
Qed.

Lemma Rlt_big_f_g_X (X : {set A}) : forall (HA: (0 < #|X|)%nat),
  (forall i, i \in X -> f i < g i) ->
  \rsum_(i in X) f i < \rsum_(i in X) g i.
Proof.
move Ha : #|X| => a.
move: a X Ha.
elim => // a IHa X Ha _ H.
move: (ltn0Sn a). rewrite -Ha card_gt0. case/set0Pn => a0 Ha0.
rewrite (@big_setD1 _ _ _ _ a0 _ f) //= (@big_setD1 _ _ _ _ a0 _ g) //=.
case: a IHa Ha => IHa Ha.
  rewrite (_ : X :\ a0 = set0); last first.
    rewrite (cardsD1 a0) Ha0 /= add1n in Ha.
    case: Ha.
    move/eqP.
    rewrite cards_eq0.
    by move/eqP.
  rewrite !big_set0 2!addR0; by apply H.
move=> HA.
apply Rplus_lt_compat.
  by apply H.
apply Ha => //.
  rewrite (cardsD1 a0) Ha0 /= add1n in HA.
  by case: HA.
move=> i Hi.
rewrite in_setD in Hi.
case/andP : Hi => Hi1 Hi2.
by apply H.
Qed.

Lemma Rle_big_P_Q_f_g : (forall i, P i -> f i <= g i) ->
  (forall i, Q i -> 0 <= g i) ->
  (forall i, P i -> Q i) ->
  \rsum_(i | P i) f i <= \rsum_(i | Q i) g i.
Proof.
move=> f_g Qg H.
elim: (index_enum _) => [| hd tl IH].
- rewrite !big_nil; by apply Rle_refl.
- rewrite !big_cons /=.
  case: ifP => Hcase.
    rewrite (H _ Hcase).
    apply Rplus_le_compat => //.
    by apply f_g.
  case: ifP => // Qhd.
  apply Rle_trans with (\big[Rplus/0]_(j <- tl | Q j) g j).
    by apply IH.
  rewrite -{1}(add0R (\big[Rplus/0]_(j <- tl | Q j) g j)).
  by apply Rplus_le_compat_r, Qg.
Qed.

Lemma Rle_big_P_true_f_g : (forall a, 0 <= g a) ->
  (forall i, i \in P -> f i <= g i) ->
  \rsum_(i in A | P i) f i <= \rsum_(i in A) g i.
Proof.
move=> K H.
elim: (index_enum _) => [| hd tl IH].
- rewrite !big_nil; by apply Rle_refl.
- rewrite !big_cons.
  case/orP : (orbN (hd \in A)) => H1.
    rewrite H1 /=.
    case: ifP => Hif.
      apply Rplus_le_compat => //.
      by apply H.
    rewrite -[X in X <= _]add0R.
    by apply Rplus_le_compat.
  rewrite (negbTE H1) /=; exact IH.
Qed.

Lemma Rle_big_f_X_Y : (forall a, 0 <= f a) ->
  (forall i, i \in P -> i \in Q) ->
  \rsum_(i in P) f i <= \rsum_(i in Q) f i.
Proof.
move=> Hf P'_P.
elim: (index_enum _) => [| hd tl IH].
- rewrite !big_nil; by apply Rle_refl.
- rewrite !big_cons.
  set cond := _ \in _; move Hcond : cond => []; subst cond => //=.
    rewrite (P'_P _ Hcond).
    by apply Rplus_le_compat_l.
  set cond := _ \in _; move Hcond2 : cond => []; subst cond => //=.
  rewrite -[X in X <= _]add0R.
  by apply Rplus_le_compat.
Qed.

Lemma Rle_big_P_Q_f_X (X : pred A) :
  (forall a, 0 <= f a) -> (forall i, P i -> Q i) ->
  \rsum_(i in X | P i) f i <= \rsum_(i in X | Q i) f i.
Proof.
move=> Hf P_Q.
elim: (index_enum _) => [| hd tl IH].
- rewrite !big_nil; by apply Rle_refl.
- rewrite !big_cons.
  set cond := _ \in _; move Hcond : cond => []; subst cond => //=.
  case: ifP => // HP.
  + case: ifP => HQ.
    * by apply Rplus_le_compat_l.
    * by rewrite (P_Q _ HP) in HQ.
  + case: ifP => // HQ.
    rewrite -[X in X <= _]add0R.
    by apply Rplus_le_compat.
Qed.

Lemma Rle_big_predU_f : (forall a, 0 <= f a) ->
  \rsum_(i in A | [predU P & Q] i) f i <=
  \rsum_(i in A | P i) f i + \rsum_(i in A | Q i) f i.
Proof.
move=> Hf.
elim: (index_enum _) => //.
- rewrite !big_nil /=; fourier.
- move=> h t IH /=.
  rewrite !big_cons /=.
  case: ifP => /=.
  + case/orP => [HP1 | HP2].
    * rewrite unfold_in in HP1.
      rewrite HP1.
      case: ifP => // HP2.
      - rewrite -addRA; apply Rplus_le_compat_l.
        eapply Rle_trans; first by apply IH.
        have : forall a b c, 0 <= c -> a + b <= a + (c + b) by move=> *; fourier.
        apply.
        by apply Hf.
      - rewrite -addRA; apply Rplus_le_compat_l.
        eapply Rle_trans; first by apply IH.
        by apply Req_le.
    * rewrite unfold_in in HP2.
      rewrite HP2.
      case: ifP => // HP1.
      - rewrite -addRA; apply Rplus_le_compat_l.
        eapply Rle_trans; first by apply IH.
        have : forall a b c, 0 <= c -> a + b <= a + (c + b) by move=> *; fourier.
        apply.
        by apply Hf.
      - rewrite -(Rplus_comm (f h + _)) -addRA; apply Rplus_le_compat_l.
        eapply Rle_trans; first by apply IH.
        by rewrite Rplus_comm; apply Req_le.
  + move/negbT.
    rewrite negb_or.
    case/andP.
    rewrite unfold_in; move/negbTE => ->.
    rewrite unfold_in; move/negbTE => ->.
    by apply IH.
Qed.

End Rcomparison_rsum.

Lemma Rle0_prsum (A : finType) (P : pred A) f (H : forall i, P i -> 0 <= f i) :
  0 <= \rsum_(i in A | P i) f i.
Proof.
apply Rle_trans with (\rsum_(i | (i \in A) && P i) (fun=> 0) i).
rewrite big_const iter_Rplus mulR0 /=; by apply Rle_refl.
by apply Rle_big_P_f_g.
Qed.

Lemma Rle_prsum_restrict {A : finType} (f : A -> R) (P Q : pred A) (H : forall a, 0 <= f a) :
  (forall i, P i -> Q i) ->
  \rsum_(i | P i) f i <= \rsum_(i | Q i) f i.
Proof.
move=> R_T.
apply: Rle_trans; last by apply (@Rle_big_P_Q_f_X A f P Q xpredT).
by apply Req_le.
Qed.

Lemma Req_0_rmul_inv' {A : finType} (P Q : pred A) f (H : forall i, 0 <= f i) :
  forall j, P j -> f j <= \rsum_(i | P i) f i.
Proof.
move=> j Hj.
rewrite (_ : f j = \rsum_(i | i == j) f i); last by rewrite big_pred1_eq.
apply: Rle_prsum_restrict => // i /eqP ?; by subst j.
Qed.

Lemma prsum_eq0P {A : finType} (P : pred A) f (Hf : forall a, P a -> 0 <= f a) :
  \rsum_(a | P a) f a = 0 <-> (forall a, P a -> f a = 0).
Proof.
split=> [H a Ha|h]; last first.
  by rewrite (eq_bigr (fun=> 0)) // big_const iter_Rplus mulR0.
suff : f a = 0 /\ \rsum_(i | P i && (i != a)) f i = 0 by case.
apply: Rplus_eq_R0.
- exact/Hf/Ha.
- apply: Rle0_prsum => ? /andP[? ?]; by apply Hf.
- rewrite -bigD1 /=; [exact H | exact Ha].
Qed.

Lemma prsum_eq0PW {A : finType} (P : pred A) f (Hf : forall a, 0 <= f a) :
  \rsum_(a | P a) f a = 0 <-> (forall a, P a -> f a = 0).
Proof.
split => [H a Pa | H]; last first.
  by rewrite (eq_bigr (fun=> 0)) // big_const iter_Rplus mulR0.
case/Rle_lt_or_eq_dec : (Hf a) => // fa.
exfalso.
have : f a <= \rsum_(i | P i) f i by apply Req_0_rmul_inv'.
rewrite H => ?; fourier.
Qed.

Lemma Rlt_big_0_g (A : finType) (g : A -> R) (HA : (0 < #|A|)%nat) :
  (forall i, 0 < g i) -> 0 < \rsum_(i in A) g i.
Proof.
move=> H.
rewrite (_ : \rsum_(i in A) g i = \rsum_(i in [set: A]) g i); last first.
  apply eq_bigl => x /=; by rewrite !inE.
eapply Rle_lt_trans; last first.
  apply Rlt_big_f_g_X with (f := fun x => 0) => //.
  by rewrite cardsT.
rewrite big_const_seq iter_Rplus mulR0; by apply Rle_refl.
Qed.

Lemma rsum_neq0 {A : finType} (P : {set A}) (g : A -> R) :
  \rsum_(t | t \in P) g t != 0 -> [exists t, (t \in P) && (g t != 0)].
Proof.
move=> H1.
apply negbNE.
rewrite negb_exists.
apply/negP => /forallP abs.
move/negP : H1; apply.
rewrite big_mkcond /=.
apply/eqP.
transitivity (\rsum_(a : A) 0); last by rewrite big_const iter_Rplus mulR0.
apply eq_bigr => a _.
case: ifP => // Hcond.
move: (abs a); by rewrite Hcond /= negbK => /eqP.
Qed.

(* TODO: factorize? *)
Lemma Rle_big_eq (B : finType) (f g : B -> R) (U : pred B) :
   (forall i : B, U i -> f i <= g i) ->
   \rsum_(i|U i) g i = \rsum_(i|U i) f i ->
   (forall i : B, U i -> g i = f i).
Proof.
move=> H1 H2 i Hi.
apply (Rplus_eq_reg_l (- (f i))).
rewrite Rplus_opp_l Rplus_comm.
move: i Hi.
apply prsum_eq0P.
- move=> i Hi.
  apply (Rplus_le_reg_l (f i)).
  rewrite addR0 subRKC; by apply H1.
- rewrite big_split /= -(big_morph _ morph_Ropp oppR0).
  by apply Rminus_diag_eq, H2.
Qed.

(* TODO: generalize to any bigop *)
Lemma rsum_union {C : finType} (B1 B2 B : {set C}) f :
  [disjoint B2 & B1] ->
  B = B1 :|: B2 ->
  \rsum_(b | b \in B) f b =
  \rsum_(b | b \in B1) f b + \rsum_(b | b \in B2) f b.
Proof.
move=> Hdisj ->.
rewrite (@big_setID _ _ _ _ _ B1) /= setUK setDUl setDv set0U.
suff : B2 :\: B1 = B2 by move=> ->.
by apply/setDidPl.
Qed.

(** Big sums lemmas for products *)

Section big_sums_prods.

Variables A B : finType.

Lemma pair_big_fst : forall (F : {: A * B} -> R) P Q,
  P =1 Q \o (fun x => x.1) ->
  \rsum_(i in A | Q i) \rsum_(j in B) (F (i, j)) = \rsum_(i in {: A * B} | P i) F i.
Proof.
move=> /= F Q' Q Q'Q; rewrite pair_big /=.
apply eq_big.
- case=> /= i1 i2; by rewrite inE andbC Q'Q.
- by case.
Qed.

Lemma pair_big_snd : forall (F : {: A * B} -> R) P Q,
  P =1 Q \o (fun x => x.2) ->
  \rsum_(i in A) \rsum_(j in B | Q j) (F (i, j)) = \rsum_(i in {: A * B} | P i) F i.
Proof.
move=> /= F Q' Q Q'Q; rewrite pair_big /=.
apply eq_big.
- case=> /= i1 i2; by rewrite Q'Q.
- by case.
Qed.

End big_sums_prods.

(** Switching from a sum on the domain to a sum on the image of function *)

Definition fin_img (A : finType) (B : eqType) (f : A -> B) : seq B := undup (map f (enum A)).

Section sum_dom_codom.

Variable A : finType.

Lemma sum_parti (p : seq A) (X : A -> R) : forall F, uniq p ->
  \rsum_(i <- p) (F i) =
  \rsum_(r <- undup (map X p)) \big[Rplus/0]_(i <- p | X i == r) (F i).
Proof.
move Hn : (undup (map X (p))) => n.
move: n p X Hn.
elim => [p X HA F Hp | h t IH p X H F Hp].
- rewrite big_nil.
  move/undup_nil_inv : HA.
  move/map_nil_inv => ->.
  by rewrite big_nil.
- rewrite big_cons.
  have [preh [pret [H1 [H2 H3]]]] : exists preh pret,
    perm_eq p (preh ++ pret) /\ undup (map X preh) = [:: h] /\ undup (map X pret) = t.
    by apply undup_perm.
  apply trans_eq with (\big[Rplus/0]_(i <- preh ++ pret) F i).
    by apply: eq_big_perm.
  apply trans_eq with
   (\big[Rplus/0]_(i <- preh ++ pret | X i == h) F i +
   \rsum_(j <- t) \big[Rplus/0]_(i <- preh ++ pret | X i == j) F i); last first.
    f_equal.
    apply: eq_big_perm.
      by rewrite perm_eq_sym.
    apply eq_bigr => i _ /=.
    apply: eq_big_perm.
    by rewrite perm_eq_sym.
  have -> :
    \rsum_(j <- t) \big[Rplus/0]_(i <- (preh ++ pret) | X i == j) F i =
    \rsum_(j <- t) \big[Rplus/0]_(i <- pret | X i == j) F i.
    rewrite big_seq_cond.
    symmetry.
    rewrite big_seq_cond /=.
    apply eq_bigr => i Hi.
    rewrite big_cat /=.
    have -> : \big[Rplus/0]_(i0 <- preh | X i0 == i) F i0 = 0.
      transitivity (\big[Rplus/0]_(i0 <- preh | false) F i0).
      rewrite big_seq_cond.
      apply eq_bigl => /= j.
      apply/negP.
      case/andP; move=> Xj_i; move/eqP=> j_preh.
      subst i.
      have Xj_h : X j \in [:: h].
        have H4 : X j \in map X preh by apply/mapP; exists j.
        have H5 : X j \in undup (map X preh)  by rewrite mem_undup.
        by rewrite H2 in H5.
      have : uniq (h :: t).
        rewrite -H.
        apply undup_uniq.
        rewrite /= in_cons in_nil orbC /= in Xj_h.
        move/eqP : Xj_h => Xj_h.
        subst h.
        rewrite andbC /= in Hi.
        by rewrite /= Hi.
      by rewrite big_pred0.
      by rewrite add0R.
  rewrite -IH //; last first.
    have : uniq (preh ++ pret) by rewrite -(@perm_eq_uniq _ _ _ H1).
    rewrite cat_uniq.
    case/andP => _; by case/andP.
  have -> :  \big[Rplus/0]_(i <- (preh ++ pret) | X i == h) F i =
    \rsum_(i <- preh) F i.
    rewrite big_cat /=.
    have -> : \big[Rplus/0]_(i <- pret | X i == h) F i = 0.
      transitivity (\big[Rplus/0]_(i0 <- pret | false) F i0); last first.
        by rewrite big_pred0.
      rewrite big_seq_cond.
      apply eq_bigl => /= j.
      apply/negP.
      case/andP; move => j_pret; move/eqP => Xj_h.
      subst h.
      have Xj_t : X j \in t.
        have H4 : X j \in map X pret.
        apply/mapP; by exists j.
        have H5 : X j \in undup (map X pret).
        by rewrite mem_undup.
        by rewrite H3 in H5.
      have : uniq (X j :: t).
        rewrite -H.
        by apply undup_uniq.
      by rewrite /= Xj_t.
    rewrite addR0 big_seq_cond /=.
    symmetry.
    rewrite big_seq_cond /=.
    apply congr_big => //= x.
    case/orP : (orbN (x \in preh)) => Y.
    + rewrite Y /=.
      symmetry.
      have : X x \in [:: h].
        rewrite -H2 mem_undup.
        apply/mapP.
        by exists x.
      by rewrite in_cons /= in_nil orbC.
    + by rewrite (negbTE Y) andbC.
  by rewrite big_cat.
Qed.

(* NB: use finset.partition_big_imset? *)
Lemma sum_parti_finType (X : A -> R) F :
   \rsum_(i in A) (F i) =
   \rsum_(r <- fin_img X) \big[Rplus/0]_(i in A | X i == r) (F i).
Proof.
move: (@sum_parti (enum A) X F) => /=.
rewrite enum_uniq.
move/(_ (refl_equal _)) => IH.
transitivity (\big[Rplus/0]_(i <- enum A) F i).
  apply congr_big => //.
  by rewrite enumT.
rewrite IH.
apply eq_bigr => i _.
apply congr_big => //.
by rewrite enumT.
Qed.

End sum_dom_codom.

Local Open Scope R_scope.

Section rsum_rV_prod.

Local Open Scope ring_scope.

Lemma rsum_rV_prod (A B : finType) n f (s : {set 'rV[A * B]_n}) :
  \rsum_(a in 'rV[A * B]_n | a \in s) f a =
  \rsum_(a in {: 'rV[A]_n * 'rV[B]_n} | (prod_tuple a) \in s) f (prod_tuple a).
Proof.
rewrite (reindex_onto (@tuple_prod _ _ _) (@prod_tuple _ _ _)) //=; last first.
  move=> ? _; by rewrite prod_tupleK.
apply eq_big => /=.
  move=> ? /=; by rewrite tuple_prodK eqxx andbC.
move=> ? _; by rewrite tuple_prodK.
Qed.

End rsum_rV_prod.

Section big_sum_rV_01.

Variable A : finType.

Lemma rsum_rV_0 F Q : \rsum_(j in 'rV[A]_0 | Q j) F j =
  if Q (row_of_tuple [tuple]) then F (row_of_tuple [tuple]) else 0.
Proof.
rewrite -big_map /= /index_enum -enumT /=.
set e := enum _.
rewrite (_ : e = [:: row_of_tuple [tuple]]).
  by rewrite /= big_cons big_nil addR0.
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

Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.

Lemma rsum_rV_1 F G P Q :
  (forall i : 'rV[A]_1, F i = G (i ``_ ord0)) ->
  (forall i : 'rV[A]_1, P i = Q (i ``_ ord0)) ->
  \rsum_(i in 'rV[A]_1 | P i) F i = \rsum_(i in A | Q i) G i.
Proof.
move=> FG PQ.
rewrite (reindex_onto (fun i => \row_(j < 1) i) (fun p => p ``_ ord0)) /=; last first.
  move=> m Pm.
  apply/matrixP => a b; rewrite {a}(ord1 a) {b}(ord1 b); by rewrite mxE.
apply eq_big => a.
  by rewrite PQ mxE eqxx andbT.
by rewrite FG !mxE.
Qed.

Lemma big_singl_rV (p : A -> R) :
  \rsum_(i in A) p i = 1%R -> \rsum_(i in 'rV[A]_1) p (i ``_ ord0) = 1%R.
Proof.
move=> <-.
rewrite (reindex_onto (fun j => \row_(i < 1) j) (fun p => p ``_ ord0)) /=.
- apply eq_big => a; first by rewrite mxE eqxx inE.
  move=> _; by rewrite mxE.
- move=> t _; apply/matrixP => a b; by rewrite (ord1 a) (ord1 b) mxE.
Qed.

End big_sum_rV_01.

Section big_sums_tuples.

Variable A : finType.

(* TODO: useless? *)
Lemma rsum_0_tuple F Q :
  \rsum_( j in {:0.-tuple A} | Q j) F j = if Q [tuple] then F [tuple] else 0.
Proof.
rewrite -big_map /= /index_enum -enumT (_ : enum (tuple_finType 0 A) = [tuple] :: [::]).
  by rewrite /= big_cons big_nil addR0.
apply eq_from_nth with [tuple] => /=.
  by rewrite size_tuple card_tuple.
move=> i.
rewrite size_tuple card_tuple expn0 ltnS leqn0 => /eqP ->{i}.
set e := enum _ .
destruct e => //.
apply val_inj => /=.
by case: s => -[].
Qed.

Lemma rsum_1_tuple F G P Q :
  (forall i : 1.-tuple A, F i = G (thead i)) ->
  (forall i : 1.-tuple A, P i = Q (thead i)) ->
  \rsum_(i in {: 1.-tuple A} | P i) F i = \rsum_(i in A | Q i) G i.
Proof.
move=> FG PQ.
rewrite (reindex_onto (fun i => [tuple of [:: i]]) (fun p => thead p)) /=; last first.
  case/tupleP => h t X; by rewrite theadE (tuple0 t).
apply eq_big => x //.
by rewrite (PQ [tuple x]) /= theadE eqxx andbC.
move=> X; by rewrite FG.
Qed.

Lemma big_singl_tuple (p : A -> R) :
  \rsum_(i in A) p i = 1 -> \rsum_(i in {: 1.-tuple A}) p (thead i) = 1.
Proof.
move=> <-.
rewrite (reindex_onto (fun j => [tuple of [:: j]]) (fun p => thead p)) => /=.
- apply eq_bigl => x; by rewrite theadE inE eqxx.
- by move=> i _; apply thead_tuple1.
Qed.

Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.

Lemma big_head_rbehead n (F : 'rV[A]_n.+1 -> R) (i : A) :
  \rsum_(j in 'rV[A]_n) (F (row_mx (\row_(k < 1) i) j)) =
  \rsum_(p in 'rV[A]_n.+1 | p ``_ ord0 == i) (F p).
Proof.
symmetry.
rewrite (reindex_onto (fun j : 'rV[A]_n => (row_mx (\row_(k < 1) i) j))
  (fun p : 'rV[A]_n.+1=> rbehead p)) /=; last first.
  move=> m Hm.
  apply/matrixP => a b; rewrite {a}(ord1 a).
  rewrite row_mx_rbehead //.
  by apply/eqP.
apply eq_bigl => /= x.
by rewrite rbehead_row_mx eqxx andbT row_mx_row_ord0 eqxx.
Qed.

(* TODO: rename *)
Lemma big_head_big_behead n (F : 'rV[A]_n.+1 -> R) (j : 'rV[A]_n) :
  \rsum_(i in A ) (F (row_mx (\row_(k < 1) i) j)) =
  \rsum_(p in 'rV[A]_n.+1 | rbehead p == j) (F p).
Proof.
apply/esym.
rewrite (reindex_onto (fun p => row_mx (\row_(k < 1) p) j) (fun p => p ``_ ord0) ) /=; last first.
  move=> i /eqP <-.
  apply/matrixP => a b; rewrite {a}(ord1 a).
  by rewrite row_mx_rbehead.
apply eq_bigl => /= a.
by rewrite rbehead_row_mx eqxx /= row_mx_row_ord0 eqxx.
Qed.

Lemma big_head_rbehead_P_set n (F : 'rV[A]_n.+1 -> R) (P1 : {set A}) (P2 : {set {: 'rV[A]_n}}) :
  \rsum_(i in P1) \rsum_(j in P2) (F (row_mx (\row_(k < 1) i) j))
  =
  \rsum_(p in 'rV[A]_n.+1 | (p ``_ ord0 \in P1) && (rbehead p \in P2)) (F p).
Proof.
apply/esym.
rewrite (@partition_big _ _ _ _ _ _ (fun x : 'rV[A]_n.+1 => x ``_ ord0)
  (fun x : A => x \in P1)) //=.
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

Lemma big_head_behead_P n (F : 'rV[A]_n.+1 -> R) (P1 : pred A) (P2 : pred 'rV[A]_n) :
  \rsum_(i in A | P1 i) \rsum_(j in 'rV[A]_n | P2 j) (F (row_mx (\row_(k < 1) i) j))
  =
  \rsum_(p in 'rV[A]_n.+1 | (P1 (p ``_ ord0)) && (P2 (rbehead p)) ) (F p).
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

Lemma big_head_behead n (F : 'rV[A]_n.+1 -> R) :
  \rsum_(i in A) \rsum_(j in 'rV[A]_n) (F (row_mx (\row_(k < 1) i) j)) =
  \rsum_(p in 'rV[A]_n.+1) (F p).
Proof. by rewrite big_head_behead_P. Qed.

Lemma big_tcast n (F : n.-tuple A -> R) (P : pred {: n.-tuple A}) m
  (n_m : m = n) :
  \rsum_(p in {: n.-tuple A} | P p) (F p) =
  \rsum_(p in {: m.-tuple A} | P (tcast n_m p)) (F (tcast n_m p)).
Proof.
subst m.
apply eq_bigr => ta.
case/andP => _ H.
by rewrite tcast_id.
Qed.

Local Open Scope tuple_ext_scope.

(* TODO: remove? *)
Lemma rsum_tuple_tnth n i (f : n.+1.-tuple A -> R):
  \rsum_(t | t \in {: n.+1.-tuple A}) f t =
  \rsum_(a | a \in A) \rsum_(t | t \_ i == a) f t.
Proof.
by rewrite (partition_big (fun x : n.+1.-tuple A => x \_ i) xpredT).
Qed.

Local Close Scope tuple_ext_scope.

End big_sums_tuples.

Section sum_tuple_ffun.

Import Monoid.Theory.

Variable R : Type.
Variable times : Monoid.mul_law 0.
Local Notation "*%M" := times (at level 0).
Variable plus : Monoid.add_law 0 *%M.
Local Notation "+%M" := plus (at level 0).

Lemma sum_tuple_ffun (I J : finType) (F : {ffun I -> J} -> R)
  (G : _ -> _ -> _) (jdef : J) (idef : I) :
  \big[+%M/0]_(j : #|I|.-tuple J) G (F (Finfun j)) (nth jdef j 0)
    = \big[+%M/0]_(f : {ffun I -> J}) G (F f) (f (nth idef (enum I) 0)).
Proof.
rewrite (reindex_onto (fun y => fgraph y) (fun p => Finfun p)) //.
apply eq_big; first by case => t /=; by rewrite eqxx.
move=> i _.
f_equal.
  by destruct i.
destruct i as [ [tval Htval] ].
rewrite [fgraph _]/= -(nth_map idef jdef); last first.
  rewrite -cardE.
  apply/card_gt0P.
  by exists idef.
by rewrite -codomE codom_ffun.
Qed.

End sum_tuple_ffun.

Lemma sum_f_R0_rsum : forall k (f : nat -> R),
  sum_f_R0 f k = \rsum_(i<k.+1) f i.
Proof.
elim => [f|] /=.
  by rewrite big_ord_recl /= big_ord0 addR0.
move=> k IH f.
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

(** Rle, Rlt lemmas for big-mult of reals *)

Reserved Notation "\rmul_ ( i : A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
     format "'[' \rmul_ ( i  :  A  |  P ) '/  '  F ']'").
Reserved Notation "\rmul_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50, only parsing).
Reserved Notation "\rmul_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
    format "'[' \rmul_ ( i  'in'  A ) '/  '  F ']'").
Notation "\rmul_ ( i | P ) F" := (\big[Rmult/1%R]_( i | P) F)
  (at level 41, F at level 41, i at level 50,
    format "'[' \rmul_ ( i | P ) '/  '  F ']'") : R_scope.
Reserved Notation "\rmul_ ( i < A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
     format "'[' \rmul_ ( i  <  A  |  P ) '/  '  F ']'").
Reserved Notation "\rmul_ ( i < t ) F"
  (at level 41, F at level 41, i, t at level 50,
    format "'[' \rmul_ ( i < t ) '/  '  F ']'").

Notation "\rmul_ ( i : A | P ) F" := (\big[Rmult/R1]_( i : A | P ) F): R_scope.
Notation "\rmul_ ( i : t ) F" := (\big[Rmult/R1]_( i : t ) F) : R_scope.
Notation "\rmul_ ( i 'in' A ) F" := (\big[Rmult/R1]_( i in A ) F) : R_scope.
Notation "\rmul_ ( i < A | P ) F" := (\big[Rmult/R1]_( i < A | P ) F): R_scope.
Notation "\rmul_ ( i < t ) F" := (\big[Rmult/R1]_( i < t ) F) : R_scope.

Section compare_big_mult.

Lemma Rlt_0_big_mult {A : finType} F : (forall i, 0 < F i) ->
  0 < \rmul_(i : A) F i.
Proof.
move=> H.
elim: (index_enum _) => [| hd tl IH].
rewrite big_nil; fourier.
rewrite big_cons; apply mulR_gt0 => //; by apply H.
Qed.

Lemma Rle_0_big_mult {A : finType} F : (forall i, 0 <= F i) ->
  0 <= \rmul_(i : A) F i.
Proof.
move=> H.
elim: (index_enum _) => [| hd tl IH].
  rewrite big_nil; fourier.
rewrite big_cons; apply mulR_ge0 => //; exact H.
Qed.

Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.

Lemma Rlt_0_rmul_inv {B : finType} F (HF: forall a, 0 <= F a) :
  forall n (x : 'rV[B]_n.+1),
  0 < \rmul_(i < n.+1) F (x ``_ i) -> forall i, 0 < F (x ``_ i).
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
  by apply HF.
  apply Rle_0_big_mult => i; by apply HF.
case.
case=> [Hi | i Hi].
  rewrite (_ : Ordinal _ = ord0); last by apply val_inj.
  by case: H.
case: H => _ H.
have : 0 < \rmul_(i0 < n.+1) F (t ``_ i0).
  suff : \rmul_(i < n.+1) F (x ``_ (lift ord0 i)) =
    \rmul_(i0 < n.+1) F (t ``_ i0).
    by move=> <-.
  apply eq_bigr => j _.
  by rewrite mxE.
have Hi' : (i < n.+1)%nat.
  clear -Hi; by rewrite ltnS in Hi.
move/IH.
move/(_ (Ordinal Hi')).
set o1 := Ordinal _.
set o2 := Ordinal _.
suff : lift ord0 o1 = o2.
  move=> <-.
  by rewrite mxE.
by apply val_inj.
Qed.

Lemma Rle_1_big_mult {A : finType}  f : (forall i, 1 <= f i) ->
  1 <= \rmul_(i : A) f i.
Proof.
move=> Hf.
elim: (index_enum _) => [| hd tl IH].
- rewrite big_nil; by apply Rle_refl.
- rewrite big_cons -{1}(mulR1 1%R).
  apply Rmult_le_compat => // ; fourier.
Qed.

Local Open Scope R_scope.

Lemma Rle_big_mult {A : finType} f g : (forall i, 0 <= f i <= g i) ->
  \rmul_(i : A) f i <= \rmul_(i : A) g i.
Proof.
move=> Hfg.
case/orP : (orbN [forall i, f i != 0%R]) ; last first.
- rewrite negb_forall => /existsP Hf.
  case: Hf => i0 /negPn/eqP Hi0.
  rewrite (bigD1 i0) //= Hi0 mul0R; apply Rle_0_big_mult.
  move=> i ; move: (Hfg i) => [Hi1 Hi2] ; by apply (Rle_trans _ _ _ Hi1 Hi2).
- move=> /forallP Hf.
  have Hprodf : 0 < \rmul_(i:A) f i.
    apply Rlt_0_big_mult => i.
    move: (Hf i) (Hfg i) => {Hf}Hf {Hfg}[Hf2 _].
    apply/RltP; rewrite Rlt_neqAle eq_sym Hf /=; by apply/RleP.
  apply (Rmult_le_reg_r (1 * / \rmul_(i : A) f i) _ _).
    apply Rlt_mult_inv_pos => //; fourier.
  rewrite mul1R Rinv_r; last by apply not_eq_sym, Rlt_not_eq.
  set inv_spec := fun r => if r == 0 then 0 else / r.
  rewrite (_ : / (\rmul_(a : A) f a) = inv_spec (\rmul_(a : A) f a)) ; last first.
    rewrite /inv_spec (_ : \rmul_(a : A) f a == 0 = false) //.
    apply/eqP ; by apply not_eq_sym, Rlt_not_eq.
  rewrite (@big_morph _ _ (inv_spec) R1 Rmult R1 Rmult _); last 2 first.
  - move=> a b /=.
    case/boolP : ((a != 0) && (b != 0)).
    - move=> /andP [/negbTE Ha /negbTE Hb] ; rewrite /inv_spec Ha Hb.
      move/negbT in Ha ; move/negbT in Hb.
      have : (a * b)%R == 0 = false ; last move=> ->.
      apply/negP => /eqP Habs.
        apply (Rmult_eq_compat_r (/ b)) in Habs ; move: Habs.
        rewrite -mulRA mul0R Rinv_r ?mulR1; move/eqP; by apply/negP.
      apply Rinv_mult_distr; move/eqP; by apply/negP.
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
  apply Rle_1_big_mult => i.
  move/(_ i) in Hf.
  move: Hfg => /(_ i) [Hf2 Hfg].
  rewrite /inv_spec.
  move/negbTE in Hf ; rewrite Hf ; move/negbT in Hf.
  rewrite -(Rinv_r (f i)); last by move/eqP; apply/negP.
  apply Rmult_le_compat_r => //.
  rewrite -(mul1R (/ f i)).
  apply Rle_mult_inv_pos; first fourier.
  apply/RltP; rewrite Rlt_neqAle eq_sym Hf /=; by apply/RleP.
Qed.

Local Close Scope R_scope.

End compare_big_mult.

Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.

Lemma log_rmul_rsum_mlog {A : finType} (f : A -> R+) : forall n (ta : 'rV[A]_n.+1),
  (forall i, 0 < f ta ``_ i) ->
  (- log (\rmul_(i < n.+1) f ta ``_ i) = \rsum_(i < n.+1) - log (f ta ``_ i))%R.
Proof.
elim => [i Hi | n IH].
  by rewrite big_ord_recl big_ord0 mulR1 big_ord_recl big_ord0 addR0.
move=> ta Hi.
rewrite big_ord_recl /= log_mult; last 2 first.
  by apply Hi.
  apply Rlt_0_big_mult => i; by apply Hi.
set tl := \row_(i < n.+1) ta ``_ (lift ord0 i).
have Htmp : forall i0 : 'I_n.+1, 0 < f tl ``_ i0.
  move=> i.
  rewrite mxE.
  by apply Hi.
move: {IH Htmp}(IH _ Htmp) => IH.
have -> : \rmul_(i < n.+1) f ta ``_ (lift ord0 i) = \rmul_(i0<n.+1) f tl ``_ i0.
  apply eq_bigr => i _.
  congr (f _).
  by rewrite /tl mxE.
rewrite oppRD [X in _ = X]big_ord_recl IH.
congr (_ + _)%R.
apply eq_bigr => i _; by rewrite /tl mxE.
Qed.

Local Close Scope tuple_ext_scope.
