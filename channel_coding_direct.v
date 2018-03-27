(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix perm.
Require Import Reals Fourier Classical.
Require Import Reals_ext ssr_ext Rssr log2 ssralg_ext Rbigop proba entropy.
Require Import aep typ_seq joint_typ_seq channel channel_code.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope proba_scope.
Local Open Scope jtyp_seq_scope.
Local Open Scope channel_code_scope.
Local Open Scope channel_scope.

Module Wght.

Section Wght_sect.

Variables A M : finType.
Variable P : dist A.
Variable n : nat.

Definition pmf := fun f : encT A M n => \rprod_(m in M) P `^ n (f m).

Lemma pmf0 (f : {ffun M -> 'rV[A]_n}) : 0 <= pmf f.
Proof. apply rprodr_ge0 => ?; exact: dist_nonneg. Qed.

Lemma pmf1 : \rsum_(f | f \in {ffun M -> 'rV[A]_n}) pmf f = 1.
Proof.
rewrite -(bigA_distr_bigA (fun _ ta => P `^ n ta)) /=.
rewrite [X in _ X](_ : 1 = \rprod_(i : M | xpredT i) 1); last first.
  by rewrite big_const /= iter_Rmult pow1.
apply eq_bigr => _ _; by rewrite (pmf1 (P `^ n)).
Qed.

Definition d : dist [finType of encT A M n] := locked (makeDist pmf0 pmf1).

End Wght_sect.

End Wght.

Arguments Wght.d [A] [M] _ [n].

Section joint_typicality_decoding.

Variables A B M : finType.
Variable n : nat.

(** Joint typicality decoding *)

Definition jtdec P W epsilon (f : encT A M n) : decT B M n :=
  [ffun tb => [pick m |
    (prod_rV (f m, tb) \in `JTS P W n epsilon) &&
    [forall m', (m' != m) ==> (prod_rV (f m', tb) \notin `JTS P W n epsilon)]]].

Lemma jtdec_map epsilon (P : dist A) (W : `Ch_1(A, B)) (f : encT A M n) tb m0 m1 :
  (prod_rV (f m0, tb) \in `JTS P W n epsilon) &&
  [forall m', (m' != m0) ==> (prod_rV (f m', tb) \notin `JTS P W n epsilon)] ->
  (prod_rV (f m1, tb) \in `JTS P W n epsilon) &&
  [forall m', (m' != m1) ==> (prod_rV (f m', tb) \notin `JTS P W n epsilon)] ->
  m0 = m1.
Proof.
case/andP.
rewrite /prod_rV /= => H1 H2.
case/andP => H1'.
move/forallP/(_ m0).
rewrite implybE.
case/orP.
- rewrite negbK; by move/eqP.
- by rewrite H1.
Qed.

Hypothesis HM : (0 < #|M|)%nat.

Lemma good_code_sufficient_condition P W epsilon
  (phi : encT A M n -> decT B M n) :
  \rsum_(f : encT A M n) (Wght.d P f * echa(W , mkCode f (phi f))) < epsilon ->
  exists f, echa(W , mkCode f (phi f)) < epsilon.
Proof.
move=> H.
apply not_all_not_ex => abs.
set x := \rsum_(f <- _) _ in H.
have : \rsum_(f : encT A M n) Wght.d P f * epsilon <= x.
  rewrite /x.
  apply ler_rsum_l => //= i _.
  - apply Rmult_le_compat_l; [exact/dist_nonneg | exact/Rnot_lt_le/abs].
  - apply mulR_ge0; [exact/dist_nonneg | exact/echa_pos].
apply Rlt_not_le, Rlt_le_trans with epsilon => //.
rewrite -big_distrl /= (pmf1 (Wght.d P)) mul1R; exact/Rle_refl.
Qed.

Definition o_PI (m m' : M) := fun g : encT A M n => [ffun x => g (tperm m m' x)].

Lemma o_PI_2 (g : encT A M n) (m m' m_ : M) : (o_PI m m' (o_PI m m' g)) m_ = g m_.
Proof. by rewrite /o_PI !ffunE tpermK. Qed.

Lemma wght_o_PI m m' P (h : encT A M n) : Wght.d P (o_PI m m' h) = Wght.d P h.
Proof.
rewrite /Wght.d -lock /Wght.pmf /= (reindex_onto (fun m_ => (tperm m m') m_)
  (fun m_ => (tperm m m') m_)) /=; last first.
  move=> i _; by rewrite tpermK.
apply eq_big => m_.
by rewrite tpermK eqxx.
move=> _; by rewrite /o_PI ffunE tpermK.
Qed.

Lemma error_rate_symmetry (P : {dist A}) (W : `Ch_1(A, B)) epsilon :
  0 <= epsilon -> let Jtdec := jtdec P W epsilon in
    forall m m',
      \rsum_(f : encT A M n) (Wght.d P f * e(W, mkCode f (Jtdec f)) m) =
      \rsum_(f : encT A M n) (Wght.d P f * e(W, mkCode f (Jtdec f)) m').
Proof.
move=> Hepsilon PHI' m m'.
set lhs := \rsum_(_ <- _) _.
have Hlhs : lhs = \rsum_(f : encT A M n) (Wght.d P f * e(W, mkCode f (PHI' f)) m).
  done.
have Hlhs2 : lhs = \rsum_(f : encT A M n)
  (Wght.d P (o_PI m m' f) * e(W, mkCode (o_PI m m' f) (PHI' (o_PI m m' f))) m).
  rewrite Hlhs (reindex_onto (o_PI m m') (o_PI m m')) /=; last first.
    move=> i _; apply/ffunP => m_; by rewrite o_PI_2.
  apply eq_bigl => x /=.
  apply/eqP.
  apply/ffunP => y.
  by apply: o_PI_2.
rewrite Hlhs2.
apply eq_bigr => g _.
rewrite wght_o_PI; congr (_ * _).
rewrite /ErrRateCond /= (_ : (o_PI m m' g) m = g m'); last by rewrite ffunE tpermL.
apply Pr_ext; apply/setP => tb /=.
rewrite 2!inE.
apply/negbLR. rewrite in_setC negbK.
apply/idP/idP.
- rewrite {1}/PHI' {1}/jtdec.
  rewrite ffunE.
  set p0 := fun _ => _ && _.
  case: (pickP _) => [m0 Hm0 | Hm0].
  + case/eqP => ?; subst m0.
    rewrite /p0 {p0} in Hm0.
    rewrite /PHI' /jtdec.
    rewrite inE ffunE.
    case: (pickP _) => [m1 Hm1 | Hm1].
    * apply/eqP; f_equal.
      have Hm' : (prod_rV (g m', tb) \in `JTS P W n epsilon) &&
        [forall m'0, (m'0 != m') ==> (prod_rV (g m'0, tb) \notin `JTS P W n epsilon)].
        apply/andP; split.
        - rewrite {1}/o_PI ffunE tpermL in Hm0. by case/andP : Hm0.
        - apply/forallP => m_. apply/implyP => m__m'.
          case/andP : Hm0 => Hm0. move/forallP => Hm0'.
          case/boolP : (m_ == m) => m__m.
          + move/eqP in m__m; subst m_.
            move: {Hm0'}(Hm0' m') => Hm0'.
            rewrite eqtype.eq_sym m__m' /= /o_PI ffunE tpermR in Hm0'. by apply Hm0'.
          + move: {Hm0'}(Hm0' m_) => Hm0'.
            rewrite eqtype.eq_sym in m__m'.
            rewrite m__m /= /o_PI ffunE tpermD // in Hm0'; by rewrite eqtype.eq_sym.
      by apply: (jtdec_map Hm1 Hm').
    * suff : False by done.
      rewrite {1}/o_PI ffunE tpermL in Hm0.
      move/negbT: {Hm1}(Hm1 m').
      rewrite negb_and; case/orP => Hm'.
      - case/andP : Hm0 => Hm0 _; by rewrite Hm0 in Hm'.
        move/negP : Hm'; apply.
        apply/forallP => m_. apply/implyP => m__m'.
        case/andP: Hm0 => Hm0.
        move/forallP => Hm01.
        case/boolP : (m_ == m) => m__m.
        + move/eqP in m__m; subst m_.
          move: {Hm01}(Hm01 m') => Hm01.
          rewrite eqtype.eq_sym m__m' /= /o_PI ffunE tpermR in Hm01. by apply Hm01.
        + move: {Hm01}(Hm01 m_) => Hm01.
          rewrite m__m /= /o_PI ffunE tpermD // in Hm01; by rewrite eqtype.eq_sym.
  + by move/eqP.
- rewrite {1}/PHI' {1}/jtdec.
  rewrite inE ffunE.
  case: (pickP _) => [m0 Hm0 | Hm0].
  + case/eqP => ?; subst m0.
    apply/eqP.
    rewrite /PHI' /jtdec.
    rewrite ffunE.
    case: (pickP _) => [m1 Hm1 | Hm1].
    * f_equal.
      have {Hm0}Hm0 : (prod_rV ((o_PI m m' g) m, tb) \in `JTS P W n epsilon) &&
        [forall m'0, (m'0 != m) ==>
           (prod_rV ((o_PI m m' g) m'0, tb) \notin `JTS P W n epsilon)].
        apply/andP; split.
        - rewrite /o_PI ffunE tpermL. by case/andP: Hm0.
        - apply/forallP => m_.
          apply/implyP => m__m.
          case/boolP : (m_ == m').
          + move/eqP => ?; subst m_.
            rewrite /o_PI ffunE tpermR.
            case/andP : Hm0 => _.
            move/forallP. move/(_ m). by rewrite eqtype.eq_sym m__m.
          + move=> m__m'.
            rewrite eqtype.eq_sym in m__m. rewrite eqtype.eq_sym in m__m'.
            rewrite /o_PI ffunE tpermD //.
            case/andP : Hm0 => _.
            move/forallP. move/(_ m_). by rewrite eqtype.eq_sym m__m'.
      by apply: (jtdec_map Hm1 Hm0).
    * suff : False by done.
      move: {Hm1}(Hm1 m).
      move/negbT. rewrite negb_and. case/orP.
      - rewrite /o_PI ffunE tpermL.
        by case/andP : Hm0 => ->.
      - move/negP; apply.
        apply/forallP => m_.
        apply/implyP => m__m.
        case/boolP : (m_ == m').
        + move/eqP => ?; subst m_.
          rewrite /o_PI ffunE tpermR.
          case/andP : Hm0 => _.
          move/forallP. move/(_ m). by rewrite eqtype.eq_sym m__m.
        + move=> m__m'.
          rewrite eqtype.eq_sym in m__m. rewrite eqtype.eq_sym in m__m'.
          rewrite /o_PI ffunE tpermD //.
          case/andP : Hm0 => _.
          move/forallP. move/(_ m_). by rewrite eqtype.eq_sym m__m'.
  + by move/eqP.
Qed.

End joint_typicality_decoding.

Section sum_rV_ffun.

Import Monoid.Theory.

Variable R : Type.
Variable times : Monoid.mul_law 0.
Local Notation "*%M" := times (at level 0).
Variable plus : Monoid.add_law 0 *%M.
Local Notation "+%M" := plus (at level 0).

Lemma sum_rV_ffun (I J : finType) (F : {ffun I -> J} -> R)
  (G : _ -> _ -> _) (idef : I) (zero : 'I_ _) : O = zero ->
  \big[+%M/0]_(j : 'rV[J]_#|I|) G (F [ffun x => j ord0 (enum_rank x)]) (j ord0 zero)
    = \big[+%M/0]_(f : {ffun I -> J}) G (F f) (f (nth idef (enum I) 0)).
Proof.
Local Open Scope ring_scope.
move=> Hzero.
rewrite (reindex_onto (fun y : {ffun _ -> _} => \row_(i < _) y (enum_val i))
                      (fun p => [ffun x => p ord0 (enum_rank x)])) //.
  apply eq_big.
    move=> t /=.
    apply/eqP/ffunP => i'.
    by rewrite ffunE mxE enum_rankK.
  move=> i Hi.
  rewrite /= in Hi.
  rewrite (eqP Hi).
  f_equal.
  by rewrite mxE (enum_val_nth idef) -Hzero.
move=> i _.
apply/matrixP => a b; rewrite {a}(ord1 a).
by rewrite mxE ffunE enum_valK.
Qed.

End sum_rV_ffun.

Section random_coding_good_code_existence.

Variables B A : finType.
Variable W : `Ch_1(A, B).
Variable P : dist A.

Definition epsilon0_condition r epsilon epsilon0 :=
  0 < epsilon0 /\ epsilon0 < epsilon / 2 /\ epsilon0 < (`I(P ; W) - r) / 4.

Definition n_condition r epsilon0 n :=
  (O < n)%nat /\ - log epsilon0 / epsilon0 < INR n /\
  frac_part (exp2 (INR n * r)) = 0 /\ (JTS_1_bound P W epsilon0 <= n)%nat.

(** the set of output tb such that (f m, tb) is jointly typical: *)

Definition cal_E M n epsilon (f : encT A M n) m :=
  [set tb | prod_rV (f m, tb) \in `JTS P W n epsilon].

Local Open Scope tuple_ext_scope.

(* TODO: clean *)
Lemma big_head_behead_P_tuple {C:finType} n (F : n.+1.-tuple C -> R) (P1 : pred C) (P2 : pred ({: n.-tuple C})) :
  \rsum_(i in C | P1 i) \rsum_(j in {: n.-tuple C} | P2 j) (F [tuple of (i :: j)])
  =
  \rsum_(p in {: n.+1.-tuple C} | (P1 (thead p)) && (P2 (tbehead p)) ) (F p).
Proof.
symmetry.
rewrite (@partition_big _ _ _ _ _ _ (fun x : {: n.+1.-tuple C} => thead x)
  (fun x : C => P1 x)) //=.
- apply eq_bigr => i Hi.
  rewrite (reindex_onto (fun j : {: n.-tuple C} => [tuple of (i :: j)])
    (fun p => [tuple of (behead p)])) /=; last first.
    move=> j Hj.
    case/andP : Hj => Hj1 /eqP => <-.
    symmetry.
    by apply tuple_eta.
  apply congr_big => // x /=.
  rewrite !theadE eqxx /= Hi /= -andbA /=.
  set tmp := _ == x.
  have Htmp : tmp = true.
    rewrite /tmp tupleE /behead_tuple /=.
    apply/eqP => /=.
    by apply val_inj.
  rewrite Htmp andbC /=.
  f_equal.
  by apply/eqP.
move=> i; by case/andP.
Qed.

(* NB: similar lemma in proba2.v *)
Lemma rsum_rmul_tuple_pmf_tnth {C : finType} n k (Q : dist C) :
  \rsum_(t : {:k.-tuple ('rV[C]_n)}) \rprod_(m < k) (Q `^ n) t \_ m = 1%R.
Proof.
transitivity (\rsum_(j : {ffun 'I_k -> 'rV[_]_n})
  \rprod_(m < k) Q `^ _ (j m)).
  rewrite (reindex_onto (fun p => Finfun p) (fun x => fgraph x)) //=; last by case.
  rewrite (big_tcast _ _ (card_ord k)) //.
  apply eq_big => //.
  - move=> i /=; by rewrite eqxx.
  - move=> i _.
    apply eq_bigr => j _; by rewrite FunFinfun.fun_of_finE tcastE enum_rank_ord.
rewrite -(bigA_distr_bigA (fun m xn => Q `^ _ xn)) /= big_const.
rewrite (_ : \rsum_(_ <- _) _ = 1%R); last by rewrite pmf1.
by rewrite iter_Rmult pow1.
Qed.

Lemma first_summand k n epsilon0 :
  let M := [finType of 'I_k.+1] in
  \rsum_(f : encT A M n) Wght.d P f *
    Pr (W ``(| f ord0)) (~: cal_E epsilon0 f ord0) =
  Pr (`J(P , W) `^ n) (~: `JTS P W n epsilon0).
Proof.
move=> M.
have M_prednK : #|M|.-1.+1 = #|M| by rewrite card_ord.
set E_F_N := @cal_E M n epsilon0.
rewrite {1}/E_F_N {1}/cal_E.
case/card_gt0P : (dist_domain_not_empty P) => xdef _.
pose zero := @enum_rank M ord0.
move: (@sum_rV_ffun _ mulR_muloid addR_addoid M [finType of 'rV[A]_n]
  (fun f => \rprod_(m : M) P `^ n (f m))
  (fun r => fun ta => (r * Pr ( W ``(| ta ) )
    (~: [set tb | prod_rV (ta, tb) \in `JTS P W n epsilon0]))%R)
  ord0 zero).
rewrite (_ : nth ord0 (enum M) 0 = ord0); last by rewrite enum_ordS.
rewrite /Wght.d -lock /= => <-.
transitivity (\rsum_(ta : 'rV['rV[A]_n]_#|M|) (
    (\rprod_(m : M) P `^ n ([ffun x => ta ord0 x] (enum_rank m))) *
    \rsum_(tb | tb \in ~: cal_E epsilon0 [ffun x => ta ord0 x] zero)
    (W ``(| [ffun x => ta ord0 x] zero)) tb))%R.
  apply eq_bigr => ta _.
  congr (_ * _); first by apply eq_bigr => m _; rewrite 2!ffunE.
  apply eq_big.
  - move=> /= vb; by rewrite !inE ffunE.
  - move=> cb _; by rewrite ffunE.
rewrite /cal_E.
transitivity (\rsum_(ta : 'rV[A]_n)
  (\rsum_(y in ~: [set y0 | prod_rV (ta, y0) \in `JTS P W n epsilon0])
    ((W ``(| ta)) y)) *
  \rsum_(j in {: #|M|.-1.-tuple ('rV[A]_n)})
  (\rprod_(m : M) P `^ _ (Finfun (tcast M_prednK [tuple of ta :: j]) m))).
Local Open Scope ring_scope.
  rewrite (reindex_onto (fun y : {ffun _ -> _} => \row_(i < _) y (enum_val i))
                        (fun p : 'rV_ _ => [ffun x => p ord0 (enum_rank x)])) //=; last first.
    move=> i _.
    by apply/matrixP => a b; rewrite {a}(ord1 a) mxE ffunE enum_valK.
  apply trans_eq with (\rsum_(j : {ffun M -> _})
    ((\rprod_(m < k.+1) P `^ n (j m)) *
      (\rsum_(y in ~: [set y0 | prod_rV (j ord0, y0) \in `JTS P W n epsilon0])
      W ``(y | j ord0))))%R.
    apply eq_big => //= f.
    - apply/eqP/ffunP => m; by rewrite ffunE mxE enum_rankK.
    - move/eqP => Hf.
      congr (_ * _)%R.
        apply eq_bigr => i _; by rewrite -[in RHS]Hf 2!ffunE.
      apply eq_big => /=.
        move=> vb; by rewrite !inE -[in RHS]Hf !ffunE mxE.
      move=> vb _; by rewrite -[in RHS]Hf !ffunE mxE.
  rewrite (_ : ord0 = nth ord0 (enum M) 0); last by rewrite enum_ordS.
  rewrite -(big_tuple_ffun _ (fun f => \rprod_(m : M) P `^ n (f m))
    (fun r => fun yn => r *
      (\rsum_(y in ~: [set y0 | prod_rV (yn, y0) \in `JTS P W n epsilon0])
      W ``(y | yn))) (\row_(i < n) xdef) ord0)%R.
  transitivity (\rsum_(j : _)
    ((\rprod_(m : M) P `^ n (Finfun (tcast M_prednK j) m)) *
      (\rsum_(y in ~: [set y0 | prod_rV (nth (\row_(i < n) xdef) j 0, y0) \in
          `JTS P W n epsilon0])
      W ``(y | nth (\row_(i < n) xdef) j 0))))%R.
    rewrite (big_tcast _ _ M_prednK) //.
    apply eq_bigr => i _.
    congr (_ * _)%R.
    have Hcst : nth (\row_(i < n) xdef) (tcast M_prednK i) 0 =
      nth (\row_(i < n) xdef) i 0.
      move: M_prednK i; rewrite card_ord => M_prednK i.
      rewrite -(tnth_nth _ i ord0) -(tnth_nth _ (tcast M_prednK i) ord0).
      by rewrite tcastE /= cast_ord_id.
    apply eq_big.
    - move=> vb; by rewrite !inE Hcst.
    - move=> *; by rewrite Hcst.
  rewrite -(@big_head_behead_P_tuple _ #|M|.-1
   (fun j => ((\rprod_(m : M) P `^ n (Finfun (tcast M_prednK j) m)) *
     (\rsum_(y in ~: [set y0 | prod_rV (nth (\row_(i < n) xdef) j 0, y0) \in
         `JTS P W n epsilon0]) W ``(y | nth (\row_(i < n) xdef) j 0)))) xpredT xpredT)%R.
  apply eq_bigr => ta _ /=.
  by rewrite -big_distrl /= mulRC.
transitivity (
  (\rsum_(ta in 'rV[A]_n) P `^ _ ta *
    (\rsum_(y in ~: [set y0 | prod_rV (ta, y0) \in `JTS P W n epsilon0])
    (W ``(| ta ) ) y)) *
    (\rsum_(j in {:k.-tuple ('rV[A]_n)}) \rprod_(m < k) (P `^ _ (j \_ m))))%R.
  rewrite big_distrl /=.
  apply eq_bigr => ta _.
  rewrite -mulRA [X in _ = X]mulRC -mulRA.
  f_equal.
  transitivity (\rsum_(j in {: #|'I_k|.-tuple ('rV[A]_n) })
    P `^ _ ta * \rprod_(m < k) P `^ _ (Finfun j m))%R.
    have k_prednK : #|'I_k.+1|.-1 = #|'I_k| by rewrite !card_ord.
    rewrite (big_tcast _ _ k_prednK) //.
    apply eq_bigr => i0 Hi0.
    rewrite big_ord_recl /=.
    f_equal.
      by rewrite FunFinfun.fun_of_finE tcastE enum_rank_ord cast_ord_comp.
    apply eq_bigr => i1 _.
    f_equal.
    symmetry.
    rewrite {1}FunFinfun.fun_of_finE tcastE enum_rank_ord cast_ord_comp.
    symmetry.
    rewrite FunFinfun.fun_of_finE tcastE enum_rank_ord cast_ord_comp /tnth /=.
    apply set_nth_default.
    by rewrite size_tuple card_ord /= (ltn_ord i1).
  rewrite -big_distrr /= [X in _ = X]mulRC; congr (_ * _)%R.
  rewrite (big_tcast _ _ (card_ord k)) //.
  apply eq_bigr => i0 Hi0.
  apply eq_bigr => i1 Hi1.
  congr (P `^ _ _).
  by rewrite FunFinfun.fun_of_finE tcastE enum_rank_ord.
rewrite rsum_rmul_tuple_pmf_tnth mulR1.
transitivity (\rsum_(ta in 'rV[A]_n)
  (\rsum_(y in ~: [set y0 | prod_rV (ta, y0) \in `JTS P W n epsilon0])
  ((`J(P , W)) `^ n (prod_rV (ta, y))))).
  apply eq_bigr => ta _.
  rewrite big_distrr /=.
  apply eq_bigr => // tb Htb.
  rewrite DMCE.
  rewrite 2!TupleDist.dE.
  rewrite -big_split /=; apply eq_bigr => /= i _.
  by rewrite JointDist.dE -fst_tnth_prod_rV -snd_tnth_prod_rV /= mulRC.
rewrite /Pr big_rV_prod pair_big_dep /=.
apply eq_bigl; case=> /= ta tb; by rewrite !inE.
by rewrite /zero enum_rank_ord.
Qed.


Lemma big_head_behead_tuple {C:finType} n (F : n.+1.-tuple C -> R) :
  \rsum_(i in C) \rsum_(j in {: n.-tuple C}) (F [tuple of (i :: j)]) =
  \rsum_(p in {: n.+1.-tuple C}) (F p).
Proof. by rewrite big_head_behead_P_tuple. Qed.

Lemma big_cat_tuple {C:finType} m n (F : (m + n)%nat.-tuple C -> R) :
  \rsum_(i in {:m.-tuple C} ) \rsum_(j in {: n.-tuple C})
  F [tuple of (i ++ j)] = \rsum_(p in {: (m + n)%nat.-tuple C}) (F p).
Proof.
move: m n F.
elim.
- move=> m2 F /=.
  transitivity ( \rsum_(i <- [tuple] :: [::])
    \rsum_(j in tuple_finType m2 C) F [tuple of i ++ j] ).
    apply congr_big => //=.
    symmetry.
    rewrite /index_enum /=.
    rewrite Finite.EnumDef.enumDef /=.
    apply eq_from_nth with [tuple] => //=.
    by rewrite FinTuple.size_enum expn0.
    case=> //= _.
    destruct (FinTuple.enum 0 C) => //.
    by rewrite (tuple0 t).
  rewrite big_cons /= big_nil /= addR0.
  apply eq_bigr => // i _.
  f_equal.
  by apply val_inj.
- move=> m IH n F.
  symmetry.
  transitivity (\rsum_(p in tuple_finType (m + n).+1 C) F p); first by apply congr_big.
  rewrite -big_head_behead_tuple -big_head_behead_tuple.
  apply eq_bigr => i _.
  symmetry.
  move: {IH}(IH n (fun x => F [tuple of i :: x])) => <-.
  apply eq_bigr => i0 _.
  apply eq_bigr => i1 _.
  f_equal.
  by apply val_inj.
Qed.


Lemma big_cat_tuple_seq {C:finType} m n (F : seq C -> R) :
  \rsum_(i in {:m.-tuple C} ) \rsum_(j in {: n.-tuple C}) (F (i ++ j)) =
  \rsum_(p in {: (m + n)%nat.-tuple C}) (F p).
Proof.
move: (@big_cat_tuple _ m n (fun l => if size l == (m + n)%nat then F l else 0%R)) => IH.
set lhs := \rsum_(i in _) _ in IH.
apply trans_eq with lhs.
rewrite /lhs.
apply eq_bigr => i _.
apply eq_bigr => j _.
set test := _ == _.
have Htest : test = true by rewrite /test size_tuple eqxx.
case: ifP => // abs.
by rewrite abs in Htest.
rewrite IH.
apply eq_bigr => i _.
by rewrite size_tuple eqxx.
Qed.

Lemma rsum_rmul_tuple_pmf {C} n k (Q : dist C) :
  (\rsum_(t in {:k.-tuple ('rV[C]_n)}) \rprod_(x <- t) (Q `^ n) x = 1)%R.
Proof.
rewrite -[X in _ = X](rsum_rmul_tuple_pmf_tnth n k Q).
apply eq_bigr => t _.
rewrite big_tnth /=.
rewrite (reindex_onto (cast_ord (size_tuple t))
  (cast_ord (esym (size_tuple t)))) //=; last first.
  move=> i _; by apply val_inj.
apply eq_big => //= i.
- symmetry.
  apply/val_eqP.
  by apply val_inj.
- move=> _; by rewrite !tvalK tcastE esymK.
Qed.

Lemma second_summand n k epsilon0 :
  let M := [finType of 'I_k.+1] in
    forall i, i != ord0 ->
      (\rsum_(f : encT A M n) Wght.d P f *
        Pr (W ``(| f ord0)) (cal_E epsilon0 f i))%R =
   Pr ((P `^ n) `x ((`O( P , W )) `^ n)) [set x | prod_rV x \in `JTS P W n epsilon0].
Proof.
move=> M.
have M_prednK : #|M|.-1.+1 = #|M| by rewrite card_ord.
move=> i i_m0.
set E_F_N := @cal_E M n epsilon0.
have Hcast : (i.-1 + (#|M| - i.+1).+1).+1 = #|M|.
  rewrite /M card_ord subSS addnS -addSn prednK; last by rewrite lt0n.
  by rewrite subnKC // -ltnS ltn_ord.
transitivity (
  \rsum_(j1 in {: i.-1.-tuple ('rV[A]_n)})
  \rsum_(j2 in {: (#|M| - i.+1).-tuple ('rV[A]_n)})
  \rsum_(j0 in 'rV[A]_n)
  \rsum_(ji in 'rV[A]_n)
  Wght.d P (Finfun (tcast Hcast [tuple of j0 :: j1 ++ ji :: j2])) *
  \rsum_( y | y \in [set y0 | prod_rV (ji, y0) \in `JTS P W n epsilon0])
  (W ``(| j0)) y)%R.
  transitivity (
    \rsum_(j0 in 'rV[A]_n)
    \rsum_(j1 in {: i.-1.-tuple ('rV[A]_n)})
    \rsum_(ji in 'rV[A]_n)
    \rsum_(j2 in {: (#|M| - i.+1).-tuple ('rV[A]_n)})
    Wght.d P (Finfun (tcast Hcast [tuple of j0 :: j1 ++ ji :: j2])) *
    \rsum_( y | y \in [set y0 | prod_rV (ji, y0) \in `JTS P W n epsilon0])
    (W ``(| j0) ) y)%R.
    rewrite (reindex_onto (fun p => Finfun p) (fun y => fgraph y)) /=; last by case.
    transitivity ( \rsum_(j : _)
      (Wght.d P (Finfun j) * Pr (W ``(| Finfun j ord0)) (E_F_N (Finfun j) i)))%R.
      apply eq_big => //= x; by rewrite eqxx.
    rewrite (big_tcast _ _ (esym (card_ord k.+1))) //.
    rewrite -big_head_behead_tuple.
    apply eq_bigr => i0 _.
    have [Hq i_q] : (i.-1 + (k - i.-1) = k /\ i <= k)%nat.
      split.
        rewrite addnBA; last first.
          apply leq_trans with i; last by rewrite -ltnS; apply ltn_ord.
          by apply leq_pred.
        by rewrite addnC -addnBA // subnn addn0.
      by apply (ltn_ord i).
    rewrite (big_tcast _ _ Hq) //.
    rewrite -big_cat_tuple /=.
    apply eq_bigr => /= i1 _.
    have Hs : ((k-i).+1 = k - i.-1)%nat.
      rewrite -subn1 subnBA; last by rewrite lt0n.
      by rewrite addnC -addnBA.
    rewrite (big_tcast _ _ Hs) // -big_head_behead_tuple.
    apply eq_bigr => i2 _.
    have Ht : (k - i)%nat = (#|'I_k.+1| - i.+1)%nat by rewrite card_ord /= subSS.
    rewrite (big_tcast _ _ Ht) //.
    apply eq_bigr => i3 _.
    rewrite /Wght.d -lock /Wght.pmf /=.
    f_equal.
    - f_equal.
      apply FunctionalExtensionality.functional_extensionality => i4 /=.
      do 4 f_equal.
      apply: eq_tcast => /=.
      symmetry.
      apply: eq_tcast2 => /=.
      f_equal.
      apply: eq_tcast2 => /=.
      f_equal.
      apply: eq_tcast2 => /=.
      f_equal.
      symmetry.
      by apply: eq_tcast2.
    - rewrite /Pr.
      apply eq_big.
      + move=> x /=.
        rewrite !inE.
        set f1 := (Finfun _) _.
        suff : f1 = i2 by move=> ->.
        rewrite /f1 {f1} !FunFinfun.fun_of_finE /= enum_rank_ord /= tcastE !cast_ord_comp.
        rewrite (tnth_nth i0) /=.
        rewrite (_ : tval (tcast Hq [tuple of i1 ++ tcast Hs [tuple of i2 :: i3]]) = i1 ++ i2 :: i3); last first.
          symmetry.
          apply eq_tcast2 => /=.
          f_equal.
          by apply eq_tcast2.
        rewrite -cat_cons nth_cat /= size_tuple prednK; last by rewrite lt0n.
        by rewrite ltnn subnn.
      + move=> i4 Hi4.
        rewrite 2!DMCE.
        apply eq_bigr => i5 /= _.
        f_equal.
        by rewrite !FunFinfun.fun_of_finE tcastE /= enum_rank_ord /= cast_ordK.
  rewrite exchange_big /=.
  apply eq_bigr => /= i1 _.
  symmetry.
  rewrite exchange_big /=.
  apply eq_bigr => /= i2 _.
  rewrite exchange_big /=.
  by apply eq_bigr.
transitivity (
  (\rsum_(j1 in {: i.-1.-tuple ('rV[A]_n)})
   \rsum_(j2 in {: (#|M| - i.+1).-tuple ('rV[A]_n)})
   \rprod_(i <- j1 ++ j2) (P `^ n) i) *
  (\rsum_(j0 in 'rV[A]_n)
    \rsum_(ji in 'rV[A]_n)
    ((P `^ n) j0) * ((P `^ n) ji) *
    (\rsum_( y | y \in
      [set y0 | prod_rV (ji , y0) \in `JTS P W n epsilon0])
    (W ``(| j0) ) y)))%R.
  rewrite !big_distrl /=.
  apply eq_bigr => j1 _.
  rewrite !big_distrl /=.
  apply eq_bigr => j2 _.
  rewrite !big_distrr /=.
  apply eq_bigr => j0 _.
  rewrite !big_distrr /=.
  apply eq_bigr => j3 _.
  rewrite !mulRA /Wght.d -lock /Wght.pmf /=.
  congr (_ * _)%R.
  transitivity (\rprod_( i <- j0 :: j1 ++ j3 :: j2) P `^ _ i)%R; last first.
    rewrite big_cons -mulRA [in X in _ = X]mulRC -mulRA.
    congr (_ * _)%R.
    rewrite big_cat /= big_cons mulRC -[in X in X = _]mulRA.
    congr (_ * _)%R.
    by rewrite big_cat /= mulRC.
  symmetry.
  rewrite (big_nth j0) /= big_mkord.
  symmetry.
  rewrite (reindex_onto enum_val enum_rank) /=; last first.
    move=> i0 _; by rewrite enum_rankK.
  transitivity (\rprod_(j < #|@predT M|)
    P `^ _ ((Finfun (tcast Hcast [tuple of j0 :: j1 ++ j3 :: j2])) (enum_val j)))%R.
    apply eq_bigl => i0 /=.
    by rewrite enum_valK eqxx.
  have j_M : (size (j1 ++ j3 :: j2)).+1 = #|M|.
    rewrite size_cat (size_tuple j1) /= (size_tuple j2) card_ord.
    rewrite <- (card_ord k.+1).
    by rewrite -Hcast card_ord.
  rewrite j_M.
  apply eq_bigr => i0 _.
  f_equal.
  rewrite !FunFinfun.fun_of_finE /= enum_valK tcastE /tnth /=.
  apply set_nth_default.
  by rewrite /= j_M ltn_ord.
transitivity (\rsum_(j0 : 'rV[A]_n) \rsum_(ji : 'rV[A]_n)
  ((P `^ n) j0) * ((P `^ n) ji) * (\rsum_( y | y \in
    [set y0 in 'rV[B]_n | prod_rV (ji , y0) \in `JTS P W n epsilon0])
  (W ``(| j0)) y))%R.
  set lhs := \rsum_(_ <- _) _.
  suff : lhs = 1%R by move=> ->; rewrite mul1R.
  rewrite /lhs {lhs}.
  rewrite (@big_cat_tuple_seq _ i.-1 (#|M| - i.+1)
    (fun x => \rprod_(i0 <- x) (P `^ n) i0))%R.
  by rewrite rsum_rmul_tuple_pmf.
transitivity (\rsum_(ji : 'rV[A]_n) ((P `^ n) ji) *
  (\rsum_(y | y \in [set y0 | prod_rV (ji , y0) \in `JTS P W n epsilon0])
  \rsum_(j0 : 'rV[A]_n) ((W ``(| j0) ) y) * ((P `^ n) j0)))%R.
  rewrite exchange_big /=.
  apply eq_bigr => ta _.
  transitivity (\rsum_(i1 : 'rV[A]_n) P `^ _ ta * P `^ _ i1 *
    (\rsum_(y in [set y0 | prod_rV (ta, y0) \in `JTS P W n epsilon0])
       W ``(y | i1)))%R.
    apply eq_bigr => i1 _.
    rewrite -!mulRA mulRC -!mulRA.
    f_equal.
    by rewrite mulRC.
  rewrite exchange_big /= big_distrr /=.
  apply eq_bigr => ta' _.
  rewrite -!mulRA.
  f_equal.
  by rewrite mulRC big_distrl.
transitivity (\rsum_(ji : 'rV[A]_n) ((P `^ n) ji) *
  \rsum_( y | y \in [set y0 | prod_rV (ji , y0) \in `JTS P W n epsilon0])
  ((`O(P , W)) `^ n) y)%R.
  apply eq_bigr => ta _.
  f_equal.
  apply eq_bigr => tb _.
  rewrite -tuple_pmf_out_dist.
  apply eq_bigr => i0 _; by rewrite DMCE.
transitivity (\rsum_(ji : 'rV[A]_n)
  (\rsum_( y | y \in
    [set y0 | prod_rV (ji , y0) \in `JTS P W n epsilon0])
    ((P `^ n) `x ((`O(P , W)) `^ n)) (ji, y))).
  apply eq_bigr => // i0 _; by rewrite /= big_distrr.
transitivity (\rsum_( jiy | prod_rV jiy \in `JTS P W n epsilon0)
  ((P `^ n) `x ((`O(P , W)) `^ n)) jiy).
  symmetry.
  rewrite pair_big_dep /=.
  apply eq_big => //.
  case=> ta tb; by rewrite !inE.
apply eq_bigl => tab; by rewrite !inE.
Qed.

Local Close Scope tuple_ext_scope.

Lemma preimC_Cal_E k n epsilon0 :
  let M := [finType of 'I_k.+1] in
  let PHI' := jtdec P W epsilon0 in
  let Cal_E := @cal_E M n epsilon0 in
  forall f : encT A M n,
    preimC (PHI' f) ord0 =i
    (~: Cal_E f ord0) :|: \bigcup_(m : M | m != ord0) Cal_E f m.
Proof.
move=> M PHI' Cal_E f tb.
rewrite 2!inE.
apply/idP/idP.
- rewrite /PHI' /jtdec ffunE.
  case: (pickP _) => [m2 Hm2 | Hm2].
  + move/eqP => m2m0.
    rewrite inE {1}/Cal_E {1}/cal_E 2!inE.
    apply/orP; left.
    case/andP : Hm2 => _.
    move/forallP/(_ ord0).
    rewrite /set_jtyp_seq inE.
    move/implyP => -> //.
    apply/eqP => ?; by subst m2.
  + move=> _.
    rewrite inE.
    move/negbT : {Hm2}(Hm2 ord0).
    rewrite negb_and.
    case/orP => Hm2.
    * rewrite {1}/Cal_E {1}/cal_E 2!inE.
      by apply/orP; left.
    * apply/orP; right.
      apply/negPn.
      move: Hm2; apply contra => Hm2.
      apply/forallP => m_.
      apply/implyP => m_m0.
      apply: contra Hm2 => Hm2.
      apply/bigcupP.
      exists m_ => //.
      rewrite !inE in Hm2.
      by rewrite /Cal_E !inE.
- rewrite inE ffunE.
  case: (pickP _) => [m2 Hm2 | Hm2 //].
  case/orP => Hy.
  + rewrite inE /cal_E inE in Hy.
    case/andP : Hm2 => Hm2 _.
    apply/eqP. case => ?; subst m2.
    by rewrite Hm2 in Hy.
  + apply/eqP. case => ?; subst m2.
    case/andP : Hm2 => _ /forallP Hm2.
    case/bigcupP : Hy => m [Hm m_tb].
    rewrite /cal_E inE inE in m_tb.
    move: {Hm2}(Hm2 m).
    by rewrite !inE m_tb Hm.
Qed.

Lemma random_coding_good_code epsilon : 0 <= epsilon ->
  forall (r : CodeRateType),
    forall epsilon0, epsilon0_condition r epsilon epsilon0 ->
    forall n, n_condition r epsilon0 n ->
  exists M : finType, (0 < #|M|)%nat /\ #|M| = Zabs_nat (Int_part (exp2 (INR n * r))) /\
  let Jtdec := jtdec P W epsilon0 in
  \rsum_(f : encT A M n) (Wght.d P f * echa(W , mkCode f (Jtdec f)))%R < epsilon.
Proof.
move=> Hepsilon r epsilon0 Hepsilon0 n Hn.
have [k Hk] : exists k, (log (INR k.+1) / INR n = r)%R.
  case: Hn => ? [? [Hn2 ?]].
  case/fp_nat : Hn2 => k Hn2.
  exists (Zabs_nat k).-1.
  rewrite prednK; last first.
    apply/ltP/INR_lt.
    rewrite INR_Zabs_nat.
      rewrite -Hn2; by apply exp2_pos.
    apply le_IZR.
    rewrite -Hn2; exact/ltRW/exp2_pos.
  apply Rmult_eq_reg_l with (INR n); last first.
    apply/not_0_INR/eqP; by rewrite -lt0n.
 rewrite mulRCA mulRV ?mulR1; last first.
    apply/not_0_INR/eqP; by rewrite -lt0n.
  rewrite -(log_exp2 (INR n * r)) Hn2 INR_Zabs_nat //.
  apply le_IZR.
  rewrite -Hn2; exact/ltRW/exp2_pos.
set M := [finType of 'I_k.+1].
exists [finType of 'I_k.+1].
split; first by rewrite /= card_ord.
split.
  have -> : (INR n * r)%R = log (INR k.+1).
    rewrite -Hk mulRCA mulRV ?mulR1 //.
    apply not_0_INR.
    by case: Hn => Hn _ ?; subst n.
  rewrite exp2_log; last exact/lt_0_INR/ltP.
  by rewrite Int_part_INR Zabs_nat_Z_of_nat card_ord.
move=> Jtdec.
rewrite /CodeErrRate.
rewrite [X in X < _](_ : _ = (1 / INR #|M| *
  \rsum_(f : encT A M n) Wght.d P f * (\rsum_(m in M) e(W, mkCode f (Jtdec f)) m))%R); last first.
  rewrite big_distrr /=.
  apply eq_bigr => f _.
  rewrite -!mulRA mulRC -!mulRA.
  do 2 f_equal.
  by rewrite mulRC.
rewrite [X in X < _](_ : _ = (\rsum_(f : encT A M n) Wght.d P f * (e(W, mkCode f (Jtdec f))) ord0)%R); last first.
  transitivity (1 / INR #|M| *
    \rsum_(f : encT A M n) (\rsum_(m in M) Wght.d P f * (e(W, mkCode f (Jtdec f))) m))%R.
    f_equal.
    apply eq_bigr => i _; by rewrite big_distrr.
  rewrite exchange_big /=.
  transitivity (1 / INR #|M| * \rsum_(f : encT A M n)
    (\rsum_( m_ in M ) Wght.d P f * (e(W, mkCode f (Jtdec f))) ord0))%R.
    congr (_ * _)%R.
    apply/esym.
    rewrite exchange_big /=.
    apply eq_bigr => m' _.
    apply error_rate_symmetry.
    by move: Hepsilon0; rewrite /epsilon0_condition; case => /ltRW.
  rewrite exchange_big /= big_const /= iter_Rplus !mulRA div1R mulVR ?mul1R //.
  apply not_0_INR; by rewrite card_ord.
set Cal_E := @cal_E M n epsilon0.
apply Rle_lt_trans with
(\rsum_(f : encT A M n) Wght.d P f * Pr (W ``(| f ord0)) (~: Cal_E f ord0) +
  \rsum_(i | i != ord0)
  \rsum_(f : encT A M n) Wght.d P f * Pr (W ``(| f ord0)) (Cal_E f i))%R.
  rewrite exchange_big /= -big_split /=.
  apply ler_rsum => /= i _.
  rewrite -big_distrr /= -mulRDr.
  apply Rmult_le_compat_l; first exact: (dist_nonneg (Wght.d P)).
  rewrite [X in X <= _](_ : _ = Pr (W ``(| i ord0))
    (~: Cal_E i ord0 :|: \bigcup_(i0 : M | i0 != ord0) Cal_E i i0)); last first.
    apply Pr_ext; apply/setP => tb /=.
    move: (preimC_Cal_E epsilon0 i tb); by rewrite inE.
  apply Rle_trans with (Pr (W ``(| i ord0)) (~: Cal_E i ord0) +
    Pr (W ``(| i ord0)) (\bigcup_(i0 | i0 != ord0) (Cal_E i i0)))%R.
    by apply Pr_union.
  by apply Rplus_le_compat_l, Pr_bigcup.
rewrite first_summand //.
set lhs := \rsum_(_ < _ | _) _.
have -> : lhs = (INR #| M |.-1 * Pr ((P `^ n) `x ((`O(P , W)) `^ n)) [set x | prod_rV x \in `JTS P W n epsilon0])%R.
  rewrite {}/lhs.
  rewrite [RHS](_ : _ = \rsum_(H0 < k.+1 | H0 != ord0)
    Pr ((P `^ n) `x ((`O( P , W )) `^ n)) [set x | prod_rV x \in `JTS P W n epsilon0])%R; last first.
    rewrite big_const /= iter_Rplus.
    do 2 f_equal.
    rewrite card_ord /=.
    transitivity (#| setT :\ (@ord0 k)|).
      move: (cardsD1 (@ord0 k) setT) => /=.
      rewrite !cardsT !card_ord inE /= add1n.
      case=> H1; by rewrite {1}H1.
    rewrite cardsE.
    apply eq_card => m_.
    by rewrite -!topredE /= !in_set andbC.
    apply eq_big => //; by apply: second_summand.
rewrite card_ord /=.
apply Rle_lt_trans with (epsilon0 + INR k *
   Pr P `^ n `x (`O(P , W)) `^ n [set x | prod_rV x \in `JTS P W n epsilon0])%R.
  apply Rplus_le_compat_r.
  rewrite Pr_of_cplt.
  have : forall a b, a >= 1 - b -> 1 - a <= b by move=> *; fourier.
  apply.
  apply JTS_1 => //.
  rewrite /epsilon0_condition in Hepsilon0; tauto.
  by case: Hn => _ [_ []].
apply Rle_lt_trans with (epsilon0 + INR #| M | * exp2 (- INR n * (`I( P ; W ) - 3 * epsilon0)))%R.
  apply Rplus_le_compat_l, Rmult_le_compat.
    rewrite (_ : 0 = INR 0)%R //. apply le_INR. by apply/leP.
    apply le_0_Pr. apply le_INR. apply/leP. by rewrite card_ord.
    by apply non_typical_sequences.
apply Rlt_trans with (epsilon0 + epsilon0)%R.
  apply Rplus_lt_compat_l.
  have -> : INR #| M | = exp2 (log (INR #| M |)).
    rewrite exp2_log // (_ : 0 = INR 0)%R //.
    apply lt_INR. rewrite card_ord. by apply/ltP.
  rewrite -exp2_plus.
  rewrite (_ : _ + _ = - INR n * (`I(P ; W) - log (INR #| M |) / INR n - 3 * epsilon0))%R; last first.
    field.
    apply not_0_INR => abs. case: Hn => Hn _; by rewrite abs in Hn.
  rewrite (_ : _ / _ = r)%R; last by rewrite -Hk card_ord.
  apply Rlt_trans with (exp2 (- INR n * epsilon0)).
    apply exp2_increasing.
    rewrite !mulNR.
    apply Ropp_lt_contravar, Rmult_lt_compat_l.
    - apply lt_0_INR; case: Hn => Hn _; by apply/ltP.
    - case: Hepsilon0 => _ [_ Hepsilon0].
      apply (Rmult_lt_compat_l 4) in Hepsilon0; last by fourier.
      rewrite mulRCA mulRV // mulR1 in Hepsilon0.
      clear Hk; fourier.
  apply Rlt_le_trans with (exp2 (- (- (log epsilon0) / epsilon0) * epsilon0)).
    apply exp2_increasing, Rmult_lt_compat_r.
    - rewrite /epsilon0_condition in Hepsilon0; tauto.
    - apply Ropp_lt_contravar; by case: Hn => _ [Hn2 _].
      rewrite -mulNR oppRK -mulRA -Rinv_l_sym; last first.
        apply nesym, Rlt_not_eq.
        rewrite /epsilon0_condition in Hepsilon0; tauto.
      rewrite mulR1 exp2_log; last by rewrite /epsilon0_condition in Hepsilon0; tauto.
      by apply Rle_refl.
case: Hepsilon0 => ? [? ?]; fourier.
Qed.

End random_coding_good_code_existence.

Section channel_coding_theorem.

Variables A B : finType.
Variable W : `Ch_1(A, B).
Variable cap : R.
Hypothesis Hc : capacity W cap.

(** * Channel Coding Theorem (direct part) *)

Theorem channel_coding (r : CodeRateType) : r < cap ->
  forall epsilon, 0 < epsilon ->
    exists n M (c : code A B M n), CodeRate c = r /\ echa(W, c) < epsilon.
Proof.
move=> r_I epsilon Hepsilon.
have [P HP] : exists P : dist A, r < `I(P ; W).
  case: Hc => H1 H2.
  apply NNPP => abs.
  have {abs}abs : forall P : dist A, r >= `I(P ; W).
    move/not_ex_all_not in abs.
    move=> P.
    by apply Rnot_lt_ge, abs.
  have Hcap : r >= cap.
    apply Rle_ge, H2 => P.
    by apply Rge_le, abs.
  fourier.
have [epsilon0 Hepsilon0] : exists epsilon0,
  0 < epsilon0 /\ epsilon0 < epsilon / 2 /\ epsilon0 < (`I(P ; W) - r) / 4.
  exists ((Rmin (epsilon/2) ((`I(P ; W) - r) / 4))/2).
  have Htmp : 0 < Rmin (epsilon / 2) (((`I(P ; W) - r) / 4)).
    apply Rmin_pos; apply mulR_gt0 => //; fourier.
  split.
    apply mulR_gt0 => //; fourier.
  split.
    apply Rlt_le_trans with (Rmin (epsilon / 2) ((`I(P ; W) - r) / 4)).
    by apply Rlt_eps2_eps.
    by apply Rmin_l.
    apply Rlt_le_trans with (Rmin (epsilon / 2) ((`I(P ; W) - r) / 4)).
    by apply Rlt_eps2_eps.
    by apply Rmin_r.
have [n Hn] : exists n, n_condition W P r epsilon0 n.
  destruct r as [r [num [den [Hnum [Hden Hr]]]]].
  have Hn : exists n, (0 < n)%nat /\
    - log epsilon0 / epsilon0 < INR n /\
    (maxn (Zabs_nat (up (aep_bound P (epsilon0 / 3))))
    (maxn (Zabs_nat (up (aep_bound (`O(P , W)) (epsilon0 / 3))))
          (Zabs_nat (up (aep_bound (`J(P , W)) (epsilon0 / 3))))) <= n)%nat.
    set supermax := maxn 1
      (maxn (Zabs_nat (up (- log epsilon0 / epsilon0)))
      (maxn (Zabs_nat (up (aep_bound P (epsilon0 / 3))))
      (maxn (Zabs_nat (up (aep_bound (`O(P , W)) (epsilon0 / 3))))
            (Zabs_nat (up (aep_bound (`J(P , W)) (epsilon0 / 3))))))).
    exists supermax.
    split; first by rewrite leq_max.
    split.
      apply Rlt_le_trans with (IZR (up (- log epsilon0 / epsilon0))).
        rewrite up_Int_part.
        case: (base_Int_part (- log epsilon0 / epsilon0)) => H1 H2.
        rewrite plus_IZR //.
        move: H2.
        set eps := - log epsilon0 / epsilon0.
        move=> ?; fourier.
      apply Rle_trans with (INR (Zabs_nat (up (- log epsilon0 / epsilon0)))).
        case: (Z_lt_le_dec (up (- log epsilon0 / epsilon0)) 0) => H1.
          apply Rle_trans with 0.
            by apply IZR_le, Zlt_le_weak.
          by apply pos_INR.
        rewrite INR_Zabs_nat //; by apply Rle_refl.
      apply le_INR.
      rewrite /supermax maxnA.
      apply/leP.
      rewrite leq_max.
      apply/orP; left; by rewrite leq_max leqnn orbC.
    by rewrite [X in (_ <= X)%nat]maxnA leq_maxr.
  lapply (exists_frac_part Hn Hnum Hden); last move=> n1 n2 n1_n2 Pn1.
    case=> n [[Hn1 [Hn3 Hn4]] Hn2].
    exists n => /=.
    rewrite /n_condition.
    intuition.
    congruence.
  split.
    apply/ltP.
    apply lt_le_trans with n1; [apply/ltP; tauto | by apply/leP].
  split.
    apply Rlt_le_trans with (INR n1); [tauto | exact/le_INR/leP].
  apply leq_trans with n1 => //; tauto.
case: (random_coding_good_code (ltRW _ _ Hepsilon) Hepsilon0 Hn) =>
  M [HM [M_k H]].
case: (good_code_sufficient_condition HM H) => f Hf.
exists n, M, (mkCode f (jtdec P W epsilon0 f)); split; last assumption.
rewrite /CodeRate M_k INR_Zabs_nat; last by apply Int_part_pos, ltRW, exp2_pos.
suff Htmp : IZR (Int_part (exp2 (INR n * r))) = exp2 (INR n * r).
  rewrite Htmp log_exp2 /Rdiv -mulRA mulRCA mulRV ?mulR1 //.
  apply not_0_INR => abs; case: Hn => Hn _; by rewrite abs in Hn.
  apply frac_Int_part; by case: Hn => _ [_ []].
Qed.

End channel_coding_theorem.
