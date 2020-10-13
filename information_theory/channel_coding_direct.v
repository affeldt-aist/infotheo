(* infotheo: information theory and error-correcting codes in Coq               *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later              *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg matrix perm.
Require Import Reals Lra Classical.
Require Import ssrZ ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop.
Require Import fdist proba entropy aep typ_seq joint_typ_seq channel.
Require Import channel_code.

(******************************************************************************)
(*                 Channel coding theorem (direct part)                       *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   jtdec == joint typicality decoding                                       *)
(*   cal_E M n epsilong f == the set of output vb such that (f m, vb) is      *)
(*                           jointly typical                                  *)
(*                                                                            *)
(* Theorem:                                                                   *)
(*   channel_coding == channel coding theorem (direct part)                   *)
(*                                                                            *)
(* For details, see Reynald Affeldt, Manabu Hagiwara, and Jonas Sénizergues.  *)
(* Formalization of Shannon's theorems. Journal of Automated Reasoning,       *)
(* 53(1):63--103, 2014                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.
Local Open Scope proba_scope.
Local Open Scope jtyp_seq_scope.
Local Open Scope channel_code_scope.
Local Open Scope channel_scope.
Local Open Scope vec_ext_scope.

Module Wght.
Section wght.
Variables (A M : finType) (P : fdist A) (n : nat).
Definition f := [ffun g : encT A M n => \prod_(m in M) P `^ n (g m)].
Lemma f0 g : 0 <= f g. Proof. rewrite ffunE; exact: prodR_ge0. Qed.
Lemma f1 : \sum_(g in {ffun M -> 'rV[A]_n}) f g = 1.
Proof.
rewrite /f; evar (h : {ffun M -> 'rV[A]_n} -> R); rewrite (eq_bigr h); last first.
  move=> a _; rewrite ffunE /h; reflexivity.
rewrite {}/h -(bigA_distr_bigA (fun _ v => P `^ n v)) /=.
rewrite [RHS](_ : _ = \prod_(m0 : M | xpredT m0) 1); last by rewrite big1.
apply eq_bigr => _ _; by rewrite (FDist.f1 (P `^ n)).
Qed.
Definition d : {fdist encT A M n} := locked (FDist.make f0 f1).
Lemma dE x : d x = f x. Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
End wght.
End Wght.

Arguments Wght.d {A} {M} _ {n}.

Section joint_typicality_decoding.

Variables A B M : finType.
Variable n : nat.

Definition jtdec P W epsilon (f : encT A M n) : decT B M n :=
  [ffun tb => [pick m |
    (prod_rV (f m, tb) \in `JTS P W n epsilon) &&
    [forall m', (m' != m) ==> (prod_rV (f m', tb) \notin `JTS P W n epsilon)]]].

Lemma jtdec_map epsilon (P : fdist A) (W : `Ch(A, B)) (f : encT A M n) tb m0 m1 :
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
  \sum_(f : encT A M n) (Wght.d P f * echa(W , mkCode f (phi f))) < epsilon ->
  exists f, echa(W , mkCode f (phi f)) < epsilon.
Proof.
move=> H.
apply not_all_not_ex => abs.
set x := \sum_(f <- _) _ in H.
have : \sum_(f : encT A M n) Wght.d P f * epsilon <= x.
  rewrite /x; apply leR_sumRl => //= f _.
  - by apply leR_wpmul2l => //; exact/Rnot_lt_le/abs.
  - by apply mulR_ge0 => //; exact/echa_ge0.
apply/Rlt_not_le/(@ltR_leR_trans epsilon) => //.
by rewrite -big_distrl /= (FDist.f1 (Wght.d P)) mul1R; exact/leRR.
Qed.

Definition o_PI (m m' : M) := fun g : encT A M n => [ffun x => g (tperm m m' x)].

Lemma o_PI_2 (g : encT A M n) (m m' m_ : M) : (o_PI m m' (o_PI m m' g)) m_ = g m_.
Proof. by rewrite /o_PI !ffunE tpermK. Qed.

Lemma wght_o_PI m m' P (h : encT A M n) : Wght.d P (o_PI m m' h) = Wght.d P h.
Proof.
rewrite 2!Wght.dE /Wght.f 2!ffunE
  (reindex_onto (tperm m m') (tperm m m')) /=; last first.
  move=> m0 _; by rewrite tpermK.
apply eq_big => m0.
- by rewrite tpermK eqxx.
- by move=> _; rewrite /o_PI ffunE tpermK.
Qed.

Lemma error_rate_symmetry (P : {fdist A}) (W : `Ch(A, B)) epsilon :
  0 <= epsilon -> let Jtdec := jtdec P W epsilon in
    forall m m',
      \sum_(f : encT A M n) (Wght.d P f * e(W, mkCode f (Jtdec f)) m) =
      \sum_(f : encT A M n) (Wght.d P f * e(W, mkCode f (Jtdec f)) m').
Proof.
move=> Hepsilon PHI' m m'.
set lhs := \sum_(_ <- _) _.
have Hlhs : lhs = \sum_(f : encT A M n) (Wght.d P f * e(W, mkCode f (PHI' f)) m) by [].
have Hlhs2 : lhs = \sum_(f : encT A M n)
  (Wght.d P (o_PI m m' f) * e(W, mkCode (o_PI m m' f) (PHI' (o_PI m m' f))) m).
  rewrite Hlhs (reindex_onto (o_PI m m') (o_PI m m')) /=; last first.
    move=> i _; apply/ffunP => m_; by rewrite o_PI_2.
  apply eq_bigl => x /=.
  apply/eqP/ffunP => y; exact: o_PI_2.
rewrite Hlhs2.
apply eq_bigr => g _.
rewrite wght_o_PI; congr (_ * _).
rewrite /ErrRateCond /= (_ : (o_PI m m' g) m = g m'); last by rewrite ffunE tpermL.
congr Pr; apply/setP => tb /=.
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
    * exfalso.
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
      have {}Hm0 : (prod_rV ((o_PI m m' g) m, tb) \in `JTS P W n epsilon) &&
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
      exact: (jtdec_map Hm1 Hm0).
    * exfalso.
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

(* TODO: move? *)
Section sum_rV_ffun.

Import Monoid.Theory.

Variable R : Type.
Variable times : Monoid.mul_law 0.
Local Notation "*%M" := times (at level 0).
Variable plus : Monoid.add_law 0 *%M.
Local Notation "+%M" := plus (at level 0).

Lemma sum_rV_ffun (I J : finType) (F : {ffun I -> J} -> R)
  (G : _ -> _ -> _) (idef : I) (zero : 'I_ _) : O = zero ->
  \big[+%M/0]_(j : 'rV[J]_#|I|) G (F [ffun x => j ord0 (enum_rank x)]) (j ord0 zero) =
  \big[+%M/0]_(f : {ffun I -> J}) G (F f) (f (nth idef (enum I) 0)).
Proof.
Local Open Scope ring_scope.
move=> Hzero.
rewrite (reindex_onto (fun y : {ffun _ -> J} => \row_(i < _) y (enum_val i))
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
apply/rowP => a; by rewrite mxE ffunE enum_valK.
Qed.

End sum_rV_ffun.

Section random_coding_good_code_existence.

Variables (B A : finType) (W : `Ch(A, B)) (P : fdist A).

Definition epsilon0_condition r epsilon epsilon0 :=
  0 < epsilon0 /\ epsilon0 < epsilon / 2 /\ epsilon0 < (`I(P, W) - r) / 4.

Definition n_condition r epsilon0 n :=
  (O < n)%nat /\ - log epsilon0 / epsilon0 < INR n /\
  frac_part (exp2 (INR n * r)) = 0 /\ (JTS_1_bound P W epsilon0 <= n)%nat.

Definition cal_E M n epsilon (f : encT A M n) m :=
  [set vb | prod_rV (f m, vb) \in `JTS P W n epsilon].

Local Open Scope tuple_ext_scope.

(* TODO: move? *) (* NB: similar to big_rV_cons_behead *)
Lemma big_tuple_cons_behead {C : finType} n (F : n.+1.-tuple C -> R)
  (P1 : pred C) (P2 : pred {: n.-tuple C}) :
  \sum_(i in C | P1 i) \sum_(j in {: n.-tuple C} | P2 j) (F [tuple of (i :: j)])
  =
  \sum_(p in {: n.+1.-tuple C} | (P1 (thead p)) && (P2 (tbehead p)) ) (F p).
Proof.
apply/esym.
rewrite (@partition_big _ _ _ _ _ _ (fun x => thead x) (fun x => P1 x)) //=; last first.
  move=> t; by case/andP.
apply eq_bigr => i Hi.
rewrite (reindex_onto (fun j : {: n.-tuple C} => [tuple of (i :: j)])
  (fun p => [tuple of (behead p)])) /=; last first.
  move=> j /andP[Hj1 /eqP <-]; exact/esym/tuple_eta.
apply congr_big => // x /=.
rewrite !theadE eqxx /= Hi /= -andbA /=.
rewrite (_ : _ == x = true) ?andbT; last first.
  rewrite tupleE /behead_tuple /=; exact/eqP/val_inj.
congr P2; rewrite /tbehead tupleE /behead_tuple; exact: val_inj.
Qed.

(* TODO: move? *)
Lemma rsum_rmul_tuple_pmf_tnth {C : finType} n k (Q : fdist C) :
  \sum_(t : {:k.-tuple ('rV[C]_n)}) \prod_(m < k) (Q `^ n) t \_ m = 1%R.
Proof.
transitivity (\sum_(j : {ffun 'I_k -> 'rV[_]_n}) \prod_(m < k) Q `^ _ (j m)).
  rewrite (reindex_onto (fun p => [ffun x => p\_(enum_rank x)])
                        (fun x => fgraph x)) //=; last first.
    by move=> f _; apply/ffunP => /= i; rewrite ffunE tnth_fgraph enum_rankK.
  rewrite (big_tcast (esym (card_ord k))) esymK.
  apply eq_big => //.
  - move=> i /=; apply/esym/eqP/eq_from_tnth => j.
    by rewrite tnth_fgraph ffunE enum_valK.
  - by move=> i _; apply eq_bigr => j _; rewrite ffunE /= tcastE -enum_rank_ord.
rewrite -(bigA_distr_bigA (fun m xn => Q `^ _ xn)) /= big_const.
by rewrite FDist.f1 iter_mulR exp1R.
Qed.

(* TODO: move? *)
Lemma rsum_rmul_tuple_pmf {C} n k (Q : fdist C) :
  (\sum_(t in {:k.-tuple ('rV[C]_n)}) \prod_(x <- t) (Q `^ n) x = 1)%R.
Proof.
rewrite -[X in _ = X](rsum_rmul_tuple_pmf_tnth n k Q).
apply eq_bigr => t _.
rewrite big_tnth /= (reindex_onto (cast_ord (size_tuple t))
  (cast_ord (esym (size_tuple t)))) //=; last first.
  move=> i _; exact/val_inj.
apply eq_big => //= i.
- by rewrite cast_ordK eqxx.
- move=> _; by rewrite tvalK tcastE esymK.
Qed.

Local Open Scope ring_scope.

Lemma first_summand k n epsilon0 :
  let M := [finType of 'I_k.+1] in
  (\sum_(f : encT A M n) Wght.d P f *
    Pr (W ``(| f ord0)) (~: cal_E epsilon0 f ord0))%R =
  Pr (`J(P , W) `^ n) (~: `JTS P W n epsilon0).
Proof.
move=> M.
have M_prednK : #|M|.-1.+1 = #|M| by rewrite card_ord.
pose E_F_N := @cal_E M n epsilon0.
rewrite {1}/cal_E.
case/card_gt0P : (fdist_card_neq0 P) => a _.
pose zero := @enum_rank M ord0.
have : 0%N = zero :> nat by rewrite /zero enum_rank_ord.
move/(@sum_rV_ffun _ _ _ _ _ (Wght.d P)
  (fun r v => r * Pr (W ``(| v )) (~: [set w | prod_rV (v, w) \in `JTS P W n epsilon0]))%R
  ord0 zero).
rewrite (_ : nth ord0 (enum M) 0 = ord0); last by rewrite enum_ordS.
move=> <- /=.
transitivity (\sum_(v : 'rV['rV[A]_n]_#|M|) (
    (\prod_(m : M) P `^ n ([ffun x => v ``_ x] (enum_rank m))) *
    \sum_(w | w \in ~: cal_E epsilon0 [ffun x => v ``_ x] zero)
    (W ``(| [ffun x => v ``_ x] zero)) w))%R.
  apply eq_bigr => v _; congr (_ * _)%R.
    rewrite Wght.dE ffunE. (* NB *)
    by apply eq_bigr => m _; rewrite 2!ffunE.
  apply eq_big.
  - move=> /= ?; by rewrite !inE ffunE.
  - move=> ? _; by rewrite ffunE.
rewrite /cal_E.
transitivity (\sum_(v : 'rV[A]_n)
  (\sum_(y in ~: [set w | prod_rV (v, w) \in `JTS P W n epsilon0])
  (W ``(| v)) y) *
    \sum_(j in {: #|M|.-1.-tuple ('rV[A]_n)})
      (\prod_(m : M) P `^ _ ((tcast M_prednK [tuple of v :: j]) \_ (enum_rank m))))%R.
  rewrite (reindex_onto (fun y : {ffun _ -> 'rV__} => \row_(i < _) y (enum_val i))
      (fun p : 'rV_ _ => [ffun x => p ``_ (enum_rank x)])) //=; last first.
    move=> v _; by apply/rowP => i; rewrite mxE ffunE enum_valK.
  apply trans_eq with (\sum_(f : {ffun M -> 'rV__})
    ((\prod_(m < k.+1) P `^ n (f m)) *
      \sum_(y in ~: [set y0 | prod_rV (f ord0, y0) \in `JTS P W n epsilon0])
      W ``(y | f ord0)))%R.
    apply eq_big => //= f.
    - apply/eqP/ffunP => m; by rewrite ffunE mxE enum_rankK.
    - move/eqP => Hf;  congr (_ * _)%R.
        apply eq_bigr => i _; by rewrite -[in RHS]Hf 2!ffunE.
      apply eq_big => /=.
        move=> ?; by rewrite !inE -[in RHS]Hf !ffunE mxE.
      move=> ? _; by rewrite -[in RHS]Hf !ffunE mxE.
  rewrite (_ : ord0 = nth ord0 (enum M) 0); last by rewrite enum_ordS.
  rewrite -(big_tuple_ffun _ (fun f => \prod_(m : M) P `^ n (f m))
    (fun r => fun yn => r *
      (\sum_(y in ~: [set y0 | prod_rV (yn, y0) \in `JTS P W n epsilon0])
      W ``(y | yn))) (\row_(i < n) a) ord0)%R.
  transitivity (\sum_(j : _)
    (\prod_(m : M) P `^ n ((tcast M_prednK j) \_ (enum_rank m))) *
      (\sum_(y in ~: [set y0 | prod_rV (nth (\row_(i < n) a) j 0, y0) \in
          `JTS P W n epsilon0])
      W ``(y | nth (\row_(i < n) a) j 0)))%R.
    rewrite (big_tcast (esym M_prednK)) esymK.
    apply eq_bigr => i _; congr (_ * _)%R.
      apply eq_bigr => m _; by rewrite ffunE.
    have H : nth (\row_(i < n) a) (tcast M_prednK i) 0 = nth (\row_(i < n) a) i 0.
      move: M_prednK i; rewrite card_ord => M_prednK i.
      rewrite -(tnth_nth _ i ord0) -(tnth_nth _ (tcast M_prednK i) ord0).
      by rewrite tcastE /= cast_ord_id.
    apply eq_big => m; by rewrite !inE H.
  rewrite -(@big_tuple_cons_behead _ #|M|.-1
   (fun j => ((\prod_(m : M) P `^ n ((tcast M_prednK j) \_ (enum_rank m))) *
     (\sum_(y in ~: [set y0 | prod_rV (nth (\row_(i < n) a) j 0, y0) \in
         `JTS P W n epsilon0]) W ``(y | nth (\row_(i < n) a) j 0)))) xpredT xpredT)%R.
  apply eq_bigr => ta _ /=; by rewrite -big_distrl /= mulRC.
transitivity ((\sum_(ta in 'rV[A]_n) P `^ _ ta *
    (\sum_(y in ~: [set y0 | prod_rV (ta, y0) \in `JTS P W n epsilon0])
    (W ``(| ta ) ) y)) *
    \sum_(j in {:k.-tuple ('rV[A]_n)}) \prod_(m < k) (P `^ _ (j \_ m)))%R.
  rewrite big_distrl /=.
  apply eq_bigr => ta _.
  rewrite -mulRA mulRCA; congr Rmult.
  transitivity (\sum_(j in {: #|'I_k|.-tuple ('rV[A]_n) })
    P `^ _ ta * \prod_(m < k) P `^ _ (j \_ (enum_rank m)))%R.
    have k_prednK : #|'I_k.+1|.-1 = #|'I_k| by rewrite !card_ord.
    rewrite (big_tcast (esym k_prednK)) esymK.
    apply eq_bigr => i0 Hi0.
    rewrite big_ord_recl /=.
    congr (P `^ _ _ * _)%R; first by rewrite tcastE // enum_rank_ord.
    apply eq_bigr => i1 _; congr (P `^ _ _).
    rewrite !tcastE {1}/tnth /=.
    rewrite (_ : enum_rank _ = (enum_rank i1).+1 :> nat) /=; last by rewrite !enum_rank_ord.
    apply set_nth_default; by rewrite size_tuple /= enum_rank_ord /= card_ord.
  rewrite -big_distrr /=; congr (_ * _)%R.
  rewrite (big_tcast (esym (card_ord k))) esymK.
  apply eq_bigr => /= i0 _.
  apply eq_bigr => /= i1 _.
  by rewrite tcastE -enum_rank_ord.
rewrite rsum_rmul_tuple_pmf_tnth mulR1.
transitivity (\sum_(v in 'rV[A]_n)
  \sum_(y in ~: [set w | prod_rV (v, w) \in `JTS P W n epsilon0])
    (`J(P , W) `^ n (prod_rV (v, y))))%R.
  apply eq_bigr => /= v _.
  rewrite big_distrr /=.
  apply eq_bigr => // w _.
  rewrite DMCE 2!TupleFDist.dE -big_split /=.
  apply eq_bigr => /= i _.
  by rewrite JointFDistChan.dE -fst_tnth_prod_rV -snd_tnth_prod_rV /= mulRC.
rewrite /Pr big_rV_prod pair_big_dep /=.
apply eq_bigl; case=> /= ? ?; by rewrite !inE.
Qed.

(* TODO: move? *)
Lemma big_cat_tuple {C : finType} m n (F : (m + n)%nat.-tuple C -> R) :
  (\sum_(i in {:m.-tuple C}) \sum_(j in {: n.-tuple C})
  F [tuple of (i ++ j)] = \sum_(p in {: (m + n)%nat.-tuple C}) (F p))%R.
Proof.
elim: m n F => [m2 F /=|m IH n F].
- transitivity (\sum_(i <- [tuple] :: [::])
    \sum_(j in {: m2.-tuple C}) F [tuple of i ++ j] )%R.
    apply congr_big => //=.
    apply (@eq_from_nth _ [tuple]);
      rewrite /index_enum -enumT /= (eqP (enum_tupleP _)) card_tuple expn0 //.
    move=> i; rewrite ltnS leqn0 => /eqP ->.
    rewrite tupleE /=.
    case: (enum _) => //= t.
    by rewrite (tuple0 t).
  rewrite big_cons /= big_nil /= addR0.
  apply eq_bigr => // i _; congr F.
  exact/val_inj.
- symmetry.
  transitivity (\sum_(p in tuple_finType (m + n).+1 C) F p)%R; first by apply congr_big.
  rewrite -(@big_tuple_cons_behead _ _ _ xpredT xpredT).
  rewrite -(@big_tuple_cons_behead _ _ _ xpredT xpredT).
  apply eq_bigr => i _.
  move: {IH}(IH n (fun x => F [tuple of i :: x])) => <-.
  apply eq_bigr => /= t _; apply eq_bigr => /= t' _; congr F.
  exact/val_inj.
Qed.

(* TODO: move? *)
Lemma big_cat_tuple_seq {C : finType} m n (F : seq C -> R) :
  (\sum_(i in {:m.-tuple C} ) \sum_(j in {: n.-tuple C}) (F (i ++ j)) =
  \sum_(p in {: (m + n)%nat.-tuple C}) (F p))%R.
Proof.
move: (@big_cat_tuple _ m n (fun l => if size l == (m + n)%nat then F l else R0)).
set lhs := (\sum_(i in _) _)%R => H.
apply trans_eq with lhs.
  apply eq_bigr => /= t _; apply eq_bigr => /= t' _.
  case: ifP => //; by rewrite size_tuple eqxx.
rewrite H; apply eq_bigr => /= t _; by rewrite size_tuple eqxx.
Qed.

Lemma second_summand n k epsilon0 :
  let M := [finType of 'I_k.+1] in
    forall i, i != ord0 ->
      (\sum_(f : encT A M n) Wght.d P f *
        Pr (W ``(| f ord0)) (cal_E epsilon0 f i))%R =
   Pr ((P `^ n) `x `O( P , W ) `^ n) [set x | prod_rV x \in `JTS P W n epsilon0].
Proof.
move=> M.
have M_prednK : #|M|.-1.+1 = #|M| by rewrite card_ord.
move=> i i_m0.
set E_F_N := @cal_E M n epsilon0.
have Hcast : (i.-1 + (#|M| - i.+1).+1).+1 = #|M|.
  rewrite /M card_ord subSS addnS -addSn prednK; last by rewrite lt0n.
  by rewrite subnKC // -ltnS ltn_ord.
transitivity (
  \sum_(j1 in {: i.-1.-tuple ('rV[A]_n)})
  \sum_(j2 in {: (#|M| - i.+1).-tuple ('rV[A]_n)})
  \sum_(j0 in 'rV[A]_n)
  \sum_(ji in 'rV[A]_n)
  Wght.d P [ffun x => (tcast Hcast [tuple of j0 :: j1 ++ ji :: j2])\_x] *
  \sum_(y | y \in [set w | prod_rV (ji, w) \in `JTS P W n epsilon0])
  (W ``(| j0)) y)%R.
  transitivity (
    \sum_(j0 in 'rV[A]_n)
    \sum_(j1 in {: i.-1.-tuple ('rV[A]_n)})
    \sum_(ji in 'rV[A]_n)
    \sum_(j2 in {: (#|M| - i.+1).-tuple ('rV[A]_n)})
    Wght.d P [ffun x => (tcast Hcast [tuple of j0 :: j1 ++ ji :: j2])\_x] *
    \sum_( y | y \in [set w | prod_rV (ji, w) \in `JTS P W n epsilon0])
    (W ``(| j0) ) y)%R.
    rewrite (reindex_onto (fun p => [ffun x => p\_(enum_rank x)]) (fun y => fgraph y)) /=; last first.
      move=> f _; apply/ffunP => m; by rewrite ffunE tnth_fgraph enum_rankK.
    transitivity ( \sum_(j : _)
      (Wght.d P [ffun x => j\_(enum_rank x)] *
        Pr (W ``(| [ffun x => j\_(enum_rank x)] ord0)) (E_F_N [ffun x => j\_(enum_rank x)] i)))%R.
      apply eq_big => //= x; apply/eqP/eq_from_tnth => j.
      by rewrite tnth_fgraph ffunE enum_valK.
    rewrite (big_tcast (card_ord k.+1)).
    rewrite -(big_tuple_cons_behead _ xpredT xpredT).
    apply eq_bigr => i0 _.
    have [Hq i_q] : (i.-1 + (k - i.-1) = k /\ i <= k)%nat.
      split.
        by rewrite subnKC // -(leq_add2r 1) !addn1 (leq_ltn_trans _ (ltn_ord i)) // leq_pred.
      by rewrite -(leq_add2r 1) !addn1 ltn_ord.
    rewrite (big_tcast (esym Hq)) esymK.
    rewrite -big_cat_tuple /=.
    apply eq_bigr => /= i1 _.
    have Hs : (k - i.-1 = (k - i).+1)%nat.
      by rewrite -subn1 subnBA ?lt0n // addnC -addnBA.
    rewrite (big_tcast Hs) -(big_tuple_cons_behead _ xpredT xpredT).
    apply eq_bigr => i2 _.
    have Ht : (#|'I_k.+1| - i.+1 = k - i)%nat by rewrite card_ord /= subSS.
    rewrite (big_tcast Ht) //; apply eq_bigr => /= i3 _; congr (_ * _)%R.
    - rewrite 2!Wght.dE /Wght.f 2!ffunE /=.
      rewrite (reindex_onto enum_rank enum_val); last by move=> *; rewrite enum_valK.
      apply eq_big => /=; first by move=> x; rewrite enum_rankK eqxx inE.
      move=> i4 _; congr (P `^ _ _).
      rewrite !ffunE; congr (_ \_ _).
      apply: eq_tcast => /=.
      apply/esym/eq_tcast2 => /=; congr (_ :: _).
      apply: eq_tcast2 => /=; congr (_ ++ _).
      apply: eq_tcast2 => /=; congr (_ :: _).
      exact/esym/eq_tcast2.
    - apply eq_big.
      + move=> x /=.
        rewrite !inE ffunE.
        rewrite (_ : (_ \_ _) = i2) //=.
        rewrite enum_rank_ord /= tcastE !cast_ord_comp (tnth_nth i0) /=.
        rewrite (_ : tval (tcast Hq _) = i1 ++ i2 :: i3); last first.
          apply/esym/eq_tcast2 => /=; congr cat; exact/eq_tcast2.
        by rewrite -cat_cons nth_cat /= size_tuple prednK ?lt0n // ltnn subnn.
      + move=> i4 Hi4.
        rewrite 2!DMCE.
        apply eq_bigr => i5 /= _; congr (W _ _).
        by rewrite ffunE tcastE /= enum_rank_ord /= cast_ordK.
  rewrite exchange_big /=.
  apply eq_bigr => /= i1 _.
  rewrite [in RHS]exchange_big /=.
  apply eq_bigr => /= i2 _.
  rewrite [in RHS]exchange_big /=.
  by apply eq_bigr.
transitivity (
  (\sum_(j1 in {: i.-1.-tuple ('rV[A]_n)})
   \sum_(j2 in {: (#|M| - i.+1).-tuple ('rV[A]_n)})
   \prod_(i <- j1 ++ j2) (P `^ n) i) *
  (\sum_(j0 in 'rV[A]_n)
    \sum_(ji in 'rV[A]_n)
    ((P `^ n) j0) * ((P `^ n) ji) *
    (\sum_( y | y \in
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
  rewrite !mulRA Wght.dE /Wght.f /=; congr (_ * _)%R.
  transitivity (\prod_( i <- j0 :: j1 ++ j3 :: j2) P `^ _ i)%R; last first.
    rewrite big_cons -mulRA mulRCA; congr (_ * _)%R.
    rewrite big_cat /= big_cons [in RHS]mulRC mulRCA; congr (_ * _)%R.
    by rewrite big_cat /= mulRC.
  rewrite [in RHS](big_nth j0) /= big_mkord.
  transitivity (\prod_(j < #|@predT M|)
    P `^ _ ([ffun x => (tcast Hcast [tuple of j0 :: j1 ++ j3 :: j2])\_(enum_rank x)] (enum_val j)))%R.
    rewrite ffunE; apply eq_big => ? //= _.
    by rewrite !ffunE enum_valK.
  have j_M : (size (j1 ++ j3 :: j2)).+1 = #|M|.
    rewrite size_cat (size_tuple j1) /= (size_tuple j2) card_ord.
    by rewrite -[RHS](card_ord k.+1) -Hcast card_ord.
  rewrite j_M.
  apply eq_bigr => i0 _; congr (P `^ n _).
  rewrite ffunE /= enum_valK tcastE /tnth /=.
  apply set_nth_default; by rewrite /= j_M ltn_ord.
transitivity (\sum_(j0 : 'rV[A]_n) \sum_(ji : 'rV[A]_n)
  ((P `^ n) j0) * ((P `^ n) ji) * (\sum_( y | y \in
    [set y0 in 'rV[B]_n | prod_rV (ji , y0) \in `JTS P W n epsilon0])
  (W ``(| j0)) y))%R.
  set lhs := (\sum_(_ <- _) _)%R.
  suff : lhs = 1%R by move=> ->; rewrite mul1R.
  rewrite /lhs {lhs}.
  rewrite (@big_cat_tuple_seq _ i.-1 (#|M| - i.+1) (fun x => \prod_(i0 <- x) (P `^ n) i0))%R.
  by rewrite rsum_rmul_tuple_pmf.
transitivity (\sum_(ji : 'rV[A]_n) ((P `^ n) ji) *
  (\sum_(y | y \in [set y0 | prod_rV (ji , y0) \in `JTS P W n epsilon0])
  \sum_(j0 : 'rV[A]_n) ((W ``(| j0) ) y) * ((P `^ n) j0)))%R.
  rewrite exchange_big /=.
  apply eq_bigr => ta _.
  transitivity (\sum_(i1 : 'rV[A]_n) P `^ _ ta * P `^ _ i1 *
    (\sum_(y in [set y0 | prod_rV (ta, y0) \in `JTS P W n epsilon0])
       W ``(y | i1)))%R.
    apply eq_bigr => i1 _.
    by rewrite -mulRA mulRCA mulRA.
  rewrite exchange_big /= big_distrr /=.
  apply eq_bigr => ta' _.
  rewrite -[in X in _ = (_ * X)%R]big_distrl /= -mulRA; congr Rmult.
  by rewrite mulRC.
transitivity (\sum_(ji : 'rV[A]_n) ((P `^ n) ji) *
  \sum_( y | y \in [set y0 | prod_rV (ji , y0) \in `JTS P W n epsilon0])
  ((`O(P , W)) `^ n) y)%R.
  apply eq_bigr => ta _; congr (_ * _)%R.
  apply eq_bigr => /= tb _.
  rewrite -tuple_pmf_out_fdist.
  apply eq_bigr => i0 _; by rewrite DMCE.
transitivity (\sum_(v : 'rV[A]_n)
  (\sum_(y | y \in
    [set y0 | prod_rV (v , y0) \in `JTS P W n epsilon0])
    ((P `^ n) `x ((`O(P , W)) `^ n)) (v, y)))%R.
  apply eq_bigr => // v _.
  rewrite big_distrr /=; apply eq_bigr => w _; by rewrite ProdFDist.dE.
transitivity (\sum_( jiy | prod_rV jiy \in `JTS P W n epsilon0)
  ((P `^ n) `x ((`O(P , W)) `^ n)) jiy)%R.
  rewrite [in LHS]pair_big_dep /=.
  by apply eq_big => -[? ?] /=; rewrite !inE ?ProdFDist.dE.
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
    rewrite in_setU in_setC {1}/Cal_E {1}/cal_E inE; apply/orP; left.
    case/andP : Hm2 => _ /forallP/(_ ord0)/implyP; apply.
    by move/eqP in m2m0; apply: contra m2m0 => /eqP <-.
  + move=> _.
    rewrite in_setU.
    move/negbT : {Hm2}(Hm2 ord0).
    rewrite negb_and.
    case/orP => Hm2.
    * by rewrite in_setC {1}/Cal_E {1}/cal_E inE Hm2.
    * apply/orP; right.
      apply/negPn.
      move: Hm2; apply contra => Hm2.
      apply/forallP => m_; apply/implyP => m_m0.
      apply: contra Hm2 => Hm2.
      apply/bigcupP; exists m_ => //; by rewrite /Cal_E /cal_E inE.
- rewrite in_setU ffunE.
  case: (pickP _) => [m2 Hm2|//].
  case/orP.
  + rewrite in_setC /cal_E inE => Hy.
    apply/eqP => -[m20].
    by case/andP : Hm2; rewrite m20 (negbTE Hy).
  + case/bigcupP => m Hm; rewrite /cal_E 2!inE => m_tb.
    apply/eqP => -[m20].
    case/andP : Hm2 => _ /forallP /(_ m); by rewrite !inE m_tb m20 Hm implyTb.
Qed.

Local Open Scope zarith_ext_scope.

Lemma random_coding_good_code epsilon : 0 <= epsilon ->
  forall (r : CodeRateType),
    forall epsilon0, epsilon0_condition r epsilon epsilon0 ->
    forall n, n_condition r epsilon0 n ->
  exists M : finType, (0 < #|M|)%nat /\ #|M| = '| Int_part (exp2 (INR n * r)) | /\
  let Jtdec := jtdec P W epsilon0 in
  \sum_(f : encT A M n) (Wght.d P f * echa(W , mkCode f (Jtdec f)))%R < epsilon.
Proof.
move=> Hepsilon r epsilon0 Hepsilon0 n Hn.
have [k Hk] : exists k, (log (INR k.+1) / INR n = r)%R.
  case: Hn => ? [? [Hn2 ?]].
  case/fp_nat : Hn2 => k Hn2.
  exists '| k |.-1.
  rewrite prednK; last first.
    apply/ltP/INR_lt. (* TODO: ssrZ? *)
    rewrite INR_Zabs_nat; [by rewrite -Hn2 | apply le_IZR; by rewrite -Hn2].
  rewrite -(@eqR_mul2l (INR n)); last by rewrite INR_eq0; apply/eqP; rewrite -lt0n.
  rewrite mulRCA mulRV ?INR_eq0' -?lt0n // mulR1 -(exp2K (INR n * r)) Hn2 INR_Zabs_nat //.
  apply le_IZR; by rewrite -Hn2.
set M := [finType of 'I_k.+1].
exists [finType of 'I_k.+1].
split; first by rewrite /= card_ord.
split.
  have -> : (INR n * r)%R = log (INR k.+1).
    rewrite -Hk mulRCA mulRV ?INR_eq0' -?lt0n ?mulR1 //; by case: Hn.
  rewrite logK; last exact/ltR0n.
  by rewrite Int_part_INR Zabs_nat_Z_of_nat card_ord.
move=> Jtdec.
rewrite /CodeErrRate.
rewrite [X in X < _](_ : _ = (1 / INR #|M| *
  \sum_(f : encT A M n) Wght.d P f * (\sum_(m in M) e(W, mkCode f (Jtdec f)) m))%R); last first.
  rewrite big_distrr /=.
  apply eq_bigr => f _.
  rewrite -!mulRA mulRC -!mulRA.
  do 2 f_equal.
  by rewrite mulRC.
rewrite [X in X < _](_ : _ = (\sum_(f : encT A M n) Wght.d P f * (e(W, mkCode f (Jtdec f))) ord0)%R); last first.
  transitivity (1 / INR #|M| *
    \sum_(f : encT A M n) (\sum_(m in M) Wght.d P f * (e(W, mkCode f (Jtdec f))) m))%R.
    f_equal.
    apply eq_bigr => i _; by rewrite big_distrr.
  rewrite exchange_big /=.
  transitivity (1 / INR #|M| * \sum_(f : encT A M n)
    (\sum_( m_ in M ) Wght.d P f * (e(W, mkCode f (Jtdec f))) ord0))%R.
    congr (_ * _)%R.
    rewrite [in RHS]exchange_big /=.
    apply eq_bigr => m' _.
    apply error_rate_symmetry.
    by move: Hepsilon0; rewrite /epsilon0_condition; case => /ltRW.
  rewrite exchange_big /= big_const /= iter_addR div1R mulRA mulVR ?mul1R //.
  by rewrite INR_eq0' card_ord.
set Cal_E := @cal_E M n epsilon0.
apply (@leR_ltR_trans
(\sum_(f : encT A M n) Wght.d P f * Pr (W ``(| f ord0)) (~: Cal_E f ord0) +
  \sum_(i | i != ord0)
  \sum_(f : encT A M n) Wght.d P f * Pr (W ``(| f ord0)) (Cal_E f i))%R).
  rewrite exchange_big /= -big_split /=.
  apply leR_sumR => /= i _.
  rewrite -big_distrr /= -mulRDr.
  apply leR_wpmul2l; first exact: FDist.ge0.
  rewrite [X in X <= _](_ : _ = Pr (W ``(| i ord0))
    (~: Cal_E i ord0 :|: \bigcup_(i0 : M | i0 != ord0) Cal_E i i0)); last first.
    congr Pr; apply/setP => /= tb.
    move: (preimC_Cal_E epsilon0 i tb); by rewrite inE.
  apply (@leR_trans (Pr (W ``(| i ord0)) (~: Cal_E i ord0) +
    Pr (W ``(| i ord0)) (\bigcup_(i0 | i0 != ord0) (Cal_E i i0)))%R).
    exact: Pr_union.
  exact/leR_add2l/Pr_bigcup.
rewrite first_summand //.
set lhs := (\sum_(_ < _ | _) _)%R.
have -> : lhs = (#| M |.-1%:R * Pr ((P `^ n) `x ((`O(P , W)) `^ n)) [set x | prod_rV x \in `JTS P W n epsilon0])%R.
  rewrite {}/lhs.
  rewrite [RHS](_ : _ = \sum_(H0 < k.+1 | H0 != ord0)
    Pr ((P `^ n) `x ((`O( P , W )) `^ n)) [set x | prod_rV x \in `JTS P W n epsilon0])%R; last first.
    rewrite big_const /= iter_addR; congr (_%:R * _)%R.
    rewrite card_ord /=.
    transitivity (#| setT :\ (@ord0 k)|).
      move: (cardsD1 (@ord0 k) setT) => /=.
      rewrite !cardsT !card_ord inE /= add1n.
      case=> H1; by rewrite {1}H1.
    rewrite cardsE.
    apply eq_card => m_.
    by rewrite -!topredE /= !in_set andbC.
  by apply eq_big => //; exact: second_summand.
rewrite card_ord /=.
apply (@leR_ltR_trans (epsilon0 + k%:R *
   Pr P `^ n `x (`O(P , W)) `^ n [set x | prod_rV x \in `JTS P W n epsilon0])%R).
  apply leR_add2r.
  rewrite Pr_of_cplt leR_subl_addr addRC -leR_subl_addr; apply/JTS_1 => //.
  by case: Hepsilon0.
  by case: Hn => _ [_ []].
apply (@leR_ltR_trans (epsilon0 +
    #| M |%:R * exp2 (- n%:R * (`I(P, W ) - 3 * epsilon0)))).
  apply/leR_add2l/leR_pmul.
    exact: leR0n.
    exact: Pr_ge0.
    apply/le_INR/leP; by rewrite card_ord.
  exact: non_typical_sequences.
apply (@ltR_trans (epsilon0 + epsilon0)); last first.
  case: Hepsilon0 => ? [? ?]; lra.
apply ltR_add2l.
have -> : INR #| M | = exp2 (log (INR #| M |)).
  rewrite logK // (_ : 0 = INR 0)%R //.
  apply lt_INR. rewrite card_ord. exact/ltP.
rewrite -ExpD.
rewrite (_ : _ + _ = - n%:R * (`I(P, W) - log #| M |%:R / n%:R - 3 * epsilon0))%R; last first.
  field.
  apply/eqP; rewrite INR_eq0' gtn_eqF //; by case: Hn.
rewrite (_ : _ / _ = r)%R; last by rewrite -Hk card_ord.
apply (@ltR_trans (exp2 (- n%:R * epsilon0))).
  apply Exp_increasing => //.
  rewrite !mulNR ltR_oppr oppRK; apply/ltR_pmul2l.
  - apply ltR0n; by case: Hn.
  - case: Hepsilon0 => _ [_ Hepsilon0].
    apply (@ltR_pmul2l 4) in Hepsilon0; last lra.
    rewrite mulRCA mulRV ?mulR1 in Hepsilon0; last exact/eqP.
    clear Hk; lra.
apply (@ltR_leR_trans (exp2 (- (- (log epsilon0) / epsilon0) * epsilon0))).
  apply Exp_increasing => //; apply ltR_pmul2r.
  - rewrite /epsilon0_condition in Hepsilon0; tauto.
  - rewrite ltR_oppr oppRK; by case: Hn => _ [Hn2 _].
    rewrite !mulNR -mulRA mulVR ?mulR1 ?oppRK; last first.
      by apply/eqP/gtR_eqF; case: Hepsilon0.
    by rewrite logK; [exact/leRR | case: Hepsilon0].
Qed.

End random_coding_good_code_existence.

Section channel_coding_theorem.

Variables (A B : finType) (W : `Ch(A, B)).
Hypothesis set_of_I_nonempty : classical_sets.nonempty (fun y => exists P, `I(P, W) = y).

Local Open Scope zarith_ext_scope.

Theorem channel_coding (r : CodeRateType) : r < capacity W ->
  forall epsilon, 0 < epsilon ->
    exists n M (c : code A B M n), CodeRate c = r /\ echa(W, c) < epsilon.
Proof.
move=> r_I epsilon Hepsilon.
have [P HP] : exists P : fdist A, r < `I(P, W).
  apply NNPP => abs.
  have {}abs : forall P : fdist A, `I(P, W) <= r.
    move/not_ex_all_not in abs.
    move=> P; exact/Rnot_lt_le/abs.
  have ? : capacity W <= r.
    apply Rstruct.real_sup_is_lub.
      case: set_of_I_nonempty => [x [P H1]]; split; first by exists x, P.
      by exists (rate r) => _ [Q _ <-]; exact/Rstruct.RleP/abs.
    by move=> x [P _ <-{x}]; exact: abs.
  lra.
have [epsilon0 Hepsilon0] : exists epsilon0,
  0 < epsilon0 /\ epsilon0 < epsilon / 2 /\ epsilon0 < (`I(P, W) - r) / 4.
  exists ((Rmin (epsilon/2) ((`I(P, W) - r) / 4))/2).
  have H0 : 0 < Rmin (epsilon / 2) ((`I(P, W) - r) / 4).
    apply Rmin_pos; apply mulR_gt0 => //; lra.
  split; first by apply mulR_gt0 => //; lra.
  split; [exact/(ltR_leR_trans (Rlt_eps2_eps _ H0))/geR_minl |
          exact/(ltR_leR_trans (Rlt_eps2_eps _ H0))/geR_minr ].
have [n Hn] : exists n, n_condition W P r epsilon0 n.
  destruct r as [r [num [den [Hnum [Hden Hr]]]]].
  have Hn : exists n, (0 < n)%nat /\
    - log epsilon0 / epsilon0 < INR n /\
    (maxn '| up (aep_bound P (epsilon0 / 3)) |
    (maxn '| up (aep_bound (`O(P , W)) (epsilon0 / 3)) |
          '| up (aep_bound (`J(P , W)) (epsilon0 / 3)) |) <= n)%nat.
    set supermax := maxn 1
      (maxn '| up (- log epsilon0 / epsilon0) |
      (maxn '| up (aep_bound P (epsilon0 / 3)) |
      (maxn '| up (aep_bound (`O(P , W)) (epsilon0 / 3)) |
            '| up (aep_bound (`J(P , W)) (epsilon0 / 3)) |))).
    exists supermax.
    split; first by rewrite leq_max.
    split.
      apply (@ltR_leR_trans (IZR (up (- log epsilon0 / epsilon0)))).
        rewrite up_Int_part.
        case: (base_Int_part (- log epsilon0 / epsilon0)) => H1 H2.
        rewrite plus_IZR //.
        move: H2.
        set eps := - log epsilon0 / epsilon0.
        move=> ?; lra.
      apply (@leR_trans (INR '| up (- log epsilon0 / epsilon0) |)).
        case: (Z_lt_le_dec (up (- log epsilon0 / epsilon0)) 0) => H1.
          apply (@leR_trans 0); [exact/IZR_le/ltZW | exact: leR0n].
        rewrite INR_Zabs_nat //; exact/leRR.
      apply le_INR.
      rewrite /supermax maxnA.
      apply/leP.
      by rewrite leq_max leq_max leqnn orbT.
    by rewrite [X in (_ <= X)%nat]maxnA leq_maxr.
  lapply (exists_frac_part Hn Hnum Hden); last move=> n1 n2 n1_n2 Pn1.
    case=> n [[Hn1 [Hn3 Hn4]] Hn2].
    exists n => /=.
    rewrite /n_condition.
    split => //; split => //; split => //.
    by rewrite -Hr in Hn2.
  split.
    apply/(@leq_trans n1) => //; tauto.
  split.
    apply (@ltR_leR_trans (INR n1)); [tauto | exact/le_INR/leP].
  apply leq_trans with n1 => //; tauto.
case: (random_coding_good_code (ltRW Hepsilon) Hepsilon0 Hn) =>
  M [HM [M_k H]].
case: (good_code_sufficient_condition HM H) => f Hf.
exists n, M, (mkCode f (jtdec P W epsilon0 f)); split => //.
rewrite /CodeRate M_k INR_Zabs_nat; last exact/Int_part_ge0.
suff -> : IZR (Int_part (exp2 (INR n * r))) = exp2 (INR n * r).
  rewrite exp2K /Rdiv -mulRA mulRCA mulRV ?INR_eq0' -?lt0n ?mulR1 //; by case: Hn.
by apply frac_Int_part; case: Hn => _ [_ []].
Qed.

End channel_coding_theorem.
