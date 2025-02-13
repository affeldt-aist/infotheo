(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint matrix perm.
From mathcomp Require Import archimedean lra ring.
From mathcomp Require Import mathcomp_extra boolp classical_sets reals Rstruct.
From mathcomp Require Import exp.
Require Import ssr_ext ssralg_ext bigop_ext realType_ext realType_ln.
Require Import fdist proba entropy aep typ_seq joint_typ_seq channel.
Require Import channel_code.

(**md**************************************************************************)
(* # Channel coding theorem (direct part)                                     *)
(*                                                                            *)
(* The channel coding theorem (direct part) is `channel_coding`.              *)
(*                                                                            *)
(* Documented in:                                                             *)
(* - Reynald Affeldt, Manabu Hagiwara, and Jonas Sénizergues. Formalization   *)
(*   of Shannon's theorems. Journal of Automated Reasoning, 53(1):63--103,    *)
(*   2014                                                                     *)
(*                                                                            *)
(* ```                                                                        *)
(*                  jtdec == joint typicality decoding                        *)
(*                   o_PI == TODO                                             *)
(*     epsilon0_condition == TODO                                             *)
(*   cal_E M n epsilong f == the set of output vb such that (f m, vb) is      *)
(*                           jointly typical                                  *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope ring_scope.
Local Open Scope jtyp_seq_scope.
Local Open Scope channel_code_scope.
Local Open Scope channel_scope.
Local Open Scope vec_ext_scope.

Import Order.Theory GRing.Theory Num.Theory.
#[local] Definition R := Rdefinitions.R.

(* TODO: doc *)
Module Wght.
Section wght.
Variables (A M : finType) (P : {fdist A}) (n : nat).

Definition f := [ffun g : encT A M n => \prod_(m in M) (P `^ n)%fdist (g m)].

Lemma f0 g : 0 <= f g. Proof. by rewrite ffunE prodr_ge0. Qed.

Lemma f1 : \sum_(g in {ffun M -> 'rV[A]_n}) f g = 1.
Proof.
under eq_bigr do rewrite ffunE /=.
rewrite -(bigA_distr_bigA (fun _ => (P `^ n)%fdist)) /=.
rewrite [RHS](_ : _ = \prod_(m0 : M | xpredT m0) 1); last by rewrite big1.
by apply eq_bigr => _ _; rewrite (FDist.f1 (P `^ n)%fdist).
Qed.

Definition d : {fdist encT A M n} := locked (FDist.make f0 f1).

Lemma dE x : d x = f x. Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
End wght.
End Wght.

Arguments Wght.d {A} {M} _ {n}.

Section joint_typicality_decoding.
Variables (A B M : finType) (n : nat).

Definition jtdec P W epsilon (f : encT A M n) : decT B M n :=
  [ffun tb => [pick m |
    (prod_rV (f m, tb) \in `JTS P W n epsilon) &&
    [forall m', (m' != m) ==> (prod_rV (f m', tb) \notin `JTS P W n epsilon)]]].

Lemma jtdec_map epsilon (P : {fdist A}) (W : `Ch(A, B)) (f : encT A M n) tb m0 m1 :
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
apply/not_existsP => abs.
set x := \sum_(f <- _) _ in H.
have : \sum_(f : encT A M n) Wght.d P f * epsilon <= x.
  rewrite /x ler_suml => //= f _.
  by rewrite ler_wpM2l // leNgt; exact/negP.
apply/negP.
rewrite -ltNge.
apply/(lt_le_trans H).
by rewrite -big_distrl /= (FDist.f1 (Wght.d P)) mul1r.
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
have -> : lhs = \sum_(f : encT A M n)
    (Wght.d P (o_PI m m' f) * e(W, mkCode (o_PI m m' f) (PHI' (o_PI m m' f))) m).
  rewrite Hlhs (reindex_onto (o_PI m m') (o_PI m m')) /=; last first.
    by move=> i _; apply/ffunP => m_; rewrite o_PI_2.
  by apply eq_bigl => x /=; apply/eqP/ffunP => y; exact: o_PI_2.
apply: eq_bigr => g _; rewrite wght_o_PI; congr (_ * _).
rewrite /ErrRateCond /= (_ : (o_PI m m' g) m = g m'); last by rewrite ffunE tpermL.
congr Pr; apply/setP => tb /=.
rewrite 2!inE.
apply/negbLR.
rewrite finset.in_setC negbK.
apply/idP/idP.
- rewrite {1}/PHI' {1}/jtdec ffunE.
  set p0 := fun _ => _ && _.
  case: (pickP _) => [m0 Hm0 | Hm0 /eqP //].
  case/eqP => ?; subst m0.
  rewrite /p0 {p0} in Hm0.
  rewrite /PHI' /jtdec.
  rewrite inE ffunE.
  case: (pickP _) => [m1 Hm1 | Hm1].
  + apply/eqP; f_equal.
    suff : (prod_rV (g m', tb) \in `JTS P W n epsilon) &&
      [forall m'0, (m'0 != m') ==> (prod_rV (g m'0, tb) \notin `JTS P W n epsilon)].
      by move/(jtdec_map Hm1).
    apply/andP; split.
    * by move: Hm0; rewrite {1}/o_PI ffunE tpermL => /andP[].
    * apply/forallP => m_; apply/implyP => m__m'.
      case/andP : Hm0 => Hm0 /forallP Hm0'.
      have [m_m|m_m] := eqVneq m_ m.
      - subst m_.
        by move: (Hm0' m'); rewrite eq_sym m__m' /= /o_PI ffunE tpermR; exact.
      - move: (Hm0' m_) => {}Hm0'.
        rewrite eq_sym in m__m'.
        by move: Hm0'; rewrite m_m /= /o_PI ffunE tpermD // eq_sym.
  + exfalso.
    rewrite {1}/o_PI ffunE tpermL in Hm0.
    move/negbT: {Hm1}(Hm1 m').
    rewrite negb_and; case/orP => Hm'.
    * by case/andP : Hm0 => Hm0 _; rewrite Hm0 in Hm'.
    * move/negP : Hm'; apply.
      apply/forallP => m_; apply/implyP => m_m'.
      case/andP: Hm0 => Hm0 /forallP Hm01.
      have [m_m|m_m] := eqVneq m_ m.
      - subst m_.
        by move: (Hm01 m'); rewrite eq_sym m_m' /= /o_PI ffunE tpermR; exact.
      - by move: (Hm01 m_); rewrite m_m /= /o_PI ffunE tpermD // eq_sym.
- rewrite {1}/PHI' {1}/jtdec inE ffunE.
  case: (pickP _) => [m0 Hm0 | Hm0 /eqP //].
  case/eqP => ?; subst m0.
  apply/eqP.
  rewrite /PHI' /jtdec ffunE.
  case: (pickP _) => [m1 Hm1 | Hm1].
  + f_equal.
    suff : (prod_rV ((o_PI m m' g) m, tb) \in `JTS P W n epsilon) &&
      [forall m'0, (m'0 != m) ==>
         (prod_rV ((o_PI m m' g) m'0, tb) \notin `JTS P W n epsilon)].
      by move/(jtdec_map Hm1).
    apply/andP; split.
    - by rewrite /o_PI ffunE tpermL; case/andP: Hm0.
    - apply/forallP => m_; apply/implyP => m_m.
      have [?|m_m'] := eqVneq m_ m'.
      + subst m_.
        rewrite /o_PI ffunE tpermR.
        case/andP : Hm0 => _ /forallP/(_ m).
        by rewrite eq_sym m_m.
      + rewrite eq_sym in m_m; rewrite eq_sym in m_m'.
        rewrite /o_PI ffunE tpermD //.
        case/andP : Hm0 => _ /forallP/(_ m_).
        by rewrite eq_sym m_m'.
  * exfalso.
    move: {Hm1}(Hm1 m) => /negbT; rewrite negb_and => /orP[|].
    - rewrite /o_PI ffunE tpermL.
      by case/andP : Hm0 => ->.
    - move/negP; apply.
      apply/forallP => m_; apply/implyP => m_m.
      have [?|m_m'] := eqVneq m_ m'.
      + subst m_.
        rewrite /o_PI ffunE tpermR.
        case/andP : Hm0 => _ /forallP/(_ m).
        by rewrite eq_sym m_m.
      + rewrite eq_sym in m_m; rewrite eq_sym in m_m'.
        rewrite /o_PI ffunE tpermD //.
        case/andP : Hm0 => _ /forallP/(_ m_).
        by rewrite eq_sym m_m'.
Qed.

End joint_typicality_decoding.

(* TODO: move? *)
Section sum_rV_ffun.
Lemma sum_rV_ffun S (I J : finType) (F : {ffun I -> J} -> S)
  (G : _ -> _ -> _) (idef : I) (zero : 'I_ _) : O = zero ->
  \sum_(j : 'rV[J]_#|I|) G (F [ffun x => j ord0 (enum_rank x)]) (j ord0 zero) =
  \sum_(f : {ffun I -> J}) G (F f) (f (nth idef (enum I) 0)) :> R.
Proof.
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

Variables (B A : finType) (W : `Ch(A, B)) (P : {fdist A}).

Definition epsilon0_condition r epsilon epsilon0 :=
  0 < epsilon0 /\ epsilon0 < epsilon / 2 /\ epsilon0 < (`I(P, W) - r) / 4.

(* TODO: move, doc *)
Definition frac_part (x : R) := x - (Num.floor x)%:~R.
Definition n_condition r epsilon0 n :=
  (O < n)%nat /\ - log epsilon0 / epsilon0 < n%:R /\
  frac_part (2 `^ (r *+ n)) = 0 /\ (JTS_1_bound P W epsilon0 <= n)%nat.

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
rewrite (partition_big (fun x => thead x) (fun x => P1 x)) //=; last first.
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
Lemma rsum_rmul_tuple_pmf_tnth {C : finType} n k (Q : {fdist C}) :
  \sum_(t : {:k.-tuple ('rV[C]_n)}) \prod_(m < k) (Q `^ n)%fdist t !_ m = 1.
Proof.
transitivity (\sum_(j : {ffun 'I_k -> 'rV[_]_n}) \prod_(m < k) (Q `^ _)%fdist (j m)).
  rewrite (reindex_onto (fun p => [ffun x => p!_(enum_rank x)])
                        (fun x => fgraph x)) //=; last first.
    by move=> f _; apply/ffunP => /= i; rewrite ffunE tnth_fgraph enum_rankK.
  rewrite (big_tcast (esym (card_ord k))) esymK.
  apply eq_big => //.
  - move=> i /=; apply/esym/eqP/eq_from_tnth => j.
    by rewrite tnth_fgraph ffunE enum_valK.
  - by move=> i _; apply eq_bigr => j _; rewrite ffunE /= tcastE -enum_rank_ord.
rewrite -(bigA_distr_bigA (fun _ => (Q `^ _)%fdist)) /= big_const.
by rewrite FDist.f1 iter_mulr mulr1 expr1n.
Qed.

(* TODO: move? *)
Lemma rsum_rmul_tuple_pmf {C : finType} n k (Q : {fdist C}) :
  \sum_(t in {:k.-tuple ('rV[C]_n)}) \prod_(x <- t) (Q `^ n)%fdist x = 1.
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
  let M := 'I_k.+1 in
  (\sum_(f : encT A M n) Wght.d P f *
    Pr (W ``(| f ord0)) (~: cal_E epsilon0 f ord0)) =
  Pr ((P `X W) `^ n)%fdist (~: `JTS P W n epsilon0).
Proof.
move=> M.
have M_prednK : #|M|.-1.+1 = #|M| by rewrite card_ord.
pose E_F_N := @cal_E M n epsilon0.
rewrite {1}/cal_E.
case/card_gt0P : (fdist_card_neq0 P) => a _.
pose zero := @enum_rank M ord0.
have : 0%N = zero :> nat by rewrite /zero enum_rank_ord.
move/(sum_rV_ffun (Wght.d P)
  (fun r v =>
     r * Pr (W ``(| v )) (~: [set w | prod_rV (v, w) \in `JTS P W n epsilon0]))
  ord0).
rewrite (_ : nth ord0 (enum M) 0 = ord0); last by rewrite enum_ordSl.
move=> <- /=.
transitivity (\sum_(v : 'rV['rV[A]_n]_#|M|) (
    (\prod_(m : M) (P `^ n)%fdist ([ffun x => v ``_ x] (enum_rank m))) *
    \sum_(w | w \in ~: cal_E epsilon0 [ffun x => v ``_ x] zero)
    (W ``(| [ffun x => v ``_ x] zero)) w)).
  apply eq_bigr => v _; congr (_ * _).
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
      (\prod_(m : M)
         (P `^ _)%fdist ((tcast M_prednK [tuple of v :: j]) !_ (enum_rank m)))).
  rewrite (reindex_onto
             (fun y : {ffun _ -> 'rV__} => \row_(i < _) y (enum_val i))
      (fun p : 'rV_ _ => [ffun x => p ``_ (enum_rank x)])) //=; last first.
    move=> v _; by apply/rowP => i; rewrite mxE ffunE enum_valK.
  apply trans_eq with (\sum_(f : {ffun M -> 'rV__})
    ((\prod_(m < k.+1) (P `^ n)%fdist (f m)) *
      \sum_(y in ~: [set y0 | prod_rV (f ord0, y0) \in `JTS P W n epsilon0])
      W ``(y | f ord0))).
    apply eq_big => //= f.
    - apply/eqP/ffunP => m; by rewrite ffunE mxE enum_rankK.
    - move/eqP => Hf;  congr (_ * _).
        apply eq_bigr => i _; by rewrite -[in RHS]Hf 2!ffunE.
      apply eq_big => /=.
        move=> ?; by rewrite !inE -[in RHS]Hf !ffunE mxE.
      move=> ? _; by rewrite -[in RHS]Hf !ffunE mxE.
  rewrite (_ : ord0 = nth ord0 (enum M) 0); last by rewrite enum_ordSl.
  rewrite -(big_tuple_ffun _ (fun f => \prod_(m : M) (P `^ n)%fdist (f m))
    (fun r yn => r *
      (\sum_(y in ~: [set y0 | prod_rV (yn, y0) \in `JTS P W n epsilon0])
      W ``(y | yn))) (\row_(i < n) a) ord0).
  transitivity (\sum_(j : _)
    (\prod_(m : M) (P `^ n)%fdist ((tcast M_prednK j) !_ (enum_rank m))) *
      (\sum_(y in ~: [set y0 | prod_rV (nth (\row_(i < n) a) j 0, y0) \in
          `JTS P W n epsilon0])
      W ``(y | nth (\row_(i < n) a) j 0))).
    rewrite (big_tcast (esym M_prednK)) esymK.
    apply eq_bigr => i _; congr (_ * _).
      apply eq_bigr => m _; by rewrite ffunE.
    have H : nth (\row_(i < n) a) (tcast M_prednK i) 0 = nth (\row_(i < n) a) i 0.
      move: M_prednK i; rewrite card_ord => M_prednK i.
      rewrite -(tnth_nth _ i ord0) -(tnth_nth _ (tcast M_prednK i) ord0).
      by rewrite tcastE /= cast_ord_id.
    apply eq_big => m; by rewrite !inE H.
  rewrite -(@big_tuple_cons_behead _ #|M|.-1
   (fun j => ((\prod_(m : M) (P `^ n)%fdist ((tcast M_prednK j) !_ (enum_rank m))) *
     (\sum_(y in ~: [set y0 | prod_rV (nth (\row_(i < n) a) j 0, y0) \in
         `JTS P W n epsilon0]) W ``(y | nth (\row_(i < n) a) j 0)))) xpredT xpredT).
  apply eq_bigr => ta _ /=; by rewrite -big_distrl /= mulrC.
transitivity ((\sum_(ta in 'rV[A]_n) (P `^ _)%fdist ta *
    (\sum_(y in ~: [set y0 | prod_rV (ta, y0) \in `JTS P W n epsilon0])
    (W ``(| ta ) ) y)) *
    \sum_(j in {:k.-tuple ('rV[A]_n)}) \prod_(m < k) ((P `^ _)%fdist (j !_ m))).
  rewrite big_distrl /=.
  apply eq_bigr => ta _.
  rewrite -mulrA mulrCA; congr (_ * _).
  transitivity (\sum_(j in {: #|'I_k|.-tuple ('rV[A]_n) })
      (P `^ _)%fdist ta * \prod_(m < k) (P `^ _)%fdist (j !_ (enum_rank m))).
    have k_prednK : #|'I_k.+1|.-1 = #|'I_k| by rewrite !card_ord.
    rewrite (big_tcast (esym k_prednK)) esymK.
    apply eq_bigr => i0 Hi0.
    rewrite big_ord_recl /=.
    congr ((P `^ _)%fdist _ * _); first by rewrite tcastE // enum_rank_ord.
    apply eq_bigr => i1 _; congr ((P `^ _)%fdist _).
    rewrite !tcastE {1}/tnth /=.
    rewrite (_ : enum_rank _ = (enum_rank i1).+1 :> nat) /=; last by rewrite !enum_rank_ord.
    apply set_nth_default; by rewrite size_tuple /= enum_rank_ord /= card_ord.
  rewrite -big_distrr /=; congr (_ * _).
  rewrite (big_tcast (esym (card_ord k))) esymK.
  apply eq_bigr => /= i0 _.
  apply eq_bigr => /= i1 _.
  by rewrite tcastE -enum_rank_ord.
rewrite rsum_rmul_tuple_pmf_tnth mulr1.
transitivity (\sum_(v in 'rV[A]_n)
  \sum_(y in ~: [set w | prod_rV (v, w) \in `JTS P W n epsilon0])
    (((P `X W) `^ n)%fdist (prod_rV (v, y)))).
  apply eq_bigr => /= v _.
  rewrite big_distrr /=.
  apply eq_bigr => // w _.
  rewrite DMCE 2!fdist_rVE -big_split /=.
  apply eq_bigr => /= i _.
  by rewrite fdist_prodE -fst_tnth_prod_rV -snd_tnth_prod_rV /=.
rewrite /Pr big_rV_prod pair_big_dep /=.
by apply eq_bigl; case=> /= ? ?; rewrite !inE.
Qed.

(* TODO: move? *)
Lemma big_cat_tuple {C : finType} m n (F : (m + n)%nat.-tuple C -> R) :
  (\sum_(i in {:m.-tuple C}) \sum_(j in {: n.-tuple C})
  F [tuple of (i ++ j)] = \sum_(p in {: (m + n)%nat.-tuple C}) (F p)).
Proof.
elim: m n F => [m2 F /=|m IH n F].
- transitivity (\sum_(i <- [tuple] :: [::])
    \sum_(j in {: m2.-tuple C}) F [tuple of i ++ j] ).
    apply congr_big => //=.
    apply (@eq_from_nth _ [tuple]);
      rewrite /index_enum -enumT /= (eqP (enum_tupleP _)) card_tuple expn0 //.
    move=> i; rewrite ltnS leqn0 => /eqP ->.
    rewrite tupleE /=.
    case: (enum _) => //= t.
    by rewrite (tuple0 t).
  rewrite big_cons /= big_nil /= addr0.
  apply eq_bigr => // i _; congr F.
  exact/val_inj.
- symmetry.
  transitivity (\sum_(p in [the finType of (m + n).+1.-tuple C]) F p);
    first by apply congr_big.
  rewrite -(@big_tuple_cons_behead _ _ _ xpredT xpredT).
  rewrite -(@big_tuple_cons_behead _ _ _ xpredT xpredT).
  apply eq_bigr => i _.
  move: {IH}(IH n (fun x => F [tuple of i :: x])) => <-.
  apply eq_bigr => /= t _; apply eq_bigr => /= t' _; congr F.
  exact/val_inj.
Qed.

(* TODO: move? *)
Lemma big_cat_tuple_seq {C : finType} m n (F : seq C -> R) :
  \sum_(i in {:m.-tuple C} ) \sum_(j in {: n.-tuple C}) (F (i ++ j)) =
  \sum_(p in {: (m + n)%nat.-tuple C}) (F p).
Proof.
move: (@big_cat_tuple _ m n (fun l => if size l == (m + n)%nat then F l else 0)).
set lhs := (\sum_(i in _) _) => H.
apply trans_eq with lhs.
  apply eq_bigr => /= t _; apply eq_bigr => /= t' _.
  case: ifP => //; by rewrite size_tuple eqxx.
rewrite H; apply eq_bigr => /= t _; by rewrite size_tuple eqxx.
Qed.

Lemma second_summand n k epsilon0 :
  let M := 'I_k.+1 in
    forall i, i != ord0 ->
      (\sum_(f : encT A M n) Wght.d P f *
        Pr (W ``(| f ord0)) (cal_E epsilon0 f i)) =
   Pr ((P `^ n) `x `O( P , W ) `^ n)%fdist [set x | prod_rV x \in `JTS P W n epsilon0].
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
  Wght.d P [ffun x => (tcast Hcast [tuple of j0 :: j1 ++ ji :: j2])!_x] *
  \sum_(y | y \in [set w | prod_rV (ji, w) \in `JTS P W n epsilon0])
  (W ``(| j0)) y).
  transitivity (
    \sum_(j0 in 'rV[A]_n)
    \sum_(j1 in {: i.-1.-tuple ('rV[A]_n)})
    \sum_(ji in 'rV[A]_n)
    \sum_(j2 in {: (#|M| - i.+1).-tuple ('rV[A]_n)})
    Wght.d P [ffun x => (tcast Hcast [tuple of j0 :: j1 ++ ji :: j2])!_x] *
    \sum_( y | y \in [set w | prod_rV (ji, w) \in `JTS P W n epsilon0])
    (W ``(| j0) ) y).
    rewrite (reindex_onto (fun p => [ffun x => p!_(enum_rank x)]) (fun y => fgraph y)) /=; last first.
      move=> f _; apply/ffunP => m; by rewrite ffunE tnth_fgraph enum_rankK.
    transitivity ( \sum_(j : _)
      (Wght.d P [ffun x => j!_(enum_rank x)] *
        Pr (W ``(| [ffun x => j!_(enum_rank x)] ord0)) (E_F_N [ffun x => j!_(enum_rank x)] i))).
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
    rewrite (big_tcast Ht) //; apply eq_bigr => /= i3 _; congr (_ * _).
    - rewrite 2!Wght.dE /Wght.f 2!ffunE /=.
      rewrite (reindex_onto enum_rank enum_val); last by move=> *; rewrite enum_valK.
      apply eq_big => /=; first by move=> x; rewrite enum_rankK eqxx inE.
      move=> i4 _; congr ((P `^ _)%fdist _).
      rewrite !ffunE; congr (_ !_ _).
      apply/val_inj => /=.
      rewrite [LHS]eq_tcast /= !eq_tcast /= [RHS]eq_tcast eq_tcast /=; congr (_ :: _ ++ _ :: _).
      by rewrite eq_tcast.
    - apply eq_big.
      + move=> x /=.
        rewrite !inE ffunE.
        rewrite (_ : (_ !_ _) = i2) //=.
        rewrite enum_rank_ord /= tcastE !cast_ord_comp (tnth_nth i0) /=.
        rewrite eq_tcast /=.
        rewrite -cat_cons nth_cat /= size_tuple prednK ?lt0n // ltnn subnn.
        by rewrite eq_tcast.
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
   \prod_(i <- j1 ++ j2) (P `^ n)%fdist i) *
  (\sum_(j0 in 'rV[A]_n)
    \sum_(ji in 'rV[A]_n)
    ((P `^ n)%fdist j0) * ((P `^ n)%fdist ji) *
    (\sum_( y | y \in
      [set y0 | prod_rV (ji , y0) \in `JTS P W n epsilon0])
    (W ``(| j0) ) y))).
  rewrite !big_distrl /=.
  apply eq_bigr => j1 _.
  rewrite !big_distrl /=.
  apply eq_bigr => j2 _.
  rewrite !big_distrr /=.
  apply eq_bigr => j0 _.
  rewrite !big_distrr /=.
  apply eq_bigr => j3 _.
  rewrite !mulrA Wght.dE /Wght.f /=; congr (_ * _).
  transitivity (\prod_( i <- j0 :: j1 ++ j3 :: j2) (P `^ _)%fdist i); last first.
    rewrite big_cons -mulrA mulrCA; congr (_ * _).
    rewrite big_cat /= big_cons [in RHS]mulrC mulrCA; congr (_ * _).
    by rewrite big_cat /= mulrC.
  rewrite [in RHS](big_nth j0) /= big_mkord.
  transitivity (\prod_(j < #|@predT M|)
    (P `^ _)%fdist ([ffun x => (tcast Hcast [tuple of j0 :: j1 ++ j3 :: j2])!_(enum_rank x)] (enum_val j))).
    rewrite ffunE; apply eq_big => ? //= _.
    by rewrite !ffunE enum_valK.
  have j_M : (size (j1 ++ j3 :: j2)).+1 = #|M|.
    rewrite size_cat (size_tuple j1) /= (size_tuple j2) card_ord.
    by rewrite -[RHS](card_ord k.+1) -Hcast card_ord.
  rewrite j_M.
  apply eq_bigr => i0 _; congr ((P `^ n)%fdist _).
  rewrite ffunE /= enum_valK tcastE /tnth /=.
  apply set_nth_default; by rewrite /= j_M ltn_ord.
transitivity (\sum_(j0 : 'rV[A]_n) \sum_(ji : 'rV[A]_n)
  ((P `^ n)%fdist j0) * ((P `^ n)%fdist ji) * (\sum_( y | y \in
    [set y0 in 'rV[B]_n | prod_rV (ji , y0) \in `JTS P W n epsilon0])
  (W ``(| j0)) y)).
  set lhs := (\sum_(_ <- _) _).
  suff : lhs = 1 by move=> ->; rewrite mul1r.
  rewrite /lhs {lhs}.
  rewrite (@big_cat_tuple_seq _ i.-1 (#|M| - i.+1) (fun x => \prod_(i0 <- x) (P `^ n)%fdist i0)).
  by rewrite rsum_rmul_tuple_pmf.
transitivity (\sum_(ji : 'rV[A]_n) ((P `^ n)%fdist ji) *
  (\sum_(y | y \in [set y0 | prod_rV (ji , y0) \in `JTS P W n epsilon0])
  \sum_(j0 : 'rV[A]_n) ((W ``(| j0) ) y) * ((P `^ n)%fdist j0))).
  rewrite exchange_big /=.
  apply eq_bigr => ta _.
  transitivity (\sum_(i1 : 'rV[A]_n) (P `^ _)%fdist ta * (P `^ _)%fdist i1 *
    (\sum_(y in [set y0 | prod_rV (ta, y0) \in `JTS P W n epsilon0])
       W ``(y | i1))).
    apply eq_bigr => i1 _.
    by rewrite -mulrA mulrCA mulrA.
  rewrite exchange_big /= big_distrr /=.
  apply eq_bigr => ta' _.
  rewrite -[in X in _ = (_ * X)]big_distrl /= -mulrA; congr (_ * _).
  by rewrite mulrC.
transitivity (\sum_(ji : 'rV[A]_n) ((P `^ n)%fdist ji) *
  \sum_( y | y \in [set y0 | prod_rV (ji , y0) \in `JTS P W n epsilon0])
  ((`O(P , W)) `^ n)%fdist y).
  apply eq_bigr => ta _; congr (_ * _); apply eq_bigr => /= tb _.
  by rewrite fdist_rV_out; apply eq_bigr => i0 _; by rewrite DMCE.
transitivity (\sum_(v : 'rV[A]_n)
  (\sum_(y | y \in
    [set y0 | prod_rV (v , y0) \in `JTS P W n epsilon0])
    ((P `^ n) `x ((`O(P , W)) `^ n))%fdist (v, y))).
  apply eq_bigr => // v _.
  rewrite big_distrr /=; apply eq_bigr => w _; by rewrite fdist_prodE.
transitivity (\sum_( jiy | prod_rV jiy \in `JTS P W n epsilon0)
  ((P `^ n) `x ((`O(P , W)) `^ n))%fdist jiy).
  rewrite [in LHS]pair_big_dep /=.
  by apply eq_big => -[? ?] /=; rewrite !inE ?fdist_prodE.
by apply eq_bigl => ?; rewrite !inE.
Qed.

Local Close Scope tuple_ext_scope.

Lemma preimC_Cal_E k n epsilon0 :
  let M := 'I_k.+1 in
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
    rewrite finset.in_setU finset.in_setC {1}/Cal_E {1}/cal_E inE; apply/orP; left.
    case/andP : Hm2 => _ /forallP/(_ ord0)/implyP; apply.
    by move/eqP in m2m0; apply: contra m2m0 => /eqP <-.
  + move=> _.
    rewrite finset.in_setU.
    move/negbT : {Hm2}(Hm2 ord0).
    rewrite negb_and.
    case/orP => Hm2.
    * by rewrite finset.in_setC {1}/Cal_E {1}/cal_E inE Hm2.
    * apply/orP; right.
      apply/negPn.
      move: Hm2; apply contra => Hm2.
      apply/forallP => m_; apply/implyP => m_m0.
      apply: contra Hm2 => Hm2.
      by apply/bigcupP; exists m_ => //; rewrite /Cal_E /cal_E inE.
- rewrite finset.in_setU ffunE.
  case: (pickP _) => [m2 Hm2|//].
  case/orP.
  + rewrite finset.in_setC /cal_E inE => Hy.
    apply/eqP => -[m20].
    by case/andP : Hm2; rewrite m20 (negbTE Hy).
  + case/bigcupP => m Hm; rewrite /cal_E 2!inE => m_tb.
    apply/eqP => -[m20].
    by case/andP : Hm2 => _ /forallP /(_ m); rewrite !inE m_tb m20 Hm implyTb.
Qed.

(* TODO: move *)
Lemma ExpK (R' : realType) n x : (1 < n)%N -> Log n (n%:R `^ x) = x :> R'.
Proof.
move=> n1; rewrite /Log prednK// 1?ltnW// ln_powR mulrK //.
by apply/unitf_gt0/ln_gt0; rewrite ltr1n.
Qed.

Lemma random_coding_good_code epsilon : 0 <= epsilon ->
  forall (r : CodeRateType),
    forall epsilon0, epsilon0_condition r epsilon epsilon0 ->
    forall n, n_condition r epsilon0 n ->
  exists M : finType, (0 < #|M|)%nat /\ #|M| = `| Num.floor (2 `^ (rate r *+ n)) |%N /\
  let Jtdec := jtdec P W epsilon0 in
  (\sum_(f : encT A M n) Wght.d P f * echa(W , mkCode f (Jtdec f))) < epsilon.
Proof.
move=> Hepsilon r epsilon0 Hepsilon0 n Hn.
have [k Hk] : exists k, log k.+1%:R / n%:R = r :> R.
  case: Hn => ? [? [Hn2 ?]].
  exists `| Num.floor (2 `^ (rate r *+ n)) |.-1.
  rewrite prednK; last first.
    rewrite absz_gt0; apply/eqP => Habs.
    rewrite /frac_part Habs subr0 in Hn2.
    by move/eqP : Hn2; apply/negP; rewrite gt_eqF// powR_gt0.
  rewrite eqr_divr_mulr; last by rewrite (eqr_nat R n 0) -lt0n.
  rewrite -[in LHS]mulrz_nat natz gez0_abs.
    move/subr0_eq: Hn2 => <-.
    by rewrite /log ExpK // mulr_natr.
  by rewrite floor_ge0 powR_ge0.
set M : finType := 'I_k.+1.
exists M.
split; first by rewrite /= card_ord.
split.
  have -> : rate r *+ n = log k.+1%:R.
    rewrite -Hk -[LHS]mulr_natr -mulrA mulVr ?mulr1 //.
    by case: Hn; rewrite -(ltr_nat R) => /unitf_gt0.
  rewrite LogK // card_ord (floor_def (m:=k.+1)) // -{1}natz mulrz_nat lexx.
  by rewrite addrC -intS -natz mulrz_nat ltr_nat leqnn.
move=> Jtdec.
rewrite /CodeErrRate.
rewrite [X in X < _](_ : _ = (1 / #|M|%:R *
  \sum_(f : encT A M n) Wght.d P f * (\sum_(m in M) e(W, mkCode f (Jtdec f)) m))); last first.
  rewrite big_distrr /=.
  apply eq_bigr => f _.
  by rewrite -!mulrA mulrC mul1r -!mulrA [Wght.d _ _ * _]mulrC.
rewrite [X in X < _](_ : _ = (\sum_(f : encT A M n) Wght.d P f * (e(W, mkCode f (Jtdec f))) ord0)); last first.
  transitivity (1 / #|M|%:R *
    \sum_(f : encT A M n) (\sum_(m in M) Wght.d P f * (e(W, mkCode f (Jtdec f))) m)).
    f_equal.
    apply eq_bigr => i _; by rewrite big_distrr.
  rewrite exchange_big /=.
  transitivity (1 / #|M|%:R * \sum_(f : encT A M n)
    (\sum_( m_ in M ) Wght.d P f * (e(W, mkCode f (Jtdec f))) ord0)).
    congr (_ * _).
    rewrite [in RHS]exchange_big /=.
    apply eq_bigr => m' _.
    apply error_rate_symmetry.
    by move: Hepsilon0; rewrite /epsilon0_condition; case => /ltW.
  rewrite exchange_big /= big_const /= iter_addr addr0 div1r.
  by rewrite -(mulr_natl (\sum__ _)) mulrA mulVr (mul1r,unitf_gt0) // card_ord.
set Cal_E := @cal_E M n epsilon0.
apply (@le_lt_trans _ _
(\sum_(f : encT A M n) Wght.d P f * Pr (W ``(| f ord0)) (~: Cal_E f ord0) +
  \sum_(i | i != ord0)
  \sum_(f : encT A M n) Wght.d P f * Pr (W ``(| f ord0)) (Cal_E f i))).
  rewrite exchange_big /= -big_split /=.
  apply ler_sum => /= i _.
  rewrite -big_distrr /= -mulrDr.
  apply ler_wpM2l; first by rewrite FDist.ge0.
  rewrite [X in (X <= _)](_ : _ = Pr (W ``(| i ord0))
    (~: Cal_E i ord0 :|: \bigcup_(i0 : M | i0 != ord0) Cal_E i i0)); last first.
    congr Pr; apply/setP => /= tb.
    move: (preimC_Cal_E epsilon0 i tb); by rewrite inE.
  apply (@le_trans _ _ (Pr (W ``(| i ord0)) (~: Cal_E i ord0) +
    Pr (W ``(| i ord0)) (\bigcup_(i0 | i0 != ord0) (Cal_E i i0)))).
    exact: le_Pr_setU.
  by rewrite lerD2l Pr_bigcup.
rewrite first_summand //.
set lhs := (\sum_(_ < _ | _) _).
have -> : lhs = (#| M |.-1%:R * Pr ((P `^ n) `x ((`O(P , W)) `^ n)) [set x | prod_rV x \in `JTS P W n epsilon0])%fdist.
  rewrite {}/lhs.
  rewrite [RHS](_ : _ = \sum_(H0 < k.+1 | H0 != ord0)
    Pr ((P `^ n) `x ((`O( P , W )) `^ n))%fdist [set x | prod_rV x \in `JTS P W n epsilon0]); last first.
    rewrite big_const /= iter_addr addr0 -[in RHS]mulr_natl.
    congr (_%:R * _).
    rewrite card_ord /=.
    transitivity (#| finset.setT :\ (@ord0 k)|).
      move: (cardsD1 (@ord0 k) finset.setT) => /=.
      rewrite !cardsT !card_ord inE /= add1n.
      case=> H1; by rewrite {1}H1.
    rewrite cardsE.
    apply eq_card => m_.
    by rewrite -!topredE /= !finset.in_set andbC/= inE.
  by apply eq_big => //; exact: second_summand.
rewrite card_ord /=.
apply (@le_lt_trans _ _ (epsilon0 + k%:R *
   Pr (P `^ n) `x (`O(P , W) `^ n) [set x | prod_rV x \in `JTS P W n epsilon0])%fdist).
  rewrite lerD2r.
  rewrite Pr_setC lerBlDr addrC -lerBlDr; apply/JTS_1 => //.
  by case: Hepsilon0.
  by case: Hn => _ [_ []].
apply (@le_lt_trans _ _ (epsilon0 +
    #| M |%:R * 2 `^ (- n%:R * (`I(P, W ) - 3 * epsilon0)))).
  rewrite lerD2l ler_pM //. by rewrite card_ord ler_nat.
  exact: non_typical_sequences.
apply (@lt_trans _ _ (epsilon0 + epsilon0)); last by case: Hepsilon0 => ? [? ?]; lra.
rewrite ltrD2l.
have -> : #| M |%:R = 2 `^ (log #| M |%:R) :> R by rewrite LogK // card_ord.
rewrite -powRD; last by rewrite (eqr_nat R 2 0) implybT.
rewrite (_ : _ + _ = - n%:R * (`I(P, W) - log #| M |%:R / n%:R - 3 * epsilon0)); last first.
  field.
  by case: Hn; rewrite -(ltr_nat R) => /lt0r_neq0.
rewrite (_ : _ / _ = rate r); last by rewrite -Hk card_ord.
apply (@lt_trans _ _ (2 `^ (- n%:R * epsilon0))).
  rewrite gt1_ltr_powRr ?ltr1n//.
  rewrite -mulr_natr -mulNr.
  rewrite -2!mulrA ltr_nM2l ?oppr_lt0 //.
  rewrite ltr_pM2l; last by case: Hn; rewrite (ltr_nat R 0 n).
  case: Hepsilon0 => _ [_ Hepsilon0].
  rewrite -(@ltr_pM2l R 4) in Hepsilon0; last lra.
  rewrite mulrCA mulrV ?mulR1 in Hepsilon0; last first.
    by rewrite unitfE (eqr_nat R 4 0).
  lra.
apply (@lt_le_trans _ _ (2 `^ (- (- (log epsilon0) / epsilon0) * epsilon0))).
  rewrite /powR (eqr_nat R 2 0) /=.
  rewrite ltr_expR ltr_pM2r; last by apply/ln_gt0; rewrite (ltr_nat R 1 2).
  rewrite ltr_pM2r; first last.
  - by case: Hepsilon0.
  - rewrite -mulr_natr ltrN2 mul1r.
    by case: Hn => _ [].
rewrite !mulNr opprK -mulrA mulVr; last first.
  by case: Hepsilon0 => /lt0r_neq0; rewrite unitfE.
by rewrite mulr1 LogK ?lexx //; case: Hepsilon0.
Qed.

End random_coding_good_code_existence.

(* TODO: move to realType_logb *)
Lemma exists_frac_part (P : nat -> Prop) : (exists n, P n) ->
  forall num den, (0 < num)%nat -> (0 < den)%nat ->
  (forall n m, (n <= m)%nat -> P n -> P m) ->
  exists n, P n /\
    frac_part (2 `^ (n%:R * (log num%:R / den%:R))) = 0.
Proof.
case=> n Pn num den Hden HP.
exists (n * den)%nat.
split.
  apply H with n => //.
  by rewrite -{1}(muln1 n) leq_mul2l HP orbC.
rewrite natrM -mulrA (mulrCA den%:R) mulrV // ?mulr1; last first.
  by rewrite unitfE lt0r_neq0 // (ltr_nat R 0).
rewrite /frac_part mulrC powRrM.
rewrite (LogK (n:=2)) // ?ltr0n // powR_mulrn ?ler0n // -natrX.
by rewrite floorK ?subrr // intr_nat.
Qed.

Section channel_coding_theorem.
Variables (A B : finType) (W : `Ch(A, B)).
Hypothesis set_of_I_nonempty :
  classical_sets.nonempty (fun y => exists P, `I(P, W) = y).

Theorem channel_coding (r : CodeRateType) : rate r < capacity W ->
  forall epsilon, 0 < epsilon ->
    exists n M (c : code A B M n), CodeRate c = r /\ echa(W, c) < epsilon.
Proof.
move=> r_I epsilon Hepsilon.
have [P HP] : exists P : {fdist A}, rate r < `I(P, W).
  apply/not_existsP => abs.
  have {}abs : forall P : {fdist A}, `I(P, W) <= r.
    by move=> P; rewrite leNgt; apply/negP.
  have ? : capacity W <= r.
    have : has_sup [set `I(P, W) | P in [set: {fdist A}]].
      case: set_of_I_nonempty => [x [P H1]]; split; first by exists x, P.
      by exists (rate r) => _ [Q _ <-].
    move=> /(@Rsup_isLub 0 [set `I(P, W) | P in [set: {fdist A}]])[_].
    apply.
    by move=> x [P _ <-{x}].
  lra.
have [epsilon0 Hepsilon0] : exists epsilon0,
  0 < epsilon0 /\ epsilon0 < epsilon / 2 /\ epsilon0 < (`I(P, W) - rate r) / 4.
  exists ((Order.min (epsilon/2) ((`I(P, W) - rate r) / 4))/2).
  have H0 : 0 < Order.min (epsilon / 2) ((`I(P, W) - rate r) / 4).
    rewrite lt_min; lra.
  split; first by apply mulr_gt0 => //; lra.
  split; apply/(@lt_le_trans _ _ (Num.min (epsilon / 2) ((`I(P, W) - rate r) / 4))); try by rewrite ltr_pdivrMr // mulr_natr mulr2n ltr_pwDr.
    by rewrite ge_min lexx.
  by rewrite ge_min lexx orbT.
have [n Hn] : exists n, n_condition W P r epsilon0 n.
  destruct r as [r [num [den [Hnum [Hden Hr]]]]].
  have Hn : exists n, (0 < n)%nat /\
    - log epsilon0 / epsilon0 < n%:R /\
    (maxn (Nup (aep_bound P (epsilon0 / 3)))
    (maxn (Nup (aep_bound (`O(P , W)) (epsilon0 / 3)))
          (Nup (aep_bound ((P `X W)) (epsilon0 / 3)))) <= n)%nat.
    set supermax := maxn 1
      (maxn (Nup (- log epsilon0 / epsilon0))
         (maxn (Nup (aep_bound P (epsilon0 / 3)))
            (maxn (Nup (aep_bound (`O(P , W)) (epsilon0 / 3)))
               (Nup (aep_bound ((P `X W)) (epsilon0 / 3)))))).
    exists supermax.
    split; first by rewrite leq_max.
    split.
      apply (@lt_le_trans _ R (Num.floor (- log epsilon0 / epsilon0) + 1)%:~R).
        exact: lt_succ_floor.
      apply (@le_trans _ R (Nup (- log epsilon0 / epsilon0))%:R).
        by rewrite /Nup -addn1 -mulrz_nat natz PoszD ler_int lerD // lez_abs.
      by rewrite ler_nat /supermax 2!leq_max leqnn orbT.
    by rewrite [X in (_ <= X)%nat]maxnA leq_maxr.
  rewrite /n_condition.
  lapply (exists_frac_part Hn Hnum Hden); last move=> n1 n2 n1_n2 Pn1.
    case=> n [[Hn1 [Hn3 Hn4]] Hn2].
    exists n => /=.
    rewrite /n_condition.
    split => //; split => //; split => //.
    by rewrite -Hr mulr_natl in Hn2.
  split.
    by apply/(@leq_trans n1) => //; tauto.
  split.
    by apply: (@lt_le_trans _ _ n1%:R); [tauto | rewrite ler_nat].
  by apply leq_trans with n1 => //; tauto.
have He : (0 <= epsilon) by apply ltW.
case: (random_coding_good_code He Hepsilon0 Hn) =>
  M [HM [M_k H]].
case: (good_code_sufficient_condition H) => f Hf.
exists n, M, (mkCode f (jtdec P W epsilon0 f)); split => //.
rewrite /CodeRate M_k -mulrz_nat natz gez0_abs; last first.
  by rewrite floor_ge0 powR_ge0.
case: Hn => Hn [_] [].
rewrite /frac_part => /subr0_eq <- _.
rewrite /log ExpK // -(mulr_natr (rate r)) mulrK //.
by apply/unitf_gt0; rewrite ltr0n.
Qed.

End channel_coding_theorem.
