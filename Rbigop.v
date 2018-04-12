(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import Rssr Reals_ext log2 ssr_ext ssralg_ext.

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

Notation "\rmax_ ( i <- r | P ) F" := (\big[Rmax/R0]_(i <- r | P%B) F)
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \rmax_ ( i  <-  r  |  P ) '/  '  F ']'").
Notation "\rmax_ ( i <- r ) F" :=  (\big[Rmax/R0]_(i <- r) F)
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \rmax_ ( i  <-  r ) '/  '  F ']'").
Notation "\rmax_ ( i | P ) F" := (\big[Rmax/R0]_(i | P%B) F)
  (at level 41, F at level 41, i at level 50,
           format "'[' \rmax_ ( i  |  P ) '/  '  F ']'").
Notation "\rmax_ ( i : t | P ) F" := (\big[Rmax/R0]_(i : t | P%B) F)
  (at level 41, F at level 41, i at level 50,
           only parsing).
Notation "\rmax_ ( i : t ) F" := (\big[Rmax/R0]_(i : t) F)
  (at level 41, F at level 41, i at level 50,
           only parsing).
Notation "\rmax_ ( i 'in' A | P ) F" := (\big[Rmax/R0]_(i in A | P%B) F)
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \rmax_ ( i  'in'  A  |  P ) '/  '  F ']'").
Notation "\rmax_ ( i 'in' A ) F" := (\big[Rmax/R0]_(i in A) F)
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \rmax_ ( i  'in'  A ) '/  '  F ']'").
Reserved Notation "\min^ b '_(' a 'in' A ) F" (at level 41,
  F at level 41, a, A at level 50,
   format "'[' \min^ b '_(' a  'in'  A ) '/  '  F ']'").

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope reals_ext_scope.

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
Proof. move=> ? ? /=; by rewrite -ExpD. Qed.

Lemma iter_Rmax a b (Hb : b <= a) k : ssrnat.iter k (Rmax b) a = a.
Proof. elim: k => // k Hk; by rewrite iterS Hk Rmax_right. Qed.

(** Rle, Rlt lemmas for big sums of reals *)

Lemma rsum_setT (A : finType) (f : A -> R) (P : pred A) :
  \rsum_(i in A | P i) f i = \rsum_(i in [set: A] | P i) f i.
Proof. apply eq_bigl => x /=; by rewrite !inE. Qed.

Section ler_ltr_rsum.

Variables (A : finType) (f g : A -> R) (P Q : pred A).

Lemma ler_rsum_support (X : {set A}) :
  (forall i, i \in X -> P i -> f i <= g i) ->
  \rsum_(i in X | P i) f i <= \rsum_(i in X | P i) g i.
Proof.
move=> H.
elim: (index_enum _) => [|h t IH].
- rewrite !big_nil; exact/Rle_refl.
- rewrite !big_cons.
  set K := _ && _; move HK : K => []; subst K => //.
  apply Rplus_le_compat => //.
  case/andP : HK; exact: H.
Qed.

Lemma ler_rsum : (forall i, P i -> f i <= g i) ->
  \rsum_(i | P i) f i <= \rsum_(i | P i) g i.
Proof.
move=> H; rewrite rsum_setT [in X in _ <= X]rsum_setT.
apply ler_rsum_support => a _; exact: H.
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

Lemma ltR_rsum : (O < #|A|)%nat -> (forall i, f i < g i) ->
  \rsum_(i in A) f i < \rsum_(i in A) g i.
Proof.
move=> A0 H0.
have : forall i : A, i \in [set: A] -> f i < g i by move=> a _; exact/H0.
move/ltr_rsum_support; rewrite cardsT => /(_ A0).
rewrite big_mkcond /= [in X in _ < X]big_mkcond /=.
rewrite (eq_bigr f) //; last by move=> *; rewrite inE.
rewrite [in X in _ < X](eq_bigr g) //; by move=> *; rewrite inE.
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
    apply/RltP; rewrite lt0R Hf /=; exact/RleP.
  apply (Rmult_le_reg_r (1 * / \rprod_(i : A) f i) _ _).
    apply Rlt_mult_inv_pos => //; fourier.
  rewrite mul1R mulRV; last exact/eqP/not_eq_sym/Rlt_not_eq.
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
        rewrite -mulRA mul0R mulRV // ?mulR1; move/eqP; exact/negP.
      rewrite invRM //; exact/eqP.
    - rewrite negb_and !negbK => /orP[|]/eqP ->;
        by rewrite /inv_spec !(eqxx,mul0R,mulR0).
  - rewrite /inv_spec ifF ?invR1 //; exact/negbTE/eqP/R1_neq_R0.
  rewrite -big_split /=.
  apply rprodr_ge1 => a.
  move/(_ a) in Hf.
  move: Hfg => /(_ a) [Hf2 Hfg].
  rewrite /inv_spec.
  move/negbTE in Hf; rewrite Hf; move/negbT in Hf.
  rewrite -(mulRV (f a)) //.
  apply Rmult_le_compat_r => //.
  rewrite -(mul1R (/ f a)).
  apply Rle_mult_inv_pos; [fourier | apply/RltP; rewrite lt0R Hf; exact/RleP].
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

(* TODO: rename *)
Lemma log_rmul_rsum_mlog {A : finType} k (f : A -> R+) : forall n (ta : 'rV[A]_n.+1),
  (forall i, 0 < f ta ``_ i) ->
  (- Log k (\rprod_(i < n.+1) f ta ``_ i) = \rsum_(i < n.+1) - Log k (f ta ``_ i))%R.
Proof.
elim => [i Hi | n IH].
  by rewrite big_ord_recl big_ord0 mulR1 big_ord_recl big_ord0 addR0.
move=> ta Hi.
rewrite big_ord_recl /= LogM; last 2 first.
  exact/Hi.
  apply rprodr_gt0 => ?; exact/Hi.
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

Section bigrmax_sect.

Variables (A : eqType) (F : A -> R) (s : seq A).

Lemma Rle_bigRmax : forall m, m \in s -> F m <= \rmax_(m <- s) (F m).
Proof.
elim: s => // hd tl IH m; rewrite in_cons; case/orP.
- move/eqP => ->; rewrite big_cons; by apply Rmax_l.
- move/IH => H; rewrite big_cons.
  eapply Rle_trans; by [apply H | apply Rmax_r].
Qed.

Lemma Rle_0_bigRmax : (forall r, r \in s -> 0 <= F r) -> 0 <= \rmax_(m <- s) (F m).
Proof.
case: s => [_ | hd tl Hr].
- rewrite big_nil; by apply Rle_refl.
- apply Rle_trans with (F hd); last by rewrite big_cons; apply Rmax_l.
  apply Hr; by rewrite in_cons eqxx.
Qed.

End bigrmax_sect.

Lemma bigrmax_undup (I : eqType) g : forall (s : seq I),
   \rmax_(c <- s) g c = \rmax_(c <- undup s) g c.
Proof.
elim=> // hd tl IH /=.
rewrite big_cons.
case: ifP => Hcase.
- rewrite -IH Rmax_right //; by apply Rle_bigRmax.
- by rewrite big_cons IH.
Qed.

Lemma bigrmax_cat (I : eqType) g : forall (s1 s2 : seq I),
  (forall x, x \in s1 ++ s2 -> 0 <= g x) ->
  \rmax_(c <- s1 ++ s2) g c = Rmax (\rmax_(c <- s1) g c) (\rmax_(c <- s2) g c).
Proof.
elim => [s2 Hg /= | h1 t1 IH s2 Hg /=].
  rewrite big_nil Rmax_right //.
  by apply Rle_0_bigRmax.
rewrite 2!big_cons IH ?maxRA //.
move=> x Hx; apply Hg.
by rewrite /= in_cons Hx orbC.
Qed.

Lemma bigrmax_perm (I : eqType) g : forall (s1 s2 : seq I),
  (forall r, r \in s2 -> 0 <= g r) ->
  perm_eq s1 s2 -> uniq s1 -> uniq s2 ->
  \rmax_(c0 <- s1) g c0 = \rmax_(c0 <- s2) g c0.
Proof.
move=> s1.
move H : (size s1) => n1.
elim: n1 s1 H => //.
  case=> // _ s _ Hs.
  suff -> : s = [::].
    move=> _ _; by rewrite !big_nil.
  destruct s => //.
  move/allP : Hs.
  move/(_ s).
  by rewrite /= inE eqxx /= => /(_ Logic.eq_refl) /= add1n.
move=> n1 IH1 [|h1 t1] // [] H1 s2 Hg Hs2 K1 K2.
rewrite big_cons.
have [h2 [t2 ht2]] : exists h2 t2, s2 = h2 ++ h1 :: t2.
  apply in_cat; by rewrite -(perm_eq_mem Hs2) in_cons eqxx.
have Hs2' : perm_eq t1 (h2 ++ t2).
  rewrite ht2 in Hs2.
  rewrite -(perm_cons h1).
  eapply perm_eq_trans; first by apply Hs2.
  by rewrite perm_catC /= perm_cons perm_catC.
have Hg' r : r \in h2 ++ t2 -> 0 <= g r.
  move=> rs2; apply Hg.
  rewrite ht2 mem_cat in_cons.
  rewrite mem_cat in rs2.
  case/orP : rs2 => [-> // | -> /=].
  by rewrite orbA orbC.
rewrite (IH1 _ H1 _ Hg' Hs2'); last 2 first.
  by case/andP : K1.
  rewrite ht2 cat_uniq /= in K2.
  case/andP : K2 => K2 /andP [] K4 /andP [] _ K3.
  rewrite cat_uniq K2 K3 /= andbC /=.
  rewrite negb_or in K4.
  by case/andP : K4.
rewrite bigrmax_cat // maxRA (maxRC (g h1)) -maxRA ht2 bigrmax_cat; last first.
  move=> x Hx; apply Hg; by rewrite ht2.
by rewrite big_cons.
Qed.

Lemma bigrmax_eqi (I : finType) g : forall (s1 s2 : seq I),
  (forall r : I, r \in s1 -> 0 <= g r) -> s1 =i s2 ->
  \rmax_(c0 <- s1) g c0 = \rmax_(c0 <- s2) g c0.
Proof.
move=> s1 s2 Hg s1s2.
rewrite (bigrmax_undup _ s1) (bigrmax_undup g s2).
apply bigrmax_perm; [ | | by rewrite undup_uniq | by rewrite undup_uniq].
- move=> r Hr; apply Hg.
  rewrite mem_undup in Hr.
  by rewrite s1s2.
- apply uniq_perm_eq; [by rewrite undup_uniq | by rewrite undup_uniq | ].
  move=> i; by rewrite !mem_undup.
Qed.

Lemma rmax_imset' {M : finType} (I : finType) h (g : I -> R) (s : seq M) :
  (forall r : I, r \in enum [set h x | x in s] -> 0 <= g r) ->
  \rmax_(c0 <- enum [set h x | x in s]) g c0 = \rmax_(m <- s) g (h m).
Proof.
elim: s.
  rewrite big_nil.
  set tmp := enum _.
  suff -> : tmp = [::] by rewrite big_nil.
  rewrite /tmp -[in X in _ = X]enum0.
  apply eq_enum => a.
  rewrite !inE.
  apply/imsetP. case => m.
  by rewrite in_nil.
move=> hd tl IH Hg /=.
rewrite big_cons -IH; last first.
  move=> r Hr.
  apply Hg.
  rewrite mem_enum.
  apply/imsetP.
  rewrite mem_enum in Hr.
  case/imsetP : Hr => x xtl Hr.
  exists x => //.
  by rewrite in_cons xtl orbC.
transitivity (\rmax_(c0 <- h hd :: enum [set h x | x in tl]) g c0).
apply bigrmax_eqi => // x.
rewrite inE !mem_enum.
move Hlhs : (x \in [set _ _ | _ in _]) => lhs.
destruct lhs.
  - case/imsetP : Hlhs => x0 Hx0 H.
    rewrite in_cons in Hx0.
    case/orP : Hx0 => Hx0.
      move/eqP : Hx0 => ?; subst x0.
      by rewrite H eqxx.
    symmetry.
    apply/orP; right.
    apply/imsetP; by exists x0.
  - symmetry.
    apply/negbTE.
    move/negbT : Hlhs.
    apply contra.
    case/orP => Hcase.
    + move/eqP in Hcase; subst x.
      apply/imsetP.
      exists hd => //.
      by rewrite inE eqxx.
    + apply/imsetP.
      case/imsetP : Hcase => x0 Hx0 ?; subst x.
      exists x0 => //.
      by rewrite inE Hx0 orbC.
by rewrite big_cons.
Qed.

Lemma rmax_imset {M : finType} (I : finType) h (g : I -> R) :
  (forall r : I, r \in [set h x | x in M] -> 0 <= g r) ->
  \rmax_(c0 in [set h x | x in M]) g c0 = \rmax_(m in M) g (h m).
Proof.
move=> Hg.
eapply trans_eq.
  eapply trans_eq; last first.
    apply (@rmax_imset' _ I h g (enum M)).
    move=> r; rewrite mem_enum; case/imsetP => x; rewrite mem_enum => Hx ->.
    apply Hg; apply/imsetP; by exists x.
  rewrite big_filter /=.
  apply congr_big => //.
  move=> i /=.
  move Hlhs : (i \in _) => lhs.
  destruct lhs.
  - case/imsetP : Hlhs => x Hx ?; subst i.
    symmetry; apply/imsetP.
    exists x => //.
    by rewrite mem_enum.
  - symmetry.
    apply/negbTE.
    move/negbT : Hlhs; apply contra.
    case/imsetP => m Hm ?; subst i.
    apply/imsetP.
    by exists m.
apply congr_big => //; by rewrite enumT.
Qed.

Lemma Rle_bigrmax_R {A : finType} (h : A -> R) (tl : seq A) hd :
  (forall r, 0 <= h r) ->
  (forall c : A, c \in tl -> h c <= h hd) ->
  \rmax_(j <- tl) h j <= h hd.
Proof.
elim: tl hd => [hd Hh _ | hd1 tl2 IH hd Hhpos Hh].
  rewrite big_nil; by apply Hh.
rewrite big_cons.
apply Rmax_lub.
- apply Hh.
  by rewrite in_cons eqxx.
- apply IH => // c0 Hc0; apply Hh.
  by rewrite in_cons Hc0 orbC.
Qed.

Lemma bigrmax_max_seq {A : finType} (h : A -> R) (s : seq A) a :
  a \in s ->
  (forall r, 0 <= h r) ->
  (forall c, c \in s -> h c <= h a) ->
  h a = \rmax_(c <- s) h c.
Proof.
elim: s a => // hd tl IH a; rewrite in_cons; case/orP.
- move/eqP => -> Hhpos Hh.
  rewrite big_cons.
  rewrite Rmax_left //.
  apply Rle_bigrmax_R => //.
  move=> c0 Hc0; apply Hh.
  by rewrite in_cons Hc0 orbC.
- move=> atl Hhpos Hh.
  rewrite big_cons Rmax_right //.
  + apply IH => //.
    move=> c0 Hc0; apply Hh.
    by rewrite in_cons Hc0 orbC.
  + rewrite -(IH a) //.
    * apply Hh.
      by rewrite in_cons eqxx.
    * move=> c0 Hc0.
      apply Hh.
      by rewrite in_cons Hc0 orbC.
Qed.

Lemma bigrmax_max {A : finType} (C : {set A}) a (h : A -> R):
  a \in C ->
  (forall r, 0 <= h r) ->
  (forall c, c \in C -> h c <= h a) ->
  h a = \rmax_(c | c \in C) h c.
Proof.
move=> aC Hhpos Hh.
rewrite -big_filter.
apply bigrmax_max_seq => //.
- by rewrite mem_filter aC /= mem_index_enum.
- move=> c0.
  rewrite mem_filter.
  case/andP => ? ?.
  by apply Hh.
Qed.

Local Open Scope R_scope.

Lemma rmax_distrr I a (apos: 0 <= a) r (Q:pred I) F :
  ((a * \rmax_(i <- r | Q i) F i) = \rmax_(i <- r | Q i) (a * F i)).
Proof.
elim: r => [| h t IH].
  by rewrite 2!big_nil mulR0.
rewrite 2!big_cons.
case: ifP => Qh //.
by rewrite -IH RmaxRmult.
Qed.

Lemma rmax_distrl I a (apos: 0 <= a) r (Q:pred I) F :
  ((\rmax_(i <- r | Q i) F i) * a = \rmax_(i <- r | Q i) (F i * a)).
Proof.
rewrite mulRC rmax_distrr //.
by apply congr_big; auto using mulRC.
Qed.

Notation "\min^ b '_(' a 'in' A ) F" :=
((fun a => F) (arg_min b (fun x => x \in A) (fun a => F))) : min_scope.

Local Open Scope min_scope.

Lemma bigminn_min {A : finType} (C : {set A}) (cnot0 : {c0 | c0 \in C}) a (Ha : a \in C) (h : A -> nat) :
  (\min^ (sval cnot0) _(c in C) h c <= h a)%nat.
Proof.
case: arg_minP.
by destruct cnot0.
move=> a0 a0C H.
by apply H.
Qed.

(* TODO: useless ? *)
Lemma big_rmax_bigminn_helper {A : finType} n (g : nat -> R) :
  (forall n1 n2, (n1 <= n2 <= n)%nat -> (g n2 <= g n1)%R) ->
  (forall r, 0 <= g r) ->
  forall (C : {set n.-tuple A}) c'' (_ : c'' \in C) (d : n.-tuple A -> nat)
  (_ : forall c, c \in C -> (d c <= n)%nat)
  (cnot0 : {c0 | c0 \in C}),
  d c'' = \min^ (sval cnot0) _(c in C) d c ->
  g (d c'') = \rmax_(c in C) g (d c).
Proof.
move=> Hdecr Hr C c'' Hcc' d Hd cnot0 H.
apply (@bigrmax_max _ C c'' (fun a => g (d a))) => //.
move=> /= c0 c0C.
apply Hdecr.
apply/andP; split.
  rewrite H.
  by apply bigminn_min.
by apply Hd.
Qed.

Lemma big_rmax_bigminn {A M : finType} n (f : {ffun M -> n.-tuple A}) (g : nat -> R)
  (cnot0 : {c0 | c0 \in f @: M } ) :
  (forall n1 n2, (n1 <= n2 <= n)%nat -> (g n2 <= g n1)%R) ->
  (forall r, 0 <= g r) ->
  forall m'' (d : n.-tuple A -> nat)
  (_ : forall c0 : n.-tuple A, c0 \in [set f x | x : M] -> (d c0 <= n)%nat),
  d (f m'') = \min^ (sval cnot0) _(c in [set f x | x in M]) d c ->
  g (d (f m'')) = \rmax_(m | m \in M) g (d (f m)).
Proof.
move=> n1n2 Hg m'' d H Hd.
transitivity (\rmax_(c in [set f x | x in M]) g (d c)); last by rewrite rmax_imset.
apply big_rmax_bigminn_helper with cnot0 => //.
apply/imsetP.
by exists m''.
Qed.

Lemma big_rmax_bigminn_helper_vec {A : finType} n (g : nat -> R) :
  (forall n1 n2, (n1 <= n2 <= n)%nat -> (g n2 <= g n1)%R) ->
  (forall r, 0 <= g r) ->
  forall (C : {set 'rV[A]_n}) c'' (_ : c'' \in C) (d : 'rV[A]_n -> nat)
  (_ : forall c, c \in C -> (d c <= n)%nat)
  (cnot0 : {c0 | c0 \in C}),
  d c'' = \min^ (sval cnot0) _(c in C) d c ->
  g (d c'') = \rmax_(c in C) g (d c).
Proof.
move=> Hdecr Hr C c'' Hcc' d Hd cnot0 H.
apply (@bigrmax_max _ C c'' (fun a => g (d a))) => //.
move=> /= c0 c0C.
apply Hdecr.
apply/andP; split.
  rewrite H.
  by apply bigminn_min.
by apply Hd.
Qed.

Lemma big_rmax_bigminn_vec {A M : finType} n (f : {ffun M -> 'rV[A]_n}) (g : nat -> R)
  (cnot0 : {c0 | c0 \in f @: M } ) :
  (forall n1 n2, (n1 <= n2 <= n)%nat -> (g n2 <= g n1)%R) ->
  (forall r, 0 <= g r) ->
  forall m'' (d : 'rV[A]_n -> nat)
  (_ : forall c0 : 'rV[A]_n, c0 \in f @: M -> (d c0 <= n)%nat),
  d (f m'') = \min^ (sval cnot0) _(c in f @: M) d c ->
  g (d (f m'')) = \rmax_(m in M) g (d (f m)).
Proof.
move=> n1n2 Hg m'' d H Hd.
transitivity (\rmax_(c in f @: M) g (d c)); last by rewrite rmax_imset.
apply big_rmax_bigminn_helper_vec with cnot0 => //.
apply/imsetP.
by exists m''.
Qed.
