(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix.
From mathcomp Require Import Rstruct.
Require Import Reals Lra.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext.

(******************************************************************************)
(*    Instantiation of MathComp's canonical big operators with Coq reals      *)
(*                                                                            *)
(* Various lemmas for iterated sum, prod, and max                             *)
(*                                                                            *)
(******************************************************************************)

Notation "\sum_ ( i <- r | P ) F" := (\big[Rplus/R0]_(i <- r | P%B) F)
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \sum_ ( i  <-  r  |  P ) '/  '  F ']'") : R_scope.
Notation "\sum_ ( i <- r ) F" :=  (\big[Rplus/R0]_(i <- r) F)
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \sum_ ( i  <-  r ) '/  '  F ']'") : R_scope.
Notation "\sum_ ( m <= i < n | P ) F" := (\big[Rplus/R0]_(m <= i < n | P%B) F)
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \sum_ ( m  <=  i  <  n  |  P ) '/  '  F ']'") : R_scope.
Notation "\sum_ ( m <= i < n ) F" := (\big[Rplus/R0]_(m <= i < n) F)
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \sum_ ( m  <=  i  <  n ) '/  '  F ']'") : R_scope.
Notation "\sum_ ( i | P ) F" := (\big[Rplus/R0]_(i | P%B) F)
  (at level 41, F at level 41, i at level 50,
           format "'[' \sum_ ( i  |  P ) '/  '  F ']'") : R_scope .
Notation "\sum_ i F" := (\big[Rplus/R0]_i F)
  (at level 41, F at level 41, i at level 0, right associativity,
  format "'[' \sum_ i '/  '  F ']'") : R_scope.
Notation "\sum_ ( i : t | P ) F" := (\big[Rplus/R0]_(i : t | P%B) F)
  (at level 41, F at level 41, i at level 50,
           only parsing) : R_scope.
Notation "\sum_ ( i : t ) F" := (\big[Rplus/R0]_(i : t) F)
  (at level 41, F at level 41, i at level 50,
           only parsing) : R_scope.
Notation "\sum_ ( i < n | P ) F" := (\big[Rplus/R0]_(i < n | P%B) F)
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \sum_ ( i  <  n  |  P ) '/  '  F ']'") : R_scope.
Notation "\sum_ ( i < n ) F" := (\big[Rplus/R0]_(i < n) F)
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \sum_ ( i  <  n ) '/  '  F ']'") : R_scope.
Notation "\sum_ ( i 'in' A | P ) F" := (\big[Rplus/R0]_(i in A | P%B) F)
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \sum_ ( i  'in'  A  |  P ) '/  '  F ']'") : R_scope.
Notation "\sum_ ( i 'in' A ) F" := (\big[Rplus/R0]_(i in A) F)
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \sum_ ( i  'in'  A ) '/  '  F ']'") : R_scope.

Notation "\prod_ ( i <- r | P ) F" := (\big[Rmult/R1]_(i <- r | P%B) F)
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \prod_ ( i  <-  r  |  P ) '/  '  F ']'") : R_scope.
Notation "\prod_ ( i <- r ) F" :=  (\big[Rmult/R1]_(i <- r) F)
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \prod_ ( i  <-  r ) '/  '  F ']'") : R_scope.
Notation "\prod_ ( m <= i < n | P ) F" := (\big[Rmult/R1]_(m <= i < n | P%B) F)
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \prod_ ( m  <=  i  <  n  |  P ) '/  '  F ']'") : R_scope.
Notation "\prod_ ( m <= i < n ) F" := (\big[Rmult/R1]_(m <= i < n) F)
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \prod_ ( m  <=  i  <  n ) '/  '  F ']'") : R_scope.
Notation "\prod_ ( i | P ) F" := (\big[Rmult/R1]_(i | P%B) F)
  (at level 36, F at level 36, i at level 50,
           format "'[' \prod_ ( i  |  P ) '/  '  F ']'") : R_scope.
Notation "\prod_ i F" := (\big[Rmult/R1]_i F)
  (at level 36, F at level 36, i at level 0,
  format "'[' \prod_ i '/  '  F ']'") : R_scope.
Notation "\prod_ ( i : t | P ) F" := (\big[Rmult/R1]_(i : t | P%B) F)
  (at level 36, F at level 36, i at level 50,
           only parsing) : R_scope.
Notation "\prod_ ( i : t ) F" := (\big[Rmult/R1]_(i : t) F)
  (at level 36, F at level 36, i at level 50,
           only parsing) : R_scope.
Notation "\prod_ ( i < n | P ) F" := (\big[Rmult/R1]_(i < n | P%B) F)
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \prod_ ( i  <  n  |  P ) '/  '  F ']'") : R_scope.
Notation "\prod_ ( i < n ) F" := (\big[Rmult/R1]_(i < n) F)
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \prod_ ( i  <  n ) '/  '  F ']'") : R_scope.
Notation "\prod_ ( i 'in' A | P ) F" := (\big[Rmult/R1]_(i in A | P%B) F)
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \prod_ ( i  'in'  A  |  P ) '/  '  F ']'") : R_scope.
Notation "\prod_ ( i 'in' A ) F" := (\big[Rmult/R1]_(i in A) F)
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \prod_ ( i  'in'  A ) '/  '  F ']'") : R_scope.

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

Declare Scope min_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import Num.Theory.

Local Open Scope R_scope.
Local Open Scope reals_ext_scope.

Canonical addR_monoid := Monoid.Law addRA add0R addR0.
Canonical addR_comoid := Monoid.ComLaw addRC.
Canonical mulR_monoid := Monoid.Law mulRA mul1R mulR1.
Canonical mulR_muloid := Monoid.MulLaw mul0R mulR0.
Canonical mulR_comoid := Monoid.ComLaw mulRC.
Canonical addR_addoid := Monoid.AddLaw mulRDl mulRDr.

Lemma morph_oppR : {morph [eta Ropp] : x y / x + y}.
Proof. by move=> x y /=; field. Qed.

Definition big_morph_oppR := big_morph _ morph_oppR oppR0.

Lemma morph_natRD : {morph INR : x y / (x + y)%nat >-> x + y}.
Proof. move=> x y /=; by rewrite natRD. Qed.

Definition big_morph_natRD := big_morph INR morph_natRD (erefl 0%:R).

Lemma morph_natRM : {morph INR : x y / (x * y)%nat >-> x * y}.
Proof. move=> x y /=; by rewrite natRM. Qed.

Definition big_morph_natRM := big_morph INR morph_natRM (erefl 1%:R).

Lemma morph_mulRDr a : {morph [eta Rmult a] : x y / x + y}.
Proof. move=> * /=; by rewrite mulRDr. Qed.

Lemma morph_mulRDl a : {morph Rmult^~ a : x y / x + y}.
Proof. move=> x y /=; by rewrite mulRDl. Qed.

Lemma morph_exp2_plus : {morph [eta exp2] : x y / x + y >-> x * y}.
Proof. move=> ? ? /=; by rewrite -ExpD. Qed.

Lemma iter_Rmax a b (Hb : b <= a) k : ssrnat.iter k (Rmax b) a = a.
Proof. elim: k => // k Hk; by rewrite iterS Hk Rmax_right. Qed.

(** Rle, Rlt lemmas for big sums of reals *)

Lemma sumR_ord_setT (n : nat) (f : 'I_n -> R) :
  \sum_(i < n) f i = \sum_(i in [set: 'I_n]) f i.
Proof. by apply eq_bigl => i; rewrite inE. Qed.

Lemma sumR_ge0 (A : eqType) (d : seq A) (P : pred A) f
  (H : forall i, P i -> 0 <= f i) : 0 <= \sum_(i <- d | P i) f i.
Proof.
elim: d => [|h t IH]; first by rewrite big_nil; exact/leRR.
rewrite big_cons; case: ifPn => // Ph; apply/addR_ge0 => //; exact: H.
Qed.

Lemma sumR_neq0 (U : eqType) (P : U -> R) (s : seq.seq U) :
  (forall i, 0 <= P i) ->
  \sum_(a0 <- s) P a0 != 0 <-> exists i : U, i \in s /\ 0 < P i.
Proof.
move=> P0; elim: s => [|]; first by rewrite big_nil eqxx; split => // -[] u [].
move=> h t ih; rewrite big_cons; have [Ph0|Ph0] := boolP (P h == 0).
  rewrite (eqP Ph0) add0R; split.
    by move/ih => [u [ut Pu0]]; exists u; split => //; rewrite inE ut orbT.
  move=> [u []]; rewrite inE => /orP[/eqP ->|ut Pu0]; last by apply/ih; exists u.
  by rewrite (eqP Ph0) => /ltRR.
split=> _.
  exists h; rewrite inE eqxx /=; split => //.
  by rewrite ltR_neqAle; split; [exact/nesym/eqP|exact: P0].
by apply/paddR_neq0 => //; [apply sumR_ge0 => u _; exact: P0 | left].
Qed.

Lemma sumR_gt0 (A : finType) (f : A -> R) (HA : (0 < #|A|)%nat) :
  (forall a, 0 < f a) -> 0 < \sum_(a in A) f a.
Proof.
move=> f0; rewrite ltR_neqAle; split; last by apply sumR_ge0 => a _; apply/ltRW.
apply/nesym/eqP/sumR_neq0; last by move/card_gt0P : HA => [a _]; exists a.
by move=> a; apply/ltRW/f0.
Qed.

Lemma psumR_seq_eq0P (A : eqType) (l : seq A) f :
  uniq l ->
  (forall a, a \in l -> 0 <= f a) ->
  \sum_(a <- l) f a = 0 <-> (forall a, a \in l -> f a = 0).
Proof.
move=> ul Hf; split=> [H a al|h]; last first.
  by rewrite (eq_big_seq (fun=> 0)) ?big1.
suff : f a = 0 /\ \sum_(i <- l|i != a) f i = 0 by case.
apply: Rplus_eq_R0.
- exact/Hf.
- by rewrite big_seq_cond; apply: sumR_ge0 => ? /andP[? ?]; apply Hf.
- by rewrite -bigD1_seq.
Qed.

Lemma psumR_eq0P (A : finType) (P : pred A) f :
  (forall a, P a -> 0 <= f a) ->
  \sum_(a | P a) f a = 0 <-> (forall a, P a -> f a = 0).
Proof.
move=> Hf; split=> [H a Ha|h]; last first.
  by rewrite (eq_bigr (fun=> 0)) // big_const iter_addR mulR0.
suff : f a = 0 /\ \sum_(i | P i && (i != a)) f i = 0 by case.
apply: Rplus_eq_R0.
- exact/Hf/Ha.
- apply: sumR_ge0 => ? /andP[? ?]; by apply Hf.
- rewrite -bigD1 /=; [exact H | exact Ha].
Qed.

Section leR_ltR_sumR.
Variable A : Type.
Implicit Types (f g : A -> R) (P Q : pred A).

Lemma leR_sumR r P f g : (forall i, P i -> f i <= g i) ->
  \sum_(i <- r | P i) f i <= \sum_(i <- r | P i) g i.
Proof.
move=> leE12.
elim/big_ind2: _ => //.
  exact: Rle_refl.
by move=> m1 m2 n1 n2; lra.
Qed.

End leR_ltR_sumR.

Section leR_ltR_sumR_finType.
Variables (A : finType) (f g : A -> R) (P Q : pred A).

Lemma leR_sumR_support (X : {set A}) :
  (forall i, i \in X -> P i -> f i <= g i) ->
  \sum_(i in X | P i) f i <= \sum_(i in X | P i) g i.
Proof.
move=> H; elim/big_rec2 : _ => //.
  exact: Rle_refl.
move=> a x y /andP[aX Pa] yx.
by apply leR_add => //; apply: H.
Qed.

Lemma leR_sumRl : (forall i, P i -> f i <= g i) ->
  (forall i, Q i -> 0 <= g i) -> (forall i, P i -> Q i) ->
  \sum_(i | P i) f i <= \sum_(i | Q i) g i.
Proof.
move=> f_g Qg H; elim: (index_enum _) => [| h t IH].
- by rewrite !big_nil; exact/leRR.
- rewrite !big_cons /=; case: ifP => [Ph|Ph].
    by rewrite (H _ Ph); apply leR_add => //; exact: f_g.
  case: ifP => // Qh; apply: (leR_trans IH).
  by rewrite -{1}[X in X <= _](add0R _); exact/leR_add2r/Qg.
Qed.

Lemma leR_sumRl_support (U : pred A) :
  (forall a, 0 <= f a) -> (forall i, P i -> Q i) ->
  \sum_(i in U | P i) f i <= \sum_(i in U | Q i) f i.
Proof.
move=> Hf P_Q; elim: (index_enum _) => [|h t IH].
- by rewrite !big_nil; exact/leRR.
- rewrite !big_cons; case: (h \in U) => //=; case: ifP => // Ph.
  + by case: ifP => [Qh|]; [rewrite leR_add2l | rewrite (P_Q _ Ph)].
  + by case: ifP => // Qh; rewrite -[X in X <= _]add0R; exact/leR_add.
Qed.

Lemma ltR_sumR_support (X : {set A}) : (0 < #|X|)%nat ->
  (forall i, i \in X -> f i < g i) ->
  \sum_(i in X) f i < \sum_(i in X) g i.
Proof.
move Hn : #|X| => n; elim: n X Hn => // n IH X Hn _ H.
move: (ltn0Sn n); rewrite -Hn card_gt0; case/set0Pn => a0 Ha0.
rewrite (@big_setD1 _ _ _ _ a0 _ f) //= (@big_setD1 _ _ _ _ a0 _ g) //=.
case: n => [|n] in IH Hn.
  rewrite (_ : X :\ a0 = set0); first by rewrite !big_set0 2!addR0; exact: H.
  move: Hn.
  by rewrite (cardsD1 a0) Ha0 /= add1n => -[] /eqP; rewrite cards_eq0 => /eqP.
apply ltR_add; first exact/H.
apply IH => //.
- by move: Hn; rewrite (cardsD1 a0) Ha0 /= add1n => -[].
- by move=> a; rewrite in_setD inE => /andP[_ ?]; exact: H.
Qed.

Lemma ltR_sumR : (O < #|A|)%nat -> (forall i, f i < g i) ->
  \sum_(i in A) f i < \sum_(i in A) g i.
Proof.
move=> A0 H0.
have : forall i : A, i \in [set: A] -> f i < g i by move=> a _; exact/H0.
move/ltR_sumR_support; rewrite cardsT => /(_ A0).
rewrite big_mkcond /= [in X in _ < X]big_mkcond /=.
rewrite (eq_bigr f) //; last by move=> *; rewrite inE.
by rewrite [in X in _ < X](eq_bigr g) // => *; rewrite inE.
Qed.

End leR_ltR_sumR_finType.

Lemma leR_sumR_Rabs (A : finType) f : `| \sum_a f a | <= \sum_(a : A) `| f a |.
Proof.
elim: (index_enum _) => [|h t IH].
  rewrite 2!big_nil Rabs_R0; exact/leRR.
rewrite 2!big_cons.
apply (@leR_trans (`| f h | + `| \sum_(j <- t) f j |));
  [exact/Rabs_triang |exact/leR_add2l].
Qed.

Lemma leR_sumR_predU (A : finType) (f : A -> R) (P Q : pred A) :
  (forall a, 0 <= f a) -> \sum_(i in A | [predU P & Q] i) f i <=
  \sum_(i in A | P i) f i + \sum_(i in A | Q i) f i.
Proof.
move=> Hf.
elim: (index_enum _) => [|h t IH /=]; first by rewrite !big_nil /=; lra.
rewrite !big_cons /=.
case: ifPn => /=.
- case/orP => [hP | hQ].
  + move: hP; rewrite unfold_in => ->.
    case: ifP => // Qh.
    * rewrite -addRA; apply leR_add2l.
      apply (leR_trans IH).
      have : forall a b c, 0 <= c -> a + b <= a + (c + b) by move=> *; lra.
      apply; by apply Hf.
    * rewrite -addRA; apply leR_add2l.
      exact/(leR_trans IH)/Req_le.
  + move: hQ; rewrite unfold_in => ->.
    case: ifP => // Ph.
    * rewrite -addRA; apply/leR_add2l/(leR_trans IH).
      have : forall a b c, 0 <= c -> a + b <= a + (c + b) by move=> *; lra.
      apply; by apply Hf.
    * rewrite -(addRC (f h + _)) -addRA; apply/leR_add2l/(leR_trans IH).
      by rewrite addRC; apply Req_le.
- rewrite negb_or.
  case/andP.
  rewrite !unfold_in; move/negbTE => -> /negbTE ->.
  exact/IH.
Qed.

Lemma classify_big (A : finType) n (f : A -> 'I_n) (F : 'I_n -> R) :
  \sum_a F (f a) = \sum_(i < n) INR #|f @^-1: [set i]| * F i.
Proof.
transitivity (\sum_(i < n) \sum_(a | true && (f a == i)) F (f a)).
  by apply partition_big.
apply eq_bigr => i _ /=.
transitivity (\sum_(a | f a == i) F i); first by apply eq_bigr => s /eqP ->.
rewrite big_const iter_addR; congr (INR _ * _).
apply eq_card => j /=; by rewrite !inE.
Qed.

(* TODO: factorize? rename? *)
Lemma leR_sumR_eq (A : finType) (f g : A -> R) (P : pred A) :
   (forall a, P a -> f a <= g a) ->
   \sum_(a | P a) g a = \sum_(a | P a) f a ->
   (forall a, P a -> g a = f a).
Proof.
move=> H1 H2 i Hi; rewrite -subR_eq0; move: i Hi; apply psumR_eq0P.
- move=> i Hi; rewrite leR_subr_addr add0R; exact: H1.
- by rewrite big_split /= -big_morph_oppR subR_eq0 H2.
Qed.

Section pascal.

Lemma sum_f_R0_sumR : forall n (f : nat -> R),
  sum_f_R0 f n = \sum_(i < n.+1) f i.
Proof.
elim => [f|n IH f] /=; first by rewrite big_ord_recl /= big_ord0 addR0.
by rewrite big_ord_recr /= IH.
Qed.

Theorem RPascal k (a b : R) :
  (a + b) ^ k = \sum_(i < k.+1) INR ('C(k, i))* (a ^ (k - i) * b ^ i).
Proof.
rewrite addRC Binomial.binomial sum_f_R0_sumR.
apply eq_bigr => i _.
rewrite combinaisonE; last by rewrite -ltnS.
rewrite -minusE; field.
Qed.

End pascal.

Section leR_ltR_rprod.

(*Lemma prodR_gt0 (A : finType) F : (forall a, 0 < F a) ->
  0 < \prod_(a : A) F a.
Proof. by move=> F0; elim/big_ind : _ => // x y ? ?; exact: mulR_gt0. Qed.*)

Lemma prodR_ge0 (A : finType) F : (forall a, 0 <= F a) ->
  0 <= \prod_(a : A) F a.
Proof. by move=> F0; elim/big_ind : _ => // x y ? ?; exact: mulR_ge0. Qed.

Lemma prodR_eq0 (A : finType) (p : pred A) (F : A -> R) :
  (exists2 i : A, p i & F i = 0%R) <-> \prod_(i : A | p i) F i = 0%R.
Proof.
split.
{ by case => [i Hi Hi0]; rewrite (bigD1 i) //= Hi0 mul0R. }
apply big_ind.
- by move=> K; exfalso; auto with real.
- by move=> ? ? ? ?; rewrite mulR_eq0 => -[]; tauto.
- by move=> i Hi Hi0; exists i.
Qed.

Lemma prodR_ge1 (A : finType) f : (forall a, 1 <= f a) ->
  1 <= \prod_(a : A) f a.
Proof.
elim/big_ind : _ => // [|x y Hx Hy *]; first by move=> _; exact/leRR.
by rewrite -{1}(mulR1 1); apply/leR_pmul => //; [exact: Hx | exact: Hy].
Qed.

Lemma prodR_constE (x0 : R) (k : nat) : \prod_(i < k) x0 = x0 ^ k.
Proof. by rewrite big_const cardT size_enum_ord iter_mulR. Qed.

Lemma prodR_card_constE (I : finType) (B : pred I) x0 : \prod_(i in B) x0 = x0 ^ #|B|.
Proof. by rewrite big_const iter_mulR. Qed.

Lemma prodRN (I : finType) (p : pred I) (F : I -> R) :
  \prod_(i in p) - F i = (-1) ^ #|p| * \prod_(i in p) F i.
Proof.
rewrite -prodR_card_constE.
apply: (big_rec3 (fun a b c => a = b * c)).
{ by rewrite mul1R. }
move=> i a b c Hi Habc; rewrite Habc; ring.
Qed.

Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.

Lemma prodR_gt0_inv (B : finType) F (HF: forall a, (0 <= F a)%coqR) :
  forall n (x : 'rV[B]_n.+1),
    (0 < \prod_(i < n.+1) F (x ``_ i) -> forall i, 0 < F (x ``_ i))%coqR.
Proof.
elim => [x | n IH].
  rewrite big_ord_recr /= big_ord0 mul1R => Hi i.
  suff : i = ord_max by move=> ->.
  by rewrite (ord1 i); exact/val_inj.
move=> x.
set t := \row_(i < n.+1) (x ``_ (lift ord0 i)).
rewrite big_ord_recl /=.
move: (HF (x ``_ ord0)); rewrite leR_eqVlt => -[<-|H].
  by rewrite mul0R => /ltRR.
rewrite mulRC (pmulR_lgt0 H) => H'.
case; case => [i0|i Hi].
  rewrite (_ : Ordinal _ = ord0) //; exact/val_inj.
have : (0 < \prod_(i0 < n.+1) F (t ``_ i0))%coqR.
  suff : (\prod_(i < n.+1) F (x ``_ (lift ord0 i)) =
         \prod_(i < n.+1) F (t ``_ i))%R by move=> <-.
  apply eq_bigr => ? _; by rewrite mxE.
have Hi' : (i < n.+1)%nat by rewrite ltnS in Hi.
move/IH/(_ (Ordinal Hi')).
set o1 := Ordinal _. set o2 := Ordinal _.
suff : lift ord0 o1 = o2 by move=> <-; rewrite mxE.
exact/val_inj.
Qed.

Local Close Scope vec_ext_scope.
Local Close Scope ring_scope.

Lemma leR_prodR (A : finType) f g : (forall a, 0 <= f a <= g a) ->
  \prod_a f a <= \prod_(a : A) g a.
Proof.
move=> fg.
have [/forallP Hf|] := boolP [forall i, f i != 0%R]; last first.
  rewrite negb_forall => /existsP[i0 /negPn/eqP fi0].
  rewrite (bigD1 i0) //= fi0 mul0R; apply prodR_ge0.
  by move=> i ; move: (fg i) => [Hi1 Hi2]; exact: (leR_trans Hi1 Hi2).
have Hprodf : 0 < \prod_(i : A) f i.
  apply/RltP. apply prodr_gt0 => a _. apply/RltP.
  move: (Hf a) (fg a) => {}Hf {fg}[Hf2 _].
  apply/ltRP; rewrite lt0R Hf /=; exact/leRP.
apply (@leR_pmul2r (1 * / \prod_(i : A) f i) _ _).
  apply divR_gt0 => //; lra.
rewrite mul1R mulRV; last exact/gtR_eqF.
set inv_spec := fun r => if r == 0 then 0 else / r.
rewrite (_ : / (\prod_(a : A) f a) = inv_spec (\prod_(a : A) f a)); last first.
  rewrite /inv_spec (_ : \prod_(a : A) f a == 0 = false) //.
  exact/negbTE/gtR_eqF.
rewrite (@big_morph _ _ (inv_spec) R1 Rmult R1 Rmult _); last 2 first.
  - move=> a b /=.
    case/boolP : ((a != 0) && (b != 0)).
    + move=> /andP [/negbTE Ha /negbTE Hb]; rewrite /inv_spec Ha Hb.
      move/negbT in Ha ; move/negbT in Hb.
      have -> : (a * b)%R == 0 = false by rewrite mulR_eq0' (negbTE Ha) (negbTE Hb).
      by rewrite invRM //; exact/eqP.
    + rewrite negb_and !negbK => /orP[|]/eqP ->;
      by rewrite /inv_spec !(eqxx,mul0R,mulR0).
  - by rewrite /inv_spec ifF ?invR1 //; exact/negbTE/eqP/R1_neq_R0.
rewrite -big_split /=; apply prodR_ge1 => a.
move/(_ a) in Hf.
move: fg => /(_ a) [Hf2 fg].
rewrite /inv_spec.
move/negbTE in Hf; rewrite Hf; move/negbT in Hf.
rewrite -(mulRV (f a)) //.
apply leR_wpmul2r => //.
rewrite -(mul1R (/ f a)).
apply divR_ge0; [lra | apply/ltRP; rewrite lt0R Hf; exact/leRP].
Qed.

End leR_ltR_rprod.

Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.

Lemma log_prodR_sumR_mlog {A : finType} k (f : A -> R) :
  (forall a, 0 <= f a)%coqR ->
  forall n (ta : 'rV[A]_n.+1),
  (forall i, 0 < f ta ``_ i)%coqR ->
  (- Log k (\prod_(i < n.+1) f ta ``_ i) = \sum_(i < n.+1) - Log k (f ta ``_ i))%R.
Proof.
move=> f0.
elim => [i Hi | n IH].
  by rewrite big_ord_recl big_ord0 mulR1 big_ord_recl big_ord0 addR0.
move=> ta Hi.
rewrite big_ord_recl /= LogM; last 2 first.
  exact/Hi.
  by apply/RltP; apply prodr_gt0 => ? _; exact/RltP/Hi.
set tl := \row_(i < n.+1) ta ``_ (lift ord0 i).
have : forall i0 : 'I_n.+1, (0 < f tl ``_ i0)%coqR.
  move=> i; rewrite mxE; exact/Hi.
move/IH => {}IH.
have -> : (\prod_(i < n.+1) f ta ``_ (lift ord0 i) = \prod_(i < n.+1) f tl ``_ i)%R.
  apply eq_bigr => i _; by rewrite mxE.
rewrite oppRD [X in _ = X]big_ord_recl IH.
congr (_ + _)%R.
apply eq_bigr => i _; by rewrite mxE.
Qed.

Local Close Scope vec_ext_scope.
Local Close Scope ring_scope.

Section bigmaxR.

Variables (A : eqType) (F : A -> R) (s : seq A).

Lemma leR_bigmaxR : forall m, m \in s -> F m <= \rmax_(m <- s) (F m).
Proof.
elim: s => // hd tl IH m; rewrite in_cons; case/orP.
- move/eqP => ->; rewrite big_cons; exact/leR_maxl.
- move/IH => H; rewrite big_cons; exact/(leR_trans H)/leR_maxr.
Qed.

Lemma bigmaxR_ge0 : (forall r, r \in s -> 0 <= F r) -> 0 <= \rmax_(m <- s) (F m).
Proof.
case: s => [_ | hd tl Hr].
- rewrite big_nil; exact/leRR.
- apply (@leR_trans (F hd)); last by rewrite big_cons; exact: leR_maxl.
  apply Hr; by rewrite in_cons eqxx.
Qed.

End bigmaxR.

Lemma bigmaxR_undup (I : eqType) g : forall (s : seq I),
   \rmax_(c <- s) g c = \rmax_(c <- undup s) g c.
Proof.
elim=> // hd tl IH /=.
rewrite big_cons.
case: ifP => Hcase.
- rewrite -IH Rmax_right //; exact: leR_bigmaxR.
- by rewrite big_cons IH.
Qed.

Lemma bigmaxR_cat (I : eqType) g : forall (s1 s2 : seq I),
  (forall x, x \in s1 ++ s2 -> 0 <= g x) ->
  \rmax_(c <- s1 ++ s2) g c = Rmax (\rmax_(c <- s1) g c) (\rmax_(c <- s2) g c).
Proof.
elim => [s2 Hg /= | h1 t1 IH s2 Hg /=].
  by rewrite big_nil Rmax_right //; exact: bigmaxR_ge0.
rewrite 2!big_cons IH ?maxRA //.
move=> x Hx; apply Hg.
by rewrite /= in_cons Hx orbC.
Qed.

Lemma bigmaxR_perm (I : eqType) g : forall (s1 s2 : seq I),
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
  have /path.splitPr[h2 t2] : h1 \in s2 by rewrite -(perm_mem Hs2) in_cons eqxx.
  by exists h2, t2.
have Hs2' : perm_eq t1 (h2 ++ t2).
  rewrite ht2 in Hs2.
  rewrite -(perm_cons h1).
  eapply perm_trans; first by apply Hs2.
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
rewrite bigmaxR_cat // maxRA (maxRC (g h1)) -maxRA ht2 bigmaxR_cat; last first.
  move=> x Hx; apply Hg; by rewrite ht2.
by rewrite big_cons.
Qed.

Lemma bigmaxR_eqi (I : finType) g (s1 s2 : seq I) :
  (forall r : I, r \in s1 -> 0 <= g r) -> s1 =i s2 ->
  \rmax_(c0 <- s1) g c0 = \rmax_(c0 <- s2) g c0.
Proof.
move=> Hg s1s2.
rewrite (bigmaxR_undup _ s1) (bigmaxR_undup g s2).
apply bigmaxR_perm; [ | | by rewrite undup_uniq | by rewrite undup_uniq].
- move=> r Hr; apply Hg.
  rewrite mem_undup in Hr.
  by rewrite s1s2.
- apply uniq_perm; [by rewrite undup_uniq | by rewrite undup_uniq | ].
  move=> i; by rewrite !mem_undup.
Qed.

Lemma bigmaxR_imset_helper (M I : finType) h (g : I -> R) (s : seq M) :
  (forall r : I, r \in enum [set h x | x in s] -> 0 <= g r) ->
  \rmax_(c0 <- enum [set h x | x in s]) g c0 = \rmax_(m <- s) g (h m).
Proof.
elim: s => [|hd tl IH Hg /=].
  rewrite big_nil.
  set tmp := enum _.
  suff -> : tmp = [::] by rewrite big_nil.
  rewrite /tmp -[in X in _ = X]enum0.
  apply eq_enum => a.
  rewrite !inE.
  apply/imsetP. case => m.
  by rewrite in_nil.
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
apply bigmaxR_eqi => // x.
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

Lemma bigmaxR_imset (M I : finType) h (g : I -> R) :
  (forall r : I, r \in [set h x | x in M] -> 0 <= g r) ->
  \rmax_(c0 in [set h x | x in M]) g c0 = \rmax_(m in M) g (h m).
Proof.
move=> Hg.
eapply trans_eq.
  eapply trans_eq; last first.
    apply (@bigmaxR_imset_helper _ I h g (enum M)).
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

Lemma leR_bigmaxRl (A : finType) (f : A -> R) (s : seq A) a :
  (forall a0, 0 <= f a0) ->
  (forall a0, a0 \in s -> f a0 <= f a) ->
  \rmax_(a0 <- s) f a0 <= f a.
Proof.
elim: s a => [a f0 _ | a0 s' IH a f0 Hf].
  rewrite big_nil; exact/f0.
rewrite big_cons; apply Rmax_lub.
- by apply Hf; rewrite mem_head.
- apply IH => // a1 a1s; apply Hf.
  by rewrite in_cons a1s orbC.
Qed.

Lemma bigmaxR_seq_eq (A : finType) (f : A -> R) (s : seq A) a :
  a \in s ->
  (forall a0, 0 <= f a0) ->
  (forall a0, a0 \in s -> f a0 <= f a) ->
  f a = \rmax_(a0 <- s) f a0.
Proof.
elim: s a => // hd tl IH a; rewrite in_cons; case/orP.
- move/eqP => -> Hhpos Hh.
  rewrite big_cons.
  rewrite Rmax_left //.
  apply leR_bigmaxRl => //.
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

Lemma bigmaxR_eq (A : finType) (C : {set A}) a (f : A -> R):
  a \in C ->
  (forall a0, 0 <= f a0) ->
  (forall c, c \in C -> f c <= f a) ->
  f a = \rmax_(c | c \in C) f c.
Proof.
move=> aC f0 Hf.
rewrite -big_filter.
apply bigmaxR_seq_eq => //.
- by rewrite mem_filter aC /= mem_index_enum.
- by move=> a0; rewrite mem_filter mem_index_enum andbT => /Hf.
Qed.

Local Open Scope R_scope.

Lemma bigmaxR_distrr I a (a0 : 0 <= a) r (P : pred I) F :
  (a * \rmax_(i <- r | P i) F i) = \rmax_(i <- r | P i) (a * F i).
Proof.
elim: r => [| h t IH].
  by rewrite 2!big_nil mulR0.
rewrite 2!big_cons.
case: ifP => Qh //.
by rewrite -IH RmaxRmult.
Qed.

Lemma bigmaxR_distrl I a (a0 : 0 <= a) r (P : pred I) F :
  (\rmax_(i <- r | P i) F i) * a = \rmax_(i <- r | P i) (F i * a).
Proof.
by rewrite mulRC bigmaxR_distrr //; apply congr_big => // ?; rewrite mulRC.
Qed.

Notation "\min^ b '_(' a 'in' A ) F" :=
  ((fun a => F) (arg_min b (fun x => x \in A) (fun a => F))) : min_scope.

Local Open Scope min_scope.

Lemma leq_bigmin (A : finType) (C : {set A}) (cnot0 : {c0 | c0 \in C})
  a (Ha : a \in C) (h : A -> nat) :
  (\min^ (sval cnot0) _(c in C) h c <= h a)%nat.
Proof. by case: arg_minnP; [case: cnot0|move=> a0 a0C; exact]. Qed.

Lemma bigmaxR_bigmin_helper (A : finType) n (g : nat -> R) :
  (forall n1 n2, (n1 <= n2 <= n)%nat -> (g n2 <= g n1)%R) ->
  (forall r, 0 <= g r) ->
  forall (C : {set n.-tuple A}) c (_ : c \in C) (d : n.-tuple A -> nat)
  (_ : forall c, c \in C -> (d c <= n)%nat)
  (cnot0 : {c0 | c0 \in C}),
  d c = \min^ (sval cnot0) _(c in C) d c ->
  g (d c) = \rmax_(c in C) g (d c).
Proof.
move=> Hdecr Hr C c cC d Hd cnot0 H.
apply (@bigmaxR_eq _ C c (fun a => g (d a))) => //.
move=> /= c0 c0C.
apply/Hdecr/andP; split; [|exact: Hd].
rewrite H; exact: leq_bigmin.
Qed.

(* TODO: useful for? *)
Lemma bigmaxR_bigmin (A M : finType) n (f : {ffun M -> n.-tuple A}) (g : nat -> R)
  (cnot0 : {c0 | c0 \in f @: M } ) :
  (forall n1 n2, (n1 <= n2 <= n)%nat -> (g n2 <= g n1)%R) ->
  (forall r, 0 <= g r) ->
  forall m (d : n.-tuple A -> nat)
  (_ : forall c0 : n.-tuple A, c0 \in [set f x | x : M] -> (d c0 <= n)%nat),
  d (f m) = \min^ (sval cnot0) _(c in [set f x | x in M]) d c ->
  g (d (f m)) = \rmax_(m | m \in M) g (d (f m)).
Proof.
move=> n1n2 Hg m d H Hd.
transitivity (\rmax_(c in [set f x | x in M]) g (d c)); last by rewrite bigmaxR_imset.
apply bigmaxR_bigmin_helper with cnot0 => //.
apply/imsetP; by exists m.
Qed.

Lemma bigmaxR_bigmin_vec_helper (A : finType) n (g : nat -> R) :
  (forall n1 n2, (n1 <= n2 <= n)%nat -> (g n2 <= g n1)%R) ->
  (forall r, 0 <= g r) ->
  forall (C : {set 'rV[A]_n}) c (_ : c \in C) (d : 'rV[A]_n -> nat)
  (_ : forall c, c \in C -> (d c <= n)%nat)
  (cnot0 : {c0 | c0 \in C}),
  d c = \min^ (sval cnot0) _(c in C) d c ->
  g (d c) = \rmax_(c in C) g (d c).
Proof.
move=> Hdecr Hr C c cC d Hd cnot0 H.
apply (@bigmaxR_eq _ C c (fun a => g (d a))) => //.
move=> /= c0 c0C.
apply/Hdecr/andP; split; [|exact: Hd].
rewrite H; exact: leq_bigmin.
Qed.

Lemma bigmaxR_bigmin_vec (A M : finType) n (f : {ffun M -> 'rV[A]_n}) (g : nat -> R)
  (cnot0 : {c0 | c0 \in f @: M } ) :
  (forall n1 n2, (n1 <= n2 <= n)%nat -> (g n2 <= g n1)%R) ->
  (forall r, 0 <= g r) ->
  forall m (d : 'rV[A]_n -> nat)
  (_ : forall c0 : 'rV[A]_n, c0 \in f @: M -> (d c0 <= n)%nat),
  d (f m) = \min^ (sval cnot0) _(c in f @: M) d c ->
  g (d (f m)) = \rmax_(m in M) g (d (f m)).
Proof.
move=> n1n2 Hg m d H Hd.
transitivity (\rmax_(c in f @: M) g (d c)); last by rewrite bigmaxR_imset.
apply bigmaxR_bigmin_vec_helper with cnot0 => //.
by apply/imsetP; exists m.
Qed.
