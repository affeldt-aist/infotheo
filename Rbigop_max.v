(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg perm zmodp matrix.
Require Import Reals Fourier.
Require Import Rssr Reals_ext ssr_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Bigmax/min Operators for Coq Reals *)

Lemma iter_Rmax a b (Hb : b <= a) k : ssrnat.iter k (Rmax b) a = a.
Proof. elim: k => // k Hk; by rewrite iterS Hk Rmax_right. Qed.

Notation "\rmax_ ( a 'in' A ) F" := (\big[Rmax/0%R]_( a in A ) F)
  (at level 41, F at level 41, a, A at level 50,
    format "'[' \rmax_ ( a  'in'  A ) '/  '  F ']'") : R_scope.
Notation "\rmax_ ( i | P ) F" := (\big[Rmax/0%R]_( i | P) F)
  (at level 41, F at level 41, i at level 50,
    format "'[' \rmax_ ( i | P ) '/  '  F ']'") : R_scope.
Notation "\rmax_ ( i '<-' A | P ) F" := (\big[Rmax/0%R]_( i <- A | P ) F)
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \rmax_ ( i  '<-'  A  |  P ) '/  '  F ']'") : R_scope.
Notation "\rmax_ ( a '<-' A ) F" := (\big[Rmax/0%R]_( a <- A ) F)
  (at level 41, F at level 41, a, A at level 50,
    format "'[' \rmax_ ( a  '<-'  A ) '/  '  F ']'") : R_scope.
Reserved Notation "\rmax_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).

Notation "\rmax_ ( i : I ) F" :=
  (\big[Rmax/R0]_(i : I) F) (only parsing) : R_scope.

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
rewrite 2!big_cons IH; last first.
  move=> x Hx; apply Hg.
  by rewrite /= in_cons Hx orbC.
by rewrite RmaxA.
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
rewrite bigrmax_cat // RmaxA (RmaxC (g h1)) -RmaxA ht2 bigrmax_cat; last first.
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
((fun a => F) (arg_min b (fun x => x \in A) (fun a => F)))
  (at level 41, F at level 41, a, A at level 50,
    format "'[' \min^ b '_(' a  'in'  A ) '/  '  F ']'") : min_scope.

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
