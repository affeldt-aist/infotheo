(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div fintype tuple finfun bigop.
Require Import Reals Fourier.
Require Import Rssr Reals_ext ssr_ext num_occ.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope Rb_scope.

(** * Variation of the SSReflect standard library *)

Section MinFintype.

Local Open Scope nat_scope.

Variables (I : finType) (i0 : I) (P : pred I) (ord : rel I).

Let arg_pred_min := [pred i | P i && [forall j, P j ==> ord i j]].

Definition arg_minord := odflt i0 (pick arg_pred_min).

CoInductive minimum_spec_ord : I -> Type :=
  MinimumSpecOrd i of P i & (forall j, P j -> ord i j)
    : minimum_spec_ord i.

Hypothesis P_not_pred0 : {i | P i}.
Hypothesis transitive_ord : transitive ord.
Hypothesis reflexive_ord : reflexive ord.
Hypothesis total_ord : total ord.

Lemma in_sort a s : a \in (sort ord s) = (a \in s).
Proof.
rewrite -2!has_pred1.
apply eq_has_r, mem_sort.
Qed.

Lemma all_sort s : all P (sort ord s) = all P s.
Proof.
apply eq_all_r, mem_sort.
Qed.

Lemma in_sorted a s: sorted ord s -> a \in s -> ord (head a s) a.
Proof.
case : s ; first by rewrite in_nil.
move=> hd tl Hs a_in_s.
rewrite -nth0.
rewrite {2}(_ : a = nth a (hd :: tl) (find (pred1 a) (hd :: tl))) ; last first.
  symmetry.
  apply/eqP.
  rewrite (_ : nth a (hd :: tl) (find (pred1 a) (hd :: tl)) == a = pred1 a (nth a (hd :: tl) (find (pred1 a) (hd :: tl)))) ; last done.
  apply nth_find.
  by rewrite has_pred1.
case/orP : (orbN (find (pred1 a) (hd :: tl) == 0)) ; first by move/eqP => ->.
move => H.
apply sorted_inv => //.
apply/andP ; split.
- rewrite ltn_neqAle.
  apply/andP ; split.
  - apply/negP => /eqP abs ; contradict H ; rewrite abs ; by apply/negP/negPn/eqP.
  - by apply leq0n.
by rewrite -has_find has_pred1.
Qed.

Lemma find_ex_minord : {i | P i & forall j, P j -> ord i j}.
Proof.
case P_not_pred0 => j0 Pj0.
exists (head j0 (sort ord (filter P (enum I)))).
- move Hs : (sort _ _) => s.
  case: s Hs ; first by move=> _ /=.
  move=> hd tl hd_tl /=.
  have : all P (hd :: tl) ; last move=> /allP Hs.
    rewrite -hd_tl.
    rewrite all_sort.
    apply filter_all.
  apply Hs.
  by rewrite in_cons eqxx.
- move=> i Pi.
  move Hs : (sort _ _) => s.
  have i_in_s: i \in s.
    by rewrite -Hs in_sort mem_filter Pi /= mem_enum.
  rewrite (_ : head j0 s = head i s) ; last first.
    clear Hs.
    case: s i_in_s ; first by rewrite in_nil.
    by move=> hd tl _ /=.
  apply in_sorted => //.
  rewrite -Hs.
  by apply sort_sorted.
Qed.

Definition ex_minord := s2val find_ex_minord.

Inductive ex_minord_spec : I -> Type :=
  ExMinordSpec i of P i & (forall j, P j -> ord i j) : ex_minord_spec i.

Lemma ex_minordP : ex_minord_spec ex_minord.
Proof. by rewrite /ex_minord; case: find_ex_minord. Qed.

Hypothesis Pi0 : P i0.

Let FP j := [exists i, P i && (i == j)].

Let FP_F i : P i -> FP i.
Proof. by move=> Pi; apply/existsP; exists i; rewrite Pi /=. Qed.

Let exFP : exists r, FP r. Proof. by exists i0; exact: FP_F. Qed.

Lemma arg_minordP : minimum_spec_ord arg_minord.
Proof.
rewrite /arg_minord; case: pickP => [i /andP[Pi /forallP min_i] | no_i].
  split=> // j ; exact/implyP.
move: (ex_minordP).
case => n ex_i min_i.
apply FP_F in ex_i.
case/pred0P: ex_i => i.
apply: contraFF (no_i i) => /andP[Pi def_n]; rewrite /= Pi.
apply/forallP=> j.
apply/implyP=> Pj.
move/eqP in def_n.
rewrite def_n.
apply min_i.
exact Pj.
Qed.

End MinFintype.

Section MaxFintype.

Variables (I : finType) (i0 : I) (P : pred I) (ord : rel I).

Let ord_inv i j := ord j i.

Definition arg_maxord := arg_minord i0 P ord_inv.

CoInductive maximum_spec_ord : I -> Type :=
  MaximumSpecOrd i of P i & (forall j, P j -> ord j i)
    : maximum_spec_ord i.

Hypothesis P_not_pred0 : {i | P i}.
Hypothesis transitive_ord : transitive ord.

Let transitive_ord_inv : transitive ord_inv.
Proof. rewrite /ord_inv /transitive => x y z Hxy Hzx ; apply (transitive_ord Hzx Hxy). Qed.

Hypothesis reflexive_ord : reflexive ord.

Let reflexive_ord_inv : reflexive ord_inv.
Proof. by rewrite /reflexive /ord_inv. Qed.

Hypothesis total_ord : total ord.

Let total_ord_inv : total ord_inv.
Proof. rewrite /total => x y ; apply total_ord. Qed.

Lemma arg_maxordP : maximum_spec_ord arg_maxord.
Proof.
rewrite /arg_maxord.
move: (@arg_minordP _ i0 P ord_inv P_not_pred0 transitive_ord_inv reflexive_ord_inv total_ord_inv) => Harg.
constructor ; move: Harg ; by case.
Qed.

End MaxFintype.

Section rExtrema.

Variables (I : finType) (i0 : I) (P : pred I) (F : I -> R).

Let ord_F_Rle i j := (F i) <b= (F j).

Let transitive_ord : transitive ord_F_Rle.
Proof.
rewrite /transitive /ord_F_Rle => x y z /RleP Hyx /RleP Hxz ; apply/RleP.
by apply (Rle_trans _ (F x) _).
Qed.

Let reflexive_ord : reflexive ord_F_Rle.
Proof. rewrite /reflexive /ord_F_Rle => x ; apply/RleP ; apply Rle_refl. Qed.

Let total_ord : total ord_F_Rle.
Proof.
rewrite /total /ord_F_Rle => x y. apply/orP.
case (Rlt_le_dec (F x) (F y)) => [/(Rlt_le)|] /RleP H ; by [apply or_introl|apply or_intror].
Qed.

Definition arg_rmax := arg_maxord i0 P ord_F_Rle.

CoInductive minimum_spec_r : I -> Type :=
  MinimumSpecR i of P i & (forall j, P j -> ord_F_Rle i j)
    : minimum_spec_r i.

CoInductive maximum_spec_r : I -> Type :=
  MaximumSpecR i of P i & (forall j, P j -> ord_F_Rle j i)
    : maximum_spec_r i.

Hypothesis P_not_pred0 : {i | P i}.

Lemma arg_rmaxP : maximum_spec_r arg_rmax.
Proof.
rewrite /arg_rmax.
move: (@arg_maxordP _ i0 P ord_F_Rle P_not_pred0 transitive_ord reflexive_ord total_ord) => Harg.
constructor ; move: Harg ; by case.
Qed.

Lemma arg_rmax2 : forall j, P j -> F j <= F arg_rmax.
Proof.
move: arg_rmaxP.
case => i1 Pi1.
rewrite /ord_F_Rle => H.
move=> j Pj.
apply/RleP.
by apply H.
Qed.

End rExtrema.
