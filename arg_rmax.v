(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div fintype tuple finfun bigop.
Require Import Reals Fourier.
Require Import ssrR Reals_ext ssr_ext num_occ.

(** * Variation of the SSReflect standard library *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section MinFintype.

Local Open Scope nat_scope.

Variables (I : finType) (i0 : I) (P : pred I) (ord : rel I).

Let arg_pred_min := [pred i | P i && [forall j, P j ==> ord i j]].

Definition arg_minord := odflt i0 (pick arg_pred_min).

CoInductive minimum_spec_ord : I -> Type :=
  MinimumSpecOrd i of P i & (forall j, P j -> ord i j)
    : minimum_spec_ord i.

Hypothesis P_not_pred0 : {i | P i}.
Hypothesis ord_trans : transitive ord.
Hypothesis ord_refl : reflexive ord.
Hypothesis ord_total : total ord.

Lemma in_sort a s : a \in (sort ord s) = (a \in s).
Proof. rewrite -2!has_pred1; exact/eq_has_r/mem_sort. Qed.

Lemma all_sort s : all P (sort ord s) = all P s.
Proof. exact/eq_all_r/mem_sort. Qed.

Lemma in_sorted a s : sorted ord s -> a \in s -> ord (head a s) a.
Proof.
case: s; first by rewrite in_nil.
move=> hd tl Hs a_in_s.
rewrite -nth0.
rewrite {2}(_ : a = nth a (hd :: tl) (find (pred1 a) (hd :: tl))); last first.
  apply/esym/eqP.
  rewrite (_ : nth a (hd :: tl) (find (pred1 a) (hd :: tl)) == a = pred1 a (nth a (hd :: tl) (find (pred1 a) (hd :: tl)))) //.
  by rewrite nth_find // has_pred1.
case/boolP : (find (pred1 a) (hd :: tl) == 0) => [/eqP -> //|H].
apply sorted_of_nth => //.
apply/andP; split.
- rewrite ltn_neqAle leq0n andbT.
  apply/negP => /eqP abs; contradict H; rewrite abs; exact/negP/negPn/eqP.
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
    by rewrite -hd_tl all_sort filter_all.
  apply Hs.
  by rewrite in_cons eqxx.
- move=> i Pi.
  move Hs : (sort _ _) => s.
  have i_in_s: i \in s.
    by rewrite -Hs in_sort mem_filter Pi /= mem_enum.
  rewrite (_ : head j0 s = head i s); last first.
    clear Hs.
    case: s i_in_s => //; by rewrite in_nil.
  apply in_sorted => //.
  rewrite -Hs.
  exact/sort_sorted.
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
exact/min_i/Pj.
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
Hypothesis ord_trans : transitive ord.

Let ord_inv_trans : transitive ord_inv.
Proof. move => x y z Hxy Hzx; apply (ord_trans Hzx Hxy). Qed.

Hypothesis ord_refl : reflexive ord.

Let ord_inv_refl : reflexive ord_inv.
Proof. by rewrite /reflexive /ord_inv. Qed.

Hypothesis ord_total : total ord.

Let ord_inv_total : total ord_inv.
Proof. rewrite /total => x y ; apply ord_total. Qed.

Lemma arg_maxordP : maximum_spec_ord arg_maxord.
Proof.
rewrite /arg_maxord.
move: (@arg_minordP _ i0 P ord_inv P_not_pred0 ord_inv_trans ord_inv_refl ord_inv_total) => Harg.
constructor; move: Harg ; by case.
Qed.

End MaxFintype.

Section rExtrema.

Variables (I : finType) (i0 : I) (P : pred I) (F : I -> R).

Let ord_F_Rle i j := (F i) <b= (F j).

Let ord_trans : transitive ord_F_Rle.
Proof.
rewrite /transitive /ord_F_Rle => x y z /leRP Hyx /leRP Hxz; apply/leRP.
exact/(@leR_trans (F x)).
Qed.

Let ord_refl : reflexive ord_F_Rle.
Proof. rewrite /reflexive /ord_F_Rle => x ; exact/leRP/leRR. Qed.

Let ord_total : total ord_F_Rle.
Proof.
rewrite /total /ord_F_Rle => x y. apply/orP.
case (Rlt_le_dec (F x) (F y)) => [/ltRW|] /leRP H; by [left|right].
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
move: (@arg_maxordP _ i0 P ord_F_Rle P_not_pred0 ord_trans ord_refl ord_total) => Harg.
constructor; move: Harg ; by case.
Qed.

Lemma arg_rmax2 : forall j, P j -> F j <= F arg_rmax.
Proof.
case: arg_rmaxP => i1 Pi1.
rewrite /ord_F_Rle => H j Pj.
exact/leRP/H.
Qed.

End rExtrema.
