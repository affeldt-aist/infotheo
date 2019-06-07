From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup perm finalg matrix.
Require Import Reals Lra.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.
Require Import cproba divergence entropy.

(* tentative formalization Cover and Thomas, Chapter 2
see also convex_dist.v
Contents:
- Various distributions (Take.d, Nth.d, PairNth.d, PairTake.d, MargDist.d,
  MultivarPerm.d, TakeDrop.d)
- Module JointEntropy.
  Section joint_entropy_prop.
- Module CondEntropy.
  Section conditional_entropy_prop3.
- Module conditional_entropy_example.
- Section chain_rule. (thm 2.1.1)
- Section chain_rule_generalization.
- Section entropy_chain_rule_corollary.
- Section conditional_entropy_prop.
- Section conditional_entropy_prop2.
- Module MutualInfo.
- Section mutualinfo_prop.
- Section chain_rule_for_entropy.
- Section divergence_conditional_distributions.
- Section conditional_mutual_information.
- Section conditional_relative_entropy.
- Section chain_rule_for_information. ( thm 2.5.1 )
- Section conditioning_reduces_entropy.
- Section independence_bound_on_entropy.
- Section markov_chain.
- Section markov_chain_prop.
- Section Han_inequality.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.
Local Open Scope proba_scope.

(* TODO: move? *)
Section row_mxA'.
Variables (A : finType) (n : nat) (i : 'I_n.+1).
Lemma row_mxA' (w1 : 'rV_(n - i)) (a : A) (w : 'rV_i) (H1 : (n.+1 - i)%nat = (n - i)%nat.+1)
  (H2 : _) (H3 : (i + 1%nat + (n - i))%nat = n.+1) :
  castmx (erefl 1%nat, H3) (row_mx (row_mx w (\row__ a)) w1) =
  castmx (erefl 1%nat, H2) (row_mx w (castmx (erefl 1%nat, esym H1) (row_mx (\row_(_ < 1) a) w1))).
Proof.
apply/rowP => j.
rewrite !castmxE /= !cast_ord_id /=.
case: (ltnP j i) => [ji|].
  move=> [:Hj0].
  have @j0 : 'I_(i + 1) by apply: (@Ordinal _ j); abstract: Hj0; rewrite addn1 ltnS ltnW.
  rewrite (_ : cast_ord _ _ = lshift (n - i) j0); last exact/val_inj.
  rewrite row_mxEl.
  rewrite (_ : cast_ord _ _ = lshift (n.+1 - i) (Ordinal ji)); last exact/val_inj.
  rewrite row_mxEl.
  rewrite (_ : j0 = lshift 1 (Ordinal ji)); last exact/val_inj.
  by rewrite row_mxEl.
rewrite leq_eqVlt => /orP[/eqP|]ij.
  move=> [:Hj0].
  have @j0 : 'I_(i + 1) by apply: (@Ordinal _ j); abstract: Hj0; by rewrite addn1 ij ltnS.
  rewrite (_ : cast_ord _ _ = lshift (n - i) j0); last exact/val_inj.
  rewrite row_mxEl.
  rewrite (_ : j0 = rshift i ord0); last first.
    by apply val_inj => /=; rewrite ij addn0.
  rewrite row_mxEr mxE.
  move=> [:Hj1].
  have @j1 : 'I_(n.+1 - i).
    by apply: (@Ordinal _ 0); abstract: Hj1; rewrite subn_gt0.
  rewrite (_ : cast_ord _ _ = rshift i j1); last first.
    by apply/val_inj => /=; rewrite ij addn0.
  rewrite row_mxEr castmxE /= cast_ord_id esymK.
  have @j2 : 'I_1 := ord0.
  rewrite (_ : cast_ord _ _ = lshift (n - i) j2); last exact/val_inj.
  by rewrite (@row_mxEl _ _ 1%nat) mxE.
move=> [:Hj0].
have @j0 : 'I_(n - i).
  apply: (@Ordinal _ (j - i.+1)); abstract: Hj0.
  by rewrite subnS prednK ?subn_gt0 // leq_sub2r // -ltnS.
rewrite (_ : cast_ord _ _ = rshift (i + 1) j0); last first.
  apply/val_inj => /=; by rewrite addn1 subnKC.
rewrite row_mxEr.
have @j1 : 'I_(n.+1 - i) by apply: (@Ordinal _ (j - i)); rewrite ltn_sub2r.
rewrite (_ : cast_ord _ _ = rshift i j1); last first.
  by apply val_inj => /=; rewrite subnKC // ltnW.
rewrite row_mxEr castmxE /= cast_ord_id.
have @j2 : 'I_(n - i).
  apply: (@Ordinal _ (j1 - 1)).
  by rewrite /= subn1 prednK ?subn_gt0 // leq_sub2r // -ltnS.
rewrite (_ : cast_ord _ _ = rshift 1 j2); last first.
  apply/val_inj => /=; by rewrite subnKC // subn_gt0.
rewrite (@row_mxEr _ _ 1%nat); congr (_ _ _); apply val_inj => /=; by rewrite subnS subn1.
Qed.
End row_mxA'.

Lemma ltnS' n m : (n < m.+1)%nat -> (n <= m)%nat.
Proof. by rewrite ltnS. Qed.

Section rV_take_drop.
Variables (A : finType) (n : nat).
Implicit Types (i : 'I_n.+1) (v : 'rV[A]_n).
Local Open Scope ring_scope.

Definition row_take i v : 'rV_i :=
  lsubmx (castmx (erefl, esym (subnKC (ltnS' (ltn_ord i)))) v).

Definition row_drop i v : 'rV_(n - i):=
  rsubmx (castmx (erefl, esym (subnKC (ltnS' (ltn_ord i)))) v).

Lemma row_mx_take_drop i v :
  v = castmx (erefl, subnKC (ltnS' (ltn_ord i))) (row_mx (row_take i v) (row_drop i v)).
Proof.
rewrite hsubmxK; apply/rowP => j; rewrite !castmxE /= !cast_ord_id.
congr (v ord0 _); exact: val_inj.
Qed.
End rV_take_drop.

(* TODO: move? *)
Lemma head_of_fst_belast_last (A : finType) (n : nat) (P : {dist 'rV[A]_n.+2}) :
  Multivar.head_of (Bivar.fst (Multivar.belast_last P)) = Multivar.head_of P.
Proof.
rewrite /Multivar.head_of /Bivar.fst /Multivar.to_bivar /Multivar.belast_last.
rewrite !DistMap.comp; congr (DistMap.d _ P).
apply FunctionalExtensionality.functional_extensionality => /= v.
rewrite /rbelast mxE; congr (v ord0 _); exact: val_inj.
Qed.

Module Take.
Section def.
Variable (A : finType) (n : nat) (P : {dist 'rV[A]_n}).
Definition d (i : 'I_n.+1) : {dist 'rV[A]_i} := DistMap.d (row_take i) P.
Lemma dE i v : d i v = \rsum_(w in 'rV[A]_(n - i))
  P (castmx (erefl, subnKC (ltnS' (ltn_ord i))) (row_mx v w)).
Proof.
rewrite DistMap.dE /=.
rewrite (@reindex_onto _ _ _ [finType of 'rV[A]_n] [finType of 'rV[A]_(n - i)]
  (fun w => castmx (erefl 1%nat, subnKC (ltnS' (ltn_ord i))) (row_mx v w))
  (@row_drop A n i)) /=; last first.
  move=> w wv; apply/rowP => j.
  rewrite castmxE /= cast_ord_id /row_drop mxE; case: splitP => [j0 /= jj0|k /= jik].
  - rewrite -(eqP wv) mxE castmxE /= cast_ord_id; congr (w _ _); exact: val_inj.
  - rewrite mxE /= castmxE /= cast_ord_id; congr (w _ _); exact: val_inj.
apply eq_bigl => w; rewrite inE; apply/andP; split; apply/eqP/rowP => j.
- by rewrite !mxE !castmxE /= !cast_ord_id esymK cast_ordK row_mxEl.
- by rewrite !mxE !castmxE /= cast_ord_id esymK cast_ordK cast_ord_id row_mxEr.
Qed.
End def.
Section prop.
Local Open Scope vec_ext_scope.
Lemma all (A : finType) (n : nat) (P : {dist 'rV[A]_n.+2}) :
  d P (lift ord0 ord_max) = P.
Proof.
rewrite /d (_ : row_take (lift ord0 ord_max) = ssrfun.id) ?DistMap.id //.
apply FunctionalExtensionality.functional_extensionality => v; apply/rowP => i.
rewrite /row_take mxE castmxE /= cast_ord_id; congr (v _ _); exact: val_inj.
Qed.
End prop.
End Take.
Arguments Take.dE {A} {n} _ _ _.

Module Nth.
Section def.
Local Open Scope vec_ext_scope.
Variables (A : finType) (n : nat) (P : {dist 'rV[A]_n}) (i : 'I_n).
Definition d : {dist A} := DistMap.d (fun v : 'rV[A]_n => v ord0 i) P.
Lemma dE a : d a = \rsum_(x : 'rV[A]_n | x ``_ i == a) P x.
Proof. by rewrite DistMap.dE. Qed.
End def.
End Nth.

Module PairNth.
Section def.
Local Open Scope vec_ext_scope.
Variables (A B : finType) (n : nat) (P : {dist 'rV[A]_n * B}) (i : 'I_n).
Definition d : {dist A * B} := DistMap.d (fun x : 'rV[A]_n * B => (x.1 ord0 i, x.2)) P.
Lemma dE ab : d ab = \rsum_(x : 'rV[A]_n * B | (x.1 ``_ i == ab.1) && (x.2 == ab.2)) P x.
Proof. by rewrite DistMap.dE. Qed.
End def.
End PairNth.

Module PairTake.
Section def.
Variables (A B : finType) (n : nat) (P : {dist 'rV[A]_n.+1 * B}) (i : 'I_n.+1).
Definition d : {dist 'rV_i * A * B} :=
  DistMap.d (fun x : 'rV[A]_n.+1 * B => (row_take (widen_ord (leqnSn _) i) x.1, x.1 ord0 i, x.2)) P.
End def.
End PairTake.

Section to_bivar_last_take.

Variables (A B : finType).
Variables (n : nat) (PY : {dist 'rV[A]_n.+1 * B}).
Let P : {dist 'rV[A]_n.+1} := Bivar.fst PY.

Lemma belast_last_take (j : 'I_n.+1) :
  Multivar.belast_last (Take.d P (lift ord0 j)) = Bivar.fst (PairTake.d PY j).
Proof.
rewrite /Multivar.belast_last /Take.d /Bivar.fst /PairTake.d !DistMap.comp.
congr (DistMap.d _ PY).
apply FunctionalExtensionality.functional_extensionality => /= -[v b] /=.
congr (_, _).
- apply/rowP => i.
  rewrite /rbelast !mxE !castmxE /=; congr (v _ _); exact: val_inj.
- rewrite /rlast mxE castmxE /=; congr (v _ _); exact: val_inj.
Qed.

End to_bivar_last_take.

Lemma head_of_nth0 (A : finType) (n : nat) (P : {dist 'rV[A]_n.+1}) :
  Multivar.head_of P = Nth.d P ord0.
Proof.
by rewrite /Multivar.head_of /Nth.d /Bivar.fst /Multivar.to_bivar DistMap.comp.
Qed.

Local Open Scope vec_ext_scope.

Lemma take_nth (A : finType) (n : nat) (P : {dist 'rV[A]_n.+1}) (i : 'I_n.+1) :
  Bivar.snd (Multivar.belast_last (Take.d P (lift ord0 i))) = Nth.d P i.
Proof.
rewrite /Bivar.snd /Multivar.belast_last /Take.d /Nth.d !DistMap.comp.
congr (DistMap.d _ _).
apply FunctionalExtensionality.functional_extensionality => /= v.
rewrite /rlast mxE castmxE /= cast_ord_id /=; congr (v ``_ _); exact: val_inj.
Qed.

Module MargDist.
Section def.
Variables (A : finType) (n : nat) (P : {dist 'rV[A]_n.+1}) (i : 'I_n.+1).
Definition d : {dist 'rV[A]_n} := DistMap.d (fun v => col' i v) P.
Lemma dE v : d v = \rsum_(x : 'rV[A]_n.+1 | col' i x == v) P x.
Proof. by rewrite DistMap.dE. Qed.
End def.
Section prop.
Variables (A : finType) (n : nat) (P : {dist 'rV[A]_n.+1}).
Lemma zero : d P ord0 = Multivar.tail_of P.
Proof.
by rewrite /d /Multivar.tail_of /Bivar.snd /Multivar.to_bivar DistMap.comp.
Qed.
End prop.
End MargDist.

(*TODO: move*)
Lemma col_perm_inj n (s : 'S_n) T m : injective (@col_perm T m n s).
Proof.
move=> x y; rewrite /col_perm => /matrixP xy; apply/matrixP => i j.
by move: (xy i (s^-1%g j)); rewrite !mxE permKV.
Qed.

Module MultivarPerm.
Section def.
Variables (A : finType) (n : nat) (P : {dist 'rV[A]_n}) (s : 'S_n).
Definition d : {dist 'rV[A]_n} := DistMap.d (col_perm s^-1) P.
Lemma dE v : d v = P (col_perm s v).
Proof.
rewrite DistMap.dE /= {1}(_ : v = col_perm s^-1 (col_perm s v)); last first.
  by rewrite -col_permM mulVg col_perm1.
rewrite big_pred1_inj //; exact: col_perm_inj.
Qed.
End def.
Section prop.
Variables (A : finType) (n : nat) (P : {dist 'rV[A]_n}) (s : 'S_n).
Local Open Scope entropy_scope.
Lemma entropy : `H P = `H (d P s).
Proof.
rewrite /entropy; congr (- _) => /=.
rewrite (@reindex_inj _ _ _ _ (@col_perm _ _ _ s) xpredT); last first.
  exact: col_perm_inj.
apply eq_bigr => v _; by rewrite MultivarPerm.dE.
Qed.
End prop.
End MultivarPerm.

Module TakeDrop.
Section def.
Variables (A : finType) (n : nat) (P : {dist 'rV[A]_n.+1}) (i : 'I_n.+1).
Definition d : {dist A * 'rV[A]_i * 'rV[A]_(n - i)} :=
  DistMap.d (fun x : 'rV[A]_n.+1 => (x ord0 ord0, row_take i (rbehead x), row_drop i (rbehead x))) P.
Let g (x : 'rV[A]_n.+1) : A * 'rV[A]_i * 'rV[A]_(n - i) :=
  (x ``_ ord0,
   row_take i (rbehead x),
   row_drop i (rbehead x)).
Lemma inj_g : injective g.
Proof.
move=> a b; rewrite /g => -[H1 H2 H3].
rewrite -(row_mx_rbehead a) -(row_mx_rbehead b) H1; congr (@row_mx _ 1%nat 1%nat _ _ _).
rewrite (row_mx_take_drop i (rbehead a)) (row_mx_take_drop i (rbehead b)).
by rewrite H2 H3.
Qed.
Lemma dE x : d x = P (row_mx (\row_(_ < 1) x.1.1) (castmx (erefl 1%nat, @subnKC i n (ltnS' (ltn_ord i))) (row_mx x.1.2 x.2))).
Proof.
rewrite /d DistMap.dE /=.
rewrite (eq_bigl (fun a => g a == x)) //.
rewrite {1}(_ : x = g (row_mx (\row_(k<1) x.1.1) (castmx (erefl 1%nat, subnKC (ltnS' (ltn_ord i))) (row_mx x.1.2 x.2)))); last first.
  move: x => /= -[[x11 x12] x2].
  rewrite /g row_mx_row_ord0 /=; congr (_, _, _).
  apply/rowP => j; rewrite !mxE !castmxE /= cast_ord_id mxE esymK.
  have @k : 'I_n.
    by apply: (@Ordinal _ j); rewrite (leq_trans (ltn_ord j)) // -ltnS.
  rewrite (_ : lift _ _ = rshift 1%nat k); last first.
    by apply val_inj => /=; rewrite /bump leq0n.
  rewrite (@row_mxEr _ 1%nat 1%nat) // castmxE /= cast_ord_id.
  rewrite (_ : cast_ord _ k = lshift (n - i) j).
  by rewrite row_mxEl.
  exact: val_inj.
  apply/rowP => j; rewrite mxE castmxE /= cast_ord_id mxE esymK.
  have @k0 : 'I_n by apply: (@Ordinal _ (i + j)); rewrite -ltn_subRL.
  rewrite (_ : lift _ _ = rshift 1%nat k0); last first.
    apply val_inj => /=; by rewrite /bump leq0n.
  rewrite (@row_mxEr _ 1%nat 1%nat) castmxE /=.
  rewrite (_ : cast_ord _ _ = rshift i j); last exact: val_inj.
  by rewrite row_mxEr cast_ord_id.
by rewrite (big_pred1_inj inj_g).
Qed.
End def.
End TakeDrop.

Local Open Scope entropy_scope.

Module JointEntropy.
Local Open Scope entropy_scope.
Section jointentropy.
Variables (A B : finType) (P : {dist A * B}).

(* eqn 2.8 *)
Definition h := `H P.

(* eqn 2.9 *)
Lemma hE : h = `E (--log P).
Proof. by rewrite /h entropy_Ex. Qed.

Lemma hC : h = `H (Swap.d P).
Proof.
congr (- _) => /=.
rewrite (eq_bigr (fun a => P (a.1, a.2) * log (P (a.1, a.2)))); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => P (a1, a2) * log (P (a1, a2)))) /=.
rewrite exchange_big pair_big; apply eq_bigr => -[a b] _; by rewrite Swap.dE.
Qed.

End jointentropy.
End JointEntropy.

Section joint_entropy_prop.

Variable (A : finType) (P : {dist A}).

Lemma joint_entropy_self : `H (Self.d P) = `H P.
Proof.
rewrite /entropy; congr (- _).
rewrite (eq_bigr  (fun a => Self.d P (a.1, a.2) * log (Self.d P (a.1, a.2)))); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => Self.d P (a1, a2) * log (Self.d P (a1, a2)))) /=.
apply/eq_bigr => a _.
rewrite (bigD1 a) //= !Self.dE /= eqxx (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 ?addR0 //.
move=> a' /negbTE; rewrite Self.dE /= eq_sym => ->; by rewrite mul0R.
Qed.

End joint_entropy_prop.

Module CondEntropy.
Section condentropy.
Variables (A B : finType) (QP : {dist B * A}).

(* H(Y|X = x), see eqn 2.10 *)
Definition h1 a := - \rsum_(b in B)
  \Pr_QP [ [set b] | [set a] ] * log (\Pr_QP [ [set b] | [set a] ]).

Let P := Bivar.snd QP.

(*eqn 2.11 *)
Definition h := \rsum_(a in A) P a * h1 a.

Let PQ := Swap.d QP.

(* cover&thomas 2.12 *)
Lemma hE : h = - \rsum_(a in A) \rsum_(b in B)
  PQ (a, b) * log (\Pr_QP [ [set b] | [set a]]).
Proof.
rewrite /h big_morph_oppR /=; apply eq_bigr => a _.
rewrite /h1 mulRN big_distrr /=; congr (- _); apply eq_bigr => b _.
rewrite mulRA; congr (_ * _).
by rewrite mulRC -(Pr_set1 P a) -Pr_cPr setX1 Swap.dE Pr_set1.
Qed.

Lemma h1_ge0 a : 0 <= h1 a.
Proof.
rewrite /h1 big_morph_oppR; apply rsumr_ge0 => b _.
rewrite -mulRN.
case/boolP : (\Pr_QP[[set b]|[set a]] == 0) => [/eqP|] H0.
  rewrite H0 mul0R; exact/leRR.
apply mulR_ge0; [exact: cPr_ge0|].
rewrite -oppR0 -(Log_1 2) /log leR_oppr oppRK.
apply Log_increasing_le => //; [by rewrite cPr_gt0 | exact: cPr_max].
Qed.

Lemma h_ge0 : 0 <= h.
Proof.
apply rsumr_ge0 => a _; apply mulR_ge0; [exact: dist_ge0 | exact: h1_ge0].
Qed.

End condentropy.
End CondEntropy.

Section conditional_entropy_prop3.

Variables (A B C : finType) (PQR : {dist A * B * C}).

Lemma h1TripC23 b c :
  CondEntropy.h1 (TripA.d PQR) (b, c) =
  CondEntropy.h1 (TripA.d (TripC23.d PQR)) (c, b).
Proof.
rewrite /CondEntropy.h1; congr (- _).
by apply eq_bigr => a _; rewrite -!setX1 cPr_TripA_TripC23.
Qed.

Lemma hTripC23 :
  CondEntropy.h (TripA.d PQR) =
  CondEntropy.h (TripA.d (TripC23.d PQR)).
Proof.
rewrite /CondEntropy.h /=.
rewrite (eq_bigr (fun a => (Bivar.snd (TripA.d PQR)) (a.1, a.2) * CondEntropy.h1 (TripA.d PQR) (a.1, a.2))); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => (Bivar.snd (TripA.d PQR)) (a1, a2) * CondEntropy.h1 (TripA.d PQR) (a1, a2))) /=.
rewrite exchange_big pair_big /=; apply eq_bigr => -[c b] _ /=; congr (_ * _).
  by rewrite TripC23.sndA Swap.dE.
by rewrite h1TripC23.
Qed.

End conditional_entropy_prop3.

Module conditional_entropy_example.

Definition zero : 'I_4 := ord0.
Definition one : 'I_4 := @Ordinal 4 1 isT.
Definition two : 'I_4 := @Ordinal 4 2 isT.
Definition three : 'I_4 := @Ordinal 4 3 isT.

Definition f := [ffun x : 'I_4 * 'I_4 => [eta (fun=>0) with
(zero, zero) |-> (1/8), (zero, one) |-> (1/16), (zero, two) |-> (1/16), (zero, three) |-> (1/4),
(one, zero) |-> (1/16), (one, one) |-> (1/8), (one, two) |-> (1/16), (one, three) |-> 0,
(two, zero) |-> (1/32), (two, one) |-> (1/32), (two, two) |-> (1/16), (two, three) |-> 0,
(three, zero) |-> (1/32), (three, one) |-> (1/32), (three, two) |-> (1/16), (three, three) |-> 0] x].

Lemma f0 : forall x, 0 <= f x.
Proof.
move=> x; rewrite ffunE; move: x.
case => -[ [? [[|[|[|[|[]//]]]]]
  | [? [[|[|[|[|[]//]]]]]
  | [? [[|[|[|[|[]//]]]]]
  | [? [[|[|[|[|[]//]]]]] | []//]]]]]; rewrite /f /=; try lra.
Qed.

Lemma f1 : \rsum_(x in {: 'I_4 * 'I_4}) f x = 1.
Proof.
rewrite (eq_bigr (fun x => f (x.1, x.2))); last by case.
rewrite -(pair_bigA _ (fun x1 x2 => f (x1, x2))) /=.
rewrite !big_ord_recl !big_ord0 /f /= !ffunE /=; field.
Qed.

Definition d : {dist 'I_4 * 'I_4} := locked (makeDist f0 f1).

Lemma dE x : d x = f x.
Proof. by rewrite /d; unlock. Qed.

Definition conditional_entropy := CondEntropy.h d.

Lemma conditional_entropyE : conditional_entropy = 11/8.
Proof.
rewrite /conditional_entropy /CondEntropy.h /=.
rewrite !big_ord_recl big_ord0 !Bivar.sndE /=.
rewrite !big_ord_recl !big_ord0 !dE /f /=.
rewrite /CondEntropy.h1 /=.
rewrite !big_ord_recl !big_ord0 /cPr /Pr !(big_setX,big_set1) !dE /f /=.
rewrite !Bivar.sndE /=.
rewrite !big_ord_recl !big_ord0 !dE /f !ffunE /=.
rewrite !(addR0,add0R,div0R,mul0R).
repeat (rewrite logDiv; try lra).
rewrite !log1 !sub0R !log4 !log8 !log16 !log32.
rewrite [X in log X](_ : _ = 1/4); last lra.
rewrite !div1R logV; last lra.
rewrite !log4.
rewrite [X in log X](_ : _ = 1/4); last lra.
rewrite !div1R logV; last lra.
rewrite !log4.
rewrite [X in log X](_ : _ = 1/4); last lra.
rewrite !div1R logV; last lra.
rewrite !log4.
field.
Qed.

End conditional_entropy_example.

Section chain_rule.
Variables (A B : finType) (PQ : {dist A * B}).
Let P := Bivar.fst PQ.
Let QP := Swap.d PQ.

(* thm 2.1.1 *)
Lemma chain_rule : JointEntropy.h PQ = `H P + CondEntropy.h QP. (* 2.14 *)
Proof.
rewrite /JointEntropy.h {1}/entropy.
transitivity (- (\rsum_(a in A) \rsum_(b in B)
    PQ (a, b) * log (P a * \Pr_QP [ [set b] | [set a] ]))). (* 2.16 *)
  congr (- _); rewrite pair_big /=; apply eq_bigr => -[a b] _ /=.
  congr (_ * log _); case/boolP : (P a == 0) => [/eqP|] H0.
  - by rewrite (Bivar.dom_by_fst _ H0) H0 mul0R.
  - by rewrite -(Pr_set1 P a) /P -(Swap.snd PQ) mulRC -Pr_cPr setX1 Pr_set1 Swap.dE.
transitivity (
  - (\rsum_(a in A) \rsum_(b in B) PQ (a, b) * log (P a))
  - (\rsum_(a in A) \rsum_(b in B) PQ (a, b) * log (\Pr_QP [ [set b] | [set a] ]))). (* 2.17 *)
  rewrite -oppRB; congr (- _); rewrite -addR_opp oppRK -big_split /=.
  apply eq_bigr => a _; rewrite -big_split /=; apply eq_bigr => b _.
  case/boolP : (PQ (a, b) == 0) => [/eqP H0|H0].
  - by rewrite H0 !mul0R addR0.
  - rewrite -mulRDr; congr (_ * _); rewrite mulRC logM //.
    by rewrite -cPr_Pr_setX_gt0 setX1 Pr_set1 Swap.dE -dist_gt0.
    rewrite -dist_gt0; exact: Bivar.dom_by_fstN H0.
rewrite [in X in _ + X = _]big_morph_oppR; congr (_ + _).
- rewrite /entropy; congr (- _); apply eq_bigr => a _.
  by rewrite -big_distrl /= -Bivar.fstE.
- rewrite CondEntropy.hE big_morph_oppR.
  apply eq_bigr => a _; congr (- _); apply eq_bigr => b _; by rewrite !Swap.dE.
Qed.

End chain_rule.

Section chain_rule_generalization.

(* TODO: move *)
Lemma to_bivar_entropy (A : finType) (n : nat) (P : {dist 'rV[A]_n.+1}) :
  `H P = `H (Multivar.to_bivar P).
Proof.
rewrite /entropy /=; congr (- _).
apply/esym.
rewrite (eq_bigr (fun a => (Multivar.to_bivar P) (a.1, a.2) * log ((Multivar.to_bivar P) (a.1, a.2)))); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => (Multivar.to_bivar P) (a1, a2) * log ((Multivar.to_bivar P) (a1, a2)))) /=.
rewrite -(big_rV_cons_behead _ xpredT xpredT) /=.
apply eq_bigr => a _; apply eq_bigr => v _.
by rewrite Multivar.to_bivarE /=.
Qed.

Local Open Scope ring_scope.

(* TODO: move *)
Definition put_front (n : nat) (i : 'I_n.+1) : 'I_n.+1 -> 'I_n.+1 := fun j =>
  if j == i then ord0 else
    if (j < i)%nat then inord (j.+1) else
      j.

Definition put_back (n : nat) (i : 'I_n.+1) : 'I_n.+1 -> 'I_n.+1 := fun j =>
  if j == ord0 then i else
    if (j <= i)%nat then inord (j.-1) else
      j.

Lemma put_front_inj (n : nat) (i : 'I_n.+1) : injective (put_front i).
Proof.
apply: (@can_inj _ _ (put_front i) (put_back i)) => j.
rewrite /put_back /put_front; case: (ifPn (j == i)) => [ji|].
  rewrite eqxx; exact/esym/eqP.
rewrite neq_ltn => /orP[|] ji.
  rewrite ji ifF; last first.
    apply/negbTE/eqP => /(congr1 val) => /=.
    by rewrite inordK // ltnS (leq_trans ji) // -ltnS.
  rewrite inordK; last by rewrite ltnS (leq_trans ji) // -ltnS.
  by rewrite ji /=; apply val_inj => /=; rewrite inordK.
rewrite ltnNge (ltnW ji) /= ifF; last first.
  by apply/negbTE; rewrite -lt0n (leq_trans _ ji).
by rewrite leqNgt ji.
Qed.

Definition put_front_perm (n : nat) i : 'S_n.+1 := perm (@put_front_inj n i).

(* TODO: clean *)
Lemma chain_rule_multivar (A : finType) (n : nat) (P : {dist 'rV[A]_n.+1}) (i : 'I_n.+1) :
  i != ord0 ->
  (`H P = `H (MargDist.d P i) + CondEntropy.h (Multivar.to_bivar (MultivarPerm.d P (put_front_perm i))))%R.
Proof.
move=> i0.
rewrite -(Swap.dI (Multivar.to_bivar _)).
set PQ : {dist 'rV[A]_n * A} := Swap.d (Multivar.to_bivar _).
have -> : MargDist.d P i = Bivar.fst PQ.
  apply/dist_ext => /= v.
  rewrite MargDist.dE.
  rewrite Bivar.fstE.
  rewrite {}/PQ.
  apply/esym; evar (f : A -> R); rewrite (eq_bigr f); last first.
    move=> a _; rewrite Swap.dE /f; reflexivity.
  rewrite {}/f.
  apply/esym.
  destruct n as [|n']; first by rewrite (ord1 i) eqxx in i0.
  transitivity (\rsum_(x : A) P
    (\row_(k < n'.+2) (if k == i then x else v ``_ (inord (unbump i k)))))%R.
    rewrite (reindex_onto (fun a => \row_k (if k == i then a else v ``_ (inord (unbump i k))))
      (fun w => w ``_ i)); last first.
      move=> w wv.
      apply/rowP => j.
      rewrite !mxE; case: ifPn => [/eqP -> //|ji].
      rewrite -(eqP wv) mxE; congr (w _ _).
      move: ji; rewrite neq_ltn => /orP[|] ji.
        apply val_inj => /=.
        rewrite inordK; last first.
          by rewrite /unbump (ltnNge i j) (ltnW ji) subn0 (leq_trans ji) // -ltnS.
        by rewrite unbumpK //= inE ltn_eqF.
      apply val_inj => /=.
      rewrite inordK; last first.
        rewrite /unbump ji subn1 prednK //; by [rewrite -ltnS | rewrite (leq_ltn_trans _ ji)].
      by rewrite unbumpK //= inE gtn_eqF.
    apply eq_bigl => a /=.
    apply/andP; split.
      apply/eqP/rowP => k.
      rewrite !mxE eq_sym (negbTE (neq_lift _ _)).
      congr (v _ _).
      apply val_inj => /=.
      by rewrite bumpK inordK.
    by rewrite mxE eqxx.
  transitivity (\rsum_(i1 in A) (MultivarPerm.d P (put_front_perm i)) (row_mx (\row_(i < 1) i1) v)); last first.
    apply eq_bigr => a _.
    by rewrite Multivar.to_bivarE.
  apply/esym; evar (f : A -> R); rewrite (eq_bigr f); last first.
    move=> a _.
    rewrite MultivarPerm.dE /f; reflexivity.
  rewrite {}/f.
  apply/eq_bigr => a _.
  congr (P _); apply/rowP => k.
  rewrite /col_perm /= 2!mxE /=.
  rewrite /put_front_perm /= permE /put_front.
  case: ifPn => [ki|]; first by rewrite row_mx_row_ord0.
  rewrite neq_ltn => /orP[|] ki.
    rewrite ki mxE; case: splitP => [j|j].
      by rewrite (ord1 j) inordK // (leq_ltn_trans _ (ltn_ord i)).
   rewrite inordK; last by rewrite (leq_ltn_trans _ (ltn_ord i)).
   rewrite add1n => -[] kj.
   congr (v _ _); apply val_inj => /=.
   rewrite /unbump ltnNge (ltnW ki) subn0 inordK; last first.
      rewrite (_ : nat_of_ord k = nat_of_ord j) //.
      by rewrite kj.
   rewrite ltnNge (ltnW ki) /= mxE; case: splitP => [j|k' kk'].
     rewrite (ord1 j){j} => k0.
     by rewrite k0 ltn0 in ki.
   congr (v _ _).
   apply val_inj => /=.
   rewrite kk' /unbump -kk' ki subn1 inordK.
   by rewrite kk' add1n.
   rewrite prednK //.
   by rewrite -ltnS.
   by rewrite (leq_ltn_trans _ ki).
by rewrite -chain_rule JointEntropy.hC Swap.dI -to_bivar_entropy -MultivarPerm.entropy.
Qed.

End chain_rule_generalization.

Section entropy_chain_rule_corollary.
Variables (A B C : finType) (PQR : {dist A * B * C}).
Let PR : {dist A * C} := Proj13.d PQR.
Let QPR : {dist B * (A * C)} := TripA.d (TripC12.d PQR).

(* eqn 2.21, H(X,Y|Z) = H(X|Z) + H(Y|X,Z) *)
Lemma chain_rule_corollary :
  CondEntropy.h PQR = CondEntropy.h PR + CondEntropy.h QPR.
Proof.
rewrite !CondEntropy.hE -oppRD; congr (- _).
rewrite [in X in _ = _ + X](eq_bigr (fun j => \rsum_(i in B) (Swap.d QPR) ((j.1, j.2), i) * log \Pr_QPR[[set i] | [set (j.1, j.2)]])); last by case.
rewrite -[in RHS](pair_bigA _ (fun j1 j2 => \rsum_(i in B) (Swap.d QPR ((j1, j2), i) * log \Pr_QPR[[set i] | [set (j1, j2)]]))) /=.
rewrite [in X in _ = _ + X]exchange_big /= -big_split; apply eq_bigr => c _ /=.
rewrite [in LHS](eq_bigr (fun j => (Swap.d PQR) (c, (j.1, j.2)) * log \Pr_PQR[[set (j.1, j.2)] | [set c]])); last by case.
rewrite -[in LHS](pair_bigA _ (fun j1 j2 => (Swap.d PQR) (c, (j1, j2)) * log \Pr_PQR[[set (j1, j2)] | [set c]])) /=.
rewrite -big_split; apply eq_bigr => a _ /=.
rewrite Swap.dE Proj13.dE big_distrl /= -big_split; apply eq_bigr => b _ /=.
rewrite !(Swap.dE,TripA.dE,TripC12.dE) /= -mulRDr.
case/boolP : (PQR (a, b, c) == 0) => [/eqP H0|H0].
  by rewrite H0 !mul0R.
rewrite -logM; last 2 first.
  rewrite -cPr_Pr_setX_gt0 Pr_gt0 setX1 Pr_set1; exact: Proj13.dominN H0.
  by rewrite -cPr_Pr_setX_gt0 Pr_gt0 setX1 Pr_set1 TripA.dE /= TripC12.dE.
congr (_ * log _).
by rewrite -setX1 product_ruleC !setX1 mulRC.
Qed.

End entropy_chain_rule_corollary.

Section conditional_entropy_prop. (* NB: here because use chain rule *)

Variables (A B : finType) (PQ : {dist A * B}).
Let P := Bivar.fst PQ.
Let Q := Bivar.snd PQ.
Let QP := Swap.d PQ.

Lemma entropyB : `H P - CondEntropy.h PQ = `H Q - CondEntropy.h QP.
Proof.
rewrite subR_eq addRAC -subR_eq subR_opp -chain_rule JointEntropy.hC.
by rewrite -/(JointEntropy.h (Swap.d PQ)) chain_rule Swap.fst -/Q Swap.dI.
Qed.

End conditional_entropy_prop.

Section conditional_entropy_prop2. (* NB: here because use chain rule *)

Variables (A : finType) (P : {dist A}).

Lemma CondEntrop_self : CondEntropy.h (Self.d P) = 0.
Proof.
move: (@chain_rule _ _ (Self.d P)).
rewrite !Self.fst Self.swap addRC -subR_eq => <-.
by rewrite /JointEntropy.h joint_entropy_self subRR.
Qed.

End conditional_entropy_prop2.

Module MutualInfo.
Local Open Scope divergence_scope.
Section def.
Variables (A B : finType) (PQ : {dist A * B}).
Let P := Bivar.fst PQ.
Let Q := Bivar.snd PQ.
Let QP := Swap.d PQ.

(* I(X;Y) *)
Definition mi := D(PQ || P `x Q).
End def.
Section prop.
Variables (A B : finType) (PQ : {dist A * B}).
Let P := Bivar.fst PQ.
Let Q := Bivar.snd PQ.
Let QP := Swap.d PQ.

(* 2.28 *)
Lemma miE : mi PQ =
  \rsum_(a in A) \rsum_(b in B) PQ (a, b) * log (PQ (a, b) / (P a * Q b)).
Proof.
rewrite /mi /div pair_big /=; apply eq_bigr; case => a b _ /=.
case/boolP : (PQ (a, b) == 0) => [/eqP H0|H0].
- by rewrite H0 !mul0R.
- by rewrite ProdDist.dE.
Qed.

(* 2.39 *)
Lemma miE2 : mi PQ = `H P - CondEntropy.h PQ.
Proof.
rewrite miE.
transitivity (\rsum_(a in A) \rsum_(b in B)
    PQ (a, b) * log (\Pr_PQ [ [set a] | [set b] ] / P a)).
  apply eq_bigr => a _; apply eq_bigr => b _.
  rewrite /cPr setX1 2!Pr_set1 /= -/Q.
  case/boolP : (PQ (a, b) == 0) => [/eqP H0 | H0].
  - by rewrite H0 !mul0R.
  - congr (_ * log _).
    rewrite divRM; last 2 first.
      apply/eqP; exact: Bivar.dom_by_fstN H0.
      apply/eqP; exact: Bivar.dom_by_sndN H0.
    by rewrite mulRAC.
transitivity (- (\rsum_(a in A) \rsum_(b in B) PQ (a, b) * log (P a)) +
  \rsum_(a in A) \rsum_(b in B) PQ (a, b) * log (\Pr_PQ [ [set a] | [set b] ])). (* 2.37 *)
  rewrite big_morph_oppR -big_split; apply/eq_bigr => a _ /=.
  rewrite big_morph_oppR -big_split; apply/eq_bigr => b _ /=.
  rewrite addRC -mulRN -mulRDr addR_opp.
  case/boolP : (PQ (a, b) == 0) => [/eqP ->| H0].
  - by rewrite !mul0R.
  - congr (_ * _); rewrite logDiv //.
    + by rewrite -cPr_Pr_setX_gt0 Pr_gt0 setX1 Pr_set1.
    + rewrite -dist_gt0; exact: Bivar.dom_by_fstN H0.
rewrite -subR_opp; congr (_ - _).
- rewrite /entropy; congr (- _); apply/eq_bigr => a _.
  by rewrite -big_distrl /= -Bivar.fstE.
- rewrite /CondEntropy.h exchange_big.
  rewrite big_morph_oppR; apply eq_bigr=> b _ /=.
  rewrite mulRN; congr (- _).
  rewrite big_distrr /=; apply eq_bigr=> a _ /=.
  rewrite mulRA; congr (_ * _); rewrite -/Q.
  by rewrite -[in LHS]Pr_set1 -setX1 Pr_cPr Pr_set1 -/Q mulRC.
Qed.

Lemma miE3 : mi PQ = `H Q - CondEntropy.h QP. (* 2.40 *)
Proof. by rewrite miE2 entropyB. Qed.

Lemma miE4 : mi PQ = `H P + `H Q - `H PQ. (* 2.41 *)
Proof.
rewrite miE2; move: (chain_rule QP).
rewrite addRC -subR_eq -(Swap.dI PQ) -/QP => <-.
by rewrite -addR_opp oppRB Swap.fst -/Q addRA JointEntropy.hC.
Qed.

(* nonnegativity of mutual information 2.90 *)
Lemma mi_ge0 : 0 <= mi PQ.
Proof. exact/div_ge0/Prod_dominates_Joint. Qed.

Lemma mi0P : mi PQ = 0 <-> PQ = P `x Q.
Proof.
split; last by rewrite /mi => <-; rewrite div0P //; exact: dominatesxx.
rewrite /mi div0P //; exact: Prod_dominates_Joint.
Qed.
End prop.
End MutualInfo.

(* TODO: example 2.3.1 *)

Section mutualinfo_prop.

Local Open Scope divergence_scope.

(* eqn 2.46 *)
Lemma mi_sym (A B : finType) (PQ : {dist A * B}) :
  let P := Bivar.fst PQ in
  let Q := Bivar.snd PQ in
  MutualInfo.mi PQ = MutualInfo.mi (Swap.d PQ).
Proof.
by move=> P Q; rewrite !MutualInfo.miE2 entropyB Swap.fst.
Qed.

(* eqn 2.47 *)
Lemma mutual_info_self (A : finType) (P : dist A) :
  MutualInfo.mi (Self.d P) = `H P.
Proof.
by rewrite MutualInfo.miE2 CondEntrop_self subR0 Self.fst.
Qed.

End mutualinfo_prop.

Section chain_rule_for_entropy.

Local Open Scope vec_ext_scope.

Lemma entropy_head_of1 (A : finType) (P : {dist 'M[A]_1}) :
  `H P = `H (Multivar.head_of P).
Proof.
rewrite /entropy; congr (- _); apply: big_rV_1 => // a.
rewrite /Multivar.head_of Bivar.fstE /= (big_rV_0 _ _ (a ``_ ord0)).
rewrite Multivar.to_bivarE /=; congr (P _ * log (P _)).
- apply/rowP => i.
  by rewrite (ord1 i) !mxE; case: splitP => // i0; rewrite (ord1 i0) mxE.
- apply/rowP => i.
  by rewrite (ord1 i) !mxE; case: splitP => // i0; rewrite (ord1 i0) mxE.
Qed.

(* thm 2.5.1 *)
Lemma chain_rule_rV (A : finType) (n : nat) (P : {dist 'rV[A]_n.+1}) :
  `H P = \rsum_(i < n.+1)
          if i == O :> nat then
            `H (Multivar.head_of P)
          else
            CondEntropy.h (Swap.d (Multivar.belast_last (Take.d P (lift ord0 i)))).
Proof.
elim: n P => [P|n IH P].
  by rewrite big_ord_recl /= big_ord0 addR0 -entropy_head_of1.
transitivity (JointEntropy.h (Multivar.belast_last P)).
  (* TODO: lemma? *)
  rewrite /JointEntropy.h /entropy; congr (- _) => /=.
  rewrite -(big_rV_belast_last _ xpredT xpredT) /=.
  rewrite pair_big /=; apply eq_bigr => -[a b] _ /=.
  by rewrite Multivar.belast_lastE.
rewrite chain_rule {}IH [in RHS]big_ord_recr /=; congr (_ + _); last first.
  by rewrite Take.all.
apply eq_bigr => i _.
case: ifP => i0.
  rewrite /entropy; congr (- _).
  apply eq_bigr => a _; by rewrite head_of_fst_belast_last.
congr (CondEntropy.h (Swap.d (Multivar.belast_last _))).
rewrite /Take.d /Bivar.fst /Multivar.belast_last !DistMap.comp.
congr (DistMap.d _ P).
apply FunctionalExtensionality.functional_extensionality => /= v.
apply/rowP => j; rewrite !mxE !castmxE /= !mxE /= cast_ord_id; congr (v _ _).
exact: val_inj.
Qed.

End chain_rule_for_entropy.

Section divergence_conditional_distributions.

Variables (A B C : finType) (PQR : {dist A * B * C}).

Definition cdiv1 z := \rsum_(x in {: A * B})
  \Pr_PQR[[set x] | [set z]] * log (\Pr_PQR[[set x] | [set z]] /
    (\Pr_(Proj13.d PQR)[[set x.1] | [set z]] * \Pr_(Proj23.d PQR)[[set x.2] | [set z]])).

Local Open Scope divergence_scope.

Lemma cdiv1_is_div c (Hc : _) (Hc1 : _) (Hc2 : _) :
  cdiv1 c = D(CondDist.d (Swap.d PQR) c Hc ||
    (CondDist.d (Swap.d (Proj13.d PQR)) c Hc1) `x (CondDist.d (Swap.d (Proj23.d PQR)) c Hc2)).
Proof.
rewrite /cdiv1 /div; apply eq_bigr => -[a b] /= _; rewrite CondDist.dE.
rewrite Swap.dI.
case/boolP : (\Pr_PQR[[set (a, b)]|[set c]] == 0) => [/eqP ->|H0].
  by rewrite !mul0R.
by rewrite ProdDist.dE /= 2!CondDist.dE !Swap.dI.
Qed.

Lemma cdiv1_ge0 z : 0 <= cdiv1 z.
Proof.
case/boolP : ((Bivar.snd PQR) z == 0) => [/eqP|] z0.
  apply rsumr_ge0 => -[a b] _.
  rewrite {1}/cPr setX1 Pr_set1 (Bivar.dom_by_snd _ z0) div0R mul0R.
  exact: leRR.
rewrite cdiv1_is_div.
  by rewrite Swap.fst.
  by rewrite Swap.fst Proj13.snd.
  by rewrite Swap.fst Proj23.snd.
move=> ? Hz1 Hz2; apply div_ge0.
(* TODO: lemma *)
apply/dominatesP => -[a b].
rewrite ProdDist.dE !CondDist.dE /= mulR_eq0 => -[|].
- rewrite /cPr !setX1 !Pr_set1 !mulR_eq0 => -[|].
  rewrite !Swap.dI.
  move/Proj13.domin => ->; by left.
  rewrite !Swap.dI.
  rewrite Proj13.snd /Rdiv => ->; by right.
- rewrite /cPr !setX1 !Pr_set1 !mulR_eq0 => -[|].
  rewrite !Swap.dI.
  move/Proj23.domin => ->; by left.
  rewrite !Swap.dI.
  rewrite Proj23.snd => ->; by right.
Qed.

End divergence_conditional_distributions.

Section conditional_mutual_information.
Section def.
Variables (A B C : finType) (PQR : {dist A * B * C}).

(* I(X;Y|Z) = H(X|Z) - H(X|Y,Z) 2.60 *)
Definition cmi := CondEntropy.h (Proj13.d PQR) - CondEntropy.h (TripA.d PQR).
End def.
Section prop.
Variables (A B C : finType) (PQR : {dist A * B * C}).
Lemma cmiE : cmi PQR = \rsum_(x in {: A * B * C}) PQR x *
  log (\Pr_PQR[[set x.1] | [set x.2]] /
       (\Pr_(Proj13.d PQR)[[set x.1.1] | [set x.2]] * \Pr_(Proj23.d PQR)[[set x.1.2] | [set x.2]])).
Proof.
rewrite /cmi 2!CondEntropy.hE /= subR_opp big_morph_oppR.
rewrite (eq_bigr (fun a => \rsum_(b in A) (Swap.d (TripA.d PQR)) (a.1, a.2, b) * log \Pr_(TripA.d PQR)[[set b] | [set (a.1, a.2)]])); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => \rsum_(b in A) (Swap.d (TripA.d PQR)) ((a1, a2), b) * log \Pr_(TripA.d PQR)[[set b] | [set (a1, a2)]])).
rewrite exchange_big -big_split /=.
rewrite (eq_bigr (fun x => PQR (x.1, x.2) * log
(\Pr_PQR[[set x.1] | [set x.2]] /
        (\Pr_(Proj13.d PQR)[[set x.1.1] | [set x.2]] * \Pr_(Proj23.d PQR)[[set x.1.2] | [set x.2]])))); last by case.
rewrite -(pair_bigA _ (fun x1 x2 => PQR (x1, x2) * log
(\Pr_PQR[[set x1] | [set x2]] /
        (\Pr_(Proj13.d PQR)[[set x1.1] | [set x2]] * \Pr_(Proj23.d PQR)[[set x1.2] | [set x2]])))).
rewrite /= exchange_big; apply eq_bigr => c _.
rewrite big_morph_oppR /= exchange_big -big_split /=.
rewrite (eq_bigr (fun i => PQR ((i.1, i.2), c) * log
       (\Pr_PQR[[set (i.1, i.2)] | [set c]] /
        (\Pr_(Proj13.d PQR)[[set i.1] | [set c]] * \Pr_(Proj23.d PQR)[[set i.2] | [set c]])))); last by case.
rewrite -(pair_bigA _ (fun i1 i2 => PQR (i1, i2, c) * log
  (\Pr_PQR[[set (i1, i2)] | [set c]] /
  (\Pr_(Proj13.d PQR)[[set i1] | [set c]] * \Pr_(Proj23.d PQR)[[set i2] | [set c]])))).
apply eq_bigr => a _ /=.
rewrite Swap.dE Proj13.dE big_distrl /= big_morph_oppR -big_split.
apply eq_bigr => b _ /=.
rewrite Swap.dE TripA.dE /= -mulRN -mulRDr.
case/boolP : (PQR (a, b, c) == 0) => [/eqP ->| H0]; first by rewrite !mul0R.
congr (_ * _).
rewrite addRC addR_opp -logDiv; last 2 first.
  rewrite -cPr_Pr_setX_gt0 Pr_gt0 setX1 Pr_set1; exact: TripA.dominN H0.
  rewrite -cPr_Pr_setX_gt0 Pr_gt0 setX1 Pr_set1; exact: Proj13.dominN H0.
congr (log _).
rewrite divRM; last 2 first.
  apply/eqP.
  rewrite -cPr_gt0 -cPr_Pr_setX_gt0 Pr_gt0 setX1 Pr_set1; exact: Proj13.dominN H0.
  apply/eqP.
  rewrite -cPr_gt0 -cPr_Pr_setX_gt0 Pr_gt0 setX1 Pr_set1; exact: Proj23.dominN H0.
rewrite {2}/Rdiv -mulRA mulRCA {1}/Rdiv [in LHS]mulRC; congr (_ * _).
rewrite -[in X in _ = X * _]setX1 product_rule setX1 -mulRA mulRV ?mulR1 //.
rewrite /cPr mulR_neq0' setX1 !Pr_set1; apply/andP; split.
exact: Proj23.dominN H0.
rewrite invR_neq0' // Proj23.snd; exact: Bivar.dom_by_sndN H0.
Qed.

Let R := Bivar.snd PQR.

Lemma cmiE2 : cmi PQR = \rsum_(z in C) R z * cdiv1 PQR z.
Proof.
rewrite cmiE.
rewrite (eq_bigr (fun x => PQR (x.1, x.2) * log
  (\Pr_PQR[[set x.1] | [set x.2]] /
    (\Pr_(Proj13.d PQR)[[set x.1.1] | [set x.2]] * \Pr_(Proj23.d PQR)[[set x.1.2] | [set x.2]])))); last by case.
rewrite -(pair_bigA _ (fun x1 x2 => PQR (x1, x2) * log
  (\Pr_PQR[[set x1] | [set x2]] /
    (\Pr_(Proj13.d PQR)[[set x1.1] | [set x2]] * \Pr_(Proj23.d PQR)[[set x1.2] | [set x2]])))).
rewrite exchange_big; apply eq_bigr => c _ /=.
rewrite big_distrr /=; apply eq_bigr => -[a b] _ /=; rewrite mulRA; congr (_ * _).
rewrite mulRC.
move: (Pr_cPr PQR [set (a, b)] [set c]); rewrite -/R Pr_set1 => <-.
by rewrite setX1 Pr_set1.
Qed.

(* 2.92 *)
Lemma cmi_ge0 : 0 <= cmi PQR.
Proof.
rewrite cmiE2; apply rsumr_ge0 => c _.
apply mulR_ge0; [exact: dist_ge0 | exact: cdiv1_ge0].
Qed.

Let P : dist A := Bivar.fst (TripA.d PQR).
Let Q : dist B := Bivar.snd (Bivar.fst PQR).

Lemma chain_rule_mi : MutualInfo.mi PQR = MutualInfo.mi (Proj13.d PQR) + cmi (Swap.d (TripA.d PQR)).
Proof.
rewrite MutualInfo.miE2.
move: (chain_rule (Bivar.fst PQR)); rewrite /JointEntropy.h => ->.
have -> : CondEntropy.h PQR = CondEntropy.h (Proj13.d PQR) + CondEntropy.h (TripA.d (TripC12.d PQR)).
  by rewrite chain_rule_corollary.
rewrite -addR_opp oppRD addRCA 2!addRA -(addRA (- _ + _)) addR_opp; congr (_ + _).
  rewrite MutualInfo.miE2 addRC; congr (_ - _).
  by rewrite Proj13.fst TripA.fst.
rewrite /cmi; congr (CondEntropy.h _ - _).
  by rewrite /Proj13.d -/(TripC13.d _) TripC13.sndA.
(* TODO: lemma *)
rewrite /CondEntropy.h.
rewrite (eq_bigr (fun a => (Bivar.snd (TripA.d (TripC12.d PQR))) (a.1, a.2) * CondEntropy.h1 (TripA.d (TripC12.d PQR)) (a.1, a.2))); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => (Bivar.snd (TripA.d (TripC12.d PQR))) (a1, a2) * CondEntropy.h1 (TripA.d (TripC12.d PQR)) (a1, a2))).
rewrite exchange_big pair_big; apply eq_bigr => -[c a] _ /=; congr (_ * _).
  rewrite !Bivar.sndE; apply eq_bigr => b _.
  by rewrite !(Swap.dE,TripA.dE,TripC12.dE).
rewrite /CondEntropy.h1; congr (- _).
apply eq_bigr => b _.
by rewrite -setX1 cPr_TripA_TripC12 setX1.
Qed.
End prop.
End conditional_mutual_information.

Section conditional_relative_entropy.
Section def.
Variables (A B : finType) (P Q : CDist.t A B).
Let Pj : {dist B * A} := Swap.d (CDist.joint_of P).
Let Qj : {dist B * A} := Swap.d (CDist.joint_of Q).
Let P1 : {dist A} := CDist.P P.

(* eqn 2.65 *)
Definition cre := \rsum_(x in A) P1 x * \rsum_(y in B)
  \Pr_Pj[[set y]|[set x]] * log (\Pr_Pj[[set y]|[set x]] / \Pr_Qj[[set y]|[set x]]).
End def.

Section prop.
Local Open Scope divergence_scope.
Local Open Scope reals_ext_scope.
Variables (A B : finType) (P Q : CDist.t A B).
Let Pj : {dist B * A} := Swap.d (CDist.joint_of P).
Let Qj : {dist B * A} := Swap.d (CDist.joint_of Q).
Let P1 : {dist A} := CDist.P P.
Let Q1 : {dist A} := CDist.P Q.

(* thm 2.5.3 *)
Lemma chain_rule_relative_entropy : Pj << Qj -> D(Pj || Qj) = D(P1 || Q1) + cre P Q.
Proof.
move=> PQ.
rewrite {2}/div /cre -big_split /= {1}/div /=.
rewrite (eq_bigr (fun a => Pj (a.1, a.2) * (log (Pj (a.1, a.2) / (Qj (a.1, a.2)))))); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => Pj (a1, a2) * (log (Pj (a1, a2) / (Qj (a1, a2)))))) /=.
rewrite exchange_big; apply eq_bigr => a _ /=.
rewrite [in X in _ = X * _ + _](_ : P1 a = Bivar.snd Pj a); last first.
  by rewrite /P Swap.snd ProdDist.fst.
rewrite Bivar.sndE big_distrl /= big_distrr /= -big_split /=; apply eq_bigr => b _.
rewrite mulRA (_ : P1 a * _ = Pj (b, a)); last first.
  rewrite /cPr Pr_set1 -/P1 mulRCA setX1 Pr_set1 {1}/Pj Swap.snd ProdDist.fst.
  case/boolP : (P1 a == 0) => [/eqP|] P2a0.
    have Pba0 : Pj (b, a) = 0 by rewrite /P Swap.dE ProdDist.dE P2a0 mul0R.
    by rewrite Pba0 mul0R.
  by rewrite mulRV // ?mulR1.
rewrite -mulRDr.
case/boolP : (Pj (b, a) == 0) => [/eqP ->|H0]; first by rewrite !mul0R.
congr (_ * _).
have P1a0 : P1 a != 0.
  apply: contra H0 => /eqP.
  rewrite /P Swap.dE ProdDist.dE => ->; by rewrite mul0R.
have Qba0 := dominatesEN PQ H0.
have Q2a0 : Q1 a != 0.
  apply: contra Qba0; rewrite /Q Swap.dE ProdDist.dE => /eqP ->; by rewrite mul0R.
rewrite -logM; last 2 first.
  by apply/divR_gt0; rewrite -dist_gt0.
  apply/divR_gt0; by rewrite -cPr_Pr_setX_gt0 setX1 Pr_set1 -dist_gt0.
congr (log _).
rewrite /cPr !setX1 !Pr_set1.
rewrite !Swap.dE !Swap.snd !ProdDist.fst !ProdDist.dE /=.
rewrite -/P1 -/Q1; field.
split; first exact/eqP.
split; first exact/eqP.
apply/eqP.
apply: contra Qba0; rewrite /Qj Swap.dE ProdDist.dE /= => /eqP ->; by rewrite mulR0.
Qed.
End prop.
End conditional_relative_entropy.

Section chain_rule_for_information. (* thm 2.5.1 *)

Variables (A : finType).
Let B := A. (* need in the do-not-delete-me step *)
Variables (n : nat) (PY : {dist 'rV[A]_n.+1 * B}).
Let P : {dist 'rV[A]_n.+1} := Bivar.fst PY.
Let Y : {dist B} := Bivar.snd PY.

Let f (i : 'I_n.+1) : {dist A * 'rV[A]_i * B} := TripC12.d (PairTake.d PY i).
Let f23 (i : 'I_n.+1) : {dist A * B * 'rV[A]_i} := TripC23.d (f i).
Let fA (i : 'I_n.+1) : {dist A * ('rV[A]_i * B)} := TripA.d (f i).

Local Open Scope vec_ext_scope.

Lemma chain_rule_information :
  (* 2.62 *) MutualInfo.mi PY = \rsum_(i < n.+1)
    if i == O :> nat then
      MutualInfo.mi (PairNth.d PY ord0)
    else
      cmi (f23 i).
Proof.
rewrite MutualInfo.miE2 chain_rule_rV.
have -> : CondEntropy.h PY = \rsum_(j < n.+1)
  if j == O :> nat then
    CondEntropy.h (PairNth.d PY ord0)
  else
    CondEntropy.h (fA j).
  move: (chain_rule (Swap.d PY)).
  rewrite Swap.dI addRC -subR_eq Swap.fst -/Y => <-.
  rewrite /JointEntropy.h.
  (* do-not-delete-me *)
  set YP : {dist 'rV[A]_n.+2} := Multivar.from_bivar (Swap.d PY).
  transitivity (`H YP - `H Y); first by rewrite /YP entropy_from_bivar.
  rewrite (chain_rule_rV YP).
  rewrite [in LHS]big_ord_recl /=.
  rewrite (_ : `H (Multivar.head_of YP) = `H Y); last first.
    by rewrite /YP /Multivar.head_of (Multivar.from_bivarK (Swap.d PY)) Swap.fst.
  rewrite addRC addRK.
  apply eq_bigr => j _.
  case: ifPn => j0.
  - have {j0}j0 : j = ord0 by move: j0 => /eqP j0; exact/val_inj.
    subst j.
    rewrite /CondEntropy.h /=.
    apply big_rV_1 => // a1.
    have H1 : forall a,
     (Swap.d (Multivar.belast_last (Take.d YP (lift ord0 (lift ord0 ord0))))) (a, a1) =
     (PairNth.d PY ord0) (a, a1 ``_ ord0).
      move=> a.
      rewrite Swap.dE Multivar.belast_lastE (Take.dE _ (lift ord0 (lift ord0 ord0))) PairNth.dE /=.
      have H1 : (n.+2 - bump 0 (bump 0 0) = n)%nat by rewrite /bump !leq0n !add1n subn2.
      rewrite (big_cast_rV H1).
      rewrite (eq_bigr (fun x => PY (x.1, x.2))); last by case.
      rewrite -(pair_big (fun i : 'rV_n.+1 => i ``_ ord0 == a) (fun i => i == a1 ``_ ord0) (fun i1 i2 => PY (i1, i2))) /=.
      rewrite [in RHS](eq_bigl (fun i : 'rV_n.+1 => (xpred1 a (i ``_ ord0)) && (xpredT i))); last first.
        move=> i; by rewrite andbT.
      rewrite -(big_rV_cons_behead (fun i => \rsum_(j | j == a1 ``_ ord0) PY (i, j)) (fun i => i == a) xpredT).
      rewrite exchange_big /=.
      apply eq_bigr => v _.
      rewrite big_pred1_eq.
      rewrite big_pred1_eq.
      rewrite /YP.
      rewrite Multivar.from_bivarE Swap.dE /=; congr (PY (_, _)).
        apply/rowP => i.
        rewrite mxE castmxE /=.
        move: (leq0n i); rewrite leq_eqVlt => /orP[/eqP|] i0.
          move=> [:Hi1].
          have @i1 : 'I_(bump 0 0).+1.
            apply: (@Ordinal _ i.+1); abstract: Hi1.
            by rewrite /bump leq0n add1n -i0.
          rewrite (_ : cast_ord _ _ = lshift (n.+2 - bump 0 (bump 0 0)) i1); last exact/val_inj.
          rewrite row_mxEl castmxE /= 2!cast_ord_id.
          rewrite (_ : cast_ord _ _ = rshift 1 (Ordinal (ltn_ord ord0))); last first.
            apply val_inj => /=; by rewrite add1n -i0.
          rewrite row_mxEr mxE.
          set i2 : 'I_1 := Ordinal (ltn_ord ord0).
          rewrite (_ : i = lshift n i2); last exact/val_inj.
          by rewrite (@row_mxEl _ _ 1) mxE.
        move=> [:Hi1].
        have @i1 : 'I_(n.+2 - bump 0 (bump 0 0)).
          apply: (@Ordinal _ i.-1); abstract: Hi1.
          by rewrite /bump !leq0n !add1n subn2 prednK //= -ltnS.
        rewrite (_ : cast_ord _ _ = rshift (bump 0 0).+1 i1); last first.
          by apply/val_inj => /=; rewrite /bump !leq0n !add1n add2n prednK.
        rewrite row_mxEr castmxE /= !cast_ord_id.
        have @i2 : 'I_n by apply: (@Ordinal _ i.-1); rewrite prednK // -ltnS.
        rewrite (_ : i = rshift 1 i2); last first.
          by apply/val_inj => /=; rewrite add1n prednK.
        rewrite (@row_mxEr _ _ 1) //; congr (v _ _); exact/val_inj.
      rewrite castmxE /=.
      rewrite (_ : cast_ord _ _ = lshift (n.+2 - bump 0 (bump 0 0)) (Ordinal (ltn_ord ord0))); last exact/val_inj.
      rewrite row_mxEl castmxE /= 2!cast_ord_id.
      rewrite (_ : cast_ord _ _ = lshift 1 (Ordinal (ltn_ord ord0))); last exact/val_inj.
      rewrite row_mxEl /=; congr (a1 ``_ _); exact/val_inj.
    congr (_ * _).
      rewrite 2!Bivar.sndE; apply eq_bigr => a _; by rewrite H1.
    rewrite /CondEntropy.h1; congr (- _).
    apply eq_bigr => a _; congr (_ * log _).
    + rewrite /cPr /Pr !big_setX /= !big_set1.
      rewrite H1; congr (_ / _).
      rewrite !Bivar.sndE; apply eq_bigr => a0 _.
      by rewrite H1.
    + rewrite /cPr /Pr !big_setX /= !big_set1.
      rewrite H1; congr (_ / _).
      rewrite !Bivar.sndE; apply eq_bigr => a0 _.
      by rewrite H1.
  - rewrite /fA /f.
    rewrite /CondEntropy.h /=.
    have H1 : bump 0 j = j.+1 by rewrite /bump leq0n.
    rewrite (big_cast_rV H1) /=.
    rewrite -(big_rV_cons_behead _ xpredT xpredT) /= exchange_big /= pair_bigA.
    have H2 : forall (v : 'rV_j) (b : B) (a : A) (H1' : (1 + j)%nat = lift ord0 j),
      (Swap.d (Multivar.belast_last (Take.d YP (lift ord0 (lift ord0 j)))))
      (a, (castmx (erefl 1%nat, H1') (row_mx (\row__ b) v))) =
      (TripA.d (TripC12.d (PairTake.d PY j))) (a, (v, b)).
      move=> v b a H1'.
      rewrite /YP /Swap.d /Multivar.belast_last /Take.d /Multivar.from_bivar.
      rewrite /TripA.d /TripC12.d /PairTake.d !DistMap.comp !DistMap.dE /=.
      apply eq_bigl => -[w b0]; rewrite /= /swap /=.
      rewrite (_ : rlast _ = w ``_ j); last first.
        rewrite /rlast !mxE !castmxE /= cast_ord_id.
        rewrite (_ : cast_ord _ _ = rshift 1%nat j); last exact/val_inj.
        by rewrite (@row_mxEr _ 1%nat 1%nat n.+1).
      rewrite !xpair_eqE; congr (_ && _).
      rewrite (_ : rbelast _ =
        row_take (lift ord0 j) (rbelast (row_mx (\row_(k<1) b0) w))); last first.
        apply/rowP => i; rewrite !mxE !castmxE /= esymK !cast_ord_id.
        rewrite /rbelast mxE; congr (row_mx _ _ _ _); exact: val_inj.
      rewrite (_ : rbelast _ = row_mx (\row_(k<1) b0) (rbelast w)); last first.
        apply/rowP => i; rewrite mxE /rbelast.
        case/boolP : (i == O :> nat) => [/eqP | ] i0.
          rewrite (_ : widen_ord _ _ = ord0); last exact: val_inj.
          rewrite (_ : i = ord0); last exact: val_inj.
          by rewrite 2!row_mx_row_ord0.
        have @k : 'I_n.+1.
          apply: (@Ordinal _ i.-1).
          by rewrite prednK // ?lt0n // -ltnS (leq_trans (ltn_ord i)).
        rewrite (_ : widen_ord _ _ = rshift 1%nat k); last first.
          by apply val_inj => /=; rewrite -subn1 subnKC // lt0n.
        rewrite (@row_mxEr _ 1%nat 1%nat n.+1).
        have @k' : 'I_n.
          apply: (@Ordinal _ i.-1).
          by rewrite prednK // ?lt0n // -ltnS (leq_trans (ltn_ord i)).
        rewrite (_ : i = rshift 1%nat k'); last first.
          by apply val_inj => /=; rewrite -subn1 subnKC // lt0n.
        rewrite (@row_mxEr _ 1%nat 1%nat n) mxE; congr (w ord0 _); exact: val_inj.
      apply/idP/idP; last first.
        move/andP => /= [/eqP <- /eqP ->].
        apply/eqP/rowP => k.
        rewrite !mxE !castmxE /= esymK !cast_ord_id.
        case/boolP : (k == O :> nat) => [/eqP | ] k0.
          rewrite (_ : cast_ord _ _ = ord0); last exact: val_inj.
          rewrite (_ : k = ord0); last exact: val_inj.
          by rewrite 2!row_mx_row_ord0.
        have @l : 'I_n.
          apply: (@Ordinal _ k.-1).
          by rewrite prednK // ?lt0n // -ltnS (leq_trans (ltn_ord k)).
        rewrite (_ : cast_ord _ _ = rshift 1%nat l); last first.
          by apply val_inj => /=; rewrite add1n prednK // lt0n.
        rewrite (@row_mxEr _ 1%nat 1%nat n) //.
        have @l0 : 'I_(widen_ord (leqnSn n.+1) j).
          apply: (@Ordinal _ k.-1).
          by rewrite prednK // ?lt0n // -ltnS (leq_trans (ltn_ord k)).
        rewrite (_ : k = rshift 1%nat l0); last first.
          by apply val_inj => /=; rewrite add1n prednK // lt0n.
        rewrite (@row_mxEr _ 1%nat 1%nat) //.
        rewrite !mxE !castmxE /= cast_ord_id; congr (w _ _).
        exact: val_inj.
      move/eqP/rowP => H.
      move: (H ord0).
      rewrite !mxE !castmxE /= 2!cast_ord_id esymK.
      rewrite (_ : cast_ord _ _ = ord0); last exact: val_inj.
      rewrite 2!row_mx_row_ord0 => ->; rewrite eqxx andbT.
      apply/eqP/rowP => k.
      have @k1 : 'I_(bump 0 j).
        apply: (@Ordinal _ k.+1).
        by rewrite /bump leq0n add1n ltnS.
      move: (H k1).
      rewrite !mxE !castmxE /= esymK !cast_ord_id.
      have @k2 : 'I_n.
        apply: (@Ordinal _ k).
        by rewrite (leq_trans (ltn_ord k)) // -ltnS (leq_trans (ltn_ord j)).
      rewrite (_ : cast_ord _ _ = rshift 1%nat k2); last first.
        by apply val_inj => /=; rewrite add1n.
      rewrite (@row_mxEr _ 1%nat 1%nat) mxE.
      rewrite (_ : cast_ord _ _ = widen_ord (leqnSn n) k2); last exact: val_inj.
      move=> ->.
      rewrite (_ : k1 = rshift 1%nat k); last by apply val_inj => /=; rewrite add1n.
      by rewrite row_mxEr.
    apply eq_bigr => -[v b] _ /=.
    rewrite 2!Bivar.sndE; congr (_ * _).
      apply eq_bigr => a _.
      rewrite -H2.
      congr (Swap.d _ (a, castmx (_, _) _)).
      exact: eq_irrelevance.
    rewrite /CondEntropy.h1; congr (- _).
    apply eq_bigr => a _.
    rewrite /cPr /Pr !big_setX /= !big_set1.
    rewrite !H2 //=.
    congr (_ / _ * log (_ / _)).
    + rewrite 2!Bivar.sndE; apply eq_bigr => a' _; by rewrite H2.
    + rewrite 2!Bivar.sndE; apply eq_bigr => a' _; by rewrite H2.
rewrite -addR_opp big_morph_oppR -big_split /=; apply eq_bigr => j _ /=.
case: ifPn => j0.
- rewrite MutualInfo.miE2 addR_opp; congr (`H _ - _).
  rewrite /Multivar.head_of /Bivar.fst.
  rewrite /Multivar.to_bivar.
  by rewrite /PairNth.d !DistMap.comp.
- rewrite /cmi /fA -/P; congr (_ - _).
  + congr CondEntropy.h.
    by rewrite /f23 /f Proj13_TripC23 TripC12.fst belast_last_take.
  + rewrite /f23 /f /TripC23.d TripC12.dI /CondEntropy.h /=.
    rewrite (eq_bigr (fun a => (Bivar.snd (TripA.d (TripC12.d (PairTake.d PY j)))) (a.1, a.2) *
       CondEntropy.h1 (TripA.d (TripC12.d (PairTake.d PY j))) (a.1, a.2))); last by case.
    rewrite -(pair_bigA _ (fun a1 a2 => (Bivar.snd (TripA.d (TripC12.d (PairTake.d PY j)))) (a1, a2) *
       CondEntropy.h1 (TripA.d (TripC12.d (PairTake.d PY j))) (a1, a2))) /=.
    rewrite exchange_big pair_bigA /=; apply eq_bigr => -[b v] _ /=.
    congr (_ * _).
    * rewrite !Bivar.sndE; apply eq_bigr=> a _.
      by rewrite !TripA.dE /= Swap.dE TripC12.dE /= TripA.dE.
    * (* TODO: lemma? *)
      rewrite /CondEntropy.h1; congr (- _); apply eq_bigr => a _.
      by rewrite -!setX1 -cPr_TripA_TripC23 /TripC23.d TripC12.dI.
Qed.

End chain_rule_for_information.

Section conditioning_reduces_entropy.
Section prop.
Variables (A B : finType) (PQ : {dist A * B}).
Let P := Bivar.fst PQ.
Let Q := Bivar.snd PQ.
Let QP := Swap.d PQ.

(* 2.95 *)
Lemma information_cant_hurt : CondEntropy.h PQ <= `H P.
Proof. rewrite -subR_ge0 -MutualInfo.miE2; exact: MutualInfo.mi_ge0. Qed.

Lemma condentropy_indep : PQ = P `x Q -> CondEntropy.h PQ = `H P.
Proof. move/MutualInfo.mi0P; by rewrite MutualInfo.miE2 subR_eq0 => <-. Qed.
End prop.
Section prop2.
Variables (A B C : finType) (PQR : {dist A * B * C}).
Let P : dist A := Bivar.fst (TripA.d PQR).
Let Q : dist B := Bivar.snd (Bivar.fst PQR).
Let R := Bivar.snd PQR.
Lemma mi_bound : Bivar.fst PQR = P `x Q (* P and Q independent *) ->
  MutualInfo.mi (Proj13.d PQR) + MutualInfo.mi (Proj23.d PQR) <= MutualInfo.mi PQR.
Proof.
move=> PQ; rewrite chain_rule_mi leR_add2l /cmi.
rewrite [X in _ <= X - _](_ : _ = `H Q); last first.
  rewrite condentropy_indep; last first.
    rewrite Proj13.fst TripA.fst Swap.fst TripA.fst_snd -/Q.
    rewrite Proj13.snd Swap.snd -/P.
    rewrite -[RHS]Swap.dI Swap.ProdDist -PQ.
    apply/dist_ext => -[b a]. (* TODO: lemma? *)
    rewrite Proj13.dE Swap.dE Bivar.fstE; apply eq_bigr => c _.
    by rewrite Swap.dE TripA.dE.
  by rewrite /Proj13.d TripA.fst_snd TripC12.fst Swap.fst Swap.snd TripA.fst_snd -/Q.
rewrite MutualInfo.miE2.
rewrite Proj23.fst -/Q.
rewrite -oppRB leR_oppl oppRB -!addR_opp leR_add2r.
(* conditioning cannot increase entropy *)
(* Q|R,P <= Q|R, lemma *)
rewrite -subR_ge0.
move: (cmi_ge0 (TripC12.d PQR)); rewrite /cmi.
rewrite /Proj13.d TripC12.dI -/(Proj23.d _).
by rewrite hTripC23 /TripC23.d TripC12.dI.
Qed.
End prop2.
End conditioning_reduces_entropy.

(* TODO: example 2.6.1 *)

Section independence_bound_on_entropy.

Variables (A : finType) (n : nat) (P : {dist 'rV[A]_n.+1}).

(* thm 2.6.6 TODO: with equality in case of independence *)
Lemma independence_bound_on_entropy : `H P <= \rsum_(i < n.+1) `H (Nth.d P i).
Proof.
rewrite chain_rule_rV; apply ler_rsum => /= i _.
case: ifPn => [/eqP|] i0.
  rewrite (_ : i = ord0); last exact/val_inj.
  rewrite head_of_nth0; exact/leRR.
apply: leR_trans; first exact: information_cant_hurt.
rewrite Swap.fst.
apply Req_le; congr (`H _).
by rewrite take_nth.
Qed.

End independence_bound_on_entropy.

Section markov_chain.

Variables (A B C : finType) (PQR : {dist A * B * C}).
Let P := Bivar.fst (Bivar.fst PQR).
Let Q := Bivar.snd (Bivar.fst PQR).
Let PQ := Bivar.fst PQR.
Let QP := Swap.d PQ.
Let RQ := Swap.d (Bivar.snd (TripA.d PQR)).

(* cond. distr. of Z depends only on Y and conditionally independent of X *)
Definition markov_chain := forall (x : A) (y : B) (z : C),
  PQR (x, y, z) = P x * \Pr_QP[ [set y] | [set x]] * \Pr_RQ[ [set z] | [set y]].

Let PRQ := TripC23.d PQR.

(* X and Z are conditionally independent given Y TODO: iff *)
Lemma markov_cmi : markov_chain -> cmi (PRQ : {dist A * C * B}) = 0.
Proof.
rewrite /markov_chain => mc.
rewrite cmiE (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 //= => x _.
case/boolP : (PRQ x == 0) => [/eqP ->|H0]; first by rewrite mul0R.
rewrite (_ : _ / _ = 1); first by rewrite /log Log_1 mulR0.
rewrite eqR_divr_mulr ?mul1R; last first.
  rewrite mulR_neq0'; apply/andP; split.
    (* TODO: lemma? *)
    rewrite /cPr mulR_neq0'; apply/andP; split.
      (* TODO: lemma? *)
      rewrite setX1 Pr_set1.
      case: x => [[x11 x12] x2] in H0 *.
      exact: Proj13.dominN H0.
    rewrite invR_neq0' // Pr_set1 Proj13.snd.
    case: x => [x1 x2] in H0 *.
    exact: Bivar.dom_by_sndN H0.
  (* TODO: lemma? *)
  rewrite /cPr mulR_neq0'; apply/andP; split.
    rewrite setX1 Pr_set1.
    case: x => [[x11 x12] x2] in H0 *.
    exact: Proj23.dominN H0.
  rewrite invR_neq0' // Pr_set1 Proj23.snd.
  case: x => [x1 x2] in H0 *.
  exact: Bivar.dom_by_sndN H0.
(* TODO: lemma? *) (* 2.118 *)
transitivity (Pr PRQ [set x] / Pr Q [set x.2]).
  rewrite /cPr setX1 {2}/PRQ TripC23.snd -/Q; by case: x H0.
transitivity (Pr PQ [set (x.1.1,x.2)] * \Pr_RQ[[set x.1.2]|[set x.2]] / Pr Q [set x.2]).
  congr (_ / _).
  case: x H0 => [[a c] b] H0 /=.
  rewrite /PRQ Pr_set1 TripC23.dE /= mc; congr (_ * _).
  rewrite /cPr {2}/QP Swap.snd -/P Pr_set1 mulRCA mulRV ?mulR1; last first.
    apply Bivar.dom_by_fstN with b.
    apply Bivar.dom_by_fstN with c.
    by rewrite TripC23.dE in H0.
  by rewrite /QP -Swap.Pr setX1.
rewrite {1}/Rdiv -mulRA mulRCA mulRC; congr (_ * _).
  rewrite /cPr Proj13.snd -/Q {2}/PRQ TripC23.snd -/Q -/(Rdiv _ _); congr (_ / _).
  by rewrite /PRQ /PQ setX1 Proj13_TripC23.
rewrite /cPr Proj23.snd; congr (_ / _).
- by rewrite /RQ /PRQ /Proj23.d TripC23.sndA.
- by rewrite /RQ Swap.snd TripA.fst_snd /PRQ TripC23.snd.
Qed.

Let PR := Proj13.d PQR.

(* thm 2.8.1 *)
Lemma data_processing_inequality : markov_chain ->
  MutualInfo.mi PR <= MutualInfo.mi PQ.
Proof.
move=> H.
have H1 : MutualInfo.mi (TripA.d PQR) = MutualInfo.mi PR + cmi PQR.
  rewrite /cmi !MutualInfo.miE2 addRA; congr (_ - _).
  by rewrite -/PR subRK /PR Proj13.fst.
have H2 : MutualInfo.mi (TripA.d PQR) = MutualInfo.mi PQ + cmi PRQ.
  transitivity (MutualInfo.mi (TripA.d PRQ)).
    by rewrite !MutualInfo.miE2 TripC23.fstA hTripC23.
  rewrite /cmi !MutualInfo.miE2 addRA; congr (_ - _).
  by rewrite TripA.fst {1}/PRQ Proj13_TripC23 -/PQ subRK /PQ TripC23.fst_fst.
have H3 : cmi PRQ = 0 by rewrite markov_cmi.
have H4 : 0 <= cmi PQR by exact: cmi_ge0.
move: H2; rewrite {}H3 addR0 => <-.
by rewrite {}H1 addRC -leR_subl_addr subRR.
Qed.

End markov_chain.

Section markov_chain_prop.

Variables (A B C : finType) (PQR : {dist A * B * C}).

Lemma markov_chain_order : markov_chain PQR -> markov_chain (TripC13.d PQR).
Proof.
rewrite /markov_chain => H c b a.
rewrite TripC13.dE /=.
rewrite {}H.
rewrite TripC13.fst_fst.
rewrite (bayes _ [set a] [set b]).
rewrite Swap.dI.
rewrite Swap.fst.
rewrite Swap.snd.
rewrite (mulRC (_ a)) -mulRA.
rewrite [in RHS]mulRCA -[in RHS]mulRA.
congr (_ * _).
  by rewrite TripC13.sndA.
rewrite (bayes _ [set c] [set b]).
rewrite Swap.dI.
rewrite [in LHS]mulRCA -[in LHS]mulRA.
rewrite [in RHS](mulRC (_ c)) -[in RHS](mulRA _ (_ c)).
rewrite [in RHS]mulRCA.
congr (_ * _).
  congr cPr.
  by rewrite TripC13.fst Swap.dI.
rewrite !Pr_set1.
rewrite [in RHS]mulRCA.
congr (_ * _).
  by rewrite Swap.fst TripA.snd_snd.
congr (_ * / _).
  congr (_ a).
  by rewrite TripA.snd_snd TripC13.snd.
by rewrite Swap.snd TripA.fst_snd TripC13.sndA Swap.fst.
Qed.

End markov_chain_prop.

Section Han_inequality.

Local Open Scope ring_scope.

Lemma information_cant_hurt_cond (A : finType) (n' : nat) (n := n'.+1 : nat)
  (P : {dist 'rV[A]_n}) (i : 'I_n) (i0 : i != O :> nat) :
  CondEntropy.h (Multivar.to_bivar P) <=
  CondEntropy.h (Multivar.to_bivar (Take.d P (lift ord0 i))).
Proof.
rewrite -subR_ge0.
set Q : {dist A * 'rV[A]_i * 'rV[A]_(n' - i)} := TakeDrop.d P i.
have H1 : Proj13.d (TripC23.d Q) = Multivar.to_bivar (Take.d P (lift ord0 i)).
  rewrite /Proj13.d /TripC23.d /Multivar.to_bivar /Take.d /Bivar.snd /TripA.d.
  rewrite /TripC12.d /Swap.d /TakeDrop.d !DistMap.comp; congr (DistMap.d _ P).
  apply FunctionalExtensionality.functional_extensionality => /= v.
  congr (_, _).
  - rewrite mxE castmxE /= cast_ord_id; congr (v ord0 _); exact: val_inj.
  - apply/rowP => j.
    rewrite !mxE !castmxE /= !cast_ord_id !esymK mxE; congr (v ord0 _).
    exact: val_inj.
have H2 : CondEntropy.h (TripA.d (TripC23.d Q)) = CondEntropy.h (Multivar.to_bivar P).
  rewrite -hTripC23 /CondEntropy.h /=.
  rewrite (@partition_big _ _ _ _ _ xpredT (@row_take A _ i) xpredT) //=.
  rewrite (eq_bigr (fun a => (Bivar.snd (TripA.d Q)) (a.1, a.2) *
           CondEntropy.h1 (TripA.d Q) (a.1, a.2))%R); last by case.
  rewrite -(pair_bigA _ (fun a1 a2 => (Bivar.snd (TripA.d Q)) (a1, a2) *
           CondEntropy.h1 (TripA.d Q) (a1, a2))%R) /=.
  apply eq_bigr => v _.
(* TODO: lemma yyy *)
  rewrite (@reindex_onto _ _ _ [finType of 'rV[A]_n'] [finType of 'rV[A]_(n' - i)]
    (fun w => (castmx (erefl 1%nat, subnKC (ltnS' (ltn_ord i))) (row_mx v w)))
    (@row_drop A _ i)) /=; last first.
    move=> w wv; apply/rowP => j.
    rewrite castmxE /= cast_ord_id /row_drop mxE; case: splitP => [j0 /= jj0|k /= jik].
    - rewrite -(eqP wv) mxE castmxE /= cast_ord_id; congr (w _ _); exact: val_inj.
    - rewrite mxE /= castmxE /= cast_ord_id; congr (w _ _); exact: val_inj.
  apply eq_big => /= w.
    apply/esym/andP; split; apply/eqP/rowP => j.
    by rewrite !mxE !castmxE /= !cast_ord_id esymK cast_ordK row_mxEl.
    by rewrite !mxE !castmxE /= cast_ord_id esymK cast_ordK cast_ord_id row_mxEr.
  move=> _; congr (_ * _)%R.
  - rewrite !Bivar.sndE; apply eq_bigr => a _.
    by rewrite TripA.dE /= Multivar.to_bivarE /= /Q TakeDrop.dE.
  - rewrite /CondEntropy.h1; congr (- _)%R; apply eq_bigr => a _.
    congr (_ * log _)%R.
    + rewrite /cPr !(Pr_set1,setX1) TripA.dE /= /Q TakeDrop.dE /= Multivar.to_bivarE /=.
      congr (_ / _)%R.
      rewrite !Bivar.sndE; apply eq_bigr => a0 _.
      by rewrite TripA.dE TakeDrop.dE Multivar.to_bivarE.
    + rewrite /cPr !(Pr_set1,setX1) TripA.dE /= /Q TakeDrop.dE /= Multivar.to_bivarE /=.
      congr (_ / _)%R.
      rewrite !Bivar.sndE; apply eq_bigr => a0 _.
      by rewrite TripA.dE TakeDrop.dE Multivar.to_bivarE.
rewrite (_ : _ - _ = cmi (TripC23.d Q))%R; last by rewrite /cmi H1 H2.
exact/cmi_ge0.
Qed.

Lemma han_helper (A : finType) (n' : nat) (n := n'.+1 : nat)
  (P : {dist 'rV[A]_n}) (i : 'I_n) (i0 : i != O :> nat) :
  CondEntropy.h (Multivar.to_bivar (MultivarPerm.d P (put_front_perm i))) <=
  CondEntropy.h (Swap.d (Multivar.belast_last (Take.d P (lift ord0 i)))).
Proof.
rewrite (_ : Swap.d _ = Multivar.to_bivar (MultivarPerm.d
    (Take.d P (lift ord0 i)) (put_front_perm (inord i)))); last first.
  apply/dist_ext => /= -[a v].
  rewrite Swap.dE Multivar.belast_lastE Multivar.to_bivarE /= MultivarPerm.dE.
  rewrite !(Take.dE _ (lift ord0 i)); apply eq_bigr => /= w _; congr (P _); apply/rowP => k.
  rewrite !castmxE /= cast_ord_id.
  case/boolP : (k < i.+1)%nat => ki.
    have @k1 : 'I_i.+1 := Ordinal ki.
    rewrite (_ : cast_ord _ k = lshift (n - bump 0 i) k1); last exact/val_inj.
    rewrite 2!row_mxEl castmxE /= cast_ord_id [in RHS]mxE.
    case/boolP : (k < i)%nat => [ki'|].
      rewrite (_ : cast_ord _ _ = lshift 1%nat (Ordinal ki')) /=; last exact/val_inj.
      rewrite row_mxEl /put_front_perm permE /put_front ifF; last first.
        apply/negbTE/eqP => /(congr1 val) /=.
        by rewrite inordK // => /eqP; rewrite ltn_eqF.
      rewrite inordK //= ki' (_ : inord k.+1 = rshift 1%nat (Ordinal ki')); last first.
        by apply/val_inj => /=; rewrite inordK.
      by rewrite (@row_mxEr _ 1%nat 1%nat).
    rewrite permE /put_front.
    rewrite -leqNgt leq_eqVlt => /orP[|] ik.
      rewrite ifT; last first.
        apply/eqP/val_inj => /=; rewrite inordK //; exact/esym/eqP.
      rewrite row_mx_row_ord0 (_ : cast_ord _ _ = rshift i ord0); last first.
        by apply val_inj => /=; rewrite addn0; apply/esym/eqP.
      by rewrite row_mxEr mxE.
    move: (leq_ltn_trans ik ki); by rewrite ltnn.
  rewrite -ltnNge ltnS in ki.
  move=> [:Hk1].
  have @k1 : 'I_(n - bump 0 i).
    apply: (@Ordinal _ (k - i.+1)).
    abstract: Hk1.
    by rewrite /bump leq0n add1n ltn_sub2r // (leq_ltn_trans _ (ltn_ord k)).
  rewrite (_ : cast_ord _ _ = rshift i.+1 k1); last by apply val_inj => /=; rewrite subnKC.
  by rewrite 2!row_mxEr.
rewrite (_ : MultivarPerm.d (Take.d _ _) _ =
  Take.d (MultivarPerm.d P (put_front_perm i)) (lift ord0 i)); last first.
  apply/dist_ext => /= w.
  rewrite MultivarPerm.dE 2!(Take.dE _ (lift ord0 i)); apply eq_bigr => /= v _.
  rewrite MultivarPerm.dE; congr (P _); apply/rowP => /= k.
  rewrite /col_perm mxE !castmxE /= !cast_ord_id /=.
  case/boolP : (k < bump 0 i)%nat => ki.
    rewrite (_ : cast_ord _ _ = lshift (n - bump 0 i) (Ordinal ki)); last exact/val_inj.
    rewrite row_mxEl mxE /put_front_perm !permE /= /put_front /=.
    case/boolP : (k == i) => ik.
      rewrite ifT; last first.
        apply/eqP/val_inj => /=; rewrite inordK //; exact/eqP.
      rewrite (_ : cast_ord _ _ = lshift (n - bump 0 i) ord0); last exact/val_inj.
      by rewrite row_mxEl.
    rewrite ifF; last first.
      apply/negbTE/eqP => /(congr1 val) /=.
      apply/eqP; by rewrite inordK.
    case/boolP : (k < i)%nat => {ik}ik.
      rewrite inordK // ik.
      move=> [:Hk1].
      have @k1 : 'I_(bump 0 i).
        apply: (@Ordinal _ k.+1).
        abstract: Hk1.
        by rewrite /bump leq0n add1n.
      rewrite (_ : cast_ord _ _ = lshift (n - bump 0 i) k1); last first.
        apply/val_inj => /=; rewrite inordK // ltnS.
        by rewrite (leq_trans ik) // -ltnS.
      rewrite row_mxEl; congr (w _ _).
      by apply val_inj => /=; rewrite inordK.
    rewrite -ltnNge in ik.
    rewrite ifF; last first.
      apply/negbTE.
      by rewrite -leqNgt -ltnS inordK.
    rewrite (_ : cast_ord _ _ = lshift (n - bump 0 i) (Ordinal ki)); last exact/val_inj.
    by rewrite row_mxEl.
  rewrite -ltnNge /bump leq0n add1n ltnS in ki.
  move=> [:Hk1].
  have @k1 : 'I_(n - bump 0 i).
    apply: (@Ordinal _ (k - i.+1)).
    abstract: Hk1.
    by rewrite /bump leq0n add1n ltn_sub2r // (leq_trans _ (ltn_ord k)).
  rewrite (_ : cast_ord _ _ = rshift i.+1 k1); last by apply/val_inj => /=; rewrite subnKC.
  rewrite row_mxEr permE /put_front /= ifF; last first.
     by move: ki; rewrite ltnNge; apply: contraNF => /eqP ->.
  rewrite ltnNge (ltnW ki) /=.
  move=> [:Hk2].
  have @k2 : 'I_(n - bump 0 i).
    apply: (@Ordinal _ (k - i.+1)).
    abstract: Hk2.
    by rewrite /bump leq0n add1n ltn_sub2r // (leq_trans _ (ltn_ord k)).
  rewrite (_ : cast_ord _ _ = rshift (bump 0 i) k2); last first.
    by apply/val_inj => /=; rewrite /bump leq0n add1n subnKC.
  rewrite row_mxEr; congr (v _ _); exact/val_inj.
exact/information_cant_hurt_cond.
Qed.

Variables (A : finType) (n' : nat).
Let n := n'.+1.
Variable (P : {dist 'rV[A]_n}).

Lemma han : n.-1%:R * `H P <= \rsum_(i < n) `H (MargDist.d P i).
Proof.
rewrite -subn1 natRB // mulRBl mul1R leR_subl_addr {2}(chain_rule_rV P).
rewrite -big_split /= -{1}(card_ord n) -sum1_card big_morph_natRD big_distrl /=.
apply ler_rsum => i _; rewrite mul1R.
case: ifPn => [/eqP|] i0.
  rewrite (_ : i = ord0); last exact/val_inj.
  rewrite MargDist.zero /Multivar.tail_of /Multivar.head_of.
  rewrite -{1}(Multivar.to_bivarK P) entropy_from_bivar.
  move: (chain_rule (Multivar.to_bivar P)); rewrite /JointEntropy.h => ->.
  rewrite [in X in _ <= X]addRC leR_add2l -Swap.fst; exact: information_cant_hurt.
rewrite (chain_rule_multivar _ i0) leR_add2l; exact/han_helper.
Qed.

End Han_inequality.
