From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import Reals Lra.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.
Require Import cproba divergence entropy.

(* tentative formalization Cover and Thomas, Chapter 2 *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

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
  rewrite (_ : j0 = rshift i ord0); last by apply/val_inj => /=; rewrite ij.
  rewrite row_mxEr mxE.
  move=> [:Hj1].
  have @j1 : 'I_(n.+1 - i) by apply: (@Ordinal _ 0); abstract: Hj1; by rewrite subn_gt0.
  rewrite (_ : cast_ord _ _ = rshift i j1); last by apply/val_inj => /=; rewrite ij.
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

Local Open Scope R_scope.
Local Open Scope proba_scope.

Module CondDist.
Section def.
Variables (A B : finType) (PQ : {dist A * B}) (b : B).
Hypothesis Hb : Bivar.snd PQ b != 0.
Let helper (F : {set B}) :
  \rsum_(a in A) Pr PQ (setX [set a] F) = Pr (Bivar.snd PQ) F.
Proof.
rewrite /Pr (eq_bigr (fun i =>
    \rsum_(a in [set i]) \rsum_(j in F) PQ (a, j))); last first.
  by move=> a _; rewrite big_setX.
rewrite pair_big_dep /= exchange_big /=; apply eq_bigr => b0 _.
rewrite Bivar.sndE (reindex_onto (fun x => (x, x)) fst); last first.
  by case => /= a b1; rewrite in_set1 => /eqP ->.
by rewrite /= (eq_bigl predT) // => a; rewrite !inE !eqxx.
Qed.
Definition f a := \Pr_PQ [[set a] | [set b]].
Lemma f0 a : 0 <= f a. Proof. exact: cPr_ge0. Qed.
Lemma f1 : \rsum_(a in A) f a = 1.
Proof. by rewrite /f /cPr -big_distrl /= helper mulRV // Pr_set1. Qed.
Definition d : {dist A} := locked (makeDist f0 f1).
Lemma dE a : d a = \Pr_PQ [[set a] | [set b]].
Proof. by rewrite /d; unlock. Qed.
End def.
End CondDist.

Arguments CondDist.d {A} {B} _ _ _.

(* TODO: move? *)
Lemma head_of_fst_belast_last (A : finType) (n : nat) (P : {dist 'rV[A]_n.+2}) :
  Multivar.head_of (Bivar.fst (Multivar.belast_last P)) = Multivar.head_of P.
Proof.
apply/dist_ext => a.
rewrite /Multivar.head_of 2!Bivar.fstE /= -(big_rV_belast_last _ xpredT xpredT) /=.
apply eq_bigr => v _.
rewrite Multivar.to_bivarE /= Bivar.fstE; apply eq_bigr => a0 _.
rewrite Multivar.to_bivarE Multivar.belast_lastE /=.
congr (P _).
apply/rowP => i.
rewrite castmxE /= cast_ord_id /=.
case: (ltnP i 1) => [i1|Oi].
  set i0 : 'I_(1 + n) := Ordinal (leq_trans i1 (ltn0Sn n)).
  rewrite (_ : cast_ord _ _ = lshift 1 i0) ?row_mxEl; last exact/val_inj.
  set i2 : 'I_1 := Ordinal i1.
  rewrite (_ : i0 = lshift n i2); last exact/val_inj.
  rewrite (@row_mxEl _ _ 1%nat) mxE.
  rewrite (_ : i = lshift n.+1 i2); last exact/val_inj.
  by rewrite (@row_mxEl _ _ 1%nat) mxE.
move=> [:Hi2].
have @i2 : 'I_(1%nat + n) by apply: (@Ordinal _ i.-1); abstract: Hi2; rewrite prednK // add1n -ltnS.
rewrite [in RHS](_ : i = rshift 1%nat i2); last first.
  by apply/val_inj => /=; rewrite add1n prednK.
rewrite (@row_mxEr _ _ 1%nat) castmxE /= cast_ord_id.
case: (ltnP i n.+1) => [ni|jn].
  move=> [:Hi3].
  have @i3 : 'I_(1 + n) by apply: (@Ordinal _ i); abstract: Hi3; by rewrite add1n.
  rewrite (_ : cast_ord _ _ = lshift 1%nat i3); last exact/val_inj.
  rewrite row_mxEl.
  move=> [:Hj4].
  have @i4 : 'I_n by apply: (@Ordinal _ i.-1); abstract: Hj4; rewrite prednK.
  rewrite (_ : i3 = rshift 1%nat i4); last first.
    apply/val_inj => /=; by rewrite add1n prednK.
  rewrite (@row_mxEr _ _ 1%nat).
  have @i5 : 'I_n by apply: (@Ordinal _ i2).
  rewrite (_ : cast_ord _ _ = lshift 1%nat i5); last exact/val_inj.
  by rewrite row_mxEl.
have {jn}jn : i = ord_max.
  by apply/val_inj => /=; apply/eqP; rewrite eqn_leq jn andbT -ltnS.
have @i3 : 'I_1 by apply: (@Ordinal _ ord0).
rewrite (_ : cast_ord _ _ = rshift (1 + n) i3); last first.
  by apply val_inj => /=; rewrite jn /= add1n.
rewrite row_mxEr mxE.
rewrite (_ : cast_ord _ _ = rshift n i3); last first.
  apply val_inj => /=; by rewrite jn.
by rewrite row_mxEr mxE.
Qed.

Module Take.
Section def.
Variable (A : finType) (n : nat) (P : {dist 'rV[A]_n}).
Definition f (i : 'I_n.+1) (v : 'rV[A]_i) : R :=
  \rsum_(w in 'rV[A]_(n - i)) P (castmx (erefl, subnKC (ltnS' (ltn_ord i))) (row_mx v w)).
Lemma f0 i x : 0 <= @f i x.
Proof. apply rsumr_ge0 => /= v _; exact: dist_ge0. Qed.
Lemma f1 (i : 'I_n.+1) : \rsum_(x in 'rV[A]_i) @f i x = 1%R.
Proof.
rewrite -(pmf1 P) /= /f; apply/esym.
rewrite (@partition_big _ _ _ _ [finType of 'rV[A]_i] xpredT (@row_take A n i) xpredT) //=.
apply eq_bigr => v _.
rewrite (@reindex_onto _ _ _ [finType of 'rV[A]_n] [finType of 'rV[A]_(n - i)]
  (fun w => (castmx (erefl 1%nat, subnKC (ltnS' (ltn_ord i))) (row_mx v w)))
  (@row_drop A n i)) /=; last first.
  move=> w wv; apply/rowP => j.
  rewrite castmxE /= cast_ord_id /row_drop mxE; case: splitP => [j0 /= jj0|k /= jik].
  - rewrite -(eqP wv) mxE castmxE /= cast_ord_id; congr (w _ _); exact: val_inj.
  - rewrite mxE /= castmxE /= cast_ord_id; congr (w _ _); exact: val_inj.
apply eq_bigl => w; rewrite inE; apply/andP; split; apply/eqP/rowP => j.
- by rewrite !mxE !castmxE /= !cast_ord_id esymK cast_ordK row_mxEl.
- by rewrite !mxE !castmxE /= cast_ord_id esymK cast_ordK cast_ord_id row_mxEr.
Qed.
Definition d (i : 'I_n.+1) : {dist 'rV[A]_i} := locked (makeDist (@f0 i) (@f1 i)).
Lemma dE i v : d i v = \rsum_(w in 'rV[A]_(n - i))
  P (castmx (erefl, subnKC (ltnS' (ltn_ord i))) (row_mx v w)).
Proof. by rewrite /d; unlock. Qed.
End def.
Section prop.
Local Open Scope vec_ext_scope.
Lemma all (A : finType) (n : nat) (P : {dist 'rV[A]_n.+2}) :
  d P (lift ord0 ord_max) = P.
Proof.
apply/dist_ext => /= v.
rewrite dE /=.
have H1 : (n.+2 - bump 0 n.+1)%nat = O by rewrite /bump /= add1n subnn.
rewrite (big_cast_rV H1) //= (big_rV_0 _ _ (v ``_ ord0)); congr (P _).
apply/rowP => i.
rewrite castmxE /= cast_ord_id /=.
rewrite (_ : cast_ord _  _ = lshift (n.+2 - bump 0 n.+1) i); last exact/val_inj.
by rewrite row_mxEl.
Qed.
End prop.
End Take.

Module PairNth.
Section def.
Local Open Scope vec_ext_scope.
Variables (A B : finType) (n : nat) (P : {dist 'rV[A]_n * B}) (i : 'I_n).
Definition f (ab : A * B) :=
  \rsum_(x : 'rV[A]_n * B | (x.1 ``_ i == ab.1) && (x.2 == ab.2)) P x.
Lemma f0 ab : 0 <= f ab.
Proof. rewrite /f; apply: rsumr_ge0 => /= -[a b] /= _; exact: dist_ge0. Qed.
Lemma f1 : \rsum_(ab : A * B) f ab = 1.
Proof.
rewrite -(pmf1 P) /= (eq_bigr (fun x => f (x.1, x.2))); last by case.
rewrite -(pair_bigA _ (fun a b => f (a, b))) /=.
rewrite (eq_bigr (fun x => P (x.1, x.2))); last by case.
rewrite -(pair_bigA _ (fun a b => P (a, b))) /=.
rewrite [in LHS]exchange_big [in RHS]exchange_big /=; apply eq_bigr => b _.
rewrite /f /= (partition_big (fun x : 'rV[A]_n => x ``_ i) xpredT) //=.
apply eq_bigr => a _.
rewrite (eq_bigr (fun x => P (x.1, x.2))); last by case.
rewrite -(pair_big (fun x : 'rV[A]_n => x ord0 i == a) (fun x => x == b) (fun a b => P (a, b))) /=.
apply eq_bigr => t /eqP tja; by rewrite big_pred1_eq.
Qed.
Definition d : {dist A * B} := locked (makeDist f0 f1).
Lemma dE ab : d ab = \rsum_(x : 'rV[A]_n * B | (x.1 ``_ i == ab.1) && (x.2 == ab.2)) P x.
Proof. by rewrite /d; unlock. Qed.
End def.
End PairNth.

Module PairTake.
Section def.
Variables (A B : finType) (n : nat) (P : {dist 'rV[A]_n.+1 * B}) (i : 'I_n.+1).
Lemma cast : (i + 1%nat + (n - i))%nat = n.+1.
by rewrite addn1 addSn subnKC // -ltnS.
Qed.
Definition f (ab : 'rV[A]_i * A * B) := \rsum_(w : 'rV[A]_(n - i)) P
    (castmx (erefl, cast) (row_mx (row_mx ab.1.1 (\row__ ab.1.2)) w), ab.2).
Lemma f0 ab : 0 <= f ab.
Proof. rewrite /f; apply: rsumr_ge0 => w _; exact: dist_ge0. Qed.
Lemma f1 : \rsum_(ab : 'rV[A]_i * A * B) f ab = 1.
Proof.
rewrite -(pmf1 P) /=.
rewrite [in RHS](eq_bigr (fun x => P (x.1, x.2))); last by case.
rewrite -[in RHS](pair_bigA _ (fun a b => P (a, b))) /=.
rewrite (eq_bigr (fun x => f (x.1, x.2))); last by case.
rewrite -(pair_bigA _ (fun a b => f (a, b))) /=.
rewrite (@partition_big _ _ _ _ [finType of 'rV[A]_i] xpredT (@row_take A n.+1 (widen_ord (leqnSn _) i)) xpredT) //=.
rewrite (eq_bigr (fun i0 => \rsum_(j | true) f (i0.1, i0.2, j))); last by case.
rewrite -(pair_bigA _ (fun a b => \rsum_(j | true) f (a, b, j))) /=.
apply eq_bigr => w _.
have H1 : (i + (n.+1 - i))%nat = n.+1 by rewrite subnKC // ltnW.
rewrite (@reindex_onto _ _ _ [finType of 'rV[A]_n.+1] [finType of 'rV[A]_(n.+1 - i)]
  (fun w0 => (castmx (erefl 1%nat, H1) (row_mx w w0)))
  (@row_drop A n.+1 (widen_ord (leqnSn _) i))) /=; last first.
  move=> w0 w0w; apply/rowP => j.
  rewrite castmxE /= cast_ord_id /= !mxE.
  case: splitP => [j0 /= ?|k /= jik].
  - rewrite -(eqP w0w) mxE castmxE /= cast_ord_id; congr (w0 _ _); exact/val_inj.
  - rewrite mxE castmxE /= cast_ord_id; congr (w0 _ _); exact/val_inj.
rewrite exchange_big /= [in RHS]exchange_big /=; apply eq_bigr => b _.
transitivity (\rsum_(i0 : 'rV__) P (castmx (erefl 1%nat, H1) (row_mx w i0), b)); last first.
  apply eq_bigl => v; apply/esym.
  apply/andP; split.
    apply/eqP/rowP => j.
    rewrite mxE 2!castmxE /= !cast_ord_id /=.
    rewrite (_ : cast_ord _ _ = lshift (n.+1 - i) j); last exact/val_inj.
    by rewrite row_mxEl.
  apply/eqP/rowP => j.
  rewrite mxE 2!castmxE /= !cast_ord_id /=.
  rewrite (_ : cast_ord _ _ = rshift i j); last exact/val_inj.
  by rewrite row_mxEr.
rewrite /f /=.
rewrite exchange_big /=.
have H2 : (n.+1 - i = (n - i).+1)%nat by rewrite subSn // -ltnS.
rewrite (big_cast_rV H2) /=.
rewrite -(big_rV_cons_behead _ xpredT xpredT) /=.
rewrite exchange_big /=.
apply eq_bigr => a _.
apply eq_bigr => w1 _.
by rewrite row_mxA'.
Qed.
Definition d : {dist 'rV_i * A * B} := locked (makeDist f0 f1).
Lemma dE ab : d ab = f ab. Proof. by rewrite /d; unlock. Qed.
End def.
End PairTake.

Section to_bivar_last_take.

Variables (A B : finType).
Variables (n : nat) (PY : {dist 'rV[A]_n.+1 * B}).
Let P : {dist 'rV[A]_n.+1} := Bivar.fst PY.

Lemma belast_last_take (j : 'I_n.+1) :
  Multivar.belast_last (Take.d P (lift ord0 j)) = Bivar.fst (PairTake.d PY j).
Proof.
apply/dist_ext => /= -[v a].
rewrite Multivar.belast_lastE.
rewrite Take.dE /=.
rewrite Bivar.fstE.
rewrite /PairTake.d; unlock => /=; rewrite /PairTake.f /=.
rewrite exchange_big => /=.
apply eq_bigr => w _.
rewrite /P Bivar.fstE; apply eq_bigr => b _ /=.
congr (PY (_, b)).
apply/rowP => i.
rewrite !castmxE /= !cast_ord_id /=.
case: (ltnP i j) => [ij|].
  move=> [:Hi0].
  have @i0 : 'I_j.+1 by apply: (@Ordinal _ i) => /=; abstract: Hi0; exact/ltnW.
  rewrite (_ : cast_ord _ _ = lshift (n - j)%nat i0); last exact/val_inj.
  rewrite row_mxEl castmxE /= cast_ord_id.
  rewrite (_ : cast_ord _ _ = lshift 1%nat (Ordinal ij)); last exact/val_inj.
  rewrite row_mxEl.
  move=> [:Hi1].
  have @i1 : 'I_(j + 1) by apply: (@Ordinal _ i); abstract: Hi1; rewrite addn1.
  rewrite (_ : cast_ord _ _ = lshift (n - j) i1); last exact/val_inj.
  rewrite row_mxEl (_ : i1 = lshift 1%nat (Ordinal ij)); last exact/val_inj.
  by rewrite row_mxEl.
rewrite leq_eqVlt => /orP[/eqP ji|ji].
- rewrite (_ : cast_ord _ _ = lshift (n - j) ord_max); last exact/val_inj.
  rewrite row_mxEl castmxE /= cast_ord_id.
  rewrite (_ : cast_ord _ _ = rshift j ord0); last first.
    apply/val_inj => /=; by rewrite addn0.
  rewrite row_mxEr mxE.
  move=> [:Hi0].
  have @i0 : 'I_(j + 1) by apply: (@Ordinal _ i); abstract: Hi0; rewrite addn1 ji.
  rewrite (_ : cast_ord _ _ = lshift (n - j) i0); last exact/val_inj.
  rewrite row_mxEl (_ : i0 = rshift j ord0); last first.
    apply/val_inj => /=; by rewrite addn0.
  by rewrite row_mxEr mxE.
- move=> [:Hi1].
  have @i1 : 'I_(n - j).
    apply: (@Ordinal _ (i - j.+1)); abstract: Hi1.
    by rewrite subnS prednK // ?subn_gt0 // leq_sub2r // -ltnS.
  rewrite (_ : cast_ord _ _ = rshift j.+1 i1); last first.
    by apply val_inj => /=; rewrite subnKC.
  rewrite row_mxEr (_ : cast_ord _ _ = rshift (j + 1) i1); last first.
    by apply val_inj => /=; rewrite addn1 subnKC.
  by rewrite row_mxEr.
Qed.

End to_bivar_last_take.

Module Nth.
Section def.
Local Open Scope vec_ext_scope.
Variables (A : finType) (n : nat) (P : {dist 'rV[A]_n}) (i : 'I_n).
Definition f (a : A) := \rsum_(x : 'rV[A]_n | x ``_ i == a) P x.
Lemma f0 a : 0 <= f a.
Proof. apply: (@rsumr_ge0 _ _ (fun x : 'rV_n => x ``_ i == a)) => /= x _; exact/dist_ge0. Qed.
Lemma f1 : \rsum_(a : A) f a = 1.
Proof. by rewrite -(pmf1 P) /= (partition_big (fun x : 'rV[A]_n => x ``_ i) xpredT). Qed.
Definition d : {dist A} := locked (makeDist f0 f1).
Lemma dE a : d a = \rsum_(x : 'rV[A]_n | x ``_ i == a) P x.
Proof. by rewrite /d; unlock => /=. Qed.
End def.
End Nth.

Local Open Scope entropy_scope.

Module JointEntropy.
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
rewrite /h (big_morph _ morph_Ropp oppR0) /=; apply eq_bigr => a _.
rewrite /h1 mulRN big_distrr /=; congr (- _); apply eq_bigr => b _.
rewrite mulRA; congr (_ * _).
by rewrite mulRC -(Pr_set1 P a) -Pr_cPr Pr_setX1 Pr_set1 Swap.dE.
Qed.

Lemma h1_ge0 a : 0 <= h1 a.
Proof.
rewrite /h1 (big_morph _ morph_Ropp oppR0); apply rsumr_ge0 => b _.
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

Definition f : 'I_4 * 'I_4 -> R := [eta (fun=>0) with
(zero, zero) |-> (1/8), (zero, one) |-> (1/16), (zero, two) |-> (1/16), (zero, three) |-> (1/4),
(one, zero) |-> (1/16), (one, one) |-> (1/8), (one, two) |-> (1/16), (one, three) |-> 0,
(two, zero) |-> (1/32), (two, one) |-> (1/32), (two, two) |-> (1/16), (zero, three) |-> 0,
(three, zero) |-> (1/32), (three, one) |-> (1/32), (three, two) |-> (1/16), (two, three) |-> 0].

Lemma f0 : forall x, 0 <= f x.
Proof.
case => -[ [? [[|[|[|[|[]//]]]]]
  | [? [[|[|[|[|[]//]]]]]
  | [? [[|[|[|[|[]//]]]]]
  | [? [[|[|[|[|[]//]]]]] | []//]]]]]; rewrite /f /=; try lra.
Qed.

Lemma f1 : \rsum_(x in {: 'I_4 * 'I_4}) f x = 1.
Proof.
rewrite (eq_bigr (fun x => f (x.1, x.2))); last by case.
rewrite -(pair_bigA _ (fun x1 x2 => f (x1, x2))) /=.
rewrite !big_ord_recl !big_ord0 /f /=; field.
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
rewrite !big_ord_recl !big_ord0 !dE /f /=.
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
  - by rewrite -(Pr_set1 P a) /P -(Swap.snd PQ) mulRC -Pr_cPr Pr_setX1 Pr_set1 Swap.dE.
transitivity (
  - (\rsum_(a in A) \rsum_(b in B) PQ (a, b) * log (P a))
  - (\rsum_(a in A) \rsum_(b in B) PQ (a, b) * log (\Pr_QP [ [set b] | [set a] ]))). (* 2.17 *)
  rewrite -oppRB; congr (- _); rewrite -addR_opp oppRK -big_split /=.
  apply eq_bigr => a _; rewrite -big_split /=; apply eq_bigr => b _.
  case/boolP : (PQ (a, b) == 0) => [/eqP H0|H0].
  - by rewrite H0 !mul0R addR0.
  - rewrite -mulRDr; congr (_ * _); rewrite mulRC logM //.
    by rewrite -cPr_Pr_setX_gt0 Pr_setX1 Pr_set1 Swap.dE -dist_neq0.
    rewrite -dist_neq0; exact: Bivar.dom_by_fstN H0.
rewrite /CondEntropy.h [in X in _ + X = _](big_morph _ morph_Ropp oppR0); congr (_ + _).
- (* TODO: lemma? *)
  congr (- _); apply eq_bigr => a _.
  by rewrite -big_distrl /= -Bivar.fstE.
- apply eq_bigr => a _.
  rewrite /CondEntropy.h1 /= mulRN; congr (- _).
  rewrite big_distrr /=; apply eq_bigr => b _.
  rewrite mulRA; congr (_ * _).
  by rewrite -(Pr_set1 (Bivar.snd _) a) mulRC -Pr_cPr Pr_setX1 Pr_set1 Swap.dE.
Qed.

End chain_rule.

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
  rewrite -cPr_Pr_setX_gt0 Pr_gt0 Pr_setX1 Pr_set1; exact: Proj13.dominN H0.
  by rewrite -cPr_Pr_setX_gt0 Pr_gt0 Pr_setX1 Pr_set1 TripA.dE /= TripC12.dE.
congr (_ * log _).
(* TODO: lemma? *)
rewrite /cPr !Pr_setX1 !Pr_set1.
rewrite mulRCA -mulRA TripA.dE TripC12.dE /=; congr (_ * _).
rewrite -invRM; last 2 first.
  apply/eqP; rewrite (@Bivar.dom_by_sndN _ _ _ a) //; exact: Proj13.dominN H0.
  apply/eqP; by rewrite (@Bivar.dom_by_sndN _ _ _ b) // TripA.dE /= TripC12.dE.
suff -> : (Bivar.snd PR) c * (Bivar.snd QPR) (a, c) =
  PR (a, c) * (Bivar.snd PQR) c.
  rewrite invRM; last 2 first.
    apply/eqP; exact: Proj13.dominN H0.
    by apply/eqP; rewrite (@Bivar.dom_by_sndN _ _ _ (a, b)).
  rewrite mulRA mulRV ?mul1R //; exact: Proj13.dominN H0.
rewrite mulRC.
congr (_ * _).
by rewrite /PR Proj13.def.
by rewrite /PR Proj13.snd.
Qed.

End entropy_chain_rule_corollary.

Section conditional_entropy_prop. (* NB: here because use chain rule *)

Variables (A B : finType) (PQ : {dist A * B}).
Let P := Bivar.fst PQ.
Let Q := Bivar.snd PQ.
Let QP := Swap.d PQ.

Lemma entropyB : `H P - CondEntropy.h PQ = `H Q - CondEntropy.h QP.
Proof.
apply/eqP; rewrite subR_eq addRAC -subR_eq subR_opp; apply/eqP.
rewrite -chain_rule JointEntropy.hC.
rewrite -/(JointEntropy.h (Swap.d PQ)) chain_rule.
by rewrite Swap.fst -/Q Swap.dI.
Qed.

End conditional_entropy_prop.

Section conditional_entropy_prop2. (* NB: here because use chain rule *)

Variables (A : finType) (P : {dist A}).

Lemma CondEntrop_self : CondEntropy.h (Self.d P) = 0.
Proof.
move: (@chain_rule _ _ (Self.d P)) => /eqP.
rewrite !Self.fst Self.swap addRC -subR_eq => /eqP <-.
by rewrite /JointEntropy.h joint_entropy_self subRR.
Qed.

End conditional_entropy_prop2.

Module MutualInfo.
Section mutualinfo.

Variables (A B : finType) (PQ : {dist A * B}).
Let P := Bivar.fst PQ.
Let Q := Bivar.snd PQ.
Let QP := Swap.d PQ.

Local Open Scope divergence_scope.

(* I(X;Y) *)
Definition mi := D( PQ || P `x Q).

(* 2.28 *)
Lemma miE : mi = \rsum_(a in A) \rsum_(b in B) PQ (a, b) * log (PQ (a, b) / (P a * Q b)).
Proof.
rewrite /mi /div pair_big /=; apply eq_bigr; case => a b _ /=.
case/boolP : (PQ (a, b) == 0) => [/eqP H0|H0].
- by rewrite H0 !mul0R.
- rewrite -[in X in _ = _ * (log (_ / X))]/((a, b).1).
  rewrite -[in X in _ = _ * (log (_ / X))]/((a, b).2).
  by rewrite -(ProdDist.dE P Q).
Qed.

(* 2.39 *)
Lemma miE2 : mi = `H P - CondEntropy.h PQ.
Proof.
rewrite miE.
transitivity (\rsum_(a in A) \rsum_(b in B)
    PQ (a, b) * log (\Pr_PQ [ [set a] | [set b] ] / P a)).
  apply eq_bigr => a _; apply eq_bigr => b _.
  rewrite /cPr Pr_setX1 2!Pr_set1 /= -/Q.
  case/boolP : (PQ (a, b) == 0) => [/eqP H0 | H0].
  - by rewrite H0 !mul0R.
  - congr (_ * log _).
    rewrite divRM; last 2 first.
      apply/eqP; exact: Bivar.dom_by_fstN H0.
      apply/eqP; exact: Bivar.dom_by_sndN H0.
    by rewrite mulRAC.
transitivity (- (\rsum_(a in A) \rsum_(b in B) PQ (a, b) * log (P a)) +
  \rsum_(a in A) \rsum_(b in B) PQ (a, b) * log (\Pr_PQ [ [set a] | [set b] ])). (* 2.37 *)
  rewrite (big_morph _ morph_Ropp oppR0) -big_split; apply/eq_bigr => a _ /=.
  rewrite (big_morph _ morph_Ropp oppR0) -big_split; apply/eq_bigr => b _ /=.
  rewrite addRC -mulRN -mulRDr addR_opp.
  case/boolP : (PQ (a, b) == 0) => [/eqP ->| H0].
  - by rewrite !mul0R.
  - congr (_ * _); rewrite logDiv //.
    + by rewrite -cPr_Pr_setX_gt0 Pr_gt0 Pr_setX1 Pr_set1.
    + rewrite -dist_neq0; exact: Bivar.dom_by_fstN H0.
rewrite -subR_opp; congr (_ - _).
- rewrite /entropy; congr (- _); apply/eq_bigr => a _.
  by rewrite -big_distrl /= -Bivar.fstE.
- rewrite /CondEntropy.h exchange_big.
  rewrite (big_morph _ morph_Ropp oppR0); apply eq_bigr=> b _ /=.
  rewrite mulRN; congr (- _).
  rewrite big_distrr /=; apply eq_bigr=> a _ /=.
  rewrite mulRA; congr (_ * _); rewrite -/Q.
  by rewrite -[in LHS]Pr_set1 -Pr_setX1 Pr_cPr Pr_set1 -/Q mulRC.
Qed.

Lemma miE3 : mi = `H Q - CondEntropy.h QP. (* 2.40 *)
Proof. by rewrite miE2 entropyB. Qed.

Lemma miE4 : mi = `H P + `H Q - `H PQ. (* 2.41 *)
Proof.
rewrite miE2; move/eqP: (chain_rule QP).
rewrite addRC -subR_eq => /eqP; rewrite -(Swap.dI PQ) -/QP => <-.
rewrite -addR_opp oppRB Swap.fst -/Q addRA; congr (_ - _).
by rewrite JointEntropy.hC.
Qed.

(* nonnegativity of mutual information 2.90 *)
Lemma mi_ge0 : 0 <= mi.
Proof. exact/div_ge0/Prod_dominates_Joint. Qed.

Lemma mi0P : mi = 0 <-> PQ = P `x Q.
Proof.
split; last by rewrite /mi => <-; rewrite div0P //; exact: dominatesxx.
rewrite /mi div0P //; exact: Prod_dominates_Joint.
Qed.

End mutualinfo.
End MutualInfo.

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
  `H P =
  \rsum_(i < n.+1)
   match Bool.bool_dec (O < i)%nat true with
   | right _ => `H (Multivar.head_of P)
   | left H => CondEntropy.h (Swap.d (Multivar.belast_last (Take.d P (lift ord0 i))))
   end.
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
case: Bool.bool_dec => i0; last first.
  rewrite /entropy; congr (- _).
  apply eq_bigr => a _; by rewrite head_of_fst_belast_last.
congr (CondEntropy.h (Swap.d (Multivar.belast_last _))).
apply/dist_ext => /= v.
rewrite 2!Take.dE.
have H1 : (n.+2 - lift ord0 (widen_ord (leqnSn n.+1) i) = (n.+1 - i.+1).+1)%nat.
  by rewrite lift0 /= subSn.
rewrite (big_cast_rV H1) //=.
rewrite -(big_rV_belast_last _ xpredT xpredT) /=.
apply eq_bigr => w /= _.
rewrite Bivar.fstE /=.
apply eq_bigr => a _.
rewrite Multivar.belast_lastE /=.
congr (P _).
apply/rowP => j.
rewrite 2!castmxE /= cast_ord_id /= castmx_comp /=.
case: (ltnP j i.+1) => [ji|ij].
  move=> [:Hj0].
  have @j0 : 'I_n.+1 by apply: (@Ordinal _ j); abstract: Hj0; rewrite (leq_trans ji).
  rewrite (_ : cast_ord _ _ = lshift 1 j0); last exact/val_inj.
  rewrite row_mxEl castmxE /= cast_ord_id /=.
  move=> [:Hj1].
  have @j1 : 'I_i.+1 by apply: (@Ordinal _ j); abstract: Hj1; exact: ji.
  rewrite (_ : cast_ord _ _ = lshift (n.+1 - i.+1) j1); last exact/val_inj.
  rewrite row_mxEl.
  rewrite (_ : cast_ord _ _ = lshift (n.+2 - lift ord0 i) j1); last exact/val_inj.
  by rewrite row_mxEl // castmxE /= cast_ord_id.
case: (ltnP j n.+1) => [jn|nj].
  rewrite (_ : cast_ord _ _ = lshift 1 (Ordinal jn)); last exact/val_inj.
  rewrite row_mxEl castmxE /= cast_ord_id /=.
  move=> [:Hj0].
  have @j0 : 'I_(n.+1 - i.+1).
    apply: (@Ordinal _ (j - i.+1)); abstract: Hj0.
    by rewrite ltn_sub2r // ltnS (leq_trans ij).
  rewrite (_ : cast_ord _ _ = rshift i.+1 j0); last first.
    by apply val_inj => /=; rewrite subnKC.
  rewrite row_mxEr.
  move=> [:Hj1].
  have @j1 : 'I_(n.+2 - lift ord0 i).
    apply: (@Ordinal _ (j - i.+1)); abstract: Hj1.
    by rewrite lift0 ltn_sub2r // ltnS.
  rewrite (_ : cast_ord _ _ = rshift i.+1 j1); last first.
    by apply val_inj => /=; rewrite subnKC.
  rewrite row_mxEr castmxE /=.
  rewrite (_ : cast_ord _ _ = lshift 1 j0); last exact/val_inj.
  by rewrite row_mxEl cast_ord_id.
have {nj}jn : j = ord_max.
  by apply/val_inj/eqP => /=; rewrite eq_sym eqn_leq nj /= -ltnS.
subst j.
rewrite (_ : cast_ord _ _ = rshift n.+1 ord0); last by apply/val_inj => /=.
rewrite row_mxEr mxE.
move=> [:Hj0].
have @j0 : 'I_(n.+2 - lift ord0 i).
  apply: (@Ordinal _ (@ord_max n.+1 - i.+1)); abstract: Hj0.
  by rewrite lift0 /= ltn_sub2l.
rewrite (_ : cast_ord _ _ = rshift i.+1 j0); last first.
  by apply val_inj => /=; rewrite subnKC.
rewrite row_mxEr castmxE /=.
rewrite (_ : cast_ord _ _ = rshift (n.+1 - i.+1) ord0); last by apply val_inj => /=.
by rewrite row_mxEr mxE.
Qed.

End chain_rule_for_entropy.

Section divergence_conditional_distributions.

Variables (A B C : finType) (PQR : {dist A * B * C}).

Definition cdiv1 z := \rsum_(x in {: A * B})
  \Pr_PQR[[set x] | [set z]] * log (\Pr_PQR[[set x] | [set z]] /
    (\Pr_(Proj13.d PQR)[[set x.1] | [set z]] * \Pr_(Proj23.d PQR)[[set x.2] | [set z]])).

Local Open Scope divergence_scope.

Lemma cdiv1_is_div c
  (Hc : Bivar.snd PQR c != 0)
  (Hc1 : (Bivar.snd (Proj13.d PQR)) c != 0)
  (Hc2 : (Bivar.snd (Proj23.d PQR)) c != 0) :
  cdiv1 c = D(CondDist.d PQR c Hc ||
    (CondDist.d (Proj13.d PQR) c Hc1) `x (CondDist.d (Proj23.d PQR) c Hc2)).
Proof.
rewrite /cdiv1 /div; apply eq_bigr => -[a b] /= _; rewrite CondDist.dE.
case/boolP : (\Pr_PQR[[set (a, b)]|[set c]] == 0) => [/eqP ->|H0].
  by rewrite !mul0R.
congr (_ * log (_ / _)).
by rewrite ProdDist.dE 2!CondDist.dE.
Qed.

Lemma cdiv1_ge0 z : 0 <= cdiv1 z.
Proof.
case/boolP : ((Bivar.snd PQR) z == 0) => [/eqP|] z0.
  apply rsumr_ge0 => -[a b] _.
  rewrite {1}/cPr Pr_setX1 Pr_set1 (Bivar.dom_by_snd _ z0) div0R mul0R.
  exact: leRR.
rewrite cdiv1_is_div.
  by rewrite Proj13.snd.
  by rewrite Proj23.snd.
move=> Hz1 Hz2; apply div_ge0.
(* TODO: lemma *)
apply/dominatesP => -[a b].
rewrite ProdDist.dE !CondDist.dE /= mulR_eq0 => -[|].
- rewrite /cPr !Pr_setX1 !Pr_set1 !mulR_eq0 => -[|].
  move/Proj13.domin => ->; by left.
  rewrite Proj13.snd /Rdiv => ->; by right.
- rewrite /cPr !Pr_setX1 !Pr_set1 !mulR_eq0 => -[|].
  move/Proj23.domin => ->; by left.
  rewrite Proj23.snd => ->; by right.
Qed.

End divergence_conditional_distributions.

Section conditional_mutual_information.

Variables (A B C : finType) (PQR : {dist A * B * C}).

(* I(X;Y|Z) = H(X|Z) - H(X|Y,Z) 2.60 *)
Definition cmi := CondEntropy.h (Proj13.d PQR) - CondEntropy.h (TripA.d PQR).

Lemma cmiE : cmi = \rsum_(x in {: A * B * C}) PQR x *
  log (\Pr_PQR[[set x.1] | [set x.2]] /
       (\Pr_(Proj13.d PQR)[[set x.1.1] | [set x.2]] * \Pr_(Proj23.d PQR)[[set x.1.2] | [set x.2]])).
Proof.
rewrite /cmi 2!CondEntropy.hE /= subR_opp (big_morph _ morph_Ropp oppR0).
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
rewrite (big_morph _ morph_Ropp oppR0) /= exchange_big -big_split /=.
rewrite (eq_bigr (fun i => PQR ((i.1, i.2), c) * log
       (\Pr_PQR[[set (i.1, i.2)] | [set c]] /
        (\Pr_(Proj13.d PQR)[[set i.1] | [set c]] * \Pr_(Proj23.d PQR)[[set i.2] | [set c]])))); last by case.
rewrite -(pair_bigA _ (fun i1 i2 => PQR (i1, i2, c) * log
  (\Pr_PQR[[set (i1, i2)] | [set c]] /
  (\Pr_(Proj13.d PQR)[[set i1] | [set c]] * \Pr_(Proj23.d PQR)[[set i2] | [set c]])))).
apply eq_bigr => a _ /=.
rewrite Swap.dE Proj13.dE big_distrl /= (big_morph _ morph_Ropp oppR0) -big_split.
apply eq_bigr => b _ /=.
rewrite Swap.dE TripA.dE /= -mulRN -mulRDr.
case/boolP : (PQR (a, b, c) == 0) => [/eqP ->| H0]; first by rewrite !mul0R.
congr (_ * _).
rewrite addRC addR_opp -logDiv; last 2 first.
  rewrite -cPr_Pr_setX_gt0 Pr_gt0 Pr_setX1 Pr_set1; exact: TripA.dominN H0.
  rewrite -cPr_Pr_setX_gt0 Pr_gt0 Pr_setX1 Pr_set1; exact: Proj13.dominN H0.
congr (log _).
rewrite divRM; last 2 first.
  apply/eqP.
  rewrite -cPr_gt0 -cPr_Pr_setX_gt0 Pr_gt0 Pr_setX1 Pr_set1; exact: Proj13.dominN H0.
  apply/eqP.
  rewrite -cPr_gt0 -cPr_Pr_setX_gt0 Pr_gt0 Pr_setX1 Pr_set1; exact: Proj23.dominN H0.
rewrite {2}/Rdiv -mulRA mulRCA {1}/Rdiv [in LHS]mulRC; congr (_ * _).
(* TODO: lemma? *)
rewrite /cPr !Pr_setX1 !Pr_set1 TripA.dE /= {1 2}/Rdiv -mulRA; congr (_ * _).
rewrite -invRM; last 2 first.
  apply/eqP; exact: Bivar.dom_by_sndN H0.
  apply/eqP; rewrite mulR_neq0; apply/andP; split.
  exact: Proj23.dominN H0.
  move/Bivar.dom_by_sndN in H0; by rewrite invR_neq0 // Proj23.snd.
congr (/ _).
rewrite Proj23.snd mulRCA mulRV ?mulR1 //.
by rewrite Proj23.def.
exact: Bivar.dom_by_sndN H0.
Qed.

Let R := Bivar.snd PQR.

Lemma cmiE2 : cmi = \rsum_(z in C) R z * cdiv1 PQR z.
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
by rewrite Pr_setX1 Pr_set1.
Qed.

(* 2.92 *)
Lemma cmi_ge0 : 0 <= cmi.
Proof.
rewrite cmiE2; apply rsumr_ge0 => c _.
apply mulR_ge0; [exact: dist_ge0 | exact: cdiv1_ge0].
Qed.

End conditional_mutual_information.

Section conditional_relative_entropy.

Variables (A B : finType) (P Q : {dist B * A}).
Let P2 : dist A := Bivar.snd P.

(* eqn 2.65 *)
Definition cre := \rsum_(x in A) P2 x * \rsum_(y in B)
  \Pr_P[[set y]|[set x]] * log (\Pr_P[[set y]|[set x]] / \Pr_Q[[set y]|[set x]]).

Let Q2 : dist A := Bivar.snd Q.

Local Open Scope divergence_scope.
Local Open Scope reals_ext_scope.

(* thm 2.5.3 *)
Lemma chain_rule_relative_entropy : P << Q -> D(P || Q) = D(P2 || Q2) + cre.
Proof.
move=> PQ.
rewrite {2}/div.
rewrite /cre.
rewrite -big_split /=.
rewrite {1}/div /=.
rewrite (eq_bigr (fun a => P (a.1, a.2) * (log (P (a.1, a.2) / (Q (a.1, a.2)))))); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => P (a1, a2) * (log (P (a1, a2) / (Q (a1, a2)))))) /=.
rewrite exchange_big; apply eq_bigr => a _ /=.
rewrite [in X in _ = X * _ + _]/P2 [in X in _ = X * _ + _]Bivar.sndE.
rewrite big_distrl /=.
rewrite big_distrr /=.
rewrite -big_split /=.
apply eq_bigr => b _.
rewrite mulRA.
rewrite (_ : P2 a * _ = P (b, a)); last first.
  rewrite /cPr Pr_set1 -/P2 mulRCA.
  case/boolP : (P2 a == 0) => [/eqP|] P2a0.
    have Pba0 : P (b, a) = 0 by apply Bivar.dom_by_snd.
    by rewrite Pr_setX1 Pr_set1 Pba0 mul0R.
  by rewrite mulRV // mulR1 Pr_setX1 Pr_set1.
rewrite -mulRDr.
case/boolP : (P (b, a) == 0) => [/eqP ->|H0]; first by rewrite !mul0R.
congr (_ * _).
have P2a0 : P2 a != 0 by apply: Bivar.dom_by_sndN H0.
have Qba0 := dominatesEN PQ H0.
have Q2a0 : Q2 a != 0 by apply: Bivar.dom_by_sndN Qba0.
rewrite -logM; last 2 first.
  apply/divR_gt0; rewrite -dist_neq0 //.
  apply/divR_gt0; by rewrite -cPr_Pr_setX_gt0 Pr_setX1 Pr_set1 -dist_neq0.
congr (log _).
rewrite /cPr !Pr_setX1 !Pr_set1 -/P2 -/Q2.
rewrite {3}/Rdiv.
rewrite Rinv_Rdiv; [|exact/eqP|exact/eqP].
rewrite !mulRA; congr (_ * _).
rewrite (mulRC _ (P (b, a))).
rewrite -mulRA.
rewrite (mulRC (/ _) (Q2 a)).
rewrite -/(Rdiv (Q2 a) (P2 a)) -(Rinv_Rdiv (P2 a) (Q2 a)); [|exact/eqP|exact/eqP].
rewrite -mulRA mulRV ?mulR1 // mulR_eq0' negb_or P2a0 /=.
apply: contra Q2a0; exact: invR_eq0.
Qed.

End conditional_relative_entropy.

Section chain_rule_for_information. (* theorem 2.5.1 *)

Variables (A : finType).
Let B := A. (* need in the do-not-delete-me step *)
Variables (n : nat) (PY : {dist 'rV[A]_n.+1 * B}).
Let P : {dist 'rV[A]_n.+1} := Bivar.fst PY.
Let Y : {dist B} := Bivar.snd PY.

Let g0 : {dist 'rV[A]_n.+1 * B} -> {dist A * B} := fun d => PairNth.d d ord0.
Let pre_giA : {dist 'rV[A]_n.+1 * B} -> forall i : 'I_n.+1, {dist A * 'rV[A]_i * B} := fun d i =>
  TripC12.d (PairTake.d d i).
Let gi : {dist 'rV[A]_n.+1 * B} -> forall i : 'I_n.+1, {dist A * B * 'rV[A]_i} :=
  fun d i => TripC23.d (pre_giA d i).
Let giA : {dist 'rV[A]_n.+1 * B} -> forall i : 'I_n.+1, {dist A * ('rV[A]_i * B)} :=
  fun d i => TripA.d (pre_giA d i).

Local Open Scope vec_ext_scope.

Lemma chain_rule_information :
  (* 2.62 *) MutualInfo.mi PY = \rsum_(j < n.+1)
    match Bool.bool_dec (O < j)%nat true with
    | right _ => MutualInfo.mi (g0 PY)
    | left H => cmi (gi PY j)
    end.
Proof.
rewrite MutualInfo.miE2 chain_rule_rV.
have -> : CondEntropy.h PY = \rsum_(j < n.+1)
  match Bool.bool_dec (0 < j)%nat true with
    | right _ => CondEntropy.h (g0 PY)
    | left _ => CondEntropy.h (giA PY j)
  end.
  move/eqP : (chain_rule (Swap.d PY)).
  rewrite Swap.dI addRC -subR_eq Swap.fst -/Y => /eqP <-.
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
  case: (Bool.bool_dec _ _) => j0.
  - rewrite /giA /pre_giA.
    rewrite /CondEntropy.h /=.
    have H1 : bump 0 j = j.+1 by rewrite /bump leq0n.
    rewrite (big_cast_rV H1) /=.
    rewrite -(big_rV_cons_behead _ xpredT xpredT) /= exchange_big /= pair_bigA.
    have H2 : forall (v : 'rV_j) (b : B) (a : A) (H1' : (1 + j)%nat = lift ord0 j),
      (Swap.d (Multivar.belast_last (Take.d YP (lift ord0 (lift ord0 j)))))
      (a, (castmx (erefl 1%nat, H1') (row_mx (\row__ b) v))) =
      (TripA.d (TripC12.d (PairTake.d PY j))) (a, (v, b)).
      move=> v b a H1'.
      rewrite Swap.dE Multivar.belast_lastE /=.
      rewrite TripA.dE /= TripC12.dE /=.
      rewrite PairTake.dE /PairTake.f /=.
      rewrite Take.dE /=.
      have H2 : (n.+2 - bump 0 (bump 0 j) = n - j)%nat by rewrite /bump !leq0n !add1n 2!subSS.
      rewrite (big_cast_rV H2); apply eq_bigr => w _.
      rewrite /YP Multivar.from_bivarE Swap.dE /=.
      congr (PY (_, _)).
        apply/rowP => i.
        rewrite castmxE /= /rbehead mxE castmxE /= cast_ord_id /=.
        case: (ltnP i j) => [ij|].
          move=> [:Hi0].
          have @i0 : 'I_(bump 0 j).+1.
            apply: (@Ordinal _ i.+1); abstract: Hi0.
            by rewrite /bump leq0n add1n ltnS ltnW // ltnS.
          rewrite (_ : cast_ord _ _ = lshift (n - j) i0); last exact/val_inj.
          rewrite row_mxEl castmxE /= cast_ord_id.
          have @i1 : 'I_j.+1 by apply: (@Ordinal _ i.+1); rewrite ltnS.
          rewrite (_ : cast_ord _ _ = lshift 1 i1); last exact/val_inj.
          rewrite row_mxEl castmxE /= cast_ord_id.
          rewrite (_ : cast_ord _ _ = rshift 1 (Ordinal ij)); last exact/val_inj.
          rewrite row_mxEr.
          have @i2 : 'I_(j + 1) by apply: (@Ordinal _ i); rewrite addn1 ltnW.
          rewrite (_ : cast_ord _ _ = lshift (n - j) i2); last exact/val_inj.
          rewrite row_mxEl.
          rewrite (_ : i2 = lshift 1 (Ordinal ij)); last exact/ val_inj.
          by rewrite row_mxEl.
        rewrite leq_eqVlt => /orP[/eqP|] ji.
          move=> [:Hi0].
          have @i0 : 'I_((bump 0 j).+1).
            apply: (@Ordinal _ i.+1); abstract: Hi0.
            by rewrite /bump leq0n add1n ltnS ji.
          rewrite (_ : cast_ord _ _ = lshift (n - j) i0); last first.
            apply/val_inj => /=; by rewrite /bump !leq0n! add1n.
          rewrite row_mxEl castmxE cast_ord_id /=.
          set x := castmx _ _.
          rewrite (_ : cast_ord _ _ = rshift j.+1 (Ordinal (ltn_ord ord0))); last first.
            apply val_inj => /=; by rewrite addn0 ji.
          rewrite row_mxEr mxE.
          have @i1 : 'I_(j + 1) by apply: (@Ordinal _ i); rewrite addn1 ji.
          rewrite (_ : cast_ord _ _ = lshift (n - j) i1); last exact/val_inj.
          rewrite row_mxEl.
          rewrite (_ : i1 = rshift j (Ordinal (ltn_ord ord0))); last first.
            apply/val_inj => /=; by rewrite addn0 ji.
          by rewrite row_mxEr mxE.
        move=> [:Hi2].
        have @i2 : 'I_(n - j).
          apply: (@Ordinal _ (i - j.+1)); abstract:  Hi2.
          by rewrite subnS prednK ?subn_gt0 // leq_sub2r // -ltnS.
        rewrite (_ : cast_ord _ _ = rshift (bump 0 j).+1 i2); last first.
          apply val_inj => /=; by rewrite /bump !leq0n !add1n addSn subnKC.
        rewrite row_mxEr castmxE /= cast_ord_id.
        move=> [:Hi3].
        have @i3 : 'I_(n - j).
          apply: (@Ordinal _ (i - j.+1)); abstract: Hi3.
          by rewrite subnS prednK ?subn_gt0 // leq_sub2r // -ltnS.
        rewrite (_ : cast_ord _ _ = rshift (j + 1) i3); last first.
          apply val_inj => /=; by rewrite addn1 subnKC.
        rewrite row_mxEr; congr (w _ _); exact/val_inj.
      rewrite castmxE /= cast_ord_id.
      set i0 : 'I_(bump 0 j).+1 := Ordinal (ltn_ord ord0).
      rewrite (_ : cast_ord _ _ = lshift (n - j) i0); last exact/val_inj.
      rewrite row_mxEl castmxE cast_ord_id /=.
      set i1 : 'I_j.+1 := Ordinal (ltn_ord ord0).
      rewrite (_ : cast_ord _ _ = lshift 1 i1); last exact/val_inj.
      rewrite row_mxEl castmxE /= cast_ord_id.
      rewrite (_ : cast_ord _ _ = lshift j (Ordinal (ltn_ord ord0))); last exact/val_inj.
      by rewrite row_mxEl mxE.
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
    - rewrite 2!Bivar.sndE; apply eq_bigr => a' _; by rewrite H2.
    - rewrite 2!Bivar.sndE; apply eq_bigr => a' _; by rewrite H2.
  - have {j0}j0 : j = ord0 by move/negP : j0; rewrite lt0n negbK => /eqP j0; exact/val_inj.
    subst j.
    rewrite /g0 /CondEntropy.h /=.
    apply big_rV_1 => // a1.
    have H1 : forall a,
     (Swap.d (Multivar.belast_last (Take.d YP (lift ord0 (lift ord0 ord0))))) (a, a1) =
     (PairNth.d PY ord0) (a, a1 ``_ ord0).
      move=> a.
      rewrite Swap.dE Multivar.belast_lastE Take.dE PairNth.dE /=.
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
    - rewrite /cPr /Pr !big_setX /= !big_set1.
      rewrite H1; congr (_ / _).
      rewrite !Bivar.sndE; apply eq_bigr => a0 _.
      by rewrite H1.
    - rewrite /cPr /Pr !big_setX /= !big_set1.
      rewrite H1; congr (_ / _).
      rewrite !Bivar.sndE; apply eq_bigr => a0 _.
      by rewrite H1.
rewrite -addR_opp (big_morph _ morph_Ropp oppR0) -big_split /=; apply eq_bigr => j _ /=.
case: Bool.bool_dec => j0 /=.
  rewrite /cmi /giA -/P; congr (_ - _).
  - congr CondEntropy.h.
    by rewrite /gi /pre_giA Proj13_TripC23 TripC12.fst belast_last_take.
  - rewrite /gi /pre_giA TripC23.def TripC12.dI /CondEntropy.h /=.
    rewrite (eq_bigr (fun a => (Bivar.snd (TripA.d (TripC12.d (PairTake.d PY j)))) (a.1, a.2) *
       CondEntropy.h1 (TripA.d (TripC12.d (PairTake.d PY j))) (a.1, a.2))); last by case.
    rewrite -(pair_bigA _ (fun a1 a2 => (Bivar.snd (TripA.d (TripC12.d (PairTake.d PY j)))) (a1, a2) *
       CondEntropy.h1 (TripA.d (TripC12.d (PairTake.d PY j))) (a1, a2))) /=.
    rewrite exchange_big pair_bigA /=; apply eq_bigr => -[b v] _ /=.
    congr (_ * _).
    - rewrite !Bivar.sndE; apply eq_bigr=> a _.
      by rewrite !TripA.dE /= Swap.dE TripC12.dE /= TripA.dE.
    - (* TODO: lemma? *)
      rewrite /CondEntropy.h1; congr (- _); apply eq_bigr => a _.
      by rewrite -!setX1 -cPr_TripA_TripC23 TripC23.def TripC12.dI.
rewrite /g0 MutualInfo.miE2 addR_opp; congr (`H _ - _).
rewrite /Multivar.head_of.
apply/dist_ext => a.
rewrite [in RHS]Bivar.fstE.
transitivity ((Nth.d (Bivar.fst PY) ord0) a); last first.
  (* TODO: lemma *)
  rewrite Nth.dE -big_rV_cons /=.
  transitivity (\rsum_(v in 'rV_n) \rsum_(b in B)
      (PY (castmx (erefl, @add1n n) (row_mx (\row__ a) v), b))).
    apply eq_bigr => /= w _; rewrite Bivar.fstE.
    apply eq_bigr => b _; congr (PY (_, b)).
    apply/rowP => i; rewrite castmxE /= cast_ord_id.
    congr (_ _ _); exact/val_inj.
  rewrite exchange_big /=; apply eq_bigr => b _.
  rewrite PairNth.dE /=.
  rewrite [in RHS](eq_bigr (fun x => PY (x.1, x.2))); last by case.
  rewrite -(pair_big (fun x : 'rV__ => x ord0 ord0 == a) (fun x => x == b) (fun i1 i2 => PY (i1, i2))) /=.
  rewrite -big_rV_cons /=; apply eq_bigr => w _.
  rewrite big_pred1_eq /=; congr (PY (_, b)).
  apply/rowP => i; rewrite castmxE /= cast_ord_id; congr (_ _ _).
  exact/val_inj.
rewrite Bivar.fstE /= Nth.dE /= -big_rV_cons /=.
apply eq_bigr => v _; by rewrite Multivar.to_bivarE.
Qed.

End chain_rule_for_information.

Section conditioning_reduces_entropy.

Variables (A B : finType) (PQ : {dist A * B}).
Let P := Bivar.fst PQ.
Let Q := Bivar.snd PQ.
Let QP := Swap.d PQ.

(* 2.95 *)
Lemma information_cant_hurt : CondEntropy.h PQ <= `H P.
Proof. rewrite -subR_ge0 -MutualInfo.miE2; exact: MutualInfo.mi_ge0. Qed.

End conditioning_reduces_entropy.

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
  rewrite mulR_neq0; apply/andP; split.
    (* TODO: lemma? *)
    rewrite /cPr mulR_neq0; apply/andP; split.
      (* TODO: lemma? *)
      rewrite Pr_setX1 Pr_set1.
      case: x => [[x11 x12] x2] in H0 *.
      exact: Proj13.dominN H0.
    rewrite invR_neq0 // Pr_set1 Proj13.snd.
    case: x => [x1 x2] in H0 *.
    exact: Bivar.dom_by_sndN H0.
  (* TODO: lemma? *)
  rewrite /cPr mulR_neq0; apply/andP; split.
    rewrite Pr_setX1 Pr_set1.
    case: x => [[x11 x12] x2] in H0 *.
    exact: Proj23.dominN H0.
  rewrite invR_neq0 // Pr_set1 Proj23.snd.
  case: x => [x1 x2] in H0 *.
  exact: Bivar.dom_by_sndN H0.
(* TODO: lemma? *) (* 2.118 *)
transitivity (Pr PRQ [set x] / Pr Q [set x.2]).
  rewrite /cPr Pr_setX1 {2}/PRQ TripC23.snd -/Q; by case: x H0.
transitivity (Pr PQ [set (x.1.1,x.2)] * \Pr_RQ[[set x.1.2]|[set x.2]] / Pr Q [set x.2]).
  congr (_ / _).
  case: x H0 => [[a c] b] H0 /=.
  rewrite /PRQ Pr_set1 TripC23.dE /= mc; congr (_ * _).
  rewrite /cPr {2}/QP Swap.snd -/P Pr_set1 mulRCA mulRV ?mulR1; last first.
    apply Bivar.dom_by_fstN with b.
    apply Bivar.dom_by_fstN with c.
    by rewrite TripC23.dE in H0.
  by rewrite /QP -Swap.Pr Pr_setX1.
rewrite {1}/Rdiv -mulRA mulRCA mulRC; congr (_ * _).
  rewrite /cPr Proj13.snd -/Q {2}/PRQ TripC23.snd -/Q -/(Rdiv _ _); congr (_ / _).
  by rewrite /PRQ /PQ Pr_setX1 Proj13_TripC23.
rewrite /cPr Proj23.snd; congr (_ / _).
- by rewrite /RQ /PRQ Proj23.def TripC23.sndA.
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

Require Import channel.

Local Open Scope channel_scope.

Section condentropychan_condentropy.

Variables (A B : finType) (W : `Ch_1(A, B)) (P : dist A).
Let PQ := JointDistChan.d P W.
Let QP := Swap.d PQ.

Lemma cond_entropy_chanE : (forall (a : A) (b : B), cPr QP [set b] [set a] = W a b) ->
  `H(W | P) = CondEntropy.h QP.
Proof.
move=> H.
rewrite CondEntropyChan.hE CondEntropy.hE (big_morph _ morph_Ropp oppR0).
apply eq_bigr => a _.
rewrite /entropy mulRN; congr (- _).
rewrite big_distrr /=; apply eq_bigr => b _.
rewrite !Swap.dE JointDistChan.dE /= mulRCA mulRA; congr (_ * log _).
by rewrite H.
Qed.

End condentropychan_condentropy.
