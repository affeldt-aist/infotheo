(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint fingroup.
From mathcomp Require Import finalg perm zmodp matrix mxalgebra vector.
Require Import ssr_ext f2.

(**md**************************************************************************)
(* # Additional lemmas about row vectors and other types from ssralg.v        *)
(*                                                                            *)
(* Overview:                                                                  *)
(* - Section prod_rV:                                                         *)
(*   Technical lemmas to switch between products of vectors (A^n x B^n) and   *)
(*   vectors of products (A x B)^n                                            *)
(* - Section AboutRowTuple:                                                   *)
(*   Conversions between row vectors and tuples                               *)
(* - Several seq-like definitions for row vectors:                            *)
(*   rbehead, rbelast, rlast, row_take, row_drop                              *)
(* - Some lemmas about matrices (and their rank)                              *)
(*                                                                            *)
(* ```                                                                        *)
(*        v ``_ i == the ith element of v                                     *)
(*         supp v == the set of indices of elements from v that are not 0     *)
(*  v `[ i := x ] == v where the ith element has been replaced with x         *)
(*         v \# S == the vector of size #|S| containing the elements of       *)
(*                   index i \in S                                            *)
(* ```                                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(*   GF2_of_F2    == morphism between F_2 and GF(2^m)                         *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.

Notation "u '``_' i" := (u ord0 i) (at level 3,
  i at level 2, left associativity, format "u '``_' i") : vec_ext_scope.
Reserved Notation "v `[ i := x ]" (at level 20).
Reserved Notation "t \# V" (at level 55, V at next level).

Section AboutRingType.
Variable R : ringType.

Lemma iter_addr0 : forall n x, iter n (+%R (0 : R)) x = x.
Proof. elim=> //= n IH x. by rewrite IH add0r. Qed.

Lemma iter_addr0_cV r : forall n (x : 'cV[R]_r), iter n (+%R 0) x = x.
Proof. elim=> //= n IH x; by rewrite IH add0r. Qed.
End AboutRingType.

Local Open Scope vec_ext_scope.

Section support_set.
Variables (R : ringType) (n : nat).
Implicit Types e : 'rV[R]_n.

Definition supp e : {set 'I_n} := [set i | e ``_ i != 0].

Lemma insupp e i : (i \in supp e) = (e ``_ i != 0).
Proof. by rewrite in_set. Qed.

Lemma sum_supp e x :
  \sum_(i < n) e ``_ i * x ^+ i = \sum_(i in supp e) e ``_ i * x ^+ i.
Proof.
rewrite (bigID (mem (supp e))) /= addrC (eq_bigr (fun=> 0)); last first.
  move=> ?; rewrite inE /= negbK => /eqP ->; by rewrite mul0r.
by rewrite big_const /= iter_addr0 add0r.
Qed.

Lemma supp_set0 e : (supp e == set0) = (e == 0).
Proof.
apply/idP/idP => [/eqP/setP HE |/eqP ]; last first.
  rewrite /supp => ->; by apply/eqP/setP => i; rewrite !inE /= mxE eqxx.
apply/eqP/rowP => i; rewrite mxE.
move: (HE i); by rewrite !inE /= => /negbT; rewrite negbK => /eqP.
Qed.

Lemma supp0 : supp (0 : 'rV[R]_n) = set0.
Proof. apply/setP => i; by rewrite !inE mxE eqxx. Qed.

End support_set.

Definition row_set B n (n0 : 'I_n) (x : B) (d : 'rV_n) :=
  \row_(i < n) if i == n0 then x else d ``_ i.

Notation "v `[ i := x ]" := (row_set i x v) : vec_ext_scope.

Lemma inj_row_set (A : ringType) n n0 (d : 'rV_n) :
  {in A &, injective ((row_set n0)^~ d)}.
Proof. move=> a b _ _ /= /rowP /(_ n0); by rewrite mxE eqxx mxE eqxx. Qed.

Lemma row_setC n A (i j : 'I_n) (a b : A) d :
  i != j -> d `[ j := b ] `[ i := a ] = d `[ i := a ] `[ j := b ].
Proof.
move=> ij; apply/rowP => k; rewrite !mxE.
by case: ifP => // /eqP ->; case: ifPn => //; rewrite (negbTE ij).
Qed.

Lemma row_setK n A (i : 'I_n) (a : A) d : d `[i := a] ``_ i = a.
Proof. by rewrite /row_set mxE eqxx. Qed.

Section sub_vec_sect.
Variables (A : Type) (n : nat).

Definition sub_vec (t : 'rV[A]_n) (S : {set 'I_n}) : 'rV[A]_#| S | :=
  \row_(j < #|S|) t ``_ (enum_val j).
(* NB: enum_val j is the jth item of enum S *)

End sub_vec_sect.

Notation "t \# S" := (sub_vec t S) : vec_ext_scope.

Section prod_rV.
Variables A B : Type.

Definition prod_rV n (x : 'rV[A]_n * 'rV[B]_n) : 'rV[A * B]_n :=
  \row_(k < n) (x.1 ``_ k, x.2 ``_ k).

Definition rV_prod n (x : 'rV[A * B]_n) : {: 'rV[A]_n * 'rV[B]_n} :=
  (\row_(k < n) (x ``_ k).1, \row_(k < n) (x ``_ k).2).

Lemma prod_rVK n (x : 'rV[A]_n * 'rV[B]_n) : rV_prod (prod_rV x) = x.
Proof. case: x => x1 x2; congr (_ , _); apply/rowP => b; by rewrite !mxE. Qed.

Lemma rV_prodK n (x : 'rV[A * B]_n) : prod_rV (rV_prod x) = x.
Proof. apply/rowP => b; rewrite !mxE; by case: (x ``_ b). Qed.

Lemma fst_tnth_prod_rV n (x : {: 'rV[A]_n * 'rV[B]_n}) i :
  x.1 ``_ i = ((prod_rV x) ``_ i).1.
Proof. by rewrite mxE. Qed.

Lemma snd_tnth_prod_rV n (x : {: 'rV[A]_n * 'rV[B]_n}) i :
  x.2 ``_ i = ((prod_rV x) ``_ i).2.
Proof. by rewrite mxE. Qed.

End prod_rV.

Section AboutRowTuple.
Variables A B : predArgType.

Definition tuple_of_row n (v : 'rV[A]_n) := [tuple v ``_ i | i < n].

Local Open Scope tuple_ext_scope.

Definition row_of_tuple n (t : n.-tuple A) := \row_(i < n) (t !_ i).

Lemma row_of_tupleK n (t : n.-tuple A) : tuple_of_row (row_of_tuple t) = t.
Proof. apply eq_from_tnth => n0; by rewrite tnth_mktuple mxE. Qed.

Lemma row_of_tuple_inj n : injective (@row_of_tuple n).
Proof. by move=> a b ab; rewrite -(row_of_tupleK b) -ab row_of_tupleK. Qed.

Lemma tuple_of_row_inj n : injective (@tuple_of_row n).
Proof.
move=> i j ij.
apply/rowP => m0.
move/(congr1 (fun x => x !_ m0)) : ij.
by rewrite 2!tnth_mktuple.
Qed.

Local Close Scope tuple_ext_scope.

Lemma tuple_of_rowK n (v : 'rV[A]_n) : row_of_tuple (tuple_of_row v) = v.
Proof. apply tuple_of_row_inj; by rewrite row_of_tupleK. Qed.

Definition row_of_seq
  (f : B -> A) (b : B) (l : seq B) n (H : size l == n) : 'rV[A]_n.
Proof.
exact (matrix_of_fun matrix_key (fun i j => f (nth b l j))).
Defined.

Lemma row_of_seqK n l H f b :
  map f l = tuple_of_row (@row_of_seq f b l n H).
Proof.
apply/(@eq_from_nth _ (f b)) => [|i Hi].
  by rewrite size_map size_tuple (eqP H).
rewrite size_map in Hi.
rewrite (nth_map b) //.
rewrite (eqP H) in Hi.
transitivity (tnth (tuple_of_row (row_of_seq f b H)) (Ordinal Hi)).
  by rewrite tnth_mktuple mxE.
apply set_nth_default; by rewrite size_tuple.
Qed.

Definition col_of_seq
  (f : B -> A) (b : B) (l : seq B) n (H : size l == n) : 'cV[A]_n.
Proof.
exact (matrix_of_fun matrix_key (fun i j => f (nth b l i))).
Defined.

End AboutRowTuple.

Arguments row_of_seq {A} {B} _ _ l n.
Arguments col_of_seq {A} {B} _ _ l n.

Lemma tuple_of_row_ord0 (F : Type) (y : 'rV[F]_0) : tuple_of_row y = [tuple of [::]].
Proof. apply eq_from_tnth; by case. Qed.

Local Open Scope tuple_ext_scope.

Lemma tuple_of_row_row_mx (C : finType) n1 n2 (v1 : 'rV[C]_n1) (B : 'rV[C]_n2) :
  tuple_of_row (row_mx v1 B) = [tuple of tuple_of_row v1 ++ tuple_of_row B].
Proof.
apply eq_from_tnth => n0.
rewrite tnth_mktuple mxE.
case: splitP => [n3 n0n3|n3 n0n1n3].
  rewrite /tnth nth_cat size_tuple (_ : (n0 < n1 = true)%nat); last by rewrite n0n3 ltn_ord.
  transitivity ((tuple_of_row v1) !_ n3); first by rewrite tnth_mktuple.
  rewrite /tnth n0n3; apply set_nth_default; by rewrite size_tuple.
rewrite /tnth nth_cat size_tuple (_ : (n0 < n1 = false)%nat); last first.
  rewrite n0n1n3; apply/negbTE; by rewrite -leqNgt leq_addr.
  transitivity ((tuple_of_row B) !_ n3); first by rewrite tnth_mktuple.
  rewrite /tnth (_ : (n0 - n1 = n3)%nat); last by rewrite n0n1n3 addnC addnK.
  apply set_nth_default; by rewrite size_tuple.
Qed.

Local Close Scope tuple_ext_scope.

Lemma row_to_seq_0 n : tuple_of_row 0 = [tuple of nseq n ( 0 : 'F_2)].
Proof.
apply eq_from_tnth => i.
by rewrite {2}/tnth nth_nseq (ltn_ord i) tnth_mktuple mxE.
Qed.

Definition rowF2_tuplebool {n : nat} (M : 'rV['F_2]_n) : n.-tuple bool :=
  [tuple of map (fun x => x != 0) (tuple_of_row M)].
Definition row_of_bitseq := row_of_seq F2_of_bool false.
Definition col_of_bitseq := col_of_seq F2_of_bool false.

Section row_mx_ext.
Context {A : Type} {n : nat}.

Definition rbehead (x : 'rV[A]_n.+1) := col' ord0 x.

Lemma rbehead_row_mx (x : 'rV_n) a : rbehead (row_mx (\row_(j < 1) a) x) = x.
Proof.
apply/rowP => i; rewrite mxE (_ : lift _ _ = rshift 1%nat i); last exact/val_inj.
by rewrite (@row_mxEr _ _ 1).
Qed.

Lemma row_mx_row_ord0 (x : 'rV[A]_n) a : (row_mx (\row_(k < 1) a) x) ``_ 0 = a.
Proof.
rewrite [X in _ _ X = _](_ : _ = lshift n 0 :> 'I_(1 + n)); last exact/val_inj.
by rewrite row_mxEl mxE.
Qed.

Lemma row_mx_rbehead (x : 'rV_(1 + n)) : row_mx (\row__ (x ``_ 0)) (rbehead x) = x.
Proof.
apply/rowP => i; rewrite mxE; case: splitP=> [j|j i1j].
- rewrite (ord1 j) mxE => i0; congr (x _ _); exact/val_inj.
- rewrite mxE; congr (x _ _); exact/val_inj.
Qed.

Definition rbelast (x : 'rV[A]_n.+1) := \row_(i < n) x ``_ (widen_ord (leqnSn _) i).

Definition rlast (x : 'rV[A]_n.+1) := x ``_ ord_max.

Lemma row_mx_row_ord_max (x : 'rV[A]_n) a :
  rlast (castmx (erefl 1%nat, addn1 n) (row_mx x (\row_(k < 1) a))) = a.
Proof.
rewrite /rlast castmxE /= mxE /=; case: splitP => [j Hj|k _].
by move: (ltn_ord j); rewrite -Hj ltnn.
by rewrite (ord1 k) mxE.
Qed.

Lemma row_mx_rbelast (x : 'rV_n.+1) :
  castmx (erefl 1%N, addn1 n) (row_mx (rbelast x) (\row__ (rlast x))) = x.
Proof.
apply/rowP => i; rewrite castmxE /= mxE; case: splitP => [j /= ij|k /=].
rewrite mxE; congr (x _ _); exact/val_inj.
rewrite (ord1 k) addn0 => ni; rewrite mxE; congr (x _ _); exact/val_inj.
Qed.

Lemma rbelast_row_mx (x : 'rV_n) a :
  rbelast (castmx (erefl 1%N, addn1 n) (row_mx x (\row_(j < 1) a))) = x.
Proof.
apply/rowP => i; rewrite !(mxE,castmxE) /=; case: splitP => [j /= ij|k /=].
by congr (x _ _); apply/val_inj.
rewrite (ord1 k) addn0 => ni; move: (ltn_ord i); by rewrite ni ltnn.
Qed.

End row_mx_ext.

Section row_mxA'.
Variables (A : finType) (n : nat) (i : 'I_n.+1).

Lemma row_mxA' (w1 : 'rV_(n - i)) (a : A) (w : 'rV_i)
    (H1 : (n.+1 - i)%nat = (n - i)%nat.+1) (H2 : _)
    (H3 : (i + 1%nat + (n - i))%nat = n.+1) :
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

Lemma col_matrix (R : ringType) m n (A : 'I_m -> 'cV[R]_(n.+1)) (i : 'I_m) :
  col i (\matrix_(a < n.+1, b < m) (A b) a ord0) = A i.
Proof. by apply/colP => a; rewrite !mxE. Qed.

Lemma ltnS' n m : (n < m.+1)%nat -> (n <= m)%nat.
Proof. by rewrite ltnS. Qed.

Section rV_take_drop.
Variables (A : Type) (n : nat).
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

Section AboutPermPid.

Variable R : comRingType.

(* s : 0 -> s0; 1 -> s1, etc.
in column 0, there is a 1 at line s0

         | 0 1 |
[a b ] * | 1 0 |  = [b a]
*)
Lemma vec_perm_mx n (s : 'S_n) (z : 'rV[R]_n) :
  z *m perm_mx s = \matrix_(i < 1, j < n) z i ((s^-1)%g j).
Proof.
apply/rowP => j; rewrite !mxE (bigID (pred1 ((s^-1)%g j))) /=.
rewrite big_pred1_eq !mxE {2}permE perm_invK eqxx mulr1 (eq_bigr (fun _ => 0)).
- by rewrite big_const_seq iter_addr0 addr0.
- move=> i H.
  rewrite !mxE (_ : (s i == j) = false); first by rewrite mulr0.
  apply/eqP; move/eqP in H; contradict H.
  by rewrite -H -permM (mulgV s) perm1.
Qed.

Lemma perm_mx_vec n (s : 'S_n) (z : 'cV[R]_n) :
  perm_mx s *m z = \matrix_(i < n, j < 1) z (s i) j.
Proof.
apply/colP => i; rewrite !mxE (bigID (pred1 (s i))) /=.
rewrite big_pred1_eq {1}/perm_mx !mxE eqxx mul1r (eq_bigr (fun _ => 0)).
- by rewrite big_const_seq iter_addr0 addr0.
- move=> j; move/negbTE => H.
  by rewrite !mxE eq_sym H /= mul0r.
Qed.

Lemma pid_mx_inj r n (a b : 'rV[R]_r) : (r <= n)%N ->
  a *m (@pid_mx _ r n r) = b *m (@pid_mx _ r n r) -> a = b.
Proof.
move=> Hrn /matrixP Heq.
apply/matrixP => x y.
move: {Heq}(Heq x (widen_ord Hrn y)).
rewrite !mxE (ord1 x){x} (bigID (pred1 y)) /= big_pred1_eq (eq_bigr (fun _ => 0)); last first.
  move=> i Hiy.
  rewrite mxE /= (_ : nat_of_ord _ == nat_of_ord _ = false) /=; last first.
    by move/negbTE : Hiy.
  by rewrite mulr0.
rewrite big_const_seq iter_addr0 (bigID (pred1 y)) /= big_pred1_eq (eq_bigr (fun _ => 0)); last first.
  move=> i Hiy.
  rewrite mxE /= (_ : nat_of_ord i == nat_of_ord y = false) /=; last first.
    by move/negbTE : Hiy.
  by rewrite mulr0.
by rewrite big_const_seq iter_addr0 !addr0 !mxE /= eqxx /= (ltn_ord y) /= 2!mulr1.
Qed.

End AboutPermPid.

(* NB: similar to mulmx_sum_row in matrix.v *)
(* NB: used in hamming_code.v *)
Lemma mulmx_sum_col {R : comRingType} m n (u : 'cV[R]_n) (A : 'M_(m, n)) :
  A *m u = \sum_i u i 0 *: col i A.
Proof.
apply/colP => j; rewrite mxE summxE; apply: eq_bigr => i _.
by rewrite !mxE mulrC.
Qed.

Lemma col_perm_inj n (s : 'S_n) T m : injective (@col_perm T m n s).
Proof.
move=> x y; rewrite /col_perm => /matrixP xy; apply/matrixP => i j.
by move: (xy i (s^-1%g j)); rewrite !mxE permKV.
Qed.

Section AboutRank.
Variable F : fieldType.

Lemma rank_I n : \rank (1%:M : 'M[F]_n) = n.
Proof.
apply/eqP. apply/row_freeP.
exists (1%:M : 'M[F]_n); by rewrite mulmx1.
Qed.

Lemma rank_row_mx n (A : 'M[F]_n) m (B : 'M[F]_(n, m)) :
  \rank A = n -> \rank (row_mx A B) = n.
Proof.
move=> HA.
apply/eqP. apply/row_freeP.
exists (col_mx ((invmx (row_ebase A)) *m (invmx (col_ebase A))) 0).
rewrite mul_row_col mulmx0 addr0 -{1}(mulmx_ebase A) HA pid_mx_1 mulmx1 -!mulmxA.
have -> : row_ebase A *m (invmx (row_ebase A) *m invmx (col_ebase A)) =
  invmx (col_ebase A).
  rewrite !mulmxA mulmxV.
  by rewrite mul1mx.
  by apply: row_ebase_unit.
rewrite mulmxV //.
by apply: col_ebase_unit.
Qed.

Lemma empty_rV (A : ringType) (a : 'rV[A]_O) : a = 0.
Proof. apply/rowP; by case. Qed.

Lemma full_rank_inj m n (A : 'M[F]_(m, n)) : (m <= n)%N -> \rank A = m ->
  forall (a b : 'rV[F]_m),  a *m A = b *m A -> a = b.
Proof.
move=> Hmn Hrank a b Hab.
move: Hrank.
destruct m => //= [_|].
  by rewrite (empty_rV a) (empty_rV b).
destruct n => //=.
unlock.
move Herk : (Gaussian_elimination A) => LUr /= Htmp.
move: (mulmx_ebase A) => Heq.
rewrite -Heq !mulmxA in Hab.
have {}Hab :
  a *m col_ebase A *m pid_mx (\rank A) *m row_ebase A *m (invmx (row_ebase A)) =
  b *m col_ebase A *m pid_mx (\rank A) *m row_ebase A *m (invmx (row_ebase A)).
  by rewrite Hab.
rewrite -!mulmxA mulmxV in Hab; last by exact: row_ebase_unit.
rewrite !Htmp mulmx1 !mulmxA /mxrank /= in Hab.
move: {Heq}(@pid_mx_inj _ _ _ (a *m col_ebase A) (b *m col_ebase A) Hmn Hab) => Heq.
have {}Hab : a *m col_ebase A *m (invmx (col_ebase A)) =
  b *m col_ebase A *m (invmx (col_ebase A)) by rewrite Heq.
rewrite -!mulmxA mulmxV in Hab; last by apply: col_ebase_unit.
by rewrite !mulmx1 in Hab.
Qed.

Lemma mxrank_castmx a a' b b' (M : 'M[F]_(a, b)) (H1 : a = a') (H2 : b = b') :
  \rank (castmx (H1, H2) M) = \rank M.
Proof. by subst a' b'. Qed.

End AboutRank.

Section non_trivial_vspace.

Variables (F : finFieldType) (n : nat) (C : {vspace 'rV[F]_n}).

Definition not_trivial := exists cw, (cw \in C) && (cw != 0).

Lemma not_trivialP : not_trivial <-> C != 0%VS.
Proof.
split; rewrite /not_trivial.
- case => x /andP[xC].
  apply: contra => /eqP C0; move: xC; by rewrite C0 memv0.
- rewrite -vpick0 => C0.
  exists (vpick C); by rewrite C0 andbT memv_pick.
Qed.

End non_trivial_vspace.

Section about_row_vectors_on_prime_fields.

Lemma card_rV_wo_zeros p n : prime p ->
  (\sum_(x : 'rV['F_p]_n | [forall j, x ord0 j != 0%R]) 1)%N = (p.-1 ^ n)%N.
Proof.
move=> primep.
destruct p as [|p'] => //; destruct p' as [|p'] => //.
set p := p'.+2.
transitivity (\sum_(x : {: n.-tuple 'I_p.-1}) 1)%N; last first.
  by rewrite sum1_card card_tuple card_ord.
pose g : 'F_p -> 'I_p.-1 := fun x =>
  inord (cast_ord (@card_Fp _ primep) (enum_rank x : 'I_#|'F_p|)).-1.
pose g' : 'I_p.-1 -> 'F_p := fun x =>
  enum_val (cast_ord (esym (@card_Fp _ primep)) (inord x.+1)).
have Hg' : forall j, g' j != 0.
  move=> j; apply/eqP => /(congr1 enum_rank).
  rewrite enum_valK => /(congr1 val) /=.
  by rewrite enum_rank_ord /= inordK // ltnS.
have gg' : {in [set x in 'F_p | x != 0], cancel g g'}.
  move=> x; rewrite inE => /andP[Hx x_neq0].
  rewrite /g' inordK //=; last first.
    rewrite enum_rank_ord //= prednK ?lt0n //.
    move: (ltn_ord x) => /=; rewrite ltnS => /leq_trans; apply.
    by rewrite -(ltn_add2r 1) 2!addn1 Zp_cast // ?pdiv_leq // pdiv_id.
  rewrite (enum_rank_ord x) //= prednK ?lt0n //= enum_val_ord /=.
  apply val_inj => /=; rewrite inordK //.
  move: (ltn_ord x) => /leq_trans; apply; by rewrite Zp_cast ?pdiv_id.
have g'g : cancel g' g.
  move=> x; rewrite /g /g' /= enum_valK; apply val_inj => /=.
  by rewrite (@inordK _ x.+1) /= ?inordK // ltnS.
set f : 'rV['F_p]_n -> n.-tuple 'I_p.-1 := fun x => tuple_of_row (map_mx g x).
set f' : n.-tuple 'I_p.-1 -> 'rV['F_p]_n := fun x => map_mx g' (row_of_tuple x).
rewrite (reindex_onto f' f); last first.
  rewrite /= => x /forallP /= H; apply/rowP => j.
  by rewrite /f' /f mxE tuple_of_rowK mxE gg' // !inE /= H.
apply eq_bigl => x; apply/andP; split.
  by apply/forallP => j; rewrite !mxE Hg'.
apply/eqP/eq_from_tnth => i; by rewrite tnth_mktuple !mxE g'g.
Qed.

End about_row_vectors_on_prime_fields.

Lemma sum_sqr (F : fieldType) (_ : 2%N \in [char F]) k (f : 'I_k -> F) :
  (\sum_(i < k) f i) ^+ 2 = \sum_(i < k) (f i) ^+ 2.
Proof.
elim/big_ind2 : _ => [|x1 x2 y1 y2 <- <-|//] /=; first by rewrite expr0n.
by rewrite sqrrD mulr2n addrr_char2 // addr0.
Qed.

From mathcomp Require Import finfield.

Section GFqm.

Variables (q m' : nat).
Let m := m'.+1.
Hypothesis primeq : prime q.

Definition GF : finFieldType := sval (@PrimePowerField q m primeq isT).

Lemma char_GFqm : q \in [char GF].
Proof. exact (proj1 (proj2_sig (@PrimePowerField q m primeq isT))). Qed.

Lemma card_GFqm : #| GF | = (q ^ m)%N.
Proof. rewrite /GF; by case: (@PrimePowerField q m primeq isT). Qed.

End GFqm.

Section GF2m.

Variable m : nat.

Definition GF2 : finFieldType := @GF 2 m.-1 isT.

Definition GF2_of_F2 : 'F_2 -> GF2 := [eta \0 with 0 |-> 0, 1 |-> 1].

Definition additive_GF2_of_F2 : additive GF2_of_F2.
Proof.
move=> x y; apply/esym; rewrite /GF2_of_F2 /=; case: ifPn=> [/eqP ->|].
- rewrite !add0r; case: ifPn => [/eqP -> /=|]; first by rewrite oppr0.
  case: ifPn => [/eqP -> _ /=|].
  + by rewrite oppr_char2 // char_GFqm.
  + by rewrite -F2_eq0 => /eqP ->.
- rewrite -F2_eq1 => /eqP -> /=.
  case: ifPn => [/eqP -> /=|]; first by rewrite subr0.
  rewrite -F2_eq1 => /eqP -> /=; by rewrite subrr.
Qed.

Definition multiplicative_GF2_of_F2 : multiplicative GF2_of_F2.
Proof.
split => // x y; rewrite /GF2_of_F2 /=; apply/esym.
case: ifPn => [/eqP -> /=|]; first by rewrite mul0r.
rewrite -F2_eq1 => /eqP -> /=; by rewrite !mul1r.
Qed.

Lemma GF2_of_F2_eq0 x : (GF2_of_F2 x == 0) = (x == 0).
Proof.
apply/idP/idP => [|/eqP -> //].
rewrite /GF2_of_F2 /=; case: ifPn => //; rewrite -F2_eq1 => ->.
by rewrite oner_eq0.
Qed.

End GF2m.

Arguments GF2_of_F2 [_] _.

HB.instance Definition _ m := GRing.isAdditive.Build _ _ (@GF2_of_F2 m) (additive_GF2_of_F2 m).
HB.instance Definition _ m := GRing.isMultiplicative.Build _ _ _ (multiplicative_GF2_of_F2 m).

Definition F2_to_GF2 (m : nat) n (y : 'rV['F_2]_n) := map_mx (@GF2_of_F2 m) y.

Lemma supp_F2_to_GF2 n m (e : 'rV['F_2]_n) : supp (F2_to_GF2 m e) = supp e.
Proof.
apply/setP => i; rewrite !inE !mxE; apply/idP/idP; apply: contra.
  by move/eqP => ->; rewrite /= rmorph0.
by rewrite GF2_of_F2_eq0.
Qed.

Section Det_mlinear.
Context {R : comRingType}.

Let det_mlinear_rec n (f : 'I_n.+1 -> 'I_n.+1 -> R) (g : 'I_n.+1 -> R) k :
  (k <= n.+1)%N ->
  \det (\matrix_(j, i) (f i j * g j)) =
  (\prod_(l < k) g (inord l)) *
    \det (\matrix_(j, i) (f i j * if (j >= k)%N then g j else 1)).
Proof.
elim: k => [_|k IH]; first by rewrite big_ord0 mul1r.
rewrite ltnS => kn.
rewrite IH; last by rewrite ltnW.
rewrite big_ord_recr /= -mulrA; congr (_ * _).
rewrite (@determinant_multilinear _ _ _
           (\matrix_(j, i) (f i j * (if (k < j)%N then g j else 1)))
           (\matrix_(j, i) (f i j * (if (k <= j)%N then g j else 1)))
           (inord k) (g (inord k)) 0); last 3 first.
- rewrite scale0r addr0.
  apply/rowP => j.
  rewrite !mxE mulrCA; congr (_ * _).
  by rewrite inordK // leqnn ltnn mulr1.
- apply/matrixP => i j; rewrite !mxE.
  case: ifPn => [H1|].
    by case: ifPn => //; rewrite (ltnW H1).
  case: ifPn => //; rewrite -ltnNge ltnS => H1 H2.
  rewrite mulr1.
  have /eqP abs : k = lift (inord k) i by apply/eqP; rewrite eqn_leq H1 H2.
  exfalso.
  move/eqP : abs; apply/eqP.
  apply: contra (@neq_lift _ (inord k) i) => /eqP {1}->.
  by apply/eqP/val_inj; rewrite inord_val.
- by apply/matrixP => i j; rewrite !mxE.
- by rewrite mul0r addr0 -det_tr.
Qed.

Lemma det_mlinear (n: nat) (f : 'I_n -> 'I_n -> R) (g : 'I_n -> R) :
  \det (\matrix_(i, j) (f i j * g j)) =
    \prod_(i < n) g i * \det (\matrix_(i, j) (f i j)).
Proof.
case: n => [|n] in f g *; first by rewrite big_ord0 mul1r !det_mx00.
rewrite -det_tr (_ : _^T = \matrix_(j, i) (f i j * g j)); last first.
  by apply/matrixP => i j; rewrite !mxE.
rewrite (@det_mlinear_rec _ _ _ n.+1) //; congr (_ * _).
  by under eq_bigr do rewrite inord_val.
rewrite -det_tr; congr (\det _).
by apply/matrixP => i j; rewrite !mxE ltnNge -ltnS ltn_ord /= mulr1.
Qed.

End Det_mlinear.

Section regular_algebra.

Lemma mulr_regl [R : ringType] (a : R) (x : R^o) : a * x = a *: x.
Proof. by []. Qed.

Lemma mulr_regr [R : comRingType] (a : R) (x : R^o) : x * a = a *: x.
Proof. by rewrite mulrC. Qed.

End regular_algebra.

Section ssrnum_ext.
Import ssrnum Num.Theory.

Lemma sqrBC (R : realDomainType) (x y : R) : (x - y) ^+ 2 = (y - x) ^+ 2.
Proof.
have:= num_real (x - y) => /real_normK <-.
by rewrite distrC real_normK // num_real.
Qed.

Lemma ler_abs_sqr (T : realDomainType) (x y : T) : (`|x| <= `|y|) = (x ^+ 2 <= y ^+ 2).
Proof. by rewrite -[LHS]ler_sqr ?nnegrE// ?real_normK// num_real. Qed.
End ssrnum_ext.

Section ssrint_ext.
Import ssrnum Num.Theory ssrint.

Lemma sum_exprz {R : numFieldType} (n : nat) x : x != 1 ->
  \sum_(i < n) x ^ i.+1 = x * (1 - (x ^ n)) / (1 - x) :> R.
Proof.
move=> neq_x_1.
rewrite -opprB.
rewrite subrX1.
rewrite -opprB mulNr opprK.
rewrite mulrCA mulrC !mulrA mulVf; last first.
  by rewrite subr_eq0 eq_sym.
rewrite mul1r big_distrr//=.
by apply: eq_bigr => i _; rewrite exprSz.
Qed.

End ssrint_ext.
