(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div choice fintype tuple finfun bigop prime ssralg.
From mathcomp Require Import finset fingroup perm finalg zmodp matrix mxalgebra.
From mathcomp Require Import mxrepresentation vector.
Require Import ssr_ext f2.

(** * Additional lemmas about algebraic datatypes *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Notation "x '``_' i" := (x ord0 i) (at level 9) : vec_ext_scope.
Reserved Notation "v `[ i := x ]" (at level 20).
Reserved Notation "t # V" (at level 55, V at next level).

Import GRing.Theory.
Local Open Scope ring_scope.

Lemma sum_char2 (F : fieldType) (_ : 2 \in [char F]) k (f : 'I_k -> F) :
  (\sum_(i < k) (f i)) ^+ 2 = \sum_(i < k) (f i) ^+ 2.
Proof.
elim/big_ind2 : _ => [|x1 x2 y1 y2 <- <-|//] /=; first by rewrite expr0n.
by rewrite sqrrD mulr2n addrr_char2 // addr0.
Qed.

Section AboutRingType.

Variable R : ringType.

Lemma iter_addr0 : forall n x, iter n (+%R (0 : R)) x = x.
Proof. elim=> //= n IH x. by rewrite IH add0r. Qed.

Lemma iter_addr0_cV r : forall n (x : 'cV[R]_r), iter n (+%R 0) x = x.
Proof. elim=> //= n IH x; by rewrite IH add0r. Qed.

End AboutRingType.

Local Open Scope vec_ext_scope.

(** * (A^n x B^n) <-> (A x B)^n *)

(** Technical lemmas to switch between products of vectors (A^n x B^n) and
   vectors of products (A x B)^n: *)

Section prod_rV.

Variables A B : finType.

Definition prod_rV n (x : 'rV[A]_n * 'rV[B]_n) : 'rV[A * B]_n :=
  \row_(k < n) (x.1 ``_ k, x.2 ``_ k).

Definition rV_prod n (x : 'rV[A * B]_n) : {: 'rV[A]_n * 'rV[B]_n} :=
  (\row_(k < n) (x ``_ k).1, \row_(k < n) (x ``_ k).2).

Lemma prod_rVK n (x : 'rV[A]_n * 'rV[B]_n) : rV_prod (prod_rV x) = x.
Proof.
case: x => x1 x2.
congr (_ , _); apply/matrixP => a b; rewrite {a}(ord1 a); by rewrite !mxE /=.
Qed.

Lemma rV_prodK n (x : 'rV[A * B]_n) : prod_rV (rV_prod x) = x.
Proof.
apply/matrixP => a b; rewrite {a}(ord1 a); rewrite !mxE; by case: (x ``_ b).
Qed.

Lemma fst_tnth_prod_rV n (x : {: 'rV[A]_n * 'rV[B]_n}) i :
  x.1 ``_ i = ((prod_rV x) ``_ i).1.
Proof. by rewrite mxE. Qed.

Lemma snd_tnth_prod_rV n (x : {: 'rV[A]_n * 'rV[B]_n}) i :
  x.2 ``_ i = ((prod_rV x) ``_ i).2.
Proof. by rewrite mxE. Qed.

End prod_rV.

Section support_set.

Variables (R : ringType) (n : nat) (e : 'rV[R]_n).

Definition supp : {set 'I_n} := [set i | e ``_ i != 0].

Lemma insupp i : (i \in supp) = (e ``_ i != 0).
Proof. by rewrite in_set. Qed.

Lemma sum_supp x : \sum_(i < n) e ``_ i * x ^+ i = \sum_(i in supp) e ``_ i * x ^+ i.
Proof.
rewrite (bigID (mem supp)) /= addrC (eq_bigr (fun=> 0)); last first.
  move=> ?; rewrite inE /= negbK => /eqP ->; by rewrite mul0r.
by rewrite big_const /= iter_addr0 add0r.
Qed.

Lemma supp_set0 : (supp == set0) = (e == 0).
Proof.
apply/idP/idP => [/eqP/setP HE |/eqP ]; last first.
  rewrite /supp => ->; by apply/eqP/setP => i; rewrite !inE /= mxE eqxx.
apply/eqP/matrixP => i j; rewrite mxE (ord1 i).
move: (HE j); by rewrite !inE /= => /negbT; rewrite negbK => /eqP.
Qed.

End support_set.

Lemma supp0 n (R : ringType) : supp (0 : 'rV[R]_n) = set0.
Proof. apply/setP => i; by rewrite !inE mxE eqxx. Qed.

Definition row_set B n (n0 : 'I_n) (x : B) (d : 'rV_n) :=
  \row_(i < n) if i == n0 then x else d ``_ i.

Notation "v `[ i := x ]" := (row_set i x v) : vec_ext_scope.

Lemma inj_row_set (A : ringType) n n0 (d : 'rV_n) :
  {in A &, injective ((row_set n0)^~ d)}.
Proof. move=> a b _ _ /= /rowP /(_ n0); by rewrite mxE eqxx mxE eqxx. Qed.

Lemma row_set_comm n A (i1 i2 : 'I_n) (x1 x2 : A) d :
  i1 != i2 -> d `[ i2 := x2 ] `[ i1 := x1 ] = (d `[ i1 := x1 ]) `[ i2 := x2 ].
Proof.
move=> Hneq.
apply/rowP => i; rewrite !mxE.
case Hi1: (i == i1); case Hi2: (i == i2) => //=.
by rewrite -(eqP Hi1) (eqP Hi2) eqxx in Hneq.
Qed.

Section sub_vec_sect.

Variables (A : Type) (n : nat).

Definition sub_vec (t : 'rV[A]_n) (S : {set 'I_n}) : 'rV[A]_#| S | :=
  \row_(j < #|S|) (t ``_ (enum_val j)).
(* NB: enum_val j is the jth item of enum S *)

End sub_vec_sect.

Notation "t # V" := (sub_vec t V) : vec_ext_scope.

Section row_mx_ext.

Context {A : Type}.

Definition rbehead {n} (x : 'rV[A]_n.+1) := \row_(i < n) x ``_ (lift ord0 i).

Lemma rbehead_row_mx {n} (x : 'rV_n) (i : A) : rbehead (row_mx (\row_(j < 1) i) x) = x.
Proof.
apply/matrixP => a b; rewrite {a}(ord1 a) !mxE.
case: splitP; first by move=> j; rewrite {j}(ord1 j) lift0.
by move=> n0; rewrite lift0 add1n => -[] /val_inj ->.
Qed.

Lemma row_mx_row_ord0 {n} (x : 'rV_n) (i : A) : (row_mx (\row_(k < 1) i) x) ``_ ord0 = i.
Proof.
rewrite mxE; case: splitP => [|/=] k; first by rewrite {k}(ord1 k) mxE.
by rewrite add1n.
Qed.

Lemma row_mx_rbehead {n} (x : 'rV_(1 + n)) (i : A) (b : 'I_(1 + n)) :
  x ``_ ord0 = i -> (row_mx (\row__ i) (rbehead x)) ``_ b = x ``_ b.
Proof.
move=> xi.
rewrite mxE; case: splitP => [j|k bk].
  rewrite {j}(ord1 j) => Hb; rewrite mxE -xi; congr (_ ``_ _).
  exact/val_inj.
rewrite mxE; congr (_ ``_ _); exact/val_inj.
Qed.

End row_mx_ext.

Lemma col_matrix (R : ringType) m n (A : 'I_m -> 'cV[R]_(n.+1)) (i : 'I_m) :
  col i (\matrix_(a < n.+1, b < m) (A b) a ord0) = A i.
Proof. apply/matrixP => a b; by rewrite !mxE (ord1 b). Qed.

Section AboutPermPid.

Variable R : comRingType.

(* s : 0 -> s0; 1 -> s1, etc.
in column 0, there is a 1 at line s0

         | 0 1 |
[a b ] * | 1 0 |  = [b a]
*)
Lemma vec_perm_mx : forall n (s : 'S_n) (z : 'rV[R]_n),
  z *m perm_mx s = \matrix_(i < 1, j < n) z i ((s^-1)%g j).
Proof.
move=> n s z; apply/matrixP => i j.
rewrite (ord1 i) {i} !mxE (bigID (pred1 ((s^-1)%g j))) /=.
rewrite big_pred1_eq !mxE {2}permE perm_invK eqxx mulr1 (eq_bigr (fun _ => 0)).
- by rewrite big_const_seq iter_addr0 addr0.
- move=> i H.
  rewrite !mxE (_ : (s i == j) = false); first by rewrite mulr0.
  apply/eqP; move/eqP : H => H; contradict H.
  by rewrite -H -permM (mulgV s) perm1.
Qed.

Lemma perm_mx_vec : forall n (s : 'S_n) (z : 'cV[R]_n),
  perm_mx s *m z = \matrix_(i < n, j < 1) z (s i) j.
Proof.
move=> n s z; apply/matrixP => i j.
rewrite (ord1 j) {j} !mxE (bigID (pred1 (s i))) /=.
rewrite big_pred1_eq {1}/perm_mx !mxE eqxx mul1r (eq_bigr (fun _ => 0)).
- by rewrite big_const_seq iter_addr0 addr0.
- move=> j; move/negbTE => H.
  by rewrite !mxE eq_sym H /= mul0r.
Qed.

Lemma pid_mx_inj : forall r n (a b : 'rV[R]_r), r <= n ->
  a *m (@pid_mx _ r n r) = b *m (@pid_mx _ r n r) -> a = b.
Proof.
move=> r n a b Hrn /matrixP Heq.
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
Lemma mulmx_sum_col : forall {R : comRingType} m n (u : 'cV[R]_n) (A : 'M_(m, n)),
  A *m u = \sum_i u i 0 *: col i A.
Proof.
move=> R m n u A; apply/colP=> j; rewrite mxE summxE; apply: eq_bigr => i _.
by rewrite !mxE mulrC.
Qed.

Section AboutRowTuple.

Variables A B : predArgType.

Definition tuple_of_row n (v : 'rV[A]_n) := [tuple v ``_ i | i < n].

Local Open Scope tuple_ext_scope.

Definition row_of_tuple n (t : n.-tuple A) := \row_(i < n) (t \_ i).

Lemma row_of_tupleK n (t : n.-tuple A) : tuple_of_row (row_of_tuple t) = t.
Proof. apply eq_from_tnth => n0; by rewrite tnth_mktuple mxE. Qed.

Lemma tuple_of_row_inj n : injective (@tuple_of_row n).
Proof.
move=> i j ij.
apply/rowP => m0.
move/(congr1 (fun x => x \_ m0)) : ij.
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

Lemma tuple_of_row_row_mx {C : finType} n1 n2 (v1 : 'rV[C]_n1) (B : 'rV[C]_n2) :
  tuple_of_row (row_mx v1 B) = [tuple of tuple_of_row v1 ++ tuple_of_row B].
Proof.
apply eq_from_tnth => n0.
rewrite tnth_mktuple mxE.
case: splitP => [n3 n0n3|n3 n0n1n3].
  rewrite /tnth nth_cat size_tuple (_ : (n0 < n1 = true)%nat); last by rewrite n0n3 ltn_ord.
  transitivity ((tuple_of_row v1) \_ n3); first by rewrite tnth_mktuple.
  rewrite /tnth n0n3; apply set_nth_default; by rewrite size_tuple.
rewrite /tnth nth_cat size_tuple (_ : (n0 < n1 = false)%nat); last first.
  rewrite n0n1n3; apply/negbTE; by rewrite -leqNgt leq_addr.
  transitivity ((tuple_of_row B) \_ n3); first by rewrite tnth_mktuple.
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

Lemma trmx_cV_0 {k} (x : 'cV['F_2]_k) : (x ^T == 0) = (x == 0).
Proof.
case Hlhs : (_ ^T == _).
  symmetry.
  move/eqP in Hlhs.
  by rewrite -(trmxK x) Hlhs trmx0 eqxx.
symmetry; apply/eqP.
move=> abs; subst x.
by rewrite trmx0 eqxx in Hlhs.
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

Lemma empty_rV {A : ringType} (a : 'rV[A]_O) : a = 0.
Proof. apply/matrixP => x []; by rewrite (ord1 x). Qed.

Lemma full_rank_inj m n (A : 'M[F]_(m, n)) : m <= n -> \rank A = m ->
  forall (a b : 'rV[F]_m),  a *m A = b *m A -> a = b.
Proof.
move=> Hmn Hrank a b Hab.
move: Hrank.
rewrite /mxrank.
destruct m => //= [_|].
  by rewrite (empty_rV a) (empty_rV b).
destruct n => //=.
unlock.
move Herk : (Gaussian_elimination A) => LUr /= Htmp.
move: (mulmx_ebase A) => Heq.
rewrite -Heq !mulmxA in Hab.
have {Hab}Hab :
  a *m col_ebase A *m pid_mx (\rank A) *m row_ebase A *m (invmx (row_ebase A)) =
  b *m col_ebase A *m pid_mx (\rank A) *m row_ebase A *m (invmx (row_ebase A)).
  by rewrite Hab.
rewrite -!mulmxA mulmxV in Hab; last by exact: row_ebase_unit.
rewrite mulmx1 !mulmxA /mxrank /= in Hab.
unlock in Hab.
rewrite !Htmp in Hab.
move: {Heq}(@pid_mx_inj _ _ _ (a *m col_ebase A) (b *m col_ebase A) Hmn Hab) => Heq.
have {Hab}Hab : a *m col_ebase A *m (invmx (col_ebase A)) =
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
  (\sum_(x : 'rV['F_p]_n | [forall j, x ord0 j != 0%R]) 1)%N = p.-1 ^ n.
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

From mathcomp Require Import finfield.

Section GFqm.

Variables (q m' : nat).
Let m := m'.+1.
Hypothesis primeq : prime q.

Definition GF : finFieldType := sval (@PrimePowerField q m primeq isT).

Lemma char_GFqm : q \in [char GF].
Proof. exact (proj1 (proj2_sig (@PrimePowerField q m primeq isT))). Qed.

Lemma card_GFqm : #| GF | = q ^ m.
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

Definition rmorphism_GF2_of_F2 : rmorphism GF2_of_F2.
Proof. split; [exact: additive_GF2_of_F2|exact: multiplicative_GF2_of_F2]. Qed.

Lemma GF2_of_F2_eq0 x : (GF2_of_F2 x == 0) = (x == 0).
Proof.
apply/idP/idP => [|/eqP -> //].
rewrite /GF2_of_F2 /=; case: ifPn => //; rewrite -F2_eq1 => ->.
by rewrite oner_eq0.
Qed.

End GF2m.

Arguments GF2_of_F2 [_] _.

Canonical GF2_of_F2_additive m := Additive (additive_GF2_of_F2 m).
Canonical GF2_of_F2_rmorphism m := RMorphism (rmorphism_GF2_of_F2 m).

Definition F2_to_GF2 (m : nat) n (y : 'rV['F_2]_n) := map_mx (@GF2_of_F2 m) y.

Lemma supp_F2_to_GF2 n m (e : 'rV['F_2]_n) : supp (F2_to_GF2 m e) = supp e.
Proof.
apply/setP => i; rewrite !inE !mxE; apply/idP/idP; apply: contra.
  move/eqP => ->; by rewrite rmorph0.
by rewrite GF2_of_F2_eq0.
Qed.
