(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg perm zmodp matrix vector.
Require Import Reals.
Require Import ssralg_ext ssrR Reals_ext f2 proba channel tanner linearcode.
Require Import Rbigop pproba.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.

(** * Checksum Operator *)

(** OUTLINE:
- Section checksubsum_parity.
- Section post_proba_checksubsum.
*)

Import GRing.Theory.

Definition checksubsum n (V : {set 'I_n}) (x : 'rV['F_2]_n) : bool :=
  (\sum_(n0 in V) x ``_ n0) == 0.

Notation "'\delta'" := (checksubsum).

Lemma checksubsum_set1 n i (x : 'rV['F_2]_n) :
  \delta [set i] x = ~~ (bool_of_F2 x ``_ i).
Proof.
rewrite /checksubsum (big_pred1 i).
  by rewrite /bool_of_F2 negbK.
move=> /= n2; by rewrite in_set1.
Qed.

Lemma checksubsum_set2 n n1 n2 (n1n2 : n1 != n2) (d : 'rV_n) :
  \delta [set n1; n2] d = (d ``_ n1 == d ``_ n2).
Proof.
rewrite /checksubsum.
rewrite big_setU1 /=; last by rewrite inE.
rewrite big_set1.
by rewrite -{1}(oppr_char2 (@char_Fp 2 erefl) (d ``_ n2)) subr_eq0.
Qed.

Section checksubsum_parity.

Variables (n m : nat) (H : 'M['F_2]_(m, n)) (A : {set 'I_n}).

Lemma checksubsum_D1 i x : i \in A ->
  \delta A x = (F2_of_bool (\delta (A :\ i) x) != x ``_ i).
Proof.
move=> iA; rewrite /checksubsum (bigD1 i) //=.
rewrite (_ : \sum_(i0 in A | i0 != i) x ``_ i0 = \sum_(n0 in A :\ i) x ``_ n0); last first.
  apply eq_bigl => j; by rewrite in_setD1 andbC.
rewrite addr_eq0 eq_sym oppr_char2 //.
case/F2P : (x ``_ i) => //=.
  apply/idP/idP; [by move=> ->|].
  by case/boolP : (\sum_(n0 in _) _ == _).
apply/idP/idP; [by move/eqP => -> |].
rewrite -F2_eq0; by case: F2P.
Qed.

End checksubsum_parity.

Local Open Scope channel_scope.

Section post_proba_checksubsum.

Variables (B : finType) (W : `Ch_1('F_2, B)).
Variables (m n : nat) (H : 'M['F_2]_(m, n)).
Local Notation "''V'" := (Vnext H).

Lemma kernel_checksubsum1 (x : 'rV['F_2]_n) : x \in kernel H ->
  1%R = INR (\prod_m0 \delta ('V m0) x).
Proof.
move=> x_in_C.
rewrite {1}(_ : 1%R = INR (\prod_(m0 < m) 1)); [congr INR |
  by rewrite big_const iter_muln_1 exp1n].
apply eq_bigr => m0 _.
rewrite /C mem_kernel_syndrome0 /syndrome in x_in_C.
move/eqP in x_in_C.
have {x_in_C}x_in_C : forall m0, \sum_i (H m0 i) * (x ``_ i) = 0.
  move=> m1.
  move/rowP : x_in_C => /(_ m1).
  rewrite !mxE.
  move=> t_in_C; rewrite -[in X in _ = X]t_in_C.
  apply eq_bigr => // i _; congr (_ * _).
  by rewrite /row_of_tuple !mxE.
have {x_in_C}x_in_C : forall m0, \sum_(i in 'V m0) ((H m0 i) * x ``_ i) = 0.
  move=> m1.
  rewrite -[in X in _ = X](x_in_C m1); symmetry.
  rewrite (bigID [pred i | i \in 'V m1]) /=.
  set tmp := {2}(\sum_(i in 'V m1) _).
  rewrite -[in X in _ = X](addr0 tmp); congr (_ + _).
  rewrite [in X in _ = X](_ : 0 = \sum_(i | i \notin 'V m1) 0); last first.
    by rewrite big_const /= iter_addr0.
  apply eq_big => // n0.
  rewrite VnextE tanner_relE -F2_eq0 => /eqP ->; by rewrite mul0r.
have {x_in_C}x_in_C : forall m0, \sum_(i in 'V m0) x ``_ i = 0.
  move=> m1.
  rewrite -[in X in _ = X](x_in_C m1).
  apply eq_bigr => // i.
  rewrite VnextE tanner_relE => /eqP ->; by rewrite mul1r.
have {x_in_C}x_in_C : forall m0, \sum_(i in 'V m0) x ``_ i = 0.
  move=> m1.
  by rewrite -{2}(x_in_C m1).
by rewrite /checksubsum (x_in_C m0) eqxx.
Qed.

Lemma kernel_checksubsum0 (x : 'rV['F_2]_n) : x \notin kernel H ->
  INR (\prod_m0 checksubsum ('V m0) x) = 0%R.
Proof.
move=> x_notin_C.
rewrite /C mem_kernel_syndrome0 /syndrome in x_notin_C.
have {x_notin_C}x_notin_C : [exists m0, \sum_i (H m0 i) * (x ``_ i) != 0].
  rewrite -negb_forall; apply: contra x_notin_C => /forallP x_notin_C.
  apply/eqP/rowP => a; rewrite !mxE /=.
  move: (x_notin_C a) => /eqP Htmp.
  rewrite -[in X in _ = X]Htmp.
  apply eq_bigr => // i _; congr (_ * _).
  by rewrite /row_of_tuple !mxE.
have {x_notin_C}x_notin_C : [exists m0, \sum_(i in 'V m0) ((H m0 i) * x ``_ i) != 0].
  case/existsP : x_notin_C => m0 Hm0.
  apply/existsP; exists m0.
  apply: contra Hm0 => /eqP Hm0.
  apply/eqP.
  rewrite (bigID [pred i | i \in 'V m0]) /= Hm0 add0r.
  rewrite [in X in _ = X](_ : 0 = \sum_(i | i \notin 'V m0) 0); last first.
    by rewrite big_const /= iter_addr0.
  apply eq_big => n0 //.
  rewrite VnextE tanner_relE -F2_eq0 => /eqP ->; by rewrite mul0r.
have {x_notin_C}x_notin_C : [exists m0, \sum_(i in 'V m0) x ``_ i != 0].
  case/existsP : x_notin_C => /= i x_notin_C.
  apply/existsP; exists i; apply: contra x_notin_C => /eqP Htmp.
  apply/eqP.
  rewrite -[in X in _ = X]Htmp.
  apply eq_bigr => n0.
  rewrite VnextE tanner_relE => /eqP ->; by rewrite mul1r.
have {x_notin_C}x_notin_C : [exists m0, \sum_(i in 'V m0) x ``_ i != 0].
  case/existsP : x_notin_C => /= i x_notin_C.
  apply/existsP; exists i; apply: contra x_notin_C => /eqP Htmp.
  by apply/eqP.
case/existsP : x_notin_C => m0 Hm0.
rewrite /checksubsum (bigID (pred1 m0)) /=.
set lhs := (\prod_(i < m | i == m0) _)%nat.
suff -> : lhs = O. by rewrite mul0n.
rewrite /lhs big_pred1_eq.
by move/negbTE : Hm0 => ->.
Qed.

Lemma kernel_checksubsum (x : 'rV['F_2]_n) :
  x \in kernel H = \big[andb/true]_m0 checksubsum ('V m0) x.
Proof.
apply/idP/idP; last first.
  apply: contraTT => /kernel_checksubsum0.
  rewrite -(@big_morph _ _ nat_of_bool true muln true andb) //.
    rewrite -eqb0 /= (_ : 0%R = INR 0) //; by move/INR_eq/eqP.
  move=> ? ? /=; by rewrite mulnb.
move/kernel_checksubsum1.
rewrite -(@big_morph _ _ nat_of_bool true muln true andb) //; last first.
  move=> ? ? /=; by rewrite mulnb.
rewrite (_ : 1%R = INR true) // => /INR_eq/esym.
by case: (\big[andb/true]_(_ < _) _).
Qed.

Local Open Scope R_scope.

Lemma checksubsum_in_kernel (x : 'rV['F_2]_n) :
  \rprod_(i < m) INR (\delta ('V i) x) = INR (x \in kernel H).
Proof.
rewrite kernel_checksubsum.
transitivity (INR (\prod_m1 (nat_of_bool (\delta ('V m1) x)))).
  by rewrite (big_morph _ mult_INR erefl).
congr (INR _).
erewrite (@big_morph _ _ nat_of_bool true) => //.
move=> ? ? /=; by rewrite mulnb.
Qed.

Local Close Scope R_scope.

Let C := kernel H.
Hypothesis HC : 0 < #| [set cw in C] |.

Variable y : 'rV[B]_n.
Local Open Scope proba_scope.
Hypothesis Hy : receivable W (`U HC) y.

Lemma post_proba_uniform_checksubsum (x : 'rV['F_2]_n) :
  (`U HC) `^^ W, Hy (x | y) =
    (Kppu W [set cw in C] y * INR (\prod_m0 (\delta ('V m0) x)) * W ``(y | x))%R.
Proof.
rewrite post_proba_uniform_kernel; congr (_ * _ * _)%R.
rewrite (big_morph _ mult_INR erefl) checksubsum_in_kernel.
by rewrite inE mem_kernel_syndrome0.
Qed.

End post_proba_checksubsum.
