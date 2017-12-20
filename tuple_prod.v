(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import ssr_ext ssralg_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * (A^n x B^n) <-> (A x B)^n *)

(** Technical lemmas to switch between products of tuples (A^n x B^n) and
   tuples of products (A x B)^n: *)

Local Open Scope ring_scope.
Local Open Scope vec_ext_scope.

Section prod_tuple_def.

Variables A B : finType.

(* TODO: rename *)
Definition prod_tuple n (x : 'rV[A]_n * 'rV[B]_n) : 'rV[A * B]_n :=
  \row_(k < n) (x.1 ``_ k, x.2 ``_ k).

End prod_tuple_def.

Section tuple_of_prods_to_prod_of_tuples.

Variable A B : finType.

Definition tuple_prod n (x : 'rV[A * B]_n) : {: 'rV[A]_n * 'rV[B]_n} :=
  (\row_(k < n) (x ``_ k).1, \row_(k < n) (x ``_ k).2).

Lemma prod_tupleK n (x : 'rV[A]_n * 'rV[B]_n) : tuple_prod (prod_tuple x) = x.
Proof.
case: x => x1 x2.
rewrite /tuple_prod /prod_tuple /=.
congr (_ , _); apply/matrixP => a b; rewrite {a}(ord1 a); by rewrite !mxE /=.
Qed.

Lemma tuple_prodK n (x : 'rV[A * B]_n) : prod_tuple (tuple_prod x) = x.
Proof.
rewrite /tuple_prod /= /prod_tuple /=.
apply/matrixP => a b; rewrite {a}(ord1 a); rewrite !mxE.
by case: (x ``_ b).
Qed.

End tuple_of_prods_to_prod_of_tuples.

Section prod_of_tuples_to_tuple_of_prods.

Variables A B : finType.

(*
Lemma unzip1_prod_tuple n : forall (x : 'rV[A]_n * 'rV[B]_n),
  unzip1 (prod_tuple x) = x.1.
Proof. case => /= a b. by rewrite unzip1_zip // !size_tuple. Qed.

Lemma unzip2_prod_tuple n : forall (x : {: n.-tuple A * n.-tuple B }),
   unzip2 (prod_tuple x) = x.2.
Proof. case => /= a b; by rewrite unzip2_zip // !size_tuple. Qed.*)

Lemma snd_tnth_prod_tuple n (x : {: 'rV[A]_n * 'rV[B]_n}) i :
  x.2 ``_ i = ((prod_tuple x) ``_ i).2.
Proof.
by rewrite /prod_tuple /= mxE /=.
Qed.

Lemma fst_tnth_prod_tuple n (x : {: 'rV[A]_n * 'rV[B]_n}) i :
  x.1 ``_ i = ((prod_tuple x) ``_ i).1.
Proof.
by rewrite /prod_tuple /= mxE /=.
Qed.

(*
Lemma behead_prod_tuple n : forall (x : {: n.-tuple A * n.-tuple B }),
  prod_tuple ([tuple of behead x.1], [tuple of behead x.2]) =
  [tuple of behead (prod_tuple x)].
Proof.
case=> x1 x2 /=.
apply val_inj => /=.
destruct x1 as [a1 Ha1].
destruct x2 as [a2 Ha2] => /=.
move/eqP in Ha1.
move/eqP in Ha2.
destruct n as [|n].
  by rewrite (size0nil Ha1) (size0nil Ha2).
by rewrite (@behead_zip _ _ n).
Qed.

Lemma prod_tuple_eta n : forall (x : {: n.+1.-tuple A * n.+1.-tuple B }),
  prod_tuple x = [tuple of thead (prod_tuple x) :: behead (prod_tuple x)].
Proof. case=> x1 x2; rewrite (tuple_eta x1) (tuple_eta x2) /=; by apply val_inj. Qed.

Lemma snd_thead_prod_tuple n : forall (x : {: n.+1.-tuple A * n.+1.-tuple B}),
  thead x.2 = (thead (prod_tuple x)).2.
Proof. case=> x1 x2. by rewrite [snd _]/= (tuple_eta x2) theadE (tuple_eta x1). Qed.

Lemma fst_thead_prod_tuple n : forall (x : {: n.+1.-tuple A * n.+1.-tuple B }),
  thead x.1 = (thead (prod_tuple x)).1.
Proof. case=> x1 x2. by rewrite [fst _]/= (tuple_eta x1) theadE (tuple_eta x2). Qed.
*)

End prod_of_tuples_to_tuple_of_prods.
