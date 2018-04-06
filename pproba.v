(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg zmodp matrix.
Require Import Reals Fourier.
Require Import Rssr Reals_ext ssr_ext ssralg_ext bigop_ext Rbigop proba channel.

(** * Posterior Probability *)

(** OUTLINE:
- Section receivable_def.
- Section receivable_uniform.
- Module PosteriorProbability.
- Section post_proba_prop.
- Module MarginalPosteriorProbabiliy.
- Section marginal_post_proba_prop.
*)

Reserved Notation "P '`^^' W ',' H '(' x '|' y ')'" (at level 10,
  W, y, x, H at next level).
Reserved Notation "P ''_' n0 '`^^' W ',' H '(' a '|' y ')'" (at level 10,
  n0, W, H, a, y at next level).

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope channel_scope.
Local Open Scope proba_scope.

Section receivable_def.

Variables (A B : finType) (W : `Ch_1(A, B)).
Variables (n : nat) (P : {dist 'rV[A]_n}).

Definition receivable y := [exists x, (P x != 0) && (W ``(y | x) != 0)].

Lemma receivableE y :
  receivable y = (\rsum_(x in 'rV[A]_n) P x * W ``(y | x) != 0).
Proof.
apply/idP/idP => [|H].
- case/existsP => x /andP [] H1.
  apply: contra => /eqP/prsumr_eq0P => H2.
  apply/eqP.
  apply Rmult_eq_reg_l with (P x); last exact/eqP.
  rewrite mulR0 H2 // => /= x' _.
  apply mulR_ge0; by [apply dist_nonneg | apply DMC_nonneg].
- have : \rsum_(x in setT) P x * W ``(y | x) != 0.
    apply: contra H => /eqP H; apply/eqP.
    rewrite -[RHS]H; apply/eq_bigl => /= x; by rewrite !inE.
  case/big_neq0/existsP => /= x /andP[_ H1].
  rewrite /receivable; apply/existsP; exists x; rewrite -negb_or.
  apply: contra H1 => /orP[|] /eqP ->; by rewrite ?mul0R ?mulR0.
Qed.

End receivable_def.

Section receivable_uniform.

Variables (A B : finType) (W : `Ch_1(A, B)).
Variables (n : nat) (x : 'rV[A]_n).

Variable C : {set 'rV[A]_n}.
Hypothesis HC : (0 < #| C |)%nat.

Variable y : 'rV[B]_n.

Lemma not_receivable_uniformE :
  ~~ receivable W (`U HC) y = (\rsum_(t0 in C) W ``(y | t0) == 0)%R.
Proof.
apply/idP/idP => [|/eqP].
- rewrite negb_exists => /forallP H.
  rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_Rplus ?mulR0 // => i iC.
  move: (H i).
  rewrite negb_and !negbK => /orP[|/eqP //].
  by rewrite -(negbK (_ == _)) UniformSupport.neq0 iC.
- have : forall i : 'rV_n, i \in C -> (0 <= W ``(y | i))%R.
    move=> ? ?; by apply DMC_nonneg.
  move/prsumr_eq0P => H /H {H} H.
  rewrite /receivable; apply/negP.
  case/existsP => z /andP[].
  rewrite UniformSupport.neq0 => /H ->; by rewrite eqxx.
Qed.

End receivable_uniform.

Module PosteriorProbability.
Section PosteriorProbability_sect.

Variables (A B : finType) (W : `Ch_1(A, B)) (n : nat).
Variable P : {dist 'rV[A]_n}.
Variable y : 'rV[B]_n.
Definition den := \rsum_(x in 'rV_n) P x * W ``(y | x).
Hypothesis receivable_y : receivable W P y.

Definition f x := P x * W ``(y | x) / den.

Lemma den_nonneg : 0 <= den.
Proof.
apply rsumr_ge0 => x _; apply mulR_ge0; [exact/dist_nonneg | exact/DMC_nonneg].
Qed.

Lemma f0 x : 0 <= f x.
Proof.
apply Rle_mult_inv_pos; first by apply mulR_ge0; exact/dist_nonneg.
apply/RltP; rewrite lt0R {1}/den -receivableE receivable_y; exact/RleP/den_nonneg.
Qed.

Lemma f1 : \rsum_(x in 'rV_n) f x = 1.
Proof.
rewrite /f /Rdiv -big_distrl /= mulRC.
apply/Rinv_l/eqP; by rewrite -receivableE.
Qed.

Definition d : {dist 'rV[A]_n} := locked (makeDist f0 f1).

Lemma dE x : d x = P x * W ``(y | x) / den.
Proof. rewrite /d; by unlock. Qed.

End PosteriorProbability_sect.
End PosteriorProbability.

Notation "P '`^^' W ',' H '(' x '|' y ')'" :=
  (@PosteriorProbability.d _ _ W _ P y H x) : proba_scope.

Section post_proba_prop.

Variables (A B : finType) (W : `Ch_1(A, B)).
Variables (n : nat) (C : {set 'rV[A]_n}).
Hypothesis HC : (0 < #| C |)%nat.

Variable y : 'rV[B]_n.
Hypothesis Hy : receivable W (`U HC) y.

Definition Kppu := (/ \rsum_(c in C) W ``(y | c))%R.

Lemma post_proba_uniform0 (x : 'rV[A]_n) : x \notin C ->
  (`U HC) `^^ W, Hy (x | y) = 0%R.
Proof.
move=> xC.
by rewrite PosteriorProbability.dE UniformSupport.E0 // /Rdiv !mul0R.
Qed.

Lemma post_proba_uniformE (x : 'rV[A]_n) : x \in C ->
  (`U HC) `^^ W, Hy (x | y) = (Kppu * W ``(y | x))%R.
Proof.
move=> Ht.
rewrite PosteriorProbability.dE UniformSupport.E // mulRC {1}/Rdiv -mulRA [in RHS]mulRC; congr (_ * _).
rewrite /PosteriorProbability.den UniformSupport.restrict.
have Htmp : INR #|C| != 0 by rewrite INR_eq0 -lt0n.
rewrite div1R -Rinv_mult_distr //.
  rewrite /Kppu; congr Rinv; rewrite big_distrr /=; apply eq_bigr => i iC.
  by rewrite UniformSupport.E // div1R mulRA mulRV // mul1R.
exact/eqP.
rewrite (eq_bigr (fun t => 1 / INR #|C| * W ``(y | t))); last first.
  move=> i iC; by rewrite UniformSupport.E.
rewrite -big_distrr /=; apply Rmult_integral_contrapositive; split.
  rewrite div1R => /invR_eq0; exact/eqP.
by apply/eqP; rewrite -not_receivable_uniformE Hy.
Qed.

Lemma post_proba_uniform_kernel (x : 'rV[A]_n) :
  (`U HC) `^^ W, Hy (x | y) = (Kppu * INR (x \in C) * W ``(y | x))%R.
Proof.
case/boolP : (x \in C) => Ht.
- by rewrite post_proba_uniformE // ?inE // mulR1.
- by rewrite post_proba_uniform0 ?inE // mulR0 mul0R.
Qed.

End post_proba_prop.

Local Open Scope vec_ext_scope.

Module MarginalPosteriorProbabiliy.
Section marginal_post_proba.

Variable n : nat.
Variables (A : finType) (P : {dist 'rV[A]_n}).
Variables (B : finType) (W : `Ch_1(A, B)).
Variable y : 'rV[B]_n.
Hypothesis H : receivable W P y.

Let f' := fun x : 'rV_n => P `^^ W, H (x | y).

Definition Kmpp : R := 1 / \rsum_(t in 'rV_n) f' t.

Lemma f'_neq0 : \rsum_(t in 'rV_n) f' t <> 0.
Proof.
evar (x : 'rV[A]_n -> R).
rewrite (eq_bigr x); last first.
  move=> i _; rewrite /f' PosteriorProbability.dE /Rdiv /x; reflexivity.
rewrite -big_distrl { x} /=.
apply Rmult_integral_contrapositive_currified; last first.
  apply/Rinv_neq_0_compat/eqP; by rewrite -receivableE.
apply/eqP; by rewrite -receivableE.
Qed.

Definition f (i : 'I_n) a := Kmpp * \rsum_(t in 'rV_n | t ``_ i == a) f' t.

Lemma f0 i a : 0 <= f i a.
Proof.
apply mulR_ge0.
- rewrite /Kmpp.
  apply Rle_mult_inv_pos; [fourier|].
  apply/RltP; rewrite lt0R; apply/andP; split; [apply/eqP |apply/RleP]; last first.
    apply rsumr_ge0 => /= ? _; exact: dist_nonneg.
  exact/f'_neq0.
- apply rsumr_ge0 => /= ? _; exact: dist_nonneg.
Qed.

Lemma f1 i : \rsum_(a in A) f i a = 1.
Proof.
rewrite /f /= -big_distrr /= /Kmpp div1R.
set tmp1 := \rsum_( _ | _ ) _.
set tmp2 := \rsum_( _ | _ ) _.
suff : tmp1 = tmp2.
  move=> tp12; rewrite -tp12 mulVR //; exact/eqP/f'_neq0.
by rewrite {}/tmp1 {}/tmp2 (partition_big (fun x : 'rV_n => x ``_ i) xpredT).
Qed.

Definition d i : dist A := makeDist (f0 i) (f1 i).

End marginal_post_proba.
End MarginalPosteriorProbabiliy.

Notation "P ''_' n0 '`^^' W ',' H '(' a '|' y ')'" :=
  (@MarginalPosteriorProbabiliy.d _ _ P _ W y H n0 a) : proba_scope.

Section marginal_post_proba_prop.

Variables (A B : finType) (W : `Ch_1(A, B)).
Variables (n : nat) (C : {set 'rV[A]_n}).
Hypothesis HC : (0 < #| C |)%nat.

Variable y : 'rV[B]_n.
Hypothesis Hy : receivable W (`U HC) y.

Import MarginalPosteriorProbabiliy.

Lemma marginal_post_probaE b n0 :
  (`U HC) '_ n0 `^^ W, Hy (b | y) =
  (Kmpp Hy * (\rsum_(t in 'rV_n | t ``_ n0 == b) (`U HC) `^^ W, Hy (t | y)))%R.
Proof. by []. Qed.

End marginal_post_proba_prop.
