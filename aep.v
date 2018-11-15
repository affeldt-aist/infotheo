(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import Reals Fourier FunctionalExtensionality.
Require Import ssrR Reals_ext ssr_ext ssralg_ext logb Rbigop proba entropy.

(** * Asymptotic Equipartition Property (AEP) *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.
Local Open Scope vec_ext_scope.

(* properties of the ``- log P'' random variable, NB: to go to proba.v? *)
Section mlog_prop.

Variables (A : finType) (P : dist A).

Lemma E_mlog : `E (--log P) = `H P.
Proof.
rewrite ExE /entropy (big_morph _ morph_Ropp oppR0).
apply eq_bigr=> a _; by rewrite /= mulNR mulRC.
Qed.

Definition aep_sigma2 := (\rsum_(a in A) P a * (log (P a))^2 - (`H P)^2)%R.

Lemma V_mlog : `V (--log P) = aep_sigma2.
Proof.
rewrite /Var E_trans_id_rem E_mlog ExE /aep_sigma2 /= -/(_ ^ 2).
transitivity
  (\rsum_(a in A) ((- log (P a))^2 * P a - 2 * `H P * - log (P a) * P a + `H P ^ 2 * P a))%R.
  apply eq_bigr => a _; by field.
rewrite big_split /= big_split /= -big_distrr /= (pmf1 P) mulR1.
set s := (\rsum_(a in A) - _)%R.
have {s}-> : s = (- (2 * `H P ^ 2))%R.
  rewrite /s -{1}(big_morph _ morph_Ropp oppR0); congr (- _)%R.
  rewrite [X in X = _](_ : _ = \rsum_(a in A) (2 * `H P) * (- (P a * log (P a))))%R; last first.
    apply eq_bigr => a _; by rewrite -!mulRA (mulRC (P a)) mulNR.
  rewrite -big_distrr /= -{1}(big_morph _ morph_Ropp oppR0) -/(entropy P).
  by rewrite mulR1 mulRA.
set s := \rsum_(a in A ) _.
rewrite (_ : \rsum_(a in A) _ = s); last by apply eq_bigr => a _; field.
by field.
Qed.

Lemma aep_sigma2_nonneg : 0 <= aep_sigma2.
Proof. rewrite -V_mlog /Var; apply Ex_nonneg => ?; exact: pow_even_ge0. Qed.

End mlog_prop.

Definition sum_mlog_prod A (P : dist A) n : rvar [finType of 'rV[A]_n] :=
  mkRvar (P `^ n) (fun t => \rsum_(i < n) - log (P t ``_ i))%R.

Lemma inde_rv_sum_mlog_prod A (P : dist A) n :
  (Multivar.to_bivar `p_ (sum_mlog_prod P n.+1)) |= --log P _|_ sum_mlog_prod P n.
Proof.
rewrite /inde_rv /= => x y.
rewrite -/(Multivar.head_of _) -/(Multivar.tail_of _).
rewrite -!TupleDist.head_of -!TupleDist.tail_of.
rewrite -inde_rv_tuple_dist /=.
(* TODO: lemma? *)
rewrite /Pr.
rewrite (reindex (fun x : 'rV[A]_n.+1 => (x ``_ ord0, rbehead x))) //=; last first.
  exists (fun x => let: (a, b) := x in row_mx (\row_(i < 1) a) b).
  - move=> t _; by rewrite row_mx_rbehead.
  - case=> a b; by rewrite rbehead_row_mx row_mx_row_ord0.
apply eq_big.
- move=> t; by rewrite !inE.
- move=> t _; by rewrite Multivar.to_bivarE /= row_mx_rbehead.
Qed.

Lemma sum_mlog_prod_isum_map_mlog A (P : dist A) : forall n,
  sum_mlog_prod P n.+1 \=isum (\row_(i < n.+1) --log P).
Proof.
elim => [|n IH].
- move: (@isum_n_1 A (\row_i --log P)).
  set mlogP := cast_rv _.
  move => HmlogP.
  set mlogprodP := sum_mlog_prod _ _.
  suff -> : mlogprodP = mlogP by [].
  rewrite /mlogprodP /mlogP /sum_mlog_prod /cast_rv /= mxE /=; congr mkRvar.
  apply functional_extensionality => ta; by rewrite big_ord_recl big_ord0 addR0.
- rewrite [X in _ \=isum X](_ : _ =
      row_mx (\row_(i < 1) (--log P)) (\row_(i < n.+1) --log P)); last first.
    apply/rowP => b; rewrite !mxE; case: splitP.
      move=> a; rewrite {a}(ord1 a) => _; by rewrite mxE.
    move=> k _; by rewrite mxE.
  apply: (isum_n_cons IH _ (inde_rv_sum_mlog_prod _ _)).
  rewrite /sum; split.
  + split; [exact: TupleDist.head_of | exact: TupleDist.tail_of].
  + move=> ta; rewrite /= big_ord_recl /=; congr (_ + _)%R.
    apply eq_bigr => i _; by rewrite mxE.
Qed.

(** Constant used in the statement of AEP: *)

Section aep_k0_constant.

Variables (A : finType) (P : dist A).

Definition aep_bound epsilon := (aep_sigma2 P / epsilon ^ 3)%R.

Lemma aep_bound_pos e (_ : 0 < e) : 0 <= aep_bound e.
Proof. apply divR_ge0; [exact: aep_sigma2_nonneg | exact/pow_lt]. Qed.

Lemma aep_bound_decreasing e e' : 0 < e' <= e -> aep_bound e <= aep_bound e'.
Proof.
case=> Oe' e'e.
apply leR_wpmul2l; first exact: aep_sigma2_nonneg.
apply leR_inv => //; first exact/pow_lt.
apply pow_incr => //; split; [exact/ltRW | exact/e'e ].
Qed.

End aep_k0_constant.

Section AEP.

Variables (A : finType) (P : dist A) (n : nat) (epsilon : R).
Hypothesis Hepsilon : 0 < epsilon.

Lemma aep : aep_bound P epsilon <= INR n.+1 ->
  Pr (P `^ n.+1) [set t | (0 <b P `^ n.+1 t) &&
    (`| (--log (P `^ n.+1) '/ n.+1) t - `H P | >b= epsilon) ] <= epsilon.
Proof.
move=> Hbound.
apply (@leR_trans (aep_sigma2 P / (INR n.+1 * epsilon ^ 2))%R); last first.
  rewrite /aep_bound in Hbound.
  apply (@leR_wpmul2r (epsilon / INR n.+1)) in Hbound; last first.
    apply divR_ge0; [exact/ltRW/Hepsilon | exact/ltR0n].
  rewrite [in X in _ <= X]mulRCA mulRV ?INR_eq0' // ?mulR1 in Hbound.
  apply/(leR_trans _ Hbound)/Req_le; field.
  split; [by rewrite INR_eq0 | exact: gtR_eqF].
have Hisum := sum_mlog_prod_isum_map_mlog P n.
have H1 : forall k i, `E ((\row_(i < k.+1) --log P) ``_ i) = `H P.
  by move=> k i; rewrite mxE E_mlog.
have H2 : forall k i, `V ((\row_(i < k.+1) --log P) ``_ i) = aep_sigma2 P.
  by move=> k i; rewrite mxE V_mlog.
have {H1 H2} := (wlln (H1 n) (H2 n) Hisum Hepsilon).
move/(leR_trans _); apply.
apply/Pr_incl/subsetP => ta; rewrite 2!inE => /andP[H1].
rewrite [--log _]lock /= -lock /= TupleDist.dE log_rmul_rsum_mlog //.
apply: (rprodr_gt0_inv (dist_ge0 P)).
move: H1; by rewrite TupleDist.dE => /ltRP.
Qed.

End AEP.
