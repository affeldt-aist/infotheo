(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype.
From mathcomp Require Import tuple finfun bigop.
Require Import Reals Fourier.
Require Import Reals_ext Rssr ln_facts log2 Rbigop proba.

(** * The Kullback-Leibler divergence *)

Reserved Notation "'D(' P '||' Q ')' " (at level 50, P, Q at next level).

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section divergence_def.

Variable A : finType.
Variables P Q : dist A.

Definition div := \rsum_(a in A) P a * (log (P a) - log (Q a)).

End divergence_def.

Notation "'D(' P '||' Q ')' " := (div P Q) : divergence_scope.

Local Open Scope divergence_scope.
Local Open Scope proba_scope.
Local Open Scope reals_ext_scope.

Section divergence_lemmas.

Variable A : finType.
Variables P Q : dist A.

Lemma div_diff_ub x y : 0 <= x -> 0 <= y -> (y = 0 -> x = 0) ->
                        x * (log y - log x) <= (y - x) * log (exp 1).
Proof.
move=> Hx Hy Hxy.
case/boolP : (y == 0) => [ /eqP y0 | /eqP y0].
- move: (Hxy y0) => ->.
  rewrite y0 subRR mul0R subRR mul0R; exact: Rle_refl.
- have y_pos : 0 < y by apply Rlt_le_neq => // aux; symmetry in aux.
  case/boolP : (x == 0) => [/eqP -> | /eqP x_not_0].
  + rewrite mul0R subR0; apply mulR_ge0 => //; exact: log_exp1_Rle_0.
  + have x_pos : 0 < x by apply Rlt_le_neq => // /esym.
    rewrite (_ : y - x = x * (y / x - 1) ); last first.
      rewrite mulRDr /Rdiv mulRC -mulRA Rinv_l; last by apply not_eq_sym, Rlt_not_eq, x_pos.
      by rewrite mulRN 2!mulR1.
    rewrite -mulRA; apply Rmult_le_compat_l; first exact/ltRW/x_pos.
    rewrite /Rminus -LogV; last by apply x_pos.
    rewrite -Log_mult; last 2 first.
      exact y_pos.
      by apply Rinv_0_lt_compat, x_pos.
    apply log_id_cmp.
    by apply (Rlt_mult_inv_pos _ _ y_pos x_pos).
Qed.

Hypothesis P_dom_by_Q : P << Q.

Lemma leq0div : 0 <= D(P || Q).
Proof.
apply Rge_le; rewrite /div.
rewrite [X in X >= _](_ : _ = - \rsum_(a | a \in A) P a * (log (Q a) - log (P a))); last first.
  rewrite (big_morph _ morph_Ropp oppR0); apply eq_bigr => a _; by field.
rewrite -[X in _ >= X]oppR0; apply Ropp_le_ge_contravar.
apply (Rle_trans _ ((\rsum_(a | a \in A) (Q a - P a)) * log (exp 1))).
  rewrite (big_morph _ (morph_mulRDl _) (mul0R _)).
  apply ler_rsum => a _; apply div_diff_ub; by
    [apply dist_nonneg | apply Rle0 | apply P_dom_by_Q].
rewrite -{1}(mul0R (log (exp 1))).
apply Rmult_le_compat_r; first exact/log_exp1_Rle_0.
rewrite big_split /= -(big_morph _ morph_Ropp oppR0).
rewrite !pmf1 Rplus_opp_r; exact/Rle_refl.
Qed.

(* TODO: move? *)
Lemma log_id_diff x y : 0 <= x -> 0 <= y ->
  (y = 0 -> x = 0) -> x * (log y - log x) = (y - x) * log (exp 1) -> x = y.
Proof.
move=> Hx Hy Hxy Hxy2.
case/boolP : (y == 0) => [y0 | y_not_0].
- move/eqP in y0 ; have x0 : x = 0 ; first apply Hxy, y0 ; by rewrite x0 y0.
- move/eqP in y_not_0.
  have y_pos : 0 < y by apply Rlt_le_neq => // /esym.
  case/boolP : (x == 0) => [/eqP x0 | /eqP x_not_0].
  - move/esym : Hxy2; rewrite x0 mul0R subR0 => /Rmult_integral => Hxy2.
    case : Hxy2 => //.
    by rewrite logexp1E => /invR_eq0/ln_2_neq0.
  - have x_pos : 0 < x by apply Rlt_le_neq => // /esym.
    symmetry.
    apply (Rmult_eq_reg_l (/ x)); last by apply not_eq_sym, Rlt_not_eq, Rinv_0_lt_compat.
    rewrite Rinv_l ; last by apply not_eq_sym, Rlt_not_eq, x_pos.
    apply log_id_eq.
      by rewrite mulRC; apply Rlt_mult_inv_pos ; [apply y_pos | apply x_pos].
    rewrite {1}/log Log_mult; last 2 first.
      by apply Rinv_0_lt_compat, x_pos.
      assumption.
    apply (Rmult_eq_reg_l x); last by apply not_eq_sym, Rlt_not_eq.
    rewrite LogV // addRC Hxy2 mulRA /Rminus mulRDr; apply Rmult_eq_compat_r.
    field.
    exact/gtR_eqF.
Qed.

Lemma eq0div : D(P || Q) = 0 <-> P = Q.
Proof.
split => [HPQ | ->].
- apply dist_eq, pos_fun_eq, FunctionalExtensionality.functional_extensionality => j.
  apply log_id_diff; last 4 first.
    by apply dist_nonneg.
    by apply dist_nonneg.
    by apply P_dom_by_Q.
  symmetry.
  move: j (Logic.eq_refl true).
  apply Rle_big_eq.
  - move=> i _; apply div_diff_ub.
      by apply dist_nonneg.
      by apply dist_nonneg.
      by apply P_dom_by_Q.
  - transitivity 0; last first.
      symmetry.
      rewrite -{1}oppR0 -{1}HPQ (big_morph _ morph_Ropp oppR0); apply eq_bigr => a _; by field.
  - rewrite -(big_morph _ (morph_mulRDl _) (mul0R _)) big_split /=.
    by rewrite -(big_morph _ morph_Ropp oppR0) !pmf1 Rplus_opp_r mul0R.
- by rewrite /div; apply big1=> a _; rewrite subRR mulR0.
Qed.

End divergence_lemmas.
