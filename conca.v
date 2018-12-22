From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.
Require Import entropy proba cproba convex binary_entropy_function.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section concavity_of_entropy.

Lemma Rnonneg_convex : convex_interval (fun x => 0 <= x).
Proof.
  rewrite /convex_interval.
  move => x y t H H0 H1.
  have H2 : 0 <= onem t by move : H1 => [] _ /onem_ge0.
  have H3 : 0 = 0 + 0 by rewrite Rplus_0_r.
  rewrite (_ : 0 = 0 + 0);
    [apply Rplus_le_compat;
     rewrite (_ : 0 = 0 * 0);
     [|by rewrite Rmult_0_r| |by rewrite Rmult_0_r]
    | by rewrite Rplus_0_r]; apply Rmult_le_compat => //=; try by apply Req_le.
  by move : H1 => [].
Qed.

Definition Rnonneg_interval := mkInterval Rnonneg_convex.

Lemma concavivity_of_entropy : concavef_in Rnonneg_interval H2.
Abort.

End concavity_of_entropy.
(* TODO: concavity of relative entropy and of mutual information *)
