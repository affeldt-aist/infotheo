From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.
Require Import entropy proba cproba convex binary_entropy_function.
Require Import Ranalysis_ext Lra.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section concavity_of_entropy.

Lemma Rnonneg_convex : convex_interval (fun x => 0 <= x).
Proof.
  rewrite /convex_interval.
  move => x y t Hx Hy Ht.
  have H : 0 <= onem t by move : Ht => [] _ /onem_ge0.
  rewrite (_ : 0 = 0 + 0);
    [apply Rplus_le_compat;
     rewrite (_ : 0 = 0 * 0);
     [|by rewrite Rmult_0_r| |by rewrite Rmult_0_r]
    | by rewrite Rplus_0_r]; apply Rmult_le_compat => //=; try by apply Req_le.
  by move : Ht => [].
Qed.

Definition Rnonneg_interval := mkInterval Rnonneg_convex.

Lemma onem_eq1 : forall r : R, onem r = 1 <-> r = 0.
Proof.
  rewrite /onem; move => r; apply conj; [|by move => ->; rewrite Rminus_0_r].
  by move /Rplus_0_r_uniq /Ropp_eq_0_compat; rewrite Ropp_involutive.
Qed.

Lemma onem_01 : onem 0 = 1.
Proof. by rewrite onem_eq1. Qed.
Lemma onem_10 : onem 1 = 0.
Proof. by rewrite onem_eq0. Qed.

Lemma open_interval_convex (a b : R) (Hab : a < b) : convex_interval (fun x => a < x < b).
Proof.
  move => x y t [Hxa Hxb] [Hya Hyb] [[Haltt|Haeqt] [Htltb|Hteqb]]
   ; [
   | by rewrite {Haltt} Hteqb onem_10 mul0R addR0 mul1R; apply conj
   | by rewrite {Htltb} -Haeqt onem_01 mul0R add0R mul1R; apply conj
   | by rewrite Hteqb in Haeqt; move : Rlt_0_1 => /Rlt_not_eq].
  have H : 0 < onem t by apply onem_gt0.
  apply conj.
  - rewrite -[X in X < t * x + onem t * y]mul1R -(onemKC t) mulRDl.
    by apply ltR_add; rewrite ltR_pmul2l.
  - rewrite -[X in _ + _ < X]mul1R -(onemKC t) mulRDl.
    by apply ltR_add; rewrite ltR_pmul2l.
Qed.  

Lemma open_unit_interval_convex : convex_interval (fun x => 0 < x < 1).
Proof.
  apply /open_interval_convex /Rlt_0_1.
Qed.

Definition open_unit_interval := mkInterval open_unit_interval_convex.

Lemma pderivable_H2 : pderivable H2 (mem_interval open_unit_interval).
Proof.
move=> x /= [Hx0 Hx1].
apply derivable_pt_plus.
apply derivable_pt_opp.
apply derivable_pt_mult; [apply derivable_pt_id|apply derivable_pt_Log].
assumption.
apply derivable_pt_opp.
apply derivable_pt_mult.
apply derivable_pt_Rminus.
apply derivable_pt_comp.
apply derivable_pt_Rminus.
apply derivable_pt_Log.
lra.
(* NB : transparent definition is required to proceed with a forward proof, later in concavity_of_entropy_x_le_y *)
Defined.

Lemma expand_interval_closed_to_open a b c d :
  a < b -> b < c -> c < d -> forall x, b <= x <= c -> a < x < d.
Proof.
  move => Hab Hbc Hcd x [Hbx Hxc].
  by apply conj; [eapply Rlt_le_trans|eapply Rle_lt_trans]; [exact Hab|exact Hbx|exact Hxc|exact Hcd].
Qed.

Lemma expand_internal_closed_to_closed a b c d :
  a <= b -> b < c -> c <= d -> forall x, b <= x <= c -> a <= x <= d.
Proof.
  move => Hab Hbc Hcd x [Hbx Hxc].
  by apply conj; [eapply Rle_trans|eapply Rle_trans]; [exact Hab|exact Hbx|exact Hxc|exact Hcd].
Qed.

Lemma expand_interval_open_to_open a b c d :
  a < b -> b < c -> c < d -> forall x, b < x < c -> a < x < d.
Proof.
  move => Hab Hbc Hcd x [Hbx Hxc].
  by apply conj; [eapply Rlt_trans|eapply Rlt_trans]; [exact Hab|exact Hbx|exact Hxc|exact Hcd].
Qed.

Lemma expand_interval_closed_to_closed a b c d :
  a <= b -> b < c -> c <= d -> forall x, b <= x <= c -> a <= x <= d.
Proof.
  move => Hab Hbc Hcd x [Hbx Hxc].
  by apply conj; [eapply Rle_trans|eapply Rle_trans]; [exact Hab|exact Hbx|exact Hxc|exact Hcd].
Qed.

Lemma concavity_of_entropy_x_le_y x y t :
      open_unit_interval x -> open_unit_interval y -> 0 <= t <= 1 -> x < y
      -> concavef_leq H2 x y t.
Proof.
  move => [H0x Hx1] [H0y Hy1] [H0t Ht1] Hxy.
  eapply second_derivative_convexf.
  Unshelve.
  - Focus 4. done.
  - Focus 4. done.
  - Focus 4.
    move => z Hz.
    by apply /derivable_pt_opp /pderivable_H2 /(@expand_interval_closed_to_open 0 x y 1).
  - Focus 4.
    exact (fun z => log z - log (1 - z)).
  - Focus 4.
    move => z [Hxz Hzy].
    apply derivable_pt_minus.
    apply derivable_pt_Log.
    apply (ltR_leR_trans H0x Hxz).
    apply derivable_pt_comp.
    apply derivable_pt_Rminus.
    apply derivable_pt_Log.
    apply subR_gt0.
    by apply (leR_ltR_trans Hzy Hy1).
  - Focus 4.
    exact (fun z => / (z * (1 - z) * ln 2)).
  -
    move => z Hz.
    rewrite derive_pt_opp.
    set (H := expand_interval_closed_to_open _ _ _ _).
    rewrite /pderivable_H2.
    case H => [H0z Hz1].
    rewrite derive_pt_plus.
    rewrite 2!derive_pt_opp.
    rewrite 2!derive_pt_mult.
    rewrite derive_pt_id derive_pt_comp 2!derive_pt_Log /=.
    rewrite mul1R mulN1R mulRN1.
    rewrite [X in z * X]mulRC [X in (1 - z) * - X]mulRC mulRN 2!mulRA.
    rewrite !mulRV; [|by apply /eqP; move => /subR0_eq /gtR_eqF|by apply /eqP /gtR_eqF].
    rewrite mul1R -2!oppRD oppRK.
    by rewrite [X in X + - _]addRC oppRD addRA addRC !addRA Rplus_opp_l add0R addR_opp.
  -
    move => z [Hxz Hzy].
    rewrite derive_pt_minus.
    rewrite derive_pt_comp 2!derive_pt_Log /=.
    rewrite mulRN1 -[X in _ = X]addR_opp oppRK.
    rewrite -mulRDr [X in _ = X]mulRC.
    have Hzn0 : z != 0 by apply /eqP /gtR_eqF /ltR_leR_trans; [exact H0x| exact Hxz].
    have H1zn0 : 1 - z != 0 by apply /eqP; move => /subR0_eq /gtR_eqF H; apply /H /leR_ltR_trans; [exact Hzy| exact Hy1].
    have Hzn0' : z <> 0 by move : Hzn0 => /eqP.
    have H1zn0' : 1 - z <> 0 by move : H1zn0 => /eqP.
    have Hz1zn0 : z * (1 - z) <> 0 by apply /eqP; rewrite mulR_neq0; apply /andP.
    have ln2n0 : ln 2 <> 0 by move : ln2_gt0 => /gtR_eqF.
    have -> : / z = (1 - z) / (z * (1 - z)) by change (/ z = (1 - z) * / (z * (1 - z))); rewrite invRM // [X in _ = _ * X]mulRC mulRA mulRV // mul1R.
    have -> : / (1 - z) = z  / (z * (1 - z)) by change (/ (1 - z) = z * / (z * (1 - z))); rewrite invRM // mulRA mulRV // mul1R.
    rewrite -Rdiv_plus_distr.
    rewrite -addRA Rplus_opp_l addR0.
    by rewrite div1R -invRM.
  -
    move => z [Hxz Hzy].
    have Hz : 0 < z by apply /ltR_leR_trans; [exact H0x| exact Hxz].
    have H1z : 0 < 1 - z by apply /subR_gt0 /leR_ltR_trans; [exact Hzy| exact Hy1].
    apply /or_introl /invR_gt0.
    by apply mulR_gt0; [apply mulR_gt0|apply ln2_gt0].
Qed.

Lemma convexf_leq_sym f x y : (forall t, 0 <= t <= 1 -> convexf_leq f x y t) -> forall t, 0 <= t <= 1 -> convexf_leq f y x t.
Proof.
  move => H t [H0t Ht1]; move: (H (onem t)).
  rewrite /convexf_leq onemK.
  rewrite [X in (_ -> f X <= _) -> _]addRC [X in (_ -> f _ <= X) -> _]addRC.
  apply.
  by apply conj; [apply onem_ge0 | apply onem_le1].
Qed.

Lemma convexf_on_point f x t : convexf_leq f x x t.
Proof.
  by rewrite /convexf_leq -2!mulRDl onemKC 2!mul1R; apply or_intror.
Qed.

Lemma concavity_of_entropy : concavef_in open_unit_interval H2.
Proof.
  rewrite /concavef_in /concavef_leq => x y t Hx Hy Ht.  
  (* wlogつかう. まず関係ない変数を戻し, *)
  move : t Ht.
  (* 不等号をorでつないだやつを用意して *)
  move : (Rtotal_order x y) => Hxy.
  (* その不等号のひとつを固定してwlogする *)
  wlog : x y Hx Hy Hxy / x < y.
  -
    move => H.
    case Hxy; [apply H|] => //.
    case => [-> t Ht|]; [by apply convexf_on_point|].
    move => Hxy'; apply convexf_leq_sym.
    apply H => //.
    by apply or_introl.
  - 
    by move => Hxy' t Ht; apply concavity_of_entropy_x_le_y.
Qed.

End concavity_of_entropy.
(* TODO: concavity of relative entropy and of mutual information *)
