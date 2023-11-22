(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix.
From mathcomp Require boolp.
From mathcomp Require Import mathcomp_extra Rstruct reals.
Require Import Reals Ranalysis_ext Lra.
Require Import ssrR Reals_ext realType_ext logb ssr_ext ssralg_ext bigop_ext.
Require Import fdist jfdist_cond entropy convex binary_entropy_function.
Require Import log_sum divergence.

(******************************************************************************)
(*                Section 2.7 of Elements of Information Theory               *)
(*                                                                            *)
(* Formalization of the section 2.7 of:                                       *)
(* Thomas M. Cover, Joy A. Thomas, Elements of Information Theory, Wiley,     *)
(* 2005                                                                       *)
(*                                                                            *)
(* dom_pair A == type of dominated pairs, i.e., a pair of distributions       *)
(*               (d, e) s.t. d << e                                           *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*              convex_div == divergence restricted to dominated pairs is a   *)
(*                            convex function; it's actually not a            *)
(*                            restriction since div is meaningful only on     *)
(*                            dominated pairs                                 *)
(* convex_relative_entropy == convexity of relative entropy                   *)
(*                            (thm 2.7.2)                                     *)
(*         entropy_concave == entropy is concave (thm 2.7.3)                  *)
(* mutual_information_concave == the mutual information is concave w.r.t.     *)
(*                            its first argument (thm 2.7.4)                  *)
(* mutual_information_convex == the mutual information is convex w.r.t        *)
(*                            its second argument (thm 2.7.4)                 *)
(*                                                                            *)
(* ref: Thomas M. Cover, Joy A. Thomas, Elements of Information Theory, 2nd   *)
(* edition, Wiley, 2005                                                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.
Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope convex_scope.
Local Open Scope entropy_scope.

Import Order.POrderTheory GRing.Theory Num.Theory.

Section entropy_log_div.
Variables (A : finType) (p : {fdist A}) (n : nat) (An1 : #|A| = n.+1).
Let u := @fdist_uniform R_numFieldType _ _ An1.

Local Open Scope divergence_scope.

Lemma entropy_log_div : entropy p = log #|A|%:R - D(p || u).
Proof.
rewrite /entropy /div.
evar (RHS : A -> R).
have H a : p a * log (p a / u a) = RHS a.
  have /RleP[H|H] := FDist.ge0 p a.
  - rewrite fdist_uniformE.
    change (p a * log (p a / / #|A|%:R)) with (p a * log (p a * / / #|A|%:R)).
    have H0 : 0 < #|A|%:R by rewrite An1 ltR0n.
    have /eqP H1 : #|A|%:R <> 0 by apply/eqP/gtR_eqF.
    rewrite -RinvE ?An1; last first.
      by rewrite -INRE// INR_eq0'.
    rewrite /Rdiv invRK// logM //; last first.
      by rewrite -INRE ltR0n.
    rewrite mulRDr -INRE.
    rewrite -An1.
    by instantiate (RHS := fun a => p a * log (p a) + p a * log #|A|%:R).
  - by rewrite /RHS -H /= 3!mul0R add0R.
have -> : \sum_(a in A) p a * log (p a / u a) = \sum_(a in A) RHS a.
  by move : H; rewrite /RHS => H; exact: eq_bigr.
rewrite /RHS big_split /= -big_distrl /= (FDist.f1 p) mul1R.
by rewrite -addR_opp oppRD addRC -addRA Rplus_opp_l addR0.
Qed.
End entropy_log_div.

Section dominated_pair.
Variable A : finType.
Implicit Types p q : {prob R}.

Definition dom_pair := {d : {fdist A} * {fdist A} | d.1 `<< d.2}.

Lemma dom_conv p (x y u v : {fdist A}) :
  x `<< y -> u `<< v -> x <| p |> u `<< y <| p |> v.
Proof.
move=> /dominatesP xy /dominatesP uv; apply/dominatesP => a.
rewrite !fdist_convE.
rewrite paddR_eq0; [|exact/mulR_ge0 |exact/mulR_ge0].
rewrite !mulR_eq0 => -[[->|/xy ->]]; last first.
  by rewrite -RplusE -!RmultE mulR0 add0R => -[->|/uv ->]; rewrite !(mul0R,mulR0).
by rewrite -RplusE -!RmultE mul0R add0R => -[|/uv ->];
  [rewrite onem0 => /R1_neq_R0 | rewrite mulR0].
Qed.

Definition avg_dom_pair p (x y : dom_pair) : dom_pair :=
  let ab := proj1_sig x in
  let b_dom_a := proj2_sig x in
  let cd := proj1_sig y in
  let d_dom_c := proj2_sig y in
  exist _ (ab <| p |> cd) (dom_conv p b_dom_a d_dom_c).

Definition uncurry_dom_pair U (f : {fdist A} -> {fdist A} -> U) (x : dom_pair) :=
  f (sval x).1 (sval x).2.

Let avg := avg_dom_pair.

Let avg1 x y : avg 1%:pr x y = x.
Proof. by rewrite /avg; case x => x0 H /=; exact/boolp.eq_exist/conv1. Qed.

Let avgI p x : avg p x x = x.
Proof. by rewrite /avg; case x => x0 H /=; exact/boolp.eq_exist/convmm. Qed.

Let avgC p x y : avg p x y = avg (Prob.p p).~%:pr y x.
Proof. by rewrite /avg; exact/boolp.eq_exist/convC. Qed.

Let avgA p q x y z :
  avg p x (avg q y z) = avg [s_of p, q] (avg [r_of p, q] x y) z.
Proof. by rewrite /avg /=; exact/boolp.eq_exist/convA. Qed.

HB.instance Definition _ := @isConvexSpace.Build dom_pair
  (Choice.class (choice_of_Type dom_pair)) avg avg1 avgI avgC avgA.

End dominated_pair.

Section divergence_convex.
Local Open Scope divergence_scope.
Variables A : finType.

Lemma convex_div : convex_function (uncurry_dom_pair (@div A)).
Proof.
move=> [x Hx] [y Hy] p /=; rewrite /uncurry_dom_pair /=.
rewrite /convex_function_at/= avgRE 2!big_distrr /= -big_split /= /div.
apply leR_sumR => a _; rewrite 2!fdist_convE.
have [y2a0|y2a0] := eqVneq (y.2 a) 0.
  rewrite y2a0 (_ : y.1 a = 0) ?(mulR0,addR0,mul0R); last first.
    by move/dominatesP : Hy; exact.
  have [x2a0|x2a0] := eqVneq (x.2 a) 0.
    rewrite (_ : x.1 a = 0).
      by rewrite -!RmultE -!RplusE ?(mul0R,mulR0,addR0).
    exact/((dominatesP _ _).1 Hx).
  have [p0|p0] := eqVneq p 0%:pr.
    by rewrite p0 -!RmultE -!RplusE ?(mul0R,mulR0,addR0).
  apply/Req_le; rewrite -!RmultE -!RplusE mulRA ?(mulR0,addR0); congr (_ * _ * log _).
  simpl.
  by field; split; exact/eqP.
have [x2a0|x2a0] := eqVneq (x.2 a) 0.
  rewrite x2a0 (_ : x.1 a = 0)// -?RplusE -?RmultE ?(mulR0,add0R,mul0R); last first.
    by move/dominatesP : Hx; exact.
  have [->|t0] := eqVneq (Prob.p p).~ 0; first by rewrite !mul0R.
  apply/Req_le; rewrite mulRA; congr (_ * _ * log _).
  simpl.
  by field; split; exact/eqP.
set h : {fdist A} -> {fdist A} -> {ffun 'I_2 -> R} := fun p1 p2 => [ffun i =>
  [eta (fun=> 0) with ord0 |-> Prob.p p * p1 a, lift ord0 ord0 |-> (Prob.p p).~ * p2 a] i].
have hdom : h x.1 y.1 `<< h x.2 y.2.
  apply/dominatesP => i; rewrite /h /= !ffunE; case: ifPn => _.
    by rewrite mulR_eq0 => -[->|/eqP]; [rewrite mul0R | rewrite (negbTE x2a0)].
  case: ifPn => // _.
  by rewrite mulR_eq0 => -[->|/eqP]; [rewrite mul0R | rewrite (negbTE y2a0)].
have h0 p1 p2 : [forall i, (0 <= h p1 p2 i)%mcR].
  apply/forallPP; first by move=> ?; exact/RleP.
  move=> ?; rewrite /h /= ffunE.
  case: ifPn => [_ | _]; first exact/mulR_ge0.
  case: ifPn => [_ |//].
  by apply/mulR_ge0 => //; exact/onem_ge0/prob_le1.
have h01 (x0 : 'I_2) : 0 <= mkNNFinfun (h0 x.1 y.1) x0.
  rewrite /= /h ffunE/=; case: ifPn => _; first exact: mulR_ge0.
  by case: ifPn => // _; exact: mulR_ge0.
have h02 (x0 : 'I_2) : 0 <= mkNNFinfun (h0 x.2 y.2) x0.
  rewrite /= /h ffunE/=; case: ifPn => _; first exact: mulR_ge0.
  by case: ifPn => // _; exact: mulR_ge0.
have := log_sum setT (mkNNFinfun (h0 x.1 y.1)) (mkNNFinfun (h0 x.2 y.2)) h01 h02 hdom.
rewrite /= -!sumR_ord_setT !big_ord_recl !big_ord0 !addR0.
rewrite /h /= !ffunE => /leR_trans; apply.
rewrite !eqxx eq_sym (negbTE (neq_lift ord0 ord0)) -!mulRA; apply/Req_le.
congr (_  + _ ).
  have [->|t0] := eqVneq p 0%:pr; first by rewrite !mul0R.
  by congr (_ * (_ * log _)); field; split; exact/eqP.
have [->|t1] := eqVneq (Prob.p p).~ 0; first by rewrite !mul0R.
by congr (_ * (_ * log _)); field; split; exact/eqP.
Qed.

Lemma convex_relative_entropy (p1 p2 q1 q2 : {fdist A}) (r : {prob R}) :
  p1 `<< q1 -> p2 `<< q2 ->
  D(p1 <| r |> p2 || q1 <| r |> q2) <= D(p1 || q1) <| r |> D(p2 || q2).
Proof.
move=> pq1 pq2.
exact: (convex_div (exist _ (p1, q1) pq1) (exist _ (p2, q2) pq2)).
Qed.

End divergence_convex.

Section entropy_concave.
Local Open Scope divergence_scope.
Variable A : finType.
Hypothesis cardA_gt0 : (0 < #|A|)%nat.

Let cardApredS : #|A| = #|A|.-1.+1.
Proof. by rewrite prednK. Qed.

Lemma entropy_concave : concave_function (fun P : choice_of_Type {fdist A} => `H P).
Proof.
apply RNconcave_function => p q t; rewrite /convex_function_at.
rewrite !(entropy_log_div _ cardApredS) /= /leconv /= [in X in _ <= X]avgRE.
rewrite oppRD oppRK 2!mulRN mulRDr mulRN mulRDr mulRN oppRD oppRK oppRD oppRK.
rewrite addRCA !addRA -2!mulRN -mulRDl (addRC _ (Prob.p t)).
rewrite !RplusE onemKC mul1R -!RplusE -addRA leR_add2l.
have := convex_relative_entropy t (dom_by_uniform p cardApredS)
                                  (dom_by_uniform q cardApredS).
by rewrite convmm.
Qed.

End entropy_concave.

Module entropy_concave_alternative_proof_binary_case.

Lemma pderivable_H2 : pderivable H2 (CSet.car open_unit_interval).
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
(* NB : transparent definition is required to proceed with a forward proof,
   later in concavity_of_entropy_x_le_y *)
Defined.

Lemma expand_interval_closed_to_open a b c d :
  a < b -> b < c -> c < d -> forall x, b <= x <= c -> a < x < d.
Proof.
move=> ? ? ? x [? ?]; split;
  [exact: (@ltR_leR_trans b)|exact: (@leR_ltR_trans c)].
Qed.

Lemma expand_internal_closed_to_closed a b c d :
  a <= b -> b < c -> c <= d -> forall x, b <= x <= c -> a <= x <= d.
Proof.
move=> ? ? ? ? [? ?]; split; [exact: (@leR_trans b)|exact: (@leR_trans c)].
Qed.

Lemma expand_interval_open_to_open a b c d :
  a < b -> b < c -> c < d -> forall x, b < x < c -> a < x < d.
Proof.
move=> ? ? ? x [? ?]; split; [exact: (@ltR_trans b)|exact: (@ltR_trans c)].
Qed.

Lemma expand_interval_open_to_closed a b c d :
  a <= b -> b < c -> c <= d -> forall x, b < x < c -> a <= x <= d.
Proof.
move=> ? ? ? x [? ?]; split;
  [exact/ltRW/(@leR_ltR_trans b)|exact/ltRW/(@ltR_leR_trans c)].
Qed.

Lemma concavity_of_entropy_x_le_y x y (t : {prob R}) :
  x \in open_unit_interval -> y \in open_unit_interval -> x < y ->
  concave_function_at H2 x y t.
Proof.
rewrite !classical_sets.in_setE => -[H0x Hx1] [H0y Hy1] Hxy.
apply RNconcave_function_at.
set Df := fun z : R => log z - log (1 - z).
have @f_derive : pderivable (fun x0 => - H2 x0) (fun z => x <= z <= y).
  move => z Hz.
  exact/derivable_pt_opp/pderivable_H2/(@expand_interval_closed_to_open 0 x y 1).
have @derive_pt_f : forall z (Hz : x <= z <= y),
  Df z = derive_pt (fun x1 => - H2 x1) _ (f_derive _ Hz).
  move => z Hz.
  rewrite derive_pt_opp.
  set H := expand_interval_closed_to_open _ _ _ _.
  rewrite /pderivable_H2.
  case H => [H0z Hz1].
  rewrite derive_pt_plus.
  rewrite 2!derive_pt_opp.
  rewrite 2!derive_pt_mult.
  rewrite derive_pt_id derive_pt_comp 2!derive_pt_Log /=.
  rewrite mul1R mulN1R mulRN1.
  rewrite [X in z * X]mulRC [X in (1 - z) * - X]mulRC mulRN 2!mulRA.
  rewrite !mulRV ?gtR_eqF // ?subR_gt0 // mul1R -2!oppRD oppRK.
  by rewrite [X in X + - _]addRC oppRD addRA addRC !addRA Rplus_opp_l add0R addR_opp.
have @pderivable_Df : pderivable Df (fun z => x <= z <= y).
  move => z [Hxz Hzy].
  apply derivable_pt_minus.
  apply derivable_pt_Log.
  apply (ltR_leR_trans H0x Hxz).
  apply derivable_pt_comp.
  apply derivable_pt_Rminus.
  apply derivable_pt_Log.
  apply subR_gt0.
  exact: leR_ltR_trans Hzy Hy1.
set DDf := fun z => / (z * (1 - z) * ln 2).
have derive_pt_Df : forall z (Hz : x <= z <= y), DDf z = derive_pt Df z (pderivable_Df z Hz).
  rewrite -/Df => z [Hxz Hzy].
  rewrite derive_pt_minus derive_pt_comp 2!derive_pt_Log /=.
  rewrite mulRN1 -[X in _ = X]addR_opp oppRK.
  rewrite -mulRDr [X in _ = X]mulRC.
  have Hzn0 : z != 0 by apply/gtR_eqF/(ltR_leR_trans H0x Hxz).
  have H1zn0 : 1 - z != 0.
    by rewrite subR_eq0' ?gtR_eqF //; apply/leR_ltR_trans; [exact Hzy| exact Hy1].
  have Hzn0' : z <> 0 by move : Hzn0 => /eqP.
  have H1zn0' : 1 - z <> 0 by move : H1zn0 => /eqP.
  have /eqP Hz1zn0 : z * (1 - z) <> 0 by rewrite mulR_neq0.
  have -> : / z = (1 - z) / (z * (1 - z)).
    change (/ z = (1 - z) * / (z * (1 - z))).
    by rewrite invRM // [X in _ = _ * X]mulRC mulRA mulRV // mul1R.
  have -> : / (1 - z) = z  / (z * (1 - z)).
    change (/ (1 - z) = z * / (z * (1 - z))).
    by rewrite invRM // mulRA mulRV // mul1R.
  by rewrite -Rdiv_plus_distr -addRA Rplus_opp_l addR0 div1R -invRM // ln2_neq0.
have DDf_nonneg : forall z, x <= z <= y -> 0 <= DDf z.
  move => z [Hxz Hzy].
  have Hz : 0 < z by apply /ltR_leR_trans; [exact H0x| exact Hxz].
  have H1z : 0 < 1 - z by apply /subR_gt0 /leR_ltR_trans; [exact Hzy| exact Hy1].
  by apply/or_introl/invR_gt0/mulR_gt0; [exact/mulR_gt0 | exact/ln2_gt0].
exact: (@second_derivative_convexf_pt _ _ _ _ Df _ _ DDf).
Qed.

Lemma concavity_of_entropy : concave_function_in open_unit_interval H2.
Proof.
rewrite /concave_function_in => x y t Hx Hy.
apply: RNconcave_function_at.
(* wlogつかう. まず関係ない変数を戻し, *)
move: t.
(* 不等号をorでつないだやつを用意して *)
have Hxy := Rtotal_order x y.
(* その不等号のひとつを固定してwlogする *)
wlog : x y Hx Hy Hxy / x < y.
  move=> H.
  case: Hxy.
    by apply H => //; lra.
  case => [-> t|Hxy' t]; first exact/convex_function_atxx.
  apply: convex_function_sym => // t0.
  by apply H => //; left.
move=> Hxy' t.
exact/R_convex_function_atN /concavity_of_entropy_x_le_y.
Qed.

End entropy_concave_alternative_proof_binary_case.

Section mutual_information_concave.
Local Open Scope fdist_scope.
Variables (A B : finType) (W : A -> {fdist B}).
Hypothesis B_not_empty : (0 < #|B|)%nat.

Lemma mutual_information_concave :
  concave_function (fun P : choice_of_Type {fdist A} => mutual_info (P `X W)).
Proof.
suff : concave_function
  (fun P : choice_of_Type {fdist A} => let PQ := fdistX (P `X W) in `H PQ`1 - cond_entropy PQ).
  set f := fun _ => _. set g := fun _ => _.
  suff -> : f = g by [].
  by rewrite boolp.funeqE => d; rewrite {}/f {}/g /= -mutual_infoE -mutual_info_sym.
apply: R_concave_functionB.
  have /RNconvex_function concave_H := entropy_concave B_not_empty.
  apply: R_concave_functionN => p q t /=.
  rewrite /convex_function_at 3!fdistX1.
  apply: leR_trans (concave_H (p `X W)`2 (q `X W)`2 t).
  under eq_bigr do rewrite fdist_prod2_conv.
  by apply/RleP; rewrite lexx.
suff : affine (fun x : choice_of_Type {fdist A} => cond_entropy (fdistX (x `X W))).
  by move=> /affine_functionP[].
move=> t p q.
rewrite /= avgRE /cond_entropy /cond_entropy1.
rewrite 2!big_distrr -big_split /=; apply eq_bigr => a _.
rewrite !fdistX2 !fdist_fstE !mulRN -oppRD; congr (- _).
rewrite !big_distrr -big_split /=; apply eq_bigr => b _.
rewrite !big_distrl !big_distrr -big_split /=; apply eq_bigr => b0 _.
rewrite !fdist_prodE /= fdist_convE /= !(mulRA (Prob.p t)) !(mulRA (Prob.p t).~).
rewrite -!(RmultE,RplusE).
have [Hp|/eqP Hp] := eqVneq (Prob.p t * p a) 0.
  rewrite Hp ?(add0R,mul0R).
  have [->|/eqP Hq] := eqVneq ((Prob.p t).~ * q a) 0.
    by rewrite ?(mul0R).
  rewrite jcPr_fdistX_prod /=; last first.
    by rewrite fdist_convE -RplusE -!RmultE Hp add0R.
  by rewrite jcPr_fdistX_prod //=; move: Hq; rewrite mulR_neq0 => -[].
have [Hq|Hq] := eqVneq ((Prob.p t).~ * q a) 0.
  rewrite Hq !(mul0R,addR0).
  rewrite jcPr_fdistX_prod; last first.
    by rewrite fdist_convE -RplusE -!RmultE Hq addR0.
  by rewrite jcPr_fdistX_prod //=; move: Hp; rewrite mulR_neq0 => -[].
rewrite jcPr_fdistX_prod; last first.
  by rewrite /= fdist_convE paddR_eq0; [tauto|exact/mulR_ge0|exact/mulR_ge0].
rewrite jcPr_fdistX_prod; last by move: Hp; rewrite mulR_neq0 => -[].
rewrite jcPr_fdistX_prod //=; last by move/eqP: Hq; rewrite mulR_neq0 => -[].
move/eqP in Hq.
rewrite /onem -RminusE (_ : 1%mcR = 1)//.
rewrite /onem -RminusE (_ : 1%mcR = 1)// in Hq.
by rewrite -!mulRDl.
Qed.

End mutual_information_concave.

Section mutual_information_convex.
Local Open Scope divergence_scope.
Local Open Scope fdist_scope.
Variables (A B : finType) (P : {fdist A}).

Lemma mutual_information_convex :
  convex_function (fun W : A -> {fdist B} => mutual_info (P `X W)).
Proof.
move=> /= p1yx p2yx t.
pose p1xy := P `X p1yx.
pose p2xy := P `X p2yx.
pose p1 := p1xy`2.
pose p2 := p2xy`2.
pose plambdayx := fun a => p1yx a <| t |> p2yx a.
pose plambdaxy := P `X plambdayx.
pose plambday := plambdaxy`2.
pose qlambdaxy := P `x plambday.
pose q1xy := P `x p1.
pose q2xy := P `x p2.
rewrite /convex_function_at.
have -> : mutual_info (P `X (fun x => p1yx x <| t |> p2yx x)) = D(plambdaxy || qlambdaxy).
  rewrite mutual_infoE0 /div pair_big /=; apply: eq_bigr => -[a b] _ /=.
  congr (_ * log (_ / _)).
  by rewrite /qlambdaxy fdist_prodE /= fdist_prod1.
have -> : qlambdaxy = q1xy <| t |> q2xy.
  apply/fdist_ext => -[a b].
  rewrite !fdist_prodE !fdist_convE /= /q1xy /q2xy !fdist_prodE /= /p1 /plambday.
  rewrite !fdist_sndE !big_distrr /= -big_split /=; apply eq_bigr => a0 _.
  rewrite /plambdaxy /= !fdist_prodE /= /p1xy /plambdayx fdist_convE /=.
  rewrite -!(RmultE,RplusE).
  field.
have -> : plambdaxy = p1xy <| t |> p2xy.
  apply/fdist_ext => -[a b].
  rewrite !fdist_prodE !fdist_convE /= /p1xy /p2xy !fdist_prodE /=.
  rewrite -!(RmultE,RplusE).
  field.
have -> : mutual_info (P `X p1yx) = D(p1xy || q1xy).
  rewrite mutual_infoE0 /div pair_big /=; apply: eq_bigr => -[a b] _ /=.
  congr (_ * log (_ / _)).
  by rewrite /q1xy fdist_prodE /= fdist_prod1.
have -> : mutual_info (P `X p2yx) = D(p2xy || q2xy).
  rewrite mutual_infoE0 /div pair_big /=; apply: eq_bigr => -[a b] _ /=.
  by congr (_ * log (_ / _)); rewrite /q2xy fdist_prodE fdist_prod1.
apply: convex_relative_entropy.
- apply/dominatesP => -[a b].
  rewrite /q1xy /p1xy fdist_prodE /= mulR_eq0 /p1 /p1xy => -[|].
    by rewrite fdist_prodE => ->; rewrite /= mul0r.
  by rewrite fdist_sndE => /psumr_eq0P ->.
- apply/dominatesP => -[a b].
  rewrite /q1xy /p1xy fdist_prodE /= mulR_eq0.
  rewrite /p1 /p1xy => -[|].
    by rewrite fdist_prodE => ->; rewrite mul0r.
  by rewrite fdist_sndE => /psumr_eq0P /= ->.
Qed.

End mutual_information_convex.
