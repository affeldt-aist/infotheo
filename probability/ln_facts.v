(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum interval lra.
From mathcomp Require Import boolp classical_sets Rstruct reals.
From mathcomp Require Import topology normedtype derive sequences exp.
Require Import realType_ext realType_logb convex derive_ext.

(******************************************************************************)
(*                      Results about the Analysis of ln                      *)
(*                                                                            *)
(* Section ln_id_sect.                                                        *)
(*   about the function x |-> ln x - (x - 1)                                  *)
(* Section xlnx_sect.                                                         *)
(*   about the function x |-> x * ln x                                        *)
(* Section diff_xlnx                                                          *)
(*   about the function x |-> xlnx (1 - x) - xlnx x.                          *)
(* Section Rabs_xlnx                                                          *)
(*   proof that | x - y | <= a implies | xlnx x - xlnx y | <= - xlnx a        *)
(* Section log_concave                                                        *)
(*   concavity of log                                                         *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import Order.Theory GRing.Theory Num.Theory.

Import numFieldTopology.Exports.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.

(* TODO: move *)
Lemma derivable_ln {R : realType} x : 0 < x -> derivable (@ln R) x 1.
Proof. by move=> x0; apply: ex_derive; exact: exp.is_derive1_ln. Qed.

(* TODO: move *)
Lemma gt0_near_nbhs {R : realType} (x : R) : 0 < x ->
  \forall x0 \near nbhs x, 0 < x0.
Proof.
move=> x0.
exists (x / 2) => //=.
  by rewrite divr_gt0//.
move=> A/=.
have [//|A0] := ltP 0 A.
rewrite ltNge => /negP; rewrite boolp.falseE; apply.
rewrite ger0_norm ?subr_ge0; last first.
  by rewrite (le_trans A0)// ltW.
rewrite lerBrDr.
rewrite (@le_trans _ _ (x/2))//.
rewrite gerDl//.
by rewrite ler_piMr// ltW.
Unshelve. all: by end_near. Qed.

(* TODO: clean *)
Lemma MVT_cor1_pderivable_open_continuity {R : realType} (f : R -> R) (a b : R) :
  (forall x, a < x < b -> derivable f x 1) -> continuous_at a f ->
  continuous_at b f ->
  a < b ->
  exists c, a < c < b /\
    f b - f a = 'D_1 f c * (b - a) /\ a < c < b.
Proof.
move=> H prca prcb ab.
have H1 : (forall x : R^o, x \in `]a, b[ -> is_derive x 1 f ('D_1 f x)).
  move=> x.
  rewrite in_itv/= => /andP[ax xb].
  apply/derivableP.
  apply: H.
  by rewrite ax xb.
have H2 : {within `[a, b], continuous f}%classic.
  apply/continuous_within_itvP => //.
  split.
    have : {in `]a, b[, forall x, derivable f x 1}.
      move=> w wab.
      apply: H.
      done.
    move/derivable_within_continuous.
    rewrite continuous_open_subspace//.
      move=> K z zab.
      apply: K => //.
      by rewrite inE.
    by apply: interval_open => //=.
    (* TODO: pkoi je peux pas utiliser itv_open?*)
  red in prca.
  exact: cvg_at_right_filter.
  red in prca.
  exact: cvg_at_left_filter.
have [c ca fab] := @MVT R f ('D_1 f) _ _ ab H1 H2.
exists c; split.
 by move: ca; rewrite in_itv/=.
by rewrite fab.
Qed.

(* TODO: clean *)
Lemma derive_sincreasing_interv {R : realType} a b (f : R -> R)
  (pr : forall x, a < x < b -> derivable f x 1)
  (prc : forall x, a <= x <= b -> continuous_at x f) :
  a < b ->
  ((forall t:R, a < t < b -> derivable f t 1 -> 0 < 'D_1 f t) ->
    forall x y:R, a <= x <= b -> a <= y <= b -> x < y -> f x < f y).
Proof.
intros H H0 x y H1 H2 H3.
rewrite -subr_gt0.
have prd' : forall z, x < z < y -> derivable f z 1.
  move=> z /= /andP[Hz1 Hz2] ; apply pr.
  apply/andP; split.
  - apply: (@le_lt_trans _ _ x) => //.
    by case/andP : H1.
  - apply: (@lt_le_trans _ _ y) => //.
    by case/andP : H2.
have H0' : forall t, x < t < y -> 0 < 'D_1 f t.
  move=> z /= /andP[Hz0 Hz1].
  apply H0.
  apply/andP; split.
  - apply: (@le_lt_trans _ _ x) => //.
    by case/andP : H1.
  - apply: (@lt_le_trans _ _ y) => //.
    by case/andP : H2.
  apply: pr.
  case/andP : H1 => + _.
  move=> /le_lt_trans => /(_ _ Hz0) ->/=.
  rewrite (lt_le_trans Hz1)//.
  by case/andP : H2.
have prcx : continuous_at (x : R^o) f.
  by apply: prc.
have prcy : continuous_at (y : R^o) f.
  by apply: prc.
have aux : a < b.
  done.
case: (MVT_cor1_pderivable_open_continuity prd' prcx prcy H3); intros x0 [x1 [H7 H8]].
rewrite H7.
apply mulr_gt0; first by apply H0'.
by rewrite subr_gt0.
Qed.

Section xlnx_sect.

Section xlnx.
Context {R : realType}.

Definition xlnx_total (y : R) := y * ln y.

Lemma derivable_xlnx_total x : 0 < x -> derivable xlnx_total x 1.
Proof. by move=> x0; apply: derivableM => //; exact: derivable_ln. Qed.

Lemma xlnx_total_neg (x : R) : 0 < x < 1 -> xlnx_total x < 0.
Proof.
case/andP => lt0x ltx1.
rewrite -(opprK 0) ltrNr oppr0 -mulrN.
apply mulr_gt0 => //.
by rewrite ltrNr oppr0 ln_lt0// lt0x.
Qed.

Lemma xlnx_total_xlnx x : 0 < x -> xlnx x = xlnx_total x.
Proof. by move=> x0; rewrite /xlnx x0. Qed.

Lemma continuous_at_xlnx_total (r : R) : 0 < r -> continuous_at r xlnx_total.
Proof. by move=> r0; apply: cvgM => //; exact: continuous_ln. Qed.

Definition xlnx (x : R) := if 0 < x then xlnx_total x else 0.

Lemma xlnx_0 : xlnx 0 = 0.
Proof. by rewrite /xlnx ltxx. Qed.

Lemma xlnx_1 : xlnx 1 = 0.
Proof. by rewrite /xlnx ltr01 /xlnx_total ln1 mulr0. Qed.

Lemma xlnx_neg x : 0 < x < 1 -> xlnx x < 0.
Proof. by move=> /andP[x0 x1]; rewrite /xlnx x0 xlnx_total_neg ?x0. Qed.

Lemma continuous_at_xlnx (r : R) : continuous_at r xlnx.
Proof.
apply/cvgrPdist_le => /= eps eps_pos.
have [r_gt0|r_lt0|<-{r}] := ltgtP 0 r.
- have := continuous_at_xlnx_total r_gt0.
  move=> /cvgrPdist_le/(_ _ eps_pos)[k/= k_pos Hk].
  exists (Num.min k r).
    by rewrite lt_min r_gt0 k_pos.
  move=> x/=; rewrite lt_min => /andP[rxk rxr].
  rewrite /xlnx r_gt0.
  have -> : 0 < x.
    rewrite -(addr0 x) -[in ltRHS](subrr r) addrA addrAC.
    apply (@le_lt_trans _ _ ((x + - r) + `| x + - r |)).
      by rewrite addrC -lerBlDr sub0r -normrN ler_norm.
    by rewrite ltrD2l distrC.
  exact: Hk.
- exists (- r).
    by rewrite ltrNr oppr0.
  move=> x/= rxr.
  rewrite /xlnx.
  have -> : 0 < x = false.
    apply/negbTE.
    rewrite -leNgt.
    rewrite -(addr0 x) -{1}(subrr r) addrA addrAC.
    apply (@le_trans _ _ ((x + - r) - `| x + - r |)).
      by rewrite lerD2l lerNr distrC ltW.
    by rewrite subr_le0 ler_norm.
  have -> : (0 < r) = false.
    by apply/negbTE; rewrite -leNgt; apply/ltW.
  by rewrite subrr normr0 ltW.
- exists (expR (- 2 / eps)); first by rewrite expR_gt0.
  move=> x/=; rewrite sub0r normrN => Hx2.
  rewrite /xlnx ltxx sub0r normrN.
  case: ifPn => Hcase; last by rewrite normr0 ltW.
  rewrite (ger0_norm (ltW Hcase)) in Hx2.
  rewrite -{1}(lnK Hcase).
  set X := ln x.
  have X_neg : X < 0.
    apply (@lt_trans _ _ (-2 / eps)).
      by rewrite -ltr_expR lnK.
    by rewrite mulNr ltrNl oppr0 divr_gt0//.
  apply/ltW.
  apply: (@lt_le_trans _ _ (2 / (- X))).
  + rewrite ltr0_norm; last first.
      by rewrite /xlnx_total pmulr_rlt0 ?expR_gt0 ?lnK.
    rewrite -mulrN.
    rewrite -(@ltr_pM2r _ ((- X)^-1)); last first.
      by rewrite invr_gt0 ltrNr oppr0.
    rewrite lnK// -mulrA divff ?mulr1; last first.
      by rewrite oppr_eq0 lt_eqF.
    rewrite -(invrK 2) -mulrA.
    rewrite invrN mulNr (mulrN (X^-1)) opprK -invfM -expr2 invrK.
    rewrite (_ : 2 = 2`!%:R)//.
    have := @exp_strict_lb _ 2 (- X).
    rewrite ltrNr oppr0 => /(_ X_neg).
    rewrite expRN.
    rewrite -[X in X < _ -> _]invrK.
    rewrite ltf_pV2 ?posrE ?expR_gt0 ?invr_gt0 ?mulr_gt0//=; last 3 first.
      by rewrite ltrNr oppr0.
      by rewrite ltrNr oppr0.
      by rewrite invr_gt0.
    by rewrite lnK// sqrrN invf_div.
  + move: Hx2.
    rewrite -ltr_ln ?posrE ?expR_gt0//.
    rewrite -/X.
    rewrite expRK.
    rewrite mulNr ltrNr.
    rewrite ltr_pdivrMr//.
    by rewrite -ltr_pdivrMl 1?ltrNr ?oppr0// mulrC => /ltW.
Qed.

Lemma derivable_xlnx x : 0 < x -> derivable xlnx x 1.
Proof.
move=> x0; rewrite (near_eq_derivable _ xlnx_total)//.
- exact: derivable_xlnx_total.
- by rewrite oner_eq0.
- near=> z.
  rewrite /xlnx ifT//.
  near: z.
  exact: gt0_near_nbhs.
Unshelve. all: by end_near. Qed.

Lemma derive_xlnxE x : 0 < x -> 'D_1 xlnx x = ln x + 1.
Proof.
move=> x_pos.
rewrite /xlnx.
transitivity ('D_1 (fun x0 : R^o => x0 * exp.ln x0) x).
  apply: near_eq_derive.
    by rewrite oner_eq0.
  near=> z.
  rewrite ifT//.
  near: z.
  exact: gt0_near_nbhs.
rewrite deriveM//=; last exact: derivable_ln.
rewrite derive_val addrC; congr +%R.
  by rewrite /GRing.scale/= mulr1.
rewrite (@derive_val _ _ _ _ _ _ _ (exp.is_derive1_ln x_pos)).
by rewrite -(@mulfV _ x)// gt_eqF.
Unshelve. all: by end_near. Qed.

(*
Lemma pderivable_Ropp_xlnx : pderivable (fun y => - xlnx y) (fun x => 0 < x <= exp (- 1)).
Proof.
move=> x /= Hx.
apply derivable_pt_opp.
apply derivable_pt_xlnx.
apply Hx.
Defined.

Lemma xlnx_sdecreasing_0_Rinv_e_helper : forall (t : R) (Ht : 0 < t <= exp (-1)),
  0 < (if t == exp (-1) then 1 else derive_pt (fun x => - xlnx x) t (pderivable_Ropp_xlnx Ht)).
Proof.
move=> t [t0 te]; case: ifPn => [//|] /eqP Hcase.
rewrite derive_pt_opp derive_pt_xlnx //.
rewrite ltR_oppr oppR0 addRC -ltR_subRL sub0R.
apply exp_lt_inv; by rewrite exp_ln // ltR_neqAle.
Qed.
*)

Lemma xlnx_sdecreasing_0_Rinv_e x y :
  0 <= x <= expR (-1) ->
  0 <= y <= expR (-1) -> x < y -> xlnx y < xlnx x.
Proof.
move=> /andP[x1 x2] /andP[y1 y2] xy.
case/boolP : (x == 0) => [/eqP ->|x0].
- rewrite xlnx_0; apply xlnx_neg.
  rewrite (le_lt_trans x1 xy)/=.
  rewrite (le_lt_trans y2)//.
  by rewrite exp.expR_lt1// ltrN10.
- rewrite -[X in _ < X]opprK ltrNr.
  have {}x0 : 0 < x.
    by rewrite lt_neqAle eq_sym x0 x1.
  have {x1 y1}y0 : 0 < y.
    by rewrite (le_lt_trans x1).
  apply: (@derivable1_mono _ (BRight 0) (BRight (expR (-1))) (fun x => - xlnx x)) => //.
  + by rewrite in_itv//= (x0).
  + by rewrite in_itv//= (y0).
  + move=> /= z.
    rewrite in_itv/= => /andP[z0 z1].
    apply: derivableN.
    by apply: derivable_xlnx => //.
  + move=> /= t.
    rewrite in_itv/= => /andP[tx ty].
    rewrite [ltRHS](_ : _ = 'D_1 (fun x : R => - (x * exp.ln x)) t); last first.
      apply: near_eq_derive.
        by rewrite oner_eq0.
      near=> z.
      rewrite /xlnx.
      case: ifPn => z0 //.
      rewrite oppr0.
      by rewrite exp.ln0 ?mulr0// ?oppr0// leNgt.
    rewrite deriveN; last first.
      apply: derivableM => //.
      apply: ex_derive.
      apply: exp.is_derive1_ln.
      by rewrite (lt_trans _ tx).
    rewrite ltrNr oppr0.
    rewrite deriveM//; last first.
      apply: ex_derive.
      apply: exp.is_derive1_ln.
      by rewrite (lt_trans _ tx).
    have := exp.is_derive1_ln (lt_trans x0 tx).
    move/(@derive_val R R^o R^o) => ->.
    rewrite derive_id [X in X + _]mulfV ?gt_eqF//; last by rewrite (lt_trans x0).
    rewrite (@lt_le_trans _ _ (1 + exp.ln y))//.
      rewrite ltrD2l.
      rewrite /GRing.scale/= mulr1.
      by rewrite exp.ltr_ln ?posrE ?(lt_trans x0)// ltW.
    rewrite (@le_trans _ _ (1 + exp.ln (expR (-1))))//.
      by rewrite lerD2l exp.ler_ln ?posrE// exp.expR_gt0.
      by rewrite exp.expRK subrr.
Unshelve. all: by end_near. Qed.

Lemma xlnx_decreasing_0_Rinv_e x y :
  0 <= x <= expR (-1) -> 0 <= y <= expR (-1) -> x <= y -> xlnx y <= xlnx x.
Proof.
move=> Hx Hy Hxy.
case/boolP : (x == y) => [/eqP ->|/eqP H].
  by rewrite lexx.
apply/ltW/xlnx_sdecreasing_0_Rinv_e => //.
rewrite lt_neqAle Hxy andbT.
exact/eqP.
Qed.

End xlnx.

Section diff_xlnx.
Context {R : realType}.

Definition diff_xlnx (x : R) := xlnx (1 - x) - xlnx x.

Lemma derivable_pt_diff_xlnx x : 0 < x < 1 -> derivable diff_xlnx x 1.
Proof.
move=> /andP[x0 x1].
apply: derivableB.
  apply/derivable1_diffP.
  have := (@differentiable_comp _ _ _ _ (fun t : R^o => 1 - t)%R
    (xlnx: R^o -> R^o)).
  apply => //.
  apply/derivable1_diffP.
  apply: derivable_xlnx.
  by rewrite subr_gt0.
exact: derivable_xlnx.
Qed.

Lemma derive_pt_diff_xlnx x : 0 < x < 1 ->
  derivable diff_xlnx x 1 ->
  'D_1 diff_xlnx x = -(2 + exp.ln (x * (1-x))).
Proof.
move=> /andP[] x0 x1 H.
rewrite deriveB/=; last 2 first.
  (* TODO: copy past *)
  apply/derivable1_diffP.
  have := (@differentiable_comp _ _ _ _ (fun t : R^o => 1 - t)%R xlnx).
  apply => //.
  apply/derivable1_diffP.
  apply: derivable_xlnx.
  by rewrite subr_gt0.
  exact: derivable_xlnx.
rewrite -derive1E derive1_comp; last 2 first.
  apply: derivableB.
    exact: derivable_cst.
  exact: derivable_id.
  apply: derivable_xlnx.
  by rewrite subr_gt0.
rewrite derive_xlnxE//.
rewrite [X in X * _]derive1E.
rewrite derive_xlnxE; last by rewrite subr_gt0.
rewrite derive1E deriveB; last 2 first.
  exact: derivable_cst.
  exact: derivable_id.
rewrite derive_cst derive_id sub0r mulrN1 -opprB; congr (- _).
rewrite opprK addrACA addrC; congr +%R.
by rewrite lnM// posrE subr_gt0.
Qed.

Lemma diff_xlnx_0 : diff_xlnx 0 = 0.
Proof. by rewrite /diff_xlnx subr0 xlnx_0 xlnx_1 subrr. Qed.

(*
Lemma diff_xlnx_1 : diff_xlnx 1 = 0.
Proof. by rewrite /diff_xlnx subRR xlnx_0 xlnx_1 subRR. Qed.
*)

Lemma derive_diff_xlnx_gt0 x : 0 < x < 1 -> x < expR (-2) -> 0 < 'D_1 diff_xlnx x.
Proof.
move=> /andP[x0 x1] xltexp2.
rewrite derive_pt_diff_xlnx; last 2 first.
  by rewrite x0.
  apply: derivable_pt_diff_xlnx.
  by rewrite x0.
rewrite ltrNr oppr0.
rewrite -[X in X + _]opprK addrC.
rewrite subr_lt0.
rewrite -ltr_expR lnK; last first.
  by rewrite posrE mulr_gt0// subr_gt0.
apply: (@lt_trans _ _ (expR (-2) * (1 - x))).
  by rewrite ltr_pM2r ?subr_gt0.
rewrite -[ltRHS]mulr1.
rewrite ltr_pM2l ?expR_gt0//.
by rewrite ltrBlDl addrC -ltrBlDl subrr.
Qed.

Lemma diff_xlnx_sincreasing_0_Rinv_e2 (x y : R) :
  0 <= x <= expR (-2) -> 0 <= y <= expR (-2) ->
  x < y -> diff_xlnx x < diff_xlnx y.
Proof.
move=> /andP[x0 x2] /andP[y0 y2] xy.
apply (@derive_sincreasing_interv R 0 (expR (-2))) => //.
- move=> x' /= /andP[Hx1 Hx2].
  apply derivable_pt_diff_xlnx.
  apply/andP; split => //.
  by rewrite (lt_le_trans Hx2)// -[leRHS]exp.expR0 exp.ler_expR lerNl oppr0.
- move=> x' /= /andP[Hx1 Hx2].
  rewrite /diff_xlnx.
  apply: cvgB => //.
    apply: cvg_comp; last exact: continuous_at_xlnx.
    apply: cvgB => //.
    exact: cvg_cst.
  by apply: continuous_at_xlnx.
- by rewrite exp.expR_gt0.
- move=> x' /= /andP[Hx1 Hx2] K.
  rewrite derive_diff_xlnx_gt0//.
  rewrite Hx1/=.
  rewrite (lt_le_trans Hx2)//.
  by rewrite -[leRHS]exp.expR0 exp.ler_expR lerNl oppr0.
- by rewrite x0.
- by rewrite y0.
Qed.

Lemma xlnx_ineq (x : R) : 0 <= x <= expR (-2) -> xlnx x <= xlnx (1-x).
Proof.
move=> /andP[Hx1 Hx2].
rewrite -subr_ge0.
rewrite -diff_xlnx_0 -/(diff_xlnx x).
case/boolP : (0 == x) => [/eqP ->|/eqP xnot0].
  by rewrite lexx.
apply/ltW/diff_xlnx_sincreasing_0_Rinv_e2 => //.
  by rewrite lexx exp.expR_ge0.
  by rewrite Hx1 Hx2.
rewrite lt_neqAle Hx1 andbT.
exact/eqP.
Qed.

End diff_xlnx.

Section Rabs_xlnx.
Context {R : realType}.

Definition xlnx_delta a (x : R) := xlnx (x + a) - xlnx x.

Lemma derivable_xlnx_delta (eps : R) (Heps : 0 < eps < 1) x (Hx : 0 < x < 1 - eps) :
  derivable (xlnx_delta eps) x 1.
Proof.
rewrite /xlnx_delta.
apply: derivableB => /=.
  apply/derivable1_diffP/differentiable_comp => //.
  apply/derivable1_diffP.
  apply: derivable_xlnx.
  move: Heps Hx => /andP[? _] /andP[? _].
  by rewrite addr_gt0.
apply: derivable_xlnx.
by case/andP : Hx.
Qed.

Lemma derive_pt_xlnx_delta eps (Heps : 0 < eps < 1) x (Hx : 0 < x < 1 - eps) :
  'D_1 (xlnx_delta eps) x = ln (x + eps) - ln x.
Proof.
rewrite deriveB//=; last 2 first.
  apply/derivable1_diffP/differentiable_comp => //.
  apply/derivable1_diffP.
  apply: derivable_xlnx.
  rewrite addr_gt0//.
  by case/andP: Hx.
  by case/andP: Heps.
  apply: derivable_xlnx.
  by case/andP : Hx.
rewrite derive_xlnxE; last first.
  by case/andP: Hx.
rewrite -derive1E.
rewrite derive1_comp//; last first.
  apply: derivable_xlnx.
  rewrite addr_gt0//.
  by case/andP: Hx.
  by case/andP: Heps.
rewrite derive1E derive_xlnxE; last first.
  rewrite addr_gt0//.
  by case/andP: Hx.
  by case/andP: Heps.
rewrite derive1E.
rewrite deriveD//.
rewrite derive_id derive_cst addr0 mulr1.
by rewrite opprD addrACA subrr addr0.
Qed.

Lemma increasing_xlnx_delta eps (Heps : 0< eps < 1) :
  forall x y : R, 0 <= x <= 1 - eps -> 0 <= y <= 1 - eps -> x < y ->
                  xlnx_delta eps x < xlnx_delta eps y.
Proof.
move=> x y /andP[x0 x1] /andP[y0 y1] xy.
apply (@derive_sincreasing_interv R 0 (1 - eps)) => //=.
- move=> z /andP[z0 z1].
  apply: derivable_xlnx_delta => //.
  by rewrite z0.
- move=> z /andP[z0 z1].
  apply: cvgB.
    apply: cvg_comp; last first.
      exact: continuous_at_xlnx.
    apply: cvgD.
      exact: cvg_id.
    exact: cvg_cst.
  exact: continuous_at_xlnx.
- rewrite subr_gt0.
  by case/andP : Heps.
- move=> t /andP[t0 t1] H.
  rewrite derive_pt_xlnx_delta//.
    rewrite subr_gt0 ltr_ln ?posrE//.
    rewrite ltrDl.
    by case/andP: Heps.
    rewrite addr_gt0//.
    by case/andP: Heps.
    by rewrite t0/=.
- by rewrite x0.
- by rewrite y0.
Qed.

Lemma xlnx_delta_bound eps : 0 < eps <= expR (-2) ->
  forall x, 0 <= x <= 1 - eps -> `| xlnx_delta eps x | <= - xlnx eps.
Proof.
move=> /andP[Heps1 Heps2] x /andP[Hx1 Hx2].
rewrite ler_norml; apply/andP; split.
- rewrite opprK (_ : xlnx eps = xlnx_delta eps 0); last first.
    by rewrite /xlnx_delta add0r xlnx_0 subr0.
  have [->|xnot0] := eqVneq x 0; first by rewrite lexx.
  apply/ltW/increasing_xlnx_delta => //.
  + rewrite Heps1/=.
    by rewrite (le_lt_trans Heps2)// exp.expR_lt1// ltrNl oppr0//.
  + rewrite lexx/= subr_ge0.
    rewrite (le_trans Heps2)//.
    by rewrite ltW// exp.expR_lt1// ltrNl oppr0//.
  + by rewrite Hx1.
  + by rewrite lt_neqAle eq_sym xnot0.
- apply: (@le_trans _ _ (xlnx_delta eps (1 - eps))).
    have [->|xnot0] := eqVneq x (1 - eps); first by rewrite lexx.
    apply/ltW/increasing_xlnx_delta => //.
    + rewrite Heps1/=.
      by rewrite (le_lt_trans Heps2)// exp.expR_lt1// ltrNl oppr0//.
    + by rewrite Hx1.
    + rewrite lexx andbT subr_ge0.
      rewrite (le_trans Heps2)//.
      by rewrite ltW// exp.expR_lt1// ltrNl oppr0//.
    + by rewrite lt_neqAle xnot0/=.
  rewrite /xlnx_delta subrK xlnx_1 sub0r lerNr opprK.
  apply: xlnx_ineq.
  by rewrite (ltW Heps1)/=.
Qed.

Lemma Rabs_xlnx (a : R) (Ha : 0 <= a <= expR (-2)) x y :
  0 <= x <= 1 -> 0 <= y <= 1 -> `| x - y | <= a ->
  `| xlnx x - xlnx y | <= - xlnx a.
Proof.
move=> /andP[Hx1 Hx2] /andP[Hy1 Hy2] H.
have [Hcase|Hcase|Hcase] := ltgtP x y.
- have Haux : y = x + `| x - y |.
    by rewrite distrC gtr0_norm ?subr_gt0 // addrC subrK.
  rewrite Haux -normrN opprD opprK addrC.
  apply (@le_trans _ _ (- xlnx `| x - y |)).
    apply xlnx_delta_bound.
    - apply/andP; split.
      - by rewrite distrC gtr0_norm ?subr_gt0.
      - apply (@le_trans _ _ a) => //.
        by case/andP: Ha.
    - by rewrite Hx1/= lerBrDr -Haux.
  rewrite lerNr opprK.
  apply xlnx_decreasing_0_Rinv_e => //.
  - apply/andP; split; first exact: normr_ge0.
    apply (@le_trans _ _ a) => //.
    apply (@le_trans _ _ (expR (- 2))).
      by case/andP: Ha.
    by rewrite exp.ler_expR// lerN2 ler1n.
  - apply/andP; split.
      by case/andP : Ha.
    case/andP : Ha => Ha /le_trans; apply.
    by rewrite exp.ler_expR// lerN2 ler1n.
- have Haux : x = y + `| x - y |.
    by rewrite gtr0_norm ?subr_gt0// addrCA subrr addr0.
  rewrite distrC in H Haux.
  rewrite Haux.
  apply (@le_trans _ _ (- xlnx `| y - x |)).
    apply xlnx_delta_bound.
    - apply/andP; split.
      - by rewrite distrC gtr0_norm ?subr_gt0.
      - rewrite (le_trans H)//.
        by case/andP : Ha.
    - by rewrite Hy1/= lerBrDr -Haux.
  rewrite lerNr opprK.
  apply xlnx_decreasing_0_Rinv_e => //.
    - apply/andP; split.
      - by rewrite ltr0_norm ?subr_lt0// opprB subr_ge0 ltW.
      - rewrite (le_trans H)//.
        case/andP : Ha => _ /le_trans; apply.
        by rewrite exp.ler_expR lerN2 ler1n.
    - apply/andP; split.
        by case/andP : Ha.
      case/andP : Ha => _ /le_trans; apply.
      by rewrite exp.ler_expR lerN2 ler1n.
- subst x ; rewrite subrr normr0 lerNr oppr0.
  case/orP : (orbN (0 == a)); last move=> anot0.
    move=> /eqP <-; rewrite xlnx_0.
    by rewrite lexx.
  apply/ltW/xlnx_neg; apply/andP; split.
  - rewrite lt_neqAle anot0/=.
    by case/andP : Ha.
  - case/andP : Ha => _ /le_lt_trans; apply.
    by rewrite exp.expR_lt1 ltrNl oppr0 ltr0n.
Qed.

End Rabs_xlnx.

End xlnx_sect.

Section log_concave.

(* TODO: commented out to make it compile, to use Rabs_xlnx
Lemma pderivable_log a x1 : 0 <= a -> pderivable log (fun x2 : R => a < x2 < x1).
Proof.
move=> a0; rewrite /pderivable => x Hx.
rewrite /log /Log (_ : (fun x0 => ln x0 / ln 2) =
  (mult_real_fct (/ ln 2) (fun x0 => ln x0))); last first.
  by rewrite boolp.funeqE => x0; rewrite /mult_real_fct mulRC.
apply/derivable_pt_scal/derivable_pt_ln/(leR_ltR_trans a0); by case: Hx.
Qed.*)

(* TODO: commented out to make it compile, to use Rabs_xlnx
Lemma ln_concave_at_gt0 x y (t : {prob R}) : x < y ->
  0 < x -> 0 < y -> concave_function_at ln x y t.
Proof.
move=> xy x0 y0; apply RNconcave_function_at.
set Df := fun x => - / x.
move: t.
have HDf : pderivable (fun x => - ln x) (fun x0 => x <= x0 <= y).
  rewrite (_ : (fun x => - ln x) = comp Ropp ln); last by rewrite boolp.funeqE.
  move=> r xry; apply derivable_pt_comp; last exact: derivable_pt_Ropp.
  apply/derivable_pt_ln/(@ltR_leR_trans x) => //; by case: xry.
set DDf := fun x => / x^2.
have HDDf : pderivable Df (fun x0 : R => x <= x0 <= y).
  rewrite /Df (_ : (fun x => - / x) = comp Ropp Rinv); last first.
    by rewrite boolp.funeqE.
  move=> r xry; apply derivable_pt_comp; last exact/derivable_pt_Ropp.
  rewrite (_ : Rinv = inv_fct (fun x => x)); last by rewrite boolp.funeqE.
  apply derivable_pt_inv; last exact: derivable_pt_id.
  by apply/eqP/gtR_eqF/(@ltR_leR_trans x) => //; case: xry.
apply: (@second_derivative_convexf_pt _ _ _ HDf Df _ HDDf DDf) => //.
- move=> r xry; rewrite /Df.
  have r0 : 0 < r by apply (@ltR_leR_trans x) => //; case: xry.
  transitivity (derive_pt (comp Ropp ln) _
    (derivable_pt_comp ln Ropp _ (derivable_pt_ln r0) (derivable_pt_Ropp _))).
    by rewrite derive_pt_comp /= mulN1R.
  exact: proof_derive_irrelevance.
- move=> r xry; rewrite /DDf /Df.
  have /eqP r0 : r != 0 by apply/gtR_eqF/(@ltR_leR_trans x) => //; case: xry.
  transitivity (derive_pt (comp Ropp Rinv) _
    (derivable_pt_comp Rinv Ropp _
      (derivable_pt_inv _ _ r0 (derivable_pt_id _)) (derivable_pt_Ropp _))).
    rewrite derive_pt_comp [in RHS]/= derive_pt_inv derive_pt_id mulN1R.
    by rewrite /Rdiv mulNR oppRK mul1R Rsqr_pow2 (* TODO: rename? *).
  exact/proof_derive_irrelevance.
- move=> r; rewrite /DDf => -[x11 x12].
  rewrite -expRV; last by apply/gtR_eqF/(@ltR_leR_trans x).
  exact/expR_ge0/ltRW/invR_gt0/(@ltR_leR_trans x).
Qed.
*)

(*
Lemma log_concave_at_gt0W x y (t : {prob R}) : x < y ->
  0 < x -> 0 < y -> concave_function_at log x y t.
Proof.
move=> xy x0 y0; rewrite /log /Log.
apply concave_function_atN; [exact: ln_concave_at_gt0 | exact/ltRW/invR_gt0/ln2_gt0].
Qed.

Lemma log_concave_at_gt0 x y (t : {prob R}) : 0 < x -> 0 < y -> concave_function_at log x y t.
Proof.
move=> x0 y0.
case/boolP : (x < y)%mcR => [/RltP xy|].
  exact: log_concave_at_gt0W.
rewrite -leNgt le_eqVlt => /predU1P[->|yx].
  exact: concave_function_atxx.
rewrite (probK t); apply: concavef_at_onem => //.
  exact/RltP.
by apply: log_concave_at_gt0W => //; exact/RltP.
Qed.

Lemma log_concave : concave_function_in Rpos_interval log.
Proof.
move=> x y t; rewrite !classical_sets.in_setE(*TODO: import?*) => Hx Hy.
exact: log_concave_at_gt0.
Qed.
*)

End log_concave.
