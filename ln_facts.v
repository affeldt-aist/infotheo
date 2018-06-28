(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div fintype tuple finfun bigop.
Require Import Reals Fourier.
Require Import ssrR Reals_ext Ranalysis_ext logb.

(** * Some Results about the Analysis of ln *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section ln_id_sect.

Definition ln_id x := ln x - (x - 1).

Lemma pderivable_ln_id_xle1 : pderivable ln_id (fun x => 0 < x <= 1).
Proof.
rewrite /pderivable => x Hx.
rewrite /ln_id.
apply derivable_pt_plus.
- apply derivable_pt_ln, Hx.
- apply derivable_pt_opp, derivable_pt_minus ; [apply derivable_pt_id | apply derivable_pt_cst].
Defined.

Definition ln_id' x (H : 0 < x <= 1) := derive_pt ln_id x (pderivable_ln_id_xle1 H).

Lemma derive_pt_ln_id_xle1 : forall x (Hx : 0 < x <= 1), (/ x) - 1 = ln_id' Hx.
Proof.
move=> y Hy.
rewrite /ln_id' /pderivable_ln_id_xle1 /ln_id.
rewrite derive_pt_plus derive_pt_opp derive_pt_ln derive_pt_minus derive_pt_id derive_pt_cst.
rewrite subR0.
reflexivity.
Defined.

Lemma derive_pt_ln_id_xle1_ge0 x (Hx : 0 < x <= 1) : 0 < if x==1 then 1 else ln_id' Hx.
Proof.
case/boolP : (x == 1) => Hcase ; first by fourier.
rewrite -derive_pt_ln_id_xle1; apply/subR_gt0.
rewrite -invR1; apply ltR_inv => //; first by case: Hx.
case (Rle_lt_or_eq_dec x 1) ; [apply Hx | by [] | ].
move/eqP in Hcase ; move => Habs.
rewrite Habs in Hcase ; by contradict Hcase.
Defined.

Lemma ln_idlt0_xlt1 : forall x, 0 < x < 1 -> ln_id x < 0.
Proof.
rewrite {2}(_ : 0 = ln_id 1); last by rewrite /ln_id ln_1 2!subRR.
move=> x Hx.
have lt01 : 0 < 1 by fourier.
apply (derive_increasing_ad_hoc lt01 derive_pt_ln_id_xle1_ge0).
- by split; [apply Hx | apply ltRW, Hx].
- split; by fourier.
- by apply Hx.
Qed.

Lemma ln_idlt0_xgt1 x : 0 < x -> 1 < x -> ln_id x < 0.
Proof.
move=> x0 x1.
rewrite /ln_id; apply/subR_lt0/exp_lt_inv.
rewrite (exp_ln _ x0) -{1}(addR0 x) -(subRR 1) addRCA.
exact/exp_ineq1/subR_gt0.
Qed.

Lemma ln_idgt0 x : 0 < x -> ln_id x <= 0.
Proof.
move=> Hx.
case (total_order_T x 1).
- case => Hx2; first exact/ltRW/ln_idlt0_xlt1.
  + subst x; rewrite /ln_id ln_1 2!subRR; exact/leRR.
- move=> Hx2; apply/ltRW/ln_idlt0_xgt1; by [apply Hx | apply Rgt_lt, Hx2].
Qed.

Lemma ln_id_cmp x : 0 < x -> ln x <= x - 1.
Proof. move=> Hx ; apply Rminus_le ; apply ln_idgt0 ; exact Hx. Qed.

Lemma log_id_cmp x : 0 < x -> log x <= (x - 1) * log (exp 1).
Proof.
move=> Hx; rewrite logexp1E; apply leR_wpmul2r;
  [exact/ltRW/invR_gt0 | exact/ln_id_cmp].
Qed.

Lemma ln_id_eq x : 0 < x -> ln x = x - 1 -> x = 1.
Proof.
move=> Hx' Hx.
case (total_order_T x 1) => [ [] // Hx2 | Hx2]; contradict Hx.
- apply/ltR_eqF; rewrite -subR_lt0.
  apply ln_idlt0_xlt1; split; [exact Hx' | exact Hx2].
- apply/ltR_eqF; rewrite -subR_lt0; exact: ln_idlt0_xgt1.
Qed.

Lemma log_id_eq x : 0 < x -> log x = (x - 1) * log (exp 1) -> x = 1.
Proof.
move=> Hx'; rewrite logexp1E.
rewrite eqR_mul2r; last exact/nesym/ltR_eqF/invR_gt0.
apply ln_id_eq; by [apply Hx' | apply Hx].
Qed.

End ln_id_sect.

Section xlnx_sect.

Section xlnx.

Definition xlnx := fun x => if 0 <b x then x * ln x else 0.

Lemma xlnx_0 : xlnx 0 = 0.
Proof. rewrite /xlnx mul0R; by case : ifP. Qed.

Lemma xlnx_1 : xlnx 1 = 0.
Proof. rewrite /xlnx ln_1 mulR0 ; by case : ifP. Qed.

Lemma xlnx_neg x : 0 < x < 1 -> xlnx x < 0.
Proof.
case => lt0x ltx1.
rewrite /xlnx.
have -> : 0 <b x ; first by apply/ltRP.
rewrite -(oppRK 0) ltR_oppr oppR0 -mulRN.
apply mulR_gt0 => //.
rewrite ltR_oppr oppR0.
apply exp_lt_inv.
by rewrite exp_ln // exp_0.
Qed.

Lemma continue_xlnx : continuity xlnx.
Proof.
rewrite /continuity => r.
rewrite /continuity_pt /continue_in /limit1_in /limit_in => eps eps_pos /=.
case (total_order_T 0 r) ; first case ; move=> Hcase.
- have : continuity_pt (fun x => x * ln x) r.
    apply continuity_pt_mult.
      by apply derivable_continuous_pt, derivable_id.
    by apply derivable_continuous_pt, derivable_pt_ln.
  rewrite /continuity_pt /continue_in /limit1_in /limit_in => /(_ eps eps_pos).
  case => /= k [k_pos Hk].
  exists (Rmin k r); split; first exact/Rlt_gt/Rmin_pos.
  - move=> x ; rewrite /D_x ; move => [[_ Hx1] Hx2].
    rewrite /xlnx.
    have -> : 0 <b x.
      apply/ltRP.
      rewrite -(addR0 x) -{2}(subRR r) addRA addRAC.
      apply (@leR_ltR_trans ((x + - r) + `| x + - r |)).
        rewrite addRC -leR_subl_addr sub0R -normRN; exact: Rle_abs.
      rewrite /R_dist in Hx2.
      apply/ltR_add2l/(@ltR_leR_trans (Rmin k r)) => //; exact: geR_minr.
    have -> : 0 <b r by apply/ltRP.
    apply Hk.
    split => //.
    exact/(ltR_leR_trans Hx2)/geR_minl.
- subst r.
  exists (exp (- 2 * / eps)).
  split ; first exact: exp_pos.
  move=> x; rewrite /R_dist subR0; case=> Hx1 Hx2.
  rewrite /xlnx ltRR'.
  case: ifPn => Hcase; move/ltRP in Hcase.
  + rewrite (geR0_norm _ (ltRW Hcase)) in Hx2.
    rewrite subR0 -{1}(exp_ln _ Hcase).
    set X := ln x.
    have X_neg : X < 0.
      apply (@ltR_trans (-2 * / eps)).
      by apply exp_lt_inv; subst X; rewrite exp_ln.
      rewrite mulNR.
      exact/oppR_lt0/Rlt_mult_inv_pos.
    apply: (@ltR_leR_trans (2 * / (- X))).
    * rewrite ltR0_norm; last first.
        rewrite -(mulR0 (exp X)) ltR_pmul2l => //; exact: exp_pos.
      rewrite -mulRN.
      apply (@ltR_pmul2r (/ - X)); first exact/invR_gt0/oppR_gt0.
      rewrite -mulRA mulRV ?mulR1; last by rewrite oppR_eq0; apply/eqP/ltR_eqF.
      rewrite -(invRK 2) //.
      rewrite -mulRA ( _ : forall r, r * r = r ^ 2); last by move=> ?; rewrite /pow mulR1.
      rewrite expRV; last exact/eqP/not_eq_sym/ltR_eqF/oppR_gt0.
      rewrite -invRM; last 2 first.
        apply/eqP; rewrite invR_neq0 //; exact/eqP/gtR_eqF.
        apply/eqP; rewrite pow_eq0 oppR_eq0; exact/eqP/ltR_eqF.
      rewrite -(invRK (exp X)); last exact/gtR_eqF/exp_pos.
      apply ltR_inv => //.
        exact/invR_gt0/exp_pos.
        apply/mulR_gt0; first fourier.
        apply pow_gt0; by fourier.
        rewrite -exp_Ropp mulRC (_ : 2 = INR 2`!) //.
        exact/exp_strict_lb/oppR_gt0.
    * apply (@leR_pmul2r (/ 2)); first exact/invR_gt0.
      rewrite mulRC mulRA mulVR ?mul1R //; last exact/eqP/gtR_eqF.
      rewrite -(invRK eps); last exact/gtR_eqF.
      rewrite -invRM //; last exact/gtR_eqF/invR_gt0.
      apply leR_inv => //.
      - apply/mulR_gt0 => //; exact: invR_gt0.
      - rewrite leR_oppr mulRC -mulNR.
        apply/exp_le_inv/ltRW; subst X; by rewrite exp_ln.
  + by rewrite subRR normR0.
- exists (- r); split; first exact: oppR_gt0.
  move=> x [[_ Hx1] Hx2].
  rewrite /R_dist /xlnx.
  have -> : 0 <b x = false.
    apply/ltRP/leRNgt.
    rewrite -(addR0 x) -{1}(subRR r) addRA addRAC.
    apply (@leR_trans ((x + - r) - `| x + - r |)).
      apply/leR_add2l/ltRW; by rewrite ltR_oppr.
    exact/Rle_minus/Rle_abs.
  have -> : 0 <b r = false by apply/negbTE; rewrite -leRNgt'; apply/leRP/ltRW.
  by rewrite subRR normR0.
Qed.

(* TODO: not used *)
Lemma uniformly_continue_xlnx : uniform_continuity xlnx (fun x => 0 <= x <= 1).
Proof.
apply Heine ; first by apply compact_P3.
move=> x _ ; by apply continue_xlnx.
Qed.

Let xlnx_total := fun y => y * ln y.

Lemma derivable_xlnx_total x : 0 < x -> derivable_pt xlnx_total x.
Proof.
move=> x_pos.
apply derivable_pt_mult.
  by apply derivable_id.
by apply derivable_pt_ln.
Defined.

Lemma xlnx_total_xlnx x : 0 < x -> xlnx x = xlnx_total x.
Proof. by rewrite /xlnx /f => /ltRP ->. Qed.

Lemma derivable_pt_xlnx x (x_pos : 0 < x) : derivable_pt xlnx x.
Proof. apply (@derivable_f_eq_g _ _ x 0 xlnx_total_xlnx x_pos (derivable_xlnx_total x_pos)). Defined.

Lemma derive_xlnx_aux1 x (x_pos : 0 < x) :
  derive_pt xlnx x (derivable_pt_xlnx x_pos) =
  derive_pt xlnx_total x (derivable_xlnx_total x_pos).
Proof. by rewrite -derive_pt_f_eq_g. Qed.

Lemma derive_xlnx_aux2 x (x_pos : 0 < x) : derive_pt xlnx x (derivable_pt_xlnx x_pos) = ln x + 1.
Proof.
rewrite derive_xlnx_aux1 /f derive_pt_mult derive_pt_ln.
rewrite mulRV; last exact/eqP/gtR_eqF.
rewrite (_ : derive_pt ssrfun.id x (derivable_id x) = 1) ; first by rewrite mul1R.
rewrite -(derive_pt_id x).
by apply proof_derive_irrelevance.
Qed.

Lemma derive_pt_xlnx x (x_pos : 0 < x) (pr : derivable_pt xlnx x) : derive_pt xlnx x pr = ln x + 1.
Proof. rewrite -derive_xlnx_aux2 ; by apply proof_derive_irrelevance. Qed.

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
move=> t [Ht1 Ht2].
case : ifP => [//|/negbT] Hcase.
rewrite derive_pt_opp derive_pt_xlnx //.
rewrite ltR_oppr oppR0 addRC -ltR_subRL sub0R.
apply exp_lt_inv.
rewrite exp_ln //.
apply/ltRP; rewrite ltR_neqAle Hcase; exact/leRP.
Qed.

Lemma xlnx_sdecreasing_0_Rinv_e x y :
  0 <= x <= exp (-1) -> 0 <= y <= exp (-1) -> x < y -> xlnx y < xlnx x.
Proof.
move=> [x1 x2] [y1 y2] xy.
case/boolP : (x == 0) => [/eqP ->|x0].
- rewrite xlnx_0; apply xlnx_neg.
  exact: (conj (@leR_ltR_trans x _ _ _ _) (leR_ltR_trans y2 ltRinve1)).
- rewrite -[X in _ < X]oppRK ltR_oppr.
  have {x0}x0 : 0 < x by apply/ltRP; rewrite lt0R x0; exact/leRP.
  have {x1 y1}y0 : 0 < y by exact: (@ltR_trans x).
  exact: (derive_increasing_ad_hoc (exp_pos _) xlnx_sdecreasing_0_Rinv_e_helper).
Qed.

Lemma xlnx_decreasing_0_Rinv_e x y :
  0 <= x <= exp (-1) -> 0 <= y <= exp (-1) -> x <= y -> xlnx y <= xlnx x.
Proof.
move=> Hx Hy Hxy.
case/boolP : (x == y) => [/eqP ->|H]; first exact/leRR.
- apply/ltRW/xlnx_sdecreasing_0_Rinv_e => //.
  apply/ltRP; rewrite ltR_neqAle H; exact/leRP.
Qed.

End xlnx.

Section diff_xlnx.

Definition diff_xlnx := fun x => xlnx (1 - x) - xlnx x.

Lemma derivable_pt_diff_xlnx x (Hx : 0 < x < 1) : derivable_pt diff_xlnx x.
Proof.
rewrite /diff_xlnx.
apply derivable_pt_plus ; last by apply derivable_pt_opp, derivable_pt_xlnx, Hx.
apply (derivable_pt_comp (fun x => 1 + - x) xlnx).
  apply derivable_pt_plus ; first by apply derivable_pt_const.
  apply derivable_pt_Ropp.
apply derivable_pt_xlnx.
rewrite subR_gt0; by case: Hx.
Defined.

Lemma derive_pt_diff_xlnx x (Hx : 0 < x < 1) :
  derive_pt diff_xlnx x (derivable_pt_diff_xlnx Hx) = -(2 + ln (x * (1-x))).
Proof.
rewrite derive_pt_plus derive_pt_opp derive_pt_xlnx; last by apply Hx.
rewrite derive_pt_comp derive_pt_plus derive_pt_const.
rewrite derive_pt_xlnx /=; last first.
  rewrite subR_gt0; by case: Hx.
rewrite add0R ln_mult; first field.
- by apply Hx.
- rewrite subR_gt0; by case: Hx.
Qed.

Lemma diff_xlnx_0 : diff_xlnx 0 = 0.
Proof. by rewrite /diff_xlnx subR0 xlnx_0 xlnx_1 subRR. Qed.

Lemma diff_xlnx_1 : diff_xlnx 1 = 0.
Proof. by rewrite /diff_xlnx subRR xlnx_0 xlnx_1 subRR. Qed.

Lemma derive_diff_xlnx_neg_aux x (Hx : 0 < x < 1) : x < exp (-2) -> 0 < derive_pt diff_xlnx x (derivable_pt_diff_xlnx Hx).
Proof.
rewrite derive_pt_diff_xlnx; case: Hx => Hx1 Hx2 xltexp2.
rewrite oppRD subR_gt0.
apply exp_lt_inv.
rewrite exp_ln ; last first.
  apply mulR_gt0 => //; by rewrite subR_gt0.
apply (@ltR_trans (exp (-2) * (1 - x))).
  apply ltR_pmul2r => //; by rewrite ltR_subRL addR0.
rewrite -{2}(mulR1 (exp (-2))).
apply ltR_pmul2l; first exact: exp_pos.
apply (@ltR_add2r (-1)).
by rewrite addRAC -[X in _ < X](addR0 _) ltR_add2l ltR_oppl oppR0.
Qed.

Lemma derive_diff_xlnx_pos x (Hx : 0 < x < 1) (pr : derivable_pt diff_xlnx x) : x < exp (-2) -> 0 < derive_pt diff_xlnx x pr.
Proof.
rewrite (proof_derive_irrelevance _ (derivable_pt_diff_xlnx Hx)).
apply derive_diff_xlnx_neg_aux.
Qed.

Lemma MVT_cor1_pderivable_new f a b : forall (prd : pderivable f (fun x => a < x < b)) (prc : forall x (Hx : a <= x <= b), continuity_pt f x),
  a < b ->
  exists c (Hc : a < c < b),
    f b - f a = derive_pt f c (prd c Hc) * (b - a) /\ a < c < b.
Proof.
intros prd prc ab.
have H0 : forall c : R, a < c < b -> derivable_pt f c.
  move=> c Hc.
  apply prd.
  case: Hc => ? ?; split; fourier.
have H1 : forall c : R, a < c < b -> derivable_pt id c.
  move=> c _; by apply derivable_pt_id.
have H2 : forall c, a <= c <= b -> continuity_pt f c.
  move=> x Hc.
  by apply prc.
have H3 : forall c, a <= c <= b -> continuity_pt id c.
  move=> x Hc; by apply derivable_continuous_pt, derivable_pt_id.
case: (MVT f id a b H0 H1 ab H2 H3) => c [Hc H'].
exists c.
exists Hc.
split => //.
cut (derive_pt id c (H1 c Hc) = derive_pt id c (derivable_pt_id c));
    [ intro | apply pr_nu ].
rewrite H (derive_pt_id c) mulR1 in H'.
rewrite -H' /= /id mulRC.
f_equal.
by apply pr_nu.
Qed.

Lemma MVT_cor1_pderivable_new_var f a b : forall (prd : pderivable f (fun x => a < x < b)) (prca : continuity_pt f a) (prcb : continuity_pt f b),
  a < b ->
  exists c (Hc : a < c < b),
    f b - f a = derive_pt f c (prd c Hc) * (b - a) /\ a < c < b.
Proof.
intros prd prca prcb ab.
have prc : forall x (Hx : a <= x <= b), continuity_pt f x.
  move=> x Hx.
  case/boolP : (x == a) => [/eqP -> //|xnota].
  case/boolP : (x == b) => [/eqP -> //|xnotb].
  apply derivable_continuous_pt, prd.
  split; apply/ltRP; rewrite ltR_neqAle.
  - rewrite eq_sym xnota; exact/leRP/(proj1 Hx).
  - rewrite xnotb; exact/leRP/(proj2 Hx).
have H0 : forall c : R, a < c < b -> derivable_pt f c.
  move=> c Hc.
  apply prd.
  case: Hc => ? ?; split; fourier.
have H1 : forall c : R, a < c < b -> derivable_pt id c.
  move=> c _; by apply derivable_pt_id.
have H2 : forall c, a <= c <= b -> continuity_pt f c.
  move=> x Hc.
  by apply prc.
have H3 : forall c, a <= c <= b -> continuity_pt id c.
  move=> x Hc; by apply derivable_continuous_pt, derivable_pt_id.
case: (MVT f id a b H0 H1 ab H2 H3) => c [Hc H'].
exists c.
exists Hc.
split => //.
cut (derive_pt id c (H1 c Hc) = derive_pt id c (derivable_pt_id c));
    [ intro | apply pr_nu ].
rewrite H (derive_pt_id c) mulR1 in H'.
rewrite -H' /= /id mulRC.
f_equal.
by apply pr_nu.
Qed.

Lemma derive_sincreasing_interv a b (f:R -> R) (pr: pderivable f (fun x => a < x < b)) (prc : forall x (Hx : a <= x <= b), continuity_pt f x) :
    a < b ->
    ((forall t:R, forall (prt : derivable_pt f t), a < t < b -> 0 < derive_pt f t prt) ->
      forall x y:R, a <= x <= b -> a <= y <= b -> x < y -> f x < f y).
Proof.
intros H H0 x y H1 H2 H3.
rewrite -subR_gt0.
have prd' : pderivable f (fun z => x < z < y).
  move=> z /= [Hz1 Hz2] ; apply pr.
  split.
  - apply (@leR_ltR_trans x) => //; by apply H1.
  - apply (@ltR_leR_trans y) => //; by apply H2.
have H0' : forall t (Ht : x < t < y), 0 < derive_pt f t (prd' t Ht).
  move=> z /= [Hz0 Hz1].
  apply H0.
  split.
  - apply (@leR_ltR_trans x) => //; by apply H1.
  - apply (@ltR_leR_trans y) => //; by apply H2.
have prcx : continuity_pt f x by apply prc; split; apply H1.
have prcy : continuity_pt f y by apply prc; split; apply H2.
have aux : a < b.
  apply (@leR_ltR_trans x) ; first by apply H1.
  apply (@ltR_leR_trans y) => //; by apply H2.
case: (MVT_cor1_pderivable_new_var prd' prcx prcy H3); intros x0 [x1 [H7 H8]].
rewrite H7.
apply mulR_gt0; first by apply H0'.
by rewrite subR_gt0.
Qed.

Lemma diff_xlnx_sincreasing_0_Rinv_e2 : forall x y : R, 0 <= x <= exp (-2) -> 0 <= y <= exp (-2) -> x < y -> diff_xlnx x < diff_xlnx y.
Proof.
apply derive_sincreasing_interv.
- move=> x /= [Hx1 Hx2].
  apply derivable_pt_diff_xlnx.
  split => //.
  exact: (ltR_trans Hx2 ltRinve21).
- move=> x /= Hx.
  rewrite /diff_xlnx.
  apply continuity_pt_minus ; last by apply continue_xlnx.
  apply (continuity_pt_comp (fun x => 1 - x) xlnx); last by apply continue_xlnx.
  apply continuity_pt_plus ; first by apply continuity_pt_const.
  apply continuity_pt_opp.
  apply derivable_continuous_pt.
  by apply derivable_pt_id.
- by apply exp_pos.
- move => t prt [Ht1 Ht2].
  apply derive_diff_xlnx_pos => //.
  exact: (conj Ht1 (ltR_trans Ht2 ltRinve21)).
Qed.

Lemma xlnx_ineq x : 0 <= x <= exp (-2) -> xlnx x <= xlnx (1-x).
Proof.
move=> [Hx1 Hx2].
apply Rge_le, Rminus_ge, Rle_ge.
rewrite -diff_xlnx_0 -/(diff_xlnx x).
case/boolP : (0 == x) => [/eqP ->|xnot0]; first exact/leRR.
apply/ltRW/diff_xlnx_sincreasing_0_Rinv_e2 => //.
  split; [exact/leRR | exact/ltRW/exp_pos].
apply/ltRP; rewrite ltR_neqAle xnot0; exact/leRP.
Qed.

End diff_xlnx.

Definition xlnx_delta a := fun x => xlnx (x + a) - xlnx x.

Lemma derivable_xlnx_delta eps (Heps : 0 < eps < 1) x (Hx : 0 < x < 1 - eps) :
  derivable_pt (xlnx_delta eps) x.
Proof.
rewrite /xlnx_delta.
apply derivable_pt_minus.
- apply (derivable_pt_comp (fun x => x + eps) xlnx).
    apply derivable_pt_plus ; first by apply derivable_pt_id.
    by apply derivable_pt_const.
  apply derivable_pt_xlnx.
  apply addR_gt0; by [apply Heps | apply Hx].
- by apply derivable_pt_xlnx, Hx.
Defined.

Lemma derive_pt_xlnx_delta eps (Heps : 0 < eps < 1) x (Hx : 0 < x < 1 - eps) :
  derive_pt (xlnx_delta eps) x (derivable_xlnx_delta Heps Hx) = ln (x + eps) - ln x.
Proof.
rewrite derive_pt_minus derive_pt_comp derive_pt_plus derive_pt_id.
rewrite derive_pt_const derive_pt_xlnx; last first.
  apply addR_gt0; by [apply Hx | apply Heps].
rewrite derive_pt_xlnx ; by [field | apply Hx].
Qed.

Lemma increasing_xlnx_delta eps (Heps : 0< eps < 1) :
  forall x y : R, 0 <= x <= 1 - eps -> 0 <= y <= 1 - eps -> x < y ->
                  xlnx_delta eps x < xlnx_delta eps y.
Proof.
apply derive_sincreasing_interv.
- move=> x /= [Hx1 Hx2] ; rewrite /xlnx_delta.
  apply derivable_pt_minus.
  - apply (derivable_pt_comp (fun x => x + eps) xlnx).
      apply derivable_pt_plus ; first by apply derivable_pt_id.
      by apply derivable_pt_const.
    apply derivable_pt_xlnx.
    apply addR_gt0 => //; by apply Heps.
  - exact: derivable_pt_xlnx.
- move=> x /= [Hx1 Hx2] ; rewrite /xlnx_delta.
  apply continuity_pt_minus.
  - apply (continuity_pt_comp (fun x => x + eps) xlnx); last by apply continue_xlnx.
      apply continuity_pt_plus ; first by apply derivable_continuous_pt, derivable_pt_id.
      by apply continuity_pt_const.
  - by apply continue_xlnx.
- apply subR_gt0; by case: Heps.
- move=> t prd Ht.
  rewrite (proof_derive_irrelevance _ (derivable_xlnx_delta Heps Ht)) derive_pt_xlnx_delta.
  apply/subR_gt0/ln_increasing; first by apply Ht.
  rewrite -{1}(addR0 t).
  by apply ltR_add2l, Heps.
Qed.

Lemma xlnx_delta_bound eps : 0 < eps <= exp (-2) ->
  forall x, 0 <= x <= 1 - eps -> `| xlnx_delta eps x | <= - xlnx eps.
Proof.
move=> [Heps1 Heps2] x [Hx1 Hx2].
apply/leRP; rewrite leR_Rabsl oppRK; apply/andP; split; apply/leRP.
- rewrite (_ : xlnx eps = xlnx_delta eps 0); last first.
    by rewrite /xlnx_delta add0R xlnx_0 subR0.
  case/boolP : (0 == x) => [/eqP <-|xnot0]; first exact/leRR.
  apply/ltRW/increasing_xlnx_delta => //.
  + exact: (conj Heps1 (leR_ltR_trans Heps2 ltRinve21)).
  + split ; by [apply (@leR_trans x) | exact: leRR].
  + apply/ltRP; rewrite ltR_neqAle xnot0; exact/leRP.
- apply (@leR_trans (xlnx_delta eps (1 - eps))).
    case/boolP : (x == 1 - eps) => [/eqP ->|xnot0]; first exact/leRR.
    apply/ltRW/increasing_xlnx_delta => //.
    + exact: (conj Heps1 (leR_ltR_trans Heps2 ltRinve21)).
    + split; by [apply (@leR_trans x) | exact: leRR].
    + apply/ltRP; rewrite ltR_neqAle xnot0; exact/leRP.
  rewrite /xlnx_delta subRK xlnx_1 sub0R leR_oppr oppRK.
  apply xlnx_ineq.
  split => //; exact: ltRW.
Qed.

Lemma Rabs_xlnx a (Ha : 0 <= a <= exp(-2)) x y :
  0 <= x <= 1 -> 0 <= y <= 1 -> `| x - y | <= a ->
  `| xlnx x - xlnx y | <= - xlnx a.
Proof.
move=> [Hx1 Hx2] [Hy1 Hy2] H.
case : (Rtotal_order x y) ; last case ; move => Hcase.
- have Haux : y = x + `| x - y |.
    by rewrite distRC gtR0_norm ?subR_gt0 // subRKC.
  rewrite Haux -normRN oppRD oppRK addRC.
  apply (@leR_trans (- xlnx `| x - y |)).
    apply xlnx_delta_bound.
    - split.
      - exact/Rabs_pos_lt/ltR_eqF/subR_lt0.
      - apply (@leR_trans a) => //; by apply Ha.
    - split => //.
      by rewrite leR_subr_addr -Haux.
  rewrite leR_oppr oppRK.
  apply xlnx_decreasing_0_Rinv_e => //.
  - split; first exact: normR_ge0.
    apply (@leR_trans a) => //.
    apply (@leR_trans (exp (- 2))); first by apply Ha.
    apply/ltRW/exp_increasing; fourier.
  - split; first by apply Ha.
    apply (@leR_trans (exp (-2))); first by apply Ha.
    apply/ltRW/exp_increasing; fourier.
- subst x ; rewrite subRR normR0 leR_oppr oppR0.
  case/orP : (orbN (0 == a)); last move=> anot0.
    by move=> /eqP <-; rewrite xlnx_0; exact: leRR.
  apply/ltRW/xlnx_neg; split.
  - apply/ltRP; rewrite lt0R eq_sym anot0; exact/leRP/(proj1 Ha).
  - exact: (leR_ltR_trans (proj2 Ha) ltRinve21).
- apply Rgt_lt in Hcase.
  have Haux : x = y + `| x - y | by rewrite gtR0_norm ?subR_gt0 // subRKC.
  rewrite distRC in H Haux.
  rewrite Haux.
  apply (@leR_trans (- xlnx `| y - x |)).
    apply xlnx_delta_bound.
    - split.
      - exact/Rabs_pos_lt/ltR_eqF/subR_lt0.
      - apply (@leR_trans a) => //; by apply Ha.
    - split => //.
      by rewrite leR_subr_addr -Haux.
  rewrite leR_oppr oppRK.
  apply xlnx_decreasing_0_Rinv_e => //.
  + split; first exact: normR_ge0.
    apply (@leR_trans a) => //.
    apply (@leR_trans (exp (-2))); first by apply Ha.
    apply/ltRW/exp_increasing; fourier.
  - split; first by apply Ha.
    apply (@leR_trans (exp (-2))); first by apply Ha.
    apply/ltRW/exp_increasing; fourier.
Qed.

End xlnx_sect.
