(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype.
From mathcomp Require Import tuple finfun bigop.
Require Import Reals Fourier.
Require Import Reals_ext Rssr.

(** * Additional lemmas about real analysis *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** Small extension to the mean value theorem to handle partially derivable functions *)

Lemma proof_derive_irrelevance g x (derg1 derg2 : derivable_pt g x) : derive_pt g x derg1 = derive_pt g x derg2.
Proof.
move : derg1 derg2.
case => l Hl.
case => m Hm.
move: Hl Hm ; rewrite /derivable_pt_abs => Hl Hm.
have ml : l = m by exact: (uniqueness_limite g x).
by subst m.
Qed.

Lemma derivable_pt_cst : forall c x, derivable_pt (fun _ => c) x.
Proof.
rewrite /derivable_pt /derivable_pt_abs /derivable_pt_lim.
exists 0 => e He.
exists (mkposreal _ He) => h Hh h0.
by rewrite subRR div0R subRR Rabs_R0.
Defined.

Lemma derive_pt_cst : forall x c, derive_pt (fun _ => c) x (derivable_pt_cst c x) = 0.
Proof. done. Defined.

Lemma derivable_pt_Ropp x : derivable_pt Ropp x.
Proof.
exists (-1) => eps Heps.
exists (mkposreal _ Heps) => h /eqP Hh /= Hh'.
rewrite (_ : (- (x + h) - - x) = - h); last by field.
rewrite /Rdiv mulNR mulRV // (_ : -1 - -1 = 0); last by field.
by rewrite Rabs_R0.
Defined.

Lemma derivable_pt_Rminus p x : derivable_pt (Rminus p) x.
Proof.
exists (-1) => eps Heps.
exists (mkposreal _ Heps) => h /eqP Hh /= Hh'.
rewrite (_ : (p - (x + h) - (p - x)) = - h); last by field.
rewrite /Rdiv mulNR mulRV // (_ : -1 - -1 = 0); last by field.
by rewrite Rabs_R0.
Defined.

Lemma derivable_pt_ln x : 0 < x -> derivable_pt ln x.
Proof.
move=> Hx.
exists (/ x).
apply derivable_pt_lim_ln.
assumption.
Defined.

Lemma derive_pt_ln : forall a (Ha : 0 < a), derive_pt ln a (derivable_pt_ln Ha) = (/ a).
Proof. done. Defined.

Lemma derivable_f_eq_g (f g : R -> R) x r : (forall y, r < y -> g y = f y) -> r < x ->
  derivable_pt f x -> derivable_pt g x.
Proof.
move=> Hfg rltx.
case => l Hl.
exists l => eps Heps ; move : Hl => /(_ eps Heps) ; case ; case => delt delt_pos Hdelt.
have aux : 0 < Rmin (x - r) delt.
  apply Rmin_case => // ; apply (Rplus_lt_reg_r r).
  by rewrite add0R addRC subRKC.
exists (mkposreal (Rmin (x - r) delt) aux) => /= h hnot0 Rlthdelta.
rewrite Hfg ; last first.
  apply (Rplus_lt_reg_r (- h)), Rgt_lt.
  rewrite -addRA Rplus_opp_r addR0; apply Rlt_gt.
  apply (Rplus_lt_reg_r (- r)).
  rewrite (addRC r) -addRA Rplus_opp_r addR0 addRC.
  apply (Rle_lt_trans _ (Rabs h)) ; first by [rewrite -Rabs_Ropp ; apply Rle_abs].
  apply (Rlt_le_trans _ (Rmin (- r + x) delt)) => //.
  by rewrite addRC.
  by apply Rmin_l.
rewrite Hfg //.
apply Hdelt => //=.
apply (Rlt_le_trans _ (Rmin (x - r) delt)) => // ; by apply Rmin_r.
Defined.

Lemma derive_pt_f_eq_g f g x r (Hfg : forall y, r < y -> g y = f y)
  (rltx : r < x) (derivable_f : derivable_pt f x) :
  derive_pt f x (derivable_f) =
  derive_pt g x (derivable_f_eq_g Hfg rltx derivable_f).
Proof.
rewrite /derive_pt /derivable_f_eq_g.
by destruct derivable_f.
Qed.

(** Derivability restricted by a condition (such as an appartenance to an interval): *)
Definition pderivable f (P : R -> Prop) := forall x, P x -> derivable_pt f x.

Section pderivable_prop.

Variables a b : R.
Variable f : R -> R.

Lemma MVT_cor1_pderivable : forall (pr : pderivable f (fun x => a <= x <= b)),
  a < b ->
  exists c, exists Hc : a <= c <= b,
    f b - f a = derive_pt f c (pr c Hc) * (b - a) /\ a < c < b.
Proof.
intros pr ab.
have H0 : forall c : R, a < c < b -> derivable_pt f c.
  move=> c Hc.
  apply pr.
  case: Hc => ? ?; split; fourier.
have H1 : forall c : R, a < c < b -> derivable_pt id c.
  move=> c _; by apply derivable_pt_id.
have H2 : forall c, a <= c <= b -> continuity_pt f c.
  move=> x Hc.
  apply derivable_continuous_pt.
  apply pr.
  case: Hc => ? ?; split; fourier.
have H3 : forall c, a <= c <= b -> continuity_pt id c.
  move=> x Hc; by apply derivable_continuous_pt, derivable_pt_id.
case: (MVT f id a b H0 H1 ab H2 H3) => c [Hc H'].
exists c.
have Hc' : a <= c <= b.
  clear H'.
  case: Hc => ? ?; split; fourier.
exists Hc'.
split; last by done.
cut (derive_pt id c (H1 c Hc) = derive_pt id c (derivable_pt_id c));
    [ intro | apply pr_nu ].
rewrite H (derive_pt_id c) mulR1 in H'.
rewrite -H' /= /id mulRC.
f_equal.
by apply pr_nu.
Qed.

Lemma pderivable_restrict_left : pderivable f (fun x => a < x <= b) ->
  forall a' b', a < a' -> b' <= b -> a' < b' ->
  pderivable f (fun x => a' <= x <= b').
Proof. move=> H a' b' aa' bb' a'b' z [z0 z1]; apply H; split; fourier. Defined.

Lemma pderivable_restrict_right : pderivable f (fun x => a <= x < b) ->
  forall a' b', a <= a' -> b' < b -> a' < b' ->
  pderivable f (fun x => a' <= x <= b').
Proof. move=> H a' b' aa' bb' a'b' z [z0 z1]; apply H; split; fourier. Defined.

End pderivable_prop.

Lemma derive_increasing_interv_ax_left : forall (a b:R) (f:R -> R) (pr: pderivable f (fun x => a < x <= b)),
    a < b ->
    ((forall t:R, forall Ht :a < t <= b, 0 < derive_pt f t (pr t Ht)) ->
      forall x y:R, a < x <= b -> a < y <= b -> x < y -> f x < f y) /\
    ((forall t:R, forall Ht : a < t <= b, 0 <= derive_pt f t (pr t Ht)) ->
      forall x y:R, a < x <= b -> a < y <= b -> x < y -> f x <= f y).
Proof.
intros a b f pr H; split; intros H0 x y H1 H2 H3.
- apply Rplus_lt_reg_r with (- f x).
  rewrite addRC Rplus_opp_l.
  set pr' := pderivable_restrict_left pr (proj1 H1) (proj2 H2) H3.
  have H0' : forall t (Ht : x <= t <= y), 0 < derive_pt f t (pr' t Ht).
    move=> z /= [Hz0 Hz1].
    by apply H0.
  case: (MVT_cor1_pderivable pr' H3); intros x0 [x1 [H7 H8]].
  unfold Rminus in H7.
  rewrite H7.
  apply mulR_gt0; [by apply H0' | fourier].
- set pr' := pderivable_restrict_left pr (proj1 H1) (proj2 H2) H3.
  have H0' : forall t (Ht : x <= t <= y), 0 <= derive_pt f t (pr' t Ht).
    move=> z /= [Hz0 Hz1].
    by apply H0.
  case: (MVT_cor1_pderivable pr' H3); intros x0 [x1 [H7 H8]].
  apply Rplus_le_reg_l with (- f x).
  unfold Rminus in H7.
  rewrite Rplus_opp_l addRC H7.
  apply mulR_ge0; [by apply H0' | fourier].
Qed.

Lemma derive_increasing_interv_ax_right :
  forall (a b:R) (f:R -> R) (pr: pderivable f (fun x => a <= x < b)),
    a < b ->
    ((forall t:R, forall Ht :a <= t < b, 0 < derive_pt f t (pr t Ht)) ->
      forall x y:R, a <= x < b -> a <= y < b -> x < y -> f x < f y) /\
    ((forall t:R, forall Ht : a <= t < b, 0 <= derive_pt f t (pr t Ht)) ->
      forall x y:R, a <= x < b -> a <= y < b -> x < y -> f x <= f y).
Proof.
intros a b f pr H; split; intros H0 x y H1 H2 H3.
- apply Rplus_lt_reg_r with (- f x).
  rewrite addRC Rplus_opp_l.
  set pr' := pderivable_restrict_right pr (proj1 H1) (proj2 H2) H3.
  have H0' : forall t (Ht : x <= t <= y), 0 < derive_pt f t (pr' t Ht).
    move=> z /= [Hz0 Hz1].
    by apply H0.
  case: (MVT_cor1_pderivable pr' H3); intros x0 [x1 [H7 H8]].
  unfold Rminus in H7.
  rewrite H7.
  apply mulR_gt0; [by apply H0' | fourier].
- set pr' := pderivable_restrict_right pr (proj1 H1) (proj2 H2) H3.
  have H0' : forall t (Ht : x <= t <= y), 0 <= derive_pt f t (pr' t Ht).
    move=> z /= [Hz0 Hz1].
    by apply H0.
  assert (H4 := MVT_cor1_pderivable pr' H3).
  case H4; intros x0 [x1 [H7 H8]].
  apply Rplus_le_reg_l with (- f x).
  unfold Rminus in H7.
  rewrite Rplus_opp_l addRC H7.
  apply mulR_ge0; [by apply H0' | fourier].
Qed.

Lemma derive_increasing_interv_left :
  forall (a b:R) (f:R -> R) (pr:pderivable f (fun x => a < x <= b)),
    a < b ->
    (forall t:R, forall Ht : a < t <= b, 0 <= derive_pt f t (pr t Ht)) ->
    forall x y:R, a < x <= b -> a < y <= b -> x <= y -> f x <= f y.
Proof.
move=> a b f pr ab H x y Hx Hy xy.
case: (derive_increasing_interv_ax_left pr ab) => H1 H2.
case/Rle_lt_or_eq_dec : xy => xy.
- now apply H2.
- rewrite xy; by apply Req_le.
Qed.

Lemma derive_increasing_interv_right :
  forall (a b:R) (f:R -> R) (pr:pderivable f (fun x => a <= x < b)),
    a < b ->
    (forall t:R, forall Ht : a <= t < b, 0 <= derive_pt f t (pr t Ht)) ->
    forall x y:R, a <= x < b -> a <= y < b -> x <= y -> f x <= f y.
Proof.
move=> a b f pr ab H x y Hx Hy xy.
case: (derive_increasing_interv_ax_right pr ab) => H1 H2.
case/Rle_lt_or_eq_dec : xy => xy.
apply H2 => //.
subst y.
by apply Req_le.
Qed.

Lemma derive_increasing_ad_hoc (a b : R) (f : R -> R) (pr : pderivable f (fun x => a < x <= b)) :
  a < b ->
  ((forall t:R, forall Ht :a < t <= b, 0 < if t == b then 1 else derive_pt f t (pr t Ht))  ->
   forall x y:R, a < x <= b -> a < y <= b -> x < y -> f x < f y).
Proof.
move=> H H0 x y H1 H2 H3.
apply Rplus_lt_reg_r with (- f x).
rewrite addRC Rplus_opp_l.
set pr' := pderivable_restrict_left pr (proj1 H1) (proj2 H2) H3.
have H0' : forall t (Ht : x <= t <= y), 0 < if t == y then 1 else derive_pt f t (pr' t Ht).
  move=> z /= [Hz0 Hz1].
  case/orP : (orbN (z == y)) => Hcase.
  - rewrite Hcase ; fourier.
  - move/negbTE in Hcase ; rewrite Hcase.
  have Hz : a < z <= b.
    split.
    - apply (Rlt_le_trans _ x _) ; [apply H1 | exact Hz0].
    - apply (Rle_trans _ y _) ; [exact Hz1 | apply H2].
  move: (H0 z) => H02.
  have Hz2 : ~~ (z == b).
    apply/eqP.
    apply Rlt_not_eq.
    clear Hz0 H1 H3 pr' H H0 x.
    move/eqP in Hcase.
    apply (Rlt_le_trans _ y _).
    - case (total_order_T z y) ; first case ; move=> Hzy.
      - exact Hzy.
      - contradict Hcase ; exact Hzy.
      - fourier.
    - apply H2.
  move/negbTE in Hz2.
  rewrite Hz2 in H02.
  by apply H02.
case: (MVT_cor1_pderivable pr' H3); intros x0 [x1 [H7 H8]].
unfold Rminus in H7.
rewrite H7.
apply mulR_gt0; last by fourier.
have Hx0 : ~~ (x0 == y).
  apply/eqP ; apply Rlt_not_eq, H8.
move/negbTE in Hx0.
move: (H0' x0) ; rewrite Hx0 ; by apply.
Qed.
