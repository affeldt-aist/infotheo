From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.
Require Import Reals Fourier ProofIrrelevance FunctionalExtensionality.
Require Import ssrR Reals_ext ssr_ext ssralg_ext logb Rbigop.
Require Import proba.

Require Import Ranalysis_ext jensen.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* NB(saikawa):
Assume f is twice differentiable on an open interval I.
Let Df and DDf be the first and second derivatives of f.
Further assume DDf is always positive.  By applying MVT, we have :
forall a x \in I, exists c1 \in [a,x], f(x) = f(a) + (x-a) * Df(c1).
Fix a and x.  Applying MVT again, we further get :
exists c2 \in (a,c1), Df(c1) = Df(a) + (c1-a) * DDf(c2).
The two equations combined is :
f(x) = f(a) + (x-a) * Df(a) + (x-a)(c1-a) * DDf(c2).
The last term is then positive thanks to the assumption on DDf.
Now this is an equivalent condition to the convexity of f.
 *)

(* ref: http://www.math.wisc.edu/~nagel/convexity.pdf *)
Section twice_der_convex.

Variables (f : R -> R) (a b : R).
Let I := fun x0 => a <= x0 <= b.
Hypothesis HDf : pderivable f I.
Variable Df : R -> R.
Hypothesis DfE : forall x (Hx : I x), Df x = derive_pt f x (HDf Hx).
Hypothesis HDDf : pderivable Df I.
Variable DDf : R -> R.
Hypothesis DDfE : forall x (Hx : I x), DDf x = derive_pt Df x (HDDf Hx).
Hypothesis DDf_ge0 : forall x, I x -> 0 <= DDf x.

Definition L (x : R) := f a + (x - a) / (b - a) * (f b - f a).

Hypothesis ab : a < b.

Lemma LE x : L x = (b - x) / (b - a) * f a + (x - a) / (b - a) * f b.
Proof.
rewrite /L mulRBr [in LHS]addRA addRAC; congr (_ + _).
rewrite addR_opp -{1}(mul1R (f a)) -mulRBl; congr (_ * _).
rewrite -(mulRV (b - a)); last by rewrite subR_eq0; exact/eqP/gtR_eqF.
by rewrite -mulRBl -addR_opp oppRB addRA subRK addR_opp.
Qed.

Lemma convexP : (forall x, a <= x <= b -> 0 <= L x - f x) ->
  forall t, 0 <= t <= 1 -> convex_leq f a b t.
Proof.
move=> H t t01; rewrite /convex_leq.
set x := t * a + (1 - t) * b.
have : a <= x <= b.
  rewrite /x; split.
  - apply (@leR_trans (t * a + (1 - t) * a)).
      rewrite -mulRDl addRCA addR_opp subRR addR0 mul1R; exact/leRR.
    case/boolP : (t == 1) => [/eqP ->|t1].
      rewrite subRR !mul0R !addR0 mul1R; exact/leRR.
    rewrite leR_add2l; apply leR_wpmul2l; last exact/ltRW.
    rewrite subR_ge0; by case: t01.
  - apply (@leR_trans (t * b + (1 - t) * b)); last first.
      rewrite -mulRDl addRCA addR_opp subRR addR0 mul1R; exact/leRR.
    rewrite leR_add2r; apply leR_wpmul2l; [by case: t01 | exact/ltRW].
move/H; rewrite subR_ge0 => /leR_trans; apply.
rewrite LE //.
have -> : (b - x) / (b - a) = t.
  rewrite /x -addR_opp oppRD addRCA mulRBl mul1R oppRB (addRCA b).
  rewrite addR_opp subRR addR0 -mulRN addRC -mulRDr addR_opp.
  rewrite /Rdiv -mulRA mulRV ?mulR1 // subR_eq0; exact/eqP/gtR_eqF.
have -> : (x - a) / (b - a) = 1 - t.
  rewrite /x -addR_opp addRAC -{1}(oppRK a) mulRN -mulNR -{2}(mul1R (- a)).
  rewrite -mulRDl (addRC _ 1) addR_opp -mulRDr addRC addR_opp.
  rewrite /Rdiv -mulRA mulRV ?mulR1 // subR_eq0; exact/eqP/gtR_eqF.
exact/leRR.
Qed.

Lemma second_derivative_convex : forall t,
  0 <= t <= 1 -> convex_leq f a b t.
Proof.
have note1 : forall x, 1 = (x - a) / (b - a) + (b - x) / (b - a).
  move=> x; rewrite -mulRDl addRC addRA subRK addR_opp mulRV // subR_eq0.
  exact/eqP/gtR_eqF.
have step1 : forall x, f x = (x - a) / (b - a) * f x + (b - x) / (b - a) * f x.
  by move=> x; rewrite -mulRDl -note1 mul1R.
apply convexP => // x axb.
rewrite /L.
case: axb.
  rewrite leR_eqVlt => -[-> _|].
  rewrite /L subRR div0R mul0R addR0 subRR; exact/leRR.
move=> ax.
rewrite leR_eqVlt => -[->|].
rewrite /L /Rdiv mulRV ?mul1R; last by rewrite subR_eq0; exact/eqP/gtR_eqF.
rewrite addRC subRK subRR; exact/leRR.
move=> xb.
have {step1}step2 : L x - f x =
  (x - a) * (b - x) / (b - a) * ((f b - f x) / (b - x)) -
  (b - x) * (x - a) / (b - a) * ((f x - f a) / (x - a)).
  rewrite {1}step1 {step1}.
  rewrite -addR_opp oppRD addRA addRC addRA.
  rewrite LE //.
  rewrite {1}/Rdiv -(mulRN _ (f x)) -/(Rdiv _ _).
  rewrite addRA -mulRDr (addRC _ (f a)) (addR_opp (f a)).
  rewrite -mulRN -addRA -mulRDr (addR_opp (f b)).
  rewrite addRC.
  rewrite -(oppRK (f a - f x)) mulRN addR_opp oppRB.
  congr (_ + _).
    rewrite {1}/Rdiv -!mulRA; congr (_ * _).
    rewrite mulRCA; congr (_ * _).
    rewrite mulRCA mulRV ?mulR1 // subR_eq0; exact/eqP/gtR_eqF.
  rewrite -!mulNR -!mulRA; congr (_ * _).
  rewrite mulRCA; congr (_ * _).
  rewrite mulRCA mulRV ?mulR1 // subR_eq0; exact/eqP/gtR_eqF.
have [c2 [Ic2 Hc2]] : exists c2, x < c2 < b /\ (f b - f x) / (b - x) = Df c2.
  have H : pderivable f (fun x0 => x <= x0 <= b).
    move=> z [z1 z2]; apply HDf; split => //.
    apply (@leR_trans x) => //; exact: ltRW.
  case: (@MVT_cor1_pderivable x b f H xb) => c2 [Ic2 [H1 H2]].
  exists c2; split => //.
  rewrite H1 /Rdiv -mulRA mulRV ?mulR1; last first.
    by rewrite subR_eq0; exact/eqP/gtR_eqF.
  rewrite DfE; last by move=> ?; exact: proof_derive_irrelevance.
  split.
    apply (@leR_trans x); [exact/ltRW | by case: Ic2 H1].
  by case: H2 => _ /ltRW.
have [c1 [Ic1 Hc1]] : exists c1, a < c1 < x /\ (f x - f a) / (x - a) = Df c1.
  have H : pderivable f (fun x0 => a <= x0 <= x).
    move=> z [z1 z2]; apply HDf; split => //.
    apply (@leR_trans x) => //; exact: ltRW.
  case: (@MVT_cor1_pderivable a x f H ax) => c1 [Ic1 [H1 H2]].
  exists c1; split => //.
  rewrite H1 /Rdiv -mulRA mulRV ?mulR1; last first.
    by rewrite subR_eq0; exact/eqP/gtR_eqF.
  rewrite DfE; last by move=> ?; exact: proof_derive_irrelevance.
  split.
    by case: H2 => /ltRW.
  apply (@leR_trans x).
  by case: H2 => _ /ltRW.
  apply (@leR_trans c2); apply/ltRW; by case: Ic2.
have c1c2 : c1 < c2.
  apply (@ltR_trans x); [by case: Ic1 | by case: Ic2].
have {step2 Hc1 Hc2}step3 : L x - f x =
  (b - x) * (x - a) * (c2 - c1) / (b - a) * ((Df c2 - Df c1) / (c2 - c1)).
  rewrite {}step2.
  rewrite Hc2 Hc1 (mulRC (x - a)) -mulRBr {1}/Rdiv -!mulRA.
  congr (_ * (_ * _)).
  rewrite mulRCA.
  congr (_ * _).
  rewrite mulRCA mulRV ?mulR1 // subR_eq0.
  by move/gtR_eqF/eqP : c1c2.
have [d [Id H]] : exists d, c1 < d < c2 /\ (Df c2 - Df c1) / (c2 - c1) = DDf d.
  have H : pderivable Df (fun x0 => c1 <= x0 <= c2).
    move=> z [z1 z2]; apply HDDf; split => //.
    apply (@leR_trans c1) => //.
    by case: Ic1 => /ltRW.
    apply (@leR_trans c2) => //.
    by case: Ic2 => _ /ltRW.
  case: (@MVT_cor1_pderivable c1 c2 Df H c1c2) => d [Id [H1 H2]].
  exists d; split => //.
  rewrite H1 /Rdiv -mulRA mulRV ?mulR1; last first.
    by rewrite subR_eq0; exact/eqP/gtR_eqF.
  rewrite DDfE; last by move=> ?; exact: proof_derive_irrelevance.
  split.
  apply (@leR_trans c1); last by case: Id H1.
  apply/ltRW; by case: Ic1.
  apply (@leR_trans c2); last first.
    by case: Ic2 => _ /ltRW.
  by case: H2 => _ /ltRW.
rewrite {}step3 {}H.
apply/mulR_ge0; last first.
  apply: DDf_ge0; split.
    apply (@leR_trans c1).
      apply/ltRW; by case: Ic1.
     by case: Id => /ltRW.
  apply (@leR_trans c2).
    by case: Id => _ /ltRW.
  apply/ltRW; by case: Ic2.
apply/mulR_ge0; last by apply/ltRW/invR_gt0; rewrite subR_gt0.
apply/mulR_ge0; last first.
  by rewrite subR_ge0; case: Id => Id1 Id2; apply (@leR_trans d); exact/ltRW.
apply/mulR_ge0; rewrite subR_ge0; exact/ltRW.
Qed.

End twice_der_convex.

Section log_concave.

Lemma pderivable_log a x1 : 0 <= a -> pderivable log (fun x2 : R => a < x2 < x1).
Proof.
move=> a0.
rewrite /pderivable => x Hx.
rewrite /log /Log.
rewrite (_ : (fun x0 => ln x0 / ln 2) = (mult_real_fct (/ ln 2) (fun x0 => ln x0))); last first.
  apply functional_extensionality => x0; by rewrite /mult_real_fct mulRC.
apply derivable_pt_scal.
apply derivable_pt_ln.
apply: (leR_ltR_trans a0).
by case: Hx.
Qed.

Lemma log_concave_gt0 x y t : x < y ->
  0 < x -> 0 < y -> 0 <= t <= 1 -> concave_leq log x y t.
Proof.
move=> xy x0 y0 t01.
suff : convex_leq (fun x => - log x) x y t.
  (* TODO: lemma, see concaveN *)
  rewrite /convex_leq /concave_leq !mulRN => /leR_oppl; by rewrite oppRD !oppRK.
set Df := fun x => - (/ln 2 * / x).
move: t t01.
have HDf : pderivable (fun x => - log x) (fun x0 => x <= x0 <= y).
  rewrite (_ : (fun x => - log x) = comp Ropp log); last first.
    exact: functional_extensionality.
  move=> r xry.
  apply derivable_pt_comp.
    apply/derivable_pt_Log/(@ltR_leR_trans x) => //; by case: xry.
  exact: derivable_pt_Ropp.
set DDf := fun x => /ln 2 * / x^2.
have HDDf : pderivable Df (fun x0 : R => x <= x0 <= y).
  rewrite /Df.
  rewrite (_ : (fun x => - (/ln 2 * / x)) =
      comp (fun x => - / ln 2 * x) Rinv); last first.
    apply: functional_extensionality => x1; by rewrite -mulNR.
  move=> r xry.
  apply derivable_pt_comp; last first.
    exact/derivable_pt_scal/derivable_pt_id.
  rewrite (_ : Rinv = inv_fct (fun x => x)); last first.
    exact: functional_extensionality.
  apply derivable_pt_inv; last exact: derivable_pt_id.
  apply/gtR_eqF/(@ltR_leR_trans x) => //; by case: xry.
apply: (@second_derivative_convex _ _ _ HDf Df _ HDDf DDf) => //.
- move=> r xry; rewrite /Df.
  have r0 : 0 < r by apply (@ltR_leR_trans x) => //; case: xry.
  transitivity (derive_pt (comp Ropp log) _
    (derivable_pt_comp log Ropp _ (derivable_pt_Log 2 r0) (derivable_pt_Ropp _))).
    by rewrite derive_pt_comp /= mulN1R.
  exact: proof_derive_irrelevance.
- move=> r xry.
  rewrite /DDf /Df.
  have r0 : r <> 0 by apply/gtR_eqF/(@ltR_leR_trans x) => //; case: xry.
  have Htmp : derivable_pt [eta Rmult (- / ln 2)] (/ r).
    exact/derivable_pt_scal/derivable_pt_id.
  transitivity (derive_pt (comp (fun x => (- / ln 2) * x) Rinv) _
    (derivable_pt_comp Rinv (fun x => (- / ln 2) * x) _
      (@derivable_pt_inv ssrfun.id _ r0 (derivable_pt_id _)) Htmp)).
    rewrite derive_pt_comp [in RHS]/= -(oppRK (_ * _)) -mulNR -mulRN.
    congr (_ * _).
      transitivity (derive_pt (mult_real_fct (- / ln 2) ssrfun.id) (/ r)
          (derivable_pt_scal ssrfun.id (- / ln 2) _ (derivable_pt_id _))).
        by rewrite derive_pt_scal derive_pt_id mulR1.
      by apply proof_derive_irrelevance.
    transitivity (derive_pt (/ ssrfun.id) _
      (@derivable_pt_inv ssrfun.id _ r0 (derivable_pt_id _))).
      rewrite derive_pt_inv derive_pt_id Rsqr_pow2 (* TODO: rename? *).
      by rewrite /Rdiv mulN1R.
    exact: proof_derive_irrelevance.
  apply proof_derive_irrelevance => z /=; by rewrite /comp mulNR.
- move=> r; rewrite /DDf => -[x11 x12].
  rewrite -expRV; last by apply/eqP/gtR_eqF/(@ltR_leR_trans x).
  apply/mulR_ge0.
  exact/ltRW/invR_gt0/ln2_gt0.
  exact/pow_ge0/ltRW/invR_gt0/(@ltR_leR_trans x).
Qed.

End log_concave.
