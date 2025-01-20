(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix interval.
From mathcomp Require Import ring.
From mathcomp Require boolp.
From mathcomp Require Import mathcomp_extra Rstruct reals set_interval.
From mathcomp Require Import functions topology normedtype realfun derive exp.
From mathcomp Require convex.
Require Reals Ranalysis_ext Lra Reals_ext.
Require Import ssrR realType_ext realType_logb ssr_ext ssralg_ext bigop_ext.
Require Import derive_ext.
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

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope convex_scope.
Local Open Scope entropy_scope.

Import Order.POrderTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Import numFieldNormedType.Exports.

Section analysis_ext.
Import boolp classical_sets.

(*
Lemma near_eq_cvg_to (U : nbhsType) (T : Type) (F : set_system T)
  (f g : T -> U) (x : U) :
  Filter F -> 
  (\near F, f F = g F) ->
  (fmap f F --> x)%classic = (fmap g F --> x)%classic.
Proof.
move=> FF nfg.
suff-> : (f x @[x --> F] = g x @[x --> F])%classic. by [].
rewrite eqEsubset; split; apply: near_eq_cvg=> //.
by move/filterS: nfg; apply=> ?; exact: fsym.
Qed.
Arguments near_eq_cvg_to [U T F].
*)

Lemma open_norm_subball (R : numFieldType) (M : normedModType R)
  (A : set M) (x : M) :
  open A -> A x ->
  \forall e \near ((0 : R)^')%classic, (ball x `|e| `<=` A)%classic.
Proof.
move/(@conj (open A) _)/[apply]/open_nbhs_nbhs/nbhsr0P.
rewrite -!nbhs_nearE=> H.
under [X in nbhs _ X]funext=> e.
  rewrite /subset.
  under eq_forall=> y do rewrite -ball_normE /=.
  over.
case: H=> e /= e0 He.
exists e=> //= e' /=.
rewrite distrC subr0=> e'e e'0 y xye'.
apply: (He `|e'|).
- by rewrite /= distrC subr0 normr_id.
- by rewrite normr_gt0.
- exact: ltW.
Qed.

Local Notation DQ f v a h := (h^-1 *: (f (h *: v + a) - f a)).

Let near_eq_difference_quotient (R : numFieldType) (V W : normedModType R)
  (f g : V -> W) (a v : V) :
  v != 0 -> (\near a, f a = g a) ->
  \forall h \near nbhs (0^')%classic, DQ f v a h = DQ g v a h.
Proof.
move=> vn0 fg.
have fg0: \forall h \near (0^')%classic, f (h *: v + a) = g (h *: v + a).
  have:= fg.
  rewrite -!nbhs_nearE nbhsE => -[] U [] oU Ua Ufg.
  have:= open_norm_subball oU Ua; case=> e /= e0 eU.
  exists (e * `|2 *: v|^-1)=> /=.
    rewrite mulr_gt0// invr_gt0 normrZ mulr_gt0// ?(normr_gt0 v)//.
    by rewrite normr_nat ltr0Sn.
  move=> h /= /[1!distrC] /[!subr0] he2v h0.
  apply/(Ufg (h *: v + a))/(eU (h * `| 2 *: v|)).
  - rewrite /= distrC subr0 normrM normr_id -ltr_pdivlMr//.
    rewrite normrZ mulr_gt0// ?(normr_gt0 v)//.
    by rewrite normr_nat ltr0Sn.
  - rewrite mulf_neq0// normrZ.
    rewrite mulf_neq0// normr_eq0//.
    by rewrite pnatr_eq0.
  - rewrite -ball_normE /=.
    rewrite opprD addrCA subrr addr0 normrN !normrZ !normr_id.
    rewrite mulrCA ltr_pMl// ?mulr_gt0// ?normr_gt0//.
    by rewrite [ltLHS](_ : 1 = 1%:R)// normr_nat ltr_nat.
have:= fg0 => /filterS; apply=> h ->.
move: fg.
by rewrite -nbhs_nearE nbhsE=> -[] U [] oU Ua /(_ a Ua) ->.
Qed.

Lemma near_eq_derive (R : numFieldType) (V W : normedModType R)
  (f g : V -> W) (a v : V) :
  v != 0 -> (\near a, f a = g a) -> 'D_v f a = 'D_v g a.
Proof.
move=> vn0 fg.
rewrite /derive.
suff-> : (DQ f v a h @[h --> 0^'])%classic = (DQ g v a h @[h --> 0^'])%classic
  by [].
have Dfg := near_eq_difference_quotient vn0 fg.
rewrite eqEsubset; split; apply: near_eq_cvg=> //.
by move/filterS: Dfg; apply=> ?; exact: fsym.
Qed.

Lemma near_eq_derivable (R : numFieldType) (V W : normedModType R)
  (f g : V -> W) (a v : V) :
  v != 0 -> (\near a, f a = g a) -> derivable f a v = derivable g a v.
Proof.
move=> vn0 nfg.
rewrite /derivable.
suff-> : (DQ f v a h @[h --> 0^'])%classic = (DQ g v a h @[h --> 0^'])%classic
  by [].
have Dfg := near_eq_difference_quotient vn0 nfg.
rewrite eqEsubset; split; apply: near_eq_cvg=> //.
by move/filterS: Dfg; apply=> ?; exact: fsym.
Qed.

Lemma near_eq_is_derive (R : numFieldType) (V W : normedModType R)
  (f g : V -> W) (a v : V) (df : W) :
  v != 0 -> (\near a, f a = g a) ->
  is_derive a v f df = is_derive a v g df.
Proof.
move=> vn0; move: f g.
suff fg f g (nfg : \near a, f a = g a) :
  is_derive a v f df -> is_derive a v g df.
  move=> f g nfg; apply: propext; split; apply: fg => //.
  suff->: (\near a, g a = f a) = (\near a, f a = g a) by [].
  by apply: eq_near=> ?; split; exact: esym.
move/[dup]/@ex_derive=> H.
move/@derive_val<-.
rewrite (near_eq_derive vn0 nfg).
apply/derivableP.
by rewrite -(near_eq_derivable vn0 nfg).
Qed.

End analysis_ext.
Arguments near_eq_derive [R V W] f g [a].
Arguments near_eq_derivable [R V W] f g [a].
Arguments near_eq_is_derive [R V W] f g [a].

Local Notation "{ 'fdist' T }" := (_ .-fdist T) : fdist_scope.

Section entropy_log_div.
Variable R : realType.
Variables (A : finType) (p : R.-fdist A) (n : nat) (An1 : #|A| = n.+1).
Let u := @fdist_uniform R _ _ An1.

Local Open Scope divergence_scope.

Lemma entropy_log_div : entropy p = log #|A|%:R - D(p || u).
Proof.
rewrite /entropy /div.
evar (RHS : A -> R).
have H a : p a * log (p a / u a) = RHS a.
  have:= FDist.ge0 p a.
  rewrite le_eqVlt=> /orP [/eqP H|H]; last first.
  - rewrite fdist_uniformE invrK logM//; last by rewrite An1.
    rewrite mulrDr.
    by instantiate (RHS := fun a => p a * log (p a) + p a * log #|A|%:R).
  - by rewrite /RHS -H /= 3!mul0r add0r.
have -> : \sum_(a in A) p a * log (p a / u a) = \sum_(a in A) RHS a.
  by move : H; rewrite /RHS => H; exact: eq_bigr.
rewrite /RHS big_split /= -big_distrl /= (FDist.f1 p) mul1r.
by rewrite opprD addrC -addrA addNr addr0.
Qed.
End entropy_log_div.

Section dominated_pair.
Let R := Rdefinitions.R.
Variable A : finType.
Implicit Types p q : {prob R}.

Definition dom_pair := {d : R.-fdist A * {fdist A} | d.1 `<< d.2}.

(* TODO: wouldn't be needed if dominates were on bool *)
HB.instance Definition _ := boolp.gen_eqMixin dom_pair.
HB.instance Definition _ := boolp.gen_choiceMixin dom_pair.

Lemma dom_conv p (x y u v : {fdist A}) :
  x `<< y -> u `<< v -> x <| p |> u `<< y <| p |> v.
Proof.
move=> /dominatesP xy /dominatesP uv; apply/dominatesP => a.
rewrite !fdist_convE.
rewrite paddR_eq0; [|exact/mulR_ge0 |exact/mulR_ge0].
rewrite !mulR_eq0 => -[[->|/xy ->]]; last first.
  by rewrite -RplusE -!RmultE mulR0 add0R => -[->|/uv ->]; rewrite !(mul0R,mulR0).
by rewrite -RplusE -!RmultE mul0R add0R => -[|/uv ->];
  [rewrite onem0 => /Raxioms.R1_neq_R0 | rewrite mulR0].
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
  avg avg1 avgI avgC avgA.

End dominated_pair.

Section divergence_convex.
Local Open Scope divergence_scope.
Variables A : finType.
Import Reals Reals_ext.

Lemma convex_div : convex_function (uncurry_dom_pair (@div _ A)).
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
  apply/Req_le; rewrite -!coqRE mulRA mul0R mulR0 !addR0; congr (_ * _ * log _).
  by rewrite !coqRE mulrAC invfM !mulrA mulfV// div1r mulrC.
have [x2a0|x2a0] := eqVneq (x.2 a) 0.
  rewrite x2a0 (_ : x.1 a = 0)// -?RplusE -?RmultE ?(mulR0,add0R,mul0R); last first.
    by move/dominatesP : Hx; exact.
  have [->|t0] := eqVneq (Prob.p p).~ 0; first by rewrite !mul0R.
  apply/Req_le; rewrite mulRA; congr (_ * _ * log _).
  by rewrite !coqRE mulrAC invfM !mulrA mulfV// div1r mulrC.
set h : {fdist A} -> {fdist A} -> {ffun 'I_2 -> R} := fun p1 p2 => [ffun i =>
  [eta (fun=> 0) with ord0 |-> Prob.p p * p1 a, lift ord0 ord0 |-> (Prob.p p).~ * p2 a] i].
have hdom : h x.1 y.1 `<< h x.2 y.2.
  apply/dominatesP => i; rewrite /h /= !ffunE; case: ifPn => _.
    by rewrite mulR_eq0 => -[->|/eqP]; [rewrite mul0r | rewrite (negbTE x2a0)].
  case: ifPn => // _.
  by rewrite mulR_eq0 => -[->|/eqP]; [rewrite mul0r | rewrite (negbTE y2a0)].
have h0 p1 p2 : [forall i, (0 <= h p1 p2 i)%mcR].
  apply/forallPP; first by move=> ?; exact/RleP.
  move=> ?; rewrite /h /= ffunE.
  case: ifPn => [_ | _]; first exact/mulR_ge0.
  case: ifPn => [_ |]; last by move=>*; exact: Rle_refl.
  by apply/mulR_ge0 => //; exact/onem_ge0/prob_le1.
have h01 (x0 : 'I_2) : (0 <= mkNNFinfun (h0 x.1 y.1) x0)%mcR.
  rewrite /= /h ffunE/=; case: ifPn => _; first exact: mulr_ge0.
  by case: ifPn => // _; exact: mulr_ge0.
have h02 (x0 : 'I_2) : (0 <= mkNNFinfun (h0 x.2 y.2) x0)%mcR.
  rewrite /= /h ffunE/=; case: ifPn => _; first exact: mulr_ge0.
  by case: ifPn => // _; exact: mulr_ge0.
have := @log_sum _ _ setT (mkNNFinfun (h0 x.1 y.1)) (mkNNFinfun (h0 x.2 y.2)) h01 h02 hdom.
rewrite /= -!sumR_ord_setT !big_ord_recl !big_ord0 !addR0.
move/RleP; rewrite /h /= !ffunE => /leR_trans; apply.
rewrite !eqxx eq_sym (negbTE (neq_lift ord0 ord0)) -coqRE -!mulRA; apply/Req_le.
congr (_  + _ ).
  have [->|t0] := eqVneq p 0%:pr; first by rewrite !mul0R.
  by congr (_ * (_ * log _)); rewrite mulrAC invfM !mulrA mulfV// div1r mulrC.
have [->|t1] := eqVneq (Prob.p p).~ 0; first by rewrite !mul0R !mul0r.
rewrite -coqRE !mulRA.
by congr (_ * _ * _); rewrite mulrAC invfM !mulrA mulfV// div1r mulrC.
Qed.

Lemma convex_relative_entropy (p1 p2 q1 q2 : {fdist A}) (r : {prob R}) :
  p1 `<< q1 -> p2 `<< q2 ->
  D(p1 <| r |> p2 || q1 <| r |> q2) <= D(p1 || q1) <| r |> D(p2 || q2).
Proof.
move=> pq1 pq2.
exact/RleP/(convex_div (exist _ (p1, q1) pq1) (exist _ (p2, q2) pq2)).
Qed.

End divergence_convex.

Section entropy_concave.
Local Open Scope divergence_scope.
Variable A : finType.
Hypothesis cardA_gt0 : (0 < #|A|)%nat.

Let cardApredS : #|A| = #|A|.-1.+1.
Proof. by rewrite prednK. Qed.

Lemma entropy_concave : concave_function (fun P : {fdist A} => `H P).
Proof.
apply RNconcave_function => p q t; rewrite /convex_function_at.
apply/RleP.
rewrite !(entropy_log_div _ cardApredS) /= /leconv /= [in X in _ <= X]avgRE.
rewrite oppRD oppRK 2!mulRN mulRDr mulRN mulRDr mulRN oppRD oppRK oppRD oppRK.
rewrite addRCA !addRA -2!mulRN -mulRDl (addRC _ (Prob.p t)).
apply/RleP.
rewrite !RplusE onemKC mul1R -!RplusE -addRA leR_add2l.
have := convex_relative_entropy t (dom_by_uniform p cardApredS)
                                  (dom_by_uniform q cardApredS).
move/RleP.
by rewrite convmm.
Qed.

End entropy_concave.

Lemma unitiE x : uniti x = (0 < x < 1).
Proof.
rewrite /uniti -(boolp.propext (rwP andP)).
by rewrite (boolp.propext (rwP (RltP 0 x))) (boolp.propext (rwP (RltP x 1))).
Qed.

Module entropy_concave_alternative_proof_binary_case.
Import classical_sets.

Section realType.

Variable R : realType.
Local Notation H2 := (@H2 R).

Lemma derivable_H2 v : {in `]0, 1[, forall x : R, derivable H2 x v}.
move=> x /= /[!in_itv] /= /andP [] x0 x1.
apply: derivableD.
  apply: derivableN.
  apply: derivableM; first exact: derivable_id.
  exact/diff_derivable/differentiable_Log. (* TODO: derivable_Log *)
apply: derivableN.
apply: derivableM; first exact: ex_derive.
apply: diff_derivable. (* TODO: derivable_comp *)
apply: differentiable_comp; first exact: ex_diff.
apply: differentiable_Log=> //.
by rewrite subr_gt0.
Qed.

Lemma derivable_nH2 v : {in `]0, 1[, forall x : R, derivable (- H2) x v}.
move=> x /= /[!in_itv] /= /andP [] x0 x1.
apply: diff_derivable.
apply: differentiableN.
apply: differentiableD.
  apply: differentiableN.
  apply: differentiableM; first exact: ex_diff.
  exact: differentiable_Log.
apply: differentiableN.
apply: differentiableM.
  exact: ex_diff.
apply: differentiable_comp.
  exact: ex_diff.
apply: differentiable_Log=> //.
by rewrite subr_gt0.
Qed.

Definition sig_derive1_H2 (x : R) :
  {D : R | x \in `]0, 1[ -> is_derive x 1 H2 D}.
Proof.
evar (D0 : (R : Type)); evar (D1 : (R : Type)); exists D0.
rewrite in_itv /= => /andP [] x0 x1.
suff->: D0 = D1.
  rewrite /H2.
  apply: is_deriveD.
    apply: is_deriveN.
    apply: is_deriveM.
      exact: is_derive_id.
    exact: is_derive1_Logf.
  apply: is_deriveN.
  apply: is_deriveM.
  apply: is_derive1_comp.
  apply: is_derive1_Logf=> //.
  by rewrite subr_gt0 //.
have ? : x != 0 by exact: lt0r_neq0.
have ? : 1 - x != 0 by rewrite lt0r_neq0// subr_gt0.
rewrite /D1.
rewrite -!mulr_regl !(add0r, mul1r, mulr1, mulrN, mulNr, opprD, opprK).
rewrite mulrCA divff// mulrCA divff//.
rewrite !mulr1 addrCA !addrA subrr add0r addrC.
by instantiate (D0 := log (1 - x) - log x).
Defined.

Definition sig_derive1_nH2 (x : R) :
  {D : R | x \in `]0, 1[ -> is_derive x 1 (- H2) D}.
Proof.
evar (D0 : (R : Type)); evar (D1 : (R : Type)); exists D0.
rewrite in_itv /= => /andP [] x0 x1.
suff->: D0 = D1.
  rewrite /H2.
  apply: is_deriveN.
  apply: is_deriveD.
    apply: is_deriveN.
    apply: is_deriveM.
      exact: is_derive_id.
    exact: is_derive1_Logf.
  apply: is_deriveN.
  apply: is_deriveM.
  apply: is_derive1_comp.
  apply: is_derive1_Logf=> //.
  by rewrite subr_gt0 //.
have ? : x != 0 by exact: lt0r_neq0.
have ? : 1 - x != 0 by rewrite lt0r_neq0// subr_gt0.
rewrite /D1.
rewrite -!mulr_regl !(add0r, mul1r, mulr1, mulrN, mulNr, opprD, opprK).
rewrite mulrCA divff// mulrCA divff//.
rewrite !mulr1 addrAC addrA subrr add0r addrC.
by instantiate (D0 := log x - log (1 - x)).
Defined.

Local Notation DH2 := (fun x => log (1 - x) - log x).
Local Notation DnH2 := (fun x => log x - log (1 - x)).

Lemma DH2E (x : R) :
  x \in `]0, 1[ -> \near x, 'D_1 H2 x = DH2 x.
Proof.
move=> x01.
rewrite -nbhs_nearE nbhsE; exists `]0, 1[%classic.
  split=> //; exact: (@itv_open _ (R : realFieldType)).
by move=> y /= /(svalP (sig_derive1_H2 y))/@derive_val.
Qed.

Lemma DnH2E (x : R) :
  x \in `]0, 1[ -> \near x, 'D_1 (- H2) x = DnH2 x.
Proof.
move=> x01.

STOP

near=> y.
  rewrite deriveN; last exact: derivable_H2.
  apply: oppr_inj; rewrite opprK opprB.
  exact: (near (DH2E x01) y).
Unshelve.
exists `]0, 1[%classic.

by [].
Qed.
  near: y.
Unset Printing Notations.
simpl.
rewrite 
rewrite -nbhs_nearE /=.
  

rewrite -nbhs_nearE nbhsE; exists `]0, 1[%classic.
  split=> //; exact: (@itv_open _ (R : realFieldType)).
(*by move=> y /= /(svalP (sig_derive1_nH2 y))/@derive_val->.*)
move=> y /= /[dup] y01 /(svalP (sig_derive1_H2 y)) /@derive_val /=.
rewrite deriveN ?(boolp.propT (derivable_H2 y01))//.
by move->; rewrite opprB.
Qed.

Definition sig_derive1_DH2 (x : R) :
  {D : R | x \in `]0, 1[ -> is_derive x 1 ('D_1 H2) D}.
Proof.
evar (D0 : (R : Type)); evar (D1 : (R : Type)); exists D0.
move/[dup]=> x01.
rewrite in_itv /= => /andP [] x0 x1.
rewrite (near_eq_is_derive _ DnH2) ?oner_neq0//; last first.
  rewrite -nbhs_nearE nbhsE /=.
  exists `]0, 1[%classic.
    split=>//; exact: (@itv_open _ (R : realFieldType)).
  exact: DnH2E.
suff->: D0 = D1.
  apply: is_deriveB.
    exact: is_derive1_Logf.
  apply: is_derive1_Logf=> //.
  by rewrite subr_gt0.
have ? : x != 0 by exact: lt0r_neq0.
have ? : 1 - x != 0 by rewrite lt0r_neq0// subr_gt0.
rewrite /D1.
rewrite !(add0r, mul1r, mulr1, mulrN, mulNr, opprD, opprK) -mulrDr.
by instantiate (D0 := (ln 2)^-1 * (x^-1 + (1 - x)^-1)).
Defined.

(*
Lemma DnH2E (x : R) :
  x \in `]0, 1[ -> 'D_1 (- H2) x = DnH2 x.
Proof. by move/(svalP (sig_derive1_nH2 x))/@derive_val->. Qed.

Definition sig_derive1_DnH2 (x : R) :
  {D : R | x \in `]0, 1[ -> is_derive x 1 ('D_1 (- H2)) D}.
Proof.
evar (D0 : (R : Type)); evar (D1 : (R : Type)); exists D0.
move/[dup]=> x01.
rewrite in_itv /= => /andP [] x0 x1.
rewrite (near_eq_is_derive _ DnH2) ?oner_neq0//; last first.
  rewrite -nbhs_nearE nbhsE /=.
  exists `]0, 1[%classic.
    split=>//; exact: (@itv_open _ (R : realFieldType)).
  exact: DnH2E.
suff->: D0 = D1.
  apply: is_deriveB.
    exact: is_derive1_Logf.
  apply: is_derive1_Logf=> //.
  by rewrite subr_gt0.
have ? : x != 0 by exact: lt0r_neq0.
have ? : 1 - x != 0 by rewrite lt0r_neq0// subr_gt0.
rewrite /D1.
rewrite !(add0r, mul1r, mulr1, mulrN, mulNr, opprD, opprK) -mulrDr.
by instantiate (D0 := (ln 2)^-1 * (x^-1 + (1 - x)^-1)).
Defined.
*)

Local Notation DDnH2 := (fun x => (ln 2)^-1 * (x^-1 + (1 - x)^-1)).

Lemma DDnH2E (x : R) :
  x \in `]0, 1[ -> 'D_1 ('D_1 (- H2)) x = DDnH2 x.
Proof.
move=> x01.
by have:= svalP (sig_derive1_DnH2 x) => /(_ x01) /@derive_val /= <-.
Qed.

Lemma DDnH2_nonneg (x : R) : x \in `]0, 1[ -> 0 <= DDnH2 x.
Proof.
rewrite in_itv /= => /andP [] x0 x1.
rewrite mulr_ge0//.
  by rewrite invr_ge0 ln2_ge0.
by rewrite addr_ge0// invr_ge0 ltW // subr_gt0.
Qed.

(*
Lemma expand_interval_closed_to_open (a b c d : R) :
  a < b -> b < c -> c < d -> forall x, b <= x <= c -> a < x < d.
Proof.
move=> ? ? ? x /andP [? ?]; apply/andP; split;
  [exact: (@lt_le_trans _ _ b)|exact: (@le_lt_trans _ _ c)].
Qed.

Lemma expand_internal_closed_to_closed (a b c d : R) :
  a <= b -> b < c -> c <= d -> forall x, b <= x <= c -> a <= x <= d.
Proof.
move=> ? ? ? ? /andP [? ?]; apply/andP; split;
  [exact: (@le_trans _ _ b)|exact: (@le_trans _ _ c)].
Qed.

Lemma expand_interval_open_to_open (a b c d : R) :
  a < b -> b < c -> c < d -> forall x, b < x < c -> a < x < d.
Proof.
move=> ? ? ? x /andP [? ?]; apply/andP; split;
  [exact: (@lt_trans _ _ b)|exact: (@lt_trans _ _ c)].
Qed.

Lemma expand_interval_open_to_closed (a b c d : R) :
  a <= b -> b < c -> c <= d -> forall x, b < x < c -> a <= x <= d.
Proof.
move=> ? ? ? x /andP [? ?]; apply/andP; split;
  [exact/ltW/(@le_lt_trans _ _ b)|exact/ltW/(@lt_le_trans _ _ c)].
Qed.
*)

Definition probR_itv (p : {prob R}) :
  itv.Itv.def R `[(ssrint.Posz 0), (ssrint.Posz 1)].
Proof.
apply (@itv.Itv.Def _ _ (p.~)).
rewrite /itv.Itv.itv_cond.
by rewrite in_itv /=; apply/andP; split.
Defined.

Lemma continuous_id (T : topologicalType) : continuous (@idfun T).
Proof. exact/continuousP. Qed.

Lemma continuous_log (x : R) : 0 < x -> {for x, continuous log}.
Proof. by move=> x0 y; exact/differentiable_continuous/differentiable_Log. Qed.

Lemma continuous_onem : continuous (@onem R).
Proof.
move=> ?; by apply: continuousB; [exact: cst_continuous | exact: continuous_id].
Qed.

Lemma continuous_H2 x : x \in `]0, 1[ -> {for x, continuous H2}.
Proof.
move=> x01; rewrite /H2.
have:= x01 => /[!in_itv] /= /andP [] x0 x1.
have->: (fun p : R => - (p * log p) - (1 - p) * log (1 - p)) =
        - (@idfun R * log) - @onem R * (log \o @onem R) by [].
apply: continuousD.
  apply: continuousN.
  apply: continuousM.
    exact: continuous_id.
  exact: continuous_log.
apply: continuousN.
apply: continuousM.
  exact: continuous_onem.
apply: continuous_comp.
  exact: continuous_onem.
apply: continuous_log.
exact: onem_gt0.
Qed.

End realType.
Arguments derivable_nH2 [R] v x.

Section Rdefinitions_R.

Let R := Rdefinitions.R.
Let H2 := @H2 R.
(*Local Notation H2 := (@H2 R).*)

From mathcomp Require Import -(notations) convex.

Lemma conv_conv (x y : R^o) (p : {prob R}) :
  x <| p |> y = mathcomp.analysis.convex.conv (probR_itv p)
                  (x : @convex.convex_realDomainType R)
                  (y : @convex.convex_realDomainType R).
Proof.
by rewrite avgRE /= /conv /isConvexSpace.conv /= /conv /= -!mulr_regl onemK.
Qed.

Import Reals.
Lemma concavity_of_entropy_x_le_y x y (t : {prob R}) :
  x \in `]0, 1[ -> y \in `]0, 1[ -> x < y ->
  concave_function_at H2 x y t.
Proof.
move=> x01 y01 xy.
have cnH2: {within `[x, y], continuous (- H2)}%classic.
  apply: continuous_in_subspaceT=> z; rewrite in_setE.
  have:= x01.
  move/subset_itv_oo_oc/andP=> [] /subset_itvr=> + _ => /[apply].
  have:= y01.
  move/subset_itv_oo_co/andP=> [] _ /subset_itvl /[apply] z01.
  exact/continuousN/continuous_H2.
have zxy01 z : z \in `]x, y[ -> z \in `]0, 1[.
  have:= y01 => /[1!in_itv] /= /andP [] _ /ltW.
  have:= x01 => /[1!in_itv] /= /andP [] /ltW + _.
  by move=> /subset_itvW /[apply] /[apply] /(_ false true).
apply/RNconcave_function_at.
rewrite /convex_function_at /leconv /=.
apply/RleP.
rewrite !conv_conv !coqRE.
have:= @mathcomp.analysis.convex.second_derivative_convex R (fun z => - (H2 z)) x y.
apply.
- move=> z xzy.
  have/zxy01 z01: z \in `]x, y[ by rewrite in_itv.
  by rewrite DDnH2E// DDnH2_nonneg.
- have:= cnH2 => /(continuous_within_itvP _ xy).
  by case.
- have:= cnH2 => /(continuous_within_itvP _ xy).
  by case.
- move=> z /zxy01 z01.
  exact/derivable_nH2.
- move=> z /zxy01 z01.
  apply: ex_derive.
  rewrite (boolp.funext (deriveN _)).
  apply: is_deriveN.
  have:= svalP (sig_derive1_nH2 x) x01 => /@derive_val.


  apply: ex_derive.

  have:= svalP (sig_derive1_nDH2 z) => /(_ z01) /@ex_derive /=.
  congr (derive.derivable _ z 1).
  apply: boolp.funext=> ? /=.
  rewrite -nDH2E//.

  
- exact: ltW.

rewrite !in_itv /= => /andP [H0x Hx1] /andP [H0y Hy1] Hxy.
apply RNconcave_function_at.
set Df := fun z : R => log z - log (1 - z).
have f_is_derive1 (z : R) :
  z \in `[x, y] -> is_derive z 1 (fun x0 => - H2 x0) (fun x0 => - H2' x0).
(*
have @f_derive : {in `[x, y], forall z, derivable (fun x0 => - H2 x0) z 1}.
  move=> z; rewrite in_itv /= => /andP [] ? ?.
  apply/derivableN/derivable_H2.
  rewrite inE unitiE.
  apply/(@expand_interval_closed_to_open 0 x y 1)=> //.
  exact/andP.
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
*)
have DDf_nonneg : forall z, x <= z <= y -> 0 <= DDf z.
  move => z [Hxz Hzy].
  have Hz : 0 < z by apply /ltR_leR_trans; [exact H0x| exact Hxz].
  have H1z : 0 < 1 - z by apply /subR_gt0 /leR_ltR_trans; [exact Hzy| exact Hy1].
  by apply/or_introl/invR_gt0/mulR_gt0; [exact/mulR_gt0 | exact/ln2_gt0].
exact: (@second_derivative_convexf_pt _ _ _ _ Df _ _ DDf).
Qed.

Lemma concavity_of_entropy : concave_function_in uniti H2.
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
by apply/R_convex_function_atN /concavity_of_entropy_x_le_y => //; apply/classical_sets.set_mem.
Qed.

End Rdefinitions_R.

End entropy_concave_alternative_proof_binary_case.

Section mutual_information_concave.
Local Open Scope fdist_scope.
Variables (A B : finType) (W : A -> {fdist B}).
Hypothesis B_not_empty : (0 < #|B|)%nat.

Lemma mutual_information_concave :
  concave_function (fun P : {fdist A} => mutual_info (P `X W)).
Proof.
suff : concave_function
  (fun P : {fdist A} => let PQ := fdistX (P `X W) in `H PQ`1 - cond_entropy PQ).
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
suff : affine (fun x : {fdist A} => cond_entropy (fdistX (x `X W))).
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
