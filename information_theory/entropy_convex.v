(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix interval.
From mathcomp Require Import ring.
From mathcomp Require boolp.
From mathcomp Require Import mathcomp_extra Rstruct reals interval_inference.
From mathcomp Require Import set_interval.
From mathcomp Require Import functions topology normedtype realfun derive exp.
From mathcomp Require convex.
Require Import ssr_ext ssralg_ext bigop_ext realType_ext realType_ln.
Require Import derive_ext fdist jfdist_cond entropy convex.
Require Import binary_entropy_function log_sum divergence.

(**md**************************************************************************)
(* # Elements of Information Theory (cont'd)                                  *)
(*                                                                            *)
(* This file contains a formalization of the section 2.7 of:                  *)
(* - Thomas M. Cover, Joy A. Thomas, Elements of Information Theory, Wiley,   *)
(*   2005                                                                     *)
(* Lemmas:                                                                    *)
(* - divergence restricted to dominated pairs is a convex function; it's      *)
(*   actually not a restriction since div is meaningful only on dominated     *)
(*   pairs (`convex_div`)                                                     *)
(* - convexity of relative entropy (thm 2.7.2) (`convex_relative_entropy`)    *)
(* - entropy is concave (thm 2.7.3) (`entropy_concave`)                       *)
(* - the mutual information is concave w.r.t. its first argument (thm 2.7.4)  *)
(*   (`mutual_information_concave`)                                           *)
(* - the mutual information is convex w.r.t. its second argument (thm 2.7.4)  *)
(*   (`mutual_information_convex`)                                            *)
(*                                                                            *)
(* ```                                                                        *)
(*           dom_pair A == type of dominated pairs, i.e., a pair of           *)
(*                         distributions (d, e) s.t. d << e                   *)
(*         avg_dom_pair == TODO                                               *)
(*     uncurry_dom_pair == TODO                                               *)
(* ```                                                                        *)
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
Variable R : realType.
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
move/eqP; rewrite paddr_eq0; [|exact/mulr_ge0 |exact/mulr_ge0].
rewrite !mulf_eq0=> /andP [/orP [/eqP ->|/eqP /xy ->]].
  rewrite onem0 (negPf (oner_neq0 _)) /= => /eqP /uv ->.
  by rewrite mul0r mulr0 addr0.
by case/orP=> [/eqP -> | /eqP /uv ->]; rewrite ?(mul0r, mulr0, addr0).
Qed.

Definition avg_dom_pair p (x y : dom_pair) : dom_pair :=
  let ab := proj1_sig x in
  let b_dom_a := proj2_sig x in
  let cd := proj1_sig y in
  let d_dom_c := proj2_sig y in
  exist _ (ab <| p |> cd) (dom_conv p b_dom_a d_dom_c).

Definition uncurry_dom_pair
  U (f : {fdist A} -> {fdist A} -> U) (x : dom_pair) : U^o :=
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

HB.instance Definition _ := @isConvexSpace.Build R dom_pair
  avg avg1 avgI avgC avgA.

End dominated_pair.

Section divergence_convex.
Local Open Scope divergence_scope.
Variable R : realType.
Variables A : finType.

Lemma convex_div : convex_function (uncurry_dom_pair (@div R A)).
Proof.
move=> [x Hx] [y Hy] p /=; rewrite /uncurry_dom_pair /=.
rewrite /convex_function_at/= avgRE 2!big_distrr /= -big_split /= /div.
have [->|p0] := eqVneq p 0%:pr.
  apply/eqW/eq_bigr=> a _ /=.
  by rewrite !conv0 mul0r add0r onem0 mul1r.
have [/onem_eq0 /val_inj ->|t0] := eqVneq (Prob.p p).~ 0.
  apply/eqW/eq_bigr=> a _ /=.
  by rewrite !conv1 mul1r onem1 mul0r addr0.
have quv (q u v : R) : q != 0 -> q * u / (q * v) = u / v.
  by move=> ?; rewrite invfM mulrACA divff// mul1r.
apply ler_sum => a _; rewrite 2!fdist_convE.
have [y2a0|y2a0] := eqVneq (y.2 a) 0.
  rewrite y2a0 (_ : y.1 a = 0) ?(mulR0,addR0,mul0R); last first.
    by move/dominatesP : Hy; exact.
  have [x2a0|x2a0] := eqVneq (x.2 a) 0.
    rewrite (_ : x.1 a = 0).
      by rewrite ?(mul0r,mulr0,addr0).
    exact/((dominatesP _ _).1 Hx).
  apply/eqW; rewrite !mulrA !(mul0r,mulr0,addr0); congr (_ * _ * ln _ * _).
  by rewrite quv.
have [x2a0|x2a0] := eqVneq (x.2 a) 0.
  rewrite x2a0 (_ : x.1 a = 0)// ?(mulR0,add0R,mul0R); last first.
    by move/dominatesP : Hx; exact.
  apply/eqW; rewrite !(mulrA, mulr0, mul0r, add0r); congr (_ * _ * ln _ * _).
  by rewrite quv.
set h : {fdist A} -> {fdist A} -> {ffun 'I_2 -> R} := fun p1 p2 => [ffun i =>
  [eta (fun=> 0) with ord0 |-> Prob.p p * p1 a, lift ord0 ord0 |-> (Prob.p p).~ * p2 a] i].
have hdom : h x.1 y.1 `<< h x.2 y.2.
  apply/dominatesP => i; rewrite /h /= !ffunE; case: ifPn => _ /eqP.
    by rewrite mulf_eq0 (negPf x2a0) orbF => /eqP ->; rewrite mul0r.
  case: ifPn => // _.
  by rewrite mulf_eq0 (negPf y2a0) orbF => /eqP ->; rewrite mul0r.
have h0 p1 p2 : [forall i, 0 <= h p1 p2 i].
  apply/forallP=> ?; rewrite /h /= ffunE.
  case: ifPn => [_ | _]; first exact/mulr_ge0.
  case: ifPn => [_ |]; last by move=>*; exact: lexx.
  by apply/mulr_ge0 => //; exact/onem_ge0/prob_le1.
have h01 (x0 : 'I_2) : 0 <= h x.1 y.1 x0.
  rewrite /= /h ffunE/=; case: ifPn => _; first exact: mulr_ge0.
  by case: ifPn => // _; exact: mulr_ge0.
have h02 (x0 : 'I_2) : 0 <= h x.2 y.2 x0.
  rewrite /= /h ffunE/=; case: ifPn => _; first exact: mulr_ge0.
  by case: ifPn => // _; exact: mulr_ge0.
have := @log_sum _ _ setT (h x.1 y.1) (h x.2 y.2) h01 h02 hdom.
rewrite !big_set !big_mkcond !big_ord_recl !big_ord0 /= !addr0.
rewrite /h /= !ffunE /= => /le_trans; apply.
apply/eqW; rewrite !mulrA.
by congr (_ * _ * ln _ * _ + _ * _ * ln _ * _); rewrite quv.
Qed.

Lemma convex_relative_entropy (p1 p2 q1 q2 : {fdist A}) (r : {prob R}) :
  p1 `<< q1 -> p2 `<< q2 ->
  D(p1 <| r |> p2 || q1 <| r |> q2) <= D(p1 || q1) <| r |> D(p2 || q2).
Proof.
move=> pq1 pq2.
exact/(convex_div (exist _ (p1, q1) pq1) (exist _ (p2, q2) pq2)).
Qed.

End divergence_convex.

Section entropy_concave.
Local Open Scope divergence_scope.
Variable R : realType.
Variable A : finType.
Hypothesis cardA_gt0 : (0 < #|A|)%nat.

Let cardApredS : #|A| = #|A|.-1.+1.
Proof. by rewrite prednK. Qed.

Lemma entropy_concave : concave_function (fun P : R.-fdist A => `H P).
Proof.
apply RNconcave_function => p q t; rewrite /convex_function_at.
rewrite !(entropy_log_div _ cardApredS) [in X in _ <= X]avgRE.
rewrite !opprD !mulrDr addrACA -mulrDl add_onemK mul1r lerD ?lexx// !opprK.
have := convex_relative_entropy t (dom_by_uniform p cardApredS)
                                  (dom_by_uniform q cardApredS).
by rewrite convmm.
Qed.

End entropy_concave.

Module entropy_concave_alternative_proof_binary_case.
Import classical_sets.

Section realType.

Variable R : realType.
Local Notation H2 := (@H2 R^o : R^o -> R^o).

From mathcomp Require Import -(notations) convex.

(* TODO: introduce two notations and make two conventions more symmetric *)
Definition prob_itv (p : {prob R}) :
  Itv.def (@Itv.num_sem R) (Itv.Real `[(ssrint.Posz 0), (ssrint.Posz 1)]).
Proof.
exists p.~ => /=; apply/andP; split.
  by rewrite num_real.
by rewrite in_itv /=; apply/andP; split.
Defined.

Lemma conv_conv (x y : R^o) (p : {prob R}) :
  x <| p |> y = mathcomp.analysis.convex.conv (prob_itv p) x y.
Proof.
by rewrite avgRE /= /conv /isConvexSpace.conv /= /conv /= -!mulr_regl onemK.
Qed.

Lemma concavity_of_entropy_x_le_y x y (t : {prob R}) :
  x \in `]0, 1[%classic -> y \in `]0, 1[%classic -> x < y ->
  concave_function_at H2 x y t.
Proof.
move=> x01 y01 xy.
have zxycc01 z : z \in `[x, y]%classic -> z \in `]0, 1[%classic.
  rewrite !inE.
  have:= x01; rewrite inE.
  move/subset_itv_oo_oc/andP=> [] /subset_itvr=> + _ => /[apply].
  have:= y01; rewrite inE.
  by move/subset_itv_oo_co/andP=> [] _ /subset_itvl /[apply] z01.
have zxyoo01 z : z \in `]x, y[%classic -> z \in `]0, 1[%classic.
  by move=> /[1!inE] zxy; apply: zxycc01; rewrite inE; apply/subset_itv_oo_cc.
have cnH2: {within `[x, y], continuous (- H2)}%classic.
  by apply: continuous_in_subspaceT=> z /zxycc01 /continuous_H2 /continuousN.
apply/RNconcave_function_at.
rewrite /convex_function_at /=.
rewrite !conv_conv.
have:= @mathcomp.analysis.convex.second_derivative_convex R (fun z => - (H2 z)) x y.
apply.
- move=> z xzy.
  have/zxyoo01 z01: z \in `]x, y[%classic by rewrite inE.
  by rewrite DDnH2E// DDnH2_nonneg.
- have:= cnH2 => /(continuous_within_itvP _ xy).
  by case.
- have:= cnH2 => /(continuous_within_itvP _ xy).
  by case.
- move=> z; rewrite -inE => /zxyoo01 z01.
  exact/derivable_nH2.
- move=> z; rewrite -inE => /zxyoo01 z01.
  exact/derivable_DnH2.
- exact: ltW.
Qed.

Lemma concavity_of_entropy : concave_function_in uniti H2.
Proof.
rewrite /concave_function_in => x y t Hx Hy.
apply: RNconcave_function_at.
(* wlogをつかう. convex_function_symのためにtを戻し, *)
move: t.
(* 不等号のひとつを固定してwlogする *)
wlog : x y Hx Hy / x < y.
  move=> H.
  (* 全順序性で場合分け *)
  have [xy|] := ltrP x y; first exact: H.
  (* x = y の場合はかんたん*)
  rewrite le_eqVlt=> /orP [/eqP ->|yx]; first exact: convex_function_atxx.
  (* 逆の場合は対称性を使う *)
  apply: convex_function_sym => // t0.
  exact: H.
by move=> *; exact/R_convex_function_atN /concavity_of_entropy_x_le_y.
Qed.

End realType.

End entropy_concave_alternative_proof_binary_case.

Section mutual_information_concave.
Local Open Scope fdist_scope.
Variables (R : realType) (A B : finType) (W : A -> R.-fdist B).
Hypothesis B_not_empty : (0 < #|B|)%nat.

Lemma mutual_information_concave :
  concave_function (fun P : {fdist A} => mutual_info (P `X W)).
Proof.
suff : concave_function
  (fun P : {fdist A} => let PQ := fdistX (P `X W) in `H PQ`1 - centropy PQ).
  set f := fun _ => _. set g := fun _ => _.
  suff -> : f = g by [].
  by rewrite boolp.funeqE => d; rewrite {}/f {}/g /= -mutual_infoE -mutual_info_sym.
apply: R_concave_functionB.
  have /RNconvex_function concave_H := @entropy_concave R B B_not_empty.
  apply: R_concave_functionN => p q t /=.
  rewrite /convex_function_at 3!fdistX1.
  apply: le_trans (concave_H (p `X W)`2 (q `X W)`2 t).
  under eq_bigr do rewrite fdist_prod2_conv.
  by rewrite lexx.
suff : affine (fun x : {fdist A} => centropy (fdistX (x `X W))).
  by case/affine_functionP.
move=> t p q.
rewrite /= avgRE /centropy /centropy1.
rewrite 2!big_distrr -big_split /=; apply eq_bigr => a _.
rewrite !fdistX2 !fdist_fstE !mulrN -opprD; congr (- _).
rewrite !big_distrr -big_split /=; apply eq_bigr => b _.
rewrite !big_distrl !big_distrr -big_split /=; apply eq_bigr => b0 _.
rewrite !fdist_prodE /= fdist_convE /= !(mulrA (Prob.p t)) !(mulrA (Prob.p t).~).
have [Hp|Hp] := eqVneq (Prob.p t * p a) 0.
  rewrite Hp ?(add0R,mul0R).
  have [->|/eqP Hq] := eqVneq ((Prob.p t).~ * q a) 0.
    by rewrite ?(mul0r,add0r).
  rewrite jcPr_fdistX_prod /=; last first.
    by rewrite fdist_convE Hp add0r.
  rewrite !mul0r !add0r; congr (_ * _).
  rewrite jcPr_fdistX_prod//; apply/eqP; move/eqP: Hq; apply: contraNN.
  by move/eqP->; rewrite mulr0.
have [Hq|Hq] := eqVneq ((Prob.p t).~ * q a) 0.
  rewrite Hq !(mul0r,addr0).
  rewrite jcPr_fdistX_prod; last first.
    by rewrite fdist_convE Hq addr0; apply/eqP.
  congr (_ * _).
  rewrite jcPr_fdistX_prod//; apply/eqP; move: Hp; apply: contraNN.
  by move/eqP->; rewrite mulr0.
rewrite jcPr_fdistX_prod; last first.
  rewrite fdist_convE.
  by apply/eqP; rewrite paddr_eq0// ?(negPf Hp) ?(negPf Hq)//; exact: mulr_ge0.
by rewrite !jcPr_fdistX_prod ?mulrDl//; apply/eqP;
   [move: Hq | move: Hp]; apply: contraNN => /eqP ->; rewrite mulr0.
Qed.

End mutual_information_concave.

Section mutual_information_convex.
Local Open Scope divergence_scope.
Local Open Scope fdist_scope.
Variables (R : realType) (A B : finType) (P : R.-fdist A).

Lemma mutual_information_convex :
  convex_function (fun W : A -> R.-fdist B => mutual_info (P `X W)).
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
  by field.
have -> : plambdaxy = p1xy <| t |> p2xy.
  apply/fdist_ext => -[a b].
  rewrite !fdist_prodE !fdist_convE /= /p1xy /p2xy !fdist_prodE /=.
  by field.
have -> : mutual_info (P `X p1yx) = D(p1xy || q1xy).
  rewrite mutual_infoE0 /div pair_big /=; apply: eq_bigr => -[a b] _ /=.
  congr (_ * log (_ / _)).
  by rewrite /q1xy fdist_prodE /= fdist_prod1.
have -> : mutual_info (P `X p2yx) = D(p2xy || q2xy).
  rewrite mutual_infoE0 /div pair_big /=; apply: eq_bigr => -[a b] _ /=.
  by congr (_ * log (_ / _)); rewrite /q2xy fdist_prodE fdist_prod1.
apply: convex_relative_entropy.
- apply/dominatesP => -[a b].
  rewrite /q1xy /p1xy fdist_prodE /=.
  move/eqP; rewrite mulf_eq0 /p1 /p1xy => /orP -[/eqP|/eqP].
    by rewrite fdist_prodE => ->; rewrite /= mul0r.
  by rewrite fdist_sndE => /psumr_eq0P ->.
- apply/dominatesP => -[a b].
  rewrite /q1xy /p1xy fdist_prodE /=.
  move/eqP; rewrite mulf_eq0 /p1 /p1xy => /orP -[/eqP|/eqP].
    by rewrite fdist_prodE => ->; rewrite mul0r.
  by rewrite fdist_sndE => /psumr_eq0P /= ->.
Qed.

End mutual_information_convex.
