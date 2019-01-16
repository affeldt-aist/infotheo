From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import Reals Fourier Ranalysis_ext Lra.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.
Require Import entropy proba cproba convex binary_entropy_function.
Require Import log_sum divergence.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* wip: concavity of relative entropy and of mutual information *)

Local Open Scope proba_scope.
Local Open Scope reals_ext_scope.
Local Open Scope convex_scope.

Section convex_dist_pair.
Variables (A : finType) (f : dist A -> dist A -> R).
Definition convex_dist_pair := forall (p1 p2 q1 q2 : dist A) (t : prob),
  p1 << q1 -> p2 << q2 ->
  f (p1 <| t |> p2) (q1 <| t |> q2) <= f p1 q1 <| t |> f p2 q2.
End convex_dist_pair.
Definition concave_dist_pair (A : finType) (f : dist A -> dist A -> R) :=
  convex_dist_pair (fun a b => - f a b).

Local Open Scope entropy_scope.

Section entropy_log_div.
Variables (A : finType) (p : dist A) (n : nat) (A_not_empty : #|A| = n.+1).
Let u := Uniform.d A_not_empty.

Local Open Scope divergence_scope.

Lemma entropy_log_div : entropy p = log #|A|%:R - D(p || u).
Proof.
rewrite /entropy /div.
evar (RHS : A -> R).
have H : forall a : A, p a * log (p a / u a) = RHS a.
  move => a.
  move : (pos_f_ge0 (pmf p) a) => [H|H].
  - rewrite Uniform.dE.
    change (p a * log (p a / / #|A|%:R)) with (p a * log (p a * / / #|A|%:R)).
    have H0 : 0 < #|A|%:R by rewrite A_not_empty ltR0n.
    have H1 : #|A|%:R <> 0 by apply gtR_eqF.
    rewrite invRK // logM // mulRDr.
    by instantiate (RHS := fun a => p a * log (p a) + p a * log #|A|%:R).
  - by rewrite /RHS -H /= 3!mul0R add0R.
have H0 : \rsum_(a in A) p a * log (p a / u a) = \rsum_(a in A) RHS a.
  move : H; rewrite /RHS => H.
  exact: eq_bigr.
rewrite H0 /RHS.
rewrite big_split /=.
rewrite -big_distrl /=.
rewrite (pmf1 p) mul1R.
by rewrite -addR_opp oppRD addRC -addRA Rplus_opp_l addR0.
Qed.
End entropy_log_div.

(* convexity of relative entropy *)
Section divergence_convex.
Variables (A : finType) (n : nat) (A_not_empty : #|A| = n.+1).

Local Open Scope divergence_scope.

(* thm 2.7.2 *)
Lemma div_convex : convex_dist_pair (@div A).
Proof.
(* TODO: clean *)
move=> p1 p2 q1 q2 t pq1 pq2.
rewrite /Conv /= /avg /= (* TODO *).
rewrite 2!big_distrr /= -big_split /= /div.
rewrite rsum_setT [in X in _ <= X]rsum_setT.
apply ler_rsum => a _.
rewrite 2!Conv2Dist.dE.
case/boolP : (q2 a == 0) => [|] q2a0.
  rewrite (eqP q2a0) !(mul0R,mulR0,add0R).
  have p2a0 : p2 a == 0.
    apply/eqP.
    move/dominatesP in pq2.
    exact/pq2/eqP.
  rewrite (eqP p2a0) !(mulR0,addR0,mul0R).
  case/boolP : (q1 a == 0) => [|] q1a0.
    have p1a0 : p1 a == 0.
      apply/eqP.
      move/dominatesP in pq1.
      exact/pq1/eqP.
    rewrite (eqP p1a0) !(mulR0,mul0R); exact/leRR.
  case/boolP : (t == `Pr 0) => [/eqP /=|] t0.
    rewrite t0 !mul0R; exact/leRR.
  apply/Req_le.
  rewrite mulRA; congr (_ * _ * log _).
  field.
  split; exact/eqP.
case/boolP : (q1 a == 0) => [|] q1a0.
  rewrite (eqP q1a0) !(mul0R,mulR0,add0R).
  have p1a0 : p1 a == 0.
    apply/eqP.
    move/dominatesP in pq1.
    exact/pq1/eqP.
  rewrite (eqP p1a0) !(mulR0,addR0,mul0R,add0R).
  case/boolP : (t.~ == 0) => [/eqP ->|t0].
    rewrite !mul0R; exact/leRR.
  apply/Req_le.
  rewrite mulRA; congr (_ * _ * log _).
  field.
  split; exact/eqP.
set h : dist A -> dist A -> 'I_2 -> R := fun p1 p2 => [eta (fun=> 0) with
  ord0 |-> t * p1 a, lift ord0 ord0 |-> t.~ * p2 a].
have hdom : ((h p1 p2) << (h q1 q2)).
  apply/dominatesP => i.
  rewrite /h /=; case: ifPn => _.
  rewrite mulR_eq0 => -[->|/eqP].
  by rewrite mul0R.
  by rewrite (negbTE q1a0).
  case: ifPn => // _.
  rewrite mulR_eq0 => -[->|/eqP].
  by rewrite mul0R.
  by rewrite (negbTE q2a0).
set f : 'I_2 -> R := h p1 p2.
set g : 'I_2 -> R := h q1 q2.
have h0 : forall p1 p2 i, 0 <= h p1 p2 i.
  move=> ? ? ?; rewrite /h /=.
  case: ifPn => [_ | _]; first by apply mulR_ge0; [exact/prob_ge0|exact/dist_ge0].
  case: ifPn => [_ |  _]; [|exact/leRR].
  apply/mulR_ge0; [apply/onem_ge0; exact/prob_le1|exact/dist_ge0].
move: (@log_sum _ setT (mkPosFun (h0 p1 p2)) (mkPosFun (h0 q1 q2)) hdom).
rewrite /=.
have rsum_setT' : forall (f : 'I_2 -> R),
  \rsum_(i < 2) f i = \rsum_(i in [set: 'I_2]) f i.
  move=> f0; by apply eq_bigl => i; rewrite inE.
rewrite -!rsum_setT' !big_ord_recl !big_ord0 !addR0.
rewrite /h /=; move/leR_trans; apply.
apply/Req_le; congr (_ + _).
  case/boolP : (t == `Pr 0) => [/eqP ->|t0]; first by rewrite !mul0R.
  rewrite mulRA; congr (_ * _ * log _).
  field.
  split; exact/eqP.
case/boolP : (t.~ == 0) => [/eqP ->|t1]; first by rewrite !mul0R.
rewrite mulRA; congr (_ * _ * log _).
field.
split; exact/eqP.
Qed.

End divergence_convex.

Section entropy_concave.
Variable (A : finType).
Hypothesis A_not_empty : (0 < #|A|)%nat.
Let A_not_empty' : #|A| = #|A|.-1.+1.
Proof. by rewrite prednK. Qed.
Let u : {dist A} := Uniform.d A_not_empty'.

Local Open Scope divergence_scope.

(* thm 2.7.3 *)
Lemma entropy_concave : concave_function (fun P : dist A => `H P).
Proof.
rewrite /concave_function => p q t; rewrite /convex_function_at.
rewrite !(entropy_log_div _ A_not_empty') /=.
rewrite [in X in _ <= X]/Conv /= /avg /= (* TODO *).
rewrite oppRD oppRK 2!mulRN mulRDr mulRN mulRDr mulRN oppRD oppRK oppRD oppRK.
rewrite addRCA !addRA -2!mulRN -mulRDl (addRC _ t) onemKC mul1R -addRA leR_add2l.
move: (div_convex t (dom_by_uniform p A_not_empty') (dom_by_uniform q A_not_empty')).
by rewrite convmm.
Qed.

End entropy_concave.

Module entropy_concave_alternative_proof_binary_case.

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

Lemma expand_interval_open_to_closed a b c d :
  a <= b -> b < c -> c <= d -> forall x, b < x < c -> a <= x <= d.
Proof.
  move => Hab Hbc Hcd x [Hbx Hxc].
  by apply conj; [eapply Rle_trans|eapply Rle_trans]; [exact Hab|apply or_introl; exact Hbx|apply or_introl; exact Hxc|exact Hcd].
Qed.

Lemma concavity_of_entropy_x_le_y x y (t : prob) :
  open_unit_interval x -> open_unit_interval y -> x < y ->
  concave_function_at H2 x y t.
Proof.
move => [H0x Hx1] [H0y Hy1] Hxy.
eapply second_derivative_convexf_pt.
Unshelve.
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
  have Hz1zn0 : z * (1 - z) <> 0 by rewrite mulR_neq0.
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

Lemma concavity_of_entropy : concave_function_in open_unit_interval H2.
Proof.
rewrite /concave_function_in /concave_function_at => x y t Hx Hy.
(* wlogつかう. まず関係ない変数を戻し, *)
move : t.
(* 不等号をorでつないだやつを用意して *)
move : (Rtotal_order x y) => Hxy.
(* その不等号のひとつを固定してwlogする *)
wlog : x y Hx Hy Hxy / x < y.
  move => H.
  case Hxy; [apply H|] => //.
  case => [-> t|]; [exact/convex_function_atxx|].
  move => Hxy' t.
  apply: convex_function_sym => // t0.
  apply H => //.
  by apply or_introl.
by move => Hxy' t; apply concavity_of_entropy_x_le_y.
Qed.

End entropy_concave_alternative_proof_binary_case.

Require Import chap2.

Section mutual_information_concave.

Variables (A B : finType) (Q : A -> dist B).
Hypothesis B_not_empty : (0 < #|B|)%nat.

(* If Cond is statisfied, then the conditional probability is indeed Q *)
(*Lemma Cond_cproba (d : dist A) :
  forall a b, d a <> 0 ->
    \Pr_(Swap.d (ProdDist.d d Q))[[set b]|[set a]] = Q a b.
Proof.
move=> a b /eqP Hda.
rewrite (@channel.channel_cPr _ _ Q d a b Hda); congr cPr.
apply/dist_ext => -[b0 a0].
by rewrite !Swap.dE channel.JointDistChan.dE ProdDist.dE.
Qed.*)

Lemma mutual_information_concave :
  concave_function (fun P => MutualInfo.mi (CDist.make_joint P Q)).
Proof.
suff : concave_function (fun P => let PQ := Swap.d (CDist.make_joint P Q) in
                           `H (Bivar.fst PQ) - CondEntropy.h PQ).
  set f := fun _ => _. set g := fun _ => _.
  rewrite (FunctionalExtensionality.functional_extensionality f g) //.
  move=> d; rewrite {}/f {}/g /=.
  by rewrite -MutualInfo.miE2 -mi_sym.
apply concave_functionB.
- move: (entropy_concave B_not_empty) => H.
  move=> p q t /=.
  rewrite /convex_function_at.
  rewrite 3!Swap.fst.
  apply: leR_trans (H (Bivar.snd (CDist.make_joint p Q)) (Bivar.snd (CDist.make_joint q Q)) t).
  destruct t. rewrite /Conv /=. (* TODO *)
  rewrite -ProdDist.snd_convex; exact/leRR.
- suff : affine_function (fun x => CondEntropy.h (Swap.d (CDist.make_joint x Q))) by case.
  apply/affine_functionP => p q t /=.
  rewrite /CondEntropy.h /CondEntropy.h1.
  rewrite /Conv /= /avg /=.
  rewrite 2!big_distrr /= -big_split /=; apply eq_bigr => a _.
  rewrite !Swap.snd !Bivar.fstE !mulRN -oppRD; congr (- _).
  rewrite !big_distrr -big_split /=; apply eq_bigr => b _.
  rewrite !big_distrl !big_distrr -big_split /=; apply eq_bigr => b0 _.
  rewrite !ProdDist.dE /= Conv2Dist.dE /=.
  rewrite !(mulRA t) !(mulRA t.~).
  case/boolP: (t * p a == 0) => /eqP Hp.
    rewrite Hp.
    case/boolP: (t.~ * q a == 0) => /eqP Hq.
      rewrite Hq; field.
    rewrite !(mul0R,add0R).
    rewrite -CDist.E /=; last by rewrite Conv2Dist.dE Hp add0R.
    rewrite -CDist.E /= //; by move: Hq; rewrite mulR_neq0 => -[].
  case/boolP: (t.~ * q a == 0) => /eqP Hq.
    rewrite Hq !(mul0R,addR0).
    rewrite -CDist.E; last by rewrite Conv2Dist.dE Hq addR0.
    rewrite -CDist.E /= //; by move: Hp; rewrite mulR_neq0 => -[].
  rewrite -CDist.E; last first.
    rewrite /= Conv2Dist.dE paddR_eq0; [tauto | |].
    apply/mulR_ge0; [exact/prob_ge0 | exact/dist_ge0].
    apply/mulR_ge0; [apply/onem_ge0; exact/prob_le1 | exact/dist_ge0].
  rewrite -CDist.E; last by move: Hp; rewrite mulR_neq0 => -[].
  rewrite -CDist.E //=; last by move: Hq; rewrite mulR_neq0 => -[].
  field.
Qed.

End mutual_information_concave.

Module AffineConvexType.
Require Import R_for_mathcomp.

Definition I t := 0 <= t <= 1.

Lemma Isym t : I t -> I t.~.
Proof. by case => *; split; [apply onem_ge0|apply onem_le1]. Qed.

Lemma I0 : I 0.
Proof. split; [exact /leRR|exact (leR0n 1)]. Qed.

Lemma Imul t u : I t -> I u -> I (t * u).
Proof.
  move => [] /leRP t0 /leRP t1 [] /leRP u0 /leRP u1; split.
  - by apply /leRP /mulR_ge0.
  - rewrite -[X in _ <= X]mulR1.
      by apply /leR_pmul; apply /leRP.
Qed.

(* mixture of convex set and convex space taken from nlab, and ConvexDist *)
Structure affineConvexType : Type :=
  AffineConvexType
    { car : Type;
      w (x y : car) (t : R) : I t -> car;
      w0 x y : w x y I0 = y;
      widem x t (H : I t) : w x x H = x;
      wscom x y t (H : I t) : w x y H = w y x (Isym H);
      wqassoc x y z p q r s 
              (Hp : I p) (Hq : I q) (Hr : I r) (Hs : I s) :
        p = r * s ->  s.~ = p.~ * q.~ -> 
        w x (w y z Hq) Hp = w (w x y Hr) z Hs;
      wproofirrelevant t (H H' : I t) x y : w x y H = w x y H'
    }.

Local Notation "x <| H |> y" := (w x y H) (format "x  <| H |>  y", at level 50).

Lemma w0' (T : affineConvexType) (x y : car T) (H : I 0) : x <| H |> y = y.
Proof. by rewrite (wproofirrelevant H I0) w0. Qed.

Lemma I1 : 0 <= 1 <= 1.
Proof. split; [exact (leR0n 1)|exact /leRR]. Qed.

Lemma wscom' (T : affineConvexType) (x y : car T) t (H : I t) (H' : I t.~) : x <| H |> y = y <| H' |> x.
Proof. by rewrite wscom (wproofirrelevant (Isym H) H'). Qed.

Lemma w1 (T : affineConvexType) (x y : car T) : x <| I1 |> y = x.
Proof.
  rewrite wscom'.
  - rewrite /onem subRR; exact I0.
  rewrite /onem subRR => H; by rewrite (wproofirrelevant H I0) w0.
Qed.

Lemma w1' (T : affineConvexType) (x y : car T) (H : I 1) : x <| H |> y = x.
Proof.  by rewrite (wproofirrelevant H I1) w1. Qed.

Lemma wcom (T : affineConvexType) (x1 y1 x2 y2 : car T)
      p q :  forall (Hp : I p) (Hq : I q), 
    (x1 <|Hq|> y1) <|Hp|> (x2 <|Hq|> y2) = (x1 <|Hp|> x2) <|Hq|> (y1 <|Hp|> y2).
Proof.
rewrite /I => Hp Hq.
case/boolP : (p == 0 :> R) => [|]/eqP p0; first by subst p; rewrite !w0'.
case/boolP : (q == 0 :> R) => [|]/eqP q0; first by subst q; rewrite !w0'.
case/boolP : (p == 1 :> R) => [|]/eqP p1; first by subst p; rewrite !w1'.
case/boolP : (q == 1 :> R) => [|]/eqP q1; first by subst q; rewrite !w1'.
set r := p * q.
have pq1 : p * q != 1.
  apply/eqP => pq1; have {p1} : p < 1 by lra.
  rewrite -pq1 mulRC -ltR_pdivr_mulr; last lra.
  rewrite divRR; [lra | exact/eqP].
have r1 : r < 1.
  rewrite ltR_neqAle; split; [exact/eqP|rewrite -(mulR1 1); apply/leR_pmul; tauto].
set s := (p - r) / (1 - r).
rewrite -(@wqassoc T x1 _ _ r s); last 2 first.
  by rewrite mulRC.
  rewrite /onem {}/s; field; by apply/eqP; rewrite subR_eq0 eq_sym.
  split.
  - apply divR_ge0; last by rewrite subR_gt0.
    rewrite subR_ge0 /r -{2}(mulR1 p); apply/leR_wpmul2l; tauto.
  - rewrite /s leR_pdivr_mulr ?subR_gt0 // mul1R leR_add2r; tauto.
  exact (Imul Hp Hq).
move=> Hs Hr.
rewrite (wscom' y1); [exact (Isym Hs)|].
move=> Hs'.
set t := s.~ * q.
have t01 : 0 <= t <= 1 by exact (Imul (Isym Hs) Hq).
have t1 : t < 1.
  rewrite ltR_neqAle; split; last tauto.
  move=> t1; subst t.
  have {q1} : q < 1 by lra.
    rewrite -t1 -ltR_pdivr_mulr; last by lra.
    rewrite divRR; [rewrite /I in Hs'; lra | exact/eqP].
rewrite -(@wqassoc T x2 _ _ t p.~) => //; last 2 first.
  by rewrite mulRC.
  rewrite 2!onemK /t /onem /s /r; field.
  by apply/eqP; rewrite subR_eq0 eq_sym.
  exact (Isym Hp).
move=> Hp'.
rewrite (@wqassoc T x1 _ _ _ _ p.~.~ q); last 2 first.
  by rewrite onemK.
  rewrite /t /onem /s /r; field; by apply/eqP; rewrite subR_eq0 eq_sym.
  by rewrite onemK.
move=> Hp''.
rewrite (wscom' y2 y1).
move: Hp''; rewrite onemK => Hp''.
by rewrite !(wproofirrelevant Hp'' Hp).
Qed.

End AffineConvexType.

Section gconvex_dist.
Section def.
Variables (A : finType) (B : finType) (f : (A -> dist B) -> R).
Definition gconvex_dist := forall (p q : A -> dist B) (t : prob),
  f (fun x => p x <| t |> q x) <= f p <| t |> f q.
End def.
End gconvex_dist.

Section mutual_information_convex.

Variables (A B : finType) (P : dist A).

Local Open Scope divergence_scope.

Lemma mutual_information_convex :
  gconvex_dist (fun (Q : A -> dist B) => MutualInfo.mi (CDist.make_joint P Q)).
Proof.
move=> p1yx p2yx t.
pose p1' := CDist.mkt P p1yx.
pose p2' := CDist.mkt P p2yx.
pose p1xy := CDist.joint_of p1'.
pose p2xy := CDist.joint_of p2'.
pose p1 := Bivar.snd p1xy.
pose p2 := Bivar.snd p2xy.
pose plambdayx := fun a : A => p1yx a <| t |> p2yx a.
pose plambda' := CDist.mkt P plambdayx.
pose plambdaxy := CDist.joint_of plambda'.
pose plambday := Bivar.snd plambdaxy.
pose qlambdaxy := P `x plambday.
pose q1xy := P `x p1.
pose q2xy := P `x p2.
have -> : MutualInfo.mi (CDist.make_joint P (fun x : A => p1yx x <| t |> p2yx x)) =
       D(plambdaxy || qlambdaxy).
  rewrite MutualInfo.miE /div pair_big /=.
  apply eq_bigr => -[a b] _ /=.
  congr (_ * log (_ / _)).
  rewrite /qlambdaxy.
  by rewrite ProdDist.dE /= /CDist.make_joint /CDist.joint_of /= ProdDist.fst; congr (_ * _).
have -> : qlambdaxy = q1xy <| t |> q2xy.
  apply/dist_ext => -[a b].
  rewrite !ProdDist.dE !Conv2Dist.dE /=.
  rewrite /q1xy /q2xy !ProdDist.dE /=.
  rewrite /p1 /plambday.
  rewrite !Bivar.sndE !big_distrr /= -big_split /=.
  apply eq_bigr => a0 _.
  rewrite /plambdaxy /= !ProdDist.dE /= /p1xy /plambdayx.
  rewrite Conv2Dist.dE /=.
  field.
have -> : plambdaxy = p1xy <| t |> p2xy.
  apply/dist_ext => -[a b].
  rewrite !ProdDist.dE !Conv2Dist.dE /=.
  rewrite /p1xy /p2xy !ProdDist.dE /=.
  field.
have -> : MutualInfo.mi (CDist.make_joint P p1yx) = D(p1xy || q1xy).
  rewrite MutualInfo.miE /div pair_big /=.
  apply eq_bigr => -[a b] _ /=.
  congr (_ * log (_ / _)).
  by rewrite /q1xy ProdDist.dE /CDist.make_joint /CDist.joint_of /= ProdDist.fst.
have -> : MutualInfo.mi (CDist.make_joint P p2yx) = D(p2xy || q2xy).
  rewrite MutualInfo.miE /div pair_big /=.
  apply eq_bigr => -[a b] _ /=.
  congr (_ * log (_ / _)).
  by rewrite /q2xy ProdDist.dE /CDist.make_joint /CDist.joint_of /= ProdDist.fst.
apply: div_convex.
- apply/dominatesP => -[a b].
  rewrite /q1xy /p1xy ProdDist.dE /= mulR_eq0.
  rewrite /p1 /p1xy /CDist.joint_of => -[|].
    by rewrite ProdDist.dE => ->; rewrite mul0R.
  rewrite Bivar.sndE.
  move/prsumr_eq0P => -> // a0 _; exact/dist_ge0.
-  apply/dominatesP => -[a b].
  rewrite /q1xy /p1xy ProdDist.dE /= mulR_eq0.
  rewrite /p1 /p1xy /CDist.joint_of => -[|].
    by rewrite ProdDist.dE => ->; rewrite mul0R.
  rewrite Bivar.sndE.
  move/prsumr_eq0P => -> // a0 _; exact/dist_ge0.
Qed.

End mutual_information_convex.
