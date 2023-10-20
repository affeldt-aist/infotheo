(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg finset fingroup finalg matrix.
Require Import Reals.
From mathcomp Require Import Rstruct.
Require Import ssrR Reals_ext ssr_ext ssralg_ext logb Rbigop ln_facts.
Require Import num_occ fdist entropy channel divergence types jtypes.
Require Import proba jfdist_cond.

(******************************************************************************)
(*                        Conditional divergence                              *)
(******************************************************************************)

Reserved Notation "P '|-' V '<<' W" (at level 5, V, W at next level).
Reserved Notation "P '|-' V '<<b' W" (at level 5, V, W at next level).
Reserved Notation "'D(' V '||' W '|' P ')'"
  (at level 50, V, W, P at next level).

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.
Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope channel_scope.
Local Open Scope divergence_scope.
Local Open Scope num_occ_scope.
Local Open Scope types_scope.

Section conditional_dominance.
Variables (A B : finType) (V W : `Ch(A, B)) (P : {fdist A}).

Definition cdom_by := forall a, P a != 0 -> V a `<< W a.

Lemma dom_by_cdom_by : (P `X V) `<< (P `X W) <-> cdom_by.
Proof.
split; [move/dominatesP => H | move=> H; apply/dominatesP].
- move=> a p_not_0; apply/dominatesP => b; move: (H (a, b)).
  rewrite fdist_prodE /= => H0 H1.
  move: H0; rewrite H1 -RmultE mulR0 => /(_ erefl)/eqP.
  by rewrite fdist_prodE mulR_eq0' /= (negbTE p_not_0) orFb => /eqP.
- case=> a p_not_0 b; move: {H}(H a) => H.
  rewrite fdist_prodE /=.
  have [->|H1] := eqVneq (P a) 0; first by rewrite -RmultE mul0R.
  move: {H}(H H1) => /dominatesP ->; first by rewrite -RmultE mulR0.
  move/eqP : b; by rewrite fdist_prodE mulR_eq0' /= (negbTE H1) orFb => /eqP.
Qed.

End conditional_dominance.

Notation "P '|-' V '<<' W" := (cdom_by V W P) : divergence_scope.
Notation "P '|-' V '<<b' W" := ([forall a, (P a != 0) ==> V a `<<b W a])
  : divergence_scope.

Section joint_dom.
Variables (A B : finType) (V W : `Ch(A, B)) (P : {fdist A}).

(* TODO: rename *)
Lemma joint_dominates : P |- V << W -> (P `X V) `<< (P `X W).
Proof.
move=> V_dom_by_W /=; apply/dominatesP => ab Hab.
case/RleP/leR_eqVlt : (FDist.ge0 P ab.1) => [/esym|] Hab1.
- by rewrite fdist_prodE Hab1 -RmultE mul0R.
- rewrite fdist_prodE in Hab.
  rewrite fdist_prodE (dominatesE (V_dom_by_W _ _)) -?RmultE ?mulR0 //.
  + exact/gtR_eqF.
  + move: Hab; rewrite mulR_eq0 => -[|//].
    by move: (gtR_eqF _ _ Hab1) => /eqP.
Qed.

End joint_dom.

Section conditional_divergence.
Variables (A B : finType) (V W : `Ch(A, B)) (P : {fdist A}).
Definition cdiv := \sum_(a : A) P a * D(V a || W a).
End conditional_divergence.

Notation "'D(' V '||' W '|' P ')'" := (cdiv V W P) : divergence_scope.

Section conditional_divergence_prop.
Variables (A B : finType) (V W : `Ch(A, B)) (P : {fdist A}).

Hypothesis V_dom_by_W : P |- V << W.

Lemma cdiv_is_div_joint_dist : D(V || W | P) = D((P `X V) || (P `X W)).
Proof.
rewrite (_ : D(V || W | P) = \sum_(a in A) (\sum_(b in B)
    V a b * (log (V a b / W a b)) * P a)); last first.
  apply eq_bigr => a _.
  by rewrite -(big_morph _ (morph_mulRDl _) (mul0R _)) mulRC.
rewrite pair_bigA big_mkcond /=.
apply eq_bigr => -[a b] /= _.
rewrite fdist_prodE /= -RmultE (mulRC (P a)) [in RHS]mulRAC.
case/boolP : (P a == 0) => [/eqP -> | Pa0]; first by rewrite !mulR0.
congr (_ * _).
case/boolP : (V a b == 0) => [/eqP -> | Vab0]; first by rewrite !mul0R.
congr (_ * _).
have Wab0 : W a b != 0 := dominatesEN (V_dom_by_W Pa0) Vab0.
rewrite fdist_prodE /= {2}/Rdiv -RmultE (mulRC _ (W a b)) (invRM (W a b)) //.
by rewrite -mulRA (mulRCA (P a)) mulRV // mulR1.
Qed.

Lemma cdiv_ge0 : 0 <= D(V || W | P).
Proof. rewrite cdiv_is_div_joint_dist //; exact/div_ge0/joint_dominates. Qed.

Lemma cdiv0P : D(V || W | P) = 0 <-> (P `X V) = (P `X W).
Proof. rewrite cdiv_is_div_joint_dist; exact/div0P/joint_dominates. Qed.

End conditional_divergence_prop.

Section conditional_divergence_vs_conditional_relative_entropy.
Local Open Scope divergence_scope.
Local Open Scope reals_ext_scope.
Variables (A B : finType) (P Q : A -> {fdist B}) (R : {fdist A}).

Lemma cond_relative_entropy_compat : R `X P `<< R `X Q ->
  cond_relative_entropy (R, P) (R, Q) = D(P || Q | R).
Proof.
move=> PQ.
rewrite /cond_relative_entropy cdiv_is_div_joint_dist; last exact/dom_by_cdom_by.
rewrite /div.
under eq_bigr do rewrite big_distrr /=.
rewrite pair_big /=; apply eq_bigr => -[a b] _ /=.
rewrite (_ : (R `X P) (a, b) = (R `X P) (a, b)); last by rewrite fdist_prodE.
rewrite (_ : (R `X Q) (a, b) = (R `X Q) (a, b)); last by rewrite fdist_prodE.
rewrite mulRA.
rewrite {1}/jcPr.
rewrite fdistX2 fdist_prod1 Pr_set1.
have [H|H] := eqVneq (R a) 0.
  by rewrite H mul0R fdist_prodE H -RmultE !mul0R/=.
congr (_ * log _).
  by rewrite setX1 Pr_set1 fdistXE fdist_prodE /=; field; exact/eqP.
rewrite /jcPr !setX1 !Pr_set1 !fdistXE !fdistX2.
have [H'|H'] := eqVneq ((R `X Q) (a, b)) 0.
  have : (R `X P) (a, b) = 0 by move/dominatesP : PQ => ->.
  rewrite fdist_prodE /= mulR_eq0 => -[| -> ].
    by move/eqP : H; tauto.
  rewrite -RmultE.
  by rewrite !(mulR0,mul0R,div0R).
by rewrite 2!fdist_prod1 /=; field; split; exact/eqP.
Qed.

End conditional_divergence_vs_conditional_relative_entropy.

Section dmc_cdiv_cond_entropy.
Variables (A B : finType) (W : `Ch(A, B)).
Variable n : nat.
Variable P : P_ n ( A ).
Variable V : P_ n ( A , B ).
Variable x : 'rV[A]_n.
Variable y : 'rV[B]_n.

Local Open Scope vec_ext_scope.

Lemma dmc_cdiv_cond_entropy_aux : W ``(y | x) =
  \prod_(a : A) \prod_(b : B) W a b ^ N(a, b | tuple_of_row x, tuple_of_row y).
Proof.
transitivity (\prod_(a : A) \prod_(b : B) \prod_(i < n)
  if (a == x ``_ i) && (b == y ``_ i) then W `(y ``_ i | x ``_ i) else 1).
  rewrite pair_big exchange_big /= DMCE.
  apply eq_bigr => i _.
  rewrite (bigD1 (x ``_ i, y ``_ i)) //= 2!eqxx andbT.
  rewrite big1; first by rewrite mulR1.
  case=> a b /=.
  rewrite xpair_eqE negb_and.
  case/orP.
  - by move/negbTE => ->.
  - move/negbTE => ->; by rewrite andbF.
apply eq_bigr => a _; apply eq_bigr => b _.
rewrite num_co_occ_alt -sum1_card.
rewrite (@big_morph _ _ (fun x => W a b ^ x) 1 Rmult O addn) //; last first.
  move=> * /=; by rewrite -pow_add.
rewrite [in RHS]big_mkcond.
apply eq_bigr => i _.
case: ifP.
  case/andP => /eqP Ha /eqP Hb.
  by rewrite inE 2!tnth_mktuple -Ha -Hb 2!eqxx /= mulR1.
move/negbT.
rewrite negb_and inE 2!tnth_mktuple.
case/orP => /negbTE.
  by rewrite eq_sym => ->.
by rewrite andbC eq_sym => ->.
Qed.

Local Close Scope tuple_ext_scope.

Hypothesis W0_V0 : P |- V << W.
Hypothesis Hx : tuple_of_row x \in T_{P}.
Hypothesis HV : V \in \nu^{B}(P).
Hypothesis Hy : tuple_of_row y \in V.-shell (tuple_of_row x).
Hypothesis Hn : n != O.

(** Expression of the probability transition matrix of a DMC using
   the conditional divergence and the condition entropy *)

Lemma dmc_cdiv_cond_entropy :
  W ``(y | x) = exp2 (- INR n * (D(V || W | P) + `H(V | P))).
Proof.
rewrite dmc_cdiv_cond_entropy_aux cond_entropy_chanE2.
rewrite /cdiv /entropy -big_split /=.
rewrite (big_morph _ (morph_mulRDr _) (mulR0 _)).
rewrite (big_morph _ morph_exp2_plus exp2_0).
apply eq_bigr => a _.
rewrite big_morph_oppR.
rewrite /div /= -mulRDr mulRA -big_split /=.
rewrite (big_morph _ (morph_mulRDr _) (mulR0 _)).
rewrite (big_morph _ morph_exp2_plus exp2_0).
apply eq_bigr => b _.
case/boolP : (type.d P a == 0) => [/eqP|] Pa0.
  move: Hy; rewrite in_set => /forallP/(_ a)/forallP/(_ b)/eqP => ->.
  move: (HV); rewrite in_set => /cond_type_equiv/(_ _ Hx a).
  move: Hx; rewrite in_set => /forallP/(_ a)/eqP; rewrite {}Pa0 => HPa sumB.
  move: HPa; rewrite -sumB => /esym; rewrite mulR_eq0 => -[/eqP|/eqP]; last first.
    by move/invR_eq0'; rewrite INR_eq0' (negbTE Hn).
  rewrite INR_eq0' sum_nat_eq0 => /forall_inP/(_ b erefl)/eqP => H; apply/eqP.
  by rewrite H pow_O !(mulR0,mul0R) exp2_0.
case/boolP : (W a b == 0) => [/eqP |] Wab0.
  move: (dominatesE (W0_V0 Pa0) Wab0) => nullV.
  suff -> : N(a, b| tuple_of_row x, tuple_of_row y) = O.
    by rewrite nullV 2!mul0R oppR0 addR0 mulR0 exp2_0.
  move: Hy; rewrite in_set => /forallP/(_ a)/forallP/(_ b)/eqP => ->.
  by rewrite jtype_0_jtypef.
rewrite -{1}(@logK (W a b)); last first.
  apply/RltP.
  by rewrite -fdist_gt0.
case/boolP : (V a b == 0) => [/eqP|] Vab0.
  suff -> : N( a, b | [seq x ``_ i | i <- enum 'I_n], [seq y ``_ i | i <- enum 'I_n]) = O.
    by rewrite pow_O Vab0 !(mulR0,mul0R,addR0,add0R,oppR0,exp2_0).
  move: Hy; rewrite in_set => /forallP/(_ a)/forallP/(_ b)/eqP => ->.
  by rewrite jtype_0_jtypef.
rewrite -exp2_pow; congr exp2.
rewrite -mulRN -mulRDr mulRA addR_opp -logDiv; last 2 first.
  apply/divR_gt0.
  apply/RltP.
  by rewrite -fdist_gt0//.
  apply/RltP.
  by rewrite -fdist_gt0//.
  apply/RltP.
  by rewrite -fdist_gt0//.
rewrite /Rdiv (mulRAC _ (/ _)) mulRV // mul1R logV -?fdist_gt0 //; last first.
  apply/RltP.
  by rewrite -fdist_gt0//.
rewrite mulRN 3!mulNR oppRK; congr (_ * log _).
move: Hy; rewrite in_set => /forallP/(_ a)/forallP/(_ b)/eqP => ->.
move: (HV); rewrite in_set => /cond_type_equiv => /(_ _ Hx a) sumB.
move: Hx; rewrite in_set => /forallP/(_ a)/eqP => HPa.
rewrite (JType.c_f V) /=.
case: ifPn => [/eqP|] HP.
- rewrite HPa -sumB HP div0R mulR0 mul0R.
  move/eqP : HP; rewrite sum_nat_eq0 => /forallP/(_ b).
  by rewrite implyTb => /eqP ->.
- rewrite HPa -sumB (mulRCA (INR n)) mulRV ?INR_eq0' // mulR1.
  by rewrite mulRCA mulRV ?mulR1 // INR_eq0'.
Qed.

End dmc_cdiv_cond_entropy.

Section cdiv_specialized.
Variables (A B : finType) (n : nat).
Variable P : P_ n ( A ).
Variable V : P_ n ( A , B ).
Variable W : `Ch*(A, B).

Definition exp_cdiv :=
  if (type.d P) |- V <<b W
  then exp2 (- INR n * D(V || W | P))
  else 0.

Lemma exp_cdiv_left (H : P |- V << W) : exp_cdiv = exp2 (-INR n * D(V || W | P)).
Proof.
rewrite /exp_cdiv.
suff : (type.d P) |- V <<b W by move=> ->.
apply/forallP => a; apply/implyP => Pa0.
apply/forall_inP => b /eqP Wab; by rewrite (dominatesE (H _ Pa0)).
Qed.

End cdiv_specialized.

Section dmc_cdiv_cond_entropy_spec.
Variables (A B : finType) (W : `Ch*(A, B)).
Variable n' : nat.
Let n := n'.+1.
Variable P : P_ n ( A ).
Variable V : P_ n ( A , B ).
Variable x : 'rV[A]_n.
Variable y : 'rV[B]_n.

Hypothesis Hta : tuple_of_row x \in T_{P}.
Hypothesis Vctyp : V \in \nu^{B}(P).
Hypothesis Htb : tuple_of_row y \in V.-shell (tuple_of_row x).

Lemma dmc_exp_cdiv_cond_entropy :
  W ``(y | x) = exp_cdiv P V W * exp2 (- INR n * `H(V | P)).
Proof.
rewrite /exp_cdiv.
case : ifP => Hcase.
- rewrite -ExpD -mulRDr.
  apply dmc_cdiv_cond_entropy => //.
  (* TODO: lemma? *)
  move=> a Pa; apply/dominatesP => b /eqP Wab.
  by move: Hcase => /forallP/(_ a)/implyP/(_ Pa)/forallP/(_ b)/implyP/(_ Wab)/eqP.
- rewrite mul0R.
  move: Hcase => /negbT; rewrite negb_forall; case/existsP => a.
  rewrite negb_imply.
  case/andP => Pa.
  rewrite negb_forall_in ; move/existsP ; case => b.
  case/andP=> Wab H.
  rewrite dmc_cdiv_cond_entropy_aux.
  rewrite pair_big /= (bigD1 (a, b)) //=.
  rewrite mulR_eq0; left.
  move/eqP in Wab; rewrite Wab.
  apply pow_i.
  apply/ltP.
  rewrite lt0n.
  move: Htb ; rewrite in_set => /forallP/(_ a)/forallP/(_ b)/eqP ->.
  move: H => /=.
  rewrite (JType.c_f V) /=.
  move: (Vctyp).
  rewrite in_set.
  move/cond_type_equiv => /(_ _ Hta a) ->.
  move: Hta; rewrite in_set => /forallP/(_ a)/eqP => HPa.
  case: ifPn => Nax; last first.
    by apply: contra => /eqP ->; rewrite div0R.
  exfalso.
  move/eqP : Pa; apply.
  by rewrite HPa (eqP Nax) div0R.
Qed.

End dmc_cdiv_cond_entropy_spec.
