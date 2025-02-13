(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix ring lra.
From mathcomp Require Import Rstruct reals exp.
Require Import ssr_ext bigop_ext ssralg_ext realType_ext realType_ln.
Require Import num_occ fdist proba entropy channel divergence types jtypes.
Require Import jfdist_cond.

(**md**************************************************************************)
(* # Conditional divergence                                                   *)
(******************************************************************************)

Reserved Notation "P '|-' V '<<' W" (at level 5, V, W at next level).
Reserved Notation "P '|-' V '<<b' W" (at level 5, V, W at next level).
Reserved Notation "'D(' V '||' W '|' P ')'"
  (at level 50, V, W, P at next level).

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope ring_scope.
Local Open Scope entropy_scope.
Local Open Scope channel_scope.
Local Open Scope divergence_scope.
Local Open Scope num_occ_scope.
Local Open Scope types_scope.

Import Order.TTheory GRing.Theory Num.Theory.

Section conditional_dominance.
Variables (A B : finType) (V W : `Ch(A, B)) (P : {fdist A}).

Definition cdom_by := forall a, P a != 0 -> V a `<< W a.

Lemma dom_by_cdom_by : (P `X V) `<< (P `X W) <-> cdom_by.
Proof.
split; [move/dominatesP => H | move=> H; apply/dominatesP].
- move=> a p_not_0; apply/dominatesP => b; move: (H (a, b)).
  rewrite fdist_prodE /= => H0 H1.
  move: H0; rewrite H1 mulr0 => /(_ erefl)/eqP.
  rewrite fdist_prodE/= [X in _ == X -> _](_ : _ = 0%:R)//.
  by rewrite mulf_eq0 (negbTE p_not_0) orFb => /eqP.
- case=> a p_not_0 b; move: {H}(H a) => H.
  rewrite fdist_prodE /=.
  have [->|H1] := eqVneq (P a) 0; first by rewrite mul0r.
  move: {H}(H H1) => /dominatesP ->; first by rewrite mulr0.
  move/eqP : b; by rewrite fdist_prodE mulf_eq0 /= (negbTE H1) orFb => /eqP.
Qed.

End conditional_dominance.

Notation "P '|-' V '<<' W" := (cdom_by V W P) : divergence_scope.
Notation "P '|-' V '<<b' W" := ([forall a, (P a != 0) ==> V a `<<b W a])
  : divergence_scope.

Section joint_dom.
Variables (A B : finType) (V W : `Ch(A, B)) (P : {fdist A}).

Lemma dominates_prodl : P |- V << W -> (P `X V) `<< (P `X W).
Proof.
move=> V_dom_by_W /=; apply/dominatesP => ab Hab.
have := FDist.ge0 P ab.1; rewrite le_eqVlt => /predU1P[/esym|] Hab1.
- by rewrite fdist_prodE Hab1 mul0r.
- rewrite fdist_prodE in Hab.
  rewrite fdist_prodE (dominatesE (V_dom_by_W _ _)) ?mulr0 //.
  + by rewrite gt_eqF//.
  + move/eqP: Hab; rewrite mulf_eq0 => -/orP[|/eqP//].
    by move: Hab1 => /[swap] /eqP ->; rewrite ltxx.
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
  apply eq_bigr => a _; rewrite big_distrr//=.
  by apply: eq_bigr => b _; rewrite mulrC.
rewrite pair_bigA big_mkcond /=.
apply eq_bigr => -[a b] /= _.
rewrite fdist_prodE /= (mulrC (P a)) [in RHS]mulrAC.
have [->|Pa0] := eqVneq (P a) 0; first by rewrite !mulr0.
congr *%R.
have [->|Vab0] := eqVneq (V a b) 0; first by rewrite !mul0r.
congr *%R.
have Wab0 : W a b != 0 := dominatesEN (V_dom_by_W Pa0) Vab0.
rewrite fdist_prodE /=.
by rewrite -(mulrA _ (P a)) invfM (mulrA (P a)) divff// mul1r.
Qed.

Lemma cdiv_ge0 : 0 <= D(V || W | P).
Proof. by rewrite cdiv_is_div_joint_dist //; exact/div_ge0/dominates_prodl. Qed.

Lemma cdiv0P : D(V || W | P) = 0 <-> P `X V = P `X W.
Proof. by rewrite cdiv_is_div_joint_dist; exact/div0P/dominates_prodl. Qed.

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
rewrite mulrA.
rewrite {1}/jcPr.
rewrite fdistX2 fdist_prod1 Pr_set1.
have [H|H] := eqVneq (R a) 0.
  by rewrite H mulrA fdist_prodE H !mul0r/=.
congr (_ * log _).
  by rewrite setX1 Pr_set1 fdistXE fdist_prodE /=; field.
rewrite /jcPr !setX1 !Pr_set1 !fdistXE !fdistX2.
have [H'|H'] := eqVneq ((R `X Q) (a, b)) 0.
  have : (R `X P) (a, b) = 0 by move/dominatesP : PQ => ->.
  rewrite fdist_prodE /= => /eqP; rewrite mulf_eq0 => -/predU1P[|/eqP ->].
    by move/eqP : H; tauto.
  by rewrite !(mulr0,mul0r).
rewrite 2!fdist_prod1 /=.
set x := R _.
set y := (R `X P _).
set z := (R `X Q _).
field.
by rewrite H'.
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
  \prod_(a : A) \prod_(b : B) W a b ^+ N(a, b | tuple_of_row x, tuple_of_row y).
Proof.
transitivity (\prod_(a : A) \prod_(b : B) \prod_(i < n)
  if (a == x ``_ i) && (b == y ``_ i) then W `(y ``_ i | x ``_ i) else 1).
  rewrite pair_big exchange_big /= DMCE.
  apply eq_bigr => i _.
  rewrite (bigD1 (x ``_ i, y ``_ i)) //= 2!eqxx andbT.
  rewrite big1; first by rewrite mulr1.
  case=> a b /=.
  rewrite xpair_eqE negb_and.
  case/orP.
  - by move/negbTE => ->.
  - move/negbTE => ->; by rewrite andbF.
apply eq_bigr => a _; apply eq_bigr => b _.
rewrite num_co_occ_alt -sum1_card.
rewrite (@big_morph _ _ (fun x => W a b ^+ x) 1 *%R O addn) //; last first.
  by move=> * /=; rewrite exprD.
rewrite [in RHS]big_mkcond.
apply eq_bigr => i _.
case: ifP.
  case/andP => /eqP Ha /eqP Hb.
  by rewrite inE 2!tnth_mktuple -Ha -Hb 2!eqxx /= expr1.
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
  W ``(y | x) = 2 `^ (- n%:R * (D(V || W | P) + `H(V | P))).
Proof.
rewrite dmc_cdiv_cond_entropy_aux cond_entropy_chanE2.
rewrite /cdiv /entropy -big_split /=.
rewrite big_distrr/= powR2sum.
apply eq_bigr => a _.
rewrite big_morph_oppr.
rewrite /div /= -mulrDr mulrA -big_split /=.
rewrite big_distrr/= powR2sum.
apply eq_bigr => b _.
have [Pa0|Pa0] := eqVneq (type.d P a) 0.
  move: Hy; rewrite in_set => /forallP/(_ a)/forallP/(_ b)/eqP => ->.
  move: (HV); rewrite in_set => /cond_type_equiv/(_ _ Hx a).
  move: Hx; rewrite in_set => /forallP/(_ a)/eqP; rewrite {}Pa0 => HPa sumB.
  move: HPa; rewrite -sumB => /esym/eqP; rewrite mulf_eq0 => -/orP[/eqP|/eqP]; last first.
    move=> /eqP.
    by rewrite invr_eq0 (_ : 0 = 0%:R)// eqr_nat (negbTE Hn).
  move=> /eqP; rewrite (_ : 0 = 0%:R)// eqr_nat.
  rewrite sum_nat_eq0 => /forall_inP/(_ b erefl)/eqP => H; apply/eqP.
  by rewrite H expr0 !(mulr0,mul0r) powRr0.
have [Wab0|Wab0] := eqVneq (W a b) 0.
  move: (dominatesE (W0_V0 Pa0) Wab0) => nullV.
  suff -> : N(a, b| tuple_of_row x, tuple_of_row y) = O.
    by rewrite nullV 2!mul0r oppr0 addr0 mulr0 powRr0.
  move: Hy; rewrite in_set => /forallP/(_ a)/forallP/(_ b)/eqP => ->.
  by rewrite jtype_0_jtypef.
rewrite -{1}(@LogK _ 2 (W a b))//; last first.
  by rewrite -fdist_gt0.
have [Vab0|Vab0] := eqVneq (V a b) 0.
  suff -> : N( a, b | [seq x ``_ i | i <- enum 'I_n], [seq y ``_ i | i <- enum 'I_n]) = O.
    by rewrite expr0 Vab0 !(mulr0,mul0r,addr0,add0r,oppr0,powRr0).
  move: Hy; rewrite in_set => /forallP/(_ a)/forallP/(_ b)/eqP => ->.
  by rewrite jtype_0_jtypef.
rewrite -powR_mulrn ?powR_ge0// -powRrM//.
congr (_ `^ _).
rewrite -mulrN -mulrDr mulrA.
rewrite logM; last 2 first.
  by rewrite -fdist_gt0.
  by rewrite invr_gt0 -fdist_gt0.
rewrite logV; last by rewrite -fdist_gt0.
rewrite addrAC subrr add0r.
rewrite mulrN 3!mulNr opprK.
rewrite mulrC.
congr (_ * log _).
move: Hy; rewrite in_set => /forallP/(_ a)/forallP/(_ b)/eqP => ->.
move: (HV); rewrite in_set => /cond_type_equiv => /(_ _ Hx a) sumB.
move: Hx; rewrite in_set => /forallP/(_ a)/eqP => HPa.
rewrite (JType.c_f V) /=.
case: ifPn => [/eqP|] HP.
- rewrite HPa -sumB HP mul0r mulr0 mul0r.
  move/eqP : HP; rewrite sum_nat_eq0 => /forallP/(_ b).
  by rewrite implyTb => /eqP ->.
- rewrite HPa -sumB (mulrCA (n%:R)) mulfV ?mulr1; last first.
    by rewrite pnatr_eq0.
  by rewrite mulrCA mulfV ?mulr1 // pnatr_eq0.
Qed.

End dmc_cdiv_cond_entropy.

Section cdiv_specialized.
Variables (A B : finType) (n : nat).
Variable P : P_ n ( A ).
Variable V : P_ n ( A , B ).
Variable W : `Ch*(A, B).

Definition exp_cdiv :=
  if (type.d P) |- V <<b W
  then 2 `^ (- n%:R * D(V || W | P))
  else 0.

Lemma exp_cdiv_left (H : P |- V << W) : exp_cdiv = 2 `^ (- n%:R * D(V || W | P)).
Proof.
rewrite /exp_cdiv.
suff : (type.d P) |- V <<b W by move=> ->.
apply/forallP => a; apply/implyP => Pa0.
by apply/forall_inP => b /eqP Wab; rewrite (dominatesE (H _ Pa0)).
Qed.

Lemma exp_cdiv_ge0 : 0 <= exp_cdiv.
Proof. by rewrite /exp_cdiv; case: ifPn => // _; rewrite powR_ge0. Qed.

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
  W ``(y | x) = exp_cdiv P V W * 2 `^ (- n%:R * `H(V | P)).
Proof.
rewrite /exp_cdiv.
case : ifP => Hcase.
- rewrite -powRD; last by rewrite pnatr_eq0 implybT.
  rewrite -mulrDr.
  apply dmc_cdiv_cond_entropy => //.
  (* TODO: lemma? *)
  move=> a Pa; apply/dominatesP => b /eqP Wab.
  by move: Hcase => /forallP/(_ a)/implyP/(_ Pa)/forallP/(_ b)/implyP/(_ Wab)/eqP.
- rewrite mul0r.
  move: Hcase => /negbT; rewrite negb_forall; case/existsP => a.
  rewrite negb_imply.
  case/andP => Pa.
  rewrite negb_forall_in ; move/existsP ; case => b.
  case/andP=> Wab H.
  rewrite dmc_cdiv_cond_entropy_aux.
  rewrite pair_big /= (bigD1 (a, b)) //=; apply/eqP.
  rewrite mulf_eq0; apply/orP; left.
  move/eqP in Wab; rewrite Wab.
  rewrite expr0n.
  move: Htb ; rewrite in_set => /forallP/(_ a)/forallP/(_ b)/eqP ->.
  move: H => /=.
  rewrite (JType.c_f V) /=.
  move: (Vctyp).
  rewrite in_set.
  move/cond_type_equiv => /(_ _ Hta a) ->.
  move: Hta; rewrite in_set => /forallP/(_ a)/eqP => HPa.
  case: ifPn => Nax; last first.
    rewrite mulf_eq0 negb_or invr_eq0.
    by rewrite !pnatr_eq0 Nax andbT => /negbTE ->.
  exfalso.
  move/eqP : Pa; apply.
  by rewrite HPa (eqP Nax) mul0r.
Qed.

End dmc_cdiv_cond_entropy_spec.
