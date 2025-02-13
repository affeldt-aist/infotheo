(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssrnum ssrint ssralg matrix.
From mathcomp Require Import lra ring archimedean.
From mathcomp Require Import mathcomp_extra Rstruct reals exp.
Require Import ssr_ext ssralg_ext bigop_ext realType_ext realType_ln.
Require Import fdist proba entropy aep typ_seq channel.

(**md**************************************************************************)
(* # Jointly typical sequences                                                *)
(*                                                                            *)
(* Documented in:                                                             *)
(* - Reynald Affeldt, Manabu Hagiwara, and Jonas Sénizergues. Formalization   *)
(*   of Shannon's theorems. Journal of Automated Reasoning,  53(1):63--103,   *)
(*   2014                                                                     *)
(*                                                                            *)
(* ```                                                                        *)
(*      JTS P W n epsilon == epsilon-jointly typical sequences of size n for  *)
(*                           an input distribution P and  a channel W         *)
(*                           JTS(n,e) is a subset of TS_{P,W}(n,e) such that  *)
(*                           (x,y) \in JTS(n,e) <->                           *)
(*                           x \in TS_P(n,e) /\ y \in TS_{PW}(n,e)            *)
(* ```                                                                        *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(* ```                                                                        *)
(*                JTS_sup == Upper-bound for the set of jointly typical       *)
(*                           sequences                                        *)
(*                  JTS_1 == when they are very long, the jointly typical     *)
(*                           sequences coincide with the typical sequences of *)
(*                           the joint distribution                           *)
(*  non_typical_sequences == the probability of the same event (joint         *)
(*                           typicality) taken over the product distribution  *)
(*                           of the inputs and the out-puts considered        *)
(*                           independently tends to 0 as n gets large         *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Declare Scope jtyp_seq_scope.
Reserved Notation "'`JTS'".

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope typ_seq_scope.
Local Open Scope fdist_scope.
Local Open Scope channel_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.
#[local] Definition R := Rdefinitions.R.

Import Order.Theory GRing.Theory Num.Theory.

Section joint_typ_seq_definition.
Variables A B : finType.
Variable P : {fdist A}.
Variable W : `Ch(A, B).
Variable n : nat.
Variable epsilon : R.

Definition jtyp_seq (t : 'rV[A * B]_n) :=
  [&& typ_seq P epsilon (rV_prod t).1,
      typ_seq (`O(P , W)) epsilon (rV_prod t).2 &
      typ_seq ((P `X W)) epsilon t].

Definition set_jtyp_seq : {set 'rV[A * B]_n} := [set tab | jtyp_seq tab].

Local Notation "'`JTS'" := (set_jtyp_seq).

Lemma typical_sequence1_JTS x : prod_rV x \in `JTS ->
  2 `^ (- n%:R * (`H P + epsilon)) <= (P `^ n)%fdist x.1 <= 2 `^ (- n%:R * (`H P - epsilon)).
Proof. by rewrite inE /jtyp_seq prod_rVK => /and3P[] /andP[-> ->]. Qed.

Lemma typical_sequence1_JTS' x : prod_rV x \in `JTS ->
  2 `^ (- n%:R * (`H (`O( P , W)) + epsilon)) <= (`O( P , W) `^ n)%fdist x.2 <=
  2 `^ (- n%:R * (`H (`O( P , W)) - epsilon)).
Proof. by rewrite inE /jtyp_seq prod_rVK => /and3P[_] /andP[-> ->]. Qed.

End joint_typ_seq_definition.

Notation "'`JTS'" := (set_jtyp_seq) : jtyp_seq_scope.
Local Open Scope jtyp_seq_scope.

Section jtyp_seq_upper.
Variables (A B : finType) (P : {fdist A}) (W : `Ch(A, B)).
Variable n : nat.
Variable epsilon : R.

Lemma JTS_sup :
  #| `JTS P W n epsilon|%:R <= 2 `^ (n%:R * (`H(P , W) + epsilon)%channel).
Proof.
have : #|`JTS P W n epsilon|%:R <= #|`TS ((P `X W)) n epsilon|%:R :> R.
  suff : `JTS P W n epsilon \subset `TS ((P `X W)) n epsilon.
    by rewrite ler_nat => /subset_leq_card.
  apply/subsetP => tab.
  by rewrite /set_jtyp_seq inE /jtyp_seq inE => /and3P[].
by move/le_trans; apply; exact: TS_sup.
Qed.

End jtyp_seq_upper.

Section jtyp_seq_transmitted.
Variables (A B : finType) (P : {fdist A}) (W : `Ch(A, B)).
Variable epsilon : R.
Definition Nup (x : R) := `| Num.floor x |.+1.
Lemma Nup_gt x : x < (Nup x)%:R.
Proof.
apply: (lt_le_trans (lt_succ_floor x)).
by rewrite /Nup -intrD1 -natr1 lerD // natr_absz ler_int ler_norm.
Qed.

Definition JTS_1_bound :=
  maxn (Nup (aep_bound P (epsilon / 3)))
 (maxn (Nup (aep_bound (`O(P , W)) (epsilon / 3)))
       (Nup (aep_bound ((P `X W)) (epsilon / 3)))).

Variable n : nat.
Hypothesis He : 0 < epsilon.

Lemma JTS_1 : (JTS_1_bound <= n)%nat ->
  1 - epsilon <= Pr ((P `X W) `^ n)%fdist (`JTS P W n epsilon).
Proof.
have : (JTS_1_bound <= n)%nat ->
  Pr ( ((P `^ n)%fdist `X (W ``^ n)) )
    [set x | x.1 \notin `TS P n epsilon] +
  Pr ( ((P `^ n)%fdist `X (W ``^ n)) )
    [set x | x.2 \notin `TS (`O(P , W)) n epsilon] +
  Pr ( ((P `^ n)%fdist `X  (W ``^ n)))
    [set x | prod_rV x \notin `TS ( (P `X W) ) n epsilon] <= epsilon.
  have H1 : forall n, Pr ((P `X W) `^ n)%fdist [set x | (rV_prod x).1 \notin `TS P n epsilon ] <=
    Pr (P `^ n)%fdist [set x | x \notin `TS P n (epsilon / 3)].
    move=> m.
    move: (set_typ_seq_incl P m (ltW He)) => Hincl.
    rewrite (Pr_DMC_fst P W (fun x => x \notin `TS P m epsilon)).
    apply/subset_Pr/subsetP => i /=; rewrite !inE.
    apply contra.
    by move/subsetP : Hincl => /(_ i); rewrite !inE.
  have {H1}HnP : forall n, (Nup (aep_bound P (epsilon / 3)) <= n)%N ->
    Pr ((P `X W) `^ n)%fdist [set x | (rV_prod x).1 \notin `TS P n epsilon ] <= epsilon /3.
    move=> m Hm.
    apply: le_trans; first exact: (H1 m).
    have m_prednK : m.-1.+1 = m by rewrite prednK // (leq_trans _ Hm).
    have : 1 - (epsilon / 3) <= Pr (P `^ m)%fdist (`TS P m (epsilon / 3)).
      rewrite -m_prednK.
      apply: Pr_TS_1.
      - by rewrite divr_gt0.
      - rewrite m_prednK.
        move: Hm; rewrite -(ler_nat R); exact/le_trans/ltW/Nup_gt.
    rewrite lerBlDr addrC -lerBlDr; apply: le_trans.
    by rewrite Pr_to_cplt setCK.
  have H1 m :
    Pr ((P `X W) `^ m)%fdist [set x | (rV_prod x).2 \notin `TS ( `O(P , W) ) m epsilon ] <=
    Pr ( (`O( P , W) ) `^ m)%fdist (~: `TS ( `O( P , W) ) m (epsilon / 3)).
    have Hincl := set_typ_seq_incl (`O(P , W)) m (ltW He).
    rewrite Pr_DMC_out.
    apply/subset_Pr/subsetP => i /=; rewrite !inE.
    apply contra.
    move/subsetP : Hincl => /(_ i).
    by rewrite !inE.
  have {H1}HnPW m : (Nup (aep_bound (`O(P , W)) (epsilon / 3)) <= m)%nat ->
    Pr ((P `X W) `^ m)%fdist [set x | (rV_prod x).2 \notin `TS (`O(P , W)) m epsilon] <= epsilon /3.
    move=> Hm.
    apply: le_trans; first exact: (H1 m).
    have m_prednK : m.-1.+1 = m by rewrite prednK // (leq_trans _ Hm).
    have : 1 - epsilon / 3 <= Pr ((`O(P , W)) `^ m)%fdist (`TS (`O(P , W)) m (epsilon / 3)).
      rewrite -m_prednK.
      apply: Pr_TS_1.
      - by rewrite divr_gt0.
      - move: Hm.
        rewrite m_prednK -(ler_nat R).
        exact/le_trans/ltW/Nup_gt.
    rewrite lerBlDr addrC -lerBlDr; apply: le_trans.
    by rewrite Pr_to_cplt setCK.
  have H1 m : Pr ((P `X W) `^ m)%fdist (~: `TS ((P `X W)) m epsilon) <=
    Pr ((P `X W) `^ m)%fdist (~: `TS ((P `X W)) m (epsilon / 3)).
    have Hincl := set_typ_seq_incl ((P `X W)) m (ltW He).
    apply/subset_Pr/subsetP => /= v; rewrite !inE.
    apply contra.
    by move/subsetP : Hincl => /(_ v); by rewrite !inE.
  have {H1}HnP_W m : (Nup (aep_bound ((P `X W)) (epsilon / 3)) <= m)%nat ->
    Pr ((P `X W) `^ m)%fdist (~: `TS ((P `X W)) m epsilon) <= epsilon /3.
    move=> Hm.
    apply: le_trans; first exact: (H1 m).
    have m_prednK : m.-1.+1 = m by rewrite prednK // (leq_trans _ Hm).
    have : 1 - epsilon / 3 <= Pr ((P `X W) `^ m)%fdist (`TS (P `X W) m (epsilon / 3)).
      rewrite -m_prednK; apply: Pr_TS_1.
      - by rewrite divr_gt0.
      - move: Hm; rewrite m_prednK -(ler_nat R).
        exact/le_trans/ltW/Nup_gt.
    rewrite lerBlDr addrC -lerBlDr; apply: le_trans.
    by rewrite Pr_to_cplt setCK.
  move=> Hn.
  rewrite [in X in _ <= X](_ : epsilon = epsilon / 3 + epsilon / 3 + epsilon / 3); last by field.
  move: Hn; rewrite 2!geq_max => /andP[Hn1 /andP[Hn2 Hn3]].
  rewrite !Pr_DMC_rV_prod.
  apply lerD; first by apply lerD; [exact: HnP | exact: HnPW].
  apply: le_trans; last exact/HnP_W/Hn3.
  by apply/eqW; congr Pr; apply/setP => /= tab; rewrite !inE rV_prodK.
move=> Hn_Pr Hn.
suff H : Pr ((P `X W) `^ n)%fdist (~: `JTS P W n epsilon) <= epsilon.
  rewrite -(Pr_cplt ((P `X W) `^ n)%fdist (`JTS P W n epsilon)).
  by rewrite lerBlDr lerD2l.
apply (@le_trans _ _ (Pr ((P `X W) `^ n)%fdist
                    ([set x | ((rV_prod x).1 \notin `TS P n epsilon)] :|:
                    ([set x | ((rV_prod x).2 \notin `TS (`O( P , W)) n epsilon)] :|:
                    (~: `TS (P `X W) n epsilon))))).
  by apply/eqW; congr Pr; apply/setP => xy;  rewrite !inE 2!negb_and orbA.
apply: le_trans; last exact: Hn_Pr.
apply (@le_trans _ _ (
 Pr ((P `X W) `^ n)%fdist [set x | (rV_prod x).1 \notin `TS P n epsilon] +
 Pr ((P `X W) `^ n)%fdist ([set x | ((rV_prod x).2 \notin `TS (`O( P , W)) n epsilon)] :|:
                      (~: `TS ((P `X W)) n epsilon)))).
  exact: le_Pr_setU.
rewrite -addrA !Pr_DMC_rV_prod lerD2l //; apply: le_trans (le_Pr_setU _ _ _).
by apply/eqW; congr Pr; apply/setP => t; rewrite !inE rV_prodK.
Qed.

End jtyp_seq_transmitted.

Section non_typicality.
Variables (A B : finType) (P : {fdist A}) (W : `Ch(A, B)) (n : nat) (epsilon : R).

Lemma non_typical_sequences : Pr ((P `^ n) `x ((`O(P , W)) `^ n))%fdist
  [set x | prod_rV x \in `JTS P W n epsilon] <= 2 `^ (- n%:R * (`I(P, W) - 3 * epsilon)).
Proof.
rewrite /Pr /=.
apply (@le_trans _ _ (\sum_(i | i \in `JTS P W n epsilon)
    (2 `^ (- n%:R * (`H P - epsilon)) * 2 `^ (- n%:R * (`H( P `o W ) - epsilon))))) => /=.
  rewrite (reindex_onto (fun y => prod_rV y) (fun x => rV_prod x)) /=; last first.
    by move=> ? ?; rewrite rV_prodK.
  apply: leR_sumRl => i; rewrite inE => iJTS.
  - rewrite fdist_prodE ler_pM //.
      by case/andP: (typical_sequence1_JTS iJTS).
    by case/andP: (typical_sequence1_JTS' iJTS).
  - by rewrite mulr_ge0 ?powR_ge0.
  - by rewrite prod_rVK eqxx andbC.
rewrite (_ : \sum_(_ | _) _ =
  #| `JTS P W n epsilon|%:R *
  2 `^ (- n%:R * (`H P - epsilon)) * 2 `^ (- n%:R * (`H( P `o W) - epsilon)));
  last by rewrite big_const iter_addr addr0 -mulr_natl mulrA.
apply (@le_trans _ _ (2 `^ (n%:R * (`H( P , W )%channel + epsilon)) *
  2 `^ (- n%:R * (`H P - epsilon)) * 2 `^ (- n%:R * (`H( P `o W ) - epsilon)))).
  by rewrite !ler_wpM2r ?powR_ge0 // JTS_sup.
apply/eqW.
rewrite -!powRD; try by rewrite (@eqr_nat R 2 0) implybT.
rewrite /mutual_info_chan !mulrDr !mulrNN; congr exp.powR.
by rewrite (_ : 3 * epsilon = epsilon + epsilon + epsilon) //; field.
Qed.

End non_typicality.
