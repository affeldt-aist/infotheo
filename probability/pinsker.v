(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import all_ssreflect.
Require Import Reals Lra.
Require Import ssrR Reals_ext Ranalysis_ext ssr_ext logb ln_facts bigop_ext.
Require Import Rbigop proba divergence variation_dist pinsker_function.
Require Import partition_inequality.

(******************************************************************************)
(*                       Pinsker's Inequality                                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope divergence_scope.
Local Open Scope variation_distance_scope.
Local Open Scope R_scope.
Local Open Scope reals_ext_scope.

Section Pinsker_2_bdist.

Variables p q : prob.
Variable A : finType.
Hypothesis card_A : #|A| = 2%nat.

Let P := Binary.d card_A p (Set2.a card_A).
Let Q := Binary.d card_A q (Set2.a card_A).

Hypothesis P_dom_by_Q : P << Q.

Lemma pinsker_fun_p_eq c : pinsker_fun p c q = D(P || Q) - c * d(P , Q) ^ 2.
Proof.
pose a := Set2.a card_A. pose b := Set2.b card_A.
set pi := P a.
set pj := P b.
set qi := Q a.
set qj := Q b.
have Hpi : pi = 1 - p by rewrite /pi /P Binary.dxx.
have Hqi : qi = 1 - q by rewrite /qi /= Binary.dxx.
have Hpj : pj = p.
  by rewrite /pj /= Binary.dE eq_sym (negbTE (Set2.a_neq_b card_A)).
have Hqj : qj = q.
  by rewrite /qj /= Binary.dE eq_sym (negbTE (Set2.a_neq_b card_A)).
transitivity (D(P || Q) - c * (`| p - q | + `| (1 - p) - (1 - q) |) ^ 2).
  rewrite /pinsker_fun /div Set2sumE -/a -/b -/pi -/pj -/qi -/qj Hpi Hpj Hqi Hqj.
  set tmp := (`| _ | + _) ^ 2.
  have -> : tmp = 4 * (p - q) ^ 2.
    rewrite /tmp (_ : 1 - p - (1 - q) = q - p); last by field.
    rewrite sqrRD (distRC q p) -mulRA -{3}(pow_1 `| p - q |).
    rewrite -expRS sqR_norm; ring.
  rewrite [X in _ = _ + _ - X]mulRA.
  rewrite [in X in _ = _ + _ - X](mulRC c).
  congr (_ - _).
  case/boolP : (p == `Pr 0) => [/eqP |] p0.
    rewrite p0 !mul0R subR0 addR0 add0R !mul1R /log (*_Log_1*) /Rdiv.
    case/boolP : (q == `Pr 1) => [/eqP |] q1.
      move/dominatesP : P_dom_by_Q => /(_ (Set2.a card_A)).
      rewrite -/pi -/qi Hqi q1 subRR => /(_ erefl).
      rewrite Hpi p0 subR0 => ?. exfalso. lra.
    rewrite /log LogM; last 2 first.
      lra.
      by apply/invR_gt0; rewrite subR_gt0 -prob_lt1.
      by rewrite LogV ?subR_gt0 -?prob_lt1 // Log_1.
  case/boolP : (q == `Pr 0) => [/eqP |] q0.
    move/dominatesP : P_dom_by_Q => /(_ (Set2.b card_A)).
    rewrite -/pj -/qj Hqj q0 => /(_ erefl).
    rewrite Hpj => abs.
    have : p == `Pr 0 by apply/eqP/prob_ext.
    by rewrite (negbTE p0).
  rewrite /div_fct /comp /= (_ : id q = q) //.
  case/boolP : (p == `Pr 1) => [/eqP |] p1.
    rewrite p1 subRR !mul0R /Rdiv /log LogM; last 2 first.
      done.
      apply/invR_gt0; by rewrite -prob_gt0.
      by rewrite Log_1 mul1R LogV // -?prob_gt0 // !(add0R,mul1R,addR0,sub0R).
  rewrite /log LogM //; last 2 first.
    by rewrite -prob_gt0.
    apply/invR_gt0; by rewrite -prob_gt0.
  rewrite LogV //; last first.
    by rewrite -prob_gt0.
  case/boolP : (q == `Pr 1) => [/eqP |] q1.
    move/dominatesP : P_dom_by_Q => /(_ (Set2.a card_A)).
    rewrite -/pi -/qi Hqi q1 subRR => /(_ erefl).
    rewrite Hpi subR_eq0 => abs.
    have : p == `Pr 1 by apply/eqP/prob_ext.
    by rewrite (negbTE p1).
  rewrite /Rdiv LogM ?subR_gt0 //; last 2 first.
    by rewrite -prob_lt1.
    by apply/invR_gt0; rewrite subR_gt0 -prob_lt1.
  rewrite LogV ?subR_gt0 //; last by rewrite -prob_lt1.
  ring.
congr (_ - _ * _).
by rewrite /var_dist Set2sumE // -/pi -/pj -/qi -/qj Hpi Hpj Hqi Hqj addRC.
Qed.

Lemma Pinsker_2_inequality_bdist : / (2 * ln 2) * d(P , Q) ^ 2 <= D(P || Q).
Proof.
set lhs := _ * _.
set rhs := D(_ || _).
rewrite -subR_ge0 -pinsker_fun_p_eq.
apply pinsker_fun_pos with A card_A => //.
split; [exact/ltRW/invR_gt0/mulR_gt0 | exact/leRR].
Qed.

End Pinsker_2_bdist.

Section Pinsker_2.

Variables (A : finType) (P Q : fdist A).
Hypothesis card_A : #|A| = 2%nat.
Hypothesis P_dom_by_Q : P << Q.

Lemma Pinsker_2_inequality : / (2 * ln 2) * d(P , Q) ^ 2 <= D(P || Q).
Proof.
move: (charac_bdist P card_A) => [r1 Hp].
move: (charac_bdist Q card_A) => [r2 Hq].
rewrite Hp Hq.
apply Pinsker_2_inequality_bdist.
by rewrite -Hp -Hq.
Qed.

End Pinsker_2.

Section Pinsker.

Variables (A : finType) (P Q : fdist A).
Hypothesis P_dom_by_Q : P << Q.

Local Notation "0" := (false).
Local Notation "1" := (true).

Lemma Pinsker_inequality : / (2 * ln 2) * d(P , Q) ^ 2 <= D(P || Q).
Proof.
pose A0 := [set a | Q a <b= P a].
pose A1 := [set a | P a <b Q a].
pose A_ := fun b => match b with 0 => A0 | 1 => A1 end.
have cov : A_ 0 :|: A_ 1 = setT.
  rewrite /= /A0 /A1.
  have -> : [set x | P x <b Q x] = ~: [set x | Q x <b= P x].
    apply/setP => a; by rewrite in_set in_setC in_set ltRNge'.
  by rewrite setUCr.
have dis : A_ 0 :&: A_ 1 = set0.
  rewrite /A_ /A0 /A1.
  have -> : [set x | P x <b Q x] = ~: [set x | Q x <b= P x].
    apply/setP => a; by rewrite in_set in_setC in_set ltRNge'.
  by rewrite setICr.
pose P_A := bipart dis cov P.
pose Q_A := bipart dis cov Q.
have step1 : D(P_A || Q_A) <= D(P || Q) by apply partition_inequality; exact P_dom_by_Q.
suff : / (2 * ln 2) * d(P , Q) ^2 <= D(P_A || Q_A).
  move=> ?; apply (@leR_trans (D(P_A || Q_A))) => //; exact/Rge_le.
have step2 : d( P , Q ) = d( P_A , Q_A ).
  rewrite /var_dist.
  transitivity (\sum_(a | a \in A0) `| P a - Q a | + \sum_(a | a \in A1) `| P a - Q a |).
    rewrite -big_union //; last by rewrite -setI_eq0 -dis /A_ setIC.
    apply eq_bigl => a; by rewrite cov in_set.
  transitivity (`| P_A 0 - Q_A 0 | + `| P_A 1 - Q_A 1 |).
    congr (_ + _).
    - rewrite /P_A /Q_A /bipart /= /bipart_pmf /=.
      transitivity (\sum_(a | a \in A0) (P a - Q a)).
        apply eq_bigr => a; rewrite /A0 in_set => /leRP Ha.
        by rewrite geR0_norm ?subR_ge0.
      rewrite big_split /= geR0_norm; last first.
        rewrite subR_ge0; rewrite !ffunE; apply ler_rsum => ?; by rewrite inE => /leRP.
      by rewrite -big_morph_oppR // 2!ffunE addR_opp.
    - rewrite /P_A /Q_A /bipart /= !ffunE /=.
      have [A1_card | A1_card] : #|A1| = O \/ (0 < #|A1|)%nat.
        destruct (#|A1|); [tauto | by right].
      + move/eqP : A1_card; rewrite cards_eq0; move/eqP => A1_card.
        by rewrite A1_card !big_set0 subRR normR0.
      + transitivity (\sum_(a | a \in A1) - (P a - Q a)).
          apply eq_bigr => a; rewrite /A1 in_set => Ha.
          rewrite ltR0_norm // subR_lt0; exact/ltRP.
        rewrite -big_morph_oppR // big_split /= ltR0_norm; last first.
          rewrite subR_lt0; apply ltr_rsum_support => // a.
          rewrite /A1 in_set; by move/ltRP.
        by rewrite -big_morph_oppR.
  by rewrite big_bool /= /bipart_pmf !ffunE /=.
rewrite step2.
apply (Pinsker_2_inequality card_bool).
(* TODO: lemma *)
apply/dominatesP => /= b.
rewrite !ffunE.
move/prsumr_eq0P => H.
transitivity (\sum_(a | a \in A_ b) 0%R).
  apply eq_bigr => // a ?; rewrite (dominatesE P_dom_by_Q) // H // => a' ?; exact/pos_ff_ge0.
by rewrite big_const iter_addR mulR0.
Qed.

Lemma Pinsker_inequality_weak : d(P , Q) <= sqrt (2 * D(P || Q)).
Proof.
rewrite -(sqrt_Rsqr (d(P , Q))); last exact/pos_var_dist.
apply sqrt_le_1_alt.
apply (@leR_pmul2l (/ 2)); first by apply invR_gt0; lra.
apply (@leR_trans (D(P || Q))); last first.
  rewrite mulRA mulVR // ?mul1R; [exact/leRR | exact/eqP/gtR_eqF].
apply: (leR_trans _ Pinsker_inequality).
rewrite (_ : forall x, Rsqr x = x ^ 2); last by move=> ?; rewrite /Rsqr /pow mulR1.
apply leR_wpmul2r; first exact: pow_even_ge0.
apply leR_inv => //; first exact/mulR_gt0.
rewrite -[X in _ <= X]mulR1.
apply leR_wpmul2l; first lra.
rewrite [X in _ <= X](_ : 1%R = ln (exp 1)); last by rewrite ln_exp.
apply ln_increasing_le; [lra | exact leR2e].
Qed.

End Pinsker.
