(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype tuple finfun bigop finset.
Require Import Reals Fourier.
Require Import Reals_ext Ranalysis_ext ssr_ext Rssr log2 ln_facts Rbigop proba.
Require Import divergence variation_dist pinsker_function partition_inequality.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope divergence_scope.
Local Open Scope variation_distance_scope.
Local Open Scope reals_ext_scope.

Section Pinsker_2_bdist.

Variables p q : R.
Hypothesis p01 : 0 <= p <= 1.
Hypothesis q01 : 0 <= q <= 1.
Variable A : finType.
Hypothesis card_A : #|A| = 2%nat.

Let P := bdist card_A p01.
Let Q := bdist card_A q01.

Hypothesis P_dom_by_Q : P << Q.

Lemma pinsker_fun_p_eq c : pinsker_fun p c q = D(P || Q) - c * d(P , Q) ^ 2.
Proof.
pose A_0 := Two_set.val0 card_A.
pose A_1 := Two_set.val1 card_A.
set pi := P A_0.
set pj := P A_1.
set qi := Q A_0.
set qj := Q A_1.
have Hpi : pi = 1 - p.
  rewrite /pi /= ffunE.
  case: ifP => //; by rewrite eqxx.
have Hqi : qi = 1 - q.
  rewrite /qi /= ffunE.
  case: ifP => //; by rewrite eqxx.
have Hpj : pj = p.
  rewrite /pj /= ffunE /Two_set.val1.
  case: ifP => //; by move/eqP/enum_val_inj.
have Hqj : qj = q.
  rewrite /qj /= ffunE /Two_set.val1.
  case: ifP => //; by move/eqP/enum_val_inj.
transitivity (D(P || Q) - c * (Rabs (p - q) + Rabs ((1 - p) - (1 - q))) ^ 2).
  rewrite /pinsker_fun /div /index_enum -enumT Two_set.enum big_cons big_cons big_nil addR0.
  rewrite -/pi -/pj -/qi -/qj Hpi Hpj Hqi Hqj.
  have -> : Two_set.val0 card_A \in A by apply enum_valP.
  have -> : Two_set.val1 card_A \in A by apply enum_valP.
  set tmp := (Rabs (_) + _) ^ 2.
  have -> : tmp = 4 * (p - q) ^ 2.
    rewrite /tmp (_ : 1 - p - (1 - q) = q - p); last by field.
    rewrite id_rem_plus.
    have -> : Rabs (q - p) = Rabs (p - q).
      rewrite -Rabs_Ropp.
      f_equal; by field.
    rewrite -mulRA (_ : Rabs _ * Rabs _ = (Rabs (p - q))^2); last by rewrite /= mulR1.
    rewrite Rabs_sq; by field.
  rewrite [X in _ = _ + _ - X]mulRA.
  rewrite [in X in _ = _ + _ - X](mulRC c).
  f_equal.
  case: p01 => Hp1 Hp2.
  case: q01 => Hq1 Hq2.
  case/Rle_lt_or_eq_dec : Hp1 => Hp1; last first.
    rewrite -Hp1 !mul0R Rminus_0_r addR0 add0R !mul1R log_1 /Rdiv.
    case/Rle_lt_or_eq_dec : Hq2 => Hq2; last first.
      move: (@P_dom_by_Q (Two_set.val0 card_A)).
      rewrite -/pi -/qi => abs.
      rewrite Hqi Hq2 Rminus_diag_eq // in abs.
      move: {abs}(abs Logic.eq_refl).
      rewrite Hpi -Hp1 Rminus_0_r.
      move=> abs. suff : False by done. fourier.
    rewrite log_mult; last 2 first.
      fourier.
      apply Rinv_0_lt_compat; fourier.
      rewrite log_Rinv; last by fourier.
      rewrite log_1; by field.
  case/Rle_lt_or_eq_dec : Hq1 => Hq1; last first.
    move: (@P_dom_by_Q (Two_set.val1 card_A)).
    rewrite -/pj -/qj Hqj -Hq1.
    move/(_ Logic.eq_refl).
    rewrite Hpj => abs.
    rewrite abs in Hp1.
    by apply Rlt_irrefl in Hp1.
  rewrite /div_fct /comp /= (_ : id q = q) //.
  case/Rle_lt_or_eq_dec : Hp2 => Hp2; last first.
    rewrite Hp2 Rminus_diag_eq // !mul0R /Rdiv log_mult; last 2 first.
      fourier.
      apply Rinv_0_lt_compat; fourier.
    rewrite log_1 Rmult_1_l log_Rinv //; by field.
  rewrite log_mult //; last by apply Rinv_0_lt_compat.
  rewrite log_Rinv //.
  case/Rle_lt_or_eq_dec : Hq2 => Hq2; last first.
    move: (@P_dom_by_Q (Two_set.val0 card_A)).
    rewrite -/pi -/qi Hqi -Hq2 Rminus_diag_eq //.
    move/(_ Logic.eq_refl).
    rewrite Hpi => abs.
    suff : False by done. fourier.
  rewrite /Rdiv log_mult; last 2 first.
    fourier.
    apply Rinv_0_lt_compat; fourier.
  rewrite log_Rinv; last by fourier.
  by field.
do 2 f_equal.
rewrite /var_dist /index_enum -enumT Two_set.enum big_cons big_cons big_nil addR0.
by rewrite -/pi -/pj -/qi -/qj Hpi Hpj Hqi Hqj addRC.
Qed.

Lemma Pinsker_2_inequality_bdist : / (2 * ln 2) * d(P , Q) ^ 2 <= D(P || Q).
Proof.
set lhs := _ * _.
set rhs := D(_ || _).
suff : 0 <= rhs - lhs by move=> ?; fourier.
rewrite -pinsker_fun_p_eq.
apply pinsker_fun_pos with p01 q01 A card_A => //.
split.
  apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat.
  fourier.
  by apply ln_2_pos.
by apply Rle_refl.
Qed.

End Pinsker_2_bdist.

Section Pinsker_2.

Variable A : finType.
Variables P Q : dist A.
Hypothesis card_A : #|A| = 2%nat.
Hypothesis P_dom_by_Q : P << Q.

Lemma Pinsker_2_inequality : / (2 * ln 2) * d(P , Q) ^ 2 <= D(P || Q).
Proof.
move: (charac_bdist P card_A) => [r1 [Hr1 Hp]].
move: (charac_bdist Q card_A) => [r2 [Hr2 Hq]].
rewrite Hp Hq.
apply Pinsker_2_inequality_bdist.
by rewrite /dom_by -Hp -Hq.
Qed.

End Pinsker_2.

Section Pinsker.

Variable A : finType.
Variables P Q : dist A.
Hypothesis P_dom_by_Q : P << Q.

Local Open Scope Rb_scope.

Local Notation "0" := (false).
Local Notation "1" := (true).

(** * Pinsker's Inequality *)

Lemma Pinsker_inequality : / (2 * ln 2) * d(P , Q) ^ 2 <= D(P || Q).
Proof.
pose A0 := [set a | Q a <b= P a].
pose A1 := [set a | P a <b Q a].
pose A_ := fun b => match b with 0 => A0 | 1 => A1 end.
have cov : A_ 0 :|: A_ 1 = setT.
  rewrite /= /A0 /A1.
  have -> : [set x | P x <b Q x] = ~: [set x | Q x <b= P x].
    apply/setP => a; by rewrite in_set in_setC in_set RltNge.
  by rewrite setUCr.
have dis : A_ 0 :&: A_ 1 = set0.
  rewrite /A_ /A0 /A1.
  have -> : [set x | P x <b Q x] = ~: [set x | Q x <b= P x].
    apply/setP => a; by rewrite in_set in_setC in_set RltNge.
  by rewrite setICr.
pose P_A := bipart dis cov P.
pose Q_A := bipart dis cov Q.
have step1 : D(P_A || Q_A) <= D(P || Q) by apply partition_inequality; exact P_dom_by_Q.
suff : / (2 * ln 2) * d(P , Q) ^2 <= D(P_A || Q_A).
  move=> ?; apply Rle_trans with (D(P_A || Q_A)) => //; by apply Rge_le.
have step2 : d( P , Q ) = d( P_A , Q_A ).
  rewrite /var_dist.
  transitivity (\rsum_(a | a \in A0) Rabs (P a - Q a) + \rsum_(a | a \in A1) Rabs (P a - Q a)).
    rewrite -(@rsum_union _ _ _ (A0 :|: A1)) //; last by rewrite -setI_eq0 -dis /A_ setIC.
    apply eq_bigl => a; by rewrite cov in_set.
  transitivity (Rabs (P_A 0 - Q_A 0) + Rabs (P_A 1 - Q_A 1)).
    f_equal.
    - rewrite /P_A /Q_A /bipart /= /bipart_pmf /=.
      transitivity (\rsum_(a | a \in A0) (P a - Q a)).
        apply eq_bigr => a; rewrite /A0 in_set => Ha.
        rewrite Rabs_pos_eq //.
        move/RleP in Ha; by fourier.
      rewrite big_split /= Rabs_pos_eq; last first.
        suff : \rsum_(a | a \in A0)Q a <= \rsum_(a | a \in A0) P a.
          move=> ?; by fourier.
        apply: Rle_big_P_f_g => a.
        rewrite inE; by move/RleP.
      rewrite -(big_morph _ morph_Ropp Ropp_0) //; by field.
    - rewrite /P_A /Q_A /bipart /= /bipart_pmf /=.
      have [A1_card | A1_card] : #|A1| = O \/ (0 < #|A1|)%nat.
        destruct (#|A1|); [tauto | by right].
      + move/eqP : A1_card; rewrite cards_eq0; move/eqP => A1_card.
        rewrite A1_card !big_set0 Rabs_pos_eq //; [by field | fourier].
      + transitivity (\rsum_(a | a \in A1) - (P a - Q a)).
          apply eq_bigr => a; rewrite /A1 in_set => Ha.
          rewrite Rabs_left //.
          move/RltP in Ha; by fourier.
        rewrite -(big_morph _  morph_Ropp Ropp_0) // big_split /= Rabs_left; last first.
          suff : \rsum_(a | a \in A1) P a < \rsum_(a | a \in A1) Q a by move=> ?; fourier.
          apply: Rlt_big_f_g_X => // a.
          rewrite /A1 in_set; by move/RltP.
        by rewrite -(big_morph _ morph_Ropp Ropp_0).
  rewrite /index_enum -enumT Two_set.enum /=.
    symmetry; by rewrite card_bool.
  move=> HX.
  rewrite /bipart_pmf big_cons /= big_cons /= big_nil /= addR0.
  set i0 := Two_set.val0 HX.
  set i1 := Two_set.val1 HX.
  have : i0 <> i1.
    apply/eqP.
    by apply Two_set.val0_neq_val1.
  wlog : i0 i1 / (i0 == false) && (i1 == true).
    move=> Hwlog i0i1.
    have : ((i0, i1) == (true, false)) || ((i0, i1) == (false, true)).
      move: i0 i1 i0i1; by case; case.
    case/orP; case/eqP => -> ->.
    - by rewrite (Hwlog false true) // addRC.
    - by apply Hwlog.
  case/andP => /eqP ? /eqP ?; by subst i0 i1.
rewrite step2.
apply (Pinsker_2_inequality card_bool) => /= b.
rewrite /bipart_pmf => H.
have {H}H : 0%R = bipart_pmf A_ Q b. done.
move: (@Req_0_rmul_inv A (mem (A_ b)) (pmf Q) (dist_nonneg Q) H) => {H}H.
transitivity (\rsum_(a | a \in A_ b) 0%R).
  apply eq_bigr => // a Ha.
  apply P_dom_by_Q; by rewrite -H.
by rewrite big_const iter_Rplus mulR0.
Qed.

Lemma Pinsker_inequality_weak : d(P , Q) <= sqrt (2 * D(P || Q)).
Proof.
rewrite -(sqrt_Rsqr (d(P , Q))); last by apply pos_var_dist.
apply sqrt_le_1_alt.
apply (Rmult_le_reg_l (/ 2)); first by apply Rinv_0_lt_compat; fourier.
apply Rle_trans with (D(P || Q)); last first.
  rewrite mulRA Rinv_l; last by move=> ?; fourier.
  rewrite mul1R; by apply Rle_refl.
eapply Rle_trans; last by apply Pinsker_inequality.
rewrite (_ : forall x, Rsqr x = x ^ 2); last by move=> ?; rewrite /Rsqr /pow; field.
apply Rmult_le_compat_r; first by apply le_sq.
apply Rle_Rinv; [ | fourier| ].
- apply Rmult_lt_0_compat; [fourier | exact ln_2_pos].
- rewrite -[X in _ <= X]mulR1.
  apply Rmult_le_compat_l; first by fourier.
  rewrite [X in _ <= X](_ : 1%R = ln (exp 1)); last by rewrite ln_exp.
  apply ln_increasing_le; [fourier | exact two_e].
Qed.

End Pinsker.
