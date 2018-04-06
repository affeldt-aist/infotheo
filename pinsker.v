(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype tuple finfun bigop finset.
Require Import Reals Fourier.
Require Import Rssr Reals_ext Ranalysis_ext ssr_ext log2 ln_facts bigop_ext.
Require Import Rbigop proba divergence variation_dist pinsker_function.
Require Import partition_inequality.

(** * Pinsker's Inequality *)

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

Let P := Binary.d card_A p01.
Let Q := Binary.d card_A q01.

Hypothesis P_dom_by_Q : P << Q.

Lemma pinsker_fun_p_eq c : pinsker_fun p c q = D(P || Q) - c * d(P , Q) ^ 2.
Proof.
pose a := Set2.a card_A. pose b := Set2.b card_A.
set pi := P a.
set pj := P b.
set qi := Q a.
set qj := Q b.
have Hpi : pi = 1 - p by rewrite /pi /= Binary.fxx.
have Hqi : qi = 1 - q by rewrite /qi /= Binary.fxx.
have Hpj : pj = p.
  by rewrite /pj /= /Binary.f eq_sym (negbTE (Set2.a_neq_b card_A)).
have Hqj : qj = q.
  by rewrite /qj /= /Binary.f eq_sym (negbTE (Set2.a_neq_b card_A)).
transitivity (D(P || Q) - c * (Rabs (p - q) + Rabs ((1 - p) - (1 - q))) ^ 2).
  rewrite /pinsker_fun /div Set2sumE -/a -/b -/pi -/pj -/qi -/qj Hpi Hpj Hqi Hqj.
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
    rewrite -Hp1 !mul0R subR0 addR0 add0R !mul1R /log Log_1 /Rdiv.
    case/Rle_lt_or_eq_dec : Hq2 => Hq2; last first.
      move: (@P_dom_by_Q (Set2.a card_A)).
      rewrite -/pi -/qi Hqi Hq2 Rminus_diag_eq // => /(_ erefl).
      rewrite Hpi -Hp1 subR0 => ?. exfalso. fourier.
    rewrite /log Log_mult; last 2 first.
      fourier.
      apply/invR_gt0; fourier.
      rewrite LogV; last by fourier.
      rewrite Log_1; by field.
  case/Rle_lt_or_eq_dec : Hq1 => Hq1; last first.
    move: (@P_dom_by_Q (Set2.b card_A)).
    rewrite -/pj -/qj Hqj -Hq1 => /(_ erefl).
    rewrite Hpj => abs.
    move: Hp1; by rewrite abs => /Rlt_irrefl.
  rewrite /div_fct /comp /= (_ : id q = q) //.
  case/Rle_lt_or_eq_dec : Hp2 => Hp2; last first.
    rewrite Hp2 Rminus_diag_eq // !mul0R /Rdiv /log Log_mult; last 2 first.
      fourier.
      exact/invR_gt0.
    rewrite Log_1 mul1R LogV //; by field.
  rewrite /log Log_mult //; last exact/invR_gt0.
  rewrite LogV //.
  case/Rle_lt_or_eq_dec : Hq2 => Hq2; last first.
    move: (@P_dom_by_Q (Set2.a card_A)).
    rewrite -/pi -/qi Hqi -Hq2 Rminus_diag_eq // => /(_ erefl).
    rewrite Hpi => abs. exfalso. fourier.
  rewrite /Rdiv Log_mult; last 2 first.
    fourier.
    apply/invR_gt0; fourier.
  rewrite LogV; last by fourier.
  by field.
do 2 f_equal.
by rewrite /var_dist Set2sumE // -/pi -/pj -/qi -/qj Hpi Hpj Hqi Hqj addRC.
Qed.

Lemma Pinsker_2_inequality_bdist : / (2 * ln 2) * d(P , Q) ^ 2 <= D(P || Q).
Proof.
set lhs := _ * _.
set rhs := D(_ || _).
suff : 0 <= rhs - lhs by move=> ?; fourier.
rewrite -pinsker_fun_p_eq.
apply pinsker_fun_pos with p01 q01 A card_A => //.
split; last exact: Rle_refl.
apply Rlt_le, Rinv_0_lt_compat, mulR_gt0; [fourier | by apply ln_2_pos].
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
    rewrite -big_union //; last by rewrite -setI_eq0 -dis /A_ setIC.
    apply eq_bigl => a; by rewrite cov in_set.
  transitivity (Rabs (P_A 0 - Q_A 0) + Rabs (P_A 1 - Q_A 1)).
    congr (_ + _).
    - rewrite /P_A /Q_A /bipart /= /bipart_pmf /=.
      transitivity (\rsum_(a | a \in A0) (P a - Q a)).
        apply eq_bigr => a; rewrite /A0 in_set => /RleP Ha.
        rewrite Rabs_pos_eq //; by fourier.
      rewrite big_split /= Rabs_pos_eq; last first.
        suff : \rsum_(a | a \in A0) Q a <= \rsum_(a | a \in A0) P a.
          move=> ?; by fourier.
        apply ler_rsum => a; by rewrite inE => /RleP.
      rewrite -(big_morph _ morph_Ropp oppR0) //; by field.
    - rewrite /P_A /Q_A /bipart /= /bipart_pmf /=.
      have [A1_card | A1_card] : #|A1| = O \/ (0 < #|A1|)%nat.
        destruct (#|A1|); [tauto | by right].
      + move/eqP : A1_card; rewrite cards_eq0; move/eqP => A1_card.
        rewrite A1_card !big_set0 Rabs_pos_eq //; [by field | fourier].
      + transitivity (\rsum_(a | a \in A1) - (P a - Q a)).
          apply eq_bigr => a; rewrite /A1 in_set => Ha.
          rewrite Rabs_left //.
          move/RltP in Ha; by fourier.
        rewrite -(big_morph _  morph_Ropp oppR0) // big_split /= Rabs_left; last first.
          suff : \rsum_(a | a \in A1) P a < \rsum_(a | a \in A1) Q a by move=> ?; fourier.
          apply ltr_rsum_support => // a.
          rewrite /A1 in_set; by move/RltP.
        by rewrite -(big_morph _ morph_Ropp oppR0).
  rewrite Set2sumE ?card_bool // => HX; rewrite /bipart_pmf.
  set a := Set2.a HX. set b := Set2.b HX.
  have : a <> b by apply/eqP/Set2.a_neq_b.
  wlog : a b / (a == false) && (b == true).
    move=> Hwlog ab.
    have : ((a, b) == (true, false)) || ((a, b) == (false, true)).
      move: a b ab; by case; case.
    case/orP; case/eqP => -> ->.
    - by rewrite (Hwlog false true) //= addRC.
    - by apply Hwlog.
  case/andP => /eqP ? /eqP ?; by subst a b.
rewrite step2.
apply (Pinsker_2_inequality card_bool) => /= b.
rewrite /bipart_pmf.
move/prsumr_eq0P => H.
transitivity (\rsum_(a | a \in A_ b) 0%R).
  apply eq_bigr => // a ?; apply P_dom_by_Q; rewrite H // => c ?; exact/pos_f_nonneg.
by rewrite big_const iter_Rplus mulR0.
Qed.

Lemma Pinsker_inequality_weak : d(P , Q) <= sqrt (2 * D(P || Q)).
Proof.
rewrite -(sqrt_Rsqr (d(P , Q))); last by apply pos_var_dist.
apply sqrt_le_1_alt.
apply (Rmult_le_reg_l (/ 2)); first by apply Rinv_0_lt_compat; fourier.
apply Rle_trans with (D(P || Q)); last first.
  rewrite mulRA Rinv_l; last by move=> ?; fourier.
  rewrite mul1R; exact/Rle_refl.
eapply Rle_trans; last by apply Pinsker_inequality.
rewrite (_ : forall x, Rsqr x = x ^ 2); last by move=> ?; rewrite /Rsqr /pow; field.
apply Rmult_le_compat_r; first by apply le_sq.
apply Rinv_le_contravar.
- apply mulR_gt0; [fourier | exact ln_2_pos].
- rewrite -[X in _ <= X]mulR1.
  apply Rmult_le_compat_l; first by fourier.
  rewrite [X in _ <= X](_ : 1%R = ln (exp 1)); last by rewrite ln_exp.
  apply ln_increasing_le; [fourier | exact leR2e].
Qed.

End Pinsker.
