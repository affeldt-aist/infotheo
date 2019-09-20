(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg matrix.
Require Import Reals.
Require Import ssrR Reals_ext ssr_ext ssralg_ext logb ln_facts Rbigop arg_rmax.
Require Import num_occ proba entropy types jtypes divergence.
Require Import conditional_divergence error_exponent channel_code channel.
Require Import success_decode_bound.

(** * Converse of the Channel Coding Theorem *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope channel_code_scope.
Local Open Scope channel_scope.
Local Open Scope entropy_scope.
Local Open Scope tuple_ext_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope types_scope.
Local Open Scope divergence_scope.
Local Open Scope R_scope.

Section channel_coding_converse_intermediate_lemma.

Variables (A B : finType) (W : `Ch*(A, B)).
Variable cap : R.
Hypothesis Hc : capacity W cap.

Variable minRate : R.
Hypothesis HminRate : minRate > cap.

Let Anot0 : (0 < #|A|)%nat. Proof. by case: W. Qed.

Let Bnot0 : (0 < #|B|)%nat.
Proof. case/card_gt0P : Anot0 => a _; exact: (fdist_card_neq0 (W a)). Qed.

Lemma channel_coding_converse_gen : exists Delta, 0 < Delta /\ forall n',
  let n := n'.+1 in forall (M : finType) (c : code A B M n), (0 < #|M|)%nat ->
    minRate <= CodeRate c ->
      scha(W, c) <= n.+1%:R ^ (#|A| + #|A| * #|B|) * exp2 (- n%:R * Delta).
Proof.
move: error_exponent_bound => /(_ _ _ Bnot0 W _ Hc _ HminRate); case => Delta [Delta_pos HDelta].
exists Delta; split => // n' n M c Mnot0 H.
apply: (leR_trans (success_bound W Mnot0 c)).
set Pmax := arg_rmax _ _ _.
set tc :=  _.-typed_code _.
rewrite pow_add -mulRA.
apply leR_wpmul2l; first exact/pow_le/leR0n.
apply (leR_trans (typed_success_bound W Mnot0 (Pmax.-typed_code c))).
apply leR_wpmul2l; first exact/pow_le/leR0n.
set Vmax := arg_rmax _ _ _.
rewrite /success_factor_bound /exp_cdiv.
case : ifP => Hcase; last by rewrite mul0R.
rewrite -ExpD.
apply Exp_le_increasing => //.
rewrite -mulRDr 2!mulNR.
rewrite leR_oppr oppRK; apply/leR_wpmul2l; first exact/leR0n.
have {}Hcase : Pmax |- Vmax << W.
  move=> a Hp; apply/dominatesP => b /eqP Hw.
  move/forallP : Hcase.
  by move/(_ a)/implyP/(_ Hp)/forallP/(_ b)/implyP/(_ Hw)/eqP.
apply (leR_trans (HDelta Pmax Vmax Hcase)) => /=.
exact/leR_add2l/Rle_max_compat_l/leR_add2r.
Qed.

End channel_coding_converse_intermediate_lemma.

Section channel_coding_converse.

Variables A B : finType.
Variable W : `Ch*(A, B).
Variable cap : R.
Hypothesis w_cap : capacity W cap.

Variable epsilon : R.
Hypothesis eps_gt0 : 0 < epsilon.

Variable minRate : R.
Hypothesis minRate_cap : minRate > cap.

(** Converse of the Channel Coding Theorem #<a name="label_channel_coding_converse"> </a># *)

Theorem channel_coding_converse : exists n0,
  forall n M (c : code A B M n),
    (0 < #|M|)%nat -> n0 < n%:R -> minRate <= CodeRate c -> scha(W, c) < epsilon.
Proof.
case: (channel_coding_converse_gen w_cap minRate_cap) => Delta [Delta_pos HDelta].
pose K := (#|A| + #|A| * #|B|)%nat.
pose n0 := 2 ^ K * K.+1`!%:R / ((Delta * ln 2) ^ K.+1) / epsilon.
exists n0 => n M c HM n0_n HminRate.
have Rlt0n : 0 < n%:R.
  apply: (ltR_trans _ n0_n).
  rewrite /n0.
  apply mulR_gt0; last exact/invR_gt0.
  rewrite /Rdiv -mulRA.
  apply mulR_gt0; first exact/expR_gt0/Rlt_0_2.
  apply mulR_gt0;
    [exact/ltR0n/fact_gt0 | exact/invR_gt0/expR_gt0/mulR_gt0].
destruct n as [|n'].
  by apply ltRR in Rlt0n.
set n := n'.+1.
apply: (@leR_ltR_trans (n.+1%:R ^ K * exp2 (- n%:R * Delta))).
  exact: HDelta.
move: (n0_n) => /(@ltR_pmul2l (/ n%:R) _) => /(_ (invR_gt0 n%:R Rlt0n)).
rewrite mulVR ?INR_eq0' //.
move/(@ltR_pmul2l epsilon) => /(_ eps_gt0); rewrite mulR1 => H1'.
apply: (leR_ltR_trans _ H1') => {H1'}.
rewrite /n0 [in X in _ <= X]mulRC -2![in X in _ <= X]mulRA.
rewrite mulVR ?mulR1; last exact/eqP/gtR_eqF.
apply Rge_le; rewrite mulRC -2!mulRA; apply Rle_ge.
set aux := _%:R * (_ * _).
have aux_gt0 : 0 < aux.
  apply mulR_gt0; first exact/ltR0n/fact_gt0.
  apply mulR_gt0; [exact/invR_gt0/expR_gt0/mulR_gt0 | exact/invR_gt0].
apply (@leR_trans ((n.+1%:R / n%:R) ^ K * aux)); last first.
  apply leR_pmul => //.
  - apply/expR_ge0/divR_ge0 => //; exact: leR0n.
  - exact: ltRW.
  - apply pow_incr; split.
    + apply divR_ge0 => //; exact: leR0n.
    + apply (@leR_pmul2r n%:R) => //.
      rewrite -mulRA mulVR // ?mulR1 ?INR_eq0' ?gtn_eqF // (_ : 2 = 2%:R) //.
      rewrite -natRM; apply/le_INR/leP; by rewrite -{1}(mul1n n) ltn_pmul2r.
  - exact/leRR.
rewrite expRM -mulRA; apply leR_pmul => //.
- exact/expR_ge0/ltRW/ltR0n.
- exact/leRR.
- apply invR_le => //.
  + apply mulR_gt0; last exact aux_gt0.
    rewrite expRV ?INR_eq0' //; exact/invR_gt0/expR_gt0.
  + rewrite -exp2_Ropp mulNR oppRK /exp2.
    have nDeltaln2 : 0 <= n%:R * Delta * ln 2.
      apply mulR_ge0; last exact/ltRW.
      apply mulR_ge0; [exact/leR0n | exact/ltRW].
    apply: (leR_trans _ (exp_lb (K.+1) nDeltaln2)) => {nDeltaln2}.
    apply Req_le.
    rewrite invRM; last 2 first.
      exact/gtR_eqF/expR_gt0/invR_gt0.
      exact/gtR_eqF.
    rewrite -/(Rdiv _ _) divRM; last 2 first.
      by apply/eqP; rewrite INR_eq0' gtn_eqF // fact_gt0.
      apply/nesym/ltR_eqF/mulR_gt0; last exact/invR_gt0.
      exact/invR_gt0/expR_gt0/mulR_gt0.
    rewrite -mulRA mulRC invRM; last 2 first.
    - apply/invR_neq0/eqP; rewrite expR_eq0 mulR_neq0' ln2_neq0 andbT; exact/eqP/gtR_eqF.
    - apply/invR_neq0/eqP; by rewrite INR_eq0'.
    - rewrite invRK; last first.
        apply/eqP; rewrite expR_eq0 mulR_neq0' ln2_neq0 andbT; exact/eqP/gtR_eqF.
      rewrite invRK; last by apply/eqP; rewrite INR_eq0'.
      rewrite (_ : / (/ n%:R) ^ K = n%:R ^ K); last first.
        rewrite expRV ?INR_eq0' // invRK //; apply/eqP/expR_neq0; by rewrite INR_eq0'.
      rewrite -mulRA {1}/Rdiv (mulRA n%:R) -expRS mulRA -expRM.
      by rewrite -/(Rdiv _ _) mulRCA -mulRA (mulRC (ln 2)).
Qed.

End channel_coding_converse.
