(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg matrix.
Require Import Reals Lra.
From mathcomp Require Import Rstruct.
Require Import ssrZ ssrR Reals_ext ssr_ext ssralg_ext logb natbin Rbigop fdist.
Require Import proba entropy aep typ_seq source_code.

(******************************************************************************)
(*         Source coding theorem (fixed length, direct part)                  *)
(*                                                                            *)
(* Main theorem: source_coding_direct                                         *)
(*                                                                            *)
(* For details, see Reynald Affeldt, Manabu Hagiwara, and Jonas Sénizergues.  *)
(* Formalization of Shannon's theorems. Journal of Automated Reasoning,       *)
(* 53(1):63--103, 2014                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Section encoder_and_decoder.

Variables (A : finType) (P : fdist A).
Variables n k : nat.

Variable S : {set 'rV[A]_k.+1}.

Definition f : encT A 'rV_n k.+1 := fun x =>
  if x \in S then
    let i := seq.index x (enum S) in
    row_of_tuple (Tuple (size_bitseq_of_nat i.+1 n))
  else
    \row_(j < n) false.

Variable def : 'rV[A]_k.+1.
Hypothesis Hdef : def \in S.

Definition phi : decT A 'rV_n k.+1 := fun x =>
  let i := tuple2N (tuple_of_row x) in
  if i is N0 then def else
    if (i.-1 < #| S |)%nat then nth def (enum S) i.-1 else def.

Lemma phi_f i : phi (f i) = i -> i \in S.
Proof.
rewrite /f.
case: ifP => // H1.
rewrite /phi.
rewrite (_ : tuple_of_row _ = [tuple of nseq n false]); last first.
  rewrite -[RHS]row_of_tupleK; congr tuple_of_row.
  apply/matrixP => a b.
  by rewrite !mxE /tnth nth_nseq ltn_ord.
rewrite /tuple2N /= /N_of_bitseq /= -{1}(cats0 (nseq n false)) rem_lea_false_nseq /=.
move=> Hi; by rewrite -Hi Hdef in H1.
Qed.

Hypothesis HS : (#| S | < expn 2 n)%nat.

Lemma f_phi i : i \in S ->  phi (f i) = i.
Proof.
move=> Hi.
rewrite /f Hi /phi.
rewrite row_of_tupleK.
have H : ((seq.index i (enum S)).+1 < expn 2 n)%nat.
  have H : ((seq.index i (enum S)).+1 <= #| S |)%nat.
    apply seq_index_enum_card => //; by apply enum_uniq.
  by apply leq_ltn_trans with #| S |.
move Heq1 : (tuple2N _) => eq1.
case: eq1 Heq1 => [|i0] Heq1.
- case/tuple2N_0 : Heq1 => Heq1.
  have H1 : (seq.index i (enum S)).+1 <> O by [].
  move: (bitseq_of_nat_nseq_false H1 H); by rewrite Heq1.
- move Heq : ((Npos i0).-1 < #| S |)%nat => [].
  - by rewrite -Heq1 /= N_of_bitseq_bitseq_of_nat // nth_index // mem_enum.
  - rewrite -Heq1 /tuple2N N_of_bitseq_bitseq_of_nat //= (@seq_index_enum_card _ (enum S) S i) // in Heq.
    by rewrite enum_uniq.
Qed.

End encoder_and_decoder.

Local Open Scope R_scope.
Local Open Scope zarith_ext_scope.

Lemma SrcDirectBound' d D : { k | D <= INR (k * d.+1) }.
Proof.
exists '| up D |.
rewrite -multE (natRM '| up D | d.+1).
apply (@leR_trans (IZR `| up D |)); first exact: Rle_up.
rewrite INR_IZR_INZ inj_Zabs_nat -{1}(mulR1 (IZR _)).
apply leR_wpmul2l; first exact/IZR_le/Zabs_pos (* TODO: ssrZ? *).
rewrite -addn1 natRD /= (_ : INR 1 = 1%R) //; move: (leR0n d) => ?; lra.
Qed.

Lemma SrcDirectBound d D : { k | D <= INR (k.+1 * d.+1) }.
Proof.
case: (SrcDirectBound' d D) => k Hk.
destruct k as [|k]; last by exists k.
exists O; rewrite mul1n.
apply (@leR_trans 0%R); by [ | apply leR0n].
Qed.

Local Open Scope source_code_scope.
Local Open Scope entropy_scope.
Local Open Scope reals_ext_scope.

Section source_coding_direct'.

Variables (A : finType) (P : fdist A).
Variables num den : nat.

Let r := (INR num / INR den.+1)%R.

Hypothesis Hr : `H P < r.
Variable epsilon : R.
Hypothesis Hepsilon : 0 < epsilon < 1.

Definition lambda := min(r - `H P, epsilon).

Definition delta := max(aep_bound P (lambda / 2), 2 / lambda).

Let k' := sval (SrcDirectBound den delta).

Definition k := (k'.+1 * den.+1)%nat.

Definition n := (k'.+1 * num)%nat.

(* a few easy lemmas to simplify the proof *)

Lemma lambda0 : 0 < lambda.
Proof.
apply Rmin_glb_lt; last by apply (proj1 Hepsilon).
move: Hr => ? ; lra.
Qed.

Lemma halflambdaepsilon : lambda / 2 <= epsilon.
Proof.
apply (@leR_trans lambda).
  rewrite leR_pdivr_mulr //; apply leR_pmulr; [lra | exact/ltRW/lambda0].
rewrite /lambda.
case: (Rlt_le_dec (r - `H P) epsilon) => ?.
- rewrite Rmin_left; lra.
- rewrite Rmin_right //; lra.
Qed.

Lemma halflambda0 : 0 < lambda / 2.
Proof. apply divR_gt0 => //; exact: lambda0. Qed.

Lemma halflambda1 : lambda / 2 < 1.
Proof. exact (leR_ltR_trans halflambdaepsilon (proj2 Hepsilon)). Qed.

Lemma lambdainv2 : 0 < 2 / lambda.
Proof. apply divR_gt0; [lra | exact lambda0]. Qed.

Lemma Hlambdar : `H P + lambda <= r.
Proof.
rewrite /lambda.
case: (Rlt_le_dec (r - `H P) epsilon) => ?.
- rewrite Rmin_left; lra.
- rewrite Rmin_right //; lra.
Qed.

Local Open Scope fdist_scope.
Local Open Scope typ_seq_scope.

Theorem source_coding' : exists sc : scode_fl A k n,
  SrcRate sc = r /\ esrc(P , sc) <= epsilon.
Proof.
move: (proj2_sig (SrcDirectBound den delta)) => Hdelta.
have Hk : aep_bound P (lambda / 2) <= INR k by exact/(leR_trans _ Hdelta)/leR_maxl.
set S := `TS P k (lambda / 2).
set def := TS_0 halflambda0 halflambda1 Hk. (*TODO: get rid of this expansion*)
set F := f n S.
set PHI := @phi _ n _ S def.
exists (mkScode F PHI).
split.
  rewrite /SrcRate /r /n /k 2!natRM; field.
  split; exact/INR_eq0.
set lhs := esrc(_, _).
suff -> : lhs = (1 - Pr (P `^ k) (`TS P k (lambda / 2)))%R.
  rewrite leR_subl_addr addRC -leR_subl_addr.
  apply (@leR_trans (1 - lambda / 2)%R).
    apply leR_add2l; rewrite leR_oppr oppRK; exact halflambdaepsilon.
  by move: (Pr_TS_1 halflambda0 Hk).
rewrite /lhs {lhs} /SrcErrRate /Pr /=.
set lhs := \sum_(_ | _ ) _.
suff -> : lhs = \sum_(x in 'rV[A]_k | x \notin S) P `^ k x.
  have : forall a b : R, (a + b = 1 -> b = 1 - a)%R. by move=> ? ? <-; field.
  apply.
  rewrite -[X in _ = X](Pr_cplt (P `^ k) (`TS P k (lambda / 2))).
  congr (_ + _)%R.
  rewrite /Pr.
  apply eq_bigl => ta /=.
  by rewrite /`TS !inE.
rewrite /lhs {lhs}.
apply eq_bigl => // i.
rewrite inE /=.
apply/negPn/negPn.
- suff H : def \in S by move/eqP/phi_f; tauto.
  exact: (TS_0_is_typ_seq halflambda0 halflambda1 Hk).
- suff S_2n : (#| S | < expn 2 n)%nat.
    by move/(f_phi def S_2n)/eqP.
  suff card_S_bound : #| S |%:R < exp2 (k%:R * r).
    apply/ltP/INR_lt; rewrite -natRexp2.
    suff : INR n = (INR k * r)%R by move=> ->.
    rewrite /n /k /r (natRM _ den.+1) /Rdiv -mulRA.
    by rewrite (mulRCA (INR den.+1)) mulRV ?INR_eq0' // mulR1 natRM.
  suff card_S_bound : 1 + #| S |%:R <= exp2 (k%:R * r) by lra.
  suff card_S_bound : 1 + #| S |%:R <= exp2 (k%:R * (`H P + lambda)).
    apply: leR_trans; first exact: card_S_bound.
    apply Exp_le_increasing => //; apply leR_wpmul2l; [exact/leR0n | exact/Hlambdar].
  apply (@leR_trans (exp2 (INR k * (lambda / 2) +
                              INR k * (`H P + lambda / 2)))); last first.
    rewrite -mulRDr addRC -addRA.
    rewrite (_ : forall a, a / 2 + a / 2 = a)%R; last by move=> ?; field.
    exact/leRR.
  apply (@leR_trans (exp2 (1 + INR k * (`H P + lambda / 2)))); last first.
   apply Exp_le_increasing => //; apply leR_add2r.
    move/leR_max : Hdelta => [_ Hlambda].
    apply (@leR_pmul2r (2 / lambda)%R); first exact lambdainv2.
    rewrite mul1R -mulRA -{2}(Rinv_Rdiv lambda 2); last 2 first.
      by apply/eqP; rewrite gtR_eqF //; exact/lambda0.
      by move=> ?; lra.
      by rewrite mulRV ?mulR1 //; exact/gtR_eqF/halflambda0.
  apply: leR_trans; first exact/leR_add2l/TS_sup.
  apply (@leR_trans (exp2 (INR k* (`H P + lambda / 2)) +
                        exp2 (INR k * (`H P + lambda / 2)))%R).
  + apply leR_add2r.
    rewrite -exp2_0.
    apply Exp_le_increasing => //.
    apply mulR_ge0; first exact: leR0n.
    apply addR_ge0; first exact: entropy_ge0.
    apply Rlt_le; exact: halflambda0.
  + rewrite (_ : forall a, a + a = 2 * a)%R; last by move=> ?; field.
    rewrite {1}(_ : 2 = exp2 (log 2)); last by rewrite logK //; lra.
    by rewrite -ExpD {1}/log Log_n //; exact/leRR.
Qed.

End source_coding_direct'.

Section source_coding_direct.

Variables (A : finType) (P : fdist A).

Theorem source_coding_direct : forall epsilon, 0 < epsilon < 1 ->
  forall r : Qplus, `H P < r ->
    exists k n (sc : scode_fl A k n), SrcRate sc = r /\ esrc(P , sc) <= epsilon.
Proof.
move=> eps Heps re HP_r.
destruct re as [num den].
exists (k P num den eps), (n P num den eps); exact: source_coding'.
Qed.

End source_coding_direct.
