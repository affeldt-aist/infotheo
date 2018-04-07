(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import Reals_ext ssr_ext ssralg_ext Rssr log2 natbin Rbigop proba.
Require Import entropy aep typ_seq source_code.

(** * Source coding theorem (direct part) *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Section encoder_and_decoder.

Variable A : finType.
Variable P : dist A.
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
  have H1 : (seq.index i (enum S)).+1 <> O by done.
  move: (bitseq_of_nat_nseq_false H1 H); by rewrite Heq1.
- move Heq : ((Npos i0).-1 < #| S |)%nat => [].
  - by rewrite -Heq1 /= N_of_bitseq_bitseq_of_nat // nth_index // mem_enum.
  - rewrite -Heq1 /tuple2N N_of_bitseq_bitseq_of_nat //= (@seq_index_enum_card _ (enum S) S i) // in Heq.
    by rewrite enum_uniq.
Qed.

End encoder_and_decoder.

Lemma SrcDirectBound' d D : { k | D <= INR (k * (d.+1)) }.
Proof.
exists (Zabs_nat (up D)).
rewrite -multE (mult_INR (Zabs_nat (up D)) d.+1).
apply Rle_trans with (IZR (Zabs (up D))); first by apply Rle_up.
rewrite INR_IZR_INZ inj_Zabs_nat -{1}(mulR1 (IZR _)).
apply Rmult_le_compat_l.
  by apply IZR_le, Zabs_pos.
rewrite -addn1 plus_INR /= (_ : INR 1 = 1%R) //; move: (pos_INR d) => ?; fourier.
Qed.

Lemma SrcDirectBound d D : { k | D <= INR ((k.+1) * (d.+1)) }.
Proof.
case: (SrcDirectBound' d D) => k Hk.
destruct k as [|k]; last by exists k.
exists O; rewrite mul1n.
apply Rle_trans with 0%R; by [assumption | apply pos_INR].
Qed.

Local Open Scope source_code_scope.
Local Open Scope entropy_scope.
Local Open Scope reals_ext_scope.

Section source_coding_direct'.

Variable A : finType.
Variable P : dist A.
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
move: Hr => ? ; fourier.
Qed.

Lemma halflambdaepsilon : lambda / 2 <= epsilon.
Proof.
apply Rle_trans with lambda.
  apply Rdiv_le; [apply Rlt_le; exact lambda0 | fourier].
rewrite /lambda.
case: (Rlt_le_dec (r - `H P) epsilon) => ?.
- rewrite Rmin_left; fourier.
- rewrite Rmin_right //; fourier.
Qed.

Lemma halflambda0 : 0 < lambda / 2.
Proof. apply Rlt_mult_inv_pos; [exact lambda0 | fourier]. Qed.

Lemma halflambda1 : lambda / 2 < 1.
Proof.
eapply Rle_lt_trans; by [apply halflambdaepsilon | apply (proj2 Hepsilon)].
Qed.

Lemma lambdainv2 : 0 < 2 / lambda.
Proof. apply Rlt_mult_inv_pos; [fourier | exact lambda0]. Qed.

Lemma Hlambdar : `H P + lambda <= r.
Proof.
rewrite /lambda.
case: (Rlt_le_dec (r - `H P) epsilon) => ?.
- rewrite Rmin_left; fourier.
- rewrite Rmin_right //; fourier.
Qed.

Local Open Scope proba_scope.
Local Open Scope typ_seq_scope.

Theorem source_coding' : exists sc : scode_fl A k n,
  SrcRate sc = r /\ esrc(P , sc) <= epsilon.
Proof.
move: (proj2_sig (SrcDirectBound den delta)) => Hk.
have k_k0 : aep_bound P (lambda / 2) <= INR k.
  eapply Rle_trans; by [apply Rmax_l | apply Hk].
set S := `TS P k (lambda / 2).
set def := TS_0 halflambda0 halflambda1 k_k0.
set F := f n S.
set PHI := @phi _ n _ S def.
exists (mkScode F PHI).
split.
  rewrite /SrcRate /r /n /k 2!mult_INR; field.
  split; by apply not_0_INR.
set lhs := esrc(_, _).
suff -> : lhs = (1 - Pr (P `^ k) (`TS P k (lambda / 2)))%R.
  apply Ropp_le_cancel.
  rewrite Ropp_minus_distr.
  apply (Rplus_le_reg_l 1).
  rewrite Rplus_minus.
  apply Rge_le, Rge_trans with (1 - lambda / 2)%R; last first.
    apply Rle_ge, Rplus_le_compat_l, Ropp_ge_le_contravar, Rle_ge; exact halflambdaepsilon.
  by move: (Pr_TS_1 halflambda0 k_k0).
rewrite /lhs {lhs} /SrcErrRate /Pr /=.
set lhs := \rsum_(_ | _ ) _.
suff -> : lhs = \rsum_(x in 'rV[A]_k | x \notin S) P `^ k x.
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
  exact: (TS_0_is_typ_seq halflambda0 halflambda1 k_k0).
- suff S_2n : (#| S | < expn 2 n)%nat.
    by move/(f_phi def S_2n)/eqP.
  suff card_S_bound : INR #| S | < exp2 (INR k * r).
    apply/ltP/INR_lt.
    rewrite -exp2_pow2.
    suff : INR n = (INR k * r)%R by move=> ->.
    rewrite /n /k /r (mult_INR _ den.+1) /Rdiv -mulRA.
    by rewrite (mulRCA (INR den.+1)) mulRV ?INR_eq0 // mulR1 ?mult_INR.
  suff card_S_bound : 1 + INR #| S | <= exp2 (INR k * r) by fourier.
  suff card_S_bound : 1 + INR #| S | <= exp2 (INR k * (`H P + lambda)).
    eapply Rle_trans; first by apply card_S_bound.
    apply Exp_le_increasing => //; apply Rmult_le_compat_l; [exact/pos_INR | exact/Hlambdar].
  apply Rle_trans with (exp2 (INR k * (lambda / 2) +
                              INR k * (`H P + lambda / 2))); last first.
    rewrite -mulRDr addRC -addRA.
    rewrite (_ : forall a, a / 2 + a / 2 = a)%R; last by move=> ?; field.
    by apply Rle_refl.
  apply Rle_trans with (exp2 (1 + INR k * (`H P + lambda / 2))); last first.
   apply Exp_le_increasing => //; apply Rplus_le_compat_r.
    move/RleP : Hk; rewrite leR_maxl => /andP[_ /RleP Hk].
    apply Rmult_le_reg_r with (2 / lambda)%R; first by exact lambdainv2.
    rewrite mul1R -mulRA -{2}(Rinv_Rdiv lambda 2); last 2 first.
      apply nesym, Rlt_not_eq; exact lambda0.
      move=> ?; fourier.
      rewrite mulRV ?mulR1 //; exact/eqP/nesym/Rlt_not_eq/halflambda0.
  eapply Rle_trans; first exact/Rplus_le_compat_l/TS_sup.
  apply Rle_trans with (exp2 (INR k* (`H P + lambda / 2)) +
                        exp2 (INR k * (`H P + lambda / 2)))%R.
  + apply Rplus_le_compat_r.
    rewrite -exp2_0.
    apply Exp_le_increasing => //.
    apply mulR_ge0; first exact: pos_INR.
    apply addR_ge0; first exact: entropy_pos.
    apply Rlt_le; exact: halflambda0.
  + rewrite (_ : forall a, a + a = 2 * a)%R; last by move=> ?; field.
    rewrite {1}(_ : 2 = exp2 (log 2)); last by rewrite logK //; fourier.
    rewrite -ExpD {1}/log Log_n //; exact/Rle_refl.
Qed.

End source_coding_direct'.

Section source_coding_direct.

Variable A : finType.
Variable P : dist A.

(** Source coding theorem (direct part) #<a name="label_source_coding_direct"> </a># *)

Theorem source_coding_direct : forall epsilon, 0 < epsilon < 1 ->
  forall r : Qplus, `H P < r ->
    exists k n (sc : scode_fl A k n), SrcRate sc = r /\ esrc(P , sc) <= epsilon.
Proof.
move=> eps Heps re HP_r.
destruct re as [num den].
exists (k P num den eps), (n P num den eps).
by apply source_coding'.
Qed.

End source_coding_direct.
