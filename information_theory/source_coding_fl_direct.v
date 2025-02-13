(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint matrix.
From mathcomp Require Import archimedean lra ring.
From mathcomp Require Import Rstruct reals exp.
Require Import ssr_ext ssralg_ext realType_ln natbin fdist.
Require Import proba entropy aep typ_seq source_code.

(**md**************************************************************************)
(* # Source coding theorem (fixed length, direct part)                        *)
(*                                                                            *)
(* The main theorem is `source_coding_direct`.                                *)
(*                                                                            *)
(* For details, see Reynald Affeldt, Manabu Hagiwara, and Jonas Sénizergues.  *)
(* Formalization of Shannon's theorems. Journal of Automated Reasoning,       *)
(* 53(1):63--103, 2014                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import Order.POrderTheory GRing.Theory Num.Theory Num.Def Order.TotalTheory.

Local Open Scope fdist_scope.
Local Open Scope ring_scope.

Section encoder_and_decoder.
Let R := Rdefinitions.R.
Variables (A : finType) (P : R.-fdist A) (n k : nat).

Variable S : {set 'rV[A]_k.+1}.

Definition f : encT A 'rV_n k.+1 := fun x =>
  if x \in S then
    let i := index x (enum S) in
    row_of_tuple (Tuple (size_bitseq_of_nat i.+1 n))
  else
    \row_(j < n) false.

Variable def : 'rV[A]_k.+1.
Hypothesis def_S : def \in S.

Definition phi : decT A 'rV_n k.+1 := fun x =>
  let i := tuple2N (tuple_of_row x) in
  if i is BinNat.N0 then def else
    if (i.-1 < #| S |)%nat then nth def (enum S) i.-1 else def.

Lemma phi_f i : phi (f i) = i -> i \in S.
Proof.
rewrite /f; case: ifPn => // iS.
rewrite /phi (_ : tuple_of_row _ = [tuple of nseq n false]); last first.
  rewrite -[RHS]row_of_tupleK; congr tuple_of_row.
  by apply/rowP => a; rewrite !mxE /tnth nth_nseq ltn_ord.
rewrite /tuple2N /= /N_of_bitseq /= -{1}(cats0 (nseq n false)).
rewrite rem_lea_false_nseq /= => defi.
by rewrite -defi def_S in iS.
Qed.

Hypothesis HS : (#| S | < expn 2 n)%nat.

Lemma f_phi i : i \in S -> phi (f i) = i.
Proof.
move=> iS; rewrite /f iS /phi row_of_tupleK.
have H : ((index i (enum S)).+1 < expn 2 n)%nat.
  have : ((index i (enum S)).+1 <= #| S |)%nat.
    by apply seq_index_enum_card => //; exact: enum_uniq.
  by move/leq_ltn_trans; exact.
move Heq1 : (tuple2N _) => eq1.
case: eq1 Heq1 => [|i0 Heq1].
- case/tuple2N_0 => Heq1.
  have : (seq.index i (enum S)).+1 <> O by [].
  by move=> /bitseq_of_nat_nseq_false/(_ H); rewrite Heq1.
- move Heq : ((BinNat.Npos i0).-1 < #| S |)%nat => [].
  - by rewrite -Heq1 /= N_of_bitseq_bitseq_of_nat // nth_index // mem_enum.
  - move: Heq.
    by rewrite -Heq1 /tuple2N N_of_bitseq_bitseq_of_nat// seq_index_enum_card // enum_uniq.
Qed.

End encoder_and_decoder.

Section source_direct_bound.
Let R := Rdefinitions.R.

Let source_direct_bound' d (D : R) : { k | D <= (k * d.+1)%:R }.
Proof.
exists `| Num.ceil D |%N.
rewrite natrM.
apply: (@le_trans _ _ `| Num.ceil D |%:R).
  by rewrite (le_trans (le_ceil _))// natr_absz ler_int ler_norm.
by rewrite ler_peMr// ler1n.
Qed.

Lemma source_direct_bound d (D : R) : { k | D <= (k.+1 * d.+1)%:R }.
Proof.
case: (source_direct_bound' d D) => k Hk.
destruct k as [|k]; last by exists k.
exists O; rewrite mul1n.
by move: Hk; rewrite mul0n => /le_trans; apply.
Qed.

End source_direct_bound.

Local Open Scope source_code_scope.
Local Open Scope entropy_scope.
Local Open Scope reals_ext_scope.

Section source_coding_direct'.
Let R := Rdefinitions.R.
Variables (A : finType) (P : R.-fdist A) (num den : nat).
Let r : R := num%:R / den.+1%:R.
Hypothesis Hr : `H P < r.
Variable epsilon : R.
Hypothesis epsilon01 : 0 < epsilon < 1.

Definition lambda := minr (r - `H P) epsilon.

Lemma lambda_gt0 : 0 < lambda.
Proof.
rewrite lt_min subr_gt0 Hr/=.
by case/andP : epsilon01.
Qed.

Lemma lambda2_epsilon : lambda / 2 <= epsilon.
Proof.
apply (@le_trans _ _ lambda).
  by rewrite ler_pdivrMr// ler_peMr ?ler1n// ltW// lambda_gt0.
by rewrite /lambda ge_min lexx orbT.
Qed.

Lemma lambda2_gt0 : 0 < lambda / 2.
Proof. by apply divr_gt0 => //; exact: lambda_gt0. Qed.

Lemma lambda2_lt1 : lambda / 2 < 1.
Proof. apply: (le_lt_trans lambda2_epsilon); by case/andP: epsilon01. Qed.

Definition delta := maxr (aep_bound P (lambda / 2)) (2 / lambda).

Let k' := sval (source_direct_bound den delta).

Definition k := (k'.+1 * den.+1)%nat.

Definition n := (k'.+1 * num)%nat.

Lemma Hlambdar : `H P + lambda <= r.
Proof.
rewrite /lambda.
have [?|?] := leP (r - `H P) epsilon.
- by rewrite addrCA subrr addr0.
- lra.
Qed.

Local Open Scope typ_seq_scope.

Theorem source_coding' : exists sc : scode_fl A k n,
  SrcRate sc = r /\ esrc(P , sc) <= epsilon.
Proof.
move: (proj2_sig (source_direct_bound den delta)) => Hdelta.
have Hk : aep_bound P (lambda / 2) <= k%:R.
  by apply/(le_trans _ Hdelta); rewrite le_max lexx.
set S := `TS P k (lambda / 2).
set def := TS_0 lambda2_gt0 lambda2_lt1 Hk. (*TODO: get rid of this expansion*)
set F := f n S.
set PHI := @phi _ n _ S def.
exists (mkScode F PHI); split.
  rewrite /SrcRate /r /n /k.
  field.
  by rewrite !nat1r/= !gt_eqF//=.
set lhs := esrc(_, _).
suff -> : lhs = 1 - Pr (P `^ k)%fdist (`TS P k (lambda / 2)).
  rewrite lerBlDr addrC -lerBlDr.
  apply (@le_trans _ _ (1 - lambda / 2)).
    by rewrite lerD2l lerNr opprK; exact: lambda2_epsilon.
  exact: (Pr_TS_1 lambda2_gt0).
rewrite /lhs {lhs} /SrcErrRate /Pr /=.
set lhs := \sum_(_ | _ ) _.
suff -> : lhs = \sum_(x in 'rV[A]_k | x \notin S) (P `^ k)%fdist x.
  have : forall a b : R, a + b = 1 -> b = 1 - a by move=> ? ? <-; field.
  apply.
  rewrite -[X in _ = X](Pr_cplt (P `^ k)%fdist (`TS P k (lambda / 2))).
  congr +%R.
  by apply: eq_bigl => ta /=; rewrite !inE.
rewrite {}/lhs; apply eq_bigl => //= i.
rewrite inE /=; apply/negPn/negPn.
- suff H : def \in S by move/eqP/phi_f; tauto.
  exact: (TS_0_is_typ_seq lambda2_gt0 lambda2_lt1 Hk).
- suff S_2n : (#| S | < expn 2 n)%nat by move/(f_phi def S_2n)/eqP.
  suff card_S_bound : #| S |%:R < 2 `^ (k%:R * r).
    rewrite -(ltr_nat R) -natrXE natrX -powR_mulrn ?ler0n//.
    suff : n%:R = k%:R * r by move=> ->.
    rewrite /n /k /r.
    by rewrite !natrM mulrCA -mulrA divff ?mulr1 ?pnatr_eq0// mulrC.
  suff card_S_bound : 1 + #| S |%:R <= 2 `^ (k%:R * r) by lra.
  suff card_S_bound : 1 + #| S |%:R <= 2 `^ (k%:R * (`H P + lambda)).
    apply: le_trans; first exact: card_S_bound.
    by rewrite gt1_ler_powRr ?ltr1n// ler_wpM2l// Hlambdar.
  apply (@le_trans _ _ (2 `^ (k%:R * (lambda / 2) + k%:R * (`H P + lambda / 2)))); last first.
    rewrite -mulrDr addrC -addrA.
    rewrite (_ : forall a, a / 2 + a / 2 = a); last by move=> ?; field.
    by rewrite lexx.
  apply (@le_trans _ _ (2 `^ (1 + k%:R * (`H P + lambda / 2)))); last first.
    rewrite gt1_ler_powRr ?ltr1n// lerD2r//.
    move: Hdelta; rewrite ge_max => /andP[_ Hlambda].
    rewrite -(@ler_pM2r _ (2 / lambda)); last first.
      by rewrite divr_gt0//; exact: lambda_gt0.
    rewrite mul1r -mulrA.
    rewrite -[in leRHS]invf_div// mulVf ?mulr1//.
    by rewrite gt_eqF// -invf_div// invr_gt0// lambda2_gt0.
  apply:(@le_trans _ _ (1 + powR 2 (k%:R * (`H P + (lambda / 2))))).
    rewrite lerD2l//.
    exact: TS_sup.
    rewrite /S.
  apply (@le_trans _ _ (2 `^ (k%:R * (`H P + lambda / 2)) +
                        2 `^ (k%:R * (`H P + lambda / 2)))).
  + rewrite lerD2r -[leLHS](powRr0 2).
    rewrite ler_powR ?ler1n// mulr_ge0// addr_ge0//; first exact: entropy_ge0.
    by rewrite divr_ge0// ltW// lambda_gt0.
  + rewrite -mulr2n -mulr_natl powRD; last by rewrite pnatr_eq0 implybT.
    by rewrite ler_pM2r ?powR_gt0// powRr1.
Qed.

End source_coding_direct'.

Section source_coding_direct.
Variables (A : finType) (P : {fdist A}).

Theorem source_coding_direct epsilon : 0 < epsilon < 1 ->
  forall nu de : nat, `H P < nu%:R / de.+1%:R ->
    exists k n (sc : scode_fl A k n), SrcRate sc = nu%:R/de.+1%:R /\
                                      esrc(P , sc) <= epsilon.
Proof.
move=> Heps nu de HP_r.
exists (k P nu de epsilon), (n P nu de epsilon).
exact: source_coding'.
Qed.

End source_coding_direct.
