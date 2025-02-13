(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint matrix.
From mathcomp Require Import archimedean lra ring.
From mathcomp Require Import Rstruct reals exp.
Require Import  ssr_ext ssralg_ext bigop_ext realType_ext realType_ln.
Require Import fdist proba entropy aep typ_seq natbin source_code.

(**md**************************************************************************)
(* # Source coding theorem (variable length, direct part)                     *)
(*                                                                            *)
(* Formalization documented in:                                               *)
(* - Ryosuke Obi, Manabu Hagiwara, and Reynald Affeldt. Formalization of      *)
(*   variable-length source coding theorem: Direct part. International        *)
(*   Symposium on Information Theory and Its Applications (ISITA 2014),       *)
(*   Melbourne, Australia, October 26--29, 2014, pages 201--205. IEICE. IEEE  *)
(*   Xplore, Oct 2014                                                         *)
(*                                                                            *)
(* Original source file by R. Obi, quickly patched to compile with InfoTheo   *)
(* [2019-08-19] and simplified afterwards.                                    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope typ_seq_scope.

Local Open Scope ring_scope.

Import Order.POrderTheory GRing.Theory Num.Theory Num.Def Order.TotalTheory.

Section R_lemma.
Let R := Rdefinitions.R.
Variable (X : finType) (n' : nat).
Variable f0 : X -> R.
Let n := n'.+1.
Variable S : {set  X}.

Lemma rsum_split:
  \sum_(x| x \in X) f0 x = \sum_(x| x \in S) f0 x + \sum_(x| x \in ~: S) f0 x.
Proof.
rewrite (bigID (fun x => x \in S)) /=; congr (_ + _).
by apply eq_bigl => x /=; rewrite inE.
Qed.

Lemma log_pow_INR m k : (m > 0)%nat -> log (expn m k)%:R = k%:R * log m%:R :> R.
Proof.
move=> m0; elim: k => [|k ih]; first by rewrite expn0 /log Log1 mul0r.
rewrite expnS natrM logM ?ltr0n // ?expn_gt0 ?m0 // ih.
by rewrite -nat1r mulrDl mul1r.
Qed.

Lemma elevenOverTwelve_le_One : 4^-1 + 3^-1 + 3^-1 < 1 :> R.
Proof.
lra.
Qed.

End R_lemma.

Import Order.POrderTheory GRing.Theory Num.Theory Num.Def Order.TotalTheory.

Section Length.
Let R := Rdefinitions.R.
Variable (X : finType) (n' : nat).
Let n := n'.+1.
Variable P : R.-fdist X.
Variable epsilon : R.
Hypothesis eps_pos : 0 < epsilon.

Lemma fdist_support_LB : 1 <= #|X|%:R :> R.
Proof. rewrite (_ : 1 = 1%:R) // ler_nat; apply/fdist_card_neq0; exact: P. Qed.

Lemma fdist_supp_lg_add_1_neq_0 : 1 + log (#|X|%:R) != 0 :> R.
Proof.
rewrite gt_eqF// ltr_pwDl//.
rewrite -log1 ler_log ?posrE// ?fdist_support_LB//.
by rewrite (lt_le_trans _ fdist_support_LB)//.
Qed.

Definition L_typ := Num.ceil (n%:R * (`H P + epsilon)).
Definition L_not_typ := Num.ceil (log (#| [set : n.-tuple X]|%:R) : R).

Lemma Lt_pos : 0 < L_typ%:~R :> R.
Proof.
apply: (@lt_le_trans _ _ (n%:R * (`H P + epsilon))); last first.
  by rewrite le_ceil.
by rewrite mulr_gt0// ltr_pwDr// entropy_ge0.
Qed.

Lemma Lnt_nonneg : 0 <= L_not_typ%:~R :> R.
Proof.
apply: (@le_trans _ _ (log (#|[set: n.-tuple X]|%:R))); last first.
  by rewrite le_ceil.
rewrite -log1 ler_log ?posrE// cardsT card_tuple.
  by rewrite natrX exprn_ege1// fdist_support_LB.
rewrite natrX exprn_gt0//.
by rewrite (lt_le_trans _ fdist_support_LB).
Qed.

Lemma card_le_TS_Lt : #| `TS P n epsilon |%:R <= #|[ set : `|L_typ|%N.-tuple bool]|%:R :> R.
Proof.
apply: (le_trans (TS_sup _ _ _)).
rewrite cardsT /= card_tuple /= card_bool.
rewrite natrX.
rewrite -exp.powR_mulrn//.
rewrite exp.ler_powR ?ler1n//.
rewrite (le_trans (le_ceil _))//.
rewrite natr_absz ler_int.
by rewrite ler_norm.
Qed.

Lemma card_le_Xn_Lnt' : #| [set: n.-tuple X]|%:R <= #| [set: `|L_not_typ|%N.-tuple bool]|%:R :> R.
Proof.
rewrite /L_not_typ cardsT card_tuple.
rewrite {1}(_ : (expn #|X| n)%:R = 2 `^ (log ((expn #|X| n)%:R))).
- rewrite cardsT card_tuple card_bool.
  rewrite [in leRHS]natrX.
  rewrite -powR_mulrn//.
  rewrite ler_powR ?ler1n//.
  rewrite (le_trans (le_ceil _))//.
  rewrite natr_absz ler_int.
  by rewrite (le_trans (ler_norm _)).
- rewrite LogK// natrX exprn_gt0//.
  by rewrite (lt_le_trans _ fdist_support_LB).
Qed.

End Length.

Section Enc_Dec.
Let R := Rdefinitions.R.
Variable (X : finType) (n' : nat).
Let n := n'.+1.
Variable P : R.-fdist X.
Variable epsilon : R.
Hypothesis eps_pos : 0 < epsilon.

Local Notation "'L_typ'" := (L_typ n' P epsilon).
Local Notation "'L_not_typ'" := (L_not_typ X n').

Definition enc_typ x :=
 let i := seq.index x (enum (`TS P n epsilon))
 in Tuple (size_bitseq_of_nat i (`|L_typ|%N)).

Lemma  card_le_Xn_Lnt :
  (#|[the finType of n.-tuple X] | <= #|[the finType of `|L_not_typ|%N.-tuple bool]|)%nat.
Proof.
rewrite -!cardsT.
rewrite -(ler_nat R).
by rewrite (card_le_Xn_Lnt' n' P).
Qed.

Definition enc_not_typ x := enum_val (widen_ord card_le_Xn_Lnt (enum_rank x)).

Lemma inj_enc_not_typ : injective enc_not_typ.
Proof. by move=> a1 a2 /enum_val_inj [] /ord_inj/enum_rank_inj. Qed.

Definition f : encT X (seq bool) n := fun x =>
  if x \in `TS P n epsilon then
    true :: enc_typ x
  else
    false :: enc_not_typ (tuple_of_row x).

Lemma f_inj : injective f.
Proof.
have card_TS_Lt : (#|`TS P n epsilon| <= (expn 2 (`|L_typ|)))%nat.
  rewrite -(ler_nat R).
  by move: (card_le_TS_Lt n' P epsilon);
       rewrite {1}cardsT card_tuple /= card_bool.
move=> t1 t2; rewrite /f.
case/boolP : (t1 == t2) ; first by move /eqP.
move=> mainCase.
case: ifP=>?; case: ifP=>? //; case=> H; last by apply/tuple_of_row_inj/inj_enc_not_typ/val_inj.
-  have {}H : index t1 (enum (`TS P n epsilon)) =
              index t2 (enum (`TS P n epsilon))
     by apply (@bitseq_of_nat_inj (`|L_typ|%N)) => //;  apply: (leq_trans _ card_TS_Lt);
     apply: seq_index_enum_card => //;  apply: enum_uniq.
 rewrite -(@nth_index _ t1 t1 (enum (`TS P n epsilon))); last by rewrite mem_enum.
 rewrite -(@nth_index _ t1 t2 (enum (`TS P n epsilon))); last by rewrite mem_enum.
 by rewrite H.
Qed.

Definition phi_def : n.-tuple X.
move Hpick : [pick x | x \in [set: X] ] => p;
move: Hpick; case: (pickP _)=>[x _ _ | abs]; first apply: [tuple of nseq n x].
exfalso.
move: (fdist_card_neq0 P).
rewrite -cardsT card_gt0; case/set0Pn => ?.
by rewrite abs.
Defined.

Definition phi : decT X (seq bool) n := fun y =>
 if [ pick x | f x == y ] is Some x then x else row_of_tuple phi_def.

Lemma phi_f x : phi (f x) = x.
Proof.
rewrite /phi.
case:(pickP _)=> [x0 /eqP | H].
-by apply: f_inj.
-by move: (H x); rewrite eqxx.
Qed.

(*Definition extension (enc : encT X (seq bool) n) (x : seq ('rV[X]_n)) :=
flatten (map enc x).
NB: 2015/02/06 -> already defined in uniquely_decodable.v *)

Lemma uniq_decodable_f : uniquely_decodable f.
Proof.
elim => [ | a la H ]; case => [|b lb]; rewrite /extension /= /f //=;
 [by case : ifP |by case : ifP | ].
case: ifP  => aT; case: ifP=> bT //;  move /eqP; rewrite -/f eqseq_cat.
+ by case/andP=>[/eqP eq_ab ] /eqP /H ->; congr (_ :: _); apply: f_inj; rewrite /f aT bT.
+ by rewrite /= !/bitseq_of_nat !size_pad_seqL.
+ by case/andP=>[/eqP eq_ab ] /eqP /H ->; congr (_ :: _); apply: f_inj; rewrite /f aT bT.
+ by rewrite !size_tuple.
Qed.

End Enc_Dec.

Section E_Leng_Cw_Lemma.
Let R := Rdefinitions.R.
Variables (X : finType).
Variable (n' : nat).
Let n := n'.+1.
Variable P : {fdist X}.
Variable epsilon : R.
Hypothesis eps_pos : 0 < epsilon.
Hypothesis aepbound_UB : aep_bound P epsilon <= n%:R.

Local Notation "'L_typ'" := (L_typ n' P epsilon).
Local Notation "'L_not_typ'" := (L_not_typ X n').

Lemma eq_sizef_Lt :
  \sum_(x| x \in `TS P n epsilon) (P `^ n)%fdist (x) * (size (f P epsilon x))%:R =
  \sum_(x| x \in `TS P n epsilon) (P `^ n)%fdist (x) * (L_typ%:~R + 1).
Proof.
apply: eq_bigr=> i H.
congr (_ * _).
rewrite /f H /= size_pad_seqL.
rewrite -natr1 natr_absz.
congr (_ %:~R + _).
rewrite ger0_norm//.
rewrite -(ler_int R) ltW//.
by rewrite Lt_pos.
Qed.

Lemma eq_sizef_Lnt:
  \sum_(x| x \in ~:(`TS P n epsilon)) (P `^ n)%fdist x * (size (f P epsilon x))%:R
  = \sum_(x| x \in ~:(`TS P n epsilon)) (P `^ n)%fdist x * (L_not_typ%:~R + 1) .
Proof.
apply: eq_bigr => ? H.
congr *%R.
move: H; rewrite in_setC.
rewrite /f; move /negbTE ->.
rewrite /= -addn1 size_tuple natrD//.
rewrite natr_absz.
rewrite ger0_norm//.
rewrite -(ler_int R).
by rewrite Lnt_nonneg.
Qed.

Lemma E_leng_cw_le_Length : @E_leng_cw _ _ P (f (n':=n') P epsilon) <=
  (L_typ%:~R + 1) + epsilon * (L_not_typ%:~R + 1) .
Proof.
rewrite /E_leng_cw /Ex /=.
under eq_bigr do rewrite mulrC.
rewrite (rsum_split _ (`TS P n'.+1 epsilon)).
rewrite eq_sizef_Lnt eq_sizef_Lt.
rewrite -!big_distrl/= mulrC.
rewrite (_ : \sum_(i | i \in ~: `TS P n epsilon)
 (P `^ n)%fdist i = 1 - \sum_(i | i \in `TS P n epsilon) (P `^ n)%fdist i); last first.
- rewrite -(FDist.f1 (P `^ n)%fdist) (rsum_split _ (`TS P n epsilon)).
  by rewrite addrAC subrr add0r.
- apply: lerD => //.
  + rewrite -[X in _ <= X]mulr1; apply: ler_wpM2l => //.
    * by apply: addr_ge0 => //; exact/ltW/Lt_pos.
    * by rewrite -(FDist.f1 (P `^ n)%fdist); apply: leR_sumRl => // *.
  + apply: ler_wpM2r => //.
    * by apply addr_ge0 => //; exact (Lnt_nonneg _ P).
    * by rewrite lerBlDr addrC -lerBlDr; exact: Pr_TS_1.
Qed.

End E_Leng_Cw_Lemma.

Section v_scode.
Let R := Rdefinitions.R.
Variable (X : finType) (n' : nat).
Let n := n'.+1.
Variable P : {fdist X}.
Variable epsilon : R.
Hypothesis eps_pos : 0 < epsilon .
Definition epsilon':= epsilon / (3 + (3 * log (#|X|)%:R)).
Definition n0 := maxn (`|(ceil (2 / (1 + @log R (#|X|%:R))))|%N)
                     (maxn (`|(ceil (8 / epsilon))|%N)
                     (`|(ceil (aep_sigma2 P/ epsilon' ^ 3))|%N)).
Hypothesis n0_Le_n : (n0 < n)%nat.

Lemma n0_eps3 :  2 * (epsilon / (3 * (1 + log (#|X|%:R)))) / n%:R < epsilon / 3.
Proof.
move: (fdist_supp_lg_add_1_neq_0 P) => ?.
rewrite (mulrC 2) -!mulrA.
rewrite ltr_pM2l//.
rewrite invfM.
rewrite -mulrA.
rewrite gtr_pMr ?invr_gt0//.
rewrite !mulrA.
rewrite ltr_pdivrMr// mul1r.
rewrite mulrC .
move: n0_Le_n.
rewrite -(ltr_nat R).
apply: le_lt_trans.
rewrite /n0.
rewrite (le_trans (le_ceil _))//.
rewrite (le_trans (ler_norm _))//.
rewrite -intr_norm.
rewrite -natr_absz ler_nat.
by rewrite leq_max leqnn.
Qed.

Lemma n0_eps4 :  2 / n%:R  < epsilon / 4.
Proof.
move: n0_Le_n; rewrite /n0 !gtn_max;  case/andP=> _;  case/andP=> Hyp _.
rewrite ltr_pdivrMr//.
rewrite -ltr_pdivrMl ?divr_gt0//.
rewrite -(ltr_nat R) in Hyp.
rewrite (le_lt_trans _ Hyp)//.
rewrite invfM -mulrA invrK -natrM/= mulrC.
rewrite (le_trans (le_ceil _))//.
rewrite (le_trans (ler_norm _))//.
rewrite -intr_norm.
by rewrite natr_absz.
Qed.

Lemma eps'_pos : 0 < epsilon'.
Proof.
rewrite /epsilon'.
rewrite divr_gt0//.
rewrite ltr_wpDr// mulr_ge0// -log1 ler_log ?posrE//.
  exact: fdist_support_LB.
by rewrite (lt_le_trans _ (fdist_support_LB P)).
Qed.

Lemma le_aepbound_n : aep_bound P epsilon' <= n%:R.
Proof.
move: n0_Le_n.
rewrite -(ltr_nat R) => /ltW; apply: le_trans.
rewrite /n0.
rewrite /aep_bound.
rewrite (le_trans (le_ceil _))//.
rewrite (le_trans (ler_norm _))//.
rewrite -intr_norm.
rewrite -natr_absz.
rewrite ler_nat.
by rewrite !leq_max leqnn !orbT.
Qed.

Lemma lb_entro_plus_eps :
 (L_typ n' P epsilon')%:~R + 1 + epsilon' * ((L_not_typ X n')%:~R + 1) <
   (`H P + epsilon) * n%:R.
Proof.
move : (fdist_supp_lg_add_1_neq_0 P) => ?.
rewrite /L_typ /L_not_typ.
apply: (@le_lt_trans _ _  (n'.+1%:R * (`H P + epsilon') + 1 + 1 +
   epsilon' * (log (#|[set: (n'.+1).-tuple X]|%:R) + 1 + 1))).
- rewrite lerD//.
  + rewrite lerD//.
    rewrite -lerBlDr ltW//.
    rewrite [X in _ - X](_ : 1 = 1%:~R)//.
    by rewrite -intrB gt_pred_ceil.
  + rewrite ler_wpM2l//.
      by rewrite ltW// eps'_pos.
    rewrite lerD2r.
    rewrite -lerBlDr ltW//.
    rewrite [X in _ - X](_ : 1 = 1%:~R)//.
    by rewrite -intrB gt_pred_ceil.
- rewrite cardsT card_tuple log_pow_INR; last by apply: fdist_card_neq0; exact: P.
  rewrite -addrA -addrA -addrA addrC addrA addrC addrA.
  rewrite (_ : 1 + 1 = (1 + 1) * n%:R * n%:R^-1); last first.
    by rewrite -mulrA divff ?mulr1// pnatr_eq0.
  rewrite (mulrC 2 _).
  rewrite -mulrA -!mulrDr.
  rewrite (mulrC epsilon' _) -mulrA.
  rewrite -mulrDr.
  rewrite [ltRHS]mulrC.
  rewrite ltr_pM2l//.
  rewrite -addrA -addrA ltrD2l.
  apply: (@le_lt_trans _ _ (epsilon / 4 + epsilon / 3 + epsilon / 3)); last first.
    rewrite -!mulrDr gtr_pMr//.
    by apply: elevenOverTwelve_le_One.
  rewrite addrCA -addrA.
  rewrite lerD//.
    by rewrite ltW// n0_eps4.
  rewrite {2}/epsilon'.
  rewrite mulrDl addrA lerD//; last first.
    rewrite -mulrA.
    rewrite (mulrC _^-1).
    rewrite ltW//.
    rewrite (le_lt_trans _ n0_eps3)//.
    by rewrite mulrDr mulr1 -mulrA.
  rewrite -/epsilon'.
  rewrite /epsilon'.
  rewrite (mulrCA _ epsilon).
  rewrite -mulrDr ler_pM2l//.
  rewrite -[X in X + _ <= _]mul1r.
  rewrite -mulrDl.
  rewrite -{1}(mulr1 3) -mulrDr mulrC.
  rewrite invfM -mulrA.
  rewrite mulVf//.
  by rewrite mulr1.
Qed.

Lemma v_scode' : exists sc : scode_vl _ n,
  cancel (enc sc) (dec sc) /\
  @E_leng_cw _ _ P (enc sc) / n%:R < `H P + epsilon.
Proof.
move : (fdist_supp_lg_add_1_neq_0 P) => ?.
exists (mkScode (f P epsilon') (phi n' P epsilon')).
split.
  move=> x/=.
  by rewrite phi_f.
rewrite ltr_pdivrMr//.
rewrite (le_lt_trans (E_leng_cw_le_Length eps'_pos le_aepbound_n))//.
by apply: lb_entro_plus_eps.
Qed.

End v_scode.

Section variable_length_source_coding.
Variables (X : finType) (P : {fdist X}).
Let R := Rdefinitions.R.
Variable epsilon : R.
Hypothesis eps_pos : 0 < epsilon.
Local Notation "'n0'" := (n0 P epsilon).

Theorem v_scode_direct : exists n : nat,
  exists f : encT X (seq bool) n,
    injective f /\
    @E_leng_cw _ _ P f / n%:R < `H P + epsilon.
Proof.
apply: (ex_intro _ (n0.+1)).
have: (n0 < n0.+1)%nat by[].
case/v_scode'=> // sc [fphi ccl].
apply: (ex_intro _ (enc sc)).
by split => //; exact: (can_inj fphi).
Qed.

End variable_length_source_coding.
