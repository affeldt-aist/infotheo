(* infotheo: information theory and error-correcting codes in Coq               *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later              *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg matrix.
Require Import Reals Lra.
From mathcomp Require Import Rstruct.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext.
Require Import Rbigop fdist proba entropy aep typ_seq natbin source_code.

(******************************************************************************)
(*        Source coding theorem (variable length, direct part)                *)
(*                                                                            *)
(* For details, see Ryosuke Obi, Manabu Hagiwara, and Reynald Affeldt.        *)
(* Formalization of variable-length source coding theorem: Direct part.       *)
(* International Symposium on Information Theory and Its Applications (ISITA  *)
(* 2014), Melbourne, Australia, October 26--29, 2014, pages 201--205. IEICE.  *)
(* IEEE Xplore, Oct 2014                                                      *)
(*                                                                            *)
(* original source file by R. Obi, quickly patched to compile with infotheo   *)
(* [2019-08-19] and simplified afterwards                                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope typ_seq_scope.
Local Open Scope proba_scope.
Local Open Scope reals_ext_scope.
Local Open Scope entropy_scope.

Local Open Scope R_scope.

Section R_lemma.
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

Lemma log_pow_INR m k : (m > 0)%nat -> log (expn m k)%:R = k%:R * log m%:R.
Proof.
move=> m0; elim: k => [|k ih]; first by rewrite expn0 /log Log_1 mul0R.
rewrite expnS natRM /log LogM ?ltR0n // ?expn_gt0 ?m0 // -!/(log _) ih.
by rewrite -addn1 natRD addRC mulRDl mul1R.
Qed.

Lemma R3neqR0 : 3 <> 0.
Proof. by apply: nesym;apply: Rlt_not_eq; exact: Rplus_lt_pos. Qed.

Lemma zero_ge_4 : 0 < 4. Proof. by apply: Rmult_lt_0_compat. Qed.

Lemma R4neqR0 : 4 <> 0. Proof.  by apply: Rgt_not_eq; apply: zero_ge_4. Qed.

Lemma elevenOverTwelve_le_One : / 4 + / 3 + / 3 < 1.
Proof.
move : R3neqR0 R4neqR0 => ? ?.
apply: (Rmult_lt_reg_r 3); first exact: Rplus_lt_pos.
rewrite 2!mulRDl -Rinv_l_sym // mul1R mulRC.
apply: (Rmult_lt_reg_r 4); first exact: Rmult_lt_0_compat.
rewrite 2!mulRDl -mulRA -Rinv_l_sym //=.
rewrite !(mulR1, mul1R) 2!mulRDl !mul1R.
rewrite addRC; apply: Rplus_lt_compat_l.
apply: Rplus_lt_compat_r; apply: (Rlt_le_trans _ _ _ (Rlt_plus_1 _)).
lra.
Qed.

End R_lemma.

Section Length.
Variable (X : finType) (n' : nat).
Let n := n'.+1.
Variable P : fdist X.
Variable epsilon : R.
Hypothesis eps_pos : 0 < epsilon.

Lemma leng_neq_0 : n%:R <> 0.
Proof. by apply gtR_eqF; rewrite ltR0n. Qed.

Lemma fdist_support_LB : 1 <= INR #|X|.
Proof. rewrite (_ : 1 = INR 1)  //; exact/le_INR/leP/fdist_card_neq0. Qed.

Lemma fdist_supp_lg_add_1_neq_0 : 1 + log (INR #|X|) <> 0.
Proof.
by apply: nesym; apply: Rlt_not_eq; apply: (Rplus_lt_le_0_compat _ _ Rlt_0_1);
 rewrite -(Log_1 2); apply: Log_increasing_le => //; apply: fdist_support_LB.
Qed.

Definition L_typ := ceil (INR n * (`H P + epsilon)).
Definition L_not_typ := ceil (log (INR #| [set : n.-tuple X]|)).

Lemma Lt_pos : 0 < IZR L_typ.
Proof.
apply: (Rlt_le_trans _ (INR n * (`H P + epsilon))); last exact: (proj1 (ceilP _)).
rewrite -(mulR0 0).
apply: (Rmult_le_0_lt_compat _ _ _ _ (Rle_refl _) (Rle_refl _)).
- by apply: lt_0_INR; apply/ltP.
- by apply(Rplus_le_lt_0_compat _ _ (entropy_ge0 P) eps_pos).
Qed.

Lemma Lnt_nonneg: 0 <= IZR L_not_typ.
Proof.
apply: (Rle_trans _ (log (INR #|[set: n.-tuple X]|))); last exact: (proj1 (ceilP _)).
rewrite -(Log_1 2); apply: Log_increasing_le => //.
rewrite cardsT card_tuple -natRexp.
by apply: pow_R1_Rle; apply: fdist_support_LB.
Qed.

Lemma card_le_TS_Lt : INR #| `TS P n epsilon | <= INR #|[ set : (Z.abs_nat L_typ).-tuple bool]|.
Proof.
apply: (Rle_trans _ _ _ (TS_sup _ _ _)).
rewrite cardsT /= card_tuple  /=  card_bool.
rewrite -natRexp2.
apply: Exp_le_increasing => //.
rewrite INR_Zabs_nat.
- exact: (proj1 (ceilP _)).
- by apply: le_IZR; apply: ltRW; apply: Lt_pos.
Qed.

Lemma card_le_Xn_Lnt' : INR #| [set: n.-tuple X]| <= INR #| [set: (Z.abs_nat L_not_typ).-tuple bool]|.
Proof.
have fact : log (INR (expn #|X| n)) <= IZR (ceil (log (INR (expn #|X| n)))).
  exact: (proj1 (ceilP _)).
rewrite /L_not_typ cardsT card_tuple.
rewrite {1}(_ : INR (expn #|X| n) = exp2 (log (INR (expn #|X| n)))).
-rewrite cardsT card_tuple card_bool -natRexp2.
 apply: Exp_le_increasing => //.
 rewrite /L_not_typ INR_Zabs_nat //.
 apply: le_IZR; apply: (Rle_trans _ (log (INR (expn #|X| n)))) => //.
 rewrite /= -(Log_1 2); apply: Log_increasing_le => //.
 rewrite -natRexp.
 by apply: pow_R1_Rle; apply: fdist_support_LB.
-rewrite logK //; last rewrite -natRexp.
 exact/pow_lt/(Rlt_le_trans _ 1 _ _ fdist_support_LB).
Qed.

End Length.

Section Enc_Dec.
Variable (X : finType) (n' : nat).
Let n := n'.+1.
Variable P : fdist X.
Variable epsilon : R.
Hypothesis eps_pos : 0 < epsilon.

Local Notation "'L_typ'" := (L_typ n' P epsilon).
Local Notation "'L_not_typ'" := (L_not_typ X n').

Definition enc_typ x :=
 let i := seq.index x (enum (`TS P n epsilon))
 in Tuple (size_bitseq_of_nat i (Z.abs_nat L_typ)).

Lemma  card_le_Xn_Lnt :
  (#|[finType of n.-tuple X] | <= #|[finType of (Z.abs_nat L_not_typ).-tuple bool]|)%nat.
Proof.
rewrite -!cardsT.
apply/leP.
apply: (INR_le _ _ (card_le_Xn_Lnt' n' P)).
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
have card_TS_Lt : (#|`TS P n epsilon| <= (expn 2 (Z.abs_nat L_typ)))%nat.
  by apply/leP;  apply: INR_le; move: (card_le_TS_Lt n' P eps_pos);
       rewrite {1}cardsT card_tuple /= card_bool.
move=> t1 t2; rewrite /f.
case/boolP : (t1 == t2) ; first by move /eqP.
move=> mainCase.
case: ifP=>?; case: ifP=>? //; case=> H; last by apply/tuple_of_row_inj/inj_enc_not_typ/val_inj.
-  have {}H : index t1 (enum (`TS P n epsilon)) =
              index t2 (enum (`TS P n epsilon))
     by apply (@bitseq_of_nat_inj (Z.abs_nat L_typ)) => //;  apply: (leq_trans _ card_TS_Lt);
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
Variables (X : finType).
Variable (n' : nat).
Let n := n'.+1.
Variable P : fdist X.
Variable epsilon : R.
Hypothesis eps_pos : 0 < epsilon.
Hypothesis aepbound_UB : aep_bound P epsilon <= INR n.

Local Notation "'L_typ'" := (L_typ n' P epsilon).
Local Notation "'L_not_typ'" := (L_not_typ X n').

Lemma eq_sizef_Lt :
  \sum_(x| x \in `TS P n epsilon) P `^ n (x) * (INR (size (f P epsilon x)) ) =
  \sum_(x| x \in `TS P n epsilon) P `^ n (x) * (IZR L_typ + 1).
Proof.
apply: eq_bigr=> i H.
apply: Rmult_eq_compat_l.
rewrite /f H /= size_pad_seqL -INR_Zabs_nat.
-by rewrite -addn1; rewrite plus_INR.
-by apply: le_IZR;apply: ltRW; apply: Lt_pos.
Qed.

Lemma eq_sizef_Lnt:
  \sum_(x| x \in ~:(`TS P n epsilon)) P `^ n (x) * (INR (size (f P epsilon x)) )
  = \sum_(x| x \in ~:(`TS P n epsilon)) P `^ n (x) * (IZR L_not_typ + 1) .
Proof.
apply: eq_bigr => ? H.
apply: Rmult_eq_compat_l.
move: H; rewrite in_setC.
rewrite /f; move /negbTE ->.
rewrite /= -addn1 size_tuple plus_INR INR_Zabs_nat.
-by [].
-by apply: le_IZR; apply: (Lnt_nonneg _ P).
Qed.

Lemma E_leng_cw_le_Length : @E_leng_cw _ _ P (f (n':=n') P epsilon) <=
  (IZR L_typ + 1) + epsilon * (IZR L_not_typ + 1) .
Proof.
rewrite /E_leng_cw /Ex /=.
under eq_bigr do rewrite mulRC.
rewrite (rsum_split _ (`TS P n'.+1 epsilon)).
rewrite eq_sizef_Lnt eq_sizef_Lt -!(big_morph _ (morph_mulRDl _) (mul0R _)) mulRC.
rewrite (_ : \sum_(i | i \in ~: `TS P n epsilon)
 P `^ n i = 1 - \sum_(i | i \in `TS P n epsilon) P `^ n i); last first.
- by rewrite -(FDist.f1 P`^n) (rsum_split _ (`TS P n epsilon)) addRC addRK.
- apply leR_add.
  + rewrite -[X in _ <= X]mulR1; apply: leR_wpmul2l => //.
    * by apply: addR_ge0 => //; exact/ltRW/Lt_pos.
    * by rewrite -(FDist.f1 (P `^ n)); apply: leR_sumRl => // *; exact/leRR.
  + apply: leR_wpmul2r => //.
    * by apply addR_ge0 => //; exact (Lnt_nonneg _ P).
    * by rewrite leR_subl_addr addRC -leR_subl_addr; exact: Pr_TS_1.
Qed.

End E_Leng_Cw_Lemma.

Section v_scode.
Variable (X : finType) (n' : nat).
Let n := n'.+1.
Variable P : fdist X.
Variable epsilon : R.
Hypothesis eps_pos : 0 < epsilon .
Definition epsilon':= epsilon / (3 + (3 * log (INR #|X|))).
Definition n0 := maxn (Z.abs_nat (ceil (INR 2 / (INR 1 + log (INR #|X|)))))
                     (maxn (Z.abs_nat (ceil (8 / epsilon)))
                     (Z.abs_nat (ceil (aep_sigma2 P/ epsilon' ^ 3)))).
Hypothesis n0_Le_n : (n0 < n)%nat.

Lemma n0_eps3 :  2 * (epsilon / (3 * (1 + log (INR #|X|)))) / INR n < epsilon / 3.
Proof.
move : (@leng_neq_0 n') (fdist_supp_lg_add_1_neq_0 P) R3neqR0 => ? ? ?.
rewrite mulRC /Rdiv -?mulRA; apply: (Rmult_lt_compat_l _ _ _ eps_pos); rewrite ?mulRA (mulRC _ 2).
apply: (Rmult_lt_reg_l 3); first exact: Rplus_lt_pos.
rewrite Rinv_mult_distr // ?mulRA (mulRC 3 2) Rinv_r_simpl_l //.
apply: (Rmult_lt_reg_l (INR n)); first exact/ltR0n.
rewrite mulRC -mulRA (mulRC _ (INR n)) ?mulRA Rinv_r_simpl_l // Rinv_r_simpl_l //.
apply: (Rle_lt_trans _ _ _ (proj1 (ceilP _))).
rewrite -INR_Zabs_nat.
-apply: (lt_INR _ _).
 move : n0_Le_n; rewrite /n0 gtn_max.
 by case/andP => /ltP.
-apply: le_IZR;apply: (Rle_trans _ (2 * / (1 + log (INR #|X|)))); last exact: (proj1 (ceilP _)).
 apply: Rmult_le_pos; first exact: ltRW.
 apply: Rlt_le; apply: Rinv_0_lt_compat.
 apply: Rplus_lt_le_0_compat => //.
 rewrite -(Log_1 2).
 apply: Log_increasing_le => //.
 exact: fdist_support_LB.
Qed.

Lemma n0_eps4 :  2 * / INR n  < epsilon / 4.
Proof.
move: (@leng_neq_0 n') R4neqR0 zero_ge_4 => ? ? ?.
have Fact8 : 4 * 2 = 8 by field.
move: n0_Le_n; rewrite /n0 !gtn_max;  case/andP=> _;  case/andP=> Hyp _.
apply: (Rmult_lt_reg_l 4) => //.
rewrite /Rdiv (mulRC epsilon (/ 4)) mulRA mulRA Rinv_r // Fact8 mul1R.
apply: (Rmult_lt_reg_l (INR n)); first exact/ltR0n.
rewrite mulRA (mulRC _ 8) Rinv_r_simpl_l //.
apply: (Rmult_lt_reg_l ( / epsilon)); first by apply: Rinv_0_lt_compat.
rewrite mulRC (mulRC (/ epsilon) (INR n * epsilon)) Rinv_r_simpl_l;
 last by apply: nesym; apply: Rlt_not_eq=>//.
apply: (Rle_lt_trans _ (IZR (ceil (8 * / epsilon))) _ (proj1 (ceilP _))).
rewrite -INR_Zabs_nat.
-by apply: lt_INR; apply/ltP.
-apply: le_IZR;apply: (Rle_trans _ (8 * / epsilon)); last by apply: (proj1 (ceilP _)).
 apply: Rle_mult_inv_pos ; last by apply eps_pos.
 by apply: Rmult_le_pos; exact: ltRW.
Qed.

Lemma eps'_pos : 0 < epsilon'.
Proof.
rewrite /epsilon' /Rdiv -(mulR0 epsilon); apply ltR_pmul2l => //; apply/invR_gt0.
apply: Rplus_lt_le_0_compat; first lra.
apply: Rmult_le_pos; first lra.
rewrite -(Log_1 2).
exact: (Log_increasing_le _ _ (fdist_support_LB P)).
Qed.

Lemma le_aepbound_n : aep_bound P epsilon' <= INR n.
Proof.
rewrite /aep_bound .
apply: (Rle_trans _ _ _ (proj1 (ceilP _))).
rewrite -INR_Zabs_nat.
  apply: ltRW; apply: lt_INR.
  move: n0_Le_n.
  rewrite /n0 !gtn_max.
  case/andP=> _.
  case/andP=> _ H2.
  by apply/ltP.
apply: le_IZR; apply: (Rle_trans _ (aep_sigma2 P / epsilon' ^ 3)); last by apply: (proj1 (ceilP _)).
apply: Rmult_le_pos; first by apply: aep_sigma2_ge0.
by apply: Rlt_le; apply: Rinv_0_lt_compat; apply: (pow_lt _ _ eps'_pos).
Qed.

Lemma lb_entro_plus_eps :
 IZR (L_typ n' P epsilon') + 1 + epsilon' * (IZR (L_not_typ X n') + 1) <
   (`H P + epsilon) * INR n.
Proof.
move : (@leng_neq_0 n') (fdist_supp_lg_add_1_neq_0 P) R3neqR0 R4neqR0 => ? ? ? ?.
rewrite /L_typ /L_not_typ.
apply: (Rle_lt_trans _  (INR n'.+1 * (`H P + epsilon') + 1 + 1 +
   epsilon' * (log (INR #|[set: (n'.+1).-tuple X]|) + 1 + 1))).
-apply: Rplus_le_compat.
 +by apply: Rplus_le_compat; [apply: ltRW; apply: (proj2 (ceilP _)) | apply: Rle_refl].
 +apply: Rmult_le_compat_l; first by apply: Rlt_le; apply: eps'_pos.
   by apply: Rplus_le_compat; [apply: ltRW; apply: (proj2 (ceilP _)) | apply: Rle_refl].
 -rewrite cardsT card_tuple log_pow_INR; last exact: fdist_card_neq0.
  rewrite -addRA -addRA -addRA addRC addRA addRC addRA -(Rinv_r_simpl_l (INR n) (1 + 1)) //.
  rewrite (mulRC 2 _) -{1}mulRA -mulRDr -mulRA -mulRDr (mulRC epsilon' _) -mulRA.
  rewrite (mulRC _ epsilon') -mulRDr mulRC.
  apply: Rmult_lt_compat_r; first by apply: lt_0_INR; apply/ltP.
  rewrite -addRA -addRA; apply: Rplus_lt_compat_l.
  rewrite mulRDr (addRC (epsilon' * log (INR #|X|)) _) addRC addRA -addRA
    (addRC _ epsilon') -{2}(mulR1 epsilon') -mulRDr -addRA
    (addRC (epsilon' * (2 / INR n)) _) addRA addRC  mulRC addRC /epsilon'
    -{1}(mulR1 3) -{3}(mulR1 3) -mulRDr /Rdiv {1}(Rinv_mult_distr) // mulRA
    -mulRA -Rinv_l_sym // mulR1.
  apply: (Rle_lt_trans _ (epsilon / 4 + epsilon * / 3 + epsilon / 3)).
  *apply: Rplus_le_compat.
   +by apply: Rplus_le_compat; [apply: ltRW; apply: n0_eps4 | apply: Rle_refl].
   +by rewrite mulRC /Rdiv (mulRC 2 _) mulRA mulRC mulRA; apply: ltRW; apply: n0_eps3.
  rewrite /Rdiv -?mulRDr -{2}(mulR1 epsilon);  apply: (Rmult_lt_compat_l _ _ _ eps_pos).
by apply: elevenOverTwelve_le_One.
Qed.

Lemma v_scode' : exists sc : scode_vl _ n,
  cancel (enc sc) (dec sc) /\
  @E_leng_cw _ _ P (enc sc) / INR n < `H P + epsilon.
Proof.
move : (@leng_neq_0 n') (fdist_supp_lg_add_1_neq_0 P) R3neqR0 R4neqR0 => ? ? ? ?.
exists (mkScode (f P epsilon') (phi n' P epsilon')).
apply: conj=> [ x |]; first by apply: (phi_f _ eps'_pos).
apply: (Rmult_lt_reg_r (INR n)); first by apply: lt_0_INR; apply/ltP.
rewrite /Rdiv -mulRA -(mulRC (INR n)) Rinv_r // mulR1.
apply: (Rle_lt_trans _ (IZR (L_typ n' P epsilon') + 1 + epsilon' * (IZR (L_not_typ X n') + 1))).
- by apply: E_leng_cw_le_Length; [apply: eps'_pos | apply: le_aepbound_n].
- by apply: lb_entro_plus_eps.
Qed.

End v_scode.

Section variable_length_source_coding.

Variables (X : finType) (P : fdist X).
Variable epsilon : R.
Hypothesis eps_pos : 0 < epsilon .
Local Notation "'n0'" := (n0 P epsilon).

Theorem v_scode_direct : exists n: nat,
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
