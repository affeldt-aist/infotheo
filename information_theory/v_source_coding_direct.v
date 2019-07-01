Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finfun finset bigop.
Require Import Reals Fourier.
Require Import Reals_ext log2 ssr_ext Rbigop proba entropy aep typ_seq natbin Rssr ceiling v_source_code.

Set Implicit Arguments.
Import Prenex Implicits.

Local Open Scope tuple_ext_scope.
Local Open Scope typ_seq_scope.
Local Open Scope proba_scope.
Local Open Scope reals_ext_scope.
Local Open Scope entropy_scope.

Section R_lemma.
Variable (X : finType) (n : nat).
Variable f : X -> R.
Hypothesis n_pos : (0 < n)%nat.
Variable S : {set  X}.

Lemma rsum_mulRC g P: \rsum_(i| P i) f i * g i = \rsum_(i| P i) g i * f i.
Proof.
by apply:eq_bigr=>? _; rewrite mulRC.
Qed.

Lemma rsum_union':
  \rsum_(x| x \in X) f x = \rsum_(x| x \in S ) f x + \rsum_(x| x \in ~: S) f x.
Proof. 
rewrite [X in X = _](_ : _ = \rsum_(x in [set : X]) f(x)); last first.
  by apply:eq_bigl=>i; rewrite in_setT.
apply:rsum_union; first by rewrite disjoints_subset setCS.
by apply/setP=> ?; rewrite !inE orbN.
Qed.

Lemma log_pow_INR k:
  log (INR (n ^ k)) = (INR k) * log (INR n).
Proof. 
elim: k => [| k IH].
  by rewrite mul0R expn0 log_1.
rewrite expnS mult_INR log_mult; first by rewrite IH -addn1 plus_INR mulRDl addRC mul1R.
  apply:lt_0_INR; by apply/ltP.
apply:lt_0_INR; apply/ltP; by rewrite expn_gt0 /orb n_pos.
Qed.

Variable P : dist X.

Lemma dist_support_LB : 1 <= INR #|X|.
Proof.
rewrite (_ : 1 = INR 1) //.
apply:le_INR. 
by apply/leP; apply:(dist_support_not_empty P).
Qed.
End R_lemma.

Section Length.
Variable (X : finType) (n' : nat).
Let n := n'.+1.
Variable P : dist X.
Variable epsilon : R.
Hypothesis ep_pos : 0 < epsilon.

Definition L_typ := ceil (INR n * (`H P + epsilon)).

Definition L_not_typ :=  ceil (log (INR #| [set : n.-tuple X]|)).

Lemma Lt_pos : 0 < IZR L_typ.
Proof.
rewrite /L_typ.
apply:(Rlt_le_trans _ (INR n * (`H P + epsilon))); last by apply:ceil_bottom.
rewrite -(mulR0 0).
apply:(Rmult_le_0_lt_compat _ _ _ _ (Rle_refl _) (Rle_refl _)).
apply:lt_0_INR; by apply/ltP.
by apply(Rplus_le_lt_0_compat _ _ (entropy_pos P) ep_pos).
Qed.

Lemma Lnt_nonneg: 0 <= IZR L_not_typ.
Proof.
apply:(Rle_trans _ (log (INR #|[set: n.-tuple X]|))); last by apply:ceil_bottom.
rewrite -log_1.
apply:(log_increasing_le Rlt_0_1).
rewrite cardsT card_tuple -INR_pow_expn.
by apply:pow_R1_Rle; apply:dist_support_LB. 
Qed.

Lemma card_le_TS_Lt : INR #| `TS P n epsilon | <= INR #|[ set : (Zabs_nat L_typ).-tuple bool]|. 
Proof.
apply:(Rle_trans _ _ _ (TS_sup _ _ _)).
rewrite cardsT /= card_tuple /= card_bool -exp2_pow2.
apply:exp2_le_increasing.
rewrite INR_Zabs_nat; last by apply:le_IZR; apply:RltW; apply:Lt_pos.
by apply:ceil_bottom. 
Qed.

Lemma card_le_Xn_Lnt' : INR #| [set: n.-tuple X]| <= INR #| [set: (Zabs_nat L_not_typ).-tuple bool]|.
Proof.
rewrite /L_not_typ cardsT card_tuple.
rewrite {1}(_ :  INR (#|X| ^ n) = exp2 (log ( INR (#|X|^n)))); last first.
  rewrite exp2_log //; last rewrite -INR_pow_expn.
  apply:pow_lt.
  apply:(Rlt_le_trans _ 1 _ Rlt_0_1 (dist_support_LB P)).
rewrite cardsT card_tuple card_bool -exp2_pow2.
apply:exp2_le_increasing.
rewrite /L_not_typ INR_Zabs_nat; last first.
  apply:le_IZR; apply:(Rle_trans _ (log (INR (#|X|^n)))); last by apply:ceil_bottom.  
  rewrite /= -log_1; apply:(log_increasing_le Rlt_0_1).
  rewrite -INR_pow_expn.
  by apply:pow_R1_Rle; apply:dist_support_LB. 
by apply:(Rle_trans _ _ _ (Rle_refl _) (ceil_bottom _)).
Qed.

End Length.

Section uniquely_decodable.

Variable X : finType.
Variable Y : Type.

Definition extension (enc : X -> seq Y) x:= flatten (map enc x).

Definition uniquely_decodable (enc : X -> seq Y):= injective (extension enc).

End uniquely_decodable.

Section Enc_Dec.
Local Open Scope nat_scope.

Variable (X : finType) (n' : nat).
Let n := n'.+1.
Variable P : dist X.
Variable epsilon : R.
Hypothesis eps_pos : (0 < epsilon)%R.

Local Notation "'L_typ'" := (L_typ n' P epsilon).
Local Notation "'L_not_typ'" := (L_not_typ X n').

Lemma  card_le_Xn_Lnt :
  #|[finType of n.-tuple X] | <= #|[finType of (Zabs_nat L_not_typ).-tuple bool]|.
Proof.
rewrite -!cardsT.
by apply/leP; apply:(INR_le _ _ (card_le_Xn_Lnt' n' P)).
Qed.

Definition enc_not_typ x := enum_val (widen_ord card_le_Xn_Lnt (enum_rank x)).

Lemma inj_enc_not_typ : injective enc_not_typ.
Proof.
by move=> a1 a2 [] /enum_val_inj [] /ord_inj/enum_rank_inj.
Qed.

Definition enc_typ x :=
 let i := seq.index x (enum (`TS P n epsilon))
 in Tuple (size_nat2bin i (Zabs_nat L_typ)).

Definition f : var_enc X n := fun x =>
  if x \in `TS P n epsilon then
    true :: enc_typ x
  else 
    false :: enc_not_typ x.

Lemma f_inj : injective f.
Proof.
move=> t1 t2.
rewrite /f.
case/boolP : (t1 == t2); first by move/eqP.
move=> t1t2.
case: ifP => Ht1.
  case: ifP => Ht2 //.
  case=> H.
  have {H}H : seq.index t1 (enum (`TS P n epsilon)) =
              seq.index t2 (enum (`TS P n epsilon)).
    have card_TS_Lt :  #|`TS P n epsilon| <= (2 ^ Z.abs_nat L_typ).
      apply/leP.
      apply:INR_le.
      move: (card_le_TS_Lt n' P eps_pos).
      by rewrite {1}cardsT card_tuple /= card_bool.
    apply:(nat2bin_inj (Zabs_nat L_typ)) => //. 
    apply:(leq_trans _ card_TS_Lt).
      apply:seq_index_enum_card => //; by apply: enum_uniq.
    apply:(leq_trans _ card_TS_Lt).
      apply:seq_index_enum_card => //; by apply: enum_uniq.
  rewrite -(@nth_index _ t1 t1 (enum (`TS P n epsilon))); last by rewrite mem_enum.
  rewrite -(@nth_index _ t1 t2 (enum (`TS P n epsilon))); last by rewrite mem_enum.
  by rewrite H.
case: ifP => Ht2 //.
case => ?.
apply:(inj_enc_not_typ t1 t2).
by apply:val_inj.
Qed.


Definition phi_def : n.-tuple X.
move: (dist_support_not_empty P) => H.
move Hpick : [pick x | x \in [set: X] ] => p.
move: Hpick.
case: (pickP _)=>[x _ _ | abs H']; first apply:[tuple of nseq n x].
suff : False by [].
move: H; rewrite -cardsT card_gt0.
case/set0Pn => ?.
by rewrite abs.
Defined.

Definition phi y := if [ pick x | f x == y ] is Some x then x else phi_def.

Lemma phi_f x : phi (f x) = x.
Proof.
rewrite /phi.
case:(pickP _) => [x0 /eqP | H].
  by apply:f_inj.
move: (H x).
by rewrite eqxx.
Qed.

Lemma uniquely_decodable_f : uniquely_decodable ([finType of n.-tuple X]) f.
Proof.
move=>t1.
elim: t1=>[t2|a la H t2].
  by case:t2=>[|a la] //; rewrite /extension /f /=; case: ifP.
case: t2=>[|b lb]; [by rewrite /extension /f /=; case: ifP | rewrite /extension /= /f ].
case: ifP=> [ainT | aninT].
  case: ifP=> binT //.
  move/eqP.
  rewrite -/f eqseq_cat; last by rewrite /= !/nat2bin !size_pad_seqL.
  case/andP=>[/eqP eq_ab ] /eqP /H ->.
  congr (_ :: _); by apply:f_inj; rewrite /f ainT binT.
case: ifP=> bninT //.
move/eqP.
rewrite  -/f eqseq_cat; last by rewrite !size_tuple. 
case/andP=>[/eqP eq_ab ] /eqP /H ->.
congr (_ :: _); by apply:f_inj; rewrite /f aninT bninT.
Qed. 

End Enc_Dec.

Section exp_len_cw_def.
Variable (X : finType) (n :nat).
Variable f : var_enc X n.
Variable P : dist X.

Definition exp_len_cw := 
  \rsum_(x in [finType of n.-tuple X])( P`^n(x) * (INR (size (f x)))).

Lemma exp_len_cw' : exp_len_cw = `E (mkRvar (P `^ n) (fun x => INR (size (f x)))).
Proof.
rewrite /exp_len_cw /Ex_alt /=.
by rewrite rsum_mulRC.
Qed.

End exp_len_cw_def.

Section exp_len_cw_lemma.
Variable (X : finType) (n' : nat).
Let n := n'.+1.
Variable P : dist X.
Variable epsilon:R.
Hypothesis eps_pos: 0 < epsilon.
Hypothesis aepbound_UB : aep_bound P epsilon <= INR n.

Local Notation "'L_typ'" := (L_typ n' P epsilon).
Local Notation "'L_not_typ'" := (L_not_typ X n').

Lemma eq_sizef_Lt :
  \rsum_(x| x \in `TS P n epsilon) P `^ n (x) * (INR (size (f P epsilon x)) ) =
  \rsum_(x| x \in `TS P n epsilon) P `^ n (x) * (IZR L_typ + 1).
Proof.
apply:eq_bigr=> i H.
apply:Rmult_eq_compat_l.
rewrite /f H /= size_pad_seqL -INR_Zabs_nat; last by apply:le_IZR;apply:RltW; apply:Lt_pos.
by rewrite -addn1; rewrite plus_INR.
Qed.

Lemma eq_sizef_Lnt:
  \rsum_(x| x \in ~:(`TS P n epsilon)) P `^ n (x) * (INR (size (f P epsilon x)) )
  = \rsum_(x| x \in ~:(`TS P n epsilon)) P `^ n (x) * (IZR L_not_typ + 1) .
Proof.
apply:eq_bigr=> i H.
apply:Rmult_eq_compat_l.
move:H;rewrite /f in_setC.
move/negbTE ->.
rewrite /= -addn1 size_tuple plus_INR.
by rewrite INR_Zabs_nat; last by apply:le_IZR;apply:(Lnt_nonneg _ P).
Qed.

Lemma exp_len_cw_le_Length : exp_len_cw (f (n':=n')P epsilon) P <= (IZR L_typ + 1) + epsilon * (IZR L_not_typ + 1) .
Proof.
rewrite /exp_len_cw (rsum_union' _ (`TS P n'.+1 epsilon)).
rewrite eq_sizef_Lnt eq_sizef_Lt.
rewrite -!(big_morph _ (morph_mulRDl _) (mul0R _)) mulRC.
rewrite (_ : \rsum_(i | i \in ~: `TS P n epsilon) P `^ n i = 1 - \rsum_(i | i \in `TS P n epsilon) P `^ n i); last first. 
  rewrite -(pmf1 P`^n) (rsum_union' _ (`TS P n epsilon)).
  by rewrite addRC /Rminus -addRA Rplus_opp_r addR0.
apply:Rplus_le_compat.
  rewrite -[X in _ <= X]mulR1.
  apply:Rmult_le_compat_l. 
    apply:(Rplus_le_le_0_compat _ _ _ Rle_0_1); by apply:RltW; apply:Lt_pos.
  rewrite -(pmf1 P`^ n). 
  apply:Rle_big_f_X_Y=> //; by move=> ?; apply:Rle0f.
apply:Rmult_le_compat_r.
  by apply:(Rplus_le_le_0_compat _ _ (Lnt_nonneg _ P) Rle_0_1).
apply:Rminus_le.
rewrite /Rminus addRC addRA.
apply:Rle_minus.
rewrite addRC.
by apply:Rge_le; apply:Pr_TS_1.
Qed.

End exp_len_cw_lemma.

Section vscode.
Variable (X : finType) (n : nat).
Variable P : dist X.
Variable epsilon : R.
Hypothesis eps_pos : 0 < epsilon .
Definition epsilon':= epsilon / (3 + (3 * log (INR #|X|))).
Definition n0 := maxn (Zabs_nat (ceil (INR 2 / (INR 1 + log (INR #|X|))))) 
                     (maxn (Zabs_nat (ceil (8 / epsilon)))
                     (Zabs_nat (ceil (aep_sigma2 P/ epsilon' ^ 3)))).
Hypothesis n0_n : (n0 < n)%coq_nat.

Definition n' := n.-1.
Lemma n_pos : n = n'.+1.
by apply:(S_pred _ _ n0_n).
Qed.

Lemma n0_eps3 :  2 * (epsilon / (3 * (1 + log (INR #|X|)))) / INR n < epsilon / 3.
Proof.
have Hfrac1: INR n <> 0.
  apply:nesym; apply:Rlt_not_eq. 
  rewrite n_pos.
  by apply:lt_0_INR; apply/ltP.
have Hfrac2 : 1 + log (INR #|X|) <> 0.
  apply:nesym; apply:Rlt_not_eq; apply:(Rplus_lt_le_0_compat _ _ Rlt_0_1).
  rewrite -log_1.
  apply:(log_increasing_le Rlt_0_1).
  by apply:dist_support_LB.
have Hfrac3 : 3 <> 0.
  apply:nesym;apply:Rlt_not_eq.
  by apply:Rplus_lt_pos; [apply:Rlt_0_1 | apply:Rlt_0_2].
rewrite (_ : 2 * _ / _ = epsilon * (2 /  (3 * (1 + log (INR #|X|))) / INR n)); last first.
  rewrite mulRC /Rdiv -mulRA -mulRA; apply:Rmult_eq_compat_l.
  rewrite mulRC -mulRA -[in RHS]mulRA; apply:Rmult_eq_compat_l.
  by rewrite mulRC.
apply:(Rmult_lt_compat_l _ _ _ eps_pos).
apply:(Rmult_lt_reg_l 3); first by apply:Rplus_lt_pos; [apply:Rlt_0_1 | apply:Rlt_0_2].
rewrite (_ : 3 * _ = 2 * 3 / 3 / (1 + log (INR #|X|)) * / INR n); last first.
  rewrite (_ : 2 = INR 2) // (_ : 3 = INR 3); last by rewrite S_O_plus_INR. 
  rewrite -[in RHS]mulRA -[in RHS]mulRA -[in RHS]mulRA mulRC /Rdiv -mulRA -mulRA.
  apply:Rmult_eq_compat_l.
  rewrite mulRA mulRC; apply:Rmult_eq_compat_l.
  rewrite mulRA Rinv_mult_distr //; apply:nesym; apply:Rlt_not_eq.
  by apply:lt_0_INR; apply/leP.
rewrite /Rdiv Rinv_r_simpl_l //.
apply:(Rmult_lt_reg_l (INR n)); first by rewrite n_pos; apply:lt_0_INR; apply/ltP.
rewrite (_ : _ * _ = (2 * / (1 + log (INR #|X|)) * INR n  * / INR n)); last first.
  by rewrite mulRC -mulRA -[in RHS]mulRA; apply:Rmult_eq_compat_l; rewrite mulRC.
rewrite Rinv_r_simpl_l //.
apply:(Rle_lt_trans _ _ _ (ceil_bottom _)).
rewrite -INR_Zabs_nat; last first.
  apply:le_IZR;apply:(Rle_trans _ (2 * / (1 + log (INR #|X|)))); last by apply:ceil_bottom.
  apply:Rmult_le_pos; first by apply:RltW; apply:Rlt_0_2.
  apply:Rlt_le; apply:Rinv_0_lt_compat.
  apply:(Rplus_lt_le_0_compat _ _ Rlt_0_1).
  rewrite -log_1.
  apply:(log_increasing_le Rlt_0_1).
  by apply:dist_support_LB.
rewrite Rinv_r // mulR1.
apply:(lt_INR _ _).
move/ltP : n0_n.
rewrite /n0 gtn_max.
by case/andP => /ltP.
Qed.

Lemma n0_eps4 :  2 * / INR n  < epsilon / 4.
Proof.
have Hfrac1: INR n <> 0.
  apply:nesym; apply:Rlt_not_eq. 
  rewrite n_pos.
  by apply:lt_0_INR; apply/ltP.
have Hfrac2 : 4 <> 0.
  apply:nesym; apply:Rlt_not_eq.
  by apply:Rmult_lt_0_compat; [apply:Rlt_0_2|apply:Rlt_0_2].
apply:(Rmult_lt_reg_l 4); first by apply:Rmult_lt_0_compat; [apply:Rlt_0_2|apply:Rlt_0_2].
rewrite /Rdiv (mulRC epsilon (/ 4)) mulRA mulRA Rinv_r //.
apply:(Rmult_lt_reg_l (INR n)); first by rewrite n_pos; apply:lt_0_INR; apply/ltP. 
rewrite (_ : _ * (_ * _ * / _) = 8 * INR n * / INR n); last first. 
  rewrite mulRC -[in RHS]mulRA -mulRA (mulRC (INR n) _) mulRC [in RHS]mulRC. 
  apply:Rmult_eq_compat_l.
  by rewrite mulRA.
rewrite Rinv_r_simpl_l //.
apply:(Rmult_lt_reg_l ( / epsilon)); first by apply:Rinv_0_lt_compat.
rewrite mul1R (mulRC (/ epsilon) (INR n * epsilon)).
rewrite Rinv_r_simpl_l; last by apply:nesym; apply:Rlt_not_eq=>//.
rewrite mulRC.
apply:(Rle_lt_trans _ (IZR (ceil (8 * / epsilon))) _ (ceil_bottom _)).
rewrite -INR_Zabs_nat.
  apply:lt_INR.
  move/ltP : n0_n.
  rewrite /n0 !gtn_max.
  case/andP=> H. 
  case/andP=> H1 H2.
  by apply/ltP.
apply:le_IZR;apply:(Rle_trans _ (8 * / epsilon)); last  by apply:ceil_bottom.
apply:(Rmult_le_reg_l epsilon _ _ eps_pos).
rewrite (mulRC 8  (/ epsilon)) mulRA Rinv_r; last by apply:nesym; apply:Rlt_not_eq=>//.
rewrite mulR0 mul1R.
apply:Rmult_le_pos; first by apply:RltW; apply:Rlt_0_2.
by apply:Rmult_le_pos; [apply:RltW; apply:Rlt_0_2 | apply:RltW; apply:Rlt_0_2].
Qed.

Lemma eps'_pos : 0 < epsilon'.
Proof. 
rewrite /epsilon' /Rdiv. 
rewrite -(mulR0 epsilon).
apply:Rmult_lt_compat_l=>//.
apply:Rinv_0_lt_compat.
apply:Rplus_lt_le_0_compat; first by apply:(Rlt_zero_pos_plus1 _ Rlt_R0_R2).
apply:Rmult_le_pos; first by apply:Rle_zero_pos_plus1; apply:(Rle_zero_pos_plus1 _ Rle_0_1).
rewrite -log_1.
by apply:(log_increasing_le Rlt_0_1 (dist_support_LB P)).
Qed.


Lemma le_aepbound_n : aep_bound P epsilon' <= INR n.
Proof.
rewrite /aep_bound .
apply:(Rle_trans _ _ _ (ceil_bottom _)).
rewrite -INR_Zabs_nat.
  apply:RltW; apply:lt_INR.
  move/ltP : n0_n.
  rewrite /n0 !gtn_max.
  case/andP=> H. 
  case/andP=> H1 H2.
  by apply/ltP.
apply:le_IZR;apply:(Rle_trans _ (aep_sigma2 P / epsilon' ^ 3)); last by apply:(ceil_bottom _).
apply:Rmult_le_pos; first by apply:aep_sigma2_pos.
by apply:Rlt_le; apply:Rinv_0_lt_compat; apply:(pow_lt _ _ eps'_pos).
Qed. 

Lemma v_scode' : exists (f : var_enc X n) (phi : var_dec X n) , 
                         (forall x, phi (f x) = x) /\
                         (exp_len_cw f P) / (INR n) < (`H P + epsilon).
Proof.
rewrite n_pos.
exists (f P epsilon') .
exists (phi n' P epsilon').
apply:conj=> [ x |]; first by apply:(phi_f _ eps'_pos).
have Hfrac1: INR n <> 0.
  apply:nesym; apply:Rlt_not_eq. 
  rewrite n_pos.
  by apply:lt_0_INR; apply/ltP.
have Hfrac2 : 1 + log (INR #|X|) <> 0.
  apply:nesym; apply:Rlt_not_eq; apply:(Rplus_lt_le_0_compat _ _ Rlt_0_1).
  rewrite -log_1.
  apply:(log_increasing_le Rlt_0_1).
  by apply:dist_support_LB.
have Hfrac3 : 3 <> 0.
  apply:nesym;apply:Rlt_not_eq.
  by apply:Rplus_lt_pos; [apply:Rlt_0_1 | apply:Rlt_0_2].
rewrite -{2}n_pos .
apply:(Rmult_lt_reg_r (INR n)); first by rewrite n_pos; apply:lt_0_INR; apply/ltP.
rewrite /Rdiv -mulRA -(mulRC (INR n)).
rewrite Rinv_r // mulR1.
apply:(Rle_lt_trans _ (IZR (L_typ n' P epsilon') + 1 + epsilon' * (IZR (L_not_typ X n') + 1))).
  by apply:exp_len_cw_le_Length;[apply:eps'_pos | rewrite -n_pos; apply:le_aepbound_n].
rewrite /L_typ /L_not_typ.
apply:(Rle_lt_trans _  (INR n'.+1 * (`H P + epsilon') + 1 + 1 +
   epsilon' * (log (INR #|[set: (n'.+1).-tuple X]|) + 1 + 1))).
  apply:Rplus_le_compat.
    by apply:Rplus_le_compat; by [apply:RltW; apply:ceil_upper | apply:Rle_refl].
  apply:Rmult_le_compat_l; first by apply:Rlt_le; apply:eps'_pos.
  by apply:Rplus_le_compat; by [apply:RltW; apply:ceil_upper | apply:Rle_refl].
rewrite cardsT card_tuple.
rewrite log_pow_INR; last by apply:(dist_support_not_empty P).
rewrite -addRA -addRA -addRA addRC addRA addRC addRA -n_pos -(Rinv_r_simpl_l (INR n) 2) //.
rewrite (_ :  _ * _ + _ * _ / _ =
              INR n * (`H P + epsilon' + 2 / INR n)) ;last first. 
  by rewrite !Rmult_plus_distr_l /Rdiv -mulRA (mulRC _ (2 / INR n)) (mulRC _ (/ INR n)) -mulRA.
rewrite (_ :  _ * _ * / _ = INR n * (2  / INR n)); last first.
  by rewrite -mulRA mulRC -mulRA (mulRC _ 2) mulRA.
rewrite -Rmult_plus_distr_l.
rewrite (mulRC epsilon' _) -mulRA (mulRC _ epsilon') -Rmult_plus_distr_l mulRC.
apply:Rmult_lt_compat_r; first by rewrite n_pos;  apply:lt_0_INR; apply/ltP.
rewrite -addRA -addRA.
apply:Rplus_lt_compat_l.
rewrite Rmult_plus_distr_l.
rewrite (addRC (epsilon' * log (INR #|X|)) _) addRC addRA -addRA.
rewrite (addRC _ epsilon') -{2}(mulR1 epsilon') -Rmult_plus_distr_l.
rewrite -addRA (addRC (epsilon' * (2 / INR n)) _) addRA addRC  mulRC addRC.
rewrite /epsilon' -{1}(mulR1 3) -{3}(mulR1 3) -Rmult_plus_distr_l.
rewrite {2}/Rdiv {1}(Rinv_mult_distr) //.
rewrite mulRA -mulRA -Rinv_l_sym // mulR1.
apply:(Rle_lt_trans _ (epsilon / 4 + epsilon * / 3 + epsilon / 3)).
  apply:Rplus_le_compat.
    by apply:Rplus_le_compat; by [apply:RltW; apply:n0_eps4 | apply:Rle_refl].
  rewrite mulRC /Rdiv (mulRC 2 _) mulRA mulRC mulRA.
  by apply:RltW; apply:n0_eps3.
rewrite (_ : _ / _ + _ / _ + _ / _ = epsilon * ( / 4 + / 3 + / 3)); last first.
  by rewrite !Rmult_plus_distr_l.
rewrite -{2}(mulR1 epsilon).
apply:(Rmult_lt_compat_l _ _ _ eps_pos).
apply:(Rmult_lt_reg_r 3); first by apply:Rplus_lt_pos; [apply:Rlt_0_1 | apply:Rlt_0_2].
rewrite Rmult_plus_distr_r Rmult_plus_distr_r -Rinv_l_sym // mul1R mulRC.
apply:(Rmult_lt_reg_r 4); first   by apply:Rmult_lt_0_compat; [apply:Rlt_0_2|apply:Rlt_0_2].
rewrite Rmult_plus_distr_r Rmult_plus_distr_r -mulRA -Rinv_l_sym; last first.
  apply:nesym; apply:Rlt_not_eq.
  by apply:Rmult_lt_0_compat; [apply:Rlt_0_2 | apply:Rlt_0_2].
rewrite mulR1 mul1R !Rmult_plus_distr_r !Rmult_plus_distr_l mulR1 mul1R.
rewrite addRC; apply:Rplus_lt_compat_l.
rewrite addRC; apply:Rplus_lt_compat_l.
by apply:Rplus_lt_compat_r; apply:Rlt_plus_1.
Qed.

End vscode.

Section variable_length_source_coding.

Variable (X : finType) (n : nat).
Variable P : dist X.
Variable epsilon : R.
Hypothesis eps_pos : 0 < epsilon .
(*Definition n0 := maxn 
          (Z.to_nat (ceil (INR 2 / (INR 1 + log (INR #|X|))))) 
          (maxn (Z.to_nat (ceil (8 / epsilon)))
          (Z.to_nat (ceil (aep_sigma2 P/ epsilon' ^ 3)))).*)
Local Notation "'n0'" := (n0 P epsilon).

Theorem vscode : (n0 < n)%nat -> 
  exists f : var_enc X n,
    injective f /\
    exp_len_cw f P / INR n < `H P + epsilon.
Proof.
move/ltP=>le_n0_n.
set n' := n.-1.
have n_pos: n = n'.+1 by apply:(S_pred _ _ le_n0_n).
move:le_n0_n; rewrite n_pos.
case/v_scode' => // f [phi [fphi ccl]].
apply:(ex_intro _ f).
apply:conj=>//.
by apply:(can_inj fphi).
Qed.

End variable_length_source_coding.
