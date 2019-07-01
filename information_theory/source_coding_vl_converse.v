Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
Require Import tuple finfun bigop prime binomial ssralg finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import Reals_ext log2 ssr_ext ssralg_ext Rbigop proba entropy Rssr ceiling.
Require Import divergence log_sum source_code.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope tuple_ext_scope.
(*Local Open Scope typ_seq_scope.*)
Local Open Scope proba_scope.
Local Open Scope reals_ext_scope.
Local Open Scope entropy_scope.
Local Open Scope divergence_scope.

Section log_sum_ord.
Variable A : finType.
Variable n: nat.
Variable f g: nat -> R+.
Hypothesis f_dom_by_g : f << g.

Lemma log_sum_inequality_ord:
  \rsum_(i| i \in 'I_n) (f i * (log (f i / g i))) >= 
  (\rsum_(i| i \in 'I_n) f i) * (log ((\rsum_(i| i \in 'I_n) f i) / (\rsum_(i| i \in 'I_n) g i))).
Proof.
have Rle0f': forall (x : [finType of 'I_n]), 0 <= f x by move=> ?; apply:(Rle0f f).
have Rle0g': forall (x : [finType of 'I_n]), 0 <= g x by move=> ?; apply:(Rle0f g).
have H:forall h, \rsum_(a | a \in [set: 'I_n]) h a = \rsum_(a | a \in  'I_n) h a. 
  by move=>?; apply:eq_bigl=>?; rewrite in_setT.
rewrite -!H /=; apply: Rle_ge.
by apply: (log_sum [set: 'I_n] (mkPosFun Rle0f') (mkPosFun Rle0g') f_dom_by_g).
Qed.

Lemma log_sum_inequality_ord_add1: 
  \rsum_(i| i \in 'I_n) f i.+1 * (log (f i.+1 / g i.+1)) >= 
  (\rsum_(i| i \in 'I_n) f i.+1) * (log ((\rsum_(i| i \in 'I_n) f i.+1) / (\rsum_(i| i \in 'I_n) g i.+1))).
Proof.
have Rle0f_add1: forall (x : [finType of 'I_n]), 0 <= f x.+1 by move=> ?; apply:(Rle0f f).
have Rle0g_add1: forall (x : [finType of 'I_n]), 0 <= g x.+1 by move=> ?; apply:(Rle0f g).
have f_dom_by_g1 : (mkPosFun Rle0f_add1) << (mkPosFun Rle0g_add1).
  by rewrite /dom_by=>?; apply:f_dom_by_g.
have H:forall h, \rsum_(a | a \in [set: 'I_n]) h a.+1 = \rsum_(a | a \in  'I_n) h a.+1.
  by move=>?; apply:eq_bigl=>?; rewrite in_setT.
rewrite -!H -(H (fun i => f i * log (f i / g i))); apply: Rle_ge.
apply: (log_sum [set: 'I_n] (mkPosFun Rle0f_add1) (mkPosFun Rle0g_add1) f_dom_by_g1).
Qed.

Lemma log_sum_inequality_ord_add1':
  \rsum_(i| i \in 'I_n) f i.+1 * (log (f i.+1) - log (g i.+1)) >= 
  (\rsum_(i| i \in 'I_n) f i.+1) * (log (\rsum_(i| i \in 'I_n) f i.+1) - log (\rsum_(i| i \in 'I_n) g i.+1)).
Proof.
rewrite [X in X >= _](_ : _ = \rsum_(i | i \in 'I_n) f i.+1 * log (f i.+1 / (g i.+1))).
  rewrite [X in _ >= X](_ : _ =  (\rsum_(i | i \in 'I_n) f i.+1) *
   (log ((\rsum_(i | i \in 'I_n)f i.+1) / (\rsum_(i | i \in 'I_n) g i.+1)))).
      by apply: log_sum_inequality_ord_add1.
  have :0 <= \rsum_(i | i \in 'I_n) f i.+1 by apply: Rle_big_0_P_g=>i _; apply: Rle0f.
  case=>[Hf | <-]; last by rewrite !mul0R.
  have : 0 <= \rsum_(i | i \in 'I_n) g i.+1 by apply: Rle_big_0_P_g=>i _; apply: Rle0f.
  case=>[Hg |].
    rewrite log_mult//; last by apply: Rinv_0_lt_compat.
    by rewrite log_Rinv.
  have Rle0g_add1: forall (x : ordinal_finType n), 0 <= g x.+1 by move=> ?; apply:(Rle0f g).
  move/(Req_0_rmul_inv (fun i => i \in 'I_n) _ Rle0g_add1)=>eq_g_0.
  have : 0 = \rsum_(i | i \in 'I_n) f i.+1.
    by apply:Req_0_rmul=>i _; apply:esym; apply: (@f_dom_by_g i.+1); rewrite -eq_g_0.
  by move=>tmp; move:Hf; rewrite -tmp; move/Rlt_not_eq.
apply: eq_bigr=>i _.
case:(Rle0f f i.+1)=>[fpos|<-]; last by rewrite !mul0R.
  case:(Rle0f g i.+1)=>[gpos|]; last by  move/esym/(@f_dom_by_g i.+1)->; rewrite !mul0R.
  rewrite log_mult//; last by apply: Rinv_0_lt_compat.
  by rewrite log_Rinv.
Qed.

End log_sum_ord.

Section Ordinal.
Variable T : finType.
Variable f : T -> nat.

Definition inordf t := inord (f t) : [finType of 'I_(\max_t f t).+1].

Lemma inordf_eq : f =1 inordf.
Proof. move=> t; rewrite /inordf inordK //; by apply: leq_bigmax. Qed.

End Ordinal.
Prenex Implicits inordf.

Section Big_pow.
End Big_pow.

Section Bigop_Lemma.
Variable A : finType.

Lemma rsum_mulRC (h : A -> R) g P: \rsum_(i| P i) h i * g i = \rsum_(i| P i) g i * h i.
Proof.
by apply: eq_bigr=>? _; rewrite mulRC.
Qed.

Variable P : dist A.
Variable n : nat.
Variable f : A -> seq bool.
Hypothesis f_inj : injective f.

Lemma big_seq_tuple (F : seq bool -> R): (0 < #|A|)%nat ->
  \big[Rplus/0]_(i <- [seq f i | i <- index_enum A] | size i == n) F i =
  \big[Rplus/0]_(i : n.-tuple bool | tval i \in codom f) F i.
Proof.
move Hpick : [pick x | x \in [set: A] ] => p Anon0.
move: Hpick; case: (pickP _)=>[defaultA _ _ | abs]; last first.  
  suff : False by [].
  move:Anon0.
  rewrite -cardsT card_gt0; case/set0Pn => ?.
  by rewrite abs.
rewrite big_map.
 pose dummy := [tuple of nseq n false].
 pose h (i : n.-tuple bool) := odflt defaultA [pick a | f a == i].
 pose h' a : n.-tuple bool := insubd dummy (f a).
 have H a : odflt defaultA [pick a0 | f a0 == f a ] = a.
 - case: pickP => /=; last by move/(_ a); rewrite eqxx.
   by move => a0 /eqP /f_inj ->.
 - rewrite (reindex_onto h h'); last first.
   + move => a sizefa. rewrite /h' /h insubdK //.
   + apply: esym.
     apply: eq_big => i; last by move/codomP => [a fa]; rewrite /h fa H.
     apply/idP/andP.
     * move/codomP => [a fa]. rewrite /h fa H.
       split; first by rewrite -fa size_tuple eqxx.
       by rewrite /h' -fa valKd.
     * rewrite /h /h' => [] [sizefhi /eqP <-]; rewrite insubdK //.
       exact: codom_f.
Qed.

Lemma big_seq_tuple' (F : seq bool -> R): (0 < #|A|)%nat ->
  (forall i, F i = if i \in codom f then F i else 0)->
  \big[Rplus/0]_(i in {: n.-tuple bool}) F i =
  \big[Rplus/0]_(i| size (f i) == n) F (f i).
Proof.
move=>Anon0 Fi0.
rewrite -(big_map f (fun i0 => size i0 == n) (fun x => F x )) /=.
rewrite big_seq_tuple //.
rewrite (eq_bigr (fun a => if (tval a \in codom f) then F a else 0))=>[|i _].
  rewrite -big_mkcondr/=.
  by apply: eq_bigl=>//.
case:ifP=>//. 
by rewrite Fi0; move->.
Qed.

Lemma big_ord_exclude0 (h:nat -> R): h 0%nat = 0 -> 
    \rsum_(i | i \in 'I_n.+1) h i = \rsum_(i | i \in 'I_n) h i.+1.
Proof.
move=>H.
rewrite -(big_mkord xpredT _) -(big_mkord xpredT (fun i => h i.+1)).
by rewrite big_ltn// H add0R big_add1.
Qed.

Variable x : R.
Hypothesis neq_x_1 : x <> 1.

Lemma big_pow1 : \rsum_(i | i \in 'I_n) x ^ i.+1 = x * (1 - (x ^ n)) / (1 - x).
Proof.
apply: (Rplus_eq_reg_l 1).
rewrite /Rdiv {1}[in RHS](Rinv_r_sym (1 - x)); last by apply:Rminus_eq_contra; apply: nesym.
rewrite Rmult_plus_distr_l mulR1 -Rmult_plus_distr_r addRA /Rminus [in RHS]addRC -addRA.
rewrite Rplus_opp_l addR0 (addRC _ 1) Ropp_mult_distr_r_reverse.
rewrite -(big_mkord xpredT (fun i => x ^ i.+1)) (_ : n = n.+1.-1) //.
rewrite -(big_add1 _ _ _ _  xpredT)-{1}(pow_O x) -big_ltn//.
by rewrite big_mkord -sum_f_R0_rsum tech3.
Qed.

Lemma log_pow r: 0 < r -> log (r ^ n) = (INR n) * log r.
Proof.
elim:n=> [|n' IH lt_0_r]; first by rewrite log_1 mul0R.
rewrite log_mult//;last by apply:pow_lt.
by rewrite IH // -addn1 addRC plus_INR Rmult_plus_distr_r mul1R.
Qed.

End Bigop_Lemma.

Local Open Scope vec_ext_scope.

Section Entropy_lemma.

Variable A : finType.
Variable P : dist A.
Variable n : nat.

Lemma entropy_TupleDist : `H (P `^ n) = (INR n) * `H P.
Proof.
elim:n=>[|n0 IH]. 
  rewrite /entropy /= /TupleDist.f rsum_0rV /=.
  by rewrite big_ord0 log_1 mulR0 mul0R Ropp_0.
rewrite S_INR Rmult_plus_distr_r mul1R -IH.
rewrite /entropy -big_head_behead /= /TupleDist.f /=. 
rewrite -Ropp_plus_distr; apply:Ropp_eq_compat.
rewrite [X in X = _](_ :_ = \rsum_(i | i \in A) P i * log (P i) * 
          (\rsum_(j in 'rV[A]_n0) (\rmul_(i0 < n0) P j /_ i0)) +
           \rsum_(i | i \in A) P i * \rsum_(j in 'rV[A]_n0)
          (\rmul_(i0 < n0) P j /_ i0) * log (\rmul_(i0 < n0) P j /_ i0)); last first.
  rewrite -big_split /=.
  apply:eq_bigr=> i _.
  rewrite -mulRA -Rmult_plus_distr_l (mulRC (log (P i))) (big_distrl (log (P i)) _ _) /=.
  rewrite -big_split /= big_distrr/=.
  apply: eq_bigr=>i0 _.
  rewrite big_ord_recl (_ : _ /_ ord0 = i); last first.
    rewrite mxE; case: splitP => // j Hj; by rewrite mxE.
  rewrite -mulRA.
  case:(Rle0f P i)=>[ pi_pos| <-]; last by rewrite !mul0R.
  apply:Rmult_eq_compat_l.
  rewrite -Rmult_plus_distr_l.
  rewrite (@eq_bigr _ _ _ _ _ _ (fun x => P ((row_mx (\row_(_ < 1) i) i0) /_ (lift ord0 x))) (fun x => P i0 /_ x))=>[|i1 _]; last first.
    congr (P _).
    rewrite mxE.
    case: splitP => j; first by rewrite (ord1 j).
    by rewrite lift0 add1n; case=> /eqP /val_eqP ->.
  case: (Req_dec 0 (\rmul_(i'<n0) P i0 /_ i'))=>[<-|rmul_non0].
    by rewrite !mul0R.
  have rmul_pos: 0 < \rmul_(i1<n0) P i0 /_ i1.
    apply:Rlt_le_neq=>//.
    by apply:Rle_0_big_mult=>?; apply:Rle0f.
  by rewrite log_mult // !Rmult_plus_distr_l mulRA mulRA.
rewrite TupleDist.f1 -big_distrl /= mulR1 [in RHS]addRC.
apply:Rplus_eq_compat_l.
by rewrite -big_distrl/= pmf1 mul1R.
Qed.

End Entropy_lemma.

Section le_entroPN_logeEX.

Variable (A : finType) (P : dist A) (f : A -> seq bool).
Let X := mkRvar P (INR \o size \o f).
Definition Nmax := (\max_(a| a \in A) size (f a)).
Definition I_lmax := [finType of 'I_Nmax.+1].
Hypothesis f_uniq : uniquely_decodable f.

Lemma Xnon0 x : 0 <> X x.
Proof.
rewrite /X/=; case:(Req_dec 0 (INR (size (f x))))=>// H.
move:H; rewrite (_ : 0 = INR 0)//; move/INR_eq.
move/esym /size0nil=>fx_nil.
move:(@f_uniq [::] ([:: x])).
rewrite /extension /= fx_nil cat0s=>H.
have nil: [::] = [::] by[].
by move:(H (nil bool)).
Qed.

Lemma Xpos a: 0 < X a.
Proof.
move/nesym/INR_not_0:(@Xnon0 a)=>H.
apply: lt_0_INR; apply/ltP.
move:(leq0n (size (f a))); rewrite /X/= leq_eqVlt.
by move=>tmp; move:tmp H; case/orP=>// /eqP ->.
Qed.

Lemma Rle0Pr (i : I_lmax) : 0 <= Pr[X = (INR i)]. Proof. by apply:le_0_Pr. Qed.

Definition pmfN := mkPosFun Rle0Pr.

Lemma pmf1N : \rsum_(i | i \in I_lmax) pmfN i = 1.
Proof.
rewrite -(pmf1 P).
rewrite [in RHS](partition_big (inordf (size \o f)) (fun i => i \in I_lmax)) //=.
apply:eq_bigr=> i _; apply:eq_bigl=>i0.
rewrite /= inE (inordf_eq (fun x=> size (f x)) i0).
by apply/eqP/eqP=>[|-> //]; first move/INR_eq; apply:ord_inj.
Qed.

Definition PN := mkDist pmf1N.

Lemma EX_ord : `E X = \rsum_(i | i \in I_lmax) (INR i) * PN i.
Proof.
rewrite /E_leng_cw/Ex_alt (partition_big (inordf (size \o f)) (fun i => i \in I_lmax)) //=.
apply:eq_bigr=> i _.
rewrite /@pr /Pr mulRC big_distrl /=.
rewrite [in RHS]rsum_mulRC. 
apply: congr_big=>[//| x| x]; last by move:(inordf_eq (size \o f) x)=>/=->; move/eqP->.
rewrite inE; apply/eqP/eqP; first by move:(inordf_eq (size \o f) x)=>/=->; move->. 
by move/INR_eq; rewrite (inordf_eq (fun x=> size (f x))); move/val_inj.
Qed.

Lemma le_1_EX : 1 <= `E X.
Proof.
rewrite -(pmf1 P).
apply:Rle_big_P_f_g=>i _.
rewrite -{1}(mul1R ( P i)). 
apply:Rmult_le_compat_r; first by apply:Rle0f.
rewrite (_ : 1 = INR 1) //; move: (Xpos i).
by rewrite /= (_ : 0 = INR 0)//; move/INR_lt/lt_le_S/le_INR.
Qed.

Lemma EX_pos: 0 < `E X.
Proof. by apply:(Rlt_le_trans _ _ _ Rlt_0_1 le_1_EX). Qed. 

Lemma EX_non0: `E X  <> 0.
Proof. by apply:nesym; apply:Rlt_not_eq; apply: EX_pos. Qed.

Lemma entroPN_0 : `E X  = 1 -> `H PN = 0.
Proof.
move=>EX_1.
have eq_0_P: forall a, X a <> 1 -> 0 = P a.
  move:EX_1.
  rewrite /Ex_alt /= -{1}(pmf1 P)=>EX1 a Xnon1.
  have : forall i : A, i \in A -> P i <= INR (size (f i)) * P i.
    move=> i _; rewrite -{1}(mul1R ( P i)). 
    apply:Rmult_le_compat_r; first apply:Rle0f.
    rewrite (_ : 1 = INR 1) //; move: (Xpos i); rewrite /= (_ : 0 = INR 0) //.
    by move/INR_lt/lt_le_S/le_INR.
  move/Rle_big_eq=>H.
  case: (Req_dec (P a) 0)=>//.
  have: INR (size (f a)) * P a = P a by rewrite (H EX1 a).
  rewrite -{2}(mul1R (P a)).
  by move/Rmult_eq_reg_r=>tmp /tmp.
rewrite /entropy Ropp_eq_0_compat //.
rewrite {2}(Req_0_rmul (fun i => i \in I_lmax) (fun i => 0))//.
apply:eq_bigr=> i _; rewrite /= /@pr /Pr.
case (Req_dec (INR i) 1)=>[->| neq0].
  rewrite [X in _ * log X = _](_ : _ = 1); first by rewrite log_1 mulR0.
  rewrite -{2}(pmf1 P).
  rewrite [in RHS](bigID (fun a => a \in [set x | INR (size (f x)) == 1])) /=.
  rewrite [X in _ = _ + X](_ : _ = 0); first by rewrite addR0.
  apply: esym; apply: Req_0_rmul=>j.
  rewrite inE; move/eqP.
  by apply: (eq_0_P j).
rewrite [X in X * _ = _](_ : _ = 0); first by rewrite mul0R.
apply: esym; apply:Req_0_rmul=>j.
rewrite inE; move/eqP=>eq_Xj_i.
move:neq0; rewrite -eq_Xj_i.
by apply: (eq_0_P j).
Qed.

Lemma le_entroPN_logeEX': 
  `H PN <= `E X  * log (`E X ) - (`E X  - 1) * log((`E X ) -1).
Proof.
move: EX_pos EX_non0=>EX_pos EX_non0.
move/Rle_lt_or_eq_dec:le_1_EX=>[lt_EX_1| eq_E_0]; last first.
  rewrite -eq_E_0 /Rminus Rplus_opp_r mul0R Ropp_0 addR0 mul1R log_1.
  by move/esym/entroPN_0:eq_E_0->; apply:Rle_refl.
have lt_0_EX_1 : 0 < `E X  - 1.
  apply:(Rplus_lt_reg_r 1).
  by rewrite addR0 addRC -addRA Rplus_opp_l addR0.
pose alp := (`E X  - 1) / `E X .
have gt_alp_1 : alp < 1.
    apply:(Rmult_lt_reg_r (`E X )); first by apply:(Rlt_trans _ _ _ (Rlt_0_1)).
    rewrite /alp mul1R -mulRA -Rinv_l_sym // mulR1.
    by apply:Rgt_lt; apply:(tech_Rgt_minus _ _ (Rlt_0_1)).
have lt_0_alp : 0 < alp.
  rewrite /alp.
  by apply:Rlt_mult_inv_pos=>//.
have EX_pos' : 0 < 1 - (`E X  - 1) * / `E X .
  rewrite Rmult_plus_distr_r -Rinv_r_sym // Ropp_mult_distr_l_reverse mul1R /Rminus.
  rewrite Ropp_plus_distr addRA Ropp_involutive addRC Rplus_opp_r addR0.
  by apply: Rinv_0_lt_compat.
have max_pos: (0 < \max_(a in A) size (f a))%coq_nat.
  apply:ltP.
  move/card_gt0P:(dist_support_not_empty P)=>[a _].
  apply:(bigmax_sup a)=> //.
  by move:(Xpos a); rewrite /X /= (_ : 0 = INR 0)//;move/INR_lt/ltP.

rewrite [X in _ <= X](_ :_ = log ( alp / (1 - alp)) - (log alp) * `E X ); last first.
  rewrite /alp /Rdiv !log_mult  //; last first.
      by apply: Rinv_0_lt_compat. 
    by apply: Rinv_0_lt_compat.
  rewrite !log_Rinv //.
  rewrite Rmult_plus_distr_r /Rminus [in RHS]addRC (addRC _ (- log (`E X ) * `E X )).
  rewrite Ropp_plus_distr !Ropp_mult_distr_l_reverse Ropp_involutive mulRC -addRA. 
  apply: Rplus_eq_compat_l.
  rewrite Rmult_plus_distr_r mulRC Ropp_plus_distr -Ropp_mult_distr_l_reverse.
  apply: Rplus_eq_compat_l.
  rewrite Ropp_mult_distr_l_reverse Ropp_involutive mul1R -addRA -{1}(addR0 (log (`E X  + -1))).
  apply: Rplus_eq_compat_l.
  rewrite Rmult_plus_distr_r -Rinv_r_sym // Ropp_mult_distr_l_reverse mul1R.
  rewrite  Ropp_plus_distr Ropp_involutive (addRC 1 _) (addRC (-1) _).
  by rewrite -addRA Rplus_opp_l addR0 log_Rinv //Ropp_involutive Rplus_opp_l.

apply:(Rle_trans _  (log (alp * (1 - (alp ^ (\max_(a| a \in A) size (f a)))) / (1 - alp))
                     - log alp * `E X ) _); last first.
  apply:Rplus_le_compat_r.
  apply:log_increasing_le.
    apply:Rmult_lt_0_compat; last by  apply: Rinv_0_lt_compat ; apply:Rgt_lt; apply:Rgt_minus.
    apply:Rmult_lt_0_compat=> //. 
    apply:Rgt_lt; apply:Rgt_minus; apply:Rlt_gt.
    have : 0 <= alp < 1 by apply:conj=> //; first apply:Rlt_le.
     by move/(pow_lt_1_compat _ _ ):max_pos=>tmp; move/tmp/proj2.
  rewrite /Rdiv -mulRA.
  apply:Rmult_le_compat_l; first by apply:Rlt_le.
  rewrite -{2}(mul1R (/ (1 - alp))) ; apply:Rmult_le_compat_r.
    by apply:Rlt_le; apply:Rinv_0_lt_compat; apply:Rgt_lt; apply:Rgt_minus; apply:Rlt_gt.
  rewrite -{2}(addR0 1) /Rminus; apply:Rplus_le_compat; first by apply:Rle_refl.
  apply:Rge_le; apply:Ropp_0_le_ge_contravar.
  by apply:pow_le; apply:Rlt_le.

rewrite EX_ord -big_pow1; last by apply:Rlt_not_eq.
rewrite mulRC (big_morph _ (morph_mulRDl _) (mul0R _)).
apply:(Rplus_le_reg_r (\rsum_(i|i \in I_lmax) INR i * Pr[X = (INR i)] * log alp)).
rewrite -addRA Rplus_opp_l addR0.
rewrite  (@eq_bigr _ _ _ I_lmax _ _ _ (fun i => Pr[X = (INR i)] * log (alp ^ i))); last first.
  by move=> i _; rewrite log_pow // [in RHS]mulRC -mulRA (mulRC _ (log alp)) mulRA.
rewrite /entropy addRC; move:Ropp_minus_distr; rewrite/Rminus; move<-.
rewrite -(Ropp_involutive (log _)).
apply:Ropp_le_contravar; apply:Rge_le.
rewrite (big_morph _ morph_Ropp Ropp_0).
rewrite -big_split /=.
rewrite [X in X >= _](_ : _ =  \rsum_(i|i\in I_lmax)
      Pr[X = (INR i)] * (log Pr[X = (INR i)] - log (alp ^ i))); last first.
  by apply:eq_bigr=>i _; rewrite Rmult_plus_distr_l Ropp_mult_distr_r_reverse.
rewrite -Rminus_0_l -(mul1R (0 - _)).

have pmf1': \rsum_(i | i\in 'I_(\max_(a in A) size (f a))) Pr[X = (INR i.+1)] = 1.
  rewrite -pmf1N /=.
  rewrite (@big_ord_exclude0 _ (fun x => Pr[X = (INR x)])); first by[].
  apply:esym; apply:Req_0_rmul=> i.
  rewrite inE; move/eqP=> Xi_0.
  by move/Rlt_not_eq:(Xpos i); rewrite Xi_0.
rewrite -{2}log_1 -pmf1'.
have Rle0Pr (i : nat): 0 <= Pr[X = (INR i)] by apply:Rle_big_0_P_g=>? _;  apply:(Rle0f P).
have Rle0alpi (i : nat): 0 <= alp ^ i by apply:pow_le; apply:Rlt_le.
pose h := mkPosFun Rle0Pr.
pose g := mkPosFun Rle0alpi.
have dom_by_hg:  h << g.
  move=> i; move/pow0_inv=>alp0.
  by move:lt_0_alp; rewrite alp0;move/Rlt_not_eq.
rewrite /I_lmax/=/Nmax.
rewrite (@big_ord_exclude0 _ (fun i => Pr[X = (INR i)] * (log Pr[X = (INR i)] - log (alp ^ i)))); last first.
  rewrite /@pr/Pr.
  have ->: [set x | X x == INR 0] = set0; last by rewrite big_set0 mul0R.
  apply/setP=>i; rewrite inE/=in_set0.
  by apply/eqP; apply: nesym; apply: Rlt_not_eq; apply: Xpos.
by move: (log_sum_inequality_ord_add1' (\max_(a in A) size (f a)) dom_by_hg).
Qed.

Lemma le_entroPN_logeEX : `H PN <= log (`E X ) + log (exp 1).
Proof.
move: EX_pos EX_non0=>EX_pos EX_non0.
move/Rle_lt_or_eq_dec:le_1_EX=>[? | eq_EX_1]; last first.
  rewrite -eq_EX_1 log_1 add0R.
  by move/esym/entroPN_0:eq_EX_1->; apply:log_exp1_Rle_0.
have EX_1 : 0 < `E X  - 1.
  apply:(Rplus_lt_reg_r 1).
  by rewrite addR0 addRC -addRA Rplus_opp_l addR0.
have neq_EX1_0 :(`E X  + -1) <> 0.
  by apply:nesym; apply:Rlt_not_eq.
apply:(Rle_trans _ (`E X  * log (`E X ) - (`E X  - 1) * log((`E X ) -1)) _).
  by apply: le_entroPN_logeEX'.
rewrite -{1}(Rplus_minus 1 (`E X)).
rewrite Rmult_plus_distr_r mul1R /Rminus -addRA; apply:Rplus_le_compat_l.
rewrite -Ropp_mult_distr_r_reverse -Rmult_plus_distr_l -(mul1R (log (exp 1))).
rewrite -{3}(Rplus_minus (`E X ) 1) -Ropp_minus_distr'. 
apply:div_diff_ub=>//; first by apply:Rlt_le.
by apply:Rlt_le; apply:(Rlt_trans _ _ _ (Rlt_0_1)).
Qed.

End le_entroPN_logeEX.

Section v_scode_converse'_1tuple.

Variable A : finType.
Variable P : dist A.
Variable n : nat.
Variable f : A -> seq bool.
Local Notation "'I_lmax'" := (I_lmax f).
Let X := mkRvar P (INR \o size \o f).
Local Notation "'PN'" := (PN P f).
Hypothesis f_uniq: uniquely_decodable f.

Definition Pf (i : seq bool) := if [ pick x | f x == i ] is Some x then P x else 0.

Lemma Rle0Pf i : 0 <= Pf i.
Proof.
rewrite /Pf.
case:pickP=>[x _ | _ ]; first apply:Rle0f.
apply: Rle_refl.
Qed.

Lemma pmf1_Pf : \rsum_(m| m \in I_lmax) \rsum_(a in {: m.-tuple bool}) Pf a = 1.
Proof.
move:(uniq_dec_inj f_uniq)=> f_inj.
rewrite -(pmf1 P) (partition_big (inordf (size \o f)) (fun i => i \in I_lmax)) //=.
apply:eq_bigr=>i _.
rewrite (big_seq_tuple' i f_inj (dist_support_not_empty P)) /Pf=>[|x].
  apply:eq_big=>[?| i0]; first by rewrite (inordf_eq (fun x => size (f x))). 
  by case:(pickP ) =>[x /eqP /f_inj ->| /(_ i0)]; last rewrite eqxx. 
case:(pickP ) =>[? /eqP <-| _ ]; first by rewrite codom_f.
by case:ifP.
Qed.

Definition Pf' (m : I_lmax) (a : m.-tuple bool) :=  Pf a / (PN m).

Lemma Rle0Pf' (m : I_lmax) : PN m <> 0 -> forall (a : m.-tuple bool) , 0 <= Pf' a.
Proof.
move=> PNnon0 a; rewrite /Pf'.
apply:(Rmult_le_reg_r (PN m)).
  apply:Rlt_le_neq; first by apply:le_0_Pr.
  by apply:nesym.
rewrite mul0R /Rdiv -mulRA -Rinv_l_sym // mulR1.
rewrite /Pf; case:pickP=>[? _ | ? ]; first by apply:Rle0f.
by apply:Rle_refl.
Qed.

Lemma pmf1_Pf' m : PN m <> 0 -> \rsum_(a | a \in {: m.-tuple bool}) Pf' a = 1.
Proof.
move:(uniq_dec_inj f_uniq)=>f_inj.
move=>PNnon0.
rewrite -big_distrl /=.
apply:(Rmult_eq_reg_r (PN m))=>//.
rewrite -mulRA -Rinv_l_sym // mul1R mulR1 /=.
rewrite /@pr /Pr (eq_bigr (fun x => Pf (f x)))=>[|a ain]; last first.
  rewrite /Pf.
  case:pickP; first by move=>x /eqP/ f_inj ->.
  by move/(_ a); rewrite eqxx.
rewrite (eq_bigl (fun x =>  size (f x) == m) _)=>[|a]; last first.
rewrite inE /X/=.
apply/eqP/eqP=>[/INR_eq | ->] //.
rewrite (big_seq_tuple' m f_inj (dist_support_not_empty P)) /Pf=>[//|i0].
case:(pickP ) => // ?; first by move/eqP <-; rewrite codom_f.
by case:ifP.
Qed.

Lemma disjoints_set1 h: \rsum_(a | a \in [set : I_lmax]) h a = 
 \rsum_(a | a \in [set x | PN x == 0]) h a + \rsum_(a | a \in [set x | PN x != 0]) h a.
Proof.
rewrite (rsum_union [set x : I_lmax | PN x != 0] [set x : I_lmax | PN x == 0]).
    by rewrite addRC.
  rewrite disjoints_subset.
  rewrite (_ : ~: [set x | PN x != 0] = [set x | PN x == 0])//.
  apply/setP=>i.
  rewrite !inE.
  by case:(PN i == 0); rewrite -negb_involutive_reverse.
by rewrite setUC; apply/setP=> ?; rewrite !inE orbN. 
Qed.

Lemma rewrite_HP_with_Pf : `H P = 
 - \rsum_(m| m \in I_lmax) \rsum_(a in {: m.-tuple bool}) Pf a * log (Pf a).
Proof.
move:(uniq_dec_inj f_uniq)=> f_inj.
apply:Ropp_eq_compat.
rewrite [in LHS](partition_big (inordf (size \o f)) (fun i => i \in I_lmax)) //=.
apply:eq_bigr=>i _.
rewrite (eq_bigr (fun i0 => Pf (f i0) * log (Pf (f i0))))=>[|a]; last first.
  rewrite /Pf.
  case:(pickP _) => [x0 /eqP /f_inj->|] //. 
  move/(_ a); by rewrite eqxx.
rewrite (eq_bigl (fun x=> size (f x) == i) _) =>[|x]; last first.
  apply/eqP/eqP; first by move<-; rewrite (inordf_eq (fun x => size (f x))).
  rewrite (inordf_eq (fun x => size (f x))). 
  by apply/ord_inj.
rewrite (@big_seq_tuple' _ i _ f_inj (fun a => Pf a * log (Pf a)) (dist_support_not_empty P))//.
rewrite /Pf; move=>i0.
case:(pickP ) => // x; first by move/eqP <-; rewrite codom_f.
by case:ifP; rewrite mul0R.
Qed.

Lemma rewrite_HP_with_PN : `H P = - \rsum_(m| m \in [set x | PN x != 0]) PN m * 
                           (\rsum_(a in {: m.-tuple bool}) Pf' a * (log (Pf' a) + log (PN m))).
Proof.
rewrite rewrite_HP_with_Pf.
apply:Ropp_eq_compat.
rewrite (eq_bigl (fun m => m \in [set : I_lmax]) _)=>[|?]; last by rewrite /= in_setT.
rewrite disjoints_set1.
rewrite [Y in Y + _ = _](_ : _ = 0); last first.
  apply:esym; apply: Req_0_rmul=>i.
  rewrite inE /@pr /Pr/= =>/eqP/Rle_big_eq_0=>H.
  have {H}H: forall j : A, j \in [set x | INR (size (f x)) == INR i] -> P j = 0.
    by apply:H=> ? ?; apply:Rle0f.
  apply:Req_0_rmul=>i0 i_in.
  rewrite /Pf.
  case:pickP=>[x /eqP fx_j|?]; last by rewrite mul0R.
  have ->: P x = 0; last by rewrite mul0R.
  apply:H.
  by rewrite inE fx_j size_tuple.
rewrite add0R.
apply:eq_bigr=>i. 
rewrite inE ;move/eqP=>Pr_non0.
rewrite big_distrr /=.
apply:eq_bigr=>i0 _. 
rewrite [in RHS]mulRC /Rdiv -mulRA -mulRA.
case: (Req_dec (Pf i0) 0)=>[->| /nesym Pfi0_non0]; first by rewrite !mul0R.
apply:Rmult_eq_compat_l.
rewrite mulRC -mulRA.
rewrite -Rinv_r_sym // mulR1 log_mult.
    rewrite log_Rinv; first by rewrite -addRA Rplus_opp_l addR0.
    apply:Rlt_le_neq; first by apply:le_0_Pr.
    by apply:nesym.
  apply:Rlt_le_neq=>//.
  rewrite /Pf; case:pickP=>[? _ | ? ]; first by apply:Rle0f.
  by apply:Rle_refl.
apply:Rinv_0_lt_compat.
apply:Rlt_le_neq; first by apply:le_0_Pr.
by apply:nesym.
Qed.

Lemma rewrite_HP_with_HPN : `H P =  \rsum_(m| m \in [set x : I_lmax | PN x != 0]) 
PN m * (- \rsum_(a in {: m.-tuple bool}) Pf' a * 
(log ((Pf' a)))) + `H PN.
Proof.
move:(uniq_dec_inj f_uniq)=>f_inj.
rewrite {2}/entropy (eq_bigl (fun m => m \in [set : I_lmax]) (fun x=> _ * log _))=>[|?]; last by rewrite /= in_setT.
rewrite disjoints_set1.
rewrite [Y in  _ = _ + - ( Y + _)](_ :_ = 0); last first.
  apply:esym; apply: Req_0_rmul=>i.
  rewrite inE /PN /==>/eqP->.
  by rewrite mul0R.
rewrite add0R rewrite_HP_with_PN !(big_morph _ morph_Ropp Ropp_0) -big_split/=.
apply:eq_bigr=>i.
rewrite inE =>/eqP=>Pr_non0.
rewrite Ropp_mult_distr_r_reverse -Ropp_plus_distr; apply:Ropp_eq_compat.
rewrite -Rmult_plus_distr_l; apply:Rmult_eq_compat_l.
rewrite -[Y in _ = _ + Y]mul1R -(pmf1_Pf' Pr_non0) big_distrl/= -big_split/=.  
by apply:eq_bigr=>? _; by rewrite Rmult_plus_distr_l.
Qed.

Lemma apply_max_HPN : `H P <= `E X  + `H PN.
Proof.
move:(uniq_dec_inj f_uniq)=>f_inj.
rewrite rewrite_HP_with_HPN addRC (addRC _ (`H _)). 
apply:Rplus_le_compat_l.
rewrite EX_ord.
rewrite (eq_bigl (fun m => m \in [set : I_lmax]) (fun x=> INR x * _ ))=>[|?]; last by rewrite /= in_setT.
rewrite disjoints_set1.
rewrite [Y in _ <= Y + _ ](_ :_ = 0). 
  rewrite add0R. 
  apply:Rle_big_P_f_g=>i.
  rewrite mulRC inE; move/eqP=>H.
  apply:Rmult_le_compat_r; first by apply:le_0_Pr.
  pose pmf_Pf' := mkPosFun (Rle0Pf' H).
  have pmf1'_Pf' : \rsum_(a in {: i.-tuple bool}) pmf_Pf' a = 1 by apply: (pmf1_Pf' H).
  pose distPf := mkDist pmf1'_Pf'.
  move:(entropy_max distPf).
  rewrite card_tuple/= card_bool -INR_pow_expn log_pow (_ : INR 2 = 2)//.
    by rewrite log_2 mulR1.
  by apply:Rlt_R0_R2.
apply:esym; apply: Req_0_rmul=>i.
rewrite inE /PN /==>/eqP->.
by rewrite mulR0.
Qed.

Lemma apply_le_HN_logE_loge: `H P <= `E X  + log ((exp 1) * (`E X )).
Proof. 
apply:(Rle_trans _ _ _ apply_max_HPN).
apply:Rplus_le_compat_l.
rewrite mulRC (log_mult (EX_pos P f_uniq) (exp_pos 1)).
by apply:(le_entroPN_logeEX _ f_uniq).
Qed.

End v_scode_converse'_1tuple.

Section v_scode_converse'_ntuple.

Variable A : finType.
Variable n:nat.
Variable f : encT A (seq bool) n.
Variable P : dist A.
Hypothesis f_uniq : uniquely_decodable f.

Lemma converse_case1 : E_leng_cw f P < (INR n) * (log (INR #|A|)) -> 
`H (P `^ n) <= E_leng_cw f P + log ((exp 1) * (INR n) * (log (INR #|A|))).
Proof.
move=>H.
apply:(Rle_trans _ _ _ (apply_le_HN_logE_loge (P `^ n) f_uniq)). 
apply:Rplus_le_compat_l.
apply:log_increasing_le.
  apply:(Rmult_lt_0_compat _ _ (exp_pos 1)).
  apply: (EX_pos (P `^ n) f_uniq).
rewrite -mulRA; apply:Rmult_le_compat_l; first by apply:Rlt_le; apply:exp_pos.
by apply:Rlt_le.
Qed.

Lemma converse_case2 :  (INR n) * (log (INR #|A|)) <= E_leng_cw f P -> 
 `H (P `^ n) <= E_leng_cw f P.
Proof.
move=> H.
rewrite entropy_TupleDist.
apply: (Rle_trans (INR n * `H P) (INR n * log (INR #|A|)) _); last by apply: H.
apply: Rmult_le_compat_l; last by apply: entropy_max.
by rewrite (_ : 0 = INR 0) //; apply:le_INR; apply/leP; apply:leq0n.
Qed.

End v_scode_converse'_ntuple.

Section Extend_encoder.

Variable A : finType.
Variable n m:nat.
Variable f : encT A (seq bool) n.
Variable P : dist A.
Hypothesis f_uniq : uniquely_decodable f.
Hypothesis m_non0 : 0 <> (INR m).
Let fm (x : 'rV['rV[A]_n]_m) := extension f (tuple_of_row x).

Lemma fm_uniq : uniquely_decodable fm.
Proof.
pose m' := m.-1.
have mpos: m = m'.+1.
  case/Rdichotomy:m_non0; first by rewrite (_ : 0 = INR 0)//; move/INR_lt/(S_pred _ 0).
  by rewrite (_ : 0 = INR 0)//; move/Rgt_lt/INR_lt/ltP.
have: @extension [finType of 'rV[A]_n] _ f \o (flatten \o map (fun x => @tval m _ (tuple_of_row x))) =1 
      @extension [finType of {: 'rV[ 'rV[A]_n ]_m} ] _ fm.
   by elim => //= ta sta; rewrite /extension /= map_cat flatten_cat => <-.
apply: eq_inj. 
apply: inj_comp => //.
rewrite mpos.
elim => /= [| ta1 sta1 IHsta1]; case => [| ta2 sta2] //=.
- move/(congr1 size); by rewrite /= size_cat size_tuple addSn.
- move/(congr1 size); by rewrite /= size_cat size_tuple addSn.
- move/eqP. 
  rewrite eqseq_cat; last by rewrite !size_tuple.
  case/andP => H1 /eqP /IHsta1 ->.
  congr (_ :: _).
  by apply/tuple_of_row_inj/eqP.
Qed.

Lemma ELC_TupleDist : E_leng_cw fm (P `^ n)  = (INR m) * E_leng_cw f P.
Proof.
rewrite /E_leng_cw /Ex_alt /=  /fm /TupleDist.f. 
pose X := mkRvar (P `^ n) (INR \o size \o f).
elim:m=>[| m']; first by rewrite rsum_0rV row_of_tupleK /= !mul0R.
elim:m'=>[_ |m'' _ IH].
  rewrite mul1R -/(Ex_alt X) -E_rvar2tuple1.
  apply:eq_bigr=>i _.
  rewrite /= /TupleDist.f big_ord_recl big_ord0 mulR1.
  apply:Rmult_eq_compat_r.
  rewrite (_ : tuple_of_row i = [tuple of [:: i /_ ord0]]); last first.
    apply eq_from_tnth => a; by rewrite {a}(ord1 a) tnth_tuple_of_row.
  by rewrite /extension /= cats0.
pose fm1 (x : 'rV['rV[A]_n]_(m''.+1)) := extension f (tuple_of_row x).
pose Xm1 := mkRvar ((P `^ n) `^ (m''.+1)) (INR \o size \o fm1).
pose fm2 (x : 'rV['rV[A]_n]_(m''.+2)) := extension f (tuple_of_row x).
pose Xm2 := mkRvar ((P `^ n) `^ (m''.+2)) (INR \o size \o fm2).
have X_Xm1_Xm2 : Xm2 \= X @+ Xm1.
  apply:conj=>[|x /=]; first by apply:joint_prod_n.
  rewrite-plus_INR plusE -size_cat.
  rewrite /fm2 /extension /fm1 /extension.
  congr (INR (size _)).
  rewrite {1}(_ : x = row_mx (\row_(i < 1) (x /_ ord0)) (rbehead x)); last first.
    apply/matrixP => a b; by rewrite {a}(ord1 a) row_mx_rbehead.
Local Open Scope ring_scope.
  rewrite (@tuple_of_row_row_mx _ _ _ (\row_(i < 1) (x /_ ord0)) (rbehead x)) /=.
  rewrite map_cat /= flatten_cat.
  congr (_ ++ _).
  rewrite (_ : tuple_of_row _ = [tuple of [:: x /_ ord0]]); last first.
    by apply eq_from_tnth => i; rewrite {i}(ord1 i) /= tnth_tuple_of_row mxE.
  by rewrite /= cats0.
rewrite -/(Ex_alt Xm2) (E_linear_2 X_Xm1_Xm2) -(mul1R (`E X)).
by rewrite /Ex_alt IH -Rmult_plus_distr_r addRC -addn1 S_INR.
Qed.

End Extend_encoder.

Section v_scode_converse'.

Variable A : finType.
Variable P : dist A.
Variable n : nat.
Variable f : encT A (seq bool) n.
Hypothesis f_uniq : uniquely_decodable f.

Let alp := exp 1 * log (INR #| 'rV[A]_n |).
Let m eps:= Zabs_nat (floor (exp (INR (maxn (Zabs_nat (ceil ((ln alp) + INR n * eps * ln 2))) 
                                  (maxn (Zabs_nat (ceil (4 /(INR n * eps * ln 2)))) 1))))).

Lemma mpos eps: 0 <> INR n -> 0 < INR (m eps).
Proof.
rewrite /m =>nnon0.
rewrite (_ : 0 = INR 0)//; apply: lt_INR. 
rewrite {1}(_ : 0%nat = Z.abs_nat 0)//; apply:Zabs_nat_lt; apply:conj=>//.
apply: lt_0_IZR.
apply: (Rlt_trans _ (exp (INR (maxn (Z.abs_nat (ceil (ln alp + INR n * eps * ln 2)))
                 (maxn (Z.abs_nat (ceil (4 / (INR n * eps * ln 2))))
                    1))) -1) _); last by apply: (floor_bottom _).
apply: (Rplus_lt_reg_r 1).
rewrite addR0 addRC /Rdiv -addRA Rplus_opp_l addR0 -{1}exp_0.
apply: exp_increasing.
rewrite (_ : 0 = INR 0)//; apply: lt_INR; apply: ltP.
apply: (@leq_trans ((maxn (Z.abs_nat (ceil (4 * / (INR n * eps * ln 2)))) 1))); last by apply: leq_maxr.
by apply: (@leq_trans 1); last by apply: leq_maxr.
Qed.

Lemma le_eps eps: 0 <> INR n -> 1 <= INR n * log (INR #|A|) -> 0 < eps ->
  log (INR (m eps) * alp) * / INR (m eps) * / INR n <= eps.
Proof.
move=> nnon0 eps_pos cardA_non1.
pose x := (INR (maxn (Z.abs_nat (ceil (ln alp + INR n * eps * ln 2)))
                     (maxn (Z.abs_nat (ceil (4 / (INR n * eps * ln 2)))) 1))).
pose Y := (eps * INR n * ln 2).
have npos: 0 < INR n.
  by case/Rdichotomy:nnon0=>//; rewrite (_ : 0 = INR 0)// => /INR_lt/ltP.
have xpos : 0 < x.
  rewrite (_ : 0 = INR 0)//; apply: lt_INR; apply/leP.
  apply: (@leq_trans ((maxn (Z.abs_nat (ceil (4 * / (INR n * eps * ln 2)))) 1))); last by apply: leq_maxr.
  by apply: (@leq_trans 1); last by apply: leq_maxr.
have mpos': (0 < floor (exp x))%Z.
  apply: lt_IZR. 
  apply: (Rlt_trans _ (exp x - 1) _); last by apply: floor_bottom.
  apply: (Rplus_lt_reg_r 1).
  rewrite addR0 addRC /Rminus -addRA Rplus_opp_l addR0 -exp_0.
  by apply: exp_increasing=>//.
have le_1_alp: 1 <= alp.
  rewrite /alp -(mulR1 1).
  apply: (Rmult_le_compat _ _ _ _ Rle_0_1 Rle_0_1).
  rewrite mulR1.
  apply: (Rle_trans _ 2); last by apply: two_e.
  by rewrite -{1}(addR0 1); apply: (Rplus_le_compat_l _ _ _ Rle_0_1).
  rewrite card_matrix -INR_pow_expn mul1n log_pow //.
  by rewrite (_ : 0 = INR 0)//; apply: lt_INR; apply/ltP; apply: dist_support_not_empty.
have alppos: 0 < alp.
  by apply: (Rlt_le_trans _ 1 _ Rlt_0_1).
have Ypos: 0 < Y.
  apply: Rmult_lt_0_compat; last by apply:ln_2_pos.
  by apply: Rmult_lt_0_compat=>//.
apply: (Rmult_le_reg_r (INR (m eps) * INR n)).
  apply: Rmult_lt_0_compat=>//; by apply: (mpos eps nnon0).
rewrite -mulRA (mulRC (/ INR n) _ ) -mulRA -mulRA -Rinv_r_sym; last by apply: nesym.
rewrite mulR1 -(Rinv_l_sym _ (nesym (Rlt_not_eq _ _ (mpos eps nnon0)))) mulR1.
apply: (Rle_trans _ ((x ^ 2 / 2 - 1) * eps * (INR n)) _); last first.
  rewrite -mulRA mulRC -mulRA; apply: Rmult_le_compat_l; first by apply: Rlt_le.
  rewrite mulRC; apply: Rmult_le_compat_r; first by apply: Rlt_le.
  apply: (Rle_trans _ (exp x - 1) _).
    apply: (Rplus_le_reg_r 1).
    rewrite -addRA Rplus_opp_l addR0 -addRA Rplus_opp_l addR0.
    by rewrite (_ : 2 = INR 2 `!)//; apply: (exp_lb 2); apply: pos_INR.
  rewrite INR_Zabs_nat; last first. 
    by apply: le_IZR; apply: Rlt_le; apply: IZR_lt.
  by apply: Rlt_le; apply: floor_bottom.
rewrite INR_Zabs_nat; last by apply: le_IZR; apply: Rlt_le; apply: IZR_lt.
rewrite log_mult//; last by rewrite (_ :0 = IZR 0)//; apply: IZR_lt.
apply: (Rmult_le_reg_r (ln 2) _ _ ln_2_pos).
rewrite Rmult_plus_distr_r /log/Rdiv -mulRA -(Rinv_l_sym _ (nesym (Rlt_not_eq _ _(ln_2_pos)))).
rewrite mulR1 -(mulRA _ (/ ln 2) _) -(Rinv_l_sym _ (nesym (Rlt_not_eq _ _ (ln_2_pos)))) mulR1.
apply: (Rle_trans _ (x + ln alp) _).
  apply: Rplus_le_compat_r.
  rewrite -(ln_exp x).
  apply: ln_increasing_le; last by apply: floor_upper.
  apply: (Rlt_trans _ (exp x - 1) _); last by apply: floor_bottom.
  apply: (Rplus_lt_reg_r 1).
  rewrite addR0 addRC -addRA Rplus_opp_l addR0 -exp_0.
  apply: exp_increasing=>//.
apply: (Rle_trans _ (2 * x - (eps * INR n * ln 2))).
  rewrite double /Rminus -addRA.
  apply: Rplus_le_compat_l.
  apply: (Rplus_le_reg_r (eps * INR n * ln 2)).
  rewrite -addRA Rplus_opp_l addR0 mulRC mulRA mulRC (mulRC _ eps) mulRA.
  apply: (Rle_trans _ (IZR (ceil (ln alp +  INR n * eps * ln 2)))); first by apply: ceil_bottom.
  rewrite -INR_Zabs_nat; first by apply: le_INR; apply/leP; apply: leq_maxl.
  apply: le_IZR.
  apply: (Rle_trans _ (ln alp + Y)); last by rewrite /Y (mulRC eps); apply: ceil_bottom.
  apply: Rplus_le_le_0_compat; last by apply: Rlt_le.
  by rewrite -(ln_exp 0) exp_0; apply: ln_increasing_le=> //; apply: Rlt_0_1.
rewrite -(mulRA _ eps) -(mulRA _ (eps * INR n)).
rewrite (Rmult_plus_distr_r (x ^ 2 * / 2) _ (eps * INR n * ln 2)).
rewrite Ropp_mult_distr_l_reverse mul1R /Rminus.
apply: Rplus_le_compat_r.
apply: (Rmult_le_reg_r (/ Y * 2 * / x)).
  apply: Rlt_mult_inv_pos=>//.
  apply: Rmult_lt_0_compat; last by apply: Rlt_0_2.
  by apply: Rinv_0_lt_compat.
rewrite mulRC -mulRA (mulRC (/ x)) -mulRA -mulRA -(Rinv_r_sym _ (nesym (Rlt_not_eq _ _ xpos))).
rewrite mulR1 mulRC mulRA mulRA (mulRC _ (/x)) /=mulR1 mulRA (mulRC _ 2).
rewrite -(mulRA _ Y) -(Rinv_r_sym _ (nesym (Rlt_not_eq _ _ Ypos))).
rewrite mulR1 (mulRC 2) !mulRA -(mulRA _ _ 2) -!Rinv_l_sym; last first.
  by apply: (nesym (Rlt_not_eq _ _ xpos)).
  by apply: (nesym (Rlt_not_eq _ _ Rlt_0_2)).
rewrite mulR1 mul1R.
apply: (Rle_trans _ (INR (maxn (Z.abs_nat (ceil (4 * / (INR n * eps * ln 2)))) 1))); last by apply: le_INR; apply: leP; apply: leq_maxr.
apply: (Rle_trans _ (INR (Z.abs_nat (ceil (4 * / (INR n * eps * ln 2)))))); last by apply: le_INR; apply: leP; apply: leq_maxl.
rewrite INR_Zabs_nat.
  apply: (Rle_trans _ ( (4 * / (INR n * eps * ln 2)))); last by apply: ceil_bottom.
  rewrite (mulRC (INR n)); by apply: Rle_refl.
apply:le_IZR.
apply: (Rle_trans _ ( (4 * / (INR n * eps * ln 2)))); last by apply: ceil_bottom.
apply: Rle_mult_inv_pos; first by apply: (Rlt_le _ _ (Rmult_lt_0_compat _ _ Rlt_0_2 Rlt_0_2)).
by rewrite (mulRC (INR n)).
Qed.

Theorem v_scode_converse' :
  E_leng_cw f P >= (INR n) * `H P.
Proof.
case: (Req_dec 0 (INR n))=>[<-|nnon0].
  rewrite mul0R.
  apply:Rle_ge; apply: Rlt_le.
  apply: (EX_pos (P `^ n) f_uniq).
apply:Rle_ge.
have npos: 0 < INR n.
  by case/Rdichotomy:nnon0=>//; rewrite (_ : 0 = INR 0)// => /INR_lt/ltP.
apply: (Rmult_le_reg_r (/ INR n)).
  by apply: Rinv_0_lt_compat.
rewrite (mulRC (INR n)) -mulRA -Rinv_r_sym; last by apply: nesym.
rewrite mulR1.
apply:le_epsilon=>eps epspos.
pose fm (x : 'rV['rV[A]_n]_((m eps))) := extension f (tuple_of_row x).
case:(Rle_or_lt  ((INR (m eps)) * (log (INR #| 'rV[A]_n |)))(E_leng_cw fm (P `^ n))).
  move/(@converse_case2 _ _ fm (P `^ n)).
  rewrite !entropy_TupleDist ELC_TupleDist.
  move/(Rmult_le_reg_l _ _ _ (mpos eps nnon0))=>H.
  apply: (Rle_trans _ (E_leng_cw  f P / (INR n)))=>//.
    apply: (Rmult_le_reg_r (INR n)).
      by case/Rdichotomy:nnon0=>//; rewrite (_ : 0 = INR 0)// => /INR_lt/ltP.
    rewrite mulRC -mulRA -Rinv_l_sym; last by apply: nesym.
    by rewrite mulR1.
  by rewrite -{1}(addR0 (E_leng_cw f P / (INR n))); apply:  Rplus_le_compat_l; apply: Rlt_le.
have mnon0: INR (m eps) <> 0.
  by apply: (nesym (Rlt_not_eq _ _ (mpos eps nnon0))).
move=>case2.
move:(@converse_case1 _ _ _ (P `^ n) (fm_uniq f_uniq (Rlt_not_eq _ _ (mpos eps nnon0))) case2).
rewrite !entropy_TupleDist ELC_TupleDist /Ex_alt /= -!mulRA mulRA.
move/(Rmult_le_compat_r _ _ _  (Rlt_le _ _ (Rinv_0_lt_compat _ (mpos eps nnon0)))).
rewrite -mulRA -mulRA mulRC mulRA -mulRA -Rinv_l_sym//.
rewrite mulR1 Rmult_plus_distr_r (mulRC (INR (m eps))) -mulRA -Rinv_r_sym// mulR1.
move/(Rmult_le_compat_r _ _ _  (Rlt_le _ _ (Rinv_0_lt_compat _ npos))).
rewrite (mulRC (INR n)) -mulRA -Rinv_r_sym; last by apply: nesym.
rewrite mulR1 Rmult_plus_distr_r=>H.
apply: (Rle_trans _ _ _ H).
apply: Rplus_le_compat_l. 
rewrite mulRA (mulRC (exp 1)) -(mulRA (INR (m eps))).
apply le_eps => //.
move:case2.
rewrite ELC_TupleDist mulRC (mulRC (INR (m eps))) card_matrix mul1n -INR_pow_expn log_pow; last first.
  by rewrite (_ : 0 = INR 0)//; apply: lt_INR; apply/ltP; apply: dist_support_not_empty.
move/(Rmult_lt_reg_r _ _ _ (mpos eps nnon0))=>H'.
apply: (Rle_trans _ (E_leng_cw f P)).
by apply: (le_1_EX (P `^ n) f_uniq).
by apply: Rlt_le.
Qed.

End v_scode_converse'.

Section v_scode_converse.

Variable A : finType.
Variable P : dist A.
Variable n : nat.
Variable f : encT A (seq bool) n.
Hypothesis f_uniq : uniquely_decodable f.

Theorem v_scode_converse :
  E_leng_cw f P >= INR n * `H P.
Proof.
  by apply:v_scode_converse'=>//.
Qed.

End v_scode_converse.
