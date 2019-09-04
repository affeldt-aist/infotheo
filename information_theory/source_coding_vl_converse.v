From mathcomp Require Import all_ssreflect ssralg fingroup finalg matrix.
Require Import Reals.
From infotheo Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext.
From infotheo Require Import Rbigop proba entropy divergence log_sum source_code.

(* documentation
   Ryosuke Obi.
   In MI Lecture Note Workshop on Theorem proving and provers for reliable
   theory and implementations (TPP2014),
   Kyushu University, December 3--5, 2014, volume 61, pages 76--78, Dec 2014
*)

(* quickly patched to compile with infotheo [2019-08-19] *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope tuple_ext_scope.
Local Open Scope proba_scope.
Local Open Scope reals_ext_scope.
Local Open Scope entropy_scope.
Local Open Scope divergence_scope.
Local Open Scope R_scope.

Section log_sum_ord.
Variable A : finType.
Variable n: nat.
Variable f g: nat ->R^+.
Hypothesis f_dom_by_g : f << g.

Lemma log_sum_inequality_ord_add1:
  (\sum_(i in 'I_n) f i.+1) *
  (log ((\sum_(i in 'I_n) f i.+1) / (\sum_(i in 'I_n) g i.+1))) <=
  \sum_(i in 'I_n) f i.+1 * (log (f i.+1 / g i.+1)).
Proof.
have Rle0f_1: forall (x : 'I_n), 0 <= f x.+1 by move=> ?; apply pos_f_ge0.
have Rle0g_1: forall (x : 'I_n), 0 <= g x.+1 by move=> ?; apply pos_f_ge0.
have newRle0f_1: [forall x : 'I_n, 0 <b= [ffun x : 'I_n => f x.+1] x].
  by apply/forallP_leRP => ?; rewrite ffunE.
have newRle0g_1: [forall x : 'I_n, 0 <b= [ffun x : 'I_n => g x.+1] x].
  by apply/forallP_leRP => ?; rewrite ffunE.
have f_dom_by_g1 : (mkPosFfun newRle0f_1) << (mkPosFfun newRle0g_1).
  apply/dominatesP => a; move/dominatesP : f_dom_by_g.
  rewrite /= !ffunE; exact.
have H:forall h,
  \sum_(a | a \in [set: 'I_n]) h a.+1 = \sum_(a | a \in 'I_n) h a.+1.
  by move=>?; apply:eq_bigl=>?; rewrite in_setT.
rewrite -!H -(H (fun i => f i * log (f i / g i))).
move: (log_sum [set: 'I_n] (mkPosFfun newRle0f_1) (mkPosFfun newRle0g_1) f_dom_by_g1).
rewrite /=.
evar (h : 'I_n -> R); rewrite (eq_bigr h); last first.
  move=> a aC; rewrite ffunE /h; reflexivity.
rewrite {}/h.
evar (h : 'I_n -> R); rewrite [in X in _ * log (_ / X) <= _ -> _](eq_bigr h); last first.
  move=> a aC; rewrite ffunE /h; reflexivity.
rewrite {}/h.
evar (h : 'I_n -> R); rewrite [in X in _ <= X  -> _](eq_bigr h); last first.
  move=> a aC; rewrite ffunE /h; reflexivity.
rewrite {}/h.
move/leR_trans; apply.
apply Req_le.
apply eq_bigr => i _.
by rewrite ffunE.
Qed.

Lemma log_sum_inequality_ord_add1':
  (\sum_(i in 'I_n) f i.+1) * (log (\sum_(i in 'I_n) f i.+1)
                                - log (\sum_(i in 'I_n) g i.+1)) <=
    \sum_(i in 'I_n) f i.+1 * (log (f i.+1) - log (g i.+1)).
Proof.
rewrite [X in _ <= X]
        (_ : _ = \sum_(i in 'I_n) f i.+1 * log (f i.+1 / (g i.+1))).
  rewrite [X in X <= _](_ : _ =  (\sum_(i in 'I_n) f i.+1) *
   (log ((\sum_(i in 'I_n)f i.+1) / (\sum_(i in 'I_n) g i.+1)))).
      by apply: log_sum_inequality_ord_add1.
  have : 0 <= \sum_(i in 'I_n) f i.+1.
    apply rsumr_ge0 => ? _; exact: pos_f_ge0.
  case=>[Hf | <-]; last by rewrite !mul0R.
  have : 0 <= \sum_(i in 'I_n) g i.+1.
    apply rsumr_ge0 => ? _; exact: pos_f_ge0.
  case=>[Hg |].
    rewrite /log LogM // ?LogV //; last exact: Rinv_0_lt_compat.
  have Rle0g_add1: forall (x : ordinal_finType n), 0 <= g x.+1.
    by move=> ?; apply pos_f_ge0.
  move=> H.
  have eq_g_0 : forall i : 'I_n, 0 = g i.+1.
    move/esym/prsumr_eq0P : H => H i; by rewrite H.
  have : 0 = \sum_(i in 'I_n) f i.+1.
    apply/esym/prsumr_eq0P => i _; [exact: pos_f_ge0|].
    move/dominatesP : f_dom_by_g; apply; by rewrite -eq_g_0.
  by move=>tmp; move:Hf; rewrite -tmp; move/Rlt_not_eq.
apply: eq_bigr=>i _.
case: (pos_f_ge0 f i.+1)=>[fpos|<-]; last by rewrite !mul0R.
  case: (pos_f_ge0 g i.+1); last first.
    move/esym => g0; move/dominatesP : f_dom_by_g => /(_ _ g0) ->; by rewrite !mul0R.
  move=>gpos; rewrite /log LogM // ?LogV //; exact: Rinv_0_lt_compat.
Qed.

End log_sum_ord.


Section Ordinal.
Variable T : finType.
Variable f : T -> nat.

Definition inordf t := inord (f t) : 'I_(\max_t f t).+1.

Lemma inordfE:  (fun t : T => nat_of_ord (inordf t)) =1 f .
Proof.
move=>t.
apply: inordK; by apply: leq_bigmax.
Qed.

End Ordinal.
Prenex Implicits inordf.

Section Bigop_Lemma.
Variable A : finType.

Lemma rsum_mulRC (h : A -> R) g P:
  \sum_(i| P i) h i * g i = \sum_(i| P i) g i * h i.
Proof.
by apply: eq_bigr=>? _; rewrite mulRC.
Qed.

Variable n : nat.
Variable f : A -> seq bool.
Hypothesis f_inj : injective f.

Lemma big_seq_tuple'' (F : seq bool -> R): (0 < #|A|)%nat ->
  \sum_(a | size (f a) == n) F (f a) =
  \big[Rplus/0]_(i : n.-tuple bool | tval i \in codom f) F i.
Proof.
move Hpick : [pick x | x \in [set: A] ] => p Anon0.
move: Hpick; case: (pickP _)=>[defaultA _ _ | abs]; last first.
  move:Anon0.
  rewrite -cardsT card_gt0; case/set0Pn=> ?.
  by rewrite abs.
 pose dummy := [tuple of nseq n false].
 pose h a : n.-tuple bool := insubd dummy (f a).
 pose h' (i : n.-tuple bool) := odflt defaultA [pick a | f a == i].
 have H a : odflt defaultA [pick a0 | f a0 == f a ] = a.
 - case: pickP => /=; last by move/(_ a); rewrite eqxx.
   by move => a0 /eqP /f_inj ->.
 - rewrite (reindex_onto h h'); last first.
   + move=>a /codomP [i a_fi].
     rewrite /h' a_fi H /h /insubd insubT; first by rewrite -a_fi size_tuple.
     by move=>?; apply/val_inj=>//.
   + apply: eq_big =>[i | i sizefi]; last by rewrite /h /insubd insubT//.
     apply/idP/andP=>[sizefi |[/codomP [a hi_fa]] /eqP].
       by rewrite /h /h' insubdK// H; apply:(conj (codom_f _ _))=>//.
     by rewrite /h' hi_fa H=><-; rewrite -hi_fa size_tuple.
Qed.

Lemma big_seq_tuple (F : seq bool -> R): (0 < #|A|)%nat ->
  \sum_(a | size (f a) == n) F (f a) =
  \big[Rplus/0]_(i : n.-tuple bool | tval i \in codom f) F i.
Proof.
move Hpick : [pick x | x \in [set: A] ] => p Anon0.
move: Hpick; case: (pickP _)=>[defaultA _ _ | abs]; last first.
  suff : False by [].
  move:Anon0.
  rewrite -cardsT card_gt0; case/set0Pn => ?.
  by rewrite abs.
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
  \sum_(i in {: n.-tuple bool}) F i = \sum_(a| size (f a) == n) F (f a).
Proof.
move=>Anon0 Fi0.
rewrite big_seq_tuple //.
rewrite (eq_bigr (fun a => if (tval a \in codom f) then F a else 0))=>[|i _].
  by rewrite -big_mkcondr/=.
by case:ifP=>//; rewrite Fi0; move->.
Qed.

Lemma big_ord_exclude0 (h:nat -> R): h 0%nat = 0 ->
    \sum_(i in 'I_n.+1) h i = \sum_(i in 'I_n) h i.+1.
Proof.
move=>H.
rewrite -(big_mkord xpredT _) -(big_mkord xpredT (fun i => h i.+1)).
by rewrite big_ltn// H add0R big_add1.
Qed.

Lemma big_pow1 x : x <> 1 ->
  \sum_(i in 'I_n) x ^ i.+1 = x * (1 - (x ^ n)) / (1 - x).
Proof.
move=>neq_x_1.
apply: (Rplus_eq_reg_l 1).
rewrite {1}[in RHS](Rinv_r_sym (1 - x) (Rminus_eq_contra _ _ (nesym neq_x_1))).
rewrite Rmult_plus_distr_l mulR1 -Rmult_plus_distr_r addRA [in RHS]addRC -addRA.
rewrite Rplus_opp_l addR0 (addRC _ 1) Ropp_mult_distr_r_reverse.
rewrite -(big_mkord xpredT (fun i => x ^ i.+1)) (_ : n = n.+1.-1) //.
rewrite -(big_add1 _ _ _ _  xpredT)-{1}(pow_O x) -big_ltn//.
by rewrite big_mkord -sum_f_R0_rsum tech3.
Qed.

Lemma log_pow r: 0 < r -> log (r ^ n) = (INR n) * log r.
Proof.
elim:n=> [|n' IH lt_0_r]; first by rewrite /log Log_1 mul0R.
rewrite /log LogM//;last exact: pow_lt.
rewrite /log in IH; by rewrite IH // -addn1 addRC plus_INR Rmult_plus_distr_r mul1R.
Qed.

End Bigop_Lemma.

Local Open Scope vec_ext_scope.

Section Entropy_lemma.

Variables (A : finType) (P : fdist A) (n : nat).

Lemma entropy_TupleFDist : `H (P `^ n) = (INR n) * `H P.
Proof.
elim:n=>[|n0 IH].
  rewrite /entropy /= mul0R (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 ?oppR0 // => i _.
  by rewrite TupleFDist.zero /log Log_1 mulR0.
rewrite S_INR Rmult_plus_distr_r mul1R -IH.
rewrite /entropy -(big_rV_cons_behead _ xpredT xpredT) /=.
rewrite -Ropp_plus_distr; apply:Ropp_eq_compat.
rewrite [X in X = _](_ :_ = \sum_(i | i \in A) P i * log (P i) *
          (\sum_(j in 'rV[A]_n0) (\prod_(i0 < n0) P j ``_ i0)) +
           \sum_(i | i \in A) P i * \sum_(j in 'rV[A]_n0)
          (\prod_(i0 < n0) P j ``_ i0) * log (\prod_(i0 < n0) P j ``_ i0)); last first.
  rewrite -big_split /=.
  apply:eq_bigr=> i _.
  rewrite -mulRA -Rmult_plus_distr_l (mulRC (log (P i))) (big_distrl (log (P i)) _ _) /=.
  rewrite -big_split /= big_distrr/=.
  apply: eq_bigr=>i0 _.
  rewrite TupleFDist.dE.
  rewrite big_ord_recl (_ : _ ``_ ord0 = i); last first.
    rewrite mxE; case: splitP => // j Hj; by rewrite mxE.
  rewrite -mulRA.
  case: (FDist.ge0 P i) => [ pi_pos| <-]; last by rewrite !mul0R.
  apply:Rmult_eq_compat_l.
  rewrite -Rmult_plus_distr_l.
  rewrite (@eq_bigr _ _ _ _ _ _ (fun x => P ((row_mx (\row_(_ < 1) i) i0) ``_ (lift ord0 x))) (fun x => P i0 ``_ x))=>[|i1 _]; last first.
    congr (P _).
    rewrite mxE.
    case: splitP => j; first by rewrite (ord1 j).
    by rewrite lift0 add1n; case=> /eqP /val_eqP ->.
  case: (Req_dec 0 (\prod_(i'<n0) P i0 ``_ i'))=>[<-|rmul_non0].
    by rewrite !mul0R.
  have rmul_pos: 0 < \prod_(i1<n0) P i0 ``_ i1.
    move/eqP in rmul_non0.
    apply/ltRP; rewrite lt0R eq_sym rmul_non0; apply/leRP/rprodr_ge0 => ?; exact: pos_ff_ge0.
  by rewrite /log LogM // !Rmult_plus_distr_l mulRA mulRA.
rewrite (_ : \sum_(j in 'rV_n0) _ = 1); last first.
  by rewrite -(FDist.f1 (P `^ n0)); apply eq_bigr => i _; rewrite TupleFDist.dE.
rewrite -big_distrl /= mulR1 [in RHS]addRC.
congr (_ + _).
rewrite -big_distrl /= FDist.f1 mul1R; apply eq_bigr => i _.
by rewrite TupleFDist.dE.
Qed.

End Entropy_lemma.

Section le_entroPN_logeEX.

Variable (A : finType) (P : fdist A) (f : A -> seq bool).
Let X : {RV P -> R} := (INR \o size \o f).
Definition Nmax := (\max_(a in A) size (f a)).
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

Lemma Rle0Pr : forall i : 'I_Nmax.+1, 0 <= [ffun x : 'I__ => @Pr _ P (X @^-1 (INR x))] i.
Proof.
move => a.
by rewrite ffunE; apply: Pr_ge0.
Qed.

Lemma pmf1N : \sum_(i in 'I_Nmax.+1) [ffun x : 'I__ => @Pr _ P (X @^-1 (INR x))] i = 1.
Proof.
rewrite -(FDist.f1 P).
rewrite [in RHS](partition_big (inordf (size \o f)) (fun i => i \in 'I_Nmax.+1)) //=.
apply:eq_bigr=> i _; rewrite ffunE; apply:eq_bigl=>i0.
rewrite /= inE.
apply/eqP/eqP=>[/INR_eq H|<-]; last by rewrite inordfE.
apply: ord_inj.
by rewrite -H inordfE.
Qed.

Definition PN := FDist.make Rle0Pr pmf1N.

Lemma EX_ord : `E X = \sum_(i in 'I_Nmax.+1) (INR i) * PN i.
Proof.
rewrite /Ex (partition_big (inordf (size \o f)) (fun i => i \in 'I_Nmax.+1)) //=.
apply:eq_bigr=> i _.
rewrite /pr_eq /Pr ffunE mulRC big_distrl /=.
rewrite [in RHS]rsum_mulRC.
apply: congr_big=>[//| x| x]; last by move/eqP<-; rewrite inordfE.
rewrite inE; apply/eqP/eqP; first by move<-; rewrite inordfE.
by move/INR_eq=>H; apply: ord_inj; rewrite -H inordfE.
Qed.

Lemma le_1_EX : 1 <= `E X.
Proof.
rewrite -(FDist.f1 P); apply: ler_rsum => i _.
rewrite -{1}(mul1R ( P i)).
apply leR_wpmul2r; first by apply pos_ff_ge0.
rewrite (_ : 1 = INR 1) //; move: (Xpos i).
by rewrite /= (_ : 0 = INR 0) //; move/INR_lt/lt_le_S/le_INR.
Qed.

Lemma EX_pos : 0 < `E X.
Proof. exact: (Rlt_le_trans _ _ _ Rlt_0_1 le_1_EX). Qed.

Lemma EX_non0 : `E X <> 0.
Proof. by apply:nesym; apply:Rlt_not_eq; apply: EX_pos. Qed.

Lemma entroPN_0 : `E X  = 1 -> `H PN = 0.
Proof.
move=>EX_1.
have eq_0_P: forall a, X a <> 1 -> 0 = P a.
  move: EX_1.
  rewrite -{1}(FDist.f1 P)=>EX1 a Xnon1.
  have : forall i : A, i \in A -> P i <= INR (size (f i)) * P i.
    move=> i _; rewrite -{1}(mul1R ( P i)).
    apply:Rmult_le_compat_r; first apply pos_ff_ge0.
    rewrite (_ : 1 = INR 1) //; move: (Xpos i); rewrite /= (_ : 0 = INR 0) //.
    by move/INR_lt/lt_le_S/le_INR.
  move/Rle_big_eq=>H.
  case: (Req_dec (P a) 0)=>//.
  have: INR (size (f a)) * P a = P a by rewrite (H EX1 a).
  rewrite -{2}(mul1R (P a)).
  by move/Rmult_eq_reg_r=>tmp /tmp.
rewrite /entropy Ropp_eq_0_compat //.
rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 //= => i _.
rewrite /= /pr_eq /Pr ffunE.
case (Req_dec (INR i) 1)=>[->| neq0].
  rewrite [X in _ * log X = _](_ : _ = 1); first by rewrite /log Log_1 mulR0.
  rewrite -{2}(FDist.f1 P).
  rewrite [in RHS](bigID (fun a => a \in [set x | INR (size (f x)) == 1])) /=.
  rewrite [X in _ = _ + X](_ : _ = 0); first by rewrite addR0.
  rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 // => j.
  by rewrite inE; move/eqP/eq_0_P.
rewrite [X in X * _ = _](_ : _ = 0); first by rewrite mul0R.
  rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 // => j.
rewrite inE; move/eqP=>eq_Xj_i.
by move:neq0; rewrite -eq_Xj_i => /eq_0_P.
Qed.

Lemma le_entroPN_logeEX':
  `H PN <= `E X  * log (`E X) - (`E X  - 1) * log((`E X ) - 1).
Proof.
move: EX_pos EX_non0=>EX_pos EX_non0.
move/Rle_lt_or_eq_dec:le_1_EX=>[lt_EX_1| eq_E_0]; last first.
  rewrite -eq_E_0 /Rminus Rplus_opp_r mul0R Ropp_0 addR0 mul1R /log Log_1.
  by move/esym/entroPN_0:eq_E_0->; apply:Rle_refl.
have lt_0_EX_1 : 0 < `E X  - 1.
  apply:(Rplus_lt_reg_r 1).
  by rewrite  addRC -addRA Rplus_opp_l 2!addR0.
pose alp := (`E X  - 1) / `E X .
have gt_alp_1 : alp < 1.
    apply:(Rmult_lt_reg_r (@Ex _ P X )); first exact: (ltR_trans Rlt_0_1).
    rewrite /alp mul1R -mulRA -Rinv_l_sym // mulR1.
    by apply:Rgt_lt; apply:(tech_Rgt_minus _ _ (Rlt_0_1)).
have lt_0_alp : 0 < alp.
  rewrite /alp.
  by apply:Rlt_mult_inv_pos=>//.
have EX_pos' : 0 < 1 - (`E X  - 1) * / `E X .
  rewrite Rmult_plus_distr_r -Rinv_r_sym // Ropp_mult_distr_l_reverse mul1R.
  rewrite /Rminus Ropp_plus_distr addRA Ropp_involutive addRC Rplus_opp_r addR0.
  by apply: Rinv_0_lt_compat.
have max_pos: (0 < \max_(a in A) size (f a))%coq_nat.
  apply:ltP.
  move/card_gt0P : (fdist_card_neq0 P) => [a _].
  apply:(bigmax_sup a)=> //.
  by move:(Xpos a); rewrite /X /= (_ : 0 = INR 0)//;move/INR_lt/ltP.

rewrite [X in _ <= X](_ :_ = log ( alp / (1 - alp)) - (log alp) * `E X);
    last first.
  rewrite /alp /Rdiv /log !LogM  //; last first.
      exact: Rinv_0_lt_compat.
    exact: Rinv_0_lt_compat.
  rewrite !LogV // Rmult_plus_distr_r /Rminus.
  rewrite [in RHS]addRC (addRC _ (- log (`E X ) * `E X )) Ropp_plus_distr.
  rewrite  !Ropp_mult_distr_l_reverse Ropp_involutive mulRC -addRA.
  apply: Rplus_eq_compat_l.
  rewrite Rmult_plus_distr_r mulRC Ropp_plus_distr -Ropp_mult_distr_l_reverse.
  apply: Rplus_eq_compat_l.
  rewrite Ropp_mult_distr_l_reverse Ropp_involutive mul1R -addRA.
  rewrite -{1}(addR0 (Log 2 (`E X  + -1))).
  apply: Rplus_eq_compat_l.
  rewrite Rmult_plus_distr_r -Rinv_r_sym // Ropp_mult_distr_l_reverse mul1R.
  rewrite  Ropp_plus_distr Ropp_involutive (addRC 1 _) (addRC (-1) _).
  by rewrite -addRA Rplus_opp_l addR0 LogV //Ropp_involutive Rplus_opp_l.

apply:(Rle_trans _  (log (alp * (1 - (alp ^ (\max_(a| a \in A) size (f a)))) / (1 - alp))
                     - log alp * `E X ) _); last first.
  apply:Rplus_le_compat_r.
  apply:Log_increasing_le => //.
    apply:Rmult_lt_0_compat; last first.
      by apply: Rinv_0_lt_compat ; apply:Rgt_lt; apply:Rgt_minus.
    apply:Rmult_lt_0_compat=> //.
    apply:Rgt_lt; apply:Rgt_minus; apply:Rlt_gt.
    have : 0 <= alp < 1 by apply:conj=> //; first apply:Rlt_le.
     by move/(pow_lt_1_compat _ _ ):max_pos=>tmp; move/tmp/proj2.
  rewrite /Rdiv -mulRA.
  apply:Rmult_le_compat_l; first by apply:Rlt_le.
  rewrite -{2}(mul1R (/ (1 - alp))) ; apply:Rmult_le_compat_r.
    apply:Rlt_le; apply:Rinv_0_lt_compat.
    by apply:Rgt_lt; apply:Rgt_minus; apply:Rlt_gt.
  rewrite -{2}(addR0 1) /Rminus; apply:Rplus_le_compat; first by apply:Rle_refl.
  apply:Rge_le; apply:Ropp_0_le_ge_contravar.
  by apply:pow_le; apply:Rlt_le.

rewrite EX_ord -big_pow1; last by apply:Rlt_not_eq.
rewrite mulRC (big_morph _ (morph_mulRDl _) (mul0R _)).
apply:(Rplus_le_reg_r (\sum_(i in 'I_Nmax.+1) INR i * @Pr _ P (X @^-1 (INR i)) * log alp)).
rewrite -addRA.
rewrite (_ : - _ + _ = 0); last first.
  rewrite addRC addR_opp subR_eq0.
  apply eq_bigr => i _.
  by rewrite ffunE.
rewrite addR0.
rewrite (@eq_bigr _ _ _ 'I_Nmax.+1 _ _ _ (fun i => @Pr _ P (X @^-1 (INR i)) * log (alp ^ i)))=>[|i _]; last first.
  by rewrite log_pow // [in RHS]mulRC -mulRA (mulRC _ (log alp)) mulRA.
rewrite /entropy addRC; move:Ropp_minus_distr; rewrite/Rminus; move<-.
rewrite -(Ropp_involutive (log _)).
apply:Ropp_le_contravar.
rewrite big_morph_oppR.
rewrite -big_split /=.
rewrite [X in _ <= X](_ : _ =  \sum_(i in 'I_Nmax.+1)
      @Pr _ P (X @^-1 (INR i)) * (log (@Pr _ P (X @^-1 (INR i))) - log (alp ^ i))); last first.
  by apply:eq_bigr=>i _; rewrite ffunE Rmult_plus_distr_l Ropp_mult_distr_r_reverse.
rewrite -Rminus_0_l -(mul1R (0 - _)).

have pmf1': \sum_(i in 'I_Nmax) @Pr _ P (X @^-1 (INR i.+1)) = 1.
  rewrite -pmf1N /=.
  evar (h : 'I_Nmax.+1 -> R); rewrite (eq_bigr h); last first.
    move=> a aC; rewrite ffunE /h; reflexivity.
  rewrite {}/h.
  rewrite (@big_ord_exclude0 _ (fun x => @Pr _ P (X @^-1 (INR x)))); first by[].
  rewrite /pr_eq /Pr (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 // => i.
  rewrite inE; move/eqP=> Xi_0.
  by move/Rlt_not_eq:(Xpos i); rewrite Xi_0.
rewrite -{1}(Log_1  2) -pmf1'.
have Rle0Pr (i : nat): 0 <= @Pr _ P (X @^-1 (INR i)).
  apply rsumr_ge0 => ? _; exact: pos_ff_ge0.
have Rle0alpi (i : nat): 0 <= alp ^ i by apply:pow_le; apply:Rlt_le.
pose h := mkPosFun Rle0Pr.
pose g := mkPosFun Rle0alpi.
have dom_by_hg:  h << g.
  apply/dominatesP => i.
  rewrite /g /= => alp0.
  move:lt_0_alp.
  have -> : alp = 0 by move: (pow_nonzero alp i); tauto.
  by move/ltRR.
rewrite (@big_ord_exclude0 _ (fun i => \Pr[X = INR i] * (log \Pr[X = INR i] - log (alp ^ i)))); last first.
  rewrite /pr_eq /Pr.
  have ->: [set x | X x == INR 0] = set0; last by rewrite big_set0 mul0R.
  apply/setP=>i; rewrite inE/=in_set0.
  by apply/eqP; apply: nesym; apply: Rlt_not_eq; apply: Xpos.
by move: (log_sum_inequality_ord_add1' Nmax dom_by_hg).
Qed.

Lemma le_entroPN_logeEX : `H PN <= log (`E X) + log (exp 1).
Proof.
move: EX_pos EX_non0=>EX_pos EX_non0.
move/Rle_lt_or_eq_dec:le_1_EX=>[? | eq_EX_1]; last first.
  rewrite -eq_EX_1 /log Log_1 add0R.
  by move/esym/entroPN_0:eq_EX_1->; apply:log_exp1_Rle_0.
have EX_1 : 0 < `E X  - 1.
  apply:(Rplus_lt_reg_r 1).
  by rewrite addRC -addRA Rplus_opp_l 2!addR0.
have neq_EX1_0 : (`E X  + -1) <> 0.
  by apply:nesym; apply:Rlt_not_eq.
apply:(Rle_trans _ (`E X  * log (`E X ) - (`E X  - 1) * log((`E X ) -1)) _).
  by apply: le_entroPN_logeEX'.
rewrite -{1}(Rplus_minus 1 (`E X)).
rewrite Rmult_plus_distr_r mul1R /Rminus -addRA; apply:Rplus_le_compat_l.
rewrite -Ropp_mult_distr_r_reverse -Rmult_plus_distr_l -(mul1R (log (exp 1))).
rewrite -{3}(Rplus_minus (`E X) 1) -Ropp_minus_distr'.
  rewrite (addR_opp (log (`E X))) -logDiv //.
  apply:div_diff_ub=>//; first by apply:Rlt_le.
by apply:Rlt_le; apply:(Rlt_trans _ _ _ (Rlt_0_1)).
Qed.

End le_entroPN_logeEX.

Section v_scode_converse'_1tuple.

Variables (A : finType) (P : fdist A).
Variable n : nat.
Variable f : A -> seq bool.
Local Notation "'Nmax'" := (Nmax f).
Let X : {RV P -> R} := (INR \o size \o f).
Local Notation "'PN'" := (PN P f).
Hypothesis f_uniq : uniquely_decodable f.

Definition Pf (i : seq bool) := if [ pick x | f x == i ] is Some x then P x else 0.

Lemma Rle0Pf i : 0 <= Pf i.
Proof.
rewrite /Pf.
case:pickP=>[x _ | _ ]; first apply pos_ff_ge0.
apply: Rle_refl.
Qed.

Lemma pmf1_Pf : \sum_(m in 'I_Nmax.+1) \sum_(a in {: m.-tuple bool}) Pf a = 1.
Proof.
move: (uniq_dec_inj f_uniq) => f_inj.
rewrite -(FDist.f1 P).
rewrite (partition_big (inordf (size \o f)) (fun i => i \in 'I_Nmax.+1)) //=.
apply:eq_bigr=>i _.
rewrite (big_seq_tuple' i f_inj (fdist_card_neq0 P)) /Pf=>[|x].
  apply:eq_big=>x.
    apply/eqP/eqP=>[H|<-]; first by apply: ord_inj; rewrite -H inordfE.
    by rewrite inordfE.
  by case:pickP  =>[? /eqP /f_inj ->| /(_ x)]; last rewrite eqxx.
case:pickP =>[? /eqP <-| _ ]; first by rewrite codom_f.
by case:ifP.
Qed.

Definition Pf' (m : 'I_Nmax.+1) := [ffun a : m.-tuple bool =>  Pf a / (PN m)].

Lemma Rle0Pf' (m : 'I_Nmax.+1) :
  PN m <> 0 -> [forall a : m.-tuple bool, 0 <b= Pf' m a].
Proof.
move=> PNnon0; apply/forallP_leRP => a; rewrite /Pf'.
apply:(Rmult_le_reg_r (PN m)).
  move/eqP in PNnon0.
  apply/ltRP; rewrite lt0R PNnon0 ffunE; exact/leRP/Pr_ge0.
rewrite mul0R ffunE /Rdiv -mulRA -Rinv_l_sym // mulR1 /Pf.
case:pickP=>[? _ | _ ]; first by apply pos_ff_ge0.
by apply:Rle_refl.
Qed.

Lemma pmf1_Pf' m : PN m <> 0 -> \sum_(a in {: m.-tuple bool}) Pf' m a = 1.
Proof.
move:(uniq_dec_inj f_uniq)=>f_inj PNnon0.
rewrite /Pf'.
evar (h : m.-tuple bool -> R); rewrite (eq_bigr h); last first.
  move=> a aC; rewrite ffunE /h; reflexivity.
rewrite {}/h.
rewrite -big_distrl /=.
apply:(Rmult_eq_reg_r (PN m))=>//.
rewrite -mulRA -Rinv_l_sym // mul1R mulR1 /= ffunE.
rewrite /pr_eq /Pr (eq_bigr (fun x => Pf (f x)))=>[|a ain]; last first.
  rewrite /Pf.
  case:pickP; first by move=>x /eqP/ f_inj ->.
  by move/(_ a); rewrite eqxx.
rewrite (eq_bigl (fun x =>  size (f x) == m) _)=>[|a]; last first.
  rewrite inE /X/=.
  by apply/eqP/eqP=>[/INR_eq | ->].
rewrite (big_seq_tuple' m f_inj (fdist_card_neq0 P)) /Pf=>[//|i0].
case:pickP => // ?; first by move/eqP <-; rewrite codom_f.
by case:ifP.
Qed.

Lemma rsum_disjoints_set h: \sum_(a in [set : 'I_Nmax.+1]) h a =
 \sum_(a in [set x | PN x == 0]) h a + \sum_(a in [set x | PN x != 0]) h a.
Proof.
rewrite -big_union //; last first.
  rewrite disjoints_subset.
  rewrite (_ : ~: [set x | PN x == 0] = [set x | PN x != 0])//.
  apply/setP=>i.
  by rewrite !inE.
by apply eq_bigl => i; rewrite !inE orbN.
Qed.

Lemma rewrite_HP_with_Pf : `H P =
 - \sum_(m in 'I_Nmax.+1) \sum_(a in {: m.-tuple bool}) Pf a * log (Pf a).
Proof.
move:(uniq_dec_inj f_uniq)=> f_inj.
apply:Ropp_eq_compat.
rewrite [in LHS](partition_big (inordf (size \o f)) (fun i => i \in 'I_Nmax.+1))//=.
apply:eq_bigr=>i _.
rewrite (eq_bigr (fun i0 => Pf (f i0) * log (Pf (f i0))))=>[|a]; last first.
  rewrite /Pf.
  case:(pickP _) => [x0 /eqP /f_inj->|] //.
  move/(_ a); by rewrite eqxx.
rewrite (eq_bigl (fun x=> size (f x) == i) _) =>[|x]; last first.
  apply/eqP/eqP=>[<-| H]; first by rewrite inordfE.
  by apply/ord_inj; rewrite inordfE.
rewrite (@big_seq_tuple' _ i _ f_inj (fun a => Pf a * log (Pf a)) (fdist_card_neq0 P))//.
rewrite /Pf; move=>i0.
case:(pickP ) => // x; first by move/eqP <-; rewrite codom_f.
by case:ifP; rewrite mul0R.
Qed.

Lemma rewrite_HP_with_PN :
  `H P = - \sum_(m in [set x | PN x != 0]) PN m *
           (\sum_(a in {: m.-tuple bool}) Pf' m a * (log (Pf' m a) + log (PN m))).
Proof.
rewrite rewrite_HP_with_Pf.
apply:Ropp_eq_compat.
rewrite (eq_bigl (fun m => m \in [set : 'I_Nmax.+1]) _)=>[|?]; last first.
  by rewrite /= in_setT.
rewrite rsum_disjoints_set.
rewrite [Y in Y + _ = _](_ : _ = 0); last first.
  rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 // => i.
  rewrite inE /pr_eq /Pr ffunE /= => /eqP/prsumr_eq0P=>H.
  have {H}H: forall j : A, j \in [set x | INR (size (f x)) == INR i] -> P j = 0.
    apply:H=> ? ?; exact: pos_ff_ge0.
  rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 // => i0 i_n.
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
rewrite ffunE.
rewrite {1}/Pf'.
rewrite ffunE.
rewrite [in RHS]mulRC /Rdiv -mulRA -mulRA.
case: (Req_dec (Pf i0) 0)=>[->| /nesym Pfi0_non0]; first by rewrite !mul0R.
apply:Rmult_eq_compat_l.
rewrite mulRC -mulRA.
rewrite {2}/PN.
rewrite [in X in _ = _ * (_ * / X)]/= [in X in _ = _ * (_ * / X)]ffunE.
rewrite -Rinv_r_sym //; last by rewrite /PN /= ffunE in Pr_non0.
rewrite mulR1 /log LogM.
    rewrite LogV.
      rewrite /PN /= ffunE.
      by rewrite -addRA Rplus_opp_l addR0.
    move/eqP in Pr_non0.
    apply/ltRP; rewrite lt0R Pr_non0 /= ffunE; exact/leRP/Pr_ge0.
  move/eqP in Pfi0_non0.
  apply/ltRP; rewrite lt0R eq_sym Pfi0_non0; apply/leRP.
  rewrite /Pf; case:pickP=>[? _ | ? ]; first by apply pos_ff_ge0.
  by apply:Rle_refl.
apply:Rinv_0_lt_compat.
move/eqP in Pr_non0.
apply/ltRP; rewrite lt0R Pr_non0 ffunE; exact/leRP/Pr_ge0.
Qed.

Lemma rewrite_HP_with_HPN : `H P =  \sum_(m in [set x : 'I_Nmax.+1 | PN x != 0])
PN m * (- \sum_(a in {: m.-tuple bool}) Pf' m a *
(log ((Pf' m a)))) + `H PN.
Proof.
rewrite {2}/entropy.
rewrite (eq_bigl (fun m => m \in [set : 'I_Nmax.+1]) (fun x=> _ * log _))=>[|?]; last first.
  by rewrite /= in_setT.
rewrite rsum_disjoints_set.
rewrite [Y in  _ = _ + - (Y + _)](_ :_ = 0); last first.
  rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 // => i.
  rewrite inE /PN /= =>/eqP->.
  by rewrite mul0R.
rewrite add0R rewrite_HP_with_PN !big_morph_oppR -big_split/=.
apply:eq_bigr=>i.
rewrite inE =>/eqP=>Pr_non0.
rewrite Ropp_mult_distr_r_reverse -Ropp_plus_distr; apply:Ropp_eq_compat.
rewrite -Rmult_plus_distr_l; apply:Rmult_eq_compat_l.
rewrite -[Y in _ = _ + Y]mul1R -(pmf1_Pf' Pr_non0) big_distrl/= -big_split/=.
by apply:eq_bigr=>? _; rewrite Rmult_plus_distr_l.
Qed.

Lemma apply_max_HPN : `H P <= `E X  + `H PN.
Proof.
have f_inj := uniq_dec_inj f_uniq.
rewrite rewrite_HP_with_HPN addRC (addRC _ (`H _)) leR_add2l EX_ord.
rewrite (eq_bigl (fun m => m \in [set : 'I_Nmax.+1]) (fun x=> INR x * _ ))=>[|?]; last first.
  by rewrite /= in_setT.
rewrite rsum_disjoints_set.
rewrite [Y in _ <= Y + _ ](_ :_ = 0).
  rewrite add0R.
  apply: ler_rsum => i.
  rewrite mulRC inE; move/eqP=>H.
  apply:Rmult_le_compat_r.
    rewrite /PN /= ffunE.
    exact: Pr_ge0.
  pose pmf_Pf' := mkPosFfun (Rle0Pf' H).
  have pmf1'_Pf' : \sum_(a in {: i.-tuple bool}) pmf_Pf' a == 1 :> R.
    by apply/eqP; apply: (pmf1_Pf' H).
  pose distPf := FDist.mk pmf1'_Pf'.
  move: (entropy_max distPf).
  rewrite card_tuple /= card_bool -natRexp log_pow (_ : INR 2 = 2) //.
  by rewrite /log Log_n // mulR1.
rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 // => i.
rewrite inE /PN /==>/eqP->.
by rewrite mulR0.
Qed.

Lemma apply_le_HN_logE_loge : `H P <= `E X  + log ((exp 1) * `E X).
Proof.
apply: (leR_trans apply_max_HPN).
rewrite leR_add2l mulRC /log (LogM _ (EX_pos P f_uniq) (exp_pos 1)).
exact: le_entroPN_logeEX f_uniq.
Qed.

End v_scode_converse'_1tuple.

Section v_scode_converse'_ntuple.

Variable A : finType.
Variable n:nat.
Variable f : encT A (seq bool) n.
Variable P : fdist A.
Hypothesis f_uniq : uniquely_decodable f.

Lemma converse_case1 : E_leng_cw f P < (INR n) * (log (INR #|A|)) ->
`H (P `^ n) <= E_leng_cw f P + log ((exp 1) * (INR n) * (log (INR #|A|))).
Proof.
move=>H.
apply:(Rle_trans _ _ _ (apply_le_HN_logE_loge (P `^ n) f_uniq)).
apply:Rplus_le_compat_l.
apply:Log_increasing_le => //.
  apply:(Rmult_lt_0_compat _ _ (exp_pos 1)).
  apply: (EX_pos (P `^ n) f_uniq).
rewrite -mulRA; apply:Rmult_le_compat_l; first by apply:Rlt_le; apply:exp_pos.
by apply:Rlt_le.
Qed.

Lemma converse_case2 :  (INR n) * (log (INR #|A|)) <= E_leng_cw f P ->
 `H (P `^ n) <= E_leng_cw f P.
Proof.
move=> H.
rewrite entropy_TupleFDist.
apply: (Rle_trans (INR n * `H P) (INR n * log (INR #|A|)) _); last by apply: H.
apply: Rmult_le_compat_l; last by apply: entropy_max.
by rewrite (_ : 0 = INR 0) //; apply:le_INR; apply/leP; apply:leq0n.
Qed.

End v_scode_converse'_ntuple.

Section Extend_encoder.

Variable A : finType.
Variable n m:nat.
Variable f : encT A (seq bool) n.
Variable P : fdist A.
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
- move/(congr1 size); by rewrite size_cat size_map size_enum_ord addSn.
- move/(congr1 size); by rewrite size_cat size_map size_enum_ord addSn.
- move/eqP.
  rewrite eqseq_cat; last by rewrite !size_tuple.
  case/andP => H1 /eqP /IHsta1 ->.
  congr (_ :: _).
  by apply/tuple_of_row_inj/eqP.
Qed.

Lemma ELC_TupleFDist : E_leng_cw fm (P `^ n)  = (INR m) * E_leng_cw f P.
Proof.
rewrite /E_leng_cw /=  /fm.
pose X := (*mkRvar (P `^ n)*) (INR \o size \o f).
elim:m=>[| m'].
  rewrite mul0R /Ex (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 // => i _.
  rewrite TupleFDist.zero ?mulR1.
  rewrite [tuple_of_row]lock /= -lock.
  rewrite (_ : tuple_of_row i = [tuple]) //.
  apply: eq_from_tnth.
  by case; case.
elim:m'=>[_ |m'' _ IH].
  rewrite mul1R.
  rewrite -[in RHS]E_cast_RV_tuplefdist1.
  apply:eq_bigr=>i _.
  rewrite TupleFDist.one.
  apply: Rmult_eq_compat_r.
  rewrite [tuple_of_row]lock /= -lock.
  rewrite (_ : tuple_of_row i = [tuple of [:: i ``_ ord0]]); last first.
    apply eq_from_tnth => a; by rewrite {a}(ord1 a) tnth_mktuple.
  by rewrite /extension /= cats0.
pose fm1 (x : 'rV['rV[A]_n]_(m''.+1)) := extension f (tuple_of_row x).
pose Xm1 := (*mkRvar ((P `^ n) `^ (m''.+1))*) (INR \o size \o fm1).
pose fm2 (x : 'rV['rV[A]_n]_(m''.+2)) := extension f (tuple_of_row x).
pose Xm2 := (*mkRvar ((P `^ n) `^ (m''.+2))*) (INR \o size \o fm2).
have X_Xm1_Xm2 : Xm2 \= X @+ Xm1.
  (*apply:conj=>[|x /=]; first by rewrite -TupleDist.head_of -TupleDist.tail_of.*)
  rewrite /Xm2.
  move=> x /=.
  rewrite-plus_INR plusE -size_cat.
  rewrite /fm2 /extension /fm1 /extension.
  rewrite [tuple_of_row]lock /= -lock.
  congr (INR (size _)).
  rewrite {1}(_ : x = row_mx (\row_(i < 1) (x ``_ ord0)) (rbehead x)); last first.
    apply/matrixP => a b; by rewrite {a}(ord1 a) row_mx_rbehead.
Local Open Scope ring_scope.
  rewrite (@tuple_of_row_row_mx _ _ _ (\row_(i < 1) (x ``_ ord0)) (rbehead x)).
  rewrite map_cat flatten_cat.
  congr (_ ++ _).
  rewrite (_ : tuple_of_row _ = [tuple of [:: x ``_ ord0]]); last first.
    by apply eq_from_tnth => i; rewrite {i}(ord1 i) /= tnth_mktuple mxE.
  by rewrite /= cats0.
rewrite (E_sum_2 X_Xm1_Xm2).
rewrite S_INR mulRDl -IH.
rewrite addRC.
congr (Rplus _ _).
  rewrite /Xm1 -/fm1.
  by rewrite /Ex /p_of TupleFDist.tail_of.
rewrite -/X mul1R.
by rewrite /Ex /p_of TupleFDist.head_of.
Qed.

End Extend_encoder.

Section v_scode_converse'.

Variables (A : finType) (P : fdist A).
Variable n : nat.
Variable f : encT A (seq bool) n.
Hypothesis f_uniq : uniquely_decodable f.

Let alp := exp 1 * log (INR #| 'rV[A]_n |).
Let m eps:= Z.abs_nat (floor (exp (INR (maxn (Z.abs_nat (ceil ((ln alp) + INR n * eps * ln 2)))
                                  (maxn (Z.abs_nat (ceil (4 /(INR n * eps * ln 2)))) 1))))).

Lemma mpos eps: 0 <> INR n -> 0 < INR (m eps).
Proof.
rewrite /m =>nnon0.
rewrite (_ : 0 = INR 0)//; apply: lt_INR.
rewrite {1}(_ : 0%nat = Z.abs_nat 0)//; apply:Zabs_nat_lt; apply:conj=>//.
apply: lt_0_IZR.
apply: (Rlt_trans _ (exp (INR (maxn (Z.abs_nat (ceil (ln alp + INR n * eps * ln 2)))
                 (maxn (Z.abs_nat (ceil (4 / (INR n * eps * ln 2))))
                    1))) -1) _); last exact: (proj1 (floorP _)).
apply: (Rplus_lt_reg_r 1).
rewrite addRC /Rdiv -addRA Rplus_opp_l 2!addR0 -{1}exp_0.
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
  apply: (Rlt_trans _ (exp x - 1) _); last exact: (proj1 (floorP _)).
  apply: (Rplus_lt_reg_r 1).
  rewrite addRC /Rminus -addRA Rplus_opp_l 2!addR0 -exp_0.
  by apply: exp_increasing=>//.
have le_1_alp: 1 <= alp.
  rewrite /alp -(mulR1 1).
  apply: (Rmult_le_compat _ _ _ _ Rle_0_1 Rle_0_1).
  rewrite mulR1.
  apply: (Rle_trans _ 2); last by apply: leR2e.
  by rewrite -{1}(addR0 1); apply: (Rplus_le_compat_l _ _ _ Rle_0_1).
  rewrite card_matrix -natRexp mul1n log_pow //.
  by rewrite (_ : 0 = INR 0)//; apply: lt_INR; apply/ltP; apply: fdist_card_neq0.
have alppos: 0 < alp  by apply: (Rlt_le_trans _ 1 _ Rlt_0_1).
have Ypos: 0 < Y.
  apply: Rmult_lt_0_compat => //.
  exact: Rmult_lt_0_compat.
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
  by apply: Rlt_le; exact: proj1 (floorP _).
rewrite INR_Zabs_nat; last by apply: le_IZR; apply: Rlt_le; apply: IZR_lt.
rewrite {1}/log LogM//; last exact: IZR_lt.
rewrite -/(log _).
apply: (Rmult_le_reg_r (ln 2) _ _ ln2_gt0).
rewrite Rmult_plus_distr_r /Log/Rdiv -(mulRA (ln alp)) -(Rinv_l_sym _ (nesym (Rlt_not_eq _ _ (ln2_gt0)))).
rewrite mulR1 -(mulRA _ (/ ln 2) _) -(Rinv_l_sym _ (nesym (Rlt_not_eq _ _ (ln2_gt0)))) mulR1.
apply: (Rle_trans _ (x + ln alp) _).
  apply: Rplus_le_compat_r.
  rewrite -(ln_exp x).
  apply: ln_increasing_le; last exact: (proj2 (floorP _)).
  apply: (Rlt_trans _ (exp x - 1) _); last exact: proj1 (floorP _).
  apply: (Rplus_lt_reg_r 1).
  rewrite addRC -addRA Rplus_opp_l 2!addR0 -exp_0.
  apply: exp_increasing=>//.
apply: (Rle_trans _ (2 * x - (eps * INR n * ln 2))).
  rewrite double /Rminus -addRA.
  apply: Rplus_le_compat_l.
  apply: (Rplus_le_reg_r (eps * INR n * ln 2)).
  rewrite -addRA Rplus_opp_l addR0 mulRC mulRA mulRC (mulRC _ eps) mulRA.
  apply: (Rle_trans _ (IZR (ceil (ln alp +  INR n * eps * ln 2)))); first exact: proj1 (ceilP _).
  rewrite -INR_Zabs_nat; first by apply: le_INR; apply/leP; apply: leq_maxl.
  apply: le_IZR.
  apply: (Rle_trans _ (ln alp + Y)); last by rewrite /Y (mulRC eps); exact: proj1 (ceilP _).
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
  apply: (Rle_trans _ ( (4 * / (INR n * eps * ln 2)))); last exact: proj1 (ceilP _).
  rewrite (mulRC (INR n)); by apply: Rle_refl.
apply:le_IZR.
apply: (Rle_trans _ ( (4 * / (INR n * eps * ln 2)))); last exact: proj1 (ceilP _).
apply: Rle_mult_inv_pos; first by apply: (Rlt_le _ _ (Rmult_lt_0_compat _ _ Rlt_0_2 Rlt_0_2)).
by rewrite (mulRC (INR n)).
Qed.

Theorem v_scode_converse' :
  (INR n) * `H P <= E_leng_cw f P.
Proof.
case: (Req_dec 0 (INR n))=>[<-|nnon0].
  rewrite mul0R.
  apply: Rlt_le.
  apply: (EX_pos (P `^ n) f_uniq).
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
  rewrite !entropy_TupleFDist ELC_TupleFDist.
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
rewrite !entropy_TupleFDist ELC_TupleFDist -!mulRA mulRA.
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
rewrite ELC_TupleFDist mulRC (mulRC (INR (m eps))) card_matrix mul1n -natRexp log_pow; last first.
  by rewrite (_ : 0 = INR 0)//; apply: lt_INR; apply/ltP; apply: fdist_card_neq0.
move/(Rmult_lt_reg_r _ _ _ (mpos eps nnon0))=>H'.
apply: (Rle_trans _ (E_leng_cw f P)).
exact: (le_1_EX (P `^ n) f_uniq).
exact: Rlt_le.
Qed.

End v_scode_converse'.

Section v_scode_converse.

Variables (A : finType) (P : fdist A).
Variable n : nat.
Variable f : encT A (seq bool) n.
Hypothesis f_uniq : uniquely_decodable f.

Theorem v_scode_converse : INR n * `H P <= E_leng_cw f P.
Proof. exact: v_scode_converse'. Qed.

End v_scode_converse.
