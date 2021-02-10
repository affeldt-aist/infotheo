(* infotheo: information theory and error-correcting codes in Coq               *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later              *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg matrix.
Require Import Reals.
From mathcomp Require Import Rstruct.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext.
Require Import Rbigop fdist proba entropy divergence log_sum source_code.

(******************************************************************************)
(*        Source coding theorem (variable length, converse part)              *)
(*                                                                            *)
(* For details, see Ryosuke Obi. In MI Lecture Note Workshop on Theorem       *)
(* proving and provers for reliable theory and implementations (TPP2014),     *)
(* Kyushu University, December 3--5, 2014, volume 61, pages 76--78, Dec 2014  *)
(*                                                                            *)
(* original source file from R. Obi, quickly patched to compile with infotheo *)
(* [2019-08-19] and simplified afterwards                                     *)
(******************************************************************************)

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
Variable n : nat.
Variable f g : nat ->R^+.
Hypothesis f_dom_by_g : f `<< g.

Lemma log_sum_inequality_ord_add1 :
  (\sum_(i < n) f i.+1) *
  (log ((\sum_(i < n) f i.+1) / (\sum_(i < n) g i.+1))) <=
  \sum_(i < n) f i.+1 * (log (f i.+1 / g i.+1)).
Proof.
have Rle0f_1 : forall x : 'I_n, 0 <= f x.+1 by move=> ?; apply pos_f_ge0.
have Rle0g_1 : forall x : 'I_n, 0 <= g x.+1 by move=> ?; apply pos_f_ge0.
have newRle0f_1: [forall x : 'I_n, 0 <b= [ffun x : 'I_n => f x.+1] x].
  by apply/forallP_leRP => ?; rewrite ffunE.
have newRle0g_1: [forall x : 'I_n, 0 <b= [ffun x : 'I_n => g x.+1] x].
  by apply/forallP_leRP => ?; rewrite ffunE.
have f_dom_by_g1 : mkPosFfun newRle0f_1 `<< mkPosFfun newRle0g_1.
  apply/dominatesP => a; move/dominatesP : f_dom_by_g.
  rewrite /= !ffunE; exact.
have H : forall h,
  \sum_(a | a \in [set: 'I_n]) h a.+1 = \sum_(a | a \in 'I_n) h a.+1.
  by move=> ?; under eq_bigl do rewrite in_setT.
rewrite -!H -(H (fun i => f i * log (f i / g i))).
move: (log_sum [set: 'I_n] (mkPosFfun newRle0f_1) (mkPosFfun newRle0g_1) f_dom_by_g1).
rewrite /=.
under eq_bigr do rewrite ffunE.
under [in X in _ * log (_ / X) <= _ -> _]eq_bigr do rewrite ffunE.
under [in X in _ <= X  -> _]eq_bigr do rewrite ffunE.
move/leR_trans; apply.
rewrite leR_eqVlt; left.
by under eq_bigr do rewrite ffunE.
Qed.

Lemma log_sum_inequality_ord_add1' :
  (\sum_(i < n) f i.+1) * (log (\sum_(i < n) f i.+1)
                                - log (\sum_(i < n) g i.+1)) <=
    \sum_(i < n) f i.+1 * (log (f i.+1) - log (g i.+1)).
Proof.
rewrite [X in _ <= X]
        (_ : _ = \sum_(i < n) f i.+1 * log (f i.+1 / (g i.+1))).
  rewrite [X in X <= _](_ : _ =  (\sum_(i < n) f i.+1) *
   (log ((\sum_(i < n)f i.+1) / (\sum_(i < n) g i.+1)))).
      exact: log_sum_inequality_ord_add1.
  have : 0 <= \sum_(i in 'I_n) f i.+1.
    by apply sumR_ge0 => ? _; exact: pos_f_ge0.
  case=>[Hf | <-]; last by rewrite !mul0R.
  have : 0 <= \sum_(i in 'I_n) g i.+1.
    by apply sumR_ge0 => ? _; exact: pos_f_ge0.
  case => [Hg |].
    rewrite /log LogM // ?LogV //; last exact: invR_gt0.
  have Rle0g_add1 : forall x : 'I_n, 0 <= g x.+1 by move=> ?; apply pos_f_ge0.
  move=> H.
  have eq_g_0 : forall i : 'I_n, 0 = g i.+1.
    move/esym/psumR_eq0P : H => H i; by rewrite H.
  have : 0 = \sum_(i < n) f i.+1.
    apply/esym/psumR_eq0P => i _; [exact: pos_f_ge0|].
    by move/dominatesP : f_dom_by_g; apply; rewrite -eq_g_0.
  by move => tmp; move: Hf; rewrite -tmp; move/Rlt_not_eq.
apply: eq_bigr => i _.
case: (pos_f_ge0 f i.+1) => [fpos|<-]; last by rewrite !mul0R.
case: (pos_f_ge0 g i.+1); last first.
  move/esym => g0; move/dominatesP : f_dom_by_g => /(_ _ g0) ->.
  by rewrite !mul0R.
by move=>gpos; rewrite /log LogM // ?LogV //; exact: invR_gt0.
Qed.

End log_sum_ord.

Section Ordinal.
Variables (T : finType) (f : T -> nat).

Definition inordf t := inord (f t) : 'I_(\max_t f t).+1.

Lemma inordfE :  (fun t : T => nat_of_ord (inordf t)) =1 f .
Proof.
move=>t.
apply: inordK; by apply: leq_bigmax.
Qed.

End Ordinal.

Section Bigop_Lemma.
Variable A : finType.
Variable n : nat.
Variable f : A -> seq bool.
Hypothesis f_inj : injective f.

Let big_seq_tuple' (F : seq bool -> R) : (0 < #|A|)%nat ->
  \sum_(a | size (f a) == n) F (f a) =
  \sum_(i : n.-tuple bool | tval i \in codom f) F i.
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

Lemma big_seq_tuple (F : seq bool -> R) : (0 < #|A|)%nat ->
  (forall i, F i = if i \in codom f then F i else 0)->
  \sum_(i in {: n.-tuple bool}) F i = \sum_(a| size (f a) == n) F (f a).
Proof.
move=> Anon0 Fi0.
rewrite big_seq_tuple' //.
rewrite (eq_bigr (fun a => if (tval a \in codom f) then F a else 0)) => [|i _].
  by rewrite -big_mkcondr.
by rewrite {1}Fi0.
Qed.

Lemma big_pow1 x : x <> 1 ->
  \sum_(i < n) x ^ i.+1 = x * (1 - (x ^ n)) / (1 - x).
Proof.
move => neq_x_1.
apply: (Rplus_eq_reg_l 1).
rewrite [X in _ = X + _](_ : _ = (1 - x) / (1 - x)); last first.
  rewrite divRR //; apply/eqP; rewrite subR_eq0; exact/nesym.
rewrite mulRDr mulR1 -mulRDl addRA [in RHS]addRC -addRA.
rewrite Rplus_opp_l addR0 (addRC _ 1) mulRN.
rewrite -(big_mkord xpredT (fun i => x ^ i.+1)) (_ : n = n.+1.-1) //.
rewrite -(big_add1 _ _ _ _  xpredT)-{1}(pow_O x) -big_ltn //.
by rewrite big_mkord -sum_f_R0_sumR tech3.
Qed.

Lemma log_pow r : 0 < r -> log (r ^ n) = n%:R * log r.
Proof.
elim:n=> [|n' IH lt_0_r]; first by rewrite /log Log_1 mul0R.
rewrite /log LogM //;last exact: pow_lt.
rewrite /log in IH; by rewrite IH // -addn1 addRC plus_INR mulRDl mul1R.
Qed.

End Bigop_Lemma.

Local Open Scope vec_ext_scope.

Section Entropy_lemma.
Variables (A : finType) (P : fdist A) (n : nat).

Lemma entropy_TupleFDist : `H (P `^ n) = n%:R * `H P.
Proof.
elim:n=>[|n0 IH].
  rewrite mul0R /entropy /= big1 ?oppR0 // => i _.
  by rewrite TupleFDist.zero /log Log_1 mulR0.
rewrite S_INR mulRDl mul1R -IH /entropy -(big_rV_cons_behead _ xpredT xpredT).
rewrite /= -oppRD; congr (- _).
rewrite [LHS](_ :_ = \sum_(i | i \in A) P i * log (P i) *
    (\sum_(j in 'rV[A]_n0) (\prod_(i0 < n0) P j ``_ i0)) +
     \sum_(i | i \in A) P i * \sum_(j in 'rV[A]_n0)
    (\prod_(i0 < n0) P j ``_ i0) * log (\prod_(i0 < n0) P j ``_ i0)); last first.
  rewrite -big_split /=; apply: eq_bigr => i _.
  rewrite -mulRA -mulRDr (mulRC (log (P i))) (big_distrl (log (P i)) _ _) /=.
  rewrite -big_split /= big_distrr /=.
  apply: eq_bigr => i0 _.
  rewrite TupleFDist.dE.
  rewrite big_ord_recl (_ : _ ``_ ord0 = i); last first.
    by rewrite mxE; case: splitP => // j Hj; rewrite mxE.
  rewrite -mulRA.
  case: (FDist.ge0 P i) => [pi_pos| <-]; last by rewrite !mul0R.
  congr (P i * _).
  rewrite -mulRDr.
  rewrite (@eq_bigr _ _ _ _ _ _
      (fun x => P ((row_mx (\row_(_ < 1) i) i0) ``_ (lift ord0 x)))
      (fun x => P i0 ``_ x)) => [|i1 _]; last first.
    congr (P _).
    rewrite mxE.
    case: splitP => j; first by rewrite (ord1 j).
    by rewrite lift0 add1n; case=> /eqP /val_eqP ->.
  case: (Req_dec 0 (\prod_(i' < n0) P i0 ``_ i')) => [<-|rmul_non0].
    by rewrite !mul0R.
  have rmul_pos : 0 < \prod_(i1<n0) P i0 ``_ i1.
    move/eqP in rmul_non0.
    apply/ltRP; rewrite lt0R eq_sym rmul_non0; apply/leRP/prodR_ge0 => ?.
    exact: FDist.ge0.
  by rewrite /log LogM // !mulRDr mulRA mulRA.
rewrite (_ : \sum_(j in 'rV_n0) _ = 1); last first.
  by rewrite -(FDist.f1 (P `^ n0)); apply eq_bigr => i _; rewrite TupleFDist.dE.
rewrite -big_distrl /= mulR1 [in RHS]addRC; congr (_ + _).
rewrite -big_distrl /= FDist.f1 mul1R; apply eq_bigr => i _.
by rewrite TupleFDist.dE.
Qed.

End Entropy_lemma.

Section le_entroPN_logeEX.

Variable (A : finType) (P : fdist A) (f : A -> seq bool).
Let X : {RV P -> R} := INR \o size \o f.
Definition Nmax := \max_(a in A) size (f a).
Hypothesis f_uniq : uniquely_decodable f.

Let Xnon0 x : 0 <> X x.
Proof.
rewrite /X /=; case: (Req_dec 0 (size (f x))%:R)=>// H.
move: H; rewrite (_ : 0 = 0%:R)//; move/INR_eq.
move/esym/size0nil => fx_nil.
move: (@f_uniq [::] ([:: x])).
by rewrite /extension /= fx_nil cat0s => /(_ erefl).
Qed.

Lemma Xpos a : 0 < X a.
Proof.
move/nesym/INR_not_0 : (@Xnon0 a) => H.
by rewrite ltR0n ltn_neqAle /= leq0n andbT; apply/eqP/nesym.
Qed.

Let PN_ge0 : forall i : 'I_Nmax.+1, 0 <= [ffun x : 'I__ => `Pr[ X = x%:R]] i.
Proof. by move => a; rewrite ffunE. Qed.

Lemma PN_sum1 :
  \sum_(i < Nmax.+1) [ffun x : 'I__ => `Pr[ X = x%:R] ] i = 1.
Proof.
rewrite -(FDist.f1 P).
rewrite [in RHS](partition_big (inordf (size \o f)) (fun i => i \in 'I_Nmax.+1)) //=.
apply: eq_bigr => i _; rewrite ffunE.
rewrite /pr_eq; unlock.
apply: eq_bigl => i0.
rewrite /= inE.
apply/eqP/eqP=>[/INR_eq H|<-]; last by rewrite inordfE.
apply: ord_inj.
by rewrite -H inordfE.
Qed.

Definition PN := FDist.make PN_ge0 PN_sum1.

Lemma EX_ord : `E X = \sum_(i < Nmax.+1) i%:R * PN i.
Proof.
rewrite /Ex (partition_big (inordf (size \o f)) (fun i => i \in 'I_Nmax.+1)) //=.
apply : eq_bigr=> i _.
rewrite /pr_eq; unlock.
rewrite /Pr ffunE mulRC big_distrl /=.
under eq_bigr do rewrite mulRC.
apply: congr_big=>[//| x| x]; last by move/eqP<-; rewrite inordfE.
rewrite inE; apply/eqP/eqP; first by move<-; rewrite inordfE.
by move/INR_eq => H; apply: ord_inj; rewrite -H inordfE.
Qed.

Lemma le_1_EX : 1 <= `E X.
Proof.
rewrite -(FDist.f1 P); apply: leR_sumR => i _.
rewrite -{1}(mul1R (P i)).
apply leR_wpmul2r; first exact: FDist.ge0.
by move: (Xpos i); rewrite (_ : 1 = 1%:R) //= (_ : 0 = 0%:R) // ltR_nat leR_nat.
Qed.

Lemma EX_gt0 : 0 < `E X. Proof. exact: ltR_leR_trans le_1_EX. Qed.

Lemma entroPN_0 : `E X = 1 -> `H PN = 0.
Proof.
move => EX_1.
have eq_0_P : forall a, X a <> 1 -> 0 = P a.
  move: EX_1.
  rewrite -{1}(FDist.f1 P) => EX1 a Xnon1.
  have /leR_sumR_eq H : forall i : A, i \in A -> P i <= (size (f i))%:R * P i.
    move=> i _; rewrite -{1}(mul1R ( P i)).
    apply/leR_wpmul2r; first exact: FDist.ge0.
    by move: (Xpos i); rewrite (_ : 1 = 1%:R) //= (_ : 0 = 0%:R) // ltR_nat leR_nat.
  case: (Req_dec (P a) 0) => //.
  have : (size (f a))%:R * P a = P a by rewrite (H EX1 a).
  rewrite -{2}(mul1R (P a)).
  by move/Rmult_eq_reg_r => tmp /tmp.
rewrite /entropy Ropp_eq_0_compat //.
rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 //= => i _.
rewrite /pr_eq; unlock.
rewrite /Pr ffunE.
case (Req_dec i%:R 1)=>[->| neq0].
  rewrite [X in _ * log X = _](_ : _ = 1); first by rewrite /log Log_1 mulR0.
  rewrite -{2}(FDist.f1 P).
  rewrite [in RHS](bigID (fun a => a \in [set x | (size (f x))%:R == 1])) /=.
  rewrite [X in _ = _ + X](_ : _ = 0); first by rewrite addR0.
  rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 // => j.
  by rewrite inE; move/eqP/eq_0_P.
rewrite [X in X * _ = _](_ : _ = 0); first by rewrite mul0R.
rewrite big1 // => j.
rewrite inE; move/eqP => eq_Xj_i.
by move: neq0; rewrite -eq_Xj_i => /eq_0_P.
Qed.

Lemma le_entroPN_logeEX' :
  `H PN <= `E X  * log (`E X) - (`E X  - 1) * log((`E X ) - 1).
Proof.
move/Rle_lt_or_eq_dec:le_1_EX=>[lt_EX_1| eq_E_0]; last first.
  rewrite -eq_E_0 /Rminus Rplus_opp_r mul0R Ropp_0 addR0 mul1R /log Log_1.
  by move/esym/entroPN_0 : eq_E_0 ->; exact: leRR.
have lt_0_EX_1 : 0 < `E X - 1 by rewrite subR_gt0.
pose alp := (`E X - 1) / `E X .
have gt_alp_1 : alp < 1.
  rewrite -(ltR_pmul2r EX_gt0) // mul1R.
  rewrite /alp -mulRA mulVR ?mulR1; last exact/gtR_eqF/EX_gt0.
  by rewrite -ltR_subr_addl subRR -ltR_oppl oppR0.
have lt_0_alp : 0 < alp by rewrite /alp; exact/divR_gt0/EX_gt0.
have EX_pos' : 0 < 1 - (`E X  - 1) / `E X .
  rewrite divRDl divRR; last exact/gtR_eqF/EX_gt0.
  rewrite divN1R addR_opp subRB subRR add0R; exact/invR_gt0/EX_gt0.
have max_pos: (0 < \max_(a in A) size (f a))%coq_nat.
  apply/ltP.
  move/card_gt0P : (fdist_card_neq0 P) => [a _].
  apply: (bigmax_sup a)=> //.
  by move: (Xpos a); rewrite /X /= (_ : 0 = INR 0) // => /INR_lt/ltP.
rewrite [X in _ <= X](_ :_ = log ( alp / (1 - alp)) - (log alp) * `E X);
    last first.
  rewrite /alp /Rdiv /log !LogM //; last 2 first.
    exact/invR_gt0/EX_gt0.
    exact/invR_gt0.
  rewrite ![in RHS](LogV _ EX_gt0) // mulRDl [in RHS]/Rminus.
  rewrite [in RHS]addRC (addRC _ (- log (`E X ) * `E X )) oppRD.
  rewrite [in RHS]mulNR oppRK -addRA.
  rewrite [in LHS]mulRC -addR_opp; congr (_ + _).
  rewrite [in LHS]mulRDl mulRC oppRD mulN1R oppRK; congr (_ + _).
  rewrite -[in RHS]addRA -[LHS]addR0; congr (_ + _).
  rewrite mulRDl mulRV; last exact/gtR_eqF/EX_gt0.
  rewrite mulN1R !addR_opp subRB subRR add0R invRK ?Rplus_opp_l //.
  exact/gtR_eqF/EX_gt0.
apply: (@leR_trans (log (alp * (1 - (alp ^ (\max_(a | a \in A) size (f a))))
                               / (1 - alp)) - log alp * `E X ) _); last first.
  rewrite leR_add2r.
  apply: Log_increasing_le => //.
    apply/mulR_gt0; last by apply/invR_gt0; rewrite subR_gt0.
    apply/mulR_gt0 => //; rewrite subR_gt0.
    have : 0 <= alp < 1 by split => //; exact/ltRW.
    by case/(pow_lt_1_compat _ _)/(_ max_pos).
  rewrite /Rdiv -mulRA; apply/(leR_wpmul2l (ltRW lt_0_alp)).
  rewrite -{2}(mul1R (/ (1 - alp))).
  apply/leR_wpmul2r; first by apply/ltRW/invR_gt0; rewrite subR_gt0.
  rewrite -addR_opp addRC -leR_subr_addr subRR leR_oppl oppR0.
  exact/expR_ge0/ltRW.
rewrite EX_ord -big_pow1; last exact/eqP/ltR_eqF.
rewrite mulRC (big_morph _ (morph_mulRDl _) (mul0R _)).
rewrite -(@leR_add2r (\sum_(i < Nmax.+1) i%:R * `Pr[ X = i%:R ] * log alp)).
rewrite -addRA (_ : - _ + _ = 0) ?addR0; last first.
  by rewrite addRC addR_opp subR_eq0; apply eq_bigr => i _; rewrite ffunE.
rewrite (@eq_bigr _ _ _ 'I_Nmax.+1 _ _ _ (fun i => `Pr[ X = i%:R ] * log (alp ^ i)))=>[|i _]; last first.
  by rewrite log_pow // [in RHS]mulRC -mulRA (mulRC _ (log alp)) mulRA.
rewrite /entropy addRC; move: oppRB; rewrite/Rminus; move<-.
rewrite -(oppRK (log _)) leR_oppl oppRK big_morph_oppR -big_split /=.
rewrite [X in _ <= X](_ : _ = \sum_(i < Nmax.+1)
      `Pr[ X = i%:R] *
      (log (`Pr[ X = i%:R ]) - log (alp ^ i))); last first.
  by apply: eq_bigr => i _; rewrite ffunE addR_opp -mulRBr.
rewrite -sub0R -(mul1R (0 - _)).
have pmf1' : \sum_(i < Nmax) `Pr[X = i.+1%:R] = 1.
  rewrite -PN_sum1 /=.
  under [in RHS]eq_bigr do rewrite ffunE.
  rewrite big_ord_recl -subR_eq subRR; apply/esym.
  rewrite /pr_eq; unlock.
  rewrite /Pr big1 // => i.
  rewrite inE; move/eqP =>  Xi_0.
  by move/gtR_eqF: (Xpos i); rewrite Xi_0 => /eqP.
rewrite -{1}(Log_1 2) -pmf1'.
have Pr_ge0' (i : nat) : 0 <= `Pr[ X = i%:R] by [].
have alpi_ge0 (i : nat) : 0 <= alp ^ i by exact/pow_le/ltRW.
pose h := mkPosFun Pr_ge0'.
pose g := mkPosFun alpi_ge0.
have dom_by_hg :  h `<< g.
  apply/dominatesP => i.
  rewrite /g /= => alp0.
  move: lt_0_alp.
  have -> : alp = 0 by move: (pow_nonzero alp i); tauto.
  by move/ltRR.
rewrite big_ord_recl [X in _ <= X + _](_ : _ = 0) ?add0R; last first.
  rewrite /pr_eq; unlock.
  rewrite /Pr.
  have -> : [set x | X x == INR 0] = set0; last by rewrite big_set0 mul0R.
  apply/setP => i; rewrite inE /= in_set0.
  by apply/negbTE; rewrite gtR_eqF //; exact: Xpos.
exact: (log_sum_inequality_ord_add1' Nmax dom_by_hg).
Qed.

Lemma le_entroPN_logeEX : `H PN <= log (`E X) + log (exp 1).
Proof.
move/Rle_lt_or_eq_dec : le_1_EX => [?|eq_EX_1]; last first.
  rewrite -eq_EX_1 /log Log_1 add0R.
  by move/esym/entroPN_0 : eq_EX_1 ->; apply: log_exp1_Rle_0.
have EX_1 : 0 < `E X  - 1 by rewrite subR_gt0.
have /eqP neq_EX1_0 : (`E X  + -1) != 0 by exact/gtR_eqF.
apply: (@leR_trans (`E X  * log (`E X ) - (`E X  - 1) * log((`E X ) -1))).
  exact: le_entroPN_logeEX'.
rewrite -{1}(Rplus_minus 1 (`E X)) mulRDl mul1R /Rminus -addRA leR_add2l.
rewrite -mulRN -mulRDr -(mul1R (log (exp 1))) -{3}(subRKC (`E X) 1) -oppRB.
rewrite (addR_opp (log (`E X))) -logDiv //; last exact EX_gt0.
by apply: div_diff_ub; [exact/ltRW |
  by move=> EX0; exfalso; move: EX0; apply/eqP/gtR_eqF/EX_gt0 |
  exact/ltRW/EX_gt0].
Qed.

End le_entroPN_logeEX.

Section v_scode_converse'_1tuple.

Variables (A : finType) (P : fdist A).
Variable f : A -> seq bool.
Local Notation "'Nmax'" := (Nmax f).
Let X : {RV P -> R} := (INR \o size \o f).
Local Notation "'PN'" := (PN P f).
Hypothesis f_uniq : uniquely_decodable f.

Definition Pf (i : seq bool) := if [ pick x | f x == i ] is Some x then P x else 0.

Lemma Rle0Pf i : 0 <= Pf i.
Proof.
rewrite /Pf.
case: pickP => [x _ | _ ]; [exact: FDist.ge0|exact: leRR].
Qed.

Lemma pmf1_Pf : \sum_(m < Nmax.+1) \sum_(a in {: m.-tuple bool}) Pf a = 1.
Proof.
move: (uniq_dec_inj f_uniq) => f_inj.
rewrite -(FDist.f1 P).
rewrite (partition_big (inordf (size \o f)) (fun i => i \in 'I_Nmax.+1)) //=.
apply: eq_bigr => i _.
rewrite (big_seq_tuple i f_inj (fdist_card_neq0 P)) /Pf=>[|x].
  apply: eq_big => x.
    apply/eqP/eqP => [H|<-]; first by apply: ord_inj; rewrite -H inordfE.
    by rewrite inordfE.
  by case: pickP => [? /eqP /f_inj ->| /(_ x)]; last rewrite eqxx.
case: pickP => [? /eqP <-| _ ]; first by rewrite codom_f.
by case: ifP.
Qed.

Definition Pf' (m : 'I_Nmax.+1) := [ffun a : m.-tuple bool =>  Pf a / (PN m)].

Lemma Rle0Pf' (m : 'I_Nmax.+1) :
  PN m <> 0 -> [forall a : m.-tuple bool, 0 <b= Pf' m a].
Proof.
move=> PNnon0; apply/forallP_leRP => a; rewrite /Pf'.
apply: (Rmult_le_reg_r (PN m)).
  move/eqP in PNnon0.
  by apply/ltRP; rewrite lt0R PNnon0 ffunE; exact/leRP.
rewrite mul0R ffunE /Rdiv -mulRA -Rinv_l_sym // mulR1 /Pf.
by case: pickP => [? _ // | _ ]; exact: leRR.
Qed.

Lemma pmf1_Pf' m : PN m <> 0 -> \sum_(a in {: m.-tuple bool}) Pf' m a = 1.
Proof.
move: (uniq_dec_inj f_uniq) => f_inj PNnon0.
rewrite /Pf'.
under eq_bigr do rewrite ffunE.
rewrite -big_distrl /=.
apply: (Rmult_eq_reg_r (PN m)) => //; rewrite mul1R.
rewrite -mulRA mulVR ?mulR1; last exact/eqP.
rewrite /= ffunE.
rewrite /pr_eq; unlock.
rewrite /Pr (eq_bigr (fun x => Pf (f x))) => [|a ain]; last first.
  rewrite /Pf.
  case:pickP; first by move =>x /eqP/ f_inj ->.
  by move/(_ a); rewrite eqxx.
rewrite (eq_bigl (fun x =>  size (f x) == m) _) => [|a]; last first.
  rewrite inE /X /=.
  by apply/eqP/eqP => [/INR_eq | ->].
rewrite (big_seq_tuple m f_inj (fdist_card_neq0 P)) /Pf => [//|i0].
case: pickP => // ?; first by move/eqP <-; rewrite codom_f.
by case: ifP.
Qed.

Lemma rsum_disjoints_set h : \sum_(a in [set : 'I_Nmax.+1]) h a =
 \sum_(a in [set x | PN x == 0]) h a + \sum_(a in [set x | PN x != 0]) h a.
Proof.
rewrite -big_union //; last first.
  rewrite disjoints_subset.
  rewrite (_ : ~: [set x | PN x == 0] = [set x | PN x != 0])//.
  by apply/setP => i; rewrite !inE.
by apply eq_bigl => i; rewrite !inE orbN.
Qed.

Lemma rewrite_HP_with_Pf : `H P =
 - \sum_(m in 'I_Nmax.+1) \sum_(a in {: m.-tuple bool}) Pf a * log (Pf a).
Proof.
move: (uniq_dec_inj f_uniq) => f_inj; congr (- _).
rewrite [in LHS](partition_big (inordf (size \o f)) (fun i => i \in 'I_Nmax.+1))//=.
apply: eq_bigr => i _.
rewrite (eq_bigr (fun i0 => Pf (f i0) * log (Pf (f i0)))) =>[|a]; last first.
  rewrite /Pf.
  case: (pickP _) => [x0 /eqP /f_inj->|] //.
  move/(_ a); by rewrite eqxx.
rewrite (eq_bigl (fun x => size (f x) == i) _) =>[|x]; last first.
  apply/eqP/eqP => [<-| H]; first by rewrite inordfE.
  by apply/ord_inj; rewrite inordfE.
rewrite (@big_seq_tuple _ i _ f_inj (fun a => Pf a * log (Pf a)) (fdist_card_neq0 P))//.
rewrite /Pf; move=> i0.
case: (pickP ) => // x; first by move/eqP <-; rewrite codom_f.
by case: ifP; rewrite mul0R.
Qed.

Lemma rewrite_HP_with_PN :
  `H P = - \sum_(m in [set x | PN x != 0]) PN m *
           (\sum_(a in {: m.-tuple bool}) Pf' m a * (log (Pf' m a) + log (PN m))).
Proof.
rewrite rewrite_HP_with_Pf; congr (- _).
rewrite (eq_bigl (fun m => m \in [set : 'I_Nmax.+1]) _) => [|?]; last first.
  by rewrite /= in_setT.
rewrite rsum_disjoints_set [Y in Y + _ = _]big1 ?add0R; last first.
  move=> /= i; rewrite inE.
  rewrite /pr_eq; unlock.
  rewrite /Pr ffunE /= => /eqP/psumR_eq0P => H.
  have {}H : forall j : A, j \in [set x | (size (f x))%:R == i%:R] -> P j = 0.
    by apply: H => ? ?; exact: FDist.ge0.
  rewrite big1 // => i0 _.
  rewrite {1}/Pf.
  case: pickP => [a /eqP fai0|]; last by rewrite mul0R.
  by rewrite H ?mul0R // inE fai0 size_tuple.
apply : eq_bigr => i.
rewrite inE /eqP => Pr_non0.
rewrite big_distrr /=.
apply : eq_bigr => i0 _.
rewrite ffunE.
rewrite {1}/Pf'.
rewrite ffunE.
rewrite [in RHS]mulRC /Rdiv -mulRA -mulRA.
case: (Req_dec (Pf i0) 0) => [->| /nesym/eqP Pfi0_non0]; first by rewrite !mul0R.
congr (_ * _).
rewrite mulRC -mulRA.
rewrite {2}/PN.
rewrite [in X in _ = _ * (_ * / X)]/= [in X in _ = _ * (_ * / X)]ffunE.
rewrite mulRV ?mulR1; last by rewrite /PN /= ffunE in Pr_non0.
rewrite /log LogM; last 2 first.
  apply/ltRP; rewrite lt0R eq_sym Pfi0_non0; apply/leRP.
  rewrite /Pf; case:pickP=>[? _ | ? ]; [exact: FDist.ge0 | exact/leRR].
  by apply/invR_gt0; rewrite -fdist_gt0.
rewrite LogV; last by rewrite -fdist_gt0.
by rewrite /PN /= ffunE -addRA Rplus_opp_l addR0.
Qed.

Lemma rewrite_HP_with_HPN : `H P =
  \sum_(m in [set x : 'I_Nmax.+1 | PN x != 0])
    PN m * (- \sum_(a in {: m.-tuple bool}) Pf' m a *
    (log ((Pf' m a)))) + `H PN.
Proof.
rewrite {2}/entropy.
rewrite (eq_bigl (fun m => m \in [set : 'I_Nmax.+1]) (fun x=> _ * log _))=>[|?]; last first.
  by rewrite /= in_setT.
rewrite rsum_disjoints_set [Y in  _ = _ + - (Y + _)]big1; last first.
  by move => /= i; rewrite inE /PN /= => /eqP ->; rewrite mul0R.
rewrite add0R rewrite_HP_with_PN !big_morph_oppR -big_split /=.
apply: eq_bigr => i.
rewrite inE => /eqP Pr_non0.
rewrite mulRN -oppRD; congr (- _).
rewrite -mulRDr. congr (_ * _).
rewrite -[Y in _ = _ + Y]mul1R -(pmf1_Pf' Pr_non0) big_distrl /= -big_split /=.
by under eq_bigr do rewrite mulRDr.
Qed.

Lemma apply_max_HPN : `H P <= `E X  + `H PN.
Proof.
have f_inj := uniq_dec_inj f_uniq.
rewrite rewrite_HP_with_HPN addRC (addRC _ (`H _)) leR_add2l EX_ord.
rewrite (eq_bigl (fun m => m \in [set : 'I_Nmax.+1]) (fun x=> INR x * _ ))=>[|?]; last first.
  by rewrite /= in_setT.
rewrite rsum_disjoints_set.
rewrite [Y in _ <= Y + _ ](_ :_ = 0).
  rewrite add0R; apply: leR_sumR => i.
  rewrite mulRC inE; move/eqP => H.
  apply/leR_wpmul2r; first by rewrite /PN /= ffunE.
  pose pmf_Pf' := mkPosFfun (Rle0Pf' H).
  have pmf1'_Pf' : \sum_(a in {: i.-tuple bool}) pmf_Pf' a == 1 :> R.
    by apply/eqP; apply: (pmf1_Pf' H).
  pose distPf := FDist.mk pmf1'_Pf'.
  move: (entropy_max distPf).
  rewrite card_tuple /= card_bool -natRexp log_pow (_ : INR 2 = 2) //.
  by rewrite /log Log_n // mulR1.
rewrite big1 //= => i.
rewrite inE /PN /= => /eqP ->.
by rewrite mulR0.
Qed.

Lemma apply_le_HN_logE_loge : `H P <= `E X  + log ((exp 1) * `E X).
Proof.
apply: (leR_trans apply_max_HPN).
rewrite leR_add2l mulRC /log (LogM _ (EX_gt0 P f_uniq) (exp_pos 1)).
exact: le_entroPN_logeEX f_uniq.
Qed.

End v_scode_converse'_1tuple.

Section v_scode_converse'_ntuple.

Variables (A : finType) (n : nat).
Variable f : encT A (seq bool) n.
Variable P : fdist A.
Hypothesis f_uniq : uniquely_decodable f.

Lemma converse_case1 : @E_leng_cw _ _ P f < n%:R * log #|A|%:R ->
`H (P `^ n) <= @E_leng_cw _ _ P f + log ((exp 1) * n%:R * log #|A|%:R).
Proof.
move=>H.
apply: (leR_trans (apply_le_HN_logE_loge (P `^ n) f_uniq)).
rewrite leR_add2l; apply: Log_increasing_le => //.
  apply/mulR_gt0; [exact/exp_pos | exact/EX_gt0].
rewrite -mulRA; apply: leR_wpmul2l; [exact/ltRW/exp_pos|exact/ltRW].
Qed.

Lemma converse_case2 : n%:R * log #|A|%:R <= @E_leng_cw _ _ P f ->
 `H (P `^ n) <= @E_leng_cw _ _ P f.
Proof.
move=> H; rewrite entropy_TupleFDist; apply: (leR_trans _ H).
apply leR_wpmul2l; [exact/leR0n | exact/entropy_max].
Qed.

End v_scode_converse'_ntuple.

Section Extend_encoder.

Variables (A : finType) (n m : nat).
Variable f : encT A (seq bool) n.
Variable P : fdist A.
Hypothesis f_uniq : uniquely_decodable f.
Hypothesis m_non0 : 0 <> m%:R.
Let fm (x : 'rV['rV[A]_n]_m) := extension f (tuple_of_row x).

Lemma fm_uniq : uniquely_decodable fm.
Proof.
pose m' := m.-1.
have mpos : m = m'.+1.
  rewrite prednK // -ltR_nat ltR_neqAle; split => //; exact/leR0n.
have: (@extension [finType of 'rV[A]_n] _ f) \o
      (flatten \o map (fun x => @tval m _ (tuple_of_row x))) =1
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
  exact/tuple_of_row_inj/eqP.
Qed.

Lemma ELC_TupleFDist : @E_leng_cw _ _ (P `^ n) fm = m%:R * @E_leng_cw _ _ P f.
Proof.
rewrite /E_leng_cw /=  /fm.
pose X := INR \o size \o f.
elim: m => [|m'].
  rewrite mul0R /Ex big1 // => i _.
  rewrite TupleFDist.zero ?mulR1.
  rewrite /comp_RV.
  rewrite [tuple_of_row]lock /= -lock.
  rewrite (_ : tuple_of_row i = [tuple]) //.
  apply: eq_from_tnth.
  by case; case.
elim: m' => [_ |m'' _ IH].
  rewrite mul1R.
  rewrite -[in RHS]E_cast_RV_tuplefdist1.
  apply: eq_bigr => i _.
  rewrite TupleFDist.one.
  congr (_ * _).
  rewrite /comp_RV.
  rewrite [tuple_of_row]lock /= -lock.
  rewrite (_ : tuple_of_row i = [tuple of [:: i ``_ ord0]]); last first.
    apply eq_from_tnth => a; by rewrite {a}(ord1 a) tnth_mktuple.
  by rewrite /extension /= cats0.
pose fm1 (x : 'rV['rV[A]_n]_(m''.+1)) := extension f (tuple_of_row x).
pose Xm1 := INR \o size \o fm1.
pose fm2 (x : 'rV['rV[A]_n]_(m''.+2)) := extension f (tuple_of_row x).
pose Xm2 := INR \o size \o fm2.
have X_Xm1_Xm2 : Xm2 \= X @+ Xm1.
  rewrite /Xm2 => x /=.
  rewrite -plus_INR plusE -size_cat.
  rewrite /fm2 /extension /fm1 /extension.
  rewrite [tuple_of_row]lock /= -lock.
  congr ((size _)%:R).
  rewrite {1}(_ : x = row_mx (\row_(i < 1) (x ``_ ord0)) (rbehead x)); last first.
    apply/matrixP => a b; by rewrite {}(ord1 a) row_mx_rbehead.
  rewrite (@tuple_of_row_row_mx _ _ _ (\row_(i < 1) (x ``_ ord0)) (rbehead x)).
  rewrite map_cat flatten_cat.
  congr (_ ++ _).
  rewrite (_ : tuple_of_row _ = [tuple of [:: x ``_ ord0]]); last first.
    by apply eq_from_tnth => i; rewrite {i}(ord1 i) /= tnth_mktuple mxE.
  by rewrite /= cats0.
rewrite (E_sum_2 X_Xm1_Xm2) S_INR mulRDl -IH addRC; congr (_ + _)%R.
  by rewrite /Xm1 -/fm1 /Ex TupleFDist.tail_of.
by rewrite -/X mul1R /Ex TupleFDist.head_of.
Qed.

End Extend_encoder.

Section v_scode_converse'.

Variables (A : finType) (P : fdist A).
Variable n : nat.
Variable f : encT A (seq bool) n.
Hypothesis f_uniq : uniquely_decodable f.

Let alp := exp 1 * log (INR #| 'rV[A]_n |).
Let m''' eps := Z.abs_nat (ceil (4 / (n%:R * eps * ln 2))).
Let m'' eps := maxn (m''' eps) 1.
Let m' eps := (maxn (Z.abs_nat (ceil (ln alp + n%:R * eps * ln 2))) (m'' eps))%:R.
Let m eps := Z.abs_nat (floor (exp (m' eps))).

Lemma mpos eps : 0 <> INR n -> 0 < (m eps)%:R.
Proof.
rewrite /m => nnon0.
rewrite (_ : 0 = INR 0)//; apply: lt_INR.
rewrite {1}(_ : 0%nat = Z.abs_nat 0)//; apply: Zabs_nat_lt; split => //.
apply: lt_0_IZR.
apply: (@ltR_trans (exp (m' eps) - 1)); last exact: (proj1 (floorP _)).
rewrite -(@ltR_add2r 1) addRC /Rdiv -addRA Rplus_opp_l 2!addR0 -{1}exp_0.
apply: exp_increasing.
rewrite (_ : 0 = INR 0) //; apply: lt_INR; apply: ltP.
apply: (@leq_trans (m'' eps)); last exact: leq_maxr.
by apply: (@leq_trans 1); last exact: leq_maxr.
Qed.

Lemma le_eps eps : 0 <> n%:R -> 1 <= n%:R * log #|A|%:R -> 0 < eps ->
  log ((m eps)%:R * alp) * / (m eps)%:R * / n%:R <= eps.
Proof.
move=> nnon0 eps_pos cardA_non1.
pose x := m' eps.
pose Y := eps * INR n * ln 2.
have npos : 0 < INR n.
  by case/Rdichotomy : nnon0 => //; rewrite (_ : 0 = INR 0)// => /INR_lt/ltP.
have xpos : 0 < x.
  rewrite (_ : 0 = INR 0)//; apply: lt_INR; apply/leP.
  apply: (@leq_trans (m'' eps)); last exact: leq_maxr.
  by apply: (@leq_trans 1); last exact: leq_maxr.
have mpos': (0 < floor (exp x))%Z.
  apply/lt_IZR/(@ltR_trans (exp x - 1)); last exact: (proj1 (floorP _)).
  rewrite -(@ltR_add2r 1) addRC /Rminus -addRA Rplus_opp_l 2!addR0 -exp_0.
  exact: exp_increasing.
have le_1_alp : 1 <= alp.
  rewrite /alp -(mulR1 1).
  apply/leR_pmul => //.
    rewrite mulR1; apply: (@leR_trans 2); last exact: leR2e.
    by rewrite (_ : 1 = 1%:R) // (_ : 2 = 2%:R) // leR_nat.
  rewrite card_matrix -natRexp mul1n log_pow //.
  by rewrite (_ : 0 = INR 0) //; apply/lt_INR/ltP/fdist_card_neq0.
have alppos : 0 < alp by exact: (@ltR_leR_trans 1).
have Ypos : 0 < Y by apply/mulR_gt0 => //; apply/mulR_gt0.
apply: (Rmult_le_reg_r (INR (m eps) * INR n)).
  by apply: mulR_gt0 => //; apply/mpos.
rewrite -mulRA (mulRC (/ INR n) _ ) -mulRA -mulRA -Rinv_r_sym; last exact: nesym.
rewrite mulR1 mulVR ?mulR1; last exact/gtR_eqF/mpos/eqP/ltR_eqF.
apply: (@leR_trans ((x ^ 2 / 2 - 1) * eps * (INR n))); last first.
  rewrite -mulRA mulRC -mulRA; apply: leR_wpmul2l; first exact: ltRW.
  rewrite mulRC; apply: leR_wpmul2r; first exact/ltRW.
  apply: (@leR_trans (exp x - 1)).
    rewrite leR_subl_addr subRK (_ : 2 = INR 2 `!)//; exact/(exp_lb 2)/pos_INR.
  rewrite INR_Zabs_nat; last exact/le_IZR/ltRW/IZR_lt.
  exact/ltRW/(proj1 (floorP _)).
rewrite INR_Zabs_nat; last exact/le_IZR/Rlt_le/IZR_lt.
rewrite {1}/log LogM//; last exact: IZR_lt.
rewrite -/(log _).
rewrite -(leR_pmul2r ln2_gt0).
rewrite mulRDl /Log/Rdiv -(mulRA (ln alp)) (mulVR _ ln2_neq0).
rewrite mulR1 -(mulRA _ (/ ln 2) _) (mulVR _ ln2_neq0).
apply: (@leR_trans (x + ln alp)).
  rewrite leR_add2r ?mulR1 -(ln_exp x).
  apply: ln_increasing_le; last exact: (proj2 (floorP _)).
  apply: (@ltR_trans (exp x - 1)); last exact: proj1 (floorP _).
  rewrite subR_gt0 -exp_0; exact: exp_increasing.
apply: (@leR_trans (2 * x - (eps * INR n * ln 2))).
  rewrite double /Rminus -addRA leR_add2l addR_opp leR_subr_addr (mulRC eps).
  apply: (@leR_trans (IZR (ceil (ln alp + n%:R * eps * ln 2)))); first exact: proj1 (ceilP _).
  rewrite -INR_Zabs_nat; first exact/le_INR/leP/leq_maxl.
  apply: le_IZR.
  apply: (@leR_trans (ln alp + Y)); last first.
    by rewrite /Y (mulRC eps); exact: proj1 (ceilP _).
  apply/addR_ge0; last exact/ltRW.
  by rewrite -(ln_exp 0) exp_0; exact: ln_increasing_le.
rewrite -(mulRA _ eps) -(mulRA _ (eps * INR n)).
rewrite mulRBl mul1R leR_add2r.
apply: (Rmult_le_reg_r (/ Y * 2 * / x)).
  apply/mulR_gt0; [apply/mulR_gt0 => //; exact/invR_gt0|exact/invR_gt0].
rewrite mulRC -mulRA (mulRC (/ x)) -mulRA -mulRA mulRV; last exact/gtR_eqF.
rewrite mulR1 mulRC mulRA mulRA (mulRC _ (/x)) /= mulR1 mulRA (mulRC _ 2).
rewrite -(mulRA _ Y) mulRV ?mulR1; last exact/gtR_eqF.
rewrite (mulRC 2) !mulRA -(mulRA _ _ 2) !mulVR // ?(mul1R,mulR1); last 2 first.
  exact/eqP.
  exact/gtR_eqF.
apply: (@leR_trans (m'' eps)%:R); last exact/le_INR/leP/leq_maxr.
apply: (@leR_trans (m''' eps)%:R); last exact/le_INR/leP/leq_maxl.
rewrite INR_Zabs_nat.
  apply: (@leR_trans ((4 * / (INR n * eps * ln 2)))); last exact: proj1 (ceilP _).
  rewrite (mulRC n%:R); exact/leRR.
apply: le_IZR.
apply: (@leR_trans ((4 * / (INR n * eps * ln 2)))); last exact: proj1 (ceilP _).
apply: Rle_mult_inv_pos; first exact: ltRW (@mulR_gt0 2 2 _ _).
by rewrite (mulRC n%:R).
Qed.

Theorem v_scode_converse' : n%:R * `H P <= @E_leng_cw _ _ P f.
Proof.
case: (Req_dec 0 (INR n))=>[<-|nnon0].
  by rewrite mul0R; apply/ltRW/(EX_gt0 (P `^ n) f_uniq).
have npos : 0 < n%:R by rewrite (_ : 0 = INR 0) // ltR_neqAle leR_nat leq0n.
rewrite -(@leR_pmul2r (/ n%:R)); last exact/invR_gt0.
rewrite (mulRC (INR n)) -mulRA mulRV ?mulR1; last exact/gtR_eqF.
apply: le_epsilon => eps eps0.
pose fm (x : 'rV['rV[A]_n]_((m eps))) := extension f (tuple_of_row x).
case: (Rle_or_lt ((m eps)%:R * (log #| 'rV[A]_n |%:R)) (@E_leng_cw _ _ (P `^ n) fm)).
  move/(@converse_case2 _ _ fm (P `^ n)).
  rewrite !entropy_TupleFDist ELC_TupleFDist.
  rewrite (leR_pmul2l (mpos eps nnon0)) => H.
  apply: (@leR_trans (@E_leng_cw _ _ P f / n%:R)) => //.
    by rewrite leR_pdivl_mulr // mulRC.
  rewrite leR_addl; exact/ltRW.
have mnon0 : (m eps)%:R <> 0 by exact/eqP/gtR_eqF/mpos.
move => case2.
move: (@converse_case1 _ _ _ (P `^ n)
  (fm_uniq f_uniq (Rlt_not_eq _ _ (mpos eps nnon0))) case2).
rewrite !entropy_TupleFDist ELC_TupleFDist -!mulRA mulRA.
move/(Rmult_le_compat_r _ _ _  (Rlt_le _ _ (Rinv_0_lt_compat _ (mpos eps nnon0)))).
rewrite -mulRA -mulRA mulRC mulRA -mulRA mulVR ?mulR1; last exact/eqP.
rewrite mulRDl (mulRC (m eps)%:R) -mulRA ?mulRV ?mulR1; last exact/eqP.
move/(Rmult_le_compat_r _ _ _  (Rlt_le _ _ (Rinv_0_lt_compat _ npos))).
rewrite (mulRC (INR n)) -mulRA mulRV ?mulR1; last exact/gtR_eqF.
rewrite mulRDl.
move/leR_trans; apply.
rewrite leR_add2l.
rewrite mulRA (mulRC (exp 1)) -(mulRA (m eps)%:R).
apply le_eps => //.
move:case2.
rewrite ELC_TupleFDist mulRC (mulRC (m eps)%:R) card_matrix mul1n -natRexp log_pow; last first.
  by rewrite (_ : 0 = INR 0) //; apply/lt_INR/ltP/fdist_card_neq0.
move/(ltR_pmul2r (mpos eps nnon0)) => /ltRW.
apply: leR_trans; exact/le_1_EX.
Qed.

End v_scode_converse'.

Section v_scode_converse.

Variables (A : finType) (P : fdist A) (n : nat).
Variable f : encT A (seq bool) n.
Hypothesis f_uniq : uniquely_decodable f.

Theorem v_scode_converse : n%:R * `H P <= @E_leng_cw _ _ P f.
Proof. exact: v_scode_converse'. Qed.

End v_scode_converse.
