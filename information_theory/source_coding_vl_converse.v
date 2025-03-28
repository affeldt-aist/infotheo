(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint matrix.
From mathcomp Require Import archimedean lra ring.
From mathcomp Require Import Rstruct reals sequences exp.
Require Import ssr_ext ssralg_ext bigop_ext realType_ext realType_ln.
Require Import fdist proba entropy divergence log_sum source_code.

(**md**************************************************************************)
(* # Source coding theorem (variable length, converse part)                   *)
(*                                                                            *)
(* Documented in:                                                             *)
(* - Ryosuke Obi. In MI Lecture Note Workshop on Theorem proving and provers  *)
(*   for reliable theory and implementations (TPP2014), Kyushu University,    *)
(*   December 3--5, 2014, volume 61, pages 76--78, Dec 2014                   *)
(*                                                                            *)
(* Original source file from R. Obi, quickly patched to compile with InfoTheo *)
(* [2019-08-19] and simplified afterwards.                                    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope tuple_ext_scope.
Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope divergence_scope.
Local Open Scope ring_scope.

Import Order.POrderTheory GRing.Theory Num.Theory Num.Def Order.TotalTheory.

(* TODO: move to log_sum? *)
Section log_sum_ord.
Let R := Rdefinitions.R.
Variable n : nat.
Variable f g : nat -> R.
Hypothesis (f0 : forall n, 0 <= f n) (g0 : forall n, 0 <= g n).
Hypothesis f_dom_by_g : f `<< g.

Lemma log_sum_inequality_ord_add1 :
  (\sum_(i < n) f i.+1) *
  log ((\sum_(i < n) f i.+1) / (\sum_(i < n) g i.+1)) <=
  \sum_(i < n) f i.+1 * log (f i.+1 / g i.+1).
Proof.
have Rle0f_1 (x : 'I_n) : 0 <= f x.+1 by exact: f0.
have Rle0g_1 (x : 'I_n) : 0 <= g x.+1 by exact: g0.
have newRle0f_1 : [forall x : 'I_n, 0 <= [ffun x : 'I_n => f x.+1] x].
  by apply/forallP => //= ?/=; rewrite ffunE.
have newRle0g_1 : [forall x : 'I_n, 0 <= [ffun x : 'I_n => g x.+1] x].
  by apply/forallP => //= ?/=; rewrite ffunE.
have f_dom_by_g1 : [ffun x0 : 'I_n => f x0.+1] `<< [ffun x0 : 'I_n => g x0.+1].
  apply/dominatesP => a; move/dominatesP : f_dom_by_g.
  by rewrite /= !ffunE; exact.
have H h :
  \sum_(a | a \in [set: 'I_n]) h a.+1 = \sum_(a | a \in 'I_n) h a.+1 :> R.
  by under eq_bigl do rewrite in_setT.
rewrite -!H -(H (fun i => f i * log (f i / g i))).
move/forallP in newRle0f_1.
move/forallP in newRle0g_1.
have := @log_sum R _ [set: 'I_n] [ffun x0 : 'I_n => f x0.+1]
  [ffun x0 : 'I_n => g x0.+1] newRle0f_1 newRle0g_1 f_dom_by_g1.
under eq_bigr do rewrite ffunE.
under [in X in _ * log (_ / X) <= _ -> _]eq_bigr do rewrite ffunE.
under [in X in _ <= X  -> _]eq_bigr do rewrite ffunE.
move/le_trans; apply.
apply/eqW.
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
    by apply/sumr_ge0 => ? _.
  rewrite le_eqVlt => /predU1P[<-|Hf].
    by rewrite !mul0r.
  have : 0 <= \sum_(i in 'I_n) g i.+1 by exact/sumr_ge0.
  rewrite le_eqVlt => /predU1P[H|Hg]; last first.
    by rewrite logM// ?invr_gt0//; congr *%R; rewrite logV.
  have eq_g_0 : forall i : 'I_n, 0 = g i.+1.
    by move/esym/psumr_eq0P : H => H i; rewrite H//.
  have : 0 = \sum_(i < n) f i.+1.
    apply/esym/eqP; rewrite psumr_eq0 //.
    apply/allP => i _; apply/eqP.
    by move/dominatesP : f_dom_by_g; apply; rewrite -eq_g_0.
  by move => tmp; move: Hf; rewrite -tmp ltxx.
apply: eq_bigr => i _.
have := (f0 i.+1); rewrite le_eqVlt => /predU1P[<-|fpos]; first by rewrite !mul0r.
have := (g0 i.+1); rewrite le_eqVlt => /predU1P[|].
  clear g0.
  move/esym => g0; move/dominatesP : f_dom_by_g => /(_ _ g0) ->.
  by rewrite !mul0r.
by move=>gpos; rewrite logM ?invr_gt0// logV.
Qed.

End log_sum_ord.

Section Ordinal.
Variables (T : finType) (f : T -> nat).

Definition inordf t := inord (f t) : 'I_(\max_t f t).+1.

Lemma inordfE : (fun t : T => nat_of_ord (inordf t)) =1 f.
Proof.
move=>t.
apply: inordK; by apply: leq_bigmax.
Qed.

End Ordinal.

Section Bigop_Lemma.
Let R := Rdefinitions.R.
Variable A : finType.
Variable n : nat.
Variable f : A -> seq bool.
Hypothesis f_inj : injective f.

Let big_seq_tuple' (F : seq bool -> R) : (0 < #|A|)%N ->
  \sum_(a | size (f a) == n) F (f a) =
  \sum_(i : n.-tuple bool | tval i \in codom f) F i.
Proof.
move Hpick : [pick x | x \in [set: A] ] => p Anon0.
move: Hpick; case: (pickP _) => [defaultA _ _ | abs]; last first.
  exfalso.
  move: Anon0.
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
   + apply/esym/eq_big => i; last by move/codomP => [a fa]; rewrite /h fa H.
     apply/idP/andP.
     * move/codomP => [a fa]. rewrite /h fa H.
       split; first by rewrite -fa size_tuple eqxx.
       by rewrite /h' -fa valKd.
     * rewrite /h /h' => [] [sizefhi /eqP <-]; rewrite insubdK //.
       exact: codom_f.
Qed.

Lemma big_seq_tuple (F : seq bool -> R) : (0 < #|A|)%N ->
  (forall i, F i = if i \in codom f then F i else 0)->
  \sum_(i in {: n.-tuple bool}) F i = \sum_(a | size (f a) == n) F (f a).
Proof.
move=> Anon0 Fi0.
rewrite big_seq_tuple' //.
rewrite (eq_bigr (fun a => if (tval a \in codom f) then F a else 0)) => [|i _].
  by rewrite -big_mkcondr.
by rewrite {1}Fi0.
Qed.

End Bigop_Lemma.

Local Open Scope vec_ext_scope.

Section Entropy_lemma.
Variables (A : finType) (P : {fdist A}) (n : nat).

(* TODO: move to entropy.v *)
Lemma entropy_TupleFDist : `H (P `^ n)%fdist = n%:R * `H P.
Proof.
elim:n=>[|n0 IH].
  rewrite mul0r /entropy /= big1 ?oppr0 // => i _.
  by rewrite fdist_rV0 log1 mulr0.
rewrite -natr1 mulrDl mul1r -IH /entropy -(big_rV_cons_behead _ xpredT xpredT)/=.
rewrite /= -opprD; congr (- _).
rewrite [LHS](_ :_ = \sum_(i | i \in A) P i * log (P i) *
    (\sum_(j in 'rV[A]_n0) (\prod_(i0 < n0) P j ``_ i0)) +
     \sum_(i | i \in A) P i * \sum_(j in 'rV[A]_n0)
    (\prod_(i0 < n0) P j ``_ i0) * log (\prod_(i0 < n0) P j ``_ i0)); last first.
  rewrite -big_split /=; apply: eq_bigr => i _.
  rewrite -mulrA -mulrDr (mulrC (log (P i))) (big_distrl (log (P i)) _ _) /=.
  rewrite -big_split /= big_distrr /=.
  apply: eq_bigr => i0 _.
  rewrite fdist_rVE.
  rewrite big_ord_recl (_ : _ ``_ ord0 = i); last first.
    by rewrite mxE; case: splitP => // j Hj; rewrite mxE.
  rewrite -mulrA.
  case/RleP : (FDist.ge0 P i) => [/RltP pi_pos| <-]; last by rewrite !mul0r.
  congr (P i * _).
  rewrite -mulrDr.
  rewrite (@eq_bigr _ _ _ _ _ _
      (fun x => P ((row_mx (\row_(_ < 1) i) i0) ``_ (lift ord0 x)))
      (fun x => P i0 ``_ x)) => [|i1 _]; last first.
    congr (P _).
    rewrite mxE.
    case: splitP => j; first by rewrite (ord1 j).
    by rewrite lift0 add1n; case=> /eqP /val_eqP ->.
  have [<-|rmul_non0] := eqVneq 0 (\prod_(i' < n0) P i0 ``_ i').
    by rewrite !mul0r.
  have rmul_pos : 0 < \prod_(i1<n0) P i0 ``_ i1.
    by rewrite lt0r eq_sym rmul_non0; apply/prodr_ge0 => ?.
  by rewrite logM//.
rewrite (_ : \sum_(j in 'rV_n0) _ = 1); last first.
  rewrite -[RHS](FDist.f1 (P `^ n0)%fdist).
  by apply eq_bigr => i _; rewrite fdist_rVE.
rewrite -big_distrl /= mulr1 [in RHS]addrC; congr +%R.
rewrite -big_distrl /= FDist.f1 mul1r; apply eq_bigr => i _.
by rewrite fdist_rVE.
Qed.

End Entropy_lemma.

Section le_entroPN_logeEX.
Let R := Rdefinitions.R.

Variable (A : finType) (P : {fdist A}) (f : A -> seq bool).
Let X : {RV P -> R} := (fun x => x%:R) \o size \o f.
Definition Nmax := \max_(a in A) size (f a).
Hypothesis f_uniq : uniquely_decodable f.

Let Xnon0 x : 0 <> X x.
Proof.
rewrite /X /=; have [/eqP|/eqP//] := eqVneq (0:R) (size (f x))%:R.
rewrite (_ : 0 = 0%:R)// eqr_nat => /eqP.
move/esym/size0nil => fx_nil.
move: (@f_uniq [::] ([:: x])).
by rewrite /extension /= fx_nil cat0s => /(_ erefl).
Qed.

(* TODO: rename *)
Lemma Xpos a : 0 < X a.
Proof.
by rewrite lt_neqAle eq_sym ler0n andbT; apply/eqP/nesym/Xnon0.
Qed.

Let PN_ge0 (i : 'I_Nmax.+1) : 0 <= [ffun x : 'I__ => `Pr[ X = x%:R]] i.
Proof. by rewrite ffunE. Qed.

Lemma PN_sum1 :
  \sum_(i < Nmax.+1) [ffun x : 'I__ => `Pr[ X = x%:R] ] i = 1.
Proof.
rewrite -(FDist.f1 P).
rewrite [in RHS](partition_big (inordf (size \o f)) (fun i => i \in 'I_Nmax.+1)) //=.
apply: eq_bigr => i _; rewrite ffunE.
rewrite /pr_eq; unlock.
apply: eq_bigl => i0.
rewrite /= inE.
apply/eqP/eqP=> [|<-]; last first.
  by rewrite inordfE /X /= FDist.f1.
rewrite FDist.f1 /X /= => /eqP; rewrite eqr_nat => /eqP H.
apply/val_inj => /=.
by rewrite inordfE.
Qed.

Definition PN := FDist.make PN_ge0 PN_sum1.

Lemma EX_ord : `E X = \sum_(i < Nmax.+1) i%:R * PN i.
Proof.
rewrite /Ex (partition_big (inordf (size \o f)) (fun i => i \in 'I_Nmax.+1)) //=.
apply : eq_bigr=> i _.
rewrite /pr_eq; unlock.
rewrite /Pr ffunE mulrC big_distrl /=.
under eq_bigr do rewrite mulrC.
apply: congr_big=>[//| x| x]; last by move/eqP<-; rewrite inordfE.
rewrite inE; apply/eqP/eqP=> [<-|].
  by rewrite inordfE /X/=.
rewrite /X /= => /eqP; rewrite eqr_nat => /eqP H.
by apply: ord_inj; rewrite -H inordfE.
Qed.

Lemma le_1_EX : 1 <= `E X.
Proof.
rewrite -(FDist.f1 P); apply: ler_sum => i _.
rewrite -{1}(mul1r (P i)).
apply ler_wpM2r; first exact/FDist.ge0.
by move: (Xpos i); rewrite (_ : 1 = 1%:R) //= (_ : 0 = 0%:R) // ltr_nat ler_nat.
Qed.

Lemma EX_gt0 : 0 < `E X. Proof. exact: lt_le_trans le_1_EX. Qed.

Lemma entroPN_0 : `E X = 1 -> `H PN = 0.
Proof.
move => EX_1.
have eq_0_P : forall a, X a <> 1 -> 0 = P a.
  move: EX_1.
  rewrite -{1}(FDist.f1 P) => EX1 a Xnon1.
  have /leR_sumR_eq H (i : A) : i \in A -> P i <= (size (f i))%:R * P i.
    move=> _; rewrite -{1}(mul1r ( P i)).
    apply/ler_wpM2r; first exact/FDist.ge0.
    by move: (Xpos i); rewrite (_ : 1 = 1%:R) //= (_ : 0 = 0%:R) // ltr_nat ler_nat.
  have [//|] := eqVneq (P a) 0.
  have : (size (f a))%:R * P a = P a by rewrite (H EX1 a).
  rewrite -{2}(mul1r (P a)) => + Pa0.
  move=> /(congr1 (fun x => x * (P a)^-1)).
  by rewrite -!mulrA divff// !mulr1.
rewrite /entropy.
apply/eqP; rewrite oppr_eq0; apply/eqP.
rewrite big1//= => i _.
rewrite /pr_eq; unlock.
rewrite /Pr ffunE.
have [->|neq0] := eqVneq i%:R (1:R).
  rewrite [X in _ * log X = _](_ : _ = 1); first by rewrite log1 mulr0.
  rewrite -{2}(FDist.f1 P).
  rewrite [in RHS](bigID (fun a => a \in [set x | (size (f x))%:R == (1:R)])) /=.
  rewrite [X in _ = _ + X](_ : _ = 0).
    by rewrite addr0.
  rewrite big1// => j.
  by rewrite inE => /eqP/eq_0_P.
rewrite [X in X * _ = _](_ : _ = 0); first by rewrite mul0r.
rewrite big1 // => j.
rewrite inE; move/eqP => eq_Xj_i.
by move: neq0; rewrite -eq_Xj_i => /eqP/eq_0_P.
Qed.

Lemma le_entroPN_logeEX' :
  `H PN <= `E X  * log (`E X) - (`E X  - 1) * log((`E X ) - 1).
Proof.
move: le_1_EX; rewrite le_eqVlt => /predU1P[eq_E_0|lt_EX_1].
  rewrite -eq_E_0 log1 mulr0 subrr mul0r subrr.
  by move/esym/entroPN_0 : eq_E_0 ->.
have lt_0_EX_1 : 0 < `E X - 1 by rewrite subr_gt0.
pose alp := (`E X - 1) / `E X .
have gt_alp_1 : alp < 1.
  rewrite -(ltr_pM2r EX_gt0) // mul1r.
  rewrite /alp -mulrA mulVf ?mulr1; last first.
    by rewrite gt_eqF// (le_lt_trans _ lt_EX_1).
  by rewrite -ltrBrDl subrr -ltrNl oppr0.
have lt_0_alp : 0 < alp.
  by rewrite /alp divr_gt0// EX_gt0.
have EX_pos' : 0 < 1 - (`E X  - 1) / `E X .
  rewrite mulrBl divff//; last first.
    by rewrite gt_eqF// (le_lt_trans _ lt_EX_1).
  by rewrite mul1r opprB addrC subrK invr_gt0// EX_gt0.
have max_pos: (0 < \max_(a in A) size (f a))%N.
  move/card_gt0P : (fdist_card_neq0 P) => [a _].
  apply: (bigop.bigmax_sup a) (* TODO: name conflict *)=> //.
  by move: (Xpos a); rewrite /X /= ltr0n.
rewrite [X in _ <= X](_ :_ = log ( alp / (1 - alp)) - (log alp) * `E X);
    last first.
  rewrite /alp !logM //; last 2 first.
    by rewrite invr_gt0; exact/EX_gt0.
    by rewrite invr_gt0.
  rewrite ![in RHS](logV EX_gt0) //.
  rewrite [in X in _ = _ - X]mulrDl.
  rewrite [in RHS]addrC (addrC _ (- log (`E X ) * `E X )) opprD.
  rewrite [in RHS]mulNr opprK -addrA.
  rewrite [in LHS]mulrC; congr (_ + _).
  rewrite [in LHS]mulrDl mulrC opprD mulN1r opprK; congr (_ + _).
  rewrite -[in RHS]addrA -[LHS]addr0; congr (_ + _).
  rewrite mulrDl mulfV; last first.
    by rewrite gt_eqF// EX_gt0.
  by rewrite mulN1r opprB addrCA subrr addr0 invrK addrC subrr.
apply: (@le_trans _ _ (log (alp * (1 - (alp ^ (\max_(a | a \in A) size (f a))))
                               / (1 - alp)) - log alp * `E X ) _); last first.
  rewrite lerD2r.
  rewrite ler_log ?posrE//; last 2 first.
    apply/mulr_gt0; last by rewrite invr_gt0.
    rewrite mulr_gt0// subr_gt0.
    have : 0 <= alp < 1 by apply/andP; split => //; exact/ltW.
    move/andP => [alp0 alp1].
    by rewrite -exprnP expr_lt1.
    by rewrite divr_gt0//.
  rewrite -mulrA (ler_wpM2l (ltW lt_0_alp))//.
  rewrite -{2}(mul1r ((1 - alp)^-1)).
  rewrite ler_wpM2r ?invr_ge0 ?subr_ge0//.
    exact: ltW.
  rewrite -lerBrDl subrr lerNl oppr0.
  by rewrite -exprnP exprn_ge0// ltW.
rewrite EX_ord -sum_exprz; last by rewrite lt_eqF.
rewrite mulrC.
rewrite big_distrl//=.
rewrite -(@lerD2r _ (\sum_(i < Nmax.+1) i%:R * `Pr[ X = i%:R ] * log alp)).
rewrite -addrA addrC (_ : - _ + _ = 0) ?addr0; last first.
  apply/eqP; rewrite addrC subr_eq0; apply/eqP.
  by apply eq_bigr => i _; rewrite ffunE.
rewrite (@eq_bigr _ _ _ 'I_Nmax.+1 _ _ _ (fun i => `Pr[ X = i%:R ] * log (alp ^ i)))=>[|i _]; last first.
  by rewrite log_exprz // [in RHS]mulrC -mulrA (mulrC _ (log alp)) mulrA.
rewrite /entropy/=.
rewrite -[leLHS]opprB.
rewrite -(opprK (log _)) lerNl opprK big_morph_oppr -big_split /=.
rewrite [X in _ <= X](_ : _ = \sum_(i < Nmax.+1)
      `Pr[ X = i%:R] *
      (log (`Pr[ X = i%:R ]) - log (alp ^ i))); last first.
  by apply: eq_bigr => i _; rewrite ffunE -mulrBr.
rewrite -sub0r -(mul1r (0 - _)).
have pmf1' : \sum_(i < Nmax) `Pr[X = i.+1%:R] = 1.
  rewrite -[RHS]PN_sum1 /=.
  under [in RHS]eq_bigr do rewrite ffunE.
  rewrite [RHS]big_ord_recl.
  apply/eqP; rewrite -subr_eq; apply/eqP.
  rewrite [LHS](_ : _ = 0); last first.
    by apply/eqP; rewrite GRing.subr_eq0; apply/eqP/eq_bigr => i _ /=.
  apply/esym.
  rewrite /pr_eq; unlock.
  rewrite /Pr big1 // => i.
  rewrite inE; move/eqP =>  Xi_0.
  have := Xpos i.
  by rewrite Xi_0 ltxx.
rewrite -{1}(log1).
rewrite -{1 2}[in leLHS]pmf1'.
have Pr_ge0' (i : nat) : 0 <= `Pr[ X = i%:R] by [].
have alpi_ge0 (i : nat) : 0 <= alp ^ i.
  by rewrite -exprnP exprn_ge0// ltW.
pose h := [ffun i : 'I_Nmax.+1 => `Pr[ X = i%:R ]].
pose g := [ffun i : 'I_Nmax.+1 => alp ^ i].
have dom_by_hg : (fun i : nat => `Pr[ X = i%:R ]) `<< (fun i : nat => alp ^ i).
  apply/dominatesP => i.
  rewrite /g /= => alp0.
  move: lt_0_alp.
  have -> : alp = 0.
    move: alp0.
    rewrite -exprnP => /eqP.
    by rewrite expf_eq0 => /andP[_ /eqP].
  by rewrite ltxx.
rewrite big_ord_recl [X in _ <= X + _](_ : _ = 0) ?add0r; last first.
  rewrite /pr_eq; unlock.
  rewrite /Pr.
  have -> : [set x | X x == 0] = set0; last by rewrite big_set0 mul0r.
  apply/setP => i; rewrite inE /= in_set0.
  by apply/negbTE; rewrite gt_eqF //; exact: Xpos.
have := log_sum_inequality_ord_add1' Nmax Pr_ge0' alpi_ge0.
by apply.
Qed.

Lemma le_entroPN_logeEX : `H PN <= log (`E X) + log (expR 1).
Proof.
move: le_1_EX; rewrite le_eqVlt => /predU1P[eq_EX_1|?].
  rewrite -eq_EX_1 log1 add0r.
  by move/esym/entroPN_0 : eq_EX_1 ->; apply: log_exp1_Rle_0.
have EX_1 : 0 < `E X  - 1 by rewrite subr_gt0.
have /eqP neq_EX1_0 : (`E X  + -1) != 0 by rewrite gt_eqF.
apply: (@le_trans _ _ (`E X  * log (`E X ) - (`E X  - 1) * log ((`E X) - 1))).
  exact: le_entroPN_logeEX'.
rewrite -{1}(_ : 1 + (`E X - 1) = `E X); last first.
  by rewrite addrCA subrr addr0.
rewrite mulrDl mul1r.
rewrite -addrA.
rewrite lerD2l.
rewrite -mulrN.
rewrite -mulrDr.
rewrite -(mul1r (log (expR 1))).
rewrite -{3}(_ : (`E X + (1 - `E X)) = 1); last first.
  by rewrite addrCA subrr addr0.
rewrite -opprB.
rewrite -logV; last first.
  by rewrite opprB subr_gt0.
rewrite -logM; last 2 first.
  by rewrite (lt_trans (@ltr01 _)).
  by rewrite invr_gt0 ltrNr oppr0 subr_lt0.
rewrite -[in leRHS](opprK ((1 - `E X))).
apply: div_diff_ub.
- by rewrite opprB subr_ge0 ltW.
- move=> EX0.
  move: EX_1.
  by rewrite EX0 sub0r -ltrNr oppr0 ltNge ler01.
by rewrite (le_trans (@ler01 _) (ltW _)).
Qed.

End le_entroPN_logeEX.

Section v_scode_converse'_1tuple.
Let R := Rdefinitions.R.

Variables (A : finType) (P : {fdist A}).
Variable f : A -> seq bool.
Local Notation "'Nmax'" := (Nmax f).
Let X : {RV P -> R} := ((fun x => x%:R) \o size \o f).
Local Notation "'PN'" := (PN P f).
Hypothesis f_uniq : uniquely_decodable f.

Definition Pf (i : seq bool) := if [ pick x | f x == i ] is Some x then P x else 0.

Lemma Rle0Pf i : 0 <= Pf i.
Proof.
rewrite /Pf.
by case: pickP => [x _ | _ ]; [exact/FDist.ge0|].
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
  PN m <> 0 -> [forall a : m.-tuple bool, 0 <= Pf' m a].
Proof.
move=> PNnon0; apply/forallP => /=.
move=> a; rewrite /Pf'.
rewrite ffunE.
rewrite divr_ge0//.
rewrite /Pf.
by case: pickP.
Qed.

Lemma pmf1_Pf' m : PN m <> 0 -> \sum_(a in {: m.-tuple bool}) Pf' m a = 1.
Proof.
move: (uniq_dec_inj f_uniq) => f_inj PNnon0.
rewrite /Pf'.
under eq_bigr do rewrite ffunE.
rewrite -big_distrl.
apply: (@mulIf _ (PN m)).
  exact/eqP.
rewrite -mulrA mulVf ?mulr1 ?mul1r; last first.
  exact/eqP.
rewrite /= ffunE.
rewrite /pr_eq; unlock.
rewrite /Pr (eq_bigr (fun x => Pf (f x))) => [|a ain]; last first.
  rewrite /Pf.
  case:pickP; first by move =>x /eqP/ f_inj ->.
  by move/(_ a); rewrite eqxx.
rewrite (eq_bigl (fun x =>  size (f x) == m) _) => [|a]; last first.
  by rewrite inE /X /= eqr_nat.
rewrite (big_seq_tuple m f_inj (fdist_card_neq0 P)) /Pf => [//|i0].
case: pickP => // ?; first by move/eqP <-; rewrite codom_f.
by case: ifP.
Qed.

Lemma rsum_disjoints_set h : \sum_(a in [set : 'I_Nmax.+1]) h a =
 \sum_(a in [set x | PN x == 0]) h a + \sum_(a in [set x | PN x != 0]) h a :> R.
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
by case: ifP; rewrite mul0r.
Qed.

Lemma rewrite_HP_with_PN :
  `H P = - \sum_(m in [set x | PN x != 0]) PN m *
           (\sum_(a in {: m.-tuple bool}) Pf' m a * (log (Pf' m a) + log (PN m))).
Proof.
rewrite rewrite_HP_with_Pf; congr (- _).
rewrite (eq_bigl (fun m => m \in [set : 'I_Nmax.+1]) _) => [|?]; last first.
  by rewrite /= in_setT.
rewrite rsum_disjoints_set [Y in Y + _ = _]big1 ?add0r; last first.
  move=> /= i; rewrite inE.
  rewrite /pr_eq; unlock.
  rewrite /Pr ffunE /= => /eqP/psumr_eq0P => H.
  have {}H : forall j : A, j \in [set x | (size (f x))%:R == i%:R :> R] -> P j = 0.
    move=> a Ha.
    by apply: H => //.
  rewrite big1 // => i0 _.
  rewrite {1}/Pf.
  case: pickP => [a /eqP fai0|]; last by rewrite mul0r.
  by rewrite H ?mul0r // inE fai0 size_tuple.
apply : eq_bigr => i.
rewrite inE /eqP => Pr_non0.
rewrite big_distrr /=.
apply : eq_bigr => i0 _.
rewrite ffunE.
rewrite {1}/Pf'.
rewrite ffunE.
rewrite [in RHS]mulrC -mulrA -mulrA.
have [->|Pfi0_non0] := eqVneq (Pf i0) 0.
  by rewrite !mul0r.
congr (_ * _).
rewrite -mulrA.
rewrite mulrC.
rewrite -mulrA.
rewrite {2}/PN.
rewrite [in X in _ = _ * (_ / X)]/= [in X in _ = _ * (_ / X)]ffunE.
rewrite mulfV ?mulr1; last by rewrite /PN /= ffunE in Pr_non0.
rewrite logM; last 2 first.
  rewrite lt_neqAle eq_sym Pfi0_non0//=.
  rewrite /Pf.
  by case: pickP => //.
  rewrite invr_gt0.
  by rewrite lt_neqAle eq_sym Pr_non0//= ffunE//.
rewrite logV; last by rewrite -fdist_gt0.
by rewrite /PN /= ffunE addrAC -addrA subrr addr0.
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
  by move => /= i; rewrite inE /PN /= => /eqP ->; rewrite mul0r.
rewrite add0r rewrite_HP_with_PN !big_morph_oppr -big_split /=.
apply: eq_bigr => i.
rewrite inE => /eqP Pr_non0.
rewrite mulrN -opprD; congr (- _).
rewrite -mulrDr. congr (_ * _).
rewrite -[Y in _ = _ + Y]mul1r -(pmf1_Pf' Pr_non0) big_distrl /= -big_split /=.
by under eq_bigr do rewrite mulrDr.
Qed.

Lemma apply_max_HPN : `H P <= `E X  + `H PN.
Proof.
have f_inj := uniq_dec_inj f_uniq.
rewrite rewrite_HP_with_HPN addrC (addrC _ (`H _)) lerD2l EX_ord.
rewrite (eq_bigl (fun m => m \in [set : 'I_Nmax.+1]) (fun x=> x%:R * _ ))=>[|?]; last first.
  by rewrite /= in_setT.
rewrite rsum_disjoints_set.
rewrite [Y in _ <= Y + _ ](_ :_ = 0).
  rewrite add0r; apply: ler_sum => i.
  rewrite mulrC inE; move/eqP => H.
  rewrite ler_wpM2r//.
(*  apply/leR_wpmul2r; first by rewrite /PN /= ffunE.*)
(*  pose pmf_Pf' := mkNNFinfun (Rle0Pf' H).*)
  have pmf1'_Pf' : ([forall a, 0 <= Pf' i a] && (\sum_(a in {: i.-tuple bool}) Pf' i a == 1)).
    apply/andP; split.
      apply/forallP => x.
      rewrite /Pf'; rewrite ffunE.
      rewrite divr_ge0// /Pf.
      by case: pickP.
    by apply/eqP; apply: (pmf1_Pf' H).
  pose distPf := FDist.mk pmf1'_Pf'.
  move: (entropy_max distPf).
  rewrite card_tuple /= card_bool.
  by rewrite natrX exprnP log_exprz// log2 mulr1.
rewrite big1 //= => i.
by rewrite inE /PN /= => /eqP ->; rewrite mulr0.
Qed.

Lemma apply_le_HN_logE_loge : `H P <= `E X  + log ((expR 1) * `E X).
Proof.
apply: (le_trans apply_max_HPN).
rewrite lerD2l mulrC.
rewrite (logM (EX_gt0 P f_uniq)) ?expR_gt0//.
exact: le_entroPN_logeEX f_uniq.
Qed.

End v_scode_converse'_1tuple.

Section v_scode_converse'_ntuple.
Let R := Rdefinitions.R.
Variables (A : finType) (n : nat).
Variable f : encT A (seq bool) n.
Variable P : {fdist A}.
Hypothesis f_uniq : uniquely_decodable f.

Lemma converse_case1 : @E_leng_cw _ _ P f < n%:R * log #|A|%:R ->
`H (P `^ n)%fdist <= @E_leng_cw _ _ P f + log ((expR 1) * n%:R * log #|A|%:R).
Proof.
move=> H.
apply: (le_trans (apply_le_HN_logE_loge (P `^ n)%fdist f_uniq)).
rewrite lerD2l//; apply: Log_increasing_le => //.
  by rewrite mulr_gt0 ?expR_gt0// EX_gt0.
by rewrite -mulrA ler_wpM2l ?expR_ge0// ltW.
Qed.

Lemma converse_case2 : n%:R * log #|A|%:R <= @E_leng_cw _ _ P f ->
  `H (P `^ n)%fdist <= @E_leng_cw _ _ P f.
Proof.
move=> H; rewrite entropy_TupleFDist; apply: (le_trans _ H).
by rewrite ler_wpM2l//; exact/entropy_max.
Qed.

End v_scode_converse'_ntuple.

Section Extend_encoder.
Let R := Rdefinitions.R.
Variables (A : finType) (n m : nat).
Variable f : encT A (seq bool) n.
Variable P : {fdist A}.
Hypothesis f_uniq : uniquely_decodable f.
Hypothesis m_non0 : m%:R != 0 :> R.
Let fm (x : 'rV['rV[A]_n]_m) := extension f (tuple_of_row x).

Lemma fm_uniq : uniquely_decodable fm.
Proof.
pose m' := m.-1.
have mpos : m = m'.+1.
  by rewrite prednK // -(ltr_nat R) lt_neqAle eq_sym m_non0/=.
have: (@extension 'rV[A]_n _ f) \o
      (flatten \o map (fun x => @tval m _ (tuple_of_row x))) =1
      @extension {: 'rV[ 'rV[A]_n ]_m} _ fm.
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

Lemma ELC_TupleFDist : @E_leng_cw _ _ (P `^ n)%fdist fm = m%:R * @E_leng_cw _ _ P f.
Proof.
rewrite /E_leng_cw /=  /fm.
pose X := (fun x => x%:R : R) \o size \o f.
elim: m => [|m'].
  rewrite mul0r /Ex big1 // => i _.
  rewrite fdist_rV0 ?mulr1.
  rewrite /comp_RV.
  rewrite [tuple_of_row]lock /= -lock.
  rewrite (_ : tuple_of_row i = [tuple]) //.
  apply: eq_from_tnth.
  by case; case.
elim: m' => [_ |m'' _ IH].
  rewrite mul1r.
  rewrite -[in RHS]E_cast_RV_fdist_rV1.
  apply: eq_bigr => i _.
  rewrite fdist_rV1; congr *%R.
  rewrite /comp_RV.
  rewrite [tuple_of_row]lock /= -lock.
  rewrite (_ : tuple_of_row i = [tuple of [:: i ``_ ord0]]); last first.
    by apply eq_from_tnth => a; rewrite {a}(ord1 a) tnth_mktuple.
  by rewrite /extension /= cats0.
pose fm1 (x : 'rV['rV[A]_n]_(m''.+1)) := extension f (tuple_of_row x).
pose Xm1 := (fun x => x%:R : R) \o size \o fm1.
pose fm2 (x : 'rV['rV[A]_n]_(m''.+2)) := extension f (tuple_of_row x).
pose Xm2 := (fun x => x%:R : R) \o size \o fm2.
have X_Xm1_Xm2 : Xm2 \= X @+ Xm1.
  rewrite /Xm2 => x /=.
  rewrite /X/= /Xm1/= -natrD.
  rewrite -size_cat.
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
rewrite (E_sum_2 X_Xm1_Xm2).
rewrite -natr1 mulrDl -IH addrC; congr +%R.
  by rewrite /Xm1 -/fm1 /Ex tail_of_fdist_rV_fdist_rV.
by rewrite -/X mul1r /Ex head_of_fdist_rV_fdist_rV.
Qed.

End Extend_encoder.

Section v_scode_converse'.
Let R := Rdefinitions.R.
Variables (A : finType) (P : {fdist A}).
Variable n : nat.
Variable f : encT A (seq bool) n.
Hypothesis f_uniq : uniquely_decodable f.

Let alp : R := expR 1 * log (#| 'rV[A]_n |%:R).
Let m''' eps := `|(Num.ceil (4 / (n%:R * eps * exp.ln 2) : R))|%N.
Let m'' eps := maxn (m''' eps) 1.
Let m' eps : R := (maxn (`|(ceil (exp.ln alp + n%:R * eps * exp.ln 2))|%N) (m'' eps))%:R.
Let m eps := `|Num.floor (expR (m' eps) : R)|%N.

Lemma mpos eps : (0:R) <> n%:R -> (0:R) < (m eps)%:R.
Proof.
rewrite /m => nnon0.
rewrite ltr0n.
rewrite absz_gt0.
rewrite mathcomp_extra.floor_neq0; apply/orP; right.
by rewrite -expR0 ler_expR.
Qed.

Lemma le_eps eps : (0:R) <> n%:R -> (1:R) <= n%:R * log #|A|%:R -> (0:R) < eps ->
  log ((m eps)%:R * alp) / (m eps)%:R / n%:R <= eps.
Proof.
move=> nnon0 eps_pos cardA_non1.
pose x := m' eps.
pose Y := eps * n%:R * exp.ln 2.
have npos : 0 < n%:R :> R.
  rewrite lt_neqAle.
  by move/eqP: nnon0 => -> /=.
have xpos : 0 < x.
  rewrite ltr0n.
  apply: (@leq_trans (m'' eps)); last exact: leq_maxr.
  by apply: (@leq_trans 1); last exact: leq_maxr.
have mpos': (0 < floor (expR x)).
  rewrite lt_neqAle -floor_ge_int exp.expR_ge0 andbT.
  rewrite eq_sym mathcomp_extra.floor_neq0.
  apply/orP; right.
  by rewrite -exp.expR0 exp.ler_expR//.
have le_1_alp : 1 <= alp.
  rewrite /alp -(mulr1 1).
  rewrite ler_pM//.
    rewrite mulr1; apply: (@le_trans _ _ 2); last first.
      rewrite (_ : 2 = 1 + 1)//.
      by rewrite exp.expR_ge1Dx.
    by rewrite ler1n.
  rewrite mul1r//.
  rewrite card_mx mul1n.
  rewrite natrX exprnP log_exprz// ltr0n.
  exact/(fdist_card_neq0 P).
have alppos : 0 < alp by exact: (@lt_le_trans _ _ 1).
have Ypos : 0 < Y.
  by rewrite mulr_gt0// ?mulr_gt0// ln2_gt0.
rewrite -mulrA -invfM ler_pdivrMr//; last first.
  by rewrite mulr_gt0//; apply: mpos.
(*rewrite mulR1 mulVR ?mulR1; last exact/gtR_eqF/mpos/eqP/ltR_eqF.*)
apply: (@le_trans _ _ ((x ^ 2 / 2 - 1) * eps * n%:R)); last first.
  rewrite -mulrA mulrC -mulrA.
  rewrite ler_wpM2l//; first exact/ltW.
  rewrite mulrC ler_wpM2r//.
  apply: (@le_trans _ _ (expR x - 1)).
    rewrite lerBlDr subrK (_ : 2 = (2 `!)%:R)//.
    exact/ltW/exp_strict_lb.
  rewrite /m /x.
  rewrite lerBlDr.
  rewrite (le_trans (ltW (mathcomp_extra.lt_succ_floor _)))//.
  rewrite natr_absz.
  rewrite mathcomp_extra.intrD1 ler_int.
  rewrite lerD2r.
  by rewrite ler_norm.
rewrite logM//; last exact: mpos.
rewrite -(ler_pM2r ln2_gt0).
rewrite mulrDl -(mulrA (ln alp)) (mulVf ln2_neq0).
rewrite mulr1 -(mulrA _ (ln 2)^-1 _) (mulVf ln2_neq0).
apply: (@le_trans _ _ (x + ln alp)).
  rewrite lerD2r ?mulr1 -(expRK x).
  rewrite ler_ln ?posrE ?expR_gt0//; last exact: mpos.
  rewrite /m /x.
  rewrite (le_trans _ (ge_floor _))//.
  rewrite natr_absz ler_int.
  by rewrite ger0_norm// mathcomp_extra.floor_ge0// expR_ge0.
apply: (@le_trans _ _ (2 * x - (eps * n%:R * ln 2))).
  rewrite mulr_natl mulr2n -addrA lerD2l.
  rewrite lerBrDr (mulrC eps).
  apply: (@le_trans _ _ ((Num.ceil (ln alp + n%:R * eps * ln 2))%:~R)).
    by rewrite le_ceil.
  rewrite /x /m'.
  rewrite (le_trans (ler_norm _))//.
  rewrite -intr_norm.
  rewrite -natr_absz ler_nat.
  by rewrite leq_max leqnn.
rewrite -(mulrA _ eps) -(mulrA _ (eps * n%:R)).
rewrite mulrBl mul1r lerD2r.
rewrite -/Y.
rewrite -(@ler_pM2l _ ((Y^-1 * 2 / x))); last first.
  by rewrite mulr_gt0 ?invr_gt0// mulr_gt0// invr_gt0.
rewrite -!mulrA (mulrCA x^-1) mulVf ?mulr1 ?gt_eqF//.
rewrite (mulrA x^-1) mulVf ?mul1r ?gt_eqF//.
rewrite (mulrCA 2) (mulrA 2) divff ?gt_eqF// mul1r.
rewrite [leRHS]mulrCA mulVf ?mulr1 ?gt_eqF//.
apply: (@le_trans _ _ (m'' eps)%:R); last first.
  rewrite /x /m'.
  rewrite ler_nat.
  by rewrite leq_maxr.
apply: (@le_trans _ _ (m''' eps)%:R); last first.
  by rewrite /m'' ler_nat leq_max leqnn.
rewrite /m'''.
rewrite (mulrC n%:R) -/Y.
rewrite mulrC -natrM.
rewrite (le_trans (le_ceil _))//.
rewrite natr_absz.
rewrite (le_trans (ler_norm _))//.
by rewrite intr_norm.
Qed.

Theorem v_scode_converse' : n%:R * `H P <= @E_leng_cw _ _ P f.
Proof.
have [<-|nnon0] := eqVneq (0:R) n%:R.
  rewrite mul0r ltW//.
  rewrite /E_leng_cw.
  by rewrite EX_gt0//.
have npos : 0 < n%:R :> R.
  move: nnon0.
  rewrite eq_sym pnatr_eq0 ltr0n.
  by rewrite lt0n.
rewrite -ler_pdivlMl// mulrC.
apply/ler_addgt0Pl => /= eps eps0.
pose fm (x : 'rV['rV[A]_n]_((m eps))) := extension f (tuple_of_row x).
have [|] := leP ((m eps)%:R * (log #| 'rV[A]_n |%:R)) (@E_leng_cw _ _ (P `^ n)%fdist fm).
  move/(@converse_case2 _ _ fm (P `^ n)%fdist).
  rewrite !entropy_TupleFDist ELC_TupleFDist.
  rewrite ler_pM2l//; last first.
    apply: mpos => //.
    exact/eqP.
  move=> H.
  apply: (@le_trans _ _ (@E_leng_cw _ _ P f / n%:R)) => //.
    by rewrite ler_pdivlMr// mulrC.
  by rewrite ler_wpDl// ltW.
have mnon0 : (m eps)%:R <> 0 :> R.
  apply/eqP.
  rewrite gt_eqF// mpos//.
  exact/eqP.
move => case2.
move/eqP in mnon0.
move: (@converse_case1 _ _ _ (P `^ n)%fdist
  (fm_uniq f_uniq mnon0) case2).
rewrite !entropy_TupleFDist ELC_TupleFDist -!mulrA mulrA.
rewrite -ler_pdivlMl; last first.
  rewrite mulr_gt0//.
  apply: mpos.
  exact/eqP.
move=> /le_trans; apply.
rewrite mulrDr.
rewrite {1}invfM.
rewrite mulrCA.
rewrite ![in X in X + _ <= _](mulrA (m eps)%:R) divff// mul1r.
rewrite mulrC addrC lerD2r.
rewrite mulrC.
move/eqP in nnon0.
rewrite invfM.
rewrite (mulrCA (expR 1)).
rewrite (mulrA (log _)).
apply: le_eps => //.
move: case2.
rewrite ELC_TupleFDist mulrC (mulrC (m eps)%:R) card_mx mul1n.
rewrite natrX log_exprz; last first.
  by rewrite ltr0n// (fdist_card_neq0 P).
rewrite ltr_pM2r//; last exact: mpos.
move=> /ltW.
apply: le_trans.
exact/le_1_EX.
Qed.

End v_scode_converse'.

Section v_scode_converse.
Variables (A : finType) (P : {fdist A}) (n : nat).
Variable f : encT A (seq bool) n.
Hypothesis f_uniq : uniquely_decodable f.

Theorem v_scode_converse : n%:R * `H P <= @E_leng_cw _ _ P f.
Proof. exact: v_scode_converse'. Qed.

End v_scode_converse.
