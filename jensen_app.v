From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.

Require Import Reals Fourier ProofIrrelevance FunctionalExtensionality.
Require Import Rssr Reals_ext ssr_ext ssralg_ext log2 Rbigop.
Require Import proba jensen num_occ.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section string_concat.

Variable A : finType.

Definition minlen (s : seq A) :=
  \rsum_(c <- s) log (INR (size s) / INR (num_occ c s)).

Definition Hs0 (s : seq A) :=
  / INR (size s) * minlen s.

Lemma sum_num_occ (s : seq A) : \sum_(a in A) num_occ a s = size s.
Proof.
elim: s => [|a s IH] /=.
+ by apply big1_eq.
+ rewrite big_split /= IH -big_mkcond /= (big_pred1 a) //.
  by move=> i; rewrite eq_sym.
Qed.

Definition Hs (s : seq A) :=
 \rsum_(a in A)
  if num_occ a s == 0%nat then 0 else
  INR (num_occ a s) / INR (size s) * log (INR (size s) / INR (num_occ a s)).

Definition nHs (s : seq A) :=
 \rsum_(a in A)
  if num_occ a s == 0%nat then 0 else
  INR (num_occ a s) * log (INR (size s) / INR (num_occ a s)).

Lemma szHs_is_nHs s : INR (size s) * Hs s = nHs s.
Proof.
rewrite /Hs /nHs big_distrr.
apply eq_bigr => i _ /=.
case: ifP => Hnum.
  by rewrite mulR0.
rewrite /Rdiv (mulRC (INR (num_occ i s))) 2!(mulRA (INR _)).
rewrite !mulRV ?mul1R // ?INR_eq0.
apply/eqP => Hsz.
move: (count_size (pred1 i) s).
by rewrite Hsz leqn0 Hnum.
Qed.

Lemma log_concave : concave_in (fun x => 0 < x) log.
Proof.
move=> x y t Hx Hy Ht.
split; last first.
case Ht1: (t == 1).
  rewrite (eqP Ht1).
Search (0 < _ + _).
  apply Rplus_lt_le_0_compat.
    by rewrite mul1R.
  rewrite subRR mul0R.
  by apply Rle_refl.
apply Rplus_le_lt_0_compat.
  apply Rmult_le_pos.
    exact/(proj1 Ht).
  by apply Rlt_le.
apply mulR_gt0 => //.
apply (Rplus_lt_reg_l t).
rewrite addR0 Rplus_minus.
apply/RltP; rewrite ltR_neqAle Ht1 /=; apply/RleP; by case: Ht.
Admitted.

Lemma a_eq_true : Set2.a card_bool = true.
Proof.
rewrite /Set2.a /enum_val /enum_mem.
by rewrite Finite.EnumDef.enumDef /=.
Qed.

Theorem concat_entropy s1 s2 :
  INR (size s1) * Hs s1 + INR (size s2) * Hs s2
  <= INR (size (s1 ++ s2)) * Hs (s1 ++ s2).
Proof.
rewrite !szHs_is_nHs.
rewrite /nHs -big_split /=.
apply ler_rsum => i _.
rewrite /num_occ count_cat size_cat.
case: ifP => Hs1.
  rewrite (eqP Hs1) !add0n add0R.
  case: ifP => Hs2.
    by apply Rle_refl.
  have cnt_s2_gt0: 0 < INR (count_mem i s2).
    apply lt_0_INR.
    apply /leP.
    by rewrite lt0n Hs2.
  have cnt_lt_size t: INR ((count_mem i) t) <= INR (size t).
    apply le_INR.
    apply/leP.
    by apply count_size.
  have sz_s2_gt0: 0 < INR (size s2).
    apply (Rlt_le_trans _ _ _ cnt_s2_gt0).
    by apply cnt_lt_size.
  apply Rmult_le_compat_l.
    by apply Rlt_le.
  apply Log_increasing_le.
      by apply Rlt_1_2.
    by apply Rlt_mult_inv_pos.
  apply Rmult_le_compat_r.
    by apply Rlt_le, invR_gt0, cnt_s2_gt0.
  apply le_INR.
  apply /leP.
  by apply leq_addl.
have cnt_s1_gt0: 0 < INR (count_mem i s1).
  apply lt_0_INR.
  apply /leP.
  by rewrite lt0n Hs1.
have cnt_lt_size t: INR ((count_mem i) t) <= INR (size t).
  apply le_INR.
  apply/leP.
  by apply count_size.
have sz_s1_gt0: 0 < INR (size s1).
  apply (Rlt_le_trans _ _ _ cnt_s1_gt0).
  by apply cnt_lt_size.
case: ifP => Hs2.
  rewrite (eqP Hs2) !addn0 addR0 Hs1.
  apply Rmult_le_compat_l.
    by apply Rlt_le.
  apply Log_increasing_le.
      by apply Rlt_1_2.
    by apply Rlt_mult_inv_pos.
  apply Rmult_le_compat_r.
    by apply Rlt_le, invR_gt0, cnt_s1_gt0.
  apply le_INR.
  apply /leP.
  by apply leq_addr.
case: ifP => Hs12.
  by rewrite addn_eq0 Hs1 in Hs12.
have cnt_s2_gt0: 0 < INR (count_mem i s2).
  apply lt_0_INR.
  apply /leP.
  by rewrite lt0n Hs2.
have cnt_12_gt0: 0 < INR (count_mem i s1 + count_mem i s2).
  apply (Rlt_le_trans _ _ _ cnt_s1_gt0).
  apply le_INR.
  apply/leP.
  by apply leq_addr.
(* Then we should use jensen_dist *)
have Hp: 0 <= INR (count_mem i s2) / INR (count_mem i (s1 ++ s2)) <= 1.
  rewrite count_cat.
  split.
    apply Rlt_le.
    apply mulR_gt0 => //.
    by apply invR_gt0.
  apply (Rmult_le_reg_r _ _ _ cnt_12_gt0).
  rewrite -mulRA (mulRC (/ _)) mulRV ?(mulR1,mul1R).
    apply le_INR.
    apply/leP.
    by apply leq_addl.
  rewrite INR_eq0 -lt0n -ltR0n; exact/RltP.
have H1m: 1 - INR (count_mem i s2) / INR (count_mem i (s1 ++ s2)) =
          INR (count_mem i s1) / INR (count_mem i (s1 ++ s2)).
  rewrite count_cat -(divRR (INR (count_mem i s1 + count_mem i s2))).
    rewrite -Rdiv_minus_distr -minus_INR.
      by rewrite minusE addnK.
    apply/leP.
    by apply leq_addl.
  rewrite INR_eq0 -lt0n -ltR0n; exact/RltP.
have Hdist: (0 < #|dist_supp (Binary.d card_bool Hp)|)%nat.
  rewrite /dist_supp card_gt0.
  apply/eqP => /setP /(_ true).
  rewrite !inE /= a_eq_true /= /Binary.f eqxx.
  rewrite H1m.
  move/eqP.
  apply Rmult_integral_contrapositive.
  split.
    exact/gtR_eqF.
  apply/eqP/invR_neq0/eqP/gtR_eqF; by rewrite count_cat.
set r := (fun b => if b then INR (size s1) / INR (count_mem i s1)
                   else INR (size s2) / INR (count_mem i s2)).
have Hr: dist_covered (fun x => 0 < x) r (Binary.d card_bool Hp).
  move=> [|] _ /=.
    by apply Rdiv_lt_0_compat.
  apply Rdiv_lt_0_compat => //.
  apply lt_0_INR.
  apply/leP.
  apply (@leq_trans (count_mem i s2)).
    by rewrite lt0n Hs2.
  by apply count_size.
move: (jensen_dist_concave log_concave Hdist Hr).
rewrite (bigD1 true) ?inE // (bigD1 false) ?inE // big_pred0 /=;
  last by move=> j /=; case: j.
rewrite (bigD1 true) ?inE // (bigD1 false) ?inE // big_pred0 /Binary.f /=;
  last by move=> j /=; case: j.
rewrite a_eq_true eqxx eqb_id /=.
rewrite H1m !addR0.
rewrite /Rdiv 4!mulRA -2![_ * / _ * _]mulRA.
rewrite mulVR ?mulR1; last first.
  by rewrite INR_eq0 Hs2.
rewrite mulVR ?mulR1; last first.
  by rewrite INR_eq0 Hs1.
rewrite -2!Rmult_plus_distr_r.
rewrite mulRC.
move/(Rmult_le_compat_l (INR ((count_mem i) (s1 ++ s2)))).
rewrite mulRA mulRV ?INR_eq0 ?mul1R; last first.
  rewrite -?lt0n count_cat -ltR0n; exact/RltP.
rewrite -count_cat plus_INR.
rewrite ![_ * INR (count_mem _ _)]mulRC.
apply.
apply Rlt_le.
by rewrite count_cat.
Qed.

Lemma num_occ_flatten (a:A) ss :
  num_occ a (flatten ss) = \sum_(s <- ss) num_occ a s.
Proof.
rewrite /num_occ.
elim: ss => [|s ss IH] /=.
  by rewrite big_nil.
by rewrite big_cons /= count_cat IH.
Qed.

Definition big_morph_plus_INR := big_morph INR morph_plus_INR (erefl (INR 0)).

Theorem concats_entropy ss :
  \rsum_(s <- ss) INR (size s) * Hs s
       <= INR (size (flatten ss)) * Hs (flatten ss).
Proof.
(* First simplify formula *)
rewrite szHs_is_nHs.
rewrite (eq_bigr _ (fun i _ => szHs_is_nHs i)) exchange_big /=.
apply ler_rsum=> a _.
(* Remove string containing no occurences from the sums *)
rewrite (bigID (fun s => num_occ a s == O)) /=.
rewrite big1; last by move=> i ->.
rewrite num_occ_flatten add0R.
rewrite [in X in _ <= X](bigID (fun s => num_occ a s == O)) /=.
rewrite [in X in _ <= X]big1 //; last by move=> i /eqP.
rewrite (eq_bigr
       (fun i => log (INR (size i) / INR (num_occ a i)) * INR (num_occ a i)));
  last by move=> i /negbTE ->; rewrite mulRC.
rewrite -big_filter -[in X in _ <= X]big_filter add0n.
(* ss' contains only strings with ocurrences *)
set ss' := [seq s <- ss | num_occ a s != O].
case Hss': (ss' == [::]).
  by rewrite (eqP Hss') !big_nil eqxx; right.
have Hnum (s : seq A) : s \in ss' -> num_occ a s != O.
  by rewrite /ss' mem_filter => /andP [->].
have Hnum': 0 < INR (num_occ a (flatten ss')).
  apply /lt_0_INR /leP.
  destruct ss' => //=.
  rewrite /num_occ count_cat ltn_addr //.
  by rewrite lt0n Hnum // in_cons eqxx.
have Hsz: 0 < INR (size (flatten ss')).
  apply (Rlt_le_trans _ _ _ Hnum').
  by apply /le_INR /leP /count_size.
apply (Rle_trans _ (INR (\sum_(i <- ss') num_occ a i) *
    log (INR (size (flatten ss')) / INR (\sum_(i <- ss') num_occ a i))));
  last first.
  (* Not mentioned in the book: one has to compensate for the discarding
     of strings containing no occurences.
     Works thanks to monotonicity of log. *)
  case: ifP => Hsum.
    by rewrite (eqP Hsum) mul0R; right.
  apply Rmult_le_compat_l; first by apply pos_INR.
  apply Log_increasing_le; first by apply Rlt_1_2.
    apply Rlt_mult_inv_pos => //.
    apply/lt_0_INR/ltP.
    by rewrite lt0n Hsum.
  apply Rmult_le_compat_r.
    apply /Rlt_le /invR_gt0 /lt_0_INR /ltP.
    by rewrite lt0n Hsum.
  apply /le_INR /leP.
  rewrite !size_flatten !sumn_big_addn !big_map big_filter.
  rewrite [in X in (_ <= X)%nat](bigID (fun s => num_occ a s == O)) /=.
  by apply leq_addl.
(* Prepare to use jensen_dist_concave *)
set f := fun x : 'I_(size ss') =>
  INR (num_occ a (tnth (in_tuple ss') x)) / INR (num_occ a (flatten ss')).
set r := fun x : 'I_(size ss') =>
  INR (size (tnth (in_tuple ss') x)) / INR (num_occ a (tnth (in_tuple ss') x)).
have f_pos x : 0 < f x.
  apply Rlt_mult_inv_pos => //.
  apply /lt_0_INR /ltP.
  by rewrite lt0n Hnum // mem_tnth.
have f_nonneg x : 0 <= f x by apply Rlt_le.
have f_1 : \rsum_(a < size ss') (mkPosFun f_nonneg) a = 1.
  rewrite /= /f -big_distrl /= num_occ_flatten.
  rewrite big_morph_plus_INR mulRC big_tnth /= mulVR //.
  rewrite -big_morph_plus_INR INR_eq0.
  destruct ss' => //=.
  rewrite big_ord_recl (tnth_nth [::]) /=.
  by rewrite addn_eq0 negb_and Hnum // in_cons eqxx.
set d := mkDist f_1.
have Hdist: (0 < #|dist_supp d|)%nat.
  rewrite /dist_supp card_gt0.
  destruct ss' => //.
  apply/eqP => /setP /(_ ord0).
  rewrite !inE /d /= => /negbFE /eqP.
  exact/gtR_eqF.
have Hr: dist_covered (fun x => 0 < x) r d.
  move=> i Hi.
  rewrite /r /=.
  apply Rlt_mult_inv_pos.
    apply /lt_0_INR /ltP /(@leq_trans (num_occ a (tnth (in_tuple ss') i))).
      by rewrite lt0n Hnum // mem_tnth.
    by apply count_size.
  apply /lt_0_INR /ltP.
  by rewrite lt0n Hnum // mem_tnth.
move: (jensen_dist_concave log_concave Hdist Hr).
rewrite /d /f /r /=.
rewrite -(big_tuple R0 Rplus (in_tuple ss') xpredT
  (fun s:seq A =>
     log (INR (size s) / INR (num_occ a s)) *
     (INR (num_occ a s) / INR (num_occ a (flatten ss'))))).
rewrite -(big_tuple R0 Rplus (in_tuple ss') xpredT
  (fun s:seq A =>
     INR (size s) / INR (num_occ a s) *
     (INR (num_occ a s) / INR (num_occ a (flatten ss'))))) /=.
move/(Rmult_le_compat_r (INR (num_occ a (flatten ss'))) _ _ (pos_INR _)).
rewrite !big_distrl /=.
rewrite (eq_bigr
     (fun i => log (INR (size i) / INR (num_occ a i)) * INR (num_occ a i)));
  last first.
  move=> i _; rewrite !mulRA -mulRA mulVR ?mulR1 //.
  exact/eqP/gtR_eqF.
(* LHS do match *)
move/Rle_trans; apply.
rewrite mulRC -num_occ_flatten big_filter.
rewrite (eq_bigr
     (fun i => INR (size i) * / INR (num_occ a (flatten ss'))));
  last first.
  by move=> i Hi; rewrite !mulRA -(mulRA _ (/ _)) mulVR ?mulR1 // INR_eq0.
rewrite -big_filter -/ss' -big_distrl -big_morph_plus_INR /=.
by rewrite size_flatten sumn_big_addn big_map; right.
Qed.
    
End string_concat.
