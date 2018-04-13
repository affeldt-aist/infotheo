From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype tuple bigop finset path ssralg.
From mathcomp Require Import fingroup zmodp poly ssrnum.

Require Import ssr_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma empty_finType_nil (T : finType) : (#|T| = 0) -> forall c : seq T, c = [::].
Proof. move/card0_eq => T0; by case=> // h; move: (T0 h); rewrite !inE. Qed.

Lemma sorted_leq_last s : sorted leq s -> forall i, i \in s -> i <= last 0 s.
Proof.
move=> H /= m; case/(nthP O) => i Hi <-.
rewrite -nth_last; apply nth_of_sorted => //.
move: Hi; case: (size _) => //= k; by rewrite ltnS => -> /=.
Qed.

Section prefix.

Variable T : finType.
Implicit Types a b : seq T.

Definition prefix a b := a == take (size a) b.

Lemma prefix_cons x y a b : prefix (x :: a) (y :: b) = (x == y) && prefix a b.
Proof.
rewrite /prefix /=.
by apply/eqP/andP => [[-> {1}-> //]|[/eqP -> /eqP <-]].
Qed.

Lemma prefix_cat a b : prefix a (a ++ b).
Proof. by rewrite /prefix take_cat ltnn subnn take0 cats0. Qed.

Lemma prefixP a b : reflect (exists s, a ++ s == b) (prefix a b).
Proof.
apply: (iffP idP); last by case=> s /eqP <-; exact: prefix_cat.
elim: b a => [[] // _|h t IH]; first by exists [::].
case=> [/= _|x a]; first by exists (h :: t).
rewrite prefix_cons => /andP[/eqP -> /IH[s Hs]].
by exists s; rewrite /= (eqP Hs).
Qed.

Lemma prefix_common a b s : prefix a s -> prefix b s ->
  prefix a b \/ prefix b a.
Proof.
case/prefixP => t /eqP <-{s} /prefixP[t'].
wlog : t t' a b / size a <= size b.
  move=> H.
  case/boolP : (size a <= size b) => [? K|]; first exact: (H t t').
  rewrite leqNgt negbK => /ltnW /(H t' t) {H} H /eqP/esym/eqP; tauto.
move=> ab H; left; apply/prefixP; exists (take (size b - size a) t).
move/eqP : H => /(congr1 (take (size b))).
by rewrite take_cat ltnn subnn take0 cats0 take_cat ltnNge ab /= => <-.
Qed.

Lemma prefixW a b : a != b -> prefix a b -> size a < size b.
Proof.
move=> ab /prefixP[[|h t /eqP <-]]; first by rewrite cats0 (negbTE ab).
by rewrite size_cat /= -addSnnS ltn_addr.
Qed.

Lemma prefix_neq_size a b : prefix a b -> a != b -> size a < size b.
Proof.
move/prefixP => [c /eqP  <-]; rewrite ltnNge; apply: contra.
case: c => [|x y]; first by rewrite cats0.
by rewrite size_cat /= -{2}(addn0 (size a)) leq_add2l ltn0.
Qed.

Lemma prefix_leq_size a b : prefix a b -> size a <= size b.
Proof. by move/prefixP => [c /eqP  <-]; rewrite size_cat leq_addr. Qed.

End prefix.

Section ary_of_nat.

Variable t' : nat.
Let t := t'.+2.

Program Definition ary_of_nat'
  (n : nat) (f : forall n', (n' < n)%coq_nat -> seq 'I_t) : seq 'I_t :=
  match n with
    | O => [:: ord0]
    | n'.+1 =>
      if n < t then
        [:: inord n]
      else
        rcons (f (n %/ t) _) (inord (n %% t))
  end.
Next Obligation. exact/ltP/ltn_Pdiv. Qed.

Definition ary_of_nat := Fix Wf_nat.lt_wf (fun _ => seq 'I_t) ary_of_nat'.

Require FunctionalExtensionality.

Lemma ary_of_nat_unfold n : ary_of_nat n =
  if n < t then [:: inord n] else rcons (ary_of_nat (n %/ t)) (inord (n %% t)).
Proof.
rewrite {1}/ary_of_nat Fix_eq //.
  destruct n => //=.
  congr cons; apply val_inj => /=; by rewrite inordK.
move=> m f f' H; congr ary_of_nat'.
apply FunctionalExtensionality.functional_extensionality_dep => k.
by apply FunctionalExtensionality.functional_extensionality.
Qed.

Lemma ary_of_nat0 : ary_of_nat 0 = [:: ord0].
Proof. by []. Qed.

Lemma ary_of_nat_head' n def : head def (ary_of_nat n.+1) != ord0.
Proof.
elim: n.+1 {-2}n (ltnSn n) def => {n}// n IH m; rewrite ltnS => mn def.
rewrite ary_of_nat_unfold; case: ifPn => [nt /=|].
  apply/eqP => /(congr1 val) /=; by rewrite inordK.
rewrite -leqNgt => nt; rewrite headI /=.
move: nt; rewrite leq_eqVlt => /orP[/eqP tm|].
  rewrite (_ : _ %/ _ = 1); last by rewrite tm divnn.
  apply/eqP => /(congr1 val) /=; by rewrite inordK.
move=> nt.
suff [k Hk] : exists k : 'I_n, m.+1 %/ t = k.+1 by rewrite Hk IH.
move=> [:Hx].
have @x : 'I_n.
  apply: (@Ordinal _ (m.+1 %/ t).-1 _).
  abstract: Hx.
  rewrite prednK ?divn_gt0 //; [apply/ltnW | by rewrite ltnW].
  rewrite ltn_divLR // -addn2 mulnS leq_add //.
  destruct m as [|m] => //; destruct n as [|n] => //.
  rewrite mulnS addSn ltnS.
  destruct n as [|n]; by [destruct m | rewrite addSn ltnS].
by exists x => /=; rewrite prednK // divn_gt0 // ltnW.
Qed.

Lemma ary_of_nat_head n def : (head def (ary_of_nat n) == ord0) = (n == O).
Proof.
apply/idP/idP => [|/eqP ->]; last by rewrite ary_of_nat0.
apply: contraTT; destruct n as [|n] => // _; by apply ary_of_nat_head'.
Qed.

Lemma size_ary_of_nat k : k != 0 -> forall n, n < t ^ k -> size (ary_of_nat n) <= k.
Proof.
elim: k.+1 {-2}k (ltnSn k) => // {k}k IH [_ //|n].
rewrite ltnS => nk _ m mt.
rewrite ary_of_nat_unfold; case: ifPn => //.
rewrite -leqNgt => tm; rewrite size_rcons ltnS IH //.
  destruct n as [|n] => //.
  rewrite expn1 in mt; move: (leq_ltn_trans tm mt); by rewrite ltnn.
by rewrite -(@ltn_pmul2r t) // -expnSr (leq_trans _ mt) // ltnS leq_trunc_div.
Qed.

Definition nat_of_ary (s : seq 'I_t) : nat :=
  \sum_(i < size s) nth ord0 s i * t ^ ((size s).-1 - i).

Lemma nat_of_ary_nseq0 (n : nat) : nat_of_ary (nseq n ord0) = 0.
Proof.
rewrite /nat_of_ary (eq_bigr (fun=> O)) ?big1 //= => i _.
rewrite nth_nseq; by case: ifPn.
Qed.

Lemma nat_of_ary1 (m : 'I_t) : nat_of_ary [:: m] = m.
Proof. by rewrite /nat_of_ary big_ord_recl expn0 muln1 big_ord0 addn0. Qed.

Lemma nat_of_ary_cat (s1 s2 : seq 'I_t) :
  nat_of_ary (s1 ++ s2) = nat_of_ary s1 * #|'I_t| ^ size s2 + nat_of_ary s2.
Proof.
rewrite {1}/nat_of_ary size_cat (bigID (fun i : 'I__ => i < size s1)) /=.
congr addn.
  rewrite /nat_of_ary big_distrl /=.
  transitivity (\sum_(i < size s1)
    nth ord0 (s1 ++ s2) i * t ^ ((size s1 + size s2).-1 - i)).
    rewrite -(big_mkord (fun i => i < size s1)
      (fun i => nth ord0 (s1 ++ s2) i * t ^ ((size s1 + size s2).-1 - i))).
    rewrite -(big_mkord xpredT
      (fun i => nth ord0 (s1 ++ s2) i * t ^ ((size s1 + size s2).-1 - i))).
    rewrite -big_filter -[in RHS]big_filter; apply congr_big => //.
    rewrite /index_iota !subn0 iota_add filter_cat add0n.
    rewrite (@eq_in_filter _ _ predT) ?filter_predT; last first.
      by move=> ?; rewrite mem_iota leq0n /= => ->.
    rewrite (@eq_in_filter _ _ pred0) ?filter_pred0 ?cats0 //.
    by move=> i; rewrite mem_iota leqNgt => /andP[/negbTE].
  apply eq_bigr => i _.
  rewrite nth_cat ltn_ord card_ord -mulnA -expnD; congr (_ * _ ^ _).
  by rewrite [in RHS](addnC _ (size s2)) addnC -!subn1 -!subnDA addnBA.
transitivity (\sum_(size s1 <= i < size s1 + size s2)
    nth ord0 (s1 ++ s2) i * t ^ ((size s1 + size s2).-1 - i)).
  rewrite -(big_mkord (fun i => ~~ (i < size s1))
    (fun i => nth ord0 (s1 ++ s2) i * t ^ ((size s1 + size s2).-1 - i))).
  rewrite -big_filter; apply congr_big => //.
  rewrite /index_iota subn0 iota_add filter_cat add0n.
  rewrite (@eq_in_filter _ _ pred0) ?filter_pred0 //; last first.
      move=> i; by rewrite mem_iota leq0n /= add0n => ->.
  rewrite cat0s addnC addnK (@eq_in_filter _ _ predT) ?filter_predT //.
  move=> i; by rewrite mem_iota leqNgt => /andP[].
rewrite -{1}(add0n (size s1)) big_addn addnC addnK big_mkord.
apply eq_bigr => i _.
rewrite nth_cat ifF; last by apply/negbTE; rewrite -leqNgt leq_addl.
rewrite addnK; congr (_ * t ^ _).
rewrite (addnC i) subnDA; congr (_ - _).
by rewrite -subn1 -subnDA (addnC 1) subnDA addnK subn1.
Qed.

Lemma nat_of_ary_ub (s : seq 'I_t) : nat_of_ary s < #|'I_t| ^ size s.
Proof.
elim/last_ind : s => [|a b IH]; first by rewrite /nat_of_ary big_ord0 expn0.
rewrite -{1}cats1 nat_of_ary_cat expn1 size_rcons /=.
rewrite (@leq_trans (nat_of_ary a * #|'I_t| + #|'I_t|)) //.
  by rewrite ltn_add2l nat_of_ary1 card_ord.
by rewrite -mulSnr expnSr leq_pmul2r // card_ord.
Qed.

Lemma prefix_modn (s1 s2 : seq 'I_t) : prefix s1 s2 ->
  nat_of_ary s2 = nat_of_ary s1 * #|'I_t| ^ (size s2 - size s1) +
                  nat_of_ary s2 %% #|'I_t| ^ (size s2 - size s1).
Proof.
case/prefixP => s3 H.
rewrite -{1 2}(eqP H) nat_of_ary_cat size_cat (addnC (_ s1)) addnK; congr addn.
rewrite -{1 2}(eqP H) nat_of_ary_cat size_cat (addnC (_ s1)) addnK.
by rewrite modnMDl modn_small // nat_of_ary_ub.
Qed.

Lemma ary_of_natK n : nat_of_ary (ary_of_nat n) = n.
Proof.
elim: n.+1 {-2}n (ltnSn n) => {n}// n IH m mn.
rewrite ary_of_nat_unfold.
case: ifPn => [nt|]; first by rewrite nat_of_ary1 inordK.
rewrite -leqNgt => tn.
rewrite -cats1 nat_of_ary_cat /= expn1 card_ord IH //; last first.
  rewrite ltn_divLR // (leq_trans mn) // ltn_Pmulr //.
  destruct n => //; by destruct m.
by rewrite nat_of_ary1 inordK // ?ltn_pmod // -divn_eq.
Qed.

Lemma injective_ary_of_nat : injective ary_of_nat.
Proof. apply (@can_inj _ _ _ nat_of_ary) => i; by rewrite ary_of_natK. Qed.

Lemma nat_of_ary_0' s : nat_of_ary s = 0 -> all (eq_op^~ ord0) s.
Proof.
elim: s => // a b IH.
rewrite -cat1s nat_of_ary_cat => /eqP; rewrite addn_eq0 => /andP[/=].
rewrite muln_eq0 card_ord expn_eq0 /= orbF nat_of_ary1 => /eqP H1 /eqP H2.
by rewrite /= IH // andbT; apply/eqP/val_inj.
Qed.

Lemma nat_of_ary_0 s : (nat_of_ary s == 0) = (all (xpred1 ord0) s).
Proof.
apply/idP/idP => [/eqP|/all_pred1P H]; first exact: nat_of_ary_0'.
apply/eqP/injective_ary_of_nat.
by rewrite ary_of_nat0 H nat_of_ary_nseq0 ary_of_nat0.
Qed.

End ary_of_nat.

Section code.

Variable T : finType.

Record code_set := CodeSet {
  codeset :> seq (seq T) ;
  _ : uniq codeset
}.

Definition mem_code_set (C : code_set) := fun x => x \in codeset C.
Canonical code_set_predType := Eval hnf in @mkPredType _ code_set mem_code_set.

Definition sort_sizes (C : code_set) : seq nat := sort leq (map size C).

Lemma sorted_sort_sizes C : sorted leq (sort_sizes C).
Proof. apply sort_sorted; exact: leq_total. Qed.

Lemma size_sort_sizes C : size (sort_sizes C) = size C.
Proof. by rewrite size_sort size_map. Qed.

Lemma empty_finType_code_set (C : code_set) : (#|T| = 0) ->
  C = [::] :> seq _ \/ C = [:: [::]] :> seq _.
Proof.
move=> T0.
case/boolP : (C == [::] :> seq _); first by move/eqP; left.
rewrite -size_eq0 => C0; right.
have : size C <= 1.
  rewrite leqNgt.
  apply/negP => C2.
  have : exists a b, a \in C /\ b \in C /\ a != b.
    destruct C as [[|s1 [|s2 s3]] Hs] => //.
    simpl in *.
    exists s1, s2.
    rewrite !inE !eqxx /= orbT; split => //; split => //.
    apply/negP => /= /eqP s1s2.
    move: (Hs); by rewrite s1s2 !inE eqxx.
  case=> a; case=> b [aC [bC]].
  apply/negP; by rewrite negbK (empty_finType_nil T0 a) (empty_finType_nil _ b).
rewrite leq_eqVlt ltnS leqn0 (negbTE C0) orbF.
destruct C as [s Hs] => /=.
destruct s as [|s1 [|s2 s3]] => // _.
by rewrite (empty_finType_nil T0 s1).
Qed.

Lemma empty_finType_size (C : code_set) : (#|T| = 0) -> size C <= 1.
Proof. by case/(empty_finType_code_set C) => ->. Qed.

End code.

Section prefix_code.

Variable T : finType.

Definition prefix_code (C : code_set T) :=
  forall c c', c \in C -> c' \in C -> c != c' -> ~~ prefix c c'.

Definition prefix_code_strong (C : code_set T) :=
  forall c c', c \in C -> c' \in C -> c != c' ->
  size c <= size c' -> ~~ prefix c c'.

Lemma prefix_codeP C : prefix_code C <-> prefix_code_strong C.
Proof.
split.
  move=> H c c' cC c'C cc' _.
  by apply H.
move=> H c c' cC c'C cc'.
  case/boolP : (size c <= size c') => [K|]; first exact: H.
  apply: contra => /eqP K.
  by rewrite -(cat_take_drop (size c) c') {1}K size_cat leq_addr.
Qed.

Lemma nnpp_prefix (C : code_set T) :
  (~ prefix_code C -> False) -> prefix_code C.
Proof.
move=> H c c' cC c'C cc'.
apply/negP => prefix_cc'; apply H => abs.
move: (abs _ _ cC c'C cc'); by rewrite prefix_cc'.
Qed.

End prefix_code.

Section example_of_code.

Variable (n' : nat) (t' : nat).
Let n := n'.+1.
Let t := t'.+2.
Let T := [finType of 'I_t].
Variable l : seq nat.
Hypothesis l_n : size l = n.
Hypothesis sorted_l : sorted leq l.
Hypothesis Hl : forall i : 'I_n, nth O l i != 0.
Let lmax := last O l.

(* see mceliece sect. 11.2, theorem 11.2 *)
Definition w (j : 'I_n) :=
  \sum_(i < j) #|T| ^ (nth 0 l j - nth 0 l i).

Lemma wE0 : w ord0 = 0.
Proof. by rewrite /w big_ord0. Qed.

Lemma w_eq0 i : (w i == 0) = (i == ord0).
Proof.
apply/idP/idP => [|/eqP ->]; last by rewrite wE0.
apply: contraTT => i0.
rewrite {1}/w sum_nat_eq0 negb_forall.
have @zero : 'I_i by exists 0; rewrite lt0n.
by apply/existsP; exists zero => /=; rewrite expn_eq0 card_ord.
Qed.

Lemma injective_w : injective w.
Proof.
move=> i j; case/boolP : (w i == 0); rewrite w_eq0 => i0.
  rewrite (eqP i0) wE0.
  case/boolP : (w j == 0); rewrite w_eq0 => j0; first by rewrite (eqP j0).
  by move/esym/eqP; rewrite w_eq0 (negbTE j0).
case/boolP : (w j == 0) => [|]; rewrite w_eq0 => j0.
  by rewrite (eqP j0) wE0 => /eqP; rewrite w_eq0 (negbTE i0).
case/boolP : (i == j) => [/eqP //|ij].
wlog : i j i0 j0 ij / i < j.
  move=> Hwlog H.
  move: ij; rewrite neq_ltn => /orP[|] ij.
  - apply Hwlog => //; by move/negbT : (ltn_eqF ij).
  - apply/esym; apply Hwlog => //; by move/negbT : (ltn_eqF ij).
move=> {ij}ij /esym.
rewrite /w (bigID (fun i1 : 'I__ => i1 < i)) /=.
set a := (X in X + _ = _ -> _). set b := (X in _ = X -> _).
set c := (X in _ + X = _ -> _).
have ab : a >= b.
  rewrite {}/a {}/b big_ord_narrow; [by apply ltnW|move=> H].
  apply: leq_sum => k _.
  rewrite leq_exp2l ?card_ord // leq_sub //; apply nth_of_sorted => //.
  by rewrite H /= l_n.
have c0 : 0 < c.
  rewrite {}/c lt0n sum_nat_eq0 negb_forall.
  apply/existsP; exists (Ordinal ij); by rewrite /= ltnn /= expn_eq0 card_ord.
move=> acb; exfalso.
move/eqP/negP : acb; apply; apply/negP/negbT/gtn_eqF; by rewrite -addn1 leq_add.
Qed.

Lemma injective_ary_of_nat_w : injective (fun j => ary_of_nat t' (w j)).
Proof. by move=> i j /injective_ary_of_nat/injective_w. Qed.

Definition sigma (j : 'I_n) :=
  let x := ary_of_nat t' (w j) in
  nseq (nth 0 l j - size x) ord0 ++ x.

Lemma sigmaE0 : sigma ord0 = nseq (nth O l O) ord0 :> seq T.
Proof.
rewrite /sigma wE0 ary_of_nat0.
have [k Hk] : exists k, nth 0 l (@ord0 t) = k.+1.
  move: (Hl ord0); case: (nth 0 l ord0) => // k _; by exists k.
by rewrite Hk subn1 cat_nseq -[RHS]cats0 cat_nseq /= /ncons -iterSr.
Qed.

Lemma size_sigma (i : 'I_n) : w i < t ^ nth O l i -> size (sigma i) = nth O l i.
Proof.
move=> step1; by rewrite /sigma size_cat size_nseq subnK // size_ary_of_nat.
Qed.

Lemma injective_sigma : injective sigma.
Proof.
move=> i j; rewrite /sigma => /eqP ij; apply/eqP; move: ij.
apply: contraTT => ij.
apply/negP => /eqP.
move/(congr1 (@nat_of_ary t')).
rewrite !nat_of_ary_cat !(nat_of_ary_nseq0,mul0n,add0n).
by rewrite !ary_of_natK => /injective_w/eqP; apply/negP.
Qed.

Definition acode := [seq sigma i | i in 'I_n].

Lemma uniq_acode : uniq acode.
Proof. rewrite map_inj_uniq ?enum_uniq //; exact injective_sigma. Qed.

Definition ACode := CodeSet uniq_acode.

End example_of_code.

Section kraft_condition.

Local Notation "s ``_ i" := (nth O s i) (at level 4).

Variable R : rcfType.

Definition kraft_cond (T : finType) (l : seq nat) :=
  let n := size l in
  (\sum_(i < n) #|T|%:R ^- l``_i <= (1 : R))%R.

End kraft_condition.

Program Definition prepend (T : finType) (lmax : nat) (c : seq T) (t : (lmax - size c).-tuple T)
  : lmax.-tuple T := @Tuple _ _ (take lmax c ++ t) _.
Next Obligation.
rewrite size_cat size_take size_tuple.
case: ifPn.
  move/ltnW; rewrite -subn_eq0 => /eqP ->; by rewrite addn0.
rewrite -leqNgt => ?; by rewrite subnKC.
Qed.

Lemma injective_prepend (T : finType) (lmax : nat) (c : seq T) : injective (@prepend T lmax c).
Proof.
move=> /= a b [] /eqP.
rewrite eqseq_cat // => /andP[_ /eqP ab]; by apply val_inj.
Qed.

Import Num.Theory GRing.Theory.

Section prefix_implies_kraft_cond.

Variables (T : finType) (C : code_set T).
Let n := size C.
Let l := sort_sizes C.
Let lmax := last O l.

Lemma leq_lmax c : c \in C -> size c <= lmax.
Proof.
move=> cC.
apply sorted_leq_last.
  rewrite /l /sort_sizes; apply sort_sorted; exact: leq_total.
rewrite mem_sort; apply/mapP; by exists c.
Qed.

Definition subtree s :=
  if s \in C then [set x : lmax.-tuple T | prefix s x] else set0.

Lemma subtree_not_empty (i : 'I_n) : 0 < #|T| -> subtree (nth [::] C i) <> set0.
Proof.
move=> T0.
rewrite /subtree mem_nth //.
move/setP.
have [t Ht] : exists t : T, t \in T by move/card_gt0P : T0.
move/(_ (@prepend T lmax (nth [::] C i) [tuple of nseq _ t])).
rewrite !inE /prepend /= take_oversize ?prefix_cat //.
apply/leq_lmax/(nthP [::]); by exists i.
Qed.

Lemma card_subtree (c : seq T) : c \in C ->
  #| subtree c | = #|T| ^ (lmax - size c).
Proof.
move=> cC.
rewrite /subtree cC -card_tuple -(card_imset _ (@injective_prepend T lmax c)).
apply eq_card => /= t; rewrite !inE.
apply/idP/imsetP => /= [ct|/= [x _ ->{t}]].
  have @x : (lmax - size c).-tuple T.
    apply: (@Tuple _ _ (drop (size c) t)); by rewrite size_drop size_tuple.
  exists x => //; apply val_inj => /=.
  move: ct => /eqP {1}->.
  rewrite take_oversize ?cat_take_drop //.
  rewrite size_take size_tuple; by case: ifPn => // /ltnW.
by rewrite /prepend /= take_oversize ?prefix_cat // leq_lmax.
Qed.

Lemma disjoint_subtree (a b : seq T) (Hprefix : prefix_code C) :
  a \in C -> b \in C -> a != b ->
  subtree a :&: subtree b == set0.
Proof.
move=> aC bC ab; rewrite /subtree aC bC.
apply/set0Pn => -[/= s]; rewrite !inE => /andP[sa sb].
wlog : a b aC bC sa sb ab / prefix a b.
  move=> H.
  case: (prefix_common sa sb) => K; first exact: (H _ _ aC bC).
  apply: (H _ _ bC aC sb sa _ K); by rewrite eq_sym.
move/negP : (Hprefix _ _ aC bC ab); exact.
Qed.

Variable R : rcfType.

Local Notation "s ``_ i" := (nth [::] s i) (at level 4).

Lemma prefix_implies_kraft_cond : prefix_code C ->
  0 < #|T| -> kraft_cond R T (map size C).
Proof.
move=> prefixC T_gt0; rewrite /kraft_cond size_map -/n.
(*\color{comment}{\framebox{at this point, the goal is $\sum_{i < n} |T|^{-\ell_i} \leq 1$}} *)
have /ler_pmul2l <- : ((0 : R) < #|T|%:R ^+ lmax)%R.
  by rewrite exprn_gt0 // ltr0n.
rewrite mulr1 big_distrr /=. (*\color{comment}{\framebox{the goal is now $\sum_{i < n}\frac{|T|^{\ell_{\mathrm{max}}}}{#|T|^{\ell(i)}} \leq |T|^{\ell_{\mathrm{max}}}$}} *)
rewrite (eq_bigr (fun i : 'I_n => #|subtree C``_i|%:R)%R); last first.
  move=> i _; rewrite card_subtree; last by apply/nthP; exists i.
  rewrite natrX exprB // ?(nth_map [::]) //.
  by apply/leq_lmax/nthP; exists i.
  by rewrite unitfE pnatr_eq0 -lt0n.
(*\color{comment}{\framebox{the goal is now $\sum_{i < n} | \{ x | \prefix{c_i}{x} \} | \leq |T|^{\ell_{\mathrm{max}}}$}} *)
apply (@ler_trans _ (#|\bigcup_(i < n) subtree (C ``_ i)|%:R)%R).
  set P := [set (subtree C``_(nat_of_ord i)) | i in 'I_n].
  rewrite (@card_partition _ P); last first.
    rewrite /partition cover_imset eqxx /=; apply/andP; split; last first.
      apply/imsetP => -[i _ /esym]; by apply: subtree_not_empty.
    apply/trivIsetP => /= x y /imsetP[i _ ->] /imsetP[j _ ->] ij.
    rewrite -setI_eq0 disjoint_subtree //; [apply/nthP; by exists i |
      apply/nthP; by exists j | by apply: contra ij => /eqP ->].
  rewrite big_imset /= ?natr_sum // => i j _ _ Hij.
  apply/eqP/negPn/negP => ij.
  have Ci : C ``_ i \in C by apply/nthP; exists i.
  have Cj : C ``_ j \in C by apply/nthP; exists j.
  have : C ``_ i != C ``_ j by rewrite nth_uniq //; case: C.
  move/(disjoint_subtree prefixC Ci Cj).
  rewrite Hij setIid => /eqP/subtree_not_empty; exact.
(*\color{comment}{\framebox{the goal is now $\left| \bigcup_{i < n} \{ x | \prefix{c_i}{x} \} \right| \leq |T|^{\ell_{\mathrm{max}}}$}} *)
by rewrite -natrX -card_tuple ler_nat max_card.
Qed.

End prefix_implies_kraft_cond.

Section kraft_code.

Variable (n' : nat) (t' : nat).
Let n := n'.+1.
Let t := t'.+2.
Let T := [finType of 'I_t].
Variable l : seq nat.
Hypothesis l_n : size l = n.
Hypothesis sorted_l : sorted leq l.
Hypothesis Hl : forall i : 'I_n, nth O l i != 0.
Let lmax := last O l.

Variable R : rcfType.

Local Notation "'w'" := (@w n' t' l).

Lemma w_ub (H : kraft_cond R T l) j : w j <= #|T|^(nth O l j) - 1.
Proof.
have H' : (\sum_(i < n) #|T|%:R^-(nth O l i) <= (1 : R))%R.
  move: H; by rewrite /kraft_cond (_ : size l = n).
rewrite -(@ler_nat R) -(@ler_pmul2l _ (#|T|%:R ^- nth O l j))%R; last first.
  by rewrite -exprVn exprn_gt0 // invr_gt0 ltr0n card_ord.
case/boolP : (j == ord0) => [/eqP ->|i0].
  by rewrite wE0 mulr0 mulr_ge0 // -exprVn exprn_ge0 // invr_ge0 ler0n.
rewrite !natrB ?expn_gt0 ?card_ord // -!natrX.
rewrite mulrBr mulVr ?unitfE ?mulr1 ?pnatr_eq0 ?expn_eq0 //.
rewrite /w // natr_sum big_distrr /=.
rewrite (eq_bigr (fun j : 'I__ => #|T|%:R ^-nth O l j))%R; last first.
  move=> i _; rewrite !natrX card_ord exprB; last 2 first.
    by apply nth_of_sorted => //; rewrite ltnW //= l_n.
    by rewrite unitfE pnatr_eq0.
  by rewrite mulrA mulVr ?unitfE -?natrX ?pnatr_eq0 ?expn_eq0 // mul1r.
rewrite ler_subr_addr natrX (ler_trans _ H') //.
rewrite [X in (X <= _)%R](_ : _ = \sum_(k < j.+1) #|T|%:R^-nth O l k)%R; last first.
  by rewrite big_ord_recr /= card_ord.
rewrite (@big_ord_widen _ _ _ j.+1 n (fun i => #|T|%:R ^- nth O l i))%R //.
rewrite [in X in (_ <= X)%R](bigID (fun k : 'I_n => k < j.+1)) /= ler_addl.
rewrite sumr_ge0 // => k _; by rewrite invr_ge0 exprn_ge0 // ler0n.
Qed.

Lemma w_sub (H : kraft_cond R T l) j : w j < #|T|^(nth O l j).
Proof.
by rewrite (leq_ltn_trans (w_ub H j)) // subn1 card_ord prednK // expn_gt0.
Qed.

Local Notation "'C'" := (@ACode n' t' _ l_n sorted_l).
Local Notation "'sigma'" := (@sigma n' t' l).

Lemma if_not_prefix (H : kraft_cond R T l) : ~ prefix_code C ->
  [exists j : 'I_n, [exists k : 'I_n, (j < k) && prefix (sigma j) (sigma k)]].
Proof.
move/prefix_codeP => notprefix; move: (w_ub H) => w_ub.
rewrite -(negbK ([exists j, _])) negb_exists.
apply/negP => /forallP /= H'.
apply notprefix => c c'.
move/mapP => [/= a _ ->{c}] /mapP[/= b _ ->{c'}] ab size_ab.
apply/negP => prefix_ab.
move: (H' a).
rewrite negb_exists => /forallP/(_ b); rewrite prefix_ab andbT -leqNgt => ba.
move: size_ab; rewrite leqNgt => /negP; apply.
rewrite ltn_neqAle; apply/andP; split.
  by rewrite eq_sym ltn_eqF // prefix_neq_size.
rewrite size_sigma //; last by rewrite -/t -(card_ord t) w_sub.
rewrite size_sigma //; last by rewrite -/t -(card_ord t) w_sub.
by rewrite nth_of_sorted // ba l_n /=.
Qed.

End kraft_code.

Section kraft_cond_implies_prefix.

Variable (n' : nat) (t' : nat).
Let n := n'.+1.
Let t := t'.+2.
Let T := [finType of 'I_t].
Variable l : seq nat.
Hypothesis l_n : size l = n.
Hypothesis sorted_l : sorted leq l.
Hypothesis l_neq0 : forall i : 'I_n, nth O l i != 0.
Let lmax := last O l.

Variable R : rcfType.

Local Notation "'w'" := (@w n' t' l).

Local Notation "s ``_ i" := (nth O s i) (at level 4).

Lemma kraft_implies_prefix : kraft_cond R T l ->
  exists C : code_set T, prefix_code C.
Proof.
move=> H; exists (ACode _ l_n sorted_l).
apply nnpp_prefix.
move=> /(if_not_prefix l_neq0 H) /existsP[j /existsP[ k /andP[jk pre]]].
(*\color{comment}{\framebox{at this point, the goal is $\forall j, k. i < k \to \neg \prefix{\sigma_j}{\sigma_k$}}} *)
pose r := ((w k)%:R / #|T|%:R^+(l``_k - l``_j) : R)%R.
(*\color{comment}{\framebox{let $r = w_k / |T|^{\ell_k - \ell_j}$}} *)
have H1 : (r >= (w j)%:R + (1 : R))%R. (*\color{comment}{\framebox{here we prove $ r \geq w_j + 1$}} *)
  pose r' := (\sum_(i < k) #|T|%:R ^+ l``_j * #|T|%:R ^- l``_i : R)%R.
  (*\color{comment}{\framebox{let $r' = \sum_{i < k} |T|^{\ell_j}|T|^{-\ell_i}$ }} *)
  have -> : r = r'. (*\color{comment}{\framebox{here we prove $r = r'$, see Eqn (\ref{eqn:kraft_converse1}) }} *)
    rewrite /r /r' natr_sum big_distrl /=; apply/eq_bigr => i _.
    have ? : (#|T|%:R ^+ (l ``_ k - l ``_ j) : R)%R \is a GRing.unit.
      by rewrite unitfE expf_eq0 card_ord pnatr_eq0 andbF.
    apply: (@mulIr _ (#|T|%:R ^+ (l``_k - l``_j))%R) => //.
    rewrite natrX -mulrA mulVr // mulr1 exprB; last 2 first.
      by rewrite nth_of_sorted // ltnW //= l_n.
      by rewrite unitfE pnatr_eq0 card_ord.
    rewrite exprB; last 2 first.
      by rewrite nth_of_sorted // ltnW //= l_n.
      by rewrite unitfE pnatr_eq0 card_ord.
    rewrite mulrCA mulrAC mulrV // ?mul1r //.
    by rewrite unitfE -natrX pnatr_eq0 expn_eq0 card_ord.
  pose u := (\sum_(j<=i<k) #|T|%:R ^+ l``_j * #|T|%:R ^- l``_i : R)%R.
  (*\framebox{\color{comment}{let $u = \sum_{j \leq i < k} |T|^{\ell_j}|T|^{-\ell_i}$}} *)
  have -> : (r' = (w j)%:R + u :> R)%R. (* \color{comment}{\framebox{$r' = w_j + u$, Eqn (\ref{eqn:kraft_converse2})}} *)
    pose f := (fun i : nat => #|T|%:R^+l``_j * #|T|%:R^-l``_i : R)%R.
    case/boolP : (j == ord0) => j0.
      rewrite /u (eqP j0) wE0 add0r big_mkord /r'.
      apply/eq_bigr => i _; by rewrite (eqP j0).
    rewrite /r' /u -(big_mkord xpredT f)%R natr_sum.
    rewrite (eq_bigr (fun i : 'I__ => f i)); last first.
      move=> i _; rewrite natrX exprB //.
      by rewrite nth_of_sorted // ltnW //= l_n.
      by rewrite unitfE pnatr_eq0 card_ord.
    by rewrite -(big_mkord xpredT f)%R -big_cat_nat //= ltnW.
  rewrite ler_add //.
  (*\color{comment}{\framebox{at this point, the subgoal is $1 \leq u$, for the step (\ref{eqn:kraft_converse2})-(\ref{eqn:kraft_converse3})}} *)
  rewrite /u -(@prednK k); last by rewrite (leq_ltn_trans _ jk).
  rewrite big_nat_recl; last by move/(leq_sub2r 1) : jk; rewrite !subn1.
  rewrite divrr ?unitfE -?natrX ?pnatr_eq0 ?expn_eq0 ?card_ord //.
  rewrite ler_addl sumr_ge0 // => i _.
  by rewrite natrX divr_ge0 // exprn_ge0 // ?card_ord ?ler0n.
have H2 : (r - 1 < (w j)%:R)%R. (* \color{comment}{\framebox{here we prove $r - 1 < w_j$}} *)
  have /(congr1 (fun x => x%:R : R)%R) : w k =
    w j * #|T| ^ (l``_k - l``_j) + w k %% #|T| ^ (l``_k - l``_j).
    (*\color{comment}{\framebox{here we prove $w_k = w_j |T|^{\ell_k - \ell_j} +w_k \bmod |T|^{\ell_k-\ell_j}$, leading to (\ref{eqn:kraft_converse5})}} *)
    have := prefix_modn pre.
    do 2 rewrite nat_of_ary_cat nat_of_ary_nseq0 mul0n add0n ary_of_natK.
    by rewrite !size_cat !size_nseq !subnK // size_ary_of_nat // -/t
     -(card_ord t) (w_sub l_n sorted_l H).
  rewrite natrD => /(congr1 (fun x => x / #|T|%:R^+(l``_k - l``_j)))%R.
  rewrite -/r mulrDl natrM natrX mulrK; last first.
    by rewrite unitfE expf_eq0 card_ord pnatr_eq0 andbF.
  move=> wkE.
  have : ((w k %% #|T| ^ (l``_k - l``_j))%:R /
          #|T|%:R ^+ (l``_k - l``_j) < (1 : R))%R.
    (*\color{comment}{\framebox{here we prove $(w_k \bmod |T|^{\ell_k-\ell_j}) / |T|^{\ell_k - \ell_j} < 1$, leading to (\ref{eqn:kraft_converse6})}} *)
    rewrite ltr_pdivr_mulr; last by rewrite -natrX ltr0n expn_gt0 card_ord.
    by rewrite mul1r -natrX ltr_nat ltn_mod expn_gt0 card_ord.
  by rewrite {}wkE ltr_sub_addl addrC ltr_add2r.
by rewrite ltr_subl_addl addrC ltrNge H1 in H2.
Qed.
End kraft_cond_implies_prefix.

(* wip *)
Section cw.

Variables (n : nat) (T : Type).

Structure cw_of : Type := Cw {cwval :> seq T; _ : size cwval <= n}.

Lemma cwval_inj : injective cwval.
Proof.
move=> [a Ha] [b Hb] /= H.
move: Ha Hb; rewrite H => Ha Hb.
congr Cw.
exact: eq_irrelevance.
Qed.

Canonical cw_subType := Eval hnf in [subType for cwval].

End cw.

Notation "n .-cw" := (cw_of n) (at level 2, format "n .-cw") : type_scope.

Section canonical.

Variable n : nat.

Definition cw_eqMixin (T : eqType) := Eval hnf in [eqMixin of n.-cw T by <:].
Canonical cw_eqType (T : eqType) := Eval hnf in EqType (n.-cw T) (cw_eqMixin T).
Canonical cw_predType (T : eqType) := Eval hnf in mkPredType (fun t : n.-cw T => mem_seq t).
Definition cw_choiceMixin (T : choiceType) := [choiceMixin of n.-cw T by <:].
Canonical cw_choiceType (T : choiceType) :=
  Eval hnf in ChoiceType (n.-cw T) (cw_choiceMixin T).
Definition cw_countMixin (T : countType) := [countMixin of n.-cw T by <:].
Canonical cw_countType (T : countType) :=
  Eval hnf in CountType (n.-cw T) (cw_countMixin T).
Canonical cw_subCountType (T : countType) := Eval hnf in [subCountType of n.-cw T].

End canonical.

Program Definition cw0 n (T : finType) : n.-cw T := @Cw n T [::] _.

Definition cw_of_tuple n (T : finType) (t : seq T) : n.-cw T :=
  match Bool.bool_dec (size t <= n) true with
    left H => Cw H | right _ => @cw0 n T
  end.

Lemma enumP n (T : finType) : Finite.axiom
  (flatten (map (fun m => map (@cw_of_tuple n _) (map (@tval _ _) (enum {: m.-tuple T}))) (iota 0 n.+1))).
Proof.
case=> x xn.
rewrite count_uniq_mem.
  rewrite -/(nat_of_bool true); congr (nat_of_bool _).
  apply/flattenP.
  exists ([seq cw_of_tuple n i | i <- map (@tval _ _) (enum {:(size x).-tuple T})]) => //.
    apply/mapP; exists (size x) => //; by rewrite mem_iota leq0n add0n ltnS.
  apply/mapP; exists x.
    apply/mapP; exists (in_tuple x) => //; by rewrite mem_enum inE.
  rewrite /cw_of_tuple; case: Bool.bool_dec => // ?; congr Cw; exact: eq_irrelevance.
Admitted.

Canonical cw_finMixin n (T : finType) := Eval hnf in FinMixin (@enumP n T).
Canonical cw_finType n (T : finType) := Eval hnf in FinType (n.-cw T) (cw_finMixin n T).
Canonical cw_subFinType n (T: finType) := Eval hnf in [subFinType of n.-cw T].

Section code_cw.

Variable T : finType.

Record code_set_cw M := CodeSetCw {
  codesetcw :> {set M.-cw T}
}.

Definition code_set_cw_of_code_set (c : code_set T) : code_set_cw (foldr maxn O (map size c)).
Proof.
set M := foldr maxn O (map size c).
pose l : seq (M.-cw T) := map (@cw_of_tuple M T) (codeset c).
apply CodeSetCw.
exact: [set x | x in l].
Defined.

Definition code_set_of_code_set_cw M (c : code_set_cw M) : code_set T.
set x := enum (codesetcw c).
pose l : seq (seq T) := map (@cwval _ _) x.
apply CodeSet with l.
rewrite map_inj_uniq.
by rewrite enum_uniq.
exact: cwval_inj.
Defined.

End code_cw.
