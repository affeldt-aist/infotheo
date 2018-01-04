From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype tuple bigop finset path ssralg.
From mathcomp Require Import fingroup zmodp poly ssrnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

End prefix.

Lemma sorted_nth (l : seq nat) : sorted leq l -> forall i j,
  i <= j < size l -> nth O l i <= nth O l j.
Proof.
elim: l => [/= _ i j|h t IH Ht]; first by rewrite ltn0 andbF.
move/pathP : (Ht) => H; move/path_sorted in Ht.
case => [/= [// | j /=] | i /= [// | j]].
  rewrite ltnS => jt.
  eapply leq_trans; last by apply: (IH Ht O); rewrite leq0n jt.
  eapply leq_trans; last by apply H; rewrite (leq_ltn_trans _ jt).
  done.
rewrite !ltnS => ijt.
eapply leq_trans; first by apply: (IH _ _ j).
done.
Qed.

Lemma empty_finType_nil (T : finType) : (#|T| = 0) -> forall c : seq T, c = [::].
Proof. move/card0_eq => T0; by case=> // h; move: (T0 h); rewrite !inE. Qed.

Section code.

Variable T : finType.

Record code_set := CodeSet {
  codeset :> seq (seq T) ;
  _ : uniq codeset
}.

Definition mem_code_set (C : code_set) := fun x => x \in codeset C.
Canonical code_set_predType := Eval hnf in @mkPredType _ code_set mem_code_set.

Definition sizes (C : code_set) : seq nat := sort leq (map size C).

Lemma sorted_sizes C : sorted leq (sizes C).
Proof. apply sort_sorted; exact: leq_total. Qed.

Lemma size_sizes C : size (sizes C) = size C.
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
  forall c c', c \in C -> c' \in C -> c != c' ->
  size c <= size c' -> ~~ prefix c c'.

End prefix_code.

Section kraft_inequality_wip.

Variables (T : finType).
Variable C : code_set T.
Let n := size C.
Let ls := sizes C.
Let lmin := nth O ls O.
Let lmax := last O ls.

Lemma leq_lmax c : c \in C -> size c <= lmax.
Proof.
move=> cC.
have : size c \in sizes C by rewrite /sizes mem_sort; apply/mapP; exists c.
case/(nthP O) => i Hi <-.
rewrite /lmax /ls -nth_last.
apply sorted_nth; first by apply sort_sorted; exact: leq_total.
move: Hi; case: (size _) => //= m; by rewrite ltnS => -> /=.
Qed.

Definition subtree s :=
  if s \in C then [set x : lmax.-tuple T | prefix s x] else set0.

Hypothesis Hprefix : prefix_code C.

Lemma disjoint_subtree (a b : seq T) : a \in C -> b \in C -> a != b ->
  subtree a :&: subtree b == set0.
Proof.
move=> aC bC ab; rewrite /subtree aC bC.
apply/set0Pn => -[/= s]; rewrite !inE => /andP[sa sb].
wlog : a b aC bC sa sb ab / prefix a b.
  move=> H.
  case: (prefix_common sa sb) => K; first exact: (H _ _ aC bC).
  apply: (H _ _ bC aC sb sa _ K); by rewrite eq_sym.
case/boolP : (size a <= size b); first by move/(Hprefix aC bC ab)/negP; auto.
by rewrite -ltnNge => H /prefixW => /(_ ab); rewrite ltnNge leq_eqVlt H orbT.
Qed.

Program Definition prepend (c : seq T) (t : (lmax - size c).-tuple T)
  : lmax.-tuple T := @Tuple _ _ (take lmax c ++ t) _.
Next Obligation.
rewrite size_cat size_take size_tuple.
case: ifPn.
  move/ltnW; rewrite -subn_eq0 => /eqP ->; by rewrite addn0.
rewrite -leqNgt => ?; by rewrite subnKC.
Qed.

Lemma injective_prepend (c : seq T) : injective (@prepend c).
Proof.
move=> /= a b [] /eqP.
rewrite eqseq_cat // => /andP[_ /eqP ab]; by apply val_inj.
Qed.

Lemma subtree_not_empty (i : 'I_n) : 0 < #|T| -> subtree (nth [::] C i) <> set0.
Proof.
move=> T0.
rewrite /subtree mem_nth //.
move/setP.
have [t Ht] : exists t : T, t \in T by move/card_gt0P : T0.
move/(_ (@prepend (nth [::] C i) [tuple of nseq _ t])).
rewrite !inE /prepend /= take_oversize ?prefix_cat //.
apply/leq_lmax/(nthP [::]); by exists i.
Qed.

Lemma card_subtree (c : seq T) : c \in C ->
  #| subtree c | = #|T| ^ (lmax - size c).
Proof.
move=> cC.
rewrite /subtree cC -card_tuple -(card_imset _ (@injective_prepend c)).
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

Import Num.Theory GRing.Theory.

Lemma prefix_implies_kraft (R : rcfType) : 0 < #|T| ->
  (\sum_(i < n) #|T|%:R^-(size (nth [::] C i)) <= (1 : R))%R.
Proof.
move=> T0.
have : ((0 : R) < #|T|%:R ^+ lmax)%R .
  rewrite exprn_gt0 => //; by rewrite ltr0n.
move/ler_pmul2l => <-.
rewrite big_distrr /= mulr1.
rewrite [X in (X <= _)%R](_ : _ = \sum_(i < n) #|subtree (nth [::] C i)|%:R)%R; last first.
  apply/eq_bigr => i _.
  rewrite card_subtree; last by apply/(nthP [::]); exists i.
  rewrite natrX exprB // ?unitfE ?pnatr_eq0 -?lt0n //.
    apply/leq_lmax/(nthP [::]); by exists i.
rewrite [X in (X <= _)%R](_ : _ = #|\bigcup_(i < n) subtree (nth [::] C i)|%:R)%R; last first.
  set P := [set (subtree (nth [::] C (nat_of_ord i))) | i in 'I_n].
  rewrite (@card_partition _ P); last first.
    rewrite /partition cover_imset eqxx /=; apply/andP; split.
      apply/trivIsetP => /= x y /imsetP[i _ ->] /imsetP[j _ ->] ij.
      rewrite -setI_eq0 disjoint_subtree //.
      apply/(nthP [::]); by exists i.
      apply/(nthP [::]); by exists j.
      by apply: contra ij => /eqP ->.
    apply/imsetP => -[i _ /esym]; by apply: subtree_not_empty.
  rewrite big_imset /=; last first.
    move=> i j _ _ Hij.
    apply/eqP/negPn/negP => ij.
    have Hi : nth [::] C i \in C by apply/(nthP [::]); exists i.
    have Hj : nth [::] C j \in C by apply/(nthP [::]); exists j.
    have Kij : nth [::] C i != nth [::] C j by rewrite nth_uniq //; case: C.
    move: (disjoint_subtree Hi Hj Kij).
    rewrite Hij setIid => /eqP/subtree_not_empty; by apply.
  rewrite (@big_morph _ _ (fun a => a%:R)%R 0%R (fun a b => a + b)%R O) //; exact: natrD.
by rewrite -natrX -card_tuple ler_nat max_card.
Qed.

End kraft_inequality_wip.
