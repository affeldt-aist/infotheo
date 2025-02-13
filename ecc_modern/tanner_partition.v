(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg perm zmodp.
From mathcomp Require Import matrix.
From mathcomp Require Import Rstruct.
Require Import ssr_ext subgraph_partition tanner f2.

(**md**************************************************************************)
(* # Cover/partition properties of Tanner graphs                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.
Local Open Scope ring_scope.

Lemma trivIsetS_f (A B : finType) (f : A -> B) (AA : {set {set A}})
    (BB : {set {set B}}) :
    (forall a, a \in AA -> exists b, b \in BB /\ a = [set a' | f a' \in b]) ->
  trivIset BB -> trivIset AA.
Proof.
move=> /= Hsub.
move/trivIsetP => Hdisj.
apply/trivIsetP => /= x y Hx Hy.
rewrite -setI_eq0.
case: (Hsub _ Hx) => x' [] x'Q ->.
case: (Hsub _ Hy) => y' [] y'Q -> xy.
have {xy} : x' != y' by apply: contra xy => /eqP ?; subst y'.
move/(Hdisj _ _ x'Q y'Q).
rewrite -setI_eq0 => /eqP abs.
apply/eqP/setP => /= m0.
rewrite in_set0.
move/setP : abs => /(_ (f m0)).
rewrite in_set0 => /negbT.
rewrite inE negb_and !inE.
case/orP; move/negbTE => -> //; by rewrite andbF.
Qed.

Section tanner_rel_no_hypo.
Variables (m n : nat) (H : 'M['F_2]_(m, n)).

Local Notation "''V'" := (Vnext H).
Local Notation "''F'" := (Fnext H).
Local Notation "''V(' x ',' y ')'" := (Vgraph H x y).
Local Notation "''F(' x ',' y ')'" := (Fgraph H x y).

Lemma Vgraph_decompose n1 m0 n0 : n0 \in 'V m0 ->
  n1 \in 'V(m0, n0) -> n1 != n0 -> n1 \notin 'V m0 -> exists n1',
  n1' \in 'V m0 :\ n0 /\ exists m1, m1 \in 'F n1' :\ m0 /\
    n1 \in 'V(m1, n1').
Proof.
move=> m0n0 Hn1 n1n0 n1Vm0.
rewrite !inE (negbTE n1n0) /= in Hn1.
case/andP : Hn1 => _.
case/connectP => /= q Hq Hq'.
case/shortenP : Hq Hq' => /= p Hp Huniq pq Hp'.
destruct p as [|[?|n1'] p]; [by [] | by rewrite exceptE /= tanner_relE in Hp | ].
rewrite /= in Hp'.
rewrite /= {1}exceptE /= -andbA in Hp.
case/and3P : Hp => m0n1' n1'n0 Hp.
have n1n1' : n1 != n1'.
  apply/eqP => ?; subst n1'.
  by move: n1Vm0; rewrite VnextE sym_tanner_rel m0n1'.
destruct p as [|[m1|?] t]; [ | | by rewrite exceptE /= tanner_relE in Hp ].
  exfalso; move/negP : n1n1'; apply.
  by case: Hp' => ->.
move: Hp; rewrite /= {1}exceptE; case/andP => /and3P[/= m1n1' _ _] Hp.
exists n1'.
rewrite !inE /=.
split.
  rewrite VnextE sym_tanner_rel m0n1' andbT.
  by apply: contra n1'n0 => /eqP ->.
exists m1; split.
  rewrite in_setD1 FnextE VnextE m1n1' andbT.
  apply/eqP => ?; subst m1.
  by rewrite !inE /= eqxx /= in Huniq.
rewrite !inE /= (negbTE n1n1') /= m1n1' /=.
apply/connectP; exists t => //.
apply: (sub_path_except _ _ Hp) => //.
case/andP : Huniq => _.
rewrite -(cat1s (inr _)) -(cat1s (inl m1)).
by rewrite uniq_catCA cat_uniq => /and3P[_ _ /= /andP[]].
Qed.

End tanner_rel_no_hypo.

Section acyclic_tanner_rel.
Variables (m n : nat) (H : 'M['F_2]_(m, n)).

Local Notation "''V'" := (Vnext H).
Local Notation "''F'" := (Fnext H).
Local Notation "''V(' x ',' y ')'" := (Vgraph H x y).
Local Notation "''F(' x ',' y ')'" := (Fgraph H x y).

Hypothesis Hacyclic : acyclic (tanner_rel H).

Lemma notin_Vgraph n1 m0 n0 m1 : n0 \in 'V m0 ->
  n1 \in 'V m0 :\ n0 -> m1 \in 'F n1 :\ m0 ->
  n0 \notin 'V(m1, n1).
Proof.
move=> n0m0 Hn1 Hm1.
rewrite in_setD1 in Hn1; case/andP : Hn1 => n1n0 n1m0.
rewrite in_setD1 in Hm1; case/andP : Hm1 => m1m0 m1n1.
suff : inr n0 \notin subgraph (tanner_rel H) (inl m1) (inr n1).
  move=> ?.
  by rewrite /Vgraph inE negb_or in_set1 eq_sym n1n0 /= inE.
apply: (@notin_subgraph _ (tanner_rel H) _ _ _ _ (inl m0)) => //.
exact: sym_tanner_rel.
exact: simple_tanner_rel.
by rewrite /= -VnextE.
by rewrite /= -VnextE.
by rewrite /= -VnextE -FnextE.
Qed.

Lemma Vgraph_inclusion n1 m0 n0 m1 n2 : n0 \in 'V m0 ->
  n1 \in 'V m0 :\ n0 -> m1 \in 'F n1 :\ m0 ->
  n2 \in 'V(m1, n1) -> n2 \in 'V(m0, n0).
Proof.
move=> n0m0 Hn1 Hm1 Hn2.
rewrite !inE.
case/boolP : (n2 == n0) => //= n2n0.
rewrite -VnextE n0m0 /=.
rewrite !inE /= in Hn2.
case/orP : Hn2 => Hn2.
  move/eqP in Hn2; subst n2.
  apply connect1 => /=.
  move: (Hn1); rewrite in_setD1 exceptE /= -VnextE => /andP[_ -> /=].
  by apply: contra n2n0 => /eqP [] ->.
case/andP : Hn2 => m1n1 Hn2.
case/connectP : Hn2 => p.
case/shortenP => p' Hp' Hun p'p Hlast.
apply/connectP.
exists [:: inr n1, inl m1 & p'] => //.
rewrite /=.
rewrite !inE /= in Hn1.
case/andP : Hn1 => n1n0 Hn1.
rewrite {1 2}exceptE /= -VnextE Hn1 /= m1n1 /=.
apply/andP; split.
  by apply: contra n1n0 => /eqP [] ->.
apply/andP; split.
  rewrite andbT.
  by apply: contra n1n0 => /eqP [] ->.
apply (@sub_path_except _ _ (inr n1)) => //.
apply/negP => n0p'.
case/splitPr : n0p' => p1 p2 in Hp' Hun p'p Hlast.
suff : path.ucycle (tanner_rel H) [:: inr n0, inl m0, inr n1, inl m1 & p1].
  exact: Hacyclic.
apply: uniq_path_ucycle_extend_2 => //.
exact: sym_tanner_rel.
exact: simple_tanner_rel.
by rewrite /= -VnextE.
by rewrite /= -VnextE.
apply/eqP; case => ?; subst m1; by rewrite in_setD1 eqxx in Hm1.
rewrite -(cat1s (inr n0)) catA cats1 cat_path in Hp'; by case/andP : Hp'.
rewrite -(cat1s (inl m1)) catA cat_uniq in Hun; by case/andP : Hun.
Qed.

End acyclic_tanner_rel.

Section tanner_partition.
Variables (m n : nat).
Variable H : 'M['F_2]_(m, n).

Local Notation "''V'" := (Vnext H).
Local Notation "''F'" := (Fnext H).
Local Notation "''V(' x ',' y ')'" := (Vgraph H x y).
Local Notation "''F(' x ',' y ')'" := (Fgraph H x y).

Definition Fgraph_part_fnode (n0 : 'I_n) : {set {set 'I_m}} :=
  (fun m => 'F(m, n0)) @: ('F n0).

Hypothesis Hconnect : forall a b, connect (tanner_rel H) a b.

Lemma cover_Fgraph_part_fnode (n0 : 'I_n) : cover (Fgraph_part_fnode n0) = setT.
Proof.
apply/setP => /= m1; rewrite in_set.
apply/bigcupP => /=.
have : inl m1 \in cover ([set inr n0] |: subgraph_succ (tanner_rel H) (inr n0)).
move: (cover_subgraph_succ (tanner_rel H) (inr n0)) => /setP/(_ (inl m1)) ->.
  by rewrite inE Hconnect.
case/bigcupP => /= E HE m1_in_E.
rewrite in_setU1 in HE.
move/orP: HE => [HE | ].
  by rewrite (eqP HE) in_set1 in m1_in_E.
case/imsetP => /= p Hp HE.
rewrite HE in_set in m1_in_E.
rewrite in_set in Hp.
case: p HE Hp m1_in_E => p HE /= Hp m1_in_E; last by rewrite tanner_relE in m1_in_E.
exists [set m0 | inl m0 \in E].
  apply/imsetP => /=.
  exists p.
    by rewrite FnextE VnextE.
  apply/setP => /= m0.
  by rewrite HE !inE.
by rewrite HE !in_set.
Qed.

Definition Vgraph_part_vnode (n0 : 'I_n) : {set {set 'I_n}} :=
  (fun m => 'V(m, n0) :\ n0) @: ('F n0).

Lemma notin_Vgraph_part_vnode (n0 : 'I_n) : n0 \notin cover (Vgraph_part_vnode n0).
Proof.
apply/bigcupP => /=; case=> E /imsetP [] /= m0 Hm0 ->; by rewrite 2!inE eqxx.
Qed.

Lemma cover_Vgraph_part_vnode (n0 : 'I_n) : cover (Vgraph_part_vnode n0) = setT :\ n0.
Proof.
apply/setP => /= n1.
rewrite !inE andbT.
case/boolP : (n1 == n0) => [ /eqP -> | n1n0] /=.
  exact/negbTE/notin_Vgraph_part_vnode.
apply/bigcupP => /=.
have : inr n1 \in cover ([set inr n0] |: subgraph_succ (tanner_rel H) (inr n0)).
  by rewrite (cover_subgraph_succ (tanner_rel H) (inr n0)) inE Hconnect.
case/bigcupP => /= p.
rewrite !inE.
case/orP => [ /eqP -> | ].
  rewrite inE.
  case/eqP => abs; by rewrite abs eqxx in n1n0.
case/imsetP => /=; case=> p1; last by rewrite inE tanner_relE.
move=> Hp1 pp1 n1p.
exists ('V(p1, n0) :\ n0).
  apply/imsetP => /=.
  exists p1 => //.
  rewrite inE /= -VnextE in Hp1.
  by rewrite FnextE.
rewrite !inE n1n0 /= predU1r //.
by rewrite pp1 inE in n1p.
Qed.

Hypothesis Hacyclic : acyclic (tanner_rel H).

Lemma trivIset_Fgraph_part_fnode (n0 : 'I_n) : trivIset (Fgraph_part_fnode n0).
Proof.
have K : trivIset (subgraph_succ (tanner_rel H) (inr n0)).
  exact: trivIsetS _ (subsetUr _ _)
    (trivIset_subgraph_succ (simple_tanner_rel H) (sym_tanner_rel H) Hacyclic (inr n0)).
apply: trivIsetS_f K => /= z.
case/imsetP => /= i Hi Hz.
exists [set x | x in subgraph (tanner_rel H) (inl i) (inr n0)].
split.
  apply/imsetP.
  exists (inl i).
    by rewrite inE /= -VnextE -FnextE.
  apply/setP => /= j.
  move Hlhs : (j \in _) => [|]; first by case/imsetP : Hlhs => /= k kz ->.
  apply/esym/negbTE.
  move/negbT : Hlhs; apply contra => Hlhs.
  apply/imsetP.
  by exists j.
apply/setP => /= j.
rewrite inE.
move Hlhs : (j \in z) => [|].
  apply/esym/imsetP.
  exists (inl j) => //.
  by rewrite Hz /Fgraph inE in Hlhs.
apply/esym/negbTE.
move/negbT : Hlhs; apply contra.
case/imsetP => /= p Hp ?; subst p.
by rewrite Hz inE.
Qed.

Lemma trivIset_Vgraph_part_vnode n0 : trivIset (Vgraph_part_vnode n0).
Proof.
have : trivIset (subgraph_succ (tanner_rel H) (inr n0)).
  exact: trivIsetS _ (subsetUr _ _) (trivIset_subgraph_succ
    (simple_tanner_rel H) (sym_tanner_rel H) Hacyclic (inr n0)).
apply: trivIsetS_f => /= z.
case/imsetP => /= i Hi Hz.
exists [set x | x in (subgraph (tanner_rel H) (inl i) (inr n0))].
split.
  apply/imsetP.
  exists (inl i).
    by rewrite inE /= -VnextE -FnextE.
  apply/setP => /= j.
  move Hlhs : (j \in _) => [|]; first by case/imsetP : Hlhs => /= k kz ->.
  apply/esym/negbTE.
  move/negbT : Hlhs; apply contra => Hlhs.
  apply/imsetP.
  by exists j.
apply/setP => /= j.
move Hlhs : (j \in z) => [|].
  rewrite inE.
  apply/esym/imsetP => /=.
  exists (inr j) => //.
  rewrite Hz !inE in Hlhs.
  case/andP : Hlhs => jn0.
  case/orP => jn0'.
    by rewrite (negbTE jn0) in jn0'.
  by rewrite inE.
apply/esym/negbTE.
move/negbT : Hlhs; apply contra.
rewrite inE.
case/imsetP => /= p Hp ?; subst p.
rewrite Hz !inE.
apply/andP; split.
  apply/negP => /eqP ?; subst j.
  move: Hp; apply/negP.
  apply (root_notin_subgraph (simple_tanner_rel _)).
  by rewrite inE /= -VnextE -FnextE.
rewrite inE in Hp.
by rewrite Hp orbT.
Qed.

(* NB: Lemma Vgraph_inclusion n1 m0 n0 m1 n2 : n0 \in `V m0 ->
  n1 \in `V m0 :\ n0 -> m1 \in `F n1 :\ m0 ->
  n2 \in `V(m1, n1) -> n2 \in `V(m0, n0).
=> do not need the n2 \in `V(m0, n0) hypo
*)

Lemma disjoint_Vgraph2 m0 n0 n1 n2 m1 (m0n0 : n0 \in 'V m0) :
  n1 \in 'V m0 :\ n0 ->
  n2 \in 'V(m0, n1) :\ n1 ->
  m1 \in 'F n1 :\ m0 ->
  n2 \in 'V(m1, n1) ->
  n2 \notin 'V m0 ->
  n2 \in 'V(m0, n0) -> Logic.False.
Proof.
move=> Hn1 Hn2 Hm1 H1 H2 H3.
move: (trivIset_Vgraph_part_vnode n1).
move/trivIsetP.
move/(_ ('V(m0, n1) :\ n1) ('V(m1,n1) :\ n1)).
rewrite /Vgraph_part_vnode.
have K1 : 'V(m0, n1) :\ n1 \in [set 'V(m2, n1) :\ n1 | m2 in 'F n1].
  apply/imsetP.
  exists m0 => //.
  by move: Hn1; rewrite in_setD1 -FnextE => /andP[].
move/(_ K1).
have K2 : 'V(m1, n1) :\ n1 \in [set 'V(m2, n1) :\ n1 | m2 in 'F n1].
  apply/imsetP.
  exists m1 => //.
  rewrite inE in Hm1.
  by case/andP : Hm1.
move/(_ K2).
have K3 : 'V(m0, n1) :\ n1 != 'V(m1, n1) :\ n1.
  have K4 : n0 \in 'V(m0, n1) :\ n1.
    rewrite !inE.
    rewrite !inE in Hn1.
    case/andP : Hn1 => n1n0 m0n1.
    rewrite eq_sym n1n0 /= -VnextE (negbTE n1n0) /= m0n1 /=.
    apply/connect1.
    rewrite exceptE /= -VnextE m0n0 /=.
    by apply: contra n1n0 => /eqP[->].
  have K5 : n0 \notin 'V(m1, n1) :\ n1.
    rewrite !inE negb_and negbK negb_or /=.
    rewrite !inE in Hn1.
    case/andP : Hn1 => n1n0 m0n1.
    rewrite eq_sym (negbTE n1n0) /= negb_and.
    rewrite !inE in Hm1.
    apply/orP; right.
    apply/negP.
    case/connectP => p.
    case/shortenP => p' Hp' Hun pp' Hlast.
    suff : ucycle (tanner_rel H) (inl m0 :: inr n1 :: inl m1 :: p').
      exact: Hacyclic.
    apply: uniq_path_ucycle_extend_1 => //.
    exact: simple_tanner_rel.
    by rewrite /= -VnextE; case/andP : Hm1.
    by rewrite /= -VnextE -FnextE; case/andP : Hm1.
    rewrite rcons_path Hp' /= exceptE /= andbT -Hlast -VnextE m0n0 /=.
    apply/eqP; case => ?; subst n1.
    by rewrite in_setD1 eqxx in K4.
    rewrite rcons_uniq Hun andbT /= !inE /= negb_or.
    apply/andP; split.
      apply/eqP; case => ?; subst m1; by rewrite eqxx in Hm1.
    apply/negP => m0p.
    case/splitPr : m0p => p1 p2 in Hp' Hun pp' Hlast.
    suff : ucycle (tanner_rel H) (inl m0 :: inr n1 :: inl m1 :: p1) by apply Hacyclic.
    apply: uniq_path_ucycle_extend_1.
    exact: simple_tanner_rel.
    by rewrite /= -VnextE.
    rewrite /= -VnextE -FnextE; by case/andP : Hm1.
    rewrite -(cat1s (inl m0)) catA cat_path in Hp'.
    rewrite !cats1 in Hp'.
    by case/andP : Hp'.
    rewrite rcons_uniq.
    move: Hun.
    rewrite -cat_cons cat_uniq => /andP[->]; rewrite andbT.
    by rewrite /= negb_or -andbA => /and3P[].
  apply/eqP.
  move/setP/(_ n0).
  by rewrite K4 (negbTE K5).
move/(_ K3)/disjoint_setI0/setP/(_ n2).
rewrite inE Hn2 /= in_set0 in_setD1 H1.
rewrite in_setD1 in Hn2.
case/andP : Hn2.
by move=> -> _.
Qed.

Lemma Fgraph_injective n0 m0 m1 :
  n0 \in 'V m0 -> n0 \in 'V m1 -> 'F(m0, n0) = 'F(m1, n0) -> m0 = m1.
Proof.
move=> Hm0 Hm1 m0m1.
apply/eqP/negPn/negP => abs.
have : exists cy, (2 < size cy)%nat /\ ucycleb (tanner_rel H) cy.
  have : connect (except (tanner_rel H) (inr n0)) (inl m0) (inl m1).
    have : m0 \in 'F(m1, n0).
      by rewrite -m0m1 /Fgraph 2!inE connect0 andbT -VnextE.
    rewrite 2!inE /subgraph.
    case/andP => n0m1.
    rewrite connect_sym //; exact/symmetric_except/sym_tanner_rel.
  case/connectP => /= s H1 H2.
  case/shortenP : (H1) H2 => /= s' H1' H2' H3' H2.
  have [/= s1 [s2 s1s2]] : exists s1 s2, s' = s1 ++ inl m1 :: s2.
    have m1s : inl m1 \in s'.
      rewrite H2.
      destruct s' as [|h t].
        rewrite /= in H2.
        case: H2 => ?; subst m1; by rewrite eqxx in abs.
      by rewrite /= mem_last.
    case/(nthP (inl m0)) : m1s => i Hi im1.
    exists (take i s'), (drop i.+1 s').
    by rewrite -im1 -drop_nth // cat_take_drop.
  exists (inr n0 :: inl m0 :: s1 ++ [:: inl m1]).
  split.
    by rewrite /= size_cat /= addn1.
  apply/andP; split; last first.
    rewrite -/(uniq (inl m0 :: s')) s1s2 -cat1s catA -(cat1s (inl m1)) catA cat_uniq in H2'.
    case/andP : H2' => H2' H2''.
    rewrite cons_uniq H2' andbC /= inE /= mem_cat /= negb_or.
    apply/andP; split => //.
    apply/negP => abs'.
    have {}abs' : inr n0 \in s' by rewrite s1s2 mem_cat abs'.
    case/(nthP (inl m0)) : abs' => i Hi abs'.
    move/pathP : H1'.
    move/( _ (inl m0) _ Hi).
    by rewrite exceptE /= abs' eqxx andbA andbC.
  rewrite /cycle /=.
  rewrite -VnextE Hm0 /= rcons_path.
  apply/andP; split.
    rewrite s1s2 -cat1s catA cat_path in H1'.
    case/andP : H1' => H1' _; move: H1'.
    exact: except_path.
  by rewrite last_cat /= -VnextE.
case=> cy [] H1; exact: Hacyclic.
Qed.

Lemma Fgraph_disjoint n0 m0 m1 m2 :
  m2 \in 'F(m0, n0) -> m2 \in 'F(m1, n0) -> m0 = m1.
Proof.
move=> m3m1 m3m2.
case/boolP : (m0 == m1) => [/eqP //| m1m2].
exfalso.
move: (trivIset_Fgraph_part_fnode n0).
move/trivIsetP.
move/(_ 'F(m0, n0) 'F(m1, n0)).
have m1n1 : n0 \in 'V m0.
  apply: contraLR m3m1.
  move/Fgraph_nonempty/eqP => ->.
  by rewrite in_set0.
have m2n1 : n0 \in 'V m1.
  apply: contraLR m3m2.
  move/Fgraph_nonempty/eqP => ->.
  by rewrite in_set0.
have H1 : 'F(m0, n0) \in Fgraph_part_fnode n0.
  apply/imsetP; exists m0 => //; by rewrite FnextE.
have H2 : 'F(m1, n0) \in Fgraph_part_fnode n0.
  apply/imsetP; exists m1 => //; by rewrite FnextE.
move/(_ H1 H2) => {H1 H2}.
have HF : 'F(m0, n0) != 'F(m1, n0).
  apply: contra m1m2 => /eqP HF; apply/eqP; exact: Fgraph_injective HF.
move/(_ HF) => {HF}.
rewrite -setI_eq0 => /set0Pn; apply.
exists m2; by rewrite inE m3m1 m3m2.
Qed.

Lemma Vgraph_injective n0 m0 m1 :
  n0 \in 'V m0 -> n0 \in 'V m1 -> 'V(m0, n0) :\ n0 != set0 ->
  'V(m1, n0) :\ n0 != set0 -> 'V(m0, n0) :\ n0 = 'V(m1, n0) :\ n0 -> m0 = m1.
Proof.
move=> Hm0 Hm1 m0m1 H10 H20.
apply/eqP/negPn/negP => abs.
have : exists cy, (2 < size cy)%nat /\ ucycleb (tanner_rel H) cy.
  have : connect (except (tanner_rel H) (inr n0)) (inl m0) (inl m1).
    have : exists n1, n1 \in 'V(m1, n0) :\ n0 by apply/set0Pn.
    case=> n1 Hn1; move: (Hn1).
    rewrite !inE.
    case/andP => n1n0.
    case/orP => [/eqP ? | ]; first by subst n1; rewrite eqxx in n1n0.
    rewrite /subgraph => /andP [] n0m1 m1n1.
    have : connect (except (tanner_rel H) (inr n0)) (inl m0) (inr n1).
      move: Hn1; by rewrite -H20 !inE n1n0 /= (negbTE n1n0) /= => /andP[].
    move/connect_trans; apply.
    rewrite connect_sym //; exact/symmetric_except/sym_tanner_rel.
  case/connectP => /= s H1 H2.
  case/shortenP : (H1) H2 => /= s' H1' H2' H3' H2.
  have [/= s1 [s2 s1s2]] : exists s1 s2, s' = s1 ++ inl m1 :: s2.
    have m1s : inl m1 \in s'.
      rewrite H2.
      destruct s' as [|h t].
        rewrite /= in H2.
        case: H2 => ?; subst m1; by rewrite eqxx in abs.
      by rewrite /= mem_last.
    case/(nthP (inl m0)) : m1s => i Hi im1.
    exists (take i s'), (drop i.+1 s').
    by rewrite -im1 -drop_nth // cat_take_drop.
  exists (inr n0 :: inl m0 :: s1 ++ [:: inl m1]).
  rewrite /= size_cat /= addn1; split => //.
  apply/andP; split; last first.
    rewrite -/(uniq (inl m0 :: s')) s1s2 -cat1s catA -(cat1s (inl m1)) catA cat_uniq in H2'.
    case/andP : H2' => H2' H2''.
    rewrite cons_uniq H2' andbC /= inE /= mem_cat /= negb_or.
    apply/andP; split => //.
    apply/negP => abs'.
    have {}abs' : inr n0 \in s' by rewrite s1s2 mem_cat abs'.
    case/(nthP (inl m0)) : abs' => i Hi abs'.
    move/pathP : H1'.
    move/( _ (inl m0) _ Hi).
    by rewrite exceptE /= abs' eqxx !andbF.
  rewrite /cycle /=.
  rewrite -VnextE Hm0 /= rcons_path.
  apply/andP; split.
    rewrite s1s2 -cat1s catA cat_path in H1'.
    case/andP : H1' => H1' _; move: H1'.
    exact: except_path.
  by rewrite last_cat /= -VnextE.
case=> cy [] H1; exact: Hacyclic.
Qed.

Local Open Scope R_scope.

Lemma rprod_Fgraph_part_fnode g n0:
  \prod_(m0 < m) g m0 = \prod_(m0 in 'F n0) \prod_(m1 in 'F(m0, n0)) g m1 :> Rdefinitions.R.
Proof.
transitivity (\prod_(m0 in [set: 'I_m]) g m0).
  apply eq_bigl => /= ?; by rewrite in_set.
rewrite -(cover_Fgraph_part_fnode n0).
rewrite big_trivIset /=; last exact: trivIset_Fgraph_part_fnode.
rewrite big_imset // => //.
move=> m1 m2 Hm1 Hm2 /=.
apply Fgraph_injective => //; by rewrite -FnextE.
Qed.

Lemma disjoint_Vgraph (m0 m1 : 'I_m) (n1 n0 : 'I_n) : n1 != n0 -> m0 != m1 ->
  n1 \in 'V(m0, n0) -> n1 \notin 'V(m1, n0).
Proof.
move=> n1n0 m0m1 Hn1; apply/negP => Hm1.
have Hm0' : n0 \in 'V m0.
  apply: contraLR Hn1.
  move/Vgraph_set1 => ->; by rewrite in_set1.
have Hm1' : n0 \in 'V m1.
  apply: contraLR Hm1.
  move/Vgraph_set1 => ->; by rewrite in_set1.
have Hdiff : 'V(m0, n0) :\ n0 != 'V(m1, n0) :\ n0.
  move: m0m1; apply contra.
  move/eqP => abs; apply/eqP; move: abs.
  apply Vgraph_injective => //.
  apply/set0Pn; exists n1; by rewrite in_setD1 n1n0 Hn1.
  apply/set0Pn; exists n1; by rewrite in_setD1 n1n0 Hm1.
move: (trivIset_Vgraph_part_vnode n0).
move/trivIsetP.
move/(_ ('V(m0, n0) :\ n0) ('V(m1, n0) :\ n0)) => /= abs.
have : 'V(m0, n0) :\ n0 \in Vgraph_part_vnode n0.
  case: imsetP => // abs'.
  exfalso.
  apply abs'; exists m0 => //; by rewrite FnextE.
move/abs => {}abs.
have : 'V(m1, n0) :\ n0 \in Vgraph_part_vnode n0.
   case: imsetP => // abs'; exfalso.
   apply abs'; exists m1 => //; by rewrite FnextE.
move/abs => {}abs.
move: (abs Hdiff) => {abs}abs'.
move/disjoint_setI0 : abs' => abs'.
move: abs'; apply/eqP.
apply/set0Pn.
exists n1.
by rewrite in_setI in_setD1 n1n0 /= Hn1 /= in_setD1 n1n0 Hm1.
Qed.

Definition Fgraph_part_Fgraph m0 n0 : {set {set 'I_m}} :=
  (fun n1 => \bigcup_(m1 in 'F n1 :\ m0) 'F(m1, n1)) @: (('V m0) :\ n0).

Lemma cover_Fgraph_part_Fgraph m0 n0 : n0 \in 'V m0 ->
  cover (Fgraph_part_Fgraph m0 n0) = 'F(m0, n0) :\ m0.
Proof.
move=> Hn0.
have {Hn0}m0n0 : tanner_rel H (inl m0) (inr n0) by rewrite VnextE sym_tanner_rel in Hn0.
move: (cover_subgraph_succ2_D1 (sym_tanner_rel H) Hacyclic (simple_tanner_rel H) m0n0) => Hcover.
apply/setP => /= m1.
rewrite 2!inE.
move Hlhs : ( _ \in _ ) => [|].
  apply/esym.
  have Hm1 : inl m1 \in cover (subgraph_succ2_D1 m0n0).
    rewrite /Fgraph_part_Fgraph in Hlhs.
    case/bigcupP : Hlhs => /= i i1 i2.
    case/imsetP : i1 => /= n1 Hn1 i1.
    apply/bigcupP => /=.
    exists (inr n1 |: \bigcup_(m' in successors (tanner_rel H) (inr n1) :\ inl m0) (subgraph (tanner_rel H) m' (inr n1))).
      apply/imsetP => /=.
      exists (inr n1) => //.
      rewrite !inE /= -VnextE.
      rewrite !inE /= in Hn1.
      case/andP: Hn1 => Hn1 ->; rewrite andbT.
      by apply: contra Hn1 => /eqP Hn1; case: Hn1 => ->.
    rewrite !inE /=.
    apply/bigcupP => /=.
    rewrite i1 in i2.
    case/bigcupP : i2 => /= m2 Hm2 Hm1.
    exists (inl m2).
      rewrite !inE /=.
      rewrite !inE /= in Hm1.
      case/andP : Hm1 => -> _; rewrite andbT.
      apply/eqP => abs; case : abs => ?; subst m2.
      by rewrite !inE /= eqxx in Hm2.
    rewrite !inE /= in Hm1.
    by rewrite /subgraph !inE.
  rewrite Hcover 2!inE in Hm1.
  apply/andP; split.
    case/andP : Hm1 => Hm1 _.
    by apply: contra Hm1 => /eqP ->.
  case/andP : Hm1 => _ Hm1.
  by rewrite inE.
apply/esym/negbTE.
rewrite negb_and negbK.
case/boolP : (m1 == m0) => // m1m0 /=.
move/negbT : Hlhs; apply contra => Hlhs.
apply/bigcupP => /=.
rewrite inE in Hlhs.
rewrite /Fgraph_part_Fgraph.
rewrite !inE /= in Hlhs.
case/andP : Hlhs => Hlhs Hlhs'.
case/connectP : Hlhs' => /= p.
case/shortenP => p' Hp' Hun p'p Hlast.
case: p' Hp' Hun p'p Hlast => [|p1 p2] Hp' Hun p'p Hlast.
  rewrite /= in Hlast.
  case: Hlast => ?; subst m1.
  by rewrite eqxx in m1m0.
case: p1 Hp' Hun p'p Hlast => [|n1 Hp' Hun p'p Hlast].
  by rewrite exceptE /= tanner_relE.
exists (\bigcup_(m2 in 'F n1 :\ m0) 'F(m2, n1)).
  apply/imsetP.
  exists n1 => //.
  rewrite !inE.
  rewrite /= in Hp'.
  case/andP : Hp'.
  rewrite {1}exceptE /= -VnextE => /andP[H1 H2] _.
  rewrite H1 andbT.
  by apply: contra H2 => /eqP ->.
apply/bigcupP => /=.
case: p2 Hp' Hun p'p Hlast => [ // | [p2|p2] p'] Hp' Hun p'p Hlast; last first.
  by rewrite exceptE /= tanner_relE /= andbF in Hp'.
rewrite /= in Hp'.
case/andP : Hp' => H1 /andP [] H2 H3.
exists p2.
  rewrite !inE.
  apply/andP; split.
    apply/eqP => ?; subst p2.
    rewrite -(cat1s (inl m0)) -(cat1s (inr n1)) -[in X in _ ++ X](cat1s (inl m0)) in Hun.
    by rewrite catA uniq_catCA /= inE eqxx /= in Hun.
  by move/except_rel : H2; rewrite /= -VnextE -FnextE.
rewrite !inE.
rewrite (except_rel H2) /=.
apply/connectP; exists p' => //.
apply: sub_path_except H3 => //.
apply/negP => n1p'.
move: Hun.
rewrite -(cat1s (inl m0)) -(cat1s (inr n1)) -(cat1s (inl p2)) catA uniq_catCA.
by rewrite catA uniq_catC -!catA catA cat_uniq uniq_catC /= n1p'.
Qed.

Lemma trivIset_Fgraph_part_Fgraph m0 n0 : n0 \in 'V m0 ->
  trivIset (Fgraph_part_Fgraph m0 n0).
Proof.
move=> m0n0.
rewrite VnextE sym_tanner_rel in m0n0.
move: (@trivIset_subgraph_succ2_D1 _ _ (sym_tanner_rel H)
  Hacyclic (simple_tanner_rel H) (inl m0) (inr n0) m0n0) => K.
apply: (@trivIsetS_f _ _ inl) K => /= z.
rewrite /Fgraph_part_Fgraph.
case/imsetP => n1 Hn1 Hz.
rewrite /subgraph_succ2_D1.
exists (inr n1 |: \bigcup_(m1 in successors (tanner_rel H) (inr n1) :\ inl m0)
  (subgraph (tanner_rel H) m1 (inr n1))).
split.
  apply/imsetP => /=.
  exists (inr n1).
    rewrite !inE /= in Hn1.
    rewrite !inE /= -VnextE.
    case/andP : Hn1 => Hn1 ->.
    rewrite andbT.
    by apply: contra Hn1 => /eqP [] ->.
  by f_equal.
rewrite Hz.
apply/setP => /= m1.
apply/bigcupP.
case: ifP.
  rewrite 3!inE /=.
  case/bigcupP => /=.
  case=> [m2 Hm2 Hm1 | n2].
    exists m2 => //.
      rewrite in_setD1 FnextE.
      rewrite !inE /= -VnextE in Hm2.
      case/andP : Hm2 => Hm2 ->.
      rewrite andbT.
      by apply: contra Hm2 => /eqP ->.
    by rewrite inE.
  by rewrite !inE {2}tanner_relE.
rewrite !inE /=.
move/negbT/negP => abs' abs; apply abs' => {abs'}.
case: abs => m2 Hm Hm1.
apply/bigcupP => /=.
exists (inl m2).
  rewrite !inE /= -VnextE.
  rewrite in_setD1 FnextE in Hm.
  case/andP : Hm => Hm ->.
  rewrite andbT.
  by apply: contra Hm => /eqP [] ->.
by rewrite inE in Hm1.
Qed.

Lemma another_Fgraph_injective (m0 : 'I_m) (n0 n1 n2 : 'I_n)
  (Hn1 : n1 \in 'V m0 :\ n0) (Hn2 : n2 \in 'V m0 :\ n0) :
  'F n1 :\ m0 != set0 -> (* 'F n2 :\ m0 != set0 *)
  \bigcup_(m1 in 'F n1 :\ m0) 'F(m1, n1) = \bigcup_(m1 in 'F n2 :\ m0) 'F(m1, n2) ->
  n1 = n2.
Proof.
move=> Hset0.
move=> abs.
apply/eqP/negPn/negP => n1n2.
have {}Hset0 : \bigcup_(m1 in 'F n1 :\ m0) 'F(m1, n1) != set0.
  apply: contra Hset0; exact: bigcup_succ_set0.
case/set0Pn : Hset0 => /= m1 Habs.
move: (Habs).
case/bigcupP => /= m2 Hm2 Hm1.
rewrite !inE /= in Hm1.
case/andP : Hm1 => m2n1.
case/connectP => /= p.
case/shortenP => p' Hp' unp pp' lastp.
rewrite abs in Habs.
move: Habs.
case/bigcupP => /= m3 Hm3 Hm1'.
rewrite !inE /= in Hm1'.
case/andP : Hm1' => m3n2.
case/connectP => /= p0.
case/shortenP => p0' Hp0' unp0 p0p0' lastp0.
destruct p' as [|p'1 p'2].
  rewrite /= in lastp.
  case: lastp => ?; subst m2.
  suff : ucycle (tanner_rel H) (inr n1 :: inl m0 :: inr n2 :: inl m3 :: p0').
    exact: Hacyclic.
  apply: uniq_path_ucycle_extend_2.
  exact: sym_tanner_rel.
  exact: simple_tanner_rel.
  by [].
  by rewrite /= -VnextE; move: Hn2; rewrite in_setD1 => /andP[].
  by [].
  by rewrite /= -VnextE; move: Hn1; rewrite in_setD1 => /andP[].
  apply/eqP; case => ?; subst m3; by rewrite in_setD1 eqxx in Hm3.
  rewrite rcons_path Hp0' /= exceptE /= -lastp0 /= sym_tanner_rel m2n1 /=.
  by apply: contra n1n2 => /eqP [] ->.
  by [].
destruct p0' as [|p0'1 p0'2].
  rewrite /= in lastp0.
  case: lastp0 => ?; subst m3.
  suff : ucycle (tanner_rel H) (inr n2 :: inl m0 :: inr n1 :: inl m2 :: p'1 :: p'2).
    exact: Hacyclic.
  apply: uniq_path_ucycle_extend_3.
  exact: sym_tanner_rel.
  exact: simple_tanner_rel.
  by [].
  by move: Hp' => /= /andP[] /except_rel.
  by move: Hp' => /= /andP[] /except_rel.
  by rewrite /= -VnextE; move: Hn1; rewrite in_setD1 => /andP[].
  by rewrite /= -VnextE; move: Hn2; rewrite in_setD1 => /andP[].
  apply/eqP; case => ?; subst m2; by rewrite in_setD1 eqxx in Hm2.
  move/path_except_notin : Hp'; rewrite inE negb_or => /andP []; by rewrite eq_sym.
  by apply: contra n1n2 => /eqP [] ->.
  rewrite rcons_path; apply/andP; split.
    rewrite /= in Hp'.
    case/andP : (Hp') => Hp'1 Hp'2.
    apply: sub_path_except Hp'2.
      apply/eqP => ?; subst p'1.
      by move/andP : Hp'; rewrite exceptE /= {1}tanner_relE; case.
    apply/negP => m2p'2.
    move: unp.
    rewrite -(cat1s (inl m2)) -(cat1s p'1) uniq_catCA uniq_catC cat_uniq.
    case/andP => /andP []; by rewrite m2p'2.
  rewrite /= in lastp.
  rewrite /= exceptE /= andbT -lastp /= sym_tanner_rel m3n2 /=.
  apply/eqP; case => ?; subst m2.
  move: unp.
  by rewrite cons_uniq lastI mem_rcons inE -lastp /= eqxx.
  rewrite [p'1 :: _]lock /= -lock in unp; by case/andP : unp.
suff : ucycle (tanner_rel H)
  ((inl m1 :: rev (belast p0'1 p0'2)) ++ (inl m3 :: inr n2 :: inl m0 :: inr n1 :: inl m2 :: belast p'1 p'2)).
  apply Hacyclic; by rewrite size_cat addnC.
apply: uniq_path_ucycle_cat_extend; try assumption.
exact: sym_tanner_rel.
exact: simple_tanner_rel.
by rewrite /= -VnextE; move: Hn2; rewrite in_setD1 => /andP[].
by rewrite /= -VnextE; move: Hn1; rewrite in_setD1 => /andP[].
apply/eqP; case => ?; subst m3; by rewrite in_setD1 eqxx in Hm3.
apply/eqP; case => ?; subst m2; by rewrite in_setD1 eqxx in Hm2.
by rewrite lastp last_cons -lastI.
by rewrite lastp0 last_cons -lastI.
move: unp.
rewrite (cons_uniq (inl m2)) => /andP [] H1 H2.
rewrite cons_uniq.
apply/andP; split.
  apply: contra H1; by move/mem_belast.
rewrite lastI rcons_uniq in H2; by case/andP : H2.
move: unp0.
rewrite (cons_uniq (inl m3)) => /andP [] H1 H2.
rewrite cons_uniq.
apply/andP; split.
  apply: contra H1; by move/mem_belast.
rewrite lastI rcons_uniq in H2; by case/andP : H2.
Qed.

Lemma Vgraph_id n0 m0 n1 n1' m1 m1' n2 :
  n0 \in 'V m0 ->
  n1 \in 'V m0 :\ n0 -> n1' \in 'V m0 :\ n0 ->
  m1 \in 'F n1 :\ m0 -> m1' \in 'F n1' :\ m0 ->
  n2 \in 'V(m1, n1) ->
  n2 \in 'V(m1', n1') -> n1 = n1'.
Proof.
move=> Hn0 Hn1 Hn1' Hm1 Hm1'.
rewrite !inE.
case/orP => [/eqP ? |]; [subst n2|].
  case/orP => [/eqP ?|]; [by subst n1'|].
  case/andP => n1'm1'.
  case/connectP => /= p.
  case/shortenP => p' Hp' unp pp' lastp.
  exfalso.
  suff : path.ucycle (tanner_rel H) [:: inl m0, inr n1', inl m1' & p'].
    exact: Hacyclic.
  apply: uniq_path_ucycle_extend_1 => //.
  exact: simple_tanner_rel.
  by rewrite /= -VnextE; move: Hn1'; rewrite in_setD1 => /andP[].
  rewrite rcons_path /= Hp' /= exceptE /= -lastp andbT.
  apply/andP; split.
    by rewrite /= -VnextE; move: Hn1; rewrite in_setD1 => /andP[].
  apply/eqP; case => ?; subst n1'.
  move/path_except_notin : Hp'.
  destruct p' => //.
  rewrite /= in lastp.
  by rewrite lastI -lastp mem_rcons inE eqxx.
  rewrite rcons_uniq unp andbT inE negb_or.
  apply/andP; split.
    rewrite !inE in Hm1'.
    case/andP : Hm1' => Hm1' _.
    by apply: contra Hm1' => /eqP [] ->.
  apply/negP => Hx.
  case/splitPr : Hx => p1 p2 in Hp' unp pp' lastp.
  suff : ucycle (tanner_rel H) [:: inl m0, inr n1', inl m1' & p1].
    exact: Hacyclic.
  apply: uniq_path_ucycle_extend_1 => //.
  exact: simple_tanner_rel.
  by rewrite /= -VnextE; move: Hn1'; rewrite in_setD1 => /andP[].
  rewrite -(cat1s (inl m0)) catA cat_path in Hp'.
  rewrite cats1 in Hp'.
  by case/andP : Hp'.
  rewrite rcons_uniq.
  move: unp; rewrite -cat_cons cat_uniq => /andP[-> /=].
  by rewrite negb_or -andbA => /and3P[] ->.
case/andP => n1m1 /connectP /= [] p.
case/shortenP => p' Hp' unp pp' lastp.
case/orP => [/eqP ?|]; [subst n1'|].
  exfalso.
  suff : path.ucycle (tanner_rel H) [:: inl m0, inr n1, inl m1 & p'].
    exact: Hacyclic.
  apply: uniq_path_ucycle_extend_1 => //.
  exact: simple_tanner_rel.
  by rewrite /= -VnextE; move: Hn1; rewrite in_setD1 => /andP[].
  rewrite rcons_path Hp' /= -lastp exceptE /= andbT -VnextE.
  rewrite !inE in Hn1'.
  case/andP : Hn1' => n2n0 -> /=.
  apply/eqP; case => ?; subst n2.
  move/path_except_notin : Hp'.
  destruct p' => //.
  rewrite /= in lastp.
  by rewrite lastI mem_rcons -lastp inE eqxx.
  rewrite rcons_uniq unp andbT inE /= negb_or.
  apply/andP; split.
    apply/eqP; case => ?; subst m1.
    by rewrite in_setD1 eqxx in Hm1.
  apply/negP => Hx.
  case/splitPr : Hx => p1 p2 in Hp' unp pp' lastp.
  suff : ucycle (tanner_rel H) [:: inl m0, inr n1, inl m1 & p1] by exact: Hacyclic.
  apply: uniq_path_ucycle_extend_1 => //.
  exact: simple_tanner_rel.
  by rewrite /= -VnextE; move: Hn1; rewrite in_setD1 => /andP[].
  rewrite -(cat1s (inl m0)) catA cat_path in Hp'.
  rewrite cats1 in Hp'.
  by case/andP : Hp'.
  rewrite rcons_uniq.
  by move: unp; rewrite -cat_cons cat_uniq => /and3P[-> /=]; rewrite negb_or => /andP[->].
move: (Hm1'); rewrite !inE /= -VnextE -FnextE => /andP [] _ -> /=.
case/connectP => /= q.
case/shortenP => q' Hq' unq qq' lastq.
apply/eqP/negPn/negP => n1n1'.
case: p' Hp' unp pp' lastp => [// | p'1 p'2] Hp' unp pp' lastp.
elim/last_ind : q' Hq' unq qq' lastq => [// | q'1 q'2 _] Hq' unq qq' lastq.
rewrite last_rcons in lastq; subst q'2.
suff : ucycle (tanner_rel H) ((inr n2 :: rev q'1) ++ [:: inl m1', inr n1', inl m0, inr n1, inl m1 & belast p'1 p'2]).
  by apply Hacyclic; rewrite size_cat addnC.
apply: uniq_path_ucycle_cat_extend => //.
exact: sym_tanner_rel.
exact: simple_tanner_rel.
by rewrite /= -VnextE; move: Hn1'; rewrite in_setD1 => /andP[].
by rewrite /= -VnextE -FnextE; move: Hm1'; rewrite in_setD1 => /andP[].
by rewrite /= -VnextE; move: Hn1; rewrite in_setD1 => /andP[].
apply/eqP; case => ?; subst m1'; by rewrite in_setD1 eqxx in Hm1'.
apply/eqP; case => ?; subst m1; by rewrite in_setD1 eqxx in Hm1.
by rewrite lastp last_cons -lastI.
move: unp.
rewrite (lastI p'1) /= mem_rcons inE negb_or => /andP [] /andP [] H1 ->.
by rewrite rcons_uniq => /andP [].
move: unq.
rewrite /= mem_rcons inE negb_or => /andP [] /andP [] -> ->.
by rewrite rcons_uniq => /andP [] _ ->.
Qed.

Definition Vgraph_part_Vgraph m0 n0 : {set {set 'I_n}} :=
  (fun n1 => n1 |: (\bigcup_(m1 in 'F n1 :\ m0) ('V(m1, n1) :\ n1))) @: (('V m0) :\ n0).

Lemma cover_Vgraph_part_Vgraph m0 n0 : n0 \in 'V m0 ->
  cover (Vgraph_part_Vgraph m0 n0) = 'V(m0, n0) :\ n0.
Proof.
move=> Hn0.
have {Hn0}m0n0 : tanner_rel H (inl m0) (inr n0) by rewrite VnextE sym_tanner_rel in Hn0.
move: (cover_subgraph_succ2_D1 (sym_tanner_rel H) Hacyclic (simple_tanner_rel H) m0n0) => Hcover.
apply/setP => /= n1.
rewrite 2!inE.
move Hlhs : ( _ \in _ ) => [|].
  apply/esym.
  have Hn1 : inr n1 \in cover (subgraph_succ2_D1 m0n0).
    rewrite /Vgraph_part_Vgraph in Hlhs.
    case/bigcupP : Hlhs => /= i i1 i2.
    case/imsetP : i1 => /= n1' Hn1' i1.
    apply/bigcupP => /=.
    exists (inr n1' |: \bigcup_(m' in successors (tanner_rel H) (inr n1') :\ inl m0) (subgraph (tanner_rel H) m' (inr n1'))).
      apply/imsetP => /=.
      exists (inr n1') => //.
      rewrite !inE /= -VnextE.
      rewrite !inE /= in Hn1'.
      case/andP: Hn1' => Hn1' ->; rewrite andbT.
      by apply: contra Hn1' => /eqP Hn1'; case: Hn1' => ->.
    rewrite !inE /=.
    rewrite i1 !inE in i2.
    case/orP : i2.
      move/eqP => ->; by rewrite eqxx.
    case/bigcupP => /= m1 Hm1.
    rewrite in_setD1.
    case/andP => n1n1' Hn1.
    apply/orP; right.
    apply/bigcupP => /=.
    exists (inl m1).
      move: Hm1.
      rewrite in_setD1 /= in_setD1 inE /= -VnextE -FnextE.
      case/andP => Hm1 ->; rewrite andbT.
      by apply: contra Hm1 => /eqP [] ->.
    by rewrite inE in_set1 (negbTE n1n1') /= inE in Hn1.
  move: Hn1.
  rewrite Hcover in_setD1.
  case/andP => n1m0 Hn1.
  apply/andP; split.
    apply/eqP => ?; subst n1.
    move: Hn1.
    apply/negP/(root_notin_subgraph (simple_tanner_rel _)).
    by rewrite inE sym_tanner_rel.
  by rewrite 3!inE Hn1 orbT.
apply/esym/negbTE.
move/negbT : Hlhs; apply contra.
case/andP.
rewrite 2!inE.
move=> n1n0.
rewrite !inE (negbTE n1n0) orFb.
case/andP => _ Hn1.
apply/bigcupP => /=.
case/connectP : Hn1 => /= p.
case/shortenP.
case=> //.
case=> [|n2 p' Hp' Hun p'p Hlast]; first by rewrite exceptE tanner_relE.
exists (n2 |: \bigcup_(m1 in 'F n2 :\ m0) ('V(m1, n2) :\ n2)).
  apply/imsetP => /=.
  exists n2 => //.
  rewrite !inE /=.
  move: Hp'.
  rewrite /= exceptE /= -VnextE -andbA => /and3P[] -> tmp _.
  rewrite andbT.
  by apply: contra tmp => /eqP ->.
rewrite !inE.
case: (boolP (n1 == n2)) => //= n1n2.
apply/bigcupP.
case: p' Hp' Hun p'p Hlast => //.
  move=> _ _ _ [] ?; subst n2; by rewrite eqxx in n1n2.
case; last by rewrite exceptE /= tanner_relE /= andbF.
move=> m1 p' Hp' Hun p'p Hlast.
rewrite /= in Hp'.
case/andP : Hp' => H1 /andP [] H2 H3.
rewrite exceptE /= andbT -VnextE -FnextE in H2.
exists m1.
  rewrite !inE.
  case/andP : H2 => -> _.
  rewrite -(cat1s (inl m0)) -(cat1s (inr n2)) -(cat1s (inl m1)) in Hun.
  rewrite uniq_catCA uniq_catC /= in Hun.
  case/andP : Hun.
  rewrite inE negb_or.
  case/andP => Hun _ _.
  rewrite andbT.
  by apply: contra Hun => /eqP ->.
rewrite !inE (negbTE n1n2) /= -VnextE -FnextE.
case/andP : H2 => -> H2 /=.
apply/connectP; exists p'; last by [].
apply: sub_path_except H3 => //.
apply/negP => n2p'.
move: Hun.
rewrite -(cat1s (inl m0)) -(cat1s (inr n2)) -(cat1s (inl m1)) catA uniq_catCA.
by rewrite catA uniq_catC -!catA catA cat_uniq uniq_catC /= n2p'.
Qed.

Lemma trivIset_Vgraph_part_Vgraph m0 n0 : n0 \in 'V m0 ->
  trivIset (Vgraph_part_Vgraph m0 n0).
Proof.
move=> m0n0.
have {}m0n0 : tanner_rel H (inl m0) (inr n0) by rewrite VnextE sym_tanner_rel in m0n0.
move: (@trivIset_subgraph_succ2_D1 _ _ (sym_tanner_rel H)
  Hacyclic (simple_tanner_rel _) (inl m0) (inr n0) m0n0) => K.
apply: (@trivIsetS_f _ _ inr) K => /= z.
rewrite /Vgraph_part_Vgraph.
case/imsetP => /= n1 Hn1 Hz.
rewrite /subgraph_succ2_D1.
exists (inr n1 |: \bigcup_(m1 in successors (tanner_rel H) (inr n1) :\ inl m0)
  (@subgraph _ (tanner_rel H) m1 (inr n1))).
split.
  apply/imsetP => /=.
  exists (inr n1) => //.
  rewrite !inE /= in Hn1.
  rewrite !inE /= -VnextE.
  case/andP : Hn1 => Hn1 ->.
  rewrite andbT.
  by apply: contra Hn1 => /eqP [] ->.
rewrite Hz.
apply/setP => /= m1.
rewrite !inE.
case: (boolP (m1 == n1)) => [|m1n1] /=.
  move/eqP => ->; by rewrite eqxx.
rewrite (_ : inr m1 == _ = false) /=; last first.
  apply/negbTE.
  by apply: contra m1n1 => /eqP [] ->.
apply/bigcupP.
case: ifP.
  case/bigcupP => /=.
  case => [m2 | n2]; last by rewrite !inE {2}tanner_relE.
  rewrite 3!inE /=.
  case/andP => m2m0 m2n1 X.
  rewrite -VnextE -FnextE in m2n1.
  exists m2.
    rewrite !inE /= m2n1 andbT.
    by apply: contra m2m0 => /eqP ->.
  by rewrite in_setD1 m1n1 /= inE in_set1 (negbTE m1n1) orFb inE.
move/bigcupP => abs abs'; apply abs => {abs}.
case: abs' => m2 Hm2 Hm1 /=.
exists (inl m2).
  rewrite !inE /= -VnextE -FnextE.
  rewrite !inE /= in Hm2.
  case/andP : Hm2 => m2m0 ->.
  rewrite andbT.
  by apply: contra m2m0 => /eqP [] ->.
rewrite !inE (negbTE m1n1) /= in Hm1.
by rewrite !inE.
Qed.

Lemma Vgraph_injective3 (m0 : 'I_m) (n0 n1 n2 : 'I_n)
  (Hn1 : n1 \in 'V m0 :\ n0) (Hn2 : n2 \in 'V m0 :\ n0) :
  n1 |: (\bigcup_(m1 in 'F n1 :\ m0) ('V(m1, n1) :\ n1)) = n2 |: (\bigcup_(m1 in 'F n2 :\ m0) ('V(m1, n2) :\ n2)) ->
  n1 = n2.
Proof.
move=> abs.
apply/eqP/negPn/negP => abs'.
have [m1] : exists m1, (m1 \in 'F n1 :\ m0) && (n2 \in 'V(m1, n1) :\ n1).
  move/setP : abs.
  move/(_ n2) => abs.
  have {abs} : n2 \in n1 |: \bigcup_(m1 in 'F n1 :\ m0) ('V(m1, n1) :\ n1).
    by rewrite abs inE in_set1 eqxx.
  rewrite inE in_set1 eq_sym (negbTE abs') orFb.
  case/bigcupP => m1 Hm1 n2m1 .
  exists m1; by rewrite Hm1.
case/andP => m1n1.
rewrite in_setD1 eq_sym abs' /=.
rewrite inE.
rewrite in_set1 eq_sym (negbTE abs') /= 2!inE.
case/andP => _.
case/connectP => p.
case/shortenP => p' Hp unp pp' lastp.
suff : ucycle (tanner_rel H) [:: inl m0, inr n1, inl m1 & p'] by exact: Hacyclic.
apply: uniq_path_ucycle_extend_1.
exact: simple_tanner_rel.
by rewrite /= -VnextE; move: Hn1; rewrite in_setD1 => /andP[].
by rewrite /= -VnextE -FnextE; move: m1n1; rewrite in_setD1 => /andP[].
rewrite rcons_path Hp /= exceptE /= andbT -lastp.
apply/andP; split.
  by rewrite /= -VnextE; move: Hn2; rewrite in_setD1 => /andP[].
apply/eqP; case=> ?; subst n2; by rewrite eqxx in abs'.
rewrite rcons_uniq unp andbT inE negb_or.
apply/andP; split.
  apply/eqP; case => ?; subst m1; by rewrite in_setD1 eqxx in m1n1.
apply/negP => m0p'.
case/splitPr : m0p' => p'1 p'2 in Hp unp pp' lastp.
suff : ucycle (tanner_rel H) [:: inl m0, inr n1, inl m1 & p'1].
  exact: Hacyclic.
apply: uniq_path_ucycle_extend_1; try assumption.
exact: simple_tanner_rel.
by rewrite /= -VnextE; move: Hn1; rewrite in_setD1 => /andP[].
by rewrite /= -VnextE -FnextE; move: m1n1; rewrite in_setD1 => /andP[].
rewrite -(cat1s (inl m0)) catA cats1 cat_path in Hp; by case/andP : Hp.
rewrite rcons_uniq.
by move: unp; rewrite -cat_cons cat_uniq => /and3P[-> /=]; rewrite negb_or => /andP[->].
Qed.

End tanner_partition.
