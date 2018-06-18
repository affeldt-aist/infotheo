(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg perm zmodp matrix path.
From mathcomp Require Import fingraph.

Require Import ssr_ext.

(** * Bipartite/acyclic graphs, cover/partition properties *)

(** OUTLINE:
- Section colorable.
- Section bipartite.
- Section simple.
- Section acyclic.
- Section graph_class.
- Section subgraph.
- Section first_partition.
- Section second_partition.
- Section path_ext.
- Section third_partition.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section colorable.

Variable (V : eqType) (g : rel V).

Definition colorable n (coloring : V -> 'I_n) :=
  forall v w, coloring v = coloring w -> ~~ g v w.

Lemma colorable_path_kind n (kind : V -> 'I_n) :
  colorable kind -> forall t h, path g h t -> forall i h0,
  i < size t -> kind (nth h0 (h :: t) i) != kind (nth h0 (h :: t) i.+1).
Proof.
move=> Hcol; elim => // h [_ h0 /andP[h0h _] i h1|h1 t IH h0].
  rewrite ltnS leqn0 => /eqP -> /=; apply/eqP => /Hcol; by rewrite h0h.
rewrite [h1 :: t]lock /= -lock => /andP[eh0h hh1t] [|[/= _ _|i h0']].
  move=> /= _ _; apply/eqP => /Hcol; by rewrite eh0h.
  by apply/eqP => /Hcol; move: hh1t => /= /andP[-> _].
rewrite /= ltnS; move/IH: hh1t; by apply.
Qed.

End colorable.

Section bipartite.

Variable (V : eqType) (g : rel V) (kind : V -> 'I_2).

Lemma bipartite_path_kind_next : colorable g kind ->
  forall t h, path g h t ->
  forall i h0, i < (size t).-1 ->
  kind (nth h0 (h :: t) i) = kind (nth h0 (h :: t) i.+2).
Proof.
move=> Hcol [//|t1 [//|t2 t3]] h /= /and3P[ht1 t1t2 t2t3] i h0 it3.
have H : path g h [:: t1, t2 & t3] by rewrite /= ht1 t1t2.
move/(colorable_path_kind Hcol) : (H) => /= /(_ i.+1 h0).
rewrite ltnS it3 => /(_ isT) /= H1; apply/eqP.
move/(colorable_path_kind Hcol)  : H => /= /(_ i h0).
rewrite ltnS ltnW // => /(_ isT); move: (kind _) (kind _) (kind _) H1.
by move=> -[] [|[|a]] ? -[] [|[|b]] ? // -[] [|[|c]] ?.
Qed.

Lemma bipartite_path_kind_even : colorable g kind ->
  forall i h0 t h, path g h t -> i <= (size t)./2 ->
  kind h = kind (nth h0 (h :: t) i.*2).
Proof.
move=> Hcol; elim=> // i IH h [//|t1 [//|t2 t3]] h0 ht it2.
rewrite -[in RHS]muln2 mulSn add2n muln2 -(bipartite_path_kind_next Hcol) //.
  apply IH => //; by rewrite (leq_trans _ it2).
move: it2 => /=.
rewrite ltnS -(@leq_pmul2r 2) // !muln2 => /leq_ltn_trans; apply.
by rewrite -{2}(odd_double_half (size t3)) ltnS leq_addl.
Qed.

Lemma bipartite_cycle_even cy :
  colorable g kind -> cycle g cy -> ~~ odd (size cy).
Proof.
case: cy => //= h t Hcol Hcycle; apply/negP => abs.
suff /Hcol : kind (last h t) = kind h.
  move: Hcycle; by rewrite rcons_path => /andP[_ ->].
apply/esym.
rewrite -nth_last (_ : nth _ _ _ = nth h (h :: t) (size t)); last by destruct t.
rewrite -(odd_double_half (size t)) (negbTE abs) add0n.
apply (bipartite_path_kind_even Hcol) => //.
move: Hcycle; by rewrite /= rcons_path => /andP[].
Qed.

End bipartite.

Section simple.

Variable (V : eqType) (g : rel V).

Definition simple := forall v, ~~ g v v.

Lemma simple_neg : simple -> forall v w, g v w -> v != w.
Proof. move=> H v w; apply: contraTN => /eqP ->; by apply H. Qed.

Lemma colorable_is_simple n (coloring : V -> 'I_n) : colorable g coloring -> simple.
Proof. by move=> H v; apply H. Qed.

End simple.

Section acyclic.

Variable (V : eqType) (g : rel V).

Definition acyclic := forall p, 2 < size p -> ~ path.ucycle g p.

Definition acyclic' := forall a b p,
  a \notin b :: p -> path.cycle g [:: a, b & p] -> last b p == b.

Lemma acyclic_equiv : acyclic' <-> acyclic.
Proof.
rewrite /acyclic' /acyclic; split => [Hac | ].
  case=> [// | a [// | b [// | c p _ /= /andP[Hcp]]]].
  rewrite [ [:: b, c & p] ]lock /= -lock => /andP[abcp].
  have /eqP H : last b (c :: p) == b by move/Hac : abcp; apply.
  by rewrite /= -H /= mem_last.
move=> Hac a b p Ha.
rewrite /cycle rcons_path => /andP [/=/andP[Hab Hp]].
case : {Hp}(shortenP Hp) => p' Hp' Hun Hmem Hla.
move: {Hac}(Hac [:: a, b & p']).
rewrite /ucycle /cycle {3}[b :: p']lock /= -lock Hun Hab rcons_path Hp' Hla.
rewrite (_ : a \notin b :: p'); last first.
  apply: contra Ha; rewrite !inE => /orP[/eqP ->|]; first by rewrite eqxx.
  move/Hmem; rewrite inE => ->; by rewrite orbT.
by destruct p' as [|p'1 p'2] => [//|/= /(_ isT)].
Qed.

End acyclic.

Module Colorable.
Section colorable.
Variable (V : finType).

Record graph (edge : rel V) n := {
  kind : V -> 'I_n ;
  prop : colorable edge kind }.

End colorable.
End Colorable.

Section graph_class.

Variable (V : finType).

Record simple_graph := {
  simple_edge :> rel V ;
  simple_prop : simple simple_edge }.

Definition simple_of_colorable (r : rel V) n : Colorable.graph r n -> simple_graph.
Proof. by case => kind; move/colorable_is_simple/Build_simple_graph. Defined.

End graph_class.

Section except.

Variables (V : eqType) (g : rel V).

Definition except n : rel V := locked [rel x y | [&& g x y, x != n & y != n]].

Lemma exceptE n : except n = [rel x y | [&& g x y, x != n & y != n]].
Proof. by rewrite /except; unlock. Qed.

Lemma except13 n h m : except n h m -> n != m.
Proof. by rewrite exceptE /= => /and3P[_ _]; rewrite eq_sym. Qed.

Lemma except_rel n h m : except n h m -> g h m.
Proof. by rewrite exceptE /= => /and3P[]. Qed.

Lemma symmetric_except x : symmetric g -> symmetric (except x).
Proof. by move=> sg ? ?; rewrite exceptE /= sg andbA andbAC -andbA. Qed.

Lemma exceptN n y : ~~ except n y n.
Proof. by rewrite exceptE /= !negb_and !negbK eqxx !orbT. Qed.

Lemma path_except n h t : n \notin h :: t -> path g h t -> path (except n) h t.
Proof.
move=> nt /pathP H.
apply/(pathP n) => i it; rewrite exceptE; apply/and3P; split; [by apply H | | ].
- apply: contra nt => /eqP <-.
  apply: mem_nth => /=; by rewrite ltnS ltnW.
- apply: contra nt => /eqP <-; by rewrite inE mem_nth ?orbT.
Qed.

Lemma except_path n h t : path (except n) h t -> path g h t.
Proof.
move/(pathP n) => H; apply/(pathP n) => i Hi; exact: (except_rel (H _ Hi)).
Qed.

Lemma path_except_notin n m l : path (except n) m l -> n \notin l.
Proof.
move=> Hpath; apply/negP => /(nthP m) [i il ni].
move/pathP : Hpath => /(_ m _ il); rewrite ni; apply/negP.
by rewrite exceptN.
Qed.

Lemma path_except_neq n m h l : m \in l -> path (except n) h l -> n != m.
Proof.
elim: l n m h => // a b IH n m h; rewrite in_cons => /orP[/eqP <-{a}|mb] /=.
  by case/andP => /except13.
by case/andP => H1 /(IH _ _ _ mb).
Qed.

Lemma sub_path_except n n' m t (n'm : n' != m) :
  n' \notin t -> path (except n) m t -> path (except n') m t.
Proof.
move=> n't => /(pathP m) H; apply/(pathP m) => i it.
move/H : (it); rewrite exceptE => /and3P[H1 _ _].
rewrite exceptE /= H1 /=.
apply/andP; split; last by apply: contra n't => /eqP <-; rewrite mem_nth.
move=> {H1}; case: i => [|i] in it *; first by apply: contra n'm => /eqP <-.
apply: contra n't => /eqP <-; by rewrite /= mem_nth // ltnW.
Qed.

End except.

Section subgraph.

Variables (V : finType) (g : rel V).

Lemma connect_except n w v : connect (except g n) w v -> connect g w v.
Proof.
case/connectP=> t wt ->{v}.
case/shortenP : wt => t' wt' Hun t't.
apply/connectP; exists t' => //.
by apply: sub_path wt' => x y /except_rel.
Qed.

Definition successors n := [set m | g n m].

Definition subgraph m n := [set v | g n m && connect (except g n) m v].

Lemma start_in_subgraph n m : g n m -> m \in subgraph m n.
Proof. by move=> gnm; rewrite /subgraph inE gnm /= connect0. Qed.

Lemma root_notin_subgraph (Hg : simple g) n m :
  m \in successors n -> n \notin subgraph m n.
Proof.
rewrite 2!inE => gnm; rewrite negb_and -implybE gnm implyTb.
apply/connectP => -[[_ /=| h s]].
- apply/eqP/negP => /eqP nm; move: gnm; rewrite nm; by apply/negP.
- move=> /path_except_notin => /negP ns nsm; apply ns.
  by rewrite nsm /= mem_last.
Qed.

Lemma subgraph_empty n m : ~~ g n m -> subgraph m n == set0.
Proof. move=> nm; apply/eqP/setP => i; by rewrite /subgraph /= (negbTE nm). Qed.

End subgraph.

(** First kind of partition: choose a root n and for each sucessor m,
    consider the partition formed by the subgraphs (m->n) (assuming
    acyclicity) *)
Section first_partition.

Variables (V : finType) (g : rel V).

Definition subgraph_succ (n : V) : {set {set V}} :=
  (fun m => subgraph g m n) @: successors g n.

Lemma cover_subgraph_succ n :
  cover ([set n] |: subgraph_succ n) = [set v | connect g n v].
Proof.
apply/setP => v; rewrite inE.
apply/idP/idP => [|nv].
  case/bigcupP => /= s; rewrite !inE => /orP[/eqP ->|].
    rewrite inE => /eqP ->; by rewrite connect0.
  case/imsetP => w; rewrite !inE => nw ->.
  rewrite /subgraph inE nw /= => wv.
  move/connect1 : nw => /connect_trans; apply.
  by apply: connect_except wv.
apply/bigcupP => /=.
case/connectP : nv => t /shortenP[t' nt' Hun t't] ->{v}.
case: t' => [|h t'] in nt' Hun t't *.
  by exists [set n]; rewrite !inE // eqxx.
exists (subgraph g h n).
  rewrite inE /subgraph_succ (mem_imset (fun x => subgraph g x n)) ?orbT //.
  rewrite inE; by case/andP : nt'.
rewrite !inE /=.
rewrite /= in nt'.
case/andP : nt' => -> ht' /=.
apply/connectP; exists t' => //.
apply path_except => //.
move: Hun; by rewrite [h :: t']lock /= -lock => /andP[].
Qed.

Lemma trivIset_subgraph_succ
  (simple : simple g) (undirected : symmetric g) (acyclic : acyclic g) n :
  trivIset ([set n] |: subgraph_succ n).
Proof.
apply/trivIsetP => s1 s2.
rewrite !inE => /orP[/eqP ->{s1}|].
  case/orP => [/eqP ->{s2}|]; first by rewrite eqxx.
  rewrite (@eq_disjoint1 _ n) //; last by move => ?; rewrite inE.
  case/imsetP => v Hv -> _; exact: root_notin_subgraph.
case/imsetP => m1 Hm1 ->{s1}.
case/orP => [/eqP ->|].
  rewrite disjoint_sym (@eq_disjoint1 _ n) //; last by move => ?; rewrite inE.
  move=> _; exact: root_notin_subgraph.
case/imsetP => m2 Hm2 ->{s2} s1s2.
rewrite !inE in Hm1 Hm2.
have m1m2 : m1 != m2 by apply/negP => /eqP m12; rewrite m12 eqxx in s1s2.
rewrite -setI_eq0 /subgraph.
apply/eqP/setP => x; rewrite !inE Hm1 Hm2 /=.
apply/andP; case; case/connectP => p Hp Hp'; subst x.
case/connectP => q.
have /eq_path -> : except g n =2 fun x y => [&& g y x, y != n & x != n].
  by move => x y /=; rewrite exceptE /= undirected  andbA andbAC -andbA.
rewrite -rev_path => Hq Hpq; move/andP : {Hp Hq} (conj Hp Hq).
rewrite -Hpq exceptE -cat_path -exceptE.
have : last m1 (p ++ rev (belast m2 q)) = m2.
  rewrite /rev.
  case: q Hpq => /=; first by rewrite cats0.
  by move => qh qt; rewrite catrevE !last_cat.
move=> H H0; move/shortenP: H0 H {Hpq} => [] [] //;
  first by move => /= _ _ _ ?; subst m1; move: m1m2; rewrite eqxx.
move => hd tl tl_path tl_uniq _ /= tl_last.
move: tl_path => /=; case/andP; rewrite {1}exceptE => /and3P[]; move => m1hd m1n hdn tl_path.
move: (acyclic (n :: m1 :: hd :: tl) erefl); apply.
rewrite /ucycle cons_uniq tl_uniq andbT inE negb_or eq_sym m1n andTb inE.
rewrite negb_or eq_sym hdn andTb (path_except_notin tl_path) andbT /=.
by rewrite Hm1 m1hd /= rcons_path (except_path tl_path) /= tl_last undirected.
Qed.

End first_partition.

(** Second kind of partition: choose a root n and a successor m,
    consider the partition formed by the subgraph (m->n') for each
    successor n' of m (n' <> n) *)
Section second_partition.

Variables (V : finType) (g : rel V).
Hypothesis symmetric_g : symmetric g.
Hypothesis acyclic_g : acyclic g.

Definition subgraph_succ_D1 (m n : V) : {set {set V}} :=
  (fun n' => subgraph g n' m) @: (successors g m :\ n).

Lemma cover_subgraph_succ_D1 (Hg : simple g) (m n : V) (gmn : g m n) :
  m |: cover (subgraph_succ_D1 m n) = subgraph g m n.
Proof.
apply/setP => v.
apply/idP/idP => Hlhs.
  rewrite in_setU1 in Hlhs.
  case/orP : Hlhs.
    move/eqP => ->; by rewrite start_in_subgraph // symmetric_g.
  case/bigcupP => /= vs.
  rewrite /subgraph_succ_D1.
  case/imsetP => succ_m Hsucc_m -> succ_m_m_v.
  rewrite /subgraph inE symmetric_g gmn /=.
  move: succ_m_m_v.
  rewrite /subgraph inE.
  case/andP => H1 H2.
  rewrite 3!inE in Hsucc_m.
  suff : connect (except g n) succ_m v.
    apply/connect_trans/connect1.
    rewrite exceptE /= H1 (simple_neg Hg) //=; by case/andP : Hsucc_m.
  case/connectP : H2 => l Hl Kl.
  case/shortenP : Hl => l' Hl' uniql' subpredl' in Kl.
  apply/connectP.
  exists l' => //.
  apply: sub_path_except (Hl') => //.
    case/andP : Hsucc_m; by rewrite eq_sym.
  apply/negP => nl'.
  suff : ucycle g ([:: n; m; succ_m] ++ take (index n l') l') by apply acyclic_g.
  apply/andP; split; last first.
    rewrite -cat1s -(cat1s m) -!catA catA cat_uniq; apply/and3P; split; last first.
      move: uniql' => /= /andP[K1 K2].
      by rewrite uniq_take // ?index_mem // andbT; apply: contra K1 => /mem_take.
    rewrite /= !inE /= !negb_or; case/andP : Hsucc_m => -> Hsucc_m /=.
    rewrite eq_sym (simple_neg Hg) //=.
    apply/hasPn => x /= Hx; rewrite !inE negb_or; apply/andP; split; last first.
      move/path_except_notin : Hl'; apply: contra => /eqP <-.
      by apply: mem_take Hx.
    apply: contraTN Hx => /eqP ->.
    by rewrite take_index.
    rewrite /= inE andbT; apply: contraTN nl' => /eqP ->.
    by apply (path_except_notin Hl').
  rewrite /= symmetric_g gmn /= H1 /= rcons_path.
  apply/andP; split.
    move: Hl'; by rewrite -{1}(cat_take_drop (index n l') l') cat_path => /andP[/except_path].
  move: Hl'.
  rewrite -{1}(cat_take_drop (index n l').+1 l') (take_nth n) // ?index_mem //.
  rewrite cat_path => /andP[]; rewrite exceptE rcons_path => /andP[_ /and3P[]].
  by rewrite nth_index.
rewrite /subgraph inE symmetric_g gmn /= in Hlhs.
rewrite !inE.
case/boolP : (v == m) => //= vm.
apply/bigcupP => /=.
rewrite /subgraph_succ_D1.
case/connectP : Hlhs => t.
case/shortenP.
case => [_ /= _ _ ? | h t' /=].
  by subst v; rewrite eqxx in vm.
case/andP; rewrite {1}exceptE /= => /and3P[mh mn hn] H4 Hun t't vt.
exists (subgraph g h m).
  by rewrite (mem_imset (subgraph g ^~ m)) // !inE hn.
rewrite /subgraph inE mh /=.
apply/connectP; exists t' => //.
case/andP : Hun; rewrite inE negb_or => /andP[m_neq_h mt'] _.
exact: sub_path_except H4.
Qed.

End second_partition.

Section path_ext.

Variable (V : finType).

Lemma uniq_extend_1 m n m' (l : seq V) (mn : m != n) (nm' : n != m') (nl : n \notin l)
  (Hun : uniq (m' :: l ++ m :: nil)) : uniq [:: m, n, m' & l].
Proof.
move: (Hun) => Hun'.
move: Hun; rewrite -cat_cons cat_uniq => /andP[Hunl Hun2].
rewrite -(cat1s m) -(cat1s n) catA cat_uniq Hunl andbT.
apply/andP; split; first by rewrite /= andbT inE.
apply/hasPn => x; rewrite /= !inE.
case/orP => [/eqP ->{x}| xl].
  rewrite (eq_sym _ n) (negbTE nm') orbF; apply: contraTN Hun' => /eqP ->.
  by rewrite /= mem_cat inE eqxx orbT.
apply: contra nl => /orP[/eqP ?|/eqP <- //]; subst x.
move: Hun'; by rewrite /= cat_uniq /= xl /= 2!andbF.
Qed.

Variable (g : rel V).
Hypothesis symmetric_g : symmetric g.
Hypothesis simple_g : simple g.

Lemma uniq_path_ucycle_extend_1 m n m' l (mn : g m n) (nm' : g n m')
  (Hl : path (except g n) m' (l ++ m :: nil)) (Hun : uniq (m' :: l ++ m :: nil)) :
  ucycle g [:: m, n, m' & l].
Proof.
apply/andP; split.
  rewrite /= mn nm' /=; move: Hl; by rewrite cats1 => /except_path.
apply uniq_extend_1 => //; try by rewrite (simple_neg simple_g).
by move: Hl; rewrite cat_path => /andP[/path_except_notin].
Qed.

Hypothesis acyclic_g : acyclic g.

Lemma uniq_path_ucycle_extend_2 m n m' l n1 (nm : g m n) (nm' : g n m') (mn1 : g m n1)
  (m'm : m' != m) (Hl : path (except g n) m' (l ++ n1 :: nil))
  (Hun : uniq (m' :: l)) : ucycle g [:: n1, m, n, m' & l].
Proof.
apply/andP; split.
  rewrite /= symmetric_g mn1 nm nm' /=.
  by move: Hl; rewrite cats1 => /except_path.
move: (Hun) => Hun'.
rewrite -(cat1s m) -(cat1s n) catA -(cat1s n1) catA cat_uniq Hun' andbT.
have n1m : n1 != m by rewrite (simple_neg simple_g) // symmetric_g.
have n1n : n1 != n.
  rewrite cat_path in Hl.
  case/andP : Hl => _ /=.
  by rewrite andbT => /except13; rewrite eq_sym.
have mn : m != n by rewrite (simple_neg simple_g).
apply/andP; split.
  by rewrite /= !inE negb_or andbT n1m /= n1n.
apply/hasP; case => x.
rewrite inE.
case/orP => [ | Hx].
  move/eqP => ?; subst x.
  rewrite /= !inE.
  apply/negP.
  rewrite 2!negb_or (@eq_sym _ m' n) (simple_neg simple_g nm') andbT.
  apply/andP; split => //.
  apply/eqP => ?; subst m'.
  suff : ucycle g [:: m; n; n1] by apply acyclic_g.
  by rewrite /ucycle /= !inE negb_or andbT nm /= nm' /= symmetric_g mn1 /= mn /= eq_sym n1m /= eq_sym n1n.
rewrite /= !inE.
case/orP.
  move/eqP => ?; subst x.
  case/splitPr : Hx => k11 k12 in Hl Hun.
  suff : ucycle g [:: n1, m, n, m' & k11] by apply acyclic_g.
  apply uniq_path_ucycle_extend_1 => //.
  by rewrite symmetric_g.
  rewrite -[in X in k11 ++ X](cat1s n1) -!catA catA cat_path in Hl.
  case/andP : Hl => Hl Hl1.
  rewrite /=.
  rewrite (sub_path_except _ _ Hl) // ?andbT // 1?eq_sym //.
  by rewrite exceptE /= nm' eq_sym mn.
  rewrite mem_cat.
  rewrite last_cat /= in Hl1.
  apply/negP.
  case/orP.
    move=> Hx.
    case/splitPr : Hx => k111 k112 in Hl Hl1 Hun.
    suff : ucycle g [:: m, n, m' & k111] by apply acyclic_g.
    apply uniq_path_ucycle_extend_1 => //.
    rewrite -(cat1s m) -!catA catA cat_path in Hl.
    by case/andP : Hl.
    rewrite -(cat1s m') -(cat1s m) -!catA (catA [:: m']) (catA ([:: m'] ++ _)) cat_uniq in Hun.
    by case/andP : Hun.
  rewrite inE.
  apply/negP.
  by rewrite (simple_neg simple_g).
  rewrite -(cat1s n1) -(cat1s m') 2!catA cat_uniq in Hun.
  case/andP : Hun => Hun1 Hun2.
  rewrite cons_uniq Hun1 andbT mem_cat negb_or inE negb_or.
  rewrite (simple_neg simple_g) //= inE eq_sym n1n andbT.
  apply/negP => nk11.
  move/path_except_notin : Hl.
  by rewrite mem_cat negb_or mem_cat nk11.
case/orP.
  move/eqP => ?; subst x.
  case/splitPr : Hx => k11 k12 in Hl Hun'.
  suff : ucycle g [:: m, n, m' & k11] by apply acyclic_g.
  apply: uniq_path_ucycle_extend_1 => //.
  move: Hl; rewrite cat_path => /andP[Hl _].
  move: Hl; by rewrite -(cat1s m k12) catA (cat_path _ _ (k11 ++ [:: m])) => /andP[].
  by rewrite -(cat1s m') -(cat1s m) 2!catA cat_uniq in Hun'; case/andP : Hun'.
move/eqP => ?; subst x.
move: Hl; rewrite cat_path => /andP[/path_except_notin].
by rewrite Hx.
Qed.

Lemma uniq_path_ucycle_extend_3 m n m' l n1 m'1
  (mn : g m n) (nm' : g n m') (mn1 : g m n1) (n1m'1 : g n1 m'1)
  (n1n : n1 != n) (m'm : m' != m) (m'1m : m'1 != m)
  (Hl : path (except g n) m' (l ++ m'1 :: nil))
  (Hun : uniq (m' :: l)) :
  ucycle g [:: m'1, n1, m, n, m' & l].
Proof.
apply/andP; split.
  rewrite /cycle -cats1 -(cat1s n1) -(cat1s m) -(cat1s n) -(cat1s m') !catA.
  rewrite -(catA _ l) cat_path /= andbT mn nm' symmetric_g n1m'1 symmetric_g mn1.
  by rewrite /= (except_path Hl).
move: (Hun) => Hun'.
rewrite -(cat1s m) -(cat1s n) catA -(cat1s n1) catA -(cat1s m'1) catA cat_uniq Hun andbT.
have n1m : n1 != m by rewrite (simple_neg simple_g) // symmetric_g.
have m'1n : m'1 != n.
  by move: Hl; rewrite cat_path /= andbT => /andP[_] /except13; rewrite eq_sym.
have m_not_n : m != n by rewrite (simple_neg simple_g).
have m'1n1 : m'1 != n1 by rewrite (simple_neg simple_g) // symmetric_g.
apply/andP; split.
  by rewrite /= !inE !negb_or andbT m'1n /= andbT n1m /= m'1n1 /= m_not_n andbT m'1m.
apply/hasP; case => x.
rewrite inE.
case/orP => [ | Hx].
  move/eqP => ?; subst x.
  rewrite /= !inE.
  apply/negP.
  rewrite !negb_or (@eq_sym _ m' n) (simple_neg simple_g nm') andbT.
  apply/andP; split.
    apply/eqP => ?; subst m'.
    suff : ucycle g (m'1 :: n1 :: m :: n :: nil).
      by apply acyclic_g.
    by rewrite /ucycle /= !inE !negb_or andbT symmetric_g n1m'1 /= symmetric_g mn1 /= mn /= andbT nm' /= m'1n1 /= m'm m'1n /= n1m /= n1n /=.
  apply/andP; split => //.
  apply/eqP => ?; subst m'.
  suff : ucycle g [:: m ; n ; n1] by apply acyclic_g.
  apply/andP; split.
    by rewrite /= mn /= nm' /= andbT symmetric_g.
  by rewrite /= !inE negb_or andbT (simple_neg simple_g mn) /= eq_sym n1m /= eq_sym.
rewrite /= !inE.
case/orP.
  move/eqP => ?; subst x.
  case/splitPr : Hx => l1 l2 in Hl Hun Hun'.
  suff : ucycle g (m'1 :: n1 :: m :: n :: m' :: l1) by apply acyclic_g.
  apply uniq_path_ucycle_extend_2 => //.
  by rewrite symmetric_g.
  by rewrite eq_sym.
  rewrite -[in X in l1 ++ X](cat1s m'1) -!catA catA cat_path in Hl.
  case/andP : Hl => Hl Hl1.
  rewrite /= (sub_path_except _ _ Hl) ?andbT 1?eq_sym //.
  by rewrite exceptE /= nm' /= eq_sym m_not_n.
  rewrite mem_cat.
  rewrite last_cat /= in Hl1.
  apply/negP.
  case/orP.
    move=> Hx.
    case/splitPr : Hx => l11 l12 in Hl Hl1 Hun.
    suff : ucycle g [:: m, n, m' & l11] by apply acyclic_g.
    apply uniq_path_ucycle_extend_1 => //.
    rewrite -(cat1s m) -!catA catA cat_path in Hl.
    by case/andP : Hl.
    rewrite -(cat1s m') -(cat1s m) -!catA (catA [:: m']) (catA ([:: m'] ++ _)) cat_uniq in Hun.
    by case/andP : Hun.
  rewrite inE.
  apply/negP; by rewrite eq_sym.
  rewrite -(cat1s m'1) -(cat1s m') catA cat_uniq in Hun.
  case/andP : Hun => Hunl Hun2.
  rewrite cons_uniq Hunl andbT inE negb_or.
  rewrite (simple_neg simple_g) //=.
  apply/negP => nl1.
  move/path_except_notin : Hl.
  by rewrite mem_cat negb_or mem_cat nl1.
case/orP.
  move/eqP => ?; subst x.
  case/splitPr : Hx => l1 l2 in Hl Hun' Hun.
  suff : ucycle g [:: n1, m, n, m' & l1] by apply acyclic_g.
  apply: uniq_path_ucycle_extend_2 => //.
  rewrite cat_path in Hl; case/andP : Hl => Hl _.
  by rewrite -(cat1s n1) catA cat_path in Hl; case/andP : Hl.
  by rewrite -(cat1s m') !catA cat_uniq in Hun; case/andP : Hun.
case/orP.
  move/eqP => ?; subst x.
  case/splitPr : Hx => l1 l2 in Hl Hun' Hun.
  suff : ucycle g [:: m, n, m' & l1] by apply acyclic_g.
  apply: uniq_path_ucycle_extend_1 => //.
  rewrite cat_path in Hl; case/andP : Hl => Hl _.
  by rewrite -(cat1s m) catA cat_path in Hl; case/andP : Hl.
  rewrite -(cat1s m') -(cat1s m) 2!catA cat_uniq in Hun; by case/andP : Hun.
move/eqP => ?; subst x.
rewrite cat_path in Hl.
case/andP : Hl.
move/path_except_notin.
by rewrite Hx.
Qed.

Lemma uniq_path_ucycle_cat x m n2 l2 l1 n1 (n2m : g n2 m) (n1m : g n1 m)
  (n2n1 : n2 != n1)
  (Hl1 : path (except g m) n1 (l1 ++ x :: nil))
  (Hl2 : path (except g m) n2 (l2 ++ x :: nil))
  (Hun1 : uniq (n1 :: l1)) (Hun2 : uniq (n2 :: l2)) :
  ucycle g ((x :: rev l2) ++ [:: n2, m, n1 & l1]).
Proof.
move: Hl1 Hl2 Hun1 Hun2.
move Hp : (size (l1 ++ l2)) => p.
move: l1 l2 Hp x n2 m n2m n1 n1m n2n1.
elim: p {-2}p (leqnn p).
  case=> // _ [] // [] // _ x /=.
  move=> n2 m n2m n1 n1m n2n1.
  rewrite !andbT exceptE /=.
  case/and3P => H1 H2 H3.
  case/and3P => L2 K2 K3.
  move=> _ _.
  apply/andP; split.
    by rewrite /= symmetric_g L2 /= symmetric_g symmetric_g /= H1 n2m symmetric_g n1m.
  rewrite /= !inE !negb_or /= andbT.
  rewrite (simple_neg simple_g) /=; last by rewrite symmetric_g.
  rewrite K3 /=.
  rewrite (simple_neg simple_g) /=; last by rewrite symmetric_g.
  by rewrite K2 /= n2n1 /= eq_sym.
move=> p IH p' Hp' l1 l2 Hp x.
move=> n2 m n2m n1 n1m n2n1.
move=> Hl1 Hl2 Hun1 Hun2.
apply/andP; split.
  rewrite /= rcons_cat /= -(cat1s n2) catA cat_path.
  apply/andP; split.
    move/except_path: Hl2.
    rewrite -rev_path (_ : rev (belast _ _) = rev l2 ++ [:: n2]); last first.
      by rewrite (_ : [:: n2] = rev [:: n2]) // -rev_cat belast_cat /= (lastI n2) cats1.
    rewrite cats1 last_rcons.
    apply: sub_path => a b; by rewrite symmetric_g.
  by rewrite last_cat /= n2m /= symmetric_g n1m /= -cats1 (except_path Hl1).
rewrite -(cat1s x) -catA uniq_catC.
rewrite -catA.
rewrite -(cat1s n2).
rewrite catA.
rewrite catA.
rewrite -(catA _ _ [:: x]).
rewrite cat_uniq.
apply/andP; split; first by rewrite cats1 -rev_cons rev_uniq.
apply/andP; split.
  apply/hasP; case => y.
  rewrite mem_cat.
  case/orP.
    rewrite inE.
    case/orP.
      move/eqP => ?; subst y.
      rewrite /= mem_cat.
      case/orP.
        rewrite mem_rev => n2l2.
        move/path_except_notin : Hl2.
        by rewrite mem_cat negb_or n2l2.
      rewrite inE.
      apply/negP; by rewrite (simple_neg simple_g) // symmetric_g.
    rewrite inE.
    case/orP.
      move/eqP => ?; subst y.
      rewrite /= mem_cat mem_rev.
      case/orP.
        move=> Hm.
        case/splitPr : Hm => l21 l22 in Hl2 Hun2.
        suff : ucycle g [:: n1, m, n2 & l21] by apply acyclic_g.
        apply uniq_path_ucycle_extend_1 => //.
        by rewrite symmetric_g.
        rewrite -(cat1s n1) -2!catA catA cat_path in Hl2; by case/andP : Hl2.
        rewrite -(cat1s n1) -(cat1s n2) 2!catA cat_uniq in Hun2; by case/andP : Hun2.
       rewrite inE.
       apply/negP.
       by rewrite eq_sym.
    move=> yl1.
    rewrite inE.
    rewrite mem_cat.
    case/orP.
      rewrite mem_rev => yl2.
      case/splitPr : yl1 => l11 l12 in Hl1 Hun1 Hp.
      case/splitPr : yl2 => l21 l22 in Hl2 Hun2 Hp.
      suff : ucycle g ((y :: rev l21) ++ n2 :: m :: n1 :: l11).
        apply acyclic_g; by rewrite /= size_cat /= 2!addnS.
      apply IH with (size (l11 ++ l21)) => //.
      apply leq_trans with p'.-1.
        rewrite -Hp !size_cat /= 3!addnS /= addSnnS -!addnA leq_add2l.
        by rewrite -addnS addnC -addnA leq_addr.
      have : forall a b : nat, a.+1 <= b.+1 -> a <= b by done.
      apply.
      apply: leq_trans Hp'.
      rewrite -ltnS prednK //; first by rewrite -Hp 2!size_cat /= addnS addSn.
      rewrite -(cat1s y) -2!catA catA cat_path in Hl1; by case/andP : Hl1.
      rewrite -(cat1s y) -2!catA catA cat_path in Hl2; by case/andP : Hl2.
      rewrite -(cat1s n1) 1!catA cat_uniq in Hun1; by case/andP : Hun1.
      rewrite -(cat1s n2) 1!catA cat_uniq in Hun2; by case/andP : Hun2.
    rewrite inE => /eqP ?; subst y.
    case/splitPr : yl1 => l11 l12 in Hl1 Hun1.
    suff : ucycle g [:: n2, m, n1 & l11] by apply acyclic_g.
    apply uniq_path_ucycle_extend_1 => //.
    by rewrite symmetric_g.
    rewrite -(cat1s n2) -2!catA catA cat_path in Hl1; by case/andP : Hl1.
    rewrite -(cat1s n1) -(cat1s n2) 2!catA cat_uniq in Hun1; by case/andP : Hun1.
  rewrite inE => /eqP ?; subst y.
  rewrite /= mem_cat.
  case/orP.
    rewrite mem_rev.
    move=> xl2.
    case/splitPr : xl2 => l21 l22 in Hl2 Hun2 Hp.
    suff : ucycle g ((x :: rev l1) ++ n1 :: m :: n2 :: l21).
      apply acyclic_g; by rewrite /= size_cat /= 2!addnS.
    apply IH with (size (l1 ++ l21)) => //.
    apply leq_trans with p'.-1.
      by rewrite -Hp !size_cat /= 2!addnS /= leq_add2l leq_addr.
      by rewrite -subn1 leq_subLR -addn1.
    by rewrite 2!size_cat addnC.
    by rewrite eq_sym.
    rewrite -[in X in l21 ++ X](cat1s x) -2!catA catA cat_path in Hl2; by case/andP : Hl2.
    rewrite -(cat1s n2) 1!catA cat_uniq in Hun2; by case/andP : Hun2.
  rewrite inE => /eqP ?; subst x.
  suff : ucycle g [:: n2, m, n1 & l1] by apply acyclic_g.
    apply uniq_path_ucycle_extend_1 => //.
    by rewrite symmetric_g.
    rewrite -(cat1s n1) catA cat_uniq Hun1 /= andbT orbF inE negb_or n2n1 /=.
    apply/negP => n2l1.
    case/splitPr : n2l1 => l11 l12 in Hl1 Hun1 Hp.
    suff : ucycle g (n2 :: m :: n1 :: l11) by apply acyclic_g.
    apply uniq_path_ucycle_extend_1 => //.
    by rewrite symmetric_g.
    rewrite -[in X in l11 ++ X](cat1s n2) -2!catA catA cat_path in Hl1; by case/andP : Hl1.
    rewrite -(cat1s n1) -(cat1s n2) 2!catA cat_uniq in Hun1; by case/andP : Hun1.
rewrite -(cat1s m) -(cat1s n1).
rewrite uniq_catC.
rewrite (catA [:: x]).
rewrite cat_uniq Hun1 andbT.
apply/andP; split.
  rewrite /= andbT inE.
  apply/eqP => ?; subst x.
  move/path_except_notin : Hl1.
  by rewrite mem_cat inE eqxx orbT.
apply/hasP; case => y.
rewrite inE.
case/orP => [ | yl1].
  move/eqP => ?; subst y.
  rewrite /= inE.
  case/orP.
    move/eqP => ?; subst x.
    suff : ucycle g [:: n1, m, n2 & l2] by apply acyclic_g.
    apply uniq_path_ucycle_extend_1 => //.
    by rewrite symmetric_g.
    rewrite -(cat1s n2) catA cat_uniq Hun2 /= orbF andbT inE negb_or eq_sym n2n1 /=.
    apply/negP => n1l2.
    case/splitPr : n1l2 => l21 l22 in Hl2 Hun2.
    suff : ucycle g [:: n1, m, n2 & l21] by apply acyclic_g.
    apply uniq_path_ucycle_extend_1 => //.
    by rewrite symmetric_g.
    rewrite -[in X in l21 ++ X](cat1s n1) -!catA catA cat_path in Hl2; by case/andP : Hl2.
    rewrite -(cat1s n1) -(cat1s n2) 2!catA cat_uniq in Hun2; by case/andP : Hun2.
  rewrite inE.
  apply/negP.
  by rewrite (simple_neg simple_g).
rewrite inE /= in_cons inE.
case/orP.
  move/eqP => ?; subst y.
  case/splitPr : yl1 => l11 l12 in Hl1 Hun1 Hp.
  suff : ucycle g ((x :: rev l2) ++ n2 :: m :: n1 :: l11).
    apply acyclic_g; by rewrite /= size_cat /= 2!addnS.
  apply IH with (size (l11 ++ l2)) => //.
  apply leq_trans with p'.-1.
    by rewrite -Hp !size_cat addnS addSn /= -addnA leq_add2l leq_addl.
    by rewrite -subn1 leq_subLR -addn1.
  rewrite -[in X in l11 ++ X](cat1s x) -2!catA catA cat_path in Hl1; by case/andP : Hl1.
  rewrite -cat_cons cat_uniq in Hun1; by case/andP : Hun1.
move/eqP => ?; subst y.
move/path_except_notin : Hl1.
by rewrite mem_cat yl1.
Qed.

Lemma uniq_path_ucycle_cat_extend x m n2 m2 l2 l1 n1 m1
  (mn2 : g m n2) (n2m2 : g n2 m2)
  (mn1 : g m n1) (n1m1 : g n1 m1)
  (n1n2 : n1 != n2) (m2m : m2 != m) (m1m : m1 != m)
  (Hl1 : path (except g n1) m1 (l1 ++ x :: nil))
  (Hl2 : path (except g n2) m2 (l2 ++ x :: nil))
  (Hunl1 : uniq (m1 :: l1))
  (Hunl2 : uniq (m2 :: l2)) :
  ucycle g ((x :: rev l2) ++ [:: m2, n2, m, n1, m1 & l1]).
Proof.
rewrite -(cat1s m2) catA.
rewrite cat_cons.
rewrite (_ : rev l2 ++ [:: m2] = rev (m2 :: l2)); last first.
  by rewrite rev_cons cats1.
apply uniq_path_ucycle_cat => //.
by rewrite symmetric_g.
by rewrite symmetric_g.
by rewrite eq_sym.
rewrite /=.
apply/andP; split.
  by rewrite exceptE /= n1m1 m1m andbT /= eq_sym (simple_neg simple_g).
apply: sub_path_except (Hl1) => //.
  by rewrite eq_sym.
rewrite mem_cat inE; apply/negP.
case/orP.
  move=> yl1.
  case/splitPr : yl1 => l11 l12 in Hl1 Hunl1.
  suff : ucycle g (m :: n1 :: m1 :: l11) by apply acyclic_g.
  apply uniq_path_ucycle_extend_1 => //.
  rewrite -[in X in l11 ++ X](cat1s m) -2!catA catA cat_path in Hl1; by case/andP : Hl1.
  rewrite -(cat1s m1) -(cat1s m) 2!catA cat_uniq in Hunl1; by case/andP : Hunl1.
move/eqP => ?; subst x.
suff : ucycle g (m :: n1 :: m1 :: l1) by apply acyclic_g.
apply uniq_path_ucycle_extend_1 => //.
rewrite -(cat1s m1) catA cat_uniq Hunl1 /= orbF andbT inE /= negb_or eq_sym m1m /=.
apply/negP => ml1.
case/splitPr : ml1 => l11 l12 in Hl1 Hunl1.
suff : ucycle g (m :: n1 :: m1 :: l11) by apply acyclic_g.
apply uniq_path_ucycle_extend_1 => //.
rewrite -[in X in l11 ++ X](cat1s m) -2!catA catA cat_path in Hl1; by case/andP : Hl1.
rewrite -(cat1s m1) -(cat1s m) 2!catA cat_uniq in Hunl1; by case/andP : Hunl1.
rewrite -(cat1s m2) -catA cat_path /= andbT.
apply/andP; split.
  rewrite exceptE /= n2m2 /= (simple_neg simple_g) //=; by rewrite symmetric_g.
apply: sub_path_except (Hl2) => //.
  by rewrite eq_sym.
rewrite mem_cat inE; apply/negP.
case/orP.
  move=> yl2.
  case/splitPr : yl2 => l21 l22 in Hl2 Hunl2.
  suff : ucycle g (m :: n2 :: m2 :: l21) by apply acyclic_g.
  apply uniq_path_ucycle_extend_1 => //.
  rewrite -[in X in l21 ++ X](cat1s m) -2!catA catA cat_path in Hl2; by case/andP : Hl2.
  rewrite -(cat1s m2) -(cat1s m) 2!catA cat_uniq in Hunl2; by case/andP : Hunl2.
move/eqP => ?; subst x.
suff : ucycle g (m :: n2 :: m2 :: l2) by apply acyclic_g.
apply uniq_path_ucycle_extend_1 => //.
rewrite -(cat1s m2) catA cat_uniq Hunl2 /= orbF andbT inE /= negb_or eq_sym m2m /=.
apply/negP => ml2.
case/splitPr : ml2 => l21 l22 in Hl2 Hunl2.
suff : ucycle g (m :: n2 :: m2 :: l21) by apply acyclic_g.
apply uniq_path_ucycle_extend_1 => //.
rewrite -[in X in l21 ++ X](cat1s m) -2!catA catA cat_path in Hl2; by case/andP : Hl2.
rewrite -(cat1s m2) -(cat1s m) 2!catA cat_uniq in Hunl2; by case/andP : Hunl2.
rewrite -(cat1s n1) cat_uniq Hunl1 /= andbT !inE /= negb_or.
rewrite (simple_neg simple_g) //=; last by rewrite symmetric_g.
apply/hasP; case => y yl1 /=.
rewrite inE.
move/eqP => ?; subst y.
move/path_except_notin : Hl1.
by rewrite mem_cat yl1.
rewrite -(cat1s n2) cat_uniq Hunl2 /= andbT !inE /= negb_or.
rewrite (simple_neg simple_g) //=; last by rewrite symmetric_g.
apply/hasP; case => y yl2 /=.
rewrite inE.
move/eqP => ?; subst y.
move/path_except_notin : Hl2.
by rewrite mem_cat yl2.
Qed.

End path_ext.

(** Third kind of partition: choose a root n and a successor m,
    consider the partition formed by, for each successor n' of
    m (n <> n'), the union of n' and all the subgraph (m'->n')
    for the m' successors of n' (n' <> n). *)
Section third_partition.

Variables (V : finType) (g : rel V).
Hypothesis symmetric_g : symmetric g.
Hypothesis acyclic_g : acyclic g.

Definition subgraph_succ2_D1 (m n : V) (gmn : g m n) : {set {set V}} :=
  (fun n' => n' |: \bigcup_(m' in successors g n' :\ m) (subgraph g m' n')) @:
  (successors g m :\ n).

Lemma cover_subgraph_succ2_D1 (Hg : simple g) (m n : V) (gmn : g m n) :
  cover (subgraph_succ2_D1 gmn) = (subgraph g m n) :\ m.
Proof.
apply/setP => v.
rewrite /cover.
apply/bigcupP => /=.
rewrite 3!inE.
case: ifP.
  case/andP => vm.
  case/andP => gnm.
  case/connectP => p.
  case/shortenP => p' Hpath Hun p'p Hlast.
  rewrite /subgraph_succ2_D1.
  destruct p' as [|n' t].
    by rewrite Hlast eqxx in vm.
  rewrite /= in Hpath.
  case/andP : Hpath; rewrite {1}exceptE => /and3P[] gmn' mn n'n Hpath.
  rewrite /= in Hlast.
  exists (n' |: \bigcup_(m' in successors g n' :\ m) (subgraph g m' n')).
    apply/imsetP.
    exists n' => //.
    by rewrite !inE n'n.
  rewrite !inE.
  case/boolP : (v == n') => // vn' /=.
  apply/bigcupP.
  destruct t as [|m' t].
    by rewrite Hlast eqxx in vn'.
  rewrite /= in Hlast.
  rewrite /= in Hpath.
  case/andP : Hpath; rewrite {1}exceptE => /and3P[] gn'm' _ m'n Hpath.
  exists m'.
    rewrite !inE gn'm' andbT; apply/eqP => ?; subst m'.
    by rewrite /= !inE eqxx orbT /= in Hun.
  rewrite !inE /subgraph /= gn'm' /=.
  apply/connectP.
  exists t => //.
  apply: sub_path_except Hpath => //.
  by rewrite (simple_neg Hg).
  move: Hun; by rewrite /= => /and4P[_]; rewrite inE negb_or => /andP[].
move/negbT.
rewrite negb_and negbK.
case/orP.
  move/eqP => ?; subst m.
  case => vs.
  rewrite /subgraph_succ2_D1.
  case/imsetP => n' Hn' ->.
  rewrite !inE.
  case/orP.
    by apply/negP; apply: contraTN Hn' => /eqP ->; rewrite !inE (negbTE (Hg n')) andbF.
  case/bigcupP => m' Hm'.
  rewrite /subgraph !inE.
  case/andP => gn'm' abs.
  rewrite !inE in Hn', Hm'.
  case/andP : Hn' => H1 H2.
  case/andP : Hm' => H3 H4.
  move: acyclic_g.
  rewrite /acyclic.
  case/connectP : abs => l.
  case/shortenP => l' Hpath Hun l'l Hlast.
  destruct l' as [| l1 l2].
    rewrite /= in Hlast; subst m'.
    by rewrite eqxx in H3.
  move/(_ [:: n', m', l1 & l2] erefl) => /=.
  apply.
  rewrite /ucycle.
  apply/andP; split.
    rewrite (cycle_path n') [l1 :: _]lock /= H4 /= -lock (@except_path _ _ n') ?andbT //.
    by rewrite -Hlast.
  rewrite [m' :: _]lock /= -{2}lock Hun andbT -lock.
  rewrite inE negb_or (simple_neg Hg) //=.
  by apply: path_except_notin Hpath.
rewrite negb_and symmetric_g gmn /=.
move=> H1.
case => vs.
rewrite /subgraph_succ2_D1.
case/imsetP => n'.
rewrite !inE.
case/andP => n'n gmn' ->.
rewrite !inE.
case/orP.
  move/eqP=> ?; subst n'.
  have : connect (except g n) m v.
    apply/connectP.
    exists [:: v] => //=.
    by rewrite exceptE /= gmn' n'n /= 2!andbT (simple_neg Hg).
  by rewrite (negbTE H1).
case/bigcupP => m'.
rewrite 3!inE.
case/andP => m'm gn'm'.
rewrite /subgraph !inE gn'm' /= => m'v.
move/negP : H1; apply.
have {m'v}m'v : connect (except g n) m' v.
  case/connectP : m'v => l Hpath Hlast.
  case/shortenP : Hpath Hlast => l' Hl' Hun l'l Hlast.
  apply/connectP; exists l' => //.
  have Htmp : connect g n m'.
    apply: (@connect_trans _ _ m).
      apply connect1.
      by rewrite symmetric_g.
    by apply: (@connect_trans _ _ n' _ _ (connect1 _) (connect1 _)).
  have Htmp2 : n != m'.
    apply/eqP => ?; subst m'.
    move: (@acyclic_g [:: m ; n ; n'] erefl).
    apply.
    rewrite /ucycle; apply/andP; split.
      by rewrite /cycle rcons_path /= gmn /= symmetric_g gn'm' /= symmetric_g.
    by rewrite /= !inE /= eq_sym negb_or m'm /= andbT (simple_neg Hg) //= eq_sym.
   move: (Hl'); apply sub_path_except => //.
   apply/negP => nl'.
   case/splitPr : nl' => l1 l2 in Hl' l'l Hun Hlast.
   suff : (ucycle g [:: n, m, n', m' & l1]).
     by apply acyclic_g.
   apply/andP; split.
     rewrite /cycle rcons_path /= symmetric_g gmn gmn' gn'm' /=.
     move: Hl'.
     by rewrite -cat1s cat_path /= => /and3P[/except_path -> /= /except_rel].
  have nm : n != m by rewrite (simple_neg Hg) // symmetric_g.
  have mn' : m != n' by rewrite (simple_neg Hg).
  have n'm' : n' != m' by rewrite (simple_neg Hg).
  have m'n' : m' != n' by rewrite (simple_neg Hg) // symmetric_g.
  rewrite [m :: _]lock /= -lock; apply/andP; split.
    rewrite inE negb_or nm /= inE negb_or eq_sym n'n /= inE negb_or Htmp2 /=.
    rewrite -(cat1s n) -(cat1s m') uniq_catC -2!catA uniq_catCA catA cat_uniq in Hun.
    case/andP : Hun => Hun _.
    rewrite -rev_uniq rev_cat uniq_catC /= mem_rev in Hun.
    by case/andP : Hun.
  rewrite [n' :: _]lock /= -lock; apply/andP; split.
    rewrite !inE !negb_or mn' /=.
    apply/andP; split.
      rewrite eq_sym m'm //=.
      apply/negP => ml1; case/splitPr: ml1 => l11 l12 in Hl' l'l Hun Hlast.
      suff : ucycle g ([:: m, n', m' & l11]) by apply acyclic_g.
      apply/andP; split.
      rewrite /cycle rcons_path /= gmn' gn'm' /=.
        rewrite -catA cat_path in Hl'.
        by case/andP : Hl' => /except_path -> /= /andP[] /except_rel.
      rewrite -(cat1s m) -(cat1s n') -(cat1s m') catA cat_uniq andbA.
      apply/andP; split; last first.
        rewrite -(cat1s m') 2!catA -(catA ([:: m'] ++ l11)) cat_uniq in Hun.
        by case/andP : Hun.
      apply/andP; split; first by rewrite /= !inE mn'.
      apply/hasP; case => x.
      rewrite !inE.
      case/orP => [ | Hx ].
        move/eqP => ?; subst x; by rewrite (negbTE m'm) /= (negbTE m'n').
      case/orP.
        move/eqP => ?; subst x.
        rewrite -(cat1s m') -catA cat_uniq in Hun.
        case/andP : Hun => /= _ /andP [] Hun.
        rewrite -(cat1s m) catA cat_uniq => /andP [] abs _.
        by rewrite -rev_uniq rev_cat /= mem_rev Hx in abs.
      move/eqP => ?; subst x.
      rewrite -catA cat_path in Hl'.
      case/andP : Hl' => /path_except_notin; by rewrite Hx.
   rewrite [m' :: _]lock /= -lock; apply/andP; split.
     rewrite inE negb_or; apply/andP; split => //.
     by move: Hl'; rewrite cat_path; case/andP => /path_except_notin.
   rewrite -(cat1s m') catA cat_uniq in Hun; by case/andP : Hun.
apply: connect_trans _ m'v.
apply connect_trans with n'.
  apply connect1.
  by rewrite exceptE /= gmn' n'n andbT /= (simple_neg Hg).
apply connect1.
rewrite exceptE /= gn'm' n'n /=.
apply/eqP => abs; subst m'.
move: acyclic_g.
move/(_ [:: m; n'; n] erefl); apply.
by rewrite /ucycle /= gmn' gn'm' symmetric_g gmn /= !inE n'n negb_or (simple_neg Hg) // eq_sym m'm.
Qed.

Lemma trivIset_sub_ver_suc_suc_helper (Hg : simple g) n1 l' m'2 n2 m :
  g m n1 ->
  g m n2 ->
  m'2 \in successors g n2 :\ m ->
  g n2 m'2 ->
  path (except g n2) m'2 l' ->
  uniq (m'2 :: l') ->
  n1 = last m'2 l' ->
   False.
Proof.
move=> Hn1 Hn2 Hm'2 n2m'2 Hl' Hun Hlast.
suff : ucycle g [:: m, n2, m'2 & l'] by apply acyclic_g.
apply/andP; split.
  rewrite /= Hn2 /=.
  rewrite !inE in Hm'2.
  case/andP : Hm'2 => H3 -> /=.
  by rewrite rcons_path (@except_path _ _ n2) //= -Hlast symmetric_g.
rewrite -(cat1s m) -(cat1s n2) catA cat_uniq Hun andbT.
apply/andP; split.
  by rewrite /= andbT inE (simple_neg Hg).
rewrite /= negb_or !inE negb_or /=.
have m'2n2 : m'2 != n2 by rewrite (simple_neg Hg) // symmetric_g.
rewrite m'2n2 /= andbT.
have m'2m : m'2 != m by rewrite 2!inE in Hm'2; case/andP : Hm'2.
rewrite m'2m /=.
apply/hasP; case => x Hx /=.
rewrite !inE.
case/orP => /eqP ?; subst x; last first.
  move/path_except_notin : Hl'; by rewrite Hx.
case/splitPr : Hx => l1 l2 in Hl' Hun Hlast.
suff : ucycle g [:: m, n2, m'2 & l1] by apply acyclic_g.
apply/andP; split.
  rewrite [m'2 :: _]lock /= -lock rcons_path Hn2 /=.
  rewrite cat_path in Hl'.
  case/andP : Hl' => H1 /= /andP[/except_rel ? _].
  by rewrite (@except_path _ _ n2) // andbT n2m'2 /=.
rewrite [m'2 :: _]lock /= -lock.
move: (Hun) => Hun'.
rewrite -{1}(cat1s m'2) catA cat_uniq in Hun.
case/and3P : Hun => -> _ _.
rewrite andbT.
have mn2 : m != n2 by rewrite (simple_neg Hg).
rewrite /= !inE !negb_or /= mn2 /= eq_sym m'2m /= eq_sym m'2n2 /=.
apply/andP; split; last first.
  move : Hl'; by move/path_except_notin; rewrite mem_cat negb_or => /andP[].
move: Hun'.
rewrite -(cat1s m'2) -(cat1s m) uniq_catC -2!catA catA cat_uniq.
case/and3P; by rewrite uniq_catC /= => /andP[].
Qed.

Lemma trivIset_subgraph_succ2_D1 (Hg : simple g) (m n : V) (gmn : g m n) :
  trivIset (subgraph_succ2_D1 gmn).
Proof.
apply/trivIsetP => /= v1 v2.
rewrite /subgraph_succ2_D1.
case/imsetP => n1 Hn1 v1n1.
case/imsetP => n2 Hn2 v2n2 v1v2.
have n1n2 : n1 != n2 by apply: contra v1v2 => /eqP n1n2; rewrite v1n1 v2n2 n1n2.
rewrite -setI_eq0.
apply/set0Pn.
case=> v.
rewrite inE.
case/andP.
rewrite v1n1 v2n2 !inE.
rewrite !inE in Hn1.
case/andP : Hn1 => n1n Hn1.
rewrite !inE in Hn2.
case/andP : Hn2 => n2n Hn2.
case/orP => [ /eqP ? | vn1].
  subst v.
  rewrite (negbTE n1n2) /=.
  case/bigcupP => m'2 Hm'2.
  rewrite /subgraph inE.
  case/andP => n2m'2.
  case/connectP => l.
  case/shortenP => l' Hl' Hun l'l Hlast.
  by apply: (@trivIset_sub_ver_suc_suc_helper Hg n1 l' m'2 n2 m).
case/orP => [/eqP ? | vn2 ].
  subst v.
  case/bigcupP : vn1 => m'1 Hm'1.
  rewrite /subgraph inE.
  case/andP => n1m'1.
  case/connectP => l.
  case/shortenP => l' Hl' Hun l'l Hlast.
  by apply: (@trivIset_sub_ver_suc_suc_helper Hg n2 l' m'1 n1 m).
case/bigcupP : vn1 => m'1 Hm'1.
rewrite /subgraph inE.
case/andP => n1m'1.
case/connectP => l.
case/shortenP => l' Hl' Hunl l'l Hlast.
case/bigcupP : vn2 => m'2 Hm'2.
rewrite /subgraph inE.
case/andP => n2m'2.
case/connectP => k.
case/shortenP => k' Hk' Hunk k'k Hkast.
suff : ucycle g [:: n1, m, n2, m'2 & k' ++ rev (belast m'1 l')] by apply acyclic_g.
have m'2n2 : m'2 != n2 by rewrite (simple_neg Hg) // symmetric_g.
have n1m : n1 != m by rewrite (simple_neg Hg) // symmetric_g.
have n2m : n2 != m by rewrite (simple_neg Hg) // symmetric_g.
apply/andP; split.
  rewrite /= symmetric_g Hn1 /= Hn2 /= n2m'2 /= rcons_cat cat_path.
  apply/andP; split; first by rewrite (@except_path _ _ n2).
  rewrite rcons_path.
  apply/andP; split.
    rewrite -Hkast {1}Hlast rev_path.
    apply: sub_path Hl' => w1 w2 /except_rel; by rewrite symmetric_g.
  move/(pathP m'1) : Hl' => /(_ O).
  have Htmp' : 0 < size l'.
    case: l' Hunl l'l Hlast => //= _ _ vm1'.
    subst m'1.
    exfalso.
    suff : ucycle g [:: n1, m, n2, m'2 & k'] by apply acyclic_g.
    apply/andP; split.
      rewrite /= symmetric_g Hn1 /= Hn2 /= n2m'2 /= rcons_path.
      by rewrite (except_path Hk') /= -Hkast symmetric_g.
    rewrite -(cat1s n1) -(cat1s m) -(cat1s n2) 2!catA cat_uniq Hunk andbT.
    apply/andP; split.
      by rewrite /= !inE /= negb_or andbT n1m /= [in X in _ && X]eq_sym n2m andbT.
    rewrite /= !inE /= !negb_or /=; apply/andP; split.
      rewrite !inE in Hm'2.
      case/andP : Hm'2 => -> _.
      rewrite m'2n2 andbT andbT.
      apply/eqP => ?; subst m'2.
      suff : ucycle g [:: m; n2; n1] by apply acyclic_g.
      apply/andP; split.
        by rewrite /= Hn2 n2m'2 symmetric_g Hn1.
      by rewrite /= !inE negb_or /= andbT eq_sym n2m eq_sym n1m eq_sym.
    apply/hasP; case=> x Hx /=.
    rewrite !inE; case/orP.
      move/eqP => ?; subst x.
      case/splitPr : Hx => k1 k2 in Hk' Hunk k'k Hkast.
      suff : ucycle g [:: n1, m, n2, m'2 & k1] by apply acyclic_g.
      apply/andP; split.
        rewrite /cycle rcons_path /= symmetric_g Hn1 /= Hn2 /= n2m'2 /=.
        rewrite cat_path in Hk'.
        case/andP : Hk' => /= Hk' /andP[] /except_rel ->.
        by rewrite (except_path Hk').
      move: (Hunk).
      rewrite -cat_cons cat_uniq => /andP [] Htmp _.
      rewrite -(cat1s n1) -(cat1s m) -(cat1s n2) 2!catA cat_uniq Htmp andbT.
      apply/andP; split.
        by rewrite /= !inE /= negb_or /= n1m n1n2 /= andbT eq_sym.
      apply/hasP; case => x.
      rewrite inE.
      case/orP.
        move/eqP => ?; subst x.
        rewrite /= !inE /= (negbTE m'2n2) orbF.
        case/orP.
          move/eqP => ?; subst m'2.
          by rewrite /= mem_cat inE eqxx orbT in Hunk.
        move/eqP => ?; subst m'2.
        by rewrite in_setD1 eqxx in Hm'2.
      move=> Hx.
      rewrite /= !inE.
      case/orP.
        move/eqP => ?; subst x.
        rewrite /= in Hunk.
        case/andP : Hunk => _.
        by rewrite -(cat1s n1) catA cat_uniq /= uniq_catC /= Hx.
      case/orP => /eqP ?; subst x.
        case/splitPr : Hx => k11 k12 in Hk' Hunk k'k Hkast Htmp.
        suff : ucycle g [:: m, n2, m'2 & k11] by apply acyclic_g.
        move: Hk' Hunk.
        rewrite cat_path.
        case/andP => Hk' _.
        rewrite -cat_cons cat_uniq.
        case/andP => Hunk _.
        rewrite -(cat1s m) catA cat_path in Hk'; case/andP : Hk' => Hk' _.
        rewrite -(cat1s m'2) -(cat1s m) 2!catA cat_uniq in Hunk.
        case/andP : Hunk => Hunk _.
        rewrite -catA cat1s in Hunk.
        by apply: uniq_path_ucycle_extend_1 Hk' Hunk.
      rewrite cat_path in Hk'.
      case/andP : Hk' => /path_except_notin.
      by rewrite Hx.
    case/orP.
      move/eqP => ?; subst x.
      case/splitPr : Hx => k1 k2 in Hk' Hunk k'k Hkast.
      suff : ucycle g [:: m, n2, m'2 & k1] by apply acyclic_g.
      rewrite -(cat1s m) catA cat_path in Hk'; case/andP : Hk' => Hk' _.
      rewrite -(cat1s m'2) -(cat1s m) 2!catA cat_uniq in Hunk.
      case/andP : Hunk => Hunk _.
      rewrite -catA cat1s in Hunk.
      by apply: uniq_path_ucycle_extend_1 Hk' Hunk.
    move/eqP => ?; subst x.
    move: Hx; apply/negP.
    by move/path_except_notin : Hk'.
  move/(_ Htmp')/except_rel => Htmp.
  rewrite [nth _ (_ :: _) _]/= in Htmp.
  rewrite (_ : last _ _ = m'1); first by rewrite symmetric_g.
  rewrite (last_nth m'1) size_rev size_belast.
  rewrite (_ : _ :: _ = rev (belast m'1 l' ++ [:: last m'2 k'])); last by rewrite rev_cat.
  rewrite nth_rev; last by rewrite size_cat /= size_belast addn1.
  rewrite size_cat addnC addSn add0n subSS size_belast subnn.
  rewrite nth_cat size_belast Htmp'.
  by destruct l'.
rewrite -(cat1s n1) -(cat1s m) -(cat1s n2) 2!catA cat_uniq.
apply/andP; split.
  by rewrite /= !inE /= negb_or andbT n1m n1n2 /= eq_sym n2m.
apply/andP; split.
  apply/hasP; case => x.
  rewrite in_cons.
  case/orP.
    move/eqP => ?; subst x.
    rewrite /= !inE.
    case/orP.
      move/eqP => ?; subst m'2.
      suff : ucycle g [:: m; n2; n1] by apply acyclic_g.
      apply/andP; split.
        by rewrite /= Hn2 n2m'2 symmetric_g Hn1.
      by rewrite /= !inE negb_or /= andbT eq_sym n2m eq_sym n1m eq_sym.
    case/orP.
      move/eqP => ?; subst m.
      by rewrite in_setD1 eqxx in Hm'2.
    move/eqP => ?; subst m'2.
    by rewrite eqxx in m'2n2.
  rewrite mem_cat.
  case/orP => [ Hx | ].
    rewrite !inE.
    case/orP.
      move/eqP => ?; subst x.
      case/splitPr : Hx => k1 k2 in Hk' Hunk k'k Hkast.
      suff : ucycle g [:: n1, m, n2, m'2 & k1] by apply acyclic_g.
      apply uniq_path_ucycle_extend_2 => //.
      rewrite in_setD1 in Hm'2; by case/andP: Hm'2.
      rewrite -(cat1s n1) catA cat_path in Hk'; by case/andP : Hk'.
      rewrite -(cat1s m'2) catA cat_uniq in Hunk; by case/andP : Hunk.
    case/orP.
      move/eqP => ?; subst x.
      case/splitPr : Hx => k1 k2 in Hk' Hunk k'k Hkast.
      suff : ucycle g [:: m, n2, m'2 & k1] by apply acyclic_g.
      rewrite -(cat1s m) catA cat_path in Hk'; case/andP : Hk' => Hk' _.
      rewrite -(cat1s m'2) -(cat1s m) 2!catA cat_uniq in Hunk.
      case/andP : Hunk => Hunk _.
      by apply: uniq_path_ucycle_extend_1 Hk' Hunk.
    move/eqP => ?; subst x.
    move/path_except_notin : Hk'; by rewrite Hx.
  rewrite mem_rev.
  move/mem_belast.
  rewrite inE.
  case/orP.
    move/eqP=> ?; subst x.
    rewrite !inE /=.
    case/orP.
      apply/negP; by rewrite (simple_neg Hg) // symmetric_g.
    case/orP.
      move/eqP => ?; subst m.
      by rewrite in_setD1 eqxx in Hm'1.
    move/eqP => ?; subst m'1.
      suff : ucycle g [:: m; n2; n1] by apply acyclic_g.
      rewrite /ucycle /= !andbT !inE Hn2 /= symmetric_g n1m'1 /= symmetric_g Hn1 /=.
      by rewrite negb_or eq_sym n2m eq_sym n1m /= eq_sym (simple_neg Hg).
    move=> Hx.
    rewrite !inE /=.
    case/orP.
      apply/negP; apply: contraTN Hx => /eqP ->; by apply: path_except_notin Hl'.
    case/orP.
      move/eqP => ?; subst x.
      case/splitPr : Hx => l1 l2 in Hl' Hunl l'l Hlast.
      suff : ucycle g [:: m, n1, m'1 & l1] by apply acyclic_g.
      rewrite -(cat1s m) catA cat_path in Hl'; case/andP : Hl' => Hl' _.
      rewrite -(cat1s m'1) -(cat1s m) 2!catA cat_uniq in Hunl; case/andP : Hunl => Hunl _.
      by apply: uniq_path_ucycle_extend_1 Hl' Hunl.
    move/eqP => ?; subst x.
    case/splitPr : Hx => l1 l2 in Hl' Hunl l'l Hlast.
    suff : ucycle g [:: n2, m, n1, m'1 & l1] by apply acyclic_g.
    apply uniq_path_ucycle_extend_2 => //.
    rewrite in_setD1 in Hm'1; by case/andP : Hm'1.
    rewrite -(cat1s n2) catA cat_path in Hl'; by case/andP : Hl'.
    rewrite -(cat1s m'1) catA cat_uniq in Hunl; by case/andP : Hunl.
rewrite -cat_cons cat_uniq Hunk /=.
apply/andP; split.
  apply/hasP; case => x.
  rewrite mem_rev.
  move/mem_belast.
  rewrite inE.
  case/orP.
    move/eqP => ?; subst x.
    rewrite !inE.
    case/orP.
      move/eqP => ?; subst m'2.
      suff : ucycle g [:: n2; m; n1; m'1] by apply acyclic_g.
      rewrite /ucycle /= symmetric_g Hn2 /= Hn1 /= n1m'1 /= !andbT symmetric_g n2m'2 /=.
      rewrite !inE !negb_or n2m /= eq_sym n1n2 /= (simple_neg Hg) //= (simple_neg Hg) //=.
      by rewrite andbC (simple_neg Hg) //=; move : Hm'1; rewrite in_setD1 eq_sym => /andP[].
    move=> m'1k'.
    case/splitPr : m'1k' => k1 k2 in Hk' Hunk k'k Hkast.
    suff : ucycle g [:: m'1, n1, m, n2, m'2 & k1] by apply acyclic_g.
    apply uniq_path_ucycle_extend_3 => //.
    rewrite in_setD1 in Hm'2; by case/andP : Hm'2.
    rewrite in_setD1 in Hm'1; by case/andP : Hm'1.
    rewrite -(cat1s m'1) catA cat_path in Hk'; by case/andP : Hk'.
    rewrite -(cat1s m'2) catA cat_uniq in Hunk; by case/andP : Hunk.
  rewrite /= inE => Hx.
  case/orP.
    move/eqP => ?; subst x.
    case/splitPr : Hx => l1 l2 in Hl' Hunl l'l Hlast.
    suff : ucycle g [:: m'2, n2, m, n1, m'1 & l1] by apply acyclic_g.
    apply uniq_path_ucycle_extend_3 => //.
    by rewrite eq_sym.
    rewrite in_setD1 in Hm'1; by case/andP : Hm'1.
    rewrite in_setD1 in Hm'2; by case/andP : Hm'2.
    rewrite -(cat1s m'2) catA cat_path in Hl'; by case/andP : Hl'.
    rewrite -(cat1s m'1) catA cat_uniq in Hunl; by case/andP : Hunl.
  move=> Hx'.
  case/splitPr : Hx => l1 l2 in Hl' Hunl l'l Hlast.
  case/splitPr : Hx' => k1 k2 in Hk' Hunk k'k Hkast.
  suff : ucycle g ((x :: rev k1) ++ (m'2 :: n2 :: m :: n1 :: m'1 :: l1)).
    apply acyclic_g; by rewrite /= size_cat /= addnC.
  apply uniq_path_ucycle_cat_extend => //.
  rewrite in_setD1 in Hm'2; by case/andP : Hm'2.
  rewrite in_setD1 in Hm'1; by case/andP : Hm'1.
  rewrite -(cat1s x) catA cat_path in Hl'; by case/andP : Hl'.
  rewrite -(cat1s x) catA cat_path in Hk'; by case/andP : Hk'.
  rewrite -(cat1s m'1) catA cat_uniq in Hunl; by case/andP : Hunl.
  rewrite -(cat1s m'2) catA cat_uniq in Hunk; by case/andP : Hunk.
rewrite rev_uniq.
move: Hunl.
rewrite lastI rcons_uniq; by case/andP.
Qed.

Lemma notin_subgraph (Hg : simple g) n1 m0 n0 m1 : g n0 m0 ->
  g n1 m0 -> n1 != n0 -> g n1 m1 -> m1 != m0 ->
  n0 \notin subgraph g m1 n1.
Proof.
move=> n0m0 n1m0 n1n0 n1m1 m1m0.
rewrite inE negb_and n1m1 /=.
apply/negP => abs.
case/connectP : abs => p.
case/shortenP => p' Hp' Hun p'p Hlast.
suff : ucycle g [:: m0, n1, m1 & p'] by apply acyclic_g.
apply/andP; split.
  rewrite [m1 :: _]lock /= -lock rcons_path symmetric_g n1m0 /= n1m1 /=.
  by rewrite (@except_path _ _ n1) // -Hlast.
rewrite -(cat1s m0) -(cat1s n1) catA cat_uniq Hun andbT.
apply/andP; split.
  by rewrite /= inE andbT eq_sym (simple_neg Hg n1m0).
apply/hasP; case=> x.
rewrite inE.
case/orP => [ | Hx].
  move/eqP => ?; subst m1.
  rewrite /= inE (negbTE m1m0) /= inE.
  apply/negP.
  by rewrite eq_sym (simple_neg Hg n1m1).
rewrite /= inE.
case/orP.
  move/eqP => ?; subst x.
  case/splitPr : Hx => p1 p2 in Hp' Hun p'p Hlast.
  suff : ucycle g [:: m0, n1, m1 & p1] by apply acyclic_g.
  apply uniq_path_ucycle_extend_1 => //.
  by rewrite symmetric_g.
  rewrite -(cat1s m0) catA cat_path in Hp'; by case/andP : Hp'.
  rewrite -(cat1s m1) -(cat1s m0) 2!catA cat_uniq in Hun; by case/andP : Hun.
rewrite inE.
move/eqP => ?; subst x.
move/path_except_notin : Hp'.
by rewrite Hx.
Qed.

Lemma successor_subgraph_successor (Hg : simple g) n0 m0 m1 : g n0 m0 -> m1 != m0 ->
  m1 \in subgraph g m0 n0 -> ~~ g m1 n0.
Proof.
move=> n0m0 m1m0.
rewrite inE.
case/andP => _.
case/connectP => p.
case/shortenP => p' Hp' Hun p'p Hlast.
apply/negP => abs.
suff : ucycle g [:: n0, m0 & p'].
  apply acyclic_g => /=.
  destruct p' => //.
  rewrite /= in Hlast.
  by rewrite Hlast eqxx in m1m0.
apply/andP; split.
  by rewrite /= n0m0 /= rcons_path -Hlast abs andbT (except_path Hp').
rewrite -(cat1s n0).
rewrite cat_uniq Hun andbT /= negb_or inE /=.
rewrite eq_sym (simple_neg Hg n0m0) /=.
move/path_except_notin : Hp'; apply: contra.
rewrite -has_pred1 (@eq_in_has _ _ (pred1 n0)) // => x /=; by rewrite inE.
Qed.

End third_partition.
