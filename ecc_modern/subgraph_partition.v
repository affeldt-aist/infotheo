(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg perm zmodp.
From mathcomp Require Import matrix.
Require Import ssr_ext.

(**md**************************************************************************)
(* # Cover/partition properties of bipartite-acyclic graphs                   *)
(******************************************************************************)

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
  colorable g kind -> path.cycle g cy -> ~~ odd (size cy).
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

Lemma ext_uniq_path (ac : acyclic') a b c s :
  uniq_path g b (c :: s) -> g a b -> a \notin s.
Proof.
move/andP => [Hp Hun] Hab; apply/negP => /splitPr Hsp.
destruct Hsp.
case Hli: (last b (c :: p1) == b).
  move/andP/proj1: Hun.
  by rewrite -cat_cons mem_cat -(eqP Hli) /= mem_last.
suff: false by []; rewrite -Hli.
apply (ac a b (c :: p1)).
  apply/negP => Ha.
  by rewrite (cat_uniq [:: b,c & p1] [:: a & p2]) /= Ha /= !andbF in Hun.
rewrite -cat_rcons -cat_cons cat_path in Hp.
move/andP/proj1: Hp => /= ->.
by rewrite Hab.
Qed.

Lemma acyclic_equiv : acyclic' <-> acyclic.
Proof.
rewrite /acyclic' /acyclic; split => [Hac | ].
  case=> [// | a [// | b [// | c p _ /= /andP[Hcp]]]].
  rewrite [ [:: b, c & p] ]lock /= -lock => /andP[abcp].
  have /eqP H : last b (c :: p) == b by move/Hac : abcp; apply.
  by rewrite /= -H /= mem_last.
move=> Hac a b p Ha.
rewrite /path.cycle rcons_path => /andP [/=/andP[Hab Hp]].
case : {Hp}(shortenP Hp) => p' Hp' Hun Hmem Hla.
move: {Hac}(Hac [:: a, b & p']).
rewrite /ucycle /cycle {3}[b :: p']lock /= -lock Hun Hab rcons_path Hp' Hla.
rewrite (_ : a \notin b :: p'); last first.
  apply: contra Ha; rewrite !inE => /orP[/eqP ->|]; first by rewrite eqxx.
  by move/Hmem; rewrite ?inE(*TODO(rei): not necessary since mc1.16.0*) => ->; rewrite orbT.
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

Lemma subgraph_connect n v w : g n w -> v \in subgraph w n -> connect g n v.
Proof.
move=> nw; rewrite /subgraph inE nw /= => wv.
move/connect1 : nw => /connect_trans; apply.
exact: connect_except wv.
Qed.

End subgraph.

(** First kind of partition: choose a root n and for each sucessor m,
    consider the partition formed by the subgraphs (m->n) (assuming
    acyclicity) *)
Section first_partition.
Variables (V : finType) (g : rel V).

Definition subgraph_succ (n : V) : {set {set V}} :=
  (subgraph g)^~ n @: successors g n.

Lemma cover_subgraph_succ n :
  cover ([set n] |: subgraph_succ n) = [set v | connect g n v].
Proof.
apply/setP => v; rewrite inE.
apply/idP/idP => [|nv].
  case/bigcupP => /= s; rewrite 2!inE => /orP[/eqP ->|].
    rewrite inE => /eqP ->; exact: connect0.
  case/imsetP => w; rewrite inE => nw ->; exact: subgraph_connect.
apply/bigcupP => /=.
case/connectP : nv => t' /shortenP[t nt uniq_nt _] ->{v t'}.
case: t => [|h t] in nt uniq_nt *.
  by exists [set n]; rewrite !inE // eqxx.
exists (subgraph g h n).
  rewrite inE /subgraph_succ (imset_f ((subgraph g)^~ n)) ?orbT //.
  rewrite inE; rewrite /= in nt; by case/andP : nt.
rewrite inE /=.
rewrite /= in nt.
case/andP : nt => -> ht /=.
apply/connectP; exists t => //; apply path_except => //.
by rewrite /= in uniq_nt; case/andP : uniq_nt.
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
  (subgraph g)^~ m @: (successors g m :\ n).

Lemma cover_subgraph_succ_D1 (Hg : simple g) (m n : V) (gmn : g m n) :
  m |: cover (subgraph_succ_D1 m n) = subgraph g m n.
Proof.
apply/setP => v.
apply/idP/idP => [|Hlhs].
  rewrite in_setU1.
  case/orP => [/eqP ->|].
    by rewrite start_in_subgraph // symmetric_g.
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
        exact: mem_take Hx.
      apply: contraTN Hx => /eqP ->.
      by rewrite take_index.
    rewrite /= inE andbT; apply: contraTN nl' => /eqP ->.
    exact: (path_except_notin Hl').
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
  by rewrite (imset_f (subgraph g ^~ m)) // !inE hn.
rewrite /subgraph inE mh /=.
apply/connectP; exists t' => //.
case/andP : Hun; rewrite inE negb_or => /andP[m_neq_h mt'] _.
exact: sub_path_except H4.
Qed.

End second_partition.

Section path_ext.
Variable (V : finType).

Lemma uniq_extend_1 m n m' (l : seq V) (mn : m != n) (nm' : n != m') (nl : n \notin l)
  (Hun : uniq (rcons (m' :: l) m)) : uniq [:: m, n, m' & l].
Proof.
move: Hun.
rewrite rcons_cons [uniq (m' :: _)]/= rcons_uniq mem_rcons inE /= negb_or -andbA.
case/and4P => H1 H2 H3 H4; rewrite !inE !negb_or /= mn /= eq_sym H1 /= H3 /=.
by rewrite nm' /= nl /= H2.
Qed.

Variable (g : rel V).
Hypothesis symmetric_g : symmetric g.
Hypothesis simple_g : simple g.

Lemma uniq_path_ucycle_extend_1 m n m' l (mn : g m n) (nm' : g n m')
  (Hl : path (except g n) m' (rcons l m)) (Hun : uniq (rcons (m' :: l) m)) :
  ucycle g [:: m, n, m' & l].
Proof.
apply/andP; split.
  by rewrite /= mn nm' /=; move/except_path : Hl.
apply uniq_extend_1 => //; try by rewrite (simple_neg simple_g).
by move: Hl; rewrite rcons_path => /andP[/path_except_notin].
Qed.

Hypothesis acyclic_g : acyclic g.

Lemma uniq_path_ucycle_extend_2 m n m' l n1 (nm : g m n) (nm' : g n m') (mn1 : g m n1)
  (m'm : m' != m) (Hl : path (except g n) m' (rcons l n1))
  (Hun : uniq (m' :: l)) : ucycle g [:: n1, m, n, m' & l].
Proof.
apply/andP; split.
  rewrite /= symmetric_g mn1 nm nm' /=; exact: except_path Hl.
rewrite -(cat1s m) -(cat1s n) catA -(cat1s n1) catA cat_uniq Hun andbT.
have n1m : n1 != m by rewrite (simple_neg simple_g) // symmetric_g.
have n1n : n1 != n by move: Hl; rewrite eq_sym rcons_path => /andP[_ /except13].
have mn : m != n by rewrite (simple_neg simple_g).
apply/andP; split; first by rewrite /= !inE negb_or andbT n1m /= n1n.
apply/hasP; case => x.
rewrite in_cons => /orP[/eqP ->{x}|xl].
  rewrite /= !inE (negbTE m'm) /=.
  apply/negP; rewrite negb_or andbC eq_sym (simple_neg simple_g) //=.
  apply/eqP => m'n1.
  suff : ucycle g [:: m; n; n1] by apply acyclic_g.
  rewrite /ucycle /= andbT nm /= andbT -m'n1 nm' /= m'n1 symmetric_g mn1 /=.
  by rewrite mem_seq1 eq_sym n1n andbT mem_seq2 negb_or mn eq_sym.
rewrite /= !inE => /orP[/eqP xn1|].
  move: xl; rewrite {}xn1 {x} => xl.
  case/splitPr : xl => k11 k12 in Hl Hun.
  suff : ucycle g [:: n1, m, n, m' & k11] by apply acyclic_g.
  apply uniq_path_ucycle_extend_1 => //; first by rewrite symmetric_g.
    move: Hl; rewrite -cat_rcons rcons_cat cat_path => /andP[Hl _] /=.
    rewrite (sub_path_except _ _ Hl) // ?andbT 1?eq_sym //.
      by rewrite exceptE /= nm' eq_sym mn.
    rewrite mem_rcons inE negb_or eq_sym n1m /=; apply/negP => mk11.
    case/splitPr : mk11 => k111 k112 in Hl Hun.
    suff : ucycle g [:: m, n, m' & k111] by apply acyclic_g.
    apply uniq_path_ucycle_extend_1 => //.
    by move: Hl; rewrite -cat_rcons rcons_cat cat_path => /andP[].
    move: Hun; rewrite -2!cat_cons -(cat1s m) catA -(catA _ _ (n1 :: k12)).
    by rewrite cat_uniq cats1 => /and3P[].
  move: Hun; rewrite -(cat1s n1) -(cat1s m') 2!catA cat_uniq cats1 => /andP[Hun _].
  rewrite rcons_cons cons_uniq mem_rcons inE negb_or eq_sym n1n andTb Hun andbT.
  move/path_except_notin : Hl; rewrite rcons_cat mem_cat negb_or => /andP[nk11 _].
  by rewrite inE negb_or nk11 andbT (simple_neg simple_g).
case/orP => [/eqP xm|/eqP xn].
  move: xl; rewrite {}xm {x} => ml.
  case/splitPr : ml => k11 k12 in Hl Hun.
  suff : ucycle g [:: m, n, m' & k11] by apply acyclic_g.
  apply: uniq_path_ucycle_extend_1 => //.
    by move: Hl; rewrite -cat_rcons rcons_cat cat_path => /andP[].
  by move: Hun; rewrite -cat_cons -(cat1s m) catA cat_uniq cats1 => /andP[].
move: xl; rewrite {}xn {x}.
by move: Hl; rewrite rcons_path => /andP[/path_except_notin] /negP.
Qed.

Lemma uniq_path_ucycle_extend_3 m n m' l n1 m'1
  (mn : g m n) (nm' : g n m') (mn1 : g m n1) (n1m'1 : g n1 m'1)
  (n1n : n1 != n) (m'm : m' != m) (m'1m : m'1 != m)
  (Hl : path (except g n) m' (rcons l m'1))
  (Hun : uniq (m' :: l)) :
  ucycle g [:: m'1, n1, m, n, m' & l].
Proof.
apply/andP; split.
  rewrite /path.cycle -cats1 -(cat1s n1) -(cat1s m) -(cat1s n) -(cat1s m') !catA.
  rewrite -(catA _ l) cat_path /= andbT mn nm' symmetric_g n1m'1 symmetric_g mn1.
  by rewrite /= cats1 (except_path Hl).
rewrite -(cat1s m) -(cat1s n) catA -(cat1s n1) catA -(cat1s m'1) catA cat_uniq Hun andbT.
have n1m : n1 != m by rewrite (simple_neg simple_g) // symmetric_g.
have m'1n : m'1 != n by move: Hl; rewrite rcons_path /= eq_sym => /andP[_] /except13.
have m_not_n : m != n by rewrite (simple_neg simple_g).
have m'1n1 : m'1 != n1 by rewrite (simple_neg simple_g) // symmetric_g.
apply/andP; split.
  by rewrite /= !inE !negb_or andbT m'1n /= andbT n1m /= m'1n1 /= m_not_n andbT m'1m.
apply/hasP; case => x.
rewrite inE => /orP[/eqP ->{x} /=|xl].
  apply/negP.
  rewrite !inE !negb_or m'm /= (@eq_sym _ m' n) (simple_neg simple_g nm') andbT.
  apply/andP; split; (apply/eqP => ?; subst m').
  - suff : ucycle g [:: m'1; n1; m; n] by apply acyclic_g.
    rewrite /ucycle /= !inE !negb_or andbT symmetric_g n1m'1 /= symmetric_g.
    by rewrite mn1 /= mn /= andbT nm' /= m'1n1 /= m'm m'1n /= n1m /= n1n.
  - suff : ucycle g [:: m ; n ; n1] by apply acyclic_g.
    apply/andP; split; first by rewrite /= mn /= nm' /= andbT symmetric_g.
    by rewrite /= andbT mem_seq1 eq_sym n1n andbT mem_seq2 negb_or m_not_n /= eq_sym.
rewrite /= !inE => /orP[/eqP xm'1|].
  move: xl; rewrite {}xm'1 {x} => m'1l.
  case/splitPr : m'1l => l1 l2 in Hl Hun.
  suff : ucycle g (m'1 :: n1 :: m :: n :: m' :: l1) by apply acyclic_g.
  apply uniq_path_ucycle_extend_2 => //; [by rewrite symmetric_g|by rewrite eq_sym| |].
    move: Hl; rewrite -cat_rcons rcons_cat cat_path => /andP[Hl _].
    rewrite /= (sub_path_except _ _ Hl) ?andbT 1?eq_sym //.
      by rewrite exceptE /= nm' /= eq_sym m_not_n.
    rewrite mem_rcons inE eq_sym negb_or m'1m /=; apply/negP => ml1.
    case/splitPr : ml1 => l11 l12 in Hl Hun.
    suff : ucycle g [:: m, n, m' & l11] by apply acyclic_g.
    apply uniq_path_ucycle_extend_1 => //.
    by move: Hl; rewrite -cat_rcons rcons_cat cat_path => /andP[Hl].
    move: Hun.
    rewrite -2!cat_cons -(cat1s m) catA -(catA _ _ (m'1 :: _)) cat_uniq => /and3P[Hun _ _].
    by rewrite -cats1.
  move: Hun; rewrite -cat_cons cat_uniq => /and3P[Hun _ _].
  rewrite cons_uniq Hun andbT inE negb_or (simple_neg simple_g) //=.
  by move/path_except_notin : Hl; rewrite rcons_cat mem_cat negb_or => /andP[].
case/orP => [/eqP xn1|].
  move: xl; rewrite {}xn1 => n1l.
  case/splitPr : n1l => l1 l2 in Hl Hun.
  suff : ucycle g [:: n1, m, n, m' & l1] by apply acyclic_g.
  apply: uniq_path_ucycle_extend_2 => //.
  by move: Hl; rewrite rcons_path -cat_rcons cat_path -andbA => /andP[].
  by move: Hun; rewrite -cat_cons cat_uniq => /andP[].
case/orP => [/eqP xm|/eqP xn].
  move: xl; rewrite {}xm {x} => ml.
  case/splitPr : ml => l1 l2 in Hl Hun.
  suff : ucycle g [:: m, n, m' & l1] by apply acyclic_g.
  apply: uniq_path_ucycle_extend_1 => //.
  by move: Hl; rewrite -cat_rcons rcons_cat cat_path => /andP[].
  by move: Hun; rewrite -cat_cons -(cat1s m) catA cat_uniq cats1 => /and3P[].
move: xl; rewrite {}xn {x} => nl.
by move: Hl; rewrite rcons_path => /andP[/path_except_notin] => /negP.
Qed.

Lemma uniq_path_ucycle_cat x m n2 l2 l1 n1 (n2m : g n2 m) (n1m : g n1 m)
  (n2n1 : n2 != n1)
  (Hl1 : path (except g m) n1 (rcons l1 x))
  (Hl2 : path (except g m) n2 (rcons l2 x))
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
  case/and3P => L2 K2 K3 _ _.
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
      by rewrite (_ : [:: n2] = rev [:: n2]) // -rev_cat lastI belast_rcons /=.
    rewrite cats1 last_rcons.
    apply: sub_path => a b; by rewrite symmetric_g.
  by rewrite last_cat /= n2m /= symmetric_g n1m /= (except_path Hl1).
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
        by rewrite mem_rcons inE n2l2 orbC.
      rewrite inE.
      apply/negP; by rewrite (simple_neg simple_g) // symmetric_g.
    rewrite inE.
    case/orP => [|yl1].
      move/eqP => ?; subst y.
      rewrite /= mem_cat mem_rev mem_seq1 eq_sym (negbTE n2n1) orbF => Hm.
      case/splitPr : Hm => l21 l22 in Hl2 Hun2.
      suff : ucycle g [:: n1, m, n2 & l21] by apply acyclic_g.
      apply uniq_path_ucycle_extend_1 => //; first by rewrite symmetric_g.
      by move: Hl2; rewrite -cat_rcons rcons_cat cat_path => /andP[].
      by move: Hun2; rewrite -cat_cons -(cat1s n1) catA cat_uniq cats1 => /and3P[].
    rewrite ?inE(*TODO(rei): not necessary since mc1.16.0*) mem_cat mem_seq1 => /orP[|].
      rewrite mem_rev => yl2.
      case/splitPr : yl1 => l11 l12 in Hl1 Hun1 Hp.
      case/splitPr : yl2 => l21 l22 in Hl2 Hun2 Hp.
      suff : ucycle g ((y :: rev l21) ++ n2 :: m :: n1 :: l11).
        apply acyclic_g; by rewrite /= size_cat /= 2!addnS.
      apply (IH (size (l11 ++ l21))) => //.
      apply (@leq_trans p'.-1).
        rewrite -Hp !size_cat /= 3!addnS /= addSnnS -!addnA leq_add2l.
        by rewrite -addnS addnC -addnA leq_addr.
      rewrite -(leq_add2r 1) 2!addn1.
      apply: leq_trans Hp'.
      rewrite -ltnS prednK //; first by rewrite -Hp 2!size_cat /= addnS addSn.
      by move: Hl1; rewrite rcons_path -cat_rcons cat_path -andbA => /and3P[].
      by move: Hl2; rewrite -(cat1s y) catA rcons_cat cats1 cat_path => /andP[].
      by move: Hun1; rewrite -cat_cons cat_uniq => /and3P[].
      by move: Hun2; rewrite -cat_cons cat_uniq => /and3P[].
    move/eqP => ?; subst y.
    case/splitPr : yl1 => l11 l12 in Hl1 Hun1.
    suff : ucycle g [:: n2, m, n1 & l11] by apply acyclic_g.
    apply uniq_path_ucycle_extend_1 => //; first by rewrite symmetric_g.
    by move: Hl1; rewrite -cat_rcons rcons_path cat_path -andbA => /andP[].
    by move: Hun1; rewrite -cat_cons -(cat1s n2) catA cat_uniq cats1 => /and3P[].
  rewrite inE => /eqP ?; subst y.
  rewrite /= mem_cat mem_seq1 => /orP[|].
    rewrite mem_rev.
    move=> xl2.
    case/splitPr : xl2 => l21 l22 in Hl2 Hun2 Hp.
    suff : ucycle g ((x :: rev l1) ++ n1 :: m :: n2 :: l21).
      apply acyclic_g; by rewrite /= size_cat /= 2!addnS.
    apply (IH (size (l1 ++ l21))) => //.
    apply (@leq_trans p'.-1).
      by rewrite -Hp !size_cat /= 2!addnS /= leq_add2l leq_addr.
      by rewrite -subn1 leq_subLR -addn1.
    by rewrite 2!size_cat addnC.
    by rewrite eq_sym.
    by move: Hl2; rewrite -cat_rcons rcons_cat cat_path => /andP[].
    by move: Hun2; rewrite -cat_cons cat_uniq => /andP[].
  move/eqP => ?; subst x.
  suff : ucycle g [:: n2, m, n1 & l1] by apply acyclic_g.
    apply uniq_path_ucycle_extend_1 => //; first by rewrite symmetric_g.
    rewrite rcons_uniq Hun1 andbT inE negb_or n2n1 /=.
    apply/negP => n2l1.
    case/splitPr : n2l1 => l11 l12 in Hl1 Hun1 Hp.
    suff : ucycle g (n2 :: m :: n1 :: l11) by apply acyclic_g.
    apply uniq_path_ucycle_extend_1 => //; first by rewrite symmetric_g.
    by move: Hl1; rewrite -cat_rcons rcons_cat cat_path => /andP[].
    by move: Hun1; rewrite -cat_cons -(cat1s n2) catA cat_uniq cats1 => /and3P[].
rewrite -(cat1s m) -(cat1s n1).
rewrite uniq_catC.
rewrite (catA [:: x]).
rewrite cat_uniq Hun1 andbT.
apply/andP; split.
  rewrite /= andbT inE.
  apply/eqP => ?; subst x.
  move/path_except_notin : Hl1.
  by rewrite -cats1 mem_cat inE eqxx orbT.
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
    rewrite rcons_uniq Hun2 andbT inE negb_or eq_sym n2n1 /=.
    apply/negP => n1l2.
    case/splitPr : n1l2 => l21 l22 in Hl2 Hun2.
    suff : ucycle g [:: n1, m, n2 & l21] by apply acyclic_g.
    apply uniq_path_ucycle_extend_1 => //; first by rewrite symmetric_g.
    by move: Hl2; rewrite -cat_rcons rcons_cat cat_path => /andP[].
    by move: Hun2; rewrite -cat_cons -(cat1s n1) catA cat_uniq cats1 => /and3P[].
  rewrite inE.
  apply/negP; by rewrite (simple_neg simple_g).
rewrite ?inE /= ?in_cons ?inE(*TODO(rei): not necessary since mc1.16.0*).
case/orP.
  move/eqP => ?; subst y.
  case/splitPr : yl1 => l11 l12 in Hl1 Hun1 Hp.
  suff : ucycle g ((x :: rev l2) ++ n2 :: m :: n1 :: l11).
    apply acyclic_g; by rewrite /= size_cat /= 2!addnS.
  apply (IH (size (l11 ++ l2))) => //.
  apply (@leq_trans p'.-1).
    by rewrite -Hp !size_cat addnS addSn /= -addnA leq_add2l leq_addl.
    by rewrite -subn1 leq_subLR -addn1.
  by move: Hl1; rewrite -cat_rcons; rewrite rcons_cat cat_path => /andP[].
  by move: Hun1; rewrite -cat_cons cat_uniq => /and3P[].
move/eqP => ?; subst y.
move/path_except_notin : Hl1.
by rewrite mem_rcons inE yl1 orbC.
Qed.

Lemma uniq_path_ucycle_cat_extend x m n2 m2 l2 l1 n1 m1
  (mn2 : g m n2) (n2m2 : g n2 m2)
  (mn1 : g m n1) (n1m1 : g n1 m1)
  (n1n2 : n1 != n2) (m2m : m2 != m) (m1m : m1 != m)
  (Hl1 : path (except g n1) m1 (rcons l1 x))
  (Hl2 : path (except g n2) m2 (rcons l2 x))
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
apply: sub_path_except (Hl1) => //; first by rewrite eq_sym.
rewrite mem_rcons inE orbC; apply/negP.
case/orP.
  move=> yl1.
  case/splitPr : yl1 => l11 l12 in Hl1 Hunl1.
  suff : ucycle g (m :: n1 :: m1 :: l11) by apply acyclic_g.
  apply uniq_path_ucycle_extend_1 => //.
  by move: Hl1; rewrite -cat_rcons rcons_cat cat_path => /andP[].
  by move: Hunl1; rewrite -cat_cons -(cat1s m) catA cats1 cat_uniq => /and3P[].
move/eqP => ?; subst x.
suff : ucycle g (m :: n1 :: m1 :: l1) by apply acyclic_g.
apply uniq_path_ucycle_extend_1 => //.
rewrite rcons_uniq Hunl1 andbT inE negb_or eq_sym m1m /=.
apply/negP => ml1.
case/splitPr : ml1 => l11 l12 in Hl1 Hunl1.
suff : ucycle g (m :: n1 :: m1 :: l11) by apply acyclic_g.
apply uniq_path_ucycle_extend_1 => //.
by move: Hl1; rewrite -cat_rcons rcons_cat cat_path => /andP[].
by move: Hunl1; rewrite -cat_cons -(cat1s m) catA cat_uniq cats1 => /and3P[].
rewrite -(cat1s m2) rcons_cat cat_path /= andbT.
apply/andP; split.
  rewrite exceptE /= n2m2 /= (simple_neg simple_g) //=; by rewrite symmetric_g.
apply: sub_path_except (Hl2) => //; first by rewrite eq_sym.
rewrite mem_rcons inE orbC ; apply/negP => /orP[|].
  move=> yl2.
  case/splitPr : yl2 => l21 l22 in Hl2 Hunl2.
  suff : ucycle g (m :: n2 :: m2 :: l21) by apply acyclic_g.
  apply uniq_path_ucycle_extend_1 => //.
  by move: Hl2; rewrite -cat_rcons rcons_cat cat_path => /andP[].
  by move: Hunl2; rewrite -cat_cons -(cat1s m) catA cats1 cat_uniq => /and3P[].
move/eqP => ?; subst x.
suff : ucycle g (m :: n2 :: m2 :: l2) by apply acyclic_g.
apply uniq_path_ucycle_extend_1 => //.
rewrite rcons_uniq Hunl2 andbT inE negb_or eq_sym m2m /=.
apply/negP => ml2.
case/splitPr : ml2 => l21 l22 in Hl2 Hunl2.
suff : ucycle g (m :: n2 :: m2 :: l21) by apply acyclic_g.
apply uniq_path_ucycle_extend_1 => //.
by move: Hl2; rewrite -cat_rcons rcons_cat cat_path => /andP[].
by move: Hunl2; rewrite -cat_cons -(cat1s m) catA cats1 cat_uniq => /and3P[].
rewrite -(cat1s n1) cat_uniq Hunl1 /= andbT !inE /= negb_or.
rewrite (simple_neg simple_g) //=; last by rewrite symmetric_g.
apply/hasP; case => y yl1 /=.
rewrite inE.
move/eqP => ?; subst y.
by move/path_except_notin : Hl1; rewrite mem_rcons inE yl1 orbC.
rewrite -(cat1s n2) cat_uniq Hunl2 /= andbT !inE /= negb_or.
rewrite (simple_neg simple_g) //=; last by rewrite symmetric_g.
apply/hasP; case => y yl2 /=.
rewrite inE.
move/eqP => ?; subst y.
by move/path_except_notin : Hl2; rewrite mem_rcons inE yl2 orbC.
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
  rewrite /ucycle; apply/andP; split.
    rewrite (cycle_path n') [l1 :: _]lock /= H4 /= -lock.
    by rewrite (@except_path _ _ n') ?andbT // -Hlast.
  rewrite [m' :: _]lock /= -{2}lock Hun andbT -lock.
  rewrite inE negb_or (simple_neg Hg) //=; exact: path_except_notin Hpath.
rewrite negb_and symmetric_g gmn /= => H1 [vs].
rewrite /subgraph_succ2_D1.
case/imsetP => n'.
rewrite !inE.
case/andP => n'n gmn' ->{vs}.
rewrite !inE.
case/orP.
  move/eqP=> ?; subst n'.
  have : connect (except g n) m v.
    apply/connectP; exists [:: v] => //=.
    by rewrite exceptE /= gmn' n'n /= 2!andbT (simple_neg Hg).
  by rewrite (negbTE H1).
case/bigcupP => m'.
rewrite 3!inE => /andP[m'm n'm'].
rewrite /subgraph !inE n'm' /= => m'v.
move/negP : H1; apply.
have {}m'v : connect (except g n) m' v.
  case/connectP : m'v => l Hpath Hlast.
  case/shortenP : Hpath Hlast => l' Hl' Hun l'l Hlast.
  apply/connectP; exists l' => //.
  have nm' : n != m'.
    apply/eqP => ?; subst m'.
    apply: (@acyclic_g [:: m ; n ; n']) => //.
    rewrite /ucycle; apply/andP; split.
      by rewrite /path.cycle rcons_path /= gmn /= symmetric_g n'm' /= symmetric_g.
    by rewrite /= !inE /= eq_sym negb_or m'm /= andbT (simple_neg Hg) //= eq_sym.
   move: (Hl'); apply sub_path_except => //.
   apply/negP => nl'.
   case/splitPr : nl' => l1 l2 in Hl' l'l Hun Hlast.
   suff : (ucycle g [:: n, m, n', m' & l1]) by apply acyclic_g.
   apply/andP; split.
     rewrite /path.cycle rcons_path /= symmetric_g gmn gmn' n'm' /=.
     move: Hl'.
     by rewrite -cat1s cat_path /= => /and3P[/except_path -> /= /except_rel].
  rewrite [m :: _]lock /= -lock; apply/andP; split.
    rewrite inE negb_or eq_sym (simple_neg Hg) //= inE negb_or eq_sym n'n /= inE negb_or nm' /=.
    move: Hun.
    rewrite -(cat1s n) -(cat1s m') uniq_catC -2!catA uniq_catCA catA cat_uniq.
    case/andP => Hun _; move: Hun.
    by rewrite -rev_uniq rev_cat uniq_catC /= mem_rev => /andP[].
  rewrite [n' :: _]lock /= -lock; apply/andP; split.
    rewrite !inE !negb_or (simple_neg Hg) //= eq_sym m'm /=.
    apply/negP => ml1; case/splitPr: ml1 => l11 l12 in Hl' l'l Hun Hlast.
    suff : ucycle g ([:: m, n', m' & l11]) by apply acyclic_g.
    apply/andP; split.
    rewrite /path.cycle rcons_path /= gmn' n'm' /=.
      move: Hl'; rewrite -catA cat_path.
      by case/andP => /except_path -> /= /andP[] /except_rel.
    rewrite -(cat1s m) -(cat1s n') -(cat1s m') catA cat_uniq andbA.
    apply/andP; split; last first.
      move: Hun.
      by rewrite -[in X in X -> _](cat1s m') 2!catA -(catA ([:: m'] ++ l11)) cat_uniq => /andP[].
    apply/andP; split; first by rewrite /= !inE (simple_neg Hg).
    apply/hasP; case => x.
    rewrite !inE.
    case/orP => [/eqP ->{x} | Hx ].
        by rewrite (negbTE m'm) /= eq_sym (negbTE (simple_neg Hg _)).
      case/orP => [/eqP xm|/eqP xn'].
        move: Hun; rewrite -(cat1s m') -catA cat_uniq => /andP[/= _ /andP[] _].
        rewrite -(cat1s m) catA cat_uniq => /andP [].
        by rewrite -rev_uniq rev_cat /= mem_rev -xm Hx.
      by move: Hl'; rewrite -catA cat_path => /andP[/path_except_notin]; rewrite -xn' Hx.
   rewrite [m' :: _]lock /= -lock; apply/andP; split.
     rewrite inE negb_or (simple_neg Hg) //=.
     by move: Hl'; rewrite cat_path; case/andP => /path_except_notin.
   rewrite -(cat1s m') catA cat_uniq in Hun; by case/andP : Hun.
apply: connect_trans _ m'v.
apply (@connect_trans _ _ n').
- apply connect1.
  by rewrite exceptE /= gmn' n'n andbT /= (simple_neg Hg).
- apply connect1.
  rewrite exceptE /= n'm' n'n /=.
  apply/eqP => abs; subst m'.
  apply: (@acyclic_g [:: m; n'; n] erefl).
  by rewrite /ucycle /= gmn' n'm' symmetric_g gmn /= !inE n'n negb_or (simple_neg Hg) // eq_sym m'm.
Qed.

Lemma trivIset_sub_ver_suc_suc_helper (Hg : simple g) m n1 n2 m2 l :
  g m n1 -> g m n2 -> g n2 m2 -> m2 != m ->
  path (except g n2) m2 l ->
  uniq (m2 :: l) ->
  n1 = last m2 l -> False.
Proof.
move=> mn1 mn2 n2m2 m2m Hl Hun Hlast.
suff : ucycle g [:: m, n2, m2 & l] by apply acyclic_g.
apply/andP; split.
  by rewrite /= mn2 /= n2m2 /= rcons_path -Hlast (except_path Hl) symmetric_g.
rewrite -(cat1s m) -(cat1s n2) catA cat_uniq Hun andbT.
apply/andP; split; first by rewrite /= andbT inE (simple_neg Hg).
rewrite /= negb_or !inE negb_or -andbA andbCA eq_sym (simple_neg Hg) // m2m /=.
apply/hasP; case => x Hx /=.
rewrite 2!inE.
case/orP => /eqP ?; subst x; last first.
  move/path_except_notin : Hl; by rewrite Hx.
case/splitPr : Hx => l1 l2 in Hl Hun Hlast.
suff : ucycle g [:: m, n2, m2 & l1] by apply acyclic_g.
apply/andP; split.
  rewrite /= mn2 n2m2 /=.
  by move: Hl; rewrite -cat_rcons cat_path => /andP[/except_path].
rewrite [m2 :: _]lock /= -lock.
move: (Hun) => Hun'.
move: Hun; rewrite -{1}(cat1s m2) catA cat_uniq => /and3P[-> _ _].
rewrite andbT /= !inE /= !negb_or /= (simple_neg Hg) //=.
rewrite eq_sym m2m /= (simple_neg Hg) //=; apply/andP; split; last first.
  by move/path_except_notin : Hl; rewrite mem_cat negb_or => /andP[].
move: Hun'; rewrite -(cat1s m2) uniq_catC -(cat1s m) cat_uniq => /andP[].
by rewrite catA cat_uniq => /andP[]; rewrite uniq_catC /= => /andP[].
Qed.

Lemma trivIset_subgraph_succ2_D1_helper (Hg : simple g) m n1 n2 m1 m2 v
  (l k k' : seq V) (n1n2 : n1 != n2)
  (mn1 : g m n1) (mn2 : g m n2) (n1m1 : g n1 m1) (n2m2 : g n2 m2)
  (m2m : m2 != m)
  (Hunk : uniq (m2 :: k'))
  (k'k : subpred (mem k') (mem k))
  (Hk' : path (except g n2) m2 k')
  (Hlast : v = last m1 l) (Hkast : v = last m2 k') :
  0 < size l.
Proof.
case: l Hlast => //= vm1; subst m1.
exfalso.
suff : ucycle g [:: n1, m, n2, m2 & k'] by apply acyclic_g.
apply/andP; split.
  rewrite /= symmetric_g mn1 /= mn2 /= n2m2 /= rcons_path.
  by rewrite (except_path Hk') /= -Hkast symmetric_g.
rewrite -(cat1s n1) -(cat1s m) -(cat1s n2) 2!catA cat_uniq Hunk andbT.
apply/andP; split.
  by rewrite /= !inE negb_or eq_sym (simple_neg Hg) //= n1n2 /= (simple_neg Hg).
rewrite /= !inE /= !negb_or /=; apply/andP; split.
  rewrite m2m andTb andbC (simple_neg Hg) //= 1?symmetric_g //.
  apply/eqP => ?; subst m2.
  suff : ucycle g [:: m; n2; n1] by apply acyclic_g.
  apply/andP; split; first by rewrite /= mn2 n2m2 symmetric_g mn1.
  rewrite /= !inE negb_or /= andbT (simple_neg Hg mn2) /= eq_sym.
  by rewrite eq_sym (simple_neg Hg) //= eq_sym.
apply/hasP; case=> x Hx /=.
rewrite !inE; case/orP => [/eqP xn1|].
  move: Hx; rewrite {}xn1 {x} => Hx.
  case/splitPr : Hx => k1 k2 in Hk' Hunk k'k Hkast.
  suff : ucycle g [:: n1, m, n2, m2 & k1] by apply acyclic_g.
  apply/andP; split.
    rewrite /path.cycle rcons_path /= symmetric_g mn1 /= mn2 /= n2m2 /=.
    move: Hk'; rewrite cat_path => /andP[/except_path -> /=].
    by rewrite exceptE /= => /andP[/andP[]].
  move: (Hunk).
  rewrite -cat_cons cat_uniq => /andP [] m2k1 _.
  rewrite -(cat1s n1) -(cat1s m) -(cat1s n2) 2!catA cat_uniq m2k1 andbT.
  apply/andP; split.
    by rewrite /= !inE negb_or /= eq_sym (simple_neg Hg) //= n1n2 (simple_neg Hg).
  apply/hasP; case => x.
  rewrite inE.
  case/orP => [/eqP ->{x}|xk1].
    rewrite /= !inE /= (eq_sym m2 n2)(negbTE (simple_neg Hg n2m2)).
    rewrite (negbTE m2m) /= orbF => /eqP m'2n1.
    by move: Hunk; rewrite /= mem_cat m'2n1 inE eqxx orbCA.
  rewrite /= !inE.
  case/orP => [/eqP xn1|].
    move: Hunk; by rewrite -xn1 /= -cat_rcons cat_uniq rcons_uniq xk1 /= andbF.
  case/orP => /eqP ?; subst x.
    case/splitPr : xk1 => k11 k12 in Hk' Hunk k'k Hkast m2k1.
    suff : ucycle g [:: m, n2, m2 & k11] by apply acyclic_g.
    move: Hk'; rewrite cat_path => /andP[Hk' _]; move: Hk'.
    rewrite -[in X in X -> _](cat1s m) catA cat_path cats1 => /andP[Hk' _].
    move: Hunk; rewrite -cat_cons cat_uniq; case/andP => Hunk _; move: Hunk.
    rewrite -[in X in X -> _](cat1s m2) -[in X in X -> _](cat1s m) 2!catA.
    rewrite cat_uniq cats1 => /and3P[Hunk _ _].
    exact: uniq_path_ucycle_extend_1 Hk' Hunk.
  by move: Hk'; rewrite cat_path => /andP[/path_except_notin]; rewrite xk1.
case/orP => [/eqP xm|/eqP xn2].
  move: Hx; rewrite {}xm {x} => xk'.
  case/splitPr : xk' => k1 k2 in Hk' Hunk k'k Hkast.
  suff : ucycle g [:: m, n2, m2 & k1] by apply acyclic_g.
  move: Hk'; rewrite -[in X in X -> _](cat1s m) catA cat_path cats1 => /andP[Hk' _].
  move: Hunk; rewrite -[in X in X -> _](cat1s m2) -[in X in X -> _](cat1s m) 2!catA cat_uniq cats1 => /andP[Hunk _].
  exact: uniq_path_ucycle_extend_1 Hk' Hunk.
by move/path_except_notin : Hk'; rewrite -xn2 Hx.
Qed.

Lemma trivIset_subgraph_succ2_D1 (Hg : simple g) m n (mn : g m n) :
  trivIset (subgraph_succ2_D1 mn).
Proof.
apply/trivIsetP => /= v1 v2.
rewrite /subgraph_succ2_D1.
case/imsetP => n1 Hn1 v1n1.
case/imsetP => n2 Hn2 v2n2 v1v2.
have n1n2 : n1 != n2 by apply: contra v1v2 => /eqP n1n2; rewrite v1n1 v2n2 n1n2.
rewrite -setI_eq0.
apply/set0Pn; case=> v.
rewrite inE => /andP[].
rewrite v1n1 v2n2 !inE.
move: Hn1; rewrite !inE => /andP[n1n Hn1].
move: Hn2; rewrite !inE => /andP[n2n Hn2].
case/orP => [ /eqP ->{v} | vn1].
  rewrite (negbTE n1n2) /= => /bigcupP[m'2 Hm'2].
  rewrite /subgraph inE => /andP[n2m'2 /connectP[l]].
  case/shortenP => l' Hl' Hun l'l Hlast.
  apply: (@trivIset_sub_ver_suc_suc_helper Hg m n1 n2 m'2 l') => //.
  by move: Hm'2; rewrite in_setD1 => /andP[].
case/orP => [/eqP vn2 | vn2].
  move: vn1; rewrite {}vn2 {v} => /bigcupP[m'1 Hm'1].
  rewrite /subgraph inE => /andP[n1m'1 /connectP[l]].
  case/shortenP => l' Hl' Hun l'l Hlast.
  apply: (@trivIset_sub_ver_suc_suc_helper Hg m n2 n1 m'1 l') => //.
  by move: Hm'1; rewrite in_setD1 => /andP[].
case/bigcupP : vn1 => m'1 Hm'1.
rewrite /subgraph inE => /andP[n1m'1 /connectP[l]].
case/shortenP => l' Hl' Hunl l'l Hlast.
case/bigcupP : vn2 => m'2 Hm'2.
rewrite /subgraph inE => /andP[n2m'2 /connectP[k]].
case/shortenP => k' Hk' Hunk k'k Hkast.
suff : ucycle g [:: n1, m, n2, m'2 & k' ++ rev (belast m'1 l')] by apply acyclic_g.
apply/andP; split.
  rewrite /= symmetric_g Hn1 /= Hn2 /= n2m'2 /= rcons_cat cat_path.
  rewrite (except_path Hk') /= rcons_path; apply/andP; split.
    rewrite -Hkast {1}Hlast rev_path.
    apply: sub_path Hl' => w1 w2 /except_rel; by rewrite symmetric_g.
  rewrite (_ : last _ _ = m'1); first by rewrite symmetric_g.
  rewrite (last_nth m'1) size_rev size_belast.
  rewrite (_ : _ :: _ = rev (belast m'1 l' ++ [:: last m'2 k'])); last by rewrite rev_cat.
  rewrite nth_rev; last by rewrite size_cat /= size_belast addn1.
  rewrite size_cat addnC addSn add0n subSS size_belast subnn nth_cat size_belast.
  have -> : 0 < size l'.
    apply: (@trivIset_subgraph_succ2_D1_helper _ m n1 n2 m'1 m'2 v l' k k') => //.
    by move: Hm'2; rewrite in_setD1 => /andP[].
  by destruct l'.
rewrite -(cat1s n1) -(cat1s m) -(cat1s n2) 2!catA cat_uniq.
apply/andP; split.
  by rewrite /= !inE /= negb_or andbT eq_sym (simple_neg Hg) //=n1n2 /= (simple_neg Hg).
apply/andP; split.
  apply/hasP; case => x.
  rewrite in_cons.
  case/orP => [/eqP ->{x}|].
    rewrite /= !inE.
    case/orP => [/eqP m'2n1|].
      suff : ucycle g [:: m; n2; n1] by apply acyclic_g.
      apply/andP; split; first by rewrite /= andbT Hn2 /= andbC symmetric_g Hn1 /= -m'2n1.
      by rewrite /= !inE negb_or /= (simple_neg Hg) //= (simple_neg Hg) //= eq_sym n1n2.
    rewrite orbC eq_sym (negbTE (simple_neg _ n2m'2)) //= => /eqP m'2m.
    by move: Hm'2; rewrite m'2m in_setD1 eqxx.
  rewrite mem_cat => /orP[Hx|].
    rewrite !inE => /orP[/eqP xn1|].
      move: Hx; rewrite {}xn1 {x} => Hx.
      case/splitPr : Hx => k1 k2 in Hk' Hunk k'k Hkast.
      suff : ucycle g [:: n1, m, n2, m'2 & k1] by apply acyclic_g.
      apply uniq_path_ucycle_extend_2 => //.
      by move: Hm'2; rewrite in_setD1 => /andP[].
      by move: Hk'; rewrite -(cat1s n1) catA cats1 cat_path => /andP[].
      by move: Hunk; rewrite -cat_cons cat_uniq => /and3P[].
    case/orP => [/eqP xm|/eqP xn2].
      move: Hx; rewrite {}xm {x} => Hx.
      case/splitPr : Hx => k1 k2 in Hk' Hunk k'k Hkast.
      suff : ucycle g [:: m, n2, m'2 & k1] by apply acyclic_g.
      move: Hk'; rewrite -[in X in X -> _](cat1s m) catA cat_path cats1 => /andP[Hk' _].
      move: Hunk; rewrite -[in X in X -> _](cat1s m'2) -[in X in X -> _](cat1s m).
      rewrite 2!catA cat_uniq cats1 => /and3P[Hunk _ _].
      exact: uniq_path_ucycle_extend_1 Hk' Hunk.
    by move/path_except_notin : Hk'; rewrite -xn2 Hx.
  rewrite mem_rev => /mem_belast; rewrite inE => /orP[/eqP ->{x}|xl'].
    rewrite !inE /= => /orP[|].
      apply/negP; by rewrite (simple_neg Hg) // symmetric_g.
    case/orP => [/eqP m'1m|/eqP m'1n2]; first by move: Hm'1; rewrite m'1m in_setD1 eqxx.
    suff : ucycle g [:: m; n2; n1] by apply acyclic_g.
    rewrite /ucycle /= !andbT !inE Hn2 /= symmetric_g -{1}m'1n2 n1m'1 /= symmetric_g Hn1 /=.
    by rewrite (negbTE (simple_neg _ Hn2)) //= (simple_neg Hg) //= eq_sym.
  rewrite !inE /= => /orP[|].
    apply/negP; apply: contraTN xl' => /eqP ->; exact: path_except_notin Hl'.
  case/orP => [/eqP xm|/eqP xn2].
    move: xl'; rewrite {}xm {x} => Hx.
    case/splitPr : Hx => l1 l2 in Hl' Hunl l'l Hlast.
    suff : ucycle g [:: m, n1, m'1 & l1] by apply acyclic_g.
    move: Hl'; rewrite -[in X in X -> _](cat1s m) catA cat_path cats1 => /andP[Hl' _].
    move: Hunl; rewrite -[in X in X -> _](cat1s m'1) -[in X in X -> _](cat1s m).
    rewrite 2!catA cat_uniq cats1 => /and3P[Hunl _ _].
    exact: uniq_path_ucycle_extend_1 Hl' Hunl.
  move: xl'; rewrite xn2 => Hx.
  case/splitPr : Hx => l1 l2 in Hl' Hunl l'l Hlast.
  suff : ucycle g [:: n2, m, n1, m'1 & l1] by apply acyclic_g.
  apply uniq_path_ucycle_extend_2 => //.
  by move: Hm'1; rewrite in_setD1 => /andP[].
  by move: Hl'; rewrite -[in X in X -> _](cat1s n2) catA cats1 cat_path => /andP[].
  by move: Hunl; rewrite -[in X in X -> _](cat1s m'1) catA cat_uniq => /andP[].
rewrite -cat_cons cat_uniq Hunk /=.
apply/andP; split; last first.
  by move: Hunl; rewrite rev_uniq lastI rcons_uniq => /andP[].
apply/hasP; case => x.
rewrite mem_rev => /mem_belast.
rewrite inE => /orP[/eqP ->{x}|].
  rewrite !inE.
  case/orP => [/eqP m'1m'2|m'1k].
    suff : ucycle g [:: n2; m; n1; m'1] by apply acyclic_g.
    rewrite /ucycle /= symmetric_g Hn2 /= Hn1 /= n1m'1 /= !andbT symmetric_g m'1m'2 n2m'2 /=.
    rewrite !inE !negb_or /= eq_sym (simple_neg Hg) //= eq_sym n1n2 /= (simple_neg Hg) //=.
    rewrite (simple_neg Hg) //= -m'1m'2 andbC (simple_neg Hg) //=.
    by move: Hm'1; rewrite in_setD1 eq_sym => /andP[].
  case/splitPr : m'1k => k1 k2 in Hk' Hunk k'k Hkast.
  suff : ucycle g [:: m'1, n1, m, n2, m'2 & k1] by apply acyclic_g.
  apply uniq_path_ucycle_extend_3 => //.
  by move: Hm'2; rewrite in_setD1 => /andP[].
  by move: Hm'1; rewrite in_setD1 => /andP[].
  by move: Hk'; rewrite -[in X in X -> _](cat1s m'1) catA cats1 cat_path => /andP[].
  by move: Hunk; rewrite -[in X in X -> _](cat1s m'2) catA cat_uniq => /andP[].
rewrite /= inE => Hx.
case/orP => [/eqP xm'2|xl'].
  move: Hx; rewrite xm'2 => xl'.
  case/splitPr : xl' => l1 l2 in Hl' Hunl l'l Hlast.
  suff : ucycle g [:: m'2, n2, m, n1, m'1 & l1] by apply acyclic_g.
  apply uniq_path_ucycle_extend_3 => //; first by rewrite eq_sym.
  by move: Hm'1; rewrite in_setD1 => /andP[].
  by move: Hm'2; rewrite in_setD1 => /andP[].
  by move: Hl'; rewrite -[in X in X -> _](cat1s m'2) catA cats1 cat_path => /andP[].
  by move: Hunl; rewrite -[in X in X -> _](cat1s m'1) catA cat_uniq => /andP[].
case/splitPr : Hx => l1 l2 in Hl' Hunl l'l Hlast.
case/splitPr : xl' => k1 k2 in Hk' Hunk k'k Hkast.
suff : ucycle g ((x :: rev k1) ++ (m'2 :: n2 :: m :: n1 :: m'1 :: l1)).
  apply acyclic_g; by rewrite /= size_cat /= addnC.
apply uniq_path_ucycle_cat_extend => //.
by move: Hm'2; rewrite in_setD1 => /andP[].
by move: Hm'1; rewrite in_setD1 => /andP[].
by move: Hl'; rewrite -(cat1s x) catA cat_path cats1 => /andP[].
by move: Hk'; rewrite -(cat1s x) catA cat_path cats1 => /andP[].
by move: Hunl; rewrite -cat_cons cat_uniq => /andP[].
by move: Hunk; rewrite -cat_cons cat_uniq => /andP[].
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
case/orP => [/eqP ->{x} | Hx].
  by rewrite /= inE (negbTE m1m0) /= inE eq_sym (negbTE (simple_neg Hg n1m1)).
rewrite /= inE.
case/orP.
  move/eqP => ?; subst x.
  case/splitPr : Hx => p1 p2 in Hp' Hun p'p Hlast.
  suff : ucycle g [:: m0, n1, m1 & p1] by apply acyclic_g.
  apply uniq_path_ucycle_extend_1 => //.
  by rewrite symmetric_g.
  by move: Hp';  rewrite -(cat1s m0) catA cat_path -cats1 => /andP[].
  by move: Hun; rewrite -cat_cons -(cat1s m0) catA cat_uniq cats1 => /andP[].
rewrite inE => /eqP xm1.
move/path_except_notin : Hp'; by rewrite -{}xm1 Hx.
Qed.

Lemma successor_subgraph_successor (Hg : simple g) n0 m0 m1 : g n0 m0 -> m1 != m0 ->
  m1 \in subgraph g m0 n0 -> ~~ g m1 n0.
Proof.
move=> n0m0 m1m0.
rewrite inE => /andP[_ /connectP[p]].
case/shortenP => p' Hp' Hun p'p Hlast.
apply/negP => abs.
suff : ucycle g [:: n0, m0 & p'].
  apply acyclic_g => /=.
  move: Hlast.
  destruct p' => //= /eqP; by rewrite (negbTE m1m0).
apply/andP; split.
  by rewrite /= n0m0 /= rcons_path -Hlast abs andbT (except_path Hp').
rewrite -(cat1s n0) cat_uniq Hun andbT /= negb_or inE /=.
rewrite eq_sym (simple_neg Hg n0m0) /=.
move/path_except_notin : Hp'; apply: contra.
rewrite -has_pred1 (@eq_in_has _ _ (pred1 n0)) // => x /=; by rewrite inE.
Qed.

End third_partition.
