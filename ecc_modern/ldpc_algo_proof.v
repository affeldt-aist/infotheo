(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
Require Import Wf_nat Init.Wf Recdef.
From mathcomp Require Import all_ssreflect perm zmodp matrix ssralg ssrnum.
From mathcomp Require Import Rstruct reals ring lra.
Require Import ssr_ext ssralg_ext bigop_ext f2.
Require Import fdist channel pproba linearcode subgraph_partition tanner.
Require Import tanner_partition summary ldpc checksum ldpc_algo.

(**md**************************************************************************)
(* # Verification of a Sum-Product decoder                                    *)
(*                                                                            *)
(* Formal verification of the implementation of sum-product decoding from     *)
(* the file `ldpc_algo.v`.                                                    *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope seq_scope.
Local Open Scope ring_scope.
Import GRing.Theory.

Section TnTreeEq.
Variables i U V : eqType.

Definition kind_eq_bool (k1 k2 : kind) : bool :=
  match k1, k2 with
  | kv, kv => true
  | kf, kf => true
  | _, _ => false
  end.

Lemma kind_eqP : Equality.axiom kind_eq_bool.
Proof.
by move=> [] []; constructor.
Qed.

HB.instance Definition _ := hasDecEq.Build _ kind_eqP.

Definition tag_eq_bool k (t1 t2 : tag k) : bool :=
  match t1, t2 with
  | Func, Func => true
  | Var a, Var b => a == b
  | _, _ => false
  end.

Lemma tag_eqP k : Equality.axiom (@tag_eq_bool k).
Proof.
move=> [|r] y; refine (match y with Func => _ | Var r' => _ end) => //=.
  by constructor.
case Hrr': (r == r').
  by rewrite (eqP Hrr'); constructor.
constructor.
move=> Hv.
move: Hrr'.
by injection Hv; move=> ->; rewrite eqxx.
Qed.

Section EqTag.
Variable k : kind.

HB.instance Definition _ := hasDecEq.Build _ (@tag_eqP k).

End EqTag.

Fixpoint depth {id k U D} (t : tn_tree id k U D) :=
  let l := map depth (children t) in
  (\max_(i <- l) i).+1.

Fixpoint tn_tree_eq_bool k (a b : tn_tree i k U V) : bool :=
  (node_id a == node_id b) && (node_tag a == node_tag b) &&
  (up a == up b) && (down a == down b) &&
  (length (children a) == length (children b)) &&
  let eqch := map (@tn_tree_eq_bool (negk k)) (children a) in
  all (fun p => fst p (snd p)) (zip eqch (children b)).

Lemma tn_tree_eqP k : Equality.axiom (@tn_tree_eq_bool k).
Proof.
move=> x.
pose d := depth x.
have Hd: (depth x <= d)%N by [].
clearbody d.
elim: d k x Hd => [|d IHd] k x Hd y.
  by destruct x; rewrite ltn0 in Hd.
case Heq: (tn_tree_eq_bool x y); constructor.
  case: x y Hd Heq => [id0 tag0 ch0 up0 down0] [id1 tag1 ch1 up1 down1] /= Hd.
  do! move/andP=>[]; do! move/eqP->; move=> Hlen Hall.
  congr Node.
  move: Hd ch1 Hall Hlen; clear -IHd.
  elim: ch0 => [| a chld0 IH] Hd [] // b chld1 /= /andP[ab Hch].
  rewrite eqSS => Hlen.
  rewrite /= big_cons in Hd.
  congr (_ :: _).
    apply/IHd => //.
    refine (leq_ltn_trans _ Hd).
    by rewrite leq_max leqnn.
  apply IH => //.
  by rewrite (leq_ltn_trans _ Hd) // leq_maxr.
move=> ?; subst y.
case: x Hd Heq => /= ? ? children ? ? Hd.
rewrite !eqxx /= => /negP; apply.
clear -IHd Hd.
elim: children Hd => //= a ch0 IH.
rewrite big_cons => Hd.
rewrite IH ?andbT.
  apply /IHd => //.
  refine (leq_ltn_trans _ Hd).
  by rewrite leq_max leqnn.
by rewrite (leq_ltn_trans _ Hd) // leq_maxr.
Qed.

Section EqTnTree.
Variable k : kind.

HB.instance Definition _ := hasDecEq.Build _ (@tn_tree_eqP k).

End EqTnTree.

End TnTreeEq.

Section BuildTreeOk.
Variables (m n : nat) (H : 'M['F_2]_(m, n.+1)).
Hypothesis tanner_acyclic : acyclic' (tanner_rel H).
Hypothesis tanner_connected : forall a b, connect (tanner_rel H) a b.

Variable rW : 'I_n.+1 -> R2.

Lemma select_children_spec s k i j :
  j \in select_children H s k i =
  tanner_rel H (id_of_kind k i) (id_of_kind (negk k) j)
  && (id_of_kind (negk k) j \notin (id_of_kind k i :: s)).
Proof.
by destruct k; rewrite /= !mem_filter !mem_ord_enum andbT tanner_relE.
Qed.

Lemma select_children_uniq s k i : uniq (select_children H s k i).
Proof.
by destruct k; rewrite /select_children filter_uniq // ord_enum_uniq.
Qed.

Lemma build_tree_rec_sound h s k i a b :
  graph (build_tree_rec H rW h s k i) a b -> tanner_rel H a b.
Proof.
move: h s k i a b.
elim => [|h Hh] s k i a b /=.
  by case: ifP => Ha //; case: ifP => Hb.
rewrite <- map_comp.
do 2!(case: ifP => [/eqP <- /mapP[j Hj ->]| _] /=;
      first by move: Hj; rewrite select_children_spec => /andP[Hj _];
      destruct h; rewrite // sym_tanner_rel).
by rewrite has_map => /hasP[j] Hj /Hh.
Qed.

Lemma labels_build_tree_rec h s k i :
  forall a,
    a \in labels (build_tree_rec H rW h s k i) ->
    uniq_path (tanner_rel H) (id_of_kind k i) s ->
    exists p,
      uniq_path (tanner_rel H) a (p ++ s) /\ last a p = id_of_kind k i /\
      forall b, b \in p -> b \in labels (build_tree_rec H rW h s k i).
Proof.
move: s k i.
elim: h => [|h Hh] s k i a.
  rewrite /= mem_seq1 => /eqP -> Hi; by exists [::].
rewrite [a \in _]/= in_cons -map_comp => Ha Hi.
case Hai: (a == id_of_kind k i) => /= in Ha.
  rewrite (eqP Hai) in Hi *; by exists [::].
move /flattenP: Ha => [l] /mapP [x Hx ->] Ha.
have Hsc := Hx.
rewrite select_children_spec /= in Hx.
move /andP: Hx => [Hx Hxs].
have Hi': uniq_path (tanner_rel H) (id_of_kind (negk k) x) (id_of_kind k i ::s).
  rewrite /uniq_path /= Hxs.
  move /andP: Hi => /= [-> ->].
  by rewrite sym_tanner_rel Hx.
have [p [Hp [Hal Hl]]] := Hh _ _ _ _ Ha Hi'.
exists (rcons p (id_of_kind k i)).
split.
  by rewrite cat_rcons.
split.
  by rewrite last_rcons.
move=> b /=.
rewrite mem_rcons !in_cons -map_comp.
set f := labels \o build_tree_rec H rW h (id_of_kind k i :: s) (negk k).
case: (b == id_of_kind k i) => //= Hb.
apply/flattenP => /=.
exists (f x); by [apply (map_f f) | apply Hl].
Qed.

Lemma id_of_kind_neq k i j :
  @id_of_kind m n k i == @id_of_kind m n (negk k) j = false.
Proof. by destruct k. Qed.

Lemma id_of_kind_inj k : injective (@id_of_kind m n k).
Proof. by destruct k; move=> a b []. Qed.

Lemma uniq_labels_build_tree_rec h s k i :
  uniq_path (tanner_rel H) (id_of_kind k i) s ->
  uniq (labels (build_tree_rec H rW h s k i)).
Proof.
elim: h s k i => [|h Hh] s k i Hi //=.
rewrite -map_comp.
set labels_tree := labels \o _.
case Ha: (id_of_kind k i \in _) => /=.
  move/flattenP: Ha => [l] /mapP [j Hj ->{l}] Hil.
  rewrite select_children_spec in Hj.
  case/labels_build_tree_rec: Hil => [|p [/andP[_ /=]]].
    rewrite /uniq_path /= sym_tanner_rel.
    by case/andP: Hj Hi => -> -> /andP /=[-> ->].
  by rewrite mem_cat in_cons eqxx orbT.
set l := select_children H s k i in Ha *.
have Hch: uniq l by apply select_children_uniq.
have Hsub: {subset l <= select_children H s k i} by [].
elim: l => //= c l IH in Ha Hch Hsub *.
rewrite cat_uniq.
have Hspec: c \in select_children H s k i.
  by apply Hsub; rewrite in_cons eqxx.
rewrite select_children_spec in Hspec.
(* 3 cases: uniq head, uniq tail, and no intersection *)
apply/andP; split.
  (* head *)
  apply Hh.
  rewrite /uniq_path /= sym_tanner_rel.
  by case/andP: Hspec Hi => -> -> /andP /=[-> ->].
rewrite {}IH ?andbT; first last. (* tail *)
      by move=> x Hx; apply Hsub; rewrite in_cons Hx orbT.
    by move/andP/proj2: Hch.
  move: Ha; rewrite mem_cat.
  by case Hl: (_ \in labels _).
(* intersection *)
apply/hasP => /= -[x Hx Hmem] {Ha Hh}.
case/labels_build_tree_rec: Hmem => [|p [Hun [Hl _]]].
  rewrite /uniq_path /= sym_tanner_rel.
  by case/andP: Hspec Hi => -> -> /andP /=[-> ->].
move/flattenP: Hx => /= [d /mapP[y Hy ->{d}] Hxd].
have Hspec': y \in c :: l by rewrite in_cons Hy orbT.
apply Hsub in Hspec'.
rewrite {Hsub Hspec} select_children_spec in Hspec'.
case/labels_build_tree_rec: Hxd => [|p' [Hun' [Hl' _]]].
  rewrite /uniq_path /= sym_tanner_rel.
  by case/andP: Hspec' Hi => -> -> /andP /=[-> ->].
(* Now let's prove we have a cycle *)
move: (@tanner_acyclic (id_of_kind k i) (id_of_kind (negk k) y)
                      (rev (belast x p') ++ p)) {Hspec' Hi}.
rewrite in_cons mem_cat /=.
rewrite id_of_kind_neq /=.
move/andP/proj2: (Hun').
rewrite -cat1s catA cat_uniq mem_rev.
move/andP/proj2/andP/proj1/norP/proj1.
case Hip': (_ \in belast x p') => /=.
  by rewrite (mem_belast Hip').
move => _.
move/andP/proj2: (Hun).
rewrite /= cat_uniq /= sym_tanner_rel.
move/and4P => [_ _] /norP/proj1 Hid _ /(_ Hid){Hid}.
case Hiy: (tanner_rel H _ _); last first.
  move=> _; move/andP/proj1: Hun' Hiy.
  rewrite -cat_rcons cat_path => /andP/proj1.
  destruct p'; simpl in Hl'.
    by rewrite /= Hl' andbT => ->.
  by rewrite lastI Hl' /= rcons_path !last_rcons => /andP/proj2 ->.
rewrite /= rcons_cat cat_path.
move/andP/proj1: Hun'.
rewrite cat_path => /andP/proj1 Hun'.
rewrite (eq_path (sym_tanner_rel H)) -rev_path in Hun'.
rewrite -Hl' Hun' /=.
move/andP/proj1: Hun.
rewrite -cat_rcons cat_path => /andP/proj1 Hun.
destruct p' as [|z p']; simpl in *.
  rewrite Hun Hl Hl'.
  rewrite (inj_eq (@id_of_kind_inj _)).
  move/(_ (eqxx true)) => Hcy.
  by rewrite (eqP Hcy) Hy in Hch.
rewrite rev_cons last_rcons Hun.
rewrite last_cat last_rcons.
rewrite Hl Hl' (inj_eq (@id_of_kind_inj _)).
move/(_ (eqxx true)) => Hcy.
by rewrite (eqP Hcy) Hy in Hch.
Qed.

Lemma seq_full {A:finType} (s : seq A) a : (#|A| - #|s| <= 0)%N -> a \in s.
Proof.
move=> Hh.
have Hs: finset (mem s) = [set: A].
  apply/eqP.
  rewrite eqEcard subsetT /=.
  rewrite cardsT cardsE.
  by rewrite /leq subn0 in Hh.
by move/setP : Hs => /(_ a); rewrite !inE.
Qed.

Definition lastE := (last_cat, last_rcons, last_cons).

Lemma card_uniq_seq_decr {T : finType} x (s : seq T) h :
  (#|T| - #|s| <= h.+1)%N -> uniq (x :: s) -> (#|T| - #|x :: s| <= h)%N.
Proof.
move=> Hh Hun.
move /card_uniqP: (Hun) => ->.
rewrite /leq -!subnDA in Hh *.
rewrite /= addSnnS.
rewrite /= in Hun.
by move /andP/proj2/card_uniqP: Hun => <-.
Qed.

Lemma build_tree_rec_ok h k i s :
  (#|sumbool_ord m n.+1| - #|s| <= h)%N ->
  uniq_path (tanner_rel H) (id_of_kind k i) s ->
  let l := labels (build_tree_rec H rW h s k i) in
  forall a b, a \in l -> b \in l ->
    tanner_rel H a b -> graph (build_tree_rec H rW h s k i) a b.
Proof.
elim: h k i s => [|h IHh] k i s Hh Hi.
  have His : id_of_kind k i \in s by exact: seq_full.
  by rewrite /uniq_path /= His andbF in Hi.
move=> l.
have Hab b: b \in l -> tanner_rel H (id_of_kind k i) b ->
  b \in [seq node_id i
        | i <- [seq build_tree_rec H rW h (id_of_kind k i :: s) (negk k) j
               | j <- select_children H s k i]].
  move=> Hb HH.
  rewrite -map_comp.
  apply /mapP.
  have [x Hx]: exists x, b = id_of_kind (negk k) x.
    move: HH; clear; rewrite tanner_relE.
    case: k b i => -[] b i // _; by exists b.
  exists x; last by destruct h.
  rewrite select_children_spec.
  rewrite -Hx HH /=.
  case Hbs: (b \in s).
    have [p [Hp [Ha Hl]]] := labels_build_tree_rec Hb Hi.
    rewrite in_cons Hx eq_sym id_of_kind_neq /=.
    move /andP/proj2: Hp.
    by rewrite cons_uniq mem_cat Hbs orbT.
  by rewrite /= in_cons Hbs Hx eq_sym id_of_kind_neq.
move=> a b Ha Hb HH /=.
case: ifP => Heq.
  rewrite -(eqP Heq) in HH; by apply Hab.
case: ifP => Heq'.
  rewrite sym_tanner_rel -(eqP Heq') in HH; by apply Hab.
clear Hab.
simpl in l.
rewrite /l in_cons eq_sym Heq /= in Ha.
rewrite {}/l in_cons eq_sym Heq' /= in Hb.
move /flattenP: Ha => [sa Ha Hsa].
move /flattenP: Hb => [sb Hb Hsb].
rewrite -!map_comp in Ha Hb.
move /mapP: Ha => [ia Hia Ha].
move /mapP: Hb => [ib Hib Hb].
subst sa sb.
rewrite !select_children_spec in Hia Hib.
move /andP: Hia => [Hia Hias].
move /andP: Hib => [Hib Hibs].
move /andP: (Hi) => [Hpi Hun].
case Hiab: (ia == ib).
  rewrite has_map /=.
  apply /hasP.
  exists ia.
    by rewrite select_children_spec; exact/andP.
  rewrite -(eqP Hiab) in Hsb.
  apply: IHh => //.
    exact: card_uniq_seq_decr.
  by apply cons_uniq_path => //; rewrite sym_tanner_rel.
set sa := id_of_kind (negk k) ia in Hia Hias.
set sb := id_of_kind (negk k) ib in Hib Hibs.
set si := id_of_kind k i in Hia Hib Hsa Hsb Hias Hibs.
have Hiap: uniq_path (tanner_rel H) sa (si :: s).
  by rewrite /uniq_path /= sym_tanner_rel Hia Hpi Hias.
have Hibp: uniq_path (tanner_rel H) sb (si :: s).
  by rewrite /uniq_path /= sym_tanner_rel Hib Hpi Hibs.
have [p1 [Hp1 [Hal Hpl1]]]:= labels_build_tree_rec Hsa Hiap.
have [p2 [Hp2 [Hbl Hpl2]]]:= labels_build_tree_rec Hsb Hibp.
suff: false by [].
rewrite -/sb -/sa -/si in Hp1 Hp2 Hi Hpi Hun Hal Hbl.
clear -Hp1 Hp2 Hi Hpi Hun Hal Hbl Hiab HH tanner_acyclic.
move: (@tanner_acyclic si sb (rev (belast b p2) ++ a :: p1)).
rewrite !lastE Hal.
case Hsasb: (sa == sb).
  move /eqP: Hsasb.
  rewrite /sa /sb=> eq.
  by destruct k; inversion eq; rewrite H1 eqxx in Hiab.
move=> Hcy.
move: Hp1 => /andP[Hp1 Hun1].
move: Hp2 => /andP[Hp2 Hun2].
apply Hcy; clear Hcy Hsasb.
  rewrite -cat_cons -rev_rcons -{1}Hbl -lastI.
  rewrite mem_cat mem_rev negb_or.
  have Hsi c p: uniq ((si :: c :: p) ++ s) = uniq (c :: p ++ si :: s).
    apply perm_uniq.
    rewrite -cat1s -(cat1s c) perm_sym -cat1s -(cat1s si).
    rewrite !catA perm_cat2r.
    by rewrite perm_catC catA.
  rewrite -!Hsi !cat_uniq in Hun1 Hun2.
  case/andP/proj1/andP: Hun2 => -> _.
  by case/andP/proj1/andP: Hun1.
rewrite {Hun1 Hun2} /cycle.
rewrite -cats1 -cat_cons -rev_rcons -catA cat_path -{1 2}Hbl -lastI.
have {1}->: si = last b (rcons p2 si) by rewrite last_rcons.
rewrite -{1}(belast_rcons b p2 si) rev_path rev_cons !lastE.
apply /andP; split.
  rewrite -(eq_path (sym_tanner_rel _)) -cats1.
  rewrite -cat1s catA cat_path in Hp2.
  by case/andP: Hp2.
rewrite /= sym_tanner_rel HH.
rewrite -cat1s catA cat_path in Hp1.
by case/andP: Hp1.
Qed.

Definition tanner_split (s : seq (sumbool_ord m n.+1)) :
    rel (sumbool_ord m n.+1) :=
  fun a b => if (a \in s) || (b \in s) then false else tanner_rel H a b.

Lemma tanner_split_tanner s : subrel (tanner_split s) (tanner_rel H).
Proof. rewrite /subrel /tanner_split => x y; by case: ifP. Qed.

Lemma tanner_split_nil : tanner_split [::] =2 tanner_rel H.
Proof. by []. Qed.

Lemma tanner_split_cons c s : subrel (tanner_split (c :: s)) (tanner_split s).
Proof.
rewrite /subrel /tanner_split /= => a b.
rewrite in_cons in_cons.
case Ha: (a \in s); first by rewrite /= orbT.
case Hb: (b \in s); first by rewrite /= orbT orbT.
by case: ifP.
Qed.

Lemma tanner_rel_split (s : seq (sumbool_ord m n.+1)) (x : sumbool_ord m n.+1) p :
  ~~ has (mem s) (x :: p) -> path (tanner_rel H) x p -> path (tanner_split s) x p.
Proof.
move: x s.
elim: p => //= y p IHp x s Hs /andP[Hx Hp].
rewrite IHp //.
  rewrite /tanner_split Hx.
  by case/norP: Hs => /negbTE -> /norP[] /negbTE ->.
by case/norP: Hs.
Qed.

Lemma tanner_split_uncons (s : seq (sumbool_ord m n.+1))
    (c x : sumbool_ord m n.+1) p :
  c \notin (x :: p) -> path (tanner_split s) x p ->
  path (tanner_split (c :: s)) x p.
Proof.
move: c x s.
elim: p => [//|/=y p IHp] c x s Hc /andP[Hx Hp].
rewrite IHp //.
  move: Hx Hc; rewrite /tanner_split /= 2!(in_cons c).
  case: ifPn => // /norP[] /negbTE -> /negbTE -> ->.
  by rewrite 2!in_cons !(eq_sym c) => /norP[/negbTE->] /norP[/negbTE->].
by move /norP/proj2: Hc.
Qed.

Lemma build_tree_rec_full h k i s :
  (#|sumbool_ord m n.+1| - #|s| <= h)%N ->
  uniq_path (tanner_rel H) (id_of_kind k i) s ->
  mem (labels (build_tree_rec H rW h s k i)) =i
  connect (tanner_split s) (id_of_kind k i).
Proof.
elim: h k i s => [|h IHh] k i s Hh Hc.
  have His: id_of_kind k i \in s by apply seq_full.
  by rewrite /uniq_path /= His andbF in Hc.
move=> a /=.
rewrite in_cons.
case Hai: (a == id_of_kind k i); simpl.
  symmetry.
  rewrite inE (eqP Hai).
  apply /connectP.
  by exists [::].
move/andP: Hc => [] /= Hc Hun.
have Hh': (#|sumbool_ord m n.+1| - #|id_of_kind k i :: s| <= h)%N.
  by apply card_uniq_seq_decr.
have Hchild o: o \in select_children H s k i ->
  uniq_path (tanner_rel H) (id_of_kind (negk k) o) (id_of_kind k i :: s).
  rewrite /uniq_path /= Hc Hun.
  rewrite select_children_spec.
  move /andP=> [Hio Hos].
  by rewrite sym_tanner_rel Hio Hos.
rewrite inE.
case Hcb: (connect _ _ a).
  rewrite -map_comp.
  apply /flatten_mapP.
  move /connectP: Hcb => [p Hcb Ha].
  have Hsp:= shortenP Hcb.
  set a' := last (id_of_kind k i) p in Hsp.
  have : a = a' by rewrite Ha.
  destruct Hsp as [p3 Hp Hun' Hsp].
  clear p Hcb Ha Hsp.
  move => Ha.
  rename p3 into p.
  destruct p.
    by rewrite Ha /= eqxx in Hai.
  have [o Ho]: exists o, s0 = id_of_kind (negk k) o.
    apply (sub_path (@tanner_split_tanner _)) in Hp.
    destruct k, s0.
      by rewrite tanner_relE in Hp.
      by eexists; reflexivity.
      by eexists; reflexivity.
      by rewrite tanner_relE in Hp.
  subst s0.
  have Ho: o \in select_children H s k i.
    rewrite select_children_spec.
    apply /andP; split.
      apply (@tanner_split_tanner s).
      by move /andP/proj1: Hp.
    rewrite in_cons.
    move: (Hun').
    rewrite /= in_cons.
    move /andP/proj1/norP/proj1/negbTE => Hoi.
    rewrite eq_sym Hoi.
    move /andP/proj1: Hp.
    rewrite /tanner_split.
    case: (id_of_kind (negk k) o \in s); last by [].
    by rewrite orbT.
  exists o; first by [].
  rewrite IHh //.
    rewrite inE.
    apply /connectP.
    exists p => //.
    apply tanner_split_uncons.
      by move /andP/proj1: Hun'.
    by move /andP/proj2: Hp.
  exact: Hchild.
rewrite -map_comp.
apply /flatten_mapP => Hl.
move: Hl => [l Hl Hal].
rewrite IHh // in Hal.
  rewrite inE in Hal.
  move /connectP: Hcb.
  apply.
  move /connectP: Hal => [p Hp Hlp].
  exists (id_of_kind (negk k) l :: p); last by [].
  simpl.
  apply /andP; split.
    rewrite select_children_spec in Hl.
    rewrite /tanner_split.
    move /andP/proj1/negbTE: Hun => ->.
    rewrite in_cons in Hl.
    move /andP/proj2/norP/proj2/negbTE: (Hl) => -> /=.
    by move /andP/proj1: Hl.
  by apply (sub_path (@tanner_split_cons (id_of_kind k i) _)).
by apply Hchild.
Qed.

Lemma build_tree_full k i a :
  a \in labels (build_tree_rec H rW #|sumbool_ord m n.+1| [::] k i).
Proof.
rewrite build_tree_rec_full //.
  rewrite inE.
  apply /connectP.
  move /connectP: (tanner_connected (id_of_kind k i) a) => [p Hp Ha].
  by exists p.
by rewrite card_sum !card_ord card0 subn0.
Qed.

Theorem build_tree_ok k i :
  tanner_rel H =2 graph (build_tree H rW (k:=k) i).
Proof.
rewrite /build_tree => a b.
case Htan: (tanner_rel H a b).
  symmetry.
  apply build_tree_rec_ok with (s:=[::]).
  + by rewrite card_sum !card_ord card0 subn0.
  + by [].
  + exact: build_tree_full.
  + exact: build_tree_full.
  + by [].
symmetry.
move: Htan.
exact/contraFF/build_tree_rec_sound.
Qed.

End BuildTreeOk.

Section BuildTreeTest.
Let R := Rdefinitions.R.
Let m := 2%N.
Let n := 3%N.
Let id' := sumbool_ord m n.

Let F (i : 'I_m) (j : 'I_n) :=
  (j == widen_ord (leqnSn 2) i) || (j == lift 0 i).
Let H := \matrix_(i<2,j<3) (F i j : 'F_2).

Let rW (i : 'I_n) : R*R := (0,1)%R.

(* How can we make this to compute? *)
(* Eval compute in @build_tree 3 2 H f0 0. *)

Fixpoint my_ord_enum (n : nat) : seq 'I_n :=
  match n as m return m = n -> seq 'I_n with
  | 0 => fun _ => [::]
  | S n' => fun e =>
    match e with eq_refl =>
     eq_rect (n'.+1) (fun n => seq 'I_n)
             (@Ordinal n'.+1 n' (ltnSn n') ::
                       map (widen_ord (leqnSn n')) (my_ord_enum n'))
        n e
    end
  end (Logic.eq_refl _).

Definition enum_id : seq id' :=
  map inl (my_ord_enum m) ++ map inr (my_ord_enum n).

Definition myrel (i j : id') : bool :=
  match i, j with
  | inl i, inr j => F i j
  | inr j, inl i => F i j
  | _, _ => false
  end.

Fixpoint mypath (h : nat) : seq (seq id') :=
  match h with
  | 0 => [::]
  | S h' =>
    let ll := [::] :: mypath h' in
    flatten
      [seq [seq i :: l | l <- ll & path myrel i l] | i <- enum_id]
  end.

Theorem test_acyclic : forall p, p \in [::] :: mypath (m+n) ->
                                (size p > 2)%N ==> ~~ ucycleb myrel p.
Proof. by apply /allP. Qed.

Lemma myrel_ok : myrel =2 tanner_rel H.
Proof.
rewrite /myrel tanner_relE /tanner_rel' /= /H /=.
move=> [a|a] [b|b] //; rewrite mxE.
  by destruct (F a b).
by destruct (F b a).
Qed.

Lemma my_ord_enum_ok (h : nat) (a : 'I_h) : a \in my_ord_enum h.
Proof.
elim: h a => [|h Hh] a.
  move: (ltn_ord a).
  by rewrite ltn0.
rewrite /= in_cons.
have [//=|a_not_h] := eqVneq a (Ordinal (ltnSn h)).
suff a_ltn_h : (a < h)%N.
  apply/mapP.
  exists (Ordinal a_ltn_h) => //.
  exact/val_inj.
by rewrite ltn_neqAle a_not_h /= -ltnS.
Qed.

Lemma enum_id_ok (a : id') : a \in enum_id.
rewrite /enum_id mem_cat.
apply /orP.
destruct a; [left | right]; apply /map_f/my_ord_enum_ok.
Qed.

Lemma mypath_ok_rec h a p :
  (size p < h)%N -> path myrel a p -> (a :: p \in mypath h).
Proof.
elim: h a p => [//|h IHh] a p Hp Hun.
suff : a :: p \in flatten [seq [seq i :: l |
  l <- [::] :: mypath h & path myrel i l] | i <- enum_id] by [].
apply /flattenP.
exists [seq a :: l | l <- [::] :: mypath h & path myrel a l].
  apply /mapP.
  exists a => //; by rewrite enum_id_ok.
destruct p.
  by rewrite in_cons eqxx.
apply /mapP.
exists (s :: p) => //.
rewrite mem_filter Hun in_cons IHh ?orbT //.
simpl in Hun.
by move /andP/proj2: Hun => ->.
Qed.

Lemma mypath_ok a p :
  uniq (a :: p) -> path myrel a p -> (a :: p) \in mypath (m+n).
Proof.
move /card_uniqP => Hsz Hp.
have Hc : (#|a::p| <= #|id'|)%N by apply max_card.
rewrite Hsz card_sum !card_ord in Hc.
by apply mypath_ok_rec.
Qed.

Lemma test_connected : forall ab, ab \in allpairs pair enum_id enum_id ->
  has (fun p =>
         let (a,b) := ab in
         if p is x :: p then (a == x) && path myrel a p && (b == last x p)
         else a == b)
      (mypath (m+n)).
Proof. apply /allP; by vm_compute. Qed.

Theorem test_graph : forall k i,
    tanner_rel H =2 graph (build_tree H rW (k:=k) i).
Proof.
apply build_tree_ok.
+ apply acyclic_equiv.
  suff : acyclic myrel.
    rewrite /acyclic=> Hac p Hlen Huc.
    apply (Hac _ Hlen).
    by rewrite /ucycle /ucycleb (eq_cycle myrel_ok).
  move=> p Hlen Hun.
  apply/negP: (Hun).
  apply /implyP/test_acyclic: Hlen.
  rewrite in_cons.
  destruct p; first by [].
  move /andP: Hun => [Hp Hun].
  rewrite mypath_ok ?orbT //.
  rewrite /cycle rcons_path in Hp.
  by move/andP/proj1: Hp.
+ move => a b.
  have Hab: (a,b) \in allpairs pair enum_id enum_id.
    apply/allpairsP.
    exists (a,b). simpl.
    by rewrite !enum_id_ok.
  apply/connectP.
  move /hasP: (test_connected Hab) => [[|x p] _ Hp].
    rewrite (eqP Hp).
    by exists [::].
  move /andP: Hp => [] /andP [] /eqP -> Hp /eqP ->.
  exists p => //; by rewrite -(eq_path myrel_ok) Hp.
Qed.

End BuildTreeTest.

Section AlgoProof.
Variables m n' : nat.
Let n := n'.+1.
Variable H : 'M['F_2]_(m, n).
Hypothesis tanner_acyclic : acyclic' (tanner_rel H).
Hypothesis tanner_connected : forall a b, connect (tanner_rel H) a b.
Local Notation "''V(' x ',' y ')'" := (Vgraph H x y).
Local Notation "''F(' x ',' y ')'" := (Fgraph H x y).
Variable B : finType.
Open Scope channel_scope.
Open Scope vec_ext_scope.
Open Scope proba_scope.
Variable W : `Ch('F_2, B).
Let C := kernel H.
Let C_not_empty := Lcode0.not_empty C.
Variable vb : (`U C_not_empty).-receivable W.
Local Notation "''V'" := (Vnext H).
Local Notation "''F'" := (Fnext H).

Let rW n0 := (W 0 (vb ``_ n0), W 1 (vb ``_ n0)).

Let id' := sumbool_ord m n.

Let tn_tree' k := tn_tree id' k R2 R2.

Lemma msg_none_eq (i1 i2 i : id') k :
  i1 != i -> i2 != i -> @msg _ _ i1 i2 (Some i) k =1 @msg _ _ i1 i2 None k.
Proof.
move=> Hi1 Hi2 [id0 tag0 ch0 up0 down0] /=.
case: ifP => [/eqP [] |] Hi1'.
  by rewrite Hi1' eqxx in Hi1.
case: ifP => [/eqP [] | //] Hi2'.
by rewrite Hi2' eqxx in Hi2.
Qed.

Lemma subseq_labels {A:eqType} {k U P} (l : seq (tn_tree A k U P)) :
  subseq (map node_id l) (flatten (map labels l)).
Proof.
elim: l => [//|a l Hl].
case: a => [id0 tag0 ch0 up0 down0] /=.
rewrite eqxx.
rewrite -(cat0s [seq node_id i | i <- l]).
apply cat_subseq => //; exact: sub0seq.
Qed.

Lemma children_ind {i U V : eqType}
    (P : forall k, @tn_tree i k U V -> Prop) :
  (forall k t, (forall t', t' \in children t -> P _ t') -> P k t) ->
  forall k t, P k t.
Proof.
move=> HP k t.
set h := depth t.
have : (depth t <= h)%N by [].
clearbody h.
move: k t.
elim: h => [|h IH] k t Hh.
  by destruct t.
destruct t; simpl in *.
rewrite ltnS in Hh.
apply HP => /= t' Ht'.
apply: IH.
by rewrite (leq_trans _ Hh)// big_map leq_bigmax_seq.
Qed.

Lemma msg_nil i1 i2 (i : option id') {k} t :
  (i1 \notin i ++ labels t) || (i2 \notin i ++ labels t) ->
  size (@msg _ _ i1 i2 i k t) = 0.
Proof.
move: k t i.
refine (children_ind _).
move=> k [id0 tag0 ch0 up0 down0] /= IH i.
rewrite !mem_cat !in_cons.
case: ifP => Hi1 /=.
  rewrite -(eqP Hi1) !in_cons eqxx /=.
  case: ifP => Hi2' //.
  by rewrite orbT.
case: ifP => Hi2 /=.
  rewrite -(eqP Hi2) !in_cons eqxx /=.
  rewrite !orbF => Hi1'.
  case: ifP => {}Hi1 //.
  by rewrite Hi1 orbT in Hi1'.
rewrite size_flatten.
move=> Hch.
rewrite /shape.
rewrite -map_comp.
rewrite sumnE.
rewrite big_seq big1 //= => i' /mapP[l Hl] -> /=.
apply/IH => //.
case Hi1l: (i1 \notin _); first by [].
case Hi2l: (i2 \notin _); first by [].
simpl; symmetry.
move /orP: Hch => [Hch | Hch]; apply/contraNF: Hch => _.
  move: Hi1l; rewrite mem_cat in_cons.
  case Hi1i: (i1 \in (i : seq id')) => //=.
  case Hi10: (i1 == id0) => //= Hi1l.
  apply/flattenP.
  exists (labels l).
    by apply (map_f labels).
  by apply (negbFE Hi1l).
move: Hi2l; rewrite mem_cat in_cons.
case Hi2i: (i2 \in (i : seq id')) => //=.
have [//|/= Hi20 Hi2l] := eqVneq i2 id0.
apply/flattenP.
exists (labels l).
  exact: (map_f labels).
exact: (negbFE Hi2l).
Qed.

Corollary msg_nonnil (i1 i2 : id') i {k} t :
  (size (@msg _ _ i1 i2 i k t) > 0)%N ->
  i1 \in i ++ labels t /\ i2 \in i ++ labels t.
Proof.
move=> Hsz.
case Hi1: (i1 \in _).
  case Hi2: (i2 \in _); first by [].
  rewrite msg_nil // in Hsz.
  by rewrite Hi2 orbT.
rewrite msg_nil // in Hsz.
by rewrite Hi1.
Qed.

Lemma msg_sz (i1 i2 : id') {k} t :
  uniq (labels t) -> size (@msg _ _ i1 i2 None k t) = graph t i1 i2.
Proof.
move: k t; refine (children_ind _).
move=> k [id0 tag0  ch0 up0 down0] /= IH Hun.
rewrite !(eq_sym id0).
case: ifPn => Hi1.
  rewrite -(eqP Hi1).
  rewrite size_flatten /shape.
  rewrite -map_comp.
  rewrite (@eq_map _ _ (size \o msg i1 i2 (Some i1))
                  (pred1 i2 \o node_id)); last first.
    move=> [id1 ? ? ? ?] /=.
    by rewrite eqxx (eq_sym id1); case: ifP.
  rewrite 2!map_comp.
  rewrite -map_comp.
  rewrite count_sumn.
  apply: count_uniq_mem.
  move /andP: Hun => [_].
  by apply: subseq_uniq; exact: subseq_labels.
case: ifPn => Hi2.
  move /andP: Hun => [_ Hun].
  rewrite -(eqP Hi2).
  rewrite size_flatten /shape.
  rewrite -map_comp.
  rewrite (@eq_map _ _ (size \o msg i1 i2 (Some i2))
                  (pred1 i1 \o node_id)); last first.
    move=> [id1 ? ? ? ?] /=.
    rewrite eqxx.
    rewrite (eq_sym id1).
    case: ifP => [/eqP [Hi12]|].
      by rewrite Hi12; case: ifP.
    by case: ifP.
  rewrite !map_comp.
  rewrite -map_comp.
  rewrite count_sumn.
  apply: count_uniq_mem.
  by apply: subseq_uniq Hun; exact: subseq_labels.
rewrite (eq_map (msg_none_eq _ _)); [|by rewrite Hi1|by rewrite Hi2].
elim: ch0 => [//| a l IHc] /= in IH Hun *.
rewrite size_cat.
move: Hun; rewrite cat_uniq => /andP[Hni] /andP [Huna] /andP [Hal Hunl].
have {}IHc: size (flatten [seq msg i1 i2 None i | i <- l]) =
          has (fun n0 => graph n0 i1 i2) l.
  apply: IHc.
    by move=> t' t'l /IH; apply; rewrite in_cons t'l orbT.
  by move: Hni; rewrite mem_cat => /norP[_ ->].
case Ha: (graph a i1 i2).
  have Hsz:= f_equal nat_of_bool Ha.
  rewrite -(IH _ _ Huna) in Hsz; last by rewrite in_cons eqxx.
  have Hsz': (size (msg i1 i2 None a) > 0)%N by rewrite Hsz.
  have {Hsz'}[/= Hi1' Hi2']:= msg_nonnil Hsz'.
  suff ->: size (flatten [seq msg i1 i2 None i | i <- l]) = 0 by rewrite addn0.
  rewrite size_flatten sumnE big_seq/= big1// => i.
  rewrite /shape -map_comp => /mapP[x xl] -> /=.
  apply/msg_nil => /=; apply/orP; left.
  apply/contra: Hal => Hi1x.
  apply/hasP; exists i1; last by [].
  by apply/flattenP; exists (labels x) => //; exact/(map_f labels).
rewrite IH => //=; last by rewrite in_cons eqxx.
by rewrite Ha /= add0n.
Qed.

Let beta' := ldpc.beta H W vb.
Let alpha' := ldpc.alpha H W vb.

Lemma beta_def n0 m0 (d : 'rV_n) :
  let d0 := d `[ n0 := 0 ] in
  let d1 := d `[ n0 := 1 ] in
  beta (rW n0) [seq (alpha' m1 n0 d0, alpha' m1 n0 d1) | m1 in 'F n0 :\ m0]
  = (beta' n0 m0 d0, beta' n0 m0 d1).
Proof.
rewrite /rW /beta' /alpha' /ldpc.beta /=.
rewrite /image_mem /enum_mem.
rewrite -big_filter.
rewrite -[in X in _ = (_, X)]big_filter.
have [e He [ue Pe perme]] := big_enumP _.
rewrite {3 5}/row_set !mxE !eqxx /=.
move: (W 0 (vb ``_ n0)) (W 1 (vb ``_ n0)).
elim: e {He ue Pe perme} => [|a l IH] p0 p1.
  by rewrite /= !big_nil !mulr1.
by rewrite /= !big_cons /= IH // !mulrA.
Qed.

Lemma rmul_foldr_rsum (R := Rdefinitions.R) {I A} {X : finType} (a : R) (g : I -> X -> A -> A)
  (F0 : A -> R) l d :
  a *
  foldr (fun n1 (F : A -> R) t => \sum_(x in X) F (g n1 x t))
         F0 l d =
  foldr (fun n1 (F : A -> R) t => \sum_(x in X) F (g n1 x t))
        (fun t => a * F0 t) l d.
Proof.
elim: l d => [|x l IH] d //=.
rewrite big_distrr.
apply eq_bigr => i Hi.
apply IH.
Qed.

Definition tanner : Tanner.acyclic_graph (tanner_rel H).
  constructor.
    econstructor; try by [].
    + apply sym_tanner_rel.
    + exact: (Colorable.Build_graph (colorable_tanner_rel H)).
  by apply acyclic_equiv.
Qed.

(* TODO: move? *)
Lemma checksubsum_add n0 n1 x y (d : 'rV_n) (l : seq 'I_n) :
  n1 != n0 -> n0 \notin l -> n1 \notin l ->
  (x + y != \delta [set x in l] (d `[ n1 := x + y]))%R =
  (y != \delta [set x in n0 :: l] ((d `[ n0 := x]) `[ n1 := y])).
Proof.
move=> n1_n0 n0_l n1_l.
congr (negb _).
rewrite GRing.addrC eq_sym -GRing.subr_eq eq_sym /=.
congr (_ == _).
rewrite (row_setC _ _ _ n1_n0) (GRing.oppr_char2 _ x) //.
rewrite {2}/checksubsum [in X in _ = X](bigD1 n0) /=; last by rewrite !inE eqxx.
rewrite !mxE eqxx.
rewrite GRing.addrC /checksubsum F2_of_bool_addr.
congr (F2_of_bool ((_ + _)%R == _)).
apply congr_big => // i.
  rewrite !inE.
  have [->|] := eqVneq i n0; first exact/negbTE.
  by rewrite andbT.
rewrite !inE !mxE.
have [->|] := eqVneq i n0.
  by rewrite (negbTE n0_l).
have [->|//] := eqVneq i n1.
by rewrite (negbTE n1_l).
Qed.

Lemma alpha_def_sub (R := Rdefinitions.R) m0 n1 n0 (x y : 'F_2) (l : seq 'I_n) d :
  n1 \notin l -> uniq l -> n0 != n1 -> n0 \notin l -> n1 \in 'V m0 :\ n0 ->
  {subset l <= 'V m0 :\ n0} ->
  beta' n1 m0 (d`[n1 := x]) *
  foldr (fun n2 (F : 'rV_n -> R) t => \sum_(x in 'F_2) F (t`[n2 := x]))
    (fun t => (t ``_ n0 != \delta [set x in l] t)%:R *
              (\prod_(n3 in [set x in l]) beta' n3 m0 t))
    l (d`[n0 := x + y])%R =
  foldr (fun n2 (F : 'rV_n -> R) t => \sum_(x in 'F_2) F (t`[n2 := x]))
    (fun t => (t ``_ n0 != \delta [set x in n1 :: l] t)%:R *
              (\prod_(n3 in [set x in n1 :: l]) beta' n3 m0 t))
    l ((d`[n0 := y])`[n1 := x]).
Proof.
move=> n1_l Hun n0_n1 n0_l Hn1 Hsub.
have d' := d.
have n1_Vm0 : n1 \in 'V m0 by move: Hn1; rewrite in_setD1; case/andP.
rewrite {1}/beta'.
rewrite (@beta_inva _ _ _ _ _ _ _ _ _ (d'`[n1 := x])) => //; last first.
  by rewrite !mxE eqxx.
rewrite rmul_foldr_rsum.
pose l' := l.
rewrite -{3 6}/l'.
have n1_l' := n1_l.
have n0_l' := n0_l.
rewrite -/l' in n1_l' n0_l'.
elim: l' => [|hd tl IH] /= in d n1_l' n0_l' *.
  rewrite [X in _ = _ * X](bigD1 n1) /=; last by rewrite !inE eqxx.
  rewrite (@beta_inva _ _ _ _ W _ _ m0 _ ((d`[n0 := y])`[n1 := x])) //; last first.
    by rewrite !mxE eqxx.
  rewrite mulrA mulrA [X in _ = X * _]mulrC.
  congr (_ * _).
    congr (_ * _%:R).
    rewrite row_setC; last by rewrite eq_sym.
    by rewrite !mxE eqxx (@checksubsum_add n1).
  apply congr_big => // i.
    rewrite !inE.
    move: n1_l.
    have [-> /negbTE//|] := eqVneq i n1.
    by rewrite andbT.
  rewrite inE => i_l.
  apply beta_inva.
    by move: (Hsub _ i_l); rewrite in_setD1; case/andP.
  rewrite !mxE.
  move: i_l.
  have [->|] := eqVneq i n0.
    by rewrite (negbTE n0_l).
  have [->|//] := eqVneq i n1.
  by rewrite (negbTE n1_l).
apply eq_bigr => i _.
rewrite row_setC; last first.
  by move: n0_l'; rewrite in_cons eq_sym; case/norP.
rewrite IH; last 2 first.
  by rewrite in_cons in n1_l'; case/norP: n1_l'.
  by rewrite in_cons in n0_l'; case/norP: n0_l'.
congr (foldr _ _ _ _).
rewrite (row_setC y i); last first.
  by rewrite in_cons in n0_l'; case/norP: n0_l'.
rewrite (row_setC x i) //.
by rewrite in_cons in n1_l'; case/norP: n1_l'.
Qed.

Local Open Scope summary_scope.

Lemma alpha_def m0 n0 (d : 'rV['F_2]_n) : n0 \in 'V m0 ->
  let d0 := d`[n0 := 0%R] in
  let d1 := d`[n0 := 1%R] in
  alpha [seq (beta' n1 m0 (d`[n1 := 0%R]), beta' n1 m0 (d`[n1 := 1%R]))
        | n1 in 'V m0 :\ n0] =
  (alpha' m0 n0 d0, alpha' m0 n0 d1).
Proof.
move=> Hn0.
rewrite /alpha' !recursive_computation /alpha //; first last.
  by apply tanner.
  by apply tanner.
rewrite (eq_bigr (fun t : 'rV_n => ((t ``_ n0) != \delta ('V m0 :\ n0) t)%:R *
  (\prod_(n1 in 'V m0 :\ n0) beta' n1 m0 t))); last first.
  by move=> i _; rewrite (checksubsum_D1 _ Hn0) eq_sym.
rewrite [in X in _ = (_, X)](eq_bigr (fun t : 'rV_n =>
  ((t ``_ n0) != \delta ('V m0 :\ n0) t)%:R *
  (\prod_(n1 in 'V m0 :\ n0) beta' n1 m0 t))); last first.
  move=> i _; by rewrite (checksubsum_D1 _ Hn0) eq_sym.
rewrite !summary_powersetE !summary_foldE /summary_fold /=.
rewrite /image_mem.
set f := 'V m0 :\ n0.
rewrite {2 3 5 6}(set_mem f).
have {}Hn0 : n0 \notin enum f by rewrite mem_enum setD11.
have Hl : {subset enum f <= f} by move=> ?; rewrite mem_enum.
elim: (enum (mem _)) (enum_uniq (mem f)) => [|a l IH] /= Hun in Hn0 Hl *.
  rewrite /checksubsum.
  rewrite !big_pred0 /=; try by move=> i /=; rewrite !inE in_nil.
  by rewrite !mxE !eqxx /= !mulr1.
case/andP: Hun => a_l Hun.
rewrite in_cons in Hn0.
case/norP: Hn0 => Hn0a Hn0.
have Haf: a \in f by apply Hl; rewrite in_cons eqxx.
have Hlf : {subset l <= f}.
  by move=> x Hx; apply Hl; rewrite in_cons Hx orbT.
rewrite {}IH //.
congr pair.
  rewrite (bigD1 (0%R : 'F_2)) => //=.
  rewrite (bigD1 (1%R : 'F_2)) => //=.
  rewrite big_pred0; last by case/F2P.
  congr (_ + _).
    rewrite -[in X in _ * foldr _ _ _ X = _](GRing.add0r 0)%R.
    by apply alpha_def_sub.
  rewrite -[in X in _ * foldr _ _ _ X = _](GRing.addr0 1%R).
  by rewrite alpha_def_sub //= addr0.
rewrite (bigD1 (0%R : 'F_2)) //=.
rewrite (bigD1 (1%R : 'F_2)) //=.
rewrite big_pred0; last by case/F2P.
congr (_ + _).
  rewrite -[in X in _ * foldr _ _ _ X = _](GRing.add0r 1%R).
  by apply alpha_def_sub.
rewrite -[in X in _ * foldr _ _ _ X = _](GRing.addrr_char2 (@char_Fp 2 erefl) 1%R).
by rewrite alpha_def_sub // addr0.
Qed.

Lemma graph_sumprod_up k (t : tn_tree id' k unit unit) :
  graph t =2 graph (sumprod_up t).
Proof.
move=> a b.
move: k t; refine (children_ind _); move=> k t IH.
destruct t as [id0 tag0 ch0 up0 down0]; simpl in *.
case Ha: (id0 == a).
  rewrite -map_comp.
  congr (_ \in _).
  apply eq_in_map=> i Hi.
  by destruct i.
case Hb: (id0 == b).
  rewrite -map_comp.
  congr (_ \in _).
  apply eq_in_map=> i Hi.
  by destruct i.
elim: ch0 => [|c l IHl] in IH * => //=.
rewrite IHl; last first.
  by move=> t' Ht'; apply IH; rewrite in_cons Ht' orbT.
by rewrite IH // in_cons eqxx.
Qed.

Lemma map_apply_seq_eq {A A' B' D : eqType} (f : A -> B' -> A') (g : A -> D)
      (g' : A' -> D) (cl : seq A) (xl : seq B') :
  (forall c x, c \in cl -> g c = g' (f c x)) -> size cl == size xl ->
  map g cl = map g' (apply_seq (map f cl) xl).
Proof.
elim: cl xl => [|c cl IH] [|x xl] //= Heq.
rewrite eqSS => Hlen.
rewrite -Heq; last by rewrite in_cons eqxx.
congr (_ :: _).
apply IH => //.
by move=> c0 x0 Hc0; apply Heq; rewrite in_cons Hc0 orbT.
Qed.

Lemma size_seqs_but1 (l1 l2 : seq R2) : size (seqs_but1 l1 l2) = size l2.
Proof.
elim: l2 => [|x l2 IH] //= in l1 *.
by rewrite IH.
Qed.

Lemma graph_sumprod_down k (t : tn_tree id' k R2 unit) dn :
  graph t =2 graph (sumprod_down t dn).
Proof.
move=> a b.
move: k t dn; refine (children_ind _); move=> k t IH dn.
destruct t as [id0 tag0 ch0 up0 down0]; simpl in *.
destruct (push_init dn); simpl.
case Ha: (id0 == a).
    rewrite -(map_apply_seq_eq (g:=node_id)) //.
    move=> c x Hc.
    by destruct c.
  by rewrite size_seqs_but1 size_map eqxx.
case Hb: (id0 == b).
  rewrite -(map_apply_seq_eq (g:=node_id)) //.
    move=> c x Hc.
    by destruct c.
  by rewrite size_seqs_but1 size_map eqxx.
elim: ch0 => [|c cl IHc] in IH l * => //=.
rewrite -IHc; last first.
  by move=> t' Ht'; apply IH; rewrite in_cons Ht' orbT.
by rewrite -IH // in_cons eqxx.
Qed.

Lemma labels_sumprod_up k (t : tn_tree id' k unit unit) :
  labels (sumprod_up t) = labels t.
Proof.
move: k t; refine (children_ind _); move=> k [id0 tag0 ch0 up0 down0] /= IH.
congr (_ :: _).
rewrite -map_comp.
congr flatten.
apply eq_in_map.
by move=> t0 H0; apply IH.
Qed.

Lemma labels_sumprod_down k (t : tn_tree id' k R2 unit) dn :
  labels (sumprod_down t dn) = labels t.
Proof.
move: k t dn; refine (children_ind _).
move=> k [id0 tag0 ch0 up0 down0] /= IH dn.
destruct (push_init dn); simpl.
f_equal.
rewrite -(map_apply_seq_eq (g:=labels)) //; last first.
  by rewrite size_seqs_but1 size_map.
move=> c cl Hc.
by rewrite IH.
Qed.

Lemma apply_seqs_but1 {I U V : eqType} {k} {D}
  (f : tn_tree I k U V -> seq R2 -> D) g in0 cl :
  uniq (map node_id cl) ->
  apply_seq (map f cl) (seqs_but1 in0 (map g cl)) =
  [seq (f c (in0 ++ [seq g d | d <- cl & node_id d != node_id c])) | c <- cl].
Proof.
rewrite {1}(_ : in0 = in0 ++ map g [::]); last by rewrite cats0.
set inl := [::].
rewrite {1 4}(_ : cl = inl ++ cl) //.
elim: cl inl => [|c cl IH] inl //= Hun.
rewrite /apply_seq /=.
congr (f c _ :: _).
  rewrite -catA -map_cat; congr (_ ++ map _ _).
  rewrite filter_cat /= eqxx /= -filter_cat.
  apply/esym/all_filterP/allP => i.
  rewrite map_cat cat_uniq /= in Hun.
  case/and4P : Hun => _ /norP [] Hinl _ Hcl _.
  have [Hic|//] := eqVneq (node_id i) (node_id c).
  rewrite mem_cat => /orP [] /(map_f node_id).
  - by rewrite Hic (negbTE Hinl).
  - by rewrite Hic (negbTE Hcl).
rewrite (_ : inl ++ (c :: cl) = (inl ++ [:: c]) ++ cl); last by rewrite -catA.
rewrite -IH; last by rewrite -catA.
by rewrite rcons_cat -cats1 map_cat.
Qed.

Lemma node_id_sumprod_down {k} (t : tn_tree id' k R2 unit) dn :
  node_id (sumprod_down t dn) = node_id t.
Proof.
destruct t; simpl.
by destruct (push_init dn).
Qed.

Lemma node_id_sumprod_up {k} (t : tn_tree id' k unit unit) :
  node_id (sumprod_up t) = node_id t.
Proof.
by destruct t.
Qed.

Lemma node_id_build h s {k} (i : ord_of_kind m n' k) :
  node_id (build_tree_rec H rW h s k i) = id_of_kind k i.
Proof.
by destruct h.
Qed.

Lemma node_tag_sumprod_down {k} (t : tn_tree id' k R2 unit) dn :
  node_tag (sumprod_down t dn) = node_tag t.
Proof.
destruct t; simpl.
by destruct (push_init dn).
Qed.

Lemma node_tag_sumprod_up {k} (t : tn_tree id' k unit unit) :
  node_tag (sumprod_up t) = node_tag t.
Proof. by destruct t. Qed.

Lemma node_tag_build h s {k} (i : ord_of_kind m n' k) :
  node_tag (build_tree_rec H rW h s k i) = tag_of_kind rW k i.
Proof. by destruct h. Qed.

Lemma up_sumprod_down dn {k} (t : tn_tree id' k R2 unit) :
  up (sumprod_down t dn) = up t.
Proof.
destruct t; simpl.
by destruct (push_init dn).
Qed.

Lemma alpha_map {A} F (l : seq A) :
  alpha (map F l) = \big[alpha_op/(1,0)]_(i <- l) F i.
Proof. by rewrite /alpha foldrE big_map. Qed.

Lemma beta_map {A} F w (l : seq A) :
  beta w (map F l) = beta_op w (\big[beta_op/(1,1)]_(i <- l) F i).
Proof. by rewrite /beta foldlE /= big_cons big_map. Qed.

Lemma kind_filter {A : eqType} k i (s : {set ord_of_kind m n' (negk k)})
      (F : id' -> A) :
  let a := id_of_kind k i in
  let inj := id_of_kind (negk k) in
  [seq F c | c in finset (tanner_rel H a) :\: inj @: s] =
  [seq F (inj x) | x in finset (tanner_rel H a \o inj) :\: s].
Proof.
move=> a inj.
rewrite /image_mem /enum_mem /id' /id /=.
have -> : Finite.enum ('I_m + 'I_n)%type = sum_enum 'I_m 'I_n.
  by rewrite unlock.
rewrite /sum_enum filter_cat map_cat !filter_map -!map_comp.
transitivity
  [seq ([eta F] \o [eta inj]) i | i <- Finite.enum (ord_of_kind m n' (negk k))
  & [preim [eta inj] of [set x | tanner_rel H a x] :\: [set inj x | x in s]] i].
  have Hp: [preim (id_of_kind k) of
            [set x | tanner_rel H (id_of_kind k i) x] :\: inj @: s] =i pred0.
      move=> x; destruct k; by rewrite /= !inE tanner_relE andbF.
  destruct k; by rewrite (eq_filter Hp) filter_pred0 // cats0.
congr (map _ _).
apply eq_filter => x /=; rewrite !inE.
case/boolP : (x \in s) => /= Hx; first by rewrite imset_f.
case/boolP : (inj x \in _) => // /imsetP [y Hy] /id_of_kind_inj xy.
by rewrite xy Hy in Hx.
Qed.

Variable d : 'rV['F_2]_n.
Definition msg_spec' := msg_spec vb d.

Lemma msg_spec_alpha_beta a b :
  tanner_rel H a b ->
  msg_spec' a b =
  alpha_beta (tag_of_id rW a)
             [seq msg_spec' c a | c in finset (tanner_rel H a) :\ b].
Proof.
destruct a, b; rewrite //= => Hij.
- by rewrite tanner_relE in Hij.
- rewrite -alpha_def; last by rewrite VnextE sym_tanner_rel.
  rewrite -imset_set1 (@kind_filter _ kf).
  set x := [set x | _].
  suff : 'V o = x by move=> ->.
  by apply/setP => i; rewrite inE /= -VnextE.
- rewrite -beta_def -imset_set1 (@kind_filter _ kv) /=.
  congr beta.
  rewrite /image_mem /enum_mem.
  congr map.
  apply eq_filter => x.
  by rewrite !inE /= -VnextE -FnextE.
- by rewrite tanner_relE in Hij.
Qed.

Definition down_msg (s : seq id') (i : id') :=
  match s with
  | [::] => None
  | [:: j & _] => Some (msg_spec' j i)
  end.

Lemma alpha_beta_tag_of_id k (i : ord_of_kind m n' k) :
  alpha_beta (tag_of_kind rW k i) =
  alpha_beta (tag_of_id rW (id_of_kind k i)).
Proof. by destruct k. Qed.

Lemma cycle_in_subtree a b s h k i :
  let t1 := build_tree_rec H rW h (a :: s) k i in
  uniq_path (tanner_rel H) (id_of_kind k i) (a :: s) ->
  tanner_rel H a b ->
  b \in prec_node (a :: s) ++ labels t1 ->
  b = id_of_kind k i.
Proof.
move=> t1 Hun Hgr Hb.
have {}Hb : b \in labels t1.
  rewrite [X in _ \in X ++ _]/= mem_cat in Hb.
  move /orP: Hb => [] Hb //.
  rewrite mem_seq1 in Hb.
  rewrite (eqP Hb) in Hgr.
  rewrite tanner_relE in Hgr; by destruct a.
have [p [Hunp [Hlp _]]] := labels_build_tree_rec Hb Hun.
move/acyclic_equiv/(_ (b :: rcons p a)): tanner_acyclic.
rewrite /ucycle /ucycleb /cycle.
move/andP: Hunp => [Hp Hunp].
rewrite -cat_rcons in Hp Hunp.
rewrite -cat1s catA cat_uniq in Hunp.
move/andP: Hunp => [] -> _.
rewrite cat_path in Hp.
rewrite rcons_path last_rcons /=.
rewrite Hgr.
move/andP: Hp => [] -> _ /=.
destruct p; first by [].
rewrite size_rcons /=.
by move/(_ (eqxx true)).
Qed.

Lemma enum_select_children s k i :
  enum (select_children H s k i) = select_children H s k i.
Proof.
by destruct k; rewrite /= /enum_mem unlock /=; apply eq_filter => j;
  rewrite !inE mem_filter !in_cons mem_ord_enum andbT.
Qed.

Lemma select_children_def k j s i :
  let a := id_of_kind k i in
  let inj := id_of_kind (negk k) in
  uniq_path (tanner_rel H) a  s ->
  prec_node s = Some (inj j) ->
  select_children H s k i = enum ([set x | tanner_rel H a (inj x)] :\ j).
Proof.
move=> a inj Hun Hj.
destruct s as [|b s]; first by [].
move: Hj Hun => /= [] => -> {b}Hun.
rewrite -enum_select_children.
rewrite /enum_mem.
apply eq_filter => x.
rewrite /= !inE /=.
rewrite select_children_spec.
rewrite !in_cons.
rewrite (inj_eq (@id_of_kind_inj _ _ _)).
rewrite (eq_sym (id_of_kind _ x)) id_of_kind_neq /=.
symmetry.
rewrite andbC sym_tanner_rel.
case Hix: (tanner_rel _ _ _) => //=.
by rewrite negb_or (ext_uniq_path tanner_acyclic Hun) // andbT.
Qed.

Lemma uniq_select_children s k i : uniq (select_children H s k i).
Proof. by destruct k; rewrite filter_uniq // ord_enum_uniq. Qed.

Lemma eq_alpha_beta {A : eqType} F {k} (t1 t2 : tag k) (l1 l2 : list A) :
  t1 = t2 -> perm_eq l1 l2 ->
  alpha_beta t1 (map F l1) = alpha_beta t2 (map F l2).
Proof.
move=> Ht ?; rewrite /alpha_beta; case: t1 t2 Ht => [|v] t2 <-.
- rewrite !alpha_map; exact/perm_big.
- rewrite !beta_map; congr beta_op; exact/perm_big.
Qed.

Lemma id_of_kind_select_children x s k i :
  x \in [seq id_of_kind (negk k) j | j <- select_children H s k i] =
  tanner_rel H (id_of_kind k i) x && (x \notin s).
Proof.
case Hx: (x \in _).
move/mapP: Hx => [y Hy] ->.
  rewrite select_children_spec in Hy.
  move/andP: Hy => [] ->.
  by rewrite in_cons /= => /norP [_] ->.
symmetry.
apply/contraFF: Hx => Hex.
apply/mapP.
destruct k; destruct x as [x|x].
- by rewrite tanner_relE in Hex.
- exists x => //; by rewrite select_children_spec Hex.
- exists x => //; by rewrite select_children_spec Hex.
- by rewrite tanner_relE in Hex.
Qed.

Lemma set1F (A : finType) (s : A) : [set x | (x == s) || false] = [set s].
Proof. by apply/setP => x; rewrite !inE orbF. Qed.

Lemma unique_children h s k i :
  uniq [seq node_id (sumprod_up
                        (build_tree_rec H rW h (id_of_kind k i :: s) _ j))
       | j <- select_children H s k i].
Proof.
rewrite map_inj_uniq.
  by rewrite uniq_select_children.
move=> x y /=.
rewrite !node_id_sumprod_up !node_id_build.
by apply id_of_kind_inj.
Qed.

Lemma down_msg_spec s i : down_msg s i = omap (msg_spec' ^~ i) (prec_node s).
Proof. by destruct s. Qed.

Lemma push_init_spec s i :
  push_init (down_msg s i) =
  ((omap (msg_spec' ^~ i) (prec_node s) : seq R2),
   oapp (msg_spec' ^~ i) (1,1) (prec_node s)).
Proof. by destruct s. Qed.

Local Notation build_computed_tree := (build_computed_tree vb d).

Lemma tree_ok h (s : seq id') k (i : ord_of_kind m n' k) :
  let t1 := build_tree_rec H rW h s k i in
  let t2 := sumprod_up t1 in
  let dn := down_msg s (id_of_kind k i) in
  let t := sumprod_down t2 dn in
  (#|id'| - #|s| <= h)%nat ->
  uniq_path (tanner_rel H) (id_of_kind k i) s ->
  t = build_computed_tree h s i.
Proof.
elim: h => [|h IH] in s k i *.
  move=> t1 t2 dn t Ht1.
  have His: id_of_kind k i \in s by apply seq_full.
  by rewrite /uniq_path /= His andbF.
move=> t1 t2 dn t Hh Hun.
have Hh': (#|id'| - #|id_of_kind k i :: s| <= h)%nat.
  move/andP/proj2: Hun => Hun.
  by apply card_uniq_seq_decr.
rewrite /t /dn /=.
have Hspec' x:
  uniq_path (tanner_rel H) (id_of_kind (negk k) x) (id_of_kind k i :: s) ->
  msg_spec' (id_of_kind (negk k) x) (id_of_kind k i) =
  up (sumprod_up (build_tree_rec H rW h [:: id_of_kind k i & s] (negk k) x)).
  move=> Hx.
  rewrite msg_spec_alpha_beta; last first.
    by move/andP/proj1: Hx => /= /andP/proj1.
  rewrite -(up_sumprod_down
              (down_msg [:: id_of_kind k i] (id_of_kind (negk k) x))).
  rewrite IH //=.
  by destruct h; rewrite /= alpha_beta_tag_of_id; f_equal;
     rewrite /image_mem /enum_mem; f_equal;
     apply eq_filter=> y /=; rewrite !inE orbF.
destruct s; simpl.
  (* Root of the tree. *)
  congr {|children := _ ; up := _ |}.
    (* children *)
    rewrite apply_seqs_but1 -!map_comp; last by apply unique_children.
    apply eq_in_map => [j] /= Hj.
    move: (Hj).
    rewrite select_children_spec => /andP [Hpj Hunj].
    rewrite -IH //; last first.
      apply cons_uniq_path => //.
      by rewrite sym_tanner_rel.
    rewrite /down_msg.
    congr sumprod_down.
    congr Some.
    rewrite msg_spec_alpha_beta // alpha_beta_tag_of_id.
    congr alpha_beta.
    rewrite filter_map -map_comp.
    rewrite -imset_set1 kind_filter.
    rewrite -enum_select_children.
    rewrite /image_mem /enum_mem.
    rewrite -filter_predI.
    symmetry.
    apply eq_in_map_seqs.
      apply eq_filter => x.
      rewrite /= !inE /=.
      rewrite !node_id_sumprod_up !node_id_build.
      rewrite (inj_eq (@id_of_kind_inj _ _ _)).
      rewrite select_children_spec.
      by rewrite in_cons (eq_sym (id_of_kind _ x)) id_of_kind_neq in_nil andbT.
    move=> x /= Hx.
    rewrite mem_filter !inE in Hx.
    apply Hspec'.
    apply: cons_uniq_path => //.
      by move/andP/proj1/andP/proj2: Hx; rewrite sym_tanner_rel.
    by rewrite mem_seq1 eq_sym id_of_kind_neq.
  (* up *)
  congr alpha_beta.
  rewrite -!map_comp /=.
  rewrite -/set0 -(imset0 (id_of_kind (negk k))) kind_filter.
  rewrite -enum_select_children.
  rewrite /image_mem /enum_mem.
  symmetry.
  apply eq_in_map_seqs.
    apply eq_filter => x.
    rewrite /= !inE /=.
    rewrite select_children_spec.
    by rewrite in_cons (eq_sym (id_of_kind _ x)) id_of_kind_neq in_nil andbT.
  move=> x /= Hx.
  rewrite mem_filter !inE in Hx.
  apply Hspec'.
  apply: cons_uniq_path => //.
    by move/andP/proj1/andP/proj2: Hx; rewrite sym_tanner_rel.
  by rewrite mem_seq1 eq_sym id_of_kind_neq.
(* Inner node *)
have [o Hs]: exists o, s = id_of_kind (negk k) o.
  move: Hun => /= /andP/proj1 /= /andP/proj1.
  destruct s as [o|o], k.
  by rewrite tanner_relE.
  move=> ?; by exists o.
  move=> ?; by exists o.
  by rewrite tanner_relE.
congr {| children := _; up := _; down := _ |}.
    (* children *)
    rewrite apply_seqs_but1 -!map_comp; last by apply unique_children.
    apply eq_in_map => [j] /= Hj.
    move: (Hj).
    rewrite select_children_spec => /andP [Hpj Hunj].
    rewrite -IH //; last first.
      apply cons_uniq_path => //.
      by rewrite sym_tanner_rel.
    rewrite /down_msg.
    congr sumprod_down.
    congr Some.
    symmetry.
    rewrite msg_spec_alpha_beta // alpha_beta_tag_of_id.
    rewrite -imset_set1 kind_filter.
    rewrite filter_map -map_comp Hs.
    set ups := map (_ \o _ \o _) _.
    (* correctness of messages from children *)
    have ->: ups = [seq msg_spec' (id_of_kind (negk k) x) (id_of_kind k i)
       | x in [set x | (tanner_rel H (id_of_kind k i) \o id_of_kind (negk k))
                         x] :\ j :\ o].
      apply eq_in_map_seqs.
        rewrite -Hs (select_children_def (j:=o) Hun) Hs //.
        rewrite /enum_mem.
        rewrite -filter_predI.
        apply eq_filter => x.
        rewrite /= !inE /=.
        rewrite !node_id_sumprod_up !node_id_build.
        rewrite (inj_eq (@id_of_kind_inj _ _ _)).
        by rewrite !andbA (andbC (x !=j)).
      move=> x /=.
      rewrite mem_filter !inE !node_id_sumprod_up !node_id_build.
      rewrite select_children_spec -Hs => /andP/proj2/andP [Hx1 Hx2].
      rewrite Hspec' //=.
      apply cons_uniq_path => //.
      by rewrite sym_tanner_rel.
    rewrite /image_mem /enum_mem.
    rewrite -(map_cons
              (fun x => msg_spec' (id_of_kind (negk k) x) (id_of_kind k i))).
    apply eq_alpha_beta => //.
    (* equality of indices *)
    apply uniq_perm.
        by rewrite filter_uniq // -enumT enum_uniq.
      rewrite /= filter_uniq //.
        by rewrite mem_filter !inE eqxx.
      by rewrite -enumT enum_uniq.
    move=> x /=.
    rewrite in_cons mem_filter /= mem_enum !inE -enumT mem_enum /=.
    case Hxo: (x == o).
      rewrite (eqP Hxo).
      move: Hunj.
      rewrite !in_cons Hs.
      rewrite (inj_eq (@id_of_kind_inj _ _ _)) (eq_sym j).
      move/norP/proj2/norP/proj1 => -> /=.
      move/andP/proj1: Hun.
      by rewrite /= Hs => /andP/proj1 ->.
    by destruct k; rewrite /= !inE andbT.
  (* up *)
  congr alpha_beta.
  rewrite -!map_comp.
  symmetry.
  rewrite Hs in Hun Hspec' *.
  rewrite set1F -imset_set1 kind_filter.
  rewrite (select_children_def (j:=o) Hun) //.
  rewrite /image_mem.
  apply eq_in_map.
  move=> x /=.
  rewrite mem_filter !inE /= sym_tanner_rel => /andP [] /andP [Hx1 Hx2] _.
  rewrite -/msg_spec' Hspec' //.
  apply: cons_uniq_path => //.
  rewrite !in_cons !negb_or.
  rewrite (ext_uniq_path tanner_acyclic Hun) //.
  rewrite (eq_sym (id_of_kind _ x)) id_of_kind_neq //=.
  by rewrite (inj_eq (@id_of_kind_inj _ _ _)) Hx1.
apply msg_spec_alpha_beta.
rewrite sym_tanner_rel.
by move/andP/proj1: Hun => /= /andP/proj1.
Qed.

Corollary computed_tree_ok : computed_tree_spec vb d.
Proof. by apply tree_ok; rewrite // card0 subn0. Qed.

(* Check that the message from a to b meets its specification.
   The tree is constructed from the matrix by build_tree_rec. *)
Theorem message_ok (a b : id') h (s : seq id') k (i : ord_of_kind m n' k) :
  let t := build_computed_tree h s i in
  (#|id'| - #|s| <= h)%nat ->
  uniq_path (tanner_rel H) (id_of_kind k i) s ->
  tanner_rel H a b ->
  a \in prec_node s ++ labels t ->
  b \in prec_node s ++ labels t ->
  msg a b (prec_node s) t = [:: msg_spec' a b].
Proof.
elim: h => [|h IH] in a b s k i *.
  move=> t Ht.
  have His: id_of_kind k i \in s by apply seq_full.
  by rewrite /uniq_path /= His andbF.
move=> t Hh Hun Hgr Ha Hb.
have Hh': (#|id'| - #|id_of_kind k i :: s| <= h)%nat.
  move/andP/proj2: Hun => Hun.
  by apply card_uniq_seq_decr.
rewrite /t /=.
case Has: (Some a == prec_node s).
  destruct s; first by [].
  rewrite /= (inj_eq (@Some_inj _)) in Has.
  (* Upper node is a. Just have to check that current node is b,
     since we know the down message by hypothesis. *)
  case Hb0: (b == id_of_kind k i).
    rewrite msg_spec_alpha_beta //.
    by rewrite (eqP Has) (eqP Hb0).
  move: Hb0.
  rewrite !(eqP Has) /t in Hun Hb Hgr *.
  rewrite -tree_ok // labels_sumprod_down labels_sumprod_up in Hb.
  rewrite (cycle_in_subtree Hun Hgr Hb).
  by rewrite eqxx.
case Hbs: (Some b == prec_node s).
  (* Upper node is b. Need to check the computation of the up message. *)
  destruct s; first by [].
  simpl in Hbs.
  move/eqP: Hbs => [] Hbs; subst b.
  case Ha0: (a == _).
    rewrite msg_spec_alpha_beta // alpha_beta_tag_of_id.
    move/eqP: Ha0 => Ha0 /=; subst a.
    by rewrite set1F.
  move: Ha0.
  rewrite /t -tree_ok // labels_sumprod_down labels_sumprod_up in Ha.
  rewrite (cycle_in_subtree Hun _ Ha).
    by rewrite eqxx.
  by rewrite sym_tanner_rel.
have Hgr': graph t a b.
  rewrite /t -tree_ok // -graph_sumprod_down -graph_sumprod_up
    labels_sumprod_down labels_sumprod_up in Ha Hb *.
  apply build_tree_rec_ok => //.
    move: Ha.
    rewrite mem_cat => /orP [] //.
    destruct s; first by [].
    rewrite in_cons => /orP [] // Hab.
    by rewrite (eqP Hab) eqxx in Has.
  move: Hb.
  rewrite mem_cat => /orP [] //.
  destruct s; first by [].
  rewrite in_cons => /orP [] // Hab.
  by rewrite (eqP Hab) eqxx in Hbs.
have Hun': uniq (labels t).
  rewrite /t -tree_ok // labels_sumprod_down labels_sumprod_up.
  by apply uniq_labels_build_tree_rec.
have Hsz : size (msg a b (prec_node s) t) = graph t a b.
  destruct s.
    by apply msg_sz.
  rewrite msg_none_eq.
      by apply msg_sz.
    by apply /contraFN: Has => /eqP ->.
  by apply /contraFN: Hbs => /eqP ->.
rewrite {}Hgr' /= {}Has {}Hbs in Hsz.
set fl := flatten _ in Hsz *.
have Hfl: fl = fl by [].
rewrite {1}/fl in Hfl.
destruct fl; first by [].
destruct fl; last by [].
move: {Hsz} (eq_refl r).
rewrite -mem_seq1 -Hfl.
move/flattenP => [l Hl Hrl].
move/mapP: Hl => [c Hc Hmsgc].
subst l.
(* a and b are in subtrees.
   Suffices to prove that there is some correct message. *)
set fl := flatten _ in Hfl *.
suff : msg_spec' a b \in fl.
  rewrite Hfl mem_seq1.
  by move/eqP => ->.
apply/flatten_mapP.
exists c; first by [].
set e := id_of_kind k i in Hun Hh' Hrl *.
move/mapP: Hc => [j Hj] /= Hc.
rewrite -/e in Hc *.
rewrite select_children_spec in Hj.
change (Some e) with (prec_node [:: e & s]).
pose inj := @id_of_kind m n' (negk k).
destruct (@msg_nonnil a b (Some e) _ c) as [Hac Hbc].
  move: Hrl.
  by destruct (msg _ _ _ _).
have Hunj: uniq_path (tanner_rel H) (inj j) (e :: s).
  apply: cons_uniq_path => //.
    move/andP/proj1: Hj.
    by rewrite sym_tanner_rel.
  by move/andP/proj2: Hj.
rewrite Hc -tree_ok // ?labels_sumprod_down ?labels_sumprod_up in Hac Hbc.
rewrite Hc (IH a b [:: e & s] _ j) //.
    by rewrite mem_seq1.
  rewrite -tree_ok //.
  by rewrite labels_sumprod_down labels_sumprod_up.
rewrite -tree_ok //.
by rewrite labels_sumprod_down labels_sumprod_up.
Qed.

Theorem sumprod_ok : sumprod_spec vb d.
Proof.
move=> a b Hgr.
rewrite computed_tree_ok.
apply (@message_ok a b #|id'| [::] kv ord0) => //=.
+ by rewrite card0 subn0 card_sum !card_ord.
+ rewrite -computed_tree_ok labels_sumprod_down labels_sumprod_up.
  by apply build_tree_full.
+ rewrite -computed_tree_ok labels_sumprod_down labels_sumprod_up.
  by apply build_tree_full.
Qed.

Lemma get_esti_cat n0 (l1 l2 : seq (id' * R2)) :
  get_esti n0 (l1 ++ l2) = get_esti n0 l1 ++ get_esti n0 l2.
Proof.
elim: l1 => [|[i p] l] //= IH.
by case: ifP => Hi; rewrite IH.
Qed.

Lemma get_esti_flatten n0 (l : seq (seq (id' * R2))) :
  get_esti n0 (flatten l) = flatten (map (get_esti n0) l).
Proof.
elim: l => [|l0 l] //= IH.
by rewrite get_esti_cat IH.
Qed.

Lemma get_esti_nil n0 k (t : tn_tree' k) :
  inr n0 \notin labels t -> size (get_esti n0 (estimation t)) = 0%N.
Proof.
move: k t; refine (children_ind _) => k [id0 tag0 ch0 up0 down0] /= IH.
rewrite in_cons => /norP [Hid0 Hfl].
suff : size (get_esti n0 (flatten [seq estimation i | i <- ch0])) = 0%N.
  destruct tag0; first by [].
  by rewrite /= (eq_sym id0) (negbTE Hid0).
rewrite get_esti_flatten size_flatten sumnE big_seq/= big1// => i.
rewrite /shape -!map_comp => /mapP[x Hx] -> /=.
apply IH => //.
apply/negP => Hlx.
apply/negP: Hfl.
rewrite negbK.
apply/flattenP; exists (labels x); last by [].
exact: (map_f labels).
Qed.

Let p01 f n0 : R2 := (f (d`[n0 := 0%R]), f (d`[n0 := 1%R])).

Lemma estimation_alpha n0 h (s : seq id') k (i : ord_of_kind m n' k) :
  let t := build_computed_tree h s i in
  (#|id'| - #|s| <= h)%nat ->
  uniq_path (tanner_rel H) (id_of_kind k i) s ->
  inr n0 \in labels t ->
  get_esti n0 (estimation t) =
  [:: normalize (beta (rW n0) [seq (p01 (alpha' m1 n0) n0) | m1 in 'F n0])].
Proof.
elim: h => [|h IH] in s k i *.
  move=> t Ht.
  have His: id_of_kind k i \in s by apply seq_full.
  by rewrite /uniq_path /= His andbF.
move=> t Hh Hun Hn0.
have Hh': (#|id'| - #|id_of_kind k i :: s| <= h)%nat.
  move/andP/proj2: Hun => Hun.
  by apply card_uniq_seq_decr.
case Hid: (node_id t == inr n0).
  (* Found it! *)
  destruct k; rewrite //= Hid /=.
  congr (_ :: _).
    (* check value *)
    congr normalize.
    case/eqP: Hid => Hid; subst n0.
    destruct s as [|s s0].
      (* at tree root *)
      rewrite -/set0 -(imset0 (id_of_kind (negk kv))) kind_filter /=.
      rewrite setD0 Monoid.mulm1.
      congr beta.
      rewrite /image_mem /enum_mem.
      apply eq_in_map_seqs => //.
      have -> : Finite.enum 'I_m = ord_enum m by rewrite unlock.
      by apply eq_filter => x; rewrite /= !inE /= -VnextE -FnextE.
    (* inner node *)
    destruct s; [ | ]; last first.
      by rewrite tanner_relE in Hun.
    rewrite set1F -imset_set1 (kind_filter (k:=kv)).
    rewrite !beta_map -Monoid.mulmA; congr beta_op.
    rewrite big_filter (eq_bigr (fun j => msg_spec' (inl j) (inr i))) //.
    set tmp := alpha_beta _ _.
    rewrite /=.
    rewrite Monoid.mulmC -big_filter/=.
    rewrite /tmp.
    rewrite -msg_spec_alpha_beta; last first.
      rewrite sym_tanner_rel.
      by move/andP/proj1: Hun => /= /andP/proj1.
    rewrite -(big_seq1 beta_op _ (fun j => msg_spec' (inl j) (inr i))).
    rewrite -big_cat.
    apply/perm_big/uniq_perm.
     - rewrite /= filter_uniq.
         by rewrite mem_filter /= !inE /= eqxx.
       by rewrite -enumT enum_uniq.
     - by rewrite enum_uniq.
    move=> j /=.
    rewrite in_cons mem_filter /= mem_enum !inE /= -VnextE.
    case Hjs: (j == s).
      rewrite (eqP Hjs).
      by move/andP/proj1/andP/proj1 : Hun => /=; rewrite -VnextE -FnextE.
    case Hji: (i \in 'V j) => /=.
      by rewrite -enumT mem_enum FnextE Hji.
    by rewrite FnextE Hji.
  (* ensure it is the unique solution *)
  rewrite get_esti_flatten.
  apply/nilP.
  rewrite /nilp size_flatten sumnE big_seq/= big1// => e.
  rewrite /shape -!map_comp => /mapP[x Hx] -> /=.
  apply get_esti_nil.
  have Hunx : uniq_path (tanner_rel H) (inl x) [:: id_of_kind kv i & s].
    rewrite mem_filter in Hx.
    move/andP/proj1/andP: Hx => [Hx Hx'].
    rewrite /=.
    move: Hun.
    rewrite tanner_relE.
    exact: cons_uniq_path.
  rewrite -tree_ok // labels_sumprod_down labels_sumprod_up.
  apply/negP => Hi.
  have Hl := uniq_labels_build_tree_rec tanner_acyclic rW h.+1 Hun.
  rewrite /= in Hl.
  move/andP/proj1: Hl.
  apply/negP.
  rewrite negbK.
  apply/flattenP.
  exists (labels (build_tree_rec H rW h [:: inr i & s] kf x)).
    by apply/map_f/map_f.
  by move/eqP: Hid Hi => [] ->.
(* search children *)
rewrite /= in_cons in Hn0 Hid.
rewrite eq_sym Hid /= -!map_comp in Hn0.
move/flattenP: Hn0 => [l Hl Hn0l].
move/mapP: Hl => [j Hj] /= Hjl. (* n0 is under the child labeled by j *)
subst l.
have Hti: node_id t = id_of_kind k i by [].
have Hget:
  get_esti n0 (estimation t) =
  get_esti n0 (flatten (map (@estimation _ _) (children t))).
  destruct t; simpl.
  destruct node_tag; rewrite //=.
  rewrite /= in Hti.
  by rewrite Hti Hid.
rewrite Hget get_esti_flatten -map_comp.
rewrite select_children_spec in Hj.
have Hunj :
  uniq_path (tanner_rel H) (id_of_kind (negk k) j) (id_of_kind k i :: s).
  move/andP: Hj => [Hij Hun'].
  apply: cons_uniq_path => //.
  by rewrite sym_tanner_rel.
(* get estimation by IH *)
rewrite -(IH [:: id_of_kind k i & s] (negk k) j Hh') //.
rewrite /= -map_comp.
rewrite (flatten_single (x:=j)) => //.
    by rewrite uniq_select_children.
  by rewrite select_children_spec.
(* ensure this is the only answer *)
move=> y Hy Hyj /=.
apply/nilP/eqP.
apply get_esti_nil.
have Huny:
  uniq_path (tanner_rel H) (id_of_kind (negk k) y) (id_of_kind k i :: s).
  rewrite select_children_spec in Hy.
  move/andP: Hy => [Hiy Hun'].
  apply: cons_uniq_path => //.
  by rewrite sym_tanner_rel.
rewrite -tree_ok // labels_sumprod_down labels_sumprod_up.
have Hun':= uniq_labels_build_tree_rec tanner_acyclic rW h.+1 Hun.
move: Hun' => /= /andP/proj2.
rewrite -map_comp => Hun'.
case Hn0: (inr n0 \in _); last by [].
rewrite -select_children_spec in Hj.
rewrite (uniq_flatten_map (x:=y) (y:=j) _ Hun') ?eqxx // in Hyj.
apply/hasP.
rewrite -tree_ok // labels_sumprod_down labels_sumprod_up in Hn0l.
by exists (inr n0).
Qed.

Lemma big_beta_mul (R := Rdefinitions.R) (A : finType) (F1 F2 : A -> R) (l : pred A) :
  \big[beta_op/(1,1)]_(i <- enum l) (F1 i, F2 i) =
  (\prod_(i in l) F1 i , \prod_(i in l) F2 i).
Proof.
rewrite /index_enum big_filter.
elim: (Finite.enum A) => [|a la IH].
  by rewrite !big_nil.
rewrite !big_cons /=.
by case Ha: (a \in l); rewrite IH.
Qed.

(* get_esti returns correct estimations *)
Theorem get_esti_ok : get_esti_spec vb.
Proof.
rewrite /get_esti_spec /esti_spec.
move=> n0.
rewrite computed_tree_ok.
rewrite estimation_alpha //; last 2 first.
  by rewrite card0 subn0 card_sum !card_ord.
  rewrite -computed_tree_ok labels_sumprod_down labels_sumprod_up.
  by apply build_tree_full.
congr (_ :: _).
rewrite -(row_setK (n0 : 'I_n) 0%R d).
rewrite -(row_setK (n0 : 'I_n) 1%R d).
rewrite !estimation_correctness; last 2 first.
  by apply tanner.
  by apply tanner.
rewrite -!(K949_lemma vb tanner d n0).
rewrite /K949 /normalize.
rewrite beta_map big_beta_mul /=.
congr pair.
  rewrite mulrC /alpha' !mxE.
  by rewrite eqxx mulrA.
rewrite mulrC /alpha' !mxE.
by rewrite eqxx mulrA.
Qed.

Lemma subseq_estimation k (t : tn_tree' k) :
  subseq (T:=id') [seq p.1 | p <- estimation t] (labels t).
Proof.
move: k t.
refine (children_ind _) => k t IH.
destruct t as [id0 tag0 ch0 up0 dn0].
rewrite [estimation _]/= [labels _]/=.
rewrite /= in IH.
  destruct tag0.
  eapply subseq_trans; [| apply subseq_cons].
  rewrite map_flatten -map_comp.
  apply: (subseq_flatten (f':=labels)) => x Hx.
  exact: IH.
rewrite /= eqxx.
rewrite map_flatten -map_comp.
apply: (subseq_flatten (f':=labels)) => x Hx.
exact: IH.
Qed.

Lemma get_esti_subseq n0 l :
  subseq (map (pair (inr n0)) (@get_esti m n' n0 l)) l.
Proof.
elim: l => [|[i p] l IH] //.
rewrite [get_esti _ _]/=.
case: ifP => Hi.
  by rewrite /= (eqP Hi) eqxx.
by eapply subseq_trans; [| apply subseq_cons].
Qed.

Theorem estimation_ok : estimation_spec vb.
Proof.
split=> [|n0].
  rewrite /build_tree.
  have Hun0 : uniq_path (tanner_rel H) (id_of_kind kv ord0) [::] by [].
  have := uniq_labels_build_tree_rec tanner_acyclic rW #|id'| Hun0.
  rewrite -labels_sumprod_up -(@labels_sumprod_down kv _ None).
  apply: subseq_uniq.
  exact: subseq_estimation.
have Hn0 := get_esti_ok n0.
set estimations := estimation _ in Hn0 *.
have := get_esti_subseq n0 estimations.
by rewrite Hn0 /= -sub1seq.
Qed.

End AlgoProof.
