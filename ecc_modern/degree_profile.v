Require ProofIrrelevance.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype div bigop ssralg binomial finset fingroup.
From mathcomp Require Import zmodp poly ssrnum matrix tuple finfun path ssrnum.
From mathcomp Require Import binomial perm.
Require Import ssr_ext ssralg_ext ssrR proba.

(** * wip *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section SumCoef.
Variable K : numFieldType.
Variable p : {poly K}.

Definition sum_coef := \sum_(i < size p) p `_ i.

Lemma sum_coef_horner : sum_coef = p.[1].
Proof.
rewrite horner_coef.
apply eq_bigr => i _.
by rewrite expr1n mulr1.
Qed.
End SumCoef.

Module DegreeDistribution.

Section Lambda_definition.

Variable K : numDomainType.

(* type for Lambda and Rho *)
(* Lambda, Rho : distribution of number of nodes by arity (starts at 1) *)
Record Lambda := mkLambda {
  p :> {poly K} ;
  psize : size p != O ;
  p0 : forall i, 0 <= p `_ i }.

End Lambda_definition.

End DegreeDistribution.

Definition degdistp := DegreeDistribution.p.
Coercion degdistp : DegreeDistribution.Lambda >-> poly_of.

Import Num.Theory.

Lemma sum_coef_pos (K : numFieldType) (p : DegreeDistribution.Lambda K) : p.[1] > 0.
Proof.
destruct p.
have p0pos : 0 <= sum_coef p by apply sumr_ge0.
rewrite -sum_coef_horner lt0r /= p0pos andbT.
apply: contra psize => /eqP sum0.
rewrite size_poly_eq0 -lead_coef_eq0 /lead_coef.
case/boolP : ((size p).-1 < size p)%nat => [H|].
  apply/eqP; apply: (@psumr_eq0P K _ xpredT _ _ sum0 (Ordinal H) erefl) => ? _.
  by apply p0.
rewrite -leqNgt => ?.
by rewrite nth_default.
Qed.

Module NormalizedDegreeDistribution.

Section L_definition.

Variable K : numFieldType.

(* type for L and R, lambda and rho *)
Record L := mkL {
  p :> {poly K} ;
  p0 : forall i, 0 <= p `_ i ;
  p1 : p.[1] = 1 }.

End L_definition.

End NormalizedDegreeDistribution.

Definition Lambda_of_L K : NormalizedDegreeDistribution.L K ->
  DegreeDistribution.Lambda K.
case=> p p1 /esym/eqP-p2.
apply: (@DegreeDistribution.mkLambda _ p) => //.
rewrite size_poly_eq0; apply/eqP => p0.
by rewrite p0 horner0 oner_eq0 in p2.
Defined.

Coercion Lambda_of_L :
  NormalizedDegreeDistribution.L >-> DegreeDistribution.Lambda.

Definition nzdegdist_coerce := NormalizedDegreeDistribution.p.
Coercion nzdegdist_coerce : NormalizedDegreeDistribution.L >-> poly_of.

Require Import Reals Rbigop.

Module TreeEnsemble.

Section definition.

Variable K : numFieldType.
(* lambda, rho: distribution of the number of ports by node arities
   (starts at arity 1) *)
Variables lambda rho : NormalizedDegreeDistribution.L K.

Inductive kind := kv | kf.

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

Canonical kind_eqMixin := EqMixin kind_eqP.
Canonical kind_eqType := Eval hnf in EqType _ kind_eqMixin.

Definition negk k := if k is kv then kf else kv.
Lemma negk_involution k : negk (negk k) = k.
by destruct k.
Qed.

Inductive tree : nat -> kind -> Type :=
| Frontier : forall k, tree O k
| Node : forall l k,
    seq (tree l (negk k)) ->                       (* list of children *)
    tree l.+1 k.

Local Open Scope proba_scope.

Definition tree_children l k : tree l.+1 k -> seq (tree l (negk k)).
move Hl1 : _.+1 => l1.
destruct 1 => //.
by case: Hl1 => ->.
Defined.

Lemma tree_frontier k (t : tree O k) : t = Frontier k.
Proof match t with Frontier _ => erefl end.

Lemma tree_children_node l k (s : seq (tree l (negk k))) :
  tree_children (Node s) = s.
Proof. by []. Qed.

Lemma Node_inj l k : injective (@Node l k).
Proof.
move=> s s' H.
by rewrite (_ : s = tree_children (Node s)) // H.
Qed.

Lemma tree_node_inv l k (t : tree l.+1 k) :
  exists (s : seq (tree l (negk k))), t = Node s.
Proof match t with Node l' k' s =>  ex_intro _ _ erefl end.

Lemma tree_node_children l k (t : tree l.+1 k) :
  t = Node (tree_children t).
Proof. by case: (tree_node_inv t) => s ->. Qed.

Section EncodeDecode.

Fixpoint encode_tree l k (t : tree l k) : GenTree.tree unit :=
  match t with
  | Frontier _   => GenTree.Leaf tt
  | Node _ _ s => GenTree.Node 0 (map (@encode_tree _ _) s)
  end.

Fixpoint decode_tree l k (t : GenTree.tree unit) : tree l k :=
  match l with
  | O => Frontier k
  | l'.+1 =>
    match t with
    | GenTree.Leaf _ => Node [::]
    | GenTree.Node _ s => Node (map (@decode_tree l' (negk k)) s)
    end
  end.

Lemma cancel_tree l k : cancel (@encode_tree l k) (@decode_tree l k).
Proof.
elim: l k => [|l IH] k t.
- by rewrite (tree_frontier t).
- rewrite (tree_node_children t) /=.
  f_equal.
  elim: (tree_children t) => [|t' ts' IH'] //=.
  by rewrite IH IH'.
Qed.
End EncodeDecode.

Definition tree_eqMixin l k := CanEqMixin (@cancel_tree l k).
Canonical tree_eqType l k := Eval hnf in EqType _ (@tree_eqMixin l k).
Definition tree_choiceMixin l k := CanChoiceMixin (@cancel_tree l k).
Canonical tree_choiceType l k :=
  Eval hnf in ChoiceType _ (tree_choiceMixin l k).

(* For finite types we need to limit the branching degree *)
Fixpoint max_deg (l : nat) k (t : tree l k) : nat :=
  match t with
  | Frontier _ => O
  | Node l' k' s => foldr maxn (size s) (map (@max_deg _ _) s)
  end.

Record fintree (n l : nat) : Type := mkFintree {
  ft :> tree l.*2 kv ;
  (* ft : seq (tree (2 * l).+1 kf); *)
  _ : (max_deg ft <= n)%nat }.
(* n is the maximum branching degree. Note that the corresponding
   maximum degree of the graph is n+1 (adding the parent edge) *)

Lemma foldr_maxnE m u s : (foldr maxn m s <= u = (m <= u) && (all (fun t => t <= u) s))%nat.
Proof. elim: s => [| ? ? IH] /=; by [rewrite andbT | rewrite geq_max IH andbCA]. Qed.

Section Limit.
Variable n : nat.

Fixpoint limit_get l k (t : tree l k) : tree l k :=
  match t with
  | Frontier k' => Frontier k'
  | Node l' k' s =>
    let s' := map (@limit_get _ _) s in Node (take n s')
  end.

Lemma size_take_leq T {s : seq T} m : (size (take m s) <= m)%nat.
Proof.
rewrite size_take.
case: ifPn => //.
by rewrite -leqNgt.
Qed.

Lemma limit_get_fintree l k (t : tree l k) : (max_deg (limit_get t) <= n)%nat.
Proof.
elim: l k t => [|l IH] k t.
- by rewrite (tree_frontier t).
- rewrite (tree_node_children t) /= foldr_maxnE.
  apply/andP; split.
  + by rewrite size_take_leq.
  + apply/allP => m /mapP [t0 /mem_take/mapP [t2 Ht2 ->{t0} ->{m}]].
    by apply IH.
Qed.

Lemma limit_get_id l (t : tree l.*2 kv) (Ht : (max_deg t <= n)%nat) : limit_get t = t.
Proof.
elim: {l} l.*2 kv t Ht => [|l IH] k t.
- by rewrite (tree_frontier t).
- rewrite (tree_node_children t) foldr_maxnE /=.
  case/andP => Hdeg1 /allP-Hdeg2.
  rewrite -map_take take_oversize //.
  congr Node.
  apply map_id_in => /= t' ?.
  apply/IH/Hdeg2/mapP; by exists t'.
Qed.

End Limit.

Definition fintree_decode n l (t : tree l.*2 kv) : fintree n l :=
  mkFintree (limit_get_fintree n t).

Lemma cancel_fintree n l : @cancel _ _ (@ft n l) (@fintree_decode n l).
Proof.
case=> t Ht.
rewrite /fintree_decode.
move: (limit_get_fintree n t).
rewrite (limit_get_id Ht) => Ht'.
congr mkFintree.
by apply eq_irrelevance.
Qed.

Definition fintree_eqMixin n l := CanEqMixin (@cancel_fintree n l).
Canonical fintree_eqType n l := Eval hnf in EqType _ (@fintree_eqMixin n l).
Definition fintree_choiceMixin n l := CanChoiceMixin (@cancel_fintree n l).
Canonical fintree_choiceType n l := Eval hnf in
      ChoiceType _ (fintree_choiceMixin n l).

Definition tree_countMixin l k := CanCountMixin (@cancel_tree l k).
Canonical tree_countType l k := Eval hnf in CountType _ (tree_countMixin l k).
Definition fintree_countMixin n l := CanCountMixin (@cancel_fintree n l).
Canonical fintree_countType n l := Eval hnf in
      CountType _ (fintree_countMixin n l).

Section count_allpairs.

Variables (A B C : Type) (f : A -> B -> C) (en : seq A) (em : seq B).
Variables (a : pred A) (b : pred B) (c : pred C).
Hypothesis abc : forall x y, (a x && b y) == c (f x y).

Lemma count_map_muln (x : A) : count c [seq f x i | i <- em] = (a x * count b em)%nat.
Proof.
elim: em => [/=|y ? IH]; first by rewrite muln0.
by rewrite /= -(eqP (abc x y)) IH mulnDr mulnb.
Qed.

Lemma count_allpairs : count c (allpairs f en em) = (count a en * count b em)%nat.
Proof. elim: en => [|? ? IH] //=; by rewrite count_cat IH mulnDl count_map_muln. Qed.

End count_allpairs.

Section Finseqs.
Variables (A : eqType) (en : seq A).

(* all the lists of length n made out of elements from "en" *)
Fixpoint nseqs (n : nat) : seq (seq A) :=
  match n with
  | O => [:: [::]]
  | n'.+1 => allpairs (Cons A) en (nseqs n')
  end.

Lemma size_nseqs n s : s \in nseqs n -> size s = n.
Proof.
elim: n s => /= [|n IH] s.
  by rewrite mem_seq1 => /eqP ->.
move/allpairsP => [[x xs]] /= [Hx Hxs] -> /=.
by rewrite IH.
Qed.

(* all the lists of length <= n made out of elements from "en" *)
Definition finseqs (n : nat) : seq (seq A) := flatten (mkseq nseqs n.+1).

Lemma size_finseqs n s : s \in finseqs n -> (size s <= n)%nat.
Proof.
case/flattenP => l /mapP [m].
by rewrite mem_iota leq0n add0n /= => mn -> /size_nseqs ->.
Qed.

End Finseqs.

Section FinseqDeg.
Variables (n l : nat) (k : kind) (en : seq (tree l (negk k))).
Hypothesis en_full : forall x : tree l (negk k),
    count_mem x en = (max_deg x <= n)%nat.

Lemma nseqs_deg m (xs : seq (tree _ _)) :
  count_mem xs (nseqs en m) =
  ((size xs == m) && all (fun x => max_deg x <= n) xs)%nat.
Proof.
elim: m xs => [ [] // | m IH ] xs.
case Hsz: (size _ == _).
  case: xs Hsz  => //= x xs /eqP[xsm].
  rewrite (@count_allpairs _ _ _ _ _ _ (pred1 x) (pred1 xs)) //.
  by rewrite en_full IH mulnb xsm eqxx andTb.
apply/count_memPn.
by apply: contraFN Hsz => /size_nseqs /eqP.
Qed.

Lemma max_deg_all (xs : seq (tree l (negk k))) :
  ((max_deg (Node xs) <= n) =
  (size xs <= n) && all (fun x => (max_deg x <= n)) xs)%nat.
Proof. by rewrite /= foldr_maxnE all_map. Qed.

Lemma finseqs_deg (xs : seq (tree l (negk k))) :
  (count_mem xs (finseqs en n) = (max_deg (Node xs) <= n))%nat.
Proof.
rewrite max_deg_all.
elim: {1 2}n => [ | m IH ].
  by case: xs.
rewrite /finseqs /mkseq -addn1 iota_add map_cat flatten_cat count_cat.
rewrite [in X in (_ + X)%nat = _]/= cats0 IH.
case: leqP => Hm.
  rewrite ltnW //= (_ : count_mem _ _ = O) // ?addn0 //.
  suff /count_memPn -> : xs \notin nseqs en m.+1 by [].
  apply: contraL Hm => /size_nseqs ->.
  by rewrite ltnn.
by rewrite /= add0n leq_eqVlt ltnS leqNgt Hm orbF (nseqs_deg m.+1 xs).
Qed.

End FinseqDeg.

Section TreeEnum.
Variable n : nat.

Fixpoint tree_enum l k : seq (tree l k) :=
  match l with
  | O => [:: Frontier k]
  | l'.+1 =>
    let en := tree_enum l' (negk k) in
    map (@Node _ _) (finseqs en n)
    (* NB: finseqs en n : seq (seq (tree l' (negk k)))) *)
  end.

Lemma tree_enumP l k (x : tree l k) :
  count_mem x (tree_enum l k) = (max_deg x <= n)%nat.
Proof.
elim: l k x => [|l IH] k x.
  by rewrite (tree_frontier x) /= addn0.
rewrite (tree_node_children x).
rewrite -(@finseqs_deg n l k (tree_enum l (negk k))); last by [].
rewrite {IH} /=.
f_equal.
- rewrite eqtype.inj_eq //.
  by apply Node_inj.
- rewrite count_map.
  apply eq_count => s /=.
  rewrite eqtype.inj_eq //.
  by apply Node_inj.
Qed.

Lemma uniq_tree_enum l k : uniq (tree_enum l k).
Proof.
apply count_mem_uniq => t.
case/boolP : (t \in _).
  rewrite -has_pred1 has_count tree_enumP.
  by case: (max_deg _ <= _)%nat.
by apply/count_memPn.
Qed.

Lemma all_max_def_tree_enum l k :
  all (fun x => max_deg x <= n)%nat (tree_enum l k).
Proof.
apply/allP => x Hx.
rewrite leqNgt; apply/negP => Hx'.
move: (tree_enumP x).
rewrite leqNgt // Hx' => /count_memPn.
by rewrite Hx.
Qed.

End TreeEnum.

Definition fintree_enum_dep n l :
  {s : seq (fintree n l) | map (@ft _ _) s = tree_enum n l.*2 kv}.
move: (all_max_def_tree_enum n l.*2 kv).
set ts := tree_enum _ _ _.
elim: ts => [Hx |t ts IH /= /andP [Hx Hts]].
  by exists [::].
move: (IH Hts) => [s Hs].
exists [:: mkFintree Hx & s].
by rewrite -Hs.
Defined.

Definition fintree_enum n l := proj1_sig (@fintree_enum_dep n l).

Lemma fintree_enumP n l : Finite.axiom (@fintree_enum n l).
Proof.
rewrite /fintree_enum.
destruct fintree_enum_dep as [s Hs] => /= t.
have Hun: uniq s.
  move/(congr1 uniq) : Hs.
  by rewrite uniq_tree_enum => /map_uniq.
rewrite count_uniq_mem //.
have /mapP [x Hx1 Hx2]  : ft t \in [seq ft i | i <- s].
  move: (@count_uniq_mem _ [seq ft i | i <- s] t).
  rewrite Hs uniq_tree_enum tree_enumP => /(_ erefl).
  destruct t.
  rewrite i.
  by case: (_ \in _).
by rewrite (can_inj (@cancel_fintree n l) Hx2) Hx1.
Qed.

Definition fintree_finMixin n l := Eval hnf in FinMixin (@fintree_enumP n l).

Canonical fintree_finType n l := Eval hnf in FinType _ (fintree_finMixin n l).

Definition ensemble n l := {dist (@fintree n l)}.

(* maximum branching degree of the graph (root has no parent) *)
Variable tw : nat.
Hypothesis Hlam : (size lambda <= tw)%nat.
Hypothesis Hrho : (size rho <= tw)%nat.

Definition integ (p : {poly K}) := \poly_(i < size p) (p `_ i / (i.+1)%:R).
Definition deriv (p : {poly K}) := \poly_(i < size p) (p `_ i * (i.+1)%:R).
Definition norm  (p : {poly K}) := (p.[1]^-1) *: p.

Lemma size_integ_eq0 (p : {poly K}) :
  (forall i, 0 <= p`_i) -> size (integ p) == O -> size p == O.
Proof.
move=> p0.
rewrite size_poly_eq0 => /eqP Hip.
have : (integ p)`_(size p).-1 == 0 by rewrite Hip coef0.
rewrite /integ coef_poly.
case/boolP : (size p > 0)%nat => [Hp|].
  rewrite prednK // leqnn.
  case/boolP : (p`_(size p).-1 > 0) => [Hp'|].
    move: Hp.
    rewrite -(ltr0n K) => /(divr_gt0 Hp') H1 /eqP H2.
    by rewrite H2 ltrr in H1.
  rewrite ltr_def p0 andbT negbK lead_coef_eq0 => /eqP ->.
  by rewrite size_poly0.
by rewrite lt0n negbK.
Qed.

Definition integ_deg (p : DegreeDistribution.Lambda K) :
  DegreeDistribution.Lambda K.
destruct p.
apply (@DegreeDistribution.mkLambda _ (integ p)).
  apply: contra psize.
  by apply: size_integ_eq0 p0.
move=> i.
rewrite /integ coef_poly.
case: ifP => // ip.
by rewrite divr_ge0 // ler0n.
Defined.

Lemma size_integ p : size (integ_deg p) = size p.
Proof.
destruct p => /=.
rewrite size_poly_eq // prednK ?lt0n // lt0r_neq0 // divr_gt0 //.
  by rewrite lt0r p0 andbT lead_coef_eq0 -size_poly_eq0.
by rewrite ltr0n lt0n.
Qed.

Definition norm_deg (p : DegreeDistribution.Lambda K) :
  NormalizedDegreeDistribution.L K.
apply (@NormalizedDegreeDistribution.mkL _ (norm p)).
  move=> i.
  rewrite /norm coefZ mulr_ge0 //; last by destruct p.
  by rewrite invr_ge0 ltrW // sum_coef_pos.
by rewrite /norm hornerZ mulVf // lt0r_neq0 // sum_coef_pos.
Defined.

Lemma size_norm p : size (norm_deg p) = size p.
Proof. by rewrite size_scale // lt0r_neq0 // invr_gt0 sum_coef_pos. Qed.

Definition norm_integ_deg := norm_deg \o integ_deg.

Let LAM := norm_integ_deg lambda.
Let RHO := norm_integ_deg rho.
Let LR k := if k is kv then LAM else RHO.

Definition tree_dist_children k i (* i = arity - 1 *) (s : seq K) :=
  (LR k) `_ i * \prod_(p <- s) p.

(* NB: edge_dist? *)
Fixpoint tree_dist l k (t : @tree l k) :=
   match t with
   | Node _ k' s =>
     tree_dist_children k (size s) (map (@tree_dist _ _) s)
   | Frontier _ => 1
   end.

(* NB: node_dist? *)
Definition fintree_dist l (t : @fintree tw l) :=
  match ft t with
  | Node _ _ s =>
    if (s != [::]) then
      tree_dist_children kv (size s).-1 (map (@tree_dist _ _) s)
    else 0
  | Frontier _ => 1
  end.

Lemma LR_pos k i : 0 <= (LR k)`_i.
Proof.
rewrite /LR /LAM /RHO.
destruct (norm_integ_deg _), (norm_integ_deg _).
by destruct k.
Qed.

Lemma f0_tree l k (t : @tree l k) : 0 <= tree_dist t.
Proof.
elim: l k t => [|l IH] k t.
  by rewrite (tree_frontier t) /= ler01.
rewrite (tree_node_children t) /= / tree_dist_children.
apply mulr_ge0.
  by apply LR_pos.
rewrite big_map.
by apply prodr_ge0.
Qed.

Lemma f0 l t : 0 <= @fintree_dist l t.
Proof.
move: t => [t p1].
rewrite /fintree_dist /=.
case: l t {p1} => [|l] /=.
  move => t.
  rewrite (tree_frontier t).
  by apply ler01.
move Hs : l.+1.*2 => [ // | [|s]].
  by rewrite doubleS in Hs.
move=> t.
rewrite (tree_node_children t).
case Hch: (tree_children t).
  by apply lerr.
rewrite /tree_dist_children.
apply mulr_ge0.
  by apply LR_pos.
rewrite big_map.
rewrite (big_nth (Node [::])) big_mkord.
apply prodr_ge0 => i.
by rewrite f0_tree.
Qed.

Lemma allpairs_flatten {S T R} (f : S -> T -> R) s t :
  [seq f i j | i <- s, j <- t] = flatten [seq [seq f x y | y <- t] | x <- s].
Proof. elim: s => [|a s IH] //=; by f_equal. Qed.

Lemma f1_tree l k : \sum_(t <- tree_enum tw l k) tree_dist t = 1.
Proof.
elim: l k => [|l IH] k.
  by rewrite /= big_seq1.
rewrite big_map.
transitivity
  (\sum_(ss <- mkseq (nseqs (tree_enum tw l (negk k))) tw.+1)
    \sum_(s <- ss) tree_dist (Node s)).
  by rewrite -big_flatten.
rewrite big_map.
set tw' := tw.+1.
transitivity (\sum_(d < tw') (LR k)`_d); last first.
  have: (size (LR k) < tw')%nat.
    by destruct k; rewrite /LR /norm_integ_deg size_norm size_integ.
  destruct (LR k) => /= Hsz.
  (*rewrite -(@big_morph _ _ RofK 0 Rplus 0%:R (@GRing.add K)) //.*)
  rewrite (@horner_coef_wide _ tw') // in p1.
    rewrite -p1.
    apply eq_bigr => i _.
    by rewrite expr1n mulr1.
  by apply ltnW.
rewrite (@big_mkord _ _ _ tw').
apply eq_bigr => d _.
transitivity (\sum_(s <- nseqs (tree_enum tw l (negk k)) d)
                (LR k)`_d * \prod_(t <- s) tree_dist t).
  rewrite big_seq_cond [in X in _ = X]big_seq_cond.
  apply eq_bigr => s /andP [] /size_nseqs /= -> _.
  by rewrite /tree_dist_children big_map.
rewrite -big_distrr /=.
rewrite -[X in _ = X]mulr1.
f_equal.
elim: (val d) => [|d' IHd] /=.
  by rewrite big_seq1 big_nil.
rewrite (@allpairs_flatten _ _ _ (fun s t => s :: t)) big_flatten big_map /=.
rewrite -[X in _ = X](IH (negk k)).
apply eq_bigr=> t1 _.
rewrite big_map /=.
rewrite -[X in _ = X]mulr1 -[in X in _ = X]IHd.
rewrite big_distrr /=.
apply eq_bigr=> tl _.
by rewrite big_cons.
Qed.

Lemma f1 l : \sum_(t : @fintree tw l) (@fintree_dist l t) = 1.
Proof.
rewrite /index_enum /=.
have ->: Finite.enum (fintree_finType tw l)
    = fintree_enum tw l.
  by rewrite unlock /=.
rewrite /fintree_enum.
destruct (fintree_enum_dep _ _) => /=.
rewrite /fintree_dist.
transitivity (\sum_(t<-map (@ft _ _) x)
      match t with
      | Frontier _ => 1
      | Node l k [::] => 0
      | Node l k ((_ :: _) as s) =>
          tree_dist_children kv (size s).-1 [seq tree_dist i | i <- s]
      end).
  symmetry.
  rewrite big_map.
  apply eq_bigr => i _.
  case (ft i) => // l0 k s.
  by case s.
rewrite {}e {x}.
case: l => [|l].
  by rewrite /= big_seq1.
rewrite doubleS -addn1 /=.
rewrite big_cons add0r big_map big_flatten.
rewrite big_map /=.
rewrite (iota_addl 1 0) big_map.
rewrite /tree_dist_children.
transitivity (\sum_(0 <= d < tw) (LR kv)`_d); last first.
  have: (size (LR kv) <= tw)%nat.
    by rewrite /LR /norm_integ_deg size_norm size_integ.
  destruct (LR kv) => /= Hsz.
  rewrite (@horner_coef_wide _ tw) // in p1.
  rewrite -p1.
  rewrite big_mkord.
  apply eq_bigr => i _.
  by rewrite expr1n mulr1.
rewrite /index_iota subn0.
apply eq_bigr => d _.
rewrite -/(addn l.*2 1).
transitivity (\sum_(s <- nseqs (tree_enum tw (l.*2+1) kf) (1+d))
                (LR kv)`_d * \prod_(t <- s) tree_dist t).
  rewrite big_seq_cond [in X in _ = X]big_seq_cond.
  apply eq_bigr => s /andP [] /size_nseqs.
  case: s => [|a s] // [] Hs _.
  by rewrite big_map /= Hs.
move: (1+d)%nat => d'.
rewrite -big_distrr /=.
rewrite -[X in _ = X]mulr1.
f_equal.
elim: d' => [|d1 IHd] /=.
  by rewrite big_seq1 big_nil.
rewrite (@allpairs_flatten _ _ _ (fun s t => s :: t)) big_flatten big_map /=.
rewrite -[X in _ = X](f1_tree (l.*2+1) kf).
apply eq_bigr=> t1 _.
rewrite big_map /=.
rewrite -[X in _ = X]mulr1 -[in X in _ = X]IHd.
rewrite big_distrr /=.
apply eq_bigr=> tl _.
by rewrite big_cons.
Qed.

Variable RofK : K -> R.
Hypothesis RofKpos : forall x : K, (Num.Def.ler 0%:R x) -> (0 <= RofK x)%R.
Hypothesis RofK0 : RofK 0 = 0%R.
Hypothesis RofK1 : RofK 1 = 1%R.
Hypothesis RofKadd : forall x y : K, RofK (x + y) = (RofK x + RofK y)%R.
Hypothesis RofKmul : forall x y : K, RofK (x * y) = (RofK x * RofK y)%R.

Lemma f0R l t : (0 <= [ffun x => RofK (@fintree_dist l x)] t)%R.
Proof. rewrite ffunE; apply RofKpos, f0. Qed.

Lemma f1R l : (\sum_(t : @fintree tw l) [ffun x => RofK (@fintree_dist l x)] t = 1)%R.
Proof.
evar (h : fintree_finType tw l -> R); rewrite (eq_bigr h); last first.
  move=> i _; rewrite ffunE /h; reflexivity.
by rewrite {}/h -(@big_morph _ _ RofK 0%R Rplus 0%:R (@GRing.add K)) // f1 RofK1.
Qed.

Definition tree_ensemble l : ensemble tw l := makeDist (@f0R l) (@f1R l).

End definition.

End TreeEnsemble.

(*
From mathcomp Require Import perm ssrint.

(* TODO: move *)
Lemma card_permT (T : finType) :
  #| {perm T} | = (#|T|)`!.-1.+1.
Proof.
transitivity (#| perm_on [set: T] |); last first.
  rewrite card_perm prednK.
  by rewrite cardsT.
  by rewrite fact_gt0.
apply eq_card => /= s.
rewrite inE; by apply/sym_eq/subsetP.
Qed.

Module LDPCEnsemble.

Section ldpc_ensemble.

Variables Lambda Rho : DegreeDistribution.Lambda int_numDomainType.
Hypothesis HLambdaRho : (deriv Lambda).[1] = (deriv Rho).[1].
Let vnodes := 'I_(`|Lambda.[1]|).
Let fnodes := 'I_(`|Rho.[1]|).
Let slots := [finType of 'I_(`|(deriv Lambda).[1]|)].
Variable vslots : {ffun vnodes -> {set slots}}.
Hypothesis vslots_inj : injective vslots.
Variable fslots : {ffun fnodes -> {set slots}}.
Hypothesis fslots_inj : injective fslots.
Hypothesis vslots_prop : trivIset [set vslots x | x in [set: vnodes]].
Hypothesis fslots_prop : trivIset [set fslots x | x in [set: fnodes]].

Local Open Scope proba_scope.

Definition t := {dist {perm slots}}.

(* the ensemble of bipartite graphs *)
Definition d : t := Uniform.d (card_permT slots).

End ldpc_ensemble.

End LDPCEnsemble.*)

Section seq.
Variables A B : Type.

Lemma zip_nill (s : seq B) : zip ([::] : seq A) s = [::].
Proof. by destruct s. Qed.

Lemma zip_nilr (l : seq A) : zip l ([::] : seq B) = [::].
Proof. by destruct l. Qed.

CoInductive size_spec : nat -> seq A -> Type :=
  | SizeNil        : size_spec 0    [::]
  | SizeCons x s : size_spec (size s).+1 (x :: s).

Lemma sizeP (s : seq A) : size_spec (size s) s.
Proof. case: s; constructor. Qed.
End seq.

Section tuple.
Variables (n : nat) (T : finType).

Lemma tbeheadE (t : n.-tuple T) x : tbehead (cons_tuple x t) = t.
Proof. by apply val_inj. Qed.

Lemma cons_tuple_inj x : injective (@cons_tuple n T x).
Proof.
move=> [u Hu] [v Hv] /(f_equal (@tval _ _)) [] Heq.
by apply val_inj.
Qed.
End tuple.

Section rel.
Variable T : Type.
Variables r2 r1 r3 : rel T.

Lemma subrel_trans : subrel r1 r2 -> subrel r2 r3 -> subrel r1 r3.
Proof.
move=> Hsub1 Hsub2 a b Hr1.
by apply Hsub2, Hsub1.
Qed.

Lemma subrel_refl : subrel r1 r1.
Proof. by move=> a b. Qed.
End rel.

Section path.
Variable T : eqType.
Variables g g' : rel T.

Lemma eq_path_in (P : pred T) a q :
  {in P &, g =2 g'} -> all P (a :: q) ->
  path g a q = path g' a q.
Proof.
move=> Heq.
elim: q a => [|b q] //= IH a /andP [HPa HPb].
rewrite IH // Heq //.
by move/andP: HPb => [].
Qed.

Variable f : T -> T.
Hypothesis f_morph : forall x y, g x y = g' (f x) (f y).

Lemma cycle_morph l : cycle g l = cycle g' (map f l).
Proof.
case:l => //= *; by rewrite -map_rcons (@map_path _ _ _ _ g pred0) // has_pred0.
Qed.
End path.

Section injectivity.
(* Copied from ldpc_algo_proof. Should share. *)
Lemma inr_inj A B : injective (@inr A B).
Proof. by move=> a b []. Qed.

Lemma inl_inj A B : injective (@inl A B).
Proof. by move=> a b []. Qed.

Lemma imset_inj (A B : finType) (f : A -> B) :
  injective f -> injective (fun s : {set A} => f @: s).
Proof.
move=> Hf x y Hxy.
apply/setP => z.
move/setP/(_ (f z)): Hxy.
case Hy: (z \in y).
  rewrite (mem_imset _ Hy) // => /imsetP [t Ht Htz].
  by rewrite (Hf _ _ Htz).
case Hx: (z \in x) => //.
rewrite mem_imset // => /eqP.
rewrite eq_sym => /eqP/imsetP [t Ht Htz].
by rewrite (Hf _ _ Htz) Ht in Hy.
Qed.
End injectivity.

Section enum_val.
Variables (T : finType) (x : {set T}) (p : pred T).

Lemma enum_val_bij_on :
  x \subset p -> x != set0 -> {on x, bijective (@enum_val _ (mem p))}.
Proof.
move=> /subsetP Hxp.
case: (set_0Vmem x) => [->|[z Hz] _].
  by rewrite eqxx.
by apply (subon_bij Hxp), (enum_val_bij_in (Hxp _ Hz)).
Qed.

Lemma enum_val_full :
  x \subset p -> x = [set @enum_val _ (mem p) z | z in enum_val @^-1: x].
Proof.
move/subsetP => Hxp.
apply/setP=> y.
symmetry.
apply/imsetP.
case: ifPn => Hyx.
  rewrite -(@can2_in_imset_pre _ _ (enum_rank_in (Hxp _ Hyx))).
      esplit.
        by apply mem_imset, Hyx.
      rewrite enum_rankK_in //.
      by apply Hxp.
    move=> z Hz.
    by apply (enum_rankK_in _ (Hxp _ Hz)).
  move=> z Hz.
  by rewrite enum_valK_in.
move=> [z Hz Hzy].
rewrite /preimset inE in Hz.
by rewrite Hzy Hz in Hyx.
Qed.
End enum_val.

Section finset_ops.
Variable T : finType.

Lemma set_nil : [set y : T in [::]] = set0.
Proof. by apply/setP => x; rewrite !inE. Qed.

Lemma set_cons (a : T) s : [set y in a :: s] = a |: [set y in s].
Proof. by apply/setP => y; rewrite !inE. Qed.

Lemma eq_setSU (A B : {set T}) : A \subset B -> A :|: B = B.
Proof.
move=> HA; apply/setP=> y.
rewrite !inE.
case Hy: (y \in A) => //=.
by rewrite (subsetP HA).
Qed.

Lemma cardsCp (A : {set T}) : #|~: A| = (#|T| - #|A|)%nat.
Proof. by rewrite cardsCs setCK. Qed.

Lemma cardEP (s : pred T) : size_spec #|s| (enum s).
Proof. rewrite cardE. apply sizeP. Qed.

Lemma pred_of_setK (A : finType) (s : {set A}) : [set x in s] = s.
Proof. by apply/setP => i; rewrite inE. Qed.

Lemma leq_cards_ord n (s : {set 'I_n}) : (#|s| <= n)%nat.
Proof. by move/subset_leq_card: (subsetT s); rewrite cardsT card_ord. Qed.

Lemma disjoint_I_false p (x x' : {set T}) :
  p \in x -> p \in x' -> [disjoint x & x'] = false.
Proof.
move=> Hpx Hpx'; rewrite disjoints_subset.
apply/subsetP => /(_ p Hpx).
by rewrite inE Hpx'.
Qed.

Lemma set_flatten_cond (P1 P2 : pred T) :
  [set x in [set x | P1 x] | P2 x] = [set x | P1 x & P2 x].
Proof. by apply/setP => x; rewrite !inE. Qed.

Lemma disjointsU1 x (A B : {set T}) :
  [disjoint x |: A & B] = (x \notin B) && [disjoint A & B].
Proof. by rewrite !disjoints_subset subUset sub1set inE. Qed.

Section trivIset.
Variables (x : {set T}) (C : {set {set T}}).

Lemma trivIset_in :
  trivIset C -> x \in C -> trivIset (x |: C).
Proof.
move/trivIsetP => HC Hx.
apply/trivIsetP => y z.
rewrite !in_setU1.
by move/orP => [/eqP -> | ?]; move/orP => [/eqP -> | ?]; apply HC.
Qed.

Lemma trivIset_out :
  trivIset C -> [disjoint x & cover C] -> trivIset (x |: C).
Proof.
move/trivIsetP => HC.
rewrite disjoints_subset => Hx.
apply/trivIsetP => A B HA HB HAB.
rewrite !inE in HA HB.
wlog: A B HAB HA HB / A == x.
  move/orP: (HA) => [] HA' //. by apply.
  move/orP: (HB) => [] HB' //.
    rewrite -setI_eq0 setIC setI_eq0.
    apply => //.
    by rewrite eq_sym.
  by move=> _; apply HC.
move=> /eqP {HA}HA.
move/orP: HB => [/eqP|] HB.
  by rewrite HA HB eqxx in HAB.
rewrite HA disjoints_subset.
apply (subset_trans Hx).
by rewrite subsetC setCK bigcup_sup.
Qed.

Lemma trivIset_disjoint i :
  i \in x -> i \notin cover C -> trivIset (x |: C) -> [disjoint x & cover C].
Proof.
move=> Hpx Hp Hxc.
rewrite disjoints_subset.
apply/subsetP => j Hjx.
rewrite inE.
apply/negP => /bigcupP [y Hy Hiy].
move/trivIsetP/(_ x y): Hxc.
rewrite !inE eqxx Hy /= orbT.
case: eqP => Hxy.
- subst y.
  move/bigcupP: Hp; elim.
  by exists x.
- move/(_ erefl erefl erefl).
  by rewrite (disjoint_I_false Hjx).
Qed.

Lemma trivIset_I1 i :
  trivIset (x |: C) -> i \in x -> i \in cover C -> x \in C.
Proof.
move=> Htriv Hix /bigcupP [y Hy Hiy].
move/trivIsetP/(_ x y): Htriv.
rewrite !inE eqxx Hy orbT /=.
case: eqP => [-> //|] _ /=.
move/(_ erefl erefl erefl).
by rewrite (disjoint_I_false Hix).
Qed.

Lemma trivIset0 : @trivIset T set0.
Proof. by apply/trivIsetP => A B; rewrite inE. Qed.

Lemma trivIset1 : trivIset [set x].
Proof.
apply/trivIsetP => A B.
rewrite !inE => /eqP -> /eqP ->.
by rewrite eqxx.
Qed.

Lemma subset_cover1 : x \subset cover [set x].
Proof.
apply/subsetP => i Hi.
by rewrite /cover big_set1.
Qed.
End trivIset.

Lemma enum_cons (s : {set T}) (x : T) :
  ohead (enum s) = Some x -> enum s = x :: enum (s :\ x).
Proof.
rewrite -!filter_index_enum /index_enum -enumT.
elim: (enum _) (enum_uniq T) => //= y l IH /andP [Hy Hl].
rewrite !topredE.
case: ifP => /= Hif.
  move=> [Heq]; subst y.
  rewrite !inE eqxx /=.
  apply f_equal, eq_in_filter => z Hz.
  rewrite !topredE !inE.
  by case: eqP Hz Hy => // -> ->.
by move=> Ho; rewrite IH //= !inE Hif andbF.
Qed.

Section bigop.
Variables (R : Type) (idx : R) (op : Monoid.com_law idx) .
Variables (A : {set T}) (F : T -> R) (P : pred T).

Lemma big_enum_in_nocond :
  \big[op/idx]_(i <- enum A) F i = \big[op/idx]_(i in A) F i.
Proof. by rewrite big_filter. Qed.

Lemma big_enum_in_cond :
  \big[op/idx]_(i <- enum A | P i) F i = \big[op/idx]_(i in A | P i) F i.
Proof. by rewrite big_filter_cond. Qed.

End bigop.
End finset_ops.

Definition big_enum_in := (big_enum_in_nocond, big_enum_in_cond).

Section imset2.
Variables (aT1 aT2 rT : finType) (f : aT1 -> aT2 -> rT).
Variables (D1 : pred aT1) (D2 : aT1 -> pred aT2).

(* copy proof of curry_imset2l ! *)
Lemma curry_imset2l_dep :
  [set f x y | x in D1, y in D2 x] = \bigcup_(x in D1) f x @: D2 x.
Proof.
apply/setP=> y; apply/imset2P/bigcupP => [[x1 x2 Dx1 Dx2 ->{y}] | [x1 Dx1]].
  by exists x1; rewrite // mem_imset.
by case/imsetP=> x2 Dx2 ->{y}; exists x1 x2.
Qed.
End imset2.

Section poly_ops.
Variable K : ringType.

Lemma sum_poly_weaken (l : {poly K}) s :
  (size l <= s)%nat -> \sum_(0 <= i < s) l`_i = \sum_(i < size l) l`_i.
Proof.
move=> Hl.
rewrite -{1}(subnKC Hl) // {1}/index_iota subn0 iota_add big_cat /=.
rewrite -{1}(subn0 (size l)) big_mkord // -[RHS]addr0; congr (_ + _).
rewrite big_nat_cond big1 // add0n => i /andP[/andP[Hi _] _].
by apply/leq_sizeP : Hi.
Qed.
End poly_ops.

Section sum_ops.
Variables (T : finType) (K : realFieldType).

Lemma le_sum_all (P : pred T) (r : K) F G :
  \sum_(i in P) G i > 0 ->
  (forall i, P i -> G i > 0) ->
  (forall i, P i -> r <= F i / G i) ->
  r <= (\sum_(i in P) F i) / \sum_(i in P) G i.
Proof.
move=> HG HG' Hall.
rewrite ler_pdivl_mulr // big_distrr /=.
apply ler_sum => i Hi.
by rewrite -ler_pdivl_mulr // ?Hall // HG'.
Qed.

Lemma sum_expr_S m l : (\sum_(i < l.+1) m ^ i = 1 + m * \sum_(i < l) m ^ i)%nat.
Proof. by rewrite big_ord_recl big_distrr. Qed.
End sum_ops.

Require Import subgraph_partition tanner.

Module PartialComputationGraph.
Section pcomp_graph_def.
Variable port : finType. (* total number of ports = #|port| (NB: was E) *)
(*
Variable E : nat.
*)

Record hemi_comp_graph := {
  part :> {set {set port}} ; (* known nodes *)
  part_p : trivIset part ; (* known nodes are disjoint *)
  border : {set port} ; (* unused ports in known nodes *) (* try removing!! *)
  ports := \bigcup_(x in part) x;
  border_p : border \subset ports;
}.

Definition graph_dom n := ports n :\: border n.

Record comp_graph := {
  nodes : hemi_comp_graph ;
  conodes : hemi_comp_graph ;
  edges : {ffun port -> port} ;
  edom :=  graph_dom nodes ;
  (* edom := finset (None.-support edges) ; *)
  edom_codom : edges @: edom = graph_dom conodes ;
  edges_inj : {in edom &, injective edges};
  edges_out : {in ~: edom, edges =1 ssrfun.id}
}.

Definition known_coports (c : comp_graph) := ports (conodes c).

Lemma card_border_ports (h : hemi_comp_graph) :
  (#|border h| <= #|ports h|)%nat.
Proof. by apply subset_leq_card, border_p. Qed.

Definition hemi_comp_graph_eqb (h1 h2 : hemi_comp_graph) :=
  (part h1 == part h2) && (border h1 == border h2).

Lemma hemi_comp_graph_eqP : Equality.axiom hemi_comp_graph_eqb.
Proof.
case => p1 pp1 b1 po1 bp1.
case => p2 pp2 b2 po2 bp2.
rewrite /hemi_comp_graph_eqb /=.
case: eqP => Hp /=.
  case: eqP => Hb /=.
    eapply ReflectT.
    destruct Hp.
    destruct Hb.
    subst po1 po2.
    by rewrite (eq_irrelevance bp1 bp2) (eq_irrelevance pp1 pp2).
  apply ReflectF => [] [] _.
  by move/Hb.
apply ReflectF => [] [].
by move/Hp.
Qed.

Definition hemi_comp_graph_eqMixin := EqMixin hemi_comp_graph_eqP.
Canonical hemi_comp_graph_eqType :=
  Eval hnf in EqType _ hemi_comp_graph_eqMixin.

Definition comp_graph_eqb (c1 c2 : comp_graph) :=
 [&& nodes c1 == nodes c2, conodes c1 == conodes c2 & edges c1 == edges c2].

Lemma comp_graph_eqP : Equality.axiom comp_graph_eqb.
Proof.
case => n1 cn1 e1 ed1 ec1 ei1 eo1.
case => n2 cn2 e2 ed2 ec2 ei2 eo2.
rewrite /comp_graph_eqb /=.
case: eqP => Hn /=.
  case: eqP => Hcn /=.
    case: eqP => He /=.
      eapply ReflectT.
      destruct Hn, Hcn, He.
      subst ed1 ed2.
      rewrite (eq_irrelevance ec1 ec2).
      have -> : ei1 = ei2 by apply ProofIrrelevance.proof_irrelevance.
      have -> : eo1 = eo2 by apply ProofIrrelevance.proof_irrelevance.
      by [].
    apply ReflectF => [] [] _ _.
    by move/He.
  apply ReflectF => [] [] _.
  by move/Hcn.
apply ReflectF => [] [].
by move/Hn.
Qed.

Definition comp_graph_eqMixin := EqMixin comp_graph_eqP.
Canonical comp_graph_eqType :=
  Eval hnf in EqType _ comp_graph_eqMixin.

End pcomp_graph_def.

Section border_step.

Variables (port : finType) (c : comp_graph port).
Variables (start_port end_port : port) (end_node : {set port}).

Definition step_trivIset := trivIset (end_node |: conodes c).
Definition step_start_cond :=
  (start_port \in border (nodes c)).
Definition step_end_cond :=
  (end_port \in end_node :\: graph_dom (conodes c)).
Definition step_cond := step_start_cond && step_end_cond.

Lemma step_border n (p : port) : border n :\ p  \subset ports n.
Proof.
eapply subset_trans; [apply subD1set | apply border_p].
Qed.

Definition step_nodes : hemi_comp_graph port :=
  let n := nodes c in
  if step_trivIset && step_cond then
    Build_hemi_comp_graph (part_p n) (step_border n start_port)
  else n.

Lemma step_coborder :
  let cn := conodes c in
  ((border cn :|: if end_node \in cn then set0 else end_node) :\ end_port)
  \subset (\bigcup_(x in end_node |: conodes c) x).
Proof.
rewrite /=.
case: ifP => Hend.
- rewrite setU0.
  apply/subsetP => x.
  rewrite bigcup_setU in_setU.
  rewrite in_setD => /andP [_ Hx].
  by rewrite (subsetP (border_p (conodes c)) _ Hx) orbT.
- apply/subsetP => x.
  rewrite bigcup_setU in_setU.
  rewrite in_setD => /andP [Hx1].
  rewrite in_setU => /orP [] Hx2.
    by rewrite (subsetP (border_p (conodes c)) _ Hx2) orbT.
  apply/orP; left.
  apply/bigcupP; exists end_node; last by [].
  by rewrite in_set eqxx.
Qed.

Definition step_conodes : hemi_comp_graph port :=
  let cn := conodes c in
  if Bool.bool_dec step_trivIset true is left H then
    if step_cond then
      Build_hemi_comp_graph H step_coborder
    else cn
  else cn.

Definition step_edges :=
  if step_trivIset && step_cond then
    finfun [eta (edges c) with start_port |-> end_port]
  else
    edges c.

Let step_edom := graph_dom step_nodes.

Section step_id.
Hypothesis Hid : step_trivIset && step_cond = false.

Lemma step_nodes_id : step_nodes = nodes c.
Proof. by rewrite /step_nodes Hid. Qed.

Lemma step_edom_id : step_edom = edom c.
Proof. by rewrite /step_edom /step_nodes Hid. Qed.

Lemma step_conodes_id : step_conodes = conodes c.
Proof.
rewrite /step_conodes.
destruct Bool.bool_dec => //.
by move: Hid; rewrite e /= => ->.
Qed.

Lemma step_edges_id : step_edges = edges c.
Proof. by rewrite /step_edges Hid. Qed.
End step_id.

Section step_ok.
Hypothesis Htriv : step_trivIset.
Hypothesis Hcond : step_cond.

Lemma step_nodes_ok : part step_nodes = nodes c.
Proof. by rewrite /step_nodes Htriv Hcond. Qed.

Lemma step_border_ok :
  border step_nodes = border (nodes c) :\ start_port.
Proof. by rewrite /step_nodes Htriv Hcond. Qed.

Lemma step_ports_ok : ports step_nodes = ports (nodes c).
Proof. by rewrite /step_nodes Htriv Hcond. Qed.

Lemma step_edom_ok : step_edom = start_port |: edom c.
Proof.
apply/setP => x.
rewrite !inE step_ports_ok /step_nodes Htriv Hcond /= !inE.
case: eqP => // -> /=.
move/andP: Hcond => [Hsc Hec].
by apply (subsetP (border_p (nodes c)) start_port).
Qed.

Lemma step_edom_edom p : p != start_port -> p \in step_edom -> p \in edom c.
Proof. by rewrite step_edom_ok 2!inE => /negbTE ->. Qed.

Lemma step_conodes_ok : part step_conodes = end_node |: conodes c.
Proof.
rewrite /step_conodes.
destruct Bool.bool_dec => //.
by rewrite Hcond /=.
Qed.

Lemma step_coborder_ok :
  border step_conodes =
  (border (conodes c) :|: if end_node \in conodes c then set0 else end_node)
  :\ end_port.
Proof.
rewrite /step_conodes /=.
destruct Bool.bool_dec => //.
by rewrite Hcond /=.
Qed.

Lemma step_coports_ok : ports step_conodes = end_node :|: known_coports c.
Proof.
rewrite /step_conodes.
destruct Bool.bool_dec => //.
by rewrite /ports Hcond /= bigcup_setU big_set1.
Qed.

Lemma step_codom_ok :
  graph_dom step_conodes = end_port |: graph_dom (conodes c).
Proof.
rewrite /step_conodes.
destruct Bool.bool_dec => //.
rewrite Hcond /=.
apply/setP => i.
rewrite !inE /ports /=.
case: eqP => Hi //=.
  move/andP: Hcond => [_].
  rewrite /step_end_cond inE Hi => /andP [_ Hep].
  apply/bigcupP; exists end_node => //.
  by rewrite !inE eqxx.
case: ifP => Hen.
  by rewrite eq_setSU ?sub1set // !inE orbF.
rewrite negb_or -andbA.
apply andb_id2l => Hi'.
case Hien: (i \in end_node) => /=.
  symmetry; apply/negP => Hip.
  by rewrite (trivIset_I1 Htriv Hien) in Hen.
rewrite bigcup_setU inE.
case Hin: (i \in _) => //.
move/bigcupP: Hin Hien => [s].
by rewrite inE => /eqP -> ->.
Qed.

Lemma step_edges_ok x :
  step_edges x = if x == start_port then end_port else edges c x.
Proof. by rewrite /step_edges Htriv Hcond ffunE. Qed.

End step_ok.

Lemma step_edom_codom : step_edges @: step_edom = graph_dom step_conodes.
Proof.
case Hcond: (step_trivIset && step_cond); last first.
  by rewrite step_conodes_id // step_edom_id // step_edges_id // edom_codom.
move/andP: Hcond => [Htriv Hcond].
rewrite step_edom_ok // step_codom_ok //.
apply/setP => x.
apply/imsetP.
case: ifP.
- rewrite 2!inE.
  case Hx: (x == _) => /=.
    rewrite (eqP Hx).
    exists start_port.
      by rewrite !inE eqxx.
    by rewrite step_edges_ok // eqxx.
  rewrite -edom_codom => /imsetP [y Hy Hxy].
  exists y. by rewrite inE Hy orbT.
  rewrite Hxy step_edges_ok //.
  case: ifP => // /eqP Hys.
  move/andP: Hcond Hy => [].
  by rewrite inE /step_start_cond -Hys => ->.
- move=> Hx [y Hy Hxy].
  move/negbT/negP: Hx; elim.
  move: Hy.
  rewrite 2!inE Hxy step_edges_ok // => /orP [/eqP ->| Hy].
    by rewrite eqxx !inE eqxx /=.
  case: ifP => Hys.
    by rewrite !inE eqxx.
  rewrite inE; apply/orP; right.
  by rewrite -edom_codom mem_imset.
Qed.

Lemma step_edges_inj : {in step_edom &, injective step_edges}.
Proof.
rewrite /step_edges.
case: ifP => [/andP [Htriv Hcond]|Hcond] x y Hx Hy.
+ rewrite !ffunE /=.
  case: ifPn => Hxs.
    rewrite (eqP Hxs).
    case: ifPn => Hys.
      by rewrite (eqP Hys).
    move=> Hey.
    have Hy': y \in edom c by apply step_edom_edom.
    move/andP: Hcond => [_].
    by rewrite /step_end_cond in_setD -edom_codom Hey mem_imset.
  case: ifPn => Hys.
    move=> Hex.
    have Hx': x \in edom c by apply step_edom_edom.
    move/andP: Hcond => [_].
    by rewrite /step_end_cond in_setD -edom_codom -Hex mem_imset.
  by move=> Heq; apply (@edges_inj _ c x y); auto using step_edom_edom.
rewrite /step_edom /step_nodes Hcond in Hx Hy.
by move=> Heq; apply (@edges_inj _ c x y).
Qed.

Lemma step_edges_out : {in ~: step_edom, step_edges =1 ssrfun.id}.
Proof.
move=> p Hp.
rewrite /step_edges.
case: ifP => Hif.
  move /andP: Hif => [Htriv Hcond].
  move/andP: (Hcond) => [Hsc Hec].
  rewrite !ffunE /=.
  move: Hp.
  rewrite step_edom_ok //.
  rewrite 3!inE.
  case: ifP => _ //= Hp'.
  by rewrite edges_out // inE.
rewrite step_edom_id // in Hp.
by rewrite edges_out.
Qed.

Definition step :=
  Build_comp_graph step_edom_codom step_edges_inj step_edges_out.

End border_step.

Section switch_step.

Variables (port : finType) (c : comp_graph port).

Let switch_edom := graph_dom (conodes c).

Definition switch_edges :=
  [ffun x => if x \in switch_edom then
               if [pick ant | (edges c ant == x) && (ant \in edom c)]
               is Some ant then ant else x (* shouldn't happen *)
             else x].

Lemma switch_edges_cancel : {in edom c, cancel (edges c) switch_edges}.
Proof.
move=> x Hx.
rewrite /switch_edges ffunE.
rewrite /switch_edom -(edom_codom c).
rewrite mem_imset //.
case: pickP.
  move=> y /andP [/eqP Hyx Hyc].
  by rewrite (edges_inj Hyc Hx Hyx).
move/(_ x).
by rewrite eqxx Hx.
Qed.

Lemma switch_edom_codom : switch_edges @: switch_edom = edom c.
Proof.
apply/setP => x.
rewrite /switch_edom -edom_codom.
apply/imsetP.
case: ifP => Hx.
- exists (edges c x).
    by rewrite mem_imset.
  by rewrite switch_edges_cancel.
- move => [y Hy Hxy].
  move/imsetP: Hy => [x' Hx' Hyx'].
  rewrite Hyx' switch_edges_cancel // in Hxy.
  by rewrite Hxy Hx' in Hx.
Qed.

Lemma switch_edges_inj : {in switch_edom &, injective switch_edges}.
Proof.
rewrite /switch_edom -(edom_codom c).
move=> x y.
move/imsetP => [x0 Hx0 ->].
move/imsetP => [y0 Hy0 ->].
by rewrite !switch_edges_cancel // => ->.
Qed.

Lemma switch_edges_out : {in ~: switch_edom, switch_edges =1 ssrfun.id}.
Proof.
rewrite /switch_edges => x Hx.
rewrite ffunE.
case: ifP => // Hx'.
by rewrite inE Hx' in Hx.
Qed.

Definition switch :=
  Build_comp_graph switch_edom_codom switch_edges_inj switch_edges_out.

Lemma switch_edges_cancel2 : {in switch_edom, cancel switch_edges (edges c)}.
Proof.
move=> x Hx.
have Hxc: switch_edges x \in edom c by rewrite -switch_edom_codom mem_imset.
apply switch_edges_inj => //.
  by rewrite /switch_edom -edom_codom mem_imset //.
by rewrite switch_edges_cancel.
Qed.

End switch_step.

Section graph_rel.

Variables (port : finType) (c : comp_graph port).

Definition graph_node := Datatypes.sum port port.

Definition known_port (p : graph_node) :=
  match p with
  | inl x => x \in ports (nodes c)
  | inr y => y \in known_coports c
  end.

(* New port-based definition of graph.
   Two kinds of transitions:
   - either move between two ports of different hemi_comp_graphs,
   - or move between two different ports inside the same node
   The boolean force them to alternate. *)
Definition graph_rel : rel (graph_node * bool) :=
  fun x y =>
    match x, y with
    | (inl x, true), (inr y, false) => (x \in edom c) && (edges c x == y)
    | (inr y, false), (inr y', true) =>
      [exists s, [&& s \in conodes c, y \in s, y' \in s & y != y']]
    | (inr y, true), (inl x, false) => (x \in edom c) && (edges c x == y)
    | (inl x, false), (inl x', true) =>
      [exists s, [&& s \in nodes c, x \in s, x' \in s & x != x']]
    | _, _ => false
    end.

Definition tree_like :=
  [forall n : 'I_(#|port|*4),
      [forall p : n.+1.-tuple _, ~~ ucycleb graph_rel p]].

Definition connected_ports x y :=
  exists p b1 b2, path graph_rel (x,b1) p && (last (x,b1) p == (y, b2)).

Definition partial_connected :=
  forall x y, known_port x -> known_port y -> connected_ports x y.

Lemma graph_rel_known_port x y :
  graph_rel x y ->
  (known_port x.1 /\ known_port y.1) /\ (x.1 != y.1 /\ y.2 = negb x.2).
Proof.
case: x y => [[x|x][|]] [[y|y][|]] //=.
- move/andP => [Hdom Hed].
  move: (Hdom).
  rewrite inE => /andP [_] ->.
  move/setP/(_ y): (edom_codom c).
  rewrite -(eqP Hed) mem_imset // inE.
  by move/esym/andP => [_] ->.
- move/existsP => [s] /and4P[Hsg Hos Ho0s Hoo0].
  by split; split => //; apply/bigcupP; exists s.
- move/andP => [Hdom Hed].
  move: (Hdom).
  rewrite inE => /andP [_] ->.
  move/setP/(_ x): (edom_codom c).
  rewrite -(eqP Hed) mem_imset // inE.
  by move/esym/andP => [_] ->.
- move/existsP => [s] /and4P[Hsg Hos Ho0s Hoo0].
  by split; split => //; apply/bigcupP; exists s.
Qed.

(*
Definition rel_nodes (x y : {set 'I_E}) :=
  (x \in nodes c) && (y \in conodes c) && [exists p in x, (p \in edom c) && (edges c p \in y)].

Definition graph_node := Datatypes.sum {set 'I_E}  {set 'I_E}.

Definition graph_rel : rel graph_node :=
  fun x y =>
    match x, y with
    | inl x, inr y => rel_nodes x y
    | inr x, inl y => rel_nodes y x
    | _, _ => false
    end.

Definition tree_like :=
  [forall n : 'I_(expn 2 E).*2,
      [forall p : n.+3.-tuple graph_node, ~~ ucycleb graph_rel p]].

Lemma tree_acyclic : reflect (acyclic graph_rel) tree_like.
Proof.
rewrite /acyclic.
case Ht: tree_like; constructor.
+ move=> l Hl /andP [Hp Hu].
  have Hlen: (size l - 3 < (expn 2 E).*2)%nat.
    have Hfull: {subset l <= enum [set: graph_node]}.
      move=> x Hx.
      by rewrite mem_enum in_setT.
    move: (uniq_leq_size Hu Hfull).
    rewrite -cardE cardsT card_sum.
    rewrite -cardsT -powersetT.
    rewrite card_powerset cardsT card_ord.
    rewrite addnn => Hl'.
    apply ltnW, ltnW.
    by rewrite -addn3 subnK.
  move: Ht.
  rewrite /tree_like.
  move/forallP/(_ (Ordinal Hlen)).
  have Hsz: size l == (size l - 3).+3.
    by rewrite -addn3 subnK //.
  move/forallP/(_ (Tuple Hsz)).
  by rewrite /ucycleb Hp Hu.
+ move/negbT: Ht.
  rewrite negb_forall.
  move/existsP => [n].
  rewrite negb_forall.
  move/existsP => [l].
  rewrite negbK => Ht.
  apply; last by apply Ht.
  by rewrite size_tuple.
Qed.
*)

Definition flip (p : (graph_node * bool)) := (p.1, negb p.2).

Lemma flip_graph_rel x y : graph_rel x y -> graph_rel (flip y) (flip x).
Proof.
case: x y => [[x|x][|]] [[y|y][|]] //=.
- move/existsP => [s /and4P[Ha Hb Hc Hd]].
  apply/existsP; exists s.
  by rewrite Ha Hb Hc eq_sym.
- move/existsP => [s /and4P[Ha Hb Hc Hd]].
  apply/existsP; exists s.
  by rewrite Ha Hb Hc eq_sym.
Qed.

Lemma flip_seq_path x p :
  path graph_rel x p ->
  path graph_rel (last (flip x) (map flip p)) (map flip (rev (belast x p))).
Proof.
elim: p x => // a l IH [x b] /andP [Hp1 Hp2].
rewrite rev_cons map_rcons rcons_path {7}/flip /= IH //=.
destruct l as [|[a' b'] l].
  simpl map.
  destruct a; simpl last.
  by rewrite -/(flip (x, b)) flip_graph_rel.
rewrite rev_cons map_rcons last_rcons.
by rewrite -/(flip (x, b)) flip_graph_rel.
Qed.

End graph_rel.

Section partial_graph_progress.
Variables (port : finType) (c : comp_graph port).

Lemma switchK_edges : switch_edges (switch c) = edges c.
Proof.
apply/ffunP => p.
rewrite /switch_edges /switch ffunE /=.
case: ifP => Hp.
  case: pickP => /=.
    move=> x.
    rewrite /edom /=.
    rewrite -edom_codom => /andP [/eqP Hx] /imsetP [y Hy Hxy].
    rewrite Hxy switch_edges_cancel // in Hx.
    by rewrite -Hx.
  move/(_ (edges c p)).
  rewrite switch_edges_cancel // eqxx /=.
  by rewrite /edom -edom_codom mem_imset.
by rewrite edges_out // inE Hp.
Qed.

Lemma switchK : switch (switch c) = c.
Proof.
apply/comp_graph_eqP.
by rewrite /comp_graph_eqb /= switchK_edges !eqxx.
Qed.

Lemma conodes_switch_nodes :
  conodes (switch c) = nodes c.
Proof. by case: c. Qed.

Definition switch_graph_node (g : graph_node port) : graph_node port :=
  match g with
  | inl x => inr x
  | inr y => inl y
  end.

Definition switch_path_node (g : graph_node port * bool) :=
  (switch_graph_node g.1, g.2).

Lemma inj_switch_path_node : injective switch_path_node.
Proof. by move=> [[]x1 x2] [[]y1 y2] //= [] -> ->. Qed.

Lemma graph_rel_switch x y :
  (y \in graph_dom (conodes c)) && (switch_edges c y == x)
  = (x \in edom c) && (edges c x == y).
Proof.
case Hx: (x \in _) => /=.
  case Hxy: (edges c x == y).
    rewrite -(eqP Hxy) switch_edges_cancel // eqxx andbT.
    by rewrite -edom_codom mem_imset.
  case Hy: (y \in _) => //=.
  case Hyx: (_ == _) => //.
  by rewrite -(eqP Hyx) switch_edges_cancel2 // eqxx in Hxy.
case Hy: (y \in _) => //=.
case Hyx: (_ == _) => //.
rewrite -switch_edom_codom -(eqP Hyx) in Hx.
by rewrite mem_imset in Hx.
Qed.

Lemma switch_graph_rel x y :
  graph_rel (switch c) (switch_path_node x) (switch_path_node y) =
  graph_rel c x y.
Proof.
rewrite /graph_rel /switch /switch_path_node /switch_graph_node.
destruct x, y, g, g0, b, b0 => //=; by rewrite graph_rel_switch.
Qed.

Lemma switch_graph_nodeK : involutive switch_graph_node.
Proof. by move => []. Qed.

Lemma connected_switch : partial_connected c -> partial_connected (switch c).
Proof.
move=> Hc x y Hx Hy.
case: (Hc (switch_graph_node x) (switch_graph_node y)).
- by destruct x.
- by destruct y.
- move => p [b1 [b2 /andP [Hp Hl]]].
  exists (map switch_path_node p), b1, b2.
  rewrite -(switch_graph_nodeK x).
  rewrite -/(switch_path_node (switch_graph_node x, b1)).
  rewrite (@map_path _ _ _ _ (graph_rel c) pred0); first last.
      by rewrite has_pred0.
    move=> a b _.
    by rewrite switch_graph_rel.
  rewrite Hp /=.
  rewrite last_map (eqP Hl).
  by rewrite /switch_path_node switch_graph_nodeK.
Qed.

Section connected_step.
Variables (sp ep : port) (en : {set port}).
Let c' := (step c sp ep en).

Lemma monotonic_edom_step : edom c \subset edom c'.
Proof.
case Hcond: (step_trivIset c en && step_cond c sp ep en).
  move/andP: Hcond => [Htriv Hcond].
  rewrite /edom step_edom_ok //.
  by apply/subsetP => x Hx; rewrite inE Hx orbT.
by rewrite /edom step_edom_id.
Qed.

Lemma monotonic_edges_step x : x \in edom c -> edges c' x = edges c x.
Proof.
move=> Hx.
case Hcond: (step_trivIset c en && step_cond c sp ep en).
  move/andP: Hcond => [Htriv Hcond].
  rewrite step_edges_ok //.
  case: ifP => // Hxsp.
  move/andP: Hcond => [].
  rewrite /step_start_cond => Hsp.
  by rewrite /edom /graph_dom inE (eqP Hxsp) Hsp in Hx.
by rewrite /= step_edges_id.
Qed.

Lemma monotonic_step_rel : subrel (graph_rel c) (graph_rel c').
Proof.
rewrite /graph_rel => x y.
destruct x,y.
destruct g, g0, b, b0 => //.
- move/existsP => [s1] /and4P[Hs Hos Ho0s Hoo0].
  apply/existsP; exists s1; rewrite Hos Ho0s Hoo0 /= /step_nodes.
  by case: ifP; rewrite Hs.
- move/andP => [Hod Heo].
  rewrite (subsetP monotonic_edom_step _ Hod).
  by rewrite monotonic_edges_step.
- move/andP => [Hod Heo].
  rewrite (subsetP monotonic_edom_step _ Hod).
  by rewrite monotonic_edges_step.
- move/existsP => [s1] /and4P[Hs Hos Ho0s Hoo0].
  apply/existsP; exists s1; rewrite Hos Ho0s Hoo0 /= /step_conodes.
  case: Bool.bool_dec => Htriv.
    case: ifP => Hcond /=.
      by rewrite inE Hs orbT.
    by rewrite Hs.
  by rewrite Hs.
Qed.

Lemma tree_like_rev_subrel (c1 c2 : comp_graph port) :
  subrel (graph_rel c1) (graph_rel c2) -> tree_like c2 -> tree_like c1.
Proof.
move=> Hsub /'forall_forallP /= Htl.
apply/'forall_forallP => /= n p.
apply: contra (Htl n p).
rewrite /ucycleb 2!(cycle_path (thead p)).
by case/andP => /(sub_path Hsub) ->.
Qed.

Lemma tree_like_rev_step : tree_like c' -> tree_like c.
Proof.
apply tree_like_rev_subrel.
apply monotonic_step_rel.
Qed.

Lemma graph_rel_irrel :
  nodes c' = nodes c /\ conodes c' = conodes c /\ edges c' = edges c ->
  graph_rel c' =2 graph_rel c.
Proof.
move=> [Hn [Hcn He]] x y.
by rewrite /graph_rel /edom Hn Hcn He.
Qed.

Lemma known_port_step x :
  step_trivIset c en -> step_cond c sp ep en ->
  known_port c' x = (x \in [set inr p | p in en]) || known_port c x.
Proof.
move=> Htriv Hcond.
rewrite {1}/known_port /= step_ports_ok // /known_coports step_coports_ok //.
move: Htriv Hcond.
rewrite /step_cond /step_start_cond /step_end_cond => Htriv /andP [Hsp Hep].
destruct x as [x|y] => /=.
  by case: imsetP => // [] [].
rewrite inE.
case: imsetP.
  move=> [y' Hy' Hyy'].
  by rewrite (inr_inj Hyy') Hy'.
case Hyen: (y \in en) => //.
move/imsetP.
by rewrite mem_imset.
Qed.

Section connected_step_out.
Hypothesis (Hc : partial_connected c)
           (Htriv : step_trivIset c en)
           (Hcond : step_cond c sp ep en).

Lemma sp_in_step_edom : sp \in edom c'.
Proof. by rewrite /edom step_edom_ok // !inE eqxx. Qed.

Lemma step_edges_sp_ep : (step_edges c sp ep en) sp = ep.
Proof. by rewrite step_edges_ok // eqxx. Qed.

Lemma en_in_step_conodes : en \in step_conodes c sp ep en.
Proof. by rewrite step_conodes_ok // !inE eqxx. Qed.

Lemma ep_in_en : ep \in en.
Proof.
move/andP: Hcond => [_].
by rewrite /step_end_cond !inE => /andP [_] ->.
Qed.

Lemma connected_step_ep x :
  known_port c' x -> known_port c x ->
  exists p b1,
    path (graph_rel c') (x, b1) p && (last (x, b1) p == (inr ep, false)).
Proof.
move=> Hx Hx'.
move/andP: (Hcond) => [Hsp _].
case: (@Hc x (inl sp)) => //.
  by apply (subsetP (border_p _)).
move=> p [b1 [b2 /andP [Hp Hl]]].
destruct b2.
  exists (rcons p (inr ep, false)); exists b1.
  rewrite rcons_path last_rcons (eqP Hl) eqxx.
  rewrite /= step_edges_sp_ep eqxx sp_in_step_edom !andbT.
  by apply (sub_path monotonic_step_rel).
case: (lastP p) Hp Hl => /=.
  move=> _ /eqP [] -> _.
  exists [:: (inr ep, false)]; exists true.
  by rewrite eqxx /= sp_in_step_edom step_edges_sp_ep eqxx.
move=> {p}p x' Hp Hl.
rewrite last_rcons in Hl.
elimtype False; move: Hp.
rewrite (eqP Hl) rcons_path /graph_rel => /andP [_] /=.
case: (last (x,b1) p) => [] [|] a b.
  by destruct b.
case: b => //.
rewrite /step_start_cond in Hsp.
by rewrite inE Hsp.
Qed.

Lemma connected_step_out x y :
  known_port c' x -> known_port c' y ->
  known_port c x -> known_port c y = false ->
  connected_ports c' x y.
Proof.
move=> Hx Hy Hx' Hy'.
move: (connected_step_ep Hx Hx') => [p [b1 Hep]].
move: Hy; rewrite known_port_step // Hy' orbF => /imsetP [y' Hy'en Hyy'].
case Hyep: (y == inr ep).
  rewrite (eqP Hyep).
  by exists p; exists b1; exists false.
case Hen: (en \in conodes c).
  move: Hy'.
  rewrite Hyy' /= /ports => /bigcupP.
  by elim; exists en.
exists (rcons p (y,true)); exists b1; exists true.
rewrite rcons_path last_rcons eqxx.
move/andP: Hep => [] -> /eqP -> /=.
rewrite Hyy' andbT.
apply/existsP; exists en.
case: eqP => Hepy' /=.
  by rewrite Hepy' Hyy' eqxx in Hyep.
by rewrite Hy'en en_in_step_conodes ep_in_en.
Qed.
End connected_step_out.

Theorem connected_step : partial_connected c -> partial_connected c'.
Proof.
move => Hc x y Hx Hy.
case Hcond: (step_trivIset c en && step_cond c sp ep en); last first.
  rewrite /known_port /known_coports /= step_nodes_id // step_conodes_id // in Hx Hy.
  case: (@Hc x y) => // p [b1 [b2 Hp]].
  exists p, b1, b2.
  rewrite (eq_path (graph_rel_irrel _)) //.
  by rewrite /= step_nodes_id // step_conodes_id // step_edges_id.
move/andP: Hcond => [Htriv Hcond].
case Hx': (known_port c x).
  case Hy': (known_port c y).
    case: (@Hc x y) => // p [b1 [b2 /andP [Hp Hl]]].
    exists p; exists b1; exists b2.
    rewrite Hl andbT.
    by apply (sub_path monotonic_step_rel).
  by apply connected_step_out.
(* opposite direction *)
case Hy': (known_port c y).
  destruct(connected_step_out Hc Htriv Hcond Hy Hx Hy' Hx') as [p [b1 [b2 Hp]]].
  exists (map (@flip port) (rev (belast (y,b1) p))); exists (~~b2), (~~b1).
  move/andP: Hp => [Hp Hl].
  apply/andP; split.
    rewrite (_ : (x,~~b2) = last (flip (y,b1)) (map (@flip port) p)).
      by apply flip_seq_path.
    by rewrite last_map (eqP Hl).
  rewrite -/(flip (x,b2)) last_map.
  destruct p => /=.
    by rewrite -(eqP Hl).
  by rewrite rev_cons last_rcons.
case Hxy: (x == y).
  exists [::], true, true.
  by rewrite (eqP Hxy) eqxx.
exists [:: (y,true)], false, true.
move: Hx Hy Hxy; rewrite known_port_step // known_port_step //.
rewrite Hx' Hy' !orbF.
move/imsetP=> [x' Hxen] ->.
move/imsetP=> [y' Hyen] -> /= Hxy'.
rewrite eqxx !andbT.
apply/existsP; exists en.
rewrite Hxen Hyen en_in_step_conodes //=.
by move/negbT: Hxy'; apply/contra => /eqP ->.
Qed.
End connected_step.

Theorem tree_like_switch_imp : tree_like c -> tree_like (switch c).
Proof.
move/'forall_forallP => Hc.
apply/'forall_forallP => /= n p.
move/(_ n (map_tuple switch_path_node p)) : Hc.
apply: contra.
rewrite /ucycleb /ucycle -(@cycle_morph _ (graph_rel (switch c))).
  rewrite map_inj_in_uniq //.
  move=> ? ? _ _; exact: inj_switch_path_node.
move=> [x a] [y b].
by rewrite -switch_graph_rel /switch_path_node !switch_graph_nodeK.
Qed.

End partial_graph_progress.

Corollary tree_like_switch port (c : comp_graph port) :
  tree_like (switch c) = tree_like c.
Proof.
case Htl: (tree_like c).
  by apply tree_like_switch_imp.
rewrite -(switchK c) in Htl.
apply/contraFF: Htl.
by apply tree_like_switch_imp.
Qed.

(* NB: a notation for the set of nodes of a given arity *)
Definition ksets (A : finType) k := [set x : {set A} | #|x| == k].
Definition ksetsP (A : finType) k (P : pred {set A}) :=
  [set x : {set A} | (#|x| == k) && P x ].
Notation "[ 'node' x '$' k | P ]" := (ksetsP k (fun x => P%B))
  (at level 2, x at level 99, format "[ 'node'  x  '$'  k  |  P ]") : set_scope.

Section prob_tree_like_neighbor.

Variable port : finType.

Import Num.Theory.
Variable (K : realFieldType).

(* Appendix A of
The Capacity of Low-Density Parity-Check Codes Under Message-Passing Decoding
Thomas J. Richardson and Rudiger L. Urbanke *)
(*
just for reference:
- the result of appendix A from the paper above is cited without proof in
Fundamentals of Codes, Graphs, and Iterative Decoding
Stephen B. Wicker, Saejoon Kim,
Kluwer Academic Publishers
2002
lemma 186, p 155
"The probability that the neighborhood of depth 2l of a node in a bipartite
graph is not tree-like is \leq gamma/n for some constant gamma and number of variable
bits n"
- a lecture by urbanke where the regular case is detailed:
http://ipg.epfl.ch/lib/exe/fetch.php?media=en:courses:doctoral_courses_2010-2011:lecture6.pdf
*)

Section prob_tree_like_border.

(* lambda: distribution of the number of destination ports by node arities
   (starts at arity 1) *)
Variables lambda : NormalizedDegreeDistribution.L K.

Lemma sum_lambda_pred L :
  (size lambda <= L)%nat -> \sum_(j < L.+1 | j != 0) lambda`_j.-1 = 1.
Proof.
move=> HL.
transitivity (\sum_(0 <= j < L.+1 | j != 0%nat ) lambda`_j.-1).
  by rewrite big_mkord.
rewrite (@big_cat_nat _ _ _ 1%nat) //=.
rewrite big1_seq //; last first.
  move=> j /andP [Hj] /=.
  rewrite in_cons in_nil orbF => Hj'.
  by rewrite Hj' in Hj.
rewrite add0r big_add1 /=.
move: (NormalizedDegreeDistribution.p1 lambda).
rewrite sum_poly_weaken // -sum_coef_horner /sum_coef => <-.
by destruct lambda.
Qed.

(* How to choose k ports among E ports excluding this of P *)
Lemma card_nodes k (P : {set port}) :
  #| [node x $ k | [disjoint x & P] ] | = 'C(#|port| - #|P|, k).
(*was  #|[set x : {set port} | #|x| == k & [disjoint x & P]]| = 'C(#|port| - #|P|, k).*)
Proof.
set A := (X in #|pred_of_set X| = _).
have -> : A = [set x : {set _} | x \subset ~: P & #|x| == k].
  apply/setP => ?; by rewrite !inE subsets_disjoint setCK andbC.
by rewrite cards_draws cardsCp.
(*set epred := (predC (mem P)).
move: (card_draws (ordinal_finType #| epred |) k).
rewrite -{1}(@card_imset _ _
          (fun s : {set 'I_(#|epred|)} => (@enum_val _ epred) @: s));
  last by apply imset_inj, enum_val_inj.
rewrite card_ord -[in 'C(_,_)]cardsE cardsCp card_ord => <-.
do !f_equal.
apply/setP => x.
rewrite inE.
symmetry.
apply/imsetP.
case: ifP.
  move/andP => [Hxk Hxp].
  rewrite disjoint_subset in Hxp.
  case e: (x == set0).
    move /eqP in e.
    rewrite e cards0 in Hxk.
    exists set0.
      by rewrite inE cards0.
    by rewrite e imset0.
  exists (enum_val @^-1: x).
    rewrite inE on_card_preimset //.
    apply enum_val_bij_on => //.
    by rewrite e.
  by apply enum_val_full.
move=> Hx [y Hy Hxy].
move/negbT/negP: Hx ; apply.
rewrite Hxy card_imset; last by apply enum_val_inj.
rewrite inE in Hy.
rewrite Hy disjoint_subset /=.
apply/subsetP => z /imsetP [t Ht ->].
by apply enum_valP.*)
Qed.

Section tree_like_step.
Variable c : comp_graph port.

(*
Variable arity_of_ports : forall q (H : q \in ports (conodes c)),
  {x : nat | exists n, n \in conodes c /\ q \in n /\ x = #| n | }.

Variable end_ports : forall q arity,
  {end_node : {set 'I_E} &
    (q \in end_node) && ((q \in ports (conodes c)) (*NB: already known node *)
    || (#|end_node| == arity (*NB: new node with the requested arity*)))
   & trivIset (end_node |: conodes c) }.
*)

Definition free_coports := ~: graph_dom (conodes c).

(* What distribution should we put on dest_port so that the distribution
   of spheres we generate is the same as the distribution of spheres
   obtained by choosing a starting node in the complete graph ensemble ? *)

Definition dest_port :=
  [set x : port * {set port} |
   [&& x.1 \in free_coports, x.1 \in x.2 & trivIset (x.2 |: conodes c)]].

Section dest_port_out.
Variables (k : nat) (p : port) (Hp : p \notin known_coports c).

Lemma trivIset_port_out (x : {set port}) :
  [disjoint x & p |: known_coports c] -> trivIset (p |: x |: conodes c).
Proof.
move=> Hxp.
apply trivIset_out; first by apply part_p.
rewrite disjointsU1 Hp.
move: Hxp.
by rewrite disjoint_sym disjointsU1 disjoint_sym => /andP [_ ->].
Qed.

Lemma dest_port_out :
  [set x in dest_port | x.1 == p & #|x.2| == k.+1] =
  [set (p, p |: x) | x in [node x $ k | [disjoint x & p |: known_coports c] ]
(*    [set x : {set port} | #|x| == k & [disjoint x & p |: known_coports c]]*)
  ].
Proof.
apply/setP => [] [p' s].
rewrite !inE /=.
symmetry.
apply/imsetP.
case: ifP.
- move/andP=> [/and3P[Hpf Hps Hsc]] /andP [/eqP Hp'p Hsk].
  subst p'.
  exists (s :\ p).
    rewrite (cardsD1 p) Hps add1n eqSS in Hsk.
    rewrite inE Hsk disjoints_subset.
    apply/subsetP => x.
    rewrite !inE negb_or -in_setC.
    case: (x == p) => //=.
    apply /subsetP: x.
    rewrite -disjoints_subset.
    by apply (trivIset_disjoint Hps).
  f_equal.
  apply/setP => x.
  rewrite !inE.
  by case: eqP => //= ->.
- move/negP => Hneg [x Hx [Hp'p Hs]].
  subst p' s.
  rewrite inE in Hx.
  move/andP: Hx => [Hxk Hxp].
  apply: Hneg.
  rewrite eqxx negb_and Hp orbT !inE eqxx trivIset_port_out //=.
  rewrite cardsU1.
  case Hpx: (p \in x).
  + by rewrite (disjoint_I_false Hpx) // !inE eqxx in Hxp.
  + by rewrite add1n /= eqSS Hxk.
Qed.
End dest_port_out.

(* Number of nodes of arity k+1 and containing p in dest_ports *)
(* When p \in border (conodes c) : 0 or 1 *)
(* When p \in graph_dom (conodes c) : 0 *)
(* When p \notin ports (conodes c) :
      choose any k ports outside of p |: ports (conodes c) (cf. card_nodes) *)
Lemma card_nodes2 k p :
  p \in free_coports ->
  #|[set x in dest_port | x.1 == p & #|x.2| == k.+1]| =
  if p \in known_coports c then
    ([exists x in conodes c, (p \in x) && (#|x| == k.+1)] : nat)
  else 'C(#|port|.-1 - #|known_coports c|, k).
Proof.
move => Hp.
have {Hp}Hp: p \notin (graph_dom (conodes c)).
  move: Hp.
  by rewrite /free_coports !inE.
case: ifPn => Hp'.
- rewrite inE Hp' andbT negbK in Hp.
  case: existsP.
  + move => [x] /and3P[Hxc Hpx Hx].
    apply (@eq_card1 _ (p,x)) => [] [p' x'].
    rewrite !inE /= xpair_eqE.
    case Hpp': (p' == p); last by rewrite andbF.
    rewrite (eqP Hpp') Hp' Hp /=.
    case Hxx': (x' == x).
      rewrite (eqP Hxx') Hpx Hx.
      by rewrite trivIset_in // part_p.
    case Hpx': (p \in x') => //=.
    case: trivIsetP => //= /(_ x' x).
    rewrite !inE eqxx Hxc /= orbT Hxx' => /(_ erefl erefl erefl).
    by rewrite (disjoint_I_false Hpx').
  + move=> He.
    apply eq_card0 => [] [p' s].
    rewrite 2!inE /=.
    apply/negbTE/negP.
    move/andP => [/and3P[Hpf Hps Hsc]] /andP [/eqP Hp'p Hsk].
    subst p'.
    apply He; exists s.
    rewrite Hsk Hps.
    by rewrite (trivIset_I1 Hsc Hps).
- clear Hp.
  transitivity ('C(#|port| - #|p |: known_coports c|, k)); first last.
    by rewrite cardsU1 Hp' subnDA subn1.
  rewrite -card_nodes dest_port_out //.
  apply card_in_imset => x y Hx Hy [] Hxy.
  apply/setP => z.
  move/setP/(_ z): Hxy.
  rewrite !inE.
  case: eqP => /= [-> _ | _ ->] //.
  rewrite !inE in Hx Hy.
  move/andP/proj2/disjoint_setI0/setP/(_ p): Hx.
  move/andP/proj2/disjoint_setI0/setP/(_ p): Hy.
  by rewrite !inE !eqxx !andbT /= => -> ->.
Qed.

(* The probability that an added edge arrives in a given node dn,
   when the arrival port p is known is:
    <probability of the arrival port to be in a node of arity #|dn|> *
    <probability that the remaining ports be the ones in #|dn|, i.e.
     choosing #|dn|-1 ports among the remaining coports (excluding p)>
  The choice of the node is normalized to 1, so that this
  probability matches the distribution we introduced on tree ensembles. *)
Definition dest_dist (dn : {set port}) : K :=
  if dn \in conodes c then 1
  else (lambda `_ #|dn|.-1) / ('C(#|port|.-1 - #|known_coports c|, #|dn|.-1))%:R.

(* NB: was burried in a proof *)
Lemma dest_dist1 s : s \in conodes c -> dest_dist s = 1.
Proof. move=> sc; by rewrite /dest_dist sc. Qed.

Lemma dest_dist_ge0 a : dest_dist a >= 0.
Proof.
rewrite /dest_dist; case: ifP => // _.
by rewrite mulr_ge0 // ?DegreeDistribution.p0 // invr_ge0 ler0n.
Qed.

Definition weighted_count {T} (p : pred T) (s : seq (T * K)) : K :=
  \sum_(xw <- s | p xw.1) xw.2.

(* new graph and its probabitlity. x is taken from dest_port *)
Definition step_dist (d : K) p x :=
  (step c p x.1 x.2, d * dest_dist x.2 / #|free_coports|%:R ).

Variable p : port.
Hypothesis Hc : tree_like c.
Hypothesis Hpb : p \in border (nodes c). (* i.e., not yet explored *)
Let next_graphs := [seq (step_dist 1 p x) | x in dest_port].

Lemma step_dest_port i :
  i \in dest_port -> trivIset (i.2 |: conodes c) && step_cond c p i.1 i.2.
Proof.
rewrite /dest_port inE /free_coports inE andbA => /andP [Hif Htriv].
by rewrite Htriv /step_cond /step_start_cond /step_end_cond Hpb inE.
Qed.

Lemma free_coports_card : (#|free_coports| > 0)%nat.
Proof.
  rewrite /free_coports cardsCp.
  move: (card_in_imset (@edges_inj _ c)).
  rewrite (edom_codom c) /edom => ->.
  rewrite -cardsCp card_gt0; apply /set0Pn.
  exists p.
  by rewrite setCD in_setU Hpb orbT.
Qed.

Lemma sum_step_border :
  \sum_(i in dest_port | i.1 \in border (conodes c)) dest_dist i.2
  = #|border (conodes c)|%:R.
Proof.
rewrite -sum1_card /dest_port.
transitivity (\sum_(x : port * {set port} |
  [&& x.1 \in border (conodes c),
  x.1 \in x.2 & trivIset (x.2 |: conodes c)]) dest_dist x.2).
  apply eq_bigl => i /=.
  rewrite andbC in_set !andbA.
  case Hb: (_ \in border _) => //=.
  by rewrite /free_coports !inE Hb.
rewrite -(pair_big_dep _
         (fun x (y : {set port}) => (x \in y) && trivIset (y |: conodes c))
         (fun x => dest_dist)) /=.
transitivity (\sum_(i in border (conodes c)) (1:K)).
  apply eq_bigr => i Hi.
  move/subsetP/(_ _ Hi): (border_p (conodes c)) => /bigcupP [s Hs His].
  rewrite (big_pred1 s) ?dest_dist1 //.
  move=> s' /=.
  case: eqP => Hs'.
    rewrite Hs' His /=.
    apply trivIset_in => //.
    by apply part_p.
  case His': (i \in s') => //=.
  apply/trivIsetP => /(_ s' s).
  rewrite !inE eqxx Hs orbT /=.
  move/eqP in Hs'.
  move/(_ erefl erefl Hs')/disjoint_setI0/setP/(_ i).
  by rewrite !inE His His'.
by rewrite sum1_card sumr_const.
Qed.

Lemma sum_step_used :
  \sum_(i in dest_port | (i.1 \in known_coports c) &&
                              (i.1 \notin border (conodes c))) dest_dist i.2
  = 0.
Proof.
rewrite big1 // => i /andP [] /=.
rewrite !inE => /andP [Hp] _ /andP [Hi1 Hi2].
by rewrite Hi1 Hi2 in Hp.
Qed.

Lemma conode_outside_ports i (j : {set port}) :
  i \notin known_coports c ->
  i \in j -> trivIset (j |: conodes c) -> j \subset ~: known_coports c.
Proof.
move=> Hi Hij Htriv.
apply/subsetP => x Hx.
rewrite inE.
move: Hi; apply contra => Hxc.
apply/bigcupP; exists j => //.
by rewrite (trivIset_I1 Htriv Hx).
Qed.

Hypothesis Hsize_lambda : (size lambda <= #|port| - #|known_coports c|)%nat.

Section dest_dist_out.
Variable i : port.
Hypothesis Hi : i \notin known_coports c.
Let U := (#|port| - #|known_coports c|).+1.

Lemma card_nodes3 (k : 'I_U) : k <> 0 ->
  (forall j : {set port},
      i \in j -> trivIset (j |: conodes c) -> (#|j| < U)%nat) ->
  #| [node x $ k | (i \in x) && trivIset (x |: conodes c)] |
(* was #|[set x:{set port} | [&& i \in x, trivIset (x |: conodes c) & #|x| == k]]| *)
  = 'C(#|port|.-1 - #|known_coports c|, k.-1).
Proof.
move=> Hk Hcj.
move: (@card_nodes2 k.-1 i).
rewrite !inE.
case: ifP => Hi'.
  by move: Hi; rewrite Hi'.
rewrite andbF /= => /(_ erefl) <-.
rewrite -(@card_imset _ _ (fun x : {set port} => (i, x))); last first.
  by move=> a b [].
do !f_equal.
apply/setP => [] [j s].
rewrite !inE /=.
case Hij: (j == i) => /=.
  rewrite (eqP Hij) Hi' andbF /=.
  have <-:  k = k.-1.+1 :> nat.
    rewrite prednK // lt0n.
    by move/eqP: Hk.
  case His: (_ && _ && _).
    by rewrite mem_imset // inE andbC.
  apply/imsetP => [] [s' Hs' [Hss']].
  by rewrite -Hss' !inE -topredE /= andbC His in Hs'.
rewrite andbF.
apply/imsetP => [] [s' Hs' [Hji]].
by rewrite Hji eqxx in Hij.
Qed.

Lemma dest_dist_out :
  \sum_(j : {set port} | (i \in j) && trivIset (j |: conodes c)) dest_dist j
     = 1.
Proof.
rewrite /dest_dist.
rewrite (partition_big
           (fun x : {set port} => nth ord0 (enum 'I_U) #|x|
(*NB:could have been enum_val (cast_ord (esym (@card_ord U)) (inord #|x|)) *)) xpredT) //=.
rewrite -[X in _ = X](sum_lambda_pred Hsize_lambda) [X in _ = X]big_mkcond /=.
apply eq_bigr => k _.
have Hcj: forall j : {set port},
    i \in j -> trivIset (j |: conodes c) -> (#|j| < U)%nat.
  move=> j Hij Htriv.
  move/subset_leq_card: (conode_outside_ports Hi Hij Htriv).
  by rewrite cardsCp /U ltnS.
case: ifP => /eqP Hk; last first.
  subst k.
  rewrite big1 // => j /andP [/andP [Hij Hj] Hk].
  case Hj0: (#|j| == 0)%nat.
    rewrite cards_eq0 in Hj0.
    by rewrite (eqP Hj0) inE in Hij.
  move: Hk Hj0.
  by rewrite (_ : #|j| = Ordinal (Hcj j Hij Hj)) // nth_ord_enum -val_eqE /= => ->.
transitivity (\sum_(j : {set port} |
                    [&& #|j| == k, i \in j & trivIset (j |: conodes c)])
               lambda`_k.-1 / ('C(#|port|.-1 - #|known_coports c|, k.-1))%:R * 1).
  apply eq_big => j.
    rewrite andbC; apply andb_id2r => /andP[ij Htriv].
    by rewrite (_ : #|j| = Ordinal (Hcj _ ij Htriv)) // nth_ord_enum.
  case/andP => /andP[] ij Htriv /eqP jk.
  case: ifP => Hj.
    elim (negP Hi).
    apply/bigcupP.
    by exists j.
  by rewrite mulr1 -jk (_ : #|j| = Ordinal (Hcj _ ij Htriv)) // nth_ord_enum.
rewrite -big_distrr /= -mulrA -{2}(mulr1 (lambda`_k.-1)).
congr GRing.mul.
set CE := 'C(_,_)%:R.
have unitCE : (CE \is a GRing.unit).
  apply unitf_gt0.
  by rewrite ltr0n bin_gt0 -!subn1 subnAC leq_sub2r // -ltnS ltn_ord.
rewrite [X in _ * X = _](_ : _ = CE); first by rewrite mulVr.
by rewrite /CE -card_nodes3 // sumr_const -cardsE.
Qed.

End dest_dist_out.

Lemma sum_step_out :
  \sum_(i in dest_port | i.1 \notin known_coports c) dest_dist i.2 =
  (#|port| - #|known_coports c|)%:R.
Proof.
rewrite /dest_port.
transitivity (\sum_(x : port * {set port} |
  [&& x.1 \notin known_coports c,
  x.1 \in x.2 & trivIset (x.2 |: conodes c)]) dest_dist x.2).
  apply eq_bigl => i /=.
  rewrite andbC in_set !andbA !inE.
  case Hb: (_ \in ports _) => //=.
  by rewrite andbF.
rewrite -(pair_big_dep (fun x => x \notin known_coports c)
         (fun x (y : {set port}) => (x \in y) && trivIset (y |: conodes c))
         (fun x => dest_dist)) /=.
transitivity (\sum_(i in port | i \notin known_coports c) (1:K)); last first.
  by rewrite sumr_const -cardsE cardsCp.
apply eq_bigr => i Hi.
by rewrite dest_dist_out.
Qed.

Lemma weight_is_dist : weighted_count predT next_graphs = 1.
Proof.
rewrite /weighted_count big_map -big_distrl -big_distrr /=.
rewrite mul1r /free_coports cardsCp.
rewrite (bigID [pred ps | ps.1 \in known_coports c]) /=.
rewrite (bigID [pred ps | ps.1 \in border (conodes c)]) /=.
rewrite (eq_bigl (fun ps => ps.1 \in border (conodes c)));
    last first.
  move=> [x s] /=.
  case Hb: (x \in border _).
    rewrite andbT.
    by move/subsetP: (border_p (conodes c)); apply.
  by rewrite andbF.
rewrite 3!big_enum_in /= sum_step_border sum_step_used addr0 sum_step_out -natrD.
(*rewrite -[in X in (X - #|ports(conodes c)|)%nat](card_ord E).*)
rewrite addnBA; last by apply max_card.
rewrite addnC.
rewrite -subnBA; last by apply card_border_ports.
move: free_coports_card.
rewrite /free_coports cardsCp.
rewrite cardsDS; last by apply border_p.
move=> Hf.
rewrite divrr // unitfE.
apply lt0r_neq0.
by rewrite ltr0n.
Qed.

Hypothesis Hpc : partial_connected c.

Section tree_like_step_lemmas.
Variable i : port * {set port}.
Hypothesis Htriv : trivIset (i.2 |: conodes c).
Hypothesis Hsc : step_cond c p i.1 i.2.

Lemma tree_like_no_sharing :
  tree_like (step c p i.1 i.2) -> i.1 \notin known_coports c.
Proof.
move=> Htl; apply/negP=> Hi.
have Hksp : known_port c (inl p) := subsetP (border_p _) _ Hpb.
move: (@Hpc (inl p) (inr i.1) Hksp Hi) => [pa [b1 [b2 /andP [Hp Hl]]]].
move: (last (inl p, b1) pa) Hl (shortenP Hp) => ep /eqP Hep Hsp.
destruct Hsp as [p' Hp' Hun _].
have Hb1: b1 = false.
  case: b1 Hep Hp' {Hp Hun} => //.
  case: p' => [] // [[|] a [|] l] //=.
  by rewrite !inE  Hpb.
subst b1.
have Hb2: b2 = true.
  case: b2 Hep (flip_seq_path Hp') => // Hep.
  rewrite last_map Hep.
  case: p' Hep {Hun Hp'} => //= a l.
  rewrite rev_cons.
  case: (rev _) => [] // [[|] b [|] l'] //=.
  case Hbdom: (b \in _) => //=.
  case Hedge: (edges c b == _) => //=.
  move/andP: Hsc => [Hsp].
  rewrite /step_end_cond inE.
  move/(mem_imset (edges c)): Hbdom.
  by rewrite edom_codom (eqP Hedge) => ->.
subst b2.
have Hlen: (size p' < #|port|*4)%nat.
  move: (@uniq_leq_size _ _ (enum [set: graph_node port * bool]) Hun).
  rewrite -cardE cardsT /=.
  rewrite card_prod card_bool card_sum addnn -muln2 -mulnA.
  apply => x _.
  by rewrite mem_enum inE.
move: Htl.
rewrite /tree_like => /forallP/(_ (Ordinal Hlen)).
have Hlen': size ((inl p, false)::p') = (Ordinal Hlen).+1 by [].
move/forallP/(_ (tcast Hlen' (in_tuple ((inl p, false)::p')))).
move/negP; apply.
rewrite /ucycleb /= /cycle /=.
rewrite -(ssr_ext.eq_tcast (t:=in_tuple ((inl p, false)::p'))) in_tupleE //.
rewrite rcons_path Hun.
rewrite (sub_path (monotonic_step_rel p i.1 i.2) Hp') Hep /=.
by rewrite sp_in_step_edom // step_edges_sp_ep // eqxx.
Qed.

Hypothesis Hi1 : i.1 \notin known_coports c.

Lemma eq_edom_edges_inout x y :
  let c' := step c p i.1 i.2 in
  y \in known_coports c ->
  (x \in edom c') && (edges c' x == y) = (x \in edom c) && (edges c x == y).
Proof.
move=> /= Hky.
rewrite /edom /= step_edom_ok // 2!inE.
case Hx: (x \in edom c) => /=.
  by rewrite orbT monotonic_edges_step.
case Hxp: (x == p) => //=.
rewrite (eqP Hxp).
rewrite step_edges_sp_ep //.
apply/negP => /eqP Hy.
by move: Hi1; rewrite Hy Hky.
Qed.

Lemma no_cycle_in_known_ports (n : 'I_(#|port|*4)%nat) :
  forall px : (n.+1).-tuple ((port + port) * bool)%type,
  cycle (graph_rel (step c p i.1 i.2)) px -> uniq px ->
  all (fun x : graph_node port * bool => known_port c x.1) px = false.
Proof.
move=> [px Hpx] /= Hcy Hun.
apply/allP => /= Hin.
move/'forall_forallP : Hc => /(_ n (Tuple Hpx)).
rewrite /ucycleb Hun andbT /= => /negP; apply.
rewrite /cycle /= in Hcy *.
destruct px as [|a px] => //.
rewrite (@eq_path_in _ _ (graph_rel c) (fun x => known_port c x.1)) //
  in Hcy; last first.
  rewrite -rcons_cons all_rcons Hin.
    by apply/allP.
  by rewrite in_cons eqxx.
move=> /= x y Hkx Hky.
destruct x as [x xb], y as [y yb].
rewrite /known_port !unfold_in /= in Hkx Hky.
destruct x as [x|x], y as [y|y], xb, yb => //=.
- by rewrite /step_nodes Hsc /step_trivIset Htriv.
- by apply eq_edom_edges_inout.
- by apply eq_edom_edges_inout.
- rewrite step_conodes_ok //.
  apply/existsP.
  case: ifP => /existsP.
    move=> [s] /andP[Hsco Hs].
    exists s.
    by rewrite inE Hsco Hs orbT.
  move=> Hex [s Hs]; apply Hex.
  exists s.
  move/andP: Hs => [Hsco Hs].
  rewrite Hs andbT.
  move: Hsco.
  rewrite !inE => /orP [|] // Hsco.
  move/andP: Hs => [].
  rewrite (eqP Hsco) => Hxi2 _.
  by apply (trivIset_I1 Htriv Hxi2).
Qed.

Lemma no_sharing_tree_like : tree_like (step c p i.1 i.2).
Proof.
apply/'forall_forallP => /= n px.
apply/negP => /andP [Hcy Hun].
move/negbT: (no_cycle_in_known_ports Hcy Hun).
move/allPn => /= [[x b]] /= Hxpx Hxkp.
destruct px as [px Hpx]; simpl in *; clear Hpx.
wlog: b px Hxpx Hcy Hun / b == false.
  move=> Hfalse.
  destruct b; last first.
    by apply (Hfalse false px).
  apply (Hfalse false (map (@flip _) (rev px))) => {Hfalse} //.
  + rewrite -mem_rev in Hxpx.
    by apply (map_f (@flip _) Hxpx).
  + destruct px => //=.
    rewrite -(rotr_cycle 1) -map_rotr.
    rewrite rev_cons rotr1_rcons /=.
    move/flip_seq_path: Hcy => /=.
    by rewrite map_rcons last_rcons belast_rcons map_rev rev_cons map_rev.
  + rewrite map_rev rev_uniq map_inj_uniq /flip //.
    move=> [a a'] [b b'] /= [] ->.
    by move/negb_inj => ->.
move/eqP => Hb; subst b.
move: (next_cycle Hcy Hxpx).
move/graph_rel_known_port => /= [[Hkpx Hkpnx] [Hxnx Hbx]].
rewrite !known_port_step // in Hkpx Hkpnx.
move/orP: Hkpx => [] Hkpx; last by rewrite Hkpx in Hxkp.
move/imsetP: Hkpx => [x' Hx Hxx'].
subst x; rename x' into x.
case_eq (next px (inr x, false)) => x' b'' Hnx.
rewrite Hnx /= in Hxnx Hbx Hkpnx Hxkp.
subst b''.
move/orP: Hkpnx => [] Hkpnx; last first.
  move: (next_cycle Hcy Hxpx) => /=.
  rewrite Hnx.
  destruct x' as [x'|x'] => //.
  move/existsP => [s].
  case/and4P.
  rewrite /step_conodes.
  destruct Bool.bool_dec => //.
  rewrite Hsc /= !inE => /orP [/eqP -> | Hsco] Hxs Hx's.
    rewrite /= in Hkpnx.
    have Hi2p := (trivIset_I1 Htriv Hx's Hkpnx).
    elim (negP Hxkp).
    by apply/bigcupP; exists i.2.
  elim: (negP Hxkp).
  by apply/bigcupP; exists s.
move/imsetP: Hkpnx => [x'' Hx' Hxx'].
subst x'; rename x'' into x'.
have Hix': x' = i.1.
  rewrite -mem_next Hnx in Hxpx.
  move: (next_cycle Hcy Hxpx).
  case_eq (next px (inr x', true)) => /= x'' b'' Hx''.
  rewrite Hx''.
  destruct x'' as [x''|x''] => //.
  destruct b'' => //.
  move/andP => [Hex''].
  rewrite /step_edges /= /step_trivIset Htriv Hsc /= ffunE /=.
  case: ifP => Hx''p.
    by rewrite eq_sym => /eqP.
  move: (step_edom_edom Htriv Hsc (negbT Hx''p) Hex'') => Hx''e Hed.
  move/setP/(_ x'): (edom_codom c).
  rewrite -{1}(eqP Hed) mem_imset //= => /esym.
  rewrite !inE => /andP [_] Hx'p.
  elim (negP Hxkp).
  apply/bigcupP; exists i.2 => //.
  by rewrite (trivIset_I1 Htriv Hx').
have Hix: x = i.1.
  move: (prev_cycle Hcy Hxpx).
  case_eq (prev px (inr x, false)) => /= x'' b'' Hx''.
  rewrite Hx''.
  destruct x'' as [x''|x''], b'' => //=.
  move/andP => [Hex''].
  rewrite /step_edges /= /step_trivIset Htriv Hsc /= ffunE /=.
  case: ifP => Hx''p.
    by rewrite eq_sym => /eqP.
  move: (step_edom_edom Htriv Hsc (negbT Hx''p) Hex'') => Hx''e Hed.
  move/setP/(_ x): (edom_codom c).
  rewrite -{1}(eqP Hed) mem_imset //= => /esym.
  rewrite !inE => /andP [_] Hx'p.
  elim (negP Hxkp).
  apply/bigcupP; exists i.2 => //.
  by rewrite (trivIset_I1 Htriv Hx).
by rewrite Hix Hix' eqxx in Hxnx.
Qed.
End tree_like_step_lemmas.

Lemma tree_like_step :
  weighted_count (@tree_like _) next_graphs / weighted_count predT next_graphs
  = (#|port| - #|known_coports c|)%:R / #|free_coports|%:R.
Proof.
rewrite weight_is_dist divr1 /weighted_count big_map big_enum_in /=.
rewrite -big_distrl -big_distrr /= mul1r; congr (_ / _).
rewrite (bigID (fun ps => ps.1 \in known_coports c)) /=.
rewrite big_pred0 ?add0r; last first.
  move=> /= i; apply/negbTE; rewrite negb_and -implybE.
  by apply/implyP => /andP[] /step_dest_port /andP[] /tree_like_no_sharing.
rewrite -sum_step_out.
apply eq_bigl => /= i.
rewrite andbAC; apply/andb_idr.
move/andP=> [] /step_dest_port /andP[]; by apply no_sharing_tree_like.
Qed.
End tree_like_step.

Variable maxdeg : nat.
Hypothesis Hmax : (size lambda <= maxdeg)%nat.

Definition dest_ports c len :=
  [set x : len.-tuple (port * {set port})%type |
   [&& all (fun i => i.1 \in i.2 :\: graph_dom (conodes c)) x,
   uniq (unzip1 x) & trivIset ([set y in unzip2 x] :|: conodes c)]].

Lemma dest_ports_0 c : dest_ports c 0 = [set [tuple]].
Proof.
apply/setP => t.
by rewrite !inE tuple0 eqxx set_nil set0U part_p.
Qed.

Variable def_port : port.
Let bnext (c : comp_graph port) := head def_port (*was ord0*) (enum (border (nodes c))).

Lemma dest_ports_step c len :
  #|border (nodes c)| != 0%nat ->
  dest_ports c len.+1 =
  \bigcup_(x in dest_port c)
     cons_tuple x @:
     dest_ports (step c (bnext c) x.1 x.2) len.
Proof.
rewrite -curry_imset2l_dep => Hb.
rewrite /dest_ports /=.
symmetry.
apply/setP => t.
apply/imset2P.
case: ifP => Ht /=.
- destruct t as [x Hszx].
  destruct x as [|x s] => //.
  have Hs := Hszx; rewrite eqSS in Hs.
  move: Ht.
  rewrite inE /= => /and3P [] /andP [] Hxin Hin /andP [Hunx Hun] Htriv.
  have Hx: x \in dest_port c.
    move: Hxin => /=.
    rewrite !inE => /andP [Hout Hx].
    rewrite Hx Hout /=.
    apply/trivIsetS: Htriv.
    apply/setSU/subsetP => /= i.
    by rewrite !inE => ->.
  have Hmem0: bnext c \in border (nodes c).
    move: Hb.
    rewrite cardE -mem_enum /bnext.
    case: (enum _) => //= a l _.
    by rewrite in_cons eqxx.
  move: (step_dest_port Hmem0 Hx) => {Hmem0} /andP [Htrivx Hcond].
  exists x (Tuple Hs).
  + exact Hx.
  + rewrite inE Hun.
    apply/andP; split.
      apply/allP => /= i Hi.
      rewrite step_codom_ok //.
      move/allP/(_ i Hi): Hin.
      rewrite !inE negb_or -andbA => ->.
      rewrite andbT.
      move: Hunx; apply contra => /eqP Heq.
      by rewrite -Heq map_f // mem_nth // (eqP Hs).
    apply/trivIsetP => A B.
    rewrite step_conodes_ok //.
    rewrite !inE /= => HA HB HAB.
    by apply (trivIsetP Htriv) => //; rewrite !inE (orbC (_ == x.2)) -orbA.
  + by apply: val_inj.
- move=> [/= x t' Hx Ht' Htt'].
  move/negP: Ht; apply.
  subst t.
  move: Ht'.
  destruct t' as [t Ht] => /=.
  rewrite inE /= => /and3P[Hin Hun Htriv].
  rewrite inE in Hx.
  rewrite inE.
  move/and3P: (Hx) => [Hx1 Hx2 Htrivx].
  have Hcond: step_cond c (bnext c) x.1 x.2.
    apply/andP; split.
      rewrite /step_start_cond.
      move: Hb.
      rewrite cardE -mem_enum /bnext.
      case: (enum (border (nodes c))) => //= a l _.
      by rewrite in_cons eqxx.
    by rewrite /step_end_cond inE -in_setC Hx1 Hx2.
  rewrite step_codom_ok // in Hin.
  apply/and3P; split.
  - apply/allP=> /= i.
    rewrite inE => /orP [/eqP ->|Hi].
      by rewrite inE -in_setC Hx1 Hx2.
    move/allP/(_ _ Hi): Hin.
    by rewrite !inE negb_or -andbA => /andP [_].
  - rewrite /= Hun andbT.
    apply/negP => /mapP [y Hy Hxy].
    move/allP/(_ _ Hy): Hin.
    by rewrite -Hxy !inE eqxx.
  - apply/trivIsetP => A B.
    rewrite /= => HA HB HAB.
    have Hsub: [set y in x.2 :: unzip2 t] :|: conodes c
         \subset [set y in unzip2 t] :|: step_conodes c (bnext c) x.1 x.2.
      apply/subsetP => X.
      rewrite !inE step_conodes_ok // !inE orbA /=.
      by rewrite (orbC (X == _)).
    by apply (trivIsetP Htriv) => //; apply (subsetP Hsub).
Qed.

Definition step_dist_it c r dests :=
  foldl
    (fun (cd : _ * K) (mapping : (port * (port * {set port}))%type) =>
       step_dist cd.1 cd.2 mapping.1 mapping.2)
    (c,r) (zip (enum (border (nodes c))) dests).

Lemma weighted_count_step c r len P :
  (#|border(nodes c)| > len)%nat ->
  weighted_count P
    [seq step_dist_it c r (tval dests) | dests in dest_ports c len.+1] =
  \sum_(x in dest_port c)
    weighted_count P
      [seq step_dist_it c r (cons_tuple x y)
      | y in dest_ports (step c (bnext c) x.1 x.2) len ].
Proof.
move=> Hlen.
rewrite dest_ports_step; last first.
  rewrite -lt0n.
  by apply (leq_ltn_trans (leq0n len)).
rewrite /weighted_count big_map.
rewrite big_mkcond /=.
rewrite [in enum _]big_mkcond /=.
rewrite big_enum_in /= partition_disjoint_bigcup /=; last first.
  move=> i j Hij.
  case: ifP => Hi.
    case: ifP => Hj.
      rewrite disjoints_subset.
      apply/subsetP => a /imsetP [x Hx ->] {a}.
      rewrite inE.
      apply/negP => /imsetP [y Hy].
      move/(f_equal (@tval _ _)).
      destruct x, y => /= /eqP.
      rewrite eqseq_cons => /andP [/eqP Hij'].
      by rewrite Hij' eqxx in Hij.
    by rewrite disjoint_sym disjoints_subset sub0set.
  by rewrite disjoints_subset sub0set.
rewrite /bnext.
case: cardEP Hlen => // s b _.
symmetry.
rewrite big_mkcond /=.
apply eq_bigr => i _.
case: ifP => Hif.
  rewrite big_map big_mkcond /= big_enum_in /= big_imset //=.
  by move=> u v _ _; apply cons_tuple_inj.
by rewrite big_set0.
Qed.

Lemma le_sum_all_cond (T : finType) (P : pred T) (r1 r2 : K) F G :
  0 < r1 -> 0 < r2 -> \sum_(i in P) G i > 0 ->
  (forall i, P i -> 0 <= F i) -> (forall i, P i -> 0 <= G i) ->
  (r1 * \sum_(i in P) G i) <= \sum_(i in P | r2 <= F i / G i) G i ->
  r1 * r2 <= (\sum_(i in P) F i) / \sum_(i in P) G i.
Proof.
move=> Hr1p Hr2p HGp HF HG Hr1.
have HGneq0 : forall i, i \in P -> r2 <= F i / G i -> G i != 0.
  move=> i Hi Hir2.
  have : 0 < F i / G i by apply (ltr_le_trans Hr2p).
  move: (HF i Hi) (HG i Hi).
  rewrite le0r.
  move/orP => [|] HFi HGi.
    by rewrite (eqP HFi) mul0r ltrr.
  rewrite pmulr_rgt0 // => /lt0r_neq0 HGi1.
  by rewrite -(invrK (G i)) invr_neq0.
apply (@ler_trans K ((\sum_(i in P | r2 <= F i / G i) G i / \sum_(i in P) G i) * (\sum_(i in P | r2 <= F i / G i) F i / \sum_(i in P | r2 <= F i / G i) G i))).
  apply ler_pmul; try by assumption || apply ltrW.
    rewrite -big_distrl -(mulr1 r1) -(mulfV (lt0r_neq0 HGp)) mulrA /=.
    apply ler_pmul => //.
      by rewrite mulr_ge0 // ltrW.
    by rewrite invr_ge0 ltrW.
  rewrite -big_distrl /=.
  rewrite (_ : \sum_(i in P | r2 <= F i / G i) F i =
          \sum_(i in P | r2 <= F i / G i) (F i / G i) * G i); first last.
    apply eq_bigr => i /andP [Hi Hir2].
    rewrite -mulrA (mulrC _ (G i)) mulfV ?mulr1 //.
    by apply HGneq0.
  have HGp' : \sum_(i in P | r2 <= F i / G i) G i > 0.
    apply (@ltr_le_trans K (r1 * (\sum_(i in P) G i))) => //.
    by apply mulr_gt0.
  rewrite -{1}(mulr1 r2) -(mulfV (lt0r_neq0 HGp')).
  rewrite mulrA big_distrr /=.
  apply ler_pmul => //.
      apply sumr_ge0 => i /andP [Hi Hir2].
      rewrite mulr_ge0 //; try by apply ltrW.
      by apply HG.
    by rewrite ltrW // invr_gt0.
  apply ler_sum => i /andP [Hi Hir2].
  apply ler_pmul => //; try by apply ltrW.
  by apply HG.
apply (@ler_trans K (\sum_(i in P | r2 <= F i / G i) F i / \sum_(i in P) G i)).
  rewrite -!big_distrl /= mulrC -mulrA (mulrA _ _ (\sum_(i in P) G i)^-1).
  rewrite mulVf ?mul1r //.
  apply lt0r_neq0.
  eapply ltr_le_trans; try apply Hr1.
  by apply mulr_gt0.
rewrite -big_distrl /=.
apply ler_pmul => //.
    apply sumr_ge0 => i /andP [Hi Hir2].
    by apply HF.
  by rewrite ltrW // invr_gt0.
rewrite [\sum_(i in P) F i](bigID (fun i => r2 <= F i / G i)) /=.
apply ler_paddr => //.
apply sumr_ge0 => i /andP [Hi Hir2].
by apply HF.
Qed.

Lemma step_dist_it_const c r y :
  step_dist_it c r y =
    let (c', r') := step_dist_it c 1 y in (c', r * r').
Proof.
rewrite /step_dist_it.
move: (enum _) (free_coports c) => s1 f.
elim: (zip s1 y) r c => [|a s IHs] r c /=.
  by rewrite mulr1.
rewrite /step_dist.
rewrite IHs mul1r.
rewrite (IHs (_ / _)).
case: (foldl _ _ _) => a' b.
by rewrite !mulrA.
Qed.

Lemma step_dist_ge0 c r b a : r >= 0 -> (step_dist c r b a).2 >= 0.
Proof.
move=> Hr; rewrite /step_dist /=.
rewrite -mulrA mulr_ge0 // mulr_ge0 // ?dest_dist_ge0 //.
by rewrite invr_ge0 ler0n.
Qed.

Lemma step_dist_it_ge0 c r t : r >= 0 -> (step_dist_it c r t).2 >= 0.
Proof.
elim: t c r => [|a t IHt] c r Hr; rewrite /step_dist_it /=.
  by case: (enum _).
case: (enum _) => //.
move=> b l /=.
elim: (zip l t) (step_dist c r b a) (step_dist_ge0 c b a Hr)
  => [] //= [b' a'] l' IH r' Hr'.
by rewrite IH // step_dist_ge0.
Qed.

Lemma cards_conode_out (c : comp_graph port) (s : {set port}) :
  dest_dist c s != 0 -> s \notin conodes c -> (#|s| <= maxdeg)%nat.
Proof.
move=> Hn0 Hs.
rewrite /dest_dist (negbTE Hs) in Hn0.
case Hlam': (lambda`_#|s|.-1 == 0).
  by rewrite (eqP Hlam') !mul0r eqxx in Hn0.
move/leq_sizeP/(_ #|s|.-1): Hmax.
case Hdeg: (maxdeg <= _)%nat.
  by move/(_ erefl)/eqP; rewrite Hlam'.
rewrite leqNgt.
move=> _; move: Hdeg.
case: #|s| => [|n].
  by rewrite ltn0.
by rewrite ltnS /= => ->.
Qed.

Lemma free_step_coports_gt c k s x :
  (k.+1 * maxdeg < #|port| - #|known_coports c|)%nat ->
  s \in border (nodes c) ->
  x \in dest_port c ->
  dest_dist c x.2 != 0 ->
  (k * maxdeg < #|port| - #|known_coports (step c s x.1 x.2)|)%nat.
Proof.
move=> Hk Hhead Hx Hr'0.
have/andP [Htriv Hcond] := step_dest_port Hhead Hx.
rewrite /known_coports /= step_coports_ok //.
rewrite /ports /=.
case/boolP : (x.2 \in conodes c) => Hx2.
  rewrite eq_setSU.
    rewrite mulSn addnC in Hk.
    by rewrite -(leq_add2r maxdeg) (leq_trans Hk) // leq_addr.
  by apply/subsetP => y Hy; apply/bigcupP; exists x.2.
rewrite cardsU disjoint_setI0; last first.
  rewrite disjoint_sym disjoints_subset.
  apply/subsetP => i Hip.
  rewrite inE; apply/negP => Hix2.
  by rewrite (trivIset_I1 Htriv Hix2 Hip) in Hx2.
rewrite cards0 subn0 addnC subnDA.
rewrite mulSn addnC in Hk.
apply (leq_sub2r maxdeg) in Hk.
rewrite -addSn addnK in Hk.
apply (leq_trans Hk).
apply leq_sub2l.
by apply (cards_conode_out Hr'0).
Qed.

Lemma sum_step_dist_it_eq0 c c' (i : port * {set port}) k r :
  enum (border (nodes c)) != [::] -> dest_dist c i.2 == 0 ->
  \sum_(xw <- [seq step_dist_it c r (i :: tval y)
              | y in dest_ports c' k]) xw.2 = 0.
Proof.
move=> Heqb Hd.
have {Heqb}[s [b Heqb]] : exists s b, s :: b = enum (border (nodes c)).
  case: (enum _) Heqb => // s b _; by exists s, b.
rewrite /step_dist_it /= /bnext -Heqb /=.
rewrite big_map /= big1 // => j _.
rewrite /(step_dist c r s i) (eqP Hd) /= mulr0 mul0r.
move: (zip b j) (step c _ _ _).
clear.
elim => //= a l IH c.
by rewrite /step_dist !mul0r IH.
Qed.

Lemma weighted_count_it_eq0 i r k c :
  enum (border (nodes c)) != [::] -> dest_dist c i.2 == 0 ->
  weighted_count predT
    [seq step_dist_it c r (i :: tval y)
    | y in dest_ports (step c (bnext c) i.1 i.2) k] = 0.
Proof. move=> ? ?; by rewrite /weighted_count sum_step_dist_it_eq0. Qed.

Lemma enum_step_border c s b x :
  enum (border (nodes c)) = s :: b ->
  x \in dest_port c ->
  enum (border (nodes (step c s x.1 x.2))) = b.
Proof.
move=> Heqb Hx.
have Hhead: s \in border (nodes c).
  by rewrite -mem_enum Heqb inE eqxx.
rewrite /= /step_nodes /step_trivIset step_dest_port //=.
move: (Heqb).
rewrite (@enum_cons _ _ s) /=.
  by move=> [->].
by rewrite Heqb.
Qed.

Lemma sum_weighted_count_it c r k s b P :
  enum (border (nodes c)) = s :: b ->
  s \in border (nodes c) ->
  (forall (c : comp_graph port) (r : K), k <= #|border (nodes c)| ->
    k * maxdeg < #|port| - #|known_coports c| ->
    weighted_count predT [seq step_dist_it c r (tval y)
                         | y in dest_ports c k] = r)%nat ->
  (k < #|border (nodes c)|)%nat ->
  (k.+1 * maxdeg < #|port| - #|known_coports c|)%nat ->
  (maxdeg <= #|port| - #|known_coports c|)%nat ->
  \sum_(x in dest_port c | P x)
      weighted_count predT
        [seq step_dist_it c r (x :: tval y)
          | y in dest_ports (step c (bnext c) x.1 x.2) k] =
   \sum_(x in dest_port c | P x) (step_dist c r s x).2.
Proof.
move=> Heqb Hhead IHk Hb Hk Hlam.
apply/eq_bigr => x /andP [Hx _].
case Hr'0: (dest_dist c x.2 == 0).
  by rewrite /= (eqP Hr'0) mulr0 mul0r weighted_count_it_eq0 // Heqb.
rewrite /step_dist_it Heqb /=.
remember (step_dist c r s x) as cr.
move: cr Heqcr => [c' r'] [] -> Hr' /=.
rewrite -Hr'.
move: IHk; rewrite /step_dist_it.
rewrite /bnext Heqb -(enum_step_border Heqb Hx) /=. apply.
  rewrite /= /step_nodes.
  rewrite (step_dest_port _ Hx) //=.
  by rewrite (cardsD1 s) Hhead add1n /= ltnS in Hb.
move/negbT in Hr'0.
by apply free_step_coports_gt.
Qed.

Lemma weighted_count_it c r k :
  (k <= #|border (nodes c)|)%nat ->
  (k * maxdeg < #|port| - #|known_coports c|)%nat ->
  weighted_count predT [seq step_dist_it c r (tval y) |y in dest_ports c k] = r.
Proof.
elim: k c r => /= [|k IHk] c r Hb Hk.
  rewrite dest_ports_0 /=.
  rewrite /image_mem enum_set1 /step_dist_it /=.
  rewrite /weighted_count big_seq1.
  by case: (enum _).
rewrite weighted_count_step //.
move: (Hb); rewrite cardE.
move eqb : (enum (border (nodes c))) => [//|s b].
have Hhead: s \in border (nodes c).
  by rewrite -mem_enum eqb inE eqxx.
have Hlam: (maxdeg <= #|port| - #|known_coports c|)%nat.
  rewrite mulSn in Hk.
  apply ltnW in Hk.
  by rewrite -(leq_add2r (k * maxdeg)) (leq_trans Hk) // leq_addr.
rewrite (bigID xpredT) /= [in X in _ + X]big_pred0 ?addr0; last first.
  by move=> ?; rewrite andbF.
rewrite (sum_weighted_count_it r predT eqb) //.
move: (weight_is_dist Hhead (leq_trans Hmax Hlam)).
rewrite /weighted_count big_map big_enum_in /=.
rewrite (bigID xpredT) /= [in X in _ + X]big_pred0 ?addr0; last first.
  by move=> ?; rewrite andbF.
rewrite -!big_distrl -!big_distrr /= mul1r -mulrA => ->.
by rewrite mulr1.
Qed.

Lemma weighted_count_it_ge0 i r k P c c' : 0 < r -> 0 <= weighted_count P
  [seq step_dist_it c r (i :: tval y) | y in dest_ports c' k].
Proof.
rewrite /weighted_count big_map => ?.
apply sumr_ge0 => ? _; by rewrite step_dist_it_ge0 // ltrW.
Qed.

Lemma tree_like_empty_border c r :
  partial_connected c -> tree_like c -> r > 0 ->
  let len := #| border (nodes c) | in
  (len * maxdeg < #|port| - #|known_coports c|)%nat ->
  let next_graphs :=
      [seq step_dist_it c r (tval dests) | dests in dest_ports c len] in
  (weighted_count (@tree_like _) next_graphs / weighted_count predT next_graphs)
  >=
  ((#|port| - #|known_coports c| - maxdeg * len)%:R / #|free_coports c|%:R) ^+ len.
  (*NB: seems to work replacing #|free_coports| with E *)
Proof.
move eqk : #|border (nodes c)| => k.
elim: k c r eqk => [|k IHk] /= c r eqk Hpc Htl Hr Hlam.
  rewrite expr0.
  move/eqP: eqk.
  rewrite cards_eq0 => /eqP eqk.
  rewrite /step_dist_it.
  rewrite eqk /= enum_set0 /=.
  rewrite dest_ports_0.
  rewrite /image_mem enum_set1 /=.
  rewrite /weighted_count !big_cons !big_nil /= Htl.
  by rewrite addr0 divrr // unitf_gt0.
(* Prepare for le_sum_all_cond *)
rewrite !weighted_count_step; try by rewrite eqk.
move: (eqk).
rewrite cardE.
move eqb : (enum (border (nodes c))) => [//|s b] _.
have Hhead: head def_port (s :: b) \in border (nodes c).
  by rewrite -mem_enum eqb inE eqxx.
have Hlam': (maxdeg <= #|port| - #|known_coports c|)%nat.
  rewrite mulSn /= in Hlam.
  by apply (leq_trans (leq_addr _ _) (ltnW Hlam)).
rewrite exprS.
set r1 := _ / _.
set r2 := _ ^+ k.
have Hknownp: (#|port| - #|known_coports c| > 0)%nat.
  by rewrite (leq_trans _ (leq_trans Hmax Hlam')) //
             lt0n DegreeDistribution.psize.
have Hfreep: (#|free_coports c| > 0)%nat.
  rewrite /free_coports cardsCs setCK cardsD.
  rewrite subn_gt0 in Hknownp.
  by rewrite subn_gt0 (leq_ltn_trans _ Hknownp) // leq_subr.
have Hknownp': (#|port| - #|known_coports c| - maxdeg * k.+1 > 0)%nat.
  by rewrite ltn_subRL addn0 mulnC.
have Hr1: r1 > 0 by rewrite divr_gt0 // ltr0n.
have Hr2: r2 > 0 by apply exprn_gt0.
apply (le_sum_all_cond Hr1 Hr2); try by move=> ? _; apply weighted_count_it_ge0.
  by rewrite -(weighted_count_step r _) ?eqk // weighted_count_it // -eqk.
(* split numerator for tree_like or not *)
rewrite [X in _ <= X](bigID (fun i : port * {set port} => i.2 \notin conodes c))
  /=.
(* remove non tree_like case *)
apply ler_paddr; first by apply sumr_ge0 => i _; apply weighted_count_it_ge0.
(* simplify rhs formula *)
set F := BIG_F.
apply (@ler_trans _
  (\sum_(i in dest_port c | tree_like (step c (bnext c) i.1 i.2)) F i)).
  rewrite (bigID xpredT) /= [in X in _ + X]big_pred0 ?addr0; last first.
    by move=> ?; rewrite andbF.
  do 2 (rewrite (sum_weighted_count_it r _ eqb) // ?eqk //; last
    by move=> ? ?; apply weighted_count_it).
  rewrite (eq_bigl (mem (dest_port c))); last by move=> ?; rewrite andbT.
  rewrite -big_distrl -big_distrr /= mulrC -ler_pdivl_mull; last first.
    move: (weight_is_dist Hhead (leq_trans Hmax Hlam')).
    rewrite /weighted_count big_map big_enum_in -big_distrl /=.
    by rewrite -big_distrr /= mul1r -mulrA => ->; by rewrite mulr1.
  rewrite mulrC -big_distrl -big_distrr /=.
  move: (tree_like_step Htl Hhead (leq_trans Hmax Hlam') Hpc).
  rewrite /weighted_count 2!big_map big_enum_in -2!big_distrl /=.
  rewrite -2!big_distrr /= 2!mul1r big_mkcond big_enum_in -big_mkcondr /=.
  rewrite -3!mulf_div (@mulfV _ r) ?gtr_eqF // mulfV; last first.
    by rewrite invr_neq0 // pnatr_eq0 -lt0n.
  rewrite mul1r /bnext eqb /= => ->.
  by rewrite ler_pmul // ?ler_nat ?leq_subr // ?invr_ge0 ltrW // ltr0n.
(* prove this is equal to the original rhs *)
rewrite {}/F ler_eqVlt.
apply /orP /or_introl /eqP.
(* remove impossible cases from sum *)
rewrite (bigID (fun i => dest_dist c i.2 == 0)) /= big1; last first.
  by move=> i /andP[_]; apply weighted_count_it_eq0; rewrite eqb.
rewrite add0r [in RHS](bigID (fun i => dest_dist c i.2 == 0)) /=.
rewrite [in RHS]big1 ?add0r; last first.
  by move=> i /andP[_]; apply weighted_count_it_eq0; rewrite eqb.
apply eq_bigl => i.
apply andb_id2r => Hd; rewrite -andbA; apply andb_id2l => Hi.
move/andP: (step_dest_port Hhead Hi) => [Htriv Hcond].
case/boolP : (i.2 \in _) => Hni; rewrite (andbF, andbT).
  (* non tree_like case *)
  rewrite /bnext eqb; apply/negP.
  move/(tree_like_no_sharing Hhead Hpc Htriv Hcond)/negP; apply.
  apply/bigcupP; exists i.2 => //.
  by move: Hi; rewrite inE => /and3P[].
(* tree_like case *)
have Htl' : tree_like (step c (bnext c) i.1 i.2).
  rewrite /bnext eqb; apply no_sharing_tree_like => //.
  apply/negP => Hi1.
  move/andP: Hcond => [_].
  rewrite /step_end_cond inE => /andP [_ Hi2].
  by rewrite (trivIset_I1 Htriv Hi2) in Hni.
rewrite Htl'; symmetry.
(* prove inequality using induction hypothesis *)
move: (eqk).
rewrite cardE eqb -(enum_step_border eqb Hi) => /= [] [].
rewrite -cardE => Hk.
move: Htl' (IHk (step c (bnext c) i.1 i.2)
                (r * dest_dist c i.2 / #|free_coports c|%:R)) => /=.
rewrite /bnext eqb /= => Htl'.
set r' := r * _ / _.
have Hrd: r' > 0.
  by rewrite divr_gt0 // ?ltr0n // mulr_gt0 // lt0r Hd dest_dist_ge0.
move: (free_step_coports_gt Hlam Hhead Hi Hd) => Hlam1.
move/(_ Hk (connected_step Hpc) Htl' Hrd Hlam1).
rewrite /weighted_count /step_dist_it eqb /= /(step_dist c r s i).
rewrite (enum_step_border eqb Hi) -/r'.
apply ler_trans.
rewrite /r2 /r1.
apply ler_expn2r.
  by rewrite nnegrE ltrW.
  by rewrite nnegrE divr_ge0 // ler0n.
rewrite ler_pmul // ?invr_ge0 ?ler0n //.
  rewrite ler_nat mulnS subnDA leq_sub2r // -subnDA leq_sub2l //.
  rewrite /known_coports step_coports_ok //.
  rewrite cardsU addnC leq_subLR addnCA leq_add2l.
  by rewrite (leq_trans (cards_conode_out Hd Hni)) // leq_addl.
have Hfc: (#|free_coports (step c s i.1 i.2)| > 0)%nat.
  rewrite (@leq_ltn_trans (k * maxdeg)%nat) //.
  apply (leq_trans Hlam1).
  rewrite (cardsCs (~: _)) setCK.
  by rewrite leq_sub2l // cardsD /= leq_subr.
rewrite lef_pinv // ?posrE ?ltr0n //.
rewrite (cardsCs (~: _)) setCK (cardsCs (~: _)) setCK.
rewrite ler_nat leq_sub2l // step_codom_ok //.
by apply subset_leq_card, subsetUr.
Qed.

End prob_tree_like_border.

Section prob_tree_like_after.

Variable maxdeg : nat.
Variable def_port : port.

Definition step_it (c : comp_graph port) d :=
  let b := enum (border (nodes c)) in
  foldl (fun c x => step c x.1 x.2.1 x.2.2) c (zip b d).

Fixpoint check_ports c (ts : seq {ffun port -> port * {set port}}) :=
  match ts with
  | [::] => true
  | t :: ts =>
    [forall i in ~: border (nodes c), t i == (def_port, set0)] &&
    let b := enum (border (nodes c)) in
    let d := map t b in
    [&& all (fun i => i.1 \in i.2 :\: graph_dom (conodes c)) d,
    uniq (unzip1 d), trivIset ([set x in unzip2 d] :|: conodes c) &
    let c' := step_it c d in
    check_ports (switch c') ts]
  end.

Definition dest_ports_seqs c len :=
  [set ts : len.-tuple {ffun port -> port * {set port}} | check_ports c ts].

Fixpoint switch_step_dist_it (lam rho : NormalizedDegreeDistribution.L K)
         c r (ts : seq {ffun port -> port * {set port}}) :=
  match ts with
  | [::] => (c, r)
  | t :: ts =>
    let b := enum (border (nodes c)) in
    let (c', r') := step_dist_it lam c r (map t b) in
    switch_step_dist_it rho lam (switch c') r' ts
  end.

Fixpoint switch_step_it c (ts : seq {ffun port -> port * {set port}}) :=
  match ts with
  | [::] => c
  | t :: ts =>
    let b := enum (border (nodes c)) in
    let c' := step_it c (map t b) in
    switch_step_it (switch c') ts
  end.

Lemma step_dist_it_1 lam c r t :
  (step_dist_it lam c r t).1 = step_it c t.
Proof.
rewrite /step_dist_it /step_it.
elim: t c r (enum _) => //= [|a t IHt] c r [|s b] //=.
by apply IHt.
Qed.

Lemma switch_step_dist_it_1 lam rho c r ts :
  (switch_step_dist_it lam rho c r ts).1 = switch_step_it c ts.
Proof.
elim: ts lam rho c r => //= t ts IH lam rho c r.
rewrite -(step_dist_it_1 lam c r).
by destruct step_dist_it.
Qed.

Section TuplePartial.
Variables (A : finType) (s : {set A}).
Variables (T : finType) (def : T).

(* ffun_of_tuple? *)
Definition tuple_to_partial (t : #|s|.-tuple T) : {ffun A -> T} :=
  [ffun i => nth def t (index i (enum s))].

(* tuple_of_ffun? *)
Definition partial_to_tuple (t : {ffun A -> T}) : #|s|.-tuple T :=
  [tuple of map t (enum s)].

Lemma tuple_to_partialK t : partial_to_tuple (tuple_to_partial t) = t.
Proof.
rewrite /tuple_to_partial /partial_to_tuple.
apply eq_from_tnth => i.
rewrite tnth_map ffunE.
by rewrite index_uniq ?(tnth_nth def) ?enum_uniq // -cardE ltn_ord.
Qed.

Lemma tuple_to_partial_in t p :
  p \in s -> tuple_to_partial t p \in t.
Proof.
rewrite /tuple_to_partial ffunE -mem_enum => Hin.
apply mem_nth.
by rewrite size_tuple cardE index_mem.
Qed.

Lemma tuple_to_partial_out t :
  [forall i in ~: s, (tuple_to_partial t) i == def].
Proof.
apply/forallP => i.
rewrite inE.
apply/implyP => si.
rewrite ffunE.
rewrite nth_default // leqNgt.
apply: contra si => si.
by rewrite -mem_enum -index_mem (leq_trans si) // size_tuple -cardE.
Qed.

Lemma tuple_to_partial_enumK t :
  [seq (tuple_to_partial t) i | i <- enum s] = t.
Proof. by apply (f_equal (@tval _ _)), tuple_to_partialK. Qed.

Lemma partial_to_tupleK (t : {ffun A -> T}) :
  [forall i in ~: s, t i == def] ->
  tuple_to_partial (partial_to_tuple t) = t.
Proof.
move/forallP => /= Hout.
rewrite /tuple_to_partial /partial_to_tuple.
apply/ffunP => i.
rewrite ffunE.
case/boolP : (i \in s) => Hi.
  rewrite (nth_map i) //.
    by rewrite nth_index // mem_enum.
  by rewrite index_mem mem_enum.
move: (Hout i).
rewrite inE Hi /= => /eqP.
rewrite nth_default // leqNgt.
apply: contra Hi.
by rewrite size_map -mem_enum -index_mem.
Qed.
End TuplePartial.

Lemma dest_ports_seqs_0 c : dest_ports_seqs c 0 = [set [tuple]].
Proof.
apply/setP => t.
by rewrite !inE tuple0 eqxx /=.
Qed.

Lemma dest_ports_seqs_step c l :
  dest_ports_seqs c l.+1 =
  \bigcup_(t in dest_ports c #|border (nodes c)|)
     cons_tuple (tuple_to_partial (def_port, set0) t) @:
     dest_ports_seqs (switch (step_it c t)) l.
Proof.
rewrite -curry_imset2l_dep.
symmetry.
apply/setP => /= t.
apply/imset2P.
case: ifP => /= Ht.
- destruct t as [x Hszx].
  destruct x as [|x s] => //.
  have Hs := Hszx; rewrite eqSS in Hs.
  move: Ht.
  rewrite inE /= => /andP[Hout] /and4P[Hall Hun Htriv Hcp].
  exists (partial_to_tuple (border (nodes c)) x) (Tuple Hs).
      rewrite inE /partial_to_tuple /=.
      by rewrite Hun Hall Htriv.
    by rewrite inE.
  rewrite partial_to_tupleK //.
  by apply/val_inj.
- move=> [/= x t' Hx Ht' Htt'].
  move/negP: Ht; apply.
  subst t.
  move: Ht'.
  destruct t' as [t Ht] => /=.
  rewrite inE /= inE => Hck.
  move: Hx.
  rewrite inE => /and3P[Hall Hun Htriv].
  rewrite /= tuple_to_partial_out /=.
  by rewrite tuple_to_partial_enumK Hall Hun Htriv Hck.
Qed.

Lemma weighted_count_switch_step l c r lam rho P :
  weighted_count P
       [seq switch_step_dist_it lam rho c r (tval seqs)
       | seqs in dest_ports_seqs c l.+1] =
  \sum_(t in dest_ports c #|border (nodes c)|)
    weighted_count P
      [seq switch_step_dist_it lam rho c r
           (tuple_to_partial (def_port, set0) t :: tval y)
      | y in dest_ports_seqs (switch (step_it c t)) l].
Proof.
(* Almost same proof as weighted_count_step *)
rewrite dest_ports_seqs_step.
rewrite /weighted_count big_map big_enum_in [LHS]/=.
rewrite big_mkcondr [\bigcup_(_ in _) _]big_mkcond /=.
rewrite partition_disjoint_bigcup /=; last first.
  move=> i j Hij.
  case: ifP => Hi.
    case: ifP => Hj.
      rewrite disjoints_subset.
      apply/subsetP => a /imsetP [x Hx ->] {a}.
      rewrite inE.
      apply/negP => /imsetP [y Hy].
      move/(f_equal (@tval _ _)) => /eqP.
      rewrite eqseq_cons => /andP [] /eqP. (*/val_inj Hij' _].*)
      move/(f_equal (@partial_to_tuple _ (border (nodes c)) _)).
      rewrite !tuple_to_partialK => /eqP.
      by rewrite (negbTE Hij).
    by rewrite disjoint_sym disjoints_subset sub0set.
  by rewrite disjoints_subset sub0set.
symmetry.
rewrite big_mkcond /=.
apply eq_bigr => i _.
case: ifP => Hif.
  rewrite big_map big_mkcond /= big_enum_in /=.
  rewrite big_imset //.
  move=> u v _ _.
  destruct u as [u Hu], v as [v Hv] => /= Heq.
  apply (f_equal (@tval _ _)) in Heq.
  move: Heq => [] Heq.
  by apply val_inj.
by rewrite big_set0.
Qed.

Lemma switch_step_dist_it_ge0 lam rho c r y :
  r >= 0 -> (switch_step_dist_it lam rho c r y).2 >= 0.
Proof.
elim: y lam rho c r => //= a y IHy lam rho c r Hr.
set d := map _ _.
move: (step_dist_it_ge0 lam c d Hr).
case: (step_dist_it _ _ _) => /= c' r'.
by apply IHy.
Qed.

Lemma weighted_count_switch_ge0 P lam rho c c' r i l :
  r > 0 ->
  weighted_count P
    [seq switch_step_dist_it lam rho c r (i :: tval y)
    | y in dest_ports_seqs c' l] >= 0.
Proof.
rewrite /weighted_count big_map => Hr.
by apply sumr_ge0 => ? _; rewrite switch_step_dist_it_ge0 // ltrW.
Qed.

Lemma switch_step_dist_it_const lam rho c r y :
  switch_step_dist_it lam rho c r y =
    let (c', r') := switch_step_dist_it lam rho c 1 y in (c', r * r').
Proof.
elim: y lam rho c r => [|t y IH] lam rho c r /=.
  by rewrite mulr1.
rewrite step_dist_it_const /=.
destruct step_dist_it.
rewrite IH [in RHS]IH.
destruct switch_step_dist_it.
by rewrite mulrA.
Qed.

Let build_graphs (lam rho : NormalizedDegreeDistribution.L K) c r len :=
  [seq switch_step_dist_it lam rho c r (tval seqs)
  | seqs in dest_ports_seqs c len].

Let tree_max l := (\sum_(i < l) maxdeg.+1 ^ i)%nat.

Lemma ports_conodes_step_it lam c r k t len :
  t \in dest_ports c k ->
  (step_dist_it lam c r t).2 != 0 ->
  (size lam <= maxdeg ->
   #|ports (nodes c)| <= len ->
   #|known_coports c| <= len ->
   #|known_coports (step_it c t)| <= len * maxdeg.+1)%nat.
Proof.
clear -def_port.
move=> Ht Hr2 Hlam.
move/(leq_trans (card_border_ports _)).
rewrite mulnS.
rewrite cardE => Hp Hcp.
apply (@leq_trans (len + size (enum (border (nodes c))) * maxdeg)).
  move: {Hp} Ht Hr2 Hcp.
  elim: k r len c t => [|k IH] //= r len c t.
    move=> Ht Hr Hcp.
    rewrite tuple0 /step_it /=.
    apply (@leq_trans len).
      by destruct (enum _) => /=.
    by apply leq_addr.
  remember (enum (border (nodes c))) as b.
  rewrite /step_it -Heqb.
  destruct b => /=.
    by rewrite zip_nill mul0n addn0.
  rewrite mulSn addnA.
  rewrite (dest_ports_step def_port) /=; last first.
    by rewrite cardE -Heqb.
  move/bigcupP => [/= i Hi].
  move/imsetP => [t' Ht' ->] /=.
  rewrite -(enum_step_border (esym Heqb) Hi).
  move=> Hr Hcp.
  have Hsb: s \in border (nodes c).
    by rewrite -mem_enum -Heqb inE eqxx.
  apply (IH (step_dist lam c r s i).2).
      by rewrite -Heqb /= in Ht'.
    move: Hr; rewrite /step_dist_it -Heqb /=.
    by rewrite (enum_step_border (esym Heqb) Hi).
  rewrite /=.
  move/andP: (step_dest_port Hsb Hi) => [Hcond Htriv].
  rewrite /known_coports step_coports_ok //.
  case /boolP: (i.2 \in conodes c) => Hi2.
    rewrite eq_setSU.
      by apply (leq_trans Hcp), leq_addr.
    apply/subsetP => j Hj.
    by apply/bigcupP; exists i.2.
  rewrite cardsU addnC.
  apply (leq_trans (leq_subr _ _)).
  apply leq_add => //.
  rewrite /step_dist_it -Heqb /= in Hr.
  set cr' := step_dist _ _ _ _ _ in Hr.
  case/boolP: (cr'.2 == 0) => Hr'.
    rewrite -(enum_step_border (esym Heqb) Hi) in Hr.
    move: (step_dist_it_const lam cr'.1 cr'.2 t').
    rewrite {1}/step_dist_it -surjective_pairing => Hc.
    move: Hr.
    rewrite Hc (eqP Hr').
    destruct step_dist_it => /=.
    by rewrite mul0r eqxx.
  rewrite /= in Hr'.
  case/boolP: (dest_dist lam c i.2 == 0) => Hdi.
    by rewrite (eqP Hdi) mulr0 mul0r eqxx in Hr'.
  by apply (cards_conode_out Hlam Hdi).
by rewrite leq_add2l leq_mul2r Hp orbT.
Qed.

Lemma part_nodes_step_it c t :
  part (nodes (step_it c t)) = nodes c.
Proof.
rewrite /step_it.
move: (enum _) => b.
elim: b c t => [|s b IH] //= c t.
  by rewrite zip_nill.
case: t => [|x t] //=.
rewrite IH /=.
rewrite /step_nodes.
by case: ifP.
Qed.

Lemma border_nodes_step_it c t :
  t \in dest_ports c #|border (nodes c)| ->
  border (nodes (step_it c t)) = set0.
Proof.
remember (#|border (nodes c)|) as k.
elim: k c t Heqk => [|k IH] c t eqk.
  rewrite tuple0 /step_it.
  case: cardEP (eqk) => //= _ _.
  by apply cards0_eq.
rewrite (dest_ports_step def_port); last by rewrite -eqk.
move/bigcupP => [/= i Hi].
move/imsetP => [t' Ht' ->] /=.
rewrite /step_it /=.
move: eqk Ht' (@enum_step_border c).
case: cardEP => //= s b [] eqk Ht' /(_ s b) Hesb.
move: (IH (step c s i.1 i.2) t').
rewrite /step_it cardE Hesb //.
by apply.
Qed.

Lemma weighted_count_switch_it len (lam rho : NormalizedDegreeDistribution.L K)
      c r l :
  (size lam <= maxdeg -> size rho <= maxdeg ->
   #|ports (nodes c)| <= len ->
   #|known_coports c| <= len ->
   border (conodes c) = set0 ->
   len * tree_max l.+1 < #|port| ->
   weighted_count predT (build_graphs lam rho c r l) = r)%nat.
Proof.
rewrite /build_graphs.
elim: l len lam rho c r => /= [|l IHl] len lam rho c r Hlam Hrho Hp Hcp Hb Hl.
  rewrite dest_ports_seqs_0.
  rewrite /image_mem enum_set1 /step_dist_it /=.
  by rewrite /weighted_count big_seq1.
rewrite weighted_count_switch_step //.
transitivity (\sum_(t in dest_ports c #|border (nodes c)|)
               (step_dist_it lam c r t).2).
  apply eq_bigr => /= t Ht.
  rewrite tuple_to_partial_enumK.
  rewrite (surjective_pairing (step_dist_it _ _ _ _)) step_dist_it_1.
  case/boolP: ((step_dist_it lam c r t).2 == 0) => Hr.
    rewrite (eqP Hr).
    rewrite /weighted_count big_map /= big1 //.
    move=> i _; rewrite switch_step_dist_it_const.
    by destruct switch_step_dist_it; rewrite mul0r.
  rewrite (IHl (len * maxdeg.+1)%nat) //.
        rewrite /switch /=.
        by apply (ports_conodes_step_it Ht Hr Hlam).
      rewrite /switch /=.
      rewrite /known_coports.
      rewrite /ports part_nodes_step_it.
      rewrite mulnS.
      by apply (leq_trans Hp), leq_addr.
    rewrite /switch /=.
    by apply border_nodes_step_it.
  rewrite (leq_ltn_trans _ Hl) //.
  rewrite /tree_max [in X in (_ <= X)%nat]sum_expr_S mulnDr mulnA.
  by apply leq_addl.
move: (weighted_count_it Hlam).
move/(_ def_port c r _ (leqnn _)).
rewrite /weighted_count big_map big_enum_in /=.
apply.
rewrite ltn_subRL.
rewrite (leq_ltn_trans _ Hl) //.
rewrite /tree_max 2!sum_expr_S mulnDr muln1 mulnA mulnDr muln1 addnA.
rewrite (leq_trans _ (leq_addr _ _)) //.
rewrite leq_add // leq_mul //.
rewrite (leq_trans _ Hp) //.
by apply card_border_ports.
Qed.

Lemma tree_like_after (lam rho : NormalizedDegreeDistribution.L K) c r len l :
  partial_connected c ->
  tree_like c ->
  (size lam <= maxdeg)%nat ->
  (size rho <= maxdeg)%nat ->
  (#|ports (nodes c)| <= len)%nat ->
  (#|known_coports c| <= len)%nat ->
  border (conodes c) = set0 ->
  r > 0 ->
  (len * tree_max l.+1 < #|port|)%nat ->
  (* after emptying the border and switching l times *)
  let next_graphs := build_graphs lam rho c r l in
  (weighted_count (@tree_like _) next_graphs / weighted_count predT next_graphs)
  >= ((#|port| - len * tree_max l.+1)%:R / #|port|%:R) ^+ (len * tree_max l).
Proof.
elim: l lam rho len c r
  => [|l IHl] /= lam rho len c r Hpc Htl Hlam Hrho Hlen Hclen Hcob Hr Hlenmax.
  subst build_graphs => /=.
  rewrite dest_ports_seqs_0 /=.
  rewrite /image_mem enum_set1 /=.
  rewrite /weighted_count !big_cons !big_nil /= Htl.
  rewrite addr0 divrr ?unitf_gt0 //.
  by rewrite /tree_max big_ord0 muln0 expr0.
have Hlenmax' := Hlenmax.
rewrite /tree_max sum_expr_S mulnDr muln1 mulnA in Hlenmax.
rewrite [tree_max l.+1]sum_expr_S mulnDr muln1 mulnA.
rewrite [tree_max l.+2]sum_expr_S mulnDr muln1 mulnA.
set len' := (len * maxdeg.+1)%nat in Hlenmax *.
rewrite exprD.
set r1 := _ ^+ len.
set r2 := _ ^+ _.
have Hb: (#|border (nodes c)| <= len)%nat.
  by rewrite (leq_trans (card_border_ports _)).
have Hr1: r1 > 0.
  apply exprn_gt0, divr_gt0.
    by rewrite ltr0n ltn_subRL addn0.
  by rewrite ltr0n; apply/card_gt0P; exists def_port.
have Hr2: r2 > 0.
  apply exprn_gt0, divr_gt0.
    by rewrite ltr0n ltn_subRL addn0.
  by rewrite ltr0n; apply/card_gt0P; exists def_port.
rewrite 2!weighted_count_switch_step le_sum_all_cond //;
        try by move=> ? _; apply weighted_count_switch_ge0.
  rewrite -weighted_count_switch_step.
  by rewrite (weighted_count_switch_it r Hlam Hrho Hlen).
(* split numerator for tree_like or not *)
rewrite [X in _ <= X](bigID(fun i : _ .-tuple _ => tree_like (step_it c i))) /=.
(* remove non tree_like case *)
apply ler_paddr; first by apply sumr_ge0 => i _;apply weighted_count_switch_ge0.
(* simplify rhs formula *)
set F := BIG_F.
apply (@ler_trans _ (\sum_(i in dest_ports c #|border (nodes c)|
                           | tree_like (step_it c i)) F i)).
  rewrite (bigID xpredT) /= [in X in _ + X]big_pred0 ?addr0; last first.
    by move=> ?; rewrite andbF.
  have HF: forall P,
        \sum_(i in dest_ports c #|border (nodes c)| | P i) F i =
        \sum_(i in dest_ports c #|border (nodes c)| | P i)
                       (step_dist_it lam c r i).2.
    move=> P; apply eq_bigr => i /andP [Hi _]; rewrite /F.
    rewrite tuple_to_partial_enumK.
    rewrite (surjective_pairing (step_dist_it _ _ _ _)) /=.
    case/boolP: ((step_dist_it lam c r i).2 == 0) => Hi2.
      rewrite (eqP Hi2).
      rewrite /weighted_count big_map /= big1 //.
      move=> ? _; rewrite switch_step_dist_it_const.
      by destruct switch_step_dist_it; rewrite mul0r.
    move: (@weighted_count_switch_it len' rho lam (switch (step_it c i))
                                     (step_dist_it lam c r i).2).
    rewrite /build_graphs.
    rewrite -(step_dist_it_1 lam c r).
    apply => //.
          by rewrite step_dist_it_1 (ports_conodes_step_it Hi Hi2).
        rewrite step_dist_it_1 /known_coports /ports part_nodes_step_it.
        apply (leq_trans Hlen).
        by rewrite /len' mulnS leq_addr.
      by rewrite step_dist_it_1 border_nodes_step_it.
    by rewrite (leq_ltn_trans _ Hlenmax) // leq_addl.
  rewrite 2!{}HF {F}.
  have Hb': (#|border (nodes c)| * maxdeg < #|port| - #|known_coports c|)%nat.
    apply (@leq_ltn_trans (#|ports (nodes c)| * maxdeg)).
      apply leq_mul => //.
      by apply card_border_ports.
    rewrite ltn_subRL.
    apply (@leq_ltn_trans (len * maxdeg.+1)).
      by rewrite mulnS leq_add // leq_mul.
    rewrite (leq_ltn_trans _ Hlenmax) //.
    by rewrite sum_expr_S mulnDr addnA (addnC len) -addnA muln1 leq_addr.
  rewrite big_mkcondr /=.
  rewrite -ler_pdivl_mulr; last first.
    move: (weighted_count_it Hlam def_port r (leqnn _) Hb').
    by rewrite /weighted_count big_map big_enum_in => ->.
  move: (tree_like_empty_border Hlam def_port Hpc Htl Hr Hb') => /=.
  rewrite /weighted_count 2!big_map big_enum_in /=.
  rewrite big_mkcond big_enum_in -big_mkcondr /=.
  set r0 := _ / _.
  set tl1 := \sum_(i in _ | tree_like _) _.
  set tl2 := \sum_(i in _ | tree_like _) _.
  have -> : tl1 = tl2.
    apply eq_bigl => /= i.
    by rewrite step_dist_it_1.
  have Hfree: (#|free_coports c| > 0)%nat.
    rewrite cardsCs setCK cardsD ltn_subRL addn0.
    apply (leq_ltn_trans (leq_subr _ _)).
    apply (leq_ltn_trans Hclen).
    by rewrite (leq_ltn_trans _ Hlenmax) // leq_addr.
  apply ler_trans.
  apply (@ler_trans K (r0 ^+ len)).
    rewrite /r1.
    apply ler_expn2r.
        by rewrite rpred_div // nnegrE ler0n.
      by rewrite rpred_div // nnegrE ler0n.
    apply ler_pmul.
          by apply ler0n.
        by rewrite invr_ge0 ler0n.
      rewrite ler_nat.
      rewrite -subnDA leq_sub2l //.
      apply leq_add => //.
      rewrite sum_expr_S mulnDr muln1.
      apply (@leq_trans len').
        by rewrite mulnC leq_mul.
      by rewrite leq_addr.
    rewrite ler_pinv //.
        by rewrite ler_nat max_card.
      by rewrite inE unitf_gt0 // ltr0n /=; apply/card_gt0P; exists def_port.
    by rewrite inE unitf_gt0 // ltr0n.
  rewrite -(subnK Hb) exprD.
  rewrite ger_pmull //.
    apply exprn_ile1.
      by rewrite mulr_ge0 ?ler0n // invr_ge0 ler0n.
    rewrite ler_pdivr_mulr ?mul1r.
      rewrite ler_nat (cardsCs (free_coports _)) setCK -subnDA.
      apply leq_sub2l, (@leq_trans #|known_coports c|).
        by rewrite cardsD leq_subr.
      by rewrite leq_addr.
    by rewrite ltr0n.
  apply exprn_gt0.
  apply mulr_gt0.
    by rewrite ltr0n ltn_subRL addn0 mulnC.
  by rewrite invr_gt0 ltr0n.
(* prove this is equal to the original rhs *)
rewrite {}/F ler_eqVlt.
apply /orP /or_introl /eqP.
(* remove impossible cases from sum *)
rewrite (bigID (fun i : _ .-tuple _  => (step_dist_it lam c r i).2 == 0))
         big1 ?add0r; last first.
  move=> i /andP [] /andP [Hi _] Hd.
  rewrite tuple_to_partial_enumK.
  rewrite (surjective_pairing (step_dist_it _ _ _ _)) /=.
  rewrite (eqP Hd).
  rewrite /weighted_count big_map /= big1 //.
  move=> j _; rewrite switch_step_dist_it_const.
  by destruct switch_step_dist_it; rewrite mul0r.
rewrite [in RHS](bigID (fun i : _ .-tuple _  =>(step_dist_it lam c r i).2 == 0))
        [in RHS]big1 /= ?add0r; last first.
  move=> i /andP [] /andP [Hi _] Hd.
  rewrite tuple_to_partial_enumK.
  rewrite (surjective_pairing (step_dist_it _ _ _ _)) /=.
  rewrite (eqP Hd).
  rewrite /weighted_count big_map /= big1 //.
  move=> j _; rewrite switch_step_dist_it_const.
  by destruct switch_step_dist_it; rewrite mul0r.
apply eq_bigl => i.
apply andb_id2r => Hd; rewrite -andbA; apply andb_id2l => Hi.
(* move/andP: (step_dest_port Hhead Hi) => [Htriv Hcond]. *)
case/boolP : (tree_like _) => Htli; last by rewrite andbF.
(* tree_like case *)
symmetry; rewrite andbT.
(* prove inequality using induction hypothesis *)
rewrite tuple_to_partial_enumK.
rewrite (surjective_pairing (step_dist_it _ _ _ _)) step_dist_it_1 /=.
have Hpci: partial_connected (switch (step_it c i)).
  destruct i as [i ?] => /=.
  clear -Hpc.
  apply connected_switch.
  rewrite /step_it.
  elim: i c (enum _) Hpc => /= [|x i IH] c [|s b] Hpc //=.
  by apply IH, connected_step.
move/(_ rho lam len' _ (step_dist_it lam c r i).2 Hpci): IHl.
rewrite tree_like_switch.
move/(_ Htli Hrho Hlam).
move/(_ (ports_conodes_step_it Hi Hd Hlam Hlen Hclen)).
have Hlen': (#|known_coports (switch (step_it c i))| <= len')%nat.
  rewrite /known_coports /ports part_nodes_step_it.
  by rewrite /len' mulnS (leq_trans Hlen) // leq_addr.
have Hd': (step_dist_it lam c r i).2 > 0.
  by rewrite ltr_def Hd step_dist_it_ge0 // ltrW.
have Hlenmaxrec: (len' * tree_max l.+1 < #|port|)%nat.
  by rewrite (leq_ltn_trans _ Hlenmax) // leq_addl.
move/(_ Hlen' (border_nodes_step_it Hi) Hd' Hlenmaxrec) => /=.
apply ler_trans.
apply ler_expn2r.
    by rewrite rpred_div // nnegrE ler0n.
  by rewrite rpred_div // nnegrE ler0n.
apply ler_pmul => //.
    by apply ler0n.
  by rewrite invr_ge0 ler0n.
by rewrite subnDA subnAC ler_nat leq_subr.
Qed.

End prob_tree_like_after.

Section tree_like_start.

Definition empty_hemi_graph : hemi_comp_graph port :=
  @Build_hemi_comp_graph _ set0 (trivIset0 _) set0 (sub0set _).

Definition single_hemi_graph (pn : {set port}) : hemi_comp_graph port :=
 @Build_hemi_comp_graph _ [set pn] (trivIset1 _) pn (subset_cover1 _).

Definition start_graph (pn : {set port}) : comp_graph port.
eapply (@Build_comp_graph _ (single_hemi_graph pn) empty_hemi_graph
                          [ffun i => i]).
+ apply/setP => i.
  rewrite !inE /graph_dom /ports /=.
  rewrite big_set1 setDv imset0 big_pred0 //.
  by move=> j; rewrite inE.
+ move=> i j _ _.
  by rewrite !ffunE.
+ move=> i _.
  by rewrite ffunE.
Defined.

Variable def_port : port.

Definition build_traces l :=
  [set (pn,seqs) | pn in {set port},
                   seqs in dest_ports_seqs def_port (start_graph pn) l].

Lemma connected_start (pn : {set port}) : partial_connected (start_graph pn).
Proof.
move=> x y.
rewrite /known_port /known_coports /ports /= big_set1 big_set0.
case: x => [] x; case: y => [] y /=; try by rewrite inE.
move => Hx Hy.
case Hxy: (x == y).
  exists [::] => /=.
  exists false, false.
  by rewrite (eqP Hxy).
exists [:: (inl y, true)] => /=.
exists false, true.
rewrite eqxx /= !andbT.
apply/existsP; exists pn.
by rewrite inE eqxx Hxy Hx Hy.
Qed.

Section tree_of_trace.
Import TreeEnsemble.

Fixpoint tree_of_trace (l : nat) k p :
  l.-tuple {ffun port -> port * {set port}} -> tree l k :=
  match l as l0 return
  l0.-tuple {ffun port -> port * {set port}} -> tree l0 k with
  | 0 => fun _ => Frontier k
  | l'.+1 =>
    fun seqs =>
    let (ep,en) := (thead seqs) p in
    Node [seq tree_of_trace (negk k) p' (tbehead seqs) | p' in en :\ ep]
  end.

Fixpoint tree_of_graph (l : nat) k (c : comp_graph port) p : tree l k :=
  match l as l0 return tree l0 k with
  | 0 => Frontier k
  | l'.+1 =>
    let ep := edges c p in
    let en := \bigcup_(en in conodes c | ep \in en) en in
    Node [seq tree_of_graph l' (negk k) (switch c) p' | p' in en :\ ep]
  end.

Definition tree'_of_trace (l : nat) (pn : {set port}) seqs : tree l.+1.*2 kv :=
  Node [seq tree_of_trace (negk kv) p seqs | p in pn].

Definition tree'_of_graph (l : nat) c (pn : {set port}) : tree l.+1.*2 kv :=
  Node [seq tree_of_graph l.*2.+1 (negk kv) (switch c) p | p in pn].

Lemma tree_of_trace_deg l k p (seqs : l.-tuple _) :
  (max_deg (tree_of_trace k p seqs) <= #|port|)%nat.
Proof.
elim: l k p seqs => //= l IH k p seqs.
destruct ((thead seqs) p) as [ep en].
rewrite max_deg_all.
rewrite size_map -cardE max_card andTb.
by apply/allP => t /mapP [p' Hp' ->] {t}.
Qed.

Lemma tree_of_graph_deg l k c p :
  (max_deg (tree_of_graph l k c p) <= #|port|)%nat.
Proof.
elim: l k c p => // l IH k c p.
rewrite max_deg_all.
rewrite size_map -cardE max_card andTb.
by apply/allP => t /mapP [p' Hp' ->] {t}.
Qed.

Lemma tree'_of_trace_deg l pn (seqs : l.*2.+1.-tuple _) :
  (max_deg (tree'_of_trace pn seqs) <= #|port|)%nat.
Proof.
rewrite max_deg_all.
rewrite size_map -cardE max_card andTb.
apply/allP => t /mapP [p Hp ->] {t pn Hp}.
apply tree_of_trace_deg.
Qed.

Lemma tree'_of_graph_deg l c pn :
  (max_deg (tree'_of_graph l c pn) <= #|port|)%nat.
Proof.
rewrite max_deg_all.
rewrite size_map -cardE max_card andTb.
apply/allP => t /mapP [p Hp ->] {t pn Hp}.
apply tree_of_graph_deg.
Qed.

Definition fintree_of_trace l pns :=
  mkFintree (@tree'_of_trace_deg l pns.1 pns.2).

Definition fintree_of_graph l pnc :=
  mkFintree (@tree'_of_graph_deg l pnc.2 pnc.1).

Lemma node_of_hemi_comp_graph ep (en : {set port}) h :
  ep \in en -> en \in (part h) ->
  \bigcup_(en in h | ep \in en) en = en.
Proof.
move=> Hep Hen.
rewrite (big_pred1 en) //= => en'.
rewrite pred1E.
case/boolP: (en == en') => Henn'.
  by rewrite -(eqP Henn') Hep Hen.
case Hen': (en' \in h) => //=.
apply/negP => Hep'.
move/trivIsetP/(_ en en' Hen Hen' Henn'): (part_p h).
by rewrite (disjoint_I_false Hep).
Qed.

(*Definition switch_odd l c := ssrnat.iter (odd l) (@switch E) c.*)

Lemma monotonic_edges_step_it c t :
  {in edom c, edges (step_it c t) =1 edges c}.
Proof.
rewrite /step_it.
move: (zip _ _) => {t} z.
elim: z c => //= [] [ep en] z IH c p Hp.
rewrite IH /=.
  by rewrite monotonic_edges_step.
by move: Hp; apply/subsetP/monotonic_edom_step.
Qed.

Lemma monotonic_edom_step_it c t : edom c \subset edom (step_it c t).
Proof.
rewrite /step_it.
move: (zip _ _) => {t} z.
elim: z c => //= [] [p [ep en]] z IH c /=.
by apply (subset_trans (monotonic_edom_step c p ep en)).
Qed.

Lemma monotonic_switch_progress f (c : comp_graph port) :
  edom c \subset edom (f c) -> {in edom c, edges (f c) =1 edges c} ->
  graph_dom (conodes c) \subset graph_dom (conodes (f c)) /\
  {in graph_dom (conodes c), switch_edges (f c) =1 switch_edges c}.
Proof.
move => Hsub He.
split.
  rewrite -2!edom_codom.
  rewrite -(eq_in_imset He).
  by apply imsetS, Hsub.
move=> // ep.
rewrite -edom_codom => /imsetP [p Hp ->] {ep}.
rewrite -[in LHS](He _ Hp).
rewrite !switch_edges_cancel //.
apply/subsetP: Hp; apply Hsub.
Qed.

Definition monotonic_codom_step_it c t :=
  proj1 (@monotonic_switch_progress (step_it ^~ t) c
                                    (monotonic_edom_step_it c t)
                                    (monotonic_edges_step_it t)).

Definition monotonic_switch_edges_step_it c t :=
  proj2 (@monotonic_switch_progress (step_it ^~ t) c
                                    (monotonic_edom_step_it c t)
                                    (monotonic_edges_step_it t)).

Lemma switch_step_it_cat c ts1 ts2 :
  switch_step_it c (ts1 ++ ts2) = switch_step_it (switch_step_it c ts1) ts2.
Proof. by elim: ts1 c => //=. Qed.

Lemma monotonic_switch_step_it c l (ts : l.*2.-tuple _) :
  edom c \subset edom (switch_step_it c ts) /\
  {in edom c, edges (switch_step_it c ts) =1 edges c}.
Proof.
elim: l ts => [|l IHl] ts.
  rewrite tuple0 /=.
  by split; [apply subxx | move => ? ?].
rewrite doubleS -addn2 addnC in ts *.
case: ts => /=.
apply: last_ind => // ts t1 _.
rewrite size_rcons /= => /eqP [] Hsz.
move: ts Hsz.
apply: last_ind => // ts t2 _.
rewrite size_rcons /= => [] [] Hsz.
rewrite -cats1 /= switch_step_it_cat.
move/eqP in Hsz.
move/(_ (Tuple Hsz)) => /= in IHl.
have Hsw : {in edom c,
               switch_edges (switch_step_it c (rcons ts t2)) =1 edges c}.
  rewrite -cats1 switch_step_it_cat /= switchK_edges => p Hp.
  rewrite monotonic_edges_step_it => //.
  + by apply IHl.
  + apply/subsetP: Hp.
    by apply IHl.
have Hsw' : edom c \subset graph_dom (conodes (switch_step_it c (rcons ts t2))).
  apply (subset_trans (proj1 IHl)).
  rewrite -cats1 switch_step_it_cat /=.
  by apply monotonic_edom_step_it.
split.
  rewrite /= /edom /=.
  by rewrite (subset_trans _ (monotonic_codom_step_it _ _)).
move=> /= p Hp.
rewrite monotonic_switch_edges_step_it.
  by rewrite Hsw.
by apply/subsetP: Hp.
Qed.

Lemma monotonic_switch_step_it_odd l c (ts : l.*2.+1.-tuple _) :
  edom c \subset edom (switch_step_it (switch c) ts) /\
  {in edom c, edges (switch_step_it (switch c) ts) =1 edges c}.
Proof.
rewrite (tuple_eta ts) /=.
have Hbe: size (behead ts) == l.*2.
  by rewrite size_behead size_tuple.
have -> : behead ts = Tuple Hbe by [].
rewrite /edom -(conodes_switch_nodes c).
split.
  rewrite (subset_trans _ (proj1 (monotonic_switch_step_it _ (Tuple Hbe))))
          /edom //=.
  by rewrite (subset_trans _ (monotonic_codom_step_it _ _)).
move=> p Hp.
rewrite (proj2 (monotonic_switch_step_it _ _)).
  rewrite monotonic_switch_edges_step_it //.
  by rewrite switchK_edges.
rewrite /edom /=.
apply/subsetP: Hp.
by apply monotonic_codom_step_it.
Qed.

Lemma tree_like_rev_step_it (c : comp_graph port) t :
  tree_like (step_it c t) -> tree_like c.
Proof.
apply tree_like_rev_subrel.
rewrite /step_it.
elim: t c (enum _) => [|[ep en] t IH] /= c [] s b //=.
apply (@subrel_trans _ (graph_rel (step c s ep en))).
  apply monotonic_step_rel.
apply IH.
Qed.

Lemma tree_like_rev_switch_step_it (c : comp_graph port) t :
  tree_like (switch_step_it c t) -> tree_like c.
Proof.
elim: t c => [//|[epen] t IH] /= c Htl.
set s := map _ _ in Htl.
apply (@tree_like_rev_step_it c s).
by rewrite -tree_like_switch IH.
Qed.

Lemma conodes_step_it c t :
  t \in dest_ports c #|border (nodes c)| ->
  tree_like (step_it c t) ->
  partial_connected c ->
  [set y in unzip2 t] :|: conodes c = conodes (step_it c t) /\
  border (conodes (step_it c t)) =
  border (conodes c) :|: \bigcup_(i <- t) (i.2 :\ i.1).
Proof.
remember (#|border (nodes c)|) as k.
elim: k c t Heqk => [|k IH] c t eqk.
  rewrite tuple0 /step_it zip_nilr /=.
  by rewrite big_nil // set_nil set0U setU0.
rewrite (dest_ports_step def_port); last by rewrite -eqk.
move/bigcupP => [/= i Hi].
move/imsetP => [t' Ht' ->] Htl Hpc /=.
rewrite /step_it /=.
remember (enum _) as b0.
move: (Heqb0) eqk (@enum_step_border c).
case: cardEP => //= s b Heqb [] eqk /(_ s b i erefl Hi) Hesb.
subst b0.
rewrite big_cons set_cons setUAC setUC.
have Htl': tree_like (step_it (step c s i.1 i.2) t').
  by move: Htl; rewrite /step_it /= Heqb /= Hesb.
destruct (IH (step c s i.1 i.2) t') as [Hc Hb].
+ rewrite /step_it cardE Hesb.
+ by [].
+ by rewrite Heqb in Ht'.
+ by [].
+ by apply connected_step.
have Hin: s \in s :: b by rewrite in_cons eqxx.
rewrite -Heqb mem_enum in Hin.
have /andP[Htriv Hcond] := step_dest_port Hin Hi.
split.
  move: Hc; rewrite /step_it /= Heqb Hesb.
  by rewrite step_conodes_ok.
move: Hb; rewrite /step_it Heqb Hesb.
rewrite setUA step_coborder_ok //.
move/andP: (Hcond); rewrite /step_end_cond inE => [] [_] /andP [_ Hi12].
case: ifP => Hi2.
  move: (tree_like_no_sharing Hin Hpc Htriv Hcond (tree_like_rev_step_it Htl')).
  move/negP; elim.
  by apply/bigcupP; exists i.2.
rewrite setDUl.
have -> // : border (conodes c) :\ i.1 = border (conodes c).
apply/setP => x.
rewrite !inE.
case: eqP => Hx //.
case Hx': (x \in border _) => //.
rewrite (trivIset_I1 Htriv Hi12) // in Hi2.
rewrite -Hx.
by apply/subsetP: Hx'; apply border_p.
Qed.

Lemma connected_step_it (c : comp_graph port) t :
  partial_connected c -> partial_connected (step_it c t).
Proof.
rewrite /step_it.
move: (zip _ _) => z.
elim: z c => //= s b IH c Hpc.
by apply IH, connected_step.
Qed.

Lemma add_edge_step_it c p t ep en :
  (index p (enum (border (nodes c))) < #|border (nodes c)|)%nat ->
  t \in dest_ports c #|border (nodes c)| ->
  nth (def_port, set0) t (index p (enum (border (nodes c)))) = (ep, en) ->
  p \in edom (step_it c t) /\ (edges (step_it c t)) p = ep.
Proof.
destruct t as [t Hsz].
move: Hsz.
rewrite /step_it cardE /=.
elim: t c => [|t0 t IH] /= c.
  move=> Hsz Hidx.
  by rewrite -(eqP Hsz) ltn0 in Hidx.
set eb := enum _.
case_eq eb => // s b Hb Hsz Hidx.
rewrite (dest_ports_step def_port); last first.
  by rewrite cardE -/eb Hb.
move=> /bigcupP /= [y] Hy.
move/step_dest_port: (Hy).
move/(_ s).
rewrite -mem_enum -/eb Hb inE eqxx => /(_ erefl) /andP [Htriv Hcond].
move/imsetP => /= [x Hx] [] ? ?.
subst t0 t.
move: Hidx => /=.
case: ifP => /eqP Hs /= Hidx Hy'.
  subst y s => /=.
  have : edges (step c p ep en) p = ep := step_edges_sp_ep Htriv Hcond.
  have : p \in edom (step c p ep en) := sp_in_step_edom Htriv Hcond.
    clear.
    elim: (zip _ _) (step c _ _ _) => // a z IH c' Hp' He.
    destruct (IH (step c' a.1 a.2.1 a.2.2)) => //.
    apply/subsetP: Hp'.
      by apply monotonic_edom_step.
    by rewrite monotonic_edges_step.
rewrite -[in B in zip B x](enum_step_border Hb Hy) //=.
move/eqP: Hsz => [].
rewrite -[in RHS](enum_step_border Hb Hy) => /eqP Hsz.
apply (IH _ Hsz); rewrite ?(enum_step_border Hb Hy) //.
destruct x.
rewrite (enum_step_border Hb Hy) in Hsz *.
by rewrite (eq_irrelevance Hsz i).
Qed.

Lemma nodes_switch_conodes (c : comp_graph port) : nodes (switch c) = conodes c.
Proof. by []. Qed.

Lemma monotone_conodes_step_it c t :
  conodes c \subset conodes (step_it c t).
Proof.
rewrite /step_it.
move: (zip _ _) => z.
elim: z c => //= a l IH c.
rewrite (subset_trans _ (IH _)) //=.
rewrite /step_conodes.
destruct Bool.bool_dec => //.
destruct step_cond => //=.
apply subsetU1.
Qed.

Lemma monotone_conodes_switch_step_it l c (ts : l.*2.-tuple _) :
  conodes c \subset conodes (switch_step_it c ts).
Proof.
elim: l c ts => [|l IH] c ts.
  by rewrite tuple0.
case: ts => [] [|t1] // [|t2 ts] //=.
rewrite doubleS => /eqP [] /eqP Hsz.
rewrite (subset_trans _ (IH _ (Tuple Hsz))) //=.
rewrite part_nodes_step_it /=.
apply monotone_conodes_step_it.
Qed.

Lemma monotone_nodes_switch_step_it l c (ts : l.*2.-tuple _) :
  nodes c \subset nodes (switch_step_it c ts).
Proof.
elim: l c ts => [|l IH] c ts.
  by rewrite tuple0.
case: ts => [] [|t1] // [|t2 ts] //=.
rewrite doubleS => /eqP [] /eqP Hsz.
rewrite (subset_trans _ (IH _ (Tuple Hsz))) //=.
rewrite (subset_trans _ (monotone_conodes_step_it _ _)) //=.
by rewrite part_nodes_step_it.
Qed.

Lemma tree_of_trace_graph (l : nat) k c seqs p :
  p \in border (nodes c) ->
  seqs \in dest_ports_seqs def_port c l.*2 ->
  let c' := switch_step_it c seqs in
  tree_like c' ->
  partial_connected c ->
  tree_of_trace k p seqs = tree_of_graph l.*2 k c' p.
Proof.
elim: l k c seqs p => // l IHl k c /= seqs p Hp.
rewrite dest_ports_seqs_step.
move/bigcupP => /= [t Ht].
move/imsetP => /= [ts Hts ->].
set c' := switch_step_it _ _.
move=> Htl Hpc.
rewrite theadE /=.
move: (Hp).
rewrite -mem_enum -index_mem -cardE => Hidx.
move: (memt_nth (def_port,set0) t Hidx).
set epn := nth _ _ _.
case_eq epn => ep en def Hin.
rewrite {}/epn in def.
have [Hpc' Hepc'] : p \in edom c' /\ edges c' p = ep.
  rewrite /c' /=.
  rewrite tuple_to_partial_enumK.
  have [Hctd Hct] := add_edge_step_it Hidx Ht def.
  split.
    by apply/subsetP: Hctd; apply monotonic_switch_step_it_odd.
  by rewrite (proj2 (monotonic_switch_step_it_odd _ _)).
rewrite Hepc'.
destruct (conodes_step_it Ht) as [Hct Hbt].
+ rewrite -tree_like_switch.
  move: Htl; rewrite /c' /= tuple_to_partial_enumK.
  apply tree_like_rev_switch_step_it.
+ by [].
rewrite (@node_of_hemi_comp_graph ep en) //.
    rewrite ffunE def.
    rewrite /image_mem.
    congr Node.
    apply eq_in_map => s Hs.
    have Hsb : s \in border (conodes (step_it c t)).
      rewrite Hbt inE big_tuple.
      apply/orP/or_intror/bigcupP.
      move/tnthP: (Hin) => [i Hi].
      exists i => //.
      by rewrite -Hi /= -mem_enum.
    move: Hts.
    rewrite dest_ports_seqs_step => /bigcupP [t' Ht'].
    move/imsetP => /= [ts' Hts' eqts].
    subst ts.
    rewrite !tbeheadE theadE.
    move: (Hsb).
    rewrite -mem_enum -index_mem -cardE => Hidx'.
    move: (memt_nth (def_port,set0) t' Hidx').
    set epn' := nth _ _ _.
    case_eq epn' => ep' en' def' Hin'.
    rewrite {}/epn' in def'.
    destruct (conodes_step_it Ht') as [Hct' Hbt'].
    + rewrite -tree_like_switch.
      move: Htl; rewrite /c' /= !tuple_to_partial_enumK.
      apply tree_like_rev_switch_step_it.
    + by apply connected_switch, connected_step_it.
    destruct (@add_edge_step_it (switch (step_it c t)) s t' ep' en')
        as [Hsd Hse] => //.
    rewrite -switchK_edges // in Hse.
    have Hs' : ep' = switch_edges c' s.
      rewrite -Hse /c' /= !tuple_to_partial_enumK.
      rewrite -(proj2 (@monotonic_switch_progress
                         (fun c => switch_step_it c ts') _ _ _)) //.
        apply (proj1 (monotonic_switch_step_it _ _)).
      apply (proj2 (monotonic_switch_step_it _ _)).
    rewrite ffunE def' Hs' /c'.
    rewrite (@node_of_hemi_comp_graph _ en').
        congr Node.
        apply eq_in_map => q.
        rewrite mem_enum -Hs' => Hq.
        rewrite negk_involution switchK.
        rewrite (IHl k (switch (step_it (switch (step_it c t)) t'))).
        + by rewrite /= !tuple_to_partial_enumK.
        + rewrite Hbt' inE big_tuple.
          apply/orP/or_intror/bigcupP.
          exists (Ordinal Hidx') => //.
          move: Hq.
          by rewrite (tnth_nth (def_port,set0)) def'.
        + by [].
        + by rewrite /c' /= !tuple_to_partial_enumK in Htl.
        + by apply connected_switch, connected_step_it,
                   connected_switch, connected_step_it.
      rewrite -Hs'.
      move: Ht'; rewrite inE => /and3P[] /allP /(_ _ Hin') /=.
      by rewrite inE => /andP [].
    rewrite /= !tuple_to_partial_enumK.
    apply (subsetP (monotone_nodes_switch_step_it _ _)).
    rewrite /= -Hct'.
    rewrite inE; apply/orP/or_introl.
    rewrite inE.
    apply (map_f snd Hin').
  move: Ht; rewrite inE => /and3P[] /allP /(_ _ Hin) /=.
  by rewrite inE => /andP [].
destruct ts as [ts Hsz].
destruct ts as [|t' ts'] => //.
move/eqP: (Hsz) => [] /eqP Hsz'.
rewrite /c' /=.
eapply (subsetP (monotone_conodes_switch_step_it _ (Tuple Hsz'))).
rewrite /= part_nodes_step_it /= tuple_to_partial_enumK -Hct inE.
apply/orP/or_introl.
rewrite inE.
apply (map_f snd Hin).
Qed.

Lemma tree'_of_trace_graph l pn (seqs : l.*2.+1.-tuple _) :
  seqs \in dest_ports_seqs def_port (start_graph pn) l.*2.+1 ->
  let c' := switch_step_it (start_graph pn) seqs in
  tree_like c' ->
  tree'_of_trace pn seqs = tree'_of_graph l c' pn.
Proof.
rewrite dest_ports_seqs_step => /bigcupP /= [t Ht].
move=> /imsetP /= [ts Hts ->].
move=> Htl.
have Hpc := @connected_start pn.
rewrite /tree'_of_trace /tree'_of_graph.
congr Node.
apply eq_in_map => p.
rewrite mem_enum => /= Hp.
rewrite /= !tbeheadE !theadE !tuple_to_partial_enumK in Htl *.
set c' := switch_step_it _ _.
move: (Hp).
rewrite -mem_enum -index_mem -cardE => Hidx.
move: (memt_nth (def_port,set0) t Hidx).
rewrite ffunE.
move Heqn : (nth _ _ _) => eqn Hin.
case: eqn Heqn Hin => ep en Heqn Hin.
(*subst epn.*)
(*rewrite tnth_mktuple (index_map enum_rank_inj) in def.*)
destruct (@conodes_step_it (start_graph pn) t Ht) as [Hct Hbt].
+ rewrite -tree_like_switch.
  by apply (tree_like_rev_switch_step_it Htl).
+ by apply connected_start.
destruct (@add_edge_step_it (start_graph pn) p t ep en) as [Hpd Hpe] => //.
rewrite -switchK_edges // in Hpe.
have Hp' : ep = switch_edges c' p.
  rewrite -Hpe /c'.
  rewrite (proj2 (@monotonic_switch_progress (switch_step_it ^~ ts) _ _ _)) //.
  + by apply (proj1 (monotonic_switch_step_it _ _)).
  + by apply (proj2 (monotonic_switch_step_it _ _)).
rewrite -Hp'.
rewrite (@node_of_hemi_comp_graph _ en).
+ congr Node.
  apply eq_in_map => q.
  rewrite mem_enum switchK => /= Hq.
  apply tree_of_trace_graph => //.
  - rewrite /= Hbt inE big_tuple.
    apply/orP/or_intror/bigcupP => /=.
    exists (Ordinal Hidx) => //.
    by rewrite (tnth_nth (def_port,set0)) Heqn.
  - by apply connected_switch, connected_step_it.
+ move: Ht; rewrite inE => /and3P[] /allP /= /(_ _ Hin).
  by rewrite /= !inE /= => /andP [].
+ rewrite /c'.
  apply (subsetP (monotone_nodes_switch_step_it _ _)).
  rewrite /= -Hct.
  rewrite inE; apply/orP/or_introl.
  rewrite inE.
  by apply/mapP; exists (ep,en).
Qed.

End tree_of_trace.

Variables lam rho : NormalizedDegreeDistribution.L K.
Variable l : nat.
Let maxdeg := maxn (size lam) (size rho).
Let tree_max l : nat := \sum_(i < l) maxdeg.+1 ^ i.
Hypothesis Hmaxlen : (maxdeg * tree_max l.+1 < #|port|)%nat.

Definition start_dist (pn : {set port}) :=
  if #|pn| == 0%nat then 0 else lam`_#|pn|.-1 / ('C(#|port|, #|pn|))%:R.

Lemma start_dist_ge0 i : 0 <= start_dist i.
Proof.
rewrite /start_dist; case : ifPn => // ?.
rewrite mulr_ge0 //; first by apply DegreeDistribution.p0.
by rewrite invr_ge0 ler0n.
Qed.

Definition graph_of_trace (pns : _ * l.-tuple _) :=
  switch_step_dist_it lam rho (start_graph pns.1) (start_dist pns.1) pns.2.

Let next_graphs :=
  [seq let (c,r) := graph_of_trace pns in (pns.1,c,r) | pns in build_traces l].

Section tree_like_start_lemmas.

Lemma weighted_count_next (P : pred ({set port} * comp_graph port)) :
  weighted_count P next_graphs =
  \sum_(pn | start_dist pn != 0)
     weighted_count (fun c => P (pn,c))
     [seq switch_step_dist_it lam rho (start_graph pn) (start_dist pn)
          (tval seqs) | seqs in dest_ports_seqs def_port (start_graph pn) l].
Proof.
rewrite /weighted_count big_map big_mkcond big_enum_in /build_traces /=.
rewrite curry_imset2l_dep.
rewrite partition_disjoint_bigcup /=; last first.
  move=> i j Hij.
  rewrite disjoints_subset.
  apply/subsetP => x /imsetP [y Hy ->] {x}.
  rewrite inE.
  apply/negP => /imsetP [z Hz] [] /eqP.
  by rewrite (negbTE Hij).
rewrite (bigID (fun i => start_dist i == 0)) big1 /= ?add0r; last first.
  move=> i Hi.
  rewrite big_imset /=.
    rewrite big1 // => j Hj.
    case: ifP => _ //.
    rewrite /graph_of_trace (eqP Hi) switch_step_dist_it_const.
    destruct switch_step_dist_it.
    by rewrite mul0r.
  by move => a b _ _ [].
apply eq_bigr => i Hi.
rewrite big_imset /=; last first.
  by move => a b _ _ [].
rewrite big_map [RHS]big_mkcond big_enum_in /=.
apply eq_bigr => j Hj /=.
rewrite /graph_of_trace /=.
by destruct switch_step_dist_it.
Qed.

Lemma tree_like_start i : tree_like (start_graph i).
Proof.
apply/'forall_forallP => n.
rewrite /ucycleb /cycle.
case => /=.
case => // s1.
case => //= [|s2].
  by case: s1 => [] [] s1 [].
case => //= [|s3 s] _.
  case: s1 => [] [] s1 [] //=;
  case: s2 => [] [] s2 [] //=; by rewrite !andbF.
case: s1 => [] [] s1 [] //=;
case: s2 => [] [] s2 [] //=; try by rewrite !andbF.
- rewrite inE /= /ports big_set1.
  by case: (s1 \in i).
- case: existsP => //= [] [j].
  rewrite inE => /and4P[/eqP -> {j} H1 H2 H3].
  case: s3 => [] [] s3 [] //=; try by rewrite !andbF.
  rewrite inE /= /ports big_set1.
  by case: (s2 \in i).
- rewrite inE /= /ports big_set1.
  by case: (s2 \in i).
- case: existsP => //= [] [j].
  by rewrite inE.
Qed.

Hypothesis Hlam : (size lam <= maxdeg)%nat.
Hypothesis Hrho : (size rho <= maxdeg)%nat.

Lemma card_ports_nodes_start i :
  start_dist i != 0 -> (#|ports (nodes (start_graph i))| <= maxdeg)%nat.
Proof.
rewrite /= /ports big_set1.
rewrite /start_dist.
case: ifP => Hi0; try by rewrite eqxx.
rewrite mulf_eq0 => Hi.
move: (@max_card port (mem i)); rewrite -bin_gt0.
rewrite -(ltr0n K) -invr_gt0 ltr_def => /andP [HC _].
rewrite (negbTE HC) orbF in Hi.
move/leq_sizeP/(_ #|i|.-1): (leq_maxl (size lam) (size rho)).
rewrite -/maxdeg.
case Hdeg: (maxdeg <= _)%nat.
  by move/(_ erefl)/eqP => Hi'; rewrite Hi' in Hi.
rewrite leqNgt.
move=> _; move: Hdeg.
case: #|i| => [|n].
  by rewrite ltn0.
by rewrite ltnS /= => ->.
Qed.

(* NB: was an intermediate step in weighted_count_start_is_dist *)
Lemma partition_big_nodes_arities {A : finType} (f : {set A} -> K) (P : pred {set A}):
  \sum_(x | P x) f x =
  \sum_(j < #|A|.+1) \sum_(i : {set A} | P i && (#|i| == j)) f i.
Proof.
rewrite (@partition_big _ _ _ [finType of {set A}] [finType of 'I_#|A|.+1]
  P (fun pn => nth ord0 (enum 'I_#|A|.+1) #|pn|) predT) //=.
apply eq_bigr => j _; apply eq_bigl => x.
have x_ub : (#|x| < #|A|.+1)%nat by rewrite ltnS; apply max_card.
by rewrite (@nth_ord_enum #|A|.+1 ord0 (Ordinal x_ub)).
Qed.

Lemma weighted_count_start_is_dist : weighted_count predT next_graphs = 1.
Proof.
rewrite weighted_count_next.
transitivity (\sum_(pn | start_dist pn != 0) start_dist pn).
  apply eq_bigr => i Hi.
  rewrite (@weighted_count_switch_it maxdeg def_port maxdeg) //.
    by apply card_ports_nodes_start => //; rewrite Hi.
  by rewrite /known_coports /ports /= big_set0 cards0.
transitivity (\sum_pn start_dist pn).
  rewrite [RHS](bigID (fun pn => start_dist pn == 0)) /=.
  rewrite [in RHS]big1 ?add0r //.
  by move=> i /eqP.
rewrite partition_big_nodes_arities.
rewrite /start_dist.
rewrite (bigID (fun j : 'I_#|port|.+1 => j == 0)) /=.
rewrite big1 /= ?add0r; last first.
  move=> i /eqP Hi.
  rewrite big1 // => j /eqP Hj.
  case: ifP => //.
  by rewrite Hj Hi eqxx.
transitivity (\sum_(j < #|port|.+1 | j != 0) lam`_j.-1 *
              \sum_(i : {set port} | #|i| == j) 1
               / ('C(#|port|, j))%:R).
  apply eq_bigr => k Hk.
  rewrite big_distrr /=.
  apply eq_bigr => i /eqP -> /=.
  have -> : (k == O :> nat) = false by apply/negbTE.
  by rewrite mul1r.
transitivity (\sum_(j < #|port|.+1 | j != 0) lam`_j.-1).
  apply eq_bigr => k Hk.
  rewrite -[RHS]mulr1.
  f_equal.
  rewrite -big_distrl -[RHS](@divff K ('C(#|port|, k))%:R) /=.
    f_equal.
    by rewrite -card_draws sumr_const cardsE.
  apply lt0r_neq0.
  rewrite ltr0n bin_gt0.
  by apply (ltn_ord k).
have HlamE : (size lam <= #|port|)%nat.
  apply (leq_trans Hlam).
  rewrite (leq_trans _ (ltnW Hmaxlen)) //.
  by rewrite /tree_max sum_expr_S mulnDr muln1 leq_addr.
by rewrite sum_lambda_pred.
Qed.

End tree_like_start_lemmas.

Theorem tree_like_neighbor :
  (weighted_count (@tree_like _ \o snd) next_graphs
   / weighted_count predT next_graphs)
  >= ((#|port| - maxdeg * tree_max l.+1)%:R / #|port|%:R) ^+ (maxdeg * tree_max l).
Proof.
rewrite 2!weighted_count_next.
have Hlam : (size lam <= maxdeg)%nat by apply leq_maxl.
have Hrho : (size rho <= maxdeg)%nat by apply leq_maxr.
have Hw := weighted_count_start_is_dist Hlam Hrho.
rewrite weighted_count_next in Hw.
clear next_graphs.
apply le_sum_all.
- by rewrite /= Hw ltr01.
- move=> i.
  case: ifP => // Hi _.
  rewrite (@weighted_count_switch_it maxdeg def_port maxdeg) //.
  + rewrite ltr_def Hi /=; exact: start_dist_ge0.
  + by rewrite card_ports_nodes_start // Hi.
  + by rewrite /known_coports /ports /= big_set0 cards0.
- move=> /= i.
  case: ifP => Hi // _.
  apply tree_like_after => //.
  + by apply connected_start.
  + by apply tree_like_start.
  + by rewrite card_ports_nodes_start // Hi.
  + by rewrite /known_coports /ports /= big_set0 cards0.
  + rewrite ltr_def Hi /=; exact: start_dist_ge0.
Qed.

End tree_like_start.

End prob_tree_like_neighbor.

End PartialComputationGraph.
