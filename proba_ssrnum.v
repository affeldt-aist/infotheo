(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From mathcomp Require Import path choice fintype tuple finfun finset bigop.
From mathcomp Require Import matrix.
Require Import ProofIrrelevance FunctionalExtensionality.
Require Import ssr_ext ssralg_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope tuple_ext_scope.

(** * Distribution *)

(** Distribution over sample space #A#%$A$%
   %(numerically-valued distribution function $p : A \to \mathbb{R}$;
   for any $a \in A$, $0 \leq p(a)$; $\sum_{i \in A} p(i) = 1$)%: *)

From mathcomp Require Import ssralg ssrnum.

Variable R : realFieldType.
Local Open Scope ring_scope.

Record pos_fun (T : finType) := mkPosFun {
  pos_f :> T -> R ;
  Rle0f : forall a, 0 <= pos_f a }.

Notation "T '->' 'R+' " := (pos_fun T) (at level 10, format "'[' T  ->  R+ ']'") : reals_ext_scope.

Local Open Scope reals_ext_scope.

Import Num.Theory.

Section distribution_definition.

Variable A : finType.

Record dist := mkDist {
  pmf :> A -> R+ ;
  pmf1 : \sum_(a in A) pmf a = 1 }.

Definition makeDist : forall pmf : A -> R,
  (forall a, 0 <= pmf a) -> \sum_(a|a \in A) pmf a = 1 -> dist.
move=> f H1 H2.
apply (@mkDist (@mkPosFun _ f H1) H2).
Defined.

Lemma dist_max (P : dist) a : P a <= 1.
Proof.
rewrite -(pmf1 P) (_ : P a = \sum_(a' in A | a' == a) P a').
  rewrite big_pred1_eq (bigID (pred1 a)) /= big_pred1_eq Num.Theory.ler_paddr //.
  rewrite sumr_ge0 // => a' aa'; by apply Rle0f.
by rewrite big_pred1_eq.
Qed.

Lemma dist_eq d d' : pmf d = pmf d' -> d = d'.
Proof.
destruct d as [d d1] => /=.
destruct d' as [d' d'1] => /= H.
move: d1 d'1.
rewrite H.
move=> d1 d'1.
by rewrite (proof_irrelevance _ d1 d'1).
Qed.

End distribution_definition.

(** Distributions over sets with two elements *)

Import GRing.

Section bdist_sect.

Variable A : finType.
Hypothesis HA : #|A| = 2%nat.
Variable p : R.
Hypothesis Hp : 0 <= p <= 1.

Definition bdist : dist A.
apply makeDist with [ffun x => if x == Set2.a HA then 1 - p else p].
- move=> a.
  rewrite ffunE.
  case: ifP => _; last by case/andP : Hp.
  rewrite -(GRing.subrr 1).
  apply ler_sub => //.
  by case/andP: Hp.
- rewrite /index_enum -enumT Set2.enumE /=.
  rewrite big_cons /= big_cons /= big_nil.
  rewrite addr0 2!ffunE.
  rewrite eqxx.
  move: (Set2.a_neq_b HA).
  rewrite eqtype.eq_sym.
  move/negbTE => ->.
  by rewrite subrK.
Defined.

End bdist_sect.

(** About distributions over sets with two elements *)

Lemma pos_fun_eq {C : finType} (f g : C -> R+) : pos_f f = pos_f g -> f = g.
Proof.
destruct f as [f Hf].
destruct g as [g Hg].
move=> /= ?; subst.
suff : Hf = Hg by move=> ->.
by apply proof_irrelevance.
Qed.

Section charac_bdist_sect.

Variable A : finType.
Variables P Q : dist A.
Hypothesis card_A : #|A| = 2%nat.

Lemma charac_bdist : {r1 | {Hr1 : 0 <= r1 <= 1 & P = bdist card_A Hr1 }}.
Proof.
destruct P as [[pmf pmf0] pmf1].
exists (1 - pmf (Set2.a card_A)).
have Hr1 : 0 <= 1 - pmf (Set2.a card_A) <= 1.
  move: (dist_max (@mkDist _ (mkPosFun pmf0) pmf1) (Set2.a card_A)) => /= H1.
  move: (pmf0 (Set2.a card_A)) => H2.
  apply/andP; split.
    by rewrite -(subrr 1) ler_sub.
  by rewrite -{2}(subr0 1) ler_sub.
exists Hr1.
apply dist_eq => /=.
apply pos_fun_eq => /=.
apply FunctionalExtensionality.functional_extensionality => a.
rewrite ffunE.
case: ifP => Ha.
  move/eqP : Ha => ->.
  by rewrite opprB addrC subrK.
rewrite -pmf1.
rewrite /index_enum -enumT Set2.enumE.
rewrite big_cons /= big_cons /= big_nil.
rewrite addr0 -addrA addrC subrK.
by move/negbT/Set2.neq_a_b/eqP : Ha => ->.
Qed.

End charac_bdist_sect.

Section big_sums_tuples.

Variable A : finType.

Lemma sum_1_tuple (F G : _ -> R) P Q :
  (forall i : tuple_finType 1 A, F i = G (thead i)) ->
  (forall i : tuple_finType 1 A, P i = Q (thead i)) ->
  \sum_(i in {: 1.-tuple A} | P i) F i = \sum_(i in A | Q i) G i.
Proof.
move=> FG PQ.
rewrite (reindex_onto (fun i => [tuple of [:: i]]) (fun p => thead p)) /=; last first.
  case/tupleP => h t X; by rewrite theadE (tuple0 t).
apply eq_big => x //.
by rewrite (PQ [tuple x]) /= theadE eqxx andbC.
move=> X; by rewrite FG.
Qed.

End big_sums_tuples.

Lemma dist2tuple1 : forall A, dist A -> dist [finType of 1.-tuple A].
Proof.
move=> A d.
apply makeDist with (fun x => d (thead x)).
move=> a; by apply Rle0f.
rewrite -(pmf1 d); by apply: sum_1_tuple.
Defined.

Definition tuple2dist : forall A : finType, dist [finType of 1.-tuple A] -> dist A.
move=> A d.
apply makeDist with (fun x => d [tuple x]).
move=> a; by apply Rle0f.
rewrite -(pmf1 d).
symmetry.
apply: sum_1_tuple => // i.
by rewrite thead_tuple1.
Defined.

Lemma mulr_ge0
   (R : numDomainType) (I : Type) (r : seq I)
     (P : pred I) (F : I -> R) :
   (forall i : I, P i -> 0 <= F i) -> 0 <= \prod_(i <- r | P i) F i.
Proof. move=> H. apply big_ind => // *; by apply mulr_ge0. Qed.

Lemma iter_mul : forall n, iter n ((@mul R) 1) 1 = 1.
Proof. elim=> // m /= ->; by rewrite mul1r. Qed.

Local Open Scope tuple_ext_scope.

Section tuple_dist_definition.

Variable A : finType.
Variable P : dist A.
Variable n : nat.

Definition tuple_pmf (ta : n.-tuple A) := \prod_(i < n) P ta\_i.

(** Definition of the product distribution (over a tuple): *)

Definition tuple_dist : dist [finType of n.-tuple A].
apply makeDist with tuple_pmf.
  move=> a.
  apply mulr_ge0 => i _. by apply Rle0f.
pose P' := fun (a : 'I_n) b => P b.
suff : \sum_(f : {ffun 'I_n -> A }) \prod_(i < n) P' i (f i) = 1.
  rewrite (reindex_onto (fun j => finfun (fun x => j\_x))
    (fun i => tcast (card_ord n) (fgraph i))) /=.
  - move=> H; rewrite /tuple_pmf -{2}H {H}.
    apply eq_big => t /=.
    + rewrite inE; symmetry; apply/eqP.
      apply eq_from_tnth => i.
      rewrite tcastE tnth_fgraph ffunE; f_equal.
      rewrite enum_val_ord; by apply: val_inj.
    + move=> _.
      apply eq_bigr => i _ /=.
      by rewrite ffunE.
  move=> f _.
  apply/ffunP => i.
  by rewrite ffunE tcastE tnth_fgraph -enum_rank_ord enum_rankK.
rewrite -bigA_distr_bigA /= /P'.
rewrite [X in _ = X](_ : 1 = \prod_(i < n) 1); last first.
  rewrite big_const_ord.
  by rewrite iter_mul.
apply eq_bigr => i _.
apply pmf1.
Defined.

End tuple_dist_definition.

Notation "P `^ n" := (tuple_dist P n) (at level 5) : proba_scope.
Local Open Scope proba_scope.

Lemma tuple_pmf_singleton A (d : dist A) (i : 1.-tuple A) :
  forall a, a \in [finType of 1.-tuple A] -> (d `^ 1) a = d (thead a).
Proof.
move=> a Ha.
rewrite /tuple_dist /= /tuple_pmf /index_enum -enumT enum_ordS big_cons.
rewrite (_ : enum 'I_O = [::]); last by apply size0nil; rewrite size_enum_ord.
by rewrite big_nil mulr1.
Qed.

Local Open Scope proba_scope.

Lemma big_tcast (A : finType) n (F : n.-tuple A -> R) (P : pred {: n.-tuple A}) m
  (n_m : m = n) :
  \sum_(p in {: n.-tuple A} | P p) (F p) =
  \sum_(p in {: m.-tuple A} | P (tcast n_m p)) (F (tcast n_m p)).
Proof.
subst m.
apply eq_bigr => i.
case/andP=> H1 H2.
by rewrite tcast_id.
Qed.

Lemma rsum_rmul_tuple_pmf_tnth A n k (P : dist A) :
  \sum_(t : {:k.-tuple (n.-tuple A)}) \prod_(m < k) (P `^ n) t\_m = 1.
Proof.
transitivity (\sum_(j : {ffun 'I_k -> (tuple_finType n A)})
  \prod_(m : 'I_k) tuple_pmf P (j m)).
  rewrite (reindex_onto (fun p => Finfun p) (fun x => fgraph x)) //=; last by case.
  rewrite (@big_tcast _ _ _ _ _ (card_ord k)) //.
  apply eq_big => //.
  - move=> i /=; by rewrite eqxx.
  - move=> i Hi.
    apply eq_bigr => j _.
    by rewrite FunFinfun.fun_of_finE tcastE enum_rank_ord.
rewrite -(bigA_distr_bigA (fun m xn=> tuple_pmf P xn)) /= big_const.
rewrite (_ : \sum_(_ <- _) _ = 1); last first.
  transitivity (\sum_( j : _) P `^ n j) => //.
  by rewrite pmf1.
by rewrite iter_mul.
Qed.

Lemma rsum_rmul_tuple_pmf {A} n k (P : dist A) :
  \sum_(t in {:k.-tuple (n.-tuple A)}) \prod_(x <- t) (P `^ n) x = 1.
Proof.
rewrite -[X in _ = X](rsum_rmul_tuple_pmf_tnth n k P).
apply eq_bigr => t _.
rewrite big_tnth /=.
rewrite (reindex_onto (cast_ord (size_tuple t))
  (cast_ord (esym (size_tuple t)))) //=; last first.
  move=> i _; by apply val_inj.
apply eq_big => //= i.
- symmetry.
  apply/val_eqP.
  by apply val_inj.
- move=> _; by rewrite !tvalK tcastE esymK.
Qed.

(** Wolfowitz's counting principle: *)

Lemma iter_add_mul (x : R) : forall n : nat, ssrnat.iter n (add x) 0 = (n)%:R * x.
Proof.
elim=> //=; first by rewrite mul0r.
move=> n ->.
by rewrite -addn1 natrD mulrDl mul1r addrC.
Qed.

Section wolfowitz_counting.

Variable B : finType.
Variable P : dist B.
Variable k : nat.
Variable A : {set k.-tuple B}.

Lemma wolfowitz a b alpha beta : 0 < alpha -> 0 < beta ->
  a <= \sum_(x in A) P `^ k x <= b ->
  (forall x : k.-tuple _, x \in A -> alpha <= P `^ k x <= beta) ->
  a / beta <= (#| A |)%:R <= b /alpha.
Proof.
move=> Halpha Hbeta H1 H2.
have H3 : \sum_(x in A) tuple_pmf P x <= (#|A|)%:R * beta.
  have H3 : \sum_(x in A | predT A ) tuple_pmf P x <= (#|A|)%:R * beta.
    apply ler_trans with (\sum_(x in A | predT A) [fun _ => beta] x).
    apply ler_sum => i /andP [] iA _. by case/andP: (H2 i iA).
    rewrite -big_filter /= big_const_seq /=.
    rewrite iter_add_mul.
    rewrite ler_pmul //.
    by rewrite (_ : 0 = 0%:R) // ler_nat leq0n.
    by apply ltrW.
    rewrite filter_index_enum count_predT cardE.
    set e := enum _.
    suff -> : e = enum A by done.
    rewrite /e {e}.
    apply eq_enum => i; by rewrite /in_mem /= andbC.
  eapply ler_trans; last by apply H3.
  rewrite ler_eqVlt; apply/orP; left.
  apply/eqP.
  apply eq_bigl => i; by rewrite andbC.
have H4 : (#|A|)%:R * alpha <= \sum_(x in A) tuple_pmf P x.
  have H4 : (#|A|)%:R * alpha <= \sum_(x in A | predT A) tuple_pmf P x.
    apply ler_trans with (\sum_(x in A | predT A) [fun _ => alpha] x); last first.
      apply ler_sum => i /andP [] Hi _; by case/andP: (H2 i Hi).
    rewrite -big_filter /= big_const_seq /=.
    rewrite iter_add_mul /=.
    rewrite ler_pmul //.
    by apply ltrW.
    rewrite filter_index_enum count_predT cardE.
    set e1 := enum _.
    set e2 := enum _.
    suff -> : e2 = enum A by done.
    rewrite /e2 {e2}.
    apply eq_enum => i; by rewrite /in_mem /= andbC.
  eapply ler_trans; first by apply H4.
  rewrite ler_eqVlt; apply/orP; left.
  apply/eqP.
  apply eq_bigl => i; by rewrite andbC.
case/andP: H1 => H1 H1'.
apply/andP; split.
  rewrite ler_pdivr_mulr //.
  eapply ler_trans; first by apply H1.
  done.
rewrite ler_pdivl_mulr //.
eapply ler_trans; first by apply H4.
done.
Qed.

End wolfowitz_counting.

Import Num.Theory.

Section prod_dist_definition.

Variables A B : finType.
Variable P1 : dist A.
Variable P2 : dist B.

Definition prod_dist : dist [finType of A * B].
apply makeDist with (fun ab => P1 ab.1 * P2 ab.2).
  move=> ?.
  apply mulr_ge0; by apply Rle0f.
rewrite -(pair_big xpredT xpredT (fun a b => P1 a * P2 b)) /=.
rewrite -(pmf1 P1).
apply eq_bigr => a _.
by rewrite -big_distrr /= pmf1 mulr1.
Defined.

Definition dist_prod_proj1 (P : dist [finType of A * B]) : dist A.
apply makeDist with (fun a => \sum_(b in B) P (a, b)).
- move=> a.
  apply sumr_ge0 => a' _; by apply Rle0f.
- rewrite -(pmf1 P) pair_big /=.
  apply eq_bigr; by case.
Defined.

Definition dist_prod_proj2 (P : dist [finType of A * B]) : dist B.
apply makeDist with (fun b => \sum_(a in A) P (a, b)).
- move=> a.
  apply sumr_ge0 => a' _; by apply Rle0f.
- rewrite exchange_big /= -(pmf1 P) pair_big /=.
  apply eq_big; by case.
Defined.

End prod_dist_definition.

Notation "P1 `x P2" := (prod_dist P1 P2) (at level 6) : proba_scope.

Section tuple_prod_cast.

Variables A B : finType.
Variable n : nat.
Variable P : dist [finType of 'rV[A * B]_n].

Definition dist_tuple_prod_cast : dist [finType of 'rV[A]_n * 'rV[B]_n].
(* begin hide *)
apply makeDist with (fun xy => P (prod_rV xy)).
(* end hide *)
move=> a; by apply Rle0f.
rewrite -(pmf1 P).
rewrite (reindex_onto (fun x => rV_prod x) (fun y => prod_rV y)); last first.
  move=> i _; by rewrite prod_rVK.
rewrite /=.
apply eq_big => /= i.
- by rewrite inE rV_prodK eqxx.
- move=> _; by rewrite rV_prodK.
Defined.

End tuple_prod_cast.

(** * Probability *)

Lemma ler_sum_new I (r : seq I) (P Q : pred I) (F G : I -> R) :
    (forall i, P i -> F i <= G i) ->
  (forall i, Q i -> 0 <= G i) ->
  (forall i, P i -> Q i) ->
  \sum_(i <- r | P i) F i <= \sum_(i <- r | Q i) G i.
Proof.
move=> f_g Qg H.
elim: r => [| hd tl IH].
- by rewrite !big_nil.
- rewrite !big_cons /=.
  case: ifP => HP.
  + rewrite (H _ HP).
    rewrite ler_add //.
    by apply f_g.
  + case: ifP => // HQ.
    apply ler_trans with (\sum_(j <- tl | Q j) G j).
      by apply IH.
    rewrite -{1}(add0r (\sum_(j <- tl | Q j) G j)).
    rewrite ler_add //.
    by apply Qg.
Qed.

Lemma new_Rle_big_predU_f {A : finType}
( f : A -> R) (P Q : pred A)
: (forall a, 0 <= f a) ->
  \sum_(i in A | [predU P & Q] i) f i <=
  \sum_(i in A | P i) f i + \sum_(i in A | Q i) f i.
Proof.
move=> Hf.
elim: (index_enum _) => //.
- rewrite !big_nil /=; by rewrite addr0.
- move=> h t IH /=.
  rewrite !big_cons /=.
  case: ifP => /=.
  + case/orP => [HP1 | HP2].
    * rewrite unfold_in in HP1.
      rewrite HP1.
      case: ifP => // HP2.
      - rewrite -addrA ler_add //.
        eapply ler_trans; first by apply IH.
        rewrite ler_add // ler_addr.
        by apply Hf.
      - by rewrite -addrA ler_add.
(*        eapply ler_trans; first by apply IH.
        rewrite ler_add // ler_addr.
        by apply Hf.
      - rewrite Rplus_assoc; apply Rplus_le_compat_l.
        eapply Rle_trans; first by apply IH.
        by apply Req_le.*)
    * rewrite unfold_in in HP2.
      rewrite HP2.
      case: ifP => // HP1.
      - rewrite -addrA ler_add //.
        eapply ler_trans; first by apply IH.
        rewrite ler_add // ler_addr.
        by apply Hf.
      - rewrite [in X in _ <= X]addrC.
        rewrite -addrA.
        rewrite ler_add //.
        eapply ler_trans; first by apply IH.
        by rewrite addrC.
  + move/negbT.
    rewrite negb_or.
    case/andP.
    rewrite unfold_in; move/negbTE => ->.
    rewrite unfold_in; move/negbTE => ->.
    by apply IH.
Qed.

Section probability.

Variable A : finType.
Variable P : dist A.

(** Probability of an event #P#%$P$% with distribution #p#%$p$%
   %($Pr_p[P] = \sum_{i \in A, P\,i} \, p(i)$)%: *)

Definition Pr (E : {set A}) := \sum_(a in E) P a.
(*Definition Pr (E : pred A) := \rsum_(a in A | E a) P a.*)

(** Basic properties about probabilities *)

Lemma le_0_Pr E : 0 <= Pr E.
Proof.
apply sumr_ge0 => *; by apply Rle0f. Qed.



Lemma Pr_1 E : Pr E <= 1.
Proof.
rewrite -(pmf1 P).
rewrite /Pr.
apply ler_sum_new => a // Ha.
by apply Rle0f. Qed.

Lemma Pr_ext E F : E :=: F -> Pr E = Pr F.
Proof. move=> H; apply eq_bigl => x; by rewrite H. Qed.
(*Lemma Pr_ext E F : E =1 F -> Pr E = Pr F.
Proof. move=> H; apply eq_bigl => x; by rewrite H. Qed.*)

Lemma Pr_0 : Pr set0(*pred0*) = 0.
Proof. (*by rewrite /Pr big_pred0_eq.*)
rewrite /Pr big_pred0 // => a; by rewrite in_set0.
Qed.

Lemma Pr_cplt E : Pr E + Pr (~: E)(*[predC E]*) = 1.
Proof. (*rewrite /Pr -(pmf1 P); symmetry. by rewrite (bigID E).*)
rewrite /Pr -bigU /=; last by rewrite -subsets_disjoint.
rewrite -(pmf1 P); apply eq_bigl => /= a.
by rewrite !inE /= orbN.
Qed.

(* begin hide *)
(*Lemma Pr_cplt' Q : Pr Q = 1 - Pr [predC Q].
Proof. rewrite -(Pr_cplt Q); field. Qed.*)
Lemma Pr_cplt' E : Pr E = 1 - Pr (~: E).
Proof.
rewrite -(Pr_cplt E).
by rewrite addrK. Qed.


Lemma Pr_cplt'' {B : finType} (f : A -> B) Q :
  Pr [set x | f x \in ~: Q] = 1 - Pr [set x | f x \in Q].
Proof.
rewrite Pr_cplt'.
f_equal.
f_equal.
apply eq_bigl => a /=.
by rewrite !inE negbK.
Qed.
(*Lemma Pr_cplt'' {B : finType} (f : A -> B) Q :
  Pr [pred x | f x \in ~: Q] = 1 - Pr [pred x | f x \in Q].
Proof.
rewrite -(Pr_cplt [pred x | f x \in Q]).
rewrite (_ : forall a b, a + b - a = b); last by move=> *; field.
apply eq_bigl => i; by rewrite !inE.
Qed.*)

(* end hide *)

(* NB: useless? *)
(*Lemma Pr_predU E1 E2 : Pr [predU E1 & E2] <= Pr E1 + Pr E2.
Proof. rewrite /Pr. apply Rle_big_predU_f. by apply Rle0f. Qed.*)

(* TODO: move to Rbigop.v *)
(*Lemma Rle_big_setU_f : (forall a, 0 <= f a) ->
  \rsum_(i in A | [predU P & Q] i) f i <=
  \rsum_(i in A | P i) f i + \rsum_(i in A | Q i) f i.
Proof.
move=> Hf.
elim: (index_enum _) => //.
- rewrite !big_nil /=; fourier.
- move=> h t IH /=.
  rewrite !big_cons /=.
  case: ifP => /=.
  + case/orP => [HP1 | HP2].
    * rewrite unfold_in in HP1.
      rewrite HP1.
      case: ifP => // HP2.
      - rewrite Rplus_assoc; apply Rplus_le_compat_l.
        eapply Rle_trans; first by apply IH.
        have : forall a b c, 0 <= c -> a + b <= a + (c + b) by move=> *; fourier.
        apply.
        by apply Hf.
      - rewrite Rplus_assoc; apply Rplus_le_compat_l.
        eapply Rle_trans; first by apply IH.
        by apply Req_le.
    * rewrite unfold_in in HP2.
      rewrite HP2.
      case: ifP => // HP1.
      - rewrite Rplus_assoc; apply Rplus_le_compat_l.
        eapply Rle_trans; first by apply IH.
        have : forall a b c, 0 <= c -> a + b <= a + (c + b) by move=> *; fourier.
        apply.
        by apply Hf.
      - rewrite -(Rplus_comm (f h + _)) Rplus_assoc; apply Rplus_le_compat_l.
        eapply Rle_trans; first by apply IH.
        by rewrite Rplus_comm; apply Req_le.
  + move/negbT.
    rewrite negb_or.
    case/andP.
    rewrite unfold_in; move/negbTE => ->.
    rewrite unfold_in; move/negbTE => ->.
    by apply IH.
Qed.*)

Lemma Pr_union E1 E2 : Pr (E1 :|: E2) <= Pr E1 + Pr E2.
Proof.
rewrite /Pr.
rewrite (_ : \sum_(i in A | [pred x in E1 :|: E2] i) P i =
  \sum_(i in A | [predU E1 & E2] i) P i); last first.
  apply eq_bigl => x /=; by rewrite inE.
rewrite (_ : \sum_(i in A | [pred x in E1] i) P i =
  \sum_(i in A | pred_of_set E1 i) P i); last first.
  apply eq_bigl => x /=; by rewrite unfold_in.
rewrite (_ : \sum_(i in A | [pred x in E2] i) P i =
  \sum_(i in A | pred_of_set E2 i) P i); last first.
  apply eq_bigl => x /=; by rewrite unfold_in.
by apply new_Rle_big_predU_f

, Rle0f.
Qed.

(*Lemma Pr_union E1 E2 : Pr [pred x in E1 :|: E2] <= Pr [pred y in E1] + Pr [pred y in E2].
Proof.
rewrite /Pr.
rewrite (_ : \rsum_(i in A | [pred x in E1 :|: E2] i) P i =
  \rsum_(i in A | [predU E1 & E2] i) P i); last first.
  apply eq_bigl => x /=; by rewrite inE.
rewrite (_ : \rsum_(i in A | [pred x in E1] i) P i =
  \rsum_(i in A | pred_of_set E1 i) P i); last first.
  apply eq_bigl => x /=; by rewrite unfold_in.
rewrite (_ : \rsum_(i in A | [pred x in E2] i) P i =
  \rsum_(i in A | pred_of_set E2 i) P i); last first.
  apply eq_bigl => x /=; by rewrite unfold_in.
by apply Rle_big_predU_f, Rle0f.
Qed.*)

Lemma Pr_union_disj E1 E2 :
  E1 :&: E2 = set0 (*TODO: use disjoint?*) ->
  Pr (E1 :|: E2) = Pr E1 + Pr E2.
Proof.
move=> E1E2.
rewrite -bigU /=; last by rewrite -setI_eq0; apply/eqP.
apply eq_bigl => a /=; by rewrite !inE.
Qed.

Lemma Pr_incl (E E' : {set A}) : (E \subset E') -> Pr E <= Pr E'.
Proof. move=> H.
apply ler_sum_new => //.
move=> *; by apply Rle0f.
by apply/subsetP. Qed.

(* TODO: rename *)
Lemma Pr_bigcup2 (B : finType) (E : pred B) F :
  Pr (\bigcup_(i | E i) F i) <= \sum_(i | E i) Pr (F i).
Proof.
rewrite /Pr.
elim: (index_enum _) => [| hd tl IH].
  rewrite big_nil.
  apply sumr_ge0 => i Hi.
  by rewrite big_nil.
rewrite big_cons.
case: ifP => H1.
  move: IH.
  set lhs := \sum_(_ <- _ | _) _.
  move=> IH.
  apply ler_trans with (P hd + \sum_(i | E i) \sum_(a <- tl | a \in F i) P a).
    by rewrite ler_add //.
  rewrite [X in _ <= X](exchange_big_dep (fun hd => (hd \in A) && [pred x in \bigcup_(i | E i) F i] hd)) /=; last first.
    move=> i j Pi Fj; apply/bigcupP; by exists i.
  rewrite big_cons /=.
  rewrite H1(*2*) big_const iter_add_mul -exchange_big_dep //; last first.
    move=> i j Pi Fj; apply/bigcupP; by exists i.
  rewrite ler_add //.
  set inr := ( _ )%:R.
  suff H : 1 <= inr.
    rewrite -{1}(mul1r (P hd)).
    rewrite ler_pmul //.
    by rewrite ler01.
    by apply Rle0f.
  rewrite /inr {inr} (_ : 1 = (1)%:R) //.
  rewrite ler1n.
  apply/card_gt0P.
  case/bigcupP : H1(*2*) => h2 H1(*2*) H1'(*2'*).
  exists h2.
  by rewrite -topredE /= H1(*2*).
eapply ler_trans; first by apply IH.
apply ler_sum => i Pi.
rewrite big_cons.
case: ifP => H2.
- set lhs := \sum_(_ <- _ | _) _.
  rewrite ler_addr.
  by apply Rle0f.
- done.
Qed.

End probability.

Section Pr_tuple_prod.

Variables A B : finType.
Variable n : nat.
Variable P : dist [finType of 'rV[A * B]_n].
Variable Q : {set [finType of 'rV[A * B]_n]}.

Lemma Pr_tuple_prod_cast : Pr (@dist_tuple_prod_cast A B n P) [set x | prod_rV x \in Q] =
  Pr P Q.
Proof.
rewrite /Pr.
rewrite (reindex_onto (fun x => rV_prod x) (fun y => prod_rV y)) /=; last first.
  move=> i _; by rewrite prod_rVK.
apply eq_big.
move=> i /=.
  by rewrite !inE rV_prodK eqxx andbC.
move=> i /= Hi; by rewrite rV_prodK.
Qed.

End Pr_tuple_prod.

(** * Random Variable *)

(** Definition of a random variable (#R#%$\mathbb{R}$%-valued) with a distribution: *)

Record rvar A := mkRvar {rv_dist : dist A ; rv_fun :> A -> R }.

Notation "`p_ X" := (rv_dist X) (at level 5) : proba_scope.

(** Probability that a random variable evaluates to #r \in R#%$r \in \mathbb{R}$%:*)

Section pr_def.

Variable A : finType.

(*Definition pr (X : rvar A) r := Pr `p_X [pred x | X x == r].*)
Definition pr (X : rvar A) r := Pr `p_X [set x | X x == r].

End pr_def.

Notation "'Pr[' X '=' r ']'" := (pr X r) (at level 5, X at next level, r at next level) : proba_scope.

(** Some changes of variables: *)

Definition scale_rv A k (X : rvar A) :=
  mkRvar `p_X (fun x => k * X x).
Definition add_rv A (X Y : rvar A) (H : `p_X = `p_Y) :=
  mkRvar `p_X (fun x => X x + Y x).
Definition sub_rv A (X Y : rvar A) (H : `p_X = `p_Y) :=
  mkRvar `p_X (fun x => X x - Y x).
Definition trans_add_rv A (X : rvar A) m :=
  mkRvar `p_X (fun x => X x + m).
Definition trans_min_rv A (X : rvar A) m :=
  mkRvar `p_X (fun x => X x - m).
Definition const_rv A cst (X : rvar A) :=
  mkRvar `p_X (fun _ => cst).
Definition comp_rv A (X : rvar A) f :=
  mkRvar `p_X (fun x => f (X x)).
Definition sq_rv A (X : rvar A) := comp_rv X (fun x => x ^+ 2).

Notation "k \cst* X" := (@scale_rv _ k X) (at level 49).
Notation "X ''/' n" := (@scale_rv _ (1 / ( n )%:R) X) (at level 49, format "X  ''/'  n").
Notation "X \+_( H ) Y" := (@add_rv _ X Y H) (at level 50).
Notation "X \-_( H ) Y" := (@sub_rv _ X Y H) (at level 50).
Notation "X '\+cst' m" := (trans_add_rv X m) (at level 50).
Notation "X '\-cst' m" := (trans_min_rv X m) (at level 50).
Notation "X '^^2' " := (sq_rv X) (at level 49).

(** The ``- log P'' random variable: *)

Axiom log : R -> R.

Definition mlog_rv A (P : dist A) : rvar A := mkRvar P (fun x => - log (P x)).

Notation "'--log' P" := (mlog_rv P) (at level 5) : proba_scope.

(** Cast operation: *)

Lemma rvar2tuple1 : forall A, rvar A -> rvar [finType of 1.-tuple A].
Proof.
move=> A [d f]; apply mkRvar.
- exact (d `^ 1).
- exact (fun x => f (thead x)).
Defined.

Definition cast_rv A : 1.-tuple (rvar A) -> rvar [finType of 1.-tuple A].
move=> t.
exact (rvar2tuple1 (tnth t ord0)).
Defined.

Definition img (A : finType) (f : A -> R) :=
  undup (map f (enum A)).

(** Switching from a sum on the domain to a sum on the image of function *)

Section sum_dom_codom.

Variable A : finType.

Lemma sum_parti (p : seq A) (X : A -> R) : forall (F : A -> R), uniq p ->
  \sum_(i <- p) (F i) =
  \sum_(r <- undup (map X p)) \sum_(i <- p | X i == r) (F i).
Proof.
move Hn : (undup (map X (p))) => n.
move: n p X Hn.
elim => [p X HA F Hp | h t IH p X H F Hp].
- rewrite big_nil.
  suff : p = [::] by move=> ->; rewrite big_nil.
  move/undup_nil_inv : HA => /(congr1 size) /=; rewrite size_map.
  by move/eqP; rewrite size_eq0 => /eqP.
- rewrite big_cons.
  have [preh [pret [H1 [H2 H3]]]] : exists preh pret,
    perm_eq p (preh ++ pret) /\ undup (map X preh) = [:: h] /\ undup (map X pret) = t.
    by apply undup_perm.
  apply trans_eq with (\sum_(i <- preh ++ pret) F i).
    by apply: eq_big_perm.
  apply trans_eq with
   (\sum_(i <- preh ++ pret | X i == h) F i +
   \sum_(j <- t) \sum_(i <- preh ++ pret | X i == j) F i); last first.
    f_equal.
    apply: eq_big_perm.
      by rewrite perm_eq_sym.
    apply eq_bigr => i _ /=.
    apply: eq_big_perm.
    by rewrite perm_eq_sym.
  have -> :
    \sum_(j <- t) \sum_(i <- (preh ++ pret) | X i == j) F i =
    \sum_(j <- t) \sum_(i <- pret | X i == j) F i.
    rewrite big_seq_cond.
    symmetry.
    rewrite big_seq_cond /=.
    apply eq_bigr => i Hi.
    rewrite big_cat /=.
    have -> : \sum_(i0 <- preh | X i0 == i) F i0 = 0.
      transitivity (\sum_(i0 <- preh | false) F i0).
      rewrite big_seq_cond.
      apply eq_bigl => /= j.
      apply/negP.
      case/andP; move=> Xj_i; move/eqP=> j_preh.
      subst i.
      have Xj_h : X j \in [:: h].
        have H4 : X j \in map X preh by apply/mapP; exists j.
        have H5 : X j \in undup (map X preh)  by rewrite mem_undup.
        by rewrite H2 in H5.
      have : uniq (h :: t).
        rewrite -H.
        apply undup_uniq.
        rewrite /= in_cons in_nil orbC /= in Xj_h.
        move/eqP : Xj_h => Xj_h.
        subst h.
        rewrite andbC /= in Hi.
        by rewrite /= Hi.
      by rewrite big_pred0.
      by rewrite add0r.
  rewrite -IH //; last first.
    have : uniq (preh ++ pret) by rewrite -(@perm_eq_uniq _ _ _ H1).
    rewrite cat_uniq.
    case/andP => _; by case/andP.
  have -> : \sum_(i <- (preh ++ pret) | X i == h) F i =
    \sum_(i <- preh) F i.
    rewrite big_cat /=.
    have -> : \sum_(i <- pret | X i == h) F i = 0.
      transitivity (\sum_(i0 <- pret | false) F i0); last first.
        by rewrite big_pred0.
      rewrite big_seq_cond.
      apply eq_bigl => /= j.
      apply/negP.
      case/andP; move => j_pret; move/eqP => Xj_h.
      subst h.
      have Xj_t : X j \in t.
        have H4 : X j \in map X pret.
        apply/mapP; by exists j.
        have H5 : X j \in undup (map X pret).
        by rewrite mem_undup.
        by rewrite H3 in H5.
      have : uniq (X j :: t).
        rewrite -H.
        by apply undup_uniq.
      by rewrite /= Xj_t.
    rewrite addr0 big_seq_cond /=.
    symmetry.
    rewrite big_seq_cond /=.
    apply congr_big => //= x.
    case/orP : (orbN (x \in preh)) => Y.
    + rewrite Y /=.
      symmetry.
      have : X x \in [:: h].
        rewrite -H2 mem_undup.
        apply/mapP.
        by exists x.
      by rewrite in_cons /= in_nil orbC.
    + by rewrite (negbTE Y) andbC.
  by rewrite big_cat.
Qed.

Lemma sum_parti_finType (X : A -> R) (F : A -> R):
   \sum_(i in A) (F i) =
   \sum_(r <- undup (map X (enum A))) \sum_(i in A | X i == r) (F i).
Proof.
move: (@sum_parti (enum A) X F) => /=.
rewrite enum_uniq.
move/(_ (refl_equal _)) => IH.
transitivity (\sum_(i <- enum A) F i).
  apply congr_big => //.
  by rewrite enumT.
rewrite IH.
apply eq_bigr => i _.
apply congr_big => //.
by rewrite enumT.
Qed.

End sum_dom_codom.

(** * Expected Value *)

Section expected_value_definition.

Variable A : finType.
Variable X : rvar A.

(** Expected value of a random variable: *)

Definition Ex := \sum_(r <- img X) r * Pr[ X = r ].

(** Alternative (simpler) definition of the expected value: *)

Definition Ex_alt := \sum_(a in A) X a * `p_X a.

Lemma Ex_Ex_alt : Ex = Ex_alt.
Proof.
rewrite /Ex /Pr.
transitivity (\sum_(r <- img X) \sum_(i in A | X i == r) (X i * `p_X i)).
  apply eq_bigr => r _.
  rewrite big_distrr /=.
  apply congr_big => //= a.
  by rewrite inE.
  by rewrite inE; move/eqP => ->.
by rewrite /img -sum_parti_finType.
Qed.

Lemma Ex_alt_pos : (forall a, 0 <= X a) -> 0 <= Ex_alt.
Proof.
move=> HZ.
rewrite /Ex_alt.
apply sumr_ge0 => a _.
apply mulr_ge0 => //.
by apply Rle0f.
Qed.

End expected_value_definition.

Notation "'`E'" := (Ex_alt) (at level 5) : proba_scope.

Section expected_value_for_standard_random_variables.

Variable A : finType.
Variables X Y : rvar A.

(** Properties of the expected value of standard random variables: *)

Lemma E_scale k : `E (k \cst* X) = k * `E X.
Proof.
rewrite /scale_rv /Ex_alt /= big_distrr /=.
apply eq_bigr => i Hi; by rewrite mulrA.
Qed.

Lemma E_num_int_add (H : `p_X = `p_Y) : `E (X \+_(H) Y) = `E X + `E Y.
Proof.
rewrite /Ex_alt -big_split /=.
apply eq_bigr => i i_A /=.
by rewrite mulrDl H.
Qed.

Lemma E_num_int_sub (H : `p_X = `p_Y) : `E (X \-_(H) Y) = `E X - `E Y.
Proof.
rewrite (_ : `E X - `E Y = `E X + - 1 * `E Y); last by rewrite mulN1r.
rewrite {3}/Ex_alt  big_distrr /= -big_split /= /Ex_alt.
apply eq_bigr => i i_A /=; rewrite H.
by rewrite mulrDl mulN1r mulNr.
Qed.

Lemma E_const k : `E (const_rv k X) = k.
Proof. by rewrite /Ex_alt /= -big_distrr /= pmf1 mulr1. Qed.

Lemma E_trans_add_rv m : `E (X \+cst m) = `E X + m.
Proof.
rewrite /Ex_alt /trans_add_rv /=.
transitivity (\sum_(i in A) (X i * `p_X i + m * `p_X i)).
  apply eq_bigr => i Hi /=. by rewrite mulrDl.
by rewrite big_split /= -big_distrr /= pmf1 mulr1.
Qed.

Lemma E_trans_id_rem m :
  `E ( (X \-cst m) ^^2) = `E (X^^2 \-_( Logic.eq_refl ) (2%:R * m \cst* X) \+cst m ^+ 2).
Proof. rewrite /Ex_alt /=; apply eq_bigr => i Hi.
f_equal.
rewrite sqrrB.
do 2 f_equal.
rewrite mulr_natl.
rewrite mulrnAl.
by rewrite (mulrC m).
(* TODO: this was a field step, bien pratique pour faire des developements *)
Qed.

Lemma E_comp f k : (forall x y, f (x * y) = f x * f y) ->
  `E (comp_rv (k \cst* X) f) = `E (f k \cst* (comp_rv X f)).
Proof.
move=> H; rewrite /comp_rv /= /Ex_alt /=.
apply eq_bigr => i i_in_A; rewrite H.
done.
Qed.

Lemma E_comp_rv_ext f : `p_X = `p_Y -> rv_fun X = rv_fun Y ->
  `E (comp_rv X f) = `E (comp_rv Y f).
Proof. move=> H1 H2; by rewrite /Ex_alt /comp_rv /= H1 H2. Qed.

End expected_value_for_standard_random_variables.

Lemma E_rvar2tuple1 A : forall (X : rvar A), `E (rvar2tuple1 X) = `E X.
Proof.
case=> d f.
rewrite /Ex_alt /rvar2tuple1 /=.
apply: sum_1_tuple => // i.
by rewrite -tuple_pmf_singleton.
Qed.

(** * Variance *)

Section variance_definition.

Variable A : finType.
Variable X : rvar A.

(** Variance of a random variable %($\sigma^2(X) = V(X) = E (X^2) - (E X)^2$)%: *)

Definition Var := let miu := `E X in `E ((X \-cst miu)^^2).

(** Alternative form for computing the variance
   %($V(X) = E(X^2) - E(X)^2$ \cite[Theorem 6.6]{probook})%: *)

Lemma V_alt : Var = `E (X ^^2)  - (`E X) ^+ 2.
Proof. rewrite /Var E_trans_id_rem E_trans_add_rv E_num_int_sub E_scale.
rewrite -addrA.
f_equal.
rewrite mulr_natl.
rewrite mulrnAl.
rewrite -expr2.
rewrite -mulNrn.
rewrite mulr2n.
by rewrite subrK.
(* TODO: was happily solved by field*)
Qed.

End variance_definition.

Notation "'`V'" := (Var) (at level 5) : proba_scope.

Section variance_properties.

Variable A : finType.
Variable X : rvar A.

(** The variance is not linear %$V (k X) = k^2 V (X)$ \cite[Theorem 6.7]{probook}%: *)

Lemma V_scale k : `V (k \cst* X) = k ^+ 2 * `V X.
Proof.
rewrite {1}/`V [in X in X = _]/= E_scale.
rewrite (@E_comp_rv_ext _ ((k \cst* X) \-cst k * `E X) (k \cst* (X \+cst - `E X))) //; last first.
  rewrite /=; apply FunctionalExtensionality.functional_extensionality => x.
  rewrite mulrDr.
  f_equal.
  rewrite mulrC.
  rewrite -mulNr.
  by rewrite mulrC.
rewrite E_comp; last first.
  move=> x y.
  rewrite !expr2.
  rewrite !mulrA.
  f_equal.
  rewrite mulrC.
  by rewrite mulrA.
by rewrite E_scale.
Qed.

End variance_properties.

Lemma V_rvar2tuple1 A : forall (X : rvar A), `V (rvar2tuple1 X) = `V X.
Proof.
case=> d f.
rewrite /`V !E_rvar2tuple1 /Ex_alt /=.
apply: sum_1_tuple => // i.
rewrite /tuple_pmf big_ord_recl /= big_ord0.
rewrite mulr1.
by rewrite -tuple_pmf_singleton //.
Qed.

(** * Chebyshev's Inequality *)

(** (Probabilistic statement.)
 In any data sample, "nearly all" the values are "close to" the mean value:
 %$Pr[ |X - E X| \geq \epsilon] \leq V(X) / \epsilon^2$% *)

Section chebyshev.

Variable A : finType.
Variable X : rvar A.

(*Lemma chebyshev_inequality epsilon : 0 < epsilon ->
  Pr `p_X [pred a | Rabs (X a - `E X) >b= epsilon] <= `V X / epsilon ^ 2.*)
Lemma chebyshev_inequality epsilon : 0 < epsilon ->
  Pr `p_X [set a | `| X a - `E X | >= epsilon] <= `V X / epsilon ^+ 2.
Proof.
move=> He.
rewrite -(ler_pmul2l (exprn_gt0 2 He)).
(*apply (Rmult_le_reg_l _ _ _ (pow_gt0 He 2)).*)
rewrite [in X in _ <= X]mulrC.
rewrite -[in X in _ <= X]mulrA mulVr; last first.
  apply unitrX.
  by apply unitf_gt0.
rewrite mulr1.
(* /Rdiv (Rmult_assoc _ (/ epsilon ^+ 2) (epsilon ^ 2)) -Rinv_l_sym; [rewrite Rmult_1_r | by apply Rgt_not_eq, pow_gt0].*)
rewrite /`V {2}/Ex_alt.
rewrite (_ : `p_ ((X \-cst `E X)^^2) = `p_ X) //.
apply ler_trans with (\sum_(a in A | `| X a - `E X | >= epsilon)
    (((X \-cst `E X)^^2) a  * `p_X a)); last first.
  apply ler_sum_new => a // _.
  apply mulr_ge0; last by apply Rle0f.
  by apply sqr_ge0.
rewrite /Pr big_distrr [_ ^^2]lock /= -!lock.
apply ler_sum_new => a // Ha.
(*apply Rle_big_P_Q_f_g => // i Hi; rewrite /= -!/(_ ^ 2).*)
- rewrite ler_pmul //.
  by apply sqr_ge0.
  by apply Rle0f.
  rewrite inE in Ha.
  simpl.
  rewrite -[in X in _ <= X]real_normK; last first.
    by apply num_real.
  rewrite ler_pmul //.
  by apply ltrW.
  by apply ltrW.
  apply mulr_ge0 => /=.
  by apply sqr_ge0.
  by apply Rle0f.
- by rewrite inE in Ha.
Qed.

End chebyshev.

(** * Joint Distribution *)

Section joint_dist.

Variable A : finType.
Variable P1 : dist A.
Variable n : nat.
Variable P2 : dist [finType of n.-tuple A].
Variable P : dist [finType of n.+1.-tuple A].

Definition joint :=
  (forall x, P1 x = \sum_(t in {:n.+1.-tuple A} | thead t == x) P t) /\
  (forall x, P2 x = \sum_(t in {:n.+1.-tuple A} | behead t == x) P t).

End joint_dist.

Lemma big_behead_head {A : finType} n (F : n.+1.-tuple A -> R) (i : A) :
  \sum_(j in {: n.-tuple A}) (F [tuple of (i :: j)]) =
  \sum_(p in {: n.+1.-tuple A} | thead p == i) (F p).
Proof.
symmetry.
rewrite (reindex_onto (fun j : {: n.-tuple A} => [tuple of (i :: j)])
  (fun p => tbehead p)) /=; last first.
  move=> ij /eqP => <-; by rewrite -tuple_eta.
apply eq_bigl => /= x.
rewrite inE /= theadE eqxx /=.
apply/eqP.
rewrite tupleE /behead_tuple /=.
by apply val_inj.
Qed.

Lemma sum_0tuple {A : finType} (F : _ -> R) Q :
  \sum_( j in {:0.-tuple A} | Q j) F j = if Q [tuple] then F [tuple] else 0.
Proof.
rewrite -big_map /= /index_enum -enumT (_ : enum (tuple_finType 0 A) = [tuple] :: [::]).
by rewrite /= big_cons big_nil addr0.
apply eq_from_nth with [tuple] => /=.
by rewrite size_tuple card_tuple.
move=> i.
rewrite size_tuple card_tuple expn0.
destruct i => //= _.
set xx := enum _ .
destruct xx => //.
destruct s.
apply val_inj => /=.
by destruct tval.
Qed.

Lemma big_head_big_behead {A : finType} n (F : n.+1.-tuple A -> R) (j : {:n.-tuple A}) :
  \sum_(i in A ) (F [tuple of (i :: j)]) =
  \sum_(p in {:n.+1.-tuple A} | behead p == j) (F p).
Proof.
symmetry.
rewrite (reindex_onto (fun p : A => [tuple of (p :: j)])
  (fun p : {:n.+1.-tuple A} => thead p) ) /=; last first.
  case/tupleP => hd tl /=; move/eqP => tl_i.
  rewrite !tupleE.
  f_equal.
  by apply val_inj.
apply eq_bigl => /= x.
by rewrite inE /= theadE eqxx /= eqxx.
Qed.

(* begin hide *)
Lemma joint_prod_n_base_case A (P : dist A) : joint P (P `^ O) (P `^ 1).
Proof.
rewrite /joint; split => x.
- rewrite -big_behead_head /= sum_0tuple /= /tuple_pmf /=.
  by rewrite big_ord_recl /= big_ord0 mulr1 tnth0.
- rewrite /= (tuple0 x) /=.
  transitivity (\sum_(i in A) (tuple_pmf P [tuple of [:: i ]]));
    last by apply: big_head_big_behead.
  rewrite /tuple_pmf big_ord0 -[X in X = _](pmf1 (P `^ 1)).
  apply: sum_1_tuple => //= i.
  by rewrite thead_tuple1.
Qed.
(* end hide *)

(** The tuple distribution is a joint distribution: *)

Lemma joint_prod_n : forall n A (P : dist A), joint P (P `^ n) (P `^ n.+1).
Proof.
case; first by apply joint_prod_n_base_case.
move=> n B d; split => x.
- transitivity (\sum_(i in tuple_finType (n.+1) B) (d `^ n.+1) i * d x).
    by rewrite -big_distrl /= (pmf1 (d `^ n.+1)) mul1r.
  rewrite -big_behead_head.
  apply eq_bigr => i Hi.
  rewrite /tuple_dist /tuple_pmf /= [in X in _ = X]big_ord_recl tnth0 mulrC; f_equal.
  apply eq_bigr => i0 _; f_equal.
  by rewrite !(tnth_nth x).
- rewrite -big_head_big_behead.
  transitivity (\sum_(i in B) d i * (d `^ n.+1 x)).
    by rewrite -big_distrl /= (pmf1 d) mul1r.
  apply eq_bigr => i _ /=.
  rewrite /tuple_pmf [in X in _ = X]big_ord_recl tnth0; f_equal.
  apply eq_bigr => j _; by rewrite 2!(tnth_nth i).
Qed.

(** * Identically Distributed Random Variables *)

Section identically_distributed.

Variable A : finType.
Variable P : dist A.
Variable n : nat.

(** The random variables %$Xs$%#Xs# are identically distributed with distribution %$P$%#P#: *)

Definition id_dist (Xs : n.-tuple (rvar A)) := forall i, `p_(Xs\_i) = P.

End identically_distributed.

(** * Independent random variables *)

Section independent_random_variables.

Variable A : finType.
Variable X : rvar A.
Variable n : nat.
Variable Y : rvar [finType of n.-tuple A].
Variable P : dist [finType of n.+1.-tuple A].

Definition inde_rv := forall x y,
  Pr P [set xy | (X (thead xy) == x) && (Y (tbehead xy) == y)] =
  Pr[X = x] * Pr[Y = y].

End independent_random_variables.

Notation "X _| P |_ Y" := (inde_rv X Y P) (at level 50) : proba_scope.

(** Independent random variables over the tuple distribution: *)

Lemma big_head_behead_P_new {A : finType} n (F : n.+1.-tuple A -> R) (P1 : {set A}) (P2 : {set {: n.-tuple A}}) :
  \sum_(i in P1) \sum_(j in P2) (F [tuple of (i :: j)])
  =
  \sum_(p | (thead p \in P1) && (tbehead p \in P2)) (F p).
Proof.
symmetry.
rewrite (@partition_big _ _ _ _ _ _ (fun x : {: n.+1.-tuple A} => thead x)
  (fun x : A => x \in P1)) //=.
- apply eq_bigr => i Hi.
  rewrite (reindex_onto (fun j : {: n.-tuple A} => [tuple of (i :: j)])
    (fun p => [tuple of (behead p)])) /=; last first.
    move=> j Hj.
    case/andP : Hj => Hj1 /eqP => <-.
    symmetry.
    by apply tuple_eta.
  apply congr_big => // x /=.
  rewrite !theadE eqxx /= Hi /= -andbA /=.
  set tmp := _ == x.
  have Htmp : tmp = true.
    rewrite /tmp tupleE /behead_tuple /=.
    apply/eqP => /=.
    by apply val_inj.
  rewrite Htmp andbC /=.
  f_equal.
  by apply/eqP.
move=> i; by case/andP.
Qed.

(* TODO: clean *)
Lemma inde_rv_tuple_pmf_dist A (P : dist A) n (x y : R) (Xs : n.+2.-tuple (rvar A)) :
  id_dist P Xs ->
    Pr (P `^ n.+2) [set xy |
      (- log (P (thead xy)) == x) &&
      (\sum_(i : 'I_n.+1)
        - log (`p_ ((tbehead Xs)\_i) ((tbehead xy)\_i)) == y)] =
    Pr P [set a | - log (P a) == x] *
    Pr (P `^ n.+1) [set ta |
      \sum_(i : 'I_n.+1) - log (`p_ ((tbehead Xs)\_i) (ta\_i)) == y].
Proof.
move=> H.
rewrite /Pr.
move: (big_head_behead_P_new   (fun i : n.+2.-tuple A => tuple_pmf P i)
  [set a | - log (P a) == x]
  [set p | \sum_(i0 < n.+1 )
    - log (`p_ (tnth (tbehead Xs) i0) (tnth p i0)) == y]) => H'.
(* TODO: clean *)
eapply trans_eq.
  eapply trans_eq; last first.
    symmetry.
    by apply H'.
  apply eq_bigl => ta /=.
  by rewrite !inE.
transitivity (\sum_(i in [set i | - log (P i) == x])
  \sum_(j in [set j |
    \sum_(i0 <- index_enum (ordinal_finType n.+1))
    - log (`p_ (tnth (tbehead Xs) i0) (tnth j i0)) == y])
  P i * tuple_pmf P j).
  apply eq_bigr => i Hi.
  apply eq_bigr => j Hj.
  rewrite {1}/tuple_pmf /= big_ord_recl /= tnth0.
  f_equal.
  apply eq_bigr => i0 _; by rewrite !(tnth_nth i).
rewrite big_distrl /=.
apply eq_bigr => i Hi.
by rewrite -big_distrr /=.
Qed.

(** * Sum of Random Variables *)

(** The sum of two random variables: *)

Section sum_two_rand_var_def.

Variable A : finType.
Variable X1 : rvar A.
Variable n : nat.
Variable X2 : rvar [finType of n.+1.-tuple A].
Variable X : rvar [finType of n.+2.-tuple A].

Definition sum := joint `p_X1 `p_X2 `p_X /\
  X =1 fun x => X1 (thead x) + X2 (tbehead x).

End sum_two_rand_var_def.

Lemma big_head_behead_P {A : finType} n (F : n.+1.-tuple A -> R) (P1 : pred A) (P2 : pred ({: n.-tuple A})) :
  \sum_(i in A | P1 i) \sum_(j in {: n.-tuple A} | P2 j) (F [tuple of (i :: j)])
  =
  \sum_(p in {: n.+1.-tuple A} | (P1 (thead p)) && (P2 (tbehead p)) ) (F p).
Proof.
symmetry.
rewrite (@partition_big _ _ _ _ _ _ (fun x : {: n.+1.-tuple A} => thead x)
  (fun x : A => P1 x)) //=.
- apply eq_bigr => i Hi.
  rewrite (reindex_onto (fun j : {: n.-tuple A} => [tuple of (i :: j)])
    (fun p => [tuple of (behead p)])) /=; last first.
    move=> j Hj.
    case/andP : Hj => Hj1 /eqP => <-.
    symmetry.
    by apply tuple_eta.
  apply congr_big => // x /=.
  rewrite !theadE eqxx /= Hi /= -andbA /=.
  set tmp := _ == x.
  have Htmp : tmp = true.
    rewrite /tmp tupleE /behead_tuple /=.
    apply/eqP => /=.
    by apply val_inj.
  rewrite Htmp andbC /=.
  f_equal.
  by apply/eqP.
move=> i; by case/andP.
Qed.

Lemma big_head_behead {A : finType} n (F : n.+1.-tuple A -> R) :
  \sum_(i in A) \sum_(j in {: n.-tuple A}) (F [tuple of (i :: j)]) =
  \sum_(p in {: n.+1.-tuple A}) (F p).
Proof. by rewrite big_head_behead_P. Qed.

Notation "Z \= X `+ Y" := (sum X Y Z) (at level 50) : proba_scope.

Section sum_two_rand_var.

Variable A : finType.
Variable X1 : rvar A.
Variable n : nat.
Variable X2 : rvar [finType of n.+1.-tuple A].
Variable X : rvar [finType of n.+2.-tuple A].

(** The expected value of a sum is the sum of expected values,
   whether or not the summands are mutually independent
   (the ``First Fundamental Mystery of Probability''% \cite[Theorem 6.2]{probook}%): *)

Lemma E_linear_2 : X \= X1 `+ X2 -> `E X = `E X1 + `E X2.
Proof.
case=> Hjoint Hsum.
rewrite /Ex_alt /=.
transitivity (\sum_(i in tuple_finType n.+2 A)
  (X1 (thead i) * `p_X i + X2 [tuple of (behead i)] * `p_X i)).
- apply eq_bigr => i Hi; by rewrite Hsum mulrDl.
(*- apply eq_bigr => i Hi; by rewrite Hsum // ffunE Rmult_plus_distr_r.*)
- rewrite big_split => //=; f_equal.
  + transitivity (\sum_(i in A) (X1 i *
      \sum_(j in {:n.+1.-tuple A}) `p_X [tuple of (i :: j)])).
    * rewrite -big_head_behead.
      apply eq_bigr => i Hi; by rewrite big_distrr.
    * apply eq_bigr => i _.
      case: Hjoint.
      move/(_ i) => /= -> _.
      by rewrite big_behead_head.
  + transitivity (\sum_(i in {:n.+1.-tuple A}) (X2 i *
      \sum_(j in A) `p_X [tuple of (j :: i)])).
    * rewrite -(@big_head_behead _ (n.+1)) exchange_big /=.
      apply eq_bigr => ta _; rewrite big_distrr /=.
      apply eq_bigr => a _.
      do 2 f_equal.
      by apply val_inj.
    * apply eq_bigr => ta _.
      case: Hjoint => _.
      move/(_ ta) => /= ->.
      by rewrite -big_head_big_behead.
Qed.

(* TODO: relation with theorem 6.4 of probook (E(XY)=E(X)E(Y))? *)

Lemma E_id_rem_helper : X \= X1 `+ X2 -> X1 _| `p_X |_ X2 ->
  \sum_(i in {:n.+2.-tuple A})(X1 (thead i) * X2 (tbehead i) * `p_X i) =
    `E X1 * `E X2.
Proof.
case=> Hjoint Hsum Hinde.
rewrite -2!Ex_Ex_alt /=.
apply trans_eq with (\sum_(r <- undup (map X1 (enum A)))
   \sum_(r' <- undup (map X2 (enum (tuple_finType n.+1 A))))
   ( r * r' * Pr[ X1 = r] * Pr[ X2 = r' ])); last first.
  symmetry.
  rewrite big_distrl /=.
  apply eq_bigr => i _.
  rewrite big_distrr /=.
  apply eq_bigr => j _.
  rewrite mulrA.
  f_equal.
  rewrite -!mulrA.
  f_equal.
  by rewrite mulrC.
rewrite -big_head_behead.
apply trans_eq with (\sum_(i in A) \sum_(j in {: n.+1.-tuple A})
  (X1 i * X2 j * `p_X [tuple of i :: j])).
  apply eq_bigr => i Hi.
  apply eq_bigr => j Hj.
  rewrite theadE.
  do 3 f_equal.
  by apply val_inj.
rewrite (@sum_parti _ _ X1); last first.
  rewrite /index_enum -enumT; by apply enum_uniq.
rewrite /index_enum -enumT.
apply eq_bigr => i Hi.
rewrite {1}enumT exchange_big /= (@sum_parti _ _ X2); last first.
  rewrite /index_enum -enumT; by apply enum_uniq.
rewrite /index_enum -enumT.
apply eq_bigr => j Hj.
apply trans_eq with (i * j * \sum_(i0 | X2 i0 == j) \sum_(i1 | X1 i1 == i)
    (`p_X [tuple of i1 :: i0])).
  rewrite big_distrr /= /index_enum -!enumT.
  apply eq_bigr => k Hk.
  rewrite big_distrr /=.
  apply eq_bigr => l Hl.
  move/eqP : Hk => <-.
  by move/eqP : Hl => <-.
rewrite -!mulrA.
do 2 f_equal.
rewrite exchange_big /=.
move: {Hinde}(Hinde i j) => <-.
rewrite /Pr.
move: (big_head_behead_P_new (fun a => `p_ X a) [set j0 | X1 j0 == i] [set i0 | X2 i0 == j]) => H'.
eapply trans_eq.
  eapply trans_eq; last first.
    by apply H'.
  apply eq_big.
    move=> a /=.
    by rewrite inE.
  move=> a /eqP Ha.
  apply eq_bigl => ta /=.
  by rewrite inE.
apply eq_bigl => ta /=.
by rewrite !inE.
Qed.

(** Expected Value of the Square (requires mutual independence): *)

Lemma E_id_rem : X \= X1 `+ X2 -> X1 _| `p_X |_ X2 ->
  `E (X ^^2) = `E (X1 ^^2) + 2%:R * `E X1 * `E X2 + `E (X2 ^^2).
Proof.
case=> Hsum1 Hsum2 Hinde.
rewrite {1}/Ex_alt.
apply trans_eq with (\sum_(i in {:n.+2.-tuple A})
      ((X1 (thead i) + X2 (tbehead i)) ^+ 2%N * `p_X i)).
  apply eq_bigr => i _; by rewrite /sq_rv /= Hsum2.
apply trans_eq with (\sum_(i in {:n.+2.-tuple A})
      ((X1 (thead i)) ^+ 2 + 2%:R * X1 (thead i) * X2 (tbehead i) + (X2 (tbehead i)) ^+ 2) * `p_X i).
  apply eq_bigr => i _.
  rewrite sqrrD.
  do 3 f_equal.
  rewrite -mulrA.
  by rewrite mulr_natl.
apply trans_eq with (\sum_(i in {:n.+2.-tuple A})
      ((X1 (thead i)) ^+ 2 * `p_X i + 2%:R * (X1 (thead i) * X2 (tbehead i) * `p_X i) +
        (X2 (tbehead i)) ^+ 2 * `p_X i)).
  apply eq_bigr => i Hi.
  rewrite mulrDl.
  rewrite mulrDl.
  by rewrite !mulrA.
rewrite !big_split /=.
f_equal.
- f_equal.
  + rewrite /Ex_alt -big_head_behead /=.
    apply eq_bigr => i _.
    apply trans_eq with (X1 i ^+ 2 * \sum_(j in {:n.+1.-tuple A}) `p_X [tuple of i :: j]).
    * by rewrite big_distrr.
    * f_equal.
      case: Hsum1 => -> _.
      by apply big_behead_head.
  + rewrite -mulrA.
    rewrite mulr_natl.
    rewrite -(E_id_rem_helper (conj Hsum1 Hsum2)) //.
    rewrite -big_distrr /=.
    symmetry.
    rewrite mulr2n.
    rewrite mulr_natl.
    rewrite mulr2n.
    done.
- rewrite /Ex_alt -big_head_behead.
  rewrite exchange_big /=.
  apply eq_bigr => t _.
  apply trans_eq with (X2 t ^+ 2 * \sum_(i0 in A) (`p_X [tuple of i0 :: t])).
  + rewrite big_distrr.
    rewrite /=.
    apply eq_bigr => i0 Hi0.
    set lhs := tbehead _.
    suff : lhs = t by move=> ->.
    by apply val_inj.
  + f_equal.
    case: Hsum1 => _ ->.
    by apply big_head_big_behead.
Qed.

(** The variance of the sum is the sum of variances for any two
  independent random variables %(\cite[Theorem 6.8]{probook})%: *)

Lemma V_linear_2 : X \= X1 `+ X2 -> X1 _| `p_X |_ X2  -> `V X = `V X1 + `V X2.
Proof.
move=> Hsum Hinde.
rewrite !V_alt E_id_rem // (E_linear_2 Hsum).
rewrite -!addrA; f_equal.
rewrite addrC.
rewrite [in X in _ = X]addrC.
rewrite -!addrA; f_equal.
rewrite -opprB opprK.
rewrite addrC.
apply/eqP. rewrite subr_eq. apply/eqP.
rewrite sqrrD.
rewrite -addrA.
rewrite -[in X in _ = _ + X](addrC (`E X2 ^+ 2)).
rewrite 2!addrA.
apply/eqP. rewrite -subr_eq. apply/eqP.
rewrite -mulrA.
rewrite mulr_natl subrr.
rewrite -addrA.
rewrite -(addrC (`E X1 ^+ 2 + `E X2 ^+ 2)).
rewrite subrr.
done.
(* TODO: was happily solved by field *)
Qed.

End sum_two_rand_var.

Section sum_n_rand_var_def.

Variable A : finType.

(** The sum of #n >= 1#%$n \geq 1$% random variable(s): *)

Reserved Notation "X '\=sum' Xs" (at level 50).

Inductive sum_n : forall n,
  rvar [finType of n.-tuple A] -> n.-tuple (rvar A) -> Prop :=
| sum_n_1 : forall X, cast_rv X \=sum X
| sum_n_cons : forall n (Xs : n.+1.-tuple _) Y X Z,
  Y \=sum Xs -> Z \= X `+ Y -> Z \=sum [tuple of X :: Xs]
where "X '\=sum' Xs" := (sum_n X Xs) : proba_scope.

End sum_n_rand_var_def.

Notation "X '\=sum' Xs" := (sum_n X Xs) (at level 50) : proba_scope.

Section sum_n_rand_var.

Variable A : finType.

Lemma E_linear_n : forall n (Xs : n.-tuple (rvar A)) X,
  X \=sum Xs -> `E X = \sum_(i < n) `E Xs\_i.
Proof.
elim => [Xs Xbar | [_ Xs Xbar | n IHn Xs Xbar] ].
- by inversion 1.
- inversion 1; subst.
  apply Eqdep_dec.inj_pair2_eq_dec in H0; last first.
    by apply Peano_dec.eq_nat_dec.
  apply Eqdep_dec.inj_pair2_eq_dec in H1; last by apply Peano_dec.eq_nat_dec.
  subst Xs Xbar.
  rewrite big_ord_recl big_ord0 addr0 /cast_rv.
  by rewrite E_rvar2tuple1.
- inversion 1; subst.
  apply Eqdep_dec.inj_pair2_eq_dec in H1; last by apply Peano_dec.eq_nat_dec.
  apply Eqdep_dec.inj_pair2_eq_dec in H2; last by apply Peano_dec.eq_nat_dec.
  subst Z Xs.
  move: {IHn}(IHn _ _ H3) => IHn'.
  rewrite big_ord_recl.
  have -> : \sum_(i : 'I_n.+1) `E (tnth [tuple of X :: Xs0] (lift ord0 i)) =
       \sum_(i : 'I_n.+1) `E (tnth Xs0 i).
    apply eq_bigr => i _ /=.
    rewrite /`E /=.
    apply eq_bigr => a _ /=.
    suff : tnth [tuple of X :: Xs0] (lift ord0 i) = tnth Xs0 i by move=> ->.
    by rewrite !(tnth_nth X).
  by rewrite -IHn' (E_linear_2 H4).
Qed.

End sum_n_rand_var.

Section sum_n_independent_rand_var_def.

Variable A : finType.

(** The sum of #n >= 1#%$n \geq 1$% independent random variables: *)

Reserved Notation "X '\=isum' Xs" (at level 50).

Inductive isum_n : forall n,
  rvar [finType of n.-tuple A] -> n.-tuple (rvar A) -> Prop :=
| isum_n_1 : forall X, cast_rv X \=isum X
| isum_n_cons : forall n (Ys : n.+1.-tuple _) Y X Z,
  Y \=isum Ys -> Z \= X `+ Y -> X _| `p_Z |_ Y ->
  Z \=isum [tuple of X :: Ys]
where "X '\=isum' Xs" := (isum_n X Xs) : proba_scope.

End sum_n_independent_rand_var_def.

Notation "X '\=isum' Xs" := (isum_n X Xs) (at level 50) : proba_scope.

Section sum_n_independent_rand_var.

Variable A : finType.

Lemma sum_n_i_sum_n : forall n (Xs : n.-tuple (rvar A)) X,
  X \=isum Xs -> X \=sum Xs.
Proof.
move=> n Xs Xsum.
elim.
- move=> X; by constructor 1.
- move=> n0 lst Z W Z' H1 H2 H3 H4.
  by econstructor 2; eauto.
Qed.

Lemma V_linearity_isum : forall n
  (X : rvar [finType of n.-tuple A]) (Xs : n.-tuple (rvar A)),
  X \=isum Xs ->
  forall sigma2, (forall i, `V (tnth Xs i) = sigma2) ->
  `V X = ( n )%:R * sigma2.
Proof.
elim.
  move=> X Xs X_Xs sigma2 Hsigma2.
  by inversion X_Xs.
case=> [_ | n IH] Xsum Xs Hsum s Hs.
  inversion Hsum.
  apply Eqdep_dec.inj_pair2_eq_dec in H; last by apply Peano_dec.eq_nat_dec.
  apply Eqdep_dec.inj_pair2_eq_dec in H0; last by apply Peano_dec.eq_nat_dec.
  subst Xs Xsum.
  rewrite /cast_rv V_rvar2tuple1 /= mul1r.
  by apply Hs.
have {IH}IH : forall Xsum (Xs : (n.+1).-tuple (rvar A)),
  Xsum \=isum Xs ->
  forall sigma2, (forall i, `V (tnth Xs i) = sigma2) ->
    `V Xsum = (n.+1)%:R * sigma2 by apply IH.
move: Hsum; inversion 1.
apply Eqdep_dec.inj_pair2_eq_dec in H0; last by apply Peano_dec.eq_nat_dec.
apply Eqdep_dec.inj_pair2_eq_dec in H1; last by apply Peano_dec.eq_nat_dec.
subst Z n0 Xs.
move: {IH}(IH Y Ys H2) => IH.
rewrite -[in X in _ = X](addn1 n).
rewrite mulr_natl mulrS.
rewrite -mulr_natl addn1.
rewrite -IH //.
+ rewrite (@V_linear_2 _ _ _ _ _ H3) //.
  by rewrite -(Hs ord0) /= tnth0.
+ move=> i; rewrite -(Hs (lift ord0 i)).
  rewrite (_ : lift ord0 i = inord i.+1); last first.
    apply val_inj => /=.
    rewrite inordK //.
    move: (ltn_ord i) => i_n.
    by rewrite ltnS.
  rewrite -tnth_behead /=.
  do 2 f_equal.
  by apply val_inj.
Qed.

(** The variance of the average for independent random variables: *)

Lemma V_average_isum n (X : rvar [finType of n.-tuple A]) Xs (sum_Xs : X \=isum Xs) :
  forall sigma2, (forall i, `V (tnth Xs i) = sigma2) ->
  n%:R * `V (X '/ n) = sigma2.
Proof.
move=> s Hs.
destruct n.
  by inversion sum_Xs.
rewrite (V_scale X) // (V_linearity_isum sum_Xs Hs) //.
  (* TODO: was a field... *)
rewrite !mulrA.
rewrite !mulr1.
rewrite divff; last first.
  rewrite real_neqr_lt //; last first.
    by apply num_real.
    by apply num_real.
    by rewrite ltr0Sn orbC.
rewrite (mulrC (1 / _)).
rewrite div1r.
rewrite divff; last first.
  rewrite real_neqr_lt //; last first.
    by apply num_real.
    by apply num_real.
    by rewrite ltr0Sn orbC.
by rewrite mul1r.
Qed.

End sum_n_independent_rand_var.

(** * The Weak Law of Large Numbers *)

Section weak_law_of_large_numbers.

Variable A : finType.
Variable P : dist A.
Variable n : nat.
Variable Xs : n.+1.-tuple (rvar A). Hypothesis Xs_id : id_dist P Xs.
Variable miu : R.                   Hypothesis E_Xs : forall i, `E Xs\_i = miu.
Variable sigma2 : R.                Hypothesis V_Xs : forall i, `V Xs\_i = sigma2.
Variable X : rvar [finType of {:n.+1.-tuple A}].
Variable X_Xs : X \=isum Xs.

Lemma wlln epsilon : 0 < epsilon ->
  Pr `p_X [set t | `| (X '/ n.+1) t - miu | >= epsilon] <= sigma2 / ((n.+1)%:R * epsilon ^+ 2).
Proof.
move=> He.
have HV : `V (X '/ n.+1) = sigma2 / (n.+1)%:R.
  rewrite -(V_average_isum X_Xs V_Xs) V_scale //.
  rewrite 2!mulrA.
  rewrite [in X in _ = X]div1r.
  rewrite divff; last first.
    rewrite real_neqr_lt //; last first.
      by apply num_real.
      by apply num_real.
      by rewrite ltr0Sn orbC.
  rewrite expr2.
  rewrite -!mulrA.
  do 2 f_equal.
  rewrite mul1r.
  by rewrite -div1r mulrC.
rewrite (_ : sigma2 / (n.+1%:R * epsilon ^+ 2) = (sigma2 / n.+1%:R) * (1 / epsilon ^+ 2)); last first.
  rewrite mul1r.
  rewrite invfM.
  by rewrite mulrA.
(*rewrite /Rdiv Rinv_mult_distr; last 2 first.
  by apply not_0_INR.
  by apply Rgt_not_eq, pow_gt0.*)
(*rewrite (_ : sigma2 * n.+1%:R^-1 = sigma2 / n.+1%:R) //.*)
rewrite -{}HV.
have HE : `E (X '/ n.+1) = miu.
  rewrite E_scale (E_linear_n (sum_n_i_sum_n X_Xs)).
  set su := \sum_(_<-_) _.
  have -> : su = n.+1%:R * miu.
    rewrite /su.
    transitivity (\sum_(i < n.+1) miu).
      by apply eq_bigr.
    by rewrite big_const /= iter_add_mul cardE /= size_enum_ord.
  rewrite mulrA.
  rewrite (mulrC (1 / _)).
  rewrite mul1r.
  rewrite divff; last first.
    rewrite real_neqr_lt //; last first.
      by apply num_real.
      by apply num_real.
      by rewrite ltr0Sn orbC.
  by rewrite mul1r.
rewrite -{}HE.
have cheby : Pr `p_(X '/ n.+1)
  [set t | `| X t / n.+1%:R - `E (X '/ n.+1) | >= epsilon] <= `V (X '/ n.+1) / epsilon ^+ 2.
  move: (chebyshev_inequality (X '/ n.+1) He) => cheby.
  set g := [set _ | _] in cheby; rewrite (@Pr_ext _ _ _ g) //.
  apply/setP => x /=.
  rewrite !inE.
  simpl.
  rewrite mulrC.
  by rewrite mul1r.
set p1 := Pr _ _ in cheby. set p2 := Pr _ _.
suff : p2 = p1.
  move=> ->.
  by rewrite (mul1r ((epsilon ^+ 2) ^-1)).
apply Pr_ext.
apply/setP => ta /=; by rewrite !inE mulrC mul1r.
Qed.

End weak_law_of_large_numbers.
