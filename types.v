(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg perm zmodp matrix.
Require Import Reals Fourier FunctionalExtensionality ProofIrrelevance.
Require Import Reals_ext ssr_ext ssralg_ext Rssr log2 Rbigop proba entropy.
Require Import num_occ channel_code channel typ_seq.

Reserved Notation "'P_' n '(' A ')'" (at level 9, n, A at next level).
Reserved Notation "'T_{' P '}'" (at level 9).
Reserved Notation "P '.-typed_code' c" (at level 50, c at next level).

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope entropy_scope.
Local Open Scope num_occ_scope.

Module type.

Section type_def.

Variable A : finType.
Variable n : nat.

(** * Type definition *)

Record type : predArgType := mkType {
  d :> dist A ;
  f : {ffun A -> 'I_n.+1} ;
  d_f : forall a, d a = INR (f a) / INR n }.

End type_def.

End type.

Coercion type_coercion := type.d.

Notation "'P_' n '(' A ')'" := (type.type A n) : types_scope.

Local Open Scope types_scope.

Lemma type_fun_type A n (_ : n != O) (P : P_ n ( A )) a : INR ((type.f P) a) = INR n * P a.
Proof.
destruct P => /=; by rewrite d_f mulRCA mulRV ?INR_eq0 // mulR1.
Qed.

Lemma INR_type_fun A n (P : P_ n ( A )) a : INR ((type.f P) a) / INR n = P a.
Proof. destruct P as [d f d_f] => /=. by rewrite d_f. Qed.

Lemma no_0_type A (d : dist A) (t : {ffun A -> 'I_1}) :
  (forall a, d a = INR (t a) / INR 0) -> False.
Proof.
move=> H.
apply R1_neq_R0.
rewrite -(pmf1 d).
transitivity (\rsum_(a | a \in A) INR (t a) / 0); first by apply eq_bigr.
rewrite -big_distrl /= -(@big_morph _ _ _ 0 _ O _ morph_plus_INR) //.
rewrite (_ : \sum_(a in A) _ = O) ?mul0R //.
transitivity (\sum_(a in A) 0); first by apply eq_bigr => a _; rewrite (ord1 (t a)).
by rewrite big_const iter_addn.
Qed.

Definition type_of_tuple (A : finType) n (ta : n.+1.-tuple A) : P_ n.+1 ( A ).
set f := fun a => INR N(a | ta) / INR n.+1.
assert (H1 : forall a, (0 <= f a)%R).
  move=> a.
  rewrite /f.
  apply Rle_mult_inv_pos; by [apply pos_INR | apply lt_0_INR; apply/ltP].
assert (H2 : \rsum_(a in A) f a = 1%R).
  rewrite /f -big_distrl /= -(@big_morph _ _ _ 0 _ O _ morph_plus_INR) //.
  by rewrite sum_num_occ_alt mulRV // INR_eq0.
have H : forall a, (N(a | ta) < n.+2)%nat.
  move=> a; rewrite ltnS; by apply num_occ_leq_n.
refine (@type.mkType _ n.+1 (@mkDist _ (@mkPosFun _ f H1) H2)
  [ffun a => @Ordinal n.+2 (N(a | ta)) (H a)] _).
move=> a /=; by rewrite /f ffunE.
Defined.

Definition ffun_of_type A n (P : P_ n ( A )) := let: type.mkType _ f _ := P in f.

Lemma type_proj_eq A n (t1 t2 : P_ n ( A )) : type.f t1 = type.f t2 -> t1 = t2.
Proof.
case: t1 t2 => d1 f1 H1 /= [] d2 f2 H2 /= f1f2.
subst f2.
suff ? : d1 = d2.
  subst d2.
  f_equal.
  by apply proof_irrelevance.
apply dist_eq => /=.
apply pos_fun_eq => /=.
apply functional_extensionality => a /=.
by rewrite H1 H2.
Qed.

Definition type_eq A n (t1 t2 : P_ n ( A )) :=
  match t1, t2 with
    | type.mkType _ f1 _, type.mkType _ f2 _ => f1 == f2
  end.

Lemma type_eqP A n : Equality.axiom (@type_eq A n).
Proof.
case=> d1 f1 H1 [] d2 f2 H2 /=.
apply: (iffP idP).
- move/eqP => H; subst f2.
  suff ? : d1 = d2.
    subst d2.
    f_equal.
    by apply proof_irrelevance.
  apply dist_eq => /=.
  apply pos_fun_eq => /=.
  apply functional_extensionality => a.
  by rewrite H1 H2.
by case => _ ->.
Qed.

Definition type_eqMixin A n := EqMixin (@type_eqP A n).
Canonical type_eqType A n := Eval hnf in EqType _ (@type_eqMixin A n).

Lemma type_ffunP A n (P Q : P_ n.+1 ( A )) :
  (forall c, P c = Q c) -> P = Q.
Proof.
move=> H.
destruct P as [d1 f1 H1].
destruct Q as [d2 f2 H2].
rewrite /= in H.
apply/type_eqP => /=.
apply/eqP/ffunP => a.
apply/val_inj/INR_eq.
move: {H}(H a); rewrite H1 H2=> /Rmult_eq_reg_r; apply.
apply/eqP/invR_neq0; by rewrite INR_eq0.
Qed.

Definition pos_fun_of_ffun (A : finType) n (f : {ffun A -> 'I_n.+2}) : pos_fun A.
set d := fun a : A => INR (f a) / INR n.+1.
refine (@mkPosFun _ d _) => a.
apply Rle_mult_inv_pos; by [apply pos_INR  | apply lt_0_INR; apply/ltP].
Defined.

Definition dist_of_ffun (A : finType) n (f : {ffun A -> 'I_n.+2})
  (Hf : \sum_(a in A) f a == n.+1) : dist A.
set pf := pos_fun_of_ffun f.
assert (H : \rsum_(a in A) pf a = 1).
  rewrite /pf /= /Rdiv -big_distrl /= -(@big_morph _ _ _ 0 _ O _ morph_plus_INR) //.
  move/eqP : Hf => ->.
  by rewrite mulRV // INR_eq0.
exact (mkDist H).
Defined.

Lemma dist_of_ffun_prop (A : finType) n (f : {ffun A -> 'I_n.+2})
  (Hf : \sum_(a in A) f a == n.+1) :
forall a : A, (dist_of_ffun Hf) a = INR (f a) / INR n.+1.
Proof. by move=> a. Qed.

Definition type_choice_f (A : finType) n (f : {ffun A -> 'I_n.+1}) : option (P_ n ( A )).
destruct n; first by exact None.
refine (match Sumbool.sumbool_of_bool (\sum_(a in A) f a == n.+1) with
          | left H => Some (@type.mkType _ _ (dist_of_ffun H) f (dist_of_ffun_prop H))
          | right _ => None
        end).
Defined.

Lemma ffun_of_dist A n (d : dist A) (t : {ffun A -> 'I_n.+2})
  (H : forall a : A, d a = INR (t a) / INR n.+1) : \sum_(a in A) t a == n.+1.
Proof.
suff : INR (\sum_(a in A) t a) == INR n.+1 * \rsum_(a | a \in A) d a.
  move/eqP.
  rewrite (pmf1 d) mulR1.
  by move/INR_eq/eqP.
apply/eqP.
transitivity (INR n.+1 * (\rsum_(a|a \in A) INR (t a) / INR n.+1)).
  rewrite -big_distrl -(@big_morph _ _ _ 0 _ O _ morph_plus_INR) //.
  by rewrite mulRCA mulRV ?mulR1 // INR_eq0.
f_equal; exact/eq_bigr.
Qed.

Lemma type_choice_pcancel A n : pcancel (@type.f A n) (@type_choice_f A n).
Proof.
case=> d t H /=.
destruct n.
  by move: (no_0_type H).
rewrite /type_choice_f /=; f_equal.
move: (ffun_of_dist H) => H'.
destruct Sumbool.sumbool_of_bool as [e|e]; last first.
  by rewrite H' in e.
f_equal.
set d1 := dist_of_ffun _.
suff ? : d1 = d by subst d; f_equal; apply proof_irrelevance.
apply dist_eq => /=.
apply pos_fun_eq => /=.
apply functional_extensionality => a.
by rewrite H.
Qed.

Lemma type_choiceMixin A n : choiceMixin (P_ n ( A )).
Proof. apply (PcanChoiceMixin (@type_choice_pcancel A n)). Qed.

Canonical type_choiceType A n := Eval hnf in ChoiceType _ (type_choiceMixin A n).

Definition type_pickle A n (P : P_ n (A)) : nat.
destruct P as [d f H].
destruct (finfun_countMixin A [finType of 'I_n.+1]) as [pi unpi Hcan].
apply (pi f).
Defined.

Definition type_unpickle A n (m : nat) : option (P_ n ( A )).
destruct n.
  exact None.
case: (finfun_countMixin A [finType of 'I_n.+2]) => pi unpi Hcan.
case: (unpi m); last first.
  exact None.
move=> f.
refine (match Sumbool.sumbool_of_bool (\sum_(a in A) f a == n.+1) with
          | left H => Some (@type.mkType _ _ (dist_of_ffun H) f (dist_of_ffun_prop H))
          | right _ => None
        end).
Defined.

Lemma type_count_pcancel A n : pcancel (@type_pickle A n) (@type_unpickle A n).
Proof.
destruct n.
  case=> d t H /=; by move: (no_0_type H).
case=> d t H /=.
rewrite pcan_pickleK; last by apply valK.
move: (ffun_of_dist H) => H'.
destruct Sumbool.sumbool_of_bool as [e|e]; last first.
  by rewrite H' in e.
f_equal.
set d1 := dist_of_ffun _.
suff ? : d1 = d.
  subst d; f_equal; by apply proof_irrelevance.
apply dist_eq, pos_fun_eq, functional_extensionality => a.
by rewrite H.
Qed.

Definition type_countMixin A n := CountMixin (@type_count_pcancel A n).
Canonical type_countType A n :=
  Eval hnf in CountType (P_ n ( A )) (@type_countMixin A n).

Definition type_enum_f (A : finType) n (f : { f : {ffun A -> 'I_n.+1} | \sum_(a in A) f a == n} ) : option (P_ n ( A )).
destruct n.
  apply None.
refine (Some (@type.mkType _ _ (dist_of_ffun (proj2_sig f)) (sval f) (dist_of_ffun_prop (proj2_sig f)))).
Defined.

Definition type_enum A n := pmap (@type_enum_f A n)
  (enum [finType of {f : {ffun A -> 'I_n.+1} | \sum_(a in A) f a == n}]).

Lemma type_enumP A n : Finite.axiom (@type_enum A n).
Proof.
destruct n.
  case=> d t H /=; by move: (no_0_type H).
case=> d t H /=.
move: (ffun_of_dist H) => H'.
have : Finite.axiom (enum [finType of { f : {ffun A -> 'I_n.+2} | \sum_(a in A) f a == n.+1}]).
  rewrite enumT; by apply enumP.
move/(_ (@exist {ffun A -> 'I_n.+2} (fun f => \sum_(a in A) f a == n.+1) t H')) => <-.
rewrite /type_enum /= /type_enum_f /= count_map.
by apply eq_count.
Qed.

Definition type_finMixin A n := Eval hnf in FinMixin (@type_enumP A n).
Canonical type_finType A n := Eval hnf in FinType _ (@type_finMixin A n).

Section type_facts.

Variable A : finType.
Local Open Scope nat_scope.

(** Upper-bound of the number of types: *)

Lemma type_counting n : #| P_ n ( A ) | <= expn (n.+1) #|A|.
Proof.
rewrite -(card_ord n.+1) -card_ffun /=.
rewrite cardE /enum_mem.
apply (@leq_trans (size (map (@ffun_of_type A n) (Finite.enum (type_finType A n))))).
  by rewrite 2!size_map.
rewrite cardE.
apply uniq_leq_size.
  rewrite map_inj_uniq //.
    move: (enum_uniq (type_finType A n)).
    by rewrite enumT.
  case=> d f Hd [] d2 f2 Hd2 /= ?; subst f2.
  have ? : d = d2.
    apply dist_eq => /=. apply pos_fun_eq => /=. apply functional_extensionality => a.
    by rewrite Hd Hd2.
  subst d2.
  f_equal.
  by apply proof_irrelevance.
move=> /= f Hf.
by rewrite mem_enum.
Qed.

Lemma type_not_empty n : 0 < #|A| -> 0 < #|P_ n.+1(A)|.
Proof.
case/card_gt0P => a _.
apply/card_gt0P.
have [f Hf] : [finType of {f : {ffun A -> 'I_n.+2} | \sum_(a in A) f a == n.+1}].
  exists [ffun a1 => if pred1 a a1 then Ordinal (ltnSn n.+1) else Ordinal (ltn0Sn n.+1)].
  rewrite (bigD1 a) //= big1; first by rewrite ffunE eqxx addn0.
  move=> p /negbTE Hp; by rewrite ffunE Hp.
exists (@type.mkType _ _ (dist_of_ffun Hf) _ (dist_of_ffun_prop Hf)).
by rewrite inE.
Qed.

Lemma type_empty1 n : #|A|= 0 -> #|P_ n(A)| = 0.
Proof.
move=> A0; apply eq_card0; case=> d ? ?.
move: (dist_domain_not_empty d); by rewrite A0.
Qed.

Lemma type_empty2 : #|P_ 0(A)| = 0.
Proof.
apply eq_card0; case=> d f Hf.
exfalso.
by move/no_0_type in Hf.
Qed.

End type_facts.

Section typed_tuples.

Variable A : finType.
Variable n : nat.
Variable P : P_ n ( A ).

Local Open Scope nat_scope.

(** * Typed Tuples *)

(** Tuples that are representative of a type: *)

Definition typed_tuples :=
  [set t : n.-tuple A | [forall a, P a == (INR N(a | t) / INR n)%R] ].

End typed_tuples.

Notation "'T_{' P '}'" := (typed_tuples P) : types_scope.

Section typed_tuples_facts.

Variable A : finType.
Variable n' : nat.
Let n := n'.+1.
Variable P : P_ n ( A ).

Lemma type_numocc ta (Hta : ta \in T_{P}) a : N(a | ta) = type.f P a.
Proof.
move: Hta.
rewrite in_set.
move/forallP/(_ a)/eqP.
destruct P as [d f H] => /= Htmp.
apply/INR_eq/esym; move: Htmp.
rewrite H.
move/Rmult_eq_reg_r; apply.
apply/eqP/invR_neq0; by rewrite INR_eq0.
Qed.

Lemma typed_tuples_not_empty' : exists x : seq A,
  exists Hx : size x == n, Tuple Hx \in T_{P}.
Proof.
exists (flatten (map (fun x0 => nseq (type.f P x0) x0) (enum A))).
have Hx : size (flatten [seq nseq (type.f P x0) x0 | x0 <- enum A]) == n.
  rewrite size_flatten /shape -map_comp sumn_big_addn big_map.
  case: (P) => P' f HP' /=.
  apply/eqP.
  transitivity (\sum_(a in A) f a); last first.
     apply/eqP.
     by apply ffun_of_dist with P'.
  apply congr_big => //.
  by rewrite enumT.
  move=> a /= _.
  by rewrite size_nseq.
exists Hx.
rewrite inE.
apply/forallP => a.
rewrite /num_occ /= -size_filter.
rewrite filter_flatten size_flatten /shape -!map_comp sumn_big_addn big_map.
rewrite (bigD1 a) // big1 /= => [|a' Ha'].
- rewrite addn0 -(INR_type_fun P).
  apply/eqP.
  do 2 f_equal.
  rewrite -{1}(_ : size (nseq (type.f P a) a) = type.f P a); last by rewrite size_nseq.
  congr (size _).
  apply/esym/all_filterP/all_pred1P.
  by rewrite size_nseq.
- transitivity (size (@List.nil A)) => //.
  congr (size _).
  apply/eqP/negPn; rewrite -has_filter; apply/hasPn => l Hl.
  by case/nseqP : Hl => ->.
Qed.

Lemma typed_tuples_not_empty : { t | t \in T_{P} }.
Proof.
apply sigW.
case: typed_tuples_not_empty' => x [Hx H].
by exists (Tuple Hx).
Qed.

End typed_tuples_facts.

Section typed_tuples_facts_continued.

Variable A : finType.
Variable n : nat.
Hypothesis Hn : n != O.
Variable P : P_ n ( A ).

Lemma typed_tuples_not_empty_alt : {t : n.-tuple A | t \in T_{P}}.
Proof. destruct n => //. apply typed_tuples_not_empty. Qed.

Local Open Scope proba_scope.
Local Open Scope tuple_ext_scope.
Local Open Scope vec_ext_scope.

Lemma tuple_dist_type t : tuple_of_row t \in T_{P} ->
  P `^ n t = \rprod_(a : A) P a ^ (type.f P a).
Proof.
move=> Hx.
rewrite TupleDist.dE.
rewrite (_ : \rprod_(i < n) P (t ``_ i) =
  \rprod_(a : A) (\rprod_(i < n) (if a == t ``_ i then P t ``_ i else 1))); last first.
  rewrite exchange_big ; apply eq_big ; first done.
  move=> i _.
  rewrite (bigID (fun y => y == t ``_ i)) /=.
  rewrite -/(INR n.+1) big_pred1_eq eqxx big1 ?mulR1 //.
  by move=> i0 /negbTE ->.
apply eq_bigr => a _.
rewrite -big_mkcond /= -/(INR n.+1).
transitivity (\rprod_(i < n | t ``_ i == a) (INR (type.f P a) / INR n)).
  apply eq_big => // i.
  move/eqP => ->.
  by rewrite INR_type_fun.
rewrite big_const iter_Rmult_pow INR_type_fun.
congr (_ ^ _).
rewrite /typed_tuples inE in Hx.
move/forallP/(_ a)/eqP : Hx => Hx.
rewrite -INR_type_fun in Hx.
apply Rmult_eq_reg_r in Hx; last by apply/eqP/invR_neq0; rewrite INR_eq0.
move/INR_eq in Hx.
rewrite Hx num_occ_alt cardsE /=.
apply eq_card => /= n0.
by rewrite /in_mem /= tnth_mktuple.
Qed.

Local Close Scope tuple_ext_scope.

(** Probability of tuples representative of a type using the entropy: *)

Lemma tuple_dist_type_entropy t : tuple_of_row t \in T_{P} ->
  P `^ n t = exp2 (- INR n * `H P).
Proof.
move/(@tuple_dist_type t) => ->.
rewrite (_ : \rprod_(a : A) P a ^ (type.f P) a =
             \rprod_(a : A) exp2 (P a * log (P a) * INR n)); last first.
  apply eq_bigr => a _.
  case/boolP : (0 == P a) => H; last first.
    have {H}H : 0 < P a.
      have := dist_nonneg P a.
      case/Rle_lt_or_eq_dec => // abs.
      by rewrite abs eqxx in H.
    rewrite -{1}(logK H) -exp2_pow.
    congr exp2.
    rewrite -mulRA [X in _ = X]mulRC -mulRA mulRC.
    congr (_ * _).
    by rewrite type_fun_type.
  - move/eqP : (H) => <-.
    rewrite -(_ : O = type.f P a); first by rewrite !mul0R exp2_0 /pow.
    apply INR_eq.
    rewrite {1}/INR.
    apply (Rmult_eq_reg_r ( / INR n)); last by apply/eqP/invR_neq0; rewrite INR_eq0.
    by rewrite type_fun_type // -(eqP H) mulR0.
rewrite -(big_morph _ morph_exp2_plus exp2_0) -(big_morph _ (morph_mulRDl _) (mul0R _)).
by rewrite /entropy Rmult_opp_opp mulRC.
Qed.

Local Open Scope typ_seq_scope.

Lemma typed_tuples_are_typ_seq : (@row_of_tuple A n @: T_{ P }) \subset `TS P n 0.
Proof.
apply/subsetP => t Ht.
rewrite /set_typ_seq inE /typ_seq tuple_dist_type_entropy; last first.
  case/imsetP : Ht => x Hx ->.
  by rewrite row_of_tupleK.
by rewrite addR0 subR0 !leRR.
Qed.

(* TODO: move? *)
Lemma row_of_tuple_inj {C : finType} {m} : injective (@row_of_tuple C m).
Proof. move=> a b ab; by rewrite -(row_of_tupleK b) -ab row_of_tupleK. Qed.

(** Upper-bound of the number of tuples representative of a type using the entropy: *)

Lemma card_typed_tuples : INR #| T_{ P } | <= exp2 (INR n * `H P).
Proof.
rewrite -(invRK (exp2 (INR n * `H P))%R) => //.
rewrite -exp2_Ropp -mulNR.
set aux := - INR n * `H P.
apply/RleP; rewrite -div1R leR_pdivl_mulr //; apply/RleP; rewrite {}/aux.
case/boolP : [exists x, x \in T_{P}] => x_T_P.
- case/existsP : x_T_P => ta Hta.
  rewrite -(row_of_tupleK ta) in Hta.
  rewrite -(tuple_dist_type_entropy Hta).
  rewrite [X in X <= _](_ : _ = Pr P `^ n (@row_of_tuple A n @: T_{P})).
    by apply Pr_1.
  symmetry.
  rewrite /Pr.
  transitivity (\rsum_(a| (a \in [finType of 'rV[A]_n]) && [pred x in (@row_of_tuple A n @: T_{P})] a)
      exp2 (- INR n * `H P)).
    apply eq_big => // ta'/= Hta'.
    rewrite -(@tuple_dist_type_entropy ta') //.
    case/imsetP : Hta' => x Hx ->. by rewrite row_of_tupleK.
  rewrite big_const iter_Rplus_Rmult tuple_dist_type_entropy //.
  do 2 f_equal.
  rewrite card_imset //; exact row_of_tuple_inj.
- rewrite (_ : (INR #| T_{P} | = 0)%R); first by fourier.
  rewrite (_ : 0%R = INR 0) //; f_equal; apply/eqP.
  rewrite cards_eq0; apply/negPn.
  move: x_T_P; apply contra; by move/set0Pn/existsP.
Qed.

Lemma card_typed_tuples_alt : INR #| T_{P} | <= exp2 (INR n * `H P).
Proof.
apply Rle_trans with (INR #| `TS P n 0 |).
  apply le_INR; apply/leP.
  eapply leq_trans; last first.
    apply subset_leq_card.
    by apply typed_tuples_are_typ_seq.
  rewrite card_imset //.
  exact row_of_tuple_inj.
eapply Rle_trans; first by apply TS_sup.
rewrite addR0.
apply Rle_refl.
Qed.

Lemma perm_tuple_in_Ttuples ta (s : 'S_n) :
  perm_tuple s ta \in T_{P} <-> ta \in T_{P}.
Proof.
rewrite 2!in_set.
split => /forallP H; apply/forallP => a; move: H => /(_ a)/eqP => ->; by rewrite num_occ_perm.
Qed.

End typed_tuples_facts_continued.

Section enc_pre_img_partition.

Variables A B M : finType.
Variable n' : nat.
Let n := n'.+1.
Variable c : code A B M n.

Definition enc_pre_img (P : P_ n ( A )) := [set m | tuple_of_row (enc c m) \in T_{P}].

Lemma enc_pre_img_injective (P Q : P_ n ( A )) :
  enc_pre_img P != set0 -> enc_pre_img P = enc_pre_img Q ->
  forall a, P a = Q a.
Proof.
rewrite /enc_pre_img.
case/set0Pn => m.
rewrite in_set => HmP /setP HPQ.
have HmQ : tuple_of_row (enc c m) \in T_{Q} by move:(HPQ m) ; rewrite 2!in_set => <-.
move=> a {HPQ}.
move: HmP ; rewrite in_set => /forallP/(_ a)/eqP => ->.
move: HmQ ; rewrite in_set => /forallP/(_ a)/eqP => <-.
reflexivity.
Qed.

Definition enc_pre_img_partition :=
  enc_pre_img @: [set P in P_ n ( A ) | enc_pre_img P != set0].

Lemma cover_enc_pre_img : cover enc_pre_img_partition = [set: M].
Proof.
rewrite /cover /enc_pre_img_partition.
apply/setP => m.
rewrite in_set.
apply/bigcupP.
exists (enc_pre_img (type_of_tuple (tuple_of_row (enc c m)))).
- apply/imsetP; exists (type_of_tuple (tuple_of_row (enc c m))) => //.
  rewrite in_set.
  apply/andP; split => //.
  apply/set0Pn.
  exists m.
  rewrite 2!in_set.
  by apply/forallP.
- rewrite 2!in_set.
  by apply/forallP.
Qed.

Lemma trivIset_enc_pre_img : trivIset enc_pre_img_partition.
Proof.
apply/trivIsetP => S1 S2 /imsetP ; case => P1 _ HP1. case/imsetP => P2 _ HP2 HP12.
subst S1 S2.
rewrite /disjoint.
apply/pred0P => m /=.
apply/negP/negP.
move: m.
apply/forallP; rewrite -negb_exists; apply/negP; case/existsP => m /andP [H1 H2]; contradict HP12.
apply/negP/negPn/eqP/setP => m'.
case/boolP : (m' \in enc_pre_img P2) => [|/negbTE] Hcase.
- apply/negPn/negPn.
  rewrite 2!in_set; apply/forallP => a.
  move: H1; rewrite 2!in_set => /forallP/(_ a)/eqP ->.
  move: Hcase; rewrite 2!in_set => /forallP/(_ a)/eqP <-.
  move: H2; rewrite 2!in_set => /forallP/(_ a)/eqP <-.
  by rewrite eqxx.
- apply/negP/negPn; move: Hcase => /negP/negPn; apply contra => Hcase.
  rewrite 2!in_set; apply/forallP => a.
  move: H2; rewrite 2!in_set => /forallP/(_ a)/eqP ->.
  move: Hcase; rewrite 2!in_set => /forallP/(_ a)/eqP <-.
  move: H1; rewrite 2!in_set => /forallP/(_ a)/eqP <-.
  by rewrite eqxx.
Qed.

End enc_pre_img_partition.

Section sum_messages_types.

Variables A B M : finType.
Variable n' : nat.
Let n := n'.+1.
Variable c : code A B M n.

Lemma sum_messages_types' f :
  \rsum_(P : P_ n ( A )) (\rsum_(m |m \in enc_pre_img c P) f m) =
  \rsum_ (S | S \in enc_pre_img_partition c) \rsum_(m in S) f m.
Proof.
rewrite (bigID (fun P => [exists m, m \in enc_pre_img c P] )).
rewrite (_ : forall a b, addR_comoid a b = a + b) //.
rewrite Rplus_comm big1 ; last first.
  move=> P ; rewrite andTb negb_exists => HP.
  apply big_pred0 => m /=.
  apply/negP/negPn; by move:HP => /forallP/(_ m) ->.
rewrite /= add0R big_imset.
  apply eq_big => [P|P _] //=.
  rewrite in_set.
  case: set0Pn => [/existsP //| ?]; exact/existsP.
move=> P Q; rewrite 2!in_set => HP HQ HPQ /=.
move: (enc_pre_img_injective HP HPQ) => {HP HQ HPQ}HPQ.
case: P HPQ => /= Pd Pf HP HPQ.
case: Q HPQ => /= Qd Qf HQ HPQ.
apply/type_eqP => /=.
apply/eqP.
apply ffunP => a.
apply/val_inj/INR_eq.
move: {HPQ}(HPQ a); rewrite HP HQ; move/Rmult_eq_reg_r; apply.
apply/eqP/invR_neq0; by rewrite INR_eq0.
Qed.

Lemma sum_messages_types f :
  \rsum_(P : P_ n ( A )) (\rsum_(m |m \in enc_pre_img c P) f m) = \rsum_ (m : M) (f m).
Proof.
transitivity (\rsum_ (m in [set: M]) (f m)); last by apply eq_bigl => b; rewrite in_set.
rewrite -(cover_enc_pre_img c) /enc_pre_img_partition sum_messages_types'.
symmetry.
by apply big_trivIset, trivIset_enc_pre_img.
Qed.

End sum_messages_types.

Section typed_code_def.

Variables A B M : finType.
Variable n : nat.
Variable P : P_ n ( A ).

Record typed_code := mkTypedCode {
  untyped_code :> code A B M n ;
  typed_prop : forall m, tuple_of_row (enc untyped_code m) \in T_{P} }.

End typed_code_def.

Section typed_code_of_code.

Variables A B M : finType.
Variable n' : nat.
Let n := n'.+1.
Variable P : P_ n ( A ).
Variable c : code A B M n.

Definition def := row_of_tuple (sval (typed_tuples_not_empty P)).
Definition Hdef := proj2_sig (typed_tuples_not_empty P).

Definition tcode_untyped_code := mkCode
  [ffun m => if tuple_of_row (enc c m) \in T_{P} then enc c m else def] (dec c).

Lemma tcode_typed_prop (m : M) : tuple_of_row ((enc tcode_untyped_code) m) \in T_{P}.
Proof.
rewrite /= ffunE; case: ifP => [//| _]; rewrite /def row_of_tupleK; exact Hdef.
Qed.

Definition tcode : typed_code B M P := mkTypedCode tcode_typed_prop.

End typed_code_of_code.

Notation "P '.-typed_code' c" := (tcode P c) : types_scope.
