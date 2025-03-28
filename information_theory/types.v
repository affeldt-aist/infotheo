(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum perm matrix.
From mathcomp Require boolp.
From mathcomp Require Import Rstruct exp.
Require Import ssr_ext ssralg_ext realType_ext realType_ln.
Require Import fdist proba entropy num_occ channel_code channel typ_seq.

(**md**************************************************************************)
(* # Elements of the theory of types (in information theory)                  *)
(*                                                                            *)
(* Main lemmas:                                                               *)
(* - upper-bound of the number of types (`type_counting`)                     *)
(* - probability of tuples representative of a type using the entropy         *)
(*   (`tuple_dist_type_entropy`)                                              *)
(* - upper-bound of the number of tuples representative of a type using the   *)
(*   entropy (`card_typed_tuples`)                                            *)
(*                                                                            *)
(* ```                                                                        *)
(*                  P_n(A) == type                                            *)
(*                   T_{P} == typed tuples, tuples that are representative of *)
(*                            a type                                          *)
(*             enc_pre_img == TODO                                            *)
(*   enc_pre_img_partition == TODO                                            *)
(*                   tcode == TODO                                            *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "'P_' n '(' A ')'" (at level 9, n, A at next level).
Reserved Notation "'T_{' P '}'" (at level 9).
Reserved Notation "P '.-typed_code' c" (at level 50, c at next level).

Declare Scope types_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory Num.Theory.

Local Open Scope entropy_scope.
Local Open Scope num_occ_scope.
Local Open Scope fdist_scope.
Local Open Scope ring_scope.

Module type.

Section type_def.
Variables (A : finType) (n : nat).

Record type : predArgType := mkType {
  d :> {fdist A} ;
  f : {ffun A -> 'I_n.+1} ;
  d_f : forall a, d a = (f a)%:R / n%:R }.

End type_def.

End type.

Definition type_coercion := type.d.
Coercion type_coercion : type.type >-> FDist.t.

Notation "'P_' n '(' A ')'" := (type.type A n) : types_scope.

Local Open Scope types_scope.

Definition ffun_of_type A n (P : P_ n ( A )) := let: type.mkType _ f _ := P in f.

Lemma type_fun_type A n (_ : n != O) (P : P_ n ( A )) a :
  ((type.f P) a)%:R = n%:R * type.d P a.
Proof.
case: P => /= d f d_f.
by rewrite d_f mulrCA mulfV ?mulr1// pnatr_eq0.
Qed.

Lemma INR_type_fun A n (P : P_ n ( A )) a :
  ((type.f P) a)%:R / n%:R = type.d(*TODO: fix coercion *)P a.
Proof. destruct P as [d f d_f] => /=. by rewrite d_f. Qed.

Lemma no_0_type (A : finType) (d : {fdist A}) (t : {ffun A -> 'I_1}) :
  (forall a, d a = (t a)%:R / 0%:R) -> False.
Proof.
move=> H.
have /eqP := @oner_neq0 Rdefinitions.R; apply.
rewrite -(FDist.f1 d).
transitivity (\sum_(a | a \in A) (t a)%:R / 0 : Rdefinitions.R); first exact/eq_bigr.
rewrite -big_distrl /= -natr_sum.
rewrite (_ : (\sum_(a in A) _)%nat = O) ?mul0r //.
transitivity (\sum_(a in A) 0)%nat; first by apply eq_bigr => a _; rewrite (ord1 (t a)).
by rewrite big_const iter_addn.
Qed.

Definition type_of_tuple (A : finType) n (ta : n.+1.-tuple A) : P_ n.+1 ( A ).
pose f := [ffun a => N(a | ta)%:R / n.+1%:R : Rdefinitions.R].
assert (H1 : forall a, 0%R <= f a).
  move=> a; rewrite ffunE; apply/divr_ge0; by [apply ler0n | apply ltr0n].
assert (H2 : \sum_(a in A) f a = 1).
  under eq_bigr do rewrite ffunE /=.
  rewrite -big_distrl /= -natr_sum.
  by rewrite sum_num_occ_alt mulfV // pnatr_eq0.
assert (H : forall a, (N(a | ta) < n.+2)%nat).
  move=> a; rewrite ltnS; by apply num_occ_leq_n.
refine (@type.mkType _ n.+1 (FDist.make H1 H2)
  [ffun a => @Ordinal n.+2 (N(a | ta)) (H a)] _).
by move=> a /=; rewrite !ffunE.
Defined.

Lemma type_ext A n (t1 t2 : P_ n ( A )) : type.f t1 = type.f t2 -> t1 = t2.
Proof.
case: t1 t2 => d1 f1 H1 /= [] d2 f2 H2 /= f1f2.
subst f2.
suff ? : d1 = d2 by subst d2; congr type.mkType; exact: boolp.Prop_irrelevance.
apply fdist_ext => /= a; by rewrite H1 H2.
Qed.

Definition type_eq A n (t1 t2 : P_ n ( A )) :=
  match t1, t2 with
    | type.mkType _ f1 _, type.mkType _ f2 _ => f1 == f2
  end.

Lemma type_eqP A n : Equality.axiom (@type_eq A n).
Proof.
case=> d1 f1 H1 [] d2 f2 H2 /=.
apply: (iffP idP) => [/eqP H|[] _ -> //].
subst f2.
suff ? : d1 = d2 by subst d2; congr type.mkType; exact: boolp.Prop_irrelevance.
apply fdist_ext => /= a; by rewrite H1 H2.
Qed.

HB.instance Definition _ A n := hasDecEq.Build _ (@type_eqP A n).

Lemma type_ffunP A n (P Q : P_ n.+1 ( A )) :
  (forall c, type.d P c = type.d Q c) -> P = Q.
Proof.
move=> H.
destruct P as [d1 f1 H1].
destruct Q as [d2 f2 H2].
rewrite /= in H.
apply/type_eqP => /=.
apply/eqP/ffunP => a.
apply/val_inj/eqP.
rewrite -(eqr_nat Rdefinitions.R).
move: {H}(H a); rewrite H1 H2.
move=> /(congr1 (fun x => x * n.+1%:R)).
by rewrite -!mulrA mulVf ?mulr1 ?pnatr_eq0// => ->.
Qed.

Definition fdist_of_ffun (A : finType) n (f : {ffun A -> 'I_n.+2})
  (Hf : (\sum_(a in A) f a)%nat == n.+1) : {fdist A}.
set pf := [ffun a : A => (f a)%:R / n.+1%:R :> Rdefinitions.R].
assert (pf_ge0 : forall a, 0 <= pf a).
  move=> a.
  by rewrite /pf/= ffunE divr_ge0//.
assert (H : \sum_(a in A) pf a = 1 :> Rdefinitions.R).
  rewrite /pf; under eq_bigr do rewrite ffunE /=.
  rewrite -big_distrl /= -natr_sum.
  move/eqP : Hf => ->.
  by rewrite mulfV// pnatr_eq0.
exact: (FDist.make pf_ge0 H).
Defined.

Lemma fdist_of_ffun_prop (A : finType) n (f : {ffun A -> 'I_n.+2})
  (Hf : (\sum_(a in A) f a)%nat == n.+1) :
forall a : A, (fdist_of_ffun Hf) a = (f a)%:R / n.+1%:R.
Proof. by move=> a; rewrite ffunE. Qed.

Definition type_choice_f (A : finType) n (f : {ffun A -> 'I_n.+1}) : option (P_ n ( A )).
destruct n; first by exact None.
refine (match Sumbool.sumbool_of_bool (\sum_(a in A) f a == n.+1)%nat with
          | left H => Some (@type.mkType _ _ (fdist_of_ffun H) f (fdist_of_ffun_prop H))
          | right _ => None
        end).
Defined.

Lemma ffun_of_fdist (A : finType) n (d : {fdist A}) (t : {ffun A -> 'I_n.+2})
  (H : forall a : A, d a = (t a)%:R / n.+1%:R) : (\sum_(a in A) t a)%nat == n.+1.
Proof.
suff : (\sum_(a in A) t a)%:R == n.+1%:R * \sum_(a | a \in A) d a.
  by move/eqP; rewrite (FDist.f1 d) mulr1 => /eqP; rewrite eqr_nat.
apply/eqP.
transitivity (n.+1%:R * (\sum_(a|a \in A) (t a)%:R / n.+1%:R) :> Rdefinitions.R).
  rewrite -big_distrl -natr_sum.
  by rewrite mulrCA mulfV ?mulr1 // pnatr_eq0.
by congr (_ * _); exact/eq_bigr.
Qed.

Lemma type_choice_pcancel A n : pcancel (@type.f A n) (@type_choice_f A n).
Proof.
case=> d t H /=.
destruct n.
  by move: (no_0_type H).
rewrite /type_choice_f /=; f_equal.
move: (ffun_of_fdist H) => H'.
destruct Sumbool.sumbool_of_bool as [e|e]; last first.
  by rewrite H' in e.
congr Some.
set d1 := fdist_of_ffun _.
suff ? : d1 = d by subst d; congr type.mkType; apply boolp.Prop_irrelevance.
apply fdist_ext => /= a; by rewrite ffunE H.
Qed.

HB.instance Definition _ A n := @PCanIsCountable _ _ _ _ (@type_choice_pcancel A n).

Definition type_pickle A n (P : P_ n (A)) : nat.
destruct P as [d f H].
exact: (pickle f).
(*destruct (finfun_countMixin A [finType of 'I_n.+1]) as [pi unpi Hcan].
apply (pi f).*)
Defined.

Definition type_unpickle A n (m : nat) : option (P_ n ( A )).
destruct n.
  exact None.
pose unpi : option {ffun A -> 'I_n.+2} := unpickle m.
case: unpi; last first.
  exact None.
move=> f.
refine (match Sumbool.sumbool_of_bool ((\sum_(a in A) f a)%nat == n.+1) with
          | left H => Some (@type.mkType _ _ (fdist_of_ffun H) f (fdist_of_ffun_prop H))
          | right _ => None
        end).
Defined.

Lemma type_count_pcancel A n : pcancel (@type_pickle A n) (@type_unpickle A n).
Proof.
destruct n.
  case=> d t H /=; by move: (no_0_type H).
case=> d t H /=.
rewrite pickleK.
move: (ffun_of_fdist H) => H'.
destruct Sumbool.sumbool_of_bool as [e|e]; last first.
  by rewrite H' in e.
congr Some.
set d1 := fdist_of_ffun _.
suff ? : d1 = d by subst d; congr type.mkType; apply boolp.Prop_irrelevance.
apply/fdist_ext => a; by rewrite ffunE H.
Qed.

HB.instance Definition _ A n := @PCanIsCountable _ _ _ _ (@type_count_pcancel A n).

Definition type_enum_f (A : finType) n (f : { f : {ffun A -> 'I_n.+1} | (\sum_(a in A) f a)%nat == n} ) : option (P_ n ( A )).
destruct n.
  apply None.
refine (Some (@type.mkType _ _ (fdist_of_ffun (proj2_sig f)) (sval f) (fdist_of_ffun_prop (proj2_sig f)))).
Defined.

Definition type_enum A n := pmap (@type_enum_f A n)
  (enum [the finType of {f : {ffun A -> 'I_n.+1} | (\sum_(a in A) f a)%nat == n}]).

Lemma type_enumP A n : finite_axiom (@type_enum A n).
Proof.
destruct n.
  case=> d t H /=; by move: (no_0_type H).
case=> d t H /=.
move: (ffun_of_fdist H) => H'.
have : Finite.axiom (enum [the finType of { f : {ffun A -> 'I_n.+2} | (\sum_(a in A) f a)%nat == n.+1}]).
  rewrite enumT; by apply enumP.
move/(_ (@exist {ffun A -> 'I_n.+2} (fun f => \sum_(a in A) f a == n.+1)%nat t H')) => <-.
rewrite /type_enum /= /type_enum_f /= count_map.
by apply eq_count.
Qed.

HB.instance Definition _ A n := @isFinite.Build (P_ n (A)) _ (@type_enumP A n).

Section type_facts.
Variable A : finType.
Local Open Scope nat_scope.

Lemma type_counting n : #| P_ n ( A ) | <= expn (n.+1) #|A|.
Proof.
rewrite -(card_ord n.+1) -card_ffun /=.
rewrite cardE /enum_mem.
apply (@leq_trans (size (map (@ffun_of_type A n) (Finite.enum _)))).
  by rewrite 2!size_map.
rewrite cardE.
apply: uniq_leq_size.
  rewrite map_inj_uniq //.
    move: (enum_uniq (P_ n (A))).
    by rewrite enumT.
  case=> d f Hd [] d2 f2 Hd2 /= ?; subst f2.
  have ? : d = d2 by apply/fdist_ext => a; rewrite Hd Hd2.
  subst d2; congr type.mkType; exact: boolp.Prop_irrelevance.
move=> /= f Hf; by rewrite mem_enum.
Qed.

Lemma type_card_neq0 n : 0 < #|A| -> 0 < #|P_ n.+1(A)|.
Proof.
case/card_gt0P => a _.
apply/card_gt0P.
have [f Hf] : [the finType of {f : {ffun A -> 'I_n.+2} | \sum_(a in A) f a == n.+1}].
  exists [ffun a1 => if pred1 a a1 then Ordinal (ltnSn n.+1) else Ordinal (ltn0Sn n.+1)].
  rewrite (bigD1 a) //= big1; first by rewrite ffunE eqxx addn0.
  move=> p /negbTE Hp; by rewrite ffunE Hp.
exists (@type.mkType _ _ (fdist_of_ffun Hf) _ (fdist_of_ffun_prop Hf)).
by rewrite inE.
Qed.

Lemma type_empty1 n : #|A| = 0 -> #|P_ n(A)| = 0.
Proof.
move=> A0; apply eq_card0; case=> d ? ?.
move: (fdist_card_neq0 d); by rewrite A0.
Qed.

Lemma type_empty2 : #|P_ 0(A)| = 0.
Proof.
apply eq_card0; case=> d f Hf.
exfalso.
by move/no_0_type in Hf.
Qed.

End type_facts.

Section typed_tuples.
Variables (A : finType) (n : nat) (P : P_ n ( A )).

Definition typed_tuples :=
  [set t : n.-tuple A | [forall a, type.d P a == (N(a | t)%:R / n%:R)%R] ].

End typed_tuples.

Notation "'T_{' P '}'" := (typed_tuples P) : types_scope.

Section typed_tuples_facts.
Variables (A : finType) (n' : nat).
Let n := n'.+1.
Variable P : P_ n ( A ).

Lemma type_numocc ta (Hta : ta \in T_{P}) a : N(a | ta) = type.f P a.
Proof.
move: Hta.
rewrite in_set.
move/forallP/(_ a)/eqP.
destruct P as [d f H] => /= Htmp.
apply/eqP; rewrite -(@eqr_nat Rdefinitions.R).
move: Htmp => /(congr1 (fun x => x * n%:R)).
rewrite -mulrA mulVf ?pnatr_eq0// mulr1 => <-.
by rewrite H -mulrA mulVf ?mulr1// pnatr_eq0.
Qed.

Lemma typed_tuples_not_empty' : exists x : seq A,
  exists Hx : size x == n, Tuple Hx \in T_{P}.
Proof.
exists (flatten (map (fun x0 => nseq (type.f P x0) x0) (enum A))).
have Hx : size (flatten [seq nseq (type.f P x0) x0 | x0 <- enum A]) == n.
  rewrite size_flatten /shape -map_comp sumn_big_addn big_map.
  case: (P) => P' f HP' /=.
  apply/eqP.
  transitivity (\sum_(a in A) f a)%nat; last first.
     apply/eqP; by apply ffun_of_fdist with P'.
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
Variables (A : finType) (n : nat).
Hypothesis Hn : n != O.
Variable P : P_ n ( A ).

Lemma typed_tuples_not_empty_alt : {t : n.-tuple A | t \in T_{P}}.
Proof. destruct n => //. apply typed_tuples_not_empty. Qed.

Local Open Scope fdist_scope.
Local Open Scope tuple_ext_scope.
Local Open Scope vec_ext_scope.

Lemma tuple_dist_type t : tuple_of_row t \in T_{P} ->
  ((type.d P) `^ n) t = \prod_(a : A) type.d P a ^+ (type.f P a).
Proof.
move=> Hx.
rewrite fdist_rVE.
rewrite (_ : \prod_(i < n) type.d P (t ``_ i) =
  \prod_(a : A) (\prod_(i < n) (if a == t ``_ i then type.d P t ``_ i else 1))); last first.
  rewrite exchange_big; apply eq_big ; first by [].
  move=> i _.
  rewrite (bigID (fun y => y == t ``_ i)) /=.
  rewrite big_pred1_eq eqxx big1 ?mulr1 //.
  by move=> i0 /negbTE ->.
apply eq_bigr => a _.
rewrite -big_mkcond /=.
transitivity (\prod_(i < n | t ``_ i == a) ((type.f P a)%:R / n%:R) : Rdefinitions.R).
  by apply eq_big => // i /eqP ->; rewrite INR_type_fun.
rewrite prodr_const/=.
rewrite INR_type_fun.
congr (_ ^+ _).
rewrite /typed_tuples inE in Hx.
move/forallP/(_ a)/eqP : Hx.
rewrite -INR_type_fun.
move=> /(congr1 (fun x => x * n%:R)).
rewrite -!mulrA mulVf ?pnatr_eq0 ?mulr1// => /eqP; rewrite eqr_nat => /eqP ->.
rewrite num_occ_alt cardsE /=.
apply eq_card => /= n0.
by rewrite /in_mem /= tnth_mktuple.
Qed.

Local Close Scope tuple_ext_scope.

Lemma tuple_dist_type_entropy t : tuple_of_row t \in T_{P} ->
  ((type.d P) `^ n) t = ((2%:R:Rdefinitions.R) `^ (- n%:R * `H P))%R.
Proof.
move/(@tuple_dist_type t) => ->.
rewrite (_ : \prod_(a : A) type.d P a ^+ (type.f P) a =
             \prod_(a : A) (2%:R:Rdefinitions.R) `^ (type.d P a * log (type.d P a) * n%:R)); last first.
  apply eq_bigr => a _.
  have [H|H] := eqVneq 0 (type.d P a); last first.
    have {}H : 0 < type.d P a.
      have := FDist.ge0 (type.d P) a.
      by rewrite Order.POrderTheory.le_eqVlt (negbTE H)/=.
    rewrite -{1}(@LogK _ 2%N _ _ H)//.
    rewrite -powRrM' mulrC.
    congr (_ `^ _)%R.
    rewrite -mulrA [X in _ = X]mulrC -mulrA mulrC.
    congr (_ * _).
    by rewrite -type_fun_type.
  - move : (H) => <-.
    rewrite -(_ : O = type.f P a).
      by rewrite !mul0r expr0 exp.powRr0.
    apply/eqP.
    rewrite -(eqr_nat Rdefinitions.R).
    move : H => /(congr1 (fun x => n%:R * x)).
    by rewrite mulr0 type_fun_type// => /eqP.
rewrite -powR2sum.
congr (_ `^ _)%R.
rewrite /entropy mulrN mulNr opprK.
rewrite big_distrr/=.
apply: eq_bigr => a _.
by rewrite mulrC; congr *%R.
Qed.

Local Open Scope typ_seq_scope.

Import Order.POrderTheory.

Lemma typed_tuples_are_typ_seq :
  (@row_of_tuple A n @: T_{ P }) \subset `TS P n 0.
Proof.
apply/subsetP => t Ht.
rewrite /set_typ_seq inE /typ_seq tuple_dist_type_entropy; last first.
  by case/imsetP : Ht => x Hx ->; rewrite row_of_tupleK.
by rewrite addr0 subr0 lexx.
Qed.

Lemma card_typed_tuples :
  #| T_{ P } |%:R <= ((2%:R:Rdefinitions.R) `^ (n%:R * `H P))%R.
Proof.
rewrite -(@invrK _ ((2%:R:Rdefinitions.R) `^ (n%:R * `H P))%R) -powRN -mulNr.
set aux := - n%:R * `H P.
rewrite -div1r ler_pdivlMr // {}/aux ?powR_gt0//.
case/boolP : [exists x, x \in T_{P}] => x_T_P.
- case/existsP : x_T_P => ta Hta.
  rewrite -(row_of_tupleK ta) in Hta.
  rewrite -(tuple_dist_type_entropy Hta).
  rewrite [X in X <= _](_ : _ = Pr ((type.d P) `^ n) (@row_of_tuple A n @: T_{P})).
    exact: Pr_le1.
  symmetry.
  rewrite /Pr.
  transitivity (\sum_(a | (a \in 'rV[A]_n) &&
                          [pred x in (@row_of_tuple A n @: T_{P})] a)
      (2%:R : Rdefinitions.R) `^ (- n%:R * `H P)).
    apply eq_big => // ta'/= Hta'.
    rewrite -(@tuple_dist_type_entropy ta') //.
    case/imsetP : Hta' => x Hx ->. by rewrite row_of_tupleK.
  rewrite big_const iter_addr addr0 tuple_dist_type_entropy //.
  rewrite [in RHS]mulrC.
  rewrite mulr_natr.
  do 2 f_equal.
  by rewrite card_imset //; exact: row_of_tuple_inj.
- rewrite (_ : (#| T_{P} |%:R = 0)%R); first by rewrite mul0r.
  rewrite (_ : 0%R = 0%:R) //; congr (_%:R); apply/eqP.
  rewrite cards_eq0; apply/negPn.
  by move: x_T_P; apply contra => /set0Pn/existsP.
Qed.

Lemma card_typed_tuples_alt :
  (#| T_{P} |%:R <= (2%R:Rdefinitions.R) `^ (n%:R * `H P))%R.
Proof.
apply (@le_trans _ _ (#| `TS P n 0 |%:R)).
  rewrite ler_nat.
  apply: leq_trans; last first.
    by apply subset_leq_card; exact: typed_tuples_are_typ_seq.
  by rewrite card_imset //; exact: row_of_tuple_inj.
by apply: (le_trans (TS_sup _ _ _)); rewrite addr0.
Qed.

Lemma perm_tuple_in_Ttuples ta (s : 'S_n) :
  perm_tuple s ta \in T_{P} <-> ta \in T_{P}.
Proof.
rewrite 2!in_set.
split => /forallP H; apply/forallP => a; move: H => /(_ a)/eqP => ->; by rewrite num_occ_perm.
Qed.

End typed_tuples_facts_continued.

Section enc_pre_img_partition.
Variables (A B M : finType) (n' : nat).
Let n := n'.+1.
Variable c : code A B M n.

Definition enc_pre_img (P : P_ n ( A )) := [set m | tuple_of_row (enc c m) \in T_{P}].

Lemma enc_pre_img_injective (P Q : P_ n ( A )) :
  enc_pre_img P != set0 -> enc_pre_img P = enc_pre_img Q ->
  forall a, type.d P a = type.d Q a.
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
  by apply/forallP => a; rewrite ffunE.
- rewrite 2!in_set.
  by apply/forallP => a; rewrite ffunE.
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
Variables (A B M : finType) (n' : nat).
Let n := n'.+1.
Variable c : code A B M n.

Lemma sum_messages_types' f :
  \sum_(P : P_ n ( A )) (\sum_(m |m \in enc_pre_img c P) f m) =
  \sum_ (S | S \in enc_pre_img_partition c) \sum_(m in S) f m :> Rdefinitions.R.
Proof.
rewrite (bigID (fun P => [exists m, m \in enc_pre_img c P] )).
rewrite /=.
rewrite addrC big1 ; last first.
  move=> P; rewrite negb_exists => HP.
  apply big_pred0 => m /=.
  by apply/negP/negPn; move:HP => /forallP/(_ m) ->.
rewrite /= add0r big_imset.
  apply eq_big => [P|P _] //=.
  rewrite in_set.
  by case: set0Pn => [/existsP //| ?]; exact/existsP.
move=> P Q; rewrite 2!in_set => HP HQ HPQ /=.
move: (enc_pre_img_injective HP HPQ) => {HP HQ} {}HPQ.
case: P HPQ => /= Pd Pf HP HPQ.
case: Q HPQ => /= Qd Qf HQ HPQ.
apply/type_eqP => /=.
apply/eqP.
apply ffunP => a.
apply/val_inj.
move: {HPQ}(HPQ a); rewrite HP HQ.
move=> /(congr1 (fun x => x * n%:R)).
rewrite -!mulrA mulVf ?pnatr_eq0// !mulr1 => /eqP.
by rewrite eqr_nat => /eqP.
Qed.

Lemma sum_messages_types f :
  \sum_(P : P_ n ( A )) (\sum_(m |m \in enc_pre_img c P) f m)
  = \sum_ (m : M) (f m) :> Rdefinitions.R.
Proof.
transitivity (\sum_ (m in [set: M]) (f m)); last first.
  by apply: eq_bigl => b; rewrite in_set.
rewrite -(cover_enc_pre_img c) /enc_pre_img_partition sum_messages_types'.
exact/esym/big_trivIset/trivIset_enc_pre_img.
Qed.

End sum_messages_types.

Section typed_code_def.
Variables (A B M : finType) (n : nat).
Variable P : P_ n ( A ).

Record typed_code := mkTypedCode {
  untyped_code :> code A B M n ;
  typed_prop : forall m, tuple_of_row (enc untyped_code m) \in T_{P} }.

End typed_code_def.

Section typed_code_of_code.
Variables (A B M : finType) (n' : nat).
Let n := n'.+1.
Variable P : P_ n ( A ).
Variable c : code A B M n.

Definition def := row_of_tuple (sval (typed_tuples_not_empty P)).
Definition Hdef := proj2_sig (typed_tuples_not_empty P).

Definition tcode_untyped_code := mkCode
  [ffun m => if tuple_of_row (enc c m) \in T_{P} then enc c m else def] (dec c).

Lemma tcode_typed_prop (m : M) :
  tuple_of_row (enc tcode_untyped_code m) \in T_{P}.
Proof.
rewrite /= ffunE; case: ifP => [//| _]; rewrite /def row_of_tupleK.
exact Hdef.
Qed.

Definition tcode : typed_code B M P := mkTypedCode tcode_typed_prop.

End typed_code_of_code.

Notation "P '.-typed_code' c" := (tcode P c) : types_scope.
