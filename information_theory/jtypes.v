From HB Require Import structures.
(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum fingroup perm.
From mathcomp Require boolp.
From mathcomp Require Import Rstruct reals exp.
Require Import ssr_ext ssralg_ext realType_ext realType_ln fdist entropy.
Require Import num_occ channel types.

(**md**************************************************************************)
(* # Joint Types                                                              *)
(*                                                                            *)
(* Main lemmas:                                                               *)
(* - upper-bound of the number of conditional types (`bound_card_jtype`)      *)
(* - joint types are not empty (`jtype_not_empty`)                            *)
(* - relation between the number of symbol occurrences and the number of      *)
(*   pairs of symbols occurrences (`occ_co_occ`)                              *)
(*                                                                            *)
(* ```                                                                        *)
(*       jtype == type of joint type, notation: P_n(A, B)                     *)
(*       shell == shell, notation: V.-shell t                                 *)
(*   cond_type == conditional type, notation: \nu{V}(P)                       *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "'P_' n '(' A ',' B ')'" (at level 9,
  n at next level, A at next level, B at next level).
Reserved Notation "V '.-shell' ta" (at level 5,
  format "V '.-shell'  ta").
Reserved Notation "'\nu_' n '^{' A ',' B '}' '(' P ')'" (at level 50,
  n, A, B, P at next level, format "'\nu_' n '^{' A ',' B '}' '(' P ')'").
Reserved Notation "'\nu^{' B '}' '(' P ')'" (at level 50,
  B, P at next level, format "'\nu^{' B '}' '(' P ')'").
Reserved Notation "'`tO(' V )" (at level 10).

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope channel_scope.
Local Open Scope ring_scope.

Import Order.POrderTheory GRing.Theory Num.Theory.

Module JType.
Section def.
Variables (A B : finType) (n : nat).
Local Open Scope nat_scope.

Record t : predArgType := mk {
  c :> `Ch*(A, B) ;
  f : {ffun A -> {ffun B -> 'I_n.+1}} ;
  sum_f : \sum_(a in A) \sum_(b in B) f a b == n ;
  c_f : forall a b, c a b = let row := \sum_(b in B) f a b in
                            if row == O
                            then #|B|%:R^-1
                            else (f a b)%:R / row%:R }.

End def.
End JType.

Coercion jtype_coercion := JType.c.

Notation "'P_' n '(' A ',' B ')'" := (JType.t A B n) : types_scope.
Local Open Scope types_scope.

Definition ffun_of_jtype A B n (i : P_ n ( A , B )) := let: JType.mk _ f _ _ := i in f.

Lemma jtype_ext A B n (t1 t2 : P_ n ( A , B )) : JType.f t1 = JType.f t2 -> t1 = t2.
Proof.
case: t1 t2 => d1 f1 Hf1 H1 /= [] d2 f2 Hf2 H2 /= ?; subst f2.
have ? : d1 = d2.
  apply/Channel1.chan_star_eq.
  by rewrite boolp.funeqE => a; apply/fdist_ext => b; rewrite H1 H2.
subst d2; congr JType.mk; exact/boolp.Prop_irrelevance.
Qed.

Definition jtype_eq A B n (t1 t2 : P_ n ( A , B )) :=
  match t1, t2 with
    | JType.mk _ f1 _ _, JType.mk _ f2 _ _ => f1 == f2
  end.

Lemma jtype_eqP A B n : Equality.axiom (@jtype_eq A B n).
Proof.
case=> d1 f1 Hf1 H1 [] d2 f2 Hf2 H2 /=.
apply: (iffP idP) => [/eqP H |[] _ -> //].
subst f2.
have ? : d1 = d2.
  apply/Channel1.chan_star_eq.
  by rewrite boolp.funeqE => a /=; apply/fdist_ext => b; rewrite H1 H2.
subst d2; congr JType.mk; exact/boolp.Prop_irrelevance.
Qed.

HB.instance Definition _ A B n := @hasDecEq.Build _ _ (@jtype_eqP A B n).

Definition nneg_fun_of_pre_jtype (A B : finType) n
  (f : {ffun A -> {ffun B -> 'I_n.+1}}) : A -> {ffun B -> Rdefinitions.R}.
pose pf := fun a => [ffun b : B =>
  let ln := (\sum_(b1 in B) (f a b1))%N in
  if ln == O
    then #|B|%:R^-1
    else (f a b)%:R / ln%:R].
exact: pf.
Defined.

Definition nneg_fun_of_pre_jtype_ge0 (A B : finType) (Bnot0 : (0 < #|B|)%N) n
    (f : {ffun A -> {ffun B -> 'I_n.+1}}) a b :
  0 <= nneg_fun_of_pre_jtype f a b.
Proof.
rewrite /nneg_fun_of_pre_jtype ffunE.
case: ifPn => [_ | Hcase].
- by rewrite invr_ge0.
- by rewrite divr_ge0.
Qed.

Definition chan_of_jtype (A B : finType) (Anot0 : (0 < #|A|)%N)
    (Bnot0 : (0 < #|B|)%N)
  n (f : {ffun A -> {ffun B -> 'I_n.+1}}) : `Ch*(A, B).
set pf := fun a b =>
  let ln := (\sum_(b1 in B) (f a b1))%N in
  if ln == O
  then #|B|%:R^-1
  else ((f a b)%:R / ln%:R) : Rdefinitions.R.
refine (@Channel1.mkChan A B _ Anot0) => a.
apply: (@FDist.make _ _ (@nneg_fun_of_pre_jtype _ _ n f a)).
  move=> b.
  by apply: nneg_fun_of_pre_jtype_ge0.
under eq_bigr do rewrite ffunE.
have [->|Hcase] := eqVneq (\sum_(b1 in B) (f a b1))%N 0%N.
- rewrite big_const iter_addr addr0.
  by rewrite -[LHS]mulr_natl divff// gt_eqF// ltr0n.
- under eq_bigr=> b bB.
    rewrite /=.
    case: ifPn.
      by rewrite (negbTE Hcase).
    move=> _.
    over.
  by rewrite /= -big_distrl//= -natr_sum divff// (_ : 0 = 0%:R)// eqr_nat.
Defined.

Definition jtype_choice_f (A B : finType) n (f : {ffun A -> {ffun B -> 'I_n.+1}}) : option (P_ n ( A , B )).
refine (
match Sumbool.sumbool_of_bool (0 < #|A|)%N with
  | left Anot0 =>
    match Sumbool.sumbool_of_bool (0 < #|B|)%N with
      |left Bnot0 =>
       match Sumbool.sumbool_of_bool (\sum_(a in A) \sum_(b in B) f a b == n)%N with
         | left Hf => Some (@JType.mk A B n (chan_of_jtype Anot0 Bnot0 f) f Hf _)
         | right _ => None
       end
      | right _ => None
    end
  | right _ => None
end).
move=> a b; by rewrite ffunE.
Defined.

Lemma jtype_choice_pcancel (A B : finType) n :
  pcancel (@JType.f A B n) (@jtype_choice_f A B n).
Proof.
case=> d f Hf H /=.
rewrite /jtype_choice_f /=.
destruct d as [d Hd].
destruct Sumbool.sumbool_of_bool; last by rewrite Hd in e.
destruct Sumbool.sumbool_of_bool; last first.
  exfalso.
  case/card_gt0P : e => a Ha.
  move: e0.
  by rewrite (fdist_card_neq0 (d a)).
set d1 := chan_of_jtype _ _ _.
set d2 := Channel1.mkChan d Hd.
have d12 : d1 = d2.
  apply/Channel1.chan_star_eq.
  rewrite boolp.funeqE => /= a; apply/fdist_ext => b; by rewrite ffunE H.
destruct Sumbool.sumbool_of_bool; last by rewrite Hf in e1.
congr Some; by apply/jtype_eqP => /=.
Qed.

HB.instance Definition _ A B n := @PCanIsCountable _ _ _ _ (@jtype_choice_pcancel A B n).

Definition jtype_pickle (A B : finType) n (P : P_ n (A , B)) : nat.
destruct P as [d t H].
exact: (pickle t).
(*destruct (finfun_countMixin A [finType of {ffun B -> 'I_n.+1}]) as [pi unpi Hcan].
apply pi.
exact t.*)
Defined.

Definition jtype_unpickle (A B : finType) n (m : nat) : option (P_ n ( A , B )).
refine (
    match Sumbool.sumbool_of_bool (0 < #|A|)%N with
      | left Anot0 =>
        match Sumbool.sumbool_of_bool (0 < #|B|)%N with
          |left Bnot0 => _
          | right _ => None
        end
      | right _ => None
    end
).
(*case: (finfun_countMixin A [finType of {ffun B -> 'I_n.+1}]) => pi unpi Hcan.
case: (unpi m); last by exact None.
move=> f.*)
pose unpi : option {ffun A -> {ffun B -> 'I_n.+1}} := unpickle m.
case: unpi; last first.
  exact None.
move=> f.
refine (match Sumbool.sumbool_of_bool (\sum_(a in A) \sum_(b in B) f a b == n)%N with
          | left Hf => _
          | right _ => None
        end).
refine (Some (@JType.mk A B n (chan_of_jtype Anot0 Bnot0 f) f Hf _)).
by move=> a b; rewrite ffunE.
Defined.

Lemma jtype_count_pcancel A B n : pcancel (@jtype_pickle A B n) (@jtype_unpickle A B n).
Proof.
move=> V.
rewrite /jtype_unpickle /jtype_pickle /=.
destruct V as [[c Anot0] f Hf H].
destruct Sumbool.sumbool_of_bool; last by rewrite Anot0 in e.
case/card_gt0P : (e) => a Ha.
move: (fdist_card_neq0 (c a)) => Bnot0.
destruct Sumbool.sumbool_of_bool; last by rewrite Bnot0 in e0.
rewrite pickleK.
(*rewrite pcan_pickleK; last by apply valK.*)
set d1 := chan_of_jtype _ _ _.
have ? : d1 = Channel1.mkChan c Anot0.
  apply/Channel1.chan_star_eq.
  by rewrite boolp.funeqE => a1; apply/fdist_ext => b /=; rewrite ffunE H.
destruct Sumbool.sumbool_of_bool; last by rewrite Hf in e1.
congr Some; by apply/jtype_eqP => /=.
Qed.

HB.instance Definition _ A B n := @PCanIsCountable _ _ _ _ (@jtype_count_pcancel A B n).

Definition jtype_enum_f (A B : finType) n
  (f : { f : {ffun A -> {ffun B -> 'I_n.+1}} | (\sum_(a in A) \sum_(b in B) f a b == n)%N}) :
  option (P_ n ( A , B )).
refine (
    match Sumbool.sumbool_of_bool (0 < #|A|)%N with
      | left Anot0 =>
        match Sumbool.sumbool_of_bool (0 < #|B|)%N with
          |left Bnot0 => _
          | right _ => None
        end
      | right _ => None
    end).
refine (Some (@JType.mk A B n (@chan_of_jtype _ _ Anot0 Bnot0 n (sval f)) (sval f) (proj2_sig f) _)).
by move=> a b; rewrite ffunE.
Defined.

Definition jtype_enum A B n := pmap (@jtype_enum_f A B n)
  (enum (Finite.clone _ { f : {ffun A -> {ffun B -> 'I_n.+1}} | (\sum_(a in A) \sum_(b in B) f a b == n)%N})).

Lemma jtype_enumP A B n : Finite.axiom (@jtype_enum A B n).
Proof.
case=> d f Hf H /=.
have : Finite.axiom (enum (Finite.clone _ { f : {ffun A -> {ffun B -> 'I_n.+1}}  |
    (\sum_(a in A) \sum_(b in B) f a b == n)%N })).
  rewrite enumT; by apply enumP.
move/(_ (@exist _ _ f Hf)) => <-.
rewrite /jtype_enum /=.
rewrite /jtype_enum_f /=.
destruct d as [d Anot0].
case/card_gt0P : (Anot0) => a _.
move: (fdist_card_neq0 (d a)) => Bnot0.
set tmp := pmap _ _.
have -> : tmp = pmap (fun f =>
                        Some {|
                            JType.c := chan_of_jtype Anot0 Bnot0 (sval f);
                            JType.f := (sval f);
                            JType.sum_f := proj2_sig f;
                            JType.c_f := fun a b =>
eq_ind_r
                                     (eq^~ (if (\sum_(b0 in B) sval f a b0)%N == 0%N
                                            then #|B|%:R^-1
                                            else (sval f a b)%:R / (\sum_(b0 in B) sval f a b0)%:R))
                                     (erefl
                                        (if (\sum_(b0 in B) sval f a b0)%N == 0%N
                                         then #|B|%:R^-1
                                         else (sval f a b)%:R / (\sum_(b0 in B) sval f a b0)%:R))
                                     (ffunE
                                        (fun b0 : B =>
                                         if (\sum_(b1 in B) sval f a b1)%N == 0%N
                                         then #|B|%:R^-1
                                         else (sval f a b0)%:R / (\sum_(b1 in B) sval f a b1)%:R) b)
                                             (*(if \sum_(b0 in B) (sval f a) b0 == 0%N
                                              then / #|B|%:R
                                              else
                                                (sval f a b)%:R /
                                                    (\sum_(b0 in B) (sval f a) b0)%:R)*) |}
                     ) (enum (Finite.clone _ { f : {ffun A -> {ffun B -> 'I_n.+1}} |
                                           (\sum_(a in A) \sum_(b in B) f a b)%N == n})).
  apply: eq_pmap => V.
  destruct Sumbool.sumbool_of_bool; last by rewrite Anot0 in e.
  destruct Sumbool.sumbool_of_bool; last by rewrite Bnot0 in e0.
  congr Some.
  by apply/jtype_eqP => /=.
rewrite count_map.
by apply eq_count.
Qed.

HB.instance Definition _ A B n := @isFinite.Build (P_ n (A , B)) _ (@jtype_enumP A B n).

Section jtype_facts.
Variables (A B : finType) (n : nat) (ta : n.-tuple A).

Local Open Scope nat_scope.

Lemma jtype_entry_ub (V : P_ n ( A , B )) b : \sum_(a : A) (JType.f V) a b < n.+1.
Proof.
apply (@leq_ltn_trans (\sum_ (a : A) \sum_ (b : B) (JType.f V) a b)).
- apply leq_sum => a _.
  by rewrite (bigD1 b) //= leq_addr.
- case: V => c f Hf H /=.
  move/eqP in Hf.
  by rewrite Hf.
Qed.

Lemma jtype_0_jtypef (V : P_ n ( A , B )) a b : V a b = 0%R -> (JType.f V) a b = ord0.
Proof.
destruct V as [V1 V2 V3 V4] => /=.
rewrite V4 /=.
case: ifPn => [| H'].
  rewrite sum_nat_eq0.
  move/forallP/(_ b)/implyP/(_ Logic.eq_refl)/eqP => H _; exact: val_inj.
move=> /eqP.
rewrite mulf_eq0 => /orP[|abs].
  rewrite (_ : 0%R = 0%:R)%R// eqr_nat => /eqP ?.
  exact/val_inj.
exfalso.
move/negP : abs; apply.
apply/negP.
rewrite invr_eq0.
rewrite (_ : 0%R = 0%:R)//.
by rewrite eqr_nat.
Qed.

Lemma bound_card_jtype : #| P_ n (A , B) | <= expn n.+1 (#|A| * #|B|).
Proof.
rewrite -(card_ord n.+1) mulnC expnM -2!card_ffun cardE /enum_mem.
apply (@leq_trans (size (map (@ffun_of_jtype A B n) (Finite.enum (P_ n (A, B)))))).
  by rewrite 2!size_map.
rewrite cardE.
apply: uniq_leq_size.
  rewrite map_inj_uniq.
  rewrite -enumT; by apply enum_uniq.
  move=> [c f Hf Hc] [c1 f1 Hf1 Hc1] /= ?; subst f1.
  by apply/jtype_eqP => /=.
move=> /= x.
case/mapP => t Ht Hx.
subst x.
destruct t as [c f Hf cf] => /=.
apply/mapP.
by exists f.
Qed.

Lemma jtype_not_empty : 0 < #|A| -> 0 < #|B| -> 0 < #|P_ n (A , B)|.
Proof.
move=> Anot0 Bnot0.
move: (Anot0); case/card_gt0P => a _.
move: (Bnot0); case/card_gt0P => b _.
apply/card_gt0P.
have [tmp Htmp] : {f : {ffun A -> {ffun B -> 'I_n.+1}} |
                     \sum_(a1 in A) \sum_(b1 in B) f a1 b1 == n}.
  exists [ffun a1 => [ffun b1 => if (a1, b1) == (a, b) then
    Ordinal (ltnSn n) else Ordinal (ltn0Sn n)]].
  rewrite pair_big /=.
  rewrite (bigD1 (a, b)) //= big1 ; first by rewrite 2!ffunE eqxx addn0.
  by move=> p /negbTE Hp ; rewrite 2!ffunE -surjective_pairing Hp.
have Htmp' : (forall a b,
        (chan_of_jtype Anot0 Bnot0 tmp) a b =
        (let ln := \sum_(b0 in B) (tmp a) b0 in
         if ln == 0 then #|B|%:R^-1 else ((tmp a) b)%:R / ln%:R)).
  by move=> a0 b0; rewrite ffunE.
exists (@JType.mk _ _ _ (chan_of_jtype Anot0 Bnot0 tmp) tmp Htmp Htmp').
by rewrite inE.
Qed.

End jtype_facts.

Local Open Scope num_occ_scope.

Section shell_def.

Variables A B : finType.
Variable n : nat.
Variable ta : n.-tuple A.
Variable V : P_ n (A , B).

Local Open Scope nat_scope.

Definition shell :=
  [set tb : n.-tuple B | [forall a, [forall b, N(a, b |ta, tb) == (JType.f V) a b]]].

End shell_def.

Notation "V '.-shell' ta" := (shell ta V) : types_scope.

Section shelled_tuples_facts.

Variables A B : finType.
Variable n' : nat.
Let n := n'.+1.
Variable V : P_ n ( A , B).
Variable ta : n.-tuple A.
Variable tb : n.-tuple B.
Hypothesis Htb : tb \in V.-shell ta.

Lemma occ_co_occ : forall a b, N(a, b| ta, tb) = (JType.f V) a b.
Proof.
move: Htb => Htb' x0 y0 ; rewrite /shell inE in Htb'.
apply/eqP; move: y0; apply/forallP; move: x0; apply/forallP; exact Htb'.
Qed.

Variable P : P_ n ( A ).
Hypothesis Hta : ta \in T_{P}.

Lemma type_co_occ a b :
  ((type.f P) a * (JType.f V) a b = N(a, b | ta, tb) * N(a | ta))%N.
Proof. by rewrite occ_co_occ mulnC (type_numocc Hta a). Qed.

End shelled_tuples_facts.

Section shelled_tuples_perm_facts.

Variables A B : finType.
Variable n : nat.
Variable V : P_ n ( A , B ).
Variable ta : n.-tuple A.
Variable s : 'S_n.

(* NB: Parameter imset : forall aT rT : finType, (aT -> rT) -> mem_pred aT -> {set rT}. *)
Lemma perm_Stuples_Stuples_perm : V.-shell (perm_tuple s ta) = (perm_tuple s) @: (V.-shell ta).
Proof.
rewrite /shell.
apply/eqP.
rewrite eqEsubset.
apply/andP; split; apply/subsetP => y.
- rewrite in_set => H.
  apply/imsetP.
  exists (perm_tuple (s^-1) y); last first.
    by rewrite perm_tuple_comp mulgV perm_tuple_id.
  rewrite in_set.
  apply/forallP => a; move/forallP/(_ a) in H.
  apply/forallP => b; move/forallP/(_ b) in H.
  by rewrite -(num_co_occ_perm _ _ _ _ s) perm_tuple_comp mulgV perm_tuple_id.
- case/imsetP => z.
  rewrite !in_set => H Hy.
  apply/forallP => a; move/forallP/(_ a) in H.
  apply/forallP => b; move/forallP/(_ b) in H.
  subst y.
  by rewrite num_co_occ_perm.
Qed.

Lemma card_shelled_tuples_perm : #| V.-shell ta | = #| V.-shell (perm_tuple s ta) |.
Proof.
rewrite perm_Stuples_Stuples_perm.
symmetry.
apply card_imset.
apply: perm_tuple_inj.
Qed.

End shelled_tuples_perm_facts.

Section sum_num_occ_tuple.

Variables A B : finType.
Variable n : nat.
Variable ta : n.-tuple A.
Variable k : 'I_#|A|.

Local Open Scope nat_scope.

Lemma sum_num_occ_size : forall (a : (sum_num_occ ta k.+1).-tuple B),
  sum_num_occ ta k <= size a.
Proof.
case=> a.
rewrite sum_num_occ_rec /= => /eqP ->.
by rewrite -{1}(addn0 (sum_num_occ ta k)) leq_add2l.
Qed.

Definition cons_tuples : (sum_num_occ ta k).-tuple B * N(enum_val k | ta).-tuple B ->
  (sum_num_occ ta k.+1).-tuple B.
case => a b.
exists [tuple of tval a ++ tval b].
by rewrite size_cat 2!size_tuple sum_num_occ_rec.
Defined.

Definition split_tuple : (sum_num_occ ta k.+1).-tuple B ->
  (sum_num_occ ta k).-tuple B * N(enum_val k | ta).-tuple B.
case => a b.
apply pair.
- apply: (@Tuple _ _ (take (sum_num_occ ta k) a)).
  rewrite size_take.
  move/eqP : b => ->.
  move: (sum_num_occ_inc_loc ta k); rewrite leq_eqVlt; case/predU1P.
  move => <-; by rewrite ltnn.
  by move=> ->.
- apply: (@Tuple _ _ (take N(enum_val k | ta) (drop (sum_num_occ ta k) a))).
  rewrite size_take size_drop.
  move/eqP : b => ->; by rewrite sum_num_occ_rec addKn ltnn.
Defined.

Lemma split_cons_tuples (Z : {set (sum_num_occ ta k.+1).-tuple B})
  (Z' : {set ((sum_num_occ ta k).-tuple B) * N(enum_val k | ta).-tuple B}) :
  forall tb, tb \in Z -> split_tuple tb \in Z' -> tb \in cons_tuples @: Z'.
Proof.
case=> sb Hsb sb_Z sb_Z'.
apply/imsetP.
exists (split_tuple (Tuple Hsb)) => //.
apply val_inj => /=.
rewrite -{1}(cat_take_drop (sum_num_occ ta k) sb).
f_equal.
rewrite take_oversize // size_drop.
clear -Hsb; move/eqP : Hsb => ->.
by rewrite sum_num_occ_rec addKn.
Qed.

Lemma subset_leq_card_split_tuple (Z : {set (sum_num_occ ta k.+1).-tuple B})
  (Z' : {set (sum_num_occ ta k).-tuple B * N(enum_val k | ta).-tuple B}) :
  (forall tb, tb \in Z -> split_tuple tb \in Z') ->
  #|Z| <= #|Z'|.
Proof.
move=> Hincl.
have <- : #| cons_tuples @: Z' | = #|Z'|.
  apply: card_in_imset; case=> [a1 a2] [b1 b2] Ha Hb [] /eqP.
  rewrite eqseq_cat; last by rewrite 2!size_tuple.
  case/andP => /eqP H1 /eqP H2.
  f_equal; by apply val_inj.
apply/subset_leq_card/subsetP => tb Htb.
by apply (split_cons_tuples Htb), Hincl.
Qed.

Hypothesis ta_sorted : sorted (@le_rank _) ta.

Local Open Scope tuple_ext_scope.

Lemma drop_take_is_filter : drop (sum_num_occ ta k) (take (sum_num_occ ta k.+1) ta) =
  filter (pred1 (enum_val k)) ta.
Proof.
apply (@eq_from_nth _ (enum_val k)) => [|i Hi].
  rewrite size_drop size_take size_tuple -/(minn (sum_num_occ ta k.+1) n) minn_sum_num_occ_n.
  by rewrite (sum_num_occ_sub _ k) /num_occ -size_filter.
rewrite size_drop size_take size_tuple -/(minn (sum_num_occ ta k.+1) n) minn_sum_num_occ_n ltn_subRL in Hi.
rewrite nth_drop nth_take => //.
have Hsumk : sum_num_occ ta k + i < n by apply (leq_trans Hi (sum_num_occ_leq_n ta k.+1)).
transitivity (enum_val k).
  transitivity (ta!_(Ordinal Hsumk)).
    by rewrite [in X in _ = X](tnth_nth (enum_val k)).
  apply sum_num_occ_enum_val => //=; by rewrite Hi andbT leq_addr.
rewrite -ltn_subRL (sum_num_occ_sub ta k) in Hi.
by rewrite filter_pred1_num_occ nth_nseq Hi.
Qed.

Hypothesis Bnot0 : (0 < #|B|)%N.

Lemma drop_take_is_filter_zip (tb : n.-tuple B):
  drop (sum_num_occ ta k) (take (sum_num_occ ta k.+1) (zip ta tb)) =
  filter (fun p => p.1 == enum_val k) (zip ta tb).
Proof.
set a := enum_val k.
case/card_gt0P : Bnot0 => b _.
rewrite -(mkseq_nth (a, b) (zip ta tb)) -map_take -map_drop filter_map size_zip 2!size_tuple minnn.
f_equal.
rewrite drop_take_iota; last by rewrite sum_num_occ_inc_loc sum_num_occ_leq_n.
apply eq_in_filter => /= i.
rewrite mem_iota leq0n add0n /= => Hi.
rewrite nth_zip /=; last by rewrite 2!size_tuple.
transitivity (ta!_(Ordinal Hi) == a); by [rewrite -sum_num_occ_is_enum_val | rewrite (tnth_nth a)].
Qed.

Local Close Scope tuple_ext_scope.


Lemma drop_take_is_unzip2_filter (tb : n.-tuple B) :
  drop (sum_num_occ ta k) (take (sum_num_occ ta k.+1) tb) =
  unzip2 (filter (fun ab => ab.1 == enum_val k) (zip ta tb)).
Proof.
transitivity (unzip2 (drop (sum_num_occ ta k) (take (sum_num_occ ta k.+1) (zip ta tb)))).
by rewrite /unzip2 map_drop map_take -/(unzip2 (zip ta tb)) unzip2_zip // 2!size_tuple.
by rewrite drop_take_is_filter_zip.
Qed.

Lemma num_occ_num_co_occ (b : B) (sb : seq B) (tb : n.-tuple B) :
  sb = drop (sum_num_occ ta k) (take (sum_num_occ ta k.+1) tb) ->
  N(b | sb) = N(enum_val k, b | ta, tb).
Proof.
move=> Hsb.
set a := enum_val k.
rewrite /num_co_occ /num_occ // Hsb -!size_filter.
rewrite -(_ : filter (fun p => p.2 == b) (filter (fun p => p.1 == a) (zip ta tb)) =
              filter (pred1 (a, b)) (zip ta tb)) ; last first.
  rewrite -filter_predI /predI; apply eq_in_filter => i Hi /=.
  symmetry; by rewrite andbC {1}(surjective_pairing i) xpair_eqE.
set l1 := drop _ _.
set l2 := filter _ (zip ta tb).
suff -> : l1 = unzip2 l2 by rewrite filter_map size_map.
by rewrite /l1 /l2 {l1 l2} drop_take_is_unzip2_filter.
Qed.

End sum_num_occ_tuple.

Section take_shell_def.

Variables A B : finType.
Variable n : nat.
Variable ta : n.-tuple A.
Variable V : P_ n ( A , B).

Definition take_shell (k : nat) : {set (sum_num_occ ta k).-tuple B} :=
  (fun b : n.-tuple B =>
     tcast (minn_sum_num_occ_n ta k) [tuple of take (sum_num_occ ta k) b])
  @: (V.-shell ta).

(* Same set modulo cast: *)
Lemma full_take_shell : #| take_shell #|A| | = #| V.-shell ta |.
Proof.
apply card_imset; rewrite /injective => /= v v' vv'.
exact: (tcast_take_inj (full_sum_num_occ_n ta (leqnn #|A|)) vv').
Qed.

End take_shell_def.

Section row_num_occ_sect.

Variables (A : finType) (n : nat).
Variable P : P_ n ( A ).
Variable B : finType.
Variable V : P_ n (A , B).

Definition row_num_occ := forall ta, ta \in T_{P} ->
  forall a, (\sum_(b in B) (JType.f V) a b)%N = N(a | ta).

Hypothesis H : row_num_occ.
Variable ta : n.-tuple A.
Hypothesis Hta : ta \in T_{P}.
Variable a : A.
Variable b : B.

Lemma ctyp_element_ub : ((JType.f V) a b < N(a | ta).+1)%N .
Proof. by rewrite ltnS -(H Hta) (bigD1 b) // leq_addr. Qed.

End row_num_occ_sect.

Section take_shell_row_num_occ.
Variables A B : finType.
Variable n : nat.
Variable V : P_ n ( A , B).
Variable P : P_ n ( A ).
Variable ta : n.-tuple A.
Hypothesis Hta : ta \in T_{P}.
Hypothesis Hrow_num_occ : row_num_occ P V.

Local Open Scope nat_scope.

Definition type_of_row (a : A) (Ha : N(a | ta) != 0) : P_ N(a | ta) ( B ).
pose f := [ffun b => Ordinal (ctyp_element_ub Hrow_num_occ Hta a b)].
pose d := [ffun b => ((f b)%:R / N(a | ta)%:R) : Rdefinitions.R].
assert (d0 : forall b, (0 <= d b)%R).
  move=> b.
  by rewrite /d /= ffunE mulr_ge0// invr_ge0.
assert (d1 : (\sum_(b : B) d b = 1)%R).
  under eq_bigr do rewrite ffunE /=.
  rewrite -big_distrl /=.
  rewrite -natr_sum.
  set lhs := \sum_i _.
  suff -> : lhs = N(a | ta).
    by rewrite mulfV // (_ : 0%R = 0%:R)// eqr_nat.
  rewrite /lhs /f /= -[in X in _ = X](Hrow_num_occ Hta a).
  apply eq_bigr => b _; by rewrite ffunE.
by apply (@type.mkType _ _ (FDist.make d0 d1) f) => b; rewrite ffunE.
Defined.

Hypothesis ta_sorted : sorted (@le_rank _) ta.
Hypothesis Bnot0 : (0 < #|B|)%N.

Lemma card_take_shell_incl0 (k : 'I_#|A|) (Ha : 0 = N(enum_val k | ta)) tb :
  tb \in take_shell ta V k.+1 ->
  split_tuple tb \in setX (take_shell ta V k) (set1 (tcast Ha [tuple of ([::] : seq B)])).
Proof.
move=> tbV.
destruct tb as [s Hs].
move: tbV; rewrite /take_shell [in X in X -> _]/= => /imsetP[tb' tb'V].
move/esym/tcast2tval; rewrite [X in X -> _]/= => tb's.
rewrite /split_tuple /= in_setX; apply/andP; split.
- apply/imsetP; exists tb' => //.
  apply/val_inj => /=.
  rewrite eq_tcast /=.
  by rewrite -tb's sum_num_occ_rec take_takel// leq_addr.
- rewrite inE.
  apply/eqP/val_inj => /=.
  by rewrite eq_tcast -Ha take0.
Qed.

Lemma card_take_shell_incl (k : 'I_#|A|) (Ha : N(enum_val k | ta) != 0 ) tb :
  tb \in take_shell ta V k.+1 ->
  split_tuple tb \in setX (take_shell ta V k) (T_{type_of_row Ha}).
Proof.
move=> Hlhs.
destruct tb as [sb Hsb].
rewrite /take_shell /= in Hlhs. move:Hlhs.
case/imsetP => tb Htb_1 Htb_2.
symmetry in Htb_2; move/tcast2tval in Htb_2; rewrite /= in Htb_2.
rewrite /split_tuple /= in_setX.
apply/andP; split.
- apply/imsetP; exists tb => //; apply/val_inj => /=.
  by rewrite eq_tcast /= -Htb_2 sum_num_occ_rec take_takel // leq_addr.
- rewrite in_set.
  set t := Tuple _.
  have Ht : tval t = take N(enum_val k | ta) (drop (sum_num_occ ta k) sb) by [].
  apply/forallP => b.
  rewrite /= ffunE /=.
  move: Htb_1.
  rewrite in_set ffunE.
  move/forallP/(_ (enum_val k))/forallP/(_ b)/eqP => /= H.
  rewrite -{1}H.
  rewrite -Htb_2 in Ht.
  apply/eqP.
  have Ht2 : tval t = drop (sum_num_occ ta k) (take (sum_num_occ ta k.+1) tb).
    rewrite Ht {1}sum_num_occ_rec take_drop take_takel; last by rewrite addnC.
    by rewrite addnC sum_num_occ_rec.
  congr (_ %:R / _%:R).
  exact/esym/num_occ_num_co_occ.
Qed.

Lemma card_take_shell (k : 'I_#|A|) (Ha : N(enum_val k | ta) != 0) :
  #|take_shell ta V k.+1| <= #|take_shell ta V k| * #| T_{type_of_row Ha} |.
Proof.
rewrite -cardX -[X in _ <= X]cardsE.
apply (subset_leq_card_split_tuple (card_take_shell_incl Ha)).
Qed.

Lemma card_take_shell0 (k : 'I_#|A|) (Ha : N(enum_val k | ta) == 0) :
  #|take_shell ta V k.+1| <= #|take_shell ta V k|.
Proof.
move/eqP : (Ha).
move/esym => Ha'.
eapply leq_trans; first by apply (subset_leq_card_split_tuple (card_take_shell_incl0 Ha')).
by rewrite cardsX cards1 muln1.
Qed.

Definition card_type_of_row (i : 'I_#|A|) :=
  match Bool.bool_dec (N(enum_val i | ta) == O) true with
  | left _ => 1
  | right Ha => #| T_{type_of_row (Bool.eq_true_not_negb _ Ha)} |
  end.

Lemma split_nocc_rec : forall k, k <= #|A| ->
  #|take_shell ta V k| <= \prod_ (i < #|A| | i < k) card_type_of_row i.
Proof.
elim.
- move=> _; rewrite big_pred0; last by move=> ? /=; rewrite ltn0.
  rewrite -(expn0 #|B|) -[X in _ <= expn _ X](sum_num_occ_0 ta) -card_tuple -cardsT.
  by apply subset_leq_card, subsetT.
- move=> k IH HSk /=.
  move: (IH (ltnW HSk)) => {}IH.
  rewrite (bigD1 (Ordinal HSk)) //=.
  rewrite (eq_bigl (fun i : 'I_#|A| => i < k) _); last first.
    move=> i /=.
    have [ik|ki] := ltnP i k.
    - have -> : i != Ordinal HSk by rewrite neq_ltn; apply/orP; apply or_introl.
      by rewrite andbC /= ltnW.
    - rewrite andbC -ltn_neqAle.
      by apply/negbTE; rewrite -leqNgt.
  rewrite /card_type_of_row; case: Bool.bool_dec => [e|/Bool.eq_true_not_negb e].
    by rewrite mul1n (leq_trans (card_take_shell0 e)).
  rewrite (leq_trans (card_take_shell e))// mulnC leq_pmul2l //.
  apply/card_gt0P.
  set Q := type_of_row e.
  case: (typed_tuples_not_empty_alt e Q) => tb Htb.
  by exists tb.
Qed.

Lemma card_shelled_tuples_leq_prod_card :
  #| V.-shell ta | <= \prod_ ( i < #|A|) card_type_of_row i.
Proof.
rewrite -full_take_shell.
rewrite [leqRHS](_ : _ = \prod_(i < #|A| | i < #|A|) card_type_of_row i); last first.
  by apply eq_bigl => ?; exact/esym/ltn_ord.
exact (split_nocc_rec (leqnn #|A|)).
Qed.

End take_shell_row_num_occ.

Local Open Scope entropy_scope.

Section card_shell_ub.
Variables (A B : finType) (n' : nat).
Let n := n'.+1.
Variable V : P_ n ( A , B).
Variable P : P_ n ( A ).
Variable ta : n.-tuple A.
Hypothesis Hta : ta \in T_{P}.
Hypothesis Vctyp : row_num_occ P V.
Hypothesis ta_sorted : sorted (@le_rank _) ta.
Hypothesis Bnot0 : (0 < #|B|)%N.

Lemma card_shell_leq_exp_entropy :
  #| V.-shell ta |%:R <= 2 `^ (n%:R * `H(V | P)%channel).
Proof.
rewrite cond_entropy_chanE2.
apply (@le_trans _ _ (\prod_(i < #|A|) card_type_of_row Hta Vctyp i)%:R).
- rewrite ler_nat.
  exact/card_shelled_tuples_leq_prod_card.
- rewrite (mulrC n%:R) powRrM' natr_prod.
  rewrite (@big_morph _ _ (fun r => (2%:R `^ r) ^+ n) 1%R *%R _ +%R _); last 2 first.
    by move=> a b /=;rewrite powR2D exprMn_comm// /GRing.comm mulrC.
    by rewrite powRr0 expr1n.
  rewrite (reindex_onto enum_rank enum_val) => [|i _]; last by rewrite enum_valK.
  rewrite (_ : \prod_(j | enum_val (enum_rank j) == j) _ =
               \prod_(j : A) (card_type_of_row Hta Vctyp (enum_rank j))%:R); last first.
    by apply eq_bigl => a; rewrite enum_rankK; exact/eqP.
  apply ler_prod => a aA; apply/andP; split => //.
  rewrite -powRrM'.
  rewrite /card_type_of_row; case: Bool.bool_dec => [e|/Bool.eq_true_not_negb e].
    rewrite -[X in X <= _](powRr0 2).
    by rewrite gt1_ler_powRr ?ltr1n// !mulr_ge0//; exact: entropy_ge0.
  set pta0 := type_of_row Hta Vctyp _.
  rewrite (_ : _ `^ _ = 2 `^ (N(a | ta)%:R * `H pta0)).
    by rewrite -[in X in _ <= _ _ (X * _)](enum_rankK a); apply card_typed_tuples.
  congr (_ `^ _).
  rewrite mulrC mulrA.
  congr *%R.
  + by rewrite -type_fun_type // (type_numocc Hta).
  + rewrite /entropy.
    congr (- _)%R.
    apply: eq_bigr => b _.
    rewrite /pta0 (JType.c_f V) /= (Vctyp Hta a) -{1 4}(enum_rankK a).
    by move/negbTE : (e) => ->; rewrite !ffunE /= enum_rankK.
Qed.

End card_shell_ub.

(* TODO: move? *)
Lemma map_pred1_nseq {A : eqType} : forall (l : seq A) n a, a \notin l ->
  map (pred1 a) (flatten [seq nseq (n x) x | x <- l]) = nseq (\sum_(i <- l) (n i)) false.
Proof.
elim=> [n0 a Ha /=|h t IH n0 a]; first by rewrite big_nil.
rewrite in_cons negb_or => /andP[H1 H2] /=.
rewrite map_cat IH // (_ : map _ _ = nseq (n0 h) false); last first.
  by rewrite map_nseq /= -(negbTE H1) eqtype.eq_sym.
by rewrite big_cons nseqD.
Qed.

(* TODO: move? *)
Lemma map_filter_nseq_nil {A : eqType} : forall (l : seq A) (p : pred A) n,
  (forall x, x \in l -> ~~ p x) ->
  flatten (map (filter p) (map (fun x => nseq (n x) x) l)) = [::].
Proof.
elim=> // h t IH p n0 H /=.
rewrite IH.
- rewrite cats0.
  transitivity (filter xpred0 (nseq (n0 h) h)).
    apply eq_in_filter => a /nseqP[-> _].
    apply/negP/negP/H; by rewrite in_cons eqxx.
  by rewrite filter_pred0.
by move=> x0 Hx0; rewrite H// in_cons Hx0 orbC.
Qed.

(* TODO: move? *)
Lemma map_filter_pred1_nseq {A : eqType} (a : A) : forall lst n, uniq lst -> a \in lst ->
  flatten (map (filter (pred1 a)) (map (fun x => nseq (n x) x) lst)) = nseq (n a) a.
Proof.
elim=> // h t IH n0 /=.
case/andP=> H1 H2.
rewrite in_cons.
case/predU1P.
  move => ?; subst a.
  rewrite {IH} map_filter_nseq_nil //; last first.
    move=> x0 x0_t /=.
    apply/eqP => ?; subst x0.
    by rewrite x0_t in H1.
  rewrite (_ : filter _ _ = filter xpredT (nseq (n0 h) h)); last first.
    apply eq_in_filter => i /nseqP[-> /= ]; by rewrite eqxx.
  by rewrite filter_predT /= cats0.
move=> a_t.
rewrite IH // (_ : filter _ _ = filter xpred0 (nseq (n0 h) h)); last first.
  apply eq_in_filter => i /nseqP[-> /= _].
  by apply: contraNF H1 => /eqP  ->.
by rewrite filter_pred0.
Qed.

Section shell_not_empty_sorted.
Variables A B : finType.
Variable n : nat.
Variable ta : n.-tuple A.
Hypothesis ta_sorted : sorted (@le_rank A) ta.
Variable V : P_ n ( A , B ).
Variable P : P_ n ( A ).
Hypothesis Hrow_num_occ : row_num_occ P V.
Hypothesis Hta : ta \in T_{P}.

Local Open Scope nat_scope.

Lemma shell_not_empty' : exists sb : seq B,
  exists Hsb : size sb == n, Tuple Hsb \in V.-shell ta.
Proof.
exists (flatten (map (fun a => flatten (map (fun b => nseq (JType.f V a b) b) (enum B))) (enum A))).
set cdom := flatten _.
have /eqP Hy : size cdom = n.
  rewrite size_flatten /shape -map_comp sumn_big_addn big_map [LHS]big_filter.
  rewrite -[RHS](sum_num_occ_all ta).
  rewrite [RHS](reindex_onto enum_rank enum_val) => [|i _] ; last by rewrite enum_valK.
  apply eq_big.
  - move=> ? /=; by rewrite enum_rankK eqxx.
  - move=> a _ /=.
    rewrite [in RHS]enum_rankK.
    rewrite size_flatten /shape -map_comp sumn_big_addn big_map big_filter.
    transitivity (\sum_(b : B) JType.f V a b).
      apply eq_bigr => ? _ /=; by rewrite size_nseq.
    by rewrite (Hrow_num_occ Hta).
exists Hy.
rewrite in_set.
apply/forallP => a.
apply/forallP => b.
rewrite /num_co_occ /num_occ /=.
apply/eqP.
rewrite (@sorted_is_flattened _ _ (@le_rank_trans _)
  (@le_rank_asym _) (@le_rank_refl _) #|A| (enum A) ta) //; last 4 first.
  by rewrite cardE.
  by apply enum_uniq.
  by apply sorted_enum.
  move=> ? _; by rewrite mem_enum.
have -> : [seq filter (pred1 elt) ta | elt <- enum A] = [seq nseq N(x0 | ta) x0 | x0 <- enum A].
  apply eq_in_map => ? _; by rewrite filter_pred1_num_occ.
have sz_flat : forall a, size (flatten [seq nseq (JType.f V a b) b | b <- enum B]) = N(a | ta).
  move=> a'; rewrite size_flatten /shape -map_comp sumn_big_addn big_map.
  rewrite -(Hrow_num_occ Hta a') /= enumT.
  apply eq_bigr => b' _; by rewrite size_nseq.
set dom := flatten _.
have Hdom : size dom = n.
  rewrite /dom size_flatten /shape -map_comp sumn_big_addn big_map.
  rewrite big_filter -[RHS](sum_num_occ_alt ta).
  apply eq_bigr => a' _ /=; by rewrite size_nseq.
move/eqP in Hy.
rewrite -size_filter (_ : filter _ _ = filter
  (predI (fun x => x.2 == b) (fun x => x.1 == a)) (zip dom cdom)); last first.
  apply eq_in_filter; case=> i1 i2 Hi /=; by rewrite xpair_eqE andbC.
rewrite filter_predI (@filter_zip_L _ _ n) //.
have -> : mask (map (pred1 a) dom) cdom = flatten [seq nseq (JType.f V a b) b | b <- enum B].
  have [A1 [A2 A12]] : exists A1 A2, enum A = A1 ++ a :: A2.
    have /splitPr[A1 A2] : a \in enum A by rewrite mem_enum.
    by exists A1, A2.
  rewrite /cdom /dom A12 map_cat flatten_cat map_cat.
  rewrite [in X in mask _ X]map_cat flatten_cat mask_cat; last first.
    rewrite size_map size_flatten /shape -map_comp sumn_big_addn big_map.
    rewrite size_flatten /shape -map_comp sumn_big_addn big_map.
    apply eq_bigr => i _ /=; by rewrite sz_flat size_nseq.
  rewrite (_ : _ :: _ = [:: a] ++ A2) //.
  rewrite map_cat.
  rewrite [in X in _ ++ mask _ X = _]map_cat flatten_cat.
  rewrite mask_cat; last first.
    by rewrite size_map /= cats0 sz_flat size_nseq.
  transitivity (mask (map (pred1 a) (flatten [seq nseq N(a1 | ta) a1 | a1 <- [:: a]]))
     (flatten [seq flatten [seq nseq (JType.f V a1 b1) b1 | b1 <- enum B] | a1 <- [:: a]])).
    move: (enum_uniq A); rewrite A12 cat_uniq /= negb_or /=.
    case/andP => uniqA1 /andP [] /andP [a_A1 _] /andP [a_A2 _].
    rewrite {1}(_ : mask _ _ = [::]); last by rewrite map_pred1_nseq // mask_false.
    rewrite (_ : mask (map _ (flatten [seq _ a | a <- A2])) _ = [::]); last first.
      by rewrite map_pred1_nseq // mask_false.
    by rewrite 3!cats0 cat0s.
  rewrite /= 2!cats0 map_nseq /= eqxx mask_true // sz_flat; by apply eq_leq.
rewrite (@filter_zip_R _ _ N(a | ta)) //; last first.
  rewrite /dom filter_flatten size_flatten /shape -!map_comp sumn_big_addn.
  rewrite big_map (bigD1 a) // big1 /= => [|a1 Ha1].
  - rewrite (_ : filter _ _ = filter (xpredT) (nseq N(a | ta) a)); last first.
      apply eq_in_filter => i /nseqP[-> _]; by rewrite /pred1 /= eqxx.
    by rewrite addn0 filter_predT size_nseq.
  - rewrite (_ : filter _ _ = filter (xpred0) (nseq N(a1 | ta) a1)); last first.
      apply eq_in_filter => j /nseqP[-> _].
      by rewrite /pred1 /= (negbTE Ha1).
    by rewrite filter_pred0.
rewrite size_zip size_mask; last first.
  rewrite size_map /dom sz_flat (_ : filter _ _ = nseq N(a | ta) a); last first.
    by rewrite filter_flatten map_filter_pred1_nseq // ?enum_uniq // ?mem_enum.
  by rewrite size_nseq.
rewrite size_filter.
set x1 := count _ _. set x2 := count _ _.
have -> : x1 = x2 by rewrite /x1 /x2 count_map; apply eq_in_count.
have -> : x2 = JType.f V a b.
  rewrite /x2 -size_filter (_ : filter _ _ = nseq (JType.f V a b) b); last first.
    by rewrite filter_flatten map_filter_pred1_nseq // ?enum_uniq // ?mem_enum.
  by rewrite size_nseq.
exact/minn_idPl.
Qed.

Lemma shell_not_empty_sorted : exists tb, tb \in V.-shell ta.
Proof. by case: (shell_not_empty') => tb [Htb H]; exists (Tuple Htb). Qed.

End shell_not_empty_sorted.

Section shell_not_empty.
Variables A B : finType.
Variable n : nat.
Variable ta : n.-tuple A.
Variable V : P_ n ( A , B ).
Variable P : P_ n ( A ).
Hypothesis Hrow_num_occ : row_num_occ P V.
Hypothesis Hta : ta \in T_{P}.

Local Open Scope nat_scope.

Lemma shell_not_empty : exists tb, tb \in V.-shell ta.
Proof.
case: (tuple_exist_perm_sort (@le_rank A) ta) => s /=.
rewrite /sort_tuple /=.
set t' := Tuple _.
move=> ta_t'.
have t'ta : t' = perm_tuple s^-1 ta.
  by rewrite ta_t' perm_tuple_comp mulVg perm_tuple_id.
have sorted_t' : sorted (@le_rank A) t' by exact/sort_sorted/le_rank_total.
have Ht' : t' \in T_{P} by rewrite t'ta; apply/perm_tuple_in_Ttuples.
case: (shell_not_empty_sorted sorted_t' Hrow_num_occ Ht') => tb Htb.
by exists (perm_tuple s tb); rewrite ta_t' perm_Stuples_Stuples_perm imset_f.
Qed.

End shell_not_empty.

Section cond_type_def.
Variables (A : finType) (n : nat).
Variable P : P_ n ( A ).
Variable B : finType.

Definition cond_type :=
  [set V : P_ n ( A , B ) | [forall ta, (ta \in T_{P}) ==> (V.-shell ta != set0)]].

End cond_type_def.

Notation "'\nu_' n '^{' A ',' B '}' '(' P ')'" :=
  (@cond_type A n P B) : types_scope.
Notation "'\nu^{' B '}' '(' P ')'" := (@cond_type _ _ P B) : types_scope.

Section cond_type_prop.
Variables (A : finType) (n : nat).
Variable P : P_ n ( A ).
Variable B : finType.

Local Open Scope nat_scope.

Lemma card_nu : #|\nu^{B}( P )| <= n.+1 ^ (#|A| * #|B|).
Proof. exact/(leq_trans _ (bound_card_jtype A B n))/subset_leq_card/subsetP. Qed.

Lemma shell_injective (V V' : P_ n (A , B)) (Vctyp : V \in \nu^{B}(P))
  ta (Hta : ta \in T_{P}) : V.-shell ta = V'.-shell ta ->
  forall a b, (JType.f V) a b = (JType.f V') a b.
Proof.
move=> H a b.
rewrite /cond_type in_set in Vctyp.
move/forallP in Vctyp.
move: {Vctyp}(Vctyp ta) => Vctyp.
move/implyP in Vctyp.
move: {Vctyp}(Vctyp Hta) => Vctyp.
case/set0Pn : Vctyp => tb V_tb.
have V'_tb : tb \in V'.-shell ta by rewrite -H.
apply val_inj => /=.
move: V_tb; rewrite in_set => /forallP/(_ a)/forallP/(_ b)/eqP => <-.
move: V'_tb; by rewrite in_set => /forallP/(_ a)/forallP/(_ b)/eqP => <-.
Qed.

End cond_type_prop.

Section cond_type_equiv_sect.
Variables (A : finType) (n : nat).
Variable P : P_ n ( A ).
Variable B : finType.
Variable V : P_ n ( A , B ).

Lemma cond_type_equiv :
  row_num_occ P V <-> [forall ta, (ta \in T_{P}) ==> (V.-shell ta != set0)].
Proof.
split=> H.
- apply/forallP => ta.
  apply/implyP => Hta.
  apply/set0Pn.
  by apply shell_not_empty with P.
- move=> ta Hta a.
  move/forallP : H => /(_ ta)/implyP/(_ Hta).
  case/set0Pn => tb.
  rewrite /shell in_set.
  move/forallP/(_ a)/forallP => H.
  rewrite -(num_co_occ_num_occ ta tb).
  apply eq_bigr => b _.
  by move/eqP : (H b) => <-.
Qed.

End cond_type_equiv_sect.

Local Open Scope fdist_scope.

Module OutType.

Section OutType_sect.
Variables A B : finType.
Variable n' : nat.
Let n := n'.+1.
Variable V : P_ n ( A , B ).

Definition f := [ffun b => (\sum_(a in A) (JType.f V) a b)%:R / n%:R : Rdefinitions.R].

Lemma f0 (b : B) : 0 <= f b.
Proof. rewrite ffunE; apply/divr_ge0; [exact/ler0n | exact: ler0n]. Qed.

Lemma f1 : \sum_(b in B) f b = 1.
Proof.
under eq_bigr do rewrite ffunE /=.
rewrite -big_distrl /=.
rewrite -natr_sum exchange_big /=.
move/eqP : (JType.sum_f V) => ->; rewrite mulfV //.
by rewrite (_ : 0%R = 0%:R)// eqr_nat.
Qed.

Definition d : {fdist B} := FDist.make f0 f1.

Definition P : P_ n ( B ).
refine (@type.mkType _ _ (FDist.make f0 f1) [ffun b => Ordinal (jtype_entry_ub V b)] _).
by move=> b /=; rewrite !ffunE.
Defined.

End OutType_sect.

End OutType.

Notation "'`tO(' V )" := (OutType.P V) : types_scope.

Section output_type_facts.

Variables A B : finType.
Variable n' : nat.
Let n := n'.+1.
Variable V : P_ n ( A , B ).
Variable P : P_ n ( A ).

Lemma shell_subset_output_type ta : V.-shell ta \subset T_{ `tO( V ) }.
Proof.
apply/subsetP => tb; rewrite 2!in_set => Htb.
apply/forallP => b.
apply/eqP.
rewrite /OutType.P /OutType.d /OutType.f ffunE.
do 2 f_equal.
rewrite -(num_co_occ_partial_sum_alt tb ta).
apply eq_bigr => a _.
rewrite num_co_occ_sym.
by move/forallP/(_ a)/forallP/(_ b)/eqP : Htb.
Qed.

Hypothesis Bnot0 : (0 < #|B|)%N.
Hypothesis Vctyp : V \in \nu^{B}(P).

Lemma output_type_out_fdist : forall b, type.d (`tO( V )) b = `O( P , V ) b.
Proof.
rewrite /fdist_of_ffun /= /OutType.d /OutType.f => b /=.
rewrite ffunE.
rewrite natr_sum.
rewrite big_distrl//=.
rewrite fdist_outE; apply eq_bigr => a _.
case: (typed_tuples_not_empty P) => /= ta Hta.
move: (Vctyp).
rewrite in_set.
move/cond_type_equiv/(_ _ Hta a) => sum_V.
rewrite (JType.c_f V) /=.
case: ifP => [/eqP |] Hcase.
  rewrite Hcase in sum_V.
  rewrite in_set in Hta.
  move/forallP/(_ a) : Hta.
  rewrite -sum_V mul0r.
  move/eqP => ->; rewrite mulr0.
  move/eqP in Hcase.
  rewrite sum_nat_eq0 in Hcase.
  move/forallP/(_ b) : Hcase.
  move/implyP/(_ Logic.eq_refl)/eqP => ->.
  by rewrite mul0r.
- rewrite -mulrA sum_V; congr *%R.
  move: Hta; rewrite in_set => /forallP/(_ a)/eqP ->.
  rewrite mulrA mulVf ?div1r// -sum_V.
  by rewrite (_ : 0%R = 0%:R)// eqr_nat Hcase.
Qed.

Lemma output_type_out_entropy : `H (`tO( V )) = `H(P `o V).
Proof.
rewrite /entropy; f_equal.
apply eq_bigr => b _; by rewrite output_type_out_fdist.
Qed.

End output_type_facts.

Section card_perm_shell.
Variables A B : finType.
Variable n' : nat.
Let n := n'.+1.
Variable P : P_ n ( A ).
Variable ta : n.-tuple A.
Variable V : P_ n ( A , B ).
Hypothesis Hta : ta \in T_{P}.
Hypothesis Vctyp : V \in \nu^{B}(P).
Hypothesis Bnot0 : (0 < #|B|)%N.

Lemma card_shelled_tuples : (#| V.-shell ta |%:R <= 2 `^ (n%:R * `H(V | P)%channel))%R.
Proof.
case: (tuple_exist_perm_sort (@le_rank A) ta) => /= s Hta'.
have H : sort (@le_rank _) ta =
  perm_tuple (s^-1) ta by rewrite {2}Hta' perm_tuple_comp mulVg perm_tuple_id.
have {}Hta': ta = perm_tuple s (sort_tuple (@le_rank _) ta) by rewrite {1}Hta'.
rewrite (card_shelled_tuples_perm V ta (s^-1)).
rewrite Hta' perm_tuple_comp mulVg perm_tuple_id.
apply card_shell_leq_exp_entropy => //.
- rewrite in_set.
  apply/forallP => a /=.
  rewrite H num_occ_perm.
  move: a; apply/forallP.
  by move: Hta; rewrite in_set.
- apply cond_type_equiv.
  move: (Vctyp); by rewrite in_set.
- exact/sort_sorted/le_rank_total.
Qed.

End card_perm_shell.

Section shell_partition.
Variables A B : finType.
Variable n' : nat.
Let n := n'.+1.
Local Open Scope fun_scope.
Local Open Scope nat_scope.

(** The stochastic matrix with entries N(a, b | ta, tb): *)

Hypothesis Anot0 : (0 < #|A|)%N.
Hypothesis Bnot0 : (0 < #|B|)%N.

Definition num_co_occ_jtype (ta : n.-tuple A) (tb : n.-tuple B) : P_ n (A , B).
set f := [ffun a => [ffun b => Ordinal (num_co_occ_ub a b ta tb)]].
assert (Hf : \sum_(a in A) \sum_(b in B) f a b == n).
  rewrite /f.
  apply/eqP.
  transitivity (\sum_a \sum_b N(a, b|ta, tb)); last by rewrite num_co_occ_sum.
  apply eq_big => a //= _.
  apply eq_big => b //= _.
  by rewrite 2!ffunE.
assert (H : forall a b,
        (chan_of_jtype Anot0 Bnot0 f) a b =
        (let ln := (\sum_(b0 in B) (f a) b0)%N in
         if ln == O then #|B|%:R^-1 else (((f a) b)%:R / ln%:R))).
  by move=> a b; rewrite ffunE.
exact (@JType.mk _ _ _ (chan_of_jtype Anot0 Bnot0 f) f Hf H).
Defined.

Definition relYn (ta : n.-tuple A) (tb tb' : n.-tuple B) :=
  [forall a, [forall b, N(a, b| ta, tb) == N(a, b|ta, tb')] ].

Lemma reflexive_relYn ta : reflexive (relYn ta).
Proof.
rewrite /reflexive /relYn => tb.
by apply/forallP => a; apply/forallP => b; rewrite eqxx.
Qed.

Variable ta : n.-tuple A.
Variable P : P_ n ( A ).
Hypothesis Hta : ta \in T_{P}.

Definition shell_partition (*: {set set_of_finType [finType of n.-tuple B]}*) :=
  (fun V => V.-shell ta) @: \nu^{B}(P).

Lemma cover_shell : cover shell_partition = [set: n.-tuple B].
Proof.
rewrite /cover /cond_type; apply/setP => tb.
rewrite in_set; apply/bigcupP.
exists (num_co_occ_jtype ta tb).-shell ta.
- apply/imsetP; exists (num_co_occ_jtype ta tb) => //.
  rewrite inE.
  apply cond_type_equiv => ta' Hta' a.
  transitivity (\sum_(b in B) N(a, b | ta, tb)).
  - apply eq_bigr => b _.
    by rewrite /num_co_occ_jtype /= 2!ffunE.
  - rewrite num_co_occ_partial_sum_alt.
    move: Hta'; rewrite in_set => /forallP/(_ a)/eqP => Hta'.
    move: Hta.
    rewrite in_set => /forallP/(_ a)/eqP.
    rewrite Hta'.
    move=> /(congr1 (fun x => x * n%:R)%R).
    rewrite -!mulrA mulVf ?mulr1; last first.
      by rewrite (_ : 0%R = 0%:R)// eqr_nat.
    by move=> /eqP; rewrite eqr_nat => /eqP.
- rewrite in_set.
  apply/forallP => a. apply/forallP => b.
  by rewrite /num_co_occ_jtype /= 2!ffunE.
Qed.

Lemma trivIset_shell' tb tb' V : tb \in V.-shell ta ->
  tb' \in V.-shell ta = relYn ta tb' tb.
Proof.
rewrite 2!in_set => H.
rewrite /relYn.
apply eq_forallb => a; apply eq_forallb => b; move: H.
by move/forallP/(_ a)/forallP/(_ b)/eqP => ->.
Qed.

Lemma trivIset_shell : trivIset shell_partition.
Proof.
apply/trivIsetP => S1 S2; case/imsetP => V1 _ HS1; case/imsetP => V2 _ HS2 HS12.
subst S1 S2.
rewrite /disjoint.
apply/pred0P => tb /=.
apply/negP/negP.
move: tb.
apply/forallP; rewrite -negb_exists; apply/negP;
  case/existsP => tb /andP [H1 H2]; contradict HS12.
apply/negP/negPn/eqP/setP => ?.
rewrite 2!(@trivIset_shell' tb) //.
exact: reflexive_relYn.
Qed.

End shell_partition.

Section sum_tuples_ctypes.
Context {R : ringType}.
Variables (A B : finType) (n' : nat).
Let n := n'.+1.
Variable ta : n.-tuple A.
Variable P : P_ n ( A ).
Hypothesis Hta : ta \in T_{P}.
Local Open Scope ring_scope.

Let sum_tuples_ctypes'' (f : _ -> R) :
  \sum_(S | S \in shell_partition B ta P) \sum_(tb in S) f tb =
  \sum_(V | V \in \nu^{B}(P)) \sum_ (tb in V.-shell ta) f tb.
Proof.
rewrite big_imset // => V V' HV HV' /=.
move/(shell_injective _) => /(_ P HV Hta) V_V' {HV HV'}.
case : V V_V' => /= c fV HfV Hc HVV'.
case : V' HVV' => /= c' fV' HfV' Hc' fV_fV'.
have ? : fV = fV' by apply/ffunP => a; apply/ffunP => b; rewrite fV_fV'.
subst fV.
by apply/jtype_eqP => /=.
Qed.

Hypothesis Anot0 : (0 < #|A|)%N.
Hypothesis Bnot0 : (0 < #|B|)%N.

Let sum_tuples_ctypes' f : \sum_ (tb : _ ) (f : _ -> R) tb =
  \sum_ (V | V \in \nu^{B}(P)) \sum_ (tb in V.-shell ta) f tb.
Proof.
transitivity (\sum_ (tb in [set: n.-tuple B]) f tb).
  by apply eq_bigl => tb; rewrite in_set.
rewrite -(cover_shell Anot0 Bnot0 Hta) -sum_tuples_ctypes''// big_trivIset//.
exact: trivIset_shell.
Qed.

Lemma sum_tuples_ctypes f F :
  \sum_(tb | F tb) f tb =
  \sum_(V | V \in \nu^{B}(P)) \sum_ (tb in V.-shell ta | F tb) f tb :> R.
Proof.
rewrite big_mkcond /=.
transitivity (\sum_(V | V \in \nu^{B}(P)) \sum_(tb in V.-shell ta)
    if F tb then f tb else 0).
  exact: sum_tuples_ctypes'.
apply eq_bigr => s _.
rewrite [in LHS]big_mkcond /= [in RHS]big_mkcond /=.
apply/esym/eq_bigr => tb _.
by case/boolP : (tb \in s.-shell ta).
Qed.

End sum_tuples_ctypes.
