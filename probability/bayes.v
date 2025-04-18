(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
Require Import PeanoNat.
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix reals.
From mathcomp Require boolp.
Require Import ssr_ext ssralg_ext bigop_ext realType_ext.
Require Import fdist proba.

(**md**************************************************************************)
(* WIP towards the proof of BN_factorization.                                 *)
(*                                                                            *)
(* Main definitions:                                                          *)
(* - RV_equiv                                                                 *)
(* - univ_types / prod_types                                                  *)
(* - preim_vars                                                               *)
(* - cinde_preim                                                              *)
(* - bayesian network (Koller & Friedmann p 57)                               *)
(*                                                                            *)
(* Main theorems:                                                             *)
(* - cinde_preim_ok                                                           *)
(* - prod_vars1                                                               *)
(* - cinde_preim_equiv                                                        *)
(*                                                                            *)
(******************************************************************************)

Local Open Scope tuple_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import Num.Theory.
Import GRing.Theory.

Section fin_img.
Variables (T : finType) (S : eqType) (f : T -> S).

Definition Tfin_img := 'I_(size (fin_img f)).
Definition index_fin_img x (H : x \in fin_img f) : Tfin_img.
apply (@Ordinal _ (index x (fin_img f))).
abstract (by rewrite index_mem).
Defined.
Definition map_fin_img (x : T) : Tfin_img.
refine (@index_fin_img (f x) _).
abstract (by rewrite mem_undup map_f // mem_enum).
Defined.
Definition nth_fin_img (i : Tfin_img) : S := tnth (in_tuple (fin_img f)) i.
Definition rev_fin_img (i : Tfin_img) : T.
refine (iinv (A:=predT) (f:=f) (y:=nth_fin_img i) _).
abstract (move/mem_nth: (ltn_ord i); rewrite -mem_undup; exact).
Defined.
Lemma nth_fin_imgK x : nth_fin_img (map_fin_img x) = f x.
Proof.
rewrite /nth_fin_img /index_fin_img => /=.
by rewrite (tnth_nth (f x)) nth_index // mem_undup map_f // mem_enum.
Qed.
Lemma rev_fin_imgK i : map_fin_img (rev_fin_img i) = i.
Proof.
case: i => i isz; apply val_inj => /=.
by rewrite f_iinv nthK // undup_uniq.
Qed.
Lemma map_fin_imgK x : f (rev_fin_img (map_fin_img x)) = f x.
Proof. by rewrite /rev_fin_img f_iinv nth_fin_imgK. Qed.
Lemma fin_imgP y : reflect (exists x : T, y = f x) (y \in fin_img f).
Proof.
rewrite mem_undup; apply/(iffP mapP) => -[x].
- move=> _ ->. by exists x.
- move=> ->. by exists x; rewrite // mem_enum.
Qed.
End fin_img.

Section proba. (* proba.v ? *)
Variables (R : realType) (U : finType) (P : R.-fdist U).

Definition fdist_choice' : U.
move: (fdist_card_neq0 P).
move He: (enum U) => [|u l] //.
move/(f_equal size): He.
by rewrite -cardE => ->.
Defined.
Definition fdist_choice := Eval hnf in fdist_choice'.

Definition rvar_choice (A : eqType) (X : {RV P -> A}) := X fdist_choice.

Section RV_equiv.
Variables A B : eqType.
Variables (X : {RV P -> A}) (Y : {RV P -> B}).
Definition cancel_both (fg : (A -> B) * (B -> A)) :=
  cancel fg.1 fg.2 /\ cancel fg.2 fg.1.

Definition RV_equiv := {fg | cancel_both fg & Y =1 fg.1 \o X}.
End RV_equiv.

Lemma RV_equivC (A B : eqType) (X : {RV P -> A}) (Y : {RV P -> B}) :
  RV_equiv X Y -> RV_equiv Y X.
Proof.
case=> -[f g] []/= cfg cgf Hf.
exists (g,f) => //.
move=> u /=.
move/(f_equal g): (Hf u).
by rewrite cfg.
Qed.
End proba.

Section univ_types.
(* heterogeneous types *)
Variable n : nat.
Variable types : 'I_n -> eqType.
Definition univ_types : eqType :=
  [the eqType of {dffun forall i, types i}].

Section prod_types.
(* sets of indices *)
Variable I : {set 'I_n}.

Definition prod_types :=
  [the eqType of
   {dffun forall i : 'I_n, if i \in I then types i else unit}].

Lemma prod_types_app i (A B : prod_types) : A = B -> A i = B i.
Proof. by move=> ->. Qed.

Lemma prod_types_out (i : 'I_n) (A B : prod_types) : i \notin I -> A i = B i.
Proof.
move=> Hi.
move: (A i) (B i).
by rewrite (negbTE Hi) => -[] [].
Qed.

Lemma prod_types_neq (A B : prod_types) :
  A != B -> exists i, (i \in I) && (A i != B i).
Proof.
move=> AB.
case /boolP: [forall i, A i == B i].
  move/forallP => /= AB'.
  elim: (negP AB).
  apply/eqP/ffunP => /= x.
  by apply/eqP.
rewrite negb_forall => /existsP [x Hx].
exists x.
rewrite Hx.
case/boolP: (x \in I) => //= xe.
elim: (negP Hx).
move: (A x) (B x) {AB Hx} => /=.
by rewrite (negbTE xe) => -[] [].
Qed.

Definition set_vals' (v : prod_types) (vals : univ_types) : univ_types.
refine [ffun j => _].
case: (j \in I) (v j) => a.
- exact: a.
- exact: vals j.
Defined.
Definition set_vals : prod_types -> univ_types -> univ_types :=
  Eval hnf in set_vals'.

Lemma set_vals_hd vs2 (v : prod_types) vs1 i :
  i \in I -> set_vals v vs1 i = set_vals v vs2 i.
Proof. rewrite !ffunE; by case: (i \in I) (v i). Qed.

Lemma set_vals_tl (v : prod_types) vs i :
  i \notin I -> set_vals v vs i = vs i.
Proof. rewrite !ffunE; by case: (i \in I) (v i). Qed.

Lemma set_vals_id (v : prod_types) vs :
  set_vals v (set_vals v vs) = set_vals v vs.
Proof.
apply/ffunP => i.
case/boolP: (i \in I) => [/set_vals_hd | /set_vals_tl ->]; exact.
Qed.

Definition prod_vals' (vals : univ_types) : prod_types.
refine [ffun i => _].
move: (vals i).
case: (i \in I) => a.
- exact: a.
- exact: tt.
Defined.
Definition prod_vals vals : prod_types := Eval hnf in prod_vals' vals.

Lemma set_vals_prod_vals_id vals i :
  set_vals (prod_vals vals) vals i = vals i.
Proof. rewrite !ffunE; by case: (i \in _) (vals i). Qed.

Lemma set_vals_prod_vals vals vals' i :
  i \in I -> set_vals (prod_vals vals) vals' i = vals i.
Proof. rewrite !ffunE => ie. move: (vals i); by rewrite ie. Qed.

Lemma prod_vals_eqP vals1 vals2 i :
  prod_vals vals1 i = prod_vals vals2 i <-> (i \in I -> vals1 i = vals2 i).
Proof.
split; rewrite !ffunE; case: (i \in I) (vals1 i) (vals2 i) => // v1 v2; exact.
Qed.

Lemma prod_vals_eq (vals1 vals2 : univ_types) i :
  (i \in I -> vals1 i = vals2 i) -> prod_vals vals1 i = prod_vals vals2 i.
Proof. move=> Hi; exact/prod_vals_eqP. Qed.

Lemma set_vals_eq (A B : prod_types) vals i :
  set_vals A vals i == set_vals B vals i = (A i == B i) || (i \notin I).
Proof.
rewrite !ffunE.
case: (i \in I) (A i) (B i) => a b.
- by rewrite orbF.
- by rewrite eqxx orbT.
Qed.

Lemma set_vals_inj (A B : prod_types) vals i :
  set_vals A vals i = set_vals B vals i -> A i = B i.
Proof.
set goal := _ -> _.
case/boolP: (i \in I) => Hi; subst goal.
  move/eqP; rewrite set_vals_eq orbC.
  by move: (A i) (B i); rewrite Hi => a b /= /eqP.
move=> _; exact: prod_types_out.
Qed.

Lemma prod_vals_set_vals (A : prod_types) vals :
  prod_vals (set_vals A vals) = A.
Proof.
apply/ffunP => j.
apply (set_vals_inj (vals := vals)).
case/boolP: (j \in I) => Hj.
  by rewrite set_vals_prod_vals.
by rewrite !set_vals_tl.
Qed.

End prod_types.

Lemma set_vals_prod_vals_join (I J : {set 'I_n}) vals vals' :
  set_vals (prod_vals I vals) (set_vals (prod_vals J vals) vals') =
  set_vals (prod_vals (I :|: J) vals) vals'.
Proof.
apply/ffunP => i.
case/boolP: (i \in I) => iI.
  by rewrite !set_vals_prod_vals // inE iI.
rewrite set_vals_tl //.
case/boolP: (i \in J) => iJ.
  by rewrite !set_vals_prod_vals // inE iJ orbT.
by rewrite !set_vals_tl // inE negb_or iI.
Qed.

Lemma set_valsC I J (A : prod_types I) (B : prod_types J) V :
  [disjoint I & J] -> set_vals A (set_vals B V) = set_vals B (set_vals A V).
Proof.
move/setDidPl/setP => Disj.
apply/ffunP => /= i.
case/boolP: (i \in I) => iI.
  move: (Disj i); rewrite inE iI andbT => /set_vals_tl ->.
  by rewrite (set_vals_hd V).
case/boolP: (i \in J) => iJ.
  by rewrite set_vals_tl //; apply set_vals_hd.
by rewrite !set_vals_tl.
Qed.

Section set_val.
Definition set_val (i : 'I_n) (v : types i) (vals : univ_types) : univ_types :=
  [ffun j : 'I_n =>
    match Nat.eq_dec i j return types j with
    | left ij => eq_rect i (fun i => (types i : Type)) v j (ord_inj ij)
    | right _ => vals j
    end].

Lemma eq_dec_refl i : Nat.eq_dec i i = left (erefl i).
Proof.
case: Nat.eq_dec => Hi; last by elim Hi.
congr left; by rewrite (Eqdep_dec.UIP_refl_nat _ Hi).
Qed.

Definition ord_eq_dec (i j : 'I_n) : {i = j}+{i <> j}.
case (Nat.eq_dec i j); intro ij.
- left; now apply ord_inj.
- right; intro ij'; apply ij; now f_equal.
Defined.

Lemma set_val_hd i (v : types i) vs : set_val v vs i = v.
rewrite ffunE eq_dec_refl -Eqdep_dec.eq_rect_eq_dec //; exact: ord_eq_dec.
Qed.

Lemma set_val_tl i (v : types i) vs j : i <> j -> set_val v vs j = vs j.
rewrite ffunE => nij; case: Nat.eq_dec => ij //; elim nij; exact: ord_inj.
Qed.
End set_val.

End univ_types.


Module BN.
Section bn.
Variables (R : realType) (U : finType) (P : R.-fdist U) (n : nat).

Section preim.
Variable types : 'I_n -> eqType.
Variable vars : forall i, {RV P -> types i}.

Definition vals0 : univ_types types := [ffun i => rvar_choice (vars i)].

Definition wrap_set_vals I := f_equal (set_vals (I:=I) ^~ vals0).

Section prod_vars.
Variable I : {set 'I_n}.

Definition vals_at (u : U) : univ_types types := [ffun i => vars i u].

Definition prod_vars : {RV P -> prod_types types I} :=
  fun u => prod_vals I (vals_at u).

Lemma set_vals_prod_vars vals u i :
  i \in I -> set_vals (prod_vars u) vals i = vars i u.
Proof. move=> Hi; by rewrite set_vals_prod_vals // ffunE. Qed.
End prod_vars.

Lemma prod_vars_inter (I J : {set 'I_n}) vals i u :
  i \in I -> i \in J ->
  set_vals (prod_vars I u) vals i = set_vals (prod_vars J u) vals i.
Proof. move=> *; by rewrite !set_vals_prod_vals. Qed.

Lemma prod_vars1 (i : 'I_n) : RV_equiv (prod_vars [set i]) (vars i).
Proof.
exists ((fun A : prod_types types [set i] => set_vals A vals0 i),
        prod_vals [set i] \o set_val (i:=i) ^~ vals0).
  split => x /=.
    apply/ffunP => /= j.
    apply (set_vals_inj (vals := vals0)).
    case/boolP: (j \in [set i]) => Hj; last by rewrite !set_vals_tl.
    rewrite set_vals_prod_vals //.
    rewrite inE in Hj.
    move/eqP: Hj (set_vals _ _) => -> v.
    by rewrite set_val_hd.
  by rewrite set_vals_prod_vals ?inE // set_val_hd.
move=> u /=.
by rewrite set_vals_prod_vars // inE.
Qed.

Lemma cancel_both_disjoint (I J : {set 'I_n}) :
  [disjoint I & J] ->
  cancel_both
    ((fun A : prod_types types (I :|: J) =>
        (prod_vals I (set_vals A vals0), prod_vals J (set_vals A vals0))),
     (fun A : prod_types types I * prod_types types J =>
        prod_vals (I :|: J) (set_vals (fst A) (set_vals (snd A) vals0)))).
Proof.
move=> Disj; split => [A | [A B]] /=.
  by rewrite set_vals_prod_vals_join !prod_vals_set_vals.
congr pair; last rewrite setUC set_valsC //;
by rewrite -set_vals_prod_vals_join !prod_vals_set_vals.
Qed.

Lemma prod_vars_pair (I J : {set 'I_n}) :
  [disjoint I & J] ->
  RV_equiv (prod_vars (I :|: J)) [% prod_vars I, prod_vars J].
Proof.
move=> Disj.
esplit. exact: cancel_both_disjoint.
move=> u /=.
congr pair; apply/ffunP => i; apply prod_vals_eq => Hi;
  rewrite set_vals_prod_vars ?ffunE //; by rewrite inE Hi ?orbT.
Qed.

Definition preim_vars (I : {set 'I_n}) (vals : forall i, types i) :=
  \bigcap_(i in I) finset (vars i @^-1 (vals i)).

Definition cinde_preim (e f g : {set 'I_n}) :=
  forall vals : univ_types types,
    cinde_events P (preim_vars e vals)
                   (preim_vars f vals)
                   (preim_vars g vals).

Lemma cinde_eventsC A (Q : R.-fdist A) (E F G : {set A}) :
  cinde_events Q E F G -> cinde_events Q F E G.
Proof. by rewrite /cinde_events => Hef; rewrite setIC GRing.mulrC. Qed.

Lemma cinde_preimC (e f g : {set 'I_n}) :
  cinde_preim e f g  -> cinde_preim f e g.
Proof. move=> Hef vals; exact: cinde_eventsC. Qed.

Lemma preim_varsP  (I : {set 'I_n}) vals u :
  reflect (forall i, i \in I -> vars i u = vals i) (u \in preim_vars I vals).
Proof. by apply/(iffP bigcapP) => H i /H; rewrite !inE => /eqP. Qed.

Lemma preim_prod_vars (g : {set 'I_n}) (C : prod_types types g) vals :
  finset (prod_vars g @^-1 C) = preim_vars g (set_vals C vals).
Proof.
apply/setP => x; rewrite !inE.
apply/esym/preim_varsP; case: ifP.
- move/eqP => <- i ig.
  by rewrite set_vals_prod_vals // ffunE.
- move/negP => /= Hf Hcap; elim: Hf.
  apply/eqP/ffunP => /= i.
  rewrite /prod_vars (prod_vals_eq (vals2:=set_vals C vals)).
    by rewrite prod_vals_set_vals.
  rewrite ffunE; exact: Hcap.
Qed.

(* Simple version, using singletons *)

Lemma Rxx2 (x : R) : x = x * x -> x = 0 \/ x = 1.
Proof.
case/boolP: (x == 0) => Hx.
  rewrite (eqP Hx); by left.
move/(f_equal (GRing.mul ^~ x^-1)).
by rewrite mulrV ?unitfE // -mulrA mulrV ?unitfE // mulr1 => <-; right.
Qed.

Lemma cinde_preim_ok1 (i j k : 'I_n) :
  cinde_preim [set i] [set j] [set k] <-> P |= (vars i) _|_ (vars j) | (vars k).
Proof.
rewrite /cinde_preim /preim_vars.
split.
- move=> Hpreim.
  apply/cinde_RV_events => a b c.
  set vals := set_val a (set_val c (set_val b vals0)).
  have vi : vals i = a by rewrite /vals set_val_hd.
  move: (erefl vals) {Hpreim} (Hpreim vals).
  rewrite {2}/vals /cinde_events; clearbody vals.
  rewrite !big_set1.
  wlog: c / vals k = c.
    case: (ord_eq_dec i k) c vi.
      move=> <- {k} c vi.
      case ac: (a == c).
        rewrite -(eqP ac); exact.
      move=> _ _ _.
      rewrite (proj2 (cPr_eq0P _ _ _)); last first.
        apply/Pr_set0P => u.
        by rewrite !inE => /andP [] /andP [] /= /eqP ->; rewrite ac.
      rewrite (proj2 (cPr_eq0P _ _ _)); last first.
        apply/Pr_set0P => u.
        by rewrite !inE => /andP [] /= /eqP ->; rewrite ac.
      by rewrite mul0r.
    move=> nik c vi HG Hvals; apply: HG => //.
    by rewrite Hvals set_val_tl // set_val_hd.
  move=> vk.
  wlog: b / vals j = b.
    case: (ord_eq_dec i j) b.
      move=> <- {j} b.
      case ab: (a == b).
        rewrite -(eqP ab); exact.
      move=> _ _.
      rewrite setIid vi vk.
      set x := (X in X = X * X).
      move/Rxx2 => [] Hx.
        rewrite -/x Hx.
        rewrite (proj2 (cPr_eq0P _ _ _)) ?GRing.mul0r //.
        apply/Pr_set0P => u.
        by rewrite !inE => /andP [] /andP [] /= /eqP ->; rewrite ab.
      rewrite /cPr.
      set den := (X in _ / X).
      case/boolP: (den == 0) => /eqP Hden.
        by rewrite setIC Pr_domin_setI // setIC Pr_domin_setI // !GRing.mul0r.
      set num := (X in _ * (X / _)).
      case/boolP: (num == 0) => /eqP Hnum.
        by rewrite -setIA setIC Pr_domin_setI // Hnum !GRing.mul0r GRing.mulr0.
      elim Hnum.
      apply/Pr_set0P => u.
      rewrite !inE => /andP [] /= Hi Hk.
      move: Hx; subst x.
      move/(f_equal (GRing.mul ^~ den)).
      move/eqP in Hden.
      rewrite /cPr -mulrA mulVr ?unitfE // mulr1 mul1r.
      move/(f_equal (fun x => den - x)).
      rewrite subrr setIC -Pr_setD => /Pr_set0P/(_ u).
      by rewrite !inE (eqP Hi) Hk eq_sym ab; exact.
    case: (ord_eq_dec k j).
      move=> <- {j} ik b.
      case bc: (b == c).
        rewrite (eqP bc); exact.
      move=> _ _ _.
      rewrite (proj2 (cPr_eq0P _ _ _)); last first.
        apply/Pr_set0P => u.
        by rewrite !inE => /andP [] /andP [] _ /= /eqP ->; rewrite bc.
      rewrite GRing.mulrC (proj2 (cPr_eq0P _ _ _)) ?GRing.mul0r //.
      by apply/Pr_set0P => u; rewrite !inE => /andP [] /= /eqP ->; rewrite bc.
    move=> nkj nij b HG Hvals; apply: HG => //.
    by rewrite Hvals set_val_tl // set_val_tl // set_val_hd.
  by rewrite vi vk => -> _.
- move=> Hdrv vals.
  move/cinde_RV_events/(_ (vals i) (vals j) (vals k)): Hdrv.
  by rewrite !big_set1.
Qed.

(* Now start the hard version, using sets of variables *)

Lemma preim_vars_set_vals_tl (g e : {set 'I_n}) (A : prod_types types e) vals :
  e :&: g = set0 ->
  preim_vars g (set_vals A vals) = preim_vars g vals.
Proof.
move=> /setP eg.
apply/eq_bigr => /= i ig.
apply/setP => u.
rewrite !inE set_vals_tl //.
by move: (eg i); rewrite !inE ig andbT => ->.
Qed.

Lemma preim_inter (T S : eqType) (e : U -> T) (g : U -> S) (A : T) (C : S) :
  finset (preim (fun x => (e x, g x)) (pred1 (A, C))) =
  finset (preim e (pred1 A)) :&: finset (preim g (pred1 C)).
Proof.
apply/setP => u; rewrite !inE.
apply/andP => /=.
by case: ifPn => [/andP | /negP H /andP /H].
Qed.

Lemma preim_vars_inter (e f : {set 'I_n}) vals :
  preim_vars (e :|: f) vals = preim_vars e vals :&: preim_vars f vals.
Proof. by rewrite /preim_vars bigcap_setU. Qed.

Lemma preim_vars_vals (e : {set 'I_n}) (A : prod_types types e) vals1 vals2 :
  (forall x, x \in e -> vals1 x = vals2 x) ->
  preim_vars e vals1 = preim_vars e vals2.
Proof.
move=> Hvals.
apply/eq_bigr => /= i ie.
by apply/setP => u; rewrite !inE Hvals.
Qed.

Lemma disjoint_preim_vars (e f : {set 'I_n}) (A B : prod_types types f) vals :
  f \subset e -> A != B ->
  [disjoint preim_vars e (set_vals A vals) & preim_vars e (set_vals B vals)].
Proof.
move=> fe AB.
rewrite -setI_eq0.
apply/eqP/setP => u.
rewrite !inE.
apply/negP => /andP [] /preim_varsP /= HA /preim_varsP /= HB.
case: (prod_types_neq AB) => /= i /andP [Hif HAB].
have ie : i \in e by move/subsetP: fe; apply.
move/(_ _ ie)/eqP: HB.
rewrite HA // set_vals_eq => /orP [] H.
- by rewrite H in HAB.
- by rewrite Hif in H.
Qed.

Lemma Pr_preim_vars_sub (e f : {set 'I_n}) (vals : univ_types types) :
  f \subset e ->
  Pr P (preim_vars (e :\: f) vals) =
  \sum_(A : Tfin_img (prod_vars f))
   Pr P (preim_vars e (set_vals (nth_fin_img A) vals)).
Proof.
rewrite /Pr => fe.
rewrite -partition_disjoint_bigcup; last first.
  move=> /= A B.
  rewrite -(tnth_uniq A B (t:=in_tuple _)) ?undup_uniq => // AB.
  exact: disjoint_preim_vars.
apply/eq_bigl => u.
apply/esym/bigcupP/(equivPif idP).
  move=> [A _ /preim_varsP HA].
  apply/preim_varsP => /= i /setDP [/HA -> Hif].
  by rewrite set_vals_tl.
move=> /= /preim_varsP /= Hu.
exists (map_fin_img (prod_vars f) u) => //.
apply/preim_varsP => /= i ie.
case/boolP: (i \in f) => Hif.
  by rewrite nth_fin_imgK set_vals_prod_vars.
by rewrite set_vals_tl // Hu // inE Hif.
Qed.

Ltac cases_in i :=
  rewrite ?inE; do !case: (i \in _) => //=;
  try by do! (move/(_ isT) => // || move=> _).

Lemma cinde_preim_sub (e e' f g : {set 'I_n}) :
  e :&: (f :|: g) \subset e' -> e' \subset e ->
  cinde_preim e f g -> cinde_preim e' f g.
Proof.
rewrite /cinde_preim => ee' e'e Hef vals.
have ee'g : (e :\: e') :&: g = set0.
  apply/setP => i; move/subsetP/(_ i): ee'; by cases_in i.
transitivity (\sum_(A : Tfin_img (prod_vars (e :\: e')))
          let v := set_vals (nth_fin_img A) vals in
          `Pr_P[preim_vars e v :&: preim_vars f v | preim_vars g v]).
  rewrite /cPr -!preim_vars_inter.
  have -> : e' :|: f :|: g = (e :|: f :|: g) :\: (e :\: e').
    apply/setP => i.
    move/subsetP/(_ i): e'e.
    move/subsetP/(_ i): ee'.
    by cases_in i.
  rewrite Pr_preim_vars_sub; last by apply/subsetP=> i; cases_in i.
  rewrite big_distrl; apply eq_bigr => A _ /=.
  by rewrite -!preim_vars_inter (@preim_vars_set_vals_tl g).
under eq_bigr => A _ /=.
  rewrite Hef (@preim_vars_set_vals_tl g) // (@preim_vars_set_vals_tl f).
    over.
  apply/setP => i; move/subsetP/(_ i): ee'; by cases_in i.
rewrite -2!big_distrl /=.
rewrite [in RHS]/cPr.
congr (_ * _ * _).
rewrite -preim_vars_inter.
have -> : e' :|: g = (e :|: g) :\: (e :\: e').
  apply/setP => i.
  move/subsetP/(_ i): e'e.
  move/subsetP/(_ i): ee'.
  by cases_in i.
rewrite Pr_preim_vars_sub; last by apply/subsetP=> i; cases_in i.
apply eq_bigr => A _.
by rewrite preim_vars_inter (@preim_vars_set_vals_tl g) //.
Qed.

Lemma cinde_preim_inter e f g :
  cinde_preim e f g -> cinde_preim (e :&: f) (e :&: f) g.
Proof.
move=> Hp.
have Hp2 : cinde_preim (e :\: (e :\: f :\: g)) f g.
  apply (@cinde_preim_sub e) => // ;
    apply/subsetP => j; by cases_in j.
have : cinde_preim (e :\: (e :\: f :\: g)) (f :\: (f :\: e :\: g)) g.
  move/cinde_preimC in Hp2.
  apply/cinde_preimC.
  apply (@cinde_preim_sub f) => // ;
    apply/subsetP => j; by cases_in j.
move=> {}Hp vals.
move/(_ vals): Hp.
rewrite /cinde_events /cPr /Pr -!preim_vars_inter.
rewrite (_ : _ :|: g = (e :&: f) :|: g);
  last by apply/setP => j; cases_in j.
rewrite 2!(_ : _ :\: _ :|: _ = (e :&: f) :|: g);
  try by apply/setP => j; cases_in j.
by rewrite setUid.
Qed.

Section cinde_preim_lemmas.
Variables e f g : {set 'I_n}.
Variables (A : prod_types types e) (B : prod_types types f)
          (C : prod_types types g).
Lemma cinde_events_vals :
  [forall i in (e :&: g), set_vals C vals0 i == set_vals A vals0 i] \/
  cinde_events P (finset (prod_vars e @^-1 A)) (finset (prod_vars f @^-1 B))
                 (finset (prod_vars g @^-1 C)).
Proof.
case /boolP: [forall i in (e :&: g), _].
  by left.
rewrite negb_forall => /existsP [i].
rewrite inE negb_imply => /andP [] /andP [Hie Hig] /eqP Hvi.
right; rewrite /cinde_events.
rewrite (proj2 (cPr_eq0P _ _ _)); last first.
  apply/Pr_set0P => u; rewrite !inE => Hprod; elim: Hvi.
  case/andP: Hprod => /andP[] /eqP <- _ /eqP <-; exact: prod_vars_inter.
rewrite (proj2 (cPr_eq0P _ _ _)) ?GRing.mul0r //.
apply/Pr_set0P => u; rewrite !inE => Hprod; elim: Hvi.
case/andP: Hprod => /eqP <- /eqP <-; exact: prod_vars_inter.
Qed.

Lemma cinde_events_cPr1 (i : 'I_n) :
  let vals := set_vals C (set_vals A (set_vals B vals0)) in
  (forall x : 'I_n, x \in e -> vals x = set_vals A vals0 x) ->
  i \in e -> i \in f -> i \notin g ->
  set_vals A vals0 i <> set_vals B vals0 i ->
  `Pr_P[(preim_vars (e :&: f) vals) | (preim_vars g vals)] = 1 ->
  cinde_events P [set x | preim (prod_vars e) (pred1 A) x]
    [set x | preim (prod_vars f) (pred1 B) x]
    [set x | preim (prod_vars g) (pred1 C) x].
Proof.
move=> vals He Hie Hif Hig Hvi.
rewrite /cinde_events /cPr.
set den := (X in _ / X).
case/boolP: (den == 0) => [/eqP|] Hden.
  by rewrite setIC Pr_domin_setI // ?mul0r => /esym/eqP; rewrite oner_eq0.
set num := Pr _ _ => Hnum.
have {}Hnum : num = den.
  by rewrite -[RHS]mul1r -Hnum -mulrA mulVf ?mulr1.
rewrite -Hnum in Hden.
rewrite (proj2 (Pr_set0P _ _)); last first.
  move=> u; rewrite !inE => /andP[] /andP[] /eqP HA /eqP HB.
  by rewrite -HA -HB !set_vals_prod_vars in Hvi.
suff : `Pr_P[finset (prod_vars f @^-1 B) | finset (prod_vars g @^-1 C)] = 0.
  by rewrite /cPr => ->; rewrite GRing.mulr0 GRing.mul0r.
(* prove incompatibility between B and C *)
apply/cPr_eq0P/Pr_set0P => u.
rewrite !inE => /andP [] /eqP HB /eqP HC.
move: Hnum; rewrite /den.
have -> : g = (e :&: f :|: g) :\: ((e :&: f) :\: g).
  by apply/setP => j; cases_in j.
rewrite Pr_preim_vars_sub; last by apply/subsetP => j; cases_in j.
have : prod_vals ((e :&: f) :\: g) vals
                 \in fin_img (prod_vars ((e :&: f) :\: g)).
  case/boolP: (_ \in _) => // /negP HA.
  elim: (negP Hden); rewrite /num -preim_vars_inter.
  have -> : e :&: f :|: g = (e :&: f :\: g) :|: g.
    apply/setP => k; by cases_in k.
  apply/eqP/Pr_set0P => v.
  rewrite preim_vars_inter inE => /andP [/preim_varsP /= HA'].
  elim: HA; apply/fin_imgP.
  exists v; apply/ffunP => k.
  apply/prod_vals_eq => /HA' <-.
  by rewrite ffunE.
case/fin_imgP => v Hv {Hden}.
set a := map_fin_img (prod_vars ((e :&: f) :\: g)) v.
rewrite (bigD1 a) //= nth_fin_imgK -Hv.
rewrite /num (@preim_vars_vals _ (prod_vals (e :&: f :|: g) vals) _ vals);
  last by move=> j; rewrite set_vals_prod_vals_id.
rewrite -preim_vars_inter addrC => /eqP.
rewrite -subr_eq subrr => /eqP/esym Hnum.
have : Pr P (preim_vars (e :&: f :|: g)
      (set_vals (prod_vals (e :&: f :\: g) (set_vals B vals)) vals)) = 0.
  rewrite (_ : prod_vals _ _ = prod_vars (e :&: f :\: g) u); last first.
    apply/ffunP => k; apply/prod_vals_eq => Hk.
    rewrite -HB set_vals_prod_vars ?ffunE //.
    move: Hk; cases_in k.
  rewrite -(@nth_fin_imgK U).
  move/psumr_eq0P: Hnum; apply; first by move=> /= *; exact: Pr_ge0.
  apply/eqP => /(f_equal (fun x => nth_fin_img x)).
  rewrite !nth_fin_imgK => /(prod_types_app i) /prod_vals_eqP Hi.
  elim: Hvi; rewrite -He //.
  have iefg : i \in e :&: f :\: g by move: Hif Hig Hie; cases_in i.
  move/(prod_types_app i)/prod_vals_eqP: Hv => -> //.
  by rewrite -HB set_vals_prod_vars // -Hi // ffunE.
move/Pr_set0P; apply.
apply/preim_varsP => j Hj.
case/boolP: (j \in g) => jg.
  by rewrite set_vals_tl ?inE ?jg // /vals -HC set_vals_prod_vars.
rewrite inE (negbTE jg) orbF in Hj.
rewrite -HB set_vals_prod_vals ?set_vals_prod_vars //.
  move: Hj; by rewrite inE => /andP[].
by rewrite inE Hj jg.
Qed.
End cinde_preim_lemmas.

Lemma cinde_preim_ok (e f g : {set 'I_n}) :
  cinde_preim e f g <-> P |= prod_vars e _|_ prod_vars f | (prod_vars g).
Proof.
split.
- move=> Hpreim.
  apply/cinde_RV_events => A B C.
  set vals := set_vals C (set_vals A (set_vals B vals0)).
  case /boolP: [forall i in e, vals i == set_vals A vals0 i]; last first.
    case: (cinde_events_vals A B C) => // /forallP Heg /negP; elim.
    apply/forallP => i; apply /implyP => Hie.
    case /boolP: (i \in g) => Hig;
      last by rewrite /vals set_vals_tl // (set_vals_hd vals0).
    rewrite /vals (set_vals_hd vals0) //.
    move/implyP: (Heg i); rewrite inE Hie; exact.
  (* A and C are compatible *)
  move/forallP => /= He.
  have {}He x Hx := eqP (implyP (He x) Hx).
  case /boolP: [forall i in f, vals i == set_vals B vals0 i].
    (* A/C and B are compatible *)
    move/forallP => /= Hf.
    have {}Hf x Hx := eqP (implyP (Hf x) Hx).
    move: (Hpreim vals).
    rewrite (preim_vars_vals _ He) // (preim_vars_vals _ Hf) //.
    by rewrite /cinde_events -!preim_prod_vars -!preim_inter.
  move/cinde_preimC in Hpreim.
  move=> HB; apply cinde_eventsC.
  case: (cinde_events_vals B A C) HB => // /forallP Hfg.
  (* A/C and B are incompatible *)
  rewrite negb_forall => /existsP [i].
  rewrite negb_imply /vals => /andP [Hif].
  case /boolP: (i \in g) => Hig.
    (* B and C are incompatible *)
    move: (Hfg i); rewrite inE Hif Hig /= => /eqP <-.
    by rewrite (set_vals_hd vals0) // eqxx.
  case /boolP: (i \in e) => Hie;
    last by rewrite set_vals_tl // set_vals_tl // eqxx.
  (* A and B are incompatible *)
  rewrite set_vals_tl // (set_vals_hd vals0) // => /eqP Hvi.
  apply/cinde_eventsC.
  (* Reduce to intersection *)
  move/cinde_preimC/cinde_preim_inter/(_ vals): Hpreim.
  rewrite {1}/cinde_events -!preim_vars_inter setUid /=.
  case/Rxx2.
    (* cPr = 0 *)
    move/cPr_eq0P/Pr_set0P => Hx.
    have HAC :
      Pr P (finset (prod_vars e @^-1 A) :&: finset (prod_vars g @^-1 C)) = 0.
      apply/Pr_set0P => u Hu; apply Hx.
      rewrite -preim_vars_inter; apply/preim_varsP => j.
      move: Hu; rewrite !inE.
      rewrite /vals => /andP[] /eqP <- /eqP <-.
      case/boolP: (j \in g) => jg.
        by rewrite set_vals_prod_vars.
      case/boolP: (j \in e) => // je.
      by rewrite set_vals_tl // set_vals_prod_vars.
    rewrite /cinde_events (proj2 (cPr_eq0P _ _ _)).
      by rewrite (proj2 (cPr_eq0P _ _ _)) // GRing.mul0r.
    apply/Pr_set0P => u Hu.
    apply(proj1 (Pr_set0P _ _) HAC).
    move: Hu; by rewrite !inE => /andP[] /andP[] -> _ ->.
  (* cPr = 1 *)
  exact: (cinde_events_cPr1 (i:=i)).
- move=> Hdrv vals.
  move/cinde_RV_events: Hdrv.
  move/(_ (prod_vals e vals) (prod_vals f vals) (prod_vals g vals)).
  rewrite -(preim_vars_vals (prod_vals e vals) (set_vals_prod_vals _ vals)).
  rewrite -(preim_vars_vals (prod_vals f vals) (set_vals_prod_vals _ vals)).
  rewrite -(preim_vars_vals (prod_vals g vals) (set_vals_prod_vals _ vals)).
  by rewrite -!preim_prod_vars.
Qed.

Section Imap.
Variable parent : rel 'I_n.

Definition topological := forall i j : 'I_n, parent i j -> (i < j)%nat.

Definition independence (i j : 'I_n) :=
  ~~ closure parent [set i] j ->
  let parents := [set k | closure parent [set k] i] in
  cinde_preim [set i] [set j] parents.
End Imap.

(* Koller and Friedman, Definition 3.1, page 57 *)

Record t := mkBN
  { parent: rel 'I_n;
    topo: topological parent;
    indep: forall i j, independence parent i j
  }.
End preim.

Section equiv.
Variables types1 types2 : 'I_n -> finType.
Variable vars1 : forall i, {RV P -> types1 i}.
Variable vars2 : forall i, {RV P -> types2 i}.
Hypothesis varsE : forall i, RV_equiv (vars1 i) (vars2 i).

Definition vals1to2 (vals1 : univ_types types1) : univ_types types2
 := [ffun i => (sval (varsE i)).1 (vals1 i)].

Lemma preim_vars12 (I : {set 'I_n}) (vals1 : univ_types types1) :
  preim_vars vars2 I (vals1to2 vals1) = preim_vars vars1 I vals1.
Proof.
rewrite /preim_vars.
apply/setP => v.
apply/preim_varsP; case: ifP => /preim_varsP /= H1.
- move=> i iI; rewrite ffunE.
  move/H1: (iI).
  by case: varsE => -[f g] [/= fK gK] /(_ v) -> <-.
- move=> Hv; elim: H1 => /= i iI.
  move/Hv: (iI); rewrite ffunE.
  case: varsE => -[f g] [/= fK gK] /(_ v) -> /(f_equal g).
  by rewrite !fK => ->.
Qed.

Lemma cinde_preim_equiv1 (I J K : {set 'I_n}) :
  cinde_preim vars2 I J K -> cinde_preim vars1 I J K.
Proof.
rewrite /cinde_preim => CI vals1.
move: (CI (vals1to2 vals1)).
by rewrite !preim_vars12.
Qed.
End equiv.

Lemma cinde_preim_equiv (types1 types2 : 'I_n -> finType)
      (vars1 : forall i : 'I_n, {RV P -> types1 i})
      (vars2 : forall i : 'I_n, {RV P -> types2 i}) I J K :
  (forall i : 'I_n, RV_equiv (vars1 i) (vars2 i)) ->
  cinde_preim vars1 I J K <-> cinde_preim vars2 I J K.
Proof. split; apply cinde_preim_equiv1 => // i; by apply RV_equivC. Qed.

End bn.
End BN.

Section Factorization.
Import BN.
Variables (R : realType) (U : finType) (P : R.-fdist U) (n : nat).
Variable types : 'I_n -> finType.
Variable vars : forall i, {RV P -> types i}.
Variable bn : t vars.

(* Theorem 3.1, page 62 *)
Theorem BN_factorization vals :
  Pr P (preim_vars vars setT vals) =
  \prod_(i < n)
   let parents := [set k | closure (parent bn) [set k] i] in
   `Pr_ P [ preim_vars vars [set i] vals | preim_vars vars parents vals ].
Abort.

End Factorization.
