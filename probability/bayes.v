(* infotheo: information theory and error-correcting codes in Coq               *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later              *)
From mathcomp Require boolp.
Require Import Reals. (* Lra Nsatz. *)
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop.
Require Import fdist proba.

(******************************************************************************)
(* wip                                                                        *)
(******************************************************************************)

Local Open Scope tuple_ext_scope.
Local Open Scope proba_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* proba.v ? *)
Definition rvar_choice U (P : fdist U) (A : finType) (X : {RV P -> A}) : A.
move: (fdist_card_neq0 (`d_ X)).
move He: (enum A) => [|a l] //.
move/(f_equal size): He.
by rewrite -cardE => ->.
Defined.

Section univ_types.
(* heterogeneous types *)
Variable n : nat.
Variable types : 'I_n -> finType.
Definition univ_types := [finType of {dffun forall i, types i}].

Section prod_types.
(* sets of indices *)
Variable I : {set 'I_n}.

Definition prod_types :=
  [finType of
   {dffun forall i : 'I_n, if i \in I then types i else unit_finType}].

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
Proof.
rewrite !ffunE => ie.
move: (vals i); by rewrite ie.
Qed.

Lemma prod_vals_eqP vals1 vals2 i :
  prod_vals vals1 i = prod_vals vals2 i <-> (i \in I -> vals1 i = vals2 i).
Proof.
split.
  move=> Heq Hie.
  move: Heq.
  rewrite !ffunE /=.
  move: (vals1 i) (vals2 i); by rewrite Hie.
rewrite !ffunE.
case Hi: (i \in I) (vals1 i) (vals2 i) => // v1 v2; exact.
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
move=> _.
exact: prod_types_out.
Qed.

End prod_types.

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
Variable U : finType.
Variable P : fdist U.
Variable n : nat.
Variable types : 'I_n -> finType.
Variable vars : forall i, {RV P -> types i}.

Definition vals_at (u : U) : univ_types types := [ffun i => vars i u].

Section prod_vars.
Variable I : {set 'I_n}.

Definition prod_vars : {RV P -> prod_types types I} :=
  fun u => prod_vals I (vals_at u).

Lemma set_vals_prod_vars vals u i :
  i \in I -> set_vals (prod_vars u) vals i = vars i u.
Proof. move=> Hi; by rewrite set_vals_prod_vals // ffunE. Qed.
End prod_vars.

Lemma prod_vars_inter (e g : {set 'I_n}) vals i u :
  i \in e -> i \in g ->
  set_vals (prod_vars e u) vals i = set_vals (prod_vars g u) vals i.
Proof. move=> ie ig; by rewrite !set_vals_prod_vals. Qed.

Definition RV_equiv (A B : finType) (X : {RV P -> A}) (Y : {RV P -> B}) :=
  [set finset (X @^-1 a) | a : A] :\: [set set0] =
  [set finset (Y @^-1 b) | b : B] :\: [set set0].

Definition vals0 : univ_types types := [ffun i => rvar_choice (vars i)].

Definition prod_vals1 i (x : types i) := prod_vals [set i] (set_val x vals0).

Definition prod_proj i (x : prod_types types [set i]) := set_vals x vals0 i.

Lemma prod_vars1 (i : 'I_n) : RV_equiv (prod_vars [set i]) (vars i).
Proof.
apply/setP => s.
rewrite !inE.
case: (s == set0) => //.
apply/imsetP; case: ifPn.
  move/imsetP => [x Hx ->].
  exists (prod_vals1 x).
    by rewrite inE.
  apply/setP => u.
  rewrite !inE /prod_vars /prod_vals1 /=.
  symmetry.
  case/boolP: (vars i u == x).
    move/eqP => <-.
    apply/eqP/ffunP => j; apply/prod_vals_eqP.
    rewrite inE => /eqP ->.
    by rewrite set_val_hd ffunE.
  apply/contraNF => /eqP/(prod_types_app i)/prod_vals_eqP.
  rewrite inE eqxx set_val_hd ffunE => Hv.
  by rewrite Hv // eqxx.
move=> Hs [x] _ Hx.
elim: (negP Hs) => /=.
subst s.
apply/imsetP.
exists (prod_proj x).
  by rewrite inE.
apply/setP => u.
rewrite !inE.
case/boolP: (vars i u == _).
  move/eqP => Hv.
  apply/eqP/ffunP => /= j.
  rewrite (prod_vals_eq (vals2:=set_vals x vals0)).
    apply/(set_vals_inj (vals:=set_vals x vals0)).
    by rewrite set_vals_prod_vals_id set_vals_id.
  by rewrite inE ffunE => /eqP ->.
apply/contraNF => /eqP <-.
by rewrite /prod_proj set_vals_prod_vars // inE.
Qed.

Section prod_vars_pair.
Variables I J : {set 'I_n}.

Definition prod_vals2 (x : prod_types types I * prod_types types J) :=
  prod_vals (I :|: J) (set_vals (fst x) (set_vals (snd x) vals0)).

Definition prod_proj2 (x : prod_types types (I :|: J)) :=
  (prod_vals I (set_vals x vals0), prod_vals J (set_vals x vals0)).

Lemma prod_vars_pair :
  RV_equiv (prod_vars (I :|: J)) (RV2 (prod_vars I) (prod_vars J)).
Proof.
apply/setP => s.
rewrite !inE.
case/boolP: (s == set0) => // Hs.
apply/imsetP; case: ifPn.
  move=> Hs'.
  move/imsetP: Hs' Hs => [x _ ->] Hs.
  exists (prod_vals2 x).
    by rewrite inE.
  apply/setP => u.
  rewrite !inE /prod_vars /prod_vals2 /=.
  symmetry.
  rewrite /RV2.
  destruct x as [x1 x2] => /=.
  case/boolP: (_ == (x1,x2)); rewrite xpair_eqE.
    case/andP => /eqP <- /eqP <-.
    apply/eqP/ffunP => j.
    apply/prod_vals_eqP.
    rewrite !inE.
    case/boolP: (j \in I) => /= HI HJ.
      by rewrite set_vals_prod_vals.
    by rewrite set_vals_tl // set_vals_prod_vals.
  apply/contraNF => /eqP/ffunP.
  case/boolP: (_ == x1) => /=.
    move/eqP => Hx1.
    rewrite -Hx1 /=.
    case/boolP: (_ == x2) => //=.
    move/prod_types_neq => [i] /andP [iJ Hx2].
    case/boolP: (i \in I) => iI.
      elim: (negP Hs).
      apply/eqP/setP => u'.
      rewrite !inE xpair_eqE.
      apply/contraNF: Hx2.
      case/andP => /eqP /(f_equal (set_vals (I:=I) ^~ vals0)) /ffunP /(_ i).
      rewrite set_vals_prod_vals // => x1i.
      move/eqP/(f_equal (set_vals (I:=J) ^~ vals0))/ffunP/(_ i).
      rewrite set_vals_prod_vals // x1i -Hx1.
      by rewrite (prod_vars_inter vals0 _ iI iJ) => /set_vals_inj <-.
    move/(_ i)/prod_vals_eqP.
    rewrite set_vals_tl // inE iJ orbT => /(_ isT) Hv.
    elim: (negP Hx2); apply/eqP/(set_vals_inj (vals:=vals0)).
    by rewrite -Hv set_vals_prod_vals.
  move/prod_types_neq => [i] /andP [iI Hx1] /(_ i) /prod_vals_eqP.
  rewrite inE iI => /= /(_ isT) Hv.
  elim: (negP Hx1).
  apply/eqP/(set_vals_inj (vals:=set_vals x2 vals0)).
  by rewrite -Hv set_vals_prod_vals.
move=> {}Hs [x] _ Hx.
elim: (negP Hs); subst s.
apply/imsetP.
exists (prod_proj2 x).
  by rewrite inE.
apply/setP => u.
rewrite !inE.
symmetry.
case/boolP: (_ == x).
  move/eqP => <-.
  rewrite xpair_eqE /prod_vars.
  apply/andP; split; apply/eqP/ffunP => i; apply/prod_vals_eqP => Hi;
    by rewrite set_vals_prod_vals // inE Hi // orbT.
apply/contraNF => Hux.
apply/eqP/ffunP => i.
move: Hux.
rewrite xpair_eqE /prod_vars => /andP [].
move=> /eqP/(prod_types_app i) HI /eqP/(prod_types_app i) HJ.
rewrite (proj2 (prod_vals_eqP _ _ (set_vals x vals0) _)).
  apply (set_vals_inj (vals:=set_vals x vals0)).
  by rewrite set_vals_prod_vals_id set_vals_id.
rewrite inE => /orP [] Hi; [move: HI | move: HJ] => /prod_vals_eqP; exact.
Qed.
End prod_vars_pair.

Section preim.
Local Open Scope R_scope.

Definition preim_vars (I : {set 'I_n}) (vals : forall i, types i) :=
  \bigcap_(i in I) finset (vars i @^-1 (vals i)).

Definition cinde_preim (e f g : {set 'I_n}) :=
  forall vals : univ_types types,
    cinde_events P (preim_vars e vals)
                   (preim_vars f vals)
                   (preim_vars g vals).

Lemma cinde_eventsC A (Q : fdist A) (E F G : {set A}) :
  cinde_events Q E F G -> cinde_events Q F E G.
Proof. rewrite /cinde_events => Hef; by rewrite setIC mulRC. Qed.

Lemma cinde_preimC (e f g : {set 'I_n}) :
  cinde_preim e f g  -> cinde_preim f e g.
Proof. move=> Hef vals; exact: cinde_eventsC. Qed.

Lemma preim_prod_vars (g : {set 'I_n}) (C : prod_types types g) vals :
  finset (prod_vars g @^-1 C) = preim_vars g (set_vals C vals).
Proof.
apply/setP => x.
rewrite !inE; symmetry.
apply/bigcapP; case: ifP.
- move/eqP => <- i ig.
  by rewrite !inE set_vals_prod_vals // ffunE.
- move/negP => Hf Hcap.
  elim: Hf.
  apply/eqP/ffunP => /= i.
  move/(_ i): Hcap.
  rewrite !ffunE !inE /set_vals.
  by case: (i \in g) (C i) => /= [Ci /(_ isT) /eqP | []].
Qed.

(* Simple version, using singletons *)

Lemma Rxx2 x : x = x * x -> x = 0 \/ x = 1.
Proof.
case/boolP: (x == 0) => Hx.
  rewrite (eqP Hx); by left.
move/(f_equal (Rdiv ^~ x)).
rewrite divRR // /Rdiv -mulRA mulRV // mulR1 => <-; by right.
Qed.

Lemma cinde_preim_ok (i j k : 'I_n) :
  cinde_preim [set i] [set j] [set k] <-> P |= (vars i) _|_ (vars j) | (vars k).
Proof.
rewrite /cinde_preim /preim_vars.
split.
- move=> Hpreim.
  apply/cinde_rv_events => a b c.
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
      rewrite (proj2 (cPr_eq0 _ _ _)); last first.
        apply/Pr_set0P => u.
        by rewrite !inE => /andP [] /andP [] /= /eqP ->; rewrite ac.
      rewrite (proj2 (cPr_eq0 _ _ _)); last first.
        apply/Pr_set0P => u.
        by rewrite !inE => /andP [] /= /eqP ->; rewrite ac.
      by rewrite mul0R.
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
        rewrite (proj2 (cPr_eq0 _ _ _)) ?mul0R //.
        apply/Pr_set0P => u.
        by rewrite !inE => /andP [] /andP [] /= /eqP ->; rewrite ab.
      rewrite /cPr.
      set den := (X in _ / X).
      case/boolP: (den == 0) => /eqP Hden.
        by rewrite setIC Pr_domin_setI // setIC Pr_domin_setI // !div0R mul0R.
      set num := (X in _ * (X / _)).
      case/boolP: (num == 0) => /eqP Hnum.
        by rewrite -setIA setIC Pr_domin_setI // Hnum !div0R mulR0.
      elim Hnum.
      apply/Pr_set0P => u.
      rewrite !inE => /andP [] /= Hi Hk.
      move: Hx; subst x.
      move/(f_equal (Rmult ^~ den)).
      move/eqP in Hden.
      rewrite /cPr /Rdiv -mulRA mulVR // mulR1 mul1R.
      move/(f_equal (Rminus den)).
      rewrite subRR setIC -Pr_diff => /Pr_set0P/(_ u).
      rewrite !inE (eqP Hi) Hk eq_sym ab; exact.
    case: (ord_eq_dec k j).
      move=> <- {j} ik b.
      case bc: (b == c).
        rewrite (eqP bc); exact.
      move=> _ _ _.
      rewrite (proj2 (cPr_eq0 _ _ _)); last first.
        apply/Pr_set0P => u.
        by rewrite !inE => /andP [] /andP [] _ /= /eqP ->; rewrite bc.
      rewrite mulRC (proj2 (cPr_eq0 _ _ _)) ?mul0R //.
      by apply/Pr_set0P => u; rewrite !inE => /andP [] /= /eqP ->; rewrite bc.
    move=> nkj nij b HG Hvals; apply: HG => //.
    by rewrite Hvals set_val_tl // set_val_tl // set_val_hd.
  by rewrite vi vk => -> _.
- move=> Hdrv vals.
  move/cinde_rv_events/(_ (vals i) (vals j) (vals k)): Hdrv.
  by rewrite !big_set1.
Qed.

(* Now start the hard version, using sets of variables *)

Lemma preim_vars_set_vals_tl (g e : {set 'I_n}) (A : prod_types types e) vals :
  e :&: g = set0 ->
  preim_vars g (set_vals A vals) = preim_vars g vals.
Proof.
move=> /setP eg.
apply eq_bigr => /= i ig.
apply/setP => u.
rewrite !inE set_vals_tl //.
move: (eg i); by rewrite !inE ig andbT => ->.
Qed.

Lemma preim_inter (T S : finType) (e : U -> T) (g : U -> S) (A : T) (C : S) :
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
suff: forall vals1 vals2 u, (forall x, x \in e -> vals1 x = vals2 x) ->
         u \in preim_vars e vals1 -> u \in preim_vars e vals2.
  move=> H Hvals.
  apply/setP => u.
  case /boolP: (u \in preim_vars _ vals2).
    apply H => x Hx. by rewrite Hvals.
  move/negP => Hu; apply/negP => Hu'; elim Hu; move: Hu'.
  exact: H.
move=> {vals1 vals2} vals1 vals2 u Hvals.
move/bigcapP => Hpre; apply/bigcapP => i ie.
move: (Hpre _ ie).
by rewrite !inE Hvals.
Qed.

Lemma Pr_preim_vars_sub (e f : {set 'I_n}) (vals : univ_types types) :
  f \subset e ->
  Pr P (preim_vars (e :\: f) vals) =
  \sum_(A : prod_types types f) Pr P (preim_vars e (set_vals A vals)).
Proof.
rewrite /preim_vars /Pr => fe.
rewrite -partition_disjoint_bigcup; last first.
  move=> A B AB.
  rewrite -setI_eq0.
  apply/eqP/setP => u.
  rewrite !inE.
  apply/negP => /andP [] /bigcapP /= HA /bigcapP /= HB.
  case: (prod_types_neq AB) => /= i /andP [Hif HAB].
  have ie : i \in e by move/subsetP: fe; apply.
  move/(_ _ ie): HB.
  move/(_ _ ie): HA.
  rewrite !inE /= => /eqP ->.
  rewrite set_vals_eq => /orP [] H.
  - by rewrite H in HAB.
  - by rewrite Hif in H.
apply eq_bigl => u.
case: bigcupP.
  move=> [A _ /bigcapP HA].
  apply/bigcapP => /= i /setDP [/HA Hu Hif].
  move: Hu; by rewrite !inE set_vals_tl.
move=> HN.
apply/negP => /bigcapP /= Hu; elim: HN.
exists (prod_vars f u) => //.
apply/bigcapP => /= i ie.
move/(_ i): Hu.
rewrite !inE.
case/boolP: (i \in f) => Hif.
  by rewrite set_vals_prod_vars.
by rewrite set_vals_tl // ie => ->.
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
transitivity (\sum_(A : prod_types types (e :\: e'))
          let v := set_vals A vals in
          `Pr_P[preim_vars e v :&: preim_vars f v | preim_vars g v]).
  rewrite /cPr.
  rewrite -!preim_vars_inter.
  rewrite (_ : e' :|: f :|: g = (e :|: f :|: g) :\: (e :\: e')); last first.
    apply/setP => i.
    move/subsetP/(_ i): e'e.
    move/subsetP/(_ i): ee'.
    by cases_in i.
  rewrite Pr_preim_vars_sub; last by apply/subsetP=> i; cases_in i.
  under [in RHS]eq_bigr => A _
    do rewrite -!preim_vars_inter (@preim_vars_set_vals_tl g) //.
  by rewrite -big_distrl.
under eq_bigr => A _ /=.
  rewrite Hef (@preim_vars_set_vals_tl g) // (@preim_vars_set_vals_tl f).
    over.
  apply/setP => i; move/subsetP/(_ i): ee'; by cases_in i.
rewrite -2!big_distrl /=.
congr (_ / _ * _).
rewrite -preim_vars_inter.
rewrite (_ : e' :|: g = (e :|: g) :\: (e :\: e')); last first.
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

Lemma cinde_events_vals (e f g : {set 'I_n}) (A : prod_types types e)
  (B : prod_types types f) (C : prod_types types g) :
  [forall i in (e :&: g), set_vals C vals0 i == set_vals A vals0 i] \/
  cinde_events P (finset (prod_vars e @^-1 A)) (finset (prod_vars f @^-1 B))
                 (finset (prod_vars g @^-1 C)).
Proof.
case /boolP: [forall i in (e :&: g), _].
  by left.
rewrite negb_forall => /existsP [i].
rewrite inE negb_imply => /andP [] /andP [Hie Hig] /eqP Hvi.
right; rewrite /cinde_events.
rewrite (proj2 (cPr_eq0 _ _ _)); last first.
  apply/Pr_set0P => u; rewrite !inE => Hprod; elim: Hvi.
  case/andP: Hprod => /andP[] /eqP <- _ /eqP <-; exact: prod_vars_inter.
rewrite (proj2 (cPr_eq0 _ _ _)) ?mul0R //.
apply/Pr_set0P => u; rewrite !inE => Hprod; elim: Hvi.
case/andP: Hprod => /eqP <- /eqP <-; exact: prod_vars_inter.
Qed.

Lemma cinde_preim_ok' (e f g : {set 'I_n}) :
  cinde_preim e f g <-> P |= prod_vars e _|_ prod_vars f | (prod_vars g).
Proof.
split.
- move=> Hpreim.
  apply/cinde_rv_events => A B C.
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
  case /boolP: [forall i in f, vals i == set_vals B vals0 i]; last first.
    move/cinde_preimC in Hpreim.
    move=> HB; apply cinde_eventsC.
    case: (cinde_events_vals B A C) HB => // /forallP Hfg.
    (* B and C are compatible *)
    rewrite negb_forall => /existsP [i].
    rewrite negb_imply /vals => /andP [Hif].
    case /boolP: (i \in g) => Hig.
      move: (Hfg i); by rewrite inE Hif Hig /= (set_vals_hd vals0) // => ->.
    case /boolP: (i \in e) => Hie;
      last by rewrite set_vals_tl // set_vals_tl // eqxx.
    (* A and B are incompatible *)
    rewrite set_vals_tl // (set_vals_hd vals0) // => /eqP Hvi.
    apply/cinde_eventsC.
    (* Reduce to intersection *)
    move/cinde_preimC/cinde_preim_inter/(_ vals): Hpreim.
    rewrite /cinde_events -!preim_vars_inter setUid /=.
    case/Rxx2.
      (* Pr = 0 *)
      move/cPr_eq0/Pr_set0P => Hx.
      have HAC :
        Pr P (finset (prod_vars e @^-1 A) :&: finset (prod_vars g @^-1 C)) = 0.
        apply Pr_set0P => u Hu; apply Hx.
        rewrite -preim_vars_inter; apply/bigcapP => j.
        move: Hu; rewrite !inE.
        rewrite /vals => /andP[] /eqP <- /eqP <-.
        case/boolP: (j \in g) => jg.
          by rewrite set_vals_prod_vars.
        case/boolP: (j \in e) => // je.
        by rewrite set_vals_tl // set_vals_prod_vars.
      rewrite (proj2 (cPr_eq0 _ _ _)).
        by rewrite (proj2 (cPr_eq0 _ _ _)) // mul0R.
      apply/Pr_set0P => u Hu.
      apply(proj1 (Pr_set0P _ _) HAC).
      move: Hu; by rewrite !inE => /andP[] /andP[] -> _ ->.
    (* Pr = 1 *)
    rewrite /cPr.
    set den := (X in _ / X).
    case/boolP: (den == 0) => /eqP Hden.
      by rewrite setIC Pr_domin_setI // ?div0R => /esym/R1_neq_R0.
    set num := Pr _ _.
    move=> Hnum.
    move/eqP in Hden.
    have Hnum' : num = den.
      by rewrite -[RHS]mul1R -Hnum /Rdiv -mulRA mulVR // mulR1.
    rewrite (proj2 (Pr_set0P _ _)); last first.
      move=> u; rewrite !inE => /andP[] /andP[] /eqP HA /eqP HB.
      by rewrite -HA -HB !set_vals_prod_vars in Hvi.
    symmetry; rewrite mulRC.
    rewrite (proj2 (Pr_set0P _ _)).
      by rewrite !div0R !mul0R.
    move=> u; rewrite !inE => /andP [] /eqP HB /eqP HC.
    move: Hnum'.
    rewrite /den (_ : g = (e :&: f :|: g) :\: ((e :&: f) :\: g));
      last by apply/setP => j; cases_in j.
    rewrite Pr_preim_vars_sub;
      last by apply/subsetP => j; cases_in j.
    rewrite (bigD1 (prod_vals ((e :&: f) :\: g) vals)) //=.
    rewrite /num (@preim_vars_vals _ (prod_vals (e :&: f :|: g) vals) _ vals);
      last by move=> j; rewrite set_vals_prod_vals_id.
    move/(f_equal (Rminus^~ (Pr P (preim_vars (e :&: f :|: g) vals)))).
    rewrite -preim_vars_inter subRR addRC /Rminus -addRA addRN addR0 => /esym.
    move=> Hnum2.
    have : Pr P (preim_vars (e :&: f :|: g)
         (set_vals (prod_vals (e :&: f :\: g) (set_vals B vals)) vals)) = 0.
      apply: (proj1 (psumR_eq0P _) Hnum2).
        move => *; by apply sumR_ge0.
      apply/eqP => /(f_equal (fun x : prod_types _ _ => x i)) /prod_vals_eqP Hi.
      elim: Hvi.
      by rewrite -(He i Hie) (set_vals_hd vals) // Hi // !inE Hif Hig Hie.
    move/Pr_set0P; apply.
    apply/bigcapP => j Hj.
    rewrite !inE.
    case/boolP: (j \in g) => jg.
      by rewrite set_vals_tl ?inE ?jg // /vals -HC set_vals_prod_vars.
    rewrite inE (negbTE jg) orbF in Hj.
    rewrite -HB set_vals_prod_vals ?set_vals_prod_vars //.
      move: Hj; by rewrite inE => /andP[].
    by rewrite inE Hj jg.
  move/forallP => /= Hf.
  have {}Hf x Hx := eqP (implyP (Hf x) Hx).
  move: (Hpreim vals).
  rewrite (preim_vars_vals _ He) // (preim_vars_vals _ Hf) //.
  by rewrite /cinde_events -!preim_prod_vars -!preim_inter.
- move=> Hdrv vals.
  move/cinde_rv_events: Hdrv.
  move/(_ (prod_vals e vals) (prod_vals f vals) (prod_vals g vals)).
  rewrite -(preim_vars_vals (prod_vals e vals) (set_vals_prod_vals _ vals)).
  rewrite -(preim_vars_vals (prod_vals f vals) (set_vals_prod_vals _ vals)).
  rewrite -(preim_vars_vals (prod_vals g vals) (set_vals_prod_vals _ vals)).
  by rewrite -!preim_prod_vars.
Qed.
End preim.

Section Imap.
Variable parent : rel 'I_n.

Definition topological := forall i j : 'I_n, parent i j -> i < j.

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
End bn.
End BN.

Section Factorization.
Import BN.
Variable U : finType.
Variable P : fdist U.
Variable n : nat.
Variable types : 'I_n -> finType.
Variable vars : forall i, {RV P -> types i}.
Variable bn : t vars.

Local Open Scope R_scope.

(* Theorem 3.1, page 62 *)
Theorem BN_factorization vals :
  Pr P (preim_vars vars setT vals) =
  \prod_(i < n)
   let parents := [set k | closure (parent bn) [set k] i] in
   `Pr_ P [ preim_vars vars [set i] vals | preim_vars vars parents vals ].
Abort.

End Factorization.
