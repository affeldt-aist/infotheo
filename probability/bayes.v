(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import all_ssreflect ssralg fingroup perm finalg matrix.
From mathcomp Require boolp.
Require Import Reals. (* Lra Nsatz. *)
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop.
Require Import fdist proba jfdist cinde.

(******************************************************************************)
(* wip                                                                        *)
(******************************************************************************)

Local Open Scope tuple_ext_scope.
Local Open Scope proba_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module BN.
Section bn.
Variable U : finType.
Variable P : fdist U.
Variable n : nat.
Variable types : 'I_n -> finType.
Variable vars : forall i, {RV P -> types i}.

Section prod_vars.
Variable I : {set 'I_n}.

Definition prod_types :=
  [finType of
   {dffun forall i : 'I_n, if i \in I then types i else unit_finType}].

Definition prod_vars' : {RV P -> prod_types}.
move=> u.
refine [ffun i => _].
case: (i \in I).
- exact: vars i u.
- exact: tt.
Defined.
(* fun u => [ffun i => if i \in I then vars i u else tt] *)
Definition prod_vars : {RV P -> prod_types} := Eval hnf in prod_vars'.
End prod_vars.

Section preim.
Local Open Scope R_scope.

Definition preim_vars (I : {set 'I_n}) (vals : forall i, types i) :=
  \bigcap_(i in I) finset (vars i @^-1 (vals i)).

Definition cinde_preim (e f g : {set 'I_n}) :=
  forall vals,
    let E := preim_vars e vals in
    let F := preim_vars f vals in
    let G := preim_vars g vals in
    `Pr_ P [ E :&: F | G ] = `Pr_ P [ E | G ] * `Pr_ P [ F | G ].

Definition rvar_choice (A : finType) (X : {RV P -> A}) : A.
move: (fdist_card_neq0 (`d_ X)).
move He: (enum A) => [|a l] //.
move/(f_equal size): He.
by rewrite -cardE => ->.
Defined.

Definition set_val (i : 'I_n) (v : types i) (vals : forall j, types j) :=
  fun j : 'I_n =>
    match Nat.eq_dec i j return types j with
    | left ij => eq_rect i (fun i => (types i : Type)) v j (ord_inj ij)
    | right _ => vals j
    end.

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
rewrite /set_val eq_dec_refl -Eqdep_dec.eq_rect_eq_dec //; exact: ord_eq_dec.
Qed.

Lemma set_val_tl i (v : types i) vs j : i <> j -> set_val v vs j = vs j.
rewrite /set_val => nij; case: Nat.eq_dec => ij //; elim nij; exact: ord_inj.
Qed.

Lemma Rxx2 x : x = x * x -> x = 0 \/ x = 1.
Proof.
case/boolP: (x == 0) => Hx.
  rewrite (eqP Hx); by left.
move/(f_equal (Rdiv ^~ x)).
rewrite divRR // /Rdiv -mulRA mulRV // mulR1 => <-; by right.
Qed.

Lemma cinde_preim_ok (i j k : 'I_n) :
  cinde_preim [set i] [set j] [set k] <-> vars i _|_ vars j | (vars k).
Proof.
rewrite /jcinde_rv /cinde_preim /preim_vars.
split.
- move=> Hpreim a b c.
  set vals := set_val a (set_val c (set_val b (fun i => rvar_choice (vars i)))).
  have vi : vals i = a by rewrite /vals set_val_hd.
  move: (erefl vals) {Hpreim} (Hpreim vals).
  rewrite {2}/vals /jcPr /cPr /Pr /dist_of_RV; clearbody vals.
  rewrite !setX1 !big_set1 !snd_RV3 !snd_RV2 !FDistMap.dE /=.
  wlog: c / vals k = c.
    case: (ord_eq_dec i k) c vi.
      move=> <- {k} c vi.
      case ac: (a == c).
        rewrite -(eqP ac); by apply.
      move=> _ _ _.
      rewrite big1; last by move=> u /andP [] /andP [] /= /eqP ->; rewrite ac.
      rewrite div0R.
      rewrite big1; last by move=> u /andP [] /= /eqP ->; rewrite ac.
      by rewrite div0R mul0R.
    move=> nik c vi HG Hvals; apply: HG => //.
    by rewrite Hvals set_val_tl // set_val_hd.
  move=> vk.
  wlog: b / vals j = b.
    case: (ord_eq_dec i j) b.
      move=> <- {j} b.
      case ab: (a == b).
        rewrite -(eqP ab); by apply.
      move=> _ _.
      rewrite setIid vi vk.
      set x := _ / _.
      move/Rxx2 => [].
        move/mulR_eq0 => [] Hx.
        - rewrite big1; last
            by move=> u /andP [] /andP [] /= /eqP ->; rewrite ab.
          rewrite div0R (_ : \sum_(u | _) _ = 0).
            by rewrite !div0R mul0R.
          rewrite -Hx.
          apply eq_bigl => ?; by rewrite !inE.
        - rewrite /Rdiv (_ : / _ = 0) ?mulR0 // -Hx; congr (/ _).
          apply eq_bigl => ?; by rewrite !inE.
      move=> Hx.
      set den := \sum_(u | _ c) _.
      case/boolP: (den == 0) => Hden.
        have Hden' u : vars k u == c -> P u = 0.
          move=> Hu.
          by move/eqP/psumR_eq0P: Hden => ->.
        rewrite !big1; try by move=> u /andP [] /= _; apply Hden'.
        by rewrite !div0R mul0R.
      set num := \sum_(u | _ == (b, c)) _.
      case/boolP: (num == 0) => /eqP Hnum.
        rewrite Hnum big1.
          by rewrite div0R !mulR0.
        move=> u /andP [] /andP [] /= /eqP ->.
        by rewrite ab.
      elim Hnum.
      apply big1 => u /andP [] /= Hi Hk.
      move: Hx; subst x.
      have -> : \sum_(u in finset (vars k @^-1 c)) P u = den.
        by apply eq_bigl => ?; rewrite !inE.
      move/(f_equal (Rmult ^~ den)).
      rewrite /Rdiv -mulRA mulVR // mulR1 mul1R.
      rewrite /den (bigID (fun u => vars i u == a) (fun u => _ == c)) /=.
      set ca := \sum_(v | _ && _) _.
      rewrite (_ : \sum_(v in _) _ = ca); last
        by apply eq_bigl => v; rewrite !inE andbC.
      move/(f_equal (Rminus ^~ ca)).
      rewrite subRR addRC addRK => /esym /psumR_eq0P; apply => //.
      by rewrite Hk (eqP Hi) eq_sym ab.
    case: (ord_eq_dec k j).
      move=> <- {j} ik b.
      case cb: (c == b).
        rewrite -(eqP cb); by apply.
      move=> _ _ _.
      rewrite big1; last
        by move => u /andP [] /andP [] /= _ /eqP ->; rewrite eq_sym cb.
      rewrite div0R mulRC big1 /Rdiv ?mul0R // => // u /andP [] /= /eqP ->.
      by rewrite eq_sym cb.
    move=> nkj nij b HG Hvals; apply: HG => //.
    by rewrite Hvals set_val_tl // set_val_tl // set_val_hd.
  rewrite vi vk => -> _.
  set lhs1 := _ / _ => Hpreim.
  set lhs2 := _ / _.
  have <- : lhs1 = lhs2.
    by congr (_ / _); apply eq_bigl => u; rewrite !inE.
  rewrite Hpreim.
  by congr ((_/_) * (_/_)); apply eq_bigl => u; rewrite !inE.
- move=> Hdrv vals.
  move/(_ (vals i) (vals j) (vals k)): Hdrv.
  rewrite /jcPr /cPr /Pr /dist_of_RV.
  rewrite !setX1 !big_set1 !snd_RV3 !snd_RV2 !FDistMap.dE /=.
  set lhs1 := _ / _ => Hdrv.
  set lhs2 := _ / _.
  have -> : lhs2 = lhs1.
    by congr (_ / _); apply eq_bigl => u; rewrite !inE.
  rewrite Hdrv.
  by congr ((_/_) * (_/_)); apply eq_bigl => u; rewrite !inE.
Qed.

Definition set_vals' (I : {set 'I_n}) (v : prod_types I)
           (vals : forall j, types j) : forall j, types j.
move=> j.
move: (v j).
case: (j \in I) => a.
- exact: a.
- exact: vals j.
Defined.
Definition set_vals := Eval hnf in set_vals'.

Lemma set_vals_hd vs2 I (v : prod_types I) vs1 i :
  i \in I -> set_vals v vs1 i = set_vals v vs2 i.
Proof. rewrite /set_vals; by case: (i \in I) (v i). Qed.

Lemma set_vals_tl I (v : prod_types I) vs i :
  i \notin I -> set_vals v vs i = vs i.
Proof. rewrite /set_vals; by case: (i \in I) (v i). Qed.

Lemma set_vals_prod_vars (I : {set 'I_n}) vals u i :
  i \in I -> set_vals (prod_vars I u) vals i = vars i u.
Proof.
rewrite /set_vals /prod_vars ffunE /= => Hi.
move: (vals i) (vars i u); by rewrite Hi.
Qed.

Definition prod_vals' (I : {set 'I_n}) (vals : forall j, types j)
  : prod_types I.
refine [ffun i => _].
move: (vals i).
case: (i \in I) => a.
- exact: a.
- exact: tt.
Defined.
Definition prod_vals (I : {set 'I_n}) vals : prod_types I :=
  Eval hnf in prod_vals' I vals.
Print prod_vals.

Lemma prod_vars_inter (e g : {set 'I_n}) vals i u :
  i \in e -> i \in g ->
  set_vals (prod_vars e u) vals i = set_vals (prod_vars g u) vals i.
Proof.
rewrite /set_vals /prod_vars !ffunE.
by case: (i \in e) (i \in g) => // -[].
Qed.

Lemma preim_prod_vars (g : {set 'I_n}) (C : prod_types g) vals :
  finset (prod_vars g @^-1 C) = preim_vars g (set_vals C vals).
Proof.
apply/setP => x.
rewrite !inE; symmetry.
apply/bigcapP; case: ifP.
- move/eqP => <- i ig.
  by rewrite /set_vals /prod_vars !inE ffunE ig.
- move/negP => Hf Hcap.
  elim: Hf.
  apply/eqP/ffunP => /= i.
  move/(_ i): Hcap.
  rewrite !ffunE !inE /set_vals.
  by case: (i \in g) (C i) => /= [Ci /(_ isT) /eqP | []].
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

Lemma preim_vars_vals (e : {set 'I_n}) (A : prod_types e) vals1 vals2 :
  (forall x, (x \in e) ==> (vals1 x == vals2 x)) ->
  preim_vars e vals1 = preim_vars e vals2.
Proof.
suff: forall vals1 vals2 u, (forall x, (x \in e) ==> (vals1 x == vals2 x)) ->
         u \in preim_vars e vals1 -> u \in preim_vars e vals2.
  move=> H Hvals.
  apply/setP => u.
  case /boolP: (u \in preim_vars _ vals2).
    apply H => x; by rewrite eq_sym.
  move/negP => Hu.
  apply/negP => Hu'; elim Hu; move: Hu'.
  exact: H.
move=> {vals1 vals2} vals1 vals2 u Hvals.
move/bigcapP => Hpre.
apply/bigcapP => i ie.
move: (Hpre _ ie).
rewrite !inE => /eqP ->.
by apply/implyP: ie.
Qed.

Lemma prod_vals_vars (e : {set 'I_n}) (vals : forall i, types i) i :
  (i \in e) ==> (set_vals (prod_vals e vals) vals i == vals i).
Proof.
apply/implyP => _.
rewrite /set_vals /prod_vals ffunE.
by case: (i \in e) (vals i).
Qed.

Lemma cinde_preimC (e f g : {set 'I_n}) :
  cinde_preim e f g  -> cinde_preim f e g.
Proof.
rewrite /cinde_preim => Hef vals.
by rewrite setIC mulRC.
Qed.

Lemma prod_types_set0_eq (A B : prod_types set0) : A = B.
Proof.
apply/ffunP => /= x.
move: (A x) (B x).
case: ifP.
  by rewrite inE.
by move=> _ [] [].
Qed.

Lemma prod_types_neq e (A B : prod_types e) :
  A != B -> exists i, (i \in e) && (A i != B i).
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
case/boolP: (x \in e) => //= xe.
elim: (negP Hx).
move: (A x) (B x) {AB Hx} => /=.
by rewrite (negbTE xe) => -[] [].
Qed.

Lemma set_vals_eq (e : {set 'I_n}) (A B : prod_types e) vals i :
  set_vals A vals i == set_vals B vals i = (A i == B i) || (i \notin e).
Proof.
rewrite /set_vals.
case: (i \in e) (A i) (B i) => a b.
- by rewrite orbF.
- by rewrite eqxx orbT.
Qed.

Lemma Pr_preim_vars_sub (e f : {set 'I_n}) vals :
  f \subset e ->
  Pr P (preim_vars (e :\: f) vals) =
  \sum_(A : prod_types f) Pr P (preim_vars e (set_vals A vals)).
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
  apply/bigcapP => /= i ief.
  have ie : i \in e by case/setDP: ief.
  move/(_ _ ie): HA.
  rewrite !inE set_vals_tl //.
  by case/setDP: ief.
move=> HN.
apply/negP => /bigcapP /= Hu.
elim: HN.
exists (prod_vars f u) => //.
apply/bigcapP => /= i ie.
move/(_ i): Hu.
rewrite !inE.
case/boolP: (i \in f) => Hif.
  by rewrite set_vals_prod_vars.
by rewrite set_vals_tl // ie => ->.
Qed.

Lemma preim_vars_set_vals_tl (g e : {set 'I_n}) (A : prod_types e) vals :
  e :&: g = set0 ->
  preim_vars g (set_vals A vals) = preim_vars g vals.
Proof.
move=> /setP eg.
apply eq_bigr => /= i ig.
apply/setP => u.
rewrite !inE set_vals_tl //.
move: (eg i).
by rewrite !inE ig andbT => ->.
Qed.

Lemma cinde_preim_sub (e e' f g : {set 'I_n}) :
  e :&: (f :|: g) \subset e' -> e' \subset e ->
  cinde_preim e f g -> cinde_preim e' f g.
Proof.
rewrite /cinde_preim => ee' e'e Hef vals.
have ee'g : (e :\: e') :&: g = set0.
  apply/setP => i.
  move/subsetP/(_ i): ee'.
  rewrite !inE.
  do !case: (i \in _) => //=; by move/(_ isT).
transitivity (\sum_(A : prod_types (e :\: e'))
          let v := set_vals A vals in
          `Pr_P[preim_vars e v :&: preim_vars f v | preim_vars g v]).
  rewrite /cPr.
  rewrite -!preim_vars_inter.
  rewrite (_ : e' :|: f :|: g = (e :|: f :|: g) :\: (e :\: e')); last first.
    apply/setP => i.
    move/subsetP/(_ i): e'e.
    move/subsetP/(_ i): ee'.
    rewrite !inE.
    do !case: (i \in _) => //=; do! (move/(_ isT) => // || move=> _).
  rewrite Pr_preim_vars_sub; last first.
    apply/subsetP=> i; rewrite !inE; case: (i \in e) => //.
    by rewrite !andbF.
  under [in RHS]eq_bigr => A _.
    rewrite -!preim_vars_inter.
    rewrite (@preim_vars_set_vals_tl g) //.
    over.
  by rewrite -big_distrl.
under eq_bigr => A _ /=.
  rewrite Hef.
  rewrite (@preim_vars_set_vals_tl g) //.
  rewrite (@preim_vars_set_vals_tl f); last first.
    apply/setP => i.
    move/subsetP/(_ i): ee'.
    rewrite !inE.
    do !case: (i \in _) => //=; by move/(_ isT).
  over.
rewrite -big_distrl /=.
congr Rmult.
rewrite /cPr.
rewrite -big_distrl /=.
congr Rmult.
rewrite -preim_vars_inter.
rewrite (_ : e' :|: g = (e :|: g) :\: (e :\: e')); last first.
  apply/setP => i.
  move/subsetP/(_ i): e'e.
  move/subsetP/(_ i): ee'.
  rewrite !inE.
  do !case: (i \in _) => //=; do! (move/(_ isT) => // || move=> _).
rewrite Pr_preim_vars_sub; last first.
  apply/subsetP=> i; rewrite !inE; case: (i \in e) => //.
  by rewrite !andbF.
apply eq_bigr => A _.
by rewrite preim_vars_inter (@preim_vars_set_vals_tl g) //.
Qed.

Lemma preim_vars_sub (e f : {set 'I_n}) vals :
  e \subset f ->
  \sum_(a in preim_vars f vals) P a <= \sum_(a in preim_vars e vals) P a.
Proof.
move=> ef.
apply leR_sumRl => a Ha //.
  apply leRR.
apply/bigcapP => i ie.
by move/bigcapP/(_ i (subsetP ef _ ie)): Ha.
Qed.

Definition vals0 := fun i => rvar_choice (vars i).

Lemma cinde_preim_ok' (e f g : {set 'I_n}) :
  cinde_preim e f g <-> prod_vars e _|_ prod_vars f | (prod_vars g).
Proof.
rewrite /jcinde_rv /cinde_preim.
split.
- move=> Hpreim A B C.
  set vals := set_vals C (set_vals A (set_vals B vals0)).
  case /boolP: [forall i in e, vals i == set_vals A vals0 i]; last first.
    rewrite negb_forall => /existsP [i].
    rewrite negb_imply => /andP [Hie] /eqP Hvi.
    case /boolP: (i \in g) => Hig; last first.
      elim Hvi; by rewrite /vals set_vals_tl // (set_vals_hd vals0).
    rewrite /jcPr /cPr /Pr !setX1 !big_set1 !snd_RV3 !snd_RV2 !FDistMap.dE /=.
    rewrite /vals (set_vals_hd vals0) // in Hvi.
    rewrite big1.
      symmetry; rewrite big1.
        by rewrite !div0R mul0R.
      move=> u; rewrite inE /= /RV2 => Hprod; elim: Hvi.
      case/eqP: Hprod => <- <-; exact: prod_vars_inter.
    move=> u; rewrite inE /= /RV2 => Hprod; elim: Hvi.
    case/eqP: Hprod => <- _ <-; exact: prod_vars_inter.
  move/forallP => /= He.
  case /boolP: [forall i in f, vals i == set_vals B vals0 i]; last first.
    rewrite negb_forall => /existsP [i].
    rewrite negb_imply => /andP [Hif] /eqP Hvi.
    case /boolP: (i \in g) => Hig.
      rewrite /jcPr /cPr /Pr !setX1 !big_set1 !snd_RV3 !snd_RV2 !FDistMap.dE /=.
      rewrite /vals (set_vals_hd vals0) // in Hvi.
      rewrite big1.
        symmetry.
        rewrite mulRC big1.
          by rewrite !div0R mul0R.
        move=> u; rewrite inE /= /RV2 => Hprod; elim: Hvi.
        case/eqP: Hprod => <- <-; exact: prod_vars_inter.
      move=> u; rewrite inE /= /RV2 => Hprod; elim: Hvi.
      case/eqP: Hprod => _ <- <-; exact: prod_vars_inter.
    rewrite /vals set_vals_tl // in Hvi.
    case /boolP: (i \in e) => Hie; last first.
      elim Hvi; by rewrite /vals set_vals_tl // (set_vals_hd vals0).
    rewrite (set_vals_hd vals0) // in Hvi.
    rewrite -/(cinde_preim e f g) in Hpreim.
    have Hp2 : cinde_preim (e :\: (e :\: f :\: g)) f g.
      apply (@cinde_preim_sub e) => // ;
        apply/subsetP => j; rewrite !inE; by do !case: (j \in _).
    have : cinde_preim (e :\: (e :\: f :\: g)) (f :\: (f :\: e :\: g)) g.
      move/cinde_preimC in Hp2.
      apply/cinde_preimC.
      apply (@cinde_preim_sub f) => // ;
        apply/subsetP => j; rewrite !inE; by do !case: (j \in _).
    move/(_ vals).
    rewrite /cPr /Pr -!preim_vars_inter.
    rewrite (_ : _ :|: _ = (e :&: f) :|: g); last first.
      apply/setP => j; rewrite !inE; by do !case: (j \in _).
    rewrite (_ : _ :\: _ :|: _ = (e :&: f) :|: g); last first.
      apply/setP => j; rewrite !inE; by do !case: (j \in _).
    rewrite (_ : _ :\: _ :|: _ = (e :&: f) :|: g); last first.
      apply/setP => j; rewrite !inE; by do !case: (j \in _).
    case/Rxx2.
      rewrite /jcPr /cPr /Pr !setX1 !big_set1 !snd_RV3 !snd_RV2 !FDistMap.dE /=.
      rewrite /RV2.
      rewrite -!preim_prod_vars !big_set /=.
      move/mulR_eq0 => [] Hx.
      - rewrite big1; last first.
          move=> u Hu.
          move/psumR_eq0P/(_ u): Hx => -> //.
          apply/bigcapP => j.
          move: Hu; rewrite !inE => /eqP [].
          rewrite /vals => <- <- <-.
          case/boolP: (j \in g) => jg.
            by rewrite set_vals_prod_vars.
          case/boolP: (j \in e) => // je.
          by rewrite set_vals_tl // set_vals_prod_vars.
        symmetry; rewrite big1.
          by rewrite !div0R mul0R.
        move=> u Hu.
        move/psumR_eq0P/(_ u): Hx => -> //.
        apply/bigcapP => j.
        move: Hu; rewrite !inE => /eqP [].
        rewrite /vals => <- <-.
        case/boolP: (j \in g) => jg.
          by rewrite set_vals_prod_vars.
        case/boolP: (j \in e) => // je.
        by rewrite set_vals_tl // set_vals_prod_vars.
      - by rewrite /Rdiv (_ : / _ = 0) // !mulR0.
    rewrite /jcPr /cPr /Pr !setX1 !big_set1 !snd_RV3 !snd_RV2 !FDistMap.dE /=.
    rewrite /RV2.
    rewrite /Rdiv.
    set den := \sum_(a in preim_vars g vals) P a.
    set den' := \sum_(a in prod_vars g @^-1 C) P a.
    have Hden' : den' = den.
      rewrite /den /den' -preim_prod_vars.
      by apply/eq_bigl => u; rewrite !inE.
    rewrite Hden'.
    case/boolP: (den == 0).
      move/eqP/psumR_eq0P => Hden _.
      rewrite big1; last first.
        move=> u Hu; apply Hden => //.
        move: Hu; rewrite !inE => /eqP [] _ _.
        rewrite /vals => <-.
        apply/bigcapP => j Hj.
        by rewrite !inE set_vals_prod_vars.
      symmetry.
      rewrite big1; last first.
        move=> u Hu; apply Hden => //.
        move: Hu; rewrite !inE => /eqP [] _.
        rewrite /vals => <-.
        apply/bigcapP => j Hj.
        by rewrite !inE set_vals_prod_vars.
      by rewrite !mul0R.
    set num := \sum_(a in _) _.
    move => Hden Hnum.
    have Hnum' : num = den.
      by rewrite -[RHS]mul1R -Hnum -mulRA mulVR // mulR1.
    rewrite big1; last first.
      move=> u; rewrite !inE => /eqP [] HA HB.
      elim Hvi.
      by rewrite -HA -HB !set_vals_prod_vars.
    symmetry. rewrite mulRC.
    rewrite big1; last first.
      move=> u; rewrite !inE => /eqP [] HB HC.
      move: Hnum'.
      rewrite /den -/(Pr P (preim_vars g vals)).
      rewrite (_ : g = (e :&: f :|: g) :\: ((e :&: f) :\: g)); last first.
        apply/setP => j; rewrite !inE.
        by do !case: (j \in _).
      rewrite Pr_preim_vars_sub; first last.
        apply/subsetP => j; rewrite !inE.
        by do !case: (j \in _).
      rewrite (bigD1 (prod_vals ((e :&: f) :\: g) vals)) //=.
      rewrite /num -/(Pr P (preim_vars (e :&: f :|: g) vals)).
      rewrite (@preim_vars_vals _ (prod_vals (e :&: f :|: g) vals) _ vals);
        last first.
        move=> j; apply/implyP => _.
        rewrite /set_vals /prod_vals.
        rewrite ffunE.
        move: (vals j).
        by case: (j \in _).
        move/(f_equal (Rminus^~ (Pr P (preim_vars (e :&: f :|: g) vals)))).
        rewrite subRR addRC /Rminus -addRA addRN addR0 => /esym.
      move=> Hnum2.
      have : Pr P (preim_vars (e :&: f :|: g)
           (set_vals (prod_vals (e :&: f :\: g) (set_vals B vals)) vals)) = 0.
        apply: (proj1 (psumR_eq0P _) Hnum2).
          move => *. by apply sumR_ge0.
        apply/eqP.
        move/(f_equal (fun x : prod_types (e :&: f :\: g) => x i)).
        rewrite /prod_vals !ffunE /=.
        have : (vals i <> set_vals B vals i).
          rewrite /vals set_vals_tl // (@set_vals_hd vals0 _ B) //.
          rewrite (set_vals_hd vals0) //.
        move: (vals i) (set_vals B vals i).
        rewrite !inE Hig Hie Hif /= => ? ? H H'.
        by elim H.
      move/psumR_eq0P; apply => //.
      apply/bigcapP => j.
      rewrite !inE.
      move=> /orP [/andP [_ Hf] | Hg].
        rewrite -HB.
        rewrite {1}/set_vals /prod_vals ffunE.
        rewrite set_vals_prod_vars //.
        rewrite /vals -HB -HC !inE /set_vals /prod_vars !ffunE.
        move: (vars j u) (A j).
        rewrite Hf andbT.
        case: (j \in e) => //=; by case: (j \in g).
      rewrite set_vals_tl.
        by rewrite /vals -HC set_vals_prod_vars.
      by rewrite inE Hg.
    by rewrite !mul0R.
  move/forallP => /= Hf.
  move: (Hpreim vals).
  rewrite /jcPr /cPr /Pr !setX1 !big_set1 !snd_RV3 !snd_RV2 !FDistMap.dE /=.
  rewrite /RV2.
  rewrite (preim_vars_vals _ He) // (preim_vars_vals _ Hf) //.
  by rewrite -!preim_prod_vars -!preim_inter !big_set.
- move=> Hdrv vals.
  move/(_ (prod_vals e vals) (prod_vals f vals) (prod_vals g vals)): Hdrv.
  rewrite /jcPr /cPr /Pr !setX1 !big_set1 !snd_RV3 !snd_RV2 !FDistMap.dE /=.
  rewrite /RV2.
  rewrite -(preim_vars_vals (prod_vals e vals) (prod_vals_vars e vals)).
  rewrite -(preim_vars_vals (prod_vals f vals) (prod_vals_vars f vals)).
  rewrite -(preim_vars_vals (prod_vals g vals) (prod_vals_vars g vals)).
  by rewrite -!preim_prod_vars -!preim_inter !big_set.
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
