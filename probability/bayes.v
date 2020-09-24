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
rewrite /cinde_drv /cinde_preim /preim_vars.
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

Definition vals0 := fun i => rvar_choice (vars i).

Lemma prod_vars_inter (e g : {set 'I_n}) vals i u :
  i \in e -> i \in g ->
  set_vals (prod_vars e u) vals i = set_vals (prod_vars g u) vals i.
Proof.
rewrite /set_vals /prod_vars !ffunE.
by case: (i \in e) (i \in g) => // -[].
Qed.

Lemma cinde_preim_ok' (e f g : {set 'I_n}) :
  cinde_preim e f g <-> prod_vars e _|_ prod_vars f | (prod_vars g).
Proof.
rewrite /cinde_drv /cinde_preim.
split.
- move=> Hpreim A B C.
  set vals := set_vals C (set_vals A (set_vals B vals0)).
  case /boolP: [forall i, (i \in e) ==> (vals i == (set_vals A vals0) i)];
    last first.
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
  case /boolP: [forall i, (i \in f) ==> (vals i == (set_vals B vals0) i)];
    last first.
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
    move: (Hpreim vals).
    admit.
  move/forallP => /= Hf.
  move: (Hpreim vals).
  rewrite /jcPr /cPr /Pr !setX1 !big_set1 !snd_RV3 !snd_RV2 !FDistMap.dE /=.
  rewrite /RV2.
  admit.
- move=> Hdrv vals.
  move/(_ (prod_vals e vals) (prod_vals f vals) (prod_vals g vals)): Hdrv.
  rewrite /jcPr /cPr /Pr /dist_of_RV.
  rewrite !setX1 !big_set1 !snd_RV3 !snd_RV2 !FDistMap.dE /=.
Abort.
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
