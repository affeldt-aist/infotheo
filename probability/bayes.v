(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import all_ssreflect ssralg fingroup perm finalg matrix.
From mathcomp Require boolp.
Require Import Reals. (* Lra Nsatz. *)
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop.
Require Import fdist jfdist cinde.

Local Open Scope tuple_ext_scope.
Local Open Scope proba_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* wip *)

Module BN.
Section bn.
Variable U : finType.
Variable P : fdist U.
Variable n : nat.
Variable types : 'I_n -> finType.
Variable vars : forall i, {RV P -> types i}.

Section preim.
Local Open Scope R_scope.

Definition preim_vars (I : {set 'I_n}) (vals : forall i, types i) :=
  \bigcap_(i in I) vars i @^-1 (vals i).

Definition cinde_preim (e f g : {set 'I_n}) :=
  forall vals,
    let E := preim_vars e vals in
    let F := preim_vars f vals in
    let G := preim_vars g vals in
    `Pr_ P [ E :&: F | G ] = `Pr_ P [ E | G ] * `Pr_ P [ F | G ].

Definition rvar_choice : forall A : finType, {RV P -> A} -> A.
move=> A X.
move: (fdist_card_neq0 (RVar.d X)).
move He: (enum A) => [|a l] //.
move/(f_equal size): He.
by rewrite -cardE => ->.
Defined.

Definition ord_eq_dec (i j : 'I_n) : {i = j}+{i <> j}.
case (Nat.eq_dec i j); intro ij.
- left; now apply ord_inj.
- right; intro ij'; apply ij; now f_equal.
Defined.

Definition set_val (i : 'I_n) (v : types i) (vals : forall j, types j) :=
  fun j : 'I_n =>
    match Nat.eq_dec i j return types j with
    | left ij => eq_rect i (fun i => Finite.sort (types i)) v j (ord_inj ij)
    | right _ => vals j
    end.

Lemma eq_dec_refl i : Nat.eq_dec i i = left (erefl i).
Proof.
case: Nat.eq_dec => Hi; last by elim Hi.
congr left; by rewrite (Eqdep_dec.UIP_refl_nat _ Hi).
Qed.

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
  move/(_ vals): Hpreim.
  rewrite !big_set1 /cPr /cPr0 !setX1 !snd_RV3 !snd_RV2.
  rewrite ![Pr _ [set _]]/Pr !big_set1 /RVar.d !FDistMap.dE /Pr /=.
  have vi : vals i = a by rewrite /vals set_val_hd.
  have Hvals := erefl vals.
  rewrite {2}/vals in Hvals.
  wlog: c vals vi Hvals / vals k = c.
    case: (ord_eq_dec i k) c vals vi Hvals.
      move=> <- {k} c.
      case ac: (a == c).
        rewrite -(eqP ac) {ac c}.
        move=> vals Ha Hvals; by apply.
      set num := \sum_(d | _) P d.
      have -> : num = 0.
        apply prsumr_eq0P => // u /andP [] /andP [] /= /eqP ->.
        by rewrite ac.
      rewrite div0R.
      set num' := \sum_(d | _) P d.
      have -> : num' = 0.
        apply prsumr_eq0P => // u /andP [] /= /eqP ->.
        by rewrite ac.
      by rewrite /Rdiv !mul0R.
    move=> nik c vals Ha Hvals.
    apply => //.
    by rewrite Hvals set_val_tl // set_val_hd.
  move=> vk.
  wlog: b vals vi vk Hvals / vals j = b.
    case: (ord_eq_dec i j) b Hvals.
      move=> <- {j} b.
      case ab: (a == b).
        rewrite -(eqP ab); move=> Hvals; by apply.
      move=> Hvals _.
      rewrite setIid vi vk.
      set x := _ / _.
      move/Rxx2 => [].
        move/mulR_eq0 => [] Hx.
        - set num := \sum_(u | _) _.
          have -> : num = 0.
            apply prsumr_eq0P => // u /andP [] /andP [] /= /eqP ->.
            by rewrite ab.
          symmetry.
          rewrite (_ : \sum_(u | _) _ = 0).
            by rewrite !div0R mul0R.
          rewrite -Hx.
          apply eq_bigl => u.
          by rewrite !inE.
        - rewrite /Rdiv (_ : / _ = 0) ?mulR0 // -Hx; congr (/ _).
          by apply eq_bigl => u; rewrite !inE.
      move=> Hx.
      set den := \sum_(u | _ c) _.
      case/boolP: (den == 0) => Hden.
        have Hden': forall a, vars k a == c -> P a = 0.
          move=> u Hu.
          by move/eqP/prsumr_eq0P: Hden => ->.
        rewrite !(proj2 (prsumr_eq0P _)) //;
          try by move=> u /andP [] /= _; apply Hden'.
        by rewrite !div0R mul0R.
      set num := \sum_(u | _ == (b, c)) _.
      case/boolP: (num == 0) => /eqP Hnum.
        rewrite Hnum (proj2 (prsumr_eq0P _)) //.
          by rewrite div0R !mulR0.
        move=> u /andP [] /andP [] /= /eqP -> //.
        by rewrite ab.
      elim Hnum.
      apply prsumr_eq0P => // u /andP [] /= Hi Hk.
      move: Hx; subst x.
      rewrite (_ : \sum_(u in _ @^-1 c) _ = den); last first.
        by apply eq_bigl => ?; rewrite !inE.
      move/(f_equal (Rmult ^~ den)).
      rewrite /Rdiv -mulRA mulVR // mulR1 mul1R.
      rewrite /den (bigID (fun u => vars i u == a) (fun u => _ == c)) /=.
      set ca := \sum_(v | _ && _) _.
      rewrite (_ : \sum_(v in _) _ = ca); last first.
        by apply eq_bigl => v; rewrite !inE andbC.
      move/(f_equal (Rminus ^~ ca)).
      rewrite subRR addRC addRK => /esym /prsumr_eq0P; apply => //.
      by rewrite Hk (eqP Hi) eq_sym ab.
    case: (ord_eq_dec k j).
      move=> <- {j} ik b.
      case cb: (c == b).
        rewrite -(eqP cb) => Hvals; by apply.
      move=> Hvals _ _.
      set num := \sum_(d | _) P d.
      have -> : num = 0.
        apply prsumr_eq0P => // u /andP [] /andP [] /= _ /eqP ->.
        by rewrite eq_sym cb.
      rewrite div0R mulRC.
      set num' := \sum_(d | _) P d.
      have -> : num' = 0.
        apply prsumr_eq0P => // u /andP [] /= /eqP ->.
        by rewrite eq_sym cb.
      by rewrite /Rdiv !mul0R.
    move=> nkj nij b Hvals.
    apply => //.
    by rewrite Hvals set_val_tl // set_val_tl // set_val_hd.
  rewrite vi vk => ->.
  set lhs1 := _ / _ => Hpreim.
  set lhs2 := _ / _.
  have <- : lhs1 = lhs2.
    by congr (_ / _); apply eq_bigl => u; rewrite !inE.
  rewrite Hpreim.
  by congr ((_/_) * (_/_)); apply eq_bigl => u; rewrite !inE.
- move=> Hdrv vals.
  move/(_ (vals i) (vals j) (vals k)): Hdrv.
  rewrite !big_set1 /cPr /cPr0 !setX1 !snd_RV3 !snd_RV2.
  rewrite ![Pr _ [set _]]/Pr !big_set1 /RVar.d !FDistMap.dE /Pr.
  set lhs1 := _ / _ => Hdrv.
  set lhs2 := _ / _.
  have -> : lhs2 = lhs1.
    by congr (_ / _); apply eq_bigl => u; rewrite !inE.
  rewrite Hdrv.
  by congr ((_/_) * (_/_)); apply eq_bigl => u; rewrite !inE.
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
