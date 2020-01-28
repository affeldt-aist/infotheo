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

Lemma cinde_preim_ok (i j k : 'I_n) :
  i <> j -> i <> k -> j <> k ->
  cinde_preim [set i] [set j] [set k] <-> vars i _|_ vars j | (vars k).
Proof.
move=> nij nik njk.
rewrite /cinde_drv /cinde_preim /preim_vars.
split.
- move=> Hpreim a b c.
  set vals := set_val a (set_val b (set_val c (fun i => rvar_choice (vars i)))).
  move/(_ vals): Hpreim.
  rewrite !big_set1 /cPr /cPr0 !setX1 !snd_RV3 !snd_RV2.
  rewrite ![Pr _ [set _]]/Pr !big_set1 /RVar.d !FDistMap.dE /Pr.
  have -> : vals i = a.
    rewrite /vals /set_val eq_dec_refl.
    rewrite -Eqdep_dec.eq_rect_eq_dec //; exact: ord_eq_dec.
  have -> : vals j = b.
    rewrite /vals /set_val eq_dec_refl.
    case: Nat.eq_dec => ij; first by elim nij; apply ord_inj.
    rewrite -Eqdep_dec.eq_rect_eq_dec //; exact: ord_eq_dec.
  have -> : vals k = c.
    rewrite /vals /set_val eq_dec_refl.
    case: Nat.eq_dec => ik; first by elim nik; apply ord_inj.
    case: Nat.eq_dec => jk; first by elim njk; apply ord_inj.
    rewrite -Eqdep_dec.eq_rect_eq_dec //; exact: ord_eq_dec.
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
