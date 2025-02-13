(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg zmodp matrix.
From mathcomp Require Import Rstruct reals.
Require Import ssr_ext ssralg_ext f2.

(**md**************************************************************************)
(* # The Summary Operator                                                     *)
(*                                                                            *)
(* This file provides a formalization of the summary operator used in         *)
(* pencil-and-paper proofs in modern coding theory.                           *)
(*                                                                            *)
(* ```                                                                        *)
(*   \sum_( x = d [~ s]) F == summation over the vectors x equal to d on all  *)
(*                            components except the freely enumerated         *)
(*                            indices in s                                    *)
(*      summary_fold r d e == alternative expression of \sum_( x = d [~ r]) e *)
(* ```                                                                        *)
(******************************************************************************)

Reserved Notation "\sum_ ( x '=' d [~ s ] ) F" (at level 41,
  F at level 41, x, s, d at level 50,
    format "'[' \sum_ ( x  '='  d  [~  s ] ) '/  '  F ']'").
Reserved Notation "\sum_ ( x '=' d [~ s ] '|' P ) F" (at level 41,
  F at level 41, x, s, d at level 50,
    format "'[' \sum_ ( x  '='  d  [~  s ]  '|'  P ) '/  '  F ']'").

Declare Scope summary_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.

Section free_on.
Variables (A : eqType) (n : nat).

Definition freeon (s : {set 'I_n}) (t d : 'rV[A]_n) : bool :=
  [forall j, (j \notin s) ==> (t ``_ j == d ``_ j)].

Lemma freeon_refl V (t : 'rV[A]_n) : freeon V t t.
Proof. by apply/forallP => n0; rewrite eqxx implybT. Qed.

Lemma freeon_sym V (t d : 'rV[A]_n) : freeon V t d = freeon V d t.
Proof. apply/forallP/forallP => /= H x; by rewrite eq_sym. Qed.

Lemma freeon0 (t d : 'rV_n) : (freeon set0 t d) = (t == d).
Proof.
apply/forallP/eqP => /= [H|-> x]; last by rewrite eqxx implybT.
apply/rowP => i; move: (H i); by rewrite !inE implyTb => /eqP.
Qed.

Lemma freeon_notin t d n0 V : freeon V d t -> n0 \notin V -> d ``_ n0 = t ``_ n0.
Proof.
move/forallP/(_ n0)/implyP => H1 H2; by rewrite (eqP (H1 H2)).
Qed.

Lemma freeon_all (t d : 'rV_n) n0 : (t ``_ n0 == d ``_ n0) = freeon (setT :\ n0) d t.
Proof.
apply/idP/idP => H.
  apply/forallP => i.
  rewrite !inE andbT negbK; apply/implyP => /eqP ->; by rewrite eq_sym.
by rewrite (@freeon_notin t _ _ (setT :\ n0)) // !inE eqxx.
Qed.

Lemma freeon_row_set n0 (d : 'rV[A]_n) x : freeon [set n0] d (d `[ n0 := x ]).
Proof.
apply/forallP => /= i; rewrite !inE !mxE.
by have [//|] := eqVneq i n0; rewrite implyTb.
Qed.

End free_on.

Lemma freeon1 (F : finFieldType) {n} i (d : 'rV[F]_n) : forall t,
  freeon [set i] d t = (t \in [set d `[ i := x ] | x in F]).
Proof.
move=> t.
case/boolP : (_ \in _).
  case/imsetP => /= x _ ->; by rewrite freeon_row_set.
apply: contraNF.
move/forallP => /= X.
apply/imsetP => /=.
exists (t ``_ i) => //.
apply/rowP => b.
rewrite mxE.
case: ifPn => [/eqP -> //| bi].
apply/esym/eqP.
move: (X b) => /implyP; apply.
by rewrite in_set1.
Qed.

(** sum over vectors t whose V projection is free and its complemented fixed by d *)
Notation "\sum_ ( x '=' d [~ s ] ) F" :=
  (\sum_( x | freeon s d x ) F) : summary_scope.
Notation "\sum_ ( x '=' d [~ s ] '|' P ) F" :=
  (\sum_( x | freeon s d x && P x) F) : summary_scope.

Local Open Scope summary_scope.

Section rsum_freeon.
Let R := Rdefinitions.R.
Variable n : nat.

Lemma rsum_freeon0 (d : 'rV['F_2]_n) (F : 'rV_n -> R) :
  \sum_(t = d [~set0]) F t = F d.
Proof.
transitivity (\sum_(t | t == d) F t)%R.
  apply eq_bigl => /= t; by rewrite freeon0 eq_sym.
by rewrite (big_pred1 d).
Qed.

Lemma rsum_freeon1 n2 (d : 'rV['F_2]_n) (F : 'rV_n -> R) :
  \sum_(t = d [~[set n2]]) F t = (F (d `[ n2 := Zp0 ]) + F (d `[ n2 := Zp1 ]))%R.
Proof.
transitivity (\sum_(t | (t \in [set d `[ n2 := x ] | x in 'F_2])) F t)%R.
  apply eq_bigl => /= t.
  by rewrite freeon1.
rewrite big_imset /=; last by exact: inj_row_set.
rewrite (bigID (pred1 Zp0)) /= (big_pred1 Zp0) //.
rewrite (bigID (pred1 Zp1)) /= (big_pred1 Zp1); last by case/F2P.
rewrite big_pred0; last by case/F2P.
by rewrite GRing.addr0.
Qed.

End rsum_freeon.

Section alternative_definitions_of_summary.
Let R := Rdefinitions.R.
Variables n : nat.

Definition summary_powerset (X : {set 'I_n}) (d : 'rV['F_2]_n) (e : 'rV_n -> R) :=
  let bvect s := \row_(i < n) if i \in X then F2_of_bool (i \in s) else d ``_ i in
  \sum_(s in powerset X) e (bvect s).

Local Open Scope tuple_ext_scope.

(* used in ldpc_algo_proof.v *)
Lemma summary_powersetE (s : {set 'I_n}) (d : 'rV['F_2]_n) (e : 'rV['F_2]_n -> R) :
  \sum_(t = d [~s]) e t = summary_powerset s d e.
Proof.
rewrite /summary_powerset.
transitivity (\sum_(f in {ffun 'I_n -> 'F_2} | freeon s (\row_i f i) d)
  e (\row_(k0 < n) if k0 \in s then (fgraph f) !_ (cast_ord (esym (@card_ord n)) k0)
    else d ``_ k0))%R.
  rewrite (reindex_onto (fun p => [ffun x => p !_ (cast_ord (esym (@card_ord n)) x)])
    (fun y => fgraph y)) /=; last first.
    move=> /= f Hf.
    apply/ffunP => /= k0.
    by rewrite ffunE -enum_rank_ord tnth_fgraph enum_rankK.
  rewrite (reindex_onto (fun p => row_of_tuple (tcast (@card_ord n) p))
    (fun y => tcast (esym (@card_ord n)) (tuple_of_row y))) /=; last first.
    move=> k0 Hk0.
    apply/rowP => b.
    by rewrite !mxE 2!tcastE tnth_mktuple esymK -enum_rank_ord -enum_val_ord enum_rankK.
  apply eq_big.
    move=> t.
    congr (_ && _).
      rewrite freeon_sym; congr (freeon s _ d).
      apply/rowP => i; by rewrite !mxE ffunE tcastE.
    congr (_  == t); apply eq_from_tnth => i /=.
    rewrite !tcastE tnth_mktuple mxE tcastE tnth_fgraph ffunE.
    by rewrite esymK -enum_val_ord.
  move=> t Ht.
  congr e.
  apply/rowP => b; rewrite !mxE.
  case/boolP : (b \in s) => bs.
    by rewrite tnth_fgraph ffunE tcastE enum_val_ord cast_ordK.
  rewrite tcastE.
  case/andP : Ht => Ht1 Ht2.
  move/forallP : Ht1.
  move/(_ b).
  rewrite bs implyTb.
  move/eqP => ->.
  by rewrite /row_of_tuple mxE tcastE.
transitivity (\sum_(f in {ffun 'I_n -> bool} | freeon s d (\row_i F2_of_bool (f i)))
      e (\row_k0 (if k0 \in s
                  then F2_of_bool ((fgraph f) !_ (cast_ord (esym (card_ord n)) k0))
                  else d ``_ k0)))%R.
  rewrite (reindex_onto (fun f : {ffun 'I_n -> bool} => [ffun x => F2_of_bool (f x)])
    (fun f : {ffun 'I_n -> 'F_2} => [ffun x => bool_of_F2 (f x)])); last first.
    move=> /= f Hf.
    apply/ffunP => /= k0.
    by rewrite !ffunE bool_of_F2K.
  apply eq_big.
    move=> /= f.
    rewrite freeon_sym -[RHS]andbT; congr (freeon s d _ && _).
      apply/rowP => i; by rewrite !mxE ffunE.
    by apply/eqP/ffunP => i; rewrite !ffunE F2_of_boolK.
  move=> /= f.
  case/andP => H1 H2.
  congr e.
  apply/rowP => b; rewrite !mxE.
  case : (b \in s) => //.
  by rewrite 2!tnth_fgraph ffunE.
transitivity (\sum_(f in {set 'I_n} | freeon s d (\row_i F2_of_bool (i \in f)))
      e (\row_k0 (if k0 \in s then F2_of_bool (k0 \in f) else d ``_ k0)))%R.
  have @f' : {set 'I_n} -> {ffun 'I_n -> bool} := (fun x => [ffun i => i \in x]).
  rewrite (reindex_onto (fun f : {ffun 'I_n -> bool} => [set x | f x ]) f').
    apply eq_big => /= f.
      rewrite -[LHS]andbT; congr (freeon s d _ && _).
        by apply/rowP => i; rewrite !mxE inE.
      apply/esym/eqP/ffunP => /= i.
      by rewrite /f' ffunE inE.
    move=> Hf.
    congr e.
    apply/rowP => b; rewrite !mxE.
    case: (b \in s) => //.
    by rewrite inE tnth_fgraph -enum_rank_ord enum_rankK.
  move=> /= f Hf.
  apply/setP => /= k0.
  by rewrite inE /f' ffunE.
transitivity (\sum_(f in {set 'I_n} | f \subset s) e (\row_(k0 < n) if k0 \in s then F2_of_bool (k0 \in f) else d ``_ k0))%R; last first.
  apply eq_bigl => /= s0.
  by rewrite powersetE.
rewrite (reindex_onto (fun f => f :|: [set j | (j \notin s) && bool_of_F2 (d ``_ j)])
                      (fun f => f :&: s)); last first.
  move=> /= f fs.
  apply/setP => /= k0.
  rewrite !inE.
  case K : (k0 \in f) => /=; case L : (k0 \in s) => //=;
    by move/forallP : fs => /(_ k0); rewrite L implyTb mxE K => /eqP ->.
apply eq_big => /= s0.
  apply/andP/subsetP.
    case=> /forallP H1 H2 /= k0 Hk0.
    rewrite -(eqP H2) !inE in Hk0.
    case/andP : Hk0.
    by case/orP.
  move=> s0s; split.
    apply/forallP => /= k0; apply/implyP => Hk0.
    rewrite mxE !inE Hk0 /=.
    case K : (k0 \in s0) => /=; last by rewrite bool_of_F2K.
    move: (s0s k0).
    by rewrite K (negbTE Hk0) => /(_ erefl).
  apply/eqP/setP => /= k0; rewrite !inE.
  case K : (k0 \in s0) => /=; first by apply s0s.
  by case: (k0 \in s) => //; rewrite andbF.
move=> K.
congr e.
apply/rowP => b; rewrite !mxE.
case: ifP => // bs.
rewrite !inE.
by case : (b \in s0) => //=; rewrite bs.
Qed.

Local Close Scope tuple_ext_scope.

Definition summary_fold (X : {set 'I_n}) d e : R :=
  foldr (fun i F t => \sum_(b in 'F_2) F (t `[ i := b ])) e (enum X) d.

Lemma set_mem {T : finType} (s : {set T}) : s = finset (ssrbool.mem (enum s)).
Proof. apply/setP=> i. by rewrite !inE mem_enum. Qed.

(* used in ldpc_algo_proof.v *)
Lemma summary_foldE s d e : summary_powerset s d e = summary_fold s d e.
Proof.
rewrite /summary_powerset /summary_fold.
rewrite {1 2}(set_mem s).
move: (enum s) d e (enum_uniq (ssrbool.mem s)).
elim => {s} [|n1 s IH] d e Hs /=.
  rewrite powerset0 big_set1; congr e.
  apply/rowP => i; by rewrite mxE /= in_set0.
rewrite (partition_big_imset (fun s : {set 'I_n} => n1 \in s)).
rewrite (_ : [set n1 \in (s0 : {set 'I_n}) | s0 in _] = [set: bool]); last first.
  apply/setP => x; rewrite !inE /=.
  apply/imsetP; case: x.
  - exists [set n1]; last by rewrite in_set1 eqxx.
    by rewrite powersetE sub1set !inE eqxx.
  - exists set0; last by rewrite in_set0.
    by rewrite powersetE sub0set.
rewrite (reindex F2_of_bool bijective_F2_of_bool).
apply eq_big => [i|i _]; first by rewrite /= !inE.
case/andP : Hs => /= Hn1 Hs.
rewrite -IH; last by [].
rewrite (reindex_onto (fun f => if i then n1 |: f else f) (fun f => f :\ n1)); last first.
  move=> /= j; rewrite !inE.
  move/andP=> [] /subsetP Hj.
  case: i => Hi.
    by rewrite setD1K // (eqP Hi).
  by apply/eqP; rewrite eqEsubset subD1set /= subsetD1 (eqP Hi) andbT.
apply eq_big=> j; last first.
  move=> Hi.
  congr e.
  apply/rowP => k; rewrite !mxE !inE /=.
  have [Hkn1|Hkn1] := eqVneq k n1.
    rewrite Hkn1 (negbTE Hn1).
    case: ifP Hi => [? Hi|? /=].
      by rewrite in_setU1 eqxx.
    by move=> -/andP[/andP[_ /eqP -> _ //]].
  case: ifP => //; case: ifPn => //=.
    by rewrite /= in_setU1 (negbTE Hkn1) orFb => _ ->.
  by move=> _ ->.
case: ifP => [Hi|Hi].
- rewrite /powerset !inE eqxx andbT /=.
  case/boolP : (j \subset [set i in s]) => Hj.
    rewrite setU1K ?eqxx ?andbT; last first.
      apply: contra Hn1; move/subsetP : Hj => /(_ n1).
      by rewrite inE.
    apply/subsetP => x /setU1P -[|] Hx.
      by rewrite Hx 3!inE eqxx.
    move/subsetP/(_ _ Hx) : Hj.
    rewrite !inE => ->; by rewrite orbT.
  case/boolP : ((n1 |: j) :\ n1 == j) => Hn1j; last first.
    by rewrite andbF.
  rewrite andbT.
  apply: contraNF Hj => /subsetP Hj'.
  apply/subsetP => k Hk.
  move: Hj' => /(_ k).
  rewrite in_setU1 Hk orbT => /(_ isT).
  rewrite !inE => /orP[/eqP kn1 | //].
  by move: Hk; rewrite kn1 -(eqP Hn1j) setD11.
- rewrite /powerset !inE.
  case/boolP : (j \subset [set x in s]) => Hj.
    case/boolP : (n1 \in j) => Hn1j.
      move/subsetP/(_ _ Hn1j) : Hj.
      by rewrite !inE (negbTE Hn1).
    rewrite eqxx andbT.
    have -> : j :\ n1 = j.
      apply/setP => k; rewrite !inE.
      have [->/=|//] := eqVneq k n1.
      exact/esym/negbTE.
    rewrite eqxx andbT.
    apply/subsetP=> k Hk.
    move/subsetP/(_ _ Hk): Hj.
    by rewrite !inE => ->; rewrite orbT.
  case/boolP : (n1 \in j) => Hn1j; first by rewrite /= andbF.
  have -> : j :\ n1 = j.
    apply/setP => k; rewrite !inE.
    have [/= ->|//] := eqVneq k n1.
    exact/esym/negbTE.
  rewrite !eqxx !andbT.
  apply/subsetP => Hjs.
  move/subsetP: Hj; apply => k Hk.
  move: (Hjs _ Hk).
  rewrite !inE => /orP[/eqP ?|//].
  by subst n1; rewrite Hk in Hn1j.
Qed.

End alternative_definitions_of_summary.
