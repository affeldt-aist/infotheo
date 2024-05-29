(* infotheo: information theory and error-correcting codes in Coq               *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later              *)

From mathcomp Require Import all_ssreflect ssralg ssrnum matrix.
From mathcomp Require Import reals Rstruct zmodp ring lra.
Require Import Reals.

Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond graphoid.
Import GRing.Theory.

(******************************************************************************)
(*                              SMC Useful Tools                              *)
(*     From: Information-theoretically Secure Number-product Protocol         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Section more_independent_rv_lemmas.

Variables (A : finType) (P : R.-fdist A) (TA TB TC TD : finType).
Variables (X : {RV P -> TA}) (Y : {RV P -> TB}) (Z : {RV P -> TC}).
Variables (UA UB : finType) (f : TA -> UA) (g : TB -> UB).

Local Notation "f × g" :=
  (fun xy => (f xy.1, g xy.2)) (at level 10).

(* Information-Theoretically Secure Number Protocol*)
(* Lemma 3.1 *)
Lemma inde_rv_comp : inde_rv X Y -> inde_rv (f `o X) (g `o Y).
Proof.
move/inde_rv_events'.
rewrite /inde_rv_ev.
move=> H i j.
rewrite -[LHS]pr_eq_set1.
rewrite comp_RV2_ACA /=.
rewrite pr_in_comp'.
rewrite -setX1.
rewrite preimsetX.
rewrite !/(_ @^-1: _).
rewrite H. (* second to third line in the pencil-paper proof *)
rewrite -!pr_in_comp'.
by rewrite !pr_eq_set1.
Qed.

(* Lemma 3.2 *)
Lemma RV2_inde_rv_snd : P |= [% X, Y] _|_ Z -> P |= Y _|_ Z.
Proof.
move/inde_rv_events'.
move=> H y z.
rewrite -[LHS]pr_eq_set1 pr_inE'.
rewrite -(snd_RV2 X [% Y, Z]) Pr_fdist_snd.
rewrite -pr_inE'.
rewrite setTE -setX1.
rewrite pr_in_pairA.
rewrite H.
by rewrite -setTE pr_inE' -Pr_fdist_snd snd_RV2 -pr_inE' !pr_eq_set1.
Qed.


Lemma cpr_prd_unit_RV : X _|_ Y | [% unit_RV P, Z] -> X _|_ Y | Z.
Proof.
move=>H a b c.
have:=H a b (tt,c).
Undo 2.
move=> + a  /[swap] b c.
Undo 1.
move=> + a b c => /(_ a b (tt,c)).
rewrite 3!cpr_eqE'.
have->: finset (preim [% unit_RV P, Z] (pred1 (tt, c))) = finset (preim Z (pred1 c)).
  apply /setP => x.
  by rewrite !inE.
by rewrite -!cpr_eqE'.
Qed.

(* Lemma 3.3 *)
Lemma inde_RV2_cinde : P |= [% X, Z] _|_ Y -> X _|_ Y | Z.
Proof.
move/cinde_rv_unit /cinde_rv_sym.
move/weak_union /cinde_rv_sym.
by apply cpr_prd_unit_RV.
Qed.

End more_independent_rv_lemmas.

Section lemma_3_4.

Lemma cpr_eqE_mul (U : finType) (P : {fdist U}) (TA TB : finType)
  (X : {RV P -> TA}) (Y : {RV P -> TB}) a b :
  `Pr[ X = a | Y = b ] * `Pr[Y = b] = `Pr[ [% X, Y] = (a, b) ].
Proof.
rewrite cpr_eqE.
rewrite !coqRE.
rewrite -!mulrA.
have [|?] := eqVneq `Pr[ Y = b ] 0.
  move=>Y0.
  rewrite Y0.
  rewrite !mulr0.
  rewrite pr_eq_pairC.
  by rewrite pr_eq_domin_RV2.
rewrite mulVr //.
by rewrite mulr1.
Qed.

Variable T : finType.
Variable P : R.-fdist T.
Variable n : nat.
Notation p := n.+1.
Variables (X Y : {RV P -> 'I_p}).

(* How to express "the distribution of random variable Y is uniform distribution" as a prop. *)
Variable pY_unif : `p_ Y = fdist_uniform (card_ord p).
Variable XY_indep : P |= X _|_ Y.

(* Add two random variables = add results from two functions. *)
(* We use this because add_RV is in coqR *)
Definition add_RV' : {RV P -> 'I_p} := X \+ Y.

(* Lemma 3.4 *)
Lemma add_RV_unif : `p_ add_RV' = fdist_uniform (card_ord p).
(* TODO: I cannot directly put X \+ Y in this lemma because the implicit P cannot be inferred. *)
Proof.
apply: fdist_ext=> /= i.
rewrite fdist_uniformE /=.
transitivity (`Pr[add_RV' \in [set i]]).
  by rewrite pr_inE' /Pr big_set1.
rewrite (reasoning_by_cases _ X).
transitivity (\sum_(k <- fin_img X) `Pr[ [% X, Y] \in ([set k] `* [set i-k]%mcR) ]).
  apply eq_bigr=> k _.
  rewrite !pr_eq_setE.
  rewrite /Pr.
  apply: eq_bigl.
  move=>r /=.
  rewrite !inE /=.
  rewrite /add_RV'.
  rewrite andbC; apply: andb_id2l.
  rewrite /=.
  move /eqP ->.
  rewrite [RHS]eq_sym.
  by rewrite subr_eq addrC eq_sym.
under eq_bigr do rewrite setX1 pr_eq_set1 -cpr_eqE_mul.
under eq_bigr=> k _.
  (* Similar to `have->:`, set the wanted form *)
  rewrite (_ : _ * _ = `Pr[ X = k ] * `Pr[ Y = (i - k)%mcR ] ); last first.
  rewrite cpr_eqE.  (* To remove the form of conditional probability *)
  rewrite XY_indep. (* So we can split it from `Pr [% X, Y] to `Pr X and `Pr Y*)
  rewrite !coqRE. (* Because / and * are in stdlib, not in mathcomp *)
  rewrite -!mulrA.
  (* case analysis on (`Pr[ Y = (i - k)%mcR ] == 0) *)
  have [|H] := eqVneq `Pr[ Y = (i - k)%mcR ] 0.
  - by move->; rewrite !mulr0.
  - by rewrite mulVr ?mulr1 //.
  over.
under eq_bigr=> k _.
  rewrite [X in _ * X]pr_eqE' pY_unif fdist_uniformE /=.
  rewrite -cpr_eq_unit_RV.
  over.
rewrite -big_distrl /=.  (* Pull the const part `Pr[ Y = (i - k) ] from the \sum_k *)
by rewrite cPr_1 ?mul1r // pr_eq_unit oner_neq0.
Qed.

End lemma_3_4.

Section lemma_3_5.
  
Variable T : finType.
Variable P : R.-fdist T.
Variable n : nat.
Notation p := n.+1.
Variable i y : 'I_p.
Variables (X Y Z: {RV P -> 'I_p}).

Variable pZ_unif : `p_ Z = fdist_uniform (card_ord p).
Variable Z_XY_indep : inde_rv Z [%X, Y].

Let XZ : {RV P -> 'I_p} := X \+ Z.
(* TODO: I cannot directly put X\+Z in lemma because it compains about:

   Cannot infer the implicit parameter P of pr_eq whose type is "R.-fdistT" in:.... *)

Lemma lemma_3_5 : `Pr[ XZ = i | Y = y] = `Pr[ XZ = i].  (* The paper way to prove P |= X\+Z _|_ Y *)
Proof.
transitivity (\sum_(k < p) `Pr[[% X, Z] = (k, inord (i - k)%mcR) | Y = y]).
  rewrite -cpr_eq_set1.
  (*Although About cpr_eq_set1 only show Y \in y,
    the original version actually converts both X and Y*)
  rewrite (@creasoning_by_cases T P _ _ _ XZ X Y).
  transitivity ((\sum_(b < p) `Pr[ [% XZ, X] \in ([set i] `* [set b]) | Y = y ])).
  admit.
  apply: eq_bigr => k _.
  Search ([set _] `* [set _]).
  rewrite setX1. (* From two sets' `* to one pair*)
  rewrite cpr_inE cpr_eqE pr_eq_set1. (* Make two sides "similar"*)
  congr (_ / _)%coqR; last first.
  rewrite setX1.
  rewrite pr_eq_set1.
  rewrite !pr_eqE /Pr.
  apply: eq_bigl => j.
  rewrite !inE.
  rewrite /RV2.
  rewrite !xpair_eqE.
  rewrite /XZ /=.
  congr (_ && _).
  apply/idP/idP.
    move => /andP [ /eqP <- /eqP <- ].
    rewrite eqxx /=.
    apply/eqP /val_inj => /=.
    Set Printing Coercions.
    rewrite inordK.
      Unset Printing Coercions.
      Search modn.
      rewrite modnDm.
      have ->: (X j + Z j + (p - X j) = Z j + p)%nat.
      rewrite (addnC _ (Z j)) -addnA subnKC //=.
      apply/ltnW /ltn_ord.
      by rewrite modnDr modn_small.
    Search modn.
    exact: ltn_pmod.
  move => /andP [ /eqP <- /eqP -> ].
  rewrite eqxx andbT. (* andbT remove the (&& true) part*)
  Disable Notation "_ = _".
  apply/eqP.
  apply/val_inj => /=.
  rewrite inordK; last exact:ltn_pmod.
  rewrite -(@modn_small (X j) p); last exact:ltn_ord.
  rewrite -(modnDm i) -(modnDm (i%%p)).
  rewrite addnA.
  


  rewrite -[in LHS](@modn_small i p); last exact:ltn_ord.

  rewrite !modnDm.
  Search modn.
  rewrite addrA.
  rewrite (modnDm i).
  Search modn subn.


  
admit.
transitivity (\sum_(k < p) `Pr[X = k | Y = y] * `Pr[Z = inord (i - k) | [%X, Y] = (k, y) ] ).
admit.
transitivity (\sum_(k < p) `Pr[X = k | Y = y] * `Pr[Z = inord (i - k) ] ).
admit.
transitivity (\sum_(k < p) `Pr[X = k | Y = y] * p%:R^-1).
admit.
transitivity (p%:R^-1 : R). (* cannot know which ring to convert to, so need the 2nd :R -- it is part of Coq language.*)
admit.

Search `Pr[ _ = _ | _ = _ ] `Pr[ _ \in _ | _ \in _ ].
(* TODO: cannot find a lemma to convert the X in cpr to event *)
rewrite -cpr_eq_set1.
rewrite -pr_eq_set1.

Undo 2.
rewrite cpr_eqE.
rewrite !coqRE.
rewrite -pr_eq_set1.
Search creasoning_by_cases.

transitivity (\sum_(k <- fin_img ))

rewrite -cpr_eq_set1.




rewrite cpr_eqE.
rewrite !coqRE.

(*Memo: pattern search. *)
(*

    set rhs:= (w in w%%p).  (* To know the type (X j + Z j + (p - X j))*)
    have: rhs = (Z j + p)%nat.
*)
(*


  Search cpr_inE. (* Memo: the search target itself won't show but "related" things *)

*)
Search `Pr[_ = _] `Pr[_ \in _].
Search ([set _] `* [set _]).

Abort.





End lemma_3_5.
