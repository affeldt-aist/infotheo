(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect.

(**md**************************************************************************)
(* # Maximum Subset Satisfying some Property                                  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Maxsubset.
Section maxsubset.
Variable A : finType.

Definition maxset P (E : {set A}) := (P E) &&
  [forall F : {set A}, (P F && (E \subset F)) == (E == F)].

Lemma maxset_eq P1 P2 E : P1 =1 P2 -> maxset P1 E = maxset P2 E.
Proof.
move=> P1P2.
rewrite /maxset.
rewrite P1P2.
congr (_ && _).
apply/forallP/forallP => /= H x.
by rewrite -P1P2 H.
by rewrite P1P2 H.
Qed.

Lemma maxsetP (P : {set A} -> bool) E :
  reflect ((P E) /\ (forall F, P F -> E \subset F -> E = F)) (maxset P E).
Proof.
case H : (maxset P E); [apply ReflectT | apply ReflectF].
  case/andP : H => -> /forallP H.
  split => // F H1 H2.
  move: (H F).
  by rewrite H1 H2 /= eq_sym eqb_id => /eqP.
case => H1 H2.
move/negP : H; apply.
rewrite /maxset H1 /=.
apply/forallP => F.
case H : (_ && _).
  case/andP : H.
  move/H2 => H3; move/H3 => ->.
  by rewrite eqxx.
rewrite eq_sym.
rewrite eqbF_neg.
apply/eqP => ?; subst F.
rewrite H1 /= in H.
move/negP : H; by apply.
Qed.

Lemma maxsetp E P : maxset P E -> P E.
Proof. by case/maxsetP. Qed.

Lemma maxsetinf P E F : maxset P E -> P F -> E \subset F -> E = F.
Proof.
case/maxsetP => H1 H2 PF.
by apply H2.
Qed.

Lemma ex_maxset (P : pred {set A}): (exists E, P E) -> {E | maxset P E}.
Proof.
move=> exQ.
pose pS n := [pred F | P F & #|F| == n].
pose p n := ~~ pred0b (pS n).
have {exQ} : exists n, p n.
  case: exQ => E QE.
  exists #| E  |.
  rewrite /p.
  apply/existsP.
  exists E.
  by rewrite eqxx andbT.
case/(@ex_maxnP _ #|A|).
  move=> o pi.
  case/existsP : pi => B /andP [] QB /eqP <-.
  by apply max_card.
move=> i.
move/pred0P.
case: (pickP (pS i)) => // F.
move=> pSF H Hi.
exists F.
apply/(@maxsetP P).
split.
  rewrite /pS inE in pSF.
  by case/andP : pSF.
move=> G QG FG.
apply/eqP.
rewrite eqEcard FG /=.
move: (Hi #|G|).
rewrite /pS inE in pSF.
case/andP : pSF => H1 H2.
rewrite (eqP H2).
apply.
apply/existsP.
exists G.
by rewrite QG eqxx.
Qed.

Lemma maxset_exists (P : pred {set A}) C : P C -> {F | maxset P F & C \subset F}.
Proof.
move=> PC.
have{PC}: exists A, P A && (C \subset A).
  by exists C; rewrite PC /=.
case/ex_maxset => B.
move/maxsetP => [].
case/andP => BP CB maxB.
exists B => //.
apply/maxsetP.
split=> // D PD BD.
rewrite (maxB D) // PD.
by rewrite (subset_trans CB).
Qed.
End maxsubset.
End Maxsubset.

Section max_subset_satisfying_P.
Variable A : finType.
Variable P : pred {set A}.

Definition Psets (E : {set A}) : {set {set A}} :=
  [set s : {set A} | s \subset E & P s].

Definition maxset E := \bigcup_(s in Psets E) s.

Lemma maxset_is_subset E : maxset E \subset E.
Proof. apply/bigcupsP => /= s; rewrite inE; by case/andP. Qed.

Definition covered_by (E K : {set A}):=
  [forall s, (s \in Psets E) ==> (s \subset K)].

Lemma covered_by_maxset E : covered_by E (maxset E).
Proof.
apply/forallP => s.
apply/implyP => Hs.
rewrite /maxset.
exact: subset_trans (bigcup_sup _ Hs).
Qed.

Hypothesis P0 : P set0.

Lemma card_Psets (E : {set A}) : #| Psets E | != 0.
Proof.
rewrite cards_eq0.
apply/set0Pn => /=.
exists set0; by rewrite inE P0 andbT sub0set.
Qed.

Hypothesis PU : forall s1 s2, P s1 -> P s2 -> P (s1 :|: s2).

Lemma PsetsU s1 s2 E : s1 \in Psets E -> s2 \in Psets E ->
  s1 :|: s2 \in Psets E.
Proof.
rewrite /Psets.
rewrite inE; case/andP => s1E Ps1.
rewrite inE; case/andP => s2E Ps2.
rewrite inE.
apply/andP; split.
  by apply/subUsetP.
by rewrite PU.
Qed.

Lemma maxset_in_Psets E : maxset E \in Psets E.
Proof.
rewrite /Psets inE maxset_is_subset /= /maxset.
suff Hgen : forall F : {set {set A}} , (forall s', s' \in F -> P s') -> P (\bigcup_(s in F) s).
  apply Hgen => s'.
  rewrite inE.
  by case/andP.
move=> F /= HF.
move Hk : (#| F |) => k.
elim: k => [ | k IH ] in F Hk HF *.
  rewrite big_pred0.
    by rewrite P0.
  move=> s /=.
  apply/negbTE.
  move/eqP : Hk.
  rewrite cards_eq0 => /negPn.
  apply: contra => sF.
  apply/set0Pn; by exists s.
have : #|F| != O by rewrite Hk.
rewrite cards_eq0.
case/set0Pn => f0 Hf0.
rewrite -(@setD1K _ f0 F) // bigcup_setU PU //.
  rewrite (big_pred1 f0).
    by apply HF.
  move=> /= s; by rewrite inE.
apply IH.
  rewrite (cardsD1 f0) in Hk.
  rewrite Hf0 in Hk.
  rewrite add1n in Hk.
  by case: Hk.
move=> s' Hs'.
apply HF.
rewrite inE in Hs'.
by case/andP : Hs'.
Qed.

Lemma maxset_is_Ppred E : P (maxset E).
Proof.
have : maxset E \in Psets E by apply maxset_in_Psets.
rewrite inE.
by case/andP.
Qed.

Definition is_unique E (P : {set A} -> Prop)  : Prop :=
  forall E', P E' -> E' = E.

Lemma maxset_is_unique E : is_unique (maxset E)
  (fun E' => E' \subset E /\ covered_by E E' /\ P E').
Proof.
rewrite /is_unique => E'.
case=> EsubE'.
case=> EE' HE'.
apply/setP => /= n0.
case/boolP : (n0 \in maxset E) => Hn0.
  move/forallP : EE'.
  move=> /(_ (maxset E)).
  move /implyP.
  move/(_ (maxset_in_Psets E)).
  move /subsetP.
  by apply.
apply: contraTF Hn0.
rewrite negbK => n0E'.
apply/bigcupP => /=.
exists E' => //.
by rewrite inE HE' andbT.
Qed.

End max_subset_satisfying_P.
