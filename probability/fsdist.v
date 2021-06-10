(* infotheo: information theory and error-correcting codes in Coq               *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import finmap.
From mathcomp Require boolp.
Require Import Reals.
From mathcomp Require Import Rstruct.
Require Import ssrR Reals_ext ssr_ext ssralg_ext bigop_ext Rbigop fdist.
Require Import convex.

(******************************************************************************)
(*                    Finitely-supported distributions                        *)
(*                                                                            *)
(* This file provides a formalization of finitely-supported probability       *)
(* distributions. It generalizes the finite discrete probability              *)
(* distributions over a finType from fdist.v and makes it possible to         *)
(* talk about distributions of distributions to turn distributions into       *)
(* a genuine monad.                                                           *)
(*                                                                            *)
(*          {dist A} == the type of finitely-supported distributions over A   *)
(*                      where A is a choiceType (see proba.v for              *)
(*                      distributions over a finType)                         *)
(*    Module FSDist1 == unit of the probability monad                         *)
(* Module FSDistBind == bind of the probability monad                         *)
(*        FSDistfmap == map of the probability monad                          *)
(* FSDist_choiceType == instance of choiceType with finitely-supported        *)
(*                      distributions                                         *)
(*                                                                            *)
(* Free convex spaces in terms of finitely-supported distributions:           *)
(*  FSDist_convType   == shows that finitely-supported distributions over a   *)
(*                       choiceType form a convex space                       *)
(*  Convn_of_FSDist d == <$>_(fdist_of_Dist d) (fun x : finsupp d => fsval x),*)
(*                       a variant of Convn whose input data (points and      *)
(*                       weights) are provided by a single FSDist; this is    *)
(*                       the counit of the adjunction that produces the       *)
(*                       probability monad (see monae, gcm_model.v)           *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "{ 'dist' T }" (at level 0, format "{ 'dist'  T }").

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.
Local Open Scope fset_scope.

(* TODO: move? *)
Section finmap_ext.
Lemma bigfcup_fset1 (T I : choiceType) (P : {fset I}) (f : I -> T) :
  \bigcup_(x <- P) [fset f x] = f @` P.
Proof.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP=> x.
- case/bigfcupP=> i /andP [] iP _.
  rewrite inE => /eqP ->.
  by apply/imfsetP; exists i.
- case/imfsetP => i /= iP ->; apply/bigfcupP; exists i; rewrite ?andbT //.
  by apply/imfsetP; exists (f i); rewrite ?inE.
Qed.
Section fbig_pred1_inj.
Variables (R : Type) (idx : R) (op : Monoid.com_law idx).
Lemma fbig_pred1_inj (A C : choiceType) h (k : A -> C) (d : {fset _}) a :
  a \in d -> injective k -> \big[op/idx]_(a0 <- d | k a0 == k a) h a0 = h a.
Proof.
move=> ad inj_k.
rewrite big_fset_condE -(big_seq_fset1 op); apply eq_fbig => // a0.
rewrite !inE /=; apply/idP/idP => [|/eqP ->]; last by rewrite eqxx andbT.
by case/andP => _ /eqP/inj_k ->.
Qed.
End fbig_pred1_inj.
Arguments fbig_pred1_inj [R] [idx] [op] [A] [C] [h] [k].
End finmap_ext.

Module FSDist.
Section fsdist.
Variable A : choiceType.
Record t := mk {
  f :> {fsfun A -> R with 0} ;
  _ : all (fun x => 0 <b f x) (finsupp f) &&
        \sum_(a <- finsupp f) f a == 1}.
Lemma ge0 (d : t) a : 0 <= d a.
Proof.
case: d => /= f /andP[/allP H _].
case/boolP : (a \in finsupp f) => [/H/ltRP/ltRW //|].
rewrite memNfinsupp => /eqP ->; exact/leRR.
Qed.
Lemma gt0 (d : t) a : a \in finsupp d -> 0 < d a.
Proof.
rewrite mem_finsupp => Pa; apply/ltRP; rewrite lt0R Pa; exact/leRP/ge0.
Qed.
Lemma f1 (d : t) : \sum_(a <- finsupp d) d a = 1.
Proof. by case: d => d /= /andP[_ /eqP]. Qed.
Lemma le1 (d : t) a : d a <= 1.
Proof.
have [ad|?] := boolP (a \in finsupp d); last by rewrite fsfun_dflt.
rewrite -(f1 d) (big_fsetD1 _ ad) /= addRC -leR_subl_addr subRR.
by apply sumR_ge0 => ? _; exact: ge0.
Qed.
Obligation Tactic := idtac.
Program Definition make (f : {fsfun A -> R with 0})
  (H0 : forall a, a \in finsupp f -> 0 < f a)
  (H1 : \sum_(a <- finsupp f) f a = 1) : t := @mk f _.
Next Obligation.
by move=> f H0 ->; rewrite eqxx andbT; apply/allP => a /H0/ltRP.
Qed.
End fsdist.
End FSDist.
Coercion FSDist.f : FSDist.t >-> fsfun.

Global Hint Resolve FSDist.ge0 : core.

Section FSDist_canonical.
Variable A : choiceType.
Canonical FSDist_subType := Eval hnf in [subType for @FSDist.f A].
Definition FSDist_eqMixin := [eqMixin of @FSDist.t A by <:].
Canonical FSDist_eqType := Eval hnf in EqType _ FSDist_eqMixin.
Definition FSDist_choiceMixin := [choiceMixin of @FSDist.t A by <:].
Canonical FSDist_choiceType := Eval hnf in ChoiceType _ FSDist_choiceMixin.
End FSDist_canonical.

Definition FSDist_to_Type (A : choiceType) :=
  fun phT : phant (Choice.sort A) => FSDist.t A.
Local Notation "{ 'dist' T }" := (FSDist_to_Type (Phant T)).

Section FSDist_prop.
Variable A : choiceType.

Lemma FSDist_ext (d d' : {dist A}) : (forall x, d x = d' x) -> d = d'.
Proof. by move=> ?; exact/val_inj/fsfunP. Qed.

Lemma FSDist_supp_neq0 (d : {dist A}) : finsupp d != fset0.
Proof.
apply/eqP => H.
move: (FSDist.f1 d); rewrite H big_nil => /esym; exact: R1_neq_R0.
Qed.

End FSDist_prop.

Module FSDist1.
Section def.
Variables (A : choiceType) (a : A).
Let D := [fset a].
Definition f : {fsfun A -> R with 0} := [fsfun b in D => 1 | 0].
Lemma suppf : finsupp f = D.
Proof.
apply/fsetP => b; rewrite mem_finsupp /f fsfunE inE.
by case: ifPn => ba; [exact/gtR_eqF | by rewrite eqxx].
Qed.
Lemma f0 b : b \in finsupp f -> 0 < f b.
Proof. rewrite mem_finsupp fsfunE inE; case: ifPn => //; by rewrite eqxx. Qed.
Lemma f1 : \sum_(b <- finsupp f) f b = 1.
Proof. by rewrite suppf big_seq_fset1 /f fsfunE inE eqxx. Qed.
Definition d : {dist A} := locked (FSDist.make f0 f1).
Lemma dE a0 : d a0 = if a0 \in D then 1 else 0.
Proof. by rewrite /d; unlock; rewrite fsfunE. Qed.
Lemma supp : finsupp d = D.
Proof. by rewrite -suppf; apply/fsetP => b; rewrite !mem_finsupp dE fsfunE. Qed.
End def.
End FSDist1.

Lemma FSDist1_inj (C : choiceType) : injective (@FSDist1.d C).
Proof.
move=> a b /eqP ab; apply/eqP; apply: contraTT ab => ab.
apply/eqP => /(congr1 (fun x : FSDist.t _ => x a)).
rewrite !FSDist1.dE !inE eqxx (negbTE ab); exact: R1_neq_R0.
Qed.

Module FSDistBind.
Section def.
Variables (A B : choiceType) (p : {dist A}) (g : A -> {dist B}).
Let D := \bigcup_(d <- g @` [fset a | a in finsupp p]) finsupp d.
Definition f : {fsfun B -> R with 0} :=
  [fsfun b in D => \sum_(a <- finsupp p) p a * (g a) b | 0].
Lemma f0 b : b \in finsupp f -> 0 < f b.
Proof.
rewrite mem_finsupp fsfunE; case: ifPn => [_ /eqP/nesym ?|]; last by rewrite eqxx.
by rewrite ltR_neqAle; split => //; apply sumR_ge0 => a _; exact/mulR_ge0.
Qed.
Lemma f1 : \sum_(b <- finsupp f) f b = 1.
Proof.
rewrite {2}/f.
evar (h : B -> R); rewrite (eq_bigr h); last first.
  move=> b _; rewrite fsfunE /h; reflexivity.
rewrite {}/h -big_mkcond /= exchange_big /=.
rewrite -[RHS](FSDist.f1 p); apply eq_bigr => a _.
case/boolP : (p a == R0 :> R) => [/eqP -> | pa0].
  rewrite big1 // => *; by rewrite mul0R.
rewrite -big_distrr /=.
rewrite (_ : \sum_(_ <- _ | _) _ = 1) ?mulR1 //.
rewrite (bigID (fun x => x \in finsupp (g a))) /=.
rewrite [X in (_ + X)%R = _]big1 ?addR0; last first.
  by move=> b /andP[_]; rewrite memNfinsupp => /eqP.
rewrite (eq_bigl (fun i => i \in finsupp (g a))); last first.
  move=> b; rewrite andb_idl // mem_finsupp => gab0.
  apply/bigfcupP; exists (g a); rewrite ?mem_finsupp // andbT.
  apply/imfsetP; exists a => //; by rewrite inE mem_finsupp.
rewrite -big_filter -[RHS](FSDist.f1 (g a)); apply perm_big.
apply uniq_perm; [by rewrite filter_uniq | by rewrite fset_uniq |move=> b].
rewrite mem_finsupp.
apply/idP/idP => [|gab0]; first by rewrite mem_filter mem_finsupp => /andP[].
rewrite mem_filter 2!mem_finsupp gab0 /= /f fsfunE ifT; last first.
  apply/bigfcupP; exists (g a); rewrite ?mem_finsupp // andbT.
  by apply/imfsetP; exists a => //; rewrite inE mem_finsupp.
apply: contra gab0 => /eqP/psumR_seq_eq0P.
rewrite fset_uniq => /(_ isT) H.
suff : p a * g a b = 0.
 by rewrite mulR_eq0 => -[/eqP|->//]; rewrite (negbTE pa0).
apply/H; rewrite ?mem_finsupp // => a0 _; exact/mulR_ge0.
Qed.
Definition d : {dist B} := locked (FSDist.make f0 f1).
Lemma dE x : d x = if x \in D then \sum_(a <- finsupp p) p a * (g a) x else 0.
Proof. by rewrite /d; unlock; rewrite fsfunE. Qed.
Lemma supp : finsupp d = D.
Proof.
apply/fsetP => b; rewrite mem_finsupp; apply/idP/idP => [|].
  rewrite dE; case: ifPn => //; by rewrite eqxx.
case/bigfcupP => dB.
rewrite andbT => /imfsetP[a] /=.
rewrite imfset_id => ap ->{dB} bga.
rewrite dE; case: ifPn => [/bigfcupP[dB] | ]; last first.
  apply: contra => _.
  apply/bigfcupP; exists (g a)=> //; rewrite andbT.
  by apply/imfsetP; exists a => //=; rewrite imfset_id.
rewrite andbT => /imfsetP[a0] /=.
rewrite imfset_id => a0p ->{dB} bga0.
apply/eqP => H.
have : (p a0) * (g a0) b <> 0.
  by rewrite mulR_eq0 => -[]; apply/eqP; rewrite -mem_finsupp.
apply.
move/psumR_seq_eq0P : H; apply => // b0 _; exact/mulR_ge0.
Qed.
End def.
End FSDistBind.

Lemma FSDistBind1f (A B : choiceType) (a : A) (f : A -> {dist B}) :
  FSDistBind.d (FSDist1.d a) f = f a.
Proof.
apply/val_inj/val_inj => /=; congr fmap_of_fsfun; apply/fsfunP => b.
rewrite FSDistBind.dE; case: ifPn => [|H].
  case/bigfcupP => /= d; rewrite andbT.
  case/imfsetP => a0 /= /imfsetP[a1 /=].
  rewrite FSDist1.supp inE => /eqP ->{a1} ->{a0} ->{d} bfa.
  by rewrite big_seq_fsetE big_fset1 FSDist1.dE /= inE eqxx mul1R.
case/boolP : ((f a) b == R0 :> R) => [/eqP ->//|fab0].
case/bigfcupP : H.
exists (f a); last by rewrite mem_finsupp.
rewrite andbT; apply/imfsetP; exists a => //=.
by rewrite imfset_id FSDist1.supp inE.
Qed.

Lemma FSDistBindp1 (A : choiceType) (p : {dist A}) : FSDistBind.d p (@FSDist1.d A) = p.
Proof.
apply/val_inj/val_inj => /=; congr fmap_of_fsfun; apply/fsfunP => b.
rewrite FSDistBind.dE; case: ifPn => [|H].
  case/bigfcupP => /= d; rewrite andbT.
  case/imfsetP => /= a /imfsetP[a0] /= pa00 ->{a} ->{d}.
  rewrite FSDist1.supp inE => /eqP ->{b}.
  rewrite (big_fsetD1 a0) //= FSDist1.dE inE eqxx mulR1 big1_fset ?addR0 // => a.
  rewrite !inE => /andP[aa0] ap _.
  by rewrite FSDist1.dE inE eq_sym (negbTE aa0) mulR0.
case/boolP : (p b == R0 :> R) => [/eqP ->//|pb0].
case/bigfcupP : H.
exists (FSDist1.d b); last by rewrite FSDist1.supp inE.
by rewrite andbT; apply/imfsetP; exists b => //=; rewrite imfset_id mem_finsupp.
Qed.

Lemma FSDistBindA (A B C : choiceType) (m : {dist A}) (f : A -> {dist B}) (g : B -> {dist C}) :
  FSDistBind.d (FSDistBind.d m f) g = FSDistBind.d m (fun x => FSDistBind.d (f x) g).
Proof.
apply/val_inj/val_inj => /=; congr fmap_of_fsfun; apply/fsfunP => c.
rewrite !FSDistBind.dE; case: ifPn => [|H]; last first.
  rewrite ifF //; apply/negbTE; apply: contra H.
  case/bigfcupP => /= dC; rewrite andbT.
  move=> /imfsetP[x] /=; rewrite imfset_id => mx ->{dC}.
  rewrite FSDistBind.supp.
  case/bigfcupP => dC; rewrite andbT => /imfsetP[b] /=.
  rewrite imfset_id => bfx ->{dC} cgb.
  apply/bigfcupP; exists (g b) => //; rewrite andbT.
  apply/imfsetP; exists b => //=.
  rewrite imfset_id FSDistBind.supp.
  apply/bigfcupP; exists (f x) => //; rewrite andbT.
  by apply/imfsetP; exists x => //=; rewrite imfset_id.
case/bigfcupP => /= dC.
rewrite andbT => /imfsetP[b] /=.
rewrite imfset_id {1}FSDistBind.supp => /bigfcupP[dB].
rewrite andbT => /imfsetP[a] /=.
rewrite imfset_id => ma ->{dB} fab0 ->{dC} gbc0.
rewrite ifT; last first.
  apply/bigfcupP => /=; exists (FSDistBind.d (f a) g); last first.
    rewrite FSDistBind.supp; apply/bigfcupP; exists (g b) => //.
    by rewrite andbT; apply/imfsetP; exists b => //=; rewrite imfset_id.
  by rewrite andbT; apply/imfsetP => /=; exists a.
rewrite (eq_bigr (fun a => \sum_(a0 <- finsupp m) m a0 * (f a0) a * (g a) c)); last first.
  move=> b0 _.
  rewrite FSDistBind.dE; case: ifPn => [/bigfcupP[dB] | ].
    by rewrite andbT => /imfsetP[a0] _ _ _; rewrite -big_distrl.
  rewrite (mul0R (g b0 c)) => K.
  rewrite big1_fset => // a0 ma00 _.
  apply/eqP/negPn/negP => L.
  move/negP : K; apply.
  apply/bigfcupP; exists (f a0); last first.
    by rewrite mem_finsupp; apply: contra L => /eqP ->; rewrite mulR0 mul0R.
  by rewrite andbT; apply/imfsetP; exists a0 => //=; rewrite imfset_id.
rewrite exchange_big; apply eq_bigr => a0 _ /=.
rewrite FSDistBind.dE.
case/boolP : (m a0 == R0 :> R) => [/eqP ->|ma00].
  by rewrite mul0R big1_fset // => b2 _ _; rewrite 2!mul0R.
case: ifPn => [/bigfcupP[dC] | Hc].
  rewrite andbT => /imfsetP[b0] /=.
  rewrite imfset_id => fa0b0 ->{dC} gb0c.
  evar (h : B -> R); rewrite (eq_bigr h); last first.
    move=> ? _; rewrite -mulRA /h; reflexivity.
  rewrite {}/h -(big_distrr  (m a0)) /=; congr (_ * _).
  rewrite (big_fsetID _ (fun x => x \in finsupp (f a0))) /=.
  rewrite [X in (_ + X)%R = _](_ : _ = 0) ?addR0; last first.
    rewrite big1_fset => // b1 /imfsetP [b2 /=]; rewrite inE => /andP[/= _].
    by rewrite !mem_finsupp negbK => /eqP K -> _; rewrite K mul0R.
  apply big_fset_incl.
    by apply/fsubsetP => b1; case/imfsetP => b2 /= /andP[_ ?] ->.
  move=> b1 fa0b1.
  case/boolP : (g b1 c == R0 :> R) => [/eqP -> _|gb1c]; first by rewrite mulR0.
  case/imfsetP; exists b1 => //=.
  rewrite inE fa0b1 andbT mem_finsupp FSDistBind.dE ifT.
    have /eqP K : (m a0 * (f a0 b1) <> R0 :> R).
      rewrite mulR_eq0 => -[].
      exact/eqP.
      by apply/eqP; rewrite -mem_finsupp.
    apply/eqP => /psumR_seq_eq0P => L.
    move/eqP : K; apply.
    apply L => //.
    - move=> a1 _; exact: mulR_ge0.
    - by rewrite mem_finsupp.
  apply/bigfcupP; exists (f a0) => //; rewrite andbT.
  by apply/imfsetP; exists a0 => //=; rewrite imfset_id mem_finsupp.
rewrite FSDistBind.supp.
suff : \sum_(i <- finsupp (FSDistBind.d m f)) (f a0) i * (g i) c = R0 :> R.
  rewrite FSDistBind.supp => L.
  evar (h : B -> R); rewrite (eq_bigr h); last first.
    move=> ? _; rewrite -mulRA /h; reflexivity.
  by rewrite -(big_distrr (m a0)) /= L !mulR0.
apply/psumR_seq_eq0P.
- exact: fset_uniq.
- move=> b1 _; exact: mulR_ge0.
- move=> a1 Ha1.
  case/boolP : (g a1 c == R0 :> R) => [/eqP -> | ga1c]; first by rewrite mulR0.
  case/boolP : (f a0 a1 == R0 :> R) => [/eqP -> | fa0a1]; first by rewrite mul0R.
  case/bigfcupP : Hc.
  exists (g a1); last by rewrite mem_finsupp.
  rewrite andbT.
  apply/imfsetP; exists a1 => //=.
  by rewrite imfset_id mem_finsupp.
Qed.

Definition FSDistfmap (A B : choiceType) (f : A -> B) (d : {dist A}) : {dist B} :=
  FSDistBind.d d (fun a => FSDist1.d (f a)).

Lemma FSDistfmap_id (A : choiceType) : FSDistfmap (@id A) = @id {dist A}.
Proof. by rewrite boolp.funeqE => a; rewrite /FSDistfmap FSDistBindp1. Qed.

Lemma FSDistfmap_comp (A B C : choiceType) (g : B -> C) (h : A -> B) :
  FSDistfmap (g \o h) = FSDistfmap g \o FSDistfmap h.
Proof.
rewrite boolp.funeqE => d; rewrite /FSDistfmap /= FSDistBindA; congr FSDistBind.d.
by rewrite boolp.funeqE => a; rewrite FSDistBind1f.
Qed.

Definition FSDistfmapE (A B : choiceType) (f : A -> B) (d : {dist A}) b :
  FSDistfmap f d b = \sum_(a <- finsupp d | f a == b) d a.
Proof.
rewrite {1}/FSDistfmap [in LHS]FSDistBind.dE; case: ifPn => Hb.
  rewrite (bigID (fun a => f a == b)) /=.
  rewrite [X in (_ + X)%R = _](_ : _ = 0) ?addR0; last first.
    by rewrite big1 // => a /negbTE fab; rewrite FSDist1.dE inE eq_sym fab mulR0.
  by apply eq_bigr => a fab; rewrite FSDist1.dE inE eq_sym fab mulR1.
rewrite big_seq_cond big1 // => a /andP[ad] fab.
exfalso; move/negP : Hb; apply.
apply/bigfcupP; rewrite imfset_id; exists (FSDist1.d (f a)).
  by rewrite andbT; apply/imfsetP => /=; exists a.
by rewrite FSDist1.supp inE eq_sym.
Qed.

Lemma supp_FSDistfmap (A B : choiceType) (f : A -> B) d :
  finsupp (FSDistfmap f d) = [fset f x | x in finsupp d].
Proof.
rewrite /FSDistfmap FSDistBind.supp; apply/fsetP => d'.
apply/bigfcupP/imfsetP => [[D]|].
  rewrite andbT => /imfsetP[a /=]; rewrite imfset_id => ad ->{D}.
  by rewrite FSDist1.supp inE => /eqP ->{d'}; exists a.
case=> a /= ad -> {d'}; exists (FSDist1.d (f a)).
  rewrite andbT; apply/imfsetP; exists a => //=; by rewrite imfset_id.
by rewrite FSDist1.supp inE.
Qed.

Lemma FSDistfmap1 (A B : choiceType) (f : A -> B) x :
  FSDistfmap f (FSDist1.d x) = FSDist1.d (f x).
Proof. by rewrite /FSDistfmap FSDistBind1f. Qed.

Lemma FSDistfmap_FSDist1 (C : choiceType) (d : {dist C}) (i : C) :
  FSDistfmap (FSDist1.d (A:=C)) d (FSDist1.d i) = d i.
Proof.
rewrite FSDistfmapE.
case/boolP: (i \in finsupp d)=> ifd; first by rewrite fbig_pred1_inj //; apply:FSDist1_inj.
transitivity(\sum_(a <- finsupp d | a == i) d a);
  first by apply eq_bigl=> j; apply/eqtype.inj_eq/FSDist1_inj.
rewrite big_seq_cond big_pred0;
  last by move=> j; apply/andP; case=> jfd /eqP ji; move: jfd; rewrite ji (negbTE ifd).
by rewrite fsfun_dflt.
Qed.

Local Open Scope reals_ext_scope.
Lemma FSDist_finsuppD1 (C : choiceType) (d : {dist C}) (x : C) :
  \sum_(i <- finsupp d `\ x) d i = (d x).~.
Proof.
rewrite -subR_eq0 subR_onem.
case/boolP: (x \in finsupp d)=> xfd;
  first by rewrite addRC -big_fsetD1 //= FSDist.f1 subRR.
by rewrite fsfun_dflt // mem_fsetD1 // FSDist.f1 addR0 subRR.
Qed.
Local Close Scope reals_ext_scope.

Definition FSDist_prob (C : choiceType) (d : {dist C}) (x : C) : prob :=
  Eval hnf in Prob.mk_ (conj (FSDist.ge0 d x) (FSDist.le1 d x)).
Canonical FSDist_prob.

Definition FSDistjoin A (D : {dist (FSDist_choiceType A)}) : {dist A} :=
  FSDistBind.d D ssrfun.id.

Lemma FSDistjoinE A (D : {dist (FSDist_choiceType A)}) x :
  FSDistjoin D x = \sum_(d <- finsupp D) D d * d x.
Proof.
rewrite /FSDistjoin FSDistBind.dE 2!imfset_id; case: ifPn => // xD.
rewrite big_seq (eq_bigr (fun=> 0)) ?big1 // => d dD.
case/boolP : (d x == 0) => [/eqP -> |dx0]; first by rewrite mulR0.
exfalso; move/negP : xD; apply.
apply/bigfcupP; exists d; by [rewrite dD | rewrite mem_finsupp].
Qed.

Lemma FSDistjoin1 (A : choiceType) (D : {dist (FSDist_choiceType A)}) :
  FSDistjoin (FSDist1.d D) = D.
Proof.
apply/FSDist_ext => d.
by rewrite FSDistjoinE FSDist1.supp big_imfset // big_seq1 FSDist1.dE inE eqxx mul1R.
Qed.

Module FSDist_crop0.
Section def.
Variables (A : choiceType) (P : {dist A}).
Definition D := [fset a : finsupp P | true].
Definition f' : {ffun finsupp P -> R} := [ffun a => P (fsval a)].
Definition f : {fsfun finsupp P -> R with 0} := [fsfun x in D  => f' x | 0].
Lemma f0 a : a \in finsupp f -> 0 < f a.
Proof.
by move=> _; rewrite /f fsfunE /D inE /= /f' ffunE; apply FSDist.gt0.
Qed.
Lemma f1 : \sum_(a <- finsupp f) f a = 1.
Proof.
rewrite -(FSDist.f1 P) !big_seq_fsetE /=.
have hP (a : [finType of finsupp P]) : a \in finsupp f.
  by rewrite mem_finsupp fsfunE ffunE inE -mem_finsupp fsvalP.
pose h a := FSetSub (hP a).
rewrite (reindex h) /=.
  by apply eq_bigr => i _; rewrite fsfunE ffunE inE.
by exists (@fsval _ _) => //= -[a] *; exact: val_inj.
Qed.
Definition d : {dist [finType of finsupp P]} := FSDist.make f0 f1.
End def.
End FSDist_crop0.

Module FSDist_lift_supp.
Section def.
Variables (A B : choiceType) (r : A -> B) (P : {dist B})
          (s : B -> A) (H : cancel s r).
Definition D := [fset s b | b in finsupp P].
Lemma s_inj : injective s.
Proof. exact (can_inj H). Qed.
Lemma r_surj : forall b : B, exists a : A, b = r a.
Proof. by move=> b; exists (s b); rewrite H. Qed.
Let f := [fsfun a in D => P (r a) | 0].
Lemma f0 a : a \in finsupp f -> 0 < f a.
Proof.
rewrite mem_finsupp /f fsfunE; case: ifPn => Ha; last by rewrite eqxx.
rewrite -mem_finsupp; exact/FSDist.gt0.
Qed.
Lemma DsuppE : D = finsupp f.
Proof.
apply fsetP => a.
rewrite /f /D !mem_finsupp !fsfunE; case: ifPn; last by rewrite eqxx.
by case/imfsetP => b /= Hb ->; rewrite H // -mem_finsupp.
Qed.
Lemma f1 : \sum_(a <- finsupp f) f a = 1.
Proof.
rewrite -DsuppE /D big_imfset /=; last by move=> i j _ _; exact: s_inj.
rewrite (eq_bigr P) ?FSDist.f1 // => i _; rewrite /f fsfunE /D H.
apply/eqP; case: ifPn => //; apply: contraNT => Pi0.
by apply/imfsetP => /=; exists i => //; rewrite mem_finsupp eq_sym.
Qed.
Definition d : {dist A} := locked (FSDist.make f0 f1).
Lemma dE a : d a = if a \in [fset s b | b in finsupp P] then P (r a) else 0.
Proof. by rewrite /d; unlock => /=; rewrite fsfunE. Qed.
End def.
End FSDist_lift_supp.

Module FSDist_of_fdist.
Section def.
Variable (A : finType) (P : fdist A).
Let D := [fset a0 : A | P a0 != 0].
Definition f : {fsfun A -> R with 0} := [fsfun a in D => P a | 0].
Let f0 a : a \in finsupp f -> 0 < f a.
Proof.
rewrite fsfunE mem_finsupp /f fsfunE.
case: ifPn => [_|]; by [rewrite fdist_gt0 | rewrite eqxx].
Qed.
Let f1 : \sum_(a <- finsupp f) f a = 1.
Proof.
rewrite -[RHS](FDist.f1 P) [in RHS](bigID (fun x => x \in finsupp f)) /=.
rewrite [in X in _ = (_ + X)%R]big1 ?addR0; last first.
  move=> a; rewrite memNfinsupp fsfunE !inE /=.
  by case: ifPn => [_ /eqP //|]; rewrite negbK => /eqP.
rewrite (@eq_fbigr _ _ _ _ _ _ _ (fun i => P i)) /=; last first.
  move=> a; rewrite mem_finsupp fsfunE !inE /=; case: ifPn => //; by rewrite eqxx.
exact/big_uniq/fset_uniq.
Qed.
Definition d : {dist A} := FSDist.make f0 f1.
End def.
End FSDist_of_fdist.

Module fdist_of_FSDist.
Section def.
Variable (A : choiceType) (P : {dist A}).
Definition D := [finType of finsupp P] : finType.
Definition f := [ffun d : D => P (fsval d)].
Lemma f0 b : 0 <= f b. Proof. by rewrite ffunE. Qed.
Lemma f1 : \sum_(b in D) f b = 1.
Proof.
rewrite -(FSDist.f1 P) big_seq_fsetE /=; apply eq_bigr => a; by rewrite ffunE.
Qed.
Definition d : fdist D := locked (FDist.make f0 f1).
End def.
Module Exports.
Notation fdist_of_Dist := d.
End Exports.
End fdist_of_FSDist.
Export fdist_of_FSDist.Exports.

Section fdist_of_FSDist_lemmas.
Variable (A : choiceType) (d : {dist A}).
Lemma fdist_of_FSDistE i : fdist_of_Dist d i = d (fsval i).
Proof. by rewrite /fdist_of_Dist; unlock; rewrite ffunE; reflexivity. Qed.
Lemma fdist_of_FSDistDE : fdist_of_FSDist.D d = [finType of finsupp d].
Proof. reflexivity. Qed.
End fdist_of_FSDist_lemmas.

Module fdist_of_finFSDist.
Section def.
Variable (A : finType) (P : {dist A}).
Definition f := [ffun d : A => P d].
Lemma f0 b : 0 <= f b. Proof. by rewrite ffunE. Qed.
Lemma f1 : \sum_(b in A) f b = 1.
Proof.
rewrite -(FSDist.f1 P) (bigID (fun x => x \in finsupp P)) /=.
rewrite [X in (_ + X = _)%R](_ : _ = 0) ?addR0.
  by rewrite big_uniq /= ?fset_uniq //; apply eq_bigr => i _; rewrite ffunE.
by rewrite big1 // => a; rewrite mem_finsupp negbK ffunE => /eqP.
Qed.
Definition d : fdist A := locked (FDist.make f0 f1).
Lemma dE a : d a = P a.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
End def.
Module Exports.
Notation fdist_of_finFSDist := d.
End Exports.
End fdist_of_finFSDist.
Export fdist_of_finFSDist.Exports.

Module ConvnFSDist.
Local Open Scope proba_scope.
Section def.
Variables (A : choiceType) (n : nat) (e : {fdist 'I_n}) (g : 'I_n -> {dist A}).
Definition D : {fset A} := \big[fsetU/fset0]_(i < n | 0 <b e i) finsupp (g i).
Definition f := [fsfun a in D => \sum_(i < n) e i * g i a | 0].
Lemma supp : finsupp f = D.
Proof.
apply/fsetP => a; apply/idP/idP => [|].
  rewrite mem_finsupp /f fsfunE.
  case: ifPn => //; by rewrite eqxx.
rewrite mem_finsupp fsfunE => aD.
rewrite aD.
case/bigfcupP : aD => /= i.
rewrite mem_index_enum /= => /ltRP ei0.
rewrite mem_finsupp => gia0.
apply: contra gia0 => /eqP H; apply/eqP.
rewrite -(@eqR_mul2l (e i)) ?mulR0; last exact/eqP/gtR_eqF.
move/psumR_eq0P : H; apply => //= j _; exact/mulR_ge0.
Qed.
Lemma f0 a : a \in finsupp f -> 0 < f a.
Proof.
rewrite mem_finsupp fsfunE; case: ifPn => [_ ?|]; last by rewrite eqxx.
rewrite ltR_neqAle; split; first exact/nesym/eqP.
by apply/sumR_ge0 => i _; exact/mulR_ge0.
Qed.
Lemma f1 : \sum_(a <- finsupp f) f a = 1.
Proof.
rewrite {2}/f; evar (h : A -> R); rewrite (eq_big_seq h); last first.
  move=> b; rewrite supp => bD.
  rewrite fsfunE bD /h; reflexivity.
rewrite {}/h exchange_big /= -[RHS](FDist.f1 e) /=; apply eq_bigr => i _.
rewrite -big_distrr /=.
case/boolP : (e i == R0 :> R) => [/eqP -> | ei0]; first by rewrite mul0R.
rewrite -(@big_fset_incl _ _ _ _ (finsupp (g i))).
- by rewrite FSDist.f1 mulR1.
- rewrite supp /D bigfcup_sup //; exact/ltRP/fdist_gt0.
- by move=> a _; rewrite memNfinsupp => /eqP.
Qed.
Definition d : {dist A} := locked (FSDist.make f0 f1).
Lemma dE a : d a = [fsfun a in D => \sum_(i < n) e i * g i a | 0] a.
Proof. by rewrite /d; unlock; rewrite fsfunE. Qed.
End def.
End ConvnFSDist.

Module ConvFSDist.
Section def.
Variables (A : choiceType) (p : prob) (d1 d2 : {dist A}).
Definition d : {dist A} := locked
  (ConvnFSDist.d (I2FDist.d p) (fun i => if i == ord0 then d1 else d2)).
Local Open Scope reals_ext_scope.
Lemma dE a : (d a = p * d1 a + p.~ * d2 a)%R.
Proof.
rewrite /d; unlock => /=.
rewrite ConvnFSDist.dE fsfunE.
case: ifPn => [?|H].
  rewrite !big_ord_recl big_ord0 /= addR0 !I2FDist.dE.
  by rewrite eqxx eq_sym (negbTE (neq_lift _ _)).
case/boolP : (p == R0 :> R) => [/eqP |] p0.
  rewrite p0 mul0R add0R onem0 mul1R.
  apply/esym/eqP; rewrite -memNfinsupp.
  apply: contra H => H.
  rewrite (_ : p = 0%:pr) //; last exact/val_inj.
  rewrite I2FDist.p0 (_ : Ordinal _ = @ord_max 1); last exact/val_inj.
  (* TODO: generalize *)
  suff : ConvnFSDist.D (FDist1.d ord_max) (fun i : 'I_2 => if i == ord0 then d1 else d2) = finsupp d2 by move=> ->.
  rewrite /ConvnFSDist.D; apply/fsetP => a0; apply/bigfcupP/idP.
    case => /= i; rewrite mem_index_enum /= FDist1.dE.
    by case/orP : (ord2 i) => /eqP -> // /ltRP/ltRR.
  move=> a0d2.
  by exists ord_max => //=; rewrite mem_index_enum /= FDist1.dE eqxx; apply/ltRP.
have d1a0 : d1 a = 0.
  apply/eqP; rewrite -memNfinsupp.
  apply: contra H => H.
  rewrite /ConvnFSDist.D; apply/bigfcupP; exists ord0; last by rewrite eqxx.
  rewrite mem_index_enum /= I2FDist.dE eqxx; exact/ltRP/prob_gt0.
rewrite d1a0 mulR0 add0R.
case/boolP : (p == R1 :> R) => [/eqP |] p1; first by rewrite p1 onem1 mul0R.
suff : d2 a = 0 by move=> ->; rewrite mulR0.
apply/eqP; rewrite -memNfinsupp.
apply: contra H => H.
rewrite /ConvnFSDist.D; apply/bigfcupP; exists (lift ord0 ord0).
rewrite mem_index_enum /= I2FDist.dE eq_sym (negbTE (neq_lift _ _)).
exact/ltRP/onem_gt0/prob_lt1.
by rewrite eq_sym (negbTE (neq_lift _ _)).
Qed.
End def.
Section prop.
Variables (A : choiceType).
Implicit Types a b c : {dist A}.
Local Notation "x <| p |> y" := (d p x y).
Local Open Scope reals_ext_scope.
Lemma conv0 (mx my : {dist A}) : mx <| 0%:pr |> my = my.
Proof. by apply/FSDist_ext => a; rewrite dE /= mul0R add0R onem0 mul1R. Qed.
Lemma conv1 (mx my : {dist A}) : mx <| 1%:pr |> my = mx.
Proof. by apply/FSDist_ext => a; rewrite dE /= mul1R onem1 mul0R addR0. Qed.
Lemma convmm p : idempotent (fun x y => x <| p |> y : {dist A}).
Proof. by move=> d; apply/FSDist_ext => a; rewrite dE -mulRDl onemKC mul1R. Qed.
Lemma convC (p : prob) (mx my : {dist A}) : mx <| p |> my = my <| p.~%:pr |> mx.
Proof. by apply/FSDist_ext => a; rewrite 2!dE /= onemK addRC. Qed.
Lemma convA (p q r s : prob) (mx my mz : {dist A}) :
  p = r * s :> R /\ s.~ = p.~ * q.~ ->
  mx <| p |> (my <| q |> mz) = (mx <| r |> my) <| s |> mz.
Proof.
move=> [Hp Hs]; apply/FSDist_ext => a.
rewrite !dE [in RHS]mulRDr (@mulRCA _ r) (@mulRA r) -Hp -addRA; congr (_ + _)%R.
rewrite mulRDr (@mulRA p.~ q.~) -Hs; congr (_ + _)%R.
rewrite !mulRA; congr (_ * _)%R.
rewrite -p_of_rsE in Hp.
move/(congr1 onem) : Hs; rewrite onemK => Hs.
rewrite -s_of_pqE in Hs.
case/boolP : (r == 0%:pr :> prob) => [/eqP | ] r0.
  rewrite r0 /= onem0 mulR1 Hs s_of_pqE.
  by rewrite Hp p_of_rsE r0 /= mul0R onem0 !mul1R onemK.
case/boolP : (s == 0%:pr :> prob) => [/eqP | ] s0.
  rewrite Hp p_of_rsE s0 /= mulR0 onem0 mul0R mul1R.
  by move: Hs; rewrite s_of_pqE Hp p_of_rsE s0 /= mulR0 onem0 mul1R onemK.
rewrite p_of_rsE in Hp.
rewrite s_of_pqE in Hs.
move/(congr1 onem) : Hs; rewrite onemK => Hs.
move: (@r_of_pq_is_r p q r s r0 s0 Hp Hs) => <-.
rewrite pq_is_rs mulRC; congr (_ * _)%R.
by rewrite s_of_pqE -Hs onemK.
Qed.
(* TODO: move the glue lemma to convex *)
Lemma convA' (p q : prob) (a b c : {dist A}) :
  d p a (d q b c) = d (s_of_pq p q) (d (r_of_pq p q) a b) c.
Proof.
rewrite (convA (r := r_of_pq p q) (s := s_of_pq p q)) //.
rewrite {2}s_of_pqE onemK; split => //.
case/boolP : (s_of_pq p q == 0%:pr :> prob) => s0.
- rewrite (eqP s0) mulR0; apply/eqP; move: s0.
  by apply: contraTT => /(s_of_gt0 q); rewrite prob_gt0.
- by rewrite -p_is_rs.
Qed.
Lemma incl_finsupp_conv2fsdist (a b : {dist A}) (p : prob) :
  p != 0%:pr -> finsupp a `<=` finsupp (a <|p|> b).
Proof.
move=> p0.
apply/fsubsetP => a1.
rewrite !mem_finsupp => aa1.
rewrite dE.
apply: contra aa1 => /eqP.
rewrite paddR_eq0; last 2 first.
  exact/mulR_ge0.
  exact/mulR_ge0.
case.
rewrite mulR_eq0 => -[p0'|/eqP //].
exfalso.
move/eqP : p0; apply.
by apply/val_inj; rewrite /= p0'.
Qed.
Lemma tech1 (B : choiceType) (a b : {dist A}) (f : A -> {dist B}) (p : prob)
  (a0 : A) (b0 : B) (b0a0 : b0 \in finsupp (f a0)) :
  p != 0%:pr ->
  \sum_(i <- finsupp (a <|p|> b)) (a i * (f i) b0) = (FSDistBind.d a f) b0.
Proof.
move=> p0.
rewrite FSDistBind.dE.
case: ifPn => [/bigfcupP[dB] | ].
- rewrite andbT; case/imfsetP => a1 /=.
  rewrite imfset_id => a1a ->{dB} b0a2.
  apply/esym/big_fset_incl.
    exact/incl_finsupp_conv2fsdist.
  by move=> a3 Ha3; rewrite memNfinsupp => /eqP ->; rewrite mul0R.
- move=> Hb0.
  apply/psumR_seq_eq0P.
  + exact/fset_uniq.
  + move=> a1 _; exact/mulR_ge0.
  + move=> a1 Ha1.
    case/boolP : (a a1 == 0 :> R) => [/eqP -> |aa10]; first by rewrite mul0R.
    rewrite mulR_eq0; right.
    apply/eqP; rewrite -memNfinsupp.
    apply: contra Hb0 => Hb0.
    apply/bigfcupP; exists (f a1) => //; rewrite andbT.
    by apply/imfsetP; exists a1 => //=; rewrite imfset_id mem_finsupp.
Qed.
Lemma bind_left_distr (B : choiceType) (p : prob) a b (f : A -> {dist B}) :
  FSDistBind.d (a <| p |> b) f = FSDistBind.d a f <| p |> FSDistBind.d b f.
Proof.
apply/FSDist_ext => b0 /=; rewrite FSDistBind.dE dE.
case/boolP : (p == 0%:pr :> prob) => [/eqP -> | p0].
  by rewrite conv0 mul0R add0R onem0 mul1R FSDistBind.dE.
case/boolP : (p == 1%:pr :> prob) => [/eqP -> | p1].
  by rewrite conv1 mul1R onem1 mul0R addR0 FSDistBind.dE.
case: ifPn => [/bigfcupP[dB] | ].
  rewrite andbT.
  case/imfsetP => a0 /=.
  rewrite inE /= => Ha0 ->{dB} b0a0.
  evar (h : A -> R); rewrite (eq_bigr h); last first.
    move=> a1 _.
    rewrite dE (@mulRDl _ _ (f a1 b0)) -!mulRA /h; reflexivity.
  rewrite {}/h big_split /= -2!big_distrr /=.
  congr (_ * _ + _ * _)%R.
  exact/(tech1 _ _ b0a0).
  rewrite convC (tech1 _ _ b0a0) //.
  apply: contra p1 => /eqP.
  move/(congr1 (fun x : prob => x.~)).
  rewrite onemK onem0 => p1.
  exact/eqP/val_inj.
move=> Hb0.
apply/esym/paddR_eq0.
  exact/mulR_ge0.
  exact/mulR_ge0.
split.
- rewrite mulR_eq0; right.
  rewrite FSDistBind.dE; case: ifPn => // abs.
  exfalso.
  move/negP : Hb0; apply.
  case/bigfcupP : abs => dB.
  rewrite andbT => /imfsetP[a0 /=] /imfsetP[a1 /=] a1a ->{a0} ->{dB} Hb0.
  apply/bigfcupP; exists (f a1) => //; rewrite andbT.
  apply/imfsetP; exists a1 => //=.
  rewrite imfset_id.
  move: a1 a1a {Hb0}; apply/fsubsetP.
  exact/incl_finsupp_conv2fsdist.
- (* TODO: copype *) rewrite mulR_eq0; right.
  rewrite FSDistBind.dE; case: ifPn => // abs.
  exfalso.
  move/negP : Hb0; apply.
  case/bigfcupP : abs => dB; rewrite andbT.
  move => /imfsetP[a0 /=] /imfsetP[a1 /=] a1a ->{a0} ->{dB} Hb0.
  apply/bigfcupP; exists (f a1) => //; rewrite andbT.
  apply/imfsetP; exists a1 => //=.
  rewrite imfset_id.
  move: a1 a1a {Hb0}; apply/fsubsetP.
  rewrite convC; apply/incl_finsupp_conv2fsdist.
  apply: contra p1 => /eqP.
  move/(congr1 (fun x : prob => x.~)).
  by rewrite onemK onem0 => p1; exact/eqP/val_inj.
Qed.
End prop.
End ConvFSDist.

(*Require Import convex.

Section Dist_convex_space.
Variable A : choiceType.
Definition Dist_convMixin :=
  @ConvexSpace.Class (Dist A) (@Conv2Dist.d A)
  (@Conv2Dist.conv1 A)
  (fun d p => @Conv2Dist.convmm A p d)
  (fun d1 d2 p => @Conv2Dist.convC A p d1 d2)
  (@Conv2Dist.convA' A).
Canonical Dist_convType := ConvexSpace.Pack Dist_convMixin.
End Dist_convex_space.*)

Definition FSDist_convMixin (A : choiceType) :=
  @ConvexSpace.Mixin (FSDist_choiceType A) (@ConvFSDist.d A)
  (@ConvFSDist.conv1 A)
  (@ConvFSDist.convmm A)
  (@ConvFSDist.convC A)
  (@ConvFSDist.convA' A).
Canonical FSDist_convType (A : choiceType) :=
  ConvexSpace.Pack (ConvexSpace.Class (FSDist_convMixin A)).

Fact FSDistfmap_affine (A B : choiceType) (f : A -> B) : affine (FSDistfmap f).
Proof. by move=> ? ? ?; rewrite /FSDistfmap ConvFSDist.bind_left_distr. Qed.
Canonical Affine_FSDistfmap_affine (A B : choiceType) (f : A -> B) :=
  Affine (FSDistfmap_affine f).

Definition FSDist_to_convType (A : choiceType) :=
  fun phT : phant (Choice.sort A) => FSDist_convType A.
Notation "{ 'dist' T }" := (FSDist_to_convType (Phant T)) : proba_scope.

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope convex_scope.

Section FSDist_convex_space.
Variable A : choiceType.

(* Reuse the morphisms from R_convex_space. *)
Import ScaledConvex finmap.
Lemma convn_convnfsdist (n : nat) (g : 'I_n -> {dist A}) (d : {fdist 'I_n}) :
  <|>_d g = ConvnFSDist.d d g.
Proof.
apply FSDist_ext=> a; rewrite -[LHS]Scaled1RK.
pose f := fun x : {dist A} => finmap.fun_of_fsfun x a.
have af : affine f by move=> p x y; rewrite /f /= ConvFSDist.dE.
rewrite (S1_convn_proj (Affine af)) /= big_scaleR ConvnFSDist.dE /= fsfunE.
case: ifPn => adg.
  by apply eq_bigr => i _; rewrite scaleR_scalept // Scaled1RK.
(* TODO: extra lemmas ? *)
rewrite big1 // => i _.
move: adg; rewrite /ConvnFSDist.D => /bigfcupP Hn.
have [/eqP ->|di0] := boolP (d i == 0); first by rewrite scalept0.
have [/eqP gia0|gia0] := boolP (g i a == 0).
  by rewrite /f gia0 scaleR_scalept /= ?mulR0.
elim: Hn; exists i; last by rewrite mem_finsupp.
by rewrite mem_index_enum /=; apply/ltRP; rewrite -fdist_gt0.
Qed.
End FSDist_convex_space.

Section fsdist_ordered_convex_space.
Variable A : choiceType.
Definition fsdist_orderedConvMixin := @OrderedConvexSpace.Mixin {dist A}.
End fsdist_ordered_convex_space.

(* TODO: these lemmas could be better organized *)
Section misc_lemmas.

Lemma finsupp_Conv (C : convType) p (p0 : p != 0%:pr) (p1 : p != 1%:pr) (d e : {dist C}) :
  finsupp (d <|p|> e) = (finsupp d `|` finsupp e)%fset.
Proof.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP => j;
  rewrite !mem_finsupp !ConvFSDist.dE inE; first by
    move=> H; rewrite 2!mem_finsupp; apply/orP/paddR_neq0 => //;
    apply: contra H => /eqP/paddR_eq0 => /(_ (FSDist.ge0 _ _ ))/(_ (FSDist.ge0 _ _)) [-> ->];
    rewrite 2!mulR0 addR0.
move/prob_gt0 in p0.
move: p1 => /onem_neq0 /prob_gt0 /= p1.
by rewrite 2!mem_finsupp => /orP[dj0|ej0]; apply/gtR_eqF;
  [apply/addR_gt0wl; last exact/mulR_ge0;
   apply/mulR_gt0 => //; apply/ltR_neqAle; split => //; exact/nesym/eqP |
   apply/addR_gt0wr; first exact/mulR_ge0;
   apply/mulR_gt0 => //; apply/ltR_neqAle; split => //; exact/nesym/eqP].
Qed.

(* Evaluation operation of FSDists at some fixed element is affine *)
Lemma FSDist_eval_affine (C : choiceType) (x : C) :
  affine (fun D : {dist C} => D x).
Proof. by move=> a b p; rewrite ConvFSDist.dE. Qed.
Canonical Affine_FSDist_eval_affine (C : choiceType) (x : C) :=
  Affine (FSDist_eval_affine x).

Section misc_scaled.
Import ScaledConvex.
Local Open Scope R_scope.

Lemma FSDist_scalept_conv (C : convType) (x y : {dist C}) (p : prob) (i : C) :
  scalept ((x <|p|> y) i) (S1 i) =
    scalept (x i) (S1 i) <|p|> scalept (y i) (S1 i).
Proof. by rewrite ConvFSDist.dE scalept_conv. Qed.
End misc_scaled.

End misc_lemmas.

Section Convn_of_FSDist.
Local Open Scope classical_set_scope.
Variable C : convType.

Definition Convn_of_FSDist (d : {dist C}) : C :=
  <$>_(fdist_of_Dist d) (fun x : finsupp d => fsval x).
Import ScaledConvex.

Lemma ssum_seq_finsuppE'' (D : convType) (f : C -> D) (d x : {dist C}) :
  \ssum_(i : fdist_of_FSDist.D d) scalept (x (fsval i)) (S1 (f (fsval i))) =
  \ssum_(i <- finsupp d) scalept (x i) (S1 (f i)).
Proof.
by rewrite -(@big_seq_fsetE
               _ _ _ _ _ xpredT
               (fun i => scalept (x i) (S1 (f i)))).
Qed.

Lemma ssum_seq_finsuppE' (d x : {dist C}) :
  \ssum_(i : fdist_of_FSDist.D d) scalept (x (fsval i)) (S1 (fsval i)) =
  \ssum_(i <- finsupp d) scalept (x i) (S1 i).
Proof.
by rewrite (ssum_seq_finsuppE'' idfun).
Qed.

Lemma ssum_seq_finsuppE (d : {dist C}) :
  \ssum_i scalept (fdist_of_Dist d i) (S1 (fsval i)) =
  \ssum_(i <- finsupp d) scalept (d i) (S1 i).
Proof.
under eq_bigr do rewrite fdist_of_FSDistE.
by rewrite ssum_seq_finsuppE'.
Qed.

Lemma ssum_widen_finsupp (x : {dist C}) X :
  (finsupp x `<=` X)%fset ->
  \ssum_(i <- finsupp x) scalept (x i) (S1 i) =
  \ssum_(i <- X) scalept (x i) (S1 i).
Proof.
move=> xX.
rewrite [in RHS](bigID (fun i => i \in finsupp x)) /=.
have -> : (\ssum_(i <- X | i \notin finsupp x) scalept (x i) (S1 i)) = Zero
  by rewrite big1 //= => i Hi; rewrite fsfun_dflt // scalept0.
rewrite addpt0 [in RHS]big_fset_condE /=.
suff H : finsupp x = [fset i | i in X & i \in finsupp x]%fset
  by rewrite [in LHS]H.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP=> c; rewrite !inE /=.
- by move=> cfx; move/fsubsetP/(_ c):xX ->.
- by case/andP.
Qed.

Lemma Convn_of_FSDist_affine : affine Convn_of_FSDist.
Proof.
move=> p x y.
case/boolP : (p == 0%:pr) => [/eqP ->|pn0]; first by rewrite !conv0.
case/boolP : (p == 1%:pr) => [/eqP ->|pn1]; first by rewrite !conv1.
have opn0 : p.~ != 0%:pr by apply onem_neq0.
apply S1_inj.
rewrite S1_conv !S1_Convn_finType ssum_seq_finsuppE.
under eq_bigr do rewrite FSDist_scalept_conv.
rewrite big_seq_fsetE big_scalept_conv_split /=.
rewrite 2!ssum_seq_finsuppE' 2!ssum_seq_finsuppE.
have -> : \ssum_(i <- finsupp x) scalept (x i) (S1 i) =
         \ssum_(i <- finsupp (x <|p|> y)) scalept (x i) (S1 i)
  by apply/ssum_widen_finsupp/ConvFSDist.incl_finsupp_conv2fsdist.
have -> : \ssum_(i <- finsupp y) scalept (y i) (S1 i) =
         \ssum_(i <- finsupp (x <|p|> y)) scalept (y i) (S1 i)
  by rewrite convC; apply/ssum_widen_finsupp/ConvFSDist.incl_finsupp_conv2fsdist.
done.
Qed.
Canonical Affine_Convn_of_FSDist_affine := Affine Convn_of_FSDist_affine.
End Convn_of_FSDist.

Section lemmas_for_probability_monad_and_adjunction.
Import ScaledConvex.
Local Open Scope fset_scope.
Local Open Scope R_scope.
Lemma Convn_of_FSDist_FSDist1 (C : convType) (x : C) :
  Convn_of_FSDist (FSDist1.d x) = x.
Proof.
apply: (@ScaledConvex.S1_inj _ _ x).
rewrite S1_Convn_finType /=.
rewrite (eq_bigr (fun=> ScaledConvex.S1 x)); last first.
  move=> i _; rewrite fdist_of_FSDistE FSDist1.dE /= -(FSDist1.supp x).
  rewrite fsvalP ScaledConvex.scalept1 /=; congr (ScaledConvex.S1 _).
  by case: i => i Hi /=; rewrite FSDist1.supp inE in Hi; rewrite (eqP Hi).
by rewrite big_const (_ : #| _ | = 1%N) // -cardfE FSDist1.supp cardfs1.
Qed.

Lemma Convn_of_FSDist_FSDistfmap (C D : convType) (f : {affine C -> D}) (d : {dist C}) :
  f (Convn_of_FSDist d) = Convn_of_FSDist (FSDistfmap f d).
Proof.
apply S1_inj => /=.
rewrite S1_proj_Convn_finType // S1_Convn_finType.
set X := LHS.
under eq_bigr do rewrite fdist_of_FSDistE.
rewrite ssum_seq_finsuppE' supp_FSDistfmap.
under eq_bigr do rewrite FSDistBind.dE imfset_id.
have Hsupp : forall y,
    y \in [fset f x | x in finsupp d] ->
    y \in \bigcup_(d0 <- [fset FSDist1.d (f a) | a in finsupp d]) finsupp d0.
- move=> y.
  case/imfsetP=> x /= xfd ->.
  apply/bigfcupP; exists (FSDist1.d (f x)); last by rewrite FSDist1.supp inE.
  by rewrite andbT; apply/imfsetP; exists x.
rewrite big_seq; under eq_bigr=> y Hy.
- rewrite (Hsupp y Hy).
  rewrite big_scaleptl'; [| by rewrite scalept0 | by move=> j; apply mulR_ge0].
  under eq_bigr=> i do rewrite FSDist1.dE inE.
  over.
rewrite -big_seq exchange_big /=.
rewrite (@big_seq _ _ _ _ (finsupp d)).
under eq_bigr=> x Hx.
- rewrite (big_fsetD1 (f x)) /=; last by apply/imfsetP; exists x.
  rewrite eqxx mulR1.
  rewrite (@big_seq _ _ _ _ ([fset f x0 | x0 in finsupp d] `\ f x)).
  under eq_bigr=> y do [rewrite in_fsetD1=> /andP [] /negbTE -> Hy; rewrite mulR0 scalept0].
  rewrite big1 // addpt0.
  over.
rewrite /X.
under eq_bigr do rewrite fdist_of_FSDistE.
by rewrite ssum_seq_finsuppE'' big_seq.
Qed.

Section triangular_laws_left_convn.
Variable C : choiceType.
Lemma triangular_laws_left0 (d : {dist C}) :
  Convn_of_FSDist (FSDistfmap (@FSDist1.d C) d) = d.
Proof.
apply FSDist_ext => x; apply S1_inj.
rewrite (S1_proj_Convn_finType (Affine_FSDist_eval_affine x)).
under eq_bigr do rewrite fdist_of_FSDistE.
rewrite (ssum_seq_finsuppE'' (fun i : {dist C} => i x)).
rewrite supp_FSDistfmap.
rewrite big_imfset /=; last by move=> *; apply: FSDist1_inj.
under eq_bigr do rewrite FSDist1.dE inE FSDistfmap_FSDist1.
have nx0 :
  \ssum_(i <- finsupp d `\ x)
   scalept (d i) (S1 (if x == i then 1 else 0)) = scalept (d x).~ (S1 0).
- transitivity (scalept (\sum_(i <- finsupp d `\ x) (d i)) (S1 0)).
  + rewrite big_scaleptl' //; last by rewrite scalept0.
    erewrite eq_fbigr; first reflexivity.
    by move=> y /fsetD1P []; rewrite eq_sym=> /negbTE ->.
  congr (_ _ _).
  by rewrite FSDist_finsuppD1.
case/boolP: (x \in finsupp d) => xfd.
- rewrite (big_fsetD1 x) //= nx0 eqxx -convptE adjunction_2.
  by rewrite avgRE mulR0 addR0 mulR1.
by rewrite -(mem_fsetD1 xfd) nx0 fsfun_dflt // onem0 scalept1.
Qed.
End triangular_laws_left_convn.

End lemmas_for_probability_monad_and_adjunction.
