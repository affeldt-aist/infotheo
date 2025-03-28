(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import finmap.
From mathcomp Require Import mathcomp_extra.
From mathcomp Require Import classical_sets boolp cardinality reals Rstruct.
From mathcomp Require ereal topology esum measure probability.
Require Import realType_ext ssr_ext ssralg_ext.
Require Import bigop_ext fdist convex.

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
(*                      where A is a choiceType (see fdist.v for              *)
(*                      distributions over a finType)                         *)
(*           fsdist1 == unit of the probability monad                         *)
(*        fsdistbind == bind of the probability monad, notation >>=, scope    *)
(*                      fsdist_scope (delimiter: fsdist)                      *)
(*         fsdistmap == map of the probability monad                          *)
(* FSDist_choiceType == instance of choiceType with finitely-supported        *)
(*                      distributions                                         *)
(* [the convType of {dist A}] == instance of a convex space on {dist A}       *)
(*                                                                            *)
(* Free convex spaces in terms of finitely-supported distributions:           *)
(*  the instance [the convType of {dist A}] constructs a freely generated     *)
(*  convex space from any given choiceType A.                                 *)
(*   fsdistmap f is shown to have the structure of an affine function         *)
(*   fsdist_eval x d == evaluation operation of fsdists at some fixed element,*)
(*                      shown have the structure of an affine function        *)
(*  Convn_of_fsdist d == <$>_(fdist_of_fs d) (fun x : finsupp d => fsval x),  *)
(*                       a variant of Convn whose input data (points and      *)
(*                       weights) are provided by a single fsdist; this is    *)
(*                       the counit of the adjunction that produces the       *)
(*                       probability monad (see monae, gcm_model.v), shown    *)
(*                       to have the structure of an affine function          *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "{ 'dist' T }" (at level 0, format "{ 'dist'  T }").
Reserved Notation "R '.-dist' T" (at level 2, format "R '.-dist'  T").

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fset_scope.
Local Open Scope fdist_scope.
Local Open Scope ring_scope.

Import Order.POrderTheory GRing.Theory Num.Theory.

(* NB: PR to finmap in progress *)
Lemma bigfcup_imfset (T I : choiceType) (P : {fset I}) (f : I -> T) :
  \bigcup_(x <- P) [fset f x] = f @` P.
Proof.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP=> x.
- case/bigfcupP=> i /andP [] iP _.
  rewrite inE => /eqP ->.
  by apply/imfsetP; exists i.
- case/imfsetP => i /= iP ->; apply/bigfcupP; exists i; rewrite ?andbT //.
  by apply/imfsetP; exists (f i); rewrite ?inE.
Qed.

(* NB: PR to finmap in progress *)
Section fbig_pred1_inj.
Variables (R : Type) (idx : R) (op : Monoid.com_law idx).
Lemma fbig_pred1_inj (A : choiceType) (C : eqType) h (k : A -> C) (d : {fset _}) a :
  a \in d -> injective k -> \big[op/idx]_(a0 <- d | k a0 == k a) h a0 = h a.
Proof.
move=> ad inj_k.
rewrite big_fset_condE -(big_seq_fset1 op); apply eq_fbig => // a0.
rewrite !inE /=; apply/idP/idP => [|/eqP ->]; last by rewrite eqxx andbT.
by case/andP => _ /eqP/inj_k ->.
Qed.
End fbig_pred1_inj.
Arguments fbig_pred1_inj [R] [idx] [op] [A] [C] [h] [k].

Module FSDist.
Section fsdist.
Variable R : realType.
Variable A : choiceType.

Record t := mk {
  f :> {fsfun A -> R with 0} ;
  _ : all (fun x => 0 < f x) (finsupp f) &&
      \sum_(a <- finsupp f) f a == 1}.

Lemma ge0 (d : t) a : 0 <= d a.
Proof.
case: d => /= [f /andP[/allP f0 _]].
have [/f0/ltW//|/fsfun_dflt->] := boolP (a \in finsupp f).
exact: lexx.
Qed.

Lemma gt0 (d : t) a : a \in finsupp d -> 0 < d a.
Proof.
by rewrite mem_finsupp => da; rewrite lt0r da; exact/ge0.
Qed.

Lemma f1 (d : t) : \sum_(a <- finsupp d) d a = 1.
Proof. by case: d => f /= /andP[_ /eqP]. Qed.

Lemma le1 (d : t) a : d a <= 1.
Proof.
have [ad|?] := boolP (a \in finsupp d); last by rewrite fsfun_dflt.
rewrite -(f1 d) (big_fsetD1 _ ad)/=; rewrite lerDl.
by apply/sumr_ge0 => ? _; exact/ge0.
Qed.

Obligation Tactic := idtac.

Program Definition make (f : {fsfun A -> R with 0})
  (H0 : forall a, a \in finsupp f -> 0 < f a)
  (H1 : \sum_(a <- finsupp f) f a = 1) : t := @mk f _.
Next Obligation.
by move=> f H0 ->; rewrite eqxx andbT; apply/allP => a /H0.
Qed.

End fsdist.
End FSDist.
Notation fsdist := FSDist.t.
Coercion FSDist.f : FSDist.t >-> fsfun.

Global Hint Resolve FSDist.ge0 : core.
Hint Extern 0 (is_true (0 <= _)) => solve [exact: FSDist.ge0] : core.
Hint Extern 0 (is_true (_ <= 1)) => solve [exact: FSDist.le1] : core.

Section FSDist_canonical.
Context {R : realType}.
Variable A : choiceType.
HB.instance Definition _ := [isSub for @FSDist.f R A].
HB.instance Definition _ := [Equality of fsdist R A by <:].
HB.instance Definition _ := [Choice of fsdist R A by <:].
End FSDist_canonical.

(*Definition FSDist_to_Type (A : choiceType) :=
  fun phT : phant (Choice.sort A) => fsdist A.
Local Notation "{ 'dist' T }" := (FSDist_to_Type (Phant T)).*)
Notation "R '.-dist' T" := (fsdist R T%type).
Local Notation "{ 'dist' T }" := (fsdist Rdefinitions.R T%type).

Section fsdist_prop.
Context {R : realType}.
Variable A : choiceType.

Lemma fsdist_ext (d d' : R.-dist A) : (forall x, d x = d' x) -> d = d'.
Proof. by move=> ?; exact/val_inj/fsfunP. Qed.

Lemma fsdist_supp_neq0 (d : R.-dist A) : finsupp d != fset0.
Proof.
apply/eqP => d0.
by move: (FSDist.f1 d); rewrite d0 big_nil => /esym; exact/eqP/oner_neq0.
Qed.

End fsdist_prop.

Section fsdist1.
Context {R : realType}.
Variables (A : choiceType) (a : A).

Let D := [fset a].

Let f : {fsfun A -> R with 0} := [fsfun b in D => 1 | 0].

Let suppf : finsupp f = D.
Proof.
apply/fsetP => b; rewrite mem_finsupp /f fsfunE inE.
by case: ifPn=> ba; rewrite ?oner_neq0 ?eqxx.
Qed.

Let f0 b : b \in finsupp f -> 0 < f b.
Proof. by rewrite mem_finsupp fsfunE inE; case: ifPn => //; rewrite eqxx. Qed.

Let f1 : \sum_(b <- finsupp f) f b = 1.
Proof. by rewrite suppf big_seq_fset1 /f fsfunE inE eqxx. Qed.

(* TODO simpl never *)
Definition fsdist1 : R.-dist A := locked (FSDist.make f0 f1).

Lemma fsdist1E a0 : fsdist1 a0 = if a0 \in D then 1 else 0.
Proof. by rewrite /fsdist1; unlock; rewrite fsfunE. Qed.

Lemma supp_fsdist1 : finsupp fsdist1 = D.
Proof.
by rewrite -suppf; apply/fsetP => b; rewrite !mem_finsupp fsdist1E fsfunE.
Qed.

Lemma fsdist1xx : fsdist1 a = 1.
Proof. by rewrite fsdist1E /= /D inE eqxx. Qed.

Lemma fsdist10 a0 : a0 != a -> fsdist1 a0 = 0.
Proof. by move=> a0a; rewrite fsdist1E /D inE (negbTE a0a). Qed.

End fsdist1.

Lemma fsdist1_inj {R : realType} (C : choiceType) : injective (@fsdist1 R C).
Proof.
move=> a b /eqP ab; apply/eqP; apply: contraTT ab => ab.
apply/eqP => /(congr1 (fun x : FSDist.t R _ => x a)).
by rewrite !fsdist1E !inE eqxx (negbTE ab); exact/eqP/oner_neq0.
Qed.

Section fsdistbind.
Context {R : realType}.
Variables (A B : choiceType) (p : R.-dist A) (g : A -> R.-dist B).

Let D := \bigcup_(d <- g @` finsupp p) finsupp d.

Let f : {fsfun B -> R with 0} :=
  [fsfun b in D => \sum_(a <- finsupp p) p a * (g a) b | 0].

Let f0 b : b \in finsupp f -> 0 < f b.
Proof.
rewrite mem_finsupp fsfunE; case: ifPn => [_ H|]; last by rewrite eqxx.
rewrite lt_neqAle [X in ~~ X && _]eq_sym H /= sumr_ge0 // => *.
exact:mulr_ge0.
Qed.

Let f1 : \sum_(b <- finsupp f) f b = 1.
Proof.
rewrite {2}/f.
under eq_bigr do rewrite fsfunE.
rewrite -big_mkcond /= exchange_big /=.
rewrite -[RHS](FSDist.f1 p); apply eq_bigr => a _.
have [->|pa0] := eqVneq (p a) 0.
  by rewrite big1 // => *; rewrite mul0r.
rewrite -big_distrr /= (_ : \sum_(_ <- _ | _) _ = 1) ?mulr1 //.
rewrite (bigID (mem (finsupp (g a)))) /=.
rewrite [X in _ + X = _]big1 ?addr0; last first.
  by move=> b /andP[_]; rewrite memNfinsupp => /eqP.
rewrite (eq_bigl (fun i => i \in finsupp (g a))); last first.
  move=> b; rewrite andb_idl // mem_finsupp => gab0.
  apply/bigfcupP; exists (g a); rewrite ?mem_finsupp // andbT.
  by apply/imfsetP; exists a => //; rewrite mem_finsupp.
rewrite -big_filter -[RHS](FSDist.f1 (g a)); apply perm_big.
apply uniq_perm; [by rewrite filter_uniq | by rewrite fset_uniq |move=> b].
rewrite mem_finsupp.
apply/idP/idP => [|gab0]; first by rewrite mem_filter mem_finsupp => /andP[].
rewrite mem_filter 2!mem_finsupp gab0 /= /f fsfunE ifT; last first.
  apply/bigfcupP; exists (g a); rewrite ?mem_finsupp // andbT.
  by apply/imfsetP; exists a => //; rewrite mem_finsupp.
apply: contra gab0; rewrite psumr_eq0; last first.
  by move=> a0 _; rewrite mulr_ge0//.
move=> /allP H.
suff : p a * g a b == 0 by rewrite mulrI_eq0 //; apply/lregP.
by apply/H; rewrite mem_finsupp.
Qed.

Definition fsdistbind : R.-dist B := locked (FSDist.make f0 f1).

Lemma fsdistbindEcond x :
  fsdistbind x = if x \in D then \sum_(a <- finsupp p) p a * (g a) x else 0.
Proof. by rewrite /fsdistbind; unlock; rewrite fsfunE. Qed.

Lemma fsdistbindE x : fsdistbind x = \sum_(a <- finsupp p) p a * (g a) x.
Proof.
rewrite fsdistbindEcond.
case: ifPn => // aD.
apply/eqP; move: aD; apply: contraLR.
rewrite eq_sym negbK psumr_neq0; last by move=> *; exact: mulr_ge0.
case/hasP => i suppi /= pg0.
apply/bigfcupP; exists (g i).
- by rewrite in_imfset.
- by rewrite mem_finsupp gt_eqF // (wpmulr_rgt0 _ pg0).
Qed.

Lemma fsdistbindEwiden S x :
  finsupp p `<=` S -> fsdistbind x = \sum_(a <- S) p a * (g a) x.
Proof.
move=> suppS; rewrite fsdistbindE (big_fset_incl _ suppS) //.
by move=> a2 Ha2; rewrite memNfinsupp => /eqP ->; rewrite mul0r.
Qed.

Lemma supp_fsdistbind : finsupp fsdistbind = D.
Proof.
apply/fsetP => b; rewrite mem_finsupp; apply/idP/idP => [|].
  by rewrite fsdistbindEcond; case: ifPn => //; rewrite eqxx.
case/bigfcupP => dB.
rewrite andbT => /imfsetP[a] /= ap ->{dB} bga.
rewrite fsdistbindE psumr_neq0; last by move=> *; exact/mulr_ge0.
apply/hasP; exists a=> //=.
by rewrite mulr_gt0 // FSDist.gt0.
Qed.

End fsdistbind.

Declare Scope fsdist_scope.
Delimit Scope fsdist_scope with fsdist.
Reserved Notation "m >>= f" (at level 49).
Notation "m >>= f" := (fsdistbind m f) : fsdist_scope.
Local Open Scope fsdist_scope.

Section fsdist_lemmas.
Context {R : realType}.

Lemma fsdist1bind (A B : choiceType) (a : A) (f : A -> R.-dist B) :
  fsdist1 a >>= f = f a.
Proof.
apply/val_inj/val_inj => /=; congr fmap_of_fsfun; apply/fsfunP => b.
by rewrite fsdistbindE supp_fsdist1 big_seq_fset1 fsdist1xx mul1r.
Qed.

Lemma fsdistbind1 (A : choiceType) (p : R.-dist A) : p >>= @fsdist1 R A = p.
Proof.
apply/val_inj/val_inj => /=; congr fmap_of_fsfun; apply/fsfunP => b.
rewrite fsdistbindEcond; case: ifPn => [|H].
  case/bigfcupP => /= d; rewrite andbT.
  case/imfsetP => /= a ap ->{d}.
  rewrite supp_fsdist1 inE => /eqP ->{b}.
  rewrite (big_fsetD1 a) //= fsdist1xx mulr1 big1_fset ?addr0 // => a0.
  by rewrite !inE => /andP[aa0] a0p _; rewrite fsdist10 ?mulr0// eq_sym.
have [->//|pb0] := eqVneq (p b) 0.
case/bigfcupP : H.
exists (fsdist1 b); last by rewrite supp_fsdist1 inE.
by rewrite andbT; apply/imfsetP; exists b => //=; rewrite mem_finsupp.
Qed.

Lemma fsdistbindA (A B C : choiceType) (m : R.-dist A) (f : A -> R.-dist B)
    (g : B -> R.-dist C) :
  (m >>= f) >>= g = m >>= (fun x => f x >>= g).
Proof.
apply/val_inj/val_inj => /=; congr fmap_of_fsfun; apply/fsfunP => c.
rewrite !fsdistbindE.
under eq_bigr do rewrite fsdistbindE big_distrl.
under [in RHS]eq_bigr do
  (rewrite fsdistbindE big_distrr /=; under eq_bigr do rewrite mulrA).
rewrite exchange_big /= !big_seq; apply: eq_bigr => a a_m.
rewrite supp_fsdistbind; apply/esym/big_fset_incl => [| b].
  apply/fsubsetP => ? ?;  apply/bigfcupP => /=.
  by exists (f a) => //; rewrite andbT in_imfset.
case/bigfcupP => ?; rewrite andbT; case/imfsetP => ? /= ? -> ?.
rewrite mem_finsupp negbK => /eqP ->.
by rewrite mulr0 mul0r.
Qed.

Definition fsdistmap (A B : choiceType) (f : A -> B) (d : R.-dist A) : R.-dist B :=
  d >>= (fun a => fsdist1 (f a)).

Lemma fsdistmap_id (A : choiceType) : fsdistmap (@id A) = @id (R.-dist A).
Proof. by rewrite boolp.funeqE => a; rewrite /fsdistmap fsdistbind1. Qed.

Lemma fsdistmap_comp (A B C : choiceType) (g : B -> C) (h : A -> B) :
  fsdistmap (g \o h) = fsdistmap g \o fsdistmap h.
Proof.
rewrite boolp.funeqE => d; rewrite /fsdistmap /= fsdistbindA; congr (_ >>= _).
by rewrite boolp.funeqE => a; rewrite fsdist1bind.
Qed.

Definition fsdistmapE (A B : choiceType) (f : A -> B) (d : R.-dist A) b :
  fsdistmap f d b = \sum_(a <- finsupp d | f a == b) d a.
Proof.
rewrite {1}/fsdistmap [in LHS]fsdistbindE (bigID (fun a => f a == b)) /=.
rewrite [X in (_ + X)%R = _](_ : _ = 0) ?addr0; last first.
  by rewrite big1 // => a fab; rewrite fsdist10 ?mulr0// eq_sym.
by apply eq_bigr => a /eqP ->; rewrite fsdist1xx mulr1.
Qed.

Lemma supp_fsdistmap (A B : choiceType) (f : A -> B) d :
  finsupp (fsdistmap f d) = [fset f x | x in finsupp d].
Proof.
rewrite /fsdistmap supp_fsdistbind; apply/fsetP => d'.
apply/bigfcupP/imfsetP => [[D]|].
  rewrite andbT => /imfsetP[a /=] ad ->{D}.
  by rewrite supp_fsdist1 inE => /eqP ->{d'}; exists a.
case=> a /= ad -> {d'}; exists (fsdist1 (f a)).
  by rewrite andbT; apply/imfsetP; exists a.
by rewrite supp_fsdist1 inE.
Qed.

Lemma fsdistmap1 (A B : choiceType) (f : A -> B) x :
  fsdistmap f (fsdist1 x) = fsdist1 (f x).
Proof. by rewrite /fsdistmap fsdist1bind. Qed.

Lemma fsdist1map (C : choiceType) (d : R.-dist C) (c : C) :
  fsdistmap (@fsdist1 R C) d (fsdist1 c) = d c.
Proof.
rewrite fsdistmapE.
case/boolP: (c \in finsupp d)=> ifd.
  by rewrite fbig_pred1_inj //; apply: fsdist1_inj.
transitivity(\sum_(a <- finsupp d | a == c) d a).
  by apply eq_bigl=> j; apply/eqtype.inj_eq/fsdist1_inj.
rewrite big_seq_cond big_pred0; last first.
  by move=> j; apply/andP; case=> jfd /eqP ji; move: jfd; rewrite ji (negbTE ifd).
by rewrite fsfun_dflt.
Qed.

Lemma fsdist_suppD1 (C : choiceType) (d : R.-dist C) (x : C) :
  \sum_(i <- finsupp d `\ x) d i = (d x).~.
Proof.
apply/eqP; rewrite -subr_eq0 subr_onem.
case/boolP: (x \in finsupp d)=> xfd.
  by rewrite [X in X - 1]addrC -big_fsetD1 //= FSDist.f1 subrr.
by rewrite fsfun_dflt // mem_fsetD1 // FSDist.f1 addr0 subrr.
Qed.

(*TODO Local Close Scope reals_ext_scope.*)

Definition FSDist_prob (C : choiceType) (d : R.-dist C) (x : C) : {prob R} :=
  Eval hnf in Prob.mk_ (andb_true_intro (conj (FSDist.ge0 d x) (FSDist.le1 d x))).
Canonical FSDist_prob.

Definition fsdistjoin A (D : R.-dist (R.-dist A)) : R.-dist A :=
  D >>= ssrfun.id.

Lemma fsdistjoinE A (D : R.-dist (R.-dist A)) x :
  fsdistjoin D x = \sum_(d <- finsupp D) D d * d x.
Proof. by rewrite /fsdistjoin fsdistbindE. Qed.

Lemma fsdistjoin1 (A : choiceType) (D : R.-dist (R.-dist A)) :
  fsdistjoin (fsdist1 D) = D.
Proof.
apply/fsdist_ext => d.
by rewrite fsdistjoinE supp_fsdist1 big_imfset // big_seq1 fsdist1xx mul1r.
Qed.

End fsdist_lemmas.

Module FSDist_crop0.
Section def.
Context {R : realType}.
Variables (A : choiceType) (P : R.-dist A).
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
have hP (a : finsupp P) : a \in finsupp f.
  by rewrite mem_finsupp fsfunE ffunE inE -mem_finsupp fsvalP.
pose h a := FSetSub (hP a).
rewrite (reindex h) /=.
  by apply eq_bigr => i _; rewrite fsfunE ffunE inE.
by exists (@fsval _ _) => //= -[a] *; exact: val_inj.
Qed.

Definition d : R.-dist (finsupp P) := FSDist.make f0 f1.

End def.
End FSDist_crop0.

Module FSDist_lift_supp.
Section def.
Context {R : realType}.
Variables (A B : choiceType) (r : A -> B) (P : R.-dist B)
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

Definition d : R.-dist A := locked (FSDist.make f0 f1).

Lemma dE a : d a = if a \in [fset s b | b in finsupp P] then P (r a) else 0.
Proof. by rewrite /d; unlock => /=; rewrite fsfunE. Qed.

End def.
End FSDist_lift_supp.

Module FSDist_of_fdist.
Section def.
Context {R : realType}.
Variable (A : finType) (P : R.-fdist A).

Let D := [fset a0 : A | P a0 != 0].
Definition f : {fsfun A -> R with 0} := [fsfun a in D => P a | 0].

Let f0 a : a \in finsupp f -> 0 < f a.
Proof.
rewrite fsfunE mem_finsupp /f fsfunE.
case: ifPn => [_|]; by [rewrite fdist_gt0 | rewrite eqxx].
Qed.

Let f1 : \sum_(a <- finsupp f) f a = 1.
Proof.
rewrite -[RHS](FDist.f1 P) [in RHS](bigID (mem (finsupp f))) /=.
rewrite [in X in _ = (_ + X)]big1 ?addr0; last first.
  move=> a; rewrite memNfinsupp fsfunE !inE /=.
  by case: ifPn => [_ /eqP //|]; rewrite negbK => /eqP.
rewrite (@eq_fbigr _ _ _ _ _ _ _ P) /=; last first.
  move=> a; rewrite mem_finsupp fsfunE !inE /=; case: ifPn => //.
  by rewrite eqxx.
exact/big_uniq/fset_uniq.
Qed.

Definition d : R.-dist A := FSDist.make f0 f1.
End def.
End FSDist_of_fdist.

Module fdist_of_FSDist.
Section def.
Context {R : realType}.
Variable (A : choiceType) (P : R.-dist A).
Definition D := finsupp P : finType.
Definition f := [ffun d : D => P (fsval d)].
Lemma f0 b : 0 <= f b. Proof. by rewrite ffunE. Qed.
Lemma f1 : \sum_(b in D) f b = 1.
Proof.
rewrite -(FSDist.f1 P) big_seq_fsetE /=; apply eq_bigr => a; by rewrite ffunE.
Qed.

Definition d : R.-fdist D := locked (FDist.make f0 f1).
End def.
Module Exports.
Notation fdist_of_fs := d.
End Exports.
End fdist_of_FSDist.
Export fdist_of_FSDist.Exports.

Section fdist_of_FSDist_lemmas.
Context {R : realType}.
Variable (A : choiceType) (d : R.-dist A).

Lemma fdist_of_fsE i : fdist_of_fs d i = d (fsval i).
Proof. by rewrite /fdist_of_fs; unlock; rewrite ffunE. Qed.

Lemma fdist_of_FSDistDE : fdist_of_FSDist.D d = finsupp d.
Proof. by []. Qed.

End fdist_of_FSDist_lemmas.

Module fdist_of_finFSDist.
Section def.
Context {R : realType}.
Variable (A : finType) (P : R.-dist A).
Definition f := [ffun d : A => P d].

Lemma f0 b : 0 <= f b. Proof. by rewrite ffunE. Qed.

Lemma f1 : \sum_(b in A) f b = 1.
Proof.
rewrite -(FSDist.f1 P) (bigID (fun x => x \in finsupp P)) /=.
rewrite [X in (_ + X = _)](_ : _ = 0) ?addr0.
  by rewrite big_uniq /= ?fset_uniq //; apply eq_bigr => i _; rewrite ffunE.
by rewrite big1 // => a; rewrite mem_finsupp negbK ffunE => /eqP.
Qed.

Definition d : R.-fdist A := locked (FDist.make f0 f1).

Lemma dE a : d a = P a.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.

End def.
Module Exports.
Notation fdist_of_finfs := d.
End Exports.
End fdist_of_finFSDist.
Export fdist_of_finFSDist.Exports.

Section fsdist_conv_def.
Context {R : realType}.
Variables (A : choiceType) (p : {prob R}) (d1 d2 : R.-dist A).
(*Local Open Scope reals_ext_scope.*)
Local Open Scope convex_scope.

Let D : {fset A} :=
  if p == 0%:pr then finsupp d2
  else if p == 1%:pr then finsupp d1
       else finsupp d1 `|` finsupp d2.

Let f := [fsfun a in D => (d1 a : R^o) <| p |> d2 a | 0].

Let supp : finsupp f = D.
Proof.
apply/fsetP => a; rewrite /f /D.
case: ifPn; [|case: ifPn];
 rewrite !mem_finsupp fsfunE ?inE !mem_finsupp avgRE.
- move/eqP => -> /=.
  rewrite onem0 mul1r mul0r add0r.
  by case: ifP => //; rewrite eqxx.
- move/eqP => -> /=.
  rewrite onem1 mul1r mul0r addr0.
  by case: ifP => //; rewrite eqxx.
- move => /[swap] /prob_gt0 p0 /onem_neq0 /prob_gt0 /= p1.
  case:ifPn; last by rewrite eqxx.
  move => /orP[dj0|ej0]; rewrite gt_eqF //.
    apply/ltr_pwDl; last exact/mulr_ge0.
    by rewrite mulr_gt0 // lt_neqAle eq_sym dj0 /=.
  apply/ltr_pwDr; last exact/mulr_ge0.
  by rewrite mulr_gt0 // lt_neqAle eq_sym ej0 /=.
Qed.

Let f0 a : a \in finsupp f -> 0 < f a.
Proof.
move => /[dup]; rewrite {1}supp => aD.
rewrite /f lt_neqAle mem_finsupp eq_sym => -> /=.
rewrite /f fsfunE avgRE aD.
by rewrite !addr_ge0.
Qed.

Let f1 : \sum_(a <- finsupp f) f a = 1.
Proof.
under eq_big_seq => b /[!supp] bD do rewrite /f fsfunE bD.
rewrite supp; under eq_bigr do rewrite avgRE.
rewrite /D; case: ifPn; [|case: ifPn].
- by move/eqP ->; under eq_bigr do rewrite onem0 mul0r mul1r add0r; rewrite FSDist.f1.
- by move/eqP ->; under eq_bigr do rewrite onem1 mul0r mul1r addr0; rewrite FSDist.f1.
- move=> /prob_lt1 p1 /prob_gt0 p0.
  rewrite big_split /=.
  rewrite -(big_fset_incl _ (fsubsetUl (finsupp d1) (finsupp d2))); last first.
    by move=> a _; rewrite mem_finsupp negbK => /eqP ->; rewrite mulr0.
  rewrite -(big_fset_incl _ (fsubsetUr (finsupp d1) (finsupp d2))); last first.
    by move=> a _; rewrite mem_finsupp negbK => /eqP ->; rewrite mulr0.
by rewrite -!big_distrr !FSDist.f1 /= !mulr1 add_onemK.
Qed.

Definition fsdist_conv : R.-dist A := locked (FSDist.make f0 f1).

Lemma fsdist_convE a : fsdist_conv a = (d1 a : R^o) <| p |> d2 a.
Proof.
rewrite /fsdist_conv -lock fsfunE.
case: ifPn => //.
rewrite /D; case: ifPn; [| case: ifPn].
- by move/eqP ->; rewrite conv0 mem_finsupp negbK => /eqP ->.
- by move/eqP ->; rewrite conv1 mem_finsupp negbK => _ /eqP ->.
- move=> _ _; rewrite inE !mem_finsupp negb_or !negbK => /andP [] /eqP -> /eqP ->.
  by rewrite convmm.
Qed.

Lemma supp_fsdist_conv' : finsupp fsdist_conv = D.
Proof. by rewrite /fsdist_conv -lock supp. Qed.

End fsdist_conv_def.

Section fsdist_convType.
Context {R : realType}.
Variables (A : choiceType).
Implicit Types (p q : {prob R}) (a b c : R.-dist A).
(*Local Open Scope reals_ext_scope.*)

Local Notation "x <| p |> y" := (fsdist_conv p x y) : fsdist_scope.

Let conv0 a b : a <| 0%:pr |> b = b.
Proof. by apply/fsdist_ext => ?; rewrite fsdist_convE conv0. Qed.

Let conv1 a b : a <| 1%:pr |> b = a.
Proof. by apply/fsdist_ext => ?; rewrite fsdist_convE conv1. Qed.

Let convmm p : idempotent_op (fun x y => x <| p |> y : R.-dist A).
Proof. by move=> d; apply/fsdist_ext => ?; rewrite fsdist_convE convmm. Qed.

Let convC p a b : a <| p |> b = b <| (Prob.p p).~%:pr |> a.
Proof. by apply/fsdist_ext => ?; rewrite 2!fsdist_convE convC. Qed.

Let convA p q a b c :
  a <| p |> (b <| q |> c) = (a <| r_of_pq p q |> b) <| s_of_pq p q |> c.
Proof. by apply/fsdist_ext=> ?; rewrite !fsdist_convE convA. Qed.

HB.instance Definition _ :=
  @isConvexSpace.Build _ (FSDist.t _ _) (@fsdist_conv R A)
  conv1 convmm convC convA.

End fsdist_convType.

Section fsdist_conv_prop.
Context {R : realType}.
Variables (A : choiceType).
Implicit Types (p : {prob R}) (a b c : R.-dist A).
(*Local Open Scope reals_ext_scope.*)
Local Open Scope convex_scope.

Lemma finsupp_conv_subr a b p :
  p != 0%:pr -> finsupp a `<=` finsupp (a <|p|> b).
Proof.
move=> p0.
rewrite /conv supp_fsdist_conv' (negPf p0).
by case: ifP=> ?; [exact: fsubset_refl | exact: fsubsetUl].
Qed.

Lemma finsupp_conv_subl a b p :
  p != 1%:pr -> finsupp b `<=` finsupp (a <|p|> b).
Proof.
move=> p1; rewrite convC; apply: finsupp_conv_subr.
apply: contra p1 => /eqP/(congr1 val) /= /onem_eq0 p1.
exact/eqP/val_inj.
Qed.

Lemma fsdist_conv_bind_left_distr (B : choiceType) p a b (f : A -> R.-dist B) :
  (a <| p |> b) >>= f = (a >>= f) <| p |> (b >>= f).
Proof.
apply/fsdist_ext => b0 /=; rewrite fsdistbindE fsdist_convE.
have [->|p0] := eqVneq p 0%:pr.
  by rewrite 2!conv0 fsdistbindE.
have [->|p1] := eqVneq p 1%:pr.
  by rewrite 2!conv1 fsdistbindE.
under eq_bigr do rewrite fsdist_convE avgRE mulrDl -!mulrA.
(*under eq_bigr do rewrite fsdist_convE avgR_mulDl avgRE.*)
rewrite big_split -2!big_distrr /=.
by rewrite -!fsdistbindEwiden // ?finsupp_conv_subl ?finsupp_conv_subr.
Qed.

Lemma supp_fsdist_conv p (p0 : p != 0%:pr) (p1 : p != 1%:pr) a b :
  finsupp (a <|p|> b) = finsupp a `|` finsupp b.
Proof. by rewrite supp_fsdist_conv' (negPf p0) (negPf p1). Qed.

Lemma fsdist_scalept_conv (C : convType R) (x y : R.-dist C) (p : {prob R}) (i : C) :
  scalept ((x <|p|> y) i) (S1 i) = scalept (x i) (S1 i) <|p|> scalept (y i) (S1 i).
Proof. by rewrite fsdist_convE scalept_conv. Qed.

End fsdist_conv_prop.

(*Definition FSDist_to_convType (A : choiceType) :=
  fun phT : phant (Choice.sort A) => conv_choiceType [the convType of FSDist.t A].
Notation "{ 'dist' T }" := (FSDist_to_convType (Phant T)) : proba_scope.*)
Notation "{ 'dist' T }" := (FSDist.t T) : proba_scope.

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope convex_scope.

Section FSDist_affine_instances.
Context {R : realType}.
Variable A B : choiceType.

Lemma fsdistmap_affine (f : A -> B) : @affine R _ _ (fsdistmap f).
Proof. by move=> ? ? ?; rewrite /fsdistmap fsdist_conv_bind_left_distr. Qed.

HB.instance Definition _ (f : A -> B) :=
  isAffine.Build _ _ _ _ (fsdistmap_affine f).

Definition fsdist_eval (x : A) := fun D : R.-dist A => (D x: R^o).

Lemma fsdist_eval_affine (x : A) : @affine R _ R^o (fsdist_eval x).
Proof. by move=> a b p; rewrite /fsdist_eval fsdist_convE. Qed.

HB.instance Definition _ (x : A) :=
  isAffine.Build _ _ _ _ (fsdist_eval_affine x).

End FSDist_affine_instances.

Section fsdist_convn_lemmas.
Context {R : realType}.
Local Open Scope fdist_scope.
Variables (A : choiceType) (n : nat) (e : R.-fdist 'I_n) (g : 'I_n -> R.-dist A).

Lemma fsdist_convnE x : (<|>_e g) x = \sum_(i < n) e i * g i x.
Proof. by rewrite -/(fsdist_eval x _) Convn_comp /= /fsdist_eval avgnRE. Qed.

(*TODO: unused, remove?*)
Lemma supp_fsdist_convn :
  finsupp (<|>_e g) = \big[fsetU/fset0]_(i < n | (0 < e i)) finsupp (g i).
Proof.
apply/fsetP => a; apply/idP/idP => [|]; rewrite mem_finsupp fsdist_convnE.
  rewrite psumr_neq0 /=; last by move=> *; rewrite mulr_ge0.
  case/hasP=> /= j jn eg0.
  apply/bigfcupP.
  exists j; first by rewrite jn /= (wpmulr_lgt0 _ eg0).
  by rewrite mem_finsupp gt_eqF // (wpmulr_rgt0 _ eg0).
case/bigfcupP=> j /andP [] ? ? /[!mem_finsupp] /prob_gt0 /= ?.
rewrite psumr_neq0 /=; last by move=> *; rewrite mulr_ge0.
by apply/hasP; exists j=> //; rewrite mulr_gt0.
Qed.

End fsdist_convn_lemmas.

(*HB.instance Definition _ a := isAffine.Build _ _ _ (af a).

Definition fsdist_eval (x : A) := fun D : R.-dist A => D x.

Lemma fsdist_eval_affine (x : A) : affine (fsdist_eval x).
Proof. by move=> a b p; rewrite /fsdist_eval fsdist_convE. Qed.

HB.instance Definition _ (x : A) :=
  isAffine.Build _ _ _ (fsdist_eval_affine x).*)

(* TODO*)

(*Section fsdist_ordered_convex_space.
Variable A : choiceType.
(*Definition fsdist_orderedConvMixin := @OrderedConvexSpace.Mixin R.-dist A.
NB: not used?*)
End fsdist_ordered_convex_space.*)

Section Convn_of_FSDist.
Local Open Scope classical_set_scope.
Context {R : realType}.
Variable C : convType R.

Definition Convn_of_fsdist (d : R.-dist C) : C :=
  <$>_(fdist_of_fs d) (fun x : finsupp d => fsval x).

Lemma ssum_seq_finsuppE'' (D : convType R) (f : C -> D) (d x : R.-dist C) :
  \ssum_(i : fdist_of_FSDist.D d) scalept (x (fsval i)) (S1 (f (fsval i))) =
  \ssum_(i <- finsupp d) scalept (x i) (S1 (f i)).
Proof.
by rewrite -(@big_seq_fsetE
               _ _ _ _ _ xpredT
               (fun i => scalept (x i) (S1 (f i)))).
Qed.

Lemma ssum_seq_finsuppE' (d x : R.-dist C) :
  \ssum_(i : fdist_of_FSDist.D d) scalept (x (fsval i)) (S1 (fsval i)) =
  \ssum_(i <- finsupp d) scalept (x i) (S1 i).
Proof.
by rewrite (ssum_seq_finsuppE'' idfun).
Qed.

Lemma ssum_seq_finsuppE (d : R.-dist C) :
  \ssum_i scalept (fdist_of_fs d i) (S1 (fsval i)) =
  \ssum_(i <- finsupp d) scalept (d i) (S1 i).
Proof.
under eq_bigr do rewrite fdist_of_fsE.
by rewrite ssum_seq_finsuppE'.
Qed.

Lemma ssum_widen_finsupp (x : R.-dist C) X :
  (finsupp x `<=` X)%fset ->
  \ssum_(i <- finsupp x) scalept (x i) (S1 i) =
  \ssum_(i <- X) scalept (x i) (S1 i).
Proof.
move=> xX.
rewrite [in RHS](bigID (fun i => i \in finsupp x)) /=.
have -> : (\ssum_(i <- X | i \notin finsupp x) scalept (x i) (S1 i)) = Zero
  by rewrite big1 //= => i Hi; rewrite fsfun_dflt // scale0pt.
rewrite addpt0 [in RHS]big_fset_condE /=.
suff H : finsupp x = [fset i | i in X & i \in finsupp x]%fset
  by rewrite [in LHS]H.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP=> c; rewrite !inE /=.
- by move=> cfx; move/fsubsetP/(_ c):xX ->.
- by case/andP.
Qed.

Lemma Convn_of_fsdist_affine : affine Convn_of_fsdist.
Proof.
move=> p x y.
have [->|pn0] := eqVneq p 0%:pr; first by rewrite !conv0.
have [->|pn1] := eqVneq p 1%:pr; first by rewrite !conv1.
have opn0 : (Prob.p p).~ != 0. by apply onem_neq0.
apply: (S1_inj R); rewrite affine_conv/= !S1_Convn_finType ssum_seq_finsuppE.
under [LHS]eq_bigr do rewrite fsdist_scalept_conv.
rewrite big_seq_fsetE big_scalept_conv_split /=.
rewrite 2!ssum_seq_finsuppE' 2!ssum_seq_finsuppE.
rewrite -(@ssum_widen_finsupp x); last exact/finsupp_conv_subr.
by rewrite -(@ssum_widen_finsupp y)//; exact/finsupp_conv_subl.
Qed.

HB.instance Definition _ := isAffine.Build _ _ _ _ Convn_of_fsdist_affine.

End Convn_of_FSDist.

Section lemmas_for_probability_monad_and_adjunction.
Context {R : realType}.
Local Open Scope fset_scope.

Lemma Convn_of_fsdistjoin (A : choiceType) (D : R.-dist (R.-dist A)) :
  Convn_of_fsdist D = fsdistjoin D.
Proof.
apply: fsdist_ext => a; rewrite -[LHS]Scaled1RK.
rewrite (S1_proj_Convn_finType [the {affine _ -> _} of fsdist_eval a]).
(* TODO: instantiate scaled as an Lmodule, and use big_scaler *)
rewrite big_scaleR fsdistjoinE big_seq_fsetE; apply eq_bigr => -[d dD] _ /=.
rewrite scaleR_scalept; last by rewrite FDist.ge0.
by rewrite fdist_of_fsE /= mul1r.
Qed.

Lemma Convn_of_fsdist1 (C : convType R) (x : C) : Convn_of_fsdist (fsdist1 x) = x.
Proof.
apply: (S1_inj R).
rewrite S1_Convn_finType /=.
rewrite (eq_bigr (fun=> S1 x)); last first.
  move=> i _; rewrite fdist_of_fsE fsdist1E -(@supp_fsdist1 R).
  rewrite fsvalP scale1pt /=; congr (S1 _).
  by case: i => i /=; rewrite supp_fsdist1 inE => /eqP.
by rewrite big_const (_ : #| _ | = 1%N) // -cardfE supp_fsdist1 cardfs1.
Qed.

Lemma Convn_of_fsdistmap (C D : convType R) (f : {affine C -> D})
    (d : R.-dist C) :
  f (Convn_of_fsdist d) = Convn_of_fsdist (fsdistmap f d).
Proof.
apply (S1_inj R) => /=.
rewrite S1_proj_Convn_finType // S1_Convn_finType.
set X := LHS.
under eq_bigr do rewrite fdist_of_fsE.
rewrite ssum_seq_finsuppE' supp_fsdistmap.
under eq_bigr do rewrite fsdistbindE.
rewrite big_seq; under eq_bigr=> y Hy.
- rewrite big_scaleptl';
    [| by rewrite scale0pt | by move=> j; rewrite mulr_ge0].
  under eq_bigr=> i do rewrite fsdist1E inE.
  over.
rewrite -big_seq exchange_big /=.
rewrite (@big_seq _ _ _ _ (finsupp d)).
under eq_bigr=> x Hx.
- rewrite (big_fsetD1 (f x)) /=; last by apply/imfsetP; exists x.
  rewrite eqxx mulr1.
  rewrite (@big_seq _ _ _ _ ([fset f x0 | x0 in finsupp d] `\ f x)).
  under eq_bigr=> y do [rewrite in_fsetD1=> /andP [] /negbTE -> Hy;
                        rewrite mulr0 scale0pt].
  rewrite big1 // addpt0.
  over.
rewrite /X.
under eq_bigr do rewrite fdist_of_fsE.
by rewrite ssum_seq_finsuppE'' big_seq.
Qed.

Section triangular_laws_left_convn.
Variable C : choiceType.

Local Notation S1 := (@S1 R).

Lemma triangular_laws_left0 (d : R.-dist C) :
  Convn_of_fsdist (fsdistmap (@fsdist1 _ C) d) = d.
Proof.
apply: fsdist_ext => x; apply (S1_inj R).
rewrite (S1_proj_Convn_finType [the {affine _ -> _} of fsdist_eval x]).
under eq_bigr do rewrite fdist_of_fsE.
rewrite (ssum_seq_finsuppE'' (fun i : R.-dist C => i x : R^o)).
rewrite supp_fsdistmap.
rewrite big_imfset /=; last by move=> ? ? ? ?; exact/fsdist1_inj.
under eq_bigr do rewrite fsdist1E inE fsdist1map.
have nx0 : \ssum_(i <- finsupp d `\ x)
    scalept (d i) (S1 (if x == i then 1 else 0 : R^o)) = scalept (d x).~ (S1 (0:R^o)).
  transitivity (scalept (\sum_(i <- finsupp d `\ x) (d i)) (S1 (0:R^o))).
    rewrite big_scaleptl' //; last by rewrite scale0pt.
    by apply: eq_fbigr => y /fsetD1P []; rewrite eq_sym=> /negbTE ->.
  by congr (_ _ _); rewrite fsdist_suppD1.
case/boolP : (x \in finsupp d) => xfd.
  rewrite (big_fsetD1 x) //= nx0 eqxx -convptE -affine_conv/=.
  by rewrite avgRE mulr0 addr0 mulr1.
by rewrite -(mem_fsetD1 xfd) nx0 fsfun_dflt // onem0 scale1pt.
Qed.

End triangular_laws_left_convn.

End lemmas_for_probability_monad_and_adjunction.

Import ereal topology esum measure probability.

Section probability_measure.

Section trivIset.
Import boolp classical_sets.
From mathcomp Require Import measure probability.
Local Open Scope classical_set_scope.
Context [T : Type] [I : eqType].
Variables (D : set I) (F : I -> set T)
          (disjF : trivIset D F).
Definition fibration_of_partition (x : T) : option I :=
  match asboolP ((\bigcup_(i in D) F i) x) with
  | ReflectT p => let (x0, _, _) := cid2 p in Some x0
  | ReflectF _ => None
  end.
Lemma fibration_of_partitionE i x : D i -> F i x -> fibration_of_partition x = Some i.
Proof.
move=> Di Fix.
rewrite /fibration_of_partition.
case: asboolP; last by have : ((\bigcup_(i0 in D) F i0) x) by exists i => //.
move=> ?; case: cid2 => j Dj Fjx.
congr Some; apply: contrapT; move/eqP => ji.
move: disjF => /trivIsetP /(_ j i Dj Di ji).
apply/eqP/set0P.
by exists x.
Qed.
(*
Definition fibration_of_partition' : option I.
Proof.
case/asboolP : ((\bigcup_(i in D) F i) x).
- case/cid2 => i _ _; exact (Some i).
- move=> *; exact None.
Defined.
Eval hnf in fibration_of_partition'.
(*
     = match asboolP ((\bigcup_(i in D) F i) x) with
       | ReflectT _ p => let (x0, _, _) := cid2 p in Some x0
       | ReflectF _ _ => None
       end
     : option I
*)
*)
Lemma in_fibration_of_partition (x : T) :
  if fibration_of_partition x is Some i then x \in F i else true.
Proof.
rewrite /fibration_of_partition /=.
case/asboolP: ((\bigcup_(i in D) F i) x) => //=.
case/cid2 => *.
by rewrite inE.
Qed.
End trivIset.

Variable disp : measure_display.
Variable T : measurableType disp.
Local Open Scope ring_scope.
Import GRing.Theory.
Variable R : realType.
Variable d : {fsfun T -> R with 0}.
Hypothesis Hd : all (fun x => 0 < d x) (finsupp d) &&
                \sum_(a <- finsupp d) d a == 1.

Lemma d0' : forall (x : T), x \in finsupp d -> 0 < d x.
Proof. by move => x xfsd; case/andP: Hd => /allP /(_ x xfsd). Qed.

Lemma d0 (x : T) : 0 <= d x.
Proof.
case/boolP: (x \in finsupp d); first by move/d0'/ltW.
by move/fsfun_dflt ->; exact: lexx.
Qed.

Lemma d1 : \sum_(a <- finsupp d) d a = 1.
Proof. by apply/eqP; case/andP: Hd. Qed.

Definition P := fun (A : set T) => (\esum_(k in A) (d k)%:E)%E.

Lemma P_fssum' A : P A = \esum_(k in A `&` [set` finsupp d]) (d k)%:E.
Proof.
rewrite /P esum_mkcondr.
apply eq_esum => i _.
rewrite mem_setE.
by case: finsuppP.
Qed.

Lemma P_fssum A : P A = (\sum_(i \in A `&` [set` finsupp d]) (d i)%:E)%E.
Proof.
rewrite P_fssum'.
by rewrite esum_fset; [| exact: finite_setIr | by move=> *; exact: d0].
Qed.

Lemma P_fin {X} : P X \is a fin_num.
Proof. by rewrite P_fssum sumEFin. Qed.

Lemma P_set0 : P set0 = 0%E.
Proof. by rewrite /P esum_set0. Qed.

Lemma P_ge0 X : (0 <= P X)%E.
Proof.
apply esum_ge0=> x _.
rewrite lee_fin.
exact: d0.
Qed.

Lemma P_semi_sigma_additive : semi_sigma_additive P.
Proof.
(* TODO: clean *)
move=> F mFi disjF mUF.
move=> X /=.
rewrite /nbhs /=.
rewrite -[Y in ereal_nbhs Y]fineK ?P_fin //=.
case => x /= xpos.
rewrite /ball_ => xball.
rewrite /nbhs /= /nbhs /=.
rewrite /eventually /=.
rewrite /filter_from /=.
suff: exists N, forall k, (N <= k)%nat ->
    P (\bigcup_n F n) = P (\bigcup_(i < k) F i).
  case=> N HN.
  exists N => //.
  move=> j /= ij.
  rewrite -[y in X y]fineK; last by apply/sum_fin_numP => *; exact: P_fin.
  apply: xball => /=.
  rewrite [X in X < x](_ : _ = 0) //.
  apply/eqP.
  rewrite normr_eq0 subr_eq0.
  apply/eqP; congr fine.
  rewrite (HN j) // /P.
  rewrite esum_bigcupT //; last exact: d0.
  rewrite esum_fset //; last by move=> *; apply esum_ge0 => *; exact: d0.
  rewrite big_mkord.
  by rewrite -fsbigop.fsbig_ord.
rewrite P_fssum.
set f := fun t =>
           if fibration_of_partition [set: nat] F t is Some i then i else 0%N.
exists (\max_(t <- finsupp d | `[< (\bigcup_i F i)%classic t >]) f t).+1.
move=> k Nk.
rewrite P_fssum.
suff : (\bigcup_n F n `&` [set` finsupp d] = \bigcup_(i < k) F i `&` [set` finsupp d])%classic by move ->.
rewrite (bigcupID `I_k) setIUl 2!setTI -[RHS]setU0.
congr setU.
rewrite setI_bigcupl bigcup0 // => i.
rewrite /mkset /=.
apply: contra_notP.
case/eqP/set0P => t [] Fit tfd.
apply:(leq_ltn_trans _ Nk).
suff-> : i = f t.
  apply bigop.leq_bigmax_seq => //.
  by apply/asboolP; exists i .
rewrite /f /=.
by rewrite (fibration_of_partitionE disjF _ Fit).
Qed.

HB.instance Definition _ :=
  isMeasure.Build disp T _ P P_set0 P_ge0 P_semi_sigma_additive.

Lemma P_is_probability : P [set: _] = 1%E.
Proof.
rewrite P_fssum.
rewrite fsbigop.fsbig_finite /=; last exact: finite_setIr.
rewrite setTI set_fsetK.
by rewrite sumEFin d1.
Qed.

HB.instance Definition _ := isProbability.Build disp T _ P P_is_probability.

End probability_measure.
