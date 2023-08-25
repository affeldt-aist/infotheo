(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import finmap.
From mathcomp Require boolp.
Require Import Reals.
From mathcomp Require Import Rstruct.
Require Import ssrR realType_ext Reals_ext ssr_ext ssralg_ext bigop_ext Rbigop fdist.
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
(*                      where A is a choiceType (see fdist.v for              *)
(*                      distributions over a finType)                         *)
(*           fsdist1 == unit of the probability monad                         *)
(*        fsdistbind == bind of the probability monad, notation >>=, scope    *)
(*                      fsdist_scope (delimiter: fsdist)                      *)
(*         fsdistmap == map of the probability monad                          *)
(* FSDist_choiceType == instance of choiceType with finitely-supported        *)
(*                      distributions                                         *)
(*      fsdist_convn == of type {fdist 'I_n} -> ('I_n -> {dist A}) -> {dist A}*)
(*                      convex combination of n distributions                 *)
(*       fsdist_conv == of type prob -> {dist A} -> {dist A} -> {dist A}      *)
(*                      convex combination of two distributions, notation     *)
(*                       . <| . |> . (fsdist_scope)                           *)
(*                                                                            *)
(* Free convex spaces in terms of finitely-supported distributions:           *)
(*  {dist A} and @fsdist_conv A are used to form an instance of convType,     *)
(*  this shows that finitely-supported distributions over a choiceType form a *)
(*  convex space                                                              *)
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

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.
Local Open Scope fset_scope.
Local Open Scope fdist_scope.

Lemma fdist_Rgt0 (A: finType) (d : real_realType.-fdist A) a :
  (d a != 0) <-> (0 < d a)%coqR.
Proof. by rewrite fdist_gt0; split=> /RltP. Qed.
Lemma fdist_Rge0 (A: finType) (d : real_realType.-fdist A) a :
  0 <= d a.
Proof. by apply/RleP; rewrite FDist.ge0. Qed.

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
Variable A : choiceType.

Record t := mk {
  f :> {fsfun A -> R with 0} ;
  _ : all (fun x => 0 <b f x) (finsupp f) &&
      \sum_(a <- finsupp f) f a == 1}.

Lemma ge0 (d : t) a : 0 <= d a.
Proof.
case: d => /= [f /andP[/allP f0 _]].
have [/f0/ltRP/ltRW|/fsfun_dflt->] := boolP (a \in finsupp f); first exact.
exact/leRR.
Qed.

Lemma ge0' (d : t) a : (0 <= d a)%O.
Proof. by apply/RleP/ge0. Qed.

Lemma gt0 (d : t) a : a \in finsupp d -> 0 < d a.
Proof.
by rewrite mem_finsupp => da; apply/ltRP; rewrite lt0R da; exact/leRP/ge0.
Qed.

Lemma f1 (d : t) : \sum_(a <- finsupp d) d a = 1.
Proof. by case: d => f /= /andP[_ /eqP]. Qed.

Lemma le1 (d : t) a : d a <= 1.
Proof.
have [ad|?] := boolP (a \in finsupp d); last by rewrite fsfun_dflt.
rewrite -(f1 d) (big_fsetD1 _ ad)/=; apply/leR_addl.
by apply sumR_ge0 => ? _; exact: ge0.
Qed.

Lemma le1' (d : t) a : (d a <= 1)%O.
Proof. by apply/RleP/le1. Qed.

Obligation Tactic := idtac.

Program Definition make (f : {fsfun A -> R with 0})
  (H0 : forall a, a \in finsupp f -> 0 < f a)
  (H1 : \sum_(a <- finsupp f) f a = 1) : t := @mk f _.
Next Obligation.
by move=> f H0 ->; rewrite eqxx andbT; apply/allP => a /H0/ltRP.
Qed.

End fsdist.
End FSDist.
Notation fsdist := FSDist.t.
Coercion FSDist.f : FSDist.t >-> fsfun.

Global Hint Resolve FSDist.ge0 : core.

Section FSDist_canonical.
Variable A : choiceType.
Canonical FSDist_subType := Eval hnf in [subType for @FSDist.f A].
Definition FSDist_eqMixin := [eqMixin of fsdist A by <:].
Canonical FSDist_eqType := Eval hnf in EqType _ FSDist_eqMixin.
Definition FSDist_choiceMixin := [choiceMixin of fsdist A by <:].
Canonical FSDist_choiceType := Eval hnf in ChoiceType _ FSDist_choiceMixin.
End FSDist_canonical.

Definition FSDist_to_Type (A : choiceType) :=
  fun phT : phant (Choice.sort A) => fsdist A.
Local Notation "{ 'dist' T }" := (FSDist_to_Type (Phant T)).

Section fsdist_prop.
Variable A : choiceType.

Lemma fsdist_ext (d d' : {dist A}) : (forall x, d x = d' x) -> d = d'.
Proof. by move=> ?; exact/val_inj/fsfunP. Qed.

Lemma fsdist_supp_neq0 (d : {dist A}) : finsupp d != fset0.
Proof.
apply/eqP => d0.
by move: (FSDist.f1 d); rewrite d0 big_nil => /esym; exact: R1_neq_R0.
Qed.

End fsdist_prop.

Section fsdist1.
Variables (A : choiceType) (a : A).

Let D := [fset a].

Let f : {fsfun A -> R with 0} := [fsfun b in D => 1 | 0].

Let suppf : finsupp f = D.
Proof.
apply/fsetP => b; rewrite mem_finsupp /f fsfunE inE.
by case: ifPn => ba; [exact/gtR_eqF | by rewrite eqxx].
Qed.

Let f0 b : b \in finsupp f -> 0 < f b.
Proof. by rewrite mem_finsupp fsfunE inE; case: ifPn => //; rewrite eqxx. Qed.

Let f1 : \sum_(b <- finsupp f) f b = 1.
Proof. by rewrite suppf big_seq_fset1 /f fsfunE inE eqxx. Qed.

Definition fsdist1 : {dist A} := locked (FSDist.make f0 f1).

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

Lemma fsdist1_inj (C : choiceType) : injective (@fsdist1 C).
Proof.
move=> a b /eqP ab; apply/eqP; apply: contraTT ab => ab.
apply/eqP => /(congr1 (fun x : FSDist.t _ => x a)).
rewrite !fsdist1E !inE eqxx (negbTE ab); exact: R1_neq_R0.
Qed.

Section fsdistbind.
Variables (A B : choiceType) (p : {dist A}) (g : A -> {dist B}).

Let D := \bigcup_(d <- g @` finsupp p) finsupp d.

Let f : {fsfun B -> R with 0} :=
  [fsfun b in D => \sum_(a <- finsupp p) p a * (g a) b | 0].

Let f0 b : b \in finsupp f -> 0 < f b.
Proof.
rewrite mem_finsupp fsfunE; case: ifPn => [_ /eqP/nesym ?|]; last by rewrite eqxx.
by rewrite ltR_neqAle; split => //; apply sumR_ge0 => a _; exact/mulR_ge0.
Qed.

Let f1 : \sum_(b <- finsupp f) f b = 1.
Proof.
rewrite {2}/f.
under eq_bigr do rewrite fsfunE.
rewrite -big_mkcond /= exchange_big /=.
rewrite -[RHS](FSDist.f1 p); apply eq_bigr => a _.
have [->|pa0] := eqVneq (p a) 0%coqR.
  by rewrite big1 // => *; rewrite mul0R.
rewrite -big_distrr /= (_ : \sum_(_ <- _ | _) _ = 1) ?mulR1 //.
rewrite (bigID (mem (finsupp (g a)))) /=.
rewrite [X in (_ + X)%coqR = _]big1 ?addR0; last first.
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
apply: contra gab0 => /eqP/psumR_seq_eq0P.
rewrite fset_uniq => /(_ isT) H.
suff : p a * g a b = 0.
 by rewrite mulR_eq0 => -[/eqP|->//]; rewrite (negbTE pa0).
apply/H; rewrite ?mem_finsupp // => a0 _; exact/mulR_ge0.
Qed.

Definition fsdistbind : {dist B} := locked (FSDist.make f0 f1).

Lemma fsdistbindEcond x :
  fsdistbind x = if x \in D then \sum_(a <- finsupp p) p a * (g a) x else 0.
Proof. by rewrite /fsdistbind; unlock; rewrite fsfunE. Qed.

Lemma fsdistbindE x : fsdistbind x = \sum_(a <- finsupp p) p a * (g a) x.
Proof.
rewrite fsdistbindEcond.
case: ifPn => // aD.
apply/eqP; move: aD; apply: contraLR.
rewrite eq_sym negbK sumR_neq0; last by move=> ?; exact: mulR_ge0.
case => i [] suppi pg0.
apply/bigfcupP; exists (g i).
- by rewrite in_imfset.
- by rewrite mem_finsupp; apply/gtR_eqF/(pmulR_rgt0' pg0).
Qed.

Lemma fsdistbindEwiden S x :
  finsupp p `<=` S -> fsdistbind x = \sum_(a <- S) p a * (g a) x.
Proof.
move=> suppS; rewrite fsdistbindE (big_fset_incl _ suppS) //.
by move=> a2 Ha2; rewrite memNfinsupp => /eqP ->; rewrite mul0R.
Qed.

Lemma supp_fsdistbind : finsupp fsdistbind = D.
Proof.
apply/fsetP => b; rewrite mem_finsupp; apply/idP/idP => [|].
  by rewrite fsdistbindEcond; case: ifPn => //; rewrite eqxx.
case/bigfcupP => dB.
rewrite andbT => /imfsetP[a] /= ap ->{dB} bga.
rewrite fsdistbindE.
apply/eqP => H.
have : (p a) * (g a) b <> 0.
  by rewrite mulR_eq0 => -[]; apply/eqP; rewrite -mem_finsupp.
apply.
by move/psumR_seq_eq0P : H; apply => // b0 _; exact/mulR_ge0.
Qed.

End fsdistbind.

Declare Scope fsdist_scope.
Delimit Scope fsdist_scope with fsdist.
Reserved Notation "m >>= f" (at level 49).
Notation "m >>= f" := (fsdistbind m f) : fsdist_scope.
Local Open Scope fsdist_scope.

Lemma fsdist1bind (A B : choiceType) (a : A) (f : A -> {dist B}) :
  fsdist1 a >>= f = f a.
Proof.
apply/val_inj/val_inj => /=; congr fmap_of_fsfun; apply/fsfunP => b.
by rewrite fsdistbindE supp_fsdist1 big_seq_fset1 fsdist1xx mul1R.
Qed.

Lemma fsdistbind1 (A : choiceType) (p : {dist A}) : p >>= @fsdist1 A = p.
Proof.
apply/val_inj/val_inj => /=; congr fmap_of_fsfun; apply/fsfunP => b.
rewrite fsdistbindEcond; case: ifPn => [|H].
  case/bigfcupP => /= d; rewrite andbT.
  case/imfsetP => /= a ap ->{d}.
  rewrite supp_fsdist1 inE => /eqP ->{b}.
  rewrite (big_fsetD1 a) //= fsdist1xx mulR1 big1_fset ?addR0 // => a0.
  by rewrite !inE => /andP[aa0] a0p _; rewrite fsdist10 ?mulR0// eq_sym.
have [->//|pb0] := eqVneq (p b) 0%coqR.
case/bigfcupP : H.
exists (fsdist1 b); last by rewrite supp_fsdist1 inE.
by rewrite andbT; apply/imfsetP; exists b => //=; rewrite mem_finsupp.
Qed.

Lemma fsdistbindA (A B C : choiceType) (m : {dist A}) (f : A -> {dist B})
    (g : B -> {dist C}) :
  (m >>= f) >>= g = m >>= (fun x => f x >>= g).
Proof.
apply/val_inj/val_inj => /=; congr fmap_of_fsfun; apply/fsfunP => c.
rewrite !fsdistbindE.
under eq_bigr do rewrite fsdistbindE big_distrl.
under [in RHS]eq_bigr do
  (rewrite fsdistbindE big_distrr /=; under eq_bigr do rewrite mulRA).
rewrite exchange_big /= !big_seq; apply: eq_bigr => a a_m.
rewrite supp_fsdistbind; apply/esym/big_fset_incl => [| b].
  apply/fsubsetP => ? ?;  apply/bigfcupP => /=.
  by exists (f a) => //; rewrite andbT in_imfset.
case/bigfcupP => ?; rewrite andbT; case/imfsetP => ? /= ? -> ?.
rewrite mem_finsupp negbK => /eqP ->.
by rewrite mulR0 mul0R.
Qed.

Definition fsdistmap (A B : choiceType) (f : A -> B) (d : {dist A}) : {dist B} :=
  d >>= (fun a => fsdist1 (f a)).

Lemma fsdistmap_id (A : choiceType) : fsdistmap (@id A) = @id {dist A}.
Proof. by rewrite boolp.funeqE => a; rewrite /fsdistmap fsdistbind1. Qed.

Lemma fsdistmap_comp (A B C : choiceType) (g : B -> C) (h : A -> B) :
  fsdistmap (g \o h) = fsdistmap g \o fsdistmap h.
Proof.
rewrite boolp.funeqE => d; rewrite /fsdistmap /= fsdistbindA; congr (_ >>= _).
by rewrite boolp.funeqE => a; rewrite fsdist1bind.
Qed.

Definition fsdistmapE (A B : choiceType) (f : A -> B) (d : {dist A}) b :
  fsdistmap f d b = \sum_(a <- finsupp d | f a == b) d a.
Proof.
rewrite {1}/fsdistmap [in LHS]fsdistbindE (bigID (fun a => f a == b)) /=.
rewrite [X in (_ + X)%R = _](_ : _ = 0) ?addR0; last first.
  by rewrite big1 // => a fab; rewrite fsdist10 ?mulR0// eq_sym.
by apply eq_bigr => a /eqP ->; rewrite fsdist1xx mulR1.
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

Lemma fsdist1map (C : choiceType) (d : {dist C}) (c : C) :
  fsdistmap (@fsdist1 C) d (fsdist1 c) = d c.
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

Local Open Scope reals_ext_scope.
Lemma fsdist_suppD1 (C : choiceType) (d : {dist C}) (x : C) :
  \sum_(i <- finsupp d `\ x) d i = (d x).~.
Proof.
rewrite -subR_eq0 subR_onem.
case/boolP: (x \in finsupp d)=> xfd.
  by rewrite addRC -big_fsetD1 //= FSDist.f1 subRR.
by rewrite fsfun_dflt // mem_fsetD1 // FSDist.f1 addR0 subRR.
Qed.
Local Close Scope reals_ext_scope.

Definition FSDist_prob (C : choiceType) (d : {dist C}) (x : C) : {prob R} :=
  Eval hnf in Prob.mk_ (andb_true_intro (conj (FSDist.ge0' d x) (FSDist.le1' d x))).
Canonical FSDist_prob.

Definition fsdistjoin A (D : {dist (FSDist_choiceType A)}) : {dist A} :=
  D >>= ssrfun.id.

Lemma fsdistjoinE A (D : {dist (FSDist_choiceType A)}) x :
  fsdistjoin D x = \sum_(d <- finsupp D) D d * d x.
Proof. by rewrite /fsdistjoin fsdistbindE. Qed.

Lemma fsdistjoin1 (A : choiceType) (D : {dist (FSDist_choiceType A)}) :
  fsdistjoin (fsdist1 D) = D.
Proof.
apply/fsdist_ext => d.
by rewrite fsdistjoinE supp_fsdist1 big_imfset // big_seq1 fsdist1xx mul1R.
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
Variable (A : finType) (P : real_realType.-fdist A).

Let D := [fset a0 : A | P a0 != 0].
Definition f : {fsfun A -> R with 0} := [fsfun a in D => P a | 0].

Let f0 a : a \in finsupp f -> 0 < f a.
Proof.
rewrite fsfunE mem_finsupp /f fsfunE.
case: ifPn => [_|]; by [rewrite fdist_Rgt0 | rewrite eqxx].
Qed.

Let f1 : \sum_(a <- finsupp f) f a = 1.
Proof.
rewrite -[RHS](FDist.f1 P) [in RHS](bigID (mem (finsupp f))) /=.
rewrite [in X in _ = (_ + X)%coqR]big1 ?addR0; last first.
  move=> a; rewrite memNfinsupp fsfunE !inE /=.
  by case: ifPn => [_ /eqP //|]; rewrite negbK => /eqP.
rewrite (@eq_fbigr _ _ _ _ _ _ _ P) /=; last first.
  move=> a; rewrite mem_finsupp fsfunE !inE /=; case: ifPn => //.
  by rewrite eqxx.
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
Lemma f0' b : (0 <= f b)%O. Proof. (*TODO: *) Admitted.

Definition d : real_realType.-fdist D := locked (FDist.make f0' f1).
End def.
Module Exports.
Notation fdist_of_fs := d.
End Exports.
End fdist_of_FSDist.
Export fdist_of_FSDist.Exports.

Section fdist_of_FSDist_lemmas.
Variable (A : choiceType) (d : {dist A}).

Lemma fdist_of_fsE i : fdist_of_fs d i = d (fsval i).
Proof. by rewrite /fdist_of_fs; unlock; rewrite ffunE. Qed.

Lemma fdist_of_FSDistDE : fdist_of_FSDist.D d = [finType of finsupp d].
Proof. by []. Qed.

End fdist_of_FSDist_lemmas.

Module fdist_of_finFSDist.
Section def.
Variable (A : finType) (P : {dist A}).
Definition f := [ffun d : A => P d].

Lemma f0 b : 0 <= f b. Proof. by rewrite ffunE. Qed.

Lemma f0' b : (0 <= f b)%O. Proof. exact/RleP/f0. Qed.

Lemma f1 : \sum_(b in A) f b = 1.
Proof.
rewrite -(FSDist.f1 P) (bigID (fun x => x \in finsupp P)) /=.
rewrite [X in (_ + X = _)%coqR](_ : _ = 0) ?addR0.
  by rewrite big_uniq /= ?fset_uniq //; apply eq_bigr => i _; rewrite ffunE.
by rewrite big1 // => a; rewrite mem_finsupp negbK ffunE => /eqP.
Qed.

Definition d : real_realType.-fdist A := locked (FDist.make f0' f1).

Lemma dE a : d a = P a.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.

End def.
Module Exports.
Notation fdist_of_finfs := d.
End Exports.
End fdist_of_finFSDist.
Export fdist_of_finFSDist.Exports.

Section fsdist_convn.
Local Open Scope fdist_scope.
Variables (A : choiceType) (n : nat) (e : real_realType.-fdist 'I_n) (g : 'I_n -> {dist A}).

Definition fsdist_convn_supp : {fset A} :=
  \big[fsetU/fset0]_(i < n | 0 <b e i) finsupp (g i).

Local Notation D := fsdist_convn_supp.

Let f := [fsfun a in D => \sum_(i < n) e i * g i a | 0].

Let supp : finsupp f = D.
Proof.
apply/fsetP => a; apply/idP/idP => [|].
  by rewrite mem_finsupp /f fsfunE; case: ifPn => //; rewrite eqxx.
rewrite mem_finsupp fsfunE => aD.
rewrite aD.
case/bigfcupP : aD => /= i.
rewrite mem_index_enum /= => /ltRP ei0.
rewrite mem_finsupp => gia0.
apply: contra gia0 => /eqP H; apply/eqP.
rewrite -(@eqR_mul2l (e i)) ?mulR0; last exact/eqP/gtR_eqF.
by move/psumR_eq0P : H; apply => //= j _; exact/mulR_ge0.
Qed.

Let f0 a : a \in finsupp f -> 0 < f a.
Proof.
rewrite mem_finsupp fsfunE; case: ifPn => [_ ?|]; last by rewrite eqxx.
rewrite ltR_neqAle; split; first exact/nesym/eqP.
by apply/sumR_ge0 => i _; exact/mulR_ge0.
Qed.

Let f1 : \sum_(a <- finsupp f) f a = 1.
Proof.
under eq_big_seq.
  by move=> b; rewrite supp => bD; rewrite fsfunE bD; over.
rewrite exchange_big /= -[RHS](FDist.f1 e) /=; apply eq_bigr => i _.
rewrite -big_distrr /=.
have [-> | ei0] := eqVneq (e i) 0%coqR; first by rewrite mul0R.
rewrite -(@big_fset_incl _ _ _ _ (finsupp (g i))).
- by rewrite FSDist.f1 mulR1.
- by rewrite supp /D bigfcup_sup //; exact/ltRP/fdist_Rgt0.
- by move=> a _; rewrite memNfinsupp => /eqP.
Qed.

Definition fsdist_convn : {dist A} := locked (FSDist.make f0 f1).

Lemma fsdist_convnE a :
  fsdist_convn a = [fsfun a in D => \sum_(i < n) e i * g i a | 0] a.
Proof. by rewrite /fsdist_convn; unlock; rewrite fsfunE. Qed.

End fsdist_convn.

Section fsdist_conv.
Variables (A : choiceType) (p : {prob R}) (d1 d2 : {dist A}).

Definition fsdist_conv : {dist A} := locked
  (fsdist_convn (fdistI2 p) (fun i => if i == ord0 then d1 else d2)).
Local Open Scope reals_ext_scope.

Lemma fsdist_convE a : (fsdist_conv a = Prob.p p * d1 a + p.~ * d2 a)%coqR.
Proof.
rewrite /fsdist_conv; unlock => /=; rewrite fsdist_convnE fsfunE.
case: ifPn => [?|H].
  rewrite !big_ord_recl big_ord0 /= addR0 !fdistI2E.
  by rewrite eqxx eq_sym (negbTE (neq_lift _ _)).
have [p0|p0] := eqVneq (Prob.p p : R) 0%coqR.
  rewrite p0 mul0R add0R onem0 mul1R.
  apply/esym/eqP; rewrite -memNfinsupp.
  apply: contra H => H.
  rewrite (_ : p = R0%:pr) //; last exact/val_inj.
  rewrite fdistI20 (_ : Ordinal _ = @ord_max 1); last exact/val_inj.
  (* TODO: generalize *)
  suff : fsdist_convn_supp (fdist1 ord_max)
    (fun i : 'I_2 => if i == ord0 then d1 else d2) = finsupp d2 by move=> ->.
  rewrite /fsdist_convn_supp; apply/fsetP => a0; apply/bigfcupP/idP.
    case => /= i; rewrite mem_index_enum /= fdist1E.
    by case/orP : (ord2 i) => /eqP -> // /ltRP/ltRR.
  move=> a0d2.
  by exists ord_max => //=; rewrite mem_index_enum /= fdist1xx; exact/ltRP.
have d1a0 : d1 a = 0.
  apply/eqP; rewrite -memNfinsupp.
  apply: contra H => H.
  rewrite /fsdist_convn_supp; apply/bigfcupP; exists ord0; last by rewrite eqxx.
  by rewrite mem_index_enum /= fdistI2E eqxx; exact/ltRP/probR_gt0.
rewrite d1a0 mulR0 add0R.
have [p1|p1] := eqVneq (Prob.p p : R) 1%coqR; first by rewrite p1 onem1 mul0R.
suff : d2 a = 0 by move=> ->; rewrite mulR0.
apply/eqP; rewrite -memNfinsupp.
apply: contra H => H.
rewrite /fsdist_convn_supp; apply/bigfcupP; exists (lift ord0 ord0).
rewrite mem_index_enum /= fdistI2E eq_sym (negbTE (neq_lift _ _)).
  exact/ltRP/onem_gt0/probR_lt1.
by rewrite eq_sym (negbTE (neq_lift _ _)).
Qed.

End fsdist_conv.

Notation "x <| p |> y" := (fsdist_conv p x y) : fsdist_scope.

Section fsdist_conv_prop.
Variables (A : choiceType).
Implicit Types a b c : {dist A}.
Local Open Scope reals_ext_scope.

Lemma finsupp_conv_subr (a b : {dist A}) (p : {prob R}) :
  p != R0%:pr -> finsupp a `<=` finsupp (a <|p|> b).
Proof.
move=> p0; apply/fsubsetP => a1.
rewrite !mem_finsupp => aa1.
rewrite fsdist_convE.
apply: contra aa1 => /eqP.
rewrite paddR_eq0; [move=> [+ _]|exact/mulR_ge0|exact/mulR_ge0].
rewrite mulR_eq0 => -[p0'|/eqP //].
exfalso.
move/eqP : p0; apply.
by apply/val_inj; rewrite /= p0'.
Qed.

Let conv0 (mx my : {dist A}) : mx <| 0%:pr |> my = my.
(*Let conv0 (mx my : {dist A}) : mx <| R0%:pr |> my = my.*)

Proof.
by apply/fsdist_ext => a; rewrite fsdist_convE /= mul0R add0R onem0 mul1R.
Qed.

Let conv1 (mx my : {dist A}) : mx <| R1%:pr |> my = mx.
Proof.
by apply/fsdist_ext => a; rewrite fsdist_convE /= mul1R onem1 mul0R addR0.
Qed.

Let convmm p : idempotent (fun x y => x <| p |> y : {dist A}).
Proof.
by move=> d; apply/fsdist_ext => a; rewrite fsdist_convE -mulRDl onemKC mul1R.
Qed.

Let convC (p : {prob R}) (mx my : {dist A}) : mx <| p |> my = my <| p.~%:pr |> mx.
Proof.
by apply/fsdist_ext => a; rewrite 2!fsdist_convE /= onemK addRC.
Qed.

Definition fsdist_convA (p q r s : {prob R}) (mx my mz : {dist A}) :
  Prob.p p = Prob.p r * Prob.p s :> R /\ s.~ = p.~ * q.~ ->
  mx <| p |> (my <| q |> mz) = (mx <| r |> my) <| s |> mz.
Proof.
move=> [Hp Hs]; apply/fsdist_ext => a.
rewrite !fsdist_convE [in RHS]mulRDr (@mulRCA _ (Prob.p r)) (@mulRA (Prob.p r)) -Hp -addRA; congr (_ + _)%coqR.
rewrite mulRDr (@mulRA p.~ q.~) -Hs; congr (_ + _)%coqR.
rewrite !mulRA; congr (_ * _)%coqR.
rewrite -p_of_rsE in Hp.
move/(congr1 (@onem _)) : Hs; rewrite onemK => Hs.
rewrite -s_of_pqE in Hs.
have [r0|r0] := eqVneq r R0%:pr.
  rewrite r0 /= onem0 mulR1 Hs s_of_pqE.
  by rewrite Hp p_of_rsE r0 /= mul0R onem0 2!mul1R onemK.
have [s0|s0] := eqVneq s R0%:pr.
  rewrite Hp p_of_rsE s0 /= mulR0 onem0 mul0R mul1R.
  by move: Hs; rewrite s_of_pqE Hp p_of_rsE s0 /= mulR0 onem0 mul1R onemK.
rewrite p_of_rsE in Hp.
rewrite s_of_pqE in Hs.
move/(congr1 (@onem _)) : Hs; rewrite onemK => Hs.
move: (@r_of_pq_is_r p q r s r0 s0 Hp Hs) => <-.
rewrite pq_is_rs mulRC; congr (_ * _)%coqR.
by rewrite s_of_pqE -Hs onemK.
Qed.

(* TODO: move the glue lemma to convex *)
Let convA (p q : {prob R}) (a b c : {dist A}) :
  a <| p |> (b <| q |> c) = (a <| r_of_pq p q |> b) <| s_of_pq p q |> c.
Proof.
rewrite (fsdist_convA (r := r_of_pq p q) (s := s_of_pq p q)) //.
rewrite {2}s_of_pqE onemK; split => //.
have [s0|s0] := eqVneq (s_of_pq p q) R0%:pr.
- rewrite s0 mulR0; apply/eqP; move/eqP: s0.
  by apply: contraTT => /(s_of_gt0 q); rewrite probR_gt0.
- by rewrite -p_is_rs.
Qed.

HB.instance Definition _ :=
  @isConvexSpace.Build (FSDist.t _) (Choice.class _) (@fsdist_conv A)
  conv1 convmm convC convA.

Lemma finsupp_conv_subl (a b : {dist A}) (p : {prob R}) :
  p != R1%:pr -> finsupp b `<=` finsupp (a <|p|> b).
Proof.
move=> p1; rewrite convC; apply: finsupp_conv_subr.
apply: contra p1 => /eqP/(congr1 val) /= /onem_eq0 p1.
exact/eqP/val_inj.
Qed.

Lemma fsdist_conv_bind_left_distr (B : choiceType) (p : {prob R}) a b (f : A -> {dist B}) :
  (a <| p |> b) >>= f = (a >>= f) <| p |> (b >>= f).
Proof.
apply/fsdist_ext => b0 /=; rewrite fsdistbindE fsdist_convE.
have [->|p0] := eqVneq p R0%:pr.
  by rewrite conv0 mul0R add0R onem0 mul1R fsdistbindE.
have [->|p1] := eqVneq p R1%:pr.
  by rewrite conv1 mul1R onem1 mul0R addR0 fsdistbindE.

under eq_bigr.
  by move=> a1 _; rewrite fsdist_convE (@mulRDl _ _ (f a1 b0)) -!mulRA; over.
rewrite big_split /= -2!big_distrr /= -!fsdistbindEwiden //.
  by rewrite finsupp_conv_subl.
by rewrite finsupp_conv_subr.
Qed.

End fsdist_conv_prop.

Lemma fsdistmap_affine (A B : choiceType) (f : A -> B) : affine (fsdistmap f).
Proof. by move=> ? ? ?; rewrite /fsdistmap fsdist_conv_bind_left_distr. Qed.

HB.instance Definition _ (A B : choiceType) (f : A -> B) :=
  isAffine.Build _ _ _ (fsdistmap_affine f).

Definition FSDist_to_convType (A : choiceType) :=
  fun phT : phant (Choice.sort A) => conv_choiceType [the convType of FSDist.t A].
Notation "{ 'dist' T }" := (FSDist_to_convType (Phant T)) : proba_scope.

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope convex_scope.

Lemma supp_fsdist_conv (C : choiceType) p (p0 : p != R0%:pr) (p1 : p != R1%:pr)
  (d e : {dist C}) :
  finsupp (d <|p|> e) = (finsupp d `|` finsupp e)%fset.
Proof.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP => j;
  rewrite !mem_finsupp !fsdist_convE inE.
  move=> H; rewrite 2!mem_finsupp; apply/orP/paddR_neq0 => //.
  apply: contra H => /eqP/paddR_eq0.
  move => /(_ (FSDist.ge0 _ _ ))/(_ (FSDist.ge0 _ _)) [-> ->].
  by rewrite 2!mulR0 addR0.
move/probR_gt0 in p0.
move: p1 => /onem_neq0 /probR_gt0 /= p1.
by rewrite 2!mem_finsupp => /orP[dj0|ej0]; apply/gtR_eqF;
  [apply/addR_gt0wl; last exact/mulR_ge0;
   apply/mulR_gt0 => //; apply/ltR_neqAle; split => //; exact/nesym/eqP |
   apply/addR_gt0wr; first exact/mulR_ge0;
   apply/mulR_gt0 => //; apply/ltR_neqAle; split => //; exact/nesym/eqP].
Qed.

Section misc_scaled.
Local Open Scope R_scope.

Lemma fsdist_scalept_conv (C : convType) (x y : {dist C}) (p : {prob R}) (i : C) :
  scalept ((x <|p|> y) i) (S1 i) = scalept (x i) (S1 i) <|p|> scalept (y i) (S1 i).
Proof. by rewrite fsdist_convE scalept_conv. Qed.

End misc_scaled.

Section FSDist_convex_space.
Variable A : choiceType.

Let f a := fun x : {dist A} => finmap.fun_of_fsfun x a.

Let af a : affine (f a).
Proof. by move=> p x y; rewrite /f /= fsdist_convE. Qed.

HB.instance Definition _ a := isAffine.Build _ _ _ (af a).

(* Reuse the morphisms from R_convex_space. *)
Import finmap.
Local Open Scope fdist_scope.

Lemma convn_convnfsdist (n : nat) (g : 'I_n -> {dist A}) (d : {fdist 'I_n}) :
  <|>_d g = fsdist_convn d g.
Proof.
apply: fsdist_ext=> a; rewrite -[LHS]Scaled1RK.
rewrite (S1_Convn_proj [the {affine _ -> _} of f a]) /=.
rewrite big_scaleR fsdist_convnE /= fsfunE.
case: ifPn => adg.
  by apply eq_bigr => i _; rewrite scaleR_scalept // Scaled1RK.
(* TODO: extra lemmas ? *)
rewrite big1 // => i _.
have [->|di0] := eqVneq (d i) 0; first by rewrite scale0pt.
have [gia0|gia0] := eqVneq (g i a) 0.
  by rewrite /f gia0 scaleR_scalept/= ?mulR0.
move/bigfcupP : adg => abs; exfalso; apply: abs.
exists i; last by rewrite mem_finsupp.
by rewrite mem_index_enum/=; apply/ltRP; rewrite -fdist_Rgt0.
Qed.

End FSDist_convex_space.

(*Section fsdist_ordered_convex_space.
Variable A : choiceType.
(*Definition fsdist_orderedConvMixin := @OrderedConvexSpace.Mixin {dist A}.
NB: not used?*)
End fsdist_ordered_convex_space.*)

Definition fsdist_eval (C : choiceType) (x : C) := fun D : {dist C} => D x.

Lemma fsdist_eval_affine (C : choiceType) (x : C) : affine (fsdist_eval x).
Proof. by move=> a b p; rewrite /fsdist_eval fsdist_convE. Qed.

HB.instance Definition _ (C : choiceType) (x : C) :=
  isAffine.Build _ _ _ (fsdist_eval_affine x).

Section Convn_of_FSDist.
Local Open Scope classical_set_scope.
Variable C : convType.

Definition Convn_of_fsdist (d : {dist C}) : C :=
  <$>_(fdist_of_fs d) (fun x : finsupp d => fsval x).

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
  \ssum_i scalept (fdist_of_fs d i) (S1 (fsval i)) =
  \ssum_(i <- finsupp d) scalept (d i) (S1 i).
Proof.
under eq_bigr do rewrite fdist_of_fsE.
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
have [->|pn0] := eqVneq p R0%:pr; first by rewrite !conv0.
have [->|pn1] := eqVneq p R1%:pr; first by rewrite !conv1.
have opn0 : p.~ != R0. by apply onem_neq0.
apply: S1_inj; rewrite affine_conv/= !S1_Convn_finType ssum_seq_finsuppE.
under [LHS]eq_bigr do rewrite fsdist_scalept_conv.
rewrite big_seq_fsetE big_scalept_conv_split /=.
rewrite 2!ssum_seq_finsuppE' 2!ssum_seq_finsuppE.
rewrite -(@ssum_widen_finsupp x); last exact/finsupp_conv_subr.
by rewrite -(@ssum_widen_finsupp y)//; exact/finsupp_conv_subl.
Qed.

HB.instance Definition _ := isAffine.Build _ _ _ Convn_of_fsdist_affine.

End Convn_of_FSDist.

Lemma Convn_of_fsdistjoin (C : choiceType) (D : {dist {dist C}}) :
  Convn_of_fsdist D = fsdistjoin D.
Proof.
apply: fsdist_ext => a; rewrite -[LHS]Scaled1RK.
rewrite (S1_proj_Convn_finType [the {affine _ -> _} of fsdist_eval a]).
rewrite big_scaleR fsdistjoinE big_seq_fsetE; apply eq_bigr => -[d dD] _.
by rewrite (scaleR_scalept _ (fdist_Rge0 _ _)) fdist_of_fsE Scaled1RK.
Qed.

Section lemmas_for_probability_monad_and_adjunction.
Local Open Scope fset_scope.
Local Open Scope R_scope.

Lemma Convn_of_fsdist1 (C : convType) (x : C) : Convn_of_fsdist (fsdist1 x) = x.
Proof.
apply: (@S1_inj _ _ x).
rewrite S1_Convn_finType /=.
rewrite (eq_bigr (fun=> S1 x)); last first.
  move=> i _; rewrite fdist_of_fsE fsdist1E /= -(supp_fsdist1 x).
  rewrite fsvalP scale1pt /=; congr (S1 _).
  by case: i => i /=; rewrite supp_fsdist1 inE => /eqP.
by rewrite big_const (_ : #| _ | = 1%N) // -cardfE supp_fsdist1 cardfs1.
Qed.

Lemma Convn_of_fsdistmap (C D : convType) (f : {affine C -> D})
    (d : {dist C}) :
  f (Convn_of_fsdist d) = Convn_of_fsdist (fsdistmap f d).
Proof.
apply S1_inj => /=.
rewrite S1_proj_Convn_finType // S1_Convn_finType.
set X := LHS.
under eq_bigr do rewrite fdist_of_fsE.
rewrite ssum_seq_finsuppE' supp_fsdistmap.
under eq_bigr do rewrite fsdistbindE.
rewrite big_seq; under eq_bigr=> y Hy.
- rewrite big_scaleptl'; [| by rewrite scale0pt | by move=> j; apply mulR_ge0].
  under eq_bigr=> i do rewrite fsdist1E inE.
  over.
rewrite -big_seq exchange_big /=.
rewrite (@big_seq _ _ _ _ (finsupp d)).
under eq_bigr=> x Hx.
- rewrite (big_fsetD1 (f x)) /=; last by apply/imfsetP; exists x.
  rewrite eqxx mulR1.
  rewrite (@big_seq _ _ _ _ ([fset f x0 | x0 in finsupp d] `\ f x)).
  under eq_bigr=> y do [rewrite in_fsetD1=> /andP [] /negbTE -> Hy;
                        rewrite mulR0 scale0pt].
  rewrite big1 // addpt0.
  over.
rewrite /X.
under eq_bigr do rewrite fdist_of_fsE.
by rewrite ssum_seq_finsuppE'' big_seq.
Qed.

Section triangular_laws_left_convn.
Variable C : choiceType.

Lemma triangular_laws_left0 (d : {dist C}) :
  Convn_of_fsdist (fsdistmap (@fsdist1 C) d) = d.
Proof.
apply: fsdist_ext => x; apply S1_inj.
rewrite (S1_proj_Convn_finType [the {affine _ -> _} of fsdist_eval x]).
under eq_bigr do rewrite fdist_of_fsE.
rewrite (ssum_seq_finsuppE'' (fun i : {dist C} => i x)).
rewrite supp_fsdistmap.
rewrite big_imfset /=; last by move=> *; apply: fsdist1_inj.
under eq_bigr do rewrite fsdist1E inE fsdist1map.
have nx0 : \ssum_(i <- finsupp d `\ x)
    scalept (d i) (S1 (if x == i then 1 else 0)) = scalept (d x).~ (S1 0).
  transitivity (scalept (\sum_(i <- finsupp d `\ x) (d i)) (S1 0)).
    rewrite big_scaleptl' //; last by rewrite scale0pt.
    by apply: eq_fbigr => y /fsetD1P []; rewrite eq_sym=> /negbTE ->.
  by congr (_ _ _); rewrite fsdist_suppD1.
case/boolP : (x \in finsupp d) => xfd.

  rewrite (big_fsetD1 x) //=.
  rewrite nx0.
  rewrite eqxx.
  rewrite -(convptE (d x)).
(*↑TODO 2023 08 25 *)

  rewrite (big_fsetD1 x) //= nx0 eqxx -convptE -affine_conv/=.
  by rewrite avgRE mulR0 addR0 mulR1.
by rewrite -(mem_fsetD1 xfd) nx0 fsfun_dflt // onem0 scale1pt.
Qed.

End triangular_laws_left_convn.

End lemmas_for_probability_monad_and_adjunction.
