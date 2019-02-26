From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup perm finalg matrix.
From mathcomp Require Import finmap set.
Require Import Reals Lra Nsatz FunctionalExtensionality.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop.
Require Import proba.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* wip *)

Axiom R_choiceMixin : Choice.mixin_of R.
Canonical R_choiceType := ChoiceType R R_choiceMixin.

(* distribution using choiceType *)
Module Dist.
Section dist.
Variable (A : choiceType).
Record t  := mk {
  f :> {fsfun A -> R for (fun=>0)} ;
  f01 : all (fun x => 0 <b= x)%R (map f (finsupp f)) &&
        \rsum_(a <- undup (finsupp f)) f a == 1}.
Lemma ge0 (P : t) a : (0 <= P a)%R.
Proof.
case: P => /= f /andP[/allP H _]; apply/leRP.
have [/eqP ->|fa0] := boolP (f a == 0%R); first exact/leRR'.
apply/H/mapP; exists a => //; by rewrite mem_finsupp.
Qed.
Lemma f1 (P : t) : \rsum_(a <- undup (finsupp P)) P a = 1.
Proof. by case: P => P /= /andP[_ /eqP]. Qed.
End dist.
End Dist.
Coercion distg := Dist.f.

Section distt_canonical.
Variable (A : choiceType).

Canonical distt_subType := Eval hnf in [subType for @Dist.f A].
Definition distt_eqMixin := [eqMixin of @Dist.t A by <:].
Canonical distt_eqType := Eval hnf in EqType _ distt_eqMixin.
Definition distt_choiceMixin := [choiceMixin of @Dist.t A by <:].
Canonical distt_choiceType := Eval hnf in ChoiceType _ distt_choiceMixin.

End distt_canonical.

Definition distt (A : choiceType) : choiceType := distt_choiceType A.

Section distt_lemmas.
Variable A : choiceType.

Lemma Distmk (f : {fsfun A -> R for (fun=>0)}) (H0 : forall a, (0 <= f a)%R)
  (H1 : \rsum_(a <- undup (finsupp f)) f a = 1%R) : all (fun x => 0 <b= x)%R (map f (finsupp f)) &&
        \rsum_(a <- undup (finsupp f)) f a == 1.
Proof.
rewrite H1 eqxx andbT; apply/allP => x.
case/mapP => a; rewrite mem_finsupp => fa0 ->{x}; exact/leRP/H0.
Qed.

Definition makeDist (f : {fsfun A -> R for (fun=>0)}) (H0 : forall a, (0 <= f a)%R)
  (H1 : \rsum_(a <- undup (finsupp f)) f a = 1%R) := Dist.mk (Distmk H0 H1).

End distt_lemmas.

Module Dist1.
Section def.
Local Open Scope fset_scope.
Variables (A : choiceType) (a : A).
Definition f : {fsfun A -> R for (fun=>0)} := [fsfun b in [fset a] => 1 | 0].
Lemma f0 b : (0 <= f b)%R.
Proof. rewrite fsfun_fun inE; case: ifPn => // _; exact/leRR. Qed.
Lemma f1 : \rsum_(b <- undup (finsupp f)) f b = 1%R.
Proof.
rewrite (_ : undup (finsupp f) = [fset a]); last first.
  have -> : finsupp f = [fset a].
    apply/fsetP => b; rewrite mem_finsupp /f fsfunE inE.
    case: ifPn => ba; [exact/eqP/gtR_eqF | by rewrite eqxx].
  by rewrite undup_id.
by rewrite big_seq_fset1 /f fsfunE inE eqxx.
Qed.
Definition d : distt A := locked (makeDist f0 f1).
Lemma dE a0 : d a0 = INR (a0 == a)%bool.
Proof.
rewrite /d; unlock; rewrite /= /f fsfunE inE; by case: ifPn.
Qed.
End def.
End Dist1.

Module DistBind.
Section def.
Local Open Scope fset_scope.
Variables (A B : choiceType) (p : distt A) (g : A -> distt B).
Let D := \bigcup_(d <- g @` [fset a | a in finsupp p]) finsupp d.
Definition f : {fsfun B -> R for (fun=>0)} :=
  [fsfun b in D => \rsum_(a <- undup (finsupp p)) p a * (g a) b | 0].
Lemma f0 b : (0 <= f b)%R.
Proof.
rewrite /f fsfunE; case: ifP =>  _; last exact/leRR.
apply rsumr_ge0 => a _; apply/mulR_ge0; exact/Dist.ge0.
Qed.
Lemma f1 : \rsum_(b <- undup (finsupp f)) f b = 1.
Proof.
rewrite {2}/f.
evar (h : B -> R); rewrite (eq_bigr h); last first.
  move=> b _; rewrite fsfunE /h; reflexivity.
rewrite {}/h -big_mkcond /= exchange_big /=.
rewrite -[RHS](Dist.f1 p); apply eq_bigr => a _.
rewrite -big_distrr /= (_ : Dist.f p a = p a); last by case: p.
rewrite (_ : (\rsum_(_ <- _ | _) _ = 1%R)%R) ?mulR1 //.
rewrite -[RHS](Dist.f1 (g a)).
Admitted.
(*Proof.
rewrite /f exchange_big /= -[RHS](pmf1 p); apply eq_bigr => a _.
by rewrite -big_distrr /= pmf1 mulR1.
Qed.*)
Definition d : distt B := locked (makeDist f0 f1).
(*Lemma dE x : d x = \rsum_(a in A) p a * (g a) x.
Proof. by rewrite /d; unlock. Qed.*)
End def.
End DistBind.

Lemma DistBind1f (A B : choiceType) (a : A) (f : A -> distt B) :
  DistBind.d (Dist1.d a) f = f a.
Proof.
(*apply/dist_ext => b.
rewrite DistBind.dE /= (bigD1 a) //= Dist1.dE eqxx mul1R.
rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 ?addR0 // => c ca.
by rewrite Dist1.dE (negbTE ca) mul0R.
Qed.*) Admitted.
