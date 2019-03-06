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

(* wip: distribution using choiceType *)

Axiom R_choiceMixin : Choice.mixin_of R.
Canonical R_choiceType := ChoiceType R R_choiceMixin.

Module Dist.
Section dist.
Variable A : choiceType.
Record t  := mk {
  f :> {fsfun A -> R for (fun=>0)} ;
  f01 : all (fun x => 0 <b= x)%R (map f (finsupp f)) &&
        \rsum_(a <- (finsupp f)) f a == 1}.
Lemma ge0 (P : t) a : (0 <= P a)%R.
Proof.
case: P => /= f /andP[/allP H _]; apply/leRP.
have [/eqP ->|fa0] := boolP (f a == 0%R); first exact/leRR'.
apply/H/mapP; exists a => //; by rewrite mem_finsupp.
Qed.
Lemma f1 (P : t) : \rsum_(a <- (finsupp P)) P a = 1.
Proof. by case: P => P /= /andP[_ /eqP]. Qed.
End dist.
End Dist.
Coercion distf := Dist.f.

Section Dist_canonical.
Variable A : choiceType.
Canonical Dist_subType := Eval hnf in [subType for @Dist.f A].
Definition Dist_eqMixin := [eqMixin of @Dist.t A by <:].
Canonical Dist_eqType := Eval hnf in EqType _ Dist_eqMixin.
Definition Dist_choiceMixin := [choiceMixin of @Dist.t A by <:].
Canonical Dist_choiceType := Eval hnf in ChoiceType _ Dist_choiceMixin.
End Dist_canonical.

Definition Dist (A : choiceType) : choiceType := Dist_choiceType A.

Definition Dist_of (A : choiceType) := fun phT : phant (Choice.sort A) => Dist A.

Notation "{ 'Dist' T }" := (Dist_of (Phant T)).

Section Dist_prop.
Variable A : choiceType.

Lemma Distmk (f : {fsfun A -> R for (fun=>0)}) (H0 : forall a, (0 <= f a)%R)
  (H1 : \rsum_(a <- finsupp f) f a = 1%R) : all (fun x => 0 <b= x)%R (map f (finsupp f)) &&
        \rsum_(a <- finsupp f) f a == 1.
Proof.
rewrite H1 eqxx andbT; apply/allP => x.
case/mapP => a; rewrite mem_finsupp => fa0 ->{x}; exact/leRP/H0.
Qed.

Definition makeDist (f : {fsfun A -> R for (fun=>0)}) (H0 : forall a, (0 <= f a)%R)
  (H1 : \rsum_(a <- finsupp f) f a = 1%R) := Dist.mk (Distmk H0 H1).

End Dist_prop.

Module Dist_of_dist.
Section def.
Variable (A : finType) (P : dist A).
Local Open Scope fset_scope.
Let f := [fsfun a in [fset a0 | a0 in enum A] => P a | 0].
Let f0 : (forall a, 0 <= f a)%R.
Proof.
move=> a; rewrite fsfunE; case: ifPn => _; [exact/dist_ge0|exact/leRR].
Qed.
Let f1 : \rsum_(a <- finsupp f) f a = 1%R.
Proof.
rewrite (bigID (fun x => x \in enum A)) /=.
rewrite [in X in (_ + X)%R = _]big1 ?addR0; last first.
  by move=> a; rewrite mem_enum inE.
rewrite (eq_bigr (fun x => P x)); last first.
  by move=> a _; rewrite fsfunE; case: ifPn => //; rewrite inE mem_enum inE.
rewrite -[RHS](pmf1 P) [in RHS](bigID (fun x => x \in finsupp f)) /=.
rewrite [in X in _ = (_ + X)%R]big1 ?addR0; last first.
  move=> a /eqP; rewrite memNfinsupp fsfunE.
  by case: ifPn => [_ /eqP/eqP //|]; rewrite inE /= mem_enum inE.
rewrite -big_filter -[in RHS]big_filter; apply eq_big_perm.
apply uniq_perm_eq.
exact/filter_uniq/fset_uniq.
by apply/filter_uniq; rewrite /index_enum -enumT; apply/enum_uniq.
by move=> a; rewrite !mem_filter !inE /= andbC.
Qed.
Definition d : Dist A := makeDist f0 f1.
End def.
End Dist_of_dist.

Module Dist1.
Section def.
Local Open Scope fset_scope.
Variables (A : choiceType) (a : A).
Definition f : {fsfun A -> R for (fun=>0)} := [fsfun b in [fset a] => 1 | 0].
Lemma f0 b : (0 <= f b)%R.
Proof. rewrite fsfun_fun inE; case: ifPn => // _; exact/leRR. Qed.
Lemma f1 : \rsum_(b <- (finsupp f)) f b = 1%R.
Proof.
rewrite (_ : finsupp f = [fset a]); last first.
  apply/fsetP => b; rewrite mem_finsupp /f fsfunE inE.
  case: ifPn => ba; [exact/eqP/gtR_eqF | by rewrite eqxx].
by rewrite big_seq_fset1 /f fsfunE inE eqxx.
Qed.
Definition d : Dist A := locked (makeDist f0 f1).
Lemma dE a0 : d a0 = INR (a0 == a)%bool.
Proof.
rewrite /d; unlock; rewrite /= /f fsfunE inE; by case: ifPn.
Qed.
End def.
End Dist1.

Module DistBind.
Section def.
Local Open Scope fset_scope.
Variables (A B : choiceType) (p : Dist A) (g : A -> Dist B).
Let D := \bigcup_(d <- g @` [fset a | a in finsupp p]) finsupp d.
Definition f : {fsfun B -> R for (fun=>0)} :=
  [fsfun b in D => \rsum_(a <- finsupp p) p a * (g a) b | 0].
Lemma f0 b : (0 <= f b)%R.
Proof.
rewrite /f fsfunE; case: ifP =>  _; last exact/leRR.
apply rsumr_ge0 => a _; apply/mulR_ge0; exact/Dist.ge0.
Qed.
Lemma f1 : \rsum_(b <- finsupp f) f b = 1.
Proof.
rewrite {2}/f.
evar (h : B -> R); rewrite (eq_bigr h); last first.
  move=> b _; rewrite fsfunE /h; reflexivity.
rewrite {}/h -big_mkcond /= exchange_big /=.
rewrite -[RHS](Dist.f1 p); apply eq_bigr => a _.
case/boolP : (p a == R0 :> R) => pa0.
  rewrite (eqP pa0) big1 // => b _; exact: mul0R (* TODO *).
rewrite -big_distrr /= (_ : Dist.f p a = p a); last by case: p.
rewrite (_ : (\rsum_(_ <- _ | _) _ = 1%R)%R) ?mulR1 //.
rewrite (bigID (fun x => x \in finsupp (g a))) /=.
rewrite [X in (_ + X)%R = _]big1 ?addR0; last first.
  by move=> b /andP[_]; rewrite memNfinsupp => /eqP.
rewrite (eq_bigl (fun i => i \in finsupp (g a))); last first.
  move=> b; rewrite andb_idl // mem_finsupp => gab0.
  apply/bigfcupP; exists (g a); rewrite ?mem_finsupp // andbT.
  apply/imfsetP; exists a => //; by rewrite inE mem_finsupp.
rewrite -big_filter -[RHS](Dist.f1 (g a)); apply eq_big_perm.
apply uniq_perm_eq; [by rewrite filter_uniq | by rewrite fset_uniq |move=> b].
rewrite mem_finsupp.
apply/idP/idP => [|gab0]; first by rewrite mem_filter mem_finsupp => /andP[].
rewrite mem_filter 2!mem_finsupp gab0 /= /f fsfunE ifT; last first.
  apply/bigfcupP; exists (g a); rewrite ?mem_finsupp // andbT.
  by apply/imfsetP; exists a => //; rewrite inE mem_finsupp.
apply: contra gab0 => /eqP/prsumr_seq_eq0P.
rewrite fset_uniq => /(_ isT) H.
suff : (p a * g a b = 0)%R.
 by rewrite mulR_eq0 => -[/eqP|->//]; rewrite (negbTE pa0).
apply/H; rewrite ?mem_finsupp // => a0 _; apply/mulR_ge0; exact/Dist.ge0.
Qed.
Definition d : Dist B := locked (makeDist f0 f1).
(*Lemma dE x : d x = \rsum_(a in A) p a * (g a) x.
Proof. by rewrite /d; unlock. Qed.*)
End def.
End DistBind.

Lemma DistBind1f (A B : choiceType) (a : A) (f : A -> Dist B) :
  DistBind.d (Dist1.d a) f = f a.
Proof.
(*apply/dist_ext => b.
rewrite DistBind.dE /= (bigD1 a) //= Dist1.dE eqxx mul1R.
rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 ?addR0 // => c ca.
by rewrite Dist1.dE (negbTE ca) mul0R.
Qed.*) Admitted.

Lemma DistBindp1 (A : choiceType) (p : Dist A) : DistBind.d p (@Dist1.d A) = p.
Proof.
(*apply/dist_ext => /= a.
rewrite DistBind.dE /= (bigD1 a) //= Dist1.dE eqxx mulR1.
rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addR ?mulR0 /= ?addR0 //.
by move=> b ba; rewrite Dist1.dE eq_sym (negbTE ba) mulR0.
Qed.*) Admitted.

Lemma DistBindA A B C (m : Dist A) (f : A -> Dist B) (g : B -> Dist C) :
  DistBind.d (DistBind.d m f) g = DistBind.d m (fun x => DistBind.d (f x) g).
Proof.
(*apply/dist_ext => c; rewrite !DistBind.dE /=.
rewrite (eq_bigr (fun a => (\rsum_(a0 in A) m a0 * (f a0) a * (g a) c))); last first.
  move=> b _; by rewrite DistBind.dE big_distrl.
rewrite exchange_big /=; apply eq_bigr => a _.
rewrite DistBind.dE big_distrr /=; apply eq_bigr => b _; by rewrite mulRA.
Qed.*) Admitted.

Module I2Dist.
Section def.
Variable (p : prob).
(*Definition f := [ffun i : 'I_2 => if i == ord0 then Prob.p p else p.~].
Lemma f0 i : 0 <= f i.
Proof.
rewrite /f ffunE /=; case: ifP => _; [exact/prob_ge0|exact/onem_ge0/prob_le1].
Qed.
Lemma f1 : \rsum_(i < 2) f i = 1.
Proof. by rewrite 2!big_ord_recl big_ord0 addR0 /f !ffunE /= onemKC. Qed.*)
Definition d : {Dist 'I_2}(* := locked (makeDist f0 f1)*). Admitted.
(*Lemma dE a : d a = if a == ord0 then Prob.p p else p.~.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.*)
End def.
End I2Dist.

Module ConvDist.
Section def.
Variables (A : choiceType) (n : nat) (e : {Dist 'I_n}) (g : 'I_n -> Dist A).
(*Definition f := [ffun a => \rsum_(i < n) e i * g i a].
Lemma f0 a : 0 <= f a.
Proof. rewrite ffunE; apply: rsumr_ge0 => /= i _; apply mulR_ge0; exact: dist_ge0. Qed.
Lemma f1 : \rsum_(a in A) f a = 1.
Proof.
rewrite /f; evar (h : A -> R); rewrite (eq_bigr h); last first.
  move=> b _; rewrite ffunE /h; reflexivity.
rewrite {}/h exchange_big /= -(pmf1 e) /=; apply eq_bigr => i _.
by rewrite -big_distrr /= pmf1 mulR1.
Qed.*)
Definition d : Dist A(* := locked (makeDist f0 f1)*). Admitted.
(*Lemma dE a : d a = \rsum_(i < n) e i * g i a.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.*)
End def.
End ConvDist.

Module Conv2Dist.
Section def.
Variables (A : choiceType) (d1 d2 : Dist A) (p : prob).
Definition d : Dist A := locked
  (ConvDist.d (I2Dist.d p) (fun i => if i == ord0 then d1 else d2)).
(*Lemma dE a : d a = p * d1 a + p.~ * d2 a.
Proof.
rewrite /d; unlock => /=.
by rewrite ConvDist.dE !big_ord_recl big_ord0 /= addR0 !I2Dist.dE.
Qed.*)
End def.
Section prop.
Variables (A : choiceType).
Implicit Types a b c : Dist A.
Local Notation "x <| p |> y" := (d x y p).
Lemma bind_left_distr (B : choiceType) (p : prob) a b (f : A -> Dist B) :
  DistBind.d (a <| p |> b) f = DistBind.d a f <| p |> DistBind.d b f.
Proof.
(*apply/dist_ext => a0 /=; rewrite !(DistBind.dE,Conv2Dist.dE) /=.
rewrite 2!big_distrr /= -big_split /=; apply/eq_bigr => a1 _.
by rewrite Conv2Dist.dE mulRDl !mulRA.
Qed.*) Admitted.
End prop.
End Conv2Dist.
