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
Record t := mk {
  f :> {fsfun A -> R with 0} ;
  f01 : all (fun x => 0 <b= f x)%R (finsupp f) &&
        \rsum_(a <- finsupp f) f a == 1}.
Lemma ge0 (P : t) a : (0 <= P a)%R.
Proof.
case: P => /= f /andP[/allP H _]; apply/leRP.
have [/eqP ->|fa0] := boolP (f a == 0%R); first exact/leRR'.
apply/H; by rewrite mem_finsupp.
Qed.
Lemma f1 (P : t) : \rsum_(a <- (finsupp P)) P a = 1.
Proof. by case: P => P /= /andP[_ /eqP]. Qed.
End dist.
End Dist.
Coercion Dist.f : Dist.t >-> fsfun.

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

Lemma Distmk (f : {fsfun A -> R with 0}) (H0 : forall a, (0 <= f a)%R)
  (H1 : \rsum_(a <- finsupp f) f a = 1%R) :
  all (fun x => 0 <b= f x)%R (finsupp f) && \rsum_(a <- finsupp f) f a == 1.
Proof. rewrite H1 eqxx andbT; apply/allP => x _. exact/leRP/H0. Qed.

Definition makeDist (f : {fsfun A -> R with 0}) (H0 : forall a, (0 <= f a)%R)
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
rewrite -[RHS](epmf1 P) [in RHS](bigID (fun x => x \in finsupp f)) /=.
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
Definition f : {fsfun A -> R with 0} := [fsfun b in [fset a] => 1 | 0].
Lemma suppf : finsupp f = [fset a].
Proof.
apply/fsetP => b; rewrite mem_finsupp /f fsfunE inE.
case: ifPn => ba; [exact/eqP/gtR_eqF | by rewrite eqxx].
Qed.
Lemma f0 b : (0 <= f b)%R.
Proof. rewrite fsfun_fun inE; case: ifPn => // _; exact/leRR. Qed.
Lemma f1 : \rsum_(b <- finsupp f) f b = 1%R.
Proof. by rewrite suppf big_seq_fset1 /f fsfunE inE eqxx. Qed.
Definition d : Dist A := locked (makeDist f0 f1).
Lemma dE a0 : d a0 = f a0.
Proof. by rewrite /d; unlock. Qed.
Lemma supp : finsupp d = [fset a].
Proof. by rewrite -suppf; apply/fsetP => b; rewrite !mem_finsupp dE. Qed.
End def.
End Dist1.

Module DistBind.
Section def.
Local Open Scope fset_scope.
Variables (A B : choiceType) (p : Dist A) (g : A -> Dist B).
Let D := \bigcup_(d <- g @` [fset a | a in finsupp p]) finsupp d.
Definition f : {fsfun B -> R with 0} :=
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
rewrite -big_distrr /=.
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
Lemma dE x : d x = f x.
Proof. by rewrite /d; unlock. Qed.
Lemma supp : finsupp d = D.
Proof.
apply/fsetP => b; rewrite !mem_finsupp; apply/idP/idP => [|].
  rewrite dE /f fsfunE; case: ifPn => //; by rewrite eqxx.
case/bigfcupP => dB.
rewrite andbT => /imfsetP[a].
rewrite !(inE,mem_finsupp) => pa0 ->{dB} gab0.
rewrite dE /f fsfunE; case: ifPn; last first.
  apply: contra => _.
  apply/bigfcupP.
  exists (g a); last by rewrite mem_finsupp.
  by rewrite andbT; apply/imfsetP; exists a => //; rewrite !(inE,mem_finsupp).
case/bigfcupP => dB.
rewrite andbT => /imfsetP[a0].
rewrite !(inE,mem_finsupp) => pa00 ->{dB} ga0b0.
apply/eqP => H.
have : ((p a0) * (g a0) b <> R0)%R by rewrite mulR_eq0 => -[]; exact/eqP.
apply.
move/prsumr_seq_eq0P : H; apply.
exact: fset_uniq.
move=> b0 _; apply/mulR_ge0; exact/Dist.ge0.
by rewrite mem_finsupp.
Qed.
End def.
End DistBind.

Lemma DistBind1f (A B : choiceType) (a : A) (f : A -> Dist B) :
  DistBind.d (Dist1.d a) f = f a.
Proof.
apply/val_inj/val_inj => /=; congr fmap_of_fsfun; apply/fsfunP => b.
rewrite DistBind.dE /= /DistBind.f /= fsfunE /=.
case: ifPn => [|H].
  case/bigfcupP => /= d; rewrite andbT.
  case/imfsetP => a0 /= /imfsetP[a1 /=].
  rewrite mem_finsupp Dist1.dE /Dist1.f fsfunE inE.
  case: ifPn; last by rewrite eqxx.
  move/eqP=> ->{a1} _ ->{a0} ->{d}.
  rewrite mem_finsupp => fa1b.
  rewrite Dist1.supp big_seq_fsetE big_fset1 Dist1.dE /Dist1.f fsfunE /= inE eqxx.
  by rewrite /multiplication /mul_notation mul1R.
case/boolP : ((f a) b == R0 :> R) => [/eqP ->//|fab0].
case/bigfcupP : H.
exists (f a); last by rewrite mem_finsupp.
rewrite andbT; apply/imfsetP; exists a => //.
rewrite inE mem_finsupp Dist1.dE /Dist1.f fsfunE inE eqxx.
rewrite /one_notation /zero_notation /zero /one; exact/eqP.
Qed.

Lemma DistBindp1 (A : choiceType) (p : Dist A) : DistBind.d p (@Dist1.d A) = p.
Proof.
apply/val_inj/val_inj => /=; congr fmap_of_fsfun; apply/fsfunP => b.
rewrite DistBind.dE /DistBind.f fsfunE /=.
case: ifPn => [|H].
  case/bigfcupP => /= d; rewrite andbT.
  case/imfsetP => /= a /imfsetP[a0].
  rewrite !mem_finsupp => pa00 ->{a} ->{d}.
  rewrite Dist1.dE /Dist1.f fsfunE inE; case: ifPn => [/eqP ->{b} _|]; last by rewrite eqxx.
  rewrite (big_fsetD1 a0) ?mem_finsupp //= Dist1.dE /= /Dist1.f fsfunE inE eqxx /=.
  rewrite big1_fset ?addR0 //.
    by rewrite /one /one_notation /multiplication /mul_notation mulR1.
  move=> a.
  rewrite !inE => /andP[aa0].
  rewrite mem_finsupp => pa0 _.
  rewrite Dist1.dE /Dist1.f fsfunE inE eq_sym (negbTE aa0).
  by rewrite /zero /zero_notation /multiplication /mul_notation mulR0.
case/boolP : (p b == R0 :> R) => [/eqP ->//|pb0].
case/bigfcupP : H.
exists (Dist1.d b); last first.
  rewrite mem_finsupp Dist1.dE /Dist1.f fsfunE inE eqxx.
  by apply/eqP; rewrite /one /zero /one_notation /zero_notation.
rewrite andbT; apply/imfsetP; exists b => //.
by rewrite !(inE,mem_finsupp).
Qed.

Lemma DistBindA A B C (m : Dist A) (f : A -> Dist B) (g : B -> Dist C) :
  DistBind.d (DistBind.d m f) g = DistBind.d m (fun x => DistBind.d (f x) g).
Proof.
apply/val_inj/val_inj => /=; congr fmap_of_fsfun; apply/fsfunP => c.
rewrite !DistBind.dE /DistBind.f !fsfunE /=.
case: ifPn => [|H].
  case/bigfcupP => /= dC.
  rewrite andbT => /imfsetP[b].
  rewrite !(inE,mem_finsupp) DistBind.dE /DistBind.f fsfunE /=.
  case: ifPn; last by rewrite eqxx.
  case/bigfcupP => /= dB.
  rewrite andbT => /imfsetP[a].
  rewrite !(inE,mem_finsupp) => ma0 ->{dB} fab0 H ->{dC} gbc0.
  rewrite ifT; last first.
    apply/bigfcupP => /=.
    exists (DistBind.d (f a) g); last first.
      rewrite DistBind.supp.
      apply/bigfcupP; exists (g b); last by rewrite mem_finsupp.
      rewrite andbT; apply/imfsetP.
      exists b => //.
      by rewrite !(inE,mem_finsupp).
    rewrite andbT; apply/imfsetP.
    by exists a => //; rewrite !(inE,mem_finsupp).
  rewrite (eq_bigr (fun a => (\rsum_(a0 <- finsupp m) m a0 * (f a0) a * (g a) c))); last first.
    move=> b0 _.
    rewrite DistBind.dE /DistBind.f fsfunE.
    case: ifPn.
      case/bigfcupP => dB.
      rewrite andbT => /imfsetP[a0].
      rewrite !(inE,mem_finsupp) => ma00 ->{dB} fa0b0.
      by rewrite -big_distrl.
    rewrite {1}/multiplication /mul_notation /=.
    rewrite (mul0R (g b0 c)) => K.
    rewrite big1_fset => // a0.
    rewrite mem_finsupp => ma00 _.
    apply/eqP/negPn/negP => L.
    move/negP : K; apply.
    apply/bigfcupP.
    exists (f a0); last first.
      rewrite mem_finsupp; apply: contra L => /eqP ->.
      by rewrite /multiplication /mul_notation /= mulR0 mul0R.
    rewrite andbT; apply/imfsetP; exists a0 => //.
    by rewrite !(inE,mem_finsupp).
  rewrite exchange_big; apply eq_bigr => a0 _ /=.
  rewrite DistBind.dE /DistBind.f fsfunE.
  case/boolP : (m a0 == R0 :> R) => [/eqP ma00|ma00].
    rewrite ma00.
    rewrite {3}/multiplication /mul_notation mul0R big1_fset // => b2 _ _.
    by rewrite /multiplication /mul_notation 2!mul0R.
  case: ifPn.
    case/bigfcupP => dC.
    rewrite andbT => /imfsetP[b0].
    rewrite !(inE,mem_finsupp) => fa0b0 ->{dC} gb0c.
    evar (h : B -> R); rewrite (eq_bigr h); last first.
      move=> b1 _.
      rewrite /multiplication /mul_notation.
      rewrite -mulRA.
      rewrite /h.
      reflexivity.
    rewrite {}/h.
    rewrite -(big_distrr  (m a0)) /=.
    congr (_ * _).
    rewrite (big_fsetID _ (fun x => x \in finsupp (f a0))) /=.
    rewrite [X in (_ + X)%R = _](_ : _ = 0) ?addR0; last first.
      rewrite big1_fset => // b1.
      case/imfsetP => b2 /=.
      rewrite !inE => /andP[/=].
      by rewrite !mem_finsupp negbK => _ /eqP K -> _; rewrite K mul0R.
    apply big_fset_incl.
      apply/fsubsetP => b1.
      rewrite mem_finsupp.
      case/imfsetP => b2.
     by rewrite !(inE,mem_finsupp) => /andP[_] ? ->.
    move=> b1.
    rewrite mem_finsupp => fa0b1.
    case/boolP : (g b1 c == R0 :> R) => [/eqP -> _|gb1c].
      by rewrite /multiplication /mul_notation mulR0.
    case/imfsetP; exists b1 => //.
    rewrite !(inE,mem_finsupp) fa0b1 andbT DistBind.dE /DistBind.f fsfunE.
    rewrite ifT.
    have /eqP K : (m a0 * (f a0 b1) <> R0 :> R) by rewrite mulR_eq0 => -[]; exact/eqP.
    apply/eqP.
    move/prsumr_seq_eq0P => L.
    move/eqP : K; apply.
    apply L => //.
    move=> a1 _; apply mulR_ge0; exact/Dist.ge0.
    by rewrite mem_finsupp.
  apply/bigfcupP.
  exists (f a0); last by rewrite mem_finsupp.
  rewrite andbT.
  apply/imfsetP.
  exists a0 => //.
  by rewrite !(inE,mem_finsupp).
  move=> K.
  rewrite DistBind.supp.
  suff : \rsum_(i <- finsupp (DistBind.d m f)) ((f a0) i * (g i) c)%R = R0 :> R.
    rewrite DistBind.supp => L.
    evar (h : B -> R); rewrite (eq_bigr h); last first.
      move=> b1 _.
      rewrite /multiplication /mul_notation.
      rewrite -mulRA.
      rewrite /h.
      reflexivity.
    by rewrite -(big_distrr (m a0)) /= L !mulR0 /multiplication /mul_notation mulR0.
  apply/prsumr_seq_eq0P.
  exact: fset_uniq.
  move=> b1 _; apply mulR_ge0; exact/Dist.ge0.
  move=> a1 Ha1.
  case/boolP : (g a1 c == R0 :> R) => ga1c.
    by rewrite (eqP ga1c) mulR0.
  case/boolP : (f a0 a1 == R0 :> R) => fa0a1.
    by rewrite (eqP fa0a1) mul0R.
  case/bigfcupP : K.
  exists (g a1); last by rewrite mem_finsupp.
  rewrite andbT.
  apply/imfsetP; exists a1 => //.
  by rewrite !(inE,mem_finsupp).
rewrite ifF //; apply/negbTE; apply: contra H.
case/bigfcupP => /= dC.
rewrite andbT => /imfsetP[x]; rewrite !(inE,mem_finsupp) => mx0 ->{dC}.
rewrite DistBind.dE /DistBind.f fsfunE.
case: ifPn; last by rewrite eqxx.
case/bigfcupP => dC; rewrite andbT => /imfsetP[b].
rewrite !(inE,mem_finsupp) => fxb0 ->{dC} gbc0 K.
apply/bigfcupP.
exists (g b); last by rewrite mem_finsupp.
rewrite andbT; apply/imfsetP; exists b => //.
rewrite !(inE,mem_finsupp) DistBind.dE /DistBind.f fsfunE.
case: ifPn; last first.
  apply: contra => _.
  apply/bigfcupP.
  exists (f x); last by rewrite mem_finsupp.
  rewrite andbT; apply/imfsetP; exists x => //.
  by rewrite !(inE,mem_finsupp).
case/bigfcupP => dB.
rewrite andbT => /imfsetP[a].
rewrite !(inE,mem_finsupp) => ma0 ->{dB} fab0.
have /eqP : (m a * (f a b) <> R0)%R by rewrite mulR_eq0 => -[]; exact/eqP.
apply: contra => /eqP /prsumr_seq_eq0P L; apply/eqP/L.
by rewrite fset_uniq.
move=> a0 _; apply/mulR_ge0; exact/Dist.ge0.
by rewrite mem_finsupp.
Qed.

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
