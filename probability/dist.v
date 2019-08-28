From mathcomp Require Import all_ssreflect.
From mathcomp Require Import finmap.
From mathcomp Require Rstruct boolp.
Require Import Reals.
Require Import ssrR Reals_ext ssr_ext ssralg_ext bigop_ext Rbigop proba.

(* probability distributions with finite support using choiceType *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.
Local Open Scope fset_scope.

Module Dist.
Section dist.
Variable A : choiceType.
Record t := mk {
  f :> {fsfun A -> R with 0} ;
  f01 : all (fun x => 0 <b f x) (finsupp f) &&
        \sum_(a <- finsupp f) f a == 1}.
Lemma ge0 (P : t) a : 0 <= P a.
Proof.
case: P => /= f /andP[/allP H _].
case/boolP : (a \in finsupp f) => [/H/ltRP/ltRW //|].
rewrite memNfinsupp => /eqP ->; exact/leRR.
Qed.
Lemma gt0 (P : t) a : a \in finsupp P -> 0 < P a.
Proof.
rewrite mem_finsupp => Pa; apply/ltRP; rewrite lt0R Pa; exact/leRP/ge0.
Qed.
Lemma f1 (P : t) : \sum_(a <- finsupp P) P a = 1.
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

Lemma Dist_ext (d d' : Dist A) : (forall x, d x = d' x) -> d = d'.
Proof. move=> H; exact/val_inj/fsfunP/H. Qed.

Lemma Distmk (f : {fsfun A -> R with 0}) (H0 : forall a, a \in finsupp f -> 0 < f a)
  (H1 : \sum_(a <- finsupp f) f a = 1) :
  all (fun x => 0 <b f x) (finsupp f) && (\sum_(a <- finsupp f) f a == 1).
Proof. by rewrite H1 eqxx andbT; apply/allP => a /H0/ltRP. Qed.

Definition makeDist (f : {fsfun A -> R with 0}) (H0 : forall a, a \in finsupp f -> 0 < f a)
  (H1 : \sum_(a <- finsupp f) f a = 1) := Dist.mk (Distmk H0 H1).

Lemma Dist_supp_neq0 (d : Dist A) : finsupp d != fset0.
Proof.
apply/eqP => H.
move: (Dist.f1 d); rewrite H big_nil => /esym; exact: R1_neq_R0.
Qed.

End Dist_prop.

Module Dist1.
Section def.
Variables (A : choiceType) (a : A).
Let D := [fset a].
Definition f : {fsfun A -> R with 0} := [fsfun b in D => 1 | 0].
Lemma suppf : finsupp f = D.
Proof.
apply/fsetP => b; rewrite mem_finsupp /f fsfunE inE.
case: ifPn => ba; [exact/eqP/gtR_eqF | by rewrite eqxx].
Qed.
Lemma f0 b : b \in finsupp f -> 0 < f b.
Proof. rewrite mem_finsupp fsfunE inE; case: ifPn => //; by rewrite eqxx. Qed.
Lemma f1 : \sum_(b <- finsupp f) f b = 1.
Proof. by rewrite suppf big_seq_fset1 /f fsfunE inE eqxx. Qed.
Definition d : Dist A := locked (makeDist f0 f1).
Lemma dE a0 : d a0 = if a0 \in D then 1 else 0.
Proof. by rewrite /d; unlock; rewrite fsfunE. Qed.
Lemma supp : finsupp d = D.
Proof. by rewrite -suppf; apply/fsetP => b; rewrite !mem_finsupp dE fsfunE. Qed.
End def.
End Dist1.

Lemma Dist1_inj (C : choiceType) : injective (@Dist1.d C).
Proof.
move=> a b /eqP ab; apply/eqP; apply: contraTT ab => ab.
apply/eqP => /(congr1 (fun x : Dist.t _ => x a)).
rewrite !Dist1.dE !inE eqxx (negbTE ab); exact: R1_neq_R0.
Qed.

Module DistBind.
Section def.
Variables (A B : choiceType) (p : Dist A) (g : A -> Dist B).
Let D := \bigcup_(d <- g @` [fset a | a in finsupp p]) finsupp d.
Definition f : {fsfun B -> R with 0} :=
  [fsfun b in D => \sum_(a <- finsupp p) p a * (g a) b | 0].
Lemma f0 b : b \in finsupp f -> 0 < f b.
Proof.
rewrite mem_finsupp fsfunE; case: ifPn => [_ /eqP/nesym ?|]; last by rewrite eqxx.
rewrite ltR_neqAle; split => //.
apply rsumr_ge0 => a _; apply/mulR_ge0; exact/Dist.ge0.
Qed.
Lemma f1 : \sum_(b <- finsupp f) f b = 1.
Proof.
rewrite {2}/f.
evar (h : B -> R); rewrite (eq_bigr h); last first.
  move=> b _; rewrite fsfunE /h; reflexivity.
rewrite {}/h -big_mkcond /= exchange_big /=.
rewrite -[RHS](Dist.f1 p); apply eq_bigr => a _.
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
rewrite -big_filter -[RHS](Dist.f1 (g a)); apply perm_big.
apply uniq_perm; [by rewrite filter_uniq | by rewrite fset_uniq |move=> b].
rewrite mem_finsupp.
apply/idP/idP => [|gab0]; first by rewrite mem_filter mem_finsupp => /andP[].
rewrite mem_filter 2!mem_finsupp gab0 /= /f fsfunE ifT; last first.
  apply/bigfcupP; exists (g a); rewrite ?mem_finsupp // andbT.
  by apply/imfsetP; exists a => //; rewrite inE mem_finsupp.
apply: contra gab0 => /eqP/prsumr_seq_eq0P.
rewrite fset_uniq => /(_ isT) H.
suff : p a * g a b = 0.
 by rewrite mulR_eq0 => -[/eqP|->//]; rewrite (negbTE pa0).
apply/H; rewrite ?mem_finsupp // => a0 _; apply/mulR_ge0; exact/Dist.ge0.
Qed.
Definition d : Dist B := locked (makeDist f0 f1).
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
move/prsumr_seq_eq0P : H; apply => //.
move=> b0 _; apply/mulR_ge0; exact/Dist.ge0.
Qed.
End def.
End DistBind.

Lemma DistBind1f (A B : choiceType) (a : A) (f : A -> Dist B) :
  DistBind.d (Dist1.d a) f = f a.
Proof.
apply/val_inj/val_inj => /=; congr fmap_of_fsfun; apply/fsfunP => b.
rewrite DistBind.dE; case: ifPn => [|H].
  case/bigfcupP => /= d; rewrite andbT.
  case/imfsetP => a0 /= /imfsetP[a1 /=].
  rewrite Dist1.supp inE => /eqP ->{a1} ->{a0} ->{d} bfa.
  by rewrite big_seq_fsetE big_fset1 Dist1.dE /= inE eqxx mul1R.
case/boolP : ((f a) b == R0 :> R) => [/eqP ->//|fab0].
case/bigfcupP : H.
exists (f a); last by rewrite mem_finsupp.
rewrite andbT; apply/imfsetP; exists a => //=.
by rewrite imfset_id Dist1.supp inE.
Qed.

Lemma DistBindp1 (A : choiceType) (p : Dist A) : DistBind.d p (@Dist1.d A) = p.
Proof.
apply/val_inj/val_inj => /=; congr fmap_of_fsfun; apply/fsfunP => b.
rewrite DistBind.dE; case: ifPn => [|H].
  case/bigfcupP => /= d; rewrite andbT.
  case/imfsetP => /= a /imfsetP[a0] /= pa00 ->{a} ->{d}.
  rewrite Dist1.supp inE => /eqP ->{b}.
  rewrite (big_fsetD1 a0) //= Dist1.dE inE eqxx mulR1 big1_fset ?addR0 // => a.
  rewrite !inE => /andP[aa0] ap _.
  by rewrite Dist1.dE inE eq_sym (negbTE aa0) mulR0.
case/boolP : (p b == R0 :> R) => [/eqP ->//|pb0].
case/bigfcupP : H.
exists (Dist1.d b); last by rewrite Dist1.supp inE.
by rewrite andbT; apply/imfsetP; exists b => //=; rewrite imfset_id mem_finsupp.
Qed.

Lemma DistBindA A B C (m : Dist A) (f : A -> Dist B) (g : B -> Dist C) :
  DistBind.d (DistBind.d m f) g = DistBind.d m (fun x => DistBind.d (f x) g).
Proof.
apply/val_inj/val_inj => /=; congr fmap_of_fsfun; apply/fsfunP => c.
rewrite !DistBind.dE; case: ifPn => [|H]; last first.
  rewrite ifF //; apply/negbTE; apply: contra H.
  case/bigfcupP => /= dC; rewrite andbT.
  move=> /imfsetP[x] /=; rewrite imfset_id => mx ->{dC}.
  rewrite DistBind.supp.
  case/bigfcupP => dC; rewrite andbT => /imfsetP[b] /=.
  rewrite imfset_id => bfx ->{dC} cgb.
  apply/bigfcupP; exists (g b) => //; rewrite andbT.
  apply/imfsetP; exists b => //=.
  rewrite imfset_id DistBind.supp.
  apply/bigfcupP; exists (f x) => //; rewrite andbT.
  by apply/imfsetP; exists x => //=; rewrite imfset_id.
case/bigfcupP => /= dC.
rewrite andbT => /imfsetP[b] /=.
rewrite imfset_id {1}DistBind.supp => /bigfcupP[dB].
rewrite andbT => /imfsetP[a] /=.
rewrite imfset_id => ma ->{dB} fab0 ->{dC} gbc0.
rewrite ifT; last first.
  apply/bigfcupP => /=; exists (DistBind.d (f a) g); last first.
    rewrite DistBind.supp; apply/bigfcupP; exists (g b) => //.
    by rewrite andbT; apply/imfsetP; exists b => //=; rewrite imfset_id.
  by rewrite andbT; apply/imfsetP => /=; exists a.
rewrite (eq_bigr (fun a => \sum_(a0 <- finsupp m) m a0 * (f a0) a * (g a) c)); last first.
  move=> b0 _.
  rewrite DistBind.dE; case: ifPn => [/bigfcupP[dB] | ].
    by rewrite andbT => /imfsetP[a0] _ _ _; rewrite -big_distrl.
  rewrite (mul0R (g b0 c)) => K.
  rewrite big1_fset => // a0 ma00 _.
  apply/eqP/negPn/negP => L.
  move/negP : K; apply.
  apply/bigfcupP; exists (f a0); last first.
    by rewrite mem_finsupp; apply: contra L => /eqP ->; rewrite mulR0 mul0R.
  by rewrite andbT; apply/imfsetP; exists a0 => //=; rewrite imfset_id.
rewrite exchange_big; apply eq_bigr => a0 _ /=.
rewrite DistBind.dE.
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
  rewrite inE fa0b1 andbT mem_finsupp DistBind.dE ifT.
    have /eqP K : (m a0 * (f a0 b1) <> R0 :> R).
      rewrite mulR_eq0 => -[].
      exact/eqP.
      by apply/eqP; rewrite -mem_finsupp.
    apply/eqP => /prsumr_seq_eq0P => L.
    move/eqP : K; apply.
    apply L => //.
    - move=> a1 _; apply mulR_ge0; exact/Dist.ge0.
    - by rewrite mem_finsupp.
  apply/bigfcupP; exists (f a0) => //; rewrite andbT.
  by apply/imfsetP; exists a0 => //=; rewrite imfset_id mem_finsupp.
rewrite DistBind.supp.
suff : \sum_(i <- finsupp (DistBind.d m f)) (f a0) i * (g i) c = R0 :> R.
  rewrite DistBind.supp => L.
  evar (h : B -> R); rewrite (eq_bigr h); last first.
    move=> ? _; rewrite -mulRA /h; reflexivity.
  by rewrite -(big_distrr (m a0)) /= L !mulR0.
apply/prsumr_seq_eq0P.
- exact: fset_uniq.
- move=> b1 _; apply mulR_ge0; exact/Dist.ge0.
- move=> a1 Ha1.
  case/boolP : (g a1 c == R0 :> R) => [/eqP -> | ga1c]; first by rewrite mulR0.
  case/boolP : (f a0 a1 == R0 :> R) => [/eqP -> | fa0a1]; first by rewrite mul0R.
  case/bigfcupP : Hc.
  exists (g a1); last by rewrite mem_finsupp.
  rewrite andbT.
  apply/imfsetP; exists a1 => //=.
  by rewrite imfset_id mem_finsupp.
Qed.

Definition Distfmap (A B : choiceType) (f : A -> B) (d : Dist A) : Dist B :=
  DistBind.d d (fun a => Dist1.d (f a)).

Lemma Distfmap_id (A : choiceType) : Distfmap (@id A) = @id (Dist A).
Proof. by rewrite boolp.funeqE => a; rewrite /Distfmap DistBindp1. Qed.

Lemma Distfmap_comp (A B C : choiceType) (g : B -> C) (h : A -> B) :
  Distfmap (g \o h) = Distfmap g \o Distfmap h.
Proof.
rewrite boolp.funeqE => d; rewrite /Distfmap /= DistBindA; congr DistBind.d.
by rewrite boolp.funeqE => a; rewrite DistBind1f.
Qed.

Lemma supp_Distfmap_Dist1 (A : choiceType) d :
  finsupp (Distfmap (@Dist1.d A) d) = [fset Dist1.d x | x in finsupp d]%fset.
Proof.
rewrite /Distfmap DistBind.supp; apply/fsetP => d'.
apply/bigfcupP/imfsetP => [[D]|].
  rewrite andbT => /imfsetP[a /=]; rewrite imfset_id => ad ->{D}.
  by rewrite Dist1.supp inE => /eqP ->{d'}; exists a.
case=> a /= ad -> {d'}; exists (Dist1.d (Dist1.d a)).
  rewrite andbT; apply/imfsetP; exists a => //=; by rewrite imfset_id.
by rewrite Dist1.supp inE.
Qed.

Module Dist_of_dist.
Section def.
Variable (A : finType) (P : dist A).
Let D := [fset a0 : A | P a0 != 0].
Definition f : {fsfun A -> R with 0} := [fsfun a in D => P a | 0].
Let f0 a : a \in finsupp f -> 0 < f a.
Proof.
rewrite fsfunE mem_finsupp /f fsfunE.
case: ifPn => [_|]; by [rewrite dist_gt0 | rewrite eqxx].
Qed.
Let f1 : \sum_(a <- finsupp f) f a = 1.
Proof.
rewrite -[RHS](epmf1 P) [in RHS](bigID (fun x => x \in finsupp f)) /=.
rewrite [in X in _ = (_ + X)%R]big1 ?addR0; last first.
  move=> a; rewrite memNfinsupp fsfunE !inE /=.
  by case: ifPn => [_ /eqP //|]; rewrite negbK => /eqP.
rewrite (@eq_fbigr _ _ _ _ _ _ _ (fun i => P i)) /=; last first.
  move=> a; rewrite mem_finsupp fsfunE !inE /=; case: ifPn => //; by rewrite eqxx.
exact/big_uniq/fset_uniq.
Qed.
Definition d : Dist A := makeDist f0 f1.
End def.
End Dist_of_dist.

Module Dist_crop0.
Section def.
Variables (A : choiceType) (P : Dist A).
Definition D := [fset a : finsupp P | true].
Definition f' : {ffun finsupp P -> R} := [ffun a => P (fsval a)].
Definition f : {fsfun finsupp P -> R with 0} := [fsfun x in D  => f' x | 0].
Lemma f0 a : a \in finsupp f -> 0 < f a.
Proof.
move=> _; rewrite /f fsfunE ifT.
  rewrite /f' ffunE; exact: Dist.gt0.
by rewrite /D inE /= inE.
Qed.
Lemma f1 : \sum_(a <- finsupp f) f a = 1.
Proof.
rewrite -(Dist.f1 P) !big_seq_fsetE /=.
have hP (a : [finType of finsupp P]) : a \in finsupp f.
  by rewrite mem_finsupp fsfunE ffunE inE -mem_finsupp fsvalP.
pose h a := FSetSub (hP a).
rewrite (reindex h) /=.
  apply eq_bigr => i _.
  by rewrite fsfunE ffunE inE.
exists (@fsval _ _) => //= -[a] *.
by apply val_inj.
Qed.
Definition d : Dist.t [finType of finsupp P] := makeDist f0 f1.
End def.
End Dist_crop0.

Module Dist_lift_supp.
Section def.
Variables (A B : choiceType) (r : A -> B) (P : Dist B)
          (s : B -> A) (H : cancel s r).
Definition D := [fset s b | b in finsupp P].
Lemma s_inj : injective s.
Proof. exact (can_inj H). Qed.
Lemma r_surj : forall b : B, exists a : A, b = r a.
Proof. by move=> b; exists (s b); rewrite H. Qed.
Let f := [fsfun a in D => P (r a) | 0].
Lemma f0 a : a \in finsupp f -> 0 < f a.
Proof.
rewrite mem_finsupp /f fsfunE.
case: ifPn => Ha; last by rewrite eqxx.
rewrite -mem_finsupp; exact/Dist.gt0.
Qed.
Lemma DsuppE : D = finsupp f.
Proof.
apply fsetP => a.
rewrite /f /D !mem_finsupp !fsfunE.
case: ifPn; last by rewrite eqxx.
case/imfsetP => b /= Hb ->.
by rewrite H // -mem_finsupp.
Qed.
Lemma f1 : \sum_(a <- finsupp f) f a = 1.
Proof.
rewrite -DsuppE /D big_imfset /=; last by move=> i j _ _; exact: s_inj.
rewrite (eq_bigr P) ?Dist.f1 // => i _; rewrite /f fsfunE /D H.
apply/eqP; case: ifPn => //; apply: contraNT => Pi0.
by apply/imfsetP => /=; exists i => //; rewrite mem_finsupp eq_sym.
Qed.
Definition d := locked (makeDist f0 f1).
Lemma dE a : d a = if a \in [fset s b | b in finsupp P] then P (r a) else 0.
Proof. by rewrite /d; unlock => /=; rewrite fsfunE. Qed.
End def.
End Dist_lift_supp.

Module dist_of_Dist.
Section def.
Variable (A : choiceType) (P : Dist A).
Definition D := [finType of finsupp P] : finType.
Definition f := [ffun d : D => P (fsval d)].
Lemma f0 b : 0 <= f b. Proof. rewrite ffunE; by apply Dist.ge0. Qed.
Lemma f1 : \sum_(b in D) f b = 1.
Proof.
rewrite -(Dist.f1 P) big_seq_fsetE /=; apply eq_bigr => a; by rewrite ffunE.
Qed.
Definition d : dist D := locked (proba.makeDist f0 f1).
End def.
Module Exports.
Notation dist_of_Dist := d.
End Exports.
End dist_of_Dist.
Export dist_of_Dist.Exports.

Section dist_of_Dist_lemmas.
Variable (A : choiceType) (d : Dist A).
Lemma dist_of_DistE i : dist_of_Dist d i = d (fsval i).
Proof. by rewrite /dist_of_Dist; unlock; rewrite ffunE; reflexivity. Qed.
Lemma dist_of_DistDE : dist_of_Dist.D d = [finType of finsupp d].
Proof. reflexivity. Qed.
End dist_of_Dist_lemmas.

Module dist_of_finDist.
Section def.
Variable (A : finType) (P : Dist A).
Definition f := [ffun d : A => P d].
Lemma f0 b : 0 <= f b. Proof. rewrite ffunE; by apply Dist.ge0. Qed.
Lemma f1 : \sum_(b in A) f b = 1.
Proof.
rewrite -(Dist.f1 P) (bigID (fun x => x \in finsupp P)) /=.
rewrite [X in (_ + X = _)%R](_ : _ = 0) ?addR0.
  by rewrite big_uniq /= ?fset_uniq //; apply eq_bigr => i _; rewrite ffunE.
by rewrite big1 // => a; rewrite mem_finsupp negbK ffunE => /eqP.
Qed.
Definition d : dist A := locked (proba.makeDist f0 f1).
Lemma dE a : d a = P a.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
End def.
Module Exports.
Notation dist_of_finDist := d.
End Exports.
End dist_of_finDist.
Export dist_of_finDist.Exports.

Module ConvDist.
Section def.
Local Open Scope proba_scope.
Variables (A : choiceType) (n : nat) (e : {dist 'I_n}) (g : 'I_n -> Dist A).
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
rewrite -(@eqR_mul2l (e i)) ?mulR0; last exact/gtR_eqF.
move/prsumr_eq0P : H; apply => //= j _.
apply/mulR_ge0; [exact/dist_ge0 | exact/Dist.ge0].
Qed.
Lemma f0 a : a \in finsupp f -> 0 < f a.
Proof.
rewrite mem_finsupp fsfunE; case: ifPn => [_ ?|]; last by rewrite eqxx.
rewrite ltR_neqAle; split; first exact/nesym/eqP.
apply/rsumr_ge0 => i _; apply/mulR_ge0; [exact/dist_ge0 | exact/Dist.ge0].
Qed.
Lemma f1 : \sum_(a <- finsupp f) f a = 1.
Proof.
rewrite {2}/f; evar (h : A -> R); rewrite (eq_big_seq h); last first.
  move=> b; rewrite supp => bD.
  rewrite fsfunE bD /h; reflexivity.
rewrite {}/h exchange_big /= -[RHS](epmf1 e) /=; apply eq_bigr => i _.
rewrite -big_distrr /=.
case/boolP : (e i == R0 :> R) => [/eqP -> | ei0]; first by rewrite mul0R.
rewrite -(@big_fset_incl _ _ _ _ (finsupp (g i))).
- by rewrite Dist.f1 mulR1.
- rewrite supp /D bigfcup_sup //; exact/ltRP/dist_gt0.
- by move=> a _; rewrite memNfinsupp => /eqP.
Qed.
Definition d : Dist A := locked (makeDist f0 f1).
Lemma dE a : d a = [fsfun a in D => \sum_(i < n) e i * g i a | 0] a.
Proof. by rewrite /d; unlock; rewrite fsfunE. Qed.
End def.
End ConvDist.

Module Conv2Dist.
Section def.
Variables (A : choiceType) (d1 d2 : Dist A) (p : prob).
Definition d : Dist A := locked
  (ConvDist.d (I2Dist.d p) (fun i => if i == ord0 then d1 else d2)).
Local Open Scope reals_ext_scope.
Lemma dE a : (d a = p * d1 a + p.~ * d2 a)%R.
Proof.
rewrite /d; unlock => /=.
rewrite ConvDist.dE fsfunE.
case: ifPn => [?|H].
  rewrite !big_ord_recl big_ord0 /= addR0 !I2Dist.dE.
  by rewrite eqxx eq_sym (negbTE (neq_lift _ _)).
case/boolP : (p == R0 :> R) => [/eqP |] p0.
  rewrite p0 mul0R add0R onem0 mul1R.
  apply/esym/eqP; rewrite -memNfinsupp.
  apply: contra H => H.
  rewrite /ConvDist.D; apply/bigfcupP; exists (lift ord0 ord0).
  rewrite mem_index_enum /= I2Dist.dE eq_sym (negbTE (neq_lift _ _)) p0 onem0; exact/ltRP.
  by rewrite eq_sym (negbTE (neq_lift _ _)).
have d1a0 : d1 a = 0.
  apply/eqP; rewrite -memNfinsupp.
  apply: contra H => H.
  rewrite /ConvDist.D; apply/bigfcupP; exists ord0; last by rewrite eqxx.
  rewrite mem_index_enum /= I2Dist.dE eqxx; exact/ltRP/prob_gt0.
rewrite d1a0 mulR0 add0R.
case/boolP : (p == R1 :> R) => [/eqP |] p1; first by rewrite p1 onem1 mul0R.
suff : d2 a = 0 by move=> ->; rewrite mulR0.
apply/eqP; rewrite -memNfinsupp.
apply: contra H => H.
rewrite /ConvDist.D; apply/bigfcupP; exists (lift ord0 ord0).
rewrite mem_index_enum /= I2Dist.dE eq_sym (negbTE (neq_lift _ _)).
exact/ltRP/onem_gt0/prob_lt1.
by rewrite eq_sym (negbTE (neq_lift _ _)).
Qed.
End def.
Section prop.
Variables (A : choiceType).
Implicit Types a b c : Dist A.
Local Notation "x <| p |> y" := (d x y p).
Local Open Scope reals_ext_scope.
Lemma conv0 (mx my : Dist A) : mx <| `Pr 0 |> my = my.
Proof. by apply/Dist_ext => a; rewrite Conv2Dist.dE /= mul0R add0R onem0 mul1R. Qed.
Lemma conv1 (mx my : Dist A) : mx <| `Pr 1 |> my = mx.
Proof. by apply/Dist_ext => a; rewrite Conv2Dist.dE /= mul1R onem1 mul0R addR0. Qed.
Lemma convmm p : idempotent (fun x y => x <| p |> y : Dist A).
Proof. by move=> d; apply/Dist_ext => a; rewrite Conv2Dist.dE -mulRDl onemKC mul1R. Qed.
Lemma convC (p : prob) (mx my : Dist A) : mx <| p |> my = my <| `Pr p.~ |> mx.
Proof. by apply/Dist_ext => a; rewrite 2!Conv2Dist.dE /= onemK addRC. Qed.
Lemma convA (p q r s : prob) (mx my mz : Dist A) :
  p = r * s :> R /\ s.~ = p.~ * q.~ ->
  mx <| p |> (my <| q |> mz) = (mx <| r |> my) <| s |> mz.
Proof.
move=> [Hp Hs]; apply/Dist_ext => a.
rewrite !Conv2Dist.dE [in RHS]mulRDr (@mulRCA _ r) (@mulRA r) -Hp -addRA; congr (_ + _)%R.
rewrite mulRDr (@mulRA p.~ q.~) -Hs; congr (_ + _)%R.
rewrite !mulRA; congr (_ * _)%R.
rewrite -p_of_rsE in Hp.
move/(congr1 onem) : Hs; rewrite onemK => Hs.
rewrite -s_of_pqE in Hs.
case/boolP : (r == `Pr 0 :> prob) => [/eqP | ] r0.
  rewrite r0 /= onem0 mulR1 Hs s_of_pqE.
  by rewrite Hp p_of_rsE r0 /= mul0R onem0 !mul1R onemK.
case/boolP : (s == `Pr 0 :> prob) => [/eqP | ] s0.
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
Lemma convA' (p q : prob) (a b c : Dist A) :
  d a (d b c q) p = d (d a b (r_of_pq p q)) c (s_of_pq p q).
Proof.
rewrite (convA (r := r_of_pq p q) (s := s_of_pq p q)) //.
rewrite {2}s_of_pqE onemK; split => //.
case/boolP : (s_of_pq p q == `Pr 0 :> prob) => s0.
- rewrite (eqP s0) mulR0; apply/eqP; move: s0.
  by apply: contraTT => /(s_of_gt0 q); rewrite prob_gt0.
- by rewrite -p_is_rs.
Qed.
Lemma incl_finsupp_conv2dist (a b : Dist A) (p : prob) :
  p != `Pr 0 -> finsupp a `<=` finsupp (a <|p|> b).
Proof.
move=> p0.
apply/fsubsetP => a1.
rewrite !mem_finsupp => aa1.
rewrite Conv2Dist.dE.
apply: contra aa1 => /eqP.
rewrite paddR_eq0; last 2 first.
  apply/mulR_ge0; [exact/prob_ge0 | exact/Dist.ge0].
  apply/mulR_ge0; [exact/prob_ge0 | exact/Dist.ge0].
case.
rewrite mulR_eq0 => -[p0'|/eqP //].
exfalso.
move/eqP : p0; apply.
apply/prob_ext; by rewrite p0'.
Qed.
Lemma tech1 (B : choiceType) (a b : Dist A) (f : A -> Dist B) (p : prob) (a0 : A) (b0 : B) (b0a0 : b0 \in finsupp (f a0)) :
  p != `Pr 0 ->
  \sum_(i <- finsupp (a <|p|> b)) (a i * (f i) b0) = (DistBind.d a f) b0.
Proof.
move=> p0.
rewrite DistBind.dE.
case: ifPn => [/bigfcupP[dB] | ].
- rewrite andbT; case/imfsetP => a1 /=.
  rewrite imfset_id => a1a ->{dB} b0a2.
  apply/esym/big_fset_incl.
    exact/incl_finsupp_conv2dist.
  by move=> a3 Ha3; rewrite memNfinsupp => /eqP ->; rewrite mul0R.
- move=> Hb0.
  apply/prsumr_seq_eq0P.
  + exact/fset_uniq.
  + move=> a1 _; apply/mulR_ge0; exact/Dist.ge0.
  + move=> a1 Ha1.
    case/boolP : (a a1 == 0 :> R) => [/eqP -> |aa10]; first by rewrite mul0R.
    rewrite mulR_eq0; right.
    apply/eqP; rewrite -memNfinsupp.
    apply: contra Hb0 => Hb0.
    apply/bigfcupP; exists (f a1) => //; rewrite andbT.
    by apply/imfsetP; exists a1 => //=; rewrite imfset_id mem_finsupp.
Qed.
Lemma bind_left_distr (B : choiceType) (p : prob) a b (f : A -> Dist B) :
  DistBind.d (a <| p |> b) f = DistBind.d a f <| p |> DistBind.d b f.
Proof.
apply/Dist_ext => b0 /=; rewrite DistBind.dE Conv2Dist.dE.
case/boolP : (p == `Pr 0 :> prob) => [/eqP -> | p0].
  by rewrite conv0 mul0R add0R onem0 mul1R DistBind.dE.
case/boolP : (p == `Pr 1 :> prob) => [/eqP -> | p1].
  by rewrite conv1 mul1R onem1 mul0R addR0 DistBind.dE.
case: ifPn => [/bigfcupP[dB] | ].
  rewrite andbT.
  case/imfsetP => a0 /=.
  rewrite inE /= => Ha0 ->{dB} b0a0.
  evar (h : A -> R); rewrite (eq_bigr h); last first.
    move=> a1 _.
    rewrite Conv2Dist.dE (@mulRDl _ _ (f a1 b0)) -!mulRA /h; reflexivity.
  rewrite {}/h big_split /= -2!big_distrr /=.
  congr (_ * _ + _ * _)%R.
  exact/(tech1 _ _ b0a0).
  rewrite convC (tech1 _ _ b0a0) //.
  apply: contra p1 => /eqP.
  move/(congr1 (fun x : prob => x.~)).
  rewrite onemK onem0 => p1.
  exact/eqP/prob_ext.
move=> Hb0.
apply/esym/paddR_eq0.
  apply/mulR_ge0; [exact/prob_ge0 | exact/Dist.ge0].
  apply/mulR_ge0; [exact/prob_ge0 | exact/Dist.ge0].
split.
- rewrite mulR_eq0; right.
  rewrite DistBind.dE; case: ifPn => // abs.
  exfalso.
  move/negP : Hb0; apply.
  case/bigfcupP : abs => dB.
  rewrite andbT => /imfsetP[a0 /=] /imfsetP[a1 /=] a1a ->{a0} ->{dB} Hb0.
  apply/bigfcupP; exists (f a1) => //; rewrite andbT.
  apply/imfsetP; exists a1 => //=.
  rewrite imfset_id.
  move: a1 a1a {Hb0}; apply/fsubsetP.
  exact/incl_finsupp_conv2dist.
- (* TODO: copype *) rewrite mulR_eq0; right.
  rewrite DistBind.dE; case: ifPn => // abs.
  exfalso.
  move/negP : Hb0; apply.
  case/bigfcupP : abs => dB; rewrite andbT.
  move => /imfsetP[a0 /=] /imfsetP[a1 /=] a1a ->{a0} ->{dB} Hb0.
  apply/bigfcupP; exists (f a1) => //; rewrite andbT.
  apply/imfsetP; exists a1 => //=.
  rewrite imfset_id.
  move: a1 a1a {Hb0}; apply/fsubsetP.
  rewrite convC; apply/incl_finsupp_conv2dist.
  apply: contra p1 => /eqP.
  move/(congr1 (fun x : prob => x.~)).
  rewrite onemK onem0 => p1; exact/eqP/prob_ext.
Qed.
End prop.
End Conv2Dist.

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
