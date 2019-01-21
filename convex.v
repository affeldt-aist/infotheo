(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.
From mathcomp Require Import boolp classical_sets.
Require Import Reals Lra ProofIrrelevance FunctionalExtensionality.
Require Import ssrR Reals_ext Ranalysis_ext ssr_ext ssralg_ext logb Rbigop.
Require Import proba.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "x <| p |> y" (format "x  <| p |>  y", at level 50).
Reserved Notation "{ 'convex_set' T }" (format "{ 'convex_set'  T }").

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.

Section PR_to_classical_sets.

Variable T : Type.
Implicit Types A B C : set T.

Local Open Scope classical_set_scope.

Lemma imsetP T1 T2 (D : set T1) (f : T1 -> T2) b :
  reflect (exists2 a, a \in D & b = f a) (b \in f @` D).
Proof.
apply: (iffP idP) => [|[a aC ->]].
by rewrite in_setE => -[a Ca <-{b}]; exists a => //; rewrite in_setE.
by rewrite in_setE; apply/classical_sets.imageP; rewrite -in_setE.
Qed.

Lemma in_setU A B x : (x \in A `|` B) = (x \in A) || (x \in B) :> Prop.
Proof.
rewrite propeqE; split => [ | ]; last first.
  move/orP => -[]; rewrite 2!in_setE => ?; by [left|right].
rewrite in_setE => -[?|?]; apply/orP; rewrite 2!in_setE; tauto.
Qed.

Lemma set0U A : set0 `|` A = A.
Proof. rewrite funeqE => t; rewrite propeqE; split; by [case|right]. Qed.

Lemma setU0 A : A `|` set0 = A.
Proof. rewrite funeqE => t; rewrite propeqE; split; by [case|left]. Qed.

Lemma sub0set A : set0 `<=` A.
Proof. by []. Qed.

Lemma subset0 A : (A `<=` set0) = (A = set0).
Proof. rewrite propeqE; split => [?|-> //]; exact/eqEsubset. Qed.

Lemma subUset A B C : (B `|` C `<=` A) = ((B `<=` A) /\ (C `<=` A)).
Proof.
rewrite propeqE; split => [H|H]; first by split => x Hx; apply H; [left|right].
move=> x [] Hx; [exact: (proj1 H)|exact: (proj2 H)].
Qed.

Lemma setU_eq0 A B : (A `|` B = set0) = ((A = set0) /\ (B = set0)).
Proof. by rewrite -!subset0 subUset. Qed.

Lemma set0P A : (A != set0) <-> (A !=set0).
Proof.
split; [move=> A_neq0|by case=> t tA; apply/negP => /eqP A0; rewrite A0 in tA].
apply/existsp_asboolP; rewrite -(negbK `[exists _, _]); apply/negP.
rewrite existsbE => /forallp_asboolPn H.
move/negP : A_neq0; apply; apply/eqP; rewrite funeqE => t; rewrite propeqE.
move: (H t); by rewrite asboolE.
Qed.

End PR_to_classical_sets.

Section tmp.
Local Open Scope proba_scope.
Variables (n m : nat) (d1 : {dist 'I_n}) (d2 : {dist 'I_m}) (p : prob).
Lemma ConvDist_Add (A : finType) (g : 'I_n -> dist A) (h : 'I_m -> dist A) :
  ConvDist.d
    (AddDist.d d1 d2 p)
    [ffun i => match fintype.split i with inl a => g a | inr a => h a end] =
  Conv2Dist.d (ConvDist.d d1 g) (ConvDist.d d2 h) p.
Proof.
apply/dist_ext => a.
rewrite !Conv2Dist.dE !ConvDist.dE.
rewrite 2!big_distrr /= big_split_ord /=; congr (_ + _)%R;
  apply eq_bigr => i _; rewrite AddDist.dE ffunE.
case: splitP => /= j ij.
rewrite mulRA; congr (_ * d1 _ * (g _) a)%R; exact/val_inj.
move: (ltn_ord i); by rewrite ij -ltn_subRL subnn ltn0.
case: splitP => /= j ij.
move: (ltn_ord j); by rewrite -ij -ltn_subRL subnn ltn0.
move/eqP : ij; rewrite eqn_add2l => /eqP ij.
rewrite mulRA; congr (_ * d2 _ * (h _) a)%R; exact/val_inj.
Qed.
End tmp.

Section tmp2.
Variables (A : finType) (n : nat) (g : 'I_n.+1 -> dist A) (P : {dist 'I_n.+1}).
Lemma DelDistConvex (j : 'I_n.+1) (H : (0 <= P j <= 1)%R) (Pj1 : P j != 1%R) :
  let g' := fun i : 'I_n => g (DelDist.h j i) in
  ConvDist.d P g = Conv2Dist.d (g j) (ConvDist.d (DelDist.d Pj1) g') (Prob.mk H).
Proof.
move=> g' /=; apply/dist_ext => a.
rewrite Conv2Dist.dE /= ConvDist.dE (bigD1 j) //=; congr (_ + _)%R.
rewrite ConvDist.dE big_distrr /=.
rewrite (bigID (fun i : 'I_n.+1 => (i < j)%nat)) //= (bigID (fun i : 'I_n => (i < j)%nat)) //=; congr (_ + _)%R.
  rewrite (@big_ord_narrow_cond _ _ _ j n.+1); first by rewrite ltnW.
  move=> jn; rewrite (@big_ord_narrow_cond _ _ _ j n xpredT); first by rewrite -ltnS.
  move=> jn'.
  apply/eq_big.
  by move=> /= i; apply/negP => /eqP/(congr1 val) /=; apply/eqP; rewrite ltn_eqF.
  move=> /= i _.
  rewrite DelDist.dE /= /DelDist.h /= ltn_ord D1Dist.dE /= ifF /=; last first.
    by apply/negP => /eqP/(congr1 val) /=; apply/eqP; rewrite ltn_eqF.
  rewrite mulRA mulRCA mulRV ?mulR1 ?onem_neq0 //.
  congr (P _ * _)%R; first exact/val_inj.
  rewrite /g' /DelDist.h /= ltn_ord; congr (g _ a).
  exact/val_inj.
rewrite (eq_bigl (fun i : 'I_n.+1 => (j < i)%nat)); last first.
  move=> i; by rewrite -leqNgt eq_sym -ltn_neqAle.
rewrite (eq_bigl (fun i : 'I_n => (j <= i)%nat)); last first.
  move=> i; by rewrite -leqNgt.
rewrite big_mkcond.
rewrite big_ord_recl ltn0 /= add0R.
rewrite [in RHS]big_mkcond.
apply eq_bigr => i _.
rewrite /bump add1n ltnS; case: ifPn => // ji.
rewrite DelDist.dE D1Dist.dE /DelDist.h /= ltnNge ji /= ifF; last first.
  apply/eqP => /(congr1 val) => /=.
  rewrite /bump add1n => ij.
  move: ji; apply/negP; by rewrite -ij ltnn.
rewrite /Rdiv mulRAC [in RHS] mulRC -mulRA mulVR // ?mulR1 ?onem_neq0 //.
by rewrite /g' /DelDist.h ltnNge ji.
Qed.
End tmp2.

(* technical device *)
Module CodomDDist.
Section def.
Local Open Scope classical_set_scope.
Variables (A : Type) (n : nat) (g : 'I_n -> A) (e : {dist 'I_n}) (y : set A).
Definition f : 'I_n -> R := fun i => if g i \in y then e i else 0%R.
Lemma f0 i : (0 <= f i)%R.
Proof. rewrite /f; case: ifPn => _; [exact/dist_ge0|exact/leRR]. Qed.
Lemma f1 (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, g i \in x -> e i = 0%R) :
  (\rsum_(i < n) f i = 1)%R.
Proof.
rewrite /f -(pmf1 e) /=.
apply eq_bigr => i _.
case: ifPn => // giy.
rewrite ge //.
have : g i \in x `|` y by rewrite in_setE; apply/gX; by exists i.
rewrite in_setU => /orP[|] //.
by rewrite (negbTE giy).
Qed.
Definition d (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, g i \in x -> e i = 0%R) : {dist 'I_n} :=
  locked (makeDist f0 (f1 gX ge)).
Lemma dE (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, g i \in x -> e i = 0%R) i :
  d gX ge i = if g i \in y then e i else 0%R.
Proof. by rewrite /d; unlock. Qed.
Lemma f1' (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, (g i \in x) && (g i \notin y) -> e i = 0%R) :
  (\rsum_(i < n) f i = 1)%R.
Proof.
rewrite /f -(pmf1 e) /=.
apply eq_bigr => i _.
case: ifPn => // giy.
rewrite ge //.
have : g i \in x `|` y by rewrite in_setE; apply/gX; by exists i.
rewrite in_setU => /orP[|].
  by rewrite (negbTE giy) andbT.
by rewrite (negbTE giy).
Qed.
Definition d' (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, (g i \in x) && (g i \notin y) -> e i = 0%R) :=
  locked (makeDist f0 (f1' gX ge)).
Lemma dE' (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, (g i \in x) && (g i \notin y) -> e i = 0%R) i :
  d' gX ge i = if g i \in y then e i else 0%R.
Proof. by rewrite /d'; unlock. Qed.
End def.
End CodomDDist.

Module ConvexSpace.
Record class_of (car : Type) : Type := Class {
  conv : car -> car -> prob -> car where "a <| p |> b" := (conv a b p);
  _ : forall a b, a <| `Pr 1 |> b = a ;
  _ : forall a p, a <| p |> a = a ;
  _ : forall a b p, a <| p |> b = b <| `Pr p.~ |> a;
  _ : forall (p q r s : prob) (a b c : car),
      p = (r * s)%R :> R -> (s.~ = p.~ * q.~)%R ->
      a <| p |> (b <| q |> c) = (a <| r |> b) <| s |> c
}.
Structure t : Type := Pack { car : Type ; class : class_of car }.
Module Exports.
Definition Conv (T : t) : car T -> car T -> prob -> car T :=
  let: Pack _ (Class x _ _ _ _) := T in x.
Arguments Conv {T} : simpl never.
Notation "x <| p |> y" := (Conv x y p) : convex_scope.
Notation convType := t.
Coercion car : convType >-> Sortclass.
End Exports.
End ConvexSpace.
Export ConvexSpace.Exports.

Local Open Scope convex_scope.

Section convex_space_interface.
Variables A : convType.
Implicit Types a b c : A.
Implicit Types p q r s : prob.
Lemma conv1 a b : a <| `Pr 1 |> b = a.
Proof. by case: A a b => ? []. Qed.
Lemma convmm a p : a <| p |> a = a.
Proof. by case: A a => ? []. Qed.
Lemma convC a b p : a <| p |> b = b <| `Pr p.~ |> a.
Proof. by case: A a b => ? []. Qed.
Lemma convA p q r s a b c :
  p = (r * s)%R :> R -> (s.~ = p.~ * q.~)%R ->
  a <| p |> (b <| q |> c) = (a <| r |> b) <| s |> c.
Proof.
case: A a b c p q r s => ? [] f H0 H1 H2 H3 d0 d1 d2 p q r s K1 K2.
by rewrite /Conv; rewrite (H3 _ _ _ _ _ _ _ K1 K2).
Qed.
End convex_space_interface.

Section convex_space_prop.
Variables A : convType.
Implicit Types a b : A.
Lemma conv0 a b : a <| `Pr 0 |> b = b.
Proof.
rewrite convC (_ : `Pr _ = `Pr 1) ?conv1 //=; apply prob_ext; exact: onem0.
Qed.

Local Open Scope vec_ext_scope.

Fixpoint Convn n : {dist 'I_n} -> ('I_n -> A) -> A :=
  match n return forall (e : {dist 'I_n}) (g : 'I_n -> A), A with
  | O => fun e g => False_rect A (distI0_False e)
  | m.+1 => fun e g =>
    match eqVneq (e ord0) 1%R with
    | left _ => g ord0
    | right H => let G := fun i => g (DelDist.h ord0 i) in
      g ord0 <| Prob.mk (conj (dist_ge0 e ord0) (dist_max e ord0)) |> Convn (DelDist.d H) G
    end
  end.

Lemma convn1E a e : Convn e (fun _ : 'I_1 => a) = a.
Proof.
rewrite /=; case: eqVneq => [//|H]; exfalso; move: H.
by rewrite dist_supp_singleP dist_supp1 eqxx.
Qed.

Lemma convnE0 n g (d : {dist 'I_n.+1}) (d01 : d ord0 == 1%R) : Convn d g = g ord0.
Proof.
rewrite /=; case: eqVneq => [//|H]; exfalso; by rewrite d01 in H.
Qed.

Lemma convnE n g (d : {dist 'I_n.+1}) (i1 : d ord0 != 1%R) :
  Convn d g = g ord0
              <| Prob.mk (conj (dist_ge0 d ord0) (dist_max d ord0)) |>
              Convn (DelDist.d i1) (fun x => g (DelDist.h ord0 x)).
Proof.
rewrite /=; case: eqVneq => /= H.
exfalso; by rewrite H eqxx in i1.
by rewrite (ProofIrrelevance.proof_irrelevance _ H i1).
Qed.

Lemma convn_proj n g (d : {dist 'I_n}) i : d i = R1 -> Convn d g = g i.
Proof.
elim: n g d i => [d d0|n IH g d i di1]; first by move: (distI0_False d0).
case/boolP : (i == ord0) => [/eqP|]i0; first by subst i; rewrite convnE0 // di1.
have d00 : d ord0 = R0 by move/eqP/dist1P : di1 => -> //; rewrite eq_sym.
rewrite convnE; first by rewrite d00; apply/eqP; lra.
move=> d01.
rewrite (_ : Prob.mk _ = `Pr 0); last exact/prob_ext.
rewrite conv0.
move=> [:Hj].
have @j : 'I_n.
  apply: (@Ordinal _ i.-1).
  abstract: Hj; by rewrite prednK // ?lt0n // -ltnS.
rewrite (IH _ _ j) // ?ltn0.
  congr g; apply val_inj => /=.
  by rewrite /bump leq0n add1n prednK // lt0n.
rewrite DelDist.dE /DelDist.h ltn0 D1Dist.dE eq_sym (negbTE (neq_lift _ _ )).
rewrite d00 subR0 divR1 -di1; congr (d _).
apply val_inj => /=; by rewrite /bump leq0n add1n prednK // lt0n.
Qed.

End convex_space_prop.

Section is_convex_set.
Local Open Scope classical_set_scope.
Variable A : convType.

Definition is_convex_set (D : set A) : bool :=
  `[<forall x y t, x \in D -> y \in D -> x <| t |> y \in D>].

Lemma is_convex_set0 : is_convex_set set0.
Proof. apply/asboolP => x y p; by rewrite in_setE. Qed.

Lemma is_convex_setT : is_convex_set setT.
Proof. apply/asboolP => ? ? ? _ _; by rewrite in_setE. Qed.

Definition is_convex_set_n (X : set A) : bool :=
  `[< forall n (g : 'I_n -> A) (d : {dist 'I_n}), g @` setT `<=` X -> Convn d g \in X >].

Lemma is_convex_setP (X : set A) : is_convex_set X = is_convex_set_n X.
Proof.
apply/idP/idP => H; apply/asboolP; last first.
  move=> x y p xX yX.
  case/boolP : (p == `Pr 1) => [/eqP ->|p1]; first by rewrite conv1.
  set g : 'I_2 -> A := fun i => if i == ord0 then x else y.
  have gX : g @` setT `<=` X by move=> a -[i _ <-]; rewrite -in_setE /g; case: ifPn.
  move/asboolP : H => /(_ _ g (I2Dist.d p) gX).
  rewrite convnE; first by rewrite I2Dist.dE eqxx.
  move=> p1'.
  rewrite {1}/g eqxx (_ : Prob.mk _ = p); last first.
    by apply prob_ext => /=; rewrite I2Dist.dE eqxx.
  by rewrite (_ : Convn _ _ = y) // (_ : (fun _ => _) = (fun=> y)) ?convn1E.
elim => [g d|n IH g d]; first by move: (distI0_False d).
destruct n as [|n] => gX.
  rewrite {IH} (@convn_proj _ _ _ _ ord0) //.
  rewrite in_setE; exact/gX/classical_sets.imageP.
  by apply/eqP; rewrite dist_supp_singleP dist_supp1.
case/boolP : (d ord0 == 1%R) => [/eqP|]d01.
  suff -> : Convn d g = g ord0 by rewrite in_setE; apply gX; exists ord0.
  by rewrite (@convn_proj _ _ _ _ ord0).
set D : {dist 'I_n.+1} := DelDist.d d01.
pose G (i : 'I_n.+1) : A := g (DelDist.h (@ord0 _) i).
have : G @` setT `<=` X.
  by move=> x -[i _ <-{x}]; rewrite /G /DelDist.h ltn0; apply gX; exists ((lift ord0 i)).
move/(IH _ D) => {IH}IH.
rewrite convnE //.
move/asboolP : H; apply => //.
rewrite in_setE; exact/gX/classical_sets.imageP.
Qed.
End is_convex_set.

Section hull_def.
Local Open Scope classical_set_scope.
Definition hull (A : convType) (X : set A) : set A :=
  [set d | exists n, exists g : 'I_n -> A, exists e : {dist 'I_n}, g @` setT `<=` X /\ d = Convn e g].
End hull_def.

Section hull_prop.
Variable A : convType.
Lemma hull_mem (X : set A) x : x \in X -> x \in hull X.
Proof.
move=> xX.
rewrite in_setE /hull.
exists 1, (fun=> x), (Dist1.d ord0); split; last by rewrite convn1E.
move=> d -[i _ <-]; by rewrite -in_setE.
Qed.
Lemma hull0 : hull set0 = set0 :> set A.
Proof.
rewrite funeqE => d; rewrite propeqE; split => //.
case=> n [g [e [gX ->{d}]]].
destruct n as [|n].
  by move: (distI0_False e).
exfalso; apply: (gX (g ord0)); exact/imageP.
Qed.
Lemma hull_eq0 (X : set A) : (hull X == set0) = (X == set0).
Proof.
apply/idP/idP=> [/eqP abs|]; last by move=> /eqP ->; rewrite hull0.
apply/negPn/negP => /set0P[/= d]; rewrite -in_setE => dX.
move: abs; rewrite funeqE => /(_ d); rewrite propeqE /set0 => -[H _]; apply H.
by rewrite -in_setE; apply: hull_mem.
Qed.
Lemma mem_hull_setU (x y : set A) (a0 a1 : A) p :
  a0 \in x -> a1 \in y -> a0 <| p |> a1 \in hull (x `|` y).
Proof.
move=> a0x a1y.
rewrite in_setE.
exists 2, (fun i => if i == ord0 then a0 else a1), (I2Dist.d p); split => /=.
  move=> a2.
  rewrite -in_setE.
  case/imsetP => i _ ->{a2} /=.
  case: ifPn => _.
  by rewrite -in_setE in_setU a0x.
  by rewrite -in_setE in_setU orbC a1y.
case: eqVneq => [|H].
  rewrite I2Dist.dE eqxx /= => p1.
  suff -> : p = `Pr 1 by rewrite conv1.
  exact/prob_ext.
congr (_ <| _ |> _); last by apply prob_ext => /=; rewrite I2Dist.dE eqxx.
case: eqVneq => H' //.
exfalso.
move: H'; rewrite DelDist.dE D1Dist.dE /DelDist.h ltnn.
have lift0' : lift ord0 ord0 != ord0 :> 'I_2.
  by apply/eqP => /(congr1 val) /=; rewrite /bump leq0n.
rewrite (negbTE lift0') I2Dist.dE (negbTE lift0') I2Dist.dE eqxx divRR ?eqxx //.
by move: H; rewrite I2Dist.dE eqxx onem_neq0.
Qed.
Lemma mem_hull_setU_left (x y : set A) (a : A) : a \in x -> a \in hull (x `|` y).
Proof. by move=> ax; apply: hull_mem; rewrite in_setU ax. Qed.

End hull_prop.

Module CSet.
Section def.
Local Open Scope classical_set_scope.
Variable A : convType.
Record t : Type := mk {
  car :> set A ;
  H : is_convex_set car }.
End def.
End CSet.
Notation convex_set := CSet.t.
Coercion CSet.car : convex_set >-> set.

Definition convex_set_of (A : convType) :=
  fun phT : phant (ConvexSpace.car A) => convex_set A.
Notation "{ 'convex_set' T }" := (convex_set_of (Phant T)) : convex_scope.

Section cset_canonical.
Variable (A : convType).
Canonical cset_subType := [subType for @CSet.car A].
Canonical cset_predType :=
  Eval hnf in mkPredType (fun t : convex_set A => (fun x => x \in CSet.car t)).
Definition cset_eqMixin := Eval hnf in [eqMixin of convex_set A by <:].
Canonical cset_eqType := Eval hnf in EqType (convex_set A) cset_eqMixin.
End cset_canonical.

Section CSet_prop.
Local Open Scope classical_set_scope.
Variable A : convType.

Definition cset0 : {convex_set A} := CSet.mk (is_convex_set0 A).

Lemma cset0P (x : {convex_set A}) : (x == cset0) = (x == set0 :> set _).
Proof. by case: x. Qed.

Lemma cset0PN (x : {convex_set A}) : (x != cset0) <-> (x !=set0).
Proof.
rewrite cset0P; case: x => //= x Hx; split; last first.
  case=> a xa; apply/eqP => x0; move: xa; by rewrite x0.
by case/set0P => /= d dx; exists d.
Qed.

Lemma hull_cset (x : {convex_set A}) : hull x = x.
Proof.
rewrite predeqE => d; split.
- move=> -[n [g [e [gX ->{d}]]]].
  move: (CSet.H x); rewrite is_convex_setP /is_convex_set_n => /asboolP/(_ _ g e gX).
  by rewrite in_setE.
- by rewrite -in_setE => /hull_mem; rewrite in_setE.
Qed.
End CSet_prop.

Section R_convex_space.
Definition avg a b (t : prob) := (t * a + t.~ * b)%R.
Lemma avg1 a b : avg a b (`Pr 1) = a.
Proof. by rewrite /avg /= mul1R onem1 mul0R addR0. Qed.
Lemma avgI x (p : prob) : avg x x p = x.
Proof. by rewrite /avg -mulRDl onemKC mul1R. Qed.
Lemma avgC x y (p : prob) : avg x y p = avg y x `Pr p.~.
Proof. by rewrite /avg onemK addRC. Qed.
Lemma avgA (p q r s : prob) (d0 d1 d2 : R) :
  p = (r * s)%R :> R ->
  s.~ = (p.~ * q.~)%R ->
  avg d0 (avg d1 d2 q) p = avg (avg d0 d1 r) d2 s.
Proof.
move: p q r s => -[p Hp] [q Hq] [r Hr] [s Hs] /= K1.
rewrite /avg /onem => K2 /=.
rewrite (mulRDr s) -addRA (mulRA s) (mulRC s r) -K1; congr (_ + _)%R.
rewrite K2 mulRDr -(mulRA (1 - p)%R); congr (_ + _)%R.
rewrite !mulRA; congr (_ * _)%R.
rewrite mulRBl mulRBr mulR1 (mulRC s r) -K1; lra.
Qed.
Definition R_convMixin := ConvexSpace.Class avg1 avgI avgC avgA.
Canonical R_convType := ConvexSpace.Pack R_convMixin.
Definition avgn n (g : 'I_n -> R) (e : {dist 'I_n}) := \rsum_(i < n) (e i * g i)%R.
Lemma avgnE n (g : 'I_n -> R) e : Convn e g = avgn g e.
Proof.
elim: n g e => /= [g e|n IH g e]; first by move: (distI0_False e).
case: eqVneq => H /=.
  rewrite /avgn big_ord_recl /= H mul1R big1 ?addR0 // => j _.
  by move/eqP/dist1P : H => ->; rewrite ?mul0R.
rewrite /avgn big_ord_recl /=.
rewrite /Conv /= /avg /=; congr (_ + _)%R.
rewrite IH /avgn big_distrr /=; apply eq_bigr => j _.
rewrite DelDist.dE D1Dist.dE /DelDist.h ltn0 eq_sym (negbTE (neq_lift _ _)).
by rewrite mulRAC mulRC -mulRA mulVR ?onem_neq0 // mulR1.
Qed.
End R_convex_space.

Module Funavg.
Section funavg.
Variables (A : Type) (B : convType).
Let T := A -> B.
Definition avg (x y : T) (t : prob) := fun a : A => (x a <| t |> y a).
Lemma avg1 (x y : T) : avg x y (`Pr 1) = x.
Proof.
apply FunctionalExtensionality.functional_extensionality => a.
by apply conv1.
Qed.
Lemma avgI (x : T) (p : prob) : avg x x p = x.
Proof.
apply FunctionalExtensionality.functional_extensionality => a.
by apply convmm.
Qed.
Lemma avgC (x y : T) (p : prob) : avg x y p = avg y x `Pr p.~.
Proof.
apply FunctionalExtensionality.functional_extensionality => a.
by apply convC.
Qed.
Lemma avgA (p q r s : prob) (d0 d1 d2 : T) :
  p = (r * s)%R :> R -> s.~ = (p.~ * q.~)%R ->
  avg d0 (avg d1 d2 q) p = avg (avg d0 d1 r) d2 s.
Proof.
move => *.
apply FunctionalExtensionality.functional_extensionality => a.
by apply convA.
Qed.
End funavg.
End Funavg.

Section fun_convex_space.
Variables (A : Type) (B : convType).

Definition funConvMixin := ConvexSpace.Class
  (@Funavg.avg1 A B) (@Funavg.avgI A B) (@Funavg.avgC A B) (@Funavg.avgA A B).
Canonical funConvType := ConvexSpace.Pack funConvMixin.

End fun_convex_space.

Module Depfunavg.
Section depfunavg.
Variables (A : Type) (B : A -> convType).
Let T := forall a : A , B a.
Definition avg (x y : T) (t : prob) := fun a : A => (x a <| t |> y a).
Lemma avg1 (x y : T) : avg x y (`Pr 1) = x.
Proof.
apply FunctionalExtensionality.functional_extensionality_dep => a.
by apply conv1.
Qed.
Lemma avgI (x : T) (p : prob) : avg x x p = x.
Proof.
apply FunctionalExtensionality.functional_extensionality_dep => a.
by apply convmm.
Qed.
Lemma avgC (x y : T) (p : prob) : avg x y p = avg y x `Pr p.~.
Proof.
apply FunctionalExtensionality.functional_extensionality_dep => a.
by apply convC.
Qed.
Lemma avgA (p q r s : prob) (d0 d1 d2 : T) :
  p = (r * s)%R :> R -> s.~ = (p.~ * q.~)%R ->
  avg d0 (avg d1 d2 q) p = avg (avg d0 d1 r) d2 s.
Proof.
move => *.
apply FunctionalExtensionality.functional_extensionality_dep => a.
by apply convA.
Qed.
End depfunavg.
End Depfunavg.

Section depfun_convex_space.
Variables (A : Type) (B : A -> convType).

Definition depfunConvMixin := ConvexSpace.Class
  (@Depfunavg.avg1 A B) (@Depfunavg.avgI A B) (@Depfunavg.avgC A B) (@Depfunavg.avgA A B).
Canonical depfunConvType := ConvexSpace.Pack depfunConvMixin.

End depfun_convex_space.

Module Prodavg.
Section prodavg.
Variables (A B : convType).
Let T := prod A B.
Definition avg (x y : T) (t : prob) := (fst x <| t |> fst y , snd x <| t |> snd y).
Lemma avg1 (x y : T) : avg x y (`Pr 1) = x.
Proof.
  rewrite /avg (conv1 (fst x)) (conv1 (snd x)).
    by case x.
Qed.
Lemma avgI (x : T) (p : prob) : avg x x p = x.
Proof.
  rewrite /avg (convmm (fst x)) (convmm (snd x)).
    by case x.
Qed.
Lemma avgC (x y : T) (p : prob) : avg x y p = avg y x `Pr p.~.
Proof.
by congr (pair _ _); apply convC.
Qed.
Lemma avgA (p q r s : prob) (d0 d1 d2 : T) :
  p = (r * s)%R :> R -> s.~ = (p.~ * q.~)%R ->
  avg d0 (avg d1 d2 q) p = avg (avg d0 d1 r) d2 s.
Proof.
move => *.
congr (pair _ _); by apply convA.
Qed.
End prodavg.
End Prodavg.

Section prod_convex_space.
Variables (A B : convType).

Definition prodConvMixin := ConvexSpace.Class
  (@Prodavg.avg1 A B) (@Prodavg.avgI A B) (@Prodavg.avgC A B) (@Prodavg.avgA A B).
Canonical prodConvType := ConvexSpace.Pack prodConvMixin.

End prod_convex_space.

Section convex_function_def.
Variables (A : convType) (f : A -> R).

Definition convex_function_at a b t := (f (a <| t |> b) <= f a <| t |> f b)%R.

Definition strictly_convexf_at := forall a b (t : prob),
  a <> b -> (0 < t < 1)%R -> convex_function_at a b t.

Definition convex_function := forall a b t, convex_function_at a b t.

Lemma convex_functionP : convex_function <-> forall a b t, convex_function_at a b t.
Proof. split => [H x y t|H x y t]; exact: H. Qed.

Lemma convex_function_atxx a t : convex_function_at a a t.
Proof. rewrite /convex_function_at !convmm; exact/leRR. Qed.

End convex_function_def.

Section convex_function_prop.
Variable (A : convType).

Lemma convex_function_sym (f : A -> R) a b : (forall t, convex_function_at f a b t) ->
  forall t, convex_function_at f b a t.
Proof.
move => H t; move: (H (`Pr t.~)).
by rewrite /convex_function_at /= convC -probK (convC (f a)) -probK.
Qed.

(* NB : The proofs below should work for any ordered convType instead of R *)
Lemma convex_function_comp (f : A -> R) (g : R -> R)
      (Hf : convex_function f) (Hg : convex_function g)
      (g_monotone_on_hull_Im_f : forall a b t, (f (a <|t|> b) <= f a <|t|> f b)%R -> (g (f (a <|t|> b)) <= g (f a <|t|> f b))%R)
      : convex_function (fun a => g (f a)).
Proof.
  rewrite convex_functionP => a b t.
  move : (Hg (f a) (f b) t) => {Hg}.
  rewrite /convex_function_at => Hg.
  eapply leR_trans; [| exact Hg] => {Hg}.
  apply g_monotone_on_hull_Im_f.
  exact: Hf.
Qed.
Lemma convex_function_comp' (f : A -> R) (g : R -> R)
      (Hf : convex_function f) (Hg : convex_function g)
      (g_monotone : forall x y, (x <= y)%R -> (g x <= g y)%R)
      : convex_function (fun a => g (f a)).
Proof.
  apply convex_function_comp => // *.
  by apply g_monotone.
Qed.

End convex_function_prop.

Section concave_function_def.
Variables (A : convType) (f : A -> R).
Definition concave_function_at := convex_function_at (fun x => - f x)%R.
Definition concave_function := convex_function (fun x => - f x)%R.
Definition strictly_concavef_at := forall a b (t : prob),
  a <> b -> (0 < t < 1)%R -> concave_function_at a b t.
End concave_function_def.

Section concave_function_prop.
Variable (A : convType).
Section prop.
Variable (f : A -> R).

Lemma concave_function_atxx a t : concave_function_at f a a t.
Proof. exact: convex_function_atxx. Qed.

Lemma convex_functionN : concave_function f -> convex_function (fun x => - f x)%R.
Proof. by []. Qed.

Lemma concave_functionN : convex_function f -> concave_function (fun x => - f x)%R.
Proof.
move=> H; rewrite /concave_function (_ : (fun x => - - f x)%R = f) //.
apply FunctionalExtensionality.functional_extensionality => ?; by rewrite oppRK.
Qed.
End prop.
Section prop2.
Lemma convex_functionB (f g : A -> R) :
  convex_function f -> concave_function g -> convex_function (fun x => f x - g x)%R.
Proof.
move=> H1 H2 p q t.
rewrite /convex_function_at /=.
rewrite {3}/Conv /= /avg /= (* TODO *) 2!mulRBr addRAC addRA.
move: (H1 p q t) => {H1}H1.
rewrite -addR_opp -addRA; apply leR_add => //.
rewrite -2!mulRN addRC; exact: H2.
Qed.
Lemma concave_functionB (f g : A -> R) :
  concave_function f -> convex_function g -> concave_function (fun x => f x - g x)%R.
Proof.
move=> H1 H2.
rewrite (_ : (fun _ => _) = (fun x => - (g x - f x)))%R; last first.
  apply FunctionalExtensionality.functional_extensionality => x; by rewrite oppRB.
exact/concave_functionN/convex_functionB.
Qed.
End prop2.
End concave_function_prop.

(* NB affine_functionPのほうが定義で, affine_functionのほうは性質では？ - saikawa *)
Section affine_function_def.
Variables (A : convType) (f : A -> R).
Definition affine_function := convex_function f /\ concave_function f.
End affine_function_def.

Section affine_function_prop.
Variables (A : convType) (f : A -> R).
Lemma affine_functionP : affine_function f <-> forall a b (t : prob),
  f (a <| t |> b) = f a <| t |> f b.
Proof.
split => [[H1 H2] p q t| H]; last first.
  split.
  - move=> p q t; rewrite /convex_function_at /= H //; exact/leRR.
  - move=> p q t; rewrite /convex_function_at H // oppRD -!mulRN; exact/leRR.
rewrite eqR_le; split; first exact/H1.
rewrite -[X in (X <= _)%R](oppRK _)leR_oppl oppRD -2!mulRN; exact/H2.
Qed.
Lemma affine_functiontN : affine_function f -> affine_function (fun x => - f x)%R.
Proof. case=> H1 H2; split => //; exact/concave_functionN. Qed.
End affine_function_prop.

Section convex_function_in_def.
Variables (A : convType) (D : convex_set A) (f : A -> R).
Definition convex_function_in := forall a b t, a \in D -> b \in D -> convex_function_at f a b t.
Definition concave_function_in := forall a b t, a \in D -> b \in D -> concave_function_at f a b t.
End convex_function_in_def.

Section dist_convex_space.
Variable A : finType.
Definition dist_convMixin :=
  @ConvexSpace.Class (dist A) (@Conv2Dist.d A)
  (@Conv2Dist.d1 A)
  (@Conv2Dist.idempotent A)
  (@Conv2Dist.skewed_commute A)
  (@Conv2Dist.quasi_assoc A).
Canonical dist_convType := ConvexSpace.Pack dist_convMixin.

Lemma convn_convdist (n : nat) (g : 'I_n -> dist A) (d : {dist 'I_n}) :
  Convn d g = ConvDist.d d g.
Proof.
elim: n g d => /= [g d|n IH g d]; first by move: (distI0_False d).
case: eqVneq => H.
  apply/dist_ext => a.
  rewrite ConvDist.dE big_ord_recl H mul1R big1 ?addR0 //= => j _.
  by move/eqP/dist1P : H => -> //; rewrite ?mul0R.
apply/dist_ext => a.
rewrite Conv2Dist.dE ConvDist.dE /= big_ord_recl; congr (_ + _)%R.
rewrite IH ConvDist.dE big_distrr /=; apply eq_bigr => i _.
rewrite DelDist.dE D1Dist.dE /DelDist.h ltn0 eq_sym (negbTE (neq_lift _ _)).
by rewrite /Rdiv mulRAC mulRC -mulRA mulVR ?onem_neq0 // mulR1.
Qed.
End dist_convex_space.

Lemma Conv2DistdE (A : finType) (a b : dist A) (p : prob) (x : A) :
  (a <| p |> b) x = a x <| p |> b x.
Proof. by rewrite Conv2Dist.dE. Qed.

Lemma DistBindConv (A : finType) (B : finType)(p : prob) (dx dy : dist A) (f : A -> dist B) :
  DistBind.d dx f <|p|> DistBind.d dy f = DistBind.d (dx <|p|> dy) f.
Proof.
apply/dist_ext => b0.
rewrite !(Conv2Dist.dE,DistBind.dE) !big_distrr -big_split; apply eq_bigr => a0 _ /=.
by rewrite Conv2Dist.dE mulRDl 2!mulRA.
Qed.

Lemma rsum_Conv (A : finType) (p : prob) (dx dy : dist A):
  \rsum_(a in A) (dx a <|p|> dy a) =
  \rsum_(a in A) dx a <|p|> \rsum_(a in A) dy a.
Proof. by rewrite /Conv /= /avg big_split /= -2!big_distrr. Qed.

Section convex_set_R.

Lemma Rpos_convex : is_convex_set (fun x => 0 < x)%R.
Proof.
apply/asboolP => x y t; rewrite !in_setE => Hx Hy.
case/boolP : (t == `Pr 0) => [/eqP ->| Ht0]; first by rewrite conv0.
apply addR_gt0wl; first by apply mulR_gt0 => //; exact/prob_gt0.
apply mulR_ge0; [exact/onem_ge0/prob_le1 | exact: ltRW].
Qed.

Definition Rpos_interval := CSet.mk Rpos_convex.

Lemma Rnonneg_convex : is_convex_set (fun x => 0 <= x)%R.
Proof.
apply/asboolP => x y t; rewrite !in_setE => Hx Hy.
apply addR_ge0; apply/mulR_ge0 => //; [exact/prob_ge0 | apply/onem_ge0; exact/prob_le1].
Qed.

Definition Rnonneg_interval := CSet.mk Rnonneg_convex.

Lemma open_interval_convex a b (Hab : (a < b)%R) : is_convex_set (fun x => a < x < b)%R.
Proof.
apply/asboolP => x y t; rewrite !in_setE => -[xa xb] [ya yb].
case/boolP : (t == `Pr 0) => [/eqP|]t0; first by rewrite t0 conv0.
case/boolP : (t == `Pr 1) => [/eqP|]t1; first by rewrite t1 conv1.
apply conj.
- rewrite -[X in (X < t * x + t.~ * y)%R]mul1R -(onemKC t) mulRDl.
  apply ltR_add; rewrite ltR_pmul2l //; [exact/prob_gt0 | exact/onem_gt0/prob_lt1].
- rewrite -[X in (_ + _ < X)%R]mul1R -(onemKC t) mulRDl.
  apply ltR_add; rewrite ltR_pmul2l //; [exact/prob_gt0 | exact/onem_gt0/prob_lt1].
Qed.

Lemma open_unit_interval_convex : is_convex_set (fun x => 0 < x < 1)%R.
Proof. apply /open_interval_convex /Rlt_0_1. Qed.

Definition open_unit_interval := CSet.mk open_unit_interval_convex.

End convex_set_R.

Section convex_function_R.

Implicit Types f : R_convType -> R.

Lemma concave_function_atN f x y t : concave_function_at f x y t ->
  forall k, (0 <= k)%R -> concave_function_at (fun x => f x * k)%R x y t.
Proof.
move=> H k k0; rewrite /concave_function_at /convex_function_at.
rewrite {2}/Conv /= /avg /= (* TODO *).
rewrite -3!mulNR 2!mulRA -mulRDl; exact: leR_wpmul2r.
Qed.

Lemma convexf_at_onem x y (t : prob) f : (0 < x -> 0 < y -> x < y ->
  convex_function_at f x y t -> convex_function_at f y x (`Pr t.~))%R.
Proof.
move=> x0 y0 xy H; rewrite /convex_function_at.
rewrite {2}/Conv /= /avg /= onemK addRC.
rewrite /convex_function_at /Conv /= /avg /= in H.
rewrite /Conv /= /avg /= onemK addRC.
apply: (leR_trans H); rewrite addRC; exact/leRR.
Qed.

Lemma concavef_at_onem x y (t : prob) f : (0 < x -> 0 < y -> x < y ->
  concave_function_at f x y t -> concave_function_at f y x (`Pr t.~))%R.
Proof. move=> ? ? ?; exact/convexf_at_onem. Qed.

End convex_function_R.

(* NB(saikawa):
Assume f is twice differentiable on an open interval I.
Let Df and DDf be the first and second derivatives of f.
Further assume DDf is always positive.  By applying MVT, we have :
forall a x \in I, exists c1 \in [a,x], f(x) = f(a) + (x-a) * Df(c1).
Fix a and x.  Applying MVT again, we further get :
exists c2 \in (a,c1), Df(c1) = Df(a) + (c1-a) * DDf(c2).
The two equations combined is :
f(x) = f(a) + (x-a) * Df(a) + (x-a)(c1-a) * DDf(c2).
The last term is then positive thanks to the assumption on DDf.
Now this is an equivalent condition to the convexity of f.
 *)

(* ref: http://www.math.wisc.edu/~nagel/convexity.pdf *)
Section twice_derivable_convex.

Variables (f : R -> R) (a b : R).
Let I := fun x0 => (a <= x0 <= b)%R.
Hypothesis HDf : pderivable f I.
Variable Df : R -> R.
Hypothesis DfE : forall x (Hx : I x), Df x = derive_pt f x (HDf Hx).
Hypothesis HDDf : pderivable Df I.
Variable DDf : R -> R.
Hypothesis DDfE : forall x (Hx : I x), DDf x = derive_pt Df x (HDDf Hx).
Hypothesis DDf_ge0 : forall x, I x -> (0 <= DDf x)%R.

Definition L (x : R) := (f a + (x - a) / (b - a) * (f b - f a))%R.

Hypothesis ab : (a < b)%R.

Lemma LE x : L x = ((b - x) / (b - a) * f a + (x - a) / (b - a) * f b)%R.
Proof.
rewrite /L mulRBr [in LHS]addRA addRAC; congr (_ + _)%R.
rewrite addR_opp -{1}(mul1R (f a)) -mulRBl; congr (_ * _)%R.
rewrite -(mulRV (b - a)); last by rewrite subR_eq0; exact/eqP/gtR_eqF.
by rewrite -mulRBl -addR_opp oppRB addRA subRK addR_opp.
Qed.

Lemma convexf_ptP : (forall x, a <= x <= b -> 0 <= L x - f x)%R ->
  forall t : prob, convex_function_at f a b t.
Proof.
move=> H t; rewrite /convex_function_at.
set x := (t * a + t.~ * b)%R.
have : (a <= x <= b)%R.
  rewrite /x; split.
  - apply (@leR_trans (t * a + t.~ * a)).
      rewrite -mulRDl addRCA addR_opp subRR addR0 mul1R; exact/leRR.
    case/boolP : (t == `Pr 1) => [/eqP ->|t1].
      rewrite /onem subRR !mul0R !addR0; exact/leRR.
    rewrite leR_add2l; apply leR_wpmul2l; last exact/ltRW.
    exact/onem_ge0/prob_le1.
  - apply (@leR_trans (t * b + t.~ * b)); last first.
      rewrite -mulRDl addRCA addR_opp subRR addR0 mul1R; exact/leRR.
    rewrite leR_add2r; apply leR_wpmul2l; [exact/prob_ge0 | exact/ltRW].
move/H; rewrite subR_ge0 => /leR_trans; apply.
rewrite LE //.
have -> : ((b - x) / (b - a) = t)%R.
  rewrite /x -addR_opp oppRD addRCA mulRBl mul1R oppRB (addRCA b).
  rewrite addR_opp subRR addR0 -mulRN addRC -mulRDr addR_opp.
  rewrite /Rdiv -mulRA mulRV ?mulR1 // subR_eq0; exact/eqP/gtR_eqF.
have -> : ((x - a) / (b - a) = t.~)%R.
  rewrite /x -addR_opp addRAC -{1}(oppRK a) mulRN -mulNR -{2}(mul1R (- a)%R).
  rewrite -mulRDl (addRC _ R1) addR_opp -mulRDr addRC addR_opp.
  rewrite /Rdiv -mulRA mulRV ?mulR1 // subR_eq0; exact/eqP/gtR_eqF.
exact/leRR.
Qed.

Lemma second_derivative_convexf_pt : forall t : prob, convex_function_at f a b t.
Proof.
have note1 : forall x, R1 = ((x - a) / (b - a) + (b - x) / (b - a))%R.
  move=> x; rewrite -mulRDl addRC addRA subRK addR_opp mulRV // subR_eq0.
  exact/eqP/gtR_eqF.
have step1 : forall x, f x = ((x - a) / (b - a) * f x + (b - x) / (b - a) * f x)%R.
  by move=> x; rewrite -mulRDl -note1 mul1R.
apply convexf_ptP => // x axb.
rewrite /L.
case: axb.
  rewrite leR_eqVlt => -[-> _|].
  rewrite /L subRR div0R mul0R addR0 subRR; exact/leRR.
move=> ax.
rewrite leR_eqVlt => -[->|].
rewrite /L /Rdiv mulRV ?mul1R; last by rewrite subR_eq0; exact/eqP/gtR_eqF.
rewrite addRC subRK subRR; exact/leRR.
move=> xb.
have {step1}step2 : (L x - f x =
  (x - a) * (b - x) / (b - a) * ((f b - f x) / (b - x)) -
  (b - x) * (x - a) / (b - a) * ((f x - f a) / (x - a)))%R.
  rewrite {1}step1 {step1}.
  rewrite -addR_opp oppRD addRA addRC addRA.
  rewrite LE //.
  rewrite {1}/Rdiv -(mulRN _ (f x)) -/(Rdiv _ _).
  rewrite addRA -mulRDr (addRC _ (f a)) (addR_opp (f a)).
  rewrite -mulRN -addRA -mulRDr (addR_opp (f b)).
  rewrite addRC.
  rewrite -(oppRK (f a - f x)) mulRN addR_opp oppRB.
  congr (_ + _)%R.
  - rewrite {1}/Rdiv -!mulRA; congr (_ * _)%R; rewrite mulRCA; congr (_ * _)%R.
    rewrite mulRCA mulRV ?mulR1 // subR_eq0; exact/eqP/gtR_eqF.
  - rewrite -!mulNR -!mulRA; congr (_ * _)%R; rewrite mulRCA; congr (_ * _)%R.
    rewrite mulRCA mulRV ?mulR1 // subR_eq0; exact/eqP/gtR_eqF.
have [c2 [Ic2 Hc2]] : exists c2, (x < c2 < b /\ (f b - f x) / (b - x) = Df c2)%R.
  have H : pderivable f (fun x0 => x <= x0 <= b)%R.
    move=> z [z1 z2]; apply HDf; split => //.
    apply (@leR_trans x) => //; exact: ltRW.
  case: (@MVT_cor1_pderivable x b f H xb) => c2 [Ic2 [H1 H2]].
  exists c2; split => //.
  rewrite H1 /Rdiv -mulRA mulRV ?mulR1; last first.
    by rewrite subR_eq0; exact/eqP/gtR_eqF.
  rewrite DfE; last by move=> ?; exact: proof_derive_irrelevance.
  split.
    apply (@leR_trans x); [exact/ltRW | by case: Ic2 H1].
  by case: H2 => _ /ltRW.
have [c1 [Ic1 Hc1]] : exists c1, (a < c1 < x /\ (f x - f a) / (x - a) = Df c1)%R.
  have H : pderivable f (fun x0 => a <= x0 <= x)%R.
    move=> z [z1 z2]; apply HDf; split => //.
    apply (@leR_trans x) => //; exact: ltRW.
  case: (@MVT_cor1_pderivable a x f H ax) => c1 [Ic1 [H1 H2]].
  exists c1; split => //.
  rewrite H1 /Rdiv -mulRA mulRV ?mulR1; last first.
    by rewrite subR_eq0; exact/eqP/gtR_eqF.
  rewrite DfE; last by move=> ?; exact: proof_derive_irrelevance.
  split.
  - by case: H2 => /ltRW.
  - apply (@leR_trans x).
    by case: H2 => _ /ltRW.
    apply (@leR_trans c2); apply/ltRW; by case: Ic2.
have c1c2 : (c1 < c2)%R by apply (@ltR_trans x); [case: Ic1 | case: Ic2].
have {step2 Hc1 Hc2}step3 : (L x - f x =
  (b - x) * (x - a) * (c2 - c1) / (b - a) * ((Df c2 - Df c1) / (c2 - c1)))%R.
  rewrite {}step2 Hc2 Hc1 (mulRC (x - a)%R) -mulRBr {1}/Rdiv -!mulRA.
  congr (_ * (_ * _))%R; rewrite mulRCA; congr (_ * _)%R.
  rewrite mulRCA mulRV ?mulR1 // subR_eq0; by move/gtR_eqF/eqP : c1c2.
have [d [Id H]] : exists d, (c1 < d < c2 /\ (Df c2 - Df c1) / (c2 - c1) = DDf d)%R.
  have H : pderivable Df (fun x0 => c1 <= x0 <= c2)%R.
    move=> z [z1 z2]; apply HDDf; split => //.
    - apply (@leR_trans c1) => //; by case: Ic1 => /ltRW.
    - apply (@leR_trans c2) => //; by case: Ic2 => _ /ltRW.
  case: (@MVT_cor1_pderivable c1 c2 Df H c1c2) => d [Id [H1 H2]].
  exists d; split => //.
  rewrite H1 /Rdiv -mulRA mulRV ?mulR1; last first.
    by rewrite subR_eq0; exact/eqP/gtR_eqF.
  rewrite DDfE; last by move=> ?; exact: proof_derive_irrelevance.
  split.
  - apply (@leR_trans c1); last by case: Id H1.
    apply/ltRW; by case: Ic1.
  - apply (@leR_trans c2); last by case: Ic2 => _ /ltRW.
    by case: H2 => _ /ltRW.
rewrite {}step3 {}H.
apply/mulR_ge0; last first.
  apply: DDf_ge0; split.
    apply (@leR_trans c1).
      apply/ltRW; by case: Ic1.
     by case: Id => /ltRW.
  apply (@leR_trans c2).
    by case: Id => _ /ltRW.
  apply/ltRW; by case: Ic2.
apply/mulR_ge0; last by apply/ltRW/invR_gt0; rewrite subR_gt0.
apply/mulR_ge0; last first.
  by rewrite subR_ge0; case: Id => Id1 Id2; apply (@leR_trans d); exact/ltRW.
apply/mulR_ge0; rewrite subR_ge0; exact/ltRW.
Qed.

End twice_derivable_convex.
