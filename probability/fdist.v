(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg fingroup perm matrix.
From mathcomp Require Import all_algebra vector reals normedtype.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import Rstruct.
Require Import ssr_ext ssralg_ext bigop_ext realType_ext.

(**md**************************************************************************)
(* # Finite distributions                                                     *)
(*                                                                            *)
(* This file provides a formalization of finite probability distributions and *)
(* lemmas about them (e.g., Wolfowitz's counting principle).                  *)
(*                                                                            *)
(* ```                                                                        *)
(*         f @^-1 y == preimage of the point y via the function f where the   *)
(*                     type of x is an eqType                                 *)
(*       R.-fdist T == the type of distributions over a finType T             *)
(*                     w.r.t. R : realType                                    *)
(*        {fdist T} := Rdefinitions.R.-fdist R                                *)
(*        probfdist == TODO                                                   *)
(*       is_fdist f == the function f is a distribution (predicate in Prop)   *)
(*     fdist_supp d := [set a | d a != 0]                                     *)
(*           fdist1 == point-supported distribution                           *)
(*        fdistbind == of type fdist A -> (A -> fdist B) -> fdist B           *)
(*                     bind of the "probability monad"                        *)
(*                     notation >>=, scope fdist_scope/delimiter fdist        *)
(*         fdistmap == map of the "probability monad"                         *)
(*    fdist_uniform == uniform distribution other a finite type               *)
(*            `U C0 == the uniform distribution with support C,               *)
(*                     where C0 is a proof that the set C is not empty        *)
(* fdist_binary H p == where H is a proof of #|A| = 2%N and p is a            *)
(*                     probability: binary distribution over A with bias p    *)
(*        fdistI2 p == binary distributions over 'I_2                         *)
(*      fdistD1 X P == distribution built from X where the entry b has been   *)
(*                     removed (where P is a proof that X b != 1)             *)
(*        fdist_add == concatenation of two distributions according to a      *)
(*                     given probability p                                    *)
(*                     (convex analogue of the canonical presentation of      *)
(*                     an element of the direct sum of two R.-fdist _'s)      *)
(*        fdist_del == restriction of the domain of a distribution            *)
(*                     (convex analogue of the projection of a vector         *)
(*                     to a subspace)                                         *)
(*     fdist_belast == TODO                                                   *)
(*      fdist_convn == of type                                                *)
(*                     R.-fdist 'I_n -> ('I_n -> R.-fdist A) -> R.-fdist A    *)
(*                     convex combination of n finite distributions           *)
(*       fdist_conv == convex combination of two distributions                *)
(*                     (convex analogue of vector addition)                   *)
(*                     notation: P1 <| p |> P1 where p is a probability       *)
(*       fdist_perm == TODO                                                   *)
(*  fdistI_perm s d == s-permutation of the distribution d : R.-fdist 'I_n    *)
(* ```                                                                        *)
(*                                                                            *)
(* About bivariate (joint) distributions:                                     *)
(* ```                                                                        *)
(*                P`1 == marginal left (fdist_scope/fdist)                    *)
(*                P`2 == marginal right (fdist_scope/fdist)                   *)
(*             P `X W == pair of a distribution and a stochastic matrix       *)
(*           P1 `x P2 == product distribution                                 *)
(*                       (convex analogue of the simple tensor of 2 vectors)  *)
(*           fdistX P == swap the two projections of P : R.-fdist A * B       *)
(*             P `^ n == product distribution over a row vector               *)
(*                       identifier: fdist_rV                                 *)
(*   fdist_prod_of_rV == TODO                                                 *)
(*   head_of_fdist_rV == head marginal                                        *)
(*   tail_of_fdist_rV == tail marginal                                        *)
(*         fdist_col' == marginal distribution                                *)
(*   fdist_belast_last_of_rV == TODO                                          *)
(*   fdist_rV_of_prod == TODO                                                 *)
(*         fdist_col' == TODO                                                 *)
(*          fdist_nth == TODO                                                 *)
(*         fdist_take == TODO                                                 *)
(*             fdistA == TODO                                                 *)
(*           fdistC12 == TODO                                                 *)
(*            fdistAC == TODO                                                 *)
(*           fdistC13 == TODO                                                 *)
(*       fdist_proj13 == TODO                                                 *)
(*       fdist_proj23 == TODO                                                 *)
(*         fdist_self == TODO                                                 *)
(*     fdist_prod_nth == TODO                                                 *)
(*    fdist_prod_take == TODO                                                 *)
(*    fdist_take_drop == TODO                                                 *)
(*        CodomDFDist == TODO                                                 *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "{ 'fdist' T }" (at level 0, format "{ 'fdist'  T }").
Reserved Notation "R '.-fdist' T" (at level 2, format "R '.-fdist'  T").
Reserved Notation "'`U' C0 " (at level 10, C0 at next level).
Reserved Notation "P `^ n" (at level 11).
Reserved Notation "P `X W" (at level 6).
Reserved Notation "P1 `x P2" (at level 6).
Reserved Notation "x <| p |> y" (format "x  <| p |>  y", at level 49).
Reserved Notation "f @^-1 y" (at level 10).

Declare Scope fdist_scope.
Delimit Scope fdist_scope with fdist.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Declare Scope proba_scope.

(* NB: f @^-1: [set y] would require to have finType's *)
Notation "f @^-1 y" := (preim f (pred1 y)) : fdist_scope.
Local Open Scope fdist_scope.

(* TODO: move *)
Definition ex2C (T : Type) (P Q : T -> Prop) : @ex2 T P Q <-> @ex2 T Q P.
Proof. by split; case=> x H0 H1; exists x. Qed.

Lemma bij_swap A B : bijective (@swap A B).
Proof. apply Bijective with swap; by case. Qed.
Arguments bij_swap {A B}.

Lemma swapK A B : (@swap A B) \o swap = @id (B * A).
Proof. by rewrite boolp.funeqE => -[]. Qed.

Unset Printing Implicit Defensive.

Import Order.POrderTheory Order.TotalTheory GRing.Theory Num.Theory.

Module FDist.
Section fdist.
Variables (R : numDomainType) (A : finType).
Local Open Scope ring_scope.
Record t := mk {
  f :> {ffun A -> R};
  _ : [forall a, 0 <= f a] && (\sum_(a in A) f a == 1) }.
Lemma ge0 (d : t) a : 0 <= d a.
Proof. by case: d => ? /= /andP[/forallP ]. Qed.
Lemma f1 (d : t) : \sum_(a in A) d a = 1.
Proof. by case: d => ? /= /andP[? /eqP]. Qed.
Lemma le1 (d : t) a : d a <= 1.
Proof.
rewrite -(f1 d) (_ : d a = \sum_(a' in A | a' == a) d a').
  rewrite big_mkcond /=. apply: ler_sum => a0 _. case: ifPn => // _. exact: ge0.
by rewrite big_pred1_eq.
Qed.

Definition make (f : {ffun A -> R}) (H0 : forall a, (0 <= f a)%R)
  (H1 : \sum_(a in A) f a = 1) : t.
refine (@mk f _). apply/andP. split; [exact /forallP | exact/eqP].
Defined.

End fdist.
Module Exports.
Notation fdist := t.
End Exports.
End FDist.
Export FDist.Exports.
Coercion FDist.f : fdist >-> finfun_of.

HB.instance Definition _ R A := [isSub for @FDist.f R A].
HB.instance Definition _ R A := [Choice of fdist R A by <:].

#[global] Hint Extern 0 (is_true (0 <= _)%mcR) => solve [exact: FDist.ge0] : core.
#[global] Hint Extern 0 (is_true (_ <= 1)%mcR) => solve [exact: FDist.le1] : core.

Notation "R '.-fdist' T" := (fdist R T%type) : fdist_scope.
Notation "{ 'fdist' T }" := (fdist Rdefinitions.R T%type) : fdist_scope.

Lemma fdist_ge0_le1 (R : numDomainType) (A : finType) (d : fdist R A) a :
  (0 <= d a <= 1)%R.
Proof. by apply/andP. Qed.

Definition probfdist (R: realType) (A : finType) (d : fdist R A) a :=
  Eval hnf in Prob.mk_ (@fdist_ge0_le1 R A d a).

Section fdist_lemmas.
Local Open Scope ring_scope.

Variable R : numDomainType.
Variable A : finType.
Implicit Types d : fdist R A.

Definition is_fdist (f : A -> R) : Prop :=
  (forall a, 0 <= f a) /\ (\sum_(a in A) f a = 1).

Lemma fdist_is_fdist d : is_fdist d.
Proof. by case: d => f /= /andP[] /forallP ? /eqP. Qed.

Lemma fdist_card_neq0 d : (0 < #| A |)%nat.
Proof.
apply/negPn/negP => abs.
have /eqP := oner_neq0 R; apply.
rewrite -(FDist.f1 d) (eq_bigl xpred0) ?big_pred0_eq // => a.
apply/negP => aA.
by move/card_gt0P : abs; apply; exists a.
Qed.

Definition fdist_supp d := [set a | d a != 0].

Lemma sum_fdist_supp (f : A -> R) d (P : pred A):
  \sum_(a in A | P a) d a * f a = \sum_(a | P a && (a \in fdist_supp d)) d a * f a.
Proof.
rewrite (bigID (mem (fdist_supp d))) /= addrC big1 ?add0r//.
by move=> i; rewrite inE negbK => /andP[_ /eqP] ->; rewrite mul0r.
Qed.

Lemma fdist_supp_neq0 (d : fdist R A) : fdist_supp d != set0.
Proof.
apply/eqP => H; move: (FDist.f1 d).
rewrite -[LHS]mulr1 big_distrl sum_fdist_supp H big1 //=.
  by move=> /esym/eqP; rewrite oner_eq0.
by move=> i; rewrite inE.
Qed.

Lemma fdist_supp_mem (d : fdist R A) : {i | i \in fdist_supp d}.
Proof.
by case: (set_0Vmem (fdist_supp d)) (fdist_supp_neq0 d) => // ->; rewrite eqxx.
Qed.

Lemma fdist_ind (P : fdist R A -> Type) :
  (forall n : nat, (forall X, #|fdist_supp X| = n -> P X) ->
    forall X b, #|fdist_supp X| = n.+1 -> X b != 0 -> P X) ->
  forall X, P X.
Proof.
move=> H1 d.
move: {-2}(#|fdist_supp d|) (erefl (#|fdist_supp d|)) => n; move: n d.
elim=> [d /esym /card0_eq Hd0|n IH d n13].
  move: (FDist.f1 d).
  rewrite -[X in X = _]mulr1 big_distrl sum_fdist_supp big1 => [|a].
    by move=> /esym/eqP; rewrite oner_eq0.
  by rewrite Hd0.
have [b Hb] : {b : A | d b != 0}.
  suff : {x | x \in fdist_supp d} by case => a; rewrite inE => ?; exists a.
  by apply/sigW/set0Pn; rewrite -cards_eq0 -n13.
by refine (H1 n _ _ _ _ Hb) => // d' A2; apply IH.
Qed.

Lemma fdist_gt0 d a : (d a != 0) <-> (0 < d a).
Proof.
split => H; last by rewrite gt_eqF.
by rewrite lt_neqAle eq_sym H /=.
Qed.

Lemma fdist_lt1 d a : (d a != 1) <-> (d a < 1).
Proof.
split=> H; first by rewrite lt_neqAle H /=.
by rewrite lt_eqF.
Qed.

Lemma fdist_ext d d' : (forall x, d x = d' x) -> d = d'.
Proof. by move=> ?; exact/val_inj/ffunP. Qed.

End fdist_lemmas.

Section fdist1.
Local Open Scope ring_scope.
Variables (R : numDomainType) (A : finType) (a : A).
Let f := [ffun b => (b == a)%bool%:R : R].

Let f0 b : 0 <= f b. Proof. by rewrite ffunE; exact: ler0n. Qed.

Let f1 : \sum_(b in A) f b = 1.
Proof.
rewrite (bigD1 a) //= {1}/f ffunE eqxx /= (eq_bigr (fun=> 0)); last first.
  by move=> b ba; rewrite /f ffunE (negbTE ba).
by rewrite big1_eq // addr0.
Qed.

Definition fdist1 : fdist R A := locked (FDist.make f0 f1).

Lemma fdist1E a0 : fdist1 a0 = (a0 == a)%bool%:R.
Proof. by rewrite /fdist1; unlock; rewrite ffunE. Qed.

Lemma supp_fdist1 : fdist_supp fdist1 = [set a] :> {set A}.
Proof.
apply/setP => a0; rewrite !inE.
have [->|a0a] := eqVneq a0 a; first by rewrite fdist1E eqxx oner_eq0.
by apply/negbTE; rewrite negbK fdist1E (negbTE a0a).
Qed.

End fdist1.
Arguments fdist1 {R A}.

Section fdist1_prop.
Local Open Scope ring_scope.
Variable (R : realType) (A : finType).

Lemma fdist1P (d : R.-fdist A) a :
  reflect (forall i, i != a -> d i = 0) (d a == 1 :> R).
Proof.
apply: (iffP idP) => [/eqP H b ?|H].
- move: (FDist.f1 d); rewrite (bigD1 a) //= H => /esym/eqP.
  rewrite addrC -subr_eq subrr.
  by move/eqP/esym/psumr_eq0P => -> // c ca; exact/fdist_ge0.
- move: (FDist.f1 d); rewrite (bigD1 a) //= => /esym /eqP.
  by rewrite -subr_eq => /eqP <-; rewrite big1 // subr0.
Qed.

Lemma fdist1E1 (d' : fdist R A) a :
  (d' a == 1 :> R) = (d' == fdist1 a :> R.-fdist A).
Proof.
apply/idP/idP => [Pa1|/eqP ->]; last by rewrite fdist1E eqxx.
apply/eqP/fdist_ext => a0; rewrite fdist1E.
have [->|Ha] := eqVneq a0 a; first exact/eqP.
by move/fdist1P : Pa1 => ->.
Qed.

Lemma fdist1I1 (d : R.-fdist 'I_1) : d = fdist1 ord0 :> fdist R _.
Proof.
apply/fdist_ext => /= i; rewrite fdist1E (ord1 i) eqxx.
by move: (FDist.f1 d); rewrite big_ord_recl big_ord0 addr0.
Qed.

Lemma fdist1xx (a : A) : fdist1 a a = 1 :> R.
Proof. by rewrite fdist1E eqxx. Qed.

Lemma fdist10 (a a0 : A) : a0 != a -> fdist1 a a0 = 0 :> R.
Proof. by move=> a0a; rewrite fdist1E (negbTE a0a). Qed.

End fdist1_prop.

Section fdistbind.
Local Open Scope ring_scope.
Variable R : numDomainType.
Variables (A B : finType) (p : fdist R A) (g : A -> fdist R B).

Let f := [ffun b => \sum_(a in A) p a * (g a) b].

Let f0 b : 0 <= f b.
Proof. rewrite /f ffunE; apply sumr_ge0 => a _; exact: mulr_ge0. Qed.

Let f1 : \sum_(b in B) f b = 1.
Proof.
rewrite /f.
under eq_bigr do rewrite ffunE.
rewrite exchange_big /= -[RHS](FDist.f1 p); apply eq_bigr => a _.
by rewrite -big_distrr /= FDist.f1 mulr1.
Qed.

Definition fdistbind : fdist R B := locked (FDist.make f0 f1).

Lemma fdistbindE x : fdistbind x = \sum_(a in A) p a * (g a) x.
Proof. by rewrite /fdistbind; unlock; rewrite ffunE. Qed.

End fdistbind.

Reserved Notation "m >>= f" (at level 49).
Notation "m >>= f" := (fdistbind m f) : fdist_scope.

Lemma fdist1bind (R : realType) (A B : finType) (a : A)
  (f : A -> fdist R B) :
  fdist1 a >>= f = f a.
Proof.
apply/fdist_ext => b; rewrite fdistbindE /= (bigD1 a) //= fdist1xx mul1r.
by rewrite big1 ?addr0// => a0 a0a; rewrite fdist10// mul0r.
Qed.

Lemma fdistbind1 (R: realType) A (p : fdist R A) : p >>= @fdist1 R A = p.
Proof.
apply/fdist_ext => /= a; rewrite fdistbindE /= (bigD1 a) //= fdist1xx mulr1.
by rewrite big1 ?addr0// => a0 a0a; rewrite fdist10 ?mulr0// eq_sym.
Qed.

Lemma fdistbindA R A B C (m : fdist R A) (f : A -> fdist R B)
  (g : B -> fdist R C) :
  (m >>= f) >>= g = m >>= (fun x => f x >>= g).
Proof.
apply/fdist_ext => c; rewrite !fdistbindE /=.
rewrite (eq_bigr (fun a => \sum_(a0 in A) m a0 * f a0 a * g a c)%R); last first.
  by move=> b _; rewrite fdistbindE big_distrl.
rewrite exchange_big /=; apply eq_bigr => a _.
by rewrite fdistbindE big_distrr /=; apply eq_bigr => b _; rewrite mulrA.
Qed.

Section fdistmap.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A B : finType) (g : A -> B) (p : fdist R A).

Definition fdistmap : R.-fdist B := p >>= (fun a => fdist1 (g a)).

Lemma fdistmapE (b : B) : fdistmap b = \sum_(a in A | a \in g @^-1 b) p a.
Proof.
rewrite /fdistmap fdistbindE [in RHS]big_mkcond /=; apply eq_bigr => a _.
case: ifPn => [|]; first by rewrite inE => /eqP->; rewrite fdist1xx mulr1.
by rewrite !inE => gab; rewrite fdist10 ?mulr0// eq_sym.
Qed.
End fdistmap.

Section fdistmap_prop.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A B C : finType).

Lemma fdistmap_id (P : fdist R A) : fdistmap (@id A) P = P. Proof.
by rewrite /fdistmap fdistbind1. Qed.

Lemma fdistmap_comp (g : A -> B) (h : C -> A) (P : fdist R C) :
  fdistmap g (fdistmap h P) = fdistmap (g \o h) P.
Proof.
rewrite /fdistmap fdistbindA; congr (_ >>= _).
by rewrite boolp.funeqE => x; rewrite fdist1bind.
Qed.

End fdistmap_prop.

Section fdist_uniform.
Local Open Scope ring_scope.
Context {R : numFieldType}.
Variables (A : finType) (n : nat).

Hypothesis domain_not_empty : #|A| = n.+1.

Let f : {ffun A -> R} := [ffun a : A => #|A|%:R^-1].

Let f0 a : 0 <= f a.
Proof. by rewrite ffunE invr_ge0 ler0n. Qed.

Let f1 : \sum_(a in A) f a = 1.
Proof.
under eq_bigr do rewrite ffunE.
rewrite big_const iter_addr -[_ *+ _]mulr_natr.
by rewrite mulVr ?addr0// unitf_gt0// ltr0n domain_not_empty.
Qed.

Definition fdist_uniform : fdist R A := locked (FDist.make f0 f1).

Lemma fdist_uniformE a : fdist_uniform a = #|A|%:R^-1.
Proof. by rewrite /fdist_uniform; unlock => /=; rewrite /f ffunE. Qed.

End fdist_uniform.

Section fdist_uniform_prop.
Local Open Scope ring_scope.
Variable R : numFieldType.

Lemma fdist_uniform_neq0 (C : finType) (domain_non_empty : { m : nat | #| C | = m.+1 }) :
  forall x, @fdist_uniform R _ _ (projT2 domain_non_empty) x != 0.
Proof.
move=> c; rewrite fdist_uniformE invr_eq0 pnatr_eq0.
by case domain_non_empty => x' ->.
Qed.

End fdist_uniform_prop.

Lemma dominatesP (R: realType) A (Q P : A -> R) :
  P `<< Q <-> forall a, Q a = 0%R -> P a = 0%R.
Proof. by rewrite /dominates; unlock. Qed.

Lemma dom_by_uniform (R: realType) A (P : fdist R A) n (An1 : #|A| = n.+1) :
  P `<< fdist_uniform An1.
Proof.
apply/dominatesP => a; rewrite fdist_uniformE => /esym abs; exfalso.
by move: abs; rewrite An1; apply/eqP; rewrite lt_eqF // invr_gt0 ltr0n.
Qed.

Section fdist_uniform_supp.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A : finType) (C : {set A}).
Hypothesis C0 : (0 < #|C|)%nat.

Let f : {ffun A -> R} := [ffun a : A => if a \in C then #|C|%:R^-1 else 0].

Let f0 a : 0 <= f a.
Proof.
rewrite /f ffunE.
case e : (a \in C); last exact/lexx.
by rewrite invr_ge0 ler0n.
Qed.

Let f1 : \sum_(a in A) f a = 1.
Proof.
rewrite /f.
have HC' : #|C|%:R != 0 :> R; first by rewrite pnatr_eq0 -lt0n.
under eq_bigr do rewrite ffunE.
rewrite -big_mkcondr big_const iter_addr.
by rewrite -[_ *+ _]mulr_natr mulVf// addr0.
Qed.

Definition fdist_uniform_supp : fdist R A := locked (FDist.make f0 f1).

End fdist_uniform_supp.
Notation "'`U' C0 " := (fdist_uniform_supp _ C0).

Section fdist_uniform_supp_prop.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A : finType) (C : {set A}) (HC : (0 < #| C |)%nat).

Lemma fdist_uniform_supp_in z : z \in C -> (`U HC) z = #|C|%:R^-1 :> R.

Proof. by rewrite /fdist_uniform_supp; unlock; rewrite /= ffunE => ->. Qed.

Lemma fdist_uniform_supp_notin z : z \notin C -> (`U HC) z = 0 :> R.
Proof.
by rewrite /fdist_uniform_supp; unlock; move/negbTE; rewrite /= ffunE => ->.
Qed.

Lemma fdist_uniform_supp_restrict g :
  \sum_(t in A) ((`U HC) t * g t) = \sum_(t in C) ((`U HC) t * g t) :> R.
Proof.
rewrite (bigID (fun x => x \in C)) /= addrC big1 ?add0r// => a aC.
by rewrite fdist_uniform_supp_notin // mul0r.
Qed.

Lemma fdist_uniform_supp_distrr g :
  \sum_(t in C) ((`U HC) t * g t) = (#|C|%:R^-1 * \sum_(t in C) g t) :> R.
Proof.
rewrite /= big_distrr /=; apply eq_bigr => /= i Hi.
by rewrite fdist_uniform_supp_in.
Qed.

Lemma fdist_uniform_supp_neq0 z : ((`U HC) z != 0 :> R) = (z \in C).
Proof.
case/boolP : (z \in C) => [/fdist_uniform_supp_in ->|
                           /fdist_uniform_supp_notin ->].
  by rewrite invr_neq0// pnatr_eq0 -lt0n.
by rewrite eqxx.
Qed.

End fdist_uniform_supp_prop.

Section fdist_binary.
Local Open Scope ring_scope.
Variable R : realType.
Variable A : finType.
Hypothesis HA : #|A| = 2%nat.
Variable p : prob R.

Let f (a : A) := [ffun a' => (if a' == a then (Prob.p p).~ else p : R)].

Let f0 (a a' : A) : 0 <= (f a a' : R).
Proof. by rewrite /f ffunE; case: ifP. Qed.

Let f1 (a : A) : \sum_(a' in A) (f a a' : R) = 1.
Proof.
rewrite Set2sumE /= /f !ffunE; case: ifPn => [/eqP <-|].
  by rewrite eq_sym (negbTE (Set2.a_neq_b HA)) addrC onemKC.
by rewrite eq_sym; move/Set2.neq_a_b/eqP => <-; rewrite eqxx onemKC.
Qed.

Definition fdist_binary : A -> fdist R A :=
  fun a => locked (FDist.make (f0 a) (f1 a)).

Lemma fdist_binaryE a a' : fdist_binary a a' = (if a' == a then (Prob.p p).~ else p : R).
Proof. by rewrite /fdist_binary; unlock; rewrite ffunE. Qed.

Lemma sum_fdist_binary_swap a :
  \sum_(a' in A) fdist_binary a a' = \sum_(a' in A) fdist_binary a' a.
Proof. by rewrite 2!Set2sumE /= !fdist_binaryE !(eq_sym a). Qed.

Lemma fdist_binaryxx a : fdist_binary a a = (Prob.p p).~.
Proof. by rewrite fdist_binaryE eqxx. Qed.

End fdist_binary.

Section fdist_binary_prop.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A : finType) (P Q : fdist R A).
Hypothesis card_A : #|A| = 2%nat.

Lemma charac_bdist : {r : prob R | P = fdist_binary card_A r (Set2.a card_A)}.
Proof.
destruct P as [pf pf01].
have rb : 0 <= pf (Set2.b card_A) <= 1.
  move: (FDist.le1 (FDist.mk pf01) (Set2.b card_A)) => /= H1.
  by move: pf01 => /andP [/forallP pf0 _]; apply/andP.
exists (Prob.mk rb).
apply/fdist_ext => a /=.
move: pf01 => /andP [/forallP pf0 /eqP pf1].
rewrite fdist_binaryE; case: ifPn => [/eqP -> |Ha/=].
  by rewrite /onem -pf1 /= Set2sumE /= addrK.
by move/Set2.neq_a_b/eqP : Ha <-.
Qed.

End fdist_binary_prop.

Section fdist_binary_supp.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A : finType) (d : fdist R A).

Hypothesis Hd : #|fdist_supp d| = 2%nat.

(* TODO: doc *)
Definition fdist_binary_supp0 := enum_val (cast_ord (esym Hd) ord0).

(* TODO: doc *)
Definition fdist_binary_supp1 := enum_val (cast_ord (esym Hd) (lift ord0 ord0)).

Lemma enum_fdist_binary_supp :
  enum (fdist_supp d) = fdist_binary_supp0 :: fdist_binary_supp1 :: [::].
Proof.
apply (@eq_from_nth _ fdist_binary_supp0); first by rewrite -cardE Hd.
case=> [_ |]; first by rewrite [X in _ = X]/= {2}/fdist_binary_supp0 (enum_val_nth fdist_binary_supp0).
case=> [_ |i]; last by rewrite -cardE Hd.
by rewrite [X in _ = X]/= {1}/fdist_binary_supp1 (enum_val_nth fdist_binary_supp0).
Qed.

Lemma sum_fdist_binary_supp (f : A -> R) :
  \sum_(i in fdist_supp d) f i = f fdist_binary_supp0 + f fdist_binary_supp1.
Proof.
transitivity (\sum_(i <- enum (fdist_supp d)) f i); last first.
  by rewrite enum_fdist_binary_supp 2!big_cons big_nil addr0.
by rewrite big_filter; apply eq_bigl => ?; rewrite !inE.
Qed.

End fdist_binary_supp.

Section fdistD1.
Local Open Scope ring_scope.
Variable R : realType.
Variables (B : finType) (X : fdist R B) (b : B).

Definition f : B -> R := [ffun a => if a == b then 0 else X a / (1 - X b)].

Hypothesis Xb1 : X b != 1.

Let f0 : forall a, 0 <= f a.
Proof.
move=> a; rewrite /f ffunE.
case: ifPn => [_ |ab]; first exact/lexx.
by apply: mulr_ge0 => //; rewrite invr_ge0 subr_ge0 ltW// -fdist_lt1.
Qed.

Let f1 : \sum_(a in B) f a = 1.
Proof.
rewrite (bigD1 b) //= {1}/f ffunE eqxx add0r.
rewrite (eq_bigr (fun c => X c / (1 - X b))); last first.
  by move=> ? cb; rewrite /f ffunE (negbTE cb).
rewrite -big_distrl /=.
move: (FDist.f1 X); rewrite (bigD1 b) //=.
move=> /esym /eqP. rewrite addrC -subr_eq => /eqP H.
have ?: 1 - X b != 0 by rewrite subr_eq0 eq_sym.
rewrite -H.
exact: mulfV.
Qed.

Definition fdistD1 := locked (FDist.make f0 f1).

Lemma fdistD1E a : fdistD1 a = if a == b then 0 else X a / (1 - X b).
Proof. by rewrite /fdistD1; unlock; rewrite ffunE. Qed.

End fdistD1.

Section fdistD1_prop.
Local Open Scope ring_scope.
Variable R : realType.
Variables (B : finType) (X : fdist R B) (b : B).

Hypothesis Xb1 : X b != 1.

Lemma card_supp_fdistD1 (Xb0 : X b != 0) :
  #|fdist_supp (fdistD1 Xb1)| = #|fdist_supp X|.-1.
Proof.
rewrite /fdist_supp (cardsD1 b [set a | X a != 0]) !inE Xb0 add1n /=.
apply eq_card => i; rewrite !inE fdistD1E.
case: ifPn => //= ib; first by rewrite eqxx.
apply/idP/idP; first by apply: contra => /eqP ->; rewrite mul0r.
apply: contra. rewrite mulf_eq0 => /orP[// | H].
exfalso.
move/negPn/negP : H; apply.
by rewrite invr_neq0// subr_eq0 eq_sym.
Qed.

Lemma fdistD1_eq0 a (Xa0 : X a != 0) : ((fdistD1 Xb1 a == 0) = (b == a))%bool.
Proof.
rewrite fdistD1E; case: ifPn => [/eqP ->|ab]; first by rewrite !eqxx.
apply/idP/idP => [|]; last by rewrite eq_sym (negbTE ab).
rewrite mulf_eq0 => /orP[]; first by rewrite (negbTE Xa0).
by rewrite invr_eq0 subr_eq0 eq_sym (negbTE Xb1).
Qed.

Lemma fdistD1_0 a : X a = 0 -> fdistD1 Xb1 a = 0.
Proof. by move=> Xa0; rewrite fdistD1E Xa0 mul0r; case: ifP. Qed.

End fdistD1_prop.

Lemma fdistI0_False (R : realType) (d : R.-fdist 'I_O) : False.
Proof. move: (fdist_card_neq0 d); by rewrite card_ord. Qed.

Section fdistI2.
Local Open Scope ring_scope.
Variable R : realType.
Variable p : prob R.

Definition fdistI2 : R.-fdist 'I_2 :=
  fdist_binary (card_ord 2) p (lift ord0 ord0).

Lemma fdistI2E a : fdistI2 a = if a == ord0 then p : R else (Prob.p p).~.
Proof.
rewrite /fdistI2 fdist_binaryE; case: ifPn => [/eqP ->|].
  by rewrite eq_sym (negbTE (neq_lift _ _)).
by case: ifPn => //; move: a => -[[//|[|]//]].
Qed.

End fdistI2.

Section fdistI2_prop.
Local Open Scope ring_scope.
Variable R : realType.

Lemma fdistI21 : @fdistI2 R 1%:pr = fdist1 ord0.
Proof.
apply/fdist_ext => /= i; rewrite fdistI2E fdist1E; case: ifPn => //= _.
by rewrite onem1.
Qed.

Lemma fdistI20 : @fdistI2 R 0%:pr = fdist1 (Ordinal (erefl (1 < 2)%nat)).
Proof.
apply/fdist_ext => /= i; rewrite fdistI2E fdist1E; case: ifPn => [/eqP ->//|].
by case: i => -[//|] [|//] i12 _ /=; rewrite onem0.
Qed.

End fdistI2_prop.

Section fdist_add.
Local Open Scope ring_scope.
Variable R : realType.

Variables (n m : nat)
  (d1 : R.-fdist 'I_n)
  (d2 : R.-fdist 'I_m)
  (p : prob R).

Let f := [ffun i : 'I_(n + m) =>
  let si := fintype.split i in
  match si with inl a => ((p : R) * d1 a) | inr a => (Prob.p p).~ * d2 a end].

Let f0 i : 0 <= f i.
Proof. by rewrite /f ffunE; case: splitP => a _; exact: mulr_ge0. Qed.

Let f1 : \sum_(i < n + m) f i = 1.
Proof.
rewrite -(onemKC (p : R)) -{1}(mulr1 (p : R)) -(mulr1 (Prob.p p).~).
rewrite -{1}(FDist.f1 d1) -(FDist.f1 d2) big_split_ord /=; congr (_ + _).
- rewrite big_distrr /f /=; apply eq_bigr => i _; rewrite ffunE.
  case: splitP => [j Hj|k /= Hi].
  + by congr (_ * d1 _); apply/val_inj => /=; rewrite -Hj.
  + by move: (ltn_ord i); rewrite Hi -ltn_subRL subnn ltn0.
- rewrite big_distrr /f /=; apply eq_bigr => i _; rewrite ffunE.
  case: splitP => [j /= Hi|k /= /eqP].
  + by move: (ltn_ord j); rewrite -Hi -ltn_subRL subnn ltn0.
  + by rewrite eqn_add2l => /eqP ik; congr (_ * d2 _); exact/val_inj.
Qed.

Definition fdist_add : R.-fdist 'I_(n + m) := locked (FDist.make f0 f1).

Lemma fdist_addE i : fdist_add i =
  match fintype.split i with inl a => (p : R) * d1 a | inr a => (Prob.p p).~ * d2 a end.
Proof. by rewrite /fdist_add; unlock; rewrite ffunE. Qed.

End fdist_add.

Section fdist_del.
Local Open Scope ring_scope.
Variable R : realType.
Variables (n : nat) (P : R.-fdist 'I_n.+1) (j : 'I_n.+1) (Pj_neq1 : P j != 1).

Let D : R.-fdist 'I_n.+1 := fdistD1 Pj_neq1.

Let h (i : 'I_n) := if (i < j)%nat then widen_ord (leqnSn _) i else lift ord0 i.

Let f0 i : 0 <= [ffun x => (D \o h) x] i.
Proof. by rewrite /h ffunE /=; case: ifPn. Qed.

Let f1 : \sum_(i < n) [ffun x => (D \o h) x] i = 1.
Proof.
rewrite -(FDist.f1 D) /= (bigID (fun i : 'I_n.+1 => (i < j)%nat)) /=.
rewrite (bigID (fun i : 'I_n => (i < j)%nat)) /=; congr (_ + _).
  rewrite (@big_ord_narrow_cond _ _ _ j n.+1 xpredT); first by rewrite ltnW.
  move=> jn; rewrite (@big_ord_narrow_cond _ _ _ j n xpredT); first by rewrite -ltnS.
  move=> jn'; apply eq_bigr => i _; rewrite ffunE; congr (D _).
  rewrite /h /= ltn_ord; exact/val_inj.
rewrite (bigID (pred1 j)) /= [X in _ = X + _](_ : _ = 0) ?add0r; last first.
  rewrite (big_pred1 j).
  by rewrite /D fdistD1E eqxx.
  by move=> /= i; rewrite -leqNgt andbC andb_idr // => /eqP ->.
rewrite [in RHS]big_mkcond big_ord_recl /=.
rewrite /= -leqNgt leqn0 eq_sym andbN add0r.
rewrite big_mkcond; apply eq_bigr => i _.
rewrite -2!leqNgt andbC eq_sym -ltn_neqAle ltnS.
case: ifPn => // ji; by rewrite /h ffunE ltnNge ji.
Qed.

Definition fdist_del : R.-fdist 'I_n := locked (FDist.make f0 f1).

Lemma fdist_delE i : fdist_del i = D (h i).
Proof. by rewrite /fdist_del; unlock; rewrite ffunE. Qed.

Definition fdist_del_idx (i : 'I_n) := h i.

End fdist_del.

Section fdist_belast.
Local Open Scope ring_scope.
Variable R : realType.
Variables (n : nat) (P : fdist R 'I_n.+1) (Pmax_neq1 : P ord_max != 1).

Let D : R.-fdist 'I_n.+1 := fdistD1 Pmax_neq1.

Definition fdist_belast : R.-fdist 'I_n := locked (fdist_del Pmax_neq1).

Lemma fdist_belastE i : fdist_belast i = D (widen_ord (leqnSn _) i).
Proof. by rewrite /fdist_belast; unlock; rewrite fdist_delE ltn_ord. Qed.

End fdist_belast.

Section fdist_convn.
Local Open Scope ring_scope.
Variables (R : realType) (A : finType) (n : nat) (e : R.-fdist 'I_n)
  (g : 'I_n -> fdist R A).

Let f := [ffun a => \sum_(i < n) e i * g i a].

Let f0 a : 0 <= f a.
Proof. by rewrite ffunE; apply: sumr_ge0 => /= i _; apply mulr_ge0. Qed.

Let f1 : \sum_(a in A) f a = 1.
Proof.
under eq_bigr do rewrite ffunE.
rewrite exchange_big /= -(FDist.f1 e) /=; apply eq_bigr => i _.
by rewrite -big_distrr /= FDist.f1 mulr1.
Qed.

Definition fdist_convn : fdist R A := locked (FDist.make f0 f1).

Lemma fdist_convnE a : fdist_convn a = \sum_(i < n) e i * g i a.
Proof. by rewrite /fdist_convn; unlock; rewrite ffunE. Qed.

End fdist_convn.

Section fdist_convn_prop.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A : finType) (n : nat).

Lemma fdist_convn1 (g : 'I_n -> fdist R A) a : fdist_convn (fdist1 a) g = g a.
Proof.
apply/fdist_ext => a0; rewrite fdist_convnE (bigD1 a) //= fdist1xx mul1r.
by rewrite big1 ?addr0 // => i ia; rewrite fdist10// mul0r.
Qed.

Lemma fdist_convn_cst (e : R.-fdist 'I_n) (a : R.-fdist A) :
  fdist_convn e (fun=> a) = a.
Proof.
by apply/fdist_ext => ?; rewrite fdist_convnE -big_distrl /= FDist.f1 mul1r.
Qed.

End fdist_convn_prop.

Section fdist_conv.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A : finType) (p : prob R) (d1 d2 : fdist R A).

Definition fdist_conv : R.-fdist A := locked
  (fdist_convn (fdistI2 p) (fun i => if i == ord0 then d1 else d2)).

Lemma fdist_convE a : fdist_conv a = (p : R) * d1 a + (Prob.p p).~ * d2 a.
Proof.
rewrite /fdist_conv; unlock => /=.
  by rewrite fdist_convnE !big_ord_recl big_ord0 /= addr0 !fdistI2E.
Qed.

End fdist_conv.

Notation "x <| p |> y" := (fdist_conv p x y) : fdist_scope.

Lemma fdist_conv_bind_left_distr (R : realType) (A B : finType) p a b (f : A -> fdist R B) :
  (a <| p |> b) >>= f = (a >>= f) <| p |> (b >>= f).
Proof.
apply/fdist_ext => a0 /=; rewrite !(fdistbindE,fdist_convE) /=.
rewrite 2!big_distrr /= -big_split /=; apply/eq_bigr => a1 _.
by rewrite fdist_convE mulrDl !mulrA.
Qed.

Section fdist_perm.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A : finType) (n : nat) (P : R.-fdist 'rV[A]_n) (s : 'S_n).

Definition fdist_perm : R.-fdist 'rV[A]_n := fdistmap (col_perm s^-1) P.

Lemma fdist_permE v : fdist_perm v = P (col_perm s v).
Proof.
rewrite fdistmapE /= {1}(_ : v = col_perm s^-1 (col_perm s v)); last first.
  by rewrite -col_permM mulVg col_perm1.
rewrite big_pred1_inj //; exact: col_perm_inj.
Qed.
End fdist_perm.

Section fdistI_perm.
Local Open Scope ring_scope.
Variable R : realType.
Variables (n : nat) (P : R.-fdist  'I_n) (s : 'S_n).

Let f := [ffun i : 'I_n => P (s i)].

Let f0 (i : 'I_n) : 0 <= f i. Proof. by rewrite ffunE. Qed.

Let f1 : \sum_(i < n) f i = 1.
Proof.
transitivity (\sum_(i <- [tuple (s^-1)%g i | i < n]) f i).
  apply/perm_big/tuple_permP; exists s.
  destruct n; first by move: (fdistI0_False P).
  rewrite /index_enum -enumT; apply/(@eq_from_nth _ ord0).
    by rewrite size_map size_tuple -enumT size_enum_ord.
  move=> i; rewrite size_enum_ord => ni /=.
  rewrite (nth_map ord0) ?size_enum_ord //= tnth_map /=.
  apply (@perm_inj _ s); by rewrite permKV /= tnth_ord_tuple.
rewrite -(FDist.f1 P) /= big_map; apply: congr_big => //.
  by rewrite /index_enum -enumT.
by move=> i _; rewrite /f ffunE permKV.
Qed.

Definition fdistI_perm : R.-fdist 'I_n := locked (FDist.make f0 f1).

Lemma fdistI_permE i : fdistI_perm i = P (s i).
Proof. by rewrite /fdistI_perm; unlock; rewrite ffunE. Qed.

End fdistI_perm.

Section fdistI_perm_prop.
Local Open Scope ring_scope.
Variable R : realType.

Lemma fdistI_perm1 (n : nat) (P : R.-fdist 'I_n) : @fdistI_perm R n P 1%g = P.
Proof. by apply/fdist_ext => /= i; rewrite fdistI_permE perm1. Qed.

Lemma fdistI_permM (n : nat) (P : R.-fdist 'I_n) (s s' : 'S_n) :
  @fdistI_perm R n (fdistI_perm P s) s' = fdistI_perm P (s' * s).
Proof. by apply/fdist_ext => /= i; rewrite !fdistI_permE permM. Qed.

Lemma fdistI_tperm (n : nat) (a b : 'I_n) :
  @fdistI_perm R n (fdist1 a) (tperm a b) = fdist1 b.
Proof.
apply/fdist_ext => /= x; rewrite fdistI_permE !fdist1E permE /=.
case: ifPn => [/eqP ->|xa]; first by rewrite eq_sym.
case: ifPn; by [rewrite eqxx | move=> _; rewrite (negbTE xa)].
Qed.

Lemma fdistI_perm_fdist1 (n : nat) (a : 'I_n) (s : 'S_n) :
  @fdistI_perm R n (fdist1 a) s = fdist1 (s^-1 a)%g.
Proof.
apply/fdist_ext => /= i; rewrite fdistI_permE !fdist1E. congr ((nat_of_bool _)%:R).
by apply/eqP/eqP => [<-|->]; rewrite ?permK // ?permKV.
Qed.

End fdistI_perm_prop.

Reserved Notation "d `1" (at level 2, left associativity, format "d `1").
Reserved Notation "d `2" (at level 2, left associativity, format "d `2").

Section fdist_fst_snd.
Local Open Scope ring_scope.
Variable R : realType.

Variables (A B : finType) (P : R.-fdist (A * B)).

Definition fdist_fst : fdist R A := fdistmap fst P.

Lemma fdist_fstE a : fdist_fst a = \sum_(i in B) P (a, i).
Proof.
by rewrite fdistmapE /= -(pair_big_fst _ _ (pred1 a)) //= ?big_pred1_eq.
Qed.

Lemma dom_by_fdist_fst a b : fdist_fst a = 0 -> P (a, b) = 0.
Proof. rewrite fdist_fstE => /psumr_eq0P -> // ? _; exact: fdist_ge0. Qed.

Lemma dom_by_fdist_fstN a b : P (a, b) != 0 -> fdist_fst a != 0.
Proof. by apply: contra => /eqP /dom_by_fdist_fst ->. Qed.

Definition fdist_snd : fdist R B := fdistmap snd P.

Lemma fdist_sndE b : fdist_snd b = \sum_(i in A) P (i, b).
Proof.
rewrite fdistmapE -(pair_big_snd _ _ (pred1 b)) //=.
by apply eq_bigr => a ?; rewrite big_pred1_eq.
Qed.

Lemma dom_by_fdist_snd a b : fdist_snd b = 0 -> P (a, b) = 0.
Proof. by rewrite fdist_sndE => /psumr_eq0P -> // ? _; exact: fdist_ge0. Qed.

Lemma dom_by_fdist_sndN a b : P (a, b) != 0 -> fdist_snd b != 0.
Proof. by apply: contra => /eqP /dom_by_fdist_snd ->. Qed.

End fdist_fst_snd.
Notation "d `1" := (fdist_fst d) : fdist_scope.
Notation "d `2" := (fdist_snd d) : fdist_scope.

Section fdist_prod.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A B : finType) (P : fdist R A) (W : A -> fdist R B).

Let f := [ffun ab => P ab.1 * W ab.1 ab.2].

Let f0 ab : 0 <= f ab. Proof. by rewrite ffunE; apply/mulr_ge0. Qed.

Let f1 : \sum_(ab in {: A * B}) f ab = 1.
Proof.
under eq_bigr do rewrite ffunE.
rewrite -(pair_bigA _ (fun i j => P i * W i j)) /= -(FDist.f1 P).
by apply eq_bigr => a _; rewrite -big_distrr FDist.f1 /= mulr1.
Qed.

Definition fdist_prod := locked (FDist.make f0 f1).

Lemma fdist_prodE ab : fdist_prod ab = P ab.1 * W ab.1 ab.2.
Proof. by rewrite /fdist_prod; unlock; rewrite ffunE. Qed.

Lemma fdist_prod1 : fdist_prod`1 = P.
Proof.
apply/fdist_ext=> a; rewrite fdist_fstE (eq_bigr _ (fun b _ => fdist_prodE (a,b))) /=.
by rewrite -big_distrr FDist.f1 /= mulr1.
Qed.

End fdist_prod.

Notation "P `X W" := (fdist_prod P W) : fdist_scope.

Section fdist_prod_prop.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A B : finType) (W : A -> fdist R B).

Lemma fdist_prod1_conv p (a b : fdist R A) :
  ((a <| p |> b) `X W)`1 = (a `X W)`1 <| p |> (b `X W)`1.
Proof. by rewrite !fdist_prod1. Qed.

Lemma fdist_prod2_conv p (a b : fdist R A) :
  ((a <| p |> b) `X W)`2 = (a `X W)`2 <| p |> (b `X W)`2.
Proof.
apply/fdist_ext => b0.
rewrite fdist_sndE fdist_convE !fdist_sndE 2!big_distrr /=.

rewrite -big_split; apply eq_bigr => a0 _; rewrite !fdist_prodE fdist_convE /=.
by rewrite mulrDl !mulrA.
Qed.

End fdist_prod_prop.

Notation "P1 `x P2" := (P1 `X (fun _ => P2)) : fdist_scope.

Section prod_dominates_joint.
Local Open Scope ring_scope.
Variable R : realType.

Variables (A B : finType) (P : R.-fdist (A * B)).

Lemma Prod_dominates_Joint : P `<< P`1 `x P`2.
Proof.
apply/dominatesP => -[a b].
rewrite fdist_prodE /= => /eqP. rewrite mulf_eq0 => /orP -[/eqP P1a| /eqP P2b];
  by [rewrite dom_by_fdist_fst | rewrite dom_by_fdist_snd].
Qed.

End prod_dominates_joint.

Section fdistX.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A B : finType) (P : R.-fdist (A * B)).

Definition fdistX : R.-fdist (B * A) := fdistmap swap P.

Lemma fdistXE a b : fdistX (b, a) = P (a, b).
Proof.
by rewrite fdistmapE /= -/(swap (a, b)) (big_pred1_inj (bij_inj bij_swap)).
Qed.

Lemma fdistX1 : fdistX`1 = P`2.
Proof. by rewrite /fdist_fst /fdistX fdistmap_comp. Qed.

Lemma fdistX2 : fdistX`2 = P`1.
Proof. by rewrite /fdist_snd /fdistX fdistmap_comp. Qed.

End fdistX.

Section fdistX_prop.
Local Open Scope ring_scope.
Variable T : realType.
Variables (A B : finType) (P : fdist T A) (Q : fdist T B)
  (R S : T .-fdist (A * B)).

Lemma fdistXI : fdistX (fdistX R) = R.
Proof. by rewrite /fdistX fdistmap_comp swapK fdistmap_id. Qed.

Lemma fdistX_prod : fdistX (Q `x P) = P `x Q.
Proof. by apply/fdist_ext => -[a b]; rewrite fdistXE !fdist_prodE mulrC. Qed.

Local Open Scope reals_ext_scope.

Lemma fdistX_dom_by : dominates R S -> dominates (fdistX R) (fdistX S).
Proof.
by move/dominatesP => H; apply/dominatesP => -[b a]; rewrite !fdistXE => /H.
Qed.

End fdistX_prop.

Section fdistX_prop_ext.
Lemma fdistX_prod2 {R: realType}
  (A B : finType) (P : fdist R A) (W : A -> fdist R B) :
  (fdistX (P `X W))`2 = P.
Proof. by rewrite fdistX2 fdist_prod1. Qed.
End fdistX_prop_ext.

Section fdist_prop_ext.
Definition fdistE :=
  (fdistmapE,fdist1E,fdist_prodE,fdistXI,fdistXE,fdist_convnE,fdist_fstE).
End fdist_prop_ext.

Section fdist_rV.
Local Open Scope ring_scope.
Variable R : realType.
Local Open Scope vec_ext_scope.
Variables (A : finType) (P : fdist R A) (n : nat).

Let f := [ffun t : 'rV[A]_n => \prod_(i < n) P t ``_ i].

Let f0 t : 0 <= f t.
Proof. by rewrite ffunE; apply prodr_ge0. Qed.

Let f1 : \sum_(t in 'rV_n) f t = 1.
Proof.
pose P' := fun (a : 'I_n) b => P b.
suff : \sum_(g : {ffun 'I_n -> A }) \prod_(i < n) P' i (g i) = 1.
  rewrite (reindex_onto (fun j : 'rV[A]_n => finfun (fun x => j ``_ x))
                        (fun i => \row_(j < n) i j)) /=.
  - move=> H. rewrite /f -[RHS]H {H}.
    apply: eq_big => t /=.
    + by apply/esym/eqP/rowP => i; rewrite mxE ffunE.
    + move=> _; rewrite ffunE; apply eq_bigr => i _ /=; by rewrite ffunE.
  move=> g _; apply/ffunP => i; by rewrite ffunE mxE.
rewrite -bigA_distr_bigA /= /P'.
rewrite [RHS](_ : _ = \prod_(i < n) 1); last by rewrite big1.
by apply eq_bigr => i _; exact: FDist.f1.
Qed.

Definition fdist_rV : R.-fdist 'rV[A]_n := locked (FDist.make f0 f1).

Lemma fdist_rVE t : fdist_rV t = \prod_(i < n) P t ``_ i.
Proof. by rewrite /fdist_rV; unlock; rewrite ffunE. Qed.

End fdist_rV.

Notation "P `^ n" := (fdist_rV P n) : fdist_scope.

Section wolfowitz_counting.
Local Open Scope ring_scope.
Variable R : realType.

Variables (C : finType) (P : fdist R C) (k : nat) (s : {set 'rV[C]_k}).

Lemma wolfowitz a b A B : 0 < A -> 0 < B ->
  a <= \sum_(x in s) (P `^ k) x <= b ->
  (forall x : 'rV_k, x \in s -> A <= (P `^ k) x <= B) ->
  a / B <= (#| s |)%:R <= b / A.
Proof.
move=> A0 B0 /andP [Ha Hb] H.
have eq_le_ : forall x y, (x = y) -> (x <= y)%O. by move=> ? ? ? ? ->.
have HB : \sum_(x in s) (P `^ _) x <= #|s|%:R * B.
  apply (@le_trans _ _ (\sum_(x in s) [fun _ => B] x)).
    by apply: ler_sum => /= i iA; move: (H i iA) => /andP [].
  rewrite -big_filter /= big_const_seq /= iter_addr /=.
  rewrite addr0 -(mulr_natl B (count _ _)).
  apply: ler_wpM2r; first by rewrite ltW.
  apply eq_le_.
  have [/= l el [ul ls] [pl sl]] := big_enumP _.
  by rewrite count_predT sl; congr (_%:R)%R.
have HA : (#|s|)%:R * A <= \sum_(x in s) (P `^ _) x.
  apply (@le_trans _ _ (\sum_(x in s) [fun _ => A] x)); last first.
    by apply: ler_sum => i Hi /=; case/andP: (H i Hi).
  rewrite -big_filter /= big_const_seq /= iter_addr /=.
  rewrite addr0 -(mulr_natl A (count _ _)).
  apply: ler_wpM2r; first by rewrite ltW.
  apply eq_le_.
  have [/= l el [ul ls] [pl sl]] := big_enumP _.
  by rewrite count_predT sl; congr (_%:R)%R.
apply/andP. split.
- by rewrite ler_pdivrMr //; move/le_trans : Ha; exact.
- by rewrite ler_pdivlMr //; exact: (le_trans HA).
Qed.

End wolfowitz_counting.

Section fdist_prod_of_rV.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A : finType) (n : nat) (P : R .-fdist 'rV[A]_n.+1).

Let f (v : 'rV[A]_n.+1) : A * 'rV[A]_n := (v ord0 ord0, rbehead v).

Let inj_f : injective f.
Proof.
move=> a b -[H1 H2]; rewrite -(row_mx_rbehead a) -(row_mx_rbehead b).
by rewrite {}H2; congr (@row_mx _ 1 1 n _ _); apply/rowP => i; rewrite !mxE.
Qed.

Definition fdist_prod_of_rV : R.-fdist (A * 'rV[A]_n) := fdistmap f P.

Lemma fdist_prod_of_rVE a :
  fdist_prod_of_rV a = P (row_mx (\row_(i < 1) a.1) a.2).
Proof.
case: a => x y; rewrite /fdist_prod_of_rV fdistmapE /=.
rewrite (_ : (x, y) = f (row_mx (\row_(i < 1) x) y)); last first.
  by rewrite /f row_mx_row_ord0 rbehead_row_mx.
by rewrite (big_pred1_inj inj_f).
Qed.

Definition head_of_fdist_rV := fdist_prod_of_rV`1.
Definition tail_of_fdist_rV := fdist_prod_of_rV`2.

Let g (v : 'rV[A]_n.+1) : 'rV[A]_n * A := (rbelast v, rlast v).

Let inj_g : injective g.
Proof.
by move=> a b -[H1 H2]; rewrite -(row_mx_rbelast a) -(row_mx_rbelast b) H1 H2.
Qed.

Definition fdist_belast_last_of_rV : R.-fdist ('rV[A]_n * A) := fdistmap g P.

Lemma fdist_belast_last_of_rVE a : fdist_belast_last_of_rV a =
  P (castmx (erefl, addn1 n) (row_mx a.1 (\row_(i < 1) a.2))).
Proof.
case: a => x y; rewrite /fdist_belast_last_of_rV fdistmapE /=.
rewrite (_ : (x, y) = g (castmx (erefl 1%nat, addn1 n) (row_mx x (\row__ y)))); last first.
  by rewrite /g rbelast_row_mx row_mx_row_ord_max.
by rewrite (big_pred1_inj inj_g).
Qed.

End fdist_prod_of_rV.

Lemma head_of_fdist_rV_belast_last (R: realType) (A : finType) (n : nat) (P : R.-fdist 'rV[A]_n.+2) :
  head_of_fdist_rV ((fdist_belast_last_of_rV P)`1) = @head_of_fdist_rV R _ _ P.
Proof.
rewrite /head_of_fdist_rV /fdist_fst /fdist_prod_of_rV /fdist_belast_last_of_rV.
rewrite !fdistmap_comp; congr (fdistmap _ P).
rewrite boolp.funeqE => /= v /=.
rewrite /rbelast mxE; congr (v ord0 _); exact: val_inj.
Qed.

Section fdist_rV_of_prod.
Local Open Scope ring_scope.
Variable R : realType.
Local Open Scope vec_ext_scope.
Variables (A : finType) (n : nat) (P : R.-fdist (A * 'rV[A]_n)).

Let f (x : A * 'rV[A]_n) : 'rV[A]_n.+1 := row_mx (\row_(_ < 1) x.1) x.2.
Lemma inj_f : injective f.
Proof.
move=> -[x1 x2] -[y1 y2]; rewrite /f /= => H.
move: (H) => /(congr1 (@lsubmx A 1 1 n)); rewrite 2!row_mxKl => /rowP/(_ ord0).
rewrite !mxE => ->; congr (_, _).
by move: H => /(congr1 (@rsubmx A 1 1 n)); rewrite 2!row_mxKr.
Qed.

Definition fdist_rV_of_prod : R.-fdist 'rV[A]_n.+1 := fdistmap f P.

Lemma fdist_rV_of_prodE a : fdist_rV_of_prod a = P (a ``_ ord0, rbehead a).
Proof.
rewrite /fdist_rV_of_prod fdistmapE /=.
rewrite {1}(_ : a = f (a ``_ ord0, rbehead a)); last first.
  by rewrite /f /= row_mx_rbehead.
by rewrite (big_pred1_inj inj_f).
Qed.

End fdist_rV_of_prod.

Section fdist_rV_prop.
Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.
Variable R : realType.
Variable A : finType.

Lemma fdist_prod_of_rVK n : cancel (@fdist_rV_of_prod R A n) (@fdist_prod_of_rV R A n).
Proof.
move=> P; apply/fdist_ext => /= -[a b].
by rewrite fdist_prod_of_rVE /= fdist_rV_of_prodE /= row_mx_row_ord0 rbehead_row_mx.
Qed.

Lemma fdist_rV_of_prodK n : cancel (@fdist_prod_of_rV R A n) (@fdist_rV_of_prod R A n).
Proof.
move=> P; apply/fdist_ext => v.
by rewrite fdist_rV_of_prodE fdist_prod_of_rVE row_mx_rbehead.
Qed.

Lemma fdist_rV0 (x : 'rV[A]_0) (P: fdist R A) : (P `^ 0) x = 1.
Proof. by rewrite fdist_rVE big_ord0. Qed.

Lemma fdist_rVS n (x : 'rV[A]_n.+1) (P : fdist R A) :
  (P `^ n.+1) x = P (x ``_ ord0) * (P `^ n) (rbehead x).
Proof.
rewrite 2!fdist_rVE big_ord_recl; congr (_ * _).
by apply eq_bigr => i _; rewrite /rbehead mxE.
Qed.

Lemma fdist_rV1 (a : 'rV[A]_1) (P : fdist R A) : (P `^ 1) a = P (a ``_ ord0).
Proof. by rewrite fdist_rVS fdist_rV0 mulr1. Qed.

Lemma fdist_prod_of_fdist_rV n (P : fdist R A) :
  fdist_prod_of_rV (P `^ n.+1) = P `x (P `^ n).
Proof.
apply/fdist_ext => /= -[a b].
rewrite fdist_prod_of_rVE /= fdist_rVS fdist_prodE; congr (P _ * (P `^ n) _) => /=.
  by rewrite row_mx_row_ord0.
by rewrite rbehead_row_mx.
Qed.

Lemma head_of_fdist_rV_fdist_rV n (P : fdist R A) :
  head_of_fdist_rV (P `^ n.+1) = P.
Proof.
apply/fdist_ext => a; rewrite /head_of_fdist_rV fdist_fstE /=.
under eq_bigr.
  move=> v _; rewrite fdist_prod_of_rVE /= fdist_rVS.
  by rewrite row_mx_row_ord0 rbehead_row_mx; over.
by rewrite -big_distrr /= FDist.f1 mulr1.
Qed.

Lemma tail_of_fdist_rV_fdist_rV n (P : fdist R A) :
  tail_of_fdist_rV (P `^ n.+1) = P `^ n.
Proof.
apply/fdist_ext => a; rewrite /tail_of_fdist_rV fdist_sndE /=.
under eq_bigr.
  move=> v _; rewrite fdist_prod_of_rVE /= fdist_rVS.
  by rewrite row_mx_row_ord0 rbehead_row_mx; over.
by rewrite -big_distrl /= FDist.f1 mul1r.
Qed.

End fdist_rV_prop.

Section fdist_col'.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A : finType) (n : nat) (P : R.-fdist 'rV[A]_n.+1) (i : 'I_n.+1).

Definition fdist_col' : R.-fdist 'rV[A]_n := fdistmap (col' i) P.

Lemma fdist_col'E v : fdist_col' v = \sum_(x : 'rV[A]_n.+1 | col' i x == v) P x.
Proof. by rewrite fdistmapE. Qed.

End fdist_col'.

Section fdist_col'_prop.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A : finType) (n : nat) (P : R.-fdist 'rV[A]_n.+1).

Lemma tail_of_fdist_rV_fdist_col' : tail_of_fdist_rV P = fdist_col' P ord0.
Proof.
by rewrite /fdist_col' /tail_of_fdist_rV /fdist_snd /tail_of_fdist_rV fdistmap_comp.
Qed.

End fdist_col'_prop.

Section fdist_nth.
Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A : finType) (n : nat) (P : R.-fdist 'rV[A]_n) (i : 'I_n).

Definition fdist_nth : R.-fdist A := fdistmap (fun v : 'rV[A]_n => v ``_ i) P.

Lemma fdist_nthE a : fdist_nth a = \sum_(x : 'rV[A]_n | x ``_ i == a) P x.
Proof. by rewrite fdistmapE. Qed.

End fdist_nth.

Section fdist_nth_prop.
Local Open Scope ring_scope.
Variable R : realType.

Lemma head_of_fdist_rV_fdist_nth (A : finType) (n : nat) (P : R.-fdist 'rV[A]_n.+1) :
  head_of_fdist_rV P = fdist_nth P ord0.
Proof.
by rewrite /head_of_fdist_rV /fdist_nth /fdist_fst /head_of_fdist_rV fdistmap_comp.
Qed.

End fdist_nth_prop.

Section fdist_take.
Local Open Scope ring_scope.
Variable R : realType.
Variable (A : finType) (n : nat) (P : R.-fdist 'rV[A]_n).

Definition fdist_take (i : 'I_n.+1) : R.-fdist 'rV[A]_i := fdistmap (row_take i) P.

Lemma fdist_takeE i v : fdist_take i v = \sum_(w in 'rV[A]_(n - i))
  P (castmx (erefl, subnKC (ltnS' (ltn_ord i))) (row_mx v w)).
Proof.
rewrite fdistmapE /=.
rewrite (@reindex_onto _ _ _ 'rV[A]_n 'rV[A]_(n - i)
  (fun w => castmx (erefl 1%nat, subnKC (ltnS' (ltn_ord i))) (row_mx v w))
  (@row_drop A n i)) /=; last first.
  move=> w wv; apply/rowP => j.
  rewrite castmxE /= cast_ord_id /row_drop mxE; case: splitP => [j0 /= jj0|k /= jik].
  - rewrite -(eqP wv) mxE castmxE /= cast_ord_id; congr (w _ _); exact: val_inj.
  - rewrite mxE /= castmxE /= cast_ord_id; congr (w _ _); exact: val_inj.
apply eq_bigl => w; rewrite inE; apply/andP; split; apply/eqP/rowP => j.
- by rewrite !mxE !castmxE /= !cast_ord_id esymK cast_ordK row_mxEl.
- by rewrite !mxE !castmxE /= cast_ord_id esymK cast_ordK cast_ord_id row_mxEr.
Qed.

End fdist_take.

Section fdist_take_prop.
Local Open Scope ring_scope.
Variable R : realType.

Lemma fdist_take_all (A : finType) (n : nat) (P : R.-fdist 'rV[A]_n.+2) :
  fdist_take P (lift ord0 ord_max) = P.
Proof.
rewrite /fdist_take (_ : row_take (lift ord0 ord_max) = ssrfun.id) ?fdistmap_id //.
rewrite boolp.funeqE => v; apply/rowP => i.
by rewrite /row_take mxE castmxE /= cast_ord_id; congr (v _ _); exact: val_inj.
Qed.

End fdist_take_prop.
Arguments fdist_takeE {R} {A} {n} _ _ _.

Local Open Scope vec_ext_scope.
Lemma fdist_take_nth (R : realType) (A : finType) (n : nat)
  (P : R.-fdist 'rV[A]_n.+1) (i : 'I_n.+1) :
  (fdist_belast_last_of_rV (fdist_take P (lift ord0 i)))`2 = fdist_nth P i.
Proof.
rewrite /fdist_snd /fdist_belast_last_of_rV /fdist_take /fdist_nth !fdistmap_comp.
congr (fdistmap _ _); rewrite boolp.funeqE => /= v /=.
by rewrite /rlast mxE castmxE /= cast_ord_id /=; congr (v ``_ _); exact: val_inj.
Qed.

Section fdistA.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A B C : finType) (P : R.-fdist (A * B * C)).

(* TODO: doc *)
Definition prodA (x : A * B * C) := (x.1.1, (x.1.2, x.2)).

Lemma imsetA E F G : [set prodA x | x in (E `* F) `* G] = E `* (F `* G).
Proof.
apply/setP=> -[a [b c]]; apply/imsetP/idP.
- rewrite ex2C; move=> [[[a' b'] c']] /eqP.
  rewrite /f !inE !xpair_eqE /=.
  by move=> /andP [] /eqP -> /andP [] /eqP -> /eqP -> /andP [] /andP [] -> -> ->.
- rewrite !inE /= => /andP [aE /andP [bF cG]].
  by exists ((a, b), c); rewrite // !inE /= aE bF cG.
Qed.

Definition inj_prodA : injective prodA.
Proof. by rewrite /f => -[[? ?] ?] [[? ?] ?] /= [-> -> ->]. Qed.

Definition fdistA : R.-fdist (A * (B * C)) := fdistmap prodA P.

Lemma fdistAE x : fdistA x = P (x.1, x.2.1, x.2.2).
Proof.
case: x => a [b c]; rewrite /fdistA fdistmapE /= -/(prodA (a, b, c)) big_pred1_inj//.
exact: inj_prodA.
Qed.

Lemma fdistA_domin a b c : fdistA (a, (b, c)) = 0 -> P (a, b, c) = 0.
Proof. by rewrite fdistAE. Qed.

Lemma fdistA_dominN a b c : P (a, b, c) != 0 -> fdistA (a, (b, c)) != 0.
Proof. by apply: contra => /eqP H; apply/eqP; apply: fdistA_domin H. Qed.

End fdistA.
Arguments inj_prodA {A B C}.

Section fdistA_prop.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A B C : finType) (P : R.-fdist (A * B * C)).
Implicit Types (E : {set A}) (F : {set B}) (G : {set C}).

Lemma fdistA1 : (fdistA P)`1 = (P`1)`1.
Proof. by rewrite /fdist_fst /fdistA 2!fdistmap_comp. Qed.

Lemma fdistA21 : ((fdistA P)`2)`1 = (P`1)`2.
Proof. by rewrite /fdistA /fdist_snd /fdist_fst /= !fdistmap_comp. Qed.

Lemma fdistA22 : ((fdistA P)`2)`2 = P`2.
Proof. by rewrite /fdistA /fdist_snd !fdistmap_comp. Qed.

Lemma fdistAX2 : (fdistX (fdistA P))`2 = (P`1)`1.
Proof. by rewrite /fdistA /fdist_snd /fdistX /fdist_fst /= 3!fdistmap_comp. Qed.

Lemma fdistAX12 : ((fdistX (fdistA P))`1)`2 = P`2.
Proof. by rewrite /fdist_snd /fdist_fst /fdistX !fdistmap_comp. Qed.

End fdistA_prop.

Section fdistC12.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A B C : finType) (P : R.-fdist (A * B * C)).

Let f (x : A * B * C) := (x.1.2, x.1.1, x.2).

Let inj_f : injective f.
Proof. by rewrite /f => -[[? ?] ?] [[? ?] ?] /= [-> -> ->]. Qed.

Definition fdistC12 : R.-fdist (B * A * C) := fdistmap f P.

Lemma fdistC12E x : fdistC12 x = P (x.1.2, x.1.1, x.2).
Proof.
case: x => -[b a] c; rewrite /fdistC12 fdistmapE /= -/(f (a, b, c)).
by rewrite (big_pred1_inj inj_f).
Qed.

Lemma fdistC12_snd : fdistC12`2 = P`2.
Proof. by rewrite /fdist_snd /fdistC12 fdistmap_comp. Qed.

Lemma fdistC12_fst : fdistC12`1 = fdistX (P`1).
Proof. by rewrite /fdist_fst /fdistC12 /fdistX 2!fdistmap_comp. Qed.

Lemma fdistA_C12_fst : (fdistA fdistC12)`1 = (P`1)`2.
Proof. by rewrite /fdist_fst /fdistA /fdist_snd !fdistmap_comp. Qed.

End fdistC12.

Section fdistC12_prop.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A B C : finType) (P : R.-fdist (A * B * C)).

Lemma fdistC12I : fdistC12 (fdistC12 P) = P.
Proof.
rewrite /fdistC12 fdistmap_comp (_ : _ \o _ = ssrfun.id) ?fdistmap_id //.
by rewrite boolp.funeqE => -[[]].
Qed.

End fdistC12_prop.

Section fdistAC.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A B C : finType) (P : R.-fdist (A * B * C)).

(* TODO: doc *)
Definition prodAC := fun x : A * B * C => (x.1.1, x.2, x.1.2).

Lemma inj_prodAC : injective prodAC.
Proof. by move=> -[[? ?] ?] [[? ?] ?] [-> -> ->]. Qed.

Lemma imsetAC E F G : [set prodAC x | x in E `* F `* G] = E `* G `* F.
Proof.
apply/setP => -[[a c] b]; apply/imsetP/idP.
- rewrite ex2C; move=> [[[a' b'] c']] /eqP.
  by rewrite /f !inE !xpair_eqE /= => /andP [] /andP [] /eqP -> /eqP -> /eqP -> /andP [] /andP [] -> -> ->.
- by rewrite !inE /= => /andP [] /andP [] aE cG bF; exists ((a, b), c); rewrite // !inE  /= aE cG bF.
Qed.

Definition fdistAC : R.-fdist (A * C * B) := fdistX (fdistA (fdistC12 P)).

Lemma fdistACE x : fdistAC x = P (x.1.1, x.2, x.1.2).
Proof. by case: x => x1 x2; rewrite /fdistAC fdistXE fdistAE fdistC12E. Qed.

End fdistAC.
Arguments inj_prodAC {A B C}.

Section fdistAC_prop.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A B C : finType) (P : R.-fdist (A * B * C)).
Implicit Types (E : {set A}) (F : {set B}) (G : {set C}).

Lemma fdistAC2 : (fdistAC P)`2 = (P`1)`2.
Proof. by rewrite /fdistAC fdistX2 fdistA_C12_fst. Qed.

Lemma fdistA_AC_fst : (fdistA (fdistAC P))`1 = (fdistA P)`1.
Proof. by rewrite /fdist_fst !fdistmap_comp. Qed.

Lemma fdistA_AC_snd : (fdistA (fdistAC P))`2 = fdistX ((fdistA P)`2).
Proof. by rewrite /fdist_snd /fdistX !fdistmap_comp. Qed.

Lemma fdistAC_fst_fst : ((fdistAC P)`1)`1 = (P`1)`1.
Proof. by rewrite /fdist_fst !fdistmap_comp. Qed.

End fdistAC_prop.

Section fdistC13.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A B C : finType) (P : R.-fdist (A * B * C)).

Definition fdistC13 : R.-fdist (C * B * A) := fdistC12 (fdistX (fdistA P)).

Lemma fdistC13E x : fdistC13 x = P (x.2, x.1.2, x.1.1).
Proof. by rewrite /fdistC13 fdistC12E fdistXE fdistAE. Qed.

Lemma fdistC13_fst : fdistC13`1 = fdistX ((fdistA P)`2).
Proof. by rewrite /fdistC13 /fdist_fst /fdistX !fdistmap_comp. Qed.

Lemma fdistC13_snd : fdistC13`2 = (P`1)`1.
Proof. by rewrite /fdistC13 fdistC12_snd fdistAX2. Qed.

Lemma fdistC13_fst_fst : (fdistC13`1)`1 = P`2.
Proof. by rewrite /fdist_fst /fdist_snd !fdistmap_comp. Qed.

Lemma fdistA_C13_snd : (fdistA fdistC13)`2 = fdistX (P`1).
Proof. by rewrite /fdist_snd /fdistX !fdistmap_comp. Qed.

End fdistC13.

Section fdist_proj13.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A B C : finType) (P : R.-fdist (A * B * C)).

Definition fdist_proj13 : R.-fdist (A * C) := (fdistA (fdistC12 P))`2.

Lemma fdist_proj13E x : fdist_proj13 x = \sum_(b in B) P (x.1, b, x.2).
Proof.
by rewrite /fdist_proj13 fdist_sndE; apply eq_bigr => b _; rewrite fdistAE fdistC12E.
Qed.

Lemma fdist_proj13_domin a b c : fdist_proj13 (a, c) = 0 -> P (a, b, c) = 0.
Proof. by rewrite fdist_proj13E /= => /psumr_eq0P ->. Qed.

Lemma fdist_proj13_dominN a b c : P (a, b, c) != 0 -> fdist_proj13 (a, c) != 0.
Proof. by apply: contra => /eqP H; apply/eqP/fdist_proj13_domin. Qed.

Lemma fdist_proj13_snd : fdist_proj13`2 = P`2.
Proof. by rewrite /fdist_proj13 fdistA22 fdistC12_snd. Qed.

Lemma fdist_proj13_fst : fdist_proj13`1 = (fdistA P)`1.
Proof. by rewrite /fdist_proj13 fdistA21 fdistC12_fst fdistX2 fdistA1. Qed.

End fdist_proj13.

Section fdist_proj23.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A B C : finType) (P : R.-fdist (A * B * C)).

Definition fdist_proj23 : R.-fdist (B * C) := (fdistA P)`2.

Lemma fdist_proj23E x : fdist_proj23 x = \sum_(a in A) P (a, x.1, x.2).
Proof.
by rewrite /fdist_proj23 fdist_sndE; apply eq_bigr => a _; rewrite fdistAE.
Qed.

Lemma fdist_proj23_domin a b c : fdist_proj23 (b, c) = 0 -> P (a, b, c) = 0.
Proof. by rewrite fdist_proj23E /= => /psumr_eq0P ->. Qed.

Lemma fdist_proj23_dominN a b c : P (a, b, c) != 0 -> fdist_proj23 (b, c) != 0.
Proof. by apply: contra => /eqP H; apply/eqP; apply: fdist_proj23_domin. Qed.

Lemma fdist_proj23_fst : fdist_proj23`1 = (P`1)`2.
Proof. by rewrite /fdist_proj23 fdistA21. Qed.

Lemma fdist_proj23_snd : fdist_proj23`2 = P`2.
Proof. by rewrite /fdist_proj23 fdistA22. Qed.

End fdist_proj23.

Lemma fdist_proj13_AC (R : realType) (A B C : finType)
  (P : R.-fdist (A * B * C)) :
  fdist_proj13 (fdistAC P) = P`1.
Proof.
rewrite /fdist_proj13 /fdist_snd /fdistA /fdistC12 /fdistAC /fdist_fst.
rewrite !fdistmap_comp /=; congr (fdistmap _ _).
by rewrite boolp.funeqE => -[[]].
Qed.

Section fdist_self.
Local Open Scope ring_scope.
Variable R : realType.
Variable (A : finType) (P : R.-fdist A).

Let f := [ffun a : A * A => if a.1 == a.2 then P a.1 else 0].

Let f0 x : 0 <= f x.
Proof. rewrite /f ffunE; case: ifPn => [/eqP -> //| _]; exact: lexx. Qed.

Let f1 : \sum_(x in {: A * A}) f x = 1.
Proof.
rewrite (eq_bigr (fun a => f (a.1, a.2))); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => f (a1, a2))) /=.
rewrite -(FDist.f1 P); apply/eq_bigr => a _.
under eq_bigr do rewrite ffunE.
rewrite /= (bigD1 a) //= eqxx.
by rewrite big1 ?addr0 // => a' /negbTE; rewrite eq_sym => ->.
Qed.

Definition fdist_self : R.-fdist (A * A) := locked (FDist.make f0 f1).

Lemma fdist_selfE a : fdist_self a = if a.1 == a.2 then P a.1 else 0.
Proof. by rewrite /fdist_self; unlock; rewrite ffunE. Qed.

End fdist_self.

Section fdist_self_prop.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A : finType) (P : R.-fdist A).

Lemma fdist_self1 : (fdist_self P)`1 = P.
Proof.
apply/fdist_ext => a /=; rewrite fdist_fstE (bigD1 a) //= fdist_selfE eqxx /=.
by rewrite big1 ?addr0 // => a' /negbTE; rewrite fdist_selfE /= eq_sym => ->.
Qed.

Lemma fdistX_self : fdistX (fdist_self P) = fdist_self P.
Proof.
apply/fdist_ext => -[a1 a2].
by rewrite fdistXE !fdist_selfE /= eq_sym; case: ifPn => // /eqP ->.
Qed.

End fdist_self_prop.

Local Open Scope ring_scope.
(* TODO: rm? *)
Lemma rsum_rmul_rV_pmf_tnth (R : realType) A n k (P : fdist R A) :
  \sum_(t : 'rV[ 'rV[A]_n]_k) \prod_(m < k) (P `^ n) t ``_ m = 1.
Proof.
transitivity (\sum_(j : {ffun 'I_k -> 'rV[A]_n}) \prod_(m : 'I_k) (P `^ _) (j m)).
  rewrite (reindex_onto (fun p : 'rV_k => [ffun i => p ``_ i])
    (fun x : {ffun 'I_k -> 'rV_n} => \row_(i < k) x i)) //=; last first.
    by move=> f _; apply/ffunP => /= k0; rewrite ffunE mxE.
  apply eq_big => //.
  - by move=> v /=; apply/esym/eqP/rowP => i; rewrite mxE ffunE.
  - by move=> i _; apply eq_bigr => j _; rewrite ffunE.
rewrite -(bigA_distr_bigA (fun m => P `^ _)) /= big_const.
by rewrite iter_mulr FDist.f1 expr1n mulr1.
Qed.
Local Close Scope ring_scope.
Local Close Scope vec_ext_scope.

(* wip *)
Module Subvec.
Section def.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A : finType) (n : nat) (P : R.-fdist 'rV[A]_n) (s : {set 'I_n}).
Definition d : R.-fdist 'rV[A]_#|s| := fdistmap (fun x => sub_vec x s) P.
End def.
End Subvec.
Section subvec_prop.
Local Open Scope ring_scope.
Variable R : realType.
Local Open Scope vec_ext_scope.
Variables (A : finType) (n : nat) (P : R.-fdist 'rV[A]_n.+1).
Definition marginal1_cast (i : 'I_n.+1) (v : 'rV[A]_#|[set i]|) : A :=
  (castmx (erefl, cards1 i) v) ``_ ord0.
Lemma head_ofE :
  head_of_fdist_rV P = fdistmap (@marginal1_cast ord0) (@Subvec.d R A n.+1 P [set ord0]).
Proof.
apply fdist_ext => a.
rewrite fdistmapE /= /head_of_fdist_rV fdist_fstE /= /head_of_fdist_rV.
under eq_bigr do rewrite fdistmapE /=.
rewrite /Subvec.d.
under [in RHS] eq_bigr do rewrite fdistmapE /=.
Abort.
End subvec_prop.

Section fdist_prod_nth.
Local Open Scope ring_scope.
Variable R : realType.
Local Open Scope vec_ext_scope.
Variables (A B : finType) (n : nat) (P : R.-fdist ('rV[A]_n * B)) (i : 'I_n).

Definition fdist_prod_nth : R.-fdist (A * B) :=
  fdistmap (fun x : 'rV[A]_n * B => (x.1 ord0 i, x.2)) P.

Lemma fdist_prod_nthE ab :
  fdist_prod_nth ab = \sum_(x : 'rV[A]_n * B | (x.1 ``_ i == ab.1) && (x.2 == ab.2)) P x.
Proof. by rewrite fdistmapE. Qed.

End fdist_prod_nth.

Section fdist_prod_take.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A B : finType) (n : nat) (P : R.-fdist ('rV[A]_n.+1 * B)) (i : 'I_n.+1).

Definition fdist_prod_take : R.-fdist ('rV_i * A * B) :=
  fdistmap (fun x : 'rV[A]_n.+1 * B => (row_take (widen_ord (leqnSn _) i) x.1, x.1 ord0 i, x.2)) P.

End fdist_prod_take.

Section to_bivar_last_take.
Local Open Scope ring_scope.
Variable R : realType.
Variables (A B : finType).
Variables (n : nat) (PY : R.-fdist ('rV[A]_n.+1 * B)).
Let P : R.-fdist 'rV[A]_n.+1 := PY`1.

Lemma belast_last_take (j : 'I_n.+1) :
  fdist_belast_last_of_rV (fdist_take P (lift ord0 j)) = (fdist_prod_take PY j)`1.
Proof.
rewrite /fdist_belast_last_of_rV /fdist_take /fdist_fst /fdist_prod_take !fdistmap_comp.
congr (fdistmap _ PY); rewrite boolp.funeqE => /= -[v b] /=; congr (_, _).
- apply/rowP => i.
  by rewrite /rbelast !mxE !castmxE /=; congr (v _ _); exact: val_inj.
- by rewrite /rlast mxE castmxE /=; congr (v _ _); exact: val_inj.
Qed.

End to_bivar_last_take.

Section fdist_take_drop.
Local Open Scope ring_scope.
Variable R : realType.
Local Open Scope vec_ext_scope.
Variables (A : finType) (n : nat) (P : R.-fdist 'rV[A]_n.+1) (i : 'I_n.+1).

Definition fdist_take_drop : R.-fdist (A * 'rV[A]_i * 'rV[A]_(n - i)) :=
  fdistmap (fun x : 'rV[A]_n.+1 =>
            (x ord0 ord0, row_take i (rbehead x), row_drop i (rbehead x))) P.

Let g (x : 'rV[A]_n.+1) : A * 'rV[A]_i * 'rV[A]_(n - i) :=
  (x ``_ ord0,
   row_take i (rbehead x),
   row_drop i (rbehead x)).

Let inj_g : injective g.
Proof.
move=> a b; rewrite /g => -[H1 H2 H3].
rewrite -(row_mx_rbehead a) -(row_mx_rbehead b) H1; congr (@row_mx _ 1%nat 1%nat _ _ _).
rewrite (row_mx_take_drop i (rbehead a)) (row_mx_take_drop i (rbehead b)).
by rewrite H2 H3.
Qed.

Lemma fdist_take_dropE x : fdist_take_drop x = P (row_mx (\row_(_ < 1) x.1.1)
                               (castmx (erefl 1%nat, @subnKC i n (ltnS' (ltn_ord i)))
                               (row_mx x.1.2 x.2))).
Proof.
rewrite /fdist_take_drop fdistmapE /=.
rewrite (eq_bigl (fun a : 'rV_n.+1 => (g a == x)%bool)) //.
rewrite {1}(_ : x = g (row_mx (\row_(k<1) x.1.1)
                                 (castmx (erefl 1%nat, subnKC (ltnS' (ltn_ord i)))
                                 (row_mx x.1.2 x.2)))); last first.
  move: x => /= -[[x11 x12] x2].
  rewrite /g row_mx_row_ord0 /=; congr (_, _, _).
  apply/rowP => j; rewrite !mxE !castmxE /= cast_ord_id mxE esymK.
  have @k : 'I_n.
    by apply: (@Ordinal _ j); rewrite (leq_trans (ltn_ord j)) // -ltnS.
  rewrite (_ : lift _ _ = rshift 1%nat k); last first.
    by apply val_inj => /=; rewrite /bump leq0n.
  rewrite (@row_mxEr _ 1%nat 1%nat) // castmxE /= cast_ord_id.
  rewrite (_ : cast_ord _ k = lshift (n - i) j).
  by rewrite row_mxEl.
  exact: val_inj.
  apply/rowP => j; rewrite mxE castmxE /= cast_ord_id mxE esymK.
  have @k0 : 'I_n by apply: (@Ordinal _ (i + j)); rewrite -ltn_subRL.
  rewrite (_ : lift _ _ = rshift 1%nat k0); last first.
    apply val_inj => /=; by rewrite /bump leq0n.
  rewrite (@row_mxEr _ 1%nat 1%nat) castmxE /=.
  rewrite (_ : cast_ord _ _ = rshift i j); last exact: val_inj.
  by rewrite row_mxEr cast_ord_id.
by rewrite (big_pred1_inj inj_g).
Qed.

End fdist_take_drop.

(*Section tuple_prod_cast.

Variables A B : finType.
Variable n : nat.
Variable P : {dist 'rV[A * B]_n}.

(*
Definition dist_tuple_prod_cast : dist [finType of n.-tuple A * n.-tuple B].
apply makeDist with (fun xy => P (prod_tuple xy)).
move=> a; by apply Rle0f.
rewrite -(pmf1 P).
rewrite (reindex_onto (fun x => tuple_prod x) (fun y => prod_tuple y)); last first.
  move=> i _; by rewrite prod_tupleK.
rewrite /=.
apply eq_big => /= i.
- by rewrite inE tuple_prodK eqxx.
- move=> _; by rewrite tuple_prodK.
Defined.
*)

End tuple_prod_cast.*)

(* TODO: the following lemmas are currently not in use. Maybe remove? *)
Section moved_from_convex.
Local Open Scope ring_scope.

Lemma fdist_convn_Add (R : realType)
      (n m : nat) (d1 : R.-fdist 'I_n) (d2 : R.-fdist 'I_m) (p : {prob R})
      (A : finType) (g : 'I_n -> R.-fdist A) (h : 'I_m -> R.-fdist A) :
  fdist_convn (fdist_add d1 d2 p)
    [ffun i => match fintype.split i with inl a => g a | inr a => h a end] =
  (fdist_convn d1 g <| p |> fdist_convn d2 h)%fdist.
Proof.
apply/fdist_ext => a; rewrite !fdist_convE !fdist_convnE.
rewrite 2!big_distrr /= big_split_ord /=; congr (_ + _);
   apply eq_bigr => i _; rewrite fdist_addE ffunE.
case: splitP => /= j ij.
rewrite mulrA; congr (_ * d1 _ * (g _) a); exact/val_inj.
move: (ltn_ord i); by rewrite ij -ltn_subRL subnn ltn0.
case: splitP => /= j ij.
move: (ltn_ord j); by rewrite -ij -ltn_subRL subnn ltn0.
move/eqP : ij; rewrite eqn_add2l => /eqP ij.
rewrite mulrA; congr (_ * d2 _ * (h _) a); exact/val_inj.
Qed.

Import realType_ext.
Lemma fdist_convn_del
        (R : realType)
      (A : finType) (n : nat) (g : 'I_n.+1 -> R.-fdist A) (P : R.-fdist 'I_n.+1)
      (j : 'I_n.+1) (H : (0 <= P j <= 1)) (Pj1 : P j != 1) :
  let g' := fun i : 'I_n => g (fdist_del_idx j i) in
  fdist_convn P g =
    (g j <| @Prob.mk_ R _ H |> fdist_convn (fdist_del Pj1) g')%fdist.
Proof.
move=> g' /=; apply/fdist_ext => a.
rewrite fdist_convE /= fdist_convnE (bigD1 j) //=; congr (_ + _).
rewrite fdist_convnE big_distrr /=.
rewrite (bigID (fun i : 'I_n.+1 => (i < j)%nat)) //=.
rewrite (bigID (fun i : 'I_n => (i < j)%nat)) //=; congr (_ + _).
  rewrite (@big_ord_narrow_cond _ _ _ j n.+1); first by rewrite ltnW.
  move=> jn; rewrite (@big_ord_narrow_cond _ _ _ j n xpredT); first by rewrite -ltnS.
  move=> jn'.
  apply/eq_big.
  by move=> /= i; apply/negP => /eqP/(congr1 val) /=; apply/eqP; rewrite ltn_eqF.
  move=> /= i _.
  rewrite fdist_delE /= ltn_ord fdistD1E /= ifF /=; last first.
    by apply/negP => /eqP/(congr1 val) /=; apply/eqP; rewrite ltn_eqF.
  rewrite mulrA mulrCA mulrV ?mulr1; last first.
rewrite unitfE. rewrite onem_neq0 ?onem_neq0 //.
  congr (P _ * _); first exact/val_inj.
  by rewrite /g' /fdist_del_idx /= ltn_ord; congr (g _ a); exact/val_inj.
rewrite (eq_bigl (fun i : 'I_n.+1 => (j < i)%nat)); last first.
  move=> i; by rewrite -leqNgt eq_sym -ltn_neqAle.
rewrite (eq_bigl (fun i : 'I_n => (j <= i)%nat)); last first.
  move=> i; by rewrite -leqNgt.
rewrite big_mkcond.
rewrite big_ord_recl ltn0 /= add0r.
rewrite [in RHS]big_mkcond.
apply eq_bigr => i _.
rewrite /bump add1n ltnS; case: ifPn => // ji.
rewrite fdist_delE fdistD1E ltnNge ji /= ifF; last first.
  apply/eqP => /(congr1 val) => /=.
  rewrite /bump add1n => ij.
  by move: ji; apply/negP; rewrite -ij ltnn.
rewrite -[1 - P j]/(P j).~.
rewrite [_ / _]mulrC !mulrA divrr ?unitfE ?onem_neq0 // mul1r.
by rewrite /g' /fdist_del_idx ltnNge ji.
Qed.
End moved_from_convex.

Module CodomDFDist.
Import classical_sets.
Section def.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Variables (R: realType) (A : Type) (n : nat) (g : 'I_n -> A).
Variables (e : R .-fdist 'I_n) (y : set A).
Definition f := [ffun i : 'I_n => if g i \in y then e i else 0].
Lemma f0 i : (0 <= f i). Proof. by rewrite /f ffunE; case: ifPn. Qed.
Lemma f1 (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, x (g i) -> e i = 0) :
  (\sum_(i < n) f i = 1).
Proof.
rewrite /f -(FDist.f1 e) /=.
apply eq_bigr => i _; rewrite ffunE.
case: ifPn => // /negP; rewrite in_setE => ygi.
rewrite ge //.
have : (x `|` y) (g i) by apply/gX; by exists i.
by case.
Qed.
Definition d (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, x (g i) -> e i = 0) : R.-fdist 'I_n :=
  locked (FDist.make f0 (f1 gX ge)).
Lemma dE (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, x (g i) -> e i = 0) i :
  d gX ge i = if g i \in y then e i else 0.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
Lemma f1' (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, (x (g i)) /\ (~ y (g i)) -> e i = 0) :
  (\sum_(i < n) f i = 1).
Proof.
rewrite /f -(FDist.f1 e) /=; apply eq_bigr => i _; rewrite ffunE.
case: ifPn => // /negP; rewrite in_setE => giy.
rewrite ge //.
have : (x `|` y) (g i) by apply/gX; by exists i.
by case.
Qed.
Definition d' (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, (x (g i)) /\ (~ y (g i)) -> e i = 0) :=
  locked (FDist.make f0 (f1' gX ge)).
Lemma dE' (x : set A) (gX : g @` setT `<=` x `|` y)
  (ge : forall i : 'I_n, (x (g i)) /\ (~ y (g i)) -> e i = 0) i :
  d' gX ge i = if g i \in y then e i else 0.
Proof. by rewrite /d'; unlock; rewrite ffunE. Qed.
End def.
End CodomDFDist.
