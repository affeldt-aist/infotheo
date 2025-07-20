(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum fingroup perm matrix.
From mathcomp Require Import unstable mathcomp_extra boolp classical_sets.
From mathcomp Require Import Rstruct reals.
Require Import ssr_ext ssralg_ext realType_ext fdist jfdist_cond fsdist convex.

(**md**************************************************************************)
(* # Equivalence of Convexity Definitions                                     *)
(*                                                                            *)
(* Documented in:                                                             *)
(* - R. Affeldt, J. Garrigue, T. Saikawa. Formal adventures in convex and     *)
(*   conical spaces. CICM 2020                                                *)
(*                                                                            *)
(* In this file, we prove equivalences between various axiomatizations of     *)
(* convex spaces:                                                             *)
(* - one with a binary operator and binary laws (`convType` of `convex.v`)    *)
(* - ones with an n-ary operator                                              *)
(*   + Bonchi's axiomatization   [Bonchi 2017]                                *)
(*   + Beaulieu's axiomatization [Beaulieu PhD 2008]                          *)
(*   + (and two others)                                                       *)
(*                                                                            *)
(* The n-ary laws and their logical dependencies are listed in                *)
(* `Module NaryLaws`.                                                         *)
(*                                                                            *)
(* The equivalences between n-ary theories are provided as Hierarchy-Builder  *)
(* structures and factories:                                                  *)
(* ```                                                                        *)
(* naryConvOpType == type with an n-ary convex opreator                       *)
(*                   (mixin hasNaryConvOp)                                    *)
(*        <&>_d f == notation for the operator of naryConvOpType              *)
(*   naryConvType == type with n-ary convex theory in Bonchi's style          *)
(*                   (mixin isNaryConvexSpace)                                *)
(*                                                                            *)
(* Module NaryConvexSpaceTheory                                               *)
(*                == proofs that an naryConvType satisfies all the laws       *)
(* isNaryBeaulieuConvexSpace                                                  *)
(*                == HB factory for Beaulieu's axiomatization                 *)
(* isNaryBaryMapConstConvexSpace, isNaryBarypartIdemConvexSpace               *)
(*                == HB factory for two other combinations of the laws        *)
(* ```                                                                        *)
(*                                                                            *)
(* The equivalence between `convType` and `naryConvType` is given as          *)
(* following modules:                                                         *)
(* ```                                                                        *)
(* BinToNary, NaryToBin == mutual instantiations between the two structures   *)
(* BinToNaryToBin, NaryToBinToNary                                            *)
(*                      == proofs that these constructions cancel each other, *)
(*                         i.e., they are essentially the same structure      *)
(*          a <& p &> b == binary instance of the <&>_ operator,              *)
(*                         provided by NaryToBin                              *)
(* ```                                                                        *)
(* The instance in `NaryToBin` is exported, i.e.,                             *)
(* `Check (T : naryConvType R) : convType R.` succeeds.                       *)
(******************************************************************************)

Reserved Notation "'<&>_' d f" (at level 36, f at level 36, d at level 0,
  format "<&>_ d  f").
Reserved Notation "x <& p &> y" (format "x  <& p &>  y", at level 49).

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory Num.Theory.

Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope convex_scope.


(* naryConvOpType is a basic structure carrying just an n-ary convex opreator.
   (This is actually a "structure" in the model-theoretic sense.)
   Various laws are stated with respect to this. *)

HB.mixin Record hasNaryConvOp (R : realType) (T : Type) of Choice T := {
  convn : forall n, (R.-fdist 'I_n) -> ('I_n -> T) -> T
}.

#[short(type=naryConvOpType)]
HB.structure Definition NaryConvOp R := {T of hasNaryConvOp R T &}.

Notation "'<&>_' d f" := (convn _ d f) : convex_scope.


(* n-ary laws that we deal with in this file *)

Module NaryConvLaws.
Section laws.

Variables (R : realType) (T : naryConvOpType R).

(* Bonchi's version [Bonchi 2017] *)
Definition ax_bary :=
  forall n m (d : R.-fdist 'I_n) (e : 'I_n -> R.-fdist 'I_m) (g : 'I_m -> T),
    <&>_d (fun i => <&>_(e i) g) = <&>_(fdist_convn d e) g.
Definition ax_proj :=
  forall  n (i : 'I_n) (g : 'I_n -> T), <&>_(fdist1 i) g = g i.

(* Beaulieu's version [Beaulieu PhD 2008] *)
Definition ax_part :=
  forall n m (K : 'I_m -> 'I_n) (d : R.-fdist 'I_m) (g : 'I_m -> T),
    <&>_d g = <&>_(fdistmap K d) (fun i => <&>_(FDistPart.d K d i) g).
Definition ax_idem :=
  forall (a : T) (n : nat) (d : R.-fdist 'I_n) (g : 'I_n -> T),
    (forall i, i \in fdist_supp d -> g i = a) -> <&>_d g = a.

(* Alternative to ax_proj *)
Definition ax_map :=
  forall (n m : nat) (u : 'I_m -> 'I_n) (d : R.-fdist 'I_m) (g : 'I_n -> T),
    <&>_d (g \o u) = <&>_(fdistmap u d) g.
Definition ax_const :=
  forall (a : T) (n : nat) (d : R.-fdist 'I_n),
    <&>_d (fun _ => a) = a.

(* Alternative to ax_part, just a restriction of ax_bary *)
Definition ax_barypart :=
  forall n m (d : R.-fdist 'I_n) (e : 'I_n -> R.-fdist 'I_m) (g : 'I_m -> T),
    (forall i j, i != j ->
                 fdist_supp (e i) :&: fdist_supp (e j) = finset.set0) ->
    <&>_d (fun i => <&>_(e i) g) = <&>_(fdist_convn d e) g.

(* Restriction of ax_map to injective maps *)
Definition ax_injmap :=
  forall (n m : nat) (u : 'I_m -> 'I_n) (d : R.-fdist 'I_m) (g : 'I_n -> T),
    injective u -> <&>_d (g \o u) = <&>_(fdistmap u d) g.

End laws.

(* Logical combinations of the above laws *)
Section lemmas.
Variables (R : realType) (T : naryConvOpType R).

Lemma ax_map_of_bary_proj : ax_bary T -> ax_proj T -> ax_map T.
Proof.
move=> axbary axproj n m u d g.
have -> : fdistmap u d = fdist_convn d (fun i : 'I_m => fdist1 (u i)).
  by apply: fdist_ext => /= i; rewrite /fdistmap/= fdistbindE// fdist_convnE.
rewrite -axbary.
by congr (<&>_ _ _); apply: funext => i /=; rewrite axproj.
Qed.

Lemma ax_const_of_bary_proj : ax_bary T -> ax_proj T -> ax_const T.
Proof.
move=> axbary axproj a n d.
by rewrite -(axproj _ (@ord0 0) (fun=>a)) axbary fdist_convn_cst.
Qed.

Lemma ax_idem_of_bary_proj : ax_bary T -> ax_proj T -> ax_idem T.
Proof.
move=> axbary axproj a n d g Hd.
have /=[k Hk] := fdist_supp_mem d.
have -> : g = (fun i => <&>_(fdist1 (if i \in fdist_supp d then k else i)) g).
  apply: funext => i; rewrite axproj.
  case: ifP => // /Hd ->; by rewrite (Hd k).
rewrite axbary (_ : fdist_convn _ _ = fdist1 k) ?axproj ?Hd //.
apply: fdist_ext => /= i.
rewrite fdist_convnE sum_fdist_supp fdistE.
under eq_bigr => j /= -> do rewrite fdistE.
by rewrite -sum_fdist_supp -big_distrl FDist.f1 /= mul1r.
Qed.

Lemma ax_const_of_idem : ax_idem T -> ax_const T.
Proof. by move=> + a n d; exact. Qed.

Lemma ax_idem_of_map_const : ax_map T -> ax_const T -> ax_idem T.
Proof.
move=> axmap axconst a n d g Ha.
set supp := fdist_supp d.
set f : 'I_#|supp| -> 'I_n := enum_val.
have [x Hx] := fdist_supp_mem d.
set f' : 'I_n -> 'I_#|supp| := enum_rank_in Hx.
set d' := fdistmap f' d.
have -> : d = fdistmap f d'.
  apply: fdist_ext => i /=.
  rewrite fdistmap_comp fdistmapE /=.
  case/boolP: (i \in supp) => Hi.
  - rewrite (bigD1 i) /=; last first.
      by rewrite !inE /f /f' /= enum_rankK_in.
    rewrite big1; first by rewrite addr0.
    move=> j /andP[] /eqP <-.
    case/boolP: (j \in supp).
      by move=> Hj; rewrite /f /f' /= enum_rankK_in // eqxx.
    by rewrite inE negbK => /eqP.
  - rewrite big_pred0.
      move: Hi; by rewrite inE negbK => /eqP.
    move=> j; apply/negP => /eqP Hj.
    by move: Hi; rewrite -Hj enum_valP.
rewrite -axmap.
have -> : g \o f = fun=> a.
  apply: funext => i; rewrite /f /= Ha //.
  by move: (enum_valP i); rewrite inE.
by rewrite axconst.
Qed.

Lemma ax_barypart_of_bary : ax_bary T -> ax_barypart T.
Proof. by move=>  + ?; exact. Qed.

Lemma ax_part_of_bary : ax_bary T -> ax_part T.
Proof.
move=> axbary n m K d g; rewrite axbary; congr (<&>_ _ _).
by apply: fdist_ext => /= j; rewrite !fdistE -FDistPart.dK.
Qed.

Lemma ax_proj_of_idem : ax_idem T -> ax_proj T.
Proof. by move=> + ? *; apply => j; rewrite supp_fdist1 inE => /eqP ->. Qed.

Lemma ax_barypart_of_part_idem : ax_part T -> ax_idem T -> ax_barypart T.
Proof.
move=> axpart axidem n m d e g HP.
have [n0 Hn0] := fdist_supp_mem d.
set h' : 'I_n -> 'I_#|fdist_supp d| := enum_rank_in Hn0.
set h : 'I_#|fdist_supp d| -> 'I_n := enum_val.
have f j :
  {i | [forall i, j \notin fdist_supp (e (h i))]||(j \in fdist_supp (e (h i)))}.
  case/boolP: [forall i, j \notin fdist_supp (e (h i))].
    by move=> _; exists (proj1_sig (fdist_supp_mem (fdistmap h' d))).
  by rewrite -negb_exists negbK => /existsP; exact: sigW.
rewrite /= in f.
rewrite [LHS](axpart _ _ h').
rewrite [RHS](axpart _ _ (fun j => proj1_sig (f j))).
have trivIK i j x : x \in fdist_supp (e i) -> x \in fdist_supp (e j) -> i = j.
  have [|] := eqVneq i j => [// | ij] xi xj.
  move/setP/(_ x): (HP _ _ ij); by rewrite inE xi xj inE.
have neqj j a k :
  a \in fdist_supp (e (h j)) -> k != (h j) -> (d k * e k a = 0)%R.
  move=> Haj kj.
  case/boolP: (a \in fdist_supp (e k)) => [ak|].
    by rewrite (trivIK _ _ _ Haj ak) eqxx in kj.
  rewrite inE negbK => /eqP ->.
  by rewrite mulr0.
have Hmap' i : fdistmap h' d i = (\sum_j d (h i) * e (h i) j)%R.
  rewrite -big_distrr fdistE /= FDist.f1 /= mulr1.
  rewrite (bigD1 (h i)) /=; last by rewrite /h /h' !inE enum_valK_in eqxx.
  rewrite big1 /= ?addr0 // => j /andP[] /eqP <-.
  case /boolP: (j \in fdist_supp d) => Hj.
    by rewrite /h /h' (enum_rankK_in Hn0 Hj) eqxx.
  move: Hj; by rewrite inE negbK => /eqP.
have Hmap i :
  fdistmap (fun j : 'I_m => sval (f j)) (fdist_convn d e) i =
  fdistmap h' d i.
  rewrite fdistE big_mkcond /=.
  under eq_bigr do rewrite fdistE.
  rewrite (eq_bigr (fun j => d (h i) * e (h i) j)%R).
    by rewrite Hmap'.
  move=> /= a _; rewrite !inE; case: (f a) => j /= /orP[/forallP /= |] Ha.
    have Ha0 k : (d k * e k a = 0)%R.
      case/boolP: (k \in fdist_supp d) => [Hk|].
        move: (Ha (h' k)).
        by rewrite inE negbK /h/h' enum_rankK_in // => /eqP ->; rewrite mulr0.
      by rewrite inE negbK => /eqP -> ; rewrite mul0r.
    case: ifPn => [/eqP|] _.
      by rewrite Ha0 big1.
    by rewrite Ha0.
  case: ifPn => [/eqP/esym ->{i}|ji].
    by rewrite (bigD1 (h j)) //= big1 ?addr0 // => *; rewrite (neqj j).
  by rewrite (neqj j) //; apply: contra ji => /eqP/enum_val_inj ->.
congr (<&>_ _ _); first by apply: fdist_ext => /= i; rewrite Hmap.
apply: funext => i /=.
have HF : fdistmap h' d i != 0%R.
  rewrite fdistE /=.
  apply/eqP => /psumr_eq0P H.
  have: h i \in fdist_supp d by apply: enum_valP.
  by rewrite inE H ?eqxx // 2!inE /h /h' enum_valK_in.
rewrite (axidem (<&>_(e (h i)) g)); last first.
  move=> /= j; rewrite inE.
  rewrite FDistPart.dE //.
  case/boolP: (j \in fdist_supp d) => [Hj|].
    case: (@eqP _ i) => [-> |].
      by rewrite /h /h' (enum_rankK_in _ Hj).
    by rewrite mulr0 mul0r eqxx.
  by rewrite inE negbK => /eqP ->; rewrite !mul0r eqxx.
congr (<&>_ _ _); apply: fdist_ext => j.
rewrite FDistPart.dE; last first.
  rewrite !fdistE /=.
  under eq_bigr do rewrite fdistE.
  rewrite exchange_big /=.
  rewrite (bigD1 (h i)) //=.
  rewrite -big_distrr big_mkcond /=.
  rewrite (eq_bigr (e (h i))).
    rewrite FDist.f1 mulr1 paddr_eq0 //.
      by have:= enum_valP i=> /[!inE] /negPf ->.
    by apply/sumr_ge0 => *; apply/sumr_ge0 => *; rewrite mulr_ge0.
  move=> /= k _; rewrite 2!inE; case: ifP => //.
  case: (f k) => /= x /orP[/forallP/(_ i)|Hkx Hx].
    by rewrite inE negbK => /eqP ->.
  case/boolP: (k \in fdist_supp (e (h i))) => [Hki |].
    move/eqP: (trivIK _ _ _ Hkx Hki) Hx.
    by rewrite (can_eq (enum_valK_in Hn0)) => ->.
  by rewrite inE negbK => /eqP ->.
move: (Hmap i).
rewrite fdistE /= => ->.
rewrite fdistE.
case: (f j) => /= k /orP[Hn|jk].
  move/forallP/(_ i): (Hn).
  rewrite inE negbK => /eqP ->.
  rewrite big1 ?mul0r //.
  move=> a _.
  move/forallP/(_ (h' a)): Hn.
  case/boolP: (a \in fdist_supp d).
    rewrite /h /h'.
    move/(enum_rankK_in _) ->.
    by rewrite inE negbK => /eqP ->; rewrite mulr0.
  by rewrite inE negbK => /eqP ->; rewrite mul0r.
rewrite (bigD1 (h k)) //= big1 ?addr0; last first.
  by move=> a Ha; apply: (neqj k).
case/boolP: (j \in fdist_supp (e (h i))) => ji.
  have /enum_val_inj H := trivIK _ _ _ jk ji.
  subst k => {jk}.
  move: HF; rewrite eqxx mulr1 Hmap'.
  rewrite -big_distrr /= FDist.f1 mulr1 => HF.
  by rewrite mulrAC mulfV // mul1r.
case: eqP ji => [->|ik]; first by rewrite jk.
by rewrite inE negbK => /eqP ->; rewrite mulr0 mul0r.
Qed.

Lemma ax_injmap_of_barypart_idem : ax_barypart T -> ax_idem T -> ax_injmap T.
Proof.
move=> axbarypart axidem n m u d g Hu.
have -> : fdistmap u d = fdist_convn d (fun i : 'I_m => fdist1 (u i)).
  by apply: fdist_ext => i; rewrite /fdistmap fdistbindE// fdist_convnE.
rewrite -axbarypart.
- congr (<&>_ _ _); apply: funext => j /=; symmetry; apply: axidem => i.
  by rewrite supp_fdist1 inE => /eqP ->.
- move=> x y xy.
  apply/setP => z.
  rewrite !supp_fdist1 !inE.
  case: eqP => //= ->.
  by rewrite eqtype.inj_eq //; exact: negbTE.
Qed.

Corollary ax_injmap_of_ax_part_idem : ax_part T -> ax_idem T -> ax_injmap T.
Proof.
move=> axpart axidem.
apply: ax_injmap_of_barypart_idem=> //.
exact: ax_barypart_of_part_idem.
Qed.

Lemma ax_bary_of_injmap_barypart_idem :
  ax_injmap T -> ax_barypart T -> ax_idem T -> ax_bary T.
Proof.
move=> axinjmap axbarypart axidem n m d e g.
set f : 'I_n * 'I_m -> 'I_#|{: 'I_n * 'I_m}| := enum_rank.
set f' : 'I_#|{: 'I_n * 'I_m}| -> 'I_n * 'I_m := enum_val.
set h := fun k i => f (k, i).
set h' := fun i => snd (f' i).
rewrite (_ : (fun i => _) = (fun i => <&>_(fdistmap (h i) (e i)) (g \o h')));
  last first.
  apply: funext => i.
  have {1}-> : g = (g \o h') \o h i.
    by apply: funext => j; rewrite /h' /h /= /f' /f enum_rankK.
  rewrite axinjmap //.
  by move=> x y; rewrite /h => /enum_rank_inj [].
rewrite axbarypart; first last.
- move=> i j ij.
  apply/setP => x; rewrite !inE !fdistE.
  case/boolP: (i == (f' x).1) ij => [/eqP ->|] ij.
    rewrite [in X in _ && X]big_pred0 ?eqxx ?andbF //.
    move=> k; apply/eqP => hjk.
    move: ij; by rewrite -hjk /h /f /f' enum_rankK eqxx.
  rewrite big_pred0 ?eqxx //.
  move=> k; apply/eqP => hik.
  by move: ij; rewrite -hik /h /f /f' enum_rankK eqxx.
set e' := fun j => fdistmap f (((fdistX (d `X e)) `(| j)) `x (fdist1 j)).
have {2}-> : g = (fun j => <&>_(e' j) (g \o h')).
  apply: funext => j; apply/esym/axidem => k //.
  rewrite inE /e' fdistE (big_pred1 (f' k)) /=; last first.
    by move=> i; rewrite 2!inE -{1}(enum_valK k) /f (can_eq enum_rankK).
  rewrite !fdistE.
  by have [<-//f'kj|] := eqVneq _ j; rewrite mulr0 eqxx.
rewrite [RHS]axbarypart; last first.
  move=> i j ij;  apply/setP => x.
  rewrite inE [RHS]inE.
  case/boolP: (_ \in _) => kx //.
  case/boolP: (_ \in _) => ky //.
  rewrite !(inE,fdistE) /= in kx ky *.
  rewrite (big_pred1 (f' x)) in kx; last first.
    by move=> a; rewrite -{1}(enum_valK x) !inE (can_eq enum_rankK) eq_sym.
  rewrite (big_pred1 (f' x)) in ky; last first.
    by move=> a; rewrite -{1}(enum_valK x) !inE (can_eq enum_rankK) eq_sym.
  move: kx ky; rewrite !fdistE.
  case/boolP: ((f' x).2 == i) ij => [/eqP <-|] ij; last by rewrite mulr0 eqxx.
  by case/boolP: ((f' x).2 == j) ij => [/eqP <-|] //; rewrite mulr0 eqxx.
congr (<&>_ _ _); apply: fdist_ext => k.
rewrite /d1 !fdistE.
under eq_bigr do rewrite fdistE big_distrr big_mkcond /=.
rewrite exchange_big /=; apply: eq_bigr => j _.
rewrite !fdistE -big_mkcond /=.
rewrite (big_pred1 (f' k));
  last by move=> a; rewrite !inE -{1}(enum_valK k) /f (can_eq enum_rankK).
set p := f' k => /=.
have [->|Hj] := eqVneq j p.2; last first.
  rewrite big_pred0; first last.
    move=> i; apply/negbTE; apply: contra Hj.
    rewrite !inE -(enum_valK k) (can_eq enum_rankK).
    by rewrite (surjective_pairing (enum_val k)) => /eqP [] _ /eqP.
  by rewrite !fdistE eq_sym (negbTE Hj) !mulr0.
rewrite (big_pred1 p.1) /=; last first.
  move=> i; rewrite !inE -(enum_valK k) (can_eq enum_rankK).
  by rewrite (surjective_pairing (enum_val k)) xpair_eqE eqxx andbT.
have [Hp|Hp] := eqVneq (\sum_(i < n) d i * e i p.2)%R 0%R.
  rewrite Hp mul0r.
  by move/psumr_eq0P : Hp => ->//= i _; rewrite mulr_ge0.
rewrite [RHS]mulrC !fdistE jfdist_condE !fdistE /=; last first.
  by under eq_bigr do rewrite fdistXE fdist_prodE.
rewrite /jcPr /proba.Pr (big_pred1 p); last first.
  by move=> i; rewrite !inE -xpair_eqE -!surjective_pairing.
rewrite (big_pred1 p.2); last by move=> i; rewrite !inE.
rewrite eqxx mulr1 fdist_sndE /= fdist_prodE.
under eq_bigr do rewrite fdist_prodE /=.
by rewrite -!mulrA mulVf ?mulr1.
Qed.

Corollary ax_bary_of_part_idem : ax_part T -> ax_idem T -> ax_bary T.
Proof.
move=> axpart axidem.
apply: ax_bary_of_injmap_barypart_idem => //.
  exact: ax_injmap_of_ax_part_idem.
exact: ax_barypart_of_part_idem.
Qed.

End lemmas.
End NaryConvLaws.

Import NaryConvLaws.


(* We endow naryConvOpType with Bonchi's axioms: naryConvType *)

HB.mixin Record isNaryConvexSpace
  (R : realType) (T : Type) of NaryConvOp R T := {
  axbary : ax_bary T;
  axproj : ax_proj T;
}.

#[short(type=naryConvType)]
HB.structure Definition NaryConvexSpace (R : realType) :=
  {T of isNaryConvexSpace R T &}.


(* An naryConvType actually validates all the laws *)

Module NaryConvexSpaceTheory.
Section lemmas.
Variables (R : realType) (T : naryConvType R).

Lemma axpart : ax_part T.
Proof. exact/ax_part_of_bary/axbary. Qed.

Lemma axidem : ax_idem T.
Proof. by apply: ax_idem_of_bary_proj; [exact: axbary | exact: axproj]. Qed.

Lemma axmap  : ax_map T.
Proof. by apply: ax_map_of_bary_proj; [exact: axbary | exact: axproj]. Qed.

Lemma axconst : ax_const T.
Proof. exact/ax_const_of_idem/axidem. Qed.

Lemma axbarypart : ax_barypart T.
Proof. exact/ax_barypart_of_bary/axbary. Qed.

Lemma axinjmap : ax_injmap T.
Proof. apply: ax_injmap_of_ax_part_idem; [exact: axpart | exact: axidem]. Qed.

End lemmas.
End NaryConvexSpaceTheory.

Import NaryConvexSpaceTheory.


(* The following combinations of the laws are equivalent:
   - ax_bary + ax_proj (Bonchi)
   - ax_part + ax_idem (Beaulieu)
   - ax_bary + ax_map + ax_const
   - ax_barypart + ax_idem
   This has been implicitly shown as logical implications in Module NaryLaws.
   Module NaryConvexSpaceTheory says that Bonchi subsumes the other three.
   We now exhibit the remaining equivalences by providing Hierarchy-Builder
   factories for the others.

   TODO: show that (ax_bary + ax_const) and (ax_part + ax_proj) are weaker.
 *)

HB.factory Record isNaryBeaulieuConvexSpace
  (R : realType) (T : Type) of NaryConvOp R T := {
  axpart : ax_part T;
  axidem : ax_idem T;
}.

HB.builders Context R T of isNaryBeaulieuConvexSpace R T.

Lemma axproj : ax_proj T.
Proof. exact/ax_proj_of_idem/axidem. Qed.

Lemma axbary : ax_bary T.
Proof. apply/ax_bary_of_part_idem; [exact: axpart | exact: axidem]. Qed.

HB.instance Definition _ := isNaryConvexSpace.Build R T axbary axproj.
HB.end.


HB.factory Record isNaryBaryMapConstConvexSpace
  (R : realType) (T : Type) of NaryConvOp R T := {
  axbary : ax_bary T;
  axmap : ax_map T;
  axconst : ax_const T;
}.

HB.builders Context R T of isNaryBaryMapConstConvexSpace R T.

Lemma axproj : ax_proj T.
Proof.
by apply/ax_proj_of_idem/ax_idem_of_map_const; [exact: axmap | exact: axconst].
Qed.

HB.instance Definition _ := isNaryConvexSpace.Build R T axbary axproj.
HB.end.


HB.factory Record isNaryBarypartIdemConvexSpace
  (R : realType) (T : Type) of NaryConvOp R T := {
  axbarypart : ax_barypart T;
  axidem : ax_idem T;
}.

HB.builders Context R T of isNaryBarypartIdemConvexSpace R T.

Lemma axbary : ax_bary T.
Proof.
apply: ax_bary_of_injmap_barypart_idem; [| exact: axbarypart | exact: axidem].
by apply: ax_injmap_of_barypart_idem; [exact: axbarypart | exact: axidem].
Qed.

Lemma axproj : ax_proj T.
Proof. exact/ax_proj_of_idem/axidem. Qed.

HB.instance Definition _ := isNaryConvexSpace.Build R T axbary axproj.
HB.end.


(* naryConvType is equivalent to convType,
   the binary axiomatization formalized in convex.v.
   We prove this equivalence in two steps.

   First prove mutual definability between convType and naryConvSpace *)

Module BinToNary.
Section instances.
Variables (R : realType) (C : convType R).

HB.instance Definition _ := @hasNaryConvOp.Build R C (@Convn R C conv).

Definition axbary := @Convn_fdist_convn R C.
Definition axproj := @Convn_fdist1 R C.

HB.instance Definition  _ := @isNaryConvexSpace.Build R C axbary axproj.

End instances.
End BinToNary.


Module NaryToBin.
Section instance.
Variables (R : realType) (C : naryConvType R).

Definition binconv p (a b : C) :=
  <&>_(fdistI2 p) (fun x => if x == ord0 then a else b).
Notation "a <& p &> b" := (binconv p a b).

Lemma binconvC p a b : a <& p &> b = b <& ((Prob.p p).~)%:pr &> a.
Proof.
rewrite /binconv.
set g1 := fun x => _.
set g2 := fun x => _.
have -> : g1 = g2 \o tperm ord0 (Ordinal (erefl (1 < 2))).
  rewrite /g1 /g2 /=.
  apply: funext => i /=.
  by case/orP: (ord2 i) => /eqP -> /=; rewrite (tpermL,tpermR).
rewrite axmap.
congr (<&>_ _ _); apply: fdist_ext => i.
rewrite fdistmapE (bigD1 (tperm ord0 (Ordinal (erefl (1 < 2))) i)) /=; last first.
  by rewrite !inE tpermK.
rewrite big1 ?addr0.
  rewrite !fdistI2E onemK.
  by case/orP: (ord2 i) => /eqP -> /=; rewrite (tpermL,tpermR).
by move=> j /andP[] /eqP <-; rewrite tpermK eqxx.
Qed.

Lemma convn_if A n (p : A -> bool) (d1 d2 : R.-fdist 'I_n) (g : _ -> C):
  (fun x => if p x then <&>_d1 g else <&>_d2 g) =
  (fun x => <&>_(if p x then d1 else d2) g).
Proof. apply: funext => x; by rewrite (fun_if (fun d => <&>_d g)). Qed.

Lemma binconvA p q a b c :
  a <& p &> (b <& q &> c) = (a <& [r_of p, q] &> b) <& [s_of p, q] &> c.
Proof.
rewrite /binconv.
set g := fun i : 'I_3 => if i <= 0 then a else if i <= 1 then b else c.
rewrite [X in <&>_(fdistI2 q) X](_ : _ = g \o lift ord0); last first.
  by apply: funext => i; case/orP: (ord2 i) => /eqP ->.
rewrite [X in <&>_(fdistI2 [r_of p, q]) X](_ : _ = g \o (widen_ord (leqnSn 2))); last first.
  by apply: funext => i; case/orP: (ord2 i) => /eqP ->.
rewrite 2!axmap.
set d1 := fdistmap _ _.
set d2 := fdistmap _ _.
set ord23 := Ordinal (ltnSn 2).
have -> : a = g ord0 by [].
have -> : c = g ord23 by [].
rewrite -2!axproj 2!convn_if 2!axbary.
congr (<&>_ _ _); apply: fdist_ext => j.
rewrite !fdist_convnE !big_ord_recl !big_ord0 /=.
rewrite !fdistI2E !fdistmapE !fdist1E !addr0 /=.
case: j => -[|[|[]]] //= Hj.
- rewrite [in RHS](big_pred1 ord0)// big1; last by move=> [] [].
  by rewrite fdistI2E eqxx !(mulr0,addr0) mulr1 mulrC -p_is_rs.
- rewrite (big_pred1 ord0) // (big_pred1 (Ordinal (ltnSn 1))) //.
  rewrite !fdistI2E !eqxx !(mulr0,addr0,add0r)/=.
  rewrite {2}/onem mulrDr mulr1 mulrN [in RHS]mulrC.
  rewrite -p_is_rs s_of_pqE onemM !onemK /onem mulrBl mul1r.
  by rewrite -!addrA (addrC (Prob.p p)) !addrA subrK.
- rewrite (big_pred1 (Ordinal (ltnSn 1))) //.
  rewrite big1; last by case => -[|[]].
  by rewrite !fdistI2E 2!mulr0 2!add0r mulr1 s_of_pqE onemK.
Qed.

Lemma binconv1 a b : binconv 1%:pr a b = a.
Proof.
apply: axidem => /= i; rewrite inE fdistI2E; case: ifP => //=.
by rewrite /onem subrr eqxx.
Qed.

Lemma binconvmm p a : binconv p a a = a.
Proof. by apply: axidem => i; case: ifP. Qed.

(*
(* This instantiation breaks the compilation of the next module on Coq 8.20 *)
HB.instance Definition _ := @isConvexSpace.Build R C binconv
  binconv1 binconvmm binconvC binconvA.
*)
Definition binconv_mixin := @isConvexSpace.Build R C binconv
  binconv1 binconvmm binconvC binconvA.

End instance.
Notation "a <& p &> b" := (binconv p a b).
End NaryToBin.


(* Then prove the definitions of operators cancel each other *)

Module BinToNaryToBin.
Section proof.
Variables (R : realType) (C : convType R).
Import BinToNary NaryToBin.

#[local]
Fact _equiv_convn n (d : R.-fdist 'I_n) (g : 'I_n -> C) : <&>_d g = <|>_d g.
Proof. by []. Qed.

(* The LHS is native to C; the RHS is obtained through BinToNary and NaryToBin *)
Lemma equiv_conv p (a b : C) : a <| p |> b = a <& p &> b.
Proof.
pose g := fun (x : 'I_2) => if x == ord0 then a else b.
change a with (g ord0).
change b with (g (lift ord0 ord0)).
pose d := fdistI2 p.
rewrite [in LHS](_ : p = probfdist d ord0); last first.
  by apply: val_inj=> /=; rewrite fdistI2E eqxx.
by rewrite -!ConvnI2E convnE.
Qed.

End proof.
End BinToNaryToBin.


Module NaryToBinToNary.
Section proof.
Variables (R : realType) (T : naryConvType R).
Import NaryToBin.
(* We do not need to import BinToNary here because exactly
   the same construction (Convn) is already in convex.v with a
   handy notation <|>_ d g *)

(* On Rocq 9.0, this instantiation can be done in Module NaryToBin *)
HB.instance Definition _ := binconv_mixin T.

(* The LHS is native to T; the RHS is obtained through NaryToBin *)
Lemma equiv_convn n (d : R.-fdist 'I_n) (g : 'I_n -> T) : <&>_d g = <|>_d g.
Proof.
elim: n d g => [|n IH d g /=].
  by move=> d; move: (fdist_card_neq0 d); rewrite card_ord.
case: Bool.bool_dec => [|b].
  by rewrite fdist1E1 => /eqP ->; rewrite axproj.
rewrite -{}IH.
have -> : (fun i => g (fdist_del_idx ord0 i)) = g \o lift ord0.
  by apply: funext => i; rewrite /fdist_del_idx ltn0.
apply/esym; rewrite axmap /=.
rewrite /(_ <| _ |> _)/= /binconv.
set d' := fdistmap _ _.
rewrite -(axproj _ ord0) convn_if axbary.
congr (<&>_ _ _); apply: fdist_ext => i.
rewrite fdist_convnE !big_ord_recl big_ord0 addr0 /= !fdistI2E /=.
rewrite fdist1E /d' fdistmapE /=.
have [->|] := eqVneq i ord0; first by rewrite big1 // mulr0 mulr1 addr0.
case: (unliftP ord0 i) => //= [j|] -> // Hj.
rewrite (big_pred1 j) //=.
rewrite fdist_delE fdistD1E /= /onem.
rewrite mulr0 add0r mulrA (mulrC (1 - d ord0)%R) mulfK //.
apply/eqP=> /(congr1 (+%R (d ord0))).
rewrite addrCA addrN !addr0 => b'.
by elim b; rewrite -b' eqxx.
Qed.

#[local]
Corollary _equiv_conv p (x y : T) : x <& p &> y = x <| p |> y.
Proof.
rewrite /binconv.
set g := fun (o : 'I_2) => if o == ord0 then x else y.
set d := fdistI2 p.
change x with (g ord0).
change y with (g (lift ord0 ord0)).
have -> : p = probfdist d ord0 by apply: val_inj=> /=; rewrite fdistI2E eqxx.
by rewrite -ConvnI2E convnE equiv_convn.
Qed.

End proof.
End NaryToBinToNary.


(* Export the instantiation of convType from naryConvType *)
Section naryConvType_convType.
Variables (R : realType) (T : naryConvType R).
HB.instance Definition _ := NaryToBin.binconv_mixin T.
End naryConvType_convType.


Module test.
Section test.
Variables (R : realType) (opT : naryConvOpType R).
Variables (axpart : ax_part opT) (axidem : ax_idem opT).

Local Definition T := (opT : Type).

HB.instance Definition _ := NaryConvOp.on T.
HB.instance Definition A := isNaryBeaulieuConvexSpace.Build R T axpart axidem.

(* `Succeed Check T : naryConvType R.` prints noise. Definition does not. *)
Succeed Definition test := T = T :> naryConvType R.
(* Fail Check T : convType R. *)
Fail Definition    test := T = T :> convType R.
(* Succeed Check (T : naryConvType R) : convType R. *)
Succeed Definition test :=
  (T : naryConvType R) = (T : naryConvType R) :> convType R.

End test.
End test.
