(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum fingroup perm matrix.
From mathcomp Require Import unstable mathcomp_extra boolp classical_sets.
From mathcomp Require Import functions Rstruct reals.
From mathcomp Require Import finmap.
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
(*   + (and three others)                                                     *)
(*                                                                            *)
(* The n-ary laws and their logical dependencies are listed in                *)
(* `Module NaryConvLaws`.                                                     *)
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
(* isNary( BaryMapConst | BarypartIdem | ProjPartConst )ConvexSpace           *)
(*                == HB factories for three other combinations of the laws    *)
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
(*                                                                            *)
(* Some combinations of the laws are strictly weaker.  They are illustrated   *)
(* in modules `counterexamples_*` at the end of this file.                    *)
(******************************************************************************)

Reserved Notation "'<&>_' d f" (at level 36, f at level 36, d at level 0,
  format "<&>_ d  f").
Reserved Notation "x <& p &> y" (format "x  <& p &>  y", at level 49).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope convex_scope.
Local Open Scope fset_scope.

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
  forall n (i : 'I_n) (g : 'I_n -> T), <&>_(fdist1 i) g = g i.

(* Beaulieu's version [Beaulieu PhD 2008] *)
Definition ax_part :=
  forall n m (K : 'I_m -> 'I_n) (d : R.-fdist 'I_m) (g : 'I_m -> T),
    <&>_d g = <&>_(fdistmap K d) (fun i => <&>_(FDistPart.d K d i) g).
Definition ax_idem :=
  forall (a : T) n (d : R.-fdist 'I_n) (g : 'I_n -> T),
    (forall i, i \in fdist_supp d -> g i = a) -> <&>_d g = a.

(* Alternative to ax_proj *)
Definition ax_map :=
  forall n m (u : 'I_m -> 'I_n) (d : R.-fdist 'I_m) (g : 'I_n -> T),
    <&>_d (g \o u) = <&>_(fdistmap u d) g.
Definition ax_const :=
  forall (a : T) n (d : R.-fdist 'I_n), <&>_d (fun _ => a) = a.

(* Alternative to ax_part, just a restriction of ax_bary *)
Definition ax_barypart :=
  forall n m (d : R.-fdist 'I_n) (e : 'I_n -> R.-fdist 'I_m) (g : 'I_m -> T),
    (forall i j, i != j ->
      fdist_supp (e i) :&: fdist_supp (e j) = finset.set0) ->
    <&>_d (fun i => <&>_(e i) g) = <&>_(fdist_convn d e) g.

(* Restriction of ax_map to injective maps *)
Definition ax_injmap :=
  forall n m (u : 'I_m -> 'I_n) (d : R.-fdist 'I_m) (g : 'I_n -> T),
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
  by case: ifP => // /Hd ->; rewrite (Hd k).
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
  have [isupp|isupp] := boolP (i \in supp).
  - rewrite (bigD1 i) /=; last by rewrite inE /f /f' /= enum_rankK_in.
    rewrite big1 ?addr0// => j /andP[] /eqP <-.
    have [?|] := boolP (j \in supp).
      by rewrite /f /f' /= enum_rankK_in // eqxx.
    by rewrite inE negbK => /eqP.
  - rewrite big_pred0.
      by move: isupp; rewrite inE negbK => /eqP.
    move=> j; apply/negP => /eqP ff'ji.
    by move: isupp; rewrite -ff'ji enum_valP.
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
move=> axpart axidem n m d e g e0.
have [n0 Hn0] := fdist_supp_mem d.
set h' : 'I_n -> 'I_#|fdist_supp d| := enum_rank_in Hn0.
set h : 'I_#|fdist_supp d| -> 'I_n := enum_val.
have f j : {i | [forall i, j \notin fdist_supp (e (h i))] ||
                (j \in fdist_supp (e (h i)))}.
  have [_|] := boolP [forall i, j \notin fdist_supp (e (h i))].
    by exists (proj1_sig (fdist_supp_mem (fdistmap h' d))).
  by rewrite -negb_exists negbK => /existsP; exact: sigW.
rewrite [LHS](axpart _ _ h').
rewrite [RHS](axpart _ _ (fun j => proj1_sig (f j))).
have trivIK i j x : x \in fdist_supp (e i) -> x \in fdist_supp (e j) -> i = j.
  have [//| + xi xj] := eqVneq i j.
  by move/e0 => /setP/(_ x); rewrite inE xi xj inE.
have neqj j a k :
    a \in fdist_supp (e (h j)) -> k != h j -> (d k * e k a = 0)%R.
  move=> aj kj.
  have [ak|] := boolP (a \in fdist_supp (e k)).
    by rewrite (trivIK _ _ _ aj ak) eqxx in kj.
  by rewrite inE negbK => /eqP ->; rewrite mulr0.
have maph' i : fdistmap h' d i = (\sum_j d (h i) * e (h i) j)%R.
  rewrite -big_distrr fdistE /= FDist.f1 /= mulr1.
  rewrite (bigD1 (h i)) /=; last by rewrite /h /h' !inE enum_valK_in eqxx.
  rewrite big1 /= ?addr0 // => j /andP[] /eqP <-.
  have [jd|] := boolP (j \in fdist_supp d).
    by rewrite /h /h' (enum_rankK_in Hn0 jd) eqxx.
  by rewrite inE negbK => /eqP.
have Hmap i :
  fdistmap (fun j : 'I_m => sval (f j)) (fdist_convn d e) i =
    fdistmap h' d i.
  rewrite fdistE big_mkcond /=.
  under eq_bigr do rewrite fdistE.
  rewrite (eq_bigr (fun j => d (h i) * e (h i) j)%R).
    by rewrite maph'.
  move=> /= a _; rewrite !inE; case: (f a) => j /= /orP[/forallP /= |] Ha.
    have dea0 k : (d k * e k a = 0)%R.
      have [Hk|] := boolP (k \in fdist_supp d).
        have := Ha (h' k).
        by rewrite inE negbK /h/h' enum_rankK_in // => /eqP ->; rewrite mulr0.
      by rewrite inE negbK => /eqP -> ; rewrite mul0r.
    by case: ifPn => [|] _; rewrite ?dea0// big1.
  case: ifPn => [/eqP/esym ->{i}|ji].
    by rewrite (bigD1 (h j)) //= big1 ?addr0 // => *; rewrite (neqj j).
  by rewrite (neqj j) //; apply: contra ji => /eqP/enum_val_inj ->.
congr (<&>_ _ _); first by apply: fdist_ext => /= i; rewrite Hmap.
apply: funext => i /=.
have HF : fdistmap h' d i != 0%R.
  rewrite fdistE /=.
  apply/eqP => /psumr_eq0P H.
  have : h i \in fdist_supp d by apply: enum_valP.
  by rewrite inE H ?eqxx // 2!inE /h /h' enum_valK_in.
rewrite (axidem (<&>_(e (h i)) g)); last first.
  move=> /= j; rewrite inE FDistPart.dE //.
  have [Hj|] := boolP (j \in fdist_supp d).
    have [->|] := eqVneq i (h' j).
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
      by have := enum_valP i => /[!inE] /negPf ->.
    by apply/sumr_ge0 => *; apply/sumr_ge0 => *; rewrite mulr_ge0.
  move=> /= k _; rewrite 2!inE; case: ifP => //.
  case: (f k) => /= x /orP[/forallP/(_ i)|Hkx Hx].
    by rewrite inE negbK => /eqP ->.
  have [Hki|] := boolP (k \in fdist_supp (e (h i))).
    move/eqP: (trivIK _ _ _ Hkx Hki) Hx.
    by rewrite (can_eq (enum_valK_in Hn0)) => ->.
  by rewrite inE negbK => /eqP ->.
have := Hmap i.
rewrite fdistE /= => ->.
rewrite fdistE.
case: (f j) => /= k /orP[Hn|jk].
  move/forallP/(_ i): (Hn).
  rewrite inE negbK => /eqP ->.
  rewrite big1 ?mul0r// => a _.
  move/forallP/(_ (h' a)) : Hn.
  case/boolP: (a \in fdist_supp d).
    rewrite /h /h'.
    move/(enum_rankK_in _) ->.
    by rewrite inE negbK => /eqP ->; rewrite mulr0.
  by rewrite inE negbK => /eqP ->; rewrite mul0r.
rewrite (bigD1 (h k)) //= big1 ?addr0; last first.
  by move=> a ?; exact: (neqj k).
have [|ji] := boolP (j \in fdist_supp (e (h i))).
  move=> /(trivIK _ _ _ jk) /enum_val_inj ->.
  move: HF; rewrite eqxx mulr1 maph'.
  rewrite -big_distrr /= FDist.f1 mulr1 => dhi0.
  by rewrite mulrAC mulfV// mul1r.
case: eqP ji => [->|ik]; first by rewrite jk.
by rewrite inE negbK => /eqP ->; rewrite mulr0 mul0r.
Qed.

Lemma ax_injmap_of_barypart_idem : ax_barypart T -> ax_idem T -> ax_injmap T.
Proof.
move=> axbarypart axidem n m u d g inju.
have -> : fdistmap u d = fdist_convn d (fun i => fdist1 (u i)).
  by apply: fdist_ext => i; rewrite /fdistmap fdistbindE// fdist_convnE.
rewrite -axbarypart.
- congr (<&>_ _ _); apply: funext => j /=; symmetry; apply: axidem => i.
  by rewrite supp_fdist1 inE => /eqP ->.
- move=> x y xy; apply/setP => z; rewrite !supp_fdist1 !inE.
  by apply/negP => /andP[/eqP -> /eqP/inju]; exact/eqP.
Qed.

Corollary ax_injmap_of_part_idem : ax_part T -> ax_idem T -> ax_injmap T.
Proof.
move=> axpart axidem.
apply: ax_injmap_of_barypart_idem => //.
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
  by rewrite axinjmap // => x y; rewrite /h => /enum_rank_inj [].
rewrite axbarypart; first last.
  move=> i j ij; apply/setP => x; rewrite !inE !fdistE.
  move: ij; have [-> ij|ij] := eqVneq i (f' x).1.
    rewrite [in X in _ && X]big_pred0 ?eqxx ?andbF // => k; apply/eqP.
    by move: ij => /[swap] <-; rewrite /h /f /f' enum_rankK eqxx.
  rewrite big_pred0 ?eqxx // => k; apply/eqP => hik.
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
  move: ij; have [<-| ij] := eqVneq (f' x).2 i; last by rewrite mulr0 eqxx.
  by have [<-//|_ _] := eqVneq (f' x).2 j; rewrite mulr0 eqxx.
congr (<&>_ _ _); apply: fdist_ext => k.
rewrite /d1 !fdistE.
under eq_bigr do rewrite fdistE big_distrr big_mkcond /=.
rewrite exchange_big /=; apply: eq_bigr => j _.
rewrite !fdistE -big_mkcond /=.
rewrite (big_pred1 (f' k)); last first.
  by move=> a; rewrite !inE -{1}(enum_valK k) /f (can_eq enum_rankK).
set p := f' k => /=.
have [->|Hj] := eqVneq j p.2; last first.
  rewrite big_pred0; last first.
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
  exact: ax_injmap_of_part_idem.
exact: ax_barypart_of_part_idem.
Qed.

(* Copied from Corelib of Rocq 9.0 for compatibility with Coq 8.20 *)
Local Definition sumbool_of_bool (b : bool) : {b = true} + {b = false} :=
  if b return {b = true} + {b = false} then left erefl else right erefl.

(* Added on [2025-Jul-22]; a new combination? *)
Lemma ax_idem_of_proj_part_const :
  ax_proj T -> ax_part T -> ax_const T -> ax_idem T.
Proof.
move=> axproj axpart axconst.
move=> a n d g gia.
have [e esd] := fdist_supp_mem d.
pose supp := [fset i in fdist_supp d].
have es : e \in supp by rewrite inE.
pose m := #|` supp |.
pose K' (i : 'I_n) : supp :=
  match sumbool_of_bool (i \in supp) with
  | left suppP => [` suppP]
  | right _ => [` es]
  end.
have im (x : 'I_n) (xs : x \in supp) := eq_rect _ _ xs _ (esym (index_mem _ _)).
pose os (s : supp) : 'I_m := Ordinal (im (\val s) (valP s)).
pose K := os \o K'.
have K_nth (i : 'I_m) : K (nth e supp i) = i.
  apply/val_inj; rewrite /K /os /K'/=.
  case: sumbool_of_bool; first by move=> ? /=; rewrite index_uniq// fset_uniq.
  by rewrite mem_nth.
rewrite (axpart _ _ K).
under [F in <&>_ _ F]funext=> i.
  rewrite [d in <&>_d _](_ : _ = fdist1 (nth e supp i)).
    rewrite axproj gia; first by over.
    suff: nth e supp i \in supp by rewrite inE.
    by apply: mem_nth; rewrite -/m.
  apply: fdistpart_eq1; apply/andP; split; last by rewrite K_nth.
  rewrite finset.eqEsubset; apply/andP.
  split; apply/fintype.subsetP=> j /[!inE]/=.
    case/andP => dj0 /eqP.
    rewrite /K /os /K' => /(congr1 \val)/=.
    case: sumbool_of_bool => /=; first by move=> ? <-; rewrite nth_index.
    by rewrite !inE dj0.
  move/eqP=> ->.
  have : nth e supp i \in supp by rewrite mem_nth.
  by rewrite K_nth !inE => -> /=.
by rewrite axconst.
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

Lemma axmap : ax_map T.
Proof. by apply: ax_map_of_bary_proj; [exact: axbary | exact: axproj]. Qed.

Lemma axconst : ax_const T.
Proof. exact/ax_const_of_idem/axidem. Qed.

Lemma axbarypart : ax_barypart T.
Proof. exact/ax_barypart_of_bary/axbary. Qed.

Lemma axinjmap : ax_injmap T.
Proof. apply: ax_injmap_of_part_idem; [exact: axpart | exact: axidem]. Qed.

End lemmas.
End NaryConvexSpaceTheory.

Import NaryConvexSpaceTheory.

(* The following combinations of the laws are equivalent:
   - ax_bary + ax_proj (Bonchi)
   - ax_part + ax_idem (Beaulieu)
   - ax_bary + ax_map + ax_const
   - ax_barypart + ax_idem
   - ax_proj + ax_part + ax_const
   This has been implicitly shown as logical implications in Module NaryLaws.
   Module NaryConvexSpaceTheory says that Bonchi subsumes the other three.
   We now exhibit the remaining equivalences by providing Hierarchy-Builder
   factories for the others.
 *)

HB.factory Record isNaryBeaulieuConvexSpace
    (R : realType) (T : Type) of NaryConvOp R T := {
  axpart : ax_part T ;
  axidem : ax_idem T
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
  axbary : ax_bary T ;
  axmap : ax_map T ;
  axconst : ax_const T
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


HB.factory Record isNaryProjPartConstConvexSpace
  (R : realType) (T : Type) of NaryConvOp R T := {
  axproj : ax_proj T;
  axpart : ax_part T;
  axconst : ax_const T;
}.

HB.builders Context R T of isNaryProjPartConstConvexSpace R T.

Lemma axidem : ax_idem T.
Proof.
by apply: ax_idem_of_proj_part_const;
   [exact: axproj | exact: axpart | exact: axconst].
Qed.

HB.instance Definition _ := isNaryBeaulieuConvexSpace.Build R T axpart axidem.

HB.end.

(* naryConvType is equivalent to convType,
   the binary axiomatization formalized in convex.v.
   We prove this equivalence in two steps.

   First prove mutual definability between convType and naryConvType *)

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
  by have /orP[|] := ord2 i => /eqP -> /=; rewrite (tpermL,tpermR).
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
rewrite [X in <&>_(fdistI2 [r_of p, q]) X](_ : _ = g \o widen_ord (leqnSn 2)); last first.
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
case: j => -[|[|[]]] //= ?; rewrite ?(mulr1,mulr0,add0r).
- rewrite [in RHS](big_pred1 ord0)// big1; last by move=> [] [].
  by rewrite fdistI2E/= mulr0 !addr0 mulrC -p_is_rs.
- rewrite (big_pred1 ord0) // (big_pred1 (Ordinal (ltnSn 1))) //.
  by rewrite !fdistI2E/= addr0 pq_is_rs mulrC.
- rewrite (big_pred1 (Ordinal (ltnSn 1)))// big1; last by case => -[|[]].
  by rewrite !fdistI2E/= mulr0 add0r s_of_pqE onemK.
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
pose g := fun x : 'I_2 => if x == ord0 then a else b.
rewrite -[a]/(g ord0).
rewrite -[b]/(g (lift ord0 ord0)).
pose d := fdistI2 p.
rewrite [in LHS](_ : p = probfdist d ord0).
  by rewrite -!ConvnI2E convnE.
by apply: val_inj=> /=; rewrite fdistI2E eqxx.
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
elim: n d g => [d|n IH d g /=].
  by have := fdist_card_neq0 d; rewrite card_ord.
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
apply/eqP => /(congr1 (+%R (d ord0))).
rewrite addrCA addrN !addr0 => d01.
by move: b {d'}; rewrite -d01 eqxx.
Qed.

#[local]
Corollary _equiv_conv p (x y : T) : x <& p &> y = x <| p |> y.
Proof.
rewrite /binconv.
set g := fun o : 'I_2 => if o == ord0 then x else y.
set d := fdistI2 p.
rewrite -[x]/(g ord0).
rewrite -[y]/(g (lift ord0 ord0)).
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
Succeed Definition test := T : naryConvType R.
Fail    Definition test := T : convType R.
Succeed Definition test := (T : naryConvType R) : convType R.

End test.
End test.

(*
Counterexamples to show that some combinations are strictly weaker:
- ax_bary /\ ax_const /\ ~ ax_proj
- ax_proj /\ ax_part /\ ~ ax_const (therefore, ~ ax_idem)
- ax_part /\ ax_const /\ ~ ax_proj
*)

Module counterexample_bary_const_noproj.
Section counterexample.
Local Open Scope ring_scope.
Variable (R : realType).

(* first projection, ignoring d *)
Example proj_1st n :=
  if n is n'.+1 return (R.-fdist 'I_n) -> ('I_n -> bool) -> bool
  then fun _ g => g ord0
  else fun _ _ => 0.

Fail Definition test := bool : naryConvOpType R.
HB.instance Definition _ := hasNaryConvOp.Build R bool proj_1st.
Succeed Definition test := bool : naryConvOpType R.

Fact axbary : ax_bary bool.
Proof.
move=> n m d.
have /prednK := fdist_card_neq0 d.
rewrite card_ord; move: d => /[swap] <- d e.
have /prednK := fdist_card_neq0 (e ord0).
by rewrite card_ord; move: e => /[swap] <- e g.
Qed.

Fact axconst : ax_const bool.
Proof.
move=> c n d.
have /prednK := fdist_card_neq0 d.
by rewrite card_ord; move: d => /[swap] <- d.
Qed.

Fact noproj : ~ ax_proj bool.
Proof.
by rewrite /ax_proj => /(_ 2 (inord 1) (fun o => o%:R)); rewrite /convn inordK.
Qed.

End counterexample.
End counterexample_bary_const_noproj.

Module counterexample_proj_part_noconst_noidem.
Section counterexample.
Local Open Scope ring_scope.
Variables (R : realType).

(* flat sum, equalizing all probabilities to 1 *)
Example weight1_sum n (d : R.-fdist 'I_n) (g : 'I_n -> nat) :=
  \sum_(i < n) if d i == 0 then 0 else g i.

Fail Definition test := nat : naryConvOpType R.
HB.instance Definition _ := hasNaryConvOp.Build R nat weight1_sum.
Succeed Definition test := nat : naryConvOpType R.

Fact axproj : ax_proj nat.
Proof.
move=> n i g.
rewrite /convn/= /weight1_sum/= (bigD1 i)//= fdist1xx oner_eq0 big1 ?addr0//.
by move=> j ji; rewrite fdist10// eqxx.
Qed.

Fact axpart : ax_part nat.
Proof.
move=> n m K d g.
rewrite /convn/= /weight1_sum/=.
rewrite (bigID (fun i => fdistmap K d i == 0))/=.
rewrite [X in _ = X + _]big1 ?add0r/=; last by move=> ? ->.
under [RHS]eq_bigr=> i /negPf -> do [].
rewrite exchange_big/=; apply: eq_bigr=> i _.
rewrite big_mkcond (bigD1 (K i))//=.
rewrite big1; last first.
  move=> j Kij; case: ifPn => // /FDistPart.dE ->.
  by rewrite (negPf Kij) mulr0 mul0r eqxx.
rewrite addr0 -(if_neg (FDistPart.d _ _ _ _ == 0)) -if_and -if_neg.
congr (if _ then _ else _).
apply/idP/idP => [di|/andP[di]].
  have: fdistmap K d (K i) != 0.
    rewrite fdistmapE/= psumr_neq0/=; last by move=> *; exact: FDist.ge0.
    apply/hasP; exists i; first by rewrite mem_index_enum.
    by rewrite inE/= eqxx /= fdist_gt0.
  move=> /[dup] map0 -> /=.
  rewrite FDistPart.dE// eqxx mulr1 mulf_neq0//= invr_neq0//.
  rewrite psumr_neq0/=; last by move=> *; exact: FDist.ge0.
  apply/hasP; exists i; last by rewrite eqxx/= fdist_gt0.
  by rewrite mem_index_enum.
rewrite FDistPart.dE// eqxx mulr1.
by apply: contraNneq => ->; rewrite mul0r.
Qed.

Fact noconst : ~ ax_const nat.
Proof.
rewrite /ax_const.
move/(_ 1 2 (fdist_uniform (fdist_card_prednK (@fdist1 R _ ord0)))).
rewrite /convn/= /weight1_sum/=.
under eq_bigr.
  move=> i _.
  rewrite fdist_uniformE invr_eq0 card_ord (_ : 0 = 0%:R)// eqr_nat/=.
  over.
by rewrite big_const_ord iter_addr_0 natn.
Qed.

Corollary noidem : ~ ax_idem nat.
Proof. by move: noconst; exact/contra_not/ax_const_of_idem. Qed.

End counterexample.
End counterexample_proj_part_noconst_noidem.

Module counterexample_part_const_noproj.
Section counterexample.
Local Open Scope ring_scope.
Variables (R : realType).

(* bad bigmin that does not respect d *)
Example bigand n (d : R.-fdist 'I_n) (g : 'I_n -> bool) :=
  \big[andb/true]_(i < n) g i.

Fail Definition test := bool : naryConvOpType R.
HB.instance Definition _ := hasNaryConvOp.Build R bool bigand.
Succeed Definition test := bool : naryConvOpType R.

Fact axconst : ax_const bool.
Proof.
move=> a n d.
have [e] := fdist_supp_mem d.
rewrite inE => de0.
rewrite /convn/= /bigand/= big_const -sum1_card (bigD1 e)//=.
by rewrite andb_idr// => ->; rewrite add0n iter_fix.
Qed.

Fact axpart : ax_part bool.
Proof.
move=> n m K d g.
rewrite /convn/= /bigand/= exchange_big/=; apply: eq_bigr=> i _.
rewrite big_const -sum1_card (bigD1 (K i))//= add0n.
by rewrite andb_idr// => ->; rewrite iter_fix.
Qed.

Fact noproj : ~ ax_proj bool.
Proof.
rewrite /ax_proj /convn/= /bigand/= => /(_ 2 ord0 (xpred1 ord0)).
by rewrite big_ord_recl/= big_ord1.
Qed.

End counterexample.
End counterexample_part_const_noproj.

(* compare to the previous counterexample *)
Module example_proj_part_const.
Section example.
Local Open Scope ring_scope.
Variables (R : realType).

(* (good) bigmin in bool *)
Example bigand n (d : R.-fdist 'I_n) (g : 'I_n -> bool) :=
  \big[andb/true]_(i < n) if d i == 0 then true else g i.

Fail Definition test := bool : naryConvOpType R.
HB.instance Definition _ := hasNaryConvOp.Build R bool bigand.
Succeed Definition test := bool : naryConvOpType R.

Fact axproj : ax_proj bool.
Proof.
move=> n i g.
rewrite /convn/= /bigand/= (bigD1 i)//= (fdist1xx _ i) oner_eq0/=.
by rewrite big1 ?andbT// => j ij; rewrite fdist10// eqxx.
Qed.

Fact axpart : ax_part bool.
Proof.
move=> n m K d g.
rewrite /convn/= /bigand/=.
rewrite [RHS](bigID (fun i => fdistmap K d i == 0))/=.
rewrite [X in X && _]big1/=; last by move=> i ->.
under [RHS]eq_bigr => i /[dup] H /negPf-> /=.
  under eq_bigr do rewrite FDistPart.dE//.
  over.
rewrite exchange_big/=; apply: eq_bigr=> i _.
have [->|di0] := eqVneq (d i) 0.
  by rewrite big1// => ? ?; rewrite !mul0r eqxx.
rewrite (bigID (xpred1 (K i)))/=.
under eq_bigr => j /andP[] dj jKi.
  move: dj; rewrite fdistmapE/=.
  (under eq_bigl do rewrite inE/=) => dj.
  rewrite !mulf_eq0 (negPf di0)/= invr_eq0 (negPf dj) jKi oner_eq0/=.
  over.
rewrite big_const/=.
under eq_bigr => j /andP [] dj /negPf -> do rewrite mulr0 mul0r eqxx.
rewrite big1// andbT.
rewrite -sum1_card (bigD1 (K i))/= ?add0n; last first.
  apply/andP; split=> //.
  rewrite fdistmapE/= psumr_neq0/= ?FDist.ge0//.
  apply/hasP; exists i; first by rewrite mem_index_enum.
  by rewrite inE/= eqxx fdist_gt0.
by rewrite andb_idr// => ->; rewrite iter_fix.
Qed.

Fact axconst : ax_const bool.
Proof.
move=> a n d.
have [e] := fdist_supp_mem d.
rewrite !inE => de0.
rewrite /convn/= /bigand/= (bigD1 e)//= (negPf de0) andb_idr// => ->.
under eq_bigr do rewrite if_same.
by rewrite big_const/= iter_fix.
Qed.

End example.
End example_proj_part_const.
