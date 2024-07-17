(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix.
From mathcomp Require boolp.
From mathcomp Require Import Rstruct reals.
Require Import Reals Lra.
Require Import ssrR Reals_ext realType_ext logb ssr_ext ssralg_ext.
Require Import bigop_ext fdist proba.

(* from mca master *)
Local Lemma Pos_to_natE p : Pos.to_nat p = nat_of_pos p.
Proof.
by elim: p => //= p <-;
  rewrite ?(Pnat.Pos2Nat.inj_xI,Pnat.Pos2Nat.inj_xO) NatTrec.doubleE -mul2n.
Qed.
Local Lemma IZRposE (p : positive) : IZR (Z.pos p) = INR (nat_of_pos p).
Proof. by rewrite -Pos_to_natE INR_IPR. Qed.
Local Definition coqRE := (IZRposE, coqRE).

(* TODO: update proba.v to use mcR *)
Lemma Ex_ge0 (U : finType) (P : {fdist U})
  (X : {RV P -> R}) : (forall u : U, 0 <= X u) -> 0 <= `E X.
Proof. by move=> H; apply/RleP/Ex_ge0=> u; apply/RleP/H. Qed.
Lemma sq_RV_ge0 (U : finType) (P : {fdist U})
  (X : {RV (P) -> (R)}) (x : U) : 0 <= (X `^2) x.
Proof. exact/RleP/sq_RV_ge0. Qed.
Lemma Pr_lt1 (A : finType) (P : R.-fdist A) (E : {set A}) :
  Pr P E < 1 <-> Pr P E != 1.
Proof. by rewrite -(rwP (RltP (Pr P E) 1)) Pr_lt1. Qed.
Lemma Pr_gt0 (A : finType) (P : R.-fdist A) (E : {set A}) :
  0 < Pr P E <-> Pr P E != 0.
Proof. by rewrite -(rwP (RltP 0 (Pr P E))) Pr_gt0. Qed.
Lemma Pr_ge0 (A : finType) (P : R.-fdist A) (E : {set A}) : 0 <= Pr P E.
Proof. by exact/RleP/Pr_ge0. Qed.
(* should be Pr_subset? *)
Lemma Pr_incl (A : finType) (P : R.-fdist A) (E E' : {set A}) :
  E \subset E' -> Pr P E <= Pr P E'.
Proof. by move/Pr_incl=> ?; exact/RleP. Qed.
(* should be Pr_setC? *)
Lemma Pr_of_cplt (A : finType) (P : R.-fdist A) (E : {set A}) :
  Pr P (~: E) = 1 - Pr P E.
Proof. exact: Pr_of_cplt. Qed.
Lemma Pr_to_cplt (A : finType) (P : R.-fdist A) (E : {set A}) :
  Pr P E = 1 - Pr P (~: E).
Proof. exact: Pr_to_cplt. Qed.
(* should be Pr_setD? *)
Lemma Pr_diff (A : finType) (P : R.-fdist A) (E1 E2 : {set A}) :
  Pr P (E1 :\: E2) = Pr P E1 - Pr P (E1 :&: E2).
Proof. exact: Pr_diff. Qed.
(* should be Pr_add_setC (or PrDsetC)? *)
Lemma Pr_cplt (A : finType) (P : R.-fdist A) (E : {set A}) :
  Pr P E + Pr P (~: E) = 1.
Proof. exact: Pr_cplt. Qed.
(* should be Pr_setI? *)
Lemma Pr_inter_eq (A : finType) (P : R.-fdist A) (E1 E2 : {set A}) :
  Pr P (E1 :&: E2) = Pr P E1 + Pr P E2 - Pr P (E1 :|: E2).
Proof. exact: Pr_inter_eq. Qed.
(* should be Pr_setU? *)
Lemma Pr_union_eq (A : finType) (P : R.-fdist A) (E1 E2 : {set A}) :
  Pr P (E1 :|: E2) = Pr P E1 + Pr P E2 - Pr P (E1 :&: E2).
Proof. exact: Pr_union_eq. Qed.
(* should be Pr_setU_disj (or Pr_disjU)? *)
Lemma Pr_union_disj (A : finType) (P : R.-fdist A) (E1 E2 : {set A}) :
  [disjoint E1 & E2] -> Pr P (E1 :|: E2) = Pr P E1 + Pr P E2.
Proof. exact: Pr_union_disj. Qed.
(* should be Pr_eq0P *)
Lemma Pr_set0P (A : finType) (P : R.-fdist A) (E : {set A}) :
  Pr P E = 0 <-> (forall a : A, a \in E -> P a = 0).
Proof. exact: Pr_set0P. Qed.
Lemma E_sub_RV (U : finType) (P : R.-fdist U) (X Y : {RV (P) -> (R)}) :
  `E (X `- Y) = `E X - `E Y.
Proof. exact: E_sub_RV. Qed.
Lemma E_add_RV (U : finType) (P : R.-fdist U) (X Y : {RV (P) -> (R)}) :
  `E (X `+ Y) = `E X + `E Y.
Proof. exact: E_add_RV. Qed.
Lemma E_scalel_RV (U : finType) (P : R.-fdist U) (X : {RV (P) -> (R)})
  (k : R) : `E (k `cst* X) = k * `E X.
Proof. exact: E_scalel_RV. Qed.

(* TODO: define RV_ringType mimicking fct_ringType *)
Section mul_RV.
Variables (U : finType) (P : {fdist U}).
Definition mul_RV (X Y : {RV P -> R}) : {RV P -> R} := fun x => X x * Y x.
Notation "X `* Y" := (mul_RV X Y) : proba_scope.
Arguments mul_RV /.
Lemma mul_RVA : associative mul_RV.
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite mulrA. Qed.
Lemma mul_RVC : commutative mul_RV.
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite mulrC. Qed.
Lemma mul_RVAC : right_commutative mul_RV.
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite mulrAC. Qed.
Lemma mul_RVCA : left_commutative mul_RV.
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite mulrCA. Qed.
Lemma mul_RVACA : interchange mul_RV mul_RV.
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite mulrACA. Qed.
Lemma mul_RVDr : right_distributive mul_RV (@add_RV U P).
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite mulrDr. Qed.
Lemma mul_RVDl : left_distributive mul_RV (@add_RV U P).
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite mulrDl. Qed.
Lemma mul_RVBr (f g h : {RV (P) -> (R)}) : f `* (g `- h) = f `* g `- f `* h.
Proof. by apply: boolp.funext=> u /=; rewrite mulrBr. Qed.
Lemma mul_RVBl (f g h : {RV (P) -> (R)}) : (f `- g) `* h = f `* h `- g `* h.
Proof. by apply: boolp.funext=> u /=; rewrite mulrBl. Qed.
End mul_RV.
Notation "X `* Y" := (mul_RV X Y) : proba_scope.
Arguments mul_RV /.

Section add_RV.
Variables (U : finType) (P : {fdist U}).
Arguments add_RV /.
Lemma add_RVA : associative (@add_RV U P).
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite addRA. Qed.
Lemma add_RVC : commutative (@add_RV U P).
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite addRC. Qed.
Lemma add_RVAC : right_commutative (@add_RV U P).
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite addRAC. Qed.
Lemma add_RVCA : left_commutative (@add_RV U P).
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite addRCA. Qed.
Lemma add_RVACA : interchange (@add_RV U P) (@add_RV U P).
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite !coqRE addrACA. Qed.
End add_RV.

Section scalelr.
Variables (U : finType) (P : {fdist U}).
Lemma scalel_RVE m (X : {RV P -> R}) : scalel_RV m X = const_RV P m `* X.
Proof. by apply: boolp.funext=> ? /=; rewrite /scalel_RV /const_RV !coqRE. Qed.
Lemma scaler_RVE m (X : {RV P -> R}) : scaler_RV X m = X `* const_RV P m.
Proof. by apply: boolp.funext=> ? /=; rewrite /scaler_RV /const_RV !coqRE. Qed.
End scalelr.
