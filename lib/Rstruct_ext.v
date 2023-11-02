(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra Rstruct reals.
Require Import Reals.
Require Import ssrR Reals_ext ssr_ext ssralg_ext Rbigop f2 fdist proba.
Require Import realType_ext.

Import (*GRing.Theory Num.Theory*) Order.Theory.

Local Open Scope ring_scope.

(* NB: this lemma depends on the internals of Rinv and Rinvx *)
Lemma RinvE' (x : R) : (/ x)%coqR = x^-1.
Proof.
have [-> | ] := eqVneq x 0%coqR; last exact: RinvE.
rewrite /GRing.inv /GRing.mul /= /Rinvx eqxx /=.
rewrite RinvImpl.Rinv_def.
case: (Req_appart_dec 0 R0) => //.
by move=> /[dup] -[]; move: (ltRR 0) => /[apply].
Qed.

Lemma RdivE' (x y : R) : (x / y)%coqR = x / y.
Proof. by rewrite divRE RinvE'. Qed.

Lemma bigmaxRE (I : Type) (r : seq I) (P : pred I) (F : I -> R) :
  \rmax_(i <- r | P i) F i = \big[Order.max/0]_(i <- r | P i) F i.
Proof.
rewrite /Rmax /Order.max -R0E /=.
congr BigOp.bigop.
apply: boolp.funext=> i /=.
congr BigBody.
apply: boolp.funext=> x /=.
apply: boolp.funext=> y /=.
rewrite lt_neqAle.
case: (Rle_dec x y); move/RleP;
  first by case/boolP: (x == y) => /= [/eqP -> | _ ->].
by move/negPf->; rewrite andbF.
Qed.

Definition coqRE :=
  (R0E, R1E, INRE,
    RinvE', RoppE, RdivE', RminusE, RplusE, RmultE, RpowE).
