(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import Rstruct.
Require Import Reals.
Require Import ssrR Rbigop.

Local Open Scope ring_scope.
Delimit Scope R_scope with coqR.

Import (*GRing.Theory Num.Theory*) Order.Theory.

(* NB: this lemma depends on the internals of Rinv and Rinvx *)
Lemma RinvE' (x : R) : (/ x)%coqR = x^-1.
Proof.
have [-> | ] := eqVneq x 0%coqR; last exact: RinvE.
rewrite /GRing.inv /GRing.mul /= /Rinvx eqxx /=.
rewrite RinvImpl.Rinv_def.
case: (Req_appart_dec 0 R0) => //.
by move=> /[dup] -[] => /RltP; rewrite ltxx.
Qed.

Lemma RdivE' (x y : R) : (x / y)%coqR = x / y.
Proof. by rewrite ssrR.divRE RinvE'. Qed.

Lemma bigmaxRE (I : Type) (r : seq I) (P : pred I) (F : I -> R) :
  \rmax_(i <- r | P i) F i = \big[Order.max/0]_(i <- r | P i) F i.
Proof.
rewrite /Rmax /Order.max/=.
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

Lemma R1E : 1%coqR = GRing.one _.
Proof. by []. Qed.
Lemma R0E : 0%coqR = GRing.zero _.
Proof. by []. Qed.

Definition coqRE :=
  (R0E, R1E, INRE,
    RinvE', RoppE, RdivE', RminusE, RplusE, RmultE, RpowE).
