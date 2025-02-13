(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg finalg poly polydiv cyclic.
From mathcomp Require Import perm matrix mxpoly vector mxalgebra zmodp.
Require Import ssr_ext ssralg_ext linearcode dft poly_decoding.

(**md**************************************************************************)
(* # Generalized Reed-Solomon Codes                                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope vec_ext_scope.

Module GRS.

Section GRS_def.
Variables (n : nat).
Variable (F : finFieldType).
Variable a : 'rV[F]_n.
Hypothesis a_inj : injective [ffun i => a``_i]. (* pairwise distinct *)
Variable b : 'rV[F]_n.
Hypothesis b_neq0 : forall i, b ``_ i != 0.
Variable k : nat.
Hypothesis Hk : 1 <= k <= n.

(* 'rV[F]_k = polynomials of deg < k *)
Definition codebook :=
  [set \row_i ((rVpoly f).[a ``_ i] * (b ``_ i)) | f in 'rV[F]_k].

(* r = d - 1 *)
Definition PCM r : 'M_(r, n):= Vandermonde r a *m diag_mx b.

Definition syndrome_coord (i : nat) (y : 'rV_n) :=
  \sum_(j < n) y ``_ j * b ``_ j * (a ``_ j) ^+ i.

Definition syndrome r (y : 'rV_n) : 'rV[F]_r := \row_i (syndrome_coord i y).

Lemma syndromeE r y : syndrome r y = linearcode.syndrome (PCM r) y.
Proof.
apply/rowP => l; rewrite !mxE; apply/eq_bigr => /= i _.
rewrite 2!mxE [in RHS]mulrC -mulrA; congr (_ * _).
rewrite (bigD1 i) //= !mxE eqxx /= mulr1n mulrC.
apply/eqP; rewrite addrC -subr_eq subrr; apply/eqP.
rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addr0 // => j ji.
by rewrite !mxE (negbTE ji) mulr0n mulr0.
Qed.

Definition syndrome_coord_supp (l : nat) (y : 'rV_n) :=
  \sum_(j in supp y) y ``_ j * b ``_ j * (a ``_ j) ^+ l.

Lemma syndrome_coord_suppE l y : syndrome_coord l y = syndrome_coord_supp l y.
Proof.
rewrite /syndrome_coord (bigID (fun i => i \in supp y)) /=.
rewrite addrC (eq_bigr (fun=> 0)); last first.
  by move=> i; rewrite inE negbK => /eqP ->; rewrite 2!mul0r.
by rewrite big_const iter_addr0 add0r.
Qed.

Definition syndromep r y := \poly_(l < r) (syndrome_coord l y).

Lemma syndromepE r y :
  syndromep r y = \sum_(i in supp y)
     (y ``_ i * b ``_ i)%:P * (\sum_(l < r) (a ``_ i ^+ l)%:P * 'X^l).
Proof.
rewrite /syndromep poly_def.
rewrite (eq_bigr (fun i : 'I_r=> 'X^i * (syndrome_coord i y)%:P)); last first.
  by move=> i _; rewrite mulrC -scale_polyE.
rewrite (eq_bigr (fun i : 'I_r => 'X^i * (syndrome_coord_supp i y)%:P)); last first.
  move=> i _.
  by rewrite syndrome_coord_suppE.
rewrite /syndrome_coord_supp.
rewrite (eq_bigr (fun i : 'I_r => (\sum_(j in supp y) 'X^i * (y ``_ j * b ``_ j * a ``_ j ^+ i)%:P))); last first.
  move=> i _.
  by rewrite -big_distrr /= (big_morph (id1:=0) (fun x => x%:P) (@polyCD _)).
rewrite exchange_big /=.
rewrite (eq_bigr (fun j => (y ``_ j * b ``_ j)%:P * \sum_(l < r) ((a ``_ j ^+ l)%:P * 'X^l))) //.
move=> i isupp.
rewrite !big_distrr /=; apply eq_bigr => j _.
by rewrite mulrC mulrA polyCM.
Qed.

Lemma syndromep_syndrome r y : (syndrome r y == 0) = (syndromep r y == 0).
Proof.
apply/idP/idP; rewrite /syndrome /syndromep => H0.
  apply/eqP/polyP => i.
  rewrite coef0 coef_poly; case: ifPn => // ir.
  by move/eqP/rowP : H0 => /(_  (Ordinal ir)); rewrite !mxE.
apply/eqP/rowP => i.
rewrite mxE.
move/eqP/polyP : H0 => /(_ i); rewrite coef0 coef_poly (ltn_ord i) => ->.
by rewrite mxE.
Qed.

End GRS_def.

End GRS.

Section GRS_rank.
Variables (F : finFieldType) (n' : nat).
Let n := n'.+1.
Variable (r : nat).

Definition GRS_PCM_sq (a b : 'rV[F]_n) r :=
  \matrix_(i < r, j < r) (GRS.PCM a b r) i (inord j).

Lemma GRS_PCM_sq_vander (a b : 'rV[F]_n) (rn : r <= n) :
  GRS_PCM_sq a b r =
    Vandermonde r (\row_(i < r) a``_(inord i)) *m
      diag_mx (\row_(i < r) b``_(inord i)).
Proof.
apply/matrixP => i j.
rewrite !mxE (bigID (fun i : 'I_n => i < r)) /=.
rewrite [in X in _ + X = _](eq_bigr (fun=> 0)); last first.
  move=> l lr.
  rewrite !mxE (_ : l == inord j = false); last first.
    apply/negbTE; apply: contra lr => /eqP ->.
    by rewrite inordK // (leq_trans (ltn_ord j)).
  by rewrite mulr0n mulr0.
rewrite big_const iter_addr0 addr0 big_ord_narrow //.
apply/eq_bigr => l _.
have Hl : widen_ord rn l = inord l.
  apply val_inj => /=; by rewrite inordK // (leq_trans (ltn_ord l)).
rewrite !mxE Hl; congr (_ * (_ *+ _ )).
rewrite (_ : inord j = widen_ord rn j) -?Hl //.
apply val_inj => /=; by rewrite inordK //(leq_trans (ltn_ord j)).
Qed.

Variable (a : 'rV[F]_n).
Hypothesis a_inj : injective [ffun i => a``_i]. (* pairwise distinct *)

Lemma rank_GRS_PCM_sq (b : 'rV_n) (rn : r <= n) (b0 : forall i, b ``_i != 0) :
  \rank (GRS_PCM_sq a b r) = r.
Proof.
apply mxrank_unit.
rewrite unitmxE unitfE GRS_PCM_sq_vander // det_mulmx mulf_neq0 //; last first.
  by rewrite det_diag prodf_seq_neq0; apply/allP => /= i _; rewrite mxE b0.
case: r rn => [|r' rn]; first by rewrite det_mx00 oner_neq0.
rewrite det_Vandermonde prodf_seq_neq0; apply/allP => /= i _.
rewrite prodf_seq_neq0; apply/allP => /= j _; apply/implyP.
rewrite ltnNge => ij; rewrite !mxE subr_eq0; apply: contra ij => /eqP ij.
move: (@a_inj (inord i) (inord j)); rewrite !ffunE ij => /(_ erefl).
move/(congr1 (@nat_of_ord n)).
rewrite inordK // ?(leq_trans (ltn_ord i)) // => ->.
by rewrite inordK // (leq_trans (ltn_ord j)).
Qed.

Lemma rank_GRS_PCM (b : 'rV[F]_n) (rn : r <= n) (b0 : forall i, b ``_i != 0) :
  \rank (GRS.PCM a b r) = r.
Proof.
set lhs := GRS.PCM _ _ _.
set lhs' := castmx (erefl r, esym (subnKC rn)) lhs.
set K1 := lsubmx lhs'.
set K2 := rsubmx lhs'.
rewrite -(mxrank_castmx lhs (erefl r) (esym (subnKC rn))).
rewrite -/lhs' -(hsubmxK lhs') rank_row_mx //.
suff -> : lsubmx lhs' = GRS_PCM_sq a b r by rewrite rank_GRS_PCM_sq.
rewrite /lhs' /lhs GRS_PCM_sq_vander //.
apply/matrixP => i j.
rewrite !mxE castmxE !mxE /=.
rewrite (bigID (fun x : 'I_n => x < r) xpredT) /=.
rewrite [in X in _ + X = _](eq_bigr (fun=> 0)); last first.
  move=> k kj; rewrite !mxE esymK (_ : _ == _ = false).
    by rewrite mulr0n mulr0.
  apply/negbTE; by apply: contra kj => /eqP -> /=.
rewrite big_const iter_addr0 addr0.
rewrite big_ord_narrow //.
apply eq_bigr => k _.
rewrite !mxE /=.
rewrite (_ : widen_ord _ _ = inord k); last first.
  apply val_inj => /=; by rewrite inordK // (leq_trans (ltn_ord k)).
congr (_ * (_ *+ nat_of_bool _)).
rewrite esymK.
apply/idP/idP => [|/eqP ->]; last first.
  apply/eqP/val_inj => /=.
  by rewrite inordK // (leq_trans (ltn_ord j)).
move/eqP/(congr1 (@nat_of_ord n)).
rewrite inordK; last by rewrite (leq_trans (ltn_ord k)).
move=> Hk.
apply/eqP/ord_inj; by rewrite Hk.
Qed.

End GRS_rank.

Section reduced_key_equation.
Variables (F : finFieldType) (n : nat) (y : 'rV[F]_n).
Let E := supp y.
Variables b a : 'rV[F]_n.

Definition Sigma : {poly F} := errloc a E.

Definition Omega : {poly F} := @erreval F n b a y.

Definition GRS_mod r : {poly F} :=
  \sum_(i in supp y) y ``_ i *: (\prod_(i0 in E | i0 != i) ((1 - a ``_ i0 *: 'X))) * (a ``_ i ^+ r)%:P * - (b ``_ i)%:P.

Lemma GRS_key_equation r :
  Sigma * GRS.syndromep a b r y = Omega + GRS_mod r * 'X^r.
Proof.
have [r0|r0] := eqVneq r 0.
  rewrite r0 mulr1.
  rewrite /GRS.syndromep poly_def big_ord0 mulr0.
  apply/eqP; rewrite eq_sym addr_eq0; apply/eqP.
  rewrite /GRS_mod /Omega /erreval -sumrN; apply eq_bigr => j jy.
  rewrite expr0 mulr1 mulrN opprK [in RHS]mulrC mulrC -!scalerA.
  rewrite -scalerAl mulrC mul_polyC; congr (_ *: (_ *: _)).
  by apply eq_bigl => k; rewrite in_setD1 andbC.
rewrite /GRS_mod big_distrl /= /Omega /erreval -big_split /=.
rewrite GRS.syndromepE big_distrr /=.
apply eq_bigr => i iy.
rewrite -3!scalerAl -scalerA -scalerDr.
rewrite polyCM -!mulrA mulrCA !mulrA mul_polyC -!scalerAl; congr (_ *: _).
rewrite /Sigma /errloc.
rewrite (bigD1 i) //=.
rewrite (mulrC (1 - a ``_ i *: 'X)).
rewrite -!mulrA mulrBl mul1r.
set x := (X in _ * X = _).
rewrite (_ : x = (b ``_ i)%:P * (1 - (a ``_ i ^+ r)%:P * 'X^r)); last first.
  rewrite /x mulrCA -mulrBr big_distrr /= -sumrB.
  rewrite (_ : \sum_(i0 < r) _ = 1 - ((a ``_ i ^+ r)%:P * 'X^r)) //.
  rewrite big_split /=.
  destruct r => //.
  rewrite big_ord_recl /= expr0 mulr1 big_ord_recr /= -addrA.
  rewrite (addrA _ _ (- (_ *: _ * _))).
  rewrite addrCA [X in X + _](_ : _ = 0) ?add0r; last first.
    rewrite sumrN.
    apply/eqP; rewrite subr_eq0; apply/eqP.
    apply eq_bigr => j _.
    rewrite -!scalerAl mulrCA -exprS !scalerAl; congr (_ * _).
    by rewrite -mul_polyC -polyCM -exprS.
  by rewrite -mulrCA -scalerAl -exprS 2!mul_polyC scalerA -exprSr.
rewrite [in LHS]mulrA mulrBr mulr1 mulrC -mul_polyC; congr (_ * _ + _).
 apply/eq_bigl => j; by rewrite in_setD1 andbC.
rewrite -mulNr !mulrA; congr (_ * _).
by rewrite -mulNr -mulrA mulrC -!mulrA.
Qed.

End reduced_key_equation.
