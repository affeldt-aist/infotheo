(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect fingroup perm ssralg zmodp.
From mathcomp Require Import matrix mxalgebra poly polydiv mxpoly.
Require Import ssralg_ext.

(**md**************************************************************************)
(* # Additional lemmas about polynomials                                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.

Section AboutPoly.

Variable R : idomainType.

Lemma size_quot_eq0 : forall q d r : {poly R},
  d \is monic -> size r < size d -> (size (q * d + r) < size d) = (q == 0).
Proof.
move=> q d r mon sz; apply/eqP/eqP => [sz0 | ->]; apply/eqP.
- apply/negPn; apply/negP=> ab_absurdo; move: sz0.
  rewrite size_addl; last first.
    rewrite mulrC size_monicM //.
    have Htmp : 0 < size q by rewrite lt0n size_poly_eq0.
    rewrite -subn1 -addnBA //.
    apply leq_trans with (size d) => //.
    by rewrite leq_addr.
  rewrite mulrC size_monicM // prednK; last first.
    rewrite addn_gt0.
    apply/orP; left.
    by apply leq_ltn_trans with (size r).
  move/eqP.
  rewrite addnC -addnBA // subnn addn0 size_poly_eq0; by apply/negP.
- by rewrite mul0r add0r subn_eq0.
Qed.

Lemma poly_def_lead_coef : forall p : {poly R},
  p = \sum_(i < (size p).-1) p`_i *: 'X^i + lead_coef p *: 'X^(size p).-1.
Proof.
move=> p; case sz_p : (size _) => [|n].
- move/eqP: sz_p; rewrite size_poly_eq0; move/eqP => ->.
  by rewrite big_ord0 /lead_coef coef0 scale0r addr0.
- by rewrite -{1}(coefK p) /lead_coef sz_p [_.-1]/= poly_def big_ord_recr /=.
Qed.

Lemma size_lead_coefK : forall n (p : {poly R}), size p <= n.+1 ->
  size (p - lead_coef p *: 'X^(size p).-1) <= n.
Proof.
elim=> [|n IHn] p sz_p.
- rewrite (size1_polyC sz_p) lead_coefC size_polyC.
  set t := (_ != _); have -> : t.-1 = O by case: t.
  by rewrite expr0 alg_polyC subrr size_poly0.
- rewrite {1}(poly_def_lead_coef p) -addrA subrr addr0; eapply leq_trans.
  + by rewrite -poly_def; apply size_poly.
  + by move: sz_p; case: (size _).
Qed.

Lemma size_sub (p q : {poly R}) : p <> 0 -> size p = size q ->
  lead_coef p = lead_coef q -> size (p - q) < size p.
Proof.
move=> p0 pq lc_pq.
move: (size_add p (-q)); rewrite pq size_opp (maxn_idPr _) //.
rewrite leq_eqVlt; case/orP => // abs.
rewrite (@leq_ltn_trans (size q).-1) //; last first.
  by rewrite -pq prednK // lt0n size_poly_eq0; apply/eqP.
rewrite (poly_def_lead_coef p) {1}(poly_def_lead_coef q) lc_pq pq.
rewrite opprD addrCA addrK addrC.
rewrite (_ : _ - _ = \poly_(i < (size q).-1) (p`_i - q`_i)) ?size_poly //.
rewrite -sumrB poly_def; apply eq_bigr => i _; by rewrite scalerBl.
Qed.

Lemma rVpoly0 n (p : 'rV[R]_n) : (rVpoly p == 0) = (p == 0).
Proof.
apply/idP/idP => [p0|/eqP ->]; last by rewrite linear0.
by apply/eqP/rowP => i; rewrite mxE -coef_rVpoly_ord (eqP p0) coef0.
Qed.

Lemma poly_rV_0_inv n (p : {poly R}) : size p <= n ->
  poly_rV p == (0 : 'rV[R]_n) -> p == 0.
Proof.
move=> pn /eqP p0; apply/eqP/polyP => i.
case/boolP : (i < size p) => ip.
- transitivity (poly_rV p 0 (widen_ord pn (Ordinal ip))); first by rewrite !mxE.
  by rewrite p0 mxE coef0.
- by rewrite -(@poly_rV_K _ n p) // p0 linear0.
Qed.

Lemma poly_rV_0 n (p : {poly R}) : p == 0 -> poly_rV p == (0 : 'rV[R]_n).
Proof. by move=> /eqP ->; apply/eqP/rowP => i; rewrite !mxE coef0. Qed.

End AboutPoly.

Lemma morph_modp (F : fieldType) (p : {poly F}) :
  {morph (fun x : {poly F} => x %% p) : x y / x + y}.
Proof. move=> x y; by rewrite modpD. Qed.
