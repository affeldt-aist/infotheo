From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg perm zmodp matrix.
Require Import ssralg_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Local Open Scope vec_ext_scope.

(** * Vandermonde Matrices *)

(** OUTLINE:
- Section vandermonde_matrix.
- Section vandermonde_k_matrix.
- Section vandermonde_determinant.

*)

Section vandermonde_matrix.

Variables (n : nat) (R : ringType) (a : 'rV[R]_n).

Definition vander_gen (r : nat) := \matrix_(i < r, j < n) (a``_j) ^+ i.

Definition vander := vander_gen n.

End vandermonde_matrix.

Section vandermonde_k_matrix.

Variable (R : comRingType).

Definition lc n (a : R) (r0 r1 : 'rV[R]_n) := r0 - a *: r1.

Definition mat_lc n cst (M : 'M[R]_n.+1) (k : 'I_n.+1) :=
  if k == 0 then M else
    \matrix_(i < n.+1) if i == k then
                         lc cst (row i M) (row (inord i.-1) M)
                       else
                         row i M.

(* k = 0 -> modifies nothing  *)
(* k = 1 -> modifies row n  *)
(* k = 2 -> modifies row n-1, n *)
(* k = 3 -> modifies row n-2, n-1, n *)
(* k = n.+1 -> modifies row 0, 1, ..., n *)
(* do not use with k > n.+1 *)
Definition vander_k n (a : 'rV[R]_n.+1) (M : 'M_n.+1) (k : nat) :=
  foldl (fun acc x => mat_lc (a``_ord0) acc (inord x)) M (rev (iota (n.+1 - k) k)).

Lemma vander_k_rec n (a : 'rV[R]_n.+1) k : k <= n.+1 ->
  forall i, i <= n ->
  forall M,
  row (inord i) (vander_k a M k) =
  if i == O then
    row 0 M
  else if n.+1 - k <= i <= n then
    lc (a``_ord0) (row (inord i) M) (row (inord i.-1) M)
  else
    row (inord i) M.
Proof.
elim: k => [n0 i ni|k IH].
  move=> M.
  case: ifPn => [/eqP ->|n0'].
    rewrite /vander_k /= (_ : inord 0 = 0) //.
    apply/val_inj => /=; by rewrite inordK.
  by rewrite subn0 ni andbT ltnNge ni.
rewrite ltnS => kn i ni M.
case: ifPn => [|i0].
  move/eqP => ?; subst i.
  rewrite /vander_k -{2}(add1n k) iota_add rev_cat foldl_cat addn1.
  rewrite -subSn // subSS -/(vander_k a _ k) subSS /= /mat_lc.
  case: ifP => [|nk0].
    move/eqP => /(congr1 (fun x => nat_of_ord x)) /=.
    rewrite inordK; last by rewrite ltnS leq_subr.
    move/eqP.
    rewrite subn_eq0 => nk.
    have ? : n = k by apply/eqP; rewrite eqn_leq kn nk.
   by rewrite IH // ltnW.
  rewrite rowK eq_sym (_ : inord 0 = 0) //; last first.
    apply/val_inj => /=; by rewrite inordK.
  rewrite nk0 -(_ : inord 0 = 0) //; last first.
    apply/val_inj => /=.
    by rewrite inordK.
  rewrite IH //; last by rewrite ltnW.
  rewrite eqxx (_ : inord 0 = 0) //.
  apply/val_inj => /=.
  by rewrite inordK.
rewrite {1}/vander_k -{2}(add1n k) iota_add rev_cat foldl_cat.
rewrite addn1 -subSn // subSS -/(vander_k a _ k) subSS /= /mat_lc.
case: ifP => [|nk0].
  move/eqP/(congr1 (fun x => nat_of_ord x)) => /=.
  rewrite inordK //; last  by rewrite ltnS leq_subr.
  move/eqP.
  rewrite subn_eq0 => nk.
  have ? : n = k by apply/eqP; rewrite eqn_leq kn nk.
  subst k.
  by rewrite subnn leq0n /= ni IH // (negbTE i0) subSn // subnn lt0n i0 ni.
rewrite rowK.
case: ifPn => [|nik].
  move/eqP => /(congr1 (fun x => nat_of_ord x)) /=.
  rewrite inordK; last by rewrite ltnS.
  rewrite inordK; last by rewrite ltnS leq_subr.
  move/eqP => ink.
  rewrite -(eqP ink) leqnn /= ni IH //; last by rewrite ltnW.
  rewrite (negbTE i0) {1}(eqP ink).
  case: ifPn.
    case/andP.
    by rewrite leq_subLR subnKC // ltnn.
  rewrite ni andbT -ltnNge => ok.
  rewrite {1}IH; last first.
    by apply: (leq_trans (@leq_pred _) ni).
    by rewrite ltnW.
  case: ifPn => [Hi1|Hi1].
    rewrite (eqP Hi1) (_ : inord 0 = 0) //.
    apply/val_inj => /=.
    by rewrite inordK.
  case: ifP => //.
  case/andP.
  rewrite {1}(eqP ink) -subnS subSn // subnS => abs.
  exfalso.
  move: abs.
  rewrite ltnNge => /negP.
  apply.
  by rewrite leq_pred.
rewrite ni andbT.
case: ifPn => nki.
  rewrite /lc IH //; last by rewrite ltnW.
  rewrite (negbTE i0) ni andbT.
  case: ifPn => [nki' //|].
  rewrite -ltnNge subSn // ltnS => abs.
  have abs' : (i = n - k)%N by apply/eqP; rewrite eqn_leq nki abs.
  exfalso.
  move/eqP : nik; apply.
  apply/val_inj => /=.
  by rewrite inordK // inordK // ltnS leq_subr.
rewrite IH //; last by rewrite ltnW.
rewrite (negbTE i0) ni andbT.
case: ifP => // abs.
exfalso.
rewrite -ltnNge in nki.
rewrite subSn // in abs.
move: (ltn_trans nki abs).
by rewrite ltnn.
Qed.

Definition vander_last n (a : 'rV[R]_n.+1) :=
  \matrix_(i < n.+1, j < n.+1)
   if i == 0 then 1
   else if j == 0 then 0
        else (a``_j) ^+ i - a``_0 * (a``_j) ^+ i.-1.

Lemma vander_lastE n (a : 'rV[R]_n.+1) : vander_last a = vander_k a (vander a) n.
Proof.
apply/row_matrixP => i.
rewrite {2}(_ : i = inord i); last first.
  apply/val_inj => /=.
  by rewrite inordK.
rewrite vander_k_rec //; last by rewrite -ltnS.
case: ifPn => i0.
  rewrite /vander_last.
  apply/rowP => j.
  rewrite !mxE.
  case: ifP => //.
  move/eqP => abs; exfalso.
  apply abs.
  apply/val_inj => /=.
  by move/eqP : i0.
rewrite subSn // subnn lt0n i0 /= -ltnS ltn_ord /= /lc /vander_last; apply/rowP => j.
rewrite !mxE.
case: ifP => [|i0'].
  move/eqP/(congr1 (fun x => nat_of_ord x)) => /= abs; exfalso.
  move/eqP : i0; by apply.
case: ifP => [|j0].
  move=> /eqP ->.
  rewrite -exprS inordK // inordK; last first.
    by rewrite (leq_trans _ (ltn_ord i)) // ltnS leq_pred.
  rewrite prednK; last first.
    by rewrite lt0n.
  by rewrite (_ : 0 = ord0) // subrr.
rewrite inordK // inordK // (ltn_trans _ (ltn_ord i)) // -subn1.
by rewrite -{2}(subn0 i) ltn_sub2l // lt0n.
Qed.

Lemma vander_k_max n (a : 'rV[R]_n.+1) (M : 'M[R]_n.+1) : vander_k a M n.+1 = vander_k a M n.
Proof.
apply/row_matrixP => i.
rewrite (_ : i = inord i); last first.
  apply/val_inj => /=.
  by rewrite inordK.
rewrite vander_k_rec //; last by rewrite -ltnS.
case: ifPn => i0.
  by rewrite (eqP i0) vander_k_rec // leq_pred.
rewrite subnn leq0n -ltnS ltn_ord /=.
rewrite vander_k_rec ?leq_pred //; last by rewrite -ltnS ltn_ord.
rewrite (negbTE i0) -(ltnS i) ltn_ord andbT.
by rewrite /= subSn // subnn lt0n i0.
Qed.

Lemma det_vander_k_rec n (a : 'rV[R]_n.+1) (k : nat) (M : 'M[R]_n.+1) : k < n.+1 ->
  \det (vander_k a M k) = \det (vander_k a M k.-1).
Proof.
move=> kn.
destruct k as [|k] => //=.
rewrite /lc /= (@determinant_multilinear _ _ _
  (\matrix_i (if i == inord (n.+1 - k.+1) then row (inord i) (vander_k a M k) else row (inord i) (vander_k a M k.+1)))
  (\matrix_i (if i == inord (n.+1 - k.+1) then row (inord i.-1) (vander_k a M k) else row (inord i) (vander_k a M k.+1)))
  (inord (n.+1 - k.+1)) 1 (- a``_ord0)); last 3 first.
  rewrite scale1r !rowK eqxx vander_k_rec //; last first.
    by rewrite subSS leq_subr.
    by rewrite ltnW.
  rewrite subSS.
  rewrite leq_subr andbT subn_eq0.
  case: ifPn => [nk|].
    move: (leq_ltn_trans nk kn).
    by rewrite ltnn.
  rewrite -ltnNge => kn'.
  rewrite leqnn /lc inordK; last by rewrite ltnS leq_subr.
  rewrite vander_k_rec //; last 2 first.
    rewrite ltnW //; by apply: (ltn_trans kn').
    by rewrite leq_subr.
  rewrite subn_eq0 leqNgt kn' /= leq_subr andbT leq_subLR addnBA; last first.
    by rewrite ltnW.
  rewrite addnC.
  rewrite -addnBA // subnn addn0 ltnn vander_k_rec //; last 2 first.
    by rewrite ltnW // ltnS ltnW.
    by rewrite -subnS leq_subr.
  rewrite -subnS subn_eq0.
  rewrite ltnS in kn, kn'.
  case: ifPn.
    rewrite -subn_eq0 => /eqP ->.
    rewrite (_ : inord 0 = 0) // ?scaleNr //.
    apply/val_inj => //=.
    by rewrite inordK.
  rewrite -ltnNge => k1n.
  case: ifPn => //.
    case/andP.
    rewrite subnS subSn; last by rewrite ltnW.
    by rewrite ltnNge leq_pred.
  by rewrite scaleNr.
  apply/matrixP => i j; by rewrite !mxE eq_sym (negbTE (neq_lift _ _)) mxE inord_val.
  apply/matrixP => i j; by rewrite !mxE eq_sym (negbTE (neq_lift _ _)) mxE inord_val.
rewrite mul1r (_ : \matrix_i _ = vander_k a M k); last first.
  apply/matrixP => i j; rewrite !mxE.
  case: ifPn => [/eqP Hi|Hi].
    rewrite !mxE (_ : inord i = i) //.
    apply/val_inj => /=.
    by rewrite inordK.
  rewrite vander_k_rec //; last first.
    by rewrite -ltnS.
  by rewrite ltnW.
  case: ifPn => i0.
    transitivity ((row (inord i) (vander_k a M k)) 0 j); last first.
      rewrite mxE (_ : inord i = i) //.
      apply/val_inj => /=.
      by rewrite inordK.
    rewrite vander_k_rec //; last 2 first.
      by rewrite (leq_trans _ kn) // -addn2 leq_addr.
      by rewrite -ltnS.
    by rewrite i0.
  rewrite -(ltnS i) ltn_ord andbT.
  case: ifPn => nki.
    rewrite /lc.
    transitivity ((row (inord i) (vander_k a M k)) 0 j); last first.
      rewrite mxE (_ : inord i = i) //.
      apply/val_inj => /=.
      by rewrite inordK.
    rewrite vander_k_rec //; last 2 first.
      by rewrite ltnW // ltnW.
      by rewrite -ltnS.
    rewrite (negbTE i0) -(ltnS i) ltn_ord andbT.
    have {nki} : n.+1 - k.+1 < i.
      rewrite ltn_neqAle nki andbT.
      apply: contra Hi => /eqP ->.
      apply/eqP/val_inj => /=.
      by rewrite inordK //.
    rewrite subnS -ltnS prednK; last by rewrite lt0n subn_eq0 -ltnNge ltnW.
    by rewrite ltnS => ->.
  transitivity ((row (inord i) (vander_k a M k)) 0 j); last first.
    rewrite mxE (_ : inord i = i) //.
    apply/val_inj => /=.
    by rewrite inordK.
  rewrite vander_k_rec //; last 2 first.
    by rewrite ltnW // ltnW.
    by rewrite -ltnS.
  rewrite (negbTE i0) -(ltnS i) ltn_ord andbT.
  have /negbTE -> // : ~~ (n.+1 - k <= i).
  apply: contra nki.
  apply: leq_trans.
  rewrite leq_subLR addnC.
  destruct n as [|n] => //.
  rewrite subSn; last by rewrite -ltnS ltnW.
  by rewrite addSn addnS subnK // -ltnS ltnW.
rewrite (_ : \det (\matrix_i _) = 0) ?mulr0 ?addr0 //.
have H : inord (n.+1 - k.+1) != inord (n.+1 - k.+2) :> 'I_n.+1.
  apply/eqP => /(congr1 (fun x => nat_of_ord x)) /=.
  rewrite 2!subSS.
  rewrite inordK // ?ltnS ?leq_subr //.
  rewrite inordK // ?ltnS ?leq_subr //.
  destruct n as [|n] => //.
  rewrite !subSS.
  move/(congr1 (fun x => x + k)%N).
  rewrite subnK; last by rewrite ltnW.
  rewrite addnC addnBA // addnC.
  rewrite addnK -{2}(addn0 n).
  rewrite -addn1 => /eqP.
  by rewrite eqn_add2l.
apply (@determinant_alternate _ _ _ (inord (n.+1 - k.+1)) (inord (n.+1 - k.+2))) => //.
move=> i.
rewrite !mxE eqxx eq_sym (negbTE H) 2!subSS.
rewrite inordK; last by rewrite ltnS leq_subr.
rewrite inordK; last by rewrite ltnS leq_subr.
rewrite -subnS [in LHS]vander_k_rec // ?leq_subr //; last by rewrite ltnW // ltnW.
rewrite subn_eq0.
case: ifPn => // nk2.
  rewrite (_ : n - k.+1 = 0)%N //; last by apply/eqP; rewrite subn_eq0.
  by rewrite  vander_k_rec // ltnW // ltnW.
rewrite andbT (_ : _ <= _ = false); last first.
  rewrite -(leq_add2r k.+1) subnK //.
  rewrite addnC addnBA; last by rewrite ltnW // ltnW.
  rewrite addnC -addnBA; last by rewrite -addn1 leq_addr.
  rewrite subSn // subnn // addn1.
  apply/negbTE.
  by rewrite -leqNgt.
rewrite [in RHS]vander_k_rec // ?leq_subr //; last by rewrite ltnW.
rewrite subn_eq0 (negbTE nk2) andbT (_ : _ <= _ = false) //.
rewrite -(leq_add2r k.+1) subnK //; last by rewrite ltnW.
by rewrite subnK ?ltnn.
Qed.

Lemma det_vander_k n (a : 'rV[R]_n.+1) (k : nat) (M : 'M[R]_n.+1) :
  k <= n.+1 -> \det (vander_k a M k) = \det (vander_k a M k.-1).
Proof.
rewrite leq_eqVlt => /orP[/eqP ->|];
  by [rewrite vander_k_max | apply det_vander_k_rec].
Qed.

Lemma det_vander_k_vander n (a : 'rV[R]_n.+1) (k : nat) : k <= n.+1 ->
  \det (vander_k a (vander a) k) = \det (vander a).
Proof.
elim: k => // k IH.
rewrite ltnS => kn.
by rewrite det_vander_k // IH // ltnW.
Qed.

End vandermonde_k_matrix.

Section vandermonde_determinant.

Variable (R : comRingType).

Lemma det_mlinear_rec n (f : 'I_n.+1 -> 'I_n.+1 -> R) (g : 'I_n.+1 -> R) k : k <= n.+1 ->
  \det (\matrix_(j, i) (f i j * g j)) =
  (\prod_(l < k) g (inord l)) * \det (\matrix_(j, i) (f i j * if j >= k then g j else 1)).
Proof.
elim: k => [_|k IH]; first by rewrite big_ord0 mul1r.
rewrite ltnS => kn.
rewrite IH; last by rewrite ltnW.
rewrite big_ord_recr /= -mulrA; congr (_ * _).
rewrite (@determinant_multilinear _ _ _ (\matrix_(j, i) (f i j * (if k < j then g j else 1))) (\matrix_(j, i) (f i j * (if k <= j then g j else 1))) (inord k) (g (inord k)) 0); last 3 first.
  rewrite scale0r addr0.
  apply/rowP => j.
  rewrite !mxE mulrCA; congr (_ * _).
  by rewrite inordK // leqnn ltnn mulr1.
  apply/matrixP => i j; rewrite !mxE.
  case: ifPn => [H1|].
    case: ifP => // /negbT; by rewrite leq_eqVlt H1 orbT.
  case: ifPn => //; rewrite -ltnNge ltnS => H1 H2.
  rewrite mulr1.
  have /eqP abs : k = lift (inord k) i by apply/eqP; rewrite eqn_leq H1 H2.
  exfalso.
  move/eqP : abs; apply/eqP.
  apply: contra (@neq_lift _ (inord k) i) => /eqP {1}->.
  apply/eqP/val_inj; by rewrite inord_val.
  apply/matrixP => i j; by rewrite !mxE.
rewrite mul0r addr0 -det_tr.
rewrite (_ : _^T = \matrix_(i, j) (f i j * (if k < j then g j else 1))) //.
by apply/matrixP => i j; rewrite !mxE.
Qed.

Lemma det_mlinear n (f : 'I_n -> 'I_n -> R) (g : 'I_n -> R) :
  \det (\matrix_(i, j) (f i j * g j)) = \prod_(i < n) g i * \det (\matrix_(i, j) (f i j)).
Proof.
destruct n as [|n]; first by rewrite big_ord0 mul1r !det_mx00.
rewrite -det_tr (_ : _^T = (\matrix_(j, i) (f i j * g j))); last first.
  by apply/matrixP => i j; rewrite !mxE.
rewrite (@det_mlinear_rec _ _ _ n.+1) //; congr (_ * _).
  apply eq_bigr => i _; by rewrite inord_val.
rewrite -det_tr; congr (\det _).
apply/matrixP => i j; by rewrite !mxE ltnNge -ltnS ltn_ord /= mulr1.
Qed.

Lemma det_vander_rec n (a : 'rV[R]_n.+1) : \det (vander a) =
  \det (vander (\row_(i < n) a``_(inord i.+1))) * \prod_(1 <= j < n.+1) (a``_(inord j) - a``_0).
Proof.
transitivity (\det (vander_last a)); first by rewrite vander_lastE /= det_vander_k_vander.
rewrite /vander_last (expand_det_col _ ord0) /= (bigD1 ord0) //=.
rewrite [X in _ + X = _](_ : _ = 0) ?addr0; last first.
  rewrite (eq_bigr (fun=> 0)); first  by rewrite big_const iter_addr0.
  move=> i i0; by rewrite !mxE (negbTE i0) /= mul0r.
rewrite mxE /= mul1r /cofactor expr0 mul1r.
transitivity (\det (\matrix_(i < n, j < n) ((\row_(i < n) a``_(inord i.+1))``_j ^+ i.+1 - a``_0 * (\row_(i < n) a``_(inord i.+1))``_j ^+ i))).
  congr (\det _).
  apply/matrixP => i j; rewrite !mxE.
  do 2 rewrite eq_sym (negbTE (neq_lift _ _)).
  rewrite !lift0 /=; congr (a ``_ _ ^+ _ - _ * a ``_ _ ^+ _);
    by apply/val_inj; rewrite -lift0 inord_val.
transitivity (\det (\matrix_(i < n, j < n) ((\row_(i < n) a``_(inord i.+1))``_j ^+ i * ((\row_(i < n) a``_(inord i.+1))``_j - a``_0)))).
  congr (\det _).
  apply/matrixP => i j; by rewrite !mxE exprS -mulrBl mulrC.
transitivity ((\prod_(j < n) (a``_(inord j.+1) - a``_0)) * \det (\matrix_(i < n, j < n) ((\row_(i < n) a``_(inord i.+1))``_j ^+ i))).
  rewrite det_mlinear; congr (_ * _).
  by apply/eq_bigr => j _; rewrite mxE.
rewrite mulrC; congr (_ * _).
rewrite (big_addn 0 n.+1 1) subn1 /= big_mkord; apply/eq_bigr => i _; by rewrite addn1.
Qed.

Lemma det_vander n (a : 'rV[R]_n.+1) : \det (vander a) =
  \prod_(i < n.+1) (\prod_(j < n.+1 | i < j) (a``_(inord j) - a``_(inord i))).
Proof.
elim: n a => [a|n IH a].
  rewrite (mx11_scalar (vander a)) det_scalar1 mxE expr0 big_ord_recr /=.
  rewrite big_ord0 mul1r (eq_bigl (xpred0)) ?big_pred0 // => i; by rewrite ord1.
rewrite det_vander_rec IH.
rewrite (eq_bigr (fun i : 'I_n.+1 => \prod_(1 <= j < n.+2 | i < j.-1) (a``_(inord j) - a``_(inord i.+1)))); last first.
  move=> i _; rewrite (big_addn O n.+2 1) subn1 /= big_mkord.
  apply/eq_big; first by move=> j; rewrite addn1.
  move=> j ij; by rewrite 2!mxE inordK // inordK // addn1.
rewrite [in RHS]big_ord_recl [in RHS]mulrC; congr (_ * _); last first.
  rewrite [in RHS]big_mkcond /= [in RHS]big_ord_recl ltnn mul1r big_add1 big_mkord.
  apply/eq_bigr => i _.
  rewrite lift0 (_ : inord 0 = 0) //.
  by apply/val_inj => /=; rewrite inordK.
apply eq_bigr => i _.
rewrite [in RHS]big_mkcond /= [in RHS]big_ord_recl ltn0 mul1r big_add1 big_mkord.
rewrite [in LHS]big_mkcond /=; by apply eq_bigr => j _.
Qed.

End vandermonde_determinant.
