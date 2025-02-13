(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg poly polydiv finalg zmodp.
From mathcomp Require Import matrix mxalgebra mxpoly vector fieldext finfield.
Require Import ssralg_ext hamming linearcode decoding cyclic_code poly_decoding.
Require Import dft euclid grs f2.

(**md**************************************************************************)
(* # Binary BCH codes                                                         *)
(*                                                                            *)
(* The main result of this file is the proof that binary BCH codes implement  *)
(* bounded-distance decoding (lemma `BCH_repair_is_correct`).                 *)
(*                                                                            *)
(* Main reference: Robert McEliece, The Theory of Information and Coding,     *)
(* Cambridge University Press, 2002                                           *)
(******************************************************************************)

Reserved Notation "'\BCHsynp_(' a , e , t )" (at level 3).
Reserved Notation "'\BCHomega_(' a , e )" (at level 3).

Declare Scope bch_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope vec_ext_scope.
Local Open Scope dft_scope.

Module BCH.
Section BCH_PCM_def.
Variables (F : finFieldType) (n : nat) (a : 'rV[F]_n) (t : nat).

Definition PCM : 'M_(t, n) := \matrix_(i < t, j < n) (a ``_ j) ^+ i.*2.+1.

Definition PCM_alt : 'M[F]_(t.*2, n) := \matrix_(i < t.*2, j < n) (a ``_ j) ^+ i.+1.

Lemma PCM_alt_GRS : PCM_alt = GRS.PCM a a t.*2.
Proof.
apply/matrixP => i j.
rewrite !mxE (bigD1 j) //= !mxE eqxx mulr1n exprS mulrC.
rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addr0 ?addr0 // => k kj.
by rewrite !mxE (negbTE kj) mulr0n mulr0.
Qed.

End BCH_PCM_def.

Section BCH_PCM_alt.
Variables (n : nat) (m' : nat).
Let m := m'.+1.
Let F := GF2 m.
Variable a : 'rV[F]_n.
Variable t : nat.

Lemma BCH_PCM_altP2 (x : 'rV[F]_n) :
  (forall i : 'I_t.*2, \sum_j x ``_ j * a ``_ j ^+ i.+1 = 0) ->
  (forall i : 'I_t,\sum_j x ``_ j * a ``_ j ^+ i.*2.+1 = 0).
Proof.
move=> H i.
have @j : 'I_t.*2 by refine (@Ordinal _ i.*2 _); rewrite -!muln2 ltn_pmul2r.
rewrite -[RHS](H j); by apply eq_bigr => /= k _.
Qed.

Lemma BCH_PCM_altP1 (x : 'rV['F_2]_n) :
  (forall i : 'I_t, \sum_j GF2_of_F2 x ``_ j * a ``_ j ^+ i.*2.+1 = 0) ->
  (forall i : 'I_t.*2, \sum_j GF2_of_F2 x ``_ j * a ``_ j ^+ i.+1 = 0).
Proof.
move=> H [i].
elim: i {-2}i (leqnn i) => [|i IH j ji i1].
  move=> i; rewrite leqn0 => /eqP -> i0.
  destruct t.
    exfalso; by rewrite -muln2 mul0n ltnn in i0.
  by rewrite -[RHS](H ord0); apply eq_bigr.
case/boolP : (odd j) => [odd_j|even_j]; last first.
  have j2t : j./2 < t by rewrite -divn2 ltn_divLR // muln2.
  rewrite -[in RHS](H (Ordinal j2t)) /=.
  apply/eq_bigr => k _.
  move: (odd_double_half j).
  by rewrite (negbTE even_j) add0n => ->.
move: (IH j.-1./2).
rewrite -{1}divn2 leq_divLR; last first.
  rewrite dvdn2 -subn1 oddB; last by destruct j.
  by rewrite /= addbT odd_j.
have -> : (j.-1 <= i * 2)%N.
  rewrite muln2 -addnn -subn1 leq_subLR addnA add1n (leq_trans ji) //.
  by rewrite addSn ltnS leq_addr.
move/(_ isT).
have j2t : (j.-1)./2 < t.*2.
  rewrite -divn2 ltn_divLR // -ltnS.
  destruct j => //.
  by rewrite /= (ltn_trans i1) // ltnS muln2 -[in X in _ <= X]addnn leq_addl.
move/(_ j2t)/(congr1 (fun x => x ^+ 2)).
rewrite expr0n /= sum_sqr ?char_GFqm // => H'.
rewrite -[RHS]H'; apply eq_bigr => k _.
rewrite exprMn_comm; last by rewrite /GRing.comm mulrC.
congr (_ * _); last first.
  rewrite /= -exprM muln2; congr (_ ^+ _).
  move: (odd_double_half j).
  rewrite odd_j add1n => <-.
  by rewrite (half_bit_double (j./2) false) -doubleS.
by rewrite (expr2 (GF2_of_F2 x ``_ k)) -rmorphM -expr2 f2.expr2_char2.
Qed.

Lemma PCM_altP (x : 'rV_n) :
  (syndrome (BCH.PCM a t) (F2_to_GF2 m x) == 0) =
  (syndrome (BCH.PCM_alt a t) (F2_to_GF2 m x) == 0).
Proof.
apply/idP/idP.
- rewrite /BCH.PCM /BCH.PCM_alt /syndrome => H.
  suff H' : forall j : 'I_t.*2, \sum_j0 (GF2_of_F2 (x ``_ j0) * (a ``_ j0) ^+ j.+1) = 0.
    apply/eqP/rowP => j; rewrite !mxE.
    rewrite -[RHS](H' j).
    apply eq_bigr => /= i _.
    by rewrite !mxE mulrC.
  move=> j.
  apply BCH_PCM_altP1 => i.
  move/eqP/rowP : H => /(_ i).
  rewrite !mxE => H; rewrite -[RHS]H.
  by apply eq_bigr => /= k _; rewrite !mxE /= mulrC.
- rewrite /BCH.PCM_alt /BCH.PCM /syndrome => H.
  apply/eqP/rowP => i.
  have @j : 'I_t.*2.
    by refine (@Ordinal _ i.*2 _); rewrite -!muln2 ltn_pmul2r.
  move/eqP : H => /matrixP/(_ ord0 j).
  rewrite !mxE => {2}<-.
  by apply eq_bigr => k _; rewrite !mxE.
Qed.

End BCH_PCM_alt.

Section BCH_def.
Variables (n : nat) (m : nat).

Definition code (a : 'rV_n) t := Rcode.t (@GF2_of_F2 m) (kernel (PCM a t)).

End BCH_def.

Section BCH_syndromep.
Variable n' : nat.
Let n := n'.+1.
Variable (m : nat).
Let F : fieldType := GF2 m.
Implicit Types a : 'rV[F]_n.

Definition syndromep a y t := syndromep a (F2_to_GF2 m y) t.*2.

End BCH_syndromep.

End BCH.

Notation "'\BCHsynp_(' a , e , t )" := (BCH.syndromep a e t) : bch_scope.

Local Open Scope bch_scope.

Section BCH_is_GRS.
Variable m : nat.
Let F := GF2 m.
Variable (n' : nat).
Let n := n'.+1.
Variable a : F.
Variable (t : nat).

Hypothesis tn : t.*2 < n.

Lemma fdcoor_syndrome_coord (y : 'rV['F_2]_n) i (it : i < t.*2) :
  fdcoor (rVexp a n) (F2_to_GF2 m y) (inord i.+1) =
  GRS.syndrome_coord (rVexp a n) (rVexp a n) i (F2_to_GF2 m y).
Proof.
rewrite /fdcoor /GRS.syndrome_coord horner_poly; apply eq_bigr => j _.
rewrite insubT // => jn.
rewrite !mxE -mulrA; congr (GF2_of_F2 (y _ _) * _); first by apply val_inj.
by rewrite -exprS -exprM mulnC exprM inordK // ltnS (leq_trans it).
Qed.

Lemma BCH_syndromep_is_GRS_syndromep y :
  \BCHsynp_(rVexp a n, y, t) =
  GRS.syndromep (rVexp a n) (rVexp a n) t.*2 (F2_to_GF2 m y).
Proof.
apply/polyP => i.
by rewrite !coef_poly; case: ifPn => // it; rewrite fdcoor_syndrome_coord.
Qed.

End BCH_is_GRS.

Section BCH_PCM_checksum.
Variables (n' : nat) (m : nat).
Let n := n'.+1.
Let F := GF2 m.
Variable a : F.
Variable t : nat.
Variable BCHcode : BCH.code (rVexp a n) t.

Hypothesis tn : t <= n.-1./2.

Lemma BCH_codebook (c : 'rV['F_2]_n) :
  (c \in BCHcode) =
  [forall j : 'I_t, (map_mx (@GF2_of_F2 m) c) ^`_(rVexp a n, inord j.*2.+1) == 0].
Proof.
apply/idP/idP.
- case: BCHcode => code condition /= /condition.
  rewrite mem_kernel_syndrome0 -trmx0 => /eqP/trmx_inj/matrixP Hc.
  apply/forallP => /= i; apply/eqP; rewrite /fdcoor horner_poly.
  move: (Hc i ord0); rewrite !mxE => H1; rewrite -[RHS]H1.
  apply/eq_bigr => /= j _; rewrite insubT // => jn.
  rewrite mulrC 3![in RHS]mxE; congr (_ * (map_mx _ c) ord0 _); last by apply val_inj.
  rewrite inordK //; last first.
    move: (ltn_ord i).
    rewrite -(@ltn_pmul2r 2) // !muln2 -(ltn_add2r 1) !addn1.
    move/leq_trans; apply.
    move: tn.
    rewrite -divn2 leq_divRL // muln2.
    move/leq_ltn_trans; by apply.
  by rewrite exprAC.
- move/forallP => H.
  case: BCHcode => code condition /=; apply (proj2 (condition _)).
  rewrite mem_kernel_syndrome0; apply/eqP/rowP => i; rewrite !mxE.
  rewrite -[RHS](eqP (H i)) /fdcoor horner_poly; apply/eq_bigr => /= j _.
  rewrite insubT // => jn.
  rewrite !mxE mulrC; congr (GF2_of_F2 (c ord0 _) * _); first by apply val_inj.
  rewrite inordK //; first by rewrite exprAC.
  move: (ltn_ord i).
  rewrite -(@ltn_pmul2r 2) // !muln2 -(ltn_add2r 1) !addn1.
  move/leq_trans; apply.
  move: tn.
  by rewrite -divn2 leq_divRL // muln2 => /leq_ltn_trans; exact.
Qed.

End BCH_PCM_checksum.

Section BCH_syndrome_syndromep.
Variables (n' : nat) (m : nat).
Let n := n'.+1.
Let F := GF2 m.
Variable a : F.
Variable t' : nat.
Let t := t'.+1.

Lemma BCH_syndrome_synp y : t.*2 < n ->
  (syndrome (BCH.PCM (rVexp a n) t) (F2_to_GF2 m y) == 0) =
  (\BCHsynp_(rVexp a n, y, t) == 0).
Proof.
move=> tn.
apply/idP/idP.
- move/eqP/eqP.
  rewrite BCH.PCM_altP // /BCH.PCM_alt.
  move/eqP => K.
  rewrite /BCH.syndromep /syndromep.
  rewrite poly_def (eq_bigr (fun=> 0)) ?big_const ?iter_addr0 // => /= i _.
  apply/eqP; rewrite scaler_eq0.
  rewrite fdcoorE -size_poly_eq0 size_polyXn /= orbF.
  move/rowP : K => /(_ (inord i)) K.
  apply/eqP.
  rewrite !mxE in K.
  rewrite -[RHS]K.
  apply eq_bigr => k _.
  rewrite !mxE mulrC; congr (_ * _).
  rewrite -exprM mulnC exprM; congr (a ^+ _ ^+ _).
  by rewrite inord_val // inordK // (leq_ltn_trans (ltn_ord i)).
- move=> K.
  apply/eqP; apply/eqP.
  rewrite BCH.PCM_altP //; apply/eqP.
  rewrite /BCH.PCM_alt.
  apply/rowP => i.
  rewrite !mxE.
  move/eqP: K.
  move/(congr1 (fun x : {poly F} => x`_i)).
  rewrite /BCH.syndromep /syndromep.
  rewrite coef0 poly_def coef_sum (bigD1 i) //= (eq_bigr (fun=> 0)); last first.
    move=> j ji.
    rewrite coefZ coefXn (_ : _ == _ = false) ?mulr0 //.
    by apply/negbTE; rewrite eq_sym.
  rewrite big_const iter_addr0 addr0 fdcoorE coefZ coefXn eqxx mulr1 => K.
  rewrite -[RHS]K.
  apply eq_bigr => k _.
  rewrite !mxE mulrC; congr (_ * _).
  by rewrite -exprM mulnC exprM inordK // (leq_ltn_trans _ tn).
Qed.

End BCH_syndrome_syndromep.

Section BCH_minimum_distance_lb.
Variables (m : nat) (n : nat).
Let F := GF2 m.
Variable a : 'rV[F]_n.

Lemma BCH_det_mlinear t r' (f : 'I_r'.+1 -> 'I_n) (rt : r' < t.*2) :
  let B := \matrix_(i, j) BCH.PCM_alt a t (widen_ord rt i) (f j) in
  let V := Vandermonde r'.+1 (row 0 B) in
  \det B = \prod_(i < r'.+1) BCH.PCM_alt a t (widen_ord rt 0) (f i) * \det V.
Proof.
move=> B V.
set h := Vandermonde r'.+1 (row 0 B).
set g := fun i => BCH.PCM_alt a t (widen_ord (rt) 0) (f i).
transitivity (\det (\matrix_(i, j) (h i j * g j))).
  congr (\det _).
  apply/matrixP => i j.
  by rewrite !mxE /h /g /BCH.PCM_alt !mxE -!exprD /= -exprM mul1n addn1.
rewrite det_mlinear; congr (_ * _).
by congr (\det _); apply/matrixP => i j; rewrite !mxE /h -exprM.
Qed.

Hypothesis a_neq0 : distinct_non_zero a.

Lemma det_B_neq0 t r f (Hr' : r.+1 < t.*2) (Hinj : injective f) :
  let B := \matrix_(i < r.+1, j < r.+1)
             BCH.PCM_alt a t (widen_ord (ltnW Hr') i) (f j) in
  \det B != 0.
Proof.
rewrite /=; set B := \matrix_(_, _) _.
rewrite BCH_det_mlinear det_Vandermonde mulf_neq0 //.
- rewrite prodf_seq_neq0 /=; apply/allP => /= j _.
  by rewrite !mxE /= expr1 (proj2 a_neq0).
- rewrite prodf_seq_neq0 /=; apply/allP => /= j _.
  rewrite prodf_seq_neq0 /=; apply/allP => /= k _.
  apply/implyP => jk; rewrite !mxE /= !expr1 subr_eq0.
  apply/negP => /eqP; move: (proj1 a_neq0) => /(_ (f k) (f j)).
  by rewrite 2!ffunE => akj /akj/Hinj; exact/eqP/negbT/gtn_eqF.
Qed.

(** parity-check matrix of a binary (n, k) code capable ot correcting
   all error patterns of weight <= t with dimension k >= n - m * t
   (see [McEliece 2002], thm 9.1) *)
Lemma BCH_min_dist1 t x (x0 : x != 0) (t0 : 0 < t) (C : BCH.code a t) :
  x \in C -> t < wH x.
Proof.
move/(proj1 (Rcode.P C _)).
rewrite mem_kernel_syndrome0 BCH.PCM_altP // => /eqP H.
(* there are r <= t columns in the PCM s.t. their linear comb. w.r.t. is 0 *)
rewrite leqNgt; apply/negP => abs.
have /eqP : #| wH_supp x | = (wH x).-1.+1.
   by rewrite card_wH_supp prednK // lt0n wH_eq0.
rewrite cardE => supp_wH.
have Hinj : injective [ffun i : 'I_(wH x).-1.+1 => tnth (Tuple supp_wH) i].
  move=> /= i j.
  rewrite !ffunE /tnth /= => /eqP.
  rewrite (set_nth_default (tnth_default (Tuple supp_wH) j)) //; last first.
    rewrite -cardE card_wH_supp; move: i; by rewrite prednK // lt0n wH_eq0.
  rewrite nth_uniq ?enum_uniq //.
  by move/eqP/val_inj.
  rewrite -cardE card_wH_supp; move: i; by rewrite prednK // lt0n wH_eq0.
  rewrite -cardE card_wH_supp; move: j; by rewrite prednK // lt0n wH_eq0.
set f := finfun (tnth (Tuple supp_wH)).
move=> [:tmp].
have @f' : 'I_n -> 'I_(wH x).-1.+1.
  move=> i.
  set tmp' := fun i => if x ``_ i != 0 then index i (enum (wH_supp x)) else O.
  refine (@Ordinal _ (tmp' i) _).
  move: i.
  abstract: tmp.
  move=> i.
  case: ifP => // H'.
  by rewrite -(eqP supp_wH) index_mem mem_enum -mem_wH_supp.
have f'K : forall j, x ``_ j != 0 -> f (f' j) = j.
  move=> i xj.
  by rewrite ffunE /tnth /= xj nth_index // mem_enum -mem_wH_supp.
have Hf : \sum_(i < (wH x).-1.+1)
    (GF2_of_F2 x``_(f i)) *: col (f i) (BCH.PCM_alt a t) = 0 :> 'cV__.
  move/(congr1 trmx) : H; rewrite trmx0 => H.
  rewrite -[RHS]H.
  apply/colP => i.
  rewrite ![in RHS]mxE ![in LHS]summxE [in RHS](bigID (fun j => x ``_ j == 0)).
  rewrite /= [X in _ = X + _](_ : _ = 0) ?add0r; last first.
    rewrite (eq_bigr (fun x=> 0)); last first.
      by move=> j /eqP xj0; rewrite !mxE xj0 rmorph0 mulr0.
    by rewrite big_const iter_addr0.
  have ? : (wH x).-1.+1 <= n by rewrite -ltnS prednK ?lt0n ?wH_eq0 // ltnS max_wH.
  rewrite [in RHS](reindex_onto (fun x => f x) f' f'K) /= [in RHS]big_mkcond /=.
  apply/eq_bigr => j _.
  case: ifPn => [_|]; first by rewrite!mxE mulrC.
  rewrite negb_and negbK.
  case/orP => [/eqP ->|abs']; first by rewrite rmorph0 scale0r mxE.
  have [->|abs''] := eqVneq (x ``_ (f j)) 0.
    by rewrite rmorph0 scale0r mxE.
  exfalso.
  move/eqP: abs'; apply.
  rewrite /f'; apply/val_inj => /=.
  rewrite abs'' /f ffunE /tnth /= index_uniq //.
    by rewrite -cardE card_wH_supp -[in X in _ < X](@prednK (wH x)) // lt0n wH_eq0.
  by rewrite enum_uniq.
set r' := (wH x).-1.
have Hr' : r'.+1 < t.*2.
  by rewrite /r' prednK // ?lt0n ?wH_eq0 // (leq_trans abs) // -addnn -{1}(add0n t) ltn_add2r.
have {}Hf : \sum_(i < r'.+1) GF2_of_F2 x ``_ (f i) *:
    \col_(j < r'.+1) (BCH.PCM_alt a t (widen_ord (ltnW Hr') j) (f i)) = 0.
  apply/colP => j.
  rewrite mxE summxE.
  move/colP : Hf => /(_ (widen_ord (ltnW Hr') j)).
  rewrite !mxE summxE => Hf.
  rewrite -[RHS]Hf.
  by apply eq_bigr => /= i _; rewrite !mxE.
have /negP := det_B_neq0 Hr' Hinj.
rewrite -det_tr; apply.
apply/det0P; exists (\row_i GF2_of_F2 x ``_ (f i)).
  suff -> : \row_i GF2_of_F2 x ``_ (f i) = const_mx 1.
    apply/eqP => /rowP/(_ 0).
    rewrite !mxE; apply/eqP; exact: oner_neq0.
  move=> n0; apply/rowP => k.
  rewrite !mxE /f ffunE /tnth /=.
  have -> : forall i, i \in (enum (wH_supp x)) -> x ``_ i = 1.
    by move=> /= i; rewrite mem_enum inE -f2.F2_eq1 => /eqP.
  by rewrite rmorph1.
  apply/(nthP (tnth_default (Tuple supp_wH) k)); exists k => //.
  rewrite -cardE card_wH_supp.
  move: (ltn_ord k); by rewrite {2}prednK // lt0n wH_eq0.
apply/rowP => i; rewrite !mxE.
move/colP : Hf => /(_ i).
rewrite !mxE => Hf; rewrite -[RHS]Hf.
by rewrite summxE; apply eq_bigr=> k _; rewrite !mxE.
Qed.

End BCH_minimum_distance_lb.

Section BCH_erreval.
Variables (F : fieldType) (n : nat) (a : 'rV[F]_n).

Definition BCH_erreval := erreval (const_mx 1) a.

End BCH_erreval.

Notation "'\BCHomega_(' a , e )" := (BCH_erreval a e) : bch_scope.

Section BCH_key_equation_old.
Variables (F : fieldType) (n' : nat).
Let n := n'.+1.
Variable a : F.

(** see [McEliece 2002], thm 9.4 *)
Lemma BCH_key_equation_old (y : 'rV[F]_n) : a ^+ n = 1 ->
  \sigma_(rVexp a n, y) * rVpoly (dft (rVexp a n) n y) =
  \BCHomega_(rVexp a n, y) * (1 - 'X^n).
Proof.
move=> an1.
rewrite dftE big_distrr /=.
under eq_bigr.
  move=> i ie.
  rewrite -scalerAr.
  rewrite (_ : \sigma_(rVexp a n, y) =
    \sigma_(rVexp a n, y, i) * (1 - ((rVexp a n) ``_ i) *: 'X)); last first.
    rewrite /errloc (bigD1 i) //= mulrC; congr (_ * _).
    by apply eq_bigl => ij; rewrite in_setD1 andbC.
  over.
transitivity (\sum_(i in supp y) y ``_ i *:
     (\sigma_(rVexp a n, y, i) * (1 - a ^+ (i * n) *: 'X^n))).
  apply eq_bigr => /= i ie; congr (_ *: _).
  rewrite -mulrA; congr (_ * _).
  rewrite mulrDl mul1r mulNr big_distrr /=.
  rewrite [X in _ - X](eq_bigr (fun j : 'I_n => a ^+ (i * j.+1) *: 'X^j.+1)); last first.
    move=> j _.
    rewrite !mxE -scalerAr -scalerAl scalerA -exprM -exprD.
    by rewrite inord_val addnC -mulSn mulnC -exprS.
  rewrite big_ord_recl !mxE inord_val expr0 expr1n scale1r expr0.
  rewrite big_ord_recr /= opprD addrA.
  rewrite (_ : forall a b c d, b = c -> a + b - c - d = a - d) //.
  move=> a0 b c d -> //; by rewrite addrK.
  apply eq_bigr => j _; by rewrite mxE -exprM mulnC inordK // ltnS.
rewrite /BCH_erreval [in RHS]big_distrl /=.
apply eq_bigr => i ie.
rewrite mxE -scalerAl mulr1; congr (_ *: (_ * _)).
by rewrite mulnC exprM an1 expr1n scale1r.
Qed.

End BCH_key_equation_old.

Section decoding_using_euclid.
Variables (n' : nat) (m : nat).
Let n := n'.+1.
Let F := GF2 m.
Variable a : F.
Variable t' : nat.
Let t := t'.+1.
Let H := BCH.PCM (rVexp a n) t.

Hypothesis a_neq0 : a != 0.

Definition BCH_mod (y : 'rV[F]_n) : {poly F} :=
  \sum_(i in supp y) y ``_ i *:
    (\prod_(j in supp y :\ i)
      (1 - a ^+ j *: 'X) * - (a ^+ (t.*2.+1 * i))%:P).

Lemma BCH_mod_is_GRS_mod y : BCH_mod y = GRS_mod y (rVexp a n) (rVexp a n) t.*2.
Proof.
rewrite /BCH_mod /GRS_mod; apply/eq_bigr => i iy.
rewrite !mulrN scalerN; congr (- _).
rewrite -!scalerAl; congr (_ *: _).
rewrite mxE -mulrA; congr (_ * _).
  apply/eq_big.
    by move=> j; rewrite in_setD1 andbC.
  move=> j _; by rewrite mxE.
by rewrite -polyCM -exprSr -exprM mulnC.
Qed.

Hypothesis (tn : t.*2 < n).

Lemma BCH_key_equation y :
  \sigma_(rVexp a n, F2_to_GF2 m y) * \BCHsynp_(rVexp a n, y, t) =
    \BCHomega_(rVexp a n, twisted a (F2_to_GF2 m y)) +
    BCH_mod (F2_to_GF2 m y) * 'X^t.*2.
Proof.
move: (@GRS_key_equation F n (F2_to_GF2 m y) (rVexp a n) (rVexp a n) t.*2) => H0.
rewrite BCH_syndromep_is_GRS_syndromep // H0; congr (_ + _ * _).
  rewrite /Omega /BCH_erreval; apply/polyP => i.
  rewrite !coef_sum supp_twisted //.
  apply eq_bigr => /= j jy.
  by rewrite !mxE mulr1.
by rewrite -BCH_mod_is_GRS_mod.
Qed.

Lemma errloc_twisted (y : 'rV[F]_n) :
  errloc (rVexp a n) (supp y) = errloc (rVexp a n) (supp (twisted a y)).
Proof. by rewrite /errloc supp_twisted. Qed.

Lemma size_erreval_twisted (e : 'rV_n) : #|supp (F2_to_GF2 m e)| <= t ->
  size (\omega_(const_mx 1, rVexp a n, twisted a (F2_to_GF2 m e))) <= t.
Proof.
move=> et.
have et' : #|supp (twisted a (F2_to_GF2 m e))| <= t by rewrite supp_twisted.
by apply: (size_erreval (rVexp a n) (Errvec et') (const_mx 1)).
Qed.

Local Notation "'v'" := (Euclid.v).

Definition BCH_err y : {poly 'F_2} :=
  let r0 : {poly F} := 'X^t.*2 in
  let r1 := \BCHsynp_(rVexp a n, y, t) in
  let vstop := v r0 r1 (stop t r0 r1) in
  let s := vstop.[0]^-1 *: vstop in
  \poly_(i < n) (if s.[a^- i] == 0 then 1 else 0).

Definition BCH_repair : repairT 'F_2 'F_2 n :=
  [ffun y => if \BCHsynp_(rVexp a n, y, t) == 0 then
    Some y
  else
    let ret := y + poly_rV (BCH_err y) in
    if \BCHsynp_(rVexp a n, ret, t) == 0 then Some ret else None].

Lemma BCH_err_is_correct (a_not_uroot : not_uroot_on a n) l (e y : 'rV_n) :
  let r0 := 'X^t.*2 : {poly F} in
  let r1 := \BCHsynp_(rVexp a n, y, t) in
  let vj := Euclid.v r0 r1 (stop t r0 r1) in
  l <> 0 ->
  vj = l *: \sigma_(rVexp a n, F2_to_GF2 m e) ->
  e = poly_rV (BCH_err y).
Proof.
have H1 := distinct_non_zero_rVexp a_neq0 a_not_uroot.
move=> r0 r1 vj /eqP l0 Hvj; apply/rowP => i.
set r_ := \BCHomega_(rVexp a n, twisted a (F2_to_GF2 m e)).
rewrite !mxE coef_poly ltn_ord; case: ifPn.
  rewrite -/r0 -/r1 -/r_ -/vj Hvj.
  rewrite !hornerZ !mulf_eq0 invrM; last 2 first.
    by rewrite unitfE.
    by rewrite unitfE horner_errloc_0 oner_neq0.
  rewrite mulf_eq0 !invr_eq0 (negbTE l0) /= orbF horner_errloc_0 oner_eq0 /=.
  move: (errloc_zero (supp (F2_to_GF2 m e)) i H1); rewrite mxE => ->.
  by rewrite supp_F2_to_GF2 inE -F2_eq1 => /eqP.
rewrite -/r0 -/vj in Hvj *.
rewrite Hvj !hornerZ !mulf_eq0 invrM; last 2 first.
  by rewrite unitfE.
  by rewrite unitfE horner_errloc_0 oner_neq0.
rewrite mulf_eq0 !invr_eq0 (negbTE l0) /= orbF horner_errloc_0 oner_eq0 /=.
move: (errloc_zero (supp (F2_to_GF2 m e)) i H1); rewrite mxE => ->.
by rewrite supp_F2_to_GF2 inE negbK => /eqP ->.
Qed.

Local Open Scope ecc_scope.

Lemma BCH_repair_is_correct (C : BCH.code (rVexp a n) t) : not_uroot_on a n ->
  t.-BDD (C, BCH_repair).
Proof.
move=> a_not_uroot c e.
set y := c + e.
set r0 : {poly F} := 'X^t.*2.
set r1 := \BCHsynp_(rVexp a n, y, t).
set vj := Euclid.v r0 r1 (stop t r0 r1).
move=> Hc et.
set r : {poly F} := \BCHomega_(rVexp a n, twisted a (F2_to_GF2 m e)).
have H1 := distinct_non_zero_rVexp a_neq0 a_not_uroot.
rewrite /BCH_repair.
have syn_c : \BCHsynp_(rVexp a n, c, t) = 0.
  move/(proj1 (Rcode.P C _)) : Hc.
  by rewrite mem_kernel_syndrome0 BCH_syndrome_synp // => /eqP ->.
have syn_y_e : \BCHsynp_(rVexp a n, y, t) = \BCHsynp_(rVexp a n, e, t).
  rewrite {1}/BCH.syndromep /F2_to_GF2 map_mxD syndromepD.
  by rewrite -!/(BCH.syndromep _ _ _) syn_c add0r.
rewrite ffunE.
case: ifPn => syn_y.
  suff e0 : e = 0 by rewrite /y e0 addr0.
  apply/eqP/negPn/negP => e0.
  move: et.
  apply/negP.
  rewrite -ltnNge (@BCH_min_dist1 _ _ _ H1 _ _ e0 _ C) //.
  rewrite (_ : e = y - c); last by rewrite /y addrAC subrr add0r.
  apply Lcode0.aclosed => //; last by rewrite Lcode0.oclosed.
  apply: (proj2 (Rcode.P C _)).
  by rewrite mem_kernel_syndrome0 BCH_syndrome_synp.
have size_r1 : size r1 <= size ('X^t.*2 : {poly F}).
  by rewrite /r1 /BCH.syndromep size_polyXn (leq_trans (size_syndromep _ _ _)).
have eqn : \sigma_(rVexp a n, F2_to_GF2 m e) * r1 = r + - - BCH_mod (F2_to_GF2 m e) * 'X^t.*2.
  by rewrite opprK -(BCH_key_equation e) /r1 syn_y_e.
have size_sigma : size \sigma_(rVexp a n, F2_to_GF2 m e) <= t.+1.
  by rewrite (leq_trans (size_errloc _ _)) // ltnS supp_F2_to_GF2 -wH_card_supp.
have size_r : size r <= t.
  move: et.
  rewrite /r wH_card_supp -(@supp_F2_to_GF2 _ m _) -(supp_twisted a_neq0) => et'.
  by rewrite (leq_trans (size_erreval (rVexp a n) (Errvec et') _)).
have deg : (t.+1 + t)%N = size ('X^t.*2 : {poly F}).
  by rewrite size_polyXn addSn addnn.
have cop : coprimep \sigma_(rVexp a n, F2_to_GF2 m e) r.
  have tmp : (forall i, ((const_mx 1) : 'rV[F]_n) ``_ i != 0 :> F).
    by move=> ?; rewrite mxE ?oner_neq0.
  rewrite /r errloc_twisted; by apply: (coprime_errloc_erreval H1 tmp).
case: (solve_key_equation_coprimep size_r1 (errloc_neq0 _ _) syn_y eqn size_sigma size_r deg cop) => [l [l0 [Hvj _]]].
by rewrite -(@BCH_err_is_correct _ l e) // -addrA F2_addmx addr0 syn_c eqxx.
Qed.

End decoding_using_euclid.

Section BCH_cyclic.
Variables (n' m : nat).
Let n := n'.+1.
Let F := GF2 m.
Variable a : F.
Variable t : nat.
Hypothesis tn : t <= n.-1./2.

Local Open Scope cyclic_code_scope.

Lemma rcsP_BCH_cyclic (C : BCH.code (rVexp a n) t) : a ^+ n = 1 ->
  rcsP [set cw in C].
Proof.
move=> a1 x.
rewrite inE (BCH_codebook C tn) => /forallP /= Hx.
rewrite inE (BCH_codebook C tn); apply/forallP => /= i.
rewrite map_mx_rcs rcs_rcs_poly /rcs_poly.
set x' := map_mx _ _.
have [M HM] : exists M, `[ 'X * rVpoly x' ]_ n = 'X * rVpoly x' + M * ('X^n - 1).
  exists (- ('X * rVpoly x') %/ ('X^n - 1)).
  move/eqP: (divp_eq ('X * rVpoly x') ('X^n - 1)); rewrite addrC -subr_eq => /eqP <-.
  by rewrite divpN mulNr.
rewrite HM /fdcoor poly_rV_K //; last first.
  rewrite -HM.
  move: (ltn_modp ('X * rVpoly x') ('X^n - 1)).
  rewrite size_XnsubC // ltnS => ->.
  by rewrite monic_neq0 // monicXnsubC.
rewrite !(hornerE,hornerXn).
move: (Hx i); rewrite /fdcoor => /eqP ->; rewrite mulr0 add0r.
by rewrite mxE exprAC a1 expr1n subrr mulr0.
Qed.

End BCH_cyclic.
