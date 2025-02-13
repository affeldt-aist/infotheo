(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg poly polydiv fingroup perm.
From mathcomp Require Import finalg zmodp matrix mxalgebra mxpoly vector.
Require Import ssr_ext ssralg_ext poly_ext f2 hamming decoding channel_code.

(**md**************************************************************************)
(* # Definition of Linear Error-correcting Codes (ECCs)                       *)
(*                                                                            *)
(* Main lemmas:                                                               *)
(* - dimension of the kernel (`dim_kernel`)                                   *)
(* - Any code that contains more than the zero polynomial has a nonzero       *)
(*   polynomial of lowest degree (`exists_non0_codeword_lowest_deg`)          *)
(* - minimum distance decoding is bounded distance decoding (`MD_BDD`)        *)
(* - singleton bound (`singleton_bound`)                                      *)
(* - Hamming bound (`hamming_bound`)                                          *)
(*                                                                            *)
(* ```                                                                        *)
(*         Lcode0.t == type of linear ECCs as a vector space of row-vectors   *)
(*          kernel  == definition of a linear ECC as the kernel of a          *)
(*                     parity-check matrices (PCMs)                           *)
(*         min_dist == the minimum distance is the minimum Hamming weight of  *)
(*                     non-zero codewords or the smallest number of columns   *)
(*                     of a PCM that are linearly independent                 *)
(*      mdd_err_cor == the number of errors that can be corrected by minimum  *)
(*                     distance decoding                                      *)
(*          perfect == perfect codes                                          *)
(*        Encoder.t == type of an encoder                                     *)
(*        Decoder.t == type of a decoder                                      *)
(* ```                                                                        *)
(*                                                                            *)
(* Linear Codes in Systematic Form:                                           *)
(* ```                                                                        *)
(*     Syslcode.CSM == check symbols matrix                                   *)
(*     Syslcode.PCM == PCM of a linear ECC in systematic form, defined using  *)
(*                     the check symbols matrix                               *)
(*     Syslcode.GEN == generating matrix                                      *)
(*  Syslcode.encode == encoding function                                      *)
(* Syslcode.discard == function to discard check symbols                      *)
(*          Rcode.t == definition of "restricted code" (see BCH.v)            *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Module Lcode0.

Definition t (F : finFieldType) n := {vspace 'rV[F]_n}.

Section lcode0_prop.
Variables (n : nat) (F : finFieldType) (C : t F n).

Lemma aclosed : addr_closed C.
Proof. split => [|? ? ? ?]; by [rewrite mem0v | rewrite rpredD]. Qed.

Lemma sclosed : GRing.scaler_closed C.
Proof. move=> ? ? ?; by rewrite rpredZ. Qed.

Lemma oclosed : oppr_closed C.
Proof. move=> ? ?; by rewrite -scaleN1r rpredZ. Qed.

Definition not_empty : 0 < #| [set cw in C] | := vspace_not_empty C.

Lemma mem_poly_rV k (f : 'I_k -> {poly F}) : (forall i, poly_rV (f i) \in C) ->
  poly_rV (\big[+%R/0]_(i < k) (f i)) \in C.
Proof.
elim: k f => [f ? /= | ? IH f ?].
- by rewrite big_ord0 linear0 mem0v.
- by rewrite big_ord_recl linearD /= (proj2 aclosed) // IH.
Qed.

End lcode0_prop.

End Lcode0.

Section syndrome_and_kernel.

Variables (F : finFieldType) (n m : nat) (H : 'M[F]_(m, n)).

Definition syndrome (y : 'rV_n) : 'rV_m := (H *m y^T)^T.

Lemma syndromeD y y' : syndrome (y + y') = syndrome y + syndrome y'.
Proof. by rewrite /syndrome linearD /= mulmxDr linearD /=. Qed.

Lemma syndromeZ k y : syndrome (k *: y) = k *: syndrome y.
Proof. by rewrite /syndrome 3!linearZ /=. Qed.

Lemma syndromeN y : syndrome (- y) = - syndrome y.
Proof. by rewrite /syndrome 3!linearN. Qed.

Lemma syndrome0 : syndrome 0 = 0.
Proof. by rewrite /syndrome trmx0 mulmx0 trmx0. Qed.

Lemma additive_syndrome : additive syndrome.
Proof. move=> x y; by rewrite syndromeD syndromeN. Qed.

HB.instance Definition _ :=
  GRing.isAdditive.Build _ _ _ additive_syndrome.
HB.instance Definition _ :=
  GRing.isScalable.Build _ _ _ _ _ syndromeZ.

(*Definition lin_syndrome : {linear 'rV[F]_n -> 'rV[F]_m} :=
  GRing.Linear.Pack _ (GRing.Linear.Class additive_syndrome syndromeZ).*)

Definition hom_syndrome : 'Hom('rV[F]_n, 'rV[F]_m) :=
  linfun syndrome.

Definition kernel : Lcode0.t F n := lker hom_syndrome.

Lemma dim_hom_syndrome_ub : \dim (limg hom_syndrome) <= m.
Proof.
rewrite [in X in _ <= X](_ : m = \dim (fullv : {vspace 'rV[F]_m})); last first.
  by rewrite dimvf/= /dim/= mul1n.
by rewrite dimvS // subvf.
Qed.

Lemma mem_kernel_syndrome0 y : (y \in kernel) = (syndrome y == 0).
Proof. by rewrite memv_ker lfunE. Qed.

Lemma dim_kernel (Hm : \rank H = m) (mn : m <= n) : \dim kernel = (n - m)%N.
Proof.
move: (limg_ker_dim hom_syndrome fullv).
rewrite (_ : (fullv :&: _)%VS = kernel); last by apply/capv_idPr/subvf.
rewrite (_ : \dim fullv = n); last by rewrite dimvf /dim /= mul1n.
move=> H0; rewrite -{}[in RHS]H0.
suff -> : \dim (limg hom_syndrome) = m by rewrite addnK.
set K := castmx (erefl, Hm) (col_base H).
have rankK : \rank K = m.
  rewrite /K mxrank_castmx.
  by move: (col_base_full H) => /eqP ->.
set b := [tuple row i K^T | i < m].
apply size_basis with b.
rewrite basisEfree; apply/and3P; split.
- apply/freeP => k Hk m0.
  apply/eqP/negPn/negP => abs.
  have H1 : \row_i k i *m K^T = const_mx 0 *m K^T.
    rewrite mul0mx; apply/rowP => m1.
    rewrite !mxE (eq_bigr (fun j => k j * b`_j 0 m1)); last first.
      move=> m2 _; by rewrite !mxE /b nth_mktuple !mxE.
    move/rowP : Hk => /(_ m1).
    rewrite !mxE summxE => X; rewrite -[RHS]X.
    apply eq_bigr => m2 _; by rewrite !mxE.
  move: rankK; rewrite -/K -mxrank_tr.
  move/(@full_rank_inj _ _ _ _ (leqnn _)).
  move/(_ _ _ H1)/rowP/(_ m0).
  rewrite !mxE; by apply/eqP.
- apply/span_subvP => /= x.
  case/mapP => /= m0 _ ->{x}.
  apply/memv_imgP.
  move: (mulmx_ebase H) => HH.
  set s := pid_mx _ in HH.
  exists (row m0 K^T *m invmx (col_ebase H)^T *m s *m (invmx (row_ebase H)^T)).
    by rewrite memvf.
  rewrite /hom_syndrome lfunE /= /syndrome.
  rewrite trmx_mul trmxK -{3}HH trmx_mul.
  transitivity (row m0 K^T *m invmx (col_ebase H)^T *m s *m (col_ebase H *m s)^T); last first.
    rewrite -!mulmxA; congr (_ *m (_ *m (_ *m _))).
    by rewrite mulmxA mulVmx ?mul1mx // unitmx_tr row_ebase_unit.
  rewrite trmx_mul.
  transitivity (row m0 K^T *m invmx (col_ebase H)^T *m pid_mx m *m (col_ebase H)^T); last first.
    rewrite -!mulmxA; congr (_ *m (_ *m _)); rewrite mulmxA.
    by rewrite tr_pid_mx pid_mx_id ?Hm.
  by rewrite pid_mx_1 mulmx1 -mulmxA mulVmx ? mulmx1 // unitmx_tr col_ebase_unit.
- by rewrite size_tuple dim_hom_syndrome_ub.
Qed.

End syndrome_and_kernel.

(* wip *)
Section dual_code.

Variables (F : finFieldType) (m n : nat) (H : 'M[F]_(m, n)).

Definition dual_code : {vspace 'rV[F]_n} :=
  (linfun (mulmxr H) @: fullv)%VS.

Lemma dim_dual_code : (\dim (kernel H) + \dim dual_code = n)%N.
Proof.
move: (limg_ker_dim (linfun (syndrome H)) fullv).
rewrite -/(kernel H).
rewrite (_ : (fullv :&: _)%VS = kernel H); last by apply/capv_idPr/subvf.
rewrite (_ : \dim fullv = n); last by rewrite dimvf /dim /= mul1n.
rewrite (_ : \dim (limg _) = \dim dual_code) // /dual_code.
rewrite /dimv.
Abort.

Lemma dual_codeP1 y : y \in dual_code ->
  (forall x, x \in kernel H -> y *m x^T = 0).
Proof.
case/memv_imgP => y' _.
rewrite !lfunE => ->{y} x.
rewrite memv_ker => /eqP.
rewrite lfunE /= /syndrome => /(congr1 trmx).
rewrite trmx0 trmxK -mulmxA => ->; by rewrite mulmx0.
Qed.

Lemma dual_codeP2 y : (forall x, x \in kernel H -> y *m x^T = 0) ->
  y \in dual_code.
Proof.
move=> /= H0.
suff [l Hl] : exists l : 'rV_m, y = \sum_(j < m) (l ord0 j) *: (row j H).
  apply/memv_imgP; exists l.
  by rewrite memvf.
  by rewrite lfunE /= Hl mulmx_sum_row.
Abort.

End dual_code.

Section not_trivial_code_properties.

Variables (F : finFieldType) (n : nat) (C : Lcode0.t F n).

Hypothesis C_not_trivial : not_trivial C.

Lemma not_trivial_dim : 0 < \dim C.
Proof. rewrite lt0n dimv_eq0; by apply not_trivialP. Qed.

Definition codeword_lowest_deg c :=
  [forall y, [&& y \in C, y != c & y != 0] ==>
             (size (rVpoly c) <= size (rVpoly y))].

Definition non0_codeword_lowest_deg c :=
  [&& c \in C, c != 0 & codeword_lowest_deg c].

Lemma exists_non0_codeword_lowest_deg : { c : 'rV_n | non0_codeword_lowest_deg c }.
Proof.
apply: sigW.
case: C_not_trivial => g /andP[gC g0].
have := erefl [arg min_(g' < g | (g' \in C) && (g' != 0)) (size (rVpoly g'))].
case: arg_minnP => /=; [by apply/andP | move=> g'].
case/andP=> g'C g'0 g_min _.
exists g'.
rewrite /non0_codeword_lowest_deg g'C g'0 /= /codeword_lowest_deg.
apply/forallP => y; apply/implyP => /and3P[yC yg' y0].
apply g_min; by rewrite yC.
Qed.

Definition lowest_size := size (rVpoly (val exists_non0_codeword_lowest_deg)).

Lemma size_lowestP x : x \in C -> x != 0 -> lowest_size <= size (rVpoly x).
Proof.
move=> xC x0.
rewrite /lowest_size.
case: exists_non0_codeword_lowest_deg => g /= /and3P[H1 H2 /forallP].
move/(_ x); rewrite xC x0 /= andbT.
have [->//|xg] := eqVneq x g.
by rewrite implyTb.
Qed.

Lemma size_lowest g : non0_codeword_lowest_deg g ->
  size (rVpoly g) = lowest_size.
Proof.
case/and3P => gC g0 Hg.
rewrite /lowest_size.
case: exists_non0_codeword_lowest_deg => g' /= /and3P[g'C g'0 Hg'].
have [->//|gg'] := eqVneq g g'.
apply/eqP; rewrite eqn_leq.
move: Hg => /forallP/(_ g').
rewrite g'C /= g'0 andbT eq_sym gg' implyTb => ->.
move: Hg' => /forallP/(_ g).
by rewrite gC /= g0 andbT gg' implyTb => ->.
Qed.

End not_trivial_code_properties.

Section minimum_distance.

Variables (F : finFieldType) (n : nat) (C : Lcode0.t F n).

Hypothesis C_not_trivial : not_trivial C.

Definition non_0_cw := xchoose C_not_trivial.

Lemma non_0_cw_mem : non_0_cw \in C.
Proof. by rewrite /non_0_cw; case/andP: (xchooseP C_not_trivial). Qed.

Lemma wH_non_0_cw : wH non_0_cw != O.
Proof.
by rewrite /non_0_cw; case/andP: (xchooseP C_not_trivial); rewrite wH_eq0.
Qed.

Definition min_wH_cw :=
  arg_min non_0_cw [pred cw | (cw \in C) && (wH cw != O)] (@wH F n).

Definition min_dist := wH min_wH_cw.

Lemma min_dist_is_min c : c \in C -> c != 0 -> min_dist <= wH c.
Proof.
move=> cC c0; rewrite /min_dist /min_wH_cw.
case: arg_minnP => /= [|c1 /andP [] Hc1 wHc1].
  by rewrite non_0_cw_mem wH_non_0_cw.
by apply; rewrite cC /= wH_eq0.
Qed.

Lemma min_dist_achieved : exists c, c \in C /\ c <> 0 /\ wH c = min_dist.
Proof.
exists min_wH_cw; split.
  rewrite /min_wH_cw /=.
  case: arg_minnP => /=.
    by rewrite non_0_cw_mem wH_non_0_cw.
  by move=> /= c /andP[].
split; last reflexivity.
rewrite /min_wH_cw /=.
case: arg_minnP => /=.
  by rewrite non_0_cw_mem wH_non_0_cw.
by move=> /= c /andP[_ /negP]; rewrite wH_eq0 => /negP/eqP.
Qed.

Lemma min_dist_neq0 : min_dist <> O.
Proof.
move=> abs.
case: min_dist_achieved => /= v [vC [/eqP/eqP v0]].
by rewrite abs; move/eqP; rewrite wH_eq0 => /eqP.
Qed.

Lemma min_distP d :
  (forall x : 'rV[F]_n, x \in C -> x != 0 -> d <= wH x) /\
  (exists x : 'rV[F]_n, x \in C /\ x != 0 /\ wH x <= d) ->
  min_dist = d.
Proof.
case=> H1 [y [yC [y0 yd]]].
rewrite /min_dist /min_wH_cw.
case: arg_minnP => /=.
  by rewrite non_0_cw_mem wH_non_0_cw.
move=> x /andP[xC x0] H.
apply/eqP.
rewrite eqn_leq; apply/andP; split; last first.
  apply H1 => //; by rewrite -wH_eq0.
by rewrite (leq_trans _ yd) // H // yC wH_eq0.
Qed.

Lemma min_dist_prop m m' :
  m \in C -> m' \in C -> m != m' -> min_dist <= dH m m'.
Proof.
move=> /= mm' mC m'C; apply min_dist_is_min.
by apply Lcode0.aclosed => //; rewrite Lcode0.oclosed.
by rewrite subr_eq0.
Qed.

Definition mdd_err_cor := min_dist.-1./2.

Lemma mdd_oddE : odd min_dist -> mdd_err_cor = min_dist./2.
Proof.
move=> odd_d.
rewrite /mdd_err_cor (_ : _.-1./2 = min_dist./2) //.
by rewrite -{1}(odd_double_half min_dist) odd_d /= (half_bit_double _ false).
Qed.

Lemma mdd_evenE : ~~ odd min_dist -> mdd_err_cor = (min_dist./2 - 1)%N.
Proof.
move=> even_d.
rewrite /mdd_err_cor (_ : min_dist.-1./2 = min_dist./2 - 1)%N //.
move Hd : min_dist => d.
case: d Hd even_d => //= d -> /=.
by rewrite negbK uphalf_half => ->; rewrite add1n subn1.
Qed.

Definition sbound_f' k (H : k.-1 <= n) :=
  fun c : 'rV[F]_n => \row_(i < k.-1) c ord0 (widen_ord H i).

Lemma sbound_f'Z k (H : k.-1 <= n) a y :
  sbound_f' H (a *: y) = a *: sbound_f' H y.
Proof. by apply/rowP => i; rewrite !mxE. Qed.

Lemma sbound_f'D k (H : k.-1 <= n) y y' :
  sbound_f' H (y + y') = sbound_f' H y + sbound_f' H y'.
Proof. by apply/rowP => i; rewrite !mxE. Qed.

Lemma sbound_f'N k (H : k.-1 <= n) y : sbound_f' H (- y) = - sbound_f' H y.
Proof. by apply/rowP => i; rewrite !mxE. Qed.

Lemma additive_sbound_f' k (H : k.-1 <= n) : additive (sbound_f' H).
Proof. by move=> x y; rewrite sbound_f'D sbound_f'N. Qed.

HB.instance Definition _ k (H : k.-1 <= n) :=
  GRing.isAdditive.Build _ _ _ (additive_sbound_f' H).
HB.instance Definition _ k (H : k.-1 <= n) :=
  GRing.isScalable.Build _ _ _ _ _ (sbound_f'Z H).

(*Definition sbound_f_linear k (H : k.-1 <= n) :
  {linear 'rV[F]_n -> 'rV[F]_k.-1} :=
  GRing.Linear.Pack _ (GRing.Linear.Class (additive_sbound_f' H) (sbound_f'Z H)).*)

(* McEliece, theorem 9.8, p.255 *)
Lemma singleton_bound : min_dist <= n - \dim C + 1.
Proof.
set k := \dim C.
have dimCn : k.-1 < n.
  have /dimvS := subvf C.
  rewrite dimvf /dim /= mul1n.
  by apply: leq_trans; rewrite prednK // not_trivial_dim.
set f := linfun (sbound_f' (ltnW dimCn)).
have H1 : \dim (f @: C) <= k.-1.
  suff : \dim (f @: C) <= \dim (fullv : {vspace 'rV[F]_k.-1}).
    by rewrite dimvf /= /dim /= mul1n.
  by apply/dimvS/subvf.
have H2 : (\dim (f @: C) + \dim (C :&: lker f) = \dim (fullv : {vspace 'rV[F]_k}))%N.
  by rewrite dimvf /= /dim /= mul1n -[RHS](limg_ker_dim f C) addnC.
have H3 : 1 <= \dim (C :&: lker f).
  rewrite lt0n; apply/eqP => abs; move: H2.
  rewrite abs addn0 dimvf /dim /= mul1n -/k.
  apply/eqP.
  move: H1; rewrite leqNgt; apply: contra => /eqP ->.
  by rewrite prednK // not_trivial_dim.
have [cw [Hcw1 [Hcw2 Hcw3]]] : exists cw, cw \in C /\ cw != 0 /\ f cw = 0.
  have : \dim (C :&: lker f) != O by rewrite lt0n in H3.
  rewrite dimv_eq0.
  rewrite -vpick0 => Htmp.
  exists (vpick (C :&: lker f)).
  split.
    move: (memv_pick (C :&: lker f)).
    by rewrite memv_cap => /andP[].
  split => //.
  apply/eqP; rewrite -memv_ker.
  move: (memv_pick (C :&: lker f)).
  by rewrite memv_cap => /andP[].
have Kcw : wH cw <= n - k + 1.
  rewrite wH_sum (bigID (fun x : 'I_n => x < k.-1)) /=.
  rewrite (eq_bigr (fun=> O)) ?big_const ?iter_addn ?mul0n ?add0n; last first.
    move=> i Hi /=.
    apply/eqP.
    rewrite eqb0 negbK.
    move: Hcw3.
    rewrite lfunE /= /sbound_f'.
    move/rowP => /= /(_ (Ordinal Hi)).
    rewrite !mxE /=.
    set x := widen_ord _ _.
    suff -> : x = i by move/eqP.
    exact: val_inj.
  have X : forall i : 'I_n, ~~ (i < k.-1) -> (cw ord0 i != 0) <= 1.
    move=> i Hi.
    by case: (_ != _).
  apply: (leq_trans (@leq_sum _ _ _ _ (fun=> 1%N) X)).
  set lhs := (X in X <= _).
  rewrite (_ : lhs = (\sum_(k.-1 <= i < n) 1%N))%N; last first.
    rewrite /lhs.
    rewrite -(big_mkord (fun i => ~~ (i < k.-1)) (fun=> 1%N)).
    rewrite {1}/index_iota subn0.
    rewrite {1}(_ : n = k.-1 + (n - k.-1))%N; last by rewrite subnKC // ltnW.
    rewrite iotaD big_cat /=.
    rewrite sum1_count.
    rewrite (@eq_in_count _ _ xpred0); last first.
      move=> i.
      by rewrite mem_iota add0n leq0n /= => ->.
    rewrite count_pred0 add0n add0n.
    rewrite sum1_count.
    rewrite (@eq_in_count _ _ xpredT); last first.
      move=> i.
      rewrite mem_iota -ltnNge => /andP[K1 K2].
      by rewrite ltnS.
    rewrite sum1_count.
    by rewrite /index_iota.
  rewrite sum_nat_const_nat muln1 -subn1 subnBA ?not_trivial_dim //.
  rewrite addn1 subSn; last first.
    clear f H1 H2 H3 Hcw3.
    move: dimCn.
    by rewrite prednK // not_trivial_dim.
  by rewrite addn1.
exact/(leq_trans _ Kcw)/min_dist_is_min.
Qed.

Definition maximum_distance_separable := (min_dist == n - \dim C + 1)%N.

End minimum_distance.

Section not_trivial_binary_codes.

Variable (n : nat) (C : Lcode0.t 'F_2 n).

Hypothesis C_not_trivial : not_trivial C.

Lemma non0_codeword_lowest_deg_uniq (g : 'rV['F_2]_n) :
  g \in C -> g != 0 -> codeword_lowest_deg C g ->
  forall j, j \in C -> j != 0 -> size (rVpoly g) = size (rVpoly j) -> g = j.
Proof.
move=> gC g0 Cg /= j jC j0 gj.
(* i show that if j is another polynomial with minimal degree but different from g
   then g - j can only be 0, contradiction *)
set k : 'rV_n := g - j.
apply/eqP; apply/negPn; apply/negP => abs.
have gk : size (rVpoly g) <= size (rVpoly k).
  move: Cg.
  rewrite /codeword_lowest_deg => /forallP/(_ k)/implyP; apply.
  apply/and3P; split.
  - by rewrite /k (proj2 (Lcode0.aclosed C)) // Lcode0.oclosed.
  - apply: contra j0.
    by rewrite /k subr_eq addrC -subr_eq subrr eq_sym.
  - rewrite /k; move: abs; apply contra; by rewrite subr_eq0.
suff kg : size (rVpoly k) < size (rVpoly g).
  by move: (leq_ltn_trans gk kg); rewrite ltnn.
rewrite /k linearB /=; have [size_1g|size_1g] := ltnP 1 (size (rVpoly g)).
- apply: size_sub => //=; last by apply lead_coef_F2.
  by apply/eqP; apply: contra g0; rewrite rVpoly0.
- (* this means that g is constant *)
  have sz_g1 : size (rVpoly g) = 1%N.
    have : size (rVpoly g) != O by rewrite size_poly_eq0 rVpoly0.
    by case: (size _) size_1g => //; case.
  rewrite (@size1_polyC_F2 _ sz_g1).
  rewrite gj in sz_g1.
  by rewrite (@size1_polyC_F2 _ sz_g1) size_polyC subrr size_poly0.
Qed.

End not_trivial_binary_codes.

Section min_dist_decoding_prop.

Variables (F : finFieldType) (n : nat) (C : Lcode0.t F n).
Variable (f : repairT F F n).
Hypothesis MD_dec_f : MD_decoding [set cw in C] f.

Lemma min_dist_double v w d m : f v = Some m ->
  w \in C -> dH w v <= d -> dH w m <= d.*2.
Proof.
move=> vm wC H.
rewrite (leq_trans (dH_tri_ine v _ _)) // -addnn leq_add //.
have {}wC : w \in [set cw in C] by rewrite inE.
by rewrite dH_sym (leq_trans (MD_dec_f vm wC)).
Qed.

Hypothesis C_not_trivial : not_trivial C.
Hypothesis f_img : oimg f \subset C.

Lemma mddP x y : f y != None -> x \in C ->
  dH x y <= mdd_err_cor C_not_trivial -> f y = Some x.
Proof.
move=> dec_not_None mC enc_m_v.
have [m0 Hm0] : exists m0, f y = Some m0.
  case: (f y) dec_not_None => [m0|] // _; by exists m0.
case/boolP : (odd (min_dist C_not_trivial)) => [odd_d | even_d].
- rewrite (mdd_oddE odd_d) in enc_m_v.
  apply/eqP/negPn/negP => abs.
  have {}abs : m0 != x by apply: contra abs; rewrite Hm0 => /eqP ->.
  have : min_dist C_not_trivial <= (min_dist C_not_trivial)./2.*2.
    move: abs.
    rewrite eq_sym => /(min_dist_prop C_not_trivial)/leq_trans; apply => //.
      move/subsetP : f_img; apply.
      by rewrite inE; apply/existsP; exists y; apply/eqP.
    by rewrite (@min_dist_double y).
  by rewrite -{1}(odd_double_half (min_dist C_not_trivial)) odd_d ltnNge leqnn.
- rewrite (mdd_evenE even_d) in enc_m_v.
  apply/eqP/negPn/negP => abs.
  have {}abs : m0 != x by apply: contra abs; rewrite Hm0 => /eqP ->.
  have : (min_dist C_not_trivial)./2 <= (min_dist C_not_trivial)./2 - 1.
    move: (odd_double_half (min_dist C_not_trivial)).
    rewrite -leq_double (negbTE even_d) /= add0n => ->.
    move: abs.
    rewrite eq_sym.
    move/(min_dist_prop C_not_trivial)/leq_trans; apply => //.
      move/subsetP: f_img; apply.
      by rewrite inE; apply/existsP; exists y; apply/eqP.
    by rewrite (@min_dist_double y).
  apply/negP.
  rewrite -ltnNge subn1 prednK // half_gt0 ltnNge; apply: contra even_d.
  rewrite leq_eqVlt => /orP[/eqP->//|].
  by rewrite ltnS leqn0 => /eqP/min_dist_neq0.
Qed.

(* see for example [F.J. MacWilliams and N.J.A. Sloane, The
Theory of Error-Correcting Codes, 1977] (Theorem 2, p.10). *)
Lemma mddP' w v : f (w + v) != None ->
  w \in C ->
  wH v <= mdd_err_cor C_not_trivial -> f (w + v) = Some w.
Proof.
move=> wv wC Hv.
suff ? : dH w (w + v) <= mdd_err_cor C_not_trivial by rewrite (@mddP w _).
by rewrite /dH opprD addrA subrr sub0r wH_opp.
Qed.

End min_dist_decoding_prop.

(* TODO: move? *)
Definition vproj n (F : ringType) (x : 'rV[F]_n) (s : {set 'I_n}) :=
  \row_(i < n) if i \in s then x ord0 i else 0.

Lemma wH_vproj n (F : ringType) (x : 'rV[F]_n) (s : {set 'I_n}) : wH (vproj x s) <= #| s |.
Proof.
rewrite /wH count_map (_ : #| s | = count (mem s) (enum 'I_n)); last first.
  rewrite cardE -count_predT !count_filter; apply eq_in_count => /= i _.
  by rewrite !inE andbT.
apply sub_count => /= i /=.
rewrite mxE; case: ifPn => //; by rewrite eqxx.
Qed.

Lemma dH_vproj n (F : ringType) (x : 'rV[F]_n) (s : {set 'I_n}) :
  s \subset wH_supp x ->
  dH x (vproj x s) = #| (~: s) :&: (wH_supp x) |.
Proof.
move=> H; rewrite dHE.
have -> : x - vproj x s = vproj x (~: s).
  apply/rowP => i; rewrite !mxE !inE; case: ifPn => /=;
    [by rewrite subrr | by rewrite subr0].
rewrite /vproj /wH count_map /= cardE size_filter -enumT /=.
apply eq_in_count => /= i _; rewrite !mxE !inE.
case: ifPn => //; by rewrite eqxx.
Qed.

Lemma wH_vproj_take n (F : ringType) (x : 'rV[F]_n) t :
  wH (vproj x [set i in take t (enum (wH_supp x))]) <= t.
Proof.
set s := take t (enum (wH_supp x)).
rewrite (leq_trans (wH_vproj x [set i in s])) //.
apply (@leq_trans (size s)); last first.
  rewrite size_take -cardE card_wH_supp; case: ifPn => //; by rewrite -leqNgt.
rewrite cardsE; apply/eq_leq/card_uniqP.
have : subseq s (enum (wH_supp x)).
  by rewrite -(cat_take_drop t (enum (wH_supp x))) prefix_subseq.
move/subseq_uniq; apply; by apply enum_uniq.
Qed.

Lemma wH_vproj_take2 n (F : ringType) (x : 'rV[F]_n) t : t < wH x <= t.*2 ->
  dH x (vproj x [set i in take t (enum (wH_supp x))]) <= t.
Proof.
move=> xt.
rewrite dH_vproj; last first.
  apply/subsetP => i /=; rewrite !inE.
  by move/mem_take; rewrite mem_enum inE.
rewrite (@leq_trans #| drop t (enum (wH_supp x)) |) //.
  apply/subset_leq_card/subsetP => /= i.
  rewrite !inE => /andP[] si xi0.
  have : i \in enum (wH_supp x) by rewrite mem_enum inE.
  rewrite -{1}(cat_take_drop t (enum (wH_supp x))) mem_cat => /orP[] //.
  by rewrite (negbTE si).
have : #| wH_supp x | <= t.*2 by rewrite card_wH_supp; case/andP : xt.
rewrite cardE -{1}(cat_take_drop t (enum (wH_supp x))).
rewrite size_cat -addnn size_take -{1}cardE card_wH_supp.
case/andP : xt => -> /= _.
rewrite leq_add2l; apply/leq_trans/eq_leq/card_uniqP.
have : uniq (enum (wH_supp x)) by apply enum_uniq.
by rewrite -{1}(cat_take_drop t (enum (wH_supp x))) cat_uniq => /and3P[].
Qed.

Section hamming_bound.

Definition ball q n x r := [set y : 'rV['F_q]_n | dH x y <= r].

Lemma min_dist_ball_disjoint n q (C : Lcode0.t 'F_q n)
  (C_not_trivial : not_trivial C) t :
  min_dist C_not_trivial = t.*2.+1 ->
  forall x y, x \in C -> y \in C -> x != y -> ball x t :&: ball y t = set0.
Proof.
move=> Hmin /= x y xC yC xy.
apply/eqP/negPn/negP; case/set0Pn => /= z; rewrite !inE => /andP[xzt yzt].
have xyt : dH x y <= t.*2.
  by rewrite -addnn (leq_trans (dH_tri_ine z _ _)) // leq_add // dH_sym.
move: (min_dist_prop C_not_trivial xC yC xy).
rewrite Hmin => /(leq_ltn_trans xyt); by rewrite ltnn.
Qed.

Lemma ball_disjoint_min_dist_lb n q (C : Lcode0.t 'F_q n)
  (C_not_trivial : not_trivial C) t :
  (forall x y, x \in C -> y \in C -> x != y -> ball x t :&: ball y t = set0) ->
  forall x : 'rV_n, x \in C -> x != 0 -> t.*2 < wH x
  (* NB: not as strong as min_dist C_not_trivial = t.*2.+1 *).
Proof.
move=> H x xC x0.
rewrite ltnNge; apply: contra x0 => xt.
apply/negPn/negP => x0.
move: (H x 0 xC (mem0v C) x0) => {H}.
apply/eqP/set0Pn => /=.
case: (leqP (wH x) t) => H.
  by exists x; rewrite !inE dH0x H andbT dHE subrr wH0.
set s := take t (enum (wH_supp x)).
set x1 : 'rV['F_q]_n := vproj x [set i | i \in s].
exists x1; by rewrite !inE dH0x wH_vproj_take andbT wH_vproj_take2 // H.
Qed.

Definition card_ball q n r := (\sum_(i < r.+1) 'C(n, i) * (q.-1)^i)%N.

Lemma card_ballE q n (r : nat) : r <= n -> prime q ->
  forall x : 'rV['F_q]_n, #| ball x r | = card_ball q n r.
Proof.
destruct q as [|q'] => //.
destruct q' as [|q'] => //.
set q := q'.+2.
destruct n as [|n'].
  rewrite leqn0 => /eqP -> => primep x.
  rewrite (empty_rV x) /card_ball big_ord_recl bin0 mul1n big_ord0 addn0 expn0.
  rewrite /ball (_ : [set _ | _] = set1 0) ?cards1 //; apply/setP => /= y.
  by rewrite !inE leqn0 dH0x wH_eq0.
set n := n'.+1.
move=> rn primeq x.
rewrite /ball.
have -> : [set y | dH x y <= r] = \bigcup_(i < r.+1) [set y | dH x y == i].
  apply/setP => /= y; rewrite !inE.
  apply/idP/bigcupP => [xy|].
    rewrite -ltnS in xy.
    exists (Ordinal xy) => //; by rewrite inE.
  case=> /= i _.
  rewrite inE => /eqP ->.
  move: (ltn_ord i); by rewrite ltnS.
transitivity (\sum_(i < r.+1) #| [set y | dH x y == i] |)%N.
  set D := \bigcup_(i < _) _.
  set f := fun i : 'I_r.+1 => [set y | dH x y == i].
  have [H1 H2] : trivIset (f @: 'I_r.+1) /\ {in 'I_r.+1 &, injective f}.
    apply: trivIimset.
    - move=> i j _ _ ji; rewrite -setI_eq0; apply/eqP/setP => /= y.
      rewrite !inE.
      have [->/=|//] := eqVneq (dH x y) i.
      by apply/negbTE; rewrite eq_sym.
    - apply/negP; case/imsetP => /= i _ => /esym.
      apply/eqP/sphere_not_empty.
      by rewrite (leq_trans _ rn) //; move: (ltn_ord i); rewrite ltnS.
  have partD : partition (f @: enum 'I_r.+1) D.
    apply/and3P; split.
    - rewrite cover_imset //; apply/eqP/eq_bigl => i; by rewrite mem_enum.
    - rewrite (_ : [set f x | x in _ ] = [set f x | x : 'I_r.+1]) //.
      apply/setP => s; apply/imsetP/imsetP => -[a Ha ->]; first by exists a.
      exists a => //; by rewrite mem_enum.
    - apply/negP; case/imsetP => /= i _.
      apply/eqP; rewrite eq_sym; apply/sphere_not_empty.
      by rewrite (leq_trans _ rn) //; move: (ltn_ord i); rewrite ltnS.
  rewrite (card_partition partD) /= big_imset /=.
  - apply eq_bigl => i; by rewrite mem_enum.
  - move=> i j _ _;by apply H2.
apply eq_bigr => i _.
rewrite card_sphere // (leq_trans _ rn) //; move: (ltn_ord i); by rewrite ltnS.
Qed.

Lemma hamming_bound q n (C : Lcode0.t 'F_q n)
  (C_not_trivial : not_trivial C) t (tn : t <= n) : prime q ->
  min_dist C_not_trivial = t.*2.+1 -> #| C | * card_ball q n t <= q^n.
Proof.
move=> primeq.
destruct q as [|q'] => //.
destruct q' as [|q'] => //.
set q := q'.+2.
move/min_dist_ball_disjoint => H.
suff : \sum_(c in C) #|ball c t| <= q ^ n.
  rewrite (eq_bigr (fun c => card_ball q n t)); last first.
    rewrite /= => c cC; by rewrite card_ballE.
  by rewrite big_const iter_addn_0 mulnC.
have -> : q ^ n = #| 'rV['F_q]_n |.
  by rewrite card_mx mul1n card_ord Fp_cast.
set P : {set {set _}} := [set ball c t | c in C].
have trivIP : trivIset P.
  apply/trivIsetP => /= s1 s2 /imsetP[/= c1 c1C] -> /imsetP[/= c2 c2C] -> s1s2.
  rewrite -setI_eq0; apply/eqP/H => //.
  by apply: contra s1s2 => /eqP ->.
have /card_partition : partition P (\bigcup_(c in C) ball c t).
  apply/and3P; split => //; first by rewrite cover_imset.
  apply/imsetP; case => /= x xC.
  move/setP/(_ x); by rewrite !inE dHE subrr wH0 leq0n.
rewrite big_imset /=; last first.
  move=> c1 c2 c1C c2C.
  have [//|c1c2 abs] := eqVneq c1 c2.
  move: (H _ _ c1C c2C c1c2).
  rewrite abs setIid => /setP/(_ c2).
  by rewrite !inE dHE subrr wH0 leq0n.
by move=> <-; apply subset_leq_card; apply/subsetP => x; rewrite inE.
Qed.

Definition perfect n q (C : Lcode0.t 'F_q n)
  (C_not_trivial : not_trivial C) :=
  exists r, min_dist C_not_trivial = r.*2.+1 /\ (#| C | * card_ball q n r = q^n)%N.

End hamming_bound.

Section bounded_distance_decoding.

Variables (F : finFieldType) (n : nat) (C : Lcode0.t F n).
Variable (f : repairT F F n).
Hypothesis C_not_trivial : not_trivial C.

Local Open Scope ecc_scope.

Lemma MD_BDD (Himg : oimg f \subset C) :
  (forall x, f x != None) (* f does not fail *) ->
  MD_decoding [set cw in C] f ->
  (mdd_err_cor C_not_trivial).-BDD (C, f).
Proof.
move=> no_fail Hmin.
rewrite /BD_decoding => /= c e cC wHe.
move: (@mddP _ _ _ _  Hmin C_not_trivial Himg c (c + e) (no_fail _) cC) => //.
by rewrite dH_wH => /(_ wHe).
Qed.

End bounded_distance_decoding.

Module Encoder.

Section encoder_def.

Variables (A : finFieldType) (n : nat).

Record t (C : Lcode0.t A n) (M : finType) : Type := mk {
  enc :> encT A M n ;
  enc_inj : injective enc ;
  enc_img : enc @: M \subset C }.

End encoder_def.

End Encoder.

Coercion encoder_coercion A n (C : Lcode0.t A n) M (c : Encoder.t C M) : encT A M n :=
 let: Encoder.mk v _ _ := c in v.

Module Decoder.

Section decoder_def.

Variables (A B : finFieldType) (n : nat).

Record t (C : Lcode0.t A n) (M : finType) : Type := mk {
  repair :> repairT B A n ;
  repair_img : oimg repair \subset C ;
  discard : discardT A n M ;
  dec : decT B M n := [ffun x => omap discard (repair x)] }.

End decoder_def.

End Decoder.

Coercion decoder_coercion B A n (C : Lcode0.t A n) k (c : Decoder.t B C k) : repairT B A n :=
 let: Decoder.mk v _ _ _ := c in v.

Module Lcode.

Section lcode_def.

Variables (A B : finFieldType) (n : nat) (M : finType).

Record t : Type := mk {
  lcode0_of :> Lcode0.t A n ;
  enc : Encoder.t lcode0_of M ;
  dec : Decoder.t B lcode0_of M ;
  compatible : cancel_on lcode0_of (Encoder.enc enc) (Decoder.discard dec) }.

End lcode_def.

Local Coercion lcode_coercion (A B : finFieldType) (n : nat) (M : finType) (c : t A B n M) : {vspace 'rV[A]_n} :=
 Lcode.lcode0_of c.

Section lcode_prop.

Variables (A B : finFieldType) (n : nat).

Lemma dimlen (k : nat) (C : t A B n 'rV[A]_k) : 1 < #|A| -> k <= n.
Proof.
move=> F1.
case : C =>  cws [] /= f.
move/inj_card => /=.
by rewrite !card_mx !mul1n leq_exp2l.
Qed.

Lemma min_dist_prop_old (M : finType) (C : t A B n M) (C_not_trivial : not_trivial C) m m' :
  m != m' ->
  min_dist C_not_trivial <= dH (Encoder.enc (enc C) m) (Encoder.enc (enc C) m').
Proof.
move=> /= mm'.
have H : Encoder.enc (enc C) m - Encoder.enc (enc C) m' \in C.
  apply Lcode0.aclosed.
  - move/subsetP: (Encoder.enc_img (enc C)) => /(_ (Encoder.enc (enc C) m)).
    apply; apply/imsetP => /=; by exists m.
  - rewrite Lcode0.oclosed //.
    move/subsetP: (Encoder.enc_img (enc C)) => /(_ (Encoder.enc (enc C) m')).
    apply; apply/imsetP => /=; by exists m'.
have H' : Encoder.enc (enc C) m - Encoder.enc (enc C) m' != 0.
  move: mm'; apply contra. rewrite subr_eq0. move/eqP.
  move/Encoder.enc_inj/eqP. by rewrite eqtype.eq_sym.
by apply min_dist_is_min.
Qed.

End lcode_prop.

End Lcode.

Coercion lcode_coercion (A B : finFieldType) (n : nat) (M : finType) (c : Lcode.t A B n M) : {vspace 'rV[A]_n} :=
 let: Lcode.mk v _ _ _ := c in v.

Section AboutCasts.

Variable R : comRingType.

Definition cast_cols {rows} {f : nat -> nat -> nat} {P : nat -> nat -> Type}
  (HPf : forall k n, P k n -> f k n = n) {k n} (HP : P k n) :
  'M[R]_(rows, f k n) -> 'M_(rows, n) :=
  castmx (erefl rows, HPf _ _ HP).

Lemma mulmx_castmx_cols_comm :
  forall (f : nat -> nat -> nat) (P : nat -> nat -> Type)
  (HPf: forall k n, P k n -> f k n = n) k n (HP : P k n)
  rows (x : 'M[R]_(rows, k)) (B : 'M_(k, f k n)),
  x *m castmx (erefl k, HPf _ _ HP) B =
  castmx (erefl rows, HPf _ _ HP) (x *m B).
Proof.
move=> f P HPf k n HP.
move: (HPf k n HP); rewrite (HPf k n HP) => e.
by rewrite (eq_irrelevance e (refl_equal n)).
Qed.

Lemma castmx_mulmx_cols_comm :
  forall (f : nat -> nat -> nat) (P : nat -> nat -> Type)
  (HPf: forall k n, P k n -> f k n = n) k n (HP : P k n)
  (x : 'M[R]_(n, k)) (B : 'M_(k, f k n)),
  (castmx (erefl k, HPf _ _ HP) B) *m x =
  (B *m castmx (esym (HPf _ _ HP), erefl _) x).
Proof.
move=> f P HPf k n_ HP.
move: (HPf k n_ HP); rewrite (HPf k n_ HP) => e.
by rewrite (eq_irrelevance e (refl_equal n_)).
Qed.

Lemma mulmx_castmx_cols_comm2 :
  forall (f : nat -> nat -> nat) (P : nat -> nat -> Type)
  (HPf: forall k n, P k n -> f k n = n) k n (HP : P k n)
  rows (x : 'M[R]_(f k n, rows)) cols (B : 'M_(rows, cols)),
  castmx (HPf _ _ HP, erefl rows) x *m B =
  castmx (HPf _ _ HP, erefl cols) (x *m B).
Proof.
move=> f P HPf k n_ HP.
move: (HPf k n_ HP); rewrite (HPf k n_ HP) => e.
by rewrite (eq_irrelevance e (refl_equal n_)).
Qed.

Lemma castmx_cols_mulmx : forall (f : nat -> nat -> nat) P
  (HPf : forall k n, P k n -> f k n = n) k n (HP : P k n)
  rows (X : 'M[R]_(rows, f k n)) cols (Y : 'M_(f k n, cols)),
  castmx (erefl rows, HPf _ _ HP) X *m
  castmx (HPf _ _ HP, erefl cols) Y = X *m Y.
Proof.
move=> f P HPf k n HP rows X cols Y; apply/matrixP => i j.
rewrite !mxE /=.
move: (HPf _ _ HP) X Y; rewrite (HPf _ _ HP) => e M Y.
apply eq_bigr => l _ /=.
by rewrite (eq_irrelevance e (refl_equal n)).
Qed.

Lemma castmx_cols_mulmx2 : forall (f : nat -> nat -> nat) P
  (HPf : forall k n, P k n -> f k n = n) k n (HP : P k n)
  (X : 'M[R]_(f k n, f k n)) cols (Y : 'M_(f k n, cols)),
  castmx (HPf _ _ HP, HPf _ _ HP) X *m
  castmx (HPf _ _ HP, erefl cols) Y = castmx (HPf _ _ HP, erefl cols) (X *m Y).
Proof.
move=> f P HPf k n_ HP X cols Y; apply/matrixP => i j.
rewrite !mxE /=.
move: (HPf _ _ HP) X Y; rewrite (HPf _ _ HP) => e M Y.
rewrite castmxE !mxE /=.
apply eq_bigr => l _ /=.
rewrite !castmxE /=.
congr (M _ _ * Y _ _); by apply val_inj.
Qed.

End AboutCasts.

Arguments cast_cols {R} {rows} {f} {P} _ {k} {n}.

Section AboutCasts2.

Variable F : fieldType. (* NB: rank requires fields *)

Lemma rank_cast_cols_comm :
  forall (f : nat -> nat -> nat) (P : nat -> nat -> Type)
  (HPf: forall k n, P k n -> f k n = n) k n (HP : P k n)
  (B : 'M[F]_(k, f k n)),
  \rank (cast_cols HPf HP B) = \rank B.
Proof.
move=> f P HPf k n HP.
rewrite /cast_cols /eq_rect.
move: (HPf k n HP); rewrite (HPf k n HP) => e.
by rewrite (eq_irrelevance e (refl_equal n)).
Qed.

End AboutCasts2.

Module Syslcode.

Section systematic_lcode_def.

Variables (F : finFieldType) (k n : nat).

Hypothesis dimlen : k <= n.

Variable CSM : 'M[F]_(n - k, k).

Definition PCM : 'M_(n - k, n) := castmx (erefl, subnKC dimlen) (row_mx CSM 1%:M).

Definition GEN : 'M_(k, n) := castmx (erefl, subnKC dimlen) (row_mx 1%:M (- CSM)^T).

Local Notation "'A" := CSM.
Local Notation "'G" := GEN.
Local Notation "'H" := PCM.

Lemma rank_GEN : \rank 'G = k.
Proof. rewrite /GEN mxrank_castmx; by apply rank_row_mx, rank_I. Qed.

(* H^T is the right kernel of G *)
Lemma G_H_T : 'G *m 'H ^T = 0.
Proof.
rewrite /GEN /PCM trmx_cast /= (castmx_cols_mulmx subnKC) tr_row_mx.
by rewrite mul_row_col mul1mx trmx1 mulmx1 -linearD addrN linear0.
Qed.

Lemma H_G_T : 'H *m 'G ^T = 0.
Proof. by rewrite -trmx0 -G_H_T trmx_mul trmxK. Qed.

Definition encode : encT F 'rV[F]_k n := [ffun x => x *m 'G].

Lemma encode_inj : injective encode.
Proof.
rewrite /injective => a b; rewrite /encode 2!ffunE.
exact: (@full_rank_inj _ _ _ 'G dimlen rank_GEN).
Qed.

Lemma encode_code pt : encode pt \in kernel 'H.
Proof.
rewrite memv_ker lfunE /= /encode ffunE /syndrome.
by rewrite trmx_mul trmxK -mulmxA G_H_T mulmx0.
Qed.

Definition DIS : 'M[F]_(k, n) := castmx (erefl, subnKC dimlen) (row_mx 1%:M 0).

Local Notation "'D" := DIS.

Definition discard : discardT F n 'rV_k := [ffun x => x *m 'D^T].

Definition t (repair : repairT F F n)
             (repair_img : oimg repair \subset kernel 'H)
             (H : cancel_on (kernel 'H) encode discard) : Lcode.t F F n 'rV[F]_k.
apply: (@Lcode.mk _ _ _ _ (kernel 'H)
         (Encoder.mk encode_inj _)
         (Decoder.mk repair_img discard)
         H) => /=.
apply/subsetP => m.
case/imsetP => /= m' _ ->.
exact: encode_code.
Defined.

End systematic_lcode_def.

End Syslcode.

Section syslcode_properties.

Variables (F : finFieldType) (n k : nat).
Hypothesis dimlen : k <= n.
Variable CSM : 'M[F]_(n - k, k).
Variable repair : repairT F F n.
Hypothesis repair_img : oimg repair \subset kernel (Syslcode.PCM dimlen CSM).
Local Notation "'H" := (Syslcode.PCM dimlen CSM).
Local Notation "'G" := (Syslcode.GEN dimlen CSM).
Local Notation "'D" := (Syslcode.DIS dimlen CSM).

Hypothesis cancel_discard :
  cancel_on (kernel 'H) (Syslcode.encode dimlen CSM) (Syslcode.discard dimlen).
Let C : Lcode.t _ _ _ _ := Syslcode.t repair_img cancel_discard.

Lemma encode_image_code (x : 'rV_n) :
  {y : 'rV_k | Encoder.enc (Lcode.enc C) y = x} -> x \in C.
Proof.
case=> y <-.
by rewrite /= memv_ker lfunE /= /syndrome ffunE trmx_mul trmxK -mulmxA Syslcode.G_H_T mulmx0.
Qed.

End syslcode_properties.

From mathcomp Require Import fieldext finfield.

Module Rcode.

Section restricted_code_definition.

Variables (F0 F1 : finFieldType) (f : {rmorphism F0 -> F1}) (n : nat).

Inductive t (C : Lcode0.t F1 n) := mk {
  c : Lcode0.t F0 n ;
  P : forall x, x \in c <-> map_mx f x \in C }.

End restricted_code_definition.

End Rcode.

Coercion rcode_coercion (F0 F1 : finFieldType) (f : {rmorphism F0 -> F1}) (n : nat) (C : Lcode0.t F1 n) (c : Rcode.t f C) : {vspace 'rV[F0]_n} :=
 let: Rcode.mk x _ := c in x.
