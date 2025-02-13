(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg perm zmodp.
From mathcomp Require Import matrix vector ssrnum lra ring.
From mathcomp Require Import Rstruct reals.
Require Import realType_ext ssr_ext ssralg_ext num_occ bigop_ext.
Require Import fdist channel pproba f2 linearcode subgraph_partition tanner.
Require Import tanner_partition hamming binary_symmetric_channel decoding.
Require Import channel_code summary checksum summary_tanner.

(**md**************************************************************************)
(* # LDPC Codes and Sum-Product Decoding                                      *)
(*                                                                            *)
(* Main emmas:                                                                *)
(* - Correctness of the estimation of the sum-product algorithm, i.e., proof  *)
(*   that it computes the marginal aposteriori probability                    *)
(*   (`estimation_correctness`)                                               *)
(* - Proof that alpha message can be computed recursively                     *)
(*   (`recursive_computation`)                                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory Num.Theory.

Local Open Scope num_occ_scope.
Local Open Scope channel_scope.
Local Open Scope ring_scope.

Section regular_ldpc.
Let R := Rdefinitions.R.
Variables (m n : nat).

Definition Hreg_ldpc (H : 'M['F_2]_(m, n)) (lambda rho : nat) :=
  (forall n0, wH (col n0 H)^T = lambda) /\ (forall m0, wH (row m0 H) = rho).

Record reg_ldpc := {
  regH : 'M['F_2]_(m, n) ;
  reglambda : nat ;
  regrho : nat ;
  Hreg : Hreg_ldpc regH reglambda regrho }.

Definition reg_rate C : R := 1 - (reglambda C)%:R / (regrho C)%:R.

End regular_ldpc.

Lemma reg_ldpc_prop {R : realType} m n : forall (C : reg_ldpc m n),
  n <> O -> regrho C <> O ->
  m%:R / n%:R = (reglambda C)%:R / (regrho C)%:R :> R.
Proof.
case => /= H lam rho [] Hlam Hrho Hm0 Hrho0.
have : (\sum_(m0 : 'I_m) wH (row m0 H) = rho * m)%nat.
  transitivity (\sum_(m0 < m) rho)%nat.
    apply eq_bigr => i _; by apply Hrho.
  by rewrite big_const iter_addn addn0 card_ord.
rewrite sum_wH_row => Htmp.
have {}Htmp : (lam * n = rho * m)%nat.
  rewrite -Htmp.
  transitivity (\sum_(n0 < n) lam)%nat.
    by rewrite big_const iter_addn addn0 card_ord.
  apply eq_bigr => i _; exact/esym/Hlam.
apply: (@mulfI _ n%:R).
  by rewrite (_ : 0 = 0%:R)// eqr_nat; exact/eqP.
rewrite mulrCA divff ?mulr1//; last first.
  by rewrite (_ : 0 = 0%:R)// eqr_nat; exact/eqP.
apply: (@mulfI _ rho%:R).
  by rewrite (_ : 0 = 0%:R)// eqr_nat; exact/eqP.
rewrite mulrA [in X in _ = X](mulrC rho%:R).
rewrite -mulrA (mulrCA rho%:R) mulfV ?mulr1; last first.
  by rewrite (_ : 0 = 0%:R)// eqr_nat; exact/eqP.
by rewrite -natrM -Htmp natrM mulrC.
Qed.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope vec_ext_scope.

Section DMC_sub_vec_Fnext_Vgraph.
Variables (B : finType) (W : `Ch('F_2, B)).
Variable n' : nat.
Let n := n'.+1.
Variable tb : 'rV[B]_n.
Variable m : nat.
Variable H : 'M['F_2]_(m, n).
Local Notation "''V(' x ',' y ')'" := (Vgraph H x y).
Local Notation "''F(' x ',' y ')'" := (Fgraph H x y).
Local Notation "''V'" := (Vnext H).
Local Notation "''F'" := (Fnext H).
Variable tanner : Tanner.acyclic_graph (tanner_rel H).

Lemma DMC_sub_vec_Fnext t n0 :
  W ``(tb \# [set~ n0] | t \# [set~ n0]) =
  (\prod_(i in 'F n0) W ``(tb \# 'V(i, n0) :\ n0 | t \# 'V(i, n0) :\ n0))%R.
Proof.
rewrite DMCE.
transitivity (\prod_(i in setT :\ n0) W (t ``_ i) (tb ``_ i))%R.
  transitivity (\prod_(i in [set~ n0]) W (t ``_ i) (tb ``_ i))%R; last first.
    apply eq_bigl => x /=; by rewrite !inE andbT.
  by rewrite -rprod_sub_vec.
rewrite -{1}(cover_Vgraph_part_vnode (Tanner.connected tanner) n0).
rewrite big_trivIset /=; last by apply trivIset_Vgraph_part_vnode, (Tanner.acyclic tanner).
rewrite /Vgraph_part_vnode.
(* specialize the bigop for non-empty A's only *)
transitivity (\prod_(A in [set 'V(m0, n0) :\ n0 | m0 in 'F n0 & ('V(m0, n0) :\ n0 != set0)])
  \prod_(x in A) W (t ``_ x) (tb ``_ x))%R.
  rewrite (bigID [pred x | x == set0 ]) /=.
  rewrite big1; last first.
    move=> i /andP [] Hi1 /eqP ->.
    rewrite big1 // => j.
    by rewrite inE.
  rewrite mul1r.
  apply eq_bigl => i.
  move Hrhs : (_ \in _) => [|] /=.
    case/imsetP : Hrhs => /= m1 Hm1 Hi.
    move Hrhs' : (_ != _) => [|] /=.
      apply/esym/imsetP; exists m1 => //.
      by rewrite inE Hm1 -Hi.
    apply/esym/imsetP => abs.
    case: abs => m2 Hm2 Hi2.
    rewrite inE in Hm2.
    case/andP : Hm2 => _.
    by rewrite -Hi2 Hrhs'.
  apply negbT in Hrhs.
  apply/esym/negbTE.
  apply: contra Hrhs.
  case/imsetP => m1.
  rewrite inE => /andP [] Hm1 Hm1' Hi.
  by apply/imsetP; exists m1.
rewrite big_imset; last first.
  move=> /= m0 m1 Hm0 Hm1.
  rewrite inE /= in Hm0.
  rewrite inE /= in Hm1.
  case/andP : Hm0 Hm1 => ? ? /andP [] ? ?.
  apply Vgraph_injective => //; [ | | ]; try by rewrite -FnextE.
  by apply tanner.
apply/esym.
(* specialize the bigop for non-empty `V(i,n0):\n0 only *)
rewrite /= (bigID [pred x | 'V(x, n0) :\ n0 == set0 ]) /=.
rewrite [X in (X * _)%R = _](_ : _ = 1); last first.
  rewrite big1 // => i /andP [] Hi1 /eqP Hi2.
  rewrite Hi2 DMCE.
  rewrite big1 //= => j.
  exfalso.
  rewrite cards0 /= in j.
  by case: j.
rewrite mul1r.
apply eq_big.
  move=> i /=; by rewrite !inE.
move=> i /andP [] Hi1 Hi2.
by rewrite DMCE -rprod_sub_vec.
Qed.

Lemma DMC_sub_vec_Vgraph t m0 n0 : n0 \in 'V m0 ->
   W ``(tb \# ('V(m0, n0) :\ n0) | t \# ('V(m0, n0) :\ n0)) =
   (\prod_(n1 in 'V m0 :\ n0) (W (t ``_ n1) (tb ``_ n1) *
     \prod_(m1 in 'F n1 :\ m0) W ``(tb \# 'V(m1, n1) :\ n1 | t \# 'V(m1, n1) :\ n1)))%R.
Proof.
move=> m0n0.
rewrite DMCE rprod_sub_vec.
rewrite -{1}(cover_Vgraph_part_Vgraph (Tanner.acyclic tanner) m0n0).
rewrite big_trivIset /=; last by apply trivIset_Vgraph_part_Vgraph => //; by apply (Tanner.acyclic tanner).
rewrite /Vgraph_part_Vgraph.
rewrite big_imset /=; last first.
  move=> n1 n2 Hn1 Hn2 /=.
  apply: Vgraph_injective3 Hn1 Hn2 => //; by apply: Tanner.acyclic tanner.
apply eq_bigr => n1 Hn1.
set body := BIG_F.
transitivity (\prod_(i in [predU (pred1 n1) & [pred x | x \in \bigcup_(m1 in 'F n1 :\ m0) ('V(m1, n1) :\ n1)]]) (body i))%R.
  apply eq_bigl => x /=.
  by rewrite !inE.
rewrite {}/body bigU /=; last first.
  apply bigcup_disjoint => m1 Hm1.
  rewrite (@eq_disjoint1 _ n1) //.
  by rewrite !inE eqxx /=.
rewrite (@big_bigcup_partition _ _ _ _ _ (fun x => ('V(x, n1) :\ n1)) (fun x => (W (t ``_ x)) (tb ``_ x)) ('F n1 :\ m0)) /=; last first.
  move=> i j ij.
  rewrite -setI_eq0.
  apply/set0Pn; case=> n2.
  rewrite inE.
  case/andP.
  rewrite 2!inE.
  case/andP => n2n1 Hn2.
  rewrite 2!inE n2n1 /=.
  apply/negP.
  move: Hn2.
  apply disjoint_Vgraph => //; by apply: Tanner.acyclic tanner.
rewrite (big_pred1 n1); last first.
  move=> x /=.
  by rewrite !inE.
congr (_ * _)%R.
apply eq_bigr => m1 Hm1.
by rewrite DMCE -rprod_sub_vec.
Qed.

End DMC_sub_vec_Fnext_Vgraph.

Local Open Scope summary_scope.

Section alpha_beta.

Variable (m n : nat).
Variable H : 'M['F_2]_(m, n).
Local Notation "''V'" := (Vnext H).
Local Notation "''F'" := (Fnext H).
Local Notation "''V(' x ',' y ')'" := (Vgraph H x y).
Local Notation "''F(' x ',' y ')'" := (Fgraph H x y).
Variable B : finType.
Variable W : `Ch('F_2, B).
Variable y : 'rV[B]_n.

Local Open Scope R_scope.

Definition alpha m0 n0 d := \sum_(x = d [~'V(m0, n0) :\ n0])
  W ``(y \# 'V(m0, n0) :\ n0 | x \# 'V(m0, n0) :\ n0) *
    \prod_(m1 in 'F(m0, n0)) (\delta ('V m1) x)%:R.

Definition beta n0 m0 (d : 'rV_n) :=
  W (d ``_ n0) (y ``_ n0) * \prod_(m1 in 'F n0 :\ m0) alpha m1 n0 d.

Local Close Scope R_scope.

Definition dproj_V m0 n0 (d t : 'rV['F_2]_n) := dproj d ('V(m0, n0) :\ n0) t.

(* only the value of d ``_ n0 matters to alpha and beta *)

Lemma alpha_inva n0 m0 (d d' : 'rV_n) :
  n0 \in 'V m0 -> d ``_ n0 = d' ``_ n0 ->
  alpha m0 n0 d = alpha m0 n0 d'.
Proof.
move=> n0m0 dd'.
rewrite /alpha.
transitivity (\sum_(x = d [~'V(m0, n0) :\ n0])
     W ``((y \# 'V(m0, n0) :\ n0) | ((dproj_V m0 n0 d x) \# 'V(m0, n0) :\ n0)) *
     (\prod_(m2 in 'F(m0, n0)) (\delta ('V m2) (dproj_V m0 n0 d x))%:R))%R.
  apply eq_bigr => /= t Ht.
  congr (W ``(_ | _) * _)%R.
    by rewrite /dproj_V sub_vec_dproj.
  apply eq_bigr => i Hi.
  by rewrite /dproj_V checksubsum_dproj_freeon.
transitivity (\sum_(x = d [~'V(m0, n0) :\ n0])
     W ``((y \# 'V(m0, n0) :\ n0) | ((dproj_V m0 n0 d' x) \# 'V(m0, n0) :\ n0)) *
     (\prod_(m2 in 'F(m0, n0)) (\delta ('V m2) (dproj_V m0 n0 d' x))%:R))%R.
  apply eq_bigr => /= i Hi.
  congr (W ``(_ | _) * _)%R.
    by rewrite sub_vec_dproj // sub_vec_dproj.
  apply eq_bigr => j Hj; congr (_%:R)%R.
  rewrite /checksubsum; congr (_ == _).
  apply eq_bigr => /= k Hk.
  rewrite /dproj_V.
  case/boolP : (k \in 'V(m0, n0) :\ n0) => K.
    by rewrite !dproj_in.
  do 2 rewrite dproj_out //.
  have [->//|kn0] := eqVneq k n0.
  rewrite in_setD1 kn0 /= in K.
  exfalso.
  move/negP : K; apply.
  move: kn0.
  by apply Fgraph_Vnext_Vgraph with j.
transitivity (\sum_(x = d' [~'V(m0, n0) :\ n0])
     W ``((y \# 'V(m0, n0) :\ n0) | ((dproj_V m0 n0 d' x) \# 'V(m0, n0) :\ n0)) *
     (\prod_(m2 in 'F(m0, n0)) (\delta ('V m2) (dproj_V m0 n0 d' x))%:R))%R; last first.
   apply/esym.
   apply eq_bigr => /= t Ht.
   congr (W ``(_ | _) * _)%R.
     by rewrite /dproj_V sub_vec_dproj.
   apply eq_bigr => i Hi.
   by rewrite checksubsum_dproj_freeon.
rewrite (reindex_onto (dproj_V m0 n0 d) (dproj_V m0 n0 d')) /=; last first.
  move=> ? ?; by rewrite /dproj_V dprojIdef dproj_freeon.
apply eq_big => /= i.
  apply/andP/forallP.
    case => H1 H2 n1.
    apply/implyP => Hn1.
    rewrite in_setD1 negb_and negbK in Hn1.
    case/orP : Hn1 => Hn1.
      by rewrite (eqP Hn1) -(eqP H2) /dproj_V dproj_out // in_setD1 eqxx.
    by rewrite -(eqP H2) /dproj_V dproj_out // in_setD1 (negbTE Hn1) andbF.
  move=> H1.
  split.
    apply/forallP => n1; apply/implyP => Hn1.
    by rewrite /dproj_V dproj_out.
  rewrite /dproj_V dprojIdef // dproj_freeon //.
  by apply/forallP.
case/andP=> H1 H2.
congr (_ * _)%R.
  congr (W ``(_ | _)).
  by rewrite !sub_vec_dproj.
apply eq_bigr => m2 Hm2.
congr ((_ == _)%:R)%R.
apply eq_bigr => n3 Hn3.
have [X|X] := boolP (n3 \in 'V(m0, n0) :\ n0).
  by rewrite !dproj_in.
by rewrite !dproj_out.
Qed.

Lemma beta_inva_helper n0 m0 m1 (d d' : 'rV_n) :
  n0 \in 'V m0 -> d ``_ n0 = d' ``_ n0 -> m1 \in 'F n0 :\ m0 ->
  alpha m1 n0 d = alpha m1 n0 d'.
Proof.
move=> n0m0 dd' Hm1.
rewrite /alpha.
transitivity (\sum_(x = d [~'V(m1, n0) :\ n0])
      W ``((y \# 'V(m1, n0) :\ n0) | ((dproj_V m1 n0 d x) \# 'V(m1, n0) :\ n0)) *
      (\prod_(m2 in 'F(m1, n0)) (\delta ('V m2) (dproj_V m1 n0 d x))%:R))%R.
  apply eq_bigr => /= t Ht.
  congr (W ``(_ | _) * _)%R.
    by rewrite /dproj_V sub_vec_dproj.
  apply eq_bigr => i Hi.
  by rewrite checksubsum_dproj_freeon.
transitivity (\sum_(x = d [~'V(m1, n0) :\ n0])
      W ``((y \# 'V(m1, n0) :\ n0) | ((dproj_V m1 n0 d' x) \# 'V(m1, n0) :\ n0)) *
      (\prod_(m2 in 'F(m1, n0)) (\delta ('V m2) (dproj_V m1 n0 d' x))%:R))%R.
  apply eq_bigr => /= i Hi.
  congr (W ``(_ | _) * _)%R.
    by rewrite /dproj_V sub_vec_dproj // sub_vec_dproj.
  apply eq_bigr => j Hj.
  rewrite /checksubsum.
  congr ((_ == _)%:R)%R.
  apply eq_bigr => /= k Hk.
  rewrite /dproj_V.
  case/boolP : (k \in 'V( m1, n0) :\ n0) => K.
    by do 2 rewrite dproj_in //.
  do 2 rewrite dproj_out //.
  have [->//|kn0] := eqVneq k n0.
  rewrite in_setD1 kn0 /= in K.
  exfalso.
  move/negP : K; apply.
  move: kn0.
  by apply Fgraph_Vnext_Vgraph with j.
transitivity (\sum_(x = d' [~'V(m1, n0) :\ n0])
      W ``((y \# 'V(m1, n0) :\ n0) | ((dproj_V m1 n0 d' x) \# 'V(m1, n0) :\ n0)) *
      (\prod_(m2 in 'F(m1, n0)) (\delta ('V m2) (dproj_V m1 n0 d' x))%:R))%R; last first.
    apply/esym.
    apply eq_bigr => /= t Ht.
    congr (W ``(_ | _) * _)%R.
      by rewrite /dproj_V sub_vec_dproj.
    apply eq_bigr => i Hi.
    by rewrite checksubsum_dproj_freeon.
rewrite (reindex_onto (dproj_V m1 n0 d) (dproj_V m1 n0 d')) /=; last first.
  move=> ? ?; by rewrite /dproj_V dprojIdef dproj_freeon.
apply eq_big => /= i.
  apply/andP/forallP.
    case => H1 H2 n1.
    apply/implyP => Hn1.
    rewrite in_setD1 negb_and negbK in Hn1.
    case/orP : Hn1 => Hn1.
      rewrite (eqP Hn1) -(eqP H2) /dproj_V.
      have K : n0 \notin 'V( m1, n0) :\ n0 by rewrite in_setD1 eqxx.
      by rewrite dproj_out.
    by rewrite -(eqP H2) /dproj_V dproj_out // in_setD1 (negbTE Hn1) andbF.
  move=> H1.
  split.
    apply/forallP => n1; apply/implyP => Hn1.
    rewrite in_setD1 negb_and negbK in Hn1.
    case/orP : Hn1 => n1n0.
      move/eqP : n1n0 => ?; subst n1.
      by rewrite /dproj_V dproj_out // in_setD1 eqxx.
    by rewrite /dproj_V dproj_out // in_setD1 (negbTE n1n0) andbC.
  rewrite /dproj_V dprojIdef dproj_freeon //.
  by apply/forallP.
case/andP=> H1 H2.
congr (_ * _)%R.
  congr (W ``(_ | _)).
  by rewrite /dproj_V !sub_vec_dproj.
apply eq_bigr => m2 Hm2.
congr ((_ == _)%:R)%R.
apply eq_bigr => n3 Hn3.
rewrite /dproj_V.
case/boolP : (n3 \in 'V( m1, n0) :\ n0) => K.
  by rewrite !dproj_in.
by rewrite !dproj_out.
Qed.

Lemma beta_inva n0 m0 (d d' : 'rV_n) :
  n0 \in 'V m0 -> d ``_ n0 = d' ``_ n0 ->
  beta n0 m0 d = beta n0 m0 d'.
Proof.
move=> n0m0 dd'.
rewrite /beta dd'.
congr (_ * _)%R.
apply eq_bigr => m1 Hm1.
by apply beta_inva_helper with m0.
Qed.

End alpha_beta.

Section sum_prod_correctness.

Variables (m n' : nat).
Let n := n'.+1.
Variable H : 'M['F_2]_(m, n).
Variable (B : finType) (W : `Ch('F_2, B)).
Let C := kernel H.
Let C_not_empty := Lcode0.not_empty C.
Variable y : (`U C_not_empty).-receivable W.

(*Let g := fun n0 (x : 'F_2) => (`U C_not_empty) '_ n0 `^^ W (x | Hy).*)

Local Notation "''V'" := (Vnext H).
Local Notation "''F'" := (Fnext H).
Local Notation "''V(' x ',' y ')'" := (Vgraph H x y).
Local Notation "''F(' x ',' y ')'" := (Fgraph H x y).

Variable tanner : Tanner.acyclic_graph (tanner_rel H).

Local Notation "'alpha'" := (alpha H W y).

Local Open Scope R_scope.

Lemma estimation_correctness (d : 'rV_n) n0 :
  let b := d ``_ n0 in let P := `U C_not_empty in
  P '_ n0 `^^ W (b | y) =
    marginal_post_prob_den y * post_prob_uniform_cst [set cw in C] y *
    W `(y ``_ n0 | b) * \prod_(m0 in 'F n0) alpha m0 n0 d.
Proof.
move=> b P.
rewrite fdist_marginal_post_probE -2!mulrA; congr (_ * _).
transitivity (post_prob_uniform_cst [set cw in C] y *
              (\sum_(x = d [~ setT :\ n0])
                W ``(y | x) * \prod_(m0 < m) (\delta ('V m0) x)%:R))%R.
  rewrite [RHS]big_distrr [in RHS]/=.
  apply eq_big => t; first by rewrite -freeon_all.
  rewrite inE andTb => td_n0.
  rewrite post_prob_uniform_kernel -mulrA; congr (_ * _)%R.
  rewrite mulrC; congr (_ * _)%R.
  by rewrite checksubsum_in_kernel inE mem_kernel_syndrome0.
congr (_ * _)%R.
transitivity (W `(y ``_ n0 | b) *
  (\sum_(x = d [~ setT :\ n0]) W ``(y \# ~: [set n0] | x \# ~: [set n0]) *
   \prod_(m0 < m) (\delta ('V m0) x)%:R)).
  rewrite big_distrr /=; apply eq_bigr => t Ht.
  rewrite mulrA; congr (_ * _)%R.
  rewrite /b (freeon_notin Ht); last by rewrite !inE eqxx.
  rewrite DMCE (bigD1 n0) //=; congr (_ * _).
  rewrite DMCE rprod_sub_vec; apply eq_big => i //=.
  by rewrite in_setC in_set1.
congr (_ * _).
transitivity (
    \sum_(x = d [~ setT :\ n0]) W ``(y \# ~: [set n0] | x \# ~: [set n0]) *
    \prod_(m0 in 'F n0) \prod_(m1 in 'F(m0, n0)) (\delta ('V m1) x)%:R).
  apply eq_bigr => /= t Ht.
  congr (_ * _)%R.
  by rewrite -(rprod_Fgraph_part_fnode (Tanner.connected tanner) (Tanner.acyclic tanner)
      (fun m0 => (\delta ('V m0) t)%:R)).
transitivity (
  \sum_(x = d [~ setT :\ n0]) \prod_(m0 in 'F n0)
    (W ``(y \# 'V(m0, n0) :\ n0 | x \# 'V(m0, n0) :\ n0) *
      \prod_(m1 in 'F(m0, n0)) (\delta ('V m1) x)%:R)).
  apply: eq_bigr => /= t Ht.
  rewrite [in X in _ = X]big_split /=; congr (_ * _).
  by apply DMC_sub_vec_Fnext.
rewrite (@rmul_rsum_commute0 _ _ _ (Tanner.connected tanner)  (Tanner.acyclic tanner) d n0 _ y (fun m x y => W ``(x | y))) //.
move=> /= m1 m0 t m1m0n0 tn0dn0; by rewrite checksubsum_dprojs_V.
Qed.

(* TODO: rename. move? *)
Definition K949 (n0 : 'I_n) df :=
  ((W Zp0 (y ``_ n0) * \prod_(m1 in 'F n0) alpha m1 n0 (df `[ n0 := Zp0 ])) +
    W Zp1 (y ``_ n0) * \prod_(m1 in 'F n0) alpha m1 n0 (df `[ n0 := Zp1 ]))^-1.

Let R := Rdefinitions.R.

Lemma K949_lemma df n0 : K949 n0 df =
  marginal_post_prob_den y * post_prob_uniform_cst [set cw in C] y.
Proof.
rewrite /K949 /marginal_post_prob_den /post_prob_uniform_cst -invfM.
congr (_^-1).
transitivity (\sum_(t in 'rV['F_2]_n)
  if t \in kernel H then W ``(y | t) else 0); last first.
  rewrite big_distrl /=.
  apply eq_bigr => /= t Ht.
  case: ifP => HtH.
    rewrite fdist_post_probE fdist_uniform_supp_in ?inE //.
    have HH : (#|[set cw in kernel H]|%:R)%mcR != 0 :> R.
      (* the following three lines amount to INR_eq0 *)
      have->: 0 = GRing.natmul 1 0 by [].
      apply/eqP => /mulrIn /eqP.
      rewrite -unitfE unitr1 => /(_ erefl); apply/negP.
      rewrite cards_eq0.
      by apply/set0Pn; exists t; rewrite inE.
    rewrite -(mulrC (W ``(y | t))) -[X in X = _]mulr1.
    rewrite -!mulrA.
    congr (_ * _).
    rewrite fdist_uniform_supp_restrict /= fdist_uniform_supp_distrr /=; last first.
    rewrite invrM; last 2 first.
      exact/invr_neq0.
      rewrite (eq_bigl (fun x => x \in [set cw in C])); last by move=> i; rewrite inE.
      by rewrite unitfE -not_receivable_prop_uniform receivableP.
    rewrite invrK [X in _ = _ * X]mulrAC mulVr ?mul1r ?coqRE ?mulVr //.
    by rewrite unitfE -not_receivable_prop_uniform receivableP.
  rewrite fdist_post_probE fdist_uniform_supp_notin; last by rewrite inE; exact/negbT.
  by rewrite !mul0r.
rewrite -big_mkcond /=.
rewrite /alpha.
transitivity (W Zp0 (y ``_ n0) *
  (\sum_(ta = df `[ n0 := Zp0 ] [~ setT :\ n0])
    \prod_(m1 in 'F n0)
      (W ``(y \# 'V(m1, n0) :\ n0 | ta \# 'V(m1, n0) :\ n0) *
      (\prod_(m2 in 'F(m1, n0)) (\delta ('V m2) ta)%:R))) +
  W Zp1 (y ``_ n0) *
  (\sum_(ta = df `[ n0 := Zp1 ] [~ setT :\ n0])
    \prod_(m1 in 'F n0)
      (W ``(y \# 'V(m1, n0) :\ n0 | ta \# 'V(m1, n0) :\ n0) *
      (\prod_(m2 in 'F(m1, n0)) (\delta ('V m2) ta)%:R)))).
  congr (_ * _ + _ * _).
    rewrite (rmul_rsum_commute0 (Tanner.connected tanner) (Tanner.acyclic tanner) y
             (fun m x y => W ``(x | y))) // => m1 m0 t Hm1 tdf.
    by rewrite checksubsum_dprojs_V.
  rewrite (rmul_rsum_commute0 (Tanner.connected tanner) (Tanner.acyclic tanner) y
           (fun m x y => W ``(x | y))) // => m1 m0 t Hm1 tdf.
  by rewrite checksubsum_dprojs_V.
transitivity (\sum_(ta : 'rV_n) W (ta ``_ n0) (y ``_ n0) *
    \prod_(m1 in 'F n0)
      (W ``(y \# 'V(m1, n0) :\ n0 | ta \# 'V(m1, n0) :\ n0) *
        (\prod_(m2 in 'F(m1, n0)) (\delta ('V m2) ta)%:R))).
  rewrite big_distrr big_distrr /=.
  rewrite [in X in _ = X] (bigID [pred x : 'rV_n | x ``_ n0 == Zp0]) /=.
  congr (_ + _).
  + rewrite (eq_bigl [pred x : 'rV_n | x ``_ n0 == Zp0]) /=.
      by apply eq_bigr => ta /eqP ->.
    move=> ta /=.
    by rewrite -freeon_all mxE eqxx.
  + rewrite (eq_bigl [pred x : 'rV_n | x ``_ n0 != Zp0]) /=.
      apply eq_bigr => ta.
      by rewrite -F2_eq1 => /eqP ->.
    move=> v /=; by rewrite -freeon_all mxE eqxx F2_eq1.
transitivity (\sum_(ta : 'rV_n) W (ta ``_ n0) (y ``_ n0) *
    (\prod_(m1 in 'F n0) W ``(y \# 'V(m1, n0) :\ n0 | ta \# 'V(m1, n0) :\ n0)) *
    (\prod_(m1 in 'F n0) (\prod_(m2 in 'F(m1, n0)) (\delta ('V m2) ta)%:R))).
  apply eq_bigr => ta _.
  rewrite -mulrA.
  congr (_ * _).
  by rewrite big_split.
transitivity (\sum_(ta : 'rV_n)
    (\prod_(k < n)  W (ta ``_ k) (y ``_ k)) *
    (\prod_(m1 in 'F n0) \prod_(m2 in 'F(m1, n0)) (\delta ('V m2) ta)%:R)).
  apply eq_bigr => t /= _.
  congr (_ * _).
  rewrite -DMC_sub_vec_Fnext // (bigID (pred1 n0)) /= (big_pred1 n0) //.
  congr (_ * _).
  rewrite DMC_sub_vecE.
  apply eq_bigl => ? /=.
  by rewrite in_setC in_set1.
(* 4 -> 5 *)
transitivity (\sum_(ta : 'rV_n) (\prod_(k < n) (W ta ``_ k) y ``_ k) *
  (\prod_(m2 < m) (\delta ('V m2) ta)%:R)).
  apply eq_bigr => t /= _.
  congr (_ * _).
  by rewrite -(rprod_Fgraph_part_fnode (Tanner.connected tanner) (Tanner.acyclic tanner) (fun m0 => (\delta ('V m0) t)%:R)).
rewrite [in X in X = _](bigID [pred x | x \in kernel H])
  /=.
rewrite addrC (eq_bigr (fun=> 0)); last first.
  by move=> ta /negbTE Hta; rewrite checksubsum_in_kernel Hta mulr0.
rewrite big_const iter_addr mul0rn !add0r.
apply eq_bigr => ta Ha.
by rewrite checksubsum_in_kernel Ha mulr1 -DMCE.
Qed.

Local Notation "'beta'" := (beta H W y).

Lemma filter_out_set0 m0 t (g : 'I_m -> 'rV['F_2]_n -> R) (s : {set 'I_n}) :
  \prod_(A in [set \bigcup_(m1 in 'F n1 :\ m0) 'F( m1, n1) | n1 in s])
     \prod_(x in A) (g x t) =
  \prod_(A in [set \bigcup_(m1 in 'F n1 :\ m0) 'F( m1, n1)
                 | n1 in [set n1 in s | 'F n1 :\ m0 != set0]])
     \prod_(x in A) (g x t).
Proof.
rewrite (bigID [pred x | x == set0]) /= big1 ?mul1r; last first.
  move=> ms.
  case/andP => _ /eqP ->; by rewrite big_set0.
apply: eq_bigl => /= ms.
apply/esym/imsetP.
case: ifPn.
  case/andP => /imsetP[n1 Hn1 Hms Hms'].
  exists n1 => //.
  rewrite inE Hn1 /=.
  apply: contra Hms'.
  rewrite Hms => /eqP ->.
  by rewrite big_set0.
rewrite negb_and negbK.
case/orP => [|/eqP ->].
  move/imsetP => abs abs'; apply abs => {abs}.
  case: abs' => n1; rewrite inE =>/andP[abs'1 abs'2] abs''.
  by exists n1.
case=> n1.
rewrite inE.
case/andP => H1 H2 /esym/eqP/bigcup_succ_set0.
by apply/negP.
Qed.

Lemma recursive_computation_helper m0 n0 d : n0 \in 'V m0 ->
  forall x : 'rV_n, freeon ('V m0 :\ n0) d x ->
  let A := \sum_(i | freeon ('V( m0, n0) :\ n0) d i &&
                          (dproj d ('V m0 :\ n0) i == x))
          \prod_(n1 < n | n1 \in 'V m0 :\ n0)
             ((W i ``_ n1) y ``_ n1 *
             (\prod_(m1 < m | m1 \in 'F n1 :\ m0)
                 (W ``((y \# 'V( m1, n1) :\ n1) | (i \# 'V( m1, n1) :\ n1)) *
                 (\prod_(m2 < m | m2 \in 'F( m1, n1)) (\delta ('V m2) i)%:R)))) in
  A = \prod_(n1 < n | n1 \in 'V m0 :\ n0) beta n1 m0 x.
 Proof.
move=> m0n0 x Hx A; apply/esym.
transitivity (\prod_(n1 in 'V m0 :\ n0) ((W x ``_ n1) y ``_ n1 *
  (\sum_(z | (dprojs_V H x n1 z \in
      pfamily x ('F n1 :\ m0) (fun m1 => freeon ('V( m1, n1) :\ n1) x)) &&
      (comb_V H x n1 (dprojs_V H x n1 z) == z))
    \prod_(m1 in 'F n1 :\ m0)
      (W ``((y \# 'V( m1, n1) :\ n1) | ((dprojs_V H x n1 z) m1 \# 'V( m1, n1) :\ n1)) *
        (\prod_(m2 in 'F( m1, n1)) (\delta ('V m2) ((dprojs_V H x n1 z) m1))%:R))))).
  apply eq_bigr => n1 Hn1.
  congr (_ * _)%R.
  rewrite {1}(big_distr_big_dep x) /=.
  rewrite (reindex_onto (dprojs_V H x n1) (comb_V H x n1)) //.
  rewrite /= => g Hg.
  exact: (@dprojs_comb_V _ _ _ (Tanner.acyclic tanner) _ _ (fun x => 'F x :\ m0) _ Hg).
transitivity (\prod_(n1 in 'V m0 :\ n0)
   \sum_(z | (dprojs_V H x n1 z \in
      pfamily x ('F n1 :\ m0) (fun m1 => freeon ('V( m1, n1) :\ n1) x)) &&
      (comb_V H x n1 (dprojs_V H x n1 z) == z))
    (W z ``_ n1) y ``_ n1 *
    (\prod_(m1 in 'F n1 :\ m0)
        (W ``((y \# 'V( m1, n1) :\ n1) | ((dprojs_V H x n1 z) m1 \# 'V( m1, n1) :\ n1)) *
         (\prod_(m2 in 'F( m1, n1)) (\delta ('V m2) ((dprojs_V H x n1 z) m1))%:R)))).
  apply/esym.
  apply eq_bigr => /= n1 Hn1.
  rewrite [RHS]big_distrr /=.
  apply eq_bigr => /= t' Ht'.
  congr (W _ _ * _)%R.
  case/andP : Ht' => X1 X2.
  move/eqP : X2 => <-.
  rewrite comb_dprojs_V_not_in_partition // => m1; by rewrite !inE eqxx.
transitivity (\sum_(t | (dprojs_V2 H x m0 n0 t \in
  pfamily x ('V m0 :\ n0) (fun n1 => [pred t0 |
    (dprojs_V H x n1 t0 \in pfamily x ('F n1 :\ m0) (fun m1 => freeon ('V( m1, n1) :\ n1) x)) &&
    (comb_V H x n1 (dprojs_V H x n1 t0) == t0)])) &&
                         (comb_V2 H x m0 n0 (dprojs_V2 H x m0 n0 t) == t))
    \prod_(n1 < n | n1 \in 'V m0 :\ n0)
      (W (((dprojs_V2 H x m0 n0 t) n1) ``_ n1) y ``_ n1 *
      (\prod_(m1 < m | m1 \in 'F n1 :\ m0)
        (W ``((y \# 'V( m1, n1) :\ n1) | ((dprojs_V H x n1 ((dprojs_V2 H x m0 n0 t) n1)) m1 \# 'V( m1, n1) :\ n1)) *
        (\prod_(m2 < m | m2 \in 'F( m1, n1))
          (\delta ('V m2) ((dprojs_V H x n1 ((dprojs_V2 H x m0 n0 t) n1)) m1))%:R))))).
  apply/esym.
  by rewrite [in RHS](rprod_rsum_commute (Tanner.acyclic tanner)).
apply/eq_big.
  move=> t' /=.
  move Hlhs : (_ && _) => [|].
    apply/esym.
    case/andP : Hlhs => Hlhs1 Hlhs2.
    apply/andP; split.
      apply: (@comb_V2_freeon _ _ _ (Tanner.acyclic tanner) x _ _ m0n0) => //.
      by rewrite freeon_sym.
      by apply/eqP.
    apply (dproj_prop (Tanner.acyclic tanner) (simple_tanner_rel _)) => //; by apply/eqP.
  apply/esym/negbTE.
  move/negbT : Hlhs; apply: contra => /andP [] Hlhs1 Hlhs1'.
  apply/andP; split.
    apply: (@dprojs_V2_pfamily _ _ _ (Tanner.acyclic tanner) (Tanner.connected tanner) _ _ _ m0n0 _ d) => //.
    by apply/eqP.
  apply: (@comb_dprojs_V2 _ _ _ (Tanner.acyclic tanner) _ _ _ m0n0 d) =>//; by apply/eqP.
move=> t Ht.
apply eq_bigr => n1 Hn1.
congr (W _ _ * _).
  rewrite (dprojs_V2_in (Tanner.acyclic tanner) (simple_tanner_rel _)) //.
  by case/andP : Ht => _ /eqP.
apply eq_bigr => m1 Hm1.
rewrite /dprojs_V sub_vec_dprojs // sub_vec_dprojs_V2 //.
congr (_ * _).
apply eq_bigr => m2 Hm2.
congr (_%:R).
case/andP : Ht.
by move/checksubsum_dprojs_V2 => ->.
Qed.

Lemma recursive_computation m0 n0 d : n0 \in 'V m0 ->
  alpha m0 n0 d = \sum_(x = d [~'V m0 :\ n0])
    (\delta ('V m0) x)%:R * \prod_(n1 in 'V m0 :\ n0) beta n1 m0 x.
Proof.
move=> m0n0.
transitivity (\sum_(x = d [~'V(m0, n0) :\ n0])
    (\delta ('V m0) x)%:R *
      W ``(y \# 'V(m0, n0) :\ n0 | x \# 'V(m0, n0) :\ n0) * \prod_(n1 in 'V m0 :\ n0) \prod_(m1 in 'F n1 :\ m0) \prod_(m2 in 'F(m1, n1))
         (\delta ('V m2) x)%:R).
  (* get W(tb|t) out of beta *)
  rewrite /alpha.
  apply eq_bigr => /= t Ht.
  rewrite -[in X in _ = X]mulrA -[in X in _ = X]mulrC -[in X in _ = X]mulrA.
  congr (_ * _)%R.
  rewrite (bigD1 m0) /=; last by apply Fgraph_m0.
  rewrite mulrC; congr (_ * _)%R.
  transitivity (\prod_(i in 'F(m0, n0) :\ m0) (\delta ('V i) t)%:R : R).
    apply eq_bigl => /= m1.
    by rewrite 2![in X in _ = X]inE andbC.
  rewrite -(cover_Fgraph_part_Fgraph (Tanner.acyclic tanner)) //.
  rewrite big_trivIset /=; last first.
    by apply (@trivIset_Fgraph_part_Fgraph _ _ _ (Tanner.acyclic tanner)).
  rewrite /Fgraph_part_Fgraph.
  rewrite (filter_out_set0 _ _ (fun x t => (\delta ('V x) t)%:R)).
  rewrite big_imset /=; last first.
    move=> n1 /= n2 Hn1 Hn2 n1xn2x.
    rewrite inE in Hn1; case/andP : Hn1 => Hn1 H1.
    rewrite inE in Hn2; case/andP : Hn2 => Hn2 H2.
    by apply: (another_Fgraph_injective (Tanner.acyclic tanner) Hn1 Hn2 H1).
  transitivity (\prod_(n1 < n | (n1 \in 'V m0 :\ n0) && ('F n1 :\ m0 != set0))
      \prod_(m1 in 'F n1 :\ m0)
         \prod_(m2 in 'F(m1, n1)) (\delta ('V m2) t)%:R :> R); last first.
    rewrite [in RHS](bigID [pred x | 'F x :\ m0 == set0]) /= [in RHS]big1 ?mul1r //.
    move=> n1 /andP [] H1 /eqP ->; by rewrite !big_set0.
  apply eq_big => /= n1; first by rewrite !inE.
  move=> Hn1.
  rewrite big_bigcup_partition //= => m1 m2 m1m2.
  apply: contraNT m1m2.
  rewrite -setI_eq0 => /set0Pn[m3]; rewrite inE => /andP[H1 H2].
  by apply/eqP/(Fgraph_disjoint (Tanner.acyclic tanner) H1 H2).
transitivity (\sum_(x = d [~'V(m0, n0) :\ n0])
  (\delta ('V m0) x)%:R *
    \prod_(n1 in 'V m0 :\ n0) (W `(y ``_ n1 | x ``_ n1) *
    \prod_(m1 in 'F n1 :\ m0)
     ((W ``(y \# 'V(m1, n1) :\ n1 | x \# 'V(m1, n1) :\ n1))
      * \prod_(m2 in 'F(m1, n1)) (\delta ('V m2) x)%:R))).
  apply eq_bigr => /= t Ht.
  rewrite -mulrA; congr (_ * _).
  rewrite DMC_sub_vec_Vgraph // -big_split /=.
  apply eq_bigr => /= n1 _.
  by rewrite -mulrA big_split.
transitivity (\sum_(x = d [~('V m0) :\ n0])
  \sum_(x' = d [~'V(m0, n0) :\ n0] | [pred x' | dproj d ('V m0 :\ n0) x' == x])
    (\delta ('V m0) x')%:R *
    \prod_(n1 in 'V m0 :\ n0)
      (W (x' ``_ n1) (y ``_ n1) *
      (\prod_(m1 in 'F n1 :\ m0)
          (W ``(y \# 'V(m1, n1) :\ n1 | x' \# 'V(m1, n1) :\ n1) *
          (\prod_(m2 in 'F(m1, n1)) (\delta ('V m2) x')%:R))))).
  apply partition_big => /= t _.
  by apply freeon_dproj.
apply eq_bigr => /= x Hx.
transitivity
 (\sum_(x' = d [~'V(m0, n0) :\ n0] | [pred x' | dproj d ('V m0 :\ n0) x' == x])
  (\delta ('V m0) x)%:R *
  (\prod_(n1 in 'V m0 :\ n0) (W (x' ``_ n1) y ``_ n1 *
    (\prod_(m1 in 'F n1 :\ m0)
      (W ``(y \# 'V(m1, n1) :\ n1 | x' \# 'V(m1, n1) :\ n1) *
        (\prod_(m2 in 'F(m1, n1)) (\delta ('V m2) x')%:R)))))).
  apply eq_bigr => /= x' Hx'.
  congr (_%:R * _)%R.
  case/andP : Hx' => H1 /eqP <-.
  by rewrite checksubsum_dprojD1 // (freeon_notin H1) // !inE eqxx.
by rewrite -big_distrr /= recursive_computation_helper.
Qed.

(* some properties of alpha and beta messages: *)
Lemma beta_one_successor n1 m1 d :
  'F n1 = [set m1] -> beta n1 m1 d = W (d ``_ n1) (y ``_ n1).
Proof.
move=> Fn1.
rewrite /beta -[X in _ = X]mulr1.
congr (_ * _).
set g := BIG_F.
transitivity (\prod_(i in set0) g i).
  apply eq_bigl => /= m2.
  rewrite Fn1 in_setD1 in_set1 in_set0.
  by case: (m2 == m1).
by rewrite big_set0.
Qed.

Lemma alpha_one_successor n1 m1 d :
  'V m1 = [set n1] -> alpha m1 n1 d = (~~ (bool_of_F2 (d ``_ n1)))%:R.
Proof.
move=> Vm1.
rewrite recursive_computation; last first.
  by rewrite Vm1 in_set1.
rewrite Vm1.
rewrite -{1}(setU0 [set n1]) setU1K; last by rewrite in_set0.
rewrite rsum_freeon0.
rewrite -[X in _ = X]mulr1 checksubsum_set1; congr (_ * _).
rewrite big_pred0 // => /= n2.
by rewrite in_setD1 in_set1 andNb.
Qed.

Lemma alpha_two_successors n1 n2 m1 d : n1 != n2 ->
  'V m1 = [set n1; n2] -> alpha m1 n1 d = beta n2 m1 (d `[ n2 := d ``_ n1 ]).
Proof.
move=> n1n2 Hm1.
rewrite recursive_computation; last by rewrite Hm1 in_setU in_set1 eqxx.
rewrite Hm1 (_ : [set n1; n2] :\ n1 = [set n2]); last by rewrite setU1K // in_set1.
rewrite rsum_freeon1 2!big_set1.
do 2 rewrite checksubsum_set2 //.
rewrite [in X in X%:R]/row_set !mxE (negbTE n1n2) eqxx.
have [->|] := eqVneq (d ``_ n1) Zp0.
  by rewrite mul1r /= mul0r addr0.
rewrite mul0r add0r -F2_eq1 => /eqP ->.
by rewrite eqxx mul1r.
Qed.

End sum_prod_correctness.

Section ldpc_approx_algo.
Let R := Rdefinitions.R.
Variables (m n : nat) (H : 'M['F_2]_(m, n)).
Variables (B : finType) (W : `Ch('F_2, B)).
Variable y : n.-tuple B.

Local Notation "''F'" := (Fnext H).
Local Notation "''V'" := (Vnext H).

Import GRing.
Local Open Scope ring_scope.

Local Open Scope tuple_ext_scope.

Definition sumproduct_init : 'M[R]_(m, n) * 'M[R]_(m, n) :=
  let init (x : 'F_2) := \matrix_(m0 < m, n0 < n) W `(y !_ n0 | x) in
  (init 0, init 1).

Definition alpha_fun (m0 : 'I_m) (n0 : 'I_n) (beta : 'M[R]_(m, n) * 'M[R]_(m, n))
  (x : 'F_2) : R :=
  \sum_(t = \row_(i < n) (0 : 'F_2) [~'V m0 :\ n0])
   ((\delta ('V m0) t)%:R *
    \prod_(n1 in 'V m0 :\ n0) if t ``_ n1 == Zp0 then beta.1 m0 n1 else beta.2 m0 n1)%R.

Definition beta_fun (m0 : 'I_m) (n0 : 'I_n) (x : 'F_2) (alpha : 'M[R]_(m, n)) : R :=
  (W `(y !_ n0 | x) * \prod_(m1 in 'F n0 :\ m0) alpha m1 n0)%R.

Fixpoint sumproduct_loop (lmax : nat) (beta0 beta1 : 'M_(m, n)) : option ('rV['F_2]_n) :=
  match lmax with
    | O => None (* Symbol "?" *)
    | lmax'.+1 =>
      let nalpha m0 n0 x :=
        let K := (alpha_fun m0 n0 (beta0, beta1) 0 + alpha_fun m0 n0 (beta0, beta1) 1)^-1 in
        (K * alpha_fun m0 n0 (beta0, beta1) x)%R
      in
      let alpha0 : 'M_(m, n) := \matrix_(m0 < m, n0 < n) nalpha m0 n0 0 in
      let alpha1 : 'M_(m, n) := \matrix_(m0 < m, n0 < n) nalpha m0 n0 1 in
      let nbeta m0 n0 x alpha :=
        let K := (beta_fun m0 n0 Zp0 alpha + beta_fun m0 n0 Zp1 alpha)^-1 in
        (K * beta_fun m0 n0 x alpha)%R in
      let beta0 := \matrix_(m0 < m, n0 < n) nbeta m0 n0 0 alpha0 in
      let beta1 := \matrix_(m0 < m, n0 < n) nbeta m0 n0 1 alpha1 in
      let estimation x n0 alpha := (W x (y !_ n0) * \prod_(m1 in 'F n0) alpha m1 n0)%R in
      let gamma0 n0 := estimation Zp0 n0 alpha0 in
      let gamma1 n0 := estimation Zp1 n0 alpha1 in
      let chat := \matrix_(i < 1, n0 < n) if (gamma0 n0 >= gamma1 n0)%mcR then 0 else 1 in
      if H *m chat^T == 0 then
        Some chat
      else
        sumproduct_loop lmax' beta0 beta1
  end.

Definition sumproduct (lmax : nat) : option ('rV['F_2]_n) :=
  let beta_init := sumproduct_init in
  sumproduct_loop lmax beta_init.1 beta_init.2.

End ldpc_approx_algo.
