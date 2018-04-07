(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg perm zmodp matrix vector.
Require Import Reals Fourier.
Require Import Rssr Reals_ext ssr_ext ssralg_ext Rbigop f2 proba.
Require Import channel_code channel binary_symmetric_channel hamming pproba.

(** * The variety of decoders *)

(** OUTLINE:
- Section minimum_distance_decoding.
- Section bounded_distance_decoding.
- Section maximum_likelihood_decoding.
- Section maximum_likelihood_decoding_prop.
- Section MD_ML_decoding.
- Section MAP_decoding.
- Section MAP_decoding_prop.
- Section MPM_condition.
*)

Reserved Notation "t .-BDD f" (at level 2, format "t  .-BDD  f").

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Close Scope R_scope.
Import GRing.Theory.
Local Open Scope ring_scope.

Definition repairT (B A : finType) n := {ffun 'rV[B]_n -> option 'rV[A]_n}.

Definition oimg (A B : finType) (f : A -> option B) : {set B} :=
  [set b | [exists a, f a == Some b]].

Definition discardT (A : finType) n (M : finType) := 'rV[A]_n -> M.

Definition cancel_on n (F : finFieldType) (C : {vspace 'rV[F]_n}) {B} (e : B -> _) s :=
  forall c, c \in C -> e (s c) = c.

Lemma vspace_not_empty (F : finFieldType) n (C : {vspace 'rV[F]_n}) :
  0 < #| [set cw in C] |.
Proof. apply/card_gt0P; exists 0; by rewrite inE mem0v. Qed.

Section minimum_distance_decoding.

Variables (F : finFieldType) (n : nat) (C : {set 'rV[F]_n}).
Variable f : repairT F F n.

Local Open Scope nat_scope.

Definition MD_decoding :=
  forall y x, f y = Some x -> forall x', x' \in C -> dH x y <= dH x' y.

Local Close Scope nat_scope.

Local Open Scope min_scope.

Hypothesis c_not_empty : {c0 | c0 \in C}.

Definition MD_decoding_alt :=
  forall y x, f y = Some x ->
    dH y x = \min^ (sval c_not_empty) _(x' in C) dH y x'.

Variable f_img : oimg f \subset C.

Lemma MD_decoding_equiv : MD_decoding_alt <-> MD_decoding.
Proof.
split => [H /= y x yx x' x'C | H /= y x yx].
- move: {H}(H _ _ yx) => H.
  rewrite dH_sym H dH_sym.
  case: arg_minP; first by case: c_not_empty.
  move=> /= i ic ij; by rewrite dH_sym (dH_sym x') ij.
- move: {H}(H _ _ yx) => H.
  case: arg_minP; first by case: c_not_empty.
  move=> /= i Hi /(_ x) Ki.
  apply/eqP; rewrite eqn_leq; apply/andP; split.
  - by rewrite dH_sym (dH_sym y) H.
  - apply/Ki; move/subsetP: f_img; apply; rewrite inE.
    by apply/existsP; exists y; apply/eqP.
Qed.

End minimum_distance_decoding.

Section bounded_distance_decoding.

Variables (F : finFieldType) (n : nat) (C : {vspace 'rV[F]_n}).
Variable (f : repairT F F n).

Definition BD_decoding t :=
  forall c e, c \in C -> wH e <= t -> f (c + e) = Some c.

End bounded_distance_decoding.

Notation "t .-BDD f" := (BD_decoding (fst f) (snd f) t) : ecc_scope.

Local Open Scope proba_scope.
Local Open Scope channel_scope.

Section maximum_likelihood_decoding.

Variables (A : finFieldType) (B : finType) (W : `Ch_1(A, B)).
Variables (n : nat) (C : {vspace 'rV[A]_n}).
Variable f : decT B [finType of 'rV[A]_n] n.
Variable P : {dist 'rV[A]_n}.

Local Open Scope R_scope.

Definition ML_decoding :=
  forall y, receivable W P y ->
  exists x, f y = Some x /\
    W ``(y | x) = \rmax_(x' in C) W ``(y | x').

End maximum_likelihood_decoding.

Local Open Scope R_scope.

Section maximum_likelihood_decoding_prop.

Variables (A : finFieldType) (B : finType) (W : `Ch_1(A, B)).
Variables (n : nat) (C : {vspace 'rV[A]_n}).
Variable repair : decT B [finType of 'rV[A]_n] n.
Let P := UniformSupport.d (vspace_not_empty C).
Hypothesis ML_dec : ML_decoding W C repair P.

Local Open Scope channel_code_scope.

Lemma ML_err_rate x1 x2 y : repair y = Some x1 ->
  x2 \in C -> W ``(y | x2) <= W ``(y | x1).
Proof.
move=> Hx1 Hx2.
case/boolP : (W ``(y | x2) == 0%R) => [/eqP ->| Hcase].
  by apply DMC_nonneg.
have : receivable W P y.
  apply/existsP; exists x2.
  by rewrite Hcase andbT UniformSupport.neq0 inE.
case/(ML_dec (y := y)) => x' [].
rewrite Hx1 => -[<-] ->.
rewrite -big_filter.
apply (Rle_bigRmax (fun i => W ``(y | i))).
by rewrite mem_filter /= mem_index_enum andbT.
Qed.

Variable M : finType.
Hypothesis M_not_0 : (0 < #|M|)%nat.
Variable discard : discardT A n M.
Variable enc : encT A M n.
Hypothesis enc_img : enc @: M \subset C.
Hypothesis discard_cancel : forall y x, repair y = Some x -> enc (discard x) = x.

Lemma ML_smallest_err_rate phi :
  let dec := [ffun x => omap discard (repair x)] in
  echa(W, mkCode enc phi) >=
  echa(W, mkCode enc dec).
Proof.
move=> dec.
apply Rmult_ge_compat_l.
  apply/Rle_ge/mulR_ge0 => //; exact/ltRW/invR_gt0/lt_0_INR/ltP.
rewrite /ErrRateCond /=.
apply (@Rge_trans _ (\rsum_(m in M) (1 - Pr (W ``(|enc m)) [set tb | phi tb == Some m]))).
  apply Req_ge, eq_bigr => m _.
  rewrite Pr_to_cplt.
  set lhs := ~: _. set rhs := [set _ | _].
  suff -> : lhs = rhs by done.
  apply/setP => t; by rewrite !inE negbK.
apply (@Rge_trans _ (\rsum_(m in M) (1 - Pr (W ``(|enc m)) [set tb | dec tb == Some m]))); last first.
  apply Req_ge, eq_bigr => m _.
  rewrite [in X in _ = X]Pr_to_cplt.
  set lhs := ~: _. set rhs := [set _ | _].
  suff -> : lhs = rhs by done.
  apply/setP => t; by rewrite !inE negbK.
rewrite 2!big_split /=.
apply Rplus_ge_compat_l.
rewrite -2!(big_morph _ morph_Ropp oppR0).
apply Ropp_le_ge_contravar.
rewrite /Pr (exchange_big_dep xpredT) //= [in X in (_ <= X)%R](exchange_big_dep xpredT) //=.
apply ler_rsum => /= tb _.
apply (@Rle_trans _ (\rsum_(m| phi tb == Some m) (W ``(tb | enc m)))).
  apply Req_le, eq_bigl => m; by rewrite inE.
apply (@Rle_trans _ (\rsum_(m| dec tb == Some m) (W ``(tb | enc m)))); last first.
  apply Req_le, eq_bigl => m; by rewrite inE.
(* show that phi_ML succeeds more often than phi *)
case/boolP : (dec tb == None) => dectb.
  case/boolP: (receivable W P tb) => [ | Htb].
    case/ML_dec => m'.
      case=> Htmp.
      move: dectb.
      by rewrite {1}/dec {1}ffunE Htmp.
  have Htb' m : W ``(tb | enc m) = 0%R.
    apply/eqP; apply/contraR : Htb => Htb.
    apply/existsP; exists (enc m).
    rewrite Htb andbT UniformSupport.neq0 inE.
    move/subsetP : enc_img; apply.
    apply/imsetP; by exists m.
  rewrite (eq_bigr (fun=> 0)); last by move=> m _; rewrite Htb'.
  rewrite big_const iter_Rplus mulR0.
  apply rsumr_ge0 => ? _; exact/DMC_nonneg.
case/boolP : (phi tb == None) => [|phi_tb].
  move/eqP => ->.
  rewrite big_pred0 //; apply rsumr_ge0 => ? _; exact/DMC_nonneg.
have [m1 Hm1] : exists m', dec tb = Some m'.
  destruct (dec tb) => //; by exists s.
have [m2 Hm2] : exists m', phi tb = Some m'.
  destruct (phi tb) => //; by exists s.
rewrite Hm1 {}Hm2.
apply (@Rle_trans _ (\rsum_(m| m == m2) W ``(tb | enc m))).
  by apply Req_le, eq_bigl => m; rewrite eq_sym.
apply (@Rle_trans _ (\rsum_(m| m == m1) W ``(tb | enc m))); last first.
  by apply Req_le, eq_bigl => m; rewrite eq_sym.
rewrite 2!big_pred1_eq.
apply ML_err_rate.
  move: Hm1.
  rewrite /dec ffunE.
  rewrite /Option.map.
  rewrite /obind.
  rewrite /oapp.
  move H : (repair tb) => h.
  case: h H => // a Ha [<-]; congr Some.
  by rewrite (discard_cancel Ha).
move/subsetP : enc_img; apply.
apply/imsetP; by exists m2.
Qed.

End maximum_likelihood_decoding_prop.

Section MD_ML_decoding.

Variable p : R.
Hypothesis p_01 : 0 <= p <= 1.

(* TODO: move to file on bsc? *)
Lemma bsc_prob_prop n : p < 1 / 2 ->
  forall n1 n2 : nat, (n1 <= n2 <= n)%nat ->
  ((1 - p) ^ (n - n2) * p ^ n2 <= (1 - p) ^ (n - n1) * p ^ n1)%R.
Proof.
move=> p05 d1 d2 d1d2.
case/Rle_lt_or_eq_dec: (proj1 p_01) => [Hp | <-]; last first.
  destruct d2 as [|d2].
    destruct d1 as [|d1]; last by done.
    rewrite /=; by apply Rle_refl.
  rewrite !subR0 /= !mul0R !mulR0.
  destruct d1 as [|d1] => /=.
    rewrite subn0 mulR1 pow1; fourier.
  rewrite !mul0R !mulR0; by apply Rle_refl.
apply (Rmult_le_reg_l ((/ (1 - p) ^ (n - d2)) * (/ p ^ d1))%R).
  apply mulR_gt0; apply/invR_gt0/pow_lt => //; by fourier.
rewrite (mulRC ((1 - p) ^ (n - d2))) -!mulRA mulRC -!mulRA mulRV; last first.
  apply/pow_not0; rewrite subR_eq0; apply/eqP/gtR_eqF; fourier.
rewrite mulR1 -(mulRC (p ^ d1)) [in X in _ <= X]mulRC !mulRA mulVR ?mul1R; last first.
  exact/pow_not0/eqP/gtR_eqF.
rewrite -powRV; last by apply/eqP/gtR_eqF.
rewrite -powRV; last by rewrite subR_eq0; apply/eqP/gtR_eqF; fourier.
rewrite mulRC Rmult_pow_inv; last 2 first.
  move=> ?; fourier.
  by case/andP : d1d2.
rewrite Rmult_pow_inv; last 2 first.
  by move=> ?; fourier.
  apply: leq_sub2l; by case/andP : d1d2.
suff -> : (n - d1 - (n - d2) = d2 - d1)%nat.
  apply pow_incr; split; fourier.
rewrite -subnDA addnC subnDA subKn //.
by case/andP : d1d2.
Qed.

Let card_F2 : #| 'F_2 | = 2%nat. Proof. by rewrite card_Fp. Qed.
Let W := BSC.c card_F2 p_01.

Variables (n : nat) (C : {vspace 'rV['F_2]_n}).
Variable f : repairT [finType of 'F_2] [finType of 'F_2] n.
Variable f_img : oimg f \subset C.
Variable M : finType.
Variable discard : discardT [finType of 'F_2] n M.
Variable enc : encT [finType of 'F_2] M n.
Hypothesis compatible : cancel_on C enc discard.
Variable P : {dist 'rV['F_2]_n}.

Lemma MD_implies_ML : p < 1/2 -> MD_decoding [set cw in C] f ->
  (forall y, f y != None) -> ML_decoding W C f P.
Proof.
move=> p05 MD f_total y _ (* y_receivable *).
have codebook_not_empty : {c | c \in [set cw in C] }.
  move: (mem0v C); set x := (X in X \in C) => _.
  exists x; by rewrite inE mem0v.
have {MD}MD : MD_decoding_alt f codebook_not_empty.
  apply MD_decoding_equiv => //.
  apply/subsetP => y' Hy'.
  move/subsetP : f_img => /(_ _ Hy'); by rewrite inE.
move Hoc : (f y) => oc.
case: oc Hoc => [c|] Hc; last first.
  by move: (f_total y); rewrite Hc.
exists c; split; first by reflexivity.
(* replace  W ``^ n (y | f c) with a closed formula because it is a BSC *)
pose dH_y c := dH y c.
pose g : nat -> R := fun d : nat => (1 - p) ^ (n - d) * p ^ d.
have -> : W ``(y | c) = g (dH_y c).
  move: (DMC_BSC_prop p_01 enc (discard c) y).
  set cast_card := eq_ind_r _ _ _.
  rewrite (_ : cast_card = card_F2) //; last by apply eq_irrelevance.
  clear cast_card.
  rewrite -/W compatible //.
  move/subsetP : f_img; apply.
  rewrite inE; apply/existsP; by exists y; apply/eqP.
transitivity (\big[Rmax/R0]_(c in C) (g (dH_y c))); last first.
  apply eq_bigr => /= c' Hc'.
  move: (DMC_BSC_prop p_01 enc (discard c') y).
  set cast_card := eq_ind_r _ _ _.
  rewrite (_ : cast_card = card_F2) //; last by apply eq_irrelevance.
  by rewrite -/W compatible.
(* the function maxed over is decreasing so we may look for its minimizer,
   which is given by minimum distance decoding *)
rewrite (@big_rmax_bigminn_helper_vec _ _ _ _ _ _ _ _ _ _ codebook_not_empty) //.
- apply eq_bigl => /= i; by rewrite inE.
- by apply bsc_prob_prop.
- move=> r; rewrite /g.
  apply mulR_ge0; apply pow_le; [fourier | by case: p_01].
- rewrite inE; move/subsetP: f_img; apply.
  rewrite inE; apply/existsP; by exists y; apply/eqP.
- move=> ? _; by rewrite /dH_y max_dH.
- by rewrite /dH_y MD.
Qed.

End MD_ML_decoding.

Section MAP_decoding.

Variables (A : finFieldType) (B : finType) (W : `Ch_1(A, B)).
Variables (n : nat) (C : {vspace 'rV[A]_n}).
Variable dec : decT B [finType of 'rV[A]_n] n.
Variable P : {dist 'rV[A]_n}.

Definition MAP_decoding := forall y (Hy : receivable W P y),
  exists m, dec y = Some m /\
    P `^^ W , Hy (m | y) = \rmax_(m in C) (P `^^ W , Hy (m | y)).

End MAP_decoding.

Section MAP_decoding_prop.

Variables (A : finFieldType) (B : finType) (W : `Ch_1(A, B)).
Variables (n : nat) (C : {vspace 'rV[A]_n}).
Variable dec : decT B [finType of 'rV[A]_n] n.
Variable dec_img : oimg dec \subset C.
Let P := UniformSupport.d (vspace_not_empty C).

Lemma MAP_implies_ML : MAP_decoding W C dec P -> ML_decoding W C dec P.
Proof.
move=> HMAP.
rewrite /ML_decoding => /= tb Htb.
have Hunpos : INR 1 / INR #| [set cw in C] | > 0.
  rewrite div1R; by apply/invR_gt0/lt_0_INR/ltP/vspace_not_empty.
move: (HMAP _ Htb) => H.
rewrite /PosteriorProbability.d in H.
unlock in H.
simpl in H.
set tmp := \rmax_(_ <- _ | _) _ in H.
rewrite /tmp -rmax_distrl in H; last first.
  apply/ltRW/invR_gt0/RltP; rewrite ltR_neqAle; apply/andP; split; last first.
    exact/RleP/PosteriorProbability.den_nonneg.
  by rewrite eq_sym -receivableE.
rewrite /P /UniformSupport.d /UniformSupport.f /= in H.
case: H => [m' [Hm' H]].
set r := index_enum _ in H.
rewrite (eq_bigr (fun i => 1 / INR #|[set cw in C]| * W ``(tb | i))) in H; last first.
  move=> i iC; by rewrite UniformSupport.E // inE.
rewrite -rmax_distrr in H; last exact/ltRW/Hunpos.
exists m'; split.
  exact Hm'.
apply Rmult_eq_reg_r in H; last by apply/eqP/invR_neq0; rewrite -receivableE.
rewrite /= UniformSupport.E ?inE // in H; last first.
  move/subsetP : dec_img; apply.
  rewrite inE; apply/existsP; by exists tb; apply/eqP.
move/Rmult_eq_reg_l : H => -> //; exact: gtR_eqF.
Qed.

End MAP_decoding_prop.

Section MPM_condition.

(* in the special case of a binary code... *)
Variable W : `Ch_1('F_2, [finType of 'F_2]).
Variable n : nat.
Variable C : {vspace 'rV['F_2]_n}.
Hypothesis C_not_empty : (0 < #|[set cw in C]|)%nat.
Variable m : nat.
Variable enc : encT [finFieldType of 'F_2] [finType of 'rV['F_2]_(n - m)] n.
Variable dec : decT [finFieldType of 'F_2] [finType of 'rV['F_2]_(n - m)] n.

Local Open Scope vec_ext_scope.

Definition MPM_condition := let P := `U C_not_empty in
  forall y (Hy : receivable W P y),
  forall x, dec y = Some x ->
  forall n0,
    P '_ n0 `^^ W , Hy ((enc x) ``_ n0 | y) = \rmax_(b in 'F_2) P '_ n0 `^^ W , Hy (b | y).

End MPM_condition.
