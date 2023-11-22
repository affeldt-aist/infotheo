(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum fingroup finalg perm.
From mathcomp Require Import zmodp matrix vector order.
From mathcomp Require Import lra mathcomp_extra Rstruct reals.
From mathcomp Require ssrnum.
Require Import Reals.
Require Import ssrR realType_ext Reals_ext ssr_ext ssralg_ext Rbigop f2 fdist.
Require Import proba.
Require Import channel_code channel binary_symmetric_channel hamming pproba.

(******************************************************************************)
(*                      The variety of decoders                               *)
(*                                                                            *)
(* MD_decoding  == minimum distance decoding (a.k.a. nearest neighbor         *)
(*                 decoding)                                                  *)
(* BD_decoding  == bounded-distance decoding                                  *)
(*                 Notation: t .-BDD f                                        *)
(* ML_decoding  == maximum likelihood decoding                                *)
(* MAP_decoding == maximum aposteriori decoding                               *)
(* MPM_decoding == maximum posterior marginal decoding                        *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*   MD_implies_ML  == MD decoding implies ML decoding of a BSC with p < 1/2  *)
(*   MAP_implies_ML == MAP decoding implies ML decoding                       *)
(******************************************************************************)

Reserved Notation "t .-BDD f" (at level 2, format "t  .-BDD  f").

Declare Scope ecc_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Close Scope R_scope.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Definition repairT (B A : finType) n := {ffun 'rV[B]_n -> option 'rV[A]_n}.

Definition oimg (A B : finType) (f : A -> option B) : {set B} :=
  [set b | [exists a, f a == Some b]].

Definition discardT (A : finType) n (M : finType) := 'rV[A]_n -> M.

Definition cancel_on n (F : finFieldType) (C : {vspace 'rV[F]_n}) {B} (e : B -> _) s :=
  forall c, c \in C -> e (s c) = c.

Lemma vspace_not_empty (F : finFieldType) n (C : {vspace 'rV[F]_n}) :
  (0 < #| [set cw in C] |)%nat.
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
  case: arg_minnP; first by case: c_not_empty.
  move=> /= i ic ij; by rewrite dH_sym (dH_sym x') ij.
- move: {H}(H _ _ yx) => H.
  case: arg_minnP; first by case: c_not_empty.
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
  forall c e, c \in C -> (wH e <= t)%nat -> f (c + e) = Some c.

End bounded_distance_decoding.

Notation "t .-BDD f" := (BD_decoding (fst f) (snd f) t) : ecc_scope.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope channel_scope.

Local Open Scope reals_ext_scope.
Local Open Scope order_scope.

Section maximum_likelihood_decoding.

Variables (A : finFieldType) (B : finType) (W : `Ch(A, B)).
Variables (n : nat) (C : {vspace 'rV[A]_n}).
Variable f : decT B [finType of 'rV[A]_n] n.
Variable P : {fdist 'rV[A]_n}.

Local Open Scope reals_ext_scope.

Definition ML_decoding :=
  forall y : P.-receivable W,
  exists x, f y = Some x /\
    W ``(y | x) = \big[Order.max/0]_(x' in C) W ``(y | x').

End maximum_likelihood_decoding.

Section maximum_likelihood_decoding_prop.

Variables (A : finFieldType) (B : finType) (W : `Ch(A, B)).
Variables (n : nat) (C : {vspace 'rV[A]_n}).
Variable repair : decT B [finType of 'rV[A]_n] n.
Let P := fdist_uniform_supp real_realType (vspace_not_empty C).
Hypothesis ML_dec : ML_decoding W C repair P.

Local Open Scope channel_code_scope.

Lemma ML_err_rate x1 x2 y : repair y = Some x1 ->
  x2 \in C -> W ``(y | x2) <= W ``(y | x1).
Proof.
move=> Hx1 Hx2.
case/boolP : (W ``(y | x2) == 0) => [/eqP -> //| Hcase].
have PWy : receivable_prop P W y.
  apply/existsP; exists x2.
  by rewrite Hcase andbT fdist_uniform_supp_neq0 inE.
case: (ML_dec (mkReceivable PWy)) => x' [].
rewrite /= Hx1 => -[<-] ->.
by apply: (le_bigmax_cond _ (fun i => W ``(y | i))).
Qed.

Variable M : finType.
Hypothesis M_not_0 : (0 < #|M|)%nat.
Variable discard : discardT A n M.
Variable enc : encT A M n.
Hypothesis enc_img : enc @: M \subset C.
Hypothesis discard_cancel : forall y x, repair y = Some x -> enc (discard x) = x.
Let dec := [ffun x => omap discard (repair x)].

Import ssrnum.Num.Theory.

Lemma ML_smallest_err_rate phi :
  echa(W, mkCode enc dec) <= echa(W, mkCode enc phi).
Proof.
apply/RleP/leR_wpmul2l; first by apply/mulR_ge0 => //; exact/invR_ge0/ltR0n.
rewrite /ErrRateCond /=; apply/RleP.
rewrite [leRHS](eq_bigr
  (fun m => 1 - Pr (W ``(|enc m)) [set tb | phi tb == Some m])); last first.
  move=> m _; rewrite Pr_to_cplt; congr (_ - Pr _ _).
  apply/setP => t; by rewrite !inE negbK.
rewrite [leLHS](eq_bigr
  (fun m => 1 - Pr (W ``(|enc m)) [set tb | dec tb == Some m])); last first.
  move => m _.
  rewrite [in LHS]Pr_to_cplt; congr (_ - Pr _ _).
  apply/setP => t; by rewrite !inE negbK.
rewrite 2!big_split /=; apply: lerD => //.
rewrite -2!big_morph_oppR lerNr opprK /Pr (exchange_big_dep xpredT) //=.
rewrite [leRHS](exchange_big_dep xpredT) //=.
apply ler_sum => /= tb _.
rewrite (eq_bigl (fun m => phi tb == Some m)); last by move=> m; rewrite inE.
rewrite [leRHS](eq_bigl (fun m => dec tb == Some m)); last by move=> m; rewrite inE.
(* show that phi_ML succeeds more often than phi *)
have [dectb_None|dectb_Some] := boolP (dec tb == None).
  case/boolP : (receivable_prop P W tb) => [Hy|Htb].
    case: (ML_dec (mkReceivable Hy)) => [m' [tb_m']].
    by move: dectb_None; rewrite {1}/dec {1}ffunE tb_m'.
  have W_tb m : W ``(tb | enc m) = 0%R.
    apply/eqP; apply/contraR : Htb => Htb.
    apply/existsP; exists (enc m).
    rewrite Htb andbT fdist_uniform_supp_neq0 inE.
    move/subsetP : enc_img; apply; apply/imsetP; by exists m.
  rewrite (eq_bigr (fun=> 0)); last by move=> m _; rewrite W_tb.
  by rewrite big1 //; apply sumr_ge0.
case/boolP : (phi tb == None) => [/eqP ->|phi_tb].
  by rewrite big_pred0 //; apply sumr_ge0.
have [m1 Hm1] : exists m', dec tb = Some m' by destruct (dec tb) => //; exists s.
have [m2 Hm2] : exists m', phi tb = Some m' by destruct (phi tb) => //; exists s.
rewrite Hm1 {}Hm2.
rewrite (eq_bigl [pred m | m == m2]); last by move=> ?; rewrite eq_sym.
rewrite [leRHS](eq_bigl [pred m | m == m1]); last by move=> ?; rewrite eq_sym.
rewrite 2!big_pred1_eq; apply ML_err_rate.
  move: Hm1; rewrite /dec ffunE /omap /obind /oapp.
  move H : (repair tb) => h.
  case: h H => // a tb_a [<-]; congr Some.
  by rewrite (discard_cancel tb_a).
by move/subsetP : enc_img; apply; apply/imsetP; exists m2.
Qed.

End maximum_likelihood_decoding_prop.

Section MD_ML_decoding.

Variable p : {prob R}.

Let card_F2 : #| 'F_2 | = 2%nat. Proof. by rewrite card_Fp. Qed.
Let W := BSC.c card_F2 p.

Variables (n : nat) (C : {vspace 'rV['F_2]_n}).
Variable f : repairT [finType of 'F_2] [finType of 'F_2] n.
Variable f_img : oimg f \subset C.
Variable M : finType.
Variable discard : discardT [finType of 'F_2] n M.
Variable enc : encT [finType of 'F_2] M n.
Hypothesis compatible : cancel_on C enc discard.
Variable P : {fdist 'rV['F_2]_n}.

Lemma MD_implies_ML : Prob.p p < 1/2 :> R-> MD_decoding [set cw in C] f ->
  (forall y, f y != None) -> ML_decoding W C f P.
Proof.
move=> p05 MD f_total y.
have codebook_not_empty : {c | c \in [set cw in C] }.
  move: (mem0v C); set x := (X in X \in C) => _.
  exists x; by rewrite inE mem0v.
have {}MD : MD_decoding_alt f codebook_not_empty.
  apply MD_decoding_equiv => //.
  apply/subsetP => y' Hy'.
  move/subsetP : f_img => /(_ _ Hy'); by rewrite inE.
move Hoc : (f y) => oc.
case: oc Hoc => [c|] Hc; last first.
  by move: (f_total y); rewrite Hc.
exists c; split; first by reflexivity.
(* replace  W ``^ n (y | f c) with a closed formula because it is a BSC *)
pose dH_y c := dH y c.
pose g : nat -> R := fun d : nat => ((1 - Prob.p p) ^ (n - d) * (Prob.p p) ^ d)%R.
have -> : W ``(y | c) = g (dH_y c).
  move: (DMC_BSC_prop p enc (discard c) y).
  set cast_card := eq_ind_r _ _ _.
  rewrite (_ : cast_card = card_F2) //.
  clear cast_card.
  rewrite -/W compatible //.
  move/subsetP : f_img; apply.
  by rewrite inE; apply/existsP; exists (receivable_rV y); apply/eqP.
transitivity (\big[Order.max/0]_(c in C) (g (dH_y c))); last first.
  apply eq_bigr => /= c' Hc'.
  move: (DMC_BSC_prop p enc (discard c') y).
  set cast_card := eq_ind_r _ _ _.
  rewrite (_ : cast_card = card_F2) //.
  by rewrite -/W compatible.
(* the function maxed over is decreasing so we may look for its minimizer,
   which is given by minimum distance decoding *)
rewrite (@bigmaxR_bigmin_vec_helper _ _ _ _ _ _ _ _ _ _ codebook_not_empty) //.
- by rewrite bigmaxRE; apply eq_bigl => /= i; rewrite inE.
- by apply bsc_prob_prop.
- move=> r; rewrite /g !coqRE.
  apply/RleP/mulr_ge0; apply/exprn_ge0; last exact/prob_ge0.
  exact/onem_ge0/prob_le1.
- rewrite inE; move/subsetP: f_img; apply.
  rewrite inE; apply/existsP; by exists (receivable_rV y); apply/eqP.
- by move=> ? _; rewrite /dH_y max_dH.
- by rewrite /dH_y MD.
Qed.

End MD_ML_decoding.

Section MAP_decoding.

Variables (A : finFieldType) (B : finType) (W : `Ch(A, B)).
Variables (n : nat) (C : {vspace 'rV[A]_n}).
Variable dec : decT B [finType of 'rV[A]_n] n.
Variable P : {fdist 'rV[A]_n}.

Definition MAP_decoding := forall y : P.-receivable W,
  exists m, dec y = Some m /\
    P `^^ W (m | y) = \rmax_(m in C) (P `^^ W (m | y)).

End MAP_decoding.

Section MAP_decoding_prop.

Variables (A : finFieldType) (B : finType) (W : `Ch(A, B)).
Variables (n : nat) (C : {vspace 'rV[A]_n}).
Variable dec : decT B [finType of 'rV[A]_n] n.
Variable dec_img : oimg dec \subset C.
Let P := fdist_uniform_supp real_realType (vspace_not_empty C).

Lemma MAP_implies_ML : MAP_decoding W C dec P -> ML_decoding W C dec P.
Proof.
move=> HMAP.
rewrite /ML_decoding => /= tb.
have Hunpos : (#| [set cw in C] |%:R)^-1 > 0 :> R.
  by rewrite invr_gt0 ltr0n; exact/vspace_not_empty.
move: (HMAP tb) => [m [tbm]].
rewrite /fdist_post_prob. unlock. simpl.
set tmp := \rmax_(_ <- _ | _) _.
rewrite /tmp.
under [in X in _ = X -> _]eq_bigr do rewrite ffunE.
move=> H.
evar (h : 'rV[A]_n -> R); rewrite (eq_bigr h) in H; last first.
  by move=> v vC; rewrite /h; reflexivity.
rewrite -bigmaxR_distrl in H; last first.
  by apply/RleP; rewrite invr_ge0; exact/fdist_post_prob_den_ge0.
rewrite {2 3}/P in H.
set r := index_enum _ in H.
move: H.
under [in X in _ = X -> _]eq_bigr.
  move=> i iC.
  rewrite fdist_uniform_supp_in; last by rewrite inE.
  over.
move=> H.
rewrite -bigmaxR_distrr in H; last exact/RleP/ltW/Hunpos.
exists m; split; first exact tbm.
rewrite ffunE in H.
set x := (X in _ * _ / X) in H.
have x0 : x^-1 <> 0 by apply/eqP/invr_neq0; rewrite -receivable_propE receivableP.
move/(eqR_mul2r x0) in H.
rewrite /= fdist_uniform_supp_in ?inE // in H; last first.
  move/subsetP : dec_img; apply.
  by rewrite inE; apply/existsP; exists (receivable_rV tb); apply/eqP.
move/lt0r_neq0/eqP: Hunpos.
move/eqR_mul2l : H; move/[apply] ->.
by rewrite bigmaxRE.
Qed.

End MAP_decoding_prop.

Section MPM_decoding.
(* in the special case of a binary code... *)
Variable W : `Ch('F_2, [finType of 'F_2]).
Variable n : nat.
Variable C : {vspace 'rV['F_2]_n}.
Hypothesis C_not_empty : (0 < #|[set cw in C]|)%nat.
Variable m : nat.
Variable enc : encT [finFieldType of 'F_2] [finType of 'rV['F_2]_(n - m)] n.
Variable dec : decT [finFieldType of 'F_2] [finType of 'rV['F_2]_(n - m)] n.

Local Open Scope vec_ext_scope.

Definition MPM_decoding := let P := `U C_not_empty in
  forall (y : P.-receivable W),
  forall x, dec y = Some x ->
  forall n0,
    P '_ n0 `^^ W ((enc x) ``_ n0 | y) = \rmax_(b in 'F_2) P '_ n0 `^^ W (b | y).

End MPM_decoding.
