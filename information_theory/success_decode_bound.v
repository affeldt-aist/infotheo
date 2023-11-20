(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix.
Require Import Reals.
From mathcomp Require Import Rstruct.
Require Import ssrR Rstruct_ext Reals_ext ssr_ext ssralg_ext logb Rbigop fdist entropy.
Require Import ln_facts num_occ types jtypes divergence conditional_divergence.
Require Import entropy channel_code channel.

(******************************************************************************)
(*         Lemmas for the converse of the channel coding theorem              *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   success_factor       == bound of the success rate of decoding for typed  *)
(*                           codes using conditional divergence               *)
(*   success_factor_bound == bound of the success rate of decoding for typed  *)
(*                           codes                                            *)
(*                                                                            *)
(* Lemmmas:                                                                   *)
(*   typed_success_bound  == bound of the success rate of decoding for typed  *)
(*                           codes using mutual information                   *)
(*          success_bound == bound of the success rate of decoding            *)
(*                                                                            *)
(* For details, see Reynald Affeldt, Manabu Hagiwara, and Jonas Sénizergues.  *)
(* Formalization of Shannon's theorems. Journal of Automated Reasoning,       *)
(* 53(1):63--103, 2014                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.
Local Open Scope channel_code_scope.
Local Open Scope channel_scope.
Local Open Scope entropy_scope.
Local Open Scope tuple_ext_scope.
Local Open Scope reals_ext_scope.
Local Open Scope types_scope.
Local Open Scope divergence_scope.
Local Open Scope set_scope.

Import Order.POrderTheory Num.Theory.

Section typed_success_decomp_sect.

Variables A B M : finType.
Variable W : `Ch*(A, B).
Hypothesis Mnot0 : (0 < #|M|)%nat.

Variable n' : nat.
Let n := n'.+1.
Variable P : P_ n ( A ).

Definition success_factor (tc : typed_code B M P) (V : P_ n (A , B)) :=
  exp2 (- n%:R * `H(V | P)) / #|M|%:R *
  \sum_ (m : M) #| (V.-shell (tuple_of_row (enc tc m ))) :&:
                    (@tuple_of_row B n @: ((dec tc) @^-1: [set Some m])) |%:R.

Let Anot0 : (0 < #|A|)%nat. Proof. by case: W. Qed.

Let Bnot0 : (0 < #|B|)%nat.
Proof.
case/card_gt0P : Anot0 => a _; exact (fdist_card_neq0 (W a)).
Qed.

Lemma typed_success (tc : typed_code B M P) : scha(W, tc) =
  \sum_ (V | V \in \nu^{B}(P)) exp_cdiv P V W * success_factor tc V.
Proof.
rewrite schaE // div1R.
symmetry.
transitivity (/ #|M|%:R * \sum_(m : M) \sum_(V | V \in \nu^{B}(P))
    exp_cdiv P V W * #| V.-shell (tuple_of_row (enc tc m)) :&:
                        (@tuple_of_row B n @: (dec tc @^-1: [set Some m])) |%:R *
    exp2 (- n%:R * `H(V | P))).
  rewrite exchange_big /= big_distrr /=.
  apply eq_bigr => V _.
  rewrite /success_factor !mulRA -(mulRC (/ #|M|%:R)) -!mulRA; f_equal.
  symmetry; rewrite -big_distrl /= -big_distrr /= -mulRA; f_equal.
  by rewrite mulRC.
f_equal.
apply eq_bigr=> m _.
rewrite (reindex_onto (@row_of_tuple B n) (@tuple_of_row B n)); last first.
  move=> i Hi; by rewrite tuple_of_rowK.
rewrite (sum_tuples_ctypes (typed_prop tc m)) //.
apply eq_bigr=> V HV.
rewrite -mulRA mulRC -mulRA -iter_addR -big_const.
apply eq_big => tb.
- rewrite inE row_of_tupleK eqxx andbT.
  f_equal.
  apply/imsetP/idP.
    case=> v H ->; rewrite tuple_of_rowK.
    by rewrite 2!inE in H.
  move=> Hm.
  exists (row_of_tuple tb); last by rewrite row_of_tupleK.
  by rewrite !inE.
- rewrite in_set.
  move=> /andP [Htb _].
  rewrite mulRC -(@dmc_exp_cdiv_cond_entropy _ _ _ _ _ _ _ (row_of_tuple tb) (typed_prop tc m) HV) //.
  by rewrite row_of_tupleK.
Qed.

End typed_success_decomp_sect.

Section typed_success_factor_bound_sect.
Variables A B M : finType.
Hypothesis Mnot0 : (0 < #|M|)%nat.
Variable n' : nat.
Let n := n'.+1.
Variable V : P_ n ( A , B ).
Variable P : P_ n ( A ).

Definition success_factor_bound :=
  exp2(- n%:R * +| log #|M|%:R / n%:R - `I(P, V) |).

Variable tc : typed_code B M P.
Hypothesis Vctyp : V \in \nu^{B}(P).

Lemma success_factor_bound_part1 : success_factor tc V <= 1.
Proof.
apply/RleP; rewrite -(@ler_pM2l _ #|M|%:R)//; last by rewrite ltr0n.
apply/RleP.
rewrite /success_factor /Rdiv -(mulRC (/ #|M|%:R)%coqR) -!RmultE 2!mulRA.
rewrite INRE mulRV; last first.
  by rewrite -INRE INR_eq0' -?lt0n.
rewrite mul1R -INRE.
rewrite -iter_addR -big_const /=.
rewrite (_ : \sum_(m | m \in M ) 1 = \sum_(m : M) 1); last exact/eq_bigl.
rewrite big_distrr /=.
apply: leR_sumR => m _.
rewrite mulNR exp2_Ropp.
rewrite mulRC leR_pdivr_mulr // ?mul1R.
apply/(@leR_trans #| V.-shell (tuple_of_row (enc tc m)) |%:R); last first.
  apply card_shelled_tuples => //.
    exact/typed_prop.
  case: (JType.c V) => _ Anot0.
  case/card_gt0P : (Anot0) => a _.
  exact: (fdist_card_neq0 (V a)).
apply/le_INR/leP/subset_leq_card/setIidPl/setP => tb.
by rewrite in_set in_set andbC andbA andbb.
Qed.

Let partition_pre_image : {set set_of_finType [finType of n.-tuple B]} :=
  [set T_{ `tO( V ) } :&: (@tuple_of_row B n @: (dec tc @^-1: [set Some m])) |
   m in M & [exists y, y \in T_{`tO( V )} :&: (@tuple_of_row B n @: (dec tc @^-1: [set Some m]))]].

Let trivIset_pre_image : trivIset partition_pre_image.
Proof.
apply/trivIsetP => /= E F.
case/imsetP => m _ Em.
case/imsetP => l _ El diffEF.
have m_l : m != l by apply/negP => /eqP abs; move: diffEF; apply/negPn/negPn; subst.
rewrite disjoints_subset; apply/subsetP => y; subst E F; rewrite !in_set => /andP [H1 /eqP H2].
rewrite H1 andTb.
move/eqP in H2.
case/imsetP : H2 => y1 Hy1 yy1.
apply/imsetP; case => y2 Hy2 yy2.
rewrite !inE in Hy1.
rewrite !inE in Hy2.
subst y.
move/tuple_of_row_inj : yy2 => ?; subst y2.
rewrite (eqP Hy1) in Hy2.
case/eqP : Hy2 => ?; subst l.
by rewrite eqxx in m_l.
Qed.

Let cover_pre_image : cover partition_pre_image =
  \bigcup_(m : M) (T_{`tO( V )} :&: (@tuple_of_row B n @: (dec tc @^-1: [set Some m]))).
Proof.
apply/setP => tb.
case/boolP : (tb \in cover partition_pre_image) => Hcase.
- symmetry; case/bigcupP: Hcase => E.
  rewrite /partition_pre_image; case/imsetP => m _ Em ; subst E => Hcase.
  apply/bigcupP; by exists m.
- symmetry.
  apply/negP => abs; move: Hcase; apply/negP/negPn.
  case/bigcupP : abs => m _ H.
  rewrite /cover /partition_pre_image.
  apply/bigcupP; exists (T_{`tO( V )} :&: (@tuple_of_row B n @: (dec tc @^-1: [set Some m]))) => //.
  apply/imsetP; exists m => //.
  rewrite in_set; apply/andP; split => //.
  apply/existsP; by exists tb.
Qed.

Lemma success_factor_bound_part2 :
  success_factor tc V <= exp2(n%:R * `I(P, V)) / #|M|%:R.
Proof.
rewrite /success_factor -mulRA (mulRC (/ #|M|%:R)) !mulRA.
apply leR_wpmul2r; first exact/invR_ge0/ltR0n.
rewrite /mutual_info_chan -addR_opp addRC addRA.
rewrite (_ : - `H(type.d P , V) + `H P = - `H( V | P )); last first.
  rewrite /cond_entropy_chan.
  by rewrite oppRD oppRK.
rewrite mulRDr mulRN -mulNR /exp2 ExpD; apply leR_wpmul2l => //.
rewrite -big_morph_natRD; apply (@leR_trans #| T_{`tO( V )} |%:R); last first.
  by rewrite -output_type_out_entropy //; exact: card_typed_tuples.
apply/le_INR/leP.
apply: (@leq_trans (\sum_m #| T_{`tO( V )} :&: (@tuple_of_row B n @: (dec tc @^-1: [set Some m]))|)).
- apply leq_sum => m _.
  by apply subset_leq_card, setSI, shell_subset_output_type.
- set lhs := (\sum__ _)%nat.
  rewrite (_ : lhs = #|\bigcup_(i : M) (T_{`tO( V )} :&: (@tuple_of_row B n @: (dec tc @^-1: [set Some i]))) | ); last first.
    subst lhs.
    rewrite -cover_pre_image.
    move: trivIset_pre_image ; rewrite /trivIset => /eqP => <-.
    rewrite big_imset /= ; last first.
      move=> m l _.
      rewrite in_set; case/existsP => tb Htb.
      move/setP/(_ tb); rewrite Htb; move: Htb.
      rewrite in_set => /andP [_ Hl].
      rewrite in_set => /andP [_ Hm].
      suff : Some m = Some l by case.
      move: Hl Hm.
      case/imsetP => v1 Hv1 ->.
      case/imsetP => v2 Hv2.
      move/tuple_of_row_inj => ?; subst v2.
      rewrite !inE in Hv1, Hv2.
      by rewrite -(eqP Hv1) -(eqP Hv2).
    symmetry; rewrite big_mkcond /=.
    apply eq_bigr => m _.
    case : ifP => //; rewrite in_set => /negbT H.
    symmetry; apply/eqP/negPn/negP => abs ; move: H.
    apply/negP/negPn/existsP/card_gt0P; by rewrite lt0n.
  apply subset_leq_card; apply/subsetP => tb.
  case/bigcupP => m _.
  by rewrite in_set => /andP [H _].
Qed.

Lemma success_factor_ub :
  success_factor tc V <= success_factor_bound.
Proof.
rewrite /success_factor_bound.
apply Rmax_case.
- rewrite mulR0 exp2_0; by apply success_factor_bound_part1.
- apply (@leR_trans (exp2 (n%:R * `I(P, V)) / #|M|%:R)); last first.
  + apply/Req_le/esym.
    rewrite mulRDr mulRC.
    rewrite Rmult_opp_opp -mulRA mulRN mulVR ?INR_eq0' //.
    rewrite mulRN mulR1 /exp2 ExpD mulRC /Rdiv; f_equal.
    rewrite Exp_Ropp LogK //; exact/ltR0n.
  + exact/success_factor_bound_part2.
Qed.

End typed_success_factor_bound_sect.

Section typed_success_bound_sect.

Variables A B M : finType.
Variable W : `Ch*(A, B).
Hypothesis Mnot0 : (0 < #|M|)%nat.

Variable n' : nat.
Let n := n'.+1.
Variable P : P_ n ( A ).
Variable tc : typed_code B M P.

Let Anot0 : (0 < #|A|)%nat. Proof. by case: (W). Qed.

Let Bnot0 : (0 < #|B|)%nat.
Proof. case/card_gt0P : Anot0 => a _; exact: (fdist_card_neq0 (W a)). Qed.

Let V0 : P_ n (A, B).
Proof.
move: (jtype_not_empty n Anot0 Bnot0) => H; exact (enum_val (Ordinal H)).
Qed.

Hypothesis HV0 : V0 \in \nu^{B}(P).

Let exp_cdiv_bound := fun V => exp_cdiv P V W * success_factor_bound M V P.

Let Vmax := [arg max_(V > V0) exp_cdiv_bound V]%O.

Lemma typed_success_bound :
  scha(W, tc) <= n.+1%:R ^ (#|A| * #|B|) * exp_cdiv_bound Vmax.
Proof.
rewrite (typed_success W Mnot0 tc).
apply (@leR_trans ( \sum_(V|V \in \nu^{B}(P)) exp_cdiv P V W *
  exp2 (- n%:R *  +| log #|M|%:R * / n%:R - `I(P, V) |))).
  apply: leR_sumR => V Vnu.
  rewrite -mulRA; apply leR_wpmul2l.
    by rewrite /exp_cdiv; case : ifP.
  by rewrite /success_factor mulRA; exact: success_factor_ub.
apply (@leR_trans (\sum_(V | V \in \nu^{B}(P)) exp_cdiv P Vmax W *
                    exp2 (- n%:R * +| log #|M|%:R * / n%:R - `I(P, Vmax)|))).
  apply leR_sumR => V HV.
  by move/RleP: (@arg_rmax2 [finType of (P_ n (A, B))] V0
    (fun V => exp_cdiv P V W * success_factor_bound M V P) V).
rewrite big_const iter_addR /success_factor_bound; apply leR_wpmul2r.
- apply mulR_ge0; last exact/exp2_ge0.
  by rewrite /exp_cdiv; case: ifP.
- by rewrite natRexp; exact/le_INR/leP/card_nu.
Qed.

End typed_success_bound_sect.

Section success_bound_sect.

Variables A B M : finType.
Variable W : `Ch*(A, B).
Hypothesis Mnot0 : (0 < #|M|)%nat.

Variable n' : nat.
Let n := n'.+1.
Variable c : code A B M n.

Lemma Anot0 : (0 < #|A|)%nat. Proof. by case: (W) => _ Anot0. Qed.

Let P0 : P_ n ( A ).
Proof.
move: (type_card_neq0 n' Anot0) => H; exact (enum_val (Ordinal H)).
Defined.

Local Open Scope num_occ_scope.

Lemma success_bound :
  let Pmax := [arg max_(P > P0) scha(W, P.-typed_code c)]%O in
  scha(W, c) <= n.+1%:R ^ #|A| * scha(W, Pmax.-typed_code c).
Proof.
move=> Pmax.
apply (@leR_trans (#| P_ n ( A ) |%:R * scha W (Pmax.-typed_code c))); last first.
  apply leR_wpmul2r; first exact: scha_pos.
  rewrite natRexp; exact/le_INR/leP/(type_counting A n).
apply (@leR_trans (\sum_(P : P_ n ( A )) scha W (P.-typed_code c))); last first.
  rewrite (_ : #| P_ n ( A ) |%:R * scha W (Pmax.-typed_code c) =
             \sum_(P : P_ n ( A )) scha W (Pmax.-typed_code c)); last first.
    by rewrite big_const iter_addR.
  apply leR_sumR => P _.
  by move/RleP : (arg_rmax2 P0 (fun P1 : P_ n (A) => scha(W, P1.-typed_code c)) P).
rewrite schaE // -(sum_messages_types c).
rewrite div1R (big_morph _ (morph_mulRDr _) (mulR0 _)).
apply leR_sumR => P _.
rewrite mulRC leR_pdivr_mulr; last exact/ltR0n.
rewrite schaE // div1R -mulRA mulRCA mulVR ?INR_eq0' -?lt0n // mulR1.
apply/(@leR_trans (\sum_(m | m \in enc_pre_img c P)
                     \sum_(y | (dec (P.-typed_code c)) y == Some m)
                     (W ``(|(enc (P.-typed_code c)) m)) y)).
  apply: leR_sumR => m Hm.
  apply/Req_le/eq_big => tb // _.
  rewrite inE in Hm.
  by rewrite /tcode /= ffunE Hm.
- apply leR_sumRl => //= i ?; [| exact: sumR_ge0].
  by apply/RleP; rewrite lexx.
Qed.

End success_bound_sect.
