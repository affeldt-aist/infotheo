(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import Reals_ext ssr_ext ssralg_ext Rssr log2 Rbigop proba entropy.
Require Import ln_facts arg_rmax num_occ types jtypes divergence.
Require Import conditional_divergence entropy channel_code channel.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope channel_code_scope.
Local Open Scope channel_scope.
Local Open Scope entropy_scope.
Local Open Scope tuple_ext_scope.
Local Open Scope reals_ext_scope.

Section scha_def.

Variables B A M : finType.
Variable n : nat.

(** Decoding success rate: *)

Definition scha (W : `Ch_1(A, B)) (c : code A B M n) := 1 - echa(W , c).

End scha_def.

Notation "scha( W , C )" := (scha W C) (at level 50) : channel_code_scope.

Section scha_facts.

Variables B A M : finType.
Hypothesis Mnot0 : (0 < #|M|)%nat.
Variable n : nat.

Lemma scha_pos (W : `Ch_1(A, B)) (c : code A B M n) : 0 <= scha(W, c).
Proof. rewrite /scha; by apply Rge_le, Rge_minus, Rle_ge, echa1. Qed.

(** Expression of the success rate of decoding: *)

Lemma success_decode (W : `Ch_1(A, B)) (c : code A B M n) :
  scha(W, c) = 1 / INR #|M| *
    \rsum_(m : M) \rsum_(tb | dec c tb == Some m) (W ``(| enc c m)) tb.
Proof.
set rhs := \rsum_(m | _ ) _.
have {rhs}-> : rhs = \rsum_(m in M) (1 - e(W, c) m).
  apply eq_bigr => i Hi; rewrite -Pr_to_cplt.
  apply eq_bigl => t /=; by rewrite inE.
set rhs := \rsum_(m | _ ) _.
have {rhs}-> : rhs = INR #|M| - \rsum_(m in M) e(W, c) m.
  rewrite /rhs {rhs} big_split /= big_const iter_Rplus mulR1.
  by rewrite -(big_morph _ morph_Ropp oppR0).
by rewrite mulRDr -mulRA mulVR ?mulR1 ?INR_eq0 -?lt0n // mulRN.
Qed.

End scha_facts.

Local Open Scope types_scope.
Local Open Scope divergence_scope.
Local Open Scope set_scope.

Section typed_success_decomp_sect.

Variables A B M : finType.
Variable W : `Ch_1*(A, B).
Hypothesis Mnot0 : (0 < #|M|)%nat.

Variable n' : nat.
Let n := n'.+1.
Variable P : P_ n ( A ).

(** Bound of the success rate of decoding for typed codes
   using conditional divergence: *)

Definition success_factor (tc : typed_code B M P) (V : P_ n (A , B)) :=
  exp2 (- INR n * `H(V | P)) / INR #|M| *
  \rsum_ (m : M) INR #| (V.-shell (tuple_of_row (enc tc m ))) :&:
                        (@tuple_of_row B n @: ((dec tc) @^-1: [set Some m])) |.

Let Anot0 : (0 < #|A|)%nat. Proof. by case: W. Qed.

Let Bnot0 : (0 < #|B|)%nat.
Proof.
case/card_gt0P : Anot0 => a _; exact (dist_domain_not_empty (W a)).
Qed.

Lemma typed_success (tc : typed_code B M P) : scha(W, tc) =
  \rsum_ (V | V \in \nu^{B}(P)) exp_cdiv P V W * success_factor tc V.
Proof.
rewrite success_decode // div1R.
symmetry.
transitivity (/ INR #|M| * \rsum_(m : M) \rsum_(V | V \in \nu^{B}(P))
    exp_cdiv P V W * INR #| V.-shell (tuple_of_row (enc tc m)) :&:
                            (@tuple_of_row B n @: (dec tc @^-1: [set Some m])) | *
    exp2 (- INR n * `H(V | P))).
  rewrite exchange_big /= big_distrr /=.
  apply eq_bigr => V _.
  rewrite /success_factor !mulRA -(mulRC (/ INR #|M|)) -!mulRA; f_equal.
  symmetry; rewrite -big_distrl /= -big_distrr /= -mulRA; f_equal.
  by rewrite mulRC.
f_equal.
apply eq_bigr=> m _.
rewrite (reindex_onto (@row_of_tuple B n) (@tuple_of_row B n)); last first.
  move=> i Hi; by rewrite tuple_of_rowK.
rewrite (sum_tuples_ctypes (typed_prop tc m)) //.
apply eq_bigr=> V HV.
rewrite -mulRA mulRC -mulRA -iter_Rplus_Rmult -big_const.
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

(** * Bound of the success rate of decoding for typed codes *)

Definition success_factor_bound :=
  exp2(- INR n * +| log (INR #|M|) / INR n - `I(P ; V) |).

Variable tc : typed_code B M P.
Hypothesis Vctyp : V \in \nu^{B}(P).

Lemma success_factor_bound_part1 : success_factor tc V <= 1.
Proof.
apply/RleP; rewrite -(Rle_pmul2l (INR #|M|)) ?ltR0n //; apply/RleP.
rewrite /success_factor /Rdiv -(mulRC (/ INR #|M|)) 2!mulRA.
rewrite mulRV ?INR_eq0 -?lt0n // mul1R.
rewrite -iter_Rplus_Rmult -big_const /=.
rewrite (_ : \rsum_(m | m \in M ) 1 = \rsum_(m : M) 1); last exact/eq_bigl.
rewrite big_distrr /=.
apply: ler_rsum => m _.
rewrite mulNR exp2_Ropp.
apply/RleP; rewrite mulRC leR_pdivr_mulr // ?mul1R.
apply/RleP/(Rle_trans _ (INR #| V.-shell (tuple_of_row (enc tc m)) |) _); last first.
  apply card_shelled_tuples => //.
    exact/typed_prop.
  case: (jtype.c V) => _ Anot0.
  case/card_gt0P : (Anot0) => a _.
  exact: (dist_domain_not_empty (V a)).
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
  success_factor tc V <=  exp2(INR n * `I(P ; V)) / INR #|M|.
Proof.
rewrite /success_factor -mulRA (mulRC (/ INR #|M|)) !mulRA.
apply Rmult_le_compat_r; first exact/ltRW/invR_gt0/lt_0_INR/ltP.
rewrite /mut_info /Rminus addRC addRA.
rewrite (_ : - `H(P , V) + `H P = - `H( V | P )); last by rewrite /cond_entropy; field.
rewrite mulRDr mulRN -mulNR /exp2 ExpD.
apply Rmult_le_compat_l => //.
rewrite -(@big_morph _ _ _ 0 _ O _ morph_plus_INR Logic.eq_refl).
apply (Rle_trans _ (INR #| T_{`tO( V )} |)); last first.
  rewrite -output_type_out_entropy //; by apply card_typed_tuples.
apply le_INR; apply/leP.
apply: (@leq_trans (\sum_m #| T_{`tO( V )} :&: (@tuple_of_row B n @: (dec tc @^-1: [set Some m]))|)).
- apply leq_sum => m _.
  by apply subset_leq_card, setSI, shell_subset_output_type.
- set lhs := \sum_ _ _.
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
      apply Some_inj.
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
- apply (Rle_trans _ (exp2(INR n * `I(P ; V)) / INR #|M|)); last first.
  + apply Req_le; symmetry.
    rewrite /Rminus mulRDr mulRC.
    rewrite Rmult_opp_opp -mulRA mulRN mulVR ?INR_eq0 //.
    rewrite mulRN mulR1 /exp2 ExpD mulRC /Rdiv; f_equal.
    rewrite Exp_Ropp LogK //; exact/lt_0_INR/ltP.
  + exact/success_factor_bound_part2.
Qed.

End typed_success_factor_bound_sect.

Section typed_success_bound_sect.

Variables A B M : finType.
Variable W : `Ch_1*(A, B).
Hypothesis Mnot0 : (0 < #|M|)%nat.

Variable n' : nat.
Let n := n'.+1.
Variable P : P_ n ( A ).
Variable tc : typed_code B M P.

Let Anot0 : (0 < #|A|)%nat. Proof. by case: (W). Qed.

Let Bnot0 : (0 < #|B|)%nat.
Proof. case/card_gt0P : Anot0 => a _; exact: (dist_domain_not_empty (W a)). Qed.

Let V0 : P_ n (A, B).
Proof.
move: (jtype_not_empty n Anot0 Bnot0) => H; exact (enum_val (Ordinal H)).
Qed.

Let exp_cdiv_bound := fun V => exp_cdiv P V W * success_factor_bound M V P.

(** Bound of the success rate of decoding for typed codes
   using mutual information: *)

Lemma typed_success_bound :
  let Vmax := arg_rmax V0 [pred V | V \in \nu^{B}(P)] exp_cdiv_bound in
  scha(W, tc) <= (INR n.+1)^(#|A| * #|B|) * exp_cdiv_bound Vmax.
Proof.
move=> Vmax.
rewrite (typed_success W Mnot0 tc).
apply (Rle_trans _ ( \rsum_(V|V \in \nu^{B}(P)) exp_cdiv P V W *
  exp2 (- INR n *  +| log (INR #|M|) * / INR n - `I(P ; V) |))).
  apply: ler_rsum => V HV.
  rewrite -mulRA; apply Rmult_le_compat_l.
    rewrite /exp_cdiv.
    case : ifP => _ //; exact/Rle_refl.
  rewrite /success_factor mulRA.
  exact: success_factor_ub.
apply (Rle_trans _ (\rsum_(V | V \in \nu^{B}(P)) exp_cdiv P Vmax W *
                    exp2 (- INR n * +| log (INR #|M|) * / INR n - `I(P ; Vmax)|))).
  apply ler_rsum => V HV.
  move: (@arg_rmax2 [finType of (P_ n (A, B))] V0 [pred V | V \in \nu^{B}(P) ]
                    (fun V => exp_cdiv P V W * success_factor_bound M V P)).
  apply => //; by exists V.
rewrite big_const iter_Rplus_Rmult /success_factor_bound.
apply Rmult_le_compat_r.
- apply mulR_ge0; last exact/exp2_ge0.
  rewrite /exp_cdiv; case: ifP => _ //; exact/Rle_refl.
- rewrite INR_pow_expn; exact/le_INR/leP/card_nu.
Qed.

End typed_success_bound_sect.

Section success_bound_sect.

Variables A B M : finType.
Variable W : `Ch_1*(A, B).
Hypothesis Mnot0 : (0 < #|M|)%nat.

Variable n' : nat.
Let n := n'.+1.
Variable c : code A B M n.

Lemma Anot0 : (0 < #|A|)%nat. Proof. by case: (W) => _ Anot0. Qed.

Let P0 : P_ n ( A ).
Proof.
move: (type_not_empty n' Anot0) => H; exact (enum_val (Ordinal H)).
Defined.

Local Open Scope num_occ_scope.

(** * Bound of the success rate of decoding *)

Lemma success_bound :
  let Pmax := arg_rmax P0 predT (fun P => scha(W, P.-typed_code c)) in
  scha(W, c) <= (INR n.+1) ^ #|A| * scha(W, Pmax.-typed_code c).
Proof.
move=> Pmax.
apply (Rle_trans _ (INR #| P_ n ( A ) | * scha W (Pmax.-typed_code c))); last first.
  apply Rmult_le_compat_r; first by apply scha_pos.
  rewrite INR_pow_expn; apply le_INR; apply/leP.
  exact: (type_counting A n).
apply (Rle_trans _ (\rsum_(P : P_ n ( A )) scha W (P.-typed_code c))); last first.
  rewrite (_ : INR #| P_ n ( A ) | * scha W (Pmax.-typed_code c) =
             \rsum_(P : P_ n ( A )) scha W (Pmax.-typed_code c)); last first.
    by rewrite big_const iter_Rplus_Rmult.
  apply ler_rsum => P _.
  exact: (@arg_rmax2 _ P0 xpredT (fun P1 : P_ n (A) => scha(W, P1.-typed_code c))).
rewrite success_decode // -(sum_messages_types c).
rewrite div1R (big_morph _ (morph_mulRDr _) (mulR0 _)).
apply ler_rsum => P _.
apply/RleP; rewrite mulRC leR_pdivr_mulr; last by apply/RltP; rewrite ltR0n.
rewrite success_decode // div1R -mulRA mulRCA mulVR ?INR_eq0 -?lt0n // mulR1.
apply/RleP/(Rle_trans _ (\rsum_(m | m \in enc_pre_img c P)
                     \rsum_(y | (dec (P.-typed_code c)) y == Some m)
                     (W ``(|(enc (P.-typed_code c)) m)) y)).
  apply ler_rsum => m Hm.
  apply Req_le, eq_big => tb // _.
  rewrite inE in Hm.
  by rewrite /tcode /= ffunE Hm.
- apply ler_rsum_l => //= i Hi; first exact/Rle_refl.
  apply: rsumr_ge0 => ? _; exact/dist_nonneg.
Qed.

End success_bound_sect.
