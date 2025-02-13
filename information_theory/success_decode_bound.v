(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix.
From mathcomp Require Import Rstruct reals exp.
Require Import ssr_ext ssralg_ext realType_ext realType_ln fdist entropy.
Require Import num_occ types jtypes divergence conditional_divergence.
Require Import entropy channel_code channel.

(**md**************************************************************************)
(* # Lemmas for the converse of the channel coding theorem                    *)
(*                                                                            *)
(* Documented in:                                                             *)
(* - Reynald Affeldt, Manabu Hagiwara, and Jonas Sénizergues. Formalization   *)
(*   of Shannon's theorems. Journal of Automated Reasoning,  53(1):63--103,   *)
(*   2014                                                                     *)
(*                                                                            *)
(* ```                                                                        *)
(*         success_factor == bound of the success rate of decoding for typed  *)
(*                           codes using conditional divergence               *)
(*   success_factor_bound == bound of the success rate of decoding for typed  *)
(*                           codes                                            *)
(* ```                                                                        *)
(*                                                                            *)
(* Lemmmas:                                                                   *)
(* ```                                                                        *)
(*   typed_success_bound  == bound of the success rate of decoding for typed  *)
(*                           codes using mutual information                   *)
(*          success_bound == bound of the success rate of decoding            *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope channel_code_scope.
Local Open Scope channel_scope.
Local Open Scope entropy_scope.
Local Open Scope tuple_ext_scope.
Local Open Scope reals_ext_scope.
Local Open Scope types_scope.
Local Open Scope divergence_scope.
Local Open Scope set_scope.

Import Order.POrderTheory Num.Theory GRing.Theory.

Section typed_success_decomp_sect.
Variables A B M : finType.
Variable W : `Ch*(A, B).
Hypothesis Mnot0 : (0 < #|M|)%nat.

Variable n' : nat.
Let n := n'.+1.
Variable P : P_ n ( A ).

Definition success_factor (tc : typed_code B M P) (V : P_ n (A , B)) :=
  2 `^ (- n%:R * `H(V | P)%channel) / #|M|%:R *
  \sum_ (m : M) #| (V.-shell (tuple_of_row (enc tc m ))) :&:
                    (@tuple_of_row B n @: ((dec tc) @^-1: [set Some m])) |%:R.

Let Anot0 : (0 < #|A|)%nat. Proof. by case: W. Qed.

Let Bnot0 : (0 < #|B|)%nat.
Proof.
by case/card_gt0P : Anot0 => a _; exact (fdist_card_neq0 (W a)).
Qed.

Lemma typed_success (tc : typed_code B M P) : scha(W, tc) =
  \sum_ (V | V \in \nu^{B}(P)) exp_cdiv P V W * success_factor tc V.
Proof.
rewrite schaE // mul1r.
symmetry.
transitivity (#|M|%:R^-1 * \sum_(m : M) \sum_(V | V \in \nu^{B}(P))
    exp_cdiv P V W * #| V.-shell (tuple_of_row (enc tc m)) :&:
                        (@tuple_of_row B n @: (dec tc @^-1: [set Some m])) |%:R *
    2 `^ (- n%:R * `H(V | P)%channel)).
  rewrite exchange_big /= big_distrr /=.
  apply eq_bigr => V _.
  rewrite /success_factor !mulrA -(mulrC (#|M|%:R)^-1) -!mulrA; f_equal.
  symmetry; rewrite -big_distrl /= -big_distrr /= -mulrA; f_equal.
  by rewrite mulrC.
f_equal.
apply eq_bigr=> m _.
rewrite (reindex_onto (@row_of_tuple B n) (@tuple_of_row B n)); last first.
  move=> i Hi; by rewrite tuple_of_rowK.
rewrite /=.
rewrite (sum_tuples_ctypes (typed_prop tc m))//.
apply eq_bigr=> V HV.
rewrite -mulrA mulrC -mulrA.
(* TODO: dirty *)
rewrite GRing.mulr_natl.
rewrite -[LHS]addr0.
rewrite -iter_addr.
rewrite -big_const.
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
  rewrite mulrC.
  rewrite -(@dmc_exp_cdiv_cond_entropy _ _ _ _ _ _ _ (row_of_tuple tb) (typed_prop tc m) HV)//.
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

Local Open Scope reals_ext_scope.

Definition success_factor_bound :=
  2 `^ (- n%:R * +| log #|M|%:R / n%:R - `I(P, V) |).

Variable tc : typed_code B M P.
Hypothesis Vctyp : V \in \nu^{B}(P).

Lemma success_factor_bound_part1 : success_factor tc V <= 1.
Proof.
rewrite -(@ler_pM2l _ #|M|%:R)//; last by rewrite ltr0n.
rewrite /success_factor -(mulrC (#|M|%:R)^-1) 2!mulrA.
rewrite mulfV; last first.
  by rewrite pnatr_eq0 gt_eqF.
rewrite mul1r.
(* TODO: dirty *)
rewrite [leRHS]GRing.mulr_natl.
rewrite -[leRHS]addr0.
rewrite -iter_addr.
rewrite -big_const /=.
rewrite (_ : \sum_(m | m \in M ) 1 = \sum_(m : M) 1); last exact/eq_bigl.
rewrite big_distrr /=.
apply: ler_sum => m _.
rewrite mulNr.
rewrite exp.powRN.
rewrite mulrC ler_pdivrMr // ?mul1r ?exp.powR_gt0//.
apply/(@le_trans _ _ #| V.-shell (tuple_of_row (enc tc m)) |%:R); last first.
  apply card_shelled_tuples => //.
    exact/typed_prop.
  case: (JType.c V) => _ Anot0.
  case/card_gt0P : (Anot0) => a _.
  exact: (fdist_card_neq0 (V a)).
rewrite ler_nat.
apply/subset_leq_card/setIidPl/setP => tb.
by rewrite in_set in_set andbC andbA andbb.
Qed.

Let partition_pre_image (*: {set set_of_finType [finType of n.-tuple B]}*) :=
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
  success_factor tc V <= 2 `^ (n%:R * `I(P, V)) / #|M|%:R.
Proof.
rewrite /success_factor -mulrA (mulrC (#|M|%:R)^-1) !mulrA.
apply ler_wpM2r.
  by rewrite invr_ge0//.
rewrite /mutual_info_chan addrC addrA.
rewrite (_ : - `H(type.d P , V) + `H P = - `H( V | P ))%channel; last first.
  rewrite /cond_entropy_chan.
  by rewrite opprB addrC.
rewrite [in leRHS]mulrDr mulrN -mulNr.
rewrite powRD; last by rewrite pnatr_eq0 implybT.
apply ler_wpM2l => //.
  by rewrite exp.powR_ge0.
rewrite -natr_sum; apply: (@le_trans _ _ #| T_{`tO( V )} |%:R); last first.
  by rewrite -output_type_out_entropy //; exact: card_typed_tuples.
rewrite ler_nat.
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

Lemma success_factor_ub : success_factor tc V <= success_factor_bound.
Proof.
rewrite /success_factor_bound.
have [H|H] := Order.TotalTheory.leP 0 (log #|M|%:R / n%:R - (`I(P, V))).
- apply (@le_trans _ _ (2 `^ (n%:R * `I(P, V)) / #|M|%:R)); last first.
  + apply/eqW/esym.
    rewrite mulrDr mulrC.
    rewrite mulrNN -mulrA mulrN mulVf ?pnatr_eq0//.
    rewrite mulrN mulr1 powRD//; last by rewrite pnatr_eq0 implybT.
    rewrite mulrC; f_equal.
    rewrite exp.powRN.
    by rewrite logK// ltr0n.
  + exact/success_factor_bound_part2.
- by rewrite mulr0 powRr0; exact: success_factor_bound_part1.
Qed.

End typed_success_factor_bound_sect.

(* TODO: move *)
Section rExtrema.
Variables (R : realType) (I : finType) (i0 : I) (F : I -> R).

Lemma arg_rmax2 : forall j, (F j <= F [arg max_(i > i0) F i]%O)%O.
Proof.
move=> j; case: (@Order.TotalTheory.arg_maxP _ _ I i0 xpredT F isT) => i _.
exact.
Qed.

End rExtrema.

Section typed_success_bound_sect.
Let R := Rdefinitions.R.
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

Let exp_cdiv_bound := fun V => exp_cdiv P V W * success_factor_bound M V P : R.

Let Vmax := [arg max_(V > V0) exp_cdiv_bound V]%O.

Lemma typed_success_bound :
  scha(W, tc) <= n.+1%:R ^+ (#|A| * #|B|) * exp_cdiv_bound Vmax.
Proof.
rewrite (typed_success W Mnot0 tc).
apply (@le_trans _ _ ( \sum_(V|V \in \nu^{B}(P)) exp_cdiv P V W *
    2 `^ (- n%:R *  +| log #|M|%:R * n%:R^-1 - `I(P, V) |))).
  apply: ler_sum => V Vnu.
  rewrite -mulrA ler_wpM2l ?exp_cdiv_ge0//.
  by rewrite /success_factor mulrA; exact: success_factor_ub.
apply (@le_trans _ _ (\sum_(V | V \in \nu^{B}(P)) exp_cdiv P Vmax W *
                    2 `^ (- n%:R * +| log #|M|%:R * n%:R^-1 - `I(P, Vmax)|))).
  apply ler_sum => V HV.
  by move: (@arg_rmax2 _ (P_ n (A, B)) V0
    (fun V => exp_cdiv P V W * success_factor_bound M V P) V).
rewrite big_const iter_addr /success_factor_bound addr0.
rewrite -mulr_natr mulrC ler_wpM2r//.
- by rewrite mulr_ge0 ?powR_ge0 ?exp_cdiv_ge0.
- by rewrite -natrX ler_nat card_nu.
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
  scha(W, c) <= n.+1%:R ^+ #|A| * scha(W, Pmax.-typed_code c).
Proof.
red.
set Pmax := [arg max_(P > P0) scha( W, P .-typed_code c)]%O.
apply (@le_trans _ _ (#| P_ n ( A ) |%:R * scha W (Pmax.-typed_code c))); last first.
  apply ler_wpM2r; first exact/scha_pos.
  by rewrite -natrX ler_nat; exact/(type_counting A n).
apply (@le_trans _ _ (\sum_(P : P_ n ( A )) scha W (P.-typed_code c))); last first.
  rewrite (_ : #| P_ n ( A ) |%:R * scha W (Pmax.-typed_code c) =
             \sum_(P : P_ n ( A )) scha W (Pmax.-typed_code c)); last first.
    by rewrite big_const iter_addr addr0 mulr_natl.
  apply ler_sum => P _.
  by move : (arg_rmax2 P0 (fun P1 : P_ n (A) => scha(W, P1.-typed_code c)) P).
rewrite schaE // -(sum_messages_types c).
rewrite mul1r.
rewrite big_distrr/=.
apply: ler_sum => P _.
rewrite mulrC ler_pdivrMr ?ltr0n//.
rewrite schaE // mul1r -mulrA mulrCA mulVf ?pnatr_eq0 ?gt_eqF//.
apply/(@le_trans _ _ (\sum_(m | m \in enc_pre_img c P)
                     \sum_(y | (dec (P.-typed_code c)) y == Some m)
                     (W ``(|(enc (P.-typed_code c)) m)) y)).
  apply: ler_sum => m Hm.
  apply/eqW/eq_big => tb // _.
  rewrite inE in Hm.
  by rewrite /tcode /= ffunE Hm.
- rewrite mulr1 big_mkcond; apply: ler_sum => //= i _.
  by case: ifPn => // _; exact: sumr_ge0.
Qed.

End success_bound_sect.
