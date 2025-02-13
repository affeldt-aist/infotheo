(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect all_algebra archimedean.
From mathcomp Require Import Rstruct mathcomp_extra reals exp.
Require Import ssr_ext bigop_ext realType_ext realType_ln fdist entropy kraft.

(**md**************************************************************************)
(* # Shannon-Fano codes                                                       *)
(*                                                                            *)
(* Documented in:                                                             *)
(* - Reynald Affeldt, Jacques Garrigue, and Takafumi Saikawa. Examples of     *)
(*   formal proofs about data compression. International Symposium  on        *)
(*   Information Theory and Its Applications (ISITA 2018), Singapore,         *)
(*    October 28--31, 2018, pages 633--637. IEEE, Oct 2018                    *)
(*                                                                            *)
(* ```                                                                        *)
(*   is_shannon_fano == TODO                                                  *)
(*           average == TODO                                                  *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import Order.POrderTheory Num.Theory GRing.Theory.

Local Open Scope fdist_scope.

Module Encoding.
Record t (A T : finType) := mk {
  f :> {ffun A -> seq T};
  f_inj : injective f }.
End Encoding.
Coercion encoding_coercion (A T : finType) (c : Encoding.t A T) : {ffun A -> seq T} :=
 let: @Encoding.mk _ _ f _ := c in f.

Section shannon_fano_def.
Variables (A T : finType) (P : {fdist A}).

Definition is_shannon_fano (f : Encoding.t A T) :=
  forall s, size (f s) = `| Num.ceil (Log #|T|%:R (P s)^-1%R) |%N.

End shannon_fano_def.

Section shannon_fano_is_kraft.
Variables (A : finType) (P : {fdist A}).
Hypothesis Pr0 : forall s, P s != 0.

Let a : A. by move/card_gt0P: (fdist_card_neq0 P) => /sigW [i]. Qed.

Variable t' : nat.
Let t := t'.+2.
Let T := 'I_t.
Variable (f : Encoding.t A T).

Let sizes := [seq (size \o f) a| a in A].
Lemma shannon_fano_is_kraft : is_shannon_fano P f -> kraft_cond Rdefinitions.R T sizes.
Proof.
move=> H.
rewrite /kraft_cond.
rewrite -(FDist.f1 P) /sizes size_map.
rewrite (eq_bigr (fun i : 'I_(size(enum A)) =>
    #|'I_t|%:R ^- size (f (nth a (enum A) i)))); last first.
  by move=> i _; rewrite /= (nth_map a)// FDist.f1.
rewrite -(big_mkord xpredT (fun i => #|T|%:R ^- size (f (nth a (enum A) i)))).
rewrite -(big_nth a xpredT (fun i => #|'I_t|%:R ^- size (f i))).
rewrite enumT.
apply ler_sum => i _.
rewrite H.
have Pi0 : 0 < P i by rewrite lt0r Pr0/=.
apply (@le_trans _ _ (#|T|%:R `^ (- Log #|T|%:R (P i)^-1))%R); last first.
  by rewrite LogV// opprK natn LogK// card_ord.
rewrite -powR_mulrn; last by rewrite card_ord.
rewrite powRN card_ord lef_pV2// ?posrE ?powR_gt0//.
rewrite gt1_ler_powRr ?ltr1n//.
rewrite (le_trans (ceil_ge _))//.
by rewrite natr_absz// ler_int ler_norm.
Qed.

End shannon_fano_is_kraft.

Section average_length.
Variables (A T : finType) (P : {fdist A}).
Variable f : {ffun A -> seq T}. (* encoding function *)

Definition average := \sum_(x in A) P x * (size (f x))%:R.

End average_length.

Section shannon_fano_suboptimal.
Variables (A : finType) (P : {fdist A}).
Hypothesis Pr_pos : forall s, P s != 0.

Let T := 'I_2.
Variable f : Encoding.t A T.

Local Open Scope entropy_scope.

Lemma shannon_fano_average_entropy : is_shannon_fano P f ->
  average P f < `H P  + 1.
Proof.
move=> H; rewrite /average.
apply (@lt_le_trans _ _ (\sum_(x in A) P x * (- Log #|T|%:R (P x) + 1))).
  apply: ltR_sumR.
    apply: fdist_card_neq0.
    exact: P.
  move=> i.
  rewrite ltr_pM2l//; last by apply/fdist_gt0.
  rewrite H.
  rewrite (_ : #|T|%:R = 2) // ?card_ord // -!/(log _).
  set x := log _.
  rewrite -ltrBlDr.
  rewrite (le_lt_trans _ (gt_pred_ceil _))// ?num_real//.
  rewrite natr_absz.
  rewrite intrD lerB// ler_int.
  rewrite /x logV -?fdist_gt0//.
  rewrite -[leRHS]gez0_abs//.
  rewrite -mathcomp_extra.ceil_ge0//.
  rewrite (@lt_le_trans _ _ 0)// ?ltrN10// lerNr oppr0.
  by rewrite -log1 ler_log// ?posrE// -fdist_gt0.
under eq_bigr do rewrite mulrDr mulr1 mulrN.
rewrite big_split /= FDist.f1 lerD2r.
apply/eqW.
rewrite /entropy big_morph_oppr; apply eq_bigr => i _.
by rewrite card_ord.
Qed.

End shannon_fano_suboptimal.

(* wip *)
Section kraft_code_is_shannon_fano.
Variables (A : finType) (P : {fdist A}).

Variable t' : nat.
Let n := #|A|.-1.+1.
Let t := t'.+2.
Let T := 'I_t.
Variable l : seq nat.
Hypothesis l_n : size l = n.
Hypothesis sorted_l : sorted leq l.

Let C := ACode t' l_n sorted_l.

Lemma f_inj : injective [ffun a : A => nth [::] C (enum_rank a)].
Proof.
move=> x y.
rewrite !ffunE => /eqP xy.
rewrite -(enum_rankK x) -(enum_rankK y); congr enum_val.
apply/ord_inj/eqP.
rewrite -(@nth_uniq _ [::] C (enum_rank x) (enum_rank y)) //.
- rewrite /C /ACode /= /acode size_map size_enum_ord prednK //.
  exact: (fdist_card_neq0 P).
- rewrite /C /ACode /= /acode size_map size_enum_ord prednK //.
  exact: (fdist_card_neq0 P).
- rewrite /C /ACode /= /acode map_inj_uniq //.
    exact/enum_uniq.
  exact/injective_sigma.
Qed.

Let f := Encoding.mk f_inj.

End kraft_code_is_shannon_fano.
