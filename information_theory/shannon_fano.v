(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import all_ssreflect ssralg fingroup zmodp poly ssrnum.
Require Import Reals.
Require Import ssrZ ssrR logb Reals_ext Rbigop ssr_ext proba entropy kraft.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.

(* NB(rei): redefine kraft_cond in R instead of with an rcfType *)
(* TODO: use mathcomp.analysis? or build an ad-hoc interface to bridge R and rcfType as a temporary fix? *)
Definition kraft_condR (T : finType) (sizes : seq nat) :=
  let n := size sizes in
  (\sum_(i < n) #|T|%:R^-(nth O sizes i) <= (1 : R))%R.

Local Open Scope proba_scope.

Module Encoding.
Record t (A T : finType) := mk {
  f :> {ffun A -> seq T};
  f_inj : injective f }.
End Encoding.
Coercion encoding_coercion (A T : finType) (c : Encoding.t A T) : {ffun A -> seq T} :=
 let: @Encoding.mk _ _ f _ := c in f.

Section shannon_fano_def.

Variables (A T : finType) (P : {fdist A}).

Local Open Scope zarith_ext_scope.

Definition is_shannon_fano (f : Encoding.t A T) :=
  forall s, size (f s) = '| ceil (Log (INR #|T|) (1 / P s)%R) |.

End shannon_fano_def.

Section shannon_fano_is_kraft.

Variables (A : finType) (P : {fdist A}).
Hypothesis Pr_pos : forall s, P s != 0.

Let a : A. by move/card_gt0P: (fdist_card_neq0 P) => /sigW [i]. Qed.

Variable t' : nat.
Let t := t'.+2.
Let T := [finType of 'I_t].
Variable (f : Encoding.t A T).

Let sizes := [seq (size \o f) a| a in A].
Lemma shannon_fano_is_kraft : is_shannon_fano P f -> kraft_condR T sizes.
Proof.
move=> H.
rewrite /kraft_condR -(FDist.pmf1 P).
rewrite /sizes size_map.
rewrite (eq_bigr (fun i:'I_(size(enum A)) => #|'I_t|%:R ^- size (f (nth a (enum A) i)))); last first.
  move=> i _; by rewrite /= (nth_map a).
rewrite -(big_mkord xpredT (fun i => #|T|%:R ^- size (f (nth a (enum A) i)))).
rewrite -(big_nth a xpredT (fun i => #|'I_t|%:R ^- size (f i))).
rewrite enumT.
apply ler_rsum => i _.
rewrite H.
have Pi0 : 0 < P i by apply/ltRP; rewrite lt0R Pr_pos; exact/leRP.
apply (@leR_trans (Exp #|T|%:R (- Log #|T|%:R (1 / P i)))); last first.
  rewrite div1R LogV //.
  rewrite oppRK LogK //; first exact/leRR.
  by rewrite (_ : 1 = 1%:R) // ltR_nat card_ord.
rewrite pow_Exp; last by apply ltR0n; rewrite card_ord.
rewrite Exp_Ropp.
apply/leR_inv/Exp_le_increasing => //.
  by rewrite (_ : 1 = 1%:R) // ltR_nat card_ord.
rewrite INR_Zabs_nat; last first.
  case/boolP : (P i == 1) => [/eqP ->|Pj1].
    by rewrite divR1 Log_1 /ceil fp_R0 eqxx /=; apply/Int_part_pos/leRR.
  apply/leR0ceil/ltRW/ltR0Log.
  by rewrite (_ : 1 = 1%:R) // ltR_nat card_ord.
  rewrite div1R invR_gt1 // ltR_neqAle; split => //; exact/eqP.
by set x := Log _ _; case: (ceilP x).
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

Let T := [finType of 'I_2].
Variable f : Encoding.t A T.

Local Open Scope entropy_scope.

Lemma shannon_fano_average_entropy : is_shannon_fano P f ->
  average P f < `H P  + 1.
Proof.
move=> H; rewrite /average.
apply (@ltR_leR_trans (\sum_(x in A) P x * (- Log (INR #|T|) (P x) + 1))).
  apply ltR_rsum; [exact: fdist_card_neq0|move=> i].
  apply ltR_pmul2l.
    apply/ltRP; rewrite lt0R Pr_pos /=; exact/leRP.
  rewrite H.
  rewrite (_ : INR #|T| = 2) // ?card_ord // -!/(log _).
  set x := log _; case: (ceilP x) => _ Hx.
  have Pi0 : 0 < P i by apply/ltRP; rewrite lt0R Pr_pos /=; exact/leRP.
  rewrite INR_Zabs_nat; last first.
    apply/leR0ceil.
    rewrite /x div1R /log LogV //.
    apply oppR_ge0.
    by rewrite -(Log_1 2); apply Log_increasing_le.
  case: (ceilP x) => _.
  by rewrite -LogV // -/(log _) -(div1R _) /x.
evar (h : A -> R).
rewrite (eq_bigr h); last first.
  move=> i _; rewrite mulRDr mulR1 mulRN  /h; reflexivity.
rewrite {}/h big_split /=; apply leR_add.
  apply Req_le.
  rewrite /entropy big_morph_oppR; apply eq_bigr => i _.
  by rewrite card_ord (_ : INR 2 = 2).
rewrite FDist.pmf1; exact/leRR.
Qed.

End shannon_fano_suboptimal.

(* wip *)
Section kraft_code_is_shannon_fano.

Variables (A : finType) (P : {fdist A}).

Variable (t' : nat).
Let n := #|A|.-1.+1.
Let t := t'.+2.
Let T := [finType of 'I_t].
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
rewrite -(@nth_uniq _ [::] C (enum_rank x) (enum_rank y)) //; last first.
  rewrite /C /ACode /= /acode map_inj_uniq //.
  exact/enum_uniq.
  exact/injective_sigma.
rewrite /C /ACode /= /acode size_map size_enum_ord prednK //.
exact: (fdist_card_neq0 P).
rewrite /C /ACode /= /acode size_map size_enum_ord prednK //.
exact: (fdist_card_neq0 P).
Qed.

Let f := Encoding.mk f_inj.

End kraft_code_is_shannon_fano.
