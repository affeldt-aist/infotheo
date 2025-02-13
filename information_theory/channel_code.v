(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix.
From mathcomp Require Import Rstruct reals exp.
Require Import bigop_ext realType_ext realType_ln fdist proba channel.

(**md**************************************************************************)
(* # Definition of a channel code                                             *)
(*                                                                            *)
(* A code is a set of codewords with an encoding and a decoding function:     *)
(* ```                                                                        *)
(*         encT == type of the encoding function                              *)
(*         decT == type of the decoding function                              *)
(*      e(W, c) == probability of error given that the codeword m was sent    *)
(*   echa(W, c) == average probability of error                               *)
(*   scha(W, C) == decoding success rate                                      *)
(* CodeRateType == definition of the set of (code) rates (unit: bits per      *)
(*                 transmission)                                              *)
(* ```                                                                        *)
(*                                                                            *)
(* Lemma:                                                                     *)
(* ```                                                                        *)
(*        schaE == expression of the success rate of decoding                 *)
(* ```                                                                        *)
(******************************************************************************)

Reserved Notation "e( W , c )" (at level 50).
Reserved Notation "echa( W , c )" (at level 50).
Reserved Notation "scha( W , C )" (at level 50).

Declare Scope channel_code_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope proba_scope.
Local Open Scope channel_scope.
Local Open Scope ring_scope.

Import GRing.Theory Num.Theory.

Section code_definition.
Variables (A B M : finType) (n : nat).

Local Open Scope ring_scope.

Definition encT := {ffun M -> 'rV[A]_n}.
Definition decT := {ffun 'rV[B]_n -> option M}.

Record code := mkCode { enc : encT ; dec : decT }.

Definition CodeRate (c : code) : Rdefinitions.R := log (#| M |%:R) / n%:R.

Definition preimC (phi : decT) m := ~: (phi @^-1: xpred1 (Some m)).

Definition ErrRateCond (W : `Ch(A, B)) c m :=
  Pr (W ``(| enc c m)) (preimC (dec c) m).

Local Notation "e( W , c )" := (ErrRateCond W c) (at level 50).

Definition CodeErrRate (W : `Ch(A, B)) c :=
  (#| M |%:R^-1 * \sum_(m in M) e(W, c) m)%R.

Local Notation "echa( W , c )" := (CodeErrRate W c) (at level 50).

Lemma echa_ge0 (HM : (0 < #| M |)%nat) W (c : code) : 0 <= echa(W , c).
Proof.
apply/mulr_ge0.
- by rewrite invr_ge0.
- by apply/sumr_ge0 => ? _; exact: sumr_ge0.
Qed.

Lemma echa_le1 (HM : (0 < #| M |)%nat) W (c : code) : echa(W , c) <= 1.
Proof.
rewrite /CodeErrRate ler_pdivrMl ?ltr0n// mulr1.
rewrite -sum1_card natr_sum.
by apply: ler_sum => m _; exact: Pr_le1.
Qed.

Definition scha (W : `Ch(A, B)) (c : code) := (1 - echa(W , c))%R.

Local Notation "scha( W , C )" := (scha W C).

Hypothesis Mnot0 : (0 < #|M|)%nat.

Lemma scha_pos (W : `Ch(A, B)) (c : code) : 0 <= scha(W, c).
Proof. by rewrite /scha; rewrite subr_ge0; exact/echa_le1. Qed.

Lemma schaE (W : `Ch(A, B)) (c : code) :
  scha(W, c) = (1 / #|M|%:R *
    \sum_(m : M) \sum_(tb | dec c tb == Some m) (W ``(| enc c m)) tb)%R.
Proof.
set rhs := (\sum_(m | _ ) _)%R.
have {rhs}-> : rhs = (\sum_(m in M) (1 - e(W, c) m))%R.
  apply eq_bigr => i Hi; rewrite -Pr_to_cplt.
  by apply eq_bigl => t /=; rewrite inE.
set rhs := (\sum_(m | _ ) _)%R.
have {rhs}-> : rhs = (#|M|%:R - \sum_(m in M) e(W, c) m)%R.
  rewrite /rhs {rhs} big_split /= big_morph_oppr; congr +%R.
  by rewrite -sum1_card natr_sum.
rewrite mulrDr -mulrA mulVf ?mulr1 ?pnatr_eq0 ?gtn_eqF// mul1r.
by rewrite mulrN//.
Qed.

End code_definition.

Notation "e( W , c )" := (ErrRateCond W c) : channel_code_scope.
Notation "echa( W , c )" := (CodeErrRate W c) : channel_code_scope.
Notation "scha( W , C )" := (scha W C) : channel_code_scope.

Record CodeRateType := mkCodeRateType {
  rate :> Rdefinitions.R ;
  _ : exists n d, (0 < n)%nat /\ (0 < d)%nat /\ rate = log n%:R / d%:R }.
