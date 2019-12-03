(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg matrix.
Require Import Reals.
Require Import Reals_ext ssrR logb Rbigop fdist channel.

(******************************************************************************)
(*                        Definition of a channel code                        *)
(*                                                                            *)
(* A code is a set of codewords with an encoding and a decoding function:     *)
(*         encT == type of the encoding function                              *)
(*         decT == type of the decoding function                              *)
(*      e(W, c) == probability of error given that the codeword m was sent    *)
(*   echa(W, c) == average probability of error                               *)
(*   scha(W, C) == decoding success rate                                      *)
(* CodeRateType == definition of the set of (code) rates (unit: bits per      *)
(*                 transmission)                                              *)
(*                                                                            *)
(* Lemma:                                                                     *)
(*        schaE == expression of the success rate of decoding                 *)
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
Local Open Scope R_scope.

Section code_definition.
Variables (A B M : finType) (n : nat).

Local Open Scope ring_scope.

Definition encT := {ffun M -> 'rV[A]_n}.
Definition decT := {ffun 'rV[B]_n -> option M}.

Record code := mkCode { enc : encT ; dec : decT }.

Definition CodeRate (c : code) := (log (INR #| M |) / INR n)%R.

Definition preimC (phi : decT) m := ~: (phi @^-1: xpred1 (Some m)).

Definition ErrRateCond (W : `Ch(A, B)) c m :=
  Pr (W ``(| enc c m)) (preimC (dec c) m).

Local Notation "e( W , c )" := (ErrRateCond W c) (at level 50).

Definition CodeErrRate (W : `Ch(A, B)) c :=
  (1 / #| M |%:R * \sum_(m in M) e(W, c) m)%R.

Local Notation "echa( W , c )" := (CodeErrRate W c) (at level 50).

Lemma echa_ge0 (HM : (0 < #| M |)%nat) W (c : code) : 0 <= echa(W , c).
Proof.
apply mulR_ge0.
- apply divR_ge0; [exact/Rle_0_1| exact/ltR0n].
- apply: rsumr_ge0 => ? _; exact: rsumr_ge0.
Qed.

Lemma echa_le1 (HM : (0 < #| M |)%nat) W (c : code) : echa(W , c) <= 1.
Proof.
rewrite /CodeErrRate div1R.
apply (@leR_pmul2l (INR #|M|)); first exact/ltR0n.
rewrite mulRA mulRV ?INR_eq0' -?lt0n // mul1R -iter_addR -big_const.
apply: ler_rsum => m _; exact: Pr_1.
Qed.

Definition scha (W : `Ch(A, B)) (c : code) := (1 - echa(W , c))%R.

Local Notation "scha( W , C )" := (scha W C).

Hypothesis Mnot0 : (0 < #|M|)%nat.

Lemma scha_pos (W : `Ch(A, B)) (c : code) : 0 <= scha(W, c).
Proof. rewrite /scha; rewrite subR_ge0; exact/echa_le1. Qed.

Lemma schaE (W : `Ch(A, B)) (c : code) :
  scha(W, c) = (1 / #|M|%:R *
    \sum_(m : M) \sum_(tb | dec c tb == Some m) (W ``(| enc c m)) tb)%R.
Proof.
set rhs := (\sum_(m | _ ) _)%R.
have {rhs}-> : rhs = (\sum_(m in M) (1 - e(W, c) m))%R.
  apply eq_bigr => i Hi; rewrite -Pr_to_cplt.
  apply eq_bigl => t /=; by rewrite inE.
set rhs := (\sum_(m | _ ) _)%R.
have {rhs}-> : rhs = (#|M|%:R - \sum_(m in M) e(W, c) m)%R.
  by rewrite /rhs {rhs} big_split /= big_const iter_addR mulR1 -big_morph_oppR.
by rewrite mulRDr -mulRA mulVR ?mulR1 ?INR_eq0' -?lt0n // mulRN.
Qed.

End code_definition.

Notation "e( W , c )" := (ErrRateCond W c) : channel_code_scope.
Notation "echa( W , c )" := (CodeErrRate W c) : channel_code_scope.
Notation "scha( W , C )" := (scha W C) : channel_code_scope.

Record CodeRateType := mkCodeRateType {
  rate :> R ;
  _ : exists n d, (0 < n)%nat /\ (0 < d)%nat /\ rate = log (INR n) / INR d }.
