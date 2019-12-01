(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg matrix.
Require Import Reals.
Require Import ssrR Reals_ext logb fdist.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.

(** * Definition of a source code *)

Section scode_definition.

Variables (A : finType) (B : Type) (k n : nat).

(** Types for the source encoder and source decoder: *)
Definition encT := 'rV[A]_k -> B.

Definition decT := B -> 'rV[A]_k.

Record scode := mkScode { enc : encT ; dec : decT }.

Variable f : 'rV[A]_n -> B.
Variable P : fdist A.

End scode_definition.

Local Open Scope proba_scope.

Section scode_vl_definition.

Variables (A : finType) (k n : nat).

Definition scode_vl := scode A (seq bool) k.

Variables (f : 'rV[A]_n -> seq bool) (P : fdist A).

Definition E_leng_cw := `E_(P `^ n) (INR \o size \o f).

End scode_vl_definition.

Section scode_fl_definition.

Variables (A : finType) (k n : nat).

(** Definition of a source code: *)

Definition scode_fl := scode A 'rV[bool]_n k.

Definition SrcRate (sc : scode_fl) := INR n / INR k.

End scode_fl_definition.

Section code_error_rate.

Variables (A : finType) (B : Type) (P : fdist A).
Variables (k : nat) (sc : scode A B k).

(** Error rate of a source code: *)

Definition SrcErrRate := Pr (P `^ k) [set ta | dec sc (enc sc ta) != ta].

End code_error_rate.

Notation "esrc( P , sc )" := (SrcErrRate P sc) (at level 40) : source_code_scope.

Section extension.

Variables (A : finType) (B : Type).

Definition extension (f : A -> seq B) : seq A -> seq B :=
  fun a => flatten (map f a).

Definition uniquely_decodable (f : A -> seq B):= injective (extension f).

Lemma uniq_dec_inj  (f : A -> seq B) : uniquely_decodable f -> injective f.
Proof.
rewrite /uniquely_decodable/extension.
move=> f_uniq a1 a2 eq_f1_f2.
move:(f_uniq [:: a1] [:: a2]); rewrite /= !cats0.
by move=>tmp; move/tmp:eq_f1_f2=>[].
Qed.

End extension.
