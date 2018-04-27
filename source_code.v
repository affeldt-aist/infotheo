(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import Reals Fourier.
Require Import Reals_ext logb proba.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Definition of a source code *)
Section scode_definition.

Variables (A : finType) (B : Type).
Variables k n : nat.

(** Types for the source encoder and source decoder: *)
Definition encT := 'rV[A]_k -> B.

Definition decT := B -> 'rV[A]_k.

Record scode := mkScode { enc : encT ; dec : decT }.

Variable f : 'rV[A]_n -> B.
Variable P : dist A.

End scode_definition.

Local Open Scope proba_scope.


Section scode_vl_definition.

Variable A : finType.
Variables k n : nat.

Definition scode_vl := scode A (seq bool) k.

Variable f : 'rV[A]_n -> seq bool.
Variable P : dist A.

Definition E_leng_cw := `E (mkRvar (P `^ n) (INR \o size \o f)).

End scode_vl_definition.

Section scode_fl_definition.

Variable A : finType.
Variables k n : nat.

(** Definition of a source code: *)

Definition scode_fl := scode A 'rV[bool]_n k.

Definition SrcRate (sc : scode_fl) := INR n / INR k.

End scode_fl_definition.

Section code_error_rate.

Variable A : finType.
Variable B : Type.
Variable P : dist A.
Variables k : nat.
Variable sc : scode A B k.

(** Error rate of a source code: *)

Definition SrcErrRate := Pr (P `^ k) [set ta | dec sc (enc sc ta) != ta].

End code_error_rate.

Notation "esrc( P , sc )" := (SrcErrRate P sc) (at level 40) : source_code_scope.

Section extension.

Variable A : finType.
Variable B : Type.

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
