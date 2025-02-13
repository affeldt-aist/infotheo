(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix.
From mathcomp Require Import Rstruct reals.
Require Import realType_ln fdist proba.

(**md**************************************************************************)
(* # Definition of a source code                                              *)
(*                                                                            *)
(* ```                                                                        *)
(*     encT, decT == types for the source encoder and source decoder          *)
(*       scode_fl == definition of a fixed-length source code                 *)
(* esrc( P , sc ) == error rate of the source code sc                         *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Declare Scope source_code_scope.

Section scode_definition.
Variables (A : finType) (B : Type) (k : nat).

Definition encT := 'rV[A]_k -> B.

Definition decT := B -> 'rV[A]_k.

Record scode := mkScode { enc : encT ; dec : decT }.

End scode_definition.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Section scode_vl_definition.
Let R := Rdefinitions.R.
Variables (A : finType) (k n : nat).

Definition scode_vl := scode A (seq bool) k.

Variables (P : R.-fdist A) (f : {RV (P `^ n) -> seq bool}).

Definition E_leng_cw := `E (((fun x => x%:R)%R \o size) `o f).

End scode_vl_definition.

Section scode_fl_definition.
Let R := Rdefinitions.R.
Variables (A : finType) (k n : nat).

Definition scode_fl := scode A 'rV[bool]_n k.

Definition SrcRate (sc : scode_fl) : R := (n%:R / k%:R)%R.

End scode_fl_definition.

Section code_error_rate.
Let R := Rdefinitions.R.
Variables (A : finType) (B : Type) (P : R.-fdist A).
Variables (k : nat) (sc : scode A B k).

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
