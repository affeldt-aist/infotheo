From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*                            Key Type Definition                              *)
(* ========================================================================== *)

Section key_type_def.

Inductive key_type := Dec | Enc.

Definition key_type_eqb_subproof (k1 k2: key_type) : { k1 = k2 } + { k1 <> k2 }.
Proof. decide equality. Defined.

Definition key_type_eqb (k1 k2: key_type) : bool :=
  if key_type_eqb_subproof k1 k2 then true else false. 

Lemma key_type_eqP : Equality.axiom key_type_eqb.
Proof.
move=> k1 k2.
rewrite /key_type_eqb.
by case: key_type_eqb_subproof => /= H;constructor.
Qed.

HB.instance Definition _ := hasDecEq.Build key_type key_type_eqP.

Definition key_type_to_nat (a : key_type) : nat :=
  match a with Dec => 0 | Enc => 1 end.

Definition nat_to_key_type (a : nat) : key_type :=
  match a with 0 => Dec | _ => Enc end.

Lemma key_type_natK : cancel key_type_to_nat nat_to_key_type.
Proof. by case. Qed.

HB.instance Definition _ : isCountable key_type := CanIsCountable key_type_natK.

Definition key_type_enum := [:: Dec; Enc].

Lemma key_type_enumP : Finite.axiom key_type_enum.
Proof. by case. Qed.

HB.instance Definition _ := isFinite.Build key_type key_type_enumP.

End key_type_def.