(******************************************************************************)
(*                                                                            *)
(* Idealized Homomorphic Encryption Model                                     *)
(*                                                                            *)
(* This file defines an IDEALIZED model of homomorphic encryption for use in  *)
(* information-theoretic and entropy-based proofs.                            *)
(*                                                                            *)
(* == Related Files ==                                                        *)
(*                                                                            *)
(*   he_sig.v - HE_SIG module signature (shared interface)                    *)
(*   benaloh1994/benaloh_he_instance.v - Benaloh_HE functor                   *)
(*   paillier1999/paillier_he_instance.v - Paillier_HE functor                *)
(*                                                                            *)
(* == This File ==                                                            *)
(*                                                                            *)
(*   Ideal_HE module - ciphertext = plaintext, for abstract proofs            *)
(*   Party/Key/Enc types and axioms for entropy proofs                        *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import smc_proba smc_entropy.
Import smc_entropy.smc_entropy_proofs.

Import GRing.Theory.
Import Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

Local Definition R := Rdefinitions.R.

Reserved Notation "u *h w" (at level 40).
Reserved Notation "u ^h w" (at level 40).

(* HE_SIG module signature is defined in he_sig.v *)
From infotheo Require Export homomorphic_encryption.he_sig.

(* ========================================================================== *)
(*                      Note on Ideal vs Concrete HE                           *)
(* ========================================================================== *)

(* The HE_SIG interface is designed for CONCRETE cryptographic schemes like
   Benaloh and Paillier, where:
   - ct is different from msg (ciphertext hides the plaintext)
   - Ring multiplication on ct corresponds to addition on msg
   - The homomorphic property: enc(m1) * enc(m2) = enc(m1 + m2)
   
   An "ideal" model where enc(m) = m cannot implement HE_SIG because
   m1 * m2 ≠ m1 + m2 for general rings.
   
   For information-theoretic proofs, we use Section he_ideal below,
   which defines explicit Emul/Epow functions rather than relying on
   ring operations. This ideal model is compatible with the p.-enc type
   for entropy-based security proofs.
   
   For concrete HE implementations, use:
   - Benaloh_HE (benaloh1994/benaloh_he_instance.v)
   - Paillier_HE (paillier1999/paillier_he_instance.v) *)

(* ========================================================================== *)
(*                       Party-Labeled HE Functor                              *)
(* ========================================================================== *)

(* Party_HE wraps an HE_SIG with party labels for multi-party protocols.
   
   Given HE_SIG with:
     enc : msg -> rand -> ct
   
   Party_HE provides:
     penc = (party * ct)         -- party-labeled ciphertext
     E : party -> msg -> rand -> penc
     pEmul, pEpow using HE operations
   
   The p.-enc type (defined later) provides type-level party tagging. *)

Module Party_HE (HE : HE_SIG).
  
  (* Party-labeled ciphertext: (party, ciphertext) *)
  Definition penc (P : finType) := (P * HE.ct)%type.
  
  (* Party-labeled encryption *)
  Definition E (P : finType) (i : P) (m : HE.msg) (r : HE.rand) : penc P :=
    (i, HE.enc m r).
  
  (* Homomorphic multiplication on party-labeled ciphertexts.
     Only operates if parties match. *)
  Definition pEmul (P : finType) (e1 e2 : penc P) : penc P :=
    match e1, e2 with
    | (i1, c1), (i2, c2) => 
        if i1 == i2 then (i1, c1 * c2) else (i1, 1)  (* 1 = enc(0) ideally *)
    end.
  
  (* Homomorphic exponentiation on party-labeled ciphertexts *)
  Definition pEpow (P : finType) (e : penc P) (k : nat) : penc P :=
    match e with
    | (i, c) => (i, c ^+ k)
    end.
  
  (* Homomorphic properties lift from HE *)
  Lemma pEmul_hom (P : finType) : forall (i : P) (m1 m2 : HE.msg) (r1 r2 : HE.rand),
    exists r, pEmul (E i m1 r1) (E i m2 r2) = E i (m1 + m2) r.
  Proof.
    move=> i m1 m2 r1 r2.
    rewrite /pEmul /E eq_refl.
    case: (HE.Emul_hom m1 m2 r1 r2) => r Hr.
    exists r.
    by rewrite Hr.
  Qed.
  
  Lemma pEpow_hom (P : finType) : forall (i : P) (m : HE.msg) (k : nat) (r : HE.rand),
    exists r', pEpow (E i m r) k = E i (m *+ k) r'.
  Proof.
    move=> i m k r.
    rewrite /pEpow /E.
    case: (HE.Epow_hom m k r) => r' Hr.
    exists r'.
    by rewrite Hr.
  Qed.

End Party_HE.

(* ========================================================================== *)
(*                          Party and Type Definitions                         *)
(* ========================================================================== *)

Section party_def.

Inductive party := Alice | Bob | Charlie | NoParty.

Definition party_eqb_subproof (p1 p2: party) : { p1 = p2 } + { p1 <> p2 }.
Proof. decide equality. Defined.

Definition party_eqb (p1 p2: party) : bool :=
  if party_eqb_subproof p1 p2 then true else false. 

Lemma party_eqP : Equality.axiom party_eqb.
Proof.
move=> p1 p2.
rewrite /party_eqb.
by case: party_eqb_subproof => /= H;constructor.
Qed.

HB.instance Definition _ := hasDecEq.Build party party_eqP.

Definition party_to_nat (a : party) : nat :=
  match a with Alice => 0 | Bob => 1 | Charlie => 2 | NoParty => 3 end.

Definition nat_to_party (a : nat) : party :=
  match a with 0 => Alice | 1 => Bob | 2 => Charlie | _ => NoParty end.

Lemma party_natK : cancel party_to_nat nat_to_party.
Proof. by case. Qed.

HB.instance Definition _ : isCountable party := CanIsCountable party_natK.

Definition party_enum := [:: Alice; Bob; Charlie; NoParty].

Lemma party_enumP : Finite.axiom party_enum.
Proof. by case. Qed.

HB.instance Definition _ := isFinite.Build party party_enumP.

End party_def.

Notation "'n(' w ')' " := (party_to_nat w).

Section key_def.

Inductive key := Dec | Enc.

Definition key_eqb_subproof (k1 k2: key) : { k1 = k2 } + { k1 <> k2 }.
Proof. decide equality. Defined.

Definition key_eqb (k1 k2: key) : bool :=
  if key_eqb_subproof k1 k2 then true else false. 

Lemma key_eqP : Equality.axiom key_eqb.
Proof.
move=> k1 k2.
rewrite /key_eqb.
by case: key_eqb_subproof => /= H;constructor.
Qed.

HB.instance Definition _ := hasDecEq.Build key key_eqP.

Definition key_to_nat (a : key) : nat :=
  match a with Dec => 0 | Enc => 1 end.

Definition nat_to_key (a : nat) : key :=
  match a with 0 => Dec | _ => Enc end.

Lemma key_natK : cancel key_to_nat nat_to_key.
Proof. by case. Qed.

HB.instance Definition _ : isCountable key := CanIsCountable key_natK.

Definition key_enum := [:: Dec; Enc].

Lemma key_enumP : Finite.axiom key_enum.
Proof. by case. Qed.

HB.instance Definition _ := isFinite.Build key key_enumP.

End key_def.

(* ========================================================================== *)
(*                    Ideal Party-Labeled Encryption                           *)
(* ========================================================================== *)

(* This section provides the IDEAL model where ciphertext = plaintext.
   This is equivalent to Party_HE(Ideal_HE(msg)) but written directly
   for compatibility with existing code.
   
   For real HE schemes, use Party_HE(Benaloh_HE) or Party_HE(Paillier_HE). *)

Section he_ideal.

Variable party : finType.
Variable msg : finComNzRingType.

(* In the ideal model, ciphertext = plaintext (no real encryption) *)
Definition enc := (party * msg)%type.
Definition pkey := (party * key * msg)%type.

(* Ideal encryption: just pair party with plaintext *)
Definition E i m : enc := (i, m).
Definition K i k m : pkey := (i, k, m).

(* Decryption (trivial in ideal model) *)
Definition D (k : pkey) (e : enc) : option msg :=
  match k, e with
  | (i, k, _), (j, m) => if (i == j) && (k == Dec) then Some m else None
  end.

(* Homomorphic addition: operates directly on plaintexts *)
Definition Emul (e1 e2 : enc) : enc := 
  match (e1, e2) with
  | ((i1, m1), (i2, m2)) => if i1 == i2 then E i1 (m1 + m2) else E i1 0
  end.

(* Homomorphic scalar multiplication: operates directly on plaintexts *)
Definition Epow (e : enc) (m2 : msg) : enc :=
  match e with
  | (i, m1) => E i (m1 * m2)
  end.

End he_ideal.

Section party_key_def.


(* Need something like {RV P -> Alice.-key Dec T} in view;
   `T` means any type of the key's value.
*)

Variant party_key (p : party) (k : key) (T : Type) : Type :=
  KeyOf of T.

Definition party_key_v p k T (pk : party_key p k T) : T :=
  let 'KeyOf v := pk in v.

Variable (p : party) (k : key)(T : Type).

HB.instance Definition _ := [isNew for @party_key_v p k T].

End party_key_def.

Notation "p .-key k" := (party_key p k)
  (at level 2, format "p .-key k") : type_scope.

Coercion tuple_of_party_key p k T (pk : p.-key k T) : (party * key * T) :=
  let 'KeyOf v := pk in (p, k, v).

Section party_key_types.

HB.instance Definition _ p k (T : eqType) : hasDecEq (p.-key k T) :=
  [Equality of p.-key k T by <:].
HB.instance Definition _ p k (T : choiceType) :=
  [Choice of p.-key k T by <:].
HB.instance Definition _ p k (T : countType) :=
  [Countable of p.-key k T by <:].
HB.instance Definition _ p k (T : finType) :=
  [Finite of p.-key k T by <:].

Variable (p : party)(k : key)(T : finType).

Lemma card_party_key : #|{:p.-key k T}| = #|T|.
Proof.
apply (bij_eq_card (f:=@party_key_v p k T)).
exists (@KeyOf p k T).
by case.
by [].
Qed.

End party_key_types.


Section enc_type_def.

(*
  Because {RV P -> enc} is wrong:
  we have no random variables that output
  (different parties x different messages),
  but only (one fixed party x different messages).
  
  So we need to define a type level label like: {RV P -> Alice.-enc}.
*)

Variant enc_for (p : party) (T : Type) : Type :=
  EncFor of T.

Variable (p : party) (T : Type).

Definition enc_for_v p T (e : enc_for p T) : T :=
  let 'EncFor v := e in v.

HB.instance Definition _ := [isNew for @enc_for_v p T].

End enc_type_def.

Notation "p .-enc" := (enc_for p)
  (at level 2, format "p .-enc") : type_scope.

Notation "{ 'enc_for' p 'of' T }" := (p.-enc T : predArgType)
  (at level 0, only parsing) : type_scope.

Coercion tuple_of_enc_for p T (e : p.-enc T) : (party * T) :=
  let 'EncFor v := e in (p, v).

Section enc_types.

HB.instance Definition _ p (T : eqType) : hasDecEq (p.-enc T) :=
  [Equality of p.-enc T by <:].
HB.instance Definition _ p (T : choiceType) :=
  [Choice of p.-enc T by <:].
HB.instance Definition _ p (T : countType) :=
  [Countable of p.-enc T by <:].
HB.instance Definition _ p (T : finType) :=
  [Finite of p.-enc T by <:].

Definition E' (T : Type) (p : party) (t : T) : p.-enc T :=
  EncFor p t.

Variable (p : party) (T : finType).

Lemma card_enc_for :
  #|{:p.-enc T}| = #|T|.
Proof.
apply (bij_eq_card (f:=@enc_for_v p T)).
exists (@EncFor p T).
by case.
by [].
Qed.

Lemma card_enc_for' : forall (n : nat),
  #|T| = n.+1 -> #|{:p.-enc T}| = n.+1.
Proof. by rewrite card_enc_for. Qed.

End enc_types.

Section enc_lemmas.

Variables (T : finType)(P : R.-fdist T).

Axiom E_enc_unif : forall (T : finType) (P : R.-fdist T)
 (A : finType) (p : party) (X : {RV P -> p.-enc A}) (n : nat)
 (card_A : #|A| = n.+1),
   `p_X = fdist_uniform (card_enc_for' p card_A).

Axiom E_enc_inde : forall (A B : finType) (p : party)
  (X : {RV P -> p.-enc A}) (Y : {RV P -> B}),
  P |= X _|_ Y.
(* TODO: what if B is (p.-enc A) ? Whether we need a way to
   judge if B is (p.-enc A) or not?
*)

Lemma E_enc_ce_removal (A B C : finType) (p : party)
  (X : {RV P -> A})(E : {RV P -> p.-enc B})(Z : {RV P -> C})(n : nat):
  #|B| = n.+1 -> (forall x e, `Pr[ [%X, E] = (x, e)] != 0) ->
  `H(Z | [%X, E]) = `H(Z | X).
Proof.
move => card_B XE_neq0.
have HindeX_E : P |= X _|_ E.
  rewrite inde_RV_sym.
  exact: (E_enc_inde E X).
have Hunif : `p_ E = fdist_uniform (card_enc_for' p card_B).
  exact: (E_enc_unif E card_B).
have HindeXZ_E : P |= [%X, Z] _|_ E.
  rewrite inde_RV_sym.
  exact: (E_enc_inde E [%X, Z]).
apply (cpr_centropy (Y2:=X)(Y3:=E)) => c a b.
have Hpr : `Pr[ Z = c | [%X, E] = (a, b)] = `Pr[ Z = c | X = a].
  have HindeZ_X : P |= E _|_ [%Z, X].
    exact: (E_enc_inde E [%Z, X]).
  rewrite inde_RV_sym in HindeZ_X.
  have H:=(inde_RV2_cinde (X:=Z)(Y:=E)(Z:=X) HindeZ_X).
  pose proof XE_neq0 as EX_neq0.
  move/(_ a b) in EX_neq0. (* Specialize forall...*)
  rewrite pfwd1_pairC in EX_neq0.
  have H2:= (cinde_alt c H EX_neq0).
  rewrite cpr_eq_pairCr.
  exact: H2.
move => ?.
exact: Hpr.
Qed.

End enc_lemmas.
