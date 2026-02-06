(******************************************************************************)
(*                                                                            *)
(* Homomorphic Encryption: Party-Labeled Types                                *)
(*                                                                            *)
(* This file provides party-labeled encryption types for protocol proofs,     *)
(* used by dumas2017dual/dsdp/.                                               *)
(*                                                                            *)
(* == Architecture ==                                                         *)
(*                                                                            *)
(*   AHEAlgebra structure (defined using Hierarchy Builder):                  *)
(*   - HETypes bundles: party, plain, rand, cipher, party_cipher, pkey        *)
(*   - isEncDec mixin: enc, dec, key, dec_correct                             *)
(*   - isAHEnc mixin: Emul, Epow, morphism_2 properties                       *)
(*   - isAHEAlgebra mixin: assoc, comm, id properties                         *)
(*                     |               \                                      *)
(*                     v                v                                     *)
(*            Benaloh_Party_AHE    Paillier_Party_AHE                         *)
(*               ct = 'Z_n        ct = 'Z_{n²}                                *)
(*               Emul = *         Emul = *                                    *)
(*               Epow = ^+        Epow = ^+                                   *)
(*                                                                            *)
(* == This File ==                                                            *)
(*                                                                            *)
(*   party type             - protocol participant type                       *)
(*   Party_Enc_Types        - idealized enc = (party * msg) for DSDP proofs   *)
(*   p.-enc, p.-key types   - type-level party tagging for entropy proofs     *)
(*                                                                            *)
(* == Related Files ==                                                        *)
(*                                                                            *)
(*   he_types.v             - HETypes and key_type type                       *)
(*   enc_dec.v              - isEncDec mixin                                  *)
(*   ahe_enc.v              - isAHEnc mixin (morphism_2 style)                *)
(*   ahe_algebra.v          - isAHEAlgebra mixin and AHEAlgebra               *)
(*   benaloh1994/benaloh_party_ahe.v - Benaloh Party_AHE instance             *)
(*   paillier1999/paillier_party_ahe.v - Paillier Party_AHE instance          *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import spp_proba spp_entropy.

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

Reserved Notation "u *h w" (at level 40).
Reserved Notation "u ^h w" (at level 40).

(* AHE types and structures *)
Require Export he_types.
Require Export enc_dec.
Require Export ahe_enc.
Require Export ahe_algebra.

(* ========================================================================== *)
(*                          Party and Type Definitions                         *)
(* ========================================================================== *)

Section party_id_def.

(* party_id: concrete party identifiers for DSDP protocol.
   Named party_id to avoid shadowing HETypes.party field accessor. *)
Inductive party_id := Alice | Bob | Charlie | NoParty.

Definition party_id_eqb_subproof (p1 p2: party_id) : { p1 = p2 } + { p1 <> p2 }.
Proof. decide equality. Defined.

Definition party_id_eqb (p1 p2: party_id) : bool :=
  if party_id_eqb_subproof p1 p2 then true else false. 

Lemma party_id_eqP : Equality.axiom party_id_eqb.
Proof.
move=> p1 p2.
rewrite /party_id_eqb.
by case: party_id_eqb_subproof => /= H;constructor.
Qed.

HB.instance Definition _ := hasDecEq.Build party_id party_id_eqP.

Definition party_id_to_nat (a : party_id) : nat :=
  match a with Alice => 0 | Bob => 1 | Charlie => 2 | NoParty => 3 end.

Definition nat_to_party_id (a : nat) : party_id :=
  match a with 0 => Alice | 1 => Bob | 2 => Charlie | _ => NoParty end.

Lemma party_id_natK : cancel party_id_to_nat nat_to_party_id.
Proof. by case. Qed.

HB.instance Definition _ : isCountable party_id := CanIsCountable party_id_natK.

Definition party_id_enum := [:: Alice; Bob; Charlie; NoParty].

Lemma party_id_enumP : Finite.axiom party_id_enum.
Proof. by case. Qed.

HB.instance Definition _ := isFinite.Build party_id party_id_enumP.

End party_id_def.

Notation "'n(' w ')' " := (party_id_to_nat w).

(* ========================================================================== *)
(*                   Party-Labeled Encryption Types (for DSDP)                 *)
(* ========================================================================== *)

(* This section provides the basic party-labeled encryption types and operations
   used by the DSDP protocol proofs. This is an idealized model where
   enc = (party * msg), enabling information-theoretic proofs with the
   E_enc_unif and E_enc_inde axioms.

   For concrete encryption (Benaloh, Paillier), see sections below. *)

Section Party_Enc_Types.

Variable party : finType.
Variable msg : finComNzRingType.

(* Idealized party-labeled encryption types.
   Prefixed with party_ to avoid shadowing enc/Emul/Epow from HB mixins. *)
Definition party_enc := (party * msg)%type.
Definition party_pkey := (party * key_type * msg)%type.

Definition party_E i m : party_enc := (i, m).
Definition party_K i k m : party_pkey := (i, k, m).

Definition party_D (dk : party_pkey) (e : party_enc) : option msg :=
  match dk, e with
  | (i, k, _), (j, m) => if (i == j) && (k == Dec) then Some m else None
  end.

Definition party_Emul (e1 e2 : party_enc) : party_enc := 
  match (e1, e2) with
  | ((i1, m1), (i2, m2)) => if i1 == i2 then party_E i1 (m1 + m2) else party_E i1 0
  end.

Definition party_Epow (e : party_enc) (m2 : msg) : party_enc :=
  match e with
  | (i, m1) => party_E i (m1 * m2)
  end.

End Party_Enc_Types.

Section party_key_def.


(* Need something like {RV P -> Alice.-key Dec T} in view;
   `T` means any type of the key's value.
*)

Variant party_key (p : party_id) (k : key_type) (T : Type) : Type :=
  KeyOf of T.

Definition party_key_v p k T (pk : party_key p k T) : T :=
  let 'KeyOf v := pk in v.

Variable (p : party_id) (k : key_type)(T : Type).

HB.instance Definition _ := [isNew for @party_key_v p k T].

End party_key_def.

Notation "p .-key k" := (party_key p k)
  (at level 2, format "p .-key k") : type_scope.

Coercion tuple_of_party_key p k T (pk : p.-key k T) : (party_id * key_type * T) :=
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

Variable (p : party_id)(k : key_type)(T : finType).

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

Variant enc_for (p : party_id) (T : Type) : Type :=
  EncFor of T.

Variable (p : party_id) (T : Type).

Definition enc_for_v p T (e : enc_for p T) : T :=
  let 'EncFor v := e in v.

HB.instance Definition _ := [isNew for @enc_for_v p T].

End enc_type_def.

Notation "p .-enc" := (enc_for p)
  (at level 2, format "p .-enc") : type_scope.

Notation "{ 'enc_for' p 'of' T }" := (p.-enc T : predArgType)
  (at level 0, only parsing) : type_scope.

Coercion tuple_of_enc_for p T (e : p.-enc T) : (party_id * T) :=
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

Definition E' (T : Type) (p : party_id) (t : T) : p.-enc T :=
  EncFor p t.

Variable (p : party_id) (T : finType).

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

Context {R : realType}.
Variables (T : finType)(P : R.-fdist T).

Hypothesis E_enc_unif : forall (T : finType) (P : R.-fdist T)
 (A : finType) (p : party_id) (X : {RV P -> p.-enc A}) (n : nat)
 (card_A : #|A| = n.+1),
   `p_X = fdist_uniform (card_enc_for' p card_A).

Hypothesis E_enc_inde : forall (A B : finType) (p : party_id)
  (X : {RV P -> p.-enc A}) (Y : {RV P -> B}),
  P |= X _|_ Y.
(* TODO: what if B is (p.-enc A) ? Whether we need a way to
   judge if B is (p.-enc A) or not?
*)

(*
  "Ciphertext conditioning contract":
  if `E` is a fresh encryption value (uniform over `p.-enc B` and independent
  from everything else), then conditioning on `E` does not change the
  conditional entropy of `Z` given `X`.
  The hypothesis `(forall x e, Pr[[X,E]=(x,e)] != 0)` is a technical condition
  to make all the conditional probabilities `Pr[ Z=c | [X,E]=(x,e) ]` well-defined
  in the cpr/centropy lemmas used below.
*)
Lemma E_enc_ce_contract (A B C : finType) (p : party_id)
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

(*
  Methodology note (two-layer justification for HE-based SMC proofs)

  This development uses homomorphic encryption through an *idealized* interface:
  ciphertext random variables are postulated to be (1) uniform over the ciphertext
  type and (2) independent of all other random variables (see `E_enc_unif`,
  `E_enc_inde`). Under these information-theoretic axioms we can carry out clean
  Shannon-entropy calculations (e.g. dropping fresh ciphertexts from conditioning
  as in `E_enc_ce_contract`) to prove protocol-level secrecy/correctness
  properties.

  Computational HE security is accounted for in a *second layer* (not in this
  file): one proves a refinement/realization theorem showing that a concrete HE
  scheme (with computational indistinguishability guarantees) implements the
  ideal interface up to negligible error. This keeps protocol reasoning modular:
  the SMC argument is proved once for the ideal primitive, and separately linked
  to concrete assumptions via a standard reduction.
*)
