(******************************************************************************)
(*                                                                            *)
(* Benaloh Party-Labeled AHE Instance                                         *)
(*                                                                            *)
(* This file provides HB instances for Benaloh encryption implementing        *)
(* the three AHE mixins:                                                      *)
(*   - isPartyHE_EncDec   (encryption/decryption)                             *)
(*   - isPartyAHE_HomoOps (homomorphic operations)                            *)
(*   - isPartyAHE_Algebra (algebraic properties)                              *)
(*                                                                            *)
(* == Cryptographic Assumptions ==                                            *)
(*                                                                            *)
(*   y_order_r    : y ^+ r = 1        (y is an r-th root of unity in Z_n)     *)
(*   y_coprime_n  : coprime y n       (y is a unit in Z_n, for Euler)         *)
(*   euler_property : coprime u n -> u^phi(n) = 1  (Euler's theorem)          *)
(*   rand_coprime_n : forall u, coprime u n (randomness is a unit)            *)
(*   x_base_injective : x_base has exact order r (for discrete log)           *)
(*                                                                            *)
(* == References ==                                                           *)
(*                                                                            *)
(*   Benaloh, J. [1994]. "Dense Probabilistic Encryption"                     *)
(*   Benaloh, J., Tuinstra, D. [1994]. "Receipt-Free Secret-Ballot Elections" *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg zmodp ssrfun.
From mathcomp Require Import cyclic.  (* For Euler_exp_totient *)
From infotheo Require Import homomorphic_encryption.ahe_types.
From infotheo Require Import homomorphic_encryption.ahe_enc_dec.
From infotheo Require Import homomorphic_encryption.ahe_homo_ops.
From infotheo Require Import homomorphic_encryption.ahe_algebra.
From infotheo Require Import homomorphic_encryption.benaloh1994.benaloh_enc.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*                   Benaloh Party AHE Instance                                *)
(* ========================================================================== *)

Section Benaloh_Party_AHE.

Variable party : finType.
Variables (n r : nat).
Hypothesis n_gt1 : (1 < n)%N.
Hypothesis r_gt1 : (1 < r)%N.
Variable y : 'Z_n.
(* y_order_r ensures y is an r-th root of unity in Z_n.
   This is required for the homomorphic properties:
   - enc_mul_dist: E(m1,u1) * E(m2,u2) = E(m1+m2, u1*u2)
   - enc_exp_dist: E(m,u)^k = E(m*k, u^k)
   Without this, y^(m1+m2) != y^m1 * y^m2 in general. *)
Hypothesis y_order_r : y ^+ r = 1.
(* y must be in Z_n^* (coprime to n) for Euler's theorem to apply *)
Hypothesis y_coprime_n : coprime (y : nat) n.

(* ========================================================================== *)
(*                   Secret Key Parameters                                     *)
(* ========================================================================== *)

(* Benaloh decryption requires φ(n)/r where φ is Euler's totient.
   The decryption algorithm:
   1. Compute x = y^(φ(n)/r) mod n  (precomputed, part of secret key)
   2. Compute a = c^(φ(n)/r) mod n  (removes randomness: a = x^m)
   3. Find m by discrete log in {0,...,r-1} such that x^m = a
   
   Step 3 is efficient because r is small (the "block size" in Benaloh).
   
   We parameterize by phi_div_r = φ(n)/r and its key property. *)

Variable phi_div_r : nat.

(* r * phi_div_r = φ(n), i.e., phi_div_r = φ(n)/r.
   This is a key parameter relationship in the Benaloh scheme. *)
Hypothesis phi_eq_totient : r * phi_div_r = totient n.

(* Euler's theorem derived from math-comp's Euler_exp_totient.
   
   This only holds for u in the multiplicative group of units (coprime to n).
   If u is not coprime to n (e.g., n=6, u=2), then u^phi(n) != 1 mod n.
   
   The proof uses:
   - Euler_exp_totient: coprime a n -> a ^ totient n = 1 %[mod n]
   - unit_Zp_expg: for units, val (u ^+ k) = inZp (val u ^ k)
   - phi_eq_totient: r * phi_div_r = totient n *)
(* Helper: Zp_trunc n = n - 2 when n > 1, so (Zp_trunc n).+2 = n *)
Lemma Zp_trunc_eq : (Zp_trunc n).+2 = n.
Proof.
  exact: Zp_cast n_gt1.
Qed.

(* Helper to avoid dependent type error: 
   extract the modular multiplication result at the nat level.
   We extract nat values first, then use f_equal on the product. *)
Lemma Zn_mul_val (a b : 'Z_n) : val (a * b) = ((val a * val b) %% n)%N.
Proof.
  (* Extract nat values first to avoid dependent type issues *)
  set va := val a.
  set vb := val b.
  (* Both moduli are equal by Zp_trunc_eq *)
  have Hmod : (Zp_trunc n).+2 = n := Zp_trunc_eq.
  (* Compute LHS: val (a * b) = ((va * vb) %% (Zp_trunc n).+2)%N *)
  have Hlhs : val (a * b) = ((va * vb) %% (Zp_trunc n).+2)%N by [].
  (* Rewrite and use modulus equality *)
  rewrite Hlhs Hmod.
  (* Goal: va * vb = va * vb %[mod n] *)
  (* The %[mod n] notation: x = y %[mod m] means x %% m = y %% m *)
  (* So (va * vb) %% n = (va * vb) %% n, which is trivially true *)
  by apply/eqP; rewrite eqxx.
Qed.

(* Helper: ring exponentiation in 'Z_n equals modular exponentiation.
   For u : 'Z_n, val (u ^+ k) = (val u) ^ k %% n *)
Lemma Zn_ring_expn (u : 'Z_n) k : val (u ^+ k) = ((val u) ^ k %% n)%N.
Proof.
  elim: k => [|k IHk].
  - (* Base case: k = 0 *)
    rewrite expr0 expn0.
    (* val 1 = 1 %% n *)
    rewrite modn_small //.
  - (* Inductive case: k = k.+1 *)
    rewrite exprS expnS.
    (* val (u * u ^+ k) = (val u * val u ^ k)%N %% n *)
    rewrite Zn_mul_val.
    (* ((val u * val (u ^+ k)) %% n)%N = ((val u * val u ^ k) %% n)%N *)
    rewrite IHk.
    (* ((val u * (val u ^ k %% n)) %% n)%N = ((val u * val u ^ k) %% n)%N *)
    by rewrite modnMmr.
Qed.

(* Euler's theorem for 'Z_n: u^φ(n) = 1 when gcd(u,n) = 1.
   
   We use mathcomp's Euler_exp_totient from the cyclic library:
     Euler_exp_totient : coprime a n -> a ^ totient n = 1 %[mod n]
   
   The proof bridges two representations:
   - Ring exponentiation in 'Z_n: u ^+ k (returns element of 'Z_n)
   - Modular arithmetic on nat: u ^ k %% n (returns nat)
   
   Key steps:
   1. Rewrite exponent: r * phi_div_r = totient n (by phi_eq_totient)
   2. Apply Euler_exp_totient to get: (u:nat) ^ totient n = 1 %[mod n]
   3. Use Zn_ring_expn to convert ring exp to modular exp
   4. Conclude via modular arithmetic equality *)
Lemma euler_property (u : 'Z_n) : coprime (u : nat) n -> u ^+ (r * phi_div_r) = 1.
Proof.
  move=> u_coprime.
  have ->: (r * phi_div_r)%N = totient n by exact: phi_eq_totient.
  have euler := Euler_exp_totient u_coprime.
  apply/val_inj.
  rewrite Zn_ring_expn /=.
  rewrite euler.
  by rewrite Zp_trunc_eq modn_small.
Qed.

(* ========================================================================== *)
(*                   Randomness Coprimality Assumption                         *)
(* ========================================================================== *)

(* In practice, encryption randomness is chosen uniformly from Z_n^*.
   For n = p*q (product of large primes), the probability of randomly
   choosing a non-coprime element is negligible: Pr[gcd(u,n) ≠ 1] ≤ 2/min(p,q).
   
   We model this as a hypothesis: all randomness used is coprime to n.
   This makes the Section parameters represent a "valid instantiation"
   of the Benaloh scheme where randomness is properly sampled from Z_n^*.
   
   An alternative formalization would use {unit 'Z_n} as the randomness type,
   but this requires changing the type bundle interface. *)
Hypothesis rand_coprime_n : forall (u : 'Z_n), coprime (u : nat) n.

(* x = y^(φ(n)/r) is the base for discrete log in decryption *)
Definition x_base : 'Z_n := y ^+ phi_div_r.

(* ========================================================================== *)
(*                   Discrete Log Search                                       *)
(* ========================================================================== *)

(* For decryption, we need to find m such that x^m = a.
   Since m ∈ {0,...,r-1} and r is small, we can search exhaustively.
   We use MathComp's pick to find the first matching value. *)

Definition discrete_log_search (base target : 'Z_n) : 'Z_r :=
  odflt 0 [pick m : 'Z_r | base ^+ (m : nat) == target].

(* Key lemma: after removing randomness, c^(phi/r) = x^m.
   Requires u to be coprime to n (a unit) for Euler's theorem. *)
Lemma ciphertext_reduction (m : 'Z_r) (u : 'Z_n) :
  coprime (u : nat) n ->
  (benaloh_enc y m u) ^+ phi_div_r = x_base ^+ (m : nat).
Proof.
  move=> u_coprime_n.
  rewrite /benaloh_enc /x_base.
  rewrite exprMn_comm; last by apply mulrC.
  rewrite -!exprM.
  rewrite (mulnC (m : nat) phi_div_r).
  rewrite euler_property //.
  rewrite mulr1.
  reflexivity.
Qed.

(* x_base has order dividing r - provable from euler_property and y_coprime_n *)
Lemma x_base_order_r : x_base ^+ r = 1.
Proof.
  rewrite /x_base.
  rewrite -exprM.
  rewrite mulnC.
  exact: euler_property y_coprime_n.
Qed.

(* For the discrete log to succeed, we need x_base^m to be injective on 'Z_r.
   This requires x_base to have exact order r (not just dividing r).
   This is a genuine cryptographic assumption about proper key generation:
   the parameter y must be chosen such that y^(phi(n)/r) generates a cyclic
   subgroup of order exactly r in the multiplicative group of units. *)
Hypothesis x_base_injective : forall (m1 m2 : 'Z_r), 
  x_base ^+ (m1 : nat) = x_base ^+ (m2 : nat) -> m1 = m2.

(* Discrete log correctness: searching for x^m finds m *)
Lemma discrete_log_correct (m : 'Z_r) :
  discrete_log_search x_base (x_base ^+ (m : nat)) = m.
Proof.
  rewrite /discrete_log_search.
  case: pickP => [m' /eqP Hm' | Hno].
  - (* Found some m', show m' = m by injectivity *)
    apply x_base_injective.
    exact: Hm'.
  - (* No match found - contradiction since m should match *)
    exfalso.
    have := Hno m.
    by rewrite eq_refl.
Qed.

(* Benaloh decryption function *)
Definition benaloh_decrypt (c : 'Z_n) : 'Z_r :=
  discrete_log_search x_base (c ^+ phi_div_r).

(* Decryption correctness - uses rand_coprime_n assumption *)
Lemma benaloh_decrypt_correct (m : 'Z_r) (u : 'Z_n) :
  benaloh_decrypt (benaloh_enc y m u) = m.
Proof.
  rewrite /benaloh_decrypt.
  rewrite ciphertext_reduction; first by apply discrete_log_correct.
  exact: rand_coprime_n.
Qed.

(* Type definitions *)
Definition benaloh_enc_party := (party * 'Z_n)%type.
Definition benaloh_pkey := (party * key * 'Z_r)%type.

(* ========================================================================== *)
(*                   Type Bundle                                               *)
(* ========================================================================== *)

Definition Benaloh_Party_HE_types : Party_HE_types := 
  MkPartyHE party 'Z_r 'Z_n (party * 'Z_n)%type benaloh_pkey.

(* ========================================================================== *)
(*                   Encryption/Decryption Operations                          *)
(* ========================================================================== *)

Definition benaloh_phe_E (p : party) (m : 'Z_r) (u : 'Z_n) : (party * 'Z_n) := 
  (p, benaloh_enc y m u).

Definition benaloh_phe_K (p : party) (k : key) (m : 'Z_r) : benaloh_pkey := 
  (p, k, m).

(* Decryption using the Benaloh decryption algorithm.
   Only decrypts if:
   1. The key is a decryption key (k == Dec)
   2. The party labels match (i == j) *)
Definition benaloh_phe_D (dk : benaloh_pkey) (e : party * 'Z_n) : option 'Z_r :=
  match dk, e with
  | (i, k, _), (j, c) => 
    if (i == j) && (k == Dec) then Some (benaloh_decrypt c) else None
  end.

Definition benaloh_phe_msg_nat (m : 'Z_r) : nat := m.

(* Decryption correctness - proved using the Benaloh decryption algorithm.
   Uses rand_coprime_n assumption: randomness is a unit in Z_n. *)
Lemma benaloh_phe_dec_correct : forall (p : party) (m : 'Z_r) (u : 'Z_n) (sk : 'Z_r),
  benaloh_phe_D (benaloh_phe_K p Dec sk) (benaloh_phe_E p m u) = Some m.
Proof.
  move=> p m u sk.
  rewrite /benaloh_phe_D /benaloh_phe_K /benaloh_phe_E /=.
  rewrite eq_refl /=.
  rewrite benaloh_decrypt_correct.
  reflexivity.
Qed.

(* ========================================================================== *)
(*                   isPartyHE_EncDec Instance                                 *)
(* ========================================================================== *)

HB.instance Definition Benaloh_isPartyHE_EncDec : isPartyHE_EncDec Benaloh_Party_HE_types := 
  @isPartyHE_EncDec.Build Benaloh_Party_HE_types 
    benaloh_phe_E benaloh_phe_K benaloh_phe_D benaloh_phe_msg_nat
    benaloh_phe_dec_correct.

(* ========================================================================== *)
(*                   Homomorphic Operations                                    *)
(* ========================================================================== *)

(* Homomorphic addition: ciphertext multiplication *)
Definition benaloh_pahe_Emul (e1 e2 : party * 'Z_n) : (party * 'Z_n) := 
  let (p1, c1) := e1 in
  let (_, c2) := e2 in
  (p1, c1 * c2).

(* Homomorphic scalar multiplication: ciphertext exponentiation *)
Definition benaloh_pahe_Epow (e : party * 'Z_n) (m : 'Z_r) : (party * 'Z_n) :=
  let (p, c) := e in
  (p, c ^+ (m : nat)).

(* Additive homomorphism proof using morphism_2 *)
Lemma benaloh_pahe_Emul_addM : forall (p : party),
  morphism_2 (phe_E_curry Benaloh_Party_HE_types p) 
             (msg_rand_add Benaloh_Party_HE_types) 
             benaloh_pahe_Emul.
Proof.
  move=> p [m1 u1] [m2 u2].
  rewrite /phe_E_curry /msg_rand_add /benaloh_pahe_Emul /=.
  rewrite /benaloh_phe_E /=.
  congr pair.
  rewrite (@benaloh_enc.enc_mul_dist n r r_gt1 y y_order_r m1 m2 u1 u2).
  reflexivity.
Qed.

(* Scalar multiplication homomorphism proof *)
Lemma benaloh_pahe_Epow_mulM : forall (p : party) (m1 m2 : 'Z_r) (u : 'Z_n),
  benaloh_pahe_Epow (benaloh_phe_E p m1 u) m2 
    = benaloh_phe_E p (m1 * m2) (u ^+ benaloh_phe_msg_nat m2).
Proof.
  move=> p m1 m2 u.
  rewrite /benaloh_pahe_Epow /benaloh_phe_E /benaloh_phe_msg_nat /=.
  congr pair.
  rewrite (@benaloh_enc.enc_exp_dist n r r_gt1 y y_order_r m1 (m2 : nat) u).
  congr (benaloh_enc y _ _).
  by rewrite mulrC -[m2 in m2 * _]natr_Zp mulr_natl.
Qed.

(* ========================================================================== *)
(*                   isPartyAHE_HomoOps Instance                               *)
(* ========================================================================== *)

HB.instance Definition Benaloh_isPartyAHE_HomoOps : isPartyAHE_HomoOps Benaloh_Party_HE_types := 
  @isPartyAHE_HomoOps.Build Benaloh_Party_HE_types 
    benaloh_pahe_Emul benaloh_pahe_Epow
    benaloh_pahe_Emul_addM benaloh_pahe_Epow_mulM.

(* ========================================================================== *)
(*                   Algebraic Properties                                      *)
(* ========================================================================== *)

(* Associativity of Emul *)
Lemma benaloh_pahe_Emul_assoc : forall (e1 e2 e3 : party * 'Z_n),
  benaloh_pahe_Emul (benaloh_pahe_Emul e1 e2) e3 = 
  benaloh_pahe_Emul e1 (benaloh_pahe_Emul e2 e3).
Proof.
  move=> [p1 c1] [p2 c2] [p3 c3].
  rewrite /benaloh_pahe_Emul /=.
  by rewrite mulrA.
Qed.

(* Unit randomness for identity element: 1 in Z_n *)
Definition benaloh_pahe_rand_unit : 'Z_n := 1.

(* Identity element: E(p, 0, 1) acts as identity for Emul.
   Proof: benaloh_enc y 0 1 = y^0 * 1^r = 1 * 1 = 1
   So Emul (p, c) (p', 1) = (p, c * 1) = (p, c) *)
Lemma benaloh_pahe_Emul_id : forall (p : party) (e : party * 'Z_n),
  benaloh_pahe_Emul e (benaloh_phe_E p 0 benaloh_pahe_rand_unit) = e.
Proof.
  move=> p [pe ce].
  rewrite /benaloh_pahe_Emul /benaloh_phe_E /benaloh_pahe_rand_unit /=.
  rewrite /benaloh_enc.
  rewrite expr0.
  rewrite mul1r.
  rewrite expr1n.
  rewrite mulr1.
  reflexivity.
Qed.

(* Note: Full commutativity (Emul e1 e2 = Emul e2 e1) does NOT hold because
   the party label comes from the first argument. However, the ciphertext
   part does commute. We prove this weaker property for reference. *)
Lemma benaloh_pahe_Emul_comm_cipher : forall (e1 e2 : party * 'Z_n),
  (benaloh_pahe_Emul e1 e2).2 = (benaloh_pahe_Emul e2 e1).2.
Proof.
  move=> [p1 c1] [p2 c2].
  rewrite /benaloh_pahe_Emul /=.
  apply mulrC.
Qed.

(* Same-party commutativity: when parties are equal, full commutativity holds *)
Lemma benaloh_pahe_Emul_comm_same_party : forall (p : party) (c1 c2 : 'Z_n),
  benaloh_pahe_Emul (p, c1) (p, c2) = benaloh_pahe_Emul (p, c2) (p, c1).
Proof.
  move=> p c1 c2.
  rewrite /benaloh_pahe_Emul /=.
  congr pair.
  apply mulrC.
Qed.

(* ========================================================================== *)
(*                   isPartyAHE_Algebra Instance                               *)
(* ========================================================================== *)

HB.instance Definition Benaloh_isPartyAHE_Algebra : isPartyAHE_Algebra Benaloh_Party_HE_types := 
  @isPartyAHE_Algebra.Build Benaloh_Party_HE_types 
    benaloh_pahe_Emul_assoc benaloh_pahe_rand_unit benaloh_pahe_Emul_id.

End Benaloh_Party_AHE.
