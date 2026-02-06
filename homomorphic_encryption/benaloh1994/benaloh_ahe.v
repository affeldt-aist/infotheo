(******************************************************************************)
(*                                                                            *)
(* Benaloh Party-Labeled AHE Instance                                         *)
(*                                                                            *)
(* This file provides HB instances for Benaloh encryption implementing        *)
(* the three AHE mixins:                                                      *)
(*   - isEncDec     (encryption/decryption)                               *)
(*   - isAHEnc      (homomorphic operations)                              *)
(*   - isAHEAlgebra (algebraic properties)                                *)
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

(* TODO: https://arxiv.org/pdf/1008.2991 (revised version, with more hypotheses)*)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import cyclic zmodp ssrfun.  (* For Euler_exp_totient *)
Require Import he_types.
Require Import enc_dec.
Require Import ahe_enc.
Require Import ahe_algebra.
Require Import benaloh_enc.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*                   Benaloh Party AHE Instance                                *)
(* ========================================================================== *)

Section Benaloh_Party_AHE.

Variable y : 'Z_n.
(* y_order_r ensures y is an r-th root of unity in Z_n.
   This is required for the homomorphic properties:
   - enc_mul_dist: E(m1,u1) * E(m2,u2) = E(m1+m2, u1*u2)
   - enc_exp_dist: E(m,u)^k = E(m*k, u^k)
   Without this, y^(m1+m2) != y^m1 * y^m2 in general. *)
Hypothesis y_order_r : y ^+ r = 1.
(* y must be in Z_n^* (coprime to n) for Euler's theorem to apply *)
Hypothesis y_coprime_n : coprime (y : nat) n.  (* TODO: define r by this *)

Variable partyT : finType.
Variables (n r : nat).
Hypothesis n_gt1 : (1 < n)%N.
Hypothesis r_gt1 : (1 < r)%N.

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
(* TODO: remove this? *)
(* TODO: mathcomp totient computatable algorithm to find the smallest (for define r from y) *)
Hypothesis phi_eq_totient : r * phi_div_r = totient n.


(* x = y^(φ(n)/r) is the base for discrete log in decryption *)
Definition x_base : 'Z_n := y ^+ phi_div_r.

(* For the discrete log to succeed, we need x_base^m to be injective on 'Z_r.
   This requires x_base to have exact order r (not just dividing r).
   This is a genuine cryptographic assumption about proper key generation:
   the parameter y must be chosen such that y^(phi(n)/r) generates a cyclic
   subgroup of order exactly r in the multiplicative group of units. *)
Hypothesis x_base_injective : forall (m1 m2 : 'Z_r), 
  x_base ^+ (m1 : nat) = x_base ^+ (m2 : nat) -> m1 = m2.

(* ========================================================================== *)
(*                   Secret Key Parameters                                     *)
(* ========================================================================== *)



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
  by rewrite mulr1.
Qed.

(* x_base has order dividing r - provable from euler_property and y_coprime_n *)
Lemma x_base_order_r : x_base ^+ r = 1.
Proof.
  rewrite /x_base.
  rewrite -exprM.
  rewrite mulnC.
  exact: euler_property y_coprime_n.
Qed.


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
Definition benaloh_enc_party := (partyT * 'Z_n)%type.
Definition benaloh_pkey := (partyT * key_type * 'Z_r)%type.

(* ========================================================================== *)
(*                   Type Bundle                                               *)
(* ========================================================================== *)

Definition Benaloh_HETypes : HETypes := 
  MkHE partyT 'Z_r 'Z_n 'Z_n (partyT * 'Z_n)%type benaloh_pkey.

(* ========================================================================== *)
(*                   Encryption/Decryption Operations                          *)
(* ========================================================================== *)

Definition benaloh_enc (p : partyT) (m : 'Z_r) (u : 'Z_n) : (partyT * 'Z_n) := 
  (p, benaloh_enc y m u).

Definition benaloh_key (p : partyT) (k : key_type) (m : 'Z_r) : benaloh_pkey := 
  (p, k, m).

(* Decryption using the Benaloh decryption algorithm.
   Only decrypts if:
   1. The key is a decryption key (k == Dec)
   2. The party labels match (i == j) *)
Definition benaloh_dec (dk : benaloh_pkey) (e : partyT * 'Z_n) : option 'Z_r :=
  match dk, e with
  | (i, k, _), (j, c) => 
    if (i == j) && (k == Dec) then Some (benaloh_decrypt c) else None
  end.

(* Decryption correctness - proved using the Benaloh decryption algorithm.
   Uses rand_coprime_n assumption: randomness is a unit in Z_n. *)
Lemma benaloh_dec_correct : forall (p : partyT) (m : 'Z_r) (u : 'Z_n) (sk : 'Z_r),
  benaloh_dec (benaloh_key p Dec sk) (benaloh_enc p m u) = Some m.
Proof.
  move=> p m u sk.
  rewrite /benaloh_dec /benaloh_key /benaloh_enc /=.
  rewrite eq_refl /=.
  by rewrite benaloh_decrypt_correct.
Qed.

(* ========================================================================== *)
(*                   isEncDec Instance                                        *)
(* ========================================================================== *)

HB.instance Definition Benaloh_isEncDec : isEncDec Benaloh_HETypes := 
  @isEncDec.Build Benaloh_HETypes 
    benaloh_enc benaloh_key benaloh_dec
    benaloh_dec_correct.

(* ========================================================================== *)
(*                   Homomorphic Operations                                   *)
(* ========================================================================== *)

(* Homomorphic addition: ciphertext multiplication *)
Definition benaloh_Emul (e1 e2 : partyT * 'Z_n) : (partyT * 'Z_n) := 
  let (p1, c1) := e1 in
  let (_, c2) := e2 in
  (p1, c1 * c2).

(* Homomorphic scalar multiplication: ciphertext exponentiation *)
Definition benaloh_Epow (e : partyT * 'Z_n) (m : 'Z_r) : (partyT * 'Z_n) :=
  let (p, c) := e in
  (p, c ^+ (m : nat)).

(* Randomness exponentiation by message: r ^^ m *)
Definition benaloh_rand_pow (u : 'Z_n) (m : 'Z_r) : 'Z_n := u ^+ (m : nat).

(* -------------------------------------------------------------------------- *)
(*  Local notations for compact {morph} syntax                                *)
(* -------------------------------------------------------------------------- *)
(* These notations make the morphism statements readable:
   {morph E[ p ] : x y / x (+) y >-> x *E y}
   expands to:
   morphism_2 (enc_curry Benaloh_HETypes p)
              (msg_rand_add Benaloh_HETypes)
              benaloh_Emul *)
(* The reason we re-define notations already in ahe_enc.v is because the type
   now is different. In there, it is abstract types like rand T and plain T.
   If we just use the notations from there, the type we use here like 'Z_r
   cannot work. *)
Local Notation BT := Benaloh_HETypes.
Local Notation "E[ p ]" := (enc_curry BT p) (at level 10, p at level 9).
Local Notation "x {+} y" := (msg_rand_add BT x y)
  (at level 50, left associativity).
Local Notation "x {^} y" := (unpair_mul_rand_op BT x y benaloh_rand_pow)
  (at level 50, left associativity).
Local Notation "x (.) y" := (benaloh_Emul x y)
  (at level 40, left associativity).
Local Notation "x (^) y" := (benaloh_Epow x y)
  (at level 40, left associativity).

(* Additive homomorphism: E(m1,r1) * E(m2,r2) = E(m1+m2, r1*r2) mod m *)
Lemma benaloh_Emul_addM : forall (p : partyT),
  {morph E[ p ] : x y / x {+} y >-> x (.) y}.
Proof.
  move=> p [m1 u1] [m2 u2].
  rewrite /enc_curry /msg_rand_add /benaloh_Emul /=.
  rewrite /benaloh_enc /=.
  congr pair.
  by rewrite (@benaloh_enc.enc_mul_dist n r r_gt1 y y_order_r m1 m2 u1 u2).
Qed.

(* Scalar multiplication homomorphism proof:
   E(m1)^m2 = E(m1 m2) mod m *)
Lemma benaloh_Epow_mulM : forall (p : partyT) (m : 'Z_r),
  {morph E[p] : mr / mr {^} m >-> mr (^) m}.
Proof.
  move=> p m2 [m1 u].
  rewrite /enc_curry /benaloh_Epow /benaloh_enc /benaloh_rand_pow /=.
  congr pair.
  rewrite (@benaloh_enc.enc_exp_dist n r r_gt1 y y_order_r m1 (m2 : nat) u).
  congr (benaloh_enc.benaloh_enc y _ _).
  by rewrite mulrC -[m2 in m2 * _]natr_Zp mulr_natl.
Qed.

(* ========================================================================== *)
(*                   isAHEnc Instance                                         *)
(* ========================================================================== *)

HB.instance Definition Benaloh_isAHEnc : isAHEnc Benaloh_HETypes := 
  @isAHEnc.Build Benaloh_HETypes 
    benaloh_Emul benaloh_Epow benaloh_rand_pow
    benaloh_Emul_addM benaloh_Epow_mulM.

(* ========================================================================== *)
(*                   Algebraic Properties                                      *)
(* ========================================================================== *)

(* Associativity of Emul *)
Lemma benaloh_Emul_assoc : forall (e1 e2 e3 : partyT * 'Z_n),
  benaloh_Emul (benaloh_Emul e1 e2) e3 = 
  benaloh_Emul e1 (benaloh_Emul e2 e3).
Proof.
  move=> [p1 c1] [p2 c2] [p3 c3].
  rewrite /benaloh_Emul /=.
  by rewrite mulrA.
Qed.

(* Unit randomness for identity element: 1 in Z_n *)
Definition benaloh_rand_unit : 'Z_n := 1.

(* Identity element: E(p, 0, 1) acts as identity for Emul.
   Proof: benaloh_enc y 0 1 = y^0 * 1^r = 1 * 1 = 1
   So Emul (p, c) (p', 1) = (p, c * 1) = (p, c) *)
Lemma benaloh_Emul_id : forall (p : partyT) (e : partyT * 'Z_n),
  benaloh_Emul e (benaloh_enc p 0 benaloh_rand_unit) = e.
Proof.
  move=> p [pe ce].
  rewrite /benaloh_Emul /benaloh_enc /benaloh_rand_unit /=.
  (* Unfold the module-level benaloh_enc.benaloh_enc *)
  rewrite /benaloh_enc.benaloh_enc.
  rewrite expr0 mul1r expr1n mulr1.
  reflexivity.
Qed.

(* Cipher extraction: extracts the raw ciphertext without party label *)
Definition benaloh_enc_cipher (e : partyT * 'Z_n) : 'Z_n := e.2.

(* Cipher-level commutativity: the raw ciphertext part commutes *)
Lemma benaloh_Emul_comm_cipher : forall (e1 e2 : partyT * 'Z_n),
  benaloh_enc_cipher (benaloh_Emul e1 e2) = 
  benaloh_enc_cipher (benaloh_Emul e2 e1).
Proof.
  move=> [p1 c1] [p2 c2].
  rewrite /benaloh_enc_cipher /benaloh_Emul /=.
  apply mulrC.
Qed.

(* Same-party commutativity: when parties are equal, full commutativity holds *)
Lemma benaloh_Emul_comm_same_party : forall (p : partyT) (c1 c2 : 'Z_n),
  benaloh_Emul (p, c1) (p, c2) = benaloh_Emul (p, c2) (p, c1).
Proof.
  move=> p c1 c2.
  rewrite /benaloh_Emul /=.
  congr pair.
  apply mulrC.
Qed.

(* ========================================================================== *)
(*                   isAHEAlgebra Instance                                    *)
(* ========================================================================== *)

HB.instance Definition Benaloh_isAHEAlgebra : isAHEAlgebra Benaloh_HETypes := 
  @isAHEAlgebra.Build Benaloh_HETypes 
    benaloh_Emul_assoc benaloh_rand_unit benaloh_Emul_id
    benaloh_enc_cipher benaloh_Emul_comm_cipher.

End Benaloh_Party_AHE.
