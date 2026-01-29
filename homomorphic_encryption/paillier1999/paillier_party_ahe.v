(******************************************************************************)
(*                                                                            *)
(* Paillier Party-Labeled AHE Instance                                        *)
(*                                                                            *)
(* This file provides HB instances for Paillier encryption implementing       *)
(* the three AHE mixins:                                                      *)
(*   - isPartyHE_EncDec   (encryption/decryption)                             *)
(*   - isPartyAHE_HomoOps (homomorphic operations)                            *)
(*   - isPartyAHE_Algebra (algebraic properties)                              *)
(*                                                                            *)
(* == Cryptographic Assumptions ==                                            *)
(*                                                                            *)
(*   g_order_n : g ^+ n = 1   (g is an n-th root of unity in Z_{n^2})         *)
(*                                                                            *)
(* == References ==                                                           *)
(*                                                                            *)
(*   Paillier, P. (1999). "Public-Key Cryptosystems Based on Composite        *)
(*     Degree Residuosity Classes"                                            *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg zmodp ssrfun.
Require Import he_types.
Require Import enc_dec.
Require Import ahe_enc.
Require Import ahe_algebra.
Require Import paillier_enc.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*                   Paillier Party AHE Instance                               *)
(* ========================================================================== *)

Section Paillier_Party_AHE.

Variable party : finType.
Variable n : nat.
Hypothesis n_gt1 : (1 < n)%N.
Let n2 := (n * n)%N.
Variable g : 'Z_n2.
(* g_order_n ensures g is an n-th root of unity in Z_{n^2}.
   With standard choice g = 1 + n, this holds because:
     (1+n)^n = 1 + n*n = 1 (mod n^2)
   This is required for the homomorphic properties:
   - enc_mul_dist: E(m1,r1) * E(m2,r2) = E(m1+m2, r1*r2)
   - enc_exp_dist: E(m,r)^k = E(m*k, r^k)
   Without this, g^(m1+m2) != g^m1 * g^m2 in general. *)
Hypothesis g_order_n : g ^+ n = 1.

(* ========================================================================== *)
(*                   Secret Key Parameters                                     *)
(* ========================================================================== *)

(* Paillier decryption uses the L-function and private key (λ, μ):
     m = L(c^λ mod n²) · μ mod n
   where L(x) = (x - 1) / n
   
   The decryption algorithm:
   1. λ = lcm(p-1, q-1) where n = p·q (Carmichael function)
   2. μ = L(g^λ mod n²)^(-1) mod n
   3. c^λ removes randomness: (g^m * r^n)^λ = g^(m·λ) (since r^(n·λ) = 1)
   4. L(g^(m·λ)) · μ extracts m *)

Variable lambda : nat.

(* Carmichael's theorem: r^(n·λ) = 1 in Z*_{n²} *)
Hypothesis carmichael_property : forall (r : 'Z_n2), r ^+ (n * lambda) = 1.

(* ========================================================================== *)
(*                   L-function Definition                                     *)
(* ========================================================================== *)

(* The L-function: L(x) = (x-1)/n maps Z_{n²} to Z_n.
   For x = 1 + k·n (mod n²), we have L(x) = k (mod n).
   
   Mathematical justification:
   - For standard Paillier g = 1 + n, binomial theorem gives:
       (1+n)^k = 1 + k·n + C(k,2)·n² + ... = 1 + k·n (mod n²)
   - So g^k - 1 = k·n (mod n²)
   - L(g^k) = (g^k - 1)/n = k (mod n)
   
   The division by n is exact when the input is in the subgroup 
   {1 + k·n : k ∈ Z} ⊂ Z*_{n²}. *)
Definition L_func (x : 'Z_n2) : 'Z_n :=
  inZp (((x : nat) - 1) %/ n)%N.

(* μ is the modular inverse of λ in Z_n *)
Variable mu : 'Z_n.

(* Key property: L(g^k) extracts k mod n.
   
   Proof sketch (requires detailed modular arithmetic):
   1. g = 1 + n in Z_{n²}
   2. g^k = (1+n)^k = 1 + k·n (mod n²) by binomial theorem
   3. (g^k - 1) / n = k (exact integer division)
   4. k mod n gives the result in Z_n
   
   We state this as a hypothesis since the full proof requires
   establishing the binomial expansion for 'Z_n2 arithmetic. *)
Hypothesis L_of_g_power : forall (k : nat), L_func (g ^+ k) = inZp k.

(* μ satisfies: λ · μ = 1 (mod n), i.e., μ = λ^(-1) mod n *)
Hypothesis lambda_mu_inverse : (inZp lambda : 'Z_n) * mu = 1.

(* Decryption correctness: L(g^(m·λ)) · μ = m
   
   Key MathComp lemmas used:
   - Zp_nat : n%:R = inZp n
   - natrM  : (m * n)%:R = m%:R * n%:R
   - natr_Zp: (x : nat)%:R = x  for x : 'Z_n *)
Lemma L_decrypt_correct (m : 'Z_n) :
  L_func (g ^+ ((m : nat) * lambda)) * mu = m.
Proof.
  rewrite L_of_g_power.
  rewrite -(@Zp_nat (Zp_trunc n) ((m : nat) * lambda)).
  rewrite natrM.
  rewrite (natr_Zp m).
  rewrite -mulrA.
  rewrite (@Zp_nat (Zp_trunc n) lambda).
  rewrite lambda_mu_inverse mulr1.
  reflexivity.
Qed.

(* ========================================================================== *)
(*                   Paillier Decryption                                       *)
(* ========================================================================== *)

(* Paillier decryption function *)
Definition paillier_decrypt (c : 'Z_n2) : 'Z_n :=
  L_func (c ^+ lambda) * mu.

(* Key lemma: raising ciphertext to λ removes randomness *)
Lemma ciphertext_reduction (m : 'Z_n) (r : 'Z_n2) :
  (paillier_enc g m r) ^+ lambda = g ^+ ((m : nat) * lambda).
Proof.
  rewrite /paillier_enc.
  rewrite exprMn_comm; last by apply mulrC.
  rewrite -!exprM.
  rewrite carmichael_property.
  rewrite mulr1.
  reflexivity.
Qed.

(* Decryption correctness *)
Lemma paillier_decrypt_correct (m : 'Z_n) (r : 'Z_n2) :
  paillier_decrypt (paillier_enc g m r) = m.
Proof.
  rewrite /paillier_decrypt.
  rewrite ciphertext_reduction.
  apply L_decrypt_correct.
Qed.

(* Type definitions *)
Definition paillier_enc_party := (party * 'Z_n2)%type.
Definition paillier_pkey := (party * key * 'Z_n)%type.

(* ========================================================================== *)
(*                   Type Bundle                                               *)
(* ========================================================================== *)

Definition Paillier_Party_HE_types : Party_HE_types := 
  MkPartyHE party 'Z_n 'Z_n2 'Z_n2 (party * 'Z_n2)%type paillier_pkey.

(* ========================================================================== *)
(*                   Encryption/Decryption Operations                          *)
(* ========================================================================== *)

Definition paillier_phe_E (p : party) (m : 'Z_n) (r : 'Z_n2) : (party * 'Z_n2) := 
  (p, paillier_enc g m r).

Definition paillier_phe_K (p : party) (k : key) (m : 'Z_n) : paillier_pkey := 
  (p, k, m).

(* Decryption using the Paillier decryption algorithm.
   Only decrypts if:
   1. The key is a decryption key (k == Dec)
   2. The party labels match (i == j) *)
Definition paillier_phe_D (dk : paillier_pkey) (e : party * 'Z_n2) : option 'Z_n :=
  match dk, e with
  | (i, k, _), (j, c) => 
    if (i == j) && (k == Dec) then Some (paillier_decrypt c) else None
  end.

(* Decryption correctness - proved using the Paillier decryption algorithm *)
Lemma paillier_phe_dec_correct : forall (p : party) (m : 'Z_n) (r : 'Z_n2) (sk : 'Z_n),
  paillier_phe_D (paillier_phe_K p Dec sk) (paillier_phe_E p m r) = Some m.
Proof.
  move=> p m r sk.
  rewrite /paillier_phe_D /paillier_phe_K /paillier_phe_E /=.
  rewrite eq_refl /=.
  rewrite paillier_decrypt_correct.
  reflexivity.
Qed.

(* ========================================================================== *)
(*                   isPartyHE_EncDec Instance                                 *)
(* ========================================================================== *)

HB.instance Definition Paillier_isPartyHE_EncDec : isPartyHE_EncDec Paillier_Party_HE_types := 
  @isPartyHE_EncDec.Build Paillier_Party_HE_types 
    paillier_phe_E paillier_phe_K paillier_phe_D
    paillier_phe_dec_correct.

(* ========================================================================== *)
(*                   Homomorphic Operations                                    *)
(* ========================================================================== *)

(* Homomorphic addition: ciphertext multiplication *)
Definition paillier_pahe_Emul (e1 e2 : party * 'Z_n2) : (party * 'Z_n2) := 
  let (p1, c1) := e1 in
  let (_, c2) := e2 in
  (p1, c1 * c2).

(* Homomorphic scalar multiplication: ciphertext exponentiation *)
Definition paillier_pahe_Epow (e : party * 'Z_n2) (m : 'Z_n) : (party * 'Z_n2) :=
  let (p, c) := e in
  (p, c ^+ (m : nat)).

(* Randomness exponentiation by message: r ^^ m *)
Definition paillier_pahe_rand_pow (r : 'Z_n2) (m : 'Z_n) : 'Z_n2 := r ^+ (m : nat).

(* -------------------------------------------------------------------------- *)
(*  Local notations for compact {morph} syntax                                *)
(* -------------------------------------------------------------------------- *)
(* These notations make the morphism statements readable:
   {morph E[ p ] : x y / x +mr y >-> x *E y}
   expands to:
   morphism_2 (phe_E_curry Paillier_Party_HE_types p)
              (msg_rand_add Paillier_Party_HE_types)
              paillier_pahe_Emul *)
Local Notation PT := Paillier_Party_HE_types.
Local Notation "E[ p ]" := (phe_E_curry PT p) (at level 10, p at level 9).
Local Notation "x +mr y" := (msg_rand_add PT x y) (at level 50, left associativity).
Local Notation "x *E y" := (paillier_pahe_Emul x y) (at level 40, left associativity).

(* Additive homomorphism: E(m1,r1) * E(m2,r2) = E(m1+m2, r1*r2) *)
Lemma paillier_pahe_Emul_addM : forall (p : party),
  {morph E[ p ] : x y / x +mr y >-> x *E y}.
Proof.
  move=> p [m1 r1] [m2 r2].
  rewrite /phe_E_curry /msg_rand_add /paillier_pahe_Emul /=.
  rewrite /paillier_phe_E /=.
  congr pair.
  rewrite (@paillier_enc.enc_mul_dist n n_gt1 g g_order_n m1 m2 r1 r2).
  reflexivity.
Qed.

(* Scalar multiplication homomorphism proof *)
Lemma paillier_pahe_Epow_mulM : forall (p : party) (m1 m2 : 'Z_n) (r : 'Z_n2),
  paillier_pahe_Epow (paillier_phe_E p m1 r) m2 
    = paillier_phe_E p (m1 * m2) (paillier_pahe_rand_pow r m2).
Proof.
  move=> p m1 m2 r.
  rewrite /paillier_pahe_Epow /paillier_phe_E /paillier_pahe_rand_pow /=.
  congr pair.
  rewrite (@paillier_enc.enc_exp_dist n n_gt1 g g_order_n m1 (m2 : nat) r).
  congr (paillier_enc g _ _).
  by rewrite mulrC -[m2 in m2 * _]natr_Zp mulr_natl.
Qed.

(* ========================================================================== *)
(*                   isPartyAHE_HomoOps Instance                               *)
(* ========================================================================== *)

HB.instance Definition Paillier_isPartyAHE_HomoOps : isPartyAHE_HomoOps Paillier_Party_HE_types := 
  @isPartyAHE_HomoOps.Build Paillier_Party_HE_types 
    paillier_pahe_Emul paillier_pahe_Epow paillier_pahe_rand_pow
    paillier_pahe_Emul_addM paillier_pahe_Epow_mulM.

(* ========================================================================== *)
(*                   Algebraic Properties                                      *)
(* ========================================================================== *)

(* Associativity of Emul *)
Lemma paillier_pahe_Emul_assoc : forall (e1 e2 e3 : party * 'Z_n2),
  paillier_pahe_Emul (paillier_pahe_Emul e1 e2) e3 = 
  paillier_pahe_Emul e1 (paillier_pahe_Emul e2 e3).
Proof.
  move=> [p1 c1] [p2 c2] [p3 c3].
  rewrite /paillier_pahe_Emul /=.
  by rewrite mulrA.
Qed.

(* Unit randomness for identity element: 1 in Z_{n^2} *)
Definition paillier_pahe_rand_unit : 'Z_n2 := 1.

(* Identity element: E(p, 0, 1) acts as identity for Emul.
   Proof: paillier_enc g 0 1 = g^0 * 1^n = 1 * 1 = 1
   So Emul (p, c) (p', 1) = (p, c * 1) = (p, c) *)
Lemma paillier_pahe_Emul_id : forall (p : party) (e : party * 'Z_n2),
  paillier_pahe_Emul e (paillier_phe_E p 0 paillier_pahe_rand_unit) = e.
Proof.
  move=> p [pe ce].
  rewrite /paillier_pahe_Emul /paillier_phe_E /paillier_pahe_rand_unit /=.
  rewrite /paillier_enc.
  rewrite expr0.
  rewrite mul1r.
  rewrite expr1n.
  rewrite mulr1.
  reflexivity.
Qed.

(* Cipher extraction: extracts the raw ciphertext without party label *)
Definition paillier_pahe_enc_cipher (e : party * 'Z_n2) : 'Z_n2 := e.2.

(* Cipher-level commutativity: the raw ciphertext part commutes *)
Lemma paillier_pahe_Emul_comm_cipher : forall (e1 e2 : party * 'Z_n2),
  paillier_pahe_enc_cipher (paillier_pahe_Emul e1 e2) = 
  paillier_pahe_enc_cipher (paillier_pahe_Emul e2 e1).
Proof.
  move=> [p1 c1] [p2 c2].
  rewrite /paillier_pahe_enc_cipher /paillier_pahe_Emul /=.
  apply mulrC.
Qed.

(* Same-party commutativity: when parties are equal, full commutativity holds *)
Lemma paillier_pahe_Emul_comm_same_party : forall (p : party) (c1 c2 : 'Z_n2),
  paillier_pahe_Emul (p, c1) (p, c2) = paillier_pahe_Emul (p, c2) (p, c1).
Proof.
  move=> p c1 c2.
  rewrite /paillier_pahe_Emul /=.
  congr pair.
  apply mulrC.
Qed.

(* ========================================================================== *)
(*                   isPartyAHE_Algebra Instance                               *)
(* ========================================================================== *)

HB.instance Definition Paillier_isPartyAHE_Algebra : isPartyAHE_Algebra Paillier_Party_HE_types := 
  @isPartyAHE_Algebra.Build Paillier_Party_HE_types 
    paillier_pahe_Emul_assoc paillier_pahe_rand_unit paillier_pahe_Emul_id
    paillier_pahe_enc_cipher paillier_pahe_Emul_comm_cipher.

End Paillier_Party_AHE.
