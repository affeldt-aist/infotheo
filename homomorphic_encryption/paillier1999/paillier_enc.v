(******************************************************************************)
(*                                                                            *)
(* Paillier Homomorphic Encryption                                            *)
(*                                                                            *)
(* This file defines the Paillier encryption scheme and the core homomorphic  *)
(* properties using MathComp ring exponentiation lemmas.                      *)
(*                                                                            *)
(* Key property: with generator g = 1 + n, we have g ^+ n = 1 in Z_{n^2}.     *)
(* This is analogous to Benaloh's y ^+ r = 1 constraint.                      *)
(*                                                                            *)
(* == Informal "why it works" (math) ==                                       *)
(*                                                                            *)
(* Plaintexts live in Z_n, ciphertexts live in Z_{n^2}. Encryption is          *)
(*                                                                            *)
(*   c = g^m · r^n   (mod n^2)                                                 *)
(*                                                                            *)
(* where r is fresh randomness (typically sampled from the units mod n^2).     *)
(* Again this is "message part" g^m times a "mask" r^n.                        *)
(*                                                                            *)
(* Homomorphism is exponent algebra:                                          *)
(*                                                                            *)
(*   (g^{m1} r1^n) · (g^{m2} r2^n) = g^{m1+m2} (r1 r2)^n                       *)
(*                                                                            *)
(* so ciphertext multiplication corresponds to plaintext addition. Similarly, *)
(*                                                                            *)
(*   (g^m r^n)^k = g^{m·k} (r^k)^n                                              *)
(*                                                                            *)
(* so powering a ciphertext corresponds to multiplying the plaintext by k      *)
(* (repeated addition). The hypothesis g^n = 1 ensures g^m depends only on     *)
(* m mod n, matching the message space Z_n.                                    *)
(*                                                                            *)
(* Reference:                                                                 *)
(*   Paillier, P. (1999). Public-Key Cryptosystems Based on Composite         *)
(*     Degree Residuosity Classes                                             *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg zmodp.

Import GRing.Theory.
Import Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*                         Helper Lemmas                                       *)
(* ========================================================================== *)

(* Reuse the helper lemmas pattern from Benaloh *)

(* Helper: nat addition of Z_n elements equals Z_n addition mod n *)
Lemma Zp_add_eqmod (n : nat) (n_gt1 : (1 < n)%N) (m1 m2 : 'Z_n) : 
  (m1 : nat) + m2 = (m1 + m2)%R %[mod n].
Proof.
  have Hn : (Zp_trunc n).+2 = n := Zp_cast n_gt1.
  set k1 := (m1 : nat).
  set k2 := (m2 : nat).
  rewrite /eqn /GRing.add /= /Zp_add /=.
  transitivity ((k1 + k2) %% n %% n)%N; first by rewrite modn_mod.
  congr (modn _ n).
  rewrite -/k1 -/k2.
  by rewrite Hn.
Qed.

(* Helper: (m *+ k : 'Z_n) as nat equals (m * k) %% (Zp_trunc n).+2 *)
Lemma Zp_mulrn_nat (n : nat) (n_gt1 : (1 < n)%N) (m : 'Z_n) (k : nat) :
  ((m *+ k)%R : nat) = (((m : nat) * k) %% (Zp_trunc n).+2)%N.
Proof.
  elim: k => [|k IHk].
  - by rewrite GRing.mulr0n muln0 mod0n.
  - rewrite GRing.mulrSr /GRing.add /= /Zp_add /= mulnS IHk addnC modnDmr.
    reflexivity.
Qed.

(* Helper: nat mult of Z_n element by nat equals Z_n scalar mult mod n *)
Lemma Zp_mulrn_eqmod (n : nat) (n_gt1 : (1 < n)%N) (m1 : 'Z_n) (m2 : nat) :
  (m1 : nat) * m2 = (m1 *+ m2)%R %[mod n].
Proof.
  have Hn : (Zp_trunc n).+2 = n := Zp_cast n_gt1.
  set k1 := (m1 : nat).
  rewrite /eqn (Zp_mulrn_nat n_gt1).
  transitivity ((k1 * m2) %% n %% n)%N; first by rewrite modn_mod.
  congr (modn _ n).
  rewrite -/k1.
  by rewrite Hn.
Qed.

(* ========================================================================== *)
(*                      Paillier Cryptosystem Parameters                       *)
(* ========================================================================== *)

Section paillier_params.

Variable n : nat.

(* n must be > 1 for 'Z_n to be a valid type *)
Hypothesis n_gt1 : (1 < n)%N.

(* n^2 for the ciphertext space *)
Let n2 := (n * n)%N.

(* n^2 > 1 follows from n > 1 *)
Lemma n2_gt1 : (1 < n2)%N.
Proof.
  rewrite /n2 -[X in (X < _)%N]muln1.
  by apply: ltn_mul.
Qed.

(* Generator g in Z_{n^2} *)
Variable g : 'Z_n2.

(* ========================================================================== *)
(*                         Encryption Definition                               *)
(* ========================================================================== *)

(* Paillier encryption: c = g^m * r^n mod n^2 *)
Definition paillier_enc (m : 'Z_n) (r : 'Z_n2) : 'Z_n2 :=
  g ^+ m * r ^+ n.

(* ========================================================================== *)
(*                     Key Cryptographic Constraint                            *)
(* ========================================================================== *)

(* 
  The generator g must have order n in Z_{n^2}^*.
  With standard choice g = 1 + n, this holds because:
    (1+n)^n = 1 + n*n = 1 (mod n^2)
  
  This is analogous to Benaloh's y_order_r : y ^+ r = 1.
*)
Hypothesis g_order_n : g ^+ n = 1.

(* ========================================================================== *)
(*                         Homomorphic Properties                              *)
(* ========================================================================== *)

(* Exponentiation of g depends only on exponent mod n *)
Lemma expr_modn (k : nat) : g ^+ k = g ^+ (k %% n)%N.
Proof.
  rewrite {1}(divn_eq k n) exprD exprM exprAC g_order_n expr1n mul1r.
  reflexivity.
Qed.

(* Encryption multiplication distributes as addition on messages *)
Lemma enc_mul_dist : forall (m1 m2 : 'Z_n) (r1 r2 : 'Z_n2),
  paillier_enc m1 r1 * paillier_enc m2 r2 = 
  paillier_enc (m1 + m2) (r1 * r2).
Proof.
  move=> m1 m2 r1 r2.
  rewrite /paillier_enc exprMn mulrACA -exprD.
  congr (_ * _).
  rewrite (expr_modn (m1 + m2)) (expr_modn (m1 + m2)%R).
  congr (g ^+ _).
  exact: (Zp_add_eqmod n_gt1).
Qed.

(* Encryption exponentiation distributes as scalar multiplication *)
Lemma enc_exp_dist : forall (m1 : 'Z_n) (m2 : nat) (r : 'Z_n2),
  (paillier_enc m1 r) ^+ m2 = paillier_enc (m1 *+ m2) (r ^+ m2).
Proof.
  move=> m1 m2 r.
  rewrite /paillier_enc (exprMn_comm _ (mulrC _ _)) -!exprM [(n * m2)%N]mulnC.
  congr (_ * _).
  rewrite (expr_modn (m1 * m2)) (expr_modn (m1 *+ m2)).
  congr (g ^+ _).
  exact: (Zp_mulrn_eqmod n_gt1).
Qed.

End paillier_params.
