(******************************************************************************)
(*                                                                            *)
(* Benaloh Homomorphic Encryption                                             *)
(*                                                                            *)
(* This file defines the Benaloh encryption scheme and the core homomorphic   *)
(* properties using MathComp ring exponentiation lemmas.                      *)
(*                                                                            *)
(* Key assumption: the generator y has order dividing r [y ^+ r = 1].         *)
(* This is a standard cryptographic constraint in the Benaloh scheme.         *)
(*                                                                            *)
(* == Informal "why it works" (math) ==                                       *)
(*                                                                            *)
(* Plaintexts live in Z_r, ciphertexts live in Z_n. Encryption is             *)
(*                                                                            *)
(*   c = y^m · u^r   (mod n)                                                   *)
(*                                                                            *)
(* where u is fresh randomness. The ciphertext is a product of:               *)
(* - a "message part" y^m (message in the exponent), and                      *)
(* - a "mask" u^r (an r-th power that randomizes).                            *)
(*                                                                            *)
(* Homomorphism is just exponent algebra:                                     *)
(*                                                                            *)
(*   (y^{m1} u1^r) · (y^{m2} u2^r) = y^{m1+m2} (u1 u2)^r                       *)
(*                                                                            *)
(* so ciphertext multiplication corresponds to plaintext addition. Similarly, *)
(*                                                                            *)
(*   (y^m u^r)^k = y^{m·k} (u^k)^r                                              *)
(*                                                                            *)
(* so raising a ciphertext to k corresponds to multiplying the plaintext by k *)
(* (i.e., repeated addition). The hypothesis y^r = 1 ensures y^m depends only *)
(* on m mod r, matching the message space Z_r.                                *)
(*                                                                            *)
(* Reference:                                                                 *)
(*   Benaloh, J. [1994]. "Dense Probabilistic Encryption"                     *)
(*   Benaloh, J., Tuinstra, D. [1994]. "Receipt-Free Secret-Ballot Elections" *)
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

(* Helper: nat addition of Z_r elements equals Z_r addition mod r *)
Lemma Zp_add_eqmod (r : nat) (r_gt1 : (1 < r)%N) (m1 m2 : 'Z_r) : 
  (m1 : nat) + m2 = (m1 + m2)%R %[mod r].
Proof.
  have Hr : (Zp_trunc r).+2 = r := Zp_cast r_gt1.
  set n1 := (m1 : nat).
  set n2 := (m2 : nat).
  rewrite /eqn /GRing.add /= /Zp_add /=.
  transitivity ((n1 + n2) %% r %% r)%N; first by rewrite modn_mod.
  congr (modn _ r).
  rewrite -/n1 -/n2.
  by rewrite Hr.
Qed.

(* Helper: (m *+ k : 'Z_r) as nat equals (m * k) %% (Zp_trunc r).+2 *)
Lemma Zp_mulrn_nat (r : nat) (r_gt1 : (1 < r)%N) (m : 'Z_r) (k : nat) :
  ((m *+ k)%R : nat) = (((m : nat) * k) %% (Zp_trunc r).+2)%N.
Proof.
  elim: k => [|k IHk].
  - by rewrite GRing.mulr0n muln0 mod0n.
  - rewrite GRing.mulrSr /GRing.add /= /Zp_add /= mulnS IHk addnC modnDmr.
    reflexivity.
Qed.

(* Helper: nat mult of Z_r element by nat equals Z_r scalar mult mod r *)
Lemma Zp_mulrn_eqmod (r : nat) (r_gt1 : (1 < r)%N) (m1 : 'Z_r) (m2 : nat) :
  (m1 : nat) * m2 = (m1 *+ m2)%R %[mod r].
Proof.
  have Hr : (Zp_trunc r).+2 = r := Zp_cast r_gt1.
  set n1 := (m1 : nat).
  rewrite /eqn (Zp_mulrn_nat r_gt1).
  transitivity ((n1 * m2) %% r %% r)%N; first by rewrite modn_mod.
  congr (modn _ r).
  rewrite -/n1.
  by rewrite Hr.
Qed.

(* ========================================================================== *)
(*                      Benaloh Cryptosystem Parameters                        *)
(* ========================================================================== *)

Section benaloh_params.

Variable n : nat.
Variable r : nat.

(* n and r must be > 1 for 'Z_n and 'Z_r to be valid types *)
Hypothesis n_gt1 : (1 < n)%N.
Hypothesis r_gt1 : (1 < r)%N.

(* Generator y in Z_n *)
Variable y : 'Z_n.

(* ========================================================================== *)
(*                         Encryption Definition                               *)
(* ========================================================================== *)

Definition benaloh_enc (m : 'Z_r) (u : 'Z_n) : 'Z_n :=
  y ^+ m * u ^+ r.

(* ========================================================================== *)
(*                     Key Cryptographic Constraint                            *)
(* ========================================================================== *)

Hypothesis y_order_r : y ^+ r = 1.

(* ========================================================================== *)
(*                         Homomorphic Properties                              *)
(* ========================================================================== *)

(* Exponentiation of y depends only on exponent mod r *)
Lemma expr_modr (k : nat) : y ^+ k = y ^+ (k %% r)%N.
Proof.
  rewrite {1}(divn_eq k r) exprD exprM exprAC y_order_r expr1n mul1r.
  reflexivity.
Qed.

(* Encryption multiplication distributes as addition on messages *)
Lemma enc_mul_dist : forall (m1 m2 : 'Z_r) (u1 u2 : 'Z_n),
  benaloh_enc m1 u1 * benaloh_enc m2 u2 = 
  benaloh_enc (m1 + m2) (u1 * u2).
Proof.
  move=> m1 m2 u1 u2.
  rewrite /benaloh_enc exprMn mulrACA -exprD.
  congr (_ * _).
  rewrite (expr_modr (m1 + m2)) (expr_modr (m1 + m2)%R).
  congr (y ^+ _).
  exact: (Zp_add_eqmod r_gt1).
Qed.

(* Encryption exponentiation distributes as scalar multiplication *)
Lemma enc_exp_dist : forall (m1 : 'Z_r) (m2 : nat) (u : 'Z_n),
  (benaloh_enc m1 u) ^+ m2 = benaloh_enc (m1 *+ m2) (u ^+ m2).
Proof.
  move=> m1 m2 u.
  rewrite /benaloh_enc (exprMn_comm _ (mulrC _ _)) -!exprM [(r * m2)%N]mulnC.
  congr (_ * _).
  rewrite (expr_modr (m1 * m2)) (expr_modr (m1 *+ m2)).
  congr (y ^+ _).
  exact: (Zp_mulrn_eqmod r_gt1).
Qed.

End benaloh_params.
