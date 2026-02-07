(******************************************************************************)
(*                                                                            *)
(* Benaloh Homomorphic Encryption                                             *)
(*                                                                            *)
(* This file defines the Benaloh encryption scheme and the core homomorphic   *)
(* properties using MathComp ring exponentiation lemmas.                      *)
(*                                                                            *)
(* We adopt the so-called Fazio-Nicolosi condition (see e.g., Fazio and       *)
(* Nicolosi, 2002), which was specifically formalized for the Benaloh         *)
(* cryptosystem's correctness by Fousse et al. (2011):                        *)
(* - r divides phi(n), and alpha = phi(n)/r                                   *)
(* - Generator y is a unit with y^r = 1 (order dividing r)                    *)
(* - For unique decryption: order(y^alpha) = r exactly (not formalized here)  *)
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
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg zmodp cyclic.

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

Section BenalohEuler.

(* Modulus n = p * q *)
Variable n : nat.
(* Status: Must be assumed (basic parameter constraint). *)
Hypothesis n_gt1 : (1 < n)%N.

(* Block size r divides phi(n) *)
Variable r : nat.
(* Status: Must be assumed (basic parameter constraint). *)
Hypothesis r_gt1 : (1 < r)%N.

(* phi(n) via unit group cardinality *)
Definition phi_n := #|[set: {unit 'Z_n}]|.

(* Fazio-Nicolosi condition: r divides phi(n).
   Status: Must be assumed (key generation constraint).
   This is a fundamental requirement for the scheme - cannot be inferred. *)
Hypothesis r_div_phi : (r %| phi_n)%N.

(* alpha = phi(n) / r *)
(* The Fazio-Nicolosi condition requires order(y^alpha) = r exactly, ensuring *)
(* unique decryption. While not directly used in homomorphic proofs below,    *)
(* this constraint is essential for cryptographic correctness.                *)
Definition alpha := (phi_n %/ r)%N.

(* Generator y is a unit *)
Variable y : {unit 'Z_n}.

(* Key cryptographic constraint: y has order dividing r.

   Status: Could potentially be proved if y is defined as z ^+ alpha
   where z is a generator of the unit group with #[z] = phi_n.
   Then y^r = z^(alpha*r) = z^phi_n = 1 by Euler's theorem (euler_unit). *)
Hypothesis y_order_r : (val y) ^+ r = 1.

(* ========================================================================== *)
(*                         Encryption Definition                               *)
(* ========================================================================== *)

(* Encryption with unit randomness *)
Definition benaloh_enc (m : 'Z_r) (u : {unit 'Z_n}) : 'Z_n :=
  (val y) ^+ m * (val u) ^+ r.

(* ========================================================================== *)
(*                          Euler's Theorem                                    *)
(* ========================================================================== *)

(* Helper: val of group exponent = ring exponent of val *)
Lemma val_unit_exp (u : {unit 'Z_n}) k : val (u ^+ k)%g = (val u) ^+ k.
Proof. by elim: k => [|k IHk] //; rewrite expgS /= IHk exprS. Qed.

(* Euler's theorem: any unit raised to phi(n) equals 1 *)
Lemma euler_unit (x : {unit 'Z_n}) : (val x) ^+ phi_n = 1.
Proof.
  rewrite -val_unit_exp /phi_n.
  have Hmem : x \in [set: {unit 'Z_n}] by rewrite in_setT.
  by rewrite expg_cardG.
Qed.

(* ========================================================================== *)
(*                         Homomorphic Properties                              *)
(* ========================================================================== *)

(* Exponentiation of y depends only on exponent mod r *)
Lemma expr_modr (k : nat) : (val y) ^+ k = (val y) ^+ (k %% r)%N.
Proof.
  rewrite {1}(divn_eq k r) exprD exprM exprAC y_order_r expr1n mul1r.
  reflexivity.
Qed.

(* Helper: 'Z_r elements as nats are bounded by r *)
Lemma Zp_val_ltn (x : 'Z_r) : ((x : nat) < r)%N.
Proof.
  case: r r_gt1 x => [|[|r']].
  - done.
  - done.
  - move=> _ x.
    exact: ltn_ord.
Qed.

(* Encryption multiplication distributes as addition on messages *)
Lemma enc_mul_dist : forall (m1 m2 : 'Z_r) (u1 u2 : {unit 'Z_n}),
  benaloh_enc m1 u1 * benaloh_enc m2 u2 =
  benaloh_enc (m1 + m2) (u1 * u2).
Proof.
  move=> m1 m2 u1 u2.
  rewrite /benaloh_enc /= exprMn mulrACA -exprD.
  rewrite (expr_modr (m1 + m2)).
  congr (_ * _).
  congr ((val y) ^+ _).
  have H := Zp_add_eqmod r_gt1 m1 m2.
  move: H; rewrite /eqn => H.
  have Hlt := Zp_val_ltn (m1 + m2)%R.
  by rewrite H modn_small.
Qed.

(* Encryption exponentiation distributes as scalar multiplication *)
Lemma enc_exp_dist : forall (m1 : 'Z_r) (m2 : nat) (u : {unit 'Z_n}),
  (benaloh_enc m1 u) ^+ m2 = benaloh_enc (m1 *+ m2) (u ^+ m2).
Proof.
  move=> m1 m2 u.
  rewrite /benaloh_enc (exprMn_comm _ (mulrC _ _)) -!exprM [(r * m2)%N]mulnC.
  rewrite val_unit_exp.
  congr (_ * _).
  - rewrite (expr_modr (m1 * m2)) (expr_modr (m1 *+ m2)).
    f_equal.
    have H := Zp_mulrn_eqmod r_gt1 m1 m2.
    move: H; rewrite /eqn => H.
    have Hlt := Zp_val_ltn (m1 *+ m2)%R.
    by rewrite H modn_small.
  - by rewrite exprM.
Qed.

(* ========================================================================== *)
(*                    Fazio-Nicolosi Condition Lemmas                         *)
(* ========================================================================== *)

(* alpha * r = phi_n (alpha is well-defined) *)
Lemma alpha_phi : (alpha * r = phi_n)%N.
Proof. rewrite /alpha. exact: divnK. Qed.

(* r-th powers vanish when raised to alpha (subgroup structure) *)
Lemma rth_powers_vanish (u : {unit 'Z_n}) : (val u) ^+ r ^+ alpha = 1.
Proof.
  rewrite -exprM (mulnC r alpha) alpha_phi.
  exact: euler_unit.
Qed.

(* We need a hypothesis about y^alpha having exact order r.
   This ensures unique decryption - distinct messages give distinct ciphertexts.

   Status: Could potentially be proved if we strengthen the condition on y:
   - Need #[y] = r exactly (not just y^r = 1, but exact order)
   - Then #[y^alpha] would need analysis, but with exact order r for y,
     y^alpha generates a subgroup where the map m -> y^(alpha*m) is injective. *)
Hypothesis y_alpha_injective : forall (m1 m2 : 'Z_r),
  (val y) ^+ (alpha * m1) = (val y) ^+ (alpha * m2) -> m1 = m2.

(* Raising ciphertext to alpha strips randomness *)
Lemma ciphertext_to_alpha (m : 'Z_r) (u : {unit 'Z_n}) :
  (benaloh_enc m u) ^+ alpha = (val y) ^+ (alpha * m).
Proof.
  rewrite /benaloh_enc exprMn_comm; last by apply mulrC.
  rewrite -!exprM (mulnC (m : nat) alpha).
  have ->: (val u) ^+ (r * alpha) = (val u) ^+ r ^+ alpha by rewrite exprM.
  by rewrite rth_powers_vanish mulr1.
Qed.

(* Distinct messages give distinct alpha-powers (unique decryption) *)
Lemma decryption_unique (m1 m2 : 'Z_r) (u1 u2 : {unit 'Z_n}) :
  (benaloh_enc m1 u1) ^+ alpha = (benaloh_enc m2 u2) ^+ alpha ->
  m1 = m2.
Proof.
  rewrite !ciphertext_to_alpha.
  exact: y_alpha_injective.
Qed.

End BenalohEuler.
