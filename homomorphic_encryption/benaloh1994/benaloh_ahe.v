From HB Require Import structures.

From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import cyclic zmodp ssrfun.
Require Import he_types.
Require Import enc_dec.
Require Import ahe_enc.
Require Import ahe_monoid.
Require Import benaloh_enc.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Section benaloh_keys.

Variable n : nat.
Hypothesis n_gt1 : (1 < n)%N.
Variable r : nat.
Hypothesis r_gt1 : (1 < r)%N.

(* phi(n) = |Z_n^*| *)
Definition phi_n := #|[set: {unit 'Z_n}]|.

(* ============================================================ *)
(*  Public Key: Contains generator and its order property       *)
(* ============================================================ *)

Record BenalohPubKey := MkBenalohPubKey {
  pub_gen : {unit 'Z_n} ;                    (* Generator y *)
  pub_gen_order : (val pub_gen) ^+ r = 1 ;   (* y^r = 1 *)
}.

(* ============================================================ *)
(*  Private Key: Contains everything needed for decryption      *)
(* ============================================================ *)

(*
  Without priv_injective, if $y = 1$, then $y^r = 1$ holds trivially,
  but decryption would fail (all messages encrypt indistinguishably
  modulo randomness). However, we may derive it from a more primitive
  assumption (e.g., that $y$ has exact order $r$,
  stated as #[y] = r using the MathComp order function).
*)

Record BenalohPrivKey := MkBenalohPrivKey {
  priv_gen : {unit 'Z_n} ;                   (* Generator y *)
  priv_gen_order : (val priv_gen) ^+ r = 1 ; (* y^r = 1 *)
  priv_r_div_phi : (r %| phi_n)%N ;
  priv_injective : forall (m1 m2 : 'Z_r),
    (val priv_gen) ^+ ((phi_n %/ r) * m1) =
    (val priv_gen) ^+ ((phi_n %/ r) * m2) -> m1 = m2 ;
}.

(* Extract public key from private key *)
Definition pub_of_priv (priv_key : BenalohPrivKey) : BenalohPubKey :=
  MkBenalohPubKey (priv_gen_order priv_key).

End benaloh_keys.

Section benaloh_instance.

Variable n r : nat.
Hypothesis n_gt1 : (1 < n)%N.
Hypothesis r_gt1 : (1 < r)%N.

Definition BenalohHETypes : HETypes :=
  MkHE 'Z_r {unit 'Z_n} 'Z_n (BenalohPubKey n r) (BenalohPrivKey n r).

Definition enc_for_mixin
  (k : BenalohPubKey n r) (m : 'Z_r) (u : {unit 'Z_n}) : 'Z_n :=
  benaloh_enc (pub_gen k) m u.

Definition dec_for_mixin
  (dk : BenalohPrivKey n r) (c : 'Z_n) : option 'Z_r :=
  benaloh_dec r (priv_gen dk) (phi_n n %/ r) c.

Lemma dec_correct_mixin (dk : BenalohPrivKey n r)
  (u : {unit 'Z_n}) (m : 'Z_r) :
  dec_for_mixin dk
    (enc_for_mixin (pub_of_priv dk) m u) = Some m.
Proof.
  rewrite /dec_for_mixin /enc_for_mixin /pub_of_priv /=.
  exact (@benaloh_dec_correct n r
    (priv_r_div_phi dk) (priv_gen dk) (@priv_injective _ _ dk) m u).
Qed.

HB.instance Definition Benaloh_isEncDec :=
  @isEncDec.Build BenalohHETypes
    enc_for_mixin
    dec_for_mixin
    (@pub_of_priv n r)
    dec_correct_mixin.

Definition enc_curry (k : BenalohPubKey n r)
    : 'Z_r * {unit 'Z_n} -> 'Z_n :=
  fun mr => enc_for_mixin k mr.1 mr.2.
Definition Emul (c1 c2 : 'Z_n) : 'Z_n := c1 * c2.
Definition Epow (c : 'Z_n) (m : 'Z_r) : 'Z_n := c ^+ (m : nat).
Definition rand_pow (u : {unit 'Z_n}) (m : 'Z_r) : {unit 'Z_n} :=
  (u ^+ (m : nat))%g.
Definition rand_mul (u : {unit 'Z_n}) (v : {unit 'Z_n}) : {unit 'Z_n} :=
  u * v.

(* The reason we re-define notations already in ahe_enc.v is because the type
   now is different. In there, it is abstract types like rand T and plain T.
   If we just use the notations from there, the type we use here like 'Z_r
   cannot work. *)
Local Notation BT := BenalohHETypes.
Local Notation "E[ k ]" := (enc_curry k) (at level 10).
Local Notation "x {[ o ; p ]} y" := (mr_bop BT o p x y)
  (at level 50, left associativity).
Local Notation "x {< o ; p >} j" := (mr_bop_rplain BT o p x j)
  (at level 50, left associativity).
Local Notation "x (.) y" := (Emul x y) (at level 40, left associativity).
Local Notation "x (^) y" := (Epow x y) (at level 40, left associativity).
Local Notation "^r" := (rand_pow).
Local Notation "*r" := (rand_mul).
Local Notation "*m" := (GRing.mul).

Lemma Emul_addM : forall (k : BenalohPubKey n r),
  {morph E[k] : mr1 mr2 / mr1 {[ +%R ; *r ]} mr2 >-> Emul mr1 mr2}.
Proof.
  move=> p [m1 u1] [m2 u2].
  rewrite /mr_bop /enc_curry /Emul /enc_for_mixin /rand_mul /=.
  apply/esym.
  exact: (enc_mul_dist r_gt1 (pub_gen_order p)).
Qed.

Lemma Epow_scalarM : forall (k : BenalohPubKey n r) (j : 'Z_r),
  {morph E[k] : mr / mr {< *%R ; ^r >} j >-> Epow mr j}.
Proof.
  move=> p j [m u].
  rewrite /mr_bop_rplain /enc_curry /Epow /enc_for_mixin /rand_pow /=.
  apply/esym.
  rewrite (enc_exp_dist r_gt1 (pub_gen_order p)).
  congr (benaloh_enc _ _ _).
  by rewrite -mulr_natr natr_Zp.
Qed.

HB.instance Definition Benaloh_isAHEnc :=
  @isAHEnc.Build BenalohHETypes
    Emul Epow rand_pow rand_mul
    Emul_addM Epow_scalarM.

(* ========================================================================== *)
(*                   isAHEMonoid Instance                                     *)
(* ========================================================================== *)

Definition benaloh_rand_id : {unit 'Z_n} := 1%g.

Lemma benaloh_Emul_assoc : associative Emul.
Proof. by move=> x y z; rewrite /Emul mulrA. Qed.

Lemma benaloh_Emul_comm : commutative Emul.
Proof. by move=> x y; rewrite /Emul mulrC. Qed.

Lemma benaloh_Emul_id :
  forall k : pub_key BT,
  left_id (ahe_enc.enc_curry BT k (0, benaloh_rand_id)) (@Emul).
Proof.
  move=> k x.
  rewrite /ahe_enc.enc_curry /= /Emul.
  change (enc_for_mixin k 0 1%g * x = x).
  rewrite /enc_for_mixin /benaloh_enc.
  by rewrite expr0 mul1r FinRing.val_unit1 expr1n mul1r.
Qed.

HB.instance Definition Benaloh_isAHEMonoid :=
  @isAHEMonoid.Build BenalohHETypes
    benaloh_rand_id
    benaloh_Emul_assoc benaloh_Emul_comm benaloh_Emul_id.

End benaloh_instance.
