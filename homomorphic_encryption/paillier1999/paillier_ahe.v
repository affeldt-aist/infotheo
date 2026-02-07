From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg zmodp ssrfun.
Require Import he_types.
Require Import enc_dec.
Require Import ahe_enc.
Require Import ahe_monoid.
Require Import paillier_enc.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Section paillier_keys.

Variable n : nat.
Let n2 := (n * n)%N.

Record PaillierPubKey := MkPaillierPubKey {
  pub_gen : 'Z_n2 ;
  pub_gen_order : pub_gen ^+ n = 1 ;
}.

Record PaillierPrivKey := MkPaillierPrivKey {
  priv_gen : 'Z_n2 ;
  priv_gen_order : priv_gen ^+ n = 1 ;
  priv_lambda : nat ;
  priv_carmichael : forall (r : {unit 'Z_n2}), (val r) ^+ (n * priv_lambda) = 1 ;
  priv_injective : forall (m1 m2 : 'Z_n),
    priv_gen ^+ (priv_lambda * m1) = priv_gen ^+ (priv_lambda * m2) -> m1 = m2 ;
}.

Definition pub_of_priv (pk : PaillierPrivKey) : PaillierPubKey :=
  MkPaillierPubKey (priv_gen_order pk).

End paillier_keys.

Section paillier_instance.

Variable n : nat.
Hypothesis n_gt1 : (1 < n)%N.
Let n2 := (n * n)%N.

Definition PaillierHETypes : HETypes :=
  MkHE 'Z_n {unit 'Z_n2} 'Z_n2 (PaillierPubKey n) (PaillierPrivKey n).

Definition paillier_enc_for_mixin
  (k : PaillierPubKey n) (m : 'Z_n) (u : {unit 'Z_n2}) : 'Z_n2 :=
  paillier_enc.paillier_enc (pub_gen k) m u.

Definition paillier_dec_for_mixin
  (dk : PaillierPrivKey n) (c : 'Z_n2) : option 'Z_n :=
  paillier_enc.paillier_dec (priv_gen dk) (priv_lambda dk) c.

Lemma paillier_dec_correct_mixin (dk : PaillierPrivKey n)
  (u : {unit 'Z_n2}) (m : 'Z_n) :
  paillier_dec_for_mixin dk
    (paillier_enc_for_mixin (pub_of_priv dk) m u) = Some m.
Proof.
  rewrite /paillier_dec_for_mixin /paillier_enc_for_mixin /pub_of_priv /=.
  exact (@paillier_enc.paillier_dec_correct n (priv_gen dk) (priv_lambda dk)
    (priv_carmichael dk) (@priv_injective _ dk) m u).
Qed.

HB.instance Definition Paillier_isEncDec :=
  @isEncDec.Build PaillierHETypes
    paillier_enc_for_mixin
    paillier_dec_for_mixin
    (@pub_of_priv n)
    paillier_dec_correct_mixin.

(* Use abstract types from HETypes so HB.instance type-checks *)
Definition paillier_Emul : cipher PaillierHETypes -> cipher PaillierHETypes -> cipher PaillierHETypes :=
  fun c1 c2 => c1 * c2.
Definition paillier_Epow : cipher PaillierHETypes -> plain PaillierHETypes -> cipher PaillierHETypes :=
  fun c m => c ^+ (m : nat).
Definition paillier_rand_pow : rand PaillierHETypes -> plain PaillierHETypes -> rand PaillierHETypes :=
  fun u m => (u ^+ (m : nat))%g.
Definition paillier_rand_mul : rand PaillierHETypes -> rand PaillierHETypes -> rand PaillierHETypes :=
  fun u v => (u * v)%g.

Lemma paillier_Emul_addM :
    forall (k : pub_key PaillierHETypes),
    {morph enc_curry PaillierHETypes k
      : mr1 mr2 / mr_bop PaillierHETypes +%R paillier_rand_mul mr1 mr2
      >-> paillier_Emul mr1 mr2}.
Proof.
  move=> p [m1 u1] [m2 u2].
  rewrite /mr_bop /enc_curry /paillier_Emul /paillier_rand_mul /=.
  apply/esym.
  exact: (enc_mul_dist n_gt1 (pub_gen_order p)).
Qed.

Lemma paillier_Epow_scalarM :
    forall (k : pub_key PaillierHETypes) (j : plain PaillierHETypes),
    {morph enc_curry PaillierHETypes k
      : mr / mr_bop_rplain PaillierHETypes *%R paillier_rand_pow mr j
      >-> paillier_Epow mr j}.
Proof.
  move=> p j [m u].
  rewrite /mr_bop_rplain /enc_curry /paillier_Epow /paillier_rand_pow /=.
  apply/esym.
  rewrite (enc_exp_dist n_gt1 (pub_gen_order p)).
  congr (paillier_enc.paillier_enc _ _ _).
  by rewrite -mulr_natr natr_Zp.
Qed.

HB.instance Definition Paillier_isAHEnc :=
  @isAHEnc.Build PaillierHETypes
    paillier_Emul
    paillier_Epow
    paillier_rand_pow
    paillier_rand_mul
    paillier_Emul_addM
    paillier_Epow_scalarM.

(* ========================================================================== *)
(*                   isAHEMonoid Instance                                     *)
(* ========================================================================== *)

Local Notation PT := PaillierHETypes.

Definition paillier_rand_id : {unit 'Z_n2} := 1%g.

Lemma paillier_Emul_assoc : associative paillier_Emul.
Proof. by move=> x y z; rewrite /paillier_Emul mulrA. Qed.

Lemma paillier_Emul_comm : commutative paillier_Emul.
Proof. by move=> x y; rewrite /paillier_Emul mulrC. Qed.

Lemma paillier_Emul_id :
  forall k : pub_key PT,
  left_id (enc_curry PT k (0, paillier_rand_id)) paillier_Emul.
Proof.
  move=> k x.
  rewrite /enc_curry /= /paillier_Emul.
  change (paillier_enc_for_mixin k 0 1%g * x = x).
  rewrite /paillier_enc_for_mixin /paillier_enc.paillier_enc.
  by rewrite expr0 mul1r FinRing.val_unit1 expr1n mul1r.
Qed.

HB.instance Definition Paillier_isAHEMonoid :=
  @isAHEMonoid.Build PaillierHETypes
    paillier_rand_id
    paillier_Emul_assoc paillier_Emul_comm paillier_Emul_id.

End paillier_instance.
