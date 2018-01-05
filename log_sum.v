(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype finfun bigop finset.
Require Import Reals Fourier Rpower.
Require Import Reals_ext Rssr Ranalysis_ext log2 ln_facts Rbigop.

Local Open Scope reals_ext_scope.

Local Notation "'\rsum_{' C '}' f" :=
  (\rsum_(a | a \in C) f a) (at level 10, format "\rsum_{ C }  f").

Definition log_sum_stmt {A : finType} (C : {set A}) (f g : A -> R+) :=
  f << g ->
  \rsum_{C} f * log (\rsum_{C} f / \rsum_{C} g) <= \rsum_(a | a \in C) f a * log (f a / g a).

Lemma log_sum1 {A : finType} (C : {set A}) (f g : A -> R+) :
  (forall a, a \in C -> 0 < f a) -> log_sum_stmt C f g.
Proof.
move=> fspos fg.
case/boolP : (C == set0) => [ /eqP -> | Hc].
  rewrite !big_set0 mul0R; by apply Rle_refl.
have gspos : forall a, a \in C -> 0 < g a.
  move=> a a_C.
  case/Rle_lt_or_eq_dec : ((pos_f_nonneg g) a) => // abs; symmetry in abs; apply fg in abs.
  move: (fspos _ a_C); by rewrite abs; move/Rlt_irrefl.
have Fnot0 : \rsum_{ C } f <> 0.
  move=> abs; symmetry in abs.
  move/(@Req_0_rmul_inv _ (mem C) (pos_f f) (pos_f_nonneg f)) in abs.
  case/set0Pn : Hc => a a_C.
  move: (fspos _ a_C).
  rewrite -abs //; by move/Rlt_irrefl.
have Gnot0 : \rsum_{ C } g <> 0.
  move=> abs; symmetry in abs.
  move/(@Req_0_rmul_inv _ (mem C) (pos_f g) (pos_f_nonneg g)) in abs.
  case/set0Pn : Hc => a a_C.
  move: (gspos _ a_C).
  rewrite -abs //; by move/Rlt_irrefl.
wlog : Fnot0 g Gnot0 fg gspos / \rsum_{ C } f = \rsum_{ C } g.
  move=> Hwlog.
  set k := \rsum_{ C } f / \rsum_{ C } g.
  have Fspos : 0 < \rsum_{ C } f.
    suff Fpos : 0 <= \rsum_{ C } f.
      apply Rlt_le_neq => //; by apply not_eq_sym.
    apply: Rle_big_0_P_g => a C_a; exact/ltRW/fspos.
  have Gspos : 0 < \rsum_{ C } g.
    suff Gpocs : 0 <= \rsum_{ C } g.
      apply Rlt_le_neq => //; by apply not_eq_sym.
    apply: Rle_big_0_P_g => a C_a; exact/ltRW/gspos.
  have kspos : 0 < k by apply Rlt_mult_inv_pos.
  have kg_pos : forall a, 0 <= k * g a.
    move=> a; apply mulR_ge0; by [apply ltRW | apply pos_f_nonneg].
  have kabs_con : forall a, k * g a = 0 -> f a = 0.
    move=> a.
    case/Rmult_integral.
    - move=> Hk; rewrite Hk in kspos; by move/Rlt_irrefl : kspos.
    - by move/fg.
  have kgspos : forall a, a \in C -> 0 < k * g a.
    move=> a a_C; apply mulR_gt0 => //; by apply gspos.
  have Hkg : \rsum_(a | a \in C) k * g a = \rsum_{C} f.
    by rewrite -big_distrr /= /k /Rdiv -mulRA mulRC Rinv_l // mul1R.
  have Htmp : \rsum_{ C } {| pos_f := fun x : A => k * g x; pos_f_nonneg := kg_pos |} <> 0.
    by rewrite /= Hkg.
  symmetry in Hkg.
  move: {Hwlog}(Hwlog Fnot0 (@mkPosFun _ (fun x => (k * g x)) kg_pos) Htmp kabs_con kgspos Hkg) => /= Hwlog.
  rewrite Hkg {1}/Rdiv Rinv_r // log_1 Rmult_0_r in Hwlog.
  set rhs := \rsum_(_ | _) _ in Hwlog.
  rewrite (_ : rhs = \rsum_(a | a \in C) (f a * log (f a / g a) - f a * log k)) in Hwlog; last first.
    rewrite /rhs.
    apply eq_bigr => a a_C.
    rewrite /Rdiv log_mult; last 2 first.
      by apply fspos.
      apply Rinv_0_lt_compat, mulR_gt0 => //; by apply gspos.
    rewrite log_Rinv; last first.
      apply mulR_gt0 => //; exact: gspos.
    rewrite log_mult //; last exact: gspos.
    rewrite log_mult //; last 2 first.
      by apply fspos.
      apply Rinv_0_lt_compat; by [apply gspos | apply fspos].
    rewrite log_Rinv; by [field | apply gspos].
  rewrite big_split /= -(big_morph _ morph_Ropp oppR0) -big_distrl /= in Hwlog.
  have : forall a b, 0 <= a + - b -> b <= a by move=> *; fourier.
  by apply.
move=> Htmp; rewrite Htmp.
rewrite /Rdiv Rinv_r; last by rewrite -Htmp.
rewrite log_1 mulR0.
suff : 0 <= \rsum_(a | a \in C) f a * ln (f a / g a).
  move=> H.
  rewrite /log /Rdiv.
  set rhs := \rsum_( _ | _ ) _.
  have -> : rhs = \rsum_(H | H \in C) (f H * (ln (f H / g H))) / ln 2.
    rewrite /rhs.
    apply eq_bigr => a a_C; by rewrite /Rdiv -mulRA.
  rewrite -big_distrl /=.
  apply mulR_ge0 => //; by apply ltRW, Rinv_0_lt_compat, ln_2_pos.
apply Rle_trans with (\rsum_(a | a \in C) f a * (1 - g a / f a)).
  apply Rle_trans with (\rsum_(a | a \in C) (f a - g a)).
    rewrite big_split /= -(big_morph _ morph_Ropp oppR0); fourier.
  apply Req_le, eq_bigr => a a_C.
  rewrite Rmult_minus_distr_l mulR1.
  case: (Req_EM_T (g a) 0).
    move=> ->; by rewrite /Rdiv mul0R mulR0.
  move=> ga_not_0.
  field; exact/gtR_eqF/(fspos _ a_C).
apply: Rle_big_P_f_g => a C_a.
apply Rmult_le_compat_l; first by apply ltRW, fspos.
apply Ropp_le_cancel.
rewrite -ln_Rinv; last first.
  apply Rlt_mult_inv_pos; by [apply fspos | apply gspos].
rewrite Rinv_mult_distr; last 2 first.
  exact/gtR_eqF/(fspos _ C_a).
  apply Rinv_neq_0_compat; exact/gtR_eqF/(gspos _ C_a).
rewrite invRK; last exact/gtR_eqF/(gspos _ C_a).
rewrite mulRC.
eapply Rle_trans.
  apply ln_id_cmp.
  apply Rlt_mult_inv_pos; by [apply gspos | apply fspos].
apply Req_le.
field; exact/gtR_eqF/(fspos _ C_a).
Qed.

(** * The log-sum Inequality *)

Lemma log_sum {A : finType} (C : {set A}) (f g : A -> R+) :
  log_sum_stmt C f g.
Proof.
move=> fg.
set D := [set a | (a \in C) && (f a != 0)].
suff : \rsum_{D} f * log (\rsum_{D} f / \rsum_{D} g) <=
       \rsum_(a | a \in D) f a * log (f a / g a).
  move=> H.
  set D' := [set a in C | f a == 0].
  have DUD' : C = D :|: D'.
    apply/setP => a.
    move Hlhs : (a \in C) => lhs.
    destruct lhs => //.
      symmetry.
      rewrite in_setU /C1 /C1 !in_set Hlhs /=.
      by destruct (f a == 0).
    by rewrite in_setU in_set Hlhs /= /C1 in_set Hlhs.
  have DID' : [disjoint D & D'].
    rewrite -setI_eq0.
    apply/eqP/setP => a.
    rewrite in_set0 /C1 /C1 in_setI !in_set.
    destruct (a \in C) => //=; by rewrite andNb.
  have H1 : \rsum_{C} f = \rsum_{D} f.
    rewrite setUC in DUD'.
    rewrite (rsum_union f DID' DUD').
    rewrite (_ : \rsum_{D'} f = \rsum_(a | a \in D') 0); last first.
      apply eq_bigr => a a_C2.
      rewrite /D' in_set in a_C2.
      by case/andP : a_C2 => _ /eqP.
    by rewrite big_const iter_Rplus mulR0 add0R.
  rewrite -H1 in H.
  have pos_F : 0 <= \rsum_{C} f.
    apply Rle_big_0_P_g => ? ?; by apply pos_f_nonneg.
  apply Rle_trans with (\rsum_{C} f * log (\rsum_{C} f / \rsum_{D} g)).
    case/Rle_lt_or_eq_dec : pos_F => pos_F; last first.
      rewrite -pos_F !mul0R; by apply Rle_refl.
    have H2 : 0 <= \rsum_(a | a \in D) g a.
      apply: Rle_big_0_P_g => a _; by apply pos_f_nonneg.
    case/Rle_lt_or_eq_dec : H2 => H2; last first.
      have : 0 = \rsum_{D} f.
        transitivity (\rsum_(a | a \in D) 0).
          by rewrite big_const iter_Rplus Rmult_0_r.
        apply eq_bigr => a a_C1.
        rewrite fg //.
        by rewrite -(@Req_0_rmul_inv _ (mem D) (pos_f g) (pos_f_nonneg g) H2) //.
      move=> abs; rewrite -abs in H1; rewrite H1 in pos_F.
      by move/Rlt_irrefl : pos_F.
    have H3 : 0 < \rsum_(a | a \in C) g a.
      rewrite setUC in DUD'.
      rewrite (rsum_union g DID' DUD').
      apply Rplus_le_lt_0_compat => //.
      apply: Rle_big_0_P_g => *; by apply pos_f_nonneg.
    apply Rmult_le_compat_l; first exact/ltRW.
    apply log_increasing_le.
      apply Rlt_mult_inv_pos => //; by rewrite -HG.
    apply Rmult_le_compat_l; first exact/ltRW.
    apply Rle_Rinv => //.
    rewrite setUC in DUD'.
    rewrite (rsum_union g DID' DUD').
    rewrite -[X in X <= _]add0R.
    apply Rplus_le_compat_r.
    apply: Rle_big_0_P_g => a C2_a; by apply pos_f_nonneg.
  eapply Rle_trans; first by apply H.
  rewrite setUC in DUD'.
  rewrite (rsum_union (fun a => f a * log (f a / g a)) DID' DUD').
  rewrite (_ : \rsum_(_ | _ \in D') _ = 0); last first.
    transitivity (\rsum_(a | a \in D') 0).
      apply eq_bigr => a.
      rewrite /D' in_set.
      case/andP => a_C /eqP fa0.
      by rewrite fa0 mul0R.
    by rewrite big_const iter_Rplus Rmult_0_r.
  rewrite add0R; by apply Rle_refl.
apply log_sum1 => // a.
rewrite /C1 in_set.
case/andP => a_C fa_not_0.
case/Rle_lt_or_eq_dec: (pos_f_nonneg f a) => // abs.
by rewrite abs eqxx in fa_not_0.
Qed.
