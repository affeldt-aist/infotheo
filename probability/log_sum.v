(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect.
Require Import Reals Lra.
From mathcomp Require Import Rstruct.
Require Import ssrR Reals_ext Ranalysis_ext logb ln_facts bigop_ext Rbigop.

(******************************************************************************)
(*                        The log-sum Inequality                              *)
(******************************************************************************)

Local Open Scope reals_ext_scope.
Local Open Scope R_scope.

Local Notation "'\sum_{' C '}' f" :=
  (\sum_(a | a \in C) f a) (at level 10, format "\sum_{ C }  f").

Definition log_sum_stmt {A : finType} (C : {set A}) (f g : A ->R+) :=
  f `<< g ->
  \sum_{C} f * log (\sum_{C} f / \sum_{C} g) <=
    \sum_(a | a \in C) f a * log (f a / g a).

Lemma log_sum1 {A : finType} (C : {set A}) (f g : A ->R+) :
  (forall a, a \in C -> 0 < f a) -> log_sum_stmt C f g.
Proof.
move=> fspos fg.
case/boolP : (C == set0) => [ /eqP -> | Hc].
  rewrite !big_set0 mul0R; exact/leRR.
have gspos : forall a, a \in C -> 0 < g a.
  move=> a a_C; case/Rle_lt_or_eq_dec : ((nneg_finfun_ge0 g) a) => //.
  move=> /esym/(dominatesE fg) abs.
  by move: (fspos _ a_C); rewrite abs => /ltRR.
have Fnot0 : \sum_{ C } f != 0.
  apply/eqP => /psumR_eq0P abs.
  case/set0Pn : Hc => a aC.
  move: (fspos _ aC); rewrite abs //; last by move=> b bC; apply/ltRW/fspos.
  by move/ltRR.
have Gnot0 : \sum_{ C } g != 0.
  apply/eqP => /psumR_eq0P abs.
  case/set0Pn : Hc => a aC.
  move: (gspos _ aC); rewrite abs //; last by move=> b bC; apply/ltRW/gspos.
  by move/ltRR.
wlog : Fnot0 g Gnot0 fg gspos / \sum_{ C } f = \sum_{ C } g.
  move=> Hwlog.
  set k := \sum_{ C } f / \sum_{ C } g.
  have Fspos : 0 < \sum_{ C } f.
    suff Fpos : 0 <= \sum_{ C } f by apply/ltRP; rewrite lt0R Fnot0; exact/leRP.
    by apply: sumR_ge0 => ? ?; exact/ltRW/fspos.
  have Gspos : 0 < \sum_{ C } g.
    suff Gpocs : 0 <= \sum_{ C } g by apply/ltRP; rewrite lt0R Gnot0; exact/leRP.
    by apply: sumR_ge0 => ? ?; exact/ltRW/gspos.
  have kspos : 0 < k by apply divR_gt0.
  have kg_pos : [forall a, 0 <b= [ffun x => k * g x] a].
    apply/forallP => a.
    by rewrite ffunE; apply/leRP/mulR_ge0; [exact: ltRW|exact: nneg_finfun_ge0].
  have kabs_con : f `<< mkNNFinfun kg_pos.
    by apply/dominates_scale => //; exact/gtR_eqF.
  have kgspos : forall a, a \in C -> 0 < (mkNNFinfun kg_pos) a.
    by move=> a a_C; rewrite ffunE; apply mulR_gt0 => //; exact: gspos.
  have Hkg : \sum_{C} (mkNNFinfun kg_pos) = \sum_{C} f.
    transitivity (\sum_(a in C) k * g a).
      by apply eq_bigr => a aC; rewrite /= ffunE.
    by rewrite -big_distrr /= /k /Rdiv -mulRA mulRC mulVR // mul1R.
  have Htmp : \sum_{ C } (mkNNFinfun kg_pos) != 0.
    rewrite /=.
    evar (h : A -> R); rewrite (eq_bigr h); last first.
      by move=> a aC; rewrite ffunE /h; reflexivity.
    rewrite {}/h (_ : \sum_(i in C) _ = \sum_{C} f) // -Hkg.
    by apply eq_bigr => a aC /=; rewrite ffunE.
  symmetry in Hkg.
  move: {Hwlog}(Hwlog Fnot0 (@mkNNFinfun _ _ kg_pos) Htmp kabs_con kgspos Hkg) => /= Hwlog.
  rewrite Hkg {1}/Rdiv mulRV // /log Log_1 mulR0 in Hwlog.
  set rhs := \sum_(_ | _) _ in Hwlog.
  rewrite (_ : rhs = \sum_(a | a \in C) (f a * log (f a / g a) - f a * log k)) in Hwlog; last first.
    rewrite /rhs.
    apply eq_bigr => a a_C.
    rewrite /Rdiv /log LogM; last 2 first.
      exact/fspos.
      rewrite ffunE; apply/invR_gt0/mulR_gt0 => //; exact/gspos.
    rewrite LogV; last first.
      rewrite ffunE; apply mulR_gt0 => //; exact: gspos.
    rewrite ffunE LogM //; last exact: gspos.
    rewrite LogM //; last 2 first.
      exact/fspos.
      by apply invR_gt0 => //; apply gspos.
    by rewrite LogV; [field | apply gspos].
  rewrite big_split /= -big_morph_oppR -big_distrl /= in Hwlog.
  have : forall a b, 0 <= a + - b -> b <= a by move=> *; lra.
  exact.
move=> Htmp; rewrite Htmp.
rewrite /Rdiv mulRV; last by rewrite -Htmp.
rewrite /log Log_1 mulR0.
suff : 0 <= \sum_(a | a \in C) f a * ln (f a / g a).
  move=> H.
  rewrite /log /Rdiv.
  set rhs := \sum_( _ | _ ) _.
  have -> : rhs = \sum_(H | H \in C) (f H * (ln (f H / g H))) / ln 2.
    rewrite /rhs.
    apply eq_bigr => a a_C; by rewrite /Rdiv -mulRA.
  rewrite -big_distrl /=.
  by apply mulR_ge0 => //; exact/invR_ge0.
apply (@leR_trans (\sum_(a | a \in C) f a * (1 - g a / f a))).
  apply (@leR_trans (\sum_(a | a \in C) (f a - g a))).
    rewrite big_split /= -big_morph_oppR Htmp addRN; exact/leRR.
  apply Req_le, eq_bigr => a a_C.
  rewrite mulRDr mulR1 mulRN.
  case: (Req_EM_T (g a) 0) => [->|ga_not_0].
    by rewrite div0R mulR0.
  by field; exact/eqP/gtR_eqF/(fspos _ a_C).
apply: leR_sumR => a C_a.
apply leR_wpmul2l; first exact/ltRW/fspos.
rewrite -[X in _ <= X]oppRK leR_oppr -ln_Rinv; last first.
  apply divR_gt0; by [apply fspos | apply gspos].
rewrite invRM; last 2 first.
  exact/gtR_eqF/(fspos _ C_a).
  by rewrite invR_neq0' // gtR_eqF //; exact/(gspos _ C_a).
rewrite invRK; last exact/gtR_eqF/(gspos _ C_a).
rewrite mulRC.
apply: leR_trans.
  by apply/ln_id_cmp/divR_gt0; [apply gspos | apply fspos].
apply Req_le.
by field; exact/eqP/gtR_eqF/(fspos _ C_a).
Qed.

Lemma log_sum {A : finType} (C : {set A}) (f g : A ->R+) :
  log_sum_stmt C f g.
Proof.
move=> fg.
set D := [set a | (a \in C) && (f a != 0)].
suff : \sum_{D} f * log (\sum_{D} f / \sum_{D} g) <=
       \sum_(a | a \in D) f a * log (f a / g a).
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
    by destruct (a \in C) => //=; rewrite andNb.
  have H1 : \sum_{C} f = \sum_{D} f.
    rewrite setUC in DUD'.
    rewrite DUD' (big_union _ f DID') /=.
    rewrite (_ : \sum_{D'} f = \sum_(a | a \in D') 0); last first.
      apply eq_bigr => a.
      rewrite /D' in_set.
      by case/andP => _ /eqP.
    by rewrite big_const iter_addR mulR0 add0R.
  rewrite -H1 in H.
  have pos_F : 0 <= \sum_{C} f.
    by apply sumR_ge0 => ? ?; exact: nneg_finfun_ge0.
  apply (@leR_trans (\sum_{C} f * log (\sum_{C} f / \sum_{D} g))).
    case/Rle_lt_or_eq_dec : pos_F => pos_F; last first.
      rewrite -pos_F !mul0R; exact/leRR.
    have H2 : 0 <= \sum_(a | a \in D) g a.
      by apply: sumR_ge0 => ? _; exact: nneg_finfun_ge0.
    case/Rle_lt_or_eq_dec : H2 => H2; last first.
      have : 0 = \sum_{D} f.
        transitivity (\sum_(a | a \in D) 0).
          by rewrite big_const iter_addR mulR0.
        apply eq_bigr => a a_C1.
        rewrite (dominatesE fg) // (proj1 (@psumR_eq0P _ (mem D) _ _)) // => ? ?.
        exact/nneg_finfun_ge0.
      move=> abs; rewrite -abs in H1; rewrite H1 in pos_F.
      by move/ltRR : pos_F.
    have H3 : 0 < \sum_(a | a \in C) g a.
      rewrite setUC in DUD'.
      rewrite DUD' (big_union _ g DID') /=.
      apply addR_gt0wr => //.
      by apply: sumR_ge0 => *; exact/nneg_finfun_ge0.
    apply/(leR_wpmul2l (ltRW pos_F))/Log_increasing_le => //.
      apply divR_gt0 => //; by rewrite -HG.
    apply/(leR_wpmul2l (ltRW pos_F))/leR_inv => //.
    rewrite setUC in DUD'.
    rewrite DUD' (big_union _ g DID') /= -[X in X <= _]add0R; apply leR_add2r.
    by apply: sumR_ge0 => ? ?; exact/nneg_finfun_ge0.
  apply: (leR_trans H).
  rewrite setUC in DUD'.
  rewrite DUD' (big_union _ (fun a => f a * log (f a / g a)) DID') /=.
  rewrite (_ : \sum_(_ | _ \in D') _ = 0); last first.
    transitivity (\sum_(a | a \in D') 0).
      apply eq_bigr => a.
      rewrite /D' in_set => /andP[a_C /eqP ->]; by rewrite mul0R.
    by rewrite big_const iter_addR mulR0.
  by rewrite add0R; exact/leRR.
apply log_sum1 => // a.
rewrite /C1 in_set.
case/andP => a_C fa_not_0.
case/Rle_lt_or_eq_dec: (nneg_finfun_ge0 f a) => // abs.
by rewrite abs eqxx in fa_not_0.
Qed.
