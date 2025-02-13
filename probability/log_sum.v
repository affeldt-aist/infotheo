(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect all_algebra lra.
From mathcomp Require Import Rstruct reals exp.
Require Import bigop_ext realType_ext realType_ln.

(**md**************************************************************************)
(* # The log-sum Inequality                                                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Import Order.POrderTheory GRing.Theory Num.Theory.

Local Notation "'\sum_{' C '}' f" :=
  (\sum_(a | a \in C) f a) (at level 10, format "\sum_{ C }  f").

Definition log_sum_stmt {R : realType} {A : finType} (C : {set A})
    (f g : {ffun A -> R}) :=
  (forall x, 0 <= f x) -> (forall x, 0 <= g x) ->
  f `<< g ->
  \sum_{C} f * log (\sum_{C} f / \sum_{C} g) <=
    \sum_(a | a \in C) f a * log (f a / g a).

Lemma log_sum1 {R : realType} {A : finType} (C : {set A}) (f g : {ffun A -> R}) :
  (forall a, a \in C -> 0 < f a) -> log_sum_stmt C f g.
Proof.
move=> fspos f0 g0 fg.
case/boolP : (C == set0) => [ /eqP -> | Hc].
  by rewrite !big_set0 mul0r lexx.
have gspos : forall a, a \in C -> 0 < g a.
  move=> a a_C.
  rewrite lt_neqAle g0 andbT; apply/eqP.
  move=>/esym/(dominatesE fg) abs.
  by move: (fspos _ a_C); rewrite abs ltxx.
have Fnot0 : \sum_{ C } f != 0.
  apply/eqP => /psumr_eq0P abs.
  case/set0Pn : Hc => a aC.
  move: (fspos _ aC); rewrite abs //.
  by rewrite ltxx.
have Gnot0 : \sum_{ C } g != 0.
  apply/eqP => /psumr_eq0P abs.
  case/set0Pn : Hc => a aC.
  by move: (gspos _ aC); rewrite abs // ltxx.
wlog : Fnot0 g g0 Gnot0 fg gspos / \sum_{ C } f = \sum_{ C } g.
  move=> Hwlog.
  set k := (\sum_{ C } f / \sum_{ C } g).
  have Fspos : 0 < \sum_{ C } f.
    suff Fpos : 0 <= \sum_{ C } f by rewrite lt0r Fnot0.
    by apply/sumr_ge0 => ? ?; exact/ltW/fspos.
  have Gspos : 0 < \sum_{ C } g.
    suff Gpocs : 0 <= \sum_{ C } g by rewrite lt0r Gnot0.
    by apply/sumr_ge0 => ? ?; exact/ltW/gspos.
  have kspos : 0 < k by exact: divr_gt0.
  set kg := [ffun x => k * g x].
  have kg_pos : forall a, 0 <= kg a.
    by move=> a; rewrite /kg /= ffunE; apply mulr_ge0 => //; exact: ltW.
  have kabs_con : f `<< kg.
    by apply/dominates_scale => //; rewrite ?gt_eqF//.
  have kgspos : forall a, a \in C -> 0 < kg a.
    by move=> a a_C; rewrite ffunE; apply mulr_gt0 => //; exact: gspos.
  have Hkg : \sum_{C} kg = \sum_{C} f.
    transitivity (\sum_(a in C) k * g a).
      by apply eq_bigr => a aC; rewrite /= ffunE.
    by rewrite -big_distrr /= /k -mulrA mulVf ?mulr1.
  have Htmp : \sum_{ C } kg != 0.
    rewrite /=.
    evar (h : A -> R); rewrite (eq_bigr h); last first.
      by move=> a aC; rewrite ffunE /h; reflexivity.
    rewrite {}/h (_ : \sum_(i in C) _ = \sum_{C} f) // -Hkg.
    by apply eq_bigr => a aC /=; rewrite ffunE.
  symmetry in Hkg.
  move: {Hwlog}(Hwlog Fnot0 kg kg_pos Htmp kabs_con kgspos Hkg) => /= Hwlog.
  rewrite Hkg mulfV // log1  mulr0 in Hwlog.
  set rhs := \sum_(_ | _) _ in Hwlog.
  rewrite (_ : rhs = \sum_(a | a \in C) (f a * log (f a / g a) - f a * log k)) in Hwlog; last first.
    rewrite /rhs.
    apply eq_bigr => a a_C.
    rewrite logM; last 2 first.
      exact/fspos.
      by rewrite ffunE invr_gt0// mulr_gt0//; exact/gspos.
    rewrite logV; last first.
      rewrite ffunE; apply mulr_gt0 => //; exact: gspos.
    rewrite ffunE logM //; last exact: gspos.
    rewrite logM //; last 2 first.
      exact/fspos.
      by rewrite invr_gt0//; apply gspos.
    by rewrite logV; [lra | apply gspos].
  rewrite big_split /= -big_morph_oppr -big_distrl /= in Hwlog.
  by rewrite -subr_ge0.
move=> Htmp; rewrite Htmp.
rewrite mulfV; last by rewrite -Htmp.
rewrite log1 mulr0.
suff : 0 <= \sum_(a | a \in C) f a * ln (f a / g a).
  move=> H.
  set rhs := \sum_( _ | _ ) _.
  have -> : rhs = \sum_(H | H \in C) (f H * (ln (f H / g H))) / ln 2.
    rewrite /rhs.
    by apply eq_bigr => a a_C; by rewrite -mulrA.
  rewrite -big_distrl /=.
  by rewrite mulr_ge0// invr_ge0// ln2_ge0.
apply (@le_trans _ _ (\sum_(a | a \in C) f a * (1 - g a / f a))).
  apply (@le_trans _ _ (\sum_(a | a \in C) (f a - g a))).
    by rewrite big_split /= -big_morph_oppr Htmp subrr.
  rewrite le_eqVlt; apply/orP; left; apply/eqP.
  apply/eq_bigr => a a_C.
  rewrite mulrDr mulr1 mulrN.
  have [->|ga_not_0] := eqVneq (g a) 0.
    by rewrite mul0r mulr0.
  by rewrite mulrCA divff ?mulr1// gt_eqF//; exact/(fspos _ a_C).
apply: ler_sum => a C_a.
apply ler_wpM2l; first exact/ltW/fspos.
rewrite -[X in _ <= X]opprK lerNr -lnV; last first.
  by rewrite posrE divr_gt0//; [apply fspos | apply gspos].
rewrite invfM.
rewrite invrK mulrC; apply: le_trans.
  by apply/ln_id_cmp; rewrite divr_gt0//; [apply gspos | apply fspos].
by rewrite opprB.
Qed.

Lemma log_sum {R : realType} {A : finType} (C : {set A}) (f g : {ffun A -> R}) :
  log_sum_stmt C f g.
Proof.
move=> f0 g0 fg.
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
      rewrite in_setU !in_set Hlhs /=.
      by destruct (f a == 0).
    by rewrite in_setU in_set Hlhs /= in_set Hlhs.
  have DID' : [disjoint D & D'].
    rewrite -setI_eq0.
    apply/eqP/setP => a.
    rewrite in_set0 in_setI !in_set.
    by destruct (a \in C) => //=; rewrite andNb.
  have H1 : \sum_{C} f = \sum_{D} f.
    rewrite setUC in DUD'.
    rewrite DUD' (big_union _ f DID') /=.
    rewrite (_ : \sum_{D'} f = \sum_(a | a \in D') 0); last first.
      apply eq_bigr => a.
      rewrite /D' in_set.
      by case/andP => _ /eqP.
    by rewrite big_const iter_addr addr0 mul0rn add0r.
  rewrite -H1 in H.
  have pos_F : 0 <= \sum_{C} f by apply/sumr_ge0 => ? ?.
  apply (@le_trans _ _ (\sum_{C} f * log (\sum_{C} f / \sum_{D} g))).
    move: pos_F; rewrite le_eqVlt => /predU1P[pos_F|pos_F].
      by rewrite -pos_F !mul0r.
    have H2 : 0 <= \sum_(a | a \in D) g a by apply/sumr_ge0.
    move: H2; rewrite le_eqVlt => /predU1P[g0'|gt0'].
      have : 0 = \sum_{D} f.
        transitivity (\sum_(a | a \in D) (0:R))%R.
          by rewrite big1.
        apply: eq_bigr => a a_C1.
        rewrite (dominatesE fg) //.
        by apply/(@psumr_eq0P _ _ (mem D)) => //.
      by move=> abs; rewrite -abs in H1; rewrite H1 ltxx in pos_F.
    have H3 : 0 < \sum_(a | a \in C) g a.
      rewrite setUC in DUD'.
      rewrite DUD' (big_union _ g DID') /=.
      rewrite ltr_pwDr//.
      by apply/sumr_ge0 => //.
    apply/ler_wpM2l => //.
      exact/ltW.
    rewrite ler_log// ?posrE//; last 2 first.
      by apply divr_gt0 => //; rewrite -HG.
      by apply divr_gt0 => //; rewrite -HG.
    apply/ler_wpM2l => //.
      exact/ltW.
    rewrite lef_pV2//.
    rewrite setUC in DUD'.
    rewrite DUD' (big_union _ g DID') /=.
    rewrite lerDr//.
    by apply/sumr_ge0.
  apply: (le_trans H).
  rewrite setUC in DUD'.
  rewrite DUD' (big_union _ (fun a => f a * log (f a / g a)) DID') /=.
  rewrite (_ : \sum_(_ | _ \in D') _ = 0); last first.
    transitivity (\sum_(a | a \in D') (0:R)).
      apply eq_bigr => a.
      by rewrite /D' in_set => /andP[a_C /eqP ->]; rewrite mul0r.
    by rewrite big1.
  by rewrite add0r lexx.
apply: log_sum1 => // a.
rewrite in_set => /andP[a_C fa_not_0].
by rewrite lt_neqAle eq_sym fa_not_0 f0.
Qed.
