(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix fingroup perm.
From mathcomp Require Import lra ring.
From mathcomp Require boolp.
From mathcomp Require Import mathcomp_extra Rstruct reals.
Require Import ssr_ext ssralg_ext realType_ext fdist convex.

(****************************************************************************)
(* Direct formalization of the Lemma 2 from M. H. Stone. Postulates for the *)
(* barycentric calculus. Ann. Mat. Pura Appl., 29(1):25–30, 1949. The file  *)
(* convex_choice.v contains a shorter proof.                                *)
(****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory Num.Theory Order.POrderTheory.

Local Open Scope fdist_scope.
Local Open Scope convex_scope.
Local Open Scope reals_ext_scope.

(* TODO: move? *)
Module S2.

Lemma generators (s : 'S_2) : s = 1%g \/ s = tperm ord0 (Ordinal (erefl (1 < 2))).
Proof.
pose s0 := s ord0. pose s1 := s (Ordinal (erefl (1 < 2))).
case/orP : (ord2 s0) => /eqP Hs0.
- case/orP : (ord2 s1) => [/eqP |/eqP ?].
  + by rewrite -Hs0 => /perm_inj /(congr1 val).
  + left; apply/permP => i.
    by case/orP: (ord2 i) => /eqP ->; rewrite perm1.
- case/orP : (ord2 s1) => [/eqP ? |/eqP].
  + right; apply/permP => i.
    by case/orP: (ord2 i) => /eqP ->; rewrite permE.
  + by rewrite -Hs0 => /perm_inj /(congr1 val).
Qed.

End S2.

(* TODO: move? *)
Module S3.

Definition p01 : 'S_3 := tperm ord0 (Ordinal (erefl (1 < 3))).
Definition p02 : 'S_3 := tperm ord0 (Ordinal (erefl (2 < 3))).
Definition p12 : 'S_3 := tperm (Ordinal (erefl (1 < 3))) (Ordinal (erefl (2 < 3))).
Definition p021 := (p01 * p02)%g.
Definition p012 := (p02 * p01)%g.

Lemma suff_generators (P : 'S_3 -> Prop) : P 1%g -> P p01 -> P p02 ->
  (forall s s', P s -> P s' -> P (s' * s)%g) -> forall s : 'S_3, P s.
Proof.
move=> H1 H2 H3 H s.
have : s = 1%g \/ s = S3.p01 \/ s = S3.p02 \/ s = S3.p12 \/ s = S3.p021 \/ s = S3.p012.
  pose s0 := s ord0. pose s1 := s (Ordinal (erefl (1 < 3))). pose s2 := s (Ordinal (erefl (2 < 3))).
  case/or3P : (ord3 s0) => [/eqP Hs0|/eqP Hs0|/eqP Hs0].
  - case/or3P : (ord3 s1) => [/eqP|/eqP Hs1|/eqP Hs1].
    + by rewrite -Hs0 => /perm_inj.
    + case/or3P : (ord3 s2) => [/eqP|/eqP Hs2|/eqP].
      * by rewrite -Hs0 => /perm_inj.
      * by move: Hs1; rewrite -Hs2 => /perm_inj.
      * left.
        apply/permP => /= i.
        case/or3P : (ord3 i) => /eqP ->; by rewrite permE //.
    + case/or3P : (ord3 s2) => [/eqP|/eqP Hs2|/eqP].
      * by rewrite -Hs0 => /perm_inj.
      * right; right; right; left.
        apply/permP => /= i.
        by case/or3P : (ord3 i) => /eqP ->; rewrite permE.
      * by rewrite -Hs1 => /perm_inj.
  - case/or3P : (ord3 s1) => [/eqP Hs1|/eqP|/eqP Hs1].
    + case/or3P : (ord3 s2) => [/eqP|/eqP|/eqP Hs2].
      * by rewrite -Hs1 => /perm_inj.
      * by rewrite -Hs0 => /perm_inj.
      * right; left.
        apply/permP => /= i.
        by case/or3P : (ord3 i) => /eqP ->; rewrite permE.
    + by rewrite -Hs0 => /perm_inj.
    + case/or3P : (ord3 s2) => [/eqP Hs2|/eqP|/eqP].
      * right; right; right; right; left.
        apply/permP => /= i.
        by case/or3P : (ord3 i) => /eqP ->; rewrite !permE //= !permE.
      * by rewrite -Hs0 => /perm_inj.
      * by rewrite -Hs1 => /perm_inj.
  - case/or3P : (ord3 s1) => [/eqP Hs1|/eqP Hs1|/eqP Hs1].
    + case/or3P : (ord3 s2) => [/eqP Hs2|/eqP Hs2|/eqP Hs2].
      * by move: Hs1; rewrite -Hs2 => /perm_inj.
      * right; right; right; right; right.
        apply/permP => /= i.
        by case/or3P : (ord3 i) => /eqP ->; rewrite !permE //= !permE.
      * by move: Hs0; rewrite -Hs2 => /perm_inj.
    + case/or3P : (ord3 s2) => [/eqP Hs2|/eqP Hs2|/eqP Hs2].
      * right; right; left.
        apply/permP => /= i.
        by case/or3P : (ord3 i) => /eqP ->; rewrite !permE //.
        by move: Hs1; rewrite -Hs2 => /perm_inj.
      * by move: Hs0; rewrite -Hs2 => /perm_inj.
      * by move: Hs0; rewrite -Hs1 => /perm_inj.
move=> -[-> // | [-> // | [-> // | ]]].
have K1 : P S3.p021 by rewrite (_ : S3.p021 = S3.p01 * S3.p02)%g //; exact/H.
have K2 : P S3.p12.
  rewrite -(_ : S3.p02 * S3.p021 = S3.p12)%g; first exact: H.
  apply/permP => i.
  case/or3P : (ord3 i) => /eqP ->; by repeat rewrite !permE /=.
have K3 : P S3.p012 by exact: H.
by move=> -[-> // | [-> // | -> //]].
Qed.

End S3.

(* TODO: move? *)
Module Sn.

Definition proj0 n (s : 'S_n.+2) (i : 'I_n.+1) : 'I_n.+1 :=
  inord (s (lift ord0 i)).-1.

Lemma proj0_inj n (s : 'S_n.+2) : s ord0 = ord0 -> injective (proj0 s).
Proof.
move=> s00 i j; rewrite /proj0 => ij.
suff : s (lift ord0 i) = s (lift ord0 j) by move/(@perm_inj _ s)/lift_inj.
apply val_inj => /=.
rewrite -[LHS]prednK ?lt0n; last first.
  suff : s (lift ord0 i) != ord0 by [].
  rewrite -[X in _ != X]s00.
  by apply/eqP => /(@perm_inj _ s).
rewrite -[RHS]prednK ?lt0n; last first.
  suff : s (lift ord0 j) != ord0 by [].
  rewrite -[X in _ != X]s00.
  by apply/eqP => /(@perm_inj _ s).
move/(congr1 val) : ij => /= ij.
rewrite inordK // in ij; last first.
  rewrite prednK ?lt0n; first by rewrite -ltnS.
  suff : s (lift ord0 i) != ord0 by [].
  rewrite -[X in _ != X]s00.
  by apply/eqP => /(@perm_inj _ s).
rewrite inordK // in ij; last first.
  rewrite prednK ?lt0n; first by rewrite -ltnS.
  suff : s (lift ord0 j) != ord0 by [].
  rewrite -[X in _ != X]s00.
  by apply/eqP => /(@perm_inj _ s).
by rewrite ij.
Qed.

Definition swap_asa n (s : 'S_n.+2) x (i : 'I_n.+1) : 'I_n.+1 :=
  if i.+1 == (s^-1 x)%g :> nat then inord (s x).-1 else inord (s (lift ord0 i)).-1.

Lemma swap_asa_inj n (s : 'S_n.+2) (K : s ord0 != ord0) : injective (swap_asa s ord0).
Proof.
move=> i j; rewrite /swap_asa.
case: ifPn => [/eqP Hi|Hi].
  case: ifPn => [/eqP Hj ?|Hj].
    move: Hi; rewrite -Hj => -[?]; exact/val_inj.
  move/(congr1 val) => /=.
  rewrite inordK //; last by rewrite prednK ?lt0n // -ltnS.
  rewrite inordK; last first.
    rewrite prednK ?lt0n; first by rewrite -ltnS.
    suff : s (lift ord0 j) != ord0 by [].
    by apply: contra Hj => /eqP <-; rewrite permK.
  move/(congr1 S).
  rewrite prednK ?lt0n // prednK ?lt0n; last first.
    apply: contra Hj => Hj.
    suff : s (lift ord0 j) = ord0 by move=> <-; rewrite permK.
    exact/eqP.
  move=> H.
  suff : s ord0 = s (lift ord0 j) by move/(@perm_inj _ s).
  exact/val_inj.
case: ifPn => Hj.
  move/(congr1 val) => /=.
  rewrite inordK; last first.
    rewrite prednK ?lt0n; first by rewrite -ltnS.
    apply: contra Hi => Hi.
    suff : s (lift ord0 i) == ord0 :> 'I_n.+2 by move=> /eqP <-; rewrite permK.
    by [].
  rewrite inordK; last by rewrite prednK ?lt0n // -ltnS.
  move/(congr1 S).
  rewrite prednK ?lt0n; last first.
    apply: contra Hi => Hi.
    suff : s (lift ord0 i) == ord0 :> 'I_n.+2 by move/eqP <-; rewrite permK.
    by [].
  rewrite prednK ?lt0n //.
  move=> Hs.
  have {Hs} : s (lift ord0 i) = s ord0 by apply/val_inj.
  by move/(@perm_inj _ s).
move/(congr1 val) => /=.
move/(congr1 S).
rewrite inordK; last first.
  rewrite prednK ?lt0n; first by rewrite -ltnS.
  apply: contra Hi => Hi.
  suff : s (lift ord0 i) == ord0 :> 'I_n.+2 by move/eqP => <-; rewrite permK.
  by [].
rewrite inordK; last first.
  rewrite prednK ?lt0n; first by rewrite -ltnS.
  apply: contra Hj => Hj.
  suff : s (lift ord0 j) == ord0 :> 'I_n.+2 by move/eqP => <-; rewrite permK.
  by [].
rewrite prednK ?lt0n //; last first.
  apply: contra Hi => Hi.
  suff : s (lift ord0 i) == ord0 :> 'I_n.+2 by move/eqP => <-; rewrite permK.
  by [].
rewrite prednK ?lt0n; last first.
  apply: contra Hj => Hj.
  suff : s (lift ord0 j) == ord0 :> 'I_n.+2 by move/eqP => <-; rewrite permK.
  by [].
move=> Hs.
have {Hs} : s (lift ord0 i) = s (lift ord0 j) by exact/val_inj.
by move /(@perm_inj _ s)/lift_inj.
Qed.

Lemma swap_asaE n (s : 'S_n.+2) (K : s ord0 != ord0) :
  s = (lift_perm ord0 ord0 (perm (swap_asa_inj K)) * tperm (ord0) (s ord0))%g.
Proof.
apply/permP => i.
rewrite [in RHS]permE /=.
have [->|i0] := eqVneq i ord0; first by rewrite lift_perm_id permE.
have Hi : i = lift ord0 (inord i.-1).
  apply/val_inj => /=.
  rewrite /bump leq0n /= add1n inordK.
    by rewrite prednK // lt0n.
  by rewrite -ltnS prednK // lt0n.
rewrite {2}Hi lift_perm_lift 2!permE /= /swap_asa.
case: ifPn => /=.
  case: ifPn => /=.
    rewrite inordK; last by rewrite -ltnS prednK // lt0n.
    rewrite prednK // ?lt0n //.
    move=> si _.
    apply: (@perm_inj _ s^-1%g).
    rewrite permK; exact/eqP.
  rewrite inordK; last by rewrite -ltnS prednK // lt0n.
  rewrite prednK // ?lt0n // => si.
  move/eqP.
  move/(congr1 (s^-1%g)).
  rewrite permK => si0.
  exfalso.
  move/eqP : i0; apply.
  rewrite -si0 /=.
  apply: (@perm_inj _ s).
  rewrite permKV /=.
  apply/val_inj => /=.
  rewrite /bump leq0n add1n.
  rewrite inordK; last first.
    rewrite -ltnS prednK // lt0n -Hi.
    apply: contra si => /eqP si0'.
    apply/eqP.
    suff : i = (s^-1)%g ord0 by move/(congr1 val).
    apply: (@perm_inj _ s).
    rewrite permKV.
    exact/val_inj.
  rewrite prednK //; last first.
    rewrite lt0n -Hi.
    apply: contra si => /eqP si0'.
    apply/eqP.
    suff : i = (s^-1)%g ord0 by move/(congr1 val).
    apply: (@perm_inj _ s).
    rewrite permKV.
    exact/val_inj.
  by rewrite -Hi.
case: ifPn.
  rewrite inordK; last by rewrite -ltnS prednK // lt0n.
 rewrite prednK ?lt0n // => si.
  move=> L.
  exfalso.
  move/eqP : L; apply.
  apply/val_inj => /=.
  rewrite /bump leq0n add1n inordK; last by rewrite -ltnS // prednK // lt0n.
  by rewrite prednK // lt0n.
move=> L1 L2.
apply/val_inj => /=.
rewrite /bump leq0n add1n inordK; last first.
  rewrite -ltnS prednK // lt0n.
  apply: contra L1.
  move/eqP => L1.
  apply/eqP.
  rewrite inordK; last by rewrite -ltnS prednK // lt0n.
  rewrite prednK // ?lt0n //.
  move: L1.
  rewrite (_ : lift _ _ = i); last first.
    apply/val_inj => /=.
    by rewrite /bump leq0n add1n inordK // ?prednK // ?lt0n // -ltnS.
  move=> si.
  have : s i = ord0 by apply/val_inj.
  move/(congr1 s^-1%g).
  by rewrite permK => ->.
rewrite prednK // ?lt0n; last first.
  apply: contra L1 => /eqP L1.
  have {}L1 : s (lift ord0 (inord i.-1)) = ord0 by exact/val_inj.
  rewrite -L1 permK.
  exact/eqP.
by rewrite -Hi.
Qed.

Lemma suff_generators0 n (P : 'S_n.+2 -> Prop) :
  (forall s s', P s -> P s' -> P (s' * s)%g) ->
  (forall s : 'S_n.+2, P (tperm ord0 (s ord0))) ->
  (forall s : 'S_n.+2, s ord0 = ord0 -> P s) ->
  forall s : 'S_n.+2, P s.
Proof.
move=> H0 H1 H2 s.
have [K|K] := eqVneq (s ord0) ord0; first exact: H2.
rewrite (swap_asaE K); apply H0; first exact/H1.
by apply H2; rewrite lift_perm_id.
Qed.

Lemma decomp_swap (n : nat) (s : 'S_n.+2) (K : s ord0 != ord0) :
  tperm ord0 (s ord0) =
  ((tperm (lift ord0 ord0) (s ord0)) *
   (tperm ord0 (lift ord0 ord0)) *
   (tperm (lift ord0 ord0) (s ord0)))%g :> 'S_n.+2.
Proof.
apply /permP => /= i.
have [->|Hi] := eqVneq i ord0;
 first by do ! rewrite permE /=;
          have -> : (if ord0 == s ord0 then lift ord0 ord0 else ord0) = ord0
            by move => n0; rewrite ifN_eqC //=.
do ! rewrite permE /=.
rewrite ifN_eq //.
have [->|Hi1] := eqVneq i (lift ord0 ord0).
- have [->|Hs] := eqVneq (s ord0) (lift ord0 ord0);
    first by
      by have -> : (if lift ord0 ord0 == ord0 then lift ord0 ord0 else ord0) = ord0.
  by rewrite (negbTE K) eqxx (negbTE Hs).
have [His|His] := eqVneq i (s ord0);
first by  have -> : (if lift ord0 ord0 == lift ord0 ord0 then ord0 else lift ord0 ord0) = ord0; [by move => *; rewrite eq_refl|rewrite ifN_eqC //|done].
have -> : (if i == ord0
   then lift ord0 ord0
   else if i == lift ord0 ord0 then ord0 else i) = i by rewrite !ifN_eq.
by rewrite !ifN_eq.
Qed.

Lemma suff_generators n (P : 'S_n.+2 -> Prop) :
  (forall s s', P s -> P s' -> P (s' * s)%g) ->
  P (tperm ord0 (lift ord0 ord0)) ->
  (forall s : 'S_n.+2, s ord0 = ord0 -> P s) ->
  forall s : 'S_n.+2, P s.
Proof.
move=> H0 H1 H2 s.
have [K|K] := eqVneq (s ord0) ord0; first exact: H2.
apply suff_generators0 => // s'.
have [->//|K'] := eqVneq (s' ord0) (lift ord0 ord0).
have [->|K''] := eqVneq (s' ord0) ord0; first by apply H2; rewrite permE.
rewrite decomp_swap //.
apply H0.
  by apply H2; rewrite permE /= eq_sym (negbTE K'').
apply H0; first exact: H1.
by apply H2; rewrite permE /= eq_sym (negbTE K'').
Qed.

End Sn.

Section convex_space_prop.
Context {R : realType}.
Variables A : convType R.
Implicit Types a b : A.
Lemma conv0 a b : a <| 0%:pr |> b = b.
Proof.
by rewrite convC (_ : _%:pr = 1%:pr) ?conv1 //=; apply val_inj; exact: onem0.
Qed.

Lemma convA0 (p q r s : {prob R}) a b c :
  Prob.p p = (Prob.p r * Prob.p s)%R :> R ->
  ((Prob.p s).~ = (Prob.p p).~ * (Prob.p q).~)%R ->
  a <| p |> (b <| q |> c) = (a <| r |> b) <| s |> c.
Proof.
move=> H1 H2.
have [r0|r0] := eqVneq r 0%:pr.
  rewrite r0 conv0 (_ : p = 0%:pr) ?conv0; last first.
    by apply/val_inj; rewrite /= H1 r0 mul0r.
  congr (_ <| _ |> _); move: H2; rewrite H1 r0 mul0r onem0 mul1r.
  move/(congr1 (@onem _)); rewrite !onemK => ?; exact/val_inj.
have [s0|s0] := eqVneq s 0%:pr.
  rewrite s0 conv0 (_ : p = 0%:pr) ?conv0; last first.
    by apply/val_inj; rewrite /= H1 s0 mulr0.
  rewrite (_ : q = 0%:pr) ?conv0 //.
  move: H1; rewrite s0 mulr0 => p0.
  move: H2; rewrite p0 onem0 mul1r => /(congr1 (@onem _)); rewrite !onemK => sq.
  by rewrite -s0; exact/val_inj.
rewrite convA; congr ((_ <| _ |> _) <| _ |> _).
  apply val_inj; rewrite /= s_of_pqE.
  move/(congr1 (@onem _)) : H2.
  by rewrite onemK => ->.
exact: (@r_of_pq_is_r _ _ _ _ s).
Qed.

Lemma convA' (r s : {prob R}) a b c : [p_of r, s] != 1%:pr ->
  a <| [p_of r, s] |> (b <| [q_of r, s] |> c) = (a <| r |> b) <| s |> c.
Proof.
move=> H; have [->|s0] := eqVneq s 0%:pr.
- by rewrite p_of_r0 conv0 q_of_r0 conv0 conv0.
- by rewrite convA s_of_pqK // r_of_pqK.
Qed.

Lemma convACA (x1 y1 x2 y2 : A) p q :
  (x1 <|q|> y1) <|p|> (x2 <|q|> y2) = (x1 <|p|> x2) <|q|> (y1 <|p|> y2).
Proof.
have [->|p0] := eqVneq p 0%:pr; first by rewrite !conv0.
have [->|q0] := eqVneq q 0%:pr; first by rewrite !conv0.
have [->|p1] := eqVneq p 1%:pr; first by rewrite !conv1.
have [->|q1] := eqVneq q 1%:pr; first by rewrite !conv1.
set r := [p_of q, p].
have r1 : (r != 1%:pr)%R.
  by rewrite p_of_neq1//; apply/andP; split; rewrite -?prob_gt0 -?prob_lt1.
rewrite -(convA' x1 y1) //.
rewrite (convC _ y1).
set s := [q_of q, p].
set t := (Prob.p (Prob.p s).~%:pr * Prob.p q)%:pr.
have t1 : (Prob.p t < 1)%R.
  rewrite -prob_lt1; apply/eqP => t1; subst t.
  have {q1} : (Prob.p q < 1)%R by rewrite -prob_lt1.
  move/(congr1 (@Prob.p _)) : t1 => /= <-.
  rewrite -ltr_pdivrMr; last by rewrite -prob_gt0.
  rewrite divff// /onem ltrBrDl Order.TotalTheory.ltNge => /negP; apply.
  by rewrite -{1}[in (1%R <= _)%R](add0r 1%R) lerD2r.
rewrite -(convA' x2); last by rewrite prob_lt1 p_of_rsC /= p_of_rsE.
rewrite -(convA' x1) //; last by rewrite p_of_rsC.
rewrite (convC _ y2 y1) /=.
congr (_ <| _ |> _); first by rewrite p_of_rsC.
congr (_ <| _ |> _).
  (* TODO: lemma? *)
  apply val_inj => /=.
  rewrite /s /onem /= !(p_of_rsE,q_of_rsE) /= !(p_of_rsE,q_of_rsE) /= /onem.
  field.
  rewrite subr_eq0 mulrC eq_sym.
  by rewrite -p_of_rsE.
congr (_ <| _ |> _).
apply val_inj => /=.
rewrite -[in RHS](onemK (Prob.p p)); congr onem.
rewrite q_of_rsE {1}p_of_rsE /= q_of_rsE p_of_rsE /= /onem.
field.
apply/andP; split.
  by rewrite subr_eq0 eq_sym -p_of_rsE.
rewrite mulrBl mul1r opprB addrA subrK mulrDr mulr1 mulrN opprB addrA subrK.
by rewrite subr_eq0 eq_sym.
Qed.

Lemma distribute (x y z : A) (p q : {prob R}) :
  x <| p |> (y <| q |> z) = (x <| p |> y) <| q |> (x <| p |> z).
Proof. by rewrite -{1}(convmm q x) convACA. Qed.

Lemma Convn_fdist1 (n : nat) (j : 'I_n) (g : 'I_n -> A): <|>_(fdist1 j) g = g j.
Proof.
elim: n j g => [[] [] //|n IH j g /=].
case: Bool.bool_dec => [/eqP|/Bool.eq_true_not_negb b01].
  rewrite fdist1E; case j0 : (_ == _) => /=.
    by move=> _; rewrite (eqP j0).
  by move/eqP; rewrite eq_sym oner_eq0.
rewrite (_ : probfdist _ _ = 0%:pr) ?conv0; last first.
  apply val_inj => /=; move: b01; rewrite !fdist1E => j0.
  by case j0' : (_ == _) => //; rewrite j0' eqxx in j0.
have j0 : ord0 != j by apply: contra b01 => /eqP <-; rewrite fdist1xx.
have j0' : 0 < j by rewrite lt0n; apply: contra j0 => /eqP j0; apply/eqP/val_inj.
move=> [:H]; have @j' : 'I_n.
  by apply: (@Ordinal _ j.-1 _); abstract: H; rewrite prednK // -ltnS.
rewrite (_ : fdist_del b01 = fdist1 j'); last first.
  apply/fdist_ext => /= k.
  rewrite fdist_delE fdistD1E /= !fdist1E /= (negbTE j0) subr0 divr1.
  congr (GRing.natmul _ (nat_of_bool _)).
  move Hk : (k == _) => [|].
  - apply/eqP/val_inj; rewrite /= /bump leq0n add1n.
    by move/eqP : Hk => -> /=; rewrite prednK // lt0n.
  - apply: contraFF Hk => /eqP.
    move/(congr1 val) => /=; rewrite /bump leq0n add1n => kj.
    by apply/eqP/val_inj; rewrite /= -kj.
rewrite IH /fdist_del_idx ltn0; congr g.
by apply val_inj; rewrite /= /bump leq0n add1n prednK // lt0n.
Qed.

Lemma convn1E a e : <|>_e (fun _ : 'I_1 => a) = a.
Proof.
rewrite /=; case: Bool.bool_dec => // /Bool.eq_true_not_negb H; exfalso; move/eqP: H; apply.
by apply/eqP; rewrite fdist1E1 (fdist1I1 e).
Qed.

Lemma convnE n (g : 'I_n.+1 -> A) (d : R.-fdist 'I_n.+1) (i1 : d ord0 != 1%R) :
  <|>_d g =
  g ord0 <| probfdist d ord0 |> <|>_(fdist_del i1) (fun x => g (fdist_del_idx ord0 x)).
Proof.
rewrite /=; case: Bool.bool_dec => /= [|/Bool.eq_true_not_negb] H.
exfalso; by rewrite (eqP H) eqxx in i1.
by rewrite (boolp.Prop_irrelevance H i1).
Qed.

Lemma convn2E (g : 'I_2 -> A) (d : R.-fdist 'I_2) :
  <|>_d g = g ord0 <| probfdist d ord0 |> g (Ordinal (erefl (1 < 2))).
Proof.
have [/eqP |i1] := eqVneq (d ord0) 1%R.
  rewrite fdist1E1 => /eqP ->; rewrite Convn_fdist1.
  rewrite (_ : probfdist _ _ = 1%:pr) ?conv1 //.
  by apply val_inj; rewrite /= fdist1xx.
rewrite convnE; congr (_ <| _ |> _).
rewrite (_ : (fun _ => _) = (fun=> g (fdist_del_idx ord0 ord0))); last first.
  by rewrite boolp.funeqE => x; rewrite (ord1 x).
by rewrite convn1E /fdist_del_idx ltnn; congr g; exact/val_inj.
Qed.

Open Scope ring_scope.

Lemma convn3E (g : 'I_3 -> A) (d : R.-fdist 'I_3) (p : {prob R}) :
  d ord0 != 1%R ->
  (d (lift ord0 ord0) / (1 - d ord0)) = Prob.p p ->
  <|>_d g = g ord0 <| probfdist d ord0 |> (g (Ordinal (erefl (1 < 3)%nat)) <| p |> g (Ordinal (erefl (2 < 3)%nat))).
Proof.
move=> i1 Hp.
have [p1|p1] := eqVneq p 1%:pr.
  rewrite convnE; congr (_ <| _ |> _).
  rewrite convn2E /fdist_del_idx ltnn /=; congr (g _ <| _ |> g _).
      apply val_inj => /=.
      by rewrite fdist_delE fdistD1E (eq_sym (lift _ _)) (negbTE (neq_lift _ _)).
    exact/val_inj.
  exact/val_inj.
rewrite convnE; congr (_ <| _ |> _).
rewrite convn2E /fdist_del_idx ltnn /=; congr (g _ <| _ |> g _).
- apply val_inj => /=.
  by rewrite fdist_delE fdistD1E (eq_sym (lift _ _)) (negbTE (neq_lift _ _)).
- exact/val_inj.
- exact/val_inj.
Qed.

Lemma convn_proj n (g : 'I_n -> A) (d : R.-fdist 'I_n) i :
  d i = 1 -> <|>_d g = g i.
Proof.
elim: n g d i => [d d0|n IH g d i di1]; first by move: (fdistI0_False d0).
have [i0|i0] := eqVneq i ord0.
  move/eqP : di1; rewrite i0 fdist1E1 => /eqP ->.
  by rewrite Convn_fdist1.
have d00 : d ord0 = 0 by move/eqP/fdist1P : di1 => -> //; rewrite eq_sym.
rewrite convnE; first by rewrite d00; apply/eqP; lra.
move=> d01.
rewrite (_ : probfdist _ _ = 0%:pr); last exact/val_inj.
rewrite conv0.
move=> [:Hj].
have @j : 'I_n.
  apply: (@Ordinal _ i.-1).
  abstract: Hj; by rewrite prednK // ?lt0n // -ltnS.
rewrite (IH _ _ j) // ?ltn0.
  congr g; apply val_inj => /=.
  by rewrite /bump leq0n add1n prednK // lt0n.
rewrite fdist_delE ltn0 fdistD1E eq_sym (negbTE (neq_lift _ _ )).
rewrite d00 subr0 divr1 -di1; congr (d _).
by apply val_inj; rewrite /= /bump leq0n add1n prednK // lt0n.
Qed.

(* goal: Conv_perm *)

Lemma Convn_perm_1 n (d : R.-fdist 'I_n) (g : 'I_n -> A) :
  <|>_d g = <|>_(fdistI_perm d 1%g) (g \o (1%g : 'S_n)).
Proof.
rewrite fdistI_perm1; congr (Convn _ d _).
by rewrite boolp.funeqE => i /=; rewrite perm1.
Qed.

Lemma Convn_permI1 (d : R.-fdist 'I_1) (g : 'I_1 -> A) (s : 'S_1) :
  <|>_d g = <|>_(fdistI_perm d s) (g \o s).
Proof.
have s1 : s = 1%g.
  apply/permP => i; by case: (s i) => -[|//] ?; rewrite perm1 (ord1 i); exact/val_inj.
by rewrite s1 -Convn_perm_1.
Qed.

Lemma Convn_permI2 (d : R.-fdist 'I_2) (g : 'I_2 -> A) (s : 'S_2) :
  <|>_d g = <|>_(fdistI_perm d s) (g \o s).
Proof.
have [->|Hs] := S2.generators s.
  rewrite fdistI_perm1; congr Convn.
  by rewrite boolp.funeqE => i; rewrite /= perm1.
move: (FDist.ge0 d ord0); rewrite le0r => /orP -[/eqP /esym d00|d00].
  have d11 : d (Ordinal (erefl (1 < 2)%nat)) = 1.
    rewrite -(FDist.f1 d) 2!big_ord_recl big_ord0 addr0 -d00 add0r; f_equal; exact/val_inj.
  have H1 : d = fdist1 (Ordinal (erefl (1 < 2)%nat)).
    rewrite -fdistI20; apply/fdist_ext => /= i.
    rewrite fdistI2E; case: ifPn => [/eqP ->//|/= i0].
    rewrite onem0 -(FDist.f1 d) 2!big_ord_recl big_ord0 addr0 -d00 add0r; congr (d _).
    by case: i i0 => -[//|] -[|//] //= i12 _; exact/val_inj.
  rewrite {1}H1 Convn_fdist1 {1}Hs.
  have H2 : fdistI_perm d (tperm ord0 (Ordinal (erefl (1 < 2)%nat))) = fdist1 ord0.
    apply/fdist_ext => /= i; rewrite fdistI_permE fdist1E.
    have [->|i0] := eqVneq i ord0; first by rewrite permE /= d11.
    rewrite permE /= (negbTE i0).
    by case: ifPn => //; case: i i0 => -[|[|]].
  by rewrite H2 Convn_fdist1 /=; congr g; rewrite Hs permE /=.
have [d10|d10] := eqVneq (d (lift ord0 ord0)) 0.
  have d01 : d ord0 = 1.
    rewrite -(FDist.f1 d) !big_ord_recl big_ord0 addr0.
    by rewrite addrC d10 add0r.
  have -> : d = fdist1 ord0 by apply/eqP; rewrite -fdist1E1; exact/eqP.
  by rewrite Convn_fdist1 {1}Hs fdistI_tperm Convn_fdist1 /= Hs permE.
rewrite convn2E.
rewrite convn2E.
rewrite /= Hs permE /= convC !permE /=; congr (_ <| _ |> _); apply val_inj => /=.
rewrite fdistI_permE permE /= /onem -(FDist.f1 d) !big_ord_recl big_ord0.
by rewrite addr0 (addrC (d ord0)) addrK; congr (d _); exact/val_inj.
Qed.

Lemma Convn_permI3_p01 (d : R.-fdist 'I_3) (g : 'I_3 -> A) :
  <|>_d g = <|>_(fdistI_perm d S3.p01) (g \o S3.p01).
Proof.
have : (d ord0 + d (lift ord0 ord0) = 0 \/ d (lift ord0 ord0) + d ord_max = 0 \/
  (0 < d ord0 + d (lift ord0 ord0) /\ 0 < d (lift ord0 ord0) + d ord_max)).
  have : (0 <= d ord0 + d (lift ord0 ord0)) by apply addr_ge0.
  have : (0 <= d (lift ord0 ord0) + d ord_max) by apply addr_ge0.
  rewrite le0r => /orP -[/eqP|H]; first by auto.
  rewrite le0r => /orP -[/eqP|H']; first by auto.
  right; right; by auto.
move=> [ H | [ H | [H1 H2] ] ].
  have /eqP d1 : d ord_max = 1.
    rewrite -(FDist.f1 d) !big_ord_recl big_ord0 addr0 addrA H add0r.
    by congr (d _); exact/val_inj.
  rewrite fdist1E1 in d1.
  rewrite {1}(eqP d1) Convn_fdist1.
  by rewrite (eqP d1) fdistI_perm_fdist1 Convn_fdist1 /= permKV.
  have /eqP : d ord0 = 1.
    rewrite -(FDist.f1 d) !big_ord_recl big_ord0 addr0.
    rewrite (_ : lift ord0 (lift _ _) = ord_max); last exact/val_inj.
    by rewrite H addr0.
  rewrite fdist1E1 => /eqP ->.
  by rewrite Convn_fdist1 fdistI_perm_fdist1 Convn_fdist1 /= permKV.
have d01 : d ord0 <> 1.
  move=> /eqP d01.
  move: H2.
  move/fdist1P : (d01) => -> //.
  move/fdist1P : d01 => -> //.
  by rewrite add0r ltxx.
move=> [:Hp].
have @p : {prob R}.
  apply: (@Prob.mk_ _ (d (lift ord0 ord0) / (1 - d ord0))).
  abstract: Hp.
  apply/andP; split.
    by rewrite divr_ge0 // subr_ge0.
  rewrite ler_pdivrMr ?mul1r ?subr_gt0 -?fdist_lt1; last exact/eqP.
  rewrite lerBrDr -(FDist.f1 d) !big_ord_recl big_ord0 addr0.
  by rewrite addrC lerD2l addrC -lerBlDr subrr.
have [|p1] := eqVneq p 1%:pr.
  move/(congr1 (@Prob.p _)); rewrite [in X in X -> _]/=.
  move/divr1_eq => H.
  rewrite (@convn3E _ _ 1%:pr) ?conv1; last 2 first.
      exact/eqP.
    by rewrite H divrr // unitfE subr_eq0 eq_sym; exact/eqP.
  have [d00|d00] := eqVneq (d ord0) 0.
    rewrite (_ : probfdist _ _ = 0%:pr) ?conv0; last exact: val_inj.
    move: H; rewrite d00 subr0 => /eqP; rewrite fdist1E1 => /eqP ->.
    by rewrite fdistI_perm_fdist1 Convn_fdist1 /= permKV; congr g; exact/val_inj.
  rewrite (@convn3E _ _ 1%:pr) ?conv1; last first.
    rewrite !fdistI_permE /S3.p01 /= !permE /=.
    rewrite (_ : Ordinal _ = lift ord0 ord0); last exact/val_inj.
    by rewrite H opprB addrC subrK divff//.
  rewrite /S3.p01 /= fdistI_permE permE /=.
  rewrite (_ : Ordinal _ = lift ord0 ord0); last exact/val_inj.
  apply: contra d00 => /eqP d001.
  move: H; rewrite d001 => /eqP.
  by rewrite addrC -subr_eq subrr -eqr_oppLR oppr0 eq_sym.
  rewrite /= /S3.p01 !permE /= convC.
  congr (g _ <| _ |> g _).
  apply/val_inj; rewrite /= fdistI_permE permE /=.
  by rewrite (_ : Ordinal _ = lift ord0 ord0) ?H //; exact/val_inj.
rewrite (@convn3E _ _ p) //; last exact/eqP.
rewrite convA.
rewrite (convC _ (g ord0)).
have oned0 :  1 - d ord0 != 0 by rewrite subr_eq0; exact/eqP/nesym.
have H : Prob.p [p_of (Prob.p [r_of probfdist d ord0, p]).~%:pr, [s_of probfdist d ord0, p]] != Prob.p 1%:pr :> R.
  apply: p_of_neq1.
  rewrite s_of_pqE /=.
  rewrite (onemM (d ord0).~).
  rewrite !onemK.
  rewrite -addrA -opprB.
  rewrite -[X in (_ < _ - (_ - X) < _)%R]mul1r.
  rewrite -mulrBl -mulNr opprB mulrCA mulfV // mulr1.
  apply/andP; split => //.
  rewrite lt_neqAle; apply/andP; split.
    apply: contra p1 => p1.
    apply/eqP/val_inj => /=.
    move: p1; rewrite eq_sym addrC.
    rewrite -subr_eq => /eqP H; rewrite H divff//.
    by rewrite -H.
  by rewrite -(FDist.f1 d) !big_ord_recl /= big_ord0 addr0 addrA lerDl.
rewrite -convA'; last by [].
have [/eqP ds01|ds01] := eqVneq (d (S3.p01 ord0)) 1.
  move: (ds01); rewrite /S3.p01 permE => d01'.
  rewrite /= in d01'.
  rewrite (_ : Ordinal _ = lift ord0 ord0) in d01'; last exact/val_inj.
  rewrite fdist1E1 in d01'.
  rewrite fdist1E1 in ds01.
  rewrite [in RHS](eqP ds01) fdistI_perm_fdist1 Convn_fdist1 /= permKV.
  rewrite (_ : [p_of _, _] = 1%:pr); last first.
    apply/val_inj => /=.
    rewrite p_of_rsE /= r_of_pqE /= s_of_pqE /= (eqP d01').
    by rewrite fdist10// mul0r onem0 !mul1r subr0 fdist1xx onemK divr1.
  rewrite conv1 /S3.p01 permE /= (_ : Ordinal _ = lift ord0 ord0) //.
  exact/val_inj.
move=> [:Hq].
have @q : {prob R}.
  apply: (@Prob.mk_ _
    ((fdistI_perm d S3.p01) (lift ord0 ord0) / (1 - (fdistI_perm d S3.p01) ord0))).
  abstract: Hq.
  rewrite !fdistI_permE.
  apply/andP. split.
    by apply/divr_ge0 => //; rewrite subr_ge0; apply ltW; rewrite -fdist_lt1.
  rewrite ler_pdivrMr ?mul1r; last by rewrite subr_gt0 -fdist_lt1.
  rewrite lerBrDr -(FDist.f1 (fdistI_perm d S3.p01)) !big_ord_recl big_ord0.
  by rewrite addr0 !fdistI_permE addrCA addrA -[X in (X <= _)]addr0 lerD2l.
rewrite (@convn3E _ _ q) //; last by rewrite fdistI_permE.
congr (_ <| _ |> _).
- apply/val_inj => /=.
  rewrite fdistI_permE permE /= p_of_rsE /= r_of_pqE /=.
  rewrite s_of_pqE /= /onem.
  rewrite (_ : Ordinal _ = lift ord0 ord0); last exact/val_inj.
  set tmp1 := d _.
  set tmp2 := d _.
  field.
  rewrite oned0/= opprB opprB addrC addrA subrK.
  by rewrite gt_eqF// addrC.
- by rewrite /= /S3.p01 permE /=; congr g; exact/val_inj.
- congr (_ <| _ |> _).
  + apply val_inj => /=.
    rewrite q_of_rsE /= !fdistI_permE p_of_rsE /= r_of_pqE /= s_of_pqE.
    rewrite /= /onem !permE /=.
    rewrite (_ : Ordinal _ = lift ord0 ord0); last exact/val_inj.
    set tmp1 := d _.
    set tmp2 := d _.
    field.
    apply/andP; split.
      rewrite subr_eq0 eq_sym.
      apply: contra ds01.
      rewrite /S3.p01 permE /= (_ : Ordinal _ = lift ord0 ord0) //; exact/val_inj.
      by rewrite oned0/= !opprB addrC addrA subrK gt_eqF// addrC.
  + by congr g; apply val_inj => /=; rewrite /S3.p01 permE.
  + by rewrite /= /S3.p01 permE.
Qed.

Lemma Convn_permI3_p02 (d : R.-fdist 'I_3) (g : 'I_3 -> A) :
  <|>_d g = <|>_(fdistI_perm d S3.p02) (g \o S3.p02).
Proof.
(* TODO(rei): redundant part with Convn_perm3_p02 *)
have : (d ord0 + d (lift ord0 ord0) = 0 \/ d (lift ord0 ord0) + d ord_max = 0 \/
  (0 < d ord0 + d (lift ord0 ord0) /\ 0 < d (lift ord0 ord0) + d ord_max)).
  have : (0 <= d ord0 + d (lift ord0 ord0)) by apply addr_ge0.
  have : (0 <= d (lift ord0 ord0) + d ord_max) by apply addr_ge0.
  rewrite le_eqVlt => /orP -[|H]; first by move/eqP; auto.
  rewrite le_eqVlt => /orP -[|H']; first by move/eqP; auto.
  right; right; by auto.
move=> [ H | [ H | [H1 H2] ] ].
  have /eqP d1 : d ord_max = 1.
    rewrite -(FDist.f1 d) !big_ord_recl big_ord0 addr0 addrA H add0r; congr (d _); exact/val_inj.
  rewrite fdist1E1 in d1.
  rewrite {1}(eqP d1) Convn_fdist1.
  by rewrite (eqP d1) fdistI_perm_fdist1 Convn_fdist1 /= permKV.
  have /eqP d1 : d ord0 = 1.
    rewrite -(FDist.f1 d) !big_ord_recl big_ord0 addr0 addrC. apply/eqP. rewrite -subr_eq subrr.
    rewrite (_ : lift ord0 (lift _ _) = ord_max) ?H //; exact/val_inj.
  rewrite fdist1E1 in d1.
  by rewrite (eqP d1) Convn_fdist1 fdistI_perm_fdist1 Convn_fdist1 /= permKV.
have d01 : d ord0 <> 1%R.
  move=> /eqP d01.
  move: H2.
  move/fdist1P : (d01) => -> //.
  move/fdist1P : d01 => -> //.
  by rewrite add0r ltxx.
move=> [:Hp].
have @p : {prob R}.
  apply: (@Prob.mk_ _ (d (lift ord0 ord0) / (1 - d ord0))).
  abstract: Hp.
  apply/andP. split;
    first by apply/divr_ge0/ltW => //; rewrite subr_gt0 -fdist_lt1; exact/eqP.
  rewrite ler_pdivrMr; last by rewrite subr_gt0 -fdist_lt1; exact/eqP.
  rewrite mul1r.
  rewrite lerBrDr -(FDist.f1 d) !big_ord_recl big_ord0 addr0.
  by rewrite addrC lerD2l addrC -lerBlDr subrr.
rewrite (@convn3E _ _ p) //; last exact/eqP.
rewrite convC.
rewrite (convC _ _ (g (Ordinal (erefl (2 < 3)%nat)))).
have [/eqP dmax1|dmax1] := eqVneq (d ord_max) 1%R.
  move/fdist1P in dmax1.
  by move: H1; rewrite dmax1 // dmax1 // addr0 ltxx.
have [d00|d00] := eqVneq (d ord0) 0.
  rewrite (_ : (Prob.p (probfdist d ord0)).~%:pr = 1%:pr) ?conv1; last first.
    by apply/val_inj; rewrite /= d00 onem0.
  rewrite (@convn3E _ _ 1%:pr); last 2 first.
    rewrite fdistI_permE /= !permE /=.
    rewrite (_ : Ordinal _ = ord_max) //; exact/val_inj.
    rewrite !fdistI_permE /S3.p02 !permE /=.
    rewrite (_ : Ordinal _ = ord_max) //; last exact/val_inj.
    rewrite -[in LHS](FDist.f1 d) !big_ord_recl big_ord0 addr0 d00 add0r.
    rewrite (_ : lift _ (lift _ _) = ord_max); last exact/val_inj.
    rewrite addrK divff //.
    apply/eqP => d10.
    by move: H1; rewrite d00 d10 addr0 ltxx.
  rewrite /= /S3.p02 !permE /= conv1.
  congr (g _ <| _ |> _).
  apply/val_inj => /=.
  rewrite fdistI_permE permE /=.
  rewrite (_ : Ordinal _ = ord_max) //; last exact/val_inj.
  rewrite d00 subr0 divr1 /onem -(FDist.f1 d) /= !big_ord_recl big_ord0 addr0.
  rewrite d00 add0r [X in X - _]addrC addrK; congr (d _); exact/val_inj.
have H : [p_of (Prob.p p).~%:pr, (Prob.p (probfdist d ord0)).~%:pr] != 1%:pr.
  apply: p_of_neq1 => /=; apply/andP; split.
    by apply/onem_gt0; rewrite -fdist_lt1; exact/eqP.
  by rewrite ltrBlDr ltrDl -fdist_gt0.
rewrite -convA'; last by [].
move=> [:Hq].
have @q : {prob R}.
  apply: (@Prob.mk_ _ ((fdistI_perm d S3.p02) (lift ord0 ord0)
                     / (1 - (fdistI_perm d S3.p02) ord0))).
  abstract: Hq.
  rewrite !fdistI_permE !permE /= (_ : Ordinal _ = ord_max); last exact/val_inj.
  apply/andP. split.
    apply/divr_ge0 => //; first by apply/ltW; rewrite subr_gt0 -fdist_lt1.
  rewrite ler_pdivrMr ?mul1r; last by rewrite subr_gt0 -fdist_lt1 //.
  rewrite lerBrDr -(FDist.f1 d) !big_ord_recl big_ord0 addr0.
  by rewrite (_ : lift _ (lift _ _) = ord_max) ?lerDr //; exact/val_inj.
rewrite (@convn3E _ _ q) //; last first.
  rewrite fdistI_permE permE /= (_ : Ordinal _ = ord_max) //; exact/val_inj.
rewrite /= !permE /=.
have ? : 1 - d ord0 != 0; first by rewrite subr_eq0 eq_sym; exact/eqP.
congr (g _ <| _ |> (_ <| _ |> _)).
  apply val_inj => /=.
  rewrite !fdistI_permE p_of_rsE /= permE /=.
  rewrite (_ : Ordinal _ = ord_max); last exact/val_inj.
  rewrite {1}/onem.
  rewrite mulrBl mul1r -mulrA mulVf ?mulr1//.
  rewrite /onem -addrA -opprB opprK; apply/eqP; rewrite subr_eq; apply/eqP.
  rewrite  -(FDist.f1 d) !big_ord_recl big_ord0 addr0.
  rewrite (_ : lift _ (lift _ _) = ord_max); last exact/val_inj.
  by rewrite addrA addrC addrA addrAC addrA.
apply val_inj => /=.
rewrite !fdistI_permE !permE /= q_of_rsE /= p_of_rsE /=.
rewrite (_ : Ordinal _ = ord_max); last exact/val_inj.
rewrite onemK.
rewrite -2!mulrA.
congr (_ * _)%R.
rewrite mulrA mulVf//.
rewrite mul1r.
congr (_^-1)%R.
rewrite (onemM _ (d ord0).~) !onemK.
rewrite (addrC _ (d ord0)).
rewrite -{1}(mulr1 (d (lift ord0 ord0) / _))%R.
rewrite -addrA.
rewrite -mulrBr.
rewrite -mulrA.
rewrite mulVf ?mulr1//.
apply/esym/eqP; rewrite subr_eq -(FDist.f1 d) !big_ord_recl big_ord0 addr0.
rewrite (_ : lift _ (lift _ _) = ord_max); last exact/val_inj.
by rewrite addrA.
Qed.

Lemma Convn_permI3 (d : R.-fdist 'I_3) (g : 'I_3 -> A) (s : 'S_3) :
  <|>_d g = <|>_(fdistI_perm d s) (g \o s).
Proof.
move: s d g.
apply: S3.suff_generators; last first.
  move=> s s' Hs Hs' d g.
  rewrite Hs Hs' fdistI_permM; congr (Convn _ _).
  by rewrite boolp.funeqE => i /=; rewrite permE.
exact: Convn_permI3_p02.
exact: Convn_permI3_p01.
exact: Convn_perm_1.
Qed.

Lemma Convn_perm_projection n (d : R.-fdist 'I_n.+2)
  (g : 'I_n.+2 -> A) (s : 'S_n.+2) (H : s ord0 = ord0) (dmax1 : d ord0 != 1%R)
  (m : nat) (nm : (n.+1 < m)%nat) (IH : forall n : nat, (n < m)%nat -> forall (d : R.-fdist 'I_n) (g : 'I_n -> A) (s : 'S_n),
    <|>_d g = <|>_(fdistI_perm d s) (g \o s)) :
  <|>_d g = <|>_(fdistI_perm d s) (g \o s).
Proof.
transitivity (g ord0 <| probfdist d ord0 |> (<|>_(fdist_del dmax1) (fun x => g (fdist_del_idx ord0 x)))).
  by rewrite convnE.
set s' : 'S_n.+1 := perm (Sn.proj0_inj H).
transitivity (g ord0 <| probfdist d ord0 |> (<|>_(fdistI_perm (fdist_del dmax1) s') ((fun x => g (fdist_del_idx ord0 x)) \o s'))).
  by rewrite -IH.
transitivity (g (s ord0) <| probfdist d ord0 |> (<|>_(fdistI_perm (fdist_del dmax1) s') ((fun x => g (fdist_del_idx ord0 x)) \o s'))).
  by rewrite H.
rewrite [in RHS]convnE //.
  by rewrite fdistI_permE H.
move=> K.
congr (_ <| _ |> _).
  apply val_inj => /=; by rewrite fdistI_permE H.
congr (Convn _ _).
  apply/fdist_ext => /= j.
  rewrite !fdistI_permE !fdist_delE !fdistD1E !fdistI_permE.
  rewrite /s' /=.
  rewrite permE.
  rewrite /f /=.
  rewrite H; congr (_ / _).
  congr (d _).
  apply val_inj => /=.
  rewrite /bump leq0n add1n /=.
  rewrite inordK //; last first.
    rewrite prednK //.
      by rewrite -ltnS.
    rewrite lt0n.
    suff : s (lift ord0 j) != ord0 by [].
    rewrite -[in X in _ != X]H.
    by apply/eqP => /(@perm_inj _ s).
  rewrite prednK // lt0n.
  suff : s (lift ord0 j) != ord0 by [].
  rewrite -[in X in _ != X]H.
  by apply/eqP => /(@perm_inj _ s).
rewrite boolp.funeqE => j /=.
rewrite /fdist_del_idx /= /s' permE /f /=.
congr g.
apply val_inj => /=.
rewrite /bump leq0n add1n /=.
rewrite inordK //; last first.
  rewrite prednK //.
    by rewrite -ltnS.
  rewrite lt0n.
  suff : s (lift ord0 j) != ord0 by [].
  rewrite -[X in _ != X]H.
  by apply/eqP => /(@perm_inj _ s).
rewrite prednK // lt0n.
suff : s (lift ord0 j) != ord0 by [].
rewrite -[X in _ != X]H.
by apply/eqP => /(@perm_inj _ s).
Qed.

Lemma Convn_perm_tperm (n : nat) (d : R.-fdist 'I_n.+3)
  (g : 'I_n.+3 -> A) (s : 'S_n.+3) (H : s = tperm ord0 (lift ord0 ord0)) (dmax1 : d ord0 != 1%R)
  (m : nat) (nm : (n.+3 < m.+1)%nat) (IH : forall n : nat, (n < m)%nat ->
       forall (d : R.-fdist 'I_n) (g : 'I_n -> A) (s : 'S_n),
       <|>_d g = <|>_(fdistI_perm d s) (g \o s)) :
  <|>_d g = <|>_(fdistI_perm d s) (g \o s).
Proof.
have [K|K] := eqVneq (d (lift ord0 ord0)) (1 - d ord0).
  case/boolP : (d (lift ord0 ord0) == 1%R :> R) => [|d11].
    by rewrite fdist1E1 => /eqP ->; rewrite fdistI_perm_fdist1 !Convn_fdist1 /= permKV.
  rewrite convnE.
  rewrite [in RHS]convnE.
    by rewrite fdistI_permE H permE.
  move=> K'.
  rewrite (_ : <|>_ _ _ = g (lift ord0 ord0)); last first.
    have /eqP : (fdist_del dmax1) ord0 = 1%R.
      by rewrite fdist_delE fdistD1E /= K divrr // unitfE subr_eq0 eq_sym.
    rewrite fdist1E1 => /eqP ->.
    by rewrite Convn_fdist1.
  rewrite (_ : <|>_ _ _ = g ord0); last first.
    have /eqP : (fdist_del K') ord0 = 1%R.
      rewrite fdist_delE fdistD1E /= !fdistI_permE H !permE /=.
      rewrite K opprB (addrC (d _) (-1)) addrA subrr add0r divrr // unitfE.
      apply /eqP => d00.
      by move: K; rewrite d00 subr0; apply/eqP.
    by rewrite fdist1E1 => /eqP ->; rewrite Convn_fdist1 /= H !permE /=.
  rewrite convC /= H permE /=; congr (_ <| _ |> _).
  by apply val_inj => /=; rewrite fdistI_permE /= permE /= K.
have [/eqP |K1] := eqVneq (d (lift ord0 ord0)) 1%R.
  by rewrite fdist1E1 => /eqP ->; rewrite fdistI_perm_fdist1 !Convn_fdist1 /= permKV.
(* TODO: isolate this construction? *)
pose D' : {ffun 'I_3 -> R} := [ffun x => [eta (fun=>0) with
  ord0 |-> d ord0,
  lift ord0 ord0 |-> d (lift ord0 ord0),
  ord_max |-> (\sum_(i < n.+3 | (2 <= i)%nat) d i)%R] x].
have D'0 : (forall i, 0 <= D' i).
  move=> i; rewrite /D' ffunE /=; case: ifPn => _ //.
  by case: ifPn => _ //; case: ifPn => _; [exact: sumr_ge0 | exact/lexx].
have D'1 : (\sum_(i < 3) (D' i) = 1).
  rewrite !big_ord_recr big_ord0 /= add0r.
  rewrite /D' !ffunE /= -(FDist.f1 d).
  apply/esym.
  rewrite 2!big_ord_recl addrA; congr (_ + _)%R.
  apply/esym.
  set h : 'I_n.+1 -> 'I_n.+3 := fun i => lift ord0 (lift ord0 i).
  set h' : 'I_n.+3 -> 'I_n.+1 := fun i => inord (i.-2).
  rewrite (reindex_onto h h'); last first.
    move=> j /= j1.
    rewrite /h /h'.
    apply val_inj => /=.
    rewrite /bump /bump !leq0n !add1n inordK //; last first.
      rewrite prednK; last by rewrite -subn1 subn_gt0.
      by rewrite -subn1 leq_subLR add1n -ltnS.
    rewrite prednK; last by rewrite -subn1 subn_gt0.
    by rewrite prednK // (leq_trans _ j1).
  apply eq_big => //= i.
  rewrite /h' /h.
  by apply/eqP/val_inj => /=; rewrite inordK.
set D := FDist.make D'0 D'1.
have H1 : (fdist_del dmax1) ord0 != 1%R.
  rewrite fdist_delE fdistD1E (eq_sym (lift _ _)) (negbTE (neq_lift _ _)).
  apply/eqP.
  move/divr1_eq. exact/eqP.
pose G : 'I_3 -> A := [eta (fun=>g ord0) with
  ord0 |-> g ord0,
  lift ord0 ord0 |-> g (lift ord0 ord0),
  ord_max |-> <|>_(fdist_del H1) (fun i : 'I_n.+1 => g (lift ord0 (lift ord0 i)))].
transitivity (Convn conv D G).
  erewrite convn3E.
  rewrite convnE.
  congr (_ <| _ |> _).
  by apply/val_inj => /=; rewrite ffunE.
  rewrite convnE.
  rewrite /G.
  congr (_ <| _ |> _).
  by rewrite ffunE.
  by rewrite /= !ffunE fdist_delE fdistD1E.
rewrite (Convn_permI3 _ _ S3.p01).
pose q' := (d ord0 / (1 - d (lift ord0 ord0))).
move=> [:Hq].
have @q : {prob R}.
  apply: (@Prob.mk_ _ q').
  abstract: Hq.
  apply/andP. split.
    by apply/divr_ge0/ltW => //; rewrite subr_gt0 -fdist_lt1.
  rewrite ler_pdivrMr.
    rewrite mul1r.
    rewrite lerBrDr -(FDist.f1 d).
    rewrite 2!big_ord_recl addrA lerDl.
    by apply: sumr_ge0 => i _.
  by rewrite subr_gt0 -fdist_lt1.
rewrite (@convn3E _ _ q); last 2 first.
  rewrite fdistI_permE permE /= (_ : Ordinal _ = lift ord0 ord0); last exact/val_inj.
  by rewrite /D' ffunE /=.
  rewrite /= !fdistI_permE /= !permE /= (_ : Ordinal _ = lift ord0 ord0); last exact/val_inj.
  by rewrite !ffunE.
rewrite convnE.
  by rewrite fdistI_permE H !permE.
move=> K2.
congr (_ <| _ |> _).
  apply val_inj => /=.
  rewrite !fdistI_permE !permE /= (_ : Ordinal _ = lift ord0 ord0); last exact/val_inj.
  by rewrite ffunE H !permE.
by rewrite /= /G /= permE /= H permE /=.
rewrite convnE.
  rewrite fdist_delE fdistD1E !fdistI_permE H !permE /=.
  apply/eqP.
  move/divr1_eq.
  by move/eqP; rewrite eq_sym subr_eq addrC -subr_eq; apply/negP; rewrite eq_sym.
move=> K3.
congr (_ <| _ |> _).
  apply val_inj => /=.
  by rewrite !fdist_delE !fdistD1E /= !fdistI_permE H !permE.
by rewrite /= /G /= !permE /= /fdist_del_idx ltnn H permE /=.
pose s' : 'S_n.+1 := 1%g.
rewrite (@IH _ _ _ _ s') //; last by rewrite -ltnS ltnW.
transitivity (<|>_(fdist_del H1) (fun i : 'I_n.+1 => g (lift ord0 (lift ord0 i)))).
  by rewrite /G [in LHS]/= !permE [in LHS]/=.
congr (Convn _ _).
  apply/fdist_ext => j.
  rewrite !(fdist_delE,fdistI_permE,fdistD1E).
  rewrite H !permE /=.
  (* TODO: using field *)
  rewrite -!mulrA. congr (_ * _).
  have d0_1 : 1 - d ord0 != 0; first by rewrite subr_eq0 eq_sym.
  rewrite -[I in I - _ / _](mulfV d0_1).
  rewrite -mulrBl invf_div mulrA mulVf //.
  have dl0_1 : 1 - d (lift ord0 ord0) != 0; first by rewrite subr_eq0 eq_sym.
  rewrite -[I in I - _ / _](mulfV dl0_1) -mulrBl invf_div mulrA mulVf //.
  by rewrite addrAC.
by rewrite boolp.funeqE => j; rewrite /= permE H permE.
Qed.

Lemma Convn_perm (n : nat) (d : R.-fdist 'I_n) (g : 'I_n -> A) (s : 'S_n) :
  <|>_d g = <|>_(fdistI_perm d s) (g \o s).
Proof.
move: d g s.
elim: n.+1 {-2}n (ltnSn n) => {n} // m IH n nm d g s.
destruct n as [|n]; first by move: (fdistI0_False d).
destruct n as [|n]; first exact: Convn_permI1.
destruct n as [|n]; first exact: Convn_permI2.
destruct n as [|n]; first exact: Convn_permI3.
move: m IH nm d g.
apply (@Sn.suff_generators _ (fun s => forall m : nat,
  (forall n0, (n0 < m)%nat ->
   forall (d : R.-fdist 'I_n0) (g : 'I_n0 -> A) (s0 : 'S_n0),
   <|>_d g = <|>_(fdistI_perm d s0) (g \o s0)) ->
  (n.+4 < m.+1)%nat ->
  forall (d : R.-fdist 'I_n.+4) (g : 'I_n.+4 -> A),
  <|>_d g = <|>_(fdistI_perm d s) (g \o s))).
- move=> s1 s2 H1 H2 m IH nm d g.
  rewrite (H1 m) // (H2 m) // fdistI_permM; congr (Convn _ _).
  by rewrite boolp.funeqE => i; rewrite /= permM.
- move=> m IH nm d g.
  have [/eqP|dmax1] := eqVneq (d ord0) 1.
    rewrite fdist1E1 => /eqP ->.
    by rewrite Convn_fdist1 fdistI_perm_fdist1 Convn_fdist1 /= permKV.
  by apply Convn_perm_tperm with m.
- move=> {}s H.
  move=> m IH nm d g.
  have [/eqP|dmax1] := eqVneq (d ord0) 1.
    rewrite fdist1E1 => /eqP ->.
    by rewrite Convn_fdist1 fdistI_perm_fdist1 Convn_fdist1 /= permKV.
  by apply Convn_perm_projection with m.
Qed.

End convex_space_prop.

Section affine_function_prop0.
Context {R : realType}.
Lemma affine_function_Sum (A B : convType R) (f : {affine A -> B}) (n : nat)
    (g : 'I_n -> A) (e : R.-fdist 'I_n) :
  f (<|>_e g) = <|>_e (f \o g).
Proof.
elim: n g e => [g e|n IH g e]; first by move: (fdistI0_False e).
have [/eqP|e10] := eqVneq (e ord0) 1%R.
  by rewrite fdist1E1 => /eqP ->; rewrite 2!Convn_fdist1.
by rewrite 2!convnE affine_conv IH.
Qed.
End affine_function_prop0.

Section convn_convnfdist.
Variable A : finType.

Lemma convn_convnfdist n (g : 'I_n -> {fdist A}) (d : {fdist 'I_n}) :
  <|>_d g = fdist_convn d g.
Proof.
elim: n g d => /= [g d|n IH g d]; first by move: (fdistI0_False d).
case: Bool.bool_dec => [/eqP|/Bool.eq_true_not_negb] H.
  apply/fdist_ext => a.
  rewrite fdist_convnE big_ord_recl H mul1r big1 ?addr0 //= => j _.
  by move/eqP/fdist1P : H => -> //; rewrite ?mul0r.
apply/fdist_ext => a.
rewrite fdist_convE fdist_convnE /= big_ord_recl; congr (_ + _)%R.
rewrite IH fdist_convnE big_distrr /=; apply eq_bigr => i _.
rewrite fdist_delE fdistD1E eq_sym (negbTE (neq_lift _ _)).
rewrite mulrAC mulrC -!mulrA; congr *%R.
rewrite /fdist_del_idx ltn0 /onem mulVr ?mulr1//.
exact/onem_neq0.
Qed.

End convn_convnfdist.
