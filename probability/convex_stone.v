(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg fingroup perm finalg matrix.
From mathcomp Require boolp.
Require Import Reals Lra.
From mathcomp Require Import Rstruct.
Require Import ssrR Reals_ext Ranalysis_ext ssr_ext ssralg_ext logb Rbigop.
Require Import fdist convex.

(****************************************************************************)
(* Direct formalization of the Lemma 2 from M. H. Stone. Postulates for the *)
(* barycentric calculus. Ann. Mat. Pura Appl., 29(1):25–30, 1949. The file  *)
(* convex_choice.v contains a shorter proof.                                *)
(****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope convex_scope.
Local Open Scope proba_scope.
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
  s = (lift_perm ord0 ord0 (PermDef.perm (swap_asa_inj K)) * tperm (ord0) (s ord0))%g.
Proof.
apply/permP => i.
rewrite [in RHS]permE /=.
case/boolP : (i == ord0 :> 'I_n.+2) => i0.
  by rewrite (eqP i0) lift_perm_id permE.
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
case/boolP : (s ord0 == ord0 :> 'I__) => K.
  apply H2; exact/eqP.
rewrite (swap_asaE K); apply H0; first exact/H1.
apply H2; by rewrite lift_perm_id.
Qed.

Lemma decomp_swap (n : nat) (s : 'S_n.+2) (K : s ord0 != ord0) :
  tperm ord0 (s ord0) =
  ((tperm (lift ord0 ord0) (s ord0)) *
   (tperm ord0 (lift ord0 ord0)) *
   (tperm (lift ord0 ord0) (s ord0)))%g :> 'S_n.+2.
Proof.
apply /permP => /= i.
case/boolP : (i == ord0 :> 'I__) => [/eqP ->|Hi];
 first by do ! rewrite permE /=;
          have -> : (if ord0 == s ord0 then lift ord0 ord0 else ord0) = ord0
            by move => n0; rewrite ifN_eqC //=.
do ! rewrite permE /=.
rewrite ifN_eq //.
case/boolP : (i == lift ord0 ord0 :> 'I__) => [/eqP ->|Hi1].
- case/boolP : (s ord0 == lift ord0 ord0 :> 'I__) => [/eqP ->|Hs];
    first by rewrite eq_refl;
      have -> : (if lift ord0 ord0 == ord0 then lift ord0 ord0 else ord0) = ord0;
      done.
- rewrite ifN_eqC //=.
  have -> : (if s ord0 == ord0 then lift ord0 ord0 else s ord0) = s ord0 by rewrite ifN_eq.
  by rewrite ifN_eq //= eq_refl.
case/boolP : (i == s ord0 :> 'I__) => His;
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
case/boolP : (s ord0 == ord0 :> 'I__) => K.
  apply H2; exact/eqP.
apply suff_generators0 => // s'.
case/boolP : (s' ord0 == lift ord0 ord0 :> 'I__) => K'; first by rewrite (eqP K').
case/boolP : (s' ord0 == ord0 :> 'I__) => K''.
  by rewrite (eqP K''); apply H2; rewrite permE.
rewrite decomp_swap //.
apply H0.
  apply H2; by rewrite permE /= eq_sym (negbTE K'').
apply H0; first exact: H1.
apply H2; by rewrite permE /= eq_sym (negbTE K'').
Qed.

End Sn.

Section convex_space_prop.
Variables A : convType.
Implicit Types a b : A.
Lemma conv0 a b : a <| 0%:pr |> b = b.
Proof.
by rewrite convC (_ : _%:pr = 1%:pr) ?conv1 //=; apply val_inj; exact: onem0.
Qed.

Lemma convA0 (p q r s : prob) a b c :
  p = (r * s)%R :> R -> (s.~ = p.~ * q.~)%R ->
  a <| p |> (b <| q |> c) = (a <| r |> b) <| s |> c.
Proof.
move=> H1 H2.
case/boolP : (r == 0%:pr) => r0.
  rewrite (eqP r0) conv0 (_ : p = 0%:pr) ?conv0; last first.
    by apply/val_inj; rewrite /= H1 (eqP r0) mul0R.
  congr (_ <| _ |> _); move: H2; rewrite H1 (eqP r0) mul0R onem0 mul1R.
  move/(congr1 onem); rewrite !onemK => ?; exact/val_inj.
case/boolP : (s == 0%:pr) => s0.
  rewrite (eqP s0) conv0 (_ : p = 0%:pr) ?conv0; last first.
    by apply/val_inj; rewrite /= H1 (eqP s0) mulR0.
  rewrite (_ : q = 0%:pr) ?conv0 //.
  move: H1; rewrite (eqP s0) mulR0 => p0.
  move: H2; rewrite p0 onem0 mul1R => /(congr1 onem); rewrite !onemK => sq.
  rewrite -(eqP s0); exact/val_inj.
rewrite convA; congr ((_ <| _ |> _) <| _ |> _).
  by apply val_inj; rewrite /= s_of_pqE -H2 onemK.
by rewrite (@r_of_pq_is_r  _ _ r s).
Qed.

Lemma convA' (r s : prob) a b c : [p_of r, s] != 1%:pr ->
  a <| [p_of r, s] |> (b <| [q_of r, s] |> c) = (a <| r |> b) <| s |> c.
Proof.
move=> H; case/boolP : (s == 0%:pr) => s0.
- by rewrite (eqP s0) p_of_r0 conv0 q_of_r0 conv0 conv0.
- by rewrite convA s_of_pqK // r_of_pqK.
Qed.

Lemma convACA (x1 y1 x2 y2 : A) p q :
  (x1 <|q|> y1) <|p|> (x2 <|q|> y2) = (x1 <|p|> x2) <|q|> (y1 <|p|> y2).
Proof.
case/boolP : (p == 0%:pr) => [/eqP|] p0; first by rewrite p0 !conv0.
case/boolP : (q == 0%:pr) => [/eqP|] q0; first by rewrite q0 !conv0.
case/boolP : (p == 1%:pr) => [/eqP|] p1; first by rewrite p1 !conv1.
case/boolP : (q == 1%:pr) => [/eqP|] q1; first by rewrite q1 !conv1.
set r := [p_of q, p].
have r1 : (r != 1%:pr)%R by rewrite p_of_neq1 // -prob_gt0 -prob_lt1.
rewrite -(convA' x1 y1) //.
rewrite (convC y1).
set s := [q_of q, p].
set t := (s.~%:pr * q)%:pr.
have t1 : (t < 1)%R.
  rewrite -prob_lt1; apply/eqP => t1; subst t.
  have {q1} : (q < 1)%R by rewrite -prob_lt1.
  move/(congr1 Prob.p) : t1 => /= <-.
  rewrite -ltR_pdivr_mulr; last by rewrite -prob_gt0.
  rewrite divRR // /onem ltR_subr_addl ltRNge; apply.
  by rewrite -{1}(add0R 1%R) leR_add2r.
rewrite -(convA' x2); last by rewrite prob_lt1 p_of_rsC /= p_of_rsE.
rewrite -(convA' x1) //; last by rewrite p_of_rsC.
rewrite (convC y2 y1) /=.
congr (_ <| _ |> _); first by rewrite p_of_rsC.
congr (_ <| _ |> _).
  (* TODO: lemma? *)
  apply val_inj => /=.
  rewrite /s /onem /= !(p_of_rsE,q_of_rsE) /= !(p_of_rsE,q_of_rsE) /= /onem.
  field.
  rewrite subR_eq0 mulRC; apply/nesym/eqP; by rewrite -p_of_rsE.
congr (_ <| _ |> _).
apply val_inj => /=.
rewrite -[in RHS](onemK p); congr onem.
rewrite q_of_rsE {1}p_of_rsE /= q_of_rsE p_of_rsE /= /onem; field.
split.
  rewrite subR_eq0; apply/nesym/eqP; by rewrite -p_of_rsE.
rewrite mulRBl mul1R subRBA subRK mulRDr mulR1 mulRN addR_opp subRBA subRK.
rewrite subR_eq0 => /esym; exact/eqP.
Qed.

Lemma distribute (x y z : A) (p q : prob) :
  x <| p |> (y <| q |> z) = (x <| p |> y) <| q |> (x <| p |> z).
Proof. by rewrite -{1}(convmm x q) convACA. Qed.

Lemma ConvnFDist1 (n : nat) (j : 'I_n) (g : 'I_n -> A): <|>_(FDist1.d j) g = g j.
Proof.
elim: n j g => [[] [] //|n IH j g /=].
case: Bool.bool_dec => [/eqP|/Bool.eq_true_not_negb b01].
  rewrite FDist1.dE; case j0 : (_ == _) => /=.
  by move=> _; rewrite (eqP j0).
  rewrite (_ : (0%:R)%R = 0%R) //; lra.
rewrite (_ : probfdist _ _ = 0%:pr) ?conv0; last first.
  apply val_inj => /=; move: b01; rewrite !FDist1.dE => j0.
  case j0' : (_ == _) => //; by rewrite j0' eqxx in j0.
have j0 : ord0 != j by apply: contra b01 => /eqP <-; rewrite FDist1.dE eqxx.
have j0' : 0 < j by rewrite lt0n; apply: contra j0 => /eqP j0; apply/eqP/val_inj.
move=> [:H]; have @j' : 'I_n.
  by apply: (@Ordinal _ j.-1 _); abstract: H; rewrite prednK // -ltnS.
rewrite (_ : DelFDist.d b01 = FDist1.d j'); last first.
  apply/fdist_ext => /= k.
  rewrite DelFDist.dE D1FDist.dE /= !FDist1.dE /= (negbTE j0) subR0 divR1.
  congr (INR (nat_of_bool _)).
  move R : (k == _) => [|].
  - apply/eqP/val_inj; rewrite /= /bump leq0n add1n.
    by move/eqP : R => -> /=; rewrite prednK // lt0n.
  - apply: contraFF R => /eqP.
    move/(congr1 val) => /=; rewrite /bump leq0n add1n => kj.
    by apply/eqP/val_inj; rewrite /= -kj.
rewrite IH /DelFDist.f ltn0; congr g.
by apply val_inj; rewrite /= /bump leq0n add1n prednK // lt0n.
Qed.

Lemma convn1E a e : <|>_e (fun _ : 'I_1 => a) = a.
Proof.
rewrite /=; case: Bool.bool_dec => // /Bool.eq_true_not_negb H; exfalso; move/eqP: H; apply.
by apply/eqP; rewrite FDist1.dE1 (FDist1.I1 e).
Qed.

Lemma convnE n (g : 'I_n.+1 -> A) (d : {fdist 'I_n.+1}) (i1 : d ord0 != 1%R) :
  <|>_d g = g ord0 <| probfdist d ord0 |> <|>_(DelFDist.d i1) (fun x => g (DelFDist.f ord0 x)).
Proof.
rewrite /=; case: Bool.bool_dec => /= [|/Bool.eq_true_not_negb] H.
exfalso; by rewrite (eqP H) eqxx in i1.
by rewrite (boolp.Prop_irrelevance H i1).
Qed.

Lemma convn2E (g : 'I_2 -> A) (d : {fdist 'I_2}) :
  <|>_d g = g ord0 <| probfdist d ord0 |> g (Ordinal (erefl (1 < 2))).
Proof.
case/boolP : (d ord0 == 1%R) => [|i1].
  rewrite FDist1.dE1 => /eqP ->; rewrite ConvnFDist1.
  rewrite (_ : probfdist _ _ = 1%:pr) ?conv1 //.
  by apply val_inj; rewrite /= FDist1.dE eqxx.
rewrite convnE; congr (_ <| _ |> _).
rewrite (_ : (fun _ => _) = (fun=> g (DelFDist.f ord0 ord0))); last first.
  by rewrite boolp.funeqE => x; rewrite (ord1 x).
by rewrite convn1E /DelFDist.f ltnn; congr g; exact/val_inj.
Qed.

Lemma convn3E (g : 'I_3 -> A) (d : {fdist 'I_3}) (p : prob) :
  d ord0 != 1%R ->
  p = (d (lift ord0 ord0) / (1 - d ord0))%R :> R ->
  <|>_d g = g ord0 <| probfdist d ord0 |> (g (Ordinal (erefl (1 < 3)%nat)) <| p |> g (Ordinal (erefl (2 < 3)%nat))).
Proof.
move=> i1 Hp.
case/boolP : (p == 1%:pr) => p1.
  rewrite convnE; congr (_ <| _ |> _).
  rewrite convn2E /DelFDist.f ltnn /=; congr (g _ <| _ |> g _).
  apply val_inj => /=.
  by rewrite DelFDist.dE D1FDist.dE (eq_sym (lift _ _)) (negbTE (neq_lift _ _)) -Hp.
  exact/val_inj.
  exact/val_inj.
rewrite convnE; congr (_ <| _ |> _).
rewrite convn2E /DelFDist.f ltnn /=; congr (g _ <| _ |> g _).
apply val_inj => /=.
by rewrite DelFDist.dE D1FDist.dE (eq_sym (lift _ _)) (negbTE (neq_lift _ _)).
exact/val_inj.
exact/val_inj.
Qed.

Lemma convn_proj n (g : 'I_n -> A) (d : {fdist 'I_n}) i :
  d i = R1 -> <|>_d g = g i.
Proof.
elim: n g d i => [d d0|n IH g d i di1]; first by move: (fdistI0_False d0).
case/boolP : (i == ord0) => [/eqP|]i0.
  move/eqP : di1; rewrite i0 FDist1.dE1 => /eqP ->.
  by rewrite ConvnFDist1.
have d00 : d ord0 = R0 by move/eqP/FDist1.P : di1 => -> //; rewrite eq_sym.
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
rewrite DelFDist.dE ltn0 D1FDist.dE eq_sym (negbTE (neq_lift _ _ )).
rewrite d00 subR0 divR1 -di1; congr (d _).
by apply val_inj; rewrite /= /bump leq0n add1n prednK // lt0n.
Qed.

(* goal: Conv_perm *)

Lemma Convn_perm_1 n (d : {fdist 'I_n}) (g : 'I_n -> A) :
  <|>_d g = <|>_(PermFDist.d d 1%g) (g \o (1%g : 'S_n)).
Proof.
rewrite PermFDist.dE1; congr (Convn d _).
by rewrite boolp.funeqE => i /=; rewrite perm1.
Qed.

Lemma Convn_perm1 (d : {fdist 'I_1}) (g : 'I_1 -> A) (s : 'S_1) :
  <|>_d g = <|>_(PermFDist.d d s) (g \o s).
Proof.
have s1 : s = 1%g.
  apply/permP => i; by case: (s i) => -[|//] ?; rewrite perm1 (ord1 i); exact/val_inj.
by rewrite s1 -Convn_perm_1.
Qed.

Lemma Convn_perm2 (d : {fdist 'I_2}) (g : 'I_2 -> A) (s : 'S_2) :
  <|>_d g = <|>_(PermFDist.d d s) (g \o s).
Proof.
have [->|Hs] := S2.generators s.
  rewrite PermFDist.dE1; congr Convn.
  by rewrite boolp.funeqE => i; rewrite /= perm1.
move: (FDist.ge0 d ord0); rewrite leR_eqVlt => -[/esym d00|d00].
  have d11 : d (Ordinal (erefl (1 < 2))) = 1%R.
    rewrite -(FDist.f1 d) 2!big_ord_recl big_ord0 addR0 d00 add0R; f_equal; exact/val_inj.
  have H1 : d = FDist1.d (Ordinal (erefl (1 < 2))).
    rewrite -I2FDist.p0; apply/fdist_ext => /= i.
    rewrite I2FDist.dE; case: ifPn => [/eqP ->//|/= i0]; rewrite onem0.
    rewrite -(FDist.f1 d) 2!big_ord_recl big_ord0 addR0 d00 add0R; congr (d _).
    case: i i0 => -[//|] -[|//] //= i12 _; exact/val_inj.
  rewrite {1}H1 ConvnFDist1 {1}Hs.
  have H2 : PermFDist.d d (tperm ord0 (Ordinal (erefl (1 < 2)))) = FDist1.d ord0.
    apply/fdist_ext => /= i; rewrite PermFDist.dE FDist1.dE.
    case/boolP : (i == ord0 :> 'I__) => i0.
      by rewrite (eqP i0) permE /= d11.
    rewrite permE /= (negbTE i0).
    by case: ifPn => //; case: i i0 => -[|[|]].
  by rewrite H2 ConvnFDist1 /=; congr g; rewrite Hs permE /=.
case/boolP : (d (lift ord0 ord0) == 0%R :> R) => d10.
  have d01 : d ord0 = 1%R.
    rewrite -(FDist.f1 d) !big_ord_recl big_ord0 addR0.
    by rewrite addRC -subR_eq subRR (eqP d10).
  have -> : d = FDist1.d ord0 by apply/eqP; rewrite -FDist1.dE1; exact/eqP.
  by rewrite ConvnFDist1 {1}Hs PermFDist.tperm ConvnFDist1 /= Hs permE.
rewrite convn2E.
rewrite convn2E.
rewrite /= Hs permE /= convC !permE /=; congr (_ <| _ |> _); apply val_inj => /=.
rewrite PermFDist.dE permE /= /onem -(FDist.f1 d) !big_ord_recl big_ord0 addR0 addRC addRK.
f_equal; exact/val_inj.
Qed.

Lemma Convn_perm3_p01 (d : {fdist 'I_3}) (g : 'I_3 -> A) :
  <|>_d g = <|>_(PermFDist.d d S3.p01) (g \o S3.p01).
Proof.
have : (d ord0 + d (lift ord0 ord0) = 0 \/ d (lift ord0 ord0) + d ord_max = 0 \/
  (0 < d ord0 + d (lift ord0 ord0) /\ 0 < d (lift ord0 ord0) + d ord_max))%R.
  have : (0 <= d ord0 + d (lift ord0 ord0))%R by apply addR_ge0.
  have : (0 <= d (lift ord0 ord0) + d ord_max)%R by apply addR_ge0.
  rewrite leR_eqVlt => -[|H]; first by auto.
  rewrite leR_eqVlt => -[|H']; first by auto.
  right; right; by auto.
move=> [ H | [ H | [H1 H2] ] ].
  have /eqP d1 : d ord_max = 1%R.
    rewrite -(FDist.f1 d) !big_ord_recl big_ord0 addR0 addRA H add0R; congr (d _); exact/val_inj.
  rewrite FDist1.dE1 in d1.
  rewrite {1}(eqP d1) ConvnFDist1.
  by rewrite (eqP d1) PermFDist.d1 ConvnFDist1 /= permKV.
  have /eqP d1 : d ord0 = 1%R.
    rewrite -(FDist.f1 d) !big_ord_recl big_ord0 addR0 addRC -subR_eq subRR.
    rewrite (_ : lift ord0 (lift _ _) = ord_max) ?H //; exact/val_inj.
  rewrite FDist1.dE1 in d1.
  by rewrite (eqP d1) ConvnFDist1 PermFDist.d1 ConvnFDist1 /= permKV.
have d01 : d ord0 <> 1%R.
  move=> /eqP d01.
  move: H2.
  move/FDist1.P : (d01) => -> //.
  move/FDist1.P : d01 => -> //.
  by rewrite add0R; move/ltRR.
move=> [:Hp].
have @p : prob.
  apply: (@Prob.mk_ (d (lift ord0 ord0) / (1 - d ord0))).
  abstract: Hp.
  split.
    apply/divR_ge0 => //.
    by rewrite subR_gt0 -fdist_lt1; exact/eqP.
  rewrite leR_pdivr_mulr ?mul1R ?subR_gt0 -?fdist_lt1; last exact/eqP.
  rewrite leR_subr_addr -(FDist.f1 d) !big_ord_recl big_ord0 addR0.
  by rewrite addRC leR_add2l addRC -leR_subl_addr subRR.
case/boolP : (p == 1%:pr :> prob) => [/eqP |p1].
  move/(congr1 Prob.p); rewrite [in X in X -> _]/=.
  rewrite eqR_divr_mulr ?mul1R; last by apply/eqP; rewrite subR_eq0; exact/nesym.
  move=> H.
  rewrite (@convn3E _ _ 1%:pr) ?conv1; last 2 first.
    exact/eqP.
    by rewrite H divRR // subR_eq0' eq_sym; exact/eqP.
  case/boolP : (d ord0 == 0 :> R)%R => d00.
    rewrite (_ : probfdist _ _ = 0%:pr) ?conv0; last by apply val_inj => /=; exact/eqP.
    move: H; rewrite (eqP d00) subR0 => /eqP; rewrite FDist1.dE1 => /eqP ->.
    rewrite PermFDist.d1 ConvnFDist1 /= permKV; congr g; exact/val_inj.
  rewrite (@convn3E _ _ 1%:pr) ?conv1; last first.
    rewrite !PermFDist.dE /S3.p01 /= !permE /=.
    rewrite (_ : Ordinal _ = lift ord0 ord0); last exact/val_inj.
    by rewrite H subRB subRR add0R divRR.
  rewrite /S3.p01 /= PermFDist.dE permE /=.
  rewrite (_ : Ordinal _ = lift ord0 ord0); last exact/val_inj.
  apply: contra d00 => /eqP d001.
  move: H; rewrite d001 => /esym.
  by rewrite subR_eq addRC -subR_eq subRR => <-.
  rewrite /= /S3.p01 !permE /= convC.
  congr (g _ <| _ |> g _).
  apply/val_inj; rewrite /= PermFDist.dE permE /=.
  by rewrite (_ : Ordinal _ = lift ord0 ord0) ?H //; exact/val_inj.
rewrite (@convn3E _ _ p) //; last exact/eqP.
rewrite convA.
rewrite (convC (g ord0)).
have H : [p_of [r_of probfdist d ord0, p].~%:pr, [s_of probfdist d ord0, p]] != 1%:pr :> R.
  apply p_of_neq1.
  rewrite s_of_pqE /=.
  rewrite onemM !onemK -subRBA -[X in (_ < _ - (_ - X) < _)%R]mul1R.
  rewrite -mulRBl -addR_opp -mulNR oppRB /Rdiv mulRCA mulRV ?mulR1; last first.
    apply/eqP; rewrite subR_eq0; by auto.
  split => //.
  rewrite ltR_neqAle; split.
    apply/eqP; apply: contra p1 => p1.
    apply/eqP/val_inj => /=.
    move: p1; rewrite eq_sym addRC -subR_eq' => /eqP <-.
    rewrite divRR // subR_eq0'; apply/eqP; by auto.
  by rewrite -(FDist.f1 d) !big_ord_recl /= big_ord0 addR0 addRA leR_addl.
rewrite -convA'; last by [].
case/boolP : (d (S3.p01 ord0) == 1 :> R)%R => ds01.
  move: (ds01); rewrite /S3.p01 permE => d01'.
  rewrite /= in d01'.
  rewrite (_ : Ordinal _ = lift ord0 ord0) in d01'; last exact/val_inj.
  rewrite FDist1.dE1 in d01'.
  rewrite FDist1.dE1 in ds01.
  rewrite [in RHS](eqP ds01) PermFDist.d1 ConvnFDist1 /= permKV.
  rewrite (_ : [p_of _, _] = 1%:pr); last first.
    apply/val_inj => /=.
    rewrite p_of_rsE /= r_of_pqE /= s_of_pqE /= (eqP d01').
    rewrite FDist1.dE /= div0R onem0 subR0 !mul1R divR1 onemK.
    by rewrite FDist1.dE eqxx.
  rewrite conv1 /S3.p01 permE /= (_ : Ordinal _ = lift ord0 ord0) //; exact/val_inj.
move=> [:Hq].
have @q : prob.
  apply: (@Prob.mk_
    ((PermFDist.d d S3.p01) (lift ord0 ord0) / (1 - (PermFDist.d d S3.p01) ord0))).
  abstract: Hq.
  rewrite !PermFDist.dE.
  split; first by apply/divR_ge0 => //; rewrite subR_gt0 -fdist_lt1.
  rewrite leR_pdivr_mulr ?mul1R; last by rewrite subR_gt0 -fdist_lt1.
  rewrite leR_subr_addr -(FDist.f1 (PermFDist.d d S3.p01)) !big_ord_recl big_ord0.
  by rewrite addR0 !PermFDist.dE addRCA addRA -[X in (X <= _)%R]addR0 leR_add2l.
rewrite (@convn3E _ _ q) //; last by rewrite PermFDist.dE.
congr (_ <| _ |> _).
  apply/val_inj => /=.
  rewrite PermFDist.dE permE /= p_of_rsE /= r_of_pqE /=.
  rewrite s_of_pqE /= /onem.
  rewrite (_ : Ordinal _ = lift ord0 ord0); last exact/val_inj.
  field.
  split; first by rewrite subR_eq0; exact/nesym.
  rewrite -addR_opp oppRB -addR_opp oppRB addRC addRA subRK.
  by apply/eqP; rewrite gtR_eqF // addRC.
by rewrite /= /S3.p01 permE /=; congr g; exact/val_inj.
congr (_ <| _ |> _).
  apply val_inj => /=.
  rewrite q_of_rsE /= !PermFDist.dE p_of_rsE /= r_of_pqE /= s_of_pqE.
  rewrite /= /onem !permE /=.
  rewrite (_ : Ordinal _ = lift ord0 ord0); last exact/val_inj.
  field.
  split.
    rewrite subR_eq0.
    apply/nesym/eqP.
    apply: contra ds01.
    rewrite /S3.p01 permE /= (_ : Ordinal _ = lift ord0 ord0) //; exact/val_inj.
  split; first by rewrite subR_eq0; exact/nesym.
  rewrite -addR_opp oppRB -addR_opp oppRB addRC addRA subRK.
  by apply/eqP; rewrite gtR_eqF // addRC.
by congr g; apply val_inj => /=; rewrite /S3.p01 permE.
by rewrite /= /S3.p01 permE.
Qed.

Lemma Convn_perm3_p02 (d : {fdist 'I_3}) (g : 'I_3 -> A) :
  <|>_d g = <|>_(PermFDist.d d S3.p02) (g \o S3.p02).
Proof.
(* TODO(rei): redundant part with Convn_perm3_p02 *)
have : (d ord0 + d (lift ord0 ord0) = 0 \/ d (lift ord0 ord0) + d ord_max = 0 \/
  (0 < d ord0 + d (lift ord0 ord0) /\ 0 < d (lift ord0 ord0) + d ord_max))%R.
  have : (0 <= d ord0 + d (lift ord0 ord0))%R by apply addR_ge0.
  have : (0 <= d (lift ord0 ord0) + d ord_max)%R by apply addR_ge0.
  rewrite leR_eqVlt => -[|H]; first by auto.
  rewrite leR_eqVlt => -[|H']; first by auto.
  right; right; by auto.
move=> [ H | [ H | [H1 H2] ] ].
  have /eqP d1 : d ord_max = 1%R.
    rewrite -(FDist.f1 d) !big_ord_recl big_ord0 addR0 addRA H add0R; congr (d _); exact/val_inj.
  rewrite FDist1.dE1 in d1.
  rewrite {1}(eqP d1) ConvnFDist1.
  by rewrite (eqP d1) PermFDist.d1 ConvnFDist1 /= permKV.
  have /eqP d1 : d ord0 = 1%R.
    rewrite -(FDist.f1 d) !big_ord_recl big_ord0 addR0 addRC -subR_eq subRR.
    rewrite (_ : lift ord0 (lift _ _) = ord_max) ?H //; exact/val_inj.
  rewrite FDist1.dE1 in d1.
  by rewrite (eqP d1) ConvnFDist1 PermFDist.d1 ConvnFDist1 /= permKV.
have d01 : d ord0 <> 1%R.
  move=> /eqP d01.
  move: H2.
  move/FDist1.P : (d01) => -> //.
  move/FDist1.P : d01 => -> //.
  by rewrite add0R; move/ltRR.
move=> [:Hp].
have @p : prob.
  apply: (@Prob.mk_ (d (lift ord0 ord0) / (1 - d ord0))).
  abstract: Hp.
  split; first by apply/divR_ge0 => //; rewrite subR_gt0 -fdist_lt1; exact/eqP.
  rewrite leR_pdivr_mulr ?mul1R ?subR_gt0 -?fdist_lt1; last exact/eqP.
  rewrite leR_subr_addr -(FDist.f1 d) !big_ord_recl big_ord0 addR0.
  by rewrite addRC leR_add2l addRC -leR_subl_addr subRR.
rewrite (@convn3E _ _ p) //; last exact/eqP.
rewrite convC.
rewrite (convC _ (g (Ordinal (erefl (2 < 3))))).
case/boolP : (d ord_max == 1%R :> R) => dmax1.
  move/FDist1.P in dmax1.
  by move: H1; rewrite dmax1 // dmax1 // addR0 => /ltRR.
case/boolP : (d ord0 == 0 :> R)%R => d00.
  rewrite (_ : (probfdist _ _).~%:pr = 1%:pr) ?conv1; last first.
    by apply/val_inj; rewrite /= (eqP d00) onem0.
  rewrite (@convn3E _ _ 1%:pr); last 2 first.
    rewrite PermFDist.dE /= !permE /=.
    rewrite (_ : Ordinal _ = ord_max) //; exact/val_inj.
    rewrite !PermFDist.dE /S3.p02 !permE /=.
    rewrite (_ : Ordinal _ = ord_max) //; last exact/val_inj.
    rewrite -{2}(FDist.f1 d) !big_ord_recl big_ord0 addR0 (eqP d00) add0R.
    rewrite (_ : lift _ (lift _ _) = ord_max); last exact/val_inj.
    rewrite addRK divRR //.
    apply/eqP => d10.
    by move: H1; rewrite (eqP d00) d10 addR0 => /ltRR.
  rewrite /= /S3.p02 !permE /= conv1.
  congr (g _ <| _ |> _).
  apply/val_inj => /=.
  rewrite PermFDist.dE permE /=.
  rewrite (_ : Ordinal _ = ord_max) //; last exact/val_inj.
  rewrite (eqP d00) subR0 divR1 /onem -(FDist.f1 d) /= !big_ord_recl big_ord0 addR0.
  rewrite (eqP d00) add0R addRC addRK; congr (d _); exact/val_inj.
have H : [p_of p.~%:pr, (probfdist d ord0).~%:pr] != 1%:pr.
  apply p_of_neq1 => /=; split.
    apply/onem_gt0; rewrite -fdist_lt1; exact/eqP.
  by rewrite ltR_subl_addr ltR_addl -fdist_gt0.
rewrite -convA'; last by [].
move=> [:Hq].
have @q : prob.
  apply: (@Prob.mk_ ((PermFDist.d d S3.p02) (lift ord0 ord0)
                     / (1 - (PermFDist.d d S3.p02) ord0))).
  abstract: Hq.
  rewrite !PermFDist.dE !permE /= (_ : Ordinal _ = ord_max); last exact/val_inj.
  split.
    apply/divR_ge0 => //; first by rewrite subR_gt0 -fdist_lt1.
  rewrite leR_pdivr_mulr ?mul1R ?subR_gt0 -?fdist_lt1 //.
  rewrite leR_subr_addr -(FDist.f1 d) !big_ord_recl big_ord0 addR0.
  by rewrite (_ : lift _ (lift _ _) = ord_max) ?leR_addr //; exact/val_inj.
rewrite (@convn3E _ _ q) //; last first.
  rewrite PermFDist.dE permE /= (_ : Ordinal _ = ord_max) //; exact/val_inj.
rewrite /= !permE /=.
congr (g _ <| _ |> (_ <| _ |> _)).
  apply val_inj => /=.
  rewrite !PermFDist.dE p_of_rsE /= permE /=.
  rewrite (_ : Ordinal _ = ord_max); last exact/val_inj.
  rewrite {1}/onem.
  rewrite mulRBl mul1R /Rdiv -mulRA mulVR ?mulR1; last first.
    rewrite subR_eq0' eq_sym; exact/eqP.
  rewrite /onem -subRD subR_eq -(FDist.f1 d) !big_ord_recl big_ord0 addR0.
  rewrite (_ : lift _ (lift _ _) = ord_max); last exact/val_inj.
  by rewrite [in RHS]addRC -addRA.
apply val_inj => /=.
rewrite !PermFDist.dE !permE /= q_of_rsE /= p_of_rsE /=.
rewrite (_ : Ordinal _ = ord_max); last exact/val_inj.
rewrite onemK.
rewrite {1 2}/Rdiv.
rewrite -2!mulRA.
rewrite [in RHS]/Rdiv.
congr (_ * _)%R.
rewrite mulRA mulVR; last first.
  rewrite subR_eq0' eq_sym; exact/eqP.
rewrite mul1R.
congr Rinv.
rewrite onemM !onemK.
rewrite addRC.
rewrite -{1}(mulR1 (d (lift ord0 ord0) / _))%R.
rewrite -subRBA.
rewrite -mulRBr.
rewrite -addR_opp.
rewrite -mulRN.
rewrite oppRB.
rewrite /Rdiv.
rewrite -mulRA.
rewrite mulVR ?mulR1; last first.
  rewrite subR_eq0' eq_sym; exact/eqP.
apply/esym; rewrite subR_eq -(FDist.f1 d) !big_ord_recl big_ord0 addR0.
rewrite (_ : lift _ (lift _ _) = ord_max); last exact/val_inj.
by rewrite addRA.
Qed.

Lemma Convn_perm3 (d : {fdist 'I_3}) (g : 'I_3 -> A) (s : 'S_3) :
  <|>_d g = <|>_(PermFDist.d d s) (g \o s).
Proof.
move: s d g.
apply: S3.suff_generators; last first.
  move=> s s' Hs Hs' d g.
  rewrite Hs Hs' PermFDist.mul; congr (Convn _ _).
  by rewrite boolp.funeqE => i /=; rewrite permE.
exact: Convn_perm3_p02.
exact: Convn_perm3_p01.
exact: Convn_perm_1.
Qed.

Lemma Convn_perm_projection n (d : {fdist 'I_n.+2})
  (g : 'I_n.+2 -> A) (s : 'S_n.+2) (H : s ord0 = ord0) (dmax1 : d ord0 != 1%R)
  (m : nat) (nm : n.+1 < m) (IH : forall n : nat, n < m -> forall (d : {fdist 'I_n}) (g : 'I_n -> A) (s : 'S_n),
    <|>_d g = <|>_(PermFDist.d d s) (g \o s)) :
  <|>_d g = <|>_(PermFDist.d d s) (g \o s).
Proof.
transitivity (g ord0 <| probfdist d ord0 |> (<|>_(DelFDist.d dmax1) (fun x => g (DelFDist.f ord0 x)))).
  by rewrite convnE.
set s' : 'S_n.+1 := PermDef.perm (Sn.proj0_inj H).
transitivity (g ord0 <| probfdist d ord0 |> (<|>_(PermFDist.d (DelFDist.d dmax1) s') ((fun x => g (DelFDist.f ord0 x)) \o s'))).
  by rewrite -IH.
transitivity (g (s ord0) <| probfdist d ord0 |> (<|>_(PermFDist.d (DelFDist.d dmax1) s') ((fun x => g (DelFDist.f ord0 x)) \o s'))).
  by rewrite H.
rewrite [in RHS]convnE //.
  by rewrite PermFDist.dE H.
move=> K.
congr (_ <| _ |> _).
  apply val_inj => /=; by rewrite PermFDist.dE H.
congr (Convn _ _).
  apply/fdist_ext => /= j.
  rewrite !PermFDist.dE !DelFDist.dE !D1FDist.dE !PermFDist.dE.
  rewrite /s' /=.
  rewrite permE.
  rewrite /f /=.
  rewrite H; congr (_ / _)%R.
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
rewrite /DelFDist.f /= /s' permE /f /=.
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

Lemma Convn_perm_tperm (n : nat) (d : {fdist 'I_n.+3})
  (g : 'I_n.+3 -> A) (s : 'S_n.+3) (H : s = tperm ord0 (lift ord0 ord0)) (dmax1 : d ord0 != 1%R)
  (m : nat) (nm : n.+3 < m.+1) (IH : forall n : nat, n < m ->
       forall (d : {fdist 'I_n}) (g : 'I_n -> A) (s : 'S_n),
       <|>_d g = <|>_(PermFDist.d d s) (g \o s)) :
  <|>_d g = <|>_(PermFDist.d d s) (g \o s).
Proof.
case/boolP : (d (lift ord0 ord0) == 1 - d ord0 :> R)%R => K.
  case/boolP : (d (lift ord0 ord0) == 1%R :> R) => [|d11].
    by rewrite FDist1.dE1 => /eqP ->; rewrite PermFDist.d1 !ConvnFDist1 /= permKV.
  rewrite convnE.
  rewrite [in RHS]convnE.
    by rewrite PermFDist.dE H permE.
  move=> K'.
  rewrite (_ : <|>_ _ _ = g (lift ord0 ord0)); last first.
    have /eqP : (DelFDist.d dmax1) ord0 = 1%R.
      by rewrite DelFDist.dE D1FDist.dE /= (eqP K) divRR // subR_eq0' eq_sym.
    rewrite FDist1.dE1 => /eqP ->.
    by rewrite ConvnFDist1.
  rewrite (_ : <|>_ _ _ = g ord0); last first.
    have /eqP : (DelFDist.d K') ord0 = 1%R.
      rewrite DelFDist.dE D1FDist.dE /= !PermFDist.dE H !permE /=.
      rewrite (eqP K) subRB subRR add0R divRR //.
      apply/eqP => d00.
      move: K; by rewrite d00 subR0 (negbTE d11).
    by rewrite FDist1.dE1 => /eqP ->; rewrite ConvnFDist1 /= H !permE /=.
  rewrite convC /= H permE /=; congr (_ <| _ |> _).
  by apply val_inj => /=; rewrite PermFDist.dE /= permE /= (eqP K).
case/boolP : (d (lift ord0 ord0) == 1%R :> R) => [|K1].
  by rewrite FDist1.dE1 => /eqP ->; rewrite PermFDist.d1 !ConvnFDist1 /= permKV.
(* TODO: isolate this construction? *)
pose D' : {ffun 'I_3 -> R} := [ffun x => [eta (fun=>R0) with
  ord0 |-> d ord0,
  lift ord0 ord0 |-> d (lift ord0 ord0),
  ord_max |-> (\sum_(i < n.+3 | (2 <= i)%nat) d i)%R] x].
have D'0 : (forall i, 0 <= D' i)%R.
  move=> i; rewrite /D' ffunE /=; case: ifPn => _ //.
  by case: ifPn => _ //; case: ifPn => _; [exact: sumR_ge0 | exact/leRR].
have D'1 : (\sum_(i < 3) (D' i) = 1)%R.
  rewrite !big_ord_recr big_ord0 /= add0R.
  rewrite /D' !ffunE /= -(FDist.f1 d).
  apply/esym.
  rewrite 2!big_ord_recl addRA; congr (_ + _)%R.
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
have H1 : (DelFDist.d dmax1) ord0 != 1%R.
  rewrite DelFDist.dE D1FDist.dE (eq_sym (lift _ _)) (negbTE (neq_lift _ _)).
  apply/eqP.
  rewrite eqR_divr_mulr ?mul1R; first exact/eqP.
  by apply/eqP; rewrite subR_eq0; exact/nesym/eqP.
pose G : 'I_3 -> A := [eta (fun=>g ord0) with
  ord0 |-> g ord0,
  lift ord0 ord0 |-> g (lift ord0 ord0),
  ord_max |-> <|>_(DelFDist.d H1) (fun i : 'I_n.+1 => g (lift ord0 (lift ord0 i)))].
transitivity (Convn D G).
  erewrite convn3E.
  rewrite convnE.
  congr (_ <| _ |> _).
  by apply/val_inj => /=; rewrite ffunE.
  rewrite convnE.
  rewrite /G.
  congr (_ <| _ |> _).
  by rewrite ffunE.
  by rewrite /= !ffunE DelFDist.dE D1FDist.dE.
rewrite (Convn_perm3 _ _ S3.p01).
pose q' := (d ord0 / (1 - d (lift ord0 ord0)))%R.
move=> [:Hq].
have @q : prob.
  apply: (@Prob.mk_ q').
  abstract: Hq.
  split; first by apply/divR_ge0 => //; rewrite subR_gt0 -fdist_lt1.
  rewrite leR_pdivr_mulr.
  rewrite mul1R.
  rewrite leR_subr_addr -(FDist.f1 d).
  rewrite 2!big_ord_recl addRA leR_addl.
  apply: sumR_ge0 => i _ //.
  by rewrite subR_gt0 -fdist_lt1.
rewrite (@convn3E _ _ q); last 2 first.
  rewrite PermFDist.dE permE /=.
  rewrite (_ : Ordinal _ = lift ord0 ord0); last exact/val_inj.
  by rewrite /D' ffunE /=.
  rewrite /= !PermFDist.dE /= !permE /=.
  rewrite (_ : Ordinal _ = lift ord0 ord0); last exact/val_inj.
  by rewrite !ffunE.
rewrite convnE.
  by rewrite PermFDist.dE H !permE.
move=> K2.
congr (_ <| _ |> _).
  apply val_inj => /=.
  rewrite !PermFDist.dE !permE /= (_ : Ordinal _ = lift ord0 ord0); last exact/val_inj.
  by rewrite ffunE H !permE.
by rewrite /= /G /= permE /= H permE /=.
rewrite convnE.
  rewrite DelFDist.dE D1FDist.dE !PermFDist.dE H !permE /=.
  apply/eqP.
  rewrite eqR_divr_mulr ?mul1R.
    move/esym.
    rewrite subR_eq; apply/eqP.
    apply: contra K => /eqP ->.
    by rewrite addRC addRK.
  by rewrite subR_eq0' eq_sym.
move=> K3.
congr (_ <| _ |> _).
  apply val_inj => /=.
  by rewrite !DelFDist.dE !D1FDist.dE /= !PermFDist.dE H !permE.
by rewrite /= /G /= !permE /= /DelFDist.f ltnn H permE /=.
pose s' : 'S_n.+1 := 1%g.
rewrite (@IH _ _ _ _ s') //; last by rewrite -ltnS ltnW.
transitivity (<|>_(DelFDist.d H1) (fun i : 'I_n.+1 => g (lift ord0 (lift ord0 i)))).
  by rewrite /G [in LHS]/= !permE [in LHS]/=.
congr (Convn _ _).
  apply/fdist_ext => j.
  rewrite !(DelFDist.dE,PermFDist.dE,D1FDist.dE).
  rewrite H !permE /=.
  field.
  split.
    rewrite subR_eq0; by apply/nesym/eqP.
  split.
    apply/eqP; apply: contra K => /eqP.
    rewrite subR_eq0 => <-.
  by rewrite subRB subRR add0R.
by rewrite subR_eq0; apply/nesym/eqP.
by rewrite boolp.funeqE => j; rewrite /= permE H permE.
Qed.

Lemma Convn_perm (n : nat) (d : {fdist 'I_n}) (g : 'I_n -> A) (s : 'S_n) :
  <|>_d g = <|>_(PermFDist.d d s) (g \o s).
Proof.
move: d g s.
elim: n.+1 {-2}n (ltnSn n) => {n} // m IH n nm d g s.
destruct n as [|n]; first by move: (fdistI0_False d).
destruct n as [|n]; first exact: Convn_perm1.
destruct n as [|n]; first exact: Convn_perm2.
destruct n as [|n]; first exact: Convn_perm3.
move: m IH nm d g.
apply (@Sn.suff_generators _ (fun s => forall m : nat,
  (forall n0, n0 < m ->
   forall (d : {fdist 'I_n0}) (g : 'I_n0 -> A) (s0 : 'S_n0),
   <|>_d g = <|>_(PermFDist.d d s0) (g \o s0)) ->
  n.+4 < m.+1 ->
  forall (d : {fdist 'I_n.+4}) (g : 'I_n.+4 -> A),
  <|>_d g = <|>_(PermFDist.d d s) (g \o s))).
- move=> s1 s2 H1 H2 m IH nm d g.
  rewrite (H1 m) // (H2 m) // PermFDist.mul; congr (Convn _ _).
  by rewrite boolp.funeqE => i; rewrite /= permM.
- move=> m IH nm d g.
  case/boolP : (d ord0 == 1%R :> R) => [|dmax1].
    rewrite FDist1.dE1 => /eqP ->.
    by rewrite ConvnFDist1 PermFDist.d1 ConvnFDist1 /= permKV.
  by apply Convn_perm_tperm with m.
- move=> {}s H.
  move=> m IH nm d g.
  case/boolP : (d ord0 == 1%R :> R) => [|dmax1].
    rewrite FDist1.dE1 => /eqP ->.
    by rewrite ConvnFDist1 PermFDist.d1 ConvnFDist1 /= permKV.
  by apply Convn_perm_projection with m.
Qed.

End convex_space_prop.

Section affine_function_prop0.
Lemma affine_function_Sum (A B : convType) (f : {affine A -> B}) (n : nat)
    (g : 'I_n -> A) (e : {fdist 'I_n}) :
  f (<|>_e g) = <|>_e (f \o g).
Proof.
elim: n g e => [g e|n IH g e]; first by move: (fdistI0_False e).
case/boolP : (e ord0 == 1%R :> R) => [|e01].
  by rewrite FDist1.dE1 => /eqP ->; rewrite 2!ConvnFDist1.
by rewrite 2!convnE affine_conv IH.
Qed.
End affine_function_prop0.

Section convn_convnfdist.
Variable A : finType.
Lemma convn_convnfdist n (g : 'I_n -> fdist_convType A) (d : {fdist 'I_n}) :
  <|>_d g = ConvnFDist.d d g.
Proof.
elim: n g d => /= [g d|n IH g d]; first by move: (fdistI0_False d).
case: Bool.bool_dec => [/eqP|/Bool.eq_true_not_negb] H.
  apply/fdist_ext => a.
  rewrite ConvnFDist.dE big_ord_recl H mul1R big1 ?addR0 //= => j _.
  by move/eqP/FDist1.P : H => -> //; rewrite ?mul0R.
apply/fdist_ext => a.
rewrite ConvFDist.dE ConvnFDist.dE /= big_ord_recl; congr (_ + _)%R.
rewrite IH ConvnFDist.dE big_distrr /=; apply eq_bigr => i _.
rewrite DelFDist.dE D1FDist.dE eq_sym (negbTE (neq_lift _ _)).
by rewrite /Rdiv mulRAC mulRC -mulRA mulVR ?mulR1 //; exact/onem_neq0.
Qed.
End convn_convnfdist.
