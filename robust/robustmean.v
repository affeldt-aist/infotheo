From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra ring.
From mathcomp Require boolp.
From mathcomp Require Import mathcomp_extra Rstruct reals.
From infotheo Require Import ssr_ext ssralg_ext bigop_ext.
From infotheo Require Import realType_ext fdist proba.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Import Order.POrderTheory Order.Theory Num.Theory GRing.Theory.

(**md**************************************************************************)
(* # resilience, robustmean                                                   *)
(*                                                                            *)
(* |Definitions  |    | Meaning                                              |*)
(* |-------------|----|------------------------------------------------------|*)
(* |    X `* Y   | == | multiplication of random variables                    *)
(* | `V_[X \| F] | == | conditional variance                                  *)
(* | ...         | == | ...                                                   *)
(*                                                                            *)
(******************************************************************************)

(* TODO: define RV_ringType mimicking fct_ringType *)
Section mul_RV.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).
Definition mul_RV (X Y : {RV P -> R}) : {RV P -> R} := fun x => X x * Y x.
Notation "X `* Y" := (mul_RV X Y) : proba_scope.
Arguments mul_RV /.

Lemma mul_RVA : associative mul_RV.
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite mulrA. Qed.
Lemma mul_RVC : commutative mul_RV.
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite mulrC. Qed.
Lemma mul_RVAC : right_commutative mul_RV.
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite mulrAC. Qed.
Lemma mul_RVCA : left_commutative mul_RV.
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite mulrCA. Qed.
Lemma mul_RVACA : interchange mul_RV mul_RV.
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite mulrACA. Qed.
Lemma mul_RVDr : right_distributive mul_RV (@add_RV _ U P R).
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite mulrDr. Qed.
Lemma mul_RVDl : left_distributive mul_RV (@add_RV _ U P R).
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite mulrDl. Qed.
Lemma mul_RVBr (f g h : {RV (P) -> (R)}) : f `* (g `- h) = f `* g `- f `* h.
Proof. by apply: boolp.funext=> u /=; rewrite mulrBr. Qed.
Lemma mul_RVBl (f g h : {RV (P) -> (R)}) : (f `- g) `* h = f `* h `- g `* h.
Proof. by apply: boolp.funext=> u /=; rewrite mulrBl. Qed.
End mul_RV.
Notation "X `* Y" := (mul_RV X Y) : proba_scope.
Arguments mul_RV /.

Section add_RV.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).
Arguments add_RV /.
Lemma add_RVA : associative (@add_RV _ U P R).
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite addrA. Qed.
Lemma add_RVC : commutative (@add_RV _ U P R).
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite addrC. Qed.
Lemma add_RVAC : right_commutative (@add_RV _ U P R).
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite addrAC. Qed.
Lemma add_RVCA : left_commutative (@add_RV _ U P R).
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite addrCA. Qed.
Lemma add_RVACA : interchange (@add_RV _ U P R) (@add_RV _ U P R).
Proof. by move=> *; apply: boolp.funext=> u /=; rewrite addrACA. Qed.
End add_RV.

Section scalelr.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).
Lemma scalel_RVE m (X : {RV P -> R}) : scalel_RV m X = const_RV P m `* X.
Proof. by apply: boolp.funext=> ? /=; rewrite /scalel_RV /const_RV. Qed.
Lemma scaler_RVE m (X : {RV P -> R}) : scaler_RV X m = X `* const_RV P m.
Proof. by apply: boolp.funext=> ? /=; rewrite /scaler_RV /const_RV. Qed.
End scalelr.


Section conj_intro_pattern.
(* /[conj] by Cyril Cohen : *)
(*    https://coq.zulipchat.com/#narrow/stream/237664-math-comp-users/topic/how.20to.20combine.20two.20top.20assumptions.20with.20.60conj.60 *)
Lemma and_curry (A B C : Prop) : (A /\ B -> C) -> A -> B -> C.
Proof. move=> + a b; exact. Qed.
End conj_intro_pattern.
Notation "[conj]" := (ltac:(apply and_curry)) (only parsing) : ssripat_scope.

Section RV_ring.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).

(* Import topology.*)

(* Lemma add_RV_addr (X Y : {RV P -> R}) : X `+ Y = (X + Y)%mcR. *)
(* Proof. reflexivity. Qed. *)

(* Lemma sub_RV_subr (X Y : {RV P -> R}) : X `- Y = (X - Y)%mcR. *)
(* Proof. reflexivity. Qed. *)

(* Lemma trans_sub_RV_subr (X : {RV P -> R}) (y : R) : *)
(*   X `-cst y = (X - cst y)%ring. *)
(* Proof. reflexivity. Qed. *)
Definition fdist_supp_choice : U.
Proof.
by move/set0Pn/xchoose:(fdist_supp_neq0 P).
Defined.

(* Canonical fdist_supp_pointedType := *)
(*   @classical_sets.Pointed.pack U fdist_supp_choice _ _ idfun. *)

(* Lemma mul_RV_mulr (X Y : {RV P -> R}) : X `* Y = (X * Y)%ring. *)
(* Proof. reflexivity. Qed. *)

(* Lemma sq_RV_sqrr (X : {RV P -> R}) : X `^2 = (X ^+ 2)%ring. *)
(* Proof. by rewrite /sq_RV/comp_RV; apply boolp.funext => u /=; rewrite mulR1. Qed. *)

(* Definition RV_ringE := *)
(*   (add_RV_addr, sub_RV_subr, trans_sub_RV_subr, mul_RV_mulr, sq_RV_sqrr). *)
End RV_ring.

Section sets_functions.

Lemma set1I (X:finType) (x:X) (A:{set X}) :
  [set x] :&: A = if x \in A then [set x] else set0.
Proof.
  case: ifPn => H0.
  - by apply/setIidPl; rewrite sub1set.
  - by apply/disjoint_setI0; rewrite disjoints1 H0.
Qed.

Lemma in_preim1 (A:finType) (B:eqType) (a:A) (b:B) X :
  (a \in finset (T:=A) (preim X (pred1 b))) -> X a = b.
Proof. by rewrite in_set => /eqP. Qed.

Lemma in_preim1' (A:finType) (B:eqType) (a:A) (b:B) X :
  (a \in finset (T:=A) (preim X (pred1 b))) = (X a == b).
Proof.
  apply/idP; case H: (X a == b); first by move/eqP: H <-; rewrite inE /= eqxx.
  by move: H=> /[swap] /in_preim1 ->; rewrite eqxx.
Qed.

Lemma Ind_subset {R : realType} (A : finType) (X Y : {set A}) :
  X \subset Y <-> forall a, Ind X a <= Ind Y a :> R.
Proof.
rewrite /Ind; split => H.
  move=> a; case: ifPn.
  - by move/subsetP ->.
  - by case: (a \in Y).
apply/subsetP => a aX.
by move: (H a); rewrite aX; case: (a \in Y) => //; rewrite ler10.
Qed.

End sets_functions.

Section probability.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).

Lemma sq_RVE (X : {RV P -> R}) : X `^2 = X `* X.
Proof. by []. Qed.

Lemma Ind_ge0 (X : {set U}) (x : U) : 0 <= Ind X x:> R.
Proof. by rewrite /Ind; case: ifPn. Qed.

Lemma Ind_setD (X Y : {set U}) :
  Y \subset X -> Ind (X :\: Y) = Ind X `- Ind Y :> {RV P -> R}.
Proof.
move/subsetP=> YsubX; rewrite /Ind /sub_RV. apply boolp.funext => u /=.
case: ifPn; rewrite inE ?negb_and;
  first by case/andP => /negbTE -> ->; rewrite subr0.
case/orP; first by move => /negbNE /[dup] /YsubX -> ->; rewrite subrr.
move/contraNN: (YsubX u) => YsubX'.
move=> /[dup] /YsubX' /negbTE -> /negbTE ->.
by rewrite subrr.
Qed.

Lemma cEx_ExInd (X : {RV P -> R}) F :
  `E_[X | F] = `E (X `* Ind (A:=U) F : {RV P -> R}) / Pr P F.
Proof.
rewrite /Pr /cEx (* need some lemmas to avoid unfolds *) -big_distrl /=.
apply: congr2=> //.
under eq_bigr => i _.
  rewrite big_distrr.
  have -> :
    \sum_(i0 in finset (preim X (pred1 i)) :&: F) (i * P i0) =
    \sum_(i0 in finset (preim X (pred1 i)) :&: F)
     (X i0 * @Ind _ U F i0 * P i0).
    apply congr_big => // i0.
    rewrite in_setI /Ind => /andP[] /in_preim1 -> ->.
    by rewrite mulr1.
  have H1 :
    \sum_(i0 in finset (preim X (pred1 i)) :\: F) X i0 * Ind F i0 * P i0 = 0.
  (* This should be true because all elements of the sum are 0 *)
    rewrite big1 // => i1.
    rewrite in_setD => /andP [H2 H3].
    by rewrite /Ind (negbTE H2) mulr0 mul0r.
  have :
    \sum_(i0 in finset (preim X (pred1 i))) X i0 * Ind F i0 * P i0 =
    \sum_(i0 in finset (preim X (pred1 i)) :&: F) X i0 * Ind F i0 * P i0 +
    \sum_(i0 in finset (preim X (pred1 i)) :\: F) X i0 * Ind F i0 * P i0
    by apply big_setID.
  rewrite H1 addr0 => <-.
  under eq_bigl do rewrite in_preim1'.
  by over.
by rewrite -partition_big_fin_img.
Qed.

Lemma cExE (X : {RV P -> R}) F : `E_[X | F] = (\sum_(u in F) X u * P u) / Pr P F.
Proof.
rewrite cEx_ExInd.
congr (_ / _).
rewrite /Ex /ambient_dist /Ind.
under eq_bigr do rewrite /mul_RV 2!fun_if if_arg mulr0 mul0r mulr1.
rewrite [in RHS]big_mkcond /=.
exact: eq_bigr.
Qed.

Lemma Ex_square_expansion a b (X Y : {RV P -> R}):
  `E ((a `cst* X `+ b `cst* Y) `^2) =
  a * a * `E (X `^2) + b * b * `E (Y `^2) + 2 * a * b * `E (X `* Y:{RV P -> R}).
Proof.
suff : `E ((a `cst* X `+ b `cst* Y) `^2) =
       `E ((a * a) `cst* (X `^2) `+
       (b * b) `cst* (Y `^2) `+ (2 * a * b) `cst* (X `* Y)).
  by rewrite !E_add_RV !E_scalel_RV.
apply eq_bigr => i H.
unfold ambient_dist, "`cst*", "`+", "`^2", "`o", "^", "`*".
rewrite !expr2 /=.
lra.
Qed.

Lemma Ex_square_eq0 X :
  (forall x, X x = 0 \/ P x = 0) <-> `E (X `^2 : {RV P -> R}) = 0.
Proof.
split=> [XP|EX20].
- rewrite /Ex big1// => u _.
  have [|->] := XP u; last by rewrite mulr0.
  by rewrite sq_RVE /mul_RV=> ->; rewrite !mul0r.
- move=> x; rewrite !(rwP eqP); apply/orP.
  rewrite -(sqrf_eq0 (X x)) (_ : _ ^+ 2 = (X `^2: {RV P -> R}) x) // -mulf_eq0.
  have -> // := psumr_eq0P _ EX20 => *.
  by rewrite mulr_ge0 // sq_RV_ge0.
Qed.

Lemma Cauchy_Schwarz_proba (X Y : {RV P -> R}):
  (`E (X `* Y : {RV P -> R})) ^+ 2 <= `E (X `^2) * `E (Y `^2).
Proof.
pose a : R := Num.sqrt (`E (Y `^2)).
pose b : R := Num.sqrt (`E (X `^2)).
have EXge0 : 0 <= `E (X `^2) by exact/Ex_ge0/sq_RV_ge0.
have EYge0 : 0 <= `E (Y `^2) by exact/Ex_ge0/sq_RV_ge0.
have H2ab : 2 * a * b * (b * a) = a * a * `E (X `^2) + b * b * `E (Y `^2).
  by rewrite -(sqr_sqrtr EXge0) -/b -(sqr_sqrtr EYge0) -/a !expr2; lra.
have [|a0] := eqVneq a 0.
  move/eqP; rewrite sqrtr_eq0. move/(conj EYge0)/andP/le_anti/esym=> a0.
  have HY : forall y, Y y = 0 \/ P y = 0 by apply/Ex_square_eq0/a0.
  have -> : `E (X `* Y: {RV P -> R}) = 0.
    apply/eqP.
    rewrite psumr_eq0.
      apply/allP => u _; rewrite inE /=.
      by case: (HY u) => ->; rewrite ?mulr0 ?mul0r.
    move => u _; rewrite /= .
    by case : (HY u) => -> ; rewrite ?mulr0 ?mul0r.
  by rewrite expr0n; exact/mulr_ge0.
have [|b0] := eqVneq b 0.
  move/eqP; rewrite sqrtr_eq0. move/(conj EXge0)/andP/le_anti/esym=> b0.
  have HX : forall x, X x = 0 \/ P x = 0 by apply /Ex_square_eq0/b0.
  have -> : `E (X `* Y: {RV P -> R}) = 0.
    apply/eqP; rewrite psumr_eq0 /mul_RV; last first.
      by move=> u _; case : (HX u) => -> ; rewrite ?mulr0 ?mul0r.
    apply/allP => u _; rewrite inE/=.
    by case : (HX u) => -> ; rewrite ?mulr0 ?mul0r.
  by rewrite expr0n; exact/mulr_ge0.
have {}a0 : 0 < a. (*removes a0 hypothesis and reuse it*)
  by rewrite lt_neqAle eq_sym; apply/andP; split=> //; exact/sqrtr_ge0.
have {}b0 : 0 < b.
  by rewrite lt_neqAle eq_sym; apply/andP; split=> //; exact/sqrtr_ge0.
rewrite -[leRHS]sqr_sqrtr ?mulr_ge0 // sqrtrM // -/a -/b.
rewrite -subr_le0 -oppr_ge0 opprB subr_sqr.
rewrite mulr_ge0 // -[X in _ + X]opprK subr_ge0 ?opprK.
- rewrite -(@ler_pM2l _ (2 * a * b)); last by do 2 apply: mulr_gt0 => //.
  rewrite -subr_ge0 H2ab -2!mulNr -mulrN -(mulrNN a a) -Ex_square_expansion.
  exact/Ex_ge0/sq_RV_ge0.
- rewrite -(@ler_pM2l _ (2 * a * b)); last by do 2 apply: mulr_gt0 => //.
  rewrite -subr_ge0 -mulrN opprK H2ab -Ex_square_expansion.
  exact/Ex_ge0/sq_RV_ge0.
Qed.

Lemma I_square F : Ind F = ((Ind F) `^2 : {RV P -> R}).
Proof.
rewrite sq_RVE boolp.funeqE /Ind /mul_RV => x.
by case: ifPn; rewrite ?mulr0 ?mulr1.
Qed.

Lemma I_double (F : {set U}) : Ind F = (Ind F) `* (Ind F) :> {RV P -> R}.
Proof. by rewrite [LHS]I_square sq_RVE. Qed.

(*
Lemma I_mult_one F : (Ind (A:=U) F : {RV P -> R}) `* 1 = Ind (A:=U) F.
(F: {RV P -> R}): (Ind (A:=U) F: {RV P -> R}) `* 1 = (Ind (A:=U) F : {RV P -> R}). *)

Lemma cEx_trans_sub_RV (X : {RV P -> R}) m F : Pr P F != 0 ->
  `E_[ (X `-cst m) | F] = `E_[ X | F ] - m.
Proof.
move=> PF0.
rewrite !cExE.
under eq_bigr do rewrite /trans_sub_RV mulrDl.
rewrite big_split/= mulrDl; congr (_ + _).
by rewrite -big_distrr /= -mulrA divff // mulr1.
Qed.

Lemma cEx_sub (X : {RV P -> R}) (F G: {set U}) :
  0 < Pr P F ->
  F \subset G ->
  `| `E_[ X | F ] - `E_[X | G] |
= `| `E ((X `-cst `E_[X | G]) `* Ind F : {RV P -> R}) | / Pr P F.
Proof.
move=> PrPF_gt0 FsubG.
rewrite -[X in _ / X]ger0_norm ?ltW // -normf_div.
by rewrite -cEx_ExInd cEx_trans_sub_RV // lt0r_neq0 // PrPF_gt0.
Qed.

Lemma Ex_cExT (X : {RV P -> R}) : `E X = `E_[X | [set: U]].
Proof.
rewrite /cEx.
under eq_bigr do rewrite setIT Pr_setT divr1 -pr_eqE.
(* The names of lemmas for Pr are inconsistent:
   some begin with "Pr" while others "pr" *)
by rewrite -Ex_comp_RV; congr `E.
Qed.

Definition cVar (X : {RV P -> R}) F :=
  let mu := `E_[X | F] in
  `E_[(X `-cst mu) `^2 | F].
Local Notation "`V_[ X | F ]" := (cVar X F).

Lemma Var_cVarT (X : {RV P -> R}) : `V X = `V_[X | [set: U]].
Proof. by rewrite /cVar -!Ex_cExT. Qed.

Lemma cvariance_ge0 (X : {RV P -> R}) F : 0 <= `V_[X | F].
Proof.
have [H|] := boolP (0 < Pr P F)%R; last first.
  rewrite -leNgt.
  have:= Pr_ge0 P F => /[conj] /andP /le_anti H.
  rewrite /cVar /cEx; apply big_ind; [by []|exact: addr_ge0|move=> i _].
  by rewrite setIC Pr_domin_setI // mulr0 mul0r.
rewrite /cVar cEx_ExInd mulr_ge0 ?invr_ge0 ?(ltW H) //.
apply/Ex_ge0=> u /=.
by rewrite mulr_ge0 ?Ind_ge0 // sq_RV_ge0.
Qed.

Lemma variance_ge0 (X : {RV P -> R}) : 0 <= `V X.
Proof. by have := cvariance_ge0 X setT; rewrite -Var_cVarT. Qed.

Lemma cEx_cVar (X : {RV P -> R}) (F G: {set U}) : 0 < Pr P F  ->
  F \subset G ->
  let mu := `E_[X | G] in
  let var := `V_[X | G] in
  `| `E_[ X | F ] - mu | <= Num.sqrt (var * Pr P G / Pr P F ).
Proof.
move=> PrPF_pos.
move=> /[dup] /(subset_Pr P) /(lt_le_trans PrPF_pos)=> PrPG_pos.
move=> FsubG /=.
set mu:= `E_[X | G].
set var:= `V_[X | G].
have EG_ge0 : 0 <= `E (((X `-cst mu) `^2) `* Ind G).
  by apply:Ex_ge0=>*; apply:mulr_ge0; [exact:sq_RV_ge0|exact:Ind_ge0].
have EF_ge0 : 0 <= `E (((X `-cst mu) `^2) `* Ind F).
  by apply:Ex_ge0=>*; apply:mulr_ge0; [exact:sq_RV_ge0|exact:Ind_ge0].
rewrite cEx_sub //.
pose y := Num.sqrt (Ex P (((X `-cst mu) `^2) `* Ind F) * Ex P (Ind F)) / Pr P F.
apply: (@le_trans _ _ y).
  rewrite ler_pM2r ?invr_gt0 // -sqrtr_sqr.
  apply: ler_wsqrtr.
  rewrite [in leLHS]I_double mul_RVA.
  apply/(le_trans (Cauchy_Schwarz_proba _ _)).
  rewrite sq_RVE -![in leLHS]mul_RVA (mul_RVC (Ind F)) -![in leLHS]mul_RVA.
  by rewrite -I_double !mul_RVA -I_square -sq_RVE le_refl.
rewrite /y /var /cVar -/mu cEx_ExInd.
rewrite -!mulrA !sqrtrM ?invr_ge0 ?(ltW PrPG_pos) //.
rewrite -[in leLHS](sqr_sqrtr (ltW PrPF_pos)) invfM !mulrA.
rewrite -!sqrtrV ?(@ltW _ _ 0) // ler_pM2r ?sqrtr_gt0 ?invr_gt0//.
rewrite E_Ind -![in leLHS]mulrA -[in leLHS]sqrtrM ?(@ltW _ _ 0) //.
rewrite mulfV ?lt0r_neq0 //.
rewrite -![in leRHS]mulrA -[in leRHS]sqrtrM ?invr_ge0 ?(@ltW _ _ 0) //.
rewrite mulVf ?lt0r_neq0 //.
rewrite !sqrtr1 !mulr1 ler_sqrt //.
apply: ler_sum=> u uU; rewrite ler_pM 1?mulr_ge0 ?sq_RV_ge0 ?Ind_ge0 //.
rewrite ler_pM ?sq_RV_ge0 ?Ind_ge0 //.
by have/Ind_subset := FsubG; apply.
Qed.

(*prove A1 and A3 for later use*)
Lemma cEx_Var (X : {RV P -> R}) F : 0 < Pr P F  ->
  `| `E_[ X | F ] - `E X | <= Num.sqrt (`V X / Pr P F ).
Proof.
move=> H; rewrite Ex_cExT Var_cVarT.
move: (@cEx_cVar X F [set: U] H) => /=.
by rewrite Pr_setT mulr1 subsetT; apply.
Qed.

Lemma cEx_cptl (X: {RV P -> R}) F:
  0 < Pr P F -> Pr P F < 1 ->
    `E_[X | F] * Pr P F + `E_[X | (~: F)] * Pr P (~: F) = `E X.
Proof.
move => PrFgt0 PrFlt1.
rewrite !cEx_ExInd.
rewrite -!mulrA [in LHS]mulVf ?lt0r_neq0 //.
rewrite mulVf ?Pr_setC ?subr_eq0 1?eq_sym ?neq_lt ?PrFlt1 // !mulr1.
rewrite /Ex -big_split /=.
apply: eq_bigr=> i _.
rewrite /Ind inE.
by case: ifP=> _ /=; rewrite mulr1 mulr0 mul0r ?addr0 ?add0r.
Qed.

Lemma cEx_Inv_int (X: {RV P -> R}) F:
0 < Pr P F -> Pr P F < 1 ->
  Pr P F * (`E_[X | F] - `E X) = Pr P (~: F) * - (`E_[X | (~: F)] - `E X).
Proof.
move => H H0.
apply/eqP; rewrite -subr_eq0.
rewrite opprD opprK !mulrDr addrAC.
rewrite opprD !mulrN opprK addrA.
rewrite !(mulrC (Pr _ _)) cEx_cptl //.
rewrite Pr_setC mulrDr mulr1 opprD mulrN opprK !addrA.
by rewrite subrr add0r subrr.
Qed.

Lemma cEx_Inv' (X: {RV P -> R}) (F G : {set U}) :
  0 < Pr P F -> F \subset G -> Pr P F < Pr P G ->
  `| `E_[X | F] - `E_[X | G]| = (Pr P (G :\: F)) / (Pr P F) * `| `E_[X | (G :\: F)] - `E_[X | G]|.
Proof.
move=> PrPF_gt0 /[dup] /setIidPr GIFF FsubG /[dup] /(lt_trans PrPF_gt0).
move=> /[dup]; rewrite lt0Pr => /invr_neq0 PrPG_neq0 PrPG_gt0 PrPF_PrPG.
have : 0 < Pr P (G :\: F) by rewrite Pr_setD subr_gt0 GIFF.
move => /[dup]; rewrite {1}lt0Pr => PrPGF_neq0 PrPGF_gt0.
rewrite !cEx_sub ?subsetDl // mulrCA.
rewrite Ind_setD // mulrAC divff// mul1r.
congr (_ / _); apply/eqP.
rewrite mul_RVBr E_sub_RV -subr_eq0 -normr_le0.
apply: le_trans; first exact: ler_dist_normD.
rewrite addrCA subrr addr0 normr_le0.
apply/eqP/normr0_eq0.
apply/(divIf PrPG_gt0).
by rewrite mul0r -cEx_sub ?lt0Pr// subrr normr0.
Qed.

(* NB: not used *)
Lemma cEx_Inv (X: {RV P -> R}) F :
  0 < Pr P F -> Pr P F < 1 ->
  `| `E_[X | F] - `E X| = (1 - Pr P F) / Pr P F * `| `E_[X | (~: F)] - `E X|.
Proof.
move=> *; rewrite Ex_cExT -Pr_setC -setTD; apply cEx_Inv' => //.
by rewrite lt_neqAle subset_Pr // andbT Pr_setT -ltPr1.
Qed.

Lemma Ind_one F : Pr P F != 0 -> `E_[Ind F : {RV P -> R} | F] = 1.
Proof.
move=> F0; rewrite cEx_ExInd.
have -> : Ind F `* Ind F = Ind F.
  by move=>*; rewrite /Ind boolp.funeqE=>? /=; case: ifPn; rewrite ?mulr0 ?mulr1.
by rewrite E_Ind mulrV // unitfE.
Qed.

Lemma cEx_add_RV (X Y : {RV (P) -> (R)}) F:
  `E_[(X `+ Y) | F] = `E_[X | F] + `E_[Y | F].
Proof.
rewrite !cEx_ExInd -mulrDl.
congr (_ * _).
rewrite -E_add_RV.
  apply congr_big => // i HiU.
  by rewrite /mul_RV mulrDl.
Qed.

Lemma cEx_sub_RV (X Y: {RV P -> R}) F: `E_[X `- Y | F] = `E_[X|F] - `E_[Y|F].
Proof.
rewrite !cEx_ExInd -mulrBl.
congr (_ * _).
by rewrite mul_RVBl E_sub_RV.
Qed.

Lemma cEx_const_RV (k : R) F:
  0 < Pr P F ->
  `E_[(const_RV P k) | F] = k.
Proof.
by move=> ?; rewrite cEx_ExInd E_scalel_RV E_Ind -mulrA mulfV ?mulr1 ?gt_eqF.
Qed.

(* NB: It is pointless to retain both `*cst (scaler_RV) and `cst* (scalel_RV)
       since R is commutative; moreover, the name scalel does not follow the
       naming scheme of mathcomp (r in scaler should stand for rings). *)
Lemma const_RC (X: {RV P -> R}) k: X `*cst k = k `cst* X.
Proof. by rewrite boolp.funeqE => ?; exact: mulrC. Qed.

Lemma cEx_scaler_RV (X : {RV (P) -> (R)}) (k : R) F:
  `E_[(X `*cst k) | F] = `E_[X | F] * k.
Proof.
rewrite !cEx_ExInd mul_RVAC mulrAC /Ex; congr (_ / _).
rewrite big_distrl /=.
by under [LHS]eq_bigr do rewrite /= mulrAC.
Qed.

Lemma cEx_scalel_RV (X : {RV (P) -> (R)}) (k : R) F:
  `E_[(k `cst* X) | F] = k * `E_[X | F].
Proof. by rewrite mulrC -cEx_scaler_RV const_RC. Qed.

Lemma cEx_trans_add_RV (X: {RV P -> R}) m F :
  0 < Pr P F -> `E_[X `+cst m | F] = `E_[X | F] + m.
Proof. by move=> ?; rewrite cEx_add_RV cEx_const_RV. Qed.

Lemma cEx_trans_RV_id_rem (X: {RV P -> R}) m F:
  `E_[(X `-cst m) `^2 | F] = `E_[((X `^2 `- ((2 * m) `cst* X)) `+cst m ^+ 2) | F].
Proof.
rewrite !cEx_ExInd; congr *%R; apply: eq_bigr => a _.
rewrite /sub_RV /trans_add_RV /trans_sub_RV /sq_RV /= /comp_RV /scalel_RV /=.
lra.
Qed.

Lemma cEx_Pr_eq0 (X: {RV P -> R}) F : Pr P F = 0 -> `E_[X | F] = 0.
Proof. by move=> PrF0; rewrite cEx_ExInd PrF0 invr0 mulr0. Qed.

Lemma cVarE (X : {RV (P) -> (R)}) F:
  `V_[X | F] = `E_[X `^2 | F] - `E_[X | F] ^+ 2.
Proof.
have: 0 <= Pr P F by apply Pr_ge0.
rewrite le_eqVlt; case/predU1P => [/esym HPr_eq0| HPr_gt0P].
  by rewrite /cVar !cEx_Pr_eq0 // expr0n /= subr0.
rewrite /cVar cEx_trans_RV_id_rem.
rewrite cEx_trans_add_RV //.
rewrite cEx_sub_RV cEx_scalel_RV !expr2.
lra.
Qed.

Lemma cVarDist (X : {RV P -> R}) F x:
  0 < Pr P F ->
  `E_[(X `-cst x) `^2 | F] = `V_[X | F] + (`E_[X | F] - x) ^+ 2.
Proof.
move=> ?.
rewrite cEx_trans_RV_id_rem cVarE cEx_add_RV cEx_sub_RV.
rewrite cEx_const_RV // cEx_scalel_RV.
lra.
Qed.

Lemma cEx_sub_eq (X : {RV P -> R}) (F G : {set U}) :
  F \subset G -> Pr P F = Pr P G -> `E_[ X | F ] = `E_[ X | G ].
Proof.
move=> ? Pr_FG_eq; apply/eqP.
rewrite -subr_eq0 -normr_eq0 distrC.
rewrite !cEx_ExInd Pr_FG_eq -mulrBl -E_sub_RV -mul_RVBr -Ind_setD //.
rewrite normrM mulf_eq0; apply/orP; left.
rewrite normr_eq0 -sqrf_eq0 -normr_le0 normrX real_normK ?num_real //.
apply: le_trans; first exact: Cauchy_Schwarz_proba.
by rewrite -I_square Ind_setD // E_sub_RV !E_Ind Pr_FG_eq subrr mulr0.
Qed.

Lemma cEx_union (X : {RV P -> R}) (F G H : {set U}) :
  F \subset G :|: H ->
  Pr P (F :&: G) + Pr P (F :&: H) = Pr P F ->
  `E_[ X | F :&: G ] * Pr P (F :&: G) + `E_[ X | F :&: H ] * Pr P (F :&: H) =
    `E_[ X | F ] * Pr P F.
Proof.
move=> FsubGUH.
have[F0|Fneq0]:= eqVneq (Pr P F) 0.
  by rewrite !Pr_domin_setI // F0 !mulr0 addr0.
have[FIG0|FIGneq0]:= eqVneq (Pr P (F :&: G)) 0.
  rewrite FIG0 mulr0 !add0r => FIHF.
  by congr (_ * _)=> //; apply: cEx_sub_eq=> //; exact: subsetIl.
have[FIH0|FIHneq0]:= eqVneq (Pr P (F :&: H)) 0.
  rewrite FIH0 mulr0 !addr0=> FIGF.
  by congr (_ * _)=> //; apply: cEx_sub_eq=> //; exact: subsetIl.
move=> FGHF.
rewrite !cExE -!mulrA !mulVf // !mulr1 -big_union_nondisj /=; last first.
  have/setIidPl/(congr1 (Pr P)):= FsubGUH.
  rewrite setIUr Pr_setU FGHF=> /eqP.
  rewrite -subr_eq0 addrAC subrr add0r oppr_eq0 => /eqP /psumr_eq0P P0.
  by rewrite big1 // => *; rewrite P0 // mulr0.
by rewrite -setIUr; have/setIidPl->:= FsubGUH.
Qed.

(* similarly to total_prob or total_prob_cond *)
Lemma total_cEx (X : {RV P -> R}) (I : finType) (E : {set U})
  (F : I -> {set U}) :
  Pr P E = \sum_(i in I) Pr P (E :&: F i) ->
  E \subset cover [set F x | x : I] ->
  `E_[ X | E ] * Pr P E =
    \sum_(i in I) `E_[ X | E :&: F i] * Pr P (E :&: F i).
Proof.
Abort.

Lemma cExID (X : {RV P -> R}) (F G : {set U}) :
  `E_[ X | F :&: G ] * Pr P (F :&: G) + `E_[ X | F :\: G ] * Pr P (F :\: G) =
    `E_[ X | F ] * Pr P F.
Proof.
rewrite setDE cEx_union ?setUCr //.
rewrite -big_union_nondisj /=; last by rewrite setICA -setIA setICr !setI0 big_set0.
by rewrite -setIUr setUCr setIT.
Qed.

End probability.
Notation "`V_[ X | F ]" := (cVar X F) : proba_scope.
Arguments Ind_one {R U P}.
Arguments cEx_sub_eq {R U P X} F G.

Section resilience.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).

Lemma cresilience (delta : R) (X : {RV P -> R}) (F G : {set U}) :
  0 < delta -> delta <= Pr P F / Pr P G -> F \subset G ->
    `| `E_[ X | F ] - `E_[ X | G ] | <=
    Num.sqrt (`V_[ X | G ] * 2 * (1 - delta) / delta).
Proof.
move => delta_gt0 delta_FG /[dup] /setIidPr HGnF_F FG.
have [Pr_FG_eq|Pr_FG_neq] := eqVneq (Pr P F) (Pr P G).
  by rewrite (cEx_sub_eq F G) // subrr normr0 sqrtr_ge0.
have FltG: Pr P F < Pr P G by rewrite lt_neqAle Pr_FG_neq subset_Pr.
have [PrF0|PrF_neq0] := eqVneq (Pr P F) 0.
  by have:= lt_le_trans delta_gt0 delta_FG; rewrite PrF0 mul0r ltxx.
have HPrFpos : 0 < Pr P F by rewrite lt_neqAle eq_sym Pr_ge0 andbT.
have [PrG0|PrG_neq0] := eqVneq (Pr P G) 0.
  by have:= subset_Pr P FG; rewrite PrG0 => /(lt_le_trans HPrFpos); rewrite ltxx.
have HPrGpos : 0 < Pr P G by rewrite lt_neqAle eq_sym Pr_ge0 andbT.
have delta_lt1 : delta < 1.
  apply/(le_lt_trans delta_FG).
  by rewrite ltr_pdivrMr // mul1r.
have/orP[]:= le_total delta (1/2) => delta_12.
(*Pr P F <= 1/2 , A.3 implies the desired result*)
  apply: (le_trans (cEx_cVar _ _ _)) => //.
  rewrite ler_wsqrtr //.
  rewrite -!mulrA; apply (ler_wpM2l (cvariance_ge0 _ _)).
  apply: (@le_trans _ _ (1 / delta)).
    rewrite ler_pdivlMr //.
    rewrite mulrC -ler_pdivlMr; last exact: divr_gt0.
    by rewrite div1r invfM invrK mulrC.
  by rewrite mulrA ler_pM2r; [lra|rewrite invr_gt0].
have delta_neq0: delta != 0 by lra.
have delta_pos: 0 < delta by lra.
have FG_pos: 0 < Pr P F / Pr P G by exact: (lt_le_trans delta_gt0 delta_FG).
rewrite cEx_Inv' //.
have PrGDF_pos: 0 < Pr P (G :\: F) by rewrite Pr_setD HGnF_F subr_gt0.
apply: le_trans.
  apply: ler_wpM2l; first by rewrite ltW // divr_gt0.
  apply cEx_cVar => //; last exact: subsetDl.
apply: (@le_trans _ _ (Num.sqrt (`V_[ X | G] * (delta^-1 - 1) / delta))).
  rewrite -[X in X * Num.sqrt _]gtr0_norm ?divr_gt0 // -sqrtr_sqr.
  rewrite -sqrtrM ?sqr_ge0 // ler_wsqrtr //.
  rewrite mulrC -!mulrA ler_wpM2l ?cvariance_ge0 //.
  rewrite mulrC exprMn !mulrA mulVf -?lt0Pr// mul1r.
  rewrite Pr_setD HGnF_F mulrDl mulNr mulfV //.
  rewrite mulrAC -mulrA -invf_div.
  apply: ler_pM.
  - by rewrite subr_ge0 -invr1 lef_pV2 ?posrE // ler_pdivrMr // mul1r subset_Pr.
  - by rewrite invr_ge0 ltW.
  - by rewrite lerD // lef_pV2.
  - by rewrite lef_pV2.
rewrite ler_wsqrtr // -!mulrA ler_wpM2l ?cvariance_ge0 //.
rewrite [X in 2 * X]mulrDl mulNr mulfV // div1r mulrC ler_wpM2r //.
  by rewrite subr_ge0 -[leLHS]invrK lef_pV2 ?posrE ?invr1 // ltW.
by rewrite -lef_pV2 ?posrE ?invr_gt0 // invrK -div1r.
Qed.

(* NB: not used, unconditional version of cresilience *)
Lemma resilience (delta : R) (X : {RV P -> R}) F :
  0 < delta -> delta <= Pr P F ->
    `| `E_[ X | F ] - `E X | <= Num.sqrt (`V X * 2 * (1 - delta) / delta).
Proof.
move=> delta_gt0 delta_F.
have := @cresilience _ X F setT delta_gt0.
rewrite Pr_setT divr1 => /(_ delta_F); rewrite -Ex_cExT -Var_cVarT.
by apply; exact/subsetT.
Qed.

End resilience.

Section robustmean.
Context {R : realType}.
Variables (U : finType) (P : R.-fdist U).

Theorem robust_mean (good drop: {set U}) (X : {RV P -> R}) (eps : R):
  let bad := ~: good in
  let mu_hat := `E_[ X | ~: drop ] in
  let mu := `E_[ X | good ] in
  let sigma := `V_[ X | good ] in
  0 < eps -> eps <= 1/8 ->
  Pr P bad = eps -> Pr P drop = 4 * eps ->
  (* All the outliers exceeding the ε-quantile are eliminated: *)
  (forall y, y \in bad -> Num.sqrt (sigma / eps) < `| X y - mu | -> y \in drop) ->
  `| mu_hat - mu | <=  8 * Num.sqrt (sigma / eps).
Proof.
move=> bad mu_hat mu sigma Hmin_outliers Hmax_outliers Hbad_ratio Hdrop_ratio
  Hquantile_drop_bad.
have H : Pr P good = 1 - eps by rewrite -Hbad_ratio -Pr_to_cplt.
(* On the other hand, we remove at most 4ε good points *)
have max_good_drop : Pr P (good :&: drop) <= 4 * eps.
  by rewrite -Hdrop_ratio; exact/subset_Pr/subsetIr.
pose eps' := Pr P (bad :\: drop) / Pr P (~: drop).
have Hcompl : Pr P (good :\: drop) / Pr P (~: drop) = 1 - eps'.
  rewrite -(setCK good) -/bad setDE setIC -setDE.
  rewrite Pr_setD setIC -setDE mulrDl mulNr mulfV //.
  by rewrite -lt0Pr Pr_setC; lra.
have eps'_ge0 : 0 <= eps' by rewrite mulr_ge0 // ?invr_ge0 Pr_ge0.
have eps'_le1 : eps' <= 1.
  rewrite ler_pdivrMr; last by rewrite Pr_setC; lra.
  by rewrite mul1r subset_Pr // subsetDr.
(* Remaining good points: 1 - (4 * eps) / (1 - eps) *)
pose delta := 1 - (4 * eps) / (1 - eps).
have min_good_remain : delta <= Pr P (good :\: drop) / Pr P good.
  rewrite /delta Pr_setD H.
  apply: (@le_trans _ _ ((1 - eps - 4 * eps) / (1 - eps))).
    rewrite ler_pdivlMr; last lra.
    by rewrite mulrDl -mulNr -(mulrA _ _^-1) mulVf //; lra.
  rewrite ler_pdivrMr; last lra.
  rewrite -[X in _ <= X]mulrA mulVf ?mulr1; lra.
have delta_gt0 : 0 < delta.
  rewrite -(@ltr_pM2r _ (1 - eps)); last lra.
  by rewrite mul0r mulrDl mul1r -mulNr -mulrA mulVf //; lra.
have delta_le1 : delta <= 1.
  rewrite -(@ler_pM2r _ (1 - eps)); last lra.
  by rewrite mul1r mulrDl mul1r -mulNr -mulrA mulVf ?mulr1 //; lra.
have Exgood_bound : `| `E_[X | good :\: drop ] - `E_[X | good] | <=
                     Num.sqrt (`V_[X | good] * 2 * (1 - delta) / delta).
  have [gdg|gdg] := eqVneq (Pr P (good :\: drop)) (Pr P good).
  - suff : `E_[X | (good :\: drop)] = `E_[X | good].
      by move=> ->; rewrite subrr normr0 sqrtr_ge0.
    by apply: cEx_sub_eq => //; exact: subsetDl.
  - apply cresilience.
    + rewrite -(@ltr_pM2r _ (1 - eps)); last lra.
      by rewrite mul0r mulr_gt0 //; lra.
    + lra.
    + exact: subsetDl.
have Exbad_bound : 0 < Pr P (bad :\: drop) ->
    `| `E_[ X | bad :\: drop ] - mu | <= Num.sqrt (sigma / eps).
  move=> Pr_bd.
  rewrite -(mulr1 mu) -(@Ind_one _ U P (bad :\: drop)); last lra.
  rewrite 2!cEx_ExInd -mulNr mulrA -(I_double P) -mulrDl big_distrr /=.
  rewrite /Ex -big_split /= [X in `|X / _|](_ : _ =
      \sum_(i in U) (X i - mu) * @Ind _ U (bad :\: drop) i * P i); last first.
    by apply: eq_bigr => u _; rewrite -mulrA mulNr -mulrBl mulrA.
  rewrite normrM (@ger0_norm _ _^-1); last by rewrite ltW // invr_gt0.
  rewrite ler_pdivrMr //; apply: (le_trans (ler_norm_sum _ _ _)).
  rewrite (bigID [pred i | i \in bad :\: drop]) /=.
  rewrite [X in _ + X]big1 ?addr0; last first.
    by move=> u /negbTE abaddrop; rewrite /Ind abaddrop mulr0 mul0r normr0.
  rewrite /Pr big_distrr /=; apply: ler_sum => i ibaddrop.
  rewrite normrM (@ger0_norm _ (P i)) // ler_wpM2r //.
  rewrite /Ind ibaddrop mulr1.
  move: ibaddrop; rewrite inE => /andP[idrop ibad].
  by rewrite leNgt -(rwP negP) => /(Hquantile_drop_bad _ ibad); exact/negP.
have max_bad_remain : Pr P (bad :\: drop) <= eps / Pr P (~: drop).
  rewrite Pr_setC Hdrop_ratio Pr_setD Hbad_ratio.
  apply: (@le_trans _ _ eps); first by rewrite lerBlDr lerDl Pr_ge0.
  by rewrite ler_pdivlMr; [nra|lra].
have Ex_not_drop : `E_[ X | ~: drop ] =
    (`E_[ X | good :\: drop ] * Pr P (good :\: drop) +
     `E_[ X | bad :\: drop ] * Pr P (bad :\: drop))
    / Pr P (~: drop).
  rewrite !setDE (setIC good) (setIC bad) /bad -setDE cExID.
  rewrite -mulrA mulfV ?mulr1 // Pr_setC.
  lra.
rewrite -(mulr1 mu).
rewrite (_ : 1 = eps' + Pr P (good :\: drop) / Pr P (~: drop)); last first.
  by rewrite Hcompl addrCA subrr addr0.
rewrite (mulrDr mu) opprD.
rewrite /mu_hat Ex_not_drop mulrDl.
rewrite -(mulrA `E_[X | _]) -/eps'.
rewrite Hcompl.
rewrite -(mulrA `E_[X | _]).
rewrite -addrA addrC addrA -!mulNr -(mulrDl _ _ eps').
rewrite -addrA -mulrDl.
rewrite (addrC (-mu)).
rewrite (le_trans (ler_normD _ _)) //.
rewrite (normrM _ eps') (@ger0_norm _ eps'); last lra.
rewrite normrM.
rewrite mulNr -/eps' (@ger0_norm _ (1 - eps')); last lra.
apply: (@le_trans _ _ (Num.sqrt (`V_[ X | good] / eps) * eps' +
    Num.sqrt (`V_[ X | good] * 2 * (1 - delta) / delta) * (1 - eps'))).
  have [->|/eqP eps'0] := eqVneq eps' 0.
    by rewrite !(mulr0,add0r,subr0,mulr1).
  have [->|/eqP eps'1] := eqVneq eps' 1.
    rewrite !(subrr, mulr0, addr0, mulr1); apply: Exbad_bound.
    rewrite lt0Pr; apply: contra_notN eps'0 => /eqP.
    by rewrite /eps' => ->; rewrite mul0r.
  have [bd0|bd0] := eqVneq (Pr P (bad :\: drop)) 0.
    by exfalso; apply/eps'0; rewrite /eps' bd0 mul0r.
  apply: lerD; (rewrite ler_pM2r; last lra).
  - by apply: Exbad_bound; rewrite lt0Pr.
  - exact: Exgood_bound.
rewrite /sigma !sqrtrM //; last 4 first.
  - exact: cvariance_ge0.
  - by apply: mulr_ge0; [exact: cvariance_ge0|lra].
  - apply: mulr_ge0; [|lra].
    by apply: mulr_ge0; [exact: cvariance_ge0|lra].
  - exact: cvariance_ge0.
rewrite addrCA subrr addr0.
rewrite -(mulr_natl _ 8) -!mulrA -mulrDr mul1r.
rewrite -!(mulrCA (Num.sqrt `V_[ X | good])).
apply: ler_wpM2l; first exact: sqrtr_ge0.
rewrite mulrA -sqrtrM; [|lra].
rewrite mulrA -sqrtrM; [|lra].
rewrite addrC -lerBrDr (mulrC 8) -mulrBr.
rewrite -(@ger0_norm _ (1 - eps')) -?sqrtr_sqr; last lra.
rewrite -(@ger0_norm _ (8 - eps')) -?sqrtr_sqr; last lra.
rewrite [leLHS]mulrC [leRHS]mulrC.
rewrite -sqrtrM ?sqr_ge0 //.
rewrite -sqrtrM ?sqr_ge0 //.
rewrite ler_sqrt 1?mulr_ge0 ?sqr_ge0 ?invr_ge0 //; last by rewrite ltW.
apply: ler_pM.
- exact: sqr_ge0.
- by rewrite !mulr_ge0 ?invr_ge0 //; lra.
- rewrite ler_sqr ?nnegrE; lra.
- rewrite -[leRHS]mulr1 ler_pdivlMl; last lra.
  rewrite [leLHS](_ : _ = 8 * eps * eps / (1 - 5 * eps)); last first.
    rewrite /delta; field; apply/andP; split; lra.
  rewrite ler_pdivrMr; last lra.
  rewrite mul1r (@le_trans _ _ eps) //; last lra.
  by rewrite ler_piMl //; lra.
Qed.

End robustmean.
