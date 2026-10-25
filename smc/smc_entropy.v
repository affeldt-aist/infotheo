From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import mathcomp_extra contra Rstruct ring reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_proba.

(**md**************************************************************************)
(* # SMC Proofs in entropy                                                    *)
(*                                                                            *)
(*     From: Information-theoretically Secure Number-product Protocol         *)
(*     SHEN, Chih-Hao, et al. In: 2007 International Conference on Machine    *)
(*     Learning and Cybernetics. IEEE, 2007. p. 3006-3011.                    *)
(*                                                                            *)
(*                                                                            *)
(* |   Definitions     |    | Meaning                                        |*)
(* |-------------------|----|------------------------------------------------|*)
(* |    x \*d y        | == | dot product of two random vectors.             |*)
(* | scalar_product    | == | The deterministic version of                   |*)
(* |                   |    | SMC scalar product protocol as a function.     |*)
(* | is_scalar_product | == | The correctness of the SMC scalar product      |*)
(* |                   |    | results                                        |*)
(* |-------------------------------------------------------------------------|*)
(*                                                                            *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(* ```                                                                        *)
(*   pi2_bob_is_leakage_free_proof   == the proof shows that Bob's knowledge  *)
(*                                      of Alice's secret input x1 does not   *)
(*                                      increase by accessing random          *)
(*                                      variables received during the         *)
(*                                      protocols execution                   *)
(*   pi2_alice_is_leakage_free_proof == the proof shows that Alice's          *)
(*                                      knowledge of Bob's secret input x2    *)
(*                                      does not increase by accessing random *)
(*                                      variables received during the         *)
(*                                      protocols execution                   *)
(*   cpr_centropy                    == given a conditional probability       *)
(*                                      removal lemma P(X|(Y, Z))->P(X | Y),  *)
(*                                      shows that with some conditions met,  *)
(*                                      there exists a conditional entropy    *)
(*                                      removal lemma H(X | (Y, Z))->H(X | Y) *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

Reserved Notation "u *d w" (at level 40).
Reserved Notation "u \*d w" (at level 40).

Module smc_entropy_proofs.

Section extra_pr.
Context {R : realType}.
Variables (T TX TY : finType) (TX' : finType).
Variable P : R.-fdist T.
Variable n : nat.

Lemma pr_eq_diag (U : eqType) (X : {RV P -> U}) (x : U) :
  `Pr[ [% X, X] = (x, x) ] = `Pr[ X = x ].
Proof.
by rewrite !pfwd1E /Pr; apply: eq_bigl=> a; rewrite !inE xpair_eqE andbb.
(* After unfolding Pr use eq_bigl to focus on the preim and pred,
   use inE to keep only the pred and as booleaning expression,
   use xpair_eqE to separate the RV2 to two conditions,
   and show LHS and RHS will be only true.
*)
Qed.

Lemma cpr_eq_id (U : eqType) (X : {RV P -> U}) (x : U) :
  `Pr[ X = x ] != 0 -> `Pr[ X = x | X = x ] = 1.
Proof. by move=> ?; rewrite cpr_eqE pr_eq_diag divff. Qed.

End extra_pr.

(* NOT USED, and easy to solve by contra
Section extra_pr2.

Variables (T : finType) (TX TY TZ : eqType).
Variable P : R.-fdist T.

Lemma fst_RV2_neq0 (X : {RV P -> TX}) (Y : {RV P -> TY}) x y:
  `Pr[[%X, Y] = (x, y)] != 0 -> `Pr[ X = x] != 0.
Proof. by contra; exact: pr_eq_domin_RV2. Qed.

End extra_pr2.
*)

Section inde_RV.
Context {R : realType}.

Lemma dist_inde_rv_prod (T TX TY : finType) (P : R.-fdist T)
  (X : {RV P -> TX}) (Y : {RV P -> TY}) :
  P |= X _|_ Y -> `p_ [% X, Y] = `p_ X `x `p_ Y.
Proof.
move=> iXY.
apply: fdist_ext => -[x y] /=.
by rewrite fdist_prodE/= !dist_of_RVE iXY.
Qed.

End inde_RV.

Section cpr_centropy1_RV.
Context {R : realType}.
Variables (T TY1 TY2 : finType) (TY3 : finType) (P : R.-fdist T).
Variables (Y1 : {RV P -> TY1}) (Y2 : {RV P -> TY2}) (Y3 : {RV P -> TY3}).

Let reduce_inde23_to_inde123 y1 y2 y3 :
  `Pr[ [% Y2, Y3] = (y2, y3) ] != 0 ->
  P |= [%Y1, Y2] _|_ Y3 ->
  `Pr[Y1 = y1 | Y2 = y2] = `Pr[Y1 = y1 | [%Y2, Y3] = (y2, y3)].
Proof.
move=> Y23neq0.
have Y2neq0 : `Pr[Y2 = y2] != 0.
  move: Y23neq0.
  contra=> ?.
  exact: pfwd1_domin_RV2.
have Y3neq0 : `Pr[Y3 = y3] != 0.
  move: Y23neq0.
  contra=> ?.
  exact: pfwd1_domin_RV1.
move=> inde123.
have inde23 : P |= Y2 _|_ Y3.
  change Y2 with (snd \o [%Y1, Y2]).
  change Y3 with (idfun \o Y3).
  exact: inde_RV_comp.
rewrite !cpr_eqE pfwd1_pairA inde123 inde23.
field.
(* For a CI-only issue:

   Nix CI for bundle 9.1-mcmaster / mathcomp-infotheo (pull_request_target).
   https://github.com/affeldt-aist/infotheo/actions/runs/19418672975/job/55551870245

   From error logs, goals after `field`:

   Local:  (`Pr[ Y3 = y3 ] != 0) && (`Pr[ Y2 = y2 ] != 0)
   CI: goal 1: `Pr[ Y3 = y3 ] != 0 goal 2: `Pr[ Y2 = y2 ] != 0

   So here use `try` and `?` to workaround the issue.
*)
try (apply/andP; split).
by rewrite ?Y2neq0 ?Y3neq0.
by rewrite ?Y2neq0 ?Y3neq0.
Qed.

Lemma cpr_centropy1_RV y2 y3 :
  (forall y1, `Pr[Y1 = y1 | Y2 = y2] = `Pr[Y1 = y1 | [%Y2, Y3] = (y2, y3)]) ->
  `H[ Y1 | Y2 = y2 ] = `H[ Y1 | [% Y2, Y3] = (y2, y3) ].
Proof.
move=> H.
rewrite /centropy1_RV /centropy1.
congr -%R.
apply: eq_bigr => a _.
by rewrite 2!jcPrE -2!cpr_inE' 2!cpr_in1 H.
Qed.

End cpr_centropy1_RV.

Section cpr_cond_entropy_proof.
Context {R : realType}.
Variables (T TY1 TY2 TY3 : finType) (P : R.-fdist T).
Variables (Y1 : {RV P -> TY1}) (Y2 : {RV P -> TY2}) (Y3 : {RV P -> TY3}).

Lemma cpr_cond_entropy_old : P |= Y2 _|_ Y3 ->
  (forall y1 y2 y3, `Pr[ [% Y2, Y3] = (y2, y3) ] != 0 ->
     `Pr[ Y1 = y1 | [% Y2, Y3] = (y2, y3) ] = `Pr[ Y1 = y1 | Y2 = y2 ]) ->
  `H( Y1 | [% Y2, Y3]) = `H( Y1 | Y2).
Proof.
move=> Hinde Hremoval.
rewrite centropy_RVE'/=.
pose f y2 y3 := `Pr[Y2 = y2] * `Pr[Y3 = y3] * `H[Y1 | Y2 = y2].
transitivity (\sum_a f a.1 a.2).
  apply eq_bigr => a _.
  have [Ha|Ha] := eqVneq (`Pr[Y2 = a.1] * `Pr[Y3 = a.2]) 0.
    by rewrite /f Ha mul0r [in X in X * _](surjective_pairing a) Hinde Ha mul0r.
  rewrite /f [in X in X * _](surjective_pairing a) Hinde; congr (_ * _ * _).
  have [Hy3|Hy3] := eqVneq `Pr[Y3 = a.2] 0.
    by rewrite Hy3 mulr0 eqxx in Ha.
  rewrite [in LHS](surjective_pairing a).
  apply/esym/cpr_centropy1_RV => y1.
  by rewrite Hremoval// Hinde.
rewrite -pair_bigA /=; apply: eq_bigr => y2 _.
rewrite snd_RV2 dist_of_RVE -/(`H[_ | _ = _]).
by rewrite -big_distrl/= -big_distrr/= sum_pfwd1 mulr1.
Qed.

Section centropyf.
Variables (TY4 : finType) (Y4 : {RV P -> TY4}) (f : TY4 -> TY2).

Lemma cpr_centropy1_RV' y4 :
  (forall y1, `Pr[Y1 = y1 | Y4 = y4] = `Pr[Y1 = y1 | (f `o Y4) = f y4]) ->
  `H[ Y1 | Y4 = y4 ] = `H[ Y1 | (f `o Y4) = f y4 ].
Proof.
move=> H.
rewrite /centropy1_RV /centropy1.
congr -%R.
apply: eq_bigr => a _.
by rewrite 2!jcPrE -2!cpr_inE' 2!cpr_in1 H.
Qed.

Lemma cpr_centropy' :
  (forall y1 y4, `Pr[ Y4 = y4 ] != 0 ->
     `Pr[ Y1 = y1 | Y4 = y4 ] = `Pr[ Y1 = y1 | (f `o Y4) = f y4 ]) ->
  `H( Y1 | Y4 ) = `H( Y1 | f `o Y4 ).
Proof.
move=> Hremoval.
rewrite 2!centropy_RVE'/=.
rewrite (partition_big f xpredT) //=.
apply: eq_bigr => y3 _.
transitivity (\sum_(i | f i == y3) `Pr[ Y4 = i ] * `H[ Y1 | (f `o Y4) = y3 ]).
  apply: eq_bigr => y4 /eqP y4y3.
  have [->|] := eqVneq (`Pr[Y4=y4]) 0.
    by rewrite !mul0r.
  move/Hremoval => H.
  by rewrite  -y4y3 cpr_centropy1_RV'.
rewrite -big_distrl /=.
congr (_ * _).
rewrite pfwd1E /Pr.
under eq_bigr do rewrite pfwd1E /Pr.
rewrite (partition_big Y4 (fun y4 => f y4 == y3)) //=.
  apply eq_bigr => y4 y4y3.
  apply eq_bigl => a /=.
  rewrite !inE.
  have [ay4|] := eqVneq (Y4 a) y4.
    by rewrite /comp_RV ay4 y4y3.
  by rewrite andbF.
by move=> a; rewrite !inE.
Qed.

End centropyf.

Lemma cpr_centropy :
  (forall y1 y2 y3, `Pr[ [% Y2, Y3] = (y2, y3) ] != 0 ->
     `Pr[ Y1 = y1 | [% Y2, Y3] = (y2, y3) ] = `Pr[ Y1 = y1 | Y2 = y2 ]) ->
  `H( Y1 | [% Y2, Y3]) = `H( Y1 | Y2).
Proof.
move=> H.
apply: (cpr_centropy' (f:=fst)).
move=> y1 [y2 y3].
exact: H.
Qed.

End cpr_cond_entropy_proof.

Section cinde_RV_comp_removal.
Context {R : realType}.
Variables (T : finType) (TX TY TZ TO : finType) (x : TX) (y : TY) (z : TZ).
Variables (P : R.-fdist T) (X : {RV P -> TX}) (Y : {RV P -> TY})
  (Z : {RV P -> TZ})(O : {RV P -> TO}).
Variables (fy : TO -> TY)(fz : TO -> TZ).

Hypothesis XYZ_cinde : X _|_ (fy `o O) | (fz `o O).
Hypothesis YZneq0 : `Pr[ [% fy `o O, fz `o O] = (y, z) ] != 0.

Lemma cinde_rv_comp_removal:
   `Pr[ X = x | (fz `o O) = z ] = `Pr[ X = x | [% fy `o O, fz `o O ] = (y, z) ].
Proof.
have H := cinde_alt x (b:=y) (c:=z) XYZ_cinde YZneq0.
exact/esym/H.
Qed.

End cinde_RV_comp_removal.

Section inde_ex.
Context {R : realType}.
Variables (A : finType) (m n : nat)(P : R.-fdist A).
Variables (TX1 TX2 TX3 : finType).
Variables (s1 : {RV P -> TX1}) (s2 : {RV P -> TX2}) (r: {RV P -> TX3}).
Variable op : TX1 -> TX2 -> TX3.

Let rv_op (rv1 : {RV P -> TX1}) (rv2 : {RV P -> TX2}) : {RV P -> TX3}  :=
  fun p => op (rv1 p)(rv2 p).

Hypothesis s1_s2_indep : P|= s1 _|_ s2.
Hypothesis s1s2_r_indep : P|= [%s1, s2] _|_ r.

Lemma pr_eqM x : `Pr[ (rv_op s1 s2) = x ] =
  \sum_(a <- fin_img s1)
    (\sum_(b <- fin_img s2 | op a b == x) `Pr[ s1 = a ] * `Pr[ s2 = b]).
Proof.
rewrite -[LHS]pr_in1.
rewrite (reasoning_by_cases _ s1).
apply: eq_bigr => a _.
rewrite (reasoning_by_cases _ s2).
rewrite [RHS]big_mkcond /=.
apply eq_bigr => b _.
case: ifPn => [/eqP <-|Hneq].
  rewrite -s1_s2_indep.
  rewrite 2!setX1.
  rewrite pr_in1.
  pose f (p : TX1 * TX2) := (op p.1 p.2, p.1, p.2).
  have f_inj : injective f by move => [x1 x2] [? ?] [] _ -> ->.
  by rewrite -(pfwd1_comp _ _ f_inj).
rewrite 2!setX1.
rewrite pr_in1.
rewrite pfwd1_eq0//.
apply: contra Hneq.
by rewrite fin_img_imset => /imsetP[a0 _ [] -> -> ->].
Qed.

Lemma pr_eqM2 x y : `Pr[ [%(rv_op s1 s2), r] = (x, y) ] =
  \sum_(a <- fin_img s1)
    (\sum_(b <- fin_img s2 | op a b == x)
      `Pr[ s1 = a ] * `Pr[ s2 = b ] * `Pr[ r = y ]).
Proof.
rewrite -[LHS]pr_in1.
rewrite (reasoning_by_cases _ s1).
apply eq_bigr => a _.
rewrite (reasoning_by_cases _ s2).
rewrite [RHS]big_mkcond /=.
apply eq_bigr => b _.
case: ifPn => [/eqP <-|Hneq].
  rewrite -s1_s2_indep -s1s2_r_indep.
  rewrite setX1 setX1.
  rewrite pr_in1.
  pose f (p:TX1 * TX2 * TX3) := (op p.1.1 p.1.2, p.2, p.1.1, p.1.2).
  have f_inj : injective f.
     by move => [[x1 x2] ?] [[? ?] ?] [] _ -> -> -> /=.
  by rewrite -(pfwd1_comp _ _ f_inj ).
rewrite 2!setX1.
rewrite pr_in1.
rewrite pfwd1_eq0//.
apply: contra Hneq.
by rewrite fin_img_imset => /imsetP[a0 _ [] -> _ -> ->].
Qed.

Lemma s1Ms2_r_indep : P |= (rv_op s1 s2) _|_ r.
Proof.
rewrite /inde_RV  => x y.
rewrite pr_eqM pr_eqM2.
rewrite big_distrl /=.
apply eq_bigr => a _.
rewrite big_distrl /=.
by apply eq_bigr => b _.
Qed.

(* TODO: addition lemma; actually we didn't use anything about mul above
  (any binop works) *)
(* reasoning_by_cases depends on another lemma that is not general before
  (2024/12/05) -- these proof are not trivial actually. *)

End inde_ex.

Arguments s1Ms2_r_indep [_ _ _ _ _ _] s1 s2 r.

Section neg_RV_lemmas.
Context {R : realType}.
Variables (T : finType) (m n: nat) (P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].
Hypothesis card_TX : #|TX| = m.+2.

Lemma sub_RV_eq (U : finZmodType) (X Y : {RV P -> U}):
  X \- Y = X \+ neg_RV Y.
Proof.
apply: boolp.funext=> i.
rewrite /neg_RV .
rewrite /=. (* from null_fun to 0 *)
by rewrite sub0r.
Qed.

Lemma neg_RV_dist_eq (X : {RV P -> TX}):
  `p_ X = fdist_uniform card_TX ->
  `p_ X = `p_ (neg_RV X).
Proof.
rewrite /dist_of_RV=> Hunif.
apply/val_inj/ffunP => x /=. (* these two steps eq to apply: fdist_ext.*)
rewrite [RHS](_: _ = fdistmap X P (-x)).
  by rewrite !Hunif !fdist_uniformE.
rewrite /fdistmap !fdistbindE.
apply: eq_bigr=> a ?.
by rewrite /neg_RV !fdist1E /= sub0r eqr_oppLR.
Qed.

Lemma neg_RV_inde_eq (U : finType) (V : finZmodType) (X : {RV P -> U})
    (Y : {RV P -> V}):
  P |= X _|_ Y ->
  P |= X _|_ neg_RV Y.
Proof.
move => H.
have ->: X = idfun `o X by [].
have ->: neg_RV Y = (fun y: V => 0 - y ) `o Y.
  exact: boolp.funext => ? //=.
apply: inde_RV_comp.
exact: H.
Qed.

End neg_RV_lemmas.

Section dotproduct.
Context {R : realType}.
Variables (TX : ringType) (n : nat) (T : finType).

Definition dotproduct (a b : 'rV[TX]_n) := (a *m b^T)``_ord0.

Definition dotproduct_rv
  (P: R.-fdist T) (A B: {RV P -> 'rV[TX]_n}) : {RV P -> TX} :=
  fun p => dotproduct (A p) (B p).

End dotproduct.

Notation "u *d w" := (dotproduct u w).
Notation "u \*d w" := (dotproduct_rv u w).

Arguments dotproduct {TX n}.

Section unif_lemmas.
Context {R : realType}.
Variables (T : finType) (m n : nat) (P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].
Variables (s1 s2: {RV P -> 'rV[TX]_n})(r: {RV P -> TX}).

Hypothesis card_TX : #|TX| = m.+2.
Hypothesis pr_unif : `p_ r = fdist_uniform card_TX.
Hypothesis s1_s2_indep : P|= s1 _|_ s2.
Hypothesis s1s2_r_indep : P|= [%s1, s2] _|_ r.

Lemma ps1_dot_s2_r_unif:
  @dist_of_RV _ T P TX (s1 \*d s2 \- r) = fdist_uniform card_TX.
Proof.
have ->: s1 \*d s2 \- r = s1 \*d s2 \+ (neg_RV r).
  by apply: boolp.funext=> ?; rewrite /neg_RV /= sub0r.
have Hnegr1unif: `p_ (neg_RV r) = fdist_uniform card_TX.
  have Ha := neg_RV_dist_eq pr_unif.
  symmetry in Ha.
  rewrite Ha.
  by rewrite pr_unif.
apply: add_RV_unif; first by rewrite -neg_RV_dist_eq.
apply: s1Ms2_r_indep; first by [].
exact: neg_RV_inde_eq.
Qed.

End unif_lemmas.

Section pi2.

Section scalar_product_def.
Context {R : realType}.
Variables (T : finType) (m n: nat) (P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].

Definition SMC := 'rV[TX]_n -> 'rV[TX]_n -> (TX * TX).

Definition is_scalar_product (sp : SMC) :=
  forall (xa xb: 'rV[TX]_n),
  (sp xa xb).1 + (sp xa xb).2 = xa *d xb.

Definition step_eqn2_ya :
  ('rV[TX]_n * 'rV[TX]_n * TX * 'rV[TX]_n * TX) -> TX := fun z =>
  let '(xa, sa, ra, xb', t) := z in t - (xb' *d sa) + ra.

Definition step_eqn3_t_with_offset :
  ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX * TX) -> TX := fun z =>
  let '(xa, xb, sa, sb, ra, rb) := z in (xa + sa) *d xb + rb.

Definition scalar_product
  (sa sb : 'rV[TX]_n) (ra yb : TX) (xa xb : 'rV[TX]_n) : (TX * TX) :=
  let xa' := xa + sa in (* Alice -> Bob *)
  let xb' := xb + sb in (* Bob -> Alice *)
  let rb := sa *d sb - ra in (* Commodity -> Bob *)
  let t_with_offset := step_eqn3_t_with_offset (xa, xb, sa, sb, ra, rb) in
  let t :=  t_with_offset - yb in (* Bob -> Alice *)
  let ya := step_eqn2_ya (xa, sa, ra, xb', t) in
  (ya, yb).

Lemma dot_productC (aa bb : 'rV[TX]_n) : aa *d bb = bb *d aa.
Proof.
rewrite /dotproduct.
rewrite !mxE.
apply: eq_bigr=> *.
by rewrite !mxE mulrC.
Qed.

Lemma dot_productDr (aa bb cc : 'rV[TX]_n) :
  aa *d (bb + cc) = aa *d bb + aa *d cc.
Proof.
rewrite /dotproduct !mxE.
rewrite -big_split /=.
apply: eq_bigr=> *.
by rewrite !mxE mulrDr.
Qed.

(* xb *d (xa + sa) + (sa *d sb - ra) - yb - (xb + sb) *d sa + ra + yb =
   xa *d xb *)
Lemma scalar_product_correct (sa sb : 'rV[TX]_n) (ra yb : TX) :
  is_scalar_product (scalar_product sa sb ra yb).
Proof.
move=>/=xa xb/=.
rewrite (dot_productC (xa+sa) xb).
rewrite !dot_productDr.
rewrite dot_productC.
rewrite (dot_productC xb sa).
rewrite (dot_productC (xb+sb) sa).
rewrite dot_productDr.
ring.
Qed.
(*rewrite (@GRing.add R).[AC(2*2)(1*4*(3*2))].*)

End scalar_product_def.

Section eqn2_proof.
Context {R : realType}.
Variables (T : finType) (m n : nat) (P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].
Variables (r1 r2 y2 : {RV P -> TX}) (x1 x2 s1 s2 : {RV P -> 'rV[TX]_n}).
Let x1' := x1 \+ s1.
Let x2' := x2 \+ s2.
Let t := x1' \*d x2 \+ r2 \- y2.
Let y1 := t \- x2' \*d s1 \+ r1.

Let f: ('rV[TX]_n * 'rV[TX]_n * TX * 'rV[TX]_n * TX) -> TX := fun z =>
  let '(xa, sa, ra, xb', t) := z in t - (xb' *d sa) + ra.

Let y1_fcomp : y1 = f `o [%x1, s1, r1, x2', t].
Proof. exact: boolp.funext. Qed.

Lemma eqn2_proof:
  `H(x2|[%[%x1, s1, r1, x2', t], y1]) = `H(x2|[%x1, s1, r1, x2', t]).
Proof. by rewrite y1_fcomp; exact: centropy_RV_contraction. Qed.

End eqn2_proof.

Section eqn3_proof.
Context {R : realType}.
Variables (T : finType) (m n : nat) (P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].

Variables (r1 r2 y2 : {RV P -> TX}) (x1 x2 s1 s2 : {RV P -> 'rV[TX]_n}).
Let x1' := x1 \+ s1.
Let x2' := x2 \+ s2.
Let t := x1' \*d x2 \+ r2 \- y2.
Let y1 := t \- x2' \*d s1 \+ r1.

(* Selected variables from scalar-product only for eqn3.
   Each equation has a such "focus" from all variables in the scalar-product.
*)
Let O := [%x1, x2, s1, s2, r1, r2].

(* f1 `o X in mc_removal_pr must be x2 in eq3 *)
Let f1 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX * TX) ->
  'rV[TX]_n := fun z =>
  let '(x1, x2, s1, s2, r1, r2) := z in x2.

(* f2 `o X in mc_removal_pr must be (x1, s1, r1, x2 + s2) in eq3 *)
Let f2 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX * TX) ->
  ('rV[TX]_n * 'rV[TX]_n * TX * 'rV[TX]_n) := fun z =>
  let '(x1, x2, s1, s2, r1, r2) := z in (x1, s1, r1, x2 + s2).

Definition fm : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX * TX) ->
  TX := fun z =>
  let '(xa, xb, sa, sb, ra, rb) := z in (xa + sa) *d xb + rb.

(* in mc_removal_pr they are named as Y1 Y2 Ym but we already have Y
   so renaming them. *)
Let Z := neg_RV y2.
(* x2; It is okay in Alice's view to have it because only used in condition. *)
Let W1 := f1 `o O.
(* [%x1, s1, r1, x2']; cannot have x2, s2, r2 otherwise Alice knows the secret*)
Let W2 := f2 `o O.
Let Wm := fm `o O.  (* t-(neg_RV y2); t before it addes (neg_RV y2) in WmZ*)
Let WmZ := Wm `+ neg_RV y2. (* t *)

Let eq_W1_RV : f1 `o O = x2.
Proof. exact: boolp.funext. Qed.

Let eq_W2_RV : f2 `o O = [%x1, s1, r1, x2'].
Proof. exact: boolp.funext. Qed.

Let eq_Wm_RV : fm `o O = (x1 \+ s1) \*d x2 \+ r2.
Proof. exact: boolp.funext. Qed.

Let eq_WmZ_RV : fm `o O `+ (neg_RV y2) = t.
Proof.
rewrite /t /add_RV /neg_RV eq_Wm_RV /x1' /=.
apply: boolp.funext => a /=.
by rewrite sub0r.
Qed.

(* Because y2 is generated by Bob -- not related to any other variables. *)
Hypothesis Z_O_indep : P |= Z _|_ O.
Hypothesis card_TX : #|TX| = m.+2.

(* Assumption in the paper. *)
Hypothesis pZ_unif : `p_ Z = fdist_uniform card_TX.

Let Z_OO_indep : P |= Z _|_ [% O, O].
Proof.
have -> : [%O, O] = (fun o => (o, o)) `o O by [].
have -> : Z = idfun `o Z by [].
exact: inde_RV_comp.
Qed.

Let Z_WmW2_indep : P |= Z _|_ [%Wm, W2].
Proof.
rewrite /Wm /W2.
rewrite (_ : Z = idfun `o Z) //.
apply: inde_RV2_comp.
exact: Z_OO_indep.
Qed.

Let Z_W2_indep : P |= Z _|_ W2.
Proof.
rewrite (_ : Z = idfun `o Z) //.
apply: inde_RV_comp.
exact: Z_O_indep.
Qed.

Let Z_Wm_indep : P |= Z _|_ Wm.
Proof.
rewrite /Wm.
rewrite (_ : Z = idfun `o Z) //.
apply: inde_RV_comp.
exact: Z_O_indep.
Qed.

Let W2_WmZ_indep : P |= W2 _|_ WmZ.
Proof.
rewrite cinde_RV_unit.
apply: cinde_RV_sym.
rewrite -cinde_RV_unit.
rewrite /inde_RV/=.
rewrite /WmZ.
exact: (lemma_3_5' Z_WmW2_indep pZ_unif).
Qed.

Let pWmZ_unif : `p_ (Wm `+ neg_RV y2) = fdist_uniform card_TX.
Proof.
have H_ZWM := Z_Wm_indep.
rewrite inde_RV_sym in H_ZWM.
exact: (add_RV_unif Wm Z card_TX pZ_unif H_ZWM).
Qed.

Lemma eqn3_proof : `H(x2|[%x1, s1, r1, x2', t]) = `H(x2|[%x1, s1, r1, x2']).
Proof.
rewrite -eq_W1_RV -eq_W2_RV -eq_WmZ_RV eq_Wm_RV.
have Ha := cpr_centropy (Y2:=W2) (Y3:=WmZ).
apply Ha => w w2 wmz Hneq0.
exact: (mc_removal_pr f1 Z_O_indep pZ_unif w Hneq0).
Qed.

End eqn3_proof.

Section eqn4_proof.
Context {R : realType}.
Variables (T : finType) (m n: nat) (P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].
Hypothesis card_rVTX : #|'rV[TX]_n| = (m.+2 ^ n).-1.+1.
(* Coq cannot unify `(m.+2^n).-1.+1` in the definition of
   fdist_uniform and `(m.+2^n)%nat`,
   so we cannot assume `(m.+2^n)` here.

   Check fdist_uniform (n:=(m.+2^n).-1) card_rVTX.
*)

Variables (r1 : {RV P -> TX}) (x1 x2 s1 s2 : {RV P -> 'rV[TX]_n}).
Let x2' := x2 \+ s2.

Let eqn4 := `H(x2|[%x1, s1, r1, x2']) = `H(x2|[%x1, s1, r1]).

Let O := [%x1, s1, r1, x2].
Let Z := s2.
(* Assumption in the paper. *)
Hypothesis pZ_unif : `p_ Z = fdist_uniform card_rVTX. 

Let W1 := snd `o O.   (* x2 *)
Let W2 := fst `o O.   (* [%x1, s1, r1] *)
Let Wm := snd `o O.   (* x2 *)
Let WmZ := Wm `+ s2. (* x2' = x2 + s2 *)

Variable Z_O_indep : P |= Z _|_ O.

Let Z_OO_indep : P |= Z _|_ [% O, O].
Proof.
have -> : [%O, O] = (fun o => (o, o)) `o O by [].
have -> : Z = idfun `o Z by [].
exact: inde_RV_comp.
Qed.

Let Z_WmW2_indep : P |= Z _|_ [%Wm, W2].
Proof.
rewrite /Wm /W2.
rewrite (_ : Z = idfun `o Z) //.
apply: inde_RV2_comp.
exact: Z_OO_indep.
Qed.

Let Z_Wm_indep : P |= Z _|_ Wm.
Proof.
rewrite /Wm.
rewrite (_ : Z = idfun `o Z) //. (* id vs. idfun*)
apply: inde_RV_comp.
exact: Z_O_indep.
Qed.

Let pWmZ_unif : (@dist_of_RV _ T P 'rV[TX]_n WmZ) = fdist_uniform card_rVTX.
Proof.
rewrite /WmZ.
have H_ZWM := Z_Wm_indep.
rewrite inde_RV_sym in H_ZWM.
exact: (add_RV_unif Wm Z card_rVTX pZ_unif H_ZWM).
Qed.

Let W2_WmZ_indep : P |= W2 _|_ WmZ.
Proof.
rewrite cinde_RV_unit.
apply: cinde_RV_sym.
rewrite -cinde_RV_unit.
rewrite /inde_RV/=.
rewrite /WmZ.
exact: (lemma_3_5' Z_WmW2_indep (n:=(m.+2 ^ n).-1) pZ_unif).
Qed.

Lemma eqn4_proof: eqn4.
Proof.
rewrite /eqn4.
have Ha := cpr_centropy (Y2:=W2) (Y3:=WmZ) _.
apply Ha => w w2 wmz Hneq0.
simpl in *.
exact: (mc_removal_pr snd Z_O_indep pZ_unif w Hneq0).
Qed.

End eqn4_proof.

Section eqn4_1_proof.
Context {R : realType}.
Variables (T : finType) (m n : nat) (P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].
Variables (r1 : {RV P -> TX}) (x1 x2 s1 : {RV P -> 'rV[TX]_n}).

Hypothesis x2_indep : P |= [% x1, s1, r1] _|_ x2.

Lemma eqn_4_1_proof : `H(x2 | [%x1, s1, r1]) = `H `p_ x2.
Proof.
transitivity (`H([%x1, s1, r1], x2) - `H([%x1, s1], r1)).
  by rewrite chain_rule_RV addrAC subrr add0r.
rewrite inde_RV_joint_entropyE.
  by rewrite addrAC subrr add0r.
exact: x2_indep.
Qed.

End eqn4_1_proof.

Section pi2_alice_is_leakage_free_proof.
Context {R : realType}.
Variables (T : finType) (m n : nat) (P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].
Variables (r1 y2 : {RV P -> TX}) (x1 x2 s1 s2 : {RV P -> 'rV[TX]_n}).
Let x1' := x1 \+ s1.
Let x2' := x2 \+ s2.
Let r2  := s1 \*d s2 \- r1.
Let t := x1' \*d x2 \+ r2 \- y2.
Let y1 := t \- x2' \*d s1 \+ r1.
Let AliceView := [%x1, s1, r1, x2', t, y1].

Hypothesis y2_x1x2s1s2r1_eqn3_indep : P |= y2 _|_ [%x1, x2, s1, s2, r1].
Hypothesis eqn4_indep : P |= s2 _|_ [%x1, s1, r1, x2].
Hypothesis x1s2r1_x2_indep: P |= [% x1, s1, r1] _|_ x2.
Hypothesis card_TX : #|TX| = m.+2.
Hypothesis neg_py2_unif : `p_ (neg_RV y2) = fdist_uniform card_TX.
Hypothesis card_rVTX : #|'rV[TX]_n| = (m.+2 ^ n).-1.+1.
Hypothesis ps2_unif : `p_ s2 = fdist_uniform card_rVTX.

Let eqn3_indep :
  P |= neg_RV y2 _|_ [%x1, x2, s1, s2, r1, r2].
Proof.
pose f (a: ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX) ) :=
  let '(x1, x2, s1, s2, r1) := a in (a, s1 *d s2 - r1).
by move/(inde_RV_comp (fun (a : TX) => 0 - a) f):y2_x1x2s1s2r1_eqn3_indep.
Qed.

Lemma pi2_alice_is_leakage_free_proof : `H( x2 | AliceView) = `H `p_x2.
Proof.
rewrite eqn2_proof.
rewrite (eqn3_proof eqn3_indep neg_py2_unif).
rewrite (eqn4_proof ps2_unif eqn4_indep).
by rewrite eqn_4_1_proof.
Qed.

End pi2_alice_is_leakage_free_proof.

Section eqn6_proof.
Context {R : realType}.
Variables (T : finType) (m n : nat) (P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].
Hypothesis card_TX : #|TX| = m.+2.

Variables (r1 y2 : {RV P -> TX}) (x1 x2 s1 s2 : {RV P -> 'rV[TX]_n}).
Let x1' := x1 \+ s1.
Let r2  := s1 \*d s2 \- r1.

Let O := [%x1, x2, s1, s2, r2, y2].

Let f1 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX * TX) ->
  'rV[TX]_n := fun z =>
  let '(x1, _, _, _, _, _) := z in x1.

Let f2 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX * TX) ->
  ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX) := fun z =>
  let '(x1, x2, s1, s2, r2, y2) := z in (x2, s2, x1 + s1, r2).

Let fm : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX * TX) ->
  TX := fun z =>
  let '(_, _, _, _, _, y2) := z in y2.

(* x1; It is okay in Bob's view has it because only used in condition. *)
Let W1 := f1 `o O.
(* [%x2, s2, x1', r2]; cannot have x1, s1 here otherwise Bob knows the secret*)
Let W2 := f2 `o O.
Let Wm := fm `o O.  (* y2 *)

Let eq_W1_RV : f1 `o O = x1.
Proof. exact: boolp.funext. Qed.

Let eq_W2_RV : f2 `o O = [%x2, s2, x1', r2].
Proof. exact: boolp.funext. Qed.

Let eq_Wm_RV : fm `o O = y2.
Proof. exact: boolp.funext. Qed.

(* y2 (Wm) is generated by Bob; not related to x2, s2, x1, s1, r2 at all*)
Hypothesis W2_Wm_indep : P|= W2 _|_ Wm.
(* Because x1 (W1) is from Alice and y2 (Wm) is from Bob *)
Hypothesis W1_Wm_indep : P|= W1 _|_ Wm.

(* y2 (Wm) is generated by Bob; not related to x2, s2, x1, s1, r2 at all*)
Hypothesis W1W2_Wm_indep : P|= [%W1, W2] _|_ Wm.
(* TODO: deduce other indeps from this one. *)

(* In the paper, y2 (Wm) is uniform distributed*)
Hypothesis pWm_unif : `p_ Wm = fdist_uniform card_TX.

Let W1WmW2_cinde : W1 _|_ Wm | W2.
Proof.
by apply: inde_RV2_cinde; exact: W1W2_Wm_indep.
Qed.

Lemma eqn6_proof:
  `H(x1|[%[%x2, s2, x1', r2], y2]) = `H(x1|[%x2, s2, x1', r2]).
Proof.
rewrite -eq_W1_RV -eq_W2_RV -eq_Wm_RV.
have Ha := cpr_centropy (Y2:=W2) (Y3:=Wm) _.
apply Ha => w w2 wm Hneq0.
simpl in *.
rewrite pfwd1_pairC in Hneq0.
have Hb := @cinde_alt _ _ _ _ _ _ W1 Wm W2 w wm w2 W1WmW2_cinde Hneq0.
rewrite -/W1.
rewrite cpr_eq_pairCr.
exact: Hb.
Qed.

End eqn6_proof.

Section eqn7_proof.
Context {R : realType}.
Variables (T : finType) (m n : nat) (P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].

Variables (r1: {RV P -> TX})(x1 x2 s1 s2: {RV P -> 'rV[TX]_n}).
Let x1' := x1 \+ s1.
Let r2  := s1 \*d s2 \- r1.

Let O := [%x1, x2, s1, s2, r2].

Let f1 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX) ->
  'rV[TX]_n := fun z =>
  let '(x1, x2, s1, s2, r2) := z in x1.

Let f2 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX) ->
  ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n) := fun z =>
  let '(x1, x2, s1, s2, r2) := z in (x2, s2, x1 + s1).

Let fm : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n * TX) ->
  TX := fun z =>
  let '(x1, x2, s1, s2, r2) := z in r2.

(* x1; It is okay in Bob's view has it because only used in condition. *)
Let W1 := f1 `o O.
(* [%x2, s2, x1']; cannot have x1, s1 here otherwise Bob knows the secret*)
Let W2 := f2 `o O.
(* r2 *)
Let Wm := fm `o O.

Let eq_W1_RV : f1 `o O = x1. Proof. exact: boolp.funext. Qed.

Let eq_W2_RV : f2 `o O = [%x2, s2, x1']. Proof. exact: boolp.funext. Qed.

Let eq_Wm_RV : fm `o O = r2. Proof. exact: boolp.funext. Qed.

Hypothesis W2_Wm_indep: P|= W2 _|_ Wm.
Hypothesis W1W2_Wm_indep : P|= [%W1, W2] _|_ Wm.

(* In the paper, r2 (Wm) is uniform distributed*)
(*Hypothesis card_TX : #|TX| = m.+2.
Hypothesis pWm_unif: `p_ Wm = fdist_uniform card_TX.*)

Let W1WmW2_cinde : W1 _|_ Wm | W2.
Proof. by apply: inde_RV2_cinde; exact: W1W2_Wm_indep. Qed.

Lemma eqn7_proof : `H(x1|[%[%x2, s2, x1'], r2]) = `H(x1|[%x2, s2, x1']).
Proof.
rewrite -eq_W1_RV -eq_W2_RV -eq_Wm_RV.
apply: cpr_centropy.
move => w w2 wm Hneq0.
simpl in *.
rewrite pfwd1_pairC in Hneq0.
have Hb := @cinde_alt _ _ _ _ _ _ W1 Wm W2 w wm w2 W1WmW2_cinde Hneq0.
rewrite -/W1.
rewrite cpr_eq_pairCr.
exact: Hb.
Qed.

(* Although in the paper eqn_7 needs Theorem 3.7 to prove,
   it actually only needs cinde_alt. Because r2 is not Wm+Z but just Wm.
*)
End eqn7_proof.

Section eqn8_proof.
Context {R : realType}.
Variables (T : finType) (m n : nat) (P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].

Variables (x1 x2 s1 s2: {RV P -> 'rV[TX]_n}).
Let x1' := x1 \+ s1.

Let O := [%x1, x2, s2].

(* f1 `o X in mc_removal_pr must be x1 in eqn8 *)
Let f1 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n) -> 'rV[TX]_n := fun z =>
  let '(x1, x2, s2) := z in x1.

(* f2 `o X in mc_removal_pr must be (x2, s2) in eqn8 *)
Let f2 : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n) ->
  ('rV[TX]_n * 'rV[TX]_n) := fun z =>
  let '(x1, x2, s2) := z in (x2, s2).

(* (fm `o X)+Z in mc_removal_pr must be x1 in eqn8 *)
Let fm : ('rV[TX]_n * 'rV[TX]_n * 'rV[TX]_n) -> 'rV[TX]_n := fun z =>
  let '(x1, x2, s2) := z in x1.

Let Z := s1.
(*Hypothesis card_TX: #|TX| = m.+2.*)
Hypothesis card_rVTX: #|'rV[TX]_n| = (m.+2 ^ n).-1.+1.
Hypothesis pZ_unif : `p_ Z = fdist_uniform card_rVTX.

Let W1 := f1 `o O.   (* x1 *)
Let W2 := f2 `o O.   (* [%x2, s2] *)
Let Wm := fm `o O.   (* x1 *)
Let WmZ := fm `o O `+ s1.   (* must be x1': x1' = x1 + s1 *)

Let eq_W1_RV : f1 `o O = x1. Proof. exact: boolp.funext. Qed.

Let eq_W2_RV : f2 `o O = [%x2, s2]. Proof. exact: boolp.funext. Qed.

Let eq_Wm_RV : fm `o O = x1. Proof. exact: boolp.funext. Qed.

Let eq_WmZ_RV : fm `o O `+ s1 = x1'.
Proof. by rewrite /add_RV /neg_RV eq_Wm_RV /x1'. Qed.

Hypothesis Z_O_indep : P |= Z _|_ O.

(* Because s1 and x1 are generated by different participants *)
Hypothesis Z_WmZ_indep: P |= Z _|_ WmZ.

(* Because [%x2, s2] and x1 are generated by different participants *)
Hypothesis W2_WmZ_indep: P |= W2 _|_ WmZ.

Let pWmZ_unif : `p_ WmZ = fdist_uniform card_rVTX.
Proof.
apply: add_RV_unif; last first.
  rewrite (_ : s1 = idfun `o s1) //.
  apply: inde_RV_comp.
  rewrite inde_RV_sym.
  exact: Z_O_indep.
exact: pZ_unif.
Qed.

Lemma eqn8_proof : `H(x1|[%[%x2, s2], x1']) = `H(x1|[%x2, s2]).
Proof.
rewrite -eq_W1_RV -eq_W2_RV -eq_WmZ_RV.
rewrite -/W1 -/W2 -/WmZ.
apply: cpr_centropy => w w2 wm Hneq0.
rewrite -/W1.
exact: (mc_removal_pr f1 Z_O_indep pZ_unif w Hneq0).
Qed.

End eqn8_proof.

Section eqn8_1_proof.
  
Context {R : realType}.
Variables (T : finType) (m n : nat) (P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].
Variables (x1 x2 s2 : {RV P -> 'rV[TX]_n}).

Hypothesis x2s2_x1_indep : P |= [% x2, s2] _|_ x1.

Lemma eqn_8_1_proof : `H(x1 | [%x2, s2]) = `H `p_ x1.
Proof.
transitivity (`H([%x2, s2], x1) - `H(x2, s2)).
  by rewrite chain_rule_RV addrAC subrr add0r.
rewrite inde_RV_joint_entropyE.
  by rewrite addrAC subrr add0r.
exact: x2s2_x1_indep.
Qed.

End eqn8_1_proof.

Section pi2_bob_view_is_leakage_free_proof.
Context {R : realType}.
Variables (T : finType) (m n : nat) (P : R.-fdist T).
Let TX := [the finComRingType of 'I_m.+2].
Variables (r1 y2: {RV P -> TX})(x1 x2 s1 s2: {RV P -> 'rV[TX]_n}).
Let x1' := x1 \+ s1.
Let r2  := s1 \*d s2 \- r1.

(* Hypothese from the paper. *)
Hypothesis x2s2_x1'_indep : P |= [% x2, s2] _|_ x1'.
Hypothesis eqn6_indep : P |= [%x1, [%x2, s2, x1', r2]] _|_ y2.
Hypothesis eqn7_indep : P |= [%x1, [%x2, s2, x1']] _|_ r2.
Hypothesis eqn8_indep : P |= s1 _|_ [%x1, x2, s2].
Hypothesis x2s2_x1_indep : P |= [% x2, s2] _|_ x1.
Hypothesis s1s2_r1_indep : P |= [%s1, s2] _|_ r1.
Hypothesis s1_s2_indep : P |= s1 _|_ s2.

Hypothesis card_TX : #|TX| = m.+2.
Hypothesis pr1_unif : `p_ r1 = fdist_uniform card_TX.
(*Hypothesis py2_unif : `p_ y2 = fdist_uniform card_TX.*)
Hypothesis card_rVTX : #|'rV[TX]_n| = (m.+2 ^ n).-1.+1.
Hypothesis ps1_unif : `p_ s1 = fdist_uniform card_rVTX.

Let pr2_unif := ps1_dot_s2_r_unif pr1_unif s1_s2_indep s1s2_r1_indep.
Let BobView := [%x2, s2, x1', r2, y2].

Lemma pi2_bob_is_leakage_free_proof : `H( x1 | BobView) = `H `p_ x1.
Proof.
rewrite (eqn6_proof eqn6_indep).
rewrite (eqn7_proof eqn7_indep).
rewrite (eqn8_proof ps1_unif eqn8_indep).
by rewrite eqn_8_1_proof.
Qed.

End pi2_bob_view_is_leakage_free_proof.

End pi2.

(* TODO: Using graphoid for combinations of independ random variables. *)
Section mutual_indep.
Context {R : realType}.
(* Pairwise independence: Any collection of mutually independent
   random variables is pairwise independent

(But pairwise independence does not imply mutual independence.

How to express "a collection of any types of
mutual independent random variables"?
RV2 is a collection. But it is not a sequence so cannot be used to
generate arbitrary pairs of RVs.
Should RV2 supports to be traversed as a sequence??
*)
Variables (A : finType) (m n : nat)(P : R.-fdist A).
Variables (TX VX : finType).
Variables (x1 x2 s1 s2 r1 y2 : {RV P -> TX}).

Hypothesis Hinde :
  {homo nth x1 [:: x1; x2; s1; s2] : i j / i < j >-> P |= i _|_ j}%N.

Lemma x1_x2_inde : P |= x1 _|_ x2.
Proof. exact: (@Hinde 0 1). Qed.

Hypothesis Hinde_all : forall i j,
  P |= nth x1 [:: x1; x2; s1; s2] i _|_ nth r1 [:: r1; y2] j.

Lemma x1_r1_inde : P |= x1 _|_ r1.
Proof. exact: (@Hinde_all 0 0). Qed.


End mutual_indep.

End smc_entropy_proofs.
