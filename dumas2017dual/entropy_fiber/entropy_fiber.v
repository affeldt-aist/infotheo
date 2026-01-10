From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap matrix lra.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid dsdp_extra.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*  General Theory of Entropy over Fibers and Solution Sets                   *)
(*                                                                            *)
(*  This file provides an abstract framework for reasoning about conditional  *)
(*  entropy when random variables are constrained by deterministic functions. *)
(*                                                                            *)
(*  Key concepts:                                                             *)
(*  - fiber f c : the preimage (solution set) of c under f                    *)
(*  - image_set f : the range of f                                            *)
(*  - Uniform distribution over fibers leads to predictable entropy           *)
(*                                                                            *)
(*  Main results:                                                             *)
(*  - centropy1_uniform_fiber: H(X | Y=c) = log(|fiber(c)|)               *)
(*    when X is uniformly distributed over fiber(c)                           *)
(*  - functional_determinacy: H([X,Z] | Cond) = H(X | Cond)                   *)
(*    when Z is functionally determined by X and Cond                         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.

Local Definition R := Rdefinitions.R.

Section abstract_fibers.

(* Domain and codomain can be any finite types *)
Variables (DomainT CodomainT : finType).

(* An arbitrary function *)
Variable f : DomainT -> CodomainT.

(* Fiber (preimage/solution set): all x such that f(x) = c *)
Definition fiber (c : CodomainT) : {set DomainT} :=
  [set x | f x == c].

(* Image (range): all values actually taken by f *)
Definition image_set : {set CodomainT} :=
  [set c | [exists x, f x == c]].

(* Alternative characterization: c is in image iff fiber is non-empty *)
Lemma mem_image_set c : 
  (c \in image_set) = [exists x, f x == c].
Proof. by rewrite inE. Qed.

(* c is in the image of f iff its fiber (preimage) is non-empty *)
Lemma fiber_non_empty_image c :
  (c \in image_set) = (fiber c != set0).
Proof.
rewrite mem_image_set.
apply/existsP/set0Pn => [[x /eqP fx_eq_c] | [x]].
- by exists x; rewrite inE fx_eq_c eqxx.
- by rewrite inE => /eqP fx_eq_c; exists x; rewrite fx_eq_c.
Qed.

(* Membership in fiber *)
Lemma mem_fiber x c : (x \in fiber c) = (f x == c).
Proof. by rewrite inE. Qed.

(* Values outside fiber have f(x) ≠ c *)
Lemma nmem_fiber x c : (x \notin fiber c) = (f x != c).
Proof. by rewrite mem_fiber. Qed.

End abstract_fibers.

Section fiber_entropy.

Variable T : finType.
Variable P : R.-fdist T.
Variables (DomainT CodomainT : finType).
Variable f : DomainT -> CodomainT.

(* Random variables *)
Variable X : {RV P -> DomainT}.
Variable Y : {RV P -> CodomainT}.

(* Y is determined by X through function f *)
Hypothesis Y_eq_fX : Y = f `o X.

(* Helper: values outside the fiber have zero conditional probability *)
Lemma fiberC_cond_Pr0 (c : CodomainT) (x : DomainT) :
  `Pr[Y = c] != 0 ->
  x \notin fiber f c ->
  `Pr[X = x | Y = c] = 0.
Proof.
move=> Hcond_pos Hnot_solution.
set constraint := fun (conds : CodomainT) (vals : DomainT) =>
  vals \in fiber f conds.
have Hconstraint: forall t, constraint (Y t) (X t).
  move=> t.
  rewrite /constraint /=.
  rewrite inE /=.
  by rewrite Y_eq_fX /comp_RV eqxx.
by rewrite (cond_prob_zero_outside_constraint Hconstraint Hcond_pos).
Qed.

(* Conditional entropy expanded as negative sum of p*log(p) over domain. *)
Lemma centropy1_as_sum (c : CodomainT) :
  `Pr[Y = c] != 0 ->
  `H[X | Y = c] = 
    - \sum_(x : DomainT) `Pr[X = x | Y = c] * log (`Pr[X = x | Y = c]).
Proof.
move=> Hcond_pos.
rewrite centropy1_RVE // /entropy.
congr (- _); apply: eq_bigr => x _.
  by rewrite jfdist_cond_cPr_eq // fst_RV2 dist_of_RVE.
rewrite fst_RV2 dist_of_RVE.
exact: Hcond_pos.
Qed.

(** Entropy unfolded: sum of uniform probabilities equals log |S|. *)
Lemma entropy_uniform_set (S : {set DomainT}) (n : nat) :
  #|S| = n ->
  (0 < n)%N ->
  (- \sum_(x in S) n%:R^-1 * log (n%:R^-1 : R)) = log (n%:R : R).
Proof.
move=> Hcard Hn_pos.
rewrite big_const iter_addr addr0 Hcard -mulr_natr.
rewrite logV; last by rewrite ltr0n.
field.
by rewrite pnatr_eq0 -lt0n.
Qed.

(** Entropy version: fdist uniform on S with H(P) = log |S|. *)
(*  Note: although this is the same as the lemma above,
    it is difficult to use this version in the following
    `centropy1_uniform_fiber` proof. So both versions are kept. *)
Lemma entropy_fdist_uniform_set (S : {set DomainT}) (n : nat) :
  #|S| = n ->
  (0 < n)%N ->
  exists (P : R.-fdist DomainT),
    (forall x, x \in S -> P x = n%:R^-1) ->
    (forall x, x \notin S -> P x = 0) ->
    `H P = log (n%:R : R).
Proof.
move=> Hcard Hn_pos.
have HS_pos: (0 < #|S|)%N by rewrite Hcard.
pose P0 := fdist_uniform_supp _ HS_pos.
exists (P0 _) => _ _.
rewrite /entropy /P0 fdist_uniform_supp_restrict.
have ->: \sum_(i in S) (fdist_uniform_supp _ HS_pos)
  i * log ((fdist_uniform_supp _ HS_pos) i) =
     \sum_(i in S) (#|S|%:R : R)^-1 * log ((#|S|%:R : R)^-1).
  apply: eq_bigr => i Hi.
  by rewrite fdist_uniform_supp_in.
rewrite big_const iter_addr addr0 Hcard -mulr_natr.
rewrite logV; last by rewrite ltr0n.
field.
by rewrite pnatr_eq0 -lt0n.
Qed.

(* If X is uniform over fiber(c) given Y=c, then H(X|Y=c) = log|fiber(c)|.
   Key lemma for computing conditional entropy via fiber cardinality. *)
Lemma centropy1_uniform_fiber (c : CodomainT) :
  `Pr[Y = c] != 0 ->
  let fiber_c := fiber f c in
  (forall x, x \in fiber_c -> 
    `Pr[X = x | Y = c] = #|fiber_c|%:R ^-1) ->
  (forall x, x \notin fiber_c ->
    `Pr[X = x | Y = c] = 0) ->
  (0 < #|fiber_c|)%N ->
  `H[X | Y = c] = log (#|fiber_c|%:R : R).
Proof.
move=> Hcond_pos /= Hsol_unif Hnonsol_zero Hcard_pos.
rewrite (centropy1_as_sum Hcond_pos).
rewrite (entropy_sum_split Hsol_unif Hnonsol_zero).
exact: entropy_uniform_set.
Qed.

(** Uniform prior implies uniform posterior on fibers. *)
Lemma uniform_prior_cond_uniform_fiber
  (card_dom : nat) (c : CodomainT) :
  #|DomainT| = card_dom ->
  `p_ X = fdist_uniform card_dom ->
  `Pr[Y = c] != 0 ->
  let fiber_c := fiber f c in
  (forall x, x \in fiber_c ->
    `Pr[X = x | Y = c] = #|fiber_c|%:R ^-1) /\
  (forall x, x \notin fiber_c ->
    `Pr[X = x | Y = c] = 0).
Proof.
Admitted.

End fiber_entropy.

Section constant_fiber_size.

Variable T : finType.
Variable P : R.-fdist T.

Variables (DomainT CodomainT : finType).
Variable f : DomainT -> CodomainT.
Variable X : {RV P -> DomainT}.
Variable Y : {RV P -> CodomainT}.

Hypothesis Y_eq_fX : Y = f `o X.

(* When all fibers have the same size *)
Hypothesis constant_fiber_size : forall c1 c2,
  c1 \in image_set f -> c2 \in image_set f ->
  #|fiber f c1| = #|fiber f c2|.

(* And X is uniformly distributed over each fiber *)
Hypothesis uniform_on_fibers : forall c x,
  `Pr[Y = c] != 0 ->
  x \in fiber f c ->
  `Pr[X = x | Y = c] = #|fiber f c|%:R ^-1.

(* Then overall conditional entropy is constant *)
Lemma centropy_constant_fibers (fiber_card : nat) :
  (forall c, c \in image_set f -> #|fiber f c| = fiber_card) ->
  (0 < fiber_card)%N ->
  `H(X | Y) = log (fiber_card%:R : R).
Proof.
move=> Hcard Hcard_pos.
rewrite centropy_RVE' /=.
(* Each term in the sum equals Pr[Y = c] * log(fiber_card) *)
transitivity (\sum_(c : CodomainT) `Pr[Y = c] * log (fiber_card%:R : R)).
  apply: eq_bigr => c _.
  have [Pc_eq0 | Pc_neq0] := eqVneq (`Pr[Y = c]) 0.
    by rewrite Pc_eq0 !mul0r.
  (* Y = c implies c is in the image *)
  have c_in_image: c \in image_set f.
    rewrite fiber_non_empty_image.
    apply/set0Pn.
    move/pfwd1_neq0: Pc_neq0 => [t [Ht _]].
    move: Ht; rewrite inE => /eqP Yt_eq_c.
    exists (X t).
    rewrite Y_eq_fX /comp_RV in Yt_eq_c.
    by rewrite -Yt_eq_c mem_fiber.
  rewrite -(Hcard _ c_in_image).
  congr (_ * _).
  apply: centropy1_uniform_fiber => //.
  - move=> x x_in_fiber.
    by apply: uniform_on_fibers.
  - move=> x x_notin_fiber.
    by apply: (fiberC_cond_Pr0 Y_eq_fX Pc_neq0 x_notin_fiber).
  - by rewrite Hcard.
(* Factor out log(fiber_card) *)
under eq_bigr do rewrite mulrC.
by rewrite -big_distrr /= sum_pfwd1 mulr1.
Qed.

End constant_fiber_size.

Section functional_determinacy.

(* When an auxiliary variable is functionally determined,
   it adds no information to entropy *)

Variable T : finType.
Variable P : R.-fdist T.

Variables (XT YT CondT : finType).
Variable X : {RV P -> XT}.
Variable Y : {RV P -> YT}.
Variable Cond : {RV P -> CondT}.

(* Y is determined by X and Cond through function g *)
Variable g : XT -> CondT -> YT.
Hypothesis Y_determined : Y = (fun t => g (X t) (Cond t)).

(* Main result: auxiliary variable adds no entropy *)
Lemma centropy_determined_contract :
  `H([% X, Y] | Cond) = `H(X | Cond).
Proof.
(* Use chain rule *)
have ->: `H([% X, Y] | Cond) = 
  `H(Cond, [% X, Y]) - `H `p_Cond.
  by rewrite chain_rule_RV addrAC subrr add0r.
rewrite Y_determined.
(* Expand the joint entropy *)
have ->: `H(Cond, [% X, (fun t => g (X t) (Cond t))]) = 
  `H `p_[% Cond, X].
  rewrite joint_entropy_RVA.
  
  have ->: (fun t => g (X t) (Cond t)) = 
           (fun cx => g cx.2 cx.1) `o [% Cond, X].
    apply: boolp.funext => t /=.
    by rewrite /comp_RV /=.
  by rewrite joint_entropy_RV_comp.
(* Use chain rule again *)
have ->: `H(X | Cond) = `H(Cond, X) - `H `p_Cond.
  by rewrite chain_rule_RV addrAC subrr add0r.
by [].
Qed.

End functional_determinacy.

Section conditional_entropy_with_functional_constraint.

(* When conditioning on (Y, Z) where Z = g(X, Y), 
   the conditional entropy H(X | Y, Z) can be computed from 
   H(X | Y) by restricting to the fibers where Z takes specific values *)

Variable T : finType.
Variable P : R.-fdist T.
Variables (XT YT ZT : finType).
Variable X : {RV P -> XT}.
Variable Y : {RV P -> YT}.
Variable Z : {RV P -> ZT}.

(* Z is determined by X and Y *)
Variable g : XT -> YT -> ZT.
Hypothesis Z_determined : Z = (fun t => g (X t) (Y t)).

(* For each (y, z) pair, X is uniformly distributed over the fiber *)
Hypothesis uniform_over_fibers : forall y z x,
  `Pr[[% Y, Z] = (y, z)] != 0 ->
  x \in [set x' | g x' y == z] ->
  `Pr[X = x | [% Y, Z] = (y, z)] = 
    #|[set x' | g x' y == z]|%:R^-1.

(* All fibers for a fixed y have constant size *)
Hypothesis constant_fiber_size_per_y : forall y z1 z2,
  [set x' | g x' y == z1] != set0 ->
  [set x' | g x' y == z2] != set0 ->
  #|[set x' | g x' y == z1]| = #|[set x' | g x' y == z2]|.

(* Helper: values outside the fiber have zero conditional probability *)
Lemma fiberC_jcond_Pr0 (y : YT) (z : ZT) (x : XT) :
  `Pr[[% Y, Z] = (y, z)] != 0 ->
  g x y != z ->
  `Pr[X = x | [% Y, Z] = (y, z)] = 0.
Proof.
move=> Hyz_neq0 x_notin_fiber.
rewrite cpr_eqE.
have ->: `Pr[[%X, [% Y, Z]] = (x, (y, z))] = 0.
  rewrite pfwd1_eq0.
    by [].
  rewrite fin_img_imset.
  apply/imsetP => [[t _ [Xt_eq Yt_eq Zt_eq]]].
  move: x_notin_fiber.
  rewrite Zt_eq.
  by rewrite Z_determined /= Xt_eq Yt_eq eqxx.
field.
exact: Hyz_neq0.
Qed.

(* When fibers have constant cardinality and X is uniform over each fiber,
   the conditional entropy is log(fiber_card). Joint conditioning version. *)
Lemma centropy_jcond_determined_fibers (fiber_card : nat) :
  (forall y z, 
    `Pr[[% Y, Z] = (y, z)] != 0 ->
    #|[set x' | g x' y == z]| = fiber_card) ->
  (0 < fiber_card)%N ->
  `H(X | [% Y, Z]) = log (fiber_card%:R : R).
Proof.
move=> Hcard Hcard_pos.
rewrite centropy_RVE' /=.
(* Show each term equals Pr * log(fiber_card) *)
transitivity
  (\sum_(yz : YT * ZT)
    `Pr[[% Y, Z] = yz] * log (fiber_card%:R : R)).
  apply: eq_bigr => [[y z]] _.
  have [Hyz_eq0 | Hyz_neq0] := eqVneq (`Pr[[% Y, Z] = (y, z)]) 0.
    by rewrite Hyz_eq0 !mul0r.
  congr (_ * _).
  (* Define the fiber *)
  pose fiber_yz := [set x' : XT | g x' y == z].
  (* Fiber is non-empty *)
  have fiber_nempty: fiber_yz != set0.
    apply/set0Pn.
    move/pfwd1_neq0: Hyz_neq0 => [t [/eqP [Yt_eq Zt_eq] _]].
    exists (X t); rewrite inE.
    rewrite Z_determined /= Yt_eq in Zt_eq.
    apply/eqP.
    by exact: Zt_eq.
  rewrite /centropy1_RV /centropy1.
  rewrite (bigID (mem fiber_yz)) /=.
  rewrite [X in _ + X]big1 ?addr0; last first.
    move=> x x_notin.
    rewrite jPr_Pr cpr_in1.
    have ->: `Pr[X = x | [% Y, Z] = (y, z)] = 0.
      apply: fiberC_jcond_Pr0 => //.
      by rewrite inE in x_notin.
    by rewrite mul0r.
    
  (* Convert set-based conditional probability notation to equality notation *)
  have ->: \sum_(i in fiber_yz)
             \Pr_`p_ [% X, [% Y, Z]][[set i] | [set (y, z)]] *
             log \Pr_`p_ [% X, [% Y, Z]][[set i] | [set (y, z)]] =
           \sum_(i in fiber_yz)
             `Pr[X = i | [% Y, Z] = (y, z)] *
             log (`Pr[X = i | [% Y, Z] = (y, z)]).
    apply: eq_bigr => x _.
    by rewrite !jcPrE -!cpr_inE' !cpr_in1.    
  
  (* Replace conditional probabilities with uniform distribution over fiber *)
  have ->: \sum_(i in fiber_yz)
             `Pr[X = i | [% Y, Z] = (y, z)] *
             log (`Pr[X = i | [% Y, Z] = (y, z)]) =
           \sum_(i in fiber_yz)
             fiber_card%:R^-1 * log (fiber_card%:R^-1 : R).
    apply: eq_bigr => x x_in.
    have ->: `Pr[X = x | [% Y, Z] = (y, z)] = fiber_card%:R ^-1.
      rewrite uniform_over_fibers => //.
      by rewrite (Hcard y z Hyz_neq0).
    by [].    
  apply: entropy_uniform_set => //.
  exact: (Hcard y z Hyz_neq0).  
under eq_bigr do rewrite mulrC.
by rewrite -big_distrr /= sum_pfwd1 mulr1.
Qed.

End conditional_entropy_with_functional_constraint.

