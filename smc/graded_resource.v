From HB Require Import structures.
From mathcomp Require Import all_boot all_order.

(**md**************************************************************************)
(* # Graded Resource Mixins for Termination Proofs                            *)
(*                                                                            *)
(* Generic mixins that abstract over nat-indexed type families, enabling      *)
(* reuse of termination proofs across multiple indexed types.                 *)
(*                                                                            *)
(* ## Layer 1: Generic Mixins                                                 *)
(*   isNatGraded T       - T is a nat-indexed type family with base and down  *)
(*   isStepDecreasing B C - step on B with context C decreases level          *)
(*   isDecomposableInterp S interp - interpreter decomposes along nat addition*)
(*                                                                            *)
(* ## Usage Pattern                                                           *)
(*   1. Define a nat-indexed type family T : nat -> Type                      *)
(*   2. Create isNatGraded instance (base case and step-down)                 *)
(*   3. Define bundle type B (e.g., sigT T or existing record)                *)
(*   4. Create isStepDecreasing instance with level function                  *)
(*   5. Apply generic termination lemmas                                      *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(** * isNatGraded: Nat-Indexed Type Family                                    *)
(******************************************************************************)

(* Mixin: a family of types indexed by nat *)
HB.mixin Record isNatGraded (T : nat -> Type) := {
  (* Terminal value at level 0 *)
  base : T 0 ;
  (* Step down one level *)
  down : forall n, T n.+1 -> T n ;
}.

HB.structure Definition NatGraded := { T of isNatGraded T }.

(******************************************************************************)
(** * isStepDecreasing: Step Operation Respects Level Grading                 *)
(******************************************************************************)

(* Record for step operation that respects level grading.
   B is the bundle type (e.g., aproc), C is the step context type.
   We extract level from bundles rather than requiring sigT structure,
   making it easier to use existing record types.

   Note: This is defined as a plain Record rather than HB.mixin because
   it takes two independent type parameters (B and C) which doesn't fit
   HB's single-key structure model. *)
Record isStepDecreasing (B : Type) (C : Type) := IsStepDecreasing {
  (* Extract level from bundle *)
  level : B -> nat ;

  (* Step a bundled value, returning new bundle and progress indicator (0 or 1) *)
  step_bundle : B -> C -> B * nat ;

  (* Key property: new level + progress <= old level *)
  step_decreases_subproof : forall b c,
    level (step_bundle b c).1 + (step_bundle b c).2 <= level b ;
}.

(******************************************************************************)
(** * isDecomposableInterp: Interpreter Decomposes Along Addition             *)
(******************************************************************************)

(* Mixin for interpreter that decomposes along addition.
   Each state type S has one canonical interpreter.
   Note: field is named 'run' to avoid shadowing common 'interp' functions. *)
HB.mixin Record isDecomposableInterp (S : Type) := {
  (* The interpreter function *)
  run : nat -> S -> S ;
  (* Decomposition: run (n + m) = run m . run n *)
  runD : forall n m s, run (n + m) s = run m (run n s) ;
  (* Identity: run 0 is identity *)
  run0 : forall s, run 0 s = s ;
}.

HB.structure Definition DecomposableInterp := { S of isDecomposableInterp S }.

(******************************************************************************)
(** * Generic Termination Lemmas                                              *)
(******************************************************************************)

(* Generic termination section.
   These lemmas show how isDecomposableInterp enables fuel sufficiency proofs.

   Application-specific hypotheses needed:
   - total_level : S -> nat (total level/fuel across all components)
   - is_quiescent : S -> bool (can any component make progress?)
   - Proof that interp 1 on a quiescent state = identity
   - Proof that enough fuel leads to quiescence *)

Section GenericTermination.

Variable S : DecomposableInterp.type.

(* Application-specific: total level of a state *)
Variable total_level : S -> nat.

(* Application-specific: quiescence predicate *)
Variable is_quiescent : S -> bool.

(* Application-specific: quiescent states are fixed points of single steps *)
Hypothesis quiescent_fixed : forall s, is_quiescent s -> run 1 s = s.

(* Application-specific: enough fuel leads to quiescence *)
Hypothesis fuel_leads_to_quiescence : forall h s,
  h >= total_level s -> is_quiescent (run h s).

(* Helper: quiescent states are fixed points under any fuel *)
Lemma quiescent_run_id n s : is_quiescent s -> run n s = s.
Proof.
elim: n => [|n IH] Hq.
  exact: run0.
have -> : n.+1 = 1 + n by rewrite add1n.
rewrite runD (quiescent_fixed Hq).
exact: IH.
Qed.

(* Generic sufficiency lemma: extra fuel beyond total_level doesn't matter *)
Lemma suffices_generic h s :
  h >= total_level s ->
  run h s = run (total_level s) s.
Proof.
move=> Hh.
have -> : h = total_level s + (h - total_level s) by rewrite subnKC.
rewrite runD.
apply: quiescent_run_id.
exact: fuel_leads_to_quiescence.
Qed.

End GenericTermination.
