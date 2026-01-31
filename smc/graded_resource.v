From HB Require Import structures.
From mathcomp Require Import all_boot all_order.

(**md**************************************************************************)
(* # Graded Resource Mixins for Termination Proofs                            *)
(*                                                                            *)
(* Generic mixins that abstract over nat-indexed type families, enabling      *)
(* reuse of termination proofs across multiple indexed types.                 *)
(*                                                                            *)
(* ## Architecture: Current vs Ideal                                          *)
(*                                                                            *)
(* ### Current Architecture (with erased interpreter)                         *)
(*                                                                            *)
(*   The current `interp` operates on erased processes (`proc`), losing       *)
(*   type information. Resource tracking requires post-hoc reconstruction:    *)
(*                                                                            *)
(*   ```                                                                      *)
(*   proc (erased) ──> interp ──> proc (erased)                               *)
(*                                  │                                         *)
(*                                  └──> reconstruct aproc (case analysis)    *)
(*                                       ├── fuel bound ✓                     *)
(*                                       └── senv bound ✓ (but coupled!)      *)
(*   ```                                                                      *)
(*                                                                            *)
(*   Limitation: Adding a new resource requires extending the reconstruction  *)
(*   with more case analysis. Resources cannot be tracked independently.      *)
(*                                                                            *)
(* ### Ideal Architecture (with typed interpreter)                            *)
(*                                                                            *)
(*   A typed interpreter preserving `aproc` indices would enable independent  *)
(*   resource tracking via separate mixin instances:                          *)
(*                                                                            *)
(*   ```                                                                      *)
(*   aproc (typed) ──> typed_interp ──> aproc (typed)                         *)
(*                                       │                                    *)
(*                                       ├── fuel: isStepDecreasing instance  *)
(*                                       ├── senv: isStepDecreasing instance  *)
(*                                       └── new_resource: isStepDecreasing   *)
(*   ```                                                                      *)
(*                                                                            *)
(*   Benefits:                                                                *)
(*   - Each resource has its own isStepDecreasing instance                    *)
(*   - Resources are tracked independently and can be composed                *)
(*   - Adding new resources doesn't require modifying existing proofs         *)
(*                                                                            *)
(* ## Current Status                                                          *)
(*                                                                            *)
(*   This file provides forward-looking infrastructure:                       *)
(*   - isNatGraded, isStepDecreasing, isDecomposableInterp mixins are ready   *)
(*   - sum_level_decreases generalizes collection-level termination           *)
(*   - Generic termination lemmas (suffices_generic, fuel_suffices_alt)       *)
(*                                                                            *)
(*   To fully utilize this infrastructure, a typed interpreter is needed.     *)
(*   Until then, fuel_senv_decreases in smc_session_types.v couples the       *)
(*   resources via case analysis reconstruction.                              *)
(*                                                                            *)
(* ## Mixins Provided                                                         *)
(*                                                                            *)
(*   isNatGraded T         - T is a nat-indexed type family with base and down*)
(*   isStepDecreasing B    - step on B decreases level (context type as field)*)
(*   isDecomposableInterp S - interpreter decomposes along nat addition       *)
(*                                                                            *)
(* ## Usage Pattern (with typed interpreter)                                  *)
(*                                                                            *)
(*   1. Define a nat-indexed type family T : nat -> Type                      *)
(*   2. Create isNatGraded instance (base case and step-down)                 *)
(*   3. Define bundle type B (e.g., sigT T or existing record)                *)
(*   4. Create isStepDecreasing instance with level function                  *)
(*   5. Apply generic termination lemmas                                      *)
(*   6. Each resource gets its own instance, tracked independently            *)
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

(* Mixin for step operation that respects level grading.
   B is the bundle type (e.g., aproc). The context type is a field,
   similar to how 'run' is a field in isDecomposableInterp.
   We extract level from bundles rather than requiring sigT structure,
   making it easier to use existing record types. *)
HB.mixin Record isStepDecreasing (B : Type) := {
  (* Context type for stepping (e.g., traces, other processes) *)
  step_ctx : Type ;

  (* Extract level from bundle *)
  level : B -> nat ;

  (* Step a bundled value, returning new bundle and progress indicator (0 or 1) *)
  step_bundle : B -> step_ctx -> B * nat ;

  (* Key property: new level + progress <= old level *)
  step_decreases_subproof : forall b c,
    level (step_bundle b c).1 + (step_bundle b c).2 <= level b ;
}.

HB.structure Definition StepDecreasing := { B of isStepDecreasing B }.

(******************************************************************************)
(** * Sum Level Decreasing: Lifting Single-Bundle to Collection               *)
(******************************************************************************)

(* This section provides the key lemma for termination proofs over collections
   of stepped bundles. It bridges the gap between:
   
   - isStepDecreasing: property of SINGLE bundles (step decreases level)
   - Termination proofs: reason about COLLECTIONS of processes
   
   ## Role in Current Architecture
   
   With the erased interpreter, this lemma is used indirectly via
   fuel_senv_decreases which couples fuel and senv tracking through
   case analysis reconstruction.
   
   ## Role in Ideal Architecture
   
   With a typed interpreter, each resource (fuel, senv, etc.) would have
   its own isStepDecreasing instance. This lemma would be instantiated
   separately for each resource:
   
   - sum_level_decreases for fuel → fuel_suffices_nored
   - sum_level_decreases for senv → senv_suffices_nored (independent!)
   - sum_level_decreases for new_resource → new_resource_suffices_nored
   
   ## Connection to fuel_suffices_nored
   
   The original proof structure in smc_session_types.v:
   
   1. fuel_suffices_nored: After [>ps] steps, system is quiescent.
      - Key insight: stepping ONE process (with progress) decreases
        the SUM of all process fuels. This is exactly sum_level_decreases.
   
   2. fuel_suffices: Given quiescence, extra fuel doesn't change result.
      - Uses interpD to decompose fuel (corresponds to fuel_suffices_alt)
   
   The sum_level_decreases lemma abstracts the induction step:
   if we step each bundle in a sequence and at least one makes progress,
   then the total level strictly decreases. *)

Section SumDecreasing.

Variable B : Type.
Variable level : B -> nat.
Variable step_ctx : Type.
Variable step_bundle : B -> step_ctx -> B * nat.
Variable default_b : B.
Variable default_c : step_ctx.

(* Core property: each step respects level grading *)
Hypothesis step_decreases : forall b c,
  level (step_bundle b c).1 + (step_bundle b c).2 <= level b.

(* Helper: sum of levels for stepped bundles *)
Definition stepped_levels (bs : seq B) (cs : seq step_ctx) : nat :=
  \sum_(i < size bs) level (step_bundle (nth default_b bs i) (nth default_c cs i)).1.

(* Helper: sum of original levels *)
Definition original_levels (bs : seq B) : nat :=
  \sum_(i < size bs) level (nth default_b bs i).

(* Helper: sum of progress indicators *)
Definition total_progress (bs : seq B) (cs : seq step_ctx) : nat :=
  \sum_(i < size bs) (step_bundle (nth default_b bs i) (nth default_c cs i)).2.

(* Stepping respects level for the entire collection:
   sum of new levels + sum of progress <= sum of old levels *)
Lemma sum_step_decreases (bs : seq B) (cs : seq step_ctx) :
  stepped_levels bs cs + total_progress bs cs <= original_levels bs.
Proof.
rewrite /stepped_levels /total_progress /original_levels -big_split /=.
apply: leq_sum => i _.
exact: step_decreases.
Qed.

(* Key lemma: if at least one bundle makes progress, total level strictly decreases.
   
   This is the heart of termination proofs like fuel_suffices_nored:
   - Each process is a bundle with level = fuel
   - Interpreter steps all processes; at least one makes progress
   - Total fuel strictly decreases
   - By induction on total fuel, we reach quiescence
   
   The lemma abstracts this pattern so it can be reused for:
   - Fuel-indexed processes (fuel_suffices_nored)
   - Session-env-indexed processes (senv_suffices)
   - Any other nat-indexed bundle type *)
Lemma sum_level_decreases (bs : seq B) (cs : seq step_ctx) :
  (exists k, k < size bs /\
    (step_bundle (nth default_b bs k) (nth default_c cs k)).2 = 1) ->
  stepped_levels bs cs < original_levels bs.
Proof.
case=> k [Hk Hprog].
have Hsum := sum_step_decreases bs cs.
(* total_progress >= 1 because process k made progress *)
have Hprog_pos : 0 < total_progress bs cs.
  rewrite /total_progress (bigD1 (Ordinal Hk)) //=.
  by rewrite addn_gt0 Hprog orTb.
(* From Hsum: stepped + progress <= original, and Hprog_pos: 0 < progress,
   we derive: stepped < stepped + progress <= original, hence stepped < original.
   Using: a < a + b (when 0 < b), and a + b <= c implies a < c by leq_trans *)
have Hlt : stepped_levels bs cs < stepped_levels bs cs + total_progress bs cs.
  by rewrite -addn1 leq_add2l.
apply leq_trans with (n := stepped_levels bs cs + total_progress bs cs).
- exact Hlt.
- exact Hsum.
Qed.

(* Variant: using 'has' predicate for the progress condition *)
Lemma sum_level_decreases_has (bs : seq B) (cs : seq step_ctx) :
  has (fun k => (step_bundle (nth default_b bs k) (nth default_c cs k)).2 == 1)
      (iota 0 (size bs)) ->
  stepped_levels bs cs < original_levels bs.
Proof.
move/hasP => [k].
rewrite mem_iota add0n => /andP [_ Hk] /eqP Hprog.
apply: sum_level_decreases.
by exists k.
Qed.

End SumDecreasing.

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

(* Alternative: sufficiency lemma given quiescence at a specific bound.
   This version is useful when the bound n0 is computed from external information
   (like typed process indices) rather than from the runtime state itself.
   Unlike suffices_generic, this doesn't require fuel_leads_to_quiescence. *)
Lemma fuel_suffices_alt h n0 s :
  h >= n0 ->
  is_quiescent (run n0 s) ->
  run h s = run n0 s.
Proof.
move=> Hh Hq.
have -> : h = n0 + (h - n0) by rewrite subnKC.
rewrite runD.
exact: quiescent_run_id.
Qed.

End GenericTermination.
