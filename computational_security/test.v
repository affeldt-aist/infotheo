From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import seq choice fintype tuple.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TestPredSort.

Variable T : eqType.

(* Step 1: Define the new type S *)
Definition S := T -> bool.

(* Step 2: Make S a pred_sort by following the mathcomp pattern *)
(* First, define how S converts to a predicate *)
Definition pred_of_S (s : S) : pred T := s.

(* Declare the coercion from S to pred_sort *)
Coercion pred_of_S : S >-> pred.

(* Create canonical PredType instance *)
Canonical S_predType := PredType pred_of_S.

Check S_predType.

(* Step 3: Verification *)
Variable k : nat.
Variable klist : k.-bseq S.
Variable s : S.

(* This should now work: *)
Check s \in klist.

End TestPredSort.
