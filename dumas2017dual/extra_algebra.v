From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg.
From mathcomp Require Import Rstruct ring boolp.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* General algebra lemmas used in dumas2017dual formalization                 *)
(*                                                                            *)
(* This file contains lemmas that are more general than DSDP-specific:        *)
(*   - Log function lemmas                                                    *)
(*   - Bigop lemmas                                                           *)
(*   - Z/mZ unit characterization lemmas                                      *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Local Definition R := Rdefinitions.R.

(* ========================================================================== *)
(*                           Log function lemmas                               *)
(* ========================================================================== *)

Section log_extra.

Lemma logr_eq1 (x : R) : 0 < x -> (log x = 0) <-> (x = 1).
Proof.
move=> Hpos; split.
- (* log x = 0 -> x = 1 *)
  move=> Hlog.
  rewrite -[x]logK //.
  by rewrite Hlog exp.powRr0.
- (* x = 1 -> log x = 0 *)
  move=> ->.
  exact: log1.
Qed.

End log_extra.

(* ========================================================================== *)
(*                           Bigop lemmas                                      *)
(* ========================================================================== *)

Section bigop_extra.

Lemma bigD1_filter {R : Type} {op : SemiGroup.com_law R} {idx : R}
  {I : eqType} (r : seq I) (j : I) (P : pred I) (F : I -> R) :
  j \in r -> P j -> uniq r ->
  \big[op/idx]_(i <- [seq x <- r | P x]) F i = 
    op (F j) (\big[op/idx]_(i <- [seq x <- r | P x] | i != j) F i).
Proof.
Proof.
move=> j_in Pj uniq_r.
apply: bigD1_seq; last by apply: filter_uniq.
by rewrite mem_filter Pj j_in.
Qed.

Lemma bigD1_seq_cond {R : Type} {op : SemiGroup.com_law R} {idx : R}
  {I : eqType} (r : seq I) (j : I) (P : pred I) (F : I -> R) :
  j \in r -> P j -> uniq r ->
  \big[op/idx]_(i <- r | P i) F i = 
    op (F j) (\big[op/idx]_(i <- r | P i && (i != j)) F i).
Proof.
move=> j_in Pj uniq_r.
rewrite (big_rem_AC op idx P F j_in) Pj /=.
congr (op (F j) _).
rewrite (rem_filter _ uniq_r).
rewrite -(@big_filter _ _ _ _ r (predI P (predC1 j)) F).
rewrite -(@big_filter _ _ _ _ [seq x <- r | predC1 j x] P F).
congr (\big[op/idx]_(i <- _) F i).
by rewrite filter_predI.
Qed.

End bigop_extra.

(* ========================================================================== *)
(*                    Z/mZ unit characterization lemmas                        *)
(* ========================================================================== *)

Section Zp_unit_extra.

(* 
   Helper lemmas for unit characterization in Z/mZ rings.
   
   In 'Z_m (integers mod m), an element x is a unit (invertible)
   if and only if gcd(x, m) = 1, i.e., coprime x m.
   
   This is fundamental for CRT-based analysis where we work with
   composite moduli m = p*q and need to establish invertibility
   from coprimality conditions.
   
   Mathematical proof:
   - Forward (coprime -> unit): By Bezout's identity, coprime x m means
     exists s,t: s*x + t*m = 1. In Z/m, this gives s*x ≡ 1, so s is inverse.
   - Backward (unit -> coprime): If x*y = 1 in Z/m, then x*y ≡ 1 (mod m),
     so m | (x*y - 1). Any common divisor d of x and m must divide 1.
     
   Technical note: These proofs require careful handling of:
   - egcdn/egcdnP for Bezout coefficients
   - Modular arithmetic (modnMml, modnDml)
   - Conversion between 'Z_m and nat (nat_of_ord, inZp)
*)

(* coprime x m implies x is a unit in 'Z_m (when m > 1) *)
(* 
   Key lemma from MathComp: unitZpE
   (x%:R : 'Z_m) \is a GRing.unit = coprime m x  (when 1 < m)
   
   For x : 'Z_m, we have x = (nat_of_ord x)%:R, so we can apply unitZpE directly.
*)
Lemma coprime_Zp_unit (m : nat) (x : 'Z_m) :
  (1 < m)%N -> coprime x m -> x \is a GRing.unit.
Proof.
move=> Hm_gt1 Hcoprime.
set xn := nat_of_ord x.
have Hx_eq: x = xn%:R :> 'Z_m by rewrite Zp_nat valZpK.
by rewrite Hx_eq unitZpE // coprime_sym.
Qed.

(* The converse: unit in 'Z_m implies coprime (when m > 1) *)
(* 
   Uses unitZpE in reverse: (x%:R) \is a GRing.unit = coprime m x
*)
Lemma Zp_unit_coprime (m : nat) (x : 'Z_m) :
  (1 < m)%N -> x \is a GRing.unit -> coprime x m.
Proof.
move=> Hm_gt1 Hunit.
set xn := nat_of_ord x.
have Hx_eq: x = xn%:R :> 'Z_m by rewrite Zp_nat valZpK.
by move: Hunit; rewrite Hx_eq unitZpE // coprime_sym.
Qed.

(* Equivalence form: unit status iff coprime (when m > 1) *)
Lemma Zp_unitP (m : nat) (x : 'Z_m) :
  (1 < m)%N -> (x \is a GRing.unit) = coprime x m.
Proof.
move=> Hm_gt1.
apply/idP/idP; [exact: (Zp_unit_coprime Hm_gt1) | exact: (coprime_Zp_unit Hm_gt1)].
Qed.

End Zp_unit_extra.

