From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup Rstruct ring boolp classical_sets finmap.
Require Import realType_ln realType_ext ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_proba smc_entropy smc_tactics.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(*  Party, RNG and independence experiments for Secure Multiparty Protocols   *)
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
Local Open Scope vec_ext_scope.

Local Definition R := Rdefinitions.R.

Section indep.

(* TODO: if there is no wrapper type, fset cannot have
   {RV P -> V} and {RV P -> W} at the same time.
   So we have two sets here to support two types.
   It is purely an adhoc hack so we should find a better solution...

   Or we use depedendant type here to parameterize type of RV?
*)
Variable T V W : finType.
Variable P : R.-fdist T.

HB.instance Definition _ := gen_eqMixin {RV P -> V}.
HB.instance Definition _ := gen_choiceMixin {RV P -> V}.

Definition rngmap (X : finType) := {fset ({RV P -> X} * seq bool)%type}.

Axiom inde_rngs : forall (f : rngmap V) (g : rngmap W) (a : {RV P -> V}) (b : {RV P -> W}) (pa pb : seq bool),
  (a, pa) \in f -> (b, pb) \in g -> foldr andb true (map (uncurry andb) (zip pa pb)) = false ->  inde_rv a b.

End indep.

Arguments inde_rngs {_ _ _ _} f g [a b] pa pb.

Section demo.

Local Open Scope fset_scope.

Variable T V W : finType.
Variable P : R.-fdist T.
Variable x1 x2 : {RV P -> V}.
Definition px1 : seq bool := [::true; false].
Definition px2 : seq bool := [::false; true].
Let rngmap := rngmap P V.

Definition rmp : rngmap := [fset (x1, px1); (x2, px2)].

Goal P |= x1 _|_ x2.
Proof.
apply: (inde_rngs rmp rmp px1 px2) => //.
  by rewrite !inE eqxx.
by rewrite !inE eqxx orbT.
Qed.

End demo.
