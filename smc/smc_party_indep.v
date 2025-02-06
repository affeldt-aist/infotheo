From HB Require Import structures.
Require Import Reals.
From mathcomp Require Import all_ssreflect all_algebra fingroup Rstruct ring boolp classical_sets.
Require Import ssrR Reals_ext realType_ext logb ssr_ext ssralg_ext bigop_ext fdist.
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
Local Open Scope chap2_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

Section party.

Inductive party := Alice | Bob | Coserv.

Definition party_eqb_subproof (p1 p2: party) : { p1 = p2 } + { p1 <> p2 }.
Proof. decide equality. Defined.

Definition party_eqb (p1 p2: party) : bool :=
  if party_eqb_subproof p1 p2 then true else false. 

Print Module Equality.

Lemma party_eqP : Equality.axiom party_eqb.
Proof.
move=> p1 p2.
rewrite /party_eqb.
by case: party_eqb_subproof => /= H;constructor.
Qed.

HB.instance Definition _ := hasDecEq.Build party party_eqP.

Definition party_to_nat (a : party) : nat :=
  match a with Alice => 0 | Bob => 1 | Coserv => 2 end.

Definition nat_to_party (a : nat) : party :=
  match a with 0 => Alice | 1 => Bob | _ => Coserv end.

Lemma party_natK : cancel party_to_nat nat_to_party.
Proof. by case. Qed.

HB.instance Definition _ : isCountable party := CanIsCountable party_natK.

Definition party_enum := [:: Alice; Bob; Coserv].

Lemma party_enumP : Finite.axiom party_enum.
Proof. by case. Qed.

HB.instance Definition _ := isFinite.Build party party_enumP.

End party.

Section indep.

(* Memo: use this to contain related expressions *)
Inductive AliceVar := X1.
Inductive BobVar := X2 | Y2.
Inductive CoservVar := S1 | S2 | R1. (* Once one RV is generated, RGN changes so they are mutual indep *)

(* uniform distribution:

   TX : 1,2,3,.....N
        ([Alice: 100%, Bob: 0%, Coserv: 0%], 1) (Alice, 2) ..... (Alice, N)

   r1 + y1 =  (uniform dist; by <?> lemma)

   r1 : 1,2,3,..... N
   y1 : 1,2,3...... M

   r1 + y1: (

---- Convex algebra
   (party1 * party2 * party3 * {RV P -> TX})  

   (1, 0, 0, x1)
   (0.5, 0.5, 0, x1 + y2 * y2 * s1)

   can be embeded into Euclidean space.

---- Union semi-lattice

   ({RV P -> TX} * seq bool) 
 
   (x1, 1, 0, 0...)
   (x1 + y2, 1, 1, 0...)
   (s1, 0, 0, 1...)
   (x1 + y2 * s1 + s2, 1, 1, 1...)

   cannot be naturally embeded into Euclidean space.
   cosever: a collection of countable parties, so the vector become inf.
   or because protocol must stop, so the vector is finite.
----

   Variables (x : {RV P -> VX})(x_ : (party * party * party)).

   The set of tuples should form as a partial function whose type would be:
   f: {RV P -> TX} -> (A, B, C)

   (there are inf many RVs;
    initially we have values for primitive RVs like x1, s1 and so on;
    x1 maps to a specific tuple like (1, 0, 0) and so on for s1...;
    we can gradullay add such mapping to functions.
    )

    f_x1 union f_x2 .... and then the final function knows more and more
    mappings of tuples.

   Extensive function: function can accept parties one by one.

----

   (1, 0, 0, x1)    --> x1
   
*)


Variable T : finType.
Variable P : R.-fdist T.
Variable TX : finComRingType.
Variable VX : lmodType TX.

(* TODO: TX VX type issue (sum type?) *)

HB.instance Definition _ := gen_eqMixin {RV P -> VX}.
HB.instance Definition _ := gen_choiceMixin {RV P -> VX}.

From mathcomp Require Import finmap.

Variables (x1 : {RV P -> VX})(x2 : {RV P -> VX}).

Definition partymap := {fset ({RV P -> VX} * seq bool)%type}.

Print cid.
Print constructive_indefinite_description.
About sigW.

Hypothesis inde_between_parties : forall (f : partymap) (a b : {RV P -> VX}) (pa pb : seq bool),
  (a, pa) \in f -> (b, pb) \in f -> foldr andb true (map (uncurry andb) (zip pa pb)) = false ->  inde_rv a b.
Arguments inde_between_parties f [a b].

Local Open Scope fset_scope.

Definition px1 : seq bool := [::true].
Definition px2 : seq bool := [::false; true].
Definition partymap_a : partymap := [fset (x1, px1); (x2, px2)].

Goal P |= x1 _|_ x2.
Proof.
apply: (inde_between_parties partymap_a px1 px2) => //.
  by rewrite !inE eqxx.
by rewrite !inE eqxx orbT.
Qed.

End indep.

