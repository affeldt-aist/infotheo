(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import fintype fingraph div choice finfun bigop prime.
From mathcomp Require Import binomial ssralg finset fingroup finalg perm zmodp.
From mathcomp Require Import matrix.
Require Import subgraph_partition.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** * Tanner Graphs *)

(** OUTLINE:
- Module Tanner.
- Section tanner_relation.
- Section next_graph.
- Section subscript_set.
*)

(* TODO: move? *)
Lemma bigcup_set0 n i (T T' : finType) (D : 'I_n -> {set T'}) (A : T' -> 'I_n -> {set T}) :
  (exists t', (t' \in D i) && (A t' i != set0)) ->
  \bigcup_(t' in D i) A t' i == set0 -> D i == set0.
Proof.
move=> abs.
move/set0Pn => Hset0.
apply/set0Pn.
move=> abs'; apply Hset0 => {Hset0}.
case: abs' => t' t'i.
case: abs => t'' /andP[t''i].
case/set0Pn => t tA.
exists t; apply/bigcupP; by exists t''.
Qed.

Module Tanner.
Section tanner.

Variable (V : finType).

Record graph (r : rel V) := {
  connected : forall a b, connect r a b;
  undirected : symmetric r ;
  coloring : V -> 'I_2 ;
  bipartite : colorable r coloring }.

Record acyclic_graph (r : rel V) := {
  edges :> graph r ;
  acyclic : acyclic r }.

Definition bipartite_of_tanner r : graph r -> colorable_graph V 2.
Proof. by case => _ _; apply/Build_colorable_graph. Defined.

End tanner.
End Tanner.

Coercion tanneredges := Tanner.edges.

Section tanner_relation.

Local Open Scope ring_scope.

Variable (m n : nat) (H : 'M['F_2]_(m, n)).

Definition tanner_rel : rel ('I_ m + 'I_n) :=
  fun x y =>
  match x, y with
    | inl x', inr y' => H x' y' == 1
    | inr x', inl y' => H y' x' == 1
    | _, _ => false
  end.

Lemma sym_tanner_rel : symmetric tanner_rel.
Proof. by case. Qed.

Definition tanner_rel_kind (o : ('I_ m + 'I_n)) : 'I_2 :=
  if o is inl _ then 0 else 1.

Lemma colorable_tanner_rel : colorable tanner_rel tanner_rel_kind.
Proof. by case => v1; case. Qed.

Lemma simple_tanner_rel : simple tanner_rel.
Proof.
apply: (@colorable_is_simple _ tanner_rel 2) .
by apply colorable_tanner_rel.
Qed.

End tanner_relation.

Section next_graph.

Local Open Scope ring_scope.

Variables (m n : nat) (H : 'M['F_2]_(m, n)).

(** Variable nodes *)
Definition Vnext m0 := [set n0 | H m0 n0 == 1].

Local Notation "''V'" := (Vnext).

Definition Vgraph m0 n0 :=
  n0 |: [set x | inr x \in subgraph (tanner_rel H) (inl m0) (inr n0)].

Local Notation "''V(' x ',' y ')'" := (Vgraph x y) (format "''V(' x ','  y ')'").

(* TODO: rename *)
Lemma Vgraph_n0 m0 n0 : n0 \in 'V(m0, n0).
Proof. by rewrite /Vgraph 3!inE eqxx. Qed.

Lemma Vgraph_not0 m0 n0 : 0 < #|'V(m0, n0)|.
Proof.
rewrite card_gt0.
apply/set0Pn => /=.
eexists; by apply Vgraph_n0.
Qed.

Lemma Vgraph_set1 m1 n1 : n1 \notin 'V m1 -> 'V(m1, n1) = [set n1].
Proof.
move=> m1n1.
apply/setP => n2.
rewrite inE in_set1 /=.
case/boolP: (n2 == n1) => //= n2n1.
rewrite inE /= in m1n1.
by rewrite inE /= inE /= (negbTE m1n1).
Qed.

(** Function nodes *)
Definition Fnext n0 := [set m0 | n0 \in 'V m0].

Local Notation "''F'" := (Fnext).

Lemma VFnext m0 n0 : (n0 \in 'V m0) = (m0 \in 'F n0).
Proof. by rewrite [in X in _ = X]inE. Qed.

Definition Fgraph m0 n0 :=
  [set m1 | inl m1 \in subgraph (tanner_rel H) (inl m0) (inr n0)].

Local Notation "''F(' x ',' y ')'" := (Fgraph x y) (format "''F(' x ','  y ')'").

Lemma Fgraph_m0 m0 n0 : n0 \in 'V m0 -> m0 \in 'F(m0, n0).
Proof.
move=> Hm0.
rewrite /Fgraph inE /subgraph inE.
rewrite connect0 andbT.
by rewrite !inE /= in Hm0.
Qed.

Lemma Fgraph_nonempty m1 n1 : n1 \notin 'V m1 -> 'F(m1, n1) == set0.
Proof.
move=> m1n1.
apply/eqP/setP => m2.
rewrite in_set0.
apply/negbTE.
apply: contra m1n1.
rewrite 2!inE.
case/andP => X _.
by rewrite inE.
Qed.

Lemma Fnext_Vnext_Vgraph m0 n0 : n0 \in 'V m0 ->
  'V m0 :\ n0 \subset 'V(m0, n0) :\ n0.
Proof.
move=> m0Fn0; apply/subsetP => n1.
rewrite !inE /=.
case/andP => X1 X2.
rewrite !inE /= in m0Fn0.
rewrite X1 /= (negbTE X1) /= m0Fn0 /=.
apply/connect1.
rewrite /except /= /= X2 /=.
by apply: contra X1 => /eqP [] ->.
Qed.

Lemma Fgraph_Vnext_Vgraph m0 n0 m1 n1 :
  m1 \in 'F(m0, n0) -> n1 \in 'V m1 -> n1 != n0 -> n1 \in 'V(m0, n0).
Proof.
rewrite !inE /=.
case/andP => m0n0 m0m1 m1n1 n1n0.
rewrite (negbTE n1n0) m0n0 /=.
apply/connectP => /=.
case/connectP : m0m1 => /= p Hp1 Hp2.
exists (rcons p (inr n1)).
rewrite rcons_path /=.
apply/andP; split => //.
  apply/andP; split.
    apply/andP; split; by rewrite -Hp2.
  by apply: contra n1n0 => /eqP [] ->.
by rewrite last_rcons.
Qed.

Lemma Fgraph_Vnext2_Vgraph m0 n0 m1 n1 : 
  m1 \in 'F(m0, n0) -> n1 \in 'V m1 -> n0 \in 'V m0 -> n1 \in 'V(m0, n0).
Proof.
move=> Hm1 Hn1 Hm0.
apply/negPn/negP.
rewrite !inE negb_or.
case/andP => n1n0.
rewrite !inE in Hm1, Hm0.
rewrite negb_and /= Hm0 /=.
case/andP : Hm1 => _ Hm1 abs.
move/negP : abs; apply.
apply: (@connect_trans _ _ (inl m1) _ _ Hm1).
apply/connect1.
rewrite !inE in Hn1.
rewrite /except /= Hn1 /=.
by apply: contra n1n0 => /eqP [] ->.
Qed.

Lemma bigcup_Fgraph_set0 m0 n0 :
  [set \bigcup_(m1 in 'F n1 :\ m0) 'F(m1, n1) | n1 in 'V m0 :\ n0] == set0 ->
  'V m0 :\ n0 == set0.
Proof.
move/set0Pn => abs.
apply/set0Pn => abs'.
apply abs => {abs}.
case: abs' => n1 abs' /=.
exists (\bigcup_(m1 in 'F n1 :\ m0) 'F(m1, n1)).
apply/imsetP.
exists n1 => //.
Qed.

Lemma bigcup_succ_set0 n1 m0 :
  \bigcup_(m1 in 'F n1 :\ m0) 'F(m1, n1) == set0 -> 'F n1 :\ m0 == set0.
Proof.
set tmp := (X in _ -> X).
case/boolP : ('F n1 :\ m0 == set0) => //.
rewrite /tmp.
move=> abs.
apply (@bigcup_set0 n _ _ _ (fun x => 'F x :\ m0)).
case/set0Pn : abs => m1 Hm1.
exists m1 => //.
rewrite Hm1 /=.
apply/set0Pn.
rewrite !inE /= in Hm1.
exists m1.
apply Fgraph_m0.
rewrite !inE.
by case/andP : Hm1 => _.
Qed.

End next_graph.

(* TODO: clean *)
Section subscript_set.

Variables (m n : nat) (H : 'M['F_2]_(m, n)).

Local Open Scope ring_scope.

Require Import ssralg_ext f2.

Local Open Scope vec_ext_scope.

Local Notation "'`V'" := (Vnext H).

Lemma PCM_V (c : 'rV['F_2]_n) : H *m c ^T == 0 ->
  forall m0 : 'I_m, \big[+%R/Zp0]_(n0 : 'I_n | n0 \in `V m0) c ``_ n0 == 0.
Proof.
move/eqP => Hsyndrome i.
apply/eqP.
have : (H *m c^T) i ord0 = 0 by rewrite Hsyndrome mxE.
rewrite mxE => <-.
transitivity (\sum_(j | H i j != 0) H i j * c^T j ord0); last first.
  set X := \sum_(j < n | H i j != 0) H i j * c^T j ord0.
  rewrite (bigID (fun j => H i j != 0)) /=.
  rewrite [X in _ = _ + X](_ : _ = 0) ?GRing.addr0 //.
  apply (big_ind (fun x => x = 0)) => //.
  move=> ? ? -> ->; by rewrite GRing.addr0.
  move=> j; rewrite negbK => /eqP ->; by rewrite GRing.mul0r.
apply congr_big => //; first by move=> ?; rewrite inE F2_eq1.
move=> j; rewrite inE => /eqP ->; by rewrite GRing.mul1r mxE.
Qed.

End subscript_set.
