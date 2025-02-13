(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg perm zmodp.
From mathcomp Require Import matrix.
Require Import bigop_ext ssralg_ext f2 subgraph_partition.

(**md**************************************************************************)
(* # Tanner Graphs                                                            *)
(*                                                                            *)
(* ```                                                                        *)
(* 'F(m0, n0) == function nodes of the subgraph rooted at edge m0-n0          *)
(* ‘V(m0, n0) == the variable nodes of the subgraph rooted at edge m0-n0      *)
(*               (to which we add n0)                                         *)
(* ```                                                                        *)
(******************************************************************************)

Reserved Notation "''V(' x ',' y ')'" (format "''V(' x ','  y ')'").
Reserved Notation "''F(' x ',' y ')'" (format "''F(' x ','  y ')'").

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module Tanner.
Section tanner.
Variable (V : finType).

Record graph (r : rel V) := {
  connected : forall a b, connect r a b;
  undirected : symmetric r ;
  bipartite : Colorable.graph r 2 }.

Record acyclic_graph (r : rel V) := {
  edges :> graph r ;
  acyclic : acyclic r }.

End tanner.
End Tanner.

Coercion tanneredges := Tanner.edges.

Section tanner_relation.
Local Open Scope ring_scope.
Variable (m n : nat) (H : 'M['F_2]_(m, n)).

Definition tanner_rel' : rel ('I_ m + 'I_n) :=
  fun x y =>
  match x, y with
    | inl x', inr y' => H x' y' == 1
    | inr x', inl y' => H y' x' == 1
    | _, _ => false
  end.

Definition tanner_rel : rel ('I_ m + 'I_n) := locked tanner_rel'.

Lemma tanner_relE : tanner_rel = tanner_rel'.
Proof. by rewrite /tanner_rel; unlock. Qed.

Lemma sym_tanner_rel : symmetric tanner_rel.
Proof. rewrite tanner_relE; by case. Qed.

Definition tanner_rel_kind (o : ('I_ m + 'I_n)) : 'I_2 :=
  if o is inl _ then 0 else 1.

Lemma colorable_tanner_rel : colorable tanner_rel tanner_rel_kind.
Proof. rewrite tanner_relE; by case => v1; case. Qed.

Lemma simple_tanner_rel : simple tanner_rel.
Proof. exact/(@colorable_is_simple _ tanner_rel 2)/colorable_tanner_rel. Qed.

End tanner_relation.

Section next_graph.
Local Open Scope ring_scope.
Variables (m n : nat) (H : 'M['F_2]_(m, n)).

(** Variable nodes *)
Definition Vnext m0 := locked [set n0 | H m0 n0 == 1].

Local Notation "''V'" := (Vnext).

Lemma VnextE1 n0 m0 : n0 \in 'V m0 = tanner_rel H (inr n0) (inl m0).
Proof. by rewrite /Vnext tanner_relE -lock inE. Qed.

Lemma VnextE2 n0 m0 : n0 \in 'V m0 = tanner_rel H (inl m0) (inr n0).
Proof. by rewrite /Vnext tanner_relE -lock inE. Qed.

Definition VnextE := (VnextE1,VnextE2).

Definition Vgraph m0 n0 :=
  n0 |: [set x | inr x \in subgraph (tanner_rel H) (inl m0) (inr n0)].

Local Notation "''V(' x ',' y ')'" := (Vgraph x y).

Lemma root_in_Vgraph m0 n0 : n0 \in 'V(m0, n0).
Proof. by rewrite /Vgraph 3!inE eqxx. Qed.

Lemma mem_VgraphD1_Vnext n0 n1 m0 : n1 \in 'V( m0, n0) :\ n0 -> n0 \in 'V m0.
Proof.
rewrite 2!inE => /andP[n1n0].
by rewrite 3!inE (negbTE n1n0) orFb inE -VnextE => /andP[].
Qed.

Lemma Vgraph_not0 m0 n0 : 0 < #|'V(m0, n0)|.
Proof.
rewrite card_gt0.
apply/set0Pn => /=.
eexists; exact: root_in_Vgraph.
Qed.

Lemma Vgraph_set1 m1 n1 : n1 \notin 'V m1 -> 'V(m1, n1) = [set n1].
Proof.
move=> m1n1.
apply/setP => n2.
rewrite !inE.
case/boolP: (n2 == n1) => //= n2n1.
by rewrite -VnextE (negbTE m1n1).
Qed.

(** Function nodes *)
Definition Fnext n0 := locked [set m0 | n0 \in 'V m0].

Local Notation "''F'" := (Fnext).

Lemma FnextE m0 n0 : (m0 \in 'F n0) = (n0 \in 'V m0).
Proof. by rewrite /Fnext; unlock; rewrite inE. Qed.

Definition Fgraph m0 n0 :=
  [set m1 | inl m1 \in subgraph (tanner_rel H) (inl m0) (inr n0)].

Local Notation "''F(' x ',' y ')'" := (Fgraph x y).

Lemma Fgraph_m0 m0 n0 : n0 \in 'V m0 -> m0 \in 'F(m0, n0).
Proof.
move=> Hm0; by rewrite /Fgraph inE /subgraph inE -VnextE Hm0 connect0.
Qed.

Lemma Fgraph_nonempty m1 n1 : n1 \notin 'V m1 -> 'F(m1, n1) == set0.
Proof.
move=> m1n1.
apply/eqP/setP => m2.
rewrite in_set0.
apply/negbTE.
apply: contra m1n1.
rewrite 2!inE -VnextE; by case/andP.
Qed.

Lemma Fnext_Vnext_Vgraph m0 n0 : n0 \in 'V m0 ->
  'V m0 :\ n0 \subset 'V(m0, n0) :\ n0.
Proof.
move=> m0Fn0; apply/subsetP => n1.
rewrite in_setD1.
case/andP => X1 X2.
rewrite in_setD1 X1 /= !inE (negbTE X1) orFb -VnextE /= m0Fn0 /=.
apply/connect1.
rewrite exceptE /= -VnextE X2.
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
  rewrite -Hp2.
  rewrite exceptE /= -VnextE m1n1 /=.
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
rewrite negb_and /= -VnextE Hm0 /=.
case/andP : Hm1 => _ Hm1 abs.
move/negP : abs; apply.
apply: (@connect_trans _ _ (inl m1) _ _ Hm1).
apply/connect1.
rewrite exceptE /= -VnextE Hn1 /=.
by apply: contra n1n0 => /eqP [] ->.
Qed.

Lemma bigcup_Fgraph_set0 m0 n0 :
  [set \bigcup_(m1 in 'F n1 :\ m0) 'F(m1, n1) | n1 in 'V m0 :\ n0] == set0 ->
  'V m0 :\ n0 == set0.
Proof.
move/set0Pn => abs; apply/set0Pn => -[n1 Hn1 /=]; apply abs => {abs}.
exists (\bigcup_(m1 in 'F n1 :\ m0) 'F(m1, n1)).
by apply/imsetP; exists n1.
Qed.

Lemma bigcup_succ_set0 n1 m0 :
  \bigcup_(m1 in 'F n1 :\ m0) 'F(m1, n1) == set0 -> 'F n1 :\ m0 == set0.
Proof.
set goal := (X in _ -> X).
case/boolP : ('F n1 :\ m0 == set0) => //.
rewrite /goal.
case/set0Pn => m1 Hm1.
apply (@bigcup_set0 _ _ _ _ (fun x => 'F x :\ m0) _ m1); first by rewrite Hm1.
apply/set0Pn; exists m1.
rewrite Fgraph_m0 // -FnextE.
by move: Hm1; rewrite !inE => /andP[].
Qed.

End next_graph.

Section subscript_set.
Variables (m n : nat) (H : 'M['F_2]_(m, n)).
Local Notation "''V'" := (Vnext H).

Local Open Scope ring_scope.
Import GRing.Theory.
Local Open Scope vec_ext_scope.

(* TODO: not used? *)
Lemma PCM_V (c : 'rV['F_2]__) : H *m c ^T = 0 ->
  forall m0, \big[+%R/Zp0]_(n0 < n | n0 \in 'V m0) c ``_ n0 = 0.
Proof.
move=> Hsyndrome m0.
have : (H *m c^T) m0 ord0 = 0 by rewrite Hsyndrome mxE.
rewrite mxE => <-.
rewrite [in RHS](bigID (fun j => H m0 j == 0)) /=.
rewrite [in RHS](eq_bigr (fun=> 0)); last by move=> ? /eqP ->; rewrite mul0r.
rewrite [in RHS]big1 // add0r.
apply congr_big => //.
  move=> x.
  by rewrite -F2_eq1 VnextE //= sym_tanner_rel // /tanner_rel /=; unlock.
move=> n1 n1m0; rewrite (_ : H _ _ = 1) ?mul1r ?mxE //.
apply/eqP; by move: n1m0; rewrite VnextE /tanner_rel; unlock.
Qed.

End subscript_set.
