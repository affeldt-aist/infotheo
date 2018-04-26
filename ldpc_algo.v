(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
Require Import Wf Recdef Reals.
From mathcomp Require Import ssreflect seq ssrbool eqtype ssrnat ssrfun path.
From mathcomp Require Import fintype bigop finset fingraph perm zmodp matrix.
From mathcomp Require Import ssralg.
Require Import ssrR Reals_ext Rbigop f2 subgraph_partition tanner.
Require Import proba channel pproba linearcode ssralg_ext.
Require Import tanner_partition summary ldpc checksum.

(** * Sum-Product Decoder *)

(** OUTLINE:
- Section Tree.
- Section Algo.
- Section ToGraph.
- Section BuildTree.
- Section Specification.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope seq_scope.
Local Open Scope vec_ext_scope.

Section Tree.
Variable id : Type.
Definition R2 := (R * R)%type.

Inductive kind : Set := kf | kv.

Definition bool_of_kind k :=
  match k with kf => true | kv => false end.

Coercion bool_of_kind : kind >-> bool.

Inductive tag : kind -> Set :=
  | Func : tag kf
  | Var : R2 -> tag kv.

Definition negk k := match k with kf => kv | kv => kf end.

Inductive tn_tree (k : kind) (U D : Type) : Type :=
  Node { node_id : id;           (** node id *)
         node_tag : tag k;       (** function or variable node *)
         children : seq (tn_tree (negk k) U D); (** neighbors below *)
         up : U;                 (** value going to the upper node *)
         down : D }.             (** value coming from the upper node *)

End Tree.

Arguments node_id {id k U D} t.
Arguments up {id k U D} t.

Section Algo.

Open Scope R_scope.

Variable id : Type.
Let tn_tree' := tn_tree id.

(** α[m0,n0](x) = Σ_{c/V(m0)\{n0}}
      δ[Σ_{v ∈ V(m0)\{n0}} c_v = x] * Π_{n1 ∈ V(m0)\{n0}} β[m0,n1](c_n1) *)

(** Compute (α[m0,n0](0), α[m0,n0](1)) simultaneously *)
Definition alpha_op (out inp : R2) :=
  let (o,o') := out in
  let (i,i') := inp in
  (o*i + o'*i', o*i' + o'*i).
Definition alpha := foldr alpha_op (1,0).

(** β[m0,n0](x) = W(y_n0|x) Π_{m1 ∈ F(n0)\{m0}} α[m1,n0](x) *)

(** Compute (β[m0,m0](0), β[m0,n0](1)) *)
Definition beta_op (out inp : R2) :=
  let (o,o') := out in let (i,i') := inp in (o*i, o'*i').
Definition beta := foldl beta_op.

(** Select α or β according to node kind *)
Definition alpha_beta {b} (t : tag b) :=
  match t with
  | Func => alpha
  | Var v => beta v
  end.

(** Compute probabilities for uplinks *)
Fixpoint sumprod_up {k} (n : tn_tree' k unit unit) : tn_tree' k R2 unit :=
  let children' := map sumprod_up (children n) in
  let up' := alpha_beta (node_tag n) (map up children') in
  Node (node_id n) (node_tag n) children' up' tt.

(** Compute combinations for all inputs but one *)
Fixpoint seqs_but1 (a b : seq R2) :=
  if b is b1 :: b2 then (a ++ b2) :: seqs_but1 (rcons a b1) b2 else [::].

(** Apply sequence of functions to same length sequence of arguments *)
Definition apply_seq {A B : Type} (l1 : seq (A -> B)) (l2 : seq A) : seq B :=
  map (fun (p : (A -> B) * A) => (fst p) (snd p)) (zip l1 l2).

(** Get input from above *)
Definition push_init down :=
  if down is Some p then ([::p], p) else ([::], (1,1)).

(** Propagate from root to leaves *)
Fixpoint sumprod_down {k} (n : tn_tree' k R2 unit) (from_above : option R2)
  : tn_tree' k R2 R2 :=
  let (arg0, down') := push_init from_above in
  let args := seqs_but1 arg0 (map up (children n)) in
  let funs := map
      (fun n' l => sumprod_down n' (Some (alpha_beta (node_tag n) l)))
      (children n)
  in
  let children' := apply_seq funs args in
  Node (node_id n) (node_tag n) children' (up n) down'.

(** Compute all message probabilities *)
Definition sumprod {k} n := sumprod_down (@sumprod_up k n) None.

(** Normalize a probability pair *)
Definition normalize (p : R2) :=
  let (p0,p1) := p in (p0 / (p0 + p1), p1 / (p0 + p1)).

(** Lookup variable node estimations *)
Fixpoint estimation {k} (n : tn_tree' k R2 R2) :=
  let l := flatten (map estimation (children n)) in
  if node_tag n is Var _ then
    (node_id n, normalize (beta_op (up n) (down n))) :: l
  else l (* node_tag n is Func *).

End Algo.

Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive seq => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive option => "option" ["Some" "None"].
Extract Inlined Constant R => "float".
Extract Inlined Constant R0 => "0.".
Extract Inlined Constant R1 => "1.".
Extract Constant Rmult => "( *.)".
Extract Constant Rplus => "(+.)".
Extract Constant Rinv  => "fun x -> 1. /. x".
Extraction "sumprod.ml" sumprod estimation.

Section ToGraph.

Fixpoint graph {id : finType} {k U D} (n : tn_tree id k U D) : rel id :=
  fun i j : id =>
  let children := children n in
  if node_id n == i then j \in map node_id children
  else if node_id n == j then i \in map node_id children
  else has (fun n => graph n i j) children.

Fixpoint labels {id} {k U D} (n : tn_tree id k U D) : seq id :=
  let l := map labels (children n) in
  @node_id id k U D n :: flatten l.

End ToGraph.

Section BuildTree.

Variables m n' : nat.
Let n := n'.+1.
Variable H : 'M['F_2]_(m, n).

Definition id := [finType of ('I_m + 'I_n)].

Import GRing.Theory.
Local Open Scope ring_scope.

Variable rW : 'I_n -> R2.

Definition kind_of_id (i : id) :=
  match i with
  | inl _ => kf
  | inr _ => kv
  end.

Definition ord_of_kind k : finType :=
  match k with
  | kv => [finType of 'I_n]
  | kf => [finType of 'I_m]
  end.

Definition id_of_kind k : ord_of_kind k -> id :=
  match k with
  | kv => inr
  | kf => inl
  end.

Definition tag_of_kind k : ord_of_kind k -> tag k :=
  match k with
  | kv => fun i => Var (rW i)
  | kf => fun i => Func
  end.

Definition tag_of_id (a : id) : tag (kind_of_id a) :=
  match a with
  | inl _ => Func
  | inr i => Var (rW i)
  end.

Definition select_children (s : seq id) k :=
  match k return ord_of_kind k -> seq (ord_of_kind (negk k)) with
  | kv => fun i =>
     let s := id_of_kind i :: s in
     [seq j <- ord_enum m | (H j i == 1) && (inl j \notin s)]
  | kf => fun i =>
     let s := id_of_kind i :: s in
     [seq j <- ord_enum n | (H i j == 1) && (inr j \notin s)]
  end.

Fixpoint build_tree_rec (h : nat) (s : seq id) k (i : ord_of_kind k)
: tn_tree id k unit unit :=
  let chrn :=
    match h with 0 => [::]
    | h'.+1 =>
      let s' := id_of_kind i :: s in
      map (@build_tree_rec h' s' (negk k)) (select_children s i)
    end
  in
  Node (id_of_kind i) (tag_of_kind i) chrn tt tt.

Definition build_tree := build_tree_rec #|id| [::].

Fixpoint msg (i1 i2 : id) (i : option id) {k} (t : tn_tree id k R2 R2) :=
  if Some i1 == i then
    if i2 == node_id t then [:: down t] else [::]
  else if Some i2 == i then
    if i1 == node_id t then [:: up t] else [::]
  else flatten (map (msg i1 i2 (Some (node_id t))) (children t)).

End BuildTree.

Arguments id_of_kind {m n'} k i.
Arguments tag_of_kind {m n'} rW k i.
Arguments select_children {m n'} H s k i.
Arguments build_tree_rec {m n'} H rW h s k i.

Section Specification.

Variables m n' : nat.
Let n := n'.+1.
Variable H : 'M['F_2]_(m, n).

Let id' := id m n'.

Import GRing.Theory.
Local Open Scope ring_scope.

Variable B : finType.
Open Scope channel_scope.
Open Scope proba_scope.
Variable W : `Ch_1('F_2, B).
Variable y : 'rV[B]_n.

Let rW n0 := (W`(y ``_ n0 | 0), W`(y ``_ n0 | 1)).

Let computed_tree := sumprod (build_tree H rW (k := kv) 0).

Variable d : 'rV['F_2]_n.
Let p01 f n0 : R2 := (f (d `[n0 := 0%R]), f (d `[n0 := 1 %R])).
Let alpha' := ldpc.alpha H W y.
Let beta' := ldpc.beta H W y.

Definition msg_spec (i j : id') : R2 :=
  match i, j with
  | inl m0, inr n0 => p01 (alpha' m0 n0) n0
  | inr n0, inl m0 => p01 (beta' n0 m0) n0
  | _, _ => (R0,R0)
  end.

Definition prec_node (s : seq id') :=
  match s with
  | [::] => None
  | [:: a & r] => Some a
  end.

Coercion choice.seq_of_opt : option >-> seq.

Fixpoint build_computed_tree h s k i : tn_tree id' k R2 R2 :=
  let chrn :=
      match h with
      | 0 => [::]
      | h'.+1 =>
        let s' := id_of_kind k i :: s in
        map (@build_computed_tree h' s' (negk k)) (select_children H s k i)
      end
  in
  let a := id_of_kind k i in
  let tag := tag_of_kind rW k i in
  Node a tag chrn
       (alpha_beta tag
           [seq msg_spec x a
           | x in finset (tanner_rel H a) :\: finset (mem_seq (prec_node s))])
       match s with
       | [::] => (R1,R1)
       | b :: _ =>
         alpha_beta (tag_of_id rW b)
           [seq msg_spec x b | x in finset (tanner_rel H b) :\ a]
       end.

Definition computed_tree_spec :=
  computed_tree = build_computed_tree #|id'| [::] (k:=kv) ord0.

Definition sumprod_spec := forall a b,
  tanner_rel H a b ->
  msg a b None computed_tree = [:: msg_spec a b].

Let estimations := estimation computed_tree.

Let C := kernel H.
Let C_not_empty := Lcode0.not_empty C.
Hypothesis Hy : receivable W (`U C_not_empty) y.
Definition esti_spec n0 (x : 'rV_n) :=
  `U C_not_empty '_ n0 `^^ W, Hy (x ``_ n0 | y).

Definition estimation_spec := uniq (unzip1 estimations) /\
  forall n0, (inr n0, p01 (esti_spec n0) n0) \in estimations.

Definition get_esti (n0 : 'I_n) :=
  pmap (fun (p : id' * R2) =>
          let (i, e) := p in if i == inr n0 then Some e else None).

Definition get_esti_spec := forall n0 : 'I_n,
    get_esti n0 estimations = [:: p01 (esti_spec n0) n0].

End Specification.
