From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
Require Import Reals.
From mathcomp Require Import Rstruct ring.
Require Import ssrR Reals_ext realType_ext logb ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy smc graphoid.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(*     Interpreter for Secure Multiparty Protocols                            *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope vec_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Reserved Notation "u *d w" (at level 40).
Reserved Notation "u \*d w" (at level 40).

Section interp.
Variable data : eqType.

Inductive proc : Type :=
  (*| Init : nat -> (m -> data) -> (data -> proc) -> proc*)
  | Init : nat -> data -> proc -> proc
  | Wait : proc -> proc
  | Send : nat -> data -> proc -> proc
  | Recv : nat -> (data -> proc) -> proc
  | Ret : data -> proc
  | RetNone : proc
  | Fail : proc.

Definition step (A : Type) (ps : seq proc) (trace : seq data) (yes no : proc -> A)
  (i : nat) : A * seq data :=
  let p := nth Fail ps i in
    if p is Recv frm f then
        if nth Fail ps frm is Send dst v _ then
          if dst == i then (no (f v), v::trace) else (no p, trace)
        else if nth Fail ps frm is Init _ _ _ then
          (yes p, trace)
        else (no p, trace)
    else if p is Send dst w next then
      if nth Fail ps dst is Recv frm _ then
        if frm == i then (yes next, trace) else (no p, trace)
      else if nth Fail ps dst is Init _ _ _ then
        (yes p, trace)
      else (no p, trace)
    else if p is Init i d next then
      (yes next, d::trace)
    else
      (no p, trace).

(* Extract log in Send because only in send we have both dst and v: data;
   in Recv we only have f, no data.
*)
Fixpoint interp h (ps : seq proc) (traces : seq (seq data)) :=
  let trace_ret := map (fun pt => if pt.1 is Ret v then v::pt.2 else pt.2) (zip ps traces) in
  if h is h.+1 then
    if has (fun i => (@step bool ps [::] (fun=>true) (fun=>false) i).1)
        (iota 0 (size ps)) then
      let ps_trs' := map (fun i => @step proc ps (nth [::] traces i) idfun idfun i) (iota 0 (size ps)) in
      let ps' := unzip1 ps_trs' in
      let trs' := unzip2 ps_trs' in
        interp h ps' trs'
    else (ps, trace_ret)
  else (ps, traces).
End interp.

Section scalar_product.
Variable m : nat.
Variable TX : finComRingType.
Variable VX : lmodType TX. (* vector is not ringType (mul)*)
Variable T : finType.
Variable P : R.-fdist T.
Variable dotproduct : VX -> VX -> TX.
Notation "u *d w" := (dotproduct u w).

Definition alice : nat := 0.
Definition bob : nat := 1.
Definition coserv : nat := 2.
(*Note: notation will make cbv fail.*)

Definition data := option (TX + VX).
Definition one x : data := Some (inl x).
Definition vec x : data := Some (inr x).
Definition none : data := None.

Definition Recv_one frm f : proc data :=
  Recv frm (fun x => if x is Some (inl v) then f v else Ret None).
Definition Recv_vec frm f : proc data :=
  Recv frm (fun x => if x is Some (inr v) then f v else Ret None).

Definition palice (xa : VX) : proc data :=
  Init alice (vec xa) (
  Recv_vec coserv (fun sa =>
  Recv_one coserv (fun ra =>
  Send bob (vec (xa + sa)) (
  Recv_vec bob (fun xb' =>
  Recv_one bob (fun t =>
  Ret (one (t - (xb' *d sa) + ra)))))))).
Definition pbob (xb : VX) (yb : TX) : proc data :=
  Init bob (vec xb) (
  Recv_vec coserv (fun sb =>
  Recv_one coserv (fun rb =>
  Recv_vec alice (fun xa' =>
  let t := xa' *d xb + rb - yb in
    Send alice (vec (xb + sb))
    (Send alice (one t) (Ret (one yb))))))).
Definition pcoserv (sa sb: VX) (ra : TX) : proc data :=
  Init coserv (vec sa) (
  Init coserv (vec sb) (
  Init coserv (one ra) (
  Send alice (vec sa) (
  Send alice (one ra) (
  Send bob (vec sb) (
  Send bob (one (sa *d sb - ra)) (RetNone _))))))).

Variables (sa sb: VX) (ra yb: TX) (xa xb: VX).
Definition scalar_product h :=
  (interp h [:: palice xa; pbob xb yb; pcoserv sa sb ra] [::[::];[::];[::]]).

Goal (scalar_product 11).2 = ([::]).
cbv -[GRing.add GRing.opp GRing.Ring.sort (*Equality.eqtype_hasDecEq_mixin*) ].
Undo 1.
rewrite /scalar_product.
rewrite (lock (11 : nat)) /=.
rewrite -lock (lock (10 : nat)) /=.
rewrite -lock (lock (9 : nat)) /=.
rewrite -lock (lock (8 : nat)) /=.
rewrite -lock (lock (7 : nat)) /=.
rewrite -lock (lock (6 : nat)) /=.
rewrite -lock (lock (5 : nat)) /=.
rewrite -lock (lock (4 : nat)) /=.
rewrite -lock (lock (3 : nat)) /=.
rewrite -lock (lock (2 : nat)) /=.
rewrite -lock (lock (1 : nat)) /=.
rewrite -lock (lock (0 : nat)) /=.
Abort.

Lemma scalar_product_ok :
  (scalar_product 11).2 =
   [:: [:: one ((xa + sa) *d xb + (sa *d sb - ra) - yb - (xb + sb) *d sa + ra);
           one ((xa + sa) *d xb + (sa *d sb - ra) - yb);
           vec (xb + sb); 
           one ra;
           vec sa; 
           vec xa];
       [:: one yb;
           vec (xa + sa);
           one (sa *d sb - ra);
           vec sb;
           vec xb];
       [:: one ra;
           vec sb;
           vec sa]
   ].
Proof. reflexivity. Qed.

Let test := [::
       [:: one ((xa + sa) *d xb + (sa *d sb - ra) - yb - (xb + sb) *d sa + ra);
           one ((xa + sa) *d xb + (sa *d sb - ra) - yb);
           vec (xb + sb); 
           one ra;
           vec sa; 
           vec xa];
       [:: one yb;
           vec (xa + sa);
           one (sa *d sb - ra);
           vec sb;
           vec xb];
       [:: one ra;
           vec sb;
           vec sa]
    ].

End scalar_product.

Section information_leakage_proof.
  
Section information_leakage_def.

Variable n m : nat.
Variable T : finType.
Variable P : R.-fdist T.
Let TX := [the finComRingType of 'I_m.+2].
Let VX := 'rV[TX]_n.
Variable none_TX : TX.
Variable none_VX : VX.
Variables (S1 S2 X1 X2: {RV P -> VX}) (R1 Y2: {RV P -> TX}).
Hypothesis card_TX : #|TX| = m.+2.
Hypothesis card_VX : #|VX| = m.+2.

Definition dotproduct (a b:VX) : TX := (a *m b^T)``_ord0.
Definition dotproduct_rv (A B: T -> 'rV[TX]_n) := fun p => dotproduct (A p) (B p).

Notation "u *d w" := (dotproduct u w).
Notation "u \*d w" := (dotproduct_rv u w).

Definition scalar_product_uncurry (o: VX * VX * TX * TX * VX * VX) :=
  let '(sa, sb, ra, yb, xa, xb) := o in
  (scalar_product dotproduct sa sb ra yb xa xb 11).2.

Record scalar_product_random_inputs :=
  ScalarProductRandomInputs {
    x1 : {RV P -> VX};
    x2 : {RV P -> VX};
    s1 : {RV P -> VX};
    s2 : {RV P -> VX};
    r1 : {RV P -> TX};
    y2 : {RV P -> TX};

    (* Hypothese from the information-leakage-free paper. *)
    x2_indep : P |= [% x1, s1, r1] _|_ x2;
    y2_x1x2s1s2r1_eqn3_indep : P |= y2 _|_ [%x1, x2, s1, s2, r1];
    s2_x1s1r1x2_eqn4_indep : P |= s2 _|_ [%x1, s1, r1, x2];

    neg_py2_unif : `p_ (neg_RV y2) = fdist_uniform card_TX;

    ps1_unif : `p_ s1 = fdist_uniform card_VX ;
    ps2_unif : `p_ s2 = fdist_uniform card_VX;
    py2_unif : `p_ y2 = fdist_uniform card_TX;
    pr1_unif : `p_ r1 = fdist_uniform card_TX;
  }.

Record scalar_product_intermediate_vars :=
  ScalarProductIntermediateVars {
    x1' : {RV P -> VX};
    x2' : {RV P -> VX};
    t   : {RV P -> TX};
    y1  : {RV P -> TX};
    r2  : {RV P -> TX};
  }.

Record scalar_product_relations :=
  ScalarProductRelations {
    inputs : scalar_product_random_inputs;
    vars   : scalar_product_intermediate_vars;

    pr2_unif : `p_ (r2 vars) = fdist_uniform card_TX;
    
    r2_eqE   : r2 vars = s1 inputs \*d s2 inputs \- r1 inputs;
    x1'_eqE  : x1' vars = x1 inputs \+ s1 inputs; 
    x2'_eqE  : x2' vars = x2 inputs \+ s2 inputs; 
    y1_eqE   : y1 vars = t vars \- (s1 inputs \*d x1' vars) \+ r1 inputs;
    t_eqE    : t vars = (x2 inputs \*d x2' vars) \+ r2 vars \- y2 inputs;
  }.


Definition scalar_product_RV (inputs : scalar_product_random_inputs) :
  {RV P -> seq (seq (data VX))} :=
    scalar_product_uncurry `o
   [%s1 inputs, s2 inputs, r1 inputs, y2 inputs, x1 inputs, x2 inputs].

Definition get_one (d : data VX) : TX :=
  if d is Some (inl v) then v else none_TX.

Definition get_vec (d : data VX) : VX :=
  if d is Some (inr v) then v else none_VX.

Definition get_vec_RV (party slot: nat) (inputs : scalar_product_random_inputs) : {RV P -> VX} :=
    (fun traces => get_vec (nth (vec none_VX) (nth [::] traces party) slot)) \o (scalar_product_RV inputs).

Definition get_one_RV (party slot: nat) (inputs : scalar_product_random_inputs) : {RV P -> TX} :=
    (fun traces => get_one (nth (one VX none_TX) (nth [::] traces party) slot)) \o (scalar_product_RV inputs).

End information_leakage_def.

About get_one_RV.


Section alice_leakage_free_proof.

Variable n m : nat.
Variable T : finType.
Variable P : R.-fdist T.
Let TX := [the finComRingType of 'I_m.+2].
Let VX := 'rV[TX]_n.
Variable none_TX : TX.
Variable none_VX : VX.
Variables (S1 S2 X1 X2: {RV P -> VX}) (R1 Y2: {RV P -> TX}).
Hypothesis card_TX : #|TX| = m.+2.
Hypothesis card_VX : #|VX| = m.+2.

Variable inputs : scalar_product_random_inputs P card_TX card_VX.

Let intermediate_vars :=
  ScalarProductIntermediateVars
    (get_vec_RV none_VX bob 1 inputs)
    (get_vec_RV none_VX alice 2 inputs)
    (get_one_RV none_TX alice 1 inputs)
    (get_one_RV none_TX alice 0 inputs)
    (get_one_RV none_TX bob 2 inputs).

  
End alice_leakage_free_proof.

  

End information_leakage_proof.
