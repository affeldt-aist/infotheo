From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg ring.
From mathcomp Require Import Rstruct.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_proba smc_entropy.
Require Import smc_tactics.

(******************************************************************************)
(*                                                                            *)
(*     Interpreter for Secure Multiparty Protocols                            *)
(*                                                                            *)
(******************************************************************************)

Import GRing.Theory.
Import Num.Theory.
Module scp := smc_entropy.smc_entropy_proofs.

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

Reserved Notation "u *d w" (at level 40).
Reserved Notation "u \*d w" (at level 40).

Section interp.
Variable data : Type.
Inductive proc : Type :=
  | Init : data -> proc -> proc
  | Send : nat -> data -> proc -> proc
  | Recv : nat -> (data -> proc) -> proc
  | Ret : data -> proc
  | Finish : proc
  | Fail : proc.

Definition step (ps : seq proc) (trace : seq data) (i : nat) :=
  let ps := nth Fail ps in
  let p := ps i in
  let nop := (p, trace, false) in
  match p with
  | Recv frm f =>
      if ps frm is Send dst v _ then
        if dst == i then (f v, v::trace, true) else nop
      else nop
  | Send dst w next =>
      if ps dst is Recv frm _ then
        if frm == i then (next, trace, true) else nop
      else nop
  | Init d next =>
      (next, d::trace, true)
  | Ret d =>
      (Finish, d :: trace, true)
  | Finish | Fail =>
      nop
  end.

Fixpoint interp h (ps : seq proc) (traces : seq (seq data)) :=
  if h is h.+1 then
    let ps_trs' := [seq step ps (nth [::] traces i) i
                   | i <- iota 0 (size ps)] in
    if has snd ps_trs' then
      let ps' := unzip1 (unzip1 ps_trs') in
      let trs' := unzip2 (unzip1 ps_trs') in
      interp h ps' trs'
    else (ps, traces)
  else (ps, traces).

Definition run_interp h procs := interp h procs (nseq (size procs) [::]).
End interp.

Arguments Finish {data}.
Arguments Fail {data}.

Section traces.
Variable data : eqType.
Local Open Scope nat_scope.

Lemma size_traces h (procs : seq (proc data)) :
  forall s, s \in (run_interp h procs).2 -> size s <= h.
Proof.
clear.
pose k := h.
rewrite -{2}/k /run_interp.
set traces := nseq _ _ => /=.
have Htr : {in traces, forall s, size s <= k - h}.
  move=> s. by rewrite mem_nseq => /andP[] _ /eqP ->.
have : h <= k by [].
elim: h k procs traces Htr => [| h IH] k procs traces Htr hk /=.
  move=> s /Htr. by rewrite subn0.
move=> s.
case: ifP => H; last by move/Htr/leq_trans; apply; rewrite leq_subr.
move/IH; apply; last by apply/ltnW.
move=> /= {}s.
rewrite /unzip2 -2!map_comp.
case/mapP => i.
rewrite mem_iota add0n /step => /andP[] _ Hi /=.
have Hsz : size (nth [::] traces i) < k - h.
  case/boolP: (i < size traces) => Hi'.
    apply/(leq_ltn_trans (Htr _ _)).
      by rewrite mem_nth.
    by rewrite subnS prednK // leq_subRL // ?addn1 // ltnW.
  rewrite nth_default. by rewrite leq_subRL ?addn1 // ltnW.
  by rewrite leqNgt.
case: nth => /=[d p|n d p|n p|d||] -> //=; try exact/ltnW.
- case: nth => /=[{}d {}p|n1 {}d {}p| n1 _|{}d||] /=; try exact/ltnW.
  case: ifP => _ /=; exact/ltnW.
- case: nth => /=[{}d p1|n1 {}d p1| n1 p1|{}d||] /=; try exact/ltnW.
  case: ifP => _ //=; exact/ltnW.
Qed.

Lemma size_interp h (procs : seq (proc data)) (traces : seq (seq data)) :
  size procs = size traces ->
  size (interp h procs traces).1 = size procs /\
  size (interp h procs traces).2 = size procs.
Proof.
elim: h procs traces => // h IH procs traces Hsz /=.
case: ifP => _ //.
rewrite /unzip1 /unzip2 -!map_comp.
set map1 := map _ _.
set map2 := map _ _.
case: (IH map1 map2).
  by rewrite !size_map.
move=> -> ->.
by rewrite !size_map size_iota.
Qed.

Lemma size_traces_nth h (procs : seq (proc data)) (i : 'I_(size procs)) :
  (size (nth [::] (run_interp h procs).2 i) <= h)%N.
Proof.
by apply/size_traces/mem_nth; rewrite (size_interp _ _).2 // size_nseq.
Qed.

Definition interp_traces h procs : (size procs).-tuple (h.-bseq data) :=
  [tuple Bseq (size_traces_nth h i) | i < size procs].

Lemma interp_traces_ok h procs :
 map val (interp_traces h procs) = (run_interp h procs).2.
Proof.
apply (eq_from_nth (x0:=[::])).
  rewrite size_map /= size_map size_enum_ord.
  by rewrite (size_interp _ _).2 ?size_nseq.
move=> i Hi.
rewrite size_map in Hi.
rewrite (nth_map [bseq]) // /interp_traces.
rewrite size_tuple in Hi.
by rewrite (_ : i = Ordinal Hi) // nth_mktuple.
Qed.
End traces.

Section scalar_product.
Variable m : nat.
Variable TX : finComRingType.
Variable VX : lmodType TX. (* vector is not ringType (mul)*)
Variable dotproduct : VX -> VX -> TX.
Notation "u *d w" := (dotproduct u w).

Definition alice : nat := 0.
Definition bob : nat := 1.
Definition coserv : nat := 2.

Definition data := (TX + VX)%type.
Definition one x : data := inl x.
Definition vec x : data := inr x.

Definition Recv_one frm f : proc data :=
  Recv frm (fun x => if x is inl v then f v else Fail).
Definition Recv_vec frm f : proc data :=
  Recv frm (fun x => if x is inr v then f v else Fail).

Definition pcoserv (sa sb: VX) (ra : TX) : proc data :=
  Init (vec sa) (
  Init (vec sb) (
  Init (one ra) (
  Send alice (vec sa) (
  Send alice (one ra) (
  Send bob (vec sb) (
  Send bob (one (sa *d sb - ra)) Finish)))))).

Definition palice (xa : VX) : proc data :=
  Init (vec xa) (
  Recv_vec coserv (fun sa =>
  Recv_one coserv (fun ra =>
  Send bob (vec (xa + sa)) (
  Recv_vec bob (fun xb' =>
  Recv_one bob (fun t =>
  Ret (one (t - (xb' *d sa) + ra)))))))).

Definition pbob (xb : VX) (yb : TX) : proc data :=
  Init (vec xb) (
  Init (one yb) (
  Recv_vec coserv (fun sb =>
  Recv_one coserv (fun rb =>
  Recv_vec alice (fun xa' =>
  let t := xa' *d xb + rb - yb in
    Send alice (vec (xb + sb))
    (Send alice (one t) (Ret (one yb)))))))).

Variables (sa sb: VX) (ra yb: TX) (xa xb: VX).
Definition smc_scalar_product h :=
  (interp h [:: palice xa; pbob xb yb; pcoserv sa sb ra] [::[::];[::];[::]]).

Goal (smc_scalar_product 11).2 = ([::]).
cbv -[GRing.add GRing.opp GRing.Ring.sort (*Equality.eqtype_hasDecEq_mixin*) ].
Undo 1.
rewrite /smc_scalar_product.
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

Let xa' := xa + sa.
Let xb' := xb + sb.
Let rb := sa *d sb - ra.
Let t := xa' *d xb + rb - yb.
Let ya := t - xb' *d sa + ra.

Lemma smc_scalar_product_ok :
  smc_scalar_product 11 =
  ([:: Finish; Finish; Finish],
   [:: [:: one ya;
           one t;
           vec xb';
           one ra;
           vec sa;
           vec xa];
       [:: one yb;
           vec xa';
           one rb;
           vec sb;
           one yb;
           vec xb];
       [:: one ra;
           vec sb;
           vec sa]
   ]).
Proof. reflexivity. Qed.

Definition smc_scalar_product_traces :=
  interp_traces 11 [:: palice xa; pbob xb yb; pcoserv sa sb ra].

Lemma smc_scalar_product_traces_ok :
  smc_scalar_product_traces =
    [tuple
     [bseq one ya; one t; vec xb'; one ra; vec sa; vec xa];
     [bseq one yb; vec xa'; one rb; vec sb; one yb; vec xb];
     [bseq one ra; vec sb; vec sa]].
Proof. by apply/val_inj/(inj_map val_inj); rewrite interp_traces_ok. Qed.

Definition smc_scalar_product_tracesT := 11.-bseq data.

Definition smc_scalar_product_party_tracesT :=
  3.-tuple smc_scalar_product_tracesT.

Definition is_scalar_product (trs: smc_scalar_product_party_tracesT) :=
  let '(ya, xa) :=
    if tnth trs 0 is Bseq [:: inl ya; _; _; _; _; inr xa] _ then (ya, xa)
    else (0,0) in
  let '(yb, xb) :=
    if tnth trs 1 is Bseq [:: inl yb; _; _; _; _; inr xb] _ then (yb, xb)
    else (0,0) in
  xa *d xb = ya + yb.

End scalar_product.

Section pi2.

Section information_leakage_proof.
Variable n m : nat.
Variable T : finType.
Variable P : R.-fdist T.
Let TX := [the finComRingType of 'I_m.+2].
Let VX := 'rV[TX]_n.

Lemma card_TX : #|TX| = m.+2.
Proof. by rewrite card_ord. Qed.

Let q := (m.+2 ^ n)%nat.-1.
Lemma card_VX : #|VX| = q.+1.
Proof.
rewrite prednK.
  by rewrite /VX card_mx card_TX mul1n.
by rewrite expn_gt0.
Qed.

Notation "u *d w" := (scp.dotproduct u w).
Notation "u \*d w" := (scp.dotproduct_rv u w).

Lemma smc_scalar_product_is_correct sa sb ra yb xa xb :
  is_scalar_product scp.dotproduct (
      @smc_scalar_product_traces TX VX scp.dotproduct sa sb ra yb xa xb).
Proof.
rewrite smc_scalar_product_traces_ok /is_scalar_product /=.
symmetry.
rewrite (scp.dot_productC (xa+sa) xb).
rewrite !scp.dot_productDr.
rewrite scp.dot_productC.
rewrite (scp.dot_productC xb sa).
rewrite (scp.dot_productC (xb+sb) sa).
rewrite scp.dot_productDr.
(* Weird: without making it as a lemma, the ring tactic fails. *)
have // ->: xa *d xb + sa *d xb + (sa *d sb - ra) - yb - (sa *d xb + sa *d sb) + ra + yb = xa *d xb.
  by ring.
Qed.

Definition scalar_product_uncurry (o: VX * VX * TX * TX * VX * VX)
  : smc_scalar_product_party_tracesT VX :=
  let '(sa, sb, ra, yb, xa, xb) := o in
  (smc_scalar_product_traces scp.dotproduct sa sb ra yb xa xb).

Record scalar_product_random_inputs :=
  ScalarProductRandomInputs {
    x1 : {RV P -> VX};
    x2 : {RV P -> VX};
    s1 : {RV P -> VX};
    s2 : {RV P -> VX};
    r1 : {RV P -> TX};
    y2 : {RV P -> TX};
 
    (* TODO: prove others via these basic hypotheses
    x1_indep : P |= x1 _|_ [%x2, s1, s2, r1, y2];
    x2_indep : P |= x2 _|_ [%x1, s1, s2, r1, y2];
    *)

    x2s2x1s1r1_y2_indep : P |= [% x2, s2, x1, s1, r1] _|_ y2;
    x1s1r1_x2_indep : P |= [%x1, s1, r1] _|_ x2;
    s1_s2_indep : P |= s1 _|_ s2;
    s1s2_r1_indep : P |= [% s1, s2] _|_ r1;
    x2_indep : P |= [% x1, s1, r1] _|_ x2;
    y2_x1x2s1s2r1_indep : P |= y2 _|_ [% x1, x2, s1, s2, r1];
    s1_x1x2s1s2_indep : P |= s1 _|_ [% x1, x2, s1, s2];
    s2_x1s1r1x2_indep : P |= s2 _|_ [% x1, s1, r1, x2];
    x2s2_x1s1_indep : P |= [%x2, s2] _|_ [%x1, s1];
    x1_s1_indep : P |= x1 _|_ s1;
    s1_x1x2s2_indep : P |= s1 _|_ [%x1, [%x2, s2]];
    s1x2x1x2_r1_indep : P |= [% s1, s2, x1, x2] _|_ r1;
    x2s2_x1_indep : P |= [%x2, s2] _|_ x1;

    neg_py2_unif : `p_ (neg_RV y2) = fdist_uniform card_TX;

    ps1_unif : `p_ s1 = fdist_uniform card_VX;
    ps2_unif : `p_ s2 = fdist_uniform card_VX;
    py2_unif : `p_ y2 = fdist_uniform card_TX;
    pr1_unif : `p_ r1 = fdist_uniform card_TX;
  }.

Variable inputs: scalar_product_random_inputs.

Definition scalar_product_RV (inputs : scalar_product_random_inputs) :
  {RV P -> smc_scalar_product_party_tracesT VX} :=
    scalar_product_uncurry `o
   [%s1 inputs, s2 inputs, r1 inputs, y2 inputs, x1 inputs, x2 inputs].

Let alice_traces : RV (smc_scalar_product_tracesT VX) P :=
      (fun t => tnth t 0) `o scalar_product_RV inputs.

Let bob_traces : RV (smc_scalar_product_tracesT VX) P :=
      (fun t => tnth t 1) `o scalar_product_RV inputs.

Definition scalar_product_is_leakage_free :=
  `H(x2 inputs | alice_traces) = `H `p_ (x2 inputs) /\
  `H(x1 inputs | bob_traces) = `H `p_ (x1 inputs).

Let x1 := x1 inputs.
Let s1 := s1 inputs.
Let r1 := r1 inputs.
Let x2 := x2 inputs.
Let s2 := s2 inputs.
Let y2 := y2 inputs.
Let x1' : {RV P -> VX} := x1 \+ s1.
Let x2' : {RV P -> VX} := x2 \+ s2.
Let r2 : {RV P -> TX} := (s1 \*d s2) \- r1.
Let t : {RV P -> TX} := x1' \*d x2 \+ r2 \- y2.
Let y1 : {RV P -> TX} := t \- (x2' \*d s1) \+ r1.
Let data := (sum TX VX).
Let one x : data := inl x.
Let vec x : data := inr x.

(* TODO: move elsewhere *)
Lemma cond_entropyC (A B C : finType)
  (X: {RV P -> A}) (Y: {RV P -> B}) (Z: {RV P -> C}) :
  `H(X | [% Y, Z]) = `H(X | [% Z, Y]).
Proof.
rewrite /centropy_RV /centropy/=.
rewrite (reindex (fun p : C * B => (p.2, p.1))) /=; last first.
  by exists (fun p : B * C => (p.2, p.1)) => -[b c].
apply: eq_bigr => -[c b] _ /=.
rewrite !snd_RV2 -!pr_eqE' pr_eq_pairC.
congr (_ * _).
rewrite /centropy1; congr (- _).
rewrite /jcPr !snd_RV2.
apply: eq_bigr => a _.
by rewrite !setX1 !Pr_set1 -!pr_eqE' !pr_eq_pairA pr_eq_pairAC (pr_eq_pairC Z).
Qed.

Let alice_traces_from_view xs : 11.-bseq _ :=
  let '(x1, s1, r1, x2', t, y1) := xs in
  [bseq one y1; one t; vec x2'; one r1; vec s1; vec x1].

Lemma alice_traces_ok :
  alice_traces = alice_traces_from_view `o [%x1, s1, r1, x2', t, y1].
Proof.
apply: boolp.funext => x /=.
rewrite /alice_traces /scalar_product_RV /comp_RV /=.
by rewrite smc_scalar_product_traces_ok.
Qed.

Lemma alice_traces_entropy :
  `H(x2 | alice_traces) = `H(x2 | [%x1, s1, r1, x2', t, y1]).
Proof.
transitivity (`H(x2 | [% alice_traces, [%x1, s1, r1, x2', t, y1]])).
  pose f (xs : smc_scalar_product_tracesT VX) :=
    if xs is Bseq [:: inl y1; inl t; inr x2';
                      inl r1; inr s1; inr x1] _
    then (x1, s1, r1, x2', t, y1)
    else (0, 0, 0, 0, 0, 0).
  have fK : cancel alice_traces_from_view f by move=> [] [] [] [] [].
  have -> : [% x1, s1, r1, x2', t, y1] = f `o alice_traces.
    by apply: boolp.funext => x /=; rewrite alice_traces_ok /comp_RV fK.
  by rewrite scp.fun_cond_removal.
by rewrite alice_traces_ok cond_entropyC scp.fun_cond_removal.
Qed.

Let bob_traces_from_view xs : 11.-bseq _ :=
  let '(x2, s2, x1', r2, y2) := xs in
  [:: one y2; vec x1'; one r2; vec s2; one y2; vec x2].

Lemma bob_traces_ok :
  bob_traces = bob_traces_from_view `o [%x2, s2, x1', r2, y2].
Proof.
apply: boolp.funext => x /=.
rewrite /bob_traces /scalar_product_RV /comp_RV /=.
by rewrite smc_scalar_product_traces_ok.
Qed.

Lemma bob_traces_entropy :
  `H(x1 | bob_traces) = `H(x1 | [%x2, s2, x1', r2, y2]).
Proof.
transitivity (`H(x1 | [% bob_traces, [%x2, s2, x1', r2, y2]])).
  pose f (xs : 11.-bseq data) :=
    if xs is Bseq [:: inl y2; inr x1'; inl r2;
                      inr s2; inl _; inr x2] _
    then (x2, s2, x1', r2, y2)
    else (0, 0, 0, 0, 0).
  have fK : cancel bob_traces_from_view f by move=> [] [] [] [] [].
  have -> : [%x2, s2, x1', r2, y2] = f `o bob_traces.
    by apply: boolp.funext => x; rewrite bob_traces_ok /comp_RV fK.
  by rewrite scp.fun_cond_removal.
by rewrite bob_traces_ok cond_entropyC scp.fun_cond_removal.
Qed.

Let pnegy2_unif : `p_ (neg_RV y2) = fdist_uniform card_TX.
Proof.
rewrite -(scp.neg_RV_dist_eq (py2_unif inputs)).
exact: (py2_unif inputs).
Qed.

Let x2s2_x1'_indepP : P |= [% x2, s2] _|_ x1'.
Proof.
have px1_s1_unif: `p_ (x1 \+ s1 : {RV P -> _}) = fdist_uniform card_VX.
  rewrite -(add_RV_unif x1 s1) ?ps1_unif //.
  exact: x1_s1_indep.
have H := @lemma_3_5' T (VX * VX)%type VX P x1 s1 [%x2, s2] (s1_x1x2s2_indep inputs) q card_VX (ps1_unif inputs).
rewrite inde_rv_sym in H.
exact: H.
Qed.

Let x2s2x1s1r2_y2_indep :
   P |= [% x2, s2, x1, s1, r1] _|_ y2 ->
   P |= [% x2, s2, x1, s1, r2] _|_ y2.
Proof.
pose f := fun (vs : (VX * VX * VX * VX * TX)) =>
  let '(xb, sb, xa, sa, ra) := vs in (xb, sb, xa, sa, sa *d sb - ra).
pose g := fun (ws : TX) => ws.    (* because idfun causes error. *)
by apply_inde_rv_comp f g.
Qed.

Let x2s2x1'r2_y2_indep :
  P |= [% x2, s2, x1, s1, r2] _|_ y2 ->
  P |= [% x2, s2, x1', r2] _|_ y2.
Proof.
pose f := fun (vs : (VX * VX * VX * VX * TX)) =>
  let '(xb, sb, xa, sa, rb) := vs in (xb, sb, xa + sa, rb).
pose g := fun (ws : TX) => ws.
by apply_inde_rv_comp f g.
Qed.

Let x2s2x1'r2_y2_indepP :=
  x2s2x1'r2_y2_indep (x2s2x1s1r2_y2_indep (x2s2x1s1r1_y2_indep inputs)).

Let x1x2s2x1'r2_y2_indep :
  P |= [% x2, s2, x1, s1, r2] _|_ y2 ->
  P |= [% x1, [%x2, s2, x1', r2]] _|_ y2.
Proof.
rewrite /x1'.
pose f := fun (vs : (VX * VX * VX * VX * TX)) =>
  let '(xb, sb, xa, sa, rb) := vs in (xa, (xb, sb, xa + sa, rb)).
pose g := fun (ws : TX) => ws.
by apply_inde_rv_comp f g.
Qed.

Let x1x2s2x1'r2_y2_indepP :=
  x1x2s2x1'r2_y2_indep (x2s2x1s1r2_y2_indep (x2s2x1s1r1_y2_indep inputs)).

Let x1x2s2x1'_r2_indep :
  P |= [% x1, [% x2, s2, x1']] _|_ r2.
Proof.
rewrite inde_rv_sym /r2 scp.sub_RV_eq.
apply: (@lemma_3_5' _ _ _ _ _ _ _ _ _ card_TX); last first.
  by rewrite -(@scp.neg_RV_dist_eq _ _ _ card_TX) pr1_unif.
rewrite inde_rv_sym.
apply: scp.neg_RV_inde_eq.
pose f := fun (vs: (VX * VX * VX * VX)) =>
  let '(sa, sb, xa, xb) := vs in (sa *d sb, (xa, (xb, sb, xa + sa))).
pose g := fun (ws : TX) => ws.
have := s1x2x1x2_r1_indep inputs.
by apply_inde_rv_comp f g.
Qed.

Let x2s2x1'_r2_indep : P |= [% x2, s2, x1'] _|_ r2.
Proof.
have := x1x2s2x1'_r2_indep.
pose f := fun (vs: (VX * (VX * VX * VX))) =>
  let '(xa, (xb, sb, xa')) := vs in (xb, sb, xa').
pose g := fun (ws : TX) => ws.
by apply_inde_rv_comp f g.
Qed.

(* Use all hypotheses of the secret inputs and random variables,
   and all technical lemmas about intermediate results,
   to prove information leakage free equations in Sec.[III.C]{Shen2007}

   H(x2 | VIEW_1^{\pi_2}) = H(x2) ... Alice obtain no new knowledge about `x2` from the protocol
   H(x1 | VIEW_2^{\pi_2}) = H(x1) ... Bob obtain no new knowledge about `x1` from the protocol

  *)

Let proof_alice := scp.pi2_alice_is_leakage_free_proof
      (y2_x1x2s1s2r1_indep inputs)
      (s2_x1s1r1x2_indep inputs)
      (x1s1r1_x2_indep inputs) pnegy2_unif (ps2_unif inputs).

Check proof_alice.

Let proof_bob := scp.pi2_bob_is_leakage_free_proof
      (card_rVTX:=card_VX)(r1:=r1)(y2:=y2)
      x2s2_x1'_indepP x2s2x1'r2_y2_indepP x1x2s2x1'r2_y2_indepP
      x2s2x1'_r2_indep x1x2s2x1'_r2_indep
      (s1_x1x2s1s2_indep inputs) (x2s2_x1_indep inputs) (ps1_unif inputs).

Check proof_bob.

Theorem scalar_product_is_leakage_freeP :
  scalar_product_is_leakage_free.
Proof.
split.
- rewrite alice_traces_entropy.
  exact: proof_alice.
- rewrite bob_traces_entropy.
- exact: proof_bob.
Qed.

End information_leakage_proof.

End pi2.
