From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg ring.
From mathcomp Require Import Rstruct reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_proba smc_entropy smc_interpreter smc_tactics.
Require Import scalar_product_program.

(********************************************************************************)
(*                                                                              *)
(* Lemmas:                                                                      *)
(* ```                                                                          *)
(* smc_scalar_product_ok           == the proof shows the interpretation of     *)
(*                                    the SMC scalar program always terminates  *)
(*                                    correctly                                 *)
(* smc_scalar_product_traces_ok    == the proof shows the interpretation of the *)
(*                                    SMC scalar program always yields          *)
(*                                    input traces that match the specification *)
(*                                    of fixed-length list                      *)
(* scalar_product_is_leakage_freeP == the proof shows the information leakage   *)
(*                                    freedom property of the protocol          *)
(* ```                                                                          *)
(*                                                                              *)
(* The correct proofs are formalization of:                                     *)
(* A practical approach to solve secure multi-party computation problems        *)
(* Du, W., Zhan, J.Z.                                                           *)
(* In: Workshop on New Security Paradigms (NSPW 2002), Virginia Beach, VA, USA  *)
(* September 23-26, 2002. pp. 127–135. ACM (2002).                              *)
(* https://doi.org/10.1145/844102.844125                                        *)
(*                                                                              *)
(* The information leakage freedom proof is formalization of:                   *)
(* Information-theoretically secure number-product protocol                     *)
(* Shen, C.H., Zhan, J., Wang, D.W., Hsu, T.S., Liau, C.J.                      *)
(* In: 2007 International Conference on Machine Learning and Cybernetics.       *)
(* vol. 5, pp. 3006–3011 (2007). https://doi.org/10.1109/ICMLC.2007.4370663     *)
(*                                                                              *)
(********************************************************************************)

Import GRing.Theory.
Import Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

Section proof.

Context {R : realType}.
Variable n m : nat.
Variable T : finType.
Variable P : R.-fdist T.

Section trace_correctness_proof.

Variable TX : finComRingType.
Variable VX : lmodType TX. (* vector is not ringType (mul)*)

Definition data := (TX + VX)%type.
Definition one x : data := inl x.
Definition vec x : data := inr x.

Variables (sa sb: VX) (ra yb: TX) (xa xb: VX).
Variable dotproduct : VX -> VX -> TX.
Local Notation "u *d w" := (dotproduct u w).

Let xa' := xa + sa.
Let xb' := xb + sb.
Let rb := sa *d sb - ra.
Let t := xa' *d xb + rb - yb.
Let ya := t - xb' *d sa + ra.

Lemma smc_scalar_product_ok :
  smc_scalar_product dotproduct sa sb ra yb xa xb 11 =
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

Lemma smc_scalar_product_traces_ok :
  smc_scalar_product_traces dotproduct sa sb ra yb xa xb =
    [tuple
     [bseq one ya; one t; vec xb'; one ra; vec sa; vec xa];
     [bseq one yb; vec xa'; one rb; vec sb; one yb; vec xb];
     [bseq one ra; vec sb; vec sa]].
Proof. by apply/val_inj/(inj_map val_inj); rewrite interp_traces_ok. Qed.

End trace_correctness_proof.

Section result_correctness_proof.

Let TX := [the finComRingType of 'I_m.+2].
Let VX := 'rV[TX]_n.
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

End result_correctness_proof.

Section information_leakage_proof.

Let TX := [the finComRingType of 'I_m.+2].
Let VX := 'rV[TX]_n.
Notation "u *d w" := (scp.dotproduct u w).
Notation "u \*d w" := (scp.dotproduct_rv u w).

Lemma card_TX : #|TX| = m.+2.
Proof. by rewrite card_ord. Qed.

Let q := (m.+2 ^ n).-1.
Lemma card_VX : #|VX| = q.+1.
Proof.
by rewrite prednK ?expn_gt0// /VX card_mx card_TX mul1n.
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

    (* Each random variable is independ of any others excluding itself;
       other necessary independence premises can be proven from these
       primitive ones.

       TODO: the type difference between vector and scalar prevents us
       from having something like:

       Hindep : {homo nth x1 [:: x1; x2; s1; s2; r1; y2] : i j / i < j >-> P |= i _|_ j}%N.
    *)
    x1_indep : P |= [%x2, s1, s2, r1, y2] _|_ x1;
    x2_indep : P |= [%x1, s1, s2, r1, y2] _|_ x2;
    y2_indep : P |= [%x2, s2, x1, s1, r1] _|_ y2;
    s1_indep : P |= [%x2, s2, x1, y2, r1] _|_ s1;
    s2_indep : P |= [%x2, s1, x1, y2, r1] _|_ s2;
    r1_indep : P |= [%x2, s1, x1, y2, s2] _|_ r1;

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

Let x1s1r1_x2_indep :
  P |= [%x1, s1, r1] _|_ x2.
Proof.
have := x2_indep inputs.
pose f := fun (vs: (VX * VX * VX * TX * TX)) =>
  let '(xa, sa, sb, ra, yb) := vs in (xa, sa, ra).
pose g := fun (ws : VX) => ws.
apply: (inde_RV_comp f g).
Qed.

Let data := (sum TX VX).
Let one x : data := inl x.
Let vec x : data := inr x.

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
by rewrite alice_traces_ok centropyC scp.fun_cond_removal.
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
by rewrite bob_traces_ok centropyC scp.fun_cond_removal.
Qed.

Let pnegy2_unif : `p_ (neg_RV y2) = fdist_uniform card_TX.
Proof.
rewrite -(scp.neg_RV_dist_eq (py2_unif inputs)).
exact: (py2_unif inputs).
Qed.

Let x2s2_x1'_indepP : P |= [% x2, s2] _|_ x1'.
Proof.
have x1_s1_indep : P |= x1 _|_ s1.
  have H := x1_indep inputs.
  rewrite inde_RV_sym in H.
  move : H.
  pose f := fun (vs : (VX * VX * VX * TX * TX)) =>
    let '(xb, sa, sb, ra, yb) := vs in sa.
  pose g := fun (ws : VX) => ws.
  by apply_inde_rv_comp g f.
have s1_x1x2s2_indep : P |= s1 _|_ [%x1, [%x2, s2]].
  have H := s1_indep inputs.
  rewrite inde_RV_sym in H.
  move : H.
  pose f := fun (vs : (VX * VX * VX * TX * TX)) =>
    let '(xb, sb, xa, yb, ra) := vs in (xa, (xb, sb)).
  pose g := fun (ws : VX) => ws.
  by apply_inde_rv_comp g f.
have px1_s1_unif: `p_ (x1 \+ s1 : {RV P -> _}) = fdist_uniform card_VX.
  by rewrite -(add_RV_unif x1 s1) ?ps1_unif //.
have H := @lemma_3_5' _ T (VX * VX)%type VX P x1 s1 [%x2, s2] s1_x1x2s2_indep q card_VX (ps1_unif inputs).
rewrite inde_RV_sym in H.
exact: H.
Qed.

Let x2s2x1s1r2_y2_indep :
   P |= [% x2, s2, x1, s1, r2] _|_ y2.
Proof.
have := y2_indep inputs.
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
  x2s2x1'r2_y2_indep x2s2x1s1r2_y2_indep.

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
  x1x2s2x1'r2_y2_indep x2s2x1s1r2_y2_indep.

Let x1x2s2x1'_r2_indep :
  P |= [% x1, [% x2, s2, x1']] _|_ r2.
Proof.
rewrite inde_RV_sym /r2 scp.sub_RV_eq.
apply: (@lemma_3_5' _ _ _ _ _ _ _ _ _ _ card_TX); last first.
  by rewrite -(@scp.neg_RV_dist_eq _ _ _ _ card_TX) pr1_unif.
rewrite inde_RV_sym.
apply: scp.neg_RV_inde_eq.
have := r1_indep inputs.
pose f := fun vs : (VX * VX * VX * TX * VX) =>
  let '(xb, sa, xa, yb, sb) := vs in (sa *d sb, (xa, (xb, sb, xa + sa))).
pose g := fun (ws : TX) => ws.
by apply_inde_rv_comp f g.
Qed.

Let x2s2x1'_r2_indep : P |= [% x2, s2, x1'] _|_ r2.
Proof.
have := x1x2s2x1'_r2_indep.
pose f := fun vs : (VX * (VX * VX * VX)) =>
  let '(xa, (xb, sb, xa')) := vs in (xb, sb, xa').
pose g := fun (ws : TX) => ws.
by apply_inde_rv_comp f g.
Qed.

Let y2_x1x2s1s2r1_indep : P |= y2 _|_ [% x1, x2, s1, s2, r1].
Proof.
have := y2_indep inputs.
move/inde_RV_sym.
pose f := fun vs : (VX * VX * VX * VX * TX) =>
  let '(xb, sb, xa, sa, ra) := vs in (xa, xb, sa, sb, ra).
pose g := fun (ws : TX) => ws.
by apply_inde_rv_comp g f.
Qed.

Let s1_x1x2s2_indep : P |= s1 _|_ [% x1, x2, s2].
Proof.
have := s1_indep inputs.
move/inde_RV_sym.
pose f := fun vs : (VX * VX * VX * TX * TX) =>
  let '(xb, sb, xa, sa, ra) := vs in (xa, xb, sb).
pose g := fun (ws : VX) => ws.
by apply_inde_rv_comp g f.
Qed.

Let s2_x1s1r1x2_indep : P |= s2 _|_ [% x1, s1, r1, x2].
have := s2_indep inputs.
move/inde_RV_sym.
pose f := fun vs : (VX * VX * VX * TX * TX) =>
  let '(xb, sa, xa, ya, ra) := vs in (xa, sa, ra, xb).
pose g := fun (ws : VX) => ws.
by apply_inde_rv_comp g f.
Qed.

Let x2s2_x1_indep : P |= [%x2, s2] _|_ x1.
move : (x1_indep inputs).
pose f := fun vs : (VX * VX * VX * TX * TX) =>
  let '(xb, sa, sb, ra, yb) := vs in (xb, sb).
pose g := fun (ws : VX) => ws.
by apply_inde_rv_comp f g.
Qed.

(* Use all hypotheses of the secret inputs and random variables,
   and all technical lemmas about intermediate results,
   to prove information leakage free equations in Sec.[III.C]{Shen2007}

   H(x2 | VIEW_1^{\pi_2}) = H(x2) ... Alice obtain no new knowledge about `x2` from the protocol
   H(x1 | VIEW_2^{\pi_2}) = H(x1) ... Bob obtain no new knowledge about `x1` from the protocol

  *)

Let proof_alice := scp.pi2_alice_is_leakage_free_proof
      y2_x1x2s1s2r1_indep
      s2_x1s1r1x2_indep
      x1s1r1_x2_indep pnegy2_unif (ps2_unif inputs).

Check proof_alice.

Let proof_bob := scp.pi2_bob_is_leakage_free_proof
      (card_rVTX:=card_VX)(r1:=r1)(y2:=y2)
      x1x2s2x1'r2_y2_indepP
      x1x2s2x1'_r2_indep
      s1_x1x2s2_indep x2s2_x1_indep (ps1_unif inputs).

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

End proof.

