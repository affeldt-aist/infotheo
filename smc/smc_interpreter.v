From HB Require Import structures.
Require Import Reals.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix Rstruct ring.
Require Import ssrR Reals_ext realType_ext logb ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy smc graphoid smc_entropy.

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
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope chap2_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

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

Definition step (A : Type) (ps : seq proc) (trace : seq data)
  (yes no : proc * seq data -> A) (i : nat) : A :=
  let ps := nth Fail ps in
  let p := ps i in
  let nop := no (p, trace) in
  match p with
  | Recv frm f =>
      if ps frm is Send dst v _ then
        if dst == i then yes (f v, v::trace) else nop
      else nop
  | Send dst w next =>
      if ps dst is Recv frm _ then
        if frm == i then yes (next, trace) else nop
      else nop
  | Init d next =>
      yes (next, d::trace)
  | Ret d =>
      yes (Finish, d :: trace)
  | Finish | Fail =>
      nop
  end.

Fixpoint interp h (ps : seq proc) (traces : seq (seq data)) :=
  if h is h.+1 then
    if has (fun i => step ps [::] (fun=>true) (fun=>false) i)
        (iota 0 (size ps)) then
      let ps_trs' := [seq step ps (nth [::] traces i) idfun idfun i
                     | i <- iota 0 (size ps)] in
      let ps' := unzip1 ps_trs' in
      let trs' := unzip2 ps_trs' in
        interp h ps' trs'
    else (ps, traces)
  else (ps, traces).
End interp.

About interp.

Arguments Finish {data}.
Arguments Fail {data}.

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

Definition traces (s: seq (seq data)) :=
if s is [:: a; b; c] then
  Some (if a is [:: a1; a2; a3; a4; a5; a6] then Some (a1, a2, a3, a4, a5, a6)
        else None,
        if b is [:: b1; b2; b3; b4; b5; b6] then Some (b1, b2, b3, b4, b5, b6)
        else None)
else None.

Lemma smc_scalar_product_traces_ok :
  traces (smc_scalar_product 11).2 = Some (Some (
     one ya,
     one t,
     vec xb',
     one ra,
     vec sa, 
     vec xa
  ), Some (
     one yb,
     vec xa',
     one rb,
     vec sb,
     one yb,
     vec xb
  )).
Proof. reflexivity. Qed.

Definition smc_scalar_product_alice_tracesT :=
  option (data * data * data * data * data * data).

Definition smc_scalar_product_bob_tracesT :=
  option (data * data * data * data * data * data).

(* the above two types are the same; merely a coincidence? *)

Definition smc_scalar_product_party_tracesT :=
  option (smc_scalar_product_alice_tracesT * smc_scalar_product_bob_tracesT).

Definition is_scalar_product (trs: smc_scalar_product_party_tracesT) :=
  let '(ya, xa) := if Option.bind fst trs is Some (inl ya, _, _, _, _, inr xa)
                   then (ya, xa) else (0, 0) in
  let '(yb, xb) := if Option.bind snd trs is Some (inl yb, _, _, _, _, inr xb)
                   then (yb, xb) else (0, 0) in
  xa *d xb = ya + yb.

End scalar_product.

Section pi2.
  
Section information_leakage_def.

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

Notation "u *d w" := (smc_entropy_proofs.dotproduct u w).
Notation "u \*d w" := (smc_entropy_proofs.dotproduct_rv u w).

Lemma smc_scalar_product_is_correct sa sb ra yb xa xb :
  is_scalar_product smc_entropy_proofs.dotproduct (
      traces (@smc_scalar_product TX VX smc_entropy_proofs.dotproduct sa sb ra yb xa xb 11).2).
Proof.
rewrite smc_scalar_product_traces_ok /is_scalar_product /=.
symmetry.
rewrite (smc_entropy_proofs.dot_productC (xa+sa) xb).
rewrite !smc_entropy_proofs.dot_productDr.
rewrite smc_entropy_proofs.dot_productC.
rewrite (smc_entropy_proofs.dot_productC xb sa).
rewrite (smc_entropy_proofs.dot_productC (xb+sb) sa).
rewrite smc_entropy_proofs.dot_productDr.
(* Weird: without making it as a lemma, the ring tactic fails. *)
have // ->: xa *d xb + sa *d xb + (sa *d sb - ra) - yb - (sa *d xb + sa *d sb) + ra + yb = xa *d xb.
  by ring.
Qed.

Definition scalar_product_uncurry (o: VX * VX * TX * TX * VX * VX) :=
  let '(sa, sb, ra, yb, xa, xb) := o in
  (smc_scalar_product smc_entropy_proofs.dotproduct sa sb ra yb xa xb 11).2.

Record scalar_product_random_inputs :=
  ScalarProductRandomInputs {
    x1 : {RV P -> VX};
    x2 : {RV P -> VX};
    s1 : {RV P -> VX};
    s2 : {RV P -> VX};
    r1 : {RV P -> TX};
    y2 : {RV P -> TX};

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

    neg_py2_unif : `p_ (neg_RV y2) = fdist_uniform card_TX;

    ps1_unif : `p_ s1 = fdist_uniform card_VX;
    ps2_unif : `p_ s2 = fdist_uniform card_VX;
    py2_unif : `p_ y2 = fdist_uniform card_TX;
    pr1_unif : `p_ r1 = fdist_uniform card_TX;
  }.

Record scalar_product_intermediate_vars (inputs: scalar_product_random_inputs)  :=
  ScalarProductIntermediateVars {
    x1' : {RV P -> VX};
    x2' : {RV P -> VX};
    t   : {RV P -> TX};
    y1  : {RV P -> TX};
    r2  : {RV P -> TX};

    x1'_eqE  : x1' = x1 inputs \+ s1 inputs; 
    x2'_eqE  : x2' = x2 inputs \+ s2 inputs; 
    t_eqE    : t = x1' \*d x2 inputs \+ r2 \- y2 inputs;
    y1_eqE   : y1 = t \- x2' \*d s1 inputs \+ r1 inputs;
    r2_eqE   : r2 = s1 inputs \*d s2 inputs \- r1 inputs;

    x2s2_x1'_indep : P |= [% x2 inputs, s2 inputs ] _|_ x1';
    x1x2s2x1'r2_y2_indep : P |= [% x1 inputs, x2 inputs, s2 inputs, x1', r2] _|_ y2 inputs;
    x2s2x1'_r2_indep : P |= [% x2 inputs, s2 inputs, x1'] _|_ r2;
    x1x2s2x1'_r2_indep : P |= [% x1 inputs, x2 inputs, s2 inputs, x1'] _|_ r2;

    pr2_unif : `p_ r2 = fdist_uniform card_TX;
  }.

Variable inputs: scalar_product_random_inputs.

Definition scalar_product_RV (inputs : scalar_product_random_inputs) :
  {RV P -> seq (seq (data VX))} :=
    scalar_product_uncurry `o
   [%s1 inputs, s2 inputs, r1 inputs, y2 inputs, x1 inputs, x2 inputs].

Let alice_traces : RV (smc_scalar_product_alice_tracesT VX) P :=
      Option.bind fst `o (@traces _ _ `o scalar_product_RV inputs).

Let bob_traces : RV (smc_scalar_product_bob_tracesT VX) P :=
      Option.bind snd `o (@traces _ _ `o scalar_product_RV inputs).

Definition scalar_product_is_leakgae_free :=
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

Lemma cond_entropyC (A B C : finType)
  (X: {RV P -> A}) (Y: {RV P -> B}) (Z: {RV P -> C}) :
  `H(X | [% Y, Z]) = `H(X | [% Z, Y]).
Proof.
rewrite /cond_entropy /=.
rewrite (reindex (fun p : C * B => (p.2, p.1))) /=; last first.
  by exists (fun p : B * C => (p.2, p.1)) => -[b c].
apply: eq_bigr => -[c b] _ /=.
rewrite !snd_RV2 -!pr_eqE' pr_eq_pairC.
congr (_ * _).
rewrite /cond_entropy1; congr (- _).
rewrite /jcPr !snd_RV2.
apply: eq_bigr => a _.
by rewrite !setX1 !Pr_set1 -!pr_eqE' !pr_eq_pairA pr_eq_pairAC (pr_eq_pairC Z).
Qed.

Lemma alice_traces_ok :
  `H(x2 | alice_traces) = `H(x2 | [%x1, s1, r1, x2', t, y1]).
Proof.
transitivity (`H(x2 | [% alice_traces, [%x1, s1, r1, x2', t, y1]])).
  pose f (xs : option (data * data * data * data * data * data)) :=
    if xs is Some (inl y1, inl t, inr x2',
                   inl r1, inr s1, inr x1)
    then (x1, s1, r1, x2', t, y1)
    else (0, 0, 0, 0, 0, 0).
  have -> : [% x1, s1, r1, x2', t, y1] = f `o alice_traces by [].
  by rewrite smc_entropy_proofs.fun_cond_removal.
pose g xs :=
  let '(x1, s1, r1, x2', t, y1) := xs in
  Some (one y1, one t, vec x2', one r1, vec s1, vec x1).
have -> : alice_traces = g `o [% x1, s1, r1, x2', t, y1] by [].
by rewrite cond_entropyC smc_entropy_proofs.fun_cond_removal.
Qed.

Lemma bob_traces_ok :
  `H(x1 | bob_traces) = `H(x1 | [%x2, s2, x1', r2, y2]).
Proof.
transitivity (`H(x1 | [% bob_traces, [%x2, s2, x1', r2, y2]])).
  pose f (xs : option (data * data * data * data * data * data)) :=
    if xs is Some (inl y2, inr x1', inl r2,
                   inr s2, inl _, inr x2)
    then (x2, s2, x1', r2, y2)
    else (0, 0, 0, 0, 0).
  have -> : [%x2, s2, x1', r2, y2] = f `o bob_traces by [].
  by rewrite smc_entropy_proofs.fun_cond_removal.
pose g xs :=
  let '(x2, s2, x1', r2, y2) := xs in
  Some (one y2, vec x1', one r2, vec s2, one y2, vec x2).
have -> : bob_traces = g `o [%x2, s2, x1', r2, y2] by [].
by rewrite cond_entropyC smc_entropy_proofs.fun_cond_removal.
Qed.

Let pnegy2_unif :
  `p_ (neg_RV y2) = fdist_uniform card_TX.
Proof. rewrite -(smc_entropy.smc_entropy_proofs.neg_RV_dist_eq (py2_unif inputs)).
exact: (py2_unif inputs). Qed.

Let x2s2_x1'_indepP :
  P |= [% x2, s2] _|_ x1'.
Proof.
have px1_s1_unif: `p_ (x1 \+ s1 : {RV P -> _}) = fdist_uniform card_VX.
  rewrite -(add_RV_unif x1 s1) ?ps1_unif //.
  exact: x1_s1_indep.
have H:= @lemma_3_5' T (VX * VX)%type VX P q x1 s1 [%x2, s2] card_VX (ps1_unif inputs) (s1_x1x2s2_indep inputs).
rewrite inde_rv_sym in H.
exact: H.
Qed.

Let proof_alice := (smc_entropy.smc_entropy_proofs.pi2_alice_is_leakage_free_proof
      (y2_x1x2s1s2r1_indep inputs)
      (s2_x1s1r1x2_indep inputs)
      (x1s1r1_x2_indep inputs) pnegy2_unif (ps2_unif inputs)).

About smc_entropy.smc_entropy_proofs.pi2_bob_is_leakage_free_proof.

Fail Let proof_bob := (smc_entropy.smc_entropy_proofs.pi2_bob_is_leakage_free_proof
      (x2s2_x1'_indepP)
      (s2_x1s1r1x2_indep inputs)
      (x1s1r1_x2_indep inputs) pnegy2_unif (ps2_unif inputs)).


End information_leakage_def.

(*

Notation x1' := (get_vec_RV none_VX bob 1 inputs).
Notation x2' := (get_vec_RV none_VX alice 2 inputs).
Notation t := (get_one_RV none_TX alice 1 inputs).
Notation y1 := (get_one_RV none_TX alice 0 inputs).
Notation r2 := (get_one_RV none_TX bob 2 inputs).

Let r2_eqE :
  r2 = s1 inputs \*d s2 inputs \- r1 inputs.
Proof. by apply boolp.funext. Qed.

Let x1'_eqE :
  x1' = x1 inputs \+ s1 inputs. 
Proof. by apply boolp.funext. Qed.

Let x2'_eqE :
  x2' = x2 inputs \+ s2 inputs.
Proof. by apply boolp.funext. Qed.

Let t_eqE :
  t = x1' \*d x2 inputs \+ r2 \- y2 inputs.
Proof. by apply boolp.funext. Qed.

Let y1_eqE :
  y1 = t \- x2' \*d s1 inputs \+ r1 inputs.
Proof. by apply boolp.funext. Qed.

Let pr2_unif :
  `p_ r2 = fdist_uniform card_TX.
Proof.
exact: smc_entropy.smc_entropy_proofs.ps1_dot_s2_r_unif
    (pr1_unif inputs) (s1_s2_indep inputs) (s1s2_r1_indep inputs).
Qed.

Fail Check [% x2 inputs, s2 inputs ] : {RV P -> VX}.
(* For RV2 pairs: if lemma asks {RV P -> VX } but we have {TV P -> (VX * VX) },
   we need to duplicate the lemma and proof to support them?
*)

Let x2s2_x1'_indep :
  P |= [% x2 inputs, s2 inputs ] _|_ x1'.
Proof.
rewrite inde_rv_sym x1'_eqE.
have px1_s1_unif: `p_ (x1 inputs \+ s1 inputs) = fdist_uniform card_VX.
  move => t.
  have Ha := @add_RV_unif T VX P m.+1 (x1 inputs) (s1 inputs) card_VX (ps1_unif inputs) (x1_s1_indep inputs).
    rewrite /add_RV // in Ha.
    Fail rewrite Ha.
    (*Set Printing All. Problem: card_A in lemma_3_4 is #|A| = n.+1; card_VX here is #|VX| = m.+2; *)
    Fail exact: Ha.
    admit.
have H := @lemma_3_5' T (VX * VX)%type VX P m.+1 (x1 inputs) (s1 inputs) [%x2 inputs, s2 inputs] card_VX px1_s1_unif.
Abort.

About smc_entropy.smc_entropy_proofs.pi2_bob_is_leakage_free_proof.

Let vars :=
  ScalarProductIntermediateVars x1'_eqE x2'_eqE t_eqE y1_eqE r2_eqE pr2_unif.

Let pnegy2_unif :
  `p_ (neg_RV (y2 inputs)) = fdist_uniform card_TX.
Proof. rewrite -(smc_entropy.smc_entropy_proofs.neg_RV_dist_eq (py2_unif inputs)).
exact: (py2_unif inputs).
Qed.

Let leakage_free_proof :=
  ScalarProductInformationLeakageFree (inputs:=inputs)(vars:=vars)
    (smc_entropy.smc_entropy_proofs.pi2_alice_is_leakage_free_proof
      (y2_x1x2s1s2r1_indep inputs)
      (s2_x1s1r1x2_indep inputs)
      (x1s1r1_x2_indep inputs) pnegy2_unif (ps2_unif inputs)).
*)

End pi2.
