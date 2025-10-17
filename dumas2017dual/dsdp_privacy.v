From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap matrix lra.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter smc_tactics.
Require Import smc_proba homomorphic_encryption dsdp_program.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* Formalization of:                                                          *)
(*                                                                            *)
(* Dumas, J. G., Lafourcade, P., Orfila, J. B., & Puys, M. (2017).            *)
(* Dual protocols for private multi-party matrix multiplication               *)
(* and trust computations.                                                    *)
(* Computers & security, 71, 51-70.                                           *)
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

Reserved Notation "u *h w" (at level 40).
Reserved Notation "u ^h w" (at level 40).

Section dsdp_privacy_analysis.
  
Variable T : finType.
Variable P : R.-fdist T.

(* If A is const-RV actually P |= A _|_ A.
   But in the DSDP setting, we don't have such RVs.
*)
Hypothesis neg_self_indep : forall (TA : finType)
  (A : {RV P -> TA}), ~ P |= A _|_ A.

Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.

Let msg := 'I_m.  (* = Z/mZ *)
Let card_msg : #|msg| = m.
Proof. by rewrite card_ord. Qed.

Let enc := enc party msg.
Let pkey := pkey party msg.

Let data := (msg + enc + pkey)%type.
Let d x : data := inl (inl x).
Let e x : data := inl (inr x).
Let k x : data := inr x.

Notation dsdp_traceT := (15.-bseq data).
Notation dsdp_tracesT := (3.-tuple dsdp_traceT).
Notation "u *h w" := (Emul u w).
Notation "u ^h w" := (Epow u w).

Definition dsdp_uncurry (o: Alice.-key Dec msg * Bob.-key Dec msg *
  Charlie.-key Dec msg * msg * msg * msg * msg * msg * msg * msg * msg)
  : dsdp_tracesT :=
  let '(dk_a, dk_b, dk_c, v1, v2 , v3, u1, u2, u3, r2, r3) := o in
  (dsdp_traces dk_a.2 dk_b.2 dk_c.2 v1 v2 v3 u1 u2 u3 r2 r3).

Record dsdp_random_inputs :=
  DSDPRandomInputs {
    dk_a : {RV P -> Alice.-key Dec msg};
    dk_b : {RV P -> Bob.-key Dec msg};
    dk_c : {RV P -> Charlie.-key Dec msg};

    v1 : {RV P -> msg};
    v2 : {RV P -> msg};
    v3 : {RV P -> msg};
    u1 : {RV P -> msg};
    u2 : {RV P -> msg};
    u3 : {RV P -> msg};
    r2 : {RV P -> msg};
    r3 : {RV P -> msg};

    alice_indep : P |= [% dk_a, v1, u1, u2, u3, r2, r3] _|_ [% v2, v3];

    pv1_unif : `p_ v1 = fdist_uniform card_msg;
    pv2_unif : `p_ v2 = fdist_uniform card_msg;
    pv3_unif : `p_ v3 = fdist_uniform card_msg;
    pu2_unif : `p_ u2 = fdist_uniform card_msg;
    pu3_unif : `p_ u3 = fdist_uniform card_msg;
    pr2_unif : `p_ r2 = fdist_uniform card_msg;
    pr3_unif : `p_ r3 = fdist_uniform card_msg;
}.

Variable inputs : dsdp_random_inputs.

Let dk_a := dk_a inputs.
Let dk_b := dk_b inputs.
Let dk_c := dk_c inputs.
Let v1 := v1 inputs.
Let v2 := v2 inputs.
Let v3 := v3 inputs.
Let u1 := u1 inputs.
Let u2 := u2 inputs.
Let u3 := u3 inputs.
Let r2 := r2 inputs.
Let r3 := r3 inputs.
Let vu2 : {RV P -> msg} := v2 \* u2.
Let vu3 : {RV P -> msg} := v3 \* u3.
Let d2  : {RV P -> msg} := vu2 \+ r2.
Let vu3r : {RV P -> msg} := vu3 \+ r3.
Let d3 : {RV P -> msg} := vu3r \+ d2.
Let s : {RV P -> msg} := d3 \- r2 \- r3 \+ u1 \* v1.

Let E_alice_d3 : {RV P -> Alice.-enc msg} := E' alice `o d3.
Let E_charlie_v3 : {RV P -> Charlie.-enc msg} := E' charlie `o v3.
Let E_bob_v2 : {RV P -> Bob.-enc msg} := E' bob `o v2.

Definition dsdp_RV (inputs : dsdp_random_inputs) :
  {RV P -> dsdp_tracesT} :=
    dsdp_uncurry `o
    [% dk_a,
       dk_b,
       dk_c, v1, v2, v3, u1, u2, u3, r2, r3].

Section alice_privacy_analysis.

Local Notation m := m_minus_2.+2.

Let alice_traces : {RV P -> dsdp_traceT} :=
      (fun t => tnth t 0) `o dsdp_RV inputs.

(* Use these two and apply_inde_RV_comp to prove trivial indeps*)
Let alice_inputsT := (Alice.-key Dec msg * msg * msg * msg *
  msg * msg * msg)%type.
Let alice_inputs_RV : {RV P -> alice_inputsT} := [% dk_a, v1, u1, u2, u3, r2, r3].

(* E_charlie_v3 means it is encrypted (so generated) by the key of charlie.
   Therefore, encrypted RVs should be independent of other parties.
   Even other parties can add messages by HE properties, but addition to a RV
   means the independence keeps after the addition.
*)
Hypothesis inde_Echarlie : P |= alice_inputs_RV _|_ E_charlie_v3.
Hypothesis inde_Ebob : P |= alice_inputs_RV _|_ E_bob_v2.

Let alice_view_valuesT := (Alice.-key Dec msg * msg * msg * msg * msg * msg * msg * msg * Alice.-enc msg * Charlie.-enc msg * Bob.-enc msg)%type.

Let alice_view : {RV P -> alice_view_valuesT} :=
  [% dk_a, s, v1 , u1, u2, u3, r2, r3,
      E_alice_d3, E_charlie_v3, E_bob_v2].

Let alice_traces_from_view
  (v : alice_view_valuesT) : 15.-bseq _ :=
    let '(dk_a, s, v1 , u1, u2, u3, r2, r3,
      E_alice_d3, E_charlie_v3, E_bob_v2) := v in
    [bseq d s;
            e (E_alice_d3 : enc);
            e (E_charlie_v3 : enc);
            e (E_bob_v2 : enc);
            d r3; d r2; d u3; d u2; d u1; d v1; k (dk_a : pkey)].

Lemma alice_traces_from_viewP :
  alice_traces = alice_traces_from_view `o alice_view.
Proof.
apply: boolp.funext => x /=.
rewrite /alice_traces /dsdp_RV /comp_RV /= dsdp_traces_ok //=.
have Ha : dsdp_program.k (Alice, Dec, (dk_a x).2) = k (dk_a x).
  (* Rocq doesn't know this is the only case, and it makes both sides equal*)
  by case: dk_a => t. 
rewrite  -[in RHS]Ha //=.
Qed.

Local Definition alice_view_values_from_trace (xs : dsdp_traceT) :
  alice_view_valuesT :=
    let failtrace := (KeyOf Alice Dec 0,
                        0, 0, 0, 0, 0, 0, 0,
                        E' Alice 0, E' Charlie 0, E' Bob 0) in
    if xs is Bseq [:: inl (inl s);
           inl (inr E_alice_d3);
           inl (inr E_charlie_v3);
           inl (inr E_bob_v2);
           inl (inl r3); inl (inl r2); inl (inl u3);
           inl (inl u2); inl (inl u1); inl (inl v1); inr dk_a] _
    then 
         if (E_alice_d3, E_charlie_v3, E_bob_v2, dk_a) is
              ((Alice, d3), (Charlie, v3), (Bob, v2), (Alice, Dec, k_a)) then
            (KeyOf Alice Dec k_a, s, v1 , u1, u2, u3, r2, r3,
               E' Alice d3, E' Charlie v3, E' Bob v2)
         else failtrace
    else failtrace.

Lemma alice_view_values_from_traceP:
   cancel alice_traces_from_view alice_view_values_from_trace.
Proof.
move => [] [] [] [] [] [] [] [] [] [] dk ? ? ? ? ? ? ? a c b //=.
case: a => -[a ma] /=.  (* msg from `case: a`
                           can be case again to get 1. nat a 2. nat a < m*)
case: c => -[c mc] /=.
case: b => -[b mb] /=.
case: dk => -[dk mdk] /=.
by [].
Qed.

Lemma ce_alice_traces_view (w : finType) (v : {RV P -> w}) :
  `H(v | alice_traces ) = `H(v | alice_view ).
Proof.
simpl in *.
transitivity (`H(v | [%alice_traces, alice_view])).
  have -> : alice_view = alice_view_values_from_trace `o alice_traces.
    by apply: boolp.funext => x /= ;
       rewrite alice_traces_from_viewP /comp_RV alice_view_values_from_traceP.
  by rewrite centropy_RV_contraction.
by rewrite alice_traces_from_viewP centropyC centropy_RV_contraction.
Qed.

Let alice_input_view :
  {RV P ->(Alice.-key Dec msg * msg * msg * msg * msg * msg * msg)} :=
  [%dk_a, v1, u1, u2, u3, r2, r3].
Notation alice_input_view_valT :=
  (Alice.-key Dec msg * msg * msg * msg * msg * msg * msg)%type.

Section dotp2.

Notation "x \+ y" := (add_RV x y).  

Definition dotp2 (x y: (msg * msg)) := x.1 * y.1 + x.2 * y.2.

Definition dotp2_solutions (s : msg) : {set (msg * msg) * (msg * msg)} :=
  [set uv in setT `* setT | dotp2 uv.1 uv.2 == s].

Definition dotp2_rv (X Y : {RV P -> (msg * msg)}) : {RV P -> msg} :=
  fun p => dotp2 (X p) (Y p).

Definition dotp2_solutions_rv
  (S : {RV P -> msg}) : {RV P -> {set (msg * msg) * (msg * msg)} } :=
  dotp2_solutions `o S.

Definition us := [%u2, u3].
Definition vs := [%v2, v3].

Definition const_us := [% (fun _ => 1):{RV P -> msg},
  (fun _ => 0):{RV P -> msg}].
Definition vu1 : {RV P -> msg} := v1 \* u1.

Lemma s_alt :
  s = dotp2_rv vs us \+ vu1.
Proof.
rewrite /s /vs /us /d3 /vu3r /d2 /vu3 /vu2 /vu1 /dotp2_rv /dotp2 /add_RV.
apply: boolp.funext => i //=.
ring.
Qed.

Lemma s_alt2 :
  let f := (fun o => let '(u2, u3, v2, v3, v1, u1) := o
              in u2 * v2 + u3 * v3 + v1 * u1) in
  s = f `o [% u2, u3, v2, v3, v1, u1].
Proof.
rewrite /comp_RV /s /vs /us /d3 /vu3r /d2 /vu3 /vu2 /vu1 /dotp2_rv /dotp2 /add_RV.
apply: boolp.funext => i //=.
ring.
Qed.

End dotp2.

(* If an active adversary controls Alice, force `us` always output `(1, 0)`,
   then the key privacy premise `v2 _|_ dotp2_rv us vs` is impossible.

   In contrast, if Alice is an fair player, the probability that `us`
   outputs that specific value `(1, 0)` is 1/m^2.

   Finally, if Bob enforce ZPK check to abort the protocol when that value is
   generated, `v2 _|_ dotp2_rv us vs` is guaranteed, and the protocol
   is secure with that mitigation ("security with abort")
   \cite[\S5.2]{dumas2017dual}.

   Therefore, here we examine the compromised case:

      `us = (1, 0) -> ~ v2 _|_ dotp2_rv us vs`

   and the secure case:

      `us != (1, 0) ->  v2 _|_ dotp2_rv us vs`.
*)
Lemma const_us_is_v2_discloser :
  us = const_us -> dotp2_rv vs us = v2.
Proof.
move->; rewrite /const_us /vs /dotp2_rv /dotp2 /fst /snd /comp_RV.
apply: boolp.funext => i //=.
ring.
Qed.

(* TODO: the secure case *)
Local Definition dec_view : {RV P -> (alice_input_view_valT * msg)} :=
  [%dk_a, s, v1 , u1, u2, u3, r2, r3].
Local Definition eqn1_view :
  {RV P -> (alice_input_view_valT * msg * Alice.-enc msg * Charlie.-enc msg)}
  := [% dec_view, E_alice_d3, E_charlie_v3].
Local Definition eqn2_view :
  {RV P -> (alice_input_view_valT * msg * Alice.-enc msg)} :=
  [% dec_view, E_alice_d3].
 
(* TODO: define types to simplify types in the proof context *)
Hypothesis alice_view_neq0 :
    forall
      (x : alice_input_view_valT * msg * Alice.-enc msg * Charlie.-enc 'I_m)
      (e : Bob.-enc 'I_m),
    `Pr[ [% dec_view, E_alice_d3, E_charlie_v3, E_bob_v2] = (x, e) ] != 0.

Hypothesis eqn1_view_neq0 :
    forall
      (x : alice_input_view_valT * msg * Alice.-enc msg)
      (e : Charlie.-enc 'I_m),
    `Pr[ [% dec_view, E_alice_d3, E_charlie_v3] = (x, e) ] != 0.

Hypothesis eqn2_view_neq0 :
  forall
    (x :  (alice_input_view_valT * msg))
    (e : Alice.-enc msg),
  `Pr[ [% dec_view, E_alice_d3] = (x, e) ] != 0.

(* Since `alice_input_view` are generated by Alice,
   while `v2` is generated by Bob *)
Hypothesis alice_input_view_indep_v2 :
  P |= alice_input_view _|_ v2.

(* This lemma shows that if an active adversary controls Alice,
   it can set u1 and u2 as a special combination (1, 0),
   which allows revealing `v2` from the result that Alice receives.
   \cite[\S5.2]{dumas2017dual}.
*)
Lemma if_u1u2_are_compromised_v2_is_leaked :
  us = const_us -> ~ `H(v2 | alice_view ) = `H `p_v2.
Proof.
move => H.
(* From alice_view to [% alice_input_view, s] *)
rewrite !(E_enc_ce_removal v2 card_msg).
pose h := (fun o : (Alice.-key Dec msg * msg *
  msg * msg * msg * msg * msg * msg) =>
  let '(dk_a, s, v1, u1, u2, u3, r2, r3) := o in
   (dk_a, v1, u1, u2, u3, r2, r3, s)).
pose h' := (fun o : (Alice.-key Dec msg * msg *
  msg * msg * msg * msg * msg * msg) =>
  let '(dk_a, v1, u1, u2, u3, r2, r3, s) := o in
  (dk_a, s, v1, u1, u2, u3, r2, r3)).
rewrite -(centropy_RV_contraction _ _ h).
have ->: `H( v2 | [% dk_a, s, v1, u1, u2, u3, r2,
  r3, h `o [% dk_a, s, v1, u1, u2, u3, r2, r3]]) =
  `H( v2 | [% dk_a, s, v1, u1, u2, u3, r2, r3,
  [% dk_a, v1, u1, u2, u3, r2, r3, s]]).
  by [].
rewrite centropyC (centropy_RV_contraction _ _ h') -/alice_input_view.
(* From the cond_entropy to the independence goal via mutual info *)
move => H2.
have: `I(v2;[%alice_input_view, s]) = 0.
  by rewrite mutual_info_RVE H2 subrr.
move/mutual_info_RV0_indep.
(* Show the independence is impossible if Alice has been compromised
   and cheat with the specific `us`*)
rewrite s_alt /add_RV //= (const_us_is_v2_discloser H).
pose z := (fun o : (alice_input_view_valT * msg) =>
  let '(_, v1, u1, _, _, _, _, v2_r) := o in v2_r - v1 * u1).
move/(inde_RV_comp idfun z).
have -> : z `o [% alice_input_view, v2 \+ vu1] = v2.
  rewrite /z /vu1 /comp_RV /add_RV.
  apply: boolp.funext => i //=.
  by ring.
have -> : idfun `o v2 = v2.
  by apply: boolp.funext => i.
exact: neg_self_indep.
exact: eqn2_view_neq0.
exact: eqn1_view_neq0.
exact: alice_view_neq0.
Qed.

(* The constraint function: given v2, s, u2, u3, compute v3 *)
Definition compute_v3 (o : (msg * msg * msg * msg * msg * msg)) : msg :=
  let '(v1_val, u1_val, u2_val, u3_val, s_val, v2_val) := o in
    (s_val - u2_val * v2_val) / u3_val - u1_val * v1_val.  (* assuming u3 ≠ 0 *)

(* Key hypothesis: v3 is determined by v2 and the constraint *)
Hypothesis v3_determined : 
  v3 = compute_v3 `o [% v1, u1, u2, u3, s, v2].

(** * Fundamental Principle of Constraint-Based Security
    
    When an auxiliary variable is functionally determined by a secret
    and a constraint, the joint entropy equals the secret's entropy alone.
    This formalizes the principle that "knowing possible solution pairs
    gives exactly the same information as knowing the constraint on the secret."
    
    This principle underlies many MPC protocols where:
    - [v2] is the secret to protect
    - [v3] is an auxiliary/helper variable
    - [s, u2, u3] form a constraint linking them
    - Given constraint, [v3] is determined by [v2] (or vice versa)
*)
Lemma determined_auxiliary_adds_no_information_v2 :
  `H([%v2, v3] | [% v1, u1, u2, u3, s]) = `H(v2 | [% v1, u1, u2, u3, s]).
Proof.
have ->: `H([%v2, v3] | [% v1, u1, u2, u3, s]) =
  `H([% v1, u1, u2, u3, s], [%v2, v3]) - `H `p_ [% v1, u1, u2, u3, s].
  by rewrite chain_rule_RV addrAC subrr add0r.
rewrite v3_determined.
have ->: `H([% v1, u1, u2, u3, s],
    [% v2, compute_v3 `o [% v1, u1, u2, u3, s, v2]]) =
  `H `p_[% v1, u1, u2, u3, s, v2].
  by rewrite joint_entropy_RVA joint_entropy_RV_comp.
have ->: `H( v2 | [% v1, u1, u2, u3, s]) =
  `H([% v1, u1, u2, u3, s], v2) - `H `p_ [% v1, u1, u2, u3, s].
  by rewrite chain_rule_RV addrAC subrr add0r.
by [].
Qed.

Let f := fun o :
  (Alice.-key Dec msg * msg * msg * msg * msg * msg * msg * msg) =>
    let '(dk_a, v1, u1, u2, u3, r2, r3, s) := o in
         ((dk_a, v1, u1, u2, u3, r2, r3), s). 

Let comp_aiv_dotp2:
  f `o [%dk_a, v1, u1, u2, u3, r2, r3, dotp2_rv vs us `+ vu1] =
    [% alice_input_view, dotp2_rv vs us `+ vu1].
Proof. rewrite /comp_RV. apply: boolp.funext => _ //=. Qed.

Lemma bool8_perm 
    {T0 : finType} {P0 : R.-fdist T0}
    {TDK0 TV0 TU0 : finType}
    (dka0 : {RV P0 -> TDK0}) (s0 v10 u10 u20 u30 r20 r30 : {RV P0 -> TV0})
    (u0 : T0)
    (dka0' : TDK0) (r30' s0' v10' u10' u20' u30' r20' : TV0) :
  (dka0 u0 == dka0') && (s0 u0 == r30') && (v10 u0 == u10') && 
  (u10 u0 == u20') && (u20 u0 == u30') && (u30 u0 == r20') && 
  (r20 u0 == s0') && (r30 u0 == v10') =
  (dka0 u0 == dka0') && (r20 u0 == s0') && (r30 u0 == v10') && 
  (v10 u0 == u10') && (u10 u0 == u20') && (u20 u0 == u30') && 
  (u30 u0 == r20') && (s0 u0 == r30').
Proof.
by case: (dka0 u0 == dka0'); case: (s0 u0 == r30'); case: (v10 u0 == u10');
   case: (u10 u0 == u20'); case: (u20 u0 == u30'); case: (u30 u0 == r20');
   case: (r20 u0 == s0'); case: (r30 u0 == v10').
Qed.

Lemma bool8_flat
    {T0 : finType} {P0 : R.-fdist T0}
    {TDK0 TV0 : finType}
    (dka0 : {RV P0 -> TDK0}) 
    (s0 v10 u10 u20 u30 r20 r30 : {RV P0 -> TV0})
    (u0 : T0)
    (dka0' : TDK0) (r20' r30' v10' u10' u20' u30' s0' : TV0) :
  (dka0 u0 == dka0') && (r20 u0 == r20') && (r30 u0 == r30') && 
  (v10 u0 == v10') && (u10 u0 == u10') && (u20 u0 == u20') && 
  (u30 u0 == u30') && (s0 u0 == s0') =
  [&& (dka0 u0 == dka0') && (r20 u0 == r20') && (r30 u0 == r30'),
      (v10 u0 == v10') && (u10 u0 == u10') && (u20 u0 == u20') && 
      (u30 u0 == u30')
    & s0 u0 == s0'].
Proof.
by case: (dka0 u0 == dka0'); case: (r20 u0 == r20'); case: (r30 u0 == r30');
   case: (v10 u0 == v10'); case: (u10 u0 == u10'); case: (u20 u0 == u20');
   case: (u30 u0 == u30'); case: (s0 u0 == s0').
Qed.

Lemma bool9_perm
    {T0 : finType} {P0 : R.-fdist T0}
    {TA0 TDK0 TV0 : finType}
    (v0 : {RV P0 -> TA0})
    (dka0 : {RV P0 -> TDK0}) 
    (s0 v10 u10 u20 u30 r20 r30 : {RV P0 -> TV0})
    (u0 : T0)
    (a0 : TA0)
    (dka0' : TDK0) (r30' s0' v10' u10' u20' u30' r20' : TV0) :
  [&& v0 u0 == a0,
      (dka0 u0 == dka0') && (s0 u0 == r30') && (v10 u0 == u10') && 
      (u10 u0 == u20') && (u20 u0 == u30') && (u30 u0 == r20') && 
      (r20 u0 == s0')
    & r30 u0 == v10'] =
  [&& v0 u0 == a0,
      (dka0 u0 == dka0') && (r20 u0 == s0') && (r30 u0 == v10') && 
      (v10 u0 == u10') && (u10 u0 == u20') && (u20 u0 == u30') && 
      (u30 u0 == r20')
    & s0 u0 == r30'].
Proof.
by case: (v0 u0 == a0); 
   case: (dka0 u0 == dka0'); case: (s0 u0 == r30'); case: (v10 u0 == u10');
   case: (u10 u0 == u20'); case: (u20 u0 == u30'); case: (u30 u0 == r20');
   case: (r20 u0 == s0'); case: (r30 u0 == v10').
Qed.

Lemma bool9_regroup
    {T0 : finType} {P0 : R.-fdist T0}
    {TA0 TDK0 TV0 : finType}
    (v0 : {RV P0 -> TA0})
    (dka0 : {RV P0 -> TDK0}) 
    (s0 v10 u10 u20 u30 r20 r30 : {RV P0 -> TV0})
    (u0 : T0)
    (a0 : TA0)
    (dka0' : TDK0) (r20' r30' v10' u10' u20' u30' s0' : TV0) :
  [&& v0 u0 == a0,
      (dka0 u0 == dka0') && (r20 u0 == r20') && (r30 u0 == r30') && 
      (v10 u0 == v10') && (u10 u0 == u10') && (u20 u0 == u20') && 
      (u30 u0 == u30')
    & s0 u0 == s0'] =
  [&& v0 u0 == a0, 
      (dka0 u0 == dka0') && (r20 u0 == r20') && (r30 u0 == r30'),
      (v10 u0 == v10') && (u10 u0 == u10') && (u20 u0 == u20') && 
      (u30 u0 == u30')
    & s0 u0 == s0'].
Proof.
by case: (v0 u0 == a0);
   case: (dka0 u0 == dka0'); case: (r20 u0 == r20'); case: (r30 u0 == r30');
   case: (v10 u0 == v10'); case: (u10 u0 == u10'); case: (u20 u0 == u20');
   case: (u30 u0 == u30'); case: (s0 u0 == s0').
Qed.


Lemma privacy_by_bonded_leakage :
   P |= [% dk_a, r2, r3] _|_ [% v2, v3] | [% v1, u1, u2, u3, s] ->
   P |= [% dk_a, r2, r3] _|_ v2 | [% v1, u1, u2, u3, s] ->
  `H([%v2, v3] | alice_view ) = `H(v2 | alice_view).
Proof.
move => H_cinde_v2v3 H_cinde_v2.
set other_alice : {RV P -> (Alice.-key Dec msg) * msg * msg} :=
  [% dk_a, r2, r3].
have H: forall v, `H(v | alice_view ) =
    `H(v | [%other_alice, v1, u1, u2, u3, s] ).
  move => t v.
  rewrite /other_alice /alice_view.
  rewrite !(E_enc_ce_removal v card_msg); last first.
    exact: alice_view_neq0; last first.
    exact: eqn1_view_neq0; last first.
    exact: eqn2_view_neq0.
  have H_reorder: `H( v | [% dk_a, s, v1, u1, u2, u3, r2, r3]) =
    `H( v | [% dk_a, r2, r3, v1, u1, u2, u3, s]).
    rewrite /centropy_RV /centropy /= !snd_RV2.
    rewrite (reindex (fun '(dk_a', r2', r3', v1', u1', u2', u3', s') => 
                      (dk_a', s', v1', u1', u2', u3', r2', r3')))/=.
      apply: eq_bigr => [] [] [] [] [] [] [] []
        dk_a' s' v1' u1' u2' u3' r2' r3' _.
      congr (_ * _).
        by rewrite !dist_of_RVE !pfwd1E; congr Pr; apply/setP => u;
           rewrite !inE /= !xpair_eqE; rewrite bool8_perm.
      rewrite /centropy1; congr (- _).
      rewrite /jcPr !snd_RV2.
      apply: eq_bigr => a _.
      rewrite /jcPr !setX1 !Pr_set1 !dist_of_RVE !pfwd1E.
      congr (_ * _).
        f_equal.
          by congr Pr; apply/setP => u; rewrite !inE /= !xpair_eqE;
             rewrite bool9_perm.
        by f_equal; congr Pr; apply/setP => u;
           rewrite !inE /= !xpair_eqE; rewrite bool8_perm.
      congr log.
        f_equal.
          by congr Pr; apply/setP => u; rewrite !inE /= !xpair_eqE;
             rewrite bool9_perm.
        f_equal.
        by congr Pr; apply/setP => u; rewrite !inE /= !xpair_eqE;
           rewrite bool8_perm.
      by exists (fun '(dk_a', s', v1', u1', u2', u3', r2', r3') =>
             (dk_a', r2', r3', v1', u1', u2', u3', s')) 
             => [] [] [] []  [] [] [] [] dk_a' v1' u1' r2' r3' u2' u3' s'.
    exact: H_reorder.
rewrite (H msg v2) (H (msg * msg)%type [%v2, v3]).
have H_assoc: forall v, `H(v | [%other_alice, v1, u1, u2, u3, s] ) =
    `H(v | [%other_alice, [%v1, u1, u2, u3, s]] ).
  move => t v.
  rewrite /centropy_RV /centropy /= !snd_RV2.
  rewrite (reindex (fun '(o, (v1, u1, u2, u3, s)) =>
                    (o, v1, u1, u2, u3, s))) /=.
    apply: eq_bigr => [] [] [] [] dk_a' r2' r3' [] [] [] [] v1' u1' u2' u3' s' _.
    congr (_ * _).
      rewrite !dist_of_RVE !pfwd1E.
      by congr Pr; apply/setP => u; rewrite !inE /= !xpair_eqE bool8_flat.
    rewrite /centropy1; congr (- _).
    rewrite /jcPr !snd_RV2.
    apply: eq_bigr => a _.
    rewrite /jcPr !setX1 !Pr_set1 !dist_of_RVE !pfwd1E.
    congr (_ * _).
      f_equal.
        by congr Pr; apply/setP => u; rewrite !inE /= !xpair_eqE bool8_flat.
      f_equal.
      by congr Pr; apply/setP => u; rewrite !inE /= !xpair_eqE bool8_flat.
    congr log.
    f_equal.
      by congr Pr; apply/setP => u; rewrite !inE /= !xpair_eqE bool9_regroup.
    f_equal.
    by congr Pr; apply/setP => u; rewrite !inE /= !xpair_eqE bool8_flat.
  exists (fun '(o, v1, u1, u2, u3, s) =>
             (o, (v1, u1, u2, u3, s))).
        - by move=> [] o [] [] [] [] a1 a2 a3 a4 a5.
        - by move=> [] [] [] [] [] [] [] [] a1 a2 a3 a4 a5 o1 o2 o3.
rewrite (H_assoc msg v2) (H_assoc (msg * msg)%type [%v2, v3]).
rewrite (cinde_centropy_eq H_cinde_v2v3).
rewrite (cinde_centropy_eq H_cinde_v2).
exact: determined_auxiliary_adds_no_information_v2.
Qed. (* TODO: opaque check takes very long. *)

(*
  MEMO: move linear algebra part ("safety" part) and its connection with the
  information theory to another file (dsdp_safety.v)
  DSDP constraint:

  s = u2 * v2 + u3 * v3 + u1 * v1

  As linear system:

  [u1  u2  u3] * [v1]   [s]
                 [v2] = [ ]
                 [v3]   [ ]


For the inhomogeneous system (with fixed s, u1, u2, u3):
Number of solutions = #|msg|^(3 - rank(A)) where A = [u1 u2 u3]
This is an affine space parallel to the kernel

*)
                                
(*

   Rank = 1 → Kernel dim = 2 → #|solutions| = m → 
   Uniform → H = log(m) → Security with bounded leakage

*)

(* The adversary learns log(m) bits about v2, not 0 bits (perfect secrecy)
   but also not log(m^2) bits (complete knowledge).
   
   This is because:
   - There are m possible values for v2
   - Each is equally likely given alice_view
   - Entropy = log(m) bits
   
   Security holds despite information leakage.
*)

(*

TODO:

Theorem dsdp_security :
  (* By Rouché-Capelli: multiple solutions exist *)
  #|solution_set| > 1 ->
  
  (* Pair entropy = component entropy *)
  `H([%v2, v3] | alice_view) = `H(v2 | alice_view) /\
  
  (* Bounded leakage *)
  `H(v2 | alice_view) = log #|solution_set| > 0.
Proof.
  move=> multi_solutions.
  split.
  - (* Apply pair_entropy_eq_component *)
    apply: pair_entropy_eq_component.
    (* Show v3 = f(v2, s, u2, u3) *)
    ...
  - (* Uniform distribution by max entropy *)
    rewrite uniform_over_solutions.
    (* log #|solution_set| > log 1 by multi_solutions *)
    ...
Qed.                         


*)


(*

(** * Linear Algebra Foundation for DSDP Security *)

Section DSDP_LinearAlgebra.

Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Local Notation msg := 'I_m.

(** ** 1. DSDP Linear System Definition *)

(* The DSDP constraint as a matrix equation *)
Definition dsdp_matrix (u1 u2 u3 : msg) : 'M[msg]_(1, 3) :=
  \matrix_(i < 1, j < 3) 
    match j with
    | Ordinal 0 _ => u1
    | Ordinal 1 _ => u2
    | Ordinal 2 _ => u3
    end.

(* Vector of secret values *)
Definition secret_vector (v1 v2 v3 : msg) : 'rV[msg]_3 :=
  \row_(j < 3)
    match j with
    | Ordinal 0 _ => v1
    | Ordinal 1 _ => v2
    | Ordinal 2 _ => v3
    end.

(* The constraint: s = u1*v1 + u2*v2 + u3*v3 *)
Definition dsdp_constraint (u1 u2 u3 v1 v2 v3 s : msg) : Prop :=
  (secret_vector v1 v2 v3) *m (dsdp_matrix u1 u2 u3)^T = \matrix_(i < 1, j < 1) s.

(** ** 2. Rank Properties *)

Lemma dsdp_matrix_rank1 u1 u2 u3 :
  (u1 != 0) || (u2 != 0) || (u3 != 0) ->
  \rank (dsdp_matrix u1 u2 u3) = 1.
Proof.
(* The matrix [u1 u2 u3] is 1×3, so rank is at most 1 *)
(* If any coefficient is nonzero, rank is exactly 1 *)
Admitted. (* TODO: prove using matrix rank properties *)

Lemma dsdp_matrix_rank0 :
  \rank (dsdp_matrix 0 0 0) = 0.
Proof.
(* Zero matrix has rank 0 *)
Admitted.

(** ** 3. Solution Set Definition *)

(* All solutions to the homogeneous system (kernel) *)
Definition dsdp_kernel (u1 u2 u3 : msg) : {set 'rV[msg]_3} :=
  [set v : 'rV[msg]_3 | v *m (dsdp_matrix u1 u2 u3)^T == 0].

(* All solutions to the inhomogeneous system *)
Definition dsdp_solution_set (u1 u2 u3 v1 s : msg) : {set 'rV[msg]_3} :=
  [set v : 'rV[msg]_3 | 
    v *m (dsdp_matrix u1 u2 u3)^T == \matrix_(i < 1, j < 1) (s - u1 * v1)].

(* Solutions as pairs (v2, v3) given v1 *)
Definition dsdp_solution_pairs (u1 u2 u3 v1 s : msg) : {set msg * msg} :=
  [set (v2, v3) | v2 : msg, v3 : msg & u1 * v1 + u2 * v2 + u3 * v3 == s].

(** ** 4. Kernel Cardinality *)

(* Using the result from your other repo *)
Lemma dsdp_kernel_cardinality u1 u2 u3 :
  (u1 != 0) || (u2 != 0) || (u3 != 0) ->
  #|dsdp_kernel u1 u2 u3| = (m ^ (3 - 1))%N.
Proof.
move=> nonzero.
rewrite (dsdp_matrix_rank1 nonzero).
(* Apply: count_kernel_vectors_gaussian_elimination *)
(* #| kernel | = #|msg|^(dim - rank) = m^(3-1) = m^2 *)
Admitted.

(** ** 5. Solution Set Cardinality *)

Lemma dsdp_solution_set_nonempty u1 u2 u3 v1 s :
  exists v2 v3, (v2, v3) \in dsdp_solution_pairs u1 u2 u3 v1 s.
Proof.
(* Over a field, inhomogeneous linear system always has solutions *)
(* Pick any v2, then v3 = (s - u1*v1 - u2*v2) / u3 if u3 ≠ 0 *)
Admitted.

Lemma dsdp_solution_pairs_cardinality u1 u2 u3 v1 s :
  u3 != 0 ->
  #|dsdp_solution_pairs u1 u2 u3 v1 s| = m.
Proof.
move=> u3_nonzero.
(* For each v2 in msg, there's exactly one v3 = (s - u1*v1 - u2*v2) / u3 *)
(* So bijection between msg and solution pairs *)
(* Therefore #|solutions| = #|msg| = m *)
Admitted.

Lemma dsdp_solution_set_card_full u1 u2 u3 v1 s :
  u3 != 0 ->
  #|dsdp_solution_set u1 u2 u3 v1 s| = (m ^ 2)%N.
Proof.
move=> u3_nonzero.
(* The solution set is an affine space of dimension 2 *)
(* Parallel to the kernel which has dimension 2 *)
(* Cardinality = m^2 *)
Admitted.

(** ** 6. Uniformity and Entropy Connection *)

Section DSDP_Entropy_Connection.

Variable T : finType.
Variable P : R.-fdist T.
Variables (v1 v2 v3 u1 u2 u3 s : {RV P -> msg}).

(* The constraint holds with probability 1 *)
Hypothesis constraint_holds :
  forall t, s t = u1 t * v1 t + u2 t * v2 t + u3 t * v3 t.

(* Non-degeneracy assumption *)
Hypothesis u3_nonzero : forall t, u3 t != 0.

(* Given the constraint, (v2, v3) are uniformly distributed over solutions *)
Hypothesis uniform_over_solutions : forall t v1_val u1_val u2_val u3_val s_val,
  u1 t = u1_val -> u2 t = u2_val -> u3 t = u3_val ->
  v1 t = v1_val -> s t = s_val ->
  forall v2_val v3_val,
    (v2_val, v3_val) \in dsdp_solution_pairs u1_val u2_val u3_val v1_val s_val ->
    `Pr[ [% v2, v3] = (v2_val, v3_val) | [% v1, u1, u2, u3, s] = 
         (v1_val, u1_val, u2_val, u3_val, s_val) ] =
    1%:R / (#|dsdp_solution_pairs u1_val u2_val u3_val v1_val s_val|)%:R.

Lemma entropy_uniform_finite (A : finType) (S : {set A}) :
  (0 < #|S|)%N ->
  `H (fdist_uniform #|S|) = log (#|S|%:R).
Proof.
(* Standard result: entropy of uniform distribution *)
Admitted.

Lemma conditional_entropy_uniform_solutions :
  `H([%v2, v3] | [% v1, u1, u2, u3, s]) = log (m%:R).
Proof.
move: (constraint_holds) (u3_nonzero) (uniform_over_solutions) => Hcons Hu3 Hunif.
(* By uniformity and solution set cardinality *)
rewrite /centropy_RV.
(* Each conditioning value gives uniform distribution over m solutions *)
(* H(v2,v3 | cond) = sum_cond P(cond) * log(m) = log(m) *)
(* Use dsdp_solution_pairs_cardinality *)
Admitted.

End DSDP_Entropy_Connection.

End DSDP_LinearAlgebra.

(** * Main Security Theorem *)

Section DSDP_Security_Theorem.

Variable T : finType.
Variable P : R.-fdist T.
Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Local Notation msg := 'I_m.

(* Protocol random variables *)
Variables (dk_a : {RV P -> Alice.-key Dec msg}).
Variables (v1 v2 v3 u1 u2 u3 : {RV P -> msg}).
Variables (r2 r3 : {RV P -> msg}).
Variables (s : {RV P -> msg}).

(* Alice's view *)
Definition alice_view := [% dk_a, v1, u1, u2, u3, r2, r3, s].

(* Assumptions *)
Hypothesis constraint_holds :
  forall t, s t = u1 t * v1 t + u2 t * v2 t + u3 t * v3 t.

Hypothesis u3_nonzero : forall t, u3 t != 0.

Hypothesis uniform_over_solutions : (* as above *) True.

Hypothesis alice_independence_pair :
  P |= [% dk_a, r2, r3] _|_ [% v2, v3] | [% v1, u1, u2, u3, s].

Hypothesis alice_independence_v2 :
  P |= [% dk_a, r2, r3] _|_ v2 | [% v1, u1, u2, u3, s].

(* v3 is determined by other values *)
Definition compute_v3_from_constraint (v1_val u1_val u2_val u3_val s_val v2_val : msg) : msg :=
  (s_val - u1_val * v1_val - u2_val * v2_val) / u3_val.

Hypothesis v3_determined : 
  v3 = compute_v3_from_constraint `o [% v1, u1, u2, u3, s, v2].

(** ** Intermediate Results *)

Lemma pair_entropy_equals_component :
  `H([%v2, v3] | alice_view) = `H(v2 | alice_view).
Proof.
(* This is your safety_by_bonded_leakage lemma *)
exact: (safety_by_bonded_leakage alice_independence_pair alice_independence_v2).
Qed.

Lemma component_entropy_equals_solution_entropy :
  `H(v2 | alice_view) = log (m%:R) - log (m%:R) + log (m%:R).
Proof.
(* Simplification step *)
by rewrite subrr add0r.
Qed.

Lemma pair_entropy_via_conditioning :
  `H([%v2, v3] | alice_view) = `H([%v2, v3] | [% v1, u1, u2, u3, s]).
Proof.
(* By conditional independence from alice's randomness *)
(* Use alice_independence_pair and E_enc_ce_removal *)
Admitted.

Lemma pair_entropy_from_uniformity :
  `H([%v2, v3] | [% v1, u1, u2, u3, s]) = log (m%:R).
Proof.
exact: (@conditional_entropy_uniform_solutions T P v1 v2 v3 u1 u2 u3 s
         constraint_holds u3_nonzero uniform_over_solutions).
Qed.

(** ** Main Security Theorem *)

Theorem dsdp_security_bounded_leakage :
  `H(v2 | alice_view) = log (m%:R) /\
  `H(v2 | alice_view) > 0.
Proof.
split.
- (* Equality *)
  rewrite -pair_entropy_equals_component.
  rewrite pair_entropy_via_conditioning.
  exact: pair_entropy_from_uniformity.
- (* Positive bound *)
  rewrite -pair_entropy_equals_component.
  rewrite pair_entropy_via_conditioning.
  rewrite pair_entropy_from_uniformity.
  (* log(m) > 0 since m >= 2 *)
  apply: log_gt0.
  rewrite ltr1n.
  (* m = m_minus_2.+2 >= 2 *)
  by [].
Qed.

(** ** Interpretation *)

(* The adversary learns log(m) bits about v2, not 0 bits (perfect secrecy)
   but also not log(m^2) bits (complete knowledge).
   
   This is because:
   - There are m possible values for v2
   - Each is equally likely given alice_view
   - Entropy = log(m) bits
   
   Security holds despite information leakage.
*)

End DSDP_Security_Theorem.



*)


End dsdp_privacy_analysis.


