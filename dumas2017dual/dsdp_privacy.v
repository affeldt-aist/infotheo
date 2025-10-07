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

Let alice_traces : RV dsdp_traceT P :=
      (fun t => tnth t 0) `o dsdp_RV inputs.

(* Use these two and apply_inde_RV_comp to prove trivial indeps*)
Let alice_inputs_RV := [% dk_a, v1, u1, u2, u3, r2, r3].
Let alice_inputsT := (Alice.-key Dec msg * msg * msg * msg *
  msg * msg * msg)%type.

(* E_charlie_v3 means it is encrypted (so generated) by the key of charlie.
   Therefore, encrypted RVs should be independent of other parties.
   Even other parties can add messages by HE properties, but addition to a RV
   means the independence keeps after the addition.
*)
Hypothesis inde_Echarlie : P |= alice_inputs_RV _|_ E_charlie_v3.
Hypothesis inde_Ebob : P |= alice_inputs_RV _|_ E_bob_v2.

Let alice_view_valuesT := (Alice.-key Dec msg * msg * msg *
  msg * msg * msg * msg * msg * Alice.-enc msg * Charlie.-enc msg *
  Bob.-enc msg)%type.

Let alice_view := [% dk_a, s, v1 , u1, u2, u3, r2, r3,
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

Local Definition alice_view_values_from_trace (xs : dsdp_traceT) : alice_view_valuesT :=
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
transitivity (`H(v | [%alice_traces, alice_view])).
  have -> : alice_view = alice_view_values_from_trace `o alice_traces.
    by apply: boolp.funext => x /= ;
       rewrite alice_traces_from_viewP /comp_RV alice_view_values_from_traceP.
  by rewrite centropy_RV_contraction.
by rewrite alice_traces_from_viewP centropyC centropy_RV_contraction.
Qed.

Let alice_input_view := [%dk_a, v1, u1, u2, u3, r2, r3].
Notation alice_input_view_valT :=
  (Alice.-key Dec msg * msg * msg * msg * msg * msg * msg)%type.

Section dotp2.

Notation "x \+ y" := (add_RV x y).  

Definition dotp2 (x y: (msg * msg)) := x.1 * y.1 + x.2 * y.2.
Definition dotp2_rv (X Y : {RV P -> (msg * msg)}) : {RV P -> msg} :=
  fun p => dotp2 (X p) (Y p).

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
Local Definition dec_view := [%dk_a, s, v1 , u1, u2, u3, r2, r3].
Local Definition eqn1_view := [% dec_view, E_alice_d3, E_charlie_v3].
Local Definition eqn2_view := [% dec_view, E_alice_d3].
 
(* TODO: define types to simplify types in the proof context *)
Hypothesis alice_view_neq0 :
  forall x e, `Pr[ [% dec_view, E_alice_d3, E_charlie_v3, E_bob_v2] =
        (x, e) ] != 0.

Hypothesis eqn1_view_neq0 :
  forall x e, `Pr[ [% dec_view, E_alice_d3, E_charlie_v3] =
        (x, e) ] != 0.

Hypothesis eqn2_view_neq0 :
  forall x e, `Pr[ [% dec_view, E_alice_d3] =
        (x, e) ] != 0.

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

Lemma logr_eq1 (x : R) : 0 < x -> (log x = 0) <-> (x = 1).
Proof.
move=> Hpos; split.
- (* log x = 0 -> x = 1 *)
  move=> Hlog.
  rewrite -[x]logK //.
  by rewrite Hlog exp.powRr0.
- (* x = 1 -> log x = 0 *)
  move=> ->.
  exact: log1.
Qed.

(* Prove this is because we already knew U . V is safe by Rouche-Capelli *)
Lemma entropy_dot_product_result_leq_solutions
  (S : {RV P -> msg}) (U V: {RV P -> (msg * msg)}) :
  S = dotp2_rv U V ->
  `H `p_S <= `H(U, V).
Proof.
move => HS.
have centropy_S_UV_eq0 : `H(S | [%U, V]) = 0.
  pose f := fun uv => dotp2 uv.1 uv.2.
  have ->: S = f `o [%U, V].
    rewrite HS /f /dotp2_rv /dotp2.
    by apply: boolp.funext => i //=.
  by rewrite centropy_RV_comp0.
have joint_entropy_SUV_eq_UV : `H(S, [%U, V]) = `H(U, V).
  rewrite joint_entropy_RVC chain_rule_RV centropy_S_UV_eq0.
  by rewrite /joint_entropy_RV /joint_entropy addr0.
rewrite -joint_entropy_SUV_eq_UV.
rewrite chain_rule_RV.
rewrite lerDl.
have [-> //|Hneq] := eqVneq 0 (`H( [% U, V] | S)).
by rewrite centropy_ge0.
Qed.
(*
   Equaliy iff H([%V, U] | S) = 0, i.e. S uniquely determines (V, U).

      Formally:

      H(V, U | S) = 0 <-> forall s, Pr[S = s] > 0,
          exists! (v, u), Pr[V, U = (v, u) | S = s] = 1.

      Given the value of S the pair (V, U) is determined uniquely (prob is 1.0) 
*)
Lemma zero_entropy_eq_point_mass
  (Z : {RV P -> msg}) :
  `H `p_Z = 0 <-> exists! z, `Pr[Z = z] = 1.
Proof.
simpl in *.
split.
rewrite /entropy -sumrN.
move/eqP.
rewrite psumr_eq0.
move/allP.
move => Hall.
have H_terms_zero: forall i : 'I_m, - (`p_ Z i * log (`p_ Z i)) = 0.
  move=> i.
  have := Hall i.
  rewrite mem_index_enum inE /=.
  move=> H. 
  apply/eqP.
  exact: H.
have H_01: forall i : 'I_m, `p_ Z i = 0 \/ `p_ Z i = 1.
  move=> i.
  move: (H_terms_zero i).
  move/eqP.
  rewrite oppr_eq0.
  rewrite dist_of_RVE.
  move /eqP => HPrMul0.
  case: (boolP (`Pr[ Z = i ] == 0)) => [/eqP H0 | H_neq0].
    by left.
    right.
    move /eqP: HPrMul0.
    rewrite mulf_eq0 => /orP [/eqP Hp0 | //].
    by move: H_neq0; rewrite Hp0 eqxx.
  - move/eqP.
    move => Hlog0.
    have Hpos: 0 < `Pr[ Z = i ].
      rewrite lt0r; apply/andP; split.
      - exact: H_neq0.
      - by apply: pfwd1_ge0.
    by rewrite -(logr_eq1 Hpos).
have Hsum: \sum_i `Pr[ Z = i ] = 1.
  exact: sum_pfwd1.

(* Show that exactly one probability equals 1 *)
have Hcard: #|[set i : 'I_m | `Pr[ Z = i ] == 1]| = 1%N.
  (* Since each prob is 0 or 1, and sum = 1, exactly one is 1 *)
  have: \sum_i `Pr[ Z = i ] = \sum_(i | `Pr[ Z = i ] == 1) `Pr[ Z = i ].
    rewrite [LHS]big_mkcond [RHS]big_mkcond.
    apply: eq_bigr => i _.
    case: (H_01 i) => Hi.
    - rewrite dist_of_RVE in Hi.
      by rewrite Hi if_same.
    - rewrite dist_of_RVE in Hi.
      move/eqP in Hi.
      by rewrite Hi.
  move => Heq.
  apply/eqP; rewrite eqn_leq; apply/andP; split.
  - apply: contraT => /negP.
    move=> Hnot.
    have Hge2: (2 <= #|[set i | `Pr[ Z = i ] == 1%:R]|)%N.
      move: Hnot => /negP.
      rewrite -ltnNge.
      have ->: [set i | `Pr[ Z = i ] == 1%R] = [set i | `Pr[ Z = i ] == 1] by [].
      by [].
    have Hset_eq: [set i | `Pr[ Z = i ] == 1%R] = [set i | `Pr[ Z = i ] == 1].
      by apply/setP => y; rewrite !inE.
    move: Hge2; rewrite Hset_eq => Hge2.
    move: Hge2 => /card_gt1P [i [j [Hi Hj Hneq]]].
    move: Hi Hj; rewrite !inE => /eqP Hi /eqP Hj.
    have: 2 <= \sum_k `Pr[ Z = k ].
      rewrite (bigD1 i) //= Hi (bigD1 j) /=; last by rewrite eq_sym.
      rewrite Hj.
      have: 0 <= \sum_(k | (k != i) && (k != j)) `Pr[ Z = k ].
        apply: sumr_ge0 => t _.
        exact: pfwd1_ge0.
      by lra.
    rewrite Hsum.
    by lra.
  - case: (posnP #|[set i | `Pr[ Z = i ] == 1]|) => [Hcard0 | //].
    have Hall_not1: forall i : 'I_m, `Pr[ Z = i ] != 1.
    move=> i; apply/negP => /eqP Hi.
    have: i \in [set k | `Pr[ Z = k ] == 1] by rewrite inE; apply/eqP.
    by rewrite (cards0_eq Hcard0) inE.

  have Hall0: forall i : 'I_m, `Pr[ Z = i ] = 0.
    move=> i; case: (H_01 i) => [// | Hi].
    - move: (Hall_not1 i).
      move => Hnot1.
      rewrite dist_of_RVE.
      move => H1.
      exact: H1.
    - rewrite dist_of_RVE in Hi.
      have := Hall_not1 i.
      rewrite Hi.
      by lra.
  have: \sum_i `Pr[ Z = i ] = 0.
    by apply: big1 => i _; rewrite Hall0.
  rewrite Hsum.
  by lra.
  
have [z Hz]: exists z : 'I_m, [set i | `Pr[ Z = i ] == 1] = [set z].
  by apply/cards1P; rewrite Hcard.
exists z; split.
- (* Show `Pr[Z = z] = 1 *)
  have: z \in [set i | `Pr[ Z = i ] == 1].
    by rewrite Hz inE.
  by rewrite inE => /eqP.
- (* Uniqueness *)
  move=> z' Hz'.
  have: z' \in [set i | `Pr[ Z = i ] == 1].
    by rewrite inE; apply/eqP.
by rewrite Hz inE => /eqP.
move=> i _.
case: (altP (`p_ Z i =P 0)) => [-> | Hneq0].
- by rewrite mul0r oppr0.
- have /andP [Hge0 Hle1] := fdist_ge0_le1 (`p_ Z) i.
  have Hpos: 0 < `p_ Z i by rewrite lt0r Hneq0 Hge0.
  have: log (`p_ Z i) <= 0.
    rewrite -log1.
    rewrite ler_log /=.
    by rewrite Hle1.
- by rewrite posrE.
- by rewrite posrE.
- move=> Hlog_neg.
  rewrite -mulrN.
  rewrite pmulr_rge0.
  by lra.
-by lra.

(* Another direction:
  (exists ! z : 'I_m, `Pr[ Z = z ] = 1) -> `H `p_ Z = 0
*) 
case=> z [Hz Huniq].
apply/eqP; rewrite oppr_eq0.
apply/eqP.
apply: big1 => i _.
case: (altP (i =P z)) => [-> | Hneq].
- (* i = z *)
  rewrite dist_of_RVE.
  by rewrite Hz mul1r log1.
- (* i != z: show `Pr[Z = i] = 0 *)
have Hi0: `Pr[ Z = i ] = 0.
  have Hsum: \sum_j `Pr[ Z = j ] = 1 by exact: sum_pfwd1.
  move: Hsum; rewrite (bigD1 z) //= Hz => Hsum.
  
  (* The remaining sum equals 0 *)
  have Hsum0: \sum_(j | j != z) `Pr[ Z = j ] = 0.
    by move: Hsum => /(f_equal (fun x => x - 1)); lra.
  have Hge0: forall j, j != z -> 0 <= `Pr[ Z = j ].
    move => j _; exact: pfwd1_ge0.
  move: Hsum0 => /eqP.
  rewrite (psumr_eq0 _ Hge0) => /allP /(_ i).
  rewrite mem_index_enum => /(_ erefl).
  by rewrite Hneq /= => /eqP.
by rewrite dist_of_RVE Hi0 mul0r.
Qed.

Lemma entropy_dot_product_result_determinates_solutions
  (S : {RV P -> msg}) (U V: {RV P -> (msg * msg)}) :
  S = dotp2_rv U V ->
  `H([%V, U] | S) = 0 <-> (
     forall x, `Pr[S = x] > 0 -> exists! vu, `Pr[[%V, U] = vu | S = x] = 1).
Proof.
split.
move => HS x Pr_gt0.
(* TODO: use zero_entropy_eq_point_mass here. *)
Abort.

(* --------------- *)


(* First try to prove DSDP is information theoratically secure:

   FAIL: the `pvu1_unif` hypothesis cannot hold since vu1 := v1 \* u1.
   The product of two random variables is not uniform distributed.
   Unless there is any math theorem backs this, which I don't know.

   (If we assume v and u are numbers have inverse then this can be true;
    since excluding 0 means the result of multiplication will not be
    centralized to the same point.
   )
*)
Hypothesis pvu1_unif : `p_ vu1 = fdist_uniform card_msg.

(* This holds because v1, u1 are independant from v2, v3 and u2, u3. *)
Hypothesis vu1_indep :  P |= vu1 _|_ [% dotp2_rv us vs, v2].

Let dotp2_inde_v2 :
  P |= (dotp2_rv us vs `+ vu1) _|_ v2.
Proof. exact: (lemma_3_5' vu1_indep pvu1_unif). Qed.

Let f := fun o :
  (Alice.-key Dec msg * msg * msg * msg * msg * msg * msg * msg) =>
    let '(dk_a, v1, u1, u2, u3, r2, r3, s) := o in
         ((dk_a, v1, u1, u2, u3, r2, r3), s). 

Let comp_aiv_dotp2:
  f `o [%dk_a, v1, u1, u2, u3, r2, r3, dotp2_rv vs us `+ vu1] =
    [% alice_input_view, dotp2_rv vs us `+ vu1].
Proof. rewrite /comp_RV. apply: boolp.funext => _ //=. Qed.

Let aiv_dotp2_inde_v2 :
  P |= [% alice_input_view, dotp2_rv [% v2, v3] us `+ vu1] _|_ v2.
Proof.
rewrite -comp_aiv_dotp2.
have ->: v2 = idfun `o v2.
  by apply: boolp.funext => _ //=.
apply/(inde_RV_comp f idfun).
(* TODO apply lemma 3.6 until all terms are gone except the dotp2 one *)
Admitted.

Lemma try_if_alice_is_fair_dsdp_is_secure :
  s != v2 -> `H(v2 | alice_view ) = `H `p_v2.
Proof.
simpl in *.
move => H.
rewrite !(E_enc_ce_removal v2 card_msg); simpl in *.
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
rewrite centropyC (centropy_RV_contraction _ _ h').
rewrite  -/alice_input_view.
transitivity (`H([% alice_input_view, s], v2) - `H(alice_input_view, s)).
  by rewrite chain_rule_RV addrAC subrr add0r.
rewrite inde_RV_joint_entropyE.
- by rewrite addrAC subrr add0r.
- have [Ha|Hb] := eqVneq s v2.
    contradict Ha.
    move/eqP in H. (* from x != y to x <> y *)
    exact: H.
  clear.
  rewrite s_alt /vs.
Abort.

End alice_privacy_analysis.

(* Conclusion: we should prove the "safety" property
   by connecting rouch capelli and dot product here.
   
   Memo: case analysis may prove the equality of knowing dot product
   result and knowing combinations.

   Memo: even they are not equal, since we can assume/claim knowing
   combinations are safe, if we can prove that knowing the result
   the H is smaller than knowing combinations, we still can claim the safety.


   Inequality can be proved because the type provides the info already:

   {RV T -> R} vs. {RV T -> (R * R * R * R)}

   But the problem is if the LHS can restrict RHS to be one.
   So it must be inequality. To prove there is no restriction,
   use Rouch-Capelli case 3 and give the condition as a premises,
   which can be inferred from the traces (how many equations and how many
   unknown terms).
*)

End dsdp_privacy_analysis.


