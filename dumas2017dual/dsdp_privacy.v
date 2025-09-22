From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap matrix.
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


(* First try to prove DSDP is information theoratically secure:

   FAIL: the `pvu1_unif` hypothesis cannot hold since vu1 := v1 \* u1.
   The product of two random variables is not uniform distributed.
   Unless there is any math theorem backs this, which I don't know.
*)
Hypothesis pvu1_unif : `p_ vu1 = fdist_uniform card_msg.
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

End dsdp_privacy_analysis.

Section safety_by_underdetermined_systems.
(* The "safety" property of the DSDP protocol
   is based on there is only one equation but N unknown terms
   where N > 1. It is called linear underdetermined systems. 
   And since we only consider integers, this problem is an
   integer linear programming problem (ILP). But we don't need to
   solve ILP to find the optimal result, we only need to confirm
   there is more than one solution to the equation.
*)
  

Section rouché_capelli.

Lemma mxrank_sub_eqmx m n p (A : 'M[R]_(m,n)) (B : 'M[R]_(p,n)) :
  \rank A = \rank B -> (A <= B)%MS -> (A == B)%MS.
Proof. by move/eqP => Hr /mxrank_leqif_eq /eq_leqif; rewrite Hr => <-. Qed.

Lemma rouche1 m n (A : 'M[R]_(m,n)) (B : 'rV_n) :
  (exists x, x *m A = B) <-> (\rank A = \rank (col_mx A B)).
Proof.
rewrite -addsmxE; split.
  case=> x AB; apply/eqmx_rank.
  by rewrite -AB addsmx_sub submx_refl addsmxSl submxMl.
move/mxrank_sub_eqmx/(_ (addsmxSl A B)).
case/eqmxP/eqmx_sym/addsmx_idPl/submxP => x ->.
by exists x.
Qed.

Lemma rouche2 m n (A : 'M[R]_(m,n)) (B : 'rV_n) :
  \rank A = \rank (col_mx A B) -> \rank A = m ->
  exists! x, x *m A = B.
Proof.
case/rouche1 => x Hx Am.
exists x; split => // x' Hx'.
move/eqP: Hx' (sub_kermx A (x'-x)).
rewrite -Hx -GRing.subr_eq0 -mulmxBl => -> /submxP [y].
have/eqP -> : kermx A == 0 by rewrite -mxrank_eq0 mxrank_ker Am subnn.
by rewrite mulmx0 => /GRing.subr0_eq /esym.
Qed.

Lemma exists_nonzero_kernel m n (A : 'M[R]_(m, n)) :
  (\rank A < m)%N -> exists2 y : 'rV_m, y *m A = 0 & y != 0.
Proof.
rewrite -subn_gt0 -mxrank_ker lt0n mxrank_eq0 => /matrix0Pn [i] [j] Hij.
exists (row i (kermx A)); first exact/sub_kermxP/row_sub.
by apply/rV0Pn; exists j; rewrite mxE.
Qed.

Lemma kernel_membership m n p (A : 'M[R]_(m, n)) (X : 'M[R]_(n, p)) :
  A *m X = 0 -> (X^T <= kermx A^T)%MS.
Proof.
move=> HX; apply/sub_kermxP.
by rewrite -(trmx_mul A X) HX trmx0.
Qed.
Lemma kernel_coeff_exists m n p (A : 'M[R]_(m, n)) (X : 'M[R]_(n, p)) :
  A *m X = 0 -> exists P : 'M[R]_(p, n),
    X^T = P *m kermx A^T.
Proof.
move=> HX.
have /submxP [P ->] : (X^T <= kermx A^T)%MS.
  by apply: kernel_membership.
by exists P.
Qed.

End rouché_capelli.

Section solution_counting.
  
(* Proving that if exists_nonzero_kernel in a finite domain,
   the number of vectors satisify A *m X = 0 is (#| {:K} | ^ (n - \rank A))%N.
*)

Variable K : finFieldType.


(* Column span of a matrix, as a set of column vectors (boolean-quantified). *)
Definition colspan m n (B : 'M[K]_(m, n)) : {set 'cV[K]_m} :=
  [set x | [exists y : 'cV[K]_n, B *m y == x]].

Lemma sub_coker m n (A : 'M[K]_(m, n)) :
  forall x : 'cV[K]_n, x \in colspan (cokermx A) -> A *m x == 0.
Proof.
move => x.
rewrite inE => /existsP [y /eqP Ey].
move: Ey. move/eqP.
rewrite eq_sym => /eqP ->.
apply/eqP.
by rewrite mulmxA mulmx_coker mul0mx.
Qed.

Lemma kernel_cardinality_rank_nullity m n (A : 'M[K]_(m, n)) :
  #| [set x : 'cV[K]_n | A *m x == 0] | = (#| {:K} | ^ (n - \rank A))%N.
Proof.
  (* Use rank-nullity theorem *)
  have ker_dim := mxrank_ker A.
  
  (* The kernel has dimension n - rank(A) *)
  (* We need to count the number of vectors in the kernel *)
  
  (* Method 1: Use the fact that kernel vectors are determined by their coordinates *)
  (* in the basis where the first r coordinates are determined by the last n-r *)
  
  (* Get the echelon form to understand the structure *)
  pose r := \rank A.
  set L := col_ebase A.
  set R := row_ebase A.
  set P : 'M[K]_(m, n) := pid_mx r.
  
  have defA : A = L *m P *m R by rewrite mulmx_ebase.
  have UR : R \in unitmx by apply: row_ebase_unit.
  have UL : L \in unitmx by apply: col_ebase_unit.

  (* The map x |-> R * x is a bijection *)
  pose f := (fun x : 'cV[K]_n => R *m x).
  (* Show bijection *)
  have bij_f : bijective f.
  exists (fun z => invmx (row_ebase A) *m z).
    move=> x; rewrite mulmxA mulVmx ?mul1mx //; exact: row_ebase_unit.
    move=> z; rewrite /f mulmxA mulmxV ?mul1mx //; exact: row_ebase_unit.

  (* Kernel correspondence: A*x = 0 iff P*(R*x) = 0 *)
  have ker_corr1: forall x, A *m x == 0 -> P *m (f x) == 0.
    move=> x.
    rewrite /f.
    move/eqP => HAx0.
    apply/eqP.
    rewrite mulmxA.
    rewrite defA in HAx0.
    have HPR : P *m R *m x = 0.
    have : invmx L *m (L *m P *m R *m x) = 0 by rewrite HAx0 mulmx0.
    rewrite mulmxA mulmxA mulmxA mulVmx.
    rewrite mul1mx //.
    exact: UL.
    exact: HPR.
  have ker_corr2 : forall x, P *m (f x) == 0 -> A *m x == 0.
    move=> x.
    rewrite /f.
    move => HPR.
    rewrite mulmxA in HPR.
    apply/eqP.
    rewrite defA.
    move: HPR.
    move/eqP => HPR.
    rewrite -mulmxA -mulmxA HPR.
    by rewrite mulmx0.
      
  set Ax := [set x : 'cV_n | A *m x == 0].
  set Pz := [set z : 'cV_n | P *m z == 0]. (* r decides how many diag 0 *)
  have card_eq : #|Ax| = #|Pz|.
    apply: eq_card => x.
    rewrite !inE.
    (*apply: ker_corr1.*)
    admit.
  rewrite card_eq -/r.
  

Abort.
    

Lemma count_kernel_vectors_gaussian_elimination m n (A : 'M[K]_(m, n)) :
  #| [set x : 'cV[K]_n | A *m x == 0] | = (#| {:K} | ^ (n - \rank A))%N.
Proof.
(* Use Gaussian elimination: transform to echelon form *)
pose r := \rank A.
set L := col_ebase A.
set R := row_ebase A.
set P : 'M[K]_(m, n) := pid_mx r.
(* The matrix decomposition A = L * P * R *)
have defA : A = L *m P *m R by rewrite mulmx_ebase.
(* Both L and R are invertible *)
have Urow : row_ebase A \in unitmx by apply: row_ebase_unit.
have Ucol : col_ebase A \in unitmx by apply: col_ebase_unit.

have bij_row : bijective (fun x : 'cV[K]_n => row_ebase A *m x).
  exists (fun z => invmx (row_ebase A) *m z).
    move=> x; rewrite mulmxA mulVmx ?mul1mx //; exact: row_ebase_unit.
  move=> z; rewrite mulmxA mulmxV ?mul1mx //; exact: row_ebase_unit.
pose f := (fun x : 'cV[K]_n => row_ebase A *m x).
set Ax := [set x : 'cV_n | A *m x == 0].
set Pz := [set z : 'cV_n | P *m z == 0]. (* r decides how many diag 0 *)
pose Rset : {set 'cV[K]_n} := [set z : 'cV[K]_n | P *m z == 0].
have fS_eqR : f @: Pz = Rset.
  apply/setP=> z; rewrite !inE; apply/idP/idP.
  move/imsetP=> [x Hx ->].
  rewrite inE in Hx.                 (* turn x \in S into A *m x == 0 *)
  move/eqP: Hx => HAx0.              (* now HAx0 : A *m x = 0 *)
  apply/eqP.                         (* goal becomes an equality *)
  Fail have H0 : invmx L *m (A *m x) = 0 by rewrite HAx0 mulmx0.
  Fail rewrite defA -!mulmxA (mulKmx Ucol) !mulmxA in H0.
  rewrite mulmxA.
  Fail exact: H0.
Abort.

(*
High-level goal: count solutions x to A x = 0 over finite field K.

  Step 1
   Let r = rank(A). Use the standard ebase factorization
      A = L · P · R, where L = col_ebase A (invertible m×m),
      R = row_ebase A (invertible n×n), and
      P = pid_mx r (n×n projector onto the first r coordinates).
  This is the Gaussian elimination decomposition mulmx_ebase.

  Step 2:
    Define the change-of-coordinates map f: x ↦ R x.
    It’s a bijection because R is invertible (row_ebase_unit).
    So counting x is equivalent to counting their images z = R x.

  Step 3:
    Show f maps the kernel of A exactly to the kernel of P. Using A = L P R:
      A x = 0 iff L P R x = 0.
    Since L is invertible, this is equivalent to P (R x) = 0.
    Let z = R x; then the condition is P z = 0.
    This establishes f @: S = { z | P z = 0 } where S = { x | A x = 0 }.

  Step 4:
    Conclude |S| = |{ z | P z = 0 }| by bijection/cardinality preservation.

  Step 5:
    Count solutions to P z = 0 when P = pid_mx r.
    This projector forces the first r coordinates of z to be zero
    while leaving the remaining n − r coordinates free.
    Therefore the number of such z is |K|^(n − r).

Final result: |{ x | A x = 0 }| = |K|^(n − rank(A)).
*)
End solution_counting.

End safety_by_underdetermined_systems.

