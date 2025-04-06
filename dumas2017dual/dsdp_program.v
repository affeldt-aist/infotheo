From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix Rstruct ring boolp finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter smc_tactics.

Import GRing.Theory.
Import Num.Theory.
Module scp := smc_entropy.smc_entropy_proofs.

(*******************************************************************************************)
(*                                                                                         *)
(* Formalization of:                                                                       *)
(*                                                                                         *)
(* Dumas, J. G., Lafourcade, P., Orfila, J. B., & Puys, M. (2017).                         *)
(* Dual protocols for private multi-party matrix multiplication and trust computations.    *)
(* Computers & security, 71, 51-70.                                                        *)
(*                                                                                         *)
(*******************************************************************************************)

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

Section party_def.

Inductive party := Alice | Bob | Charlie | NoParty.

Definition party_eqb_subproof (p1 p2: party) : { p1 = p2 } + { p1 <> p2 }.
Proof. decide equality. Defined.

Definition party_eqb (p1 p2: party) : bool :=
  if party_eqb_subproof p1 p2 then true else false. 

Lemma party_eqP : Equality.axiom party_eqb.
Proof.
move=> p1 p2.
rewrite /party_eqb.
by case: party_eqb_subproof => /= H;constructor.
Qed.

HB.instance Definition _ := hasDecEq.Build party party_eqP.

Definition party_to_nat (a : party) : nat :=
  match a with Alice => 0 | Bob => 1 | Charlie => 2 | NoParty => 3 end.

Definition nat_to_party (a : nat) : party :=
  match a with 0 => Alice | 1 => Bob | 2 => Charlie | _ => NoParty end.

Lemma party_natK : cancel party_to_nat nat_to_party.
Proof. by case. Qed.

HB.instance Definition _ : isCountable party := CanIsCountable party_natK.

Definition party_enum := [:: Alice; Bob; Charlie; NoParty].

Lemma party_enumP : Finite.axiom party_enum.
Proof. by case. Qed.

HB.instance Definition _ := isFinite.Build party party_enumP.

End party_def.

(* Because the interpreter expects parties are nat in lots of places. *)
Notation "'n(' w ')' " := (party_to_nat w).

Section key_def.
  
Inductive key := Dec | Enc.

Definition key_eqb_subproof (k1 k2: key) : { k1 = k2 } + { k1 <> k2 }.
Proof. decide equality. Defined.

Definition key_eqb (k1 k2: key) : bool :=
  if key_eqb_subproof k1 k2 then true else false. 

Lemma key_eqP : Equality.axiom key_eqb.
Proof.
move=> k1 k2.
rewrite /key_eqb.
by case: key_eqb_subproof => /= H;constructor.
Qed.

HB.instance Definition _ := hasDecEq.Build key key_eqP.

Definition key_to_nat (a : key) : nat :=
  match a with Dec => 0 | Enc => 1 end.

Definition nat_to_key (a : nat) : key :=
  match a with 0 => Dec | _ => Enc end.

Lemma key_natK : cancel key_to_nat nat_to_key.
Proof. by case. Qed.

HB.instance Definition _ : isCountable key := CanIsCountable key_natK.

Definition key_enum := [:: Dec; Enc].

Lemma key_enumP : Finite.axiom key_enum.
Proof. by case. Qed.

HB.instance Definition _ := isFinite.Build key key_enumP.

End key_def.

Section he.
  
Variable party : finType.
Variable msg : finComRingType.

Definition enc := (party * msg)%type.
Definition pkey := (party * key * msg)%type.

Definition E i m : enc := (i, m).
Definition K i k m : pkey := (i, k, m).

Definition D (k : pkey) (e : enc) : option msg :=
  match k, e with
  | (i, k, _), (j, m) => if (i == j) && (k == Dec) then Some m else None
  end.

(* TODO: use option? But to lift a None in embedded computation
   to an interpreter Fail is distant. *)
Definition Emul (e1 e2 : enc) : enc := 
  match (e1, e2) with
  | ((i1, m1), (i2, m2)) => if i1 == i2 then E i1 (m1 + m2) else E i1 0
  end.

Definition Epow (e : enc) (m2 : msg) : enc :=
  match e with
  | (i, m1) => E i (m1 * m2)
  end.

End he.

Section party_key_def.
  

(* Need something like {RV P -> Alice.-key Dec T} in view;
   `T` means any type of the key's value.
*)

Variant party_key (p : party) (k : key) (T : Type) : Type :=
  KeyOf of T.

Definition party_key_v p k T (pk : party_key p k T) : T :=
  let 'KeyOf v := pk in v.

Variable (p : party) (k : key)(T : Type).

HB.instance Definition _ := [isNew for @party_key_v p k T].

End party_key_def.

Notation "p .-key k" := (party_key p k)
  (at level 2, format "p .-key k") : type_scope.

Coercion tuple_of_party_key p k T (pk : p.-key k T) : (party * key * T) :=
  let 'KeyOf v := pk in (p, k, v).

Section party_key_types.

HB.instance Definition _ p k (T : eqType) : hasDecEq (p.-key k T) :=
  [Equality of p.-key k T by <:].
HB.instance Definition _ p k (T : choiceType) :=
  [Choice of p.-key k T by <:].
HB.instance Definition _ p k (T : countType) :=
  [Countable of p.-key k T by <:].
HB.instance Definition _ p k (T : finType) :=
  [Finite of p.-key k T by <:].

Variable (p : party)(k : key)(T : finType).

Lemma card_party_key : #|{:p.-key k T}| = #|T|.
Proof.
apply (bij_eq_card (f:=@party_key_v p k T)).
exists (@KeyOf p k T).
by case.
by [].
Qed.

End party_key_types.


Section enc_type_def.

(*
  Because {RV P -> enc} is wrong:
  we have no random variables that output (different parties x different messages),
  but only (one fixed party x different messages).
  
  So we need to define a type level label like: {RV P -> Alice.-enc}.
*)

Variant enc_for (p : party) (T : Type) : Type :=
  EncFor of T.

Variable (p : party) (T : Type).

Definition enc_for_v p T (e : enc_for p T) : T :=
  let 'EncFor v := e in v.

HB.instance Definition _ := [isNew for @enc_for_v p T].

End enc_type_def.

Notation "p .-enc" := (enc_for p)
  (at level 2, format "p .-enc") : type_scope.

Notation "{ 'enc_for' p 'of' T }" := (p.-enc T : predArgType)
  (at level 0, only parsing) : type_scope.

Coercion tuple_of_enc_for p T (e : p.-enc T) : (party * T) :=
  let 'EncFor v := e in (p, v).

Section enc_types.
  
HB.instance Definition _ p (T : eqType) : hasDecEq (p.-enc T) :=
  [Equality of p.-enc T by <:].
HB.instance Definition _ p (T : choiceType) :=
  [Choice of p.-enc T by <:].
HB.instance Definition _ p (T : countType) :=
  [Countable of p.-enc T by <:].
HB.instance Definition _ p (T : finType) :=
  [Finite of p.-enc T by <:].

Definition E' (T : Type) (p : party) (t : T) : p.-enc T :=
  EncFor p t.

Variable (p : party) (T : finType).

Lemma card_enc_for :
  #|{:p.-enc T}| = #|T|.
Proof.
apply (bij_eq_card (f:=@enc_for_v p T)).
exists (@EncFor p T).
by case.
by [].
Qed.

Lemma card_enc_for' : forall (n : nat),
  #|T| = n.+1 -> #|{:p.-enc T}| = n.+1.
Proof. by rewrite card_enc_for. Qed.

End enc_types.

Section enc_lemmas.

Variables (T : finType)(P : R.-fdist T).

Section unif.

Variables (A : finType)(p : party)(X : {RV P -> p.-enc A})(n : nat).
Hypothesis card_A : #|A| = n.+1.

Axiom E_enc_unif :
  `p_X = fdist_uniform (card_enc_for' p card_A).

End unif.

Axiom E_enc_inde : forall (A B : finType) (p : party) (X : {RV P -> p.-enc A}) (Y : {RV P -> B}),
  P |= X _|_ Y.
(* TODO: what if B is (p.-enc A) ? Whether we need a way to judge if B is (p.-enc A) or not?*)

Section lemma_E_enc_ce.
  
Variables (A B C: finType) (p : party).
Variables (X : {RV P -> A})(E : {RV P -> p.-enc B})(Z : {RV P -> C})(n : nat).
Hypothesis card_B : #|B| = n.+1.
Hypothesis XE_neq0 : forall x e, `Pr[ [%X, E] = (x, e)] != 0.

Lemma E_enc_ce_removal :
  `H(Z | [%X, E]) = `H(Z | X).
Proof.
have HindeX_E : P |= X _|_ E.
  rewrite smc_proba.inde_rv_sym.
  exact: (E_enc_inde E X).
have Hunif : `p_ E = fdist_uniform (card_enc_for' p card_B).
  exact: (E_enc_unif E card_B).
have HindeXZ_E : P |= [%X, Z] _|_ E.
  rewrite smc_proba.inde_rv_sym.
  exact: (E_enc_inde E [%X, Z]).
apply (scp.cpr_cond_entropy (Y1:=Z)(Y2:=X)(Y3:=E) Hunif HindeX_E) => c a b.
have Hpr : `Pr[ Z = c | [%X, E] = (a, b)] = `Pr[ Z = c | X = a].
  have HindeZ_X : P |= E _|_ [%Z, X].
    exact: (E_enc_inde E [%Z, X]).
  rewrite smc_proba.inde_rv_sym in HindeZ_X.
  have H:=(smc_proba.inde_RV2_cinde (X:=Z)(Y:=E)(Z:=X) HindeZ_X).
  pose proof XE_neq0 as EX_neq0.
  move/(_ a b) in EX_neq0. (* Specialize forall...*)
  rewrite pr_eq_pairC in EX_neq0.
  have H2:= (cinde_alt c H EX_neq0).
  rewrite cpr_eq_pairCr.
  exact: H2.
move => ?.
exact: Hpr.
Qed.

End lemma_E_enc_ce.

End enc_lemmas.

Section dsdp.
  
Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Let msg := 'I_m.  (* = Z/mZ *)

Let enc := enc party msg.
Let pkey := pkey party msg.

Notation "u *h w" := (Emul u w).
Notation "u ^h w" := (Epow u w).

Definition alice : party := Alice.
Definition bob : party := Bob.
Definition charlie : party := Charlie.

Definition data := (msg + enc + pkey)%type.
Definition d x : data := inl (inl x).
Definition e x : data := inl (inr x).
Definition k x : data := inr x.

(* Should receive something the party can decrypt *)
Definition Recv_dec frm pkey f : proc data :=
  Recv frm (fun x => if x is inl (inr v) then
                       if D pkey v is Some v' then f v' else Fail
                     else Fail).

(* Should receive something the party cannot decrypt,
   but can do HE computation over it.
*)
Definition Recv_enc frm f : proc data :=
  Recv frm (fun x => if x is inl (inr v) then f v else Fail).

Definition pbob (dk : pkey)(v2 : msg) : proc data :=
  Init (k dk) (
  Init (d v2) (
  Send n(alice) (e (E bob v2)) (
  Recv_dec n(alice) dk (fun d2 =>
  Recv_enc n(alice) (fun a3 =>
    Send n(charlie) (e (a3 *h (E charlie d2))) (
  Finish)))))).

Definition pcharlie (dk : pkey)(v3 : msg) : proc data :=
  Init (k dk) (
  Init (d v3) (
  Send n(alice) (e (E charlie v3)) (
  Recv_dec n(bob) dk (fun d3 => (
    Send n(alice) (e (E alice d3))
  Finish))))).

Definition palice (dk : pkey)(v1 u1 u2 u3 r2 r3: msg) : proc data :=
  Init (k dk) (
  Init (d v1) (
  Init (d u1) (
  Init (d u2) (
  Init (d u3) (
  Init (d r2) (
  Init (d r3) (
  Recv_enc n(bob) (fun c2 =>
  Recv_enc n(charlie) (fun c3 =>
  let a2 := (c2 ^h u2 *h (E bob r2)) in
  let a3 := (c3 ^h u3 *h (E charlie r3)) in
    Send n(bob) (e a2) (
    Send n(bob) (e a3) (
    Recv_dec n(charlie) dk (fun g =>
    Ret (d ((g - r2 - r3 + u1 * v1))))))))))))))).
  
Variables (k_a k_b k_c v1 v2 v3 u1 u2 u3 r2 r3 : msg).

(* Note: must be with concrete values otherwise computation won't go *)
Let dk_a : pkey := (Alice, Dec, k_a). 
Let dk_b : pkey := (Bob, Dec, k_b). 
Let dk_c : pkey := (Charlie, Dec, k_c). 

Definition dsdp h :=
  (interp h [:: palice dk_a v1 u1 u2 u3 r2 r3; pbob dk_b v2; pcharlie dk_c v3] [::[::];[::];[::]]).

(* Different from SMC scalar product: has much less calculations *)
Goal (dsdp 15) = ([::],[::]).
rewrite /dsdp.
rewrite (lock (15 : nat)) /=.
rewrite -lock (lock (14 : nat)) /=.
rewrite -lock (lock (13 : nat)) /=.
rewrite -lock (lock (12 : nat)) /=.
rewrite -lock (lock (11 : nat)) /=.
rewrite -lock (lock (10 : nat)) /=.
rewrite -lock (lock (9 : nat)) /=.
rewrite -lock (lock (8 : nat)) /=.
rewrite -lock (lock (7 : nat)) /=.
rewrite -lock (lock (6 : nat)) /=.
rewrite -lock (lock (5 : nat)) /=.
rewrite -lock (lock (4 : nat)) /=.
rewrite -lock (lock (3 : nat)) /=.
(* Because we use nat as party ID as well -- it confuses with what we are going to compute *)
rewrite -lock [X in interp X.+1](lock (2 : nat)) /=.
rewrite -lock (lock (1 : nat)) /=.
rewrite -lock (lock (0 : nat)) /=.
Abort.

Lemma dsdp_ok :
  dsdp 15 = 
  ([:: Finish; Finish; Finish],
   [:: [:: d (v3 * u3 + r3 + (v2 * u2 + r2) - r2 - r3 + u1 * v1);
           e (E alice (v3 * u3 + r3 + (v2 * u2 + r2))); 
           e (E charlie v3);
           e (E bob v2);
           d r3; d r2; d u3; d u2; d u1; d v1; k dk_a];
       [:: e (E charlie (v3 * u3 + r3));
           e (E bob (v2 * u2 + r2)); d v2; k dk_b];
       [:: e (E charlie (v3 * u3 + r3 + (v2 * u2 + r2))); d v3; k dk_c]
  ]).
Proof. reflexivity. Qed.

(* Fuel for the interpreter != size of tuple we need
   But it must be sized as the number of fuel.
*)
Notation dsdp_traceT := (15.-bseq data).
Notation dsdp_tracesT := (3.-tuple dsdp_traceT).

Definition dsdp_traces : dsdp_tracesT :=
  interp_traces 15 [:: palice dk_a v1 u1 u2 u3 r2 r3; pbob dk_b v2; pcharlie dk_c v3].

Definition is_dsdp (trs : dsdp_tracesT) :=
  let '(s, u3, u2, u1, v1) :=
    if tnth trs 0 is Bseq [:: inl (inl s); _; _; _; _; _;
                           inl (inl u3); inl (inl u2); inl (inl u1); inl (inl v1); _] _
    then (s, u3, u2, u1, v1) else (0, 0, 0, 0, 0) in
  let '(v2) :=
    if tnth trs 1 is Bseq [:: _; _; inl (inl v2); _] _
    then (v2) else (0) in
  let '(_v3) :=
    if tnth trs 2 is Bseq [:: _; inl (inl v3); _] _
    then (v3) else (0) in
  s = v3 * u3 + v2 * u2 + v1 * u1.

Lemma dsdp_traces_ok :
  dsdp_traces =
    [tuple
       [bseq d (v3 * u3 + r3 + (v2 * u2 + r2) - r2 - r3 + u1 * v1);
             e (E alice (v3 * u3 + r3 + (v2 * u2 + r2)));
             e (E charlie v3);
             e (E bob v2);
             d r3; d r2; d u3; d u2; d u1; d v1; k dk_a];
       [bseq e (E charlie (v3 * u3 + r3));
             e (E bob (v2 * u2 + r2)); d v2; k dk_b];
       [bseq e (E charlie (v3 * u3 + r3 + (v2 * u2 + r2))); d v3; k dk_c]].
Proof. by apply/val_inj/(inj_map val_inj); rewrite interp_traces_ok. Qed.

Lemma dsdp_is_correct:
  is_dsdp dsdp_traces.
Proof. rewrite dsdp_traces_ok /is_dsdp /=.
ring.
Qed.

End dsdp.

Section dsdp_information_leakage_proof.

Variable T : finType.
Variable P : R.-fdist T.

(* If A is const-RV actually P |= A _|_ A.
   But in protocol views we don't have such RVs.
*)
Hypothesis neg_self_indep : forall (TA : finType)(A : {RV P -> TA}), ~ P |= A _|_ A.

Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.

Let msg := 'I_m.  (* = Z/mZ *)
Let card_msg : #|msg| = m.
Proof. by rewrite card_ord. Qed.

Let enc := enc party msg.
Let pkey := pkey party msg.

(* This is for {RV P -> (different parties x different messages} *)
Let card_enc : #|(enc : finType)| = (#|(party : finType)| * m).-1.+1.
Proof. rewrite /enc /dsdp_program.enc card_prod card_ord.
rewrite prednK // muln_gt0 /= ltn0Sn andbT.
apply/card_gt0P.
by exists Alice. (* Note: when goal has `exist...`, this solves it. *)
Qed.

Let card_enc_for p : #|(p.-enc msg : finType)| = m.-1.+1.
Proof. by rewrite card_enc_for. Qed.

Let enc0 := E NoParty (0 : msg).

Let data := (msg + enc + pkey)%type.
Let d x : data := inl (inl x).
Let e x : data := inl (inr x).
Let k x : data := inr x.

Notation dsdp_traceT := (15.-bseq data).
Notation dsdp_tracesT := (3.-tuple dsdp_traceT).
Notation "u *h w" := (Emul u w).
Notation "u ^h w" := (Epow u w).

(* The 3 keys are defined in the previous section and they only need the `msg` type
   extracted from them to be fulfilled.
*)
Definition dsdp_uncurry (o: Alice.-key Dec msg * Bob.-key Dec msg * Charlie.-key Dec msg * msg * msg * msg * msg * msg * msg * msg * msg)
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

Section alice_is_leakage_free_or_not.

Local Notation m := m_minus_2.+2.

Let alice_traces : RV dsdp_traceT P :=
      (fun t => tnth t 0) `o dsdp_RV inputs.

(* Use these two and apply_inde_RV_comp to prove trivial indeps*)
Let alice_inputs_RV := [% dk_a, v1, u1, u2, u3, r2, r3].
Let alice_inputsT := (Alice.-key Dec msg * msg * msg * msg * msg * msg * msg)%type.

Goal P |= [% v1 , u1] _|_ v2.
Proof.
have := alice_indep inputs.
pose f := fun (ls : alice_inputsT) =>
  let '(_, v1 , u1, _, _, _, _) := ls in (v1 , u1).
pose g := fun (rs : (msg * msg)) =>
  let '(v2 , v3) := rs in v2.
by apply_inde_rv_comp f g.
Qed.

(* E_charlie_v3 means it is encrypted (so generated) by the key of charlie.
   So it is counted as "generated" on party charlie.
   Therefore, encrypted RVs should be independent of other parties.
   Even other parties can add messages by HE properties, but addition to a RV
   means the independence keeps after the addition.

   TODO: cannot use smc_inde.v things here because RV2, RV msg and RV enc are all
   different types. They cannot be contained by one fset.
*)

Hypothesis inde_Echarlie : P |= alice_inputs_RV _|_ E_charlie_v3.
Hypothesis inde_Ebob : P |= alice_inputs_RV _|_ E_bob_v2.

Let alice_view_valuesT := (Alice.-key Dec msg * msg * msg * msg * msg * msg * msg * msg *
  Alice.-enc msg * Charlie.-enc msg * Bob.-enc msg)%type.

Let alice_view := [% dk_a, s, v1 , u1, u2, u3, r2, r3,
      E_alice_d3, E_charlie_v3, E_bob_v2].

Let alice_traces_from_view
  (v : alice_view_valuesT) : 15.-bseq _ :=
    let '(dk_a, s, v1 , u1, u2, u3, r2, r3, E_alice_d3, E_charlie_v3, E_bob_v2) := v in
    [bseq d s;
            e (E_alice_d3 : enc);
            e (E_charlie_v3 : enc);
            e (E_bob_v2 : enc);
            d r3; d r2; d u3; d u2; d u1; d v1; k (dk_a : pkey)].

Lemma alice_traces_from_viewP :
  alice_traces = alice_traces_from_view `o alice_view.
Proof.
apply: boolp.funext => x /=.
rewrite /alice_traces /dsdp_RV /comp_RV /=.
rewrite dsdp_traces_ok //=.
have Ha : dsdp_program.k (Alice, Dec, (dk_a x).2) = k (dk_a x).
  (* Coq doesn't know this is the only case, and it makes both sides equal*)
  by case: dk_a => t. 
rewrite  -[in RHS]Ha //=.
Qed.

Let alice_view_values_from_trace (xs : dsdp_traceT) : alice_view_valuesT :=
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
case: a => -[a ma] /=.  (* msg from `case: a` can be case again to get 1. nat a 2. nat a < m*)
case: c => -[c mc] /=.
case: b => -[b mb] /=.
case: dk => -[dk mdk] /=.
by [].
Qed.
(* Automation: break until the end of the seq *)

Lemma ce_alice_traces_view (w : finType) (v : {RV P -> w}) :
  `H(v | alice_traces ) = `H(v | alice_view ).
Proof.
transitivity (`H(v | [%alice_traces, alice_view])).
  have -> : alice_view = alice_view_values_from_trace `o alice_traces.
    by apply: boolp.funext => x /= ; rewrite alice_traces_from_viewP /comp_RV alice_view_values_from_traceP.
  by rewrite scp.fun_cond_removal.
by rewrite alice_traces_from_viewP scp.cond_entropyC scp.fun_cond_removal.
Qed.

Let alice_input_view := [%dk_a, v1, u1, u2, u3, r2, r3].
Notation alice_input_view_valT :=
  (Alice.-key Dec msg * msg * msg * msg * msg * msg * msg)%type.

Section cond_entropy_v2_s_removal.

Notation "x \+ y" := (smc_proba.add_RV x y).  

Definition dotp2 (x y: (msg * msg)) := x.1 * y.1 + x.2 * y.2.
Definition dotp2_rv (X Y : {RV P -> (msg * msg)}) : {RV P -> msg} :=
  fun p => dotp2 (X p) (Y p).

Definition us := [%u2, u3].
Definition vs := [%v2, v3].
Definition const_us := [% (fun _ => 1):{RV P -> msg}, (fun _ => 0):{RV P -> msg}].
Definition r : {RV P -> msg} := v1 \* u1.

Let f (a : alice_input_view_valT) :=
  let '(_, _, _, u2, u3, _, _) := a in
  (u2, u3).

Let g (a : alice_input_view_valT) :=
  let '(_, v1, u1, _, _, _, _) := a in
  v1 * u1.

Lemma s_alt :
  s = dotp2_rv us vs \+ r.
Proof.
rewrite /s /us /vs /d3 /vu3r /d2 /vu3 /vu2 /r.
rewrite /dotp2_rv /dotp2 //=.
rewrite /smc_proba.add_RV.
apply: boolp.funext => i //=.
ring.
Qed.

(* So if a set of events is sized one (from an intersection, for example);
   the probability of it is the probability of the only event inside it,
   decided by the distribution.

   "the probability of random variables A and B are not independent",
   is equal to a new random variable outputs 1 for the only k events in K
   makes them not independent, while outputs 0 for other p events in ~K.
   The total number of events are k+p, and it is the size of (K :|: ~K).

   "events make A and B are not independent" means there are some events
   in A :&: B. In the DSDP case, it means all events that `v2` encodes them as `v`,
   while `dotp2_rv us vs` also encodes them as `v`. If we unfold it more,
   the probability of such an event must be related to the probability that
   another random variable `us` outputs `(1, 0)`. But how possible it is,
   depends on the distribution of `us`: if an active adversary controls Alice,
   force `us` always output `(1, 0)`, then `v2 _|_ dotp2_rv us vs` is impossible.
   In contrast, if Alice is an fair player, the probability that `us` outputs that
   specific value is 1/m^2. Finally, if Bob enforce ZPK check to abort the protocol
   when that value is generated, `v2 _|_ dotp2_rv us vs` is a sure thing, and the protocol
   is secure with that mitigation ("security with abort").

   Anyway, I need to show that `us = (1, 0) -> ~ v2 _|_ dotp2_rv us vs` and
   `us != (1, 0) ->  v2 _|_ dotp2_rv us vs`.
*)

(* It is saying that `us` outputs an pair of encoded values (1, 0),
   _as two const RVs_ do that, v2 will be disclosed.
*)
Lemma ext_v2_discloser:
  exists a b: msg,
    dotp2_rv [% (fun _ => a):{RV P -> msg}, (fun _ => b):{RV P -> msg}] vs = v2.  
Proof.
rewrite /dotp2_rv.
exists 1.
exists 0.
rewrite /vs /dotp2 /fst /snd /comp_RV.
apply: boolp.funext => i //=.
ring.
Qed.

Lemma const_us_is_v2_discloser:
  us = const_us -> dotp2_rv us vs = v2.
Proof.
move => H.
rewrite H.
rewrite /const_us /vs /dotp2_rv /dotp2 /fst /snd /comp_RV.
apply: boolp.funext => i //=.
ring.
Qed.

Lemma neg_r_aiv_indep:
  ~ P |= r _|_ alice_input_view.
Proof.
(* r is the result of composition;
   showing that how alice_input_view is composed to become r,
   by the assumption P |= r _|_ alice_input_view.

   (~ A is just A -> False)
*)
move/(smc_proba.inde_rv_comp idfun g).
have -> : g `o alice_input_view = r.
  by apply: boolp.funext => i.
have -> : idfun `o r = r.
  by apply: boolp.funext => i.
(* Showing that by assuming P |= r _|_ alice_input_view true,
   what will become false.
*)
exact: neg_self_indep.
Qed.

(* Example of how to raise counter example:
   Only when goal is ~ for all, we can have it.
*)
Goal ~ forall x : nat, x = 0.
Search (~ forall _, _).
rewrite -existsNP.
exists (1 : nat).
by [].
Qed.

Hypothesis r_unif : `p_ r = fdist_uniform card_msg.
Hypothesis s_aiv_neg0 : forall x a, `Pr[ [% s, alice_input_view] = (x, a) ] != 0.
Lemma neg_r_v2aivdotp_indep (v x : msg) (a : alice_input_view_valT):
  ~ P |= r _|_ [% v2, alice_input_view, dotp2_rv us vs].
Proof.
pose h := (fun o : (msg * alice_input_view_valT * msg) => let '(_, aiv, _) := o in (g aiv):msg).
move/(smc_proba.inde_rv_comp idfun h).
have -> : h `o [%v2, alice_input_view, dotp2_rv us vs] = r.
  by apply: boolp.funext => i.
have -> : idfun `o r = r.
  by apply: boolp.funext => i.
exact: neg_self_indep.
Qed.

End cond_entropy_v2_s_removal.

Let dec_view := [%dk_a, s, v1 , u1, u2, u3, r2, r3].
Let eqn1_view := [% dec_view, E_alice_d3, E_charlie_v3].
Let eqn2_view := [% dec_view, E_alice_d3].
 
Hypothesis alice_view_neq0:
  forall x e, `Pr[ [% dec_view, E_alice_d3, E_charlie_v3, E_bob_v2] =
        (x, e) ] != 0.

Hypothesis eqn1_view_neq0 :
  forall x e, `Pr[ [% dec_view, E_alice_d3, E_charlie_v3] =
        (x, e) ] != 0.

Hypothesis eqn2_view_neq0 :
  forall x e, `Pr[ [% dec_view, E_alice_d3] =
        (x, e) ] != 0.

(* This lemma shows that if an active adversary controls Alice,
   it can set u1 and u2 as a special combination (1, 0),
   which allows revealing `v2` from the result that Alice receives.

   A related discussion is in the Sect~5.2 in the original paper.

   NOTE: the mitigation that Bob checks ZKP to decide if Alice is
   cheating with the values or not,
   is an implementation of the idea of "security with abort" in those abstract
   information-theoretic papers.
*)
Lemma if_u1u2_are_compromised_alice_is_not_leakage_freeP :
  us = const_us -> ~ `H(v2 | alice_view ) = `H `p_v2.
Proof.
move => H.
(* From alice_view to [% alice_input_view, s] *)
rewrite !(E_enc_ce_removal v2 card_msg).
pose h := (fun o : (Alice.-key Dec msg * msg * msg * msg * msg * msg * msg * msg) =>
  let '(dk_a, s, v1, u1, u2, u3, r2, r3) := o in (dk_a, v1, u1, u2, u3, r2, r3, s)).
pose h' := (fun o : (Alice.-key Dec msg * msg * msg * msg * msg * msg * msg * msg) =>
  let '(dk_a, v1, u1, u2, u3, r2, r3, s) := o in (dk_a, s, v1, u1, u2, u3, r2, r3)).
rewrite -(scp.fun_cond_removal _ _ h).
have ->: `H( v2 | [% dk_a, s, v1, u1, u2, u3, r2, r3, h `o [% dk_a, s, v1, u1, u2, u3, r2, r3]]) = `H( v2 | [% dk_a, s, v1, u1, u2, u3, r2, r3, [% dk_a, v1, u1, u2, u3, r2, r3, s]]).
  by [].
rewrite scp.cond_entropyC (scp.fun_cond_removal _ _ h') -/alice_input_view.
(* From the cond_entropy to the independence goal via mutual info *)
move => H2.
have: `I(v2;[%alice_input_view, s]) = 0.
  by rewrite mutual_info_RVE H2 subrr.
move/mutual_info0_indep.
(* Show the independence is impossible if Alice is being controlled
   and cheat with the specific `us`*)
rewrite s_alt.
rewrite /smc_proba.add_RV //=.
rewrite (const_us_is_v2_discloser H).
pose z := (fun o : (alice_input_view_valT * msg) =>
  let '(_, v1, u1, _, _, _, _, v2_r) := o in v2_r - v1 * u1).
move/(smc_proba.inde_rv_comp idfun z).
have -> : z `o [% alice_input_view, v2 \+ r] = v2.
  rewrite /z /r /comp_RV.
  apply: boolp.funext => i //=.
  by ring.
have -> : idfun `o v2 = v2.
  by apply: boolp.funext => i.
exact: neg_self_indep.
exact: eqn2_view_neq0.
exact: eqn1_view_neq0.
exact: alice_view_neq0.
Qed.


End alice_is_leakage_free_or_not.

End dsdp_information_leakage_proof.
