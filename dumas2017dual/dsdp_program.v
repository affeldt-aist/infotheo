From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix Rstruct ring boolp finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter smc_indep smc_tactics.

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

Section he.

Variable party : finType.
Variable msg : finComRingType.

Definition enc := (party * msg)%type.

Definition E i m : enc := (i, m).

Definition D (p : party) (e : enc) : option msg :=
  match e with
  | (i, m) => if i == p then Some m else None
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

Lemma card_enc_for : #|{:p.-enc T}| = #|T|.
Proof.
apply (bij_eq_card (f:=@enc_for_v p T)).
exists (@EncFor p T).
by case.
by [].
Qed.

End enc_types.

Section dsdp.
  
Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.
Let msg := 'I_m.  (* = Z/mZ *)

Let enc := enc party msg.

Notation "u *h w" := (Emul u w).
Notation "u ^h w" := (Epow u w).

Definition alice : party := Alice.
Definition bob : party := Bob.
Definition charlie : party := Charlie.

Definition data := (msg + enc)%type.
Definition d x : data := inl x.
Definition e x : data := inr x.


(* Should receive something the party can decrypt *)
Definition Recv_dec frm i f : proc data :=
  Recv frm (fun x => if x is inr v then
                       if D i v is Some v' then f v' else Fail
                     else Fail).

(* Should receive something the party cannot decrypt,
   but can do HE computation over it.
*)
Definition Recv_enc frm i f : proc data :=
  Recv frm (fun x => if x is inr v then
                       if D i v is Some v' then Fail else f v
                     else Fail).

Definition pbob (v2 : msg) : proc data :=
  Init (d v2) (
  Send n(alice) (e (E bob v2)) (
  Recv_dec n(alice) bob (fun d2 =>
  Recv_enc n(alice) bob (fun a3 =>
    Send n(charlie) (e (a3 *h (E charlie d2))) (
  Finish))))).

Definition pcharlie (v3 : msg) : proc data :=
  Init (d v3) (
  Send n(alice) (e (E charlie v3)) (
  Recv_dec n(bob) charlie (fun d3 => (
    Send n(alice) (e (E alice d3))
  Finish)))).

Definition palice (v1 u1 u2 u3 r2 r3: msg) : proc data :=
  Init (d v1) (
  Init (d u1) (
  Init (d u2) (
  Init (d u3) (
  Init (d r2) (
  Init (d r3) (
  Recv_enc n(bob) alice (fun c2 =>
  Recv_enc n(charlie) alice (fun c3 =>
  let a2 := (c2 ^h u2 *h (E bob r2)) in
  let a3 := (c3 ^h u3 *h (E charlie r3)) in
    Send n(bob) (e a2) (
    Send n(bob) (e a3) (
    Recv_dec n(charlie) alice (fun g =>
    Ret (d ((g - r2 - r3 + u1 * v1)))))))))))))).
  
Variables (v1 v2 v3 u1 u2 u3 r2 r3 : msg).
Definition dsdp h :=
  (interp h [:: palice v1 u1 u2 u3 r2 r3; pbob v2; pcharlie v3] [::[::];[::];[::]]).


(* Different from SMC scalar product: has much less calculations *)
Goal (dsdp 15).2 = ([::]).
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
rewrite -lock (lock (2 : nat)) /=.
rewrite -lock (lock (1 : nat)) /=.
rewrite !/Emul /=.
Abort.

Lemma dsdp_ok :
  dsdp 15 = 
  ([:: Finish; Finish; Finish],
   [:: [:: d (v3 * u3 + r3 + (v2 * u2 + r2) - r2 - r3 + u1 * v1);
           e (E alice (v3 * u3 + r3 + (v2 * u2 + r2))); 
           e (E charlie v3);
           e (E bob v2);
           d r3; d r2; d u3; d u2; d u1; d v1];
       [:: e (E charlie (v3 * u3 + r3));
           e (E bob (v2 * u2 + r2)); d v2];  (* Eventually will be recorded in Recv or Ret*)
       [:: e (E charlie (v3 * u3 + r3 + (v2 * u2 + r2))); d v3]
  ]).
Proof. reflexivity. Qed.

(* Fuel for the interpreter != size of tuple we need
   But it must be sized as the number of fuel.
*)
Notation dsdp_traceT := (15.-bseq data).
Notation dsdp_tracesT := (3.-tuple dsdp_traceT).

Definition dsdp_traces : dsdp_tracesT :=
  interp_traces 15 [:: palice v1 u1 u2 u3 r2 r3; pbob v2; pcharlie v3].

Definition is_dsdp (trs : dsdp_tracesT) :=
  let '(s, u3, u2, u1, v1) :=
    if tnth trs 0 is Bseq [:: inl s; _; _; _; _; _; inl u3; inl u2; inl u1; inl v1] _
    then (s, u3, u2, u1, v1) else (0, 0, 0, 0, 0) in
  let '(v2) :=
    if tnth trs 1 is Bseq [:: _; _; inl v2] _
    then (v2) else (0) in
  let '(_v3) :=
    if tnth trs 2 is Bseq [:: _; inl v3] _
    then (v3) else (0) in
  s = v3 * u3 + v2 * u2 + v1 * u1.

Lemma dsdp_traces_ok :
  dsdp_traces =
    [tuple
       [bseq d (v3 * u3 + r3 + (v2 * u2 + r2) - r2 - r3 + u1 * v1);
             e (E alice (v3 * u3 + r3 + (v2 * u2 + r2)));
             e (E charlie v3);
             e (E bob v2);
             d r3; d r2; d u3; d u2; d u1; d v1];
       [bseq e (E charlie (v3 * u3 + r3));
             e (E bob (v2 * u2 + r2)); d v2];
       [bseq e (E charlie (v3 * u3 + r3 + (v2 * u2 + r2))); d v3]].
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

Variable m_minus_2 : nat.
Local Notation m := m_minus_2.+2.

Let msg := 'I_m.  (* = Z/mZ *)
Let card_msg : #|msg| = m.
Proof. by rewrite card_ord. Qed.

Let enc := enc party msg.

(* This is for {RV P -> (different parties x different messages} *)
Let card_enc : #|(enc : finType)| = (#|(party : finType)| * m).-1.+1.
Proof. rewrite /enc /dsdp_program.enc card_prod card_ord.
rewrite prednK // muln_gt0 /= ltn0Sn andbT.
apply/card_gt0P.
by exists Alice. (* Note: when goal has `exist...`, this solves it. *)
Qed.

Let card_enc_forE p : #|(p.-enc msg : finType)| = m.-1.+1.
Proof. by rewrite card_enc_for. Qed.

Let enc0 := E NoParty (0 : msg).

Let data := (msg + enc)%type.
Let d x : data := inl x.
Let e x : data := inr x.

Notation dsdp_traceT := (15.-bseq data).
Notation dsdp_tracesT := (3.-tuple dsdp_traceT).
Notation "u *h w" := (Emul u w).
Notation "u ^h w" := (Epow u w).


Definition dsdp_uncurry (o: msg * msg * msg * msg * msg * msg * msg * msg)
  : dsdp_tracesT :=
  let '( v1, v2 , v3, u1, u2, u3, r2, r3) := o in
  (dsdp_traces v1 v2 v3 u1 u2 u3 r2 r3).

Record dsdp_random_inputs :=
  DSDPRandomInputs {
    v1 : {RV P -> msg};
    v2 : {RV P -> msg};
    v3 : {RV P -> msg};
    u1 : {RV P -> msg};
    u2 : {RV P -> msg};
    u3 : {RV P -> msg};
    r2 : {RV P -> msg};
    r3 : {RV P -> msg};

    alice_indep : P |= [% v1 , u1, u2, u3, r2, r3] _|_ [% v2, v3];

    pv1_unif : `p_ v1 = fdist_uniform card_msg;
    pv2_unif : `p_ v2 = fdist_uniform card_msg;
    pv3_unif : `p_ v3 = fdist_uniform card_msg;
    pu2_unif : `p_ u2 = fdist_uniform card_msg;
    pu3_unif : `p_ u3 = fdist_uniform card_msg;
    pr2_unif : `p_ r2 = fdist_uniform card_msg;
    pr3_unif : `p_ r3 = fdist_uniform card_msg;
}.

Variable inputs : dsdp_random_inputs.

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
    [%v1, v2, v3, u1, u2, u3, r2, r3].

Axiom E_enc_unif : forall (X : {RV P -> msg}) (p : party),
  `p_ X = fdist_uniform card_msg -> `p_ (E' p `o X) = fdist_uniform (card_enc_forE p).
(* TODO: prove this after the bij_RV_unif is merged *)

Axiom E_enc_inde_msg : forall (A B : finType) (p : party) (X : {RV P -> p.-enc A}) (Y : {RV P -> B}),
  P |= X _|_ Y.
(* TODO: what if B is (p.-enc A) ? Whether we need a way to judge if B is (p.-enc A) or not?*)

Section alice_is_leakage_free.

Local Notation m := m_minus_2.+2.

Let alice_traces : RV dsdp_traceT P :=
      (fun t => tnth t 0) `o dsdp_RV inputs.

(* Use these two and apply_inde_RV_comp to prove trivial indeps*)
Let alice_inputs_RV := [% v1 , u1, u2, u3, r2, r3].
Let alice_inputsT := (msg * msg * msg * msg * msg * msg)%type.

Goal P |= [% v1 , u1] _|_ v2.
Proof.
have := alice_indep inputs.
pose f := fun (ls : alice_inputsT) =>
  let '(v1 , u1, _, _, _, _) := ls in (v1 , u1).
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

Let alice_view_valuesT := (msg * msg * msg * msg * msg * msg * msg *
  Alice.-enc msg * Charlie.-enc msg * Bob.-enc msg)%type.

Let alice_view := [%s, v1 , u1, u2, u3, r2, r3,
      E_alice_d3, E_charlie_v3, E_bob_v2].

Let alice_traces_from_view
  (v : alice_view_valuesT) : 15.-bseq _ :=
    let '(s, v1 , u1, u2, u3, r2, r3, E_alice_d3, E_charlie_v3, E_bob_v2) := v in
    [bseq d s;
            e (E_alice_d3 : enc);
            e (E_charlie_v3 : enc);
            e (E_bob_v2 : enc);
            d r3; d r2; d u3; d u2; d u1; d v1].

Lemma alice_traces_from_viewP :
  alice_traces = alice_traces_from_view `o alice_view.
Proof.
apply: boolp.funext => x /=.
rewrite /alice_traces /dsdp_RV /comp_RV /=.
by rewrite dsdp_traces_ok.
Qed.

Let alice_view_values_from_trace (xs : dsdp_traceT) : alice_view_valuesT :=
    let failtrace := (0, 0, 0, 0, 0, 0, 0, E' Alice 0, E' Charlie 0, E' Bob 0) in
    if xs is Bseq [:: inl s;
           inr E_alice_d3;
           inr E_charlie_v3;
           inr E_bob_v2;
           inl r3; inl r2; inl u3; inl u2; inl u1; inl v1] _
    then 
         if (E_alice_d3, E_charlie_v3, E_bob_v2) is
              ((Alice, d3), (Charlie, v3), (Bob, v2)) then
            (s, v1 , u1, u2, u3, r2, r3,
               E' Alice d3, E' Charlie v3, E' Bob v2)
         else failtrace
    else failtrace.

Lemma alice_view_values_from_traceP:
   cancel alice_traces_from_view alice_view_values_from_trace.
Proof.
move => [] [] [] [] [] [] [] [] [] [] ? ? ? ? ? ? ? ? a c b //=.
case: a => -[a ma] /=.
case: c => -[c mc] /=.
case: b => -[b mb] /=.
by [].
Qed.
  
Lemma ce_alice_traces_view (w : finType) (v : {RV P -> w}) :
  `H(v | alice_traces ) = `H(v | alice_view ).
Proof.
transitivity (`H(v | [%alice_traces, alice_view])).
  have -> : alice_view = alice_view_values_from_trace `o alice_traces.
    by apply: boolp.funext => x /= ; rewrite alice_traces_from_viewP /comp_RV alice_view_values_from_traceP.
  by rewrite scp.fun_cond_removal.
by rewrite alice_traces_from_viewP scp.cond_entropyC scp.fun_cond_removal.
Qed.

Section eqn1.

Let Y1 := v2.
Let Y2 := alice_view.
Let Y3 := E_bob_v2.

Let Y3_unif : `p_ Y3 = fdist_uniform card_enc.
Proof. by rewrite /Y3 /E_bob_v2 E_enc_unif // (pv2_unif inputs). Qed.

Lemma eqn1P :
  `H(v2 | alice_view ) = `H(v2| [%s, v1 , u1, u2, u3, r2, r3, E_alice_d3, E_bob_v2]).
Proof. rewrite /alice_view.
Abort.

End eqn1.

Lemma alice_is_leakage_freeP :
  `H(v2 | alice_view ) = `H `p_v2.
Proof.
transitivity (`H(v2| [%s, v1 , u1, u2, u3, r2, r3, E_alice_d3] )).
  have Hb : P |= E_bob_v2 _|_ [%s, v1 , u1, u2, u3, r2, r3, E_alice_d3].
  admit.
  have Hc : P |= E_charlie_v3 _|_ [%s, v1 , u1, u2, u3, r2, r3, E_alice_d3].
  admit.
    
admit.
transitivity (`H(v2| [%s, v1 , u1, u2, u3, r2, r3, E_alice_d3] )).
admit.
transitivity (`H(v2| [%s, v1 , u1, u2, u3, r2, r3] )).
admit.
transitivity (`H(v2| [%s, v1 , u1, u2, u3, r2] )).
admit.
transitivity (`H(v2| [%s, v1 , u1, u2, u3] )).
admit.
transitivity (`H(v2| [%s, v1 , u1, u2] )).
admit.
transitivity (`H(v2| [%s, v1 , u1] )).
admit.
transitivity (`H(v2| [%s, v1] )).
admit.
transitivity (`H(v2| s )).
admit.
Abort.

End alice_is_leakage_free.

End dsdp_information_leakage_proof.
