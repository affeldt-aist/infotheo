From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
Require Import smc_interpreter.

(**md**************************************************************************)
(* # Session Types for SMC Protocols                                          *)
(*                                                                            *)
(* Binary session types for verifying communication protocols in SMC.         *)
(* Session environment is automatically inferred by Coq's unification.        *)
(*                                                                            *)
(* Two layers:                                                                *)
(*   sproc party env - session-typed process (type-checked)                   *)
(*   proc         - unindexed process (for interpretation)                    *)
(*                                                                            *)
(* Based on:                                                                  *)
(* Kohei Honda, Vasco T. Vasconcelos, and Makoto Kubo.                        *)
(* "Language Primitives and Type Discipline for Structured                    *)
(*  Communication-Based Programming."                                         *)
(* In ESOP 1998, LNCS 1381, pp. 122-138. Springer, 1998.                      *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(** * Session Type Definitions                                                *)
(******************************************************************************)

Section stype_def.

(* dtype: user-defined data kind type (e.g., DT_Vec | DT_One) *)
Variable dtype : eqType.

(* Session type: parameterized by dtype to avoid combinatorial explosion *)
Inductive stype : Type :=
  | STSend : dtype -> stype -> stype   (* !d.S - send data of kind d *)
  | STRecv : dtype -> stype -> stype   (* ?d.S - receive data of kind d *)
  | STEnd : stype.                     (* end - session finished *)

(* Session environment: maps party ID to session type with that party *)
Definition senv : Type := nat -> stype.

(* Empty environment: no communication with anyone *)
Definition senv_end : senv := fun _ => STEnd.

(* Prepend a Send to environment for specific party *)
Definition senv_send (env : senv) (dst : nat) (d : dtype) : senv :=
  fun p => if p == dst then STSend d (env p) else env p.

(* Prepend a Recv to environment for specific party *)
Definition senv_recv (env : senv) (src : nat) (d : dtype) : senv :=
  fun p => if p == src then STRecv d (env p) else env p.

End stype_def.

(* Make stype arguments explicit for clarity *)
Arguments STSend {dtype}.
Arguments STRecv {dtype}.
Arguments STEnd {dtype}.
Arguments senv_end {dtype}.
Arguments senv_send {dtype}.
Arguments senv_recv {dtype}.

(******************************************************************************)
(** * Session-Indexed Process Type                                            *)
(******************************************************************************)

Section sproc_def.

Variable dtype : eqType.
Variable data : Type.

(* Process indexed by: which party I am (party), fuel (n), session environment (env) *)
(* Both fuel AND session env are inferred by Coq's unification! *)
(* Fuel is used to compute interpreter steps; erased when converting to proc *)
Inductive sproc (party : nat) : nat -> senv dtype -> Type :=

  (* Finish: base case, fuel=1, empty session environment *)
  | SFinish : sproc party 1 senv_end
  
  (* Ret: returns value, fuel=2, empty session environment *)
  | SRet : data -> sproc party 2 senv_end
  
  (* Init: doesn't affect session types, increments fuel *)
  | SInit : forall n env,
      data -> 
      sproc party n env -> 
      sproc party n.+1 env
  
  (* Send: prepends STSend to session with dst, increments fuel *)
  | SSend : forall n env dst (dt : dtype),
      data ->
      sproc party n env ->
      sproc party n.+1 (senv_send env dst dt)
  
  (* Recv: prepends STRecv to session with src, increments fuel *)
  | SRecv : forall n env src (dt : dtype),
      (data -> sproc party n env) ->
      sproc party n.+1 (senv_recv env src dt)
  
  (* Fail: polymorphic in fuel and env for error handling *)
  | SFail : forall n env, sproc party n env.

End sproc_def.

Arguments SFinish {dtype data party}.
Arguments SRet {dtype data party}.
Arguments SInit {dtype data party n env}.
Arguments SSend {dtype data party n env} dst dt.
Arguments SRecv {dtype data party n env} src dt.
Arguments SFail {dtype data party n env}.

(******************************************************************************)
(** * Phase 1 Test: Minimal Example to Verify Unification                     *)
(******************************************************************************)

Section test_inference.

(* Simple dtype for testing: just two kinds *)
Inductive test_dtype : Type := DT_A | DT_B.

(* Make test_dtype an eqType - following pattern from homomorphic_encryption.v *)
Definition test_dtype_eqb_subproof (d1 d2 : test_dtype) : { d1 = d2 } + { d1 <> d2 }.
Proof. decide equality. Defined.

Definition test_dtype_eqb (d1 d2 : test_dtype) : bool :=
  if test_dtype_eqb_subproof d1 d2 then true else false.

Lemma test_dtype_eqP : Equality.axiom test_dtype_eqb.
Proof.
move=> d1 d2.
rewrite /test_dtype_eqb.
by case: test_dtype_eqb_subproof => /= H; constructor.
Qed.

HB.instance Definition _ := hasDecEq.Build test_dtype test_dtype_eqP.

(* Simple data type: just nat for testing *)
Definition test_data := nat.

(* Party identifiers for testing *)
Definition party0 : nat := 0.
Definition party1 : nat := 1.

(* TEST 1: Simple Finish - should infer fuel=1, env=senv_end *)
Definition test1 : @sproc test_dtype test_data party0 _ _ :=
  SFinish.

Check test1.
(* Should show: sproc ... party0 1 senv_end *)

(* TEST 2: Send then Finish - should infer fuel=2, env with one Send *)
Definition test2 : @sproc test_dtype test_data party0 _ _ :=
  SSend party1 DT_A 42 SFinish.

Check test2.
(* Should show: sproc ... party0 2 (senv_send senv_end party1 DT_A) *)

(* TEST 3: Two Sends then Finish *)
Definition test3 : @sproc test_dtype test_data party0 _ _ :=
  SSend party1 DT_B 1 (SSend party1 DT_A 2 SFinish).

Check test3.

(* TEST 4: Init then Send then Finish *)
Definition test4 : @sproc test_dtype test_data party0 _ _ :=
  SInit 100 (SSend party1 DT_A 42 SFinish).

Check test4.

(* TEST 5: Recv then Finish - need explicit dtype *)
Definition test5 : @sproc test_dtype test_data party0 _ _ :=
  SRecv party1 DT_A (fun _ => SFinish).

Check test5.

(* TEST 6: Send to party1, Recv from party1 - mixed communication *)
Definition test6 : @sproc test_dtype test_data party0 _ _ :=
  SSend party1 DT_A 10 (SRecv party1 DT_B (fun _ => SFinish)).

Check test6.

(* TEST 7: More complex - communication with multiple parties *)
Definition party2 : nat := 2.

Definition test7 : @sproc test_dtype test_data party0 _ _ :=
  SRecv party2 DT_A (fun x =>
  SRecv party2 DT_B (fun y =>
  SSend party1 DT_A (x + y) SFinish)).

Check test7.

(* Verify we can extract session type information *)
Definition get_stype {dtype : eqType} {data : Type}
    {party : nat} {n : nat} {env : senv dtype} 
    (p : @sproc dtype data party n env) (them : nat) : stype dtype :=
  env them.

(* Extract inferred fuel from sproc *)
Definition get_fuel {dtype : eqType} {data : Type}
    {party : nat} {n : nat} {env : senv dtype} 
    (p : @sproc dtype data party n env) : nat := n.

(* Check session type of test7 with party1 *)
Eval compute in get_stype test7 party1.
(* Should show: STSend DT_A STEnd *)

(* Check session type of test7 with party2 *)
Eval compute in get_stype test7 party2.
(* Should show: STRecv DT_A (STRecv DT_B STEnd) *)

(* Check inferred fuel of test7 *)
Eval compute in get_fuel test7.
(* Should show: 4 *)

End test_inference.

(******************************************************************************)
(** * Duality (Phase 2 preview)                                               *)
(******************************************************************************)

Section duality.

Variable dtype : eqType.

(* Duality: send becomes recv, recv becomes send *)
Fixpoint dual (s : stype dtype) : stype dtype :=
  match s with
  | STSend d k => STRecv d (dual k)
  | STRecv d k => STSend d (dual k)
  | STEnd => STEnd
  end.

(* Duality is involutive *)
Lemma dual_involutive : forall s : stype dtype, dual (dual s) = s.
Proof.
move=> s.
elim: s => //=.
- move=> d s IH.
  rewrite IH.
  reflexivity.
- move=> d s IH.
  rewrite IH.
  reflexivity.
Qed.

End duality.

(******************************************************************************)
(** * Existential Process Wrapper (aproc)                                     *)
(******************************************************************************)

Section aproc_def.

Variable dtype : eqType.
Variable data : Type.

(* aproc: existentially wraps party, fuel, and senv so processes can be stored in lists *)
Definition aproc : Type := { party : nat & { n : nat & { env : senv dtype & @sproc dtype data party n env }}}.

(* Smart constructor *)
Definition mk_aproc {party : nat} {n : nat} {env : senv dtype} 
    (p : @sproc dtype data party n env) : aproc :=
  existT _ party (existT _ n (existT _ env p)).

(* Accessors *)
Definition aproc_party (ap : aproc) : nat := projT1 ap.
Definition aproc_fuel (ap : aproc) : nat := projT1 (projT2 ap).
Definition aproc_env (ap : aproc) : senv dtype := projT1 (projT2 (projT2 ap)).
Definition aproc_proc (ap : aproc) : @sproc dtype data (aproc_party ap) (aproc_fuel ap) (aproc_env ap) :=
  projT2 (projT2 (projT2 ap)).

(* Get session type with specific party *)
Definition aproc_stype (ap : aproc) (them : nat) : stype dtype :=
  aproc_env ap them.

End aproc_def.

Arguments mk_aproc {dtype data party n env}.
Arguments aproc_party {dtype data}.
Arguments aproc_fuel {dtype data}.
Arguments aproc_env {dtype data}.
Arguments aproc_proc {dtype data}.
Arguments aproc_stype {dtype data}.

(* Compute sum of all fuels from aproc list - used as interpreter fuel *)
Definition sum_fuel {dtype : eqType} {data : Type} (ps : seq (aproc dtype data)) : nat := 
  sumn (map aproc_fuel ps).

(* Notation for fuel computation *)
Notation "[> ps ]" := (sum_fuel ps) (at level 0).

(******************************************************************************)
(** * Session Type Decidable Equality                                         *)
(******************************************************************************)

Section stype_eq.

Variable dtype : eqType.

(* Decidable equality for session types *)
Fixpoint stype_eqb (s1 s2 : stype dtype) : bool :=
  match s1, s2 with
  | STEnd, STEnd => true
  | STSend d1 k1, STSend d2 k2 => (d1 == d2) && stype_eqb k1 k2
  | STRecv d1 k1, STRecv d2 k2 => (d1 == d2) && stype_eqb k1 k2
  | _, _ => false
  end.

Lemma stype_eqP : Equality.axiom stype_eqb.
Proof.
move=> s1 s2.
elim: s1 s2 => [d1 k1 IH|d1 k1 IH|] [d2 k2|d2 k2|] //=; try by constructor.
- case: (d1 =P d2) => [<-|Hneq] /=.
  + case: (IH k2) => [<-|Hneq]; first by constructor.
    constructor. by case.
  + constructor. by case.
- case: (d1 =P d2) => [<-|Hneq] /=.
  + case: (IH k2) => [<-|Hneq]; first by constructor.
    constructor. by case.
  + constructor. by case.
Qed.

HB.instance Definition _ := hasDecEq.Build (stype dtype) stype_eqP.

End stype_eq.

(******************************************************************************)
(** * Duality Checking                                                        *)
(******************************************************************************)

Section duality_check.

Variable dtype : eqType.

(* Check if two session types are dual *)
Definition are_dual (s1 s2 : stype dtype) : bool := s1 == dual s2.

(* Check if two aprocs have dual session types for communication between them *)
Definition channels_dual {data : Type} (ap1 ap2 : aproc dtype data) : bool :=
  let p1 := aproc_party ap1 in
  let p2 := aproc_party ap2 in
  (* ap1's view of p2 should be dual to ap2's view of p1 *)
  are_dual (aproc_stype ap1 p2) (aproc_stype ap2 p1).

End duality_check.

Arguments are_dual {dtype}.
Arguments channels_dual {dtype data}.

(******************************************************************************)
(** * Phase 2 Tests                                                           *)
(******************************************************************************)

Section test_phase2.

(* Reuse test_dtype from Phase 1 tests *)
Let dtype := test_dtype.
Let data := test_data.

(* Two-party protocol test *)
(* Party 0 sends to Party 1, then finishes *)
Definition proto_p0 : @sproc dtype data 0 _ _ :=
  SSend 1 DT_A 42 SFinish.

(* Party 1 receives from Party 0, then finishes *)
Definition proto_p1 : @sproc dtype data 1 _ _ :=
  SRecv 0 DT_A (fun _ => SFinish).

(* Wrap in aproc *)
Definition aproc_p0 : aproc dtype data := mk_aproc proto_p0.
Definition aproc_p1 : aproc dtype data := mk_aproc proto_p1.

(* Test: Extract session types *)
Eval compute in aproc_stype aproc_p0 1.  (* Should be: STSend DT_A STEnd *)
Eval compute in aproc_stype aproc_p1 0.  (* Should be: STRecv DT_A STEnd *)

(* Test: Extract fuel *)
Eval compute in aproc_fuel aproc_p0.  (* Should be: 2 *)
Eval compute in aproc_fuel aproc_p1.  (* Should be: 2 *)

(* Test: Check duality *)
Eval compute in channels_dual aproc_p0 aproc_p1.  (* Should be: true *)

(* Verify duality mathematically *)
Lemma proto_dual_correct : channels_dual aproc_p0 aproc_p1 = true.
Proof. by native_compute. Qed.

End test_phase2.

(******************************************************************************)
(** * Specialized Recv Wrappers                                               *)
(******************************************************************************)

(* These wrappers provide type-safe receive operations that:
   1. Specify the expected dtype for session type tracking
   2. Pattern match on data to extract the expected form
   3. Use SFail if the data doesn't match the expected form *)

Section recv_wrappers.

Variable dtype : eqType.
Variable data : Type.

(* A "checker" function that extracts a typed value from data, or fails *)
(* For example: is_scalar : data -> option TX *)
Variable T : Type.                    (* Target type (e.g., TX for scalars) *)
Variable dt : dtype.                  (* dtype for session tracking *)
Variable check : data -> option T.    (* Checker: data -> option T *)

(* Specialized receive: receive from src, check data, continue with typed value *)
Definition SRecv_check {party : nat} {n : nat} {env : senv dtype} 
    (src : nat) (f : T -> @sproc dtype data party n env) : @sproc dtype data party n.+1 (senv_recv env src dt) :=
  SRecv src dt (fun d => 
    match check d with
    | Some v => f v
    | None => SFail
    end).

End recv_wrappers.

Arguments SRecv_check {dtype data T dt check party n env} src.

(* Example instantiation for scalar product data types *)
Section recv_wrappers_example.

(* Define dtype for scalar product: vectors vs scalars *)
Inductive sp_dtype : Type := DT_Vec | DT_One.

Definition sp_dtype_eqb_subproof (d1 d2 : sp_dtype) : { d1 = d2 } + { d1 <> d2 }.
Proof. decide equality. Defined.

Definition sp_dtype_eqb (d1 d2 : sp_dtype) : bool :=
  if sp_dtype_eqb_subproof d1 d2 then true else false.

Lemma sp_dtype_eqP : Equality.axiom sp_dtype_eqb.
Proof.
move=> d1 d2. rewrite /sp_dtype_eqb.
by case: sp_dtype_eqb_subproof => /= H; constructor.
Qed.

HB.instance Definition _ := hasDecEq.Build sp_dtype sp_dtype_eqP.

(* Data type for scalar product: sum of vector and scalar *)
Variable TX : Type.  (* scalar type *)
Variable VX : Type.  (* vector type *)
Let sp_data := (TX + VX)%type.

(* Checkers *)
Definition is_scalar (d : sp_data) : option TX :=
  match d with inl v => Some v | inr _ => None end.

Definition is_vector (d : sp_data) : option VX :=
  match d with inr v => Some v | inl _ => None end.

(* Specialized receivers for scalar product *)
Definition SRecv_one {party n env} (src : nat) (f : TX -> @sproc sp_dtype sp_data party n env) 
    : @sproc sp_dtype sp_data party n.+1 (senv_recv env src DT_One) :=
  @SRecv_check sp_dtype sp_data TX DT_One is_scalar party n env src f.

Definition SRecv_vec {party n env} (src : nat) (f : VX -> @sproc sp_dtype sp_data party n env)
    : @sproc sp_dtype sp_data party n.+1 (senv_recv env src DT_Vec) :=
  @SRecv_check sp_dtype sp_data VX DT_Vec is_vector party n env src f.

End recv_wrappers_example.

(******************************************************************************)
(** * Erasure: Session Types -> Unindexed proc                                *)
(******************************************************************************)

(* Erase session types and fuel from sproc to get unindexed proc for interpretation *)

Section erasure.

Variable data : Type.
Variable dtype : eqType.

(* Erasure: convert session-typed sproc to unindexed proc *)
(* This erases BOTH the fuel index AND the session environment index *)
Fixpoint erase {party : nat} {n : nat} {env : senv dtype} 
    (p : @sproc dtype data party n env) : smc_interpreter.proc data :=
  match p with
  | SFinish => Finish
  | SRet d => Ret d
  | @SInit _ _ _ _ _ d k => Init d (erase k)
  | @SSend _ _ _ _ _ dst _ d k => Send dst d (erase k)
  | @SRecv _ _ _ _ _ src _ f => Recv src (fun d => erase (f d))
  | @SFail _ _ _ _ _ => Fail
  end.

(* Erase session-typed aproc to proc *)
Definition erase_aproc (ap : aproc dtype data) : smc_interpreter.proc data :=
  erase (aproc_proc ap).

(* Erase list of aprocs to list of procs, computing total fuel *)
Definition erase_aprocs (aps : seq (aproc dtype data)) : seq (smc_interpreter.proc data) :=
  map erase_aproc aps.

Lemma nofuel_proc_fail p : aproc_fuel p = 0 -> erase_aproc p = Fail.
Proof. by case: p => x [y] [e] [||n|n|n|n]. Qed.

Lemma nofuel_procs_fail (ps : seq (aproc dtype data)) :
  [> ps] = 0 -> erase_aprocs ps = nseq (size ps) Fail.
Proof.
rewrite /sum_fuel.
elim: ps => // p ps IH /=.
case Hp: (aproc_fuel p) => // /IH ->.
by rewrite nofuel_proc_fail.
Qed.

Definition aproc_default := @mk_aproc dtype data 0 0 senv_end SFail.

Definition dependent_mktuple (A : Type) n (P : 'I_n -> A -> Prop)
  (f : forall i, {a | P i a}) : {sa : n.-tuple A | forall i, P i (tnth sa i)}.
exists [tuple sval (f i) | i < n].
abstract (move=> i; rewrite tnth_mktuple; exact: (svalP (f i))).
Defined.

Lemma fuel_decreases (ps : seq (aproc dtype data)) k tr :
  k < size ps ->
  let res := step (erase_aprocs ps) (nth [::] tr k) k in
  { ap' | erase_aproc ap' = res.1.1 /\
      aproc_fuel ap' + res.2 <= aproc_fuel (nth aproc_default ps k) }.
Proof.
move => Hk /=.
rewrite /step (nth_map aproc_default) //.
move Hnth: (nth _ ps k) => [p [n] [env] sp].
rewrite {2}/aproc_fuel /=.
move/(f_equal erase_aproc): Hnth.
rewrite -(nth_map _ (default_proc _)) // -/(erase_aprocs ps).
rewrite /erase_aproc /aproc_proc /=.
case Hn: n env / sp =>
       [|d|n' env d s|n' env dst dt d s|n' env dst d s|n' env] Hnth /=.
- by exists (mk_aproc (party:=p) SFinish).
- by exists (mk_aproc (party:=p) SFinish).
- by exists (mk_aproc (party:=p) s); rewrite addn1.
- case Hnth': nth => [||k' p'|||];
    try by exists (mk_aproc (party:=p) (SSend dst dt d s)); rewrite addn0.
  case: ifPn => [/eqP|] k'k.
    by exists (mk_aproc (party:=p) s); rewrite addn1.
  by exists (mk_aproc (party:=p) (SSend dst dt d s)); rewrite addn0.
- case Hnth': nth => [|k' d' p'||||];
    try by exists (mk_aproc (party:=p) (SRecv dst d s));
           rewrite /= (addn0 (aproc_fuel _)).
  case: ifPn => [/eqP|] k'k.
    by exists (mk_aproc (party:=p) (s d')); rewrite addn1.
  by exists (mk_aproc (party:=p) (SRecv dst d s)); rewrite addn0.
- by exists aproc_default.
Qed.

Lemma fuel_suffices h (ps : seq (aproc dtype data))  traces res :
  (h >= [> ps])%N ->
  interp h (erase_aprocs ps) traces = res ->
  ~~ has snd [seq step res.1 (nth [::] res.2 i) i | i <- iota 0 (size ps)].
Proof.
elim: h ps traces => [|h IH] ps traces.
  rewrite leqn0 => /eqP /nofuel_procs_fail -> <- /=.
  rewrite has_map -all_predC; apply/allP => i /=.
  rewrite mem_iota add0n => /andP[_ Hi].
  by rewrite /step /= !nth_nseq // Hi.
move=> Hps /=.
set ps' := unzip1 (unzip1 _).
have hles tr :=
  dependent_mktuple (fun k : 'I_(size ps) => fuel_decreases tr (ltn_ord k)).
case: ifPn; last first.
  rewrite -!all_predC -!all_map -!map_comp size_map => /allP /= Hc <-.
  apply/allP => /= b /mapP[/= i Hi] ->.
  exact/Hc/map_f.
rewrite has_map => /hasP[k].
rewrite mem_iota size_map add0n => /andP[_ Hk] /= Hck.
set traces' := unzip2 _.
suff : exists aps', erase_aprocs aps' = ps' /\
         \sum_(0 <= i < size ps) aproc_fuel (nth aproc_default aps' i) <= h.
  case=> aps' [Haps' Hh'].
  have Hsz : size ps = size aps'.
    rewrite -(size_map erase_aproc aps') -/(erase_aprocs _) Haps' !size_map.
    by rewrite size_iota.
  rewrite Hsz -Haps'.
  apply: IH.
  by rewrite /sum_fuel sumnE big_map (big_nth aproc_default) -Hsz.
have [aps' Haps'] := hles traces.
exists aps'.
have Hsz : size aps' = size ps by rewrite size_tuple.
split.
  apply: (@eq_from_nth _ Fail).
    by rewrite !size_map size_tuple size_iota.
  move=> i; rewrite !size_map Hsz => Hi.
  rewrite (nth_map aproc_default) ?Hsz // (_ : i = Ordinal Hi) // -tnth_nth.
  rewrite (proj1 (Haps' _)) -[ps']map_comp -map_comp.
  by rewrite  (nth_map 0) ?size_iota?size_map // nth_iota.
rewrite -ltnS (leq_trans _ Hps) // ?(ltnW Hk) // /sum_fuel sumnE big_map.
rewrite -{3}(ssr_ext.map_nth_iota_id aproc_default ps) big_map.
rewrite -{3}(subn0 (size ps)) -/(index_iota _ _) -subn_gt0 -sumnB.
  rewrite lt0n sum_nat_seq_neq0.
  apply/hasP; exists k; first by rewrite mem_iota leq0n add0n subn0.
  rewrite /= -lt0n subn_gt0 -addn1 (_ : 1 = true) // -Hck.
  have [_] := Haps' (Ordinal Hk).
  by rewrite (tnth_nth aproc_default).
move=> i _.
case/boolP: (i < size aps') => Hi.
  rewrite Hsz in Hi.
  have [_] := Haps' (Ordinal Hi).
  rewrite (tnth_nth aproc_default) /=.
  exact/leq_trans/leq_addr.
by rewrite nth_default // leqNgt.
Qed.
End erasure.

Arguments erase {data dtype party n env}.
Arguments erase_aproc {data dtype}.
Arguments erase_aprocs {data dtype}.

(******************************************************************************)
(** * Notations for Session-Typed Process Lists                               *)
(******************************************************************************)

(* Declare scope for session-typed processes *)
Declare Scope sproc_scope.

(* Notation for packing session-typed processes into aproc list *)
(* Usage: [aprocs p ; .. ; q ] where p,q are sproc values *)
Notation "[aprocs p ; .. ; q ]" := 
  (cons (mk_aproc p) .. (cons (mk_aproc q) nil) ..)
  (at level 0) : sproc_scope.

(* Notation for erasing and running with inferred fuel *)
(* Usage: run_sprocs [aprocs p1; p2; p3] *)
Definition run_sprocs {dtype : eqType} {data : Type} 
    (aps : seq (aproc dtype data)) : seq (proc data) * seq (seq data) :=
  run_interp [> aps] (erase_aprocs aps).

Local Open Scope sproc_scope.

(******************************************************************************)
(** * Erasure Tests                                                           *)
(******************************************************************************)

Section test_erasure.

(* Test with concrete types *)
Let dtype := test_dtype.
Let data := test_data.

(* Test erasure on simple process *)
Definition erase_test1 : proc data := erase test1.
Check erase_test1.

Definition erase_test2 : proc data := erase test2.
Check erase_test2.

(* Test fuel extraction *)
Eval compute in get_fuel test1.  (* Should be: 1 *)
Eval compute in get_fuel test2.  (* Should be: 2 *)
Eval compute in get_fuel test7.  (* Should be: 4 *)

(* Example: run two-party protocol with AUTOMATIC fuel computation *)
(* The fuel [> ...] is computed from the inferred fuel indices *)
Definition test_procs := [aprocs proto_p0; proto_p1].
Eval compute in [> test_procs].  (* Should be: 4 (= 2 + 2) *)

(* Run with automatic fuel - no manual "100" needed! *)
Definition test_run := run_sprocs test_procs.

(* The erased processes can be used with the interpreter:
   
   Definition run_scalar_product sa sb ra xa xb yb :=
     let procs := [aprocs 
       sp_proc_coserv sa sb ra;
       sp_proc_alice xa;
       sp_proc_bob xb yb
     ] in
     run_sprocs procs.  (* Fuel automatically computed! *)
*)

End test_erasure.

(******************************************************************************)
(** * Summary: Session Type System                                            *)
(******************************************************************************)

(*
This file provides a session type system for SMC protocols with the following
key properties:

1. AUTOMATIC INFERENCE: Both fuel AND session environment are automatically
   inferred by Coq's type unification. Users write programs with _ placeholders.

2. PARAMETERIZED TYPES: Session types (stype) are parameterized by a user-
   defined dtype to avoid combinatorial explosion when adding new data kinds.

3. DUALITY VERIFICATION: The channels_dual function verifies that two parties
   have dual session types, ensuring protocol correctness.

4. ERASURE: Session-typed programs (sproc) can be erased to unindexed proc
   for execution with the interpreter. This simplifies relational semantics.

5. AUTOMATIC FUEL: The inferred fuel index can be extracted using get_fuel or
   sum_fuel, eliminating the need to manually specify interpreter fuel.

Two-layer design:
  - sproc party n env : session-typed with fuel (for type checking, fuel inference)
  - proc              : unindexed process (for interpretation and relational proofs)

Usage:
  1. Define your dtype (e.g., DT_Vec | DT_One for scalar product)
  2. Define your data type (e.g., TX + VX)
  3. Write programs using sproc with _ _ for fuel and senv indices
  4. Verify duality using channels_dual and native_compute
  5. Run with run_sprocs - fuel is automatically computed!

Example:
  Definition my_sender : @sproc my_dtype my_data 0 _ _ :=
    SSend 1 DT_A 42 SFinish.
  
  Lemma sender_receiver_dual : 
    channels_dual (mk_aproc my_sender) (mk_aproc my_receiver) = true.
  Proof. by native_compute. Qed.
  
  (* Run with automatic fuel computation *)
  Definition result := run_sprocs [aprocs my_sender; my_receiver].
*)

