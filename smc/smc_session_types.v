From HB Require Import structures.
From mathcomp Require Import all_boot all_order.
Require Import ssr_ext smc_interpreter graded_resource.

(**md**************************************************************************)
(* # Session Types for SMC Protocols                                          *)
(*                                                                            *)
(* Binary session types for verifying communication protocols in SMC.         *)
(* Session environment is automatically inferred by Coq's unification.        *)
(*                                                                            *)
(* Three layers:                                                              *)
(*   sproc party n env - session-typed process with fuel n and session env    *)
(*                       Coq's unification automatically infers n and env     *)
(*   aproc             - existential wrapper: packs sproc with hidden indices *)
(*                       Enables storing heterogeneous sprocs in lists        *)
(*   proc              - unindexed process (from smc_interpreter.v)           *)
(*                       Used for actual interpretation                       *)
(*                                                                            *)
(* Workflow: sproc --(mk_aproc)--> aproc --(erase_aproc)--> proc              *)
(*   1. Write protocols as sproc with _ _ placeholders (indices auto-inferred)*)
(*   2. Pack into aproc list: [aprocs p1; p2; p3]                             *)
(*   3. Run with run_sprocs: fuel [> aps] computed from inferred indices      *)
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
(** * Session Type Depth                                                      *)
(******************************************************************************)

Section stype_depth_def.

Variable dtype : eqType.

(* Depth of a single session type - counts number of send/recv operations *)
Fixpoint stype_depth (s : stype dtype) : nat :=
  match s with
  | STEnd => 0
  | STSend _ k => (stype_depth k).+1
  | STRecv _ k => (stype_depth k).+1
  end.

(* Depth of session environment - max over specified parties *)
Definition senv_depth (env : senv dtype) (parties : seq nat) : nat :=
  \max_(p <- parties) stype_depth (env p).

(* Basic lemmas about stype_depth *)
Lemma stype_depth_send (d : dtype) (k : stype dtype) :
  stype_depth (STSend d k) = (stype_depth k).+1.
Proof. by []. Qed.

Lemma stype_depth_recv (d : dtype) (k : stype dtype) :
  stype_depth (STRecv d k) = (stype_depth k).+1.
Proof. by []. Qed.

Lemma stype_depth_end : stype_depth (@STEnd dtype) = 0.
Proof. by []. Qed.

(* senv_end has depth 0 for any party set *)
Lemma senv_depth_end (parties : seq nat) :
  senv_depth (@senv_end dtype) parties = 0.
Proof. by rewrite /senv_depth big1. Qed.

(* Helper: F i0 <= bigmax over sequence when i0 is in the sequence *)
Lemma leq_bigmax_seq_simple (F : nat -> nat) (r : seq nat) (i0 : nat) :
  i0 \in r -> F i0 <= \max_(i <- r) F i.
Proof.
elim: r => [|h t IH] //=.
rewrite in_cons big_cons => /orP[/eqP -> | Ht].
  exact: leq_maxl.
apply (leq_trans (IH Ht)).
exact: leq_maxr.
Qed.

(* senv_send increases depth for the target party *)
Lemma senv_depth_send (env : senv dtype) (dst : nat) (d : dtype) (parties : seq nat) :
  dst \in parties ->
  senv_depth (senv_send env dst d) parties >= (stype_depth (env dst)).+1.
Proof.
move=> Hdst.
rewrite /senv_depth.
apply (@leq_trans (stype_depth (senv_send env dst d dst))).
  by rewrite /senv_send eqxx.
exact: (leq_bigmax_seq_simple (fun p => stype_depth (senv_send env dst d p)) Hdst).
Qed.

(* senv_recv increases depth for the source party *)
Lemma senv_depth_recv (env : senv dtype) (src : nat) (d : dtype) (parties : seq nat) :
  src \in parties ->
  senv_depth (senv_recv env src d) parties >= (stype_depth (env src)).+1.
Proof.
move=> Hsrc.
rewrite /senv_depth.
apply (@leq_trans (stype_depth (senv_recv env src d src))).
  by rewrite /senv_recv eqxx.
exact: (leq_bigmax_seq_simple (fun p => stype_depth (senv_recv env src d p)) Hsrc).
Qed.

(* Helper: monotonicity of bigmax over sequences *)
Lemma big_max_mono (parties : seq nat) (F G : nat -> nat) :
  (forall i, i \in parties -> F i <= G i) ->
  \max_(i <- parties) F i <= \max_(i <- parties) G i.
Proof.
move=> Hleq.
apply/bigmax_leqP_seq => i Hi _.
apply: leq_trans (Hleq i Hi) _.
by apply: (leq_bigmax_seq _ Hi).
Qed.

(* senv_send preserves or increases depth (no membership requirement) *)
Lemma senv_depth_senv_send_geq (env : senv dtype) (dst : nat) (dt : dtype) (parties : seq nat) :
  senv_depth env parties <= senv_depth (senv_send env dst dt) parties.
Proof.
rewrite /senv_depth.
apply: big_max_mono => i Hi.
rewrite /senv_send.
case: (i == dst) => /=.
- by rewrite leqnSn.
- by [].
Qed.

(* senv_recv preserves or increases depth (no membership requirement) *)
Lemma senv_depth_senv_recv_geq (env : senv dtype) (src : nat) (dt : dtype) (parties : seq nat) :
  senv_depth env parties <= senv_depth (senv_recv env src dt) parties.
Proof.
rewrite /senv_depth.
apply: big_max_mono => i Hi.
rewrite /senv_recv.
case: (i == src) => /=.
- by rewrite leqnSn.
- by [].
Qed.

End stype_depth_def.

Arguments stype_depth {dtype}.
Arguments senv_depth {dtype}.

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

(* A process with zero fuel erases to Fail.
   Proof: Case analysis on the sproc constructor. Only SFail has fuel 0;
   all other constructors (SFinish, SRet, SInit, SSend, SRecv) have fuel >= 1. *)
Lemma nofuel_proc_fail p : aproc_fuel p = 0 -> erase_aproc p = Fail.
Proof. by case: p => x [y] [e] [||n|n|n|n]. Qed.

(* If total fuel is zero, all processes erase to Fail.
   Proof: By induction on the process list. If the sum is zero, each individual
   fuel must be zero (since fuel is non-negative), so nofuel_proc_fail applies. *)
Lemma nofuel_procs_fail (ps : seq (aproc dtype data)) :
  [> ps] = 0 -> erase_aprocs ps = nseq (size ps) Fail.
Proof.
rewrite /sum_fuel.
elim: ps => // p ps IH /=.
case Hp: (aproc_fuel p) => // /IH ->.
by rewrite nofuel_proc_fail.
Qed.

(* Default annotated process used as fallback value for nth when index exceeds list size *)
Definition aproc_default := @mk_aproc dtype data 0 0 senv_end SFail.

(* Construct a tuple where each element satisfies an index-dependent predicate.
   Given a function f that produces {a | P i a} for each index i, builds a
   tuple [tuple sval (f i) | i < n] with proof that forall i, P i (tnth sa i).
   Proof: Extract values with sval, then use tnth_mktuple to rewrite access,
   and svalP to get the proof component from each sigma type. *)
Definition dependent_mktuple (A : Type) n (P : 'I_n -> A -> Prop)
  (f : forall i, {a | P i a}) : {sa : n.-tuple A | forall i, P i (tnth sa i)}.
exists [tuple sval (f i) | i < n].
abstract (move=> i; rewrite tnth_mktuple; exact: (svalP (f i))).
Defined.

(* Key lemma: after one step, we can reconstruct an annotated process ap' such that:
   1. ap' erases to the resulting process
   2. fuel of ap' + "did step happen" (0 or 1) <= original fuel
   This means: if a step happens (res.2 = 1), fuel strictly decreases;
   if no step happens (res.2 = 0), fuel stays the same.
   Proof: Case analysis on the sproc constructor of the k-th process.
   - SFinish/SRet/SFail: no step possible, return same/default process
   - SInit: always steps, return continuation with fuel n-1, prove (n-1)+1 <= n
   - SSend: check if receiver ready; if matched, return continuation with decreased fuel
   - SRecv: check if sender ready; if matched, apply continuation with decreased fuel *)
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

(* Extended fuel_decreases: also tracks senv_depth non-increasing.
   The senv bound follows from the structure of sproc constructors:
   - SFinish/SRet: env = senv_end, depth = 0
   - SInit: env unchanged
   - SSend matched: env goes from (senv_send env' dst dt) to env', depth non-increasing
   - SRecv matched: env goes from (senv_recv env' src dt) to env', depth non-increasing
   - Blocked cases: env unchanged *)
Lemma fuel_senv_decreases (ps : seq (aproc dtype data)) k tr (parties : seq nat) :
  k < size ps ->
  let res := step (erase_aprocs ps) (nth [::] tr k) k in
  { ap' | erase_aproc ap' = res.1.1 /\
      aproc_fuel ap' + res.2 <= aproc_fuel (nth aproc_default ps k) /\
      senv_depth (aproc_env ap') parties <= senv_depth (aproc_env (nth aproc_default ps k)) parties }.
Proof.
move => Hk /=.
rewrite /step (nth_map aproc_default) //.
move Hnth: (nth _ ps k) => [p [n] [env] sp].
rewrite {2}/aproc_fuel {2}/aproc_env /=.
move/(f_equal erase_aproc): Hnth.
rewrite -(nth_map _ (default_proc _)) // -/(erase_aprocs ps).
rewrite /erase_aproc /aproc_proc /=.
case Hn: n env / sp =>
       [|d|n' env d s|n' env dst dt d s|n' env dst d s|n' env] Hnth /=.
- (* SFinish: env = senv_end, stays senv_end *)
  by exists (mk_aproc (party:=p) SFinish).
- (* SRet: env = senv_end, becomes senv_end (via SFinish) *)
  by exists (mk_aproc (party:=p) SFinish).
- (* SInit: env unchanged *)
  by exists (mk_aproc (party:=p) s); rewrite addn1.
- (* SSend *)
  case Hnth': nth => [||k' p'|||];
    try by exists (mk_aproc (party:=p) (SSend dst dt d s)); rewrite addn0.
  (* Recv case: check if matched *)
  case: ifPn => [/eqP|] k'k.
  + (* Matched: env goes from senv_send env dst dt to env *)
    exists (mk_aproc (party:=p) s).
    split; first by [].
    split; first by rewrite addn1.
    (* senv_depth env <= senv_depth (senv_send env dst dt) *)
    exact: senv_depth_senv_send_geq.
  + (* Not matched: blocked, env unchanged *)
    by exists (mk_aproc (party:=p) (SSend dst dt d s)); rewrite addn0.
- (* SRecv *)
  case Hnth': nth => [|k' d' p'||||];
    try by exists (mk_aproc (party:=p) (SRecv dst d s)); rewrite /= addn0.
  (* Send case: check if matched *)
  case: ifPn => [/eqP|] k'k.
  + (* Matched: env goes from senv_recv env dst dt to env *)
    exists (mk_aproc (party:=p) (s d')).
    split; first by [].
    split; first by rewrite addn1.
    (* senv_depth env <= senv_depth (senv_recv env dst dt) *)
    exact: senv_depth_senv_recv_geq.
  + (* Not matched: blocked, env unchanged *)
    by exists (mk_aproc (party:=p) (SRecv dst d s)); rewrite addn0.
- (* SFail: default process has senv_end *)
  exists aproc_default.
  split; first by [].
  split; first by [].
  by rewrite /aproc_env /aproc_default /= senv_depth_end.
Qed.

(* Termination guarantee: if fuel h >= sum of all process fuels ([> ps]),
   then after interpretation, no process can take another step.
   Every process is stuck - the system has reached a quiescent state.
   Proof: By induction on h.
   - Base (h=0): Total fuel is 0, so all processes are Fail (by nofuel_procs_fail),
     and step on Fail returns false.
   - Inductive (h=h'+1): Either no step happens (already quiescent, done), or
     some process k steps. Use dependent_mktuple with fuel_decreases to construct
     annotated processes aps' for the new state. Since process k stepped, its fuel
     strictly decreased, so total fuel decreased. Apply IH with the reduced bound. *)
Lemma fuel_suffices_nored h (ps : seq (aproc dtype data)) traces res :
  (h >= [> ps])%N ->
  interp h (erase_aprocs ps) traces = res ->
  ~~ has snd [seq step res.1 (nth [::] res.2 i) i | i <- iota 0 (size ps)].
Proof.
elim: h ps traces => [|h IH] ps traces.
  rewrite leqn0 => /eqP /nofuel_procs_fail -> <- /=.
  rewrite has_map -all_predC; apply/allP => i /=.
  by rewrite mem_iota leq0n add0n /step nth_nseq => /= ->.
move=> Hps /=.
set ps' := unzip1 (unzip1 _).
case: ifPn; last first.
  rewrite -!all_predC -!all_map -!map_comp size_map => /allP /= Hc <-.
  apply/allP => /= b /mapP[/= i Hi] ->.
  exact/Hc/map_f.
rewrite has_map => /hasP[k].
rewrite mem_iota size_map leq0n add0n => /= Hk Hck.
set traces' := unzip2 _.
suff : exists aps', erase_aprocs aps' = ps' /\
         \sum_(0 <= i < size ps) aproc_fuel (nth aproc_default aps' i) <= h.
  case=> aps' [Haps' Hh'].
  have Hsz : size ps = size aps'.
    by rewrite -(size_map erase_aproc aps') [map _ _]Haps' !size_map size_iota.
  rewrite Hsz -Haps'; apply: IH.
  by rewrite /sum_fuel sumnE big_map (big_nth aproc_default) -Hsz.
have [aps' Haps'] :=
  dependent_mktuple (fun k : 'I_(size ps) => fuel_decreases traces (ltn_ord k)).
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
rewrite -{3}(map_nth_iota_id aproc_default ps) big_map.
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

(* Interpreter decomposition: running with h1+h2 fuel equals running h1 first,
   then running h2 on the result.
   Proof: By induction on h1.
   - Base (h1=0): trivial, interp 0 is identity
   - Step (h1=h1'+1): if some process steps, apply IH; if no process steps
     (quiescent), the interpreter returns immediately regardless of remaining fuel *)
Lemma interpD h1 h2 (ps : seq (proc data)) traces :
  interp (h1 + h2) ps traces =
  let (ps',traces') := interp h1 ps traces in
  interp h2 ps' traces'.
Proof.
elim: h1 ps traces => // h1 IH ps traces /=.
case: ifPn => Hfin.
  by rewrite IH.
case: h2 {IH} => //= h2.
by rewrite (negbTE Hfin).
Qed.

(* The number of processes is preserved by interpretation.
   Proof: By induction on fuel h. The step function maps over processes,
   preserving the list size. *)
Lemma size_interp_procs h (ps : seq (proc data)) tr :
  size (interp h ps tr).1 = size ps.
Proof.
elim: h ps tr => // h IH ps tr /=.
by case: ifP => Hfin //; rewrite IH !size_map size_iota.
Qed.

(* If you have more fuel h than needed ([> ps] = sum of all process fuels),
   the extra fuel doesn't matter. The result is the same as running with
   exactly [> ps] fuel.
   Proof: Split h = [>ps] + d where d is extra fuel. Use interpD to decompose
   into: run [>ps] fuel first, then run d on result. Apply fuel_suffices_nored
   to show the intermediate result is quiescent (no more steps possible).
   Since no process can step, the interpreter's "has snd" check fails,
   and it returns immediately without using the extra fuel d. *)
Lemma fuel_suffices h (ps : seq (aproc dtype data)) traces :
  (h >= [> ps])%N ->
  interp h (erase_aprocs ps) traces = interp [> ps] (erase_aprocs ps) traces.
Proof.
move=> Hh.
have -> : h = [>ps] + (h - [> ps]).
  rewrite -maxnE; exact/esym/maxn_idPr.
set d := (h - _)%N; clearbody d.
rewrite interpD.
move Hint: (interp [>ps] _ _) => res.
have /fuel_suffices_nored := Hint.
move/(_ (leqnn _)).
case Hres: res => [ps' traces'] /=.
have := size_interp_procs [>ps] (erase_aprocs ps) traces.
rewrite Hint Hres /= size_map => <- Hfin.
case: d => // d /=.
by rewrite (negbTE Hfin).
Qed.

(******************************************************************************)
(** * Session Environment Convergence                                         *)
(******************************************************************************)

(* This section proves that for co-dual session-typed processes, the session
   environment depth (senv_depth) converges to 0 after running with sufficient
   fuel. This is the senv analogue of fuel_suffices.
   
   Key results:
   - senv_bounded: senv_depth is non-increasing through interpretation
   - co_dual_invariant: property that fuel=0 implies senv=0 (assumed for co-dual)
   - co_dual_preserved: co_dual_invariant is preserved through interpretation
   - senv_converges: for co-dual processes, senv reaches 0 when fuel exhausted *)

Variable parties : seq nat.

(* Maximum session environment depth across all annotated processes *)
Definition aprocs_senv_depth (ps : seq (aproc dtype data)) : nat :=
  \max_(ap <- ps) senv_depth (aproc_env ap) parties.

(* Co-dual invariant: fuel exhaustion implies session completion.
   
   For well-typed co-dual processes, when total fuel reaches 0, all
   communications have completed and all sessions are at STEnd (depth 0).
   This is a semantic property verified separately by type checking. *)
Definition co_dual_invariant (ps : seq (aproc dtype data)) : Prop :=
  [> ps] = 0 -> aprocs_senv_depth ps = 0.

(* senv_bounded: Session environment depth is bounded through interpretation.
   
   After running with sufficient fuel h >= [>ps], we can reconstruct aprocs
   where senv_depth is bounded by the initial value. This uses
   fuel_senv_decreases to track both fuel and senv through each step. *)
Lemma senv_bounded h (ps : seq (aproc dtype data)) traces :
  (h >= [> ps])%N ->
  exists aps' : seq (aproc dtype data),
    size aps' = size ps /\
    erase_aprocs aps' = (interp h (erase_aprocs ps) traces).1 /\
    aprocs_senv_depth aps' <= aprocs_senv_depth ps.
Proof.
elim: h ps traces => [|h IH] ps traces.
  (* Base case: h = 0, interp 0 is identity *)
  rewrite leqn0 => /eqP _.
  exists ps.
  split; first by [].
  split; first by [].
  by [].
(* Inductive case: h = h'.+1 *)
move=> Hps /=.
set ps' := unzip1 (unzip1 _).
case: ifPn; last first.
  (* No step happened - already quiescent *)
  rewrite -all_predC => Hall.
  exists ps.
  split; first by [].
  split; first by [].  (* erase_aprocs ps = (erase_aprocs ps, traces).1 *)
  by [].              (* aprocs_senv_depth ps <= aprocs_senv_depth ps *)
(* Some process stepped *)
rewrite has_map => /hasP[k].
rewrite mem_iota size_map leq0n add0n => /= Hk Hck.
set traces' := unzip2 _.
(* Use suff pattern from fuel_suffices_nored to avoid dependent tuple issues *)
suff : exists aps', erase_aprocs aps' = ps' /\
         \sum_(0 <= i < size ps) aproc_fuel (nth aproc_default aps' i) <= h /\
         aprocs_senv_depth aps' <= aprocs_senv_depth ps.
  case=> aps' [Herase [Hfuel' Hsenv']].
  have Hsz : size ps = size aps'.
    by rewrite -(size_map erase_aproc aps') [map _ _]Herase !size_map size_iota.
  have Hfuel_conv : [> aps'] <= h.
    by rewrite /sum_fuel sumnE big_map (big_nth aproc_default) -Hsz.
  have [aps'' [Hsz'' [Herase'' Hsenv'']]] := IH aps' traces' Hfuel_conv.
  exists aps''.
  split; first by rewrite Hsz'' Hsz.
  split.
    by rewrite Herase'' Herase.
  by apply: leq_trans Hsenv'' Hsenv'.
(* Now prove the suff: construct aps' using fuel_senv_decreases *)
have [aps' Haps'] :=
  dependent_mktuple (fun k : 'I_(size ps) => 
    fuel_senv_decreases traces parties (ltn_ord k)).
exists aps'.
have Hsz: size aps' = size ps by rewrite size_tuple.
split.
  (* erase_aprocs aps' = ps' *)
  apply: (@eq_from_nth _ Fail).
    by rewrite !size_map size_tuple size_iota.
  move=> i; rewrite !size_map Hsz => Hi.
  rewrite (nth_map aproc_default) ?Hsz //.
  rewrite (_ : i = Ordinal Hi) // -tnth_nth.
  have [Heq _] := Haps' (Ordinal Hi).
  rewrite Heq -[ps']map_comp -map_comp.
  by rewrite (nth_map 0) ?size_iota ?size_map // nth_iota.
split.
  (* \sum_(0 <= i < size ps) aproc_fuel (nth aproc_default aps' i) <= h *)
  rewrite -ltnS (leq_trans _ Hps) // ?(ltnW Hk) // /sum_fuel sumnE big_map.
  rewrite -{3}(map_nth_iota_id aproc_default ps) big_map.
  rewrite -{3}(subn0 (size ps)) -/(index_iota _ _) -subn_gt0 -sumnB.
    rewrite lt0n sum_nat_seq_neq0.
    apply/hasP; exists k; first by rewrite mem_iota leq0n add0n subn0.
    rewrite /= -lt0n subn_gt0 -addn1 (_ : 1 = true) // -Hck.
    have [_ []] := Haps' (Ordinal Hk).
    by rewrite (tnth_nth aproc_default).
  move=> i _.
  case/boolP: (i < size aps') => Hi.
    rewrite Hsz in Hi.
    have [_ [Hfuel _]] := Haps' (Ordinal Hi).
    move: Hfuel; rewrite (tnth_nth aproc_default) /=.
    exact/leq_trans/leq_addr.
  by rewrite nth_default // leqNgt.
(* aprocs_senv_depth aps' <= aprocs_senv_depth ps *)
rewrite /aprocs_senv_depth.
rewrite (big_tuple 0 maxn aps' xpredT (fun ap => senv_depth (aproc_env ap) parties)).
rewrite (big_nth aproc_default) /=.
apply/bigmax_leqP => i _.
have [_ [_ Hsenv_i]] := Haps' i.
apply: leq_trans Hsenv_i _.
rewrite big_mkord.
have H := @leq_bigmax 'I_(size ps) 
  (fun j : 'I_(size ps) => senv_depth (aproc_env (nth aproc_default ps j)) parties) i.
exact H.
Qed.

(* Preservation hypothesis: co_dual_invariant is preserved through interpretation.
   
   This captures that for co-dual processes, the fuel-senv relationship is
   maintained through each step: when total fuel reaches 0, all sessions
   have completed (senv_depth = 0).
   
   This is a semantic property of co-dual session types that should be proven
   separately for specific co-dual systems. *)
Hypothesis Hcd_preserved : forall h' ps' traces',
  co_dual_invariant ps' ->
  forall aps'', erase_aprocs aps'' = (interp h' (erase_aprocs ps') traces').1 ->
  co_dual_invariant aps''.

(* co_dual_preserved: The co_dual_invariant is preserved through interpretation.
   
   Given: ps satisfies co_dual_invariant (fuel=0 -> senv=0)
   After: aps' (result of interpretation) also satisfies co_dual_invariant
   
   Uses senv_bounded for the senv bound, Hcd_preserved for invariant preservation. *)
Lemma co_dual_preserved h (ps : seq (aproc dtype data)) traces :
  (h >= [> ps])%N ->
  co_dual_invariant ps ->
  exists aps' : seq (aproc dtype data),
    size aps' = size ps /\
    erase_aprocs aps' = (interp h (erase_aprocs ps) traces).1 /\
    aprocs_senv_depth aps' <= aprocs_senv_depth ps /\
    co_dual_invariant aps'.
Proof.
move=> Hh Hcd.
have [aps' [Hsz [Herase Hsenv]]] := @senv_bounded h ps traces Hh.
exists aps'.
split; first exact: Hsz.
split; first exact: Herase.
split; first exact: Hsenv.
exact (@Hcd_preserved h ps traces Hcd aps' Herase).
Qed.

(* senv_converges: For co-dual processes, senv_depth converges to 0.
   
   This is the main theorem showing that for co-dual session-typed processes,
   after running with sufficient fuel, if total fuel reaches 0, then
   aprocs_senv_depth = 0 (all sessions have completed).
   
   This is the senv analogue of fuel_suffices: while fuel_suffices shows
   extra fuel doesn't change the result, senv_converges shows that for
   co-dual processes, the session environment converges to completion. *)
Lemma senv_converges h (ps : seq (aproc dtype data)) traces :
  (h >= [> ps])%N ->
  co_dual_invariant ps ->
  exists aps' : seq (aproc dtype data),
    size aps' = size ps /\
    erase_aprocs aps' = (interp h (erase_aprocs ps) traces).1 /\
    ([> aps'] = 0 -> aprocs_senv_depth aps' = 0).
Proof.
move=> Hh Hcd.
have [aps' [Hsz [Herase [Hsenv Hcd']]]] := @co_dual_preserved h ps traces Hh Hcd.
exists aps'.
split; first exact: Hsz.
split; first exact: Herase.
exact: Hcd'.
Qed.

(* For future, if we have typed interpreter, one for each resource. *)

(******************************************************************************)
(** * isDecomposableInterp Instance                                           *)
(******************************************************************************)

(* State type for interpreter: processes paired with traces *)
Definition interp_state : Type := seq (proc data) * seq (seq data).

(* Wrapper to match isDecomposableInterp signature: nat -> S -> S *)
Definition interp_on_state (h : nat) (s : interp_state) : interp_state :=
  let (ps, traces) := s in interp h ps traces.

(* run 0 is identity *)
Lemma run0_state : forall s : interp_state, interp_on_state 0 s = s.
Proof. by case. Qed.

(* runD in the form needed for isDecomposableInterp *)
Lemma runD_state : forall n m (s : interp_state),
  interp_on_state (n + m) s = interp_on_state m (interp_on_state n s).
Proof.
move=> n m [ps traces] /=.
rewrite interpD.
by case: (interp n ps traces).
Qed.

(* HB instance of isDecomposableInterp for the interpreter state *)
HB.instance Definition _ := @isDecomposableInterp.Build
  interp_state interp_on_state runD_state run0_state.

End erasure.

Arguments erase {data dtype party n env}.
Arguments erase_aproc {data dtype}.
Arguments erase_aprocs {data dtype}.

(******************************************************************************)
(** * isNatGraded Instance for Fuel                                           *)
(******************************************************************************)

(* Fuel family: trivially indexed by nat.
   This represents fuel as a type family where all levels have the same type (unit).
   The purpose is to enable using the generic termination lemmas from graded_resource.v
   with the fuel parameter. *)
Definition fuel_family (n : nat) : Type := unit.

(* HB instance: fuel_family is a NatGraded type family.
   - base: the terminal value at level 0 is tt (the unit value)
   - down: stepping down from any level just returns tt *)
HB.instance Definition _ := isNatGraded.Build fuel_family
  tt                    (* base : fuel_family 0 *)
  (fun _ _ => tt).      (* down : forall n, fuel_family n.+1 -> fuel_family n *)

(******************************************************************************)
(** * isNatGraded Instance for Session Environment                            *)
(******************************************************************************)

(* Session environment family: indexed by depth with exact equality.
   Unlike fuel_family (trivially unit), this carries meaningful structure:
   level n contains exactly the session environments with depth n.
   
   - base : senv_family 0
     The terminal session environment where all sessions have ended.
     This is senv_end, which maps every party to STEnd.
   
   - down : senv_family n.+1 -> senv_family n
     The step-down operation corresponds to "one communication step occurred".
     It pops the outer Send/Recv constructor from each session type.
   
   Example: Consider a 2-party protocol where party 0 sends twice to party 1.
   
     env at depth 2:  party 1 -> STSend D1 (STSend D2 STEnd)
                      (other parties -> STEnd)
     
     After senv_down (one send occurred):
     env at depth 1:  party 1 -> STSend D2 STEnd
     
     After another senv_down:
     env at depth 0:  party 1 -> STEnd  (= senv_end, the base)
   
   This grading enables generic termination proofs: each communication step
   strictly decreases the session environment depth until reaching base. *)

Section senv_graded.

Variable dtype : eqType.
Variable parties : seq nat.

(* Step down a single session type - pop outer Send/Recv constructor *)
Definition stype_down (s : stype dtype) : stype dtype :=
  match s with
  | STSend _ k => k
  | STRecv _ k => k
  | STEnd => STEnd
  end.

(* stype_down reduces depth by 1, saturating at 0 *)
Lemma stype_depth_down (s : stype dtype) :
  stype_depth (stype_down s) = (stype_depth s).-1.
Proof. by case: s. Qed.

(* Step down an entire session environment pointwise *)
Definition senv_down (env : senv dtype) : senv dtype :=
  fun p => stype_down (env p).

(* Predecessor distributes over max *)
Lemma predn_max a b : (maxn a b).-1 = maxn a.-1 b.-1.
Proof.
case: a => [|a]; case: b => [|b] //=.
  by rewrite max0n.
by rewrite !maxnSS.
Qed.

(* Helper lemmas for bigmax without predicates *)
Lemma bigmax_cons h t (F : nat -> nat) :
  \max_(i <- h :: t) F i = maxn (F h) (\max_(i <- t) F i).
Proof. by rewrite big_cons. Qed.

Lemma bigmax_nil (F : nat -> nat) : \max_(i <- [::]) F i = 0.
Proof. by rewrite big_nil. Qed.

(* Key lemma: max of (f - 1) = (max f) - 1 for predecessor *)
Lemma bigmax_pred (r : seq nat) (F : nat -> nat) :
  (\max_(i <- r) (F i).-1) = (\max_(i <- r) F i).-1.
Proof.
elim: r => [|h t IH].
  by rewrite !bigmax_nil.
by rewrite !bigmax_cons IH predn_max.
Qed.

(* senv_down reduces environment depth by 1 *)
Lemma senv_depth_down (env : senv dtype) :
  senv_depth (senv_down env) parties = (senv_depth env parties).-1.
Proof.
rewrite /senv_depth /senv_down.
under eq_bigr do rewrite stype_depth_down.
exact: bigmax_pred.
Qed.

(* Type family: senvs with depth exactly n *)
Definition senv_family (n : nat) : Type :=
  { env : senv dtype | senv_depth env parties = n }.

(* Base case: senv_end has depth exactly 0 *)
Definition senv_family_base : senv_family 0.
exists senv_end.
exact: senv_depth_end.
Defined.

(* Step down: apply senv_down, use depth lemma *)
Definition senv_family_down (n : nat) (e : senv_family n.+1) : senv_family n.
exists (senv_down (sval e)).
abstract (rewrite senv_depth_down (svalP e); exact: succnK).
Defined.

(* HB instance: senv_family is a NatGraded type family *)
HB.instance Definition _ := isNatGraded.Build senv_family
  senv_family_base
  senv_family_down.

End senv_graded.

Arguments stype_down {dtype}.
Arguments senv_down {dtype}.
Arguments senv_family {dtype}.

(******************************************************************************)
(** * isStepDecreasing Instance for aproc (Fuel)                              *)
(******************************************************************************)

(* Step function that handles all operations including Send/Recv.
   Checks for matching communication partners in the process list context.
   This mirrors the interpreter's step function behavior. *)

Section aproc_step_decreasing.

Variable dtype : eqType.
Variable data : Type.

(* Context for stepping with full process list *)
Record aproc_ctx := {
  ctx_procs : seq (proc data) ;  (* all erased processes *)
  ctx_trace : seq data ;          (* trace for this process *)
  ctx_idx : nat ;                 (* index of this process *)
}.

(* Full step function: steps an aproc in context of all processes.
   - SFinish/SFail: no progress, return same
   - SRet: step to Finish, progress=1
   - SInit: step to next, progress=1
   - SSend: check if receiver is ready (Recv from us), if so progress=1
   - SRecv: check if sender is ready (Send to us), if so apply continuation *)
Definition aproc_step (ap : aproc dtype data) (ctx : aproc_ctx)
    : aproc dtype data * nat.
Proof.
case: ap => [party [n [env sp]]].
case: sp.
- exact (mk_aproc (party:=party) SFinish, 0).
- move=> d; exact (mk_aproc (party:=party) SFinish, 1).
- move=> n' env' d next; exact (mk_aproc (party:=party) next, 1).
- move=> n' env' dst dt d next.
  case Hrecv: (nth (default_proc data) (ctx_procs ctx) dst) =>
      [d' p'|dst' d' p'|frm f|d'| |].
  + exact (mk_aproc (party:=party) (SSend dst dt d next), 0).
  + exact (mk_aproc (party:=party) (SSend dst dt d next), 0).
  + case: (frm == ctx_idx ctx).
    * exact (mk_aproc (party:=party) next, 1).
    * exact (mk_aproc (party:=party) (SSend dst dt d next), 0).
  + exact (mk_aproc (party:=party) (SSend dst dt d next), 0).
  + exact (mk_aproc (party:=party) (SSend dst dt d next), 0).
  + exact (mk_aproc (party:=party) (SSend dst dt d next), 0).
- move=> n' env' src dt cont.
  case Hsend: (nth (default_proc data) (ctx_procs ctx) src) =>
      [d' p'|dst' v p'|frm f|d'| |].
  + exact (mk_aproc (party:=party) (SRecv src dt cont), 0).
  + case: (dst' == ctx_idx ctx).
    * exact (mk_aproc (party:=party) (cont v), 1).
    * exact (mk_aproc (party:=party) (SRecv src dt cont), 0).
  + exact (mk_aproc (party:=party) (SRecv src dt cont), 0).
  + exact (mk_aproc (party:=party) (SRecv src dt cont), 0).
  + exact (mk_aproc (party:=party) (SRecv src dt cont), 0).
  + exact (mk_aproc (party:=party) (SRecv src dt cont), 0).
- move=> n' env'; exact (@mk_aproc _ _ party n' env' SFail, 0).
Defined.

(* Proof that full step decreases fuel *)
Lemma aproc_step_decreases (ap : aproc dtype data) (ctx : aproc_ctx) :
  aproc_fuel (aproc_step ap ctx).1 + (aproc_step ap ctx).2 <= aproc_fuel ap.
Proof.
case: ap => [party [n [env sp]]].
case: sp => /=.
- by [].
- by move=> d.
- move=> n' env' d next; by rewrite /aproc_fuel /= addn1.
- move=> n' env' dst dt d next.
  rewrite /aproc_step /=.
  case: (nth (default_proc data) (ctx_procs ctx) dst) =>
      [d' p'|dst' d' p'|frm f|d'| |] /=.
  + by rewrite /aproc_fuel /= addn0.
  + by rewrite /aproc_fuel /= addn0.
  + case: (frm == ctx_idx ctx) => /=.
    * by rewrite /aproc_fuel /= addn1.
    * by rewrite /aproc_fuel /= addn0.
  + by rewrite /aproc_fuel /= addn0.
  + by rewrite /aproc_fuel /= addn0.
  + by rewrite /aproc_fuel /= addn0.
- move=> n' env' src dt cont.
  rewrite /aproc_step /=.
  case: (nth (default_proc data) (ctx_procs ctx) src) =>
      [d' p'|dst' v p'|frm f|d'| |] /=.
  + by rewrite /aproc_fuel /= addn0.
  + case: (dst' == ctx_idx ctx) => /=.
    * by rewrite /aproc_fuel /= addn1.
    * by rewrite /aproc_fuel /= addn0.
  + by rewrite /aproc_fuel /= addn0.
  + by rewrite /aproc_fuel /= addn0.
  + by rewrite /aproc_fuel /= addn0.
  + by rewrite /aproc_fuel /= addn0.
- move=> n' env'; by rewrite /aproc_fuel /= addn0.
Qed.

End aproc_step_decreasing.

Arguments aproc_ctx {data}.
Arguments aproc_step {dtype data}.
Arguments aproc_step_decreases {dtype data}.

(******************************************************************************)
(** * Session Env Depth Decreasing                                            *)
(******************************************************************************)

(* This section proves that stepping an aproc decreases (or preserves) the
   session environment depth. Unlike fuel which always decreases by exactly 1
   when progress is made, senv depth decrease depends on which party is involved
   in the communication.
   
   Key insight from sproc constructors:
   - SSend dst dt d next : sproc party n.+1 (senv_send env dst dt)
     When SSend succeeds, env goes from (senv_send env dst dt) to env.
     At party dst: STSend dt (env dst) -> env dst, depth decreases by 1.
   
   - SRecv src dt cont : sproc party n.+1 (senv_recv env src dt)
     When SRecv succeeds, env goes from (senv_recv env src dt) to env.
     At party src: STRecv dt (env src) -> env src, depth decreases by 1.
   
   The overall senv_depth (max over parties) decreases if the communicating
   party (dst for SSend, src for SRecv) is in the parties set.
   
   Connection to sum_level_decreases:
   This lemma provides the step_decreases hypothesis for senv-indexed processes,
   enabling derivation of senv_suffices analogous to fuel_suffices. *)

Section senv_step_decreasing.

Variable dtype : eqType.
Variable data : Type.
Variable parties : seq nat.

(* Session env depth never increases after a step.
   
   This lemma shows that stepping a process can only decrease or preserve
   the session environment depth. It's sufficient for showing that senv
   termination follows from fuel termination, since:
   1. Fuel bounds the number of steps
   2. Each step preserves or decreases senv depth
   3. Therefore, after fuel steps, senv depth is bounded
   
   Note: Unlike fuel which strictly decreases by exactly 1 on progress,
   senv_depth decrease depends on which party is involved. The depth only
   strictly decreases when the communicating party (dst for SSend, src for 
   SRecv) has the maximum depth. We use the simpler non-increasing form
   since it's sufficient for our purposes and avoids complex party tracking. *)
Lemma senv_step_nonincreasing (ap : aproc dtype data) (ctx : aproc_ctx) :
  senv_depth (aproc_env (aproc_step ap ctx).1) parties <= senv_depth (aproc_env ap) parties.
Proof.
case: ap => [party [n [env sp]]].
case: sp => /=.
- (* SFinish *) by [].
- (* SRet *) move=> d.
  rewrite /senv_depth big1 //.
- (* SInit *) move=> n' env' d next; by [].
- (* SSend *) move=> n' env' dst dt d next.
  rewrite /aproc_step /=.
  (* When blocked: output env = input env (same), use reflexivity
     When matched: output env = env' <= senv_send env' = input env *)
  case: (nth (default_proc data) (ctx_procs ctx) dst) =>
      [d' p'|dst' d' p'|frm f|d'| |] /=.
  + by [].  (* Init: blocked, same env *)
  + by [].  (* Send: blocked, same env *)
  + case: (frm == ctx_idx ctx) => /=.
    * exact: senv_depth_senv_send_geq.  (* Recv matched: env' <= senv_send env' *)
    * by [].  (* Recv not matched: blocked, same env *)
  + by [].  (* Ret: blocked, same env *)
  + by [].  (* Finish: blocked, same env *)
  + by [].  (* Fail: blocked, same env *)
- (* SRecv *) move=> n' env' src dt cont.
  rewrite /aproc_step /=.
  case: (nth (default_proc data) (ctx_procs ctx) src) =>
      [d' p'|dst' v p'|frm f|d'| |] /=.
  + by [].  (* Init: blocked, same env *)
  + case: (dst' == ctx_idx ctx) => /=.
    * exact: senv_depth_senv_recv_geq.  (* Send matched: env' <= senv_recv env' *)
    * by [].  (* Send not matched: blocked, same env *)
  + by [].  (* Recv: blocked, same env *)
  + by [].  (* Ret: blocked, same env *)
  + by [].  (* Finish: blocked, same env *)
  + by [].  (* Fail: blocked, same env *)
- (* SFail *) move=> n' env'; by [].
Qed.

End senv_step_decreasing.

Arguments senv_step_nonincreasing {dtype data} parties.

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

(*
For how `dependent_mktuple` works:

This is a dependent tuple construction that builds a tuple where each element satisfies an index-dependent predicate. Let me break down how the proof works:

Type Signature

Definition dependent_mktuple (A : Type) n (P : 'I_n -> A -> Prop)
  (f : forall i, {a | P i a}) : {sa : n.-tuple A | forall i, P i (tnth sa i)}.
Input f: For each index i : 'I_n, provides a dependent pair {a | P i a} — a value a together with a proof that P i a holds
Output: A tuple sa with a proof that forall i, P i (tnth sa i) — every element at index i satisfies P i
The Construction

exists [tuple sval (f i) | i < n].
This constructs the witness tuple using:

[tuple ... | i < n] — MathComp's tuple comprehension syntax
sval (f i) — extracts the value part from the sigma type {a | P i a} (discarding the proof)
The Proof Obligation

abstract (move=> i; rewrite tnth_mktuple; exact: (svalP (f i))).
After exists, we must prove forall i, P i (tnth [tuple sval (f i) | i < n] i):

move=> i — introduce the index i
rewrite tnth_mktuple — applies the lemma that tnth [tuple E i | i < n] j = E j, so the goal becomes P i (sval (f i))
exact: (svalP (f i)) — svalP extracts the proof component from a sigma type: if x : {a | P a}, then svalP x : P (sval x). Here it gives exactly P i (sval (f i))
The abstract Tactic
The abstract wrapper makes the proof term opaque, which:

Prevents the proof from being unfolded during computation
Keeps the definition clean when using Defined (which makes the term transparent for computation)
This is useful because you want the value (the tuple) to compute, but the proof doesn't need to.
*)


(*
Temp note:

Now I can explain how the proof of fuel_suffices_nored works. This is a complex induction proof showing that when we have enough fuel, the interpreter reaches a state where no process can make a reduction step.

Statement

Lemma fuel_suffices_nored h (ps : seq (aproc dtype data)) traces res :
  (h >= [> ps])%N ->
  interp h (erase_aprocs ps) traces = res ->
  ~~ has snd [seq step res.1 (nth [::] res.2 i) i | i <- iota 0 (size ps)].
Meaning: If fuel h is at least the sum of all process fuels ([> ps]), then after interpretation, no process can take another step (the snd of each step is the "did something happen" boolean).

Proof Structure
Base Case (h = 0)

elim: h ps traces => [|h IH] ps traces.
  rewrite leqn0 => /eqP /nofuel_procs_fail -> <- /=.
  rewrite has_map -all_predC; apply/allP => i /=.
  rewrite mem_iota add0n => /andP[_ Hi].
  by rewrite /step /= !nth_nseq // Hi.
leqn0 => /eqP — from h >= [> ps] with h = 0, deduce [> ps] = 0
/nofuel_procs_fail -> — if total fuel is 0, all processes are Fail
nth_nseq — in a constant sequence of Fail, every step returns (Fail, _, false), so no reduction happens
Inductive Case (h = h.+1)

move=> Hps /=.
set ps' := unzip1 (unzip1 _).
have hles tr :=
  dependent_mktuple (fun k : 'I_(size ps) => fuel_decreases tr (ltn_ord k)).
case: ifPn; last first.
The proof uses dependent_mktuple with fuel_decreases to construct annotated processes for the next state.

Subcase: No step happened (ifPn; last first)

  rewrite -!all_predC -!all_map -!map_comp size_map => /allP /= Hc <-.
  apply/allP => /= b /mapP[/= i Hi] ->.
  exact/Hc/map_f.
If the interpreter's has snd check fails (no process stepped), we're already done — just propagate that fact.

Subcase: Some step happened

rewrite has_map => /hasP[k].
rewrite mem_iota size_map add0n => /andP[_ Hk] /= Hck.
Some process k took a step. The proof must show the IH applies to the new state.

Key obligation (lines 574-582):


suff : exists aps', erase_aprocs aps' = ps' /\
         \sum_(0 <= i < size ps) aproc_fuel (nth aproc_default aps' i) <= h.
We need annotated processes aps' for the new state such that their total fuel is ≤ h.

Constructing aps' (line 583):


have [aps' Haps'] := hles traces.
Uses dependent_mktuple with fuel_decreases — for each index, fuel_decreases gives a new annotated process whose fuel decreased appropriately after a step.

Proving the fuel bound (lines 593-607):

The key insight is that fuel_decreases guarantees:


aproc_fuel ap' + res.2 <= aproc_fuel (nth aproc_default ps k)
Since process k actually stepped (Hck says res.2 = true = 1), its fuel strictly decreased. The proof uses:

sumnB to express the fuel difference as a sum
sum_nat_seq_neq0 to show strict decrease (at least 1 unit of fuel consumed)
Apply IH with the reduced fuel bound
Summary
The proof works by strong induction on fuel h:

Base: Zero fuel means all processes are Fail (can't step)
Inductive: Either no step happens (done), or some step happens, and fuel_decreases ensures the total fuel strictly decreases, allowing the IH to apply

*)

(*
For how `fuel_decreases` works:

Statement

Lemma fuel_decreases (ps : seq (aproc dtype data)) k tr :
  k < size ps ->
  let res := step (erase_aprocs ps) (nth [::] tr k) k in
  { ap' | erase_aproc ap' = res.1.1 /\
      aproc_fuel ap' + res.2 <= aproc_fuel (nth aproc_default ps k) }.
Meaning: For any process at index k, after taking a step, we can construct a new annotated process ap' such that:

erase_aproc ap' = res.1.1 — the new annotated process erases to the resulting process
aproc_fuel ap' + res.2 <= aproc_fuel (old process) — the fuel of ap' plus the "step happened" flag (0 or 1) is at most the original fuel
Key insight: If a step happens (res.2 = 1), the fuel strictly decreases. If no step happens (res.2 = 0), fuel stays the same.

Data Structures

(* aproc packs a session-typed process with its fuel index *)
Definition aproc : Type := 
  { party : nat & { n : nat & { env : senv dtype & @sproc dtype data party n env }}}.

(* sproc has fuel baked into its type - the 'n' index *)
Inductive sproc (party : nat) : nat -> senv dtype -> Type :=
  | SFinish : sproc party 1 senv_end           (* fuel = 1 *)
  | SRet : data -> sproc party 2 senv_end      (* fuel = 2 *)
  | SInit : ... sproc party n env -> sproc party n.+1 env    (* fuel + 1 *)
  | SSend : ... sproc party n env -> sproc party n.+1 (...)  (* fuel + 1 *)
  | SRecv : ... -> sproc party n.+1 (...)                     (* fuel + 1 *)
  | SFail : forall n env, sproc party n env                   (* any fuel *)
Proof Walkthrough
Setup (lines 527-535)

move => Hk /=.
rewrite /step (nth_map aproc_default) //.
move Hnth: (nth _ ps k) => [p [n] [env] sp].
Introduce bound Hk : k < size ps
Unfold step and rewrite nth through erase_aprocs (a map)
Destructure the k-th annotated process as [p [n] [env] sp] where:
p = party
n = fuel index
env = session environment
sp : sproc p n env = the actual session-typed process
Case Analysis (lines 534-550)

case Hn: n env / sp =>
       [|d|n' env d s|n' env dst dt d s|n' env dst d s|n' env] Hnth /=.
Case split on the structure of sp:

Case	Constructor	Result	Fuel Accounting
SFinish	SFinish	No step possible	exists (mk_aproc SFinish) — fuel stays same
SRet d	SRet d	Returns, becomes Finish	exists (mk_aproc SFinish) — fuel stays same
SInit d s	Init d (erase s)	Always steps	exists (mk_aproc s); rewrite addn1 — fuel decreases by 1
SSend dst dt d s	Send dst d (erase s)	Steps if receiver ready	See below
SRecv src dt f	Recv src (...)	Steps if sender ready	See below
SFail	Fail	No step	exists aproc_default
Send Case (lines 539-543)

case Hnth': nth => [||k' p'|||];
    try by exists (mk_aproc (party:=p) (SSend dst dt d s)); rewrite addn0.
  case: ifPn => [/eqP|] k'k.
    by exists (mk_aproc (party:=p) s); rewrite addn1.
  by exists (mk_aproc (party:=p) (SSend dst dt d s)); rewrite addn0.
Look at what the destination process is doing
If destination is Recv k' f and k' == k (matching), step happens → return continuation s, fuel decreases by 1 (addn1)
Otherwise, no step → return same SSend, fuel unchanged (addn0)
Recv Case (lines 544-549)

case Hnth': nth => [|k' d' p'||||];
    try by exists (mk_aproc (party:=p) (SRecv dst d s)); rewrite /= (addn0 (aproc_fuel _)).
  case: ifPn => [/eqP|] k'k.
    by exists (mk_aproc (party:=p) (s d')); rewrite addn1.
  by exists (mk_aproc (party:=p) (SRecv dst d s)); rewrite addn0.
Look at what the source process is doing
If source is Send k' v next and k' == k (matching), step happens → return s d' (applied continuation), fuel decreases by 1
Otherwise, no step → return same SRecv, fuel unchanged
Summary
The lemma works by:

Type-level fuel tracking: Each sproc constructor has fuel baked into its type index n
Case analysis: For each process form, determine if a step can happen
Fuel accounting:
Step happens → return the continuation with fuel n-1, prove (n-1) + 1 ≤ n
No step → return same process with same fuel n, prove n + 0 ≤ n
This is the key invariant that makes fuel_suffices_nored work: the total fuel across all processes is a strict upper bound on the number of reduction steps.
*)