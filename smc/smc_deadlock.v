From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg ring.
From mathcomp Require Import reals finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import smc_interpreter.

(**md**************************************************************************)
(* # Deadlock-Freedom via Acyclic Wait-For Graphs                             *)
(*                                                                            *)
(* General framework for proving deadlock-freedom of SMC protocols.           *)
(* A process is "stuck" if it is non-final and cannot step (Send/Recv with    *)
(* no matching partner). Each stuck process waits for a target party.         *)
(* If the wait-for graph among stuck processes is acyclic, then there are     *)
(* no stuck processes — because every stuck process has an outgoing edge,     *)
(* and a finite acyclic graph where every node has an outgoing edge must      *)
(* be empty (pigeonhole). Therefore: all_final or has_progress.               *)
(*                                                                            *)
(* This is the Coffman circular-wait theorem (1971) specialized to the        *)
(* SMC interpreter, and the graph-theoretic core of the connectivity-graph    *)
(* approach to deadlock-freedom (Jacobs et al., POPL 2022).                   *)
(*                                                                            *)
(* The framework operates on n.-tuple proc (fixed-size tuples) to connect     *)
(* with rstep_disjoint and index_class from smc_interpreter_sound.v.          *)
(* For seq-based code (e.g., dsdp_progress.v), wrap as Tuple size_proof.      *)
(******************************************************************************)

Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

Section deadlock.
Variable data : Type.

Local Open Scope tuple_ext_scope.

(******************************************************************************)
(* Process classification and wait-for relation                                *)
(*                                                                            *)
(* is_final: Finish or Fail (will never step again)                           *)
(* is_ready: step returns true (Init, Ret, or matched Send/Recv)              *)
(* is_stuck: non-final and not ready                                          *)
(*                                                                            *)
(* A stuck process is always Send or Recv (since Init/Ret always fire,        *)
(* and Finish/Fail are final). Its wait_target is the partner index.          *)
(******************************************************************************)

(* Whether process i can step in state ps *)
Definition is_ready n (ps : n.-tuple (proc data)) (i : 'I_n) : bool :=
  (step ps [::] i).2.

(* Whether process i is stuck: non-final and cannot step *)
Definition is_stuck n (ps : n.-tuple (proc data)) (i : 'I_n) : bool :=
  ~~ is_final (ps !_ i) && ~~ is_ready ps i.

(* The party that a process wants to communicate with (if Send/Recv) *)
Definition wait_target (p : proc data) : option nat :=
  match p with
  | Send j _ _ => Some j
  | Recv j _   => Some j
  | _          => None
  end.

(* The wait-for relation: i waits for j if i is stuck and targets j *)
Definition wait_for n (ps : n.-tuple (proc data)) (i j : 'I_n) : bool :=
  is_stuck ps i && (wait_target (ps !_ i) == Some (nat_of_ord j)).

(* Well-formedness: all Send/Recv targets are valid indices *)
Definition wf_targets n (ps : n.-tuple (proc data)) : Prop :=
  forall (i : 'I_n),
    match ps !_ i with
    | Send j _ _ => (j < n)%N
    | Recv j _   => (j < n)%N
    | _          => True
    end.

(* Acyclicity: no cycle in the wait-for graph.
   Defined via path/uniq: every wait-for path visits each node at most once. *)
Definition wait_for_acyclic n (ps : n.-tuple (proc data)) : Prop :=
  forall (s : seq 'I_n) (x : 'I_n),
    path (wait_for ps) x s -> uniq (x :: s).

(* Whether at least one process can step *)
Definition has_progress n (ps : n.-tuple (proc data)) : bool :=
  [exists i : 'I_n, is_ready ps i].

(******************************************************************************)
(* Key lemma: a stuck process is always Send or Recv                          *)
(*                                                                            *)
(* Init and Ret always fire (step returns true), so they are ready.           *)
(* Finish and Fail are final. Therefore stuck implies Send or Recv.           *)
(******************************************************************************)

Lemma stuck_is_send_or_recv n (ps : n.-tuple (proc data)) (i : 'I_n) :
  is_stuck ps i ->
  (exists j x p, ps !_ i = Send j x p) \/
  (exists j f, ps !_ i = Recv j f).
Proof.
rewrite /is_stuck /is_ready /is_final.
rewrite (tnth_nth (default_proc data)) /step.
case: (nth _ _ _) => [d k|j x p|j f|d| |] //=;
  [left; by exists j, x, p | right; by exists j, f].
Qed.

(* A stuck process has a wait target *)
Lemma stuck_has_target n (ps : n.-tuple (proc data)) (i : 'I_n) :
  is_stuck ps i -> exists j, wait_target (ps !_ i) = Some j.
Proof.
move=> Hi; case: (stuck_is_send_or_recv Hi).
- by move=> [j [x [p ->]]]; exists j.
- by move=> [j [f ->]]; exists j.
Qed.

(* Under wf_targets, a stuck process waits for a valid index *)
Lemma stuck_target_valid n (ps : n.-tuple (proc data)) (i : 'I_n) :
  wf_targets ps -> is_stuck ps i ->
  exists j : 'I_n, wait_for ps i j.
Proof.
move=> Hwf Hi.
have [j Hj] := stuck_has_target Hi.
have Hwfi := Hwf i.
have Hjn : (j < n)%N.
  case: (stuck_is_send_or_recv Hi).
  - move=> [j' [x [p Hp]]]; move: Hwfi Hj; rewrite Hp /=.
    by move=> Hlt -[<-].
  - move=> [j' [f Hp]]; move: Hwfi Hj; rewrite Hp /=.
    by move=> Hlt -[<-].
exists (Ordinal Hjn).
rewrite /wait_for Hi /=.
by rewrite Hj /= eqxx.
Qed.

(******************************************************************************)
(* Pigeonhole: a finite total relation must cycle                             *)
(*                                                                            *)
(* If every node in a finite set has an outgoing edge, then any maximal       *)
(* path must revisit a node. Therefore: a finite acyclic graph cannot have    *)
(* the property that every node has an outgoing edge.                         *)
(******************************************************************************)

(* Build a path by following the wait-for relation *)
Lemma follow_path n (ps : n.-tuple (proc data)) (f : 'I_n -> 'I_n) k (x : 'I_n) :
  (forall i, wait_for ps i (f i)) ->
  path (wait_for ps) x (traject f (f x) k).
Proof.
move=> Hf; elim: k x => [|k IHk] x //=.
by rewrite Hf IHk.
Qed.

(* A finite acyclic graph where every node has an outgoing edge is empty *)
Lemma acyclic_no_total n (ps : n.-tuple (proc data)) :
  wait_for_acyclic ps ->
  (forall i : 'I_n, exists j : 'I_n, wait_for ps i j) ->
  n = 0%N.
Proof.
move=> Hacyc Htotal.
case: (posnP n) => // Hn.
(* n > 0, derive contradiction *)
exfalso.
(* Build choice function f : 'I_n -> 'I_n from Htotal *)
have Hchoice : forall i : 'I_n, {j : 'I_n | wait_for ps i j}.
  move=> i; apply: sigW; exact: Htotal i.
pose f := fun i => sval (Hchoice i).
have Hf : forall i, wait_for ps i (f i).
  move=> i; exact: (svalP (Hchoice i)).
(* Build path of length n+1 starting at some node *)
pose i0 := Ordinal Hn.
have Hpath := follow_path n i0 Hf.
have Huniq := Hacyc _ _ Hpath.
(* But i0 :: traject f (f i0) n has size n+1, impossible for uniq on 'I_n *)
have Hsize : size (i0 :: traject f (f i0) n) = n.+1.
  by rewrite /= size_traject.
have Hsub : {subset i0 :: traject f (f i0) n <= enum 'I_n}.
  by move=> x _; rewrite mem_enum.
have := uniq_leq_size Huniq Hsub.
by rewrite Hsize size_enum_ord ltnn.
Qed.

(******************************************************************************)
(* Main theorem: acyclic wait-for implies deadlock-freedom                     *)
(*                                                                            *)
(* Requires an additional "no orphan" hypothesis: stuck processes only wait   *)
(* for non-final processes. Without this, a stuck process could wait for a    *)
(* finished process, and the wait-for graph would terminate without cycling.  *)
(*                                                                            *)
(* Proof by contrapositive:                                                   *)
(* 1. Assume ~~ all_final ps and ~~ has_progress ps                          *)
(* 2. No progress → every non-final process is stuck                         *)
(* 3. No orphan + no progress → every stuck target is also stuck             *)
(* 4. wf_targets → every stuck process has a valid wait-for edge             *)
(* 5. So every I_n has an outgoing edge in the wait-for graph                *)
(* Wait — only STUCK processes have edges, not all of I_n.                   *)
(*                                                                            *)
(* Revised approach: prove no process can be stuck, then derive the result.  *)
(******************************************************************************)

(* Under acyclicity + no orphan + no progress, no process is stuck *)
Lemma acyclic_no_stuck n (ps : n.-tuple (proc data)) :
  wf_targets ps ->
  wait_for_acyclic ps ->
  (forall i : 'I_n, is_stuck ps i ->
     forall j : 'I_n, wait_for ps i j -> ~~ is_final (ps !_ j)) ->
  ~~ has_progress ps ->
  forall i : 'I_n, ~~ is_stuck ps i.
Proof.
move=> Hwf Hacyc Hno_orphan Hno_prog i.
apply/negP => Hi_stuck.
(* Every stuck process has a stuck successor *)
have Hsucc : forall i0 : 'I_n, is_stuck ps i0 ->
    exists j : 'I_n, wait_for ps i0 j /\ is_stuck ps j.
  move=> i0 Hi0.
  have [j Hj] := stuck_target_valid Hwf Hi0.
  exists j; split=> //.
  rewrite /is_stuck (Hno_orphan _ Hi0 _ Hj) /=.
  apply/negP => Hready.
  move/negP: Hno_prog; apply; apply/existsP.
  by exists j.
(* Build a path of length n+1 from i, contradicting pigeonhole *)
(* We build the path inductively, carrying a proof that the last is stuck *)
suffices Hbuild : forall k (x : 'I_n), is_stuck ps x ->
    exists s : seq 'I_n, [/\ size s = k, path (wait_for ps) x s &
      is_stuck ps (last x s)].
  have [s [Hs Hp _]] := Hbuild n.+1 i Hi_stuck.
  have Huniq := Hacyc _ _ Hp.
  have Hsub : {subset i :: s <= enum 'I_n} by move=> x _; rewrite mem_enum.
  move: (uniq_leq_size Huniq Hsub).
  by rewrite /= Hs size_enum_ord ltnNge leqnSn.
elim=> [|k IHk] x Hx.
  by exists [::]; split.
have [j [Hj Hj_stuck]] := Hsucc x Hx.
have [s [Hs Hp Hlast]] := IHk j Hj_stuck.
exists (j :: s); split=> //.
- by rewrite /= Hs.
- by rewrite /= Hj.
Qed.

Theorem acyclic_progress n (ps : n.-tuple (proc data)) :
  wf_targets ps ->
  wait_for_acyclic ps ->
  (forall i : 'I_n, is_stuck ps i ->
     forall j : 'I_n, wait_for ps i j -> ~~ is_final (ps !_ j)) ->
  all_final (tval ps) \/ has_progress ps.
Proof.
move=> Hwf Hacyc Hno_orphan.
case Hprog : (has_progress ps); first by right.
left.
rewrite /all_final; apply/all_tnthP => i.
have Hno_prog : ~~ has_progress ps by rewrite Hprog.
have := acyclic_no_stuck Hwf Hacyc Hno_orphan Hno_prog i.
rewrite /is_stuck negb_and.
case Hfin : (is_final (ps !_ i)) => //=.
move/negPn => Hready.
exfalso; move/negP: Hno_prog; apply; apply/existsP.
by exists i.
Qed.

End deadlock.
