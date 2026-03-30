From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg ring.
From mathcomp Require Import reals finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.

(**md**************************************************************************)
(* # Interpreter for Secure Multiparty Protocols                              *)
(*                                                                            *)
(* Unindexed process type for simple interpretation.                          *)
(* Session types and fuel are handled separately in smc_session_types.v.      *)
(*                                                                            *)
(* ```                                                                        *)
(*                proc == unindexed process type                              *)
(*   [procs p1;..;pn ] == pack processes into seq proc                        *)
(*   interp_traces h ps == returns a tuple of traces of size <= h             *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "u *d w" (at level 40).
Reserved Notation "u \*d w" (at level 40).

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

Section interp.
Variable data : Type.

(* Unindexed process type - no fuel or session type indices *)
(* This simplifies interpreter and relational semantics proofs *)
Inductive proc : Type :=
  | Init : data -> proc -> proc
  | Send : nat -> data -> proc -> proc
  | Recv : nat -> (data -> proc) -> proc
  | Ret : data -> proc
  | Finish : proc
  | Fail : proc.

(* Default process for out-of-bounds access *)
Definition default_proc : proc := Fail.

(* Step function for process list *)
Definition step (ps : seq proc) (trace : seq data) (i : nat) :=
  let p := nth default_proc ps i in
  let nop := (p, trace, false) in
  match p with
  | Recv frm f =>
      match nth default_proc ps frm with
      | Send dst v next => 
          if dst == i then (f v, v::trace, true) else nop
      | _ => nop
      end
  | Send dst w next =>
      match nth default_proc ps dst with
      | Recv frm f =>
          if frm == i then (next, trace, true) else nop
      | _ => nop
      end
  | Init d next =>
      (next, d::trace, true)
  | Ret d =>
      (Finish, d :: trace, true)
  | Finish => nop
  | Fail => nop
  end.

Fixpoint interp h (ps : seq proc) (traces : seq (seq data)) :=
  if h is h.+1 then
    let ps_trs' := [seq step ps (nth [::] traces i) i
                   | i <- iota 0 (size ps)] in
    if has snd ps_trs' then
      let ps' := unzip1 (unzip1 ps_trs') in
      let trs' := unzip2 (unzip1 ps_trs') in
      interp h ps' trs'
    else (ps, traces)
  else (ps, traces).

Definition run_interp h procs := interp h procs (nseq (size procs) [::]).

Local Open Scope tuple_ext_scope.
Local Open Scope fset_scope.

(* Definition of lenses from qecc *)
Section lens.
Variables n m : nat.
Definition lens : Type := m.-tuple 'I_n.
Variables (l : lens) (T : Type).
Definition extract (t : n.-tuple T) := map_tuple (tnth t) l.
Definition inject (t : n.-tuple T) (t' : m.-tuple T) :=
  [tuple nth (t !_ i) t' (index i l) | i < n].
End lens.

Lemma map_extract n m A B (l : lens n m) (f : A -> B) v :
  map_tuple f (extract l v) = extract l (map_tuple f v).
Proof. by apply: eq_from_tnth => i; rewrite !tnth_map. Qed.

(* Relational reduction - single step reductions *)
Inductive rstep {n} : forall {m}, lens n m ->
      m.-tuple proc -> m.-tuple proc -> m.-tuple (seq data) -> Prop :=
  | rinit i x p : rstep [tuple i] [tuple Init x p] [tuple p] [tuple [:: x]]
  | rret i x : rstep [tuple i] [tuple Ret x] [tuple Finish] [tuple [:: x]]
  | rcomm i j x pi pj :
    rstep [tuple i; j] [tuple Send j x pi; Recv i pj] [tuple pi; pj x]
          [tuple nil; [:: x]].

(* Reflexive transitive closure of rstep *)
Inductive rsteps {n} :
      n.-tuple proc -> n.-tuple proc -> n.-tuple (seq data) -> Prop :=
  | rone m (l : lens n m) ps ps' traces :
    rstep l (extract l ps) ps' traces ->
    rsteps ps (inject l ps ps') (inject l [tuple nil | _ < n] traces)
  | rrefl ps : rsteps ps ps [tuple nil | _ < n]
  | rtrans ps1 ps2 ps3 tr1 tr2 tr3 :
    rsteps ps1 ps2 tr1 -> rsteps ps2 ps3 tr2 ->
    tr3 = [tuple tr2 !_ i ++ tr1 !_ i | i < n] ->
    rsteps ps1 ps3 tr3.

Definition res_procs n (res : n.-tuple (proc * seq data * bool)) :=
  map_tuple (fun r : proc * seq data * bool => r.1.1) res.
Definition res_traces n (res : n.-tuple (proc * seq data * bool)) :=
  map_tuple (fun r : proc * seq data * bool => r.1.2) res.

(* The step function does all possible reductions at once *)
Lemma step_complete n m (l : lens n m) ps ps' traces' :
  rstep l (extract l ps) ps' traces' ->
  let res := extract l [tuple step ps nil i | i < n] in
  res_procs res = ps' /\
  res_traces res = traces'.
Proof.
move Hps: (extract l ps) => psl H.
case: H Hps => /=.
- move=> i x p [] Hps.
  split; apply /val_inj;
    by rewrite /= tnth_mktuple /= /step -tnth_nth Hps.
- move=> i x [] Hps.
  split; apply /val_inj;
    by rewrite /= tnth_mktuple /= /step -tnth_nth Hps.
- move=> i j x pi pj [] Hi Hj.
  rewrite /res_procs /res_traces !map_extract.
  split; apply /val_inj; congr ([:: _; _]);
    rewrite /= tnth_map tnth_mktuple /= /step;
    by rewrite -tnth_nth (Hi,Hj) -tnth_nth (Hi,Hj) eqxx.
Qed.

Variant rstep2_spec n (ps : n.-tuple proc) (a b : 'I_n) : Prop :=
  | Rstep2Comm x pi pj of
      ps !_ a = Send b x pi & ps !_ b = Recv a pj
    : rstep2_spec ps a b.

Lemma rstep2P n (ps : n.-tuple proc) (a b : 'I_n) ps' traces :
  rstep [tuple a; b] (extract [tuple a; b] ps) ps' traces ->
  rstep2_spec ps a b.
Proof.
inversion 1; subst.
exact: (Rstep2Comm (esym H3) (esym H4)).
Qed.

(* Cannot have two steps conflicting each other.
   Stronger than comm_disjoint, which has the same intension.

   If a reduction gives a Send, there must be a Recv.
   Recv can be rebuilt from Send.

   Build a list of all reductions that we can do,
   meaning list of indices, conditions for firing must be built,
   from this can rebuild the reduction step,
   they are all disjointed,
   ---- still need a proof that combine all of them I get the reduction,

   
   Current
*)
Lemma rstep_disjoint n m p (ps : n.-tuple proc) (l1 : lens n m) (l2 : lens n p)
  psl1 psl2 ps1 tr1 ps2 tr2 :
  psl1 = extract l1 ps -> psl2 = extract l2 ps ->
  rstep l1 psl1 ps1 tr1 -> rstep l2 psl2 ps2 tr2 ->
  l1 == l2 :> seq _ /\ ps1 = ps2 :> seq _ /\ tr1 = tr2 :> seq _
  \/ {in l1 & l2, forall a b, a != b}.
  (* [disjoint l1 & l2] *)
Proof.
move=> Hpsl1 Hpsl2 Hred1 Hred2.
case: Hred1 Hpsl1 => [i j pi | i x | i j x pi pj] /(f_equal val) /= [] Hpi;
case: Hred2 Hpsl2 => [i' j' pi' | i' x' | i' j' x' pi' pj'] /(f_equal val) /=[];
  (have [<-|ii' Hpi'] := eqVneq i i'; [rewrite -Hpi // => -[]
   | right => a b; rewrite !inE; try by do! move /eqP ->]).
 by move=> <- <-; left.
 move=> /eqP-> /orP[] /eqP->; apply/eqP => ij; by rewrite ij -(Hpi',H) in Hpi.
 by move=> <-; left.
 move=> /eqP-> /orP[] /eqP->; apply/eqP => ij; by rewrite ij -(Hpi',H) in Hpi.
 move=> /orP[] /eqP-> /eqP->; apply/eqP => ij; by rewrite -ij -(Hpi,H) in Hpi'.
 move=> /orP[] /eqP-> /eqP->; apply/eqP => ij; by rewrite -ij -(Hpi,H) in Hpi'.
 by move=> /val_inj -> -> -> <- [] <-; left.
 move: H H0.
  have [<-|jj' Hpj' Hpj] := eqVneq j j'.
    by move=> <- [] /val_inj /eqP; rewrite (negbTE ii').
  move=> /orP[] /eqP -> /orP[] /eqP -> //; apply/eqP => ij.
  + by rewrite ij -Hpj' in Hpi.
  + by rewrite ij -Hpi' in Hpj.
Qed.

End interp.

Arguments Finish {data}.
Arguments Fail {data}.
Arguments Init {data}.
Arguments Send {data}.
Arguments Recv {data}.
Arguments Ret {data}.

Section traces.
Variable data : eqType.
Local Open Scope nat_scope.

Lemma size_traces h (procs : seq (proc data)) :
  forall s, s \in (run_interp h procs).2 -> size s <= h.
Proof.
clear.
pose k := h.
rewrite -{2}/k /run_interp.
set traces := nseq _ _ => /=.
have Htr : {in traces, forall s, size s <= k - h}.
  move=> s.
  by rewrite mem_nseq => /andP[] _ /eqP ->.
have : h <= k by [].
elim: h k procs traces Htr => [| h IH] k procs traces Htr hk /=.
  move=> s /Htr.
  by rewrite subn0.
move=> s.
case: ifP => H; last by move/Htr/leq_trans; apply; rewrite leq_subr.
move/IH; apply; last by apply/ltnW.
move=> /= {}s.
rewrite /unzip2 -2!map_comp.
case/mapP => i.
rewrite mem_iota add0n /step => /andP[] _ Hi /=.
have Hsz : size (nth [::] traces i) < k - h.
  case/boolP: (i < size traces) => Hi'.
    apply/(leq_ltn_trans (Htr _ _)).
      by rewrite mem_nth.
    by rewrite subnS prednK // leq_subRL // ?addn1 // ltnW.
  rewrite nth_default.
    by rewrite leq_subRL ?addn1 // ltnW.
  by rewrite leqNgt.
set p := nth _ _ _.
(* Case on process type - 6 constructors: Init, Send, Recv, Ret, Finish, Fail *)
case: p => [d1 p1|dst1 d1 p1|frm1 f1|d1||] /=.
(* Init: s = d1 :: nth... -> size s <= k - h *)
- by move=> ->; exact Hsz.
(* Send: nested match on destination *)
- move=> ->.
  case: (nth _ _ _) => [d2 p2|dst2 d2 p2|frm2 f2|d2||] /=;
    try exact (ltnW Hsz).
  by case: ifP => _ /=; exact (ltnW Hsz).
(* Recv: nested match on source *)
- move=> ->.
  case: (nth _ _ _) => [d2 p2|dst2 d2 p2|frm2 f2|d2||] /=;
    try exact (ltnW Hsz).
  by case: ifP => _ /=; [exact Hsz | exact (ltnW Hsz)].
(* Ret: s = d1 :: nth... -> size s <= k - h *)
- by move=> ->; exact Hsz.
(* Finish: s = nth... -> size s <= k - h *)
- by move=> ->; exact (ltnW Hsz).
(* Fail: s = nth... -> size s <= k - h *)
- by move=> ->; exact (ltnW Hsz).
Qed.

Lemma size_interp h (procs : seq (proc data)) (traces : seq (seq data)) :
  size procs = size traces ->
  size (interp h procs traces).1 = size procs /\
  size (interp h procs traces).2 = size procs.
Proof.
elim: h procs traces => // h IH procs traces Hsz /=.
case: ifP => _ //.
rewrite /unzip1 /unzip2 -!map_comp.
set map1 := map _ _.
set map2 := map _ _.
case: (IH map1 map2).
  by rewrite !size_map.
move=> -> ->.
by rewrite !size_map size_iota.
Qed.

Lemma size_traces_nth h (procs : seq (proc data)) (i : 'I_(size procs)) :
  (size (nth [::] (run_interp h procs).2 i) <= h)%N.
Proof.
by apply/size_traces/mem_nth; rewrite (size_interp _ _).2 // size_nseq.
Qed.

Definition interp_traces h procs : (size procs).-tuple (h.-bseq data) :=
  [tuple Bseq (size_traces_nth h i) | i < size procs].

Lemma interp_traces_ok h procs :
 map val (interp_traces h procs) = (run_interp h procs).2.
Proof.
apply (eq_from_nth (x0:=[::])).
  rewrite size_map /= size_map size_enum_ord.
  by rewrite (size_interp _ _).2 ?size_nseq.
move=> i Hi.
rewrite size_map in Hi.
rewrite (nth_map [bseq]) // /interp_traces.
rewrite size_tuple in Hi.
by rewrite (_ : i = Ordinal Hi) // nth_mktuple.
Qed.

End traces.

(* Convenient notations for process lists *)
Declare Scope proc_scope.

Notation "[procs p ; .. ; q ]" := 
  (cons p .. (cons q nil) ..)
  (at level 0) : proc_scope.

(******************************************************************************)
(** * Termination Predicates                                                  *)
(******************************************************************************)

Section termination.
Variable data : Type.

(* Check if a process is in a final state (Finish or Fail) *)
Definition is_final (p : proc data) : bool :=
  match p with
  | Finish => true
  | Fail => true
  | _ => false
  end.

(* Check if all processes in a list are in final states *)
Definition all_final (ps : seq (proc data)) : bool :=
  all is_final ps.

End termination.

