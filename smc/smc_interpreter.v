From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg ring.
From mathcomp Require Import Rstruct reals finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_proba smc_entropy.
Require Import smc_tactics.

(**md**************************************************************************)
(* # Interpreter for Secure Multiparty Protocols                              *)
(*                                                                            *)
(* Fuel-indexed process type where fuel is computed by type inference.        *)
(*                                                                            *)
(* ```                                                                        *)
(*              proc n == fuel-indexed process type (fuel inferred via _)     *)
(*               aproc == existential wrapper { n : nat & proc n }            *)
(*            get_fuel == extract fuel from aproc                             *)
(*            sum_fuel == compute sum of fuels from seq aproc                 *)
(*   [procs p1;..;pn ] == pack processes into seq aproc (auto-packing)        *)
(*           [> procs] == notation for sum_fuel procs                         *)
(*   interp_traces h ps == returns a tuple of traces of size <= h             *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "u *d w" (at level 40).
Reserved Notation "u \*d w" (at level 40).

Import GRing.Theory Num.Theory.

Module scp := smc_entropy.smc_entropy_proofs.

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

(* Fuel-indexed process type: fuel is computed by type inference *)
Inductive proc : nat -> Type :=
  | Init : forall n, data -> proc n -> proc n.+1
  | Send : forall n, nat -> data -> proc n -> proc n.+1
  | Recv : forall n, nat -> (data -> proc n) -> proc n.+1
  | Ret : data -> proc 2
  | Finish : proc 1
  | Fail : forall n, proc n.

(* Existential wrapper for heterogeneous process lists *)
Definition aproc := { n : nat & proc n }.

(* Extract fuel from packed process *)
Definition get_fuel (p : aproc) : nat := projT1 p.

(* Extract process from packed process *)
Definition get_proc (p : aproc) : proc (get_fuel p) := projT2 p.

(* Pack a process into aproc *)
Definition pack {n} (p : proc n) : aproc := existT _ n p.

(* Default packed process (Fail at fuel 0) *)
Definition default_aproc : aproc := pack (@Fail 0).

(* Compute sum of all fuels - used as interpreter fuel *)
Definition sum_fuel (ps : seq aproc) : nat := 
  foldr (fun p acc => get_fuel p + acc) 0 ps.

(* Step function for aproc *)
Definition step (ps : seq aproc) (trace : seq data) (i : nat) :=
  let p := nth default_aproc ps i in
  let nop := (p, trace, false) in
  match get_proc p in proc n return (aproc * seq data * bool) with
  | @Recv n frm f =>
      match get_proc (nth default_aproc ps frm) in proc m 
            return (aproc * seq data * bool) with
      | @Send m dst v next => 
          if dst == i then (pack (f v), v::trace, true) else nop
      | _ => nop
      end
  | @Send n dst w next =>
      match get_proc (nth default_aproc ps dst) in proc m
            return (aproc * seq data * bool) with
      | @Recv m frm f =>
          if frm == i then (pack next, trace, true) else nop
      | _ => nop
      end
  | @Init n d next =>
      (pack next, d::trace, true)
  | Ret d =>
      (pack Finish, d :: trace, true)
  | Finish => nop
  | @Fail n => nop
  end.

Fixpoint interp h (ps : seq aproc) (traces : seq (seq data)) :=
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

(*
Inductive rred {n} : forall {m},lens n m ->
      m.-tuple proc -> m.-tuple proc -> m.-tuple (seq data) -> Prop :=
  | rinit i x p : rred [tuple i] [tuple Init x p] [tuple p] [tuple [:: x]]
  | rret i x : rred [tuple i] [tuple Ret x] [tuple Finish] [tuple [:: x]]
  | rcomm i j x pi pj :
    rred [tuple i; j] [tuple Send j x pi; Recv i pj] [tuple pi; pj x]
         [tuple nil; [:: x]].

Inductive rstep {n} :
      n.-tuple proc -> n.-tuple proc -> n.-tuple (seq data) -> Prop :=
  | rone m (l : lens n m) ps ps' traces :
    rred l (extract l ps) ps' traces ->
    rstep ps (inject l ps ps') (inject l [tuple nil | _ < n] traces)
  | rrefl ps : rstep ps ps [tuple nil | _ < n]
  | rtrans ps1 ps2 ps3 tr1 tr2 tr3 :
    rstep ps1 ps2 tr1 -> rstep ps2 ps3 tr2 ->
    tr3 = [tuple tr2 !_ i ++ tr1 !_ i | i < n] ->
    rstep ps1 ps3 tr3.

(* we can reintroduce the trace argument after executing step *)
Definition add_trace tr (res : (proc * seq data * bool)) :=
  let '(p,tr',c) := res in (p,tr'++tr,c).
Lemma step_trace n (ps : n.-tuple proc) tr i :
  step ps tr i = add_trace tr (step ps nil i).
Proof.
by rewrite /step; case: nth => //= [j x p | j x]; case: nth => // *; case: ifP.
Qed.

(* The step function does all possible reductions at once *)
Lemma rred_ok n m (l : lens n m) ps ps' traces' :
  rred l (extract l ps) ps' traces' ->
  let res := extract l [tuple step ps nil i | i < n] in
  map_tuple (fun r => r.1.1) res = ps' /\
  map_tuple (fun r => r.1.2) res = traces'.
Proof.
move Hps : (extract l ps) => psl H.
case: H Hps => /=.
- move => i x p [] Hps; split; apply/val_inj;
    by rewrite /= tnth_mktuple /= /step -tnth_nth Hps.
- move => i x [] Hps; split; apply/val_inj;
    by rewrite /= tnth_mktuple /= /step -tnth_nth Hps.
- move => i j x pi pj [] Hi Hj; rewrite !map_extract.
  split; apply/val_inj; congr ([:: _; _]);
    rewrite /= tnth_map tnth_mktuple /= /step;
    by rewrite -tnth_nth (Hi,Hj) -tnth_nth (Hi,Hj) eqxx.
Qed.

Lemma step_sound n (ps : n.-tuple proc) :
  let res := [tuple step ps nil i | i < n] in
  rstep ps (map_tuple (fun r => r.1.1) res) (map_tuple (fun r => r.1.2) res).
Proof.
pose pss := [fset x : 'I_n | true ].
pose res' (s : {fset 'I_n}) (ps : n.-tuple proc) :=
  [tuple if i \in s then step ps [::] i else (ps !_ i, nil, false) | i < n].
move=> res.
have -> : res = res' pss ps.
  by apply: eq_from_tnth => i; rewrite !tnth_mktuple ifT // !inE.
have : forall i j ps' traces,
    rred [tuple i; j] (extract [tuple i; j] ps) ps' traces ->
    (i \in pss) = (j \in pss)
    by move=> *; rewrite !inE.
elim/finSet_rect: pss {res} => /= pss IH Hpss.
case: (fset_0Vmem pss) => [-> | [i Hi]].
  rewrite (_ : map_tuple _ _ = ps).
    rewrite (_ : map_tuple _ _ = [tuple nil | _ < n]). by constructor.
    by apply: eq_from_tnth => i; rewrite tnth_map !tnth_mktuple inE.
  by apply: eq_from_tnth => i; rewrite tnth_map !tnth_mktuple inE.
case Hpi: (ps !_ i) => [x p | j x p | j p | x ||].
- pose pss' := pss `\ i.
  have H' : pss' `<` pss by apply: fproperD1.
  apply: (rtrans (IH _ H' _)); last 3 first.
      move=> k j ps' traces H.
      rewrite !inE (Hpss _ _ _ _ H).
      have [ki|_] := eqVneq k i.
        by inversion H; subst; rewrite Hpi in H3.
      have [ji|//] := eqVneq j i.
      by inversion H; subst; rewrite Hpi in H4.
    move: (rinit i x p).
    set ps' := map_tuple _ _.
    have -> : [tuple Init x p] = extract [tuple i] ps'.
      by apply/val_inj; rewrite /= /ps' tnth_map tnth_mktuple !inE eqxx /= Hpi.
    move/rone.
    have -> : inject [tuple i] ps' [tuple p] =
            map_tuple (fun r : proc * seq data * bool => r.1.1) (res' pss ps).
      apply: eq_from_tnth => j; rewrite !(tnth_mktuple,tnth_map) /=.
      case/boolP: (i == j) => [/eqP <-|ij] /=.
        by rewrite Hi /step -tnth_nth Hpi.
      have -> // : (j \in pss') = (j \in pss) by rewrite !inE eq_sym ij.
    apply.
  apply: eq_from_tnth => j; rewrite !(tnth_mktuple, tnth_map) /=.
  case/boolP: (i == j) => [/eqP <-|ij] /=.
    by rewrite Hi !inE eqxx /= /step -tnth_nth Hpi.
  have -> // : (j \in pss') = (j \in pss) by rewrite !inE eq_sym ij.
- have [[pj Hpj]|] : decidable (exists pj, nth Fail ps j = Recv i pj).
    case Hpj: (nth Fail ps j) => [xj pj | k xj pj | i' pj | xj ||];
      try by right => -[pj'].
    case/boolP: (i' == i) => [/eqP -> | i'i]; first by left; exists pj.
    by right => -[pj'] [] /eqP; move/negbTE: i'i => ->.
  - have jn : (j < n)%N.
      rewrite ltnNge; apply/negP => nj.
      rewrite nth_default // in Hpj.
      by rewrite size_tuple.
    case/boolP: (i == Ordinal jn) => ij /=.
      by rewrite (eqP ij) (tnth_nth Fail) Hpj in Hpi.
    pose pss' := pss `\ i `\ Ordinal jn.
    have H' : pss' `<` pss.
      exact/(fsub_proper_trans (B:=pss `\ i))/fproperD1/Hi/fsubD1set.
    apply: (rtrans (IH _ H' _)); last 3 first.
        move=> k k' ps' traces H.
        rewrite !inE.
        have [kj|_] := eqVneq k (Ordinal jn).
          by inversion H; subst; rewrite (tnth_nth Fail) Hpj in H3.
        have [ki|ki] := eqVneq k i.
          inversion H; subst.
          have [//|k'j] := eqVneq k' (Ordinal jn).
          move: H3; rewrite Hpi => -[] k'j'.
          by move/eqP: k'j; elim; apply/val_inj.
        have [k'j|_] := eqVneq k' (Ordinal jn).
          inversion H; subst.
          move: H4; rewrite (tnth_nth Fail) Hpj => -[] ki'.
          by move/eqP: ki; elim; apply/val_inj.
        have [k'i|_] := eqVneq k' i.
          by inversion H; subst; rewrite Hpi in H4.
        exact: (Hpss _ _ _ _ H).
      move: (rcomm i (Ordinal jn) x p pj).
      set ps' := map_tuple _ _.
      rewrite (_ : [tuple  Send _ _ _; _] = extract [tuple i; Ordinal jn] ps');
        last first.
        apply/val_inj; rewrite /=/ps' !(tnth_mktuple,tnth_map) !inE !eqxx /=.
        by rewrite andbF Hpi (tnth_nth Fail) Hpj.
      move/rone.
      have -> : inject [tuple i; Ordinal jn] ps' [tuple p; pj x] =
           map_tuple (fun r : proc * seq data * bool => r.1.1) (res' pss ps).
        apply: eq_from_tnth => k; rewrite !(tnth_mktuple,tnth_map) /=.
        case/boolP: (i == k) => [/eqP <-|ik] /=.
          by rewrite Hi /step -tnth_nth Hpi Hpj eqxx.
        case/boolP: (_ == _) => jk /=.
        move: (rcomm i (Ordinal jn) x p pj).
        rewrite (_ : [tuple  Send _ _ _; _] = extract [tuple i; Ordinal jn] ps);
        last by apply/val_inj => /=; rewrite Hpi (tnth_nth Fail) Hpj.
        move=> Hr.
        by rewrite -(eqP jk) -(Hpss _ _ _ _ Hr) Hi /step Hpj -tnth_nth Hpi eqxx.
      by rewrite !inE eq_sym jk eq_sym ik.
    apply.
    apply: eq_from_tnth => k; rewrite !(tnth_mktuple, tnth_map) /=.
    rewrite !inE !(eq_sym k) andbCA.
    have [<- | ik] /= := eqVneq i k.
      by rewrite Hi /step -tnth_nth Hpi Hpj eqxx.
    have [<- |] //= := eqVneq (Ordinal jn) k.
    move: (rcomm i (Ordinal jn) x p pj).
    rewrite (_ : [tuple  Send _ _ _; _] = extract [tuple i; Ordinal jn] ps);
    last by apply/val_inj => /=; rewrite Hpi (tnth_nth Fail) Hpj.
    move=> Hr.
    by rewrite -(Hpss _ _ _ _ Hr) Hi /step Hpj -tnth_nth Hpi eqxx.
  move=> Hn.
  pose pss' := pss `\ i.
  have H' : pss' `<` pss by apply: fproperD1.
  have -> : res' pss ps = res' pss' ps.
    apply: eq_from_tnth => k.
    rewrite !tnth_mktuple !inE.
    have [-> |] //= := eqVneq k i.
    rewrite Hi /step -tnth_nth Hpi.
    case Hj: nth => [||e pj|||] //.
    case: ifP => ei //.
    elim: Hn.
    by exists pj; rewrite -(eqP ei).
  apply: IH => //.
  move=> a b ps' traces.
  rewrite !inE.
  have [-> | ai] := eqVneq a i; have [-> | bi] // := eqVneq b i.
  + inversion 1; subst.
    move: H3; rewrite Hpi => -[bj].
    elim: Hn; exists pj.
    by rewrite -bj -tnth_nth H4.
  + inversion 1; subst.
    by rewrite Hpi in H4.
  + exact: Hpss.
(* remaining cases are similar, but we need to find a shorted way *)
Abort.
*)
End interp.

Arguments Finish {data}.
Arguments Fail {data n}.
Arguments Init {data n}.
Arguments Send {data n}.
Arguments Recv {data n}.
Arguments pack {data n}.

Section traces.
Variable data : eqType.
Local Open Scope nat_scope.

Lemma size_traces h (procs : seq (aproc data)) :
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
case: (get_proc p) => [n1 d1 p1|n1 dst1 d1 p1|n1 frm1 f1|d1||n1] /=.
(* Init: s = d1 :: nth... -> size s <= k - h *)
- by move=> ->; exact Hsz.
(* Send: nested match on destination *)
- move=> ->.
  case: (get_proc _) => [n2 d2 p2|n2 dst2 d2 p2|n2 frm2 f2|d2||n2] /=;
    try exact (ltnW Hsz).
  by case: ifP => _ /=; exact (ltnW Hsz).
(* Recv: nested match on source *)
- move=> ->.
  case: (get_proc _) => [n2 d2 p2|n2 dst2 d2 p2|n2 frm2 f2|d2||n2] /=;
    try exact (ltnW Hsz).
  by case: ifP => _ /=; [exact Hsz | exact (ltnW Hsz)].
(* Ret: s = d1 :: nth... -> size s <= k - h *)
- by move=> ->; exact Hsz.
(* Finish: s = nth... -> size s <= k - h *)
- by move=> ->; exact (ltnW Hsz).
(* Fail: s = nth... -> size s <= k - h *)
- by move=> ->; exact (ltnW Hsz).
Qed.

Lemma size_interp h (procs : seq (aproc data)) (traces : seq (seq data)) :
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

Lemma size_traces_nth h (procs : seq (aproc data)) (i : 'I_(size procs)) :
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

(* Convenient notations for process lists and fuel computation *)
Declare Scope proc_scope.

Notation "[procs p ; .. ; q ]" := 
  (cons (pack p) .. (cons (pack q) nil) ..)
  (at level 0) : proc_scope.

Notation "[> ps ]" := (sum_fuel ps) (at level 0) : proc_scope.

(******************************************************************************)
(** * Termination Predicates                                                  *)
(******************************************************************************)

Section termination.
Variable data : Type.

(* Check if a process is in a final state (Finish or Fail) *)
Definition is_final (p : aproc data) : bool :=
  match get_proc p with
  | Finish => true
  | @Fail _ _ => true
  | _ => false
  end.

(* Check if all processes in a list are in final states *)
Definition all_final (ps : seq (aproc data)) : bool :=
  all is_final ps.

End termination.

