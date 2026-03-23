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

(* The step function does all possible reductions at once *)
Lemma step_complete n m (l : lens n m) ps ps' traces' :
  rstep l (extract l ps) ps' traces' ->
  let res := extract l [tuple step ps nil i | i < n] in
  map_tuple (fun r => r.1.1) res = ps' /\
  map_tuple (fun r => r.1.2) res = traces'.
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
  rewrite !map_extract.
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

Lemma comm_disjoint n (ps : n.-tuple proc) i j k l ps1 tr1 ps2 tr2 :
  rstep [tuple i; j] (extract [tuple i; j] ps) ps1 tr1 ->
  rstep [tuple k; l] (extract [tuple k; l] ps) ps2 tr2 ->
  (i == k) /\ (j == l) \/ (i != k) /\ (j != l).
Proof.
move=> /rstep2P [x1 pi1 pj1 Hi Hj] /rstep2P [x2 pi2 pj2 Hk Hl].
case/boolP: (i == k) => ik; [left | right]; split => //.
  move: Hk; rewrite -(eqP ik) Hi => -[lj _ _].
  exact/eqP/val_inj.
apply: contra ik => /eqP jl.
move: Hl; rewrite -jl Hj => -[ki _].
exact/eqP/val_inj.
Qed.

Lemma rstep_pss_remove n (ps : n.-tuple proc) (i : 'I_n) (pss : {fset 'I_n})
    (Hpss : forall a b ps' traces,
      rstep [tuple a; b] (extract [tuple a; b] ps) ps' traces ->
      (a \in pss) = (b \in pss)) :
  (forall j x pi, ps !_ i <> Send j x pi) ->
  (forall j pj, ps !_ i <> Recv j pj) ->
  forall a b ps' traces,
    rstep [tuple a; b] (extract [tuple a; b] ps) ps' traces ->
    (a \in pss `\ i) = (b \in pss `\ i).
Proof.
move=> Hsend Hrecv a b ps0 traces /[dup] Hr Hrstep.
case/rstep2P: Hrstep => x pi pj Ha Hb.
have ai : a != i by apply/negP => /eqP ai; subst; exact: (Hsend b x pi Ha).
have bi : b != i by apply/negP => /eqP bi; subst; exact: (Hrecv a pj Hb).
by rewrite !inE (negbTE ai) (negbTE bi) (Hpss _ _ _ _ Hr).
Qed.

(* step_res computes the result of one round of step for all parties in set s.
   For i \in s, it runs step; for i \notin s, it returns the unchanged process.
   This is used in step_sound to relate the functional step to relational rsteps
   by inductively removing parties from s. *)
Definition step_res n (s : {fset 'I_n}) (ps : n.-tuple proc) :=
  [tuple if i \in s then step ps [::] i else (ps !_ i, nil, false) | i < n].

(* When step leaves party i unchanged (Finish, Fail, or no matching partner),
   removing i from the active set doesn't change the overall result.
   This factors out the 5-line eq_from_tnth block that appears identically
   in Finish, Fail, Send-no-Recv, and Recv-no-Send cases of step_sound.
   The key insight: for k != i, membership in pss \ i equals membership in pss;
   for k = i, step returning (ps !_ i, nil, false) matches the "not in set" default. *)
Lemma step_res_inert n (ps : n.-tuple proc) (i : 'I_n) (pss : {fset 'I_n}) :
  i \in pss ->
  step ps [::] i = (ps !_ i, [::], false) ->
  step_res pss ps = step_res (pss `\ i) ps.
Proof.
move=> Hi Hstep.
apply: eq_from_tnth => k; rewrite !tnth_mktuple !inE.
by have [-> |] //= := eqVneq k i; rewrite Hi Hstep.
Qed.

(* After a 1-party rstep produces new process q and trace tr,
   injecting q into the recursive result equals the full step_res result. *)
Lemma step_res_inject1 n (ps : n.-tuple proc) (i : 'I_n) (pss : {fset 'I_n})
    (q : proc) (tr : seq data) :
  i \in pss ->
  step ps [::] i = (q, tr, true) ->
  inject [tuple i]
    (map_tuple (fun r => r.1.1) (step_res (pss `\ i) ps)) [tuple q] =
  map_tuple (fun r : proc * seq data * bool => r.1.1) (step_res pss ps).
Proof.
move=> Hi Hstep.
apply: eq_from_tnth => j; rewrite !(tnth_mktuple, tnth_map) /=.
case/boolP: (i == j) => [/eqP <- | ij] /=.
  by rewrite Hi Hstep.
by rewrite !inE eq_sym ij.
Qed.

(* After a 1-party rstep, the trace projection of step_res matches
   the concatenation pattern required by rsteps. *)
Lemma step_res_trace1 n (ps : n.-tuple proc) (i : 'I_n) (pss : {fset 'I_n})
    (q : proc) (tr : seq data) :
  i \in pss ->
  step ps [::] i = (q, tr, true) ->
  map_tuple (fun r : proc * seq data * bool => r.1.2) (step_res pss ps) =
  [tuple (inject [tuple i] [tuple [::] | _ < n] [tuple tr]) !_ k ++
         (map_tuple (fun r : proc * seq data * bool => r.1.2)
            (step_res (pss `\ i) ps)) !_ k | k < n].
Proof.
move=> Hi Hstep.
apply: eq_from_tnth => k; rewrite !(tnth_mktuple, tnth_map) /=.
case/boolP: (i == k) => [/eqP <- | /negbTE ik] /=.
  by rewrite Hi Hstep !inE eqxx /= cats0.
by have -> : (k \in pss `\ i) = (k \in pss) by rewrite !inE eq_sym ik.
Qed.

(* After a 2-party rstep (rcomm) between parties a and b,
   injecting the new processes into the recursive result (with both a,b removed)
   equals the full step_res result. *)
Lemma step_res_inject2 n (ps : n.-tuple proc) (a b : 'I_n) (pss : {fset 'I_n})
    (qa qb : proc) (tra trb : seq data) :
  a \in pss -> b \in pss -> a != b ->
  step ps [::] a = (qa, tra, true) ->
  step ps [::] b = (qb, trb, true) ->
  inject [tuple a; b]
    (map_tuple (fun r => r.1.1) (step_res (pss `\ a `\ b) ps))
    [tuple qa; qb] =
  map_tuple (fun r : proc * seq data * bool => r.1.1) (step_res pss ps).
Proof.
move=> Ha Hb ab Hstepa Hstepb.
apply: eq_from_tnth => k; rewrite !(tnth_mktuple, tnth_map) /=.
case/boolP: (a == k) => [/eqP <- | ak] /=.
  by rewrite Ha Hstepa.
case/boolP: (b == k) => [/eqP <- | bk] /=.
  by rewrite Hb Hstepb.
by rewrite !inE eq_sym bk eq_sym ak.
Qed.

(* After a 2-party rstep, the trace projection of step_res matches
   the concatenation pattern required by rsteps. *)
Lemma step_res_trace2 n (ps : n.-tuple proc) (a b : 'I_n) (pss : {fset 'I_n})
    (qa qb : proc) (tra trb : seq data) :
  a \in pss -> b \in pss -> a != b ->
  step ps [::] a = (qa, tra, true) ->
  step ps [::] b = (qb, trb, true) ->
  map_tuple (fun r : proc * seq data * bool => r.1.2) (step_res pss ps) =
  [tuple (inject [tuple a; b] [tuple [::] | _ < n] [tuple tra; trb]) !_ k ++
         (map_tuple (fun r : proc * seq data * bool => r.1.2)
            (step_res (pss `\ a `\ b) ps)) !_ k | k < n].
Proof.
move=> Ha Hb ab Hstepa Hstepb.
apply: eq_from_tnth => k; rewrite !(tnth_mktuple, tnth_map) /=.
rewrite !inE !(eq_sym k).
have [<- | ak] /= := eqVneq a k.
  by rewrite Ha Hstepa /= ifF ?cats0 // andbF.
have [<- | bk] /= := eqVneq b k.
  by rewrite Hb Hstepb /= cats0.
done.
Qed.

(* Soundness: mapping step over all processes can be simulated by rsteps *)
Lemma step_sound n (ps : n.-tuple proc) :
  let res := [tuple step ps nil i | i < n] in
  let ps' := map_tuple (fun r => r.1.1) res in
  let tr := map_tuple (fun r => r.1.2) res in
  rsteps ps ps' tr.
Proof.
pose pss := [fset x : 'I_n | true].
move=> res.
have -> : res = step_res pss ps.
  by apply: eq_from_tnth => i; rewrite !tnth_mktuple ifT // !inE.
have : forall i j ps' traces,
    rstep [tuple i; j] (extract [tuple i; j] ps) ps' traces ->
    (i \in pss) = (j \in pss)
    by move=> *; rewrite !inE.
elim/finSet_rect: pss {res} => /= pss IH Hpss.
case: (fset_0Vmem pss) => [-> | [i Hi]].
  (* Base case: empty set *)
  rewrite (_ : map_tuple _ _ = ps); last first.
    by apply: eq_from_tnth => i; rewrite tnth_map !tnth_mktuple inE.
  rewrite (_ : map_tuple _ _ = [tuple nil | _ < n]); last first.
    by apply: eq_from_tnth => i; rewrite tnth_map !tnth_mktuple inE.
  by constructor.
(* Inductive case: i in pss *)
case Hpi: (ps !_ i) => [x p | j x p | j f | x ||].
(* Case Init x p *)
- have Hstep: step ps [::] i = (p, [:: x], true)
    by rewrite /step -tnth_nth Hpi.
  pose pss' := pss `\ i.
  have H': pss' `<` pss by apply: fproperD1.
  apply: (rtrans (IH _ H' _)); last 3 first.
  + apply: rstep_pss_remove Hpss _ _ => [j' x' pi'|j' pj']; by rewrite Hpi.
  + move: (rinit i x p).
    set ps'' := map_tuple _ _.
    have -> : [tuple Init x p] = extract [tuple i] ps''.
      by apply/val_inj; rewrite /= /ps'' tnth_map tnth_mktuple !inE eqxx /= Hpi.
    move/rone. rewrite (step_res_inject1 Hi Hstep). exact.
  + exact: (step_res_trace1 Hi Hstep).
(* Case Send j x p *)
- have [[pj Hpj]|Hn] : decidable (exists pj, nth Fail ps j = Recv i pj).
    case Hpj: (nth Fail ps j) => [xj pj | k xj pj | i' pj | xj ||];
      try by right => -[pj'].
    case/boolP: (i' == i) => [/eqP -> | i'i]; first by left; exists pj.
    by right => -[pj'] [] /eqP; move/negbTE: i'i => ->.
  + (* Send-Recv communication case *)
    have jn: (j < n)%N.
      rewrite ltnNge; apply/negP => nj.
      by rewrite nth_default ?size_tuple // in Hpj.
    case/boolP: (i == Ordinal jn) => ij /=.
      by rewrite (eqP ij) (tnth_nth Fail) Hpj in Hpi.
    have := rcomm i (Ordinal jn) x p pj.
    rewrite (_ : [tuple Send _ _ _; _] = extract [tuple i; Ordinal jn] ps);
      last by apply/val_inj => /=; rewrite Hpi (tnth_nth Fail) Hpj.
    move=> Hr.
    have Hj : Ordinal jn \in pss by move/Hpss: Hr => <-.
    have Hstepi: step ps [::] i = (p, [::], true)
      by rewrite /step /default_proc -tnth_nth Hpi Hpj eqxx.
    have Hstepj: step ps [::] (Ordinal jn) = (pj x, [:: x], true)
      by rewrite /step /default_proc Hpj -tnth_nth Hpi eqxx.
    pose pss' := pss `\ i `\ Ordinal jn.
    have H': pss' `<` pss.
      exact/(fsub_proper_trans (B:=pss `\ i))/fproperD1/Hi/fsubD1set.
    apply: (rtrans (IH _ H' _)); last 3 first.
    * move=> k k' ps0 traces /[dup] H /rstep2P [x'' pi'' pj'' Hk Hk'].
      rewrite !inE.
      case: (comm_disjoint Hr H) => -[].
        by move => /eqP <- /eqP <-; rewrite !eqxx !andbF.
      rewrite eq_sym (eq_sym _ k') => -> ->.
      have [kj|_] := eqVneq k (Ordinal jn).
        by rewrite kj (tnth_nth Fail) Hpj in Hk.
      have [k'i|_] := eqVneq k' i; first by rewrite k'i Hpi in Hk'.
      exact: (Hpss _ _ _ _ H).
    * move: (rcomm i (Ordinal jn) x p pj).
      set ps'' := map_tuple _ _.
      rewrite (_ : [tuple Send _ _ _; _] = extract [tuple i; Ordinal jn] ps'');
        last first.
        apply/val_inj; rewrite /=/ps'' !(tnth_mktuple,tnth_map) !inE !eqxx /=.
        by rewrite andbF Hpi (tnth_nth Fail) Hpj.
      move/rone. rewrite (step_res_inject2 Hi Hj ij Hstepi Hstepj). exact.
    * exact: (step_res_trace2 Hi Hj ij Hstepi Hstepj).
  + (* Send but no matching Recv - skip this process *)
    have Hstep: step ps [::] i = (ps !_ i, [::], false).
      rewrite /step -tnth_nth Hpi.
      case Hj: nth => [||e pj|||] //.
      case: ifP => ei //.
      by elim: Hn; exists pj; rewrite -(eqP ei).
    rewrite (step_res_inert Hi Hstep).
    apply: IH; first exact: fproperD1.
    move=> a b ps0 traces /[dup] Hr /rstep2P [x' pi' pj' Ha Hb].
    rewrite !inE.
    have [ai | ai] := eqVneq a i; have [bi | bi] // := eqVneq b i.
    * subst a; move: Ha; rewrite Hpi => -[bj _ _].
      elim: Hn; exists pj'.
      by rewrite bj -tnth_nth Hb.
    * by subst b; rewrite Hpi in Hb.
    * exact: (Hpss _ _ _ _ Hr).
(* Case Recv j f - symmetric to Send *)
- have [[v [pj' Hpj]]|Hn] : decidable (exists v pj', nth Fail ps j = Send i v pj').
    case Hpj: (nth Fail ps j) => [xj qj | i' xj qj | k' qj | xj ||];
      try by right => -[v] [pj''].
    case/boolP: (i' == i) => [/eqP -> | i'i]; first by left; exists xj, qj.
    by right => -[v] [pj''] [] /eqP; move/negbTE: i'i => ->.
  + (* Recv-Send communication case - dual of Send-Recv *)
    have jn: (j < n)%N.
      rewrite ltnNge; apply/negP => nj.
      by rewrite nth_default ?size_tuple // in Hpj.
    case/boolP: (i == Ordinal jn) => ij /=.
      by rewrite (eqP ij) (tnth_nth Fail) Hpj in Hpi.
    move: (rcomm (Ordinal jn) i v pj' f).
    rewrite (_ : [tuple Send _ _ _; _] = extract [tuple Ordinal jn; i] ps);
      last by apply/val_inj => /=; rewrite (tnth_nth Fail) Hpj Hpi.
    move=> Hr.
    have Hj : Ordinal jn \in pss by move/Hpss: Hr => ->.
    have ji : Ordinal jn != i by rewrite eq_sym.
    have Hstepj: step ps [::] (Ordinal jn) = (pj', [::], true)
      by rewrite /step /default_proc /= Hpj -tnth_nth Hpi eqxx.
    have Hstepi: step ps [::] i = (f v, [:: v], true)
      by rewrite /step /default_proc -tnth_nth Hpi /= Hpj eqxx.
    pose pss' := pss `\ i `\ Ordinal jn.
    have H': pss' `<` pss.
      exact/(fsub_proper_trans (B:=pss `\ i))/fproperD1/Hi/fsubD1set.
    apply: (rtrans (IH _ H' _)); last 3 first.
    * move=> k k' ps0 traces /[dup] H /rstep2P [x'' pi'' pj'' Hk Hk'].
      rewrite !inE.
      case: (comm_disjoint Hr H) => -[].
        by move => /eqP <- /eqP <-; rewrite !eqxx !andbF.
      rewrite eq_sym (eq_sym _ k') => -> ->.
      have [ki|_] := eqVneq k i.
        by rewrite ki Hpi in Hk.
      have [k'j|_] := eqVneq k' (Ordinal jn).
        by rewrite k'j (tnth_nth Fail) Hpj in Hk'.
      exact: (Hpss _ _ _ _ H).
    * (* The reduction: Send j sends to Recv i *)
      move: (rcomm (Ordinal jn) i v pj' f).
      set ps'' := map_tuple _ _.
      rewrite (_ : [tuple Send _ _ _; _] = extract [tuple Ordinal jn; i] ps'');
        last first.
        apply/val_inj; rewrite /=/ps'' !(tnth_mktuple,tnth_map) !inE !eqxx /=.
        by rewrite (tnth_nth Fail) Hpj ij Hpi.
      move/rone.
      have -> : inject [tuple Ordinal jn; i] ps'' [tuple pj'; f v] =
           map_tuple (fun r : proc * seq data * bool => r.1.1) (step_res pss ps).
        rewrite /ps'' /pss'.
        have -> : (pss `\ i `\ Ordinal jn) = (pss `\ Ordinal jn `\ i)
          by apply/fsetP => z; rewrite !inE andbCA.
        exact: (step_res_inject2 Hj Hi ji Hstepj Hstepi).
      exact.
    * rewrite /pss'.
      have -> : (pss `\ i `\ Ordinal jn) = (pss `\ Ordinal jn `\ i)
        by apply/fsetP => z; rewrite !inE andbCA.
      exact: (step_res_trace2 Hj Hi ji Hstepj Hstepi).
  + (* Recv but no matching Send - skip this process *)
    have Hstep: step ps [::] i = (ps !_ i, [::], false).
      rewrite /step -tnth_nth Hpi.
      case Hj: nth => [|dst' v' pj'||||] //.
      case: ifP => ei //.
      by elim: Hn; exists v', pj'; rewrite -(eqP ei).
    rewrite (step_res_inert Hi Hstep).
    apply: IH; first exact: fproperD1.
    move=> a b ps0 traces /[dup] Hr /rstep2P [x' pi' pj0 Ha Hb].
    rewrite !inE.
    have [ai | ai] := eqVneq a i; have [bi | bi] // := eqVneq b i.
    * by subst a; rewrite Hpi in Ha.
    * subst b; move: Hb; rewrite Hpi => -[aj _].
      rewrite (tnth_nth Fail) -aj in Ha.
      by elim: Hn; exists x', pi'.
    * exact: (Hpss _ _ _ _ Hr).
(* Case Ret x *)
- have Hstep: step ps [::] i = (Finish, [:: x], true)
    by rewrite /step -tnth_nth Hpi.
  pose pss' := pss `\ i.
  have H': pss' `<` pss by apply: fproperD1.
  apply: (rtrans (IH _ H' _)); last 3 first.
  + apply: rstep_pss_remove Hpss _ _ => [j' x' pi'|j' pj']; by rewrite Hpi.
  + move: (rret i x).
    set ps'' := map_tuple _ _.
    have -> : [tuple Ret x] = extract [tuple i] ps''.
      by apply/val_inj; rewrite /= /ps'' tnth_map tnth_mktuple !inE eqxx /= Hpi.
    move/rone. rewrite (step_res_inject1 Hi Hstep). exact.
  + exact: (step_res_trace1 Hi Hstep).
(* Case Finish - does nothing, just remove from set *)
- have Hstep: step ps [::] i = (ps !_ i, [::], false)
    by rewrite /step -tnth_nth Hpi.
  rewrite (step_res_inert Hi Hstep).
  apply: IH; first exact: fproperD1.
  apply: rstep_pss_remove Hpss _ _ => [j' x' pi'|j' pj']; by rewrite Hpi.
(* Case Fail - does nothing, just remove from set *)
- have Hstep: step ps [::] i = (ps !_ i, [::], false)
    by rewrite /step -tnth_nth Hpi.
  rewrite (step_res_inert Hi Hstep).
  apply: IH; first exact: fproperD1.
  apply: rstep_pss_remove Hpss _ _ => [j' x' pi'|j' pj']; by rewrite Hpi.
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

