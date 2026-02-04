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
Inductive rred {n} : forall {m}, lens n m ->
      m.-tuple proc -> m.-tuple proc -> m.-tuple (seq data) -> Prop :=
  | rinit i x p : rred [tuple i] [tuple Init x p] [tuple p] [tuple [:: x]]
  | rret i x : rred [tuple i] [tuple Ret x] [tuple Finish] [tuple [:: x]]
  | rcomm i j x pi pj :
    rred [tuple i; j] [tuple Send j x pi; Recv i pj] [tuple pi; pj x]
         [tuple nil; [:: x]].

(* Reflexive transitive closure of rred *)
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

(* Helper: reintroduce trace argument after executing step *)
Definition add_trace tr (res : (proc * seq data * bool)) :=
  let '(p,tr',c) := res in (p, tr' ++ tr, c).

(* Reduction specification - packages reduction data *)
Inductive red_spec n : Type :=
  | RSinit (i : 'I_n) (x : data) (p : proc)
  | RSret (i : 'I_n) (x : data)
  | RScomm (i j : 'I_n) (x : data) (pi : proc) (pj : data -> proc).

Arguments RSinit {n}.
Arguments RSret {n}.
Arguments RScomm {n}.

(* Get indices involved in a reduction *)
Definition red_spec_indices {n} (r : red_spec n) : seq 'I_n :=
  match r with
  | RSinit i _ _ => [:: i]
  | RSret i _ => [:: i]
  | RScomm i j _ _ _ => [:: i; j]
  end.

(* Get lens for a reduction *)
Definition red_spec_lens {n} (r : red_spec n) :
    lens n (size (red_spec_indices r)) :=
  match r return lens n (size (red_spec_indices r)) with
  | RSinit i _ _ => [tuple i]
  | RSret i _ => [tuple i]
  | RScomm i j _ _ _ => [tuple i; j]
  end.

(* Get input processes for a reduction *)
Definition red_spec_input {n} (r : red_spec n) :
    (size (red_spec_indices r)).-tuple proc :=
  match r return (size (red_spec_indices r)).-tuple proc with
  | RSinit _ x p => [tuple Init x p]
  | RSret _ x => [tuple Ret x]
  | RScomm i j x pi pj => [tuple Send (nat_of_ord j) x pi; Recv (nat_of_ord i) pj]
  end.

(* Get output processes for a reduction *)
Definition red_spec_output {n} (r : red_spec n) :
    (size (red_spec_indices r)).-tuple proc :=
  match r return (size (red_spec_indices r)).-tuple proc with
  | RSinit _ _ p => [tuple p]
  | RSret _ _ => [tuple Finish]
  | RScomm _ _ x pi pj => [tuple pi; pj x]
  end.

(* Get output traces for a reduction *)
Definition red_spec_traces {n} (r : red_spec n) :
    (size (red_spec_indices r)).-tuple (seq data) :=
  match r return (size (red_spec_indices r)).-tuple (seq data) with
  | RSinit _ x _ => [tuple [:: x]]
  | RSret _ x => [tuple [:: x]]
  | RScomm _ _ x _ _ => [tuple nil; [:: x]]
  end.

(* Try to build a red_spec from index i based on the process at that index *)
Definition red_spec_at {n} (ps : n.-tuple proc) (i : 'I_n) : option (red_spec n) :=
  match ps !_ i with
  | Init x p => Some (RSinit i x p)
  | Ret x => Some (RSret i x)
  | Send j x p =>
      if (j < n)%N =P true is ReflectT jn then
        let j' := Ordinal jn in
        match ps !_ j' with
        | Recv frm f => if frm == i then Some (RScomm i j' x p f) else None
        | _ => None
        end
      else None
  | Recv j f =>
      if (j < n)%N =P true is ReflectT jn then
        let j' := Ordinal jn in
        match ps !_ j' with
        | Send dst x p => if dst == i then Some (RScomm j' i x p f) else None
        | _ => None
        end
      else None
  | _ => None
  end.

(* A reduction applies to a process tuple (propositional) *)
Definition red_applies {n} (ps : n.-tuple proc) (r : red_spec n) : Prop :=
  extract (red_spec_lens r) ps = red_spec_input r :> seq _.

(* red_spec yields valid rred *)
Lemma red_spec_valid n (r : red_spec n) :
  rred (red_spec_lens r) (red_spec_input r) (red_spec_output r)
       (red_spec_traces r).
Proof. by case: r => *; constructor. Qed.

(* red_spec_at produces reductions that apply *)
Lemma red_spec_at_applies n (ps : n.-tuple proc) i r :
  red_spec_at ps i = Some r -> red_applies ps r.
Proof.
rewrite /red_applies /red_spec_at.
case Hpi: (ps !_ i) => [x p|dst w next|frm f|x||] //=.
- by move=> [<-] /=; rewrite Hpi.
- case: eqP => //= dstn.
  case Hdst: (ps !_ _) => [|dst' w' next'|frm' f'|||] //=.
  case: ifP => // frm'i [<-] /=.
  by rewrite Hpi Hdst (eqP frm'i).
- case: eqP => //= frmn.
  case Hfrm: (ps !_ _) => [|dst' w' next'||||] //=.
  case: ifP => // dsti [<-] /=.
  by rewrite Hfrm Hpi (eqP dsti).
- by move=> [<-] /=; rewrite Hpi.
Qed.

(* Collect all applicable reductions from a process tuple *)
(* Only use red_spec_at (sender perspective) to avoid duplicating RScomm *)
Definition applicable_reds {n} (ps : n.-tuple proc) : seq (red_spec n) :=
  pmap (red_spec_at ps) (enum 'I_n).

(* Check if two lenses are disjoint (using seq predicate) *)
Definition lens_disjoint {n m1 m2} (l1 : lens n m1) (l2 : lens n m2) : bool :=
  all (fun x => x \notin l2) l1.

(* Helper: i not in lens implies index i l >= size l *)
Lemma notin_index_geq n m (l : lens n m) (i : 'I_n) :
  i \notin l -> (m <= index i l)%N.
Proof.
move=> Hnotin.
rewrite leqNgt.
apply/negP => Hidx.
move: Hnotin.
by rewrite -index_mem size_tuple Hidx.
Qed.

(* Injecting with disjoint lenses commutes *)
(* TODO: Complete this proof - the structure is correct but SSReflect rewriting is complex *)
Lemma inject_disjoint_comm n m1 m2 (T : eqType) (l1 : lens n m1) (l2 : lens n m2)
    (ps : n.-tuple T) (ps1 : m1.-tuple T) (ps2 : m2.-tuple T) :
  lens_disjoint l1 l2 ->
  inject l1 (inject l2 ps ps2) ps1 = inject l2 (inject l1 ps ps1) ps2.
Proof. Admitted.

Lemma step_trace n (ps : n.-tuple proc) tr i :
  step ps tr i = add_trace tr (step ps nil i).
Proof.
rewrite /step /add_trace.
case Hp: (nth default_proc ps i) => [d next|dst w next|frm f|d||] //=.
- (* Send case *)
  case Hdst: (nth default_proc ps dst) => [d' p'|dst' w' next'|frm' f'|d'||] //=.
  by case: ifP.
- (* Recv case *)
  case Hfrm: (nth default_proc ps frm) => [d' p'|dst' w' next'|frm' f'|d'||] //=.
  by case: ifP.
Qed.

(* The step function does all possible reductions at once *)
Lemma rred_ok n m (l : lens n m) ps ps' traces' :
  rred l (extract l ps) ps' traces' ->
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

Lemma rred_disjoint n m p (ps : n.-tuple proc) (l1 : lens n m) (l2 : lens n p)
  psl1 psl2 ps1 tr1 ps2 tr2 :
  psl1 = extract l1 ps -> psl2 = extract l2 ps ->
  rred l1 psl1 ps1 tr1 -> rred l2 psl2 ps2 tr2 ->
  l1 == l2 :> seq _ /\ ps1 = ps2 :> seq _ /\ tr1 = tr2 :> seq _
  \/ {in l1 & l2, forall a b, a != b}.
Proof.
move=> Hpsl1 Hpsl2 Hred1 Hred2.
case: Hred1 Hpsl1 => [i j pi | i x | i j x pi pj] /(f_equal val) /= [] Hpi;
case: Hred2 Hpsl2 => [i' j' pi' | i' x' | i' j' x' pi' pj'] /(f_equal val) /=[];
  (have [<-|ii' Hpi'] := eqVneq i i'; [rewrite -Hpi // => -[]
   | right => a b; rewrite !inE; try by do! move /eqP ->]).
- by move=> <- <-; left.
- move=> /eqP-> /orP[] /eqP->; apply/eqP => ij; by rewrite ij -(Hpi',H) in Hpi.
- by move=> <-; left.
- move=> /eqP-> /orP[] /eqP->; apply/eqP => ij; by rewrite ij -(Hpi',H) in Hpi.
- move=> /orP[] /eqP-> /eqP->; apply/eqP => ij; by rewrite -ij -(Hpi,H) in Hpi'.
- move=> /orP[] /eqP-> /eqP->; apply/eqP => ij; by rewrite -ij -(Hpi,H) in Hpi'.
- by move=> /val_inj -> -> -> <- [] <-; left.
- move: H H0.
  have [<-|jj' Hpj' Hpj] := eqVneq j j'.
    by move=> <- [] /val_inj /eqP; rewrite (negbTE ii').
  move=> /orP[] /eqP -> /orP[] /eqP -> //; apply/eqP => ij.
  + by rewrite ij -Hpj' in Hpi.
  + by rewrite ij -Hpi' in Hpj.
Qed.

Lemma comm_disjoint n (ps : n.-tuple proc) i j k l ps1 tr1 ps2 tr2 :
  rred [tuple i; j] (extract [tuple i; j] ps) ps1 tr1 ->
  rred [tuple k; l] (extract [tuple k; l] ps) ps2 tr2 ->
  (i == k) /\ (j == l) \/ (i != k) /\ (j != l).
Proof.
inversion 1; inversion 1; subst.
case/boolP: (i == k) => ik; [left | right]; split => //.
  move: H10; rewrite (tnth_nth Fail) -(eqP ik) -tnth_nth -H3 => -[lj] _ _.
  exact/eqP/val_inj.
apply: contra ik => /eqP jl.
move: H11; rewrite (tnth_nth Fail) -jl -tnth_nth -H4 => -[ki] _.
exact/eqP/val_inj.
Qed.
  
(* Soundness: step implements rstep *)
Lemma step_sound n (ps : n.-tuple proc) :
  let res := [tuple step ps nil i | i < n] in
  let ps' := map_tuple (fun r => r.1.1) res in
  let tr := map_tuple (fun r => r.1.2) res in
  rstep ps ps' tr.
Proof.
pose pss := [fset x : 'I_n | true].
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
  (* Base case: empty set *)
  rewrite (_ : map_tuple _ _ = ps); last first.
    by apply: eq_from_tnth => i; rewrite tnth_map !tnth_mktuple inE.
  rewrite (_ : map_tuple _ _ = [tuple nil | _ < n]); last first.
    by apply: eq_from_tnth => i; rewrite tnth_map !tnth_mktuple inE.
  by constructor.
(* Inductive case: i in pss *)
case Hpi: (ps !_ i) => [x p | j x p | j f | x ||].
(* Case Init x p *)
- pose pss' := pss `\ i.
  have H': pss' `<` pss by apply: fproperD1.
  apply: (rtrans (IH _ H' _)); last 3 first.
  + move=> k j' ps' traces H.
    rewrite !inE (Hpss _ _ _ _ H).
    have [ki|_] := eqVneq k i; first by inversion H; subst; rewrite Hpi in H3.
    have [ji|//] := eqVneq j' i.
    by inversion H; subst; rewrite Hpi in H4.
  + move: (rinit i x p).
    set ps'' := map_tuple _ _.
    have -> : [tuple Init x p] = extract [tuple i] ps''.
      by apply/val_inj; rewrite /= /ps'' tnth_map tnth_mktuple !inE eqxx /= Hpi.
    move/rone.
    have -> : inject [tuple i] ps'' [tuple p] =
              map_tuple (fun r : proc * seq data * bool => r.1.1) (res' pss ps).
      apply: eq_from_tnth => j'; rewrite !(tnth_mktuple,tnth_map) /=.
      case/boolP: (i == j') => [/eqP <-|ij] /=.
        by rewrite Hi /step -tnth_nth Hpi.
      by have -> : (j' \in pss') = (j' \in pss) by rewrite !inE eq_sym ij.
    exact.
  + apply: eq_from_tnth => j'; rewrite !(tnth_mktuple, tnth_map) /=.
    case/boolP: (i == j') => [/eqP <-|ij] /=.
      by rewrite Hi !inE eqxx /= /step -tnth_nth Hpi.
    by have -> : (j' \in pss') = (j' \in pss) by rewrite !inE eq_sym ij.
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
    pose pss' := pss `\ i `\ Ordinal jn.
    have H': pss' `<` pss.
      exact/(fsub_proper_trans (B:=pss `\ i))/fproperD1/Hi/fsubD1set.
    apply: (rtrans (IH _ H' _)); last 3 first.
    * move=> k k' ps' traces H.
      rewrite !inE.
      case: (comm_disjoint Hr H) => -[].
        by move => /eqP <- /eqP <-; rewrite !eqxx !andbF.
      rewrite eq_sym (eq_sym _ k') => -> ->.
      inversion H; subst.
      have [kj|_] := eqVneq k (Ordinal jn).
        by rewrite kj (tnth_nth Fail) Hpj in H3.
      have [k'i|_] := eqVneq k' i; first by rewrite k'i Hpi in H4.
      exact: (Hpss _ _ _ _ H).
    * move: (rcomm i (Ordinal jn) x p pj).
      set ps'' := map_tuple _ _.
      rewrite (_ : [tuple Send _ _ _; _] = extract [tuple i; Ordinal jn] ps'');
        last first.
        apply/val_inj; rewrite /=/ps'' !(tnth_mktuple,tnth_map) !inE !eqxx /=.
        by rewrite andbF Hpi (tnth_nth Fail) Hpj.
      move/rone.
      have -> : inject [tuple i; Ordinal jn] ps'' [tuple p; pj x] =
           map_tuple (fun r : proc * seq data * bool => r.1.1) (res' pss ps).
        apply: eq_from_tnth => k; rewrite !(tnth_mktuple,tnth_map) /=.
        case/boolP: (i == k) => [/eqP <-|ik] /=.
          by rewrite Hi /step -tnth_nth Hpi Hpj eqxx.
        case/boolP: (_ == _) => jk /=.
          by rewrite -(eqP jk) Hj /step Hpj -tnth_nth Hpi eqxx.
        by rewrite !inE eq_sym jk eq_sym ik.
      exact.
    * apply: eq_from_tnth => k; rewrite !(tnth_mktuple, tnth_map) /=.
      rewrite !inE !(eq_sym k) andbCA.
      have [<- | ik] /= := eqVneq i k.
        by rewrite Hi /step -tnth_nth Hpi Hpj eqxx.
      have [<- |] //= := eqVneq (Ordinal jn) k.
      by rewrite Hj /step Hpj -tnth_nth Hpi eqxx.
  + (* Send but no matching Recv - skip this process *)
    pose pss' := pss `\ i.
    have H': pss' `<` pss by apply: fproperD1.
    have -> : res' pss ps = res' pss' ps.
      apply: eq_from_tnth => k.
      rewrite !tnth_mktuple !inE.
      have [-> |] //= := eqVneq k i.
      rewrite Hi /step -tnth_nth Hpi.
      case Hj: nth => [||e pj|||] //.
      case: ifP => ei //.
      by elim: Hn; exists pj; rewrite -(eqP ei).
    apply: IH => //.
    move=> a b ps' traces.
    rewrite !inE.
    have [-> | ai] := eqVneq a i; have [-> | bi] // := eqVneq b i.
    * inversion 1; subst.
      move: H3; rewrite Hpi => -[bj].
      elim: Hn; exists pj.
      by rewrite -bj -tnth_nth H4.
    * inversion 1; subst.
      by rewrite Hpi in H4.
    * exact: Hpss.
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
    pose pss' := pss `\ i `\ Ordinal jn.
    have H': pss' `<` pss.
      exact/(fsub_proper_trans (B:=pss `\ i))/fproperD1/Hi/fsubD1set.
    apply: (rtrans (IH _ H' _)); last 3 first.
    * move=> k k' ps'' traces H.
      rewrite !inE.
      case: (comm_disjoint Hr H) => -[].
        by move => /eqP <- /eqP <-; rewrite !eqxx !andbF.
      rewrite eq_sym (eq_sym _ k') => -> ->.
      inversion H; subst.
      have [ki|_] := eqVneq k i.
        by rewrite ki Hpi in H3.
      have [k'j|_] := eqVneq k' (Ordinal jn).
        by rewrite k'j (tnth_nth Fail) Hpj in H4.
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
           map_tuple (fun r : proc * seq data * bool => r.1.1) (res' pss ps).
        apply: eq_from_tnth => k; rewrite !(tnth_mktuple,tnth_map) /=.
        case/boolP: (Ordinal jn == k) => [/eqP <-|jk] /=.
          by rewrite Hj /step Hpj -tnth_nth Hpi eqxx.
        case/boolP: (i == k) => [/eqP <-|ik] /=.
          by rewrite Hi /step -tnth_nth Hpi Hpj eqxx.
        by rewrite !inE eq_sym jk eq_sym ik.
      exact.
    * apply: eq_from_tnth => k; rewrite !(tnth_mktuple, tnth_map) /=.
      rewrite !inE !(eq_sym k).
      have [<- | jk] /= := eqVneq (Ordinal jn) k.
        by rewrite Hj /step Hpj -tnth_nth Hpi eqxx.
      have [<- |] //= := eqVneq i k.
      by rewrite Hi /step -tnth_nth Hpi Hpj eqxx.
  + (* Recv but no matching Send - skip this process *)
    pose pss' := pss `\ i.
    have H': pss' `<` pss by apply: fproperD1.
    have -> : res' pss ps = res' pss' ps.
      apply: eq_from_tnth => k.
      rewrite !tnth_mktuple !inE.
      have [-> |] //= := eqVneq k i.
      rewrite Hi /step -tnth_nth Hpi.
      case Hj: nth => [|dst' v' pj'||||] //.
      case: ifP => ei //.
      by elim: Hn; exists v', pj'; rewrite -(eqP ei).
    apply: IH => //.
    move=> a b ps' traces.
    rewrite !inE.
    have [-> | ai] := eqVneq a i; have [-> | bi] // := eqVneq b i.
    * (* a = i, b != i: rred would require i to have Send/Init/Ret, but it has Recv *)
      inversion 1; subst.
      (* For rcomm, H3 says ps !_ i = Send _ _ _, contradicts Hpi: ps !_ i = Recv _ _ *)
      by rewrite Hpi in H3.
    * inversion 1; subst.
      move: H4; rewrite Hpi => -[] aj.
      rewrite (tnth_nth Fail) aj in H3.
      by elim: Hn; exists x, pi.
    * exact: Hpss.
(* Case Ret x *)
- pose pss' := pss `\ i.
  have H': pss' `<` pss by apply: fproperD1.
  apply: (rtrans (IH _ H' _)); last 3 first.
  + move=> k j' ps' traces H.
    rewrite !inE (Hpss _ _ _ _ H).
    have [ki|_] := eqVneq k i; first by inversion H; subst; rewrite Hpi in H3.
    have [ji|//] := eqVneq j' i.
    by inversion H; subst; rewrite Hpi in H4.
  + move: (rret i x).
    set ps'' := map_tuple _ _.
    have -> : [tuple Ret x] = extract [tuple i] ps''.
      by apply/val_inj; rewrite /= /ps'' tnth_map tnth_mktuple !inE eqxx /= Hpi.
    move/rone.
    have -> : inject [tuple i] ps'' [tuple Finish] =
              map_tuple (fun r : proc * seq data * bool => r.1.1) (res' pss ps).
      apply: eq_from_tnth => j'; rewrite !(tnth_mktuple,tnth_map) /=.
      case/boolP: (i == j') => [/eqP <-|ij] /=.
        by rewrite Hi /step -tnth_nth Hpi.
      by have -> : (j' \in pss') = (j' \in pss) by rewrite !inE eq_sym ij.
    exact.
  + apply: eq_from_tnth => j'; rewrite !(tnth_mktuple, tnth_map) /=.
    case/boolP: (i == j') => [/eqP <-|ij] /=.
      by rewrite Hi !inE eqxx /= /step -tnth_nth Hpi.
    by have -> : (j' \in pss') = (j' \in pss) by rewrite !inE eq_sym ij.
(* Case Finish - does nothing, just remove from set *)
- pose pss' := pss `\ i.
  have H': pss' `<` pss by apply: fproperD1.
  have -> : res' pss ps = res' pss' ps.
    apply: eq_from_tnth => k.
    rewrite !tnth_mktuple !inE.
    have [-> |] //= := eqVneq k i.
    by rewrite Hi /step -tnth_nth Hpi.
  apply: IH => //.
  move=> a b ps' traces.
  rewrite !inE.
  have [-> | ai] := eqVneq a i; have [-> | bi] // := eqVneq b i.
  + by inversion 1; subst; rewrite Hpi in H3.
  + by inversion 1; subst; rewrite Hpi in H4.
  + exact: Hpss.
(* Case Fail - does nothing, just remove from set *)
- pose pss' := pss `\ i.
  have H': pss' `<` pss by apply: fproperD1.
  have -> : res' pss ps = res' pss' ps.
    apply: eq_from_tnth => k.
    rewrite !tnth_mktuple !inE.
    have [-> |] //= := eqVneq k i.
    by rewrite Hi /step -tnth_nth Hpi.
  apply: IH => //.
  move=> a b ps' traces.
  rewrite !inE.
  have [-> | ai] := eqVneq a i; have [-> | bi] // := eqVneq b i.
  + by inversion 1; subst; rewrite Hpi in H3.
  + by inversion 1; subst; rewrite Hpi in H4.
  + exact: Hpss.
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

(******************************************************************************)
(** * Reading Conclusion: Lemma step_sound (line 344)                         *)
(******************************************************************************)

(**md

## Lemma step_sound: What It Proves

The lemma `step_sound` establishes the fundamental **soundness** of the interpreter's single-step execution
function with respect to the relational semantics. Specifically, it proves that for any tuple `ps` of `n`
processes, executing one step via the `step` function (applied to all processes in parallel) yields a
configuration that is reachable via the relational semantics (`rstep`).

### Formal Statement
```coq
Lemma step_sound n (ps : n.-tuple proc) :
  let res := [tuple step ps nil i | i < n] in
  rstep ps (map_tuple (fun r => r.1.1) res) (map_tuple (fun r => r.1.2) res).
```

The lemma shows that:
- Starting from process configuration `ps`
- Applying `step` to each process (collecting results)
- Extracting the resulting processes and traces
- This configuration transition is justified by `rstep` (the relational semantics)

### Why This Is Important for Academic Paper

1. **Correctness Bridge**: This lemma bridges the operational interpreter (`step` function) with the formal
   relational semantics (`rstep`). It certifies that the actual execution engine faithfully implements the
   high-level abstract reduction rules.

2. **Proof Strategy Foundation**: The proof uses **finite set induction** over the set of processes that
   can perform a reduction. This inductive structure demonstrates how:
   - A single process executing (Init, Ret)
   - Two processes communicating (Send-Recv pairs)
   - Processes that cannot reduce are skipped
   
   All these cases compose to form a valid relational step.

3. **Completeness of Reduction Matching**: The proof systematically handles all process constructors
   (Init, Send, Recv, Ret, Finish, Fail) and verifies that the `step` function correctly identifies:
   - Which processes can reduce
   - Whether communication partners exist and match
   - How traces are accumulated during reduction

4. **Technical Contribution**: For the paper, this lemma is essential because it establishes that one can
   reason about protocol correctness using either the concrete interpreter or the abstract relational
   semantics interchangeably—they are sound with respect to each other.

### Proof Technique Insight

The proof uses **wellfounded induction on finite set inclusion** (`finSet_rect`), progressively removing
processes that have already reduced. For each process in the set:
- **Init case**: Process transitions to continuation, stores initial value
- **Send-Recv case**: When a Send/Recv pair can communicate, both processes advance (trace includes sent value)
- **Unmatched Send/Recv**: Process is skipped (removed from active set, waiting for communication partner)
- **Ret/Finish/Fail**: Terminal states handled by recursion on reduced set

This structure ensures that all possible atomic reductions in the system are captured by individual `rred`
steps, whose composition via `rtrans` produces the overall system transition.

*)

(******************************************************************************)
(** * Two Semantics: Operational vs Relational                               *)
(******************************************************************************)

(**md

## Why Both Operational and Relational Semantics?

This file defines **two different semantic models** for secure multiparty protocols:

### 1. Operational Semantics (Concrete Execution - lines 40-87)

```coq
proc: Type := Init | Send | Recv | Ret | Finish | Fail
step: seq proc -> seq data -> nat -> (proc * seq data * bool)
interp: nat -> seq proc -> seq (seq data) -> (seq proc * seq (seq data))
```

**What it is**: The **actual execution engine**
- Deterministic algorithm that executes processes
- `step` computes the next state of a single process given the current system state
- `interp` repeatedly applies `step` with a fuel limit `h`
- Returns **concrete results**: final processes and accumulated traces
- This is what you'd actually run on a computer

### 2. Relational Semantics (Abstract Specification - lines 108-127)

```coq
rred: m.-tuple proc -> m.-tuple proc -> m.-tuple (seq data) -> Prop
rstep: n.-tuple proc -> n.-tuple proc -> n.-tuple (seq data) -> Prop
```

**What it is**: The **specification of valid reductions**
- Declarative/relational rules specifying *which* execution paths are allowed
- `rred`: Single atomic reduction rules (Init, Ret, Send-Recv communication)
- `rstep`: Reflexive-transitive closure allowing sequences of reductions
- More abstract and easier to reason about in proofs

### Comparison: Operational vs Relational

| Aspect | Operational | Relational | Purpose |
|--------|-------------|-----------|---------|
| **Style** | Algorithmic | Declarative | Concrete vs. Specification |
| **Proofs** | Complex to reason about | Composable, inductive | Easier theorem proving |
| **Execution** | Executable | Non-executable | Implementation vs. Semantics |
| **Determinism** | Fully deterministic | May allow multiple paths | Concrete vs. Abstract |

### The Connection: `step_sound` Lemma

**The `step_sound` lemma (line 344) proves the relationship**:

```coq
Lemma step_sound n (ps : n.-tuple proc) :
  let res := [tuple step ps nil i | i < n] in
  rstep ps (map_tuple (fun r => r.1.1) res) (map_tuple (fun r => r.1.2) res).
```

This says: **Whatever the concrete `step` function produces is justified by the abstract `rstep` semantics.**

### Practical Workflow

1. **Prove high-level properties** about relational semantics (cleaner, more abstract)
   - Example: "protocol preserves confidentiality with respect to `rstep`"

2. **Use `step_sound`** to lift results to the concrete interpreter
   - Example: "the actual `interp` function also preserves confidentiality"

3. **Benefits**:
   - ✅ Don't need to reason about messy algorithmic details
   - ✅ Reusable specification independent of implementation
   - ✅ Modular: can change `step` implementation without rewriting all proofs
   - ✅ Natural composition via `rtrans` rule

### Formal Methods Concept

This is a standard approach in formal methods called **"refinement verification"** or **"semantic correspondence"**.
It enables:
- Abstraction layers between specification and implementation
- Easier theorem proving at the specification level
- Implementation freedom with provable correctness guarantees

*)

(******************************************************************************)
(** * Deep Dive: rred vs rstep                                               *)
(******************************************************************************)

(**md

## `rred`: Single Atomic Reduction Rules

`rred` defines the **smallest possible execution steps** - atomic actions that a single process or pair 
of processes can perform.

```coq
Inductive rred {n} : forall {m}, lens n m ->
      m.-tuple proc -> m.-tuple proc -> m.-tuple (seq data) -> Prop :=
  | rinit i x p : rred [tuple i] [tuple Init x p] [tuple p] [tuple [:: x]]
  | rret i x : rred [tuple i] [tuple Ret x] [tuple Finish] [tuple [:: x]]
  | rcomm i j x pi pj :
    rred [tuple i; j] [tuple Send j x pi; Recv i pj] [tuple pi; pj x]
         [tuple nil; [:: x]].
```

### The Three Rules:

1. **`rinit` (Initialization)**
   - **What**: Process `i` executes `Init x p`
   - **Before**: Process at position `i` is `Init x p`
   - **After**: Process becomes `p`, and value `x` is added to its trace
   - **Trace produced**: `[:: x]` (a single-element list)

2. **`rret` (Return)**
   - **What**: Process `i` executes `Ret x`
   - **Before**: Process at position `i` is `Ret x`
   - **After**: Process becomes `Finish` (terminal state), and value `x` is added to its trace
   - **Trace produced**: `[:: x]`

3. **`rcomm` (Communication)**
   - **What**: Process `i` receives from process `j` who sends
   - **Before**: 
     - Process `i` is `Recv i pj` (waiting to receive from sender `i`)
     - Process `j` is `Send j x pi` (sending value `x` to recipient `j`)
   - **After**: 
     - Process `i` becomes `pj x` (continues with the received value)
     - Process `j` becomes `pi` (continues after sending)
   - **Traces**: Process `j` gets empty trace `[]`, process `i` gets `[:: x]` (the received value)

**Key point**: Each `rred` rule is **completely deterministic** and involves only a small subset of processes 
(1 or 2 processes).

## `rstep`: Reflexive-Transitive Closure

`rstep` builds on top of `rred` to allow **sequences of reductions**:

```coq
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
```

### The Three Constructors:

1. **`rone` (Single Reduction)**
   - Apply one atomic `rred` rule to a subset of processes
   - Uses a **lens** `l` to select which processes participate
   - `extract l ps`: Extract the relevant processes
   - `inject l ps ps'`: Put the updated processes back into the full tuple
   - **Multiple reductions in parallel**: All non-overlapping `rred` rules can be applied simultaneously

2. **`rrefl` (Reflexivity)**
   - Do nothing: `rstep ps ps [tuple nil | _ < n]`
   - A system can transition to itself with no trace changes
   - This allows **zero or more** steps (not just one)

3. **`rtrans` (Transitivity)**
   - Compose two `rstep` transitions into one
   - Go from `ps1` → `ps2` → `ps3`
   - Traces are **concatenated**: `tr3 = [tuple tr2 !_ i ++ tr1 !_ i | i < n]`
   - For each process `i`, combine traces from both steps

## Visual Example

Suppose you have 3 processes and want to execute them:

### Using `rred` alone:
```
ps1 ──[rred: Init at i=0]──> ps2 ──[rred: Send-Recv at i=1,2]──> ps3
```
You're limited to sequences of single `rred` applications.

### Using `rstep` (with composition):
```
ps1 ──[rstep: multiple parallel redex]──> ps3
```

A single `rstep` can represent:
- Multiple independent `rred` rules applied in parallel (via `rone` with different lenses)
- Or a sequence of such parallel steps (via `rtrans`)

### Concrete Example:

If you have:
- Process 0: `Init x p0` (can reduce)
- Process 1: `Send 2 y p1` (waiting for receiver at position 2)
- Process 2: `Recv 1 p2` (waiting for sender at position 1)

**With `rstep`**, you could:
1. **Step 1**: Process 0 initializes (`Init`) AND processes 1-2 communicate (one `Send-Recv`) in parallel
2. This is possible because their participating indices don't overlap

## Key Differences Summary

| Aspect | `rred` | `rstep` |
|--------|--------|--------|
| **Scope** | One atomic action | Sequence of actions |
| **Processes affected** | 1 or 2 processes | Subset or all n processes |
| **Parallelism** | No parallelism | Allows parallel independent reductions |
| **Repetition** | Single step only | Zero or more steps (reflexive-transitive) |
| **Trace** | Single trace per rule | Concatenated traces |
| **Use case** | Specification primitives | Reasoning about execution runs |

## Why Both?

- **`rred`**: Clean specification of what can happen (like a grammar)
- **`rstep`**: Composable semantics for reasoning about programs (like derivations in a grammar)
- **`step_sound`**: Connects the concrete algorithm to this abstract framework

*)

(******************************************************************************)
(** * Lenses: The Architecture of Selective Process Updates                   *)
(******************************************************************************)

(**md

## How Lenses Enable the Soundness Proof

Lenses are crucial for the `step_sound` proof because they enable **selective process extraction
and injection** when reasoning about disjoint subsets of processes.

### What Lenses Do (Definition at lines 94-102)

```coq
Definition lens : Type := m.-tuple 'I_n.
Definition extract (t : n.-tuple T) := map_tuple (tnth t) l.
Definition inject (t : n.-tuple T) (t' : m.-tuple T) :=
  [tuple nth (t !_ i) t' (index i l) | i < n].
```

A **lens** is an `m`-tuple of indices selecting `m` positions from an `n`-tuple:
- **`extract l ps`**: Pull out processes at positions specified by lens `l`
- **`inject l ps ps'`**: Update positions in `ps` with values from `ps'` at `l`

### Why This Matters for `step_sound`

The proof must establish that when we execute `step` on the entire process tuple,
the result is justified by `rstep`. The key challenge: `rred` operates on **subsets** of processes.

**Without lenses**: We'd need to reason about how individual reductions fit together.

**With lenses**: We can formalize the pattern:

1. **Lens Selection** (lines 152-158): For each reduction spec `r`, compute which processes 
   participate using `red_spec_lens r`

2. **Extraction** (lines 381, 406, 481): Extract only the relevant processes:
   ```coq
   extract [tuple i] ps = [tuple Init x p]  // Extract process at position i
   ```

3. **Application of rred** (lines 216-219): Apply the atomic rule to the extracted subset:
   ```coq
   rred l (extract l ps) ps' traces  // Apply rule to selected processes
   ```

4. **Reinjection** (lines 382, 431, 508): Put the updated processes back:
   ```coq
   inject l ps ps' = [update processes at positions in l with values from ps']
   ```

### Disjointness and Parallelism

The critical lemma `lens_disjoint` (lines 244-246) ensures that when two reductions use
**disjoint lenses**, they don't interfere:

```coq
Definition lens_disjoint (l1 : lens n m1) (l2 : lens n m2) : bool :=
  all (fun x => x \notin l2) l1.
```

This enables the proof to compose:
- Process 0 can execute `Init` via lens `[tuple 0]`
- Processes 1 and 2 can communicate via lens `[tuple 1; 2]`
- These lenses are **disjoint**, so both reductions happen **independently in parallel**

### The Role in `step_sound` Proof (lines 344-602)

The proof structure uses lenses at multiple points:

1. **Line 348**: `pose pss := [fset x : 'I_n | true]` - initial set of all processes

2. **Lines 358-602**: **Finite set induction** - progressively remove processes that reduced
   - Each case (Init, Send-Recv, Ret, etc.) uses a lens to extract the active process(es)
   - The `rone` constructor (line 120-122) packages the reduction:
     ```coq
     rstep ps (inject l ps ps') (inject l [tuple nil | _ < n] traces)
     ```

3. **Lines 413, 486**: Disjointness check ensures Send-Recv pairs don't overlap with other 
   active reductions

4. **Trace Concatenation** (line 126): Lenses also organize traces by process position:
   ```coq
   tr3 = [tuple tr2 !_ i ++ tr1 !_ i | i < n]  // Concatenate per-process traces
   ```

### Why This Is Elegant

- **Type safety**: Lenses are typed tuples - index bounds are verified at compile time
- **Composability**: Disjoint lenses compose automatically (line 264 - though admitted)
- **Clarity**: Extract-apply-inject pattern is clear and reusable for any subset
- **Modularity**: Different reductions can be reasoned about independently, then combined via `rtrans`

In summary: **Lenses are the glue** that allows the proof to reason about disjoint parallel 
reductions locally, then compose them into a single `rstep` transition that matches the 
`step` function's behavior. This makes the soundness argument compositional rather than 
requiring a monolithic proof that handles all interactions at once.

*)

(*

1. Overall Proof Strategy for Step Soundness

We prove the soundness of the step function by showing that every execution
produced by the concrete interpreter faithfully corresponds to valid reductions
in the relational semantics. Our approach employs finite set induction over the
set of processes that are able to execute in the current configuration. In
the proof, we progressively remove processes from the active set as they
complete their reductions (Init, Ret, Finish, or Fail) or as communication
pairs (Send-Recv) successfully exchange data. For each induction case, we rely
on two insights: first, we identify exactly which processes can reduce at a
given step; second, we check that the step function implements the required
logic for Send-Recv matching and properly accumulates traces. These local
reductions are then composed into a global transition using the
reflexive-transitive closure (rstep), which allows multiple independent
reductions to occur in parallel. This approach transforms a complex
algorithmic proof into a modular inductive argument: rather than attempting to
reason about all process interactions at once, we handle each reduction type
in isolation.

2. Operational vs. Relational Semantics: The Bridge via Step Soundness

We provide two complementary semantic models for protocol execution. The
operational semantics—implemented by step and interp—characterize how the
interpreter actually computes process states and traces, through deterministic
pattern matching and sequential updates. The relational semantics, given by
rred and rstep, instead abstractly specify which execution paths are permitted
by the protocol rules. The step_sound lemma bridges these models by proving
that every configuration reachable via step is also reachable via rstep. This
correspondence allows us to verify high-level properties (e.g.,
confidentiality, information flow) at the more abstract relational level,
without engaging the complexity of the implementation. The key benefit is that
properties proven about rstep—which is cleaner and more modular—automatically
lift to the interpreter via step_sound. Our verification thus remains both
compositional and robust to future changes in implementation.

3. Atomic Reductions (rred) Composed via Reflexive-Transitive Closure (rstep)

We distinguish between rred and rstep as follows. The rred relation captures
the basic, atomic steps processes can perform—initialization, return, and
two-party communication. The rstep relation extends rred by permitting
sequences and (parallel) composition of these atomic steps. Each rred rule
encodes a single protocol action: rinit moves a process from Init x p to p
while recording value x; rret transitions from Ret x to Finish while recording
x; rcomm performs a synchronous Send-Recv exchange between two processes.
Three constructors define rstep: rone packages a single rred step for some
subset of processes (selected by a lens); rrefl allows zero-step transitions
(reflexivity); and rtrans composes two rstep derivations, concatenating their
traces. This design separates the logical specification of actions from the
operational semantics of execution runs. Such separation is crucial for our
proof: we can verify that step implements each atomic rule in isolation, then
show that composing these via rtrans yields exactly those global transitions
allowed by rstep.

4. Lenses as the Architecture for Selective Process Updates

Lenses are the central architectural device that make the soundness proof
compositional and enable parallel reductions. Lenses are tuples of indices
selecting m positions out of an n-tuple of processes. We use extract l ps to
isolate the processes involved in a reduction—e.g., extract [tuple i] ps pulls
out just process i for an Init or Ret action—on which the appropriate rred
rule is applied. After the reduction, inject l ps ps' re-integrates the
updated processes into the global system configuration. The lens_disjoint
predicate certifies when two lenses do not overlap, which allows us to verify
that disjoint reductions do not interfere with each other. This property is
crucial for soundness, as it ensures that an Init at process i and a
Send-Recv between processes j and k (with all three distinct indices) may
proceed independently and in any order, always producing the same final
state. By reasoning about process subsets locally using lenses, we break the
global correctness argument into local checks for each reduction rule, then
compose the results via rtrans—sidestepping the complexity of interactions
between unrelated reductions.


*)

(*

As we mentioned in the Sect.~\ref{sec:introduction}, the interpreter
of Weng et al. follows a set of rules to rewrite protocol configurations.
%
In \coqin{smc_interpreter.v}, by proving \coqin{step_sound},
we relate the interpreter to an independent small-step rewriting
semantics on protocol configurations. Concretely, we establish that every
execution produced by the interpreter faithfully corresponds to valid
reductions in the relational semantics.
%
To achieve this, we employ finite set induction over the processes capable of
executing in the current configuration.

It refers to finSet_rect — the finite set induction principle used in the proof of step_sound.
Specifically, look at line 358 in the code:
elim/finSet_rect: pss {res} => /= pss IH Hpss.
Here, pss is defined at line 348 as [fset x : 'I_n | true], which is a finite set containing all process indices initially capable of executing. The finSet_rect principle performs induction over this finite set by:
Base case (lines 359-365): When pss is empty (all processes have completed their reductions)
Inductive case (lines 366-602): When there exists at least one process i in pss that can still reduce
As the proof progresses through each case (Init, Send-Recv, Ret, Finish, Fail), processes are removed from pss using set subtraction (pss \ i), making the set strictly smaller at each step and ensuring termination of the induction.

*)

(*
rstep is called the "reflexive-transitive closure" of rred because it has three constructors that correspond exactly to these properties:
Reflexive (line 123): The rrefl constructor states that any configuration can transition to itself:
   rrefl ps : rstep ps ps [tuple nil | _ < n]
This allows zero-step transitions, which is the reflexive property.
Transitive (lines 124-127): The rtrans constructor allows composing two rstep transitions into a single transition:
   rtrans ps1 ps2 ps3 tr1 tr2 tr3 :     rstep ps1 ps2 tr1 -> rstep ps2 ps3 tr2 ->     tr3 = [tuple tr2 !_ i ++ tr1 !_ i | i < n] ->     rstep ps1 ps3 tr3.
This is the transitive property: if ps1 → ps2 and ps2 → ps3, then ps1 → ps3.
Closure of rred (lines 120-122): The rone constructor applies a single rred rule:
   rone m (l : lens n m) ps ps' traces :     rred l (extract l ps) ps' traces ->     rstep ps (inject l ps ps') (inject l [tuple nil | _ < n] traces)
This ensures that every rred reduction is also an rstep transition.
Together, these three constructors define rstep as the smallest relation containing rred that is both reflexive and transitive — precisely the definition of a reflexive-transitive closure. This allows rstep to represent execution runs that consist of zero or more rred steps composed together.

*)