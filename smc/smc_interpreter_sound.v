From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg ring.
From mathcomp Require Import reals finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import smc_interpreter.

(**md**************************************************************************)
(* # Soundness of the SMC Interpreter                                         *)
(*                                                                            *)
(* Proves that the functional interpreter (step mapped over all parties)       *)
(* is simulated by the relational semantics (rsteps).                         *)
(*                                                                            *)
(* Design: The SMC language has 6 constructors (Init, Send, Recv, Ret,        *)
(* Finish, Fail), but from the interpreter's perspective only two things      *)
(* happen at each index: a reduction fires or nothing happens.                *)
(* We introduce red_spec (3 constructors) to canonically package reductions,  *)
(* then index_class (2 constructors: Inert, Disjoint) to classify each index. *)
(* The 6→3→2 collapse eliminates the case explosion and Send/Recv symmetry.   *)
(*                                                                            *)
(* The key property enabling composition is rstep_disjoint: any two fireable  *)
(* reductions from the same state are either identical or touch disjoint       *)
(* indices. This replaces the ad-hoc comm_closed invariant.                   *)
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

Section sound.
Variable data : Type.

Local Open Scope tuple_ext_scope.
Local Open Scope fset_scope.

(******************************************************************************)
(* Reduction specifications                                                    *)
(*                                                                            *)
(* The proc type has 6 constructors, but only 3 kinds of reductions:          *)
(*   RSinit  — 1-party: Init(d,k) steps to k, emitting d                     *)
(*   RSret   — 1-party: Ret(d) steps to Finish, emitting d                   *)
(*   RScomm  — 2-party: matched Send/Recv pair exchanges data                 *)
(* The remaining constructors (Finish, Fail, unmatched Send/Recv) are inert.  *)
(*                                                                            *)
(* red_spec packages the lens, inputs, outputs, and traces for each kind.     *)
(* red_spec_at examines the process at index i and its partner (if Send/Recv) *)
(* to find the applicable reduction, returning None for inert indices.        *)
(* This absorbs the partner-searching logic that would otherwise appear       *)
(* inline in step_sound's Send and Recv branches.                             *)
(*                                                                            *)
(* Key property: red_spec_at canonicalizes Send/Recv into a single RScomm     *)
(* (sender-first), eliminating the symmetry duplication where a naive proof   *)
(* handles Send-then-find-Recv and Recv-then-find-Send separately.            *)
(******************************************************************************)

Inductive red_spec n : Type :=
  | RSinit (i : 'I_n) (x : data) (p : proc data)
  | RSret (i : 'I_n) (x : data)
  | RScomm (i j : 'I_n) (x : data) (pi : proc data)
           (pj : data -> proc data).

Arguments RSinit {n}.
Arguments RSret {n}.
Arguments RScomm {n}.

(* Size of a reduction's index set *)
Definition red_spec_size {n} (r : red_spec n) : nat :=
  match r with
  | RSinit _ _ _ | RSret _ _ => 1
  | RScomm _ _ _ _ _ => 2
  end.

(* Lens for a reduction (indices as a tuple) — primary definition *)
Definition red_spec_lens {n} (r : red_spec n) :
    lens n (red_spec_size r) :=
  match r return lens n (red_spec_size r) with
  | RSinit i _ _ => [tuple i]
  | RSret i _ => [tuple i]
  | RScomm i j _ _ _ => [tuple i; j]
  end.

(* Indices involved in a reduction — derived from lens via coercion *)
Definition red_spec_indices {n} (r : red_spec n) : seq 'I_n :=
  tval (red_spec_lens r).

(* Input processes — what the reduction expects *)
Definition red_spec_input {n} (r : red_spec n) :
    (red_spec_size r).-tuple (proc data) :=
  match r return (red_spec_size r).-tuple (proc data) with
  | RSinit _ x p => [tuple Init x p]
  | RSret _ x => [tuple Ret x]
  | RScomm i j x pi pj =>
      [tuple Send (nat_of_ord j) x pi; Recv (nat_of_ord i) pj]
  end.

(* Output processes — what the reduction produces *)
Definition red_spec_output {n} (r : red_spec n) :
    (red_spec_size r).-tuple (proc data) :=
  match r return (red_spec_size r).-tuple (proc data) with
  | RSinit _ _ p => [tuple p]
  | RSret _ _ => [tuple Finish]
  | RScomm _ _ x pi pj => [tuple pi; pj x]
  end.

(* Output traces — data emitted by the reduction *)
Definition red_spec_traces {n} (r : red_spec n) :
    (red_spec_size r).-tuple (seq data) :=
  match r return (red_spec_size r).-tuple (seq data) with
  | RSinit _ x _ => [tuple [:: x]]
  | RSret _ x => [tuple [:: x]]
  | RScomm _ _ x _ _ => [tuple nil; [:: x]]
  end.

(* Every red_spec is a valid rstep. Immediate by construction:
   each variant directly corresponds to an rstep constructor. *)
Lemma red_spec_valid n (r : red_spec n) :
  rstep (red_spec_lens r) (red_spec_input r) (red_spec_output r)
       (red_spec_traces r).
Proof. by case: r => *; constructor. Qed.

(* red_spec_at: find the applicable reduction at index i.
   For Send j x p, looks up ps[j] for matching Recv — this is the
   partner-search logic, done once here instead of inline in step_sound.
   For Recv j f, looks up ps[j] for matching Send — same RScomm,
   canonical sender-first, eliminating the Send/Recv symmetry. *)
Definition red_spec_at {n} (ps : n.-tuple (proc data)) (i : 'I_n) :
    option (red_spec n) :=
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
Definition red_applies {n} (ps : n.-tuple (proc data)) (r : red_spec n) :
    Prop :=
  extract (red_spec_lens r) ps = red_spec_input r :> seq _.

(* red_spec_at only returns reductions that actually apply to ps.
   Bridges red_spec_at → extract equality needed by rstep_disjoint. *)
Lemma red_spec_at_applies n (ps : n.-tuple (proc data)) i r :
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

(******************************************************************************)
(* Index classification: Inert vs Disjoint                                     *)
(*                                                                            *)
(* From the interpreter's perspective, each index either fires (participates  *)
(* in a reduction) or is inert (step returns the process unchanged).          *)
(* The 6-way case split on proc constructors is absorbed into classify,       *)
(* which maps each index to one of two cases:                                 *)
(*                                                                            *)
(*   Inert     — Finish, Fail, unmatched Send, unmatched Recv                 *)
(*               step ps [::] i = (ps !_ i, [::], false)                     *)
(*   Disjoint  — Init, Ret, matched Send/Recv                                *)
(*               red_spec_at ps i = Some r for some r                         *)
(*                                                                            *)
(* The name "Disjoint" reflects the key property (from rstep_disjoint):       *)
(* any two Disjoint reductions from the same state touch non-overlapping      *)
(* indices. This is what makes them composable in any order.                  *)
(*                                                                            *)
(* proc constructor mapping:                                                  *)
(*   Init d k           →  Disjoint (RSinit i d k)                           *)
(*   Ret d              →  Disjoint (RSret i d)                              *)
(*   Send j x p         →  Disjoint (RScomm i j x p f) if Recv i f at j     *)
(*                         Inert                       otherwise             *)
(*   Recv j f           →  Disjoint (RScomm j i x p f) if Send i x p at j   *)
(*                         Inert                       otherwise             *)
(*   Finish             →  Inert                                             *)
(*   Fail               →  Inert                                             *)
(******************************************************************************)

Inductive index_class n (ps : n.-tuple (proc data)) (i : 'I_n) : Type :=
  | Inert :
      step ps [::] i = (ps !_ i, [::], false) -> index_class ps i
  | Disjoint (r : red_spec n) :
      red_spec_at ps i = Some r -> index_class ps i.

(* The 6-way case split on proc constructors lives here, once.
   After this, step_sound only sees 2 cases.
   Proof-mode construction (not computational): red_spec_at uses
   opaque eqP pattern matching, so we prove red_spec_at ps i = Some r
   by unfolding and stepping through the decidability checks. *)
Lemma classify n (ps : n.-tuple (proc data)) (i : 'I_n) :
  index_class ps i.
Proof.
case Hpi: (ps !_ i) => [x p|dst w next|frm f|x||].
- by apply (Disjoint (r:=RSinit i x p)); rewrite /red_spec_at Hpi.
- (* Send dst w next *)
  case: (ltnP dst n) => dstn; last first.
    apply Inert.
    by rewrite /step -tnth_nth Hpi nth_default // size_tuple.
  set j := Ordinal dstn.
  case Hpj: (ps !_ j) => [y q|dst2 w2 nxt2|frm2 f2|y||];
    try by apply Inert; rewrite /step -tnth_nth Hpi (_: dst = j) // -tnth_nth Hpj.
  have [/eqP frm2i|frm2i] := boolP (frm2 == nat_of_ord i).
  + apply (Disjoint (r:=RScomm i j w next f2)).
    rewrite /red_spec_at Hpi /= /j.
    case: (eqP) => [pf|/negP]; last by rewrite dstn.
    by rewrite (bool_irrelevance pf dstn) Hpj frm2i eqxx.
  + by apply Inert; rewrite /step -(tnth_nth (default_proc _) ps i) Hpi
      -(tnth_nth (default_proc _) ps j) Hpj (negbTE frm2i).
- (* Recv frm f *)
  have [frmn|frmn] := boolP (frm < n)%N; last first.
    by apply Inert; rewrite /step -(tnth_nth (default_proc _) ps i) Hpi
       nth_default ?size_tuple // leqNgt.
  set j := Ordinal frmn.
  have Hj : nth (default_proc _) ps frm = ps !_ j.
    by rewrite -(tnth_nth (default_proc _) ps j).
  case Hpj: (ps !_ j) => [y q|dst2 w2 nxt2|frm2 f2|y||];
    try by (apply Inert; rewrite /step -(tnth_nth (default_proc _) ps i) Hpi
         Hj Hpj //=).
  (* Send dst2 w2 nxt2 sub-case *)
  have [/eqP dst2i|dst2i] := boolP (dst2 == nat_of_ord i).
  + apply (Disjoint (r:=RScomm j i w2 nxt2 f)).
    rewrite /red_spec_at Hpi /= /j.
    case: (eqP) => [pf|/negP]; last by rewrite frmn.
    rewrite (bool_irrelevance pf frmn).
    (* Now need: match ps !_ (Ordinal frmn) ... = Some (RScomm ...) *)
    (* ps !_ (Ordinal frmn) = ps !_ j = Send dst2 w2 nxt2 *)
    rewrite Hpj dst2i eqxx //.
  + by apply Inert; rewrite /step -(tnth_nth (default_proc _) ps i) Hpi
      Hj Hpj (negbTE dst2i).
- by apply (Disjoint (r:=RSret i x)); rewrite /red_spec_at Hpi.
- by apply Inert; rewrite /step -(tnth_nth (default_proc _) ps i) Hpi.
- by apply Inert; rewrite /step -(tnth_nth (default_proc _) ps i) Hpi.
Qed.

(* Lift red_spec_at to an rstep on the actual process state.
   Bridges red_spec (syntactic packaging) → rstep (semantic reduction).
   Proof: rewrite extract via red_spec_at_applies, apply red_spec_valid. *)
Lemma red_spec_at_rstep n (ps : n.-tuple (proc data)) (i : 'I_n) r :
  red_spec_at ps i = Some r ->
  rstep (red_spec_lens r) (extract (red_spec_lens r) ps)
        (red_spec_output r) (red_spec_traces r).
Proof.
move=> Hr.
have Ha := red_spec_at_applies Hr.
rewrite /red_applies in Ha.
have Ha' : extract (red_spec_lens r) ps = red_spec_input r by exact: val_inj.
by rewrite Ha'; exact: red_spec_valid.
Qed.

(* Backward direction of step_complete: if red_spec_at finds a reduction,
   then step actually fires at each involved index. *)
Lemma red_spec_at_fires n (ps : n.-tuple (proc data)) (i : 'I_n) r :
  red_spec_at ps i = Some r ->
  forall j, j \in red_spec_indices r ->
    (step ps [::] j).2 = true.
Proof.
move=> Hr j Hj.
have Ha := red_spec_at_applies Hr.
case: r Hr Ha Hj => /=.
- (* RSinit *)
  move=> k y p Hr Ha. rewrite inE => /eqP ->.
  rewrite /red_applies /= in Ha. move: Ha => [] Hk.
  by rewrite /step -(tnth_nth (default_proc _) ps k) Hk.
- (* RSret *)
  move=> k y Hr Ha. rewrite inE => /eqP ->.
  rewrite /red_applies /= in Ha. move: Ha => [] Hk.
  by rewrite /step -(tnth_nth (default_proc _) ps k) Hk.
- (* RScomm *)
  move=> a b y pa pb Hr Ha.
  rewrite !inE => /orP[/eqP ->|/eqP ->].
  + rewrite /red_applies /= in Ha. move: Ha => [] Ha Hb.
    rewrite /step -(tnth_nth (default_proc _) ps a) Ha.
    by rewrite -(tnth_nth (default_proc _) ps b) Hb eqxx.
  + rewrite /red_applies /= in Ha. move: Ha => [] Ha Hb.
    rewrite /step -(tnth_nth (default_proc _) ps b) Hb.
    by rewrite -(tnth_nth (default_proc _) ps a) Ha eqxx.
Qed.

(* For RScomm, the sender and receiver are distinct.
   If i = j, then ps !_ i would be simultaneously Send and Recv,
   which is impossible since proc constructors are disjoint. *)
Lemma red_spec_at_neq n (ps : n.-tuple (proc data)) (i j : 'I_n) x pi pj :
  red_spec_at ps i = Some (RScomm i j x pi pj) -> i != j.
Proof.
move=> Hr; apply /eqP => ij; subst j.
have := red_spec_at_applies Hr.
rewrite /red_applies /red_spec_lens /red_spec_input /extract /=.
by move=> [] ->.
Qed.

(* red_spec_at ps i always returns a reduction involving i *)
Lemma red_spec_at_mem n (ps : n.-tuple (proc data)) (i : 'I_n) r :
  red_spec_at ps i = Some r -> i \in red_spec_indices r.
Proof.
rewrite /red_spec_at.
case: (ps !_ i) => [x p|dst w next|frm f|x||] //=.
- by move=> [<-]; rewrite inE.
- case: eqP => //= dstn.
  case: (ps !_ _) => //= frm2 f2.
  case: ifP => //= frm2i [<-].
  by rewrite !inE eqxx.
- case: eqP => //= frmn.
  case: (ps !_ _) => //= dst2 w2 nxt2.
  case: ifP => //= dst2i [<-].
  by rewrite !inE eqxx orbT.
- by move=> [<-]; rewrite inE.
Qed.

(******************************************************************************)
(* Soundness: step simulated by rsteps                                         *)
(*                                                                            *)
(* 2-way dispatch: Inert → step_res_inert, Disjoint → step_res_red_sender.   *)
(* No 6-way case split, no partner search, no Send/Recv duplication.          *)
(* The 6-way analysis is encapsulated in classify (proved once), and          *)
(* rstep_disjoint handles all invariant maintenance uniformly.                *)
(******************************************************************************)

(* step_res computes the result of one round of step for all parties in set s.
   For i in s, it runs step; for i not in s, it returns the unchanged process.
   This intermediate definition bridges functional step and relational rsteps
   by allowing inductive removal of parties from s. *)
Definition step_res n (s : {fset 'I_n}) (ps : n.-tuple (proc data)) :=
  [tuple if i \in s then step ps [::] i
         else (ps !_ i, nil, false) | i < n].

(* The interpreter result for party set S is a valid rsteps reduction *)
Definition step_res_sound n (ps : n.-tuple (proc data))
    (S : {fset 'I_n}) : Prop :=
  rsteps ps (res_procs (step_res S ps)) (res_traces (step_res S ps)).

(* When step leaves party i unchanged, removing i from the active set
   doesn't change step_res. For k != i, membership is unchanged;
   for k = i, step returning (ps !_ i, nil, false) matches the default. *)
Lemma step_res_inert n (ps : n.-tuple (proc data)) (i : 'I_n)
    (pss : {fset 'I_n}) :
  i \in pss ->
  step ps [::] i = (ps !_ i, [::], false) ->
  step_res pss ps = step_res (pss `\ i) ps.
Proof.
move=> Hi Hstep.
apply: eq_from_tnth => k; rewrite !tnth_mktuple !inE.
by have [-> |] //= := eqVneq k i; rewrite Hi Hstep.
Qed.

(* After a 1-party rstep, injecting the result equals the full step_res. *)
Lemma step_res_inject1 n (ps : n.-tuple (proc data)) (i : 'I_n)
    (pss : {fset 'I_n}) (q : proc data) (tr : seq data) :
  i \in pss ->
  step ps [::] i = (q, tr, true) ->
  inject [tuple i] (res_procs (step_res (pss `\ i) ps)) [tuple q] =
  res_procs (step_res pss ps).
Proof.
move=> Hi Hstep.
apply: eq_from_tnth => j; rewrite !(tnth_mktuple, tnth_map) /=.
case/boolP: (i == j) => [/eqP <- | ij] /=.
  by rewrite Hi Hstep.
by rewrite !inE eq_sym ij.
Qed.

(* After a 1-party rstep, trace projection matches rsteps concatenation. *)
Lemma step_res_trace1 n (ps : n.-tuple (proc data)) (i : 'I_n)
    (pss : {fset 'I_n}) (q : proc data) (tr : seq data) :
  i \in pss ->
  step ps [::] i = (q, tr, true) ->
  res_traces (step_res pss ps) =
  [tuple (inject [tuple i] [tuple [::] | _ < n] [tuple tr]) !_ k ++
         (res_traces (step_res (pss `\ i) ps)) !_ k | k < n].
Proof.
move=> Hi Hstep.
apply: eq_from_tnth => k; rewrite !(tnth_mktuple, tnth_map) /=.
case/boolP: (i == k) => [/eqP <- | /negbTE ik] /=.
  by rewrite Hi Hstep !inE eqxx /= cats0.
by have -> : (k \in pss `\ i) = (k \in pss) by rewrite !inE eq_sym ik.
Qed.

(* After a 2-party rstep, injecting both results equals the full step_res. *)
Lemma step_res_inject2 n (ps : n.-tuple (proc data)) (a b : 'I_n)
    (pss : {fset 'I_n})
    (qa qb : proc data) (tra trb : seq data) :
  a \in pss -> b \in pss -> a != b ->
  step ps [::] a = (qa, tra, true) ->
  step ps [::] b = (qb, trb, true) ->
  inject [tuple a; b] (res_procs (step_res (pss `\ a `\ b) ps))
    [tuple qa; qb] =
  res_procs (step_res pss ps).
Proof.
move=> Ha Hb ab Hstepa Hstepb.
apply: eq_from_tnth => k; rewrite !(tnth_mktuple, tnth_map) /=.
case/boolP: (a == k) => [/eqP <- | ak] /=.
  by rewrite Ha Hstepa.
case/boolP: (b == k) => [/eqP <- | bk] /=.
  by rewrite Hb Hstepb.
by rewrite !inE eq_sym bk eq_sym ak.
Qed.

(* After a 2-party rstep, trace projection matches rsteps concatenation. *)
Lemma step_res_trace2 n (ps : n.-tuple (proc data)) (a b : 'I_n)
    (pss : {fset 'I_n})
    (qa qb : proc data) (tra trb : seq data) :
  a \in pss -> b \in pss -> a != b ->
  step ps [::] a = (qa, tra, true) ->
  step ps [::] b = (qb, trb, true) ->
  res_traces (step_res pss ps) =
  [tuple (inject [tuple a; b] [tuple [::] | _ < n] [tuple tra; trb]) !_ k ++
         (res_traces (step_res (pss `\ a `\ b) ps)) !_ k | k < n].
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

(******************************************************************************)
(* Sender-only variant: step_res_red_sender                                   *)
(*                                                                            *)
(* Takes b ∈ pss as a direct hypothesis. Only handles the i=a (sender) case *)
(* for RScomm, since the list-based approach only processes sender-side       *)
(* RScomm, since the list-based approach only processes sender-side specs.    *)
(******************************************************************************)

(* If red_spec_at from a Send-side index gives RScomm, the queried index is
   the sender (first argument). *)
Lemma red_spec_at_sender n (ps : n.-tuple (proc data)) (i : 'I_n)
    a b x pa pb :
  red_spec_at ps i = Some (RScomm a b x pa pb) ->
  is_true (match ps !_ i with Send _ _ _ => true | _ => false end) ->
  i = a.
Proof.
rewrite /red_spec_at.
case Hpi: (ps !_ i) => [y p0|dst w next|frm f|y||] //=.
case: eqP => // jn.
case Hpj: (ps !_ (Ordinal jn)) => [y' q|dst2 w2 nxt2|frm2 f2|y'||] //=.
by case: ifP => // _ [] -> _ _ _ _.
Qed.

Lemma step_res_red_sender n (ps : n.-tuple (proc data)) (pss : {fset 'I_n})
    (i : 'I_n) (r : red_spec n) :
  red_spec_at ps i = Some r ->
  i \in pss ->
  (forall a b x pa pb, r = RScomm a b x pa pb -> i = a /\ b \in pss) ->
  step_res_sound ps
    match r with
    | RSinit _ _ _ => pss `\ i
    | RSret _ _ => pss `\ i
    | RScomm a b _ _ _ => pss `\ a `\ b
    end ->
  step_res_sound ps pss.
Proof.
move=> Hr Hi Hsender IH.
case: r Hr IH Hsender => [k y p|k y|a b y pa pb] Hr IH Hsender.
- (* RSinit *)
  have Hi_mem := red_spec_at_mem Hr.
  rewrite /= inE in Hi_mem; move/eqP: Hi_mem => ?; subst k.
  have Ha := red_spec_at_applies Hr.
  rewrite /red_applies /= in Ha; move: Ha => [] Hpi.
  have Hstep : step ps [::] i = (p, [:: y], true)
    by rewrite /step -(tnth_nth (default_proc _)) Hpi.
  rewrite /step_res_sound.
  apply: (rtrans IH); last first.
  + apply: (step_res_trace1 Hi Hstep).
  + move: (rinit i y p).
    set ps'' := res_procs _.
    have -> : [tuple Init y p] = extract [tuple i] ps''.
      apply/val_inj; rewrite /= /ps'' /res_procs tnth_map tnth_mktuple.
      by rewrite !inE eqxx /= Hpi.
    move/rone.
    by rewrite (step_res_inject1 Hi Hstep).
- (* RSret *)
  have Hi_mem := red_spec_at_mem Hr.
  rewrite /= inE in Hi_mem; move/eqP: Hi_mem => ?; subst k.
  have Ha := red_spec_at_applies Hr.
  rewrite /red_applies /= in Ha; move: Ha => [] Hpi.
  have Hstep : step ps [::] i = (Finish, [:: y], true)
    by rewrite /step -(tnth_nth (default_proc _)) Hpi.
  rewrite /step_res_sound.
  apply: (rtrans IH); last first.
  + apply: (step_res_trace1 Hi Hstep).
  + move: (rret i y).
    set ps'' := res_procs _.
    have -> : [tuple Ret y] = extract [tuple i] ps''.
      apply/val_inj; rewrite /= /ps'' /res_procs tnth_map tnth_mktuple.
      by rewrite !inE eqxx /= Hpi.
    move/rone.
    by rewrite (step_res_inject1 Hi Hstep).
- (* RScomm - sender side only *)
  have [Hi_eq Hb_pss] := Hsender a b y pa pb erefl.
  subst i.
  have Hab := red_spec_at_neq Hr.
  have Happ := red_spec_at_applies Hr.
  rewrite /red_applies /= in Happ; move: Happ => [] Hpa Hpb.
  have Hstepa : step ps [::] a = (pa, [::], true).
    rewrite /step -(tnth_nth (default_proc _)) Hpa.
    by rewrite -(tnth_nth (default_proc _) ps b) Hpb eqxx.
  have Hstepb : step ps [::] b = (pb y, [:: y], true).
    rewrite /step -(tnth_nth (default_proc _)) Hpb.
    by rewrite -(tnth_nth (default_proc _) ps a) Hpa eqxx.
  rewrite /step_res_sound.
  apply: (rtrans IH); last first.
  * apply: (step_res_trace2 Hi Hb_pss Hab Hstepa Hstepb).
  * move: (rcomm a b y pa pb).
    suff Hext : [tuple Send (nat_of_ord b) y pa; Recv (nat_of_ord a) pb] =
              extract [tuple a; b] (res_procs (step_res (pss `\ a `\ b) ps))
      by rewrite Hext; move/rone;
         by rewrite (step_res_inject2 Hi Hb_pss Hab Hstepa Hstepb).
    apply/val_inj.
    rewrite /= /res_procs !(tnth_map, tnth_mktuple, tnth_ord_tuple).
    have Ha_notin : a \notin pss `\ a `\ b by rewrite !inE eqxx /= andbF.
    have Hb_notin : b \notin pss `\ a `\ b by rewrite !inE eqxx.
    by rewrite (negbTE Ha_notin) (negbTE Hb_notin) Hpa Hpb.
Qed.

(******************************************************************************)
(* List-based soundness infrastructure                                        *)
(*                                                                            *)
(* Build a deduplicated list of red_specs (one per reduction, sender-side     *)
(* only for RScomm), prove pairwise disjointness, and use list induction     *)
(* instead of finSet_rect.                                                    *)
(******************************************************************************)

(* is_sender: true for Init/Ret/Send, false for Recv/Finish/Fail.
   Used to filter out Recv so each RScomm appears once via sender indices. *)
Definition is_sender {n} (ps : n.-tuple (proc data)) (i : 'I_n) : bool :=
  match ps !_ i with
  | Init _ _ | Ret _ | Send _ _ _ => true
  | _ => false
  end.

(* has_red: i is a sender-side index with a fireable reduction *)
Definition has_red {n} (ps : n.-tuple (proc data)) (i : 'I_n) : bool :=
  is_sender ps i &&
  match red_spec_at ps i with Some _ => true | None => false end.

(* List of sender indices with fireable reductions.
   Each RScomm appears once (from the Send side, not the Recv side). *)
Definition active_senders {n} (ps : n.-tuple (proc data)) : seq 'I_n :=
  [seq i <- enum 'I_n | has_red ps i].

(* All indices involved in some reduction (senders + their partners) *)
Definition active_indices {n} (ps : n.-tuple (proc data)) : {fset 'I_n} :=
  \big[fsetU/fset0]_(i <- active_senders ps)
    match red_spec_at ps i with
    | Some r => [fset j : 'I_n | j \in red_spec_indices r]
    | None => fset0
    end.

(* For any active sender i with red_spec_at ps i = Some r,
   all indices of r are in active_indices *)
Lemma active_senders_indices n (ps : n.-tuple (proc data)) i r j :
  i \in active_senders ps -> red_spec_at ps i = Some r ->
  j \in red_spec_indices r -> j \in active_indices ps.
Proof.
move=> Hi Hr Hj; rewrite /active_indices; apply/bigfcupP.
by exists i; [rewrite Hi | rewrite Hr inE].
Qed.

(* Every Disjoint index has a corresponding active sender *)
Lemma active_senders_complete n (ps : n.-tuple (proc data)) (i : 'I_n) r :
  red_spec_at ps i = Some r ->
  exists k, k \in active_senders ps /\ red_spec_at ps k = Some r.
Proof.
move=> Hr; case Hsender: (is_sender ps i).
- exists i; split => //.
  by rewrite /active_senders mem_filter /has_red Hsender Hr mem_enum.
- rewrite /is_sender in Hsender.
  rewrite /red_spec_at in Hr.
  case Hpi: (ps !_ i) Hsender Hr => [y p0|dst w next|frm f|y||] //= _.
  case: eqP => // jn.
  set j := Ordinal jn.
  case Hpj: (ps !_ j) => [y' q|dst2 w2 nxt2|frm2 f2|y'||] //=.
  case: ifP => // /eqP dst2i [] Hr_eq; subst r.
  have din : (dst2 < n)%N by rewrite dst2i; exact: ltn_ord.
  have ji_eq : Ordinal din = i by apply: val_inj; rewrite /= dst2i.
  exists j; split.
  + rewrite /active_senders mem_filter /has_red /is_sender Hpj /= mem_enum andbT.
    rewrite /red_spec_at Hpj /=.
    case: eqP => [pf|/negP]; last by rewrite din.
    by rewrite (bool_irrelevance pf din) ji_eq Hpi eqxx.
  + rewrite /red_spec_at Hpj /=.
    case: eqP => [pf|/negP]; last by rewrite din.
    by rewrite (bool_irrelevance pf din) ji_eq Hpi eqxx.
Qed.

(* active_senders have uniq (inherited from enum) *)
Lemma active_senders_uniq n (ps : n.-tuple (proc data)) :
  uniq (active_senders ps).
Proof. exact: filter_uniq (enum_uniq 'I_n). Qed.

(* Stripping inert indices: step_res on the full set equals step_res on
   just the active indices, because inert indices don't change step_res. *)
Lemma step_res_strip_inert n (ps : n.-tuple (proc data)) :
  step_res [fset x : 'I_n | true] ps = step_res (active_indices ps) ps.
Proof.
apply: eq_from_tnth => k; rewrite !tnth_mktuple inE /=.
case: ifP => // Hk_notin.
case: (classify ps k) => [Hinert | r Hr]; first exact: Hinert.
exfalso; move/negP: Hk_notin; apply.
have [k' [Hk'_as Hk'_r]] := active_senders_complete Hr.
exact: (active_senders_indices Hk'_as Hk'_r (red_spec_at_mem Hr)).
Qed.

(* Main list-based soundness: induction over active_senders *)
Lemma step_sound_list n (ps : n.-tuple (proc data))
    (senders : seq 'I_n) (pss : {fset 'I_n}) :
  uniq senders ->
  (* all indices of all senders' reductions are in pss *)
  (forall i, i \in senders -> forall r, red_spec_at ps i = Some r ->
    forall j, j \in red_spec_indices r -> j \in pss) ->
  (* all senders are active sender indices *)
  (forall i, i \in senders -> has_red ps i) ->
  (* senders have disjoint reductions *)
  (forall i1 i2, i1 \in senders -> i2 \in senders -> i1 != i2 ->
    forall r1 r2, red_spec_at ps i1 = Some r1 -> red_spec_at ps i2 = Some r2 ->
    {in red_spec_indices r1 & red_spec_indices r2, forall a b, a != b}) ->
  (* non-sender indices in pss are inert *)
  (forall i, i \in pss -> i \notin
    \big[fsetU/fset0]_(k <- senders)
      match red_spec_at ps k with
      | Some r => [fset j : 'I_n | j \in red_spec_indices r]
      | None => fset0
      end ->
    step ps [::] i = (ps !_ i, [::], false)) ->
  step_res_sound ps pss.
Proof.
elim: senders pss => [|s senders' IHs] pss Huniq Hindices Hactive Hdisj Hinert.
- (* Base case *)
  rewrite /step_res_sound.
  have Heq : step_res pss ps = [tuple (ps !_ k, [::], false) | k < n].
    apply: eq_from_tnth => k; rewrite !tnth_mktuple.
    case/boolP: (k \in pss) => Hk //.
    apply: Hinert => //. rewrite big_nil inE //.
  rewrite Heq.
  have -> : res_procs [tuple (ps !_ k, [::], false) | k < n] = ps.
    by apply: eq_from_tnth => k; rewrite /res_procs tnth_map !tnth_mktuple.
  have -> : res_traces [tuple (ps !_ k, [::], false) | k < n] = [tuple [::] | _ < n].
    by apply: eq_from_tnth => k; rewrite /res_traces tnth_map !tnth_mktuple.
  exact: rrefl.
- (* Inductive case *)
  have /andP [Hs_notin Huniq'] := Huniq.
  have Hs_active := Hactive s (mem_head _ _).
  rewrite /has_red in Hs_active; case/andP: Hs_active => Hs_sender Hs_red.
  case Hr_eq: (red_spec_at ps s) Hs_red => [r|] //= _.
  have Hs_mem := red_spec_at_mem Hr_eq.
  have Hs_pss : s \in pss := Hindices s (mem_head _ _) r Hr_eq s Hs_mem.
  apply: (step_res_red_sender Hr_eq Hs_pss); clear Hs_mem.
  + move=> a b x pa pb Hr_comm.
    have Hr_eq' : red_spec_at ps s = Some (RScomm a b x pa pb)
      by rewrite Hr_eq Hr_comm.
    have Happ := red_spec_at_applies Hr_eq'.
    rewrite /red_applies /= in Happ; case: Happ => Hpa Hpb.
    have Hs_eq : s = a.
      have Hs_mem' := red_spec_at_mem Hr_eq'.
      rewrite /= !inE in Hs_mem'.
      case/orP: Hs_mem' => /eqP // Hsb.
      by exfalso; rewrite /is_sender Hsb Hpb in Hs_sender.
    split => //.
    have Hb_idx : b \in red_spec_indices (RScomm a b x pa pb)
      by rewrite /= !inE eqxx orbT.
    exact: Hindices s (mem_head _ _) _ Hr_eq' b Hb_idx.
  + apply: IHs => //.
    * move=> i Hi_in r' Hr' j Hj.
      have Hi_senders : i \in s :: senders' by rewrite inE Hi_in orbT.
      have Hj_pss := Hindices i Hi_senders r' Hr' j Hj.
      have Hi_neq_s : i != s.
        by apply/eqP => is_eq; subst i; move: Hs_notin; rewrite Hi_in.
      have Hrdisj := Hdisj i s Hi_senders (mem_head _ _) Hi_neq_s r' r Hr' Hr_eq.
      case: r Hr_eq Hrdisj => [k y p|k y|a b y pa pb] Hr_eq Hrdisj.
      -- rewrite !inE Hj_pss andbT.
         by have /= := Hrdisj j s Hj (red_spec_at_mem Hr_eq).
      -- rewrite !inE Hj_pss andbT.
         by have /= := Hrdisj j s Hj (red_spec_at_mem Hr_eq).
      -- rewrite !inE Hj_pss !andbT.
         have Ha_idx : a \in red_spec_indices (RScomm a b y pa pb)
           by rewrite /= !inE eqxx.
         have Hb_idx : b \in red_spec_indices (RScomm a b y pa pb)
           by rewrite /= !inE eqxx orbT.
         have /= -> := Hrdisj j a Hj Ha_idx.
         by have /= -> := Hrdisj j b Hj Hb_idx.
    * move=> i0 Hi0_in; apply: Hactive; by rewrite inE Hi0_in orbT.
    * move=> i1 i2 Hi1 Hi2 Hneq r1 r2 Hr1 Hr2.
      by apply: (Hdisj i1 i2) => //; rewrite inE ?Hi1 ?Hi2 orbT.
    * move=> i Hi_pss' Hi_notin.
      apply: Hinert.
      -- case: r Hr_eq Hi_pss' => [k y p|k y|a b y pa pb] Hr_eq.
         ++ by rewrite inE; case/andP.
         ++ by rewrite inE; case/andP.
         ++ by rewrite !inE => /andP [? /andP [? ?]].
      -- rewrite big_cons inE negb_or; apply/andP; split; last exact: Hi_notin.
         rewrite Hr_eq.
         case: r Hr_eq Hi_pss' => [k y p|k y|a b y pa pb] Hr_eq Hi_pss'.
         ++ rewrite inE in Hi_pss'; case/andP: Hi_pss' => Hi_neq _.
            rewrite inE /= inE /=.
            by have := red_spec_at_mem Hr_eq; rewrite /= inE => /eqP <-;
               rewrite inE in Hi_neq.
         ++ rewrite inE in Hi_pss'; case/andP: Hi_pss' => Hi_neq _.
            rewrite inE /= inE /=.
            by have := red_spec_at_mem Hr_eq; rewrite /= inE => /eqP <-;
               rewrite inE in Hi_neq.
         ++ rewrite !inE in Hi_pss'.
            case/andP: Hi_pss' => Hi_neq_b /andP [Hi_neq_a _].
            rewrite inE /= !inE /= negb_or.
            have := red_spec_at_mem Hr_eq; rewrite /= !inE =>
              /orP [/eqP Hsa | /eqP Hsb].
            ** by subst a; rewrite Hi_neq_a Hi_neq_b.
            ** by subst b; rewrite Hi_neq_a Hi_neq_b.
Qed.

(* Distinct active senders have disjoint reduction indices.
   Uses rstep_disjoint + the fact that both senders have is_sender = true,
   so for RScomm the receiver (b) is excluded, forcing i1 = i2 = a. *)
Lemma active_senders_disjoint n (ps : n.-tuple (proc data))
    (i1 i2 : 'I_n) r1 r2 :
  i1 \in active_senders ps -> i2 \in active_senders ps -> i1 != i2 ->
  red_spec_at ps i1 = Some r1 -> red_spec_at ps i2 = Some r2 ->
  {in red_spec_indices r1 & red_spec_indices r2, forall a b, a != b}.
Proof.
move=> Hi1 Hi2 Hneq Hr1 Hr2.
have Hrstep1 := red_spec_at_rstep Hr1.
have Hrstep2 := red_spec_at_rstep Hr2.
have indices_is_lens : forall m (s : red_spec m),
    red_spec_indices s = tval (red_spec_lens s) by [].
have Hi1_sender : is_sender ps i1.
  by rewrite /active_senders mem_filter in Hi1; case/andP: Hi1 => /andP [].
have Hi2_sender : is_sender ps i2.
  by rewrite /active_senders mem_filter in Hi2; case/andP: Hi2 => /andP [].
case: (rstep_disjoint erefl erefl Hrstep1 Hrstep2).
- move=> [/eqP Hlens_eq [_ _]].
  have Hi1_mem := red_spec_at_mem Hr1.
  have Hi2_mem := red_spec_at_mem Hr2.
  exfalso; move: Hneq; apply/negP/negPn.
  have Hi2_lens : i2 \in tval (red_spec_lens r2) by rewrite -indices_is_lens.
  rewrite -Hlens_eq in Hi2_lens.
  have Hi2_in_r1 : i2 \in red_spec_indices r1 by rewrite indices_is_lens.
  clear Hi2_lens Hlens_eq.
  case: r1 Hr1 Hrstep1 Hi1_mem Hi2_in_r1 Hi1_sender
    => [k y p|k y|a b y pa pb] Hr1 Hrstep1 Hi1_mem Hi2_in_r1 Hi1_sender.
  + by rewrite /= !inE in Hi1_mem Hi2_in_r1; rewrite (eqP Hi1_mem) (eqP Hi2_in_r1).
  + by rewrite /= !inE in Hi1_mem Hi2_in_r1; rewrite (eqP Hi1_mem) (eqP Hi2_in_r1).
  + rewrite /= !inE in Hi1_mem Hi2_in_r1.
    have Happ := red_spec_at_applies Hr1.
    rewrite /red_applies /= in Happ; case: Happ => Hpa Hpb.
    have Hi1_eq : i1 = a.
      case/orP: Hi1_mem => /eqP // Hi1b.
      by exfalso; rewrite /is_sender Hi1b Hpb in Hi1_sender.
    have Hi2_eq : i2 = a.
      case/orP: Hi2_in_r1 => /eqP // Hi2b.
      by exfalso; rewrite /is_sender Hi2b Hpb in Hi2_sender.
    by rewrite Hi1_eq Hi2_eq.
- move=> Hdisj a0 b0 Ha0 Hb0.
  rewrite indices_is_lens in Ha0.
  rewrite indices_is_lens in Hb0.
  exact: Hdisj a0 b0 Ha0 Hb0.
Qed.

(******************************************************************************)
(* Main theorem: Soundness of the functional interpreter                       *)
(*                                                                            *)
(* Uses list-based induction over active_senders instead of finSet_rect.      *)
(* 1. Bridge functional step to step_res on the full index set               *)
(* 2. Strip inert indices via step_res_strip_inert                           *)
(* 3. Apply step_sound_list with active_senders                              *)
(******************************************************************************)

Lemma step_sound n (ps : n.-tuple (proc data)) :
  let res := [tuple step ps nil i | i < n] in
  let ps' := res_procs res in
  let tr := res_traces res in
  rsteps ps ps' tr.
Proof.
move=> res.
have -> : res = step_res [fset x : 'I_n | true] ps.
  by apply: eq_from_tnth => i; rewrite !tnth_mktuple ifT // !inE.
rewrite step_res_strip_inert.
apply: (step_sound_list (active_senders_uniq ps)).
- move=> i Hi r Hr j Hj.
  exact: (active_senders_indices Hi Hr Hj).
- move=> i Hi.
  by rewrite /active_senders mem_filter in Hi; case/andP: Hi.
- move=> i1 i2 Hi1 Hi2 Hneq r1 r2 Hr1 Hr2.
  exact: (active_senders_disjoint Hi1 Hi2 Hneq Hr1 Hr2).
- move=> i Hi Hnotin.
  case: (classify ps i) => [Hinert | r Hr]; first exact: Hinert.
  exfalso; move/negP: Hnotin; apply.
  have [k [Hk_as Hk_r]] := active_senders_complete Hr.
  exact: (active_senders_indices Hk_as Hk_r (red_spec_at_mem Hr)).
Qed.

End sound.
