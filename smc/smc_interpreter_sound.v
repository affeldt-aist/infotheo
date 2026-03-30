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

(* Indices involved in a reduction *)
Definition red_spec_indices {n} (r : red_spec n) : seq 'I_n :=
  match r with
  | RSinit i _ _ => [:: i]
  | RSret i _ => [:: i]
  | RScomm i j _ _ _ => [:: i; j]
  end.

(* Lens for a reduction (indices as a tuple) *)
Definition red_spec_lens {n} (r : red_spec n) :
    lens n (size (red_spec_indices r)) :=
  match r return lens n (size (red_spec_indices r)) with
  | RSinit i _ _ => [tuple i]
  | RSret i _ => [tuple i]
  | RScomm i j _ _ _ => [tuple i; j]
  end.

(* Input processes — what the reduction expects *)
Definition red_spec_input {n} (r : red_spec n) :
    (size (red_spec_indices r)).-tuple (proc data) :=
  match r return (size (red_spec_indices r)).-tuple (proc data) with
  | RSinit _ x p => [tuple Init x p]
  | RSret _ x => [tuple Ret x]
  | RScomm i j x pi pj =>
      [tuple Send (nat_of_ord j) x pi; Recv (nat_of_ord i) pj]
  end.

(* Output processes — what the reduction produces *)
Definition red_spec_output {n} (r : red_spec n) :
    (size (red_spec_indices r)).-tuple (proc data) :=
  match r return (size (red_spec_indices r)).-tuple (proc data) with
  | RSinit _ _ p => [tuple p]
  | RSret _ _ => [tuple Finish]
  | RScomm _ _ x pi pj => [tuple pi; pj x]
  end.

(* Output traces — data emitted by the reduction *)
Definition red_spec_traces {n} (r : red_spec n) :
    (size (red_spec_indices r)).-tuple (seq data) :=
  match r return (size (red_spec_indices r)).-tuple (seq data) with
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
  have [dstn|dstn] := boolP (dst < n)%N; last first.
    by apply Inert; rewrite /step -(tnth_nth (default_proc _) ps i) Hpi
       nth_default ?size_tuple // leqNgt.
  set j := Ordinal dstn.
  case Hpj: (ps !_ j) => [y q|dst2 w2 nxt2|frm2 f2|y||];
    try by (apply Inert; rewrite /step -(tnth_nth (default_proc _) ps i) Hpi
         -(tnth_nth (default_proc _) ps j) Hpj //=).
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
   then step actually fires at each involved index.
   Needed in red_closed_skip to derive contradictions, and in step_res_red
   to compute what step returns at each index of a reduction. *)
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
   which is impossible since proc constructors are disjoint.
   Needed by step_res_red to satisfy step_res_inject2's i != j premise. *)
Lemma red_spec_at_neq n (ps : n.-tuple (proc data)) (i j : 'I_n) x pi pj :
  red_spec_at ps i = Some (RScomm i j x pi pj) -> i != j.
Proof.
move=> Hr; apply /eqP => ij; subst j.
have := red_spec_at_applies Hr.
rewrite /red_applies /red_spec_lens /red_spec_input /extract /=.
by move=> [] ->.
Qed.

(******************************************************************************)
(* Reduction-closed sets                                                       *)
(*                                                                            *)
(* Replaces comm_closed. The old invariant said: for any 2-party rstep on     *)
(* (i,j), both i and j are in pss or both are out. This was maintained by     *)
(* three ad-hoc lemmas (rstep_pss_remove, rstep_pss_remove2, using           *)
(* comm_disjoint).                                                            *)
(*                                                                            *)
(* The new invariant uses red_spec directly: if i is in the active set and    *)
(* has a reduction, then all indices of that reduction are in the active set. *)
(* This is maintained by a single uniform argument via rstep_disjoint:        *)
(* when we remove a reduction's indices, any other reduction is either        *)
(* identical (so its indices were removed too) or disjoint (so its indices    *)
(* are untouched). No case-splitting on reduction kind needed.                *)
(******************************************************************************)

(* Invariant: all indices of any reduction involving an active party
   are also active. Strictly stronger than comm_closed (covers 1-party
   reductions too), but the 1-party case is vacuous since the only
   index is i itself, which is already in pss. *)
Definition red_closed n (ps : n.-tuple (proc data)) (S : {fset 'I_n}) :=
  forall i, i \in S -> forall r, red_spec_at ps i = Some r ->
    forall j, j \in red_spec_indices r -> j \in S.

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

(* Removing a 1-party Disjoint reduction's index preserves red_closed.
   Uses rstep_disjoint: for remaining i' with red_spec_at ps i' = Some r',
   build rsteps from r and r', get identical-or-disjoint.
   Identical → i' was removed → contradiction. Disjoint → untouched. *)
Lemma red_closed_remove1 n (ps : n.-tuple (proc data))
    (pss : {fset 'I_n}) (i : 'I_n) r :
  red_spec_at ps i = Some r ->
  size (red_spec_indices r) = 1%N ->
  red_closed ps pss ->
  red_closed ps (pss `\ i).
Proof.
move=> Hr Hsz1 Hclosed i' Hi' r' Hr' j' Hj'.
rewrite inE in Hi'; case/andP: Hi' => i'_neq_i Hi'_pss.
have j'_pss := Hclosed i' Hi'_pss r' Hr' j' Hj'.
have Hrstep := red_spec_at_rstep Hr.
have Hrstep' := red_spec_at_rstep Hr'.
have indices_is_lens : forall m (s : red_spec m),
    red_spec_indices s = tval (red_spec_lens s) by move=> m [].
case: (rstep_disjoint erefl erefl Hrstep Hrstep').
- move=> [/eqP Hlens_eq [_ _]].
  have Hi_mem := red_spec_at_mem Hr.
  have Hi'_mem := red_spec_at_mem Hr'.
  exfalso; move: i'_neq_i; apply/negP/negPn; rewrite inE.
  have Hi'_lens : i' \in tval (red_spec_lens r') by rewrite -indices_is_lens.
  rewrite -Hlens_eq in Hi'_lens.
  have Hi_lens : i \in tval (red_spec_lens r) by rewrite -indices_is_lens.
  move: Hi_lens Hi'_lens Hsz1.
  case: r Hr Hrstep {Hrstep' Hlens_eq j'_pss Hj' j' Hi'_pss Hclosed Hi_mem Hi'_mem} =>
    [k x p|k x|a b x pa pb] Hr Hrstep; rewrite /= ?inE.
  + by move=> /eqP -> /eqP ->.
  + by move=> /eqP -> /eqP ->.
  + by [].
- move=> Hdisj.
  rewrite inE; apply/andP; split; last exact j'_pss.
  have Hi_mem := red_spec_at_mem Hr.
  rewrite indices_is_lens in Hi_mem.
  have Hj'_lens : j' \in tval (red_spec_lens r') by rewrite -indices_is_lens.
  have Hneq := Hdisj i j' Hi_mem Hj'_lens.
  by rewrite inE eq_sym.
Qed.

(* Removing a 2-party Disjoint reduction's indices preserves red_closed.
   Same rstep_disjoint argument as red_closed_remove1. *)
Lemma red_closed_remove2 n (ps : n.-tuple (proc data))
    (pss : {fset 'I_n}) (i : 'I_n) (a b : 'I_n) x pi pj :
  red_spec_at ps i = Some (RScomm a b x pi pj) ->
  red_closed ps pss ->
  red_closed ps (pss `\ a `\ b).
Proof.
move=> Hr Hclosed i' Hi' r' Hr' j' Hj'.
rewrite inE in Hi'; case/andP: Hi' => i'_neq_b Hi'2.
rewrite inE in Hi'2; case/andP: Hi'2 => i'_neq_a Hi'_pss.
have j'_pss := Hclosed i' Hi'_pss r' Hr' j' Hj'.
have Hrstep := red_spec_at_rstep Hr.
have Hrstep' := red_spec_at_rstep Hr'.
have indices_is_lens : forall m (s : red_spec m),
    red_spec_indices s = tval (red_spec_lens s) by move=> m0 [].
case: (rstep_disjoint erefl erefl Hrstep Hrstep').
- move=> [/eqP Hlens_eq [_ _]].
  have Hi'_mem := red_spec_at_mem Hr'.
  exfalso.
  have Hi'_lens : i' \in tval (red_spec_lens r') by rewrite -indices_is_lens.
  rewrite -Hlens_eq /= !inE in Hi'_lens.
  move: i'_neq_a i'_neq_b; rewrite !inE.
  case/orP: Hi'_lens => /eqP ->; by rewrite eqxx.
- move=> Hdisj.
  rewrite !inE.
  have Ha_mem : a \in tval (red_spec_lens (RScomm a b x pi pj))
    by rewrite /= !inE eqxx.
  have Hb_mem : b \in tval (red_spec_lens (RScomm a b x pi pj))
    by rewrite /= !inE eqxx orbT.
  have Hj'_lens : j' \in tval (red_spec_lens r')
    by rewrite -indices_is_lens.
  apply/andP; split.
    by rewrite eq_sym; exact: (Hdisj b j' Hb_mem Hj'_lens).
  apply/andP; split.
    by rewrite eq_sym; exact: (Hdisj a j' Ha_mem Hj'_lens).
  exact j'_pss.
Qed.

(* Removing an Inert index preserves red_closed.
   Key argument: if i were in some reduction r', then red_spec_at_fires
   would give (step ps [::] i).2 = true, contradicting inertness.
   So i is not an index of any remaining reduction, and removing it
   doesn't break any reduction's index-membership. *)
Lemma red_closed_skip n (ps : n.-tuple (proc data))
    (pss : {fset 'I_n}) (i : 'I_n) :
  i \in pss ->
  step ps [::] i = (ps !_ i, [::], false) ->
  red_closed ps pss ->
  red_closed ps (pss `\ i).
Proof.
move=> Hi Hstep Hclosed i' Hi' r' Hr' j' Hj'.
rewrite inE in Hi'; case/andP: Hi' => i'_neq_i Hi'_pss.
have j'_pss := Hclosed i' Hi'_pss r' Hr' j' Hj'.
rewrite inE; apply/andP; split; last exact j'_pss.
apply/negP; rewrite inE => /eqP j'_eq_i; subst j'.
have := red_spec_at_fires Hr' Hj'.
by rewrite Hstep.
Qed.

(******************************************************************************)
(* Soundness: step simulated by rsteps                                         *)
(*                                                                            *)
(* 2-way dispatch: Inert → step_res_inert, Disjoint → step_res_red.          *)
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

(* Given a Disjoint reduction at i and red_closed, reduce step_res_sound
   for pss to step_res_sound for the smaller set (with r's indices removed).
   Internally case-splits on r:
   - RSinit/RSret: smaller set is pss `\ i
   - RScomm i j: smaller set is pss `\ i `\ j
     (j in pss from red_closed, i != j from red_spec_at_neq) *)
Lemma step_res_red n (ps : n.-tuple (proc data)) (pss : {fset 'I_n})
    (i : 'I_n) (r : red_spec n) :
  red_spec_at ps i = Some r ->
  red_closed ps pss -> i \in pss ->
  step_res_sound ps
    match r with
    | RSinit _ _ _ => pss `\ i
    | RSret _ _ => pss `\ i
    | RScomm i j _ _ _ => pss `\ i `\ j
    end ->
  step_res_sound ps pss.
Proof.
move=> Hr Hclosed Hi IH.
case: r Hr IH => [k y p|k y|a b y pa pb] Hr IH.
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
- (* RScomm *)
  have Hi_mem := red_spec_at_mem Hr.
  rewrite /= !inE in Hi_mem.
  have Happ := red_spec_at_applies Hr.
  rewrite /red_applies /= in Happ; move: Happ => [] Hpa Hpb.
  case/orP: Hi_mem => /eqP Hi_eq.
  + (* i = a *)
    subst i.
    have Hab := red_spec_at_neq Hr.
    have Hb_idx : b \in red_spec_indices (RScomm a b y pa pb)
      by rewrite /= !inE eqxx orbT.
    have Hb_pss : b \in pss := Hclosed a Hi _ Hr b Hb_idx.
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
  + (* i = b *)
    subst i.
    have Ha_idx : a \in red_spec_indices (RScomm a b y pa pb)
      by rewrite /= !inE eqxx.
    have Ha_pss : a \in pss := Hclosed b Hi _ Hr a Ha_idx.
    have Hab : a != b.
      apply/eqP => ab; subst b.
      by move: Hpa Hpb => ->.
    have Hstepa : step ps [::] a = (pa, [::], true).
      rewrite /step -(tnth_nth (default_proc _)) Hpa.
      by rewrite -(tnth_nth (default_proc _) ps b) Hpb eqxx.
    have Hstepb : step ps [::] b = (pb y, [:: y], true).
      rewrite /step -(tnth_nth (default_proc _)) Hpb.
      by rewrite -(tnth_nth (default_proc _) ps a) Hpa eqxx.
    rewrite /step_res_sound.
    apply: (rtrans IH); last first.
    * apply: (step_res_trace2 Ha_pss Hi Hab Hstepa Hstepb).
    * move: (rcomm a b y pa pb).
      suff Hext : [tuple Send (nat_of_ord b) y pa; Recv (nat_of_ord a) pb] =
                extract [tuple a; b] (res_procs (step_res (pss `\ a `\ b) ps))
        by rewrite Hext; move/rone;
           by rewrite (step_res_inject2 Ha_pss Hi Hab Hstepa Hstepb).
      apply/val_inj.
      rewrite /= /res_procs !(tnth_map, tnth_mktuple, tnth_ord_tuple).
      have Ha_notin : a \notin pss `\ a `\ b by rewrite !inE eqxx /= andbF.
      have Hb_notin : b \notin pss `\ a `\ b by rewrite !inE eqxx.
      by rewrite (negbTE Ha_notin) (negbTE Hb_notin) Hpa Hpb.
Qed.

(******************************************************************************)
(* Main theorem: Soundness of the functional interpreter                       *)
(*                                                                            *)
(* The old proof (6-way case split, partner search, comm_closed threading)    *)
(* is replaced by a 2-way dispatch on classify:                               *)
(*   Inert    → step_res_inert removes the index, recurse                    *)
(*   Disjoint → step_res_red handles the reduction, recurse                  *)
(* The invariant red_closed is maintained by red_closed_skip (Inert) and      *)
(* red_closed_remove (Disjoint), both using rstep_disjoint uniformly.         *)
(*                                                                            *)
(* No case-splitting on proc constructors. No partner-search logic.           *)
(* No Send/Recv symmetry duplication. The 6-way analysis is encapsulated      *)
(* in classify (proved once), and rstep_disjoint handles all invariant        *)
(* maintenance uniformly across reduction kinds.                              *)
(******************************************************************************)

Lemma step_sound n (ps : n.-tuple (proc data)) :
  let res := [tuple step ps nil i | i < n] in
  let ps' := res_procs res in
  let tr := res_traces res in
  rsteps ps ps' tr.
Proof.
move=> res.
pose pss := [fset x : 'I_n | true].
have -> : res = step_res pss ps.
  by apply: eq_from_tnth => i; rewrite !tnth_mktuple ifT // !inE.
have : red_closed ps pss by move=> i _ r _ j _; rewrite !inE.
elim/finSet_rect: pss {res} => /= pss IH Hclosed.
case: (fset_0Vmem pss) => [-> | [i Hi]].
  rewrite (_ : res_procs _ = ps); last first.
    by apply: eq_from_tnth => i; rewrite tnth_map !tnth_mktuple inE.
  rewrite (_ : res_traces _ = [tuple nil | _ < n]); last first.
    by apply: eq_from_tnth => i; rewrite tnth_map !tnth_mktuple inE.
  exact: rrefl.
case: (classify ps i) => [Hinert | r Hr].
  rewrite (step_res_inert Hi Hinert).
  exact: IH (fproperD1 Hi) (red_closed_skip Hi Hinert Hclosed).
apply: (step_res_red Hr Hclosed Hi).
case: r Hr => [k y p|k y|a b y pa pb] Hr.
- exact: IH (fproperD1 Hi) (red_closed_remove1 Hr erefl Hclosed).
- exact: IH (fproperD1 Hi) (red_closed_remove1 Hr erefl Hclosed).
- have Ha_idx : a \in red_spec_indices (RScomm a b y pa pb)
    by rewrite /= !inE eqxx.
  have Ha_pss : a \in pss := Hclosed i Hi _ Hr a Ha_idx.
  apply: IH.
  + exact: fsub_proper_trans (fsubD1set _ b) (fproperD1 Ha_pss).
  + exact: red_closed_remove2 Hr Hclosed.
Qed.

End sound.
