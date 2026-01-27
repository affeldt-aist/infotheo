From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg ring.
From mathcomp Require Import Rstruct reals finmap.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_proba smc_entropy.
Require Import smc_tactics.

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

(* TODO: try to refactor the proof with lens_disjoint.
Definition lens_disjoint {n m1 m2} (l1 : lens n m1) (l2 : lens n m2) : bool :=
  [disjoint [fset x in l1] & [fset x in l2]].

Lemma rred_lens_disjoint : forall l1 l2 ps ps1' ps2' tr1 tr2,
  rred l1 (extract l1 ps) ps1' tr1 ->
  rred l2 (extract l2 ps) ps2' tr2 ->
  l1 != l2 ->
  lens_disjoint l1 l2.

(* Injecting with disjoint lenses commutes *)
Lemma inject_disjoint_comm n m1 m2 (l1 : lens n m1) (l2 : lens n m2) 
    (ps : n.-tuple proc) (ps1' : m1.-tuple proc) (ps2' : m2.-tuple proc) :
  lens_disjoint l1 l2 ->
  inject l1 (inject l2 ps ps2') ps1' = inject l2 (inject l1 ps ps1') ps2'.

(* Composing rstep with disjoint lenses *)
Lemma rstep_disjoint_compose n m1 m2 (l1 : lens n m1) (l2 : lens n m2)
    (ps : n.-tuple proc) ps1' ps2' tr1 tr2 :
  lens_disjoint l1 l2 ->
  rred l1 (extract l1 ps) ps1' tr1 ->
  rred l2 (extract l2 ps) ps2' tr2 ->
  rstep ps (inject l1 (inject l2 ps ps2') ps1') 
        [tuple (if i \in l1 then tr1 !_ (index i l1) 
                else if i \in l2 then tr2 !_ (index i l2) 
                else nil) | i < n].


(***** But we need to define this: ******)

(* A "reduction spec" packages a lens with the reduction data *)
Inductive red_spec n : Type :=
  | RSinit (i : 'I_n) (x : data) (p : proc)
  | RSret (i : 'I_n) (x : data)  
  | RScomm (i j : 'I_n) (x : data) (pi : proc) (pj : data -> proc).

Definition red_spec_lens n (r : red_spec n) : seq 'I_n :=
  match r with
  | RSinit i _ _ => [:: i]
  | RSret i _ => [:: i]
  | RScomm i j _ _ _ => [:: i; j]
  end.

(* Collect all applicable reductions from a process tuple *)
Definition applicable_reds n (ps : n.-tuple proc) : seq (red_spec n) :=
  (* For each i, check if Init/Ret applies, or if Send/Recv has matching partner *)
  ...

(* Key property: applicable reductions are pairwise disjoint *)
Lemma applicable_pairwise_disjoint n (ps : n.-tuple proc) :
  let rs := applicable_reds ps in
  forall r1 r2, r1 \in rs -> r2 \in rs -> r1 <> r2 ->
  lens_disjoint (red_spec_lens r1) (red_spec_lens r2).

(* Then we can have this: *)

Lemma step_sound n (ps : n.-tuple proc) :
  let res := [tuple step ps nil i | i < n] in
  rstep ps (map_tuple (fun r => r.1.1) res) (map_tuple (fun r => r.1.2) res).
Proof.
(* 1. Collect all applicable reductions *)
pose rs := applicable_reds ps.

(* 2. Show each reduction in rs produces a valid rred *)
have Hvalid : forall r, r \in rs -> 
  rred (red_spec_lens r) (extract (red_spec_lens r) ps) ... .

(* 3. The applicable reductions are pairwise disjoint *)
have Hdisj := applicable_pairwise_disjoint ps.

(* 4. Induction on the list of applicable reductions *)
elim: rs Hvalid Hdisj => [|r rs' IH] Hvalid Hdisj.
- (* No applicable reductions: step does nothing, use rrefl *)
  ...
  exact: rrefl.
- (* r :: rs': compose r with the rest *)
  apply: rtrans.
  + (* First do the reductions in rs' *)
    apply: IH.
    * move=> r' Hr'; exact: Hvalid.
    * (* rs' still pairwise disjoint *) ...
  + (* Then do reduction r - disjoint from all of rs' *)
    apply: rone.
    (* r is disjoint from everything in rs', so extract is unchanged *)
    ...
Qed.

*)

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


(* Soundness: step implements rstep *)
Lemma step_sound n (ps : n.-tuple proc) :
  let res := [tuple step ps nil i | i < n] in
  rstep ps (map_tuple (fun r => r.1.1) res) (map_tuple (fun r => r.1.2) res).
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
    apply.
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
    pose pss' := pss `\ i `\ Ordinal jn.
    have H': pss' `<` pss.
      exact/(fsub_proper_trans (B:=pss `\ i))/fproperD1/Hi/fsubD1set.
    apply: (rtrans (IH _ H' _)); last 3 first.
    * move=> k k' ps' traces H.
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
          move: (rcomm i (Ordinal jn) x p pj).
          rewrite (_ : [tuple Send _ _ _; _] = extract [tuple i; Ordinal jn] ps);
            last by apply/val_inj => /=; rewrite Hpi (tnth_nth Fail) Hpj.
          move=> Hr.
          by rewrite -(eqP jk) -(Hpss _ _ _ _ Hr) Hi /step Hpj -tnth_nth Hpi eqxx.
        by rewrite !inE eq_sym jk eq_sym ik.
      apply.
    * apply: eq_from_tnth => k; rewrite !(tnth_mktuple, tnth_map) /=.
      rewrite !inE !(eq_sym k) andbCA.
      have [<- | ik] /= := eqVneq i k.
        by rewrite Hi /step -tnth_nth Hpi Hpj eqxx.
      have [<- |] //= := eqVneq (Ordinal jn) k.
      move: (rcomm i (Ordinal jn) x p pj).
      rewrite (_ : [tuple Send _ _ _; _] = extract [tuple i; Ordinal jn] ps);
        last by apply/val_inj => /=; rewrite Hpi (tnth_nth Fail) Hpj.
      move=> Hr.
      by rewrite -(Hpss _ _ _ _ Hr) Hi /step Hpj -tnth_nth Hpi eqxx.
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
    pose pss' := pss `\ i `\ Ordinal jn.
    have H': pss' `<` pss.
      exact/(fsub_proper_trans (B:=pss `\ i))/fproperD1/Hi/fsubD1set.
    apply: (rtrans (IH _ H' _)); last 3 first.
    * move=> k k' ps'' traces H.
      rewrite !inE.
      have [kj|kj] := eqVneq k (Ordinal jn).
        (* k = Ordinal jn: H3 gives Send k' x pi = Send i v pj', so k' = i *)
        inversion H; subst.
        move: H3; rewrite (tnth_nth Fail) Hpj => -[] k'i _ _.
        by rewrite (val_inj k'i) eqxx andbF.
      have [ki|_] := eqVneq k i.
        (* k = i: H3 gives Send k' x pi = Recv j f, contradiction *)
        by inversion H; subst; rewrite Hpi in H3.
      have [k'j|_] := eqVneq k' (Ordinal jn).
        (* k' = Ordinal jn: H4 gives Recv k pj = Send i v pj', contradiction *)
        by inversion H; subst; rewrite (tnth_nth Fail) Hpj in H4.
      have [k'i|k'i] := eqVneq k' i.
        (* k' = i: rcomm gives k = Ordinal jn *)
        inversion H; subst.
        move: H4; rewrite Hpi => -[] kj'.
        by move/eqP: kj; elim; apply/val_inj.
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
          move: (rcomm (Ordinal jn) i v pj' f).
          rewrite (_ : [tuple Send _ _ _; _] = extract [tuple Ordinal jn; i] ps);
            last by apply/val_inj => /=; rewrite (tnth_nth Fail) Hpj Hpi.
          move=> Hr.
          by rewrite (Hpss _ _ _ _ Hr) Hi /step Hpj -tnth_nth Hpi eqxx.
        case/boolP: (i == k) => [/eqP <-|ik] /=.
          by rewrite Hi /step -tnth_nth Hpi Hpj eqxx.
        by rewrite !inE eq_sym jk eq_sym ik.
      apply.
    * apply: eq_from_tnth => k; rewrite !(tnth_mktuple, tnth_map) /=.
      rewrite !inE !(eq_sym k).
      have [<- | jk] /= := eqVneq (Ordinal jn) k.
        move: (rcomm (Ordinal jn) i v pj' f).
        rewrite (_ : [tuple Send _ _ _; _] = extract [tuple Ordinal jn; i] ps);
          last by apply/val_inj => /=; rewrite (tnth_nth Fail) Hpj Hpi.
        move=> Hr.
        by rewrite (Hpss _ _ _ _ Hr) Hi /step Hpj -tnth_nth Hpi eqxx.
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
    apply.
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

