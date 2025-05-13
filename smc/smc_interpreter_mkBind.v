From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
Require Import Reals.
From mathcomp Require Import Rstruct ring.
Require Import ssrR Reals_ext realType_ext logb ssr_ext ssralg_ext bigop_ext.
Require Import fdist proba jfdist_cond entropy smc graphoid.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(*     Interpreter for Secure Multiparty Protocols                            *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope vec_ext_scope.

Reserved Notation "u *d w" (at level 40).
Reserved Notation "u \*d w" (at level 40).

Section interp.
Variable data : eqType.
Inductive proc : Type -> Type :=
  | Send : nat -> data -> proc unit
  | Recv : nat -> proc data
  | Ret A : A -> proc A
  | Bind A B : proc A -> (A -> proc B) -> proc B
  | Fail A : proc A.

Arguments Fail {A}.

Fixpoint mkBind A (p : proc A) : proc A :=
  match p in proc B return B = A -> proc A with
  | Send n v => fun H => eq_rect _ proc (Bind (Send n v) (@Ret _)) _ H
  | Recv n => fun H => eq_rect _ proc (Bind (Recv n) (@Ret _)) _ H
  | Bind C _ m g => fun H0 =>
      if m is Bind _ _ _ _ then
        match mkBind m in proc D return (D = C) -> proc A with
        | Bind _ _ m f => fun H =>
          eq_rect _ proc
                  (Bind m (fun x => Bind (eq_rect _ proc (f x) _ H) g)) _ H0
        | m' => fun H => eq_rect _ proc (Bind m' g) _ H0
        end erefl
      else p
  | p => fun H => p
  end erefl.

Fixpoint interp h (ps : seq (proc data)) : seq (proc data) :=
  if h is h.+1 then
    let step A (yes : proc data -> A) (no : proc data -> A) i :=
      let p := nth Fail ps i in
      match mkBind p in proc C return (C = data) -> A with
      | Bind _ B (Send dst _) next => fun H =>
        if mkBind (nth Fail ps dst) is Bind _ _ (Recv frm) _ then
          if frm == i then yes (eq_rect B proc (next tt) _ H) else no p
        else no p
      | Bind _ B (Ret _ v) f => fun H => yes (eq_rect _ proc (f v) _ H)
      | _ => fun _ => no
       (match mkBind p in proc A return (A = data) -> proc data with
        | Bind _ B (Recv frm) f => fun H =>
          if mkBind (nth Fail ps frm) is Bind _ _ (Send dst v) _ then
            if dst == i then eq_rect B proc (f v) _ H else p
          else p
        | _ => fun H => p end erefl)
      end erefl
    in 
    if has (step bool (fun=>true) (fun=>false)) (iota 0 (size ps)) then
      let ps' := map (step (proc data) idfun idfun) (iota 0 (size ps))
      in interp h ps'
    else
      ps
  else ps.

End interp.

Arguments Fail {data A}.
Arguments Ret {data A}.
Arguments Recv {data}.
Arguments Send {data}.

Notation "m >>= f" := (Bind m f) (at level 49).
Notation "'do' x <- m ; e" := (Bind m (fun x => e))
  (at level 60, x name, m at level 200, e at level 60, only parsing).
Notation "'do' x : T <- m ; e" := (Bind m (fun x : T => e))
  (at level 60, x name, m at level 200, e at level 60, only parsing).
Notation "m >> f" := (Bind m (fun _ => f)) (at level 49).

Section scalar_product.
Variable TX VX : ringType.
Variable dotproduct : VX -> VX -> TX.
Notation "u *d w" := (dotproduct u w).

Definition alice : nat := 0.
Definition bob : nat := 1.
Definition coserv : nat := 2.
Definition data := option (TX + VX).
Definition one x : data := Some (inl x).
Definition vec x : data := Some (inr x).
Notation proc := (proc data).
Definition Recv_one frm : proc TX :=
  Recv frm >>= fun x => if x is Some (inl v) then Ret v else Fail.
Definition Recv_vec frm : proc VX :=
  Recv frm >>= fun x => if x is Some (inr v) then Ret v else Fail.

Definition palice (xa : VX) : proc data :=
  do sa <- Recv_vec coserv;
  do ra <- Recv_one coserv;
  Send bob (vec (xa + sa)) >>
  do xb' <- Recv_vec bob;
  do t <- Recv_one bob;
  Ret (one (t - (xb' *d sa) + ra)).
Definition pbob (xb : VX) : proc data :=
  do sb <- Recv_vec coserv;
  do yb <- Recv_one coserv;
  do rb <- Recv_one coserv;
  do xa' <- Recv_vec alice;
  let t := xa' *d xb + rb - yb in
  Send alice (vec (xb + sb)) >> Send alice (one t) >> Ret (one yb).
Definition pcoserv (sa sb: VX) (ra yb: TX) : proc data :=
  Send alice (vec sa) >>
  Send alice (one ra) >>
  Send bob (vec sb) >>
  Send bob (one yb) >>
  Send bob (one (sa *d sb - ra)) >> Ret None.

Variables (sa sb: VX) (ra yb: TX) (xa xb: VX).
Definition scalar_product h :=
  interp h [:: palice xa; pbob xb; pcoserv sa sb ra yb].

Goal scalar_product 16 = [:: Fail; Fail; Fail].
cbv -[GRing.add GRing.opp].
rewrite /scalar_product.
rewrite (lock (14 : nat)) /=.
rewrite -lock (lock (12 : nat)) /=.
rewrite -lock (lock (10 : nat)) /=.
rewrite -lock (lock (8 : nat)) /=.
rewrite -lock (lock (6 : nat)) /=.
rewrite -lock (lock (4 : nat)) /=.
rewrite -lock (lock (2 : nat)) /=.
rewrite -lock /=.
Abort.

Lemma scalar_product_ok :
  scalar_product 16 =
  [:: Ret (one ((xa + sa) *d xb + (sa *d sb - ra) - yb - (xb + sb) *d sa + ra));
      Ret (one yb); Ret None].
Proof. reflexivity. Qed.
End scalar_product.
