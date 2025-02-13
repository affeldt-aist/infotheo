(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg poly polydiv matrix.

(**md**************************************************************************)
(* # Euclidean algorithm for decoding                                         *)
(*                                                                            *)
(* This file contains a formalization of the Euclidean algorithm for          *)
(* decoding. It follows the presentation in:                                  *)
(* - Robert McEliece, The Theory of Information and Coding, Cambridge         *)
(*   University Press, 2002.                                                  *)
(* It used to formalize decoders for Reed-Solomon and BCH codes (see the      *)
(* ecc_classic directory.                                                     *)
(*                                                                            *)
(* The formalization is explained Sect. 5.2 of:                               *)
(* - R. Affeldt, J. Garrigue, T. Saikawa, A Library for Formalization of      *)
(* Linear Error-correcting Codes, Journal of Automated Reasoning 67(3):28     *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Lemma pair_ind (P : nat -> Type) :
  P O -> P 1%nat ->
  (forall m, P m * P m.+1 -> P m.+2) ->
  forall m, P m.
Proof.
move=> P0 P1 H m.
suff : (P m * P m.+1)%type by case.
elim: m => // m [H1 H2]; split; by [assumption | apply H].
Qed.

Module Euclid.

Section euclid_algo.

Variable (F : fieldType).
Variable r0 r1 : {poly F}.
(* r0 to be init with 'X^t.*2, r1 with the syndrome *)

Fixpoint r i :=
  if i is i1.+1 then
    if i1 is i0.+1 then r i0 %% r i1
    else r1
  else r0.

Definition q k :=
  if k is k1.+1 then
    if k1 is k0.+1 then r k0 %/ r k1
    else 0
  else 0.

Lemma qE k : q k.+2 = r k %/ r k.+1.
Proof. by []. Qed.

Lemma rE k : r k = q k.+2 * r k.+1 + r k.+2.
Proof. by rewrite /= -divp_eq. Qed.

Section uv_sect.

Variable P0 P1 : {poly F}.

Fixpoint uv k :=
  if k is k1.+1 then
    if k1 is k0.+1 then - q k * uv k1 + uv k0
    else P1
  else P0.

Lemma uvE k : uv k.+2 = - q k.+2 * uv k.+1 + uv k.
Proof. by []. Qed.

End uv_sect.

Definition v0 : {poly F} := 0.
Definition v1 : {poly F} := 1.
Definition v k := uv v0 v1 k.

Definition u0 : {poly F} := 1.
Definition u1 : {poly F} := 0.
Definition u k := uv u0 u1 k.

(* McEliece, p.245, table 9.2, slight difference *)
Lemma relationA k : v k.+1 * r k - v k * r k.+1 = (- 1)^+k *: r0.
Proof.
elim: k => [|k IH].
  by rewrite /= /v0 mul0r subr0 expr0 scale1r /v1 mul1r.
rewrite {1}[k.+1]lock [in X in X * _ - _ = _]/= -lock.
rewrite {5}[k.+1]lock [in X in _ - _ * X= _]/= -lock.
move/eqP: (divp_eq (r k) (r k.+1)).
rewrite addrC -subr_eq => /eqP <-.
rewrite mulrDl mulrDr opprD addrA.
rewrite mulrN mulNr opprK addrC !addrA mulNr mulrC mulrAC subrr add0r.
by rewrite exprS -scalerA scaleN1r -IH opprB.
Qed.

(* McEliece, p.245, table 9.2, slight difference *)
Lemma relationB k : u k.+1 * r k - u k * r k.+1 = (- 1)^+k.+1 *: r1.
Proof.
elim: k => [|k IH].
  by rewrite /= /u1 /u0 mul0r add0r mul1r expr1 scaleN1r.
rewrite {1}[k.+1]lock [in X in X * _ - _ = _]/= -lock.
rewrite {5}[k.+1]lock [in X in _ - _ * X= _]/= -lock.
move/eqP: (divp_eq (r k) (r k.+1)).
rewrite addrC -subr_eq => /eqP <-.
rewrite mulrDl mulrDr opprD addrA.
rewrite mulrN mulNr opprK addrC !addrA mulNr mulrC mulrAC subrr add0r.
by rewrite exprS -scalerA scaleN1r -IH opprB.
Qed.

(* McEliece, p.245, table 9.2, relation C *)
Lemma vu i : v i.+1 * u i - v i * u i.+1 = (- 1)^+i.
Proof.
elim: i => [|k IH].
  by rewrite /= expr0 /v1 mul1r /u0 /v0 mul0r subr0.
rewrite /v /u 2!uvE.
transitivity ((- q k.+2 * v k.+1) * u k.+1 + v k * u k.+1 +
  v k.+1 * (q k.+2 * u k.+1) - v k.+1 * u k).
  rewrite mulrDl -3!addrA; congr (_ + (_ + _)).
  rewrite mulrDr opprD; congr (_ - _).
  by rewrite mulNr mulrN opprK.
rewrite exprS -IH [in RHS]mulNr mul1r opprD opprK [in RHS]addrC; congr (_ - _).
rewrite addrC addrA -[RHS]add0r; congr (_ + _).
by rewrite mulrC -mulrA (mulrC (v k.+1)) mulrA 2!mulNr subrr.
Qed.

(* McEliece, p.245, table 9.2, relation D *)
Lemma ruv i : r i = u i * r 0 + v i * r 1.
Proof.
elim/pair_ind: i => [||k [Hk1 Hk]].
  by rewrite mul1r /= /v0 mul0r addr0.
  by rewrite /= /v1 mul1r mul0r add0r.
rewrite /v uvE.
transitivity (- q k.+2 * (u k.+1 * r 0 + v k.+1 * r 1) + (u k * r 0 + v k * r 1)).
  by rewrite -Hk -Hk1 (rE k) addrA addrC [in X in _ + X]addrC mulNr subrr addr0.
rewrite mulrDl mulrDr mulrA -2!addrA; congr (_ + _).
rewrite mulrDl [in RHS]addrC mulrA -addrA; congr (_ + _); by rewrite addrC.
Qed.

Lemma ltn_size_r i : 1 <= i -> r i != 0 -> size (r i.+1) < size (r i).
Proof.
elim: i => // -[_ _ r10|k IH _ rn2]; first by rewrite /= ltn_modp.
by rewrite {1}[k.+2]lock [in X in X < _]/= -lock ltn_modp.
Qed.

Hypothesis r1_r0 : size r1 <= size r0.

Lemma leq_size_r n : (forall k, k < n -> r k != 0) ->
  size (r n) <= size (r 0) - n.-1.
Proof.
elim/pair_ind: n => [_|_|n [H1 H2 H]].
  by rewrite /= subn0.
  by rewrite /= subn0.
rewrite [n.+1]lock /= -lock.
move: (H _ (ltnSn n.+1)) => /(ltn_modpN0 (r n)) K.
have rk_neq0 k : k < n.+1 -> r k != 0 by move=> kn; apply H; rewrite ltnW.
move: (leq_trans K (H2 rk_neq0)); rewrite [in X in _ < X -> _]/= => ltn_size.
rewrite subnS -ltnS prednK //; exact: leq_ltn_trans ltn_size.
Qed.

End euclid_algo.

End Euclid.

Section euclid_stop.

Variables (F : fieldType) (n : nat) (y : 'rV[F]_n) (t : nat).
Variable r0 r1 : {poly F}.

Local Notation "'r'" := (Euclid.r r0 r1).
Local Notation "'q'" := (Euclid.q r0 r1).

Definition euclid_cont := [pred k | [forall i : 'I_k.+1, t < size (r i)]].

Lemma euclid_next i j : ~~ euclid_cont i && (i <= j) ==> ~~ euclid_cont j.
Proof.
apply/implyP => /andP [H1 H2].
apply: contra H1 => /forallP /= H1.
apply/forallP => /= x.
have @b : 'I_j.+1 by exists x; rewrite ltnS (leq_trans _ H2) // -ltnS.
by rewrite (_ : r x = r b).
Qed.

Lemma euclid_back i j : euclid_cont j && (i <= j) ==> euclid_cont i.
Proof.
apply/implyP => /andP [/forallP H1 H2].
apply/forallP => /= x.
have @b : 'I_j.+1 by exists x; rewrite ltnS (leq_trans _ H2) // -ltnS.
by rewrite (_ : r x = r b).
Qed.

Lemma ex_euclid_cont (tr0 : t < size r0) : exists k, euclid_cont k.
Proof.
exists O; apply/forallP => /= j.
by move: (ltn_ord j); rewrite ltnS leqn0 => /eqP ->.
Qed.

Lemma euclid_cont_size_r (r1_eq_r0 : size r1 <= size r0) :
  forall k, euclid_cont k -> k <= size (r 0).
Proof.
case/boolP : [exists k : 'I_(size r0).+1, (size (r k)) <= t] =>
  [/existsP[k Hk i Hi]|].
  have Pk : ~~ euclid_cont k.
    rewrite /= negb_forall; apply/existsP; exists ord_max => /=.
    by rewrite -ltnNge.
  have : forall j, euclid_cont j -> j < k.
    move=> j Pj.
    rewrite ltnNge; apply: contra Pk => kj.
    move: (euclid_back k j) => /implyP; rewrite Pj kj; by apply.
  move/(_ i Hi) => ik.
  rewrite /=.
  move: (ltn_ord k).
  rewrite ltnS.
  apply: (leq_trans).
  by rewrite -ltnS ltnW.
rewrite negb_exists => /forallP abs i /forallP Pi.
move: (Euclid.leq_size_r (r1_eq_r0)) => size_r.
have {abs} : forall k : nat, k < (size r0).+1 -> r k != 0.
  move=> k Hk.
  rewrite -size_poly_eq0.
  rewrite /= in abs.
  move: (abs (Ordinal Hk)) => Ht.
  rewrite -ltnNge /= in Ht.
  rewrite -lt0n.
  by rewrite (leq_trans _ Ht).
move/size_r => {size_r}.
rewrite subnn leqn0 leqNgt => /eqP size_r0.
apply/negP => abs.
have {}abs : (size (r 0)).+1 < i.+1 by [].
move: (Pi (Ordinal abs)).
by rewrite /= size_r0 leqn0 -(negbK (_ == _)) -lt0n.
Qed.

Definition stop' (tr0 : t < size r0) (r1_leq_r0 : size r1 <= size r0) :=
  ex_maxn (ex_euclid_cont tr0) (euclid_cont_size_r r1_leq_r0).
Definition stop := if Bool.bool_dec (t < size r0) true is left H1 then
                     if Bool.bool_dec (size r1 <= size r0) true is left H2 then
                       (stop' H1 H2).+1
                     else O else O.

Lemma stop'_is_before (tr0 : t < size r0) (r1_leq_r0 : size r1 <= size r0) :
  t < size (r (stop' tr0 r1_leq_r0)).
Proof.
rewrite /stop'; case: ex_maxnP => i Hi _.
move: Hi; by rewrite /euclid_cont => /forallP /(_ (Ordinal (ltnSn i))).
Qed.

Lemma stop_is_after (tr0 : t < size r0) (r1_leq_r0 : size r1 <= size r0) :
  size (r stop) <= t.
Proof.
rewrite /stop.
case: Bool.bool_dec => H1; last by rewrite tr0 in H1.
case: Bool.bool_dec => H2; last by rewrite r1_leq_r0 in H2.
rewrite /stop'; case: ex_maxnP => i Hi ij.
rewrite leqNgt; apply/negP => abs.
suff /ij : euclid_cont i.+1 by rewrite ltnn.
apply/forallP => /= x.
have [->//|Hx] := eqVneq x ord_max.
have {}Hx : x < i.+1 by rewrite ltn_neqAle Hx /= -ltnS.
by move/forallP : Hi => /(_ (Ordinal Hx)).
Qed.

Lemma ltn_size_r_stop l (tr0 : t < size r0) (r1_leq_r0 : size r1 <= size r0) :
  1 <= l < stop -> size (r l.+1) < size (r l).
Proof.
move=> lEu.
apply Euclid.ltn_size_r => //.
  by case/andP : lEu.
case/andP : lEu => l0.
rewrite /stop.
case: Bool.bool_dec => H1; last by rewrite tr0 in H1.
case: Bool.bool_dec => H2; last by rewrite r1_leq_r0 in H2.
rewrite /stop'; case: ex_maxnP => i Hi H li.
move/forallP in Hi; move: (Hi (Ordinal li)).
rewrite /= ltnNge; apply: contra => /eqP ->.
by rewrite size_poly0.
Qed.

Lemma r10_stop'0 (tr0 : t < size r0) (r1_leq_r0 : size r1 <= size r0) :
  r1 = 0 -> stop' tr0 r1_leq_r0 = O.
Proof.
move=> r10; rewrite /stop'; case: ex_maxnP => i Pi Hi.
have P1 : ~~ euclid_cont 1%nat.
  rewrite /= negb_forall.
  apply/existsP; exists (lift ord0 ord0).
  by rewrite /= r10 size_poly0 leqn0 -lt0n.
case: i Pi Hi => // i Pi Hi.
move: (euclid_next 1 i.+1).
by rewrite P1 Pi.
Qed.

Lemma q0 : q 0 = 0. Proof. by []. Qed.

Lemma q1 : q 1 = 0. Proof. by []. Qed.

Lemma q2 : q 2 = r0 %/ r1. Proof. by []. Qed.

(* NB: used in cyclic_decoding.v *)
Lemma size_rstop (tr0 : t < size r0) (r1_leq_r0 : size r1 <= size r0) :
  size (r stop) <= t.
Proof.
rewrite /stop.
case: Bool.bool_dec => H1; last by rewrite tr0 in H1.
case: Bool.bool_dec => H2; last by rewrite r1_leq_r0 in H2.
rewrite /stop'.
case: ex_maxnP => i Pi Hi.
rewrite leqNgt.
apply/negP => abs.
have Pi1 : euclid_cont i.+1.
  rewrite /=.
  apply/forallP => x.
  move: (ltn_ord x).
  rewrite ltnS leq_eqVlt.
  case/orP => [/eqP ->{x} // | xi].
  rewrite /euclid_cont /= in Pi.
  move/forallP in Pi.
  by move: (Pi (Ordinal xi)).
move: (Hi _ Pi1).
by rewrite ltnn.
Qed.

Local Notation "'v'" := (Euclid.v r0 r1).

Lemma ltn_size_r_stop_r0 l (tr0 : t < size r0) (r1_leq_r0 : size r1 <= size r0) :
  1 <= l < stop -> size (r l.+1) < size (r 0).
Proof.
elim: l => // -[_ /=|l IH H].
  rewrite /stop.
  case: Bool.bool_dec => H1; last by rewrite tr0 in H1.
  case: Bool.bool_dec => H2; last by rewrite r1_leq_r0 in H2.
  rewrite /stop'; case: ex_maxnP => i Hi ij i1.
  move: Hi => /forallP /(_ (Ordinal i1)) H.
  by rewrite (leq_trans _ r1_leq_r0) // ltn_modpN0 // -size_poly_eq0 -lt0n (leq_trans _ H).
rewrite (leq_trans (ltn_size_r_stop _ _ H)) // ltnW //.
apply IH => /=.
simpl in H.
by rewrite ltnW.
Qed.

Lemma leq_size_v_incr i (tr0 : t < size r0) (r1_leq_r0 : size r1 <= size r0) :
  i < stop -> size (v i) <= size (v i.+1).
Proof.
elim: i => [? /= | i ih istop].
  by rewrite /Euclid.v0 /Euclid.v1 size_poly0 size_poly1.
rewrite {2}/Euclid.v Euclid.uvE.
do 2 rewrite -/(Euclid.v _ _ _).
have [->|vi1_eq0] := eqVneq (v i.+1) 0; first by rewrite size_poly0.
destruct i.
  rewrite /= /Euclid.v0 /Euclid.v1 size_poly1 addr0 mulr1 size_opp.
  have r10 : r1 != 0.
    move: istop.
    rewrite /stop.
    case: Bool.bool_dec => H1; last by rewrite tr0 in H1.
    case: Bool.bool_dec => H2; last by rewrite r1_leq_r0 in H2.
    rewrite /stop'; case: ex_maxnP => l Hl Hi il.
    move: Hl => /forallP /(_ (Ordinal il)) H.
    by rewrite -size_poly_eq0 -lt0n (leq_trans _ H).
  rewrite size_divp //.
  rewrite -subn1 subnBA; last by rewrite lt0n size_poly_eq0.
  by rewrite addnC addSn add0n subSn.
have ri20 : r i.+2 != 0.
    move: istop.
    rewrite /stop.
    case: Bool.bool_dec => H1; last by rewrite tr0 in H1.
    case: Bool.bool_dec => H2; last by rewrite r1_leq_r0 in H2.
    rewrite /stop'; case: ex_maxnP => l Hl Hi il.
    move: Hl => /forallP /(_ (Ordinal il)) H.
    by rewrite -size_poly_eq0 -lt0n (leq_trans _ H).
have qi3 : 1 < size (q i.+3).
  rewrite {1}Euclid.qE size_divp //.
  rewrite -subn1 subnBA ?lt0n ?size_poly_eq0 // addn1 subSn; last first.
    by rewrite ltnW // ltn_size_r_stop //= ltnW.
  by rewrite ltnS subn_gt0 ltn_size_r_stop //= ltnW.
rewrite [in X in _ <= X]size_addl.
  rewrite mulNr size_opp size_mul //; last first.
    by rewrite -size_poly_eq0 -lt0n (leq_trans _ qi3).
  rewrite -subn1 -addnBA; last by rewrite lt0n size_poly_eq0.
  rewrite (@leq_trans (1 + (size (v i.+2) - 1))) //.
    by rewrite add1n subn1 prednK // lt0n size_poly_eq0.
  by rewrite leq_add2r (leq_trans _ qi3).
rewrite mulNr size_opp.
rewrite size_mul // -?size_poly_eq0 -?lt0n ?(leq_trans _ qi3) //.
rewrite -subn1 -addnBA; last by rewrite lt0n size_poly_eq0.
rewrite (@leq_ltn_trans (1 + (size (v i.+2) - 1))) //; last first.
  by rewrite ltn_add2r.
rewrite add1n subn1 prednK // ?lt0n ?size_poly_eq0 // ih //.
by rewrite ltnW.
Qed.

Lemma relationF k (tr0 : t < size r0) (r1_leq_r0 : size r1 <= size r0) :
  k < stop -> ((size (v k.+1)).-1 + (size (r k)).-1 = (size (r 0)).-1)%N.
Proof.
elim: k => [?|k IH H].
  by rewrite /= /Euclid.v1 /Euclid.v0 size_poly1 add0n.
rewrite {1}/Euclid.v Euclid.uvE -2!/(Euclid.v _ _ _) Euclid.qE.
have rk1_neq0 : r k.+1 != 0.
  move: H; rewrite /stop.
  case: Bool.bool_dec => H1; last by rewrite tr0 in H1.
  case: Bool.bool_dec => H2; last by rewrite r1_leq_r0 in H2.
  rewrite /stop'; case: ex_maxnP => i Hi ij ki.
  move: Hi => /forallP/(_ (Ordinal ki)) H.
  by rewrite -size_poly_eq0 -lt0n (leq_trans _ H).
have rk_neq0 : r k != 0.
  move: H; rewrite /stop.
  case: Bool.bool_dec => H1; last by rewrite tr0 in H1.
  case: Bool.bool_dec => H2; last by rewrite r1_leq_r0 in H2.
  rewrite /stop'; case: ex_maxnP => i Hi ij ki.
  move: Hi => /forallP/(_ (Ordinal (ltnW ki))) H.
  by rewrite -size_poly_eq0 -lt0n (leq_trans _ H).
have vk1_neq0 : v k.+1 != 0.
  destruct k; first by rewrite /= oner_neq0.
  rewrite -size_poly_eq0.
  apply/eqP => abs.
  move: {IH}(IH (ltnW H)); rewrite abs add0n => /(congr1 (fun x => x.+1)).
  rewrite prednK; last by rewrite lt0n size_poly_eq0.
  rewrite prednK; last by rewrite (leq_trans _ tr0).
  apply/eqP; rewrite ltn_eqF //.
  destruct k.
    move: abs.
    rewrite /= addr0 mulr1 size_opp => /eqP.
    rewrite size_poly_eq0 divp_eq0 ltnNge r1_leq_r0 orbF (negbTE rk_neq0) orbF.
    rewrite -size_poly_eq0 => abs.
    exfalso.
    move/eqP : abs; apply/eqP.
    by rewrite -lt0n (leq_trans _ tr0).
  by rewrite (ltn_size_r_stop_r0) //= ltnW // ltnW.
rewrite size_addl; last first.
  rewrite mulNr size_opp.
  destruct k.
    rewrite /= /Euclid.v0 /Euclid.v1 size_poly0 mulr1 lt0n size_poly_eq0 divp_eq0.
    by rewrite ltnNge r1_leq_r0 orbF (negbTE rk1_neq0) orbF.
  have q_k3 : 1 < size (q k.+3).
    rewrite Euclid.qE size_divp // -subn1 subnBA; last by rewrite lt0n size_poly_eq0.
    rewrite addn1 subSn; last by rewrite ltnW // ltn_size_r_stop //= ltnW.
    by rewrite ltnS subn_gt0 ltn_size_r_stop //= ltnW.
  rewrite -Euclid.qE size_mul //; last first.
    by rewrite -size_poly_eq0 -lt0n (leq_trans _ q_k3).
  rewrite -subn1 -addnBA; last by rewrite lt0n size_poly_eq0.
  rewrite (@leq_ltn_trans (1 + (size (v k.+2)).-1))%N //.
    rewrite add1n prednK; last by rewrite lt0n size_poly_eq0.
    by rewrite leq_size_v_incr // ltnW.
  rewrite add1n subn1 prednK; last by rewrite lt0n size_poly_eq0.
  rewrite -subn1 addnBA ?lt0n ?size_poly_eq0 // (@leq_ltn_trans (1 + size (v k.+2) - 1)) //.
    by rewrite add1n subn1.
  by rewrite -addnBA ?lt0n ?size_poly_eq0 // -addnBA ?lt0n ?size_poly_eq0 // ltn_add2r.
have H1 : size (r k.+1) <= size (r k).
  destruct k => //.
  by rewrite ltnW // ltn_size_r_stop //= ltnW.
rewrite size_mul //; last by rewrite oppr_eq0 divpN0.
rewrite size_opp size_divp // -subn2.
set a := size (r k.+1).
rewrite addnC addnBA; last first.
  rewrite {}/a -subn1 subnBA; last by rewrite lt0n size_poly_eq0.
  by rewrite addn1 subSn // addSn ltnS addn_gt0 (lt0n (size (v k.+1))) size_poly_eq0 vk1_neq0 orbT.
rewrite addnA subnKC; last by rewrite {}/a (leq_trans _ H1) // leq_pred.
rewrite -IH; last by rewrite ltnW.
rewrite -[in X in (_ = _ + X)%N]subn1 addnBA; last by rewrite lt0n size_poly_eq0.
rewrite [in RHS]addnC subn1 subn2; congr (_ .-1).
rewrite -subn1 -addnBA; last by rewrite lt0n size_poly_eq0.
by rewrite subn1.
Qed.

Lemma ltn_size_q' i (tr0 : t < size r0) (r1_ltn_r0 : size r1 < size r0) :
  i < stop -> r i.+1 != 0 -> 1 < size (q i.+2).
Proof.
move=> istop Hr; rewrite Euclid.qE.
case: i => [|i] in Hr istop *.
  by rewrite size_divp //= ltn_subRL addn1 prednK // lt0n size_poly_eq0.
rewrite size_divp // ltn_subRL addn1 prednK; last by rewrite lt0n size_poly_eq0.
by rewrite ltn_size_r_stop // ltnW.
Qed.

Lemma ltn_size_q i (tr0 : t < size r0) (r1_ltn_r0 : size r1 < size r0) :
  i.+1 < stop -> 1 < size (q i.+2).
Proof.
move=> istop.
apply: (ltn_size_q' tr0 r1_ltn_r0 (ltn_trans (ltnSn _) istop)).
move: istop.
rewrite /stop.
case: Bool.bool_dec => H1; last by rewrite tr0 in H1.
case: Bool.bool_dec => H2; last by rewrite (ltnW r1_ltn_r0) in H2.
rewrite ltnS /stop'.
case: ex_maxnP => l Hl Hi il.
have : euclid_cont i.+1 by move: (euclid_back i.+1 l); rewrite Hl il.
rewrite /euclid_cont /= => /forallP/(_ (Ordinal (ltnSn i.+1))).
rewrite -size_poly_eq0; by case: (size _).
Qed.

Lemma size_v01 : size (v 0) < size (v 1).
Proof. by rewrite /= /Euclid.v0 /Euclid.v1 size_poly0 size_poly1. Qed.

Lemma size_v12 (r1_leq_r0 : size r1 <= size r0) : r1 != 0 -> size (v 1) <= size (v 2).
Proof.
move=> r10.
rewrite /= /Euclid.v1 /Euclid.v0 addr0 mulr1 size_opp.
rewrite size_divp // -subn1 subnBA ?lt0n ?size_poly_eq0 // size_poly1.
by rewrite addnC -addnBA.
Qed.

Lemma size_v_incr_new i (tr0 : t < size r0) (r1_leq_r0 : size r1 <= size r0) :
  1 < i < stop -> size (v i) < size (v i.+1).
Proof.
case/andP => i1 istop.
move: (relationF tr0 r1_leq_r0 istop) => H1.
destruct i => //.
move: (relationF tr0 r1_leq_r0(ltnW istop)) => H2.
move: (ltn_size_r_stop).
have H3 : 0 < i < stop.
  destruct i => //=.
  by rewrite ltnW.
move/(_ _ tr0 r1_leq_r0 H3) => H4.
move: H1.
move/(congr1 (fun x => x.+1))/eqP.
Abort.

Lemma size_v_incr (tr0 : t < size r0) (r1_ltn_r0 : size r1 < size r0) i :
  i < stop -> size (v i) < size (v i.+1).
Proof.
elim: i => [_ /= | i ih istop].
  by rewrite /Euclid.v0 /Euclid.v1 size_poly0 size_poly1.
have Hq : 1 < size (q i.+2) by apply ltn_size_q.
move=> [:H1 H2].
rewrite /Euclid.v Euclid.uvE mulNr size_addl size_opp.
  rewrite size_mul; last 2 first.
    abstract: H1; by rewrite -size_poly_eq0 -leqn0 -ltnNge (ltn_trans _ Hq).
    abstract: H2. rewrite -size_poly_eq0  -leqn0 -ltnNge (leq_ltn_trans _ (ih _)) //.
    by rewrite (ltn_trans _ istop).
  by rewrite -subn1 ltn_subRL ltn_add2r.
rewrite size_mul // -subn1 ltn_subRL (@ltn_trans (1 + size (v i.+1))) //.
  by rewrite ltn_add2l ih // (ltn_trans _ istop).
by rewrite ltn_add2r.
Qed.

Lemma ltn_size_v (tr0 : t < size r0) (r1_ltn_r0 : size r1 < size r0) i :
  i.+1 < stop -> size (v i) < size (- q i.+2 * v i.+1).
Proof.
move=> istop.
have Hq : 1 < size (q i.+2) by apply ltn_size_q.
rewrite mulNr size_opp.
rewrite size_mul; last 2 first.
  by rewrite -size_poly_eq0 -leqn0 -ltnNge (ltn_trans _ Hq).
  rewrite -size_poly_eq0 -lt0n.
  by rewrite (leq_ltn_trans _ (@size_v_incr tr0 r1_ltn_r0 _ (ltn_trans (ltnSn _) istop))).
rewrite -subn1 ltn_subRL (@ltn_trans (1 + size (v i.+1))) // ?ltn_add2r //.
by rewrite ltn_add2l size_v_incr // (ltn_trans _ istop).
Qed.

Lemma size_v_sum (tr0 : t < size r0) (r1_ltn_r0 : size r1 < size r0) k :
  k < stop -> (size (v k.+1)).-1 = (\sum_(i < k.+1) (size (q i.+1)).-1)%N.
Proof.
elim: k => [_ | k IH kstop].
  by rewrite big_ord_recr /= big_ord0 /Euclid.v1 size_poly1 size_poly0.
transitivity ((size (q k.+2)).-1 + (size (v k.+1)).-1)%N; last first.
  rewrite {}IH ?(ltn_trans _ kstop) //.
  by rewrite [in RHS]big_ord_recr addnC.
rewrite {1}/Euclid.v Euclid.uvE size_addl; last by rewrite ltn_size_v.
rewrite mulNr size_opp.
have H1 : 0 < size (q k.+2) by rewrite (ltn_trans _ (ltn_size_q tr0 r1_ltn_r0 kstop)).
have H2 : 0 < size (v k.+1).
  by rewrite (leq_ltn_trans _ (@size_v_incr tr0 r1_ltn_r0 _ (ltn_trans (ltnSn _) kstop))).
rewrite size_mul -?size_poly_eq0 -?lt0n //.
suff : (forall a b, 0 < a -> 0 < b -> (a + b).-2 = a.-1 + b.-1)%N by apply.
case=> // a; case => // b _ _; by rewrite addSn addnS.
Qed.

Lemma size_r0_sum (tr0 : t < size r0) (r1_ltn_r0 : size r1 < size r0) l :
  l < stop ->
  (size (r 0)).-1 = (\sum_(k < l.+1) (size (q k.+1)).-1 + (size (r l)).-1)%nat.
Proof.
elim: l => [_ | l IH].
  by rewrite big_ord_recr big_ord0 /= size_poly0.
move=> lEu.
rewrite IH; last by rewrite (ltn_trans (ltnSn _) lEu).
transitivity ((\sum_(k < l.+1) (size (q k.+1)).-1 + (size (q l.+2)).-1 + (size (r l.+1)).-1)%N); last first.
  by rewrite [in RHS]big_ord_recr -addnA.
rewrite -addnA.
congr addn.
have H1 : 0 < size (q l.+2) by rewrite (ltn_trans _ (ltn_size_q tr0 r1_ltn_r0 lEu)).
  have {}lEu : is_true (0 < l.+1 < stop) by rewrite lEu.
rewrite Euclid.rE size_addl; last first.
  rewrite size_mul; last 2 first.
    by rewrite -size_poly_eq0 -lt0n.
    by rewrite -size_poly_eq0 -lt0n (leq_ltn_trans _ (ltn_size_r_stop tr0 (ltnW r1_ltn_r0) lEu)).
  suff : (forall a b c, 0 < b -> a < c -> (a < (b + c).-1))%nat.
    apply => //; by apply: (ltn_size_r_stop tr0 (ltnW r1_ltn_r0) lEu).
  clear.
  move=> a.
  case=> // b; case=> // c _ ac.
  by rewrite addSn /= ltn_addl.
rewrite size_mul; last 2 first.
  by rewrite -size_poly_eq0 -lt0n.
  by rewrite -size_poly_eq0 -lt0n (leq_ltn_trans _ (ltn_size_r_stop tr0 (ltnW r1_ltn_r0) lEu)).
suff : (forall a b, 0 < a -> 0 < b -> (a + b).-2 = a.-1 + b.-1)%nat.
  apply => //; by rewrite (leq_ltn_trans _ (ltn_size_r_stop tr0 (ltnW r1_ltn_r0) lEu)).
clear.
case=> // a; case => // b _ _.
by rewrite addSn addnS.
Qed.

(* NB: used in reed_solomon.v *)
Lemma leq_size_v (tr0 : t < size r0) (r1_ltn_r0 : size r1 < size r0) k :
  (size r0).-1 <= t.*2 -> k.-1 < stop -> (size (v k)).-1 <= t.
Proof.
move=> r0t.
case: k => [_|k].
  by rewrite /= /Euclid.v0 size_poly0.
move=> lEu.
rewrite /= in lEu.
rewrite size_v_sum //.
rewrite -(leq_add2l t) addnn.
move: (size_r0_sum tr0 r1_ltn_r0 lEu).
rewrite [in X in X = _ -> _]/= => H.
apply: (leq_trans _ r0t).
rewrite [in X in _ <= X]H.
rewrite addnC leq_add2l.
move: lEu.
rewrite /stop.
case: Bool.bool_dec => H1; last by rewrite tr0 in H1.
case: Bool.bool_dec => H2; last by rewrite (ltnW r1_ltn_r0) in H2.
rewrite /stop'; case: ex_maxnP => i Pi Hi l'i.
have : euclid_cont k.
  move: (euclid_back k i).
  by rewrite -ltnS Pi l'i.
move/forallP/(_ (Ordinal (ltnSn k))) => H'.
by rewrite -(leq_add2r 1) 2!addn1 prednK // (leq_ltn_trans _ H').
Qed.

End euclid_stop.

Section euclid_lemma.

(* see [McEliece 2002], 9.4 *)
Variables (F : fieldType).
Variable r0 r1 : {poly F}.
Hypothesis r1_leq_r0 : size r1 <= size r0.

Local Notation "'r'" := (Euclid.r r0 r1).
Local Notation "'v'" := (Euclid.v r0 r1).

(* McEliece, Lemma 2, p.245 *)
Lemma euclid_lemma p t : (p + t = size (r 0))%N ->
  let stop := stop t (r 0) (r 1) in
  size (v stop) <= p /\ size (r stop) <= t.
Proof.
move=> H.
case/boolP : (0 < size r0) => [Hr0|]; last first.
  rewrite -leqNgt leqn0 size_poly_eq0 => /eqP ?; subst r0.
  suff : p = O /\ t = O.
    case=> -> -> /=.
    rewrite /stop.
    case: Bool.bool_dec => [H1|_].
      exfalso.
      by rewrite size_poly0 ltnn in H1.
    by rewrite /= /Euclid.v0 size_poly0.
  move: H; rewrite size_poly0.
  by case: p.
move=> j.
case/boolP : (t < size r0) => Hnu; last first.
  have {Hnu} ?: p = O.
    move: Hnu.
    rewrite -H -leqNgt.
    by rewrite -{2}(add0n t) leq_add2r leqn0 => /eqP.
  subst p.
  rewrite {}/j.
  rewrite /stop.
  case: Bool.bool_dec => H1.
    exfalso.
    move: H1.
    by rewrite -H add0n ltnn.
  by rewrite /= /Euclid.v0 size_poly0 leqnn -H add0n.
split; last by apply: stop_is_after.
rewrite -(leq_add2r t) H.
move: (@relationF _ _ _ _ (stop' Hnu r1_leq_r0) Hnu r1_leq_r0).
rewrite /stop.
case: Bool.bool_dec => H1; last by rewrite Hnu in H1.
case: Bool.bool_dec => H2; last by rewrite r1_leq_r0 in H2.
rewrite (_ : H1 = Hnu); last by apply eq_irrelevance.
rewrite (_ : H2 = r1_leq_r0); last by apply eq_irrelevance.
rewrite ltnSn => /(_ isT).
rewrite -/(stop _ _) => /(congr1 (fun x => x.+1)).
rewrite prednK ?lt0n ?size_poly_eq0 //; last by rewrite -size_poly_eq0 -lt0n.
move => <-.
rewrite -ltnS.
move: (stop'_is_before Hnu r1_leq_r0) => Hsave; move: (Hsave).
rewrite -(ltn_add2l (size (v j))).
move/leq_trans; apply.
rewrite -addSn.
case/boolP : (size (v j) == O) => vs0.
  rewrite (eqP vs0) add0n.
  rewrite addSn addnC -2!addSn (leq_trans _ (leq_addr _ _)) // prednK //.
  by rewrite (leq_trans _ Hsave).
rewrite /j /stop.
case: Bool.bool_dec => H1'; last by rewrite Hnu in H1.
case: Bool.bool_dec => H2'; last by rewrite r1_leq_r0 in H2.
rewrite -(_ : Hnu = H1'); last by apply eq_irrelevance.
rewrite -(_ : r1_leq_r0 = H2'); last by apply eq_irrelevance.
rewrite -addnS leq_add // prednK // ?(leq_trans _ Hsave) // ?lt0n.
apply: contra vs0.
rewrite /j /stop.
case: Bool.bool_dec => H1''; last by rewrite Hnu in H1.
case: Bool.bool_dec => H2''; last by rewrite r1_leq_r0 in H2.
rewrite -(_ : Hnu = H1''); last by apply eq_irrelevance.
rewrite -(_ : r1_leq_r0 = H2'') //; by apply eq_irrelevance.
Qed.

Local Notation "'u'" := (Euclid.u r0 r1).

Variables V R U : {poly F}.
Hypotheses (v_neq0 : V != 0) (r1_neq0 : r1 != 0).

(* see [McEliece 2002], Theorem 9.5, p.246 *)
Lemma solve_key_equation m t :
  V * (r 1) = R + U * (r 0) ->
  size V <= m -> size R <= t ->
  (m + t = size r0)%N ->
  let j := stop t r0 r1 in
  exists k, k <> 0 /\ V = k * v j /\ R = k * r j.
Proof.
have r0_neq0 : r0 != 0.
  by rewrite -size_poly_eq0 -lt0n (leq_trans _ r1_leq_r0) // lt0n size_poly_eq0.
move=> key_eqn Hmu Hnu Hsize j'.
move: (euclid_lemma Hsize) => [H2 Hj].
set j := stop _ _ _ in H2, Hj.
move: (Euclid.ruv r0 r1 j) => E1.
have {}key_eqn : R = (- U) * r0 + V * r1 by rewrite key_eqn addrC mulNr addrK.
move/(congr1 (fun x => V * x)) : (E1); rewrite mulrDr !mulrA => E1'.
move/(congr1 (fun x => v j * x)) : (key_eqn); rewrite mulrDr !mulrA => key_eqn'.
have step1 : r j * V = R * v j.
  have [k Hk] : exists k, r j * V = R * v j + k * r0.
    exists (V * u j - v j * (- U)).
    rewrite mulrC {}E1'.
    move: key_eqn' => /eqP.
    rewrite addrC -subr_eq -(mulrA _ V) mulrCA mulrA => /eqP <-.
    by rewrite addrCA mulrN mulNr 2!opprK -mulrDl mulrC.
  have HrV : size (r j * V) < size r0.
    case/boolP : (r j == 0) => [/eqP->|rj0].
      by rewrite mul0r size_poly0 lt0n size_poly_eq0.
    case/boolP : (V == 0) => [/eqP ->|V_neq0].
      by rewrite mulr0 size_poly0 lt0n size_poly_eq0.
    rewrite size_mul; last 2 first.
      exact: rj0.
      exact V_neq0.
    rewrite -Hsize.
    rewrite prednK; last first.
      by rewrite ltn_addr // lt0n size_poly_eq0.
    by rewrite addnC leq_add.
  have HRv : size (R * v j) < size r0.
    case/boolP : (v j == 0) => [/eqP->|vj0].
      by rewrite mulr0 size_poly0 lt0n size_poly_eq0.
    case/boolP : (R == 0) => [/eqP->|R_neq0].
      by rewrite mul0r size_poly0 lt0n size_poly_eq0.
    rewrite size_mul; last 2 first.
      exact R_neq0.
      exact vj0.
    rewrite prednK; last first.
      by rewrite addnC ltn_addr // lt0n size_poly_eq0.
    by rewrite -Hsize addnC leq_add.
  case/boolP : (k == 0) => [/eqP k0|k0].
    move: Hk; by rewrite k0 mul0r addr0.
  exfalso.
  move/eqP : Hk.
  rewrite addrC -subr_eq.
  move/eqP/(congr1 (fun x : {poly F} => size x)).
  apply/eqP.
  rewrite ltn_eqF //.
  rewrite (leq_ltn_trans (size_add _ _)) // size_opp.
  rewrite (@leq_trans (size r0)) //.
    by rewrite gtn_max HrV.
  by rewrite size_mul // addnC -subn1 -addnBA ?lt0n ?size_poly_eq0 // leq_addr.
have step2 : u j * V = (-U) * v j.
  move: step1.
  rewrite [in X in _ = X -> _]mulrC {}key_eqn' mulrC {}E1'.
  rewrite -(mulrA _ (v j)) mulrCA mulrA.
  move/eqP; rewrite -subr_eq addrK -subr_eq0 -mulrBl => /eqP.
  move/poly_idomainAxiom; rewrite (negbTE r0_neq0) orbF subr_eq0 => /eqP.
  rewrite mulrC => ->; by rewrite mulrC.
have [l [Hl1 Hl2]] : exists l, (-U) = l * u j /\ V = l * v j.
  have Hcoprime : coprimep (u j) (v j).
    apply/Bezout_coprimepP.
    exists (v j.+1, - u j.+1).
    rewrite mulNr (mulrC _ (v j)) (Euclid.vu r0 r1 j).
    by rewrite /eqp dvd1p andbT dvdp1 -(mulr1 ((_)^+_)) size_Msign size_poly1.
  have /dvdpP[k Hk] : u j %| (-U).
    by rewrite -(Gauss_dvdpl _ Hcoprime) -step2 dvdp_mulr.
  have /dvdpP[k' Hk'] : v j %| V.
    rewrite -(@Gauss_dvdpl _ _ (u j)); last by rewrite coprimep_sym.
    by rewrite mulrC step2 dvdp_mull.
  case/boolP : (u j == 0) => [/eqP uj0|uj0].
    move: Hcoprime.
    rewrite uj0 coprime0p => vj1.
    exists k'.
    by rewrite Hk uj0 2!mulr0.
  exists k; split => //.
  suff : k = k' by move => ->.
  move: step2.
  rewrite Hk Hk' mulrCA -mulrA => /eqP.
  rewrite -subr_eq0 -mulrBl => /eqP.
  move/poly_idomainAxiom => /orP[|/eqP]; first by rewrite subr_eq0 => /eqP.
  move/poly_idomainAxiom => /orP[] /eqP abs; last first.
    move: Hk'; rewrite abs mulr0 => /eqP; by rewrite (negbTE v_neq0).
  by rewrite abs eqxx in uj0.
exists l; split.
  move=> ?; subst l.
  rewrite mul0r in Hl2.
  move: v_neq0.
  by rewrite Hl2 eqxx.
move: key_eqn; by rewrite Hl1 Hl2 -!mulrA -mulrDr -E1.
Qed.

Lemma solve_key_equation_coprimep p t :
  V * (r 1) = R + U * (r 0) ->
  size V <= p -> size R <= t ->
  (p + t = size r0)%N ->
  coprimep V R ->
  let stop := stop t (r 0) (r 1) in
  exists k, k <> 0 /\ v stop = k *: V /\ r stop = k *: R.
Proof.
move=> H1 Hmu Hnu H2 Hco j.
have [l [l_neq0 [vvi rrj]]] := solve_key_equation H1 Hmu Hnu H2.
move: Hco.
rewrite {1}vvi {1}rrj coprimepMr coprimepMl coprimepp => /andP[/andP[]].
case/size_poly1P => k k_neq0 lk _ _.
exists k^-1; split; first by apply/eqP; rewrite invr_eq0.
split.
- by rewrite vvi lk mul_polyC scalerA mulVr ?scale1r // unitfE.
- by rewrite rrj lk mul_polyC scalerA mulVr ?scale1r // unitfE.
Qed.

End euclid_lemma.
