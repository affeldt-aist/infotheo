(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect fingroup perm ssralg zmodp.
From mathcomp Require Import matrix mxalgebra poly polydiv mxpoly.

(**md**************************************************************************)
(* # Lemmas about $\mathbb{F}_2$                                              *)
(*                                                                            *)
(* ```                                                                        *)
(*   F2_of_bool b == coercion from bool to 'F_2                               *)
(*   bool_of_F2 x == boolean corresponding to x : 'F_2                        *)
(*        negF2 x == boolean negation over 'F_2                               *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.

Local Open Scope ring_scope.

Section AboutF2.

Coercion F2_of_bool (b : bool) : 'F_2 := if b then 1 else 0.

Implicit Type x y : 'F_2.

Definition bool_of_F2 x : bool := x != 0.

Definition negF2 x : 'F_2 := x == 0.

Lemma F2_0_1 x : x = (x != 0).
Proof. rewrite -{1}[x]natr_Zp; case: x; case=> //; by case. Qed.

Lemma F2_eq1 x : (x == 1) = (x != 0).
Proof. rewrite -{1}[x]natr_Zp; case: x; case=> //; by case. Qed.

Lemma F2_eq0 x : (x == 0) = (x != 1).
Proof. rewrite -{1}[x]natr_Zp; case: x; case=> //; by case. Qed.

CoInductive F2_spec : 'F_2 -> bool -> bool -> Prop :=
| F2_0 : F2_spec 0 true false
| F2_1 : F2_spec 1 false true.

Lemma F2P x : F2_spec x (x == 0) (x == 1).
Proof.
case/boolP : (x == 0) => [/eqP -> | ]; first by constructor.
rewrite F2_eq0 negbK => /eqP ->; by constructor.
Qed.

Lemma expr2_char2 x : x ^+ 2 = x.
Proof. by case/F2P : x; rewrite ?expr0n ?expr1n. Qed.

Lemma F2_of_bool_addr x y : x + (y == 0) = ((x + y) == 0).
Proof.
by case/F2P : x y; case/F2P => //=; by rewrite ?(addr0,add0r,addrr_char2).
Qed.

Lemma F2_of_bool_0_inv b : F2_of_bool b = 0 -> b = false.
Proof. by case: b. Qed.

Lemma F2_of_boolK b : bool_of_F2 (F2_of_bool b) = b.
Proof. by case: b. Qed.

Lemma bool_of_F2K x : bool_of_F2 x = x :> 'F_2.
Proof. rewrite (F2_0_1 x); by case Heq : ( _ == _ ). Qed.

Lemma bijective_F2_of_bool : {on [pred i in 'F_2], bijective F2_of_bool}.
Proof.
exists bool_of_F2; move=> x Hx /=; by rewrite ?F2_of_boolK ?bool_of_F2K.
Qed.

Lemma bool_of_F2_add_xor x y :
  bool_of_F2 (x + y) = bool_of_F2 x (+) bool_of_F2 y.
Proof. move: x y; by case/F2P; case/F2P. Qed.

Lemma morph_F2_of_bool : {morph F2_of_bool : x y / x (+) y >-> (x + y) : 'F_2}.
Proof.
by rewrite /F2_of_bool; case; case => //=; rewrite ?(addr0,add0r,addrr_char2).
Qed.

Lemma morph_bool_of_F2 : {morph bool_of_F2 : x y / (x + y) : 'F_2 >-> x (+) y}.
Proof. move=> x y /=; by rewrite bool_of_F2_add_xor. Qed.

Lemma F2_addmx m n (a : 'M['F_2]_(m, n)) : a + a = 0.
Proof. apply/matrixP => i j; by rewrite !mxE addrr_char2. Qed.

Lemma F2_mx_opp m n (a : 'M['F_2]_(m, n)) : - a = a.
Proof. apply/matrixP => i j; by rewrite mxE oppr_char2. Qed.

Lemma F2_addmx0 m n (a b : 'M['F_2]_(m, n)) : a + b = 0 -> a = b.
Proof. by move/eqP; rewrite addr_eq0 F2_mx_opp => /eqP. Qed.

End AboutF2.

(* NB: maybe not very interesting as a lemma *)
Lemma bitseq_row_nth n (i j : bitseq) : (size i <= n)%nat -> size i = size j ->
  \row_(k < n) F2_of_bool (nth false i k) =
  \row_(k < n) F2_of_bool (nth false j k) -> i = j.
Proof.
move=> ni ij /rowP h; apply/(@eq_from_nth _ false _ _ ij) => k kj.
have kn : (k < n)%nat by rewrite (leq_trans kj)// ji.
by move: (h (Ordinal kn)); rewrite !mxE /=; do 2 case: nth.
Qed.

Section AboutPolyF2.

Implicit Types p q : {poly 'F_2}.

Lemma F2_poly_add p : p + p = 0.
Proof. apply/polyP => i; by rewrite coef0 coef_add_poly addrr_char2. Qed.

Lemma size_lead_coef_F2 p : size p <> O -> lead_coef p = 1.
Proof.
move/eqP => H; apply/eqP; rewrite F2_eq1 lead_coefE; apply: contra H.
case: p => p /=; rewrite (nth_last 0 p); by case: p => //= h t /negbTE ->.
Qed.

Lemma size1_polyC_F2 p : size p = 1%nat -> p = 1%:P.
Proof.
move=> H.
by rewrite (@size1_polyC _ p) ?H // -(@size_lead_coef_F2 p) ?H // lead_coefE H.
Qed.

Lemma lead_coef_F2 p q : size p = size q -> lead_coef p = lead_coef q.
Proof.
move=> X.
case/boolP : (size p == O) => Y.
- move: X; rewrite (eqP Y) => /esym/eqP; rewrite size_poly_eq0 => /eqP ->.
  by move: Y; rewrite size_poly_eq0 => /eqP ->.
- rewrite !size_lead_coef_F2 //; last by apply/eqP.
  rewrite -X; by apply/eqP.
Qed.

Lemma monic_F2 p : p != 0 -> p \is monic.
Proof.
move=> p0; apply/negPn/negP => H.
have {H} : lead_coef p == 0 by move/monicP/eqP : H; rewrite -F2_eq0.
rewrite lead_coef_eq0; by apply/negP.
Qed.

End AboutPolyF2.
