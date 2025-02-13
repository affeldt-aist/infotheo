(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype tuple.
Require Import BinPos BinNat PArith.
Require Import ssr_ext.

(**md**************************************************************************)
(* # Equivalence bitstrings <-> natural numbers                               *)
(*                                                                            *)
(* ```                                                                        *)
(*       bitseq_of_pos == conversion positive -> bitseq                       *)
(*         bitseq_of_N == conversion N -> bitseq                              *)
(*       rem_lea_false == remove leading false's                              *)
(*         N_of_bitseq == conversion bitseq -> N                              *)
(*             tuple2N == conversion tuple -> N                               *)
(*   bitseq_of_nat i n == conversion i < 2 ^ n to bitseq (of length n)        *)
(*           rV_of_nat == encoding of naturals as vectors, e.g.,              *)
(*                        rV_of_nat 3 1 = [ 0 0 1 ]                           *)
(*                        rV_of_nat 3 2 = [ 0 1 0 ]                           *)
(*                        rV_of_nat 3 3 = [ 0 1 1 ]                           *)
(*           nat_of_rV == conversion 'rV['F_2]_n -> nat                       *)
(* cV_of_nat/nat_of_cV == the same using column vectors                       *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* NB: not used? *)
Lemma pad_seqL_leading_true_inj : forall n i j,
  size i <= n -> size j <= n ->
  pad_seqL false (true :: i) n.+1 = pad_seqL false (true :: j) n.+1 ->
  i = j.
Proof.
elim=> [[] // [] // | ] n IH i j Hi Hj; rewrite /pad_seqL /= !ltnS !subSS => X.
rewrite Hi Hj in X.
move: Hi; rewrite leq_eqVlt.
case/orP => [/eqP Hi|Hi].
  rewrite Hi subnn /= in X.
  move: Hj; rewrite leq_eqVlt.
  case/orP => [/eqP Hj|Hj].
    by move: X; rewrite Hj subnn /= => -[].
  rewrite subSn //= in X; by rewrite -ltnS.
move: Hj; rewrite leq_eqVlt.
case/orP => [/eqP Hj|Hj].
  rewrite Hj subnn /= in X.
  rewrite subSn //= in X; by rewrite -ltnS.
move: X; rewrite !subSn //= => -[] X.
apply IH => //.
by rewrite /pad_seqL /= Hi Hj !subSS.
Qed.

Fixpoint bitseq_of_pos (p : positive) : bitseq :=
  match p with
    | xI q => true :: bitseq_of_pos q
    | xO q => false :: bitseq_of_pos q
    | xH => true :: nil
  end.

Lemma bitseq_of_pos_not_nil a : bitseq_of_pos a <> [::]. Proof. by case: a. Qed.

Lemma bitseq_of_pos_not_nseq_false i r : bitseq_of_pos i <> nseq r false.
Proof.
elim : i r => /= [p Hp [] //|| [] //].
move=> p Hp [] // r [X].
by apply Hp with r.
Qed.

Lemma bitseq_of_pos_not_false a : bitseq_of_pos a <> [:: false].
Proof. exact: bitseq_of_pos_not_nseq_false a 1. Qed.

Lemma bitseq_of_pos_inj : injective bitseq_of_pos.
Proof.
elim.
- move=> a IH [] //=.
  + by move=> b [] /IH ->.
  + by case => /bitseq_of_pos_not_nil.
- by move=> a IH [] // b /= [] /IH ->.
- by case=> // a /= [] /esym/bitseq_of_pos_not_nil.
Qed.

Lemma bitseq_of_pos_true : forall p, bitseq_of_pos p = [:: true] -> p = xH.
Proof. by case => //; case. Qed.

Fixpoint pos_of_bitseq s : positive :=
  match s with
    | [::] => xH
    | true :: t => xI (pos_of_bitseq t)
    | false :: t => xO (pos_of_bitseq t)
  end.

Lemma pos_of_bitseq_nseq_false : forall p, Pos.to_nat (pos_of_bitseq (nseq p false)) = 2 ^ p.
Proof. elim=> // p IH /=; by rewrite expnS -IH Pos2Nat.inj_xO. Qed.

Lemma pos_of_bitseq_rev : forall y p,
  rev (bitseq_of_pos p) = true :: y -> pos_of_bitseq (rev y) = p.
Proof.
elim/last_ind => [p Hp /=|h t IH []// p /=].
  apply/esym/bitseq_of_pos_true; by rewrite -[LHS]revK Hp.
- rewrite rev_cons -rcons_cons => /eqP.
  rewrite eqseq_rcons => /andP[/eqP/IH H1 /eqP <-].
  by rewrite rev_rcons /= H1.
- rewrite rev_cons -rcons_cons => /eqP.
  rewrite eqseq_rcons => /andP[/eqP/IH H1 /eqP <-].
  by rewrite rev_rcons /= H1.
- by move: p; case => <-.
Qed.

Lemma pos_of_bitseq_up : forall p l, size l <= p ->
  Pos.to_nat (pos_of_bitseq l) < 2 ^ p.+1.
Proof.
elim=> [|p ih [|h t] //]; first by destruct l.
- move=> _ /=.
  by rewrite (@leq_ltn_trans 1) // -{1}(expn0 2) ltn_exp2l.
- move=> H1 /=.
  destruct h.
    rewrite Pos2Nat.inj_xI expnS multE.
    rewrite (@leq_trans  (2 * (Pos.to_nat (pos_of_bitseq t)).+1)) //.
      by rewrite mulnS addnC addn2.
    by rewrite leq_mul2l /= ih.
  by rewrite Pos2Nat.inj_xO expnS multE ltn_mul2l /= ih.
Qed.

Definition bitseq_of_N (x : N) :=
  match x with
    | N0 => false :: nil
    | Npos p => bitseq_of_pos p
  end.

Lemma bitseq_of_N_2 x : x <> N0 -> bitseq_of_N (2 * x) = false :: bitseq_of_N x.
Proof. by case : x. Qed.

Lemma bitseq_of_N_leading_bit n : n <> N0 -> exists k, rev (bitseq_of_N n) = true :: k.
Proof.
case : n => //.
elim => [i IH _ | i IH _ | _ /=].
- have : Npos i <> 0%N by [].
  case/IH => k /= Hk.
  exists (rcons k true); by rewrite rev_cons Hk.
- have : Npos i <> 0%N by [].
  case/IH => k /= Hk.
  exists (rcons k false); by rewrite rev_cons Hk.
- by exists nil.
Qed.

Lemma bitseq_of_N_nseq_false i r : i <> O -> bitseq_of_N (bin_of_nat i) <> nseq r false.
Proof. case: i r => // i r _ /=; exact: bitseq_of_pos_not_nseq_false. Qed.

Lemma bitseq_of_N_inj : injective bitseq_of_N.
Proof.
case.
- by case => // a /= /esym/bitseq_of_pos_not_false.
- move=> a /= [] //=.
  + by move/bitseq_of_pos_not_false.
  + by move=> b /bitseq_of_pos_inj ->.
Qed.

Lemma bitseq_of_N_bin_of_nat_expn2 : forall m : nat,
  bitseq_of_N (bin_of_nat (2 ^ m)) = nseq m false ++ [:: true].
Proof.
elim => // m0 IH.
rewrite [in X in _ = X]/= -IH bin_of_nat_expn2 bitseq_of_N_2 //.
suff [i Hi] : exists i, 2 ^ m0 = nat_of_pos i.
  rewrite Hi.
  by apply bin_of_nat_nat_of_pos_not_0.
exists (Pos.of_nat (2 ^ m0)).
rewrite -BinPos_nat_of_P_nat_of_pos Nat2Pos.id //.
apply/eqP; by rewrite -lt0n expn_gt0.
Qed.

Lemma size_bitseq_of_N_ub' : forall i n, nat_of_bin i <> O ->
  nat_of_bin i < 2 ^ n -> size (bitseq_of_N i) <= n.
Proof.
case=> //=.
elim => [p IHp n _ H /= | p IHp n _ H /= | [] //].
- case: n H => [//|n H].
  have X : nat_of_pos p < 2 ^ n.
    have {H} : (nat_of_pos p).*2 < 2 ^ n.+1.
      rewrite /= NatTrec.doubleE in H.
      by apply leq_ltn_trans with (nat_of_pos p).*2.+1.
    by rewrite expnSr muln2 ltn_double.
  apply IHp in X; last exact: nat_of_pos_not_0.
  by apply leq_ltn_trans with n.
- case: n H => [H|n H].
  + rewrite expn0 in H.
    have {H} : nat_of_pos (BinPos.xO p) = O.
      by destruct (nat_of_pos (BinPos.xO p)).
    by move: (@nat_of_pos_not_0 (BinPos.xO p)).
  + have : nat_of_pos p < 2 ^ n.
      by rewrite /= NatTrec.doubleE expnSr muln2 ltn_double in H.
    rewrite ltnS; move/IHp; apply.
    exact: nat_of_pos_not_0.
Qed.

Lemma size_pad_positive c (s : bitseq) :
  pad_seqL false (rev (c :: bitseq_of_pos (pos_of_bitseq s))) (size s).+2 =
  rcons (pad_seqL false (rev (bitseq_of_pos (pos_of_bitseq s))) (size s).+1) c.
Proof.
rewrite /pad_seqL !size_rev /= ltnS.
case: ifPn => Hsz; first by rewrite subSS rev_cons rcons_cat.
have Hup := pos_of_bitseq_up (leqnn (size s)).
have Hub' := @size_bitseq_of_N_ub' (Npos (pos_of_bitseq s)) (size s).+1
             (@nat_of_pos_not_0 _).
rewrite /= -BinPos_nat_of_P_nat_of_pos in Hub'.
by rewrite Hub' in Hsz.
Qed.

Lemma size_bitseq_of_N_ub i n : i <> O ->
  i < 2 ^ n -> size (bitseq_of_N (bin_of_nat i)) <= n.
Proof.
move=> Hi Hin.
apply (@size_bitseq_of_N_ub' (bin_of_nat i) n); by rewrite bin_of_natK.
Qed.

Lemma size_bitseq_of_N_lb' : forall i n,
  2 ^ n <= nat_of_bin i -> n < size (bitseq_of_N i).
Proof.
case => [m|]; first by rewrite leqn0 expn_eq0.
elim => [p ih m K /= | p ih m K /= | m].
- case: m K => [//|m K].
  have /ih : 2 ^ m <= nat_of_pos p.
    move: K.
    by rewrite /= NatTrec.doubleE expnS -ltnS -doubleS -muln2 mulnC ltn_pmul2r.
  by rewrite ltnS.
- case: m K => [//|m K].
  have /ih : 2 ^ m <= nat_of_pos p.
    by rewrite /= NatTrec.doubleE expnS -muln2 mulnC leq_pmul2r in K.
  by rewrite ltnS.
- by rewrite -[in X in _ <= X](_ : 2 ^ 0 = 1%num) // leq_exp2l.
Qed.

Lemma size_bitseq_of_N_lb i n : 2 ^ n <= i ->
  n < size (bitseq_of_N (bin_of_nat i)).
Proof. move=> Hn; by rewrite size_bitseq_of_N_lb' // bin_of_natK. Qed.

Fixpoint rem_lea_false s :=
  match s with
    | [::] => [::]
    | true :: _ => s
    | _ :: t => rem_lea_false t
  end.

Lemma rem_lea_false_nseq : forall a b, rem_lea_false (nseq a false ++ b) =
  rem_lea_false b.
Proof. by elim. Qed.

Lemma rem_lea_false_pad_seqL : forall a l, (size l < a)%nat ->
  rem_lea_false (pad_seqL false (true :: l) a) = true :: l.
Proof.
case=> [//| a l H].
by rewrite /pad_seqL /= H subSS rem_lea_false_nseq.
Qed.

Definition N_of_bitseq s : N :=
  match rem_lea_false s with
    | [::] => N0
    | true :: t => Npos (pos_of_bitseq (rev t))
    | _ => N0 (* shouldn't happen *)
  end.

Lemma N_of_bitseq_false : forall l, N_of_bitseq (false :: l) = N_of_bitseq l.
Proof. by case. Qed.

Lemma N_of_bitseq_nseq_false : forall k, N_of_bitseq (nseq k false) = N0.
Proof. by elim. Qed.

Lemma N_of_bitseq_up : forall p l, size l <= p ->
  N.to_nat (N_of_bitseq l) < 2 ^ p.
Proof.
elim=> [[|//] _ /= |p IH [/=|h t]].
- by rewrite expn_gt0.
- by rewrite expn_gt0.
- rewrite /= ltnS => tp.
  destruct h; first by rewrite /= pos_of_bitseq_up // size_rev.
  by rewrite N_of_bitseq_false (ltn_trans (IH _ tp)) // ltn_exp2l.
Qed.

Lemma N_of_bitseq_true p : N.to_nat (N_of_bitseq (true :: nseq p false)) = 2 ^ p.
Proof.
elim : p => // p IH /=.
by rewrite (_ : false :: _ = nseq p.+1 false) // rev_nseq pos_of_bitseq_nseq_false.
Qed.

Lemma N_of_bitseq_0 : forall n0 p, N_of_bitseq p = N0 -> size p = n0 ->
  p = nseq n0 false.
Proof. elim => [ [] // | n0 IH [|[] t] //= Hp [Hsz] ]. by rewrite -(IH t). Qed.

Lemma Npos_pos_of_bitseq_rev' : forall x y,
  rev (bitseq_of_N x) = true :: y ->
  Npos (pos_of_bitseq (rev y)) = nat_of_bin x :> nat.
Proof.
elim/Nind => // x IH y.
move Heq : (N.succ x) => eq.
destruct eq => //= H.
f_equal.
by apply pos_of_bitseq_rev in H.
Qed.

Lemma Npos_pos_of_bitseq_rev x y :
  rev (bitseq_of_N (bin_of_nat x)) = true :: y ->
  Npos (pos_of_bitseq (rev y)) = x :> nat.
Proof.
move=> H.
by rewrite (@Npos_pos_of_bitseq_rev' (bin_of_nat x) y H) bin_of_natK.
Qed.

Lemma size_N_of_bitseqK (s : bitseq) :
  size s > 0 -> size (bitseq_of_N (bin_of_nat (N_of_bitseq s))) <= size s.
Proof.
move=> Hs.
case Hbs : (bin_of_nat _) => //.
apply size_bitseq_of_N_ub'.
  by apply nat_of_pos_not_0.
by rewrite -Hbs bin_of_natK -Nto_natE N_of_bitseq_up.
Qed.

Definition bitseq_of_nat (i : nat) n :=
  pad_seqL false (rev (bitseq_of_N (bin_of_nat i))) n.

Lemma size_bitseq_of_nat i n : size (bitseq_of_nat i n) == n.
Proof. by rewrite /bitseq_of_nat size_pad_seqL. Qed.

Lemma bitseq_of_nat_nseq_false i r : i <> O ->
  i < 2 ^ r -> bitseq_of_nat i r <> nseq r false.
Proof.
move=> Hi Hin.
rewrite /bitseq_of_nat /pad_seqL.
have : size (bitseq_of_N (bin_of_nat i)) <= r by exact/size_bitseq_of_N_ub.
rewrite leq_eqVlt.
case/orP => X.
- move/eqP : X => X.
  rewrite {1}size_rev {1}X leqnn -X -{1}size_rev subnn /=.
  have Y : bitseq_of_N (bin_of_nat i) <>
    rev (nseq (size (bitseq_of_N (bin_of_nat i))) false).
    rewrite rev_nseq.
    exact: bitseq_of_N_nseq_false.
  contradict Y.
  by rewrite -Y revK.
- rewrite {1}size_rev leq_eqVlt X orbC /= size_rev => abs.
  move: (nseq_cat abs) => {}abs.
  have W : bitseq_of_N (bin_of_nat i) = nseq (size (rev (bitseq_of_N (bin_of_nat i)))) false.
    by rewrite -[LHS]revK abs rev_nseq !size_nseq.
  exact: bitseq_of_N_nseq_false Hi W.
Qed.

Lemma bitseq_of_nat_expn2 p m : p < m ->
  bitseq_of_nat (2 ^ p) m = nseq (m - p.+1) false ++ true :: nseq p false.
Proof.
move=> pm.
rewrite /bitseq_of_nat /= /pad_seqL /= bitseq_of_N_bin_of_nat_expn2 size_rev.
by rewrite size_cat size_nseq /= -ltnS addn1 ltnS pm rev_cat /= rev_nseq.
Qed.

Lemma N_of_bitseq_bitseq_of_nat m x : x <> O -> (x < 2 ^ m)%nat ->
  N_of_bitseq (bitseq_of_nat x m) = x :> nat.
Proof.
move=> Hx x_m.
rewrite /N_of_bitseq /bitseq_of_nat.
have Hx' : bin_of_nat x <> N0.
  contradict Hx.
  rewrite (_ : 0 = bin_of_nat (nat_of_bin 0))%N // in Hx.
  by apply bin_of_nat_inj in Hx.
case: (@bitseq_of_N_leading_bit _ Hx') => y Hy.
rewrite Hy.
rewrite rem_lea_false_pad_seqL; last first.
  move: (size_bitseq_of_N_ub Hx x_m).
  by rewrite -size_rev Hy.
  by apply Npos_pos_of_bitseq_rev in Hy.
Qed.

Lemma bitseq_of_nat_0 n : bitseq_of_nat 0 n = nseq n false.
Proof.
rewrite /bitseq_of_nat /= /pad_seqL /=.
case: ifP => [Hn|]; last by case: n.
by rewrite cats1 -nseq_S subn1 prednK.
Qed.

Lemma bitseq_of_nat_inj n i j : i < 2 ^ n -> j < 2 ^ n ->
  bitseq_of_nat i n = bitseq_of_nat j n -> i = j.
Proof.
move=> Hi Hj.
case/boolP : (i == 0) => [/eqP -> | /eqP Hi0].
  rewrite bitseq_of_nat_0 => abs.
  apply/eqP/negPn/negP.
  rewrite eq_sym => /eqP.
  move/(@bitseq_of_nat_nseq_false j n); by apply.
case/boolP : (j == 0) => [/eqP -> | /eqP Hj0].
  rewrite bitseq_of_nat_0 => abs.
  apply/eqP/negPn/negP.
  move/eqP/(@bitseq_of_nat_nseq_false i n); by apply.
move=> H.
by rewrite -(N_of_bitseq_bitseq_of_nat Hi0 Hi) -(N_of_bitseq_bitseq_of_nat Hj0 Hj) H.
Qed.

Lemma N_of_bitseqK (s : bitseq) :
  size s > 0 -> bitseq_of_nat (N.to_nat (N_of_bitseq s)) (size s) = s.
Proof.
clear.
rewrite Nto_natE.
elim: s => // b s IHs Hs /=.
case b; simpl.
  rewrite /bitseq_of_nat nat_of_posK /=.
  rewrite -size_rev -{3}(revK s).
  elim: (rev s) => //.
  clear.
  move => b s IHs /=.
  rewrite -(cat1s b) rev_cat -cat_cons -IHs cats1.
  by case b; apply size_pad_positive.
case Hs': (size s > 0); last by destruct s.
rewrite -{3}IHs /bitseq_of_nat //.
rewrite (_ : N_of_bitseq (false :: s) = N_of_bitseq s) //.
rewrite /pad_seqL size_rev.
have Hsz := size_N_of_bitseqK Hs'.
rewrite !ifT //.
  by rewrite subSn.
by apply leqW.
Qed.

Definition tuple2N {m} (x : m.-tuple bool) := match x with Tuple x _ => N_of_bitseq x end.

Lemma tuple2N_0 n : forall p, tuple2N p = N0 -> p = [tuple of nseq n false].
Proof.
case=> p Hp /= Hp'.
apply val_inj => /=.
apply N_of_bitseq_0 => //; by apply/eqP.
Qed.

(* sample vectors *)

Lemma rev7_neq0 n : (7 * 2 ^ (n - 3))%nat <> O.
Proof.
rewrite -[in X in _ <> X ](muln0 7).
move/eqP.
by rewrite eqn_mul2l /= expn_eq0.
Qed.

Lemma rev7_ub n (Hlen : 2 < n) : 7 * 2 ^ (n - 3) < 2 ^ n.
Proof.
rewrite -[in X in _ < X](@subnKC 3 n) //.
by rewrite /= expnD ltn_pmul2r // expn_gt0.
Qed.

Lemma rev7_lb n (Hn : 2 < n) : 2 ^ n.-1 <= 7 * 2 ^ (n - 3).
Proof.
destruct n => //=.
rewrite (@leq_trans (2 ^ 2 * 2 ^( n.+1 - 3))) //.
  rewrite -expnD leq_exp2l // addnBA // addnC addn2 -addn3.
  by rewrite -addnBA // subnn addn0.
by rewrite leq_pmul2r // expn_gt0.
Qed.

Lemma bin_of_nat_7 : forall n, 2 < n ->
  bin_of_nat 7 = BinNums.Npos (BinNums.xI (BinNums.xI (BinNums.xH))).
Proof. by []. Qed.

Fixpoint xOs n cont :=
  match n with
    | O => cont
    | S m => BinNums.xO (xOs m cont)
  end.

Lemma bin_of_nat_rev7 : forall n, 2 < n ->
  bin_of_nat (7 * 2 ^ (n - 3)) =
  BinNums.Npos (xOs (n - 3) (BinNums.xI (BinNums.xI (BinNums.xH)))).
Proof.
elim=> //.
case=> //.
case=> //.
case=> //.
move=> n /(_ Logic.eq_refl) => IH _.
rewrite (_ : n.+4 - 3 = n.+1)%nat //.
rewrite (_ : n.+3 - 3 = n)%nat // in IH; last by rewrite 3!subSS subn0.
transitivity (BinNat.N.mul 2 (bin_of_nat (7 * 2 ^ n))); last by rewrite {}IH -BinPos.Pos.add_diag.
set lhs := bin_of_nat _.
set rhs := BinNat.N.mul _ _.
suff : nat_of_bin lhs = nat_of_bin rhs.
  rewrite {1}/lhs bin_of_natK /lhs => ->.
  by rewrite nat_of_binK.
rewrite /lhs /rhs bin_of_natK nat_of_mul_bin expnS mulnA (mulnC 7) -mulnA.
f_equal.
by rewrite bin_of_natK.
Qed.

(* TODO: move *)
From mathcomp Require Import bigop zmodp ssralg matrix.
Require Import ssralg_ext f2.

Import GRing.Theory.

Section rV_and_nat_def.
Variable n : nat.

Definition rV_of_nat (i : nat) : 'rV['F_2]_n :=
  row_of_bitseq (size_bitseq_of_nat i n).

Definition nat_of_rV (y : 'rV['F_2]_n) : nat :=
  BinNat.N.to_nat (N_of_bitseq (map bool_of_F2 (tuple_of_row y))).

End rV_and_nat_def.

Section rV_and_nat_prop.
Variable n : nat.

Local Open Scope ring_scope.

Lemma rV_of_nat_neq0 i : i <> O -> (i < expn 2 n)%nat -> rV_of_nat n i <> 0%R.
Proof.
move=> Hi W.
move: (bitseq_of_nat_nseq_false Hi W) => H.
contradict H.
apply eq_from_nth with false.
- by rewrite /= size_pad_seqL size_nseq.
- move=> j Hj.
  rewrite (_ : size _ = n) in Hj; last by apply/eqP; rewrite size_bitseq_of_nat.
  move/rowP : H => /(_ (Ordinal Hj)).
  rewrite !mxE /= => Hj'.
  rewrite nth_nseq Hj.
  by apply F2_of_bool_0_inv.
Qed.

Lemma rV_of_nat_inj i j : (i < expn 2 n)%nat -> (j < expn 2 n)%nat ->
  rV_of_nat n i = rV_of_nat n j -> i = j.
Proof.
move=> Hi Hj /bitseq_row_nth => h; apply (@bitseq_of_nat_inj n) => //.
by apply h; rewrite !(eqP (size_bitseq_of_nat _ _)).
Qed.

Local Open Scope nat_scope.
Local Open Scope ring_scope.

Lemma rV_of_natD_neq0 i j : i <> j -> i <> O -> j <> O ->
  (i < expn 2 n)%nat -> (j < expn 2 n)%nat -> rV_of_nat n i + rV_of_nat n j <> 0.
Proof.
move=> Hij Hi Hj Hin Hjn.
destruct i => //.
destruct j => //.
contradict Hij.
apply F2_addmx0 in Hij.
have [ii Hii] : exists ii, i.+1 = nat_of_pos ii.
  exists (BinPos.P_of_succ_nat i).
  by rewrite -Pnat.nat_of_P_o_P_of_succ_nat_eq_succ BinPos_nat_of_P_nat_of_pos.
have [jj Hjj] : exists jj, j.+1 = nat_of_pos jj.
  exists (BinPos.P_of_succ_nat j).
  by rewrite -Pnat.nat_of_P_o_P_of_succ_nat_eq_succ BinPos_nat_of_P_nat_of_pos.
rewrite Hii Hjj in Hij.
apply rV_of_nat_inj in Hij; last 2 first.
  by rewrite -Hii.
  by rewrite -Hjj.
apply nat_of_pos_inj in Hij.
rewrite Hjj; by subst ii.
Qed.

Lemma mulmx_rV_of_nat_row m (M : 'M_(n, m)) (k : 'I_n) :
  rV_of_nat n (expn 2 k) *m M = row (Ordinal (rev_ord_proof k)) M.
Proof.
rewrite /rV_of_nat.
apply/rowP => i.
rewrite !mxE /=.
transitivity (\sum_(j < n) (F2_of_bool (nth false (bitseq_of_nat (expn 2 k) n) j) * M j i)).
  apply eq_bigr => l _; by rewrite mxE.
rewrite bitseq_of_nat_expn2 //.
set j := Ordinal _.
rewrite (bigD1 j) //=.
set x := nth _ _ _.
have -> : x = true by rewrite /x nth_cat size_nseq ltnn subnn.
rewrite mul1r.
rewrite [X in _ + X = _](_ : _ = 0) ?addr0 //.
rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addr0 // => l lj.
rewrite (_ : nth _ _ _ = false) ?mul0r //.
rewrite  nth_cat size_nseq.
case: ifP => lnk; first by rewrite nth_nseq lnk.
rewrite (_ : true :: _ = [:: true] ++ nseq k false) // nth_cat /=.
case: ifP => lnk1; last by rewrite nth_nseq; case: ifP.
exfalso.
clear -lnk1 lj lnk.
have {lnk1} : l <= n - k.+1 by rewrite ltnS leqn0 in lnk1.
rewrite leq_eqVlt lnk orbC /=; by apply/negP.
Qed.

Lemma rV_of_nat_0 : rV_of_nat n 0 = 0.
Proof.
rewrite /rV_of_nat /row_of_bitseq; apply/rowP => b /=.
by rewrite !mxE bitseq_of_nat_0 nth_nseq (ltn_ord b).
Qed.

Lemma nat_of_rV_up (y : 'rV_n) : nat_of_rV y < expn 2 n.
Proof. by rewrite /nat_of_rV N_of_bitseq_up // size_map size_tuple. Qed.

Lemma nat_of_rV_0 : nat_of_rV (0 : 'rV_n) = O.
Proof.
rewrite /nat_of_rV (_ : N_of_bitseq _ = 0%N) //.
rewrite (_ : map _ _ = nseq n false) // ?N_of_bitseq_nseq_false //.
apply eq_from_nth with false; first by rewrite size_map size_nseq size_tuple.
move=> i; rewrite size_map size_tuple => ni.
rewrite (nth_map 0) ?size_tuple // nth_nseq ni (_ : nth _ _ _ = 0) //.
by rewrite /tuple_of_row /= (nth_map (Ordinal ni)) ?size_enum_ord // mxE.
Qed.

Lemma nat_of_rV_ord0 (y : 'rV_0) : nat_of_rV y = O.
Proof. by rewrite /nat_of_rV Nto_natE tuple_of_row_ord0. Qed.

Lemma nat_of_rVK (y : 'rV_n) : rV_of_nat n (nat_of_rV y) = y.
Proof.
case: n y => [|n0] y.
  apply/rowP; by case.
apply/rowP => i.
rewrite mxE /nat_of_rV.
set tmp := [seq bool_of_F2 i | i <- _].
rewrite [X in bitseq_of_nat _ X](_ : _ = size tmp); last by rewrite size_map size_tuple.
rewrite N_of_bitseqK; last by rewrite size_tuple.
rewrite /tmp (nth_map (0 : 'F_2)); last by rewrite size_tuple.
by rewrite bool_of_F2K /tuple_of_row nth_mktuple.
Qed.

Lemma nat_of_rV_eq0 (y : 'rV_n) : (nat_of_rV y == O) = (y == 0).
Proof.
case/boolP : (nat_of_rV _ == O) => H.
  have : rV_of_nat n (nat_of_rV y) = 0 by rewrite (eqP H) rV_of_nat_0.
  by rewrite nat_of_rVK => ->; rewrite eqxx.
apply/esym/eqP/eqP; apply: contra H => /eqP ->.
by rewrite nat_of_rV_0.
Qed.

End rV_and_nat_prop.

Section cV_and_nat.
Local Open Scope ring_scope.

Definition cV_of_nat (n i : nat) : 'cV['F_2]_n := (rV_of_nat n i)^T.

Definition nat_of_cV n (y : 'cV['F_2]_n) : nat := nat_of_rV y^T.

Lemma nat_of_cV_0 k : nat_of_cV (0 : 'cV_k) = O.
Proof. by rewrite /nat_of_cV trmx0 nat_of_rV_0. Qed.

Lemma nat_of_rV_tr n (y : 'rV_n) : nat_of_rV y = nat_of_cV (y^T).
Proof. by rewrite /nat_of_cV trmxK. Qed.

End cV_and_nat.

Lemma rev7_bin : forall m, (2 < m)%nat ->
  rev (bitseq_of_N (BinNums.Npos (xOs (m - 3) (BinNums.xI 3)))) =
  true :: true :: true :: nseq (m - 3) false.
Proof.
elim=> //.
case=> //.
case=> //.
case=> // m /(_ isT).
rewrite -{1}addn3 -addnBA // subnn addn0 => IH _.
rewrite -{1}addn4 -addnBA //= (_ : 4 - 3 = 1)%nat // addn1 /=.
by rewrite rev_cons IH /= -{1}addn3 -addnBA // subnn addn0 -nseq_S.
Qed.

Lemma rev_bitseq_of_nat_7 n : (2 < n)%nat ->
  rev (bitseq_of_nat 7 n) = bitseq_of_nat (7 * expn 2 (n - 3)) n.
Proof.
move=>Hn.
rewrite /bitseq_of_nat.
rewrite (bin_of_nat_rev7 Hn).
rewrite (@bin_of_nat_7 n) //=.
rewrite (rev7_bin Hn) /=.
rewrite {1}/pad_seqL /=.
rewrite Hn.
rewrite rev_cat /=.
rewrite /pad_seqL /=.
rewrite size_nseq.
case: ifP => H //.
  rewrite (_ : n - (n - 3).+3 = 0)%nat //; last first.
  destruct n => //.
  destruct n => //.
  destruct n => //.
  rewrite -addn3.
  by rewrite -(@addnBA n 3 3) // subnn addn0 addn3 subnn.
by rewrite rev_nseq.
exfalso.
move/negbT in H.
rewrite -leqNgt in H.
destruct n => //.
destruct n => //.
destruct n => //.
by rewrite -{2}addn3 -addnBA // subnn addn0 ltnn in H.
Qed.
