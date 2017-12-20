(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype tuple.
Require Import BinPos BinNat PArith.
Require Import ssr_ext.

(** * Equivalence bitstrings <-> natural numbers *)

Section Pad.

Variable A : Type.
Variable def : A.

Definition pad_seq (l : seq A) n :=
  if size l <= n then l ++ nseq (n - size l) def else take n l.

Definition pad_seqL (l : seq A) n :=
  if size l <= n then nseq (n - size l) def ++ l else take n l.

Lemma pad_seqL_inj : forall n a b, size a = n -> size b = n ->
  pad_seqL a n = pad_seqL b n -> a = b.
Proof.
elim=> [[] // [] // | ] n IH [|a ta] // [|b tb] // [Ha] [Hb].
by rewrite /pad_seqL /= Ha Hb ltnS leqnn subnn.
Qed.

Lemma size_pad_seq : forall l n, size (pad_seq l n) = n.
Proof.
move=> lst n.
rewrite /pad_seq.
case/orP : (orbN (size lst <= n)) => X.
- by rewrite X size_cat size_nseq -maxnE (maxn_idPr _) // ltnW.
- rewrite (negbTE X) size_takel //.
  rewrite leqNgt negbK in X.
  by rewrite ltnW.
Qed.

Lemma size_pad_seqL : forall l n, size (pad_seqL l n) = n.
Proof.
move=> lst n.
rewrite /pad_seqL.
case/orP : (orbN (size lst <= n)) => X.
- by rewrite X size_cat size_nseq subnK // ltnW.
- rewrite (negbTE X) size_takel //.
  rewrite leqNgt negbK in X.
  by rewrite ltnW.
Qed.

End Pad.
Implicit Arguments pad_seq [A].
Implicit Arguments pad_seqL [A].
Implicit Arguments size_pad_seq [A].

Lemma pad_seqL_leading_true_inj : forall n i j,
  size i <= n -> size j <= n ->
  pad_seqL false (true :: i) n.+1 = pad_seqL false (true :: j) n.+1 ->
  i = j.
Proof.
elim=> [[] // [] // | ] n IH i j Hi Hj; rewrite /pad_seqL /= !ltnS !subSS => X.
rewrite Hi Hj in X.
rewrite leq_eqVlt in Hi.
case/orP : Hi => Hi.
  move/eqP in Hi.
  rewrite Hi subnn /= in X.
  rewrite leq_eqVlt in Hj.
  case/orP : Hj => Hj.
    move/eqP in Hj.
    rewrite Hj subnn /= in X.
    by case: X.
  rewrite subSn //= in X; by rewrite -ltnS.
rewrite leq_eqVlt in Hj.
case/orP : Hj => Hj.
  move/eqP in Hj.
  rewrite Hj subnn /= in X.
  rewrite subSn //= in X; by rewrite -ltnS.
rewrite !subSn //= in X.
case: X => X.
apply IH => //.
by rewrite /pad_seqL /= Hi Hj !subSS.
Qed.

Lemma bin_of_nat_two_pow m0 : bin_of_nat (2 ^ m0.+1) = (2 * bin_of_nat (2 ^ m0))%N.
Proof.
set lhs := bin_of_nat _.
set rhs := (_ * _)%N.
suff : nat_of_bin lhs = nat_of_bin rhs.
  rewrite bin_of_natK /lhs /rhs {lhs rhs} => ->.
  by rewrite nat_of_binK.
rewrite /lhs /rhs {lhs rhs} bin_of_natK expnS nat_of_mul_bin.
congr mult.
by rewrite bin_of_natK.
Qed.

Lemma N_bin_to_nat x : N.to_nat x = nat_of_bin x.
Proof.
case x => //=.
elim => [ | | //] p Hp /=.
by rewrite Pos2Nat.inj_xI NatTrec.trecE Hp -mul2n.
by rewrite Pos2Nat.inj_xO NatTrec.trecE Hp -mul2n.
Qed.

Lemma nat_of_posK k : bin_of_nat (nat_of_pos k) = Npos k.
Proof. by rewrite -(nat_of_binK (Npos k)). Qed.

(** Conversion BinPos.positive / bitseq *)

Lemma BinPos_nat_of_P_nat_of_pos : forall i, BinPos.nat_of_P i = nat_of_pos i.
Proof.
elim=> // i /= Hi.
- by rewrite Pnat.nat_of_P_xI NatTrec.doubleE Hi multE mul2n.
- by rewrite Pnat.nat_of_P_xO NatTrec.doubleE Hi multE mul2n.
Qed.

(*Eval compute in (bin_of_nat 2).*)

Fixpoint positive2bitseq (p : positive) : bitseq :=
  match p with
    | xI q => true :: positive2bitseq q
    | xO q => false :: positive2bitseq q
    | xH => true :: nil
  end.

Lemma positive2bitseq_not_nil : forall a, positive2bitseq a <> [::]. by case. Qed.

Lemma positive2bitseq_not_nseq_false : forall i r, positive2bitseq i <> nseq r false.
Proof.
elim => /=.
- by move=> p Hp [].
- move=> p Hp [] // r [X].
  by apply Hp with r.
- by case.
Qed.

Lemma positive2bitseq_not_false a : positive2bitseq a <> [::false].
Proof. by apply (positive2bitseq_not_nseq_false a 1). Qed.

Lemma positive2bitseq_inj : forall a b, positive2bitseq a = positive2bitseq b -> a = b.
Proof.
elim.
- move=> a IH [] //=.
  + by move=> b [] /IH ->.
  + case=> X.
    move: (positive2bitseq_not_nil a); by rewrite X.
- by move=> a IH [] // b /= [] /IH ->.
- case=> // a /= [X].
  move: (positive2bitseq_not_nil a); by rewrite -X.
Qed.

Lemma positive2bitseq_true : forall p, positive2bitseq p = [:: true] -> p = xH.
Proof. by case => //; case. Qed.

Fixpoint bitseq2positive s : positive :=
  match s with
    | [::] => xH
    | true :: t => xI (bitseq2positive t)
    | false :: t => xO (bitseq2positive t)
  end.

Lemma helper1 : forall h,
  bitseq2positive (true :: h) = ((bitseq2positive h)~1)%positive.
Proof. by case. Qed.

Lemma helper2 : forall h,
  bitseq2positive (false :: h) = ((bitseq2positive h)~0)%positive.
Proof. by case. Qed.

Lemma positive2bitseq_bitseq2positive : forall y p,
  rev (positive2bitseq p) = true :: y -> bitseq2positive (rev y) = p.
Proof.
elim/last_ind.
  move=> p Hp /=.
  rewrite (positive2bitseq_true p) //; by apply rev_inj.
move=> h t IH.
case=> // p /=.
- rewrite rev_cons -rcons_cons.
  move/eqP.
  rewrite eqseq_rcons.
  case/andP.
  move/eqP.
  move/IH => H1 /eqP H2; subst t.
  by rewrite rev_rcons helper1 H1.
- rewrite rev_cons -rcons_cons.
  move/eqP.
  rewrite eqseq_rcons.
  case/andP.
  move/eqP.
  move/IH => H1 /eqP H2; subst t.
  by rewrite rev_rcons helper2 H1.
- rewrite /positive2bitseq /= in p.
  by case: p => <-.
Qed.

Lemma bitseq2positive_up : forall p l, size l <= p ->
  (Pos.to_nat (bitseq2positive l) < 2 ^ p.+1)%nat.
Proof.
elim=> //.
  by destruct l => // _.
move=> p IH [| h t] //.
  move=> _ /=.
  apply leq_ltn_trans with (1%nat) => //.
  by rewrite -{1}(expn0 2) ltn_exp2l.
move=> H1 /=.
destruct h.
  rewrite Pos2Nat.inj_xI expnS multE.
  apply leq_trans with (2 * ((Pos.to_nat (bitseq2positive t)).+1))%nat.
  by rewrite mulnS addnC addn2.
  rewrite leq_mul2l /=.
  by apply IH.
rewrite Pos2Nat.inj_xO expnS multE ltn_mul2l /=.
by apply IH.
Qed.

(** Conversion BinNat.N / bitseq *)

Definition N2bitseq (x : N) : bitseq :=
  match x with
    | N0 => false :: nil
    | Npos p => positive2bitseq p
  end.

Lemma N2bitseq_2 : forall x, x <> N0 -> N2bitseq (2 * x) = false :: N2bitseq x.
Proof. by case. Qed.

Lemma N2bitseq_leading_bit : forall n, n <> N0 -> exists k, rev (N2bitseq n) = true :: k.
Proof.
case=> //.
elim => [i IH _ | i IH _ | _ /=].
- have : Npos i <> 0%num by done.
  case/IH => k /= Hk.
  exists (rcons k true); by rewrite rev_cons Hk.
- have : Npos i <> 0%num by done.
  case/IH => k /= Hk.
  exists (rcons k false); by rewrite rev_cons Hk.
- by exists nil.
Qed.

Lemma N2bitseq_nseq_false : forall i r, i <> O -> N2bitseq (bin_of_nat i) <> nseq r false.
Proof.
case=> // i r _ /=.
by apply positive2bitseq_not_nseq_false.
Qed.

Lemma N2bitseq_inj : forall a b, N2bitseq a = N2bitseq b -> a = b.
Proof.
case.
- case => // a /= X.
  move: (positive2bitseq_not_false a); by rewrite -X.
- move=> a /= [] //=.
  + move=> X.
    move: (positive2bitseq_not_false a); by rewrite X.
  + by move=> b /positive2bitseq_inj ->.
Qed.

Lemma N2bitseq_bin_of_nat_two_pow : forall m : nat,
  N2bitseq (bin_of_nat (2 ^ m)) = nseq m false ++ [:: true].
Proof.
elim => // m0 IH.
rewrite [in X in _ = X]/= -IH bin_of_nat_two_pow N2bitseq_2 //.
suff [i Hi] : exists i, 2 ^ m0 = nat_of_pos i.
  rewrite Hi.
  by apply bin_of_nat_nat_of_pos_not_0.
exists (Pos.of_nat (2 ^ m0)).
rewrite -BinPos_nat_of_P_nat_of_pos Nat2Pos.id //.
apply/eqP.
by rewrite -lt0n expn_gt0.
Qed.

Lemma size_N2bitseq_ub' : forall i n, nat_of_bin i <> O ->
  nat_of_bin i < 2 ^ n -> size (N2bitseq i) <= n.
Proof.
case=> //=.
elim => [p IHp n _ H /= | p IHp n _ H /= | ].
- destruct n => //.
  have X : nat_of_pos p < 2 ^ n.
    rewrite /= NatTrec.doubleE in H.
    have {H}H : (nat_of_pos p).*2 < 2 ^ n.+1.
      by apply leq_ltn_trans with (nat_of_pos p).*2.+1.
    by rewrite expnSr muln2 ltn_double in H.
  apply IHp in X; last by exact: nat_of_pos_not_0.
  by apply leq_ltn_trans with n.
- destruct n => //.
  + rewrite expn0 in H.
    have {H}H : nat_of_pos (BinPos.xO p) = O.
      by destruct (nat_of_pos (BinPos.xO p)).
    by move: (@nat_of_pos_not_0 (BinPos.xO p)).
  + have X : nat_of_pos p < 2 ^ n.
      by rewrite /= NatTrec.doubleE expnSr muln2 ltn_double in H.
    apply IHp in X; last by exact: nat_of_pos_not_0.
    by apply leq_ltn_trans with n.
- by case.
Qed.

Lemma size_pad_positive c (s : bitseq) :
  pad_seqL false (rev (c :: positive2bitseq (bitseq2positive s))) (size s).+2 =
  pad_seqL false (rev (positive2bitseq (bitseq2positive s))) (size s).+1 ++
  [:: c].
Proof.
rewrite /pad_seqL !size_rev /=.
rewrite ltnS.
case Hsz: (size _ <= _).
  by rewrite subSS rev_cons -cats1 catA.
have Hup := bitseq2positive_up _ _ (leqnn (size s)).
have Hub' :=
  size_N2bitseq_ub' (Npos (bitseq2positive s)) ((size s).+1)
  (@nat_of_pos_not_0 _).
simpl in Hub'.
rewrite -BinPos_nat_of_P_nat_of_pos in Hub'.
by rewrite Hub' in Hsz.
Qed.

Lemma size_N2bitseq_ub i n : i <> O ->
  i < 2 ^ n -> size (N2bitseq (bin_of_nat i)) <= n.
Proof.
move=> Hi Hin. apply (size_N2bitseq_ub' (bin_of_nat i) n); by rewrite bin_of_natK.
Qed.

Lemma size_N2bitseq_lb' : forall i n,
  2 ^ n <= nat_of_bin i -> n < size (N2bitseq i).
Proof.
case => [m abs|].
  suff : False by done.
  by rewrite leqn0 expn_eq0 /= in abs.
elim => [p IHp m K /= | p IHp m K /= | ].
- destruct m => //.
  have X : 2 ^ m <= nat_of_pos p.
    rewrite /= NatTrec.doubleE expnS -ltnS -doubleS -muln2 mulnC in K.
    by rewrite ltn_pmul2r // in K.
  apply IHp in X.
  by rewrite -ltnS in X.
- destruct m => //.
  have X : 2 ^ m <= nat_of_pos p.
    rewrite /= NatTrec.doubleE expnS -muln2 mulnC in K.
    by rewrite leq_pmul2r // in K.
  apply IHp in X.
  by rewrite -ltnS in X.
- move=> m.
  rewrite -[in X in _ <= X](_ : 2 ^ 0 = 1%num) //.
  by rewrite leq_exp2l.
Qed.

Lemma size_N2bitseq_lb : forall i n,
  2 ^ n <= i -> n < size (N2bitseq (bin_of_nat i)).
Proof.
move=> i n Hn.
apply size_N2bitseq_lb'.
by rewrite bin_of_natK.
Qed.

(** remove leading false's: *)
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
elim=> [// | a IH l Hsz].
rewrite /pad_seqL /=.
case: ifP => // Ha.
  by rewrite subSS rem_lea_false_nseq.
have {Hsz Ha}Ha : a = size l.
  move/negbT in Ha.
  by rewrite Hsz in Ha.
by rewrite Ha take_size.
Qed.

Definition bitseq2N s : N :=
  match rem_lea_false s with
    | [::] => N0
    | true :: t => Npos (bitseq2positive (rev t))
    | _ => N0 (* shouldn't happen *)
  end.

Lemma bitseq2N_false : forall l, bitseq2N (false :: l) = bitseq2N l.
Proof. by elim. Qed.

Lemma bitseq2N_nseq_false : forall k, bitseq2N (nseq k false) = N0.
Proof. by elim. Qed.

Lemma bitseq2N_up : forall p l, size l <= p ->
  N.to_nat (bitseq2N l) < 2 ^ p.
Proof.
elim=> [|p IH].
  by case.
case.
  move=> _ /=.
  by rewrite expn_gt0.
move=> h t H1.
destruct h; last first.
  rewrite bitseq2N_false.
  eapply ltn_trans; first by apply IH.
  by rewrite ltn_exp2l.
rewrite /=.
apply bitseq2positive_up.
by rewrite size_rev.
Qed.

Lemma bitseq2positive_nseq_false : forall p, Pos.to_nat (bitseq2positive (nseq p false)) = 2 ^ p.
Proof. elim=> // p IH /=; by rewrite expnS -IH Pos2Nat.inj_xO. Qed.

Lemma bitseq2N_true : forall p, N.to_nat (bitseq2N (true :: nseq p false)) = 2 ^ p.
Proof.
elim=> // p IH /=.
by rewrite (_ : false :: _ = nseq p.+1 false) // rev_nseq bitseq2positive_nseq_false.
Qed.

Lemma bitseq2N_0 : forall n0 p, bitseq2N p = N0 -> size p = n0 ->
  p = nseq n0 false.
Proof. elim => [ [] // | n0 IH [|[] t] //= Hp [Hsz] ]. by rewrite -(IH t). Qed.

Lemma N2bitseq_bin_of_nat_Npos_bitseq2positive' : forall x y,
  rev (N2bitseq x) = true :: y ->
  Npos (bitseq2positive (rev y)) = nat_of_bin x :> nat.
Proof.
elim/Nind => // x IH y.
move Heq : (Nsucc x) => eq.
destruct eq => //= H.
f_equal.
by apply positive2bitseq_bitseq2positive in H.
Qed.

Lemma N2bitseq_bin_of_nat_Npos_bitseq2positive x y :
  rev (N2bitseq (bin_of_nat x)) = true :: y ->
  Npos (bitseq2positive (rev y)) = x :> nat.
Proof.
move=> H.
by rewrite (N2bitseq_bin_of_nat_Npos_bitseq2positive' (bin_of_nat x) y H) bin_of_natK.
Qed.

Lemma size_bitseq2NK (s : bitseq) :
  size s > 0 -> size (N2bitseq (bin_of_nat (bitseq2N s))) <= size s.
Proof.
move=> Hs.
case Hbs: (bin_of_nat _). done.
apply size_N2bitseq_ub'.
  by apply nat_of_pos_not_0.
rewrite -Hbs bin_of_natK -N_bin_to_nat.
by apply bitseq2N_up.
Qed.

(** Conversion i < 2 ^ n to bitseq (of length n) *)

Definition nat2bin (i : nat) n : bitseq := pad_seqL false (rev (N2bitseq (bin_of_nat i))) n.

Lemma size_nat2bin i n : size (nat2bin i n) == n.
Proof. by rewrite /nat2bin size_pad_seqL. Qed.

Lemma nat2bin_nseq_false i r : i <> O ->
  i < 2 ^ r -> nat2bin i r <> nseq r false.
Proof.
move=> Hi Hin.
rewrite /nat2bin /pad_seqL.
have : size (N2bitseq (bin_of_nat i)) <= r by apply size_N2bitseq_ub.
rewrite leq_eqVlt.
case/orP => X.
- move/eqP : X => X.
  rewrite {1}size_rev {1}X leqnn -X -{1}size_rev subnn /=.
  have Y : N2bitseq (bin_of_nat i) <>
    rev (nseq (size (N2bitseq (bin_of_nat i))) false).
    rewrite rev_nseq.
    by apply N2bitseq_nseq_false.
  contradict Y.
  by rewrite -Y revK.
- rewrite {1}size_rev leq_eqVlt X orbC /= size_rev => abs.
 apply (@nseq_cat _ _ _ _ r (r - size (rev (N2bitseq (bin_of_nat i))))) in abs; last first.
   by rewrite size_nseq size_rev.
  case: abs => U V.
  rewrite subKn in V; last first.
    rewrite size_rev.
    by apply ltnW.
  have W : N2bitseq (bin_of_nat i) = nseq (size (rev (N2bitseq (bin_of_nat i)))) false.
    by rewrite -(revK (N2bitseq (bin_of_nat i))) {1}V rev_nseq revK.
  by apply: N2bitseq_nseq_false Hi W.
Qed.

Lemma nat2bin_two_pow p m : p < m ->
  nat2bin (2 ^ p) m = nseq (m - p.+1) false ++ true :: nseq p false.
Proof.
move=> pm.
rewrite /nat2bin /= /pad_seqL /= N2bitseq_bin_of_nat_two_pow size_rev.
by rewrite size_cat size_nseq /= -ltnS addn1 ltnS pm rev_cat /= rev_nseq.
Qed.

Lemma bitseq2N_nat2bin m x : x <> O -> (x < 2 ^ m)%nat -> bitseq2N (nat2bin x m) = x :> nat.
Proof.
move=> Hx x_m.
rewrite /bitseq2N /nat2bin.
have Hx' : bin_of_nat x <> N0.
  contradict Hx.
  rewrite (_ : 0 = bin_of_nat (nat_of_bin 0))%N // in Hx.
  by apply bin_of_nat_inj in Hx.
case: (N2bitseq_leading_bit _ Hx') => y Hy.
rewrite Hy.
rewrite rem_lea_false_pad_seqL; last first.
  move: (size_N2bitseq_ub _ _ Hx x_m).
  by rewrite -size_rev Hy.
  by apply N2bitseq_bin_of_nat_Npos_bitseq2positive in Hy.
Qed.

Lemma nat2bin_0_n n : nat2bin 0 n = nseq n false.
Proof.
rewrite /nat2bin /= /pad_seqL /=.
case: ifP => //; last by destruct n.
move=> Hn; by rewrite (_ : rev [:: false] = [:: false]) // -nseq_S -subSn // subn1.
Qed.

Lemma nat2bin_inj n i j : i < 2 ^ n -> j < 2 ^ n -> nat2bin i n = nat2bin j n -> i = j.
Proof.
move=> Hi Hj.
case/boolP : (i == 0) => [/eqP -> | /eqP Hi0].
  rewrite nat2bin_0_n => abs.
  apply/eqP/negPn/negP.
  rewrite eq_sym => /eqP.
  move/(nat2bin_nseq_false j n); by apply.
case/boolP : (j == 0) => [/eqP -> | /eqP Hj0].
  rewrite nat2bin_0_n => abs.
  apply/eqP/negPn/negP.
  move/eqP/(nat2bin_nseq_false i n); by apply.
move=> H.
by rewrite -(bitseq2N_nat2bin n i Hi0 Hi) -(bitseq2N_nat2bin n _ Hj0 Hj) H.
Qed.

Lemma bitseq2NK (s : bitseq) :
  size s > 0 -> nat2bin (N.to_nat (bitseq2N s)) (size s) = s.
Proof.
clear.
rewrite N_bin_to_nat.
elim: s.
  done.
move => b s IHs Hs /=.
case b; simpl.
  rewrite /nat2bin nat_of_posK /=.
  rewrite -size_rev -{3}(revK s).
  elim: (rev s); clear.
    done.
  move => b s IHs /=.
  rewrite -(cat1s b) rev_cat -cat_cons -IHs.
  by case b; apply size_pad_positive.
case Hs': (size s > 0); last by destruct s.
rewrite -{3}IHs /nat2bin //.
rewrite (_ : bitseq2N (false::s)=bitseq2N s) //.
rewrite /pad_seqL size_rev.
have Hsz := size_bitseq2NK _ Hs'.
rewrite !ifT //.
  by rewrite subSn.
by apply leqW.
Qed.

(** Conversion tuple / N *)

Definition tuple2N {m} (x : m.-tuple bool) : N := match x with Tuple x _ => bitseq2N x end.

Lemma tuple2N_0 n : forall p, tuple2N p = N0 -> p = [tuple of nseq n false].
Proof.
case=> p Hp /= Hp'.
apply val_inj => /=.
apply bitseq2N_0 => //; by apply/eqP.
Qed.

(** sample vectors *)

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

Lemma rev7_lb n (Hn : 2 < n) : 2 ^ (n.-1) <= (7 * 2 ^ (n - 3))%nat.
Proof.
destruct n => //=.
rewrite (@leq_trans (2 ^ 2 * 2 ^(n.+1 - 3))) //.
  rewrite -expnD leq_exp2l // addnBA // addnC addn2 -addn3.
  by rewrite -addnBA // subnn addn0.
by rewrite leq_pmul2r // expn_gt0.
Qed.

Fixpoint xOs n cont :=
  match n with
    | O => cont
    | S m => BinNums.xO (xOs m cont)
  end.

Lemma bin_of_nat_7 : forall n, 2 < n ->
  bin_of_nat 7 = BinNums.Npos (BinNums.xI (BinNums.xI (BinNums.xH))).
Proof. done. Qed.

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
rewrite (_ : n.+3 - 3 = n)%nat // in IH; last by rewrite -addn3 -addnBA // subnn.
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
