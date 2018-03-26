(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime binomial.
From mathcomp Require Import ssralg finset fingroup finalg perm zmodp matrix.
From mathcomp Require Import mxalgebra vector.
Require Import hamming num_occ ssralg_ext f2 linearcode decoding channel_code.

Import GRing.Theory.

(** * Repetition Codes *)

(** OUTLINE:
- Module Rep : definitions using the systematic form
- Section assuming_a_repair_function : minimum distance
- Section repair function : by majority vote
- Section repetition_code
*)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* TODO: move? *)
Lemma seq_block_inv (A : Type) : forall r (l : seq A) k,
  size l = r * k.+1 -> exists l1 l2,
    l = l1 ++ l2 /\ size l1 = r /\ size l2 = r * k.
Proof.
elim=> [l r | r IH l [ | k H] ].
- rewrite !mul0n => Hl.
  exists l, nil; by rewrite cats0.
- rewrite muln1 => H.
  exists (take (r.+1) l), nil.
  rewrite cats0 take_oversize; by [rewrite muln0 | rewrite H].
- exists (take (r.+1) l), (drop (r.+1) l).
  rewrite cat_take_drop size_drop H size_take H ltn_Pmulr //.
  repeat (split => //).
  by rewrite -{2}(muln1 (r.+1)) -(mulnBr (r.+1)).
Qed.

(* TODO: move? *)
Lemma dH_num_occ_opp r a (v : 'rV_ r) :
  dH (const_mx a) v = num_occ (negF2 a) (tuple_of_row v).
Proof.
rewrite /dH /wH.
rewrite (_ : tuple_of_row (const_mx a%R - v) = [tuple of map (fun x => F2_of_bool (x != a%R)) (tuple_of_row v)]); last first.
  apply eq_from_tnth => i.
  rewrite tnth_mktuple tnth_map tnth_mktuple !mxE.
  by case/F2P : a; case: F2P => //; rewrite subrr.
rewrite {1}/num_occ count_map /preim.
apply eq_count => /= x.
rewrite !inE.
by case/F2P : a; case/F2P : x.
Qed.

(* TODO: move? *)
Lemma num_occ_negF2 a r (v : r.-tuple 'F_2) : num_occ a v + num_occ (negF2 a) v = r.
Proof.
rewrite /num_occ -[RHS](size_tuple v) -[RHS](count_predC (fun x => a == x) v).
congr (_ + _).
  apply eq_count => /= i; by rewrite inE eq_sym.
apply eq_count => /= i; rewrite !inE.
by case/F2P : i; case/F2P : a.
Qed.

(* TODO: move? *)
Lemma num_occ_tuple_F2 a r (v : r.-tuple 'F_2):
  r./2 < num_occ a v ->
  num_occ (negF2 a) v <= num_occ a v.
Proof.
move=> H.
rewrite -(leq_add2l (num_occ a v)) (num_occ_negF2 a v) addnn.
apply leq_trans with (r./2).*2.+1.
  rewrite -{1}(odd_double_half r) -addn1 addnC leq_add2l; by case: odd.
by rewrite ltn_double.
Qed.

Module Rep.

Section repcode_sysform.

Variable n' : nat.
Let n := n'.+1.
Let dim := 1.

Definition CSM : 'cV['F_2]_(n - dim) := const_mx 1%R.

Lemma dimlen : 1 <= n. Proof. by []. Qed.

Definition code := kernel (Syslcode.PCM dimlen CSM).

Local Open Scope vec_ext_scope.

(** Repetition codes contains only the codewords 00...0 and 11...1 *)
Lemma codewords x : x \in code -> (x = const_mx 1 \/ x = 0)%R.
Proof.
rewrite mem_kernel_syndrome0 /= /syndrome /Syslcode.PCM /CSM => abs.
have : forall i : 'I_n.-1, x ``_ ord0 = x ``_ (lift ord0 i).
  move=> i.
  set icast := cast_ord (esym (@subn1 n)) i.
  move/eqP/rowP : abs => /(_ icast).
  rewrite !mxE (bigD1 ord0) //= castmxE /= cast_ord_id (_ : _ icast _ = 1%R); last first.
    rewrite mxE.
    case: splitP => [j /= _ | k /=]; by [rewrite mxE | rewrite add1n].
  rewrite mul1r mxE (bigD1 (lift ord0 i)) //=.
  set tmp := (X in (_ + (X + _) = _)%R -> _).
  have -> : tmp = x ``_ (lift ord0 i).
    rewrite {}/tmp castmxE /= mxE.
    case: splitP => [j | k /=].
      by rewrite {j}(ord1 j) mxE mul1r mxE.
    rewrite /bump leq0n /= 2!add1n; case => ik.
    rewrite !mxE (_ : _ == _ = true); last by apply/eqP/val_inj.
    by rewrite mul1r.
  rewrite {}/tmp.
  set tmp := (X in (_ + (_ + X) = _)%R -> _).
  suff -> : tmp = 0%R.
    by move/eqP; rewrite addr_eq0 ?addr0 oppr_char2 // => /eqP.
  rewrite {}/tmp.
  set tmp := BIG_F.
  set tmp' := BIG_P.
  rewrite (eq_bigr (fun x => (0 : 'F_2))%R); first by rewrite big_const iter_addr0.
  move=> i1.
  case/andP => K1 K2.
  rewrite {}/tmp castmxE /= cast_ord_id mxE.
  case: splitP => [j /= | k /=].
    rewrite {j}(ord1 j) => Hi1.
    exfalso.
    move/negP : K1; apply.
    by apply/eqP/val_inj.
  rewrite add1n !mxE => i1k.
  rewrite (_ : _ == _ = false); first by rewrite mul0r.
  apply/negbTE.
  apply: contra K2 => /eqP.
  move/val_eqP => /= /eqP => ik.
  apply/eqP/val_inj => /=.
  by rewrite /bump leq0n /= add1n i1k ik.
move H : (x ``_ ord0) => h.
case/F2P : h H => h H; [right | left].
  apply/rowP => b; rewrite mxE.
  case: (unliftP ord0 b) =>[b' ->| -> //].
  by rewrite -H.
apply/rowP => b; rewrite mxE.
case: (unliftP ord0 b) =>[b' ->| -> //].
by rewrite -H.
Qed.

Definition discard : discardT [finType of 'F_2] n [finType of 'rV['F_2]_1] :=
  fun x => if x == const_mx 1%R then const_mx 1%R else const_mx 0%R.

Lemma compatible : cancel_on code (Syslcode.encode dimlen CSM) discard.
Proof.
move=> /= x.
case/codewords => ->.
  apply/rowP => i.
  rewrite !mxE /discard eqxx /Syslcode.encode ffunE.
  rewrite /Syslcode.GEN /= !mxE big_ord_recl /= big_ord0 !mxE mul1r addr0.
  rewrite castmxE !cast_ord_id /= !mxE /=; case: splitP.
    move=> j; by rewrite (ord1 j) !mxE eqxx.
  move=> k Hk.
  by rewrite !mxE oppr_char2.
apply/rowP => i.
rewrite !mxE /discard.
rewrite (_ : _ == _ = false); last first.
  apply/eqP.
  move/rowP/(_ ord0).
  by rewrite !mxE //.
by rewrite /Syslcode.encode ffunE mul0mx mxE.
Qed.

Definition Lcode_wo_repair (f : repairT _ _ _) (Hf : oimg f \subset code) :=
  @Syslcode.t _ _ _ dimlen CSM _ Hf discard compatible.

End repcode_sysform.

End Rep.

(** We can check that the encoding function indeed only performs
replication of the bit to encode. *)
Lemma rep_encodeE' r (b : 'F_2) H :
  Syslcode.encode H (Rep.CSM r) (const_mx b) = row_of_tuple [tuple of nseq r.+1 b].
Proof.
rewrite /row_of_tuple /Syslcode.encode /Syslcode.GEN ffunE (mulmx_castmx_cols_comm subnKC).
apply/rowP => i; rewrite mxE.
rewrite /tnth nth_nseq (ltn_ord i) castmxE /= cast_ord_id mul_mx_row mulmx1 mxE.
case: splitP => [j _| k /= bk]; first by rewrite mxE.
rewrite mxE (bigD1 ord0) //= !mxE oppr_char2 // mulr1 big_pred0; last first.
  move=> x /=; by rewrite (ord1 x) eqxx.
by rewrite addr0.
Qed.

Lemma rep_encodeE r b H :
  Syslcode.encode H (Rep.CSM r) (const_mx b) = (const_mx b)%R.
Proof.
rewrite /Syslcode.encode ffunE /Syslcode.GEN.
apply/rowP => i; rewrite !mxE.
rewrite (bigD1 ord0) //= !mxE castmxE /= mxE.
case: split => [a|b0].
- rewrite {a}(ord1 a) mxE /= mulr1 big_pred0 ?addr0 //.
  move=> x; by rewrite {x}(ord1 x).
- rewrite !mxE mulrN1 oppr_char2 // big_pred0 ?addr0 //.
  move=> x; by rewrite {x}(ord1 x).
Qed.

Lemma rep_cnot0 r (f : repairT _ _ _) (Hf : oimg f \subset Rep.code r) :
  {c | c \in Encoder.enc (Lcode.enc (Rep.Lcode_wo_repair Hf)) @: 'rV_ _}.
Proof.
exists 0%R.
apply/imsetP; exists (const_mx 0%R) => //.
by rewrite /= rep_encodeE.
Defined.

Lemma one_in_code r : (const_mx 1)%R \in Rep.code r.
Proof.
rewrite mem_kernel_syndrome0 /syndrome /Rep.CSM /Syslcode.PCM.
apply/eqP/rowP => a; rewrite !mxE.
rewrite (bigD1 ord0) //= (bigD1 (lift ord0 (cast_ord (@subn1 r.+1) a))) //=.
rewrite -[RHS](addrr_char2 (@char_Fp 2 erefl) 1%R) -[X in _ = (_ + X)%R]addr0.
congr (_ + (_ + _))%R.
- rewrite castmxE /= cast_ord_id mxE.
  case: splitP => // j /= _; by rewrite 3!mxE mulr1.
- rewrite castmxE /= cast_ord_id mxE.
  case: splitP => [j /= | k /= Hk].
    rewrite {j}(ord1 j) /= => abs.
    move: (neq_bump 0 a); by rewrite abs.
  rewrite 3!mxE mulr1.
  move: Hk.
  rewrite /bump leq0n /= 2!add1n.
  case => Hk.
  case/boolP : (a == k) => // abs.
  suff : False by done.
  move/negP : abs; apply.
  by apply/eqP/val_inj.
- rewrite (eq_bigr (fun x => 0%R)); first by rewrite big_const iter_addr0.
  move=> i /andP [] H1 H2.
  rewrite 2!mxE mulr1 castmxE /= cast_ord_id mxE.
  case: splitP => [j /= | k /= ik].
    rewrite {j}(ord1 j) => abs.
    suff : False by done.
    move/negP : H1; apply.
    by apply/eqP/val_inj.
  rewrite mxE.
  case/boolP : (a == k) => // /eqP ?; subst k.
  exfalso.
  move/negP : H2; apply.
  by apply/eqP/val_inj.
Qed.

Section assuming_a_repair_function.

Variable r : nat.
Variable f : repairT [finType of 'F_2] [finType of 'F_2] r.+1.
Hypothesis Hf : oimg f \subset Rep.code r.
Let RepLcode := Rep.Lcode_wo_repair Hf.

(** Repetition codes are not trivial *)
Lemma not_trivial_rep_code : not_trivial RepLcode.
Proof.
rewrite /not_trivial /=.
exists (const_mx 1)%R.
apply/andP; split; first by rewrite one_in_code.
apply/eqP.
move/matrixP/(_ ord0 ord0); by rewrite !mxE.
Qed.

Lemma repcode_codewords : [set cw in RepLcode] = [set const_mx 1 ; 0]%R.
Proof.
apply/setP => /= x.
case H : (x \in [set _ ; _]) => [|].
  rewrite !inE in H.
  rewrite inE mem_kernel_syndrome0 /syndrome /=.
  case/orP : H => /eqP ->.
    move: (one_in_code r).
    by rewrite mem_kernel_syndrome0.
  by rewrite trmx0 mulmx0 trmx0 eqxx.
apply: contraFF H => H.
rewrite !inE.
apply/orP.
rewrite inE in H.
case/(@Rep.codewords _ _) : H => ->; rewrite eqxx; by [left | right].
Qed.

Lemma non_0_codeword_rep : non_0_cw not_trivial_rep_code = (const_mx 1)%R.
Proof.
rewrite /non_0_cw.
case/andP: (xchooseP not_trivial_rep_code) => H1 H2.
move: repcode_codewords.
move/setP/(_ (xchoose not_trivial_rep_code)).
rewrite inE => Htmp.
rewrite Htmp inE in H1.
case/orP : H1.
  rewrite inE.
  by move/eqP.
by rewrite inE (negbTE H2).
Qed.

(** The minimum distance is r.+1  *)
Lemma min_dist_repcode (Hr : odd r.+1) : min_dist not_trivial_rep_code = r.+1.
Proof.
rewrite /min_dist /= (_ : min_wH_cw _ = (const_mx 1))%R; last first.
  rewrite /min_wH_cw.
  case: arg_minP => /=.
    rewrite non_0_codeword_rep.
    rewrite (one_in_code r) /=.
    rewrite wH_eq0 /=.
    apply/eqP => /matrixP/(_ ord0 ord0); by rewrite !mxE.
  move=> i Hi _.
  have {Hi}Hi : i \in Rep.Lcode_wo_repair Hf /\ wH i != 0.
    split; last by case/andP : Hi.
    by case/andP : Hi.
  move/setP: repcode_codewords => /(_ i).
  rewrite inE => Htmp.
  rewrite Htmp in Hi.
  case : Hi => H1 H2.
  rewrite !inE in H1.
  case/orP : H1.
    by move/eqP.
  move=> /eqP Hi.
  by rewrite Hi wH0 eqxx in H2.
rewrite wH_sum (eq_bigr (fun=> 1)).
  by rewrite sum_nat_const card_ord muln1.
move=> /= i _; by rewrite mxE.
Qed.

(** The number of error that can be fixed by MD-decoding is r/2 *)
Lemma mdd_err_cor_rep (Hr : odd r.+1) : mdd_err_cor not_trivial_rep_code = r./2.
Proof. by rewrite /mdd_err_cor min_dist_repcode // Hr. Qed.

End assuming_a_repair_function.

Section repair_function.

(** Decoding by majority vote *)
Definition majority_vote r (l : seq 'F_2) : option ('rV['F_2]_r) :=
  let cnt := num_occ 1%R l in
  if r./2 < cnt then Some (const_mx 1)%R
  else if (r./2 == cnt) && ~~ odd r then None
  else Some (const_mx 0)%R.

Definition repair r : repairT [finFieldType of 'F_2] [finFieldType of 'F_2] r.+1 :=
  [ffun l => majority_vote r.+1 (tuple_of_row l)].

Lemma repair_odd (r : nat) (Hr : odd r.+1) x : @repair r x != None.
Proof.
rewrite /repair /majority_vote ffunE.
case: ifPn => //; by rewrite Hr /= andbF.
Qed.

Lemma reprepair_img r : oimg (@repair r) \subset Rep.code r.
Proof.
apply/subsetP => y. rewrite inE => /existsP [x].
rewrite mem_kernel_syndrome0 /repair /majority_vote ffunE; case: ifPn => [_ /eqP [<-]|_].
  by rewrite -mem_kernel_syndrome0 one_in_code.
case: ifPn => // _ /eqP [<-].
by rewrite -mem_kernel_syndrome0 mem0v.
Qed.

(** Decoding by majority vote implements MD-decoding *)
Lemma rep_MD_decoding r :
  MD_decoding [set cw in Rep.code r]
              (Decoder.repair (Lcode.dec (Rep.Lcode_wo_repair (@reprepair_img r)))).
Proof.
move=> v.
rewrite /MD_decoding_alt => /= m vm m'.
move=> m'C.
rewrite /repair in vm.
move: vm.
rewrite ffunE.
move H : (majority_vote _ _) => [h | //].
case=> <-.
rewrite /majority_vote in H.
have Hm' : (m' = const_mx 0 \/ m' = const_mx 1)%R.
  move: m'C; rewrite inE => /Rep.codewords; tauto.
case: ifP H.
  move=> Hr [] h1.
  subst h.
  case: (Hm'); last first.
    by move => ->.
  move=> ->.
  rewrite 2!dH_num_occ_opp.
  rewrite {2}/negF2 eqxx; by apply num_occ_tuple_F2.
move/negbT.
rewrite -leqNgt => H.
case: ifP => //.
move/negbT.
rewrite negb_and negbK.
case/orP => H1.
  case=> ?; subst h.
  case: (Hm').
    by move=> ->.
  move=> ->.
  rewrite 2!dH_num_occ_opp.
  apply num_occ_tuple_F2.
  rewrite (_ : num_occ _ _ = r.+1 - num_occ 1%R (tuple_of_row v)); last first.
    rewrite -[in X in _ = X - _](num_occ_negF2 1%R (tuple_of_row v)).
    by rewrite addnC addnK.
  apply leq_ltn_trans with (r.+1 - (r.+1)./2); last first.
    apply ltn_sub2l.
      apply: (leq_ltn_trans H).
      rewrite -ltn_double (_ : _./2.*2 = r.+1 - odd r.+1); last first.
        by rewrite -{2}(odd_double_half r.+1) addnC addnK.
      rewrite -addnn.
      apply leq_ltn_trans with r.+1; last first.
        by rewrite addnS ltnS ltn_addr.
      by apply leq_subr.
    by rewrite ltn_neqAle H eq_sym H1.
  by rewrite -{2}(odd_double_half r.+1) -addnn addnA addnC addnA addnK leq_addr.
case=> ?; subst h.
case: Hm' => -> //.
rewrite 2!dH_num_occ_opp.
apply num_occ_tuple_F2.
rewrite (_ : num_occ _ _ = r.+1 - num_occ 1%R (tuple_of_row v)); last first.
  by rewrite -[in X in _ = X - _](num_occ_negF2 1%R (tuple_of_row v)) addnC addnK.
  rewrite -ltn_double.
  rewrite (_ : _./2.*2 = r.+1 - odd r.+1); last first.
    by rewrite -{2}(odd_double_half r.+1) addnC addnK.
  rewrite H1 /= subn1 /=.
  rewrite doubleB.
  apply leq_trans with ((r.+1).*2 - (r.+1)./2.*2); last first.
    apply leq_sub2l.
    by rewrite leq_double.
  rewrite (_ : (r.+1)./2.*2 = r.+1 - odd r.+1); last first.
    by rewrite -{2}(odd_double_half r.+1) addnC addnK.
  rewrite subnBA //; last first.
    by case: (odd r.+1).
  by rewrite -addnn -addnA addnC addnK ltn_addr.
Qed.

End repair_function.

(* TODO: remove? *)
Section repetition_code.

Variable r : nat.
Let LC := Rep.Lcode_wo_repair (@reprepair_img r).

Lemma rep_encode_decode m v : m \in LC ->
  let enc := Lcode.enc LC in
  let rep := Decoder.repair (Lcode.dec LC) in
  rep v != None ->
  dH m v <= mdd_err_cor (not_trivial_rep_code (@reprepair_img r)) -> rep v = Some m.
Proof.
move=> Hm enc dec H1 H2.
apply: (@mddP _ _ _ _ (@rep_MD_decoding r) (not_trivial_rep_code (@reprepair_img r)) ) => //=.
by apply reprepair_img.
Qed.

End repetition_code.
