(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg perm zmodp.
From mathcomp Require Import matrix mxalgebra vector.
Require Import hamming num_occ ssralg_ext f2 linearcode decoding channel_code.

(**md**************************************************************************)
(* # Repetition Codes                                                         *)
(*                                                                            *)
(* Main lemmas:                                                               *)
(* - The minimum distance is r.+1 (`min_dist_repcode`)                        *)
(* - Decoding by majority vote implements MD-decoding (`repcode_MD_decoding`) *)
(*                                                                            *)
(* ```                                                                        *)
(*   Rep.code r == definition of the r-repetition code                        *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.

Local Open Scope num_occ_scope.

(* TODO: move? *)
Lemma seq_block_inv A : forall r (l : seq A) k,
  size l = r * k.+1 -> exists l1 l2, l = l1 ++ l2 /\ size l1 = r /\ size l2 = r * k.
Proof.
elim=> [l r | r IH l [ | k H] ].
- rewrite !mul0n => Hl.
  by exists l, nil; rewrite cats0.
- rewrite muln1 => H.
  exists (take (r.+1) l), nil.
  by rewrite cats0 take_oversize; [rewrite muln0 | rewrite H].
- exists (take (r.+1) l), (drop (r.+1) l).
  rewrite cat_take_drop size_drop H size_take H ltn_Pmulr //.
  repeat (split => //).
  by rewrite -{2}(muln1 (r.+1)) -(mulnBr (r.+1)).
Qed.

(* TODO: move? *)
Lemma dH_num_occ_opp r a (v : 'rV_ r) :
  dH (const_mx a) v = N(negF2 a | tuple_of_row v).
Proof.
rewrite /dH /wH.
rewrite (_ : tuple_of_row _ =
    [tuple of map (fun x => F2_of_bool (x != a%R)) (tuple_of_row v)]); last first.
  apply eq_from_tnth => i.
  rewrite tnth_mktuple tnth_map tnth_mktuple !mxE.
  by case/F2P : a; case: F2P => //; rewrite ?subrr ?subr0 ?sub0r ?oppr_char2.
rewrite {1}/num_occ count_map /preim.
apply eq_count => /= x.
rewrite !inE.
by case/F2P : a; case/F2P : x.
Qed.

(* TODO: move? *)
Lemma num_occ_negF2 a r (v : r.-tuple 'F_2) : N(a | v) + N(negF2 a | v) = r.
Proof.
rewrite /num_occ -[RHS](size_tuple v) -[RHS](count_predC (fun x => a == x) v).
congr (_ + _).
  apply eq_count => /= i; by rewrite inE eq_sym.
apply eq_count => /= i; rewrite !inE.
by case/F2P : i; case/F2P : a.
Qed.

(* TODO: move? *)
Lemma num_occ_tuple_F2 a r (v : r.-tuple 'F_2):
  r./2 < N(a | v) -> N(negF2 a | v) <= N(a | v).
Proof.
move=> H.
rewrite -(leq_add2l (N(a | v))) (num_occ_negF2 a v) addnn.
rewrite (@leq_trans (r./2).*2.+1) // ?ltn_double //.
rewrite -{1}(odd_double_half r) -addn1 addnC leq_add2l; by case: odd.
Qed.

Local Open Scope ring_scope.
Local Open Scope vec_ext_scope.

Module Rep.
Section rep.
Variable n' : nat.
Let n := n'.+1.
Let dim := 1%nat.

Definition CSM : 'cV['F_2]_(n - dim) := const_mx 1.

Lemma dimlen : 1 <= n. Proof. by []. Qed.

Definition code := kernel (Syslcode.PCM dimlen CSM).

(* The encoding function only performs replication of the bit to encode. *)
Lemma encodeE (b : 'F_2) H : Syslcode.encode H CSM (const_mx b) = const_mx b.
Proof.
rewrite /row_of_tuple /Syslcode.encode /Syslcode.GEN ffunE.
rewrite (mulmx_castmx_cols_comm subnKC); apply/rowP => i.
rewrite mxE castmxE /= cast_ord_id mul_mx_row mulmx1 mxE.
case: splitP => [j _| k /= bk]; first by rewrite mxE.
rewrite mxE (bigD1 ord0) //= !mxE oppr_char2 // mulr1 big_pred0 ?addr0 //.
by move=> x /=; rewrite (ord1 x) eqxx.
Qed.

Let codewords' x : x \in code -> x = const_mx 1 \/ x = 0.
Proof.
rewrite mem_kernel_syndrome0 /= /syndrome /Syslcode.PCM /CSM => abs.
have : forall i : 'I_n.-1, x ``_ ord0 = x ``_ (lift ord0 i).
  move=> i.
  set i0 := cast_ord (esym (@subn1 n)) i.
  move/eqP/rowP : abs => /(_ i0).
  rewrite !mxE (bigD1 ord0) //= castmxE /= cast_ord_id.
  rewrite (_ : _ i0 _ = 1); last first.
    rewrite mxE; case: splitP => [j _ | k] /=; by [rewrite mxE | rewrite add1n].
  rewrite mul1r mxE (bigD1 (lift ord0 i)) //=.
  rewrite [X in _ + (X + _) = _ -> _](_ : _ = x ``_ (lift ord0 i)); last first.
    rewrite castmxE /= mxE.
    case: splitP => [j | k /=]; first by rewrite {j}(ord1 j) mxE mul1r mxE.
    rewrite /bump leq0n /= 2!add1n; case => ik.
    rewrite !mxE (_ : _ == _ = true) ?mul1r //; exact/eqP/val_inj.
  rewrite [X in _ + (_ + X) = _ -> _](_ : _ = 0).
    by move/eqP; rewrite addr_eq0 ?addr0 oppr_char2 // => /eqP.
  set F := BIG_F.
  rewrite big1 // => i1 /andP[i10 i11].
  rewrite {}/F castmxE /= cast_ord_id mxE.
  case: splitP => [j | k] /=.
    rewrite {j}(ord1 j) => ?.
    exfalso; move/negP : i10; apply; exact/eqP/val_inj.
  rewrite add1n !mxE => i1k.
  rewrite (_ : _ == _ = false) ?mul0r //.
  apply: contraNF i11 => /eqP/val_eqP /= /eqP ik.
  by apply/eqP/val_inj => /=; rewrite /bump leq0n /= add1n i1k ik.
move H : (x ``_ ord0) => h.
case/F2P : h H => h H; [right | left];
  (apply/rowP => b; rewrite mxE ;
   case: (unliftP ord0 b) =>[b' ->| -> //] ;
   by rewrite -H).
Qed.

Lemma const_mx_in_code b : const_mx b \in code.
Proof. rewrite /code -(encodeE b dimlen); exact: Syslcode.encode_code. Qed.

(* Repetition codes contains only the codewords 00...0 and 11...1 *)
Lemma codewords : [set cw in code] = [set const_mx 1 ; 0]%R.
Proof.
apply/setP => x; apply/idP/idP.
- by rewrite inE => /codewords' -[|] ->; rewrite !inE !eqxx // orbT.
- by rewrite !inE => /orP[|] /eqP ->; rewrite const_mx_in_code.
Qed.

Lemma compatible : cancel_on code (Syslcode.encode dimlen CSM) (Syslcode.discard dimlen).
Proof.
move=> /= x; case/codewords' => ->.
- rewrite (_ : Syslcode.discard _ _ = const_mx 1) ?encodeE //.
  rewrite /Syslcode.discard ffunE /Syslcode.DIS -trmx_const -trmx_mul.
  rewrite (@castmx_mulmx_cols_comm _ _ _ subnKC).
  by rewrite castmx_const -[in LHS]col_mx_const mul_row_col mul1mx mul0mx addr0 trmx_const.
- rewrite (_ : Syslcode.discard _ _ = const_mx 0) ?encodeE //.
  by rewrite /Syslcode.discard ffunE /Syslcode.DIS mul0mx.
Qed.

Definition Lcode_wo_repair (f : repairT _ _ _) (Hf : oimg f \subset code) :=
  @Syslcode.t _ _ _ dimlen CSM _ Hf compatible.

End rep.
End Rep.

Lemma repcode_not_empty r (f : repairT _ _ _) (Hf : oimg f \subset Rep.code r) :
  {c | c \in Encoder.enc (Lcode.enc (Rep.Lcode_wo_repair Hf)) @: 'rV_ _}.
Proof.
by exists 0; apply/imsetP; exists (const_mx 0) => //; rewrite /= Rep.encodeE.
Qed.

Section minimum_distance_decoding.
Variable r : nat.
(* we assume a repair function *)
Variable f : repairT 'F_2 'F_2 r.+1.
Hypothesis Hf : oimg f \subset Rep.code r.
Let RepLcode := Rep.Lcode_wo_repair Hf.

(* Repetition codes are not trivial *)
Lemma not_trivial_replcode : not_trivial RepLcode.
Proof.
rewrite /not_trivial /=.
exists (const_mx 1)%R.
rewrite Rep.const_mx_in_code /=.
by apply/eqP => /matrixP/(_ ord0 ord0); rewrite !mxE.
Qed.

Let non_0_codeword_replcode : non_0_cw not_trivial_replcode = const_mx 1.
Proof.
rewrite /non_0_cw.
case/andP: (xchooseP not_trivial_replcode) => H1 H2.
move: (Rep.codewords r) => /setP/(_ (xchoose not_trivial_replcode)).
rewrite inE => H.
move: H1; rewrite H inE => /orP[|].
- by rewrite inE => /eqP.
- by rewrite inE (negbTE H2).
Qed.

Lemma min_dist_repcode (Hr : odd r.+1) : min_dist not_trivial_replcode = r.+1.
Proof.
rewrite /min_dist /= (_ : min_wH_cw _ = const_mx 1) ?wH_const_mx //.
rewrite /min_wH_cw.
case: arg_minnP => /=.
  rewrite non_0_codeword_replcode (Rep.const_mx_in_code r 1) /= wH_eq0 /=.
  by apply/eqP => /matrixP/(_ 0 0); rewrite !mxE.
move=> i Hi _.
have {Hi} : i \in Rep.Lcode_wo_repair Hf /\ wH i != O by split; case/andP : Hi.
move/setP: (Rep.codewords r) => /(_ i).
rewrite !inE => -> -[] /orP [/eqP // | /eqP ->].
by rewrite wH0 eqxx.
Qed.

(* The number of error that can be fixed by MD-decoding is r/2 *)
Lemma mdd_err_cor_rep (Hr : odd r.+1) : mdd_err_cor not_trivial_replcode = r./2.
Proof. by rewrite /mdd_err_cor min_dist_repcode // Hr. Qed.

End minimum_distance_decoding.

Section majority_vote_decoding.

(* Decoding by majority vote *)
Definition majority_vote r (s : seq 'F_2) : option 'rV['F_2]_r :=
  let cnt := N(1 | s) in
  if r./2 < cnt then Some (const_mx 1)
  else if (r./2 == cnt) && ~~ odd r then None
  else Some 0.

Definition repair r : repairT 'F_2 'F_2 r.+1 :=
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
  by rewrite -mem_kernel_syndrome0 Rep.const_mx_in_code.
case: ifPn => // _ /eqP [<-].
by rewrite -mem_kernel_syndrome0 mem0v.
Qed.

Lemma repcode_MD_decoding r : MD_decoding [set cw in Rep.code r]
  (Decoder.repair (Lcode.dec (Rep.Lcode_wo_repair (@reprepair_img r)))).
Proof.
move=> /= u; rewrite /MD_decoding_alt => /= v uv w.
rewrite Rep.codewords !inE => /orP wC.
move: uv; rewrite /repair ffunE.
move H : (majority_vote _ _) => [h | //].
case=> <-.
move: H; rewrite /majority_vote; case: ifPn.
  move=> Hr [<-{h}]; case: wC => /eqP -> //.
  rewrite 2!dH_num_occ_opp {2}/negF2 eqxx; exact: num_occ_tuple_F2.
rewrite -leqNgt => H.
case: ifPn => //.
rewrite negb_and negbK.
case/orP => H1 [<-{h}].
- case: wC => /eqP -> //.
  rewrite 2!dH_num_occ_opp; apply num_occ_tuple_F2.
  rewrite (_ : N(_ | _) = r.+1 - N(1%R | tuple_of_row u))%nat; last first.
    rewrite -[in X in _ = (X - _)%nat](num_occ_negF2 1%R (tuple_of_row u)).
    by rewrite addnC addnK.
  rewrite (@leq_ltn_trans (r.+1 - (r.+1)./2)%nat) //.
    by rewrite -{2}(odd_double_half r.+1) -addnn addnA addnC addnA addnK leq_addr.
  apply ltn_sub2l; last by rewrite ltn_neqAle H eq_sym H1.
  rewrite (leq_ltn_trans H) //.
  rewrite -ltn_double (_ : _./2.*2 = r.+1 - odd r.+1)%nat; last first.
    by rewrite -{2}(odd_double_half r.+1) addnC addnK.
  by rewrite -addnn (@leq_ltn_trans r.+1) // ?leq_subr // addnS ltnS ltn_addr.
- case : wC => /eqP -> //.
  rewrite 2!dH_num_occ_opp; apply num_occ_tuple_F2.
  rewrite (_ : N(_ | _) = r.+1 - N(1%R | tuple_of_row u))%nat; last first.
    rewrite -[in X in _ = (X - _)%nat](num_occ_negF2 1%R (tuple_of_row u)).
    by rewrite addnC addnK.
  rewrite -ltn_double (_ : _./2.*2 = r.+1 - odd r.+1)%nat; last first.
    by rewrite -{2}(odd_double_half r.+1) addnC addnK.
  rewrite H1 /= subn1 /= doubleB.
  rewrite (@leq_trans ((r.+1).*2 - (r.+1)./2.*2)%nat) //; last first.
    by rewrite leq_sub2l // leq_double.
  rewrite (_ : (r.+1)./2.*2 = r.+1 - odd r.+1)%nat; last first.
    by rewrite -{2}(odd_double_half r.+1) addnC addnK.
  rewrite subnBA //; last by case: (odd r.+1).
  by rewrite -addnn -addnA addnC addnK ltn_addr.
Qed.

End majority_vote_decoding.

(* TODO: remove? *)
Section repetition_code.
Variable r : nat.
Let LC := Rep.Lcode_wo_repair (@reprepair_img r).

Lemma rep_encode_decode m v : m \in LC ->
  let enc := Lcode.enc LC in
  let rep := Decoder.repair (Lcode.dec LC) in
  rep v != None ->
  dH m v <= mdd_err_cor (not_trivial_replcode (@reprepair_img r)) -> rep v = Some m.
Proof.
move=> Hm enc dec H1 H2.
apply: (@mddP _ _ _ _ (@repcode_MD_decoding r) (not_trivial_replcode (@reprepair_img r)) ) => //=.
exact: reprepair_img.
Qed.

End repetition_code.
