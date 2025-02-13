(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
Require Program.Wf.
From mathcomp Require Import all_ssreflect ssralg fingroup finalg perm zmodp.
From mathcomp Require Import matrix.
Require Import ssr_ext ssralg_ext num_occ f2 hamming tanner linearcode.

(**md**************************************************************************)
(* # Sum-Product Decoder over the BEC                                         *)
(*                                                                            *)
(* This file provides an implementation of the Sum-Product algorithm over the *)
(* binary erasure channel as a recursive function (`SP_BEC0_rec`).            *)
(******************************************************************************)

Declare Scope letter_scope.
Declare Scope bec_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope num_occ_scope.
Local Open Scope ring_scope.
Import GRing.Theory.

Local Open Scope vec_ext_scope.

Section letter.

Inductive letter := Bit of 'F_2 | Star | Blank.

Definition eql (a b : letter) :=
  match a, b with
  | Bit a', Bit b' => a' == b'
  | Star, Star => true
  | Blank, Blank => true
  | _, _ => false
  end.

Lemma eqlP : Equality.axiom eql.
Proof.
move=> a b; apply: (iffP idP) => [|<-]; last first.
  case: a => // a'; by rewrite /= eqxx.
case: a b; [|by case|by case].
by move=> a'; case => //= b' /eqP ->.
Qed.

HB.instance Definition _ := hasDecEq.Build _ eqlP.

CoInductive letter_spec : letter -> bool -> bool -> bool -> bool -> Prop :=
| letter_spec0 : letter_spec (Bit 0) true false false false
| letter_spec1 : letter_spec (Bit 1) false true false false
| letter_specstar : letter_spec Blank false false true  false
| letter_specblank : letter_spec Star false false false true.

Lemma letterP l : letter_spec l (l == Bit 0) (l == Bit 1) (l == Blank) (l == Star).
Proof.
case: l; [|by constructor|by constructor].
case/F2P; by constructor.
Qed.

Definition letter_pickle (l : letter) :=
  match l with
  | Bit a => if a == (Zp0 : 'F_2) then O else 1%N
  | Star => 2%N
  | Blank => 3%N
  end.

Definition letter_unpickle (n : nat) :=
  match n with
  | O => Some (Bit 0)
  | 1 => Some (Bit 1)
  | 2 => Some Star
  | 3 => Some Blank
  | _ => None
  end.

Lemma letter_count : pcancel letter_pickle letter_unpickle.
Proof. by case/letterP. Qed.

HB.instance Definition _ := @PCanIsCountable _ _ _ _ letter_count.

Lemma letter_enumP : Finite.axiom [::Bit 0; Bit 1; Star; Blank].
Proof. by case => //; case/F2P. Qed.

HB.instance Definition _ := @isFinite.Build letter _ letter_enumP.

Definition F2_of_letter (l : letter) : 'F_2 := if l is Bit a then a else 0.

Definition lel (a b : letter) :=
  (a == b) || if a is Bit _ then b == Star else false.

Local Notation "A '<=l' B" := (lel A B) (at level 20).

Lemma lell x : x <=l x.
Proof. by rewrite /lel eqxx orTb. Qed.

Lemma lel_Bit a b : (a <=l Bit b) = (a == Bit b).
Proof.
apply/idP/idP => [|/eqP ->]; last by rewrite lell.
case/letterP : a b => //; by case/F2P.
Qed.

Lemma lel_Star l : Star <=l l -> l = Star.
Proof. by case/letterP : l. Qed.

Lemma lel_Blank l : Blank <=l l -> l = Blank.
Proof. by case/letterP : l. Qed.

Lemma lel_trans : transitive lel.
Proof. by do 3 case/letterP. Qed.

(* lel lifted to matrices *)
Definition mxlel m n (A B : 'M[letter]_(m, n)) := [forall m, [forall n, A m n <=l B m n]].

Local Notation "A '<=m' B" := (mxlel A B) (at level 20).

Lemma lell_mat m0 n0 (A : 'M[letter]_(m0, n0)) : A <=m A.
Proof. rewrite /mxlel; apply/'forall_forallP => i j; exact: lell. Qed.

Lemma lel_trans_mat m0 n0 : transitive (@mxlel m0 n0).
Proof.
move=> A B C /'forall_forallP /= H1 /'forall_forallP H2.
apply/'forall_forallP => m1 n1; by apply: (lel_trans (H1 _ _) (H2 _ _)).
Qed.

Definition sum_letter (t : seq letter) := \sum_(l <- t) F2_of_letter l.

Definition is_Bit (l : letter) := if l is Bit _ then true else false.

Definition starblank l := ~~ is_Bit l.

Lemma starblankP x : reflect (starblank x) ((x == Star) || (x == Blank)).
Proof. apply/(iffP idP); by [case/orP => /eqP -> | case/letterP : x]. Qed.

Lemma letter_split (l : letter) : [exists b, l == Bit b] || (starblank l).
Proof.
case/letterP : l; rewrite ?orbT //.
by apply/orP; left; apply/existsP; exists 0.
by apply/orP; left; apply/existsP; exists 1.
Qed.

End letter.

Notation "A '<=l' B" := (lel A B) (at level 20) : letter_scope.
Notation "A '<=m' B" := (mxlel A B) (at level 20) : letter_scope.
Local Open Scope letter_scope.
Local Open Scope num_occ_scope.

Section Sum_Prod_def.

Definition Sum (s : seq letter) :=
  if has starblank s then Star
  else Bit (sum_letter (filter is_Bit s)).

Definition Prod (s : seq letter) :=
  if N(Bit 0 | s) > N(Bit 1 | s) then Bit 0
  else if N(Bit 0 | s) < N(Bit 1 | s) then Bit 1
  else Star.

End Sum_Prod_def.

Section Sum_prop.

Lemma Sum_blank_inv s : Sum s != Blank.
Proof. rewrite /Sum; by case: ifP. Qed.

Lemma le_Sum_Star s : Sum s <=l Star.
Proof. rewrite /Sum; by case: ifPn. Qed.

End Sum_prop.

Section Prod_prop.

Lemma Prod_filter_Star m n (A : 'M[letter]_(m, n)) n0 (s : {set 'I_m}) :
  Prod [seq A m0 n0 | m0 in s]  =
  Prod [seq A m0 n0 | m0 <- enum s & A m0 n0 != Star].
Proof.
rewrite /Prod; case: ifPn => [H|];
  do 2 rewrite (num_occ_map_filter [pred x | x != Star]) //.
- by rewrite H.
- rewrite -leqNgt leq_eqVlt => /orP[/eqP|] H;
    by [rewrite H ltnn | rewrite H ltnNge (ltnW H)].
Qed.

Lemma Prod1 l : l != Blank -> Prod [:: l] = l.
Proof. by case/letterP : l. Qed.

Lemma Prod_cons_Star s : Prod (Star :: s) = Prod s.
Proof. by []. Qed.

Lemma Prod_starblank_is_Star s : all starblank s -> Prod s = Star.
Proof.
move=> K.
rewrite /Prod.
suff : forall x : 'F_2, N(Bit x | s) = O by move=> X; rewrite 2!X.
move=> x.
apply/eqP; rewrite -notin_num_occ_0.
move/allP : K => /(_ (Bit x))/contra; exact.
Qed.

Lemma Prod_nseq_not_blank n x : n != O -> x != Blank -> Prod (nseq n x) = x.
Proof.
elim: n x => //= n IH x _ xblank; rewrite /Prod /=.
case/letterP : x xblank => //= _.
- rewrite add0n add1n (_ : N(Bit 1 | _) = O) //.
  apply/eqP; rewrite -notin_num_occ_0; apply/nseqP; by case.
- rewrite (_ : N(Bit 0 | _) = O) //.
  apply/eqP; rewrite -notin_num_occ_0; apply/nseqP; by case.
- rewrite !add0n (_ : N(Bit 1 | _) = O); last first.
    apply/eqP; rewrite -notin_num_occ_0; apply/nseqP; by case.
  rewrite (_ : N(Bit 0 | _) = O) //.
  apply/eqP; rewrite -notin_num_occ_0; apply/nseqP; by case.
Qed.

Lemma Prod_Bit (b : 'F_2) s : Prod s = Bit b -> Bit b \in s.
Proof.
rewrite /Prod.
case: ifPn => [H [<-] | H]; first by rewrite mem_num_occ_gt0 (leq_trans _ H).
case: ifPn => // H' [<-]; by rewrite mem_num_occ_gt0 (leq_trans _ H').
Qed.

Lemma Prod_cons (x : letter) h t :
  Prod [:: h] = x /\ (Prod t = x \/ Prod t = Star) ->
  Prod (h :: t) = x.
Proof.
case=> H1 H2.
rewrite /Prod /=.
case/letterP : h H1 => /=; rewrite {1}/Prod /= => ?; subst x; rewrite ?(addn0,addn1,add0n).
- case: H2; rewrite {1}/Prod.
    case: ifPn => [H3 _|].
      by rewrite ltnS leq_eqVlt H3 orbT.
    rewrite -leqNgt leq_eqVlt.
    case/orP => [/eqP ->|->//].
    by rewrite ltnn.
  case: ifPn => //; rewrite -leqNgt leq_eqVlt.
  case/orP => [/eqP|] -> //.
  rewrite ltnn => _ /=; by rewrite ltnS leqnn.
- case: H2; rewrite {1}/Prod.
    case: ifPn => [//|].
    rewrite -leqNgt leq_eqVlt.
    case/orP => [/eqP ->|H3].
      by rewrite ltnn.
    rewrite H3 => _.
    rewrite {1}add1n (leq_trans _ (leqnSn _)) // ltnNge ltnW //.
    by apply/leq_trans: H3.
  case: ifPn => //.
  rewrite -leqNgt leq_eqVlt.
  case/orP => [/eqP|] -> //.
  rewrite ltnn => _.
  by rewrite add1n ltnSn /= ltnNge leqnSn.
- by case: H2.
- by case: H2.
Qed.

Lemma Prod_StarE (s : seq letter) :
  (Prod s == Star) = [forall b, N(Bit (F2_of_bool b) | s) == N(Bit (F2_of_bool (~~ b)) | s)].
Proof.
apply/idP/idP => [| /forallP H0].
  rewrite /Prod.
  case: ifP => //.
  move/negbT.
  rewrite -leqNgt leq_eqVlt.
  case/orP => [/eqP H1|H1].
    rewrite H1 ltnn => _; apply/forallP; case; by apply/eqP.
  by rewrite H1.
by rewrite /Prod (eqP (H0 true)) ltnn.
Qed.

Lemma Prod_map_not_Star m n (A : 'M_(m, n)) n0 (s : {set 'I_m}) :
  Prod [seq A m1 n0 | m1 in s] != Star ->
  exists b m1, m1 \in s /\ A m1 n0 = Bit b.
Proof.
rewrite Prod_StarE negb_forall => /existsP[b Hb].
have [H0|] := eqVneq (N(Bit (F2_of_bool (b : bool)) | [seq A m1 n0 | m1 in s])) O.
  have : 0 < N(Bit (F2_of_bool (~~ b)) | [seq A m1 n0 | m1 in s]).
    by rewrite lt0n; apply: contra Hb => /eqP ->; exact/eqP.
  rewrite lt0n -notin_num_occ_0 negbK => /mapP[i Hi].
  by exists (F2_of_bool (~~ b)), i; rewrite mem_enum in Hi.
rewrite -notin_num_occ_0 negbK => /mapP[i Hi] H1.
exists (F2_of_bool b), i; by rewrite mem_enum in Hi.
Qed.

End Prod_prop.

Section starletter_prop.

Definition starletter x y := (x == Star) || (x == Bit y).

Lemma starletter_letter x : starletter (Bit x) x.
Proof. by rewrite /starletter eqxx orbC. Qed.

Lemma Prod_starletter m n (A : 'M_(m, n)) n0 (b : 'F_2) (s : {set 'I_m}):
  all [pred i | starletter (A i n0) b] (enum s) ->
  (exists2 i, i \in s & A i n0 != Star) ->
  Prod [seq A i n0 | i <- enum s] = Bit b.
Proof.
move=> H0 IH.
rewrite (Prod_filter_Star A n0 s).
set tmp := [seq _ | _ <- _ & _].
rewrite (_ : tmp = nseq (size tmp) (Bit b)); last first.
  apply: all_pred1P.
  apply/allP => /= x0.
  case/mapP => /= m1 Hm1 x0m1.
  rewrite x0m1.
  rewrite mem_filter in Hm1.
  case/andP : Hm1 => m1star Hm1.
  move/allP : H0 => /(_ m1); rewrite mem_enum => H0.
  have /H0 : m1 \in s by move: Hm1; rewrite mem_enum.
  by rewrite /= /starletter (negbTE m1star).
rewrite Prod_nseq_not_blank // /tmp size_map size_filter -lt0n -has_count.
apply/hasP.
case: IH => i H1 H2.
exists i => //; by rewrite mem_enum.
Qed.

Lemma Prod_cons_starletter m n (b : 'F_2) n0 (s : {set 'I_m}) (M : 'M[letter]_(m, n)):
  all [pred i | starletter (M i n0) b] (enum s) ->
  Prod (Bit b :: [seq M i n0 | i in s]) = Bit b.
Proof.
move=> /= H1.
apply/Prod_cons.
rewrite Prod1 //; split => //.
set l := [seq _ | _ in _].
case/boolP : (Bit b \in l) => Hl.
  left.
  transitivity (Prod [seq M m0 n0 | m0 <- (enum s)]) => //.
  apply (Prod_starletter H1).
  case/mapP : Hl => m1 H2 H3.
  exists m1; rewrite -?H3 //; by rewrite mem_enum in H2.
right.
rewrite (_ : l = nseq (size l) Star); last first.
  apply/all_pred1P/allP => /= x.
  case/mapP => m1 Hm1 Hx.
  move: H1 => /allP H1.
  case/orP: (H1 _ Hm1) => [|abs].
    by rewrite Hx.
  exfalso.
  move/negP : Hl; apply.
  apply/mapP; exists m1 => //.
  by rewrite (eqP abs).
apply/Prod_starblank_is_Star; by rewrite all_nseq orbT.
Qed.

Lemma Kop_proof x1 x2 x3 y1 y2 y3 :
  (x3 <= x2) && ((x3 == x2) ==> x1) ->
  (y3 <= y2) && ((y3 == y2) ==> y1) ->
  (x3 + y3 <= x2 + y2) && ((x3 + y3 == x2 + y2)%nat ==> x1 && y1).
Proof.
move=> /andP [Hx Hx1] /andP [Hy Hy1].
rewrite (@leq_trans (x3+y2)) ?leq_add2r //=.
  apply/implyP=> H3.
  move/implyP: Hx1 => ->.
    move/implyP: Hy1 => -> //.
    rewrite -(leq_add2r y3) (eqP H3) leq_add2l in Hx.
    by rewrite eqn_leq Hy Hx.
  rewrite -(leq_add2l x3) (eqP H3) leq_add2r in Hy.
  by rewrite eqn_leq Hx Hy.
by rewrite leq_add2l Hy.
Qed.

Definition num_stars m n (A : 'M[letter]_(m, n)) : nat :=
  \sum_(m0 < m) \sum_(n0 < n) (A m0 n0 == Star).

Lemma lmat_le_decr m n (A B : 'M_(m, n)) :
  A <=m B -> (A == B) || (num_stars A < num_stars B).
Proof.
move=> Hle.
suff : (num_stars A <= num_stars B) && ((num_stars A == num_stars B) ==>
       \big[andb/true]_(i < m) (row i A == row i B)).
  case/andP => A_le_B.
  have [A_eq_B|A_not_B _] := eqVneq (num_stars A) (num_stars B).
    rewrite big_all => Hall.
    apply/orP; left.
    apply/eqP/row_matrixP => i.
    move/allP/(_ i) : Hall.
    by rewrite mem_index_enum => /(_ isT)/eqP.
  by rewrite ltn_neqAle A_le_B A_not_B orbT.
rewrite /num_stars.
elim/big_ind3 : _ => //.
  by apply Kop_proof.
move=> i _.
set lft := (_ <= _).
set rgt := (_ == _).
suff : lft && (rgt ==> \big[andb/true]_(j < n) (A i j == B i j)).
  rewrite /lft /rgt.
  case/andP => ->.
  case/boolP : (_ == _) => ? //=.
  rewrite big_all => Hall.
  apply/eqP/rowP => j.
  move/allP/(_ j): Hall.
  by rewrite mem_index_enum !mxE => /(_ isT)/eqP.
rewrite /lft /rgt.
elim/big_ind3 : _ => //.
  apply Kop_proof.
move=> j _.
move/'forall_forallP : Hle => /(_ i j).
by case/letterP : (A i j); case/letterP : (B i j).
Qed.

End starletter_prop.

Section SumProd_algo_mxStar.
Variables (m n : nat) (H : 'M['F_2]_(m, n)).

Local Notation "''F'" := (Fnext H).

Definition mxStar := \matrix_(i < m, j < n) if i \in 'F j then Star else Blank.

Lemma mxStarE i j : i \in 'F j -> mxStar i j = Star.
Proof. rewrite /mxStar => ij; by rewrite mxE ij. Qed.

Lemma all_mxStar n0 : all [pred i | mxStar i n0 == Star] (enum ('F n0)).
Proof.
apply/allP => m0 Hm0; by rewrite inE mxStarE // -mem_enum.
Qed.

Lemma Prod_mxStar_col_Star n0 (s : {set 'I_m}) : Prod [seq (col n0 mxStar) m0 ord0 | m0 in s] = Star.
Proof.
rewrite Prod_starblank_is_Star //=; apply/allP => y' /mapP [x Hx ->].
rewrite 2!mxE; by case: ifPn.
Qed.

End SumProd_algo_mxStar.

Section mat_approx.
Variable (m n : nat).

Definition blank_to_star a := if a == Blank then Star else a.

Lemma Bit_col l b (bl : Bit b <=l l) (A : 'cV[letter]_m) (s : {set 'I_m}) :
  (forall i : 'I_m, Bit b <=l blank_to_star (A i ord0)) ->
  forall b' : 'F_2, Bit b' \in l :: [seq A m0 ord0 | m0 in s] -> b' = b.
Proof.
move=> Ha b'.
rewrite in_cons => /orP [Hy|].
  by move: bl; rewrite -(eqP Hy) lel_Bit => /eqP[].
move/mapP => [x Hx Hf].
by move: (Ha x); rewrite -Hf lel_Bit => /eqP[].
Qed.

Lemma Prod_cons_Bit l b (bl : Bit b <=l l) (A : 'cV[letter]_m) (s : {set 'I_m}) :
  (forall i, Bit b <=l blank_to_star (A i ord0)) ->
  has is_Bit (l :: [seq A m0 ord0 | m0 in s]) ->
  Prod (l :: [seq A m0 ord0 | m0 in s]) = Bit b .
Proof.
move=> Ha.
rewrite /Prod.
set lst := l :: _ => Hb.
case/boolP : (Bit 0 \in lst) => Hin0.
  case/boolP : (Bit 1 \in lst) => Hin1.
    move: (Bit_col bl Ha Hin0).
    by rewrite -(Bit_col bl Ha Hin1).
  move: Hin1; rewrite notin_num_occ_0 => /eqP ->.
  by rewrite -(Bit_col bl Ha Hin0) ltn0 lt0n -notin_num_occ_0 Hin0.
move: (Hin0); rewrite notin_num_occ_0 => /eqP ->.
case/boolP : (Bit 1 \in lst) => Hin1.
  by rewrite -(Bit_col bl Ha Hin1) ltn0 lt0n -notin_num_occ_0 Hin1.
case/hasP : Hb.
case/letterP => //; by [rewrite (negbTE Hin0) | rewrite (negbTE Hin1)].
Qed.

Definition approx (c : 'rV['F_2]_n) (M : 'M[letter]_(m, n)) :=
  [forall i, map_mx Bit c <=m map_mx blank_to_star (row i M)].

Local Notation "c <=* M" := (approx c M) (at level 20).

Lemma approx_mxStar H y : y <=* mxStar H.
Proof.
apply/'forall_forallP => /= m0 ord1.
apply/forallP => /= n0; rewrite !mxE; by case: ifP => [|] _.
Qed.

End mat_approx.

Notation "y <=* A" := (approx y A) (at level 20) : letter_scope.

Section mxSumProd_def.
Variables (m n : nat) (H : 'M['F_2]_(m, n)).
Local Notation "''V'" := (Vnext H).
Local Notation "''F'" := (Fnext H).

Section rowVnext.

Definition rowVnextD1 (r : 'rV[letter]_n) n0 m0 : seq letter :=
  [seq r ``_ i | i in 'V n0 :\ m0].

Lemma sum_rowVnextD1 (c : 'rV['F_2]_n) (r : 'rV[letter]_n) m0 n0 :
  (forall j : 'I_n, j \in 'V m0 :\ n0 -> r ``_ j = Bit (c ``_ j)) ->
  sum_letter (filter is_Bit (rowVnextD1 r m0 n0)) = \sum_(i0 in 'V m0 :\ n0) c ``_ i0.
Proof.
move=> H0.
rewrite /sum_letter big_filter big_map big_mkcond /= big_filter.
apply eq_bigr => n1 Hn1; by rewrite H0.
Qed.

Section rowVnext_codeword.
Variables (c : 'rV['F_2]_n) (Hc : syndrome H c = 0).

Lemma sum_rowVnextD1_nostars m0 n0 (r : 'rV[letter]_n) :
  (forall j, j \in 'V m0 :\ n0 -> r ``_ j = Bit (c ``_ j)) ->
  m0 \in 'F n0 ->
  let s := rowVnextD1 r m0 n0 in
  ~~ has starblank s ->
  sum_letter (filter is_Bit s) = c ``_ n0.
Proof.
move=> H0 m0n0 s starblank.
move/matrixP/(_ ord0 m0) : Hc.
rewrite !mxE (bigD1 n0) //= => Hc'.
set rhs := \sum_(_ < _ | _) _ in Hc'.
have Hrhs : rhs = \sum_(i0 < _ | i0 \in 'V m0 :\ n0) c ``_ i0.
  rewrite /rhs.
  transitivity (\sum_(H0 < n | (H0 != n0) && (m0 \in 'F H0)) H m0 H0 * c^T H0 ord0).
    rewrite (bigID (fun j => m0 \in 'F j)) /=.
    rewrite (_ : \sum_(i0 < n | (i0 != n0) && (m0 \notin 'F i0)) H m0 i0 * c^T i0 ord0 = 0).
      by rewrite addr0.
    rewrite (eq_bigr (fun=> 0)).
      by rewrite big_const /= iter_addr0.
    move=> /= i0 /andP[] i0j.
    rewrite FnextE VnextE tanner_relE -F2_eq0 => /eqP ->; by rewrite mul0r.
  apply eq_big.
    by move=> j0 /=; rewrite in_setD1 FnextE.
  move=> i0 /andP[] H1.
  rewrite FnextE VnextE tanner_relE => /eqP ->; by rewrite mul1r mxE.
rewrite Hrhs (_ : H _ _ = 1) ?mul1r ?mxE in Hc'; last first.
  move: m0n0; by rewrite FnextE VnextE tanner_relE => /eqP.
move/eqP : Hc'.
rewrite addr_eq0 => /eqP ->.
rewrite (@sum_rowVnextD1 c) ?oppr_char2 // => *; by rewrite mxE H0.
Qed.

Lemma sum_rowVnextD1_Bit m0 n0 (m0n0 : m0 \in 'F n0) (r : 'rV[letter]_n) :
  (forall n1, n1 \in 'V m0 :\ n0 -> r ``_ n1 = Bit c ``_ n1) ->
  Sum (rowVnextD1 r m0 n0) = Bit c ``_ n0.
Proof.
move=> H0.
rewrite /Sum.
case: ifPn => [|Hx].
  case/hasP => /= x.
  case/mapP => /= n1.
  by rewrite mem_enum => /H0 -> ->.
rewrite sum_rowVnextD1_nostars // => *; by rewrite mxE H0.
Qed.

End rowVnext_codeword.

End rowVnext.

Section colFnext.

Definition ColFnext (l : letter) (c : 'cV[letter]_m) (s : {set 'I_m}) :=
  l :: [seq c m0 ord0 | m0 in s].

Lemma Prod_colFnext_Bit (b : 'F_2) (c : 'cV[letter]_m) (s : {set 'I_m}) :
  all [pred i | starletter (c i ord0) b] (enum s) ->
  Prod (ColFnext (Bit b) c s) = Bit b.
Proof.
move=> /= H1.
apply/Prod_cons.
rewrite Prod1 //; split => //.
set l := [seq _ | _ in _].
case/boolP : (Bit b \in l) => Hlst.
- left.
  apply Prod_starletter.
    apply/allP => x xFn0m0.
    by move: H1 => /allP/(_ x) /(_ xFn0m0).
  case/mapP : Hlst => m1 H2 H3.
  exists m1; rewrite -?H3 //; by rewrite mem_enum in H2.
- right.
  rewrite (_ : l = nseq (size l) Star); last first.
    apply/all_pred1P/allP => /= x.
    case/mapP => m1 Hm1 Hx.
    move: H1 => /allP/(_ _ Hm1).
    rewrite /= /starletter -Hx.
    case/orP => // xBitb.
    exfalso.
    move: Hlst; rewrite /l => /mapP; apply.
    exists m1 => //.
    by rewrite -Hx (eqP xBitb).
  apply/Prod_starblank_is_Star; by rewrite all_nseq orbT.
Qed.

Local Notation "'`F'" := (Fnext H).

Definition colFnext l (c : 'cV[letter]_m) n0 := ColFnext l c (`F n0).

Definition colFnextD1 l (c : 'cV[letter]_m) n0 m0 : seq letter :=
  ColFnext l c (`F n0 :\ m0).

End colFnext.

Definition mxSum M := \matrix_(i < m, j < n)
  if i \in 'F j then Sum (rowVnextD1 (row i M) i j) else M i j.

Definition mxProd (y : 'rV[letter]_n) M := \matrix_(i < m, j < n)
  if i \in 'F j then Prod (colFnextD1 (y ``_ j) (col j M) j i) else M i j.

Lemma has_starblank_rowVnextD1 (A B : 'M_(m, n)) y m0 n0 :
  mxProd y A <=m mxProd y B ->
  has starblank (rowVnextD1 (row m0 (mxProd y A)) m0 n0) ->
  has starblank (rowVnextD1 (row m0 (mxProd y B)) m0 n0).
Proof.
move=> AB /hasP[l l_row Hl]; move: l_row => /mapP[n1 Hn1 ln1].
apply/hasP => /=; exists l => //.
apply/mapP; exists n1 => //.
move/'forall_forallP/(_ m0 n1) : AB.
move: Hl.
rewrite {}ln1 {l} // mxE [(row _ _) _ _]mxE.
move/starblankP => /orP[/eqP ->|/eqP ->]; by [move/lel_Star | move/lel_Blank].
Qed.

Definition mxSumProd (y : 'rV[letter]_n) := mxSum \o mxProd y.

Lemma mxProd_Bit (y : 'rV[letter]_n) n0 (c : 'F_2) (cy : Bit c <=l y ``_ n0) (A : 'M[letter]_(m, n)) :
  (forall i, Bit c <=l blank_to_star (A i n0)) -> forall m0 b, mxProd y A m0 n0 = Bit b -> b = c.
Proof.
move=> Ha m0 b.
rewrite /mxProd mxE.
case: ifP => m0n0.
  move/Prod_Bit => mem_b.
  have Ha' : forall i : 'I_m, Bit c <=l blank_to_star ((col n0 A) i ord0).
    move=> i; move: Ha => /(_ i); by rewrite !mxE.
  apply: (@Bit_col _ _ _ cy _ ('F n0 :\ m0) Ha').
  move: mem_b; rewrite inE; case/orP => [/eqP <-|mem_b].
    by rewrite eqxx.
  apply/orP; right.
  case/mapP : mem_b => x Hx Hx'.
  apply/mapP; by exists x.
by move=> Hf; move: Ha => /(_ m0); rewrite Hf lel_Bit => /eqP[].
Qed.

Lemma mxProd_monotone y c (c_le_y : map_mx Bit c <=m y) A B : c <=* A -> c <=* B ->
  A <=m B -> mxProd y A <=m mxProd y B.
Proof.
move=> y'A y'B AB.
apply/'forall_forallP => m0 n0.
move Hpa' : (mxProd y B m0 n0) => b.
case/orP : (letter_split b) Hpa' => [/existsP[b' /eqP -> Hpa']|].
  move/'forall_forallP : c_le_y => /(_ ord0 n0); rewrite mxE => c_le_y'.
  have y'B' : forall i : 'I_m, Bit c ``_ n0 <=l blank_to_star (B i n0).
    move=> i.
    by move/'forall_forallP : y'B => /(_ i ord0)/forallP/(_ n0); rewrite !mxE.
  rewrite (mxProd_Bit c_le_y' y'B' Hpa').
  have y'A' : forall i : 'I_m, Bit c ``_ n0 <=l blank_to_star (A i n0).
    move=> i.
    by move/'forall_forallP : y'A => /(_ i ord0)/forallP/(_ n0); rewrite !mxE.
  move Hpa : (mxProd y A m0 n0) => c'.
  case/orP : (letter_split c') Hpa => [/existsP[c'' /eqP -> Hpa]|Hc' Hpa].
    by rewrite (mxProd_Bit c_le_y' y'A' Hpa) lell.
  rewrite /mxProd !mxE in Hpa Hpa'.
  case: ifP => Hi in Hpa Hpa'.
    rewrite (Prod_cons_Bit c_le_y') in Hpa => //.
      by rewrite -Hpa lell.
      move=> i.
      move/'forall_forallP : y'A => /(_ i ord0)/forallP/(_ n0).
      by rewrite !mxE.
    apply/hasP; exists (Bit b') => //.
    move/Prod_Bit: Hpa'.
    rewrite in_cons => /orP [|].
      by rewrite in_cons => ->.
    move/mapP=> [k Hk Hk'].
    move/'forall_forallP/(_ k n0): AB.
    move: Hk'; rewrite mxE => <-; rewrite lel_Bit => /eqP <-.
    rewrite in_cons; apply/orP; right.
    apply/mapP; exists k => //; by rewrite mxE.
  move/'forall_forallP/(_ m0 n0) : AB Hc'.
  by rewrite Hpa Hpa' lel_Bit => /eqP ->.
move=> Hb Hpa'.
move: Hpa' Hb.
rewrite /mxProd !mxE.
case: ifPn => [Hi|Hi <-].
  rewrite /Prod.
  case: ifPn => // H1 <- //; case: ifPn => //; case: ifPn => //; by case: ifPn.
by move/'forall_forallP/(_ m0 n0) : AB.
Qed.

Lemma mxSumProd_monotone A B y (c : 'rV['F_2]_n) (c_le_y : map_mx Bit c <=m y) :
  c <=* A -> c <=* B ->
  A <=m B -> mxSumProd y A <=m mxSumProd y B.
Proof.
move => Ha Ha' Haa'.
apply/'forall_forallP => m0 n0.
rewrite /mxSumProd !mxE.
case: ifP => Hi.
  rewrite /Sum.
  case: ifPn => [Hn1 | _].
    case: ifPn => // /negP Hn2.
    exfalso; apply Hn2; move: Hn1.
    exact/has_starblank_rowVnextD1/(mxProd_monotone c_le_y).
  case: ifPn => // Hn2.
  apply/orP; left.
  apply/eqP; congr Bit.
  rewrite /sum_letter 2!big_filter 2!big_map [in LHS]big_mkcond /=.
  rewrite [in RHS]big_mkcond /= 2!big_filter; apply eq_bigr => i Hi'.
  rewrite 2![(row _ _) _ _]mxE.
  move/forallP/(_ m0)/forallP/(_ i): (mxProd_monotone c_le_y Ha Ha' Haa') => /orP [/eqP -> //|].
  move: Hn2.
  move HB : (mxProd y A m0 i) => a.
  case/letterP : a HB => //= _ Hn2 /eqP.
    by move=> -> /=.
  move=> abs.
  exfalso.
  move/negP : Hn2; apply.
  apply/hasP; exists Star => //.
  apply/mapP; exists i => //.
  by rewrite mem_enum.
  by rewrite mxE.
rewrite Hi.
move/'forall_forallP : Haa'; by apply.
Qed.

Section mxSumProd_codeword.
Variables (c : 'rV['F_2]_n) (Hc : syndrome H c = 0).
Variables (y : 'rV[letter]_n) (c_le_y : map_mx Bit c <=m y).

Lemma approx_mxSumProd M : c <=* M -> c <=* mxSumProd y M.
Proof.
move=> cA.
apply/'forall_forallP => /= m0 k; rewrite {k}(ord1 k).
apply/forallP=> /= j.
rewrite 4!mxE.
case: ifPn => m0Fj; last first.
  rewrite mxE (negbTE m0Fj).
  move/'forall_forallP/(_ m0 ord0) : cA => /forallP/(_ j).
  by rewrite 3!mxE.
rewrite /Sum.
case: ifPn => // nostars.
apply/orP; left; apply/eqP; congr Bit.
rewrite (sum_rowVnextD1_nostars Hc) //= => n1 Hn1.
rewrite mxE.
move Hia : (mxProd y M m0 n1) => b.
case/orP : (letter_split b) Hia => [/existsP[/= b' /eqP -> Hia]|Hb Hia].
  move/'forall_forallP : c_le_y => /(_ ord0 n1); rewrite !mxE => c_le_y'.
  have Ha' : forall i : 'I_m, Bit c ``_ n1 <=l blank_to_star (M i n1).
    move=> i.
    by move/'forall_forallP : cA => /(_ i ord0)/forallP/(_ n1); rewrite !mxE.
  by rewrite (mxProd_Bit c_le_y' Ha' Hia).
move: nostars.
rewrite -all_predC.
move/allP => /=.
move/(_ b).
have X : b \in rowVnextD1 (row m0 (mxProd y M)) m0 j.
  rewrite -Hia.
  apply/mapP => /=.
  exists n1 => //; by rewrite ?(mxE, mem_enum).
move/(_ X).
by rewrite Hb.
Qed.

Lemma mxSumProd_invariant A : c <=* A -> mxSumProd y A <=m A ->
  c <=* mxSumProd y (mxSumProd y A) && mxSumProd y (mxSumProd y A) <=m mxSumProd y A.
Proof.
move=> Hap Halpha.
have Hap' := approx_mxSumProd Hap.
have Hap'' := approx_mxSumProd Hap'.
rewrite Hap'' /=.
by apply (mxSumProd_monotone c_le_y).
Qed.

End mxSumProd_codeword.

End mxSumProd_def.

Definition BEC_IO m n (H : 'M['F_2]_(m, n)) c y :=
  syndrome H c = 0 /\ map_mx Bit c <=m y.

Notation "x 'BEC(' H ')' y" := (BEC_IO H x y) (at level 20, format "x  'BEC('  H  ')'  y") : bec_scope.
Local Open Scope bec_scope.

Definition approx_BEC_input m n (H : 'M['F_2]_(m, n)) (y : 'rV[letter]_n) (M : 'M[letter]_(m, n)) :=
  exists2 c, c BEC( H ) y & c <=* M.

Section SumProdBEC_algo.
Variables (m n : nat) (H : 'M['F_2]_(m, n)).

Local Notation "''F'" := (Fnext H).

Obligation Tactic := idtac.

Program Fixpoint SP_BEC0_rec y M
  (_ : approx_BEC_input H y M) (_ : mxSumProd H y M <=m M)
  { measure (num_stars M) } :
  {M' | mxSumProd H y M' = M' /\ M' <=m M /\ exists k, M' = iter k (mxSumProd H y) M} :=
  let M0 := mxSumProd H y M in
  match Bool.bool_dec (M == M0) true with
  | left H => M
  | right H => @SP_BEC0_rec y M0 _ _ _
  end.
Next Obligation.
move=> y M BEC_y lelM SP_BEC0_rec M0 filtered_var H0 Heq_anonymous.
case: BEC_y => y' [Hy'1 Hy'2] y'a.
move/eqP : {Heq_anonymous} H0.
rewrite /M0 => <-; split => //.
split; [exact: lell_mat | by exists O].
Qed.
Next Obligation.
move=> y M BEC_y lelM SP_BEC0_rec M0 filtered_var H0 Heq_anonymous.
case: BEC_y => y' [Hy'1 Hy'2] y'a.
exists y' => //; by apply approx_mxSumProd.
Qed.
Next Obligation.
move=> y M BEC_y lelM SP_BEC0_rec M0 filtered_var H0 Heq_anonymous.
case: BEC_y => y' [Hy'1 Hy'2] y'a.
by case/andP: (mxSumProd_invariant Hy'1 Hy'2 y'a lelM).
Qed.
Next Obligation.
move=> y M BEC_y lelM SP_BEC0_rec M0 filtered_var H0 Heq_anonymous.
case: BEC_y => y' [Hy'1 Hy'2] y'a.
move/andP: (mxSumProd_invariant Hy'1 Hy'2 y'a lelM) => [Ha' Hle'].
move: (lmat_le_decr lelM) => /orP [Heq|/leP] //.
elim H0.
by rewrite /M0 (eqP Heq) eqxx.
Qed.
Next Obligation.
move=> y M BEC_y lelM SP_BEC0_rec M0 filtered_var H0 Heq_anonymous.
case: (SP_BEC0_rec _ _ _ _) => H' [H'fix [H'app [k Htmp]]].
split => //=.
split; first by apply: (lel_trans_mat H'app).
exists k.+1; by rewrite -addn1 iterD.
Qed.
Next Obligation. exact/Wf.measure_wf/Wf_nat.lt_wf. Defined.

Variable (y : 'rV[letter]_n).
Hypothesis BEC_y : exists c : 'rV['F_2]_n, c BEC( H ) y.

Lemma approx_BEC_input_mxStar : approx_BEC_input H y (mxStar H).
Proof. case: BEC_y => c cy; exists c => //; exact: approx_mxStar. Qed.

Lemma lelmxStar : mxSumProd H y (mxStar H) <=m mxStar H.
Proof.
apply/'forall_forallP => m0 n0; rewrite !mxE.
case: ifP => m0n0 /=; first exact: le_Sum_Star.
by rewrite m0n0 /= lell.
Qed.

Definition SP_BEC0 := projT1 (SP_BEC0_rec approx_BEC_input_mxStar lelmxStar).

Lemma SP_BEC0_is_a_fixpoint : SP_BEC0 = mxSum H (mxProd H y SP_BEC0).
Proof. rewrite /SP_BEC0; by case: SP_BEC0_rec => H' []. Qed.

Lemma SP_BEC0_is_mxlel : SP_BEC0 <=m mxStar H.
Proof. by rewrite /SP_BEC0; case: SP_BEC0_rec => H' [? []]. Qed.

Definition iSP_BEC0 k := iter k (mxSumProd H y) (mxStar H).

Lemma SP_BEC0_is_iter : exists k, SP_BEC0 = iSP_BEC0 k.
Proof. by rewrite /SP_BEC0; case: SP_BEC0_rec => H' [? []]. Qed.

Lemma iSP_BEC0_Blank : forall l m0 n0, m0 \notin 'F n0 ->
  (iSP_BEC0 l) m0 n0 = Blank.
Proof.
elim=> [m0 n0 m0n0 | l IH m0 n0 m0n0]; by rewrite /= !mxE (negbTE m0n0) ?IH.
Qed.

(* nth iteration + Product step *)
Definition PiSP_BEC0 l := mxProd H y (iSP_BEC0 l).

Definition Esti (M : 'M[letter]_(m, n)) : 'rV[letter]_n :=
  \row_i Prod (colFnext H (y ``_ i) (col i M) i).

Definition SP_BEC := Esti SP_BEC0.

End SumProdBEC_algo.

(*
Check bp_erasure.
Extraction "bp_erasure.ml" bp_erasure.
*)
