(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype div prime bigop finset ssralg finalg.
From mathcomp Require Import binomial poly polydiv cyclic perm finfun matrix.
From mathcomp Require Import mxpoly vector mxalgebra zmodp.
Require Import ssr_ext ssralg_ext poly_ext linearcode decoding.
Require Import hamming dft poly_decoding euclid grs.

(** * Reed-Solomon Codes *)

(** OUTLINE
- Section reed_solomon_min_dist_errors.
- Module RS.
  + Section reed_solomon_def.
  + Section reed_solomon_prop.
- Section RS_generator_def.
- Section RS_is_GRS.
- Section reed_solomon_key_equation.
- Section RS_decoding_procedure.
- Section RS_generator_prop0.
- Section RS_generator_prop1.
- Section RS_generator_prop.
- Section RS_decoding_using_euclid0.
- Section RS_decoding_using_euclid.
- Module RS_encoder.
- Section RS_cyclic.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Local Open Scope dft_scope.

Module RS.

Local Notation "'\RSsynp_(' a , y , t )" := (syndromep a y t) (at level 3).

Local Notation "'\RSomega_(' a , e )" := (erreval a a e) (at level 3).

Local Open Scope vec_ext_scope.

Section reed_solomon_min_dist_errors.

Variables (t r n : nat).

Definition redundancy_ub := r < n. (* definition of RS *)
Definition errors_ub := t <= r./2. (* necessary condition to decode t errors *)

End reed_solomon_min_dist_errors.

Section reed_solomon_def.

Variables (F : finFieldType) (a : F) (n r : nat).

Definition PCM : 'M[F]_(r, n) := \matrix_(i, j) (a ^+ i.+1) ^+ j.

Definition code : {vspace _} := kernel PCM.

End reed_solomon_def.

Section reed_solomon_prop.

Variables (F : finFieldType) (a : F) (n' : nat).
Let n := n'.+1.
Variable (r : nat).
Hypothesis rn : redundancy_ub r n.
Hypothesis a_neq0 : a != 0.
Hypothesis a_not_uroot_on : not_uroot_on a n.

Lemma uniq_roots_exp : uniq_roots [seq a ^+ i | i <- iota 1 r].
Proof.
rewrite uniq_rootsE map_inj_in_uniq; first by rewrite iota_uniq.
move=> i j.
rewrite !mem_iota addnC addn1 => H1.
move: H1 => // /andP[_ Hid] /andP [_ Hjd] /eqP aij.
apply/eqP.
by rewrite (val_eqE (Ordinal (leq_trans _ rn)) (Ordinal (leq_trans _ rn))) -(exp_inj a_neq0).
Qed.

Local Notation "v ^`_ i" := (v ^`_(rVexp a n, i)) (at level 9).

Definition codebook :=
  [set c : 'rV_n | [forall i : 'I_r.+1, (0 < i) ==> (c ^`_ (inord i) == 0)] ].

Lemma all_root_codeword c : c \in codebook ->
  all (root (rVpoly c)) [seq a ^+ i | i <- iota 1 r].
Proof.
rewrite inE => /forallP H.
apply/allP => x /mapP[i].
rewrite mem_iota addnC addn1 => H1.
move: H1 => // id ->.
apply/rootP.
case/andP : id => i0 id.
move: (H (Ordinal id)); rewrite i0 implyTb => /eqP.
by rewrite /fdcoor mxE inordK // (leq_trans id).
Qed.

Lemma deg_lb c : c \in codebook -> (c == 0) || (r.+1 <= size (rVpoly c)).
Proof.
move=> H.
case/boolP : (c == 0) => //=.
rewrite -rVpoly0 => c0.
move: (uniq_roots_exp); rewrite uniq_rootsE.
move/(max_poly_roots c0 (all_root_codeword H)).
by rewrite size_map size_iota -ltnS.
Qed.

Lemma O_in_codebook : 0 \in codebook.
Proof.
rewrite inE; apply/forallP => i; apply/implyP => i0; by rewrite fdcoor0.
Qed.

Lemma oppr_closed : oppr_closed codebook.
Proof.
move=> /= c; rewrite inE => /forallP H.
rewrite inE; apply/forallP => i; apply/implyP => i0.
rewrite fdcoorN eqr_oppLR oppr0; move: (H i); by rewrite i0 implyTb.
Qed.

Lemma addr_closed : addr_closed codebook.
Proof.
split; [exact: O_in_codebook | move=> x y].
have [xy|xy] := boolP (x + y == 0); first by rewrite /= (eqP xy) O_in_codebook.
rewrite inE => /forallP H1; rewrite inE => /forallP H2.
rewrite inE; apply/forallP => i; apply/implyP => i0.
rewrite fdcoorD.
move: (H1 i) (H2 i); by rewrite i0 2!implyTb => /eqP-> /eqP->; rewrite addr0.
Qed.

Lemma scaler_closed : GRing.scaler_closed codebook.
Proof.
move=> k x; rewrite !inE => /forallP xC.
apply/forallP => /= i; apply/implyP => i0.
rewrite tdcoorZ; move: (xC i); rewrite i0 implyTb => /eqP ->; by rewrite mulr0.
Qed.

Lemma submod_closed : submod_closed codebook.
Proof.
split=> [|k x y xC yCby]; first exact: O_in_codebook.
by rewrite (proj2 addr_closed) // scaler_closed.
Qed.

Lemma syndrome_syndromep y :
  syndrome (PCM a n r) y = poly_rV \RSsynp_(rVexp a n, y, r).
Proof.
apply/rowP => i; rewrite !mxE /syndromep poly_def coef_sum.
evar (tmp : 'I_r -> F); transitivity (\sum_j (tmp j)); last first.
  apply eq_bigr => /= j _.
  apply/esym; rewrite /fdcoor coefZ horner_poly big_distrl /= /tmp; reflexivity.
rewrite {}/tmp (exchange_big_dep xpredT) //=; apply eq_bigr => j _; rewrite !mxE.
have @i' :  'I_r.
  by apply (@Ordinal _ i); rewrite (leq_trans (ltn_ord i)).
rewrite (bigD1 i') //= coefXn insubT //= => Hj.
rewrite eqxx mulr1 (_ : Ordinal Hj = j); last by apply val_inj.
rewrite mxE inordK; last by rewrite ltnS (leq_trans (ltn_ord i)).
rewrite mulrC; apply/eqP.
  rewrite addrC -subr_eq subrr; apply/eqP/esym.
rewrite big1 // => k ki'; rewrite coefXn (_ : (_ == _) = false) ?mulr0 //.
apply: contraNF ki'; by rewrite -val_eqE /= eq_sym.
Qed.

Lemma codebook_syndrome (c : 'rV_n) : (c \in codebook) = (syndrome (PCM a n r) c == 0).
Proof.
rewrite syndrome_syndromep inE; apply/idP/idP.
- move/forallP => H; apply/eqP/rowP => i; rewrite !mxE.
  rewrite /syndromep /poly_decoding.syndromep poly_def coef_sum.
  rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addr0 // => j _.
  rewrite coefZ; apply/eqP; rewrite mulf_eq0.
  have @j' : 'I_r.+1.
    by apply (@Ordinal _ j.+1); move: (ltn_ord j); rewrite -ltnS.
  move: (H j'); by rewrite lt0n /= => ->.
- move/eqP/rowP => H.
  apply/forallP => /= i; apply/implyP => i0.
  have @i' : 'I_r.
    apply (@Ordinal _ i.-1).
    by rewrite prednK // -ltnS.
  move: (H i'); rewrite !mxE.
  rewrite /syndromep /poly_decoding.syndromep.
  rewrite coef_poly ltn_ord => /eqP /=.
  by rewrite prednK.
Qed.

Lemma lcode0_codebook : [set cw in (code a n r)] = codebook.
Proof. by apply/setP => /= x; rewrite inE mem_kernel_syndrome0 codebook_syndrome. Qed.

Lemma RS_syndromep_codeword' t (tr : t < r.+1) (c : 'rV[F]_n) :
  c \in codebook -> \RSsynp_(rVexp a n, c, t) = 0.
Proof.
rewrite inE // => /forallP H.
rewrite /syndromep /poly_decoding.syndromep poly_def (eq_bigr \0) ?big1 //.
move=> i _.
have [:tmp] @j : 'I_r.+1.
  apply/(Sub i.+1)/(leq_ltn_trans (ltn_ord _)).
  abstract: tmp.
  exact tr.
by move: (H j) => /= /eqP ->; rewrite scale0r.
Qed.

Lemma RS_syndromep_codeword (c : 'rV[F]_n) :
  (\RSsynp_(rVexp a n, c, r) == 0) = (c \in codebook).
Proof.
apply/idP/idP => [/eqP | ]; last first.
  by move/(@RS_syndromep_codeword' r) => /(_ (ltnSn _)) ->.
rewrite codebook_syndrome syndrome_syndromep => /eqP ?.
by rewrite poly_rV_0.
Qed.

End reed_solomon_prop.
End RS.

Notation "'\RSsynp_(' a , e , t )" := (syndromep a e t) (at level 3).
Notation "'\RSomega_(' a , e )" := (erreval a a e) (at level 3).

Local Open Scope vec_ext_scope.

Require Import cyclic_code.

Section RS_generator_def.

Variables (F : finFieldType) (a : F) (r : nat).

Definition rs_gen := \prod_(1 <= i < r.+1) ('X - (a ^+ i)%:P).

End RS_generator_def.

Notation "'\gen_(' a , r )" := (rs_gen a r) (at level 3).

(** Reed-Solomon codes are an instance of GRS codes. Take a and b to
be \alpha^j to get conventional RS codes. *)
Section RS_is_GRS.

Variables (F : finFieldType) (n' : nat).
Let n := n'.+1.
Variables (a : F) (r : nat).

Let b : 'rV[F]_n := rVexp a n.

Lemma RS_GRS_PCM : GRS.PCM b b r = RS.PCM a n r.
Proof.
apply/matrixP => i j.
rewrite !mxE (bigD1 j) //= !mxE eqxx mulr1n -exprSr -exprM mulnC exprM.
rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addr0 ?addr0 // => k kj.
by rewrite !mxE (negbTE kj) mulr0n mulr0.
Qed.

Lemma fdcoor_GRS_syndrome_coor y l : l < n' -> l < r ->
  fdcoor b y (inord l.+1) = GRS.syndrome_coord b b l y.
Proof.
move=> ln id1.
rewrite /fdcoor /GRS.syndrome_coord horner_poly; apply/eq_bigr => /= j _.
rewrite insubT // => jn.
rewrite 2!mxE -mulrA; congr (y ord0 _ * _); first by apply val_inj.
by rewrite -exprS -exprM mulnC exprM inordK.
Qed.

Lemma RS_GRS_syndromep y : RS.redundancy_ub r n ->
  \RSsynp_(b, y, r) = (GRS.syndromep b b r) y.
Proof.
move=> dn; rewrite /GRS.syndromep /poly_decoding.syndromep.
apply/polyP => i.
rewrite 2!coef_poly; case: ifP => // id1.
by rewrite fdcoor_GRS_syndrome_coor // (leq_trans id1).
Qed.

End RS_is_GRS.

Section reed_solomon_key_equation.

Variables (F : finFieldType) (a : F) (n' : nat).
Let n := n'.+1.
Variable t : nat.

Hypothesis tn : t < n.

Definition RS_mod (y : 'rV[F]_n) t := - \sum_(i in supp y) y ``_ i *:
  (\prod_(j in supp y :\ i) (1 - a ^+ j *: 'X) * - (a ^+ (t.+1 * i))%:P).

Lemma RS_mod_is_GRS_mod y : RS_mod y t = - GRS_mod y (rVexp a n) (rVexp a n) t.
Proof.
rewrite /RS_mod /GRS_mod; congr (- _); apply/eq_bigr => /= i iy.
rewrite !mulrN scalerN; congr (- _).
rewrite -!scalerAl; congr (_ *: _ ).
rewrite -mulrA; congr (_ * _).
  apply eq_big.
    by move=> j; rewrite in_setD1 andbC.
  move=> j; by rewrite mxE.
by rewrite mxE -polyC_mul -exprSr -exprM mulnC.
Qed.

Lemma RS_key_equation y :
  \sigma_(rVexp a n, y) * \RSsynp_(rVexp a n, y, t) =
  \RSomega_(rVexp a n, y) + - RS_mod y t * 'X^t.
Proof.
move: (@RS_GRS_syndromep F n' a t y tn) => H0.
move: (GRS_key_equation y (rVexp a n) (rVexp a n) t).
rewrite -{}H0 => ->; by rewrite RS_mod_is_GRS_mod opprK.
Qed.

End reed_solomon_key_equation.

Section RS_decoding_procedure.

Variables (F : finFieldType) (a : F) (n' : nat).
Let n := n'.+1.
Variable r : nat.
Let t := r./2.
Hypothesis rn : RS.redundancy_ub r n.

Let tr : t <= r.
Proof. by rewrite /t -divn2 leq_div. Qed.

Local Notation "'`v'" := (Euclid.v).
Local Notation "'`r'" := (Euclid.r).

Definition RS_err y : {poly F} :=
  let r0 : {poly F} := 'X^r in
  let r1 := \RSsynp_(rVexp a n, y, r) in
  let vstop := `v r0 r1 (stop (odd r + t) r0 r1) in
  let rstop := `r r0 r1 (stop (odd r + t) r0 r1) in
  let s := vstop.[0]^-1 *: vstop in
  let w := vstop.[0]^-1 *: rstop in
  \poly_(i < n) (if s.[a^- i] == 0 then - w.[a ^- i] / s^`().[a ^- i] else 0).

Definition RS_repair : repairT F F n := [ffun y =>
  if \RSsynp_(rVexp a n, y, r) == 0 then
    Some y
  else
    let ret := y - poly_rV (RS_err y) in
    if \RSsynp_(rVexp a n, ret, r) == 0 then Some ret else None].

End RS_decoding_procedure.

(* TODO: move? *)
Lemma leqnmul2 k : k <= k.*2.
Proof. by rewrite -addnn leq_addr. Qed.

Section RS_generator_prop0.

Variables (F : finFieldType) (a : F) (n' : nat) (r : nat).
Let d := r.+1.
Let n := n'.+1.

Lemma size_rs_gen : size \gen_(a, r) = d.
Proof. by rewrite size_prod_XsubC size_iota subn1 prednK. Qed.

Lemma wH_rs_gen : wH (poly_rV \gen_(a, r) : 'rV[F]_n) <= r.+1.
Proof.
by rewrite (leq_trans (wH_poly_rV _ _)) // size_rs_gen.
Qed.

Lemma gen_neq0 : \gen_(a, r) != 0.
Proof. by rewrite -size_poly_gt0 size_rs_gen. Qed.

Lemma fdcoor_codeword (n0 : 'I_d) (Hn0 : 0 < n0 < n) (m : {poly F}) :
  size (m * \gen_(a, r)) <= n ->
  (poly_rV (m * \gen_(a, r)) : 'rV_n)^`_(rVexp a n, inord n0) == 0.
Proof.
move=> mn.
rewrite /fdcoor poly_rV_K // !hornerE.
rewrite mxE inordK; last first.
  by case/andP : Hn0.
case Hm : (m.[a ^+ n0] == 0); first by rewrite (eqP Hm) mul0r.
apply negbT in Hm.
rewrite mulrI_eq0; last by move : Hm => /lregP.
rewrite -rootE.
pose rs := [seq (a ^+ i) | i <- iota 1 d.-1].
rewrite /rs_gen.
have -> : \prod_(1 <= n1 < d) ('X - (a ^+ n1)%:P) = \prod_(a <- rs) ('X - a%:P)
  by rewrite /rs big_map /index_iota subn1.
rewrite root_prod_XsubC /rs.
apply/mapP; exists (val n0) => //.
rewrite mem_iota.
case/andP : Hn0 => -> _.
by rewrite addnC addn1 prednK // andTb; by apply ltn_ord.
Qed.

Hypothesis rn : RS.redundancy_ub r n.

Lemma mem_rs_gen_RS : poly_rV \gen_(a, r) \in RS.code a n r.
Proof.
rewrite mem_kernel_syndrome0 -RS.codebook_syndrome // inE.
apply/forallP => /= i; apply/implyP => i0.
rewrite -(mul1r \gen_(a, r)) fdcoor_codeword //.
  by rewrite i0 /= (leq_trans (ltn_ord i)) //.
rewrite mul1r size_rs_gen; exact: rn.
Qed.

Lemma RS_not_trivial : not_trivial (RS.code a n r).
Proof.
rewrite /not_trivial.
exists (poly_rV (rs_gen a r)); apply/andP; split.
- by rewrite mem_rs_gen_RS.
- apply/negP => /poly_rV_0_inv.
  rewrite size_rs_gen => /(_ rn).
  apply/negP; by rewrite gen_neq0.
Qed.

Lemma RS_message_size (p : 'rV_n) x : rVpoly p = x * \gen_(a, r) ->
  (size x).-1 <= n - d.
Proof.
move=> Hx.
case/boolP : (x == 0) => [/eqP ->|x0]; first by rewrite size_poly0.
have : size (rVpoly p) <= n by rewrite size_poly.
rewrite Hx size_mul // ?gen_neq0 // => H.
rewrite -(leq_add2r d) (subnK rn) (leq_trans _ H) //.
rewrite -subn1 addnC addnBA; last by rewrite lt0n size_poly_eq0.
by rewrite -subn1 addnC leq_sub2r // leq_add2l size_rs_gen.
Qed.

End RS_generator_prop0.

Section RS_generator_prop1.

Variables q m' : nat.
Hypothesis primeq : prime q.
Let F := GF m' primeq.
Variables (a : F) (n' : nat) (r : nat).
Let d := r.+1.
Let n := n'.+1.

Hypothesis rn : RS.redundancy_ub r n.
Hypothesis qn : coprime q n.

Lemma RS_Hchar : ([char F]^').-nat n.
Proof.
by rewrite -natf_neq0 -(@dvdn_charf _ q) ?char_GFqm // -prime_coprime.
Qed.

Lemma RS_min_dist1 c : n.-primitive_root a -> c != 0 ->
  c \in RS.code a n r -> r.+1 <= wH c.
Proof.
move=> an c0 Hc.
have a_neq0 := primitive_uroot_neq0 an.
rewrite -(wH_phase_shift a_neq0 _ r).
apply: (@BCH_argument_lemma _ _ (@GRing.idfun_rmorphism F) _ RS_Hchar _ an
  (phase_shift a c r.+1) _ rn).
  by rewrite -wH_eq0 wH_phase_shift // wH_eq0.
rewrite (_ : \row_i0 (GRing.idfun_rmorphism F) ((phase_shift a c r.+1) ``_ i0) =
  phase_shift a c r.+1); last by apply/rowP => i; rewrite !mxE.
apply (dft_shifting a_neq0 (prim_expr_order an) rn) => i /andP[ir1 ir2].
have {Hc} : c \in RS.codebook a n' r by rewrite -(RS.lcode0_codebook a rn) inE.
rewrite inE => /forallP/(_ (Ordinal ir2)) /=.
by rewrite ir1 implyTb !mxE => /eqP.
Qed.

Lemma RS_min_dist : n.-primitive_root a ->
  min_dist (RS_not_trivial a rn) = r.+1.
Proof.
move=> na.
apply min_distP; split; first by move=> *; apply RS_min_dist1.
exists (poly_rV \gen_(a, r)); split; first by rewrite mem_rs_gen_RS.
apply/andP; rewrite wH_rs_gen andbT.
apply: contra (gen_neq0 a r).
move/poly_rV_0_inv; apply; by rewrite size_rs_gen.
Qed.

Lemma PCM_lin1_mx :
  RS.PCM a n r = (lin1_mx (linfun (lin_syndrome (RS.PCM a n r))))^T.
Proof.
apply/matrixP => i j.
rewrite !(mxE,lfunE) (bigD1 j) //= !mxE !eqxx mulr1 (eq_bigr (fun=> 0)).
- by rewrite big_const iter_addr0 addr0.
- move=> k kj; by rewrite !mxE eqxx (negbTE kj) mulr0.
Qed.

Lemma dim_RS_code (a0 : a != 0) (auroot : not_uroot_on a n) :
  \dim (RS.code a n r) = (n - r)%N.
Proof.
apply dim_kernel; last by rewrite ltnW.
rewrite -RS_GRS_PCM rank_GRS_PCM //.
- by apply (@rVexp_inj _ _ _ a0 auroot).
- by rewrite ltnW.
- move=> i; by rewrite mxE expf_neq0.
Qed.

Lemma RS_MDS : n.-primitive_root a ->
  maximum_distance_separable (RS_not_trivial a rn).
Proof.
move=> an.
rewrite /maximum_distance_separable RS_min_dist // addn1 dim_RS_code //.
- by rewrite subKn // ltnW.
- exact: primitive_uroot_neq0 an.
- by apply prim_root_not_uroot_on.
Qed.

End RS_generator_prop1.

Section RS_generator_prop.

Variable (F : finFieldType) (a : F).
Variables (r : nat) (n' : nat).
Let n := n'.+1.
Let d := r.+1.
Hypothesis rn : RS.redundancy_ub r n.
Hypothesis a_neq0 : a != 0.
Hypothesis a_not_uroot_on : not_uroot_on a n.

Lemma rs_genP (c : 'rV[F]_n) : c \in RS.codebook a n' r
  <-> exists m : {poly F}, (size m).-1 <= n - d /\ rVpoly c = m * \gen_(a, r).
Proof.
split => [c_in_RS| [m [H0 H1]] ]; last first.
  rewrite /RS.codebook inE.
  apply/forallP => n0; apply/implyP => Hn0.
  rewrite -(rVpolyK c) H1 fdcoor_codeword //.
    rewrite Hn0 /= (leq_trans (ltn_ord n0)) //.
    by rewrite -H1 size_poly.
case/boolP : (c == 0) => [/eqP ->|Hc].
  exists 0; by rewrite size_poly0 -subn1 sub0n leq0n mul0r linear0.
have Hc' : 0 < size (rVpoly c) by rewrite size_poly_gt0 rVpoly0.
have H1 : forall i, 1 <= i < d -> (rVpoly c).[a ^+ i] = 0.
  move=> i /andP[i0 id].
  move: c_in_RS; rewrite inE => /forallP/(_ (Ordinal id)); rewrite i0 implyTb /fdcoor // => /eqP.
  by rewrite mxE /= inordK // (leq_trans id).
have H2 : forall n0, 1 <= n0 < d -> 'X - (a ^+ n0)%:P %| rVpoly c.
  move=> n0 /H1 /eqP /factor_theorem [x ->].
  by rewrite dvdp_mull.
pose rs := [seq (a ^+ i) | i <- iota 1 d.-1].
have K1 : all (root (rVpoly c)) rs by apply RS.all_root_codeword.
have K2 : uniq_roots rs by apply: (@RS.uniq_roots_exp _ _ n').
case: (uniq_roots_prod_XsubC K1 K2) => m.
have -> : \prod_(z <- rs) ('X - z%:P) = \gen_(a, r).
  by rewrite /rs_gen /rs big_map /index_iota subn1.
have Hg := size_rs_gen a r.
have Hg' : 0 < size \gen_(a, r) by rewrite Hg.
have Hg'' := gen_neq0 a r.
move => Hm.
have Hm' : m != 0.
  move : Hm => /eqP.
  apply contraLR => /negPn/eqP ->; by rewrite mul0r rVpoly0.
have Hm'' : 0 < size m by rewrite size_poly_gt0.
exists m; split; [| by rewrite Hm].
have : size (rVpoly c) <= n by apply size_poly.
rewrite Hm.
move : (size_mul_leq m \gen_(a, d)) => Hmg.
rewrite size_mul // -!subn1 addnC -addnBA // addnC.
move /(leq_sub2r d).
rewrite Hg.
by move : (addnK d%N (size m - 1)%N) => ->.
Qed.

Local Open Scope cyclic_code_scope.

Lemma rs_gen_is_pgen : \gen_(a, r) \is 'pgen[RS.codebook a n' r].
Proof.
apply/forallP => cw; apply/eqP; apply/idP/idP.
  case/rs_genP => x [sz_x ->]; by rewrite dvdp_mulIr.
rewrite dvdp_eq => /eqP H; apply/rs_genP.
exists (rVpoly cw %/ \gen_(a, r)); split => //.
rewrite size_divp ?gen_neq0 // size_rs_gen.
by rewrite -subnS /= leq_sub2r // size_poly.
Qed.

End RS_generator_prop.

Section RS_decoding_using_euclid0.

Variables (F : finFieldType) (a : F) (n' : nat).
Let n := n'.+1.
Variable r : nat.
Let t := r./2.

Hypothesis rn : RS.redundancy_ub r n.

Hypothesis a_neq0 : a != 0.
Hypothesis a_not_uroot_on : not_uroot_on a n.

Let tn : t.*2 < n.
Proof.
by rewrite /t (leq_trans _ rn) // ltnS -{2}(odd_double_half r) leq_addl.
Qed.

(* TODO: clean *)
Lemma td : RS.errors_ub t r.+1.
Proof.
by rewrite /RS.errors_ub /t half_leq.
Qed.

Lemma RS_err_is_correct l (e y : 'rV_n) :
  distinct_non_zero (rVexp a n) ->
  let r0 := 'X^r : {poly F} in
  let r1 := \RSsynp_(rVexp a n, y, r) in
  let vj := Euclid.v r0 r1 (stop (odd r + t) r0 r1) in
  let rj := Euclid.r r0 r1 (stop (odd r + t) r0 r1) in
  l <> 0 ->
  vj = l *: \sigma_(rVexp a n, e) ->
  rj = l *: \RSomega_(rVexp a n, e) ->
  e = poly_rV (RS_err a r y).
Proof.
move=> H1 r0 r1 vj rj /eqP l0 Hvj Hrj; apply/rowP => i.
rewrite mxE coef_poly ltn_ord -/r0 -/r1 -/vj -/rj; case: ifPn => H.
  apply: (@mulIf _ ((rVexp a n) ``_ i)).
    by rewrite mxE expf_eq0 negb_and a_neq0 orbT.
  rewrite (erreval_vecE H1 (rVexp a n)) //; last first.
    rewrite -(errloc_zero _ _ H1) mxE.
    move: H; rewrite Hvj !hornerZ !mulrA mulf_eq0 => /orP[|//].
    rewrite mulf_eq0 (negbTE l0) orbF invr_eq0 mulf_eq0 (negbTE l0) orFb.
    by rewrite horner_errloc_0 oner_eq0.
  rewrite 2![in RHS]mulNr -[in RHS]mulrN [in RHS]mulrC -mulrA; congr (_ * _).
  rewrite Hvj Hrj -/(\RSomega_(rVexp a n, e)) mxE !scalerA !(hornerZ,derivZ).
  set x := (_^-1 * _).
  rewrite -mulf_div divrr ?mul1r // unitfE mulf_neq0 //.
  by rewrite invr_neq0 // mulf_neq0 // horner_errloc_0 oner_neq0.
apply/eqP; apply: contraNT H.
rewrite -insupp -(errloc_zero _ _ H1) mxE Hvj !hornerZ => /eqP ->.
by rewrite !mulr0.
Qed.

End RS_decoding_using_euclid0.

Section RS_decoding_using_euclid.

Variables q m' : nat.
Hypothesis primeq : prime q.
Let F := GF m' primeq.
Variables (a : F) (n' : nat) (r : nat).
Let d := r.+1.
Let n := n'.+1.

Hypothesis rn : RS.redundancy_ub r n.
Hypothesis qn : coprime q n.

Let t := r./2.

Local Open Scope ecc_scope.

Lemma RS_repair_is_correct : n.-primitive_root a ->
  t.-BDD (RS.code a n r, RS_repair a n' r).
Proof.
move=> an; rewrite /BD_decoding /=.
move=> c e.
set y := c + e.
set r0 : {poly F} := 'X^r.
set r1 := \RSsynp_(rVexp a n, y, r).
set vj := Euclid.v r0 r1 (stop (odd r + t) r0 r1).
set rj := Euclid.r r0 r1 (stop (odd r + t) r0 r1).
move=> Hc et.
set r_ : {poly F} := \RSomega_(rVexp a n, e).
rewrite /= /RS_repair.
have same_syndrome : \RSsynp_(rVexp a n, y, r) = \RSsynp_(rVexp a n, e, r).
  rewrite syndromepD.
  move: Hc => /=.
  rewrite mem_kernel_syndrome0 -RS.codebook_syndrome // -RS.RS_syndromep_codeword // => /eqP ->; by rewrite add0r.
rewrite ffunE.
case: ifPn => syndrome0.
  suff e0 : e = 0 by rewrite /y e0 addr0.
  suff yc : y = c.
    move/eqP : yc; by rewrite -subr_eq0 /y addrAC subrr add0r => /eqP.
  apply/eqP/negPn/negP => abs.
  suff : dH y c < min_dist (RS_not_trivial a rn).
    apply/negP; rewrite -leqNgt min_dist_prop //.
    move: syndrome0; by rewrite RS.RS_syndromep_codeword // -RS.lcode0_codebook // inE.
  rewrite (RS_min_dist rn _ an) // dH_sym dH_wH (@leq_ltn_trans t) //.
  move: (td r).
  rewrite /RS.errors_ub ltnS => /leq_trans; apply.
  by rewrite -{2}(half_bit_double r true) add1n half_leq // ltnS -addnn leq_addr.
have H1 : distinct_non_zero (rVexp a n).
  apply distinct_non_zero_rVexp.
  by apply (primitive_uroot_neq0 an).
  by move/prim_root_not_uroot_on: an.
have H2 := rVexp_neq0 _ (primitive_uroot_neq0 an).
have r1_neq0 : \RSsynp_(rVexp a n, e, r) != 0.
  apply: contra syndrome0.
  rewrite syndromepD => /eqP ->.
  by rewrite addr0 RS.RS_syndromep_codeword // -RS.lcode0_codebook // inE.
have K1 : size r1 <= size ('X^r : {poly F}).
  by rewrite /r1 size_polyXn (leq_trans (size_syndromep _ _ _)).
have K2 : \RSsynp_(rVexp a n, y, r) != 0 by rewrite same_syndrome.
have K3 : \sigma_(rVexp a n, e) * r1 = r_ + - RS_mod a e r * 'X^r.
  by rewrite /r1 same_syndrome RS_key_equation.
have K4 : size \sigma_(rVexp a n, e) <= t.+1.
  rewrite (leq_trans (size_errloc _ _)) => //; by rewrite -wH_card_supp.
have K5 : size r_ <= odd r + t.
  rewrite wH_card_supp in et.
  by rewrite (leq_trans (size_erreval (rVexp a n) (Errvec et) _)) // leq_addl.
have K6 : (t.+1 + (odd r + t))%N = size ('X^r : {poly F}).
  rewrite size_polyXn addnCA addSn addnn addnS; congr S.
  by rewrite -[RHS](odd_double_half r).
move: (@solve_key_equation_coprimep F 'X^r r1 K1 \sigma_(rVexp a n, e) r_ _ (errloc_neq0 (rVexp a n) (supp e)) K2 t.+1 _ K3 K4 K5 K6 (coprime_errloc_erreval H1 (@H2 n) _)).
case=> l [l0 [Hvj Hrj]].
by rewrite -(@RS_err_is_correct _ _ _ _ (primitive_uroot_neq0 an) l e) // /y addrK ifT // RS.RS_syndromep_codeword // -RS.lcode0_codebook // inE.
Qed.

End RS_decoding_using_euclid.

Require Import channel_code.

Module RS_encoder.

Section RS_encoder_sect.

Variable (F : finFieldType) (a : F).
Variables (r : nat) (n' : nat).
Let n := n'.+1.
Let d := r.+1.
Hypothesis rn : RS.redundancy_ub r n.

Definition encoder : encT F [finType of 'rV[F]_(n - d).+1] n :=
  let g := \gen_(a, r) in
 [ffun m => let mxd := rVpoly m * 'X^d.-1 in poly_rV (mxd - mxd %% g)].

(* TODO(rei) *)
Lemma tmp : (d.-1 + (n - d).+1 = n)%nat.
Proof. rewrite -addSnnS prednK // subnKC //; exact: dn. Qed.

Definition RS_discard' (x : 'rV[F]_n) : 'rV[F]_(n - d).+1 :=
  rsubmx (castmx (erefl, esym tmp) x).

Definition RS_discard (x : 'rV[F]_n) : 'rV[F]_(n - d).+1 :=
  poly_rV ((rVpoly x) %/ 'X^d.-1).

Definition decoder : decT F [finType of 'rV[F]_(n - d).+1] n :=
  [ffun y => omap RS_discard (RS_repair a _ r y)].

Definition RS_code := mkCode encoder decoder.

(* NB: first part of lemma 10.60 *)
Lemma RS_enc_injective : injective (enc RS_code).
Proof.
move=> x1 x2 /=.
rewrite /encoder 2!ffunE => x1x2.
suff H : rVpoly x1 * 'X^d = rVpoly x2 * 'X^d.
  rewrite -(rVpolyK x1) -(rVpolyK x2).
  have : (rVpoly x1 * 'X^d) %/ 'X^d = (rVpoly x2 * 'X^d) %/ 'X^d by rewrite H.
  rewrite mulpK; last by rewrite -size_poly_gt0 size_polyXn.
  rewrite mulpK; last by rewrite -size_poly_gt0 size_polyXn.
  by move=> ->.
apply/eqP.
rewrite -subr_eq0 -mulrBl.
suff : ((rVpoly x1 - rVpoly x2) == 0) &&
  ((rVpoly x2 * 'X^d.-1) %% \gen_(a, r) -
   (rVpoly x1 * 'X^d.-1) %% \gen_(a, r) == 0).
  case/andP => /eqP ->; by rewrite mul0r.
have H1 : size ((rVpoly x2 * 'X^d.-1) %% \gen_(a, r)) < d.
  by rewrite {3}/d -(size_rs_gen a r) ltn_modp gen_neq0.
have H2 : size ((rVpoly x1 * 'X^d.-1) %% \gen_(a, r)) < d.
  by rewrite {3}/d -(size_rs_gen a r) ltn_modp gen_neq0.
rewrite -(@rreg_div0 _ _ _ 'X^d.-1).
- rewrite mulrBl -(opprB (_ %% _)).
  rewrite (_ : forall a b c d, a - b - (c - d) = (a - c) + (d - b)); last first.
    move=> *.
    rewrite -2!addrA; congr (_ + _).
    rewrite addrA addrC opprD; congr (_ - _).
    by rewrite opprK.
  rewrite addr_eq0 opprB -subr_eq0.
  move/eqP : x1x2.
  rewrite -[in X in X -> _]subr_eq0 -linearB /= => /poly_rV_0_inv; apply.
  rewrite (leq_trans (size_add _ _)) // size_opp geq_max.
  have H : forall x : 'rV[F]_(n - d).+1, size (rVpoly x * 'X^d.-1) <= n.
    move=> x.
    apply (leq_trans (size_mul_leq _ _)).
    rewrite size_polyXn addnS /=.
    rewrite (@leq_trans ((n - d).+1 + d.-1)) //.
      by rewrite leq_add2r size_poly.
    rewrite addSnnS prednK // subnK //; exact dn.
  apply/andP; split; rewrite (leq_trans (size_add _ _)) // geq_max size_opp H /=.
    by rewrite (leq_trans _ rn) // ltnW.
    by rewrite (leq_trans _ rn) // ltnW.
- rewrite lead_coefXn; exact: GRing.rreg1.
- rewrite size_polyXn ltnS (leq_trans (size_add _ _)) //.
  rewrite geq_max size_opp /=; apply/andP; split; by rewrite -ltnS.
Qed.

Hypothesis a_neq0 : a != 0.
Hypothesis a_not_uroot_on : not_uroot_on a n.

(* NB: corresponds to lemma 10.59? *)
Lemma RS_enc_img :
  (enc RS_code) @: [finType of 'rV[F]_(n - d).+1] \subset RS.code a n r.
Proof.
apply/subsetP => /= c /imsetP[/= m _] ->{c}.
rewrite /encoder ffunE.
have Htmp : size (rVpoly m * 'X^d.-1) <= n.
  eapply leq_trans; first by apply size_mul_leq.
  rewrite size_polyXn addnS /=.
  suff : size (rVpoly m) <= (n - d).+1.
    rewrite -(leq_add2r d.-1) => /leq_trans -> //.
    by rewrite addSnnS prednK // (subnK rn).
  by apply size_poly.
suff : poly_rV (rVpoly m * 'X^d.-1 - (rVpoly m * 'X^d.-1) %% \gen_( a, r))
    \in [set cw in RS.code a n r].
  by rewrite !inE.
rewrite (@RS.lcode0_codebook _ a n' r); last by exact rn.
apply/(rs_genP rn a_neq0 a_not_uroot_on).
exists ((rVpoly m * 'X^d.-1) %/ \gen_(a, r)).
split.
  rewrite size_divp; last apply: gen_neq0.
  rewrite -subnS prednK; last by rewrite size_poly_gt0; exact: gen_neq0.
  apply (@leq_trans (n - size \gen_(a, r))).
  apply leq_sub => //.
  apply leq_sub2l => //.
  rewrite size_rs_gen //; exact: d_pos.
rewrite {1}(divp_eq (rVpoly m * 'X^d.-1) \gen_(a, r)) addrK poly_rV_K //.
by eapply leq_trans; first by apply leq_trunc_divp.
Qed.

Lemma RS_repair_output_is_in_the_code (x y : 'rV_n) (an1 : a ^+ n = 1) :
  RS_repair a _ r x = Some y -> y \in RS.code a n r.
Proof.
rewrite /RS_repair ffunE.
case: ifPn => [|_].
  rewrite RS.RS_syndromep_codeword // -RS.lcode0_codebook // inE.
  by move=> ? [<-].
case: ifPn => [|//].
rewrite RS.RS_syndromep_codeword // -RS.lcode0_codebook // inE => ?.
by case=> <-.
Qed.

Lemma RS_repair_img (an1 : a ^+ n = 1) (Hchar : ([char F]^').-nat n'.+1) :
  oimg (RS_repair a _ r) \subset RS.code a n r.
Proof.
apply/subsetP => /= y.
rewrite inE => /existsP[/= x /eqP].
by apply RS_repair_output_is_in_the_code.
Qed.

Definition low (c : 'rV[F]_n) : 'rV[F]_d.-1 := poly_rV (rVpoly c %% 'X^d.-1).
Definition high (c : 'rV[F]_n) : 'rV[F]_(n - d).+1 := poly_rV (rVpoly c %/ 'X^d.-1).

Lemma decomp_codeword (c : 'rV[F]_n) : rVpoly c = rVpoly (low c) + rVpoly (high c) * 'X^d.-1.
Proof.
rewrite poly_rV_K; last first.
 move: (@ltn_modp _ (rVpoly c) 'X^d.-1).
 rewrite size_polyXn prednK //.
 by rewrite -size_poly_eq0 size_polyXn prednK.
rewrite poly_rV_K; last first.
  rewrite size_divp; last by rewrite -size_poly_eq0 size_polyXn.
  rewrite size_polyXn /= -(subSn rn) (@leq_trans (n - d.-1)) //.
  by rewrite leq_sub2r // size_poly.
by rewrite addrC -divp_eq.
Qed.

Lemma RS_enc_surjective (c : 'rV[F]_n) : c \in RS.codebook a n' r ->
  encoder (high c) = c.
Proof.
move=> c_RS; apply/eqP; rewrite -subr_eq0 -rVpoly0.
set m := high c.
suff H : (size (rVpoly (encoder m - c))) <= d.-1.
  have : encoder m - c \in RS.codebook a n' r.
    have Hencm : encoder m \in RS.codebook a n' r.
      move: RS_enc_img.
      rewrite -RS.lcode0_codebook //.
      move/subsetP/(_ (encoder m)) => K.
      have : encoder m \in [set encoder x | x : 'rV_(n - d).+1] by apply/imsetP; exists m.
      move/K => {K}.
      by rewrite inE.
    case: (RS.addr_closed a n' r) => _.
    move/(_ _ (- c) Hencm); apply.
    by rewrite RS.oppr_closed.
  have d_pos : 0 < d by done.
  case/(@RS.deg_lb _ a _ _ rn a_neq0 a_not_uroot_on)/orP => [/eqP -> | ].
    apply/eqP/polyP => i.
    rewrite coef_poly coef0.
    case: ifP => // _.
    case: (insub i) => // ?; by rewrite mxE.
  move=> H'.
  move: (leq_trans H' H).
  rewrite -ltnS prednK; last exact d_pos.
  by rewrite ltnn.
rewrite /encoder ffunE linearB /= poly_rV_K; last first.
  rewrite (leq_trans (size_add _ _)) // geq_max.
  apply/andP; split.
    rewrite (leq_trans (size_mul_leq _ _)) // size_polyXn addnS /=.
    apply (@leq_trans ((n - d).+1 + d.-1)).
      by rewrite leq_add2r size_poly.
    by rewrite addSnnS prednK // (subnK rn).
  rewrite size_opp (@leq_trans d.-1) //; last first.
    rewrite -ltnS prednK // ltnW // ltnS; exact dn.
  by rewrite -ltnS prednK // {2}/d -(size_rs_gen a r) ltn_modp gen_neq0.
pose c1 := low c.
rewrite (_ : _ - _ = - rVpoly c1 - (rVpoly m * 'X^d.-1) %% \gen_(a, r)); last first.
  rewrite addrC addrA; congr (_ - _).
  by rewrite (decomp_codeword c) opprD subrK.
rewrite (leq_trans (size_add _ _)) // geq_max.
apply/andP; split.
  by rewrite size_opp /rVpoly size_poly.
by rewrite size_opp -ltnS -(size_rs_gen a r) ltn_modp gen_neq0.
Qed.

Lemma RS_enc_discard_is_id : cancel_on (RS.code a n r) encoder RS_discard.
Proof.
move=> /= c Hc.
rewrite /RS_discard -/(high c); apply RS_enc_surjective.
by rewrite -RS.lcode0_codebook // ?inE.
Qed.

Definition RS_as_lcode (an1 : a ^+ n = 1) (Hchar : ([char F]^').-nat n) : Lcode.t _ _ _ [finType of 'rV_(n - d).+1] :=
 @Lcode.mk _ _ _ _ _
   (Encoder.mk RS_enc_injective RS_enc_img)
   (Decoder.mk (RS_repair_img an1 Hchar) RS_discard)
   RS_enc_discard_is_id.

End RS_encoder_sect.

End RS_encoder.

Section RS_cyclic.

Variable (F : finFieldType) (a : F).
Variables (r : nat) (n' : nat).
Let n := n'.+1.
Hypothesis rn : RS.redundancy_ub r n.
Hypothesis an : n.-primitive_root a.
Let a0 : a != 0 := primitive_uroot_neq0 an.
Let an1 : a ^+ n = 1 := prim_expr_order an.

Lemma RS_cyclic : rcsP [set cw in RS.code a n r].
Proof.
rewrite (_ : [set cw in _] = [set cw in RS.codebook a n' r]); last first.
  apply/setP => i; by rewrite -RS.lcode0_codebook // inE 2![in RHS]inE.
move=> /= y.
rewrite !inE => /forallP x_RS.
apply/forallP => /= i; apply/implyP => i0; apply/eqP.
move: x_RS => /(_ i); rewrite i0 implyTb => /eqP x_RS.
move/(congr1 (fun x => a^+i * x)) : x_RS.
rewrite mulr0 => H.
apply fdcoor_rcs; first exact: prim_expr_order.
move/eqP: H.
by rewrite mulf_eq0 expf_eq0 i0 (negbTE a0) /= => /eqP.
Qed.

Local Open Scope cyclic_code_scope.

Lemma rs_gen_is_gen : poly_rV \gen_(a, r) \is 'cgen[Ccode.mk RS_cyclic].
Proof.
apply pgen_is_cgen => /=.
  exact: RS_not_trivial.
apply/forallP => /= p; apply/eqP; apply/idP/idP.
  move=> Hp.
  move: (proj1 (rs_genP rn a0 (prim_root_not_uroot_on an) p)).
  rewrite RS.codebook_syndrome //.
  rewrite inE mem_kernel_syndrome0 /syndrome in Hp.
  rewrite Hp => /(_ erefl); case=> m [H1 H2].
  rewrite poly_rV_K // ?size_rs_gen //.
  by rewrite H2 dvdp_mull // modpp.
move=> Hp.
rewrite inE mem_kernel_syndrome0 /linearcode.syndrome.
rewrite -(@RS.codebook_syndrome _ a n' r) //.
apply: (proj2 (rs_genP rn a0 (prim_root_not_uroot_on an) p)).
rewrite poly_rV_K // ?size_rs_gen // in Hp.
case/dvdpP : Hp => x Hx.
exists x; split => //.
by apply: RS_message_size Hx.
Qed.

End RS_cyclic.
