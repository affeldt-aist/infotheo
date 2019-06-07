From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop prime ssralg.
From mathcomp Require Import poly polydiv finset finalg zmodp matrix mxalgebra.
From mathcomp Require Import mxpoly vector cyclic perm.
Require Import ssr_ext ssralg_ext hamming.

(** * Discrete Fourier transform and BCH argument *)

(** OUTLINE
- Section not_nth_root_of_unity.
- Section rVexp.
- Section frequency_domain_coordinates.
- Section discrete_Fourier_transform.
- Section primitive_nth_root_of_unity.
- Section inverse_dft.
- Section tdcoor_of_fdcoor.
- Section shifts.
- Section BCH_argument.
*)

Reserved Notation "v ^`_( f , i )" (at level 9).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Local Open Scope vec_ext_scope.

Section not_nth_root_of_unity.

Variables (F : fieldType) (a : F) (n : nat).

(** not a kth root of unity for k \in (0,n): *)
Definition not_uroot_on := forall k, 0 < k < n -> a ^+ k != 1 (*~~ k.-unity_root a*).

Hypotheses (a0 : a != 0) (H : not_uroot_on).

Lemma exp_inj_helper_nat k l : k < n -> k < l -> l < n -> a ^+ k != a ^+ l.
Proof.
case: k => [|k] kn kl ln; first by rewrite expr0 eq_sym H // kl.
have /H : 0 < l - k.+1 < n.
  apply/andP; split; first by rewrite ltn_subRL addn0.
  rewrite -subSn; by [rewrite leq_subLR ltn_addl | rewrite (ltn_trans _ kl)].
apply: contra => /eqP /(congr1 (fun x => x * a ^- k.+1)).
have /divff -> : a ^+ k.+1 != 0 by rewrite expf_neq0.
by rewrite -expfB // => ->.
Qed.

Lemma exp_inj_helper_ord (k l : 'I_n) : k != l -> a ^+ k != a ^+ l.
Proof.
rewrite neq_ltn => /orP H'.
wlog : k l H' / k < l.
  case: (H') => H''; first by apply.
  rewrite eq_sym; apply => //; by apply/or_comm.
move=> kl; by rewrite exp_inj_helper_nat.
Qed.

Lemma exp_inj (k l : 'I_n) : (a ^+ k == a ^+ l) = (k == l).
Proof.
case H' : (k == l); first by rewrite (eqP H') eqxx.
by move/negbT : H' => /exp_inj_helper_ord /negbTE.
Qed.

End not_nth_root_of_unity.

Section rVexp.

Variables (F : fieldType) (a : F) (n : nat).

Definition rVexp := \row_(i < n) a ^+ i.

Lemma rVexp_neq0 i (a0 : a != 0) : rVexp ``_ i != 0.
Proof. by rewrite mxE expf_eq0 /= negb_and a0 orbT. Qed.

Lemma rVexp_inj (a0 : a != 0) (H : not_uroot_on a n) : injective [ffun i => rVexp ``_ i].
Proof.
move=> i j.
rewrite 2!ffunE 2!mxE => /eqP.
by rewrite exp_inj // => /eqP.
Qed.

End rVexp.

Section frequency_domain_coordinates.

Variables (F : fieldType) (n : nat).

Implicit Types x y a : 'rV[F]_n.

(** see [McEliece 2002] eqn 9.11 *)
Definition fdcoor a y i := (rVpoly y).[a ``_ i].

Variable a : 'rV[F]_n.

Local Notation "y ^`_ i" := (fdcoor a y i) (at level 9).

Lemma fdcoor0 i : (0 : 'rV_n) ^`_ i = 0.
Proof. by rewrite /fdcoor linear0 horner0. Qed.

Lemma fdcoorN x i : (- x) ^`_ i = - x ^`_ i.
Proof. by rewrite /fdcoor linearN hornerN. Qed.

Lemma fdcoorD x y i : (x + y) ^`_ i = x ^`_ i + y ^`_ i.
Proof. by rewrite /fdcoor linearD /= hornerD. Qed.

Lemma fdcoorB x y i : (x - y) ^`_ i = x ^`_ i - y ^`_ i.
Proof. by rewrite /fdcoor linearB /= hornerD hornerN. Qed.

Lemma tdcoorZ k x i : (k *: x) ^`_ i = k * x ^`_ i.
Proof. by rewrite /fdcoor linearZ /= hornerZ. Qed.

Lemma fdcoorE y i : y ^`_ i = \sum_(j < n) (y ``_ j) * (a ``_ i) ^+ j.
Proof.
rewrite /fdcoor horner_poly; apply eq_bigr => j _; rewrite insubT //= => jn.
rewrite (_ : Ordinal jn = j) //; by apply/val_inj.
Qed.

End frequency_domain_coordinates.

Notation "v ^`_( f , i )" := (fdcoor f v i) : dft_scope.
Local Open Scope dft_scope.

Section discrete_Fourier_transform.

Variables (F : fieldType) (n' : nat).
Let n := n'.+1.
Variable (a : 'rV[F]_n).
Variable t : nat.

Definition dft (v : 'rV[F]_n) : 'rV[F]_t := \row_(k < t) v ^`_(a, inord k).

(* see [McEliece 2002], eqn 9.15 *)
(*Lemma fdcoor_of_tdcoor (v : 'rV[F]_n) (i : 'I_t) : (dft v)``_i = (rVpoly v).[a (inord i)].
Proof. by rewrite /dft mxE /fdcoor. Qed.*)

Lemma dftE (v : 'rV[F]_n) :
  rVpoly (dft v) = \sum_(i in supp v) (v ``_ i *: \sum_(j < t) (a ``_ (inord j)) ^+ i *: 'X^j).
Proof.
rewrite /dft.
evar (tmp : 'I_n -> {poly F}).
rewrite [in RHS](eq_bigr (fun i => tmp i)); last first.
  move=> i iv.
  rewrite scaler_sumr /tmp; reflexivity.
rewrite {}/tmp exchange_big /= /rVpoly poly_def; apply eq_bigr => i _.
evar (tmp : 'I_n -> {poly F}).
rewrite [in RHS](eq_bigr (fun i => tmp i)); last first.
  move=> j jv.
  rewrite scalerA /tmp; reflexivity.
rewrite {}/tmp /fdcoor -scaler_suml; congr (_ *: _).
rewrite insubT // => ni.
rewrite mxE (@horner_coef_wide _ n); last by rewrite /rVpoly size_poly.
evar (tmp : 'I_n -> F).
rewrite [in RHS](eq_bigr (fun i => tmp i)); last first.
  move=> j jv; rewrite /tmp; reflexivity.
rewrite {}/tmp -sum_supp; apply eq_bigr => j _.
rewrite coef_rVpoly_ord (_ : Sub _ _ = i) //; by apply val_inj.
Qed.

End discrete_Fourier_transform.

Section primitive_nth_root_of_unity.

Variables (F : fieldType) (a : F) (n : nat).

Lemma prim_root_not_uroot_on : n.-primitive_root a -> not_uroot_on a n.
Proof.
destruct n as [|n'] => //.
move/forallP => H k /andP[k0 kn].
rewrite -unity_rootE.
move: (H (Ordinal (leq_ltn_trans (leq_pred k) kn))) => /=.
rewrite prednK // => /eqP ->.
by move: kn; rewrite ltnNge; apply: contra => /eqP ->.
Qed.

Lemma not_uroot_on_prim_root :
  not_uroot_on a n.+1 -> a ^+ n.+1 = 1 -> n.+1.-primitive_root a.
Proof.
move=> H an1.
apply/forallP => /= i.
rewrite unity_rootE -an1.
case/boolP : (a == 0) => [/eqP ?|a0].
  subst a.
  move: an1; rewrite expr0n /= => /eqP.
  by rewrite eq_sym oner_eq0.
rewrite !exprS.
apply/eqP; apply/idP/idP => /eqP.
  move: (exp_inj a0 H i (Ordinal (ltnSn n))) => H' /mulrI.
  rewrite unitfE => /(_ a0) /eqP.
  by rewrite H' => /eqP ->.
by case=> ->.
Qed.

Lemma primitive_uroot_neq0 : n.+1.-primitive_root a -> a != 0.
Proof.
move=> abs; apply/negP => /eqP ?; subst a.
move/prim_expr_order : abs.
by rewrite expr0n /= => /eqP; rewrite eq_sym oner_eq0.
Qed.

(** a is a principal nth root of unity: *)
Lemma primitive_is_principal : n.-primitive_root a ->
  forall k, 1 <= k < n -> \sum_(j < n) a ^+ (j * k) = 0.
Proof.
move=> an k kn.
move/(congr1 (fun x => x ^+ k)) : (prim_expr_order an).
rewrite expr1n -exprM mulnC exprM => /eqP.
rewrite -subr_eq0 => /eqP an1.
suff : a ^+ k ^+ n - 1 = (a ^+ k - 1) * \sum_(j < n) a ^+ k ^+ j.
  rewrite an1 => /esym/eqP.
  rewrite mulf_eq0 => /orP[|/eqP tmp].
    rewrite subr_eq0 -(prim_order_dvd an) gtnNdvd //; by case/andP : kn.
  rewrite -[in RHS]tmp.
  apply eq_bigr => i _; by rewrite mulnC exprM.
rewrite mulrDl mulN1r.
destruct n as [|n'] => //.
rewrite {1}big_ord_recr /= mulrDr (addrC (a ^+ k * _)).
rewrite -(exprM _ k n') -exprD -mulnS -exprM -addrA; congr (_ + _).
rewrite big_distrr /= addrC big_ord_recl expr0 opprD.
apply/eqP; rewrite -subr_eq; apply/eqP; congr (-1 - _).
apply eq_bigr => i _.
by rewrite -!exprM -exprD -mulnS.
Qed.

End primitive_nth_root_of_unity.

Section inverse_dft.

Variables (F : fieldType) (n' : nat) (a : F).
Let n := n'.+1.

(** inverse of the discrete Fourier transform (see [McEliece 2002], eqn 9.12) *)
Definition idft_coef (f : 'rV[F]_n) (j : nat) := (n%:R^-1) * \sum_(k < n) (f ``_ k) * a ^- (j * k).

Definition idft (f : 'rV[F]_n) : 'rV[F]_n := \row_(i < n) idft_coef f i.

Lemma idft0 : idft (0 : 'rV[F]_n) = 0.
Proof.
rewrite /idft; apply/rowP => i; rewrite !mxE /idft_coef.
apply/eqP; rewrite mulf_eq0; apply/orP; right.
rewrite (eq_bigr (fun=> 0)); first by rewrite big_const iter_addr0.
move=> j _; by rewrite mxE mul0r.
Qed.

(** the characteristic of F is not a prime divisor of n: *)
Hypothesis Hchar : ([char F]^').-nat n.

Hypothesis an : n.-primitive_root a.
Let a_neq0 : (a != 0) := primitive_uroot_neq0 an.

(** see [McEliece 2002], problem 9.8 *)
Lemma dftK (v : 'rV[F]_n) : idft (dft (rVexp a n) n v) = v.
Proof.
apply/rowP => i; rewrite !mxE.
rewrite /idft_coef.
transitivity (n %:R^-1 * \sum_(k < n) \sum_(j' < n) v ``_ j' * a ^+ (j' * k) / a ^+ (i * k)).
  congr (_ * _).
  apply eq_bigr => k _.
  rewrite mxE /fdcoor horner_poly big_distrl /=; apply eq_bigr => j' _.
  rewrite insubT // => j'n.
  rewrite mxE inordK // -exprM mulnC; congr (v ``_ _ * _ * _); by apply val_inj.
transitivity (n %:R^-1 * \sum_(j' < n) v ``_ j' * \sum_(k < n) a ^+ (j' * k) / a ^+ (i * k)).
  congr (_ * _); rewrite exchange_big /=.
  apply eq_bigr => i0 _.
  rewrite big_distrr /=; apply eq_bigr => j' _; by rewrite mulrA.
rename i into j.
rewrite (bigD1 j) //= (eq_bigr (fun=> 1)); last first.
  by move=> k _; rewrite divff // expf_neq0.
rewrite sumr_const card_ord mulrDr mulrCA mulVr ?mulr1; last first.
  by rewrite unitfE natf_neq0.
rewrite [X in _ + _ * X = _](_ : _ = 0) ?mulr0 ?addr0 //.
rewrite (eq_bigr (fun=> 0)) ?big_const ?iter_addr0 // => i ij.
apply/eqP.
rewrite mulf_eq0; apply/orP; right.
move: ij.
rewrite neq_ltn => /orP[ij|ji]; last first.
  rewrite (eq_bigr (fun k : 'I_n => a ^+ (k * (i - j)))); last first.
  move=> k _.
  rewrite -exprB ?unitfE //; last first.
    by rewrite leq_mul // ltnW.
  by rewrite mulnBr 2!(mulnC k).
  rewrite (primitive_is_principal an) //.
  by rewrite subn_gt0 ji /= (leq_ltn_trans _ (ltn_ord i)) // leq_subr.
rewrite (eq_bigr (fun k : 'I_n => a ^- ((j - i) * k))); last first.
  move=> k _.
  do 3 rewrite mulnC exprM.
  by rewrite exprB ?invf_div // ?unitfE ?expf_neq0 // ltnW.
have abs : n.-primitive_root a^-1.
  apply/not_uroot_on_prim_root.
  - move=> k /andP[k0 kn].
    move : an.
    rewrite /primitive_root_of_unity /= => /forallP/(_ (Ordinal (leq_ltn_trans (leq_pred _) kn))) /=.
    rewrite prednK // ltn_eqF // => /eqP.
    apply: contraFN => /eqP.
    rewrite exprVn => /(congr1 (fun x => x^-1))/eqP.
    by rewrite invrK invr1 unity_rootE.
  move/prim_expr_order : an => /(congr1 (fun x => x^-1)).
  by rewrite invr1 exprVn.
have : 0 < j - i < n.
  by rewrite subn_gt0 ij /= (leq_ltn_trans _ (ltn_ord j)) // leq_subr.
move/(primitive_is_principal abs) => {abs}abs.
apply/eqP.
rewrite -[in RHS]abs; apply/eq_bigr => k _.
by rewrite exprVn mulnC.
Qed.

Lemma dft0 (u : 'rV[F]_n) : (dft (rVexp a n) n u == 0) = (u == 0).
Proof.
apply/idP/idP => [/eqP|/eqP ->].
  move/(congr1 (fun x => idft x)); by rewrite dftK idft0 => /eqP.
apply/eqP/rowP => i; by rewrite !mxE fdcoor0.
Qed.

End inverse_dft.

Section tdcoor_of_fdcoor.

Variables (F : fieldType) (a : F) (n' : nat).
Let n := n'.+1.
Hypothesis Hchar : ([char F]^').-nat n.

Hypothesis an : n.-primitive_root a.

(** see [McEliece 2002], eqn 9.16 *)
Lemma tdcoor_of_fdcoor i (v : 'rV[F]_n) :
  v``_i = n%:R^-1 * (rVpoly (dft (rVexp a n) n v)).[a ^- i].
Proof.
rewrite -[in LHS](dftK Hchar an v) mxE.
rewrite /idft_coef; congr (_ * _); rewrite horner_poly.
apply eq_bigr => j _.
rewrite insubT // => jn.
rewrite (_ : Sub _ _ = j); last by apply/val_inj.
by rewrite -!exprVn exprM.
Qed.

End tdcoor_of_fdcoor.

Section shifts.

Variables (F : fieldType) (a : F) (n' : nat).
Let n := n'.+1.

Definition phase_shift (v : 'rV[F]_n) mu : 'rV[F]_n := \row_i ((v ``_ i) * a ^+ (mu * i)).

Hypothesis a_neq0 : a != 0.

Lemma wH_phase_shift (v : 'rV[F]_n) (m : nat) : wH (phase_shift v m.+1) = wH v.
Proof.
elim: m => [|m IH].
  rewrite /phase_shift /wH !count_map.
  apply eq_count => i /=.
  by rewrite mxE mul1n mulf_eq0 negb_or expf_neq0 // andbT.
rewrite -IH /phase_shift /wH !count_map.
apply eq_count => i /=.
by rewrite !mxE !mulf_eq0 !negb_or !expf_neq0.
Qed.

(** see [McEliece 2002], eqn 9.18 *)
Lemma time_shift (an1 : a ^+ n = 1) (v : 'rV[F]_n) (m : nat) :
  dft (rVexp a n) n (phase_shift v m) = \row_i ((dft (rVexp a n) n v)``_(inord ((m + i) %% n))).
Proof.
  apply/rowP => i.
rewrite !mxE /fdcoor !horner_poly.
apply/eq_bigr => /= j _.
rewrite insubT // => jn.
rewrite !mxE -mulrA (_ : Sub _ _ = j); last by apply val_inj.
congr (_ * _).
rewrite inordK ?ltn_pmod //.
rewrite inordK //.
rewrite inordK ?ltn_pmod //.
move: (divn_eq (m + i) n); rewrite (addnC (_ %/ _ * _)%N).
move/(congr1 (fun x => x - ((m + i) %/ n * n))%N); rewrite addnK => <-.
rewrite -[in LHS]exprM -[in LHS]exprD.
rewrite -[in RHS]exprM [in RHS]mulnBl.
rewrite [in RHS]GRing.exprB; last 2 first.
  by rewrite leq_mul // leq_trunc_div.
  by rewrite unitfE.
rewrite [in X in _ = _ / X]mulnAC [in X in _ = _ / X]mulnC.
by rewrite [in X in _ = _ / X]exprM an1 expr1n divr1 mulnDl.
Qed.

Lemma dft_shifting (an1 : a ^+ n = 1) (v : 'rV[F]_n) m (mn : m < n) :
  (forall i : 'I_n, 0 < i < m.+1 -> (dft (rVexp a n) n v) ``_ i = 0) ->
  let w := phase_shift v m.+1 in
  (forall i : 'I_n, n - m <= i < n -> (dft (rVexp a n) n w) ``_ i = 0).
Proof.
move=> H w i Hi.
rewrite time_shift // mxE H // inordK // ?ltn_pmod //.
have /andP [Hi'1 Hi'2] : n < i + m.+1 < n + m.+1.
  case/andP : Hi => Hi1 Hi2.
  by rewrite ltn_add2r Hi2 andbT addnC -leq_subLR subSS.
rewrite -(subn0 (m.+1 + i)%N).
apply/andP.
rewrite -{-1}(subnn n) subnBA // addnC -addnBA; last by rewrite addnC ltnW.
rewrite modnDl modn_small; last first.
  rewrite addnC -(ltn_add2r n) subnK; last by rewrite ltnW.
  by rewrite (leq_trans Hi'2) // leq_add2l.
split; first by rewrite subn_gt0 addnC.
by rewrite -(ltn_add2r n) subnK ?ltn_add2l // addnC ltnW.
Qed.

End shifts.

Section BCH_argument.

Variables (F0 F : fieldType).
Variable gmorph : {rmorphism F0 -> F}.
Variable (n' : nat).
Let n := n'.+1.
Hypothesis (Hchar : ([char F]^').-nat n).

Variable (a : F).
Hypothesis an : n.-primitive_root a.

(** a.k.a. BCH_bound (see [Classification by Isometry], p.238)  *)
Lemma BCH_argument_lemma (w : 'rV[F0]_n) (m : nat) (mn : m < n) : w != 0 ->
  (forall i : 'I_n, n - m <= i < n -> (dft (rVexp a n) n (\row_i (gmorph w``_ i))) ``_ i = 0) ->
  m.+1 <= wH w.
Proof.
move=> w0 dftw0.
have size_rVpoly : size (rVpoly (dft (rVexp a n) n (\row_i (gmorph w``_i)))) <= n - m.
  apply/leq_sizeP => j nmj.
  case/boolP : (j < n) => jn.
    by rewrite coef_poly jn insubT // dftw0 // nmj.
  by rewrite coef_poly (negbTE jn).
have neq_0 : rVpoly (dft (rVexp a n) n (\row_i (gmorph w``_i))) != 0.
  apply: contra w0.
  move/eqP/(congr1 (@poly_rV _ n)).
  rewrite rVpolyK linear0.
  move/eqP.
  rewrite dft0 // => dft_0.
  apply/eqP/rowP => i.
  rewrite mxE.
  move/eqP/(congr1 (fun x : 'rV[F]_n => x ``_ i)) : dft_0.
  rewrite !mxE -(rmorph0 gmorph).
  by move/fmorph_inj.
have root_rVpoly: forall rs, all (root (rVpoly (dft (rVexp a n) n (\row_i (gmorph w``_i))))) rs ->
    uniq rs -> size rs <= n - m -1.
  move=> rs all_rs uniq_rs.
  rewrite -ltnS.
  apply: (leq_trans (max_poly_roots neq_0 all_rs uniq_rs) _).
  by rewrite subnS subn0 prednK // subn_gt0.
rewrite wH_rVpoly.
suff : n - m > count (fun i : 'I_n => (rVpoly w)`_i == 0) (enum 'I_n).
  set f := fun i => _.
  move: (count_predC f (enum 'I_n)).
  rewrite size_enum_ord => Hn.
  rewrite -[in X in _ <= X - _ -> _]Hn -(ltn_add2r m) subnK; last first.
    by rewrite count_predC size_enum_ord ltnW.
  rewrite ltn_add2l.
  move/leq_trans; apply.
  by apply/eq_leq/eq_count.
rewrite (_ : count _ _ = count (fun i : 'I_n => 
  (rVpoly (dft (rVexp a n) n (\row_i gmorph w ``_ i))).[a ^- i] == 0) (enum 'I_n)); last first.
  apply eq_count => i.
  rewrite coef_poly (ltn_ord i) insubT // => ni.
  apply eq_trans with ((\row_i0 gmorph w ``_ i0) ``_ i == 0).
    rewrite mxE.
    apply/idP/idP => [/eqP H|].
      rewrite (_ : Sub _ _ = i) in H; last by apply val_inj.
      by rewrite H rmorph0.
    rewrite [X in _ == X -> _](_ : 0 = gmorph 0); last by rewrite rmorph0.
    move/eqP/fmorph_inj.
    rewrite (_ : Sub _ _ = i) //; last by apply val_inj.
    by move/eqP.
  rewrite (tdcoor_of_fdcoor Hchar an i (\row_i gmorph w ``_ i)).
  rewrite mulf_eq0 invr_eq0 /=.
  rewrite -[RHS]orFb.
  congr (_ || _).
  apply/negbTE.
  by rewrite natf_neq0.
rewrite ltnNge.
apply/negP => abs.
set rs := filter (fun i => root (rVpoly (dft (rVexp a n) n (\row_i0 gmorph w ``_ i0))) i)
                  (map (fun i : 'I_n => a ^- i) (enum 'I_n)).
have rs_uniq : uniq rs.
  rewrite filter_uniq //.
  rewrite map_inj_in_uniq ?enum_uniq // => i j _ _ bij.
  move/prim_root_not_uroot_on : an => an'.
  apply/eqP; rewrite -(exp_inj (primitive_uroot_neq0 an) an'); apply/eqP.
  move/(congr1 (fun x => x ^-1)) : bij.
  by rewrite -!exprVn invrK.
have rs_root : all (root (rVpoly (dft (rVexp a n) n (\row_i gmorph w ``_ i)))) rs.
  apply/allP => x.
  by rewrite mem_filter => /andP[].
move: (root_rVpoly _ rs_root rs_uniq).
apply/negP.
rewrite -ltnNge subn1 prednK // ?subn_gt0 // /rs size_filter.
apply: (leq_trans abs).
apply eq_leq.
rewrite [in RHS]count_map.
by apply eq_count => i /=.
Qed.

End BCH_argument.
