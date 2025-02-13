(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg finalg poly polydiv cyclic.
From mathcomp Require Import perm matrix mxpoly.
Require Import ssr_ext ssralg_ext cyclic_code dft.

(**md**************************************************************************)
(* # Error-locator, error-evaluator, and syndrome polynomials                 *)
(*                                                                            *)
(* Main lemmas:                                                               *)
(* - the error locator and evaluator polynomials are coprime (lemma           *)
(*   `coprime_errloc_erreval`)                                                *)
(* - characterization of an error vector in terms of the error and the        *)
(*   evaluator polynomials (`erreval_vecE`)                                   *)
(*                                                                            *)
(* ```                                                                        *)
(*    \sigma_(a , e ) == error locator polynomial for the vector e            *)
(*   \sigma_(a, e, i) == the ith punctured locator polynomial for             *)
(*        t.-rV[R]_ n == error vector with support of cardinal <= t           *)
(*   \omega_(f, a, e) == error evaluator polynomial                           *)
(*          syndromep == syndrome polynomial                                  *)
(*            twisted == TODO                                                 *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "'\sigma_(' a , e )" (at level 3).
Reserved Notation "'\sigma_(' a , e , i )" (at level 3).
Reserved Notation "t '.-'rV[' R ]_ n" (at level 2).
Reserved Notation "'\omega_(' f , a , e )" (at level 3).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(* TODO: move to poly_ext? *)
Lemma modp_Xn (R : idomainType) j (p : {poly R}) i :
  i <= j -> size (p %% 'X^j) <= i -> p %% 'X^i = p %% 'X^j.
Proof.
move=> ij H0.
have H : forall n, lead_coef 'X^n \is a GRing.unit
  by move=> ??; rewrite lead_coefXn GRing.unitr1.
rewrite (Pdiv.IdomainUnit.divp_eq (H R j) p).
rewrite (Pdiv.IdomainUnit.modpD (H R i)).
rewrite modp_eq0; last by rewrite dvdp_mull // dvdp_exp2l.
by rewrite add0r -(Pdiv.IdomainUnit.divp_eq (H R j) p) modp_small // size_polyXn.
Qed.

(* TODO: useful? *)
Lemma size_one_minus_X (R : idomainType) (a : R) (a0 : a != 0) :
  size (1 - a *: 'X) = 2%N.
Proof.
rewrite addrC size_addl.
  by rewrite size_opp size_scale ?size_polyX // expf_neq0.
by rewrite size_opp size_scale ?expf_neq0 // size_polyX size_polyC oner_eq0.
Qed.

Lemma one_minus_X_neq0 (R : idomainType) (a : R) : 1 - a *: 'X != 0.
Proof.
rewrite subr_eq0; apply/eqP => /(congr1 (fun x => x.[0])).
rewrite !hornerE; apply/eqP; by rewrite oner_eq0.
Qed.

(* NB: not used *)
Section error_locator_polynomial_alt.
Variables (F : fieldType) (n : nat) (a : {ffun 'I_n -> F}).

Definition errloc_alt (E : {set 'I_n}) : {poly F} :=
  \prod_(i in E) ('X - (a i)%:P).

End error_locator_polynomial_alt.

Local Open Scope vec_ext_scope.

Section distinct_non_zero.
Variables (F : fieldType) (n : nat).

Definition distinct_non_zero (a : 'rV[F]_n) :=
  injective [ffun i => a ``_i] /\ (forall i, a ``_ i != 0).

Lemma distinct_non_zero_rVexp (a : F) (a0 : a != 0) (H : not_uroot_on a n) :
  distinct_non_zero (rVexp a n).
Proof.
rewrite /distinct_non_zero; split; first by apply rVexp_inj.
move=> ?; by rewrite mxE expf_neq0.
Qed.

End distinct_non_zero.

Section error_locator_polynomial.
Variables (F : fieldType) (n : nat).

Definition errloc (a : 'rV[F]_n) (E : {set 'I_n}) : {poly F} :=
  \prod_(i in E) (1 - a ``_ i *: 'X).

Lemma errloc0 (a : 'rV[F]_n) : errloc a set0 = 1.
Proof. by rewrite /errloc big_set0. Qed.

Lemma horner_errloc_0 (a : 'rV[F]_n) E : (errloc a E).[0] = 1.
Proof.
rewrite /errloc horner_prod (eq_bigr (fun=> 1)) ?big1_eq //.
by move=> /= j _; rewrite !hornerE subr0.
Qed.

Lemma derive_errloc (a : 'rV[F]_n) E : (errloc a E)^`() =
  \sum_(j in E) - a ``_ j *: \prod_(k in E :\ j) (1 - a ``_ k *: 'X).
Proof.
move Hm : (#| E |) => m.
elim: m E Hm => [E /eqP| m IH E Em].
  rewrite cards_eq0 => /eqP ->; by rewrite /errloc 2!big_set0 derivC.
have [/= f Hf] : exists f, f \in E by apply/set0Pn; rewrite -cards_eq0 Em.
rewrite /errloc (big_setD1 f) //= derivM IH; last first.
  move: (cardsD1 f E); rewrite Hf /= add1n Em; by case.
rewrite derivB derivC sub0r linearZ /= derivX.
rewrite [in RHS](big_setD1 f) //=; congr (_ + _).
  by rewrite alg_polyC -mul_polyC polyCN.
rewrite big_distrr /=; apply eq_bigr => i Hi.
rewrite mulrC -!mul_polyC -mulrA; congr (_ * _).
rewrite [in RHS](big_setD1 f) //=; last first.
  rewrite in_setD1; by move: Hi; rewrite in_setD1 eq_sym => /andP [] ->.
rewrite mulrC mul_polyC; congr (_ * _).
apply eq_bigl => ?; rewrite !in_setD1; bool_congr.
Qed.

Lemma decomp_errloc (a :'rV[F]_n) E : (forall i, a ``_ i != 0) ->
  errloc a E = (\prod_(i in E) (- a ``_ i)%:P) * \prod_(i in E) ('X - (a ``_ i)^-1%:P).
Proof.
move=> a0.
rewrite /errloc (eq_bigr (fun i : 'I_n => (- a ``_ i)%:P * ('X - (a ``_ i)^-1%:P))).
  by rewrite big_split.
move=> i iE.
rewrite -polyCN mulrDr -polyCM mulrNN divff //.
by rewrite polyC1 -(addrC 1) polyCN mulNr mul_polyC.
Qed.

Lemma errloc_neq0 a E : errloc a E != 0.
Proof. apply/prodf_neq0 => /= i _; by rewrite one_minus_X_neq0. Qed.

Lemma size_errloc a E : size (errloc a E) <= #| E |.+1.
Proof.
apply: (leq_trans (size_prod_leq (fun x => x \in E) (fun i => 1 - a ``_ i *: 'X))).
apply (@leq_trans (#|E|.*2.+1 - #|E|)); last first.
  by rewrite subSn -addnn ?leq_addr // addnK.
rewrite leq_sub // ltnS.
apply (@leq_trans (\sum_(i in E) 2)); last by rewrite big_const iter_addn_0 mul2n.
apply leq_sum => /= i iE.
have [->|ai0] := eqVneq (a ``_ i) 0.
  by rewrite scale0r subr0 size_poly1.
by rewrite size_one_minus_X.
Qed.

Lemma errloc_zero (a : 'rV[F]_n) E (i : 'I_n) : distinct_non_zero a ->
  ((errloc a E).[(a ``_ i)^-1] == 0) = (i \in E).
Proof.
move=> Ha; apply/idP/idP => H.
- apply/negPn/negP => abs; move/eqP: H.
  apply/rootP.
  rewrite (decomp_errloc _ (proj2 Ha)) ?unitfE //= rootM negb_or.
  apply/andP; split.
    rewrite -(@big_morph _ _ _ _ _ 1 _ (@polyCM F)) // rootC prodf_seq_neq0 /=.
    apply/allP => n0 _.
    apply/implyP => _; by rewrite oppr_eq0 (proj2 Ha).
  move: (root_prod_XsubC [seq (a ``_ x)^-1 | x : 'I_n <- enum E] (a ``_ i)^-1).
  rewrite big_map -[in X in _ -> X]big_filter => ->.
  apply: contra abs.
  case/mapP => /= j Hj /invr_inj aij.
  move: (proj1 Ha) => /(_ i j); rewrite 2!ffunE => /(_ aij) ->.
  by rewrite -mem_enum.
- rewrite /errloc horner_prod prodf_seq_eq0.
  apply/hasP; exists i => //.
  rewrite H /= !hornerE divff ?(proj2 Ha) ?subrr // expf_neq0.
Qed.

Lemma size_errloc_eq a E : distinct_non_zero a -> size (errloc a E) = #| E |.+1.
Proof.
move=> Ha.
rewrite /errloc.
rewrite (eq_bigr (fun i : 'I_n => (- a ``_ i *: ('X - (a ``_ i)^-1%:P)))); last first.
  move=> i iE.
  rewrite scalerDr addrC !scaleNr scalerN opprK; congr (_ + _).
  rewrite -mul_polyC -!alg_polyC mulr_algl scalerA.
  rewrite divrr // ?alg_polyC // unitfE.
  by case: Ha => _; apply.
rewrite scaler_prod size_scale; last first.
  apply/prodf_neq0 => i iE; by rewrite oppr_eq0 (proj2 Ha).
rewrite (_ : \prod_(i in E) ('X - (a ``_ i)^-1%:P) =
  \prod_(i <- enum E) ('X - (a ``_ i)^-1%:P)); last by rewrite big_filter.
by rewrite size_prod_XsubC cardE.
Qed.

End error_locator_polynomial.

Notation "'\sigma_(' a , e )" := (errloc a (supp e)).
Notation "'\sigma_(' a , e , i )" := (errloc a (supp e :\ i)).

Lemma errloc_puncture (F : fieldType) n (f : 'rV[F]_n) (y : 'rV[F]_n) i :
  i \in supp y -> \sigma_(f, y) = (1 - f ``_ i *: 'X ) * \sigma_(f, y, i).
Proof.
move=> ?; rewrite {1}/errloc (bigD1 i) //=; congr (_ * _).
by apply eq_bigl => j; rewrite in_setD1 andbC.
Qed.

Record errvec n (F : fieldType) t := Errvec {
  errvect :> 'rV[F]_n ;
  errsupp : #| supp errvect | <= t }.

Notation "t '.-'rV[' R ]_ n" := (@errvec n R t) (only parsing).

Lemma supp_neq0 n (F : fieldType) t (e : t.-'rV[F]_n) : supp e != set0 -> t != O.
Proof.
apply: contra => /eqP t0; case: e => /= e; by rewrite t0 leqn0 -cards_eq0.
Qed.

Section error_evaluator_polynomial_def.
Variables (F : fieldType) (n : nat).

Definition erreval (b a : 'rV[F]_n) e :=
  \sum_(i in supp e) e ``_ i * b ``_ i *: \sigma_(a, e, i).

End error_evaluator_polynomial_def.

Notation "'\omega_(' f , a , e )" := (erreval f a e).

Section error_evaluator_polynomial_prop.
Variables (F : fieldType) (n : nat) (a : 'rV[F]_n).
Variables (t : nat) (e : t.-'rV[F]_n).
Variables (f : 'rV[F]_n).

Lemma size_erreval : size \omega_(f, a, e) <= t.
Proof.
eapply leq_trans; first by apply size_sum.
apply/bigmax_leqP => i; rewrite inE => /= iE.
eapply leq_trans; first by rewrite -mul_polyC; apply size_mul_leq.
rewrite size_polyC.
apply (@leq_trans (1 + size \sigma_( a, e, i)).-1).
  rewrite add1n /= addnC; case: (_ != _) => //=.
  by rewrite addn1.
  by rewrite addn0 leq_pred.
rewrite add1n /= (leq_trans (size_errloc _ _)) //.
rewrite (_ : #|_| = #|supp e|.-1); last by rewrite (cardsD1 i (supp e)) inE /= iE.
rewrite -insupp in iE.
rewrite prednK // ?(errsupp e) // lt0n cards_eq0; by apply/set0Pn; exists i.
Qed.

Hypothesis Ha : distinct_non_zero a.
Hypothesis Hf : forall i, f ``_ i != 0.

Lemma coprime_errloc_erreval E : coprimep \sigma_(a, E) \omega_(f, a, E).
Proof.
apply/coprimepP => p p_sigma p_eta.
suff no_root_p : forall x, root p x -> False.
  move : p_sigma; rewrite (decomp_errloc _ (proj2 Ha)) //.
  move/(dvdp_mull (\prod_(i in supp E) (- a ``_ i)^-1%:P)).
  rewrite mulrA -big_split /= (eq_bigr (fun=> 1%:P)); last first.
    move=> i _; by rewrite -polyCM mulVr // unitrN unitfE (proj2 Ha).
  rewrite big1 // mul1r -big_filter; case/dvdp_prod_XsubC => bs.
  set mask_bs := mask bs _.
  case size_bsE : (size mask_bs).
    move: size_bsE => /size0nil ->; by rewrite big_nil.
  have : 0 < size mask_bs by rewrite size_bsE.
  rewrite -has_predT => /hasP [/= i i_mask_bs] _ => p_prod.
  suff : root (\prod_(j <- mask_bs) ('X - (a ``_ j)^-1%:P)) (a ``_ i)^-1.
    rewrite -(eqp_root p_prod); by move/no_root_p.
  rewrite (@big_morph _ _ (fun p => root p (a ``_ i)^-1) false orb); last 2 first.
    move=> ? ?; by rewrite rootM.
    by apply/negP/negP/root1.
  rewrite big_has /=; apply/hasP; exists i => //; by rewrite root_XsubC.
move=> x px.
have [n0 [n0e xan0]] : exists n0, n0 \in supp E /\ x = (a ``_ n0)^-1.
  have : root \sigma_(a, E) x.
    rewrite -dvdp_XsubCl; apply: dvdp_trans p_sigma; by rewrite dvdp_XsubCl.
  rewrite /root (decomp_errloc _ (proj2 Ha)) hornerM mulf_eq0; case/orP.
  - rewrite horner_prod; case/prodf_eq0 => n0 n0e.
    by rewrite !hornerE oppr_eq0 (negPf (proj2 Ha n0)).
  - rewrite horner_prod; case/prodf_eq0 => n0 n0e.
    rewrite !hornerE subr_eq0 => /eqP ->; by exists n0.
rewrite {x}xan0 in px.
have {px} : root \omega_(f, a, E) (a ``_ n0)^-1.
  rewrite -dvdp_XsubCl; apply: dvdp_trans p_eta; by rewrite dvdp_XsubCl.
rewrite /root horner_sum (bigD1 _ n0e) /=.
set q := (X in _ + X == 0 -> _).
have {q}-> : q = 0.
  rewrite {}/q (eq_bigr (fun=> 0)); first by rewrite big_const /= iter_addr0.
  move=> i /andP[ie in0].
  rewrite !hornerE /= horner_prod (bigD1 n0) /=; last first.
    by rewrite in_setD1 n0e eq_sym andbT.
  by rewrite !hornerE /= divrr ?unitfE ?(proj2 Ha) // subrr mulr0 mul0r.
rewrite addr0 !hornerE /= mulf_eq0; case/orP.
- rewrite mulf_eq0 (negbTE (Hf _)) orbF.
  by move: n0e; rewrite inE /= => /negbTE ->.
- by rewrite errloc_zero // in_setD1 eqxx.
Qed.

Lemma erreval0 : \omega_(f, a, (0 : 'rV_n)) = 0.
Proof. by rewrite /erreval supp0 big_set0. Qed.

End error_evaluator_polynomial_prop.

Section characterization_of_error_vector.
Variables (F : fieldType) (n : nat) (e : 'rV[F]_n).
Variable a : 'rV[F]_n.
Hypothesis Ha : distinct_non_zero a.
Variable f : 'rV[F]_n.

Lemma erreval_vecE i : i \in supp e ->
  e ``_ i * f ``_ i = - a ``_ i *
    \omega_(f, a, e).[(a ``_ i)^-1] / \sigma_(a, e)^`().[(a ``_ i)^-1].
Proof.
move=> iE.
have morph_horner_add : {morph (fun x => x.[(a ``_ i)^-1]) : x y / x + y >-> x + y}.
  move=> x y; exact: hornerD.
have morph_horner_mul : {morph (fun x => x.[(a ``_ i)^-1]) : x y / x * y >-> x * y}.
  move=> x y; exact: hornerM.
have -> : \omega_(f, a, e).[(a ``_ i)^-1] =
    e ``_ i * f ``_ i * \prod_(j in supp e :\ i) (1 - a ``_ j * (a ``_ i)^-1).
  rewrite (@big_morph _ _ _ 0 _ _ _ morph_horner_add); last by rewrite horner0.
  rewrite [in LHS](big_setD1 i) //= [X in _ + X = _](_ :_  = 0); last first.
    rewrite (eq_bigr (fun=> 0)); first by rewrite big_const iter_addr0.
    move=> j Hj.
    rewrite !hornerE /= (@big_morph _ _ _ 1 _ _ _ morph_horner_mul); last by rewrite hornerE.
    rewrite (big_setD1 i) /=; last first.
      rewrite !inE eq_sym in Hj.
      rewrite !inE.
      case/andP : Hj => /= ->.
      by rewrite insupp in iE.
    by rewrite !hornerE /= divrr ?unitfE ?(proj2 Ha) // ?Ht' // subrr mulr0 mul0r.
  rewrite addr0 !hornerE /=; congr (_ * _).
  rewrite (@big_morph _ _ _ 1 _ _ _ morph_horner_mul); last by rewrite hornerE.
  apply eq_bigr => ? ?; by rewrite !hornerE.
have -> : (\sigma_(a, e)^`()).[(a ``_ i)^-1] = - a ``_ i *
  \prod_(j in supp e :\ i) (1 - a ``_ j * (a ``_ i)^-1).
  rewrite derive_errloc (@big_morph _ _ _ 0 _ _ _ morph_horner_add); last by rewrite horner0.
  rewrite [in LHS](big_setD1 i) //= [X in _ + X = _](_ :_  = 0); last first.
    rewrite (eq_bigr (fun=> 0)); first by rewrite big_const iter_addr0.
    move=> j Hj.
    rewrite !hornerE /= (@big_morph _ _ _ 1 _ _ _ morph_horner_mul); last by rewrite hornerE.
    rewrite (big_setD1 i) /=; last first.
      rewrite !inE; move: Hj.
      rewrite !inE eq_sym => /andP[-> /=].
      by rewrite insupp in iE.
    by rewrite !hornerE /= divrr ?unitfE ?(proj2 Ha) // ?Ht' // subrr mulr0 mul0r.
  rewrite addr0 !hornerE /=; congr (_ * _).
  rewrite (@big_morph _ _ _ 1 _ _ _ morph_horner_mul); last by rewrite hornerE.
  apply eq_bigr => ? ?; by rewrite !hornerE.
rewrite mulrCA mulrK // unitrM unitrN unitfE (proj2 Ha) /=.
apply big_ind.
- by rewrite unitr1.
- by move=> x y; rewrite unitrM => -> ->.
- move=> j Hj; rewrite GRing.unitfE.
  suff : a ``_ j / a ``_ i != 1.
    by apply: contra => /eqP /(congr1 (fun x => x + a ``_ j / a ``_ i)); rewrite subrK add0r => <-.
  apply/eqP => /(congr1 (fun x => x * a ``_ i)).
  rewrite -mulrA mulVr ?unitfE ?(proj2 Ha) ?expf_neq0 // mulr1 mul1r.
  move: (proj1 Ha) => /(_ j i); rewrite 2!ffunE => aij.
  move/aij => ij; subst j.
  move: Hj; by rewrite in_setD1 eqxx.
Qed.

End characterization_of_error_vector.

Local Open Scope dft_scope.

Section syndrome_polynomial.
Variables (F : fieldType) (n' : nat).
Let n := n'.+1.
Implicit Types u : 'rV[F]_n.

(* polynomial of degree <= t.-1 *)
Definition syndromep u y t := \poly_(k < t) y ^`_(u, inord k.+1).

Variable u :'rV[F]_n.
Variable t : nat.

Lemma syndromepE y : syndromep u y t =
  \sum_(j in supp y) \sum_(i < t) (y ``_ j * u ``_ (inord i.+1) ^+ j) *: 'X^i.
Proof.
rewrite /syndromep exchange_big /= poly_def; apply/eq_bigr => i _; rewrite /fdcoor horner_poly.
rewrite (bigID (fun i => i \in supp y)) /= -[RHS]addr0 scalerDl; congr (_ + _).
  rewrite scaler_suml; apply/eq_bigr => j Hj.
  rewrite insubT // => H; congr ((y ord0 _ * _) *: _); by apply val_inj.
apply/eqP; rewrite scaler_eq0 (eq_bigr (fun=> 0)) ?big_const ?iter_addr0 ?eqxx //.
move=> j Hj; rewrite insubT // => H; rewrite (_ : Sub _ _ = j); last by apply/val_inj.
move: Hj; rewrite inE negbK => /eqP ->; by rewrite mul0r.
Qed.

Lemma size_syndromep y : size (syndromep u y t) <= t.
Proof.
rewrite /syndromep poly_def (leq_trans (size_sum _ _ _)) //; apply/bigmax_leqP => i _.
have [->|?] := eqVneq (fdcoor u y (inord i.+1)) 0.
- by rewrite scale0r size_poly0.
- by rewrite size_scale // size_polyXn.
Qed.

Lemma syndromepD x y : syndromep u (x + y) t = syndromep u x t + syndromep u y t.
Proof.
rewrite /syndromep !poly_def -big_split /=; apply/eq_bigr => i _.
by rewrite fdcoorD scalerDl.
Qed.

Lemma syndromepN x : syndromep u (- x) t = - syndromep u x t.
Proof.
rewrite /syndromep !poly_def -[RHS]mulN1r big_distrr; apply eq_bigr => /= i _.
by rewrite fdcoorN mulN1r scaleNr.
Qed.

Lemma syndromepB x y : syndromep u (x - y) t = syndromep u x t - syndromep u y t.
Proof. by rewrite syndromepD syndromepN. Qed.

Lemma syndromep0 : syndromep u 0 t = 0.
Proof. by rewrite -[in LHS](subrr 0) syndromepB subrr. Qed.

End syndrome_polynomial.

Section twisted_error_pattern.
Variables (F : fieldType) (a : F) (n : nat).

(* twisted error pattern; see [McEliece 2002] p. 243 (def 9.36), p. 259 *)
Definition twisted (y : 'rV[F]_n) := \row_(i < n) (y ``_ i * a ^+ i).

Hypothesis a_neq0 : a != 0.

Lemma supp_twisted y : supp (twisted y) = supp y.
Proof.
apply/setP => i; by rewrite inE mxE mulf_eq0 negb_or expf_neq0 // andbT inE.
Qed.

End twisted_error_pattern.

Section syndromep_prop.
Variables (F : fieldType) (n' : nat).
Let n := n'.+1.
Variable a : F.
Hypothesis a_neq0 : a != 0.
Variable (y : 'rV[F]_n).
Variable (t : nat).
Hypothesis tn : t < n.

Lemma dft_syndromep (v : 'rV[F]_n) :
  rVpoly (dft (rVexp a n) t (twisted a v)) = syndromep (rVexp a n) v t.
Proof.
have [->|a0] := eqVneq a 0.
  apply/polyP => i.
  rewrite !coef_poly.
  case: ifPn => // it.
  rewrite insubT !mxE.
  rewrite /fdcoor !horner_poly.
  apply eq_bigr => j _.
  rewrite insubT // => jt.
  rewrite !mxE (_ : Sub _ _ = j); last by apply val_inj.
  rewrite (_ : Sub _ _ = Ordinal it) //=.
  rewrite inordK //; last by rewrite (leq_trans it) // ltnW.
  rewrite inordK; last by rewrite ltnS // (leq_trans it).
  rewrite !expr0n.
  set x := (i == _).
  case/boolP : (x) => //= Hx; first by rewrite expr1n mulr1.
  rewrite expr0n.
  set z := (_ == _).
  case/boolP : (z) => //= Hz; by [rewrite !mulr1 | rewrite !mulr0].
rewrite dftE /syndromep /fdcoor.
transitivity (\sum_(i in supp v) (\sum_(j < t) (twisted a v) ``_ i * (rVexp a n) ``_ (inord j) ^+ i *: 'X^j)).
  rewrite supp_twisted //.
  apply eq_bigr => /= i _.
  rewrite scaler_sumr; apply eq_bigr => j _.
  by rewrite scalerA.
rewrite exchange_big /= poly_def; apply eq_bigr => /= i _.
rewrite horner_poly scaler_suml.
transitivity (\sum_(i0 in 'I_n) ((twisted a v) ``_ i0 * (rVexp a n) ``_ (inord i) ^+ i0) *: 'X^i).
  apply/esym.
  rewrite (bigID (fun i => (twisted a v) ``_ i != 0)) /=.
  rewrite [X in _ + X = _](eq_bigr (fun => 0)); last first.
    move=> j.
    rewrite negbK => /eqP ->; by rewrite mul0r scale0r.
  rewrite big_const iter_addr0 addr0.
  apply eq_bigl => j; by rewrite mxE inE mulf_eq0 negb_or expf_neq0 // andbT.
apply eq_bigr => /= j _.
rewrite insubT // => jn.
rewrite (_ : Sub _ _ = j); last by apply val_inj.
rewrite !mxE inordK; last by rewrite (leq_trans (ltn_ord i)) // ltnW.
rewrite inordK //; last by rewrite ltnS // (leq_trans (ltn_ord i)).
by rewrite -exprM mulnC exprM -mulrA -exprS -exprM mulnC exprM.
Qed.

End syndromep_prop.

Lemma syndromep_t0 (F : fieldType) n (a : 'rV[F]_n.+1) e : syndromep a e 0 = 0.
Proof. by rewrite /syndromep poly_def big_ord0. Qed.
