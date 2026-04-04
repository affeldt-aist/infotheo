(* dsdp_security_instantiation.v — Concrete instantiation of N-party DSDP security

   This file constructs a concrete probability space (T, P) and random variable
   definitions that satisfy ALL hypotheses of Section dsdp_concrete_n in
   dsdp_security.v, thereby yielding:

     H(VarRV | AliceTraces_n) >= log(m^n_relay) > 0

   for concrete random variables defined from a product distribution.

   Architecture:
   - T = product of finType components (relay values, Alice's value, masks,
     party-labeled encryptions)
   - P = product of uniform distributions
   - RVs = projections or derived functions
   - S is derived (not independent): S = u0*v0 + sum u_i * v_relay_i
   - E_relay and R_relay are independent uniform components from the product
   - Dk_a is constant (deterministic)
*)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap matrix lra reals.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import homomorphic_encryption.
Require Import extra_algebra extra_proba extra_entropy.
Require Import dsdp_program dsdp_entropy dsdp_security.
Require Import linear_fiber_zpq.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section dsdp_security_instantiation.

Context {R : realType}.

(* Z/pqZ parameters — same as in dsdp_security.v *)
Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Hypothesis prime_p : prime p.
Hypothesis prime_q : prime q.
Hypothesis coprime_pq : coprime p q.
Local Notation m := (p * q).
Local Notation msg := 'Z_m.

Variable n_relay : nat.
Hypothesis Hn_relay : (0 < n_relay)%N.

(* ========================================================================== *)
(* I-1: Sample Space Construction                                             *)
(* ========================================================================== *)

(* Deterministic protocol parameters (not random variables) *)
Variable u : 'I_n_relay.+2 -> msg.     (* coefficients *)
Variable dk_msg : msg.                   (* Alice's decryption key as msg *)

(* Preconditions on coefficients (needed for fiber counting) *)
Hypothesis u_last_pos : (0 < val (u ord_max))%N.
Hypothesis u_last_bound : (val (u ord_max) < minn p q)%N.

(* Encryption type: abstract finType for simplicity *)
Variable enc_msg : finType.
Hypothesis card_enc_pos : (0 < #|enc_msg|)%N.

(* Sample space components:
   1. v_relay : {ffun 'I_n_relay.+1 -> msg}   — relay private values
   2. v0 : msg                                  — Alice's private value
   3. r_masks : {ffun 'I_n_relay.+1 -> msg}    — random masks
   4. e_relay : {ffun 'I_n_relay.+1 -> enc_msg} — "encryptions" (independent uniform)
*)

(* We build T as nested binary products *)
Let T_inner := ({ffun 'I_n_relay.+1 -> msg} * msg)%type.
Let T_dsdp := (T_inner * {ffun 'I_n_relay.+1 -> msg} * {ffun 'I_n_relay.+1 -> enc_msg})%type.

(* --- Distribution construction --- *)

Let m_gt1 : (1 < m)%N.
Proof.
have Hp2: (1 < p)%N by [].
have Hq2: (1 < q)%N by [].
by rewrite (ltn_trans Hp2) // -{1}(muln1 p) ltn_pmul2l // ltnS.
Qed.

Let card_msg : #|msg| = m.
Proof. by rewrite card_ord Zp_cast. Qed.

Let card_ffun_msg : #|{ffun 'I_n_relay.+1 -> msg}| = (m ^ n_relay.+1).-1.+1.
Proof. by rewrite prednK ?expn_gt0 ?muln_gt0 ?prime_gt0 // card_ffun !card_ord Zp_cast. Qed.

(* Uniform distribution on msg *)
Let P_msg : R.-fdist msg := fdist_uniform card_msg.

(* Uniform distribution on {ffun 'I_n_relay.+1 -> msg} *)
Let P_ffun_msg : R.-fdist {ffun 'I_n_relay.+1 -> msg} := fdist_uniform card_ffun_msg.

(* Uniform distribution on {ffun 'I_n_relay.+1 -> enc_msg} *)
Let card_ffun_enc : #|{ffun 'I_n_relay.+1 -> enc_msg}| =
  (#|enc_msg| ^ n_relay.+1).-1.+1.
Proof.
rewrite card_ffun card_ord.
have Hgt0 : (0 < #|enc_msg| ^ n_relay.+1)%N by rewrite expn_gt0 card_enc_pos.
by rewrite -(prednK Hgt0).
Qed.

Let P_enc : R.-fdist {ffun 'I_n_relay.+1 -> enc_msg} := fdist_uniform card_ffun_enc.

(* Build product distribution *)
Let P_inner : R.-fdist T_inner := P_ffun_msg `x P_msg.
Let P_mid : R.-fdist (T_inner * {ffun 'I_n_relay.+1 -> msg})%type := P_inner `x P_ffun_msg.
Let P_dsdp : R.-fdist T_dsdp := P_mid `x P_enc.

(* ========================================================================== *)
(* I-1: Random Variable Definitions                                           *)
(* ========================================================================== *)

(* Projections from T_dsdp *)
Let proj_v_relay (t : T_dsdp) : {ffun 'I_n_relay.+1 -> msg} := t.1.1.1.
Let proj_v0 (t : T_dsdp) : msg := t.1.1.2.
Let proj_r_masks (t : T_dsdp) : {ffun 'I_n_relay.+1 -> msg} := t.1.2.
Let proj_e_relay (t : T_dsdp) : {ffun 'I_n_relay.+1 -> enc_msg} := t.2.

(* RV definitions *)
Definition dsdp_VarRV : {RV P_dsdp -> {ffun 'I_n_relay.+1 -> msg}} := proj_v_relay.
Definition dsdp_V0 : {RV P_dsdp -> msg} := proj_v0.

(* Deterministic RVs (constant — coefficients are not random) *)
Definition dsdp_U0 : {RV P_dsdp -> msg} := fun _ => u ord0.
Definition dsdp_Dk_a : {RV P_dsdp -> msg} := fun _ => dk_msg.

(* Per-relay random variables *)
Definition dsdp_R_relay (i : 'I_n_relay.+1) : {RV P_dsdp -> msg} :=
  fun t => (proj_r_masks t) i.

Definition dsdp_E_relay (i : 'I_n_relay.+1) : {RV P_dsdp -> enc_msg} :=
  fun t => (proj_e_relay t) i.

(* Derived RV: protocol result S = u0*v0 + sum u_i * v_relay_i *)
Definition dsdp_S : {RV P_dsdp -> msg} :=
  fun t => u ord0 * proj_v0 t +
           \sum_(i : 'I_n_relay.+1) u (lift ord0 i) * (proj_v_relay t) i.

(* Bundled RVs (as {ffun}) *)
Definition dsdp_U_relay_RV : {RV P_dsdp -> {ffun 'I_n_relay.+1 -> msg}} :=
  fun _ => [ffun i => u (lift ord0 i)].

(* Condition RV: (V0, U0, U_relay_ffun, S) *)
Let CondT_n := (msg * msg * {ffun 'I_n_relay.+1 -> msg} * msg)%type.
Definition dsdp_CondRV : {RV P_dsdp -> CondT_n} :=
  fun t => (dsdp_V0 t, dsdp_U0 t, dsdp_U_relay_RV t, dsdp_S t).

(* Input RV: (V0, U0, U_relay_ffun) *)
Let InputT_n := (msg * msg * {ffun 'I_n_relay.+1 -> msg})%type.
Definition dsdp_InputRV : {RV P_dsdp -> InputT_n} :=
  fun t => (dsdp_V0 t, dsdp_U0 t, dsdp_U_relay_RV t).

(* Local fiber and projection functions matching what dsdp_centropy_uniform_n
   expects after section close (inlined Let bindings) *)
Let fiber_fn (cond : CondT_n) : {set {ffun 'I_n_relay.+1 -> msg}} :=
  let '(v0, u0, u_rel, s) := cond in
  @linear_fiber_nd p_minus_2 q_minus_2 n_relay u_rel (s - u0 * v0).

Let proj_input (cond : CondT_n) : InputT_n :=
  let '(v0, u0, u_rel, _) := cond in (v0, u0, u_rel).

(* ========================================================================== *)
(* I-2: Hypothesis Verification                                               *)
(* ========================================================================== *)

(* --- Fiber constraint (trivial — S is derived) --- *)
Lemma dsdp_constraint_fiber :
  forall t, dsdp_VarRV t \in fiber_fn (dsdp_CondRV t).
Proof.
move=> t.
rewrite /dsdp_VarRV /fiber_fn /dsdp_CondRV /dsdp_V0 /dsdp_U0
        /dsdp_U_relay_RV /dsdp_S.
rewrite inE.
under eq_bigr do rewrite ffunE.
by apply/eqP; ring.
Qed.

(* --- InputRV projection (trivial — by definition) --- *)
Lemma dsdp_InputRV_proj :
  forall t, dsdp_InputRV t = proj_input (dsdp_CondRV t).
Proof. by []. Qed.

(* --- VarRV uniformity --- *)
Lemma dsdp_VarRV_uniform :
  `p_ dsdp_VarRV = fdist_uniform card_ffun_msg.
Proof.
change (fdist_uniform card_ffun_msg) with P_ffun_msg.
have -> : @dist_of_RV R _ P_dsdp _ dsdp_VarRV = P_dsdp`1`1`1.
  rewrite /dist_of_RV /dsdp_VarRV /proj_v_relay /fdist_fst.
  rewrite fdistmap_comp fdistmap_comp.
  - by [].
  - by rewrite /P_dsdp /P_mid /P_inner fdist_prod1 fdist_prod1 fdist_prod1.
Qed.

(* Helper: Pr on P_dsdp of a set depending only on t.1.1 = Pr on P_inner *)
Let Pr_dsdp_inner (E : {set T_inner}) :
  Pr P_dsdp [set t : T_dsdp | t.1.1 \in E] = Pr P_inner E.
Proof.
rewrite /Pr (eq_bigl (fun t : T_dsdp => t.1.1 \in E)); last by move=> t; rewrite inE.
rewrite (eq_bigr (fun t : T_dsdp => P_dsdp (t.1, t.2))); last by case.
rewrite (eq_bigl (fun t : T_dsdp => (t.1.1 \in E) && true));
  last by move=> t; rewrite andbT.
rewrite -[LHS](pair_big (fun a => a.1 \in E) xpredT
  (fun x1 x2 => P_dsdp (x1, x2))).
under eq_bigr do (under eq_bigr do rewrite /P_dsdp fdist_prodE /=).
under eq_bigr do rewrite -big_distrr /= FDist.f1 GRing.mulr1.
rewrite (eq_bigr (fun t => P_mid (t.1, t.2))); last by case.
rewrite (eq_bigl (fun t => (t.1 \in E) && true)); last by move=> t; rewrite andbT.
rewrite -[LHS](pair_big (fun a => a \in E) xpredT
  (fun x1 x2 => P_mid (x1, x2))).
under eq_bigr do (under eq_bigr do rewrite /P_mid fdist_prodE /=).
by under eq_bigr do rewrite -big_distrr /= FDist.f1 GRing.mulr1.
Qed.

(* Helper: two RVs depending on different product components are independent *)
Let prod3_inde_fst_snd (C D : eqType)
    (f : msg -> C) (g : {ffun 'I_n_relay.+1 -> msg} -> D) :
  P_dsdp |= (fun t : T_dsdp => f t.1.1.2) _|_ (fun t : T_dsdp => g t.1.1.1).
Proof.
apply/inde_RV_events => x y.
set E1 := finset (preim _ (pred1 x)).
set E2 := finset (preim _ (pred1 y)).
rewrite /inde_events.
set Sf := finset (preim f (pred1 x)).
set Sg := finset (preim g (pred1 y)).
(* Convert all three Pr's from P_dsdp to P_inner *)
have HE1 : Pr P_dsdp E1 = Pr P_inner (T`* Sf).
  rewrite -Pr_dsdp_inner. congr (Pr _ _).
  by apply/setP => -[[[vr v0] rm] enc]; rewrite !inE /=.
have HE2 : Pr P_dsdp E2 = Pr P_inner (Sg `*T).
  rewrite -Pr_dsdp_inner. congr (Pr _ _).
  by apply/setP => -[[[vr v0] rm] enc]; rewrite !inE /=.
have HE12 : Pr P_dsdp (E1 :&: E2) = Pr P_inner ((Sg `*T) :&: (T`* Sf)).
  rewrite -Pr_dsdp_inner. congr (Pr _ _).
  by apply/setP => -[[[vr v0] rm] enc]; rewrite !inE /= andbC.
rewrite HE12 HE1 HE2.
set X := Pr P_inner (T`* Sf). set Y := Pr P_inner (Sg `*T).
by rewrite /P_inner Pr_fdist_prod GRing.mulrC.
Qed.

(* --- VarRV independence from inputs --- *)
Lemma dsdp_VarRV_indep_inputs :
  P_dsdp |= dsdp_InputRV _|_ dsdp_VarRV.
Proof.
exact: (prod3_inde_fst_snd
  (fun v0 => (v0, u ord0, [ffun i => u (lift ord0 i)]))
  (fun vr => vr)).
Qed.

(* --- joint_eq_input_n (Hard — follows 3-party pattern) --- *)
Lemma dsdp_joint_eq_input :
  forall (cond : CondT_n) (var : {ffun 'I_n_relay.+1 -> msg}),
    var \in fiber_fn cond ->
    `Pr[[%dsdp_VarRV, dsdp_CondRV] = (var, cond)] =
    `Pr[[%dsdp_VarRV, dsdp_InputRV] = (var, proj_input cond)].
Proof.
move=> [[[[v1 u1] u_rel] s]] var Hin_fiber /=.
move=> Hfib; rewrite !pfwd1E; congr (Pr P_dsdp _).
apply/setP => t0; rewrite !inE /= !xpair_eqE.
apply/idP/idP => H.
- (* LHS -> RHS: drop S *)
  move/and3P: H => [Hvar Hmid Hs].
  by rewrite Hvar Hmid.
- (* RHS -> LHS: recover S from constraint *)
  move/and3P: H => [Hvar Hmid Hurel].
  rewrite Hvar Hmid Hurel /=.
  move/eqP: Hvar => Hvar_eq.
  move/andP: Hmid => [/eqP Hv0_eq /eqP Hu0_eq].
  move/eqP: Hurel => Hurel_eq.
  rewrite /dsdp_S /dsdp_V0 /dsdp_VarRV /dsdp_U0 /dsdp_U_relay_RV in Hvar_eq Hv0_eq Hu0_eq Hurel_eq *.
  rewrite Hvar_eq Hv0_eq Hu0_eq.
  have -> : \sum_(i < n_relay.+1) u (lift ord0 i) * Hin_fiber i =
            \sum_(i < n_relay.+1) s i * Hin_fiber i.
    apply eq_bigr => i _. by rewrite -Hurel_eq ffunE.
  move: Hfib; rewrite inE => /eqP Hfib_eq.
  by apply/eqP; rewrite Hfib_eq; ring.
Qed.

(* ========================================================================== *)
(* I-2: u_of_cond preconditions                                              *)
(* ========================================================================== *)

Lemma dsdp_u_of_cond_pos (t : T_dsdp) :
  (0 < val ((fun '(_, _, u_rel, _) => u_rel) (dsdp_CondRV t) ord_max))%N.
Proof.
rewrite /dsdp_CondRV /dsdp_U_relay_RV ffunE.
suff -> : lift ord0 (@ord_max n_relay) = @ord_max n_relay.+1
  by exact: u_last_pos.
by apply: val_inj; rewrite /= /bump leq0n add1n.
Qed.

Lemma dsdp_u_of_cond_bound (t : T_dsdp) :
  (val ((fun '(_, _, u_rel, _) => u_rel) (dsdp_CondRV t) ord_max) < minn p q)%N.
Proof.
rewrite /dsdp_CondRV /dsdp_U_relay_RV ffunE.
suff -> : lift ord0 (@ord_max n_relay) = @ord_max n_relay.+1
  by exact: u_last_bound.
by apply: val_inj; rewrite /= /bump leq0n add1n.
Qed.

(* ========================================================================== *)
(* I-3: Entropy Instantiation                                                 *)
(* ========================================================================== *)

Lemma dsdp_centropy_n_concrete :
  `H(dsdp_VarRV | dsdp_CondRV) = log ((m ^ n_relay)%:R : R).
Proof.
apply (@dsdp_centropy_uniform_n R p_minus_2 q_minus_2
          prime_p prime_q n_relay T_dsdp P_dsdp
          dsdp_VarRV dsdp_CondRV dsdp_InputRV).
- exact: dsdp_constraint_fiber.
- exact: dsdp_InputRV_proj.
- rewrite dsdp_VarRV_uniform; congr (fdist_uniform _); exact: eq_irrelevance.
- exact: dsdp_VarRV_indep_inputs.
- exact: dsdp_joint_eq_input.
- exact: dsdp_u_of_cond_pos.
- exact: dsdp_u_of_cond_bound.
Qed.

(* ========================================================================== *)
(* I-2b: Independence hypotheses for trace_eavesdropper_security_n            *)
(* ========================================================================== *)

(* Dk_a is constant => independent of everything *)
Lemma dsdp_Dk_a_indep_all (B : finType) (Y : {RV P_dsdp -> B}) :
  P_dsdp |= dsdp_Dk_a _|_ Y.
Proof.
apply/inde_RVP => E F.
rewrite /inde_events /dsdp_Dk_a /pr_in.
unlock.
rewrite (_ : [% fun=> dk_msg, Y] @^-1: (E `* F)%set =
  if dk_msg \in E then Y @^-1: F else set0); last first.
  apply/setP => t; rewrite !inE /=.
  case: ifPn => HdkE; by rewrite ?inE ?HdkE.
rewrite (_ : (fun=> dk_msg) @^-1: E =
  if dk_msg \in E then [set: T_dsdp] else set0); last first.
  apply/setP => t; rewrite !inE /=.
  case: ifPn => HdkE; by rewrite ?inE.
case: ifPn => HdkE.
- by rewrite Pr_setT GRing.mul1r.
- by rewrite Pr_set0 GRing.mul0r.
Qed.

(* Helper: Pr on P_dsdp of a set depending only on t.1 = Pr on P_mid *)
Let Pr_dsdp_mid (E : {set (T_inner * {ffun 'I_n_relay.+1 -> msg})%type}) :
  Pr P_dsdp [set t : T_dsdp | t.1 \in E] = Pr P_mid E.
Proof.
rewrite /Pr (eq_bigl (fun t : T_dsdp => t.1 \in E)); last by move=> t; rewrite inE.
rewrite (eq_bigr (fun t : T_dsdp => P_mid t.1 * P_enc t.2)); last first.
  by move=> t _; rewrite /P_dsdp fdist_prodE.
rewrite (eq_bigl (fun t : T_dsdp => (t.1 \in E) && true));
  last by move=> t; rewrite andbT.
rewrite -[LHS](pair_big (fun a => a \in E) xpredT
  (fun x1 x2 => P_mid x1 * P_enc x2)) /=.
by under eq_bigr do rewrite -big_distrr /= FDist.f1 GRing.mulr1.
Qed.

(* Independence between f(t.1.1) and g(t.1.2) within P_dsdp,
   using P_mid = P_inner `x P_ffun_msg *)
Let prod_inde_mid (C D : eqType)
    (f : T_inner -> C) (g : {ffun 'I_n_relay.+1 -> msg} -> D) :
  P_dsdp |= (fun t : T_dsdp => f t.1.1) _|_ (fun t : T_dsdp => g t.1.2).
Proof.
apply/inde_RV_events => x y.
rewrite /inde_events.
set EA := finset (preim _ (pred1 x)).
set EB := finset (preim _ (pred1 y)).
have HEA : EA = (finset (preim (fun mid : T_inner * {ffun 'I_n_relay.+1 -> msg} =>
  f mid.1) (pred1 x))) `*T.
  by apply/setP => -[mid enc]; rewrite !inE /=.
have HEB : EB = (T`* (finset (preim g (pred1 y)))) `*T.
  by apply/setP => -[mid enc]; rewrite !inE /=.
have HEAB : EA :&: EB = ((finset (preim (fun mid : T_inner * {ffun 'I_n_relay.+1 -> msg} =>
  f mid.1) (pred1 x))) :&: (T`* finset (preim g (pred1 y)))) `*T.
  rewrite HEA HEB.
  by apply/setP => -[mid enc]; rewrite !inE /=.
rewrite HEAB HEA HEB !Pr_dsdp_mid.
rewrite (_ : finset (preim (fun mid : T_inner * {ffun 'I_n_relay.+1 -> msg} =>
  f mid.1) (pred1 x)) = (finset (preim f (pred1 x))) `*T); last first.
  by apply/setP => -[a b]; rewrite !inE.
by rewrite /P_mid -Pr_fdist_prod.
Qed.

(* R_relay bundled is independent of [%VarRV, CondRV] — they depend on
   different product components (t.1.2 vs t.1.1) *)
Lemma dsdp_R_relay_RV_indep :
  P_dsdp |= (fun t => [ffun i => dsdp_R_relay i t]) _|_ [%dsdp_VarRV, dsdp_CondRV].
Proof.
apply/inde_RV_sym.
rewrite (_ : [% dsdp_VarRV, dsdp_CondRV] = (fun t : T_dsdp =>
  (t.1.1.1, (t.1.1.2, u ord0, [ffun i => u (lift ord0 i)],
    u ord0 * t.1.1.2 + \sum_(i < n_relay.+1) u (lift ord0 i) * t.1.1.1 i))));
  last by apply: funext.
rewrite (_ : (fun t : T_dsdp => [ffun i => dsdp_R_relay i t]) =
  (fun t : T_dsdp => [ffun i => t.1.2 i]));
  last by apply: funext => t; apply/ffunP => i; rewrite !ffunE.
exact: (prod_inde_mid
  (fun inner : T_inner => (inner.1, (inner.2, u ord0, [ffun i => u (lift ord0 i)],
    u ord0 * inner.2 + \sum_(i < n_relay.+1) u (lift ord0 i) * inner.1 i)))
  (fun masks : {ffun 'I_n_relay.+1 -> msg} => [ffun i => masks i])).
Qed.

(* E_relay bundled is independent of [%VarRV, DecView] — E_relay depends on
   t.2 while all others depend on t.1 *)
Lemma dsdp_E_relay_RV_indep :
  P_dsdp |= (fun t => [ffun i => dsdp_E_relay i t])
    _|_ [%dsdp_VarRV, [%dsdp_Dk_a,
            (fun t => [ffun i => dsdp_R_relay i t]), dsdp_CondRV]].
Proof.
apply/inde_RV_sym.
apply/inde_RV_events => x y.
set E1 := finset (preim _ (pred1 x)).
set E2 := finset (preim _ (pred1 y)).
rewrite /inde_events.
have HE1 : E1 = (finset (preim (fun mid : T_inner * {ffun 'I_n_relay.+1 -> msg} =>
  (dsdp_VarRV (mid, y), (dsdp_Dk_a (mid, y), [ffun i => dsdp_R_relay i (mid, y)],
    dsdp_CondRV (mid, y)))) (pred1 x))) `*T.
  apply/setP => -[mid enc]; rewrite !inE /=.
  congr (_ == _).
  rewrite /dsdp_VarRV /proj_v_relay /dsdp_Dk_a /dsdp_R_relay /proj_r_masks
          /dsdp_CondRV /dsdp_V0 /proj_v0 /dsdp_U0 /dsdp_U_relay_RV /dsdp_S /=.
have HE2 : E2 = T`* [set y].
  apply/setP => -[mid enc]; rewrite !inE /=.
  congr (_ == _).
  by apply/ffunP => i; rewrite ffunE /dsdp_E_relay /proj_e_relay.
rewrite HE1 HE2.
exact: Pr_fdist_prod.
Qed.

(* ========================================================================== *)
(* I-4: Assembly — instantiate trace_eavesdropper_security_n                  *)
(* ========================================================================== *)

Theorem dsdp_security_instantiation :
  let AliceTraces := (fun '(e_relay, (dk, _, cond)) => (e_relay, dk, cond))
    `o [% (fun t => [ffun i => dsdp_E_relay i t]),
         [% dsdp_Dk_a,
            (fun t => [ffun i => dsdp_R_relay i t]),
            dsdp_CondRV]] in
  `H(dsdp_VarRV | AliceTraces) >= log ((m ^ n_relay)%:R : R) /\
  `H(dsdp_VarRV | AliceTraces) > 0.
Proof.
apply: (@trace_eavesdropper_security_n R T_dsdp P_dsdp
          p_minus_2 q_minus_2 n_relay Hn_relay
          dsdp_Dk_a dsdp_VarRV dsdp_R_relay
          enc_msg dsdp_E_relay dsdp_CondRV
          dsdp_centropy_n_concrete
          dsdp_Dk_a_indep_all
          dsdp_R_relay_RV_indep
          dsdp_E_relay_RV_indep).
Qed.

End dsdp_security_instantiation.
