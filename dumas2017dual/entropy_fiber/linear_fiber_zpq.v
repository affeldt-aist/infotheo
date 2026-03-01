From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg matrix.
From mathcomp Require Import ring boolp finmap lra.
From mathcomp Require Import mathcomp_extra.
From robot Require Import euclidean.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid.
Require Import extra_algebra extra_proba extra_entropy entropy_fiber.
Require Import rouche_capelli.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*  Linear fiber over composite modulus Z/pqZ via CRT                         *)
(*                                                                            *)
(*  Main result: linear_fiber_2d_card                                         *)
(*    |{(v2,v3) | u2*v2 + u3*v3 = target}| = m  (when 0 < u3 < min(p,q))    *)
(*                                                                            *)
(*  Approach: CRT decomposes Z/pqZ ≅ F_p × F_q, apply rouche_capelli per     *)
(*  component, then combine via CRT bijection.                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.

Section fiber_2d.

Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Hypothesis prime_p : prime p.
Hypothesis prime_q : prime q.
Hypothesis coprime_pq : coprime p q.
Local Notation m := (p * q).
Local Notation msg := 'Z_m.

Let m_gt1 : (1 < m)%N.
Proof.
by rewrite (leq_trans (prime_gt1 prime_p)) // leq_pmulr // prime_gt0.
Qed.

Let p_gt1 : (1 < p)%N := prime_gt1 prime_p.
Let q_gt1 : (1 < q)%N := prime_gt1 prime_q.

(* CRT projections: Z/(pq)Z → F_p and Z/(pq)Z → F_q *)
Definition proj_Fp (x : msg) : 'F_p := inZp (val x).
Definition proj_Fq (x : msg) : 'F_q := inZp (val x).

Lemma proj_Fp_add (x y : msg) : proj_Fp (x + y) = (proj_Fp x + proj_Fp y).
Proof.
by apply/eqP; rewrite eqE /= !Fp_cast //
   modn_dvdm ?modnDm // Zp_cast // dvdn_mulr.
Qed.

Lemma proj_Fp_mul (x y : msg) : proj_Fp (x * y) = (proj_Fp x * proj_Fp y).
Proof.
by apply/eqP; rewrite eqE /= !Fp_cast //
   modn_dvdm ?modnMm // Zp_cast // dvdn_mulr.
Qed.

Lemma proj_Fq_add (x y : msg) : proj_Fq (x + y) = (proj_Fq x + proj_Fq y).
Proof.
by apply/eqP; rewrite eqE /= !Fp_cast //
   modn_dvdm ?modnDm // Zp_cast // dvdn_mull.
Qed.

Lemma proj_Fq_mul (x y : msg) : proj_Fq (x * y) = (proj_Fq x * proj_Fq y).
Proof.
by apply/eqP; rewrite eqE /= !Fp_cast //
   modn_dvdm ?modnMm // Zp_cast // dvdn_mull.
Qed.

(* Field fibers and their cardinality via rouche_capelli *)
Definition fiber_Fp (u2 u3 target : 'F_p) : {set 'F_p * 'F_p} :=
  [set vv : 'F_p * 'F_p | u2 * vv.1 + u3 * vv.2 == target].

Definition fiber_Fq (u2 u3 target : 'F_q) : {set 'F_q * 'F_q} :=
  [set vv : 'F_q * 'F_q | u2 * vv.1 + u3 * vv.2 == target].

Lemma fiber_Fp_card (u2 u3 target : 'F_p) :
  u3 != 0 -> #|fiber_Fp u2 u3 target| = p.
Proof. by move=> Hu3; rewrite /fiber_Fp count_affine_solutions_rank1 // card_Fp. Qed.

Lemma fiber_Fq_card (u2 u3 target : 'F_q) :
  u3 != 0 -> #|fiber_Fq u2 u3 target| = q.
Proof. by move=> Hu3; rewrite /fiber_Fq count_affine_solutions_rank1 // card_Fp. Qed.

(* Modulus conversion helpers: these are all trivial but necessary because   *)
(* 'F_p = 'I_(Zp_trunc (pdiv p)).+2, so rewriting (Zp_trunc ...).+2 to p  *)
(* fails when 'F_p variables are in scope (dependent type error).           *)
(* Factoring them here avoids repeating type annotations at each use site.  *)
Let p_eq : (Zp_trunc (pdiv p)).+2 = p.
Proof. by rewrite Fp_cast // prime_gt1. Qed.

Let q_eq : (Zp_trunc (pdiv q)).+2 = q.
Proof. by rewrite Fp_cast // prime_gt1. Qed.

Let Zp_modn_p (n : nat) : (n %% (Zp_trunc (pdiv p)).+2 = n %% p)%N.
Proof. by rewrite p_eq. Qed.

Let Zp_modn_q (n : nat) : (n %% (Zp_trunc (pdiv q)).+2 = n %% q)%N.
Proof. by rewrite q_eq. Qed.

Let Fp_bound_gen (n : nat) : (n < (Zp_trunc (pdiv p)).+2)%N -> (n < p)%N.
Proof. by rewrite p_eq. Qed.

Let Fq_bound_gen (n : nat) : (n < (Zp_trunc (pdiv q)).+2)%N -> (n < q)%N.
Proof. by rewrite q_eq. Qed.

Lemma val_Fp_lt_p (x : 'F_p) : (val x < p)%N.
Proof. exact: Fp_bound_gen (ltn_ord x). Qed.

Lemma val_Fq_lt_q (x : 'F_q) : (val x < q)%N.
Proof. exact: Fq_bound_gen (ltn_ord x). Qed.

Let Zm_modn_m (n : nat) : (n %% (Zp_trunc m).+2 = n %% m)%N.
Proof. by rewrite Zp_cast. Qed.

Let Zm_bound_gen (n : nat) : (n < (Zp_trunc m).+2)%N -> (n < m)%N.
Proof. by rewrite Zp_cast. Qed.

Lemma val_msg_lt_m (x : msg) : (val x < m)%N.
Proof. exact: Zm_bound_gen (ltn_ord x). Qed.

(* CRT reconstruction: F_p × F_q → Z/(pq)Z *)
Definition crt_elem (xp : 'F_p) (xq : 'F_q) : msg :=
  inZp (chinese p q (val xp) (val xq)).

Definition crt_pair (pp : 'F_p * 'F_p) (qq : 'F_q * 'F_q) : msg * msg :=
  (crt_elem pp.1 qq.1, crt_elem pp.2 qq.2).

Lemma chinese_proj_p (vp vq : nat) :
  (vp < p)%N -> (chinese p q vp vq %% p = vp)%N.
Proof. by move=> Hvp; rewrite chinese_modl // modn_small. Qed.

Lemma chinese_proj_q (vp vq : nat) :
  (vq < q)%N -> (chinese p q vp vq %% q = vq)%N.
Proof. by move=> Hvq; rewrite chinese_modr // modn_small. Qed.

(* Projection-reconstruction round-trips *)
Lemma proj_Fp_crt (xp : 'F_p) (xq : 'F_q) : proj_Fp (crt_elem xp xq) = xp.
Proof.
apply/val_inj; rewrite /proj_Fp /crt_elem /=.
rewrite modn_dvdm; last by rewrite p_eq Zp_cast // dvdn_mulr.
by rewrite Zp_modn_p chinese_proj_p // val_Fp_lt_p.
Qed.

Lemma proj_Fq_crt (xp : 'F_p) (xq : 'F_q) : proj_Fq (crt_elem xp xq) = xq.
Proof.
apply/val_inj; rewrite /proj_Fq /crt_elem /=.
rewrite modn_dvdm; last by rewrite q_eq Zp_cast // dvdn_mull.
by rewrite Zp_modn_q chinese_proj_q // val_Fq_lt_q.
Qed.

Lemma crt_proj_id (x : msg) : crt_elem (proj_Fp x) (proj_Fq x) = x.
Proof.
apply/val_inj; rewrite /crt_elem /proj_Fp /proj_Fq /=.
rewrite !Zp_modn_p !Zp_modn_q Zm_modn_m.
by apply/eqP; rewrite eq_sym -chinese_mod // modn_small // val_msg_lt_m.
Qed.

(* CRT component extraction from modular equality *)
Lemma chinese_mod_inj_p (xp xp' : 'F_p) (xq xq' : 'F_q) :
  chinese p q (val xp) (val xq) = chinese p q (val xp') (val xq') %[mod m] ->
  xp = xp'.
Proof.
move=> /eqP Hmod; apply/val_inj.
have Hl := chinese_modl coprime_pq (val xp) (val xq).
have Hr := chinese_modl coprime_pq (val xp') (val xq').
have Hp: (chinese p q (val xp) (val xq) %% p =
          chinese p q (val xp') (val xq') %% p)%N.
  have: (chinese p q (val xp) (val xq) %% m %% p =
         chinese p q (val xp') (val xq') %% m %% p)%N by rewrite (eqP Hmod).
  by rewrite !modn_dvdm // dvdn_mulr.
move/eqP: Hl; move/eqP: Hr; rewrite -{}Hp => /eqP Hr /eqP Hl.
by rewrite -(modn_small (val_Fp_lt_p xp)) -Hl Hr modn_small // val_Fp_lt_p.
Qed.

Lemma chinese_mod_inj_q (xp xp' : 'F_p) (xq xq' : 'F_q) :
  chinese p q (val xp) (val xq) = chinese p q (val xp') (val xq') %[mod m] ->
  xq = xq'.
Proof.
move=> /eqP Hmod; apply/val_inj.
have Hl := chinese_modr coprime_pq (val xp) (val xq).
have Hr := chinese_modr coprime_pq (val xp') (val xq').
have Hq: (chinese p q (val xp) (val xq) %% q =
          chinese p q (val xp') (val xq') %% q)%N.
  have: (chinese p q (val xp) (val xq) %% m %% q =
         chinese p q (val xp') (val xq') %% m %% q)%N by rewrite (eqP Hmod).
  by rewrite !modn_dvdm // dvdn_mull.
move/eqP: Hl; move/eqP: Hr; rewrite -{}Hq => /eqP Hr /eqP Hl.
by rewrite -(modn_small (val_Fq_lt_q xq)) -Hl Hr modn_small // val_Fq_lt_q.
Qed.

Let eqmod_Zp_m (a b : nat) :
  a = b %[mod (Zp_trunc m).+2] -> a = b %[mod m].
Proof. by rewrite Zp_cast. Qed.

(* crt_pair is injective *)
Lemma crt_pair_inj (pp pp' : 'F_p * 'F_p) (qq qq' : 'F_q * 'F_q) :
  crt_pair pp qq = crt_pair pp' qq' -> pp = pp' /\ qq = qq'.
Proof.
rewrite /crt_pair.
(* Pattern matching on pair equality gives modular equalities on chinese values *)
case => H1 H2.
(* H1: chinese p q pp.1 qq.1 = chinese p q pp'.1 qq'.1 %[mod (Zp_trunc m).+2] *)
(* H2: chinese p q pp.2 qq.2 = chinese p q pp'.2 qq'.2 %[mod (Zp_trunc m).+2] *)
(* Convert (Zp_trunc m).+2 to m using the helper *)
have H1' := eqmod_Zp_m H1.
have H2' := eqmod_Zp_m H2.
(* Extract component equalities *)
have Hp1 := chinese_mod_inj_p H1'.
have Hp2 := chinese_mod_inj_p H2'.
have Hq1 := chinese_mod_inj_q H1'.
have Hq2 := chinese_mod_inj_q H2'.
(* Reconstruct pair equalities *)
split.
- by rewrite (surjective_pairing pp) (surjective_pairing pp') Hp1 Hp2.
- by rewrite (surjective_pairing qq) (surjective_pairing qq') Hq1 Hq2.
Qed.

(* Constraint correspondence between Z_m and field components *)
Lemma constraint_proj (u2 u3 target : msg) (vv : msg * msg) :
  u2 * vv.1 + u3 * vv.2 = target ->
  (proj_Fp u2 * proj_Fp vv.1 + proj_Fp u3 * proj_Fp vv.2 = proj_Fp target) /\
  (proj_Fq u2 * proj_Fq vv.1 + proj_Fq u3 * proj_Fq vv.2 = proj_Fq target).
Proof.
move=> Hc; split.
- by rewrite -!proj_Fp_mul -proj_Fp_add Hc.
- by rewrite -!proj_Fq_mul -proj_Fq_add Hc.
Qed.

Lemma constraint_crt (u2 u3 target : msg) (pp : 'F_p * 'F_p) (qq : 'F_q * 'F_q) :
  proj_Fp u2 * pp.1 + proj_Fp u3 * pp.2 = proj_Fp target ->
  proj_Fq u2 * qq.1 + proj_Fq u3 * qq.2 = proj_Fq target ->
  u2 * (crt_pair pp qq).1 + u3 * (crt_pair pp qq).2 = target.
Proof.
move=> Hp Hq.
have HprojFp: proj_Fp (u2 * (crt_pair pp qq).1 + u3 * (crt_pair pp qq).2) =
              proj_Fp target.
  by rewrite proj_Fp_add !proj_Fp_mul /crt_pair /= !proj_Fp_crt.
have HprojFq: proj_Fq (u2 * (crt_pair pp qq).1 + u3 * (crt_pair pp qq).2) =
              proj_Fq target.
  by rewrite proj_Fq_add !proj_Fq_mul /crt_pair /= !proj_Fq_crt.
by rewrite -(crt_proj_id target)
   -(crt_proj_id (u2 * _ + u3 * _)) HprojFp HprojFq.
Qed.

(* 2D fiber: solutions to u2*v2 + u3*v3 = target over Z_m *)
Definition linear_fiber_2d (u2 u3 target : msg) : {set msg * msg} :=
  [set vv : msg * msg | (u2 * vv.1 + u3 * vv.2 == target)%R].

(* Nonzero projection helpers *)
Lemma proj_Fp_neq0 (u3 : msg) :
  (0 < u3)%N -> (val u3 < p)%N -> proj_Fp u3 != 0%R.
Proof.
move=> Hu3_pos Hu3_lt_p; rewrite /proj_Fp; apply/eqP => Heq.
have /val_eqP /= := Heq; rewrite Fp_cast // modn_small // => /eqP Heq'.
by rewrite Heq' in Hu3_pos.
Qed.

Lemma proj_Fq_neq0 (u3 : msg) :
  (0 < u3)%N -> (val u3 < q)%N -> proj_Fq u3 != 0%R.
Proof.
move=> Hu3_pos Hu3_lt_q; rewrite /proj_Fq; apply/eqP => Heq.
have /val_eqP /= := Heq; rewrite Fp_cast // modn_small // => /eqP Heq'.
by rewrite Heq' in Hu3_pos.
Qed.

(* CRT projection on pairs *)
Definition crt_proj_pair (vv : msg * msg) : ('F_p * 'F_p) * ('F_q * 'F_q) :=
  ((proj_Fp vv.1, proj_Fp vv.2), (proj_Fq vv.1, proj_Fq vv.2)).

Lemma crt_proj_pair_inj : injective crt_proj_pair.
Proof.
move=> [v1 v2] [v1' v2'] /=; rewrite /crt_proj_pair /= => H.
have /= Hp1 := congr1 (fun x => x.1.1) H.
have /= Hp2 := congr1 (fun x => x.1.2) H.
have /= Hq1 := congr1 (fun x => x.2.1) H.
have /= Hq2 := congr1 (fun x => x.2.2) H.
congr pair.
- by rewrite -(crt_proj_id v1) -(crt_proj_id v1') Hp1 Hq1.
- by rewrite -(crt_proj_id v2) -(crt_proj_id v2') Hp2 Hq2.
Qed.

Lemma crt_proj_pair_fiber (u2 u3 target : msg) (vv : msg * msg) :
  vv \in linear_fiber_2d u2 u3 target ->
  crt_proj_pair vv \in
    setX (fiber_Fp (proj_Fp u2) (proj_Fp u3) (proj_Fp target))
         (fiber_Fq (proj_Fq u2) (proj_Fq u3) (proj_Fq target)).
Proof.
rewrite inE => /eqP Hconstr; rewrite inE; apply/andP; split; rewrite inE;
  apply/eqP; rewrite /crt_proj_pair /=.
- by rewrite -!proj_Fp_mul -proj_Fp_add Hconstr.
- by rewrite -!proj_Fq_mul -proj_Fq_add Hconstr.
Qed.

Lemma crt_pair_fiber (u2 u3 target : msg) (pp : 'F_p * 'F_p) (qq : 'F_q * 'F_q) :
  pp \in fiber_Fp (proj_Fp u2) (proj_Fp u3) (proj_Fp target) ->
  qq \in fiber_Fq (proj_Fq u2) (proj_Fq u3) (proj_Fq target) ->
  crt_pair pp qq \in linear_fiber_2d u2 u3 target.
Proof.
by rewrite !inE => /eqP Hp /eqP Hq; apply/eqP; exact: constraint_crt Hp Hq.
Qed.

Lemma crt_proj_pair_surj (u2 u3 target : msg)
    (ppqq : ('F_p * 'F_p) * ('F_q * 'F_q)) :
  ppqq \in setX (fiber_Fp (proj_Fp u2) (proj_Fp u3) (proj_Fp target))
                (fiber_Fq (proj_Fq u2) (proj_Fq u3) (proj_Fq target)) ->
  exists vv, vv \in linear_fiber_2d u2 u3 target /\ crt_proj_pair vv = ppqq.
Proof.
case: ppqq => pp qq; rewrite inE => /andP [/= Hpp /= Hqq].
exists (crt_pair pp qq); split; first exact (crt_pair_fiber Hpp Hqq).
by rewrite /crt_proj_pair /crt_pair /= !proj_Fp_crt !proj_Fq_crt
   -!surjective_pairing.
Qed.

(* Main result: 2D fiber cardinality = m via CRT *)
Lemma linear_fiber_2d_card (u2 u3 target : msg) :
  (0 < u3)%N -> (u3 < minn p q)%N ->
  #|linear_fiber_2d u2 u3 target| = m.
Proof.
move=> Hu3_pos Hu3_lt.
have Hu3_lt_p: (val u3 < p)%N by apply: (leq_trans Hu3_lt); apply: geq_minl.
have Hu3_lt_q: (val u3 < q)%N by apply: (leq_trans Hu3_lt); apply: geq_minr.
have Hcard_Fp := fiber_Fp_card (proj_Fp u2) (proj_Fp target)
                                (proj_Fp_neq0 Hu3_pos Hu3_lt_p).
have Hcard_Fq := fiber_Fq_card (proj_Fq u2) (proj_Fq target)
                                (proj_Fq_neq0 Hu3_pos Hu3_lt_q).
set Fp_fib := fiber_Fp (proj_Fp u2) (proj_Fp u3) (proj_Fp target).
set Fq_fib := fiber_Fq (proj_Fq u2) (proj_Fq u3) (proj_Fq target).
have Himg: [set crt_proj_pair vv | vv in linear_fiber_2d u2 u3 target] =
           setX Fp_fib Fq_fib.
  apply/setP => ppqq; apply/imsetP/idP.
  + by move=> [vv Hvv ->]; exact: crt_proj_pair_fiber.
  + by move=> Hppqq; have [vv [Hvv Heq]] := crt_proj_pair_surj Hppqq;
       exists vv.
rewrite -(card_in_imset (D := linear_fiber_2d u2 u3 target)
                        (f := crt_proj_pair)).
  by rewrite Himg cardsX Hcard_Fp Hcard_Fq.
by move=> x y _ _; apply: crt_proj_pair_inj.
Qed.

End fiber_2d.

(******************************************************************************)
(*  N-dimensional linear fiber over composite modulus Z/pqZ                   *)
(*                                                                            *)
(*  Main result: linear_fiber_nd_card                                         *)
(*    |{v : 'I_{n+1} -> Z_m | \sum u_i * v_i = target}| = m^n               *)
(*    (when u_{last} is coprime to m, i.e., 0 < u_last < min(p,q))           *)
(*                                                                            *)
(*  Approach: Direct bijection via unit inverse. Since u_last is a unit in    *)
(*  Z_m, for any choice of the first n variables, the last variable is        *)
(*  uniquely determined by the constraint. This gives a bijection between     *)
(*  Z_m^n (the free variables) and the fiber (n+1 constrained variables).     *)
(******************************************************************************)

Section fiber_nd.

Variables (p_minus_2 q_minus_2 : nat).
Local Notation p := p_minus_2.+2.
Local Notation q := q_minus_2.+2.
Hypothesis prime_p : prime p.
Hypothesis prime_q : prime q.
Hypothesis coprime_pq : coprime p q.
Local Notation m := (p * q).
Local Notation msg := 'Z_m.

Let m_gt1 : (1 < m)%N.
Proof.
by rewrite (leq_trans (prime_gt1 prime_p)) // leq_pmulr // prime_gt0.
Qed.

Variable n : nat.

(* N-dimensional linear fiber: solutions to \sum u_i * v_i = target over Z_m.
   n.+1 unknowns (indexed by 'I_{n.+1}), 1 equation, n free variables. *)
Definition linear_fiber_nd (u : 'I_n.+1 -> msg) (target : msg)
    : {set {ffun 'I_n.+1 -> msg}} :=
  [set v : {ffun 'I_n.+1 -> msg} | \sum_(i < n.+1) u i * v i == target].

(* Compute the last variable given the first n *)
Definition solve_last (u : 'I_n.+1 -> msg) (target : msg)
    (w : {ffun 'I_n -> msg}) : msg :=
  (u ord_max)^-1 * (target - \sum_(j < n) u (lift ord_max j) * w j).

(* Extend first n variables to a full solution *)
Definition extend_to_fiber (u : 'I_n.+1 -> msg) (target : msg)
    (w : {ffun 'I_n -> msg}) : {ffun 'I_n.+1 -> msg} :=
  [ffun i : 'I_n.+1 =>
    match unlift ord_max i with
    | Some j => w j
    | None => solve_last u target w
    end].

(* Project fiber element to first n variables *)
Definition project_fiber (v : {ffun 'I_n.+1 -> msg}) : {ffun 'I_n -> msg} :=
  [ffun j : 'I_n => v (lift ord_max j)].

(* 0 < u < min(p,q) implies u is coprime to m = p*q *)
Lemma lt_minpq_coprime (a : msg) :
  (0 < val a)%N -> (val a < minn p q)%N -> coprime (val a) m.
Proof.
move=> Ha_pos Ha_lt.
have Ha_lt_p : (val a < p)%N by apply: (leq_trans Ha_lt); apply: geq_minl.
have Ha_lt_q : (val a < q)%N by apply: (leq_trans Ha_lt); apply: geq_minr.
have Hcop_p : coprime (val a) p.
  rewrite coprime_sym prime_coprime //.
  apply/negP => Hdvd.
  by have := dvdn_leq Ha_pos Hdvd; rewrite leqNgt Ha_lt_p.
have Hcop_q : coprime (val a) q.
  rewrite coprime_sym prime_coprime //.
  apply/negP => Hdvd.
  by have := dvdn_leq Ha_pos Hdvd; rewrite leqNgt Ha_lt_q.
by rewrite coprimeMr Hcop_p Hcop_q.
Qed.

(* coprime to m implies unit in Z_m *)
Lemma coprime_unitZm (a : msg) : coprime (val a) m -> a \is a GRing.unit.
Proof.
move=> Hcop.
by rewrite -[a]natr_Zp unitZpE // coprime_sym.
Qed.

(* Reindex sum: split at ord_max and reindex rest via lift *)
Lemma widen_lift_ord_max (i : 'I_n) :
  widen_ord (leqnSn n) i = lift ord_max i :> 'I_n.+1.
Proof. by apply/val_inj/eqP; rewrite /= /bump leqNgt ltn_ord. Qed.

Lemma sum_split_last (F : 'I_n.+1 -> msg) :
  \sum_(i < n.+1) F i =
  F ord_max + \sum_(j < n) F (lift ord_max j).
Proof.
rewrite big_ord_recr addrC; congr (_ + _).
by apply: eq_bigr => i _; rewrite widen_lift_ord_max.
Qed.

(* extend_to_fiber produces a fiber element *)
Lemma extend_in_fiber (u : 'I_n.+1 -> msg) (target : msg)
    (w : {ffun 'I_n -> msg}) :
  u ord_max \is a GRing.unit ->
  extend_to_fiber u target w \in linear_fiber_nd u target.
Proof.
move=> Hunit; rewrite inE; apply/eqP.
rewrite big_ord_recr /= /extend_to_fiber ffunE unlift_none.
under eq_bigr do rewrite ffunE widen_lift_ord_max liftK.
rewrite /solve_last.
set S := \sum_(j < n) _.
by rewrite (mulVKr Hunit) addrC subrK.
Qed.

(* project then extend is identity *)
Lemma project_extend_id (u : 'I_n.+1 -> msg) (target : msg)
    (w : {ffun 'I_n -> msg}) :
  project_fiber (extend_to_fiber u target w) = w.
Proof.
apply/ffunP => j.
by rewrite /project_fiber /extend_to_fiber !ffunE liftK.
Qed.

(* extend then project is identity for fiber elements *)
Lemma extend_project_id (u : 'I_n.+1 -> msg) (target : msg)
    (v : {ffun 'I_n.+1 -> msg}) :
  u ord_max \is a GRing.unit ->
  v \in linear_fiber_nd u target ->
  extend_to_fiber u target (project_fiber v) = v.
Proof.
move=> Hunit; rewrite inE => /eqP Hconstr.
apply/ffunP => i.
rewrite /extend_to_fiber ffunE.
case: (unliftP ord_max i) => [j -> | ->].
- by rewrite /project_fiber ffunE.
- rewrite /solve_last /project_fiber.
  have -> : \sum_(j < n) u (lift ord_max j) * [ffun j => v (lift ord_max j)] j =
            \sum_(j < n) u (lift ord_max j) * v (lift ord_max j).
    by apply: eq_bigr => j _; rewrite ffunE.
  set S := \sum_(j < n) _.
  have Huv : u ord_max * v ord_max = target - S.
    suff : u ord_max * v ord_max + S = target.
      by move/eqP; rewrite eq_sym -subr_eq => /eqP.
    rewrite /S.
    transitivity (\sum_(i < n.+1) u i * v i); last exact: Hconstr.
    rewrite big_ord_recr addrC; congr (_ + _).
    by apply: eq_bigr => j _; rewrite widen_lift_ord_max.
  (* Goal: (u ord_max)^-1 * (target - S) = v ord_max *)
  (* Rewrite target - S = u_max * v_max, then cancel *)
  by rewrite -Huv mulrA; set ui := _^-1; rewrite mulVr // mul1r.
Qed.

(* extend_to_fiber is injective *)
Lemma extend_fiber_inj (u : 'I_n.+1 -> msg) (target : msg) :
  injective (extend_to_fiber u target).
Proof.
by move=> w1 w2 /(congr1 project_fiber); rewrite !project_extend_id.
Qed.

(* Main result: N-dimensional fiber cardinality = m^n *)
Lemma linear_fiber_nd_card (u : 'I_n.+1 -> msg) (target : msg) :
  (0 < val (u ord_max))%N -> (val (u ord_max) < minn p q)%N ->
  #|linear_fiber_nd u target| = (m ^ n)%N.
Proof.
move=> Hu_pos Hu_lt.
have Hunit : u ord_max \is a GRing.unit.
  by apply: coprime_unitZm; apply: lt_minpq_coprime.
(* Bijection: extend_to_fiber maps {ffun 'I_n -> msg} injectively to fiber,
   and project_fiber is its inverse on fiber elements *)
have Himg : linear_fiber_nd u target =
            [set extend_to_fiber u target w | w : {ffun 'I_n -> msg}].
  apply/setP => v; apply/idP/imsetP.
  - move=> Hv.
    exists (project_fiber v) => //.
    by rewrite (extend_project_id Hunit Hv).
  - by move=> [w _ ->]; apply: extend_in_fiber.
rewrite Himg card_imset; last exact: extend_fiber_inj.
by rewrite card_ffun !card_ord Zp_cast.
Qed.

(* Specialization: 2D fiber is a special case of N-d fiber (n=1) *)
(* The 2D result linear_fiber_2d_card uses a different representation
   (msg * msg vs {ffun 'I_2 -> msg}), so the connection is via
   cardinality equality rather than definitional equality. *)

End fiber_nd.
