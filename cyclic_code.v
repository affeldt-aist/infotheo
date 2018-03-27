(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div choice fintype tuple finfun bigop prime ssralg.
From mathcomp Require Import poly polydiv finset fingroup perm finalg zmodp.
From mathcomp Require Import matrix mxalgebra mxpoly polydiv vector.
Require Import ssralg_ext poly_ext f2 hamming linearcode.

(** * Cyclic codes *)

(** OUTLINE:
- Section right_cyclic_shift
- Section polynomial_code_generator.
- Module Pcode : definition of polynomial codes
- Module Ccode : definition of cyclic codes
- Section cyclic_code_generator.
- Section cyclic_code_properties.
- Section polynomial_cyclic_equivalence_condition.
*)

Reserved Notation "'`[' P ']_' n" (at level 4).
Reserved Notation "''pgen[' C ]" (at level 8, format "''pgen[' C ]").
Reserved Notation "''cgen[' C ]" (at level 8, format "''cgen[' C ]").

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.

Local Open Scope ring_scope.

Section right_cyclic_shift.

(** Messages and codewords can be represented either as (row-)vectors
or as polynomials.  Cyclic codes are stable by right cyclic shift. We
define it in several equivalent ways:
- rcs_poly is defined using (pseudo-)division for polynomials.  rcs is
- a definition for row-vectors using a permutation.  rcs' is a direct
- definition for row-vectors. *)

Definition rcs_perm_ffun n : {ffun 'I_n.+1 -> 'I_n.+1} :=
  [ffun x : 'I_n.+1 => if x == ord0 then ord_max else inord x.-1].

Lemma rcs_perm_ffun_injectiveb n : injectiveb (@rcs_perm_ffun n).
Proof.
apply/injectiveP => x y.
rewrite /rcs_perm_ffun 2!ffunE.
case: ifPn => [/eqP ->|x0].
  case: ifPn => [/eqP -> //|y0].
  move/eqP; rewrite -val_eqE /= => /eqP n0y.
  exfalso; move: (ltn_ord y).
  rewrite ltnNge => /negP; apply.
  rewrite [in X in X < _]n0y /= inordK //; first by rewrite prednK // lt0n.
  apply: ltn_trans (ltn_ord y); by rewrite prednK // lt0n.
case: ifPn => [/eqP -> //|y0 /eqP].
  move/eqP; rewrite -val_eqE /= => /eqP n0x.
  exfalso; move: (ltn_ord x).
  rewrite ltnNge => /negP; apply.
  rewrite -[in X in X < _]n0x /= inordK //; first by rewrite prednK // lt0n.
  apply: ltn_trans (ltn_ord x); by rewrite prednK // lt0n.
rewrite -val_eqE /= inordK; last first.
  apply: (ltn_trans _ (ltn_ord x)); by rewrite prednK // lt0n.
rewrite inordK; last first.
  apply: (ltn_trans _ (ltn_ord y)); by rewrite prednK // lt0n.
move/eqP/(congr1 S).
by rewrite prednK ?lt0n // prednK ?lt0n // => ?; apply val_inj.
Defined.

Definition rcs_perm n : {perm 'I_n} :=
  if n is n.+1 then Perm (rcs_perm_ffun_injectiveb n) else 1.

(** right-cyclic shift with vectors: *)
Definition rcs (R : idomainType) n (x : 'rV[R]_n) := col_perm (rcs_perm n) x.

Lemma size_rcs (R : idomainType) n (x : 'rV[R]_n.+1) :
  size (rVpoly (rcs x)) < size ('X^n.+1 - 1%:P : {poly R}).
Proof. by rewrite size_Xn_sub_1 // ltnS /rVpoly size_poly. Qed.

Lemma map_mx_rcs (R0 R1 : idomainType) n (x : 'rV[R0]_n.+1) (f : R0 -> R1) :
  map_mx f (rcs x) = rcs (map_mx f x).
Proof. by rewrite /rcs map_col_perm. Qed.

Definition rcs' (R : idomainType) n (x : 'rV[R]_n.+1) :=
  \row_(i < n.+1) (if i == ord0 then x ord0 (inord n) else x ord0 (inord i.-1)).

Lemma rcs'0 (R : idomainType) n (x : 'rV[R]_n.+1) : (rcs' x == 0) = (x == 0).
Proof.
apply/idP/idP => [|/eqP ->].
  move/eqP/rowP => H; apply/eqP/rowP => i; rewrite !mxE.
  have ni : i.+1 %% n.+1 < n.+1 by apply ltn_pmod.
  move: (H (Ordinal ni)); rewrite !mxE -val_eqE /=.
  case: ifPn => [in' Hx|in' Hx].
    have ? : n = i.
      case/dvdnP : in' => -[//|[|k abs]] /=; last first.
        exfalso; move: (ltn_ord i); rewrite ltnNge => /negP; apply.
        by rewrite -ltnS abs ltn_Pmull.
      by rewrite mul1n => /eqP; rewrite eqSS => /eqP.
    rewrite -[RHS]Hx; congr (x _ _); apply/val_inj => /=; by rewrite inordK.
  rewrite -[RHS]Hx modn_small /=; last first.
    rewrite ltnS ltn_neqAle -ltnS (ltn_ord i) andbT; apply/eqP => in''.
    by rewrite in'' modnn eqxx in in'.
  congr (x _ _); apply val_inj => /=; by rewrite inordK.
apply/eqP/rowP => i; rewrite !mxE; by case: ifPn.
Qed.

Lemma rcs'_rcs (R : idomainType) n (x : 'rV[R]_n.+1) : rcs' x = rcs x.
Proof.
rewrite /rcs' /rcs; apply/rowP => i; rewrite !mxE.
case: ifPn => [/eqP -> |i0].
  congr (x _ _); apply val_inj => /=.
  by rewrite PermDef.fun_of_permE ffunE /= inordK.
congr (x _ _); apply val_inj => /=.
rewrite PermDef.fun_of_permE ffunE /= inordK.
  by rewrite (negPf i0) inordK // (ltn_trans _ (ltn_ord i)) // prednK // lt0n.
by rewrite (ltn_trans _ (ltn_ord i)) // prednK // lt0n.
Qed.

Lemma sub_XrVpoly_rcs (R : idomainType) n (x : 'rV[R]_n.+1) :
  'X * rVpoly x - rVpoly (rcs x) = (x 0 (inord n))%:P * ('X^n.+1 - 1).
Proof.
apply/polyP => i.
rewrite coef_add_poly coefXM coefCM coef_add_poly coefXn 2!coef_opp_poly coefC.
case: ifPn => [/eqP ->|i0]; last rewrite subr0.
  rewrite 2!add0r mulrN1 coef_rVpoly /=.
  case: insubP => //= j _ j0.
  rewrite mxE PermDef.fun_of_permE ffunE /= -val_eqE j0 /= j0 eqxx; congr (- x _ _).
  by apply val_inj => /=; rewrite inordK.
case/boolP : (i == n.+1) => [/eqP ->|in0].
  rewrite mulr1 2!coef_rVpoly /=.
  case: insubP => /= [j _ j0|]; last by rewrite ltnS leqnn.
  case: insubP => /= [?|_]; first by rewrite ltnn.
  rewrite subr0; congr (x _ _); apply val_inj => /=; by rewrite j0 inordK.
rewrite mulr0 2!coef_rVpoly; case: insubP => /= [j|].
  rewrite ltnS => in0' ji; case: insubP => /= [k _ ki|].
    apply/eqP; rewrite subr_eq0; apply/eqP.
    rewrite mxE PermDef.fun_of_permE ffunE -val_eqE /= ki (negPf i0) -ji; congr (x _ _).
    apply/val_inj => /=; by rewrite inordK.
  rewrite ltnS -ltnNge => n0i; exfalso.
  rewrite -ltnS prednK // in in0'; last by rewrite lt0n.
  by move/negP : in0; apply; rewrite eq_sym eqn_leq {}n0i.
rewrite -leqNgt => n0i; case: insubP => /= [j|]; last by rewrite subrr.
rewrite ltnS => in0' ji; exfalso; move/negP : in0; apply.
by rewrite eqn_leq ltnW //= (leq_trans n0i (leq_pred i)).
Qed.

(** right-cyclic shift with polynomials: *)
Definition rcs_poly (R : idomainType) (p : {poly R}) n := ('X * p) %% ('X^n - 1).

Lemma size_rcs_poly (R : idomainType) n (x : {poly R}) (xn : size x <= n) :
  0 < n -> size (rcs_poly x n) <= n.
Proof.
move=> n0.
rewrite /rcs_poly.
set xn1 := _ - _.
apply (@leq_trans (size xn1).-1); last by rewrite /xn1 size_Xn_sub_1.
rewrite -ltnS prednK; last by rewrite size_Xn_sub_1.
have : xn1 != 0 by apply/monic_neq0/monic_Xn_sub_1.
by move/ltn_modpN0; apply.
Qed.

(* TODO: not used? *)
Lemma size_rcs_poly_old (R : idomainType) n (x : 'rV[R]_n) : size (rcs_poly (rVpoly x) n) <= n.
Proof.
destruct n as [|n'].
  rewrite /rcs_poly subrr modp0.
  have -> : x = 0 by apply/matrixP => i [].
  by rewrite linear0 mulr0 size_poly0.
by rewrite size_rcs_poly // size_poly.
Qed.

(** Equivalence right-cyclic shift vectors <-> polynomials (see
[McEliece 2002], Theorem 8.1) *)

Lemma rcs_rcs_poly (F : fieldType) n0 (x : 'rV[F]_n0) : rcs x = poly_rV (rcs_poly (rVpoly x) n0).
Proof.
destruct n0 as [|n0].
  rewrite /rcs_poly (_ : 'X^0 = 1); last first.
    by apply/polyP => i; rewrite coefXn.
  rewrite subrr modp0 (_ : rVpoly x = 0); last first.
    apply/polyP => i.
    rewrite coef_rVpoly.
    by case: insubP => //; rewrite coef0.
  rewrite mulr0 /rcs /= col_perm1.
  apply/rowP.
  case; by case.
rewrite -rcs'_rcs /rcs' /rcs_poly.
move/eqP: (sub_XrVpoly_rcs x); rewrite subr_eq => /eqP.
by case/divp_modpP/(_ (size_rcs _)) => _ <-; rewrite rVpolyK -rcs'_rcs.
Qed.

Lemma rcs_poly_rcs (F : fieldType) n0 (x : {poly F}) (xn0 : size x <= n0.+1) :
  rcs_poly x n0.+1 = rVpoly (@rcs _ n0.+1 (poly_rV x)).
Proof. rewrite rcs_rcs_poly poly_rV_K // poly_rV_K //; by apply size_rcs_poly. Qed.

(** stability by right-cyclic-shift: *)
Definition rcsP (F: finFieldType) n (C : {set 'rV[F]_n}) :=
  forall x, x \in C -> rcs x \in C.

End right_cyclic_shift.

Notation "'`[' P ']_' n" := (P %% ('X^n - 1)) : cyclic_code_scope.

Section polynomial_code_generator.

Variable (F : finFieldType) (n : nat) (C : {set 'rV[F]_n}).

Definition is_pgen := [qualify g | [forall x, (x \in C) == (g %| rVpoly x)]].
Fact is_pgen_key : pred_key is_pgen. Proof. by []. Qed.
Canonical is_pgen_keyed := KeyedQualifier is_pgen_key.

End polynomial_code_generator.

Notation "''pgen[' C ]" := (is_pgen C) : cyclic_code_scope.
Local Open Scope cyclic_code_scope.

Module Pcode.
Section polynomial_code.

Variables (F : finFieldType) (n : nat).

Record t := mk {
  lcode0 :> Lcode0.t F n ;
  gen : {poly F} ;
  size_gen : size gen < n ;
  P : gen \is 'pgen[[set cw in lcode0]] }.

End polynomial_code.
End Pcode.

Coercion pcode_coercion (F : finFieldType) (n : nat) (c : Pcode.t F n) : {vspace 'rV[F]_n} :=
  let: Pcode.mk v _ _ _ := c in v.

Module Ccode.

Section cyclic_code_definition.

Variables (F : finFieldType) (n : nat).

Record t := mk {
  lcode0 :> Lcode0.t F n ;
  P : rcsP [set cw in lcode0] }.

End cyclic_code_definition.

End Ccode.

Coercion ccode_coercion (F : finFieldType) (n : nat) (c : Ccode.t F n) : {vspace 'rV[F]_n} :=
 let: Ccode.mk v _ := c in v.

Section cyclic_code_generator.

Variable (F : finFieldType) (n : nat) (C : Ccode.t F n).
Hypothesis C_not_trivial : not_trivial C.

(** A nonzero polynomial of lowest degree in the code is called a generator polynomial: *)
Definition is_cgen := [qualify x | non0_codeword_lowest_deg C x].
Fact is_cgen_key : pred_key is_cgen. Proof. by []. Qed.
Canonical is_cgen_keyed := KeyedQualifier is_cgen_key.

Local Notation "''cgen'" := (is_cgen).

Lemma is_cgenE g : g \is 'cgen = non0_codeword_lowest_deg C g.
Proof. by []. Qed.

Lemma size_is_cgen g : g \is 'cgen -> size (rVpoly g) <= n.
Proof. by rewrite size_poly. Qed.

Definition canonical_cgen : 'rV[F]_n := val (exists_non0_codeword_lowest_deg C_not_trivial).

Lemma canonical_cgenP : non0_codeword_lowest_deg C canonical_cgen.
Proof. rewrite /canonical_cgen; by case: exists_non0_codeword_lowest_deg. Qed.

Lemma size_canonical_cgen : size (rVpoly canonical_cgen) <= n.
Proof. by rewrite size_poly. Qed.

Lemma canonical_cgen_lowest_size : size (rVpoly canonical_cgen) = lowest_size C_not_trivial.
Proof. by []. Qed.

Definition parity_check : {poly F} := ('X^n - 1) %/ rVpoly canonical_cgen.

End cyclic_code_generator.

Notation "''cgen[' C ]" := (is_cgen C) : cyclic_code_scope.

Section cyclic_code_properties.

Variable n' : nat.
Let n := n'.+1.
Variables (F : finFieldType) (C : Ccode.t F n).

(** see [McEliece 2002],  Theorem 8.2, Lemma 2(a)(b), Theorem 8.3(a)(b) *)
Lemma shift_codeword (c : {poly F}) (cn : size c <= n) : poly_rV c \in C ->
  forall k, poly_rV (`[ 'X^k * c ]_n) \in C.
Proof.
move=> gC; elim=> [| k ih] /=.
- by rewrite (_ : 'X^0 = 1) // mul1r modp_small // (leq_ltn_trans cn) // size_Xn_sub_1.
- have {ih}ih : poly_rV `[ 'X^k * c ]_ n \in [set cs in C] by rewrite inE.
  move: (Ccode.P ih); rewrite rcs_rcs_poly poly_rV_K; last first.
    rewrite -ltnS -(_ : size (('X^n : {poly F}) - 1) = n.+1); last by rewrite size_Xn_sub_1.
    by apply/ltn_modpN0/monic_neq0/monic_Xn_sub_1.
  rewrite /rcs_poly modp_mul mulrA exprS inE; by apply.
Qed.

Lemma shift_linearity_codeword (c : {poly F}) (cn : size c <= n) :
  poly_rV c \in C ->
  forall p, poly_rV (`[ p * c ]_ n) \in C.
Proof.
move=> /= cC p; rewrite -(coefK p).
have -> : \poly_(i < size p) p`_i * c = \sum_(i < size p) (p`_i *: ('X^i * c)).
  rewrite mulrC poly_def big_distrr /=.
  apply eq_bigr => k _; by rewrite mulrC scalerAl.
have -> : `[ \sum_(i < size p) (p`_i *: ('X^i * c)) ]_n  =
          \sum_(i < size p) `[ p`_i *: ('X^i * c) ]_n.
  by rewrite (big_morph (id1 := 0) _ (@morph_modp _ _)) // mod0p.
have -> : \sum_(i < size p) `[ p`_i *: ('X^i * c) ]_n  =
          \sum_(i < size p) (p`_i *: `[ 'X^i * c ]_ n ).
  apply eq_bigr => k _; by rewrite modp_scalel.
apply Lcode0.mem_poly_rV => j.
rewrite linearZ /= Lcode0.sclosed //; by apply shift_codeword.
Qed.

Lemma remainder_in_code (c : {poly F}) (cn : size c <= n) :
  poly_rV c \in C ->
  forall p r, p \in C ->
  rVpoly p = rVpoly p %/ c * c + r -> size r < size c ->
  poly_rV r \in C.
Proof.
move=> cC p /= r  p_in_C Hdivp_g Hsize_rem.
have -> : r = `[ r ]_n.
  symmetry; rewrite modp_small //.
  apply (@ltn_trans (size c)) => //.
  by rewrite size_Xn_sub_1 // ltnS.
rewrite (_ : r = rVpoly p - rVpoly p %/ c * c); last first.
  by rewrite {1}Hdivp_g addrAC subrr add0r.
rewrite modp_add linearD /=.
have -> : `[ rVpoly p ]_n = rVpoly p.
  rewrite modp_small // size_Xn_sub_1 // ltnS; by apply: size_poly.
rewrite rVpolyK; apply Lcode0.aclosed => //.
by rewrite -mulNr shift_linearity_codeword.
Qed.

Lemma scale_cgen (g' : 'rV[F]_n) (HC : not_trivial C) :
  g' \is 'cgen[C] -> { k | (k != 0) && (g' == k *: canonical_cgen HC) }.
Proof.
move=> Hg'.
set g := canonical_cgen HC.
case/boolP : (g == g') => [/eqP ->|gg'].
  exists 1; by rewrite scale1r oner_neq0 eqxx.
have size_g := canonical_cgen_lowest_size HC.
rewrite -/g in size_g.
pose k := lead_coef (rVpoly g') / lead_coef (rVpoly g).
pose g'' : {poly F} := rVpoly g' - k *: rVpoly g.
have size_g' : size (rVpoly g') = size (rVpoly g) by rewrite size_g; apply size_lowest.
case/boolP : (k == 0) => k0.
  exfalso.
  move: k0.
  rewrite /k mulf_eq0 invr_eq0 2!lead_coef_eq0.
  case/orP; rewrite rVpoly0; apply/negP.
  by case/and3P : Hg'.
  by case/and3P : (canonical_cgenP HC).
have size_g'' : size g'' < size (rVpoly g).
  rewrite /g'' -size_g'; apply size_sub => //.
  apply/eqP; rewrite rVpoly0; by case/and3P : Hg'.
  rewrite lreg_size ?size_g' //; by apply/GRing.lregP.
  rewrite lead_coefZ /k -mulrA mulVr ?mulr1 // unitfE lead_coef_eq0 rVpoly0; by case/and3P : (canonical_cgenP HC).
have g''C : poly_rV g'' \in C.
  rewrite /g'' linearD /= linearN /= linearZ /= (proj2 (Lcode0.aclosed C)) // ?rVpolyK; first by case/and3P : Hg'.
  rewrite Lcode0.oclosed // Lcode0.sclosed //; by case/and3P : (canonical_cgenP HC).
have g''0 : g'' = 0.
  apply/eqP/negPn/negP => abs.
  case/and3P: (canonical_cgenP HC) => _ _ /forallP/(_ (poly_rV g'')).
  rewrite g''C /= -/g.
  have -> : poly_rV g'' != 0 :> 'rV_n.
    apply: contra abs => /poly_rV_0_inv; apply.
    rewrite /g'' ltnW //.
    have : size (rVpoly g') <= n by rewrite size_poly.
    apply/leq_trans/size_sub => //.
      apply/eqP; rewrite rVpoly0; by case/and3P : Hg'.
      rewrite lreg_size ?size_g' //; by apply/GRing.lregP.
    rewrite lead_coefZ /k -mulrA mulVr ?mulr1 // unitfE lead_coef_eq0 rVpoly0; by case/and3P : (canonical_cgenP HC).
  rewrite andbT poly_rV_K; last by rewrite ltnW // (leq_trans size_g'') // size_canonical_cgen.
  rewrite leq_eqVlt -(eq_sym (size g'')) ltn_eqF //=.
  apply/negP.
  rewrite negb_imply -leqNgt leq_eqVlt size_g'' orbT andbT.
  move: (size_g'').
  rewrite ltnNge; apply: contra => /eqP <-.
  rewrite poly_rV_K // ltnW //; apply: (leq_trans size_g''); by rewrite size_poly.
rewrite /g'' in g''0.
move/eqP : g''0; rewrite subr_eq add0r; move/eqP => g''0.
exists k.
by rewrite k0 -(rVpolyK g') g''0 linearZ /= rVpolyK.
Qed.

Lemma divide_codeword (p : {poly F}) : poly_rV (`[ p ]_n) \in C ->
  forall g, g \is 'cgen[C] -> rVpoly g %| p.
Proof.
move=> pC g Hg.
case/boolP : (p == 0) => [/eqP -> | p0].
  by rewrite dvdp0.
move/eqP: (divp_eq p (rVpoly g)); rewrite addrC -subr_eq => /eqP.
move/(congr1 (fun x => `[ x ]_n))/esym.
have size_rem : size (p %% rVpoly g) < size (rVpoly g).
  rewrite ltn_modpN0 //; case/and3P : Hg => _ ? _; by rewrite rVpoly0.
have rem_n : size (p %% rVpoly g) <= n.
  by rewrite ltnW //; apply/(leq_trans size_rem)/(size_is_cgen Hg).
rewrite modp_small; last by rewrite size_Xn_sub_1.
rewrite modp_add modp_opp => pmodg.
have rem_in_C : poly_rV (p %% rVpoly g) \in C.
  rewrite pmodg linearD /= (proj2 (Lcode0.aclosed C)) // linearN /= Lcode0.oclosed //.
  apply/shift_linearity_codeword => //.
  by apply (size_is_cgen Hg).
  case/and3P : Hg => ? _ _; by rewrite rVpolyK.
have rem_0 : p %% rVpoly g = 0.
  apply/eqP/negPn/negP => abs.
   case/and3P : Hg => _ _ /forallP/(_ (poly_rV (p %% rVpoly g))).
   rewrite rem_in_C /= (_ : _ != 0 = true) ?andbT; last first.
     apply: contra abs; by apply poly_rV_0_inv.
   apply/negP.
   rewrite negb_imply -ltnNge poly_rV_K // size_rem andbT.
   move: size_rem.
   rewrite -{1}(poly_rV_K rem_n).
   by rewrite ltnNge; apply: contra => /eqP ->.
apply/dvdpP.
exists (p %/ rVpoly g).
by rewrite {1}(divp_eq p (rVpoly g)) rem_0 addr0.
Qed.

Lemma cgen_divides_Xn_sub_1 g : g \is 'cgen[C] -> rVpoly g %| 'X^n - 1.
Proof.
move=> Hg.
move: (@divide_codeword ('X^n - 1)).
have -> : `[ 'X^n - 1 ]_n = 0 :> {poly F} by rewrite modpp.
by rewrite linear0 (proj1 (Lcode0.aclosed C)) => /(_ erefl); apply.
Qed.

Lemma divides_lowest_size (HC : not_trivial C) (g : {poly F}) (gn : size g <= n) :
  g \is 'pgen[[set cw in C]] -> size g = lowest_size HC.
Proof.
move=> H.
rewrite -(poly_rV_K gn).
apply/size_lowest/and3P; split.
- move/forallP : H => /(_ (poly_rV g)).
  rewrite inE => /eqP ->.
  by rewrite poly_rV_K.
- apply/eqP => abs.
  have {H}H : forall p, p \in [set cw in C] -> p = 0.
    move=> p Hp.
    move/forallP : H => /(_ p).
    rewrite Hp => /eqP/esym.
    by rewrite -(poly_rV_K gn) abs linear0 dvd0p rVpoly0 => /eqP.
  case: HC => x /andP [xC].
  apply/negP; rewrite negbK; apply/eqP/H; by rewrite inE.
- apply/forallP => /= x; apply/implyP => /and3P[H1 H2 H3].
  rewrite poly_rV_K //.
  move/forallP : H => /(_ x); rewrite inE H1 => /eqP/esym.
  apply: dvdp_leq; by rewrite rVpoly0.
Qed.

Lemma cgen_is_pgen g : g \is 'cgen[C] -> rVpoly g \is 'pgen[[set cw in C]].
Proof.
move=> Hg; apply/forallP => p; apply/eqP; apply/idP/idP => [p_in_C | g_generated].
- have H : poly_rV (`[ rVpoly p ]_n) = p.
    by rewrite modp_small // ?rVpolyK // size_Xn_sub_1 // ltnS size_poly.
  rewrite -{}H in p_in_C.
  apply divide_codeword => //; by rewrite inE in p_in_C.
- case/dvdpP: g_generated => /= i p_i_g.
  rewrite -(rVpolyK p).
  have <- : `[ rVpoly p ]_n = rVpoly p.
    rewrite modp_small // size_Xn_sub_1 // ltnS; by apply size_poly.
  rewrite p_i_g inE shift_linearity_codeword //.
  by apply (size_is_cgen Hg).
  by rewrite rVpolyK //; case/and3P : Hg.
Qed.

Lemma pgen_is_cgen (g : 'rV_n) (C_not_trivial : not_trivial C) :
  rVpoly g \is 'pgen[[set cw in C]] -> g \is 'cgen[C].
Proof.
move=> Hg.
rewrite is_cgenE; apply/and3P => [:H1]; split.
- abstract: H1.
  by move/forallP : Hg => /(_ g); rewrite inE => /eqP ->.
- apply/eqP => abs.
  have {Hg}Hg : forall p, p \in [set cw in C] -> p = 0.
    move=> p Hp.
    move/forallP : Hg => /(_ p); rewrite Hp => /eqP/esym.
    by rewrite abs linear0 dvd0p rVpoly0 => /eqP.
  case: C_not_trivial => x /andP[] xC.
  move: (Hg x) => /=; rewrite inE => /(_ xC) ->; by rewrite eqxx.
- apply/forallP => /= x; apply/implyP => /and3P[K1 K2 K3].
  have gn : size (rVpoly g) <= n by rewrite size_poly.
  rewrite (divides_lowest_size C_not_trivial gn Hg).
  by apply size_lowestP.
Qed.

Lemma pgen_cgen (C_not_trivial : not_trivial C) (g : 'rV_n) :
  (rVpoly g \is 'pgen[[set cw in C]]) = (g \is 'cgen[C]).
 apply/idP/idP; [exact: pgen_is_cgen | exact: cgen_is_pgen]. Qed.

(* the dimension of C is n - deg g *)
Lemma cgen_dim (HC : not_trivial C) :
  let g := rVpoly (canonical_cgen HC) in
  \dim C = (n - (size g).-1)%nat.
Proof.
move=> g.
(* TODO *)
Abort.

Lemma divides_Xn_sub_1_is_linear (g : {poly F}) : g %| 'X^n - 1 ->
  submod_closed [set c : 'rV[F]_n | g %| rVpoly c]
  (* TODO: and the dimension of C is n - deg g *).
Proof.
case/dvdpP => /= i ig.
split.
  by rewrite inE linear0 dvdp0.
move=> k a b; rewrite !inE => ga gb.
case/boolP : (k == 0) => [/eqP ->|k0]; first by rewrite scale0r add0r.
by rewrite linearD linearZ /= dvdp_addr // dvdp_scaler.
Qed.

Lemma divides_Xn_sub_1_is_cyclic (g : {poly F}) : g %| 'X^n - 1 ->
  rcsP [set c : 'rV[F]_n | g %| rVpoly c].
Proof.
move=> gXn x.
rewrite !inE => /dvdpP[/= i xig].
rewrite rcs_rcs_poly poly_rV_K; last first.
  rewrite /rcs_poly -ltnS -(@size_Xn_sub_1 F n erefl).
  by rewrite ltn_modpN0 // -size_poly_eq0 size_Xn_sub_1.
by rewrite /rcs_poly -dvdp_mod // xig mulrA dvdp_mull // modpp.
Qed.

End cyclic_code_properties.

Section polynomial_cyclic_equivalence_condition.

Variables (F : finFieldType) (n' : nat).
Let n := n'.+1.
Variable C : Pcode.t F n.
Hypothesis C_not_trivial : not_trivial C.

Lemma polynomial_rcs : Pcode.gen C %| 'X^n - 1 <-> rcsP [set cw in C].
Proof.
split => [H|].
  rewrite /rcsP /= => cw; rewrite inE => cwC.
  rewrite inE rcs_rcs_poly.
  move/forallP: (Pcode.P C) => /(_ (poly_rV (rcs_poly (rVpoly cw) n))).
  rewrite inE => /eqP ->.
  rewrite poly_rV_K; last by apply size_rcs_poly_old.
  rewrite /rcs_poly -dvdp_mod // dvdp_mull //.
  by move/forallP: (Pcode.P C) => /(_ cw); rewrite inE cwC => /eqP/esym.
move=> H.
move: (@cgen_divides_Xn_sub_1 _ _ (@Ccode.mk _ _ (Pcode.lcode0 C) H) (poly_rV (Pcode.gen C))).
rewrite poly_rV_K; last by rewrite ltnW // (Pcode.size_gen C).
apply.
rewrite -pgen_cgen // poly_rV_K; last by rewrite ltnW // (Pcode.size_gen C).
exact: (Pcode.P C).
Qed.

End polynomial_cyclic_equivalence_condition.
