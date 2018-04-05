From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import finfun choice fintype tuple bigop finset path.
From mathcomp Require Import ssralg fingroup zmodp poly ssrnum.

Require Import Reals Fourier.
Require Import Rssr log2 Reals_ext ssr_ext proba kraft.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section prefix_code_build.

Variable t' : nat.
Let t := t'.+2.
Let T := [finType of 'I_t].
Variables sizes : seq nat.

(* TODO: relation with sigma in kraft.v? *)
(* NB: use the prepend function of kraft.v instead of nseq/cat? *)
Fixpoint prefix_from_sizes (i : nat) : seq T :=
  if i isn't i'.+1 then
    nseq (nth O sizes O) ord0
  else
    nseq (nth O sizes i - nth O sizes i') ord0 ++
    ary_of_nat _ (nat_of_ary (prefix_from_sizes i')).+1.

End prefix_code_build.

Local Open Scope R_scope.

Definition ceil (r : R) : Z := if frac_part r == 0 then Int_part r else up r.

Definition floor : R -> Z := Int_part.

Lemma floorP (r : R) : r - 1 < IZR (floor r) <= r.
Proof. rewrite /floor; case: (base_Int_part r) => ? ?; split=> //; fourier. Qed.

Lemma ceilP (r : R) : r <= IZR (ceil r) < r + 1.
Proof.
rewrite /ceil; case: ifPn => [|] /eqP r0.
  rewrite frac_Int_part //; split; fourier.
case: (floorP r); rewrite /floor => H1 /Rle_lt_or_eq_dec[] H2.
  rewrite up_Int_part plus_IZR; split; fourier.
exfalso; apply/r0/eqP; rewrite subR_eq0; by apply/eqP.
Qed.

Require Import Rbigop.

(* NB(rei): redefine kraft_cond in R instead of with an rcfType *)
(* TODO: use mathcomp.analysis? or build an ad-hoc interface to bridge R and rcfType as a temporary fix? *)

Definition kraft_cond_in_R (T : finType) (l : seq nat) :=
  let n := size l in
  (\rsum_(i < n) ((INR #|T|) ^- nth O l i) <= (1 : R))%R.

Local Open Scope proba_scope.

Section average_length.

Variable T : finType.
Variable P : {dist T}.
Variable f : T -> seq T.
Hypothesis f_inj : injective f.

Definition average := \rsum_(x in T) P x * INR (size (f x)).

End average_length.

Require Import entropy.

Local Open Scope entropy_scope.

Section ShannonFano.

Variable t' : nat.
Let t := t'.+2.
Let T := [finType of 'I_t].
Variable P : {dist T}.
Variable c : code_set T.

Hypothesis shannon_fano_sizes : forall s : T,
  size (nth [::] c s) = Zabs_nat (ceil (Log (INR #|T|) (1 / P s)%R)).

Let sizes := map size c.

Hypothesis H : size sizes = t.

Lemma leR_wiexpn2l x :
  0 <= x -> x <= 1 -> {homo (pow x) : m n / (n <= m)%nat >-> m <= n}.
Proof.
move/RleP; rewrite Rle_eqVlt => /orP[/eqP/esym -> _ m n|/RltP x0 x1 m n /leP nm].
  case: n => [|n nm].
    case: m => [_ |m _]; first exact: Rle_refl.
    rewrite pow_ne_zero //=; exact/Rle_0_1.
  rewrite pow_ne_zero; last by case: m nm.
  rewrite pow_ne_zero //; exact/Rle_refl.
apply Rle_inv_conv => //.
exact/pow_gt0.
exact/pow_gt0.
rewrite -expRV; last by apply/eqP/gtR_eqF.
rewrite -expRV; last by apply/eqP/gtR_eqF.
apply Rle_pow => //.
rewrite -invR1; apply Rle_Rinv => //; exact/Rlt_0_1.
Qed.

Lemma leR_weexpn2l x :
  1 <= x -> {homo (pow x) : m n / (m <= n)%nat >-> m <= n}.
Proof. move=> x1 m n /leP nm; exact/Rle_pow. Qed.

Lemma shannon_fano_meets_kraft : kraft_cond_in_R T sizes.
Proof.
rewrite /kraft_cond_in_R -(pmf1 P).
rewrite H.
apply ler_rsum => i _.
rewrite (@nth_map _ [::]); last first.
  move: H; by rewrite size_map => ->.
rewrite shannon_fano_sizes.
apply Rle_trans with (Exp (INR #|T|) (- Log (INR #|T|) (1 / P i))).
  admit.
rewrite div1R LogV.
  rewrite oppRK.
  rewrite LogK.
  exact/Rle_refl.
  by rewrite (_ : 1 = INR 1) //; apply/lt_INR/ltP; rewrite card_ord.
Abort.

Variable f : T -> seq T.

Lemma shannon_fano_average_entropy : average P f < `H P  + 1.
Proof.
Abort.

End ShannonFano.
