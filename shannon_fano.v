From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import finfun choice fintype tuple bigop finset path.
From mathcomp Require Import ssralg fingroup zmodp poly ssrnum.

Require Import Reals Fourier.
Require Import Rssr log2 Reals_ext Rbigop ssr_ext proba entropy kraft.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Lemma leR0ceil x : 0 <= x -> (0 <= ceil x)%Z.
Proof. move=> ?; case: (ceilP x) => K _; exact/le_IZR/(Rle_trans _ _ _ _ K). Qed.

Lemma leR_wiexpn2l x :
  0 <= x -> x <= 1 -> {homo (pow x) : m n / (n <= m)%nat >-> m <= n}.
Proof.
move/RleP; rewrite le0R => /orP[/eqP -> _ m n|/RltP x0 x1 m n /leP nm].
  case: n => [|n nm].
    case: m => [_ |m _]; first exact: Rle_refl.
    by rewrite pow_ne_zero.
  rewrite pow_ne_zero; last by case: m nm.
  rewrite pow_ne_zero //; exact/Rle_refl.
apply Rle_inv_conv => //.
exact/pow_gt0.
exact/pow_gt0.
rewrite -powRV; last exact/eqP/gtR_eqF.
rewrite -powRV; last exact/eqP/gtR_eqF.
apply Rle_pow => //.
rewrite -invR1; exact: Rinv_le_contravar.
Qed.

Lemma leR_weexpn2l x :
  1 <= x -> {homo (pow x) : m n / (m <= n)%nat >-> m <= n}.
Proof. move=> x1 m n /leP nm; exact/Rle_pow. Qed.

Lemma invR_gt1 x : 0 < x -> (1 <b / x) = (x <b 1).
Proof.
move=> x0; apply/idP/idP => [|] /RltP x1; apply/RltP; last first.
  rewrite -invR1; apply Rinv_lt_contravar => //; by rewrite mulR1.
move/Rinv_lt_contravar : x1; rewrite mul1R invR1 invRK; last exact/gtR_eqF.
apply; exact/invR_gt0.
Qed.

(* NB(rei): redefine kraft_cond in R instead of with an rcfType *)
(* TODO: use mathcomp.analysis? or build an ad-hoc interface to bridge R and rcfType as a temporary fix? *)
Definition kraft_cond_in_R (T : finType) (l : seq nat) :=
  let n := size l in
  (\rsum_(i < n) ((INR #|T|) ^- nth O l i) <= (1 : R))%R.

Local Open Scope proba_scope.

Definition is_shannon_fano_code (T : finType) (P : {dist T}) (c : code_set T) :=
  forall s : T, size (nth [::] c (enum_rank s)) =
    Zabs_nat (ceil (Log (INR #|T|) (1 / P s)%R)).

Section average_length.

Variables (T : finType) (P : {dist T}).
Variable f : T -> seq T. (* encoding function *)
Hypothesis f_inj : injective f.

Definition average := \rsum_(x in T) P x * INR (size (f x)).

End average_length.

Section ShannonFano.

Variable t' : nat.
Let t := t'.+2.
Let T := [finType of 'I_t].
Variable P : {dist T}.
Hypothesis Pr_pos : forall s, P s != 0.

Variable c : code_set T.
Let sizes := map size c.
Hypothesis H : size sizes = t.
Hypothesis shannon_fano : is_shannon_fano_code P c.

Lemma shannon_fano_meets_kraft : kraft_cond_in_R T sizes.
Proof.
rewrite /kraft_cond_in_R -(pmf1 P).
rewrite H.
apply ler_rsum => i _.
rewrite (@nth_map _ [::]); last first.
  move: H; by rewrite size_map => ->.
rewrite {1}(_ : i = enum_rank (enum_val (cast_ord (esym (card_ord _)) i)) :> nat); last first.
  by rewrite enum_valK.
rewrite shannon_fano.
have Pi0 : 0 < P i by apply/RltP; rewrite lt0R Pr_pos; exact/RleP/dist_nonneg.
apply Rle_trans with (Exp (INR #|T|) (- Log (INR #|T|) (1 / P i))); last first.
  rewrite div1R LogV //.
  rewrite oppRK LogK //.
  exact/Rle_refl.
  by apply/RltP; rewrite (_ : 1 = INR 1) // ltR_nat card_ord.
rewrite pow_Exp; last by apply/RltP; rewrite ltR0n card_ord.
rewrite Exp_Ropp.
apply/leR_inv => //.
  rewrite inE; exact/RltP/Exp_gt0.
apply Exp_le_increasing.
  by apply/RltP; rewrite (_ : 1 = INR 1) // ltR_nat card_ord.
rewrite INR_Zabs_nat; last first.
  set j := enum_val _.
  have Pj0 : 0 < P j.
    rewrite (_ : j = i) //.
    rewrite /j enum_val_ord; exact/val_inj.
  case/boolP : (P j == 1) => [/eqP ->|Pj1].
    by rewrite divR1 Log_1 /ceil fp_R0 eqxx /=; apply/Int_part_pos/Rle_refl.
  apply/leR0ceil/ltRW/ltR0Log.
  by apply/RltP; rewrite (_ : 1 = INR 1) // ltR_nat card_ord.
  rewrite div1R.
  apply/RltP; rewrite invR_gt1 // ltR_neqAle Pj1 /=; exact/RleP/dist_max.
set x := Log _ _; case: (ceilP x).
rewrite (_ : enum_val _ = i) // enum_val_ord; exact/val_inj.
Qed.

End ShannonFano.

Section BinaryShannonFano.

Let T := [finType of 'I_2].
Variable P : {dist T}.
Hypothesis Pr_pos : forall s, P s != 0.

Variable c : code_set T.
Hypothesis shannon_fano : is_shannon_fano_code P c.

Let f (s : T) := nth [::] c s (* encoding function *).

Local Open Scope entropy_scope.

Lemma shannon_fano_average_entropy : average P f < `H P  + 1.
Proof.
rewrite /average.
apply Rlt_le_trans with (\rsum_(x in T) P x * (- Log (INR #|T|) (P x) + 1)).
  apply ltR_rsum; [by rewrite card_ord|move=> i].
  apply Rmult_lt_compat_l.
    apply/RltP; rewrite lt0R Pr_pos /=; exact/RleP/dist_nonneg.
  rewrite /f.
  rewrite {1}(_ : i = enum_rank (enum_val (cast_ord (esym (card_ord _)) i)) :> nat); last first.
    by rewrite enum_valK.
  rewrite shannon_fano.
  rewrite (_ : INR #|T| = 2) // ?card_ord // -!/(log _).
  set x := log _; case: (ceilP x) => _ Hx.
  have Pi0 : 0 < P i by apply/RltP; rewrite lt0R Pr_pos /=; exact/RleP/dist_nonneg.
  rewrite INR_Zabs_nat; last first.
    apply/leR0ceil.
    rewrite /x div1R /log LogV; last first.
      rewrite (_ : enum_val _ = i) // enum_val_ord; exact/val_inj.
    apply oppR_ge0.
    rewrite -(Log_1 2); apply Log_increasing_le => //.
    rewrite (_ : enum_val _ = i) // enum_val_ord; exact/val_inj.
    exact/dist_max.
  case: (ceilP x) => _.
  rewrite -LogV // -/(log _) -(div1R _) /x.
  rewrite (_ : enum_val _ = i) // enum_val_ord; exact/val_inj.
evar (h : T -> R).
rewrite (eq_bigr h); last first.
  move=> i _; rewrite mulRDr mulR1 mulRN  /h; reflexivity.
rewrite {}/h big_split /=; apply Rplus_le_compat.
  apply Req_le.
  rewrite /entropy (big_morph _ morph_Ropp oppR0); apply eq_bigr => i _.
  by rewrite card_ord (_ : INR 2 = 2).
rewrite pmf1; exact/Rle_refl.
Qed.

End BinaryShannonFano.

Section shannon_fano_code_build.

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

End shannon_fano_code_build.
