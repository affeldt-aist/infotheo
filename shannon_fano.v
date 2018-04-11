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

Section average_length.

Variables (A T : finType) (P : {dist A}).
Variable f : A -> seq T. (* encoding function *)
Hypothesis f_inj : injective f.

Definition average := \rsum_(x in A) P x * INR (size (f x)).

End average_length.

Section shannon_fano_def.

Variables (A T : finType) (P : {dist A}).
Variables (f : A -> seq T).
Hypothesis f_inj : injective f.

Definition is_shannon_fano_code :=
  forall s, size (f s) = Zabs_nat (ceil (Log (INR #|T|) (1 / P s)%R)).

End shannon_fano_def.

Definition kraft_cond_new_in_R (T : finType) (c : code_set T) :=
  (\rsum_(i < size c) ((INR #|T|) ^- nth O (map size c) i) <= (1 : R))%R.

(*
Section kraft_equiv.

Variables (A T : finType) (f : T -> seq T).
Hypothesis f_inj : injective f.

Lemma nth_f :
  \rsum_(i < #|T|) INR #|T| ^- size (nth [::] c i) = \rsum_(i | true) INR #|T| ^- size (f i).
Proof.
Admitted.


Lemma kraft_cond_new_in_RP : kraft_cond_new_in_R f c <-> kraft_cond_in_R T (map size c).
Proof.
split => H.
  rewrite /kraft_cond_in_R.
  rewrite /kraft_cond_new_in_R in H.
  rewrite size_map.
  rewrite -f_size.
  apply: (Rle_trans _ _ _ _ H).
  apply Req_le.
  transitivity (\rsum_(i < #|T|) INR #|T| ^- size (nth [::] c i)).
    apply eq_bigr => i _.
    congr (_ ^- _).
    by rewrite (nth_map [::]) // -f_size.
  exact: nth_f.
Abort.

End kraft_equiv.
*)

Section ShannonFano.

Variable A : finType.
Variable t' : nat.
Let t := t'.+2.
Let T := [finType of 'I_t].
Variable P : {dist A}.
Hypothesis Pr_pos : forall s, P s != 0.

Let a : A.
by move/card_gt0P: (dist_domain_not_empty P) => /sigW [i].
Qed.

Variable (f : A -> seq T).
Hypothesis f_inj : injective f.
Hypothesis shannon_fano : is_shannon_fano_code P f (*c*) (*f*).

Lemma uniq_c : uniq (map f (enum A)).
Proof. by rewrite map_inj_uniq ?enum_uniq. Qed.

Let c := CodeSet uniq_c.
Let sizes := map size c.

Lemma shannon_fano_meets_kraft : kraft_cond_in_R T sizes.
Proof.
rewrite /kraft_cond_in_R -(pmf1 P).
rewrite /sizes size_map /= size_map.
rewrite (eq_bigr (fun i:'I_(size(enum A)) => INR #|'I_t| ^- size (f (nth a (enum A) i)))); last first.
  move=> i _.
  by rewrite -map_comp (nth_map a).
rewrite -(big_mkord xpredT (fun i => INR #|T| ^- size (f (nth a (enum A) i)))).
rewrite -(big_nth a xpredT (fun i => INR #|'I_t| ^- size (f i))).
rewrite enumT.
apply ler_rsum => i _.
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
  case/boolP : (P i == 1) => [/eqP ->|Pj1].
    by rewrite divR1 Log_1 /ceil fp_R0 eqxx /=; apply/Int_part_pos/Rle_refl.
  apply/leR0ceil/ltRW/ltR0Log.
  by apply/RltP; rewrite (_ : 1 = INR 1) // ltR_nat card_ord.
  rewrite div1R.
  apply/RltP; rewrite invR_gt1 // ltR_neqAle Pj1 /=; exact/RleP/dist_max.
by set x := Log _ _; case: (ceilP x).
Qed.

End ShannonFano.

Section BinaryShannonFano.

Variable A : finType.
Variable P : {dist A}.
Hypothesis Pr_pos : forall s, P s != 0.

Let T := [finType of 'I_2].
Variable (f : A -> seq T).
Hypothesis f_inj : injective f.
Hypothesis shannon_fano : is_shannon_fano_code P f (*c*) (*f*).

Local Open Scope entropy_scope.

Lemma shannon_fano_average_entropy : average P f < `H P  + 1.
Proof.
rewrite /average.
apply Rlt_le_trans with (\rsum_(x in A) P x * (- Log (INR #|T|) (P x) + 1)).
  apply ltR_rsum; [by apply dist_domain_not_empty|move=> i].
  apply Rmult_lt_compat_l.
    apply/RltP; rewrite lt0R Pr_pos /=; exact/RleP/dist_nonneg.
  rewrite shannon_fano.
  rewrite (_ : INR #|T| = 2) // ?card_ord // -!/(log _).
  set x := log _; case: (ceilP x) => _ Hx.
  have Pi0 : 0 < P i by apply/RltP; rewrite lt0R Pr_pos /=; exact/RleP/dist_nonneg.
  rewrite INR_Zabs_nat; last first.
    apply/leR0ceil.
    rewrite /x div1R /log LogV //.
    apply oppR_ge0.
    rewrite -(Log_1 2); apply Log_increasing_le => //.
    exact/dist_max.
  case: (ceilP x) => _.
  by rewrite -LogV // -/(log _) -(div1R _) /x.
evar (h : A -> R).
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

Let T := [finType of 'I_2].

Fixpoint shannon_fano_f (l : seq nat) (i : nat) : seq T :=
  if i isn't i'.+1 then
    nseq (nth O l O) ord0
  else
    ary_of_nat _ (nat_of_ary (shannon_fano_f l i')).+1 ++
    nseq (nth O l i - nth O l i') ord0.

Variables (A : finType) (P : {dist A}).

Let sizes := sort leq
  (map (fun a => Zabs_nat (ceil (Log (INR #|T|) (1 / P a)%R))) (enum A)).

Lemma shannon_fano_f_sizes i : (i < size sizes)%nat ->
  size (shannon_fano_f sizes i) = nth O sizes i.
Proof.
elim: i => [_ |i IH Hi]; first by rewrite /shannon_fano_f size_nseq.
rewrite /shannon_fano_f size_cat size_nseq -/(shannon_fano_f _ _ ).
suff -> : size (ary_of_nat 0 (nat_of_ary (shannon_fano_f sizes i)).+1) = nth O sizes i.
  rewrite subnKC // nth_of_sorted // ?leqnSn //=; exact/sort_sorted/leq_total.
rewrite ary_of_nat_unfold; case: ifPn.
  rewrite 2!ltnS leqn0 nat_of_ary_0 /=.
  admit.
rewrite -ltnNge 2!ltnS => H.
rewrite size_rcons /=.
Abort.

Lemma nat_of_aryK t' l : @ary_of_nat t' (nat_of_ary l) = l.
Proof.
Abort.

Lemma shannon_fano_f_is_shannon_fano :
  is_shannon_fano_code P (shannon_fano_f sizes \o enum_rank).
Proof.
move=> a.
rewrite /=.
rewrite card_ord -/(log _).
Abort.

End shannon_fano_code_build.
