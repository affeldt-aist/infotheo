From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import finfun choice fintype tuple bigop finset path.
From mathcomp Require Import ssralg fingroup zmodp poly ssrnum.

Require Import Reals Fourier.
Require Import Rssr Reals_ext ssr_ext proba kraft.

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

(* generalization of log2, TODO: generalize lemmas in log2.v? *)
Definition Log (n : nat) x := (ln x / ln (INR n))%R.

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
  size (nth [::] c s) = Zabs_nat (ceil (Log #|T| (1 / P s)%R)).

Let sizes := map size c.

Hypothesis H : size sizes = t.

Lemma shannon_fano_meets_kraft : kraft_cond_in_R T sizes.
Proof.
rewrite /kraft_cond_in_R -(pmf1 P).
rewrite H.
apply ler_rsum => i _.
rewrite (@nth_map _ [::]); last first.
  move: H; by rewrite size_map => ->.
rewrite shannon_fano_sizes -expRV ?INR_eq0 ?card_ord //.
Abort.

Variable f : T -> seq T.

Lemma shannon_fano_average_entropy : average P f < `H P  + 1.
Proof.
Abort.

End ShannonFano.
