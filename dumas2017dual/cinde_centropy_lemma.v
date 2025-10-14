From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix.
From mathcomp Require Import Rstruct ring boolp finmap matrix lra.
Require Import realType_ext realType_ln ssr_ext ssralg_ext bigop_ext fdist.
Require Import proba jfdist_cond entropy graphoid smc_interpreter smc_tactics.
Require Import smc_proba homomorphic_encryption dsdp_program.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(*                                                                            *)
(* Lemma connecting conditional independence to conditional entropy           *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

Section cinde_centropy.
Context (R : realType).
Variables (U : finType) (P : R.-fdist U).
Variables (A B C : finType).
Variables (X : {RV P -> A}) (Y : {RV P -> B}) (Z : {RV P -> C}).

(* Key lemma: conditional independence implies conditional mutual information is zero *)
Lemma cinde_cond_mutual_info0 :
  P |= X _|_ Y | Z -> cond_mutual_info `p_[% X, Y, Z] = 0.
Proof.
move=> H_cinde.
rewrite cond_mutual_infoE.
apply/eqP; rewrite psumr_eq0.
apply/allP => [[a b] c] _.
apply/eqP.
have [->|Habc0] := eqVneq (`p_[% X, Y, Z] (a, b, c)) 0.
  by rewrite mul0r.
rewrite mulf_eq0.
apply/orP; right.
apply/eqP.
rewrite log_eq1.
- rewrite eqr_div.
  + rewrite mul1r.
    rewrite /jcPr !setX1 !Pr_set1.
    (* Need to show:
       Pr[X,Y,Z = (a,b,c)] / Pr[Z = c] = 
       (Pr[X,Z = (a,c)] / Pr[Z = c]) * (Pr[Y,Z = (b,c)] / Pr[Z = c])
    *)
    rewrite !dist_of_RVE.
    (* Use conditional independence *)
    move: (H_cinde a b c).
    rewrite /cinde_RV.
    rewrite cpr_eqE dist_of_RVE => H_eq.
    (* Apply conditional independence *)
    case/boolP: (`Pr[Z = c] == 0) => [/eqP Hz0|Hzne0].
    * by rewrite Hz0 !invr0 !mulr0 !mul0r.
    * rewrite -H_eq.
      field.
      by rewrite Hzne0.
  + by rewrite mulf_neq0// -Pr_jcPr_gt0 lt0Pr setX1 Pr_set1.
- by rewrite divr_gt0// -Pr_jcPr_gt0 lt0Pr setX1 Pr_set1.
- move=> i _.
  by rewrite dist_of_RVE mulf_ge0.
Qed.

(* Main result: conditional independence implies conditional entropy equality *)
Lemma cinde_centropy_eq :
  P |= X _|_ Y | Z -> `H(Y | [% X, Z]) = `H(Y | Z).
Proof.
move=> H_cinde.
have H0: cond_mutual_info `p_[% X, Y, Z] = 0.
  exact: cinde_cond_mutual_info0.
rewrite /cond_mutual_info in H0.
(* I(X; Y | Z) = H(Y | Z) - H(Y | X, Z) *)
(* So 0 = H(Y | Z) - H(Y | X, Z) means H(Y | X, Z) = H(Y | Z) *)
move/eqP in H0.
rewrite subr_eq0 in H0.
move/eqP in H0.
(* Now need to relate fdist_proj13 and fdistA to our RVs *)
have ->: `H(Y | [% X, Z]) = centropy (fdistA `p_[% X, Y, Z]).
  rewrite /centropy_RV /centropy.
  congr (\sum_(i in _) _ * _).
  by rewrite snd_RV3 fdistA_RV3.
have ->: `H(Y | Z) = centropy (fdist_proj13 `p_[% X, Y, Z]).
  rewrite /centropy_RV /centropy.
  congr (\sum_(i in _) _ * _).
  by rewrite /fdist_proj13 snd_RV3 fdistA_C13_snd fdistC13_RV3.
by rewrite -H0.
Qed.

End cinde_centropy.

