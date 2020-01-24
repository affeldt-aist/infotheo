(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import all_ssreflect ssralg fingroup perm finalg matrix.
From mathcomp Require boolp.
Require Import Reals. (* Lra Nsatz. *)
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop.
Require Import fdist cinde.

Local Open Scope tuple_ext_scope.
Local Open Scope proba_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* wip *)

Module BN.
Section bn.
Variable U : finType.
Variable P : fdist U.
Variable n : nat.

Variant aRV := mkRV : forall A : finType, {RV P -> A} -> aRV. 
Definition aRV_type (v : aRV) :=
  let: mkRV A V := v in A.

Definition aRV_join (x y : aRV) :=
  let: mkRV A X := x in
  let: mkRV B Y := y in
  let Z : {RV P -> A * B} := fun u => (X u, Y u) in
  mkRV Z.

Definition aRV_1 := mkRV (fun _ => tt).

Section descendant.
Variable parent : rel 'I_n.
Definition topological := forall i j : 'I_n, parent i j -> i < j.
Hypothesis is_topo : topological.

Definition descendant : rel 'I_n := fun a b =>
  [exists p : {set 'I_n},
      (a \in p :\ b) && (b \in p) &&
      [forall i in p :\ b,
          [exists j in p, parent i j && ([set k in p | i < k < j] == set0)]]].

Lemma path_lt a b p : path parent a p -> b \in p -> a < b.
Proof.
elim: p a => [|c p IH] a //= /andP [Hac Hp'].
rewrite in_cons => /orP [/eqP -> | Hb].
  by rewrite is_topo.
by apply (ltn_trans (is_topo Hac)), IH.
Qed.

Lemma in_last (A : eqType) (a : A) p : a \in rcons p a.
Proof. by rewrite mem_rcons in_cons eqxx. Qed.

Lemma desc_max b (p : {set 'I_n}) c :
  [forall i in p :\ b,
      [exists j in p, parent i j && ([set k in p | i < k < j] == set0)]] ->
  c \in p -> c <= b.
Proof.
set h := #|p|.
have Hh: #|p| <= h by [].
clearbody h.
elim: h c p Hh => [|h IH] c p Hh /forallP Hp.
  rewrite leqn0 in Hh.
  by rewrite (cards0_eq (eqP Hh)) in_set0.
move=> Hc.
case Hcb: (c == b).
  by rewrite (eqP Hcb) leqnn.
have Hcp: c \in p :\ b by rewrite !inE Hcb.
move: (Hp c) => /implyP/(_ Hcp)/existsP [d] /and3P [Hd Hcd _].
apply (leq_trans (ltnW (is_topo Hcd))).
apply (IH d [set x in p | c < x]).
- rewrite -ltnS (leq_trans _ Hh) //.
  apply (@leq_ltn_trans (#|p :\ c|)).
    apply subset_leq_card.
    apply/subsetP => x.
    rewrite !inE.
    case Hx: (x == c) => /=.
      by rewrite (eqP Hx) ltnn andbC.
    by case: (x \in _).
  rewrite cardsD.
  have -> : p :&: [set c] = [set c].
    apply/setP => k. rewrite !inE.
    case Hk: (k == c).
      by move: Hcp; rewrite inE (eqP Hk) => /andP [_] ->.
    by rewrite andbF.
  rewrite cards1 subn1.
  case Hh': #|p|.
    by rewrite (cards0_eq Hh') inE in Hc.
  done.
- apply/forallP => e.
  rewrite !inE.
  apply/implyP => /and3P [Heb Hep Hec].
  move/implyP: (Hp e).
  rewrite !inE Heb Hep => /(_ isT) /existsP [j] /and3P [Hjp Hej /eqP <-].
  apply/existsP; exists j.
  rewrite Hej !inE Hjp /=.
  rewrite (ltn_trans Hec) /=.
    apply/eqP/setP => x.
    rewrite !inE.
    case Hex: (e < x).
      by rewrite (ltn_trans Hec Hex) andbT.
    by rewrite !andbF.
  by apply is_topo.
- by rewrite !inE Hd is_topo.
Qed.

Lemma descendantP a b :
  reflect (exists p, path parent a (rcons p b)) (descendant a b).
Proof.
apply: (iffP existsP) => -[p].
- move/andP => [/andP [Ha Hb] /forallP Hp].
  exists [seq i <- ord_enum n | (i \in p) && (a < i < b)].
  move Hh: #|p| => h.
  elim: h a p Hh Ha Hb Hp => [|h IH] a p Hh Ha Hb Hp.
    by rewrite (cards0_eq Hh) in_set0 in Hb.
  move Hp': [seq i <- ord_enum n | (i \in p) && (a < i < b)] => [|a' p'].
    rewrite /= andbT.
    move: (Hp a) => /implyP/(_ Ha)/existsP [a'] /and3P [Ha' Ha'p].
    move: Hp'.
    move/eqP.
    rewrite -(negbK (_ == [::])) -has_filter => /hasPn.
    case Ha'b: (a' == b).
      by rewrite -(eqP Ha'b).
    move/(_ a' _).
    rewrite mem_ord_enum Ha' (is_topo Ha'p) /= -leqNgt => /(_ isT).
    rewrite leq_eqVlt eq_sym => /orP [/eqP /ord_inj|] Hb'.
      by rewrite Hb' eqxx in Ha'b.
    move/eqP/setP/(_ b).
    rewrite !inE Hb Hb'.
    move/forallP in Hp.
    move: Ha; rewrite !inE.
    case Hab: (a == b) => //= Hap.
    have: a <= b by apply (desc_max Hp).
    rewrite leq_eqVlt.
    case Hab': (a < b) => //=.
    rewrite orbF => /eqP /ord_inj H.
    by rewrite H eqxx in Hab.
  rewrite rcons_cons /=.
  have Hrp': p' = [seq i <- ord_enum n | i \in p & a' < i < b].
    admit.
  rewrite Hrp' IH //.
  move: (Hp a) => /implyP/(_ Ha)/existsP [c] /and3P [Hcp Hac Hci].
  case Ha'c: (a' < c).
    have: a' \in [seq i <- ord_enum n | i \in p & a < i < b].
      by rewrite Hp' mem_head.
    rewrite mem_filter mem_ord_enum andbT => /and3P [Ha'p Haa' _].
    move/eqP/setP/(_ a'): Hci.
    by rewrite !inE Ha'p Haa' Ha'c.
  case Hca': (c < a').
    admit.
  move/negP/negP in Ha'c.
  move/negP/negP in Hca'.
  rewrite -!leqNgt in Ha'c Hca'.
  have Ha'c': a' = c.
    by apply/ord_inj/eqP; rewrite eqn_leq Ha'c Hca'.
  by rewrite Ha'c' Hac.
- move=> Hp.
  exists [set i | i \in a :: rcons p b].
  rewrite !inE eqxx /= mem_rcons /= !inE eqxx orbT !andbT.
  case Hab: (a == b) => /=.
    move/(path_lt Hp)/ltn_eqF: (in_last b p).
    by rewrite (eqP Hab) eqxx.
  apply/forallP => a'.
  apply/implyP.
  elim: p a Hp Hab => [|c p IH] a Hp Hab.
    rewrite /= !inE.
    case Ha'b: (a' == b) => //=.
    rewrite orbF => /eqP ->.
    apply/existsP.
    exists b.
    move: Hp => /andP [Hac _].
    rewrite !inE !eqxx orbT Hac /=.
    apply/eqP/setP => k.
    rewrite !inE.
    case Hka: (k == a).
      by rewrite (eqP Hka) ltnn.
    case Hkb: (k == b).
      by rewrite (eqP Hkb) ltnn andbF.
    done.
  move: Hp => /= /andP [Hac Hp].
  rewrite !inE => /andP [Ha'b] /= /orP [] Haa'.
    rewrite (eqP Haa') in Ha'b *.
    apply/existsP.
    exists c.
    rewrite !inE !eqxx /= orbT Hac /=.
    apply/eqP/setP => k.
    rewrite !inE.
    case Hka: (k == a).
      by rewrite (eqP Hka) ltnn.
    case Hkc: (k == c).
      by rewrite (eqP Hkc) ltnn andbF.
    rewrite /=.
    case Hkp: (k \in rcons p b).
      by rewrite (ltnNge k) (leq_eqVlt c) (path_lt Hp Hkp) orbT andbF.
    done.
  case Hcb: (c == b).
    move: (path_lt Hp (in_last b p)).
    by rewrite (eqP Hcb) ltnn.
  move: {IH} (IH c Hp Hcb).
  rewrite 4!inE Ha'b Haa' => /(_ isT) /existsP [d] /and3P [Hd Ha'd] /eqP <-.
  apply/existsP; exists d.
  rewrite inE in Hd.
  rewrite inE in_cons Hd orbT Ha'd /=.
  apply/eqP/setP => k.
  rewrite !inE.
  case Hka: (k == a) => //=.
  rewrite (eqP Hka).
  rewrite -in_cons in Haa'.
  have /ltnW: a < a'.
    by rewrite (path_lt _ Haa') //= Hac Hp.
  rewrite (ltnNge a' a) => -> //.
  by rewrite !andbF.
Admitted.
End descendant.

Record t :=
  { vars: 'I_n -> aRV;
    parent: rel 'I_n;
    topo: topological parent;
    indep: forall i j : 'I_n,
        ~~ descendant parent i j ->
        let: mkRV A X := vars i in
        let: mkRV B Y := vars j in
        let: mkRV C Z :=
           \big[aRV_join/aRV_1]_(k < n | descendant parent k i) vars k in
        X _|_ Y | Z }.
End bn.
End BN.
