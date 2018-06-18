(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div choice fintype fingraph tuple finfun bigop.
From mathcomp Require Import prime binomial ssralg finset fingroup finalg zmodp.
From mathcomp Require Import matrix.
Require Import Reals.
Require Import ssr_ext ssralg_ext ssrR Reals_ext Rbigop f2 summary.
Require Import subgraph_partition tanner tanner_partition proba channel.
Require Import checksum.

(** * Technical lemmas about the summary operator *)

(** OUTLINE
- Section dprojs_comb.
- Section dproj_F2.
- Section dprojs_subgraph.
- Section dprojs_subgraph_acyclic.
- Section dprojs_subsubgraph.
- Section dprojs_subsubgraph_acyclic.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope vec_ext_scope.
Local Open Scope ring_scope.

Section dprojs_comb.

Variables (n : nat) (F : finFieldType).

Implicit Types d t : 'rV[F]_n.
Implicit Types s : {set 'I_n}.
Implicit Types A : finType.

Definition dproj d s t :=
  locked (\row_(j < n) if j \in s then t ``_ j else d ``_ j).

Lemma sub_vec_dproj d t s' s : s \subset s' -> (dproj d s' t) # s = t # s.
Proof.
move=> s's.
rewrite /dproj; unlock; apply/rowP => i; rewrite !mxE; case: ifPn => //.
move/subsetP: s's => /(_ (enum_val i)); by rewrite enum_valP => ->.
Qed.

Lemma dproj_out d t s i : i \notin s -> (dproj d s t) ``_ i = d ``_i.
Proof. move=> H; by rewrite /dproj; unlock; rewrite mxE (negbTE H). Qed.

Lemma dproj_in d t s i : i \in s -> (dproj d s t) ``_ i = t ``_i.
Proof. move=> H; by rewrite /dproj; unlock; rewrite mxE H. Qed.

Lemma freeon_dproj d t s : freeon s d (dproj d s t).
Proof.
apply/forallP => n1; rewrite in_setC; apply/implyP => n1s; by rewrite dproj_out.
Qed.

Lemma dprojIdef d d' t s : dproj d s (dproj d' s t) = dproj d s t.
Proof.
apply/rowP => b; case/boolP : (b \in s) => Hb; by
  [rewrite !dproj_in | rewrite dproj_out // dproj_out].
Qed.

Lemma dproj_freeon d s t : freeon s d t -> dproj d s t = t.
Proof.
move=> /= H; apply/rowP => i; case/boolP : (i \in s) => Hb; by
  [rewrite dproj_in | rewrite dproj_out // -(freeon_notin H)].
Qed.

(* family of projections with default *)
Definition dprojs d A (g : A -> {set 'I_n}) t :=
  locked [ffun a => dproj d (g a) t].

Lemma sub_vec_dprojs d t A (g : A -> {set 'I_n}) s a :
  s \subset g a -> ((dprojs d g t) a) # s = t # s.
Proof. rewrite /dprojs; unlock => H0; by rewrite ffunE sub_vec_dproj. Qed.

Lemma freeon_dprojs d t A (g : A -> {set 'I_n}) a : freeon (g a) d ((dprojs d g t) a).
Proof. rewrite /dprojs; unlock; rewrite ffunE; by rewrite freeon_dproj. Qed.

Lemma dprojs_in d t A (g : A -> {set 'I_n}) n0 a :
  n0 \in g a -> ((dprojs d g t) a) ``_ n0 = t ``_ n0.
Proof. move=> ?; by rewrite /dprojs; unlock; rewrite ffunE dproj_in. Qed.

Lemma dprojs_out d t A (g : A -> {set 'I_n}) n0 a :
  n0 \notin g a -> ((dprojs d g t) a) ``_ n0 = d ``_n0.
Proof. move=> ?; by rewrite /dprojs; unlock; rewrite ffunE dproj_out. Qed.

(* combination of projections *)
Definition comb d A (f : {ffun A -> 'rV[F]_n}) (g : A -> {set 'I_n}) :=
  locked (\row_(j < n) (if [pick a | j \in g a] is Some a then (f a) ``_ j else d ``_ j)).

Lemma comb_in d A (f : {ffun A -> 'rV[F]_n}) (g : A -> {set 'I_n}) n1 a :
  [pick a | n1 \in g a] = Some a -> (comb d f g) ``_ n1 = (f a) ``_ n1.
Proof. by rewrite /comb; unlock; rewrite mxE => ->. Qed.

Lemma comb_out d A (f : {ffun A -> 'rV[F]_n}) (g : A -> {set 'I_n}) n1 :
  [pick a | n1 \in g a] = None-> (comb d f g) ``_ n1 = d ``_ n1.
Proof. move=> Hn1; rewrite /comb; unlock => /=; by rewrite mxE Hn1. Qed.

Lemma comb_dprojs_not_in_partition d A (g : A -> {set 'I_n}) n0 t :
  [forall a, n0 \notin g a] ->
  (comb d (dprojs d g t) g) ``_ n0 = d ``_ n0.
Proof.
move=> /forallP H0.
rewrite comb_out //.
case: pickP => // m0.
by rewrite (negbTE (H0 _)).
Qed.

Lemma comb_dprojs d A (g : A -> {set 'I_n}) t :
  (forall n0, t ``_ n0 = d ``_ n0 \/ exists a, n0 \in g a) ->
  comb d (dprojs d g t) g = t.
Proof.
move=> K.
apply/rowP => n1.
rewrite /comb; unlock => /=; rewrite mxE.
case: pickP => [/= a Ha | ]; first by rewrite dprojs_in.
move=> /= Hpred0.
case: {K}(K n1) => [ //| [a Ha]].
exfalso.
move: (Hpred0 a); by rewrite Ha.
Qed.

End dprojs_comb.

Section dproj_F2.

Variable n : nat.

Implicit Types d t : 'rV['F_2]_n.
Implicit Types s : {set 'I_n}.

Lemma checksubsum_dproj d t s s0 : (forall i, i \in s :\: s0 -> t ``_ i = d ``_ i) ->
  \delta s (dproj d s0 t) = \delta s t.
Proof.
move=> H1.
rewrite /checksubsum; congr (_ == Zp0).
apply eq_big => n1 // Hn1.
case/boolP : (n1 \in s0) => [H|H]; first by rewrite dproj_in.
by rewrite dproj_out // H1 // in_setD H.
Qed.

Lemma checksubsum_dprojD1 d n0 t s : t ``_ n0 = d ``_ n0 ->
  \delta s (dproj d (s :\ n0) t) = \delta s t.
Proof.
move=> ?; rewrite checksubsum_dproj // => n1.
by rewrite in_setD in_setD1 negb_and negbK => /andP[] /orP[/eqP -> //|/negbTE ->].
Qed.

Lemma checksubsum_dproj_freeon d s0 s t : freeon s0 d t ->
  \delta s (dproj d s0 t) = \delta s t.
Proof.
move=> Ht.
rewrite checksubsum_dproj // => i; rewrite in_setD => /andP[H1 H2].
by rewrite (freeon_notin Ht).
Qed.

End dproj_F2.

Section dprojs_subgraph.

Variables (m n : nat) (H : 'M['F_2]_(m, n)).
Hypothesis Hconnected : forall a b, connect (tanner_rel H) a b.
Local Notation "''V(' x ',' y ')'" := (Vgraph H x y).
Local Notation "''F(' x ',' y ')'" := (Fgraph H x y).
Local Notation "''V'" := (Vnext H).
Local Notation "''F'" := (Fnext H).

Implicit Types d t : 'rV['F_2]_n.

Definition sgraph n0 m0 := 'V(m0, n0) :\ n0.

(* family of projections; for each m1 : 'I_m, returns a projection on `V(m1, n0) :\ n0 *)
Definition dprojs_V d n0 t : {ffun 'I_m -> 'rV_n} := dprojs d (sgraph n0) t.

Lemma pfamily_dprojs_V d n0 t : dprojs d (sgraph n0) t \in
  pfamily d ('F n0) (fun m0 => [pred t | freeon (sgraph n0 m0) d t]).
Proof.
apply/pfamilyP; split.
  apply/supportP => m0 n0m0.
  apply/rowP => n1.
  rewrite dprojs_out //.
  apply: contra n0m0.
  rewrite FnextE; exact: mem_VgraphD1_Vnext.
move=> m0 m0n0; by rewrite inE (freeon_dprojs _ _ (sgraph n0)).
Qed.

Definition comb_V d n0 f := comb d f (sgraph n0).

Lemma comb_dprojs_V d i t : t ``_ i = d ``_ i -> comb_V d i (dprojs_V d i t) = t.
Proof.
move=> H0.
rewrite /comb_V /dprojs_V comb_dprojs // => n1.
case/boolP: (i == n1) => [/eqP <-|in1]; [by left | right].
move: (cover_Vgraph_part_vnode Hconnected i) => Hcover.
have : n1 \in cover (Vgraph_part_vnode H i) :\ i by rewrite Hcover !inE eq_sym in1.
rewrite in_setD1 eq_sym in1 /=.
case/bigcupP => /= s /imsetP[m1 Hm1 ->{s} Hn1]; by exists m1.
Qed.

Lemma comb_dprojs_V_not_in_partition d n0 t n1 : (forall m0, n1 \notin sgraph n0 m0) ->
  (comb_V d n0 (dprojs_V d n0 t)) ``_ n1 = d ``_ n1.
Proof.
move=> H0; rewrite /comb_V /dprojs_V comb_dprojs_not_in_partition //.
apply/forallP => m0; by rewrite H0.
Qed.

Lemma comb_V_support d (f : {ffun 'I_m -> 'rV_n}) n0 n1 (s : {set 'I_m}) :
  d.-support f \subset s ->
  ~~ [exists m0, (m0 \in s) && (n1 \in 'V(m0, n0))] ->
  (comb_V d n0 f) ``_ n1 = d ``_ n1.
Proof.
move=> H0 H1.
rewrite /comb_V /comb; unlock; rewrite mxE.
case: pickP => // m1 Hm1.
case/boolP : (m1 \in s) => m1s.
  move: H1; rewrite negb_exists => /forallP/(_ m1).
  rewrite m1s /=.
  by case/setD1P : Hm1 => _ ->.
by move/supportP : H0 => /(_ _ m1s) => ->.
Qed.

Lemma checksubsum_dprojs_V d n0 t m0 m1 :
  m1 \in 'F(m0, n0) -> t ``_ n0 = d ``_ n0 ->
  \delta ('V m1) ((dprojs_V d n0 t) m0) = \delta ('V m1) t.
Proof.
move=> Hm1 tn0dn0.
rewrite /dprojs_V /dprojs; unlock; rewrite ffunE. (* NB: really unlock? *)
rewrite checksubsum_dproj // => n2.
rewrite in_setD => /andP[].
rewrite in_setD1 negb_and negbK.
case/boolP : (n2 == n0) => [/eqP -> //|/= n2n0 Hn2 Hn2'].
move: (Fgraph_Vnext_Vgraph Hm1 Hn2' n2n0).
by rewrite (negbTE Hn2).
Qed.

Lemma freeon_comb_dprojs_V d t n0 : freeon (setT :\ n0) d (comb_V d n0 (dprojs_V d n0 t)).
Proof.
rewrite -freeon_all comb_dprojs_V_not_in_partition // => m0; by rewrite in_setD1 eqxx.
Qed.

End dprojs_subgraph.

Section dprojs_subgraph_acyclic.

Variables (m n : nat) (H : 'M['F_2]_(m, n)).
Hypothesis Hconnected : forall a b, connect (tanner_rel H) a b.
Local Notation "''V(' x ',' y ')'" := (Vgraph H x y).
Local Notation "''F(' x ',' y ')'" := (Fgraph H x y).
Local Notation "''V'" := (Vnext H).
Local Notation "''F'" := (Fnext H).

Implicit Types d : 'rV['F_2]_n.

Hypothesis Hacyclic : acyclic (tanner_rel H).

Lemma comb_V_in d (f : {ffun 'I_m -> 'rV_n}) n0 m0 n1 :
  n1 \in 'V(m0, n0) :\ n0 -> (comb_V H d n0 f) ``_ n1 = (f m0) ``_ n1.
Proof.
move=> Hn1; rewrite /comb_V (@comb_in _ _ _ _ f _ _ m0) //.
case: pickP => [m1 Hm1 | ].
  case/boolP : (m0 == m1) => [/eqP -> // | m0m1].
  have {Hm1}Hm1 : n1 \in 'V(m1, n0).
    move: Hm1; rewrite in_setD1; by case/andP.
  move: Hn1; rewrite in_setD1; case/andP => n1n0 Hn1.
  move: (disjoint_Vgraph Hacyclic n1n0 m0m1 Hn1); by rewrite Hm1.
move/(_ m0); by rewrite Hn1.
Qed.

Lemma dprojs_comb_V d n0 (g : 'I_n -> {set 'I_m}) (f : {ffun 'I_m -> 'rV_n}) :
  f \in pfamily d (g n0) (fun i => freeon ('V(i, n0) :\ n0) d) ->
  dprojs_V H d n0 (comb_V H d n0 f) = f.
Proof.
rewrite inE /= => /forallP => /= Hf.
apply/ffunP => /= m0.
apply/rowP => n1.
case/boolP : (n1 \in 'V( m0, n0) :\ n0) => Hn1.
  rewrite dprojs_in //.
  by rewrite (@comb_V_in _ _ _ m0) //.
rewrite dprojs_out //.
move: (Hf m0).
case: ifP => [_ | _ /eqP -> //].
rewrite inE.
by move/freeon_notin => ->.
Qed.

Local Open Scope summary_scope.
Local Open Scope R_scope.

Lemma rmul_rsum_commute0 d n0 (B : finType) (t : 'rV[B]_n)
  (W : forall m, 'rV_m -> 'rV_m -> R) (* channel *)
  (F : 'I_m -> 'rV_n -> R)
  (HF : forall m1 m0 (t' : 'rV_n), m1 \in 'F(m0, n0) -> t' ``_ n0 = d ``_ n0 -> F m1 ((dprojs_V H d n0 t') m0) = F m1 t') :
  (\rprod_(m0 in 'F n0) \rsum_(t' # 'V(m0, n0) :\ n0 , d)
    W _ (t # 'V(m0, n0) :\ n0) (t' # 'V(m0, n0) :\ n0) * (\rprod_(m1 in 'F(m0, n0)) F m1 t') =
  \rsum_(t' # setT :\ n0 , d) \rprod_(m0 in 'F n0)
    W _ (t # 'V(m0, n0) :\ n0) (t' # 'V(m0, n0) :\ n0) * (\rprod_(m1 in 'F(m0, n0)) F m1 t'))%R.
Proof.
rewrite (big_distr_big_dep d [pred x in 'F n0] (fun i => freeon ('V(i, n0) :\ n0) d)) [LHS]/=.
rewrite (reindex_onto (dprojs_V H d n0) (comb_V H d n0)); last first.
  rewrite /= => f Hf; by apply (@dprojs_comb_V d n0 (fun n => 'F n)).
rewrite [LHS]/=.
apply/esym/eq_big.
- move=> /= t'.
  case Hlhs : (freeon _ _ t').
    apply/esym.
    rewrite comb_dprojs_V => //; last first.
      by rewrite (freeon_notin Hlhs) // !inE eqxx.
    by rewrite eqxx andbT pfamily_dprojs_V.
  apply/esym/negbTE.
  move/negbT : Hlhs; apply contra.
  case/andP => _ /eqP <-.
  by rewrite freeon_comb_dprojs_V.
- move=> /= t' Ht'.
  apply eq_bigr => m0 Hm0.
  congr (_ * _)%R.
  + by rewrite /dprojs_V sub_vec_dprojs.
  + apply eq_bigr => m1 Hm1.
    by rewrite HF // -(freeon_notin Ht') //= !inE eqxx.
Qed.

End dprojs_subgraph_acyclic.

Section dprojs_subsubgraph.

Variables (m n : nat).
Variable H : 'M['F_2]_(m, n).
Local Notation "'`V(' x ',' y ')'" := (Vgraph H x y).
Local Notation "'`F(' x ',' y ')'" := (Fgraph H x y).
Local Notation "''V'" := (Vnext H).
Local Notation "'`F'" := (Fnext H).

Implicit Types d : 'rV['F_2]_n.

Definition ssgraph m0 n0 n1 :=
  [set n2 | (n1 \in 'V m0 :\ n0) && [exists m1, (m1 \in `F n1 :\ m0) && (n2 \in `V(m1, n1))]].

(* family of projections; for each n1 : 'I_n, returns a projection on ssgraph m0 n0 n1 *)
Definition dprojs_V2 d m0 n0 t : {ffun 'I_n -> 'rV_n} := dprojs d (ssgraph m0 n0) t.

Definition comb_V2 d m0 n0 (f : {ffun 'I_n -> 'rV_n}) := comb d f (ssgraph m0 n0).

Lemma sub_vec_dprojs_V2 d m0 n0 t n1 m1 : n1 \in 'V m0 :\ n0 -> m1 \in `F n1 :\ m0 ->
  (dprojs_V2 d m0 n0 t) n1 # `V(m1, n1) :\ n1 = t # `V(m1, n1) :\ n1.
Proof.
move=> Hn1 Hm1; rewrite /dprojs_V2 sub_vec_dprojs //.
apply/subsetP => n2 Hn2.
rewrite inE /ssgraph Hn1 /=; apply/existsP; exists m1; rewrite Hm1.
by move: Hn2; rewrite in_setD1 => /andP[].
Qed.

Lemma checksubsum_dprojs_V2 d m0 n0 (t' t : 'rV_n) n1 m1 m2
  (Hn1 : n1 \in 'V m0 :\ n0) (Hm1 : m1 \in `F n1 :\ m0) (Hm2 : m2 \in `F(m1, n1)) :
  dprojs_V2 d m0 n0 t \in pfamily t' ('V m0 :\ n0)
    (fun n2 => [pred t'' | (dprojs_V H d n2 t'' \in pfamily d (`F n2 :\ m0)
                             (fun m2 => freeon (`V(m2, n2) :\ n2) d)) &&
                           (comb_V H d n2 (dprojs_V H d n2 t'') == t'')]) ->
  \delta ('V m2) ((dprojs_V H d n1 ((dprojs_V2 d m0 n0 t) n1)) m1) =
  \delta ('V m2) t.
Proof.
move=> H0; rewrite /checksubsum; congr (_ == _).
apply eq_bigr => n2 n2m2.
rewrite /dprojs_V /dprojs_V2.
case/boolP : (n2 \in `V( m1, n1) :\ n1) => [Hn2|].
  rewrite dprojs_in // dprojs_in //inE /ssgraph Hn1 /=.
  apply/existsP; exists m1; rewrite Hm1.
  by case/setD1P : Hn2.
move=> Hn2; rewrite dprojs_out //; move: Hn2.
rewrite in_setD1 negb_and negbK.
case/boolP : (n2 == n1) => [/eqP ?|/=]; last first.
  by move/(Fgraph_Vnext_Vgraph Hm2 n2m2) => ->.
subst n2 => /=.
case/pfamilyP : H0 => H0 /(_ _ Hn1).
rewrite inE => /andP[_].
move/eqP/rowP/(_ n1).
rewrite comb_dprojs_V_not_in_partition; last first.
  by move=> m3; rewrite in_setD1 eqxx.
rewrite /dprojs_V2 dprojs_in // inE Hn1 /=.
apply/existsP; exists m1; by rewrite Hm1 /= root_in_Vgraph.
Qed.

End dprojs_subsubgraph.

Section dprojs_subsubgraph_acyclic.

Variables (m n : nat).
Variable H : 'M['F_2]_(m, n).
Local Notation "'`V(' x ',' y ')'" := (Vgraph H x y).
Local Notation "'`F(' x ',' y ')'" := (Fgraph H x y).
Local Notation "''V'" := (Vnext H).
Local Notation "'`F'" := (Fnext H).

Implicit Types d : 'rV['F_2]_n.

Hypothesis Hacyclic : acyclic (tanner_rel H).

Lemma comb_dprojs_V2_in_partition d t m0 n0 n1 :
  (exists n2, n1 \in ssgraph H m0 n0 n2) ->
  (comb_V2 H d m0 n0 (dprojs_V2 H d m0 n0 t)) ``_ n1 = t ``_ n1.
Proof.
case=> n2 Hn2.
have [n2' Hn2'] : exists n2', [pick a | n1 \in ssgraph H m0 n0 a] = Some n2'.
  case: pickP Hn2 => [x Hx _ | /(_ n2) -> //]; by exists x.
rewrite (@comb_in _ _ _ _ _ _ _ n2') //.
rewrite dprojs_in; first by done.
case: pickP Hn2'.
  by move=> x hx [<-].
move=> _ ?.
by exfalso.
Qed.

Lemma comb_dprojs_V2_not_in_subgraph d t n0 m0 (m0n0 : n0 \in 'V m0) n1 :
  n1 \notin `V(m0, n0) -> (comb_V2 H d m0 n0 (dprojs_V2 H d m0 n0 t)) ``_ n1 = d ``_ n1.
Proof.
move=> Hn1.
rewrite /comb_V2 comb_out //.
case: pickP => [ n2 | // ].
rewrite inE => /andP[Hn2 H0].
suff : n1 \in `V(m0, n0) by rewrite (negbTE Hn1).
case/existsP : H0 => [m1 /andP[H0 H1]].
by apply: (@Vgraph_inclusion _ _ _ Hacyclic n2 m0 n0 m1).
Qed.

Lemma comb_dprojs_V2_Vnext d t n0 m0 (m0n0 : n0 \in 'V m0) :
  (comb_V2 H d m0 n0 (dprojs_V2 H d m0 n0 t)) ``_ n0 = d ``_ n0.
Proof.
rewrite /comb_V2 comb_out //.
case: pickP => [ n2 | // ].
rewrite inE => /andP[Hn2 /existsP[m1 /andP[Hm1]]].
move/(notin_Vgraph Hacyclic) : m0n0.
by move/(_ _ _ Hn2 Hm1) => /negbTE => ->.
Qed.

Lemma freeon_trans d m0 n0 (m0n0 : n0 \in 'V m0) d' t (Ht : freeon ('V m0 :\ n0) d d') :
  freeon (`V(m0, n0) :\ n0) d t ->
  freeon (`V(m0, n0) :\ n0) d' t.
Proof.
move=> Hlhs2.
apply/forallP => /= n1.
rewrite in_setC in_setD1 negb_and negbK.
apply/implyP => /orP[/eqP ->{n1}|].
  rewrite -(freeon_notin Hlhs2) ?in_setD1 ?eqxx //.
  by rewrite (freeon_notin Ht) // !inE eqxx.
move=> Hn1.
rewrite -(freeon_notin Hlhs2) ?in_setD1 ?(negbTE Hn1) ?andbF //.
rewrite (freeon_notin Ht) //.
apply: contra Hn1 => Hn1.
move/Fnext_Vnext_Vgraph : m0n0.
move/subsetP/(_ _ Hn1).
rewrite in_setD1.
by case/andP.
Qed.

Lemma comb_V2_freeon d m0 n0 (m0n0 : n0 \in 'V m0) t' t (Ht : freeon ('V m0 :\ n0) d t') :
  comb_V2 H d m0 n0 (dprojs_V2 H d m0 n0 t) = t ->
  freeon (`V(m0, n0) :\ n0) t' t.
Proof.
move=> <-.
apply: (freeon_trans m0n0 Ht).
apply/forallP => /= n1.
rewrite in_setC in_setD1 negb_and negbK.
apply/implyP => /orP[/eqP ->{n1}|].
  by rewrite comb_dprojs_V2_Vnext // (freeon_notin Ht) // !inE eqxx.
move=> Hn1.
by rewrite comb_dprojs_V2_not_in_subgraph.
Qed.

Hypothesis Hconnected : forall a b, connect (tanner_rel H) a b.

Lemma dprojs_V2_pfamily d m0 n0 (m0n0 : n0 \in 'V m0) t d'
  (d'td : dproj d' ('V m0 :\ n0) t = d) (d't : freeon (`V(m0, n0) :\ n0) d' t) :
  dprojs_V2 H d m0 n0 t \in pfamily d ('V m0 :\ n0)
    (fun n1 => [pred t0 | (dprojs_V H d n1 t0
      \in pfamily d (`F n1 :\ m0) (fun m1 => freeon (`V(m1, n1) :\ n1) d)) &&
        (comb_V H d n1 (dprojs_V H d n1 t0) == t0)]).
Proof.
apply/pfamilyP; split.
  apply/supportP => n1.
  rewrite 2!inE /= negb_and negbK.
  case/orP => [ /eqP ->{n1}| m0n1].
    apply/rowP => n2 /=.
    by rewrite /dprojs_V2 dprojs_out // inE /ssgraph 2!inE eqxx.
  apply/rowP => n2 /=.
  by rewrite /dprojs_V2 dprojs_out // inE /ssgraph in_setD1 (negbTE m0n1) andbF.
move=> /= n1 Hn1.
rewrite {1}/in_mem /=.
apply/andP; split.
  apply/familyP => /= m1.
  rewrite {1}/in_mem /=.
  rewrite inE /= in_set1 /=.
  case: ifPn.
    case/andP => m1m0 m1n1.
    apply/forallP => n2.
    apply/implyP => Hn2.
    rewrite in_setC in Hn2.
    by rewrite /dprojs_V2 dprojs_out.
  rewrite negb_and negbK.
  case/orP => [ | m1n1 /=].
    move/eqP => -> {m1} /=.
    rewrite /dprojs_V /dprojs_V2.
    apply/eqP/rowP => n2.
    case/boolP : (n2 \in `V( m0, n1) :\ n1) => K; last by rewrite dprojs_out.
    rewrite dprojs_in //.
    case/boolP : (n2 \in ssgraph H m0 n0 n1) => L; last first.
      by rewrite dprojs_out.
    rewrite dprojs_in //.
    move: L; rewrite inE => /andP[L].
    case/existsP => m1 /andP[Hm1 n2m1n1].
    rewrite -d'td.
    case/boolP : (n2 \in 'V m0 :\ n0) => n2m0n0; first by rewrite dproj_in.
    rewrite dproj_out // (freeon_notin d't) //.
    rewrite in_setD1 negb_and negbK.
    rewrite /= in_setD1 negb_and negbK in n2m0n0.
    case/orP : n2m0n0 => [->// | n2m0].
    suff : n2 \notin `V(m0, n0) by move => ->; rewrite orbC.
    apply/negP.
    by apply: disjoint_Vgraph2 n2m1n1 n2m0.
  apply/eqP/rowP => n2.
  rewrite dprojs_out //.
  apply/negP.
  rewrite /= in_setD1.
  case/andP => Hn2' Hn2.
  move/negP : Hn2'; apply.
  rewrite Vgraph_set1 in Hn2.
    by rewrite in_set1 in Hn2.
  by rewrite -FnextE.
rewrite comb_dprojs_V //.
case/boolP: [exists m1, (m1 \in `F n1 :\ m0) && (n1 \in `V( m1, n1))] => X.
  rewrite /dprojs_V2 dprojs_in //; last by rewrite inE /ssgraph Hn1 X.
  by rewrite -d'td dproj_in.
by rewrite /dprojs_V2 dprojs_out // inE /ssgraph Hn1.
Qed.

Lemma comb_dprojs_V2 d m0 n0 (m0n0 : n0 \in 'V m0) d' t
  (d'td : dproj d' ('V m0 :\ n0) t = d) (d't : freeon (`V(m0, n0) :\ n0) d' t) :
  comb_V2 H d m0 n0 (dprojs_V2 H d m0 n0 t) == t.
Proof.
apply/eqP/rowP => n1.
case/boolP : (n1 == n0) => [/eqP ?|n1n0].
  subst n1.
  rewrite comb_dprojs_V2_Vnext // -d'td dproj_out ?in_setD1 ?eqxx //.
  move/rowP : d'td => /(_ n0).
  by rewrite (freeon_notin d't) // in_setD1 eqxx.
case/boolP : [exists n2, n1 \in ssgraph H m0 n0 n2] => [/existsP[n2 Hn2]|].
  rewrite comb_dprojs_V2_in_partition //; by exists n2.
rewrite negb_exists => H0.
rewrite comb_out; last first.
  case: pickP => // => x.
  by move/forallP : H0 => /(_ x) /negbTE ->.
rewrite -d'td.
case/boolP : (n1 \in 'V m0 :\ n0) => K.
  by rewrite dproj_in.
rewrite dproj_out //.
move/forallP: d't => /(_ n1).
rewrite in_setC in_setD1 n1n0 /=.
have -> : n1 \notin `V(m0, n0).
  apply/negP => n1m0n0.
  rewrite in_setD1 negb_and negbK (negbTE n1n0) orFb in K.
  case: (Vgraph_decompose m0n0 n1m0n0 n1n0 K) => n2 [] Hn2 [m1 [H0' H1']].
  move/forallP in H0.
  move: (H0 n2) => /=; rewrite /ssgraph Hn2 /= inE.
  by rewrite negb_exists => /forallP/(_ m1); rewrite H0' /= H1'.
by rewrite implyTb => /eqP.
Qed.

Hypothesis tannerH_simple : simple (tanner_rel H).

Lemma comb_dprojs_V2_Vnext_dangling d m0 n0 t n1 (n1m0 : n1 \in 'V m0) :
  ~~ [exists m1, (m1 \in `F n1 :\ m0)] ->
  (comb_V2 H d m0 n0 (dprojs_V2 H d m0 n0 t)) ``_ n1 = d ``_ n1.
Proof.
move=> tmp.
rewrite /comb_V2 /dprojs_V2.
rewrite /comb; unlock; rewrite mxE. (* xxx *)
case: pickP => //.
move=> n1'; rewrite inE => /andP[Hn1' /existsP[m1' Hm1']].
case/boolP : (n1 \in ssgraph H m0 n0 n1') => [|L]; last first.
  by rewrite dprojs_out.
rewrite dprojs_in; last first.
  rewrite /ssgraph Hn1' /= inE.
  apply/existsP; exists m1'; by rewrite Hm1'.
rewrite /ssgraph Hn1' /=.
case/andP: Hm1' => Hm1'.
rewrite 3!inE; case/orP => [/eqP ?|].
  subst n1'.
  move=> abs.
  rewrite inE in abs.
  exfalso.
  move/negP : tmp; apply.
  case/existsP : abs => m1 /andP[abs _].
  apply/existsP; by exists m1.
rewrite inE.
case/andP => n1'm1' /connectP [] /= p.
case/shortenP => p' Hp' Hun p'p Hlast.
exfalso.
apply (@Hacyclic [:: inl m0, inr n1', inl m1' & p'] isT).
apply: uniq_path_ucycle_extend_1 => //.
- by rewrite /= -VnextE; move: Hn1'; rewrite in_setD1 => /andP[].
- rewrite cat_path Hp' /= andbT -Hlast.
  rewrite exceptE /= andbT -VnextE n1m0 /= eq_sym.
  rewrite (path_except_neq _ Hp') // Hlast.
  destruct p' => //=; by rewrite mem_last.
- rewrite -(cat1s (inl m1')) catA cat_uniq Hun /= andbT orbF.
  rewrite inE /= negb_or.
  apply/andP; split.
    apply/eqP; case => ?; subst m1'.
    by rewrite in_setD1 eqxx in Hm1'.
  apply/negP => Hx.
  case/splitPr : Hx => p1 p2 in Hp' Hun p'p Hlast.
  rewrite last_cat /= in Hlast.
  apply (@Hacyclic [:: inl m0, inr n1', inl m1' & p1] isT).
  apply: uniq_path_ucycle_extend_1 => //.
  + by rewrite /= -VnextE; move: Hn1'; rewrite in_setD1 => /andP[].
  + rewrite -(cat1s (inl m0)) catA cat_path in Hp'; by case/andP : Hp'.
  + rewrite -(cat1s (inl m1')) -(cat1s (inl m0)) 2!catA cat_uniq in Hun; by case/andP : Hun.
Qed.

Lemma dproj_prop d m0 n0 d' t (d'd : freeon ('V m0 :\ n0) d' d)
  (Hpfamily : dprojs_V2 H d m0 n0 t
            \in pfamily d ('V m0 :\ n0)
                  (fun n1 => [pred t0 |
                   (dprojs_V H d n1 t0
                      \in pfamily d (`F n1 :\ m0)
                            (fun m1 => freeon (`V(m1, n1) :\ n1) d)) &&
                   (comb_V H d n1 (dprojs_V H d n1 t0) == t0)]))
  (Ht : comb_V2 H d m0 n0 (dprojs_V2 H d m0 n0 t) = t) :
  dproj d' ('V m0 :\ n0) t == d.
Proof.
apply/eqP/rowP => n1.
case/boolP : (n1 \in 'V m0 :\ n0) => K; last first.
  by rewrite dproj_out // (freeon_notin d'd).
rewrite dproj_in //.
move: K.
rewrite /= in_setD1.
case/andP => n1n0 Hn1.
case/pfamilyP : Hpfamily => _ /(_ n1).
rewrite inE in_set1 n1n0 /= => /(_ Hn1).
rewrite {1}/in_mem /=.
case/andP => /pfamilyP[Hlhs11 Hlhs12].
rewrite /comb_V /dprojs_V /dprojs_V2.
move/eqP/(congr1 (fun x : 'rV_n => x ``_ n1)).
rewrite /comb; unlock => /=.
rewrite mxE.
case: pickP => [m1 Hm1 | _].
  by rewrite in_setD1 eqxx in Hm1.
case/boolP : (n1 \in ssgraph H m0 n0 n1) => [L|L].
  by rewrite dprojs_in.
rewrite dprojs_out //.
move: L.
rewrite /ssgraph inE negb_and in_setD1 Hn1 andbT negbK (negbTE n1n0) orFb.
move=> tmp _.
rewrite -{}Ht comb_dprojs_V2_Vnext_dangling //.
apply: contra tmp => /existsP[m1 Hm1].
apply/existsP; exists m1; rewrite Hm1 /=; exact: root_in_Vgraph.
Qed.

Lemma dprojs_V2_in d m0 n0 t n1 (Hn1 : n1 \in 'V m0 :\ n0)
  (Ht : comb_V2 H d m0 n0 (dprojs_V2 H d m0 n0 t) = t) :
  ((dprojs_V2 H d m0 n0 t) n1) ``_ n1 = t ``_ n1.
Proof.
case/boolP : [exists m1, (m1 \in `F n1 :\ m0)] => [/existsP[m1 K]|K].
  rewrite /dprojs_V2 dprojs_in // inE /ssgraph Hn1 /=.
  by apply/existsP; exists m1; rewrite K root_in_Vgraph.
rewrite dprojs_out /=; last first.
  rewrite inE /ssgraph Hn1 /=.
  apply: contra K => /existsP[x /andP[Hx _]].
  by apply/existsP; exists x.
rewrite -Ht.
rewrite /comb_V2 /dprojs_V2 /= /comb; unlock; rewrite mxE. (* xxx *)
case: pickP => // n3.
rewrite inE => /andP[Hn3 /existsP[m1 /andP[Hm1 Hn1'']]].
rewrite negb_exists in K.
suff n31 : n3 = n1.
  move/forallP : K => /(_ m1).
  by rewrite -{1}n31 Hm1.
move: Hn1''.
rewrite inE in_set1 /= => /orP[/eqP //|].
rewrite 2!inE.
case/andP => m1n3 /connectP [] /= p.
case/shortenP => p' Hp' Hun pp' Hlast.
exfalso.
apply (@Hacyclic [:: inl m0, inr n3, inl m1 & p'] isT).
apply: uniq_path_ucycle_extend_1 => //.
- by rewrite /= -VnextE; move: Hn3; rewrite in_setD1 => /andP[].
- rewrite cat_path Hp' /= andbT -Hlast exceptE /= andbT -VnextE.
  move: Hn1; rewrite in_setD1 => /andP[_ -> /=].
  rewrite eq_sym (path_except_neq _ Hp') // Hlast.
  destruct p' => //=; by rewrite mem_last.
- rewrite -(cat1s (inl m1)) catA cat_uniq Hun /= andbT orbF.
  rewrite inE negb_or.
  apply/andP; split.
    apply/eqP; case => ?; subst m1.
    by rewrite in_setD1 eqxx in Hm1.
  apply/negP => Hx.
  case/splitPr : Hx => p1 p2 in Hp' Hun pp' Hlast.
  rewrite last_cat /= in Hlast.
  apply (@Hacyclic [:: inl m0, inr n3, inl m1 & p1] isT).
  apply: uniq_path_ucycle_extend_1 => //.
  + by rewrite /= -VnextE; move: Hn3; rewrite in_setD1 => /andP[].
  + rewrite -(cat1s (inl m0)) catA cat_path last_cat /= in Hp'; by case/andP : Hp'.
  + rewrite -(cat1s (inl m1)) -(cat1s (inl m0)) 2!catA cat_uniq in Hun; by case/andP : Hun.
Qed.

Local Open Scope channel_scope.
Local Open Scope proba_scope.

Lemma rprod_rsum_commute d (B : finType) (x : 'rV_n) (W: `Ch_1('F_2, B)) m0 n0 (m0n0 : n0 \in 'V m0) :
  let pr n1 t := (dprojs_V H d n1 t \in pfamily d (`F n1 :\ m0)
                   (fun m1 => freeon (`V(m1, n1) :\ n1) d)) &&
                 (comb_V H d n1 (dprojs_V H d n1 t) == t) in
  let g := dprojs_V2 H d m0 n0 in
  let g' := comb_V2 H d m0 n0 in
  (\rprod_(n1 in 'V m0 :\ n0)
    \rsum_(t | pr n1 t)
      (W (t ``_ n1) (x ``_ n1) *
         \rprod_(m1 in `F n1 :\ m0)
           W ``(x # `V(m1, n1) :\ n1 | ((dprojs_V H d n1 t) m1) # `V(m1, n1) :\ n1) *
           (\rprod_(m2 in `F(m1, n1)) INR (\delta ('V m2) ((dprojs_V H d n1 t) m1)))) =
  \rsum_(t | (g t \in pfamily d ('V m0 :\ n0) pr) && (g' (g t) == t))
    \rprod_(n1 in 'V m0 :\ n0)
       W ((g t n1) ``_ n1) (x ``_ n1) *
         (\rprod_(m1 in `F n1 :\ m0)
           W ``(x # `V(m1, n1) :\ n1 | ((dprojs_V H d n1 (g t n1)) m1) # `V(m1, n1) :\ n1) *
         (\rprod_(m2 in `F(m1, n1)) INR (\delta ('V m2) ((dprojs_V H d n1 (g t n1)) m1)))))%R.
Proof.
move=> pr g g'.
rewrite (big_distr_big_dep d) /=.
rewrite (reindex_onto (dprojs_V2 H d m0 n0) (comb_V2 H d m0 n0)) //.
move=> /= t' Ht'.
rewrite /dprojs_V2 /comb_V2.
apply/ffunP => /= n1.
apply/rowP => n2.
case/boolP : (n2 \in ssgraph H m0 n0 n1).
  rewrite inE; case/andP => Hn1 /existsP [] m1 Hm1.
  rewrite dprojs_in => /=; last first.
    rewrite /ssgraph Hn1 /= inE.
    apply/existsP; exists m1; by rewrite Hm1.
  move H0 : [pick a | n2 \in ssgraph H m0 n0 a] => [n1'|]; last first.
    case: pickP H0 => //.
    move/(_ n1); rewrite inE Hn1 /= => /negbT; rewrite negb_exists => /forallP/(_ m1).
    by rewrite Hm1.
  have ? : n1' = n1.
    case: pickP H0 => // x0.
    rewrite inE => /andP[Hn1' H0].
    move: H0 => /existsP[m1' /andP[Hm1' Hn2']].
    case/andP : Hm1 => Hm1 Hn2 [<-].
    by rewrite (Vgraph_id Hacyclic m0n0 Hn1 Hn1' Hm1 Hm1' Hn2 Hn2').
  subst n1'.
  by rewrite (@comb_in _ _ d _ t' (ssgraph H m0 n0) _ n1).
rewrite inE negb_and.
case/orP => [Hn1|].
  rewrite dprojs_out /=; last by rewrite inE negb_and Hn1.
  case/pfamilyP : Ht' => Ht' _.
  move/supportP : Ht'.
  by move/(_ n1 Hn1) => ->.
move=> tmp.
case/boolP : (n1 \in 'V m0 :\ n0) => Hn1; last first.
  rewrite dprojs_out //; last by rewrite inE /ssgraph (negbTE Hn1).
  case/pfamilyP : (Ht').
  by move/supportP => /(_ _ Hn1) ->.
case/pfamilyP : (Ht') => _ /(_ _ Hn1).
rewrite {1}/in_mem /=.
case/andP => H1 /eqP <-.
rewrite dprojs_out //; last by rewrite inE /ssgraph Hn1.
rewrite (comb_V_support _ tmp) //; by case/pfamilyP : H1.
Qed.

End dprojs_subsubgraph_acyclic.
