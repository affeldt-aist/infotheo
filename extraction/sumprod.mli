
type __ = Obj.t

type nat =
| O
| S of nat

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

val add : nat -> nat -> nat

module Nat :
 sig
  val add : nat -> nat -> nat

  val mul : nat -> nat -> nat

  val pow : nat -> nat -> nat
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val of_succ_nat : nat -> positive
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val size_nat : positive -> nat

  val ggcdn : nat -> positive -> positive -> positive*(positive*positive)

  val ggcd : positive -> positive -> positive*(positive*positive)

  val of_nat : nat -> positive
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val max : z -> z -> z

  val min : z -> z -> z

  val to_nat : z -> nat

  val of_nat : nat -> z

  val to_pos : z -> positive

  val sgn : z -> z

  val abs : z -> z

  val ggcd : z -> z -> z*(z*z)
 end

type q = { qnum : z; qden : positive }

type dReal = float

val dRealAbstr : float -> dReal

val dRealRepr : dReal -> float

module type RbaseSymbolsSig =
 sig
  type coq_R

  val coq_Rabst : float -> coq_R

  val coq_Rrepr : coq_R -> float

  val coq_R0 : coq_R

  val coq_R1 : coq_R

  val coq_Rplus : coq_R -> coq_R -> coq_R

  val coq_Rmult : coq_R -> coq_R -> coq_R

  val coq_Ropp : coq_R -> coq_R
 end

module RbaseSymbolsImpl :
 RbaseSymbolsSig

module type RinvSig =
 sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl :
 RinvSig

type r2 = RbaseSymbolsImpl.coq_R*RbaseSymbolsImpl.coq_R

type kind =
| Kf
| Kv

type tag =
| Func
| Var of r2

type ('id, 'u, 'd) tn_tree = { node_id : 'id; node_tag : tag;
                               children : ('id, 'u, 'd) tn_tree list;
                               up : 'u; down : 'd }

val sumprod_ext :
  kind -> ('a1, unit, unit) tn_tree -> ('a1,
  RbaseSymbolsImpl.coq_R*RbaseSymbolsImpl.coq_R,
  RbaseSymbolsImpl.coq_R*RbaseSymbolsImpl.coq_R) tn_tree

val estimation_ext :
  kind -> ('a1, RbaseSymbolsImpl.coq_R*RbaseSymbolsImpl.coq_R,
  RbaseSymbolsImpl.coq_R*RbaseSymbolsImpl.coq_R) tn_tree ->
  ('a1*(RbaseSymbolsImpl.coq_R*RbaseSymbolsImpl.coq_R)) list
