
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type nat =
| O
| S of nat

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)

 let rec add n m =
   match n with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

module Nat =
 struct
  (** val add : nat -> nat -> nat **)

  let rec add n m =
    match n with
    | O -> m
    | S p -> S (add p m)

  (** val mul : nat -> nat -> nat **)

  let rec mul n m =
    match n with
    | O -> O
    | S p -> add m (mul p m)

  (** val pow : nat -> nat -> nat **)

  let rec pow n = function
  | O -> S O
  | S m0 -> mul n (pow n m0)
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double_mask (sub_mask p q0)
       | XO q0 -> succ_double_mask (sub_mask p q0)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q0 -> double_mask (sub_mask_carry p q0)
       | XO q0 -> succ_double_mask (sub_mask_carry p q0)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val size_nat : positive -> nat **)

  let rec size_nat = function
  | XI p0 -> S (size_nat p0)
  | XO p0 -> S (size_nat p0)
  | XH -> S O

  (** val ggcdn :
      nat -> positive -> positive -> positive*(positive*positive) **)

  let rec ggcdn n a b =
    match n with
    | O -> XH,(a,b)
    | S n0 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> a,(XH,XH)
             | Lt ->
               let g,p = ggcdn n0 (sub b' a') a in
               let ba,aa = p in g,(aa,(add aa (XO ba)))
             | Gt ->
               let g,p = ggcdn n0 (sub a' b') b in
               let ab,bb = p in g,((add bb (XO ab)),bb))
          | XO b0 ->
            let g,p = ggcdn n0 a b0 in let aa,bb = p in g,(aa,(XO bb))
          | XH -> XH,(a,XH))
       | XO a0 ->
         (match b with
          | XI _ -> let g,p = ggcdn n0 a0 b in let aa,bb = p in g,((XO aa),bb)
          | XO b0 -> let g,p = ggcdn n0 a0 b0 in (XO g),p
          | XH -> XH,(a,XH))
       | XH -> XH,(XH,b))

  (** val ggcd : positive -> positive -> positive*(positive*positive) **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val of_nat : nat -> positive **)

  let rec of_nat = function
  | O -> XH
  | S x -> (match x with
            | O -> XH
            | S _ -> succ (of_nat x))
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double (pos_sub p q0)
       | XO q0 -> succ_double (pos_sub p q0)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> pred_double (pos_sub p q0)
       | XO q0 -> double (pos_sub p q0)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q0 -> Zneg (XO q0)
       | XO q0 -> Zneg (Pos.pred_double q0)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n =
    add m (opp n)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val max : z -> z -> z **)

  let max n m =
    match compare n m with
    | Lt -> m
    | _ -> n

  (** val min : z -> z -> z **)

  let min n m =
    match compare n m with
    | Gt -> m
    | _ -> n

  (** val to_nat : z -> nat **)

  let to_nat = function
  | Zpos p -> Pos.to_nat p
  | _ -> O

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n0 -> Zpos (Pos.of_succ_nat n0)

  (** val to_pos : z -> positive **)

  let to_pos = function
  | Zpos p -> p
  | _ -> XH

  (** val sgn : z -> z **)

  let sgn = function
  | Z0 -> Z0
  | Zpos _ -> Zpos XH
  | Zneg _ -> Zneg XH

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x

  (** val ggcd : z -> z -> z*(z*z) **)

  let ggcd a b =
    match a with
    | Z0 -> (abs b),(Z0,(sgn b))
    | Zpos a0 ->
      (match b with
       | Z0 -> (abs a),((sgn a),Z0)
       | Zpos b0 ->
         let g,p = Coq_Pos.ggcd a0 b0 in
         let aa,bb = p in (Zpos g),((Zpos aa),(Zpos bb))
       | Zneg b0 ->
         let g,p = Coq_Pos.ggcd a0 b0 in
         let aa,bb = p in (Zpos g),((Zpos aa),(Zneg bb)))
    | Zneg a0 ->
      (match b with
       | Z0 -> (abs a),((sgn a),Z0)
       | Zpos b0 ->
         let g,p = Coq_Pos.ggcd a0 b0 in
         let aa,bb = p in (Zpos g),((Zneg aa),(Zpos bb))
       | Zneg b0 ->
         let g,p = Coq_Pos.ggcd a0 b0 in
         let aa,bb = p in (Zpos g),((Zneg aa),(Zneg bb)))
 end

type q = { qnum : z; qden : positive }

type dReal = float

(** val dRealAbstr : float -> dReal **)

let dRealAbstr = (fun x -> x)

(** val dRealRepr : dReal -> float **)

let dRealRepr = (fun x -> x)

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

module RbaseSymbolsImpl =
 struct
  type coq_R = float

  (** val coq_Rabst : float -> dReal **)

  let coq_Rabst =
    dRealAbstr

  (** val coq_Rrepr : dReal -> float **)

  let coq_Rrepr =
    dRealRepr

  (** val coq_Rquot1 : __ **)

  let coq_Rquot1 =
    __

  (** val coq_Rquot2 : __ **)

  let coq_Rquot2 =
    __

  (** val coq_R0 : coq_R **)

  let coq_R0 = 0.

  (** val coq_R1 : coq_R **)

  let coq_R1 = 1.

  (** val coq_Rplus : coq_R -> coq_R -> coq_R **)

  let coq_Rplus = (+.)

  (** val coq_Rmult : coq_R -> coq_R -> coq_R **)

  let coq_Rmult = ( *.)

  (** val coq_Ropp : coq_R -> coq_R **)

  let coq_Ropp = (~-.)

  type coq_Rlt = __

  (** val coq_R0_def : __ **)

  let coq_R0_def =
    __

  (** val coq_R1_def : __ **)

  let coq_R1_def =
    __

  (** val coq_Rplus_def : __ **)

  let coq_Rplus_def =
    __

  (** val coq_Rmult_def : __ **)

  let coq_Rmult_def =
    __

  (** val coq_Ropp_def : __ **)

  let coq_Ropp_def =
    __

  (** val coq_Rlt_def : __ **)

  let coq_Rlt_def =
    __
 end

module type RinvSig =
 sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl =
 struct
  (** val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

  let coq_Rinv = fun x -> 1. /. x

  (** val coq_Rinv_def : __ **)

  let coq_Rinv_def =
    __
 end

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

(** val sumprod_ext :
    kind -> ('a1, unit, unit) tn_tree -> ('a1,
    RbaseSymbolsImpl.coq_R*RbaseSymbolsImpl.coq_R,
    RbaseSymbolsImpl.coq_R*RbaseSymbolsImpl.coq_R) tn_tree **)

let sumprod_ext k n =
  let rec sumprod_down k0 n0 = function
  | Some p ->
    let arg0 = p::[] in
    { node_id = n0.node_id; node_tag = n0.node_tag; children =
    (let rec map = function
     | [] -> []
     | x::s' -> (let x0,_ = x in x0 (let _,y = x in y))::(map s')
     in map
          (let rec zip s t =
             match s with
             | [] -> []
             | x::s' -> (match t with
                         | [] -> []
                         | y::t' -> (x,y)::(zip s' t'))
           in zip
                (let rec map = function
                 | [] -> []
                 | x::s' ->
                   (fun l ->
                     sumprod_down (match k0 with
                                   | Kf -> Kv
                                   | Kv -> Kf)
                       x (Some
                       (match n0.node_tag with
                        | Func ->
                          let rec foldr = function
                          | [] ->
                            RbaseSymbolsImpl.coq_R1,RbaseSymbolsImpl.coq_R0
                          | x0::s'0 ->
                            let o,o' = x0 in
                            let i,i' = foldr s'0 in
                            (RbaseSymbolsImpl.coq_Rplus
                              (RbaseSymbolsImpl.coq_Rmult o i)
                              (RbaseSymbolsImpl.coq_Rmult o' i')),(RbaseSymbolsImpl.coq_Rplus
                                                                    (RbaseSymbolsImpl.coq_Rmult
                                                                    o i')
                                                                    (RbaseSymbolsImpl.coq_Rmult
                                                                    o' i))
                          in foldr l
                        | Var v ->
                          let rec foldl z0 = function
                          | [] -> z0
                          | x0::s'0 ->
                            foldl
                              (let o,o' = z0 in
                               let i,i' = x0 in
                               (RbaseSymbolsImpl.coq_Rmult o i),(RbaseSymbolsImpl.coq_Rmult
                                                                  o' i'))
                              s'0
                          in foldl v l)))::(map s')
                 in map n0.children)
                (let rec seqs_but1 a = function
                 | [] -> []
                 | b1::b2 ->
                   (let rec cat s1 s2 =
                      match s1 with
                      | [] -> s2
                      | x::s1' -> x::(cat s1' s2)
                    in cat a b2)::(seqs_but1
                                    (let rec rcons s z0 =
                                       match s with
                                       | [] -> z0::[]
                                       | x::s' -> x::(rcons s' z0)
                                     in rcons a b1)
                                    b2)
                 in seqs_but1 arg0
                      (let rec map = function
                       | [] -> []
                       | x::s' -> x.up::(map s')
                       in map n0.children))));
    up = n0.up; down = p }
  | None ->
    let arg0 = [] in
    let down' = RbaseSymbolsImpl.coq_R1,RbaseSymbolsImpl.coq_R1 in
    { node_id = n0.node_id; node_tag = n0.node_tag; children =
    (let rec map = function
     | [] -> []
     | x::s' -> (let x0,_ = x in x0 (let _,y = x in y))::(map s')
     in map
          (let rec zip s t =
             match s with
             | [] -> []
             | x::s' -> (match t with
                         | [] -> []
                         | y::t' -> (x,y)::(zip s' t'))
           in zip
                (let rec map = function
                 | [] -> []
                 | x::s' ->
                   (fun l ->
                     sumprod_down (match k0 with
                                   | Kf -> Kv
                                   | Kv -> Kf)
                       x (Some
                       (match n0.node_tag with
                        | Func ->
                          let rec foldr = function
                          | [] ->
                            RbaseSymbolsImpl.coq_R1,RbaseSymbolsImpl.coq_R0
                          | x0::s'0 ->
                            let o,o' = x0 in
                            let i,i' = foldr s'0 in
                            (RbaseSymbolsImpl.coq_Rplus
                              (RbaseSymbolsImpl.coq_Rmult o i)
                              (RbaseSymbolsImpl.coq_Rmult o' i')),(RbaseSymbolsImpl.coq_Rplus
                                                                    (RbaseSymbolsImpl.coq_Rmult
                                                                    o i')
                                                                    (RbaseSymbolsImpl.coq_Rmult
                                                                    o' i))
                          in foldr l
                        | Var v ->
                          let rec foldl z0 = function
                          | [] -> z0
                          | x0::s'0 ->
                            foldl
                              (let o,o' = z0 in
                               let i,i' = x0 in
                               (RbaseSymbolsImpl.coq_Rmult o i),(RbaseSymbolsImpl.coq_Rmult
                                                                  o' i'))
                              s'0
                          in foldl v l)))::(map s')
                 in map n0.children)
                (let rec seqs_but1 a = function
                 | [] -> []
                 | b1::b2 ->
                   (let rec cat s1 s2 =
                      match s1 with
                      | [] -> s2
                      | x::s1' -> x::(cat s1' s2)
                    in cat a b2)::(seqs_but1
                                    (let rec rcons s z0 =
                                       match s with
                                       | [] -> z0::[]
                                       | x::s' -> x::(rcons s' z0)
                                     in rcons a b1)
                                    b2)
                 in seqs_but1 arg0
                      (let rec map = function
                       | [] -> []
                       | x::s' -> x.up::(map s')
                       in map n0.children))));
    up = n0.up; down = down' }
  in sumprod_down k
       (let rec sumprod_up k0 n0 =
          { node_id = n0.node_id; node_tag = n0.node_tag; children =
            (let rec map = function
             | [] -> []
             | x::s' ->
               (sumprod_up (match k0 with
                            | Kf -> Kv
                            | Kv -> Kf) x)::(map s')
             in map n0.children);
            up =
            (match n0.node_tag with
             | Func ->
               let rec foldr = function
               | [] -> RbaseSymbolsImpl.coq_R1,RbaseSymbolsImpl.coq_R0
               | x::s' ->
                 let o,o' = x in
                 let i,i' = foldr s' in
                 (RbaseSymbolsImpl.coq_Rplus (RbaseSymbolsImpl.coq_Rmult o i)
                   (RbaseSymbolsImpl.coq_Rmult o' i')),(RbaseSymbolsImpl.coq_Rplus
                                                         (RbaseSymbolsImpl.coq_Rmult
                                                           o i')
                                                         (RbaseSymbolsImpl.coq_Rmult
                                                           o' i))
               in foldr
                    (let rec map = function
                     | [] -> []
                     | x::s' -> x.up::(map s')
                     in map
                          (let rec map = function
                           | [] -> []
                           | x::s' ->
                             (sumprod_up (match k0 with
                                          | Kf -> Kv
                                          | Kv -> Kf)
                               x)::(map s')
                           in map n0.children))
             | Var v ->
               let rec foldl z0 = function
               | [] -> z0
               | x::s' ->
                 foldl
                   (let o,o' = z0 in
                    let i,i' = x in
                    (RbaseSymbolsImpl.coq_Rmult o i),(RbaseSymbolsImpl.coq_Rmult
                                                       o' i'))
                   s'
               in foldl v
                    (let rec map = function
                     | [] -> []
                     | x::s' -> x.up::(map s')
                     in map
                          (let rec map = function
                           | [] -> []
                           | x::s' ->
                             (sumprod_up (match k0 with
                                          | Kf -> Kv
                                          | Kv -> Kf)
                               x)::(map s')
                           in map n0.children)));
            down = () }
        in sumprod_up k n)
       None

(** val estimation_ext :
    kind -> ('a1, RbaseSymbolsImpl.coq_R*RbaseSymbolsImpl.coq_R,
    RbaseSymbolsImpl.coq_R*RbaseSymbolsImpl.coq_R) tn_tree ->
    ('a1*(RbaseSymbolsImpl.coq_R*RbaseSymbolsImpl.coq_R)) list **)

let rec estimation_ext k n =
  match n.node_tag with
  | Func ->
    let rec foldr = function
    | [] -> []
    | x::s' ->
      let rec cat s1 s2 =
        match s1 with
        | [] -> s2
        | x0::s1' -> x0::(cat s1' s2)
      in cat x (foldr s')
    in foldr
         (let rec map = function
          | [] -> []
          | x::s' ->
            (estimation_ext (match k with
                             | Kf -> Kv
                             | Kv -> Kf) x)::(map s')
          in map n.children)
  | Var _ ->
    (n.node_id,(let o,o' = n.up in
                let i,i' = n.down in
                let p0 = RbaseSymbolsImpl.coq_Rmult o i in
                let p1 = RbaseSymbolsImpl.coq_Rmult o' i' in
                (RbaseSymbolsImpl.coq_Rmult p0
                  (RinvImpl.coq_Rinv (RbaseSymbolsImpl.coq_Rplus p0 p1))),
                (RbaseSymbolsImpl.coq_Rmult p1
                  (RinvImpl.coq_Rinv (RbaseSymbolsImpl.coq_Rplus p0 p1)))))::(
      let rec foldr = function
      | [] -> []
      | x::s' ->
        let rec cat s1 s2 =
          match s1 with
          | [] -> s2
          | x0::s1' -> x0::(cat s1' s2)
        in cat x (foldr s')
      in foldr
           (let rec map = function
            | [] -> []
            | x::s' ->
              (estimation_ext (match k with
                               | Kf -> Kv
                               | Kv -> Kf) x)::(map s')
            in map n.children))
