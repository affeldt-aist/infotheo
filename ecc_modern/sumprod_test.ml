#use "sumprod.ml";;

type ('a,'b) sum = Inl of 'a | Inr of 'b;;
let rec iota m n = if m >= n then [] else m :: iota (succ m) n;;

(* Have to hand-translate build_tree_rec, because extraction
   to ocaml doesn't work *)

module type Code = sig
  type i_m
  type i_n
  val enum_m : i_m list
  val enum_n : i_n list
  val _H : i_m -> i_n -> bool
end;;

module BT (C : Code) = struct
  open C
    
  let select_children s i =
    match i with
    | Inl i ->
        let s = Inl i :: s in
        List.map (fun j -> Inr j)
          (List.filter (fun j -> _H i j && not (List.mem (Inr j) s)) enum_n)
    | Inr i ->
        let s = Inr i :: s in
        List.map (fun j -> Inl j)
          (List.filter (fun j -> _H j i && not (List.mem (Inl j) s)) enum_m)

  let tag_of_kind _W i =
    match i with
    | Inr i -> Var (_W i)
    | Inl i -> Func

  let rec build_tree_rec _W s i =
    let chrn =
      List.map (build_tree_rec _W (i :: s)) (select_children s i)
    in
    {node_id = i; node_tag = tag_of_kind _W i;
     children = chrn; up = (); down = ()}

  let decode _W =
    let tree = build_tree_rec _W [] (Inr (List.hd enum_n)) in
    let computed_tree = sumprod Kv tree in
    estimation Kv computed_tree
end;;

(* A practical example, based on a simpler variant of the fig. 6 of
   Etzion et al.: "Which codes have cycle-free Tanner graphs?" *)

module Etzion = struct
  type i_m = int
  type i_n = int
  let enum_m = iota 0 6
  let enum_n = iota 0 10
  (* Optimal acyclic code according to Etzion et al.:
     encode 4 bits + parity by duplicating them.
     I.e. all even bits are connected, and bits 2*i and 2*i+1 are equal. *)
  let _H i j =
    if i = 5 then j mod 2 = 0 else i = j / 2
end;;

module BTE = BT(Etzion);;

let f1 x = if x = 9 then (0.8, 0.2) else (0.2, 0.8);; (* bit 8 is wrong *)
let f2 x = if x = 0 then (0.8, 0.2) else (0.2, 0.8);; (* bit 1 is wrong *)
let f3 x = if x/2 = 0 then (0.8, 0.2) else (0.2, 0.8);; (* all ok *)

(* Check that decoding works. *)
BTE.decode f1;;
BTE.decode f2;;
BTE.decode f3;;

(* The example in ldpc_algo_proof.v *)

module C = struct
  type i_m = int
  type i_n = int
  let enum_m = iota 0 2
  let enum_n = iota 0 3
  let _H i j = (j = i) || (j = i+1)
end;;

module BTC = BT(C);;
   
let f0 = function
  | 0 -> (0.2, 0.8)
  | 1 -> (0.2, 0.8)
  | 2 -> (0.8, 0.2)
  | _ -> (0., 0.)
;;

BTC.decode f0;;


(* A closer translation, using GADTs for ordinals *)
type zero = Zero
and 'a succ = Succ of 'a

type _ nat =
  | NZ : zero nat
  | NS : 'a nat -> 'a succ nat

type _ ord =
  | OZ : _ succ ord
  | OS : 'a succ ord -> 'a succ succ ord

let rec lift : type m. m succ ord -> m ord -> m succ ord = fun i j ->
  match i, j with
  | OZ, OZ -> OS j
  | OZ, OS _ -> OS j
  | OS _, OZ -> OZ
  | OS i, OS j -> OS (lift i j)

let rec widen : type m. m ord -> m succ ord = function
  | OZ -> OZ
  | OS i -> OS (widen i)

let rec ord_enum : type m. m nat -> m ord list = function
  | NZ -> []
  | NS i -> OZ :: List.map (lift OZ) (ord_enum i)
;;

type two = zero succ succ
and three = zero succ succ succ;;

module C' = struct
  type i_m = two ord and i_n = three ord
  let enum_m = ord_enum (NS (NS NZ))
  and enum_n = ord_enum (NS (NS (NS NZ)))
  let _H i j = (j = widen i) || (j = lift OZ i)
end;;

module BTC' = BT(C');;

let f0 : three ord -> r2 = function
  | OZ -> (0.2, 0.8)
  | OS OZ -> (0.2, 0.8)
  | OS (OS OZ) -> (0.8, 0.2)
;;

BTC'.decode f0;;
