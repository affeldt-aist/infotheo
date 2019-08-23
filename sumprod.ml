
(** val fst : ('a1*'a2) -> 'a1 **)

let fst = function
| x,_ -> x

(** val snd : ('a1*'a2) -> 'a2 **)

let snd = function
| _,y -> y



type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

(** val rplus : float -> float -> float **)

let rplus = (+.)

(** val rmult : float -> float -> float **)

let rmult = ( *.)

(** val ropp : float -> float **)

let ropp = (~-.)

(** val rinv : float -> float **)

let rinv = fun x -> 1. /. x

(** val rdiv : float -> float -> float **)

let rdiv r1 r3 =
  rmult r1 (rinv r3)

(** val iPR_2 : positive -> float **)

let rec iPR_2 = function
| XI p0 -> rmult (rplus 1. 1.) (rplus 1. (iPR_2 p0))
| XO p0 -> rmult (rplus 1. 1.) (iPR_2 p0)
| XH -> rplus 1. 1.

(** val iPR : positive -> float **)

let iPR = function
| XI p0 -> rplus 1. (iPR_2 p0)
| XO p0 -> iPR_2 p0
| XH -> 1.

(** val iZR : z -> float **)

let iZR = function
| Z0 -> 0.
| Zpos n -> iPR n
| Zneg n -> ropp (iPR n)

(** val cat : 'a1 list -> 'a1 list -> 'a1 list **)

let rec cat s1 s2 =
  match s1 with
  | [] -> s2
  | x::s1' -> x::(cat s1' s2)

(** val rcons : 'a1 list -> 'a1 -> 'a1 list **)

let rec rcons s z0 =
  match s with
  | [] -> z0::[]
  | x::s' -> x::(rcons s' z0)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| x::s' -> (f x)::(map f s')

(** val foldr : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 **)

let rec foldr f z0 = function
| [] -> z0
| x::s' -> f x (foldr f z0 s')

(** val foldl : ('a2 -> 'a1 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 **)

let rec foldl f z0 = function
| [] -> z0
| x::s' -> foldl f (f z0 x) s'

(** val zip : 'a1 list -> 'a2 list -> ('a1*'a2) list **)

let rec zip s t =
  match s with
  | [] -> []
  | x::s' -> (match t with
              | [] -> []
              | y::t' -> (x,y)::(zip s' t'))

(** val flatten : 'a1 list list -> 'a1 list **)

let flatten s =
  foldr cat [] s

type r2 = float*float

type kind =
| Kf
| Kv

type tag =
| Func
| Var of r2

(** val negk : kind -> kind **)

let negk = function
| Kf -> Kv
| Kv -> Kf

type ('id, 'u, 'd) tn_tree = { node_id : 'id; node_tag : tag;
                               children : ('id, 'u, 'd) tn_tree list;
                               up : 'u; down : 'd }

(** val node_id : kind -> ('a1, 'a2, 'a3) tn_tree -> 'a1 **)

let node_id _ x = x.node_id

(** val node_tag : kind -> ('a1, 'a2, 'a3) tn_tree -> tag **)

let node_tag _ x = x.node_tag

(** val children :
    kind -> ('a1, 'a2, 'a3) tn_tree -> ('a1, 'a2, 'a3) tn_tree list **)

let children _ x = x.children

(** val up : kind -> ('a1, 'a2, 'a3) tn_tree -> 'a2 **)

let up _ x = x.up

(** val down : kind -> ('a1, 'a2, 'a3) tn_tree -> 'a3 **)

let down _ x = x.down

(** val alpha_op : r2 -> r2 -> float*float **)

let alpha_op out inp =
  let o,o' = out in
  let i,i' = inp in
  (rplus (rmult o i) (rmult o' i')),(rplus (rmult o i') (rmult o' i))

(** val alpha : r2 list -> r2 **)

let alpha =
  foldr alpha_op ((iZR (Zpos XH)),(iZR Z0))

(** val beta_op : r2 -> r2 -> float*float **)

let beta_op out inp =
  let o,o' = out in let i,i' = inp in (rmult o i),(rmult o' i')

(** val beta : r2 -> r2 list -> r2 **)

let beta =
  foldl beta_op

(** val alpha_beta : kind -> tag -> r2 list -> r2 **)

let alpha_beta _ = function
| Func -> alpha
| Var v -> beta v

(** val sumprod_up :
    kind -> ('a1, unit, unit) tn_tree -> ('a1, r2, unit) tn_tree **)

let rec sumprod_up k n =
  let children' = map (sumprod_up (negk k)) n.children in
  let up' = alpha_beta k n.node_tag (map (up (negk k)) children') in
  { node_id = n.node_id; node_tag = n.node_tag; children = children'; up =
  up'; down = () }

(** val seqs_but1 : r2 list -> r2 list -> r2 list list **)

let rec seqs_but1 a = function
| [] -> []
| b1::b2 -> (cat a b2)::(seqs_but1 (rcons a b1) b2)

(** val apply_seq : ('a1 -> 'a2) list -> 'a1 list -> 'a2 list **)

let apply_seq l1 l2 =
  map (fun p -> fst p (snd p)) (zip l1 l2)

(** val push_init :
    (float*float) option -> (float*float) list*(float*float) **)

let push_init = function
| Some p -> (p::[]),p
| None -> [],((iZR (Zpos XH)),(iZR (Zpos XH)))

(** val sumprod_down :
    kind -> ('a1, r2, unit) tn_tree -> r2 option -> ('a1, r2, r2) tn_tree **)

let rec sumprod_down k n from_above =
  let arg0,down' = push_init from_above in
  let args = seqs_but1 arg0 (map (up (negk k)) n.children) in
  let funs =
    map (fun n' l ->
      sumprod_down (negk k) n' (Some (alpha_beta k n.node_tag l))) n.children
  in
  let children' = apply_seq funs args in
  { node_id = n.node_id; node_tag = n.node_tag; children = children'; up =
  n.up; down = down' }

(** val sumprod :
    kind -> ('a1, unit, unit) tn_tree -> ('a1, r2, r2) tn_tree **)

let sumprod k n =
  sumprod_down k (sumprod_up k n) None

(** val normalize : r2 -> float*float **)

let normalize = function
| p0,p1 -> (rdiv p0 (rplus p0 p1)),(rdiv p1 (rplus p0 p1))

(** val estimation :
    kind -> ('a1, r2, r2) tn_tree -> ('a1*(float*float)) list **)

let rec estimation k n =
  let l = flatten (map (estimation (negk k)) n.children) in
  (match n.node_tag with
   | Func -> l
   | Var _ -> (n.node_id,(normalize (beta_op n.up n.down)))::l)
