
val fst : ('a1*'a2) -> 'a1

val snd : ('a1*'a2) -> 'a2



type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

val rplus : float -> float -> float

val rmult : float -> float -> float

val ropp : float -> float

val rinv : float -> float

val rdiv : float -> float -> float

val iPR_2 : positive -> float

val iPR : positive -> float

val iZR : z -> float

val cat : 'a1 list -> 'a1 list -> 'a1 list

val rcons : 'a1 list -> 'a1 -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val foldr : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2

val foldl : ('a2 -> 'a1 -> 'a2) -> 'a2 -> 'a1 list -> 'a2

val zip : 'a1 list -> 'a2 list -> ('a1*'a2) list

val flatten : 'a1 list list -> 'a1 list

type r2 = float*float

type kind =
| Kf
| Kv

type tag =
| Func
| Var of r2

val negk : kind -> kind

type ('id, 'u, 'd) tn_tree = { node_id : 'id; node_tag : tag;
                               children : ('id, 'u, 'd) tn_tree list;
                               up : 'u; down : 'd }

val node_id : kind -> ('a1, 'a2, 'a3) tn_tree -> 'a1

val node_tag : kind -> ('a1, 'a2, 'a3) tn_tree -> tag

val children : kind -> ('a1, 'a2, 'a3) tn_tree -> ('a1, 'a2, 'a3) tn_tree list

val up : kind -> ('a1, 'a2, 'a3) tn_tree -> 'a2

val down : kind -> ('a1, 'a2, 'a3) tn_tree -> 'a3

val alpha_op : r2 -> r2 -> float*float

val alpha : r2 list -> r2

val beta_op : r2 -> r2 -> float*float

val beta : r2 -> r2 list -> r2

val alpha_beta : kind -> tag -> r2 list -> r2

val sumprod_up : kind -> ('a1, unit, unit) tn_tree -> ('a1, r2, unit) tn_tree

val seqs_but1 : r2 list -> r2 list -> r2 list list

val apply_seq : ('a1 -> 'a2) list -> 'a1 list -> 'a2 list

val push_init : (float*float) option -> (float*float) list*(float*float)

val sumprod_down :
  kind -> ('a1, r2, unit) tn_tree -> r2 option -> ('a1, r2, r2) tn_tree

val sumprod : kind -> ('a1, unit, unit) tn_tree -> ('a1, r2, r2) tn_tree

val normalize : r2 -> float*float

val estimation : kind -> ('a1, r2, r2) tn_tree -> ('a1*(float*float)) list
