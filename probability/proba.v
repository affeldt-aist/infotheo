(* infotheo (c) AIST. R. Affeldt, M. Hagiwara, J. Senizergues. GNU GPLv3. *)
(* infotheo v2 (c) AIST, Nagoya University. GNU GPLv3. *)
Require Import fdist.

(******************************************************************************)
(*    Compatibility file for probabilities over finite distributions          *)
(*                                                                            *)
(* The file proba.v was becoming a bit large and was containing lemmas about  *)
(* probabilities over joint distributions. Most of the contents have been     *)
(* moved to fdist.v. Probabilities over joint distributions are in jfdist.v.  *)
(* You may want to Require Import fdist instead of proba from now.            *)
(*                                                                            *)
(* Side note: Finitely-supported distributions are in fsdist.v (formerly      *)
(*            cproba.v).                                                      *)
(******************************************************************************)

Export fdist.
