From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.

Section rv_indep.

Ltac2 bar () := let x := '(3+4) in constr:($x + 5).

End rv_indep.
