From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Module q1.

(*
a. [Option nat]                 List Type
b. [fun x => x;fun x =>42]      list (nat -> nat)
c. fun (x:X) => or_introl x x   ill typed
d. fun (x: nat->nat) y => y x   (nat -> nat) -> ((nat -> nat) -> A) -> A
e. Some (fun y => y y)          ill typed
*)

End q1.

(*******************************************************************************)

Module q2.

(*
a. 
b. empty
c. empty
d. 
e. (True, true)
f. [fst]
g. 
h. ill typed
i. fun (x y H) => eq_refl y
j. fun (x y H) => H
*)

End q2.

(*******************************************************************************)

Module q3.

(*
Invariant = Y = 2*(m-X) /\ X >= 42
You may also write it as Y + 2X=2m /\ X >= 42

*)

End q3.

(*******************************************************************************)

Module q4.

(*
Inductive relation:
| E_Roll : forall x st n,
    1 <= n <= 6 ->
    st =[Roll x]=> (x !-> n; st)

You can also write E_Roll1, ... E_Roll6 as the following with a different n each time:
| E_Roll1 : forall x st, st =[Roll x]=> (x !-> 1; st)


Hoare triple:

---------------------------------
{Q[x -> n] /\ 1<=n<=6} Roll x {Q}

This rule is similar to assignment. You can also put the "[1<=n<=6]" into the premise.


*)

End q4.

(*******************************************************************************)

Module q5.

(* part a *)

(* part b *)


(* part c

Bonus question:
The inductive hypothesis of tree' is bad.
You can see this by printing tree_ind and tree'_ind in Coq.
Because of the tuple, you don't get to assume that P holds for the left or right subtrees.

*)

End q5.