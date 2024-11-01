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
b. [fun x => x; fun x => 42]    list (nat -> nat)
c. fun (x:X) => or_introl x x   ill typed
d. fun (x: nat->nat) y => y x   (nat -> nat) -> ((nat -> nat) -> A) -> A
e. Some (fun y => y y)          ill typed
*)

End q1.

(*******************************************************************************)

Module q2.

(*
a. list nat -> option nat                   fun (x : list nat) => Some 1
b. forall (X Y : Prop), X*Y                 empty
c. forall (X Y Z : Type) X -> Y -> Z        empty
d. forall (X Y Z : Type) X -> Y -> Z -> Y   fun (X Y Z : Type) (x:X) (y:Y) (z:Z) => y
e. Prop * bool                              (True, true)
f. list (bool*nat -> bool)                  [fst]
g. forall (X : Prop), option (list X)       fun (X : Prop) => Some []
h. forall (x y : nat), x ^ y                ill typed
i. forall (x y : nat), x=x -> y=y           fun (x y H) => eq_refl y
j. forall (x y : nat),, x=y -> x=y          fun (x y H) => H
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

Inductive tree := 
    | Empty : tree 
    | Node : nat -> tree -> tree -> tree.

Inductive tree' := 
    | Empty' : tree' 
    | Node' : nat -> (tree'* tree') -> tree'.

Definition ex_tree_1 : tree := Node 1 (Node 5 (Node 17 Empty Empty) (Node 10 Empty Empty)) (Node 5 (Node 17 Empty Empty) (Node 10 Empty Empty)).

Definition ex_tree_2 : tree := Node 0 (Node 10 Empty Empty) (Node 5 (Node 2 Empty Empty) (Node 7 (Node 42 Empty Empty) (Node 8 Empty Empty))).

(* part a *)

Fixpoint convert (t:tree) : tree' :=
    match t with
    | Empty => Empty'
    | Node x l r => Node' x (convert l, convert r)
    end.

(* part b *)

Inductive Convert : tree -> tree' -> Prop :=
    | Conv_empty : Convert Empty Empty'
    | Conv_node : forall x l l' r r',
        (* x is syntactically equal in both t and t' *)
        Convert l l' ->
        Convert r r' ->
        Convert (Node x l r) (Node' x (l', r'))
    .

(* part c

Bonus question:
The inductive hypothesis of tree' is bad.
You can see this by printing tree_ind and tree'_ind in Coq.
Because of the tuple, you don't get to assume that P holds for the left or right subtrees.

*)

End q5.