From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Module q1.
(*
a. list Type
b. ill-typed
c. forall X : Prop, X -> X /\ X
d. ill-typed
e. list (Type -> Type) (* or List (nat -> nat) *)
*)

End q1.

(*******************************************************************************)

Module q2.
(*
a. fun (x:Nat) => [x=0]
b. fun (X:Prop) => Some true
c. empty
d. fun (X Y : Type) (x : X) => x
e. (True, 1)
f. Some (fun (p : nat * bool) => snd p)
g. fun (X:Prop) => []
h. empty
i. fun (P Q : Prop) (p : P) (q : Q) => or_introl p
*)

End q2.

(*******************************************************************************)

Module q3.

Inductive tree := 
    | Empty : tree 
    | Node : nat -> tree -> tree -> tree.

Definition ex_tree_1 : tree := Node 1 (Node 5 (Node 17 Empty Empty) (Node 10 Empty Empty)) (Node 42 Empty Empty).
Definition ex_tree_2 : tree := Node 0 (Node 10 Empty Empty) (Node 5 (Node 2 Empty Empty) (Node 7 (Node 42 Empty Empty) (Node 8 Empty Empty))).

(* part a *)

(* the exam PDF is incorrect. It should say:
    the height of ex_tree_1 is 3, while the height of ex_tree_2 is 4.

the max function is OK to assume since it is trivial to implement *)
Fixpoint height (t: tree) : nat :=  
    match t with
    | Empty => 0
    | Node v t1 t2 => 1 + max (height t1) (height t2)
    end.

(* Trivial tree: *)
Example height_leaf : height Empty = 0. Proof. reflexivity. Qed.
(* Examples *) 
Example height1 : height ex_tree_1 = 3. Proof. reflexivity. Qed.
Example height2 : height ex_tree_2 = 4. Proof. reflexivity. Qed.

(* part b *)

(* Helper: check if the tree t is height h or h-1 in all subtrees *)
Fixpoint is_height (t:tree) (h:nat) : bool :=
match t, h with
    | Empty, _ => (h <=? 1)
    | Node x l r , S h' => andb (is_height l h') (is_height r h')
    | Node x l r, _ => false
end.

Fixpoint balanced (t:tree) : bool :=
    is_height t (height t).

(* Trivial tree: *) 
Example balanced_leaf : balanced Empty = true. Proof. reflexivity. Qed.
(* Examples *) 
Example balanced1 : balanced ex_tree_1 = true.  Proof. reflexivity. Qed.
Example balanced2 : balanced ex_tree_2 = false.  Proof. reflexivity. Qed.

(* part c *)

Inductive bal : nat -> tree-> Prop :=
    | Bal_Empty0 : bal 0 Empty
    | Bal_Empty1 : bal 1 Empty
 (*   | Bal_Node1 : forall v,
        bal 0 (Node v Empty Empty) *)
    | Bal_Node : forall n v t1 t2,
        bal n t1 -> bal n t2 ->
        bal (S n) (Node v t1 t2).

(* I have also changed the height on these *)
Example bal_leaf0 : bal 0 Empty. Proof. constructor. Qed.
Example bal_leaf1 : bal 1 Empty. Proof. constructor. Qed.
Example bal1 : bal 3 ex_tree_1. Proof. repeat constructor. Qed.
Example bal2 : forall n, ~ (bal n ex_tree_2). 
Proof. unfold not. intros. inversion H; subst. 
    inversion H3; subst.
    inversion H4; subst; inversion H5; subst.
    - inversion H6.
    - inversion H9; subst. inversion H8.
    Qed.

End q3.

(*********************************************************)

Module q4.

(*
Loop invariant: Y = m * (m - Z) /\ X=m 

{{ X = m }} ->> 
{{ 0 = m * (m - X) /\ X=m }}
    Y := 0; 
{{ Y = m * (m - X) /\ X=m }}
    Z := X;
{{ Y = m * (m - Z) /\ X=m }}
    WHILE Z > 0 DO 
{{ Y = m * (m - Z) /\ X=m /\ Z > 0 }} ->>
{{ Y+X = m * (m - (Z-1)) /\ X=m }}
        Z := Z- 1;
{{ Y+X = m * (m - Z) /\ X=m }}
        Y := Y + X
{{  Y = m * (m - Z) /\ X=m }}
    DONE 
{{ Y = m * (m - Z) /\ X=m /\ Z <= 0 }} ->>
{{ Y = m * m }}
*)

End q4.

(*********************************************************)

Module q5.

(* part a *)

(* Multiple acceptable options:
          
------------------------------ (hoare_assert_1)
{{ P }} assert e {{ e /\ P }}


       P -> b
-------------------- (hoare_assert_2)
{{P}} assert b {{P}}

*)

(* part b *)

(*
| E_AssertTrue
    beval st b = true ->
    st =[ assert e ]=> st

don't add an E_AssertFalse rule to make the program stuck here

*)

End q5.