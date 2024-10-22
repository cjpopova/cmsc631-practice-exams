Module q1.
(* Q1
a. fun (x : bool) => [x]
b. fun (X : Type) => Some 1
c. empty
d. empty
e. (True, True) (* I am pretty sure * means pair here *)
f. Some (fun (p : (Prop * Prop) => (fst p)))
g. fun (X: Type) => []
h. empty (* not sure about this *)
i. (* TODO: review proof objects *)
*)
End q1.

(**********************************************************)

Module q2.
Inductive tree := 
    | Empty : tree 
    | Node : nat -> tree -> tree -> tree.

Definition ex_tree_1 : tree := Node 1 (Node 5 (Node 17 Empty Empty) (Node 10 Empty Empty)) (Node 42 Empty Empty).

Definition ex_tree_2 : tree := Node 0 (Node 10 Empty Empty) (Node 5 (Node 2 Empty Empty) (Node 7 Empty Empty)).

(*
Auxilary helper inductive relation:
A tree + n:nat satisfies heap_aux the value of its top Node (x) is geq n
AND the values of its children (l, r) are geq than the top Node x (recursive).
*)
Inductive heap_aux : tree -> nat -> Prop :=
    | Heap_AuxEmpty : forall n, heap_aux Empty n
    | Heap_AuxNode : forall n x l r, 
    x >= n -> 
    heap_aux l x ->
    heap_aux r x ->
    heap_aux (Node x l r) n
.

(* a tree is a heap if it satisfies heap_aux for the value x *)
Inductive heap_wf : tree -> Prop :=
| Heap_empty :
    heap_wf Empty
| Heap_node : forall x l r,
    heap_aux l x ->
    heap_aux r x ->
    heap_wf (Node x l r).

(* Satisfies definition: *) 
Example heap1 : heap_wf ex_tree_1. Proof. repeat constructor. Qed. (* Trivially satisfies definition: *) 
Example heap2 : heap_wf Empty. Proof. repeat constructor. Qed. (* The right subtree of ex_tree_2 does not satisfy the heap property: *) 
Example not_heap_1 : ~ (heap_wf (Node 5 (Node 2 Empty Empty) (Node 7 Empty Empty))). (* Therefore ex_tree_2 is also not a valid heap: *) 
Proof. unfold not. intros. inversion H. inversion H2. (* do something with H8 *) Admitted.
Example not_heap_2 : ~ (heap_wf ex_tree_2). Proof. Admitted.

(* NOTE: pop answer not shown, but I think Leo said we wouldn't have something like on the exam *)

End q2.

(**********************************************************)

Module q3.

(* TODO

Loop invariant: invariant: X <= 42 /\ m + Y = X 

*)

End q3.

(**********************************************************)

Module q4.

(* TODO: review me

we'll start with the hoare_if rule and rewrite it into the nonzero form:

{P /\ b}  c1 {Q}
{P /\ not b} c2 {Q}
---------------------------(hoare_if)
{P} if b then c1 else c2 {Q}


{P /\ a != 0}  c1 {Q}
{P /\ a=0} skip {Q}
---------------------------(hoare_nonzero)
{P} ifnz a c {Q}


extending the evaluation relation:

(* the easy way: compile to if *)
| E_ifnz : forall ...
    st =[ if (a <> 0) then c else skip ]=> st'
    st =[ ifnx a c ]=> st'

(* slightly harder way*)
| E_ifnz_true : forall ...
    aeval a = 0 ->
    st =[ ifnx a c ]=> st
| E_ifnz_false: forall ...
    aeval a != 0 ->
    st =[ c ]=> st' ->
    st =[ ifnx a c ]=> st'


*)

End q4.