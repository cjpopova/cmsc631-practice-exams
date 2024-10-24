From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Module q1.

(*
a. Listof Type
b. ill-typed
c. ill typed (because X is not bound)
d. (Nat -> Nat) Nat -> Nat
e. Option (Nat -> Nat)
*)

End q1.

(*******************************************************************************)

Module q2.

(*
a. fun (b:bool) => [42] (* returning [] is trival *)
b. fun (X Y: Prop) => tt (* tt is Unit *)
c. empty (* we can't return a term of type Y since no arguments of type Y are bound *)
d. fun (X Y : Type) (y : Y) => y
e. (1, True)
f. [fun (pr : bool * bool) => fst pr] (* assuming that fst is the pair accessor *)
g. fun (X : Prop) => None (* the trivial case is OK here since you can't write anything with Some here *)
h. empty (* this is clearly false*)
i. fun (x y : nat) => conj eq_refl eq_refl 
    (* 
    since the result is a Prop, we need to construct a proof object out of these pieces:
    eq_refl : x = x.
    conj  : forall A B : Prop, A -> B -> A /\ B
     *)
*)

End q2.

(*******************************************************************************)

Module q3.

Inductive tree := 
    | Empty : tree 
    | Node : nat -> tree -> tree -> tree.

Definition ex_tree_1 : tree := Node 1 (Node 5 (Node 17 Empty Empty) (Node 10 Empty Empty)) (Node 5 (Node 10 Empty Empty) (Node 17 Empty Empty)).
Definition ex_tree_2 : tree := Node 0 (Node 10 Empty Empty) (Node 5 (Node 2 Empty Empty) (Node 7 (Node 42 Empty Empty) (Node 8 Empty Empty))).

(* part a *)

(* check if t1 is a mirror of t2 *)
Fixpoint check_mirror (t1 t2 : tree) : bool :=
    match t1, t2 with
    | Empty, Empty => true
    | (Node v1 l1 r1), (Node v2 l2 r2) => 
        (andb (v1 =? v2) 
            (andb (check_mirror l1 r2) 
                  (check_mirror r1 l2)))
    | _, _ => false
    end.

Fixpoint is_sym (t:tree) : bool := check_mirror t t.

(* Trivial tree: *) 
Example sym_Empty : is_sym Empty = true. Proof. reflexivity. Qed.
(* Examples *) 
Example sym_1 : is_sym ex_tree_1 = true. Proof. reflexivity. Qed.
Example sym_2 : is_sym ex_tree_2 = false. Proof. reflexivity. Qed.

(* part b *)

(* the inductive relation has a helper to mirror the fixpoint implementation: *)
Inductive mirror : tree -> tree -> Prop :=
    | Mirror_Empty : mirror Empty Empty
    | Mirror_Node : forall (v : nat) (l1 r1 l2 r2 : tree),
        (* we don't need v1=v2 because we made them syntactically equal in the conclusion *)
        mirror l1 r2 ->
        mirror r1 l2 ->
        mirror (Node v l1 r1) (Node v l2 r2)
    .

Inductive sym : tree -> Prop :=
    | sym_ : forall (t : tree),
        mirror t t -> sym t
    .

(* Trivial tree: *) 
Example Sym_Empty : sym Empty. Proof. repeat constructor. Qed.
(* Examples *) 
Example Sym_1 : sym ex_tree_1.  Proof. repeat constructor. Qed.
Example Sym_2 : ~ (sym ex_tree_2). 
Proof. unfold not. intros. inversion H. inversion H0. inversion H4. Qed.

End q3.

(**************************************************************************)

Module q4.

(* part a *)

Fixpoint power_of_2 (n : nat) := 
    match n with
    | O => S O
    | S n' => mult 2 (power_of_2 n')
    end.

Notation "'2^' x" := (power_of_2 x) (at level 100).

(* part b *)

(*

template:

{{True}} ->>
{{ }}
X := m;
{{ }}
Y := 0;
{{ }}
Z := 1;
{{ P }}
WHILE X > 0 DO
    {{ P /\ X > 0 }} ->>
    {{ }}
    X := X - 1; 
    {{ }}
    Y := Z + Y; 
    {{ }}
    Z := Z + Z; 
    {{ P }}
DONE
{{ P /\ X <= 0 }} ->>
{{ Y+1 = 2^m }}
Y := Y + 1
{{ Y = 2^m }}


Notes:
Suppose m=4.
Value of each variable after each loop iteration:
X   3   2   1   0
Y   1   3   7   15
Z   2   4   8   16

The pattern: 2^m = 2^(m-1) + 2^(m-2) ... + 2^0 + 1
Examples:
- 2^2 = 2^1 + 2^0 + 1
- 2^3 = 8 = 2^2 + 2^1 + 2^0 + 1

loop invariant P : Z=2^(m-X) /\ Y + 1 = Z

Filled in:

{{True}} ->>
{{ 1=2^0 /\ 1 = 1 }}
X := m;
{{ 1=2^(m-X) /\ 0 + 1 = 1 }}
Y := 0;
{{ 1=2^(m-X) /\ Y + 1 = 1 }}
Z := 1;
{{ Z=2^(m-X) /\ Y + 1 = Z }}
WHILE X > 0 DO
    {{ Z=2^(m-X) /\ Y + 1 = Z /\ X > 0 }} ->>
    {{ Z + Z = 2^(m-(X-1)) /\ Y + 1 = Z }}
    X := X - 1; 
    {{ Z + Z = 2^(m-X) /\ Z + Y + 1 = Z + Z }}
    Y := Z + Y; 
    {{ Z + Z = 2^(m-X) /\ Y + 1 = Z + Z }}
    Z := Z + Z; 
    {{ Z=2^(m-X) /\ Y + 1 = Z }}
DONE
{{ Z=2^(m-X) /\ Y + 1 = Z /\ X <= 0 }} ->>
{{ Y+1 = 2^m }}
Y := Y + 1
{{ Y = 2^m }}

*)

End q4.

(**************************************************************************)

Module q5.

(*
| E_FixStop : forall st st' x c,
    st =[ c ] => st' -> 
    st x = st' x -> (* same in both states *)
    st =[ fix x c] => st
| E_FixContinue : forall st st' x c,
    st =[ c ]=> st' -> 
    ~(st x = st' x) -> (* different after 1 step *)
    st' =[ fix x c ]=> st'' ->
    st =[ fix x c] => st''
*)

End q5.