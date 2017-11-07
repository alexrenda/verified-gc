Require Import Bool Arith String List CpdtTactics.

(** model pointers as nats *)
Definition ptr := nat.
Definition ptr_eq_dec := eq_nat_dec.

(** Types of values we can have in the heap *)
Inductive val : Type := 
  | Nat_t : nat -> val
  | Pointer_t : ptr -> val.

(** We will model heaps as lists of pointers and values. *)
Definition heap := list (ptr * val).

