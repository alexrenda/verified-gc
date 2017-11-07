Require Import Bool Arith String List CpdtTactics.

(** model pointers as nats *)
Definition ptr := nat.
Definition ptr_eq_dec := eq_nat_dec.

(** Types of values we can have in the heap *)
Inductive val : Type :=
  | Nat : nat -> val
  | Pointer : ptr -> val
  | Struct : list val -> val.

(** We will model heaps as lists of pointers and values. *)
Definition heap := list (ptr * val).

Inductive valexp :=
| PtrRead : ptr -> valexp
| Deref : ptr -> nat -> valexp.

Inductive com :=
| Skip : com
| New : ptr -> valexp -> com
| Assign : ptr -> valexp -> com
| Drop : ptr -> com
| Out : valexp -> com.
Open Scope type.
Definition state := (list com * list ptr * heap).
