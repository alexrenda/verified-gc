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

Inductive com : Type := 
| Skip : com
| Assign : var -> aexp -> com
| Seq : com -> com -> com
| If : bexp -> com -> com -> com
| While : bexp -> com -> com.
| Assign : var -> aexp -> com

Inductive step_com : com -> state -> com -> state -> Prop := 
| Step_assign: forall s x e,
       step_com (Assign x e) s
                (Skip) (set x (eval_aexp e s) s)
| Step_seqL: forall c1 c2 c1' s s', step_com c1 s c1' s' ->
                step_com (Seq c1 c2) s (Seq c1' c2) s'
| Step_seqR: forall c s, step_com (Seq Skip c) s c s
| Step_if_true:  forall b c1 c2 s, eval_bexp b s = true ->
                 step_com (If b c1 c2) s c1 s
| Step_if_false: forall b c1 c2 s, eval_bexp b s = false ->
                 step_com (If b c1 c2) s c2 s
| Step_while: forall b c s,
                 step_com (While b c) s
                          (If b (Seq c (While b c)) Skip) s.


(** A command takes a heap and returns a new optional heap *)
Definition cmd := heap -> option(heap)

(** Failure -- this is like throwing an exception.  A good 
    homework for people unfamiliar with monads is to define 
    a "try _ catch _" construct. *)
Definition exit t : Cmd t := fun h => None.

(** Allocation -- to allocate a fresh location, we run through
    the heap and find the biggest pointer, and simply return 
    the next biggest pointer.  Another good homework is to 
    change the definitions here to carry along the "next available
    pointer" as part of the state of the system. *)
Definition max (p1 p2:ptr) := if le_gt_dec p1 p2 then p2 else p1.
Fixpoint max_heap(h:heap) := 
  match h with 
    | nil => 0
    | (p,_)::rest => max p (max_heap rest)
  end.

(** The [new u] command allocates a new location in the heap, 
    initializes it with the value [u], and returns the pointer
    to the freshly-allocated location. *)
Fixpoint insert (h:heap) (x:ptr) (v:) : heap := 
  match h with 
    | nil => (x,v)::nil
    | (y,w)::h' => 
      if le_gt_dec x y then
        (x,v)::(y,w)::h'
      else (y,w)::(insert h' x v)
  end.

Definition new (u:U.t) : Cmd ptr := 
  fun h => 
    let p := 1 + max_heap h in Some (insert h p u, p).

(** Lookup a pointer in the heap, returning the value associated
    with it if any. *)  
Fixpoint lookup (h:heap) (p:ptr) : option U.t := 
  match h with 
    | nil => None
    | (p',u')::rest => if ptr_eq_dec p p' then Some u' else lookup rest p
  end.

(** The [read] command looks up the given pointer and returns the
    value if any, and fails if there is no value present.  It leaves
    the heap unchanged. *)
Definition read (p:ptr) : Cmd U.t := 
  fun h => match lookup h p with 
             | None => None
             | Some u => Some (h, u)
           end.

(** Remove the pointer [p] from the heap, returning a new heap. *)
Fixpoint remove (h:heap) (p:ptr) : heap := 
  match h with 
    | nil => nil
    | (p',u')::h => if ptr_eq_dec p p' then remove h p else (p',u')::(remove h p)
  end.

(** To write [u] into the pointer [p], we first check that [p]
    is defined in the heap, and then remove it, and add it back
    with the value [u]. *)
Definition write (p:ptr) (u:U.t) : Cmd unit := 
  fun h => match lookup h p with 
             | None => None
             | Some _ => Some(insert (remove h p) p u, tt)
           end.

(** To free the pointer [p], we simply remove it from the heap.
    Again, this will fail if [p] wasn't in the heap to begin with. *)
Definition free (p:ptr) : Cmd unit := 
  fun h => match lookup h p with 
             | None => None
             | Some _ => Some(remove h p, tt)
           end.
