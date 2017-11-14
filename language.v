Require Import Bool Arith String List CpdtTactics.

(** model pointers as nats *)
Definition ptr := nat.
Definition ptr_eq_dec := eq_nat_dec.

(** model vars as nats too, a bit silly so probably change later *)
Definition var := string.
Definition var_eq_dec := string_dec.

(** Types of values we can have in the heap *)
Inductive val : Type :=
| Int : nat -> val
| Pointer : ptr -> val
| Struct : list val -> val.

(** We will model heaps as lists of pointers and values. *)
Definition heap := list (ptr * val).

Inductive valexp :=
| IntExp : nat -> valexp
| StructExp : list valexp -> valexp
| VarRead : var -> valexp (** pointer associated with var *)
| Deref : var -> valexp (** value associated with var *)
| Index : var -> nat -> valexp.

Inductive com :=
| Skip : com
| New : var -> valexp -> com
| Assign : var -> valexp -> com
| Drop : var -> com
| Out : valexp -> com.

(** roots is the top level var to pointers, output is ouput of the program *)
Definition roots := list (var * ptr).
Definition output := list nat.

Open Scope type.
(** list of root pointers, a heap, and a list of output *)
Definition state := (roots * heap * output).
Close Scope type.

(** val evaluation and helpers *)
Fixpoint heap_get (p:ptr) (h:heap) : option val :=
match h with
| nil => None
| (hp, hv)::t => if ptr_eq_dec hp p then Some hv else (heap_get p t)
end.

Fixpoint roots_get (v:var) (r:roots) : option ptr :=
match r with
| nil => None
| (hv, hp)::t => if var_eq_dec hv v then Some hp else (roots_get v t)
end.

Fixpoint optional_list_from_list_optional {A: Type} (l: list (option A)) : option (list A) :=
  match l with 
  | nil => Some nil
  | h::t => 
    match h, optional_list_from_list_optional t with
    | None, _ => None
    | _, None => None
    | Some v, Some tl => Some (v::tl)
    end
  end.

Fixpoint eval_valexp (exp:valexp) (s:state) : option val :=
  let roots := fst (fst s) in
  let heap := snd (fst s) in
    match exp with
    | IntExp n => Some (Int n) (** just an int value *)
    | StructExp l => (** a struct *)
      match optional_list_from_list_optional (List.map (fun x => eval_valexp x s) l) with
      | None => None
      | Some vl => Some (Struct vl)
      end
    | VarRead v => (** want the actual pointer *)
      match roots_get v roots with
      | None => None
      | Some p => Some (Pointer p)
      end
    | Deref v => (** want value at pointer *)
      match roots_get v roots with
      | None => None
      | Some p => heap_get p heap
      end
    | Index v n => (** value at pointer is a list of val, want the nth val of list *)
      match roots_get v roots with
      | None => None
      | Some p =>
        match heap_get p heap with
        | Some (Struct l) => nth_error l n
        | _ => None
        end
      end
  end.

(** fresh heap pointer is 1 more than the maximum heap ptr *)
Definition fresh_heap_ptr (h: heap) : ptr :=
  let max := fun (p1 p2:ptr) => if le_gt_dec p1 p2 then p2 else p1 in
  let fix max_heap (h': heap) :=
    match h' with 
    | nil => 0
    | (p,_)::t => max p (max_heap t)
    end
  in
  (max_heap h) + 1.

(** Remove var from roots, works even if var is not in it *)
Fixpoint remove_var (v:var) (r:roots) : roots := 
  match r with 
  | nil => nil
  | (v',p')::t => if var_eq_dec v v' then remove_var v t else (v',p')::(remove_var v t)
  end.

(** Set variable to a pointer *)
Definition set_var (v:var) (p:ptr) (r:roots) : roots := 
  let without_var := remove_var v r in
  (v, p)::without_var.

(** small step semantics *)
(** note that for all commands var doesn't need to be in roots, though eval_valexp may fail *)
Definition small_step (c: com) (s: state) : option state :=
  let roots := fst (fst s) in
  let heap := snd (fst s) in
  let output := snd s in
  match c with 
  | Skip => Some s
  | New var vexp =>
    match eval_valexp vexp s with 
    | Some val => 
      let p := fresh_heap_ptr heap in
      let new_heap := (p, val)::heap in
      let new_roots := set_var var p roots in
      Some (new_roots, new_heap, output)
    | None => None
    end
  | Assign var vexp => (** vexp needs to evaluate to a pointer *)
    match eval_valexp vexp s with 
    | Some (Pointer p) => 
      Some (set_var var p roots, heap, output)
    | _ => None
    end
  | Drop var => Some (remove_var var roots, heap, output)
  | Out vexp => (** vexp needs to evaluate to a nat *)
    match eval_valexp vexp s with
    | Some (Int n) => Some (roots, heap, n::output)
    | _ => None
    end
  end.

(** executing a whole program, not sure if necessary *)
Definition execute_program (program: list com): option state :=
  let fix execute (coms: list com) (s: state) := 
    match coms with
    | nil => Some s
    | c::t => 
      match small_step c s with
      | None => None
      | Some s' => execute t s'
      end
    end
  in
  execute program (nil, nil, nil).


Definition gc (s: state) : state :=
  let roots := fst (fst s) in
  let heap := snd (fst s) in
  let output := snd s in


Fixpoint mark (r: roots) (h: heap) (acc: list prt) : set ptr :=
  .

