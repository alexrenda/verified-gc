Require Import Bool Arith String List ListSet.

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
Definition heap_t := list (ptr * val).

Inductive valexp :=
| IntExp : nat -> valexp
| StructExp : list valexp -> valexp
| VarRead : var -> valexp (** pointer associated with var *)
| Deref : var -> valexp (** value associated with var *)
| Index : var -> nat -> valexp.

Inductive com :=
| New : var -> valexp -> com
| Assign : var -> valexp -> com
| Drop : var -> com
| Out : valexp -> com.

(** roots is the top level var to pointers, output is ouput of the program *)
Definition roots_t := list (var * ptr).

Fixpoint roots_get (v:var) (r:roots_t) : option ptr :=
match r with
| nil => None
| (hv, hp)::t => if var_eq_dec hv v then Some hp else (roots_get v t)
end.

Definition roots_maps (r: roots_t) (v: var) (p: ptr) : Prop :=
  List.In (v,p) r.


Definition output_t := list nat.

(** val evaluation and helpers *)
Fixpoint heap_get (p:ptr) (h:heap_t) : option val :=
match h with
| nil => None
| (hp, hv)::t => if ptr_eq_dec hp p then Some hv else (heap_get p t)
end.

Definition heap_maps (h: heap_t) (p: ptr) (v: val) : Prop :=
  List.In (p, v) h
.

Record state := mkState {
                    roots : roots_t;
                    heap : heap_t;
                    output: output_t;
                    fuel: nat;
                  }.

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
Inductive eval_valexp : valexp -> state -> val -> Prop :=
| IntExpEval : forall n s,
    eval_valexp (IntExp n) s (Int n)
| StructExpEval : forall l vl s,
    (forall i,
        List.In i l ->
        (exists v, eval_valexp i s v /\ List.In v vl)
    ) ->
    eval_valexp (StructExp l) s (Struct vl)
| VarReadEval : forall v p r h t f,
    roots_maps r v p ->
    eval_valexp (VarRead v) (mkState r h t f) (Pointer p)
| DerefEval : forall rv hv p r h t f,
    roots_maps r rv p ->
    heap_maps h p hv ->
    eval_valexp (Deref rv) (mkState r h t f) hv
| IndexEval :forall v n p l val r h t f,
    roots_maps r v p ->
    heap_maps h p (Struct l) ->
    (n < length l) ->
    eval_valexp (Index v n) (mkState r h t f) val
.

(** fresh heap pointer is 1 more than the maximum heap ptr *)
Definition fresh_heap_ptr (h: heap_t) : ptr :=
  let max := fun (p1 p2:ptr) => if le_gt_dec p1 p2 then p2 else p1 in
  let fix max_heap (h': heap_t) :=
    match h' with
    | nil => 0
    | (p,_)::t => max p (max_heap t)
    end
  in
  (max_heap h) + 1.

(** Remove var from roots, works even if var is not in it *)
Fixpoint remove_var (v:var) (r:roots_t) : roots_t :=
  match r with
  | nil => nil
  | (v',p')::t => if var_eq_dec v v' then remove_var v t else (v',p')::(remove_var v t)
  end.

(** Set variable to a pointer *)
Definition set_var (v:var) (p:ptr) (r:roots_t) : roots_t :=
  let without_var := remove_var v r in
  (v, p)::without_var.

Inductive small_step : com -> state -> state -> Prop :=
| NewStep : forall var vexp val p state,
    eval_valexp vexp state val ->
    p = fresh_heap_ptr (heap state) ->
    small_step
      (New var vexp)
      state
      (mkState
         (set_var var p (roots state))
         ((p, val) :: (heap state))
         (output state)
         (S (fuel state)))
| AssignStep : forall var vexp p state,
    eval_valexp vexp state (Pointer p) ->
    small_step
      (Assign var vexp)
      state
      (mkState
         (set_var var p (roots state))
         (heap state)
         (output state)
         (S (fuel state)))
| DropStep : forall var state,
    small_step
      (Drop var)
      state
      (mkState
         (remove_var var (roots state))
         (heap state)
         (output state)
         (S (fuel state)))
| OutStep : forall vexp n state,
    eval_valexp vexp state (Int n) ->
    small_step
      (Out vexp)
      state
      (mkState
         (roots state)
         (heap state)
         (cons n (output state))
         (S (fuel state)))
.

Fixpoint mark_head (fuel: nat) (p: ptr) (h: heap_t) (acc: set ptr)
  : set ptr :=
  match fuel, set_mem ptr_eq_dec p acc with
  | S n, false =>
    let acc := set_add ptr_eq_dec p acc in
    match heap_get p h with
    | None => acc
    | Some val =>
      match val with
      | Int _ => acc
      | Pointer ptr =>
        mark_head n p h acc
      | Struct vals =>
        List.fold_left (
            fun a v =>
              match v with
              | Pointer ptr => mark_head n ptr h a
              | _ => a
              end
          ) vals acc
      end
    end
  | _, _ => acc
  end
.

Fixpoint mark (fuel:nat) (r: roots_t) (h: heap_t) (acc: set ptr) : set ptr :=
  match r with
  | nil => acc
  | cons root rest =>
    match root with
    | (var, ptr) =>
      let acc' := mark_head fuel ptr h acc in
      mark fuel rest h acc'
    end
  end
.

Fixpoint sweep (h: heap_t) (ptrs: set ptr) : heap_t :=
  match h with
  | nil => nil
  | cons (ptr, val) tail =>
    if set_mem ptr_eq_dec ptr ptrs then
      (ptr,val) :: (sweep tail ptrs)
    else
      sweep tail ptrs
  end
.

Definition gc (s: state) : state :=
  let roots := roots s in
  let heap := heap s in
  let output := output s in
  let fuel := fuel s in

  let reachable := mark fuel roots heap nil in
  let heap' := sweep heap reachable in
  mkState roots heap' output fuel
.

Inductive addresing_string : Type :=
| TermStr : nat -> addresing_string
| FollowStr : addresing_string -> addresing_string
| IndexStr : nat -> addresing_string -> addresing_string
.

Inductive addresses : heap_t -> val -> addresing_string -> Prop :=
| TermAddressesInt : forall h n,
    addresses h (Int n) (TermStr n)
| FollowAddressesPointer : forall h v p rest,
    heap_maps h p v ->
    addresses h v rest ->
    addresses h (Pointer p) (FollowStr rest)
| IndexAddressesStruct : forall h vs n v rest,
    List.nth_error vs n = Some v ->
    addresses h v rest ->
    addresses h (Struct vs) (IndexStr n rest)
.


Require Import CpdtTactics.

Theorem safety_1 :
  forall c s s' s'',
  small_step c s = Some s' ->
  small_step c (gc s) = Some s''.
Proof.
  intros.
  destruct c ; unfold small_step in * ; crush.
  * unfold small_step in H.
Qed.