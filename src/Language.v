Require Import Bool Arith String List ListSet Vector CpdtTactics.

(** model pointers as nats *)
Definition ptr := nat.
Definition ptr_eq_dec := eq_nat_dec.

(** model vars as nats too, a bit silly so probably change later *)
Definition var := string.
Definition var_eq_dec := string_dec.

Definition var_ptr_eq_dec : forall (l r: var * ptr), {l = r} + {l <> r}.
  Hint Resolve ptr_eq_dec var_eq_dec.
  decide equality.
Qed.

(** Types of values we can have in the heap *)
Inductive val : Type :=
| Int : nat -> val
| Pointer : ptr -> val
.

(** We will model heaps as lists of pointers and values. *)
Definition heap_t := list (ptr * list val).

Inductive valexp :=
| IntExp : nat -> valexp       (* n *)
| Deref : var -> nat -> valexp (* v[n] *)
.

Inductive com :=
| New : var -> list valexp -> com         (* var = malloc(length l) ; var[:] = l *)
| AssignMem : var -> nat -> valexp -> com (* var[i] = val *)
| AssignVar : var -> valexp -> com        (* assert(type(val) = Ptr) : var = val *)
| Drop : var -> com                       (* del var *)
| Out : valexp -> com                     (* assert(type(val) = Int) ; print(val) *)
.

(** roots is the top level var to pointers, output is ouput of the program *)
Definition roots_t := list (var * ptr).

Fixpoint roots_get (v:var) (r:roots_t) : option ptr :=
match r with
| List.nil => None
| (hv, hp)::t => if var_eq_dec hv v then Some hp else (roots_get v t)
end.
Definition roots_set (r: roots_t) (v: var) (p:ptr) : roots_t := (v,p)::r.
Definition roots_unset (r: roots_t) (v: var) : roots_t :=
  match roots_get v r with
  | Some p => List.remove var_ptr_eq_dec (v,p) r
  | None => r
  end.

Definition roots_maps (r: roots_t) (v: var) (p: ptr) : Prop :=
  List.In (v,p) r.

Definition output_t := list nat.

Fixpoint heap_get_struct (p:ptr) (h:heap_t) : option (list val) :=
match h with
| List.nil => None
| (hp, hv)::t =>
  if ptr_eq_dec hp p then
    Some hv
  else
    (heap_get_struct p t)
end.

(** val evaluation and helpers *)
Definition heap_get (p:ptr) (k: nat) (h:heap_t) : option val :=
match heap_get_struct p h with
| None => None
| Some hv => List.nth_error hv k
end.

Fixpoint set_nth {A: Type} (n: nat) (v: A) (l: list A) : option (list A) :=
  match n, l with
  | 0, h::t => Some (v::t)
  | S(n'), h::t =>
    match set_nth n' v t with
    | Some l' => Some (h::l')
    | None => None
    end
  | _, _ => None
  end.

Fixpoint heap_set_k (h: heap_t) (p: ptr) (k: nat) (v: val) : option heap_t :=
match h with
| List.nil => None
| (hp, hv)::t =>
  if ptr_eq_dec hp p then
    match set_nth k v hv with
    | Some hv' => Some ((hp,hv')::t)
    | None => None
    end
  else
    match heap_set_k t p k v with
    | Some h' => Some ((hp,hv)::h')
    | None => None
    end
end
.

Lemma heap_set_ptr_no_change : forall h h0 p p1 k v p0 l l',
  heap_set_k ((p, l) :: h) p1 k v = Some ((p0, l') :: h0) ->
  p = p0.
Proof.
  intros.
  inversion H.
  destruct (ptr_eq_dec p p1) in H1.
  * destruct (set_nth k v l) in H1; crush.
  * destruct (heap_set_k h p1 k v) in H1; crush.
Qed.

Lemma heap_set_first_neq : forall h h0 p k v p0 l l',
  p0 <> p ->
  heap_set_k ((p0, l) :: h) p k v = Some ((p0, l') :: h0) ->
  heap_set_k h p k v = Some h0.
Proof.
  intros.
  inversion H0.
  destruct (ptr_eq_dec p0 p).
  * crush.
  * destruct (heap_set_k h p k v); crush.
Qed.

Lemma heap_get_first_neq : forall h p k v p0 l,
  p0 <> p ->
  heap_get p k ((p0, l) :: h) = Some v ->
  heap_get p k h = Some v.
Proof.
  intros.
  unfold heap_get in H0.
  unfold heap_get_struct in H0.
  destruct p.
  * fold heap_get_struct in H0.
    destruct (ptr_eq_dec p0 0) in H0; intuition.
  * fold heap_get_struct in H0.
    destruct (ptr_eq_dec p0 (S p)) in H0; intuition.
Qed.

Lemma set_nth_sets : forall {A: Type} k v (l l0: list A),
  set_nth k v l = Some l0 ->
  List.nth_error l0 k = Some v.
Proof.
  induction k; intros.
  * simpl in *.
    destruct l; crush.
  * simpl in *.
    destruct l.
    - crush.
    - destruct (set_nth k v l) eqn:?.
      + crush; eauto.
      + discriminate.
Qed.

(*
Theorem heap_set_sets : forall h p k v v' h',
    heap_get p k h = Some v ->
    heap_set_k h p k v' = Some h' ->
    heap_get p k h' = Some v'
.
Proof.
  Hint Resolve heap_set_ptr_no_change heap_set_first_neq heap_get_first_neq set_nth_sets.
  induction h; intros.
  * crush.
  * unfold heap_get.
    unfold heap_get_struct.
    destruct h' eqn:?.
    - simpl in *.
      destruct a in H0.
      destruct (ptr_eq_dec p0 p) in H0.
      + destruct (set_nth k v' l) in H0; discriminate.
      + destruct (heap_set_k h p k v') in H0; discriminate.
    - destruct p0.
      destruct (ptr_eq_dec p0 p).
      + inversion H.
        destruct a.
        remember H0; clear Heqe0; eapply heap_set_ptr_no_change in e0.
        subst.
        unfold heap_set_k in H0.
        destruct (ptr_eq_dec p p) in H0; intuition.
        destruct (set_nth k v' l0) eqn:?; try congruence.
        eapply set_nth_sets in Heqo.
        crush.
      + fold heap_get.
        destruct a.
        remember H0; clear Heqe; eapply heap_set_ptr_no_change in e.
        subst.
        eauto.
Admitted.
*)

(*
Lemma set_nth_does_not_set : forall {A: Type} k k' v (l l0: list A),
  k <> k' ->
  List.nth_error l k' = Some v ->
  set_nth k v l = Some l0 ->
  List.nth_error l0 k' = Some v.
Proof.
Admitted.
*)

(*
Theorem heap_set_maintains : forall h h' p k v v',
    heap_set_k h p k v' = Some h' ->
    forall p' k',
      (p <> p' \/ k <> k') ->
      heap_get p' k' h = Some v ->
      heap_get p' k' h' = Some v
.
Proof.
  induction h; intros.
  * crush.
  * unfold heap_get.
    destruct h' eqn:?.
    - simpl in *.
      destruct a in H.
      destruct (ptr_eq_dec p0 p) in H.
      + destruct (set_nth k v' l) in H; discriminate.
      + destruct (heap_set_k h p k v') in H; discriminate.
    - destruct p0.
      destruct (ptr_eq_dec p0 p).
      + destruct a.
        destruct (ptr_eq_dec p p'); subst.
        ** destruct (ptr_eq_dec p' p'); try congruence.
           admit.
        ** admit.
      + admit.
Admitted.
*)

Definition heap_maps (h: heap_t) (p: ptr) (k: nat) (v: val) : Prop :=
  heap_get p k h = Some v
.

Definition heap_maps_struct (h: heap_t) (p: ptr) (vs: list val) : Prop :=
  heap_get_struct p h = Some vs
.

(* Must be proven for liveness *)
Theorem heap_maps_struct_indexable : forall p h vs,
  heap_get_struct p h = Some vs ->
  forall a, List.In a vs ->
  exists k, heap_maps h p k a
.
Proof.
  Hint Resolve In_nth_error.
  Hint Unfold heap_maps heap_get.
  intros.
  unfold heap_maps.
  unfold heap_get.
  destruct p; crush.
Qed.

Lemma heap_maps_implies_heap_get :
  forall h p n v,
  heap_maps h p n v ->
  exists vs,
    heap_get_struct p h = Some vs
    /\
    List.nth_error vs n = Some v
.
Proof.
  induction h ; intros.
  * inversion H.
  * specialize IHh with p n v.
    destruct a.
    unfold heap_get_struct.
    unfold heap_maps in *.
    unfold heap_get in *.
    destruct (ptr_eq_dec p0 p) eqn:?.
    - exists l. crush.
      destruct (ptr_eq_dec p p); crush.
    - crush.
      destruct (ptr_eq_dec p0 p); crush.
Qed.

Record state := mkState {
                    roots : roots_t;
                    heap : heap_t;
                    output: output_t;
                  }.

(** fresh heap pointer is 1 more than the maximum heap ptr *)
Definition fresh_heap_ptr (h: heap_t) : ptr :=
  let max := fun (p1 p2:ptr) => if le_gt_dec p1 p2 then p2 else p1 in
  let fix max_heap (h': heap_t) :=
    match h' with
    | List.nil => 0
    | (p,_)::t => max p (max_heap t)
    end
  in
  (max_heap h) + 1.


Definition eval_valexp (r: roots_t) (h: heap_t) (v: valexp) : option val :=
  match v with
  | IntExp i => Some (Int i)
  | Deref var idx =>
    match roots_get var r with
    | Some p => heap_get p idx h
    | None => None
    end
  end.

Definition update_heap (r: roots_t) (h: heap_t) (lhv: var) (lhidx: nat) (rhv: val) : option heap_t :=
  match roots_get lhv r with
  | None => None
  | Some lhp =>
    match heap_set_k h lhp lhidx rhv with
    | Some h' => Some h'
    | None => None
    end
  end.

Notation "x <-- A ; B" := (match A with | Some x => B | None => None end)
                            (right associativity, only parsing, at level 84).

Definition handle_small_step (s: state) (c: com) : option state :=
  let r := roots s in
  let h := heap s in
  let o := output s in
  match c with
  | New var vals =>
    let p := fresh_heap_ptr h in
    let r' := roots_set r var p in
    match (List.fold_right (fun vexp acc =>
                              match acc, eval_valexp r h vexp with
                              | Some vs, Some v => Some (v::vs)
                              | _, _ => None
                              end) (Some List.nil) vals) with
    | Some vals =>
      let h' := (p, vals)::h in
      Some (mkState r' h' o)
    | None =>
      None
    end
  | AssignMem lhvar lhidx rhv =>
    rhv <-- eval_valexp r h rhv ;
      h' <-- update_heap r h lhvar lhidx rhv ;
      Some (mkState r h' o)
  | AssignVar var val =>
    match eval_valexp r h val with
    | Some (Pointer p) =>
      let r' := roots_set r var p in
      Some (mkState r' h o)
    | _ => None
    end
  | Drop var =>
    let r' := roots_unset r var in
    Some (mkState r' h o)
  | Out val =>
    match eval_valexp r h val with
    | Some (Int i) => Some (mkState r h (i::o))
    | _ => None
    end
  end.
