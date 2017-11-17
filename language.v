Require Import Bool Arith String List ListSet Vector CpdtTactics.

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

Definition roots_maps (r: roots_t) (v: var) (p: ptr) : Prop :=
  List.In (v,p) r.


Definition output_t := list nat.

(** val evaluation and helpers *)
Fixpoint heap_get (p:ptr) (k: nat) (h:heap_t) : option val :=
match h with
| List.nil => None
| (hp, hv)::t =>
  if ptr_eq_dec hp p then
    List.nth_error hv k
  else
    (heap_get p k t)
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
  inversion H0.
  destruct (ptr_eq_dec p0 p); crush.
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
        destruct (ptr_eq_dec p p) in H0; crush.
        destruct (set_nth k v' l0) eqn:?; crush.
        try eapply set_nth_sets in Heqo; crush.
      + fold heap_get. 
        destruct a.
        remember H0; clear Heqe; eapply heap_set_ptr_no_change in e.
        subst.
        eauto.
Qed.

Lemma set_nth_does_not_set : forall {A: Type} k k' v (l l0: list A),
  k <> k' ->
  List.nth_error l k' = Some v ->
  set_nth k v l = Some l0 ->  
  List.nth_error l0 k' = Some v.
Proof.
Admitted.

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



Definition heap_maps (h: heap_t) (p: ptr) (k: nat) (v: val) : Prop :=
  heap_get p k h = Some v
.

Record state := mkState {
                    roots : roots_t;
                    heap : heap_t;
                    output: output_t;
                    fuel: nat;
                  }.

Inductive eval_valexp : valexp -> state -> val -> Prop :=
| IntExpEval : forall n s,
    eval_valexp (IntExp n) s (Int n)
| DerefEval : forall rv hv p k r h t f,
    roots_maps r rv p ->
    heap_maps h p k hv ->
    eval_valexp (Deref rv k) (mkState r h t f) hv
.

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

(** Remove var from roots, works even if var is not in it *)
Fixpoint remove_var (v:var) (r:roots_t) : roots_t :=
  match r with
  | List.nil => List.nil
  | (v',p')::t => if var_eq_dec v v' then remove_var v t else (v',p')::(remove_var v t)
  end.

(** Set variable to a pointer *)
Definition set_var (v:var) (p:ptr) (r:roots_t) : roots_t :=
  let without_var := remove_var v r in
  (v, p)::without_var.

Inductive small_step : com -> state -> state -> Prop :=
| NewStep : forall var vexps vals p state,
    List.Forall2 (fun vexp val => eval_valexp vexp state val) vexps vals ->
    p = fresh_heap_ptr (heap state) ->
    small_step
      (New var vexps)
      state
      (mkState
         (set_var var p (roots state))
         ((p, vals) :: (heap state))
         (output state)
         (S (fuel state)))
| AssignVarStep : forall var vexp p state,
    eval_valexp vexp state (Pointer p) ->
    small_step
      (AssignVar var vexp)
      state
      (mkState
         (set_var var p (roots state))
         (heap state)
         (output state)
         (S (fuel state))
      )
| AssignMemStep : forall var ptr k vexp val state h',
    roots_maps (roots state) var ptr ->
    eval_valexp vexp state val ->
    heap_set_k (heap state) ptr k val = Some h' ->
    small_step
      (AssignMem var k vexp)
      state
      (mkState
         (roots state)
         (h')
         (output state)
         (S (fuel state))
      )
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
         (List.cons n (output state))
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

Definition gc (f: nat) (r: roots_t) (h: heap_t) : heap_t :=
  sweep h (mark f r h nil)
.

Inductive addresing_string : Type :=
| TermStr : nat -> addresing_string
| FollowStr : addresing_string -> addresing_string
| IndexStr : nat -> addresing_string -> addresing_string
.

Inductive addresses : heap_t -> ptr -> addresing_string -> Prop :=
| TermAddressesInt : forall h p n,
    heap_maps h p (Int n) ->
    addresses h p (TermStr n)
| FollowAddressesPointer : forall h p p' rest,
    heap_maps h p (Pointer p') ->
    addresses h p' rest ->
    addresses h p (FollowStr rest)
| IndexTermAddressesStructInt : forall h p vs idx n,
    heap_maps h p (Struct vs) ->
    List.nth_error vs idx = Some (Int n) ->
    addresses h p (IndexStr idx (TermStr n))
| IndexTermAddressesStructInt : forall h p vs idx n,
    heap_maps h p (Struct vs) ->
    List.nth_error vs idx = Some (Pointer p') ->
    addresses h p' rest ->
    addresses h p (IndexStr idx (FollowStr ))
.

    addresses h p rest ->
.
| FollowAddressesPointer : forall h v p rest,
    heap_maps h p v ->
    addresses h v rest ->
    addresses h (Pointer p) (FollowStr rest)
| IndexAddressesStruct : forall h vs n v rest,
    List.nth_error vs n = Some v ->
    addresses h v rest ->
    addresses h (Struct vs) (IndexStr n rest)
.

Theorem heap_marks :
  forall address s v p,
    roots_maps (roots s) v p ->
    addresses (heap s) (Pointer p) address ->
    heap_maps (heap s) p (Int n) ->
    (
      exists p',
        set_In p' mark (fuel s) (roots s) (heap s)
        /\
        heap_maps (heap s) p' (Int n)
    )
    addresses (gc (fuel s) (roots s) (heap s)) (Pointer p) address.
Proof.

Theorem heap_equivalence :
  forall address s v p,
    roots_maps (roots s) v p ->
    addresses (heap s) (Pointer p) address ->
    addresses (gc (fuel s) (roots s) (heap s)) (Pointer p) address.
Proof.
  induction address.
  * intros.
    inversion H0.
  * intros.
    inversion H0.
    subst.
    remember (fuel s) as f.
    induction f ; subst.
  -  unfold gc, mark, sweep.

      subst.
      induction (fuel s).
    -
    induction v0.
    - inversion H5.
      subst.

      inversion H5.
      specialize (IHaddress s v p).
    intuition.
    eapply IHaddress.
Qed.

Theorem safety_1 :
  forall c s s' s'',
  small_step c s = Some s' ->
  small_step c (gc s) = Some s''.
Proof.
  intros.
  destruct c ; unfold small_step in * ; crush.
  * unfold small_step in H.
Qed.