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

Definition heap_maps_struct (h: heap_t) (p: ptr) (vs: list val) : Prop :=
  heap_get_struct p h = Some vs
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

Inductive addresing_string : Type :=
| TermStr : addresing_string
| FollowStr : nat -> addresing_string -> addresing_string
.

Inductive addresses : heap_t -> ptr -> addresing_string -> ptr -> Prop :=
| TermAddresses : forall h p,
    (exists vs, heap_maps_struct h p vs) ->
    addresses h p TermStr p
| FollowAddresses : forall h p p' p'' k rest,
    heap_maps h p k (Pointer p') ->
    addresses h p' rest p'' ->
    addresses h p (FollowStr k rest) p''
.

Fixpoint mark_ptr (fuel:nat) (p: ptr) (h: heap_t) : set ptr :=
  match fuel, heap_get_struct p h with
  | S n, Some vs =>
      List.fold_left
        (set_union ptr_eq_dec)
        (List.map
           (fun v =>
              match v with
              | Int _ => List.nil
              | Pointer p => mark_ptr n p h
              end
           ) vs)
        (set_add ptr_eq_dec p (empty_set ptr))
  | _, _ => List.nil
  end
.

Require Import CpdtTactics.

Lemma fold_union_1 :
  forall {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
         (vs: list (set A)) (acc acc': set A) (a: A),
    List.fold_left (set_union eq_dec) vs acc = acc' ->
    set_In a acc ->
    set_In a acc'.
Proof.
  induction vs.
  * intros.
    subst.
    unfold List.fold_left. auto.
  * intros.
    specialize (fold_left_app (set_union eq_dec) (List.cons a List.nil) vs acc).
    crush.
    specialize (IHvs (set_union eq_dec acc a) (List.fold_left (set_union eq_dec) vs (set_union eq_dec acc a)) a0).
    assert (set_In a0 (set_union eq_dec acc a)). eapply set_union_intro1. auto.
    intuition.
Qed.

Theorem mark_ptr_marks :
  forall address h p p',
    addresses h p address p' ->
    exists f, set_In p' (mark_ptr f p h)
.
Proof.
  induction address.
  * exists 1.
    inversion H.
    inversion H0.
    crush.
    induction x.
    - crush.
    - remember (List.map
          (fun v : val =>
           match v with
           | Int _ => Datatypes.nil
           | Pointer _ => Datatypes.nil
           end) (a :: x)) as vs.
      remember (List.fold_left (set_union ptr_eq_dec) vs (p' :: Datatypes.nil)) as acc'.
      eapply fold_union_1. auto. crush.
  * intros.
    inversion H.
    subst.
    specialize (IHaddress h p p').
    intuition.
    crush.
Admitted.

Fixpoint mark (fuel:nat) (r: roots_t) (h: heap_t) : set ptr :=
  match r with
  | List.nil => List.nil
  | List.cons root rest =>
    match root with
    | (var, ptr) =>
      set_union ptr_eq_dec (mark fuel rest h) (mark_ptr fuel ptr h)
    end
  end
.

Fixpoint sweep (h: heap_t) (ptrs: set ptr) : heap_t :=
  match h with
  | List.nil => List.nil
  | List.cons (ptr, val) tail =>
    if set_mem ptr_eq_dec ptr ptrs then
      (ptr,val) :: (sweep tail ptrs)
    else
      sweep tail ptrs
  end
.

Definition gc (f: nat) (r: roots_t) (h: heap_t) : heap_t :=
  sweep h (mark f r h)
.

Theorem heap_marks :
  forall address s v p p',
    roots_maps (roots s) v p ->
    addresses (heap s) p address p' ->
    exists f, set_In p' (mark f (roots s) (heap s))
.
Proof.
(*
  induction address.
  * intros.
    exists 1.
    inversion H0 ; clear H0.
    inversion H1 ; clear H1.
    inversion H0 ; subst.
    unfold mark.
    induction (roots s). auto.
    destruct a.
    inversion H.
    - injection H1. intros. subst. clear H1.

      unfold mark_ptr.
      fold mark_ptr.
      fold mark.
      edestruct set_mem eqn:?.
      specialize (set_mem_correct1 ptr_eq_dec p' (mark 1 r (heap s)) Heqb). auto.
      destruct (heap_get_struct p' (heap s)) eqn:?.
      + injection H4. intros. subst. clear H4.
        clear H0.
        induction x.
        ** eapply set_add_intro2. crush.
        ** crush.




      inversion H. injection H1. intros. subst. clear H1. crush.

    destruct a eqn:?.
    subst.
    destruct H. injection H ; intros ; subst.
    - induction (heap s).
      + crush.
      + inversion H0.
        destruct a.
        destruct (ptr_eq_dec p p'); subst.
        ** injection H2. intros. subst. clear H2.
           crush.
           edestruct ptr_eq_dec in H4.
            -- admit.
            -- contradiction n. auto.
        **
           unfold mark.
           unfold mark_ptr.
           fold mark_ptr.
           crush.
        destruct (set_mem ptr_eq_dec p' Datatypes.nil) eqn:? ; crush.


        crush.
        destruct p.

        crush.
    - intuition.
 auto.    unfold roots_maps in H.

    destruct (var_eq_dec v0 v) eqn:?.
    - subst.
      unfold roots_maps in H.
      unfold List.In in H.
      destruct H.
      + crush.
        induction (heap s).
        ** crush.
        ** crush.
        fold mark_ptr.
      inversion H.
      inversion H.
    crush.
    subst.
    u

    induction (roots s).
    - unfold roots_maps in H.
      inversion H.
    - unfold roots_maps in H.
      unfold List.In in H.
      destruct a.
      destruct H eqn:?.
      + subst.
        inversion H1.

    exists 1.
    inversion H0.
    inversion H1.
    unfold mark.
    unfold mark.
    subst.
    inversion H0.
*)
Admitted.

(*
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
*)
