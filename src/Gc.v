Require Import Gc.Language.
Require Import List ListSet Equality CpdtTactics.

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

Fixpoint union_pointers (l : list (set ptr)) : set ptr :=
  match l with
  | nil => (empty_set ptr)
  | h::t => (set_union ptr_eq_dec h  (union_pointers t))
  end.

Fixpoint mark_ptr (fuel:nat) (p: ptr) (h: heap_t) : set ptr :=
  match fuel, heap_get_struct p h with
  | S n, Some vs =>
      (set_union ptr_eq_dec (set_add ptr_eq_dec p (empty_set ptr))
        (union_pointers 
          (List.map
            (fun v =>
              match v with
              | Int _ => List.nil
              | Pointer p' => mark_ptr n p' h
              end
           ) vs)))
  | _, _ => List.nil
  end
.

Theorem mark_ptr_marks :
  forall address h p p',
    addresses h p address p' ->
    exists f, set_In p' (mark_ptr f p h)
.
Proof.
  induction address.
  * intros.
    inversion H. clear H.
    inversion H0. clear H0.
    subst.
    exists 1.
    unfold mark_ptr.
    rewrite H.
    apply set_union_iff; crush.
  * intros.
    inversion H. clear H.
    subst.
    specialize (IHaddress h p'0 p' H6).
    inversion IHaddress. clear IHaddress.
    exists (S x).
    specialize (heap_maps_implies_heap_get h p n (Pointer p'0) H4).
    intros.
    inversion H0 ; clear H0.
    destruct H1.
    unfold mark_ptr.
    fold mark_ptr.
    rewrite H0.
    specialize (List.map_nth_error (fun v : val =>
           match v with
           | Int _ => nil
           | Pointer p'1 => mark_ptr x p'1 h
           end) n x0 H1).
    intros.
    apply set_union_iff.
    crush.
Admitted.

Theorem mark_ptr_correct :
  forall h p p' f,
    set_In p' (mark_ptr f p h) ->
    exists address, addresses h p address p'
.
Proof.
  Hint Resolve set_union_emptyL.
  Hint Constructors addresses addresing_string.
  intros.
  dependent induction f generalizing p.
  - unfold mark_ptr in H.
    intuition.
  - unfold mark_ptr in H.
    fold mark_ptr in H.
    destruct (heap_get_struct p h) eqn:?; intuition.
    assert (exists vs, heap_maps_struct h p vs); eauto.
    remember (heap_maps_struct_indexable p h l).
    assert (forall a, In a l -> exists k, heap_maps h p k a); intuition.
    clear Heqo.
    clear Heqe.
    clear e.
    apply set_union_iff in H.
    destruct H.
    * crush. 
      eauto.
    * dependent induction l.
      + crush.
      + rewrite map_cons in H.
        destruct a eqn:?.
        -- crush.
           apply set_union_emptyL in H.
           eauto.
        -- simpl in H.
           apply set_union_iff in H.
           destruct H.
           ** specialize IHf with p0.
              intuition.
              edestruct H2.
              assert (exists k, heap_maps h p k a).
              ++ crush.
              ++ edestruct H4.
                 exists (FollowStr x0 x).
                 eapply (FollowAddresses h p p0 p'); subst; eauto.
           ** apply IHl; intuition.
Qed.


Fixpoint mark (fuel:nat) (r: roots_t) (h: heap_t) : set ptr :=
  match r with
  | List.nil => List.nil
  | List.cons (var, ptr) rest =>
    set_union ptr_eq_dec (mark fuel rest h) (mark_ptr fuel ptr h)
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
  Hint Resolve set_union_iff.
  intros address s.
  induction (roots s).
  * crush.
  * intros.
    destruct a.
    specialize IHr with v p p'.
    unfold roots_maps in *.
    specialize (in_inv H). intros.
    destruct H1.
    - clear H. injection H1. clear H1. intros. subst.
      unfold mark. fold mark.
      specialize (mark_ptr_marks address (heap s) p p' H0).
      intros.
      inversion H. clear H.
      exists x.
      eapply set_union_intro2. auto.
    - intuition.
      inversion H3. clear H3.
      exists x.
      crush.
      + apply set_union_iff.
        crush.
      + apply set_union_iff.
        crush.
Qed.

(* Must be proved for liveness *)
Lemma pointer_equivalence :
  forall address s v p p' h,
    roots_maps (roots s) v p ->
    addresses (heap s) p address p' ->
    sweep (heap s) (mark (fuel s) (roots s) (heap s)) = h ->
    addresses h p address p'.
Proof.
(*  induction address.
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
 *)
Admitted.

(*
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
