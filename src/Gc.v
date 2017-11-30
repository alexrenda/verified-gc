Require Import Gc.Language.
Require Import List ListSet Equality CpdtTactics.

Inductive addresing_string : Type :=
| TermStr : addresing_string
| FollowStr : nat -> addresing_string -> addresing_string
.

Fixpoint address_length (address: addresing_string) : nat :=
  match address with
  | TermStr => 1
  | FollowStr n rest => S (address_length rest)
  end.

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

Theorem nth_union_pointers:
  forall l n p,
    set_In p (nth n l (@nil ptr)) ->
    set_In p (union_pointers l).
Proof.
  induction l ; induction n ; intros.
  * inversion H.
  * crush.
  * crush.
    eapply set_union_intro1. auto.
  * crush.
    specialize (IHl n p). intuition.
    eapply set_union_intro2. auto.
Qed.

Theorem nth_union_pointers_inv:
  forall l p,
    set_In p (union_pointers l) ->
    exists n, set_In p (nth n l (@nil nat)).
Proof.
  induction l. crush.
  intros.
  unfold union_pointers in H.
  fold union_pointers in H.
  specialize (set_union_elim ptr_eq_dec p a (union_pointers l) H).
  intros.
  destruct H0.
  * exists 0.
    crush.
  * specialize (IHl p H0).
    destruct IHl.
    exists (S x).
    crush.
Qed.

Lemma set_diff_union :
  forall {A: Type} (eq_dec : forall (x y: A), {x = y} + {x <> y})
         a b c,
    length (set_diff eq_dec (set_union eq_dec a b) (set_union eq_dec a c)) =
    length (set_diff eq_dec b c).
Proof.
Admitted.

Lemma set_diff_union_rewrite :
  forall {A: Type} (eq_dec : forall (x y: A), {x = y} + {x <> y})
         a b c foo,
  length (set_diff eq_dec (set_union eq_dec a b) (set_union eq_dec a c)) = foo ->
  length (set_diff eq_dec b c) = foo.
Proof.
  intros.
  specialize (set_diff_union eq_dec a b c).
  crush.
Qed.

Lemma set_diff_union_rewrite_inv :
  forall {A: Type} (eq_dec : forall (x y: A), {x = y} + {x <> y})
         a b c foo,
    length (set_diff eq_dec b c) = foo ->
    length (set_diff eq_dec (set_union eq_dec a b) (set_union eq_dec a c)) = foo.
Proof.
  intros.
  specialize (set_diff_union eq_dec a b c).
  crush.
Qed.

  (*
  induction a ; intros.
  * admit.
  * specialize IHa with b c.
    unfold set_union in *. fold set_union in *.
  * crush.
  * crush.
  * specialize IHb with nil.
    assert ((set_union eq_dec nil nil) = nil). crush.
    rewrite H in *. clear H.

    assert ((length (set_diff eq_dec (a :: b) nil)) = length (a::b)).
    unfold set_diff. destruct (set_mem eq_dec a nil) eqn:?. crush. crush.

    unfold set_union. fold set_union.
    unfold set_diff. fold set_diff.
    destruct (set_mem eq_dec a nil) eqn:?. crush.
    unfold set_add. fold set_add.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
Qed.
 *)

Fixpoint mark_ptr (fuel:nat) (p: ptr) (h: heap_t) : set ptr :=
  match fuel, heap_get_struct p h with
  | S n, Some vs =>
      (set_union ptr_eq_dec (set_add ptr_eq_dec p (empty_set ptr))
        (union_pointers
          (List.map
            (fun v =>
              match v with
              | Int _ => nil
              | Pointer p' => mark_ptr n p' h
              end
           ) vs)))
  | _, _ => nil
  end
.

Theorem mark_ptr_subset:
  forall f e p h,
    set_In e (mark_ptr f p h) ->
    exists v, In (e, v) h.
Proof.
  induction f ; crush.
  destruct (heap_get_struct p h) eqn:?.
  specialize (set_union_elim _ _ _ _ H). intros.
  destruct H0.
  * exists l. unfold heap_get_struct.
    clear IHf H.
    induction h. crush. intros. destruct a.
    unfold heap_get_struct in Heqo.
    destruct (ptr_eq_dec p0 p) eqn:? ; crush.
  * clear H.
    specialize (nth_union_pointers_inv _ _ H0). intros. destruct H. clear H0.

    specialize (@map_nth
                  val
                  (list ptr)
                  (fun v : val =>
                     match v with
                     | Int _ => nil
                     | Pointer p' => mark_ptr f p' h
                     end) l (Int 0) x).
  unfold ptr. unfold set.
  unfold ptr in H. unfold set in H.
  intros. rewrite H0 in H. clear H0.
  destruct (nth x l (Int 0)). crush.
  eapply IHf. apply H.
  * crush.
Qed.

Theorem mark_ptr_monotonic_1 :
  forall f e p h,
  set_In e (mark_ptr f p h) ->
  set_In e (mark_ptr (S f) p h).
Proof.
  induction f. crush.
  intros.
  specialize (IHf e).
  unfold mark_ptr in H.
  fold mark_ptr in H.
  unfold mark_ptr.
  fold mark_ptr.
  destruct (heap_get_struct p h). Focus 2. crush.
  specialize (set_union_elim _ _ _ _ H). intros. destruct H0.
  inversion H0. eapply set_union_intro1. crush.
  inversion H1.
  eapply set_union_intro2.

  specialize (nth_union_pointers_inv _ _ H0). intros. destruct H1. clear H0.
  eapply (nth_union_pointers _ x).

  specialize (@map_nth
                val
                (list ptr)
                (fun v : val =>
           match v with
           | Int _ => nil
           | Pointer p' =>
               match heap_get_struct p' h with
               | Some vs =>
                   set_union ptr_eq_dec (set_add ptr_eq_dec p' (empty_set ptr))
                     (union_pointers
                        (map
                           (fun v0 : val =>
                            match v0 with
                            | Int _ => nil
                            | Pointer p'0 => mark_ptr f p'0 h
                            end) vs))
               | None => nil
               end
           end) l (Int 0) x).
  unfold ptr. unfold set.
  intros. rewrite H0. clear H0.

  specialize (@map_nth
                val
                (list ptr)
                (fun v : val =>
                match v with
                | Int _ => nil
                | Pointer p' => mark_ptr f p' h
                end) l (Int 0) x).
  unfold ptr. unfold set.
  unfold ptr in H1. unfold set in H1.
  intros. rewrite H0 in H1. clear H0.
  destruct (nth x l (Int 0)). crush.
  specialize (IHf p0 h H1).
  auto.
Qed.

Theorem mark_ptr_monotonic_2 :
  forall f f' e p h,
    set_In e (mark_ptr f p h) ->
    f <= f' ->
    set_In e (mark_ptr f' p h).
Proof.
  induction f'.
  * intros.
    inversion H0.
    crush.
  * intros.
    specialize (IHf' e p h). intuition.
    inversion H0.
    - subst. auto.
    - intuition.
      eapply mark_ptr_monotonic_1.
      auto.
Qed.
Theorem mark_ptr_saturates_1 :
  forall f p h,
    length (set_diff ptr_eq_dec (mark_ptr (S f) p h) (mark_ptr f p h)) = 0 ->
    length (set_diff ptr_eq_dec (mark_ptr (S (S f)) p h) (mark_ptr (S f) p h)) = 0.
Proof.
  Admit.



  induction f.
  * admit.
  * intros.
    unfold mark_ptr in H ; fold mark_ptr in H.
    unfold mark_ptr ; fold mark_ptr.
    destruct (heap_get_struct p h). Focus 2. crush.
    specialize (set_diff_union_rewrite _ _ _ _ _ H). clear H. intros.
    eapply set_diff_union_rewrite_inv.
    induction l.
    - crush.
    -
      eapply IHf.



    specialize (set_diff_union_rewrite _ _ _ _ _ H). clear H. intros.
    specialize (set_diff_union ptr_eq_dec
                               (set_add ptr_eq_dec p (empty_set ptr)) (union_pointers
                 (map
                    (fun v : val =>
                     match v with
                     | Int _ => nil
                     | Pointer p' =>
                         match heap_get_struct p' h with
                         | Some vs =>
                             set_union ptr_eq_dec
                               (set_add ptr_eq_dec p' (empty_set ptr))
                               (union_pointers
                                  (map
                                     (fun v0 : val =>
                                      match v0 with
                                      | Int _ => nil
                                      | Pointer p'0 => mark_ptr f p'0 h
                                      end) vs))
                         | None => nil
                         end
                     end) l)) (union_pointers
                 (map
                    (fun v : val =>
                     match v with
                     | Int _ => nil
                     | Pointer p' => mark_ptr f p' h
                     end) l))).
    unfold ptr in *.
    unfold set in *.
    intros.
    rewrite H0 in H.
    clear H0.
    eapply set_diff_union.

Admitted.

Theorem mark_ptr_saturates_1 :
  forall f p h,
    length (mark_ptr (S f) p h) = length (mark_ptr f p h) ->
    length (mark_ptr (S (S f)) p h) = length (mark_ptr f p h).
Proof.
  induction f.
  * crush.
    destruct (heap_get_struct p h).
    - admit.
    - auto.
  * intros.

Qed.


Theorem mark_ptr_saturates_1 :
  forall h e p,
  exists f,
    set_In e (mark_ptr (S f) p h) ->
    set_In e (mark_ptr f p h).
Proof.
Admitted.

(* each addition fuel gives it at least one, up until it saturates *)
(* highest anything can saturate is length *)

Theorem mark_ptr_saturates_1 :
  forall h e p,
    set_In e (mark_ptr (S (length h)) p h) ->
    set_In e (mark_ptr (length h) p h).
Proof.
  intros.

  destruct (set_In_dec ptr_eq_dec e (mark_ptr (length h) p h)). auto.
  contradict n.
  intros.
  remember (length h) as n.
  revert Heqn H.
  induction n.
  * crush. admit.
  * intros.
  unfold mark_ptr in H ; fold mark_ptr in H.
  assert (exists n, (length h = S n)). destruct h. crush. exists (length h). crush.

  destruct H0.

  induction x.
  * rewrite H0. unfold mark_ptr ; fold mark_ptr.
    destruct (heap_get_struct p h) eqn:?. Focus 2. crush.
    destruct (ptr_eq_dec p e) eqn:?.
    - eapply set_union_intro1. crush.
    - eapply set_union_intro2.
      specialize (set_union_elim _ _ _ _ H). intros. destruct H1.
      + inversion H1. Focus 2. crush. crush.
      + clear H.

        specialize (nth_union_pointers_inv _ _ H1). intros. destruct H. clear H1.
        specialize (@map_nth
                      val
                      (list ptr)
                      (fun v : val =>
                         match v return list ptr with
                         | Int _ => nil
                         | Pointer p' => mark_ptr (length h) p' h
                         end) l (Int 0) x).
        unfold ptr. unfold set.
        unfold ptr in H. unfold set in H.
        intros.
        rewrite H1 in H.
        clear H1.
        eapply (nth_union_pointers _ x).
        specialize (@map_nth
                      val
                      (list ptr)
                      (fun v : val =>
                         match v return list ptr with
                         | Int _ => nil
                         | Pointer p' => nil
                         end) l (Int 0) x).
        unfold ptr. unfold set.
        intros.
        rewrite H1.
        clear H1.
        destruct (nth x l (Int 0)). crush.
        unfold ptr in H. unfold ptr in H0.
        rewrite H0 in H.
        unfold mark_ptr in H.
        admit.
  *

        specialize (

        rewrite H0 in H1. unfold mark_ptr in H1 ; fold mark_ptr in H1.

        subst.
        eapply set_union_intro1. crush.
    - eapply set_union_intro2. clear H.


  rewrite H0. unfold mark_ptr ; fold mark_ptr.
  destruct (heap_get_struct p h) eqn:?. Focus 2. crush.
  specialize (set_union_elim _ _ _ _ H). intros. destruct H1.
  * inversion H1. Focus 2. crush.
    subst.
    eapply set_union_intro1. crush.
  * eapply set_union_intro2. clear H.


 edestruct (heap_get_struct p h) eqn:?. unfold heap_get_

  destruct (set_In_dec ptr_eq_dec e (mark_ptr (length h) p h)). auto.
  specialize (mark_ptr_monotonic_3 (length h) e p h H n).
  intros.
  destruct H0. destruct H0. destruct H0.

  induction h. crush.
  intuition.


  induction h.
  * intros. crush.
  * intros.
    assert (length (a::h) = S (length h)). crush. rewrite H0. clear H0.
    unfold mark_ptr ; fold mark_ptr.



  pose (0:nat).
  intros h.
  assert (length h = length h - n). crush.
  rewrite H.
  induction n.
  * intros.
    rewrite H.

  intros h.
  pose ((length h):nat).
  assert (n = length h). crush.
  rewrite <- H.
  assert (n >= length h). crush. clear H.
  induction n. assert (length h = 0). inversion H0. crush. assert (h = nil). eapply length_zero_iff_nil. crush. crush.
  intros.
  destruct (PeanoNat.Nat.eq_dec n (length h)).
  * subst.
    assert (length h >= length h). crush.
    intuition. clear H1.
    specialize (H2 e p).
  *

  induction (length h) eqn:? ; intros. assert (h = nil). eapply length_zero_iff_nil. crush. crush.

  crush.

  destruct h. crush.
  assert (length (p0::h) = S (length h)). crush. rewrite H1. clear H1.
  destruct p0.

  unfold mark_ptr in H ; fold mark_ptr in H.
  unfold mark_ptr ; fold mark_ptr.
  destruct (heap_get_struct p ((p0, l) :: h)).
  * specialize (set_union_elim _ _ _ _ H). intros. destruct H1.
    - eapply set_union_intro1. crush.
    - eapply set_union_intro2.
      clear H.
      specialize (nth_union_pointers_inv _ _ H1). intros. destruct H. clear H1.
      eapply (nth_union_pointers _ x).

      specialize (@map_nth
                    val
                    (list ptr)
                    (fun v : val =>
                       match v return list ptr with
                       | Int _ => nil
                       | Pointer p' => mark_ptr (length h) p' ((p0,l)::h)
                       end) l0 (Int 0) x).
      intros. rewrite H1. clear H1.

      specialize (@map_nth
                    val
                    (list ptr)
                    (fun v : val =>
                       match v return list ptr with
                       | Int _ => nil
                       | Pointer p' => mark_ptr f p' ((p0,l)::h)
                       end) l0 (Int 0) x).
      intros.
      unfold ptr in H; unfold ptr in H1 ; unfold set in H ; unfold set in H1.
      rewrite H1 in H. clear H1.
      destruct (nth x l0 (Int 0)). crush.
      specialize (IHf ((p0,l)::h) e p1). intuition.
      destruct (Compare_dec.le_gt_dec f (length ((p0,l) :: h))).
      + assert (f = length ((p0, l) :: h)). crush.
        subst. clear H0 l1 H1.
Admitted.
(*
        eapply mark_ptr_saturates_1.
      + intuition.
      eapply IHf.
  * crush.
Qed.
  intros.
  assert (exists n, length h = S n). destruct h. crush. exists (length h). crush.
  destruct H1.
  specialize (IHf h e).
  rewrite H1 in *. clear H1.
  clear IHf.
  induction x ; induction f ; try solve [crush].
  *
  rewrite H1.
  destruct (Compare_dec.gt_dec f (S x)). Focus 2. assert (f = S x). crush. subst. clear n. clear H0. rewrite <- H1 in *. clear H1. clear IHf.
  admit.
  specialize (IHf p).
  eapply IHf.

  * admit.
  *
  unfold mark_ptr in *. fold mark_ptr in *.
  specialize (IHf h e p).

  induction h. intros. assert (exists f', f = S f'). inversion H0. crush. crush. crush.
  intros.
  assert (length (a::h) = S (length h)). crush. rewrite H1. clear H1.

  induction f. crush.
  intros.


  intros.
  eapply IHf.

  destruct h. crush.
  intros.

  assert (length (a::h) = S (length h)). crush. rewrite H1. clear H1.
  unfold mark_ptr in * ; fold mark_ptr in *.

  unfold mark_ptr.
Qed.

Theorem mark_ptr_saturates :
  forall f h e p,
    set_In e (mark_ptr f p h) ->
    set_In e (mark_ptr (length h) p h).
Proof.
  induciton f


  induction f ; induction h ; try solve [crush].
  intros.
  assert (length (a::h) = S (length h)). crush. rewrite H0. clear H0.
  unfold mark_ptr in * ; fold mark_ptr in *.
  destruct a.
  destruct (ptr_eq_dec p0 p) eqn:?.
  * unfold heap_get_struct in *. rewrite Heqs in *.
    destruct (ptr_eq_dec e p) eqn:?.
    - eapply set_union_intro1. crush.
    - eapply set_union_intro2.
      specialize (set_union_elim ptr_eq_dec _ _ _ H).
      intros.
      destruct H0 ; crush.
      specialize (nth_union_pointers_inv _ _ H0).
      intros. destruct H1.
      eapply (nth_union_pointers _ x).
      specialize (@map_nth
                    val
                    (list ptr)
                    (fun v : val =>
                       match v return list ptr with
                       | Int _ => nil
                       | Pointer p' => mark_ptr (length h) p' ((p,l)::h)
                     end) l (Int 0) x).
      intros. rewrite H2 ; clear H2.

      specialize (@map_nth
                    val
                    (set ptr)
                    (fun v : val =>
                       match v with
                       | Int _ => nil
                       | Pointer p' => mark_ptr f p' ((p, l) :: h)
                       end) l (Int 0) x).
      intros. intuition.
      unfold set in H1.
      unfold set in H2.
      unfold ptr in H2.
      unfold ptr in H1.
      rewrite H2 in H1. clear H2.
      specialize (nth_default_eq x l (Int 0)). intros.
      rewrite <- H2. rewrite <- H2 in H1. intros. clear H2.
      destruct (nth_default (Int 0) l x) eqn:?. crush.

      specialize (nth_default_eq x l (Int 0)). intros.
      unfold n

      specialize (@nth_default_eq (set ptr) x (map
               (fun v : val =>
                match v with
                | Int _ => nil
                | Pointer p' => mark_ptr f p' ((p, l) :: h)
                end) l) (@nil nat)).
      intros.
      rewrite <- H2 in H1.
      clear H2.

      destruct ((@nth_default (set ptr) (@nil nat)
            (@map val (list ptr)
               (fun v : val =>
                match v return (list ptr) with
                | Int _ => @nil ptr
                | Pointer p' =>
                    mark_ptr f p'
                      (@cons (prod ptr (list val)) (@pair ptr (list val) p l) h)
                end) l) x)). crush
      destruct ((nth_default nil
            (map
               (fun v : val =>
                match v with
                | Int _ => nil
                | Pointer p' => mark_ptr f p' ((p, l) :: h)
                end) l) x)) eqn:?.
      rewrite Heql0 in H1.

      edestruct nth_default eqn:?. crush.

      specialize (@map_nth
                    val
                    (list ptr)
                    (fun v : val =>
                       match v return list ptr with
                       | Int _ => @nil ptr
                       | Pointer p' => mark_ptr f p' ((p,l)::h)
                       end) l (Int 0) x).
      intros. intuition.
      rewrite H2 in H1.

      specialize (map_ne
      unfold nth_default. rewrite H0.
      specailze
      eapply IHh.
Admitted.
(*
  induction f ; induction h ; crush.
  destruct (ptr_eq_dec a0 p) eqn:?.
  *
  * crush.
  * induction h.
  - crush.
  - intros.
Admitted.
*)
*)
Theorem mark_ptr_marks :
  forall address h p p',
    addresses h p address p' ->
    set_In p' (mark_ptr (List.length h) p h)
.
Proof.
  induction address.
  * intros.
    inversion H. clear H.
    inversion H0. clear H0.
    subst.
    induction h.
    - inversion H.
    - assert (length (a :: h) = S (length h)) ; auto.
      rewrite H0.
      unfold mark_ptr.
      rewrite H.
      apply set_union_iff; crush.
  * intros.
    inversion H.
    subst.
    specialize (IHaddress h p'0 p' H6).
    assert (exists n0, set_In p' (mark_ptr n0 p h)).
    - exists (S (length h)).
      unfold mark_ptr ; fold mark_ptr.
      specialize (heap_maps_implies_heap_get h p n (Pointer p'0) H4).
      intros. destruct H0. destruct H0.
      rewrite H0.
      eapply set_union_intro2.
      eapply (nth_union_pointers _ n).

      specialize (@map_nth
                    val
                    (list ptr)
                    (fun v : val =>
                       match v return list ptr with
                       | Int _ => nil
                       | Pointer p'1 => mark_ptr (length h) p'1 h
                     end) x (Int 0) n).
      intros. rewrite H2 ; clear H2.
      specialize (nth_default_eq n x (Int 0)). intros.
      rewrite <- H2. intros. clear H2.
      unfold nth_default. rewrite H1.
      auto.
    - destruct H0.
      eapply mark_ptr_saturates. apply H0.
Qed.

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


Fixpoint mark (r: roots_t) (h: heap_t) : set ptr :=
  match r with
  | List.nil => List.nil
  | List.cons (var, ptr) rest =>
    set_union ptr_eq_dec (mark rest h) (mark_ptr (length h) ptr h)
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

Definition gc (r: roots_t) (h: heap_t) : heap_t :=
  sweep h (mark r h)
.

Theorem heap_marks :
  forall address roots heap var ptr ptr',
    roots_maps roots var ptr ->
    addresses heap ptr address ptr' ->
    set_In ptr' (mark roots heap)
.
Proof.
  Hint Resolve set_union_iff.
  intros address r.
  induction r.
  * crush.
  * intros.
    destruct a.
    specialize IHr with h v p p'.
    unfold roots_maps in *.
    specialize (in_inv H). intros.
    destruct H1.
    - clear H. injection H1. clear H1. intros. subst.
      unfold mark. fold mark.
      specialize (mark_ptr_marks address h p p' H0).
      intros.
      eapply set_union_intro2. auto.
    - intuition.
      crush.
      + apply set_union_iff.
        crush.
      + apply set_union_iff.
        crush.
Qed.


Lemma pointer_equivalence :
  forall address r h v p p' h',
    roots_maps r v p ->
    addresses h p address p' ->
    sweep h (mark r h) = h' ->
    addresses h' p address p'.
Proof.
  induction address.
  * intros.
    specialize (heap_marks TermStr r h v p p' H H0).
    intros.
    inversion H0. subst.
    constructor.
    destruct H3.
    exists x.
    induction h ; crush.
    destruct a.
    destruct (ptr_eq_dec p p'). subst.
    - unfold heap_maps_struct in H1. unfold heap_get_struct in H1.
      destruct (ptr_eq_dec p' p') ; crush.
      assert (set_mem ptr_eq_dec p' (mark r ((p', x) :: h)) = true).
      eapply set_mem_correct2. auto.
      crush.
      unfold heap_maps_struct. unfold heap_get_struct.
      destruct (ptr_eq_dec p' p') ; crush.
    - assert (set_mem ptr_eq_dec p (mark r ((p, l) :: h)) = true).
      unfold mark.
      induction r. crush.
      destruct a.
      destruct (ptr_eq_dec p0 p).
      + subst.
        eapply set_mem_correct2.
        eapply set_union_intro2.
        assert (length ((p, l) :: h) = S (length h)). crush.
        rewrite H3. clear H3.
        unfold mark_ptr. fold mark_ptr.
        unfold heap_get_struct. fold heap_get_struct.
        destruct (ptr_eq_dec p p) ; crush.
        eapply set_union_intro1. crush.
      + assert (roots_maps r v p'). unfold roots_maps in *. unfold In in H.
        destruct H. injection H. intros. rewrite H3 in n0.
        assert (addresses h p' TermStr p').


    eapply TermAddresses.

    constructor.
    eapply heap_marks.
Qed.

(* Must be proved for liveness *)
Lemma pointer_equivalence :
  forall address s v p p' h,
    roots_maps (roots s) v p ->
    addresses (heap s) p address p' ->
    sweep (heap s) (mark (roots s) (heap s)) = h ->
    addresses h p address p'.
Proof.
  induction address.
  * intros.
    inversion H0; subst.
    destruct H2.
    constructor.
    exists x.
    induction (heap s); crush.
    destruct a.
    unfold heap_maps_struct in *.
    destruct (ptr_eq_dec p p') eqn:?.
    - crush.
      rewrite Heqs0 in H1.
      edestruct set_mem eqn:?.
      + crush.
      + contradict Heqb.
        unfold mark.
        crush.
        clear - H2 H.
        induction (roots s). crush.
        destruct a.
        destruct (ptr_eq_dec p p') eqn:?.
        ** crush.
           rewrite Heqs0 in H2.
           specialize (set_mem_complete1 ptr_eq_dec p' _ H2).
           intros. contradiction H0.
           eapply set_union_intro2.
           eapply set_union_intro1.
           crush.
        ** unfold roots_maps in *.
           unfold In in H.
           destruct H. crush.
           intuition.
           remember ((fix mark (r : roots_t) (h : heap_t) {struct r} :
           set ptr :=
             match r with
             | nil => nil
             | (_, ptr0) :: rest =>
                 set_union ptr_eq_dec (mark rest h) (mark_ptr (length h) ptr0 h)
             end) r ((p', x) :: h)) as foo.
           clear - H0 H2.
           assert (set_mem ptr_eq_dec p' foo = true).
           destruct (set_In_dec ptr_eq_dec p' foo). eapply set_mem_correct2. auto.
           specialize (set_mem_complete2 ptr_eq_dec p' foo n). auto.
           specialize (set_mem_correct1 ptr_eq_dec p' foo H). intros.
           specialize (set_mem_complete1 ptr_eq_dec p' _ H2). intros.
           contradict H3.
           eapply set_union_intro1. auto.
    - assert (addresses h p' TermStr p').
      constructor. unfold heap_maps_struct.
      exists x.
      crush.
      rewrite Heqs0 in H1. crush.
      intuition.
      assert (heap_get_struct p' h = Some x). crush. rewrite Heqs0 in H1. crush.
      intuition.
      edestruct set_mem eqn:?.
      + unfold heap_get_struct. rewrite Heqs0. fold heap_get_struct.
        admit.
      + admit.

      edestruct set_mem eqn:?.

           specialize (set_mem_complete1 ptr_eq_dec p' _ H0).
           unfold not.
           intros.
           assert (set_mem ptr_eq_dec p' foo = true).
           unfo
           crush.
           contradict H1.
           eapply set_union_intro1.
           contradict H0.
           crush.
           unfold not in H1.
           eapply H0 in H1.

        unfold not. intros.
        specialize (set_mem_complete1 ptr_eq_dec p' (set_union ptr_eq_dec
            ((fix mark (r : roots_t) (h : heap_t) {struct r} :
              set ptr :=
                match r with
                | nil => nil
                | (_, ptr0) :: rest =>
                    set_union ptr_eq_dec (mark rest h) (mark_ptr (length h) ptr0 h)
                end) r ((p', l) :: h))
            (mark_ptr (length ((p', l) :: h)) p ((p', l) :: h))) H2).
        intros.
        contradiction H3.

        unfold mark_ptr.
        assert ((length ((p', l) :: h)) = S (length h)). crush.
        rewrite H4.
        unfold hea


      edestruct set_mem.
    - unfold heap_maps_struct in *.
      crush.
      edestruct ptr_eq_dec. crush.
      intuition.
    unfold sweep.

    eexists. apply H1.
    crush.
    inversion H2.
    inversion H5.
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
