Require Import Gc.Language.
Require Import List ListSet Equality CpdtTactics.
Require Import Coq.Program.Wf.

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

Theorem union_pointers_nodup :
  forall l,
    Forall (fun a => NoDup a) l ->
    NoDup (union_pointers l).
Proof.
  intros.
  induction l.
  constructor.
  eapply set_union_nodup ;
    inversion H ;
    eauto.
Qed.

Theorem set_union_nodup_inv_1 :
  forall l l',
    NoDup (set_union ptr_eq_dec l l') ->
    NoDup l.
Proof.
  intros l l'. revert l.
  induction l'.
  * intros.
    induction l; crush.
  * intros.
    unfold set_union in * ; fold set_union in *.
    specialize (IHl' l).
    induction (((fix set_union (x y : set nat) {struct y} : set nat :=
               match y with
               | nil => x
               | a1 :: y1 => set_add ptr_eq_dec a1 (set_union x y1)
               end) l l')).
  - eapply IHl'. constructor.
  - crush.
    destruct (ptr_eq_dec a a0).
    + eauto.
    + inversion H. subst.
      assert (NoDup s -> NoDup l).
      ** intros.
         assert (~ In a0 s).
         unfold not. intros.
         assert (In a0 (set_add ptr_eq_dec a s)). eapply set_add_intro1; auto.
         crush.
         assert (NoDup (a0 :: s)). constructor ; auto.
         intuition.
      ** eauto.
Qed.

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

Lemma heap_get_to_maps :
  forall h p v,
    heap_get_struct p h = Some v ->
    In (p,v) h.
Proof.
  induction h. crush.
  intros.
  unfold heap_get_struct in H.
  destruct a.
  edestruct ptr_eq_dec eqn:?. constructor. injection H. intros. subst. reflexivity.
  crush.
Qed.

Lemma heap_get_to_maps_2 :
  forall h p v,
    heap_get_struct p h = Some v ->
    In p (fst (split h)).
Proof.
  intros.
  specialize (heap_get_to_maps _ _ _ H).
  intros.
  unfold set_In in *. unfold ptr in *.
  assert (p = fst (p,v)). crush. rewrite H1. clear H1.
  eapply in_split_l. auto.
Qed.


Theorem set_add_noop :
  forall l a,
    set_In a l ->
    set_add ptr_eq_dec a l = l.
Proof.
  induction l. crush.
  intros.
  unfold set_In in *. unfold In in *.
  destruct H.
  * subst. unfold set_add. destruct (ptr_eq_dec a0 a0) eqn:? ; crush.
  * crush. edestruct ptr_eq_dec ; reflexivity.
Qed.

Fixpoint mark_ptr (fuel:nat) (p: ptr) (h: heap_t) : set ptr :=
  match fuel, heap_get_struct p h with
  | S n, Some vs =>
    (set_add ptr_eq_dec p
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

Definition add_vals (h: heap_t) (p: ptr) : set ptr :=
  nodup
    ptr_eq_dec
    match heap_get_struct p h with
    | Some vs =>
      (List.flat_map
         (fun v =>
            match v with
            | Int _ => nil
            | Pointer p' =>
              match heap_get_struct p' h with
              | Some _ => p'::nil
              | None => nil
              end
            end
         ) vs)
    | None => nil
    end.

Theorem add_vals_subset :
  forall h p p',
    set_In p' (add_vals h p) ->
    In p' (fst (split h)).
Proof.
  intros.
  unfold add_vals in H.
  destruct (heap_get_struct p h) eqn:?. Focus 2. crush.
  clear Heqo.
  induction l. crush.
  unfold flat_map in H ; fold flat_map in H.
  destruct a.
  remember (((fix flat_map (l : list val) : list ptr :=
               match l with
               | nil => nil
               | x :: t =>
                   match x with
                   | Int _ => nil
                   | Pointer p' =>
                       match heap_get_struct p' h with
                       | Some _ => p' :: nil
                       | None => nil
                       end
                   end ++ flat_map t
               end) l)) as foo.
  specialize (app_nil_l foo).
  intros. rewrite H0 in H. clear H0. rewrite Heqfoo in H. intuition.
  destruct (heap_get_struct p0 h) eqn:?.
  * unfold app in H.
    unfold nodup in H.
    destruct (in_dec ptr_eq_dec p0).
    - intuition.
    - crush.
      eapply heap_get_to_maps_2. apply Heqo.
  * crush.
Qed.

Fixpoint mark_ptr_single (h: heap_t) (ps: set ptr) : set ptr :=
  match ps with
  | nil => nil
  | p::ps' =>
    set_add
      ptr_eq_dec
      p
      (set_union
         ptr_eq_dec
         (add_vals h p)
         (mark_ptr_single h ps')
      )
  end.

Theorem mark_ptr_single_nodup :
  forall h ps,
    NoDup ps ->
    NoDup (mark_ptr_single h ps).
Proof.
  induction ps. crush.
  intros. inversion H. subst. intuition.
  unfold mark_ptr_single. fold mark_ptr_single.
  eapply set_add_nodup.
  eapply set_union_nodup ; auto.
  unfold add_vals. eapply NoDup_nodup.
Qed.

Theorem mark_ptr_single_monotonic_1 :
  forall h p ps,
    NoDup ps ->
    In p ps ->
    In p (mark_ptr_single h ps).
Proof.
  intros until ps. revert h p.
  induction ps. crush.
  intros.
  inversion H. clear H. subst.
  specialize (IHps h p H4).
  destruct H0. subst.
  * unfold mark_ptr_single. fold mark_ptr_single.
    eapply set_add_intro2. reflexivity.
  * unfold mark_ptr_single. fold mark_ptr_single.
    eapply set_add_intro1.
    eapply set_union_intro2.
    intuition.
Qed.

Theorem mark_ptr_single_monotonic_2 :
  forall h ps,
    NoDup ps ->
    incl ps (mark_ptr_single h ps).
Proof.
  unfold incl.
  intros.
  eapply mark_ptr_single_monotonic_1 ; auto.
Qed.

Lemma incl_cons_inv :
  forall {A: Type} (a: A) b c,
    incl (a::b) c ->
    incl b c.
Proof.
  intros until c. generalize a c.
  induction b ; induction c ; crush.
  * unfold incl. intros. inversion H0.
  * unfold incl in *.
    intros.
    specialize (H a2).
    assert (In a2 (a1 :: a0 :: b)). crush. intuition.
Qed.


Lemma mark_ptr_single_subset_1 :
  forall h ps p,
    NoDup ps ->
    incl ps (fst (split h)) ->
    set_In p (mark_ptr_single h ps) ->
    set_In p (fst (split h)).
Proof.
  induction ps. crush.
  intros. inversion H. subst. clear H.
  assert (incl ps (fst (split h))). eapply incl_cons_inv. apply H0.
  specialize (IHps p H5 H).
  unfold mark_ptr_single in * ; fold mark_ptr_single in *.
  destruct (set_add_elim _ _ _ _ H1) ; clear H1. crush. eapply incl_cons_inv ; crush.
  destruct (set_union_elim _ _ _ _ H2) ; clear H2.
  * eapply add_vals_subset. apply H1.
  * crush.
Qed.

Lemma mark_ptr_single_subset_2 :
  forall h ps,
    NoDup ps ->
    incl ps (fst (split h)) ->
    incl (mark_ptr_single h ps) (fst (split h)).
Proof.
  unfold incl.
  intros.
  eapply mark_ptr_single_subset_1. apply H. auto. auto.
Qed.

Lemma mark_ptr_single_subset_3 :
  forall h ps,
    NoDup ps ->
    incl ps (fst (split h)) ->
    length (mark_ptr_single h ps) <= length (fst (split h)).
Proof.
  intros.
  eapply NoDup_incl_length.
  eapply mark_ptr_single_nodup. auto.
  eapply mark_ptr_single_subset_2. auto. auto.
Qed.

Program Fixpoint mark_ptr_full' (h: heap_t) (ps: set ptr) (H: NoDup ps) (H': incl ps (fst (split h)))
        {measure (length h - length ps)} : set ptr :=
  let new := mark_ptr_single h ps in
  if PeanoNat.Nat.eq_dec (length ps) (length new)
  then
    new
  else
    mark_ptr_full' h new _ _
.
Next Obligation.
  clear H0.
  eapply mark_ptr_single_nodup. auto.
Defined.
Next Obligation.
  eapply mark_ptr_single_subset_2 ; auto.
Defined.
Next Obligation.
  clear mark_ptr_full'.

  assert (length ps > 0).
  destruct ps ; crush.

  assert (length (mark_ptr_single h ps) >= length ps).
  assert (incl ps (mark_ptr_single h ps)).
  eapply mark_ptr_single_monotonic_2 ; auto.
  eapply NoDup_incl_length ; auto.

  assert (length (mark_ptr_single h ps) > length ps).
  crush.

  assert (length (mark_ptr_single h ps) <= length h).
  specialize (mark_ptr_single_subset_3 _ _ H H').
  intros.
  specialize (split_length_l h). intros. crush.

  assert (length ps < length h) ; crush.
Defined.

Program Definition mark_ptr_full (r: roots_t) (h: heap_t) : set ptr :=
  let root_ptrs := (snd (split r)) in
  let present_root_ptrs := set_inter ptr_eq_dec root_ptrs (fst (split h)) in
  mark_ptr_full' h (nodup ptr_eq_dec present_root_ptrs) _ _
.
Next Obligation.
  eapply NoDup_nodup.
Defined.
Next Obligation.
  unfold incl. intros.
  specialize (nodup_In ptr_eq_dec (set_inter ptr_eq_dec (snd (split r)) (fst (split h))) a). intros. destruct H0.
  intuition. clear - H2.
  destruct (set_inter_elim _ _ _ _ H2) ; auto.
Defined.

Theorem mark_ptr_subset:
  forall f e p h,
    set_In e (mark_ptr f p h) ->
    exists v, In (e, v) h.
Proof.
  induction f ; crush.
  destruct (heap_get_struct p h) eqn:?.
  specialize (set_add_elim _ _ _ _ H). intros.
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
  specialize (set_add_elim _ _ _ _ H). intros. destruct H0.
  subst. eapply set_add_intro2. reflexivity.
  eapply set_add_intro1.

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
                       set_add ptr_eq_dec p'
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

Theorem mark_ptr_monotonic_3 :
  forall f p h vs,
    heap_maps_struct h p vs ->
    set_In p (mark_ptr (S f) p h).
Proof.
  intros.
  crush.
  eapply set_add_intro2.
  crush.
Qed.

Theorem mark_ptr_saturates :
  forall h e p,
    set_In e (mark_ptr (S (length h)) p h) ->
    set_In e (mark_ptr (length h) p h).
Proof.
Admitted.

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
    apply set_add_iff; crush.
    * intros.
      inversion H.
      subst.
      specialize (IHaddress h p'0 p' H6).
      assert (set_In p' (mark_ptr (S (length h)) p h)).
  - unfold mark_ptr ; fold mark_ptr.
    specialize (heap_maps_implies_heap_get h p n (Pointer p'0) H4).
    intros. destruct H0. destruct H0.
    rewrite H0.
    eapply set_add_intro1.
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
  - eapply mark_ptr_saturates.
    apply H0.
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
    apply set_add_iff in H.
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
  forall address r h v p p',
    roots_maps r v p ->
    addresses h p address p' ->
    set_In p' (mark r h)
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

Lemma address_extend :
  forall address h p p' p'' n v,
    addresses h p address p' ->
    heap_maps h p' n (Pointer p'') ->
    heap_maps_struct h p'' v ->
    (exists address', addresses h p address' p'').
Proof.
  induction address ; intros.
  * inversion H. destruct H2. subst. clear H.
    exists (FollowStr n TermStr).
    eapply (FollowAddresses h p' p'' p'' n TermStr). auto.
    constructor.
    unfold heap_maps in H1. unfold heap_get in H1.
    destruct (heap_get_struct p'' h) eqn:?. exists l. auto. crush.
  * crush.
    inversion H. clear H. subst.
    specialize (IHaddress h p'0 p' p'' n0 v).
    intuition.
    destruct H.
    exists (FollowStr n x).
    eapply (FollowAddresses h p p'0 p'' n x) ; auto.
Qed.

Lemma pointer_equivalence' :
  forall address r h p p',
    addresses h p address p' ->
    set_In p (mark r h) ->
    addresses (sweep h (mark r h)) p address p'.
Proof.
  induction address.
  * crush. inversion H. clear H. destruct H1.
    crush.
    remember (mark r h) as foo. clear Heqfoo.
    induction h. inversion H.
    destruct a.
    unfold sweep in * ; fold sweep in *.
    unfold heap_maps_struct in * ; fold heap_maps_struct in *.
    unfold heap_get_struct in * ; fold heap_get_struct in *.
    destruct (ptr_eq_dec p p') eqn:?.
  - crush.
    assert (set_mem ptr_eq_dec p' foo = true). eapply set_mem_correct2. auto.
    rewrite H.
    constructor. exists x. unfold heap_maps_struct. unfold heap_get_struct.
    destruct (ptr_eq_dec p' p'). crush. crush.
  - destruct (set_mem ptr_eq_dec p foo).
    + crush.
      inversion H1. destruct H2. subst.
      constructor. exists x0.
      unfold heap_maps_struct. unfold heap_get_struct.
      destruct (ptr_eq_dec p p'). crush. crush.
    + crush.
      * crush.
        inversion H. clear H. subst.
        specialize (IHaddress r h p'0 p' H7).
        assert (set_In p'0 (mark r h)).
  - clear IHaddress.
    induction r. crush.
    destruct a.
    destruct (ptr_eq_dec p'0 p0) eqn:?.
    + crush.
      assert (exists x, length h = S x). destruct h. unfold heap_maps in H5. unfold heap_get in H5. crush. exists (length h). crush.
      destruct H. rewrite H. unfold mark_ptr. fold mark_ptr.
      clear H Heqs IHr H0 H5.
      eapply set_union_intro2.
      inversion H7.
      ** destruct H. subst.
         rewrite H. eapply set_add_intro2. auto.
      ** subst.
         unfold heap_maps in H. unfold heap_get in H.
         destruct (heap_get_struct p0 h). Focus 2. crush.
         eapply set_add_intro2. auto.
    + unfold mark in * ; fold mark in *.
      unfold set_In in *.
      destruct (set_union_elim _ _ _ _ H0).
      ** crush. eapply set_union_intro1. auto.
      ** specialize (mark_ptr_correct _ _ _ _ H).
         intros.
         destruct H1.
         inversion H7.
      -- subst. clear H7.
         destruct H2.
         specialize (set_union_elim _ _ _ _ H0). intros. clear H0.
         destruct H3.
         ++ intuition.
            eapply set_union_intro1. auto.
         ++ eapply set_union_intro2. auto.
            destruct (ptr_eq_dec p' p). crush.
            assert (exists x, length h = S (S x)). destruct h. crush.
            destruct h.
            *** destruct p1.
                assert (p1 = p).
            --- unfold heap_maps in H5.
                unfold heap_get in H5.
                unfold heap_get_struct in H5.
                destruct (ptr_eq_dec p1 p). crush. crush.
            --- assert (p1 = p').
                unfold heap_maps_struct in H2.
                unfold heap_get_struct in H2.
                destruct (ptr_eq_dec p1 p'). crush. crush.
                crush.
                *** exists (length h). auto.
                *** destruct H3. rewrite H3 in H0.
                    destruct (heap_get_struct p0 h) eqn:?.
            --- unfold mark_ptr in H0. fold mark_ptr in H0.
                rewrite Heqo in H0.
                specialize (set_add_elim _ _ _ _ H0).
                intros. destruct H4 ; subst.
                +++ rewrite H3.
                    unfold mark_ptr in *. fold mark_ptr in *.
                    rewrite Heqo.
                    eapply set_add_intro1.
                    eapply (nth_union_pointers _ n).
                    unfold heap_maps in H5.
                    unfold heap_get in H5.
                    rewrite Heqo in H5.
                    specialize (@map_nth
                                  val
                                  (list ptr)
                                  (fun v : val =>
                                     match v with
                                     | Int _ => nil
                                     | Pointer p'0 =>
                                       match heap_get_struct p'0 h with
                                       | Some vs =>
                                         set_add ptr_eq_dec p'0
                                                 (union_pointers
                                                    (map
                                                       (fun v0 : val =>
                                                          match v0 with
                                                          | Int _ => nil
                                                          | Pointer p'1 => mark_ptr x1 p'1 h
                                                          end) vs))
                                       | None => nil
                                       end
                                     end) l (Int 0) n).
                    intros.
                    unfold ptr in *. unfold set in *.
                    rewrite H4. clear H4.
                    specialize (nth_default_eq n l (Int 0)). intros.
                    rewrite <- H4.
                    unfold nth_default.
                    rewrite H5.
                    destruct x1.
                    **** unfold heap_maps_struct in H2.
                         rewrite H2.
                         eapply set_add_intro2. reflexivity.
                    **** crush.
                         eapply set_add_intro2. reflexivity.
                +++ clear H0.

                    specialize (address_extend _ _ _ _ _
                                               _ _ H1 H5 H2).
                    intros.
                    destruct H0.
                    specialize (mark_ptr_marks x2 h p0 p' H0).
                    crush.
            --- inversion H1. crush. subst.
                unfold heap_maps in *. unfold heap_get in *.
                rewrite Heqo in H4. discriminate.
      -- assert (exists v, heap_maps_struct h p'0 v).
         unfold heap_maps in H2. unfold heap_get in H2.
         unfold heap_maps_struct. destruct (heap_get_struct p'0 h).
         crush. exists l. auto. discriminate.
         destruct H10.
         specialize (address_extend _ _ _ _ _ _ _ H1 H5 H10).
         intros.
         destruct H11.
         eapply set_union_intro2.
         eapply mark_ptr_marks.
         apply H11.
  - intuition.
    eapply (FollowAddresses (sweep h (mark r h)) p p'0 p' n address).
    + clear - H0 H5.
      remember (mark r h) as foo. clear Heqfoo.
      induction h. crush.
      destruct a.
      unfold sweep in * ; fold sweep in *.
      unfold heap_maps in * ; fold heap_maps in *.
      unfold heap_get in * ; fold heap_get in *.
      unfold heap_get_struct in * ; fold heap_get_struct in *.
      destruct (ptr_eq_dec p0 p) eqn:?.
      ** crush.
         assert (set_mem ptr_eq_dec p foo = true). eapply set_mem_correct2. auto.
         rewrite H. crush.
      ** crush.
         destruct (set_mem ptr_eq_dec p0 foo).
      -- crush.
      -- crush.
    + crush.
Qed.

Lemma pointer_equivalence :
  forall address r h v p p',
    roots_maps r v p ->
    addresses h p address p' ->
    addresses (sweep h (mark r h)) p address p'.
Proof.
  intros.
  eapply pointer_equivalence'.
  apply H0.
  eapply heap_marks.
  apply H.
  eapply TermAddresses.
  inversion H0.
  * apply H1.
  * unfold heap_maps in H1. unfold heap_get in H1.
    destruct (heap_get_struct p h) eqn:?.
  - exists l. crush.
  - crush.
Qed.