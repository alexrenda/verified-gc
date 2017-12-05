Require Import Gc.Language.
Require Import List ListSet Equality CpdtTactics.
Require Import Coq.Program.Wf Coq.Logic.ProofIrrelevance FunInd Recdef.

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

Definition mark_ptr_single (h: heap_t) (ps: set ptr) : set ptr :=
  nodup
    ptr_eq_dec
    (
      List.flat_map (
          fun p =>
            set_add
              ptr_eq_dec
              p
              (add_vals h p)
        ) ps
    ).

Theorem mark_ptr_single_nodup :
  forall h ps,
    NoDup ps ->
    NoDup (mark_ptr_single h ps).
Proof.
  intros.
  eapply NoDup_nodup.
Qed.

Lemma nodup_In_fwd :
  forall p l,
    In p (nodup ptr_eq_dec l) ->
    In p l.
Proof.
  intros.
  eapply nodup_In.
  apply H.
Qed.

Lemma nodup_In_inv :
  forall p l,
    In p l ->
    In p (nodup ptr_eq_dec l).
Proof.
  intros.
  eapply nodup_In.
  apply H.
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
    eapply nodup_In.
    unfold flat_map ; fold flat_map.
    eapply in_or_app.
    left.
    eapply set_add_intro2. reflexivity.
  * intuition.
    unfold mark_ptr_single ; fold mark_ptr_single.
    eapply nodup_In.
    unfold flat_map ; fold flat_map.
    eapply in_or_app.
    right.
    unfold mark_ptr_single in H0.
    specialize (nodup_In_fwd _ _ H0).
    intros.
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
  specialize (nodup_In_fwd _ _ H1).
  intros.
  unfold flat_map in * ; fold flat_map in *.
  destruct (in_app_or _ _ _ H2) ; clear H2.
  * destruct (set_add_elim _ _ _ _ H3) ; clear H3.
    - unfold incl in H0.
      specialize H0 with a.
      assert (In a (a :: ps)) ; crush.
    - eapply add_vals_subset.
      apply H2.
  * unfold mark_ptr_single in IHps.
    unfold flat_map in IHps.
    unfold set_In in *.
    specialize (nodup_In_inv _ _ H3).
    intros.
    clear H3.
    intuition.
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

Lemma mark_ptr_single_saturates_inv :
  forall h ps,
    NoDup ps ->
    incl ps (fst (split h)) ->
    length ps = length (mark_ptr_single h ps) ->
    incl (mark_ptr_single h ps) ps.
Proof.
  intros.
  eapply NoDup_length_incl.
  auto.
  crush.
  eapply mark_ptr_single_monotonic_2.
  auto.
Qed.

Functional Scheme mark_ptr_single_funind := Induction for mark_ptr_single Sort Prop.

Lemma in_flat_map_fwd : forall (f:ptr->set ptr)(l:list ptr)(y:ptr),
    In y (flat_map f l) ->
    exists x, In x l /\ In y (f x).
Proof.
  eapply in_flat_map.
Qed.

Lemma in_flat_map_inv : forall (f:ptr->set ptr)(l:list ptr)(y:ptr),
    (exists x, In x l /\ In y (f x)) ->
    In y (flat_map f l).

Proof.
  eapply in_flat_map.
Qed.

Lemma mark_ptr_single_equiv :
  forall h ps ps',
    NoDup ps ->
    incl ps (fst (split h)) ->
    NoDup ps' ->
    incl ps' (fst (split h)) ->
    incl ps ps' ->
    incl ps' ps ->
    incl (mark_ptr_single h ps) (mark_ptr_single h ps').
Proof.
  unfold incl.
  intros.
  unfold mark_ptr_single in *.
  specialize (nodup_In_fwd _ _ H5) ; clear H5 ; intros.
  eapply nodup_In_inv.
  specialize (in_flat_map_fwd _ _ _ H5) ; clear H5 ; intros.
  destruct H5. destruct H5.
  eapply in_flat_map_inv. exists x. crush.
Qed.

Lemma mark_ptr_single_saturates :
  forall h ps,
    NoDup ps ->
    incl ps (fst (split h)) ->
    incl (mark_ptr_single h ps) ps ->
    incl (mark_ptr_single h (mark_ptr_single h ps)) (mark_ptr_single h ps).
Proof.
  intros.
  eapply mark_ptr_single_equiv ; auto.
  * eapply mark_ptr_single_nodup. auto.
  * eapply mark_ptr_single_subset_2. auto. auto.
  * eapply mark_ptr_single_monotonic_2. auto.
Qed.

Function mark_ptrs (h: heap_t) (ps: set ptr) (H: NoDup ps) (H': incl ps (fst (split h))) {measure (fun z => (length h - length z)) ps} : set ptr :=
  let new := mark_ptr_single h ps in
  if PeanoNat.Nat.eq_dec (length ps) (length new)
  then
    new
  else
    mark_ptrs h new (mark_ptr_single_nodup h ps H) (mark_ptr_single_subset_2 h ps H H')
.
Proof.
  intros.
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

Program Definition mark (r: roots_t) (h: heap_t) : set ptr :=
  let root_ptrs := (snd (split r)) in
  let present_root_ptrs := set_inter ptr_eq_dec root_ptrs (fst (split h)) in
  mark_ptrs h (nodup ptr_eq_dec present_root_ptrs) _ _
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

Theorem mark_ptrs_fixy :
  forall h ps p H1 H2 H3 H4,
    NoDup ps ->
    set_In p (mark_ptrs h (mark_ptr_single h ps) H1 H2) ->
    set_In p (mark_ptrs h ps H3 H4).
Proof.
  intros until 2.
  functional induction (mark_ptrs h ps H3 H4); intros ; clear e.
  * rewrite mark_ptrs_equation in H0.
    edestruct PeanoNat.Nat.eq_dec.
    - assert (incl (mark_ptr_single h (mark_ptr_single h ps)) (mark_ptr_single h ps)).
      eapply mark_ptr_single_saturates_inv ; auto.

      unfold incl in H4.
      specialize H4 with p.
      intuition.
    - contradict n.
      specialize (mark_ptr_single_saturates h ps H).
      assert (incl (mark_ptr_single h ps) ps).
      eapply NoDup_length_incl.
      auto. crush. eapply mark_ptr_single_monotonic_2. auto.
      intros.
      intuition.

      assert (length (mark_ptr_single h (mark_ptr_single h ps)) <= length (mark_ptr_single h ps)).
      eapply NoDup_incl_length. eapply mark_ptr_single_nodup. auto. auto.

      assert (length (mark_ptr_single h ps) <= length (mark_ptr_single h (mark_ptr_single h ps))).
      eapply NoDup_incl_length. auto.
      eapply mark_ptr_single_monotonic_2. auto.
      crush.
  * assert (H1 = (mark_ptr_single_nodup h ps H3)).
    eapply proof_irrelevance. rewrite <- H4. clear H4.
    assert (H2 = (mark_ptr_single_subset_2 h ps H3 H')).
    eapply proof_irrelevance. rewrite <- H4. clear H4.
    auto.
Qed.

Theorem mark_ptrs_nodup:
  forall h ps H H',
    NoDup ps ->
    NoDup (mark_ptrs h ps H H').
Proof.
  intros.
  functional induction (mark_ptrs h ps H H'); intros ; clear e.
  * eapply mark_ptr_single_nodup. auto.
  * assert (NoDup (mark_ptr_single h ps)). eapply mark_ptr_single_nodup.
    auto.
    intuition.
Qed.

Theorem mark_ptrs_subset :
  forall h ps H H',
    incl (mark_ptrs h ps H H') (fst (split h)).
Proof.
  intros.
  functional induction (mark_ptrs h ps H H'); intros ; clear e.
  * eapply mark_ptr_single_subset_2. auto. auto.
  * auto.
Qed.

Theorem mark_ptrs_monotonic :
  forall h p ps H H',
    set_In p ps ->
    set_In p (mark_ptrs h ps H H').
Proof.
  intros.
  functional induction (mark_ptrs h ps H H'); intros ; clear e.
  * assert (incl ps (mark_ptr_single h ps)).
    eapply mark_ptr_single_monotonic_2. auto.
    unfold incl in H1.
    specialize (H1 p).
    intros.
    intuition.
  * assert (set_In p (mark_ptr_single h ps)).
    eapply mark_ptr_single_monotonic_2 ; auto.
    intuition.
Qed.

(*
Theorem mark_ptrs_monotonic_2 :
  forall h p p' ps H1 H2 H3 H4,
    set_In p (mark_ptrs h ps H1 H2) ->
    set_In p (mark_ptrs h (p'::ps) H3 H4).
Proof.
  intros.
  functional induction (mark_ptrs h ps H1 H2); intros ; clear e.
  * assert (incl ps (mark_ptr_single h ps)).
    eapply mark_ptr_single_monotonic_2. auto.
    unfold incl in H1.
    specialize (H1 p).
    intros.
    intuition.
Admitted.
 *)

Lemma mark_ptr_single_marks_address :
  forall h ps address n p p' p'',
    heap_maps h p n (Pointer p') ->
    addresses h p' address p'' ->
    set_In p ps ->
    set_In p' (mark_ptr_single h ps).
Proof.
  induction ps. crush.
  intros.
  unfold set_In in *.
  destruct H1.
  * subst.
    clear IHps.
    unfold mark_ptr_single ; fold mark_ptr_single.
    eapply nodup_In_inv.
    eapply in_flat_map_inv.
    exists p. crush.
    eapply set_add_intro1.
    unfold add_vals.
    eapply nodup_In.
    unfold heap_maps in H. unfold heap_get in H.
    edestruct heap_get_struct eqn:?. Focus 2. discriminate.
    assert (exists v, heap_get_struct p' h = Some v).
    - inversion H0. auto.
      unfold heap_maps in H1. unfold heap_get in H1.
      destruct (heap_get_struct p' h) eqn:?. eexists. eauto. discriminate.
    - clear H0.
      destruct H1.
      clear Heqo.
      specialize (nth_error_In _ _ H).
      intros.
      clear H.
      induction l. crush.
      destruct H1.
      + subst. clear IHl.
        unfold flat_map ; fold flat_map.
        rewrite H0.
        eapply in_app_iff. left. crush.
      + crush.
  * unfold mark_ptr_single ; fold mark_ptr_single.
    specialize (IHps address n p p' p'' H H0 H1).
    crush.
    eapply nodup_In_inv.
    unfold mark_ptr_single in IHps.
    specialize (nodup_In_fwd _ _ IHps); clear IHps ; intros.
    eapply in_or_app.
    right.
    auto.
Qed.

Theorem mark_ptrs_marks :
  forall address ps h p p' ND IL,
    addresses h p address p' ->
    set_In p ps ->
    set_In p' (mark_ptrs h ps ND IL)
.
Proof.
  induction address.
  * intros.
    inversion H ; subst ; clear H.
    destruct H1.
    assert (set_In p' (mark_ptr_single h ps)).
    - specialize (mark_ptr_single_monotonic_2 h ps ND).
      unfold incl.
      intros.
      specialize (H1 p' H0).
      auto.
    - eapply mark_ptrs_monotonic.
      auto.
  * intros.
    inversion H ; subst ; clear H.
    assert (set_In p'0 (mark_ptr_single h ps)).
    - clear IHaddress.
      eapply mark_ptr_single_marks_address. apply H5. apply H7. auto.
    - specialize (IHaddress (mark_ptr_single h ps) h p'0 p').

      assert (NoDup (mark_ptr_single h ps)).
      eapply mark_ptr_single_nodup. auto.

      assert (incl (mark_ptr_single h ps) (fst (split h))).
      eapply mark_ptr_single_subset_2 ; auto.

      specialize (IHaddress H1 H2 H7 H).
      eapply mark_ptrs_fixy.
      auto.
      apply IHaddress.
Qed.

Theorem mark_ptrs_correct :
  forall ps h p' ND IL,
    set_In p' (mark_ptrs h ps ND IL) ->
    exists p address,
      set_In p ps
      /\
      addresses h p address p'.
Proof.
Admitted.


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

Lemma in_split_l_tl :
  forall {A B: Type} (l: list (A * B)) (p o: A) (v: B),
    In p (fst (split l)) ->
    In p (fst (split ((o, v) :: l))).
Proof.
  induction l. crush.
  crush.
  specialize (IHl p o v).
  destruct (split l). crush.
Qed.

Lemma in_split_r_tl :
  forall {A B: Type} (l: list (A * B)) (p: B) (o: A) (v: B),
    In p (snd (split l)) ->
    In p (snd (split ((o, v) :: l))).
Proof.
  induction l. crush.
  crush.
  specialize (IHl p o v).
  destruct (split l). crush.
Qed.

Lemma heap_get_in_split :
  forall h p l,
    heap_get_struct p h = Some l ->
    set_In p (fst (split h)).
Proof.
  induction h ; intros.
  * inversion H.
  * destruct a.
    inversion H. clear H.
    destruct (ptr_eq_dec p0 p).
  - injection H1. intros. subst. clear H1.
    assert (In (p, l) ((p, l) :: h)). crush.
    specialize (in_split_l _ _ H).
    crush.
  - unfold heap_maps_struct in * ; fold heap_maps_struct in *.
    unfold heap_get_struct in * ; fold heap_get_struct in *.
    specialize (IHh p l).
    intuition.
    eapply in_split_l_tl. auto.
Qed.

Theorem mark_monotonic_1 :
  forall r v p p' h,
    set_In p (mark r h) ->
    set_In p (mark ((v, p')::r) h).
Proof.
  induction r. crush.
  intros.
  destruct a.
  unfold mark.
Admitted.

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
    assert (NoDup (nodup ptr_eq_dec
                         (set_inter ptr_eq_dec (snd (split ((v, p) :: r))) (fst (split h))))). eapply NoDup_nodup.
    assert (incl
              (nodup ptr_eq_dec
                     (set_inter ptr_eq_dec (snd (split ((v, p) :: r))) (fst (split h))))
              (fst (split h))).
    unfold incl. intros.
    specialize (nodup_In_fwd _ _ H1) ; clear H1 ; intros.
    eapply set_inter_elim2. apply H1.

    specialize (mark_ptrs_marks address (nodup ptr_eq_dec
          (set_inter ptr_eq_dec (snd (split ((v, p) :: r))) (fst (split h)))) h p p' H H1 H0).
    intros.
    assert ((mark_obligation_1 ((v, p) :: r) h) = H).
    eapply proof_irrelevance. rewrite H3. clear H3.
    assert ((mark_obligation_2 ((v, p) :: r) h) = H1).
    eapply proof_irrelevance. rewrite H3. clear H3.
    eapply H2. clear H2.
    eapply nodup_In_inv.
    eapply set_inter_intro.
    + assert (In (v, p) ((v, p) :: r)). crush.
      specialize (in_split_r _ _ H2).
      crush.
    + inversion H0.
      ** subst.
         destruct H2.
         unfold heap_maps_struct in H2.
         eapply heap_get_in_split. apply H2.
      ** subst.
         unfold heap_maps in H2.
         unfold heap_get in H2.
         destruct (heap_get_struct p h) eqn:?. Focus 2. crush.
         eapply heap_get_in_split. apply Heqo.
  - intuition.

    assert (forall x y : var * ptr, {x = y} + {x <> y}). decide equality. eapply ptr_eq_dec. eapply var_eq_dec.
    crush.
    + destruct (In_dec H2 (v,p) r).
      ** unfold mark.
         admit.
      ** admit.
    + admit.
      (*apply set_union_iff.
      crush.
    + apply set_union_iff.
      crush.*)
Admitted.

(*
Theorem mark_ptrs_marks :
  forall address ps h p p' ND IL,
    addresses h p address p' ->
    set_In p ps ->
    set_In p' (mark_ptrs h ps ND IL)
.
*)


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
Admitted.
(*
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
*)

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