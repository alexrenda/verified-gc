Require Import Gc.Language Gc.Gc Gc.Safety.
Require Import Equality CpdtTactics.

Lemma heap_sets_implies_exists_heap_maps_struct :
  forall h h' p k v,
    heap_set_k h p k v = Some h' ->
    exists vs, heap_maps_struct h p vs.
Proof.
Admitted.

Lemma heap_set_fails_implies_no_exists_heap_maps_struct :
  forall h p k v,
    heap_set_k h p k v = None ->
    ~exists vs, heap_maps_struct h p vs.
Proof.
Admitted.

Lemma heap_sets_implies_heap_maps_1 :
  forall h h' p k v,
    heap_set_k h p k v = Some h' ->
    heap_maps h' p k v.
Proof.
Admitted.

Lemma heap_sets_implies_heap_maps_2 :
  forall h h' p p' k k' v v',
    heap_set_k h p k v = Some h' ->
    (p <> p' \/ k <> k') ->
    heap_maps h  p' k' v' ->
    heap_maps h' p' k' v'.
Proof.
Admitted.

Lemma heap_sets_implies_heap_maps_3 :
  forall h h' p p' k k' v v',
    heap_set_k h p k v = Some h' ->
    (p <> p' \/ k <> k') ->
    heap_maps h' p' k' v' ->
    heap_maps h  p' k' v'.
Proof.
Admitted.

Lemma eval_valexp_safety_int :
  forall s1 s2 v n,
    equiv s1 s2 ->
    eval_valexp (roots s1) (heap s1) v = Some (Int n) ->
    eval_valexp (roots s2) (heap s2) v = Some (Int n).
Proof.
  intros.
  unfold eval_valexp in *.
  destruct v. crush.
  unfold equiv in H.
  destructo.
  unfold equiv' in H1.

  destruct (roots_get v (roots s1)) eqn:? ;
    destruct (roots_get v (roots s2)) eqn:? ;
    try discriminate ;
    unfold heap_get in H0 ;
    destruct (heap_get_struct p (heap s1)) eqn:? ;
    try discriminate ;
    specialize (H1 v p TermStr p l) ;
    assert (roots_maps (roots s1) v p) ;
    try (eapply roots_get_maps) ;
    eauto ;
    assert (addresses (heap s1) p TermStr p) ;
    try (constructor ;
         exists l;
         auto
        );
    intuition;
    destructo.
  * inversion H5. subst.
    specialize (roots_get_maps _ _ _ Heqo0). intros.
    assert (p0 = x0). eapply roots_maps_uniq ; eauto.
    subst.
    destructo.
    assert (List.nth_error x1 n0 = Some (Int n)).
    unfold struct_equiv in H7.
    destructo.
    specialize (H10 n0 n).
    destructo.
    intuition.

    unfold heap_get.
    rewrite H6.
    auto.
  * specialize (roots_maps_get _ _ _ H1).
    intros.
    crush.
Qed.

Lemma eval_valexp_safety_any :
  forall s1 s2 v val1,
    equiv s1 s2 ->
    eval_valexp (roots s1) (heap s1) v = Some val1 ->
    exists val2, eval_valexp (roots s2) (heap s2) v = Some val2.
Proof.
  intros.
  destruct H. destructo.
  unfold eval_valexp in *.
  destruct v.
  eauto.
  destruct (roots_get v (roots s1)) eqn:?.
  Focus 2. discriminate.
  destruct (roots_get v (roots s2)) eqn:?.
  * destruct (heap_get p0 n (heap s2)) eqn:?.
    eauto.
    unfold heap_get in H0.
    destruct (heap_get_struct p (heap s1)) eqn:?.
    Focus 2. discriminate.
    specialize (H1 v p TermStr p l).

    specialize (roots_get_maps _ _ _ Heqo). intros.
    assert (addresses (heap s1) p TermStr p). constructor ; eauto.
    assert (heap_maps_struct (heap s1) p l). eauto.

    intuition.
    destructo.
    specialize (roots_get_maps _ _ _ Heqo0). intros.
    specialize (roots_maps_uniq _ _ _ _ H1 H9). intros. subst.
    inversion H6. subst.
    destructo.
    unfold heap_get in Heqo1.
    rewrite H7 in Heqo1.
    unfold struct_equiv in H8. destructo.
    assert (length x1 <> length l).
    specialize (List.nth_error_None x1 n).
    specialize (List.nth_error_Some l n).
    intros.
    destructo.
    intuition.
    assert (List.nth_error l n = None -> False). intros.
    rewrite H14 in H0. discriminate.
    intuition.
    crush.
  * unfold heap_get in H0.
    destruct (heap_get_struct p (heap s1)) eqn:?.
    Focus 2. discriminate.
    specialize (H1 v p TermStr p l).

    specialize (roots_get_maps _ _ _ Heqo). intros.
    assert (addresses (heap s1) p TermStr p). constructor ; eauto.
    assert (heap_maps_struct (heap s1) p l). eauto.

    intuition.
    destructo.
    specialize (roots_maps_get _ _ _ H1).
    intros.
    crush.
Qed.

Lemma option_eval_safe :
  forall s1 s2 v val1,
    equiv s1 s2 ->
    option_eval (roots s1) (heap s1) v = Some val1 ->
    exists val2, option_eval (roots s2) (heap s2) v = Some val2.
Proof.
  induction v. eauto.
  intros.
  unfold option_eval in * ; fold option_eval in *.
  destruct (eval_valexp (roots s1) (heap s1) a) eqn:?.
  Focus 2. discriminate.
  destruct (option_eval (roots s1) (heap s1) v) eqn:?.
  Focus 2. discriminate.
  crush.
  specialize (IHv l H).
  intuition.
  destructo.
  rewrite H0.
  destruct (eval_valexp (roots s2) (heap s2) a) eqn:?.
  eauto.
  specialize (eval_valexp_safety_any _ _ _ _ H Heqo).
  crush.
Qed.

Theorem equiv_class_step_1 :
  forall s1 s2 c s1',
    handle_small_step s1 c = Some s1' ->
    equiv s1 s2 ->
    exists s2',
      handle_small_step s2 c = Some s2'.
Proof.
  intros.
  destruct c ; unfold handle_small_step in *.
  * induction l. crush. eauto.
    unfold option_eval in * ; fold option_eval in *.
    destruct (eval_valexp (roots s1) (heap s1) a) eqn:?.
    Focus 2. discriminate.
    destruct (eval_valexp (roots s2) (heap s2) a) eqn:?.
    Focus 2. specialize (eval_valexp_safety_any _ _ _ _ H0 Heqo). intros.
    destructo. crush.
    destruct (option_eval (roots s1) (heap s1) l) eqn:?.
    Focus 2. discriminate.
    specialize (option_eval_safe _ _ _ _ H0 Heqo1).
    intros.
    destructo.
    rewrite H1.
    eauto.
  * destruct (eval_valexp (roots s1) (heap s1) v0) eqn:?.
    Focus 2. discriminate.
    specialize (eval_valexp_safety_any _ _ _ _ H0 Heqo).
    intros.
    destructo.
    rewrite H1.
    edestruct (update_heap (roots s2) (heap s2) v n x) eqn:?.
    eauto.
    unfold update_heap in Heqo0.
    destruct (roots_get v (roots s2)) eqn:?.
    - destruct (heap_set_k (heap s2) p n x) eqn:?. discriminate.
      clear Heqo0.
      destruct (update_heap (roots s1) (heap s1) v n v1) eqn:?.
      Focus 2. discriminate.
      subst.
      unfold update_heap in Heqo0.
      destruct (roots_get v (roots s1)) eqn:?.
      Focus 2. discriminate.
      destruct (heap_set_k (heap s1) p0 n v1) eqn:?.
      Focus 2. discriminate.
      crush.

      destruct H0.
      destructo.
      specialize (heap_sets_implies_exists_heap_maps_struct _ _ _ _ _ Heqo4).
      intros.
      destructo.
      specialize (H0 v p0 TermStr p0 x0).

      assert (roots_maps (roots s1) v p0). eapply roots_get_maps. auto.
      assert (addresses (heap s1) p0 TermStr p0). constructor. eauto.

      intuition.
      destructo.
      assert (p = x1).
      specialize (roots_get_maps _ _ _ Heqo1). intros.
      specialize (roots_maps_uniq _ _ _ _ H9 H0). auto.
      subst.
      inversion H6. subst.
      destructo.
      specialize (heap_set_fails_implies_no_exists_heap_maps_struct _ _ _ _ Heqo2).
      intros.
      contradiction H10.
      exists x3. auto.
    - contradict Heqo1. unfold not. intros.
      clear Heqo0.
      destruct (update_heap (roots s1) (heap s1) v n v1) eqn:?.
      Focus 2. discriminate.
      unfold update_heap in Heqo0.
      destruct (roots_get v (roots s1)) eqn:?.
      Focus 2. discriminate.
      destruct (heap_set_k (heap s1) p n v1) eqn:?.
      Focus 2. discriminate.
      destruct H0. destructo.
      destruct H0.
      destructo.
      crush.
      specialize (heap_sets_implies_exists_heap_maps_struct _ _ _ _ _ Heqo2).
      intros.
      destructo.
      specialize (H3 v p TermStr p x0).

      assert (roots_maps (roots s1) v p). eapply roots_get_maps. auto.
      assert (addresses (heap s1) p TermStr p). constructor. eauto.

      intuition.
      destructo.
      specialize (roots_maps_get _ _ _ H3).
      intros.
      crush.
  * destruct (eval_valexp (roots s1) (heap s1) v0) eqn:?.
    Focus 2. discriminate.
    destruct v1 eqn:?.
    discriminate.
    crush.
    destruct (eval_valexp (roots s2) (heap s2) v0) eqn:?.
    Focus 2.
    specialize (eval_valexp_safety_any _ _ _ _ H0 Heqo).
    intros. destructo. crush.

    destruct v1.
    assert (equiv s2 s1). eapply equiv_symm ; eauto.
    specialize (eval_valexp_safety_int _ _ _ _ H Heqo0).
    intros. crush.
    eauto.
  * unfold handle_small_step in *.
    eexists.
    eauto.
  * unfold handle_small_step in *.
    edestruct eval_valexp eqn:?.
    Focus 2. discriminate.
    destruct v0 eqn:?.
    Focus 2. discriminate.
    specialize (eval_valexp_safety_int _ _ _ _ H0 Heqo). intros.
    rewrite H1.
    eauto.
Qed.

Lemma equiv_single_step :
  forall v1 p v0 p0 p1 s1 s2 p1' struct1 address,
  eval_valexp (roots s1) (heap s1) v0 = Some (Pointer p) ->
  eval_valexp (roots s2) (heap s2) v0 = Some (Pointer p0) ->
  equiv' s1 s2 ->
  roots_maps (roots_set (roots s1) v1 p) v1 p1 ->
  addresses (heap s1) p1 address p1' ->
  heap_maps_struct (heap s1) p1' struct1 ->
  exists (p2 p2' : ptr) (struct2 : list val),
    roots_maps (roots_set (roots s2) v1 p0) v1 p2 /\
    addresses (heap s2) p2 address p2' /\
    heap_maps_struct (heap s2) p2' struct2 /\
    struct_equiv struct1 struct2.
Proof.
  intros.
  specialize (roots_set_1 _ _ _ _ H2).
  intros.
  subst.
  destruct v0. crush.

  unfold eval_valexp in H.
  destruct (roots_get v (roots s1)) eqn:?.
  Focus 2. discriminate.

  unfold equiv' in H1.

  specialize (H1 v p (FollowStr n address) p1' struct1).
  specialize (roots_get_maps _ _ _ Heqo).
  intros.

  assert (addresses (heap s1) p (FollowStr n address) p1').
  eapply FollowAddresses.
  unfold heap_get in H.
  destruct (heap_get_struct p (heap s1)) eqn:?.
  Focus 2. discriminate.
  eapply heap_get_implies_heap_maps ; eauto.
  auto.

  intuition.
  destructo.

  exists p0.
  exists x0.
  exists x1.
  split. eapply roots_set_2.
  split.
  Focus 2. crush.
  inversion H7. subst.

  assert (p' = p0).
  unfold eval_valexp in H0.
  specialize (roots_maps_get _ _ _ H1). intros.
  unfold heap_get in H0.
  rewrite H10 in H0.
  unfold heap_maps in H14.
  unfold heap_get in H14.
  destruct (heap_get_struct x (heap s2)) eqn:?.
  Focus 2. discriminate.
  crush.
  subst.
  auto.
Qed.

Ltac apply_eval_safety :=
  match goal with
  | [H1 : eval_valexp (roots ?s1) (heap ?s1) ?v = Some (Int ?n),
         H2 : eval_valexp (roots ?s2) (heap ?s2) ?v = Some (Pointer ?p),
              H3 : equiv ?s1 ?s2 |-
     _
    ] =>
    let x := fresh "x" in
    specialize (eval_valexp_safety_int _ _ _ _ H3 H1) as x ;
    rewrite x in H2 ; discriminate
  end.

Theorem equiv_class_step_2 :
  forall s1 s2 c s1' s2',
    handle_small_step s1 c = Some s1' ->
    handle_small_step s2 c = Some s2' ->
    equiv s1 s2 ->
    equiv s1' s2'.
Proof.
  intros.
  destruct c ;
    unfold handle_small_step in *.
  * destruct H1. destructo.
    destruct (option_eval (roots s1) (heap s1) l) eqn:?.
    Focus 2. discriminate.
    destruct (option_eval (roots s2) (heap s2) l) eqn:?.
    Focus 2. discriminate.
    split. crush.
    crush ; admit.
  * destruct (eval_valexp (roots s1) (heap s1) v0) eqn:?.
    Focus 2. discriminate.
    destruct (update_heap (roots s1) (heap s1) v n v1) eqn:?.
    Focus 2. discriminate.
    destruct (eval_valexp (roots s2) (heap s2) v0) eqn:?.
    Focus 2. discriminate.
    destruct (update_heap (roots s2) (heap s2) v n v2) eqn:?.
    Focus 2. discriminate.
    crush.
    unfold update_heap in *.

    destruct (roots_get v (roots s1)) eqn:?.
    Focus 2. discriminate.
    destruct (roots_get v (roots s2)) eqn:?.
    Focus 2. discriminate.
    destruct (heap_set_k (heap s1) p n v1) eqn:?.
    Focus 2. discriminate.
    destruct (heap_set_k (heap s2) p0 n v2) eqn:?.
    Focus 2. discriminate.

    crush.

    split. destruct H1. auto.

    assert (equiv s2 s1). eapply equiv_symm ; eauto.

    destruct v0 ; destruct v1 ; destruct v2 ; split ; try apply_eval_safety.
    - admit.
    - admit.
    - crush.
    - crush.
    - admit.
    - admit.
    - admit.
    - admit.
  * destruct (eval_valexp (roots s1) (heap s1) v0) eqn:?.
    Focus 2. discriminate.
    destruct v1 eqn:?. discriminate.

    destruct (eval_valexp (roots s2) (heap s2) v0) eqn:?.
    Focus 2. discriminate.
    destruct v2. discriminate.

    crush.
    split. crush. destruct H1. auto.
    destruct H1. destructo.
    split ; unfold equiv' ; intros ; crush ; destruct (var_eq_dec v v1) ; subst.
    - eapply (equiv_single_step _ _ _ _ _ _ _ _ _ _ Heqo) ; eauto.
    - specialize (roots_set_3 _ _ _ _ _ n H2).
      intros.
      specialize (H0 _ _ _ _ _ H5 H3 H4).
      destructo.
      exists x, x0, x1.
      split ; eauto.
      eapply roots_set_4 ; eauto.
    - eapply (equiv_single_step _ _ _ _ _ _ _ _ _ _ Heqo0) ; eauto.
    - specialize (roots_set_3 _ _ _ _ _ n H2).
      intros.
      specialize (H1 _ _ _ _ _ H5 H3 H4).
      destructo.
      exists x, x0, x1.
      split ; eauto.
      eapply roots_set_4 ; eauto.
  * crush.
    split. destruct H1. auto.
    split.
    - unfold equiv'.
      crush.
      destruct (var_eq_dec v v0).
      + subst.
        specialize (roots_unset_1 _ _ _ H).
        intros.
        contradiction H3.
      + specialize (roots_unset_3 _ _ _ _ n H).
        intros.
        destruct H1.
        destructo.
        unfold equiv' in H4.
        specialize (H4 v0 p1 address p1' struct1).
        intuition.
        destructo.
        exists x, x0, x1.
        split.
        eapply roots_unset_2. auto. auto.
        split ; auto.
    - unfold equiv'.
      crush.
      destruct (var_eq_dec v v0).
      + subst.
        specialize (roots_unset_1 _ _ _ H).
        intros.
        contradiction H3.
      + specialize (roots_unset_3 _ _ _ _ n H).
        intros.
        destruct H1.
        destructo.
        unfold equiv' in H5.
        specialize (H5 v0 p1 address p1' struct1).
        intuition.
        destructo.
        exists x, x0, x1.
        split.
        eapply roots_unset_2. auto. auto.
        split ; auto.
  * destruct (eval_valexp (roots s1) (heap s1) v) eqn:?.
    - destruct v0 eqn:?.
      + subst.
        specialize (eval_valexp_safety_int _ _ _ _ H1 Heqo).
        intros.
        rewrite H2 in H0.
        clear H2.
        crush.
        destruct H1.
        crush.
      + discriminate.
    - discriminate.
Admitted.


Inductive execution : state -> list com -> output_t -> Prop :=
| NilExecution : forall state,
    execution state List.nil (output state)
| GcExecution : forall state coms out,
    execution (gc state) coms out ->
    execution state coms out
| ComExecution : forall com coms state state' out,
    handle_small_step state com = Some state' ->
    execution state' coms out ->
    execution state (List.cons com coms) out
.


Theorem execution_output_exists :
  forall coms st st' out,
    execution st coms out ->
    equiv st st' ->
    exists out',
      execution st' coms out'.
Proof.
  intros until 1.
  dependent induction H generalizing st'.
  * intros.
    exists (output st').
    apply NilExecution.
  * intros.
    eapply IHexecution.
    eapply equiv_trans.
    apply equiv_symm.
    apply gc_safety.
    auto.
  * intros.
    specialize (equiv_class_step_1 _ _ _ _ H H1).
    intros.
    destructo.
    specialize (IHexecution x).
    specialize (equiv_class_step_2 _ _ _ _ _ H H2 H1).
    intros.
    intuition.
    destructo.
    exists x0.
    eapply ComExecution.
    apply H2.
    apply H4.
Qed.

Theorem execution_output_equiv :
  forall coms st st' out out',
    execution st coms out ->
    execution st' coms out' ->
    equiv st st' ->
    out = out'
.
Proof.
  intros until 1.
  dependent induction H generalizing st' out'.
  * intros.
    dependent induction H.
    - destruct H0.
      destructo.
      auto.
    - eapply IHexecution.
      reflexivity.
      eapply equiv_trans.
      apply H0.
      eapply gc_safety.
  * intros.
    intuition.
    eapply IHexecution.
    apply H0.
    eapply equiv_trans.
    apply equiv_symm.
    eapply gc_safety.
    apply H1.
  * intros.
    dependent induction H1 ; subst.
    - eapply IHexecution0 ; eauto.
      eapply equiv_trans.
      apply H2.
      eapply gc_safety.
    - eapply IHexecution ; eauto.
      eapply equiv_class_step_2 ; eauto.
Qed.