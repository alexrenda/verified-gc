Require Import Gc.Language Gc.Gc Gc.Safety.
Require Import Equality CpdtTactics.


Lemma roots_maps_get :
  forall r v p,
    roots_maps r v p ->
    roots_get v r = Some p.
Proof.
Admitted.

Lemma roots_get_maps :
  forall r v p,
    roots_get v r = Some p ->
    roots_maps r v p.
Proof.
Admitted.

Lemma roots_maps_uniq :
  forall r v p p',
    roots_maps r v p ->
    roots_maps r v p' ->
    p = p'.
Proof.
Admitted.

Lemma roots_unset_1 :
  forall r v p,
    roots_maps (roots_unset r v) v p ->
    False.
Proof.
Admitted.

Lemma roots_unset_2 :
  forall r v v' p,
    v' <> v ->
    roots_maps r v p ->
    roots_maps (roots_unset r v') v p.
Proof.
Admitted.

Lemma roots_unset_3 :
  forall r v v' p,
    v' <> v ->
    roots_maps (roots_unset r v') v p ->
    roots_maps r v p.
Proof.
Admitted.

Lemma roots_set_1 :
  forall r v p p1,
    roots_maps (roots_set r v p) v p1 ->
    p = p1.
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
    specialize (H1 v p TermStr p n0 n) ;
    assert (roots_maps (roots s1) v p) ;
    try (eapply roots_get_maps) ;
    eauto ;
    assert (addresses (heap s1) p TermStr p) ;
    try (constructor ;
         unfold heap_get in H0 ;
         edestruct heap_get_struct eqn:? ;
         try discriminate ;
         exists l;
         auto
        );
    intuition;
    destructo.
  * inversion H5. subst.
    specialize (roots_get_maps _ _ _ Heqo0). intros.
    assert (p0 = x0). eapply roots_maps_uniq ; eauto.
    subst.
    auto.
  * specialize (roots_maps_get _ _ _ H1).
    intros.
    crush.
Qed.

Theorem equiv_class_step_1 :
  forall s1 s2 c s1',
    handle_small_step s1 c = Some s1' ->
    equiv s1 s2 ->
    exists s2',
      handle_small_step s2 c = Some s2'.
Proof.
Admitted.

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
  * admit.
  * admit.
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
    - specialize (roots_set_1 _ _ _ _ H2).
      intros.
      subst.
      exists p0.
      destruct v0. crush.
      unfold equiv' in H0.
      specialize (H0 v p1 address p1' k i).
      admit.
    - admit.
    - admit.
    - admit.
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
        specialize (H4 v0 p1 address p1' k i).
        intuition.
        destructo.
        exists x, x0.
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
        specialize (H5 v0 p1 address p1' k i).
        intuition.
        destructo.
        exists x, x0.
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