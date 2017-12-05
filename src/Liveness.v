Require Import Gc.Language Gc.Gc.
Require Import List ListSet CpdtTactics Equality Wf Nat Wf_nat.

Lemma subset_property: forall st v p p0 roots,
  (exists address v0 p', roots_maps (roots) v0 p' /\ addresses (heap st) p' address p0) ->
  (exists address v0 p', roots_maps ((v, p) :: roots) v0 p' /\ addresses (heap st) p' address p0)
.
Proof.
  intros.
  destruct H as [a [v0 [p' H]]].
  exists a.
  exists v0.
  exists p'.
  unfold roots_maps.
  crush.
Qed.


Lemma mark_liveness_1 :
  forall r h p vs,
    set_In p (mark r h) ->
    heap_maps_struct h p vs ->
    exists address p' v,
      roots_maps r v p'
      /\
      addresses h p' address p
.
Proof.
  Hint Unfold heap_maps_struct heap_get_struct roots_maps.
  Hint Resolve subset_property.
  Hint Constructors addresses.
  induction r. crush.
  intros.
  specialize (IHr h p vs).

  unfold mark in H ; fold mark in H.
  destruct a.
  destruct (ptr_eq_dec p p0).
  * subst.
    clear IHr.
    exists TermStr.
    exists p0. exists v.
    split. crush.
    eauto.
  * specialize (mark_ptrs_correct
                  (nodup ptr_eq_dec
                         (set_inter ptr_eq_dec (snd (split ((v, p0) :: r))) (fst (split h)))) h p (Gc.mark_obligation_1 ((v, p0) :: r) h) (Gc.mark_obligation_2 ((v, p0) :: r) h)).
    intros.
    intuition.
    destruct H2. destruct H1. destruct H1.
    exists x0. exists x.
    unfold roots_maps.
    specialize (nodup_In_fwd _ _ H1). clear H1. intros.
    specialize (set_inter_elim1 _ _ _ _ H1). clear H1. intros.
    apply in_split_exists_fst in H1.
    - destruct H1. exists x1. crush.
    - apply ptr_eq_dec.
Qed.

Lemma not_in_set_neq :
  forall {A: Type} (p p': A) ptrs,
    set_In p ptrs ->
    ~ (set_In p' ptrs) ->
    p <> p'
.
Proof.
  crush.
Qed.

Lemma sweep_actually_sweeps :
  forall h h' ptrs p vs,
    sweep h ptrs = h' ->
    heap_maps_struct h' p vs ->
    set_In p ptrs /\ heap_maps_struct h p vs
.
Proof.
  Hint Unfold heap_maps_struct heap_get_struct sweep.
  induction h; intros.
  * simpl in *.
    repeat autounfold in *.
    crush.
  * simpl in *.
    destruct a.
    destruct (set_mem ptr_eq_dec p0 ptrs) eqn:?.
    + intuition.
      - eapply set_mem_correct1 in Heqb.
        remember (ptr_eq_dec p p0).
        inversion s; subst; auto.
        unfold heap_maps_struct in H0.
        unfold heap_get_struct in H0.
        fold heap_get_struct in H0.
        edestruct ptr_eq_dec; intuition.
        eapply IHh; intuition.
        apply H0.
      - unfold heap_maps_struct.
        unfold heap_get_struct.
        fold heap_get_struct.
        edestruct ptr_eq_dec.
        ** subst.
           unfold heap_maps_struct in H0.
           unfold heap_get_struct in H0.
           fold heap_get_struct in H0.
           edestruct ptr_eq_dec in H0; intuition.
        ** subst.
           unfold heap_maps_struct in H0.
           unfold heap_get_struct in H0.
           fold heap_get_struct in H0.
           edestruct ptr_eq_dec; intuition.
           eapply (IHh (sweep h ptrs) ptrs p vs); intuition.
    + intuition.
      - apply (IHh h' ptrs p vs); intuition.
      - eapply set_mem_complete1 in Heqb.
        eapply (not_in_set_neq p p0 ptrs) in Heqb.
        ** unfold heap_maps_struct.
           unfold heap_get_struct.
           fold heap_get_struct.
           edestruct ptr_eq_dec; intuition.
           apply (IHh h' ptrs p vs); intuition.
        ** apply (IHh h' ptrs p vs); intuition.
Qed.

Lemma mark_sweep_liveness_1 :
  forall st p vs h,
    sweep (heap st) (mark (roots st) (heap st)) = h ->
    heap_maps_struct h p vs ->
    exists address v p',
      roots_maps (roots st) v p'
      /\
      addresses (heap st) p' address p
.
Proof.
  intros.
  apply (sweep_actually_sweeps (heap st) h (mark (roots st) (heap st)) p vs) in H.
  * destruct H.
    eapply (mark_liveness_1).
    + apply H.
    + apply H1.
  * intuition.
Qed.

Theorem liveness_1 :
  forall st p vs h,
    (gc (roots st) (heap st)) = h ->
    heap_maps_struct h p vs ->
    exists address v p',
      roots_maps (roots st) v p'
      /\
      addresses h p' address p
.
Proof.
  intros.
  pose H as temp.
  apply (mark_sweep_liveness_1 st p vs h) in temp.
  * destruct temp as [a [v  [p' [H1 H2]]]].
    eapply pointer_equivalence in H2; eauto.
    exists a, v, p'.
    crush.
  * auto.
Qed.