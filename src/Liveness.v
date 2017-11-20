Require Import Gc.Language Gc.Gc.
Require Import List ListSet CpdtTactics.

Lemma mark_liveness_1 :
  forall st p vs,
    set_In p (mark (fuel st) (roots st) (heap st)) ->
    heap_maps_struct (heap st) p vs ->
    exists address v p',
      roots_maps (roots st) v p'
      /\
      addresses (heap st) p' address p
.
Proof.
  Hint Unfold heap_maps_struct heap_get_struct.
  intro st.
  remember (fuel st) as fuel.
  induction fuel; intros.
  * unfold mark in H.
    remember (roots st) as roots.
    induction roots in H.
    + intuition.
    + fold mark in *. 
      unfold mark_ptr in H.
      destruct a in H.
      unfold set_union in H.
      intuition.
  *
Admitted.

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

(* This only works since pointer values don't change *)
Lemma liveness_1_helper :
  forall st p vs h,
    (gc (fuel st) (roots st) (heap st)) = h ->
    heap_maps_struct h p vs ->
    exists address v p',
      roots_maps (roots st) v p'
      /\
      addresses (heap st) p' address p
.
Proof.
  intros.
  unfold gc in H.
  apply (sweep_actually_sweeps (heap st) h (mark (fuel st) (roots st) (heap st)) p vs) in H.
  * destruct H.
    eapply (mark_liveness_1).
    + apply H.
    + apply H1.
  * intuition.
Qed.

(* This only works since pointer values don't change *)
Lemma paths_maintained:
  forall st address p p' h,
    addresses (heap st) p' address p -> 
    (gc (fuel st) (roots st) (heap st)) = h ->
    addresses h p' address p
.
Proof.
Admitted.

Theorem liveness_1 :
  forall st p vs h,
    (gc (fuel st) (roots st) (heap st)) = h ->
    heap_maps_struct h p vs ->
    exists address v p',
      roots_maps (roots st) v p'
      /\
      addresses h p' address p
.
Proof.
  intros.
  remember H as temp. clear Heqtemp.
  apply (liveness_1_helper st p vs h) in temp.
  * destruct temp as [a [v  [p' [H1 H2]]]].
    eapply paths_maintained in H2; eauto.
  * auto.
Qed.