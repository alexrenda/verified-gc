Require Import Gc.Language Gc.Gc.
Require Import List ListSet CpdtTactics PeanoNat.

Lemma mark_liveness_1 :
  forall st p vs,
    set_In p (mark (fuel st) (roots st) (heap st)) ->
    heap_maps_struct (heap st) p vs ->
    exists address v p' p'',
      roots_maps (roots st) v p'
      /\
      addresses (heap st) p' address p''
      /\
      heap_maps_struct (heap st) p'' vs
.
Proof.
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
    unfold heap_maps_struct in H0.
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

Theorem liveness_1 :
  forall st p vs,
    heap_maps_struct (gc (fuel st) (roots st) (heap st)) p vs ->
    exists address v p' p'',
      roots_maps (roots st) v p'
      /\
      addresses (heap st) p' address p''
      /\
      heap_maps_struct (heap st) p'' vs
.
Proof.
  intros.
  unfold gc in H.
  remember (sweep (heap st) (mark (fuel st) (roots st) (heap st))) as h'.
  apply (sweep_actually_sweeps (heap st) h' (mark (fuel st) (roots st) (heap st)) p vs) in H.
  * destruct H.
    eapply (mark_liveness_1).
    + apply H.
    + apply H0.
  * intuition.
Qed.