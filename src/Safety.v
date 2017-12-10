Require Import Gc.Language Gc.Gc.

Require Import List ListSet Equality CpdtTactics.

(* All integers reachable from the same variable, address, and index. *)
Definition equiv' (s1 s2: state) : Prop :=
  forall v p1 address p1' k i,
      roots_maps (roots s1) v p1 ->
      addresses (heap s1) p1 address p1' ->
      heap_maps (heap s1) p1' k (Int i) ->
      exists p2 p2',
        roots_maps (roots s2) v p2 /\
        addresses (heap s2) p2 address p2' /\
        heap_maps (heap s2) p2' k (Int i).

Definition equiv (s1 s2: state) : Prop :=
  (output s1 = output s2) /\ equiv' s1 s2 /\ equiv' s2 s1.

Lemma equiv_refl : forall s1, equiv s1 s1.
  intros.
  unfold equiv.
  split. reflexivity.
  split ;
    unfold equiv' ;
    intros ;
    exists p1, p1';
    auto.
Qed.

Lemma equiv_symm : forall s1 s2, equiv s1 s2 -> equiv s2 s1.
  intros.
  unfold equiv in *.
  crush.
Qed.

Ltac destructo :=
  repeat match goal with
         | [H : _ /\ _ |- _] => destruct H
         | [H : exists _, _|- _] => destruct H
         end.

Lemma equiv_trans : forall s1 s2 s3, equiv s1 s2 -> equiv s2 s3 -> equiv s1 s3.
Proof.
  intros.
  unfold equiv in *.
  destructo.
  split. crush.
  clear H H0.
  split ; unfold equiv' ; intros.
  * specialize (H3 v p1 address p1' k i).
    intuition.
    destructo.
    eapply H1.
    apply H3.
    apply H6.
    apply H7.
  * specialize (H2 v p1 address p1' k i).
    intuition.
    destructo.
    eapply H4.
    apply H2.
    apply H6.
    apply H7.
Qed.

Theorem gc_forward_safety :
  forall st, equiv' st (gc st)
.
Proof.
  unfold equiv'.
  intros.
  exists p1.
  exists p1'.
  intuition.
  * subst; eapply pointer_equivalence; eauto.
  * specialize (heap_maps_implies_heap_get _ _ _ _ H1); intros.
    destruct H2; inversion H2; clear H2.
    specialize address_maps_to_value with (heap (gc st)) p1 p1' address; intros.
    assert (addresses (heap (gc st)) p1 address p1').
    - subst; eapply pointer_equivalence; eauto.
    - eapply H2 in H5.
      destruct H5.
      assert (x = x0).
      + eapply (value_equivalence (roots st) (heap st) (heap (gc st)) p1' x x0); crush.
      + destruct H6.
        eapply heap_get_implies_heap_maps; crush.
Qed.

Theorem gc_backward_safety :
  forall st, equiv' (gc st) st
.
Proof.
Admitted.

Theorem gc_safety :
  forall st, equiv st (gc st)
.
Proof.
  Hint Resolve gc_forward_safety gc_backward_safety.
  Hint Unfold equiv.
  crush.
Qed.
