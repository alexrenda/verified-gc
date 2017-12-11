Require Import Gc.Language Gc.Gc.

Require Import List ListSet Equality CpdtTactics.

Ltac destructo :=
  repeat match goal with
         | [H : _ /\ _ |- _] => destruct H
         | [H : exists _, _|- _] => destruct H
         | [H : _ <-> _ |- _] => destruct H
         end.


Definition struct_equiv (s1: list val) (s2: list val) : Prop :=
  length s1 = length s2
  /\
  forall n i,
    nth_error s1 n = Some (Int i) <-> nth_error s2 n = Some (Int i).

Lemma struct_equiv_refl : forall s1, struct_equiv s1 s1.
Proof.
  Hint Unfold struct_equiv.
  induction s1 ; crush.
Qed.
Hint Resolve struct_equiv_refl.

Lemma struct_equiv_symm : forall s1 s2, struct_equiv s1 s2 -> struct_equiv s2 s1.
Proof.
  Hint Unfold struct_equiv.
  intros.
  unfold struct_equiv in *.
  destructo.
  split. auto.
  intros.
  specialize (H0 n i).
  destructo.
  split ; auto.
Qed.
Hint Resolve struct_equiv_symm.

Lemma struct_equiv_trans : forall s1 s2 s3,
    struct_equiv s1 s2 ->
    struct_equiv s2 s3 ->
    struct_equiv s1 s3.
Proof.
  Hint Unfold struct_equiv.
  intros.
  unfold struct_equiv in *.
  destructo.
  split. crush.
  intros.
  specialize (H1 n i).
  specialize (H2 n i).
  destructo.
  split ; auto.
Qed.
Hint Resolve struct_equiv_trans.


(* All integers reachable from the same variable, address, and index. *)
Definition equiv' (s1 s2: state) : Prop :=
  forall v p1 address p1' struct1,
      roots_maps (roots s1) v p1 ->
      addresses (heap s1) p1 address p1' ->
      heap_maps_struct (heap s1) p1' struct1 ->
      exists p2 p2' struct2,
        roots_maps (roots s2) v p2 /\
        addresses (heap s2) p2 address p2' /\
        heap_maps_struct (heap s2) p2' struct2 /\
        struct_equiv struct1 struct2.

Definition equiv (s1 s2: state) : Prop :=
  (output s1 = output s2) /\ equiv' s1 s2 /\ equiv' s2 s1.

Lemma equiv_refl : forall s1, equiv s1 s1.
  intros.
  unfold equiv.
  split. reflexivity.
  split ;
    unfold equiv' ;
    intros ;
    exists p1, p1', struct1 ;
    auto.
Qed.

Lemma equiv_symm : forall s1 s2, equiv s1 s2 -> equiv s2 s1.
  intros.
  unfold equiv in *.
  crush.
Qed.

Lemma equiv_trans : forall s1 s2 s3, equiv s1 s2 -> equiv s2 s3 -> equiv s1 s3.
Proof.
  intros.
  unfold equiv in *.
  destructo.
  split. crush.
  clear H H0.
  split ; unfold equiv' ; intros.
  * specialize (H3 v p1 address p1' struct1).
    intuition.
    destructo.
    specialize (H1 v x address x0 x1).
    intuition.
    destructo.
    exists x2, x3, x4.
    eauto.
  * specialize (H2 v p1 address p1' struct1).
    intuition.
    destructo.
    specialize (H4 v x address x0 x1).
    intuition.
    destructo.
    exists x2, x3, x4.
    eauto.
Qed.

Theorem gc_forward_safety :
  forall st, equiv' st (gc st)
.
Proof.
  unfold equiv'.
  intros.
  exists p1.
  exists p1'.
  exists struct1.
  intuition.
  * subst; eapply pointer_equivalence; eauto.
  * (* specialize (heap_maps_implies_heap_get _ _ _ _ H1); intros. *)
    unfold heap_maps_struct in H1.
    specialize address_maps_to_value with (heap (gc st)) p1 p1' address; intros.
    assert (addresses (heap (gc st)) p1 address p1').
    - subst; eapply pointer_equivalence; eauto.
    - intuition.
      destructo.
      assert (heap_maps_struct (heap st) p1' struct1). auto.
      assert (struct1 = x).
      + eapply (value_equivalence (roots st) (heap st) (heap (gc st)) p1' struct1 x); crush.
      + subst.
        auto.
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
