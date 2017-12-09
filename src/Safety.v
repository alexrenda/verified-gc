Require Import Gc.Language Gc.Gc.

Require Import List ListSet Equality CpdtTactics.

(* All integers reachable from the same variable, address, and index. *)
Theorem gc_safety :
  forall st st' p p' v address k i,
    roots_maps (roots st) v p ->
    addresses (heap st) p address p' ->
    heap_maps (heap st) p' k (Int i) ->
    gc st = st' ->
    (exists p'' p''', 
      roots_maps (roots st') v p'' /\
      addresses (heap st') p'' address p''' /\
      heap_maps (heap st') p''' k (Int i)
    )
.
Proof.
  Hint Resolve value_equivalence.
  intros.
  exists p.
  exists p'.
  intuition.
  * crush.
  * subst; eapply pointer_equivalence; eauto.
  * specialize (heap_maps_implies_heap_get _ _ _ _ H1); intros.
    destruct H3; inversion H3; clear H3.
    specialize address_maps_to_value with (heap st') p p' address; intros.
    assert (addresses (heap st') p address p').
    - subst; eapply pointer_equivalence; eauto.
    - eapply H3 in H6.
      destruct H6.
      assert (x = x0).
      + eapply (value_equivalence (roots st) (heap st) (heap st') p' x x0); crush.
      + destruct H7.
        eapply heap_get_implies_heap_maps; crush.
Qed.
