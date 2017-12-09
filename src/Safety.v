Require Import Gc.Language Gc.Gc.

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
Admitted.
