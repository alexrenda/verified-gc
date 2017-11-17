Require Import Gc.Language Gc.Gc.


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
Admitted.