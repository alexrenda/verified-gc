Require Import Gc.Language Gc.Gc.
Require Import Equality CpdtTactics.

(*
Theorem no_extra_crashs :
  forall c s s',
  small_step c s s' ->
  exists s'', small_step c (gc s) s''.
Proof.
(*  intros.
  destruct c ; unfold small_step in * ; crush.
  * unfold small_step in H.
*)
Admitted.


Inductive execution : state -> list com -> output_t -> Prop :=
| NilExecution : forall state,
    execution state List.nil (output state)
| GcExecution : forall state coms out,
    execution (gc state) coms out ->
    execution state coms out
| ComExecution : forall com coms state state' out,
    small_step com state state' ->
    execution state' coms out ->
    execution state (List.cons com coms) out
.

Theorem execution_output :
  forall st com out out',
    execution st com out ->
    execution st com out' ->
    out = out'
.
Proof.
Admitted.
*)