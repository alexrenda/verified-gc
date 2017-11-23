Require Import Gc.Language Gc.Gc.


Inductive execution : state -> list com -> output_t -> Prop :=
| NilExecution : forall state,
    execution state List.nil (output state)
| GcExecution : forall state coms out,
    execution (mkState (roots state) (gc (fuel state) (roots state) (heap state)) (output state) (fuel state)) coms out ->
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