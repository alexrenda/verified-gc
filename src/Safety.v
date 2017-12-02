Require Import Gc.Language Gc.Gc.

Theorem safety_1 :
  forall c s s' s'',
  small_step c s = Some s' ->
  small_step c (gc s) = Some s''.
Proof.
  intros.
  destruct c ; unfold small_step in * ; crush.
  * unfold small_step in H.
Qed.


Inductive execution : state -> list com -> output_t -> Prop :=
| NilExecution : forall state,
    execution state List.nil (output state)
| GcExecution : forall state coms out,
    execution (mkState (roots state) (gc (roots state) (heap state)) (output state)) coms out ->
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
