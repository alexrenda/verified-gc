Require Import String.

Definition named_loc := string.
Definition named_int := string.

Definition location := nat.
Definition integer := nat.

Inductive int : Type :=
| LiteralInt : integer -> int
| NamedInt : named_int -> int
.

Inductive com : Type :=
| NewCom : named_loc -> int -> com
| AssignIntCom : named_loc -> int -> com
| AssignPtrCom : named_loc -> named_loc -> com
| PrintCom : int -> com
| DerefCom : named_loc -> named_int -> named_loc -> com
| DropCom : named_loc -> com
.

Definition trace_t := list integer.

Definition set_trace (t: trace_t) (i: integer) : trace_t := cons i t.

Section Interp.
  Variable heap_t : Type.

  Variable next_loc : heap_t -> location.
  Variable heap_get : heap_t -> location -> option (location + integer).
  Variable heap_set_l : heap_t -> location -> location -> heap_t.
  Variable heap_set_r : heap_t -> location -> integer -> heap_t.

  Variable named_loc_stack_t : Type.
  Variable named_loc_stack_get : named_loc_stack_t -> named_int -> option location.
  Variable named_loc_stack_set : named_loc_stack_t -> named_int -> location -> named_loc_stack_t.
  Variable named_loc_stack_remove : named_loc_stack_t -> named_int -> option named_loc_stack_t.

  Variable named_int_stack_t : Type.
  Variable named_int_stack_get : named_int_stack_t -> named_int -> option integer.
  Variable named_int_stack_set : named_int_stack_t -> named_int -> integer -> named_int_stack_t.

  Definition eval_int (i: int) (nis: named_int_stack_t) : option integer :=
    match i with
    | LiteralInt n => Some n
    | NamedInt n => named_int_stack_get nis n
    end.

  Fixpoint interp (cs: list com) (nls: named_loc_stack_t) (nis: named_int_stack_t) (h: heap_t) (t: trace_t)
    : option (heap_t * trace_t)
    :=
      match cs with
      | nil => Some (h, t)
      | (cons c c_rest) =>
        match c with
        | NewCom x n =>
          let x_loc := next_loc h in
          match eval_int n nis with
          | None => None
          | Some i =>
            let h' := heap_set_r h x_loc i in
            let nls' := named_loc_stack_set nls x x_loc in
            interp c_rest nls' nis h' t
          end
        | AssignIntCom x n =>
          match named_loc_stack_get nls x, eval_int n nis with
          | Some x_loc, Some i =>
            let h' := heap_set_r h x_loc i in
            interp c_rest nls nis h' t
          | _, _ => None
          end
        | AssignPtrCom x y =>
          match named_loc_stack_get nls x, named_loc_stack_get nls y with
          | Some x_loc, Some y_loc =>
            let h' := heap_set_l h x_loc y_loc in
            interp c_rest nls nis h' t
          | _, _ => None
          end
        | PrintCom n =>
          match eval_int n nis with
          | Some i =>
            let t' := set_trace t i in
            interp c_rest nls nis h t'
          | None => None
          end
        | DerefCom x n y =>
          match named_loc_stack_get nls y with
          | None => None
          | Some y_loc =>
            match heap_get h y_loc with
            | Some (inl p) =>
              let nls' := named_loc_stack_set nls x y_loc in
              let nis' := named_int_stack_set nis n 0 in
              interp c_rest nls' nis' h t
            | Some (inr i) =>
              let nls' := named_loc_stack_set nls x 0 in
              let nis' := named_int_stack_set nis n i in
              interp c_rest nls' nis' h t
            | None => None
            end
          end
        | DropCom x =>
          match named_loc_stack_remove nls x with
          | Some nls' => interp c_rest nls' nis h t
          | None => None
          end
        end
      end.
End Interp.

Print interp.