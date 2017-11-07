(** * Review of IMP semantics *)

Require Import Bool Arith String List CpdtTactics.
Open Scope string_scope.

(** IMP syntax -- any CFG -- is just an inductive definition. *)

Definition var := string.

Inductive binop := Plus | Times | Minus.

Inductive aexp : Type := 
| Const : nat -> aexp
| Var : var -> aexp
| Binop : aexp -> binop -> aexp -> aexp.

Inductive bexp : Type := 
| Tt : bexp
| Ff : bexp
| Eq : aexp -> aexp -> bexp
| Lt : aexp -> aexp -> bexp
| And : bexp -> bexp -> bexp
| Or : bexp -> bexp -> bexp
| Not : bexp -> bexp.

Inductive com : Type := 
| Skip : com
| Assign : var -> aexp -> com
| Seq : com -> com -> com
| If : bexp -> com -> com -> com
| While : bexp -> com -> com.


(** Okay, now let's start defining some semantics.
    For aexp and bexp we can directly give a denotation
    to expressions by implementing an interpreter in Coq.
    However, the meaning of these expressions depends
    on the current state, which maps variables to numbers: *)

Definition state := var -> nat.

Definition get (x:var) (s:state) : nat := s x.

Definition set (x:var) (n:nat) (s:state) : state := 
  fun y => 
    match string_dec x y with 
        | left H => n 
        | right H' => get y s
    end.

(* We map binary operator expressions to underlying Coq
   operators on nat. *)

Definition eval_binop (b:binop) : nat -> nat -> nat := 
  match b with 
    | Plus => plus
    | Times => mult
    | Minus => minus
  end.

(* The implementations of eval_aexp and eval_bexp are
   recursive translations into Coq terms. *)

Fixpoint eval_aexp (e:aexp) (s:state) : nat := 
  match e with 
    | Const n => n
    | Var x => get x s
    | Binop e1 b e2 => (eval_binop b) (eval_aexp e1 s) (eval_aexp e2 s)
  end.

Fixpoint eval_bexp (b:bexp) (s:state) : bool := 
  match b with 
    | Tt => true
    | Ff => false
    | Eq e1 e2 => Nat.eqb (eval_aexp e1 s) (eval_aexp e2 s)
    | Lt e1 e2 => Nat.ltb (eval_aexp e1 s) (eval_aexp e2 s)
    | And b1 b2 => eval_bexp b1 s && eval_bexp b2 s
    | Or b1 b2 => eval_bexp b1 s || eval_bexp b2 s
    | Not b => negb (eval_bexp b s)
  end.

(** We can define notation if we feel like seeing semantic
    brackets in our proofs:
*)

Notation "⟦ A ⟧" := (eval_aexp A).
Notation "⟦ B ⟧" := (eval_bexp B).
Print eval_aexp.

Compute (eval_aexp (Binop (Const 17) Plus (Var "x")) (fun _ => 25)).

(** What goes wrong when we try to give a semantics to
    commands in the same way?
 
Fixpoint eval_com (c:com) (s: state) : state :=
  match c with
    | Skip => s
    | Assign v a => set v (eval_aexp a s) s
    | Seq c1 c2 =>
        eval_com c2 (eval_com c1 s)
    | If b c1 c2 =>
        match eval_bexp b s with
          | true => eval_com c1 s
          | false => eval_com c2 s
        end
    | While b c =>
        match eval_bexp b s with
          | false => s
          | true => eval_com (While b c) s
        end
  end.
*)

(** The computational/denotational approach to the semantics
    is hopeless, even if we make eval_com
    partial, because IMP is Turing-complete. We can't decide
    whether a program terminatse, in general. Instead, we
    can define a (big-step) semantics as a _relation_.

    The elements of eval_com are the big-step proof trees
    for the elements of that relation. This is an inductive
    definition on the structure of the proof trees.
*)
Inductive eval_com : com -> state -> state -> Prop := 
| Eval_skip : forall s, eval_com Skip s s
| Eval_assign : forall s x e, eval_com (Assign x e) s (set x (eval_aexp e s) s)
| Eval_seq : forall c1 s0 s1 c2 s2, 
               eval_com c1 s0 s1 -> eval_com c2 s1 s2 -> eval_com (Seq c1 c2) s0 s2
| Eval_if_true : forall b c1 c2 s s',
                   eval_bexp b s = true -> 
                   eval_com c1 s s' -> eval_com (If b c1 c2) s s'
| Eval_if_false : forall b c1 c2 s s',
                   eval_bexp b s = false -> 
                   eval_com c2 s s' -> eval_com (If b c1 c2) s s'
| Eval_while_false : forall b c s, 
                       eval_bexp b s = false -> 
                       eval_com (While b c) s s
| Eval_while_true : forall b c s1 s2 s3, 
                      eval_bexp b s1 = true -> 
                      eval_com c s1 s2 -> 
                      eval_com (While b c) s2 s3 -> 
                      eval_com (While b c) s1 s3.

(** Notation "⟨ A , S ⟩ ⇓ T" := (eval_com A S T) (at level 100). *)

(* y := 1; x := 2; while 0 < x { y := y * 2; x := x - 1 } *)
Definition prog1 := 
  Seq (Assign "y" (Const 1))
  (Seq (Assign "x" (Const 2))
       (While (Lt (Const 0) (Var "x"))
              (Seq (Assign "y" (Binop (Var "y") Times (Const 2)))
                   (Assign "x" (Binop (Var "x") Minus (Const 1)))))).

Theorem four : forall s, eval_com prog1 (fun _ => 0) s ->
                4 = get "y" s.
Proof.
(** We can use the semantics to prove the results of evaluation.
    But it's quite tedious. Looks ripe for automation! *)
  intros.
  unfold prog1 in H.
  inversion H; clear H; subst.
  inversion H2; clear H2; subst.
  unfold get, eval_aexp in *. simpl.
  inversion H5; clear H5; subst.
  inversion H1; clear H1; subst.
  inversion H4; clear H4; subst.
  - unfold eval_bexp, eval_aexp, get in *.  (* false *)
    unfold set in H3. simpl in H3.
    discriminate.
  - clear H1. (* true *)
    inversion H2; clear H2; subst.
    inversion H1; clear H1; subst.
    unfold eval_bexp, eval_aexp, get, eval_binop in *.
    inversion H5; clear H5; subst.
    inversion H6; clear H6; subst.
    + unfold eval_bexp, eval_aexp, get in *. simpl in *.
      unfold set, get in *. simpl in *.
      discriminate.
    + clear H1.
      inversion H2; clear H2; subst.
      inversion H1; clear H1; subst.
      inversion H6; clear H6; subst.
      repeat unfold get, eval_aexp, eval_binop in H5.
      inversion H5; clear H5; subst.
      * repeat unfold get, eval_aexp, eval_bexp in H3. subst.
        repeat unfold get, set in *. simpl in *. reflexivity.
      * clear H2 H6.
        repeat unfold set, get, eval_aexp, eval_bexp in *.
        simpl in *. discriminate.
Qed.

(** The relational approach also has the advantage that it
   can express nondeterministic semantics, e.g. a "havoc"
   command that arbitrarily changes the state. *)

(** Another option for semantics: _small-step_ *)

Inductive step_com : com -> state -> com -> state -> Prop := 
| Step_assign: forall s x e,
       step_com (Assign x e) s
                (Skip) (set x (eval_aexp e s) s)
| Step_seqL: forall c1 c2 c1' s s', step_com c1 s c1' s' ->
                step_com (Seq c1 c2) s (Seq c1' c2) s
| Step_seqR: forall c s, step_com (Seq Skip c) s c s
| Step_if_true:  forall b c1 c2 s, eval_bexp b s = true ->
                 step_com (If b c1 c2) s c1 s
| Step_if_false: forall b c1 c2 s, eval_bexp b s = false ->
                 step_com (If b c1 c2) s c2 s
| Step_while: forall b c s,
                 step_com (While b c) s
                          (If b (Seq c (While b c)) Skip) s.

Inductive steps_com : com -> state -> com -> state -> Prop :=
| No_step : forall c s, steps_com c s c s
| One_step : forall c s c' s' c'' s'', step_com c s c' s' ->
                steps_com c' s' c'' s'' -> steps_com c s c'' s''.

(** Finally, we would hope that the semantics agree
    with each other. We'll just state it for now! *)
Theorem big_small_agree :
   forall c s s', 
     eval_com c s s' <-> steps_com c s Skip s'.
Admitted.