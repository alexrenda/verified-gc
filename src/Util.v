Require Import Arith List ListSet Equality CpdtTactics.

(* Lemmas about split *)
Ltac split_solver l := subst; simpl; destruct (split l) eqn:?; crush.

Lemma in_split_l_ht :
  forall {A B: Type} (l: list (A * B)) p a b (eq_dec: forall n m : A, {n = m} + {n <> m}),
    In p (fst (split l)) \/ p = a <->
    In p (fst (split ((a, b) :: l))).
Proof.
  intros.
  intuition.
  * split_solver l.
  * split_solver l.
  * destruct (eq_dec p a).
    - split_solver l.
    - destruct (split l) eqn:?.
      simpl in H.
      rewrite Heqp0 in H.
      crush.
Qed.

Lemma in_split_r_ht :
  forall {A B: Type} (l: list (A * B)) p a b (eq_dec: forall n m : B, {n = m} + {n <> m}),
    In p (snd (split l)) \/ p = b <->
    In p (snd (split ((a, b) :: l))).
Proof.
  intros.
  intuition.
  * split_solver l.
  * split_solver l.
  * destruct (eq_dec p b).
    - split_solver l.
    - destruct (split l) eqn:?.
      simpl in H.
      rewrite Heqp0 in H.
      crush.
Qed.

Lemma in_split_exists_l :
  forall {A B: Type} (l: list (A * B)) (p: A) (eq_dec: forall n m : A, {n = m} + {n <> m}),
    In p (fst (split l)) ->
    exists v, In (p, v) l.
Proof.
  induction l; intros.
  * intuition.
  * destruct a.
    destruct (eq_dec p a).
    - exists b. crush.
    - assert (exists b : B, In (p, b) l).
      + apply IHl. intuition.
        destruct (split l) eqn:?.
        unfold snd in *.
        simpl in H.
        rewrite Heqp0 in H.
        crush.
      + destruct H0.
        exists x.
        crush.
Qed.

Lemma in_split_exists_r :
  forall {A B: Type} (l: list (A * B)) (p: B) (eq_dec: forall n m : B, {n = m} + {n <> m}),
    In p (snd (split l)) ->
    exists v, In (v, p) l.
Proof.
  induction l; intros.
  * intuition.
  * destruct a.
    destruct (eq_dec p b).
    - exists a. crush.
    - assert (exists v : A, In (v, p) l).
      + apply IHl. intuition.
        destruct (split l) eqn:?.
        unfold snd in *.
        simpl in H.
        rewrite Heqp0 in H.
        crush.
      + destruct H0.
        exists x.
        crush.
Qed.

(* Helper lemmas for proofs about lists *)
Lemma nodup_In_fwd :
  forall {A: Type} (p: A) l eq_dec,
    In p (nodup eq_dec l) ->
    In p l.
Proof.
  intros.
  eapply nodup_In.
  apply H.
Qed.

Lemma nodup_In_inv :
  forall {A: Type} (p: A) l eq_dec,
    In p l ->
    In p (nodup eq_dec l).
Proof.
  intros.
  eapply nodup_In.
  apply H.
Qed.

Lemma in_flat_map_fwd : forall {A B: Type} (f:A->set B)(l:list A) y,
    In y (flat_map f l) ->
    exists x, In x l /\ In y (f x).
Proof.
  eapply in_flat_map.
Qed.

Lemma in_flat_map_inv : forall {A B: Type} (f:A->set B)(l:list A) y,
    (exists x, In x l /\ In y (f x)) ->
    In y (flat_map f l).

Proof.
  eapply in_flat_map.
Qed.

(* Lemmas about sets *)
Lemma not_in_set_neq :
  forall {A: Type} (p p': A) ptrs,
    set_In p ptrs ->
    ~ (set_In p' ptrs) ->
    p <> p'
.
Proof.
  crush.
Qed.

Lemma set_add_noop :
  forall {A: Type} (a: A) l eq_dec,
    set_In a l ->
    set_add eq_dec a l = l.
Proof.
  induction l. crush.
  intros.
  unfold set_In in *. unfold In in *.
  destruct H.
  * subst. unfold set_add. destruct (eq_dec a a) eqn:? ; crush.
  * crush. edestruct eq_dec ; reflexivity.
Qed.

Lemma incl_cons_inv :
  forall {A: Type} (a: A) b c,
    incl (a::b) c ->
    incl b c.
Proof.
  intros until c. generalize a c.
  induction b ; induction c ; crush.
  * unfold incl. intros. inversion H0.
  * unfold incl in *.
    intros.
    specialize (H a2).
    assert (In a2 (a1 :: a0 :: b)). crush. intuition.
Qed.

(* currently only proved for nat, should extend to general type later if necessary *)
Theorem set_union_nodup_inv_1 :
  forall l l',
    NoDup (set_union eq_nat_dec l l') ->
    NoDup l.
Proof.
  intros l l'. revert l.
  induction l'.
  * intros.
    induction l; crush.
  * intros.
    unfold set_union in * ; fold set_union in *.
    specialize (IHl' l).
    induction (((fix set_union (x y : set nat) {struct y} : set nat :=
               match y with
               | nil => x
               | a1 :: y1 => set_add eq_nat_dec a1 (set_union x y1)
               end) l l')).
  - eapply IHl'. constructor.
  - simpl in H.
    destruct (eq_nat_dec a a0).
    + eauto.
    + inversion H. subst.
      assert (NoDup s -> NoDup l).
      ** intros.
         assert (~ In a0 s).
         unfold not. intros.
         assert (In a0 (set_add eq_nat_dec a s)). eapply set_add_intro1; auto.
         crush.
         assert (NoDup (a0 :: s)). constructor ; auto.
         intuition.
      ** eauto.
Qed.
