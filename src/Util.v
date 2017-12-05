Require Import List ListSet Equality CpdtTactics.

(* Lemmas about split *)
Lemma in_split_l_hd :
  forall {A B: Type} (l: list (A * B)) (a: A) (b: B),
    In a (fst (split ((a, b) :: l))).
Proof.
  intros.
  simpl.
  destruct (split l). 
  crush.
Qed.

Lemma in_split_l_tl :
  forall {A B: Type} (l: list (A * B)) (p o: A) (v: B),
    In p (fst (split l)) ->
    In p (fst (split ((o, v) :: l))).
Proof.
  induction l. crush.
  crush.
  specialize (IHl p o v).
  destruct (split l). crush.
Qed.

Lemma in_split_l :
  forall {A B: Type} (l: list (A * B)) (p o: A) (v: B),
    In p (fst (split l)) \/ p = o <->
    In p (fst (split ((o, v) :: l))).
Proof.
  Hint Resolve in_split_l_tl in_split_l_hd.
Admitted.

Lemma in_split_r_hd :
  forall {A B: Type} (l: list (A * B)) (a: A) (b: B),
    In b (snd (split ((a, b) :: l))).
Proof.
  intros.
  simpl.
  destruct (split l). 
  crush.
Qed.

Lemma in_split_r_tl :
  forall {A B: Type} (l: list (A * B)) (p: B) (o: A) (v: B),
    In p (snd (split l)) ->
    In p (snd (split ((o, v) :: l))).
Proof.
  induction l. crush.
  crush.
  specialize (IHl p o v).
  destruct (split l). crush.
Qed.

Lemma in_split_r :
  forall {A B: Type} (l: list (A * B)) (o: A) (p v: B),
    In p (snd (split l)) \/ p = v <->
    In p (snd (split ((o, v) :: l))).
Proof.
Admitted.

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
Theorem set_add_noop :
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
