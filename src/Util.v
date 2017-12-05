Require Import List ListSet Equality CpdtTactics.

(* Lemmas about split *)
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

Lemma in_split_exists_fst :
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