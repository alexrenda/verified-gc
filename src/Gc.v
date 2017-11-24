Require Import Gc.Language.
Require Import List ListSet Equality CpdtTactics.

Inductive addresing_string : Type :=
| TermStr : addresing_string
| FollowStr : nat -> addresing_string -> addresing_string
.

Inductive addresses : heap_t -> ptr -> addresing_string -> ptr -> Prop :=
| TermAddresses : forall h p,
    (exists vs, heap_maps_struct h p vs) ->
    addresses h p TermStr p
| FollowAddresses : forall h p p' p'' k rest,
    heap_maps h p k (Pointer p') ->
    addresses h p' rest p'' ->
    addresses h p (FollowStr k rest) p''
.


Fixpoint mark_ptr (fuel:nat) (p: ptr) (h: heap_t) : set ptr :=
  match fuel, heap_get_struct p h with
  | S n, Some vs =>
      List.fold_left
        (set_union ptr_eq_dec)
        (List.map
           (fun v =>
              match v with
              | Int _ => List.nil
              | Pointer p' => mark_ptr n p' h
              end
           ) vs)
        (set_add ptr_eq_dec p (empty_set ptr))
  | _, _ => List.nil
  end
.

Lemma heap_maps_implies_heap_get :
  forall h p n v,
  heap_maps h p n v ->
  exists vs,
    heap_get_struct p h = Some vs
    /\
    List.nth_error vs n = Some v
.
Proof.
(*
  induction h ; intros.
  * inversion H.
  * specialize IHh with p n v.
    destruct a.
    unfold heap_get_struct.
    unfold heap_maps in *.
    unfold heap_get in *.
    destruct (ptr_eq_dec p0 p) eqn:?.
    - exists l. crush.
      destruct (ptr_eq_dec p p); crush.
    - crush.
      destruct (ptr_eq_dec p0 p); crush.
*)
Admitted.

Lemma fold_union_1 :
  forall {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
         (vs: list (set A)) (acc acc': set A) (a: A),
    List.fold_left (set_union eq_dec) vs acc = acc' ->
    set_In a acc ->
    set_In a acc'.
Proof.
  induction vs.
  * intros.
    subst.
    unfold List.fold_left. auto.
  * intros.
    specialize (fold_left_app (set_union eq_dec) (List.cons a List.nil) vs acc).
    crush.
    specialize (IHvs (set_union eq_dec acc a) (List.fold_left (set_union eq_dec) vs (set_union eq_dec acc a)) a0).
    assert (set_In a0 (set_union eq_dec acc a)). eapply set_union_intro1. auto.
    intuition.
Qed.

Lemma fold_union_nth_error :
  forall {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
         (vs: list (set A)) (n: nat) (v acc : set A) (a: A),
    List.nth_error vs n = Some v ->
    set_In a v ->
    set_In a (List.fold_left (set_union eq_dec) vs acc).
Proof.
  induction vs.
  * intros.
    specialize (nth_error_In nil n H).
    intros.
    inversion H1.
  * induction n ; intros.
    - inversion H. clear H.
      subst.
      crush.
      eapply fold_union_1. crush.
      eapply (set_union_intro2). auto.
    - crush.
      eapply IHvs ; crush.
Qed.

Theorem mark_ptr_marks :
  forall address h p p',
    addresses h p address p' ->
    exists f, set_In p' (mark_ptr f p h)
.
Proof.
  induction address.
  * intros.
    inversion H. clear H.
    inversion H0. clear H0.
    subst.
    exists 1.
    unfold mark_ptr.
    rewrite H.
    eapply fold_union_1 ; crush.
  * intros.
    inversion H. clear H.
    subst.
    specialize (IHaddress h p'0 p' H6).
    inversion IHaddress. clear IHaddress.
    exists (S x).
    specialize (heap_maps_implies_heap_get h p n (Pointer p'0) H4).
    intros.
    inversion H0 ; clear H0.
    destruct H1.
    unfold mark_ptr.
    fold mark_ptr.
    rewrite H0.
    specialize (List.map_nth_error (fun v : val =>
           match v with
           | Int _ => nil
           | Pointer p'1 => mark_ptr x p'1 h
           end) n x0 H1).
    intros.
    eapply fold_union_nth_error.
    eapply H2.
    auto.
Qed.

Lemma fold_left_acc_irrelevence :
  forall {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
         (vs: list (set A)) (acc acc': set A) (a: A),
    set_In a (List.fold_left (set_union eq_dec) vs acc) ->
    ~ set_In a acc ->
    set_In a (List.fold_left (set_union eq_dec) vs acc').
Proof.
Admitted.

Lemma fold_left_irrelevance_forward :
  forall {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
         (vs: list (set A)) (acc acc': set A) (a: A),
    set_In a (List.fold_left (set_union eq_dec) vs acc) ->
    set_In a (List.fold_left (set_union eq_dec) vs acc') \/ set_In a acc.
Proof.
  Hint Resolve set_union_elim set_union_intro fold_union_1 set_union_emptyL.
  dependent induction vs; intros.
  * intuition.
  * pose (set_In_dec eq_dec a0 a).
    destruct s.
    - left.
      simpl in *.
      eapply (fold_union_1 eq_dec vs (set_union eq_dec acc' a) 
        (fold_left (set_union eq_dec) vs (set_union eq_dec acc' a)) a0); intuition.
    - simpl in *.
      pose (set_In_dec eq_dec a0 acc).
      destruct s; auto.
      specialize IHvs with acc (set_union eq_dec acc' a) a0.
      apply IHvs.
      eapply fold_left_acc_irrelevence in H.
      + instantiate (1 := acc) in H.
        intuition.
      + intuition.
        apply set_union_elim in H0.
        intuition.
Qed.

Lemma fold_left_irrelevance :
  forall {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
         (vs: list (set A)) (acc: set A) (a: A),
    set_In a (List.fold_left (set_union eq_dec) vs acc) <->
    set_In a (List.fold_left (set_union eq_dec) vs nil) \/ set_In a acc.
Proof.
  Hint Resolve set_union_iff fold_left_irrelevance_forward.
  Hint Resolve <- set_union_iff.
  intuition.
  * dependent induction vs.
    - intuition.
    - simpl in *.
      pose (set_In_dec eq_dec a0 a).
      destruct s.
      + eapply (fold_union_1 eq_dec vs (set_union eq_dec acc a)
            (fold_left (set_union eq_dec) vs (set_union eq_dec acc a)) a0); intuition.
      + specialize IHvs with (set_union eq_dec acc a) a0.
        apply IHvs.
        eapply fold_left_irrelevance_forward in H0.
        instantiate (1 := nil) in H0.
        destruct H0; intuition.
        apply set_union_emptyL in H.
        congruence.
  * apply (fold_union_1 eq_dec vs acc ((fold_left (set_union eq_dec) vs acc)) a); intuition.
Qed.

Lemma fold_union_2 :
  forall {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
         (vs: list (set A)) (acc1 acc2: set A) (a: A),
    set_In a (List.fold_left (set_union eq_dec) vs (set_union eq_dec acc1 acc2)) ->
    set_In a (set_union eq_dec (List.fold_left (set_union eq_dec) vs acc1) acc2).
Proof.
  Hint Resolve set_union_elim set_union_intro fold_left_irrelevance.
  Hint Resolve <- fold_left_irrelevance.
  intros.
  eapply set_union_intro.
  eapply fold_left_irrelevance in H.
  pose (set_In_dec eq_dec a acc1).
  destruct s.
  - intuition.
  - inversion H.
    + intuition.
    + right.
      apply set_union_elim in H0.
      destruct H0; intuition.
Qed.

(* Must be proved for liveness *)
Theorem mark_ptr_correct :
  forall h p p' f,
    set_In p' (mark_ptr f p h) ->
    exists address, addresses h p address p'
.
Proof.
  Hint Constructors addresses addresing_string.
  intros.
  dependent induction f generalizing p.
  - unfold mark_ptr in H.
    intuition.
  - unfold mark_ptr in H.
    fold mark_ptr in H.
    destruct (heap_get_struct p h) eqn:?; intuition.
    assert (exists vs, heap_maps_struct h p vs); eauto.
    remember (heap_maps_struct_indexable p h l).
    assert (forall a, In a l -> exists k, heap_maps h p k a); intuition.
    clear Heqo.
    clear Heqe.
    dependent induction l.
    * crush.
      eauto.
    * rewrite map_cons in H.
      destruct a eqn:?.
      + crush.
      + simpl in H.
        apply fold_union_2 in H; auto.
        apply set_union_elim in H.
        destruct H.
        -- apply IHl; intuition.
        -- specialize IHf with p0.
           intuition.
           edestruct H2.
           assert (exists k, heap_maps h p k a).
           ** crush.
           ** edestruct H4.
              exists (FollowStr x0 x).
              eapply (FollowAddresses h p p0 p'); subst; eauto.
Qed.


Fixpoint mark (fuel:nat) (r: roots_t) (h: heap_t) : set ptr :=
  match r with
  | List.nil => List.nil
  | List.cons (var, ptr) rest =>
    set_union ptr_eq_dec (mark fuel rest h) (mark_ptr fuel ptr h)
  end
.

Fixpoint sweep (h: heap_t) (ptrs: set ptr) : heap_t :=
  match h with
  | List.nil => List.nil
  | List.cons (ptr, val) tail =>
    if set_mem ptr_eq_dec ptr ptrs then
      (ptr,val) :: (sweep tail ptrs)
    else
      sweep tail ptrs
  end
.

Definition gc (f: nat) (r: roots_t) (h: heap_t) : heap_t :=
  sweep h (mark f r h)
.

Theorem heap_marks :
  forall address s v p p',
    roots_maps (roots s) v p ->
    addresses (heap s) p address p' ->
    exists f, set_In p' (mark f (roots s) (heap s))
.
Proof.
  intros address s.
  induction (roots s).
  * crush.
  * intros.
    destruct a.
    specialize IHr with v p p'.
    unfold roots_maps in *.
    specialize (in_inv H). intros.
    destruct H1.
     - clear H. injection H1. clear H1. intros. subst.
       unfold mark. fold mark.
       specialize (mark_ptr_marks address (heap s) p p' H0).
       intros.
       inversion H. clear H.
       exists x.
       eapply set_union_intro2. auto.
     - intuition.
       inversion H3. clear H3.
       exists x.
       crush.
Qed.

(* Must be proved for liveness *)
Lemma pointer_equivalence :
  forall address s v p p' h,
    roots_maps (roots s) v p ->
    addresses (heap s) p address p' ->
    sweep (heap s) (mark (fuel s) (roots s) (heap s)) = h ->
    addresses h p address p'.
Proof.
(*  induction address.
  * intros.
    inversion H0.
  * intros.
    inversion H0.
    subst.
    remember (fuel s) as f.
    induction f ; subst.
  -  unfold gc, mark, sweep.

      subst.
      induction (fuel s).
    -
    induction v0.
    - inversion H5.
      subst.

      inversion H5.
      specialize (IHaddress s v p).
    intuition.
    eapply IHaddress.
 *)
Admitted.

(*
Theorem safety_1 :
  forall c s s' s'',
  small_step c s = Some s' ->
  small_step c (gc s) = Some s''.
Proof.
  intros.
  destruct c ; unfold small_step in * ; crush.
  * unfold small_step in H.
Qed.
*)
